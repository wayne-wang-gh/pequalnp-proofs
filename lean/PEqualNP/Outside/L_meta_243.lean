import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_243

open PEqualNP.MetaComplexity

section BinCircuitCore

private def bstep (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

private def wval {n : ℕ} (C : BinaryCircuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma foldl_len (gs : List BinaryGate) (W : List Bool) :
    (gs.foldl bstep W).length = W.length + gs.length := by
  induction gs generalizing W with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, List.length_cons, ih, bstep, List.length_append, List.length_nil]; omega

private lemma foldl_prefix (gs : List BinaryGate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
    (gs.foldl bstep W).getD i false = W.getD i false := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [bstep]; omega)]
    exact List.getD_append W _ false i hi

private lemma wval_input {n : ℕ} (C : BinaryCircuit) (x : Fin n → Bool) (i : Fin n) :
    wval C x i.val = x i := by
  unfold wval BinaryCircuit.wires
  change (C.gates.foldl bstep (List.ofFn x)).getD i.val false = x i
  rw [foldl_prefix _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma wval_ge {n : ℕ} (C : BinaryCircuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wval C x w = false := by
  unfold wval BinaryCircuit.wires
  change (C.gates.foldl bstep (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by rw [foldl_len]; simp; omega)

private lemma wval_gate {n : ℕ} (C : BinaryCircuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) :
    let g := C.gates[k]
    wval C x (n + k) =
      g.op (if g.left < n + k then wval C x g.left else false)
           (if g.right < n + k then wval C x g.right else false) := by
  let g := C.gates[k]
  let pre := C.gates.take k
  let post := C.gates.drop (k + 1)
  have hsplit : C.gates = pre ++ g :: post := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = g :: post := List.drop_eq_getElem_cons hk
    rw [← h2]; exact h1.symm
  let W := pre.foldl bstep (List.ofFn x)
  have hWlen : W.length = n + k := by
    simp [W, pre, foldl_len, Nat.min_eq_left hk.le]
  have hfull : C.gates.foldl bstep (List.ofFn x) = post.foldl bstep (bstep W g) := by
    conv_lhs => rw [hsplit]
    simp only [List.foldl_append, List.foldl_cons, W]
  have hread : ∀ r : ℕ, W.getD r false = if r < n + k then wval C x r else false := by
    intro r
    by_cases hr : r < n + k
    · simp only [hr, ↓reduceIte]
      unfold wval BinaryCircuit.wires
      change W.getD r false = (C.gates.foldl bstep (List.ofFn x)).getD r false
      rw [hfull, foldl_prefix post _ r (by simp [bstep, hWlen]; omega)]
      exact (List.getD_append W _ false r (by omega)).symm
    · simp only [hr, ↓reduceIte]
      exact List.getD_eq_default _ _ (by omega)
  unfold wval BinaryCircuit.wires
  change (C.gates.foldl bstep (List.ofFn x)).getD (n + k) false = _
  rw [hfull, foldl_prefix post _ (n + k) (by simp [bstep, hWlen])]
  simp only [bstep, ← hWlen]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp only [Nat.sub_self, List.getD_cons_zero]
  rw [hWlen]
  exact congrArg₂ g.op (hread g.left) (hread g.right)

private lemma wval_take {n : ℕ} (gs : List BinaryGate) (x : Fin n → Bool) (m w : ℕ)
    (hm : m ≤ gs.length) (hw : w < n + m) :
    wval ⟨gs.take m, 0⟩ x w = wval ⟨gs, 0⟩ x w := by
  unfold wval BinaryCircuit.wires
  have hsp : gs = gs.take m ++ gs.drop m := (List.take_append_drop m gs).symm
  change ((gs.take m).foldl bstep (List.ofFn x)).getD w false =
    (gs.foldl bstep (List.ofFn x)).getD w false
  conv_rhs => rw [hsp, List.foldl_append]
  rw [foldl_prefix (gs.drop m) _ w (by rw [foldl_len]; simp [Nat.min_eq_left hm]; omega)]

private lemma flip_last_gate {n : ℕ} (gs : List BinaryGate) (m : ℕ) (hm : m < gs.length) :
    ∃ C' : BinaryCircuit, C'.size ≤ m + 1 ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = !(wval ⟨gs, 0⟩ x (n + m)) := by
  let g := gs[m]
  let gs' := gs.take m ++ [⟨fun a b => !(g.op a b), g.left, g.right⟩]
  refine ⟨⟨gs', n + m⟩, ?_, ?_⟩
  · simp [BinaryCircuit.size, gs', Nat.min_eq_left hm.le]
  · intro x
    have hlen : (gs.take m).length = m := by simp [Nat.min_eq_left hm.le]
    have hWlen : ((gs.take m).foldl bstep (List.ofFn x)).length = n + m := by
      rw [foldl_len, hlen]; simp
    have hlhs : (BinaryCircuit.mk gs' (n + m)).eval (List.ofFn x) =
        !(g.op (((gs.take m).foldl bstep (List.ofFn x)).getD g.left false)
               (((gs.take m).foldl bstep (List.ofFn x)).getD g.right false)) := by
      unfold BinaryCircuit.eval BinaryCircuit.wires
      change (gs'.foldl bstep (List.ofFn x)).getD (n + m) false = _
      simp only [gs', List.foldl_append, List.foldl_cons, List.foldl_nil, bstep]
      rw [← hWlen, List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    have hread : ∀ r : ℕ, ((gs.take m).foldl bstep (List.ofFn x)).getD r false =
        if r < n + m then wval ⟨gs, 0⟩ x r else false := by
      intro r
      by_cases hr : r < n + m
      · simp only [hr, ↓reduceIte]
        exact wval_take gs x m r hm.le hr
      · simp only [hr, ↓reduceIte]
        exact List.getD_eq_default _ _ (by omega)
    rw [hlhs, hread g.left, hread g.right]
    have hg := wval_gate ⟨gs, 0⟩ x m hm
    dsimp only at hg
    rw [hg]

private inductive WRef where
  | const (b : Bool)
  | wire (idx : ℕ) (flip : Bool)

private def evalWRef (W : List Bool) : WRef → Bool
  | WRef.const b => b
  | WRef.wire idx fl => xor fl (W.getD idx false)

private lemma evalWRef_prefix (gs : List BinaryGate) (W : List Bool) (r : WRef)
    (hr : ∀ idx fl, r = WRef.wire idx fl → idx < W.length) :
    evalWRef (gs.foldl bstep W) r = evalWRef W r := by
  cases r with
  | const b => rfl
  | wire idx fl =>
    simp only [evalWRef]
    rw [foldl_prefix gs W idx (hr idx fl rfl)]

private def unaryRef (u : Bool → Bool) (idx : ℕ) : WRef :=
  if u false = u true then WRef.const (u false) else WRef.wire idx (u false)

private lemma evalWRef_unaryRef (W : List Bool) (u : Bool → Bool) (idx : ℕ) :
    evalWRef W (unaryRef u idx) = u (W.getD idx false) := by
  unfold unaryRef
  split_ifs with h
  · simp only [evalWRef]; cases W.getD idx false <;> simp [h]
  · simp only [evalWRef]
    cases hu0 : u false <;> cases hu1 : u true <;> cases W.getD idx false <;> simp_all

private structure CompState where
  gs' : List BinaryGate
  env : ℕ → WRef
  skipped : Finset ℕ

private def compStep (n : ℕ) (ov : ℕ → Option Bool) (k : ℕ) (g : BinaryGate)
    (st : CompState) : CompState :=
  match ov (n + k) with
  | some b =>
    ⟨st.gs', Function.update st.env (n + k) (WRef.const b), insert k st.skipped⟩
  | none =>
    let rL := if g.left < n + k then st.env g.left else WRef.const false
    let rR := if g.right < n + k then st.env g.right else WRef.const false
    match rL, rR with
    | WRef.const b1, WRef.const b2 =>
      ⟨st.gs', Function.update st.env (n + k) (WRef.const (g.op b1 b2)), insert k st.skipped⟩
    | WRef.const b1, WRef.wire j2 f2 =>
      let u := fun y => g.op b1 (xor f2 y)
      ⟨st.gs', Function.update st.env (n + k) (unaryRef u j2), insert k st.skipped⟩
    | WRef.wire j1 f1, WRef.const b2 =>
      let u := fun y => g.op (xor f1 y) b2
      ⟨st.gs', Function.update st.env (n + k) (unaryRef u j1), insert k st.skipped⟩
    | WRef.wire j1 f1, WRef.wire j2 f2 =>
      if j1 = j2 then
        let u := fun y => g.op (xor f1 y) (xor f2 y)
        ⟨st.gs', Function.update st.env (n + k) (unaryRef u j1), insert k st.skipped⟩
      else
        let g' : BinaryGate := ⟨fun a b => g.op (xor f1 a) (xor f2 b), j1, j2⟩
        ⟨st.gs' ++ [g'], Function.update st.env (n + k) (WRef.wire (n + st.gs'.length) false), st.skipped⟩

private def compInit (n : ℕ) (ov : ℕ → Option Bool) : CompState :=
  ⟨[], fun w => if w < n then
    match ov w with
    | some b => WRef.const b
    | none => WRef.wire w false
  else WRef.const false, ∅⟩

private def compileRec (n : ℕ) (ov : ℕ → Option Bool) :
    ℕ → List BinaryGate → CompState → CompState
  | _, [], st => st
  | k, g :: gs, st => compileRec n ov (k + 1) gs (compStep n ov k g st)

private def compile (n : ℕ) (ov : ℕ → Option Bool) (gs : List BinaryGate) : CompState :=
  compileRec n ov 0 gs (compInit n ov)

private lemma unaryRef_wire_idx (u : Bool → Bool) (j idx : ℕ) (fl : Bool)
    (he : unaryRef u j = WRef.wire idx fl) : idx = j := by
  unfold unaryRef at he
  by_cases h : u false = u true
  · simp [h] at he
  · simp [h] at he; exact he.1.symm

private lemma compileRec_inv (n : ℕ) (ov : ℕ → Option Bool) (C : BinaryCircuit)
    (k : ℕ) (rest : List BinaryGate) (st : CompState)
    (hrest : rest = C.gates.drop k) (hk : k ≤ C.gates.length)
    (hsize : st.gs'.length + st.skipped.card = k)
    (hskip_lt : ∀ j ∈ st.skipped, j < k)
    (hbound : ∀ w < n + k, ∀ idx fl, st.env w = WRef.wire idx fl → idx < n + st.gs'.length)
    (hval : ∀ x : Fin n → Bool,
      (∀ w b, ov w = some b → wval C x w = b) →
      ∀ w < n + k, evalWRef (st.gs'.foldl bstep (List.ofFn x)) (st.env w) = wval C x w) :
    let stf := compileRec n ov k rest st
    stf.gs'.length + stf.skipped.card = C.gates.length ∧
    (∀ j ∈ st.skipped, j ∈ stf.skipped) ∧
    (∀ w < n + k, stf.env w = st.env w) ∧
    (∀ w < n + C.gates.length, ∀ idx fl, stf.env w = WRef.wire idx fl → idx < n + stf.gs'.length) ∧
    (∀ x : Fin n → Bool,
      (∀ w b, ov w = some b → wval C x w = b) →
      ∀ w < n + C.gates.length, evalWRef (stf.gs'.foldl bstep (List.ofFn x)) (stf.env w) = wval C x w) := by
  induction rest generalizing k st with
  | nil =>
    have hkeq : k = C.gates.length := by
      have hlen := congrArg List.length hrest
      simp only [List.length_nil, List.length_drop] at hlen
      omega
    subst hkeq
    exact ⟨hsize, fun _ h => h, fun _ _ => rfl, hbound, hval⟩
  | cons g gs ih =>
    have hklt : k < C.gates.length := by
      by_contra hge
      rw [List.drop_eq_nil_of_le (by omega)] at hrest
      exact List.cons_ne_nil g gs hrest
    have hgk : g = C.gates[k] := by
      have hdrop := List.drop_eq_getElem_cons hklt
      rw [hdrop] at hrest
      exact (List.cons.inj hrest).1
    have hgs : gs = C.gates.drop (k + 1) := by
      have hdrop := List.drop_eq_getElem_cons hklt
      rw [hdrop] at hrest
      exact (List.cons.inj hrest).2
    let st1 := compStep n ov k g st
    have hnotmem : k ∉ st.skipped := fun h => absurd (hskip_lt k h) (lt_irrefl k)
    have hstep :
        st1.gs'.length + st1.skipped.card = k + 1 ∧
        (∀ j ∈ st.skipped, j ∈ st1.skipped) ∧
        (∀ j ∈ st1.skipped, j < k + 1) ∧
        (∀ w < n + k, st1.env w = st.env w) ∧
        (∀ w < n + (k + 1), ∀ idx fl, st1.env w = WRef.wire idx fl → idx < n + st1.gs'.length) ∧
        (∀ x : Fin n → Bool,
          (∀ w b, ov w = some b → wval C x w = b) →
          ∀ w < n + (k + 1), evalWRef (st1.gs'.foldl bstep (List.ofFn x)) (st1.env w) = wval C x w) := by
      have hWlen : ∀ x : Fin n → Bool, (st.gs'.foldl bstep (List.ofFn x)).length = n + st.gs'.length := fun x => by
        rw [foldl_len]; simp
      have hgate_eq : ∀ x : Fin n → Bool,
          wval C x (n + k) =
            g.op (if g.left < n + k then wval C x g.left else false)
                 (if g.right < n + k then wval C x g.right else false) := by
        intro x; rw [hgk]; exact wval_gate C x k hklt
      have hr_eval : ∀ (x : Fin n → Bool) (hov : ∀ w b, ov w = some b → wval C x w = b) (r : ℕ),
          evalWRef (st.gs'.foldl bstep (List.ofFn x)) (if r < n + k then st.env r else WRef.const false) =
            if r < n + k then wval C x r else false := by
        intro x hov r
        by_cases hr : r < n + k
        · simp only [hr, ↓reduceIte]; exact hval x hov r hr
        · simp only [hr, ↓reduceIte]; rfl
      have hr_bound : ∀ (r idx : ℕ) (fl : Bool),
          (if r < n + k then st.env r else WRef.const false) = WRef.wire idx fl → idx < n + st.gs'.length := by
        intro r idx fl he
        by_cases hr : r < n + k
        · simp only [hr, ↓reduceIte] at he; exact hbound r hr idx fl he
        · simp only [hr, ↓reduceIte] at he; cases he
      dsimp only [st1, compStep]
      cases hovk : ov (n + k) with
      | some b =>
        dsimp only
        refine ⟨by rw [Finset.card_insert_of_notMem hnotmem]; omega,
          fun j hj => Finset.mem_insert_of_mem hj,
          fun j hj => by rcases Finset.mem_insert.mp hj with rfl | hj'; omega; have := hskip_lt j hj'; omega,
          fun w hw => Function.update_of_ne (by omega) _ _,
          fun w hw idx fl hwe => ?_,
          fun x hov w hw => ?_⟩
        · by_cases hwk : w = n + k
          · rw [hwk, Function.update_self] at hwe; cases hwe
          · rw [Function.update_of_ne hwk] at hwe; exact hbound w (by omega) idx fl hwe
        · by_cases hwk : w = n + k
          · rw [hwk, Function.update_self]; exact (hov (n + k) b hovk).symm
          · rw [Function.update_of_ne hwk]; exact hval x hov w (by omega)
      | none =>
        dsimp only
        generalize hL : (if g.left < n + k then st.env g.left else WRef.const false) = rL
        generalize hR : (if g.right < n + k then st.env g.right else WRef.const false) = rR
        cases rL with
        | const b1 =>
          cases rR with
          | const b2 =>
            dsimp only
            refine ⟨by rw [Finset.card_insert_of_notMem hnotmem]; omega,
              fun j hj => Finset.mem_insert_of_mem hj,
              fun j hj => by rcases Finset.mem_insert.mp hj with rfl | hj'; omega; have := hskip_lt j hj'; omega,
              fun w hw => Function.update_of_ne (by omega) _ _,
              fun w hw idx fl hwe => ?_,
              fun x hov w hw => ?_⟩
            · by_cases hwk : w = n + k
              · rw [hwk, Function.update_self] at hwe; cases hwe
              · rw [Function.update_of_ne hwk] at hwe; exact hbound w (by omega) idx fl hwe
            · by_cases hwk : w = n + k
              · rw [hwk, Function.update_self, hgate_eq x]
                have eL := hr_eval x hov g.left; rw [hL] at eL
                have eR := hr_eval x hov g.right; rw [hR] at eR
                rw [← eL, ← eR]; rfl
              · rw [Function.update_of_ne hwk]; exact hval x hov w (by omega)
          | wire j2 f2 =>
            dsimp only
            have hj2 : j2 < n + st.gs'.length := hr_bound g.right j2 f2 hR
            refine ⟨by rw [Finset.card_insert_of_notMem hnotmem]; omega,
              fun j hj => Finset.mem_insert_of_mem hj,
              fun j hj => by rcases Finset.mem_insert.mp hj with rfl | hj'; omega; have := hskip_lt j hj'; omega,
              fun w hw => Function.update_of_ne (by omega) _ _,
              fun w hw idx fl hwe => ?_,
              fun x hov w hw => ?_⟩
            · by_cases hwk : w = n + k
              · rw [hwk, Function.update_self] at hwe
                rw [unaryRef_wire_idx _ _ _ _ hwe]; exact hj2
              · rw [Function.update_of_ne hwk] at hwe; exact hbound w (by omega) idx fl hwe
            · by_cases hwk : w = n + k
              · rw [hwk, Function.update_self, evalWRef_unaryRef, hgate_eq x]
                have eL := hr_eval x hov g.left; rw [hL] at eL
                have eR := hr_eval x hov g.right; rw [hR] at eR
                rw [← eL, ← eR]; rfl
              · rw [Function.update_of_ne hwk]; exact hval x hov w (by omega)
        | wire j1 f1 =>
          have hj1 : j1 < n + st.gs'.length := hr_bound g.left j1 f1 hL
          cases rR with
          | const b2 =>
            dsimp only
            refine ⟨by rw [Finset.card_insert_of_notMem hnotmem]; omega,
              fun j hj => Finset.mem_insert_of_mem hj,
              fun j hj => by rcases Finset.mem_insert.mp hj with rfl | hj'; omega; have := hskip_lt j hj'; omega,
              fun w hw => Function.update_of_ne (by omega) _ _,
              fun w hw idx fl hwe => ?_,
              fun x hov w hw => ?_⟩
            · by_cases hwk : w = n + k
              · rw [hwk, Function.update_self] at hwe
                rw [unaryRef_wire_idx _ _ _ _ hwe]; exact hj1
              · rw [Function.update_of_ne hwk] at hwe; exact hbound w (by omega) idx fl hwe
            · by_cases hwk : w = n + k
              · rw [hwk, Function.update_self, evalWRef_unaryRef, hgate_eq x]
                have eL := hr_eval x hov g.left; rw [hL] at eL
                have eR := hr_eval x hov g.right; rw [hR] at eR
                rw [← eL, ← eR]; rfl
              · rw [Function.update_of_ne hwk]; exact hval x hov w (by omega)
          | wire j2 f2 =>
            dsimp only
            by_cases hjeq : j1 = j2
            · simp only [hjeq, ↓reduceIte]
              refine ⟨by rw [Finset.card_insert_of_notMem hnotmem]; omega,
                fun j hj => Finset.mem_insert_of_mem hj,
                fun j hj => by rcases Finset.mem_insert.mp hj with rfl | hj'; omega; have := hskip_lt j hj'; omega,
                fun w hw => Function.update_of_ne (by omega) _ _,
                fun w hw idx fl hwe => ?_,
                fun x hov w hw => ?_⟩
              · by_cases hwk : w = n + k
                · rw [hwk, Function.update_self] at hwe
                  rw [unaryRef_wire_idx _ _ _ _ hwe]; omega
                · rw [Function.update_of_ne hwk] at hwe; exact hbound w (by omega) idx fl hwe
              · by_cases hwk : w = n + k
                · rw [hwk, Function.update_self, evalWRef_unaryRef, hgate_eq x]
                  have eL := hr_eval x hov g.left; rw [hL] at eL
                  have eR := hr_eval x hov g.right; rw [hR] at eR
                  rw [← eL, ← eR, hjeq]; rfl
                · rw [Function.update_of_ne hwk]; exact hval x hov w (by omega)
            · simp only [hjeq, ↓reduceIte]
              refine ⟨by simp; omega,
                fun j hj => hj,
                fun j hj => by have := hskip_lt j hj; omega,
                fun w hw => Function.update_of_ne (by omega) _ _,
                fun w hw idx fl hwe => ?_,
                fun x hov w hw => ?_⟩
              · by_cases hwk : w = n + k
                · rw [hwk, Function.update_self] at hwe; injection hwe with h1 _; simp [← h1]
                · rw [Function.update_of_ne hwk] at hwe
                  have := hbound w (by omega) idx fl hwe; simp; omega
              · let g' : BinaryGate := ⟨fun a b => g.op (xor f1 a) (xor f2 b), j1, j2⟩
                have hfold : (st.gs' ++ [g']).foldl bstep (List.ofFn x) =
                    bstep (st.gs'.foldl bstep (List.ofFn x)) g' := by
                  simp [List.foldl_append]
                rw [hfold]
                by_cases hwk : w = n + k
                · rw [hwk, Function.update_self, hgate_eq x]
                  have eL := hr_eval x hov g.left; rw [hL] at eL
                  have eR := hr_eval x hov g.right; rw [hR] at eR
                  rw [← eL, ← eR]
                  simp only [evalWRef, bstep, ← hWlen x]
                  rw [List.getD_append_right _ _ _ _ (le_refl _)]
                  simp [g']
                · rw [Function.update_of_ne hwk]
                  have hev := evalWRef_prefix [g'] (st.gs'.foldl bstep (List.ofFn x)) (st.env w)
                    (fun idx fl he => by rw [hWlen x]; exact hbound w (by omega) idx fl he)
                  simp only [List.foldl_cons, List.foldl_nil] at hev
                  rw [hev]
                  exact hval x hov w (by omega)
    obtain ⟨hs1, hsk1, hsklt1, henv1, hb1, hv1⟩ := hstep
    obtain ⟨hsf, hskf, henvf, hbf, hvf⟩ := ih (k + 1) st1 hgs (by omega) hs1 hsklt1 hb1 hv1
    refine ⟨hsf, fun j hj => hskf j (hsk1 j hj), fun w hw => ?_, hbf, hvf⟩
    have h1 := henvf w (by omega)
    have h2 := henv1 w hw
    exact h1.trans h2

private lemma compile_spec (n : ℕ) (ov : ℕ → Option Bool) (C : BinaryCircuit) :
    let stf := compile n ov C.gates
    stf.gs'.length + stf.skipped.card = C.gates.length ∧
    (∀ w < n + C.gates.length, ∀ idx fl, stf.env w = WRef.wire idx fl → idx < n + stf.gs'.length) ∧
    (∀ x : Fin n → Bool,
      (∀ w b, ov w = some b → wval C x w = b) →
      ∀ w < n + C.gates.length, evalWRef (stf.gs'.foldl bstep (List.ofFn x)) (stf.env w) = wval C x w) := by
  have h := compileRec_inv n ov C 0 C.gates (compInit n ov) rfl (Nat.zero_le _)
    (by simp [compInit]) (fun j hj => absurd hj (Finset.notMem_empty j))
    (fun w hw idx fl he => by
      simp only [compInit, Nat.add_zero] at hw he
      simp only [hw, ↓reduceIte] at he
      cases hovw : ov w with
      | some _ => rw [hovw] at he; cases he
      | none => rw [hovw] at he; cases he; simp [compInit]; exact hw)
    (fun x hov w hw => by
      simp only [compInit, Nat.add_zero, List.foldl_nil] at hw ⊢
      simp only [hw, ↓reduceIte]
      cases hovw : ov w with
      | some b => exact (hov w b hovw).symm
      | none =>
        simp only [evalWRef, Bool.false_xor]
        let i : Fin n := ⟨w, hw⟩
        have hwi := wval_input C x i
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hw)]
        simp only [List.getElem_ofFn]
        exact hwi.symm)
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

private def NoDead (dead : ℕ → Prop) (r : WRef) : Prop :=
  ∀ idx fl, r = WRef.wire idx fl → ¬ dead idx

private def StepProps (n : ℕ) (ov : ℕ → Option Bool) (C : BinaryCircuit) (k : ℕ)
    (st : CompState) : Prop :=
  ∀ j < k, ∀ g, C.gates[j]? = some g →
    (ov (n + j) ≠ none → j ∈ st.skipped ∧ ∃ b, st.env (n + j) = WRef.const b) ∧
    ((g.left ≥ n + j ∨ (g.left < n + j ∧ ∃ b, st.env g.left = WRef.const b)) → j ∈ st.skipped) ∧
    ((g.right ≥ n + j ∨ (g.right < n + j ∧ ∃ b, st.env g.right = WRef.const b)) → j ∈ st.skipped) ∧
    ((g.left < n + j ∧ g.right < n + j ∧ g.left = g.right) → j ∈ st.skipped) ∧
    (((g.left ≥ n + j ∨ (g.left < n + j ∧ ∃ b, st.env g.left = WRef.const b)) ∧
      (g.right ≥ n + j ∨ (g.right < n + j ∧ ∃ b, st.env g.right = WRef.const b))) →
      ∃ b, st.env (n + j) = WRef.const b) ∧
    ((∃ b, g.left < n + j ∧ st.env g.left = WRef.const b ∧ g.op b false = g.op b true) →
      ∃ b', st.env (n + j) = WRef.const b') ∧
    ((∃ b, g.right < n + j ∧ st.env g.right = WRef.const b ∧ g.op false b = g.op true b) →
      ∃ b', st.env (n + j) = WRef.const b')

private lemma compileRec_step_props (n : ℕ) (ov : ℕ → Option Bool) (C : BinaryCircuit)
    (k : ℕ) (rest : List BinaryGate) (st : CompState)
    (hrest : rest = C.gates.drop k) (hk : k ≤ C.gates.length)
    (hprev : StepProps n ov C k st) :
    let stf := compileRec n ov k rest st
    (∀ j ∈ st.skipped, j ∈ stf.skipped) ∧
    (∀ w < n + k, stf.env w = st.env w) ∧
    StepProps n ov C C.gates.length stf := by
  induction rest generalizing k st with
  | nil =>
    have hkeq : k = C.gates.length := by
      have hlen := congrArg List.length hrest
      simp only [List.length_nil, List.length_drop] at hlen; omega
    subst hkeq
    exact ⟨fun _ h => h, fun _ _ => rfl, hprev⟩
  | cons g0 gs ih =>
    have hklt : k < C.gates.length := by
      by_contra hge
      rw [List.drop_eq_nil_of_le (by omega)] at hrest
      exact List.cons_ne_nil g0 gs hrest
    have hg0 : g0 = C.gates[k] := by
      rw [List.drop_eq_getElem_cons hklt] at hrest
      exact (List.cons.inj hrest).1
    have hgs : gs = C.gates.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hklt] at hrest
      exact (List.cons.inj hrest).2
    let st1 := compStep n ov k g0 st
    have hstep_skip : ∀ j ∈ st.skipped, j ∈ st1.skipped := by
      dsimp only [st1, compStep]
      cases ov (n + k) with
      | some _ => dsimp only; intro j hj; exact Finset.mem_insert_of_mem hj
      | none =>
        dsimp only
        cases (if g0.left < n + k then st.env g0.left else WRef.const false) <;>
        cases (if g0.right < n + k then st.env g0.right else WRef.const false) <;> dsimp only
        · intro j hj; exact Finset.mem_insert_of_mem hj
        · intro j hj; exact Finset.mem_insert_of_mem hj
        · intro j hj; exact Finset.mem_insert_of_mem hj
        · split_ifs
          · intro j hj; exact Finset.mem_insert_of_mem hj
          · intro j hj; exact hj
    have hstep_env_lt : ∀ w < n + k, st1.env w = st.env w := by
      intro w hw
      dsimp only [st1, compStep]
      cases ov (n + k) with
      | some _ => dsimp only; exact Function.update_of_ne (by omega) _ _
      | none =>
        dsimp only
        cases (if g0.left < n + k then st.env g0.left else WRef.const false) <;>
        cases (if g0.right < n + k then st.env g0.right else WRef.const false) <;> dsimp only
        · exact Function.update_of_ne (by omega) _ _
        · exact Function.update_of_ne (by omega) _ _
        · exact Function.update_of_ne (by omega) _ _
        · split_ifs <;> exact Function.update_of_ne (by omega) _ _
    have hprev1 : StepProps n ov C (k + 1) st1 := by
      intro j hj g hgj
      by_cases hjk : j < k
      · have hp := hprev j hjk g hgj
        have hrew_j : st1.env (n + j) = st.env (n + j) := hstep_env_lt (n + j) (by omega)
        have hrew_lt : ∀ w < n + j, st1.env w = st.env w := fun w hw => hstep_env_lt w (by omega)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hne; obtain ⟨hs, b, hb⟩ := hp.1 hne; exact ⟨hstep_skip _ hs, b, by rw [hrew_j, hb]⟩
        · rintro (hge | ⟨hlt, b, hb⟩)
          · exact hstep_skip _ (hp.2.1 (Or.inl hge))
          · rw [hrew_lt _ hlt] at hb; exact hstep_skip _ (hp.2.1 (Or.inr ⟨hlt, b, hb⟩))
        · rintro (hge | ⟨hlt, b, hb⟩)
          · exact hstep_skip _ (hp.2.2.1 (Or.inl hge))
          · rw [hrew_lt _ hlt] at hb; exact hstep_skip _ (hp.2.2.1 (Or.inr ⟨hlt, b, hb⟩))
        · intro h; exact hstep_skip _ (hp.2.2.2.1 h)
        · rintro ⟨hL, hR⟩
          have hL' : g.left ≥ n + j ∨ (g.left < n + j ∧ ∃ b, st.env g.left = WRef.const b) := by
            rcases hL with hge | ⟨hlt, b, hb⟩
            · exact Or.inl hge
            · rw [hrew_lt _ hlt] at hb; exact Or.inr ⟨hlt, b, hb⟩
          have hR' : g.right ≥ n + j ∨ (g.right < n + j ∧ ∃ b, st.env g.right = WRef.const b) := by
            rcases hR with hge | ⟨hlt, b, hb⟩
            · exact Or.inl hge
            · rw [hrew_lt _ hlt] at hb; exact Or.inr ⟨hlt, b, hb⟩
          obtain ⟨b, hb⟩ := hp.2.2.2.2.1 ⟨hL', hR'⟩
          exact ⟨b, by rw [hrew_j, hb]⟩
        · rintro ⟨b, hlt, hb, hop⟩
          rw [hrew_lt _ hlt] at hb
          obtain ⟨b', hb'⟩ := hp.2.2.2.2.2.1 ⟨b, hlt, hb, hop⟩
          exact ⟨b', by rw [hrew_j, hb']⟩
        · rintro ⟨b, hlt, hb, hop⟩
          rw [hrew_lt _ hlt] at hb
          obtain ⟨b', hb'⟩ := hp.2.2.2.2.2.2 ⟨b, hlt, hb, hop⟩
          exact ⟨b', by rw [hrew_j, hb']⟩
      · have hjeq : k = j := by omega
        rcases hjeq with rfl
        have hgeq : g0 = g := by
          rw [List.getElem?_eq_getElem hklt] at hgj
          injection hgj with hgj'; rw [← hgj', hg0]
        rcases hgeq with rfl
        have hLconst : (g0.left ≥ n + k ∨ (g0.left < n + k ∧ ∃ b, st1.env g0.left = WRef.const b)) →
            ∃ b, (if g0.left < n + k then st.env g0.left else WRef.const false) = WRef.const b := by
          rintro (hge | ⟨hlt, b, hb⟩)
          · exact ⟨false, by simp [show ¬ g0.left < n + k by omega]⟩
          · rw [hstep_env_lt _ hlt] at hb; exact ⟨b, by simp [hlt, hb]⟩
        have hRconst : (g0.right ≥ n + k ∨ (g0.right < n + k ∧ ∃ b, st1.env g0.right = WRef.const b)) →
            ∃ b, (if g0.right < n + k then st.env g0.right else WRef.const false) = WRef.const b := by
          rintro (hge | ⟨hlt, b, hb⟩)
          · exact ⟨false, by simp [show ¬ g0.right < n + k by omega]⟩
          · rw [hstep_env_lt _ hlt] at hb; exact ⟨b, by simp [hlt, hb]⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hne
          cases hovk : ov (n + k) with
          | none => exact absurd hovk hne
          | some b =>
            dsimp only [st1, compStep]; rw [hovk]; dsimp only
            exact ⟨Finset.mem_insert_self _ _, b, Function.update_self _ _ _⟩
        · intro hLc
          obtain ⟨b, hb⟩ := hLconst hLc
          dsimp only [st1, compStep]
          cases ov (n + k) with
          | some _ => dsimp only; exact Finset.mem_insert_self _ _
          | none =>
            dsimp only; rw [hb]
            cases (if g0.right < n + k then st.env g0.right else WRef.const false) <;>
              exact Finset.mem_insert_self _ _
        · intro hRc
          obtain ⟨b, hb⟩ := hRconst hRc
          dsimp only [st1, compStep]
          cases ov (n + k) with
          | some _ => dsimp only; exact Finset.mem_insert_self _ _
          | none =>
            dsimp only; rw [hb]
            cases (if g0.left < n + k then st.env g0.left else WRef.const false) <;>
              exact Finset.mem_insert_self _ _
        · rintro ⟨_, hr, heq⟩
          dsimp only [st1, compStep]
          cases ov (n + k) with
          | some _ => dsimp only; exact Finset.mem_insert_self _ _
          | none =>
            dsimp only; simp only [hr, ↓reduceIte, heq]
            cases st.env g0.right with
            | const _ => exact Finset.mem_insert_self _ _
            | wire j f => simp
        · rintro ⟨hLc, hRc⟩
          obtain ⟨b1, hb1⟩ := hLconst hLc
          obtain ⟨b2, hb2⟩ := hRconst hRc
          dsimp only [st1, compStep]
          cases ov (n + k) with
          | some b => dsimp only; exact ⟨b, Function.update_self _ _ _⟩
          | none => dsimp only; rw [hb1, hb2]; exact ⟨g0.op b1 b2, Function.update_self _ _ _⟩
        · rintro ⟨b, hlt, hb, hop⟩
          rw [hstep_env_lt _ hlt] at hb
          dsimp only [st1, compStep]
          cases ov (n + k) with
          | some b0 => dsimp only; exact ⟨b0, Function.update_self _ _ _⟩
          | none =>
            dsimp only; simp only [hlt, ↓reduceIte, hb]
            cases (if g0.right < n + k then st.env g0.right else WRef.const false) with
            | const b2 => exact ⟨g0.op b b2, Function.update_self _ _ _⟩
            | wire j2 f2 =>
              refine ⟨g0.op b (xor f2 false), ?_⟩
              dsimp only; rw [Function.update_self]; unfold unaryRef
              have hconst : g0.op b (xor f2 false) = g0.op b (xor f2 true) := by cases f2 <;> simp [hop]
              simp only [hconst, ↓reduceIte]
        · rintro ⟨b, hlt, hb, hop⟩
          rw [hstep_env_lt _ hlt] at hb
          dsimp only [st1, compStep]
          cases ov (n + k) with
          | some b0 => dsimp only; exact ⟨b0, Function.update_self _ _ _⟩
          | none =>
            dsimp only; simp only [hlt, ↓reduceIte, hb]
            cases (if g0.left < n + k then st.env g0.left else WRef.const false) with
            | const b1 => exact ⟨g0.op b1 b, Function.update_self _ _ _⟩
            | wire j1 f1 =>
              refine ⟨g0.op (xor f1 false) b, ?_⟩
              dsimp only; rw [Function.update_self]; unfold unaryRef
              have hconst : g0.op (xor f1 false) b = g0.op (xor f1 true) b := by cases f1 <;> simp [hop]
              simp only [hconst, ↓reduceIte]
    obtain ⟨hskf, henvf, hpf⟩ := ih (k + 1) st1 hgs (by omega) hprev1
    exact ⟨fun j hj => hskf j (hstep_skip j hj),
      fun w hw => (henvf w (by omega)).trans (hstep_env_lt w hw), hpf⟩

private lemma compile_step_props (n : ℕ) (ov : ℕ → Option Bool) (C : BinaryCircuit) :
    let stf := compile n ov C.gates
    (∀ w < n, ∀ b, ov w = some b → stf.env w = WRef.const b) ∧
    StepProps n ov C C.gates.length stf := by
  have h := compileRec_step_props n ov C 0 C.gates (compInit n ov) rfl (Nat.zero_le _)
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  refine ⟨fun w hw b hb => ?_, h.2.2⟩
  change (compileRec n ov 0 C.gates (compInit n ov)).env w = WRef.const b
  rw [h.2.1 w (by omega)]
  simp [compInit, hw, hb]

private lemma compileRec_noDead (n : ℕ) (ov : ℕ → Option Bool) (C : BinaryCircuit)
    (dead : ℕ → Prop)
    (hdead : ∀ w, dead w → w < n ∧
      (ov w ≠ none ∨ ∀ j (hj : j < C.gates.length),
        ((C.gates[j]'hj).left = w ∨ (C.gates[j]'hj).right = w) → ov (n + j) ≠ none))
    (k : ℕ) (rest : List BinaryGate) (st : CompState)
    (hrest : rest = C.gates.drop k) (hk : k ≤ C.gates.length)
    (hgs_nd : ∀ g ∈ st.gs', ¬ dead g.left ∧ ¬ dead g.right)
    (henv_nd : ∀ w < n + k, (¬ dead w ∨ ov w ≠ none) → NoDead dead (st.env w)) :
    let stf := compileRec n ov k rest st
    (∀ g ∈ stf.gs', ¬ dead g.left ∧ ¬ dead g.right) ∧
    (∀ w < n + C.gates.length, (¬ dead w ∨ ov w ≠ none) → NoDead dead (stf.env w)) := by
  induction rest generalizing k st with
  | nil =>
    have hkeq : k = C.gates.length := by
      have hlen := congrArg List.length hrest
      simp only [List.length_nil, List.length_drop] at hlen; omega
    subst hkeq; exact ⟨hgs_nd, henv_nd⟩
  | cons g0 gs ih =>
    have hklt : k < C.gates.length := by
      by_contra hge; rw [List.drop_eq_nil_of_le (by omega)] at hrest; exact List.cons_ne_nil g0 gs hrest
    have hg0 : g0 = C.gates[k] := by rw [List.drop_eq_getElem_cons hklt] at hrest; exact (List.cons.inj hrest).1
    have hgs : gs = C.gates.drop (k + 1) := by rw [List.drop_eq_getElem_cons hklt] at hrest; exact (List.cons.inj hrest).2
    let st1 := compStep n ov k g0 st
    have hunary_nd : ∀ (u : Bool → Bool) (j : ℕ), ¬ dead j → NoDead dead (unaryRef u j) := by
      intro u j hj idx fl he
      rw [unaryRef_wire_idx u j idx fl he]; exact hj
    have hnd_step :
        (∀ g ∈ st1.gs', ¬ dead g.left ∧ ¬ dead g.right) ∧
        (∀ w < n + (k + 1), (¬ dead w ∨ ov w ≠ none) → NoDead dead (st1.env w)) := by
      dsimp only [st1, compStep]
      cases hovk : ov (n + k) with
      | some b =>
        dsimp only
        refine ⟨hgs_nd, fun w hw hwd idx fl hwe => ?_⟩
        by_cases hwk : w = n + k
        · rw [hwk, Function.update_self] at hwe; cases hwe
        · rw [Function.update_of_ne hwk] at hwe; exact henv_nd w (by omega) hwd idx fl hwe
      | none =>
        dsimp only
        have hL_nd : NoDead dead (if g0.left < n + k then st.env g0.left else WRef.const false) := by
          by_cases hlt : g0.left < n + k
          · simp only [hlt, ↓reduceIte]
            apply henv_nd g0.left hlt
            by_cases hd : dead g0.left
            · rcases (hdead g0.left hd).2 with hov' | hread
              · exact Or.inr hov'
              · exact absurd hovk (hread k hklt (Or.inl (by rw [← hg0])))
            · exact Or.inl hd
          · simp only [hlt, ↓reduceIte]; intro idx fl he; cases he
        have hR_nd : NoDead dead (if g0.right < n + k then st.env g0.right else WRef.const false) := by
          by_cases hlt : g0.right < n + k
          · simp only [hlt, ↓reduceIte]
            apply henv_nd g0.right hlt
            by_cases hd : dead g0.right
            · rcases (hdead g0.right hd).2 with hov' | hread
              · exact Or.inr hov'
              · exact absurd hovk (hread k hklt (Or.inr (by rw [← hg0])))
            · exact Or.inl hd
          · simp only [hlt, ↓reduceIte]; intro idx fl he; cases he
        generalize hL : (if g0.left < n + k then st.env g0.left else WRef.const false) = rL at hL_nd ⊢
        generalize hR : (if g0.right < n + k then st.env g0.right else WRef.const false) = rR at hR_nd ⊢
        cases rL with
        | const b1 =>
          cases rR with
          | const b2 =>
            dsimp only
            refine ⟨hgs_nd, fun w hw hwd idx fl hwe => ?_⟩
            by_cases hwk : w = n + k
            · rw [hwk, Function.update_self] at hwe; cases hwe
            · rw [Function.update_of_ne hwk] at hwe; exact henv_nd w (by omega) hwd idx fl hwe
          | wire j2 f2 =>
            dsimp only
            have hj2 : ¬ dead j2 := hR_nd j2 f2 rfl
            refine ⟨hgs_nd, fun w hw hwd idx fl hwe => ?_⟩
            by_cases hwk : w = n + k
            · rw [hwk, Function.update_self] at hwe; exact hunary_nd _ j2 hj2 idx fl hwe
            · rw [Function.update_of_ne hwk] at hwe; exact henv_nd w (by omega) hwd idx fl hwe
        | wire j1 f1 =>
          have hj1 : ¬ dead j1 := hL_nd j1 f1 rfl
          cases rR with
          | const b2 =>
            dsimp only
            refine ⟨hgs_nd, fun w hw hwd idx fl hwe => ?_⟩
            by_cases hwk : w = n + k
            · rw [hwk, Function.update_self] at hwe; exact hunary_nd _ j1 hj1 idx fl hwe
            · rw [Function.update_of_ne hwk] at hwe; exact henv_nd w (by omega) hwd idx fl hwe
          | wire j2 f2 =>
            dsimp only
            have hj2 : ¬ dead j2 := hR_nd j2 f2 rfl
            by_cases hjeq : j1 = j2
            · simp only [hjeq, ↓reduceIte]
              refine ⟨hgs_nd, fun w hw hwd idx fl hwe => ?_⟩
              by_cases hwk : w = n + k
              · rw [hwk, Function.update_self] at hwe; exact hunary_nd _ j2 hj2 idx fl hwe
              · rw [Function.update_of_ne hwk] at hwe; exact henv_nd w (by omega) hwd idx fl hwe
            · simp only [hjeq, ↓reduceIte]
              refine ⟨fun g hg => ?_, fun w hw hwd idx fl hwe => ?_⟩
              · rcases List.mem_append.mp hg with hg1 | hg2
                · exact hgs_nd g hg1
                · rw [List.mem_singleton.mp hg2]; exact ⟨hj1, hj2⟩
              · by_cases hwk : w = n + k
                · rw [hwk, Function.update_self] at hwe
                  injection hwe with h1 _; rw [← h1]
                  intro hd; have := (hdead _ hd).1; omega
                · rw [Function.update_of_ne hwk] at hwe; exact henv_nd w (by omega) hwd idx fl hwe
    exact ih (k + 1) st1 hgs (by omega) hnd_step.1 hnd_step.2

private lemma compile_noDead (n : ℕ) (ov : ℕ → Option Bool) (C : BinaryCircuit)
    (dead : ℕ → Prop)
    (hdead : ∀ w, dead w → w < n ∧
      (ov w ≠ none ∨ ∀ j (hj : j < C.gates.length),
        ((C.gates[j]'hj).left = w ∨ (C.gates[j]'hj).right = w) → ov (n + j) ≠ none)) :
    let stf := compile n ov C.gates
    (∀ g ∈ stf.gs', ¬ dead g.left ∧ ¬ dead g.right) ∧
    (∀ w < n + C.gates.length, (¬ dead w ∨ ov w ≠ none) → NoDead dead (stf.env w)) := by
  exact compileRec_noDead n ov C dead hdead 0 C.gates (compInit n ov) rfl (Nat.zero_le _)
    (fun _ h => nomatch h)
    (fun w hw hwd idx fl he => by
      simp only [compInit, Nat.add_zero] at hw he
      simp only [hw, ↓reduceIte] at he
      cases hovw : ov w with
      | some _ => rw [hovw] at he; cases he
      | none =>
        rw [hovw] at he
        injection he with h1 _
        rw [← h1]
        rcases hwd with hnd | hne
        · exact hnd
        · exact absurd hovw hne)

private lemma foldl_eq_of_noDead {n : ℕ} (dead : ℕ → Prop) (_hdead_lt : ∀ w, dead w → w < n)
    (gs : List BinaryGate) (hgs : ∀ g ∈ gs, ¬ dead g.left ∧ ¬ dead g.right)
    (W1 W2 : List Bool) (hlen : W1.length = W2.length) (hn : n ≤ W1.length)
    (hagree : ∀ w, ¬ dead w → W1.getD w false = W2.getD w false) :
    ∀ w, ¬ dead w → (gs.foldl bstep W1).getD w false = (gs.foldl bstep W2).getD w false := by
  induction gs generalizing W1 W2 with
  | nil => exact hagree
  | cons g gs ih =>
    have hg := hgs g (List.mem_cons_self ..)
    have hgs' : ∀ g' ∈ gs, ¬ dead g'.left ∧ ¬ dead g'.right :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    simp only [List.foldl_cons]
    apply ih hgs' (bstep W1 g) (bstep W2 g) (by simp [bstep, hlen]) (by simp [bstep]; omega)
    intro w hnd
    by_cases hw : w < W1.length
    · simp only [bstep]
      rw [List.getD_append W1 _ false w hw, List.getD_append W2 _ false w (by omega)]
      exact hagree w hnd
    · by_cases hweq : w = W1.length
      · subst hweq
        simp only [bstep]
        rw [List.getD_append_right W1 _ false W1.length (le_refl _), hlen,
            List.getD_append_right W2 _ false W2.length (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero]
        rw [hagree g.left hg.1, hagree g.right hg.2]
      · rw [List.getD_eq_default _ _ (by simp [bstep]; omega),
            List.getD_eq_default _ _ (by simp [bstep]; omega)]

private lemma evalWRef_eq_of_noDead {n : ℕ} (dead : ℕ → Prop) (hdead_lt : ∀ w, dead w → w < n)
    (gs : List BinaryGate) (hgs : ∀ g ∈ gs, ¬ dead g.left ∧ ¬ dead g.right)
    (x x' : Fin n → Bool) (hagree : ∀ i : Fin n, ¬ dead i.val → x i = x' i)
    (r : WRef) (hr : NoDead dead r) :
    evalWRef (gs.foldl bstep (List.ofFn x)) r = evalWRef (gs.foldl bstep (List.ofFn x')) r := by
  cases r with
  | const b => rfl
  | wire idx fl =>
    simp only [evalWRef]
    congr 1
    apply foldl_eq_of_noDead dead hdead_lt gs hgs (List.ofFn x) (List.ofFn x')
      (by simp) (by simp) (fun w hnd => by
        by_cases hw : w < n
        · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
          simp only [List.getElem_ofFn]
          exact hagree ⟨w, hw⟩ hnd
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      idx (hr idx fl rfl)

private lemma compile_circuit {n : ℕ} (C : BinaryCircuit) (ov : ℕ → Option Bool)
    (dead : ℕ → Prop)
    (hdead : ∀ w, dead w → w < n ∧
      (ov w ≠ none ∨ ∀ j (hj : j < C.gates.length),
        ((C.gates[j]'hj).left = w ∨ (C.gates[j]'hj).right = w) → ov (n + j) ≠ none))
    (hout_nd : ¬ dead C.output ∨ ov C.output ≠ none)
    (f' : (Fin n → Bool) → Bool)
    (hf0 : f' (fun _ => false) = false)
    (hf1 : ∃ x : Fin n → Bool, f' x = true)
    (hsim : ∀ x : Fin n → Bool, ∃ x' : Fin n → Bool,
      (∀ i : Fin n, ¬ dead i.val → x' i = x i) ∧
      (∀ w b, ov w = some b → wval C x' w = b) ∧
      C.eval (List.ofFn x') = f' x) :
    HasBinarySize n f' (C.size - (compile n ov C.gates).skipped.card) ∧
    (∀ b, (compile n ov C.gates).env C.output ≠ WRef.const b) := by
  let stf := compile n ov C.gates
  obtain ⟨hcard, hbound, hval⟩ := compile_spec n ov C
  obtain ⟨hgs_nd, henv_nd⟩ := compile_noDead n ov C dead hdead
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    obtain ⟨x1, hx1⟩ := hf1
    obtain ⟨x', _, _, hev⟩ := hsim x1
    have h0 : C.eval (List.ofFn x') = false := wval_ge C x' C.output (by omega)
    rw [h0] at hev; rw [hx1] at hev; exact Bool.false_ne_true hev
  have heval_all : ∀ x : Fin n → Bool,
      evalWRef (stf.gs'.foldl bstep (List.ofFn x)) (stf.env C.output) = f' x := by
    intro x
    obtain ⟨x', hag, hov', hev⟩ := hsim x
    rw [evalWRef_eq_of_noDead dead (fun w hw => (hdead w hw).1) stf.gs' hgs_nd x x'
      (fun i hi => (hag i hi).symm) (stf.env C.output) (henv_nd C.output hout_lt hout_nd)]
    rw [hval x' hov' C.output hout_lt]
    exact hev
  have hnot_const : ∀ b, stf.env C.output ≠ WRef.const b := by
    intro b hb
    have h0 := heval_all (fun _ => false)
    obtain ⟨x1, hx1⟩ := hf1
    have h1 := heval_all x1
    rw [hb] at h0 h1; simp only [evalWRef] at h0 h1
    rw [hf0] at h0; rw [hx1] at h1
    rw [h0] at h1; exact Bool.false_ne_true h1
  refine ⟨?_, hnot_const⟩
  cases hro : stf.env C.output with
  | const b => exact absurd hro (hnot_const b)
  | wire idx fl =>
    have hidx : idx < n + stf.gs'.length := hbound C.output hout_lt idx fl hro
    have hsz : stf.gs'.length = C.size - (compile n ov C.gates).skipped.card := by
      dsimp only [stf, BinaryCircuit.size] at hcard ⊢; omega
    cases fl with
    | false =>
      refine ⟨⟨stf.gs', idx⟩, hsz.le, fun x => ?_⟩
      have h := heval_all x
      rw [hro] at h; simp only [evalWRef, Bool.false_xor] at h
      exact h
    | true =>
      by_cases hlt : idx < n
      · exfalso
        have h0 := heval_all (fun _ => false)
        rw [hro] at h0; simp only [evalWRef, Bool.true_xor] at h0
        have hget : (stf.gs'.foldl bstep (List.ofFn (fun _ : Fin n => false))).getD idx false = false := by
          rw [foldl_prefix _ _ idx (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
          simp
        rw [hget, hf0] at h0; exact Bool.false_ne_true h0.symm
      · have hm : idx - n < stf.gs'.length := by omega
        obtain ⟨C', hC'sz, hC'ev⟩ := flip_last_gate (n := n) stf.gs' (idx - n) hm
        refine ⟨C', by omega, fun x => ?_⟩
        rw [hC'ev x]
        have h := heval_all x
        rw [hro] at h
        simp only [evalWRef, Bool.true_xor] at h
        have hadd : n + (idx - n) = idx := by omega
        rw [hadd]
        exact h

private lemma deleteGate {n : ℕ} (C : BinaryCircuit) (k : ℕ) (hk : k < C.gates.length)
    (hunused_out : C.output ≠ n + k)
    (hunused_gate : ∀ j (hj : j < C.gates.length),
      (C.gates[j]'hj).left ≠ n + k ∧ (C.gates[j]'hj).right ≠ n + k) :
    ∃ C' : BinaryCircuit, C'.size = C.size - 1 ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let sh : ℕ → ℕ := fun w => if w < n + k then w else w - 1
  let gs' : List BinaryGate :=
    (C.gates.eraseIdx k).map (fun g => ⟨g.op, sh g.left, sh g.right⟩)
  let C' : BinaryCircuit := ⟨gs', sh C.output⟩
  have hlen : C'.gates.length = C.gates.length - 1 := by
    simp [C', gs', List.length_eraseIdx, hk]
  have hsh_lt : ∀ j r, j < C.gates.length → j ≠ k → r ≠ n + k →
      (sh r < sh (n + j) ↔ r < n + j) := by
    intro j r _ hjk hr
    dsimp only [sh]
    split_ifs <;> omega
  have hget_lt : ∀ j (hj : j < k), C'.gates[j]'(by omega) =
      ⟨(C.gates[j]'(by omega)).op, sh (C.gates[j]'(by omega)).left, sh (C.gates[j]'(by omega)).right⟩ := by
    intro j hj
    have hidx : (C.gates.eraseIdx k)[j]'(by rw [List.length_eraseIdx_of_lt hk]; omega) = C.gates[j]'(by omega) := by
      rw [List.getElem_eraseIdx]; simp [hj]
    simp only [C', gs', List.getElem_map, hidx]
  have hget_gt : ∀ j (hj1 : k < j) (hj2 : j < C.gates.length), C'.gates[j - 1]'(by omega) =
      ⟨(C.gates[j]'hj2).op, sh (C.gates[j]'hj2).left, sh (C.gates[j]'hj2).right⟩ := by
    intro j hj1 hj2
    have hidx : (C.gates.eraseIdx k)[j - 1]'(by rw [List.length_eraseIdx_of_lt hk]; omega) = C.gates[j]'hj2 := by
      rw [List.getElem_eraseIdx]; simp [show ¬ j - 1 < k by omega]
      congr 1; omega
    simp only [C', gs', List.getElem_map, hidx]
  have hwval : ∀ x : Fin n → Bool, ∀ w : ℕ, w ≠ n + k → wval C' x (sh w) = wval C x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwne
      by_cases hwn : w < n
      · have hshw : sh w = w := by dsimp only [sh]; simp [show w < n + k by omega]
        rw [hshw]
        exact (wval_input C' x ⟨w, hwn⟩).trans (wval_input C x ⟨w, hwn⟩).symm
      · by_cases hwge : n + C.gates.length ≤ w
        · have hshge : n + C'.gates.length ≤ sh w := by dsimp only [sh]; split_ifs <;> omega
          rw [wval_ge C' x (sh w) hshge, wval_ge C x w hwge]
        · let j := w - n
          have hj_eq : w = n + j := by omega
          have hj_lt : j < C.gates.length := by omega
          have hjk : j ≠ k := by omega
          have hgj_ne := hunused_gate j hj_lt
          have hstep : ∀ g' : BinaryGate,
              g' = ⟨(C.gates[j]'hj_lt).op, sh (C.gates[j]'hj_lt).left, sh (C.gates[j]'hj_lt).right⟩ →
              wval C' x (sh (n + j)) =
                g'.op (if g'.left < sh (n + j) then wval C' x g'.left else false)
                      (if g'.right < sh (n + j) then wval C' x g'.right else false) →
              wval C' x (sh w) = wval C x w := by
            intro g' hg' hC'g
            rw [hj_eq, hC'g, wval_gate C x j hj_lt, hg']
            dsimp only
            have hL : (if sh (C.gates[j]'hj_lt).left < sh (n + j) then wval C' x (sh (C.gates[j]'hj_lt).left) else false) =
                if (C.gates[j]'hj_lt).left < n + j then wval C x (C.gates[j]'hj_lt).left else false := by
              simp only [hsh_lt j _ hj_lt hjk hgj_ne.1]
              split_ifs with hl
              · exact ih _ (by omega) hgj_ne.1
              · rfl
            have hR : (if sh (C.gates[j]'hj_lt).right < sh (n + j) then wval C' x (sh (C.gates[j]'hj_lt).right) else false) =
                if (C.gates[j]'hj_lt).right < n + j then wval C x (C.gates[j]'hj_lt).right else false := by
              simp only [hsh_lt j _ hj_lt hjk hgj_ne.2]
              split_ifs with hr
              · exact ih _ (by omega) hgj_ne.2
              · rfl
            rw [hL, hR]
          by_cases hjl : j < k
          · have hshj : sh (n + j) = n + j := by dsimp only [sh]; simp [show n + j < n + k by omega]
            apply hstep (C'.gates[j]'(by omega)) (hget_lt j hjl)
            rw [hshj]; exact wval_gate C' x j (by omega)
          · have hjg : k < j := by omega
            have hshj : sh (n + j) = n + (j - 1) := by dsimp only [sh]; simp [show ¬ n + j < n + k by omega]; omega
            apply hstep (C'.gates[j - 1]'(by omega)) (hget_gt j hjg hj_lt)
            rw [hshj]; exact wval_gate C' x (j - 1) (by omega)
  refine ⟨C', hlen, fun x => hwval x C.output hunused_out⟩

private def IsMinCircuit {n : ℕ} (f : (Fin n → Bool) → Bool) (C : BinaryCircuit) : Prop :=
  (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) ∧
  ∀ C' : BinaryCircuit, (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = f x) → C.size ≤ C'.size

private lemma exists_minCircuit {n : ℕ} {f : (Fin n → Bool) → Bool} {s : ℕ}
    (h : HasBinarySize n f s) :
    ∃ C : BinaryCircuit, C.size ≤ s ∧ IsMinCircuit f C := by
  classical
  have hex : ∃ m, HasBinarySize n f m := ⟨s, h⟩
  let m0 := Nat.find hex
  have hm0_le : m0 ≤ s := Nat.find_min' hex h
  obtain ⟨C, hCsz, hCev⟩ := Nat.find_spec hex
  refine ⟨C, by omega, hCev, fun C' hC'ev => ?_⟩
  have hle : m0 ≤ C'.size := Nat.find_min' hex ⟨C', le_refl _, hC'ev⟩
  omega

private lemma minCircuit_no_skip {n : ℕ} {f : (Fin n → Bool) → Bool} {C : BinaryCircuit}
    (hmin : IsMinCircuit f C) (hf0 : f (fun _ => false) = false) (hf1 : ∃ x, f x = true) :
    (compile n (fun _ => none) C.gates).skipped = ∅ := by
  have hcomp := compile_circuit C (fun _ => none) (fun _ => False) (fun _ h => False.elim h)
    (Or.inl id) f hf0 hf1 (fun x => ⟨x, fun _ _ => rfl, (fun _ _ h => by cases h), hmin.1 x⟩)
  obtain ⟨C', hC'sz, hC'ev⟩ := hcomp.1
  have hle := hmin.2 C' hC'ev
  have hcard0 : (compile n (fun _ => none) C.gates).skipped.card = 0 := by
    have h1 := (compile_spec n (fun _ => none) C).1
    dsimp only [BinaryCircuit.size] at hle hC'sz
    omega
  exact Finset.card_eq_zero.mp hcard0

private lemma minCircuit_wellFormed {n : ℕ} {f : (Fin n → Bool) → Bool} {C : BinaryCircuit}
    (hmin : IsMinCircuit f C) (hf0 : f (fun _ => false) = false) (hf1 : ∃ x, f x = true) :
    (∀ k (hk : k < C.gates.length), (C.gates[k]'hk).left < n + k ∧ (C.gates[k]'hk).right < n + k ∧
      (C.gates[k]'hk).left ≠ (C.gates[k]'hk).right) ∧
    (∀ k (_ : k < C.gates.length), C.output = n + k ∨
      ∃ j, ∃ hj : j < C.gates.length, (C.gates[j]'hj).left = n + k ∨ (C.gates[j]'hj).right = n + k) := by
  have hsk : (compile n (fun _ => none) C.gates).skipped = ∅ := minCircuit_no_skip hmin hf0 hf1
  have hsp := (compile_step_props n (fun _ => none) C).2
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hpk := hsp k hk C.gates[k] (List.getElem?_eq_getElem hk)
    have hL : (C.gates[k]'hk).left < n + k := by
      by_contra hge
      have hmem := hpk.2.1 (Or.inl (by omega))
      rw [hsk] at hmem; exact Finset.notMem_empty k hmem
    have hR : (C.gates[k]'hk).right < n + k := by
      by_contra hge
      have hmem := hpk.2.2.1 (Or.inl (by omega))
      rw [hsk] at hmem; exact Finset.notMem_empty k hmem
    have hne : (C.gates[k]'hk).left ≠ (C.gates[k]'hk).right := by
      intro heq
      have hmem := hpk.2.2.2.1 ⟨hL, hR, heq⟩
      rw [hsk] at hmem; exact Finset.notMem_empty k hmem
    exact ⟨hL, hR, hne⟩
  · by_contra hnot
    push Not at hnot
    obtain ⟨hout, hgates⟩ := hnot
    obtain ⟨C', hC'sz, hC'ev⟩ := deleteGate C k hk hout hgates
    have hle := hmin.2 C' (fun x => (hC'ev x).trans (hmin.1 x))
    dsimp only [BinaryCircuit.size] at hle hC'sz
    omega

private lemma replaceGate_eval {n : ℕ} (C : BinaryCircuit) (k : ℕ) (hk : k < C.gates.length)
    (g' : BinaryGate)
    (heq : ∀ x : Fin n → Bool,
      g'.op (if g'.left < n + k then wval C x g'.left else false)
            (if g'.right < n + k then wval C x g'.right else false) =
      (C.gates[k]'hk).op (if (C.gates[k]'hk).left < n + k then wval C x (C.gates[k]'hk).left else false)
                         (if (C.gates[k]'hk).right < n + k then wval C x (C.gates[k]'hk).right else false)) :
    let C' : BinaryCircuit := ⟨C.gates.set k g', C.output⟩
    C'.size = C.size ∧ ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let C' : BinaryCircuit := ⟨C.gates.set k g', C.output⟩
  have hlen : C'.gates.length = C.gates.length := List.length_set
  have hwval : ∀ x : Fin n → Bool, ∀ w : ℕ, wval C' x w = wval C x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hwn : w < n
      · exact (wval_input C' x ⟨w, hwn⟩).trans (wval_input C x ⟨w, hwn⟩).symm
      · by_cases hwge : n + C.gates.length ≤ w
        · rw [wval_ge C' x w (by omega), wval_ge C x w hwge]
        · let j := w - n
          have hj_eq : w = n + j := by omega
          have hj_lt : j < C.gates.length := by omega
          rw [hj_eq, wval_gate C' x j (by omega), wval_gate C x j hj_lt]
          have hrew : ∀ r : ℕ,
              (if r < n + j then wval C' x r else false) =
              (if r < n + j then wval C x r else false) := fun r => by
            split_ifs with hr
            · exact ih r (by omega)
            · rfl
          by_cases hjk : j = k
          · subst hjk
            have hset : C'.gates[j]'(by omega) = g' := List.getElem_set_self (by simp [hj_lt])
            rw [hset, hrew g'.left, hrew g'.right]; exact heq x
          · have hset : C'.gates[j]'(by omega) = C.gates[j]'hj_lt := List.getElem_set_ne (Ne.symm hjk) (by simp [hj_lt])
            rw [hset, hrew, hrew]
  exact ⟨hlen, fun x => hwval x C.output⟩

private lemma minCircuit_gate_depends {n : ℕ} {f : (Fin n → Bool) → Bool} {C : BinaryCircuit}
    (hmin : IsMinCircuit f C) (hf0 : f (fun _ => false) = false) (hf1 : ∃ x, f x = true)
    (k : ℕ) (hk : k < C.gates.length) :
    (∃ b : Bool, (C.gates[k]'hk).op false b ≠ (C.gates[k]'hk).op true b) ∧
    (∃ a : Bool, (C.gates[k]'hk).op a false ≠ (C.gates[k]'hk).op a true) := by
  refine ⟨?_, ?_⟩
  · by_contra hno
    push Not at hno
    let g := C.gates[k]'hk
    let g' : BinaryGate := ⟨fun _ b => g.op false b, g.right, g.right⟩
    have hrep := replaceGate_eval C k hk g' (fun x => by
      dsimp only [g', g]
      cases (if (C.gates[k]'hk).left < n + k then wval C x (C.gates[k]'hk).left else false)
      · rfl
      · exact hno _)
    let C' : BinaryCircuit := ⟨C.gates.set k g', C.output⟩
    have hmin' : IsMinCircuit f C' := ⟨fun x => (hrep.2 x).trans (hmin.1 x),
      fun D hD => by
        have := hmin.2 D hD
        dsimp only [BinaryCircuit.size] at this ⊢
        rw [List.length_set]; exact this⟩
    have hwf' := (minCircuit_wellFormed hmin' hf0 hf1).1 k (by simp [C', hk])
    have hset : C'.gates[k]'(by simp [C', hk]) = g' := List.getElem_set_self (by simp [hk])
    rw [hset] at hwf'
    exact hwf'.2.2 rfl
  · by_contra hno
    push Not at hno
    let g := C.gates[k]'hk
    let g' : BinaryGate := ⟨fun a _ => g.op a false, g.left, g.left⟩
    have hrep := replaceGate_eval C k hk g' (fun x => by
      dsimp only [g', g]
      cases (if (C.gates[k]'hk).right < n + k then wval C x (C.gates[k]'hk).right else false)
      · rfl
      · exact hno _)
    let C' : BinaryCircuit := ⟨C.gates.set k g', C.output⟩
    have hmin' : IsMinCircuit f C' := ⟨fun x => (hrep.2 x).trans (hmin.1 x),
      fun D hD => by
        have := hmin.2 D hD
        dsimp only [BinaryCircuit.size] at this ⊢
        rw [List.length_set]; exact this⟩
    have hwf' := (minCircuit_wellFormed hmin' hf0 hf1).1 k (by simp [C', hk])
    have hset : C'.gates[k]'(by simp [C', hk]) = g' := List.getElem_set_self (by simp [hk])
    rw [hset] at hwf'
    exact hwf'.2.2 rfl

private lemma wval_indep_of_unread {n : ℕ} (C : BinaryCircuit) (i : Fin n)
    (hunread : ∀ k (hk : k < C.gates.length),
      (C.gates[k]'hk).left ≠ i.val ∧ (C.gates[k]'hk).right ≠ i.val)
    (x y : Fin n → Bool) (hxy : ∀ j : Fin n, j ≠ i → x j = y j) :
    ∀ w : ℕ, w ≠ i.val → wval C x w = wval C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hne
    by_cases hwn : w < n
    · rw [wval_input C x ⟨w, hwn⟩, wval_input C y ⟨w, hwn⟩]
      exact hxy ⟨w, hwn⟩ (fun h => hne (congrArg Fin.val h))
    · by_cases hwge : n + C.gates.length ≤ w
      · rw [wval_ge C x w hwge, wval_ge C y w hwge]
      · let k := w - n
        have hk_eq : w = n + k := by omega
        have hk_lt : k < C.gates.length := by omega
        have hkn := hunread k hk_lt
        rw [hk_eq, wval_gate C x k hk_lt, wval_gate C y k hk_lt]
        have hL : (if (C.gates[k]'hk_lt).left < n + k then wval C x (C.gates[k]'hk_lt).left else false) =
            if (C.gates[k]'hk_lt).left < n + k then wval C y (C.gates[k]'hk_lt).left else false := by
          split_ifs with hl
          · exact ih _ (by omega) hkn.1
          · rfl
        have hR : (if (C.gates[k]'hk_lt).right < n + k then wval C x (C.gates[k]'hk_lt).right else false) =
            if (C.gates[k]'hk_lt).right < n + k then wval C y (C.gates[k]'hk_lt).right else false := by
          split_ifs with hr
          · exact ih _ (by omega) hkn.2
          · rfl
        rw [hL, hR]

private def IsEssential {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)

private lemma essential_read {n : ℕ} {f : (Fin n → Bool) → Bool} {C : BinaryCircuit}
    (hev : ∀ x, C.eval (List.ofFn x) = f x) (i : Fin n) (hess : IsEssential f i) :
    C.output = i.val ∨
      ∃ k, ∃ hk : k < C.gates.length, (C.gates[k]'hk).left = i.val ∨ (C.gates[k]'hk).right = i.val := by
  by_contra hnot
  push Not at hnot
  obtain ⟨hout, hgates⟩ := hnot
  obtain ⟨x, hx⟩ := hess
  have h1 := wval_indep_of_unread C i hgates (Function.update x i true) (Function.update x i false)
    (fun j hj => by simp [Function.update_of_ne hj]) C.output hout
  change C.eval (List.ofFn (Function.update x i true)) = C.eval (List.ofFn (Function.update x i false)) at h1
  rw [hev, hev] at h1
  exact hx h1

private lemma ess_card_le_size_add_one {n : ℕ} {f : (Fin n → Bool) → Bool} {C : BinaryCircuit}
    (hmin : IsMinCircuit f C) (hf0 : f (fun _ => false) = false) (hf1 : ∃ x, f x = true)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, IsEssential f i) :
    S.card ≤ C.size + 1 := by
  let W1 : Finset ℕ := S.image Fin.val
  let W2 : Finset ℕ := (Finset.range C.gates.length).image (n + ·)
  have hdisj : Disjoint W1 W2 := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rcases Finset.mem_image.mp hw1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hw2 with ⟨k, _, hk⟩
    omega
  have hWcard : (W1 ∪ W2).card = S.card + C.gates.length := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => by omega),
      Finset.card_range]
  let Used : Finset ℕ := (Finset.range C.gates.length).biUnion (fun k =>
    if hk : k < C.gates.length then {(C.gates[k]'hk).left, (C.gates[k]'hk).right} else ∅)
  have hUsed_card : Used.card ≤ 2 * C.gates.length := by
    calc Used.card
      _ ≤ ∑ k ∈ Finset.range C.gates.length,
          (if hk : k < C.gates.length then ({(C.gates[k]'hk).left, (C.gates[k]'hk).right} : Finset ℕ) else ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Finset.range C.gates.length, 2 := by
        apply Finset.sum_le_sum
        intro k _
        split_ifs
        · exact (Finset.card_insert_le _ _).trans (by simp)
        · simp
      _ = 2 * C.gates.length := by simp [mul_comm]
  have hsub : (W1 ∪ W2).erase C.output ⊆ Used := by
    intro w hw
    rw [Finset.mem_erase] at hw
    obtain ⟨hne, hmem⟩ := hw
    have hex : ∃ k, ∃ hk : k < C.gates.length, (C.gates[k]'hk).left = w ∨ (C.gates[k]'hk).right = w := by
      rcases Finset.mem_union.mp hmem with h1 | h2
      · rcases Finset.mem_image.mp h1 with ⟨i, hiS, rfl⟩
        rcases essential_read hmin.1 i (hS i hiS) with hout | hg
        · exact absurd hout.symm hne
        · exact hg
      · rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
        rw [Finset.mem_range] at hk
        rcases (minCircuit_wellFormed hmin hf0 hf1).2 k hk with hout | hg
        · exact absurd hout.symm hne
        · exact hg
    obtain ⟨k, hk, hlr⟩ := hex
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    simp only [hk, ↓reduceDIte]
    rcases hlr with hl | hr
    · rw [← hl]; exact Finset.mem_insert_self _ _
    · rw [← hr]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hle1 : (W1 ∪ W2).card - 1 ≤ ((W1 ∪ W2).erase C.output).card := by
    by_cases hm : C.output ∈ W1 ∪ W2
    · rw [Finset.card_erase_of_mem hm]
    · rw [Finset.erase_eq_of_notMem hm]; omega
  have hle2 : ((W1 ∪ W2).erase C.output).card ≤ Used.card := Finset.card_le_card hsub
  change S.card ≤ C.gates.length + 1
  omega

end BinCircuitCore

section ForestGraph

private lemma adj_symm {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (h : G.Adj u v) :
    G.Adj v u :=
  (G.adj_comm u v).mp h

private def fGA {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (x : Fin n → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

private lemma fGA_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) :
    fGA G A (fun _ => false) = false := by
  simp [fGA]

private lemma fGA_exists_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (hne : A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) :
    ∃ x : Fin n → Bool, fGA G A x = true := by
  refine ⟨fun _ => true, ?_⟩
  simp only [fGA, decide_eq_true_eq]
  rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
  · exact Or.inl ⟨a, ha, trivial⟩
  · exact Or.inr ⟨u, v, huv, trivial, trivial⟩

private lemma fGA_essential_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha : a ∈ A) :
    IsEssential (fGA G A) a := by
  refine ⟨fun _ => false, ?_⟩
  have h1 : fGA G A (Function.update (fun _ : Fin n => false) a true) = true := by
    simp only [fGA, decide_eq_true_eq]
    exact Or.inl ⟨a, ha, by simp⟩
  have h0 : fGA G A (Function.update (fun _ : Fin n => false) a false) = false := by
    have hfn : Function.update (fun _ : Fin n => false) a false = fun _ => false := by
      ext i; by_cases hi : i = a <;> simp [hi]
    rw [hfn, fGA_false]
  rw [h1, h0]; decide

private lemma fGA_essential_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (hA_iso : ∀ a ∈ A, ∀ v, ¬ G.Adj a v)
    (u v : Fin n) (huv : G.Adj u v) :
    IsEssential (fGA G A) u := by
  have hunev : u ≠ v := G.ne_of_adj huv
  let x : Fin n → Bool := fun i => decide (i = v)
  refine ⟨x, ?_⟩
  have h1 : fGA G A (Function.update x u true) = true := by
    simp only [fGA, decide_eq_true_eq]
    exact Or.inr ⟨u, v, huv, by simp, by simp [x, hunev.symm]⟩
  have h0 : fGA G A (Function.update x u false) = false := by
    simp only [fGA, decide_eq_false_iff_not]
    rintro (⟨a, ha, hax⟩ | ⟨p, q, hpq, hpx, hqx⟩)
    · by_cases hau : a = u
      · subst hau; simp at hax
      · rw [Function.update_of_ne hau] at hax
        have hav : a = v := by simpa [x] using hax
        subst hav; exact hA_iso a ha u (adj_symm huv)
    · have hpv : p = v := by
        by_cases hpu : p = u
        · subst hpu; simp at hpx
        · rw [Function.update_of_ne hpu] at hpx; simpa [x] using hpx
      have hqv : q = v := by
        by_cases hqu : q = u
        · subst hqu; simp at hqx
        · rw [Function.update_of_ne hqu] at hqx; simpa [x] using hqx
      subst hpv; subst hqv; exact G.ne_of_adj hpq rfl
  rw [h1, h0]; decide

private def delVert {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a ≠ v ∧ b ≠ v
  symm := ⟨fun _ _ h => ⟨adj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

private lemma delVert_le {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : delVert G v ≤ G :=
  fun _ _ h => h.1

private lemma delVert_isAcyclic {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (hacyc : G.IsAcyclic) : (delVert G v).IsAcyclic := by
  intro u c hc
  rw [SimpleGraph.Walk.isCycle_def] at hc
  let f : delVert G v →g G := SimpleGraph.Hom.ofLE (delVert_le G v)
  apply hacyc (c.map f)
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_map]
    have hid : (Sym2.map f) = id := by ext e; induction e using Sym2.ind with | _ a b => rfl
    rw [hid, List.map_id]
    exact hc.1.edges_nodup
  · intro hnil
    exact hc.2.1 (by cases c <;> simp at hnil ⊢)
  · rw [SimpleGraph.Walk.support_map]
    have hid : (f : Fin n → Fin n) = id := rfl
    rw [hid, List.map_id]
    exact hc.2.2

-- Circuit builder helpers for the upper bound
private def appendGate (gs : List BinaryGate) (g : BinaryGate) : List BinaryGate :=
  gs ++ [g]

private lemma wval_append_prefix {n : ℕ} (gs gs2 : List BinaryGate) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + gs.length) :
    wval ⟨gs ++ gs2, 0⟩ x w = wval ⟨gs, 0⟩ x w := by
  unfold wval BinaryCircuit.wires
  change ((gs ++ gs2).foldl bstep (List.ofFn x)).getD w false =
    (gs.foldl bstep (List.ofFn x)).getD w false
  rw [List.foldl_append, foldl_prefix gs2 _ w (by rw [foldl_len]; simp; omega)]

private lemma wval_append_last {n : ℕ} (gs : List BinaryGate) (g : BinaryGate)
    (hL : g.left < n + gs.length) (hR : g.right < n + gs.length) (x : Fin n → Bool) :
    wval ⟨gs ++ [g], 0⟩ x (n + gs.length) = g.op (wval ⟨gs, 0⟩ x g.left) (wval ⟨gs, 0⟩ x g.right) := by
  have hg := wval_gate ⟨gs ++ [g], 0⟩ x gs.length (by simp)
  dsimp only at hg
  simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero] at hg
  rw [hg]
  simp only [hL, hR, ↓reduceIte]
  rw [wval_append_prefix gs [g] x g.left hL, wval_append_prefix gs [g] x g.right hR]

private def addOrList (n : ℕ) (gs : List BinaryGate) : List ℕ → List BinaryGate × ℕ
  | [] => (gs, 0)
  | [w] => (gs, w)
  | w :: w2 :: ws =>
    let (gs1, o1) := addOrList n gs (w2 :: ws)
    (gs1 ++ [⟨(· || ·), w, o1⟩], n + gs1.length)

private lemma addOrList_spec (n : ℕ) (gs : List BinaryGate) (ws : List ℕ) (hne : ws ≠ [])
    (hws : ∀ w ∈ ws, w < n + gs.length) :
    let res := addOrList n gs ws
    (∃ ext, res.1 = gs ++ ext ∧ ext.length = ws.length - 1) ∧
    res.2 < n + res.1.length ∧
    ∀ x : Fin n → Bool, wval ⟨res.1, 0⟩ x res.2 = ws.any (fun w => wval ⟨gs, 0⟩ x w) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons w tail ih =>
    cases tail with
    | nil =>
      refine ⟨⟨[], by simp [addOrList], rfl⟩, ?_, fun x => ?_⟩
      · simpa [addOrList] using hws w (List.mem_cons_self ..)
      · simp [addOrList]
    | cons w2 ws' =>
      have ih' := ih (List.cons_ne_nil w2 ws') (fun u hu => hws u (List.mem_cons_of_mem _ hu))
      dsimp only at ih'
      obtain ⟨⟨ext, hext, hexlen⟩, ho1_lt, ho1_ev⟩ := ih'
      have hw_lt : w < n + gs.length := hws w (List.mem_cons_self ..)
      let gs1 := (addOrList n gs (w2 :: ws')).1
      let o1 := (addOrList n gs (w2 :: ws')).2
      have hres1 : (addOrList n gs (w :: w2 :: ws')).1 = gs1 ++ [⟨(· || ·), w, o1⟩] := by
        simp [addOrList, gs1, o1]
      have hres2 : (addOrList n gs (w :: w2 :: ws')).2 = n + gs1.length := by
        simp [addOrList, gs1]
      have hw_lt1 : w < n + gs1.length := by change w < n + (addOrList n gs (w2 :: ws')).1.length; rw [hext]; simp; omega
      refine ⟨⟨ext ++ [⟨(· || ·), w, o1⟩], ?_, ?_⟩, ?_, fun x => ?_⟩
      · rw [hres1]; change (addOrList n gs (w2 :: ws')).1 ++ _ = _; rw [hext, List.append_assoc]
      · simp [hexlen]
      · rw [hres1, hres2]; simp
      · rw [hres1, hres2, wval_append_last gs1 ⟨(· || ·), w, o1⟩ hw_lt1 ho1_lt x]
        have hwg : wval ⟨gs1, 0⟩ x w = wval ⟨gs, 0⟩ x w := by
          change wval ⟨(addOrList n gs (w2 :: ws')).1, 0⟩ x w = _
          rw [hext]; exact wval_append_prefix gs ext x w hw_lt
        rw [hwg, ho1_ev x]
        simp

private def ownedNbrs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (s : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => G.Adj s u ∧ (u ∉ S ∨ s < u))

private lemma ownedNbrs_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (t : ℕ) (hSvc : CoverPromise.IsVertexCover G S) (hSc : S.card = t)
    (hmin : ∀ S', CoverPromise.IsVertexCover G S' → t ≤ S'.card)
    (s : Fin n) (hs : s ∈ S) : (ownedNbrs G S s).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have hall : ∀ u, G.Adj s u → u ∈ S := by
    intro u huv
    by_contra huS
    have hmem : u ∈ ownedNbrs G S s := by
      simp [ownedNbrs, huv, huS]
    rw [hemp] at hmem; exact Finset.notMem_empty u hmem
  have hvc' : CoverPromise.IsVertexCover G (S.erase s) := by
    intro a b hab
    by_cases has : a = s
    · subst has
      exact Or.inr (Finset.mem_erase.mpr ⟨(G.ne_of_adj hab).symm, hall b hab⟩)
    · by_cases hbs : b = s
      · subst hbs
        exact Or.inl (Finset.mem_erase.mpr ⟨G.ne_of_adj hab, hall a (adj_symm hab)⟩)
      · rcases hSvc a b hab with haS | hbS
        · exact Or.inl (Finset.mem_erase.mpr ⟨has, haS⟩)
        · exact Or.inr (Finset.mem_erase.mpr ⟨hbs, hbS⟩)
  have hle := hmin (S.erase s) hvc'
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨s, hs⟩
  rw [Finset.card_erase_of_mem hs] at hle
  omega

private lemma sum_ownedNbrs_eq_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hSvc : CoverPromise.IsVertexCover G S) :
    ∑ s ∈ S, (ownedNbrs G S s).card = G.edgeFinset.card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro ⟨s, u⟩ hp
    rw [Finset.mem_sigma] at hp
    simp only [ownedNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact G.mem_edgeFinset.mpr hp.2.1
  · intro ⟨s1, u1⟩ hp1 ⟨s2, u2⟩ hp2 heq
    rw [Finset.mem_sigma] at hp1 hp2
    simp only [ownedNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exfalso
      rcases hp1.2.2 with h1 | hlt1
      · exact h1 hp2.1
      · rcases hp2.2.2 with h2 | hlt2
        · exact h2 hp1.1
        · exact lt_asymm hlt1 hlt2
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := G.mem_edgeFinset.mp he
      have hne : a ≠ b := G.ne_of_adj hab
      rcases hSvc a b hab with haS | hbS
      · by_cases hbS : b ∈ S
        · rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact ⟨⟨a, b⟩, Finset.mem_sigma.mpr ⟨haS, by simp [ownedNbrs, hab, hlt]⟩, rfl⟩
          · exact ⟨⟨b, a⟩, Finset.mem_sigma.mpr ⟨hbS, by simp [ownedNbrs, adj_symm hab, hgt]⟩, Sym2.eq_swap⟩
        · exact ⟨⟨a, b⟩, Finset.mem_sigma.mpr ⟨haS, by simp [ownedNbrs, hab, hbS]⟩, rfl⟩
      · by_cases haS : a ∈ S
        · rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact ⟨⟨a, b⟩, Finset.mem_sigma.mpr ⟨haS, by simp [ownedNbrs, hab, hlt]⟩, rfl⟩
          · exact ⟨⟨b, a⟩, Finset.mem_sigma.mpr ⟨hbS, by simp [ownedNbrs, adj_symm hab, hgt]⟩, Sym2.eq_swap⟩
        · exact ⟨⟨b, a⟩, Finset.mem_sigma.mpr ⟨hbS, by simp [ownedNbrs, adj_symm hab, haS]⟩, Sym2.eq_swap⟩

private noncomputable def addStars (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (gs : List BinaryGate) : List (Fin n) → List BinaryGate × List ℕ
  | [] => (gs, [])
  | s :: ss =>
    let nbrs := (ownedNbrs G S s).toList.map Fin.val
    let (gs1, o1) := addOrList n gs nbrs
    let gs2 := gs1 ++ [⟨(· && ·), s.val, o1⟩]
    let wStar := n + gs1.length
    let (gs3, ws) := addStars n G S gs2 ss
    (gs3, wStar :: ws)

private lemma addStars_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (gs : List BinaryGate) (ss : List (Fin n))
    (hne : ∀ s ∈ ss, (ownedNbrs G S s).Nonempty) :
    let res := addStars n G S gs ss
    (∃ ext, res.1 = gs ++ ext ∧ ext.length = (ss.map (fun s => (ownedNbrs G S s).card)).sum) ∧
    res.2.length = ss.length ∧
    (∀ w ∈ res.2, w < n + res.1.length) ∧
    ∀ x : Fin n → Bool,
      res.2.any (fun w => wval ⟨res.1, 0⟩ x w) =
        ss.any (fun s => x s && (ownedNbrs G S s).toList.any (fun u => x u)) := by
  induction ss generalizing gs with
  | nil =>
    exact ⟨⟨[], by simp [addStars], by simp⟩, rfl, (fun _ h => by cases h), fun _ => rfl⟩
  | cons s ss ih =>
    have hsne : (ownedNbrs G S s).Nonempty := hne s (List.mem_cons_self ..)
    have hlist_ne : (ownedNbrs G S s).toList.map Fin.val ≠ [] := by
      intro hemp
      rw [List.map_eq_nil_iff, Finset.toList_eq_nil] at hemp
      exact hsne.ne_empty hemp
    have hor := addOrList_spec n gs ((ownedNbrs G S s).toList.map Fin.val) hlist_ne
      (fun w hw => by
        rcases List.mem_map.mp hw with ⟨u, _, rfl⟩
        omega)
    dsimp only at hor
    obtain ⟨⟨ext1, hext1, hext1_len⟩, ho1_lt, ho1_ev⟩ := hor
    let gs1 := (addOrList n gs ((ownedNbrs G S s).toList.map Fin.val)).1
    let o1 := (addOrList n gs ((ownedNbrs G S s).toList.map Fin.val)).2
    let gs2 := gs1 ++ [⟨(· && ·), s.val, o1⟩]
    let wStar := n + gs1.length
    have hih := ih gs2 (fun s' hs' => hne s' (List.mem_cons_of_mem _ hs'))
    dsimp only at hih
    obtain ⟨⟨ext2, hext2, hext2_len⟩, hlen2, hlt2, hev2⟩ := hih
    have hcard_pos : 1 ≤ (ownedNbrs G S s).card := Finset.card_pos.mpr hsne
    have hres1 : (addStars n G S gs (s :: ss)).1 = (addStars n G S gs2 ss).1 := rfl
    have hres2 : (addStars n G S gs (s :: ss)).2 = wStar :: (addStars n G S gs2 ss).2 := rfl
    have hgs1_eq : gs1 = gs ++ ext1 := hext1
    have hgs2_eq : gs2 = gs ++ (ext1 ++ [⟨(· && ·), s.val, o1⟩]) := by
      simp [gs2, hgs1_eq, List.append_assoc]
    have hfull_eq : (addStars n G S gs (s :: ss)).1 = gs ++ ((ext1 ++ [⟨(· && ·), s.val, o1⟩]) ++ ext2) := by
      rw [hres1, hext2, hgs2_eq, List.append_assoc]
    have hwStar_lt2 : wStar < n + gs2.length := by simp [wStar, gs2]
    refine ⟨⟨(ext1 ++ [⟨(· && ·), s.val, o1⟩]) ++ ext2, hfull_eq, ?_⟩, ?_, ?_, fun x => ?_⟩
    · simp only [List.length_append, List.length_singleton, hext1_len, hext2_len,
        List.length_map, Finset.length_toList, List.map_cons, List.sum_cons]
      omega
    · simp [hres2, hlen2]
    · intro w hw
      rw [hres2] at hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · rw [hres1, hext2]; simp; omega
      · exact hlt2 w hw'
    · rw [hres2, List.any_cons, hres1, hev2 x]
      congr 1
      rw [hext2, wval_append_prefix gs2 ext2 x wStar hwStar_lt2]
      dsimp only [wStar, gs2]
      have hs_lt : s.val < n + gs1.length := by have := s.isLt; omega
      rw [wval_append_last gs1 ⟨(· && ·), s.val, o1⟩ hs_lt ho1_lt x]
      dsimp only
      rw [wval_input ⟨gs1, 0⟩ x s, ho1_ev x]
      congr 1
      rw [List.any_map]
      congr 1
      funext u
      exact wval_input ⟨gs, 0⟩ x u

private lemma upper_bound {n t s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n))
    (hne : A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v)
    (hvc_ex : ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hvc_min : ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card)
    (hs : A.card + G.edgeFinset.card + t ≤ s + 1) :
    HasBinarySize n (fGA G A) s := by
  obtain ⟨S, hSvc, hSc⟩ := hvc_ex
  have hstar := addStars_spec G S [] S.toList
    (fun s hs' => ownedNbrs_nonempty G S t hSvc hSc hvc_min s (Finset.mem_toList.mp hs'))
  dsimp only at hstar
  obtain ⟨⟨extS, hextS, hextS_len⟩, hws_len, hws_lt, hws_ev⟩ := hstar
  let gsS := (addStars n G S [] S.toList).1
  let wsS := (addStars n G S [] S.toList).2
  have hgsS_len : gsS.length = G.edgeFinset.card := by
    change (addStars n G S [] S.toList).1.length = G.edgeFinset.card
    rw [hextS, List.nil_append, hextS_len]
    have hsum : (S.toList.map (fun s => (ownedNbrs G S s).card)).sum = ∑ s ∈ S, (ownedNbrs G S s).card := by
      rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList S]
      simp
    rw [hsum, sum_ownedNbrs_eq_edges G S hSvc]
  let allW : List ℕ := A.toList.map Fin.val ++ wsS
  have hallW_len : allW.length = A.card + t := by
    simp [allW, wsS, hws_len, hSc, Finset.length_toList]
  have hpos_At : 1 ≤ A.card + t := by
    rcases hne with hA | ⟨u, v, huv⟩
    · have := Finset.card_pos.mpr hA; omega
    · rcases hSvc u v huv with hu | hv
      · have := Finset.card_pos.mpr ⟨u, hu⟩; omega
      · have := Finset.card_pos.mpr ⟨v, hv⟩; omega
  have hallW_ne : allW ≠ [] := by
    intro hemp
    have h0 : A.card + t = 0 := by rw [← hallW_len, hemp]; rfl
    omega
  have hor := addOrList_spec n gsS allW hallW_ne (fun w hw => by
    rcases List.mem_append.mp hw with h1 | h2
    · rcases List.mem_map.mp h1 with ⟨a, _, rfl⟩; omega
    · exact hws_lt w h2)
  dsimp only at hor
  obtain ⟨⟨extO, hextO, hextO_len⟩, _, ho_ev⟩ := hor
  refine ⟨⟨(addOrList n gsS allW).1, (addOrList n gsS allW).2⟩, ?_, fun x => ?_⟩
  · change (addOrList n gsS allW).1.length ≤ s
    rw [hextO, List.length_append, hgsS_len, hextO_len, hallW_len]
    omega
  · change wval ⟨(addOrList n gsS allW).1, 0⟩ x (addOrList n gsS allW).2 = fGA G A x
    rw [ho_ev x]
    simp only [allW, List.any_append, List.any_map]
    have hA_any : (A.toList.any (fun a => wval ⟨gsS, 0⟩ x a.val)) = decide (∃ a ∈ A, x a = true) := by
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, Finset.mem_toList, decide_eq_true_eq]
      constructor
      · rintro ⟨a, ha, hx⟩; rw [wval_input ⟨gsS, 0⟩ x a] at hx; exact ⟨a, ha, hx⟩
      · rintro ⟨a, ha, hx⟩; exact ⟨a, ha, by rw [wval_input ⟨gsS, 0⟩ x a]; exact hx⟩
    have hG_any : (wsS.any (fun w => wval ⟨gsS, 0⟩ x w)) =
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
      rw [hws_ev x, Bool.eq_iff_iff]
      simp only [List.any_eq_true, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨s, hs, hxs, u, hu, hxu⟩
        simp only [ownedNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        exact ⟨s, u, hu.1, hxs, hxu⟩
      · rintro ⟨u, v, huv, hxu, hxv⟩
        have hne_uv : u ≠ v := G.ne_of_adj huv
        rcases hSvc u v huv with huS | hvS
        · by_cases hvS : v ∈ S
          · rcases lt_or_gt_of_ne hne_uv with hlt | hgt
            · exact ⟨u, huS, hxu, v, by simp [ownedNbrs, huv, hlt], hxv⟩
            · exact ⟨v, hvS, hxv, u, by simp [ownedNbrs, adj_symm huv, hgt], hxu⟩
          · exact ⟨u, huS, hxu, v, by simp [ownedNbrs, huv, hvS], hxv⟩
        · by_cases huS : u ∈ S
          · rcases lt_or_gt_of_ne hne_uv with hlt | hgt
            · exact ⟨u, huS, hxu, v, by simp [ownedNbrs, huv, hlt], hxv⟩
            · exact ⟨v, hvS, hxv, u, by simp [ownedNbrs, adj_symm huv, hgt], hxu⟩
          · exact ⟨v, hvS, hxv, u, by simp [ownedNbrs, adj_symm huv, huS], hxu⟩
    change ((A.toList.any (fun a => wval ⟨gsS, 0⟩ x a.val)) || (wsS.any (fun w => wval ⟨gsS, 0⟩ x w))) = fGA G A x
    rw [hA_any, hG_any]
    simp [fGA]

-- Vertex cover and edge count under vertex deletion
private lemma vc_del_leaf_parent {n t : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hleaf : ∀ z, G.Adj u z → z = v)
    (hvc_ex : ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hvc_min : ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) :
    1 ≤ t ∧
    (∃ S' : Finset (Fin n), CoverPromise.IsVertexCover (delVert G v) S' ∧ S'.card = t - 1) ∧
    (∀ S' : Finset (Fin n), CoverPromise.IsVertexCover (delVert G v) S' → t - 1 ≤ S'.card) := by
  obtain ⟨S, hSvc, hSc⟩ := hvc_ex
  have ht1 : 1 ≤ t := by
    rcases hSvc u v huv with hu | hv
    · have := Finset.card_pos.mpr ⟨u, hu⟩; omega
    · have := Finset.card_pos.mpr ⟨v, hv⟩; omega
  refine ⟨ht1, ?_, ?_⟩
  · by_cases hvS : v ∈ S
    · refine ⟨S.erase v, fun a b hab => ?_, by rw [Finset.card_erase_of_mem hvS, hSc]⟩
      rcases hSvc a b hab.1 with ha | hb
      · exact Or.inl (Finset.mem_erase.mpr ⟨hab.2.1, ha⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hab.2.2, hb⟩)
    · have huS : u ∈ S := (hSvc u v huv).resolve_right hvS
      refine ⟨S.erase u, fun a b hab => ?_, by rw [Finset.card_erase_of_mem huS, hSc]⟩
      have hau : a ≠ u := fun h => by subst h; exact hab.2.2 (hleaf b hab.1)
      have hbu : b ≠ u := fun h => by subst h; exact hab.2.1 (hleaf a (adj_symm hab.1))
      rcases hSvc a b hab.1 with ha | hb
      · exact Or.inl (Finset.mem_erase.mpr ⟨hau, ha⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hbu, hb⟩)
  · intro S' hS'vc
    have hvcG : CoverPromise.IsVertexCover G (insert v S') := by
      intro a b hab
      by_cases hav : a = v
      · exact Or.inl (by subst hav; exact Finset.mem_insert_self _ _)
      · by_cases hbv : b = v
        · exact Or.inr (by subst hbv; exact Finset.mem_insert_self _ _)
        · rcases hS'vc a b ⟨hab, hav, hbv⟩ with ha | hb
          · exact Or.inl (Finset.mem_insert_of_mem ha)
          · exact Or.inr (Finset.mem_insert_of_mem hb)
    have hle := hvc_min (insert v S') hvcG
    have hcard := Finset.card_insert_le v S'
    omega

private lemma vc_del_twin_leaf {n t : ℕ} (G : SimpleGraph (Fin n)) (u1 u2 v : Fin n)
    (hne : u1 ≠ u2) (h1 : G.Adj u1 v) (h2 : G.Adj u2 v)
    (hl1 : ∀ z, G.Adj u1 z → z = v) (hl2 : ∀ z, G.Adj u2 z → z = v)
    (hvc_ex : ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hvc_min : ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) :
    (∃ S' : Finset (Fin n), CoverPromise.IsVertexCover (delVert G u1) S' ∧ S'.card = t) ∧
    (∀ S' : Finset (Fin n), CoverPromise.IsVertexCover (delVert G u1) S' → t ≤ S'.card) := by
  obtain ⟨S, hSvc, hSc⟩ := hvc_ex
  refine ⟨⟨S, fun a b hab => hSvc a b hab.1, hSc⟩, ?_⟩
  intro S' hS'vc
  have hvne1 : v ≠ u1 := (G.ne_of_adj h1).symm
  have hu2v : (delVert G u1).Adj u2 v := ⟨h2, hne.symm, hvne1⟩
  by_cases hvS : v ∈ S'
  · apply hvc_min S'
    intro a b hab
    by_cases ha1 : a = u1
    · subst ha1; rw [hl1 b hab]; exact Or.inr hvS
    · by_cases hb1 : b = u1
      · subst hb1; rw [hl1 a (adj_symm hab)]; exact Or.inl hvS
      · exact hS'vc a b ⟨hab, ha1, hb1⟩
  · have hu2S : u2 ∈ S' := (hS'vc u2 v hu2v).resolve_right hvS
    let S2 := insert v (S'.erase u2)
    have hvc2 : CoverPromise.IsVertexCover G S2 := by
      intro a b hab
      by_cases hav : a = v
      · exact Or.inl (by subst hav; exact Finset.mem_insert_self _ _)
      · by_cases hbv : b = v
        · exact Or.inr (by subst hbv; exact Finset.mem_insert_self _ _)
        · have ha1 : a ≠ u1 := fun h => by subst h; exact hbv (hl1 b hab)
          have hb1 : b ≠ u1 := fun h => by subst h; exact hav (hl1 a (adj_symm hab))
          have ha2 : a ≠ u2 := fun h => by subst h; exact hbv (hl2 b hab)
          have hb2 : b ≠ u2 := fun h => by subst h; exact hav (hl2 a (adj_symm hab))
          rcases hS'vc a b ⟨hab, ha1, hb1⟩ with ha | hb
          · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ha2, ha⟩))
          · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hb2, hb⟩))
    have hle := hvc_min S2 hvc2
    have hcard : S2.card ≤ S'.card := by
      calc S2.card ≤ (S'.erase u2).card + 1 := Finset.card_insert_le v _
        _ = S'.card := by rw [Finset.card_erase_of_mem hu2S]; have := Finset.card_pos.mpr ⟨u2, hu2S⟩; omega
    omega

private lemma edgeFinset_delVert_deg1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v u : Fin n) [DecidableRel (delVert G v).Adj]
    (huv : G.Adj v u) (hdeg : ∀ z, G.Adj v z → z = u) :
    (delVert G v).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : G.edgeFinset = insert s(v, u) (delVert G v).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_insert, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.eq_iff]
      dsimp only [delVert]
      constructor
      · intro hab
        by_cases hav : a = v
        · subst hav; exact Or.inl (Or.inl ⟨rfl, hdeg b hab⟩)
        · by_cases hbv : b = v
          · subst hbv; exact Or.inl (Or.inr ⟨hdeg a (adj_symm hab), rfl⟩)
          · exact Or.inr ⟨hab, hav, hbv⟩
      · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨hab, _, _⟩)
        · exact huv
        · exact adj_symm huv
        · exact hab
  have hnot : s(v, u) ∉ (delVert G v).edgeFinset := by
    intro h; rw [SimpleGraph.mem_edgeFinset] at h; exact h.2.1 rfl
  rw [heq, Finset.card_insert_of_notMem hnot]

private lemma edgeFinset_delVert_deg2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v u w : Fin n) [DecidableRel (delVert G v).Adj]
    (huw : u ≠ w) (hvu : G.Adj v u) (hvw : G.Adj v w) (hdeg : ∀ z, G.Adj v z → z = u ∨ z = w) :
    (delVert G v).edgeFinset.card + 2 = G.edgeFinset.card := by
  have heq : G.edgeFinset = insert s(v, u) (insert s(v, w) (delVert G v).edgeFinset) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_insert, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.eq_iff]
      dsimp only [delVert]
      constructor
      · intro hab
        by_cases hav : a = v
        · subst hav
          rcases hdeg b hab with rfl | rfl
          · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
        · by_cases hbv : b = v
          · subst hbv
            rcases hdeg a (adj_symm hab) with rfl | rfl
            · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
            · exact Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))
          · exact Or.inr (Or.inr ⟨hab, hav, hbv⟩)
      · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨hab, _, _⟩)
        · exact hvu
        · exact adj_symm hvu
        · exact hvw
        · exact adj_symm hvw
        · exact hab
  have hnot1 : s(v, w) ∉ (delVert G v).edgeFinset := by
    intro h; rw [SimpleGraph.mem_edgeFinset] at h; exact h.2.1 rfl
  have hne_e : s(v, u) ≠ s(v, w) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨_, rfl⟩ | ⟨hvw', _⟩
    · exact huw rfl
    · exact G.ne_of_adj hvw hvw'
  have hnot2 : s(v, u) ∉ insert s(v, w) (delVert G v).edgeFinset := by
    rw [Finset.mem_insert]
    rintro (he | hmem)
    · exact hne_e he
    · rw [SimpleGraph.mem_edgeFinset] at hmem; exact hmem.2.1 rfl
  rw [heq, Finset.card_insert_of_notMem hnot2, Finset.card_insert_of_notMem hnot1]

-- Forest structure via longest simple path
private lemma path_of_chain {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) (xs : List (Fin n))
    (hnodup : (x :: xs).Nodup) (hchain : (x :: xs).IsChain G.Adj) (y : Fin n) (hy : y ∈ xs) :
    ∃ p : G.Walk x y, p.IsPath ∧ 1 ≤ p.length ∧ ∀ z ∈ p.support, z ∈ x :: xs := by
  induction xs generalizing x with
  | nil => cases hy
  | cons x1 xs' ih =>
    have hadj : G.Adj x x1 := by
      rw [List.isChain_cons_cons] at hchain; exact hchain.1
    have hch' : (x1 :: xs').IsChain G.Adj := by
      rw [List.isChain_cons_cons] at hchain; exact hchain.2
    have hnd' : (x1 :: xs').Nodup := (List.nodup_cons.mp hnodup).2
    have hx_not : x ∉ x1 :: xs' := (List.nodup_cons.mp hnodup).1
    by_cases hy1 : y = x1
    · subst hy1
      refine ⟨SimpleGraph.Walk.cons hadj .nil, ?_, by simp, fun z hz => ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        simp [G.ne_of_adj hadj]
      · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · have hy' : y ∈ xs' := (List.mem_cons.mp hy).resolve_left hy1
      obtain ⟨p', hp'path, hp'len, hp'sup⟩ := ih x1 hnd' hch' hy'
      have hx_not_p : x ∉ p'.support := fun h => hx_not (hp'sup x h)
      refine ⟨SimpleGraph.Walk.cons hadj p', ?_, by simp, fun z hz => ?_⟩
      · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons, List.nodup_cons]
        exact ⟨hx_not_p, hp'path.support_nodup⟩
      · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hp'sup z hz')

private lemma no_chord_of_acyclic {n : ℕ} (G : SimpleGraph (Fin n)) (hacyc : G.IsAcyclic)
    (a b : Fin n) (t : List (Fin n))
    (hnodup : (a :: b :: t).Nodup) (hchain : (a :: b :: t).IsChain G.Adj)
    (c : Fin n) (hc : c ∈ t) : ¬ G.Adj a c := by
  intro hac
  have hab : G.Adj a b := (List.isChain_cons_cons.mp hchain).1
  have hch' : (b :: t).IsChain G.Adj := (List.isChain_cons_cons.mp hchain).2
  have hnd' : (b :: t).Nodup := (List.nodup_cons.mp hnodup).2
  have ha_not : a ∉ b :: t := (List.nodup_cons.mp hnodup).1
  have hb_not : b ∉ t := (List.nodup_cons.mp hnd').1
  have hcb : c ≠ b := fun h => hb_not (h ▸ hc)
  obtain ⟨p, hppath, _, hpsup⟩ := path_of_chain G b t hnd' hch' c hc
  have ha_not_p : a ∉ p.support := fun h => ha_not (hpsup a h)
  let cyc : G.Walk c c := SimpleGraph.Walk.cons (adj_symm hac) (SimpleGraph.Walk.cons hab p)
  apply hacyc cyc
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, by simp [cyc], ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    simp only [cyc, SimpleGraph.Walk.edges_cons, List.nodup_cons]
    refine ⟨?_, ?_, hppath.isTrail.edges_nodup⟩
    · intro hmem
      rcases List.mem_cons.mp hmem with heq | hpe
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hca, _⟩ | ⟨hcb', _⟩
        · exact G.ne_of_adj hac hca.symm
        · exact hcb hcb'
      · exact ha_not_p (SimpleGraph.Walk.snd_mem_support_of_mem_edges p hpe)
    · intro hpe
      exact ha_not_p (SimpleGraph.Walk.fst_mem_support_of_mem_edges p hpe)
  · simp only [cyc, SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_cons]
    exact ⟨ha_not_p, hppath.support_nodup⟩

private lemma head_is_leaf_of_longest_path {n : ℕ} (G : SimpleGraph (Fin n)) (hacyc : G.IsAcyclic)
    (u v : Fin n) (rest : List (Fin n))
    (hnd : (u :: v :: rest).Nodup) (hch : (u :: v :: rest).IsChain G.Adj)
    (hmax : ∀ L : List (Fin n), L.Nodup → L.IsChain G.Adj → L.length ≤ (u :: v :: rest).length) :
    ∀ z : Fin n, G.Adj u z → z = v := by
  intro z huz
  by_contra hzv
  by_cases hzmem : z ∈ u :: v :: rest
  · rcases List.mem_cons.mp hzmem with rfl | h2
    · exact G.ne_of_adj huz rfl
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact hzv rfl
      · exact no_chord_of_acyclic G hacyc u v rest hnd hch z h3 huz
  · have hnd' : (z :: u :: v :: rest).Nodup := List.nodup_cons.mpr ⟨hzmem, hnd⟩
    have hch' : (z :: u :: v :: rest).IsChain G.Adj :=
      List.isChain_cons_cons.mpr ⟨adj_symm huz, hch⟩
    have hle := hmax (z :: u :: v :: rest) hnd' hch'
    simp at hle

private lemma exists_longest_path {n : ℕ} (G : SimpleGraph (Fin n))
    (hedge : ∃ a b : Fin n, G.Adj a b) :
    ∃ L : List (Fin n), L.Nodup ∧ L.IsChain G.Adj ∧ 2 ≤ L.length ∧
      ∀ L' : List (Fin n), L'.Nodup → L'.IsChain G.Adj → L'.length ≤ L.length := by
  classical
  have hle_n : ∀ L : List (Fin n), L.Nodup → L.length ≤ n := fun L hnd => by
    have := hnd.length_le_card; simpa using this
  let P : ℕ → Prop := fun k => ∃ L : List (Fin n), L.Nodup ∧ L.IsChain G.Adj ∧ L.length = k
  obtain ⟨a, b, hab⟩ := hedge
  have hP2 : P 2 := ⟨[a, b], by simp [G.ne_of_adj hab], by simp [hab], rfl⟩
  let k0 := Nat.findGreatest P n
  have h2_le_n : 2 ≤ n := by
    have := hle_n [a, b] (by simp [G.ne_of_adj hab]); simpa using this
  have h2_le_k0 : 2 ≤ k0 := Nat.le_findGreatest h2_le_n hP2
  have hk0_spec : P k0 := Nat.findGreatest_spec (m := 2) h2_le_n hP2
  obtain ⟨L, hLnd, hLch, hLlen⟩ := hk0_spec
  refine ⟨L, hLnd, hLch, by omega, fun L' hnd' hch' => ?_⟩
  rw [hLlen]
  exact Nat.le_findGreatest (hle_n L' hnd') ⟨L', hnd', hch', rfl⟩

private lemma forest_structure {n : ℕ} (G : SimpleGraph (Fin n)) (hacyc : G.IsAcyclic)
    (hedge : ∃ a b : Fin n, G.Adj a b) :
    (∃ u v : Fin n, G.Adj u v ∧ (∀ z, G.Adj u z → z = v) ∧ (∀ z, G.Adj v z → z = u)) ∨
    (∃ u1 u2 v : Fin n, u1 ≠ u2 ∧ G.Adj u1 v ∧ G.Adj u2 v ∧
      (∀ z, G.Adj u1 z → z = v) ∧ (∀ z, G.Adj u2 z → z = v)) ∨
    (∃ u v w : Fin n, u ≠ w ∧ G.Adj u v ∧ G.Adj v w ∧
      (∀ z, G.Adj u z → z = v) ∧ (∀ z, G.Adj v z → z = u ∨ z = w)) := by
  obtain ⟨L, hLnd, hLch, hLlen, hLmax⟩ := exists_longest_path G hedge
  cases L with
  | nil => simp at hLlen
  | cons u tail =>
    cases tail with
    | nil => simp at hLlen
    | cons v rest =>
      have huv : G.Adj u v := (List.isChain_cons_cons.mp hLch).1
      have hu_leaf : ∀ z, G.Adj u z → z = v :=
        head_is_leaf_of_longest_path G hacyc u v rest hLnd hLch hLmax
      cases rest with
      | nil =>
        refine Or.inl ⟨u, v, huv, hu_leaf, fun z hvz => ?_⟩
        by_contra hzu
        have hnd3 : ([u, v, z] : List (Fin n)).Nodup := by
          simp [G.ne_of_adj huv, Ne.symm hzu, G.ne_of_adj hvz]
        have hch3 : ([u, v, z] : List (Fin n)).IsChain G.Adj := by
          simp [huv, hvz]
        have hle := hLmax [u, v, z] hnd3 hch3
        simp at hle
      | cons w rest' =>
        have hch_v : (v :: w :: rest').IsChain G.Adj := (List.isChain_cons_cons.mp hLch).2
        have hvw : G.Adj v w := (List.isChain_cons_cons.mp hch_v).1
        have hnd_v : (v :: w :: rest').Nodup := (List.nodup_cons.mp hLnd).2
        have hu_not : u ∉ v :: w :: rest' := (List.nodup_cons.mp hLnd).1
        have huw : u ≠ w := fun h => hu_not (by subst h; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
        by_cases hv_extra : ∃ u2 : Fin n, G.Adj v u2 ∧ u2 ≠ u ∧ u2 ≠ w
        · obtain ⟨u2, hvu2, hu2u, hu2w⟩ := hv_extra
          have hu2_not : u2 ∉ v :: w :: rest' := by
            intro hmem
            rcases List.mem_cons.mp hmem with rfl | h2
            · exact G.ne_of_adj hvu2 rfl
            · rcases List.mem_cons.mp h2 with rfl | h3
              · exact hu2w rfl
              · exact no_chord_of_acyclic G hacyc v w rest' hnd_v hch_v u2 h3 hvu2
          have hnd2 : (u2 :: v :: w :: rest').Nodup := List.nodup_cons.mpr ⟨hu2_not, hnd_v⟩
          have hch2 : (u2 :: v :: w :: rest').IsChain G.Adj :=
            List.isChain_cons_cons.mpr ⟨adj_symm hvu2, hch_v⟩
          have hu2_leaf : ∀ z, G.Adj u2 z → z = v :=
            head_is_leaf_of_longest_path G hacyc u2 v (w :: rest') hnd2 hch2
              (fun L' h1 h2 => by simpa using hLmax L' h1 h2)
          exact Or.inr (Or.inl ⟨u, u2, v, hu2u.symm, huv, adj_symm hvu2, hu_leaf, hu2_leaf⟩)
        · push Not at hv_extra
          refine Or.inr (Or.inr ⟨u, v, w, huw, huv, hvw, hu_leaf, fun z hvz => ?_⟩)
          by_cases hzu : z = u
          · exact Or.inl hzu
          · exact Or.inr (hv_extra z hvz hzu)

end ForestGraph

section LowerBound

private lemma bool_op_left_trichotomy (op : Bool → Bool → Bool)
    (hL : ∃ b : Bool, op false b ≠ op true b) (hR : ∃ a : Bool, op a false ≠ op a true) :
    op true false = op true true ∨
    op false false = op false true ∨
    ∀ b : Bool, op false b ≠ op true b := by
  cases h00 : op false false <;> cases h01 : op false true <;>
  cases h10 : op true false <;> cases h11 : op true true <;> simp_all

private lemma bool_op_right_trichotomy (op : Bool → Bool → Bool)
    (hL : ∃ b : Bool, op false b ≠ op true b) (hR : ∃ a : Bool, op a false ≠ op a true) :
    op false true = op true true ∨
    op false false = op true false ∨
    ∀ a : Bool, op a false ≠ op a true := by
  cases h00 : op false false <;> cases h01 : op false true <;>
  cases h10 : op true false <;> cases h11 : op true true <;> simp_all

private lemma output_ne_input_of_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (hA_iso : ∀ a ∈ A, ∀ v, ¬ G.Adj a v)
    (hedge : ∃ p q : Fin n, G.Adj p q)
    (C : BinaryCircuit) (hev : ∀ x, C.eval (List.ofFn x) = fGA G A x) (i : Fin n) :
    C.output ≠ i.val := by
  intro hout
  by_cases hiA : i ∈ A
  · obtain ⟨p, q, hpq⟩ := hedge
    have hip : i ≠ p := fun h => hA_iso i hiA q (h ▸ hpq)
    have hiq : i ≠ q := fun h => hA_iso i hiA p (h ▸ adj_symm hpq)
    let x : Fin n → Bool := fun j => decide (j = p ∨ j = q)
    have hlhs : C.eval (List.ofFn x) = false := by
      change wval C x C.output = false
      rw [hout, wval_input C x i]
      simp [x, hip, hiq]
    have hrhs : fGA G A x = true := by
      simp only [fGA, decide_eq_true_eq]
      exact Or.inr ⟨p, q, hpq, by simp [x], by simp [x]⟩
    have := hev x; rw [hlhs, hrhs] at this; exact Bool.false_ne_true this
  · let x : Fin n → Bool := fun j => decide (j = i)
    have hlhs : C.eval (List.ofFn x) = true := by
      change wval C x C.output = true
      rw [hout, wval_input C x i]
      simp [x]
    have hrhs : fGA G A x = false := by
      simp only [fGA, decide_eq_false_iff_not]
      rintro (⟨a, ha, hax⟩ | ⟨p, q, hpq, hpx, hqx⟩)
      · have hai : a = i := by simpa [x] using hax
        exact hiA (hai ▸ ha)
      · have hpi : p = i := by simpa [x] using hpx
        have hqi : q = i := by simpa [x] using hqx
        subst hpi; subst hqi; exact G.ne_of_adj hpq rfl
    have := hev x; rw [hlhs, hrhs] at this; exact Bool.false_ne_true this.symm

private lemma wval_eq_below_unique_reader {n : ℕ} (C : BinaryCircuit) (u : Fin n)
    (gu : ℕ) (huniq : ∀ k (hk : k < C.gates.length), k ≠ gu →
      (C.gates[k]'hk).left ≠ u.val ∧ (C.gates[k]'hk).right ≠ u.val)
    (x y : Fin n → Bool) (hxy : ∀ j : Fin n, j ≠ u → x j = y j) :
    ∀ w < n + gu, w ≠ u.val → wval C x w = wval C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hne
    by_cases hwn : w < n
    · rw [wval_input C x ⟨w, hwn⟩, wval_input C y ⟨w, hwn⟩]
      exact hxy ⟨w, hwn⟩ (fun h => hne (congrArg Fin.val h))
    · by_cases hwge : n + C.gates.length ≤ w
      · rw [wval_ge C x w hwge, wval_ge C y w hwge]
      · let k := w - n
        have hk_eq : w = n + k := by omega
        have hk_lt : k < C.gates.length := by omega
        have hk_ne : k ≠ gu := by omega
        have hkn := huniq k hk_lt hk_ne
        rw [hk_eq, wval_gate C x k hk_lt, wval_gate C y k hk_lt]
        have hL : (if (C.gates[k]'hk_lt).left < n + k then wval C x (C.gates[k]'hk_lt).left else false) =
            if (C.gates[k]'hk_lt).left < n + k then wval C y (C.gates[k]'hk_lt).left else false := by
          split_ifs with hl
          · exact ih _ (by omega) (by omega) hkn.1
          · rfl
        have hR : (if (C.gates[k]'hk_lt).right < n + k then wval C x (C.gates[k]'hk_lt).right else false) =
            if (C.gates[k]'hk_lt).right < n + k then wval C y (C.gates[k]'hk_lt).right else false := by
          split_ifs with hr
          · exact ih _ (by omega) (by omega) hkn.2
          · rfl
        rw [hL, hR]

private lemma wval_eq_of_uv_bottleneck {n : ℕ} (C : BinaryCircuit) (u v : Fin n) (gu : ℕ)
    (honly : ∀ k (hk : k < C.gates.length), k ≠ gu →
      (C.gates[k]'hk).left ≠ u.val ∧ (C.gates[k]'hk).right ≠ u.val ∧
      (C.gates[k]'hk).left ≠ v.val ∧ (C.gates[k]'hk).right ≠ v.val)
    (x y : Fin n → Bool) (hxy : ∀ j : Fin n, j ≠ u → j ≠ v → x j = y j)
    (hgu_eq : wval C x (n + gu) = wval C y (n + gu)) :
    ∀ w : ℕ, w ≠ u.val → w ≠ v.val → wval C x w = wval C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hnu hnv
    by_cases hwn : w < n
    · rw [wval_input C x ⟨w, hwn⟩, wval_input C y ⟨w, hwn⟩]
      exact hxy ⟨w, hwn⟩ (fun h => hnu (congrArg Fin.val h)) (fun h => hnv (congrArg Fin.val h))
    · by_cases hwge : n + C.gates.length ≤ w
      · rw [wval_ge C x w hwge, wval_ge C y w hwge]
      · let k := w - n
        have hk_eq : w = n + k := by omega
        have hk_lt : k < C.gates.length := by omega
        by_cases hkg : k = gu
        · rw [hk_eq, hkg]; exact hgu_eq
        · have hkn := honly k hk_lt hkg
          rw [hk_eq, wval_gate C x k hk_lt, wval_gate C y k hk_lt]
          have hL : (if (C.gates[k]'hk_lt).left < n + k then wval C x (C.gates[k]'hk_lt).left else false) =
              if (C.gates[k]'hk_lt).left < n + k then wval C y (C.gates[k]'hk_lt).left else false := by
            split_ifs with hl
            · exact ih _ (by omega) hkn.1 hkn.2.2.1
            · rfl
          have hR : (if (C.gates[k]'hk_lt).right < n + k then wval C x (C.gates[k]'hk_lt).right else false) =
              if (C.gates[k]'hk_lt).right < n + k then wval C y (C.gates[k]'hk_lt).right else false := by
            split_ifs with hr
            · exact ih _ (by omega) hkn.2.1 hkn.2.2.2
            · rfl
          rw [hL, hR]

private lemma exists_other_reader_v {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v w : Fin n) (huw : u ≠ w) (huv : G.Adj u v) (hvw : G.Adj v w)
    (C : BinaryCircuit) (hmin : IsMinCircuit (fGA G ∅) C)
    (gu : ℕ) (hgu : gu < C.gates.length)
    (hgu_read : (C.gates[gu]'hgu).left = u.val ∨ (C.gates[gu]'hgu).right = u.val)
    (huniq_u : ∀ k (hk : k < C.gates.length), k ≠ gu →
      (C.gates[k]'hk).left ≠ u.val ∧ (C.gates[k]'hk).right ≠ u.val) :
    ∃ gv, ∃ hgv : gv < C.gates.length, gv ≠ gu ∧
      ((C.gates[gv]'hgv).left = v.val ∨ (C.gates[gv]'hgv).right = v.val) := by
  by_contra hno
  push Not at hno
  have hne_uv : u ≠ v := G.ne_of_adj huv
  have hne_vw : v ≠ w := G.ne_of_adj hvw
  have hout_u : C.output ≠ u.val :=
    output_ne_input_of_edge G ∅ (fun _ h => by cases h) ⟨u, v, huv⟩ C hmin.1 u
  have hout_v : C.output ≠ v.val :=
    output_ne_input_of_edge G ∅ (fun _ h => by cases h) ⟨u, v, huv⟩ C hmin.1 v
  have hv_ess : IsEssential (fGA G ∅) v :=
    fGA_essential_edge G ∅ (fun _ h => by cases h) v u (adj_symm huv)
  have hgu_read_v : (C.gates[gu]'hgu).left = v.val ∨ (C.gates[gu]'hgu).right = v.val := by
    rcases essential_read hmin.1 v hv_ess with hout | ⟨k, hk, hlr⟩
    · exact absurd hout hout_v
    · by_cases hkg : k = gu
      · subst hkg; exact hlr
      · have := hno k hk hkg
        rcases hlr with hl | hr
        · exact absurd hl this.1
        · exact absurd hr this.2
  have honly : ∀ k (hk : k < C.gates.length), k ≠ gu →
      (C.gates[k]'hk).left ≠ u.val ∧ (C.gates[k]'hk).right ≠ u.val ∧
      (C.gates[k]'hk).left ≠ v.val ∧ (C.gates[k]'hk).right ≠ v.val := by
    intro k hk hkg
    exact ⟨(huniq_u k hk hkg).1, (huniq_u k hk hkg).2, (hno k hk hkg).1, (hno k hk hkg).2⟩
  let inp : Bool → Bool → Bool → (Fin n → Bool) := fun bu bv bw i =>
    if i = u then bu else if i = v then bv else if i = w then bw else false
  have hgu_indep_w : ∀ bu bv bw : Bool,
      wval C (inp bu bv bw) (n + gu) = wval C (inp bu bv false) (n + gu) := by
    intro bu bv bw
    rw [wval_gate C _ gu hgu, wval_gate C _ gu hgu]
    have hlr_eq : ∀ r : ℕ, (r = u.val ∨ r = v.val) →
        (if r < n + gu then wval C (inp bu bv bw) r else false) =
        (if r < n + gu then wval C (inp bu bv false) r else false) := by
      rintro r (rfl | rfl)
      · have hlt : u.val < n + gu := by have := u.isLt; omega
        simp only [hlt, ↓reduceIte, wval_input, inp]
      · have hlt : v.val < n + gu := by have := v.isLt; omega
        simp only [hlt, ↓reduceIte, wval_input, inp, hne_uv.symm]
    have hL_uv : (C.gates[gu]'hgu).left = u.val ∨ (C.gates[gu]'hgu).left = v.val := by
      rcases hgu_read with hl | hr
      · exact Or.inl hl
      · rcases hgu_read_v with hvl | hvr
        · exact Or.inr hvl
        · exfalso; exact hne_uv (Fin.ext (hr.symm.trans hvr))
    have hR_uv : (C.gates[gu]'hgu).right = u.val ∨ (C.gates[gu]'hgu).right = v.val := by
      rcases hgu_read with hl | hr
      · rcases hgu_read_v with hvl | hvr
        · exfalso; exact hne_uv (Fin.ext (hl.symm.trans hvl))
        · exact Or.inr hvr
      · exact Or.inl hr
    rw [hlr_eq _ hL_uv, hlr_eq _ hR_uv]
  have hf_00_0 : fGA G ∅ (inp false false false) = false := by
    simp only [fGA, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_false_iff_not]
    rintro ⟨p, q, _, hp, _⟩
    dsimp only [inp] at hp; split_ifs at hp
  have hf_00_1 : fGA G ∅ (inp false false true) = false := by
    simp only [fGA, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_false_iff_not]
    rintro ⟨p, q, hpq, hp, hq⟩
    have hpw : p = w := by dsimp only [inp] at hp; split_ifs at hp; assumption
    have hqw : q = w := by dsimp only [inp] at hq; split_ifs at hq; assumption
    subst hpw; subst hqw; exact G.ne_of_adj hpq rfl
  have hf_01_0 : fGA G ∅ (inp false true false) = false := by
    simp only [fGA, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_false_iff_not]
    rintro ⟨p, q, hpq, hp, hq⟩
    have hpv : p = v := by dsimp only [inp] at hp; split_ifs at hp; assumption
    have hqv : q = v := by dsimp only [inp] at hq; split_ifs at hq; assumption
    subst hpv; subst hqv; exact G.ne_of_adj hpq rfl
  have hf_01_1 : fGA G ∅ (inp false true true) = true := by
    simp only [fGA, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_true_eq]
    exact ⟨v, w, hvw, by simp [inp, hne_uv.symm], by simp [inp, huw.symm, hne_vw.symm]⟩
  have hf_11_0 : fGA G ∅ (inp true true false) = true := by
    simp only [fGA, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [inp], by simp [inp, hne_uv.symm]⟩
  have hcollide : ∀ bu1 bv1 bu2 bv2 bw : Bool,
      wval C (inp bu1 bv1 false) (n + gu) = wval C (inp bu2 bv2 false) (n + gu) →
      fGA G ∅ (inp bu1 bv1 bw) = fGA G ∅ (inp bu2 bv2 bw) := by
    intro bu1 bv1 bu2 bv2 bw heq
    have hgu_bw : wval C (inp bu1 bv1 bw) (n + gu) = wval C (inp bu2 bv2 bw) (n + gu) := by
      rw [hgu_indep_w bu1 bv1 bw, hgu_indep_w bu2 bv2 bw, heq]
    have h1 := wval_eq_of_uv_bottleneck C u v gu honly (inp bu1 bv1 bw) (inp bu2 bv2 bw)
      (fun j hju hjv => by simp [inp, hju, hjv]) hgu_bw C.output hout_u hout_v
    change C.eval (List.ofFn (inp bu1 bv1 bw)) = C.eval (List.ofFn (inp bu2 bv2 bw)) at h1
    rw [hmin.1, hmin.1] at h1
    exact h1
  cases h00 : wval C (inp false false false) (n + gu) <;>
  cases h01 : wval C (inp false true false) (n + gu) <;>
  cases h11 : wval C (inp true true false) (n + gu)
  · have := hcollide false false false true true (h00.trans h01.symm)
    rw [hf_00_1, hf_01_1] at this; exact Bool.false_ne_true this
  · have := hcollide false false false true true (h00.trans h01.symm)
    rw [hf_00_1, hf_01_1] at this; exact Bool.false_ne_true this
  · have := hcollide false false true true false (h00.trans h11.symm)
    rw [hf_00_0, hf_11_0] at this; exact Bool.false_ne_true this
  · have := hcollide false true true true false (h01.trans h11.symm)
    rw [hf_01_0, hf_11_0] at this; exact Bool.false_ne_true this
  · have := hcollide false true true true false (h01.trans h11.symm)
    rw [hf_01_0, hf_11_0] at this; exact Bool.false_ne_true this
  · have := hcollide false false true true false (h00.trans h11.symm)
    rw [hf_00_0, hf_11_0] at this; exact Bool.false_ne_true this
  · have := hcollide false false false true true (h00.trans h01.symm)
    rw [hf_00_1, hf_01_1] at this; exact Bool.false_ne_true this
  · have := hcollide false false false true true (h00.trans h01.symm)
    rw [hf_00_1, hf_01_1] at this; exact Bool.false_ne_true this

private lemma card_ge_two_of_ne {a b : ℕ} {S : Finset ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) : 2 ≤ S.card := by
  have hsub : ({a, b} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hc : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair hne
  have := Finset.card_le_card hsub
  omega

private lemma card_ge_three_of_ne {a b c : ℕ} {S : Finset ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ S.card := by
  have hsub : ({a, b, c} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  have := Finset.card_le_card hsub
  omega

private lemma three_skipped_of_const_gu_v {n : ℕ} {f : (Fin n → Bool) → Bool}
    {C : BinaryCircuit} (hmin : IsMinCircuit f C)
    (hf0 : f (fun _ => false) = false) (hf1 : ∃ x, f x = true)
    (ov : ℕ → Option Bool) (v : Fin n) (gu : ℕ) (hgu : gu < C.gates.length)
    (hnot_const_out : ∀ b, (compile n ov C.gates).env C.output ≠ WRef.const b)
    (hv_const : (compile n ov C.gates).env v.val = WRef.const false)
    (hgu_skip : gu ∈ (compile n ov C.gates).skipped)
    (hgu_const : ∃ b, (compile n ov C.gates).env (n + gu) = WRef.const b)
    (hgv_ex : ∃ gv, ∃ hgv : gv < C.gates.length, gv ≠ gu ∧
      ((C.gates[gv]'hgv).left = v.val ∨ (C.gates[gv]'hgv).right = v.val)) :
    3 ≤ (compile n ov C.gates).skipped.card := by
  let stf := compile n ov C.gates
  have hwf := minCircuit_wellFormed hmin hf0 hf1
  have hsp := (compile_step_props n ov C).2
  obtain ⟨bgu, hbgu⟩ := hgu_const
  have hout_ne_gu : C.output ≠ n + gu := fun h => hnot_const_out bgu (h ▸ hbgu)
  obtain ⟨g2, hg2, hg2_read⟩ := (hwf.2 gu hgu).resolve_left hout_ne_gu
  have hg2_wf := hwf.1 g2 hg2
  have hgu_lt_g2 : gu < g2 := by
    rcases hg2_read with hl | hr <;> omega
  have hg2_sp := hsp g2 hg2 (C.gates[g2]'hg2) (List.getElem?_eq_getElem hg2)
  have hg2_skip : g2 ∈ stf.skipped := by
    rcases hg2_read with hl | hr
    · exact hg2_sp.2.1 (Or.inr ⟨hg2_wf.1, bgu, hl.symm ▸ hbgu⟩)
    · exact hg2_sp.2.2.1 (Or.inr ⟨hg2_wf.2.1, bgu, hr.symm ▸ hbgu⟩)
  obtain ⟨gv, hgv, hgv_ne_gu, hgv_read⟩ := hgv_ex
  have hgv_wf := hwf.1 gv hgv
  have hgv_sp := hsp gv hgv (C.gates[gv]'hgv) (List.getElem?_eq_getElem hgv)
  have hgv_skip : gv ∈ stf.skipped := by
    rcases hgv_read with hl | hr
    · exact hgv_sp.2.1 (Or.inr ⟨hgv_wf.1, false, hl.symm ▸ hv_const⟩)
    · exact hgv_sp.2.2.1 (Or.inr ⟨hgv_wf.2.1, false, hr.symm ▸ hv_const⟩)
  by_cases hgv_eq : gv = g2
  · subst hgv_eq
    have hv_ne_gu : v.val ≠ n + gu := by have := v.isLt; omega
    have hLconst : ∃ b, stf.env (C.gates[gv]'hgv).left = WRef.const b := by
      rcases hg2_read with hl | hr
      · exact ⟨bgu, hl.symm ▸ hbgu⟩
      · rcases hgv_read with hvl | hvr
        · exact ⟨false, hvl.symm ▸ hv_const⟩
        · exact absurd (hvr.symm.trans hr) hv_ne_gu
    have hRconst : ∃ b, stf.env (C.gates[gv]'hgv).right = WRef.const b := by
      rcases hg2_read with hl | hr
      · rcases hgv_read with hvl | hvr
        · exact absurd (hvl.symm.trans hl) hv_ne_gu
        · exact ⟨false, hvr.symm ▸ hv_const⟩
      · exact ⟨bgu, hr.symm ▸ hbgu⟩
    obtain ⟨bg2, hbg2⟩ := hg2_sp.2.2.2.2.1 ⟨Or.inr ⟨hg2_wf.1, hLconst⟩, Or.inr ⟨hg2_wf.2.1, hRconst⟩⟩
    have hout_ne_g2 : C.output ≠ n + gv := fun h => hnot_const_out bg2 (h ▸ hbg2)
    obtain ⟨g3, hg3, hg3_read⟩ := (hwf.2 gv hgv).resolve_left hout_ne_g2
    have hg3_wf := hwf.1 g3 hg3
    have hg2_lt_g3 : gv < g3 := by
      rcases hg3_read with hl | hr <;> omega
    have hg3_sp := hsp g3 hg3 (C.gates[g3]'hg3) (List.getElem?_eq_getElem hg3)
    have hg3_skip : g3 ∈ stf.skipped := by
      rcases hg3_read with hl | hr
      · exact hg3_sp.2.1 (Or.inr ⟨hg3_wf.1, bg2, hl.symm ▸ hbg2⟩)
      · exact hg3_sp.2.2.1 (Or.inr ⟨hg3_wf.2.1, bg2, hr.symm ▸ hbg2⟩)
    exact card_ge_three_of_ne hgu_skip hg2_skip hg3_skip (by omega) (by omega) (by omega)
  · exact card_ge_three_of_ne hgu_skip hg2_skip hgv_skip (by omega) hgv_ne_gu.symm (Ne.symm hgv_eq)

private lemma arith_drop (e' e d t' t c k s drop : ℕ)
    (he : e' + d = e) (ht : t' + drop = t) (hrec : e' + t' ≤ c - k + 1)
    (hk_lo : d + drop ≤ k) (hk_hi : k ≤ c) (hc : c ≤ s) : e + t ≤ s + 1 := by
  omega

private lemma arith_drop_one (e' e t c k s : ℕ)
    (he : e' + 2 = e) (ht : 1 ≤ t) (hrec : 1 + e' + (t - 1) ≤ c - k + 1)
    (hk_lo : 2 ≤ k) (hk_hi : k ≤ c) (hc : c ≤ s) : e + t ≤ s + 1 := by
  omega

private lemma lower_bound {n : ℕ} :
    ∀ m : ℕ, ∀ (t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      A.card + G.edgeFinset.card = m →
      G.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
      (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) →
      (∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) →
      HasBinarySize n (fGA G A) s →
      A.card + G.edgeFinset.card + t ≤ s + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro t s G _ A hm hacyc hA_iso hne hvc_ex hvc_min hbs
    obtain ⟨C, hCsz, hmin⟩ := exists_minCircuit hbs
    have hf0 := fGA_false G A
    have hf1 := fGA_exists_true G A hne
    have hwf := minCircuit_wellFormed hmin hf0 hf1
    by_cases hedge : ∃ u v : Fin n, G.Adj u v
    · by_cases hA : A.Nonempty
      · -- Case: A nonempty and G has an edge
        obtain ⟨a, ha⟩ := hA
        let A' := A.erase a
        have hA'card : A'.card + 1 = A.card := by
          have := Finset.card_pos.mpr ⟨a, ha⟩
          rw [Finset.card_erase_of_mem ha]; omega
        have hA'_iso : ∀ b ∈ A', ∀ v, ¬ G.Adj b v := fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)
        let ov : ℕ → Option Bool := fun w => if w = a.val then some false else none
        let dead : ℕ → Prop := fun w => w = a.val
        have hdead : ∀ w, dead w → w < n ∧
            (ov w ≠ none ∨ ∀ j (hj : j < C.gates.length),
              ((C.gates[j]'hj).left = w ∨ (C.gates[j]'hj).right = w) → ov (n + j) ≠ none) := by
          rintro w rfl
          exact ⟨a.isLt, Or.inl (by simp [ov])⟩
        have hcomp := compile_circuit C ov dead hdead
          (Or.inl (output_ne_input_of_edge G A hA_iso hedge C hmin.1 a))
          (fGA G A') (fGA_false G A') (fGA_exists_true G A' (Or.inr hedge)) (fun x => by
            let x' := Function.update x a false
            refine ⟨x', fun i hi => Function.update_of_ne (fun h => hi (congrArg Fin.val h)) _ _,
              fun w b hwb => ?_, ?_⟩
            · dsimp only [ov] at hwb
              split_ifs at hwb with hw
              injection hwb with hb; subst hw; subst hb
              rw [wval_input C x' a]; simp [x']
            · rw [hmin.1 x', Bool.eq_iff_iff]
              simp only [fGA, decide_eq_true_eq]
              constructor
              · rintro (⟨b, hb, hbx⟩ | ⟨p, q, hpq, hpx, hqx⟩)
                · by_cases hba : b = a
                  · subst hba; simp [x'] at hbx
                  · dsimp only [x'] at hbx
                    exact Or.inl ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, by rwa [Function.update_of_ne hba] at hbx⟩
                · have hpa : p ≠ a := fun h => hA_iso a ha q (h ▸ hpq)
                  have hqa : q ≠ a := fun h => hA_iso a ha p (h ▸ adj_symm hpq)
                  dsimp only [x'] at hpx hqx
                  rw [Function.update_of_ne hpa] at hpx
                  rw [Function.update_of_ne hqa] at hqx
                  exact Or.inr ⟨p, q, hpq, hpx, hqx⟩
              · rintro (⟨b, hb, hbx⟩ | ⟨p, q, hpq, hpx, hqx⟩)
                · obtain ⟨hba, hbA⟩ := Finset.mem_erase.mp hb
                  exact Or.inl ⟨b, hbA, by dsimp only [x']; rw [Function.update_of_ne hba]; exact hbx⟩
                · have hpa : p ≠ a := fun h => hA_iso a ha q (h ▸ hpq)
                  have hqa : q ≠ a := fun h => hA_iso a ha p (h ▸ adj_symm hpq)
                  exact Or.inr ⟨p, q, hpq, by dsimp only [x']; rw [Function.update_of_ne hpa]; exact hpx,
                    by dsimp only [x']; rw [Function.update_of_ne hqa]; exact hqx⟩)
        have hread_a := (essential_read hmin.1 a (fGA_essential_mem G A a ha)).resolve_left
          (output_ne_input_of_edge G A hA_iso hedge C hmin.1 a)
        obtain ⟨ka, hka, hka_read⟩ := hread_a
        have hsp := compile_step_props n ov C
        have ha_const : (compile n ov C.gates).env a.val = WRef.const false :=
          hsp.1 a.val a.isLt false (by simp [ov])
        have hka_sp := hsp.2 ka hka (C.gates[ka]'hka) (List.getElem?_eq_getElem hka)
        have hka_wf := hwf.1 ka hka
        have hka_skip : ka ∈ (compile n ov C.gates).skipped := by
          rcases hka_read with hl | hr
          · exact hka_sp.2.1 (Or.inr ⟨hka_wf.1, false, hl.symm ▸ ha_const⟩)
          · exact hka_sp.2.2.1 (Or.inr ⟨hka_wf.2.1, false, hr.symm ▸ ha_const⟩)
        have hsk_pos : 1 ≤ (compile n ov C.gates).skipped.card := Finset.card_pos.mpr ⟨ka, hka_skip⟩
        have hsk_le : (compile n ov C.gates).skipped.card ≤ C.size := by
          have := (compile_spec n ov C).1; dsimp only [BinaryCircuit.size]; omega
        have hrec := ih (A'.card + G.edgeFinset.card) (by exact Nat.lt_of_lt_of_le (by exact Nat.lt_of_succ_le (by rw [← hA'card]; omega)) hm.le) t
          (C.size - (compile n ov C.gates).skipped.card) G A' rfl hacyc hA'_iso (Or.inr hedge)
          hvc_ex hvc_min hcomp.1
        exact arith_drop (A'.card + G.edgeFinset.card) (A.card + G.edgeFinset.card) 1 t t
          C.size (compile n ov C.gates).skipped.card s 0
          (by rw [← hA'card]; ring) rfl hrec hsk_pos hsk_le hCsz
      · -- Case: A = ∅ and G has an edge
        rw [Finset.not_nonempty_iff_eq_empty] at hA
        subst hA
        rcases forest_structure G hacyc hedge with
          ⟨u, v, huv, hu_leaf, hv_leaf⟩ |
          ⟨u1, u2, v, hu12, h1, h2, hl1, hl2⟩ |
          ⟨u, v, w, huw, huv, hvw, hu_leaf, hv_deg2⟩
        · -- Case 3a: Isolated edge u - v
          let G' := delVert G v
          let : DecidableRel G'.Adj := fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ a ≠ v ∧ b ≠ v))
          have hacyc' : G'.IsAcyclic := delVert_isAcyclic G v hacyc
          have hedge_card : G'.edgeFinset.card + 1 = G.edgeFinset.card :=
            edgeFinset_delVert_deg1 G v u (adj_symm huv) hv_leaf
          obtain ⟨ht1, hvc'_ex, hvc'_min⟩ := vc_del_leaf_parent G u v huv hu_leaf hvc_ex hvc_min
          by_cases hedge' : ∃ p q : Fin n, G'.Adj p q
          · let ov : ℕ → Option Bool := fun w =>
              if w = u.val ∨ w = v.val then some false else none
            let dead : ℕ → Prop := fun w => w = u.val ∨ w = v.val
            have hdead : ∀ w, dead w → w < n ∧
                (ov w ≠ none ∨ ∀ j (hj : j < C.gates.length),
                  ((C.gates[j]'hj).left = w ∨ (C.gates[j]'hj).right = w) → ov (n + j) ≠ none) := by
              rintro w (rfl | rfl)
              · exact ⟨u.isLt, Or.inl (by simp [ov])⟩
              · exact ⟨v.isLt, Or.inl (by simp [ov])⟩
            have hout_nd : ¬ dead C.output ∨ ov C.output ≠ none := Or.inl (by
              rintro (h | h)
              · exact output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 u h
              · exact output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 v h)
            have hcomp := compile_circuit C ov dead hdead hout_nd
              (fGA G' ∅) (fGA_false G' ∅) (fGA_exists_true G' ∅ (Or.inr hedge')) (fun x => by
                let x' := Function.update (Function.update x v false) u false
                have hne_uv : u ≠ v := G.ne_of_adj huv
                refine ⟨x', fun i hi => by
                  have hiu : i ≠ u := fun h => hi (Or.inl (congrArg Fin.val h))
                  have hiv : i ≠ v := fun h => hi (Or.inr (congrArg Fin.val h))
                  simp [x', Function.update_of_ne hiu, Function.update_of_ne hiv],
                  fun w b hwb => ?_, ?_⟩
                · dsimp only [ov] at hwb
                  split_ifs at hwb with hw
                  injection hwb with hb; subst hb
                  rcases hw with rfl | rfl
                  · rw [wval_input C x' u]; simp [x']
                  · rw [wval_input C x' v]; simp [x', Function.update_of_ne hne_uv.symm]
                · rw [hmin.1 x', Bool.eq_iff_iff]
                  simp only [fGA, Finset.notMem_empty, false_and, exists_false, false_or,
                    decide_eq_true_eq]
                  constructor
                  · rintro ⟨p, q, hpq, hpx, hqx⟩
                    have hpu : p ≠ u := fun h => by subst h; simp [x'] at hpx
                    have hqu : q ≠ u := fun h => by subst h; simp [x'] at hqx
                    have hpv : p ≠ v := fun h => by
                      subst h; simp [x', Function.update_of_ne hne_uv.symm] at hpx
                    have hqv : q ≠ v := fun h => by
                      subst h; simp [x', Function.update_of_ne hne_uv.symm] at hqx
                    dsimp only [x'] at hpx hqx
                    rw [Function.update_of_ne hpu, Function.update_of_ne hpv] at hpx
                    rw [Function.update_of_ne hqu, Function.update_of_ne hqv] at hqx
                    exact ⟨p, q, ⟨hpq, hpv, hqv⟩, hpx, hqx⟩
                  · rintro ⟨p, q, ⟨hpq, hpv, hqv⟩, hpx, hqx⟩
                    have hpu : p ≠ u := fun h => hqv (hu_leaf q (h ▸ hpq))
                    have hqu : q ≠ u := fun h => hpv (hu_leaf p (h ▸ adj_symm hpq))
                    exact ⟨p, q, hpq, by simp [x', Function.update_of_ne hpu, Function.update_of_ne hpv, hpx],
                      by simp [x', Function.update_of_ne hqu, Function.update_of_ne hqv, hqx]⟩)
            have hsp := compile_step_props n ov C
            have hu_const : (compile n ov C.gates).env u.val = WRef.const false :=
              hsp.1 u.val u.isLt false (by simp [ov])
            have hv_const : (compile n ov C.gates).env v.val = WRef.const false :=
              hsp.1 v.val v.isLt false (by simp [ov])
            obtain ⟨gu, hgu, hgu_read⟩ := (essential_read hmin.1 u
              (fGA_essential_edge G ∅ (fun _ hm => by cases hm) u v huv)).resolve_left
              (output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 u)
            obtain ⟨gv, hgv, hgv_read⟩ := (essential_read hmin.1 v
              (fGA_essential_edge G ∅ (fun _ hm => by cases hm) v u (adj_symm huv))).resolve_left
              (output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 v)
            have hgu_wf := hwf.1 gu hgu
            have hgu_sp := hsp.2 gu hgu (C.gates[gu]'hgu) (List.getElem?_eq_getElem hgu)
            have hgu_skip : gu ∈ (compile n ov C.gates).skipped := by
              rcases hgu_read with hl | hr
              · exact hgu_sp.2.1 (Or.inr ⟨hgu_wf.1, false, hl.symm ▸ hu_const⟩)
              · exact hgu_sp.2.2.1 (Or.inr ⟨hgu_wf.2.1, false, hr.symm ▸ hu_const⟩)
            have hgv_wf := hwf.1 gv hgv
            have hgv_sp := hsp.2 gv hgv (C.gates[gv]'hgv) (List.getElem?_eq_getElem hgv)
            have hgv_skip : gv ∈ (compile n ov C.gates).skipped := by
              rcases hgv_read with hl | hr
              · exact hgv_sp.2.1 (Or.inr ⟨hgv_wf.1, false, hl.symm ▸ hv_const⟩)
              · exact hgv_sp.2.2.1 (Or.inr ⟨hgv_wf.2.1, false, hr.symm ▸ hv_const⟩)
            have hsk2 : 2 ≤ (compile n ov C.gates).skipped.card := by
              by_cases hgueq : gu = gv
              · subst hgueq
                have hne_uv : u.val ≠ v.val := fun h => G.ne_of_adj huv (Fin.ext h)
                have hLc : ∃ b, (compile n ov C.gates).env (C.gates[gu]'hgu).left = WRef.const b := by
                  rcases hgu_read with hl | hr
                  · exact ⟨false, hl.symm ▸ hu_const⟩
                  · rcases hgv_read with hvl | hvr
                    · exact ⟨false, hvl.symm ▸ hv_const⟩
                    · exact absurd (hr.symm.trans hvr) hne_uv
                have hRc : ∃ b, (compile n ov C.gates).env (C.gates[gu]'hgu).right = WRef.const b := by
                  rcases hgu_read with hl | hr
                  · rcases hgv_read with hvl | hvr
                    · exact absurd (hl.symm.trans hvl) hne_uv
                    · exact ⟨false, hvr.symm ▸ hv_const⟩
                  · exact ⟨false, hr.symm ▸ hu_const⟩
                obtain ⟨bgu, hbgu⟩ := hgu_sp.2.2.2.2.1 ⟨Or.inr ⟨hgu_wf.1, hLc⟩, Or.inr ⟨hgu_wf.2.1, hRc⟩⟩
                have hout_ne : C.output ≠ n + gu := fun h => hcomp.2 bgu (h ▸ hbgu)
                obtain ⟨g2, hg2, hg2_read⟩ := (hwf.2 gu hgu).resolve_left hout_ne
                have hg2_wf := hwf.1 g2 hg2
                have hgu_lt_g2 : gu < g2 := by rcases hg2_read with hl | hr <;> omega
                have hg2_sp := hsp.2 g2 hg2 (C.gates[g2]'hg2) (List.getElem?_eq_getElem hg2)
                have hg2_skip : g2 ∈ (compile n ov C.gates).skipped := by
                  rcases hg2_read with hl | hr
                  · exact hg2_sp.2.1 (Or.inr ⟨hg2_wf.1, bgu, hl.symm ▸ hbgu⟩)
                  · exact hg2_sp.2.2.1 (Or.inr ⟨hg2_wf.2.1, bgu, hr.symm ▸ hbgu⟩)
                exact card_ge_two_of_ne hgu_skip hg2_skip (by omega)
              · exact card_ge_two_of_ne hgu_skip hgv_skip hgueq
            have hsk_le : (compile n ov C.gates).skipped.card ≤ C.size := by
              have h1 := (compile_spec n ov C).1
              exact Nat.le_of_add_left_le h1.le
            have hlt_m : (∅ : Finset (Fin n)).card + G'.edgeFinset.card < m := by
              rw [← hm, Finset.card_empty, zero_add, zero_add, ← hedge_card]
              exact Nat.lt_succ_self _
            have hrec := ih ((∅ : Finset (Fin n)).card + G'.edgeFinset.card) hlt_m
              (t - 1) (C.size - (compile n ov C.gates).skipped.card) G' ∅ rfl hacyc'
              (fun _ hm => by cases hm) (Or.inr hedge') hvc'_ex hvc'_min hcomp.1
            simp only [Finset.card_empty, zero_add] at hrec ⊢
            exact arith_drop G'.edgeFinset.card G.edgeFinset.card 1 (t - 1) t
              C.size (compile n ov C.gates).skipped.card s 1
              hedge_card (Nat.sub_add_cancel ht1) hrec hsk2 hsk_le hCsz
          · -- G' has no edges: G has 1 edge and t = 1
            have hE'0 : G'.edgeFinset.card = 0 := by
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
              intro e he
              induction e using Sym2.ind with
              | _ p q => exact hedge' ⟨p, q, G'.mem_edgeFinset.mp he⟩
            have ht_le1 : t - 1 ≤ 0 := hvc'_min ∅ (fun p q hpq => absurd ⟨p, q, hpq⟩ hedge')
            have hess := ess_card_le_size_add_one hmin hf0 hf1 ({u, v} : Finset (Fin n)) (fun i hi => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hi
              rcases hi with hi | hi <;> rw [hi]
              · exact fGA_essential_edge G ∅ (fun _ hm => by cases hm) u v huv
              · exact fGA_essential_edge G ∅ (fun _ hm => by cases hm) v u (adj_symm huv))
            rw [Finset.card_pair (G.ne_of_adj huv)] at hess
            simp only [Finset.card_empty, zero_add]
            have hE1 : G.edgeFinset.card = 1 := by rw [← hedge_card, hE'0]
            rw [hE1]
            exact Nat.le_trans (by omega : 1 + t ≤ 2) (Nat.le_trans hess (Nat.add_le_add_right hCsz 1))
        · -- Case 3b: Two leaves u1, u2 adjacent to v
          let G' := delVert G u1
          let : DecidableRel G'.Adj := fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ a ≠ u1 ∧ b ≠ u1))
          have hacyc' : G'.IsAcyclic := delVert_isAcyclic G u1 hacyc
          have hedge_card : G'.edgeFinset.card + 1 = G.edgeFinset.card :=
            edgeFinset_delVert_deg1 G u1 v h1 hl1
          obtain ⟨hvc'_ex, hvc'_min⟩ := vc_del_twin_leaf G u1 u2 v hu12 h1 h2 hl1 hl2 hvc_ex hvc_min
          have hedge' : ∃ p q : Fin n, G'.Adj p q := ⟨u2, v, h2, hu12.symm, (G.ne_of_adj h1).symm⟩
          let ov : ℕ → Option Bool := fun w => if w = u1.val then some false else none
          let dead : ℕ → Prop := fun w => w = u1.val
          have hdead : ∀ w, dead w → w < n ∧
              (ov w ≠ none ∨ ∀ j (hj : j < C.gates.length),
                ((C.gates[j]'hj).left = w ∨ (C.gates[j]'hj).right = w) → ov (n + j) ≠ none) := by
            rintro w rfl; exact ⟨u1.isLt, Or.inl (by simp [ov])⟩
          have hcomp := compile_circuit C ov dead hdead
            (Or.inl (output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 u1))
            (fGA G' ∅) (fGA_false G' ∅) (fGA_exists_true G' ∅ (Or.inr hedge')) (fun x => by
              let x' := Function.update x u1 false
              refine ⟨x', fun i hi => Function.update_of_ne (fun h => hi (congrArg Fin.val h)) _ _,
                fun w b hwb => ?_, ?_⟩
              · dsimp only [ov] at hwb
                split_ifs at hwb with hw
                injection hwb with hb; subst hw; subst hb
                rw [wval_input C x' u1]; simp [x']
              · rw [hmin.1 x', Bool.eq_iff_iff]
                simp only [fGA, Finset.notMem_empty, false_and, exists_false, false_or,
                  decide_eq_true_eq]
                constructor
                · rintro ⟨p, q, hpq, hpx, hqx⟩
                  have hp1 : p ≠ u1 := fun h => by subst h; simp [x'] at hpx
                  have hq1 : q ≠ u1 := fun h => by subst h; simp [x'] at hqx
                  dsimp only [x'] at hpx hqx
                  rw [Function.update_of_ne hp1] at hpx
                  rw [Function.update_of_ne hq1] at hqx
                  exact ⟨p, q, ⟨hpq, hp1, hq1⟩, hpx, hqx⟩
                · rintro ⟨p, q, ⟨hpq, hp1, hq1⟩, hpx, hqx⟩
                  exact ⟨p, q, hpq, by dsimp only [x']; rw [Function.update_of_ne hp1]; exact hpx,
                    by dsimp only [x']; rw [Function.update_of_ne hq1]; exact hqx⟩)
          have hsp := compile_step_props n ov C
          have hu1_const : (compile n ov C.gates).env u1.val = WRef.const false :=
            hsp.1 u1.val u1.isLt false (by simp [ov])
          obtain ⟨k1, hk1, hk1_read⟩ := (essential_read hmin.1 u1
            (fGA_essential_edge G ∅ (fun _ hm => by cases hm) u1 v h1)).resolve_left
            (output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 u1)
          have hk1_wf := hwf.1 k1 hk1
          have hk1_sp := hsp.2 k1 hk1 (C.gates[k1]'hk1) (List.getElem?_eq_getElem hk1)
          have hk1_skip : k1 ∈ (compile n ov C.gates).skipped := by
            rcases hk1_read with hl | hr
            · exact hk1_sp.2.1 (Or.inr ⟨hk1_wf.1, false, hl.symm ▸ hu1_const⟩)
            · exact hk1_sp.2.2.1 (Or.inr ⟨hk1_wf.2.1, false, hr.symm ▸ hu1_const⟩)
          have hsk1 : 1 ≤ (compile n ov C.gates).skipped.card := Finset.card_pos.mpr ⟨k1, hk1_skip⟩
          have hsk_le : (compile n ov C.gates).skipped.card ≤ C.size := by
            have h1 := (compile_spec n ov C).1
            exact Nat.le_of_add_left_le h1.le
          have hlt_m : (∅ : Finset (Fin n)).card + G'.edgeFinset.card < m := by
            rw [← hm, Finset.card_empty, zero_add, zero_add, ← hedge_card]
            exact Nat.lt_succ_self _
          have hrec := ih ((∅ : Finset (Fin n)).card + G'.edgeFinset.card) hlt_m
            t (C.size - (compile n ov C.gates).skipped.card) G' ∅ rfl hacyc'
            (fun _ hm => by cases hm) (Or.inr hedge') hvc'_ex hvc'_min hcomp.1
          simp only [Finset.card_empty, zero_add] at hrec ⊢
          exact arith_drop G'.edgeFinset.card G.edgeFinset.card 1 t t
            C.size (compile n ov C.gates).skipped.card s 0
            hedge_card rfl hrec hsk1 hsk_le hCsz
        · -- Case 3c: Leaf u attached to degree-2 vertex v (N(u) = {v}, N(v) = {u, w})
          let G' := delVert G v
          let : DecidableRel G'.Adj := fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ a ≠ v ∧ b ≠ v))
          have hacyc' : G'.IsAcyclic := delVert_isAcyclic G v hacyc
          have hedge_card : G'.edgeFinset.card + 2 = G.edgeFinset.card :=
            edgeFinset_delVert_deg2 G v u w huw (adj_symm huv) hvw hv_deg2
          obtain ⟨ht1, hvc'_ex, hvc'_min⟩ := vc_del_leaf_parent G u v huv hu_leaf hvc_ex hvc_min
          by_cases hedge' : ∃ p q : Fin n, G'.Adj p q
          · -- G' has at least one edge
            have hne_uv : u ≠ v := G.ne_of_adj huv
            -- Helper for the u -> true restriction (computes fGA G' {v})
            have hsim_utrue : ∀ x : Fin n → Bool,
                fGA G ∅ (Function.update x u true) = fGA G' {v} x := by
              intro x
              rw [Bool.eq_iff_iff]
              simp only [fGA, Finset.notMem_empty, false_and, exists_false, false_or,
                Finset.mem_singleton, exists_eq_left, decide_eq_true_eq]
              constructor
              · rintro ⟨p, q, hpq, hpx, hqx⟩
                by_cases hpv : p = v
                · subst hpv; rw [Function.update_of_ne hne_uv.symm] at hpx; exact Or.inl hpx
                · by_cases hqv : q = v
                  · subst hqv; rw [Function.update_of_ne hne_uv.symm] at hqx; exact Or.inl hqx
                  · have hpu : p ≠ u := fun h => hqv (hu_leaf q (h ▸ hpq))
                    have hqu : q ≠ u := fun h => hpv (hu_leaf p (h ▸ adj_symm hpq))
                    rw [Function.update_of_ne hpu] at hpx
                    rw [Function.update_of_ne hqu] at hqx
                    exact Or.inr ⟨p, q, ⟨hpq, hpv, hqv⟩, hpx, hqx⟩
              · rintro (hxv | ⟨p, q, ⟨hpq, hpv, hqv⟩, hpx, hqx⟩)
                · exact ⟨u, v, huv, by simp, by rw [Function.update_of_ne hne_uv.symm]; exact hxv⟩
                · have hpu : p ≠ u := fun h => hqv (hu_leaf q (h ▸ hpq))
                  have hqu : q ≠ u := fun h => hpv (hu_leaf p (h ▸ adj_symm hpq))
                  exact ⟨p, q, hpq, by rw [Function.update_of_ne hpu]; exact hpx,
                    by rw [Function.update_of_ne hqu]; exact hqx⟩
            -- Helper for any u,v -> x' with x' v = false (computes fGA G' ∅)
            have hsim_vfalse : ∀ x x' : Fin n → Bool,
                (∀ i : Fin n, i ≠ u → i ≠ v → x' i = x i) → x' v = false →
                fGA G ∅ x' = fGA G' ∅ x := by
              intro x x' hag hxv'
              rw [Bool.eq_iff_iff]
              simp only [fGA, Finset.notMem_empty, false_and, exists_false, false_or,
                decide_eq_true_eq]
              constructor
              · rintro ⟨p, q, hpq, hpx, hqx⟩
                have hpv : p ≠ v := fun h => by rw [h, hxv'] at hpx; cases hpx
                have hqv : q ≠ v := fun h => by rw [h, hxv'] at hqx; cases hqx
                have hpu : p ≠ u := fun h => hqv (hu_leaf q (h ▸ hpq))
                have hqu : q ≠ u := fun h => hpv (hu_leaf p (h ▸ adj_symm hpq))
                rw [hag p hpu hpv] at hpx; rw [hag q hqu hqv] at hqx
                exact ⟨p, q, ⟨hpq, hpv, hqv⟩, hpx, hqx⟩
              · rintro ⟨p, q, ⟨hpq, hpv, hqv⟩, hpx, hqx⟩
                have hpu : p ≠ u := fun h => hqv (hu_leaf q (h ▸ hpq))
                have hqu : q ≠ u := fun h => hpv (hu_leaf p (h ▸ adj_symm hpq))
                exact ⟨p, q, hpq, by rw [hag p hpu hpv]; exact hpx, by rw [hag q hqu hqv]; exact hqx⟩
            -- Bundle the u -> true compilation
            let ovT : ℕ → Option Bool := fun w => if w = u.val then some true else none
            let deadT : ℕ → Prop := fun w => w = u.val
            have hdeadT : ∀ w, deadT w → w < n ∧
                (ovT w ≠ none ∨ ∀ j (hj : j < C.gates.length),
                  ((C.gates[j]'hj).left = w ∨ (C.gates[j]'hj).right = w) → ovT (n + j) ≠ none) := by
              rintro w rfl; exact ⟨u.isLt, Or.inl (by simp [ovT])⟩
            have hcompT := compile_circuit C ovT deadT hdeadT
              (Or.inl (output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 u))
              (fGA G' {v}) (fGA_false G' {v}) (fGA_exists_true G' {v} (Or.inl (Finset.singleton_nonempty v)))
              (fun x => ⟨Function.update x u true,
                fun i hi => Function.update_of_ne (fun h => hi (congrArg Fin.val h)) _ _,
                fun w b hwb => by
                  dsimp only [ovT] at hwb; split_ifs at hwb with hw
                  injection hwb with hb; subst hw; subst hb; rw [wval_input]; simp,
                by rw [hmin.1, hsim_utrue x]⟩)
            have hfinish_T : 2 ≤ (compile n ovT C.gates).skipped.card →
                (∅ : Finset (Fin n)).card + G.edgeFinset.card + t ≤ s + 1 := by
              intro hsk2
              have hsk_le : (compile n ovT C.gates).skipped.card ≤ C.size := by
                have h1 := (compile_spec n ovT C).1
                exact Nat.le_of_add_left_le h1.le
              have hlt_m : ({v} : Finset (Fin n)).card + G'.edgeFinset.card < m := by
                rw [← hm, Finset.card_singleton, Finset.card_empty, zero_add, ← hedge_card, Nat.add_comm 1]
                exact Nat.add_lt_add_left (by decide : 1 < 2) _
              have hrec := ih (({v} : Finset (Fin n)).card + G'.edgeFinset.card)
                hlt_m (t - 1) (C.size - (compile n ovT C.gates).skipped.card)
                G' {v} rfl hacyc'
                (fun a ha z => by rw [Finset.mem_singleton.mp ha]; intro h; exact h.2.1 rfl)
                (Or.inl (Finset.singleton_nonempty v)) hvc'_ex hvc'_min hcompT.1
              simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hrec ⊢
              exact arith_drop_one G'.edgeFinset.card G.edgeFinset.card t
                C.size (compile n ovT C.gates).skipped.card s
                hedge_card ht1 hrec hsk2 hsk_le hCsz
            -- Find a gate reading u
            obtain ⟨gu, hgu, hgu_read⟩ := (essential_read hmin.1 u
              (fGA_essential_edge G ∅ (fun _ hm => by cases hm) u v huv)).resolve_left
              (output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 u)
            by_cases htwo_u : ∃ gu2, ∃ hgu2 : gu2 < C.gates.length, gu2 ≠ gu ∧
                ((C.gates[gu2]'hgu2).left = u.val ∨ (C.gates[gu2]'hgu2).right = u.val)
            · -- At least 2 gates read u: ovT kills both!
              obtain ⟨gu2, hgu2, hne2, hgu2_read⟩ := htwo_u
              have hspT := compile_step_props n ovT C
              have huT : (compile n ovT C.gates).env u.val = WRef.const true :=
                hspT.1 u.val u.isLt true (by simp [ovT])
              have hgu_wf := hwf.1 gu hgu
              have hgu_sp := hspT.2 gu hgu (C.gates[gu]'hgu) (List.getElem?_eq_getElem hgu)
              have hgu_sk : gu ∈ (compile n ovT C.gates).skipped := by
                rcases hgu_read with hl | hr
                · exact hgu_sp.2.1 (Or.inr ⟨hgu_wf.1, true, hl.symm ▸ huT⟩)
                · exact hgu_sp.2.2.1 (Or.inr ⟨hgu_wf.2.1, true, hr.symm ▸ huT⟩)
              have hgu2_wf := hwf.1 gu2 hgu2
              have hgu2_sp := hspT.2 gu2 hgu2 (C.gates[gu2]'hgu2) (List.getElem?_eq_getElem hgu2)
              have hgu2_sk : gu2 ∈ (compile n ovT C.gates).skipped := by
                rcases hgu2_read with hl | hr
                · exact hgu2_sp.2.1 (Or.inr ⟨hgu2_wf.1, true, hl.symm ▸ huT⟩)
                · exact hgu2_sp.2.2.1 (Or.inr ⟨hgu2_wf.2.1, true, hr.symm ▸ huT⟩)
              exact hfinish_T (card_ge_two_of_ne hgu_sk hgu2_sk hne2.symm)
            · -- gu is the unique gate reading u
              push Not at htwo_u
              have hgv_ex := exists_other_reader_v G u v w huw huv hvw C hmin gu hgu hgu_read htwo_u
              have hdep := minCircuit_gate_depends hmin hf0 hf1 gu hgu
              have hgu_wf := hwf.1 gu hgu
              -- Helper for Subcase 2a: gu becomes constant under ovT
              have hfinish_T_const : (∃ b, (compile n ovT C.gates).env (n + gu) = WRef.const b) →
                  (∅ : Finset (Fin n)).card + G.edgeFinset.card + t ≤ s + 1 := by
                rintro ⟨bgu, hbgu⟩
                have hspT := compile_step_props n ovT C
                have huT : (compile n ovT C.gates).env u.val = WRef.const true :=
                  hspT.1 u.val u.isLt true (by simp [ovT])
                have hgu_sp := hspT.2 gu hgu (C.gates[gu]'hgu) (List.getElem?_eq_getElem hgu)
                have hgu_sk : gu ∈ (compile n ovT C.gates).skipped := by
                  rcases hgu_read with hl | hr
                  · exact hgu_sp.2.1 (Or.inr ⟨hgu_wf.1, true, hl.symm ▸ huT⟩)
                  · exact hgu_sp.2.2.1 (Or.inr ⟨hgu_wf.2.1, true, hr.symm ▸ huT⟩)
                have hout_ne : C.output ≠ n + gu := fun h => hcompT.2 bgu (h ▸ hbgu)
                obtain ⟨g2, hg2, hg2_read⟩ := (hwf.2 gu hgu).resolve_left hout_ne
                have hg2_wf := hwf.1 g2 hg2
                have hgu_lt_g2 : gu < g2 := by rcases hg2_read with hl | hr <;> omega
                have hg2_sp := hspT.2 g2 hg2 (C.gates[g2]'hg2) (List.getElem?_eq_getElem hg2)
                have hg2_sk : g2 ∈ (compile n ovT C.gates).skipped := by
                  rcases hg2_read with hl | hr
                  · exact hg2_sp.2.1 (Or.inr ⟨hg2_wf.1, bgu, hl.symm ▸ hbgu⟩)
                  · exact hg2_sp.2.2.1 (Or.inr ⟨hg2_wf.2.1, bgu, hr.symm ▸ hbgu⟩)
                exact hfinish_T (card_ge_two_of_ne hgu_sk hg2_sk (by omega))
              -- Helper for Subcase 2b: u -> false, v -> false kills 3 gates when u -> false forces gu constant
              have hfinish_F_const :
                  (let ovF : ℕ → Option Bool := fun w => if w = u.val ∨ w = v.val then some false else none
                   ∃ b, (compile n ovF C.gates).env (n + gu) = WRef.const b) →
                  (∅ : Finset (Fin n)).card + G.edgeFinset.card + t ≤ s + 1 := by
                intro hgu_const
                let ovF : ℕ → Option Bool := fun w => if w = u.val ∨ w = v.val then some false else none
                let deadF : ℕ → Prop := fun w => w = u.val ∨ w = v.val
                have hdeadF : ∀ w, deadF w → w < n ∧
                    (ovF w ≠ none ∨ ∀ j (hj : j < C.gates.length),
                      ((C.gates[j]'hj).left = w ∨ (C.gates[j]'hj).right = w) → ovF (n + j) ≠ none) := by
                  rintro w (rfl | rfl)
                  · exact ⟨u.isLt, Or.inl (by simp [ovF])⟩
                  · exact ⟨v.isLt, Or.inl (by simp [ovF])⟩
                have hout_ndF : ¬ deadF C.output ∨ ovF C.output ≠ none := Or.inl (by
                  rintro (h | h)
                  · exact output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 u h
                  · exact output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 v h)
                have hcompF := compile_circuit C ovF deadF hdeadF hout_ndF
                  (fGA G' ∅) (fGA_false G' ∅) (fGA_exists_true G' ∅ (Or.inr hedge')) (fun x => by
                    let x' := Function.update (Function.update x v false) u false
                    refine ⟨x', fun i hi => by
                      have hiu : i ≠ u := fun h => hi (Or.inl (congrArg Fin.val h))
                      have hiv : i ≠ v := fun h => hi (Or.inr (congrArg Fin.val h))
                      simp [x', Function.update_of_ne hiu, Function.update_of_ne hiv],
                      fun w b hwb => ?_, ?_⟩
                    · dsimp only [ovF] at hwb; split_ifs at hwb with hw
                      injection hwb with hb; subst hb
                      rcases hw with rfl | rfl
                      · rw [wval_input]; simp [x']
                      · rw [wval_input]; simp [x', Function.update_of_ne hne_uv.symm]
                    · rw [hmin.1 x']
                      exact hsim_vfalse x x'
                        (fun i hiu hiv => by simp [x', Function.update_of_ne hiu, Function.update_of_ne hiv])
                        (by simp [x', Function.update_of_ne hne_uv.symm]))
                have hspF := compile_step_props n ovF C
                have huF : (compile n ovF C.gates).env u.val = WRef.const false :=
                  hspF.1 u.val u.isLt false (by simp [ovF])
                have hvF : (compile n ovF C.gates).env v.val = WRef.const false :=
                  hspF.1 v.val v.isLt false (by simp [ovF])
                have hgu_sp := hspF.2 gu hgu (C.gates[gu]'hgu) (List.getElem?_eq_getElem hgu)
                have hgu_sk : gu ∈ (compile n ovF C.gates).skipped := by
                  rcases hgu_read with hl | hr
                  · exact hgu_sp.2.1 (Or.inr ⟨hgu_wf.1, false, hl.symm ▸ huF⟩)
                  · exact hgu_sp.2.2.1 (Or.inr ⟨hgu_wf.2.1, false, hr.symm ▸ huF⟩)
                have hsk3 := three_skipped_of_const_gu_v hmin hf0 hf1 ovF v gu hgu
                  hcompF.2 hvF hgu_sk hgu_const hgv_ex
                have hsk_le : (compile n ovF C.gates).skipped.card ≤ C.size := by
                  have h1 := (compile_spec n ovF C).1
                  exact Nat.le_of_add_left_le h1.le
                have hlt_m : (∅ : Finset (Fin n)).card + G'.edgeFinset.card < m := by
                  rw [← hm, Finset.card_empty, zero_add, zero_add, ← hedge_card]
                  exact Nat.lt_add_of_pos_right (by decide)
                have hrec := ih ((∅ : Finset (Fin n)).card + G'.edgeFinset.card)
                  hlt_m (t - 1) (C.size - (compile n ovF C.gates).skipped.card)
                  G' ∅ rfl hacyc' (fun _ hm => by cases hm) (Or.inr hedge') hvc'_ex hvc'_min hcompF.1
                simp only [Finset.card_empty, zero_add] at hrec ⊢
                exact arith_drop G'.edgeFinset.card G.edgeFinset.card 2 (t - 1) t
                  C.size (compile n ovF C.gates).skipped.card s 1
                  hedge_card (Nat.sub_add_cancel ht1) hrec hsk3 hsk_le hCsz
              -- Helper for Subcase 2c: XOR/XNOR gate gu -> override v=false, gu=false kills 3 gates
              have hfinish_XOR :
                  (∀ x0 x1 : Fin n → Bool,
                    (∀ j : Fin n, j ≠ u → x0 j = x1 j) → x0 u = false → x1 u = true →
                    wval C x0 (n + gu) ≠ wval C x1 (n + gu)) →
                  (∅ : Finset (Fin n)).card + G.edgeFinset.card + t ≤ s + 1 := by
                intro hflip
                let ovX : ℕ → Option Bool := fun w =>
                  if w = v.val then some false else if w = n + gu then some false else none
                let deadX : ℕ → Prop := fun w => w = u.val ∨ w = v.val
                have hv_ne_gu : v.val ≠ n + gu := by have := v.isLt; omega
                have hdeadX : ∀ w, deadX w → w < n ∧
                    (ovX w ≠ none ∨ ∀ j (hj : j < C.gates.length),
                      ((C.gates[j]'hj).left = w ∨ (C.gates[j]'hj).right = w) → ovX (n + j) ≠ none) := by
                  rintro w (rfl | rfl)
                  · refine ⟨u.isLt, Or.inr fun j hj hlr => ?_⟩
                    have hjg : j = gu := by
                      by_contra hne'
                      have := htwo_u j hj hne'
                      rcases hlr with hl | hr
                      · exact this.1 hl
                      · exact this.2 hr
                    subst hjg
                    simp [ovX, hv_ne_gu.symm]
                  · exact ⟨v.isLt, Or.inl (by simp [ovX])⟩
                have hout_ndX : ¬ deadX C.output ∨ ovX C.output ≠ none := Or.inl (by
                  rintro (h | h)
                  · exact output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 u h
                  · exact output_ne_input_of_edge G ∅ (fun _ hm => by cases hm) hedge C hmin.1 v h)
                have hcompX := compile_circuit C ovX deadX hdeadX hout_ndX
                  (fGA G' ∅) (fGA_false G' ∅) (fGA_exists_true G' ∅ (Or.inr hedge')) (fun x => by
                    let x0 := Function.update (Function.update x v false) u false
                    let x1 := Function.update (Function.update x v false) u true
                    have hag01 : ∀ j : Fin n, j ≠ u → x0 j = x1 j := fun j hj => by
                      simp [x0, x1, Function.update_of_ne hj]
                    have hne_val := hflip x0 x1 hag01 (by simp [x0]) (by simp [x1])
                    have hex_x' : ∃ x' : Fin n → Bool,
                        (∀ i : Fin n, i ≠ u → i ≠ v → x' i = x i) ∧
                        x' v = false ∧ wval C x' (n + gu) = false := by
                      cases h0 : wval C x0 (n + gu) with
                      | false =>
                        exact ⟨x0, fun i hiu hiv => by simp [x0, Function.update_of_ne hiu, Function.update_of_ne hiv],
                          by simp [x0, Function.update_of_ne hne_uv.symm], h0⟩
                      | true =>
                        have h1 : wval C x1 (n + gu) = false := by
                          cases hv1 : wval C x1 (n + gu)
                          · rfl
                          · rw [h0, hv1] at hne_val; exact absurd rfl hne_val
                        exact ⟨x1, fun i hiu hiv => by simp [x1, Function.update_of_ne hiu, Function.update_of_ne hiv],
                          by simp [x1, Function.update_of_ne hne_uv.symm], h1⟩
                    obtain ⟨x', hag, hxv', hgu0⟩ := hex_x'
                    refine ⟨x', fun i hi => hag i (fun h => hi (Or.inl (congrArg Fin.val h)))
                        (fun h => hi (Or.inr (congrArg Fin.val h))),
                      fun w b hwb => ?_, ?_⟩
                    · dsimp only [ovX] at hwb
                      split_ifs at hwb with hw1 hw2
                      · injection hwb with hb; subst hw1; subst hb; rw [wval_input, hxv']
                      · injection hwb with hb; subst hw2; subst hb; exact hgu0
                    · rw [hmin.1 x']; exact hsim_vfalse x x' hag hxv')
                have hspX := compile_step_props n ovX C
                have hvX : (compile n ovX C.gates).env v.val = WRef.const false :=
                  hspX.1 v.val v.isLt false (by simp [ovX])
                have hgu_ov : ovX (n + gu) ≠ none := by simp [ovX, hv_ne_gu.symm]
                have hgu_props := (hspX.2 gu hgu (C.gates[gu]'hgu) (List.getElem?_eq_getElem hgu)).1 hgu_ov
                have hsk3 := three_skipped_of_const_gu_v hmin hf0 hf1 ovX v gu hgu
                  hcompX.2 hvX hgu_props.1 hgu_props.2 hgv_ex
                have hsk_le : (compile n ovX C.gates).skipped.card ≤ C.size := by
                  have h1 := (compile_spec n ovX C).1
                  exact Nat.le_of_add_left_le h1.le
                have hlt_m : (∅ : Finset (Fin n)).card + G'.edgeFinset.card < m := by
                  rw [← hm, Finset.card_empty, zero_add, zero_add, ← hedge_card]
                  exact Nat.lt_add_of_pos_right (by decide)
                have hrec := ih ((∅ : Finset (Fin n)).card + G'.edgeFinset.card)
                  hlt_m (t - 1) (C.size - (compile n ovX C.gates).skipped.card)
                  G' ∅ rfl hacyc' (fun _ hm => by cases hm) (Or.inr hedge') hvc'_ex hvc'_min hcompX.1
                simp only [Finset.card_empty, zero_add] at hrec ⊢
                exact arith_drop G'.edgeFinset.card G.edgeFinset.card 2 (t - 1) t
                  C.size (compile n ovX C.gates).skipped.card s 1
                  hedge_card (Nat.sub_add_cancel ht1) hrec hsk3 hsk_le hCsz
              -- Dispatch on whether gu reads u on left or right
              rcases hgu_read with hL_u | hR_u
              · rcases bool_op_left_trichotomy (C.gates[gu]'hgu).op hdep.1 hdep.2 with hT | hF | hX
                · apply hfinish_T_const
                  have hspT := compile_step_props n ovT C
                  have huT : (compile n ovT C.gates).env u.val = WRef.const true :=
                    hspT.1 u.val u.isLt true (by simp [ovT])
                  exact (hspT.2 gu hgu (C.gates[gu]'hgu) (List.getElem?_eq_getElem hgu)).2.2.2.2.2.1
                    ⟨true, hgu_wf.1, hL_u.symm ▸ huT, hT⟩
                · apply hfinish_F_const
                  let ovF : ℕ → Option Bool := fun w => if w = u.val ∨ w = v.val then some false else none
                  have hspF := compile_step_props n ovF C
                  have huF : (compile n ovF C.gates).env u.val = WRef.const false :=
                    hspF.1 u.val u.isLt false (by simp [ovF])
                  exact (hspF.2 gu hgu (C.gates[gu]'hgu) (List.getElem?_eq_getElem hgu)).2.2.2.2.2.1
                    ⟨false, hgu_wf.1, hL_u.symm ▸ huF, hF⟩
                · apply hfinish_XOR
                  intro x0 x1 hag hx0 hx1
                  have hu_lt : u.val < n + gu := by have := u.isLt; omega
                  rw [wval_gate C x0 gu hgu, wval_gate C x1 gu hgu]
                  simp only [hgu_wf.2.1, ↓reduceIte, hL_u, hu_lt, wval_input, hx0, hx1]
                  have hR_ne : (C.gates[gu]'hgu).right ≠ u.val := hL_u ▸ hgu_wf.2.2.symm
                  have hR_eq := wval_eq_below_unique_reader C u gu htwo_u x0 x1 hag
                    (C.gates[gu]'hgu).right hgu_wf.2.1 hR_ne
                  rw [hR_eq]
                  exact hX _
              · rcases bool_op_right_trichotomy (C.gates[gu]'hgu).op hdep.1 hdep.2 with hT | hF | hX
                · apply hfinish_T_const
                  have hspT := compile_step_props n ovT C
                  have huT : (compile n ovT C.gates).env u.val = WRef.const true :=
                    hspT.1 u.val u.isLt true (by simp [ovT])
                  exact (hspT.2 gu hgu (C.gates[gu]'hgu) (List.getElem?_eq_getElem hgu)).2.2.2.2.2.2
                    ⟨true, hgu_wf.2.1, hR_u.symm ▸ huT, hT⟩
                · apply hfinish_F_const
                  let ovF : ℕ → Option Bool := fun w => if w = u.val ∨ w = v.val then some false else none
                  have hspF := compile_step_props n ovF C
                  have huF : (compile n ovF C.gates).env u.val = WRef.const false :=
                    hspF.1 u.val u.isLt false (by simp [ovF])
                  exact (hspF.2 gu hgu (C.gates[gu]'hgu) (List.getElem?_eq_getElem hgu)).2.2.2.2.2.2
                    ⟨false, hgu_wf.2.1, hR_u.symm ▸ huF, hF⟩
                · apply hfinish_XOR
                  intro x0 x1 hag hx0 hx1
                  have hu_lt : u.val < n + gu := by have := u.isLt; omega
                  rw [wval_gate C x0 gu hgu, wval_gate C x1 gu hgu]
                  simp only [hgu_wf.1, ↓reduceIte, hR_u, hu_lt, wval_input, hx0, hx1]
                  have hL_ne : (C.gates[gu]'hgu).left ≠ u.val := hR_u ▸ hgu_wf.2.2
                  have hL_eq := wval_eq_below_unique_reader C u gu htwo_u x0 x1 hag
                    (C.gates[gu]'hgu).left hgu_wf.1 hL_ne
                  rw [hL_eq]
                  exact hX _
          · -- G' has no edges: G has 2 edges (u-v, v-w) and t = 1
            have hE'0 : G'.edgeFinset.card = 0 := by
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
              intro e he
              induction e using Sym2.ind with
              | _ p q => exact hedge' ⟨p, q, G'.mem_edgeFinset.mp he⟩
            have ht_le1 : t - 1 ≤ 0 := hvc'_min ∅ (fun p q hpq => absurd ⟨p, q, hpq⟩ hedge')
            have hess := ess_card_le_size_add_one hmin hf0 hf1 ({u, v, w} : Finset (Fin n)) (fun i hi => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hi
              rcases hi with hi | hi | hi <;> rw [hi]
              · exact fGA_essential_edge G ∅ (fun _ hm => by cases hm) u v huv
              · exact fGA_essential_edge G ∅ (fun _ hm => by cases hm) v u (adj_symm huv)
              · exact fGA_essential_edge G ∅ (fun _ hm => by cases hm) w v (adj_symm hvw))
            have hcard3 : ({u, v, w} : Finset (Fin n)).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj huv, huw]),
                  Finset.card_pair (G.ne_of_adj hvw)]
            rw [hcard3] at hess
            simp only [Finset.card_empty, zero_add]
            have hE2 : G.edgeFinset.card = 2 := by rw [← hedge_card, hE'0]
            rw [hE2]
            exact Nat.le_trans (by omega : 2 + t ≤ 3) (Nat.le_trans hess (Nat.add_le_add_right hCsz 1))
    · -- Case: G has no edges
      have hE0 : G.edgeFinset.card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro e he
        induction e using Sym2.ind with
        | _ p q => exact hedge ⟨p, q, G.mem_edgeFinset.mp he⟩
      have ht0 : t ≤ 0 := hvc_min ∅ (fun p q hpq => absurd ⟨p, q, hpq⟩ hedge)
      have hess := ess_card_le_size_add_one hmin hf0 hf1 A (fun a ha => fGA_essential_mem G A a ha)
      rw [hE0, Nat.add_zero, Nat.eq_zero_of_le_zero ht0, Nat.add_zero]
      exact Nat.le_trans hess (Nat.add_le_add_right hCsz 1)

end LowerBound

end PEqualNP.Outside.L_meta_243

open PEqualNP.Outside.L_meta_243 in
theorem PEqualNP.Outside.L_meta_243 :
    ∀ (n t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.IsAcyclic →
      (∃ u v : Fin n, G.Adj u v) →
      (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      (PEqualNP.MetaComplexity.HasBinarySize n
        (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) s ↔
        G.edgeFinset.card + t ≤ s + 1) := by
  intro n t s G _ hacyc hedge hvc_ex hvc_min
  have hfeq : (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = fGA G ∅ := by
    funext x
    simp [fGA]
  rw [hfeq]
  constructor
  · intro hbs
    have h := lower_bound ((∅ : Finset (Fin n)).card + G.edgeFinset.card) t s G ∅ rfl hacyc
      (fun _ hm => by cases hm) (Or.inr hedge) hvc_ex hvc_min hbs
    simpa using h
  · intro hs
    exact upper_bound G ∅ (Or.inr hedge) hvc_ex hvc_min (by simpa using hs)
