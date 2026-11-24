import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1599
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

/-- The value of wire `w` on input `x`. -/
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

/-- With every AND gate false at `x`, a wire true at `x` is true at a single true input of `x`. -/
theorem single (gates : List Gate) {n : ℕ} (x : Fin n → Bool)
    (hao : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hand : ∀ (k : ℕ) (hk : k < gates.length), gates[k].op = GateOp.and →
      val gates (n + k) x = false) :
    ∀ (b w : ℕ), w < b → val gates w x = true →
      ∃ i : Fin n, x i = true ∧ val gates w (fun r : Fin n => decide (r = i)) = true := by
  intro b
  induction b with
  | zero => intro w hw; omega
  | succ b ih =>
    intro w hw hx
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rw [val_input gates x w hwn] at hx; exact hx
      · rw [val_input gates _ w hwn]; simp
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at hx; exact absurd hx (by simp)
      · have hk : w - n < gates.length := by omega
        have hweq : w = n + (w - n) := by omega
        rw [hweq] at hx ⊢
        rcases hao gates[w - n] (List.getElem_mem hk) with hop | hop
        · rw [hand (w - n) hk hop] at hx; exact absurd hx (by simp)
        · obtain ⟨a, ha, halt, hax⟩ := (val_or gates x (w - n) hk hop).1 hx
          obtain ⟨i, hi, hai⟩ := ih a (by omega) hax
          exact ⟨i, hi, (val_or gates _ (w - n) hk hop).2 ⟨a, ha, halt, hai⟩⟩

end PEqualNP.Outside.L_meta_1599

open PEqualNP.Outside.L_meta_1599 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned n G C := by
  classical
  intro n G _ C hao hfun u v huv
  set x : Fin n → Bool := PEqualNP.EdgeOwnership.pairInput u v with hx
  have hgate : ∀ (k : ℕ) (hk : k < C.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    intro k hk
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hk]
  have hex : ∃ k, k < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and ∧
      PEqualNP.EdgeOwnership.gateVal n C k x = true := by
    by_contra hcon
    push_neg at hcon
    have hand : ∀ (k : ℕ) (hk : k < C.gates.length), C.gates[k].op = GateOp.and →
        val C.gates (n + k) x = false := by
      intro k hk hop
      have := hcon k hk (by rw [hgate k hk]; exact hop)
      have e : PEqualNP.EdgeOwnership.gateVal n C k x = val C.gates (n + k) x := rfl
      rw [e] at this
      simpa using this
    have hout : val C.gates C.output x = true := by
      have h1 := congrFun hfun x
      have e : PEqualNP.MetaComplexity.circuitFun n C x = val C.gates C.output x := rfl
      rw [e] at h1
      rw [h1]
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u, v, huv, by simp [hx, PEqualNP.EdgeOwnership.pairInput],
        by simp [hx, PEqualNP.EdgeOwnership.pairInput]⟩
    obtain ⟨i, _, hi⟩ := single C.gates x hao hand (C.output + 1) C.output (by omega) hout
    have h1 := congrFun hfun (fun r : Fin n => decide (r = i))
    have e : PEqualNP.MetaComplexity.circuitFun n C (fun r : Fin n => decide (r = i))
        = val C.gates C.output (fun r : Fin n => decide (r = i)) := rfl
    rw [e, hi] at h1
    have h2 := h1.symm
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
      decide_eq_true_eq] at h2
    rcases h2 with ⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩
    · simp at ha
    · rw [ha, hb] at hab
      exact G.loopless.irrefl i hab
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  refine ⟨j, hj.1, hj.1, hj.2.1, hj.2.2, ?_⟩
  intro i hi _ hop
  by_contra hne
  have hval : PEqualNP.EdgeOwnership.gateVal n C i x = true := by simpa using hne
  exact Nat.find_min hex hi ⟨lt_trans hi hj.1, hop, hval⟩
