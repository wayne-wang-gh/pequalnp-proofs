import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1004

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)





theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def rows1004 : List ℕ := [10, 9, 9, 34, 9, 10, 4, 17, 34, 10, 4, 33, 36, 32, 32, 4, 36, 9, 1, 2, 2, 0, 1, 0, 10, 9, 9, 18, 9, 10, 4, 33, 18, 10, 4, 17, 20, 16, 16, 4, 20, 9, 1, 2, 2, 0, 1, 0, 9, 10, 10, 33, 10, 9, 4, 18, 33, 9, 4, 34, 36, 32, 32, 4, 36, 10, 2, 1, 1, 0, 2, 0, 9, 10, 10, 17, 10, 9, 4, 34, 17, 9, 4, 18, 20, 16, 16, 4, 20, 10, 2, 1, 1, 0, 2, 0, 36, 20, 20, 34, 20, 36, 8, 17, 34, 36, 8, 18, 10, 2, 2, 8, 10, 20, 16, 32, 32, 0, 16, 0, 20, 36, 36, 18, 36, 20, 8, 33, 18, 20, 8, 34, 10, 2, 2, 8, 10, 36, 32, 16, 16, 0, 32, 0, 36, 20, 20, 33, 20, 36, 8, 18, 33, 36, 8, 17, 9, 1, 1, 8, 9, 20, 16, 32, 32, 0, 16, 0, 20, 36, 36, 17, 36, 20, 8, 34, 17, 20, 8, 33, 9, 1, 1, 8, 9, 36, 32, 16, 16, 0, 32, 0, 11, 5, 12, 38, 13, 3, 12, 19, 6, 26, 6, 3, 5, 48, 40, 52, 35, 21, 6, 48, 35, 24, 37, 12, 11, 5, 12, 22, 13, 3, 12, 35, 6, 42, 6, 3, 5, 48, 24, 52, 19, 37, 6, 48, 19, 40, 21, 12, 11, 6, 12, 37, 14, 3, 12, 19, 5, 25, 5, 3, 6, 48, 40, 52, 35, 22, 5, 48, 35, 24, 38, 12, 11, 6, 12, 21, 14, 3, 12, 35, 5, 41, 5, 3, 6, 48, 24, 52, 19, 38, 5, 48, 19, 40, 22, 12, 52, 24, 12, 42, 28, 48, 12, 49, 40, 37, 40, 48, 24, 3, 6, 11, 50, 25, 40, 3, 50, 5, 26, 12, 52, 40, 12, 26, 44, 48, 12, 49, 24, 21, 24, 48, 40, 3, 6, 11, 50, 41, 24, 3, 50, 5, 42, 12, 52, 24, 12, 41, 28, 48, 12, 50, 40, 38, 40, 48, 24, 3, 5, 11, 49, 26, 40, 3, 49, 6, 25, 12, 52, 40, 12, 25, 44, 48, 12, 50, 24, 22, 24, 48, 40, 3, 5, 11, 49, 42, 24, 3, 49, 6, 41, 12]

def xs1004 : List ℕ := [0x59e00859e0082aa2802aa280150fa9150fa95318b35318b3017908017908000080000080180329180329460896460896, 0x2aa2802aa28059e00859e0085318b35318b3150fa9150fa9000080000080017908017908460896460896180329180329, 0xa04255a04255a04255a04255c6955ec6955ec6955ec6955e020237020237020237020237019440019440019440019440, 0xc6955ec6955ec6955ec6955ea04255a04255a04255a04255019440019440019440019440020237020237020237020237, 0x150fa95318b3150fa95318b359e0082aa28059e0082aa280180329460896180329460896017908000080017908000080, 0x5318b3150fa95318b3150fa92aa28059e0082aa28059e008460896180329460896180329000080017908000080017908]

abbrev f1004 : BFn 6 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 3 && x 5))

theorem rows1004_len : rows1004.length = 384 := by decide +kernel

theorem enc_inputs1004 :
    (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map (fun a => encL a rows1004)
      = xs1004 := by decide +kernel

theorem enc_goal1004 : encL f1004 rows1004 = goal 192 := by decide +kernel

theorem mask1004 : mask 192 = 2 ^ rows1004.length - 1 := by decide +kernel

theorem proper_fail1004 : ∀ zs ∈ xs1004.sublists, zs ≠ xs1004 →
    (cov 192 zs &&& lo 192) ≠ lo 192 := by decide +kernel

theorem no_sub1004 (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 192) (goal 192) s xs1004) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xs1004 → NatRun (mask 192) (goal 192) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xs1004
  · subst e; exact noRunFull s hs h
  · exact proper_fail1004 zs (List.mem_sublists.2 hz) e (required h)

theorem main1004 (noRunFull : ∀ s ≤ 9, ¬ NatRun (mask 192) (goal 192) s xs1004) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 3 && x 5)) 9 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run f1004 ⟨fun _ => false, fun _ => true, by decide⟩ 9 h
  have hr : NatRun (mask 192) (encL f1004 rows1004) s' (ws.map fun a => encL a rows1004) :=
    Run.map (fun a : BFn 6 => encL a rows1004)
      (fun a => by rw [mask1004]; exact encL_inv a rows1004)
      (fun a b => encL_and a b rows1004) (fun a b => encL_or a b rows1004) hrun
  rw [enc_goal1004] at hr
  refine no_sub1004 noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputs1004]
  exact hsub.map _





def blockWord (d : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | q::r, w => ((w >>> (d*q)) &&& lo d) ||| (blockWord d r w <<< d)

theorem block_hom (d : Nat) (qs : List Nat) (a b : Nat) :
    blockWord d qs (a &&& b) = (blockWord d qs a &&& blockWord d qs b) ∧
    blockWord d qs (a ||| b) = (blockWord d qs a ||| blockWord d qs b) ∧
    blockWord d qs (a ^^^ b) = (blockWord d qs a ^^^ blockWord d qs b) := by
  induction qs with
  | nil => simp [blockWord]
  | cons q qs ih =>
    refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      by_cases hj : d ≤ j <;>
      simp [blockWord,lo,Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hj, ih,
        Nat.not_lt_of_ge, Nat.lt_of_not_ge] <;> grind

theorem block_run {s ws k} (h : NatRun (mask k) (goal k) s ws)
    (d : Nat) (qs : List Nat) (hm : blockWord d qs (mask k) = mask k)
    (hg : blockWord d qs (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (blockWord d qs)) := by
  rw [← hg]
  exact Run.map _ (fun a => (block_hom d qs a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (block_hom d qs a b).1) (fun a b => (block_hom d qs a b).2.1) h





theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]





def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]





def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih





def edgeHash : List Nat → Nat
  | [] => 0
  | w :: t => (w % 4294967291 + 317)^3 % 4294967291 + 1 + edgeHash t

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/16 < N s && (rot (v/2 % 8) zs).isPerm (S s (v/16)))))

theorem barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/16 < N s && (rot (v/2 % 8) zs).isPerm (S s (v/16))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h





def t1 : Nat := 0x0

def t2 : Nat := 0x10000010000000000000000000000000000000000000000000000000

def t3 : Nat := 0x80110000000080110000000000000000000000000000000000000000000000000000

def t4 : Nat := 0x200000000000008020000400000000000000000000000000000000000000000000000000000

def t5 : Nat := 0x1000001000001000001008000008000008000008000000000000000000000000000000000000000000000000000

def t6 : Nat := 0x11000201000011000201028000408008028000408008020016000221020016000221000000011000000000011000

def t7 : Nat := 0x211000211000211000211428008428008428008428008020237020237020237020237011000011000011000011000

def t8 : Nat := 0x280020080110008510000510000020080110008000280000000000080000108000800000800000080000108000000

def t9 : Nat := 0x281020091110209510011518008028080518008028280000221020096000329020816011800000080011108000000

def t10 : Nat := 0x4000004000200200200200040508040508421012421012000000000000000000000000000000000000000000000000

def t11 : Nat := 0x401100420120021120020106850844850842901242901a020016000221020016000221000000011000000000011000

def t12 : Nat := 0x20280020280510008510008530080530080110288110288000080000080000908000908000880000880000108000108

def t13 : Nat := 0x218b3040fa1511833150d292aa00048e00028a20008e008460096180221460816180329000080017800000000017108

def t14 : Nat := 0x40708421012040708421012514008220280514008220280180329460896180329460896017908000080017908000080

def t15 : Nat := 0x4070942101304070942101340c00822820040c008228200000221020016000221020016011000000000011000000000

def t16 : Nat := 0x40788421092150508531012514000220280114008200280000000000080000108000800000800000080000108000000

def t17 : Nat := 0x61da2061da2551d2a551d2a286000286000286200286200fc84c0fc84c0fdfd48fdfd48e66896e66896b86329b86329

def t18 : Nat := 0x8a00008a00008a00008a0001108a11108a11108a11108a1000000000000000000000000000000000000000000000000

def t19 : Nat := 0x8a2800aa08019a00859a0005108a11308a11108a9110aa1000000000080000108000800000800000080000108000000

def t20 : Nat := 0x8e00008e00028a20028a200150da9150da95318b35318b3000000000000000000000000000000000000000000000000

def t21 : Nat := 0xaa0000aa00048a00848a0081108b11108b1110aa1110aa1000000000000011000011000020016020016000221000221

def t22 : Nat := 0xaa0800aa08059a00859a0081108a11108a1110aa1110aa1000080000080017908017908460896460896180329180329

def t23 : Nat := 0xca5084ab0020ca5084ab002114821200aa1114821200aa1b9f548e5fcc0b9f548e5fcc0fe6b3ffe02b7fe6b3ffe02b7

def t24 : Nat := 0x150da85318a2150da85318a2196000282280196000282280180108440880180108440880006908000080006908000080

def t25 : Nat := 0x150da95318a3150da95318a319e00028a28019e00028a280180108440880180108440880006908000080006908000080

def t26 : Nat := 0x150da95318b3150fa95318b319e00828a28059e0002aa280000108000800000000000080000108000000000800000080

def t27 : Nat := 0x150da95318b3150fa95318b319e00828a28059e0002aa280180329460896180329460896017908000080017908000080

def t28 : Nat := 0x150fa95318a3150fa95318a359e0082aa28059e0082aa280180329460896180329460896017908000080017908000080

def t29 : Nat := 0x150fa95318b3150fa95318b348e0082aa20048e0082aa200000221020016000221020016011000000000011000000000

def t30 : Nat := 0x150fa95318b3150fa95318b348e0082aa20048e0082aa200180329460896180329460896017908000080017908000080

def t31 : Nat := 0x150fa95318b3150fa95318b359e0082aa28059e0082aa280180329460896180329460896017908000080017908000080

def t32 : Nat := 0x150fb9531ab3150fb9531ab35be0086aa2885be0086aa2881a033f460ab71a033f460ab7017908011080017908011080

def t33 : Nat := 0x154fa95358b3350fa9731ab35de5082ea7885bf01a6ab292180329460896180329460896017908000080017908000080

def t34 : Nat := 0x170fa9531ab3550fa95318bb5be0887ba28059e2883ba2881803a9460896180b2946099e017988000880017908000188

def t35 : Nat := 0x178fa95398b3558fa95398bb59e0192aa29159e2092aa28118032946089619132947189603791e020096017b290002a1

def t36 : Nat := 0x1928a01928a01928a01928a01928a01928a01928a01928a0fc6988fc6988fc6988fc6988fc6988fc6988fc6988fc6988

def t37 : Nat := 0x1968a11968a1392aa1392aa11dada81dada85bb8a25bb8a2fe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t38 : Nat := 0x1dafa95bb8b31dafa95bb8b359e8a93baaa159e8a93baaa1180329460896180329460896017908000080017908000080

def t39 : Nat := 0x20420020420020420020420046151a46151a46151a46151a000000000000000000000000000000000000000000000000

def t40 : Nat := 0x20420120420120420120420146950a46950a46950a46950a020237020237020237020237019440019440019440019440

def t41 : Nat := 0x261fa3261fa3555d2b555d2b6af0026af0022ce7082ce708fe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t42 : Nat := 0x286200286200286200286200571daa571daa571daa571daafe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t43 : Nat := 0x28a20028a20008e00008e0005318b35318b3150da9150da9000000000000000000000000000000000000000000000000

def t44 : Nat := 0x28e20028e20028e20028e200571dbb571dbb571dbb571dbb000000000000000000000000000000000000000000000000

def t45 : Nat := 0x2aa2802aa28059e00859e0085318b35318b3150fa9150fa9000080000080017908017908460896460896180329180329

def t46 : Nat := 0x2ae2802ae28079e20879e208571dbb571dbb571fbb571fbb000080000080017908017908460896460896180329180329

def t47 : Nat := 0x2ea7886ab2925de5085bf01a5358b3731ab3154fa9350fa9000080000080017908017908460896460896180329180329

def t48 : Nat := 0x314aa1314aa1314aa1314aa14eb50a4eb50a4eb50a4eb50afe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t49 : Nat := 0x396aa1396aa1396aa1396aa15fbdaa5fbdaa5fbdaa5fbdaafe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t50 : Nat := 0x396aa1396aa1396aa1396aa15fbdaa5fbdaa5fbdba5fbdbafe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t51 : Nat := 0x39eaa139eaa139eaa139eaa15fbdab5fbdab5fbdab5fbdabfe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t52 : Nat := 0x3baaa13baaa159e8a959e8a95bb8b35bb8b31dafa91dafa9000080000080017908017908460896460896180329180329

def t53 : Nat := 0x3beaa13beaa179eaa979eaa95fbdbb5fbdbb5fbfab5fbfabfe6bbffe6bbfff7bbfff7bbffffddefffddefdffe9fdffe9

def t54 : Nat := 0x3d6fa97b7ab33d6fa97b7ab35ffdaa7fbfaa5ffdaa7fbfaafe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t55 : Nat := 0x3fafa97bbab35defa95bf8bb5bf8bb7bbab35defa93fafa91803a9460896197b2947799e47799e460896197b291803a9

def t56 : Nat := 0x5318b3150fa95318b3150fa92aa28059e0082aa28059e008460896180329460896180329000080017908000080017908

def t57 : Nat := 0x5358b3154fa9731ab3350fa92ea7885de5086ab2925bf01a460896180329460896180329000080017908000080017908

def t58 : Nat := 0x571daa571daa571daa571daa286200286200286200286200fdfdc8fdfdc8fdfdc8fdfdc8fe6bbffe6bbffe6bbffe6bbf

def t59 : Nat := 0x571dbb571fbb571dbb571fbb2ae28079e2082ae28079e208460896180329460896180329000080017908000080017908

def t60 : Nat := 0x571fbb571fbb571fbb571fbb7be2887be2887be2887be2885e0bbf5e0bbf5e0bbf5e0bbf017988017988017988017988

def t61 : Nat := 0x59e00859e0082aa2802aa280150fa9150fa95318b35318b3017908017908000080000080180329180329460896460896

def t62 : Nat := 0x59e00859e0082aa2802aa280150fb9150fb95318b35318b3017908017908000080000080180329180329460896460896

def t63 : Nat := 0x59e00859e0182aa2802aa290150fa9150fa95318b35318b3017908017908000080000080180329180329460896460896

def t64 : Nat := 0x59e00859e2082aa2802aa280170fa9550fa95318b35318bb017908017908000080000080180329180329460896460896

def t65 : Nat := 0x59e0085be0082aa2886aa280150fa9150fa95318b3531ab3017908017908000080000080180329180329460896460896

def t66 : Nat := 0x59e00959e0092aa2812aa281158fa9158fa95398b35398b3017908017908000080000080180329180329460896460896

def t67 : Nat := 0x59e08859e0883ba2803ba280150fa9150fa95318b35318b3017908017908000080000080180329180329460896460896

def t68 : Nat := 0x59e8a959e8a93baaa13baaa11dafa91dafa95bb8b35bb8b3017908017908000080000080180329180329460896460896

def t69 : Nat := 0x5bb8b31dafa95bb8b31dafa93baaa159e8a93baaa159e8a9460896180329460896180329000080017908000080017908

def t70 : Nat := 0x5bf01a5de5086ab2922ea788350fa9154fa9731ab35358b3017908017908000080000080180329180329460896460896

def t71 : Nat := 0x5bf8b31defa97bbab33dafa93fafa95deda97bbab35bf8bb460896180329460896180329000080017908000080017908

def t72 : Nat := 0x5bf8bb5deda97bbab33fafa93dafa91defa97bbab35bf8b3017908017908000080000080180329180329460896460896

def t73 : Nat := 0x5bf8bb5defa97bbab33fafa93fafa95defa97bbab35bf8bb47799e197b294608961803a91803a9197b2946089647799e

def t74 : Nat := 0x5de5085bf01a2ea7886ab292154fa9350fa95358b3731ab3017908017908000080000080180329180329460896460896

def t75 : Nat := 0x5defa95bf8bb3fafa97bbab35defa93fafa95bf8bb7bbab3197b2947799e1803a9460896197b291803a947799e460896

def t76 : Nat := 0x5dfd2a5dfd2a2ebfa22ebfa23d6fa93d6fa97b78b37b78b3fdfd48fdfd48fc84c0fc84c0b86329b86329e66896e66896

def t77 : Nat := 0x5fbdaa5fbdaa5fbdaa5fbdaa396aa1396aa1396aa1396aa1fdfdc8fdfdc8fdfdc8fdfdc8fe6bbffe6bbffe6bbffe6bbf

def t78 : Nat := 0x5ff51a5ff51a6eb79a6eb79a354fa9354fa9735ab3735ab3017908017908000080000080180329180329460896460896

def t79 : Nat := 0x5fffbb5fffbb7fbfbb7fbfbb7fefa97fefa97bfabb7bfabb5f7bbf5f7bbf5e0bbf5e0bbf197ba9197ba947799e47799e

def t80 : Nat := 0x79e20879e2082ae2802ae280571fbb571fbb571dbb571dbb017908017908000080000080180329180329460896460896

def t81 : Nat := 0x7bbab33fafa95bf8bb5deda97bbab35bf8b33dafa91defa9000080000080017908017908460896460896180329180329

def t82 : Nat := 0x7be2887be2887be2887be288571fbb571fbb571fbb571fbb0179880179880179880179885e0bbf5e0bbf5e0bbf5e0bbf

def t83 : Nat := 0x7fffab7fffab7fffab7fffab7fffab7fffab7fffab7fffabffffffffffffffffffffffffffffffffffffffffffffffff

def t84 : Nat := 0x800054800054800054800054800054800054800054800054000000000000000000000000000000000000000000000000

def t85 : Nat := 0x800055800255800055800255828054c0805c828054c0805c020016000221020016000221000000011000000000011000

def t86 : Nat := 0x804054804054a00254a0025484055c84055cc21056c21056000000000000000000000000000000000000000000000000

def t87 : Nat := 0x804055804055a00255a0025584854c84854cc29056c29056020237020237020237020237019440019440019440019440

def t88 : Nat := 0x841d77841d77841d77841d77a8e044a8e044a8e044a8e044fe8677fe8677fe8677fe8677a1f440a1f440a1f440a1f440

def t89 : Nat := 0x84454cc05056a40744a2105684454ca40744c05056a21056b9f769e7fc56b88661e684d6b9f769b88661e7fc56e684d6

def t90 : Nat := 0x861556861556c4155ec4155ea04054a04054a04244a04244008440008440019440019440020016020016000221000221

def t91 : Nat := 0x861df7861df7d51d7fd51d7fa8e044a8e044a8e244a8e244fe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t92 : Nat := 0x950ffdd318f7950ffdd318f7d9e05caaa2d4d9e05caaa2d4180329460896180329460896017908000080017908000080

def t93 : Nat := 0xa00254a00254804054804054c21056c2105684055c84055c000000000000000000000000000000000000000000000000

def t94 : Nat := 0xa00255a00255804055804055c29056c2905684854c84854c020237020237020237020237019440019440019440019440

def t95 : Nat := 0xa04245a04255a04245a04255c6955ec6955ec6955ec6955e020237020237020237020237019440019440019440019440

def t96 : Nat := 0xa04254a04254a04254a04254c6155ec6155ec6155ec6155e000000000000000000000000000000000000000000000000

def t97 : Nat := 0xa04254a04254a04254a04254c6155ec6155ec6155ec6155e020237020237020237020237019440019440019440019440

def t98 : Nat := 0xa04255a04255a04255a04255c6955ec6955ec6955ec6955e020237020237020237020237019440019440019440019440

def t99 : Nat := 0xa042d5a242d5b1425df14255d7955ec695ded7955ec697de0202370202b702033f020a37019c400194c0019548019440

def t100 : Nat := 0xa202d5a202d5d1405dd1405dc29056c2905684874c84874c0202b70202b7037b3f037b3f479cd6479cd6199769199769

def t101 : Nat := 0xa21af7a40fe5d15877954d6deab056caf056aca74c8ce54cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t102 : Nat := 0xa2c255a2c255e0c25de0c25dc6955fc6955fc6975fc6975f020237020237031237031237039456039456019661019661

def t103 : Nat := 0xa4475de25257a4475de25257c6d55ee6975ec6d55ee6975e020237020237020237020237019440019440019440019440

def t104 : Nat := 0xa61756a61756c4555ec4555ee25056e25056a4474ca4474cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t105 : Nat := 0xa61ff7a61ff7d55d7fd55d7feaf056eaf056ace74cace74cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t106 : Nat := 0xa61ff7a61ff7d55d7fd55d7feaf056eaf056ace75cace75cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t107 : Nat := 0xa61fffe61ff7d55d7fd75d7feaf056eaf256ace74cace74cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t108 : Nat := 0xa65ff7a65ff7f55f7ff55f7feef55eeef55eeef75eeef75efe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t109 : Nat := 0xa8e254a8e254a8e254a8e254d71dffd71dffd71dffd71dff000000000000000000000000000000000000000000000000

def t110 : Nat := 0xa8e255a8e255a8e255a8e255d79dffd79dffd79dffd79dff020237020237020237020237019440019440019440019440

def t111 : Nat := 0xaaa2d4aaa2d4d9e05cd9e05cd318f7d318f7950ffd950ffd000080000080017908017908460896460896180329180329

def t112 : Nat := 0xaae2d4aae2d4f9e25cf9e25cd71dffd71dffd71fffd71fff000080000080017908017908460896460896180329180329

def t113 : Nat := 0xaae2d5aae2d5f9e25df9e25dd79dffd79dffd79fffd79fff0202b70202b7037b3f037b3f479cd6479cd6199769199769

def t114 : Nat := 0xace74ceaf056ace74ceaf056d55d7fa61ff7d55d7fa61ff7b9f769e7fcd6b9f769e7fcd6ffff7ffe86f7ffff7ffe86f7

def t115 : Nat := 0xace75deaf257ace75deaf257d7dd7fe69fffd7dd7fe69fffbbf77fe7fef7bbf77fe7fef7ffff7fff96f7ffff7fff96f7

def t116 : Nat := 0xaeb7d6aeb7d6ddf55eddf55ef358f7f358f7b54fedb54fed0084c00084c001fd4801fd48460896460896180329180329

def t117 : Nat := 0xaebff7aebff7ddfd7fddfd7ffbf8f7fbf8f7bdefedbdefedfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t118 : Nat := 0xaee7cceaf2d6fde74cfbf05ed75dfff71ff7d55fffb71fffb9f7e9e7fcd6b9ff69e7fddefffffffe8ef7ffff7ffe87ff

def t119 : Nat := 0xaeffffeefff7fdff7ffffd7ffffd7feefff7fdff7faefffffff7fffffef7ffff7ffffffffffffffffef7ffff7ffff7ff

def t120 : Nat := 0xb14af5b14af5b14af5b14af5ceb55eceb55eceb55eceb55e020237020237020237020237019440019440019440019440

def t121 : Nat := 0xb54ffdf35af7b54ffdf35af7dff55eeeb7dedff55eeeb7de1a033f460ab71a033f460ab701fd480194c001fd480194c0

def t122 : Nat := 0xb71ff7b71ff7d55dffd55dffeaf056eaf056ace74cace74cfe86f7fe86f7ffff7fffff7fe7fcd6e7fcd6b9f769b9f769

def t123 : Nat := 0xb71ffff71ff7d55fffd75dfffbf05eeaf2d6fde74caee7ccfe87fffe8ef7ffff7fffffffe7fddee7fcd6b9ff69b9f7e9

def t124 : Nat := 0xb96af5b96af5b96af5b96af5dfbdfedfbdfedfbdfedfbdfefe6bbffe6bbffe6bbffe6bbffdfdc8fdfdc8fdfdc8fdfdc8

def t125 : Nat := 0xbdefedfbfaf7bdefedfbfaf7dffdffffbfffdffdffffbfffffffffffffffffffffffffffffffffffffffffffffffffff

def t126 : Nat := 0xbf7ff7bf7ff7fd7ffffd7ffffffdfefffdfeffffeeffffeefeeffffeeffffffffffffffffffddefffddefdffe9fdffe9

def t127 : Nat := 0xbfeffdfbfaf7fdeffdfbfaffdffdffffbfffdfffffffbfff1a03bf460ab71b7b3f477bbf47fdde479cd619ff691997e9

def t128 : Nat := 0xc6955ec6955ec6955ec6955ea04255a04255a04255a04255019440019440019440019440020237020237020237020237

def t129 : Nat := 0xc6955ec6955ec6955ec6955ea042d5b14255a042d5b14255019440019440019440019440020237020237020237020237

def t130 : Nat := 0xc6955ec6955ec6955ec6975ea04255a0425da24255e04255019440019440019440019440020237020237020237020237

def t131 : Nat := 0xc6955fc6955fc6955fc6955fa0c255a0c255a0c255a0c255019440019440019440019440020237020237020237020237

def t132 : Nat := 0xc695dec695ded7955ed7955ea04255a04255a04255a04255019440019440019440019440020237020237020237020237

def t133 : Nat := 0xc6d55ec6d55ee6975ee6975ea4475da4475de25257e25257019440019440019440019440020237020237020237020237

def t134 : Nat := 0xceb55eceb55eceb55eceb55eb14af5b14af5b14af5b14af5019440019440019440019440020237020237020237020237

def t135 : Nat := 0xcef55ecef55eeeb75eeeb75eb54ffdb54ffdf35af7f35af7019440019440019440019440020237020237020237020237

def t136 : Nat := 0xd318f7950ffdd318f7950ffdaaa2d4d9e05caaa2d4d9e05c460896180329460896180329000080017908000080017908

def t137 : Nat := 0xd55d7fd55d7fa61ff7a61ff7ace74cace74ceaf056eaf056ffff7fffff7ffe86f7fe86f7b9f769b9f769e7fcd6e7fcd6

def t138 : Nat := 0xd79dffd79dffd79dffd79dffa8e255a8e255a8e255a8e255019440019440019440019440020237020237020237020237

def t139 : Nat := 0xd79dffd79fffd79dffd79fffaae2d5f9e25daae2d5f9e25d479cd6199769479cd61997690202b7037b3f0202b7037b3f

def t140 : Nat := 0xd79fffd79dffd79fffd79dfff9e25daae2d5f9e25daae2d5199769479cd6199769479cd6037b3f0202b7037b3f0202b7

def t141 : Nat := 0xd79fffd79fffd79fffd79ffffbe2ddfbe2ddfbe2ddfbe2dd5f9fff5f9fff5f9fff5f9fff037bbf037bbf037bbf037bbf

def t142 : Nat := 0xd9e05cd9e05caaa2d4aaa2d4950ffd950ffdd318f7d318f7017908017908000080000080180329180329460896460896

def t143 : Nat := 0xdbf05edde55ceab2d6aea7dcb50ffd954ffdf31af7d358f7017908017908000080000080180329180329460896460896

def t144 : Nat := 0xddf55eddf55eaeb7d6aeb7d6b54fedb54fedf358f7f358f701fd4801fd480084c00084c0180329180329460896460896

def t145 : Nat := 0xdff55edff55eeeb7deeeb7deb54ffdb54ffdf35af7f35af701fd4801fd480194c00194c01a033f1a033f460ab7460ab7

def t146 : Nat := 0xe25257a4475de25257a4475de6975ec6d55ee6975ec6d55e020237020237020237020237019440019440019440019440

def t147 : Nat := 0xe6975ee6975ec6d55ec6d55ee25257e25257a4475da4475d019440019440019440019440020237020237020237020237

def t148 : Nat := 0xe69fffe69fffd7dd7fd7dd7feaf257eaf257ace75dace75dff96f7ff96f7ffff7fffff7fe7fef7e7fef7bbf77fbbf77f

def t149 : Nat := 0xe6d75ee6d75ee6d75ee6d75ee6575fe6575fe6575fe6575f019440019440019440019440020237020237020237020237

def t150 : Nat := 0xe6d75fe6d75fe6d75fe6d75fe6d75fe6d75fe6d75fe6d75f039677039677039677039677039677039677039677039677

def t151 : Nat := 0xeaf056ace74ceaf056ace74ca61ff7d55d7fa61ff7d55d7fe7fcd6b9f769e7fcd6b9f769fe86f7ffff7ffe86f7ffff7f

def t152 : Nat := 0xeeb7deeeb7dedff55edff55ef35af7f35af7b54ffdb54ffd0194c00194c001fd4801fd48460ab7460ab71a033f1a033f

def t153 : Nat := 0xeef75eeef75eeef75eeef75ef75ffff75ffff75ffff75fff019440019440019440019440020237020237020237020237

def t154 : Nat := 0xeef75eeef75eeef75eeef75ef75ffff75ffff75ffff75fffffffffffffffffffffffffffffffffffffffffffffffffff

def t155 : Nat := 0xeef7dfeef7dffff75ffff75ff7dffff7dffff7dffff7dfff0396f70396f703ff7f03ff7f479ef7479ef71b977f1b977f

def t156 : Nat := 0xf35af7b54ffdf35af7b54ffdeeb7dedff55eeeb7dedff55e460ab71a033f460ab71a033f0194c001fd480194c001fd48

def t157 : Nat := 0xf71ffff71fffd75dffd75dffeaf256eaf256ace74cace74cffffffffffffffffffffffffffffffffffffffffffffffff

def t158 : Nat := 0xf75ffff75ffff75ffff75fffeef75eeef75eeef75eeef75effffffffffffffffffffffffffffffffffffffffffffffff

def t159 : Nat := 0xf75ffff75ffff75ffff75ffffff7defff7defff7defff7de5e0bbf5e0bbf5e0bbf5e0bbf01fdc801fdc801fdc801fdc8

def t160 : Nat := 0xf9e25cf9e25caae2d4aae2d4d71fffd71fffd71dffd71dff017908017908000080000080180329180329460896460896

def t161 : Nat := 0xf9e25df9e25daae2d5aae2d5d79fffd79fffd79dffd79dff037b3f037b3f0202b70202b7199769199769479cd6479cd6

def t162 : Nat := 0xfff7defff7defff7defff7def75ffff75ffff75ffff75fff01fdc801fdc801fdc801fdc85e0bbf5e0bbf5e0bbf5e0bbf

def t163 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def rowsE (i : Nat) : List Nat :=
  (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then [] else []) else (if i < 3 then [] else [])) else (if i < 6 then (if i < 5 then [t31,t56,t109,t128] else [t31,t56,t110,t153]) else (if i < 7 then [t18,t31,t56,t96,t128] else [t18,t31,t56,t98,t149]))) else (if i < 12 then (if i < 10 then (if i < 9 then [t20,t31,t56,t93,t128] else [t20,t31,t56,t98,t147]) else (if i < 11 then [t31,t44,t56,t98,t128] else [t31,t44,t56,t110,t128])) else (if i < 14 then (if i < 13 then [t31,t45,t56,t110,t133] else [t31,t45,t56,t110,t135]) else (if i < 15 then [t31,t45,t71,t98,t135] else [t31,t46,t56,t110,t128])))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then [t31,t49,t56,t82,t110] else [t31,t56,t58,t82,t128]) else (if i < 19 then [t31,t56,t82,t110,t128] else [t31,t56,t82,t110,t134])) else (if i < 22 then (if i < 21 then [t31,t56,t88,t110,t128] else [t31,t56,t110,t128,t162]) else (if i < 23 then [t31,t56,t110,t145,t152] else [t31,t56,t112,t128,t161]))) else (if i < 28 then (if i < 26 then (if i < 25 then [t31,t69,t82,t98,t134] else [t31,t69,t82,t110,t128]) else (if i < 27 then [t31,t69,t98,t145,t152] else [t31,t72,t81,t98,t128])) else (if i < 30 then (if i < 29 then [t31,t82,t110,t114,t128] else [t38,t69,t82,t98,t128]) else (if i < 31 then [t10,t31,t43,t56,t98,t128] else [t10,t31,t45,t56,t110,t128]))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then [t18,t31,t39,t56,t98,t128] else [t18,t31,t45,t56,t98,t133]) else (if i < 35 then [t18,t31,t46,t56,t98,t128] else [t18,t31,t49,t56,t82,t98])) else (if i < 38 then (if i < 37 then [t18,t31,t56,t77,t82,t128] else [t18,t31,t56,t82,t98,t128]) else (if i < 39 then [t18,t31,t56,t82,t98,t134] else [t18,t31,t56,t82,t110,t128]))) else (if i < 44 then (if i < 42 then (if i < 41 then [t18,t31,t56,t88,t98,t128] else [t18,t31,t56,t98,t128,t162]) else (if i < 43 then [t18,t31,t56,t98,t145,t152] else [t18,t31,t69,t82,t98,t128])) else (if i < 46 then (if i < 45 then [t18,t31,t82,t98,t114,t128] else [t20,t31,t45,t49,t56,t98]) else (if i < 47 then [t20,t31,t45,t56,t77,t128] else [t20,t31,t45,t56,t98,t128])))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then [t20,t31,t45,t56,t98,t135] else [t20,t31,t45,t56,t110,t128]) else (if i < 51 then [t20,t31,t45,t71,t98,t128] else [t20,t31,t45,t98,t114,t128])) else (if i < 54 then (if i < 53 then [t20,t31,t46,t56,t98,t128] else [t20,t31,t56,t82,t98,t128]) else (if i < 55 then [t20,t31,t56,t98,t128,t137] else [t20,t31,t56,t98,t128,t152]))) else (if i < 60 then (if i < 58 then (if i < 57 then [t25,t45,t56,t61,t77,t128] else [t25,t45,t56,t61,t98,t128]) else (if i < 59 then [t26,t45,t56,t61,t98,t128] else [t27,t45,t56,t61,t98,t128])) else (if i < 62 then (if i < 61 then [t28,t45,t56,t61,t98,t128] else [t29,t45,t56,t61,t98,t128]) else (if i < 63 then [t30,t45,t56,t61,t98,t128] else [t31,t37,t45,t56,t61,t98])))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then [t31,t41,t45,t56,t98,t128] else [t31,t42,t45,t56,t61,t98]) else (if i < 67 then [t31,t45,t48,t56,t61,t98] else [t31,t45,t49,t56,t61,t77])) else (if i < 70 then (if i < 69 then [t31,t45,t49,t56,t61,t98] else [t31,t45,t49,t56,t61,t103]) else (if i < 71 then [t31,t45,t49,t56,t61,t110] else [t31,t45,t49,t56,t61,t120]))) else (if i < 76 then (if i < 74 then (if i < 73 then [t31,t45,t49,t56,t68,t98] else [t31,t45,t49,t56,t70,t98]) else (if i < 75 then [t31,t45,t49,t56,t77,t105] else [t31,t45,t49,t56,t80,t98])) else (if i < 78 then (if i < 77 then [t31,t45,t49,t56,t98,t105] else [t31,t45,t49,t56,t98,t142]) else (if i < 79 then [t31,t45,t49,t57,t61,t98] else [t31,t45,t49,t59,t61,t98])))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then [t31,t45,t49,t61,t69,t98] else [t31,t45,t49,t61,t98,t114]) else (if i < 83 then [t31,t45,t49,t61,t98,t136] else [t31,t45,t49,t98,t105,t114])) else (if i < 86 then (if i < 85 then [t31,t45,t50,t56,t61,t98] else [t31,t45,t51,t56,t61,t98]) else (if i < 87 then [t31,t45,t56,t61,t95,t128] else [t31,t45,t56,t61,t96,t128]))) else (if i < 92 then (if i < 90 then (if i < 89 then [t31,t45,t56,t61,t97,t128] else [t31,t45,t56,t61,t98,t128]) else (if i < 91 then [t31,t45,t56,t61,t98,t129] else [t31,t45,t56,t61,t98,t130])) else (if i < 94 then (if i < 93 then [t31,t45,t56,t61,t98,t131] else [t31,t45,t56,t61,t98,t132]) else (if i < 95 then [t31,t45,t56,t61,t98,t133] else [t31,t45,t56,t61,t98,t134]))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then [t31,t45,t56,t61,t98,t135] else [t31,t45,t56,t61,t98,t138]) else (if i < 99 then [t31,t45,t56,t61,t98,t149] else [t31,t45,t56,t61,t110,t134])) else (if i < 102 then (if i < 101 then [t31,t45,t56,t62,t98,t128] else [t31,t45,t56,t63,t98,t128]) else (if i < 103 then [t31,t45,t56,t64,t98,t128] else [t31,t45,t56,t65,t98,t128]))) else (if i < 108 then (if i < 106 then (if i < 105 then [t31,t45,t56,t66,t98,t128] else [t31,t45,t56,t67,t98,t128]) else (if i < 107 then [t31,t45,t56,t68,t98,t128] else [t31,t45,t56,t68,t98,t138])) else (if i < 110 then (if i < 109 then [t31,t45,t56,t68,t120,t128] else [t31,t45,t56,t70,t98,t128]) else (if i < 111 then [t31,t45,t56,t70,t128,t146] else [t31,t45,t56,t72,t98,t128])))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then [t31,t45,t56,t76,t98,t128] else [t31,t45,t56,t78,t98,t128]) else (if i < 115 then [t31,t45,t56,t80,t98,t128] else [t31,t45,t56,t80,t98,t147])) else (if i < 118 then (if i < 117 then [t31,t45,t56,t80,t113,t128] else [t31,t45,t56,t82,t110,t128]) else (if i < 119 then [t31,t45,t56,t86,t128,t161] else [t31,t45,t56,t91,t98,t128]))) else (if i < 124 then (if i < 122 then (if i < 121 then [t31,t45,t56,t98,t100,t128] else [t31,t45,t56,t98,t101,t128]) else (if i < 123 then [t31,t45,t56,t98,t104,t128] else [t31,t45,t56,t98,t105,t128])) else (if i < 126 then (if i < 125 then [t31,t45,t56,t98,t105,t133] else [t31,t45,t56,t98,t105,t134]) else (if i < 127 then [t31,t45,t56,t98,t105,t138] else [t31,t45,t56,t98,t105,t147]))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then [t31,t45,t56,t98,t106,t128] else [t31,t45,t56,t98,t107,t128]) else (if i < 131 then [t31,t45,t56,t98,t122,t128] else [t31,t45,t56,t98,t128,t142])) else (if i < 134 then (if i < 133 then [t31,t45,t56,t98,t128,t143] else [t31,t45,t56,t98,t128,t144]) else (if i < 135 then [t31,t45,t56,t98,t128,t157] else [t31,t45,t56,t98,t128,t160]))) else (if i < 140 then (if i < 138 then (if i < 137 then [t31,t45,t56,t98,t133,t161] else [t31,t45,t56,t98,t142,t150]) else (if i < 139 then [t31,t45,t56,t103,t105,t128] else [t31,t45,t56,t105,t110,t128])) else (if i < 142 then (if i < 141 then [t31,t45,t56,t105,t120,t128] else [t31,t45,t56,t110,t128,t145]) else (if i < 143 then [t31,t45,t57,t98,t105,t128] else [t31,t45,t59,t74,t98,t128])))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then [t31,t45,t59,t98,t105,t128] else [t31,t45,t68,t98,t114,t128]) else (if i < 147 then [t31,t45,t68,t98,t128,t156] else [t31,t45,t74,t98,t114,t128])) else (if i < 150 then (if i < 149 then [t31,t45,t98,t105,t114,t128] else [t31,t45,t98,t105,t128,t136]) else (if i < 151 then [t31,t45,t98,t128,t136,t142] else [t31,t46,t56,t98,t105,t128]))) else (if i < 156 then (if i < 154 then (if i < 153 then [t31,t46,t56,t98,t128,t161] else [t31,t47,t56,t74,t98,t128]) else (if i < 155 then [t31,t47,t56,t98,t105,t128] else [t31,t49,t56,t98,t105,t137])) else (if i < 158 then (if i < 157 then [t31,t52,t56,t68,t98,t128] else [t31,t52,t56,t98,t105,t128]) else (if i < 159 then [t31,t56,t77,t105,t128,t137] else [t31,t56,t82,t98,t110,t128]))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then [t31,t56,t82,t98,t128,t158] else [t31,t56,t82,t110,t128]) else (if i < 163 then [t31,t56,t82,t113,t128,t161] else [t31,t56,t98,t105,t111,t128])) else (if i < 166 then (if i < 165 then [t31,t56,t98,t105,t116,t128] else [t31,t56,t98,t105,t128,t137]) else (if i < 167 then [t31,t56,t98,t111,t128,t142] else [t31,t98,t105,t114,t128,t137]))) else (if i < 172 then (if i < 170 then (if i < 169 then [t1,t31,t45,t49,t56,t61,t98] else [t1,t31,t45,t56,t61,t98,t128]) else (if i < 171 then [t1,t31,t45,t56,t98,t105,t128] else [t2,t31,t45,t56,t61,t98,t128])) else (if i < 174 then (if i < 173 then [t3,t31,t45,t56,t61,t98,t128] else [t4,t31,t45,t56,t61,t98,t128]) else (if i < 175 then [t5,t31,t45,t56,t61,t98,t128] else [t6,t31,t45,t49,t56,t61,t98])))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then [t6,t31,t45,t56,t61,t77,t128] else [t6,t31,t45,t56,t61,t98,t128]) else (if i < 179 then [t6,t31,t45,t56,t61,t128,t156] else [t6,t31,t45,t56,t98,t105,t128])) else (if i < 182 then (if i < 181 then [t6,t31,t45,t61,t98,t114,t128] else [t6,t31,t45,t61,t98,t128,t156]) else (if i < 183 then [t6,t45,t56,t61,t98,t128,t151] else [t7,t31,t45,t56,t61,t98,t128]))) else (if i < 188 then (if i < 186 then (if i < 185 then [t8,t31,t45,t49,t56,t61,t98] else [t8,t31,t45,t56,t61,t98,t128]) else (if i < 187 then [t8,t31,t45,t56,t98,t105,t128] else [t8,t31,t55,t56,t61,t98,t128])) else (if i < 190 then (if i < 189 then [t8,t31,t56,t61,t98,t128,t137] else [t9,t31,t45,t56,t61,t98,t128]) else (if i < 191 then [t10,t18,t31,t45,t56,t98,t128] else [t10,t31,t45,t49,t56,t61,t98])))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then [t10,t31,t45,t56,t61,t77,t128] else [t10,t31,t45,t56,t61,t98,t128]) else (if i < 195 then [t10,t31,t45,t56,t61,t98,t133] else [t10,t31,t45,t56,t61,t128,t161])) else (if i < 198 then (if i < 197 then [t10,t31,t45,t56,t98,t105,t128] else [t10,t31,t45,t56,t98,t128,t161]) else (if i < 199 then [t10,t31,t45,t57,t61,t98,t128] else [t10,t31,t45,t61,t98,t114,t128]))) else (if i < 204 then (if i < 202 then (if i < 201 then [t10,t31,t46,t56,t61,t98,t128] else [t10,t31,t56,t61,t98,t128,t137]) else (if i < 203 then [t11,t31,t45,t56,t61,t98,t128] else [t12,t31,t45,t56,t61,t98,t128])) else (if i < 206 then (if i < 205 then [t13,t31,t45,t56,t61,t98,t128] else [t13,t31,t45,t56,t98,t105,t128]) else (if i < 207 then [t14,t31,t45,t56,t61,t98,t128] else [t14,t31,t45,t61,t98,t114,t128])))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then [t15,t31,t45,t56,t61,t98,t128] else [t16,t31,t45,t56,t61,t98,t128]) else (if i < 211 then [t17,t31,t45,t56,t61,t98,t128] else [t18,t31,t45,t49,t56,t61,t98])) else (if i < 214 then (if i < 213 then [t18,t31,t45,t56,t61,t77,t128] else [t18,t31,t45,t56,t61,t98,t128]) else (if i < 215 then [t18,t31,t45,t56,t61,t98,t134] else [t18,t31,t45,t56,t61,t110,t128]))) else (if i < 220 then (if i < 218 then (if i < 217 then [t18,t31,t45,t56,t82,t98,t128] else [t18,t31,t45,t56,t98,t105,t128]) else (if i < 219 then [t18,t31,t45,t56,t98,t128,t145] else [t18,t31,t45,t61,t69,t98,t128])) else (if i < 222 then (if i < 221 then [t18,t31,t45,t61,t98,t114,t128] else [t18,t31,t56,t82,t98,t128]) else (if i < 223 then [t19,t31,t45,t56,t61,t98,t128] else [t20,t31,t45,t56,t61,t98,t128]))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then [t20,t31,t45,t56,t98,t113,t128] else [t20,t31,t45,t56,t98,t128]) else (if i < 227 then [t21,t31,t45,t56,t61,t98,t128] else [t22,t31,t45,t56,t61,t77,t128])) else (if i < 230 then (if i < 229 then [t22,t31,t45,t56,t61,t98,t128] else [t23,t31,t45,t56,t61,t98,t128]) else (if i < 231 then [t24,t31,t45,t56,t61,t77,t128] else [t24,t31,t45,t56,t61,t98,t128]))) else (if i < 236 then (if i < 234 then (if i < 233 then [t31,t31,t45,t49,t56,t61,t98] else [t31,t31,t45,t56,t61,t77,t128]) else (if i < 235 then [t31,t31,t45,t56,t61,t98,t128] else [t31,t31,t45,t56,t98,t105,t128])) else (if i < 238 then (if i < 237 then [t31,t31,t45,t61,t98,t114,t128] else [t31,t32,t45,t56,t61,t98,t128]) else (if i < 239 then [t31,t33,t45,t56,t61,t98,t128] else [t31,t34,t45,t56,t61,t98,t128])))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then [t31,t35,t45,t56,t61,t98,t128] else [t31,t36,t45,t56,t61,t98,t128]) else (if i < 243 then [t31,t38,t45,t56,t61,t98,t128] else [t31,t39,t45,t56,t61,t98,t128])) else (if i < 246 then (if i < 245 then [t31,t40,t45,t49,t56,t61,t98] else [t31,t40,t45,t56,t61,t98,t128]) else (if i < 247 then [t31,t45,t46,t56,t61,t98,t128] else [t31,t45,t49,t49,t56,t61,t98]))) else (if i < 252 then (if i < 250 then (if i < 249 then [t31,t45,t49,t53,t56,t61,t98] else [t31,t45,t49,t54,t56,t61,t98]) else (if i < 251 then [t31,t45,t49,t55,t56,t61,t98] else [t31,t45,t49,t56,t60,t61,t98])) else (if i < 254 then (if i < 253 then [t31,t45,t49,t56,t61,t77] else [t31,t45,t49,t56,t61,t77,t98]) else (if i < 255 then [t31,t45,t49,t56,t61,t82,t98] else [t31,t45,t49,t56,t61,t84,t98])))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then [t31,t45,t49,t56,t61,t98] else [t31,t45,t49,t56,t61,t98,t98]) else (if i < 259 then [t31,t45,t49,t56,t61,t98,t105] else [t31,t45,t49,t56,t61,t98,t113])) else (if i < 262 then (if i < 261 then [t31,t45,t49,t56,t61,t98,t114] else [t31,t45,t49,t56,t61,t98,t121]) else (if i < 263 then [t31,t45,t49,t56,t61,t98,t124] else [t31,t45,t49,t56,t61,t98,t128]))) else (if i < 268 then (if i < 266 then (if i < 265 then [t31,t45,t49,t56,t61,t98,t139] else [t31,t45,t49,t56,t61,t98,t145]) else (if i < 267 then [t31,t45,t49,t56,t61,t98,t150] else [t31,t45,t49,t56,t61,t98,t163])) else (if i < 270 then (if i < 269 then [t31,t45,t49,t56,t98,t105] else [t31,t45,t49,t56,t98,t105,t128]) else (if i < 271 then [t31,t45,t49,t61,t98,t114] else [t31,t45,t49,t61,t98,t114,t128])))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then [t31,t45,t53,t56,t61,t98,t128] else [t31,t45,t54,t56,t61,t98,t128]) else (if i < 275 then [t31,t45,t55,t56,t61,t98,t128] else [t31,t45,t55,t56,t98,t105,t128])) else (if i < 278 then (if i < 277 then [t31,t45,t56,t60,t61,t98,t128] else [t31,t45,t56,t60,t98,t105,t128]) else (if i < 279 then [t31,t45,t56,t61,t79,t98,t128] else [t31,t45,t56,t61,t83,t98,t128]))) else (if i < 284 then (if i < 282 then (if i < 281 then [t31,t45,t56,t61,t84,t98,t128] else [t31,t45,t56,t61,t84,t98,t150]) else (if i < 283 then [t31,t45,t56,t61,t85,t98,t128] else [t31,t45,t56,t61,t86,t98,t128])) else (if i < 286 then (if i < 285 then [t31,t45,t56,t61,t87,t98,t128] else [t31,t45,t56,t61,t88,t98,t128]) else (if i < 287 then [t31,t45,t56,t61,t89,t98,t128] else [t31,t45,t56,t61,t90,t98,t128]))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then [t31,t45,t56,t61,t92,t98,t128] else [t31,t45,t56,t61,t98,t98,t128]) else (if i < 291 then [t31,t45,t56,t61,t98,t99,t128] else [t31,t45,t56,t61,t98,t102,t128])) else (if i < 294 then (if i < 293 then [t31,t45,t56,t61,t98,t103,t128] else [t31,t45,t56,t61,t98,t105,t128]) else (if i < 295 then [t31,t45,t56,t61,t98,t108,t128] else [t31,t45,t56,t61,t98,t110,t128]))) else (if i < 300 then (if i < 298 then (if i < 297 then [t31,t45,t56,t61,t98,t113,t128] else [t31,t45,t56,t61,t98,t115,t128]) else (if i < 299 then [t31,t45,t56,t61,t98,t117,t128] else [t31,t45,t56,t61,t98,t118,t128])) else (if i < 302 then (if i < 301 then [t31,t45,t56,t61,t98,t119,t128] else [t31,t45,t56,t61,t98,t120,t128]) else (if i < 303 then [t31,t45,t56,t61,t98,t121,t128] else [t31,t45,t56,t61,t98,t124,t128])))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then [t31,t45,t56,t61,t98,t125,t128] else [t31,t45,t56,t61,t98,t126,t128]) else (if i < 307 then [t31,t45,t56,t61,t98,t127,t128] else [t31,t45,t56,t61,t98,t128])) else (if i < 310 then (if i < 309 then [t31,t45,t56,t61,t98,t128,t141] else [t31,t45,t56,t61,t98,t128,t150]) else (if i < 311 then [t31,t45,t56,t61,t98,t128,t154] else [t31,t45,t56,t61,t98,t128,t155]))) else (if i < 316 then (if i < 314 then (if i < 313 then [t31,t45,t56,t61,t98,t128,t159] else [t31,t45,t56,t61,t98,t128,t163]) else (if i < 315 then [t31,t45,t56,t61,t98,t133] else [t31,t45,t56,t61,t98,t134])) else (if i < 318 then (if i < 317 then [t31,t45,t56,t61,t98,t138] else [t31,t45,t56,t61,t98,t139,t140]) else (if i < 319 then [t31,t45,t56,t61,t98,t145,t150] else [t31,t45,t56,t61,t98,t145,t152])))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then [t31,t45,t56,t68,t98,t128] else [t31,t45,t56,t70,t98,t128]) else (if i < 323 then [t31,t45,t56,t73,t75,t98,t128] else [t31,t45,t56,t73,t98,t105,t128])) else (if i < 326 then (if i < 325 then [t31,t45,t56,t73,t98,t128,t145] else [t31,t45,t56,t80,t98,t128]) else (if i < 327 then [t31,t45,t56,t82,t98,t105,t128] else [t31,t45,t56,t82,t98,t128,t161]))) else (if i < 332 then (if i < 330 then (if i < 329 then [t31,t45,t56,t84,t98,t105,t128] else [t31,t45,t56,t84,t98,t128,t142]) else (if i < 331 then [t31,t45,t56,t90,t98,t105,t128] else [t31,t45,t56,t94,t98,t105,t128])) else (if i < 334 then (if i < 333 then [t31,t45,t56,t98,t98,t105,t128] else [t31,t45,t56,t98,t105,t105,t128]) else (if i < 335 then [t31,t45,t56,t98,t105,t108,t128] else [t31,t45,t56,t98,t105,t113,t128])))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then [t31,t45,t56,t98,t105,t114,t128] else [t31,t45,t56,t98,t105,t117,t128]) else (if i < 339 then [t31,t45,t56,t98,t105,t121,t128] else [t31,t45,t56,t98,t105,t123,t128])) else (if i < 342 then (if i < 341 then [t31,t45,t56,t98,t105,t128] else [t31,t45,t56,t98,t105,t128,t128]) else (if i < 343 then [t31,t45,t56,t98,t105,t128,t137] else [t31,t45,t56,t98,t105,t128,t139]))) else (if i < 348 then (if i < 346 then (if i < 345 then [t31,t45,t56,t98,t105,t128,t145] else [t31,t45,t56,t98,t105,t128,t148]) else (if i < 347 then [t31,t45,t56,t98,t105,t128,t150] else [t31,t45,t56,t98,t105,t128,t152])) else (if i < 350 then (if i < 349 then [t31,t45,t56,t98,t105,t128,t161] else [t31,t45,t56,t98,t105,t128,t163]) else (if i < 351 then [t31,t45,t56,t98,t128,t142] else [t31,t45,t56,t98,t128,t145,t161]))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then [t31,t45,t98,t105,t114,t128] else [t31,t56,t98,t105,t128,t137]) else (if i < 355 then [t6,t31,t45,t56,t61,t98,t128] else [t8,t31,t45,t56,t61,t98,t128])) else (if i < 358 then (if i < 357 then [t10,t31,t45,t56,t61,t98,t128] else [t18,t31,t45,t56,t61,t98,t128]) else (if i < 359 then [t31,t31,t45,t56,t61,t98,t128] else [t31,t45,t49,t56,t61,t98]))) else (if i < 364 then (if i < 362 then (if i < 361 then [t31,t45,t49,t56,t61,t98,t128] else [t31,t45,t55,t56,t61,t98,t128]) else (if i < 363 then [t31,t45,t56,t60,t61,t98,t128] else [t31,t45,t56,t61,t84,t98,t128])) else (if i < 366 then (if i < 365 then [t31,t45,t56,t61,t98,t98,t128] else [t31,t45,t56,t61,t98,t105,t128]) else (if i < 367 then [t31,t45,t56,t61,t98,t113,t128] else [t31,t45,t56,t61,t98,t121,t128])))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then [t31,t45,t56,t61,t98,t128] else [t31,t45,t56,t61,t98,t128,t150]) else (if i < 371 then [t31,t45,t56,t98,t105,t128] else [t31,t45,t56,t61,t98,t128])) else []) else [])))) else []))

def sixE (i : Nat) : Nat :=
  let w : Nat := (if i < 128 then (if i < 64 then (if i < 32 then 0x2c0972c5715057b2c0b125d71471762d8b12210c5ed762c4972c11c5057d2c4b62217b5f5762c0b12210c5ed762e4b62217b431762ccb12bd7d43d762d8b12bd7d43d762e4af2e177371592d8b12217f5dd762d8b12210c5dd762c4b72c16b5057f2f8bc2217a5e5732c4b72bd745f57f2c4882e17b5fd7d2c4b72bd795657f2c4b725d7a5c57f2e4af2e17b5fd592e4b72bd795f57f2f8b72c16b5f174220972bd6f5e5612e4af2e17b371592c4b625d1c5c5762e4b62bd0f5f5762c4b62217b5fd762c4882bd795f57f2c4972e17b3717d2c4b82c16b5057f2c4b72bd795f57f2e08815d7d5d9772c4b62217b43176 else 0x2c4b72bd7e4a57f2e0b715d7d5d9772e0882c57d5d9772c4b62217e431762e0882e57d5d9772e0b12f9735e57a2f8b72c56b5f1742c4b72bd7943d7f2e0882e57d4a5772e0882c571505772e4b12217a5e57c2c4b82bd794a57f2e0972bd6f5f97a2e0b12f97c5f97a2c4b82bd795f57f2c4b82217b5fd762c4882e17b3717d2c4b025d1c5c5762c4882bd745f57f2e4882bd795f57f2dcbe2c17c5ad742c4882bd795657f2c48825d7a5c57f2f0be221795e9732d8af2e57d4a57b2d8972c5715057b2d89715d7d5d97b2cc972e57d4a57b2e4af2e17b5d9592d8b12217f5ed762c4b62bd0f5f5762c4b82217b43176) else (if i < 96 then 0x2c4b02217b431762e0882c5715d9772c4b62217b551762c4b825d7a5c57f2c4b82bd7e5f57f2e4b82bd795f57f2e4b82f17a5f17e2c4b82bd795657f220b12bd6f5e5612e4b32bd0f5f5762c4b72bd7e5f57f2c4b625d7b5c5762c4b82cd7e5657f2c4b72cd745657f2dcbe2c17c5e9742e4b72cd7e5657f2e0b02cd7c5f96b2dcb12cd595f97f2c4b72c17a5c57f2c4b62bd7b5f5762f0be2e17e5e9732e0b02cd6f5f97a2e0b02cd7c5f97a2c4b62bd795f5762c4882bd7e5657f2c4b72cd7e5f57f2e0972bd6f5f96b2c4b72cd7e4a57f2c4b72cd7e5657f220972bd6f5f9612e08815d7d5d97b2e0972bd6f5e57a else 0x2c4882bd794a57f2e4b62217b5fd762e4b62bd7b5f576220b82c5685c5772e4b62217a431762c4b622179431762c4972c17a5057d2c4b72bd795f5762e4b62bd795f5762e4af2c16b505592e4af2c11c5ad592d89715d7d5fd7b2d8af15d7d5fd7b2cc9715d7d5d97b2c4b82217b5f5762c4b02217b5f5762c4b025d7b5c5762c4b6221775fd762c4b62dd7b5f5762c4b62dd7b5fd762e0972bd6f5e5612c4b82cd7e4a57f2ccb12210c5ed762dcb815d765f57725c882bd795bd61220b815d765f5772c0b125d7d471762c4b622177431762e4b32217b431762c4b625d7b5f5762e4b625d1c5c5762c4b62211c43176)) else (if i < 192 then (if i < 160 then 0x2e0882e57d5d97e2ccaf15d7d5d97e2e0b32c17c5e97e2d8b12bd7d5f9762e0af25d6f5e97e220af2f17c5e97b2e0b92f17c5e97e2f0b82f97e5f17a2c4b82c16b5c57f220b815d765f57a2e0882c57d5d97a2dcbe2c57c5ad74220b82e57c5f5772dcbe2c57c5e9742e08815d7d5fd772d8b12217d5ed76220972bd6f5d161220b82c5765f5772e0af15d7d5fd7b2e09715d7d5fd7b2e0bc2f9735e57a220b82e5765f5772c4b92217e5e97c2f0be2e1745e9732c09715d7d5d97b2ccaf15d7d5d97b2c4b62bd7e5f5762c4b72cd7e5ed7f2c4b72cd7e43d7f2c4b9221795e97c2c4b92e17e5e97c2e0bc2f97c5f97a else 0x2c4b82f97e5f17a2c0b32e17e5e97c) else 0))
  (w >>> (60*(i % 32))) &&& 0xfffffffffffffff

def segE (i : Nat) : Nat :=
  (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x101 else 0x101) else (if i < 3 then 0x101 else 0x101)) else (if i < 6 then (if i < 5 then 0x10101010131010101010101010102000304030805 else 0x101000000650065006500650133014303040000040805) else (if i < 7 then 0x101010101010131000000000101010101010101010101010101010101010702000100040002010f09 else 0x650065006500650101006500650065006500650000006501330000020a000000040d08))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x101010101010131000000000101010101010101010101010101010101010702000100040002010f09 else 0x650065006500650101006500650065006500650000006501330000020a000000040d08) else (if i < 11 then 0x13300000065010100650065006500650065006500650065006500000302000001050d08 else 0x100065006500650065000000650133006501030065010100650065006500650e00010003010700051009)) else (if i < 14 then (if i < 13 then 0x6300650063006700630063006300050001010805 else 0x6300650063006700630063006300050001010805) else (if i < 15 then 0x13501330135013701350135013500050001010805 else 0xb1006500b1006700b100b100b100050001010805)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x87000101 else 0x87000101) else (if i < 19 then 0x65000000930087008700870087008704000000000805 else 0x65000000930087008700870087008704000000000805)) else (if i < 22 then (if i < 21 then 0x87000101 else 0x930093000000930093006500930093009300930093000601080002000c07) else (if i < 23 then 0x1390139013901390139000000000604 else 0x117001500150000001500150015000000150204000200000906))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x1330000013b013b013b013b013b013b04000000000805 else 0x65000000930109010901090109010904000000000805) else (if i < 27 then 0x13d013d013d013d013d000000000604 else 0x13f013f013f013f013f013f013f01030003000805)) else (if i < 30 then (if i < 29 then 0x87000101 else 0x103000001410087008700870087008704000000000805) else (if i < 31 then 0x101000000650065006500b3003400650103006500650065006500650065006500400065006500650065006500650065050a080f080200000000000602180d else 0x1050000006700600065006300630063006900630063009000630063006300630063006300630400000401080300000108130b))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x650065010100650065001000650065010300650065006500b30065006500400065006500650065006500650065160a050e000204000400030302180d else 0x67000000000060006500630015006300630063006300630063006300630063006300630201000300060900000301120b) else (if i < 35 then 0x67000000000090006500b1001500b100b100b100b100b100b100b100b100b100b100b10201000300060900000301120b else 0xa0000000870000000303)) else (if i < 38 then (if i < 37 then 0x87000101 else 0x9300000087006500c00087009f000000870087008700870087008700870087008700870001000200000700000303120b) else (if i < 39 then 0x870087009f00870093008700650087008700d00087008700870087008701200122008700870087008709020d0e03000d060005000202170d else 0x8700d000870087008700870087009f00c000c0008700870087010901320093008700970087006500870087008700870130010700870087008702121314170f0e0c1809020b00000300081f11))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x8700e00000000303 else 0x930093000000930093009300000065009300930093009300f000930093009300930093009300930093000000050012030200010300150c) else (if i < 43 then 0x10b010d010b010b0140010b010b010b0067010b0100010f010b0142010b010b010b010b010b0a02000b08010b04020004140b else 0x870087009300870087006501110130012000870087009f00870087017000870087008700870087008700040d0e110304030202000301170d)) else (if i < 46 then (if i < 45 then 0x160000000870000000303 else 0x63000101) else (if i < 47 then 0x63000101 else 0x63000000000063006300630063006700630063006300650063006300630109000200080000050f09)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x7000630063006300630067008000630065006300150063006300630063006300820063006300630063010b000e120201070001000307170d else 0x1050000006700700065006300630063006900630063009000630063006300630063006300630400000401080300000108130b) else (if i < 51 then 0x6300800067011300630065000000630063006300630063015c0063006300630063006300630200080000030002000103130b else 0x63000101)) else (if i < 54 then (if i < 53 then 0x67000000000090006500630015006300630063006300630063006300630063006300630201000300060900000301120b else 0x930000008d006500c0008d009f0000008d008d008d008d008d008d008d008d008d008d0001000200000700000303120b) else (if i < 55 then 0x63000101 else 0x650020000000670067000000670067006700670067006700670067006700670067006700670700060b00080303000600130b))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x7b000101 else 0x7b0115007b007b007b007b007b06000000000805) else (if i < 59 then 0x115007b007b0000007b007b007b007b007b0004000002000906 else 0x30003000300030003000305000000000705)) else (if i < 62 then (if i < 61 then 0x30003000300030003000305000000000705 else 0x300030003000300030003000306000300000805) else (if i < 63 then 0x30003000300030003000305000000000705 else 0x37000101)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x3000101 else 0x300b8000000000404) else (if i < 67 then 0x83000101 else 0x101)) else (if i < 70 then (if i < 69 then 0x3000101 else 0x3000101) else (if i < 71 then 0x500a000000000000100000404 else 0x3000101))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x3000101 else 0x3000101) else (if i < 75 then 0x101 else 0xd000101)) else (if i < 78 then (if i < 77 then 0x101 else 0x3000101) else (if i < 79 then 0x77000101 else 0x3000101)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x99000101 else 0x101) else (if i < 83 then 0xcd000101 else 0x101)) else (if i < 86 then (if i < 85 then 0x3000101 else 0x4b000101) else (if i < 87 then 0x30003000300030003000305000000000705 else 0x150015000000000015001500150015001500cf011700150015001500150a0800000e060107000f09))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705) else (if i < 91 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705)) else (if i < 94 then (if i < 93 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705) else (if i < 95 then 0x15000500000005000500050005000500630005010000020906 else 0x830083008300830083008305000000000705))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x500000063011b0015011900050005000500050005000500090003000701000d08 else 0x770003007b000300c800030003000301150000011d00030003000300000406000301000e08) else (if i < 99 then 0x7500150015000000150015001500150015001500a300100015011f00af0a06000005080002060f09 else 0xd000000005000500050005007f006300510007008100050005000500000109000809000e08)) else (if i < 102 then (if i < 101 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705) else (if i < 103 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x30003000300030003000305000000000705 else 0x30003000300030003000305000000000705) else (if i < 107 then 0x1150003011d000300030003000300030004020001000906 else 0x770003007b0003013c00030003000301150000011d00030003000300000406000301000e08)) else (if i < 110 then (if i < 109 then 0x770003007b0003012c00030003000301150000011d00030003000300000406000301000e08 else 0x30003000300030003000305000000000705) else (if i < 111 then 0x300cd0003007700030003000300030005000000000906 else 0x1150003011d0003007700030003000300030079060006000202020b07)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x30003000300030003000305000000000705 else 0x300030003012100030003000306000002000805) else (if i < 115 then 0xaf000d0007000d000d000d000d000d0304000005000906 else 0xaf000d0007000d000d000d000d000d0304000005000906)) else (if i < 118 then (if i < 117 then 0x27000101 else 0x7f00000005008f007f00150087008b00150087008900c0007f0087007f008d007f007f007f007f007f007f000d00020013070400070000160c) else (if i < 119 then 0x240015011700150015000000cf0015001501100000001500150015001500150015001500150904060601000201000200130b else 0xd000101))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x3000101 else 0x3000101) else (if i < 123 then 0x3000101 else 0x3000101)) else (if i < 126 then (if i < 125 then 0x5000101 else 0x83000101) else (if i < 127 then 0x16c00000003000000000404 else 0x37000101))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x3000101 else 0x3000101) else (if i < 131 then 0xcd000101 else 0x30003000300030003000305000000000705)) else (if i < 134 then (if i < 133 then 0x30003000300030003000305000000000705 else 0x123000000030003000300030003000301040000000805) else (if i < 135 then 0x63000101 else 0xaf01140015000000000000001500750015001500150015001500150000020105030100020e09))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x1500150015000b0125001500750015003400150015001500150015001500000208030b0504021009 else 0x101) else (if i < 139 then 0x3000101 else 0x5000101)) else (if i < 142 then (if i < 141 then 0x3000101 else 0x150100000000950091009300510097005100510051005100510051005100f00015005102000f03070b00050003120a) else (if i < 143 then 0x77000101 else 0x7b000300cd000300030003000300030404000004000906)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x3000101 else 0x3000101) else (if i < 147 then 0x14c0127011500000115011501150115011501150115011501150001020106040100010e09 else 0x3000101)) else (if i < 150 then (if i < 149 then 0x101 else 0xcd000101) else (if i < 151 then 0x30003000300030003000305000000000705 else 0x5000101))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x150015001500550129001500750015004000150015001500150015001500000208030b0504021009 else 0x12b0003012d000300030003000300030404000004000906) else (if i < 155 then 0x3000101 else 0x101)) else (if i < 158 then (if i < 157 then 0x770003007b0003017800030003000301150000011d00030003000300000406000301000e08 else 0x3000101) else (if i < 159 then 0x101 else 0xc0006500a7009f0107009700400093009f009f009f009f008700a301070000009f009f009f009f009f009f0107009f07040d0c06030b060502050002180d))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0x87000101 else 0x9f008700c000c00087008d009b00a0009f0087008700c0008700b00087009f009b0087009d00a100e000870087009f005000a700a1009700c0016200c000870087009700a500f0008700a300870160009f00870023232022081e1d1c0127171514260002130d160c090b2b17) else (if i < 163 then 0x8f00c0005500000015012f012f00550055005500550055005500010900000003030d08 else 0xcd000101)) else (if i < 166 then (if i < 165 then 0xd1000101 else 0x101) else (if i < 167 then 0x30003000300030003000305000000000705 else 0x101))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x26000000260000302600260026002600000000200000906 else 0x300030003000000030003000303b000050003000303b000030003000300030003000303b000030003000300010003000303b003b00003000303b0000300030003001a000000081700001606101a10110006022112) else (if i < 171 then 0x5d0000005d0000305d005d005d005d00001000200000906 else 0x300030003000000030003000303b0000500030003047a00030003000300030003000303b000030003000300010003000303b00464000300030478000300030003001a000000081700001606101a10110006022112)) else (if i < 174 then (if i < 173 then 0x300030003000000030003000303f800050003000303b000030003000300030003000303c000030003000300010003000303b003b00003000304b8000300030003001a000000081700001606101a10110006022112 else 0x300030003000000030003000303b000050003000303b000030003000300030003000303d000030003000300010003000303b00484000300030498000300030003001a000000081700001606101a10110006022112) else (if i < 175 then 0x300030003000000030003000303b000050003000303b000030003000300030003000303e000030003000300010003000304a004a40003000303b0000300030003001a000000081700001606101a10110006022112 else 0x260026000030000010403)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x268000300000000000303 else 0x3b0000300030003000300030003000300030003000303b00003000500030003000300010003000300030003000300030f110511001000030a0301010700190e) else (if i < 179 then 0x101 else 0x305d0000005d00000000403)) else (if i < 182 then (if i < 181 then 0x305da0000000303 else 0x101) else (if i < 183 then 0x5d805d800030000010403 else 0x30003000300030003000300030003000103b000030003000500030003000300030003000300030003000300140d03081003020301040201170d))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x260026000030000010403 else 0x300030003000300030003000300030003000303b0000300030005000300030003000103b0000300030003000300031015030f000302010b0e01000809190e) else (if i < 187 then 0x305d0000005d00000000403 else 0x101)) else (if i < 190 then (if i < 189 then 0x3000005d40000000303 else 0x300030003000300030003000100030003000300110003000300030003000303b00003000300030003000302140d000a12020e0102080000170d) else (if i < 191 then 0x630063006700650015001000630063006300630069003000400063006b00630063006300630063006300630063006300630063006301100063006300001108111000170f1100060f0d0002130004072012 else 0x36000000300000502d40302026002600000000200000906)))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0x502be02bc000003180278026800030200000705 else 0x3b00015000500050003040000130003000504fc000505440005000300630005006f00050005000503b000030005006d0003000500050005000504fe00030005000500050000170d06141c00131700151112160107130d00082313) else (if i < 195 then 0x40000150005000500050400001b00050005050c0005055400050015006300050005000500050005040000050005000500050005000500050005050e00050005000500050000170d06141c00131700151112160107130d00082313 else 0x56400000071000000000404)) else (if i < 198 then (if i < 197 then 0x5070007020000079005e005d000030200000705 else 0x51001500150015000b0015001500150015007500150015001500000015001506a00015001500730015001507a000150015001500150015000c04000000110100000418000e00061d10) else (if i < 199 then 0x4fe0015000500050077050e001b0005000507b80005071a0005007700630005007700050005000504fe0077000500050077000500050005000504fe00770005000500050000170d06141c00131700151112160107130d00082313 else 0x5da000005da0005072a07ca063a06ca0001000200000906))) else (if i < 204 then (if i < 202 then (if i < 201 then 0x54400150005000500050554001b0005000507180005054400050015006300050005000500050005054400050005000500050005000500050005071a00050005000500050000170d06141c00131700151112160107130d00082313 else 0x5d4000505d40000075a0758061405d40000000200000906) else (if i < 203 then 0x4fe006f006f00030003006f006f006f006f0003006f03b0006f000500050003007700050003006f006f006f0003006f0f110511001000030a0301010700190e else 0x30003000300030003000300030001000303b000030005000300030003000300030003000300030003000301140c0009070b0b0701030000170d)) else (if i < 206 then (if i < 205 then 0x3b000030003000300030003000300030003000300030003000300030003000f00790003000300010003000300030003000311120213000401020a020000090c1a0e else 0x5d0000005d000000003000000000504) else (if i < 207 then 0x300030003000300030003000300030003000303b000030003001100030003000300010003000300030003000300030f140812001202020a0001010009190e else 0x305da000005da0000000403)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x300000003000300030003000300030005040800030000000100030003000303b0000300030003000300030003000300030003000300030000000c00110b0800001b1600020b001c10 else 0x30003000300030003000300030000000500030003000300010003000304f603b00003000300030000007b0003000300030003000300030000000500170b0800000a1600020b001c10) else (if i < 211 then 0x3000300030003000300030003000100030524000300050003000300030003007d0003000700030003000301140c0009070b0b0701030000170d else 0x37000500320000502600322026002800003000200000906)) else (if i < 214 then (if i < 213 then 0x2aa006002680005026802a8026802980001000200000906 else 0x300110043000103b00410007f00030015002500010005000500050070000304ca00050003000500050005000500050063000500050081000704380005000503b000050005000504c8000500031a151222052300201212201f0f0a17170d0b0016012815) else (if i < 215 then 0x8300050005000104100410007f00830015002500050005000500050080008304ea000500830005000500050005000500630005000500810007045000050005041000050005000504e8000500831a151222052300201212201f0f0a17170d0b0016012815 else 0x500050005000504380450007f00050015002500050005000500050090000504da000500510005000500050005000500630005000500810007043800050005043800050005000504d8000500051a151222052300201212201f0f0a17170d0b0016012815))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x15008f0085007f0087008b0070007f0087007f007f007f000500150087007f007f007f007f0089007f007f0087008d00700570007f007f007f007f007f007f007f007f0517001717171614150718001310020a0700052313 else 0x5073e073c000005d005f006d000030200000705) else (if i < 219 then 0x2500c00025002500250015001500b000250043074c0091001100950051002500930025002500250025002500970025002506f0074e00250025002500250025131c080b001500100011020d0d060c121100102213 else 0x50099000500050099002504ca04ea0099000500050005007f009904ca000500250005000507e8000500d0000704da0005006300150081009900050005000504ca000500050005000500050099262300200100111f1c181615040c151617040004072815)) else (if i < 222 then (if i < 221 then 0x60a07fa000000e005da064a0005000005da06ea000200000100000a07 else 0x87007000900810083000d200500070009f0080006000700087009700700087007000a500a0009f0070008700b0009f009b002000d0008700e2009700a700a100870087008700e0009f008d008700870087009d00700087009f009b008700870087008700870087007000a10087009f008700a30097008700870087082000872d003d3c293a39383239243922381d351b34162d142b0f1c0d150a23040b020100314122) else (if i < 223 then 0x1100a90005000000030005000500010043000700030011001100110011000300110003005103b004c80011001100110001001100030011001100000807001800050000121000020e001d10 else 0x500050005000500750005006300ab051e0025000300ab0005000500050170000100810015005d0013000500050005000503b00003000500050005001504380063000500ad006304200005051c00050005006301100063000500050544000300051713232e2d000b2528241e1c180b0025140425291b080a010015321a))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x15000b000b000b000b006b000b00630063000b00630110006300af000b0110000b000b00150110000b000b000b000b000b000b000b000b0063000b000b00000063000b151f0016001e140d0e0401070c00000f000a2212 else 0x142019000f0011001000015011000b700630150006300630015001501200110006301600004018001300140006b00b9068000630063006300b500b50015006301100152006300630015006300630063006300b9000b006300630110006300150063006300630063006300b1006b006b00b30063006301100063300000002b3b3600143a26390e3837360733322d0029211c1f1b150f1a2408013e20) else (if i < 227 then 0x10001000300050023041000510001000100030001000100010003000d0003000100010023000303b0000100010001000100010001160f020b0d00000a070909000d03031c0f else 0x268026800000001000000000504)) else (if i < 230 then (if i < 229 then 0x10001000b00010001000300370005000100030001000d00050003000300050001000103b00001000100010001000300011217050602040002071003010a001a0e else 0x300030003000500030003000300030043000300030003000100010003000300030003000300030000060c0000010300110000150c) else (if i < 231 then 0x30268000002680000000403 else 0x30000000300bb0003000300030003000300030003000100030003000300030003007b001103b000030005000300030003000300030003000c1605001a0707131603000000021c0f))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x3026002600200000403 else 0x30000026802680000000403) else (if i < 235 then 0x3000300030003000300030003000300010003000300030011000300030003000303b003b000030003000300030112050209150d000301030b00180d else 0x3000005d005d00000000403)) else (if i < 238 then (if i < 237 then 0x3000005da05da0000000403 else 0x30003000300030003000100030003000300030003000100030003001100110003000300030003000303b0000300030003000300100c1313021607091001000201001b0f) else (if i < 239 then 0x4fc00bd00bd006d006d005d000300030005006d03b000bf006d006f006d006d00bf00030003006d006d001100bd0003006d006d00bd0003006d006d00bd007b006d006d006d0000211915181800170011181400080f07160600022413 else 0x30003000303b000030003000300430003001100010003000300030003000300030003000300030003000300030003000300030000000b190b09130b00140b0407000a021d11)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0x10001003d0003006d00010001000100c103b000030003000100010035000300010011000100010001000300010001000100010013040d00110d1800040402000000001c10 else 0x30003000300050003000300030003000300030003000300030001000300030003000300030003000d000c000a050300000000150c) else (if i < 243 then 0x100a9001100a9003d0003001100110011001100030011001104c8001100a9001100110003001100a900c500a900110011003d0003001100c3001100050043000103b000a9000300111d1a011f19001512220b1e181e0a01070d080803002715 else 0x150000000300150005001500150075000d006f0544006d001505380003001500af0015000500150051001500150003002704400015000300150540001503b00003001700200015053a001500150015001522251d061b00211b211900001002000d0a05191409012916)) else (if i < 246 then (if i < 245 then 0x260000000000000000300000260000000000000000807 else 0x3000303b000010003000300030003000300030003000300030027000300050003000300030005000300030003000300030c040c0b10131300000303000201011b0f) else (if i < 247 then 0x50005000500030005000500690005000b0544000500630003001503b00005000100c70110000500050005000500150005001500230005000b00150005001500400005000100bf0003000500050005230223160d0f221b0600001b03011f230022111f17142916 else 0x30260026000000000000403))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x260026001a8003b0000000000010000000605 else 0x30260026000000000000403) else (if i < 251 then 0x10000026002600000000403 else 0x2600260000300000068000000000504)) else (if i < 254 then (if i < 253 then 0x26002ca02c402500250025002c0026802c802500250025000090006000300000d08 else 0x3000101) else (if i < 255 then 0x2600050000000050000026001000000000605 else 0x34202f003400260000302f4000000010101000705)))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 0x30250033002e402600260026002e003b00332026002600260000900060b0300000e08 else 0x30260026000000000000403) else (if i < 259 then 0x3000101 else 0xb00f0026000000260000200000504)) else (if i < 262 then (if i < 261 then 0x3000101 else 0x30260026000000000000403) else (if i < 263 then 0x2600000000300000260000000000504 else 0x300030000004300030003000300030005003b00030003000300c900030003000300030003000300030005010d0002000300000500150c))) else (if i < 268 then (if i < 266 then (if i < 265 then 0x302600108000000000504 else 0x1302600001000303) else (if i < 267 then 0x260000000030000000303 else 0x26002600000026002600260000302600000000000000906)) else (if i < 270 then (if i < 269 then 0x260035007d002e002e002e002c005d0035202e002e002e000090006000300000d08 else 0x3000101) else (if i < 271 then 0x2600350035403300330033002ca05da080803300330033000090006000300000d08 else 0x3000101)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 0x3b00010003003b0003003b003b0003003b00030005003b0001000101b803b0003b003b003b0003003b003b003b0003003b0713000104000903070d080600031a0e else 0x3000000030003000300030005000303b00003000300030003004300030003007b000300c900030003000300030003003b051400030811000b010201000b0a190e) else (if i < 275 then 0x1000103b0006d0001000500010003006d00010001003500cb00010001000100010001006d00a90001000303b00003000100010001000100000d150006050c00150d00001200021d10 else 0x1000005d005d00000000403)) else (if i < 278 then (if i < 277 then 0x3b00003000303b00003000000030003000300030003000300030003000300030003000300780003000300430003000100030003000300030000000300030f16181105000f130803020001020000001f11 else 0x5d0000300ec05d00000000000000000000605) else (if i < 279 then 0x43006f00430003000500430043006f004300430043000100430043004303b0006f000303b0004303b0000000430043000300430043004310001b0d0d040d09020004020001001c0f else 0x30000000000030001000300030003000301e0000500030003000301e8000300030003000301ec000301e200030003000300030003000300030003060f060d000912000503110a02061000031e11))) else (if i < 284 then (if i < 282 then (if i < 281 then 0x3000306580003000300cd065a000100cd000303b0000300030003000300030003065403b000030650001300cd00030003000300030003000300030003000305180014171402120b0c0400091110070200032213 else 0x6b0000006b40000000303) else (if i < 283 then 0x300030003000300030003000300cd0003000303b000b500030003065a00030001000300030000000300030003000300030018051605140002070000050002190e else 0x15069400150015000500150015001500130003040000030580001306500003066c0003001500cf001500150015001500150015000303b0066e006f0003006d001500000015001500150015001a1d1e00160a1000000c0f00011b0200040a002614)) else (if i < 286 then (if i < 285 then 0x3000300030007000300030003000b0003000d03b00063000300050003000300030000000300030003000300030001000300080d150a140002090000090002190e else 0x3000000030003000300050003000100030003000300030003000300a00003000000030003000300050003000316060300050301010002000001170d) else (if i < 287 then 0x300030003000300050003000300030003006f00030003000000030003000000030003000300010003000308060600050301010300000000160d else 0x300030001000300030003000303b0000300030013000100030003000300d100010674000300030003000300030003004300030003000a00100406030e080406010200041c0f))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0x658000303b000cd0003000300030003000300cd000300cd0003000100030003000300030003000300030003000300030003000300030011000300370011000300030000000300cd1b120c121d18171400161500060f11000000032413 else 0x300030003000300030003000300030005000303b003b0000b0003000d00000003000300030003000700030003000317101109010907060005030004180d) else (if i < 291 then 0x3000b0003000500030003000300030003000300030007000303b0000d0003000d0000000300110003000300030003000300030003160e060d080004010707050a0002001b0f else 0x300030001000b0031004b000500d3003500030007004b000303b000010003003d0003004b0000004b0000004b004b004b004b004b0d0c040d02000308070706070001001b0f)) else (if i < 294 then (if i < 293 then 0x3000000cd0003000303b0000300030003007b0003000300030003000300030007000300d5000300030003000300030003000d0408000d0005000b0005000b00030003000300030003000300001922000c13050008110300110f16000314012614 else 0x30003000100030003000100030000000300030003000300030003000300050003000300030003000300040c09000d0b0300000000150c) else (if i < 295 then 0x3000300030003000300050003000303b000010005000500000003000300030003000300030003000300030005000309010f00080600040503000700180d else 0x300810015001500510015001503b0000b007500050015008500050003043800030005001500150110003d000500070015002700030031000b0005001500370014001500150015005100d7000301140007002700100057081000150000007500152c032722001e241a271823150012220b000f0300000e00200700311a))) else (if i < 300 then (if i < 298 then (if i < 297 then 0xb000301100001000b000b0005000b000b03b0000b000b0003000b00150003000b000303b00003003500af0000000b000b00d30001000b0003000b000b1a1b0000190d0b1114120c0103000305001f11 else 0x300030003000300030003000103b0000500030003000000030003000300030003000300030003000300030003000309070f010704000b0400000003180d) else (if i < 299 then 0x300010003000300030005000300010005000100db0001000103b0000100d900010000000500010005000100010001000100010d0d060a0a080404010002070402001b0f else 0x30003000300030001000300030003000503b0000300030000000300030003000300cd00030003000300030003000304010f0b0907000e0700000005180d)) else (if i < 302 then (if i < 301 then 0x30003000300030003000100030000000300030003000300050003000300030003000300030003000300040c09000d0b0300000000150c else 0x3000300030003000b0003000300030003000503b0000300030003000b04180003000d0005000300030003000700030003000300070003000d00030000000300030003000300031b1a00140f1918090a001016090e03030101012413) else (if i < 303 then 0x11000300cd000d0003000300030003005d00050003000300030003000300030003000303b003b000030003000300cb007b00030003000000350003000319120010110a0102171304000804010e001f11 else 0x4300030003000300dd003b000300050003000303b000030000000300000003000300030003000300030003000300030003000b0e07090000040a0900030007190e)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 0x301d8000300030003000300050003000301dc0003000300030003000300030003038003b0000300030003000300030003000100000000000300031a120000180c0a1109070c000704010d001e11 else 0x30003003b00030003000100030000000300030003000300050003000300010003000300030003000300040c09000d0b0300000000150c) else (if i < 307 then 0x1003500010005003500bf03b000df0035003500e1000300350003000300030035000303b003b00035003500d3003500000035003501c80003003500351d18000012100e1716080f0107040109001f11 else 0xf000d000300050260026800030001000b03b000050001000303b000030003000500030003000303b005d0000300110007000103b00003000505da0013000305d4000300030003000300030001000303b00003000300030001000300030003000300010003000305d803b032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d)) else (if i < 310 then (if i < 309 then 0x3006f0003000300010003000303b0000303b0006f0001000300000003000300030003000303b000030003000300030003000300031717060414090012060004090901031b0f else 0x3000300030003000303b00003000303b0000100030003000300030003000500030003002100e300030003000300000000000300030003000300030c0f0a0f0900130700000a0604020000021e11) else (if i < 311 then 0x3000303a00003000300030003020803b0000300030003000500030003000300cd020c00030003000000000001000308280003000300030003000300031d140e120b00001a0400090702060011051f11 else 0x3b0000300cd00030003000300030003000300030003000503b001f803b0000300030003000300030003000300030003000300050001000300030016030d0009000b00120b00000500081e10))) else (if i < 316 then (if i < 314 then (if i < 313 then 0x50003000300d30003000300cd0398000300030003000303b0000303b00003000300e50043000d000300cd03b000030003000300030077007b00b8000300030003000315132012030d1900110b09070506030f0201002313 else 0x300030003000300030003000303b00003000300030003000303b003b0000303b00003000303b0000300030003000503b000030000000100030003000300030003001f001a151d130c1002000910070e0008042112) else (if i < 315 then 0x2140278040005e0040006ca040000050614000500300019000504000015001500050005001500050005000500050015001d0015000500050400001b0005001d00050057002100050015001f000506c800050005001b000b00050005000500050005002306a00005040000050005001920001a002b000f371a2a083628350734013312321431262f241b00102203391e else 0x5000d008300050240029800830005000b04100005000100830410008300830005008300830083041005f0008300050007000104100083000506ea0013008305f4008300830083008300830001008304100083008300830001008300830083008300010083008306e8041032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d)) else (if i < 318 then (if i < 317 then 0x13a02300003043006fa0288043006000003057a057806da000306f808380430043000030003000500030007000300010001000300030138001300030003001100050604000300010003000300030001000300010003000f00010430000300030003000d0005000306d8000300030003000b00050003043000032500370023000000143b3a390e37343607351c2d0031302c1f1b150f1a082b013e20 else 0x3000300030003000000030003000300cd0003000300cd0003000300030848000300030430000300030003000a00040001000b00020100160c) else (if i < 319 then 0x21001b0400002100210005002100510025001500e700eb002100e900000021002100210021002100210021002104060400060206000500010200170d else 0xef000000150005001300010015001500370015041000f100ed00f3001500ed001500ed001500c0009100910015001500150015001500150d0b030008140006050005010003021c0f)))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 0x2a004c0032c04c005c0000504c007300003000300070003000504c007f40001000300010003000300030001000300030740000f00030003000504c00003000300030003000100030003000d000300010003000300010013000b00030003000300030003000507420011073204c0000321001f001b000e37183607352f3406332b311330002a1629281a0f022701391e else 0xf000d0003002702b0030e00030001005304f000270001000304f000030003001d00030003000304f005b2000300110007000104f000030027070e0013000307c6000300030003000300030001000304f000030003000300010003000300030003000100030003075204f032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d) else (if i < 323 then 0x6d00ad005d0011000f000f000f04c00000000f00f5000f000f000f000f000f00f7006f000f000f000f000400070002040500030400150c else 0x5d0000f00000000000303)) else (if i < 326 then (if i < 325 then 0xf000f000f001304f00000006d00e700ef004300f9004300fb000f000f0043000f000f000f000f000f000f000f03010001060005000404010200170d else 0x2d00540054005900540072e000d056000270540000d031c000d0007079400270027000d000d000d0015000d0015000d000d002707a40027000d000d001500570540000d0015000d0027000d000d000d072c000d006100fd000d0051000d000d002b0045000d000d00150164000d0540000d22001e002d0008381c37002d1a36053529341533112f282a26180d1012013a1e) else (if i < 327 then 0x505d00000000303 else 0x7054000070007007f0174001500000840001500ff0007001500070007000700270007000700070007000700070b020301020004010703000105170d))) else (if i < 332 then (if i < 330 then (if i < 329 then 0x5d007720003062005d007700000000008500003000100000906 else 0x300030003003700030003001b00030003000300030003000307800003088000030650065000030003065000030003000300030782000300030003000300031517190b1004100e13020c000d0c000200002112) else (if i < 331 then 0x5d00003086005d0000200000504 else 0x305d0000005d00000000403)) else (if i < 334 then (if i < 333 then 0x3000005d005d00000000403 else 0x5d0000305d000000100000403) else (if i < 335 then 0x305d005d00000000403 else 0x5d00000000b05a005d0000300000504)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 0x3000101 else 0x10000000005d005d0000000000504) else (if i < 339 then 0x5d005d0000000000003000100000504 else 0x305d005d00000000403)) else (if i < 342 then (if i < 341 then 0x302e0033c087005d005d005d003b00760076205d005d005d0000900060a0300000e08 else 0x5d0000305d000000100000403) else (if i < 343 then 0x3000101 else 0x5d005d00003015c0000000000000000000605))) else (if i < 348 then (if i < 346 then (if i < 345 then 0x5d0000000130000000303 else 0x5d00003000005d00100000403) else (if i < 347 then 0x5d0000305d000000100000403 else 0x5d00001000005d00100000403)) else (if i < 350 then (if i < 349 then 0x705d001840000000403 else 0x5d0000005d005d005d0000305d005d000000001000100000906) else (if i < 351 then 0x30037001100150015022002f000370037001500030003065000030003000300030003065006500003000f034c0003003700030650000300030015077e0650000300030003001b001506b0000300150003000300030003000300370003001b00030854003700030003077c065033312f2c302b31132a28300e2422201b1c29180c230d05091716010200381d else 0x51009301940051001500430051001100150650005100250580005100000015005100510051005100150051001b0051005100510051000009000006050e10000a090a01031b0f))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 0x35005da089007600760076005d0035e089c07600760076000090006000300000d08 else 0x5d005d4089008700870087007d00800089208700870087000090006000300000d08) else (if i < 355 then 0x3009008b000700090008000900003000300030005000300900003000100b00790000100540003009008b000e000900003005000030003048c00030005000900010003000300070003000300900003000d000300030011000300c00003003a000304880001000307b8000300030003000f00a000030005000300b4000300600003000300900005000b00030003000300030003045000030001009000030422089a0003000100d0000500900090000154004c003c004b00240048001f53445245003a5444533552335130481c31172a11150c1a000a2b4106400f072901592e else 0x3013001100110010e011001200003000300030005000307a001100110000108b001000110011008b0014000030042000300030056012e013e0003042c00030005001300010003000300070003000301100003000d0003000300110003014e000300580003047a0001000307ae000300030003000f01100003000500030001000301100003000300030005000b0003000300030003000304200003000108460005004800010001000304720110000354004c003e004b0022553a001d004800475438461354335331522e511a4a153c0f440a42042f2928001c0d082701592e)) else (if i < 358 then (if i < 357 then 0x1e0099e00150015019008b00170000501f000050019002300050005000b0015000500050200019009d40180019007c80190019001600005001d019000050462000501900005001704280005001d01e2019000100005000502100005001b00300015099c01f2001501a008b00015000501c0000500050005000500520005000500050005001f0015000500050920000500050190019004e00005001b0790000500210005000501b0000500050005088c000504600019001b01d00005005001900005565f405e5b0052005a0051004f004d003d00255a3a59365a324d144b2d470f2845161e58254822340b38062e1c01190900436232 else 0x33004a2098a03000350016402d00310016003200040030402d008b002b002d002d002c0042c0015001008b002d0000502f002e00930034002d0031402d00332034204a0000500250005000500270015000500270005098802d00005006807f0085808e80005004200050005000500190025000500050005000500070005000500190027000500050023000b0005000503240005042802d000250005001702d0000500050005001500050025001f000500050005001509480005000502d000050015000500050005000528005900246362613d5f575e3a00000020005c001c005c00005618551353514e375d4d480e4932060b4730462d44423805331b156634) else (if i < 359 then 0x3040000050003000100050003019802d8042000030420042008b004400420042008b00434000100030003000b0007000106a004100003000304200003000f00030003000300030001080a042000130003000300030003043000030092000306c0000300030003011400030420000306a407d804200003000d0420000101100003000300050860001100010003000542002d003f003b0042001d463d3e1a2d1521101b003b0c392b37293502112e002200240e060a4926 else 0x51202b005d001020540064005f0007005600580052205000550058001040524010602c805a005c00580066005e0053005260174058003e8040208b005d204f00644017003ba03b8059004c005b005c20580051001000418041c007205b4050405a4052003ec04000662058032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d))) else (if i < 364 then (if i < 362 then (if i < 361 then 0x3060000050003000300030003002b0029000b0003002906840088000004d00029001106800614000300100003000500030690000300030003060205f003ca000305580003000303c800030003065000030005069205f000030003000f0007002d05f00003000300030654063008700003002909100188000303fc000304f0057000050003000305f00005000306700620002f002f000305f0000300290798008c061005f000290003000300290003018a03f805f00003067200035a4f585957554b445553231f53514c4a514e463d28451e433f3d3c380b3736180331161032300e082c2a280719250100115f31 else 0x42c06a008b006a0042006a008b006a0052e06a006b00228022608ae08a009c606a009a809c806a005200001036c06e4003f0005013006be013e000109a406a00001036406e80762000100010001000d00050001003500050001000106a000010037004109b600010001000100010001000d000100010001000b001100010001003d06a000010029000100010005000109b80001000100310001003b06a0003300010005000100010001000100390007000f00010001003331004c002e004a00205a59581c5748002b56555418474654265343522551424b06403e3c00383b2d1229371a0c13360d5d30) else (if i < 363 then 0x3003b004500030003003b000b0011003b000309fa000300050003030a030809f800030003035800030003000306c008b0000305680005000300030003000306d0000700030043000500030758003b00030003000300030003000300050003000309e806c00422000106c004b806c0000306c000f009ea00030003000300030420000306c006c00900000300030003003b053006c008c006c0000f08b0001306d402340230000306c00003000306e006e4003b06c0574c0055555555515151514d45002f4b4a46441b11442541403c213b3a3606353431002e1f1c18150a120e2b2904285c2f else 0x8b007820b6a00340003078c0b64003807800b680570003707000003004700030003003700030015000300370037003700030003000300030003000f000300030788079800150700001100030a14000300150a18000300030578000300030003000300030700000300030047071006f0003007000b60070000030a08000300030037000307180003001500150003000300030700004707000a00003700030790000307000a0a0003070008b0003a00150a1a0700070000030a1000030a0400033a5b505c055b4d5a58004c5837574956490044553454455531534333412d2c28201440132a0e190d1e241801123c00220c066132)) else (if i < 366 then (if i < 365 then 0x90001508620015019405900003009200030800000305f807900003004d004b0003086007900790079000030a40001508b00790079008b007900ada000307900003019008040015004f0a440ad8000300150003000307900003000308d00003079000030700003f0051001500030003000300030003000300030003001500030003004b0015001500490003000300031a4444003c424200064018420f3b3700133d323c37330d31302b082a29280122241c002120174926 else 0x30b500003000b000300030003000100010003001309100b000001000d000302400003083c0001026c00010820000305a000030003000307d000030146000f07d000030005000300050003000500030003000300030001000302420003000300030003083e07700428000509b0000307d0001509e0000307d000030144000307d00001001000030a5000200a8c0011081c000300050310000307d0000307e00b40000300cc0ae4000309b2000307d00003074401c005cc00010a8e5a4f594d584a005856485755534654524d444200352d452e412829403d11023c250c193910360035212f0a321d221714065f31) else (if i < 367 then 0x1d408a2042c080008b008000b7401500051080002a40800072808a0060808f005b0000b07900800001508b00a70000b09f40800000b03700380039008000b44000b08000053000b00150059000b000b000b000b08c8000b0051000b0af8000b000b000b000b08000958015201b40afa005b000b000b000b0015000b0057000b0053000b0800000b000b000b000b000b000b000b00150051000b0015000b0800005900150015000b000b000b000b0051000b0015000b000b005536245a0033580000205756551c54520030520000184c54532b524b512a4e483e064645430025421a123d3c3b0c2e130d5e30 else 0x1700030057000300030003003d003908a4000303a800030900003d00a2003d08a000030003032808b00003003d00030860004f00030003001700030039061800030003003900030003003d0003003d097809cc003d029e00d200030420000308600003000305d00003086003d2073800030b78000300030860000300030aa008fa005d0017000308600860005708600003000308600968000300030aa408600860003d029a0003079000030b08003d0b3a08b00057000309c808603352005b59500059574e58564d2f5649444a2d00492c2a464525272016083e4221021e3f183c051500390f380d37071a0e5f31)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 0x6a60194080a02d00580058807da009c080008b006c806a205f008b0009208600190011405f807d008b00ac0080806a40804009808b0009004280aca086804220ac4070002d801160798019a086c07d808b006c001100790042c019808d0086207d406a0011204200ac808b032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d else 0x28208f8028c0280079808d0000308d000030620000308b008d008b008d0028808d0062808d00b2a0b2400030003006100030003005108f0096409680003000308fa00030003000304900003004f000300030790071008d0071808d00b200003005f004100410003000300030041000300410003000308d00003000308f40960096a004108d00b28005f004100030003000300030003005f0003004d08d00003000300030021002500030003000300030051005100410003425700003f56000026550000223c0000395400001e3755543452514b334a532e062d2b4900482c2012471a190c18130d5d30) else (if i < 371 then 0xaa2027c0af20214064008b00a800a000a900ac00a7006b206500ac002520ab00a3000b207d0067c0ac0066c0af00aa00a6000e80ac002500a400b800b2004320b900a20034c00b00ad001fe0b300a820ac006d001200a50044c01fc0b100ab20ae006b0012204300b820ac032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d else 0x76002400ca00300050005800ba000c00c000e000880072006000e0000200d000200014006800b000e0010000c8007400c4000800e000000048010a00d80042010400900038001600a8002a00dc00b800e00080001000a0004c002800f000d200b4007000120040010800e032302e282f2931112823300a212220191b2f18162c0515090d0e010200371d)) else 0) else 0)))) else 0))

def nsE : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 24
  | 6 => 138
  | 7 => 186
  | 8 => 17
  | 9 => 1
  | _ => 0

def offE : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 6
  | 6 => 30
  | 7 => 168
  | 8 => 354
  | 9 => 371
  | _ => 0

def stateE (s i : Nat) := rowsE (offE s+i)

def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s+i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16+8*(h % a))) &&& 255
  (t >>> (16+8*a+16*((h/a+d) % b))) &&& 65535

def rotateE (g : Nat) (ws : List Nat) : List Nat := match g with

  | 1 => ws.map (blockWord 24 [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14])

  | 2 => ws.map (blockWord 24 [2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13])

  | 3 => ws.map (blockWord 24 [3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12])

  | 4 => ws.map (blockWord 24 [4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 13, 15, 8, 10, 9, 11])

  | 5 => ws.map (blockWord 24 [5, 7, 4, 6, 1, 3, 0, 2, 13, 15, 12, 14, 9, 11, 8, 10])

  | 6 => ws.map (blockWord 24 [6, 4, 7, 5, 2, 0, 3, 1, 14, 12, 15, 13, 10, 8, 11, 9])

  | 7 => ws.map (blockWord 24 [7, 5, 6, 4, 3, 1, 2, 0, 15, 13, 14, 12, 11, 9, 10, 8])

  | _ => ws

theorem rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 192) (goal 192) s ws) : NatRun (mask 192) (goal 192) s (rotateE g ws) := by
  unfold rotateE

  split <;> first | exact h | apply block_run h _ _ (by decide +kernel) (by decide +kernel)

def Z (s : Nat) := barrier 192 stateE nsE actionE sixE rotateE s




theorem h0y0 : span (Z 0) 1 0 = true := by decide +kernel

theorem z0 : span (Z 0) 1 0 = true := h0y0

theorem h1y0 : span (Z 1) 1 0 = true := by decide +kernel

theorem z1 : span (Z 1) 1 0 = true := h1y0

theorem h2y0 : span (Z 2) 1 0 = true := by decide +kernel

theorem z2 : span (Z 2) 1 0 = true := h2y0

theorem h3y0 : span (Z 3) 1 0 = true := by decide +kernel

theorem z3 : span (Z 3) 1 0 = true := h3y0

theorem h4y0 : span (Z 4) 2 0 = true := by decide +kernel

theorem z4 : span (Z 4) 2 0 = true := h4y0

theorem h5y0 : span (Z 5) 6 0 = true := by decide +kernel

theorem h5y1 : span (Z 5) 6 6 = true := by decide +kernel

theorem h5y2 : span (Z 5) 6 12 = true := by decide +kernel

theorem h5y3 : span (Z 5) 6 18 = true := by decide +kernel

theorem z5 : span (Z 5) 24 0 = true := (@span_join (Z 5) 12 0 12 (@span_join (Z 5) 6 0 6 h5y0 h5y1) (@span_join (Z 5) 6 12 6 h5y2 h5y3))

theorem h6y0 : span (Z 6) 6 0 = true := by decide +kernel

theorem h6y1 : span (Z 6) 6 6 = true := by decide +kernel

theorem h6y2 : span (Z 6) 6 12 = true := by decide +kernel

theorem h6y3 : span (Z 6) 6 18 = true := by decide +kernel

theorem h6y4 : span (Z 6) 6 24 = true := by decide +kernel

theorem h6y5 : span (Z 6) 6 30 = true := by decide +kernel

theorem h6y6 : span (Z 6) 6 36 = true := by decide +kernel

theorem h6y7 : span (Z 6) 6 42 = true := by decide +kernel

theorem h6y8 : span (Z 6) 6 48 = true := by decide +kernel

theorem h6y9 : span (Z 6) 6 54 = true := by decide +kernel

theorem h6y10 : span (Z 6) 6 60 = true := by decide +kernel

theorem h6y11 : span (Z 6) 6 66 = true := by decide +kernel

theorem h6y12 : span (Z 6) 6 72 = true := by decide +kernel

theorem h6y13 : span (Z 6) 6 78 = true := by decide +kernel

theorem h6y14 : span (Z 6) 6 84 = true := by decide +kernel

theorem h6y15 : span (Z 6) 6 90 = true := by decide +kernel

theorem h6y16 : span (Z 6) 6 96 = true := by decide +kernel

theorem h6y17 : span (Z 6) 6 102 = true := by decide +kernel

theorem h6y18 : span (Z 6) 6 108 = true := by decide +kernel

theorem h6y19 : span (Z 6) 6 114 = true := by decide +kernel

theorem h6y20 : span (Z 6) 6 120 = true := by decide +kernel

theorem h6y21 : span (Z 6) 6 126 = true := by decide +kernel

theorem h6y22 : span (Z 6) 6 132 = true := by decide +kernel

theorem z6 : span (Z 6) 138 0 = true := (@span_join (Z 6) 96 0 42 (@span_join (Z 6) 48 0 48 (@span_join (Z 6) 24 0 24 (@span_join (Z 6) 12 0 12 (@span_join (Z 6) 6 0 6 h6y0 h6y1) (@span_join (Z 6) 6 12 6 h6y2 h6y3)) (@span_join (Z 6) 12 24 12 (@span_join (Z 6) 6 24 6 h6y4 h6y5) (@span_join (Z 6) 6 36 6 h6y6 h6y7))) (@span_join (Z 6) 24 48 24 (@span_join (Z 6) 12 48 12 (@span_join (Z 6) 6 48 6 h6y8 h6y9) (@span_join (Z 6) 6 60 6 h6y10 h6y11)) (@span_join (Z 6) 12 72 12 (@span_join (Z 6) 6 72 6 h6y12 h6y13) (@span_join (Z 6) 6 84 6 h6y14 h6y15)))) (@span_join (Z 6) 24 96 18 (@span_join (Z 6) 12 96 12 (@span_join (Z 6) 6 96 6 h6y16 h6y17) (@span_join (Z 6) 6 108 6 h6y18 h6y19)) (@span_join (Z 6) 12 120 6 (@span_join (Z 6) 6 120 6 h6y20 h6y21) h6y22)))

theorem h7y0 : span (Z 7) 6 0 = true := by decide +kernel

theorem h7y1 : span (Z 7) 6 6 = true := by decide +kernel

theorem h7y2 : span (Z 7) 6 12 = true := by decide +kernel

theorem h7y3 : span (Z 7) 6 18 = true := by decide +kernel

theorem h7y4 : span (Z 7) 6 24 = true := by decide +kernel

theorem h7y5 : span (Z 7) 6 30 = true := by decide +kernel

theorem h7y6 : span (Z 7) 6 36 = true := by decide +kernel

theorem h7y7 : span (Z 7) 6 42 = true := by decide +kernel

theorem h7y8 : span (Z 7) 6 48 = true := by decide +kernel

theorem h7y9 : span (Z 7) 6 54 = true := by decide +kernel

theorem h7y10 : span (Z 7) 6 60 = true := by decide +kernel

theorem h7y11 : span (Z 7) 6 66 = true := by decide +kernel

theorem h7y12 : span (Z 7) 6 72 = true := by decide +kernel

theorem h7y13 : span (Z 7) 6 78 = true := by decide +kernel

theorem h7y14 : span (Z 7) 6 84 = true := by decide +kernel

theorem h7y15 : span (Z 7) 6 90 = true := by decide +kernel

theorem h7y16 : span (Z 7) 6 96 = true := by decide +kernel

theorem h7y17 : span (Z 7) 6 102 = true := by decide +kernel

theorem h7y18 : span (Z 7) 6 108 = true := by decide +kernel

theorem h7y19 : span (Z 7) 6 114 = true := by decide +kernel

theorem h7y20 : span (Z 7) 6 120 = true := by decide +kernel

theorem h7y21 : span (Z 7) 6 126 = true := by decide +kernel

theorem h7y22 : span (Z 7) 6 132 = true := by decide +kernel

theorem h7y23 : span (Z 7) 6 138 = true := by decide +kernel

theorem h7y24 : span (Z 7) 6 144 = true := by decide +kernel

theorem h7y25 : span (Z 7) 6 150 = true := by decide +kernel

theorem h7y26 : span (Z 7) 6 156 = true := by decide +kernel

theorem h7y27 : span (Z 7) 6 162 = true := by decide +kernel

theorem h7y28 : span (Z 7) 6 168 = true := by decide +kernel

theorem h7y29 : span (Z 7) 6 174 = true := by decide +kernel

theorem h7y30 : span (Z 7) 6 180 = true := by decide +kernel

theorem z7 : span (Z 7) 186 0 = true := (@span_join (Z 7) 96 0 90 (@span_join (Z 7) 48 0 48 (@span_join (Z 7) 24 0 24 (@span_join (Z 7) 12 0 12 (@span_join (Z 7) 6 0 6 h7y0 h7y1) (@span_join (Z 7) 6 12 6 h7y2 h7y3)) (@span_join (Z 7) 12 24 12 (@span_join (Z 7) 6 24 6 h7y4 h7y5) (@span_join (Z 7) 6 36 6 h7y6 h7y7))) (@span_join (Z 7) 24 48 24 (@span_join (Z 7) 12 48 12 (@span_join (Z 7) 6 48 6 h7y8 h7y9) (@span_join (Z 7) 6 60 6 h7y10 h7y11)) (@span_join (Z 7) 12 72 12 (@span_join (Z 7) 6 72 6 h7y12 h7y13) (@span_join (Z 7) 6 84 6 h7y14 h7y15)))) (@span_join (Z 7) 48 96 42 (@span_join (Z 7) 24 96 24 (@span_join (Z 7) 12 96 12 (@span_join (Z 7) 6 96 6 h7y16 h7y17) (@span_join (Z 7) 6 108 6 h7y18 h7y19)) (@span_join (Z 7) 12 120 12 (@span_join (Z 7) 6 120 6 h7y20 h7y21) (@span_join (Z 7) 6 132 6 h7y22 h7y23))) (@span_join (Z 7) 24 144 18 (@span_join (Z 7) 12 144 12 (@span_join (Z 7) 6 144 6 h7y24 h7y25) (@span_join (Z 7) 6 156 6 h7y26 h7y27)) (@span_join (Z 7) 12 168 6 (@span_join (Z 7) 6 168 6 h7y28 h7y29) h7y30))))

theorem h8y0 : span (Z 8) 6 0 = true := by decide +kernel

theorem h8y1 : span (Z 8) 6 6 = true := by decide +kernel

theorem h8y2 : span (Z 8) 5 12 = true := by decide +kernel

theorem z8 : span (Z 8) 17 0 = true := (@span_join (Z 8) 12 0 5 (@span_join (Z 8) 6 0 6 h8y0 h8y1) h8y2)

theorem h9y0 : span (Z 9) 1 0 = true := by decide +kernel

theorem z9 : span (Z 9) 1 0 = true := h9y0

theorem checkedE (s : Nat) (hs : s ≤ 9) : ∀ i < nsE s, Z s i = true := by
  interval_cases s

  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRun (mask 192) (goal 192) s xs1004) : False := by
  have h10 : NatRun (mask 192) (goal 192) 9 xs1004 := extend_run h hs
  have p : xs1004.Perm (stateE 9 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 9 (by decide) 0 (by decide) (Run.perm p h10)



end PEqualNP.Outside.L_meta_1004
open PEqualNP.Outside.L_meta_1004 in
theorem PEqualNP.Outside.L_meta_1004 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 3 && x 5)) 9 := by
  exact main1004 noRunFull
