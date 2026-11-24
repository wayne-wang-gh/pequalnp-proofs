import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_247

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def target (x : Fin 4 → Bool) : Bool :=
  (!(x 3)) || (x 2 && (x 0 || x 1))

private def reads (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

private def cost (g : Gate) : ℕ :=
  match g.op with
  | .not => 0
  | _ => 1

private theorem reads_length (g : Gate) (h : g.inputs.length ≤ 2) :
    (reads g).length ≤ cost g + 1 := by
  cases g with
  | mk op inputs =>
    cases op <;> simp_all [reads, cost]

private theorem eval_reads (g : Gate) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((reads g).map f) := by
  cases g with
  | mk op inputs =>
    cases op <;> cases inputs <;> rfl

private theorem getD_snoc_ne {α : Type} (L : List α) (a d : α) (j : ℕ)
    (h : j ≠ L.length) : (L ++ [a]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem getD_snoc_eq {α : Type} (L : List α) (a d : α) :
    (L ++ [a]).getD L.length d = a := by simp

private theorem getD_ofFn {α : Type} (f : Fin 4 → α) (d : α) {i : ℕ} (hi : i < 4) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi]
  rfl

private def gateSupp (L : List (Finset (Fin 4))) (g : Gate) : Finset (Fin 4) :=
  (reads g).toFinset.biUnion fun i => L.getD i ∅

private def suppsFrom (gs : List Gate) (L : List (Finset (Fin 4))) :
    List (Finset (Fin 4)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

private def inputSupps : List (Finset (Fin 4)) :=
  List.ofFn fun i : Fin 4 => {i}

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def Agree (x y : Fin 4 → Bool) (L : List (Finset (Fin 4))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

private theorem agree_inputs (x y : Fin 4 → Bool) :
    Agree x y inputSupps (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < 4
  · rw [getD_ofFn _ _ hjn, getD_ofFn _ _ hjn]
    exact hj _ (by rw [inputSupps, getD_ofFn _ _ hjn]; simp)
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private theorem agree_wiresFrom (x y : Fin 4 → Bool) (gs : List Gate)
    (L : List (Finset (Fin 4))) (w w' : List Bool) (h : Agree x y L w w') :
    Agree x y (suppsFrom gs L) (gs.foldl step w) (gs.foldl step w') := by
  induction gs generalizing L w w' with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g]) (step w g) (step w' g)
    refine ⟨by simp [step, h1], by simp [step, h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst j
      rw [getD_snoc_eq] at hj
      rw [step, step, h1, getD_snoc_eq, h2, getD_snoc_eq]
      rw [eval_reads, eval_reads]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h3 i fun k hk => hj k (Finset.mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, hk⟩)
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      unfold step
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

private def Cnt (t : ℕ) (L : List (Finset (Fin 4))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

private theorem cnt_inputs : Cnt 0 inputSupps := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < 4
  · rw [inputSupps, getD_ofFn _ _ hjn]
    simp
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]
    simp

private theorem cnt_step (t : ℕ) (L : List (Finset (Fin 4))) (g : Gate)
    (hg : g.inputs.length ≤ 2) (h : Cnt t L) :
    Cnt (t + cost g) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst j
        have hi' : i ∈ gateSupp L g := by simpa using hij
        obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi'
        exact ⟨a, Finset.mem_union_right _ ha, hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc : (W.erase L.length ∪ (reads g).toFinset).card ≤ W.card - 1 + (cost g + 1) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left ((List.toFinset_card_le _).trans (reads_length g hg)) _
    have hWpos := Finset.card_pos.mpr ⟨_, hW⟩
    have := h (W.erase L.length ∪ (reads g).toFinset)
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

private theorem cnt_suppsFrom (gs : List Gate) (t : ℕ) (L : List (Finset (Fin 4)))
    (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2) (h : Cnt t L) :
    Cnt (t + (gs.map cost).sum) (suppsFrom gs L) := by
  induction gs generalizing t L with
  | nil => simpa [suppsFrom] using h
  | cons g gs ih =>
    simpa [suppsFrom, Nat.add_assoc] using
      ih (t + cost g) (L ++ [gateSupp L g]) (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
        (cnt_step t L g (hgs g List.mem_cons_self) h)

private theorem support_cost (C : Circuit) (hfan : FanInTwo C)
    (heval : ∀ x, C.eval (List.ofFn x) = target x) :
    4 ≤ (C.gates.map cost).sum + 1 := by
  have hdep : ∀ i : Fin 4, ∃ x : Fin 4 → Bool,
      target (Function.update x i (!x i)) ≠ target x := by decide
  let S := (suppsFrom C.gates inputSupps).getD C.output ∅
  have hall : ∀ i : Fin 4, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    rw [← heval, ← heval]
    exact (agree_wiresFrom _ _ C.gates _ _ _ (agree_inputs _ _)).2.2 C.output (by
      intro k hk
      have hki : k ≠ i := fun e => hi (e ▸ hk)
      exact Function.update_of_ne hki _ _)
  have hcard : S.card = 4 := by
    rw [Finset.eq_univ_of_forall hall]
    simp
  have hc := cnt_suppsFrom C.gates 0 inputSupps (fun g hg => (hfan g hg).2)
    cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  change S.card ≤ (C.gates.map cost).sum + 1 at hc
  rwa [hcard] at hc

private theorem gate_cost_le (g : Gate) : cost g ≤ 1 := by
  cases h : g.op <;> simp [cost, h]

private theorem cost_le (gs : List Gate) :
    (gs.map cost).sum ≤ gs.length := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    have hg := gate_cost_le g
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem cost_lt_of_not (gs : List Gate) (h : ∃ g ∈ gs, g.op = .not) :
    (gs.map cost).sum < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    obtain ⟨a, ha, haop⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha
    · have hg : cost a = 0 := by simp [cost, haop]
      have := cost_le gs
      omega
    · have hg := gate_cost_le g
      have := ih ⟨a, ha, haop⟩
      omega

private def LeL (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

private theorem eval_mono (op : GateOp) (hop : op = .and ∨ op = .or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

private theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (a b : List Bool) (hl : a.length = b.length) (h : LeL a b) :
    LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      by_cases he : i = a.length
      · subst i
        have hi' : g.op.eval (g.inputs.map fun i => a.getD i false) = true := by
          simpa [step] using hi
        rw [hl]
        simpa [step] using eval_mono _ (hgs g List.mem_cons_self) _ _ _ h hi'
      · unfold step at hi ⊢
        rw [getD_snoc_ne _ _ _ _ he] at hi
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact h i hi

private theorem lower (s : ℕ) (h : HasCircuitSize 4 target s) : 4 ≤ s := by
  obtain ⟨C, hfan, hsize, heval⟩ := h
  have hsize' : C.gates.length ≤ s := hsize
  have hs := support_cost C hfan heval
  by_contra hn
  have hm : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa using (hfan g hg).1
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := cost_lt_of_not C.gates ⟨g, hg, h⟩
      omega
  let x : Fin 4 → Bool := ![false, false, false, false]
  let y : Fin 4 → Bool := ![false, false, false, true]
  have hxy : LeL (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases hir : i < 4
    · have hfalse : ∀ j : Fin 4, x j = false := by decide
      rw [getD_ofFn _ _ hir, hfalse] at hi
      cases hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hir)] at hi
      cases hi
  have htrue : C.eval (List.ofFn x) = true := (heval x).trans (by decide)
  have hfalse : C.eval (List.ofFn y) = false := (heval y).trans (by decide)
  have hy : C.eval (List.ofFn y) = true :=
    fold_mono C.gates hm _ _ (by simp) hxy C.output htrue
  rw [hfalse] at hy
  cases hy

private theorem upper (s : ℕ) (hs : 4 ≤ s) : HasCircuitSize 4 target s := by
  let C : Circuit := ⟨[⟨.not, [3]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [4, 6]⟩], 7⟩
  refine ⟨C, ?_, hs, ?_⟩
  · simp [C, FanInTwo]
  · dsimp only [C]
    decide

end PEqualNP.Outside.L_meta_247

theorem PEqualNP.Outside.L_meta_247 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (!(x 3)) || (x 2 && (x 0 || x 1))) s ↔ 4 ≤ s := by
  intro s
  exact ⟨PEqualNP.Outside.L_meta_247.lower s, PEqualNP.Outside.L_meta_247.upper s⟩
