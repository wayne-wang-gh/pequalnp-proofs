import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1088

open PEqualNP.CircuitLowerBounds

theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

-- one step of evaluation and one step of the dependency sets
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

theorem sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
    W1.length = D.length → W2.length = D.length →
    (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = W2.getD w false) →
    ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
      (gs.foldl wstep W1).getD w false = (gs.foldl wstep W2).getD w false := by
  intro gs
  induction gs with
  | nil => intro W1 W2 D _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 D h1 h2 h
    simp only [List.foldl_cons]
    apply ih
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro w hw
      simp only [wstep, dstep] at hw ⊢
      rw [getD_snoc, getD_snoc]
      rw [getD_snoc] at hw
      rw [h1, h2]
      split_ifs with c1 c2
      · rw [if_pos c1] at hw; exact h w hw
      · rw [if_neg c1, if_pos c2] at hw
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h j
        intro i hi
        apply hw
        rw [Finset.mem_biUnion]
        exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
      · rfl

theorem cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
    ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
      T.card + k + gs.length := by
  intro gs
  induction gs with
  | nil => intro D k _ h T; simpa using h T
  | cons g gs ih =>
    intro D k hg h T
    simp only [List.foldl_cons, List.length_cons]
    have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
    · omega
    intro T
    have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
        ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨w, hw, hi⟩ := hi
      simp only [dstep] at hi
      rw [getD_snoc] at hi
      rw [Finset.mem_biUnion]
      split_ifs at hi with c1 c2
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
      · rw [Finset.mem_biUnion] at hi
        obtain ⟨j, hj, hi⟩ := hi
        exact ⟨j, Finset.mem_union_right _ hj, hi⟩
      · simp at hi
    have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
    have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
    have h4 := List.toFinset_card_le g.inputs
    have h5 := hg g List.mem_cons_self
    have h6 := Finset.card_le_card hsub
    by_cases hm : D.length ∈ T
    · have h7 := Finset.card_erase_of_mem hm
      have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
          T.biUnion fun w => D.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        simp only [dstep]
        rw [getD_snoc]
        have : w ≠ D.length := fun e => hm (e ▸ hw)
        split_ifs with c1
        · rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h9]; have := h T; omega

theorem base_card (n : ℕ) (T : Finset ℕ) :
    (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
      T.card + 0 := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [Nat.add_zero]
  calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
      ≤ ∑ w ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro w _
        rw [List.getD_eq_getElem?_getD]
        by_cases hw : w < n
        · simp [hw]
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
    _ = T.card := by simp

end PEqualNP.Outside.L_meta_1088

open PEqualNP.Outside.L_meta_1088 in
theorem PEqualNP.Outside.L_meta_1088 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ i < n, ∃ x : List Bool, x.length = n ∧ C.eval x ≠ C.eval (x.set i (!(x.getD i false)))) → n ≤ C.size + 1 := by
  intro n C hfan hdep
  let D0 : List (Finset ℕ) := (List.range n).map fun i => ({i} : Finset ℕ)
  let S := (C.gates.foldl dstep D0).getD C.output ∅
  have hsub : Finset.range n ⊆ S := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_contra hni
    obtain ⟨x, hx, hne⟩ := hdep i hi
    apply hne
    let y := x.set i (!(x.getD i false))
    have hy : y.length = n := by simp [y, hx]
    have key := sem (fun j => x.getD j false = y.getD j false) C.gates x y D0
      (by simp [D0, hx]) (by simp [D0, hy]) ?_ C.output ?_
    · unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [wires_eq, wires_eq]; exact key
    · intro w hw
      by_cases hwn : w < n
      · apply hw w
        simp [D0, List.getD_eq_getElem?_getD, hwn]
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · intro j hj
      have hji : j ≠ i := fun e => hni (e ▸ hj)
      simp only [y]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hji)]
  have hc := cardb C.gates D0 0 hfan (base_card n) {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  change n ≤ ((C.gates.foldl dstep D0).getD C.output ∅).card at this
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega
