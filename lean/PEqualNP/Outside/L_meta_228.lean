import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_228

theorem entry_rank {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℚ) (x y : α)
    (h : A x y = 1) : 1 ≤ A.rank := by
  let r := fun _ : Unit => x
  let c := fun _ : Unit => y
  have he : A.submatrix r c = (1 : Matrix Unit Unit ℚ) := by
    ext i j
    cases i
    cases j
    simpa [r,c,Matrix.submatrix] using h
  have bound := A.rank_submatrix_le r c
  simpa [he] using bound

theorem coordinate {n : ℕ} (f : (Fin n → Bool) → Bool) (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (typing : IsTyping n f τ) (i : Fin n) (x : Fin n → Bool)
    (depends : f x ≠ f (Function.update x i (!x i))) :
    1 ≤ ∑ b : Bool, (typedMatrix n f τ i b).rank := by
  classical
  let y := Function.update x i (!x i)
  have agree (j : Fin n) (ne : j ≠ i) : x j = y j := by simp [y,Function.update_of_ne ne]
  have one (a b : Fin n → Bool) (ha : f a = true) (hb : f b = false)
      (same : ∀ j, j ≠ i → a j = b j) : 1 ≤ ∑ v : Bool, (typedMatrix n f τ i v).rank := by
    obtain ⟨j,hj,ne⟩ := typing a b ha hb
    have ji : j = i := by
      by_contra bad
      exact ne (same j bad)
    subst j
    have entry : typedMatrix n f τ i (a i) a b = 1 := by simp [typedMatrix,ha,hb,hj]
    exact (entry_rank _ a b entry).trans (Finset.single_le_sum
      (f := fun v : Bool => (typedMatrix n f τ i v).rank) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (a i)))
  change f x ≠ f y at depends
  cases hx : f x <;> cases hy : f y
  · exact False.elim (depends (hx.trans hy.symm))
  · exact one y x hy hx (fun j hj => (agree j hj).symm)
  · exact one x y hx hy agree
  · exact False.elim (depends (hx.trans hy.symm))

end PEqualNP.Outside.L_meta_228

open PEqualNP.Outside.L_meta_228 in
theorem PEqualNP.Outside.L_meta_228 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s →
    (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  classical
  rintro n f s ⟨τ,typing,bound⟩
  let active := Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool,
    f x ≠ f (Function.update x i (!x i)))
  change active.card ≤ s
  calc
    active.card = ∑ _i ∈ active, 1 := by simp
    _ ≤ ∑ i ∈ active, ∑ b : Bool, (typedMatrix n f τ i b).rank := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨x,hx⟩ := (Finset.mem_filter.mp hi).2
      exact coordinate f τ typing i x hx
    _ ≤ ∑ i : Fin n, ∑ b : Bool, (typedMatrix n f τ i b).rank :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active) (fun _ _ _ => Nat.zero_le _)
    _ ≤ s := bound
