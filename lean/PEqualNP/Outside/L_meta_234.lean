import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_234_aux

open PEqualNP.MetaComplexity

-- The rank-minor argument is adapted from bluish's majority proof in PR 1791.
abbrev Input := Fin 3 → Bool

def target (x : Input) : Bool :=
  decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)

theorem lowerBound : ¬ HasTypedRank 3 target 4 := by
  rintro ⟨τ, valid, bound⟩
  let hi (i j : Fin 3) := decide (j = i)
  let lo (i j : Fin 3) := decide (j ≠ i)
  let M (k : Fin 3) := typedMatrix 3 target τ k false
  have yes : ∀ i, target (hi i) = true := by decide
  have no : ∀ i, target (lo i) = false := by decide
  have only : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ p, hi i p ≠ lo j p → p = k := by decide
  have forced (i j k : Fin 3) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
      M k (hi i) (lo j) = 1 := by
    obtain ⟨p, hp, hd⟩ := valid _ _ (yes i) (no j)
    obtain rfl := only i j k ij ik jk p hd
    exact ite_eq_left ⟨yes i, no j, hp, by simp [hi, ik.symm]⟩
  have distinct : ∀ k : Fin 3, ∃ i j, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide
  have nonzero (k : Fin 3) : 1 ≤ (M k).rank := by
    obtain ⟨i, j, ij, ik, jk⟩ := distinct k
    have sub : (M k).submatrix (fun _ : Unit => hi i) (fun _ : Unit => lo j) = 1 := by
      ext a b
      simpa [Matrix.submatrix_apply, Matrix.one_apply] using forced i j k ij ik jk
    simpa [sub] using (M k).rank_submatrix_le (fun _ : Unit => hi i) (fun _ : Unit => lo j)
  have diagonal (i j k : Fin 3) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
      (small : (M k).rank ≤ 1) : τ (hi i) (lo i) = k := by
    by_contra absent
    have zero : M k (hi i) (lo i) = 0 := ite_eq_right (fun h => absent h.2.2.1)
    let B := (M k).submatrix ![hi i, hi j] ![lo i, lo j]
    have det : B.det ≠ 0 := by
      rw [Matrix.det_fin_two]
      change M k (hi i) (lo i) * M k (hi j) (lo j) - M k (hi i) (lo j) * M k (hi j) (lo i) ≠ 0
      simp [zero, forced i j k ij ik jk, forced j i k ij.symm jk ik]
    have rankTwo : 2 ≤ (M k).rank := by
      have h : B.rank ≤ (M k).rank := (M k).rank_submatrix_le _ _
      simpa [Matrix.rank_of_det_ne_zero det] using h
    omega
  have unique (k l : Fin 3) (kl : k ≠ l) : ¬ ((M k).rank ≤ 1 ∧ (M l).rank ≤ 1) := by
    rintro ⟨hk, hl⟩
    have third : ∀ a b : Fin 3, ∃ i, i ≠ a ∧ i ≠ b := by decide
    obtain ⟨i, ik, il⟩ := third k l
    exact kl (Fin.ext ((diagonal i l k il ik kl.symm hk).symm.trans (diagonal i k l ik il kl hl)))
  have posBound : ∑ k : Fin 3, (M k).rank ≤ 4 := by
    apply le_trans _ bound
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (f := fun b => (typedMatrix 3 target τ i b).rank) (fun _ _ => Nat.zero_le _) (Finset.mem_univ false)
  rw [Fin.sum_univ_three] at posBound
  have h0 := nonzero 0
  have h1 := nonzero 1
  have h2 := nonzero 2
  have h01 := unique 0 1 (by decide)
  have h02 := unique 0 2 (by decide)
  have h12 := unique 1 2 (by decide)
  omega


end PEqualNP.Outside.L_meta_234_aux

theorem PEqualNP.Outside.L_meta_234 : ¬ PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)) 4 := by
  exact PEqualNP.Outside.L_meta_234_aux.lowerBound
