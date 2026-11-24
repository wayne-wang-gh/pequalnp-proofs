import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_230

open PEqualNP.MetaComplexity

abbrev Input := Fin 3 → Bool

def majority (x : Input) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

def choosePos (x y : Input) : ℕ :=
  if x 0 then
    if y 0 then (if x 1 then 1 else 2) else 0
  else if y 1 then 2 else 1

def indicator (b : Bool) : ℚ := if b then 1 else 0

lemma forall_input {P : Input → Prop} : (∀ x, P x) ↔ ∀ a b c, P ![a, b, c] :=
  (FinVec.forall_iff P).symm

lemma rank_le_of_rectangles {k : ℕ} (M : Matrix Input Input ℚ)
    (A : Matrix Input (Fin k) ℚ) (B : Matrix (Fin k) Input ℚ)
    (h : ∀ x y, M x y = ∑ j, A x j * B j y) : M.rank ≤ k := by
  have heq : M = A * B := Matrix.ext h
  rw [heq]
  exact (Matrix.rank_mul_le_left A B).trans (by simpa using A.rank_le_card_width)

private theorem upperBound : HasTypedRank 3 majority 5 := by
  let M := typedMatrix 3 majority choosePos
  have hzero (i : Fin 3) : M i false = 0 := by
    ext x y
    revert x y
    fin_cases i <;> simp only [forall_input] <;> decide
  have hfirst : (M 0 true).rank ≤ 1 := by
    apply rank_le_of_rectangles _
      (fun x _ => indicator (majority x && x 0))
      (fun _ y => indicator (!majority y && !y 0))
    simp only [forall_input, Fin.sum_univ_one]
    decide +kernel
  have hother (b : Bool) : (M (if b then 1 else 2) true).rank ≤ 2 := by
    apply rank_le_of_rectangles _
      (fun x => ![indicator (majority x && x 0 && (x 1 == b)), indicator (majority x && !x 0)])
      ![fun y => indicator (!majority y && y 0), fun y => indicator (!majority y && (y 1 != b))]
    simp only [forall_input, Fin.sum_univ_two]
    cases b <;> decide +kernel
  refine ⟨choosePos, ?_, ?_⟩
  · unfold IsTyping
    simp only [forall_input]
    decide
  · change ∑ i, ∑ b, (M i b).rank ≤ 5
    simp [Fin.sum_univ_succ, hzero]
    exact (by simpa using Nat.add_le_add hfirst (Nat.add_le_add (hother true) (hother false)))

private theorem lowerBound : ¬ HasTypedRank 3 majority 4 := by
  rintro ⟨τ, valid, bound⟩
  let hi (i j : Fin 3) := decide (j ≠ i)
  let lo (i j : Fin 3) := decide (j = i)
  let M (k : Fin 3) := typedMatrix 3 majority τ k true
  have yes : ∀ i, majority (hi i) = true := by decide
  have no : ∀ i, majority (lo i) = false := by decide
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
    exact Finset.single_le_sum (f := fun b => (typedMatrix 3 majority τ i b).rank) (fun _ _ => Nat.zero_le _) (Finset.mem_univ true)
  rw [Fin.sum_univ_three] at posBound
  have h0 := nonzero 0
  have h1 := nonzero 1
  have h2 := nonzero 2
  have h01 := unique 0 1 (by decide)
  have h02 := unique 0 2 (by decide)
  have h12 := unique 1 2 (by decide)
  omega

end PEqualNP.Outside.L_meta_230

theorem PEqualNP.Outside.L_meta_230 :
    PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 5 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  exact ⟨PEqualNP.Outside.L_meta_230.upperBound, PEqualNP.Outside.L_meta_230.lowerBound⟩
