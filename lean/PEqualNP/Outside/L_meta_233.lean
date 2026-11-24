import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_233_aux

open PEqualNP.MetaComplexity

def pos (x y : Fin 3 → Bool) : Fin 3 :=
  if x 0 = false ∧ y 0 = true then 0
  else if y 1 = false ∨ x 1 = true then 2 else 1

def tau (x y : Fin 3 → Bool) : ℕ := ((pos x y : Fin 3) : ℕ)

def A0 : Matrix (Fin 3 → Bool) (Fin 1) ℚ :=
  Matrix.of fun x _ => if x 0 = false ∧ (x 1 = false ∨ x 2 = false) then 1 else 0

def B0 : Matrix (Fin 1) (Fin 3 → Bool) ℚ :=
  Matrix.of fun _ y => if y 0 = true ∧ (y 1 = true ∨ y 2 = true) then 1 else 0

def A1 : Matrix (Fin 3 → Bool) (Fin 2) ℚ :=
  Matrix.of fun x j =>
    if j = 0 then (if x 0 = true ∧ x 1 = false ∧ x 2 = false then 1 else 0)
    else (if x 0 = false ∧ x 1 = false then 1 else 0)

def B1 : Matrix (Fin 2) (Fin 3 → Bool) ℚ :=
  Matrix.of fun j y =>
    if j = 0 then (if y 1 = true ∧ (y 0 = true ∨ y 2 = true) then 1 else 0)
    else (if y 0 = false ∧ y 1 = true ∧ y 2 = true then 1 else 0)

def A2 : Matrix (Fin 3 → Bool) (Fin 2) ℚ :=
  Matrix.of fun x j =>
    if j = 0 then (if x 0 = true ∧ x 1 = false ∧ x 2 = false then 1 else 0)
    else (if x 0 = false ∧ x 1 = true ∧ x 2 = false then 1 else 0)

def B2 : Matrix (Fin 2) (Fin 3 → Bool) ℚ :=
  Matrix.of fun j y =>
    if j = 0 then (if y 0 = true ∧ y 1 = false ∧ y 2 = true then 1 else 0)
    else (if y 0 = false ∧ y 1 = true ∧ y 2 = true then 1 else 0)

abbrev fn : (Fin 3 → Bool) → Bool :=
  fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)

lemma typing : IsTyping 3 fn tau := by
  intro x y hx hy
  refine ⟨pos x y, rfl, ?_⟩
  rcases Bool.eq_false_or_eq_true (x 0) with a0 | a0 <;>
  rcases Bool.eq_false_or_eq_true (x 1) with a1 | a1 <;>
  rcases Bool.eq_false_or_eq_true (x 2) with a2 | a2 <;>
  rcases Bool.eq_false_or_eq_true (y 0) with c0 | c0 <;>
  rcases Bool.eq_false_or_eq_true (y 1) with c1 | c1 <;>
  rcases Bool.eq_false_or_eq_true (y 2) with c2 | c2 <;>
  simp [fn, pos, a0, a1, a2, c0, c1, c2] at hx hy ⊢

lemma m0f : typedMatrix 3 fn tau 0 false = A0 * B0 := by
  ext x y
  simp only [typedMatrix, tau, Matrix.mul_apply, A0, B0, Matrix.of_apply, Fin.sum_univ_one]
  rcases Bool.eq_false_or_eq_true (x 0) with a0 | a0 <;>
  rcases Bool.eq_false_or_eq_true (x 1) with a1 | a1 <;>
  rcases Bool.eq_false_or_eq_true (x 2) with a2 | a2 <;>
  rcases Bool.eq_false_or_eq_true (y 0) with c0 | c0 <;>
  rcases Bool.eq_false_or_eq_true (y 1) with c1 | c1 <;>
  rcases Bool.eq_false_or_eq_true (y 2) with c2 | c2 <;>
  simp [fn, pos, a0, a1, a2, c0, c1, c2]

lemma m1f : typedMatrix 3 fn tau 1 false = A1 * B1 := by
  ext x y
  simp only [typedMatrix, tau, Matrix.mul_apply, A1, B1, Matrix.of_apply, Fin.sum_univ_two]
  rcases Bool.eq_false_or_eq_true (x 0) with a0 | a0 <;>
  rcases Bool.eq_false_or_eq_true (x 1) with a1 | a1 <;>
  rcases Bool.eq_false_or_eq_true (x 2) with a2 | a2 <;>
  rcases Bool.eq_false_or_eq_true (y 0) with c0 | c0 <;>
  rcases Bool.eq_false_or_eq_true (y 1) with c1 | c1 <;>
  rcases Bool.eq_false_or_eq_true (y 2) with c2 | c2 <;>
  simp [fn, pos, a0, a1, a2, c0, c1, c2]

lemma m2f : typedMatrix 3 fn tau 2 false = A2 * B2 := by
  ext x y
  simp only [typedMatrix, tau, Matrix.mul_apply, A2, B2, Matrix.of_apply, Fin.sum_univ_two]
  rcases Bool.eq_false_or_eq_true (x 0) with a0 | a0 <;>
  rcases Bool.eq_false_or_eq_true (x 1) with a1 | a1 <;>
  rcases Bool.eq_false_or_eq_true (x 2) with a2 | a2 <;>
  rcases Bool.eq_false_or_eq_true (y 0) with c0 | c0 <;>
  rcases Bool.eq_false_or_eq_true (y 1) with c1 | c1 <;>
  rcases Bool.eq_false_or_eq_true (y 2) with c2 | c2 <;>
  simp [fn, pos, a0, a1, a2, c0, c1, c2]

lemma mt (i : Fin 3) : typedMatrix 3 fn tau i true = 0 := by
  ext x y
  simp only [typedMatrix, tau, Matrix.zero_apply]
  rcases Bool.eq_false_or_eq_true (x 0) with a0 | a0 <;>
  rcases Bool.eq_false_or_eq_true (x 1) with a1 | a1 <;>
  rcases Bool.eq_false_or_eq_true (x 2) with a2 | a2 <;>
  rcases Bool.eq_false_or_eq_true (y 0) with c0 | c0 <;>
  rcases Bool.eq_false_or_eq_true (y 1) with c1 | c1 <;>
  rcases Bool.eq_false_or_eq_true (y 2) with c2 | c2 <;>
  fin_cases i <;>
  simp [fn, pos, a0, a1, a2, c0, c1, c2]

lemma main : HasTypedRank 3 fn 5 := by
  refine ⟨tau, typing, ?_⟩
  rw [Fin.sum_univ_three, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  rw [mt 0, mt 1, mt 2, m0f, m1f, m2f, Matrix.rank_zero]
  have h0 : (A0 * B0).rank ≤ 1 :=
    le_trans (Matrix.rank_mul_le_left _ _) (by simpa using Matrix.rank_le_card_width A0)
  have h1 : (A1 * B1).rank ≤ 2 :=
    le_trans (Matrix.rank_mul_le_left _ _) (by simpa using Matrix.rank_le_card_width A1)
  have h2 : (A2 * B2).rank ≤ 2 :=
    le_trans (Matrix.rank_mul_le_left _ _) (by simpa using Matrix.rank_le_card_width A2)
  omega

end PEqualNP.Outside.L_meta_233_aux

theorem PEqualNP.Outside.L_meta_233 : PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)) 5 := by
  exact PEqualNP.Outside.L_meta_233_aux.main
