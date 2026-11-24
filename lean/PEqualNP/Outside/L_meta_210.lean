import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_210

open PEqualNP.MetaComplexity

-- a matrix whose nonzero entries all lie in one row has rank at most one
theorem rank_le_one {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℚ) (x0 : α)
    (h : ∀ x y, x ≠ x0 → M x y = 0) : M.rank ≤ 1 := by
  have e : M = Matrix.vecMulVec (fun x => if x = x0 then (1 : ℚ) else 0) (M x0) := by
    ext x y
    by_cases hx : x = x0
    · subst hx; simp [Matrix.vecMulVec_apply]
    · simp [Matrix.vecMulVec_apply, hx, h x y hx]
  rw [e]
  exact Matrix.rank_vecMulVec_le _ _

-- a matrix with a nonzero entry has rank at least one
theorem one_le_rank {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℚ) (x y : α)
    (h : M x y ≠ 0) : 1 ≤ M.rank := by
  by_contra hc
  have h0 : M.rank = 0 := by omega
  have hz : M.mulVecLin = 0 := by
    apply LinearMap.range_eq_bot.1
    apply Submodule.finrank_eq_zero.1
    exact h0
  apply h
  have := congrFun (congrArg (fun L => L (Pi.single y 1)) hz) x
  simpa using this

def par (x : Fin 2 → Bool) : Bool := xor (x 0) (x 1)

def tau (x y : Fin 2 → Bool) : ℕ := if x 0 = y 0 then 1 else 0

theorem tau_typing : IsTyping 2 par tau := by
  unfold IsTyping
  decide

theorem row (i : Fin 2) (b : Bool) : ∀ x y : Fin 2 → Bool,
    x ≠ ![(if i = 0 then b else !b), (if i = 0 then !b else b)] →
    ¬ (par x = true ∧ par y = false ∧ tau x y = (i : ℕ) ∧ x i = b) := by
  revert i b
  decide

theorem upper (i : Fin 2) (b : Bool) : (typedMatrix 2 par tau i b).rank ≤ 1 := by
  apply rank_le_one _ ![(if i = 0 then b else !b), (if i = 0 then !b else b)]
  intro x y hx
  unfold typedMatrix
  split_ifs with hc
  · exact absurd hc (row i b x y hx)
  · rfl

theorem forced : ∀ (i : Fin 2) (b : Bool), ∃ x y : Fin 2 → Bool, par x = true ∧ par y = false ∧
    x i = b ∧ ∀ j : Fin 2, x j ≠ y j → j = i := by
  decide

theorem lower (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ) (hτ : IsTyping 2 par τ) (i : Fin 2)
    (b : Bool) : 1 ≤ (typedMatrix 2 par τ i b).rank := by
  obtain ⟨x, y, hx, hy, hb, hj⟩ := forced i b
  obtain ⟨j, hj1, hj2⟩ := hτ x y hx hy
  have hji := hj j hj2
  subst hji
  apply one_le_rank _ x y
  unfold typedMatrix
  split_ifs with hc
  · exact one_ne_zero
  · exact absurd ⟨hx, hy, hj1, hb⟩ hc

end PEqualNP.Outside.L_meta_210

theorem PEqualNP.Outside.L_meta_210 : PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 4 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 3 := by
  constructor
  · refine ⟨PEqualNP.Outside.L_meta_210.tau, PEqualNP.Outside.L_meta_210.tau_typing, ?_⟩
    have h := PEqualNP.Outside.L_meta_210.upper
    have h00 := h 0 false
    have h01 := h 0 true
    have h10 := h 1 false
    have h11 := h 1 true
    rw [Fin.sum_univ_two, Fintype.sum_bool, Fintype.sum_bool]
    change _ ≤ 1 at h00
    unfold PEqualNP.Outside.L_meta_210.par at h00 h01 h10 h11
    omega
  · rintro ⟨τ, hτ, hs⟩
    have h := PEqualNP.Outside.L_meta_210.lower τ hτ
    have h00 := h 0 false
    have h01 := h 0 true
    have h10 := h 1 false
    have h11 := h 1 true
    rw [Fin.sum_univ_two, Fintype.sum_bool, Fintype.sum_bool] at hs
    unfold PEqualNP.Outside.L_meta_210.par at h00 h01 h10 h11
    omega
