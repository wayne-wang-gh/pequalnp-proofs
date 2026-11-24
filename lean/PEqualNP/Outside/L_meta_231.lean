import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_231

open PEqualNP.MetaComplexity

def par : (Fin 3 → Bool) → Bool := fun x => xor (xor (x 0) (x 1)) (x 2)

def pA : Fin 3 → Bool := ![true, false, false]
def pB : Fin 3 → Bool := ![false, true, false]
def pC : Fin 3 → Bool := ![false, false, true]
def pD : Fin 3 → Bool := ![true, true, true]
def qO : Fin 3 → Bool := ![false, false, false]
def qE1 : Fin 3 → Bool := ![false, true, true]
def qE2 : Fin 3 → Bool := ![true, false, true]
def qE3 : Fin 3 → Bool := ![true, true, false]

lemma one_le_rank {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℚ) (r : m) (c : n) (h : M r c = 1) : 1 ≤ M.rank := by
  have hs : (M.submatrix (fun _ : Fin 1 => r) (fun _ : Fin 1 => c)).rank = 1 := by
    rw [Matrix.rank_of_isUnit]
    · simp
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
      simp [h]
  calc 1 = _ := hs.symm
    _ ≤ M.rank := Matrix.rank_submatrix_le _ _ _

lemma two_le_rank {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℚ) (r1 r2 : m) (c1 c2 : n) (h11 : M r1 c1 = 1) (h22 : M r2 c2 = 1)
    (h : M r1 c2 = 0 ∨ M r2 c1 = 0) : 2 ≤ M.rank := by
  have hs : (M.submatrix ![r1, r2] ![c1, c2]).rank = 2 := by
    rw [Matrix.rank_of_isUnit]
    · simp
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two]
      rcases h with h | h <;> simp [h11, h22, h]
  calc 2 = _ := hs.symm
    _ ≤ M.rank := Matrix.rank_submatrix_le _ _ _

lemma lit_lb (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (i : Fin 3) (b : Bool)
    (r1 r2 c1 c2 : Fin 3 → Bool) (k : ℕ) (hk : (i : ℕ) = k)
    (hr1 : par r1 = true) (hr2 : par r2 = true) (hc1 : par c1 = false) (hc2 : par c2 = false)
    (hb1 : r1 i = b) (hb2 : r2 i = b) (ht1 : τ r1 c1 = k) (ht2 : τ r2 c2 = k) :
    (if τ r1 c2 = k ∧ τ r2 c1 = k then 1 else 2) ≤ (typedMatrix 3 par τ i b).rank := by
  subst hk
  split_ifs with h
  · exact one_le_rank _ r1 c1 (by simp [typedMatrix, hr1, hc1, hb1, ht1])
  · apply two_le_rank _ r1 r2 c1 c2 (by simp [typedMatrix, hr1, hc1, hb1, ht1])
      (by simp [typedMatrix, hr2, hc2, hb2, ht2])
    rw [not_and_or] at h
    rcases h with h | h
    · left; simp [typedMatrix, h]
    · right; simp [typedMatrix, h]

lemma forced (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (hτ : IsTyping 3 par τ)
    (x y : Fin 3 → Bool) (j : Fin 3) (hx : par x = true) (hy : par y = false)
    (hd : ∀ k : Fin 3, x k ≠ y k → k = j) : τ x y = j := by
  obtain ⟨k, hk, hne⟩ := hτ x y hx hy
  rw [hk, hd k hne]

lemma lt3 (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (hτ : IsTyping 3 par τ)
    (x y : Fin 3 → Bool) (hx : par x = true) (hy : par y = false) : τ x y < 3 := by
  obtain ⟨k, hk, -⟩ := hτ x y hx hy
  rw [hk]
  exact k.isLt

lemma arith : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ d < 3,
    10 ≤ (if a = 0 ∧ d = 0 then 1 else 2) + (if b = 0 ∧ c = 0 then 1 else 2)
      + (if b = 1 ∧ d = 1 then 1 else 2) + (if a = 1 ∧ c = 1 then 1 else 2)
      + (if c = 2 ∧ d = 2 then 1 else 2) + (if a = 2 ∧ b = 2 then 1 else 2) := by
  decide

lemma lower : ¬ HasTypedRank 3 par 9 := by
  rintro ⟨τ, hτ, hsum⟩
  rw [Fin.sum_univ_three, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool] at hsum
  have l1 := lit_lb τ 0 true pA pD qO qE1 0 rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (forced τ hτ _ _ 0 (by decide) (by decide) (by decide))
    (forced τ hτ _ _ 0 (by decide) (by decide) (by decide))
  have l2 := lit_lb τ 0 false pB pC qE3 qE2 0 rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (forced τ hτ _ _ 0 (by decide) (by decide) (by decide))
    (forced τ hτ _ _ 0 (by decide) (by decide) (by decide))
  have l3 := lit_lb τ 1 true pB pD qO qE2 1 rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (forced τ hτ _ _ 1 (by decide) (by decide) (by decide))
    (forced τ hτ _ _ 1 (by decide) (by decide) (by decide))
  have l4 := lit_lb τ 1 false pA pC qE3 qE1 1 rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (forced τ hτ _ _ 1 (by decide) (by decide) (by decide))
    (forced τ hτ _ _ 1 (by decide) (by decide) (by decide))
  have l5 := lit_lb τ 2 true pC pD qO qE3 2 rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (forced τ hτ _ _ 2 (by decide) (by decide) (by decide))
    (forced τ hτ _ _ 2 (by decide) (by decide) (by decide))
  have l6 := lit_lb τ 2 false pA pB qE2 qE1 2 rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (forced τ hτ _ _ 2 (by decide) (by decide) (by decide))
    (forced τ hτ _ _ 2 (by decide) (by decide) (by decide))
  have ha := lt3 τ hτ pA qE1 (by decide) (by decide)
  have hb := lt3 τ hτ pB qE2 (by decide) (by decide)
  have hc := lt3 τ hτ pC qE3 (by decide) (by decide)
  have hd := lt3 τ hτ pD qO (by decide) (by decide)
  have h10 := arith _ ha _ hb _ hc _ hd
  omega

def τ0 : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ :=
  fun x y => if x 0 ≠ y 0 then 0 else if x 1 ≠ y 1 then 1 else 2

lemma typing0 : IsTyping 3 par τ0 := by
  intro x y hx hy
  by_cases h0 : x 0 = y 0
  · by_cases h1 : x 1 = y 1
    · refine ⟨2, by simp [τ0, h0, h1], ?_⟩
      intro h2
      have hxy : x = y := by
        funext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
      rw [hxy] at hx
      rw [hx] at hy
      exact Bool.noConfusion hy
    · exact ⟨1, by simp [τ0, h0, h1], h1⟩
  · exact ⟨0, by simp [τ0, h0], h0⟩

lemma supp (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (i : Fin 3) (b : Bool)
    (s : Finset (Fin 3 → Bool)) (hs : ∀ x, par x = true → x i = b → x ∈ s) :
    (typedMatrix 3 par τ i b).rank ≤ s.card := by
  apply Matrix.rank_le_card_of_support_subset
  rw [Function.support_subset_iff']
  intro x hx
  funext y
  rw [Matrix.row_apply]
  simp only [typedMatrix, Pi.zero_apply]
  rw [ite_eq_right_iff]
  rintro ⟨h1, -, -, h4⟩
  exact absurd (hs x h1 h4) hx

lemma rank0 (b : Bool) : (typedMatrix 3 par τ0 0 b).rank ≤ 1 := by
  have he : typedMatrix 3 par τ0 0 b =
      Matrix.vecMulVec (fun x => if par x = true ∧ x 0 = b then (1 : ℚ) else 0)
        (fun y => if par y = false ∧ y 0 = !b then (1 : ℚ) else 0) := by
    ext x y
    rw [Matrix.vecMulVec_apply]
    simp only [typedMatrix, τ0]
    rcases Bool.eq_false_or_eq_true (par x) with hpx | hpx <;>
    rcases Bool.eq_false_or_eq_true (par y) with hpy | hpy <;>
    rcases Bool.eq_false_or_eq_true (x 0) with hx0 | hx0 <;>
    rcases Bool.eq_false_or_eq_true (y 0) with hy0 | hy0 <;>
    cases b <;> simp [hpx, hpy, hx0, hy0] <;> split_ifs <;> simp
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

lemma upper : HasTypedRank 3 par 10 := by
  refine ⟨τ0, typing0, ?_⟩
  rw [Fin.sum_univ_three, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  have h1 := rank0 true
  have h2 := rank0 false
  have h3 := (supp τ0 1 true {pB, pD} (by decide)).trans (le_of_eq (Finset.card_pair (by decide)))
  have h4 := (supp τ0 1 false {pA, pC} (by decide)).trans (le_of_eq (Finset.card_pair (by decide)))
  have h5 := (supp τ0 2 true {pC, pD} (by decide)).trans (le_of_eq (Finset.card_pair (by decide)))
  have h6 := (supp τ0 2 false {pA, pB} (by decide)).trans (le_of_eq (Finset.card_pair (by decide)))
  omega

end PEqualNP.Outside.L_meta_231

theorem PEqualNP.Outside.L_meta_231 : PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => xor (xor (x 0) (x 1)) (x 2)) 10 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => xor (xor (x 0) (x 1)) (x 2)) 9 :=
  ⟨PEqualNP.Outside.L_meta_231.upper, PEqualNP.Outside.L_meta_231.lower⟩
