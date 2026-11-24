import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_229

open PEqualNP.MetaComplexity

def F (n : ℕ) : (Fin n → Bool) → Bool := fun x => decide (∃ i : Fin n, x i = true)

def z (n : ℕ) : Fin n → Bool := fun _ => false

theorem F_false_iff {n : ℕ} (y : Fin n → Bool) : F n y = false ↔ ∀ j, y j = false := by
  unfold F
  simp

theorem F_true_iff {n : ℕ} (x : Fin n → Bool) : F n x = true ↔ ∃ i, x i = true := by
  unfold F
  simp

theorem eq_z {n : ℕ} (y : Fin n → Bool) (h : F n y = false) : y = z n :=
  funext fun j => (F_false_iff y).1 h j

theorem mat_false {n : ℕ} {τ : (Fin n → Bool) → (Fin n → Bool) → ℕ}
    (hτ : IsTyping n (F n) τ) (i : Fin n) : typedMatrix n (F n) τ i false = 0 := by
  ext x y
  simp only [typedMatrix, Matrix.zero_apply]
  split_ifs with h
  · exfalso
    obtain ⟨hx, hy, hti, hxi⟩ := h
    obtain ⟨j, hj, hne⟩ := hτ x y hx hy
    have hji : j = i := Fin.ext (hj.symm.trans hti)
    subst hji
    have hyj : y j = false := (F_false_iff y).1 hy j
    exact hne (by rw [hxi, hyj])
  · rfl

theorem mat_true_le {n : ℕ} {τ : (Fin n → Bool) → (Fin n → Bool) → ℕ}
    (i : Fin n) : (typedMatrix n (F n) τ i true).rank ≤ 1 := by
  have h : typedMatrix n (F n) τ i true =
      Matrix.vecMulVec (fun x => typedMatrix n (F n) τ i true x (z n))
        (fun y => if y = z n then (1 : ℚ) else 0) := by
    ext x y
    simp only [Matrix.vecMulVec_apply]
    by_cases hy : y = z n
    · subst hy
      simp
    · rw [if_neg hy, mul_zero]
      simp only [typedMatrix]
      rw [if_neg]
      rintro ⟨_, hfy, _⟩
      exact hy (eq_z y hfy)
  rw [h]
  exact Matrix.rank_vecMulVec_le _ _

theorem rank_pos_of_entry {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix α β ℚ) (x : α) (y : β) (h : M x y ≠ 0) : 1 ≤ M.rank := by
  by_contra hlt
  have h0 : M.rank = 0 := by omega
  unfold Matrix.rank at h0
  have hb : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h0
  have hmem : M.mulVecLin (Pi.single y 1) ∈ LinearMap.range M.mulVecLin :=
    LinearMap.mem_range_self _ _
  rw [hb, Submodule.mem_bot] at hmem
  have h1 := congrFun hmem x
  simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
  exact h h1

theorem mat_true_pos {n : ℕ} {τ : (Fin n → Bool) → (Fin n → Bool) → ℕ}
    (hτ : IsTyping n (F n) τ) (i : Fin n) : 1 ≤ (typedMatrix n (F n) τ i true).rank := by
  let e : Fin n → Bool := fun j => decide (j = i)
  have hfe : F n e = true := (F_true_iff e).2 ⟨i, by simp [e]⟩
  have hfz : F n (z n) = false := (F_false_iff _).2 (fun _ => rfl)
  obtain ⟨j, hj, hne⟩ := hτ e (z n) hfe hfz
  have hji : j = i := by
    by_contra hij
    apply hne
    simp [e, z, hij]
  subst hji
  refine rank_pos_of_entry _ e (z n) ?_
  simp only [typedMatrix]
  rw [if_pos ⟨hfe, hfz, hj, by simp [e]⟩]
  exact one_ne_zero

theorem sum_eq {n : ℕ} {τ : (Fin n → Bool) → (Fin n → Bool) → ℕ}
    (hτ : IsTyping n (F n) τ) :
    ∑ i : Fin n, ∑ b : Bool, (typedMatrix n (F n) τ i b).rank = n := by
  have h : ∀ i : Fin n, ∑ b : Bool, (typedMatrix n (F n) τ i b).rank = 1 := by
    intro i
    rw [Fintype.sum_bool, mat_false hτ i, Matrix.rank_zero]
    have h1 := mat_true_le (τ := τ) i
    have h2 := mat_true_pos hτ i
    omega
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp

theorem typing (n : ℕ) : IsTyping n (F n)
    (fun x y => if h : ∃ i : Fin n, x i ≠ y i then ((Classical.choose h : Fin n) : ℕ) else 0) := by
  intro x y hx hy
  obtain ⟨i, hi⟩ := (F_true_iff x).1 hx
  have hy' := (F_false_iff y).1 hy
  have h : ∃ i : Fin n, x i ≠ y i := ⟨i, by rw [hi, hy' i]; simp⟩
  exact ⟨Classical.choose h, by show (dite _ _ _) = _; rw [dif_pos h], Classical.choose_spec h⟩

theorem main (n : ℕ) (hn : 1 ≤ n) :
    HasTypedRank n (F n) n ∧ ¬ HasTypedRank n (F n) (n - 1) := by
  constructor
  · exact ⟨_, typing n, le_of_eq (sum_eq (typing n))⟩
  · rintro ⟨τ, hτ, hsum⟩
    rw [sum_eq hτ] at hsum
    omega

end PEqualNP.Outside.L_meta_229

theorem PEqualNP.Outside.L_meta_229 : ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) n ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) := by
  intro n hn
  exact PEqualNP.Outside.L_meta_229.main n hn
