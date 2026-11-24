import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_232

abbrev par : (Fin 4 → Bool) → Bool := fun x => xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)

def inp (m : ℕ) : Fin 4 → Bool := fun t => m.testBit t.val

def code (i : Fin 4) (b : Bool) (j : Fin 4) : ℕ :=
  ((List.range 16).filter (fun m => par (inp m) && decide (inp m i = b))).getD j.val 0

def ccode (i : Fin 4) (b : Bool) (j : Fin 4) : ℕ := code i b j ^^^ 2 ^ i.val

def rows (i : Fin 4) (b : Bool) (j : Fin 4) : Fin 4 → Bool := inp (code i b j)

def cols (i : Fin 4) (b : Bool) (j : Fin 4) : Fin 4 → Bool := inp (ccode i b j)

theorem rows_par : ∀ i b j, par (rows i b j) = true := by decide

theorem cols_par : ∀ i b j, par (cols i b j) = false := by decide

theorem rows_at : ∀ i b j, rows i b j i = b := by decide

theorem diag_only : ∀ i b j (t : Fin 4), rows i b j t ≠ cols i b j t → t = i := by decide

theorem code_inj : ∀ i b j k, code i b j = code i b k → j = k := by decide

theorem ccode_inj : ∀ i b j k, ccode i b j = ccode i b k → j = k := by decide

def T : Finset (ℕ × ℕ) :=
  ((Finset.range 16) ×ˢ (Finset.range 16)).filter
    (fun q => par (inp q.1) = true ∧ par (inp q.2) = false ∧ (q.1 ^^^ q.2) ∉ ({1, 2, 4, 8} : Finset ℕ))

theorem T_card : T.card = 32 := by decide

theorem mem_T : ∀ i b j k, j ≠ k → (code i b j, ccode i b k) ∈ T := by decide

theorem le_rank_of_det {m n : Type} [Fintype n] {k : ℕ} (A : Matrix m n ℚ) (ρ : Fin k → m)
    (κ : Fin k → n) (h : (A.submatrix ρ κ).det ≠ 0) : k ≤ A.rank := by
  have h1 := Matrix.rank_submatrix_le A ρ κ
  have h2 : (A.submatrix ρ κ).rank = k := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))]
    simp
  omega

def z (P : Fin 4 → Fin 4 → Bool) (j k : Fin 4) : ℤ := if P j k then 1 else 0

def det3Z (P : Fin 4 → Fin 4 → Bool) (a b c : Fin 4) : ℤ :=
  z P a a * z P b b * z P c c - z P a a * z P b c * z P c b - z P a b * z P b a * z P c c +
    z P a b * z P b c * z P c a + z P a c * z P b a * z P c b - z P a c * z P b b * z P c a

def Pm (p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32 : Bool) : Fin 4 → Fin 4 → Bool :=
  ![![true, p01, p02, p03], ![p10, true, p12, p13], ![p20, p21, true, p23], ![p30, p31, p32, true]]

def cnt (P : Fin 4 → Fin 4 → Bool) : ℕ :=
  (Finset.univ.filter (fun jk : Fin 4 × Fin 4 => jk.1 ≠ jk.2 ∧ P jk.1 jk.2 = true)).card

set_option maxRecDepth 100000 in
theorem pat3 : ∀ p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32 : Bool,
    cnt (Pm p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32) ≤ 3 →
      det3Z (Pm p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32) 1 2 3 ≠ 0 ∨
      det3Z (Pm p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32) 0 2 3 ≠ 0 ∨
      det3Z (Pm p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32) 0 1 3 ≠ 0 ∨
      det3Z (Pm p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32) 0 1 2 ≠ 0 := by
  decide

set_option maxRecDepth 100000 in
theorem pat2 : ∀ p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32 : Bool,
    cnt (Pm p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32) ≤ 11 →
      ∃ j k : Fin 4, j ≠ k ∧ Pm p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32 j k = false := by
  decide

theorem P_eq_Pm (P : Fin 4 → Fin 4 → Bool) (hd : ∀ j, P j j = true) :
    P = Pm (P 0 1) (P 0 2) (P 0 3) (P 1 0) (P 1 2) (P 1 3) (P 2 0) (P 2 1) (P 2 3) (P 3 0)
      (P 3 1) (P 3 2) := by
  funext j k
  fin_cases j <;> fin_cases k <;> simp [Pm, hd]

theorem det3_cast (P : Fin 4 → Fin 4 → Bool) (A : Matrix (Fin 4) (Fin 4) ℚ)
    (hA : ∀ j k, A j k = if P j k then 1 else 0) (a b c : Fin 4) :
    (A.submatrix ![a, b, c] ![a, b, c]).det = (det3Z P a b c : ℚ) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, hA, det3Z, z]
  push_cast
  ring

theorem block_rank (P : Fin 4 → Fin 4 → Bool) (hd : ∀ j, P j j = true)
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : ∀ j k, A j k = if P j k then 1 else 0) :
    12 ≤ 4 * A.rank + cnt P := by
  rw [P_eq_Pm P hd] at hA ⊢
  generalize P 0 1 = p01 at *
  generalize P 0 2 = p02 at *
  generalize P 0 3 = p03 at *
  generalize P 1 0 = p10 at *
  generalize P 1 2 = p12 at *
  generalize P 1 3 = p13 at *
  generalize P 2 0 = p20 at *
  generalize P 2 1 = p21 at *
  generalize P 2 3 = p23 at *
  generalize P 3 0 = p30 at *
  generalize P 3 1 = p31 at *
  generalize P 3 2 = p32 at *
  set Q := Pm p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32 with hQ
  have hQd : ∀ j, Q j j = true := by
    intro j
    fin_cases j <;> rfl
  by_cases h3 : cnt Q ≤ 3
  · have hr : 3 ≤ A.rank := by
      rcases pat3 p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32 h3 with h | h | h | h
      · exact le_rank_of_det A ![1, 2, 3] ![1, 2, 3] (by rw [det3_cast Q A hA]; exact_mod_cast h)
      · exact le_rank_of_det A ![0, 2, 3] ![0, 2, 3] (by rw [det3_cast Q A hA]; exact_mod_cast h)
      · exact le_rank_of_det A ![0, 1, 3] ![0, 1, 3] (by rw [det3_cast Q A hA]; exact_mod_cast h)
      · exact le_rank_of_det A ![0, 1, 2] ![0, 1, 2] (by rw [det3_cast Q A hA]; exact_mod_cast h)
    omega
  · by_cases h11 : cnt Q ≤ 11
    · obtain ⟨j, k, hjk, hz0⟩ := pat2 p01 p02 p03 p10 p12 p13 p20 p21 p23 p30 p31 p32 h11
      have hz : Q j k = false := hz0
      have hr : 2 ≤ A.rank := by
        refine le_rank_of_det A ![j, k] ![j, k] ?_
        rw [Matrix.det_fin_two]
        simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, hA, hQd, hz]
        norm_num
      omega
    · have hr : 1 ≤ A.rank := by
        refine le_rank_of_det A ![0] ![0] ?_
        rw [Matrix.det_fin_one]
        simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, hA, hQd]
        norm_num
      omega

theorem block_ineq (τ : (Fin 4 → Bool) → (Fin 4 → Bool) → ℕ) (hτ : IsTyping 4 par τ)
    (i : Fin 4) (b : Bool) :
    12 ≤ 4 * (typedMatrix 4 par τ i b).rank +
      (Finset.univ.filter (fun jk : Fin 4 × Fin 4 =>
        jk.1 ≠ jk.2 ∧ τ (rows i b jk.1) (cols i b jk.2) = (i : ℕ))).card := by
  set P : Fin 4 → Fin 4 → Bool := fun j k => decide (τ (rows i b j) (cols i b k) = (i : ℕ)) with hP
  have hd : ∀ j, P j j = true := by
    intro j
    obtain ⟨t, ht, hne⟩ := hτ (rows i b j) (cols i b j) (rows_par i b j) (cols_par i b j)
    have := diag_only i b j t hne
    subst this
    simp [hP, ht]
  have hA : ∀ j k, (typedMatrix 4 par τ i b).submatrix (rows i b) (cols i b) j k =
      if P j k then 1 else 0 := by
    intro j k
    simp only [typedMatrix, Matrix.submatrix_apply]
    rw [rows_par i b j, cols_par i b k, rows_at i b j]
    simp [hP]
  have h1 := block_rank P hd _ hA
  have h2 := Matrix.rank_submatrix_le (typedMatrix 4 par τ i b) (rows i b) (cols i b)
  have h3 : cnt P = (Finset.univ.filter (fun jk : Fin 4 × Fin 4 =>
      jk.1 ≠ jk.2 ∧ τ (rows i b jk.1) (cols i b jk.2) = (i : ℕ))).card := by
    simp [cnt, hP]
  omega

theorem count_le (τ : (Fin 4 → Bool) → (Fin 4 → Bool) → ℕ) :
    (∑ i : Fin 4, ∑ b : Bool, (Finset.univ.filter (fun jk : Fin 4 × Fin 4 =>
      jk.1 ≠ jk.2 ∧ τ (rows i b jk.1) (cols i b jk.2) = (i : ℕ))).card) ≤ 32 := by
  have hO : (∑ i : Fin 4, ∑ b : Bool, (Finset.univ.filter (fun jk : Fin 4 × Fin 4 =>
      jk.1 ≠ jk.2 ∧ τ (rows i b jk.1) (cols i b jk.2) = (i : ℕ))).card) =
      (Finset.univ.filter (fun c : Fin 4 × Bool × Fin 4 × Fin 4 =>
        c.2.2.1 ≠ c.2.2.2 ∧ τ (rows c.1 c.2.1 c.2.2.1) (cols c.1 c.2.1 c.2.2.2) = (c.1 : ℕ))).card := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [hO, ← T_card]
  refine Finset.card_le_card_of_injOn (fun c => (code c.1 c.2.1 c.2.2.1, ccode c.1 c.2.1 c.2.2.2)) ?_ ?_
  · rintro ⟨i, b, j, k⟩ hc
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc
    exact mem_T i b j k hc.1
  · rintro ⟨i, b, j, k⟩ hc ⟨i', b', j', k'⟩ hc' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc hc'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hcode, hccode⟩ := heq
    have hr : rows i b j = rows i' b' j' := by
      unfold rows
      rw [hcode]
    have hc2 : cols i b k = cols i' b' k' := by
      unfold cols
      rw [hccode]
    have hi : i = i' := by
      apply Fin.ext
      have e1 := hc.2
      have e2 := hc'.2
      rw [hr, hc2] at e1
      omega
    subst hi
    have hb : b = b' := by
      have e1 := rows_at i b j
      have e2 := rows_at i b' j'
      rw [hr] at e1
      rw [← e1, e2]
    subst hb
    have hj := code_inj i b j j' hcode
    have hk := ccode_inj i b k k' hccode
    subst hj
    subst hk
    rfl

end PEqualNP.Outside.L_meta_232

theorem PEqualNP.Outside.L_meta_232 : ¬ PEqualNP.MetaComplexity.HasTypedRank 4 (fun x : Fin 4 → Bool => xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)) 15 := by
  change ¬ HasTypedRank 4 PEqualNP.Outside.L_meta_232.par 15
  rintro ⟨τ, hτ, hsum⟩
  have hc := PEqualNP.Outside.L_meta_232.count_le τ
  have b0t := PEqualNP.Outside.L_meta_232.block_ineq τ hτ 0 true
  have b0f := PEqualNP.Outside.L_meta_232.block_ineq τ hτ 0 false
  have b1t := PEqualNP.Outside.L_meta_232.block_ineq τ hτ 1 true
  have b1f := PEqualNP.Outside.L_meta_232.block_ineq τ hτ 1 false
  have b2t := PEqualNP.Outside.L_meta_232.block_ineq τ hτ 2 true
  have b2f := PEqualNP.Outside.L_meta_232.block_ineq τ hτ 2 false
  have b3t := PEqualNP.Outside.L_meta_232.block_ineq τ hτ 3 true
  have b3f := PEqualNP.Outside.L_meta_232.block_ineq τ hτ 3 false
  simp only [Fin.sum_univ_four, Fintype.sum_bool] at hsum hc
  omega
