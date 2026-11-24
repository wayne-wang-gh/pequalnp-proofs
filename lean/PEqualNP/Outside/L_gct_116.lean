import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_116_aux

open Finset

-- Index the product by the chosen columns, so a frequency assignment survives a row shift.
private noncomputable def rowTerm {n : ℕ} (T : Finset (Fin n)) (H : T → Fin n → ℂ)
    (S : Finset (Fin n)) : ℂ :=
  ∑ σ : (S ≃ T), ∏ t : T, H t (σ.symm t : Fin n)

private noncomputable def rowSum {n : ℕ} (k : ℕ) (T : Finset (Fin n)) (H : T → Fin n → ℂ) : ℂ :=
  ∑ S ∈ (univ : Finset (Fin n)).powersetCard k, rowTerm T H S

private theorem termMap {n : ℕ} (T S : Finset (Fin n)) (H : T → Fin n → ℂ)
    (e : Equiv.Perm (Fin n)) :
    rowTerm T H (S.map e.toEmbedding) = rowTerm T (fun t i => H t (e i)) S := by
  classical
  symm
  exact Fintype.sum_equiv ((Finset.equivMap e.toEmbedding S).equivCongr (Equiv.refl T)) _ _
    (fun _ => rfl)

private theorem permuteRows {n : ℕ} (k : ℕ) (T : Finset (Fin n)) (H : T → Fin n → ℂ)
    (e : Equiv.Perm (Fin n)) :
    rowSum k T H = rowSum k T (fun t i => H t (e i)) := by
  classical
  have hm := powersetCard_map e.toEmbedding k (univ : Finset (Fin n))
  rw [map_univ_equiv] at hm
  unfold rowSum
  conv_lhs => rw [hm, sum_map]
  exact sum_congr rfl (fun S _ => termMap T S H e)

private theorem scaleRows {n : ℕ} (k : ℕ) (T : Finset (Fin n)) (H : T → Fin n → ℂ)
    (w : T → ℂ) :
    rowSum k T (fun t i => w t * H t i) = (∏ t, w t) * rowSum k T H := by
  classical
  simp only [rowSum, rowTerm, prod_mul_distrib, mul_sum]

private theorem expandTerm {n m : ℕ} (T S : Finset (Fin n)) (F : Fin m → T → Fin n → ℂ) :
    rowTerm T (fun t i => ∑ a, F a t i) S =
      ∑ a : T → Fin m, rowTerm T (fun t i => F (a t) t i) S := by
  classical
  unfold rowTerm
  simp_rw [prod_univ_sum, Fintype.piFinset_univ]
  exact sum_comm

private theorem expandRows {n m : ℕ} (k : ℕ) (T : Finset (Fin n)) (F : Fin m → T → Fin n → ℂ) :
    rowSum k T (fun t i => ∑ a, F a t i) =
      ∑ a : T → Fin m, rowSum k T (fun t i => F (a t) t i) := by
  classical
  unfold rowSum
  simp_rw [expandTerm]
  exact sum_comm

private theorem rotatePower {n : ℕ} (ω : ℂ) (hn : ω ^ n = 1) (i : Fin n) :
    ω ^ (finRotate n i).val = ω * ω ^ i.val := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    by_cases h : i = Fin.last n
    · subst i
      simp only [finRotate_last, Fin.val_zero, pow_zero, Fin.val_last]
      rw [← pow_succ', hn]
    · rw [coe_finRotate_of_ne_last h, pow_succ']

private theorem rotateFrequency {n : ℕ} (ω : ℂ) (hn : ω ^ n = 1) (d : ℕ) (i : Fin n) :
    ω ^ (d * (finRotate n i).val) = ω ^ d * ω ^ (d * i.val) := by
  rw [Nat.mul_comm d (finRotate n i).val, pow_mul, rotatePower ω hn, mul_pow,
    ← pow_mul, Nat.mul_comm i.val d]

-- The multiplier of a fixed frequency assignment is different from one.
private theorem vanishing {n m k : ℕ} (T : Finset (Fin n)) (hT : T.card = k)
    (ω : ℂ) (nontrivial : ∀ s : ℕ, 0 < s → s < n → ω ^ s ≠ 1)
    (hk : 1 ≤ k) (hkm : k * m < n) (a : T → Fin m) (H : T → Fin n → ℂ)
    (shift : ∀ t i, H t (finRotate n i) = ω ^ ((a t).val + 1) * H t i) :
    rowSum k T H = 0 := by
  classical
  let d := ∑ t : T, ((a t).val + 1)
  have low : k ≤ d := calc
    k = ∑ _t : T, 1 := by simp [hT]
    _ ≤ _ := sum_le_sum fun t _ => Nat.le_add_left 1 (a t).val
  have high : d ≤ k * m := calc
    _ ≤ ∑ _t : T, m := sum_le_sum fun t _ => (a t).isLt
    _ = _ := by simp [hT]
  have hne := nontrivial d (by omega) (high.trans_lt hkm)
  have same : rowSum k T H = ω ^ d * rowSum k T H := calc
    _ = rowSum k T (fun t i => H t (finRotate n i)) := permuteRows k T H _
    _ = rowSum k T (fun t i => ω ^ ((a t).val + 1) * H t i) := by simp_rw [shift]
    _ = _ := by rw [scaleRows, prod_pow_eq_pow_sum]
  exact (mul_eq_zero.mp (show (ω^d - 1) * rowSum k T H = 0 by linear_combination -same)).resolve_left
    (sub_ne_zero.mpr hne)

end PEqualNP.Outside.L_gct_116_aux

open Finset PEqualNP.Outside.L_gct_116_aux

theorem PEqualNP.Outside.L_gct_116 : ∀ (n m k : ℕ) (ω : ℂ) (c : Fin m → Fin n → ℂ), ω ^ n = 1 → (∀ s : ℕ, 0 < s → s < n → ω ^ s ≠ 1) → 1 ≤ k → k * m < n → (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ σ : (↥S ≃ ↥T), ∏ i : ↥S, ∑ a : Fin m, ∑ b : Fin n, c a b * ω ^ ((a.val + 1) * i.val.val + b.val * (σ i).val.val)) = 0 := by
  classical
  intro n m k ω c hn hprimitive hk hkm
  rw [Finset.sum_comm]
  apply sum_eq_zero
  intro T hT
  let F (a : Fin m) (t : T) (i : Fin n) :=
    ∑ b : Fin n, c a b * ω ^ ((a.val + 1) * i.val + b.val * t.val.val)
  have reindex (S : Finset (Fin n)) (σ : S ≃ T) :
      (∏ i : S, ∑ a : Fin m, ∑ b : Fin n,
        c a b * ω ^ ((a.val + 1) * i.val.val + b.val * (σ i).val.val)) =
      ∏ t : T, ∑ a : Fin m, F a t (σ.symm t) := by
    exact Fintype.prod_equiv σ _ _ (fun i => by simp [F])
  simp_rw [reindex]
  change rowSum k T (fun t i => ∑ a, F a t i) = 0
  rw [expandRows]
  apply sum_eq_zero
  intro a _
  apply vanishing T (mem_powersetCard.mp hT).2 ω hprimitive hk hkm a
  intro t i
  dsimp only [F]
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  rw [pow_add ω (_ * (finRotate n i).val) _, pow_add ω (_ * i.val) _,
    rotateFrequency ω hn]
  ring
