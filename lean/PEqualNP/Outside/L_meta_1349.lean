import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

theorem divpow (h k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ h + 1) :
    2 ^ h * (2 ^ h + 1) / 2 ^ (k - 1) = 2 ^ (h + 1 - k) * (2 ^ h + 1) := by
  have e : 2 ^ h * (2 ^ h + 1) = 2 ^ (k - 1) * (2 ^ (h + 1 - k) * (2 ^ h + 1)) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [e, Nat.mul_div_cancel_left _ (by positivity)]

theorem arith (h g u v : ℕ) (hh : 1 ≤ h) (hg : 2 ≤ g) (huv : u + g ≤ v) (hv : v ≤ h + 2) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ (g - 1) - 1) ≤ ((if u = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if u = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h) - (if v = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if v = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (v - 1) - 2 ^ h)) * (if v = h + 2 then 2 ^ h else 2 ^ (v - 1) - 1) := by
  have hq : 2 ^ h = 2 * 2 ^ (h - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hB : 2 ^ h * 2 ^ h / 2 = 2 ^ (h - 1) * 2 ^ h := by
    have e : 2 ^ h * 2 ^ h = 2 * (2 ^ (h - 1) * 2 ^ h) := by rw [← mul_assoc, ← hq]
    rw [e, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hB]
  have hv0 : ¬ v = 0 := by omega
  have hu2 : ¬ u = h + 2 := by omega
  have hr : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
  have hG1 : 1 ≤ 2 ^ (g - 1) := Nat.one_le_two_pow
  by_cases hv2 : v = h + 2
  · simp only [if_neg hv0, if_pos hv2, Nat.sub_zero]
    by_cases hu0 : u = 0
    · simp only [if_pos hu0]
      have hG : 2 ^ (g - 1) ≤ 2 * 2 ^ h := by
        rw [← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      generalize 2 ^ (g - 1) = G at *
      generalize 2 ^ (h - 1) = r at *
      generalize 2 ^ h = q at *
      subst hq
      have h1 : r * (2 * r) * (G - 1) ≤ r * (2 * r) * (4 * r) := Nat.mul_le_mul_left _ (by omega)
      nlinarith [h1]
    · simp only [if_neg hu0, if_neg hu2]
      rw [divpow h u (by omega) (by omega)]
      have hE : 2 ^ (g - 1) ≤ 2 ^ (h + 1 - u) := Nat.pow_le_pow_right (by norm_num) (by omega)
      generalize 2 ^ (g - 1) = G at *
      generalize 2 ^ (h + 1 - u) = E at *
      generalize 2 ^ (h - 1) = r at *
      generalize 2 ^ h = q at *
      have h1 : r * (G - 1) ≤ E * (q + 1) - q := by
        have a1 : r * (G - 1) ≤ q * (G - 1) := Nat.mul_le_mul_right _ (by omega)
        have a2 : q * (G - 1) + q = q * G := by
          obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        have a3 : q * G ≤ E * q := by
          rw [mul_comm]
          exact Nat.mul_le_mul_right _ hE
        have a4 : E * (q + 1) = E * q + E := by ring
        omega
      calc r * q * (G - 1) = r * (G - 1) * q := by ring
        _ ≤ (E * (q + 1) - q) * q := Nat.mul_le_mul_right _ h1
  · simp only [if_neg hv0, if_neg hv2]
    rw [divpow h v (by omega) (by omega)]
    have hV : 2 ^ (g - 1) ≤ 2 ^ (v - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    by_cases hu0 : u = 0
    · simp only [if_pos hu0]
      have hE : 2 ^ (h + 1 - v) ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      generalize 2 ^ (g - 1) = G at *
      generalize 2 ^ (h + 1 - v) = E at *
      generalize 2 ^ (v - 1) = V at *
      generalize 2 ^ (h - 1) = r at *
      generalize 2 ^ h = q at *
      subst hq
      have b1 : E * (2 * r + 1) ≤ r * (2 * r + 1) := Nat.mul_le_mul_right _ hE
      have b2 : r * (2 * r + 1) = 2 * (r * r) + r := by ring
      have b3 : 2 * r * (2 * r) = 4 * (r * r) := by ring
      have b4 : r * (2 * r) = 2 * (r * r) := by ring
      have h1 : r * (2 * r) ≤ 2 * r * (2 * r) + 2 * r + 1 - (E * (2 * r + 1) - 2 * r) := by omega
      exact Nat.mul_le_mul h1 (by omega)
    · simp only [if_neg hu0, if_neg hu2]
      rw [divpow h u (by omega) (by omega)]
      have c1 : 2 ^ (h + 1 - u) = 2 ^ (h + 1 - v) * 2 ^ (v - u) := by
        rw [← pow_add]
        congr 1
        omega
      have c2 : 2 ^ (v - 1) = 2 * 2 ^ (v - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      have c3 : 2 ^ (h - 1) = 2 ^ (h + 1 - v) * 2 ^ (v - 2) := by
        rw [← pow_add]
        congr 1
        omega
      have hD : 2 ^ (g - 1) ≤ 2 ^ (v - u) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hE1 : 1 ≤ 2 ^ (h + 1 - v) := Nat.one_le_two_pow
      have hW1 : 1 ≤ 2 ^ (v - 2) := Nat.one_le_two_pow
      rw [c1, c2, c3]
      generalize 2 ^ (g - 1) = G at *
      generalize 2 ^ (h + 1 - v) = E at *
      generalize 2 ^ (v - u) = D at *
      generalize 2 ^ (v - 2) = W at *
      generalize 2 ^ h = q at *
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
      have d1 : E * (D' + 1) * (q + 1) = E * D' * (q + 1) + E * (q + 1) := by ring
      have d2 : q ≤ E * (q + 1) := by nlinarith
      have d3 : E * (D' + 1) * (q + 1) - q - (E * (q + 1) - q) = E * D' * (q + 1) := by omega
      rw [d3]
      calc E * W * q * (G - 1) = E * (G - 1) * q * W := by ring
        _ ≤ E * D' * (q + 1) * (2 * W - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left E (by omega)) (by omega)) (by omega)

theorem runs (P : Finset ℕ) (L : ℕ) : ∀ M : ℕ,
    (∀ u v : ℕ, u ≤ v → v < M → (∀ w ∈ P, ¬ (u < w ∧ w ≤ v)) → v - u + 1 ≤ L) →
    M ≤ ((P.filter (fun w => 0 < w ∧ w < M)).card + 1) * L := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hyp
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · exact Nat.zero_le _
    by_cases hS : (P.filter (fun w => 0 < w ∧ w < M)).Nonempty
    · obtain ⟨w, hwdef⟩ : ∃ w, w = (P.filter (fun w => 0 < w ∧ w < M)).max' hS := ⟨_, rfl⟩
      have hw : w ∈ P.filter (fun w => 0 < w ∧ w < M) := hwdef ▸ Finset.max'_mem _ hS
      have hmax : ∀ x ∈ P.filter (fun w => 0 < w ∧ w < M), x ≤ w :=
        fun x hx => hwdef ▸ Finset.le_max' _ x hx
      rw [Finset.mem_filter] at hw
      have h1 := ih w hw.2.2 (fun u v huv hv hc => hyp u v huv (by omega) hc)
      have h2 := hyp w (M - 1) (by omega) (by omega) (fun x hx hc => by
        have := hmax x (Finset.mem_filter.mpr ⟨hx, by omega, by omega⟩)
        omega)
      have hsub : P.filter (fun x => 0 < x ∧ x < w) ⊂ P.filter (fun x => 0 < x ∧ x < M) := by
        rw [Finset.ssubset_iff_of_subset (by
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hx.2.1, by omega⟩)]
        exact ⟨w, Finset.mem_filter.mpr hw, by simp⟩
      have h3 := Finset.card_lt_card hsub
      have h4 := Nat.mul_le_mul_right L h3
      have h5 : M - w ≤ L := by omega
      rw [add_mul, one_mul] at h1 ⊢
      rw [Nat.succ_mul] at h4
      omega
    · have h2 := hyp 0 (M - 1) (Nat.zero_le _) (by omega) (fun x hx hc =>
        hS ⟨x, Finset.mem_filter.mpr ⟨hx, by omega, by omega⟩⟩)
      rw [add_mul, one_mul]
      omega

theorem exrun (P : Finset ℕ) (M R g : ℕ) (hP : P.card + 1 ≤ R) (hg : R * g < M) :
    ∃ u v : ℕ, u ≤ v ∧ v < M ∧ (∀ w ∈ P, ¬ (u < w ∧ w ≤ v)) ∧ u + g ≤ v := by
  by_contra hcon
  have h1 := runs P g M (fun u v huv hv hc => by
    by_contra hlt
    exact hcon ⟨u, v, huv, hv, hc, by omega⟩)
  have hc : (P.filter (fun w => 0 < w ∧ w < M)).card ≤ P.card := Finset.card_filter_le _ _
  have h2 : ((P.filter (fun w => 0 < w ∧ w < M)).card + 1) * g ≤ R * g :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem min_lb {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℕ) (B : ℕ) (hne : s.Nonempty)
    (hall : ∀ a ∈ s, B ≤ f a) : B ≤ WithTop.untopD 0 ((s.image f).min) := by
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty (hne.image f)
  rw [hm]
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_min hm)
  exact hall a ha

end PEqualNP.Outside.L_meta_1349

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  refine PEqualNP.Outside.L_meta_1349.min_lb _ _ _ ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by
    rw [Finset.card_empty]
    exact Nat.one_le_two_pow⟩⟩ ?_
  intro P hP
  beta_reduce
  rw [Finset.mem_filter] at hP
  have hR : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hD := Nat.mul_div_le (h + 3 + 2 ^ t - 1) (2 ^ t)
  generalize (h + 3 + 2 ^ t - 1) / 2 ^ t = D at *
  by_cases hg : 2 ≤ D - 1
  · have e1 : 2 ^ t * (D - 1) + 2 ^ t = 2 ^ t * D := by
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    obtain ⟨u, v, huv, hv, hc, hd⟩ := PEqualNP.Outside.L_meta_1349.exrun P (h + 3) (2 ^ t) (D - 1) hP.2 (by omega)
    have hmem : (u, v) ∈ ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, huv, hc⟩
    refine le_trans ?_ (Finset.le_sup hmem)
    exact PEqualNP.Outside.L_meta_1349.arith h (D - 1) u v hh hg hd (by omega)
  · have e0 : D - 1 - 1 = 0 := by omega
    rw [e0]
    simp
