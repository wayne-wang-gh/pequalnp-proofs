import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1628

theorem ext_one (q N : ℕ) (L : Fin N → Finset (Fin N)) (l : Fin N) (S W : Finset (Fin N))
    (hcard : ∀ i0 : Fin N, (L i0).card = q + 1)
    (hmeet : ∀ i1 j1 : Fin N, i1 ≠ j1 → (L i1 ∩ L j1).card = 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! k1 : Fin N, p1 ∈ L k1 ∧ p2 ∈ L k1)
    (hS : ∀ t ∈ S, t ∉ L l) (harc : ∀ i2 : Fin N, (S ∩ L i2).card ≤ 2)
    (hW : ∀ w ∈ W, w ∉ L l) (hlt : S.card * (S.card - 1) * q < 2 * W.card) :
    ∃ w ∈ W, ∀ i3 : Fin N, (insert w S ∩ L i3).card ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨Sec, hSec⟩ : ∃ Sec : Finset (Fin N), ∀ i, i ∈ Sec ↔ (S ∩ L i).card = 2 :=
    ⟨Finset.univ.filter (fun i => (S ∩ L i).card = 2), by intro i; simp⟩
  have hsub : W ⊆ Sec.biUnion (fun i => L i \ L l) := by
    intro w hw
    obtain ⟨i, hi⟩ := hcon w hw
    have h2 := harc i
    have hwi : w ∈ L i := by
      by_contra hni
      rw [Finset.insert_inter_of_notMem hni] at hi
      omega
    have h1 : (insert w S ∩ L i).card ≤ (S ∩ L i).card + 1 := by
      rw [Finset.insert_inter_of_mem hwi]
      exact Finset.card_insert_le _ _
    rw [Finset.mem_biUnion]
    refine ⟨i, ?_, ?_⟩
    · rw [hSec]
      omega
    · rw [Finset.mem_sdiff]
      exact ⟨hwi, hW w hw⟩
  have hSl : (S ∩ L l).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter] at hx
    exact hS x hx.1 hx.2
  have hq : ∀ i ∈ Sec, (L i \ L l).card ≤ q := by
    intro i hi
    have hi2 := (hSec i).mp hi
    have hne : i ≠ l := by
      intro h
      rw [h] at hi2
      omega
    have h1 := Finset.card_sdiff_add_card_inter (L i) (L l)
    have h2 := hmeet i l hne
    have h3 := hcard i
    omega
  have hc1 : W.card ≤ Sec.card * q := by
    calc W.card ≤ (Sec.biUnion (fun i => L i \ L l)).card := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ Sec, (L i \ L l).card := Finset.card_biUnion_le
      _ ≤ Sec.card • q := Finset.sum_le_card_nsmul _ _ _ hq
      _ = Sec.card * q := smul_eq_mul _ _
  have hc2 : Sec.card ≤ (S.powersetCard 2).card := by
    apply Finset.card_le_card_of_injOn (fun i => S ∩ L i)
    · intro i hi
      have hi2 := (hSec i).mp hi
      exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hi2⟩
    · intro i hi j hj hij
      have hij' : S ∩ L i = S ∩ L j := hij
      have hi2 := (hSec i).mp hi
      obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hi2
      have ha : a ∈ S ∩ L i := by rw [hset]; simp
      have hb : b ∈ S ∩ L i := by rw [hset]; simp
      have ha' : a ∈ S ∩ L j := by rw [← hij']; exact ha
      have hb' : b ∈ S ∩ L j := by rw [← hij']; exact hb
      obtain ⟨k, _, hk⟩ := huniq a b hab
      exact (hk i ⟨(Finset.mem_inter.mp ha).2, (Finset.mem_inter.mp hb).2⟩).trans
        (hk j ⟨(Finset.mem_inter.mp ha').2, (Finset.mem_inter.mp hb').2⟩).symm
  have hc3 : (S.powersetCard 2).card = S.card.choose 2 := Finset.card_powersetCard 2 S
  have hc4 : 2 * S.card.choose 2 ≤ S.card * (S.card - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_le _ _
  have h5 : Sec.card * q ≤ S.card.choose 2 * q := Nat.mul_le_mul_right q (by omega)
  have h6 : 2 * S.card.choose 2 * q ≤ S.card * (S.card - 1) * q := Nat.mul_le_mul_right q hc4
  have h7 : 2 * S.card.choose 2 * q = 2 * (S.card.choose 2 * q) := Nat.mul_assoc _ _ _
  omega

end PEqualNP.Outside.L_meta_1628

theorem PEqualNP.Outside.L_meta_1628 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (l : Fin N) (T Y Z : Finset (Fin N)), 2 ≤ q → N = q * q + q + 1 → (∀ i0 : Fin N, (L i0).card = q + 1) → (∀ i1 j1 : Fin N, i1 ≠ j1 → (L i1 ∩ L j1).card = 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! k1 : Fin N, p1 ∈ L k1 ∧ p2 ∈ L k1) → (∀ t ∈ T, t ∉ L l) → (∀ i2 : Fin N, (T ∩ L i2).card ≤ 2) → (∀ y ∈ Y, y ∉ L l) → (∀ z ∈ Z, z ∉ L l) → (T.card + 1) * T.card * q < 2 * Y.card → (T.card + 1) * T.card * q < 2 * Z.card → ∃ u ∈ Y, ∃ v ∈ Z, ∀ i3 : Fin N, (insert v (insert u T) ∩ L i3).card ≤ 2 := by
  intro q N L l T Y Z _ _ hcard hmeet huniq hT harc hY hZ hYlt hZlt
  have h1 : T.card * (T.card - 1) * q < 2 * Y.card := by
    have h0 : T.card * (T.card - 1) * q ≤ (T.card + 1) * T.card * q := by
      apply Nat.mul_le_mul_right
      calc T.card * (T.card - 1) ≤ T.card * T.card := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ (T.card + 1) * T.card := Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  obtain ⟨u, hu, hua⟩ :=
    PEqualNP.Outside.L_meta_1628.ext_one q N L l T Y hcard hmeet huniq hT harc hY h1
  have hS : ∀ t ∈ insert u T, t ∉ L l := by
    intro t ht
    rcases Finset.mem_insert.mp ht with h | h
    · rw [h]
      exact hY u hu
    · exact hT t h
  have h2 : (insert u T).card * ((insert u T).card - 1) * q < 2 * Z.card := by
    have hle : (insert u T).card ≤ T.card + 1 := Finset.card_insert_le _ _
    have h0 : (insert u T).card * ((insert u T).card - 1) * q ≤ (T.card + 1) * T.card * q := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul hle (by omega)
    omega
  obtain ⟨v, hv, hva⟩ :=
    PEqualNP.Outside.L_meta_1628.ext_one q N L l (insert u T) Z hcard hmeet huniq hS hua hZ h2
  exact ⟨u, hu, v, hv, hva⟩
