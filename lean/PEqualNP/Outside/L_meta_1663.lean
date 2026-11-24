import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1663

-- Two distinct lines have at most one common point.
theorem meet_unique {N : ℕ} (L : Fin N → Finset (Fin N))
    (hmeet : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    {i j : Fin N} (hij : i ≠ j) {a b : Fin N}
    (hai : a ∈ L i) (haj : a ∈ L j) (hbi : b ∈ L i) (hbj : b ∈ L j) : a = b := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hmeet i j hij)
  have ha : a ∈ L i ∩ L j := Finset.mem_inter.mpr ⟨hai, haj⟩
  have hb : b ∈ L i ∩ L j := Finset.mem_inter.mpr ⟨hbi, hbj⟩
  rw [hc, Finset.mem_singleton] at ha hb
  rw [ha, hb]

end PEqualNP.Outside.L_meta_1663

theorem PEqualNP.Outside.L_meta_1663 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ w W : Fin N, (w = s ∧ W = Ms ∨ w = p ∧ W = Mp) → ∀ P ∈ L W,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L Mv)))) ∧
    (∀ w S1 : Fin N, (w = s ∨ w = p) → w ∈ L S1 → (∀ u : Fin N, (u = v ∨ u = s ∨ u = p) → u ∈ L S1 → u = w) → ∀ P ∈ L Mv,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S)) ∧ (P ∈ L S1 ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S1)))) := by
  intro q N L v s p Mv Ms Mp _ _ _ hmeet hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have uniq := @PEqualNP.Outside.L_meta_1663.meet_unique N L hmeet
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hvs : v ≠ s := by
    intro h
    subst h
    exact hnc Ms ⟨hvMs, hvMs, hpMs⟩
  have hvp : v ≠ p := by
    intro h
    subst h
    exact hnc Mp ⟨hvMp, hsMp, hvMp⟩
  have hsp : s ≠ p := by
    intro h
    subst h
    exact hnc Ms ⟨hvMs, hpMs, hpMs⟩
  have hSMs : S ≠ Ms := by
    intro h
    subst h
    exact hpS hpMs
  have hSMp : S ≠ Mp := by
    intro h
    subst h
    exact hsS hsMp
  refine ⟨?_, ?_⟩
  · intro w W hwW P hP hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases hwW with ⟨hw, hW⟩ | ⟨hw, hW⟩
    · rw [hW] at hP
      rw [hw] at h1
      have hPS : P ∈ L S := h1.resolve_right (fun h => hsS h.2.2.2)
      have hPv : P = v := uniq hSMs hPS hP hvS hvMs
      rw [hPv] at h2
      rcases h2 with h | h
      · exact hvMv h
      · exact h.1 rfl
    · rw [hW] at hP
      rw [hw] at h1
      have hPS : P ∈ L S := h1.resolve_right (fun h => hpS h.2.2.2)
      have hPv : P = v := uniq hSMp hPS hP hvS hvMp
      rw [hPv] at h2
      rcases h2 with h | h
      · exact hvMv h
      · exact h.1 rfl
  · intro w S1 hw hwS1 honly P hP hcon
    obtain ⟨h1, h2⟩ := hcon
    have hvw : v ≠ w := by
      rcases hw with hw | hw
      · rw [hw]; exact hvs
      · rw [hw]; exact hvp
    have hvS1 : v ∉ L S1 := fun h => hvw (honly v (Or.inl rfl) h)
    have hPS1 : P ∈ L S1 := h2.resolve_right (fun h => hvS1 h.2.2.2)
    rcases hw with hw | hw
    · have hpS1 : p ∉ L S1 := by
        intro h
        have := honly p (Or.inr (Or.inr rfl)) h
        rw [hw] at this
        exact hsp this.symm
      have hS1Mv : S1 ≠ Mv := by
        intro h
        rw [h] at hpS1
        exact hpS1 hpMv
      have hsS1 : s ∈ L S1 := hw ▸ hwS1
      have hPs : P = s := uniq hS1Mv hPS1 hP hsS1 hsMv
      rw [hPs] at h1
      rcases h1 with h | h
      · exact hsS h
      · exact h.2.1 rfl
    · have hsS1 : s ∉ L S1 := by
        intro h
        have := honly s (Or.inr (Or.inl rfl)) h
        rw [hw] at this
        exact hsp this
      have hS1Mv : S1 ≠ Mv := by
        intro h
        rw [h] at hsS1
        exact hsS1 hsMv
      have hpS1 : p ∈ L S1 := hw ▸ hwS1
      have hPp : P = p := uniq hS1Mv hPS1 hP hpS1 hpMv
      rw [hPp] at h1
      rcases h1 with h | h
      · exact hpS h
      · exact h.2.2.1 rfl
