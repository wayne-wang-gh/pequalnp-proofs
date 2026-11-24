import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1633 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ t u : Fin N, t ≠ i0 → u ≠ i0 → t ≠ u →
      ((∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) ↔ ((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L u ∧ p0 ∉ L u)) ∨ ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L u ∧ p1 ∉ L u))) := by
  classical
  intro q N L i0 p0 p1 hq _ hcard hmeet _ h01 h0 h1 T hT t u ht hu htu
  have nb : ∀ s : Fin N, s ≠ i0 → ¬ (p0 ∈ L s ∧ p1 ∈ L s) := by
    rintro s hs ⟨a, b⟩
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L s ∩ L i0 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.2 ⟨a, h0⟩
      · exact Finset.mem_inter.2 ⟨b, h1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair h01, hmeet s i0 hs] at this
    omega
  have pick : ∀ a b : Fin N, a ≠ b → ∀ z : Fin N, ∃ p ∈ L a \ L b, p ≠ z := by
    intro a b hab z
    have h2 := Finset.card_sdiff_add_card_inter (L a) (L b)
    rw [hcard, hmeet a b hab] at h2
    exact Finset.exists_mem_ne (by omega) z
  have point : ∀ a b : Fin N, a ≠ i0 → a ≠ b →
      ((∃ p ∈ L a \ L b, ∃ v ∈ L b, T a p v = true) ↔
        (p0 ∉ L a ∧ p0 ∈ L b) ∨ (p0 ∈ L a ∧ p1 ∈ L b)) := by
    intro a b ha hab
    constructor
    · rintro ⟨p, hp, v, hv, hTv⟩
      rw [Finset.mem_sdiff] at hp
      rcases (hT a p v).1 hTv with h | ⟨h1', _, h3⟩ | ⟨h1', _, _, h4⟩ | ⟨h1', h2', _⟩
      · exact absurd (h ▸ hv) hp.2
      · exact Or.inl ⟨h1', h3 ▸ hv⟩
      · exact Or.inr ⟨h1', h4 ▸ hv⟩
      · exact absurd ⟨h1', h2'⟩ (nb a ha)
    · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
      · obtain ⟨p, hp, hpne⟩ := pick a b hab p1
        exact ⟨p, hp, p0, h2', (hT a p p0).2 (Or.inr (Or.inl ⟨h1', hpne, rfl⟩))⟩
      · obtain ⟨p, hp, hpne⟩ := pick a b hab p0
        have hp1a : p1 ∉ L a := fun h => nb a ha ⟨h1', h⟩
        exact ⟨p, hp, p1, h2', (hT a p p1).2 (Or.inr (Or.inr (Or.inl ⟨h1', hp1a, hpne, rfl⟩)))⟩
  rw [point t u ht htu, point u t hu (Ne.symm htu)]
  have nt := nb t ht
  have nu := nb u hu
  tauto
