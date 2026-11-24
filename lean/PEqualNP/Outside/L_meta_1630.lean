import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1630_aux

theorem same {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 t p0 p1 : Fin N)
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (h01 : p0 ≠ p1)
    (h0 : p0 ∈ L i0) (h1 : p1 ∈ L i0) (h0t : p0 ∈ L t) (h1t : p1 ∈ L t) : t = i0 := by
  by_contra h
  have hc := hinter i0 t (Ne.symm h)
  have hs : ({p0, p1} : Finset (Fin N)) ⊆ L i0 ∩ L t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp_all
  have := Finset.card_le_card hs
  rw [Finset.card_pair h01] at this
  omega

end PEqualNP.Outside.L_meta_1630_aux

open PEqualNP.Outside.L_meta_1630_aux in
theorem PEqualNP.Outside.L_meta_1630 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    (∀ x y : Fin N → Bool, (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) → (∀ v : Fin N, x v = true → y v = true) → (y p0 = true ∨ y p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → y u = true)) ∧
    (∀ t : Fin N, ((fun v : Fin N => decide (v ∉ L t)) p0 = true ∨ (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true)) ∧
    (∀ t : Fin N, ∀ p ∈ L t, (T t p p0 = true ∨ T t p p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → T t p u = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, decide (v ∉ L t) = true) = false ∧ ∀ p ∈ L t, decide (∃ v ∈ L t, T t p v = true) = true) := by
  intro q N L i0 p0 p1 hq hN hcard hinter hpts h01 h0 h1 T hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with hx | hx | hx
    · exact Or.inl (hxy _ hx)
    · exact Or.inr (Or.inl (hxy _ hx))
    · exact Or.inr (Or.inr fun u hu => hxy u (hx u hu))
  · intro t
    by_cases a : p0 ∈ L t
    · by_cases b : p1 ∈ L t
      · have := same L i0 t p0 p1 hinter h01 h0 h1 a b
        subst this
        right; right
        intro u hu
        simp [hu]
      · right; left
        simp [b]
    · left
      simp [a]
  · intro t p hp
    by_cases a : p0 ∈ L t
    · by_cases b : p1 ∈ L t
      · by_cases c : p = p0
        · left
          exact (hT t p p0).mpr (Or.inl c.symm)
        · by_cases d : p = p1
          · right; left
            exact (hT t p p1).mpr (Or.inl d.symm)
          · have := same L i0 t p0 p1 hinter h01 h0 h1 a b
            subst this
            right; right
            intro u hu
            exact (hT t p u).mpr (Or.inr (Or.inr (Or.inr ⟨a, b, c, d, hu⟩)))
      · by_cases c : p = p0
        · left
          exact (hT t p p0).mpr (Or.inl c.symm)
        · right; left
          exact (hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨a, b, c, rfl⟩)))
    · by_cases d : p = p1
      · right; left
        exact (hT t p p1).mpr (Or.inl d.symm)
      · left
        exact (hT t p p0).mpr (Or.inr (Or.inl ⟨a, d, rfl⟩))
  · intro t
    refine ⟨by simp, fun p hp => ?_⟩
    simp only [decide_eq_true_eq]
    exact ⟨p, hp, (hT t p p).mpr (Or.inl rfl)⟩
