import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1582_aux

theorem key {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 t : Fin N) (T0 : Finset (Fin N))
    (hI : (L i0 ∩ L t).card = 1) (hT : T0 ⊆ L i0) :
    T0.card - 1 ≤ (T0.filter (fun x => x ∉ L t)).card := by
  have h1 : (T0.filter (fun x => x ∈ L t)).card ≤ 1 := by
    rw [← hI]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact Finset.mem_inter.mpr ⟨hT hx.1, hx.2⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := T0) (fun x => x ∈ L t)
  omega

theorem ex {N : ℕ} (L : Fin N → Finset (Fin N)) (t : Fin N) (T0 : Finset (Fin N))
    (h : 2 ≤ (T0.filter (fun x => x ∉ L t)).card) : ∃ v ∈ T0, v ∉ L t := by
  obtain ⟨v, hv⟩ : (T0.filter (fun x => x ∉ L t)).Nonempty := by
    rw [← Finset.card_pos]; omega
  simp only [Finset.mem_filter] at hv
  exact ⟨v, hv.1, hv.2⟩

end PEqualNP.Outside.L_meta_1582_aux

open PEqualNP.Outside.L_meta_1582_aux in
theorem PEqualNP.Outside.L_meta_1582 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) := by
  intro q m N L i0 T0 hq hm3 hmq hN hcard hinter hpts hT hm
  have hc : ∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card := by
    intro t ht
    have := key L i0 t T0 (hinter i0 t (Ne.symm ht)) hT
    rw [hm] at this
    exact this
  have hex : ∀ t : Fin N, t ≠ i0 → ∃ v ∈ T0, v ∉ L t := fun t ht => ex L t T0 (by have := hc t ht; omega)
  have hp : ∀ t p : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) := by
    intro t p
    by_cases h : t = i0
    · subst h
      right
      intro v hv
      simp [hv]
    · left
      obtain ⟨v, hv, hv'⟩ := hex t h
      exact ⟨v, hv, by simp [hv']⟩
  refine ⟨?_, ?_, hc, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with ⟨v, hv, hxv⟩ | hx
    · exact Or.inl ⟨v, hv, hxy v hxv⟩
    · exact Or.inr fun v hv => hxy v (hx v hv)
  · intro t
    by_cases h : t = i0
    · subst h
      right
      intro v hv
      simp [hv]
    · left
      obtain ⟨v, hv, hv'⟩ := hex t h
      exact ⟨v, hv, by simp [hv']⟩
  · intro x hx
    exact Or.inl ⟨x, hx, by simp⟩
  · right
    intro v hv
    simp [hv]
  · intro r _
    right
    intro v hv
    simp [hv]
  · intro t
    refine ⟨by simp, fun p hp' => ⟨hp t p, ?_⟩⟩
    simp only [decide_eq_true_eq]
    exact ⟨p, hp', by simp⟩
