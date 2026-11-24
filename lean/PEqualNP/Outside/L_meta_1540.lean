import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1540 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)) (w : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = q → w ∈ L i0 → w ∉ T0 →
    (∀ x : Fin N → Bool, ((∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) ∧ ¬ ∃ v ∈ T0, x v = true) ↔
      (x = (fun v : Fin N => decide (v ∉ L i0)) ∨ x = (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)))) ∧
    (∀ s : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L s)) v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, (fun v : Fin N => decide (v ∉ L s)) v = false → v ∈ L s) ∧ (s ≠ i0 → ∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L s)) v = true)) ∧
    (∀ x : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) ↔ ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true)) ∧
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, y v = false → v ∈ L s)) := by
  classical
  intro q N L i0 T0 w hq _ hcard hmeet _ hT0 hT0c hw hwT
  have key : ∀ s : Fin N, (∀ v ∈ T0, v ∈ L s) → s = i0 := by
    intro s hs
    by_contra hne
    have hsub : T0 ⊆ L s ∩ L i0 := fun v hv => Finset.mem_inter.2 ⟨hs v hv, hT0 hv⟩
    have := Finset.card_le_card hsub
    rw [hT0c, hmeet s i0 hne] at this
    omega
  have hL0 : ∀ v, v ∈ L i0 → v ∈ T0 ∨ v = w := by
    have he : insert w T0 = L i0 := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        rcases Finset.mem_insert.1 hv with rfl | h
        · exact hw
        · exact hT0 h
      · rw [Finset.card_insert_of_notMem hwT, hT0c, hcard]
    intro v hv
    rw [← he] at hv
    rcases Finset.mem_insert.1 hv with h | h
    · exact Or.inr h
    · exact Or.inl h
  have allfalse : ∀ x : Fin N → Bool, (¬ ∃ v ∈ T0, x v = true) → ∀ v ∈ T0, x v = false := by
    intro x h v hv
    by_contra hne
    exact h ⟨v, hv, by simpa using hne⟩
  have line0 : ∀ x : Fin N → Bool, (∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) →
      (¬ ∃ v ∈ T0, x v = true) → ∀ v : Fin N, x v = false → v ∈ L i0 := by
    rintro x ⟨s, hs⟩ hA
    have : s = i0 := key s (fun v hv => hs v (allfalse x hA v hv))
    rw [← this]; exact hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨hS, hA⟩
      have h0 := line0 x hS hA
      have hT := allfalse x hA
      have hout : ∀ v, v ∉ L i0 → x v = true := by
        intro v hv
        by_contra hne
        exact hv (h0 v (by simpa using hne))
      cases hxw : x w
      · left
        funext v
        by_cases hv : v ∈ L i0
        · rcases hL0 v hv with h | h
          · simp [hv, hT v h]
          · subst h; simp [hv, hxw]
        · simp [hv, hout v hv]
      · right
        funext v
        by_cases hv : v ∈ L i0
        · rcases hL0 v hv with h | h
          · have hvw : v ≠ w := fun e => hwT (e ▸ h)
            simp [hv, hvw, hT v h]
          · subst h; simp [hxw]
        · simp [hv, hout v hv]
    · rintro (h | h)
      · subst h
        refine ⟨⟨i0, fun v hv => by simpa using hv⟩, ?_⟩
        rintro ⟨v, hv, h⟩
        simp [hT0 hv] at h
      · subst h
        refine ⟨⟨i0, fun v hv => ?_⟩, ?_⟩
        · have := of_decide_eq_false hv
          push_neg at this
          exact this.1
        · rintro ⟨v, hv, h⟩
          have hvw : v ≠ w := fun e => hwT (e ▸ hv)
          simp [hT0 hv, hvw] at h
  · intro s
    refine ⟨Or.inr ⟨s, fun v hv => by simpa using hv⟩, fun hs => ?_⟩
    by_contra hcon
    push_neg at hcon
    apply hs
    apply key s
    intro v hv
    have := hcon v hv
    simpa using this
  · intro x
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hA : ∃ v ∈ T0, x v = true
        · exact Or.inl hA
        · right
          intro v hv
          by_contra hne
          exact hv (line0 x h hA v (by simpa using hne))
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨i0, fun v hv => ?_⟩
        by_contra hne
        rw [h v hne] at hv
        exact absurd hv (by simp)
  · intro x y h hxy
    rcases h with ⟨v, hv, h⟩ | ⟨s, h⟩
    · exact Or.inl ⟨v, hv, hxy v h⟩
    · refine Or.inr ⟨s, fun v hv => h v ?_⟩
      by_contra hne
      have : x v = true := by simpa using hne
      rw [hxy v this] at hv
      exact absurd hv (by simp)
