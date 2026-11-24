import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1653 : ∀ (N L k : ℕ) (line : Fin L → Finset (Fin N)) (A : Finset (Fin N)) (B : Fin k → Finset (Fin N)),
  (∀ p r : Fin N, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
  (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
  (∀ i : Fin k, B i ⊆ A ∧ (B i).Nonempty) →
  (¬ ∃ T : Finset (Fin N), T ⊆ A ∧
      (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      ∀ i : Fin k, (T ∩ B i).Nonempty) →
  (∀ i0 : Fin k, ∃ T : Finset (Fin N), T ⊆ A ∧
      (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      ∀ i : Fin k, i ≠ i0 → (T ∩ B i).Nonempty) →
  ∀ i0 : Fin k, ∃ T : Finset (Fin N), T ⊆ A ∧ T.card + 1 ≤ k ∧ Disjoint T (B i0) ∧
      (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      ∀ u ∈ B i0, ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ u ∈ line j := by
  classical
  intro N L k line A B _ _ hB hnone hmin i0
  obtain ⟨T', hT'A, hT'arc, hT'hit⟩ := hmin i0
  obtain ⟨d, _⟩ := (hB i0).2
  have hex : ∀ i : Fin k, ∃ x : Fin N, i ≠ i0 → x ∈ T' ∩ B i := by
    intro i
    by_cases hi : i = i0
    · exact ⟨d, fun h => absurd hi h⟩
    · obtain ⟨x, hx⟩ := hT'hit i hi
      exact ⟨x, fun _ => hx⟩
  choose t ht using hex
  let T : Finset (Fin N) := (Finset.univ.erase i0).image t
  have hTsub : T ⊆ T' := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact (Finset.mem_inter.1 (ht i (Finset.mem_erase.1 hi).1)).1
  have hTarc : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c →
      ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j :=
    fun a ha b hb c hc => hT'arc a (hTsub ha) b (hTsub hb) c (hTsub hc)
  have hThit : ∀ i : Fin k, i ≠ i0 → (T ∩ B i).Nonempty := by
    intro i hi
    refine ⟨t i, Finset.mem_inter.2 ⟨?_, (Finset.mem_inter.1 (ht i hi)).2⟩⟩
    exact Finset.mem_image.2 ⟨i, Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩, rfl⟩
  have hcard : T.card + 1 ≤ k := by
    have h1 : T.card ≤ (Finset.univ.erase i0).card := Finset.card_image_le
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
    have := i0.pos
    omega
  have hdisj : Disjoint T (B i0) := by
    rw [Finset.disjoint_left]
    intro x hxT hxB
    apply hnone
    refine ⟨T, hTsub.trans hT'A, hTarc, fun i => ?_⟩
    by_cases hi : i = i0
    · subst hi; exact ⟨x, Finset.mem_inter.2 ⟨hxT, hxB⟩⟩
    · exact hThit i hi
  refine ⟨T, hTsub.trans hT'A, hcard, hdisj, hTarc, ?_⟩
  intro u hu
  by_contra hcon
  push_neg at hcon
  apply hnone
  refine ⟨insert u T, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | h
    · exact (hB i0).1 hu
    · exact (hTsub.trans hT'A) h
  · intro a ha b hb c hc hab hac hbc
    rintro ⟨j, haj, hbj, hcj⟩
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · rcases Finset.mem_insert.1 hb with rfl | hb'
      · exact hab rfl
      · rcases Finset.mem_insert.1 hc with rfl | hc'
        · exact hac rfl
        · exact hcon b hb' c hc' hbc j hbj hcj haj
    · rcases Finset.mem_insert.1 hb with rfl | hb'
      · rcases Finset.mem_insert.1 hc with rfl | hc'
        · exact hbc rfl
        · exact hcon a ha' c hc' hac j haj hcj hbj
      · rcases Finset.mem_insert.1 hc with rfl | hc'
        · exact hcon a ha' b hb' hab j haj hbj hcj
        · exact hTarc a ha' b hb' c hc' hab hac hbc ⟨j, haj, hbj, hcj⟩
  · intro i
    by_cases hi : i = i0
    · subst hi
      exact ⟨u, Finset.mem_inter.2 ⟨Finset.mem_insert_self _ _, hu⟩⟩
    · obtain ⟨x, hx⟩ := hThit i hi
      rw [Finset.mem_inter] at hx
      exact ⟨x, Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem hx.1, hx.2⟩⟩
