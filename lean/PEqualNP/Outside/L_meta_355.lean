import Mathlib
import PEqualNP.Defs

-- Original proof by AIOvernight in PR 232, accepted by the checker before the fleet
-- paused this step. Resubmitted unchanged now that the step is open again.
theorem PEqualNP.Outside.L_meta_355 : ∀ E : List (Fin 4 × Fin 4), E = [(0, 1), (1, 2), (2, 3)] → ∀ (PV RV : Fin 2 → Finset (Fin 4)) (PG RG : Fin 2 → Finset (Fin 2)) (OV : Finset (Fin 4)) (OG : Finset (Fin 2)) (val : Finset (Fin 4) → Fin 2 → Prop), (∀ i : Fin 2, ∀ j ∈ PG i, j < i) → (∀ i : Fin 2, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin 4)) (i : Fin 2), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin 4), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ e ∈ E, e.1 ∈ X ∧ e.2 ∈ X) → ∀ (g H : Fin 2) (u : Fin 4), g ≠ H → u ∈ PV g → u ∉ RV g → (∀ i : Fin 2, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) → ∀ I : Finset (Fin 4), (∀ e ∈ E, ¬ (e.1 ∈ I ∧ e.2 ∈ I)) → u ∉ I → (∃ w ∈ I, (u, w) ∈ E ∨ (w, u) ∈ E) → val I H → (∀ v ∈ PV g, v ∉ I) ∧ (∀ j ∈ PG g, ¬ val I j) ∧ H ∉ PG g := by
  intro E hE PV RV PG RG OV OG val hPG hRG hval hout g H u hgH huP huR hu I hI huI hw hH
  have hnotP : ¬ ((∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j) := by
    intro hP
    have D : ∀ N : ℕ, ∀ i : Fin 2, i.val = N → (val (insert u I) i ↔ val I i) := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ih =>
        intro i hi
        have IH : ∀ j : Fin 2, j < i → (val (insert u I) j ↔ val I j) := fun j hj =>
          ih j.val (by rw [← hi]; exact hj) j rfl
        rw [hval (insert u I) i, hval I i]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hiH : i = H
          · rw [hiH]
            exact (hval I H).1 hH
          · by_cases hig : i = g
            · rw [hig] at h2 IH ⊢
              refine ⟨hP, ?_⟩
              rcases h2 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
              · rcases Finset.mem_insert.1 hvI with hvu | hvI
                · rw [hvu] at hv
                  exact absurd hv huR
                · exact Or.inl ⟨v, hv, hvI⟩
              · exact Or.inr ⟨j, hj, (IH j (hRG g j hj)).1 hjv⟩
            · have hnoP : u ∉ PV i := fun h => (hu i (Or.inl h)).elim hig hiH
              have hnoR : u ∉ RV i := fun h => (hu i (Or.inr h)).elim hig hiH
              refine ⟨?_, ?_⟩
              · rcases h1 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
                · rcases Finset.mem_insert.1 hvI with hvu | hvI
                  · rw [hvu] at hv
                    exact absurd hv hnoP
                  · exact Or.inl ⟨v, hv, hvI⟩
                · exact Or.inr ⟨j, hj, (IH j (hPG i j hj)).1 hjv⟩
              · rcases h2 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
                · rcases Finset.mem_insert.1 hvI with hvu | hvI
                  · rw [hvu] at hv
                    exact absurd hv hnoR
                  · exact Or.inl ⟨v, hv, hvI⟩
                · exact Or.inr ⟨j, hj, (IH j (hRG i j hj)).1 hjv⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · rcases h1 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
            · exact Or.inl ⟨v, hv, Finset.mem_insert_of_mem hvI⟩
            · exact Or.inr ⟨j, hj, (IH j (hPG i j hj)).2 hjv⟩
          · rcases h2 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
            · exact Or.inl ⟨v, hv, Finset.mem_insert_of_mem hvI⟩
            · exact Or.inr ⟨j, hj, (IH j (hRG i j hj)).2 hjv⟩
    have hloop : ∀ e ∈ E, e.1 ≠ e.2 := by
      rw [hE]
      decide
    have huOV : u ∉ OV := by
      intro h
      obtain ⟨e, he, h1, h2⟩ := (hout {u}).1 (Or.inl ⟨u, h, Finset.mem_singleton_self u⟩)
      rw [Finset.mem_singleton] at h1 h2
      exact hloop e he (h1.trans h2.symm)
    obtain ⟨w, hwI, huw⟩ := hw
    have h1 : (∃ v ∈ OV, v ∈ insert u I) ∨ ∃ j ∈ OG, val (insert u I) j := by
      rcases huw with huw | huw
      · exact (hout (insert u I)).2 ⟨(u, w), huw, Finset.mem_insert_self u I,
          Finset.mem_insert_of_mem hwI⟩
      · exact (hout (insert u I)).2 ⟨(w, u), huw, Finset.mem_insert_of_mem hwI,
          Finset.mem_insert_self u I⟩
    have h2 : (∃ v ∈ OV, v ∈ I) ∨ ∃ j ∈ OG, val I j := by
      rcases h1 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
      · rcases Finset.mem_insert.1 hvI with hvu | hvI
        · rw [hvu] at hv
          exact absurd hv huOV
        · exact Or.inl ⟨v, hv, hvI⟩
      · exact Or.inr ⟨j, hj, (D j.val j rfl).1 hjv⟩
    obtain ⟨e, he, he1, he2⟩ := (hout I).1 h2
    exact hI e he ⟨he1, he2⟩
  exact ⟨fun v hv hvI => hnotP (Or.inl ⟨v, hv, hvI⟩),
    fun j hj hjv => hnotP (Or.inr ⟨j, hj, hjv⟩),
    fun hmem => hnotP (Or.inr ⟨H, hmem, hH⟩)⟩
