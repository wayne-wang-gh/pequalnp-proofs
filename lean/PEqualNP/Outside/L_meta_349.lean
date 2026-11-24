import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_349_aux

lemma not_mem_OV {n b : ℕ} (G : SimpleGraph (Fin n))
    (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop)
    (hout : ∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c)
    (u : Fin n) : u ∉ OV := by
  intro hu
  have h1 : (∃ v ∈ OV, v ∈ ({u} : Finset (Fin n))) ∨ ∃ j ∈ OG, val {u} j := by
    left
    exact ⟨u, hu, Finset.mem_singleton_self u⟩
  have h2 := (hout {u}).mp h1
  obtain ⟨a, ha, c, hc, hadj⟩ := h2
  rw [Finset.mem_singleton] at ha hc
  subst ha hc
  exact G.loopless.irrefl _ hadj

end PEqualNP.Outside.L_meta_349_aux

open PEqualNP.Outside.L_meta_349_aux in
theorem PEqualNP.Outside.L_meta_349 : ∀ (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop), (∀ i : Fin b, ∀ j ∈ PG i, j < i) → (∀ i : Fin b, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) → ∀ (g H : Fin b) (u : Fin n), g ≠ H → u ∈ PV g → u ∉ RV g → (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) → ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → u ∉ I → (∃ w ∈ I, G.Adj u w) → val I H → (∀ v ∈ PV g, v ∉ I) ∧ (∀ j ∈ PG g, ¬ val I j) ∧ H ∉ PG g := by
  intro n b G PV RV PG RG OV OG val hPG hRG hval hout g H u hgH huPV huRV huniq I hI huI hw hvalH
  have hnot_left : ¬ ((∃ v ∈ PV g, v ∈ I) ∨ (∃ j ∈ PG g, val I j) ∨ H ∈ PG g) := by
    intro hcontr
    have hleft_g : (∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j := by
      rcases hcontr with ⟨v, hv, hvI⟩ | ⟨j, hj, hjI⟩ | hHPG
      · exact Or.inl ⟨v, hv, hvI⟩
      · exact Or.inr ⟨j, hj, hjI⟩
      · exact Or.inr ⟨H, hHPG, hvalH⟩
    have hval_rev : ∀ k : ℕ, ∀ i : Fin b, i.val = k → val (insert u I) i → val I i := by
      intro k
      induction' k using Nat.strong_induction_on with k ih
      intro i hik hvi
      obtain ⟨hleft, hright⟩ := (hval (insert u I) i).mp hvi
      have hleft_I : (∃ v ∈ PV i, v ∈ I) ∨ ∃ j ∈ PG i, val I j := by
        by_cases hig : i = g
        · rw [hig]; exact hleft_g
        · by_cases hiH : i = H
          · rw [hiH]; exact ((hval I H).mp hvalH).1
          · have hu_not_PV : u ∉ PV i := by
              intro hu
              cases huniq i (Or.inl hu) with
              | inl heq => exact hig heq
              | inr heq => exact hiH heq
            rcases hleft with ⟨v, hv, hvX⟩ | ⟨j, hj, hjX⟩
            · rw [Finset.mem_insert] at hvX
              cases hvX with
              | inl hvu =>
                rw [hvu] at hv
                exact (hu_not_PV hv).elim
              | inr hvI =>
                exact Or.inl ⟨v, hv, hvI⟩
            · have hjlt : j.val < k := by rw [← hik]; exact hPG i j hj
              exact Or.inr ⟨j, hj, ih j.val hjlt j rfl hjX⟩
      have hright_I : (∃ v ∈ RV i, v ∈ I) ∨ ∃ j ∈ RG i, val I j := by
        by_cases hiH : i = H
        · rw [hiH]; exact ((hval I H).mp hvalH).2
        · have hu_not_RV : u ∉ RV i := by
            intro hu
            cases huniq i (Or.inr hu) with
            | inl heq =>
              rw [heq] at hu
              exact huRV hu
            | inr heq => exact hiH heq
          rcases hright with ⟨v, hv, hvX⟩ | ⟨j, hj, hjX⟩
          · rw [Finset.mem_insert] at hvX
            cases hvX with
            | inl hvu =>
              rw [hvu] at hv
              exact (hu_not_RV hv).elim
            | inr hvI =>
              exact Or.inl ⟨v, hv, hvI⟩
          · have hjlt : j.val < k := by rw [← hik]; exact hRG i j hj
            exact Or.inr ⟨j, hj, ih j.val hjlt j rfl hjX⟩
      exact (hval I i).mpr ⟨hleft_I, hright_I⟩
    have hval_rev_all : ∀ i : Fin b, val (insert u I) i → val I i :=
      fun i => hval_rev i.val i rfl
    obtain ⟨w, hwI, hadj⟩ := hw
    have hedge : ∃ a ∈ insert u I, ∃ c ∈ insert u I, G.Adj a c := by
      refine ⟨u, Finset.mem_insert_self u I, w, Finset.mem_insert_of_mem hwI, hadj⟩
    have hout_X1 := (hout (insert u I)).mpr hedge
    rcases hout_X1 with ⟨v, hvOV, hvX1⟩ | ⟨j, hjOG, hjvalX1⟩
    · rw [Finset.mem_insert] at hvX1
      cases hvX1 with
      | inl hvu =>
        rw [hvu] at hvOV
        exact not_mem_OV G OV OG val hout u hvOV
      | inr hvI =>
        have hI_edge := (hout I).mp (Or.inl ⟨v, hvOV, hvI⟩)
        obtain ⟨a, ha, c, hc, hadj'⟩ := hI_edge
        exact hI a ha c hc hadj'
    · have hjvalI := hval_rev_all j hjvalX1
      have hI_edge := (hout I).mp (Or.inr ⟨j, hjOG, hjvalI⟩)
      obtain ⟨a, ha, c, hc, hadj'⟩ := hI_edge
      exact hI a ha c hc hadj'
  have h1 : ∀ v ∈ PV g, v ∉ I := fun v hv hvI => hnot_left (Or.inl ⟨v, hv, hvI⟩)
  have h2 : ∀ j ∈ PG g, ¬ val I j := fun j hj hjval => hnot_left (Or.inr (Or.inl ⟨j, hj, hjval⟩))
  have h3 : H ∉ PG g := fun hHPG => hnot_left (Or.inr (Or.inr hHPG))
  exact ⟨h1, h2, h3⟩
