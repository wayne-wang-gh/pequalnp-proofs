import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_164 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (t t1 t2 : ℕ), (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S ∨ b ∈ S) ∧ S.card = t1) → (∀ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ S ∨ b ∈ S) → t1 ≤ S.card) → (∃ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b → a ∈ S ∨ b ∈ S) ∧ S.card = t2) → (∀ S : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b → a ∈ S ∨ b ∈ S) → t2 ≤ S.card) → t = min (t1 + 1) (t2 + (Finset.univ.filter (fun u : Fin n => G.Adj v u)).card) := by
  intro n G _ v t t1 t2 ⟨A, hA, hAc⟩ hAmin ⟨B, hB, hBc⟩ hBmin ⟨C, hC, hCc⟩ hCmin
  set N : Finset (Fin n) := Finset.univ.filter (fun u : Fin n => G.Adj v u) with hN
  have hmem : ∀ u, u ∈ N ↔ G.Adj v u := by
    intro u
    simp [hN]
  apply le_antisymm
  · apply le_min
    · have hcov : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (insert v B) := by
        intro a b hab
        by_cases ha : a = v
        · left
          simp [ha]
        · by_cases hb : b = v
          · right
            simp [hb]
          · rcases hB a b hab ha hb with h | h
            · left
              exact Finset.mem_insert_of_mem h
            · right
              exact Finset.mem_insert_of_mem h
      have h1 := hAmin _ hcov
      have h2 := Finset.card_insert_le v B
      omega
    · have hcov : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (C ∪ N) := by
        intro a b hab
        by_cases ha : a = v
        · right
          apply Finset.mem_union_right
          rw [hmem]
          rw [ha] at hab
          exact hab
        · by_cases hb : b = v
          · left
            apply Finset.mem_union_right
            rw [hmem]
            rw [hb] at hab
            exact hab.symm
          · by_cases hva : G.Adj v a
            · left
              exact Finset.mem_union_right _ ((hmem a).2 hva)
            · by_cases hvb : G.Adj v b
              · right
                exact Finset.mem_union_right _ ((hmem b).2 hvb)
              · rcases hC a b hab ha hb hva hvb with h | h
                · left
                  exact Finset.mem_union_left _ h
                · right
                  exact Finset.mem_union_left _ h
      have h1 := hAmin _ hcov
      have h2 := Finset.card_union_le C N
      omega
  · by_cases hv : v ∈ A
    · apply le_trans (min_le_left _ _)
      have hcov : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → a ∈ A.erase v ∨ b ∈ A.erase v := by
        intro a b hab ha hb
        rcases hA a b hab with h | h
        · left
          exact Finset.mem_erase.2 ⟨ha, h⟩
        · right
          exact Finset.mem_erase.2 ⟨hb, h⟩
      have h1 := hBmin _ hcov
      have h2 := Finset.card_erase_of_mem hv
      have h3 : 0 < A.card := Finset.card_pos.2 ⟨v, hv⟩
      omega
    · apply le_trans (min_le_right _ _)
      have hsub : N ⊆ A := by
        intro u hu
        have huv : G.Adj v u := (hmem u).1 hu
        rcases hA v u huv with h | h
        · exact absurd h hv
        · exact h
      have hcov : ∀ a b : Fin n, G.Adj a b → a ≠ v → b ≠ v → ¬ G.Adj v a → ¬ G.Adj v b → a ∈ A \ N ∨ b ∈ A \ N := by
        intro a b hab ha hb hva hvb
        rcases hA a b hab with h | h
        · left
          exact Finset.mem_sdiff.2 ⟨h, fun hn => hva ((hmem a).1 hn)⟩
        · right
          exact Finset.mem_sdiff.2 ⟨h, fun hn => hvb ((hmem b).1 hn)⟩
      have h1 := hCmin _ hcov
      have h2 := Finset.card_sdiff_add_card_eq_card hsub
      omega
