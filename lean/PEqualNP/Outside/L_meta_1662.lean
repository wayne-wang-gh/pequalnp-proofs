import Mathlib

namespace PEqualNP.Outside.L_meta_1662
lemma unique {α : Type*} [DecidableEq α] {A B : Finset α} {x y : α}
    (h : (A ∩ B).card = 1) (hx : x ∈ A) (hx' : x ∈ B) (hy : y ∈ A) (hy' : y ∈ B) : x = y := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h
  have h1 : x ∈ ({z} : Finset α) := hz ▸ Finset.mem_inter.mpr ⟨hx, hx'⟩
  have h2 : y ∈ ({z} : Finset α) := hz ▸ Finset.mem_inter.mpr ⟨hy, hy'⟩
  exact (Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm
end PEqualNP.Outside.L_meta_1662

theorem PEqualNP.Outside.L_meta_1662 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ Q ∈ L S, Q ≠ v → Q ∉ L Mp ∧ p ∉ L Mp ∧
      ∀ S2 : Fin N, S2 ≠ S → v ∈ L S2 → s ∉ L S2 → p ∉ L S2 → Q ∉ L S2 ∧ p ∉ L S2) ∧
    (∀ S2 : Fin N, S2 ≠ S → v ∈ L S2 → s ∉ L S2 → p ∉ L S2 → ∀ B : Fin N, (B = s ∨ B = p) → ∀ P ∈ L S2,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ B ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ B ∈ L Mv)))) ∧
    (∀ K : Fin N, v ∉ L K → s ∉ L K → p ∉ L K → ∀ B : Fin N, (B = v ∨ B = s ∨ B = p) →
      ∀ P1 ∈ L K, ∀ P2 ∈ L K, (P1 ∈ L S ∨ B ∈ L S) → (P1 ∈ L Mv ∨ B ∈ L Mv) →
        (P2 ∈ L S ∨ B ∈ L S) → (P2 ∈ L Mv ∨ B ∈ L Mv) → P1 = P2) ∧
    v ∉ L Mv := by
  intro q N L v s p Mv Ms Mp hq hN hcard hint hnon hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have hvMv : v ∉ L Mv := fun h => hnon Mv ⟨h, hsMv, hpMv⟩
  have hpMp : p ∉ L Mp := fun h => hnon Mp ⟨hvMp, hsMp, h⟩
  have hSMp : S ≠ Mp := by intro h; exact hsS (h.symm ▸ hsMp)
  refine ⟨?_, ?_, ?_, hvMv⟩
  · intro Q hQS hQv
    refine ⟨?_, hpMp, ?_⟩
    · intro hQMp
      exact hQv (PEqualNP.Outside.L_meta_1662.unique (hint S Mp hSMp) hQS hQMp hvS hvMp)
    · intro S2 hne hvS2 hsS2 hpS2
      refine ⟨?_, hpS2⟩
      intro hQS2
      exact hQv (PEqualNP.Outside.L_meta_1662.unique (hint S S2 hne.symm) hQS hQS2 hvS hvS2)
  · intro S2 hne hvS2 hsS2 hpS2 B hB P hPS2 hh
    have hBS : B ∉ L S := by rcases hB with rfl | rfl <;> assumption
    have hPS : P ∈ L S := hh.1.resolve_right (fun h => hBS h.2.2.2)
    have hPv := PEqualNP.Outside.L_meta_1662.unique (hint S S2 hne.symm) hPS hPS2 hvS hvS2
    rcases hh.2 with h | h
    · exact hvMv (hPv ▸ h)
    · exact h.1 hPv
  · intro K hvK hsK hpK B hB P1 h1K P2 h2K h1S h1M h2S h2M
    rcases hB with rfl | rfl | rfl
    · have hKM : K ≠ Mv := by intro h; exact hsK (h.symm ▸ hsMv)
      exact PEqualNP.Outside.L_meta_1662.unique (hint K Mv hKM) h1K (h1M.resolve_right hvMv) h2K (h2M.resolve_right hvMv)
    · have hKS : K ≠ S := by intro h; exact hvK (h.symm ▸ hvS)
      exact PEqualNP.Outside.L_meta_1662.unique (hint K S hKS) h1K (h1S.resolve_right hsS) h2K (h2S.resolve_right hsS)
    · have hKS : K ≠ S := by intro h; exact hvK (h.symm ▸ hvS)
      exact PEqualNP.Outside.L_meta_1662.unique (hint K S hKS) h1K (h1S.resolve_right hpS) h2K (h2S.resolve_right hpS)