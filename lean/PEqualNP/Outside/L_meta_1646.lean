import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1646

theorem key (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : PEqualNP.TopForm.NoFourCycle G)
    (U : Finset (Sym2 (Fin n))) (x : Fin n) (B : Finset (Fin n))
    (hB : B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))
    (y z : Fin n) (hy : y ∈ B) (hz : z ∈ B) (hyU : s(x, y) ∈ U) (hxy : G.Adj x y) (hxz : G.Adj x z) :
    y = z := by
  rcases hB with h1 | ⟨_, c, hc, hcU⟩
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    rw [ha] at hy hz
    rw [Finset.mem_singleton] at hy hz
    rw [hy, hz]
  · have hxc : x ≠ c := by
      intro h
      apply hcU y hy
      rw [← h]
      exact hyU
    have h := hG x c hxc
    rw [Finset.card_le_one] at h
    exact h y (by simp [hxy, hc y hy]) z (by simp [hxz, hc z hz])

end PEqualNP.Outside.L_meta_1646

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  intro n G _ hG U hU x Y hY R π hπ hcov
  classical
  have hadj : ∀ y ∈ Y, G.Adj x y := fun y hy => by
    have h := hU _ (hY y hy)
    simpa using h
  let f : Fin n → Finset (Fin n) := fun y => if h : y ∈ R then Classical.choose (hcov y h) else ∅
  have hf : ∀ y ∈ R, f y ∈ π ∧ y ∈ f y := by
    intro y hy
    have h := Classical.choose_spec (hcov y hy)
    simp only [f, dif_pos hy]
    exact h
  have hinj : Set.InjOn f ↑(R ∩ Y) := by
    intro a ha b hb hab
    have ha' := Finset.mem_inter.mp ha
    have hb' := Finset.mem_inter.mp hb
    have h1 := hf a ha'.1
    have h2 := hf b hb'.1
    have hb2 : b ∈ f a := by
      rw [hab]
      exact h2.2
    exact PEqualNP.Outside.L_meta_1646.key n G hG U x (f a) (hπ _ h1.1).2 a b h1.2 hb2
      (hY a ha'.2) (hadj a ha'.2) (hadj b hb'.2)
  refine ⟨?_, ?_⟩
  · refine Finset.card_le_card_of_injOn f ?_ hinj
    intro a ha
    have ha' := Finset.mem_inter.mp ha
    exact (hf a ha'.1).1
  · intro hall hnot
    rw [Finset.not_subset] at hnot
    obtain ⟨r, hrR, hrY⟩ := hnot
    obtain ⟨B0, hB0, hrB0⟩ := hcov r hrR
    have hle : (R ∩ Y).card ≤ (π.erase B0).card := by
      refine Finset.card_le_card_of_injOn f ?_ hinj
      intro a ha
      have ha' := Finset.mem_inter.mp ha
      have h1 := hf a ha'.1
      refine Finset.mem_erase.mpr ⟨?_, h1.1⟩
      intro he
      have hr2 : r ∈ f a := by
        rw [he]
        exact hrB0
      have har : a = r := PEqualNP.Outside.L_meta_1646.key n G hG U x (f a) (hπ _ h1.1).2 a r h1.2 hr2
        (hY a ha'.2) (hadj a ha'.2) (hall r hrR)
      apply hrY
      rw [← har]
      exact ha'.2
    have hcard := Finset.card_erase_of_mem hB0
    have hpos : 0 < π.card := Finset.card_pos.mpr ⟨B0, hB0⟩
    omega
