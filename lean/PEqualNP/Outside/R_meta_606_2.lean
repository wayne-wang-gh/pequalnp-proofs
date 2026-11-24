import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_606_2
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ C : Circuit, IsLeastAO G C ∧ PEqualNP.TopForm.TopForm G C ∧ C.size ≤ D.size ∧
        (G.edgeFinset \ Ustar G C).card ≤ C.size + 1)
    (residual : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        (Ustar G C).card ≤ k * (C.size + 1)) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨k, hk⟩ := residual
  refine ⟨k + 1, ?_⟩
  intro n G inst hg D hD hfun
  classical
  by_cases he : G.edgeFinset.Nonempty
  · obtain ⟨C, hl, ht, hs, hcovered⟩ := normalize n G hg he D hD hfun
    have hu := hk n G hg he C hl ht
    have hsub : Ustar G C ⊆ G.edgeFinset := Finset.sdiff_subset
    have hsplit := Finset.card_sdiff_add_card_eq_card hsub
    calc
      G.edgeFinset.card = (G.edgeFinset \ Ustar G C).card + (Ustar G C).card := hsplit.symm
      _ ≤ (C.size + 1) + k * (C.size + 1) := Nat.add_le_add hcovered hu
      _ = (k + 1) * (C.size + 1) := by rw [Nat.add_mul, one_mul, Nat.add_comm]
      _ ≤ (k + 1) * (D.size + 1) := Nat.mul_le_mul_left _ (by omega)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp he
    simp [hempty]
