import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

-- At an accepting top, trace each operand through OR gates to a raw input
-- or to a lower AND. An uncovered edge uses at least one lower AND.
theorem PEqualNP.Outside.R_meta_606_3
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ C : Circuit, IsLeastAO G C ∧ PEqualNP.TopForm.TopForm G C ∧ C.size ≤ D.size ∧
        (G.edgeFinset \ Ustar G C).card ≤ C.size + 1)
    (trace : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ∀ e ∈ Ustar G C,
      (∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
        gateVal n C g (pairInput u v) = true) ∨
      (∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C,
        g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
        gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true))
    (single : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
        gateVal n C g (pairInput u v) = true)).card ≤ k * (C.size + 1))
    (double : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e =>
        (¬ ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          gateVal n C g (pairInput u v) = true) ∧
        (∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C,
        g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
        gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true))).card ≤ k * (C.size + 1)) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide
        (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨k₁, h₁⟩ := single
  obtain ⟨k₂, h₂⟩ := double
  refine ⟨1 + k₁ + k₂, ?_⟩
  intro n G inst hG D hD hFun
  classical
  by_cases hE : G.edgeFinset.Nonempty
  · obtain ⟨C, hLeast, hTop, hSize, hCovered⟩ := normalize n G hG hE D hD hFun
    have hSingle := h₁ n G C hG hLeast hTop
    have hDouble := h₂ n G C hG hLeast hTop
    generalize hS : ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
      gateVal n C g (pairInput u v) = true)) = S at hSingle
    generalize hT : ((Ustar G C).filter (fun e =>
      (¬ ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
        gateVal n C g (pairInput u v) = true) ∧
      (∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C,
      g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
      gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true))) = T at hDouble
    have hSub : Ustar G C ⊆ S ∪ T := by
      intro e he
      by_cases hs : e ∈ S
      · exact Finset.mem_union_left _ hs
      · have hn : ¬ ∃ u v : Fin n, e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
          u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
          gateVal n C g (pairInput u v) = true :=
          fun h => hs (hS ▸ Finset.mem_filter.mpr ⟨he, h⟩)
        have ht := (trace n G C hLeast hTop e he).resolve_left hn
        exact Finset.mem_union_right _ (hT ▸ Finset.mem_filter.mpr ⟨he, hn, ht⟩)
    have hResidual : (Ustar G C).card ≤ k₁ * (C.size + 1) + k₂ * (C.size + 1) :=
      (Finset.card_le_card hSub).trans ((Finset.card_union_le S T).trans (Nat.add_le_add hSingle hDouble))
    have hPartition := Finset.card_sdiff_add_card_eq_card
      (Finset.sdiff_subset : Ustar G C ⊆ G.edgeFinset)
    calc
      G.edgeFinset.card = (G.edgeFinset \ Ustar G C).card + (Ustar G C).card := hPartition.symm
      _ ≤ (C.size + 1) + (k₁ * (C.size + 1) + k₂ * (C.size + 1)) := Nat.add_le_add hCovered hResidual
      _ = (1 + k₁ + k₂) * (C.size + 1) := by simp [Nat.add_mul, Nat.add_assoc]
      _ ≤ (1 + k₁ + k₂) * (D.size + 1) := Nat.mul_le_mul_left _ (Nat.succ_le_succ hSize)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hE]
