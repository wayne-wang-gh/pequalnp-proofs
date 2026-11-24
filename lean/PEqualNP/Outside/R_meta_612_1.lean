import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_612_1 :
    (∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.IsAcyclic → G.edgeSet.ncard + t ≤ C.size + 1) →
    (∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → ¬ G.IsAcyclic → G.edgeSet.ncard + t ≤ C.size + 1) →
    (∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1) := by
  classical
  intro hf hc n t G C h1 h2 h3 h4 hm he
  by_cases h : G.IsAcyclic
  · exact hf n t G C h1 h2 h3 h4 hm he h
  · exact hc n t G C h1 h2 h3 h4 hm he h
