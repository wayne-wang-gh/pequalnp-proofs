import PEqualNP.MetaComplexity.Helpers.Plane614

/-- The point-line graph of the projective plane of order 3, given the n - 1 + t bound for graphs with no isolated vertex under the two neighbourhood conditions, has every circuit of AND and OR gates for its edge function of size at least 38. Conjecture, on paper. -/
theorem PEqualNP.MetaComplexity.L1478 : (∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) → (∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) → (∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ a b : Fin n, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b)) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → n + t ≤ C.size + 1) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + (b.val - 13)) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ))).Adj u v ∧ x u = true ∧ x v = true) → 38 ≤ C.size
  := by
  intro h614 C hM hC
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := PEqualNP.MetaComplexity.Plane614.facts26
  have := PEqualNP.MetaComplexity.Plane614.assemble 13 {0, 1, 3, 9} (by norm_num) h1 h2 h3 h4 h5 h6 h614 C hM hC
  omega
