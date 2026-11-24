import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Peel vertices of degree one or two. The remaining graph has minimum degree
-- three after isolated vertices are ignored.
theorem PEqualNP.Outside.R_meta_606_1 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n),
      0 < G.degree v → G.degree v ≤ 2 → ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ D' : Circuit, Monotone2 D' ∧ D'.size < D.size ∧
        circuitFun n D' = (fun x => decide
          (∃ i j, (G.deleteIncidenceSet v).Adj i j ∧ x i = true ∧ x j = true))) →
    (∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeFinset.card ≤ c * (D.size + 1)) →
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide
        (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeFinset.card ≤ c * (D.size + 1) := by
  intro eliminate core
  obtain ⟨c, hcore⟩ := core
  refine ⟨max c 2, ?_⟩
  have budget : ∀ s : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, D.size = s → Monotone2 D →
        circuitFun n D = (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) →
        G.edgeFinset.card ≤ max c 2 * (D.size + 1) := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s smaller =>
      intro n G _ hg D hsize hmon hfun
      by_cases hdegrees : ∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v
      · exact (hcore n G hdegrees hg D hmon hfun).trans
          (Nat.mul_le_mul_right _ (le_max_left c 2))
      · push_neg at hdegrees
        obtain ⟨v, hvne, hvsmall⟩ := hdegrees
        have hvpos : 0 < G.degree v := Nat.pos_of_ne_zero hvne
        have hvbound : G.degree v ≤ 2 := by omega
        obtain ⟨D', hmon', hlt, hfun'⟩ := eliminate n G v hvpos hvbound D hmon hfun
        have hcycle : ∀ (u : Fin n) (p : (G.deleteIncidenceSet v).Walk u u),
            p.IsCycle → 5 ≤ p.length := by
          intro u p hp
          have hle := G.deleteIncidenceSet_le v
          simpa only [SimpleGraph.Walk.length_mapLe] using hg u (p.mapLe hle) (hp.mapLe hle)
        have hnext := smaller D'.size (hsize ▸ hlt) n (G.deleteIncidenceSet v)
          hcycle D' rfl hmon' hfun'
        have heq := G.card_edgeFinset_deleteIncidenceSet v
        have hdeg : G.degree v ≤ G.edgeFinset.card := by
          rw [← G.card_incidenceFinset_eq_degree v]
          exact Finset.card_le_card (G.incidenceFinset_subset v)
        have hsucc : D'.size + 1 ≤ D.size := by omega
        have hm := Nat.mul_le_mul_left (max c 2) hsucc
        have hc : 2 ≤ max c 2 := le_max_right c 2
        rw [Nat.mul_succ]
        omega
  intro n G _ hg D hmon hfun
  exact budget D.size n G hg D rfl hmon hfun
