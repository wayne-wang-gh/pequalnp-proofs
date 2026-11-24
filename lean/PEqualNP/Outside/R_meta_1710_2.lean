import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

-- Split by whether the edge has an owning gate that rejects every nonedge
-- pair, including the inputs supported at one vertex.

theorem PEqualNP.Outside.R_meta_1710_2 :
    (∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      circuitFun n C = graphFun G ∅ →
      (G.edgeFinset.filter fun e => (∃ u v : Fin n, e = s(u,v) ∧
        ∃ j : Fin C.gates.length, Owns n C j u v ∧ (∀ p q : Fin n, gateVal n C j (pairInput p q) = true → G.Adj p q))).card
        ≤ c * (C.size+1)) →
    (∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      circuitFun n C = graphFun G ∅ →
      (G.edgeFinset.filter fun e => ¬ (∃ u v : Fin n, e = s(u,v) ∧
        ∃ j : Fin C.gates.length, Owns n C j u v ∧ (∀ p q : Fin n, gateVal n C j (pairInput p q) = true → G.Adj p q))).card
        ≤ c * (C.size+1)) →
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) => Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  intro sound unsound
  obtain ⟨a,ha⟩ := sound
  obtain ⟨b,hb⟩ := unsound
  refine ⟨a+b, ?_⟩
  intro n G inst hdegrees hcycles C hmono hfun
  have heq : circuitFun n C = graphFun G ∅ := by
    funext x
    change circuitFun n C x =
      (decide (∃ v ∈ (∅ : Finset (Fin n)), x v = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    exact congrFun hfun x
  have hc1 := ha n G hdegrees hcycles C hmono heq
  have hc2 := hb n G hdegrees hcycles C hmono heq
  let good (e : Sym2 (Fin n)) : Prop :=
    ∃ u v : Fin n, e = s(u,v) ∧ ∃ j : Fin C.gates.length,
      Owns n C j u v ∧ (∀ p q : Fin n, gateVal n C j (pairInput p q) = true → G.Adj p q)
  have partition := Finset.card_filter_add_card_filter_not (s := G.edgeFinset) good
  change (G.edgeFinset.filter good).card ≤ a * (C.size+1) at hc1
  change (G.edgeFinset.filter (fun e => ¬ good e)).card ≤ b * (C.size+1) at hc2
  rw [Nat.add_mul, ← partition]
  exact Nat.add_le_add hc1 hc2
