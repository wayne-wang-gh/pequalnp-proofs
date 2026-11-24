import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro hHyp m H instH D hMono hFun hGirth hClean
  have hNo4 : ∀ a b c d : Fin m, a ≠ c → b ≠ d → ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
    intro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
    let W : H.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
    have hW : W.IsCycle := by
      refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [W]⟩
      simp only [W, SimpleGraph.Walk.tail_cons, SimpleGraph.Walk.isPath_copy,
        SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
      simp [hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm, hbd]
    have h5 := hGirth a W hW
    have h4 : W.length = 4 := rfl
    omega
  have hGates : ∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hMono g hg
  have hEval : ∀ x : Fin m → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) =
        decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    have hx := congr_fun hFun x
    change D.eval (List.ofFn x) = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ x at hx
    have hD : (⟨D.gates, D.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = D := rfl
    rw [hD, hx]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty, false_and,
      exists_false, decide_false, Bool.false_or]
  have hAnd : ∀ (i : Fin D.gates.length) (x : Fin m → Bool),
      (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩ (List.ofFn x)).getD (m + (i : ℕ)) false = true →
      ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hiop hwire
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt D (i : ℕ) = D.gates.get i := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem i.isLt]
    have hgval : PEqualNP.EdgeOwnership.gateVal m D (i : ℕ) x = true := hwire
    have hgf := hClean (i : ℕ) i.isLt (hgate.symm ▸ hiop) x hgval
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty, false_and,
      exists_false, decide_false, Bool.false_or] at hgf
    exact of_decide_eq_true hgf
  obtain ⟨T, hTcov, hTcard⟩ := hHyp m H hNo4 D.gates D.output hGates hEval hAnd
  have hTsize : H.edgeFinset.card + T.card ≤ D.size + 1 := hTcard
  exact ⟨T, hTcov, hTsize, by omega⟩
