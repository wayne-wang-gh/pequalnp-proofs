import PEqualNP.Defs
import PEqualNP.Defs.LineDegree
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Defs.NestedCoverCircuit

/-! Size form of the transposition count, conditional on that count: for sets meeting pairwise in
at most one point, a fan-in-two AND/OR circuit reading only earlier wires that computes their
incidence function with at most k ANDs of two line-dependent wires has at most
(6k+6)(size) + (12k^2+13k+2)m + 6k^2 + 5k incidences. A circuit computing the function exactly is
sound on one-line inputs and accepts every incident pair, so the hypothesis applies with s = size. -/
theorem PEqualNP.MetaComplexity.L1695 : (∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k) → ∀ (n m k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (y : Fin m → Bool), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x y) = decide (∃ j : Fin m, ∃ p ∈ L j, x p = true ∧ y j = true)) → (∑ j : Fin m, (L j).card) ≤ (6 * k + 6) * C.size + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  intro hK4 n m k L C hL hM hR hk hF
  have hsound : ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 →
      PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true →
      ∃ j ∈ Y, ∃ p ∈ L j, x p = true := by
    intro x Y _ h
    rw [hF] at h
    obtain ⟨j, p, hp, hx, hy⟩ := of_decide_eq_true h
    exact ⟨j, of_decide_eq_true hy, p, hp, hx⟩
  have hmain := hK4 n m C.size k L C hL hM hR le_rfl hk hsound
  have hset : (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧
      PEqualNP.MetaComplexity.circuitFun (n + m) C
        (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true))
      = Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2) := by
    apply Finset.filter_congr
    intro e _
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rw [hF]
      exact decide_eq_true ⟨e.2, e.1, h, by simp, by simp⟩
  have hcount : (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2)).card
      = ∑ j : Fin m, (L j).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.card_filter]
    congr 1
    ext p; simp
  rw [hset, hcount] at hmain
  exact hmain
