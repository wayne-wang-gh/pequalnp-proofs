import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1727 : (∀ (N121 : ℕ) (D121 : PEqualNP.CircuitLowerBounds.Circuit) (S121 W121 : Finset (Fin N121)) (nu121 : Fin N121 → Bool), (∀ g121 ∈ D121.gates, (g121.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g121.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g121.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N121 + N121) D121 → (∀ j121 < D121.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D121 j121).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i121 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D121 j121).inputs, (D121.lineDegrees (N121 + N121) (Finset.Ico N121 (N121 + N121))).getD i121 0 = 0) ∨ (∀ h121 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D121 j121).inputs, (D121.lineDegrees (N121 + N121) (Finset.range N121)).getD h121 0 = 0)) → (∃ x121 y121 xa121 ya121 : Fin N121 → Bool, PEqualNP.MetaComplexity.circuitFun (N121 + N121) D121 (Fin.append (fun u121 => decide (u121 ∈ S121) && x121 u121) (fun t121 => if t121 ∈ W121 then y121 t121 else nu121 t121)) ≠ PEqualNP.MetaComplexity.circuitFun (N121 + N121) D121 (Fin.append (fun u121a => decide (u121a ∈ S121) && xa121 u121a) (fun t121a => if t121a ∈ W121 then ya121 t121a else nu121 t121a))) → ∃ E121 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g121a ∈ E121.gates, (g121a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g121a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g121a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N121 + N121) E121) ∧ (∀ j121a < E121.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt E121 j121a).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i121a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt E121 j121a).inputs, (E121.lineDegrees (N121 + N121) (Finset.Ico N121 (N121 + N121))).getD i121a 0 = 0) ∨ (∀ h121a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt E121 j121a).inputs, (E121.lineDegrees (N121 + N121) (Finset.range N121)).getD h121a 0 = 0)) ∧ E121.size ≤ D121.size ∧ ∀ x121a y121a : Fin N121 → Bool, PEqualNP.MetaComplexity.circuitFun (N121 + N121) E121 (Fin.append x121a y121a) = PEqualNP.MetaComplexity.circuitFun (N121 + N121) D121 (Fin.append (fun u121b => decide (u121b ∈ S121) && x121a u121b) (fun t121b => if t121b ∈ W121 then y121a t121b else nu121 t121b))) → (∀ (q122 N122 a122 b122 : ℕ) (I122 : Fin N122 → Fin N122 → Prop) [DecidableRel I122] (D122 : PEqualNP.CircuitLowerBounds.Circuit) (S122 W122 : Finset (Fin N122)), 2 ≤ q122 → N122 = q122 ^ 2 + q122 + 1 → (∀ l122d : Fin N122, (Finset.univ.filter (fun p122d => I122 p122d l122d)).card = q122 + 1) → (∀ pa122 pb122 : Fin N122, pa122 ≠ pb122 → ∃! lb122 : Fin N122, I122 pa122 lb122 ∧ I122 pb122 lb122) → (∀ g122 ∈ D122.gates, (g122.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g122.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g122.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N122 + N122) D122 → (∀ j122 < D122.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D122 j122).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i122 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D122 j122).inputs, (D122.lineDegrees (N122 + N122) (Finset.Ico N122 (N122 + N122))).getD i122 0 = 0) ∨ (∀ h122 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D122 j122).inputs, (D122.lineDegrees (N122 + N122) (Finset.range N122)).getD h122 0 = 0)) → 1 ≤ a122 → 1 ≤ b122 → (∀ x122 xa122 y122 ya122 : Fin N122 → Bool, (∀ p122 ∈ S122, x122 p122 = xa122 p122) → (∀ l122 ∈ W122, y122 l122 = ya122 l122) → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append x122 y122) = PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append xa122 ya122)) → (∀ p122a ∈ S122, ∀ l122a ∈ W122, I122 p122a l122a → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append (fun a122a => decide (a122a = p122a)) (fun a122b => decide (a122b = l122a))) = true) → (∀ p122b ∈ S122, ∀ T122 ⊆ W122, (∀ l122b ∈ T122, ¬ I122 p122b l122b) → T122.card ≤ a122 → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append (fun a122c => decide (a122c = p122b)) (fun a122d => decide (a122d ∈ T122))) = false) → (∀ l122c ∈ W122, ∀ X122 ⊆ S122, (∀ p122c ∈ X122, ¬ I122 p122c l122c) → X122.card ≤ b122 → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append (fun a122e => decide (a122e ∈ X122)) (fun a122f => decide (a122f = l122c))) = false) → min (min a122 b122) q122 * ((S122 ×ˢ W122).filter (fun pl122 => I122 pl122.1 pl122.2)).card ≤ 5 * q122 * D122.size + min (min a122 b122) q122 * (S122.card + W122.card)) → ∀ (q90 N90 a90 b90 : ℕ) (I90 : Fin N90 → Fin N90 → Prop) [DecidableRel I90] (D90 : PEqualNP.CircuitLowerBounds.Circuit) (S90 W90 : Finset (Fin N90)) (nu90 : Fin N90 → Bool), 2 ≤ q90 → N90 = q90 ^ 2 + q90 + 1 → (∀ l90c : Fin N90, (Finset.univ.filter (fun p90c => I90 p90c l90c)).card = q90 + 1) → (∀ pa90 pb90 : Fin N90, pa90 ≠ pb90 → ∃! lb90 : Fin N90, I90 pa90 lb90 ∧ I90 pb90 lb90) → (∀ g90 ∈ D90.gates, (g90.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g90.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g90.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N90 + N90) D90 → (∀ j90 < D90.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i90 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).inputs, (D90.lineDegrees (N90 + N90) (Finset.Ico N90 (N90 + N90))).getD i90 0 = 0) ∨ (∀ h90 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).inputs, (D90.lineDegrees (N90 + N90) (Finset.range N90)).getD h90 0 = 0)) → 1 ≤ a90 → 1 ≤ b90 → (∀ p90 ∈ S90, ∀ l90 ∈ W90, I90 p90 l90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90 => decide (u90 ∈ S90) && decide (u90 = p90)) (fun t90 => if t90 ∈ W90 then decide (t90 = l90) else nu90 t90)) = true) → (∀ p90a ∈ S90, ∀ T90 ⊆ W90, (∀ l90a ∈ T90, ¬ I90 p90a l90a) → T90.card ≤ a90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90a => decide (u90a ∈ S90) && decide (u90a = p90a)) (fun t90a => if t90a ∈ W90 then decide (t90a ∈ T90) else nu90 t90a)) = false) → (∀ l90b ∈ W90, ∀ X90 ⊆ S90, (∀ p90b ∈ X90, ¬ I90 p90b l90b) → X90.card ≤ b90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90b => decide (u90b ∈ S90) && decide (u90b ∈ X90)) (fun t90b => if t90b ∈ W90 then decide (t90b = l90b) else nu90 t90b)) = false) → min (min a90 b90) q90 * ((S90 ×ˢ W90).filter (fun pl90 => I90 pl90.1 pl90.2)).card ≤ 5 * q90 * D90.size + min (min a90 b90) q90 * (S90.card + W90.card) := by
  intro hR hF q N a b I _ D S W nu hq hN hl hp hg hrb hkm ha hb hacc hrejT hrejX
  by_cases hinc : ∃ p ∈ S, ∃ l ∈ W, I p l
  · obtain ⟨p, hpS, l, hlW, hI⟩ := hinc
    have h1 := hacc p hpS l hlW hI
    have h2 := hrejT p hpS ∅ (Finset.empty_subset _) (fun l0 hl0 => absurd hl0 (Finset.notMem_empty l0))
      (by simp)
    have hne : ∃ x y xa ya : Fin N → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D
          (Fin.append (fun u => decide (u ∈ S) && x u) (fun t => if t ∈ W then y t else nu t)) ≠
        PEqualNP.MetaComplexity.circuitFun (N + N) D
          (Fin.append (fun u => decide (u ∈ S) && xa u) (fun t => if t ∈ W then ya t else nu t)) := by
      refine ⟨fun u => decide (u = p), fun t => decide (t = l), fun u => decide (u = p),
        fun t => decide (t ∈ (∅ : Finset (Fin N))), ?_⟩
      intro h
      have h3 : true = false := h1.symm.trans (h.trans h2)
      exact absurd h3 (by decide)
    obtain ⟨E, ⟨hEg, hErb⟩, hEkm, hEsz, hEf⟩ := hR N D S W nu hg hrb hkm hne
    have key := hF q N a b I E S W hq hN hl hp hEg hErb hEkm ha hb
      (by
        intro x xa y ya hx hy
        have e1 : (fun u => decide (u ∈ S) && x u) = (fun u => decide (u ∈ S) && xa u) := by
          funext u
          by_cases hu : u ∈ S
          · simp [hu, hx u hu]
          · simp [hu]
        have e2 : (fun t => if t ∈ W then y t else nu t) = (fun t => if t ∈ W then ya t else nu t) := by
          funext t
          by_cases ht : t ∈ W
          · simp [ht, hy t ht]
          · simp [ht]
        rw [hEf, hEf, e1, e2])
      (by
        intro p0 hp0 l0 hl0 hI0
        rw [hEf]
        exact hacc p0 hp0 l0 hl0 hI0)
      (by
        intro p0 hp0 T hT hTI hTc
        rw [hEf]
        exact hrejT p0 hp0 T hT hTI hTc)
      (by
        intro l0 hl0 X hX hXI hXc
        rw [hEf]
        exact hrejX l0 hl0 X hX hXI hXc)
    exact le_trans key (Nat.add_le_add_right (Nat.mul_le_mul_left _ hEsz) _)
  · have hemp : ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      rintro ⟨p, l⟩ hm hI
      rw [Finset.mem_product] at hm
      exact hinc ⟨p, hm.1, l, hm.2, hI⟩
    rw [hemp]
    simp
