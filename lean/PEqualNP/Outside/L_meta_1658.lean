import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1658

theorem main_aux : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (S : Finset (Fin n)) (k0 : ℕ) (Bd : Finset ℕ) (Kc : Finset ℕ),
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  k0 < gates.length →
  (∀ u : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (n + k0) false = true ↔ u ∈ S) →
  k0 ∈ Kc →
  (∀ k1 ∈ Kc, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
    (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ Kc) →
  (∀ bw ∈ Bd, ∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate),
    (∀ bK : Set ℕ, k0 ∈ bK →
      (∀ k1 ∈ bK, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
        (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ bK) → bk ∈ bK) ∧
    gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧
    ¬ (∀ u2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin n => decide (u2k = u2)))).getD bw false = true → u2 ∈ S)) →
  Bd.card ≤ 2 * Kc.card := by
  intro n gates S k0 Bd Kc hg _ _ _ hk0 hcl hB
  classical
  have hf : ∀ k : ℕ, ((gates[k]?).elim (∅ : Finset ℕ) (fun g => g.inputs.toFinset)).card ≤ 2 := by
    intro k
    cases h : gates[k]? with
    | none => simp
    | some g =>
      have hm : g ∈ gates := by
        obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
        exact List.getElem_mem hlt
      have h2 := (hg g hm).2
      have h3 := List.toFinset_card_le g.inputs
      simp only [Option.elim]
      omega
  have hsub : Bd ⊆ Kc.biUnion
      (fun k => (gates[k]?).elim (∅ : Finset ℕ) (fun g => g.inputs.toFinset)) := by
    intro bw hbw
    obtain ⟨bk, bg, hbk, hgk, _, hin, _⟩ := hB bw hbw
    have hmem : bk ∈ (Kc : Set ℕ) := by
      apply hbk (Kc : Set ℕ)
      · exact Finset.mem_coe.mpr hk0
      · intro k1 hk1 g1 k2 h1 h2 h3 h4
        exact Finset.mem_coe.mpr (hcl k1 (Finset.mem_coe.mp hk1) g1 k2 h1 h2 h3 h4)
    rw [Finset.mem_biUnion]
    refine ⟨bk, Finset.mem_coe.mp hmem, ?_⟩
    rw [hgk]
    simp only [Option.elim]
    exact List.mem_toFinset.mpr hin
  calc Bd.card
      ≤ (Kc.biUnion
          (fun k => (gates[k]?).elim (∅ : Finset ℕ) (fun g => g.inputs.toFinset))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Kc, ((gates[k]?).elim (∅ : Finset ℕ) (fun g => g.inputs.toFinset)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Kc, 2 := Finset.sum_le_sum (fun k _ => hf k)
    _ = 2 * Kc.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

end PEqualNP.Outside.L_meta_1658

theorem PEqualNP.Outside.L_meta_1658 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (S : Finset (Fin n)) (k0 : ℕ) (Bd : Finset ℕ) (Kc : Finset ℕ),
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  k0 < gates.length →
  (∀ u : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (n + k0) false = true ↔ u ∈ S) →
  k0 ∈ Kc →
  (∀ k1 ∈ Kc, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
    (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ Kc) →
  (∀ bw ∈ Bd, ∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate),
    (∀ bK : Set ℕ, k0 ∈ bK →
      (∀ k1 ∈ bK, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
        (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ bK) → bk ∈ bK) ∧
    gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧
    ¬ (∀ u2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin n => decide (u2k = u2)))).getD bw false = true → u2 ∈ S)) →
  Bd.card ≤ 2 * Kc.card :=
  PEqualNP.Outside.L_meta_1658.main_aux
