import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1006

-- Counterexample of johnpascoe43 in PR 917: two triangles and a pentagon,
-- with additional edges. The circuit shares its first gate among three outputs.

open PEqualNP.AndCount

abbrev V := Fin 11

def hood : V → ℕ := ![1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85]

abbrev adj (v w : V) := (hood v).testBit w.val = true

def graph : SimpleGraph V where
  Adj := adj
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

def circuit : AndCountCircuit 11 where
  size := 6
  leftVars := ![{7, 10}, {2}, {0}, {8}, {4, 8}, {3}]
  leftGates := ![∅, ∅, ∅, {0}, ∅, ∅]
  rightVars := ![{6, 9}, {5, 10}, {9, 10}, {4, 5}, {1}, {6, 7}]
  rightGates := ![∅, {0}, ∅, ∅, {0}, ∅]
  outVars := ∅
  outGates := {1, 2, 3, 4, 5}

theorem wf : circuit.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem squareFree : ∀ a b c d : V, a ≠ c → b ≠ d →
    adj a b → adj b c → adj c d → ¬ adj d a := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem boundary : ∀ I : Finset V, (∀ v ∈ I, ∀ w ∈ I, ¬ adj v w) →
    (∀ u, u ∉ I → ∃ v ∈ I, adj u v) →
    circuit.eval I = false ∧ ∀ u, u ∉ I → circuit.eval (insert u I) = true := by
  decide +kernel

private def triangleA : Finset V := {1,4,8}
private def triangleB : Finset V := {3,6,7}
private def pentagon : Finset V := {0,9,5,2,10}

-- Count separately on the three vertex-disjoint odd cycles. Each local check
-- ranges over subsets of at most five vertices, not over covers of the graph.
private theorem cover_bound (T : Finset V) (h : ∀ v w, adj v w → v ∈ T ∨ w ∈ T) : 7 ≤ T.card := by
  let localCover (B U : Finset V) := ∀ v ∈ B, ∀ w ∈ B, adj v w → v ∈ U ∨ w ∈ U
  have local_ok (B : Finset V) : localCover B (B ∩ T) := by
    intro v hv w hw he
    rcases h v w he with ht | ht
    · exact Or.inl (Finset.mem_inter.mpr ⟨hv, ht⟩)
    · exact Or.inr (Finset.mem_inter.mpr ⟨hw, ht⟩)
  have amin : ∀ U ∈ triangleA.powerset, localCover triangleA U → 2 ≤ U.card := by decide +kernel
  have bmin : ∀ U ∈ triangleB.powerset, localCover triangleB U → 2 ≤ U.card := by decide +kernel
  have pmin : ∀ U ∈ pentagon.powerset, localCover pentagon U → 3 ≤ U.card := by decide +kernel
  have ha := amin _ (Finset.mem_powerset.mpr Finset.inter_subset_left) (local_ok _)
  have hb := bmin _ (Finset.mem_powerset.mpr Finset.inter_subset_left) (local_ok _)
  have hp := pmin _ (Finset.mem_powerset.mpr Finset.inter_subset_left) (local_ok _)
  have dab : Disjoint triangleA triangleB := by decide
  have dp : Disjoint (triangleA ∪ triangleB) pentagon := by decide
  have combine (A B : Finset V) (hd : Disjoint A B) :
      ((A ∪ B) ∩ T).card = (A ∩ T).card + (B ∩ T).card := by
    rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint
      (hd.mono Finset.inter_subset_left Finset.inter_subset_left)]
  have le := Finset.card_le_card (Finset.inter_subset_right (s₁ := triangleA ∪ triangleB ∪ pentagon) (s₂ := T))
  rw [combine _ _ dp, combine _ _ dab] at le
  omega

end PEqualNP.Outside.L_meta_1006

open PEqualNP.Outside.L_meta_1006 in
theorem PEqualNP.Outside.L_meta_1006 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
    (∃ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed ∧
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧
      ∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → C.size ≤ T.card) ∧
    (∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed →
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) →
      ∃ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) ∧ T.card ≤ C.size)) := by
  intro asserted
  obtain ⟨T, hc, hs⟩ := (asserted 11 graph squareFree).2 circuit wf boundary
  exact (by decide : ¬ 7 ≤ 6) ((cover_bound T hc).trans hs)
