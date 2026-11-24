import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1173

open PEqualNP.CircuitLowerBounds

def gateList : List Gate :=
  [ ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.and, [6, 7]⟩,
    ⟨GateOp.or, [11, 12]⟩,
    ⟨GateOp.or, [15, 13]⟩,
    ⟨GateOp.or, [16, 14]⟩ ]

def circ : Circuit := ⟨gateList, 17⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, gateList, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_⟩ <;> simp

end PEqualNP.Outside.L_meta_1173

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1173 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1173.circ, PEqualNP.Outside.L_meta_1173.mono, ?_, ?_⟩
  · decide
  · decide
