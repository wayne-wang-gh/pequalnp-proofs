import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1001

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [14, 8]⟩, ⟨GateOp.and, [3, 15]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [7, 17]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.and, [8, 19]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [21, 16]⟩, ⟨GateOp.or, [22, 18]⟩, ⟨GateOp.or, [23, 20]⟩], 24⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    C0.eval [b0, b1, b2, b3, b4, b5, b6, b7, b8] = ((b0 && b1) || (b1 && b2) || (b2 && b3) || (b3 && b4) || (b4 && b0) || (b0 && b5) || (b1 && b6) || (b2 && b7) || (b3 && b8) || (b5 && b7) || (b6 && b8) || (b8 && b5)) := by
  decide +kernel

theorem ofFn9 (x : Fin 9 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1001

theorem PEqualNP.Outside.L_meta_1001 : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 :=
  ⟨PEqualNP.Outside.L_meta_1001.C0, PEqualNP.Outside.L_meta_1001.ok0, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_1001.ofFn9]
      exact PEqualNP.Outside.L_meta_1001.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)⟩
