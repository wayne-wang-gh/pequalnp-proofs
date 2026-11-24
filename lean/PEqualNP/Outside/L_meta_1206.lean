import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1206

open PEqualNP.CircuitLowerBounds

def ckt : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem keval :
    ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
      ckt.eval [a0, a1, a2, a3, a4, a5, a6, a7] =
        ((a0 && a1) || (a0 && a2) || (a1 && a3) || (a2 && a4) || (a3 && a4) || (a5 && a6) || (a5 && a7)) := by
  decide

end PEqualNP.Outside.L_meta_1206

theorem PEqualNP.Outside.L_meta_1206 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1206.ckt, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1206.ckt]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1206.keval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
