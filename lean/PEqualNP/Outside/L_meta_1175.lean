import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1175_aux

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 1]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩

theorem k1 : ∀ a b c d e f g h : Bool, c1.eval [a, b, c, d, e, f, g, h] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (b && g) || (b && h)) := by
  decide

end PEqualNP.Outside.L_meta_1175_aux

open PEqualNP.Outside.L_meta_1175_aux in
theorem PEqualNP.Outside.L_meta_1175 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7)) x := by
  refine ⟨c1, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c1]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
