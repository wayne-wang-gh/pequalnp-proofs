import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1146

open PEqualNP.CircuitLowerBounds

theorem ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

def c1 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], output := 15 }

theorem e1 : ∀ a b c d e f g h : Bool, c1.eval [a, b, c, d, e, f, g, h] = ((a && b) || (a && c) || (b && d) || (e && f) || (g && h)) := by
  decide

theorem f1 : PEqualNP.MetaComplexity.Monotone2 c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1146

theorem PEqualNP.Outside.L_meta_1146 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 6 && x 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1146.c1, PEqualNP.Outside.L_meta_1146.f1, by decide, fun x => by rw [PEqualNP.Outside.L_meta_1146.ofFn8 x]; exact PEqualNP.Outside.L_meta_1146.e1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
