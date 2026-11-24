import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1203

open PEqualNP.CircuitLowerBounds

theorem ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

def c1 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], output := 17 }

theorem e1 : ∀ a b c d e f g h : Bool, c1.eval [a, b, c, d, e, f, g, h] = ((a && b) || (a && c) || (a && d) || (b && e) || (f && g) || (f && h) || (g && h)) := by
  decide

theorem f1 : PEqualNP.MetaComplexity.Monotone2 c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1203

theorem PEqualNP.Outside.L_meta_1203 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1203.c1, PEqualNP.Outside.L_meta_1203.f1, by decide, fun x => by rw [PEqualNP.Outside.L_meta_1203.ofFn8 x]; exact PEqualNP.Outside.L_meta_1203.e1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
