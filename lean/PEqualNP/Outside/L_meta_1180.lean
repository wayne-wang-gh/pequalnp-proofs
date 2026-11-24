import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1180

open PEqualNP.CircuitLowerBounds

theorem ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

def c1 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [11, 14]⟩], output := 15 }

theorem e1 : ∀ a b c d e f g h : Bool, c1.eval [a, b, c, d, e, f, g, h] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (f && g) || (f && h)) := by
  decide

theorem f1 : PEqualNP.MetaComplexity.Monotone2 c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1180

theorem PEqualNP.Outside.L_meta_1180 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6) || (x 5 && x 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1180.c1, PEqualNP.Outside.L_meta_1180.f1, by decide, fun x => by rw [PEqualNP.Outside.L_meta_1180.ofFn8 x]; exact PEqualNP.Outside.L_meta_1180.e1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
