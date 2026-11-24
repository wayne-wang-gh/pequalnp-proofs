import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1194 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) x := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    generalize x 0 = a0
    generalize x 1 = a1
    generalize x 2 = a2
    generalize x 3 = a3
    generalize x 4 = a4
    generalize x 5 = a5
    generalize x 6 = a6
    generalize x 7 = a7
    revert a0 a1 a2 a3 a4 a5 a6 a7
    decide
