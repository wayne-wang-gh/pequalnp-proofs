import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1201

open PEqualNP.CircuitLowerBounds

def gateList : List Gate :=
  [ ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.or, [12, 7]⟩,
    ⟨GateOp.and, [5, 13]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [15, 14]⟩ ]

def circ : Circuit := ⟨gateList, 16⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, gateList, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_⟩ <;> simp

theorem ev : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    circ.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) ||
        (b4 && b5) || (b5 && b6) || (b5 && b7)) := by
  decide +kernel

theorem ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1201

theorem PEqualNP.Outside.L_meta_1201 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 5 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1201.circ, PEqualNP.Outside.L_meta_1201.mono, by decide, fun x => by
    rw [PEqualNP.Outside.L_meta_1201.ofFn8]
    exact PEqualNP.Outside.L_meta_1201.ev (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
