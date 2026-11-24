import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1178

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit where
  gates := [
    { op := .or,  inputs := [1, 2] },
    { op := .or,  inputs := [8, 3] },
    { op := .or,  inputs := [9, 4] },
    { op := .and, inputs := [0, 10] },
    { op := .and, inputs := [1, 5] },
    { op := .and, inputs := [2, 6] },
    { op := .and, inputs := [3, 7] },
    { op := .or,  inputs := [11, 12] },
    { op := .or,  inputs := [15, 13] },
    { op := .or,  inputs := [16, 14] }
  ]
  output := 17

lemma circ_monotone : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma circ_size : circ.size ≤ 10 := by
  decide

lemma ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one]
  rfl

lemma eval8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    circ.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) ||
        (b1 && b5) || (b2 && b6) || (b3 && b7)) := by
  have h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
      circ.eval [a0, a1, a2, a3, a4, a5, a6, a7] =
        ((a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) ||
          (a1 && a5) || (a2 && a6) || (a3 && a7)) := by decide
  exact h b0 b1 b2 b3 b4 b5 b6 b7

lemma circ_eval (x : Fin 8 → Bool) :
    circ.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) := by
  rw [ofFn8]
  exact eval8 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

end PEqualNP.Outside.L_meta_1178

theorem PEqualNP.Outside.L_meta_1178 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1178.circ,
    PEqualNP.Outside.L_meta_1178.circ_monotone,
    PEqualNP.Outside.L_meta_1178.circ_size,
    PEqualNP.Outside.L_meta_1178.circ_eval⟩
