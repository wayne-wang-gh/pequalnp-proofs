import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1195_aux

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[ ⟨GateOp.or, [1, 2]⟩,
     ⟨GateOp.or, [8, 3]⟩,
     ⟨GateOp.and, [0, 9]⟩,
     ⟨GateOp.and, [2, 5]⟩,
     ⟨GateOp.and, [3, 6]⟩,
     ⟨GateOp.or, [1, 7]⟩,
     ⟨GateOp.and, [4, 13]⟩,
     ⟨GateOp.or, [10, 11]⟩,
     ⟨GateOp.or, [15, 12]⟩,
     ⟨GateOp.or, [16, 14]⟩ ], 17⟩

lemma mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact ⟨by simp, by decide⟩

lemma size_circ : circ.size ≤ 10 := by
  decide

lemma eval_circ (x : Fin 8 → Bool) :
    circ.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 7)) := by
  have key : ∀ a b c d e f g h : Bool,
      circ.eval (List.ofFn ![a, b, c, d, e, f, g, h]) =
        ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (d && g) || (e && h)) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

end PEqualNP.Outside.L_meta_1195_aux

theorem PEqualNP.Outside.L_meta_1195 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1195_aux.circ,
   PEqualNP.Outside.L_meta_1195_aux.mono,
   PEqualNP.Outside.L_meta_1195_aux.size_circ,
   PEqualNP.Outside.L_meta_1195_aux.eval_circ⟩
