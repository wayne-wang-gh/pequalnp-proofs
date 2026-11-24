import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_179

open PEqualNP.MetaComplexity

-- the formula (x0 or x1) and (x2 or x3 or ((x0 or x5) and (x1 or x4)))
def L (i : Fin 6) : DMFormula 6 := DMFormula.lit i true

def phi : DMFormula 6 :=
  DMFormula.and (DMFormula.or (L 0) (L 1))
    (DMFormula.or (L 2) (DMFormula.or (L 3)
      (DMFormula.and (DMFormula.or (L 0) (L 5)) (DMFormula.or (L 1) (L 4)))))

end PEqualNP.Outside.L_meta_179

theorem PEqualNP.Outside.L_meta_179 : PEqualNP.MetaComplexity.HasLeafSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 8 := by
  refine ⟨PEqualNP.Outside.L_meta_179.phi, by decide, fun x => ?_⟩
  simp only [PEqualNP.Outside.L_meta_179.phi, PEqualNP.Outside.L_meta_179.L,
    PEqualNP.MetaComplexity.DMFormula.eval, ite_true]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl
