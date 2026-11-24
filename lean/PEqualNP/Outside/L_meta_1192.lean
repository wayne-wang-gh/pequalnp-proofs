import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_1192 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) x := by
  let c : Circuit := ⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨c, ?_, by decide, ?_⟩
  · simp [Monotone2, c]
  · decide +kernel
