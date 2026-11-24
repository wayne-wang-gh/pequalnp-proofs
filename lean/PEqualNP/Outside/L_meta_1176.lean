import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1176

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [0, 10]⟩,
    ⟨.or, [5, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [2, 7]⟩,
    ⟨.or, [11, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr rfl, by decide⟩

end PEqualNP.Outside.L_meta_1176

open PEqualNP.Outside.L_meta_1176 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_1176 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
