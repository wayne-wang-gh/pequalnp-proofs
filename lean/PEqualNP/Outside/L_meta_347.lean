import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_347

private abbrev Vertex := Fin 6
private abbrev Edge := Vertex × Vertex
private def edges : List Edge := [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)]

-- A present pendant edge gives a singleton witness at its leaf. In the triangle
-- alone a vertex of degree one suffices, except for the full triangle: use {0, 1}.
private def candidates : Finset (Finset Vertex) := {{3}, {4}, {5}, {0}, {1}, {2}, {0, 1}}

set_option synthInstance.maxSize 20000 in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private theorem verify : ∀ s : {S // S ∈ edges.toFinset.powerset}, s.val.Nonempty → ∃ C ∈ candidates,
    (∀ A ∈ C.powerset, A.Nonempty → A ≠ C → ∃ e ∈ s.val,
      (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧
    (∀ a b : Vertex, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ s.val ∨ (a, x) ∈ s.val) →
      (∃ y ∈ C, (y, b) ∈ s.val ∨ (b, y) ∈ s.val) → ¬ ((a, b) ∈ edges ∨ (b, a) ∈ edges)) ∧
    (s.val.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by decide +kernel

end PEqualNP.Outside.L_meta_347

open PEqualNP.Outside.L_meta_347 in
theorem PEqualNP.Outside.L_meta_347 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ S : Finset (Fin 6 × Fin 6), (∀ e ∈ S, e ∈ E) → S.Nonempty → ∃ C : Finset (Fin 6), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 6, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  rintro E rfl S hS hn
  have sub : S ⊆ edges.toFinset := fun e he => List.mem_toFinset.mpr (hS e he)
  obtain ⟨C, _, hconn, hb, ho⟩ := verify ⟨S, Finset.mem_powerset.mpr sub⟩ hn
  exact ⟨C, fun A hA => hconn A (Finset.mem_powerset.mpr hA), hb, ho⟩
