import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_345

def el : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]

def g1 (S : Finset (Fin 5 × Fin 5)) (C : Finset (Fin 5)) : Bool :=
  decide (∀ A ∈ C.powerset, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A))

def g2 (S : Finset (Fin 5 × Fin 5)) (C : Finset (Fin 5)) : Bool :=
  decide (∀ a b : Fin 5, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ el ∨ (b, a) ∈ el))

def g3 (S : Finset (Fin 5 × Fin 5)) (C : Finset (Fin 5)) : Bool :=
  decide ((S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1)

def mk (b0 b1 b2 b3 b4 b5 : Bool) : Finset (Fin 5 × Fin 5) :=
  el.toFinset.filter (fun e => (e = (0, 1) ∧ b0 = true) ∨ (e = (0, 2) ∧ b1 = true) ∨ (e = (1, 2) ∧ b2 = true) ∨ (e = (0, 3) ∧ b3 = true) ∨ (e = (0, 4) ∧ b4 = true) ∨ (e = (3, 4) ∧ b5 = true))

lemma main : ∀ b0 b1 b2 b3 b4 b5 : Bool, (mk b0 b1 b2 b3 b4 b5).Nonempty → ∃ C : Finset (Fin 5), g1 (mk b0 b1 b2 b3 b4 b5) C = true ∧ g2 (mk b0 b1 b2 b3 b4 b5) C = true ∧ g3 (mk b0 b1 b2 b3 b4 b5) C = true := by
  decide +kernel

lemma mk_eq (S : Finset (Fin 5 × Fin 5)) (hS : ∀ e ∈ S, e ∈ el) : S = mk (decide (((0, 1) : Fin 5 × Fin 5) ∈ S)) (decide (((0, 2) : Fin 5 × Fin 5) ∈ S)) (decide (((1, 2) : Fin 5 × Fin 5) ∈ S)) (decide (((0, 3) : Fin 5 × Fin 5) ∈ S)) (decide (((0, 4) : Fin 5 × Fin 5) ∈ S)) (decide (((3, 4) : Fin 5 × Fin 5) ∈ S)) := by
  ext e
  simp only [mk, Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq]
  constructor
  · intro he
    refine ⟨hS e he, ?_⟩
    have h := hS e he
    simp only [el, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [he]
  · rintro ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ <;> exact h

end PEqualNP.Outside.L_meta_345

theorem PEqualNP.Outside.L_meta_345 : ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] → ∀ S : Finset (Fin 5 × Fin 5), (∀ e ∈ S, e ∈ E) → S.Nonempty → ∃ C : Finset (Fin 5), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 5, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  rintro E rfl S hS hne
  have hEq := PEqualNP.Outside.L_meta_345.mk_eq S hS
  have key := PEqualNP.Outside.L_meta_345.main _ _ _ _ _ _ (by rw [← hEq]; exact hne)
  rw [← hEq] at key
  obtain ⟨C, h1, h2, h3⟩ := key
  exact ⟨C, fun A hA => of_decide_eq_true h1 A (Finset.mem_powerset.mpr hA), of_decide_eq_true h2, of_decide_eq_true h3⟩
