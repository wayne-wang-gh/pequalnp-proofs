import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_928_aux

theorem edgeCons (x : Fin 8 → Bool) (a b : ℕ) (ha : a < 8) (hb : b < 8) (es : List (ℕ × ℕ)) :
    (∃ u v : Fin 8, (u.val, v.val) ∈ (a, b) :: es ∧ x u = true ∧ x v = true) ↔
    (x ⟨a, ha⟩ = true ∧ x ⟨b, hb⟩ = true) ∨
      ∃ u v : Fin 8, (u.val, v.val) ∈ es ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Or.inl ⟨(show u = ⟨a, ha⟩ from Fin.ext h1) ▸ hu, (show v = ⟨b, hb⟩ from Fin.ext h2) ▸ hv⟩
    · exact Or.inr ⟨u, v, h, hu, hv⟩
  · rintro (⟨h1, h2⟩ | ⟨u, v, h, hu, hv⟩)
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, List.mem_cons_self, h1, h2⟩
    · exact ⟨u, v, List.mem_cons_of_mem _ h, hu, hv⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem part1 : ∀ C1 : PEqualNP.CircuitLowerBounds.Circuit, C1 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C1 ∧ C1.size = 7 ∧ (∀ x1 : Fin 8 → Bool, (C1.eval (List.ofFn x1) = true ↔ ∃ u1 v1 : Fin 8, (u1.val, v1.val) ∈ ([(0, 7), (1, 7), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x1 u1 = true ∧ x1 v1 = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [edgeCons x 0 7 (by decide) (by decide)]
    rw [edgeCons x 1 7 (by decide) (by decide)]
    rw [edgeCons x 2 7 (by decide) (by decide)]
    rw [edgeCons x 3 7 (by decide) (by decide)]
    rw [edgeCons x 4 7 (by decide) (by decide)]
    rw [edgeCons x 5 7 (by decide) (by decide)]
    rw [edgeCons x 6 7 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    revert x
    decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem part2 : ∀ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C2 ∧ C2.size = 7 ∧ (∀ x2 : Fin 8 → Bool, (C2.eval (List.ofFn x2) = true ↔ ∃ u2 v2 : Fin 8, (u2.val, v2.val) ∈ ([(0, 1), (2, 3), (4, 5), (6, 7)] : List (ℕ × ℕ)) ∧ x2 u2 = true ∧ x2 v2 = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [edgeCons x 0 1 (by decide) (by decide)]
    rw [edgeCons x 2 3 (by decide) (by decide)]
    rw [edgeCons x 4 5 (by decide) (by decide)]
    rw [edgeCons x 6 7 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    revert x
    decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem part3 : ∀ C3 : PEqualNP.CircuitLowerBounds.Circuit, C3 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C3 ∧ C3.size = 7 ∧ (∀ x3 : Fin 8 → Bool, (C3.eval (List.ofFn x3) = true ↔ ∃ u3 v3 : Fin 8, (u3.val, v3.val) ∈ ([(0, 1), (2, 3), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x3 u3 = true ∧ x3 v3 = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [edgeCons x 0 1 (by decide) (by decide)]
    rw [edgeCons x 2 3 (by decide) (by decide)]
    rw [edgeCons x 4 7 (by decide) (by decide)]
    rw [edgeCons x 5 7 (by decide) (by decide)]
    rw [edgeCons x 6 7 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    revert x
    decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem part4 : ∀ C4 : PEqualNP.CircuitLowerBounds.Circuit, C4 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C4 ∧ C4.size = 7 ∧ (∀ x4 : Fin 8 → Bool, (C4.eval (List.ofFn x4) = true ↔ ∃ u4 v4 : Fin 8, (u4.val, v4.val) ∈ ([(0, 1), (2, 6), (3, 6), (4, 7), (5, 7)] : List (ℕ × ℕ)) ∧ x4 u4 = true ∧ x4 v4 = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [edgeCons x 0 1 (by decide) (by decide)]
    rw [edgeCons x 2 6 (by decide) (by decide)]
    rw [edgeCons x 3 6 (by decide) (by decide)]
    rw [edgeCons x 4 7 (by decide) (by decide)]
    rw [edgeCons x 5 7 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    revert x
    decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem part5 : ∀ C5 : PEqualNP.CircuitLowerBounds.Circuit, C5 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C5 ∧ C5.size = 7 ∧ (∀ x5 : Fin 8 → Bool, (C5.eval (List.ofFn x5) = true ↔ ∃ u5 v5 : Fin 8, (u5.val, v5.val) ∈ ([(0, 1), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x5 u5 = true ∧ x5 v5 = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [edgeCons x 0 1 (by decide) (by decide)]
    rw [edgeCons x 2 7 (by decide) (by decide)]
    rw [edgeCons x 3 7 (by decide) (by decide)]
    rw [edgeCons x 4 7 (by decide) (by decide)]
    rw [edgeCons x 5 7 (by decide) (by decide)]
    rw [edgeCons x 6 7 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    revert x
    decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem part6 : ∀ C6 : PEqualNP.CircuitLowerBounds.Circuit, C6 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C6 ∧ C6.size = 7 ∧ (∀ x6 : Fin 8 → Bool, (C6.eval (List.ofFn x6) = true ↔ ∃ u6 v6 : Fin 8, (u6.val, v6.val) ∈ ([(0, 6), (1, 6), (2, 6), (3, 7), (4, 7), (5, 7)] : List (ℕ × ℕ)) ∧ x6 u6 = true ∧ x6 v6 = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [edgeCons x 0 6 (by decide) (by decide)]
    rw [edgeCons x 1 6 (by decide) (by decide)]
    rw [edgeCons x 2 6 (by decide) (by decide)]
    rw [edgeCons x 3 7 (by decide) (by decide)]
    rw [edgeCons x 4 7 (by decide) (by decide)]
    rw [edgeCons x 5 7 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    revert x
    decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem part7 : ∀ C7 : PEqualNP.CircuitLowerBounds.Circuit, C7 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C7 ∧ C7.size = 7 ∧ (∀ x7 : Fin 8 → Bool, (C7.eval (List.ofFn x7) = true ↔ ∃ u7 v7 : Fin 8, (u7.val, v7.val) ∈ ([(0, 6), (1, 6), (2, 7), (3, 7), (4, 7), (5, 7)] : List (ℕ × ℕ)) ∧ x7 u7 = true ∧ x7 v7 = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [hx]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
    rw [edgeCons x 0 6 (by decide) (by decide)]
    rw [edgeCons x 1 6 (by decide) (by decide)]
    rw [edgeCons x 2 7 (by decide) (by decide)]
    rw [edgeCons x 3 7 (by decide) (by decide)]
    rw [edgeCons x 4 7 (by decide) (by decide)]
    rw [edgeCons x 5 7 (by decide) (by decide)]
    simp only [List.not_mem_nil, false_and, exists_false, or_false,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    revert x
    decide

end PEqualNP.Outside.L_meta_928_aux

theorem PEqualNP.Outside.L_meta_928 : (∀ C1 : PEqualNP.CircuitLowerBounds.Circuit, C1 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C1 ∧ C1.size = 7 ∧ (∀ x1 : Fin 8 → Bool, (C1.eval (List.ofFn x1) = true ↔ ∃ u1 v1 : Fin 8, (u1.val, v1.val) ∈ ([(0, 7), (1, 7), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x1 u1 = true ∧ x1 v1 = true))) ∧ (∀ C2 : PEqualNP.CircuitLowerBounds.Circuit, C2 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C2 ∧ C2.size = 7 ∧ (∀ x2 : Fin 8 → Bool, (C2.eval (List.ofFn x2) = true ↔ ∃ u2 v2 : Fin 8, (u2.val, v2.val) ∈ ([(0, 1), (2, 3), (4, 5), (6, 7)] : List (ℕ × ℕ)) ∧ x2 u2 = true ∧ x2 v2 = true))) ∧ (∀ C3 : PEqualNP.CircuitLowerBounds.Circuit, C3 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C3 ∧ C3.size = 7 ∧ (∀ x3 : Fin 8 → Bool, (C3.eval (List.ofFn x3) = true ↔ ∃ u3 v3 : Fin 8, (u3.val, v3.val) ∈ ([(0, 1), (2, 3), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x3 u3 = true ∧ x3 v3 = true))) ∧ (∀ C4 : PEqualNP.CircuitLowerBounds.Circuit, C4 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C4 ∧ C4.size = 7 ∧ (∀ x4 : Fin 8 → Bool, (C4.eval (List.ofFn x4) = true ↔ ∃ u4 v4 : Fin 8, (u4.val, v4.val) ∈ ([(0, 1), (2, 6), (3, 6), (4, 7), (5, 7)] : List (ℕ × ℕ)) ∧ x4 u4 = true ∧ x4 v4 = true))) ∧ (∀ C5 : PEqualNP.CircuitLowerBounds.Circuit, C5 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C5 ∧ C5.size = 7 ∧ (∀ x5 : Fin 8 → Bool, (C5.eval (List.ofFn x5) = true ↔ ∃ u5 v5 : Fin 8, (u5.val, v5.val) ∈ ([(0, 1), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x5 u5 = true ∧ x5 v5 = true))) ∧ (∀ C6 : PEqualNP.CircuitLowerBounds.Circuit, C6 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C6 ∧ C6.size = 7 ∧ (∀ x6 : Fin 8 → Bool, (C6.eval (List.ofFn x6) = true ↔ ∃ u6 v6 : Fin 8, (u6.val, v6.val) ∈ ([(0, 6), (1, 6), (2, 6), (3, 7), (4, 7), (5, 7)] : List (ℕ × ℕ)) ∧ x6 u6 = true ∧ x6 v6 = true))) ∧ (∀ C7 : PEqualNP.CircuitLowerBounds.Circuit, C7 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C7 ∧ C7.size = 7 ∧ (∀ x7 : Fin 8 → Bool, (C7.eval (List.ofFn x7) = true ↔ ∃ u7 v7 : Fin 8, (u7.val, v7.val) ∈ ([(0, 6), (1, 6), (2, 7), (3, 7), (4, 7), (5, 7)] : List (ℕ × ℕ)) ∧ x7 u7 = true ∧ x7 v7 = true))) :=
  ⟨PEqualNP.Outside.L_meta_928_aux.part1, PEqualNP.Outside.L_meta_928_aux.part2, PEqualNP.Outside.L_meta_928_aux.part3, PEqualNP.Outside.L_meta_928_aux.part4, PEqualNP.Outside.L_meta_928_aux.part5, PEqualNP.Outside.L_meta_928_aux.part6, PEqualNP.Outside.L_meta_928_aux.part7⟩
