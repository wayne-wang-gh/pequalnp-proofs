import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_983_aux

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

theorem k1 : ∀ a b c d e f : Bool, c1.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (d && f) || (e && f)) := by
  decide

theorem t1 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x := by
  refine ⟨c1, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c1]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c2 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem k2 : ∀ a b c d e f g : Bool, c2.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && e) || (f && g)) := by
  decide

theorem t2 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c2, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c2]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k2 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c3 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem k3 : ∀ a b c d e f g : Bool, c3.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f) || (e && g)) := by
  decide

theorem t3 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c3, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c3]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k3 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c4 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem k4 : ∀ a b c d e f g : Bool, c4.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (e && g)) := by
  decide

theorem t4 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c4, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c4]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k4 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c5 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem k5 : ∀ a b c d e f g : Bool, c5.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (d && f) || (e && g)) := by
  decide

theorem t5 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c5, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c5]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k5 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c6 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem k6 : ∀ a b c d e f g : Bool, c6.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (e && f) || (f && g)) := by
  decide

theorem t6 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine ⟨c6, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c6]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k6 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c7 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem k7 : ∀ a b c d e f g : Bool, c7.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (e && f) || (e && g) || (f && g)) := by
  decide

theorem t7 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c7, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c7]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c8 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem k8 : ∀ a b c d e f g : Bool, c8.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (d && g) || (e && f)) := by
  decide

theorem t8 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x := by
  refine ⟨c8, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c8]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k8 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c9 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem k9 : ∀ a b c d e f g : Bool, c9.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (e && g) || (f && g)) := by
  decide

theorem t9 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c9, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c9]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k9 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c10 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k10 : ∀ a b c d e f g : Bool, c10.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (a && g) || (b && c) || (d && e)) := by
  decide

theorem t10 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x := by
  refine ⟨c10, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c10]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k10 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c11 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k11 : ∀ a b c d e f g : Bool, c11.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (b && g) || (d && e)) := by
  decide

theorem t11 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x := by
  refine ⟨c11, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c11]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k11 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c12 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k12 : ∀ a b c d e f g : Bool, c12.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (d && e) || (f && g)) := by
  decide

theorem t12 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c12, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c12]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k12 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c13 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k13 : ∀ a b c d e f g : Bool, c13.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (b && g) || (d && e)) := by
  decide

theorem t13 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x := by
  refine ⟨c13, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c13]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k13 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c14 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k14 : ∀ a b c d e f g : Bool, c14.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (c && g) || (d && e)) := by
  decide

theorem t14 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x := by
  refine ⟨c14, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c14]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k14 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c15 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k15 : ∀ a b c d e f g : Bool, c15.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && e) || (d && g)) := by
  decide

theorem t15 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x := by
  refine ⟨c15, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c15]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k15 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c16 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k16 : ∀ a b c d e f g : Bool, c16.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && e) || (f && g)) := by
  decide

theorem t16 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c16, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c16]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k16 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c17 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k17 : ∀ a b c d e f g : Bool, c17.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && g) || (f && g)) := by
  decide

theorem t17 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c17, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c17]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k17 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c18 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k18 : ∀ a b c d e f g : Bool, c18.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f) || (d && g) || (f && g)) := by
  decide

theorem t18 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c18, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c18]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k18 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c19 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k19 : ∀ a b c d e f g : Bool, c19.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f) || (e && g) || (f && g)) := by
  decide

theorem t19 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c19, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c19]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k19 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c20 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k20 : ∀ a b c d e f g : Bool, c20.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (c && f) || (d && g) || (e && g)) := by
  decide

theorem t20 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x := by
  refine ⟨c20, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c20]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k20 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c21 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k21 : ∀ a b c d e f g : Bool, c21.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (d && g) || (e && f)) := by
  decide

theorem t21 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x := by
  refine ⟨c21, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c21]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k21 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c22 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k22 : ∀ a b c d e f g : Bool, c22.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (d && g) || (f && g)) := by
  decide

theorem t22 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c22, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c22]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k22 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c23 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [12, 6]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k23 : ∀ a b c d e f g : Bool, c23.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (e && f) || (f && g)) := by
  decide

theorem t23 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine ⟨c23, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c23]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k23 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c24 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k24 : ∀ a b c d e f g : Bool, c24.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (e && g) || (f && g)) := by
  decide

theorem t24 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c24, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c24]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k24 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c25 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k25 : ∀ a b c d e f g : Bool, c25.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (e && f) || (e && g) || (f && g)) := by
  decide

theorem t25 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c25, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c25]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k25 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c26 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k26 : ∀ a b c d e f g : Bool, c26.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (d && g) || (e && f) || (e && g)) := by
  decide

theorem t26 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c26, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c26]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k26 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c27 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem k27 : ∀ a b c d e f g : Bool, c27.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (a && g) || (b && c) || (d && e) || (f && g)) := by
  decide

theorem t27 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c27, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c27]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k27 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c28 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem k28 : ∀ a b c d e f g : Bool, c28.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (b && g) || (d && e) || (f && g)) := by
  decide

theorem t28 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c28, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c28]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k28 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c29 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem k29 : ∀ a b c d e f g : Bool, c29.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && e) || (d && g) || (f && g)) := by
  decide

theorem t29 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c29, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c29]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k29 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c30 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [13, 5]⟩, ⟨GateOp.and, [6, 14]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [16, 12]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem k30 : ∀ a b c d e f g : Bool, c30.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (c && f) || (d && g) || (e && g) || (f && g)) := by
  decide

theorem t30 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c30, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c30]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k30 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c31 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 14]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [16, 13]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

theorem k31 : ∀ a b c d e f g : Bool, c31.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (d && g) || (e && f) || (f && g)) := by
  decide

theorem t31 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine ⟨c31, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c31]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k31 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

end PEqualNP.Outside.L_meta_983_aux

open PEqualNP.Outside.L_meta_983_aux in
theorem PEqualNP.Outside.L_meta_983 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) :=
  ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31⟩
