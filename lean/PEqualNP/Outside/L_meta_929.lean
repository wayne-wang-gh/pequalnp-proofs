import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_929_aux

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩], 2⟩

theorem k1 : ∀ a b : Bool, c1.eval [a, b] = ((a && b)) := by
  decide

theorem t1 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 1 ∧ ∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = (fun x : Fin 2 → Bool => (x 0 && x 1)) x := by
  refine ⟨c1, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c1]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k1 (x 0) (x 1)

def c2 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩], 4⟩

theorem k2 : ∀ a b c : Bool, c2.eval [a, b, c] = ((a && b) || (a && c)) := by
  decide

theorem t2 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 2 ∧ ∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) x := by
  refine ⟨c2, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c2]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k2 (x 0) (x 1) (x 2)

def c3 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

theorem k3 : ∀ a b c : Bool, c3.eval [a, b, c] = ((a && b) || (a && c) || (b && c)) := by
  decide

theorem t3 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) x := by
  refine ⟨c3, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c3]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k3 (x 0) (x 1) (x 2)

def c4 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

theorem k4 : ∀ a b c d : Bool, c4.eval [a, b, c, d] = ((a && b) || (c && d)) := by
  decide

theorem t4 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 3 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) x := by
  refine ⟨c4, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c4]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k4 (x 0) (x 1) (x 2) (x 3)

def c5 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.and, [0, 5]⟩], 6⟩

theorem k5 : ∀ a b c d : Bool, c5.eval [a, b, c, d] = ((a && b) || (a && c) || (a && d)) := by
  decide

theorem t5 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 3 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) x := by
  refine ⟨c5, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c5]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k5 (x 0) (x 1) (x 2) (x 3)

def c6 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩

theorem k6 : ∀ a b c d : Bool, c6.eval [a, b, c, d] = ((a && b) || (a && c) || (b && d)) := by
  decide

theorem t6 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) x := by
  refine ⟨c6, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c6]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k6 (x 0) (x 1) (x 2) (x 3)

def c7 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 7]⟩], 8⟩

theorem k7 : ∀ a b c d : Bool, c7.eval [a, b, c, d] = ((a && b) || (a && c) || (a && d) || (b && c)) := by
  decide

theorem t7 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) x := by
  refine ⟨c7, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c7]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k7 (x 0) (x 1) (x 2) (x 3)

def c8 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩], 8⟩

theorem k8 : ∀ a b c d e : Bool, c8.eval [a, b, c, d, e] = ((a && b) || (a && c) || (d && e)) := by
  decide

theorem t8 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) x := by
  refine ⟨c8, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c8]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k8 (x 0) (x 1) (x 2) (x 3) (x 4)

def c9 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩], 8⟩

theorem k9 : ∀ a b c d e : Bool, c9.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (a && e)) := by
  decide

theorem t9 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) x := by
  refine ⟨c9, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c9]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k9 (x 0) (x 1) (x 2) (x 3) (x 4)

def c10 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [7, 8]⟩], 9⟩

theorem k10 : ∀ a b c d e : Bool, c10.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (b && e)) := by
  decide

theorem t10 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) x := by
  refine ⟨c10, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c10]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k10 (x 0) (x 1) (x 2) (x 3) (x 4)

def c11 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 8]⟩], 10⟩

theorem k11 : ∀ a b c d e : Bool, c11.eval [a, b, c, d, e] = ((a && b) || (a && c) || (b && c) || (d && e)) := by
  decide

theorem t11 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) x := by
  refine ⟨c11, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c11]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k11 (x 0) (x 1) (x 2) (x 3) (x 4)

def c12 : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [6, 8]⟩], 9⟩

theorem k12 : ∀ a b c d e : Bool, c12.eval [a, b, c, d, e] = ((a && b) || (a && c) || (b && d) || (c && e)) := by
  decide

theorem t12 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) x := by
  refine ⟨c12, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c12]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k12 (x 0) (x 1) (x 2) (x 3) (x 4)

def c13 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩

theorem k13 : ∀ a b c d e : Bool, c13.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c)) := by
  decide

theorem t13 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) x := by
  refine ⟨c13, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c13]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k13 (x 0) (x 1) (x 2) (x 3) (x 4)

def c14 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩

theorem k14 : ∀ a b c d e : Bool, c14.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e)) := by
  decide

theorem t14 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) x := by
  refine ⟨c14, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c14]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k14 (x 0) (x 1) (x 2) (x 3) (x 4)

def c15 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

theorem k15 : ∀ a b c d e : Bool, c15.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e)) := by
  decide

theorem t15 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) x := by
  refine ⟨c15, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c15]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k15 (x 0) (x 1) (x 2) (x 3) (x 4)

def c16 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

theorem k16 : ∀ a b c d e : Bool, c16.eval [a, b, c, d, e] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && e)) := by
  decide

theorem t16 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) x := by
  refine ⟨c16, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c16]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k16 (x 0) (x 1) (x 2) (x 3) (x 4)

def c17 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem k17 : ∀ a b c d e : Bool, c17.eval [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && e)) := by
  decide

theorem t17 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) x := by
  refine ⟨c17, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c17]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k17 (x 0) (x 1) (x 2) (x 3) (x 4)

def c18 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 8]⟩], 10⟩

theorem k18 : ∀ a b c d e f : Bool, c18.eval [a, b, c, d, e, f] = ((a && b) || (c && d) || (e && f)) := by
  decide

theorem t18 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) x := by
  refine ⟨c18, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c18]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k18 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c19 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩

theorem k19 : ∀ a b c d e f : Bool, c19.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (e && f)) := by
  decide

theorem t19 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) x := by
  refine ⟨c19, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c19]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k19 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c20 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

theorem k20 : ∀ a b c d e f : Bool, c20.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && d) || (e && f)) := by
  decide

theorem t20 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) x := by
  refine ⟨c20, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c20]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k20 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c21 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [7, 9]⟩], 10⟩

theorem k21 : ∀ a b c d e f : Bool, c21.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (d && e) || (d && f)) := by
  decide

theorem t21 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x := by
  refine ⟨c21, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c21]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k21 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c22 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩], 10⟩

theorem k22 : ∀ a b c d e f : Bool, c22.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f)) := by
  decide

theorem t22 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) x := by
  refine ⟨c22, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c22]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k22 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c23 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [9, 10]⟩], 11⟩

theorem k23 : ∀ a b c d e f : Bool, c23.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f)) := by
  decide

theorem t23 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) x := by
  refine ⟨c23, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c23]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k23 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c24 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem k24 : ∀ a b c d e f : Bool, c24.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (e && f)) := by
  decide

theorem t24 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) x := by
  refine ⟨c24, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c24]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k24 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c25 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩

theorem k25 : ∀ a b c d e f : Bool, c25.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && e) || (b && f)) := by
  decide

theorem t25 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) x := by
  refine ⟨c25, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c25]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k25 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c26 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem k26 : ∀ a b c d e f : Bool, c26.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f)) := by
  decide

theorem t26 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) x := by
  refine ⟨c26, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c26]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k26 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c27 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩

theorem k27 : ∀ a b c d e f : Bool, c27.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && e) || (e && f)) := by
  decide

theorem t27 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) x := by
  refine ⟨c27, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c27]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k27 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c28 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem k28 : ∀ a b c d e f : Bool, c28.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && c) || (d && e) || (d && f)) := by
  decide

theorem t28 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x := by
  refine ⟨c28, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c28]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k28 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c29 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem k29 : ∀ a b c d e f : Bool, c29.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && f)) := by
  decide

theorem t29 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) x := by
  refine ⟨c29, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c29]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k29 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c30 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩

theorem k30 : ∀ a b c d e f : Bool, c30.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c)) := by
  decide

theorem t30 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) x := by
  refine ⟨c30, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c30]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k30 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c31 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem k31 : ∀ a b c d e f : Bool, c31.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f)) := by
  decide

theorem t31 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) x := by
  refine ⟨c31, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c31]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k31 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c32 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k32 : ∀ a b c d e f : Bool, c32.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f)) := by
  decide

theorem t32 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) x := by
  refine ⟨c32, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c32]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k32 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c33 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k33 : ∀ a b c d e f : Bool, c33.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (c && f)) := by
  decide

theorem t33 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) x := by
  refine ⟨c33, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c33]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k33 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c34 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k34 : ∀ a b c d e f : Bool, c34.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f)) := by
  decide

theorem t34 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) x := by
  refine ⟨c34, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c34]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k34 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c35 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k35 : ∀ a b c d e f : Bool, c35.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (d && f)) := by
  decide

theorem t35 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x := by
  refine ⟨c35, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c35]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k35 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c36 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k36 : ∀ a b c d e f : Bool, c36.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (e && f)) := by
  decide

theorem t36 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) x := by
  refine ⟨c36, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c36]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k36 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c37 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k37 : ∀ a b c d e f : Bool, c37.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && f)) := by
  decide

theorem t37 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) x := by
  refine ⟨c37, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c37]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k37 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c38 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩

theorem k38 : ∀ a b c d e f : Bool, c38.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && c) || (d && e) || (d && f) || (e && f)) := by
  decide

theorem t38 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x := by
  refine ⟨c38, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c38]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k38 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c39 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k39 : ∀ a b c d e f : Bool, c39.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (e && f)) := by
  decide

theorem t39 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x := by
  refine ⟨c39, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c39]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k39 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c40 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k40 : ∀ a b c d e f : Bool, c40.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (d && e)) := by
  decide

theorem t40 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) x := by
  refine ⟨c40, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c40]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k40 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c41 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k41 : ∀ a b c d e f : Bool, c41.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && e)) := by
  decide

theorem t41 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) x := by
  refine ⟨c41, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c41]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k41 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c42 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k42 : ∀ a b c d e f : Bool, c42.eval [a, b, c, d, e, f] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (e && f)) := by
  decide

theorem t42 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x := by
  refine ⟨c42, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c42]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k42 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def c43 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

theorem k43 : ∀ a b c d e f g : Bool, c43.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (d && e) || (f && g)) := by
  decide

theorem t43 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c43, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c43]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k43 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c44 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩

theorem k44 : ∀ a b c d e f g : Bool, c44.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (f && g)) := by
  decide

theorem t44 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c44, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c44]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k44 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c45 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k45 : ∀ a b c d e f g : Bool, c45.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (f && g)) := by
  decide

theorem t45 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c45, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c45]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k45 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c46 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem k46 : ∀ a b c d e f g : Bool, c46.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (e && f) || (e && g)) := by
  decide

theorem t46 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c46, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c46]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k46 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c47 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [13, 11]⟩], 14⟩

theorem k47 : ∀ a b c d e f g : Bool, c47.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && c) || (d && e) || (f && g)) := by
  decide

theorem t47 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c47, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c47]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k47 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c48 : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k48 : ∀ a b c d e f g : Bool, c48.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && d) || (c && e) || (f && g)) := by
  decide

theorem t48 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c48, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c48]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k48 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c49 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem k49 : ∀ a b c d e f g : Bool, c49.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && d) || (e && f) || (e && g)) := by
  decide

theorem t49 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c49, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c49]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k49 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c50 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩], 12⟩

theorem k50 : ∀ a b c d e f g : Bool, c50.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (a && g)) := by
  decide

theorem t50 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) x := by
  refine ⟨c50, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c50]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k50 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c51 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem k51 : ∀ a b c d e f g : Bool, c51.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && g)) := by
  decide

theorem t51 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) x := by
  refine ⟨c51, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c51]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k51 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c52 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k52 : ∀ a b c d e f g : Bool, c52.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (f && g)) := by
  decide

theorem t52 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) x := by
  refine ⟨c52, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c52]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k52 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c53 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩

theorem k53 : ∀ a b c d e f g : Bool, c53.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (b && g)) := by
  decide

theorem t53 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) x := by
  refine ⟨c53, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c53]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k53 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c54 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k54 : ∀ a b c d e f g : Bool, c54.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (c && g)) := by
  decide

theorem t54 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x := by
  refine ⟨c54, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c54]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k54 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c55 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩

theorem k55 : ∀ a b c d e f g : Bool, c55.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (f && g)) := by
  decide

theorem t55 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) x := by
  refine ⟨c55, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c55]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k55 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c56 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k56 : ∀ a b c d e f g : Bool, c56.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (f && g)) := by
  decide

theorem t56 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c56, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c56]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k56 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c57 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

theorem k57 : ∀ a b c d e f g : Bool, c57.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (f && g)) := by
  decide

theorem t57 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c57, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c57]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k57 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c58 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k58 : ∀ a b c d e f g : Bool, c58.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (e && f) || (e && g)) := by
  decide

theorem t58 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c58, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c58]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k58 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c59 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k59 : ∀ a b c d e f g : Bool, c59.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (b && f) || (c && g)) := by
  decide

theorem t59 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x := by
  refine ⟨c59, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c59]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k59 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c60 : Circuit := ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k60 : ∀ a b c d e f g : Bool, c60.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (d && g)) := by
  decide

theorem t60 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x := by
  refine ⟨c60, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c60]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k60 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c61 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k61 : ∀ a b c d e f g : Bool, c61.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && g)) := by
  decide

theorem t61 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c61, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c61]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k61 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c62 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [9, 12]⟩], 13⟩

theorem k62 : ∀ a b c d e f g : Bool, c62.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (e && f) || (e && g)) := by
  decide

theorem t62 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c62, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c62]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k62 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c63 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k63 : ∀ a b c d e f g : Bool, c63.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (e && f) || (f && g)) := by
  decide

theorem t63 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine ⟨c63, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c63]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k63 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c64 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k64 : ∀ a b c d e f g : Bool, c64.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (e && f) || (e && g) || (f && g)) := by
  decide

theorem t64 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c64, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c64]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k64 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c65 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

theorem k65 : ∀ a b c d e f g : Bool, c65.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && c) || (d && e) || (d && f) || (e && g)) := by
  decide

theorem t65 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c65, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c65]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k65 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c66 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

theorem k66 : ∀ a b c d e f g : Bool, c66.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && e) || (f && g)) := by
  decide

theorem t66 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨c66, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c66]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k66 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c67 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k67 : ∀ a b c d e f g : Bool, c67.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (e && g)) := by
  decide

theorem t67 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c67, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c67]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k67 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c68 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

theorem k68 : ∀ a b c d e f g : Bool, c68.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (a && g) || (b && c)) := by
  decide

theorem t68 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) x := by
  refine ⟨c68, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c68]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k68 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c69 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩

theorem k69 : ∀ a b c d e f g : Bool, c69.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (b && g)) := by
  decide

theorem t69 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) x := by
  refine ⟨c69, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c69]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k69 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c70 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k70 : ∀ a b c d e f g : Bool, c70.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (d && g)) := by
  decide

theorem t70 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) x := by
  refine ⟨c70, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c70]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k70 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c71 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [10, 13]⟩], 14⟩

theorem k71 : ∀ a b c d e f g : Bool, c71.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (b && g)) := by
  decide

theorem t71 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) x := by
  refine ⟨c71, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c71]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k71 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c72 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k72 : ∀ a b c d e f g : Bool, c72.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (c && g)) := by
  decide

theorem t72 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) x := by
  refine ⟨c72, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c72]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k72 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c73 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k73 : ∀ a b c d e f g : Bool, c73.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (d && g)) := by
  decide

theorem t73 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) x := by
  refine ⟨c73, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c73]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k73 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c74 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k74 : ∀ a b c d e f g : Bool, c74.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (b && f) || (f && g)) := by
  decide

theorem t74 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) x := by
  refine ⟨c74, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c74]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k74 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c75 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k75 : ∀ a b c d e f g : Bool, c75.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f) || (d && g)) := by
  decide

theorem t75 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) x := by
  refine ⟨c75, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c75]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k75 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c76 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k76 : ∀ a b c d e f g : Bool, c76.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && c) || (d && f) || (f && g)) := by
  decide

theorem t76 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) x := by
  refine ⟨c76, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c76]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k76 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c77 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k77 : ∀ a b c d e f g : Bool, c77.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (b && g) || (f && g)) := by
  decide

theorem t77 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c77, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c77]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k77 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c78 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k78 : ∀ a b c d e f g : Bool, c78.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (c && g) || (f && g)) := by
  decide

theorem t78 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c78, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c78]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k78 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c79 : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k79 : ∀ a b c d e f g : Bool, c79.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (c && f) || (d && g)) := by
  decide

theorem t79 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x := by
  refine ⟨c79, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c79]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k79 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c80 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k80 : ∀ a b c d e f g : Bool, c80.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (d && g)) := by
  decide

theorem t80 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) x := by
  refine ⟨c80, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c80]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k80 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c81 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k81 : ∀ a b c d e f g : Bool, c81.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (d && f) || (f && g)) := by
  decide

theorem t81 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) x := by
  refine ⟨c81, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c81]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k81 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c82 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k82 : ∀ a b c d e f g : Bool, c82.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && c) || (d && e) || (e && f) || (e && g)) := by
  decide

theorem t82 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c82, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c82]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k82 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c83 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k83 : ∀ a b c d e f g : Bool, c83.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (b && f) || (c && g) || (e && g)) := by
  decide

theorem t83 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) x := by
  refine ⟨c83, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c83]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k83 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c84 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k84 : ∀ a b c d e f g : Bool, c84.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && f) || (e && g)) := by
  decide

theorem t84 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) x := by
  refine ⟨c84, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c84]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k84 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def c85 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem k85 : ∀ a b c d e f g : Bool, c85.eval [a, b, c, d, e, f, g] = ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && g) || (f && g)) := by
  decide

theorem t85 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨c85, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c85]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k85 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

end PEqualNP.Outside.L_meta_929_aux

open PEqualNP.Outside.L_meta_929_aux in
theorem PEqualNP.Outside.L_meta_929 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 1 ∧ ∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = (fun x : Fin 2 → Bool => (x 0 && x 1)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 2 ∧ ∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 3 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 3 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) :=
  ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68, t69, t70, t71, t72, t73, t74, t75, t76, t77, t78, t79, t80, t81, t82, t83, t84, t85⟩
