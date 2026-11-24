import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation

namespace PEqualNP.Outside.L_meta_344

abbrev Vertex := Fin 15
abbrev Edge := Vertex × Vertex

def allEdges : List Edge := [(0, 1), (0, 4), (0, 5), (0, 6), (1, 2), (1, 6), (1, 7), (2, 3), (2, 7), (2, 8), (3, 4), (3, 8), (3, 9), (4, 5), (4, 9), (5, 10), (5, 13), (6, 11), (6, 14), (7, 10), (7, 12), (8, 11), (8, 13), (9, 12), (9, 14), (10, 12), (10, 13), (11, 13), (11, 14), (12, 14)]

def witness : List Edge := [(0, 4), (0, 5), (0, 6), (1, 2), (1, 6), (1, 7), (2, 3), (2, 8), (3, 4), (3, 9), (4, 5), (4, 9), (5, 10), (5, 13), (6, 11), (6, 14), (7, 10), (7, 12), (8, 11), (8, 13), (9, 12), (9, 14), (10, 13), (11, 13), (11, 14), (12, 14)]

def neighbors : Vertex → List Vertex := ![[4, 5, 6], [2, 6, 7], [1, 3, 8], [2, 4, 9], [0, 3, 5, 9], [0, 4, 10, 13], [0, 1, 11, 14], [1, 10, 12], [2, 11, 13], [3, 4, 12, 14], [5, 7, 13], [6, 8, 13, 14], [7, 9, 14], [5, 8, 10, 11], [6, 9, 11, 12]]

theorem neighbors_correct : ∀ i j : Vertex, j ∈ neighbors i ↔
    (j, i) ∈ witness.toFinset ∨ (i, j) ∈ witness.toFinset := by decide

def toggle (hit parity : Bool) : Bool := if hit then !parity else parity

def oddHits (f : Vertex → Bool) : List Edge → Bool
  | [] => false
  | e :: es => toggle (f e.1 || f e.2) (oddHits f es)

def boundary (f : Vertex → Bool) (v : Vertex) : Bool := !f v && (neighbors v).any f

def violated (f : Vertex → Bool) : Bool :=
  allEdges.any fun e => boundary f e.1 && boundary f e.2

theorem boundary_spec (C : Finset Vertex) (v : Vertex)
    (h : boundary (fun i => decide (i ∈ C)) v = true) :
    v ∉ C ∧ ∃ u ∈ C, (u, v) ∈ witness.toFinset ∨ (v, u) ∈ witness.toFinset := by
  have hs : v ∉ C ∧ ∃ u ∈ neighbors v, u ∈ C := by
    simpa [boundary, List.any_eq_true] using h
  obtain ⟨hv, u, hu, hc⟩ := hs
  exact ⟨hv, u, hc, (neighbors_correct v u).mp hu⟩

theorem flipOdd (k : ℕ) : decide ((k + 1) % 2 = 1) = !decide (k % 2 = 1) := by
  by_cases h : k % 2 = 1
  · have h' : (k + 1) % 2 ≠ 1 := by omega
    simp [h, h']
  · have h' : (k + 1) % 2 = 1 := by omega
    simp [h, h']

theorem oddHits_spec (C : Finset Vertex) (es : List Edge) (hd : es.Nodup) :
    oddHits (fun i => decide (i ∈ C)) es =
      decide ((es.toFinset.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1) := by
  induction es with
  | nil => simp [oddHits]
  | cons e es ih =>
    obtain ⟨he, hd'⟩ := List.nodup_cons.mp hd
    have hs : e ∉ es.toFinset.filter (fun z => z.1 ∈ C ∨ z.2 ∈ C) := by
      intro h
      exact he (List.mem_toFinset.mp (Finset.mem_filter.mp h).1)
    by_cases present : e.1 ∈ C ∨ e.2 ∈ C
    · have b : (decide (e.1 ∈ C) || decide (e.2 ∈ C)) = true := by simpa using present
      simp only [oddHits, toggle, b, ite_true, List.toFinset_cons, Finset.filter_insert, present,
        Finset.card_insert_of_notMem hs, flipOdd, ih hd']
    · have b : (decide (e.1 ∈ C) || decide (e.2 ∈ C)) = false := by simpa using present
      simp [oddHits, toggle, b, List.toFinset_cons, Finset.filter_insert, present, ih hd']

def booleanCheck (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Bool) : Bool :=
  let b0 := !x0 && ([x4, x5, x6] : List Bool).any id
  let b1 := !x1 && ([x2, x6, x7] : List Bool).any id
  let b2 := !x2 && ([x1, x3, x8] : List Bool).any id
  let b3 := !x3 && ([x2, x4, x9] : List Bool).any id
  let b4 := !x4 && ([x0, x3, x5, x9] : List Bool).any id
  let b5 := !x5 && ([x0, x4, x10, x13] : List Bool).any id
  let b6 := !x6 && ([x0, x1, x11, x14] : List Bool).any id
  let b7 := !x7 && ([x1, x10, x12] : List Bool).any id
  let b8 := !x8 && ([x2, x11, x13] : List Bool).any id
  let b9 := !x9 && ([x3, x4, x12, x14] : List Bool).any id
  let b10 := !x10 && ([x5, x7, x13] : List Bool).any id
  let b11 := !x11 && ([x6, x8, x13, x14] : List Bool).any id
  let b12 := !x12 && ([x7, x9, x14] : List Bool).any id
  let b13 := !x13 && ([x5, x8, x10, x11] : List Bool).any id
  let b14 := !x14 && ([x6, x9, x11, x12] : List Bool).any id
  let parity := toggle (x0 || x4) (toggle (x0 || x5) (toggle (x0 || x6) (toggle (x1 || x2) (toggle (x1 || x6) (toggle (x1 || x7) (toggle (x2 || x3) (toggle (x2 || x8) (toggle (x3 || x4) (toggle (x3 || x9) (toggle (x4 || x5) (toggle (x4 || x9) (toggle (x5 || x10) (toggle (x5 || x13) (toggle (x6 || x11) (toggle (x6 || x14) (toggle (x7 || x10) (toggle (x7 || x12) (toggle (x8 || x11) (toggle (x8 || x13) (toggle (x9 || x12) (toggle (x9 || x14) (toggle (x10 || x13) (toggle (x11 || x13) (toggle (x11 || x14) (toggle (x12 || x14) (false))))))))))))))))))))))))))
  !parity || ([b0 && b1, b0 && b4, b0 && b5, b0 && b6, b1 && b2, b1 && b6, b1 && b7, b2 && b3, b2 && b7, b2 && b8, b3 && b4, b3 && b8, b3 && b9, b4 && b5, b4 && b9, b5 && b10, b5 && b13, b6 && b11, b6 && b14, b7 && b10, b7 && b12, b8 && b11, b8 && b13, b9 && b12, b9 && b14, b10 && b12, b10 && b13, b11 && b13, b11 && b14, b12 && b14] : List Bool).any id

set_option maxHeartbeats 8000000 in
theorem finiteCheck : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Bool, booleanCheck x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 = true := by decide

set_option maxRecDepth 12000 in
theorem test (f : Vertex → Bool) (h : oddHits f witness = true) : violated f = true := by
  have proof : (!oddHits f witness || violated f) = true :=
    finiteCheck (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) (f 11) (f 12) (f 13) (f 14)
  simpa [h] using proof

end PEqualNP.Outside.L_meta_344

theorem PEqualNP.Outside.L_meta_344 : ∀ E : List (Fin 15 × Fin 15), E = [(0, 1), (0, 4), (0, 5), (0, 6), (1, 2), (1, 6), (1, 7), (2, 3), (2, 7), (2, 8), (3, 4), (3, 8), (3, 9), (4, 5), (4, 9), (5, 10), (5, 13), (6, 11), (6, 14), (7, 10), (7, 12), (8, 11), (8, 13), (9, 12), (9, 14), (10, 12), (10, 13), (11, 13), (11, 14), (12, 14)] → ∃ S : Finset (Fin 15 × Fin 15), (∀ e ∈ S, e ∈ E) ∧ S.Nonempty ∧ ¬ ∃ C : Finset (Fin 15), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 15, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  intro E hE
  subst E
  refine ⟨PEqualNP.Outside.L_meta_344.witness.toFinset, ?_, ?_, ?_⟩
  · decide
  · decide
  · rintro ⟨C, _, hb, hodd⟩
    have h : PEqualNP.Outside.L_meta_344.oddHits (fun i => decide (i ∈ C)) PEqualNP.Outside.L_meta_344.witness = true := by
      rw [PEqualNP.Outside.L_meta_344.oddHits_spec C _ (by decide)]
      exact decide_eq_true hodd
    have hv := PEqualNP.Outside.L_meta_344.test _ h
    obtain ⟨⟨a,b⟩, he, hab⟩ := List.any_eq_true.mp hv
    obtain ⟨ha,hb'⟩ := Bool.and_eq_true_iff.mp hab
    obtain ⟨oa, na⟩ := PEqualNP.Outside.L_meta_344.boundary_spec C a ha
    obtain ⟨ob, nb⟩ := PEqualNP.Outside.L_meta_344.boundary_spec C b hb'
    exact hb a b oa ob na nb (Or.inl he)
