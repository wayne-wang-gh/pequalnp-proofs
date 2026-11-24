import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1555

/-- The line number `s` of Z13. -/
def Lf (s : Fin 13) : Finset (Fin 13) := {s, s + 1, s + 3, s + 9}

/-- The table of bases. -/
def tbl : List (List (Finset (Fin 13))) := [
    [{4, 8}, {8}, ∅, {8}, ∅, ∅, ∅, ∅, ∅, {8}, ∅, ∅, ∅],
    [∅, {5}, {5}, ∅, {8}, ∅, ∅, ∅, ∅, ∅, {5}, ∅, ∅],
    [∅, ∅, {9}, {8}, ∅, {8}, ∅, ∅, ∅, ∅, ∅, {8}, ∅],
    [∅, ∅, ∅, {11}, {11}, ∅, {2}, ∅, ∅, ∅, ∅, ∅, {11}],
    [{3, 12}, ∅, ∅, ∅, {12}, {12}, ∅, {12}, ∅, ∅, ∅, ∅, ∅],
    [∅, {7}, ∅, ∅, ∅, {12}, {7}, ∅, {7}, ∅, ∅, ∅, ∅],
    [∅, ∅, {4}, ∅, ∅, ∅, {4}, {3}, ∅, {4}, ∅, ∅, ∅],
    [∅, ∅, ∅, {12}, ∅, ∅, ∅, {12}, {6}, ∅, {12}, ∅, ∅],
    [∅, ∅, ∅, ∅, {10}, ∅, ∅, ∅, {10}, {10}, ∅, {5}, ∅],
    [∅, ∅, ∅, ∅, ∅, {6}, ∅, ∅, ∅, {6}, {1}, ∅, {6}],
    [{1, 2}, ∅, ∅, ∅, ∅, ∅, {1}, ∅, ∅, ∅, {1}, {1}, ∅],
    [∅, {2}, ∅, ∅, ∅, ∅, ∅, {2}, ∅, ∅, ∅, {2}, {9}],
    [{6, 9}, ∅, {6}, ∅, ∅, ∅, ∅, ∅, {6}, ∅, ∅, ∅, {6}]]

/-- The given bases as a function, extended by the argument `B` off the lines. -/
def Bf (t p : Fin 13) : Finset (Fin 13) := (tbl.getD t.val []).getD p.val ∅

set_option maxRecDepth 100000 in
theorem concl : (∀ t : Fin 13, ∀ p ∈ Lf t, Bf t p ∩ Lf t = ∅ ∧ (∀ v ∈ Lf t, decide (v = p ∨ v ∈ Bf t p) = true ↔ v = p) ∧
      (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Lf t ∧ b ∈ Lf t) ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ Bf t p)) a = true ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ Bf t p)) b = true)) ∧
    (∀ s s' : Fin 13, s ≠ 12 → s' ≠ 12 → s ≠ s' → ¬ ((∃ p ∈ Lf s \ Lf s', (Bf s p ∩ Lf s').Nonempty) ∧ (∃ p ∈ Lf s' \ Lf s, (Bf s' p ∩ Lf s).Nonempty))) ∧
    (∀ s : Fin 13, s ≠ 12 → (((∃ p ∈ Lf 12 \ Lf s, (Bf 12 p ∩ Lf s).Nonempty) ∧ (∃ p ∈ Lf s \ Lf 12, (Bf s p ∩ Lf 12).Nonempty)) ↔ s = 3 ∨ s = 5)) ∧
    ((Lf 3 \ Lf 12).filter (fun p => (Bf 3 p ∩ Lf 12).Nonempty)) = {6} ∧ ((Lf 12 \ Lf 3).filter (fun p => (Bf 12 p ∩ Lf 3).Nonempty)) = {0, 2, 8} ∧
    ((Lf 5 \ Lf 12).filter (fun p => (Bf 5 p ∩ Lf 12).Nonempty)) = {5} ∧ ((Lf 12 \ Lf 5).filter (fun p => (Bf 12 p ∩ Lf 5).Nonempty)) = {0, 2, 12} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [Finset.nonempty_iff_ne_empty]) <;>
    decide +kernel

end PEqualNP.Outside.L_meta_1555

open PEqualNP.Outside.L_meta_1555 in
theorem PEqualNP.Outside.L_meta_1555 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ B : Fin 13 → Fin 13 → Finset (Fin 13),
    (B 0 0 = {4, 8} ∧ B 0 1 = {8} ∧ B 0 3 = {8} ∧ B 0 9 = {8}) →
    (B 1 1 = {5} ∧ B 1 2 = {5} ∧ B 1 4 = {8} ∧ B 1 10 = {5}) →
    (B 2 2 = {9} ∧ B 2 3 = {8} ∧ B 2 5 = {8} ∧ B 2 11 = {8}) →
    (B 3 3 = {11} ∧ B 3 4 = {11} ∧ B 3 6 = {2} ∧ B 3 12 = {11}) →
    (B 4 0 = {3, 12} ∧ B 4 4 = {12} ∧ B 4 5 = {12} ∧ B 4 7 = {12}) →
    (B 5 1 = {7} ∧ B 5 5 = {12} ∧ B 5 6 = {7} ∧ B 5 8 = {7}) →
    (B 6 2 = {4} ∧ B 6 6 = {4} ∧ B 6 7 = {3} ∧ B 6 9 = {4}) →
    (B 7 3 = {12} ∧ B 7 7 = {12} ∧ B 7 8 = {6} ∧ B 7 10 = {12}) →
    (B 8 4 = {10} ∧ B 8 8 = {10} ∧ B 8 9 = {10} ∧ B 8 11 = {5}) →
    (B 9 5 = {6} ∧ B 9 9 = {6} ∧ B 9 10 = {1} ∧ B 9 12 = {6}) →
    (B 10 0 = {1, 2} ∧ B 10 6 = {1} ∧ B 10 10 = {1} ∧ B 10 11 = {1}) →
    (B 11 1 = {2} ∧ B 11 7 = {2} ∧ B 11 11 = {2} ∧ B 11 12 = {9}) →
    (B 12 0 = {6, 9} ∧ B 12 2 = {6} ∧ B 12 8 = {6} ∧ B 12 12 = {6}) →
    (∀ t : Fin 13, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ (∀ v ∈ L t, decide (v = p ∨ v ∈ B t p) = true ↔ v = p) ∧
      (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) a = true ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) b = true)) ∧
    (∀ s s' : Fin 13, s ≠ 12 → s' ≠ 12 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) ∧
    (∀ s : Fin 13, s ≠ 12 → (((∃ p ∈ L 12 \ L s, (B 12 p ∩ L s).Nonempty) ∧ (∃ p ∈ L s \ L 12, (B s p ∩ L 12).Nonempty)) ↔ s = 3 ∨ s = 5)) ∧
    ((L 3 \ L 12).filter (fun p => (B 3 p ∩ L 12).Nonempty)) = {6} ∧ ((L 12 \ L 3).filter (fun p => (B 12 p ∩ L 3).Nonempty)) = {0, 2, 8} ∧
    ((L 5 \ L 12).filter (fun p => (B 5 p ∩ L 12).Nonempty)) = {5} ∧ ((L 12 \ L 5).filter (fun p => (B 12 p ∩ L 5).Nonempty)) = {0, 2, 12} := by
  intro L hL B h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hLf : L = Lf := by funext s; rw [hL s]; rfl
  subst hLf
  have hB : ∀ t p : Fin 13, p ∈ Lf t → B t p = Bf t p := by
    intro t p hp
    fin_cases t <;> fin_cases p <;> first
      | (exfalso; revert hp; decide)
      | (simp only [Bf, tbl]; simp_all)
  have ex : ∀ s s' : Fin 13, (∃ p ∈ Lf s \ Lf s', (B s p ∩ Lf s').Nonempty) ↔
      (∃ p ∈ Lf s \ Lf s', (Bf s p ∩ Lf s').Nonempty) := by
    intro s s'
    constructor
    · rintro ⟨p, hp, h⟩
      exact ⟨p, hp, by rw [← hB s p (Finset.mem_sdiff.1 hp).1]; exact h⟩
    · rintro ⟨p, hp, h⟩
      exact ⟨p, hp, by rw [hB s p (Finset.mem_sdiff.1 hp).1]; exact h⟩
  have fl : ∀ s s' : Fin 13, (Lf s \ Lf s').filter (fun p => (B s p ∩ Lf s').Nonempty) =
      (Lf s \ Lf s').filter (fun p => (Bf s p ∩ Lf s').Nonempty) := by
    intro s s'
    apply Finset.filter_congr
    intro p hp
    rw [hB s p (Finset.mem_sdiff.1 hp).1]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := concl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t p hp
    rw [hB t p hp]
    exact c1 t p hp
  · intro s s' h1 h2 h3
    rw [ex s s', ex s' s]
    exact c2 s s' h1 h2 h3
  · intro s hs
    rw [ex 12 s, ex s 12]
    exact c3 s hs
  · rw [fl 3 12]; exact c4
  · rw [fl 12 3]; exact c5
  · rw [fl 5 12]; exact c6
  · rw [fl 12 5]; exact c7
