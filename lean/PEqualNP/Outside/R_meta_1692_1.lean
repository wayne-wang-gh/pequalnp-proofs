import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Separate gate elimination for nested ANDs from the lower bound without nesting.
theorem PEqualNP.Outside.R_meta_1692_1 :
  (let diff : Finset (Fin 13) := {0, 1, 3, 9}
    let correct := fun C : Circuit =>
      (∀ p l : Fin 13, p - l ∈ diff → C.eval
        (List.ofFn (fun p' : Fin 13 => decide (p' = p)) ++
          List.ofFn (fun l' : Fin 13 => decide (l' = l))) = true) ∧
      (∀ Q : Finset (Fin 13), Q.card = 4 →
        (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2) → C.eval
          (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
            List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ diff))) = false)
    let nested := fun C : Circuit => ∃ i j : ℕ,
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j
    ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C → C.size < 64 → nested C →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ correct D ∧ D.size < C.size) →
  (let diff : Finset (Fin 13) := {0, 1, 3, 9}
    let correct := fun C : Circuit =>
      (∀ p l : Fin 13, p - l ∈ diff → C.eval
        (List.ofFn (fun p' : Fin 13 => decide (p' = p)) ++
          List.ofFn (fun l' : Fin 13 => decide (l' = l))) = true) ∧
      (∀ Q : Finset (Fin 13), Q.card = 4 →
        (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2) → C.eval
          (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
            List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ diff))) = false)
    let nested := fun C : Circuit => ∃ i j : ℕ,
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j
    ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C → ¬ nested C → 64 ≤ C.size) →
  ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  intro shrink flat gates out hops hreads hpositive hnegative
  let diff : Finset (Fin 13) := {0, 1, 3, 9}
  let correct := fun C : Circuit =>
    (∀ p l : Fin 13, p - l ∈ diff → C.eval
      (List.ofFn (fun p' : Fin 13 => decide (p' = p)) ++
        List.ofFn (fun l' : Fin 13 => decide (l' = l))) = true) ∧
    (∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2) → C.eval
        (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ diff))) = false)
  let nested := fun C : Circuit => ∃ i j : ℕ,
    (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j
  change (∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C → C.size < 64 → nested C →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ correct D ∧ D.size < C.size) at shrink
  change (∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C → ¬ nested C → 64 ≤ C.size) at flat
  have lower : ∀ n : ℕ, ∀ C : Circuit, C.size = n → Monotone2 C → ReadsBack 26 C →
      correct C → 64 ≤ C.size := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n smaller =>
      intro C hsize hmon hback hcorrect
      by_cases hnested : nested C
      · by_contra hbound
        have hbudget : C.size < 64 := by omega
        obtain ⟨D, hdmon, hdback, hdcorrect, hdsmall⟩ :=
          shrink C hmon hback hcorrect hbudget hnested
        have hdsize : D.size < n := hsize ▸ hdsmall
        have hdlower := smaller D.size hdsize D rfl hdmon hdback hdcorrect
        omega
      · exact flat C hmon hback hcorrect hnested
  let C : Circuit := ⟨gates, out⟩
  have hmon : Monotone2 C := by
    change ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hops
  have hback : ReadsBack 26 C := by
    intro j hj w hw
    have hj' : j < gates.length := hj
    change w ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs at hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hw
    exact hreads ⟨j, hj'⟩ w hw
  exact lower C.size C rfl hmon hback ⟨hpositive, hnegative⟩
