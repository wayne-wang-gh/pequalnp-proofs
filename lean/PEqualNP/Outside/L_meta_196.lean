import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_196

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wireCount (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step, Nat.add_comm, Nat.add_left_comm]

lemma keepWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

-- Both circuits retain the earlier wire. When it is false the edited gate
-- computes the same value, so even the later wires agree.
lemma dropInput (gs : List Gate) (w : List Bool) (j a h : ℕ)
    (gate : gs[j]? = some ⟨.or, [a,h]⟩) (early : h < w.length + j) :
    let old := gs.foldl step w
    let new := (gs.set j ⟨.or, [a]⟩).foldl step w
    new.getD h false = old.getD h false ∧ (old.getD h false = false → new = old) := by
  induction gs generalizing w j with
  | nil => simp at gate
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at gate
      subst g
      have lt : h < w.length := by simpa using early
      have oldRead := keepWire (⟨.or, [a,h]⟩ :: gs) w h lt
      have newRead := keepWire (⟨.or, [a]⟩ :: gs) w h lt
      refine ⟨newRead.trans oldRead.symm, fun hf => ?_⟩
      have off := oldRead.symm.trans hf
      change gs.foldl step (step w ⟨.or, [a]⟩) = gs.foldl step (step w ⟨.or, [a,h]⟩)
      congr 1
      change w ++ [w.getD a false || false] = w ++ [w.getD a false || (w.getD h false || false)]
      simp only [off, Bool.or_false]
    | succ j =>
      apply ih (step w g) j gate
      simp only [step, List.length_append, List.length_singleton]
      omega

end PEqualNP.Outside.L_meta_196

theorem PEqualNP.Outside.L_meta_196 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  open PEqualNP.Outside.L_meta_196 in
  intro n j a h C f gate early x err
  let w := List.ofFn x
  let gs := C.gates.set j ⟨.or, [a]⟩
  let new := gs.foldl step w
  let old := C.gates.foldl step w
  obtain ⟨kept, same⟩ := dropInput C.gates w j a h gate (by simpa [w] using early)
  change new.getD h false = old.getD h false at kept
  change old.getD h false = false → new = old at same
  have len : new.length = n + C.size := by simp [new, gs, wireCount, w, Circuit.size]
  change ((gs ++ [(⟨.or, [C.output,h]⟩ : Gate)]).foldl step w).getD (n + C.size) false ≠ f x at err
  rw [List.foldl_append] at err
  change (new ++ [new.getD C.output false || (new.getD h false || false)]).getD (n + C.size) false ≠ f x at err
  rw [← len] at err
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some] at err
  change (new.getD C.output false || (new.getD h false || false)) ≠ f x at err
  rw [Bool.or_false, kept] at err
  change old.getD C.output false ≠ f x ∨ (old.getD h false = true ∧ f x = false)
  cases bit : old.getD h false with
  | false => exact Or.inl (by simpa only [bit, Bool.or_false, same bit] using err)
  | true =>
    right
    refine ⟨rfl, ?_⟩
    cases val : f x with
    | false => rfl
    | true => exact (err (by rw [bit, Bool.or_true, val])).elim
