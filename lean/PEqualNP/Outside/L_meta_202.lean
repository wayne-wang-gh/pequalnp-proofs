import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_202_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def appendWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldl_appendWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl appendWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [appendWire]
    omega

private theorem readEarlierWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl appendWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (appendWire w g).length := by simp [appendWire]; omega
    rw [List.foldl_cons, ih (appendWire w g) hi']
    simp only [appendWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem set_prefix_wire (gs : List Gate) (w : List Bool) (j : ℕ) (g' : Gate) (i : ℕ)
    (hi : i < w.length + j) :
    ((gs.set j g').foldl appendWire w).getD i false = (gs.foldl appendWire w).getD i false := by
  induction gs generalizing w j with
  | nil => simp
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hi
      change ((g' :: gs).foldl appendWire w).getD i false =
        ((g :: gs).foldl appendWire w).getD i false
      rw [List.foldl_cons, List.foldl_cons]
      rw [readEarlierWire gs (appendWire w g') i (by simp [appendWire]; omega)]
      rw [readEarlierWire gs (appendWire w g) i (by simp [appendWire]; omega)]
      simp only [appendWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    | succ j =>
      change ((g :: gs.set j g').foldl appendWire w).getD i false =
        ((g :: gs).foldl appendWire w).getD i false
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (appendWire w g) j
      simp only [appendWire, List.length_append, List.length_singleton]
      omega

private theorem alias_or_false (gs : List Gate) (w : List Bool) (j a h : ℕ)
    (hgate : gs[j]? = some ⟨GateOp.or, [a, h]⟩)
    (hh_lt : h < w.length + j)
    (hh_false : (gs.foldl appendWire w).getD h false = false) :
    (gs.set j ⟨GateOp.or, [a]⟩).foldl appendWire w = gs.foldl appendWire w := by
  induction gs generalizing w j with
  | nil => simp at hgate
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hgate
      rcases hgate with rfl
      simp only [Nat.add_zero] at hh_lt
      rw [List.foldl_cons] at hh_false
      rw [readEarlierWire gs (appendWire w ⟨GateOp.or, [a, h]⟩) h (by simp [appendWire]; omega)] at hh_false
      have hwh : w[h]?.getD false = false := by
        simpa [appendWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hh_lt] using hh_false
      have heq : appendWire w ⟨GateOp.or, [a]⟩ = appendWire w ⟨GateOp.or, [a, h]⟩ := by
        simp [appendWire, GateOp.eval, hwh]
      change gs.foldl appendWire (appendWire w ⟨GateOp.or, [a]⟩) =
        gs.foldl appendWire (appendWire w ⟨GateOp.or, [a, h]⟩)
      rw [heq]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hgate
      change (gs.set j ⟨GateOp.or, [a]⟩).foldl appendWire (appendWire w g) =
        gs.foldl appendWire (appendWire w g)
      apply ih (appendWire w g) j hgate
      · simp only [appendWire, List.length_append, List.length_singleton]
        omega
      · simpa [List.foldl_cons] using hh_false

private theorem mem_of_mem_set {α : Type*} {xs : List α} {j : ℕ} {v x : α}
    (hx : x ∈ xs.set j v) : x = v ∨ x ∈ xs := by
  induction xs generalizing j with
  | nil => simp at hx
  | cons y ys ih =>
    cases j with
    | zero =>
      change x ∈ v :: ys at hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem y hx)
    | succ j =>
      change x ∈ y :: ys.set j v at hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr (by simp)
      · rcases ih hx with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem y hx')

private theorem getD_append_singleton_length (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

private theorem main :
    ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.FanInTwo { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } ∧ PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } = PEqualNP.MetaComplexity.circuitFun n C := by
  intro n j a h C hfan hgate hh_lt hh_out
  refine ⟨?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · rcases mem_of_mem_set hg with rfl | hg
      · simp
      · exact hfan g hg
    · rw [List.mem_singleton] at hg
      subst hg
      simp
  · funext x
    let g_new : Gate := ⟨GateOp.or, [a]⟩
    let g_top : Gate := ⟨GateOp.or, [C.output, h]⟩
    change ({ gates := C.gates.set j g_new ++ [g_top], output := n + C.size } : Circuit).eval (List.ofFn x) =
      C.eval (List.ofFn x)
    let w' := (C.gates.set j g_new).foldl appendWire (List.ofFn x)
    have hw'_len : w'.length = n + C.size := by
      dsimp [w']
      rw [foldl_appendWire_length, List.length_ofFn, List.length_set]
      rfl
    have h_wires' :
        ({ gates := C.gates.set j g_new ++ [g_top], output := n + C.size } : Circuit).wires (List.ofFn x) =
          appendWire w' g_top := by
      change (C.gates.set j g_new ++ [g_top]).foldl appendWire (List.ofFn x) = appendWire w' g_top
      rw [List.foldl_append]
      rfl
    have h_eval' :
        ({ gates := C.gates.set j g_new ++ [g_top], output := n + C.size } : Circuit).eval (List.ofFn x) =
          (w'.getD C.output false || w'.getD h false) := by
      change (({ gates := C.gates.set j g_new ++ [g_top], output := n + C.size } : Circuit).wires (List.ofFn x)).getD (n + C.size) false = _
      rw [h_wires']
      simp only [appendWire, ← hw'_len, getD_append_singleton_length]
      simp [g_top, GateOp.eval]
    rw [h_eval']
    cases hh : (C.wires (List.ofFn x)).getD h false with
    | true =>
      have hw'_h : w'.getD h false = true := by
        dsimp [w']
        rw [set_prefix_wire C.gates (List.ofFn x) j g_new h (by rw [List.length_ofFn]; exact hh_lt)]
        exact hh
      have h_out_true : C.eval (List.ofFn x) = true := hh_out x hh
      rw [hw'_h, h_out_true, Bool.or_true]
    | false =>
      have hw'_eq : w' = C.wires (List.ofFn x) := by
        dsimp [w']
        exact alias_or_false C.gates (List.ofFn x) j a h hgate (by rw [List.length_ofFn]; exact hh_lt) hh
      have hw'_h : w'.getD h false = false := by
        rw [hw'_eq]
        exact hh
      rw [hw'_h, Bool.or_false, hw'_eq]
      rfl

end PEqualNP.Outside.L_meta_202_aux

theorem PEqualNP.Outside.L_meta_202 :
    ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.FanInTwo { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } ∧ PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } = PEqualNP.MetaComplexity.circuitFun n C := by
  exact PEqualNP.Outside.L_meta_202_aux.main
