import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1557
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

/-- The value of wire `w` on input `x`. -/
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

end PEqualNP.Outside.L_meta_1557

open PEqualNP.Outside.L_meta_1557 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1557 : ∀ (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (B : Fin n → Finset (Fin n))
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : Fin gates.length) (q q' : Fin n),
    L ∩ M = {m} → (∀ r ∈ L, B r ∩ L = ∅) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    q ∈ L → q' ∈ L → q ≠ q' →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = q ∨ v ∈ B q))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = q' ∨ v ∈ B q'))) = true →
    ∃ a : Fin gates.length, (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ∀ T : Finset (Fin gates.length), g ∈ T →
        (∀ i ∈ T, ∀ g' : Fin gates.length, n + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → a ∈ T := by
  classical
  intro n L M m B gates g q q' hLM hB hleg hq hq' hne hfL hfM htq htq'
  rw [eval_eq] at hfL hfM htq htq'
  by_contra hcon
  push_neg at hcon
  -- the cone of `g`: the gates in every closed set holding `g`
  let Closed : Finset (Fin gates.length) → Prop := fun T =>
    ∀ i ∈ T, ∀ g' : Fin gates.length, n + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T
  let C : Finset (Fin gates.length) :=
    Finset.univ.filter fun i => ∀ T : Finset (Fin gates.length), g ∈ T → Closed T → i ∈ T
  have hgC : g ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun T h _ => h
  have hCcl : ∀ i ∈ C, ∀ g' : Fin gates.length, n + (g' : ℕ) ∈ (gates.get i).inputs → g' < i →
      g' ∈ C := by
    intro i hi g' hin hlt
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro T hgT hT
    exact hT i (hi T hgT hT) g' hin hlt
  have hor : ∀ i ∈ C, (gates.get i).op = GateOp.or := by
    intro i hi
    rcases (hleg (gates.get i) (List.get_mem gates i)).1 with h | h
    · exfalso
      obtain ⟨T, hgT, hT, hiT⟩ := hcon i h
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hiT (hi T hgT hT)
    · exact h
  -- a true wire of the cone is forced by one true input
  have key : ∀ (k : ℕ) (i : Fin gates.length), i.val < k → i ∈ C → ∀ x : Fin n → Bool,
      val gates (n + i.val) x = true →
      ∃ v : Fin n, x v = true ∧ ∀ z : Fin n → Bool, z v = true → val gates (n + i.val) z = true := by
    intro k
    induction k with
    | zero => intro i hi; omega
    | succ k ih =>
      intro i hi hiC x hx
      have hop : gates[i.val].op = GateOp.or := hor i hiC
      obtain ⟨w, hw, hwlt, hwx⟩ := (val_or gates x i.val i.isLt hop).1 hx
      by_cases hwn : w < n
      · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
        · rw [val_input gates x w hwn] at hwx; exact hwx
        · intro z hz
          refine (val_or gates z i.val i.isLt hop).2 ⟨w, hw, hwlt, ?_⟩
          rw [val_input gates z w hwn]; exact hz
      · have hg'lt : w - n < gates.length := by have := i.isLt; omega
        have hweq : w = n + (w - n) := by omega
        have hg'C : (⟨w - n, hg'lt⟩ : Fin gates.length) ∈ C := by
          apply hCcl i hiC ⟨w - n, hg'lt⟩
          · show n + (w - n) ∈ gates[i.val].inputs
            rw [← hweq]; exact hw
          · show w - n < i.val
            omega
        rw [hweq] at hwx
        obtain ⟨v, hv, hforce⟩ := ih ⟨w - n, hg'lt⟩ (by show w - n < k; omega) hg'C x hwx
        refine ⟨v, hv, fun z hz => ?_⟩
        refine (val_or gates z i.val i.isLt hop).2 ⟨w, hw, hwlt, ?_⟩
        rw [hweq]; exact hforce z hz
  have point : ∀ r ∈ L, val gates (n + g.val) (fun v : Fin n => decide (v = r ∨ v ∈ B r)) = true →
      r = m := by
    intro r hr htr
    obtain ⟨v, hv, hforce⟩ := key (g.val + 1) g (by omega) hgC _ htr
    have hvL : v ∈ L := by
      by_contra hvn
      have := hforce (fun v : Fin n => decide (v ∉ L)) (by simpa using hvn)
      rw [val] at this
      rw [this] at hfL
      exact absurd hfL (by simp)
    have hvM : v ∈ M := by
      by_contra hvn
      have := hforce (fun v : Fin n => decide (v ∉ M)) (by simpa using hvn)
      rw [val] at this
      rw [this] at hfM
      exact absurd hfM (by simp)
    have hvm : v = m := by
      have : v ∈ L ∩ M := Finset.mem_inter.2 ⟨hvL, hvM⟩
      rw [hLM] at this
      simpa using this
    rcases of_decide_eq_true hv with h | h
    · rw [← h, hvm]
    · exfalso
      have : v ∈ B r ∩ L := Finset.mem_inter.2 ⟨h, hvL⟩
      rw [hB r hr] at this
      simp at this
  exact hne ((point q hq htq).trans (point q' hq' htq').symm)
