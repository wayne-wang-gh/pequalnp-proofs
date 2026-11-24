import PEqualNP.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Fin.Basic

namespace PEqualNP.Outside.L_meta_1578
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

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

-- The value of wire w on input x.
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

theorem earlier_pass (gates : List Gate) {n : ℕ} (z : Fin gates.length)
    (x x0 xt : Fin n → Bool)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hpoint : ∀ p, x0 p = false → xt p = false → x p = false)
    (hand : ∀ i : Fin gates.length, i < z → (gates.get i).op = GateOp.and →
      val gates (n + i.val) x0 = false → val gates (n + i.val) xt = false →
      val gates (n + i.val) x = false) :
    ∀ w, w < n + z.val → val gates w x0 = false → val gates w x = true →
      val gates w xt = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h0 hx
    cases ht : val gates w xt
    · exfalso
      by_cases hp : w < n
      · rw [val_input gates x0 w hp] at h0
        rw [val_input gates xt w hp] at ht
        rw [val_input gates x w hp] at hx
        simp [hpoint _ h0 ht] at hx
      let i : Fin gates.length := ⟨w - n, by have := z.isLt; omega⟩
      have hi : i < z := by
        change w - n < z.val
        omega
      have eq : n + i.val = w := by dsimp [i]; omega
      rw [← eq] at h0 ht hx
      rcases hops (gates.get i) (List.get_mem gates i) with ha | ho
      · exact Bool.noConfusion ((hand i hi ha h0 ht).symm.trans hx)
      · obtain ⟨r, hmem, hlt, hrx⟩ := (val_or gates x i.val i.isLt ho).mp hx
        have hr0 : val gates r x0 = false := by
          cases hr : val gates r x0
          · rfl
          · exact Bool.noConfusion (h0.symm.trans
              ((val_or gates x0 i.val i.isLt ho).mpr ⟨r, hmem, hlt, hr⟩))
        have hrt := ih r (by omega) (by omega) hr0 hrx
        exact Bool.noConfusion (ht.symm.trans
          ((val_or gates xt i.val i.isLt ho).mpr ⟨r, hmem, hlt, hrt⟩))
    · rfl

def side (t : Fin 13) : Prop :=
  t ∈ ({4, 10, 12} : Finset (Fin 13)) ∨ t ∈ ({1, 5, 11} : Finset (Fin 13))

def line (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def co (L : Fin 13 → Finset (Fin 13)) (t p : Fin 13) : Bool := decide (p ∉ L t)

def heavy (L : Fin 13 → Finset (Fin 13)) (r p : Fin 13) : Bool :=
  decide (p = r ∨ p ∉ L 0)

theorem side_ne : ∀ t, side t → t ≠ 0 := by
  unfold side
  decide

theorem side_disjoint_heavy : ∀ t r p : Fin 13, side t →
    (r = 3 ∨ r = 9) → co line 0 p = false → co line t p = false →
      heavy line r p = false := by
  unfold side
  decide

end PEqualNP.Outside.L_meta_1578

open PEqualNP.Outside.L_meta_1578 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1578 :
∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = true) →
    (∀ i : Fin gates.length, i < zs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
      ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 3 ∨ ((3 = 3 ∨ 3 = 9) ∧ v ∉ L 0)))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 9 ∨ ((9 = 3 ∨ 9 = 9) ∧ v ∉ L 0)))) = false) →
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) ∨
    (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, v⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = true) := by
  intro L hL gates zs u v l m hG _ hLside hMside hAnd hInputs hz0 hzL hzM hzHeavy hMin
  have hLines : L = line := funext hL
  have hclassL : side l := Or.inl hLside
  have hclassM : side m := Or.inr hMside
  have hchoose : ∃ r : Fin 13, (r = 3 ∨ r = 9) ∧
      val gates (13 + zs.val) (heavy L r) = true := by
    rcases hzHeavy with h | h
    · exact ⟨3, Or.inl rfl, by simpa [val, wf, Circuit.eval, Circuit.wires, heavy] using h⟩
    · exact ⟨9, Or.inr rfl, by simpa [val, wf, Circuit.eval, Circuit.wires, heavy] using h⟩
  obtain ⟨r, hr, hztrue⟩ := hchoose
  have good : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hG g hg).1
  have operands := (val_and gates (heavy L r) zs.val zs.isLt hAnd).mp hztrue
  change gates[zs.val].inputs = [u, v] at hInputs
  rw [hInputs] at operands
  obtain ⟨hub, hut⟩ := operands u (by simp)
  obtain ⟨hvb, hvt⟩ := operands v (by simp)
  have passes (w : ℕ) (hw : w < 13 + zs.val) (hw0 : val gates w (co L 0) = false)
      (hwt : val gates w (heavy L r) = true) (t : Fin 13) (ht : side t) :
      val gates w (co L t) = true := by
    apply earlier_pass gates zs (heavy L r) (co L 0) (co L t) good
    · rw [hLines]
      exact fun p => side_disjoint_heavy t r p ht hr
    · intro i hi hop hi0 hit
      have h := hMin i hi hop hi0 t (side_ne t ht) hit
      rcases hr with rfl | rfl
      · simpa [val, wf, Circuit.eval, Circuit.wires, heavy] using h.1
      · simpa [val, wf, Circuit.eval, Circuit.wires, heavy] using h.2
    · exact hw
    · exact hw0
    · exact hwt
  have splitZero (x : Fin 13 → Bool) (hx : val gates (13 + zs.val) x = false) :
      val gates u x = false ∨ val gates v x = false := by
    cases hu : val gates u x
    · exact Or.inl rfl
    cases hv : val gates v x
    · exact Or.inr rfl
    exfalso
    have hz := (val_and gates x zs.val zs.isLt hAnd).mpr (by
      rw [hInputs]
      intro w hw
      simp at hw
      rcases hw with rfl | rfl
      · exact ⟨hub, hu⟩
      · exact ⟨hvb, hv⟩)
    exact Bool.noConfusion (hx.symm.trans hz)
  have hzl := splitZero (co L l) hzL
  have hzm := splitZero (co L m) hzM
  have true0 (w : ℕ) (hw : w < 13 + zs.val) (hwt : val gates w (heavy L r) = true)
      (hwl : val gates w (co L l) = false) : val gates w (co L 0) = true := by
    cases h : val gates w (co L 0)
    · exact Bool.noConfusion (hwl.symm.trans (passes w hw h hwt l hclassL))
    · rfl
  rcases splitZero (co L 0) hz0 with hu0 | hv0
  · have hul := passes u hub hu0 hut l hclassL
    have hum := passes u hub hu0 hut m hclassM
    have hvl : val gates v (co L l) = false := hzl.resolve_left (by simp [hul])
    have hvm : val gates v (co L m) = false := hzm.resolve_left (by simp [hum])
    exact Or.inr ⟨hvl, hvm, true0 v hvb hvt hvl, hu0, hul, hum⟩
  · have hvl := passes v hvb hv0 hvt l hclassL
    have hvm := passes v hvb hv0 hvt m hclassM
    have hul : val gates u (co L l) = false := hzl.resolve_right (by simp [hvl])
    have hum : val gates u (co L m) = false := hzm.resolve_right (by simp [hvm])
    exact Or.inl ⟨hul, hum, true0 u hub hut hul, hv0, hvl, hvm⟩
