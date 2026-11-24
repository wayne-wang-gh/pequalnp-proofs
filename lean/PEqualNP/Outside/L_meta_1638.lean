import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1638
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

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def reach (N : ℕ) (gs : List Gate) (w v : ℕ) : Prop :=
  ∀ S : Set ℕ, w ∈ S →
    (∀ i : Fin gs.length, N + (i : ℕ) ∈ S → (gs.get i).op = GateOp.or →
      ∀ a ∈ (gs.get i).inputs, a ∈ S) → v ∈ S

def base {N : ℕ} (M : Finset (Fin N)) (v : Fin N) : Bool := decide (v ∉ M)

def test {N : ℕ} (M : Finset (Fin N)) (r v : Fin N) : Bool := decide (v ∉ M ∨ v = r)

lemma reach_false {N : ℕ} (gs : List Gate) (M : Finset (Fin N))
    (valid : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < N + (i : ℕ))
    (u : ℕ) (hu : val gs u (base M) = false) (Y : ℕ) (hY : reach N gs u Y) :
    val gs Y (base M) = false := by
  refine hY {w | val gs w (base M) = false} hu ?_
  intro i hi hor e he
  show val gs e (base M) = false
  cases hv : val gs e (base M) with
  | false => rfl
  | true =>
    have h := (val_or gs (base M) i i.isLt hor).mpr ⟨e, he, valid i e he, hv⟩
    have hi' : val gs (N + (i : ℕ)) (base M) = false := hi
    rw [hi'] at h
    contradiction

lemma rim {N : ℕ} (gs : List Gate) (M : Finset (Fin N))
    (leg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (valid : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < N + (i : ℕ))
    (u : ℕ) (hu : val gs u (base M) = false) (r : Fin N) :
    ∀ w : ℕ, reach N gs u w → val gs w (test M r) = true →
      reach N gs u r ∨ ∃ a : ℕ, reach N gs u a ∧
        (∃ i : Fin gs.length, a = N + (i : ℕ) ∧ (gs.get i).op = GateOp.and) ∧
        val gs a (test M r) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hreach ht
    have hz := reach_false gs M valid u hu w hreach
    by_cases hw : w < N
    · rw [val_input gs _ w hw] at hz ht
      have hm : (⟨w, hw⟩ : Fin N) ∈ M := by simpa [base] using hz
      have he : (⟨w, hw⟩ : Fin N) = r := by simpa [test, hm] using ht
      have he' : w = (r : ℕ) := congrArg Fin.val he
      left
      rw [← he']
      exact hreach
    · have hb : w < N + gs.length := by
        by_contra hn
        rw [val_big gs _ w (by omega)] at ht
        contradiction
      let a : Fin gs.length := ⟨w - N, by omega⟩
      have wa : w = N + (a : ℕ) := by dsimp [a]; omega
      have hleg := (leg (gs.get a) (List.get_mem gs a)).1
      rcases hleg with hand | hor
      · exact Or.inr ⟨w, hreach, ⟨a, wa, hand⟩, ht⟩
      · obtain ⟨v, hmem, hvlt, hvtrue⟩ :=
          (val_or gs (test M r) a a.isLt hor).mp (wa ▸ ht)
        have hrv : reach N gs u v := fun S hs hcl =>
          hcl a (wa ▸ hreach S hs hcl) hor v hmem
        exact ih v (by omega) hrv hvtrue

theorem main_aux : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 hq hm hmq hN hcard hinter hjoin hsub hT gs u hleg hlen hlt hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y hY
    exact reach_false gs (L i0) hlt u hz Y hY
  · intro p hp
    have h := reach_false gs (L i0) hlt u hz (p : ℕ) hp
    rw [val_input gs _ (p : ℕ) p.isLt] at h
    simpa [base] using h
  · intro r hr ht
    exact rim gs (L i0) hleg hlt u hz r u (fun S hs _ => hs) ht
  · intro a c hop hz' hc hcz r hr ht
    exact ((val_and gs (test (L i0) r) a a.isLt hop).mp ht c hc).2

end PEqualNP.Outside.L_meta_1638

theorem PEqualNP.Outside.L_meta_1638 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) :=
  PEqualNP.Outside.L_meta_1638.main_aux
