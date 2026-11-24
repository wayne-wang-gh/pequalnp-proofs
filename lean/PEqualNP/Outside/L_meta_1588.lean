import Mathlib
import PEqualNP.Defs

-- The colour-merging proof is adapted from public PR3043, L-meta-1512.
-- The wire evaluation lemmas below are reused from L-meta-1516.
namespace PEqualNP.Outside.L_meta_1588
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

-- The value of wire `w` on input `x`.
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

def carries {N : ℕ} (gs : List Gate) (M R : Finset (Fin N)) (a : Fin gs.length) : Prop :=
  (gs.get a).op = GateOp.and ∧ val gs (N + (a : ℕ)) (base M) = false ∧
    ∃ r ∈ R, val gs (N + (a : ℕ)) (test M r) = true

lemma route {N : ℕ} (gs : List Gate) (M R : Finset (Fin N))
    (ch : Fin gs.length → ℕ)
    (leg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (valid : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + (i : ℕ))
    (chosen : ∀ a : Fin gs.length, carries gs M R a →
      ch a ∈ (gs.get a).inputs ∧ val gs (ch a) (base M) = false)
    (r : Fin N) (hr : r ∈ R) :
    ∀ w : ℕ, val gs w (base M) = false → val gs w (test M r) = true →
      reach N gs w r ∨ ∃ a : Fin gs.length, carries gs M R a ∧ reach N gs (ch a) r := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hz ht
    by_cases hw : w < N
    · rw [val_input gs _ w hw] at hz ht
      have hm : (⟨w, hw⟩ : Fin N) ∈ M := by simpa [base] using hz
      have he : (⟨w, hw⟩ : Fin N) = r := by simpa [test, hm] using ht
      left
      intro S hs _
      have he' : w = (r : ℕ) := congrArg Fin.val he
      simpa [← he'] using hs
    · have hb : w < N + gs.length := by
        by_contra hn
        rw [val_big gs _ w (by omega)] at ht
        contradiction
      let a : Fin gs.length := ⟨w - N, by omega⟩
      have wa : w = N + (a : ℕ) := by dsimp [a]; omega
      have hleg := (leg (gs.get a) (List.get_mem gs a)).1
      rcases hleg with hand | hor
      · have hc : carries gs M R a := ⟨hand, wa ▸ hz, r, hr, wa ▸ ht⟩
        obtain ⟨hmem, hzero⟩ := chosen a hc
        have htrue : val gs (ch a) (test M r) = true := by
          have h := (val_and gs (test M r) a a.isLt hand).mp (wa ▸ ht)
          exact (h (ch a) hmem).2
        have hlt : ch a < w := by rw [wa]; exact (valid a).2 _ hmem
        rcases ih (ch a) hlt hzero htrue with hreach | hrest
        · exact Or.inr ⟨a, hc, hreach⟩
        · exact Or.inr hrest
      · obtain ⟨v, hmem, hvlt, hvtrue⟩ :=
          (val_or gs (test M r) a a.isLt hor).mp (wa ▸ ht)
        have hvzero : val gs v (base M) = false := by
          cases he : val gs v (base M) with
          | false => rfl
          | true =>
            have h := (val_or gs (base M) a a.isLt hor).mpr ⟨v, hmem, hvlt, he⟩
            rw [← wa, hz] at h
            contradiction
        rcases ih v (by omega) hvzero hvtrue with hreach | hrest
        · left
          intro S hs hclosed
          exact hreach S (hclosed a (wa ▸ hs) hor v hmem) hclosed
        · exact Or.inr hrest

end PEqualNP.Outside.L_meta_1588

theorem PEqualNP.Outside.L_meta_1588 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (ch : Fin gates.length → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) →
    (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) → ch a ∈ (gates.get a).inputs ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, ch a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) →
    (∀ r ∈ L i0 \ T0, (∀ S : Set ℕ, o ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S) ∨
      ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧ (∀ S : Set ℕ, ch a ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S)) ∧
    (∀ a : Fin gates.length, o = N + (a : ℕ) → (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true)) := by
  intro q m N L i0 T0 hq hm hmq hN hcard hinter hjoin hsub hT gs o ch hleg hvalid hz ht hch
  constructor
  · intro r hr
    exact PEqualNP.Outside.L_meta_1588.route gs (L i0) (L i0 \ T0) ch hleg hvalid hch r hr o hz (ht r hr)
  · intro a ha hop
    refine ⟨hop, ha ▸ hz, ?_⟩
    have hnonempty : (L i0 \ T0).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff_of_subset hsub, hcard i0, hT]
      omega
    obtain ⟨r, hr⟩ := hnonempty
    exact ⟨r, hr, ha ▸ ht r hr⟩
