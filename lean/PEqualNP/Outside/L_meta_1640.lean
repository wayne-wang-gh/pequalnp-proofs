import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1640
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

def Cl (gates : List Gate) (n : ℕ) (w : ℕ) (r : ℕ) : Prop :=
  ∀ S : Set ℕ, w ∈ S → (∀ i : Fin gates.length, n + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → r ∈ S

theorem core {n : ℕ} (gates : List Gate) (x0 xr : Fin n → Bool) (r : Fin n)
    (hin : ∀ v : Fin n, x0 v = false → xr v = true → v = r)
    (ch : Fin gates.length → ℕ)
    (hop : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hch : ∀ a : Fin gates.length, (gates.get a).op = GateOp.and → val gates (n + (a : ℕ)) x0 = false →
      val gates (n + (a : ℕ)) xr = true → ch a ∈ (gates.get a).inputs ∧ val gates (ch a) x0 = false) :
    ∀ w, val gates w x0 = false → val gates w xr = true →
      Cl gates n w (r : ℕ) ∨ ∃ a : Fin gates.length, (gates.get a).op = GateOp.and ∧
        val gates (n + (a : ℕ)) x0 = false ∧ val gates (n + (a : ℕ)) xr = true ∧ Cl gates n (ch a) (r : ℕ) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h0 h1
    by_cases hw : w < n
    · left
      rw [val_input gates _ w hw] at h0 h1
      have hv := hin ⟨w, hw⟩ h0 h1
      intro S hS _
      rw [← hv]; exact hS
    by_cases hg : w < n + gates.length
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      have h0' : val gates (n + (w - n)) x0 = false := by rw [he]; exact h0
      have h1' : val gates (n + (w - n)) xr = true := by rw [he]; exact h1
      rcases hop gates[w - n] (List.getElem_mem hi) with ha | ho
      · have hs := (val_and gates xr (w - n) hi ha).mp h1'
        obtain ⟨hc1, hc2⟩ := hch ⟨w - n, hi⟩ ha h0' h1'
        obtain ⟨hlt, hct⟩ := hs _ hc1
        rcases ih _ (by omega) hc2 hct with h | h
        · right; exact ⟨⟨w - n, hi⟩, ha, h0', h1', h⟩
        · right; exact h
      · obtain ⟨c, hc, hlt, hct⟩ := (val_or gates xr (w - n) hi ho).mp h1'
        have hc0 : val gates c x0 = false := by
          cases hv : val gates c x0 with
          | false => rfl
          | true =>
            have h2 := (val_or gates x0 (w - n) hi ho).mpr ⟨c, hc, hlt, hv⟩
            rw [h0'] at h2
            exact absurd h2 (by simp)
        rcases ih c (by omega) hc0 hct with h | h
        · left
          intro S hS hcl
          refine h S ?_ hcl
          have hS' : n + (w - n) ∈ S := by rw [he]; exact hS
          exact hcl ⟨w - n, hi⟩ hS' ho c hc
        · right; exact h
    · rw [val_big gates xr w (by omega)] at h1
      exact absurd h1 (by simp)

end PEqualNP.Outside.L_meta_1640

theorem PEqualNP.Outside.L_meta_1640 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (ch : Fin gates.length → ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) →
    (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) → ch a ∈ (gates.get a).inputs ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, ch a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) →
    (∀ r ∈ L i0 \ T0, (∀ S : Set ℕ, o ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨
      ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) ∧ (∀ S : Set ℕ, ch a ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S)) ∧
    (∀ a : Fin gates.length, o = N + (a : ℕ) → (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true)) := by
  intro q m N L i0 T0 hq hm hmq hN hL hI hP hT hTc gates o ch hg hrb1 hrb2 h0 hr hch
  have hne : (L i0 \ T0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
    have h2 := Finset.card_le_card h
    rw [hL, hTc] at h2
    omega
  refine ⟨?_, ?_⟩
  · intro r hrm
    have hrL : r ∈ L i0 := (Finset.mem_sdiff.mp hrm).1
    have hin : ∀ v : Fin N, (fun v : Fin N => decide (v ∉ L i0)) v = false →
        (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true → v = r := by
      intro v h0 h1
      simp at h0 h1
      tauto
    have hch' : ∀ a : Fin gates.length, (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.Outside.L_meta_1640.val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
        PEqualNP.Outside.L_meta_1640.val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true →
        ch a ∈ (gates.get a).inputs ∧
          PEqualNP.Outside.L_meta_1640.val gates (ch a) (fun v : Fin N => decide (v ∉ L i0)) = false := by
      intro a ha ha0 ha1
      exact hch a ⟨ha, ha0, r, hrm, ha1⟩
    have key := PEqualNP.Outside.L_meta_1640.core gates (fun v : Fin N => decide (v ∉ L i0))
      (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) r hin ch (fun g hg' => (hg g hg').1) hch' o h0 (hr r hrm)
    rcases key with h | ⟨a, ha, ha0, ha1, hcl⟩
    · left; exact h
    · right; exact ⟨a, ⟨ha, ha0, r, hrm, ha1⟩, hcl⟩
  · intro a hoa hand
    obtain ⟨r, hrm⟩ := hne
    refine ⟨hand, ?_, r, hrm, ?_⟩
    · rw [← hoa]; exact h0
    · rw [← hoa]; exact hr r hrm
