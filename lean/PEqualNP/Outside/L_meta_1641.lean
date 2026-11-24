import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1641

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

def vl {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) : Bool :=
  value (⟨gates, 0⟩ : Circuit) x w

lemma vl_input {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h : w < N) :
    vl gates x w = x ⟨w, h⟩ :=
  input_value (⟨gates, 0⟩ : Circuit) x ⟨w, h⟩

lemma vl_missing {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : N + gates.length ≤ w) : vl gates x w = false :=
  missing_value (⟨gates, 0⟩ : Circuit) x w hw

lemma vl_and {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h13 : N ≤ w)
    (hw : w < N + gates.length) (hop : (gates[w - N]'(by omega)).op = GateOp.and) :
    vl gates x w = true ↔
      ∀ r ∈ (gates[w - N]'(by omega)).inputs, r < w ∧ vl gates x r = true := by
  have h := gate_value (⟨gates, 0⟩ : Circuit) x w h13 hw
  simp only at h
  unfold vl
  rw [h, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
  constructor
  · intro hall r hr
    have := hall _ ⟨r, hr, rfl⟩
    by_cases hrw : r < w
    · simpa [hrw] using this
    · simp [hrw] at this
  · rintro hall b ⟨r, hr, rfl⟩
    have := hall r hr
    simp [this.1, this.2]

lemma vl_or {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h13 : N ≤ w)
    (hw : w < N + gates.length) (hop : (gates[w - N]'(by omega)).op = GateOp.or) :
    vl gates x w = true ↔
      ∃ r ∈ (gates[w - N]'(by omega)).inputs, r < w ∧ vl gates x r = true := by
  have h := gate_value (⟨gates, 0⟩ : Circuit) x w h13 hw
  simp only at h
  unfold vl
  rw [h, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
  constructor
  · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    by_cases hrw : r < w
    · exact ⟨r, hr, hrw, by simpa [hrw] using hb⟩
    · simp [hrw] at hb
  · rintro ⟨r, hr, hrw, hv⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by simp [hrw, hv]⟩

lemma vl_mono {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, vl gates x w = true → vl gates y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases h13 : w < N
    · rw [vl_input gates x w h13] at hx
      rw [vl_input gates y w h13]
      exact hxy _ hx
    · by_cases hw : w < N + gates.length
      · have hk : w - N < gates.length := by omega
        rcases hg (gates[w - N]) (List.getElem_mem hk) with hop | hop
        · rw [vl_and gates x w (by omega) hw hop] at hx
          rw [vl_and gates y w (by omega) hw hop]
          intro r hr
          exact ⟨(hx r hr).1, ih r (hx r hr).1 (hx r hr).2⟩
        · rw [vl_or gates x w (by omega) hw hop] at hx
          rw [vl_or gates y w (by omega) hw hop]
          obtain ⟨r, hr, hlt, hv⟩ := hx
          exact ⟨r, hr, hlt, ih r hlt hv⟩
      · rw [vl_missing gates x w (by omega)] at hx
        exact Bool.noConfusion hx


lemma vl_or_fin {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (k : Fin gates.length)
    (hop : (gates.get k).op = GateOp.or) :
    vl gates x (N + (k : ℕ)) = true ↔
      ∃ r ∈ (gates.get k).inputs, r < N + (k : ℕ) ∧ vl gates x r = true := by
  have e : N + (k : ℕ) - N = k := by omega
  have h := vl_or gates x (N + (k : ℕ)) (by omega) (by have := k.2; omega)
    (by simpa only [e, List.get_eq_getElem] using hop)
  simpa only [e, List.get_eq_getElem] using h

lemma two_inputs (l : List ℕ) (h2 : l.length ≤ 2) (h1 : 1 ≤ l.length) :
    ∃ e1 e2, e1 ∈ l ∧ e2 ∈ l ∧ ∀ e ∈ l, e = e1 ∨ e = e2 := by
  match l, h2, h1 with
  | [a], _, _ => exact ⟨a, a, by simp, by simp, by simp⟩
  | [a, b], _, _ => exact ⟨a, b, by simp, by simp, by simp⟩
  | [], _, h => simp only [List.length_nil] at h; omega
  | _ :: _ :: _ :: _, h, _ => simp only [List.length_cons] at h; omega

lemma tele {n : ℕ} (c : ℕ → ℕ) (Xs : Finset (Fin n))
    (h : ∀ j : Fin n, c j ≤ c ((j : ℕ) + 1) + 1 ∧ (j ∉ Xs → c j ≤ c ((j : ℕ) + 1))) :
    c 0 ≤ Xs.card + c n := by
  have key : ∀ k : ℕ, k ≤ n →
      c 0 ≤ (Xs.filter (fun i : Fin n => (i : ℕ) < k)).card + c k := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hk' : k < n := by omega
      have hj : c k ≤ c (k + 1) + 1 ∧ ((⟨k, hk'⟩ : Fin n) ∉ Xs → c k ≤ c (k + 1)) := h ⟨k, hk'⟩
      have hsub : Xs.filter (fun i : Fin n => (i : ℕ) < k) ⊆
          Xs.filter (fun i : Fin n => (i : ℕ) < k + 1) := by
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, by omega⟩
      by_cases hx : (⟨k, hk'⟩ : Fin n) ∈ Xs
      · have hlt : (Xs.filter (fun i : Fin n => (i : ℕ) < k)).card <
            (Xs.filter (fun i : Fin n => (i : ℕ) < k + 1)).card := by
          apply Finset.card_lt_card
          refine (Finset.ssubset_iff_of_subset hsub).2 ⟨⟨k, hk'⟩, ?_, ?_⟩
          · exact Finset.mem_filter.2 ⟨hx, Nat.lt_succ_self k⟩
          · intro hmem
            exact lt_irrefl k (Finset.mem_filter.1 hmem).2
        omega
      · have hle := Finset.card_le_card hsub
        have := hj.2 hx
        omega
  have h1 := key n le_rfl
  have h2 := Finset.card_filter_le Xs (fun i : Fin n => (i : ℕ) < n)
  omega

section abs

variable {α : Type} {n : ℕ}

def Sat (M : Finset α) (g1 g2 : Fin n → Prop) (S : Fin n → α → Prop) (j : ℕ) (X : Finset α) : Prop :=
  ∀ i : Fin n, (i : ℕ) < j → g1 i → g2 i → ∀ s ∈ M, ∀ s' ∈ M, S i s → S i s' → (s ∈ X ↔ s' ∈ X)

def Rl (M : Finset α) (g1 g2 : Fin n → Prop) (S : Fin n → α → Prop) (j : ℕ) (r r' : α) : Prop :=
  ∀ X : Finset α, Sat M g1 g2 S j X → (r ∈ X ↔ r' ∈ X)

def Blk (M : Finset α) (g1 g2 : Fin n → Prop) (S : Fin n → α → Prop) (j : ℕ) (r : α)
    (b : Finset α) : Prop :=
  ∀ r' : α, r' ∈ b ↔ (r' ∈ M ∧ Rl M g1 g2 S j r r')

def Un (M : Finset α) (g1 g2 : Fin n → Prop) (S : Fin n → α → Prop) (A : Fin n → Prop)
    (p0 p1 : α) (j : ℕ) (b : Finset α) : Prop :=
  (∃ r ∈ M, Blk M g1 g2 S j r b) ∧ p0 ∉ b ∧ p1 ∉ b ∧
    ∀ i : Fin n, (i : ℕ) < j → g1 i → g2 i → A i → ∀ s ∈ b, ¬ S i s

variable {M : Finset α} {g1 g2 : Fin n → Prop} {S : Fin n → α → Prop} {A : Fin n → Prop}
  {p0 p1 : α} {j : ℕ} {r r' r'' : α} {b b' : Finset α}

lemma un_iff : Un M g1 g2 S A p0 p1 j b ↔ ((∃ r ∈ M, Blk M g1 g2 S j r b) ∧ p0 ∉ b ∧ p1 ∉ b ∧
    ∀ i : Fin n, (i : ℕ) < j → g1 i → g2 i → A i → ∀ s ∈ b, ¬ S i s) := Iff.rfl

lemma rl_refl (M : Finset α) (g1 g2 : Fin n → Prop) (S : Fin n → α → Prop) (j : ℕ) (r : α) :
    Rl M g1 g2 S j r r := fun _ _ => Iff.rfl

lemma rl_symm (h : Rl M g1 g2 S j r r') : Rl M g1 g2 S j r' r := fun X hX => (h X hX).symm

lemma rl_trans (h : Rl M g1 g2 S j r r') (h' : Rl M g1 g2 S j r' r'') : Rl M g1 g2 S j r r'' :=
  fun X hX => (h X hX).trans (h' X hX)

lemma rl_mono (h : Rl M g1 g2 S j r r') : Rl M g1 g2 S (j + 1) r r' :=
  fun X hX => h X (fun i hi => hX i (Nat.lt_succ_of_lt hi))

lemma rl_of_S {i : Fin n} {s s' : α} (hi : (i : ℕ) < j) (h1 : g1 i) (h2 : g2 i) (hs : s ∈ M)
    (hs' : s' ∈ M) (hS : S i s) (hS' : S i s') : Rl M g1 g2 S j s s' :=
  fun _ hX => hX i hi h1 h2 s hs s' hs' hS hS'

lemma sat_succ {X : Finset α} (jj : Fin n) (hX : Sat M g1 g2 S (jj : ℕ) X)
    (hj : g1 jj → g2 jj → ∀ s ∈ M, ∀ s' ∈ M, S jj s → S jj s' → (s ∈ X ↔ s' ∈ X)) :
    Sat M g1 g2 S ((jj : ℕ) + 1) X := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · exact hX i h
  · have hij : i = jj := Fin.ext h
    subst hij
    exact hj

lemma blk_sat (hb : Blk M g1 g2 S j r b) : Sat M g1 g2 S j b := by
  intro i hi h1 h2 s hs s' hs' hS hS'
  have h : Rl M g1 g2 S j s s' := rl_of_S hi h1 h2 hs hs' hS hS'
  rw [hb s, hb s']
  exact ⟨fun hh => ⟨hs', rl_trans hh.2 h⟩, fun hh => ⟨hs, rl_trans hh.2 (rl_symm h)⟩⟩

lemma blk_self (hr : r ∈ M) (hb : Blk M g1 g2 S j r b) : r ∈ b :=
  (hb r).2 ⟨hr, rl_refl M g1 g2 S j r⟩

lemma blk_mem {x : α} (hb : Blk M g1 g2 S j r b) (hx : x ∈ b) : Blk M g1 g2 S j x b := by
  intro y
  have hx' := (hb x).1 hx
  rw [hb y]
  exact ⟨fun hh => ⟨hh.1, rl_trans (rl_symm hx'.2) hh.2⟩, fun hh => ⟨hh.1, rl_trans hx'.2 hh.2⟩⟩

lemma blk_ext (hb : Blk M g1 g2 S j r b) (hb' : Blk M g1 g2 S j r b') : b = b' := by
  ext x
  rw [hb x, hb' x]

lemma stay (jj : Fin n) (hb : Un M g1 g2 S A p0 p1 (jj : ℕ) b)
    (hF : g1 jj → g2 jj → (∀ s ∈ M, ∀ s' ∈ M, S jj s → S jj s' → (s ∈ b ↔ s' ∈ b)) ∧
      (A jj → ∀ s ∈ b, ¬ S jj s)) :
    Un M g1 g2 S A p0 p1 ((jj : ℕ) + 1) b := by
  obtain ⟨⟨r, hr, hblk⟩, h0, h1, hA⟩ := un_iff.1 hb
  refine un_iff.2 ⟨⟨r, hr, ?_⟩, h0, h1, ?_⟩
  · intro y
    constructor
    · intro h
      exact ⟨((hblk y).1 h).1, rl_mono ((hblk y).1 h).2⟩
    · intro h
      exact (h.2 b (sat_succ jj (blk_sat hblk) (fun a c => (hF a c).1))).1 (blk_self hr hblk)
  · intro i hi a c d
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact hA i h a c d
    · have hij : i = jj := Fin.ext h
      subst hij
      exact (hF a c).2 d

lemma anti (UB : ℕ → Finset (Finset α))
    (hUB : ∀ (j : ℕ) (b : Finset α), b ∈ UB j ↔ Un M g1 g2 S A p0 p1 j b) (j : ℕ) :
    (UB (j + 1)).card ≤ (UB j).card := by
  classical
  have key : ∀ b' : Finset α, ∃ b : Finset α,
      b' ∈ UB (j + 1) → (b ∈ UB j ∧ b ⊆ b' ∧ b.Nonempty) := by
    intro b'
    by_cases hb' : b' ∈ UB (j + 1)
    · obtain ⟨⟨r, hr, hblk⟩, h0, h1, hA⟩ := un_iff.1 ((hUB _ _).1 hb')
      have hsub : M.filter (fun y => Rl M g1 g2 S j r y) ⊆ b' := by
        intro y hy
        rw [Finset.mem_filter] at hy
        exact (hblk y).2 ⟨hy.1, rl_mono hy.2⟩
      refine ⟨M.filter (fun y => Rl M g1 g2 S j r y), fun _ => ⟨?_, hsub, ⟨r, ?_⟩⟩⟩
      · rw [hUB]
        exact un_iff.2 ⟨⟨r, hr, fun y => Finset.mem_filter⟩, fun h => h0 (hsub h),
          fun h => h1 (hsub h),
          fun i hi a c d s hs => hA i (Nat.lt_succ_of_lt hi) a c d s (hsub hs)⟩
      · rw [Finset.mem_filter]
        exact ⟨hr, rl_refl M g1 g2 S j r⟩
    · exact ⟨∅, fun h => absurd h hb'⟩
  choose g hg using key
  apply Finset.card_le_card_of_injOn g
  · intro b' hb'
    exact (hg b' hb').1
  · intro b1 hb1 b2 hb2 heq
    have hb1' : b1 ∈ UB (j + 1) := hb1
    have hb2' : b2 ∈ UB (j + 1) := hb2
    obtain ⟨-, h2, ⟨x, hx⟩⟩ := hg b1 hb1'
    obtain ⟨-, k2, -⟩ := hg b2 hb2'
    have hx1 : x ∈ b1 := h2 hx
    have hx2 : x ∈ b2 := by
      apply k2
      have heq' : g b1 = g b2 := heq
      rw [← heq']
      exact hx
    obtain ⟨⟨r1, hr1, hblk1⟩, -⟩ := un_iff.1 ((hUB _ _).1 hb1')
    obtain ⟨⟨r2, hr2, hblk2⟩, -⟩ := un_iff.1 ((hUB _ _).1 hb2')
    exact blk_ext (blk_mem hblk1 hx1) (blk_mem hblk2 hx2)

lemma ub0 (UB : ℕ → Finset (Finset α))
    (hUB : ∀ (j : ℕ) (b : Finset α), b ∈ UB j ↔ Un M g1 g2 S A p0 p1 j b)
    (hp0 : p0 ∈ M) (hp1 : p1 ∈ M) (hne : p0 ≠ p1) : (UB 0).card = M.card - 2 := by
  classical
  have hR : ∀ x y : α, Rl M g1 g2 S 0 x y ↔ x = y := by
    intro x y
    constructor
    · intro h
      have h1 := (h {x} (fun i hi => absurd hi (Nat.not_lt_zero _))).1 (Finset.mem_singleton_self x)
      exact (Finset.mem_singleton.1 h1).symm
    · intro h
      rw [h]
      exact rl_refl M g1 g2 S 0 y
  have hEq : UB 0 = ((M.erase p0).erase p1).image (fun x => ({x} : Finset α)) := by
    ext b
    rw [hUB, Finset.mem_image]
    constructor
    · intro hb
      obtain ⟨⟨r, hr, hblk⟩, h0, h1, -⟩ := un_iff.1 hb
      have hbr : b = {r} := by
        ext x
        rw [hblk x, hR, Finset.mem_singleton]
        constructor
        · intro h
          exact h.2.symm
        · intro h
          rw [h]
          exact ⟨hr, rfl⟩
      refine ⟨r, ?_, hbr.symm⟩
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨?_, ?_, hr⟩
      · intro h
        apply h1
        rw [hbr]
        exact Finset.mem_singleton.2 h.symm
      · intro h
        apply h0
        rw [hbr]
        exact Finset.mem_singleton.2 h.symm
    · intro hb
      obtain ⟨r, hr, hb⟩ := hb
      have hb' : b = {r} := hb.symm
      subst hb'
      rw [Finset.mem_erase, Finset.mem_erase] at hr
      refine un_iff.2 ⟨⟨r, hr.2.2, ?_⟩, ?_, ?_, ?_⟩
      · intro x
        rw [hR, Finset.mem_singleton]
        constructor
        · intro h
          rw [h]
          exact ⟨hr.2.2, rfl⟩
        · intro h
          exact h.2.symm
      · intro h
        exact hr.2.1 (Finset.mem_singleton.1 h).symm
      · intro h
        exact hr.1 (Finset.mem_singleton.1 h).symm
      · intro i hi
        exact absurd hi (Nat.not_lt_zero _)
  rw [hEq, Finset.card_image_of_injective _ Finset.singleton_injective,
    Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne.symm, hp1⟩), Finset.card_erase_of_mem hp0]
  omega

lemma step (UB : ℕ → Finset (Finset α))
    (hUB : ∀ (j : ℕ) (b : Finset α), b ∈ UB j ↔ Un M g1 g2 S A p0 p1 j b) (jj : Fin n)
    (XS : Prop)
    (hfact : g1 jj → g2 jj → ∃ a ∈ M, ∃ c ∈ M, ∃ A1 A2 : Prop,
      (∀ s ∈ M, S jj s → Rl M g1 g2 S (jj : ℕ) a s ∨ Rl M g1 g2 S (jj : ℕ) c s) ∧
      (∀ b, Blk M g1 g2 S (jj : ℕ) a b → Un M g1 g2 S A p0 p1 (jj : ℕ) b → ¬ A1) ∧
      (∀ b, Blk M g1 g2 S (jj : ℕ) c b → Un M g1 g2 S A p0 p1 (jj : ℕ) b → ¬ A2) ∧
      (A jj → A1 ∨ A2) ∧
      (¬ XS → (A1 ∧ A2) ∨ ∃ u, (∀ s ∈ M, S jj s → s = u) ∧ (A jj → u = p0 ∨ u = p1))) :
    (UB (jj : ℕ)).card ≤ (UB ((jj : ℕ) + 1)).card + 1 ∧
      (¬ XS → (UB (jj : ℕ)).card ≤ (UB ((jj : ℕ) + 1)).card) := by
  classical
  by_cases hg : g1 jj ∧ g2 jj
  swap
  · have hsub : UB (jj : ℕ) ⊆ UB ((jj : ℕ) + 1) := by
      intro b hb
      rw [hUB] at hb ⊢
      exact stay jj hb (fun a c => absurd ⟨a, c⟩ hg)
    exact ⟨(Finset.card_le_card hsub).trans (Nat.le_succ _), fun _ => Finset.card_le_card hsub⟩
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨a, ha, c, hc, A1, A2, hS, hA1, hA2, hAA, hX⟩ := hfact hg1 hg2
  have hmeet : ∀ b, Un M g1 g2 S A p0 p1 (jj : ℕ) b → ∀ s ∈ b, S jj s →
      (Blk M g1 g2 S (jj : ℕ) a b ∨ Blk M g1 g2 S (jj : ℕ) c b) := by
    intro b hb s hs hSs
    obtain ⟨⟨r, hr, hblk⟩, -⟩ := un_iff.1 hb
    have hs' := (hblk s).1 hs
    rcases hS s hs'.1 hSs with h | h
    · left
      exact blk_mem hblk ((hblk a).2 ⟨ha, rl_trans hs'.2 (rl_symm h)⟩)
    · right
      exact blk_mem hblk ((hblk c).2 ⟨hc, rl_trans hs'.2 (rl_symm h)⟩)
  refine ⟨?_, ?_⟩
  · obtain ⟨B1, hB1⟩ : ∃ B1 : Finset α, Blk M g1 g2 S (jj : ℕ) a B1 :=
      ⟨M.filter (fun y => Rl M g1 g2 S (jj : ℕ) a y), fun y => Finset.mem_filter⟩
    obtain ⟨B2, hB2⟩ : ∃ B2 : Finset α, Blk M g1 g2 S (jj : ℕ) c B2 :=
      ⟨M.filter (fun y => Rl M g1 g2 S (jj : ℕ) c y), fun y => Finset.mem_filter⟩
    have hG : ∀ b ∈ UB (jj : ℕ), b ≠ B1 → b ≠ B2 → b ∈ UB ((jj : ℕ) + 1) := by
      intro b hb n1 n2
      rw [hUB] at hb ⊢
      have hno : ∀ s ∈ b, ¬ S jj s := by
        intro s hs hSs
        rcases hmeet b hb s hs hSs with h | h
        · exact n1 (blk_ext h hB1)
        · exact n2 (blk_ext h hB2)
      exact stay jj hb (fun _ _ => ⟨fun s hs s' hs' hSs hSs' =>
        ⟨fun h => absurd hSs (hno s h), fun h => absurd hSs' (hno s' h)⟩, fun _ => hno⟩)
    have hins : ∀ B : Finset α, (∀ b ∈ UB (jj : ℕ), b ≠ B → b ∈ UB ((jj : ℕ) + 1)) →
        (UB (jj : ℕ)).card ≤ (UB ((jj : ℕ) + 1)).card + 1 := by
      intro B hB
      have hsub : UB (jj : ℕ) ⊆ insert B (UB ((jj : ℕ) + 1)) := by
        intro b hb
        by_cases h : b = B
        · rw [h]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hB b hb h)
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    by_cases e12 : B1 = B2
    · exact hins B1 (fun b hb h => hG b hb h (fun h' => h (h'.trans e12.symm)))
    by_cases m1 : B1 ∈ UB (jj : ℕ)
    swap
    · exact hins B2 (fun b hb h => hG b hb (fun h' => m1 (h' ▸ hb)) h)
    by_cases m2 : B2 ∈ UB (jj : ℕ)
    swap
    · exact hins B1 (fun b hb h => hG b hb h (fun h' => m2 (h' ▸ hb)))
    have u1 := (hUB _ _).1 m1
    have u2 := (hUB _ _).1 m2
    have nA : ¬ A jj := fun h => (hAA h).elim (hA1 B1 hB1 u1) (hA2 B2 hB2 u2)
    obtain ⟨-, a0, a1, aA⟩ := un_iff.1 u1
    obtain ⟨-, c0, c1, cA⟩ := un_iff.1 u2
    have hSB : ∀ s ∈ M, S jj s → s ∈ B1 ∨ s ∈ B2 := by
      intro s hs hSs
      rcases hS s hs hSs with h | h
      · exact Or.inl ((hB1 s).2 ⟨hs, h⟩)
      · exact Or.inr ((hB2 s).2 ⟨hs, h⟩)
    by_cases d1 : ∃ s ∈ M, S jj s ∧ s ∈ B1
    swap
    · have hB2Q : B2 ∈ UB ((jj : ℕ) + 1) := by
        rw [hUB]
        refine stay jj u2 (fun _ _ => ⟨fun s hs s' hs' hSs hSs' => ?_, fun h => absurd h nA⟩)
        have t1 : s ∈ B2 := (hSB s hs hSs).resolve_left (fun h => d1 ⟨s, hs, hSs, h⟩)
        have t2 : s' ∈ B2 := (hSB s' hs' hSs').resolve_left (fun h => d1 ⟨s', hs', hSs', h⟩)
        exact ⟨fun _ => t2, fun _ => t1⟩
      refine hins B1 (fun b hb h => ?_)
      by_cases h2 : b = B2
      · rw [h2]
        exact hB2Q
      · exact hG b hb h h2
    by_cases d2 : ∃ s ∈ M, S jj s ∧ s ∈ B2
    swap
    · have hB1Q : B1 ∈ UB ((jj : ℕ) + 1) := by
        rw [hUB]
        refine stay jj u1 (fun _ _ => ⟨fun s hs s' hs' hSs hSs' => ?_, fun h => absurd h nA⟩)
        have t1 : s ∈ B1 := (hSB s hs hSs).resolve_right (fun h => d2 ⟨s, hs, hSs, h⟩)
        have t2 : s' ∈ B1 := (hSB s' hs' hSs').resolve_right (fun h => d2 ⟨s', hs', hSs', h⟩)
        exact ⟨fun _ => t2, fun _ => t1⟩
      refine hins B2 (fun b hb h => ?_)
      by_cases h2 : b = B1
      · rw [h2]
        exact hB1Q
      · exact hG b hb h2 h
    obtain ⟨s1, hs1, hSs1, hs1B⟩ := d1
    obtain ⟨s2, hs2, hSs2, hs2B⟩ := d2
    have hQ : B1 ∪ B2 ∈ UB ((jj : ℕ) + 1) := by
      rw [hUB]
      refine un_iff.2 ⟨⟨a, ha, ?_⟩, ?_, ?_, ?_⟩
      · intro y
        constructor
        · intro h
          rcases Finset.mem_union.1 h with h | h
          · exact ⟨((hB1 y).1 h).1, rl_mono ((hB1 y).1 h).2⟩
          · refine ⟨((hB2 y).1 h).1, ?_⟩
            have e1 : Rl M g1 g2 S ((jj : ℕ) + 1) a s1 := rl_mono ((hB1 s1).1 hs1B).2
            have e2 : Rl M g1 g2 S ((jj : ℕ) + 1) s1 s2 :=
              rl_of_S (i := jj) (Nat.lt_succ_self _) hg1 hg2 hs1 hs2 hSs1 hSs2
            have e3 : Rl M g1 g2 S ((jj : ℕ) + 1) s2 y :=
              rl_mono (rl_trans (rl_symm ((hB2 s2).1 hs2B).2) ((hB2 y).1 h).2)
            exact rl_trans e1 (rl_trans e2 e3)
        · intro h
          have hsat : Sat M g1 g2 S ((jj : ℕ) + 1) (B1 ∪ B2) := by
            apply sat_succ jj
            · intro i hi k1 k2 s hs s' hs' hSs hSs'
              have q1 := blk_sat hB1 i hi k1 k2 s hs s' hs' hSs hSs'
              have q2 := blk_sat hB2 i hi k1 k2 s hs s' hs' hSs hSs'
              rw [Finset.mem_union, Finset.mem_union, q1, q2]
            · intro _ _ s hs s' hs' hSs hSs'
              exact ⟨fun _ => Finset.mem_union.2 (hSB s' hs' hSs'),
                fun _ => Finset.mem_union.2 (hSB s hs hSs)⟩
          exact (h.2 _ hsat).1 (Finset.mem_union_left _ (blk_self ha hB1))
      · intro h
        rcases Finset.mem_union.1 h with h | h
        · exact a0 h
        · exact c0 h
      · intro h
        rcases Finset.mem_union.1 h with h | h
        · exact a1 h
        · exact c1 h
      · intro i hi k1 k2 hAi s hs
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · rcases Finset.mem_union.1 hs with hs | hs
          · exact aA i h k1 k2 hAi s hs
          · exact cA i h k1 k2 hAi s hs
        · have hij : i = jj := Fin.ext h
          subst hij
          exact absurd hAi nA
    have hsub : UB (jj : ℕ) ⊆
        insert B1 (insert B2 ((UB ((jj : ℕ) + 1)).erase (B1 ∪ B2))) := by
      intro b hb
      by_cases h1 : b = B1
      · rw [h1]
        exact Finset.mem_insert_self _ _
      by_cases h2 : b = B2
      · rw [h2]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨?_, hG b hb h1 h2⟩))
      intro hbu
      obtain ⟨⟨r, hr, hblk⟩, -⟩ := un_iff.1 ((hUB _ _).1 hb)
      have hab : a ∈ b := by
        rw [hbu]
        exact Finset.mem_union_left _ (blk_self ha hB1)
      exact h1 (blk_ext (blk_mem hblk hab) hB1)
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_insert_le B1 (insert B2 ((UB ((jj : ℕ) + 1)).erase (B1 ∪ B2)))
    have hc3 := Finset.card_insert_le B2 ((UB ((jj : ℕ) + 1)).erase (B1 ∪ B2))
    have hc4 := Finset.card_erase_of_mem hQ
    have hc5 : 0 < (UB ((jj : ℕ) + 1)).card := Finset.card_pos.2 ⟨_, hQ⟩
    omega
  · intro hx
    apply Finset.card_le_card
    intro b hb
    rw [hUB] at hb ⊢
    obtain ⟨⟨r, hr, hblk⟩, h0, h1, -⟩ := un_iff.1 hb
    have hbM : ∀ s ∈ b, s ∈ M := fun s hs => ((hblk s).1 hs).1
    apply stay jj hb
    intro _ _
    rcases hX hx with ⟨k1, k2⟩ | ⟨u, hu1, hu2⟩
    · have hno : ∀ s ∈ b, ¬ S jj s := by
        intro s hs hSs
        rcases hmeet b hb s hs hSs with h | h
        · exact hA1 b h hb k1
        · exact hA2 b h hb k2
      exact ⟨fun s hs s' hs' hSs hSs' =>
        ⟨fun h => absurd hSs (hno s h), fun h => absurd hSs' (hno s' h)⟩, fun _ => hno⟩
    · refine ⟨fun s hs s' hs' hSs hSs' => by rw [hu1 s hs hSs, hu1 s' hs' hSs'],
        fun hAj s hs hSs => ?_⟩
      have hsu := hu1 s (hbM s hs) hSs
      rcases hu2 hAj with h | h
      · rw [hsu, h] at hs
        exact h0 hs
      · rw [hsu, h] at hs
        exact h1 hs

lemma perinput (jj : Fin n) (hp0 : p0 ∈ M) (Se : α → Prop) (Ae : Prop)
    (h : (∃ s0, (∀ s ∈ M, Se s → s = s0) ∧ (Ae → s0 = p0 ∨ s0 = p1)) ∨
      (∃ i : Fin n, (i : ℕ) < (jj : ℕ) ∧ g1 i ∧ g2 i ∧ (∀ s, Se s → S i s) ∧ (Ae → A i))) :
    ∃ a ∈ M, (∀ s ∈ M, Se s → Rl M g1 g2 S (jj : ℕ) a s) ∧
      (∀ b, Blk M g1 g2 S (jj : ℕ) a b → Un M g1 g2 S A p0 p1 (jj : ℕ) b → ¬ Ae) := by
  by_cases hT : ∃ s ∈ M, Se s
  · obtain ⟨s, hs, hSs⟩ := hT
    refine ⟨s, hs, ?_, ?_⟩
    · intro s' hs' hSs'
      rcases h with ⟨s0, h1, _⟩ | ⟨i, hi, hg1, hg2, hSi, _⟩
      · rw [h1 s hs hSs, h1 s' hs' hSs']
        exact rl_refl M g1 g2 S (jj : ℕ) s0
      · exact rl_of_S hi hg1 hg2 hs hs' (hSi s hSs) (hSi s' hSs')
    · intro b hblk hun hAe
      obtain ⟨-, h0, h1', hA⟩ := un_iff.1 hun
      have hsb : s ∈ b := blk_self hs hblk
      rcases h with ⟨s0, h1, h2⟩ | ⟨i, hi, hg1, hg2, hSi, hAi⟩
      · have e := h1 s hs hSs
        rcases h2 hAe with h | h
        · rw [e, h] at hsb
          exact h0 hsb
        · rw [e, h] at hsb
          exact h1' hsb
      · exact hA i hi hg1 hg2 (hAi hAe) s hsb (hSi s hSs)
  · exact ⟨p0, hp0, fun s hs hSs => absurd ⟨s, hs, hSs⟩ hT,
      fun b hblk hun _ => (un_iff.1 hun).2.1 (blk_self hp0 hblk)⟩

lemma main_abs (UB : ℕ → Finset (Finset α))
    (hUB : ∀ (j : ℕ) (b : Finset α), b ∈ UB j ↔ Un M g1 g2 S A p0 p1 j b)
    (Xs : Finset (Fin n)) (hp0 : p0 ∈ M) (hp1 : p1 ∈ M) (hne : p0 ≠ p1)
    (hgate : ∀ jj : Fin n, g1 jj → g2 jj → ∃ (Se1 Se2 : α → Prop) (Ae1 Ae2 : Prop),
      ((∃ s0, (∀ s ∈ M, Se1 s → s = s0) ∧ (Ae1 → s0 = p0 ∨ s0 = p1)) ∨
        (∃ i : Fin n, (i : ℕ) < (jj : ℕ) ∧ g1 i ∧ g2 i ∧ (∀ s, Se1 s → S i s) ∧ (Ae1 → A i))) ∧
      ((∃ s0, (∀ s ∈ M, Se2 s → s = s0) ∧ (Ae2 → s0 = p0 ∨ s0 = p1)) ∨
        (∃ i : Fin n, (i : ℕ) < (jj : ℕ) ∧ g1 i ∧ g2 i ∧ (∀ s, Se2 s → S i s) ∧ (Ae2 → A i))) ∧
      (∀ s ∈ M, S jj s → Se1 s ∨ Se2 s) ∧ (A jj → Ae1 ∨ Ae2) ∧
      (jj ∉ Xs → (Ae1 ∧ Ae2) ∨ ∃ u, (∀ s ∈ M, S jj s → s = u) ∧ (A jj → u = p0 ∨ u = p1))) :
    (∀ j : Fin n, (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧
        (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
        (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card)) ∧
      (UB 0).card = M.card - 2 ∧ M.card - 2 ≤ Xs.card + (UB n).card := by
  have hstep : ∀ j : Fin n, (UB (j : ℕ)).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
      (j ∉ Xs → (UB (j : ℕ)).card ≤ (UB ((j : ℕ) + 1)).card) := by
    intro jj
    apply step UB hUB jj (jj ∈ Xs)
    intro hg1 hg2
    obtain ⟨Se1, Se2, Ae1, Ae2, hT1, hT2, hS, hA, hX⟩ := hgate jj hg1 hg2
    obtain ⟨a, ha, ha1, ha2⟩ := perinput (A := A) (p1 := p1) jj hp0 Se1 Ae1 hT1
    obtain ⟨c, hc, hc1, hc2⟩ := perinput (A := A) (p1 := p1) jj hp0 Se2 Ae2 hT2
    refine ⟨a, ha, c, hc, Ae1, Ae2, ?_, ha2, hc2, hA, hX⟩
    intro s hs hSs
    rcases hS s hs hSs with h | h
    · exact Or.inl (ha1 s hs h)
    · exact Or.inr (hc1 s hs h)
  have h0 := ub0 UB hUB hp0 hp1 hne
  refine ⟨fun j => ⟨anti UB hUB j, (hstep j).1,
    fun hj => le_antisymm ((hstep j).2 hj) (anti UB hUB j)⟩, h0, ?_⟩
  rw [← h0]
  exact tele (fun j => (UB j).card) Xs hstep

end abs

end PEqualNP.Outside.L_meta_1641

theorem PEqualNP.Outside.L_meta_1641 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ UB : ℕ → Finset (Finset (Fin N)),
    (∀ (j : ℕ) (b : Finset (Fin N)), b ∈ UB j ↔ ((∃ r ∈ L i0, ∀ r' : Fin N, r' ∈ b ↔ (r' ∈ L i0 ∧ ∀ X : Finset (Fin N), (∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
          ∀ s ∈ L i0, ∀ s' ∈ L i0, St (N + (i : ℕ)) s → St (N + (i : ℕ)) s' → (s ∈ X ↔ s' ∈ X)) → (r ∈ X ↔ r' ∈ X))) ∧
        p0 ∉ b ∧ p1 ∉ b ∧ ∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
        (ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true) → ∀ s ∈ b, ¬ St (N + (i : ℕ)) s)) →
    ∀ Xs : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ Xs ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true))) →
      (∀ j : Fin gates.length, (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧ (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
        (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card)) ∧
      (UB 0).card = q - 1 ∧ q - 1 ≤ Xs.card + (UB gates.length).card := by
  intro q N L i0 p0 p1 hq hN hcard hint hpair hne hp0 hp1 gates hgates hlen1 hin ev hev o0 ho1 ho2 ho3 ho4 St hSt UB hUB Xs hXs
  have hval : ∀ (w : ℕ) (x : Fin N → Bool),
      ev w x = PEqualNP.Outside.L_meta_1641.vl gates x w := fun w x => hev w x
  have hE1 : ∀ (p : Fin N) (x : Fin N → Bool), ev (p : ℕ) x = x p := fun p x =>
    (hval _ _).trans (PEqualNP.Outside.L_meta_1641.vl_input gates x p p.2)
  have hOr : ∀ (k : Fin gates.length) (x : Fin N → Bool), (gates.get k).op = GateOp.or →
      (ev (N + (k : ℕ)) x = true ↔ ∃ r ∈ (gates.get k).inputs, ev r x = true) := by
    intro k x hop
    rw [hval, PEqualNP.Outside.L_meta_1641.vl_or_fin gates x k hop]
    constructor
    · rintro ⟨r, hr, _, hv⟩
      exact ⟨r, hr, (hval r x).trans hv⟩
    · rintro ⟨r, hr, hv⟩
      exact ⟨r, hr, hin k r hr, (hval r x).symm.trans hv⟩
  have hmono : ∀ (x y : Fin N → Bool), (∀ v, x v = true → y v = true) →
      ∀ w, ev w x = true → ev w y = true := by
    intro x y hxy w h
    rw [hval] at h ⊢
    exact PEqualNP.Outside.L_meta_1641.vl_mono gates (fun g hg => (hgates g hg).1) x y hxy w h
  have hSt1 : ∀ (e : ℕ) (s : Fin N), e < N → St e s → (s : ℕ) = e := by
    intro e s he h
    have h1 := (hSt e s).1 h {e} (Set.mem_singleton e) (by
      intro k hk
      have h2 : N + (k : ℕ) = e := Set.mem_singleton_iff.1 hk
      omega)
    exact Set.mem_singleton_iff.1 h1
  have hSt2 : ∀ (i : Fin gates.length) (s : Fin N), ¬ (gates.get i).op = GateOp.or →
      ¬ St (N + (i : ℕ)) s := by
    intro i s hop h
    have h1 := (hSt _ s).1 h {N + (i : ℕ)} (Set.mem_singleton _) (by
      intro k hk hk2
      have h3 : N + (k : ℕ) = N + (i : ℕ) := Set.mem_singleton_iff.1 hk
      have h4 : k = i := Fin.ext (by omega)
      rw [h4] at hk2
      exact absurd hk2 hop)
    have h2 : (s : ℕ) = N + (i : ℕ) := Set.mem_singleton_iff.1 h1
    have h5 := s.2
    omega
  have hSt3 : ∀ (k : Fin gates.length) (s : Fin N), St (N + (k : ℕ)) s →
      ∃ e ∈ (gates.get k).inputs, St e s := by
    intro k s h
    have h1 := (hSt _ s).1 h {w | w = N + (k : ℕ) ∨ ∃ e ∈ (gates.get k).inputs, ∀ Zs : Set ℕ, e ∈ Zs →
        (∀ k' : Fin gates.length, N + (k' : ℕ) ∈ Zs → (gates.get k').op = GateOp.or →
          ∀ e' ∈ (gates.get k').inputs, e' ∈ Zs) → w ∈ Zs}
      (Or.inl rfl) (by
        intro k' hk' hop' e' he'
        rcases hk' with hk' | ⟨e, he, hk'⟩
        · have h4 : k' = k := Fin.ext (by omega)
          subst h4
          exact Or.inr ⟨e', he', fun Zs hz _ => hz⟩
        · exact Or.inr ⟨e, he, fun Zs hz hcl => hcl k' (hk' Zs hz hcl) hop' e' he'⟩)
    rcases h1 with h1 | ⟨e, he, h1⟩
    · have h5 := s.2
      omega
    · exact ⟨e, he, (hSt e s).2 h1⟩
  have hreach : ∀ (w : ℕ) (s : Fin N) (x : Fin N → Bool), St w s → x s = true →
      ev w x = true := by
    intro w s x h hx
    by_contra hc
    have hc' : ev w x = false := by simpa using hc
    have h1 := (hSt w s).1 h {w' | ev w' x = false} hc' (by
      intro k hk hop e he
      have hk' : ev (N + (k : ℕ)) x = false := hk
      show ev e x = false
      by_contra hne'
      have h3 : ev e x = true := by simpa using hne'
      have h4 := (hOr k x hop).2 ⟨e, he, h3⟩
      rw [hk'] at h4
      exact Bool.noConfusion h4)
    have h2 : ev (s : ℕ) x = false := h1
    rw [hE1, hx] at h2
    exact Bool.noConfusion h2
  have hT : ∀ (jj : Fin gates.length), (gates.get jj).op = GateOp.or →
      ev (N + (jj : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
      ∀ e ∈ (gates.get jj).inputs,
      ((∃ s0 : Fin N, (∀ s ∈ L i0, St e s → s = s0) ∧
          ((ev e (fun v : Fin N => decide (v = p0)) = true ∨
            ev e (fun v : Fin N => decide (v = p1)) = true) → s0 = p0 ∨ s0 = p1)) ∨
        (∃ i : Fin gates.length, (i : ℕ) < (jj : ℕ) ∧ (gates.get i).op = GateOp.or ∧
          ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
          (∀ s, St e s → St (N + (i : ℕ)) s) ∧
          ((ev e (fun v : Fin N => decide (v = p0)) = true ∨
            ev e (fun v : Fin N => decide (v = p1)) = true) →
            (ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨
              ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true)))) := by
    intro jj hg1 hg2 e he
    have hlt := hin jj e he
    by_cases heN : e < N
    · left
      refine ⟨⟨e, heN⟩, fun s hs hSs => Fin.ext (hSt1 e s heN hSs), ?_⟩
      have h0 : ∀ x : Fin N → Bool, ev e x = x ⟨e, heN⟩ := fun x => hE1 ⟨e, heN⟩ x
      intro hA
      rcases hA with h | h
      · left
        rw [h0] at h
        exact of_decide_eq_true h
      · right
        rw [h0] at h
        exact of_decide_eq_true h
    · have hjl := jj.2
      obtain ⟨i, hiv⟩ : ∃ i : Fin gates.length, N + (i : ℕ) = e :=
        ⟨⟨e - N, by omega⟩, by show N + (e - N) = e; omega⟩
      by_cases hop : (gates.get i).op = GateOp.or
      · right
        refine ⟨i, by omega, hop, ?_, ?_, ?_⟩
        · rw [hiv]
          by_contra hc
          have hc' : ev e (fun v : Fin N => decide (v ∉ L i0)) = true := by simpa using hc
          have h4 := (hOr jj _ hg1).2 ⟨e, he, hc'⟩
          rw [hg2] at h4
          exact Bool.noConfusion h4
        · intro s hs
          rw [hiv]
          exact hs
        · intro hA
          rw [hiv]
          exact hA
      · left
        refine ⟨p0, fun s hs hSs => ?_, fun _ => Or.inl rfl⟩
        have h2 := hSt2 i s hop
        rw [hiv] at h2
        exact absurd hSs h2
  have H := PEqualNP.Outside.L_meta_1641.main_abs (M := L i0)
    (g1 := fun i : Fin gates.length => (gates.get i).op = GateOp.or)
    (g2 := fun i : Fin gates.length =>
      ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false)
    (S := fun (i : Fin gates.length) (s : Fin N) => St (N + (i : ℕ)) s)
    (A := fun i : Fin gates.length =>
      ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨
        ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true)
    (p0 := p0) (p1 := p1) UB hUB Xs hp0 hp1 hne (by
      intro jj hg1 hg2
      have hg1' : (gates.get jj).op = GateOp.or := hg1
      have hg2' : ev (N + (jj : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false := hg2
      obtain ⟨e1, e2, he1, he2, hall⟩ := PEqualNP.Outside.L_meta_1641.two_inputs
        (gates.get jj).inputs (hgates _ (List.getElem_mem jj.2)).2 (hlen1 jj)
      refine ⟨fun s => St e1 s, fun s => St e2 s,
        (ev e1 (fun v : Fin N => decide (v = p0)) = true ∨
          ev e1 (fun v : Fin N => decide (v = p1)) = true),
        (ev e2 (fun v : Fin N => decide (v = p0)) = true ∨
          ev e2 (fun v : Fin N => decide (v = p1)) = true),
        hT jj hg1' hg2' e1 he1, hT jj hg1' hg2' e2 he2, ?_, ?_, ?_⟩
      · intro s hs hSs
        obtain ⟨e, he, h⟩ := hSt3 jj s hSs
        rcases hall e he with h' | h'
        · rw [h'] at h
          exact Or.inl h
        · rw [h'] at h
          exact Or.inr h
      · intro hA
        rcases hA with h | h
        · obtain ⟨e, he, hv⟩ := (hOr jj _ hg1').1 h
          rcases hall e he with h' | h'
          · rw [h'] at hv
            exact Or.inl (Or.inl hv)
          · rw [h'] at hv
            exact Or.inr (Or.inl hv)
        · obtain ⟨e, he, hv⟩ := (hOr jj _ hg1').1 h
          rcases hall e he with h' | h'
          · rw [h'] at hv
            exact Or.inl (Or.inr hv)
          · rw [h'] at hv
            exact Or.inr (Or.inr hv)
      · intro hx
        by_cases hallA : ∀ e ∈ (gates.get jj).inputs,
            (ev e (fun v : Fin N => decide (v = p0)) = true ∨
              ev e (fun v : Fin N => decide (v = p1)) = true)
        · exact Or.inl ⟨hallA e1 he1, hallA e2 he2⟩
        · right
          have hnt : ¬ ∀ t : Fin N, t ≠ i0 →
              ev (N + (jj : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true :=
            fun h => hx ((hXs jj).2 ⟨hg1', hg2', h, hallA⟩)
          obtain ⟨t, ht⟩ := not_forall.1 hnt
          obtain ⟨ht1, hf⟩ := Classical.not_imp.1 ht
          obtain ⟨u, hu⟩ := Finset.card_eq_one.1 (hint t i0 ht1)
          have hkey : ∀ p ∈ L i0, p ∈ L t → p = u := by
            intro p hp hpt
            have h5 := Finset.mem_inter.2 ⟨hpt, hp⟩
            rw [hu] at h5
            exact Finset.mem_singleton.1 h5
          refine ⟨u, ?_, ?_⟩
          · intro s hs hSs
            apply hkey s hs
            by_contra hn
            exact hf (hreach _ s _ hSs (decide_eq_true hn))
          · intro hA
            have hk2 : ∀ p ∈ L i0,
                ev (N + (jj : ℕ)) (fun v : Fin N => decide (v = p)) = true → u = p := by
              intro p hp h
              symm
              apply hkey p hp
              by_contra hn
              refine hf (hmono _ _ (fun v hv => ?_) _ h)
              have hvp : v = p := of_decide_eq_true hv
              rw [hvp]
              exact decide_eq_true hn
            rcases hA with h | h
            · exact Or.inl (hk2 p0 hp0 h)
            · exact Or.inr (hk2 p1 hp1 h))
  have hc : (L i0).card - 2 = q - 1 := by
    rw [hcard]
    omega
  rw [hc] at H
  exact H
