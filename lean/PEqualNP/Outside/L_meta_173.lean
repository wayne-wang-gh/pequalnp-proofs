import Mathlib
import PEqualNP.Defs

-- Reuses checked arguments from the upstream proof repository, Apache-2.0.
open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_173_aux.Core

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.Outside.L_meta_173_aux.Core

namespace PEqualNP.Outside.L_meta_173_aux.Core

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.Outside.L_meta_173_aux.Core

namespace PEqualNP.Outside.L_meta_173_aux.Core

open PEqualNP.CircuitLowerBounds

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

theorem orChain (k : ℕ) : ∀ m : ℕ, k + 1 ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = k ∧ out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = decide (∃ i : Fin (k + 1), w.getD i false = true) := by
  induction k with
  | zero =>
    intro m hm
    refine ⟨[], 0, by simp, rfl, by simp; omega, ?_⟩
    intro w _
    simp [wiresFrom]
  | succ k ih =>
    intro m hm
    obtain ⟨gs, out, ok, len, hout, ev⟩ := ih m (by omega)
    refine ⟨gs ++ [⟨GateOp.or, [out, k + 1]⟩], m + gs.length, ?_, by simp [len], by simp, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ok g hg
      · simp only [List.mem_singleton] at hg; subst hg; simp [Ok]
    · intro w hw
      rw [wiresFrom_append]
      set v := wiresFrom gs w with hv
      have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
      have e1 : v.getD (k + 1) false = w.getD (k + 1) false := by
        rw [hv, getD_wiresFrom _ _ _ (by omega)]
      have step : wiresFrom [⟨GateOp.or, [out, k + 1]⟩] v
          = v ++ [GateOp.or.eval ([out, k + 1].map fun i => v.getD i false)] := rfl
      rw [step, ← lv, getD_snoc_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [ev w hw, e1]
      simp [Fin.exists_fin_succ']

theorem or_size (n s : ℕ) :
    HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i : Fin n, x i = true)) s ↔ n ≤ s + 1 := by
  constructor
  · apply dep_lower
    intro i
    refine ⟨fun _ => false, ?_⟩
    simp only [Bool.not_false, ne_eq]
    have h1 : (∃ j : Fin n, Function.update (fun _ : Fin n => false) i true j = true) :=
      ⟨i, by simp⟩
    simp [h1]
  · intro h
    cases n with
    | zero =>
      refine ⟨⟨[], 0⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
      intro x
      simp [Circuit.eval, Circuit.wires]
    | succ k =>
      obtain ⟨gs, out, ok, len, _, ev⟩ := orChain k (k + 1) le_rfl
      refine ⟨⟨gs, out⟩, ok, by simp only [Circuit.size]; omega, ?_⟩
      intro x
      have h := ev (List.ofFn x) (by simp)
      simp only [Circuit.eval, wires_eq, h, getD_ofFn]

end PEqualNP.Outside.L_meta_173_aux.Core

namespace PEqualNP.Outside.L_meta_173_aux.Core.EdgeUpper

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_173_aux.Core

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩

    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem edge_upper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) := by
  intro n G _ T hE hc
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  apply bld_hasCircuitSize
  refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
  intro x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

end PEqualNP.Outside.L_meta_173_aux.Core.EdgeUpper

namespace PEqualNP.Outside.L_meta_173_aux.Reduced

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

private def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

private def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

private lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

private lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

private lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · rw [if_pos hgt]; exact hm.2.2.2.2.2 u hgt
  · rw [if_neg hgt]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

private lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

private def effInputs (g : Gate) : List ℕ :=
  GateOp.casesOn (motive := fun _ => List ℕ) g.op
    g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs

private lemma eval_eq_effInputs (g : Gate) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((effInputs g).map f) := by
  cases hop : g.op <;> simp only [effInputs, hop, GateOp.eval]
  cases g.inputs <;> simp

private lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

private lemma output_last {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y)
    (hne : C.gates ≠ []) :
    C.output + 1 = n + C.gates.length := by
  by_contra hne_out
  by_cases hge : n + C.gates.length ≤ C.output
  · obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    simp only [circuitFun, Circuit.eval]
    rw [getD_ge_length _ _ (by rw [wires_length]; exact hge),
        getD_ge_length _ _ (by rw [wires_length]; exact hge)]
  · have hpos : 0 < C.gates.length := List.length_pos_of_ne_nil hne
    have hlt : C.output < n + (C.gates.length - 1) := by omega
    have hsplit : C.gates = C.gates.dropLast ++ [C.gates.getLast hne] :=
      (List.dropLast_append_getLast hne).symm
    let D : Circuit := ⟨C.gates.dropLast, C.output⟩
    have hfitD : FanInTwo D := fun g hg => hmin.1 g (List.dropLast_subset _ hg)
    have hfunD : circuitFun n D = circuitFun n C := by
      funext x
      simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
      conv_rhs => rw [hsplit, List.foldl_append]
      have hlt' : C.output < (C.gates.dropLast.foldl stepWire (List.ofFn x)).length := by
        rw [foldl_stepWire_length, List.length_ofFn, List.length_dropLast]
        exact hlt
      exact (foldl_stepWire_getD_lt [C.gates.getLast hne] _ C.output hlt').symm
    have hle := hmin.2 D hfitD hfunD
    simp only [Circuit.size, D, List.length_dropLast] at hle
    omega

private lemma every_gate_read {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y)
    (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (effInputs p.1).contains (n + j) = true := by
  by_contra hno
  have hne : C.gates ≠ [] := by intro h; simp [h] at hj
  have hout : C.output + 1 = n + C.gates.length := output_last hmin hnc hne
  have hj_lt : j < C.gates.length := by omega
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj_lt
  have hnot_read : ∀ (t : ℕ) (ht : t < post.length),
      ∀ u ∈ effInputs (post[t]'ht), u ≠ n + j := by
    intro t ht u hu heq
    subst heq
    apply hno
    have hidx : j + 1 + t < C.gates.length := by
      have := congrArg List.length hgs; simp [hpre_len] at this; omega
    have hget : C.gates[j + 1 + t]'hidx = post[t]'ht := by
      have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; exact hidx) = post[t]'ht := by
        rw [List.getElem_append_right (by omega)]
        have hsub : j + 1 + t - pre.length = t + 1 := by omega
        simp [hsub]
      simpa [hgs] using h1
    refine ⟨(post[t]'ht, j + 1 + t), ?_, by omega, List.contains_iff_mem.mpr hu⟩
    have hmem : (C.gates.zipIdx)[j + 1 + t]'(by simp [hidx]) ∈ C.gates.zipIdx := List.getElem_mem _
    simpa [List.getElem_zipIdx, hget] using hmem
  let shiftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftDown (n + j))⟩
  let D : Circuit := ⟨pre ++ post.map shiftGate, C.output - 1⟩
  have hfitD : FanInTwo D := by
    intro g hg
    rcases List.mem_append.mp hg with hpre | hpost
    · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
      have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨hg0C.1, by simp [shiftGate, hg0C.2]⟩
  have hfunD : circuitFun n D = circuitFun n C := by
    funext x
    simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
    conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
    rw [List.foldl_append]
    let w0 := pre.foldl stepWire (List.ofFn x)
    have hw0_len : w0.length = n + j := by
      simp [w0, foldl_stepWire_length, hpre_len]
    let bOld := gj.op.eval (gj.inputs.map fun i => w0.getD i false)
    have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
    have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
        ((post.map shiftGate).foldl stepWire w0) := by
      refine foldl_wiresMatch w0 bOld post (post.map shiftGate) (stepWire w0 gj) w0 hm0
        (by simp) ?_
      intro t htC htD vC vD hmv _
      simp only [List.getElem_map, shiftGate]
      rw [eval_eq_effInputs ⟨(post[t]'htC).op, (post[t]'htC).inputs.map (shiftDown (n + j))⟩,
          eval_eq_effInputs (post[t]'htC)]
      have heff_map : effInputs ⟨(post[t]'htC).op, (post[t]'htC).inputs.map (shiftDown (n + j))⟩ =
          (effInputs (post[t]'htC)).map (shiftDown (n + j)) := by
        cases h : (post[t]'htC).op <;> simp [effInputs, h, List.map_take]
      rw [heff_map, List.map_map]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by rw [hw0_len]; exact hnot_read t htC u hu)
    exact hmEnd.2.2.2.2.2 C.output (by omega)
  have hle := hmin.2 D hfitD hfunD
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  simp only [Circuit.size, D, List.length_append, List.length_map] at hle
  omega

private def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

private lemma no_duplicate_wire {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (i j : ℕ) (hij : i < n + j) (hj : j < C.gates.length) :
    ∃ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false := by
  by_contra hsame
  push Not at hsame
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  let aliasGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire (n + j) i)⟩
  let D : Circuit := ⟨pre ++ post.map aliasGate, aliasWire (n + j) i C.output⟩
  have hfitD : FanInTwo D := by
    intro g hg
    rcases List.mem_append.mp hg with hpre | hpost
    · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
      have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨hg0C.1, by simp [aliasGate, hg0C.2]⟩
  have hfunD : circuitFun n D = circuitFun n C := by
    funext x
    have hxy := hsame x
    simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
    conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
    rw [List.foldl_append]
    let w0 := pre.foldl stepWire (List.ofFn x)
    have hw0_len : w0.length = n + j := by
      simp [w0, foldl_stepWire_length, hpre_len]
    let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
    have hval_eq : w0.getD i false = bOld := by
      have hCi : (C.wires (List.ofFn x)).getD i false = w0.getD i false := by
        rw [wires_eq_foldl, hgs, List.foldl_append]
        exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
      have hCj : (C.wires (List.ofFn x)).getD (n + j) false = bOld := by
        rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
        rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
      rw [← hCi, ← hCj, hxy]
    have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
    have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
        ∀ u, vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
      intro vC vD hmv u
      unfold aliasWire
      by_cases hu : u = n + j
      · subst hu
        rw [if_pos rfl, hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
      · rw [if_neg hu, ← hw0_len]
        exact wiresMatch_getD_shiftDown hmv (by omega)
    have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
        ((post.map aliasGate).foldl stepWire w0) := by
      refine foldl_wiresMatch w0 bOld post (post.map aliasGate) (stepWire w0 gj) w0 hm0
        (by simp) ?_
      intro t htC htD vC vD hmv _
      simp only [List.getElem_map, aliasGate, List.map_map]
      congr 1
      refine List.map_congr_left fun u _ => ?_
      exact halias_get vC vD hmv u
    exact halias_get _ _ hmEnd C.output
  have hle := hmin.2 D hfitD hfunD
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  simp only [Circuit.size, D, List.length_append, List.length_map] at hle
  omega

private def rewriteTrueGate (wOld : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => ⟨.and, (g.inputs.filter (fun u => u != wOld)).map (shiftDown wOld)⟩
  | .or =>
    if g.inputs.contains wOld then ⟨.and, []⟩
    else ⟨.or, g.inputs.map (shiftDown wOld)⟩
  | .not =>
    match g.inputs with
    | [] => ⟨.not, []⟩
    | u :: _ => if u = wOld then ⟨.or, []⟩ else ⟨.not, [shiftDown wOld u]⟩
  | op => ⟨op, g.inputs.map (shiftDown wOld)⟩

private lemma rewriteTrueGate_fit (wOld : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (rewriteTrueGate wOld g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (rewriteTrueGate wOld g).inputs.length ≤ 2 := by
  obtain ⟨hop, hlen⟩ := hg
  change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
  rcases hop with h | h | h
  · simp only [rewriteTrueGate, h, List.length_map]
    refine ⟨Or.inl rfl, (List.length_filter_le _ _).trans hlen⟩
  · simp only [rewriteTrueGate, h]
    split
    · exact ⟨Or.inl rfl, by simp⟩
    · exact ⟨Or.inr (Or.inl rfl), by simp [hlen]⟩
  · simp only [rewriteTrueGate, h]
    cases g.inputs with
    | nil => simp
    | cons u rest =>
      by_cases hu : u = wOld <;> simp [hu]

private lemma rewriteTrueGate_eval (w0 : List Bool) (vC vD : List Bool)
    (hm : wiresMatch w0 true vC vD) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (rewriteTrueGate w0.length g).op.eval
      ((rewriteTrueGate w0.length g).inputs.map fun i => vD.getD i false) =
    g.op.eval (g.inputs.map fun i => vC.getD i false) := by
  change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
  rcases hop with h | h | h
  · simp only [rewriteTrueGate, h, GateOp.eval, List.map_map, List.all_map]
    induction g.inputs with
    | nil => rfl
    | cons u us ih =>
      by_cases hu : u = w0.length
      · subst hu
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.all_cons, Function.comp_apply, id_eq, hm.2.2.1, Bool.true_and]
        exact ih
      · have hne : (u != w0.length) = true := bne_iff_ne.mpr hu
        simp only [List.filter_cons, hne, ↓reduceIte, List.all_cons, Function.comp_apply, id_eq]
        rw [wiresMatch_getD_shiftDown hm hu, ih]
  · simp only [rewriteTrueGate, h]
    by_cases hmem : g.inputs.contains w0.length = true
    · rw [if_pos hmem]
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      refine ⟨true, List.mem_map.mpr ⟨w0.length, List.contains_iff_mem.mp hmem, hm.2.2.1⟩, rfl⟩
    · rw [if_neg hmem]
      simp only [GateOp.eval, List.map_map]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      have hne : u ≠ w0.length := fun heq => hmem (List.contains_iff_mem.mpr (heq ▸ hu))
      exact wiresMatch_getD_shiftDown hm hne
  · obtain ⟨op, inputs⟩ := g
    dsimp only at h ⊢
    subst h
    cases inputs with
    | nil => simp [rewriteTrueGate, GateOp.eval]
    | cons u rest =>
      by_cases hu : u = w0.length
      · subst hu
        simp only [rewriteTrueGate, GateOp.eval, ↓reduceIte, List.map_nil, List.any_nil,
          List.map_cons, List.headD_cons, hm.2.2.1, Bool.not_true]
      · simp only [rewriteTrueGate, GateOp.eval, hu, ↓reduceIte, List.map_cons, List.map_nil,
          List.headD_cons, wiresMatch_getD_shiftDown hm hu]

private lemma no_const_gate {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ x y : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false := by
  by_contra hconst
  push Not at hconst
  let x0 : Fin n → Bool := fun _ => false
  let b : Bool := (C.wires (List.ofFn x0)).getD (n + j) false
  have hall : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = b :=
    fun x => hconst x x0
  have hout_ne : C.output ≠ n + j := by
    intro heq
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    simp only [circuitFun, Circuit.eval, heq, hall x, hall y]
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  cases hb : b with
  | false =>
    let big : ℕ := n + C.gates.length
    let aliasGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire (n + j) big)⟩
    let D : Circuit := ⟨pre ++ post.map aliasGate, shiftDown (n + j) C.output⟩
    have hfitD : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with hpre | hpost
      · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
        have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
        exact ⟨hg0C.1, by simp [aliasGate, hg0C.2]⟩
    have hfunD : circuitFun n D = circuitFun n C := by
      funext x
      simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
      conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
      rw [List.foldl_append]
      let w0 := pre.foldl stepWire (List.ofFn x)
      have hw0_len : w0.length = n + j := by
        simp [w0, foldl_stepWire_length, hpre_len]
      have hbf : gj.op.eval (gj.inputs.map fun k => w0.getD k false) = false := by
        have hCj : (C.wires (List.ofFn x)).getD (n + j) false =
            gj.op.eval (gj.inputs.map fun k => w0.getD k false) := by
          rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
          rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
        rw [← hCj, hall x, hb]
      have hm0 : wiresMatch w0 false (stepWire w0 gj) w0 := by
        unfold stepWire; rw [hbf]; exact wiresMatch_init w0 false
      have hlenC : C.gates.length = pre.length + 1 + post.length := by
        have := congrArg List.length hgs; simp at this; omega
      have hmEnd : wiresMatch w0 false (post.foldl stepWire (stepWire w0 gj))
          ((post.map aliasGate).foldl stepWire w0) := by
        refine foldl_wiresMatch w0 false post (post.map aliasGate) (stepWire w0 gj) w0 hm0
          (by simp) ?_
        intro t htC htD vC vD hmv hvlen
        simp only [List.getElem_map, aliasGate, List.map_map]
        congr 1
        refine List.map_congr_left fun u _ => ?_
        simp only [Function.comp_apply, aliasWire]
        by_cases hu : u = n + j
        · subst hu
          simp only [↓reduceIte]
          rw [getD_ge_length vD big (by omega), ← hw0_len, hmv.2.2.1]
        · simp only [hu, ↓reduceIte]
          rw [← hw0_len]
          exact wiresMatch_getD_shiftDown hmv (by omega)
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmEnd (by rw [hw0_len]; exact hout_ne)
    have hle := hmin.2 D hfitD hfunD
    have hlenC : C.gates.length = pre.length + 1 + post.length := by
      have := congrArg List.length hgs; simp at this; omega
    simp only [Circuit.size, D, List.length_append, List.length_map] at hle
    omega
  | true =>
    let D : Circuit := ⟨pre ++ post.map (rewriteTrueGate (n + j)), shiftDown (n + j) C.output⟩
    have hfitD : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with hpre | hpost
      · exact hmin.1 g (by rw [hgs]; exact List.mem_append_left _ hpre)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hpost
        have hg0C := hmin.1 g0 (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
        exact rewriteTrueGate_fit (n + j) g0 hg0C
    have hfunD : circuitFun n D = circuitFun n C := by
      funext x
      simp only [circuitFun, Circuit.eval, wires_eq_foldl, D]
      conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
      rw [List.foldl_append]
      let w0 := pre.foldl stepWire (List.ofFn x)
      have hw0_len : w0.length = n + j := by
        simp [w0, foldl_stepWire_length, hpre_len]
      have hbt : gj.op.eval (gj.inputs.map fun k => w0.getD k false) = true := by
        have hCj : (C.wires (List.ofFn x)).getD (n + j) false =
            gj.op.eval (gj.inputs.map fun k => w0.getD k false) := by
          rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
          rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
        rw [← hCj, hall x, hb]
      have hm0 : wiresMatch w0 true (stepWire w0 gj) w0 := by
        unfold stepWire; rw [hbt]; exact wiresMatch_init w0 true
      have hmEnd : wiresMatch w0 true (post.foldl stepWire (stepWire w0 gj))
          ((post.map (rewriteTrueGate (n + j))).foldl stepWire w0) := by
        refine foldl_wiresMatch w0 true post (post.map (rewriteTrueGate (n + j)))
          (stepWire w0 gj) w0 hm0 (by simp) ?_
        intro t htC htD vC vD hmv _
        simp only [List.getElem_map]
        have hgC := hmin.1 (post[t]'htC)
          (by rw [hgs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.getElem_mem htC)))
        simpa only [hw0_len] using rewriteTrueGate_eval w0 vC vD hmv (post[t]'htC) hgC.1
      simpa only [hw0_len] using wiresMatch_getD_shiftDown hmEnd (by rw [hw0_len]; exact hout_ne)
    have hle := hmin.2 D hfitD hfunD
    have hlenC : C.gates.length = pre.length + 1 + post.length := by
      have := congrArg List.length hgs; simp at this; omega
    simp only [Circuit.size, D, List.length_append, List.length_map] at hle
    omega

theorem main (n : ℕ) (C : Circuit)
    (hmin : IsMinimalCircuit n C)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) :
    (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧
    (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧
    (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧
    (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧
      (GateOp.casesOn (motive := fun _ => List ℕ) p.1.op
        p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true) :=
  ⟨fun j hj => no_const_gate hmin hnc j hj,
   fun i j hij hj => no_duplicate_wire hmin i j hij hj,
   fun hne => output_last hmin hnc hne,
   fun j hj => every_gate_read hmin hnc j hj⟩

end PEqualNP.Outside.L_meta_173_aux.Reduced

namespace PEqualNP.Outside.L_meta_173_aux
theorem reduced_min : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true) :=
  PEqualNP.Outside.L_meta_173_aux.Reduced.main
end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux.NoNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  exact getD_snoc_eq _ _ _ _ hlen.symm

def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, NOkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
  · simp at hg
  · simp at hg

lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

lemma simplifyGate_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    simplifyGate GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [simplifyGate, simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => cases c <;> simp_all [simplifyGate, simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => simp at ht
  · simp at hlen

lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

lemma simplifyGate_both_const (op : GateOp) (m : ℕ) (c d : Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∃ e : Bool, simplifyGate op m [Sum.inl c, Sum.inl d] = (none, Sum.inl e) := by
  rcases hop with rfl | rfl
  · exact ⟨c && d, rfl⟩
  · exact ⟨c || d, rfl⟩

lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

lemma simplifyGate_mem_inputs_of_some (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (g : Gate) (hg : (simplifyGate op m ins).1 = some g) (w : ℕ) (hw : w ∈ g.inputs) :
    Sum.inr w ∈ ins := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp at hw; rcases hw with rfl | rfl <;> simp
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp at hw; rcases hw with rfl | rfl <;> simp
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp at hw; subst hw; simp
  · simp at hg
  · simp at hg

lemma simplifyGate_out_wire_mem (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (w : ℕ) (hw : (simplifyGate op m ins).2 = Sum.inr w) :
    w = m ∨ Sum.inr w ∈ ins := by
  cases op <;> simp only [simplifyGate] at hw
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hw
    · right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · left; exact hw.symm
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hw
    · right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · left; exact hw.symm
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hw
    left; exact hw.symm
  · simp at hw
  · simp at hw

lemma simplifyGate_some_snd (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (g : Gate) (hg : (simplifyGate op m ins).1 = some g) :
    (simplifyGate op m ins).2 = Sum.inr m := by
  cases op <;> simp only [simplifyGate] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg ⊢
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg ⊢
  · simp at hg
  · simp at hg

def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

def elimState (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) (j : ℕ) :
    List (Bool ⊕ ℕ) × List Gate :=
  elimPass m (gs.take j) acc

lemma elimState_zero (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimState m gs acc 0 = acc := rfl

lemma elimState_end (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimState m gs acc gs.length = elimPass m gs acc := by
  simp [elimState]

lemma elimState_succ (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    elimState m gs acc (j + 1) = elimStep m (elimState m gs acc j) gs[j] := by
  unfold elimState
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, elimPass_append,
    elimPass_cons, elimPass_nil]

lemma elimState_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j ≤ gs.length) :
    (elimState m gs acc j).1.length = acc.1.length + j := by
  rw [elimState, elimPass_fst_len, List.length_take, Nat.min_eq_left hj]

lemma elimState_getD_mono (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j k i : ℕ) (d : Bool ⊕ ℕ) (hjk : j ≤ k) (hk : k ≤ gs.length) (hi : i < acc.1.length + j) :
    (elimState m gs acc k).1.getD i d = (elimState m gs acc j).1.getD i d := by
  have htake : gs.take k = gs.take j ++ (gs.drop j).take (k - j) := by
    have h1 := List.take_add (l := gs) (i := j) (j := k - j)
    rw [show j + (k - j) = k by omega] at h1
    exact h1
  rw [elimState, htake, elimPass_append]
  exact elimPass_getD_lt m i d _ _ (by rw [elimPass_fst_len, List.length_take, Nat.min_eq_left (by omega)]; exact hi)

lemma elimState_snd_mono (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j k : ℕ) (hjk : j ≤ k) :
    (elimState m gs acc j).2.length ≤ (elimState m gs acc k).2.length := by
  induction k with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0; exact le_rfl
  | succ k ih =>
    by_cases h : j = k + 1
    · subst h; exact le_rfl
    · have h1 := ih (by omega)
      by_cases hk : k < gs.length
      · rw [elimState_succ m gs acc k hk]
        simp only [elimStep, List.length_append]
        omega
      · have htk : gs.take (k + 1) = gs.take k := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        change (elimState m gs acc j).2.length ≤ (elimPass m (gs.take (k + 1)) acc).2.length
        rw [htk]
        exact h1

lemma elimState_getD_at (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    (elimState m gs acc (j + 1)).1.getD (acc.1.length + j) (Sum.inl false) =
      (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
        (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).2 := by
  rw [elimState_succ m gs acc j hj]
  simp only [elimStep]
  exact getD_snoc_eq _ _ _ _ (elimState_fst_len m gs acc j (by omega)).symm

def elimDropped (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) : Finset ℕ :=
  (Finset.range gs.length).filter (fun j =>
    if hj : j < gs.length then
      (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
        (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
    else false)

lemma elimPass_card_dropped (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length + (elimDropped m gs acc).card = acc.2.length + gs.length := by
  suffices ∀ k ≤ gs.length,
      (elimState m gs acc k).2.length +
        ((Finset.range k).filter (fun j =>
          if hj : j < gs.length then
            (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
              (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
          else false)).card = acc.2.length + k by
    simpa [elimState_end, elimDropped] using this gs.length le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    simp [elimState_zero]
  | succ k ih =>
    intro hk
    have hklt : k < gs.length := by omega
    have hih := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnot : k ∉ (Finset.range k).filter (fun j =>
        if hj : j < gs.length then
          (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
            (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
        else false) := by
      simp
    rw [elimState_succ m gs acc k hklt]
    simp only [elimStep, List.length_append, hklt, ↓reduceDIte]
    cases hopt : (simplifyGate gs[k].op (m + (elimState m gs acc k).2.length)
        (gs[k].inputs.map fun i => (elimState m gs acc k).1.getD i (Sum.inl false))).1 with
    | none =>
      simp only [Option.toList_none, List.length_nil, Option.isNone_none, ↓reduceIte,
        Finset.card_insert_of_notMem hnot]
      omega
    | some g =>
      simp only [Option.toList_some, List.length_singleton, Option.isNone_some, Bool.false_eq_true,
        ↓reduceIte]
      omega

lemma mem_elimDropped_of_const (m : ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (j : ℕ) (hj : j < gs.length)
    (hnok : NOkGate gs[j]) (i : ℕ) (hi : i ∈ gs[j].inputs)
    (hc : ∃ c, (elimState m gs acc j).1.getD i (Sum.inl false) = Sum.inl c) :
    j ∈ elimDropped m gs acc := by
  rw [elimDropped, Finset.mem_filter, Finset.mem_range]
  refine ⟨hj, ?_⟩
  simp only [hj, ↓reduceDIte]
  obtain ⟨c, hc⟩ := hc
  have hnone : (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
      (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1 = none := by
    apply simplifyGate_none_of_const
    · exact hnok.1.1
    · simpa using hnok.1.2
    · intro h; simpa using hnok.2 h
    · exact ⟨c, List.mem_map.2 ⟨i, hi, hc⟩⟩
  rw [hnone]
  rfl

lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  obtain ⟨g, hg, hkg⟩ := hex
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hmem : j ∈ elimDropped m gs acc := by
    apply mem_elimDropped_of_const m gs acc j hj (hok _ (List.getElem_mem hj)) k hkg
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, by rw [elimState_getD_mono m gs acc 0 j k _ (Nat.zero_le _) (by omega) (by omega), elimState_zero]; exact hc⟩
  have hcard : 1 ≤ (elimDropped m gs acc).card := Finset.one_le_card.2 ⟨j, hmem⟩
  have htot := elimPass_card_dropped m gs acc
  omega

lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  have hsub : (Finset.range gs.length).filter (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)
      ⊆ elimDropped m gs acc := by
    intro j hj'
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    obtain ⟨hj, hkin⟩ := hj'
    simp only [hj, ↓reduceDIte] at hkin
    apply mem_elimDropped_of_const m gs acc j hj (hok _ (List.getElem_mem hj)) k hkin
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, by rw [elimState_getD_mono m gs acc 0 j k _ (Nat.zero_le _) (by omega) (by omega), elimState_zero]; exact hc⟩
  have hcnt : ((Finset.range gs.length).filter
      (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).card =
      (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
    clear hsub htwo hc hk hok acc m
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [List.filter_cons]
      have hbij : ((Finset.range (g :: gs).length).filter
          (fun j => if hj : j < (g :: gs).length then k ∈ (g :: gs)[j].inputs else false)).card =
          (if k ∈ g.inputs then 1 else 0) +
          ((Finset.range gs.length).filter
            (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).card := by
        have hsplit : (Finset.range (g :: gs).length).filter
            (fun j => if hj : j < (g :: gs).length then k ∈ (g :: gs)[j].inputs else false) =
            (if k ∈ g.inputs then {0} else ∅) ∪
            ((Finset.range gs.length).filter
              (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).image (· + 1) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image,
            List.length_cons]
          cases j with
          | zero =>
            by_cases hk0 : k ∈ g.inputs <;> simp [hk0]
          | succ j =>
            by_cases hk0 : k ∈ g.inputs <;> by_cases hlt : j < gs.length <;> simp [hk0, hlt]
        rw [hsplit, Finset.card_union_of_disjoint]
        · rw [Finset.card_image_of_injective _ (fun _ _ h => by omega)]
          split_ifs <;> simp
        · rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [Finset.mem_image] at hx2
          obtain ⟨y, _, rfl⟩ := hx2
          split_ifs at hx1 <;> simp at hx1
      rw [hbij, ih]
      by_cases hkg : k ∈ g.inputs <;> simp [hkg] <;> omega
  have hle := Finset.card_le_card hsub
  have htot := elimPass_card_dropped m gs acc
  omega

def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

lemma substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
  ⟨h.1, by simp [substGate]; exact h.2⟩

lemma substGate_nok (k a : ℕ) (g : Gate) (h : NOkGate g) : NOkGate (substGate k a g) :=
  ⟨substGate_ok k a g h.1, fun hop => by simp [substGate]; exact h.2 hop⟩

def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

lemma deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))

lemma deleteGate_nok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hnok : ∀ g ∈ C.gates, NOkGate g) : ∀ g ∈ (deleteGate m C j a).gates, NOkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hnok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_nok _ _ g0 (hnok g0 (List.mem_of_mem_drop hg0))

lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma deleteGate_getElem_lt (m : ℕ) (C : Circuit) (j₀ a j : ℕ)
    (hj₀ : j₀ < C.gates.length) (hjj₀ : j < j₀) :
    (deleteGate m C j₀ a).gates[j]'(by rw [deleteGate_len m C j₀ a hj₀]; omega) =
      C.gates[j]'(by omega) := by
  simp only [deleteGate]
  rw [List.getElem_append_left (by rw [List.length_take, Nat.min_eq_left (by omega)]; exact hjj₀),
    List.getElem_take]

lemma deleteGate_getElem_gt (m : ℕ) (C : Circuit) (j₀ a j : ℕ)
    (hj₀ : j₀ < C.gates.length) (hj : j < C.gates.length) (hjj₀ : j₀ < j) :
    (deleteGate m C j₀ a).gates[j - 1]'(by rw [deleteGate_len m C j₀ a hj₀]; omega) =
      substGate (m + j₀) a (C.gates[j]'hj) := by
  simp only [deleteGate]
  rw [List.getElem_append_right (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega),
    List.getElem_map, List.getElem_drop]
  congr 1
  have hidx : j₀ + 1 + (j - 1 - (C.gates.take j₀).length) = j := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
    omega
  exact congrArg (fun p : Fin C.gates.length => C.gates[p.1]'p.2)
    (Fin.ext (a := ⟨j₀ + 1 + (j - 1 - (C.gates.take j₀).length), by omega⟩) (b := ⟨j, hj⟩) hidx)

lemma wiresFrom_subst_aux (k a : ℕ) (hka : a < k) :
    ∀ (gs : List Gate) (w₁ w₂ : List Bool),
      w₁.length = w₂.length + 1 → k ≤ w₂.length →
      (∀ i < w₁.length, w₂.getD (substWire k a i) false = w₁.getD i false) →
      ∀ i < (wiresFrom gs w₁).length,
        (wiresFrom (gs.map (substGate k a)) w₂).getD (substWire k a i) false =
          (wiresFrom gs w₁).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro w₁ w₂ _ _ hag i hi
    exact hag i hi
  | cons g rest ih =>
    intro w₁ w₂ hlen hk hag
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hmap : ((substGate k a g).inputs.map fun i => w₂.getD i false) =
        (g.inputs.map fun i => w₁.getD i false) := by
      simp only [substGate, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < w₁.length
      · exact hag i hi
      · have hge : w₂.length ≤ substWire k a i := by
          unfold substWire
          split_ifs <;> omega
        rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
    rw [hmap]
    show ∀ i < (wiresFrom rest _).length,
        (wiresFrom (rest.map (substGate k a)) (w₂ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)])).getD
          (substWire k a i) false = _
    apply ih _ _ (by simp [hlen]) (by simp; omega)
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < w₁.length
    · have hsublt : substWire k a i < w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
      exact hag i hlt
    · have hieq : i = w₁.length := by omega
      have hsubeq : substWire k a i = w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]

lemma deleteGate_wires_eq (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length)
    (ha : a < m + j) (x : List Bool) (hx : x.length = m)
    (heq : (C.wires x).getD (m + j) false = (C.wires x).getD a false) :
    ∀ i < m + C.gates.length,
      ((deleteGate m C j a).wires x).getD (substWire (m + j) a i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length,
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a)) x).getD
          (substWire (m + j) a i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hag0 : ∀ i < w₁.length, w₂.getD (substWire (m + j) a i) false = w₁.getD i false := by
    intro i hi
    by_cases hlt : i < m + j
    · simp only [substWire, hlt, ↓reduceIte]
      rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]
    · have hieq : i = m + j := by omega
      subst hieq
      simp only [substWire, lt_irrefl, ↓reduceIte]
      have h1 : (C.wires x).getD (m + j) false = w₁.getD (m + j) false := by
        show (wiresFrom C.gates x).getD (m + j) false = _
        conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
        exact wiresFrom_getD_lt _ _ _ (by omega)
      have h2 : (C.wires x).getD a false = w₂.getD a false := by
        show (wiresFrom C.gates x).getD a false = _
        conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
        rw [wiresFrom_getD_lt _ _ _ (by omega), hw₁, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_lt _ _ _ _ (by omega)]
      rw [← h2, ← heq, h1]
  intro i hi
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  exact wiresFrom_subst_aux (m + j) a ha (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hag0
    i (by omega)

lemma deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
    (x : List Bool) (hx : x.length = m) :
    ∀ i < m + C.gates.length, i ≠ m + j →
      ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length, i ≠ m + j →
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
          (substWire (m + j) 0 i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop]
    exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
  have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
      w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
      (∀ g ∈ gs, (m + j) ∉ g.inputs) →
      (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
      ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
        (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
          (wiresFrom gs w₁').getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro w₁' w₂' _ _ _ hag i hi hne
      exact hag i hi hne
    | cons g rest ih =>
      intro w₁' w₂' hlen' hk' hnod hag'
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
      have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
          (g.inputs.map fun i => w₁'.getD i false) := by
        simp only [substGate, List.map_map]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp_apply]
        have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
        by_cases hlt : i < w₁'.length
        · exact hag' i hlt hne
        · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
            unfold substWire; split_ifs <;> omega
          rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
      rw [hmap]
      apply ih _ _ (by simp [hlen']) (by simp; omega)
        (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
      intro i hi hne
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < w₁'.length
      · have hsublt : substWire (m + j) 0 i < w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
        exact hag' i hlt hne
      · have hieq : i = w₁'.length := by omega
        have hsubeq : substWire (m + j) 0 i = w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
        rfl
  intro i hi hne
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
  intro u hu hune
  have hlt : u < m + j := by omega
  simp only [substWire, hlt, ↓reduceIte]
  rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

lemma deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output ≠ m + j)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
    by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
  intro x
  show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
  · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
      rw [deleteGate_len m C j 0 hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
        m + (deleteGate m C j 0).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma deleteConstGate {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (j : ℕ) (hj : j < C.gates.length) (c : Bool)
    (hconst : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false = c)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x') :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  set gs₁ := C.gates.take j with hgs₁
  set gs₂ := C.gates.drop (j + 1) with hgs₂
  have hsplit : C.gates = gs₁ ++ [C.gates[j]] ++ gs₂ := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: gs₂ := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [hgs₁, List.append_assoc, List.singleton_append] using h1.symm
  set init : List (Bool ⊕ ℕ) :=
    List.ofFn (fun i : Fin (m + j) => Sum.inr (i : ℕ)) ++ [Sum.inl c] with hinit
  set acc := elimPass m gs₂ (init, gs₁) with hacc
  have hinv : ∀ x : Fin m → Bool,
      ElimInv m (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := by
    intro x
    rw [hsplit, wiresFrom_append, hacc]
    apply elimInv_pass m (List.ofFn x) gs₂ _ (init, gs₁)
      (fun g hg => (hnok g (List.mem_of_mem_drop hg)).1)
    have hlen1 : (wiresFrom gs₁ (List.ofFn x)).length = m + j := by
      rw [wiresFrom_length, List.length_ofFn, hgs₁, List.length_take, Nat.min_eq_left (by omega)]
    have hlen2 : (wiresFrom (gs₁ ++ [C.gates[j]]) (List.ofFn x)).length = m + j + 1 := by
      rw [wiresFrom_append, wiresFrom_length, hlen1]; simp
    refine ⟨by simp, by simp [hinit, hlen2], ?_⟩
    intro i
    by_cases h1 : i < m + j
    · have hget : init.getD i (Sum.inl false) = Sum.inr i := by
        rw [hinit, getD_snoc_lt _ _ _ _ (by simp; exact h1), ofFn_getD_lt _ _ _ h1]
      rw [hget]
      refine ⟨by simp [statValid, hgs₁, List.length_take]; omega, ?_⟩
      simp only [statVal]
      rw [wiresFrom_append]
      exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
    · by_cases h2 : i = m + j
      · have hget : init.getD i (Sum.inl false) = Sum.inl c := by
          rw [hinit, getD_snoc_eq _ _ _ _ (by simp; exact h2)]
        rw [hget]
        refine ⟨trivial, ?_⟩
        simp only [statVal]
        have hcx := hconst x
        rw [h2]
        have hEq : (wiresFrom (gs₁ ++ [C.gates[j]]) (List.ofFn x)).getD (m + j) false =
            (C.wires (List.ofFn x)).getD (m + j) false := by
          show _ = (wiresFrom C.gates (List.ofFn x)).getD (m + j) false
          conv_rhs => rw [hsplit, wiresFrom_append]
          exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
        rw [hEq, hcx]
      · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
            List.getD_eq_default _ _ (by omega)]
        exact ⟨trivial, rfl⟩
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        circuitFun m C x := by
    intro x
    exact ((hinv x).2.2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr out' =>
    refine ⟨⟨acc.2, out'⟩, elimPass_ok m gs₂ _ (fun g hg => (hnok g (List.mem_of_mem_take hg)).1), ?_, ?_⟩
    · show acc.2.length ≤ C.gates.length - 1
      have hlen := elimPass_len m gs₂ (init, gs₁)
      rw [← hacc] at hlen
      simp only [Prod.snd] at hlen
      have hl1 : gs₁.length = j := by rw [hgs₁, List.length_take, Nat.min_eq_left (by omega)]
      have hl2 : gs₂.length = C.gates.length - (j + 1) := by rw [hgs₂, List.length_drop]
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

lemma deleteAliasGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j)
    (heq : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false =
      (C.wires (List.ofFn x)).getD a false) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j a, deleteGate_ok m C j a hok,
    by show (deleteGate m C j a).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j a hj], ?_⟩
  intro x
  show ((deleteGate m C j a).wires (List.ofFn x)).getD (substWire (m + j) a C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_wires_eq m C j a hj ha (List.ofFn x) (by simp) (heq x) C.output hlt
  · have hge1 : (deleteGate m C j a).gates.length + m ≤ substWire (m + j) a C.output := by
      rw [deleteGate_len m C j a hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j a).wires (List.ofFn x)).length =
        m + (deleteGate m C j a).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

lemma elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m gs (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := elimPass_len_lt m (v : ℕ) gs (initVar m v b, []) hnok
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

lemma list_split_unique_filter {α : Type*} (p : α → Bool) (l : List α)
    (h : (l.filter p).length = 1) :
    ∃ l₁ a l₂, l = l₁ ++ [a] ++ l₂ ∧ p a = true ∧
      (∀ x ∈ l₁, p x = false) ∧ (∀ x ∈ l₂, p x = false) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    cases hpx : p x with
    | true =>
      have h0 : (xs.filter p).length = 0 := by
        simp only [List.filter_cons, hpx, ↓reduceIte, List.length_cons] at h
        omega
      have hnil : xs.filter p = [] := List.eq_nil_of_length_eq_zero h0
      refine ⟨[], x, xs, rfl, hpx, by simp, ?_⟩
      intro y hy
      by_contra hpy
      have hpyt : p y = true := by cases hp : p y <;> simp_all
      have : y ∈ xs.filter p := List.mem_filter.2 ⟨hy, hpyt⟩
      rw [hnil] at this
      simp at this
    | false =>
      have h1 : (xs.filter p).length = 1 := by
        simpa [hpx] using h
      obtain ⟨l₁, a, l₂, rfl, hpa, hl₁, hl₂⟩ := ih h1
      refine ⟨x :: l₁, a, l₂, by simp, hpa, ?_, hl₂⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hpx
      · exact hl₁ y hy'

lemma elim_two_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc0 : ∃ x x' : Fin m → Bool,
      F (Function.update x v false) ≠ F (Function.update x' v false))
    (hnc1 : ∃ x x' : Fin m → Bool,
      F (Function.update x v true) ≠ F (Function.update x' v true)) :
    2 ≤ s ∧ (HasCircuitSize m (fun x => F (Function.update x v false)) (s - 2) ∨
      HasCircuitSize m (fun x => F (Function.update x v true)) (s - 2)) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc0
    have h1 := hev (Function.update x v false)
    have h2 := hev (Function.update x' v false)
    have hw1 : (C.wires (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v false) = false := by
      rw [← h1]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw1
    have e2 : F (Function.update x' v false) = false := by
      rw [← h2]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  set cnt := (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length with hcnt
  by_cases hge2 : 2 ≤ cnt
  · set acc := elimPass m gs (initVar m v false, []) with hacc
    have hlen : acc.2.length + 2 ≤ gs.length := by
      have := elimPass_len_two m (v : ℕ) gs (initVar m v false, []) hnok
        (by simp [initVar])
        ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
        (by rw [← hcnt]; exact hge2)
      rw [← hacc] at this
      simpa using this
    have hval : ∀ x : Fin m → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
          F (Function.update x v false) := by
      intro x
      have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v false, [])
        (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x)
      rw [← hacc] at hinv
      rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
      exact hev (Function.update x v false)
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, x', hne⟩ := hnc0
      have hx := hval x; have hx' := hval x'
      rw [hst] at hx hx'
      exact absurd (hx.symm.trans hx') hne
    | inr j =>
      refine ⟨by omega, Or.inl ⟨⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩⟩
      · show acc.2.length ≤ s - 2; omega
      · intro x; have := hval x; rw [hst] at this; exact this
  · by_cases hzero : cnt = 0
    · exfalso
      have hnil : gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcnt]; exact hzero)
      obtain ⟨x, hne⟩ := hdep
      have hag := wiresFrom_agree gs {(v : ℕ)}
        (List.ofFn (Function.update x v false))
        (List.ofFn (Function.update x v true))
        (by simp)
        (by intro u hu; simp at hu; subst hu; simp)
        (by
          intro i hi; simp at hi
          by_cases hlt : i < m
          · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
              intro h; apply hi; exact congrArg Fin.val h
            rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                Function.update_of_ne hne', Function.update_of_ne hne']
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg i hi hmem
          simp at hmem; subst hmem
          have : g ∈ gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) :=
            List.mem_filter.2 ⟨hg, decide_eq_true hi⟩
          rw [hnil] at this; simp at this)
      have hEq := hag.2 C.output (by simpa using hout_ne)
      rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
      exact hne ((hev _).symm.trans (hEq.trans (hev _)))
    · have hone : (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length = 1 := by
        rw [← hcnt]; omega
      have hsp := list_split_unique_filter (fun g => decide ((v : ℕ) ∈ g.inputs)) gs hone
      rcases hsp with ⟨gs₁, g₁, gs₂, hsplit, hg₁in, hgs₁no, hgs₂no⟩
      have hv_in : (v : ℕ) ∈ g₁.inputs := of_decide_eq_true hg₁in
      have hnok₁ : NOkGate g₁ := hnok g₁ (by rw [hsplit]; simp)
      set b : Bool := match g₁.op with | GateOp.or => true | _ => false with hb
      have hncb : ∃ x x' : Fin m → Bool,
          F (Function.update x v b) ≠ F (Function.update x' v b) := by
        cases hbc : b with
        | false => exact hnc0
        | true => exact hnc1
      set acc₁ := elimPass m gs₁ (initVar m v b, []) with hacc₁
      set accM := elimStep m acc₁ g₁ with haccM
      set acc := elimPass m gs₂ accM with hacc
      have hacc_eq : acc = elimPass m gs (initVar m v b, []) := by
        rw [hsplit, elimPass_append, elimPass_append, ← hacc₁, elimPass_cons, elimPass_nil, ← haccM]
      have hacc₁_len : acc₁.1.length = m + gs₁.length := by
        rw [hacc₁, elimPass_fst_len]; simp [initVar]
      have hacc₁_v : acc₁.1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
        rw [hacc₁, elimPass_getD_lt _ _ _ _ _ (by simp [initVar])]
        rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      have hmid_props : accM.2.length = acc₁.2.length ∧
          ∃ c : Bool, accM.1.getD (m + gs₁.length) (Sum.inl false) = Sum.inl c := by
        have hmem : Sum.inl b ∈ (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨(v : ℕ), hv_in, hacc₁_v⟩
        have hres : ∃ c : Bool,
            simplifyGate g₁.op (m + acc₁.2.length)
              (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) = (none, Sum.inl c) := by
          rcases hnok₁.1.1 with hop | hop | hop
          · have : g₁.op = GateOp.and := hop
            have hbf : b = false := by simp [hb, this]
            rw [this]
            rw [hbf] at hmem
            exact ⟨false, simplifyGate_and_false _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.or := hop
            have hbt : b = true := by simp [hb, this]
            rw [this]
            rw [hbt] at hmem
            exact ⟨true, simplifyGate_or_true _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.not := hop
            have hbf : b = false := by simp [hb, this]
            have hlen1 : g₁.inputs.length ≤ 1 := hnok₁.2 this
            have hsing : g₁.inputs = [(v : ℕ)] := by
              rcases hgi : g₁.inputs with _ | ⟨a, _ | ⟨d, l⟩⟩
              · rw [hgi] at hv_in; simp at hv_in
              · rw [hgi] at hv_in; simp at hv_in; subst hv_in; rfl
              · rw [hgi] at hlen1; simp at hlen1
            rw [this, hsing, List.map_singleton, hacc₁_v, hbf]
            exact ⟨true, simplifyGate_not_const _ false⟩
        obtain ⟨c, hc⟩ := hres
        refine ⟨by simp only [haccM, elimStep, hc, Option.toList_none, List.append_nil], c, ?_⟩
        simp only [haccM, elimStep, hc]
        exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
      have hval : ∀ x : Fin m → Bool,
          statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
            F (Function.update x v b) := by
        intro x
        have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
        rw [← hacc_eq] at hinv
        rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
        exact hev (Function.update x v b)
      have hout_ne_w1 : C.output ≠ m + gs₁.length := by
        intro heq
        obtain ⟨c, hc⟩ := hmid_props.2
        have hacc_w1 : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
          rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, elimStep, hacc₁_len])]
          exact hc
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hacc_w1] at hx hx'
        exact hne (hx.symm.trans hx')
      have hex₂ : ∃ g ∈ gs₂, m + gs₁.length ∈ g.inputs := by
        by_contra hno
        have hno' : ∀ g ∈ gs₂, m + gs₁.length ∉ g.inputs := fun g hg hw => hno ⟨g, hg, hw⟩
        obtain ⟨x, hne⟩ := hdep
        have hag₁ := wiresFrom_agree gs₁ {(v : ℕ)}
          (List.ofFn (Function.update x v false))
          (List.ofFn (Function.update x v true))
          (by simp)
          (by intro u hu; simp at hu; subst hu; simp)
          (by
            intro i hi; simp at hi
            by_cases hlt : i < m
            · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
                intro h; apply hi; exact congrArg Fin.val h
              rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                  Function.update_of_ne hne', Function.update_of_ne hne']
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)])
          (by
            intro g hg i hi hmem
            simp at hmem; subst hmem
            have := hgs₁no g hg
            simp [hi] at this)
        set w0 := wiresFrom gs₁ (List.ofFn (Function.update x v false))
        set w1 := wiresFrom gs₁ (List.ofFn (Function.update x v true))
        have hw0_len : w0.length = m + gs₁.length := by simp [w0, wiresFrom_length]
        have hw1_len : w1.length = m + gs₁.length := by simp [w1, wiresFrom_length]
        have hag₂ := wiresFrom_agree gs₂ {(v : ℕ), m + gs₁.length}
          (wiresFrom [g₁] w0) (wiresFrom [g₁] w1)
          (by simp [wiresFrom_length, hw0_len, hw1_len])
          (by
            intro u hu
            rcases hu with rfl | rfl
            · simp [wiresFrom_length, hw0_len]; omega
            · simp [wiresFrom_length, hw0_len])
          (by
            intro i hi
            have hiv : i ≠ (v : ℕ) := fun h => hi (Or.inl h)
            have hiw : i ≠ m + gs₁.length := fun h => hi (Or.inr h)
            simp only [wiresFrom_cons, wiresFrom_nil]
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag₁.2 i (by simpa using hiv))
          (by
            intro g hg i hi hmem
            rcases hmem with rfl | rfl
            · have := hgs₂no g hg; simp [hi] at this
            · exact hno' g hg hi)
        have hco : C.output ∉ ({(v : ℕ), m + gs₁.length} : Set ℕ) := by
          intro h; rcases h with h | h
          · exact hout_ne h
          · exact hout_ne_w1 h
        have hEq := hag₂.2 C.output hco
        have hrew0 : wiresFrom gs₂ (wiresFrom [g₁] w0) =
            wiresFrom gs (List.ofFn (Function.update x v false)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        have hrew1 : wiresFrom gs₂ (wiresFrom [g₁] w1) =
            wiresFrom gs (List.ofFn (Function.update x v true)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        rw [hrew0, hrew1, hgs, wiresFrom_norm, wiresFrom_norm] at hEq
        exact hne ((hev _).symm.trans (hEq.trans (hev _)))
      have hlen₂ := elimPass_len_lt m (m + gs₁.length) gs₂ accM
        (fun g hg => hnok g (by rw [hsplit]; simp [hg]))
        (by simp [haccM, elimStep, hacc₁_len])
        hmid_props.2
        hex₂
      rw [← hacc] at hlen₂
      have hlen₁ : acc₁.2.length ≤ gs₁.length := by
        have := elimPass_len m gs₁ (initVar m v b, [])
        rw [← hacc₁] at this; simpa using this
      have hsplit_len : gs.length = gs₁.length + 1 + gs₂.length := by
        rw [hsplit]; simp; omega
      have htot : acc.2.length + 2 ≤ gs.length := by omega
      cases hst : acc.1.getD C.output (Sum.inl false) with
      | inl c =>
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hst] at hx hx'
        exact absurd (hx.symm.trans hx') hne
      | inr j =>
        have hres : HasCircuitSize m (fun x => F (Function.update x v b)) (s - 2) := by
          refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
          · rw [hacc_eq]; exact elimPass_ok m gs _ (by simp)
          · show acc.2.length ≤ s - 2; omega
          · intro x; have := hval x; rw [hst] at this; exact this
        refine ⟨by omega, ?_⟩
        cases hbc : b with
        | false => rw [hbc] at hres; exact Or.inl hres
        | true => rw [hbc] at hres; exact Or.inr hres

lemma min_output_lt {m : ℕ} (C : Circuit)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x') :
    C.output < m + C.gates.length := by
  by_contra hge
  obtain ⟨x, x', hne⟩ := hnc
  have h1 : circuitFun m C x = false := by
    show (wiresFrom C.gates (List.ofFn x)).getD C.output false = false
    exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
  have h2 : circuitFun m C x' = false := by
    show (wiresFrom C.gates (List.ofFn x')).getD C.output false = false
    exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
  exact hne (h1.trans h2.symm)

lemma min_no_const {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x')
    (j : ℕ) (hj : j < C.gates.length) (c : Bool) :
    ¬ (∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false = c) := by
  intro hconst
  exact hmin (C.gates.length - 1) (by omega) (deleteConstGate C hnok j hj c hconst hnc)

lemma min_no_alias {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j) :
    ¬ (∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false =
      (C.wires (List.ofFn x)).getD a false) := by
  intro heq
  exact hmin (C.gates.length - 1) (by omega)
    (deleteAliasGate C (fun g hg => (hnok g hg).1) j a hj ha heq)

lemma min_no_dead {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (j : ℕ) (hj : j < C.gates.length) :
    C.output = m + j ∨ ∃ j' : ℕ, ∃ hj' : j' < C.gates.length, j < j' ∧ (m + j) ∈ C.gates[j'].inputs := by
  by_contra h
  have hout : C.output ≠ m + j := fun heq => h (Or.inl heq)
  have hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs :=
    fun j' hj' hlt hmem => h (Or.inr ⟨j', hj', hlt, hmem⟩)
  exact hmin (C.gates.length - 1) (by omega)
    (deleteDeadGate C (fun g hg => (hnok g hg).1) j hj hout hno)

lemma wire_eval_gate {m : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin m → Bool) :
    (C.wires (List.ofFn x)).getD (m + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < m + j then (C.wires (List.ofFn x)).getD i false else false) := by
  show (wiresFrom C.gates (List.ofFn x)).getD (m + j) false = _
  have h1 := wiresFrom_getD_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = m + j := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
  by_cases hi : i < m + j
  · simp only [hi, ↓reduceIte]
    have hsp : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [show C.wires (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl, hsp, wiresFrom_append]
    exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

lemma min_gate_wf {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x')
    (j : ℕ) (hj : j < C.gates.length) :
    (C.gates[j].op = GateOp.not → ∃ a, a < m + j ∧ C.gates[j].inputs = [a]) ∧
    ((C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) →
      ∃ a b, a < m + j ∧ b < m + j ∧ a ≠ b ∧ C.gates[j].inputs = [a, b]) := by
  have hg := hnok C.gates[j] (List.getElem_mem hj)
  constructor
  · intro hop
    have hlen1 := hg.2 hop
    rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exfalso
      apply min_no_const C hnok hmin hnc j hj true
      intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
    · by_cases ha : a < m + j
      · exact ⟨a, ha, rfl⟩
      · exfalso
        apply min_no_const C hnok hmin hnc j hj true
        intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, GateOp.eval]
    · rw [hins] at hlen1; simp at hlen1
  · intro hop
    have hlen2 := hg.1.2
    rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · exfalso
      rcases hop with hop | hop
      · apply min_no_const C hnok hmin hnc j hj true
        intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
      · apply min_no_const C hnok hmin hnc j hj false
        intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
    · exfalso
      by_cases ha : a < m + j
      · apply min_no_alias C hnok hmin j a hj ha
        intro x; rw [wire_eval_gate C j hj x, hins]
        rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
      · apply min_no_const C hnok hmin hnc j hj false
        intro x; rw [wire_eval_gate C j hj x, hins]
        rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
    · by_cases ha : a < m + j
      · by_cases hb : b < m + j
        · by_cases hab : a = b
          · exfalso
            subst hab
            apply min_no_alias C hnok hmin j a hj ha
            intro x; rw [wire_eval_gate C j hj x, hins]
            rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
          · exact ⟨a, b, ha, hb, hab, rfl⟩
        · exfalso
          rcases hop with hop | hop
          · apply min_no_const C hnok hmin hnc j hj false
            intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
          · apply min_no_alias C hnok hmin j a hj ha
            intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
      · exfalso
        by_cases hb : b < m + j
        · rcases hop with hop | hop
          · apply min_no_const C hnok hmin hnc j hj false
            intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
          · apply min_no_alias C hnok hmin j b hj hb
            intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
        · apply min_no_const C hnok hmin hnc j hj false
          intro x; rw [wire_eval_gate C j hj x, hins]
          rcases hop with hop | hop <;> simp [hop, ha, hb, GateOp.eval]
    · rw [hins] at hlen2; simp at hlen2

lemma elim_var_circuit {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (v : Fin m) (b : Bool)
    (hnc : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b)) :
    let acc := elimPass m C.gates (initVar m v b, [])
    ∃ out : ℕ, acc.1.getD C.output (Sum.inl false) = Sum.inr out ∧
      (∀ g ∈ acc.2, OkGate g) ∧
      acc.2.length + (elimDropped m C.gates (initVar m v b, [])).card = C.gates.length ∧
      circuitFun m ⟨acc.2, out⟩ = fun x => circuitFun m C (Function.update x v b) := by
  intro acc
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        circuitFun m C (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) C.gates _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    exact (hinv.2.2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr out =>
    refine ⟨out, rfl, elimPass_ok m C.gates _ (by simp), ?_, ?_⟩
    · have := elimPass_card_dropped m C.gates (initVar m v b, [])
      simpa using this
    · funext x
      have := hval x
      rw [hst] at this
      exact this

lemma acyclic_leaf_cases {n : ℕ} (G : SimpleGraph (Fin n)) (hAcyc : G.IsAcyclic)
    (hEdge : ∃ u v : Fin n, G.Adj u v) :
    ∃ ℓ p : Fin n, G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧
      ((∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ' p ∧ ∀ w, G.Adj ℓ' w → w = p) ∨
       (∀ w, G.Adj p w → w = ℓ) ∨
       (∃ q : Fin n, q ≠ ℓ ∧ G.Adj p q ∧ ∀ w, G.Adj p w → w = ℓ ∨ w = q)) := by
  classical
  have hlen_lt : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length < n := by
    intro u v P hP
    have h1 : P.support.length ≤ Fintype.card (Fin n) := hP.support_nodup.length_le_card
    rw [P.length_support, Fintype.card_fin] at h1
    omega
  set S : Finset ℕ := (Finset.range n).filter
    (fun k => ∃ u v : Fin n, ∃ P : G.Walk u v, P.IsPath ∧ P.length = k) with hS
  have hS_ne : S.Nonempty := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    refine ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, u₀, v₀,
      SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_, rfl⟩⟩
    · have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
        SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
      exact hlen_lt _ hp
    · exact SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
  set m := S.max' hS_ne with hm
  have hm_mem : m ∈ S := Finset.max'_mem S hS_ne
  have hm_ge : 1 ≤ m := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
    have h1 : 1 ∈ S := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (hlen_lt _ hp), u₀, v₀, _, hp, rfl⟩
    exact Finset.le_max' S 1 h1
  have hm_max : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length ≤ m := by
    intro u v P hP
    have hmem : P.length ∈ S := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (hlen_lt P hP), u, v, P, hP, rfl⟩
    exact Finset.le_max' S P.length hmem
  obtain ⟨_, ℓ, z, P, hP, hPlen⟩ := Finset.mem_filter.1 hm_mem
  cases P with
  | nil => simp at hPlen; omega
  | @cons _ p _ hlp Q =>
    have hQ : Q.IsPath := hP.of_cons
    have hℓ_not_Q : ℓ ∉ Q.support := by
      have hnd := hP.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1
    have hℓ_leaf : ∀ w, G.Adj ℓ w → w = p := by
      intro w hlw
      by_cases hw : w ∈ (SimpleGraph.Walk.cons hlp Q).support
      · simpa using hAcyc.eq_snd_of_adj_start hP hlw hw
      · exfalso
        have hP' : (SimpleGraph.Walk.cons hlw.symm (SimpleGraph.Walk.cons hlp Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP hw
        have hle := hm_max _ hP'
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    have hnotQ_leaf : ∀ w, G.Adj p w → w ∉ Q.support → ∀ u, G.Adj w u → u = p := by
      intro w hpw hwQ u hwu
      by_contra hup
      by_cases huQ : u ∈ Q.support
      · set Q' := Q.takeUntil u huQ
        have hQ' : Q'.IsPath := hQ.takeUntil huQ
        have hR : (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).IsPath := by
          refine SimpleGraph.Walk.IsPath.cons
            (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hwu.ne])) ?_
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or]
          exact ⟨hpw.ne, Ne.symm hup⟩
        have heq := (hAcyc.subsingleton_path p u).elim ⟨Q', hQ'⟩ ⟨_, hR⟩
        have hw_in_R : w ∈ (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).support := by
          simp
        have hw_in_Q' : w ∈ Q'.support := by
          rw [Subtype.mk.inj heq]; exact hw_in_R
        exact hwQ (SimpleGraph.Walk.support_takeUntil_subset_support Q huQ hw_in_Q')
      · have hP1 : (SimpleGraph.Walk.cons hpw.symm Q).IsPath :=
          SimpleGraph.Walk.IsPath.cons hQ hwQ
        have hu_not : u ∉ (SimpleGraph.Walk.cons hpw.symm Q).support := by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
          exact ⟨hwu.ne.symm, huQ⟩
        have hP2 : (SimpleGraph.Walk.cons hwu.symm (SimpleGraph.Walk.cons hpw.symm Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP1 hu_not
        have hle := hm_max _ hP2
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    refine ⟨ℓ, p, hlp, hℓ_leaf, ?_⟩
    cases Q with
    | nil =>
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj z ℓ'
      · obtain ⟨ℓ', hne, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.nil : G.Walk z z).support := by
          simp [hadj.ne.symm]
        exact Or.inl ⟨ℓ', hne, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inl ?_)
        intro w hpw
        by_contra hwne
        exact hother ⟨w, hwne, hpw⟩
    | @cons _ q _ hpq Q' =>
      have hq_ne_ℓ : q ≠ ℓ := by
        intro hq
        apply hℓ_not_Q
        rw [← hq]
        simp
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ ℓ' ≠ q ∧ G.Adj p ℓ'
      · obtain ⟨ℓ', hne1, hne2, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.cons hpq Q').support := by
          intro hmem
          exact hne2 (by simpa using hAcyc.eq_snd_of_adj_start hQ hadj hmem)
        exact Or.inl ⟨ℓ', hne1, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inr ⟨q, hq_ne_ℓ, hpq, ?_⟩)
        intro w hpw
        by_contra hnot
        exact hother ⟨w, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h), hpw⟩

def IsVC {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S

def HasMinVC {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  (∃ S : Finset (Fin n), IsVC G S ∧ S.card = t) ∧
  (∀ S : Finset (Fin n), IsVC G S → t ≤ S.card)

lemma hasMinVC_exists {n : ℕ} (G : SimpleGraph (Fin n)) : ∃ t : ℕ, HasMinVC G t := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), IsVC G S ∧ S.card = k :=
    ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro S hS
  exact Nat.find_min' hex ⟨S, hS, rfl⟩

lemma hasMinVC_empty {n t : ℕ} (G : SimpleGraph (Fin n))
    (hempty : ∀ u v : Fin n, ¬ G.Adj u v) (hvc : HasMinVC G t) : t = 0 := by
  have hle : t ≤ (∅ : Finset (Fin n)).card := hvc.2 ∅ (fun u v h => absurd h (hempty u v))
  simpa using hle

def deleteVertexEdges {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ≠ p ∧ v ≠ p
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

lemma deleteVertexEdges_le {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    deleteVertexEdges G p ≤ G :=
  fun _ _ h => h.1

lemma hasMinVC_deleteEdge {n t t₁ : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (hvc : HasMinVC G t) (hvc₁ : HasMinVC (G.deleteEdges {s(ℓ, p)}) t₁) :
    t₁ ≤ t ∧ t ≤ t₁ + 1 := by
  obtain ⟨⟨S, hS, hSc⟩, hmin⟩ := hvc
  obtain ⟨⟨S₁, hS₁, hS₁c⟩, hmin₁⟩ := hvc₁
  constructor
  · have hS_sub : IsVC (G.deleteEdges {s(ℓ, p)}) S := fun u v h => hS u v h.1
    rw [← hSc]; exact hmin₁ S hS_sub
  · have hcov : IsVC G (insert p S₁) := by
      intro u v huv
      by_cases hmem : s(u, v) = s(ℓ, p)
      · rw [Sym2.eq_iff] at hmem
        rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
        · exact Or.inr (hvp ▸ Finset.mem_insert_self p S₁)
        · exact Or.inl (hup ▸ Finset.mem_insert_self p S₁)
      · have hadj : (G.deleteEdges {s(ℓ, p)}).Adj u v :=
          SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩
        rcases hS₁ u v hadj with hu | hv
        · exact Or.inl (Finset.mem_insert_of_mem hu)
        · exact Or.inr (Finset.mem_insert_of_mem hv)
    have hle := hmin (insert p S₁) hcov
    have hcard : (insert p S₁).card ≤ S₁.card + 1 := Finset.card_insert_le p S₁
    omega

lemma hasMinVC_deleteLeafEdge_eq {n t t₁ : ℕ} (G : SimpleGraph (Fin n)) (ℓ ℓ' p : Fin n)
    (hℓ'ne : ℓ' ≠ ℓ) (hℓ'p : G.Adj ℓ' p) (hℓ'leaf : ∀ w, G.Adj ℓ' w → w = p)
    (hvc : HasMinVC G t) (hvc₁ : HasMinVC (G.deleteEdges {s(ℓ, p)}) t₁) :
    t₁ = t := by
  have hle : t₁ ≤ t := (hasMinVC_deleteEdge G ℓ p hvc hvc₁).1
  obtain ⟨⟨S₁, hS₁, hS₁c⟩, _⟩ := hvc₁
  have hge : t ≤ t₁ := by
    by_cases hp : p ∈ S₁
    · have hcov : IsVC G S₁ := by
        intro u v huv
        by_cases hmem : s(u, v) = s(ℓ, p)
        · rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
          · exact Or.inr (hvp ▸ hp)
          · exact Or.inl (hup ▸ hp)
        · exact hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩)
      rw [← hS₁c]; exact hvc.2 S₁ hcov
    · have hℓ'in : ℓ' ∈ S₁ := by
        have hne_edge : s(ℓ', p) ≠ s(ℓ, p) := by
          intro heq
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hℓ'ne h1
          · exact hℓ'p.ne h1
        have hadj : (G.deleteEdges {s(ℓ, p)}).Adj ℓ' p :=
          SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, by simpa using hne_edge⟩
        rcases hS₁ ℓ' p hadj with h | h
        · exact h
        · exact absurd h hp
      set S' := insert p (S₁.erase ℓ')
      have hcov : IsVC G S' := by
        intro u v huv
        by_cases hmem : s(u, v) = s(ℓ, p)
        · rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
          · exact Or.inr (hvp ▸ Finset.mem_insert_self p _)
          · exact Or.inl (hup ▸ Finset.mem_insert_self p _)
        · rcases hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with hu | hv
          · by_cases huℓ : u = ℓ'
            · subst huℓ
              have hv_eq : v = p := hℓ'leaf v huv
              exact Or.inr (hv_eq ▸ Finset.mem_insert_self p _)
            · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨huℓ, hu⟩))
          · by_cases hvℓ : v = ℓ'
            · subst hvℓ
              have hu_eq : u = p := hℓ'leaf u huv.symm
              exact Or.inl (hu_eq ▸ Finset.mem_insert_self p _)
            · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hvℓ, hv⟩))
      have hcard : S'.card = S₁.card := by
        have hp_not : p ∉ S₁.erase ℓ' := fun h => hp (Finset.mem_of_mem_erase h)
        rw [Finset.card_insert_of_notMem hp_not, Finset.card_erase_of_mem hℓ'in]
        have hpos : 1 ≤ S₁.card := Finset.one_le_card.2 ⟨ℓ', hℓ'in⟩
        omega
      have := hvc.2 S' hcov
      omega
  omega

lemma hasMinVC_deleteVertex {n t t' : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (hlp : G.Adj ℓ p) (hleaf : ∀ w, G.Adj ℓ w → w = p)
    (hvc : HasMinVC G t) (hvc' : HasMinVC (deleteVertexEdges G p) t') :
    t' + 1 = t := by
  obtain ⟨⟨S, hS, hSc⟩, hmin⟩ := hvc
  obtain ⟨⟨S', hS', hS'c⟩, hmin'⟩ := hvc'
  have hle : t ≤ t' + 1 := by
    have hcov : IsVC G (insert p S') := by
      intro u v huv
      by_cases hup : u = p
      · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
      · by_cases hvp : v = p
        · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
        · rcases hS' u v ⟨huv, hup, hvp⟩ with hu | hv
          · exact Or.inl (Finset.mem_insert_of_mem hu)
          · exact Or.inr (Finset.mem_insert_of_mem hv)
    have := hmin (insert p S') hcov
    have := Finset.card_insert_le p S'
    omega
  have hge : t' + 1 ≤ t := by
    by_cases hp : p ∈ S
    · have hcov : IsVC (deleteVertexEdges G p) (S.erase p) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · exact Or.inl (Finset.mem_erase.2 ⟨huv.2.1, hu⟩)
        · exact Or.inr (Finset.mem_erase.2 ⟨huv.2.2, hv⟩)
      have h1 := hmin' (S.erase p) hcov
      have h2 := Finset.card_erase_of_mem hp
      have hpos : 1 ≤ S.card := Finset.one_le_card.2 ⟨p, hp⟩
      omega
    · have hℓ : ℓ ∈ S := by
        rcases hS ℓ p hlp with h | h
        · exact h
        · exact absurd h hp
      have hcov : IsVC (deleteVertexEdges G p) (S.erase ℓ) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · have huℓ : u ≠ ℓ := by
            intro h; subst h; exact huv.2.2 (hleaf v huv.1)
          exact Or.inl (Finset.mem_erase.2 ⟨huℓ, hu⟩)
        · have hvℓ : v ≠ ℓ := by
            intro h; subst h; exact huv.2.1 (hleaf u huv.1.symm)
          exact Or.inr (Finset.mem_erase.2 ⟨hvℓ, hv⟩)
      have h1 := hmin' (S.erase ℓ) hcov
      have h2 := Finset.card_erase_of_mem hℓ
      have hpos : 1 ≤ S.card := Finset.one_le_card.2 ⟨ℓ, hℓ⟩
      omega
  omega

lemma hasMinVC_deleteVertex_le {n t t' : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n)
    (hvc : HasMinVC G t) (hvc' : HasMinVC (deleteVertexEdges G p) t') :
    t ≤ t' + 1 := by
  obtain ⟨⟨S', hS', hS'c⟩, _⟩ := hvc'
  have hcov : IsVC G (insert p S') := by
    intro u v huv
    by_cases hup : u = p
    · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
    · by_cases hvp : v = p
      · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
      · rcases hS' u v ⟨huv, hup, hvp⟩ with hu | hv
        · exact Or.inl (Finset.mem_insert_of_mem hu)
        · exact Or.inr (Finset.mem_insert_of_mem hv)
  have h1 := hvc.2 (insert p S') hcov
  have h2 := Finset.card_insert_le p S'
  omega

lemma hasMinVC_deletePair_le {n t t' : ℕ} (G : SimpleGraph (Fin n)) (u w : Fin n)
    (hvc : HasMinVC G t) (hvc' : HasMinVC (deleteVertexEdges (deleteVertexEdges G u) w) t') :
    t ≤ t' + 2 := by
  obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (deleteVertexEdges G u)
  have h1 := hasMinVC_deleteVertex_le G u hvc hvc₁
  have h2 := hasMinVC_deleteVertex_le (deleteVertexEdges G u) w hvc₁ hvc'
  omega

lemma edgeFinset_card_deleteEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) [DecidableRel (G.deleteEdges {s(ℓ, p)}).Adj] :
    (G.deleteEdges {s(ℓ, p)}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (G.deleteEdges {s(ℓ, p)}).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

lemma edgeFinset_card_deleteVertex_deg1 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p : Fin n) (hlp : G.Adj ℓ p)
    (hpdeg : ∀ w, G.Adj p w → w = ℓ) [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      dsimp only [deleteVertexEdges]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, huv⟩
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hvp h2
        · exact hup h1
      · rintro ⟨hne, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup
          exact hne (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, hpdeg v huv⟩)
        · intro hvp; subst hvp
          exact hne (by rw [Sym2.eq_iff]; exact Or.inl ⟨hpdeg u huv.symm, rfl⟩)
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

lemma edgeFinset_card_deleteVertex_deg2 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p q : Fin n) (hlp : G.Adj ℓ p) (hpq : G.Adj p q)
    (hqne : q ≠ ℓ) (hpdeg : ∀ w, G.Adj p w → w = ℓ ∨ w = q)
    [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 2 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset =
      (G.edgeFinset.erase s(ℓ, p)).erase s(p, q) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, Finset.mem_erase,
          SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      dsimp only [deleteVertexEdges]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, ?_, huv⟩
        · intro he; rw [Sym2.eq_iff] at he
          rcases he with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hup h1
          · exact hvp h2
        · intro he; rw [Sym2.eq_iff] at he
          rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact hvp h2
          · exact hup h1
      · rintro ⟨hne2, hne1, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup
          rcases hpdeg v huv with rfl | rfl
          · exact hne1 (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩)
          · exact hne2 (by rw [Sym2.eq_iff]; exact Or.inl ⟨rfl, rfl⟩)
        · intro hvp; subst hvp
          rcases hpdeg u huv.symm with rfl | rfl
          · exact hne1 (by rw [Sym2.eq_iff]; exact Or.inl ⟨rfl, rfl⟩)
          · exact hne2 (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩)
  rw [heq]
  have hmem1 : s(ℓ, p) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hne_edges : s(p, q) ≠ s(ℓ, p) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hlp.ne h1.symm
    · exact hqne h2
  have hmem2 : s(p, q) ∈ G.edgeFinset.erase s(ℓ, p) :=
    Finset.mem_erase.2 ⟨hne_edges, by rw [SimpleGraph.mem_edgeFinset]; exact hpq⟩
  have hpos2 : 1 ≤ (G.edgeFinset.erase s(ℓ, p)).card := Finset.one_le_card.2 ⟨s(p, q), hmem2⟩
  rw [Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hmem1]
  rw [Finset.card_erase_of_mem hmem1] at hpos2
  omega

def forestFun0 {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)

lemma isVertexCover_iff_isVC {n : ℕ} (K : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    K.IsVertexCover (S : Set (Fin n)) ↔ IsVC K S := by
  constructor
  · intro h u v huv
    exact h huv
  · intro h u v huv
    exact h u v huv

lemma forestFun0_false {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) :
    forestFun0 K A (fun _ => false) = false := by
  simp [forestFun0]

lemma forestFun0_true {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (hne : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) :
    forestFun0 K A (fun _ => true) = true := by
  simp only [forestFun0, decide_eq_true_eq]
  rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
  · exact Or.inl ⟨a, ha, trivial⟩
  · exact Or.inr ⟨u, v, huv, trivial, trivial⟩

lemma forestFun0_nonconst {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (hne : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) :
    ∃ x y : Fin n → Bool, forestFun0 K A x ≠ forestFun0 K A y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  rw [forestFun0_false, forestFun0_true K A hne]
  decide

lemma forestFun0_inc_A {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha : a ∈ A) :
    ∃ x : Fin n → Bool,
      forestFun0 K A (Function.update x a false) = false ∧
      forestFun0 K A (Function.update x a true) = true := by
  refine ⟨fun _ => false, ?_, ?_⟩
  · have h0 : Function.update (fun _ : Fin n => false) a false = fun _ => false := by
      funext i; by_cases h : i = a <;> simp [h]
    rw [h0, forestFun0_false]
  · simp only [forestFun0, decide_eq_true_eq]
    exact Or.inl ⟨a, ha, by simp⟩

lemma forestFun0_inc_edge {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (hA_iso : ∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v)
    (ℓ p : Fin n) (hlp : K.Adj ℓ p) :
    ∃ x : Fin n → Bool,
      forestFun0 K A (Function.update x ℓ false) = false ∧
      forestFun0 K A (Function.update x ℓ true) = true := by
  classical
  let x0 : Fin n → Bool := fun i => decide (i = p)
  refine ⟨x0, ?_, ?_⟩
  · simp only [forestFun0, decide_eq_false_iff_not, not_or]
    constructor
    · rintro ⟨a, ha, hxa⟩
      by_cases hal : a = ℓ
      · subst hal; simp at hxa
      · simp only [Function.update_of_ne hal, x0, decide_eq_true_eq] at hxa
        exact hA_iso a ha ℓ (hxa ▸ hlp.symm)
    · rintro ⟨u, v, huv, hxu, hxv⟩
      have hu : u = p := by
        by_cases hul : u = ℓ
        · subst hul; simp at hxu
        · simpa [Function.update_of_ne hul, x0] using hxu
      have hv : v = p := by
        by_cases hvl : v = ℓ
        · subst hvl; simp at hxv
        · simpa [Function.update_of_ne hvl, x0] using hxv
      subst hu; subst hv; exact huv.ne rfl
  · simp only [forestFun0, decide_eq_true_eq]
    refine Or.inr ⟨ℓ, p, hlp, by simp, ?_⟩
    simp [Function.update_of_ne hlp.ne.symm, x0]

lemma forestFun0_dep_A {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha : a ∈ A) :
    ∃ x : Fin n → Bool,
      forestFun0 K A (Function.update x a false) ≠ forestFun0 K A (Function.update x a true) := by
  obtain ⟨x, h0, h1⟩ := forestFun0_inc_A K A a ha
  exact ⟨x, by rw [h0, h1]; decide⟩

lemma forestFun0_dep_edge {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (hA_iso : ∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v)
    (ℓ p : Fin n) (hlp : K.Adj ℓ p) :
    ∃ x : Fin n → Bool,
      forestFun0 K A (Function.update x ℓ false) ≠ forestFun0 K A (Function.update x ℓ true) := by
  obtain ⟨x, h0, h1⟩ := forestFun0_inc_edge K A hA_iso ℓ p hlp
  exact ⟨x, by rw [h0, h1]; decide⟩

lemma forestFun0_update_A {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha_iso : ∀ v : Fin n, ¬ K.Adj a v) :
    (fun x : Fin n → Bool => forestFun0 K A (Function.update x a false)) =
      forestFun0 K (A.erase a) := by
  funext x
  simp only [forestFun0]
  apply decide_eq_decide.2
  constructor
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
    · by_cases hba : b = a
      · subst hba; simp at hxb
      · left; exact ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, by rwa [Function.update_of_ne hba] at hxb⟩
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      rw [Function.update_of_ne hua] at hxu
      rw [Function.update_of_ne hva] at hxv
      exact ⟨u, v, huv, hxu, hxv⟩
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
    · obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
      left; exact ⟨b, hbA, by rwa [Function.update_of_ne hba]⟩
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      exact ⟨u, v, huv, by rwa [Function.update_of_ne hua], by rwa [Function.update_of_ne hva]⟩

lemma forestFun0_update_leaf_false {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (ℓ p : Fin n) (hleaf : ∀ w, K.Adj ℓ w → w = p)
    [DecidableRel (K.deleteEdges {s(ℓ, p)}).Adj] :
    (fun x : Fin n → Bool => forestFun0 K ∅ (Function.update x ℓ false)) =
      forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅ := by
  funext x
  simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hxu, hxv⟩
    have hu : u ≠ ℓ := by intro h; subst h; simp at hxu
    have hv : v ≠ ℓ := by intro h; subst h; simp at hxv
    rw [Function.update_of_ne hu] at hxu
    rw [Function.update_of_ne hv] at hxv
    refine ⟨u, v, SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩, hxu, hxv⟩
    intro hmem
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact hu rfl
    · exact hv rfl
  · rintro ⟨u, v, hadj, hxu, hxv⟩
    obtain ⟨huv, hne⟩ := SimpleGraph.deleteEdges_adj.1 hadj
    have hu : u ≠ ℓ := by
      intro h; subst h
      have hp : v = p := hleaf v huv
      subst hp; exact hne rfl
    have hv : v ≠ ℓ := by
      intro h; subst h
      have hp : u = p := hleaf u huv.symm
      subst hp; exact hne Sym2.eq_swap
    exact ⟨u, v, huv, by rwa [Function.update_of_ne hu], by rwa [Function.update_of_ne hv]⟩

lemma forestFun0_update_leaf_true {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (ℓ p : Fin n) (hlp : K.Adj ℓ p) (hleaf : ∀ w, K.Adj ℓ w → w = p)
    [DecidableRel (deleteVertexEdges K p).Adj] :
    (fun x : Fin n → Bool => forestFun0 K ∅ (Function.update x ℓ true)) =
      forestFun0 (deleteVertexEdges K p) {p} := by
  funext x
  simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or,
    Finset.mem_singleton, exists_eq_left]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hxu, hxv⟩
    by_cases hup : u = p
    · subst hup
      left
      rwa [Function.update_of_ne hlp.ne.symm] at hxu
    · by_cases hvp : v = p
      · subst hvp
        left
        rwa [Function.update_of_ne hlp.ne.symm] at hxv
      · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
        have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
        rw [Function.update_of_ne huℓ] at hxu
        rw [Function.update_of_ne hvℓ] at hxv
        exact Or.inr ⟨u, v, ⟨huv, hup, hvp⟩, hxu, hxv⟩
  · rintro (hxp | ⟨u, v, ⟨huv, hup, hvp⟩, hxu, hxv⟩)
    · exact ⟨ℓ, p, hlp, by simp, by rwa [Function.update_of_ne hlp.ne.symm]⟩
    · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
      have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
      exact ⟨u, v, huv, by rwa [Function.update_of_ne huℓ], by rwa [Function.update_of_ne hvℓ]⟩

lemma forest_lower_bound :
    ∀ (s : ℕ) {n t : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n)),
      K.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) →
      (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) →
      HasMinVC K t →
      HasCircuitSize n (forestFun0 K A) s →
      A.card + K.edgeFinset.card + t - 1 ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro n t K _ A hAcyc hA_iso hne hvc hC
    by_cases hcard1 : A.card + K.edgeFinset.card ≤ 1
    · by_cases hAne : A.Nonempty
      · have hApos : 1 ≤ A.card := Finset.one_le_card.2 hAne
        have hE0 : K.edgeFinset.card = 0 := by omega
        have hnoE : ∀ u v : Fin n, ¬ K.Adj u v := by
          intro u v huv
          have hmem : s(u, v) ∈ K.edgeFinset := SimpleGraph.mem_edgeFinset.2 huv
          have := Finset.one_le_card.2 ⟨s(u, v), hmem⟩
          omega
        have ht0 : t = 0 := hasMinVC_empty K hnoE hvc
        omega
      · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
        subst hA0
        rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
        · exact absurd ha (Finset.notMem_empty a)
        · have hE1 : K.edgeFinset.card = 1 := by
            have h1 : 1 ≤ K.edgeFinset.card :=
              Finset.one_le_card.2 ⟨s(u, v), SimpleGraph.mem_edgeFinset.2 huv⟩
            simp at hcard1; omega
          have ht1 : t = 1 := by
            have hge1 : 1 ≤ t := by
              obtain ⟨⟨S, hS, hSc⟩, _⟩ := hvc
              rcases hS u v huv with hu | hv
              · have := Finset.one_le_card.2 ⟨u, hu⟩; omega
              · have := Finset.one_le_card.2 ⟨v, hv⟩; omega
            have hle1 : t ≤ 1 := by
              have hvc_u : IsVC K {u} := by
                intro a b hab
                have hmem1 : s(a, b) ∈ K.edgeFinset := SimpleGraph.mem_edgeFinset.2 hab
                have hmem2 : s(u, v) ∈ K.edgeFinset := SimpleGraph.mem_edgeFinset.2 huv
                have hle_e : K.edgeFinset.card ≤ 1 := by omega
                have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 hle_e s(a, b) hmem1 s(u, v) hmem2
                rw [Sym2.eq_iff] at heq
                rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · left; simp
                · right; simp
              have := hvc.2 {u} hvc_u
              simpa using this
            omega
          suffices hs1 : 1 ≤ s by simp [hE1, ht1]; omega
          by_contra hs0
          have hs_eq : s = 0 := by omega
          subst hs_eq
          obtain ⟨C, _, hsz, hev⟩ := hC
          have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (by simpa [Circuit.size] using hsz)
          have heval : ∀ x : Fin n → Bool, forestFun0 K ∅ x = (List.ofFn x).getD C.output false := by
            intro x; rw [← hev x]; simp [Circuit.eval, Circuit.wires, hnil]
          by_cases ho : C.output < n
          · set w : Fin n := ⟨C.output, ho⟩
            have hvalw : ∀ x : Fin n → Bool, forestFun0 K ∅ x = x w := by
              intro x; rw [heval x, ofFn_getD_lt x false C.output ho]
            let x1 : Fin n → Bool := fun i => decide (i = w)
            have hx1 : forestFun0 K ∅ x1 = true := by rw [hvalw x1]; simp [x1]
            simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or,
              decide_eq_true_eq] at hx1
            obtain ⟨a, b, hab, ha1, hb1⟩ := hx1
            simp [x1] at ha1 hb1
            subst ha1; subst hb1; exact hab.ne rfl
          · have hfalse : forestFun0 K ∅ (fun _ => true) = false := by
              rw [heval _, List.getD_eq_default _ _ (by simp; omega)]
            rw [forestFun0_true K ∅ (Or.inr ⟨u, v, huv⟩)] at hfalse
            exact Bool.noConfusion hfalse
    · by_cases hAne : A.Nonempty
      · obtain ⟨a, ha⟩ := hAne
        have hne' : (A.erase a).Nonempty ∨ ∃ u v : Fin n, K.Adj u v := by
          by_cases hA1 : 2 ≤ A.card
          · left
            have : 0 < (A.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
            exact Finset.card_pos.1 this
          · right
            have hAeq : A.card = 1 := by
              have := Finset.one_le_card.2 ⟨a, ha⟩; omega
            have hEpos : 0 < K.edgeFinset.card := by omega
            obtain ⟨e, he⟩ := Finset.card_pos.1 hEpos
            induction e using Sym2.ind with
            | _ u v => exact ⟨u, v, SimpleGraph.mem_edgeFinset.1 he⟩
        have hdep := forestFun0_dep_A K A a ha
        have hrew := forestFun0_update_A K A a (hA_iso a ha)
        have hnc : ∃ x x', forestFun0 K A (Function.update x a false) ≠
            forestFun0 K A (Function.update x' a false) := by
          simpa only [← congrFun hrew] using forestFun0_nonconst K (A.erase a) hne'
        obtain ⟨hs1, hC'⟩ := elim_one_var a false hC hdep hnc
        rw [hrew] at hC'
        have hih := ih (s - 1) (by omega) K (A.erase a) hAcyc
          (fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)) hne' hvc hC'
        have hcard : (A.erase a).card + 1 = A.card := by
          have := Finset.one_le_card.2 ⟨a, ha⟩
          rw [Finset.card_erase_of_mem ha]; omega
        omega
      · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
        subst hA0
        have hEdge : ∃ u v : Fin n, K.Adj u v := hne.resolve_left (by simp)
        obtain ⟨ℓ, p, hlp, hleaf, hcases⟩ := acyclic_leaf_cases K hAcyc hEdge
        rcases hcases with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | ⟨q, hqne, hpq, hpdeg2⟩
        · classical
          obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (K.deleteEdges {s(ℓ, p)})
          have ht₁ : t₁ = t := hasMinVC_deleteLeafEdge_eq K ℓ ℓ' p hℓ'ne hℓ'p hℓ'leaf hvc hvc₁
          have hne' : (∅ : Finset (Fin n)).Nonempty ∨ ∃ u v, (K.deleteEdges {s(ℓ, p)}).Adj u v := by
            right; refine ⟨ℓ', p, SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, ?_⟩⟩
            simp only [Set.mem_singleton_iff, Sym2.eq_iff]
            rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
            · exact hℓ'ne h1
            · exact hlp.ne h2.symm
          have hdep := forestFun0_dep_edge K ∅ (by simp) ℓ p hlp
          have hrew := forestFun0_update_leaf_false K ℓ p hleaf
          have hnc : ∃ x x', forestFun0 K ∅ (Function.update x ℓ false) ≠
              forestFun0 K ∅ (Function.update x' ℓ false) := by
            obtain ⟨x, x', hne1⟩ := forestFun0_nonconst (K.deleteEdges {s(ℓ, p)}) ∅ hne'
            exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hne1⟩
          obtain ⟨hs1, hC'⟩ := elim_one_var ℓ false hC hdep hnc
          rw [hrew] at hC'
          have hih := ih (s - 1) (by omega) (K.deleteEdges {s(ℓ, p)}) ∅
            (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne' hvc₁ hC'
          have hedge := edgeFinset_card_deleteEdge K ℓ p hlp
          simp only [Finset.card_empty, zero_add] at hih ⊢
          omega
        · classical
          obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges K p)
          have ht' : t' + 1 = t := hasMinVC_deleteVertex K ℓ p hlp hleaf hvc hvc'
          have hne' : ({p} : Finset (Fin n)).Nonempty ∨ ∃ u v, (deleteVertexEdges K p).Adj u v :=
            Or.inl (Finset.singleton_nonempty p)
          have hdep := forestFun0_dep_edge K ∅ (by simp) ℓ p hlp
          have hrew := forestFun0_update_leaf_true K ℓ p hlp hleaf
          have hnc : ∃ x x', forestFun0 K ∅ (Function.update x ℓ true) ≠
              forestFun0 K ∅ (Function.update x' ℓ true) := by
            obtain ⟨x, x', hne1⟩ := forestFun0_nonconst (deleteVertexEdges K p) {p} hne'
            exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hne1⟩
          obtain ⟨hs1, hC'⟩ := elim_one_var ℓ true hC hdep hnc
          rw [hrew] at hC'
          have hih := ih (s - 1) (by omega) (deleteVertexEdges K p) {p}
            (hAcyc.anti (deleteVertexEdges_le K p))
            (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl) hne' hvc' hC'
          have hedge := edgeFinset_card_deleteVertex_deg1 K ℓ p hlp hpdeg1
          simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
          omega
        · classical
          have hne0 : (∅ : Finset (Fin n)).Nonempty ∨ ∃ u v, (K.deleteEdges {s(ℓ, p)}).Adj u v := by
            right; refine ⟨p, q, SimpleGraph.deleteEdges_adj.2 ⟨hpq, ?_⟩⟩
            simp only [Set.mem_singleton_iff, Sym2.eq_iff]
            rintro (⟨h1, _⟩ | ⟨_, h2⟩)
            · exact hlp.ne h1.symm
            · exact hqne h2
          have hne1 : ({p} : Finset (Fin n)).Nonempty ∨ ∃ u v, (deleteVertexEdges K p).Adj u v :=
            Or.inl (Finset.singleton_nonempty p)
          have hdep := forestFun0_dep_edge K ∅ (by simp) ℓ p hlp
          have hrew0 := forestFun0_update_leaf_false K ℓ p hleaf
          have hrew1 := forestFun0_update_leaf_true K ℓ p hlp hleaf
          have hnc0 : ∃ x x', forestFun0 K ∅ (Function.update x ℓ false) ≠
              forestFun0 K ∅ (Function.update x' ℓ false) := by
            obtain ⟨x, x', h⟩ := forestFun0_nonconst (K.deleteEdges {s(ℓ, p)}) ∅ hne0
            exact ⟨x, x', by rw [congrFun hrew0 x, congrFun hrew0 x']; exact h⟩
          have hnc1 : ∃ x x', forestFun0 K ∅ (Function.update x ℓ true) ≠
              forestFun0 K ∅ (Function.update x' ℓ true) := by
            obtain ⟨x, x', h⟩ := forestFun0_nonconst (deleteVertexEdges K p) {p} hne1
            exact ⟨x, x', by rw [congrFun hrew1 x, congrFun hrew1 x']; exact h⟩
          obtain ⟨hs2, hC0 | hC1⟩ := elim_two_var ℓ hC hdep hnc0 hnc1
          · rw [hrew0] at hC0
            obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (K.deleteEdges {s(ℓ, p)})
            have ht₁ := (hasMinVC_deleteEdge K ℓ p hvc hvc₁).2
            have hih := ih (s - 2) (by omega) (K.deleteEdges {s(ℓ, p)}) ∅
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne0 hvc₁ hC0
            have hedge := edgeFinset_card_deleteEdge K ℓ p hlp
            simp only [Finset.card_empty, zero_add] at hih ⊢
            omega
          · rw [hrew1] at hC1
            obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges K p)
            have ht' : t' + 1 = t := hasMinVC_deleteVertex K ℓ p hlp hleaf hvc hvc'
            have hih := ih (s - 2) (by omega) (deleteVertexEdges K p) {p}
              (hAcyc.anti (deleteVertexEdges_le K p))
              (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl) hne1 hvc' hC1
            have hedge := edgeFinset_card_deleteVertex_deg2 K ℓ p q hlp hpq hqne hpdeg2
            simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
            omega

lemma max_path_end_cases {n m : ℕ} (G : SimpleGraph (Fin n)) (hAcyc : G.IsAcyclic)
    (hm_ge : 1 ≤ m)
    (hm_max : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length ≤ m)
    {ℓ z : Fin n} (P : G.Walk ℓ z) (hP : P.IsPath) (hPlen : P.length = m) :
    ∃ p : Fin n, G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧
      ((∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ' p ∧ ∀ w, G.Adj ℓ' w → w = p) ∨
       (∀ w, G.Adj p w → w = ℓ) ∨
       (∃ q : Fin n, q ≠ ℓ ∧ G.Adj p q ∧ ∀ w, G.Adj p w → w = ℓ ∨ w = q)) := by
  classical
  cases P with
  | nil => simp at hPlen; omega
  | @cons _ p _ hlp Q =>
    have hQ : Q.IsPath := hP.of_cons
    have hℓ_not_Q : ℓ ∉ Q.support := by
      have hnd := hP.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1
    have hℓ_leaf : ∀ w, G.Adj ℓ w → w = p := by
      intro w hlw
      by_cases hw : w ∈ (SimpleGraph.Walk.cons hlp Q).support
      · simpa using hAcyc.eq_snd_of_adj_start hP hlw hw
      · exfalso
        have hP' : (SimpleGraph.Walk.cons hlw.symm (SimpleGraph.Walk.cons hlp Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP hw
        have hle := hm_max _ hP'
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    have hnotQ_leaf : ∀ w, G.Adj p w → w ∉ Q.support → ∀ u, G.Adj w u → u = p := by
      intro w hpw hwQ u hwu
      by_contra hup
      by_cases huQ : u ∈ Q.support
      · set Q' := Q.takeUntil u huQ
        have hQ' : Q'.IsPath := hQ.takeUntil huQ
        have hR : (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).IsPath := by
          refine SimpleGraph.Walk.IsPath.cons
            (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hwu.ne])) ?_
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or]
          exact ⟨hpw.ne, Ne.symm hup⟩
        have heq := (hAcyc.subsingleton_path p u).elim ⟨Q', hQ'⟩ ⟨_, hR⟩
        have hw_in_R : w ∈ (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).support := by
          simp
        have hw_in_Q' : w ∈ Q'.support := by
          rw [Subtype.mk.inj heq]; exact hw_in_R
        exact hwQ (SimpleGraph.Walk.support_takeUntil_subset_support Q huQ hw_in_Q')
      · have hP1 : (SimpleGraph.Walk.cons hpw.symm Q).IsPath :=
          SimpleGraph.Walk.IsPath.cons hQ hwQ
        have hu_not : u ∉ (SimpleGraph.Walk.cons hpw.symm Q).support := by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
          exact ⟨hwu.ne.symm, huQ⟩
        have hP2 : (SimpleGraph.Walk.cons hwu.symm (SimpleGraph.Walk.cons hpw.symm Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP1 hu_not
        have hle := hm_max _ hP2
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    refine ⟨p, hlp, hℓ_leaf, ?_⟩
    cases Q with
    | nil =>
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj z ℓ'
      · obtain ⟨ℓ', hne, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.nil : G.Walk z z).support := by
          simp [hadj.ne.symm]
        exact Or.inl ⟨ℓ', hne, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inl ?_)
        intro w hpw
        by_contra hwne
        exact hother ⟨w, hwne, hpw⟩
    | @cons _ q _ hpq Q' =>
      have hq_ne_ℓ : q ≠ ℓ := by
        intro hq; apply hℓ_not_Q; rw [← hq]; simp
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ ℓ' ≠ q ∧ G.Adj p ℓ'
      · obtain ⟨ℓ', hne1, hne2, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.cons hpq Q').support := by
          intro hmem
          exact hne2 (by simpa using hAcyc.eq_snd_of_adj_start hQ hadj hmem)
        exact Or.inl ⟨ℓ', hne1, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inr ⟨q, hq_ne_ℓ, hpq, ?_⟩)
        intro w hpw
        by_contra hnot
        exact hother ⟨w, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h), hpw⟩

lemma acyclic_two_deg2_leaves {n : ℕ} (G : SimpleGraph (Fin n)) (hAcyc : G.IsAcyclic)
    (hEdge : ∃ u v : Fin n, G.Adj u v)
    (hno_sib : ¬ ∃ ℓ ℓ' p : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧
      G.Adj ℓ' p ∧ (∀ w, G.Adj ℓ' w → w = p))
    (hno_iso : ¬ ∃ ℓ p : Fin n, G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧ (∀ w, G.Adj p w → w = ℓ)) :
    ∃ ℓ₁ p₁ q₁ ℓ₂ p₂ q₂ : Fin n, ℓ₁ ≠ ℓ₂ ∧
      G.Adj ℓ₁ p₁ ∧ (∀ w, G.Adj ℓ₁ w → w = p₁) ∧ q₁ ≠ ℓ₁ ∧ G.Adj p₁ q₁ ∧
        (∀ w, G.Adj p₁ w → w = ℓ₁ ∨ w = q₁) ∧
      G.Adj ℓ₂ p₂ ∧ (∀ w, G.Adj ℓ₂ w → w = p₂) ∧ q₂ ≠ ℓ₂ ∧ G.Adj p₂ q₂ ∧
        (∀ w, G.Adj p₂ w → w = ℓ₂ ∨ w = q₂) := by
  classical
  have hlen_lt : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length < n := by
    intro u v P hP
    have h1 : P.support.length ≤ Fintype.card (Fin n) := hP.support_nodup.length_le_card
    rw [P.length_support, Fintype.card_fin] at h1
    omega
  set S : Finset ℕ := (Finset.range n).filter
    (fun k => ∃ u v : Fin n, ∃ P : G.Walk u v, P.IsPath ∧ P.length = k) with hS
  have hS_ne : S.Nonempty := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
    exact ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlen_lt _ hp), u₀, v₀, _, hp, rfl⟩⟩
  set m := S.max' hS_ne with hm
  have hm_mem : m ∈ S := Finset.max'_mem S hS_ne
  have hm_ge : 1 ≤ m := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
    exact Finset.le_max' S 1 (Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlen_lt _ hp), u₀, v₀, _, hp, rfl⟩)
  have hm_max : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length ≤ m := by
    intro u v P hP
    exact Finset.le_max' S P.length (Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlen_lt P hP), u, v, P, hP, rfl⟩)
  obtain ⟨_, ℓ₁, ℓ₂, P, hP, hPlen⟩ := Finset.mem_filter.1 hm_mem
  have hne : ℓ₁ ≠ ℓ₂ := by
    intro heq; subst heq
    cases P with
    | nil => simp at hPlen; omega
    | cons hadj Q =>
      have hnd := hP.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1 Q.end_mem_support
  obtain ⟨p₁, h1p, h1leaf, hc1⟩ := max_path_end_cases G hAcyc hm_ge hm_max P hP hPlen
  obtain ⟨q₁, hq1ne, hp1q1, hp1deg2⟩ : ∃ q₁ : Fin n, q₁ ≠ ℓ₁ ∧ G.Adj p₁ q₁ ∧
      ∀ w, G.Adj p₁ w → w = ℓ₁ ∨ w = q₁ := by
    rcases hc1 with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | hres
    · exact absurd ⟨ℓ₁, ℓ', p₁, hℓ'ne, h1p, h1leaf, hℓ'p, hℓ'leaf⟩ hno_sib
    · exact absurd ⟨ℓ₁, p₁, h1p, h1leaf, hpdeg1⟩ hno_iso
    · exact hres
  have hPrev : P.reverse.IsPath := hP.reverse
  have hPrevLen : P.reverse.length = m := by rw [SimpleGraph.Walk.length_reverse, hPlen]
  obtain ⟨p₂, h2p, h2leaf, hc2⟩ := max_path_end_cases G hAcyc hm_ge hm_max P.reverse hPrev hPrevLen
  obtain ⟨q₂, hq2ne, hp2q2, hp2deg2⟩ : ∃ q₂ : Fin n, q₂ ≠ ℓ₂ ∧ G.Adj p₂ q₂ ∧
      ∀ w, G.Adj p₂ w → w = ℓ₂ ∨ w = q₂ := by
    rcases hc2 with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | hres
    · exact absurd ⟨ℓ₂, ℓ', p₂, hℓ'ne, h2p, h2leaf, hℓ'p, hℓ'leaf⟩ hno_sib
    · exact absurd ⟨ℓ₂, p₂, h2p, h2leaf, hpdeg1⟩ hno_iso
    · exact hres
  exact ⟨ℓ₁, p₁, q₁, ℓ₂, p₂, q₂, hne, h1p, h1leaf, hq1ne, hp1q1, hp1deg2,
    h2p, h2leaf, hq2ne, hp2q2, hp2deg2⟩

def Reduced (n : ℕ) (C : Circuit) : Prop :=
  (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool,
    (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧
  (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool,
    (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧
  (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧
  (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧
    (GateOp.casesOn (motive := fun _ => List ℕ) p.1.op
      p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)

lemma effInputs_eq_inputs_of_nok (g : Gate) (h : NOkGate g) :
    (GateOp.casesOn (motive := fun _ => List ℕ) g.op
      g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs) = g.inputs := by
  rcases g with ⟨op, ins⟩
  rcases h.1.1 with rfl | rfl | rfl
  · rfl
  · rfl
  · exact List.take_of_length_le (h.2 rfl)

lemma effInputs_normGate (g : Gate) :
    (GateOp.casesOn (motive := fun _ => List ℕ) (normGate g).op
      (normGate g).inputs (normGate g).inputs ((normGate g).inputs.take 1)
      (fun _ => (normGate g).inputs) (normGate g).inputs) =
    (GateOp.casesOn (motive := fun _ => List ℕ) g.op
      g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [normGate]

lemma reduced_norm (n : ℕ) (C : Circuit) (hred : Reduced n C) :
    Reduced n ⟨C.gates.map normGate, C.output⟩ := by
  have hwires : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨C.gates.map normGate, C.output⟩ (List.ofFn x)) = C.wires (List.ofFn x) :=
    fun x => wiresFrom_norm C.gates (List.ofFn x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [List.length_map] at hj
    simpa only [hwires] using hred.1 j hj
  · intro i j hij hj
    rw [List.length_map] at hj
    simpa only [hwires] using hred.2.1 i j hij hj
  · intro hne
    have hne' : C.gates ≠ [] := fun h => hne (by simp [h])
    simpa [List.length_map] using hred.2.2.1 hne'
  · intro j hj
    rw [List.length_map] at hj
    obtain ⟨p, hp, hlt, hcont⟩ := hred.2.2.2 j hj
    rw [List.mem_iff_getElem] at hp
    obtain ⟨k, hk, hpk⟩ := hp
    have hk' : k < C.gates.length := by simpa [List.length_zipIdx] using hk
    have hpk' : p = (C.gates[k]'hk', k) := by
      rw [← hpk]; simp [List.getElem_zipIdx]
    refine ⟨(normGate (C.gates[k]'hk'), k), ?_, ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      refine ⟨k, by simp [List.length_zipIdx, hk'], ?_⟩
      simp [List.getElem_zipIdx]
    · rw [hpk'] at hlt; exact hlt
    · rw [hpk'] at hcont
      simpa only [effInputs_normGate] using hcont

lemma reduced_no_dead {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j : ℕ) (hj : j < C.gates.length) :
    C.output = m + j ∨ ∃ j' : ℕ, ∃ hj' : j' < C.gates.length, j < j' ∧ (m + j) ∈ C.gates[j'].inputs := by
  by_cases hlast : j + 1 < C.gates.length
  · right
    obtain ⟨p, hp, hlt, hcont⟩ := hred.2.2.2 j hlast
    rw [List.mem_iff_getElem] at hp
    obtain ⟨k, hk, hpk⟩ := hp
    have hk' : k < C.gates.length := by simpa [List.length_zipIdx] using hk
    have hpk' : p = (C.gates[k]'hk', k) := by
      rw [← hpk]; simp [List.getElem_zipIdx]
    rw [hpk'] at hlt hcont
    rw [effInputs_eq_inputs_of_nok _ (hnok _ (List.getElem_mem hk'))] at hcont
    exact ⟨k, hk', by omega, List.contains_iff_mem.1 hcont⟩
  · left
    have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
    have ho := hred.2.2.1 hne
    omega

lemma reduced_gate_wf {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates[j].op = GateOp.not → ∃ a, a < m + j ∧ C.gates[j].inputs = [a]) ∧
    ((C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) →
      ∃ a b, a < m + j ∧ b < m + j ∧ a ≠ b ∧ C.gates[j].inputs = [a, b]) := by
  have hnc_j : ∀ c : Bool, ¬ (∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false = c) := by
    intro c hc
    obtain ⟨x, y, hne⟩ := hred.1 j hj
    exact hne ((hc x).trans (hc y).symm)
  have hna_j : ∀ a < m + j, ¬ (∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD (m + j) false = (C.wires (List.ofFn x)).getD a false) := by
    intro a ha heq
    obtain ⟨x, hne⟩ := hred.2.1 a j ha hj
    exact hne (heq x).symm
  have hg := hnok C.gates[j] (List.getElem_mem hj)
  constructor
  · intro hop
    have hlen1 := hg.2 hop
    rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exfalso; apply hnc_j true
      intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
    · by_cases ha : a < m + j
      · exact ⟨a, ha, rfl⟩
      · exfalso; apply hnc_j true
        intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, GateOp.eval]
    · rw [hins] at hlen1; simp at hlen1
  · intro hop
    have hlen2 := hg.1.2
    rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · exfalso
      rcases hop with hop | hop
      · apply hnc_j true; intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
      · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
    · exfalso
      by_cases ha : a < m + j
      · apply hna_j a ha; intro x; rw [wire_eval_gate C j hj x, hins]
        rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
      · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hins]
        rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
    · by_cases ha : a < m + j
      · by_cases hb : b < m + j
        · by_cases hab : a = b
          · exfalso; subst hab; apply hna_j a ha
            intro x; rw [wire_eval_gate C j hj x, hins]
            rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
          · exact ⟨a, b, ha, hb, hab, rfl⟩
        · exfalso
          rcases hop with hop | hop
          · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
          · apply hna_j a ha; intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
      · exfalso
        by_cases hb : b < m + j
        · rcases hop with hop | hop
          · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
          · apply hna_j b hb; intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
        · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hins]
          rcases hop with hop | hop <;> simp [hop, ha, hb, GateOp.eval]
    · rw [hins] at hlen2; simp at hlen2

lemma reduced_inputs_lt {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j : ℕ) (hj : j < C.gates.length) :
    ∀ i ∈ C.gates[j].inputs, i < m + j := by
  intro i hi
  rcases (hnok _ (List.getElem_mem hj)).1.1 with hop | hop | hop
  · obtain ⟨a, b, ha, hb, _, hins⟩ := (reduced_gate_wf C hnok hred j hj).2 (Or.inl hop)
    rw [hins] at hi; simp at hi; rcases hi with rfl | rfl <;> assumption
  · obtain ⟨a, b, ha, hb, _, hins⟩ := (reduced_gate_wf C hnok hred j hj).2 (Or.inr hop)
    rw [hins] at hi; simp at hi; rcases hi with rfl | rfl <;> assumption
  · obtain ⟨a, ha, hins⟩ := (reduced_gate_wf C hnok hred j hj).1 hop
    rw [hins] at hi; simp at hi; subst hi; exact ha

lemma min_reduced {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (hnc : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y) :
    Reduced m C := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    by_contra hall
    push Not at hall
    exact min_no_const C hnok hmin hnc j hj ((C.wires (List.ofFn (fun _ : Fin m => false))).getD (m + j) false)
      (fun x => hall x (fun _ => false))
  · intro i j hij hj
    by_contra hall
    push Not at hall
    exact min_no_alias C hnok hmin j i hj hij (fun x => (hall x).symm)
  · intro hne
    have hpos : 0 < C.gates.length := List.length_pos_of_ne_nil hne
    have hlt := min_output_lt C hnc
    rcases min_no_dead C hnok hmin (C.gates.length - 1) (by omega) with ho | ⟨j', hj', hgt, _⟩
    · omega
    · omega
  · intro j hj
    have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
    have ho : C.output + 1 = m + C.gates.length := by
      have hlt := min_output_lt C hnc
      rcases min_no_dead C hnok hmin (C.gates.length - 1) (by omega) with ho | ⟨j', hj', hgt, _⟩
      · omega
      · omega
    rcases min_no_dead C hnok hmin j (by omega) with heq | ⟨j', hj', hlt, hmem⟩
    · omega
    · refine ⟨(C.gates[j']'hj', j'), ?_, by omega, ?_⟩
      · rw [List.mem_iff_getElem]
        refine ⟨j', by simp [List.length_zipIdx, hj'], ?_⟩
        simp [List.getElem_zipIdx]
      · rw [effInputs_eq_inputs_of_nok _ (hnok _ (List.getElem_mem hj'))]
        exact List.contains_iff_mem.2 hmem

lemma elimPass_nok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hacc : ∀ g ∈ acc.2, NOkGate g) :
    ∀ g ∈ (elimPass m gs acc).2, NOkGate g := by
  induction gs generalizing acc with
  | nil => exact hacc
  | cons g rest ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    simp only [elimStep, List.mem_append, Option.mem_toList] at hg'
    rcases hg' with h1 | h2
    · exact hacc g' h1
    · exact simplifyGate_nok _ _ _ g' h2

lemma no_not_eval_false {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hnoNot : ∀ g ∈ C.gates, g.op ≠ GateOp.not) :
    ∀ i < m + C.gates.length, (C.wires (List.ofFn (fun _ : Fin m => false))).getD i false = false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hlt : i < m
    · show (wiresFrom C.gates (List.ofFn (fun _ : Fin m => false))).getD i false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp; exact hlt), ofFn_getD_lt _ _ _ hlt]
    · set j := i - m
      have hij : i = m + j := by omega
      have hj : j < C.gates.length := by omega
      rw [hij, wire_eval_gate C j hj]
      have hop := (hnok _ (List.getElem_mem hj)).1.1
      have hne := hnoNot _ (List.getElem_mem hj)
      have hbin : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hne
      obtain ⟨a, b, ha, hb, _, hins⟩ := (reduced_gate_wf C hnok hred j hj).2 hbin
      have hva : (C.wires (List.ofFn (fun _ : Fin m => false))).getD a false = false :=
        ih a (by omega) (by omega)
      have hvb : (C.wires (List.ofFn (fun _ : Fin m => false))).getD b false = false :=
        ih b (by omega) (by omega)
      rw [hins]
      rcases hbin with h | h <;>
        simp only [h, ha, hb, ↓reduceIte, hva, hvb, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
          Bool.false_and, Bool.or_false]

lemma deleteConstGate_two {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (j k : ℕ) (hj : j < C.gates.length) (hk : k < C.gates.length) (hjk : j < k)
    (hmem : (m + j) ∈ C.gates[k].inputs) (c : Bool)
    (hconst : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false = c)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x') :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 2) := by
  set gs₁ := C.gates.take j with hgs₁
  set gs₂ := C.gates.drop (j + 1) with hgs₂
  have hsplit : C.gates = gs₁ ++ [C.gates[j]] ++ gs₂ := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: gs₂ := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [hgs₁, List.append_assoc, List.singleton_append] using h1.symm
  set init : List (Bool ⊕ ℕ) :=
    List.ofFn (fun i : Fin (m + j) => Sum.inr (i : ℕ)) ++ [Sum.inl c] with hinit
  set acc := elimPass m gs₂ (init, gs₁) with hacc
  have hinv : ∀ x : Fin m → Bool,
      ElimInv m (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := by
    intro x
    rw [hsplit, wiresFrom_append, hacc]
    apply elimInv_pass m (List.ofFn x) gs₂ _ (init, gs₁)
      (fun g hg => (hnok g (List.mem_of_mem_drop hg)).1)
    have hlen1 : (wiresFrom gs₁ (List.ofFn x)).length = m + j := by
      rw [wiresFrom_length, List.length_ofFn, hgs₁, List.length_take, Nat.min_eq_left (by omega)]
    have hlen2 : (wiresFrom (gs₁ ++ [C.gates[j]]) (List.ofFn x)).length = m + j + 1 := by
      rw [wiresFrom_append, wiresFrom_length, hlen1]; simp
    refine ⟨by simp, by simp [hinit, hlen2], ?_⟩
    intro i
    by_cases h1 : i < m + j
    · have hget : init.getD i (Sum.inl false) = Sum.inr i := by
        rw [hinit, getD_snoc_lt _ _ _ _ (by simp; exact h1), ofFn_getD_lt _ _ _ h1]
      rw [hget]
      refine ⟨by simp [statValid, hgs₁, List.length_take]; omega, ?_⟩
      simp only [statVal]
      rw [wiresFrom_append]
      exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
    · by_cases h2 : i = m + j
      · have hget : init.getD i (Sum.inl false) = Sum.inl c := by
          rw [hinit, getD_snoc_eq _ _ _ _ (by simp; exact h2)]
        rw [hget]
        refine ⟨trivial, ?_⟩
        simp only [statVal]
        rw [h2]
        have hEq : (wiresFrom (gs₁ ++ [C.gates[j]]) (List.ofFn x)).getD (m + j) false =
            (C.wires (List.ofFn x)).getD (m + j) false := by
          show _ = (wiresFrom C.gates (List.ofFn x)).getD (m + j) false
          conv_rhs => rw [hsplit, wiresFrom_append]
          exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
        rw [hEq, hconst x]
      · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
            List.getD_eq_default _ _ (by omega)]
        exact ⟨trivial, rfl⟩
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        circuitFun m C x := fun x => ((hinv x).2.2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr out' =>
    have ht_lt : k - (j + 1) < gs₂.length := by rw [hgs₂, List.length_drop]; omega
    have hgk_eq : gs₂[k - (j + 1)]'ht_lt = C.gates[k]'hk := by
      simp only [hgs₂, List.getElem_drop]
      congr 1; omega
    have hdrop_t : (k - (j + 1)) ∈ elimDropped m gs₂ (init, gs₁) := by
      apply mem_elimDropped_of_const m gs₂ (init, gs₁) (k - (j + 1)) ht_lt
        (by rw [hgk_eq]; exact hnok _ (List.getElem_mem hk)) (m + j) (by rw [hgk_eq]; exact hmem)
      refine ⟨c, ?_⟩
      rw [elimState_getD_mono m gs₂ (init, gs₁) 0 (k - (j + 1)) (m + j) _ (Nat.zero_le _) (by omega)
        (by simp [hinit]), elimState_zero, hinit, getD_snoc_eq _ _ _ _ (by simp)]
    have hcard_ge : 1 ≤ (elimDropped m gs₂ (init, gs₁)).card :=
      Finset.one_le_card.2 ⟨k - (j + 1), hdrop_t⟩
    have hcard_eq := elimPass_card_dropped m gs₂ (init, gs₁)
    rw [← hacc] at hcard_eq
    dsimp only at hcard_eq
    have hl1 : gs₁.length = j := by rw [hgs₁, List.length_take, Nat.min_eq_left (by omega)]
    have hl2 : gs₂.length = C.gates.length - (j + 1) := by rw [hgs₂, List.length_drop]
    refine ⟨⟨acc.2, out'⟩, elimPass_ok m gs₂ _ (fun g hg => (hnok g (List.mem_of_mem_take hg)).1),
      by show acc.2.length ≤ C.gates.length - 2; omega, ?_⟩
    intro x; have := hval x; rw [hst] at this; exact this

lemma single_not_antimono {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m)
    (Pos : ℕ → Prop)
    (hPos_in : ∀ i < m, Pos i ↔ i = (v : ℕ))
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length)
    (hj₀_op : C.gates[j₀].op = GateOp.not)
    (hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀)
    (hPos_j₀ : ¬ Pos (m + j₀))
    (hj₀_in : ∀ a, C.gates[j₀].inputs = [a] → Pos a)
    (hPos_gate : ∀ j : ℕ, (hj : j < C.gates.length) → j ≠ j₀ →
      (Pos (m + j) → ∀ i ∈ C.gates[j].inputs, Pos i ∨ ∀ x : Fin m → Bool,
        (C.wires (List.ofFn (Function.update x v false))).getD i false =
        (C.wires (List.ofFn (Function.update x v true))).getD i false) ∧
      (¬ Pos (m + j) → ∀ i ∈ C.gates[j].inputs, ¬ Pos i))
    (hPos_out : ¬ Pos C.output) :
    ∀ x : Fin m → Bool,
      circuitFun m C (Function.update x v true) = true →
      circuitFun m C (Function.update x v false) = true := by
  intro x
  have hwire : ∀ i < m + C.gates.length,
      (Pos i → (C.wires (List.ofFn (Function.update x v false))).getD i false = true →
        (C.wires (List.ofFn (Function.update x v true))).getD i false = true) ∧
      (¬ Pos i → (C.wires (List.ofFn (Function.update x v true))).getD i false = true →
        (C.wires (List.ofFn (Function.update x v false))).getD i false = true) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hlt : i < m
      · have h0 : (C.wires (List.ofFn (Function.update x v false))).getD i false =
            (Function.update x v false) ⟨i, hlt⟩ := by
          show (wiresFrom C.gates _).getD i false = _
          rw [wiresFrom_getD_lt _ _ _ (by simp; exact hlt), ofFn_getD_lt _ _ _ hlt]
        have h1 : (C.wires (List.ofFn (Function.update x v true))).getD i false =
            (Function.update x v true) ⟨i, hlt⟩ := by
          show (wiresFrom C.gates _).getD i false = _
          rw [wiresFrom_getD_lt _ _ _ (by simp; exact hlt), ofFn_getD_lt _ _ _ hlt]
        constructor
        · intro hpi hval
          have heq : i = (v : ℕ) := (hPos_in i hlt).1 hpi
          have hfin : (⟨i, hlt⟩ : Fin m) = v := Fin.ext heq
          rw [h1, hfin, Function.update_self]
        · intro hnpi hval
          have hne : i ≠ (v : ℕ) := fun h => hnpi ((hPos_in i hlt).2 h)
          have hfin : (⟨i, hlt⟩ : Fin m) ≠ v := fun h => hne (congrArg Fin.val h)
          rw [h0, Function.update_of_ne hfin]
          rwa [h1, Function.update_of_ne hfin] at hval
      · set j := i - m
        have hij : i = m + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hij]
        by_cases hjeq : j = j₀
        · subst hjeq
          constructor
          · intro hp; exact absurd hp hPos_j₀
          · intro _ hval
            obtain ⟨a, ha, hins⟩ := (reduced_gate_wf C hnok hred j hj).1 hj₀_op
            have hpa : Pos a := hj₀_in a hins
            have hiha := (ih a (by omega) (by omega)).1 hpa
            rw [wire_eval_gate C j hj, hj₀_op, hins] at hval ⊢
            simp only [ha, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
              List.headD_cons, Bool.not_eq_true'] at hval ⊢
            cases h0a : (C.wires (List.ofFn (Function.update x v false))).getD a false
            · rfl
            · exact absurd (hiha h0a) (by rw [hval]; decide)
        · have hbin : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
            rcases (hnok _ (List.getElem_mem hj)).1.1 with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd (hnot_uniq j hj h) hjeq
          obtain ⟨a, b, ha, hb, _, hins⟩ := (reduced_gate_wf C hnok hred j hj).2 hbin
          constructor
          · intro hpj hval
            have hpa_or := (hPos_gate j hj hjeq).1 hpj a (by rw [hins]; simp)
            have hpb_or := (hPos_gate j hj hjeq).1 hpj b (by rw [hins]; simp)
            have hma : (C.wires (List.ofFn (Function.update x v false))).getD a false = true →
                (C.wires (List.ofFn (Function.update x v true))).getD a false = true := by
              rcases hpa_or with hpa | heqa
              · exact (ih a (by omega) (by omega)).1 hpa
              · intro h; rw [← heqa x]; exact h
            have hmb : (C.wires (List.ofFn (Function.update x v false))).getD b false = true →
                (C.wires (List.ofFn (Function.update x v true))).getD b false = true := by
              rcases hpb_or with hpb | heqb
              · exact (ih b (by omega) (by omega)).1 hpb
              · intro h; rw [← heqb x]; exact h
            rw [wire_eval_gate C j hj, hins] at hval ⊢
            rcases hbin with hop | hop <;>
              simp only [hop, ha, hb, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
                Bool.and_true, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true] at hval ⊢
            · exact ⟨hma hval.1, hmb hval.2⟩
            · rcases hval with h1 | h2
              · exact Or.inl (hma h1)
              · exact Or.inr (hmb h2)
          · intro hnpj hval
            have hnpa := (hPos_gate j hj hjeq).2 hnpj a (by rw [hins]; simp)
            have hnpb := (hPos_gate j hj hjeq).2 hnpj b (by rw [hins]; simp)
            have hma := (ih a (by omega) (by omega)).2 hnpa
            have hmb := (ih b (by omega) (by omega)).2 hnpb
            rw [wire_eval_gate C j hj, hins] at hval ⊢
            rcases hbin with hop | hop <;>
              simp only [hop, ha, hb, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
                Bool.and_true, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true] at hval ⊢
            · exact ⟨hma hval.1, hmb hval.2⟩
            · rcases hval with h1 | h2
              · exact Or.inl (hma h1)
              · exact Or.inr (hmb h2)
  have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hout_lt : C.output < m + C.gates.length := by have := hred.2.2.1 hne; omega
  exact (hwire C.output hout_lt).2 hPos_out

lemma wire_indep_of_not_read {m : ℕ} (C : Circuit) (v : Fin m)
    (hno : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∉ C.gates[j].inputs) :
    ∀ k ≤ C.gates.length, ∀ i < m + k, i ≠ (v : ℕ) → ∀ x : Fin m → Bool,
      (C.wires (List.ofFn (Function.update x v false))).getD i false =
      (C.wires (List.ofFn (Function.update x v true))).getD i false := by
  intro k hk
  induction k with
  | zero =>
    intro i hi hne x
    show (wiresFrom C.gates _).getD i false = (wiresFrom C.gates _).getD i false
    rw [wiresFrom_getD_lt _ _ _ (by simp; omega), wiresFrom_getD_lt _ _ _ (by simp; omega),
      ofFn_getD_lt _ _ _ (by omega), ofFn_getD_lt _ _ _ (by omega)]
    have hfin : (⟨i, by omega⟩ : Fin m) ≠ v := fun h => hne (congrArg Fin.val h)
    rw [Function.update_of_ne hfin, Function.update_of_ne hfin]
  | succ k ih =>
    intro i hi hne x
    by_cases hlt : i < m + k
    · exact ih (by omega) i hlt hne x
    · have hieq : i = m + k := by omega
      subst hieq
      have hkt : k < C.gates.length := by omega
      rw [wire_eval_gate C k hkt, wire_eval_gate C k hkt]
      congr 1
      apply List.map_congr_left
      intro u hu
      by_cases hult : u < m + k
      · simp only [hult, ↓reduceIte]
        have hune : u ≠ (v : ℕ) := fun heq => hno k hkt (heq ▸ hu)
        exact ih (by omega) u hult hune x
      · simp only [hult, ↓reduceIte]

lemma single_not_antimono_direct {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length)
    (hnot_eq : C.gates[j₀] = ⟨GateOp.not, [(v : ℕ)]⟩)
    (hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀)
    (hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₀) :
    ∀ x : Fin m → Bool,
      circuitFun m C (Function.update x v true) = true →
      circuitFun m C (Function.update x v false) = true := by
  have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hout := hred.2.2.1 hne
  apply single_not_antimono C hnok hred v (fun i => i = (v : ℕ)) (fun _ _ => Iff.rfl)
    j₀ hj₀ (by rw [hnot_eq]) hnot_uniq (by omega)
    (by intro a ha; rw [hnot_eq] at ha; simp at ha; exact ha.symm)
    (by
      intro j hj hjne
      refine ⟨fun hp => by omega, fun _ i hi heq => hjne (hv_uniq j hj (heq ▸ hi))⟩)
    (by omega)

lemma single_not_antimono_one {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m)
    (j₁ j₀ : ℕ) (hj₁ : j₁ < C.gates.length) (hj₀ : j₀ < C.gates.length) (h10 : j₁ < j₀)
    (hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₁)
    (hnot_eq : C.gates[j₀] = ⟨GateOp.not, [m + j₁]⟩)
    (hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀)
    (hj₁_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (m + j₁) ∈ C.gates[j].inputs → j = j₀) :
    ∀ x : Fin m → Bool,
      circuitFun m C (Function.update x v true) = true →
      circuitFun m C (Function.update x v false) = true := by
  have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hout := hred.2.2.1 hne
  have hindep_lt : ∀ i < m + j₁, i ≠ (v : ℕ) → ∀ x : Fin m → Bool,
      (C.wires (List.ofFn (Function.update x v false))).getD i false =
      (C.wires (List.ofFn (Function.update x v true))).getD i false := by
    let Cpre : Circuit := ⟨C.gates.take j₁, 0⟩
    have hpre_no : ∀ j : ℕ, (hj : j < Cpre.gates.length) → (v : ℕ) ∉ Cpre.gates[j].inputs := by
      intro j hj hmem
      have hjl : j < j₁ := by simp [Cpre, List.length_take] at hj; omega
      have hj' : j < C.gates.length := by omega
      simp only [Cpre, List.getElem_take] at hmem
      exact absurd (hv_uniq j hj' hmem) (by omega)
    have hlen_pre : Cpre.gates.length = j₁ := by
      simp [Cpre, List.length_take, Nat.min_eq_left (le_of_lt hj₁)]
    intro i hi hne_v x
    have heq_f : (C.wires (List.ofFn (Function.update x v false))).getD i false =
        (Cpre.wires (List.ofFn (Function.update x v false))).getD i false := by
      show (wiresFrom C.gates _).getD i false = (wiresFrom (C.gates.take j₁) _).getD i false
      conv_lhs => rw [← List.take_append_drop j₁ C.gates, wiresFrom_append]
      exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take]; omega)
    have heq_t : (C.wires (List.ofFn (Function.update x v true))).getD i false =
        (Cpre.wires (List.ofFn (Function.update x v true))).getD i false := by
      show (wiresFrom C.gates _).getD i false = (wiresFrom (C.gates.take j₁) _).getD i false
      conv_lhs => rw [← List.take_append_drop j₁ C.gates, wiresFrom_append]
      exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take]; omega)
    rw [heq_f, heq_t]
    exact wire_indep_of_not_read Cpre v hpre_no j₁ (by omega) i hi hne_v x
  apply single_not_antimono C hnok hred v (fun i => i = (v : ℕ) ∨ i = m + j₁)
    (fun i hi => ⟨fun h => h.resolve_right (by omega), fun h => Or.inl h⟩)
    j₀ hj₀ (by rw [hnot_eq]) hnot_uniq (by omega)
    (by intro a ha; rw [hnot_eq] at ha; simp at ha; exact Or.inr ha.symm)
    (by
      intro j hj hjne
      constructor
      · intro hp i hi
        have hjeq : j = j₁ := by rcases hp with h | h <;> omega
        subst hjeq
        by_cases hiv : i = (v : ℕ)
        · exact Or.inl (Or.inl hiv)
        · right
          have hilt := reduced_inputs_lt C hnok hred j hj i hi
          exact hindep_lt i hilt hiv
      · intro hnp i hi hpi
        rcases hpi with heq | heq
        · have := hv_uniq j hj (heq ▸ hi)
          exact hnp (Or.inr (by omega))
        · exact hjne (hj₁_uniq j hj (heq ▸ hi)))
    (by intro h; rcases h with h | h <;> omega)

lemma simplifyGate_some_op (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (g' : Gate) (hg : (simplifyGate op m ins).1 = some g') :
    g'.op = op := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; rfl
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; rfl
  · simp at hg
  · simp at hg

lemma simplifyGate_some_mem_inputs (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hnot : op = GateOp.not → ins.length ≤ 1)
    (g' : Gate) (hg : (simplifyGate op m ins).1 = some g')
    (w : ℕ) (hw : Sum.inr w ∈ ins) :
    w ∈ g'.inputs := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp at hw ⊢; exact hw
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp at hw ⊢; exact hw
  · have hlen := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hw
    · cases a <;> simp [simpNot] at hg
      subst hg; simp at hw ⊢; exact hw
    · simp at hlen
  · simp at hg
  · simp at hg

lemma simplifyGate_none_of_inr_mem (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1)
    (hnone : (simplifyGate op m ins).1 = none)
    (w w' : ℕ) (hw : Sum.inr w ∈ ins) (hout : (simplifyGate op m ins).2 = Sum.inr w') :
    w' = w := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at hw
    · cases a <;> simp [simplifyGate, simpAnd] at hw hout ⊢
      exact hout.symm.trans hw.symm
    · cases a with
      | inl ca =>
        cases b with
        | inl cb => simp at hw
        | inr vb =>
          cases ca <;> simp [simplifyGate, simpAnd] at hw hout
          exact hout.symm.trans hw.symm
      | inr va =>
        cases b with
        | inl cb =>
          cases cb <;> simp [simplifyGate, simpAnd] at hw hout
          exact hout.symm.trans hw.symm
        | inr vb => simp [simplifyGate, simpAnd] at hnone
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at hw
    · cases a <;> simp [simplifyGate, simpOr] at hw hout ⊢
      exact hout.symm.trans hw.symm
    · cases a with
      | inl ca =>
        cases b with
        | inl cb => simp at hw
        | inr vb =>
          cases ca <;> simp [simplifyGate, simpOr] at hw hout
          exact hout.symm.trans hw.symm
      | inr va =>
        cases b with
        | inl cb =>
          cases cb <;> simp [simplifyGate, simpOr] at hw hout
          exact hout.symm.trans hw.symm
        | inr vb => simp [simplifyGate, simpOr] at hnone
    · simp at hlen
  · have hlen1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hw
    · cases a <;> simp [simplifyGate, simpNot] at hw hnone
    · simp at hlen1

lemma elimState_snd_append (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (t₁ t₂ : ℕ) (hle : t₁ ≤ t₂) (ht₂ : t₂ ≤ gs.length) :
    ∃ suf : List Gate, (elimState m gs acc t₂).2 = (elimState m gs acc t₁).2 ++ suf := by
  induction t₂ with
  | zero =>
    have : t₁ = 0 := by omega
    subst this; exact ⟨[], by simp⟩
  | succ t₂ ih =>
    by_cases heq : t₁ = t₂ + 1
    · subst heq; exact ⟨[], by simp⟩
    · obtain ⟨suf, hsuf⟩ := ih (by omega) (by omega)
      rw [elimState_succ m gs acc t₂ (by omega), elimStep]
      dsimp only
      rw [hsuf, List.append_assoc]
      exact ⟨_, rfl⟩

lemma elim_emit_at (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) (hnd : j ∉ elimDropped m gs acc) :
    let k := (elimState m gs acc j).2.length
    ∃ g' : Gate,
      (simplifyGate gs[j].op (m + k) (gs[j].inputs.map fun i =>
        (elimState m gs acc j).1.getD i (Sum.inl false))).1 = some g' ∧
      g'.op = gs[j].op ∧
      k < (elimPass m gs acc).2.length ∧
      (elimPass m gs acc).2[k]'(by
        have h1 : (elimState m gs acc (j + 1)).2.length = k + 1 := by
          rw [elimState_succ m gs acc j hj, elimStep]
          cases hopt : (simplifyGate gs[j].op (m + k) (gs[j].inputs.map fun i =>
              (elimState m gs acc j).1.getD i (Sum.inl false))).1 with
          | none =>
            exfalso; apply hnd
            rw [elimDropped, Finset.mem_filter, Finset.mem_range]
            dsimp only [k] at hopt
            exact ⟨hj, by simp only [hj, ↓reduceDIte, hopt]; rfl⟩
          | some g0 => simp [k]
        have h2 := elimState_snd_mono m gs acc (j + 1) gs.length (by omega)
        rw [elimState_end] at h2; omega) = g' ∧
      (elimState m gs acc (j + 1)).1.getD (acc.1.length + j) (Sum.inl false) = Sum.inr (m + k) := by
  intro k
  have hopt_ne : (simplifyGate gs[j].op (m + k) (gs[j].inputs.map fun i =>
      (elimState m gs acc j).1.getD i (Sum.inl false))).1 ≠ none := by
    intro hnone
    apply hnd
    rw [elimDropped, Finset.mem_filter, Finset.mem_range]
    dsimp only [k] at hnone
    exact ⟨hj, by simp only [hj, ↓reduceDIte, hnone]; rfl⟩
  obtain ⟨g', hopt⟩ := Option.ne_none_iff_exists'.1 hopt_ne
  have hstep : (elimState m gs acc (j + 1)).2 = (elimState m gs acc j).2 ++ [g'] := by
    dsimp only [k] at hopt
    rw [elimState_succ m gs acc j hj, elimStep, hopt]
    simp only [Option.toList_some]
  obtain ⟨suf, hsuf⟩ := elimState_snd_append m gs acc (j + 1) gs.length (by omega) le_rfl
  rw [elimState_end, hstep] at hsuf
  have hklt : k < (elimPass m gs acc).2.length := by rw [hsuf]; simp [k]
  refine ⟨g', hopt, simplifyGate_some_op _ _ _ g' hopt, hklt, ?_, ?_⟩
  · have hklt' : k < ((elimState m gs acc j).2 ++ ([g'] ++ suf)).length := by
      rw [← List.append_assoc, ← hsuf]; exact hklt
    have hcongr : (elimPass m gs acc).2[k]'hklt =
        ((elimState m gs acc j).2 ++ ([g'] ++ suf))[k]'hklt' := by
      simp only [hsuf, List.append_assoc]
    rw [hcongr, List.getElem_append_right (le_refl k)]
    simp [k]
  · rw [elimState_getD_at m gs acc j hj]
    exact simplifyGate_some_snd _ _ _ g' hopt

lemma elim_emit_inj (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j₁ j₂ : ℕ) (hj₁ : j₁ < gs.length) (hj₂ : j₂ < gs.length)
    (hnd₁ : j₁ ∉ elimDropped m gs acc) (hnd₂ : j₂ ∉ elimDropped m gs acc)
    (heq : (elimState m gs acc j₁).2.length = (elimState m gs acc j₂).2.length) :
    j₁ = j₂ := by
  by_contra hne
  wlog hlt : j₁ < j₂ generalizing j₁ j₂
  · exact this j₂ j₁ hj₂ hj₁ hnd₂ hnd₁ heq.symm (Ne.symm hne) (by omega)
  obtain ⟨g', hg', _, _, _, _⟩ := elim_emit_at m gs acc j₁ hj₁ hnd₁
  have h1 : (elimState m gs acc (j₁ + 1)).2.length = (elimState m gs acc j₁).2.length + 1 := by
    rw [elimState_succ m gs acc j₁ hj₁, elimStep, hg']; simp
  have h2 := elimState_snd_mono m gs acc (j₁ + 1) j₂ (by omega)
  omega

lemma elim_emit_wf (m : ℕ) (gs : List Gate) (v : Fin m) (b : Bool)
    (hnok : ∀ g ∈ gs, NOkGate g) :
    ∀ k : ℕ, (hk : k < (elimPass m gs (initVar m v b, [])).2.length) →
      ∀ w ∈ (elimPass m gs (initVar m v b, [])).2[k].inputs, w < m + k := by
  have hstep : ∀ t ≤ gs.length, ∀ k : ℕ, (hk : k < (elimState m gs (initVar m v b, []) t).2.length) →
      ∀ w ∈ (elimState m gs (initVar m v b, []) t).2[k].inputs, w < m + k := by
    intro t
    induction t with
    | zero => intro _ k hk; simp [elimState_zero] at hk
    | succ t ih =>
      intro ht k hk w hw
      have htlt : t < gs.length := by omega
      have hst_eq := elimState_succ m gs (initVar m v b, []) t htlt
      revert hk hw
      rw [hst_eq]
      intro hk hw
      let st := elimState m gs (initVar m v b, []) t
      have hst_def : elimState m gs (initVar m v b, []) t = st := rfl
      cases hopt : (simplifyGate gs[t].op (m + st.2.length)
          (gs[t].inputs.map fun i => st.1.getD i (Sum.inl false))).1 with
      | none =>
        have hstep_snd : (elimStep m st gs[t]).2 = st.2 := by
          simp only [elimStep, hopt, Option.toList_none, List.append_nil]
        have hk' : k < st.2.length := by rw [← hstep_snd]; exact hk
        have hw' : w ∈ (st.2[k]'hk').inputs := by
          have : (elimStep m st gs[t]).2[k]'hk = st.2[k]'hk' := by simp only [hstep_snd]
          rwa [← this]
        exact ih (by omega) k hk' w hw'
      | some g' =>
        have hstep_snd : (elimStep m st gs[t]).2 = st.2 ++ [g'] := by
          simp only [elimStep, hopt, Option.toList_some]
        by_cases hkt : k < st.2.length
        · have hw' : w ∈ (st.2[k]'hkt).inputs := by
            have : (elimStep m st gs[t]).2[k]'hk = st.2[k]'hkt := by
              simp only [hstep_snd, List.getElem_append_left hkt]
            rwa [← this]
          exact ih (by omega) k hkt w hw'
        · have hkeq : k = st.2.length := by
            have hlen_s : (elimStep m st gs[t]).2.length = st.2.length + 1 := by
              rw [hstep_snd]; simp
            have hk_lt : k < st.2.length + 1 := by rw [← hlen_s]; exact hk
            omega
          have hgw : w ∈ g'.inputs := by
            have : (elimStep m st gs[t]).2[k]'hk = g' := by
              simp only [hstep_snd, hkeq, List.getElem_append_right (le_refl st.2.length)]
              simp
            rwa [← this]
          have hmem := simplifyGate_mem_inputs_of_some _ _ _ g' hopt w hgw
          obtain ⟨i, _, hi⟩ := List.mem_map.1 hmem
          have hinv := elimInv_pass m (List.ofFn (fun _ : Fin m => false)) (gs.take t) _
            (initVar m v b, []) (fun g hg => (hnok g (List.mem_of_mem_take hg)).1)
            (elimInv_initVar m v b (fun _ => false))
          have hv := (hinv.2.2 i).1
          rw [← elimState, hst_def, hi] at hv
          simpa [statValid, hkeq] using hv
  simpa only [elimState_end] using hstep gs.length le_rfl

lemma elim_dropped_not_const {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m) (b : Bool)
    (j : ℕ) (hj : j < C.gates.length)
    (hdrop : j ∈ elimDropped m C.gates (initVar m v b, []))
    (hop : C.gates[j].op = GateOp.not) :
    ∃ a c, a < m + j ∧ C.gates[j].inputs = [a] ∧
      (elimState m C.gates (initVar m v b, []) j).1.getD a (Sum.inl false) = Sum.inl c ∧
      (elimState m C.gates (initVar m v b, []) (j + 1)).1.getD (m + j) (Sum.inl false) = Sum.inl (!c) ∧
      (a ≠ (v : ℕ) → m ≤ a ∧ a - m ∈ elimDropped m C.gates (initVar m v b, []) ∧
        (elimState m C.gates (initVar m v b, []) (a - m + 1)).1.getD a (Sum.inl false) = Sum.inl c) := by
  obtain ⟨a, ha, hins⟩ := (reduced_gate_wf C hnok hred j hj).1 hop
  have hnone : (simplifyGate GateOp.not (m + (elimState m C.gates (initVar m v b, []) j).2.length)
      [(elimState m C.gates (initVar m v b, []) j).1.getD a (Sum.inl false)]).1 = none := by
    rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdrop
    have h2 := hdrop.2
    simp only [hj, ↓reduceDIte, hop, hins, List.map_cons, List.map_nil] at h2
    exact Option.isNone_iff_eq_none.1 h2
  cases hsta : (elimState m C.gates (initVar m v b, []) j).1.getD a (Sum.inl false) with
  | inr w => rw [hsta] at hnone; simp [simplifyGate, simpNot] at hnone
  | inl c =>
    have hst_j : (elimState m C.gates (initVar m v b, []) (j + 1)).1.getD (m + j) (Sum.inl false) =
        Sum.inl (!c) := by
      have hget := elimState_getD_at m C.gates (initVar m v b, []) j hj
      have hlen : (initVar m v b).length = m := by simp [initVar]
      rw [hlen] at hget
      rw [hget, hop, hins]
      simp only [List.map_cons, List.map_nil, hsta, simplifyGate, simpNot]
    refine ⟨a, c, ha, hins, hsta, hst_j, ?_⟩
    intro hne
    have hge : m ≤ a := by
      by_contra hlt
      have hlt' : a < m := by omega
      have h0 : (elimState m C.gates (initVar m v b, []) j).1.getD a (Sum.inl false) = Sum.inr a := by
        rw [elimState_getD_mono m C.gates (initVar m v b, []) 0 j a _ (Nat.zero_le _) (by omega)
          (by simp [initVar]; exact hlt'), elimState_zero, initVar, ofFn_getD_lt _ _ _ hlt']
        have hfin : (⟨a, hlt'⟩ : Fin m) ≠ v := fun h => hne (congrArg Fin.val h)
        simp [hfin]
      rw [h0] at hsta; cases hsta
    have hst_am : (elimState m C.gates (initVar m v b, []) (a - m + 1)).1.getD a (Sum.inl false) = Sum.inl c := by
      have hmono := elimState_getD_mono m C.gates (initVar m v b, []) (a - m + 1) j a (Sum.inl false)
        (by omega) (by omega) (by simp [initVar]; omega)
      rw [← hmono, hsta]
    have hdrop_am : a - m ∈ elimDropped m C.gates (initVar m v b, []) := by
      by_contra hnd
      obtain ⟨_, _, _, _, _, hst_inr⟩ := elim_emit_at m C.gates (initVar m v b, []) (a - m) (by omega) hnd
      have hlen : (initVar m v b).length = m := by simp [initVar]
      rw [hlen, show m + (a - m) = a by omega] at hst_inr
      rw [hst_inr] at hst_am
      cases hst_am
    exact ⟨hge, hdrop_am, hst_am⟩

lemma elim_const_not_output_and_consumer {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m) (b : Bool)
    (hnc : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b))
    (j : ℕ) (hj : j < C.gates.length) (c : Bool)
    (hc : (elimState m C.gates (initVar m v b, []) (j + 1)).1.getD (m + j) (Sum.inl false) = Sum.inl c) :
    C.output ≠ m + j ∧
    ∃ k : ℕ, ∃ hk : k < C.gates.length, j < k ∧ (m + j) ∈ C.gates[k].inputs ∧
      k ∈ elimDropped m C.gates (initVar m v b, []) := by
  have hout_ne : C.output ≠ m + j := by
    intro heq
    have hst : (elimPass m C.gates (initVar m v b, [])).1.getD C.output (Sum.inl false) = Sum.inl c := by
      rw [heq, ← elimState_end,
        elimState_getD_mono m C.gates _ (j + 1) C.gates.length (m + j) _ (by omega) le_rfl (by simp [initVar])]
      exact hc
    obtain ⟨x, x', hne⟩ := hnc
    have hinv1 := elimInv_pass m (List.ofFn x) C.gates _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    have hinv2 := elimInv_pass m (List.ofFn x') C.gates _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x')
    have e1 := (hinv1.2.2 C.output).2
    have e2 := (hinv2.2.2 C.output).2
    rw [hst] at e1 e2
    exact hne (e1.symm.trans e2)
  obtain ⟨k, hk, hjk, hmem⟩ := (reduced_no_dead C hnok hred j hj).resolve_left hout_ne
  have hdrop_k : k ∈ elimDropped m C.gates (initVar m v b, []) := by
    apply mem_elimDropped_of_const m C.gates _ k hk (hnok _ (List.getElem_mem hk)) (m + j) hmem
    refine ⟨c, ?_⟩
    rw [elimState_getD_mono m C.gates _ (j + 1) k (m + j) _ (by omega) (by omega) (by simp [initVar])]
    exact hc
  exact ⟨hout_ne, k, hk, hjk, hmem, hdrop_k⟩

lemma elim_not_consumer_ne_not {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j₀ k a : ℕ) (hj₀ : j₀ < C.gates.length) (hk : k < C.gates.length)
    (hjk : j₀ < k) (ha : a < m + j₀) (hnot : C.gates[j₀] = ⟨GateOp.not, [a]⟩)
    (hmem : (m + j₀) ∈ C.gates[k].inputs) :
    C.gates[k].op ≠ GateOp.not := by
  intro hop
  obtain ⟨u, _, hins⟩ := (reduced_gate_wf C hnok hred k hk).1 hop
  rw [hins] at hmem; simp at hmem; subst hmem
  obtain ⟨x, hne⟩ := hred.2.1 a k (by omega) hk
  apply hne
  have hv0 : (C.wires (List.ofFn x)).getD (m + j₀) false = !(C.wires (List.ofFn x)).getD a false := by
    rw [wire_eval_gate C j₀ hj₀ x, hnot]
    simp only [ha, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
  rw [wire_eval_gate C k hk x, hop, hins]
  simp only [show m + j₀ < m + k by omega, ↓reduceIte, hv0, GateOp.eval, List.map_cons,
    List.map_nil, List.headD_cons, Bool.not_not]

lemma elim_gate_not_both_a_and_not_a {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j₀ k a : ℕ) (hj₀ : j₀ < C.gates.length) (hk : k < C.gates.length)
    (hjk : j₀ < k) (ha : a < m + j₀) (hnot : C.gates[j₀] = ⟨GateOp.not, [a]⟩)
    (hmem : (m + j₀) ∈ C.gates[k].inputs) :
    a ∉ C.gates[k].inputs := by
  classical
  intro ha_mem
  have hne_not := elim_not_consumer_ne_not C hnok hred j₀ k a hj₀ hk hjk ha hnot hmem
  have hbin : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
    rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hne_not
  obtain ⟨u, w, hu, hw, huw, hins⟩ := (reduced_gate_wf C hnok hred k hk).2 hbin
  rw [hins] at hmem ha_mem; simp at hmem ha_mem
  have hv0 : ∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD (m + j₀) false = !(C.wires (List.ofFn x)).getD a false := by
    intro x; rw [wire_eval_gate C j₀ hj₀ x, hnot]
    simp only [ha, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
  have hconst_val : ∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD (m + k) false =
        (if C.gates[k].op = GateOp.and then false else true) := by
    intro x
    rw [wire_eval_gate C k hk x, hins]
    rcases hmem with h1 | h1 <;> rcases ha_mem with h2 | h2
    · exact absurd (h1.trans h2.symm) (by omega)
    · rw [← h1, ← h2]
      rcases hbin with hop | hop <;>
        (simp only [hop, show m + j₀ < m + k by omega, show a < m + k by omega, ↓reduceIte,
          hv0 x, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false];
         cases (C.wires (List.ofFn x)).getD a false <;> simp)
    · rw [← h1, ← h2]
      rcases hbin with hop | hop <;>
        (simp only [hop, show m + j₀ < m + k by omega, show a < m + k by omega, ↓reduceIte,
          hv0 x, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false];
         cases (C.wires (List.ofFn x)).getD a false <;> simp)
    · exact absurd (h1.trans h2.symm) (by omega)
  obtain ⟨x, y, hne⟩ := hred.1 k hk
  exact hne ((hconst_val x).trans (hconst_val y).symm)

lemma elim_not_survives_or_dead {m opt' : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (v : Fin m) (b : Bool)
    (f' : (Fin m → Bool) → Bool)
    (hf'_eq : f' = fun x => circuitFun m C (Function.update x v b))
    (hnc' : ∃ x y : Fin m → Bool, f' x ≠ f' y)
    (hlb' : ∀ s' < opt', ¬ HasCircuitSize m f' s')
    (hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f' →
      D.size ≤ opt' + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (hsz_le : (elimPass m C.gates (initVar m v b, [])).2.length ≤ opt' + 1)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hnd : j₀ ∉ elimDropped m C.gates (initVar m v b, []))
    (hj₀_op : C.gates[j₀].op = GateOp.not) :
    let acc := elimPass m C.gates (initVar m v b, [])
    let k₀ := (elimState m C.gates (initVar m v b, []) j₀).2.length
    ∃ out : ℕ, acc.1.getD C.output (Sum.inl false) = Sum.inr out ∧
      acc.2.length = opt' + 1 ∧
      out ≠ m + k₀ ∧
      (∀ r : ℕ, (hr : r < acc.2.length) → k₀ < r → (m + k₀) ∉ acc.2[r].inputs) ∧
      (∀ r : ℕ, (hr : r < acc.2.length) → r ≠ k₀ → acc.2[r].op ≠ GateOp.not) := by
  intro acc k₀
  have hnc_upd : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    obtain ⟨x, x', hne⟩ := hnc'
    exact ⟨x, x', by simpa [hf'_eq] using hne⟩
  obtain ⟨out, hout_st, _, _, hfun_acc⟩ := elim_var_circuit C hnok v b hnc_upd
  set C' : Circuit := ⟨acc.2, out⟩ with hC'
  have hnok' : ∀ g ∈ C'.gates, NOkGate g :=
    elimPass_nok m C.gates (initVar m v b, []) (by simp)
  have hfun' : circuitFun m C' = f' := hfun_acc.trans hf'_eq.symm
  have hge_opt : opt' ≤ C'.gates.length := by
    by_contra hlt
    exact hlb' C'.gates.length (by omega)
      ⟨C', fun g hg => (hnok' g hg).1, le_rfl, fun x => congrFun hfun' x⟩
  obtain ⟨g₀, hg₀_some, hg₀_op, hk₀_lt, hk₀_eq, _⟩ :=
    elim_emit_at m C.gates (initVar m v b, []) j₀ hj₀ hnd
  have hk₀_not : (C'.gates[k₀]'hk₀_lt).op = GateOp.not := by
    change acc.2[k₀].op = GateOp.not
    rw [hk₀_eq, hg₀_op, hj₀_op]
  have hC'_le : C'.gates.length ≤ opt' + 1 := hsz_le
  have hlen_eq : C'.gates.length = opt' + 1 := by
    by_contra hne
    have hmin_eq : C'.gates.length = opt' := by omega
    have hmin' : ∀ s' < C'.gates.length, ¬ HasCircuitSize m (circuitFun m C') s' := by
      intro s' hs'; rw [hfun']; exact hlb' s' (by omega)
    have hred' := min_reduced C' hnok' hmin' (by rwa [hfun'])
    exact hIH' C' hnok' hfun' (by simpa [Circuit.size] using hsz_le) hred'
      (C'.gates[k₀]'hk₀_lt) (List.getElem_mem hk₀_lt) hk₀_not
  have hdead_kill : ∀ j : ℕ, (hj : j < C'.gates.length) →
      C'.output ≠ m + j →
      (∀ r : ℕ, (hr : r < C'.gates.length) → j < r → (m + j) ∉ C'.gates[r].inputs) →
      j = k₀ ∧ ∀ r : ℕ, (hr : r < C'.gates.length) → r ≠ k₀ → C'.gates[r].op ≠ GateOp.not := by
    intro j hj hout_ne hno_read
    set D := deleteGate m C' j 0 with hD
    have hDnok : ∀ g ∈ D.gates, NOkGate g := deleteGate_nok m C' j 0 hnok'
    have hDlen : D.gates.length = opt' := by rw [hD, deleteGate_len m C' j 0 hj, hlen_eq]; omega
    have hDfun : circuitFun m D = f' := by
      funext x
      rw [← hfun']
      show ((deleteGate m C' j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C'.output) false =
        (C'.wires (List.ofFn x)).getD C'.output false
      by_cases hlt : C'.output < m + C'.gates.length
      · exact deleteGate_dead_wires m C' j hj hno_read (List.ofFn x) (by simp) C'.output hlt hout_ne
      · have h1 : ((deleteGate m C' j 0).wires (List.ofFn x)).length =
            m + (deleteGate m C' j 0).gates.length := by
          show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
        have h2 : (C'.wires (List.ofFn x)).length = m + C'.gates.length := by
          show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
        have hge1 : m + (deleteGate m C' j 0).gates.length ≤ substWire (m + j) 0 C'.output := by
          rw [deleteGate_len m C' j 0 hj]; unfold substWire; split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    have hDmin : ∀ s' < D.gates.length, ¬ HasCircuitSize m (circuitFun m D) s' := by
      intro s' hs'; rw [hDfun]; exact hlb' s' (by omega)
    have hDred := min_reduced D hDnok hDmin (by rwa [hDfun])
    have hDnoNot : ∀ g ∈ D.gates, g.op ≠ GateOp.not :=
      hIH' D hDnok hDfun (by show D.gates.length ≤ opt' + 1; omega) hDred
    have hother_noNot : ∀ r : ℕ, (hr : r < C'.gates.length) → r ≠ j → C'.gates[r].op ≠ GateOp.not := by
      intro r hr hrne
      by_cases hlt : r < j
      · have hrD : r < D.gates.length := by omega
        have hget := deleteGate_getElem_lt m C' j 0 r hj hlt
        have hne := hDnoNot (D.gates[r]'hrD) (List.getElem_mem hrD)
        change ((deleteGate m C' j 0).gates[r]'(by rw [← hD]; exact hrD)).op ≠ GateOp.not at hne
        rwa [hget] at hne
      · have hgt : j < r := by omega
        have hrD : r - 1 < D.gates.length := by omega
        have hget := deleteGate_getElem_gt m C' j 0 r hj hr hgt
        have hne := hDnoNot (D.gates[r - 1]'hrD) (List.getElem_mem hrD)
        change ((deleteGate m C' j 0).gates[r - 1]'(by rw [← hD]; exact hrD)).op ≠ GateOp.not at hne
        rw [hget] at hne
        exact hne
    have hjeq : j = k₀ := by
      by_contra hne
      exact hother_noNot k₀ hk₀_lt (Ne.symm hne) hk₀_not
    subst hjeq
    exact ⟨rfl, hother_noNot⟩

  have hnot_red : ¬ Reduced m C' := fun hred' =>
    hIH' C' hnok' hfun' (by show C'.gates.length ≤ opt' + 1; omega) hred'
      (C'.gates[k₀]'hk₀_lt) (List.getElem_mem hk₀_lt) hk₀_not

  by_cases h1 : ∀ j : ℕ, j < C'.gates.length → ∃ x y : Fin m → Bool,
      (C'.wires (List.ofFn x)).getD (m + j) false ≠ (C'.wires (List.ofFn y)).getD (m + j) false
  · by_cases h2 : ∀ i j : ℕ, i < m + j → j < C'.gates.length → ∃ x : Fin m → Bool,
        (C'.wires (List.ofFn x)).getD i false ≠ (C'.wires (List.ofFn x)).getD (m + j) false
    · by_cases h3 : C'.gates ≠ [] → C'.output + 1 = m + C'.gates.length
      ·
        have h4 : ¬ ∀ j : ℕ, j + 1 < C'.gates.length → ∃ p ∈ C'.gates.zipIdx, m + j < m + p.2 ∧
            (GateOp.casesOn (motive := fun _ => List ℕ) p.1.op
              p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (m + j) = true :=
          fun h4 => hnot_red ⟨h1, h2, h3, h4⟩
        push Not at h4
        obtain ⟨j, hj1, hno4⟩ := h4
        have hne_nil : C'.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
        have hout_eq := h3 hne_nil
        have hno_read : ∀ r : ℕ, (hr : r < C'.gates.length) → j < r → (m + j) ∉ C'.gates[r].inputs := by
          intro r hr hlt hmem
          have hmem_z : (C'.gates[r]'hr, r) ∈ C'.gates.zipIdx := by
            rw [List.mem_iff_getElem]
            exact ⟨r, by simp [List.length_zipIdx, hr], by simp [List.getElem_zipIdx]⟩
          have hcont := hno4 (C'.gates[r]'hr, r) hmem_z (by omega)
          change (GateOp.casesOn (motive := fun _ => List ℕ) (C'.gates[r]'hr).op
            (C'.gates[r]'hr).inputs (C'.gates[r]'hr).inputs ((C'.gates[r]'hr).inputs.take 1)
            (fun _ => (C'.gates[r]'hr).inputs) (C'.gates[r]'hr).inputs).contains (m + j) ≠ true at hcont
          rw [effInputs_eq_inputs_of_nok _ (hnok' _ (List.getElem_mem hr))] at hcont
          exact hcont (List.contains_iff_mem.2 hmem)
        obtain ⟨hjk, huniq⟩ := hdead_kill j (by omega) (by omega) hno_read
        subst hjk
        exact ⟨out, hout_st, hlen_eq, by change C'.output ≠ m + k₀; omega, hno_read, huniq⟩
      ·
        push Not at h3
        obtain ⟨hne_nil, hout_ne_last⟩ := h3
        have hpos : 0 < C'.gates.length := List.length_pos_of_ne_nil hne_nil
        have hout_lt := min_output_lt C' (by rwa [hfun'])
        have hno_read : ∀ r : ℕ, (hr : r < C'.gates.length) → C'.gates.length - 1 < r →
            (m + (C'.gates.length - 1)) ∉ C'.gates[r].inputs :=
          fun r hr hlt => by omega
        obtain ⟨hjk, huniq⟩ := hdead_kill (C'.gates.length - 1) (by omega) (by omega) hno_read
        exact ⟨out, hout_st, hlen_eq, by rw [← hjk]; change C'.output ≠ m + (C'.gates.length - 1); omega,
          by rw [← hjk]; exact hno_read, huniq⟩
    ·
      exfalso
      push Not at h2
      obtain ⟨u, j, huj, hj, heq⟩ := h2
      set D := deleteGate m C' j u with hD
      have hDnok : ∀ g ∈ D.gates, NOkGate g := deleteGate_nok m C' j u hnok'
      have hDlen : D.gates.length = opt' := by rw [hD, deleteGate_len m C' j u hj, hlen_eq]; omega
      have hDfun : circuitFun m D = f' := by
        funext x
        rw [← hfun']
        show ((deleteGate m C' j u).wires (List.ofFn x)).getD (substWire (m + j) u C'.output) false =
          (C'.wires (List.ofFn x)).getD C'.output false
        by_cases hlt : C'.output < m + C'.gates.length
        · exact deleteGate_wires_eq m C' j u hj huj (List.ofFn x) (by simp) (heq x).symm C'.output hlt
        · have h1' : ((deleteGate m C' j u).wires (List.ofFn x)).length =
              m + (deleteGate m C' j u).gates.length := by
            show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
          have h2' : (C'.wires (List.ofFn x)).length = m + C'.gates.length := by
            show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
          have hge1 : m + (deleteGate m C' j u).gates.length ≤ substWire (m + j) u C'.output := by
            rw [deleteGate_len m C' j u hj]; unfold substWire; split_ifs <;> omega
          rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have hDmin : ∀ s' < D.gates.length, ¬ HasCircuitSize m (circuitFun m D) s' := by
        intro s' hs'; rw [hDfun]; exact hlb' s' (by omega)
      have hDred := min_reduced D hDnok hDmin (by rwa [hDfun])
      have hDnoNot : ∀ g ∈ D.gates, g.op ≠ GateOp.not :=
        hIH' D hDnok hDfun (by show D.gates.length ≤ opt' + 1; omega) hDred
      have hjeq : j = k₀ := by
        by_contra hne
        by_cases hlt : k₀ < j
        · have hkD : k₀ < D.gates.length := by omega
          have hget := deleteGate_getElem_lt m C' j u k₀ hj hlt
          have hnotD := hDnoNot (D.gates[k₀]'hkD) (List.getElem_mem hkD)
          change ((deleteGate m C' j u).gates[k₀]'(by rw [← hD]; exact hkD)).op ≠ GateOp.not at hnotD
          rw [hget] at hnotD; exact hnotD hk₀_not
        · have hgt : j < k₀ := by omega
          have hkD : k₀ - 1 < D.gates.length := by omega
          have hget := deleteGate_getElem_gt m C' j u k₀ hj hk₀_lt hgt
          have hnotD := hDnoNot (D.gates[k₀ - 1]'hkD) (List.getElem_mem hkD)
          change ((deleteGate m C' j u).gates[k₀ - 1]'(by rw [← hD]; exact hkD)).op ≠ GateOp.not at hnotD
          rw [hget] at hnotD; exact hnotD hk₀_not
      subst hjeq
      have hins_k₀ : ∃ a', a' < m + k₀ ∧ (C'.gates[k₀]'hk₀_lt).inputs = [a'] := by
        have hlen1 := (hnok' _ (List.getElem_mem hk₀_lt)).2 hk₀_not
        rcases hins : (C'.gates[k₀]'hk₀_lt).inputs with _ | ⟨a', _ | ⟨b', l⟩⟩
        · exfalso
          have hconst : ∀ x y : Fin m → Bool,
              (C'.wires (List.ofFn x)).getD (m + k₀) false = (C'.wires (List.ofFn y)).getD (m + k₀) false := by
            intro x y; rw [wire_eval_gate C' k₀ hk₀_lt x, wire_eval_gate C' k₀ hk₀_lt y, hk₀_not, hins]; rfl
          obtain ⟨x, y, hne⟩ := h1 k₀ hk₀_lt
          exact hne (hconst x y)
        · have hmem_a' : a' ∈ ((elimPass m C.gates (initVar m v b, [])).2[k₀]'hk₀_lt).inputs := by
            change a' ∈ (C'.gates[k₀]'hk₀_lt).inputs; rw [hins]; simp
          have ha'lt : a' < m + k₀ := elim_emit_wf m C.gates v b hnok k₀ hk₀_lt a' hmem_a'
          exact ⟨a', ha'lt, rfl⟩
        · rw [hins] at hlen1; simp at hlen1
      obtain ⟨a', ha'lt, hins'⟩ := hins_k₀
      let x0 : Fin m → Bool := fun _ => false
      have hwD_a' : (D.wires (List.ofFn x0)).getD a' false = false :=
        no_not_eval_false D hDnok hDred hDnoNot a' (by omega)
      have hwD_u : (D.wires (List.ofFn x0)).getD u false = false :=
        no_not_eval_false D hDnok hDred hDnoNot u (by omega)
      have hwC_a' : (C'.wires (List.ofFn x0)).getD a' false = false := by
        have h := deleteGate_wires_eq m C' k₀ u hk₀_lt huj (List.ofFn x0) (by simp) (heq x0).symm a' (by omega)
        have hsub : substWire (m + k₀) u a' = a' := by simp [substWire, ha'lt]
        rw [hsub, ← hD, hwD_a'] at h; exact h.symm
      have hwC_u : (C'.wires (List.ofFn x0)).getD u false = false := by
        have h := deleteGate_wires_eq m C' k₀ u hk₀_lt huj (List.ofFn x0) (by simp) (heq x0).symm u (by omega)
        have hsub : substWire (m + k₀) u u = u := by simp [substWire, huj]
        rw [hsub, ← hD, hwD_u] at h; exact h.symm
      have hwC_k₀ : (C'.wires (List.ofFn x0)).getD (m + k₀) false = true := by
        rw [wire_eval_gate C' k₀ hk₀_lt x0, hk₀_not, hins']
        simp only [ha'lt, ↓reduceIte, hwC_a', GateOp.eval, List.map_cons, List.map_nil,
          List.headD_cons, Bool.not_false]
      have hcontr := heq x0
      rw [hwC_u, hwC_k₀] at hcontr
      exact Bool.noConfusion hcontr
  ·
    push Not at h1
    obtain ⟨j, hj, hconst_all⟩ := h1
    set c := (C'.wires (List.ofFn (fun _ : Fin m => false))).getD (m + j) false
    have hconst : ∀ x : Fin m → Bool, (C'.wires (List.ofFn x)).getD (m + j) false = c :=
      fun x => hconst_all x (fun _ => false)
    have hout_ne : C'.output ≠ m + j := by
      intro heq
      obtain ⟨x, y, hne⟩ := hnc'
      rw [← hfun'] at hne
      have hx : circuitFun m C' x = c := by show (C'.wires _).getD C'.output false = c; rw [heq]; exact hconst x
      have hy : circuitFun m C' y = c := by show (C'.wires _).getD C'.output false = c; rw [heq]; exact hconst y
      exact hne (hx.trans hy.symm)
    by_cases hread : ∃ r : ℕ, ∃ hr : r < C'.gates.length, j < r ∧ (m + j) ∈ C'.gates[r].inputs
    · exfalso
      obtain ⟨r, hr, hjr, hmem⟩ := hread
      have h2 := deleteConstGate_two C' hnok' j r hj hr hjr hmem c hconst (by rwa [hfun'])
      rw [hfun', hlen_eq] at h2
      exact hlb' (opt' + 1 - 2) (by omega) h2
    · have hno_read : ∀ r : ℕ, (hr : r < C'.gates.length) → j < r → (m + j) ∉ C'.gates[r].inputs :=
        fun r hr hjr hmem => hread ⟨r, hr, hjr, hmem⟩
      obtain ⟨hjk, huniq⟩ := hdead_kill j hj hout_ne hno_read
      subst hjk
      exact ⟨out, hout_st, hlen_eq, hout_ne, hno_read, huniq⟩

lemma dead_wire_in_elim {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m) (b : Bool)
    (hnc : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b))
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hnd : j₀ ∉ elimDropped m C.gates (initVar m v b, []))
    (out : ℕ)
    (hout_st : (elimPass m C.gates (initVar m v b, [])).1.getD C.output (Sum.inl false) = Sum.inr out)
    (hout_ne : out ≠ m + (elimState m C.gates (initVar m v b, []) j₀).2.length)
    (hdead : ∀ r : ℕ, (hr : r < (elimPass m C.gates (initVar m v b, [])).2.length) →
      (elimState m C.gates (initVar m v b, []) j₀).2.length < r →
      (m + (elimState m C.gates (initVar m v b, []) j₀).2.length) ∉
        (elimPass m C.gates (initVar m v b, [])).2[r].inputs) :
    let k₀ := (elimState m C.gates (initVar m v b, []) j₀).2.length
    ∃ k r : ℕ, ∃ (hk : k < C.gates.length) (hr : r < C.gates.length) (c : Bool),
      j₀ < k ∧ k < r ∧
      k ∈ elimDropped m C.gates (initVar m v b, []) ∧
      r ∈ elimDropped m C.gates (initVar m v b, []) ∧
      (elimState m C.gates (initVar m v b, []) (k + 1)).1.getD (m + k) (Sum.inl false) = Sum.inl c ∧
      (∃ u < m + k, u ∈ C.gates[k].inputs ∧
        (elimState m C.gates (initVar m v b, []) k).1.getD u (Sum.inl false) = Sum.inr (m + k₀)) ∧
      (m + k) ∈ C.gates[r].inputs := by
  classical
  intro k₀
  set init := (initVar m v b, ([] : List Gate)) with hinit
  set acc := elimPass m C.gates init with hacc
  have hlen_init : init.1.length = m := by simp [hinit, initVar]
  obtain ⟨_, _, _, _, _, hst_j₀⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd
  rw [hlen_init] at hst_j₀
  have hacc_j₀ : acc.1.getD (m + j₀) (Sum.inl false) = Sum.inr (m + k₀) := by
    rw [hacc, ← elimState_end,
      elimState_getD_mono m C.gates init (j₀ + 1) C.gates.length (m + j₀) _ (by omega) le_rfl (by omega)]
    exact hst_j₀
  set S : Finset ℕ := (Finset.range (m + C.gates.length)).filter
    (fun u => acc.1.getD u (Sum.inl false) = Sum.inr (m + k₀)) with hS
  have hS_ne : S.Nonempty :=
    ⟨m + j₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hacc_j₀⟩⟩
  set u := S.max' hS_ne with hu
  have hu_mem : u ∈ S := Finset.max'_mem S hS_ne
  have hu_le : m + j₀ ≤ u := Finset.le_max' S (m + j₀)
    (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hacc_j₀⟩)
  obtain ⟨hu_lt, hu_st⟩ := Finset.mem_filter.1 hu_mem
  rw [Finset.mem_range] at hu_lt
  set ju := u - m with hju
  have hu_eq : u = m + ju := by omega
  have hju_lt : ju < C.gates.length := by omega
  have hout_ne_u : C.output ≠ m + ju := by
    intro heq
    rw [heq, ← hu_eq, hu_st] at hout_st
    exact hout_ne (Sum.inr.inj hout_st).symm
  obtain ⟨k, hk, hjuk, hmem_uk⟩ := (reduced_no_dead C hnok hred ju hju_lt).resolve_left hout_ne_u
  have hst_uk : (elimState m C.gates init k).1.getD (m + ju) (Sum.inl false) = Sum.inr (m + k₀) := by
    have hmono := elimState_getD_mono m C.gates init k C.gates.length (m + ju) (Sum.inl false)
      (by omega) le_rfl (by rw [hlen_init]; omega)
    rw [elimState_end, ← hacc] at hmono
    rw [← hmono, ← hu_eq, hu_st]
  have hdrop_k : k ∈ elimDropped m C.gates init := by
    by_contra hnd_k
    obtain ⟨g_k, hg_k, _, hk'_lt, hk'_eq, _⟩ := elim_emit_at m C.gates init k hk hnd_k
    set k' := (elimState m C.gates init k).2.length
    have hlt_k' : k₀ < k' := by
      have h1 : (elimState m C.gates init (j₀ + 1)).2.length = k₀ + 1 := by
        obtain ⟨g0, hg0, _, _, _, _⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd
        rw [elimState_succ m C.gates init j₀ hj₀, elimStep, hg0]; simp [k₀, hinit]
      have h2 := elimState_snd_mono m C.gates init (j₀ + 1) k (by omega)
      omega
    have hmem_ins : Sum.inr (m + k₀) ∈ (C.gates[k].inputs.map fun i =>
        (elimState m C.gates init k).1.getD i (Sum.inl false)) :=
      List.mem_map.2 ⟨m + ju, hmem_uk, hst_uk⟩
    have hmem_gk := simplifyGate_some_mem_inputs C.gates[k].op (m + k') _
      (fun hop => by simp [(hnok _ (List.getElem_mem hk)).2 hop]) g_k hg_k (m + k₀) hmem_ins
    have hmem_acc : (m + k₀) ∈ acc.2[k'].inputs := by rw [hk'_eq]; exact hmem_gk
    exact hdead k' hk'_lt hlt_k' hmem_acc
  have hst_k_const : ∃ c : Bool,
      (elimState m C.gates init (k + 1)).1.getD (m + k) (Sum.inl false) = Sum.inl c := by
    cases hstk : (elimState m C.gates init (k + 1)).1.getD (m + k) (Sum.inl false) with
    | inl c => exact ⟨c, rfl⟩
    | inr w' =>
      exfalso
      have hget := elimState_getD_at m C.gates init k hk
      rw [hlen_init] at hget
      rw [hget] at hstk
      have hnone_k : (simplifyGate C.gates[k].op (m + (elimState m C.gates init k).2.length)
          (C.gates[k].inputs.map fun i => (elimState m C.gates init k).1.getD i (Sum.inl false))).1 = none := by
        rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdrop_k
        have h2 := hdrop_k.2
        simp only [hk, ↓reduceDIte] at h2
        exact Option.isNone_iff_eq_none.1 h2
      have hmem_ins : Sum.inr (m + k₀) ∈ (C.gates[k].inputs.map fun i =>
          (elimState m C.gates init k).1.getD i (Sum.inl false)) :=
        List.mem_map.2 ⟨m + ju, hmem_uk, hst_uk⟩
      have hw'_eq := simplifyGate_none_of_inr_mem C.gates[k].op _ _
        (hnok _ (List.getElem_mem hk)).1.1 (by simp [(hnok _ (List.getElem_mem hk)).1.2])
        (fun hop => by simp [(hnok _ (List.getElem_mem hk)).2 hop]) hnone_k (m + k₀) w' hmem_ins hstk
      have hacc_k : acc.1.getD (m + k) (Sum.inl false) = Sum.inr (m + k₀) := by
        rw [hacc, ← elimState_end,
          elimState_getD_mono m C.gates init (k + 1) C.gates.length (m + k) _ (by omega) le_rfl (by omega),
          hget, hstk, hw'_eq]
      have hk_in_S : m + k ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hacc_k⟩
      have hle_u := Finset.le_max' S (m + k) hk_in_S
      omega
  obtain ⟨c, hc⟩ := hst_k_const
  obtain ⟨_, r, hr, hkr, hmem_kr, hdrop_r⟩ :=
    elim_const_not_output_and_consumer C hnok hred v b hnc k hk c hc
  exact ⟨k, r, hk, hr, c, by omega, hkr, hdrop_k, hdrop_r, hc,
    ⟨m + ju, by omega, hmem_uk, hst_uk⟩, hmem_kr⟩

lemma elim_delta1_contra {m opt : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hsz : C.gates.length ≤ opt + 1)
    (v : Fin m) (b : Bool)
    (hinc : ∃ x : Fin m → Bool,
      circuitFun m C (Function.update x v false) = false ∧
      circuitFun m C (Function.update x v true) = true)
    (f' : (Fin m → Bool) → Bool)
    (hf'_eq : f' = fun x => circuitFun m C (Function.update x v b))
    (hnc' : ∃ x y : Fin m → Bool, f' x ≠ f' y)
    (hlb' : ∀ s' < opt - 1, ¬ HasCircuitSize m f' s')
    (hopt_pos : 1 ≤ opt)
    (hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f' →
      D.size ≤ (opt - 1) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hj₀_op : C.gates[j₀].op = GateOp.not) :
    False := by
  let init := (initVar m v b, ([] : List Gate))
  let D := elimDropped m C.gates init
  have hnc_upd : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    obtain ⟨x, x', hne⟩ := hnc'
    exact ⟨x, x', by simpa [hf'_eq] using hne⟩
  obtain ⟨out, hout_st, _, hcard, hfun_acc⟩ := elim_var_circuit C hnok v b hnc_upd
  have hcard' : (elimPass m C.gates init).2.length + D.card = C.gates.length := hcard
  have hlb_len : opt - 1 ≤ (elimPass m C.gates init).2.length := by
    by_contra hlt
    exact hlb' (elimPass m C.gates init).2.length (by omega)
      ⟨⟨(elimPass m C.gates init).2, out⟩, elimPass_ok m C.gates init (by simp [init]), le_rfl,
        fun x => by rw [hf'_eq]; exact congrFun hfun_acc x⟩

  have hD_pos : 1 ≤ D.card := by
    by_contra h0
    have hD0 : D = ∅ := Finset.card_eq_zero.1 (by omega)
    have hno_v : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∉ C.gates[j].inputs := by
      intro j hj hmem
      have hdrop_j : j ∈ D := by
        apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hmem
        refine ⟨b, ?_⟩
        rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
          (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      rw [hD0] at hdrop_j; exact Finset.notMem_empty j hdrop_j
    obtain ⟨x, hx0, hx1⟩ := hinc
    have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hout := hred.2.2.1 hne
    have heq := wire_indep_of_not_read C v hno_v C.gates.length le_rfl C.output (by omega) (by omega) x
    change circuitFun m C (Function.update x v false) = circuitFun m C (Function.update x v true) at heq
    rw [hx0, hx1] at heq; exact Bool.noConfusion heq

  have hD_le2 : D.card ≤ 2 := by omega
  by_cases hD1 : D.card = 1
  ·
    have hnd : j₀ ∉ D := by
      intro hdrop
      obtain ⟨a, c, _, _, _, hst, _⟩ := elim_dropped_not_const C hnok hred v b j₀ hj₀ hdrop hj₀_op
      obtain ⟨_, k, hk, hjk, _, hdrop_k⟩ := elim_const_not_output_and_consumer C hnok hred v b hnc_upd j₀ hj₀ (!c) hst
      have hsub : ({j₀, k} : Finset ℕ) ⊆ D := by
        intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
      have hc2 : ({j₀, k} : Finset ℕ).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have := Finset.card_le_card hsub
      omega
    obtain ⟨out', hout_st', _, hout_ne, hdead, _⟩ :=
      elim_not_survives_or_dead C hnok v b f' hf'_eq hnc' hlb' hIH' (by change (elimPass m C.gates init).2.length ≤ opt - 1 + 1; omega) j₀ hj₀ hnd hj₀_op
    obtain ⟨k, r, _, _, _, _, hkr, hdk, hdr, _, _, _⟩ :=
      dead_wire_in_elim C hnok hred v b hnc_upd j₀ hj₀ hnd out' hout_st' hout_ne hdead
    have hsub : ({k, r} : Finset ℕ) ⊆ D := by
      intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
    have hc2 : ({k, r} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have := Finset.card_le_card hsub
    omega
  ·
    have hD2 : D.card = 2 := by omega
    have hacc_len : (elimPass m C.gates init).2.length = opt - 1 := by omega
    set C' : Circuit := ⟨(elimPass m C.gates init).2, out⟩ with hC'
    have hC'_len : C'.gates.length = (elimPass m C.gates init).2.length := rfl
    have hnok' : ∀ g ∈ C'.gates, NOkGate g := elimPass_nok m C.gates init (by simp [init])
    have hfun' : circuitFun m C' = f' := hfun_acc.trans hf'_eq.symm
    have hmin' : ∀ s' < C'.gates.length, ¬ HasCircuitSize m (circuitFun m C') s' := by
      intro s' hs'; rw [hfun']; exact hlb' s' (by omega)
    have hred' := min_reduced C' hnok' hmin' (by rwa [hfun'])
    have hnoNot' : ∀ g ∈ C'.gates, g.op ≠ GateOp.not :=
      hIH' C' hnok' hfun' (by show C'.gates.length ≤ (opt - 1) + 1; omega) hred'
    have hdrop_all_not : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j ∈ D := by
      intro j hj hop
      by_contra hnd
      obtain ⟨g', _, hg'op, hklt, hkeq, _⟩ := elim_emit_at m C.gates init j hj hnd
      have hne := hnoNot' (C'.gates[(elimState m C.gates init j).2.length]'hklt) (List.getElem_mem hklt)
      change ((elimPass m C.gates init).2[(elimState m C.gates init j).2.length]'hklt).op ≠ GateOp.not at hne
      rw [hkeq, hg'op, hop] at hne; exact hne rfl
    have hdrop_j₀ : j₀ ∈ D := hdrop_all_not j₀ hj₀ hj₀_op
    obtain ⟨a, c, ha, hins, _, hst_j₀, hne_v⟩ :=
      elim_dropped_not_const C hnok hred v b j₀ hj₀ hdrop_j₀ hj₀_op
    obtain ⟨_, k, hk, hjk, hmem_k, hdrop_k⟩ :=
      elim_const_not_output_and_consumer C hnok hred v b hnc_upd j₀ hj₀ (!c) hst_j₀
    have ha_eq_v : a = (v : ℕ) := by
      by_contra hne
      obtain ⟨hge, hdrop_am, _⟩ := hne_v hne
      have hsub : ({a - m, j₀, k} : Finset ℕ) ⊆ D := by
        intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
      have hc3 : ({a - m, j₀, k} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have := Finset.card_le_card hsub
      omega
    have hD_eq : D = {j₀, k} := by
      have hsub : ({j₀, k} : Finset ℕ) ⊆ D := by
        intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
      have hc2 : ({j₀, k} : Finset ℕ).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    have hnot_eq : C.gates[j₀] = ⟨GateOp.not, [(v : ℕ)]⟩ := by
      cases hg : C.gates[j₀] with
      | mk op ins =>
        rw [hg] at hj₀_op hins
        simp only at hj₀_op hins
        subst hj₀_op; subst hins; subst ha_eq_v; rfl
    have hk_ne_not : C.gates[k].op ≠ GateOp.not :=
      elim_not_consumer_ne_not C hnok hred j₀ k (v : ℕ) hj₀ hk hjk (by omega) hnot_eq hmem_k
    have hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀ := by
      intro j hj hop
      have hmem : j ∈ D := hdrop_all_not j hj hop
      rw [hD_eq] at hmem; simp at hmem
      rcases hmem with hjeq | hjeq
      · exact hjeq
      · subst hjeq; exact absurd hop hk_ne_not
    have hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₀ := by
      intro j hj hmem_v
      have hdrop_j : j ∈ D := by
        apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hmem_v
        refine ⟨b, ?_⟩
        rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
          (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      rw [hD_eq] at hdrop_j; simp at hdrop_j
      rcases hdrop_j with hjeq | hjeq
      · exact hjeq
      · subst hjeq
        exact absurd hmem_v
          (elim_gate_not_both_a_and_not_a C hnok hred j₀ j (v : ℕ) hj₀ hj hjk (by omega) hnot_eq hmem_k)
    obtain ⟨x, hx0, hx1⟩ := hinc
    have hanti := single_not_antimono_direct C hnok hred v j₀ hj₀ hnot_eq hnot_uniq hv_uniq x hx1
    rw [hx0] at hanti; exact Bool.noConfusion hanti

lemma elim_delta2_d3_contra {m opt : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hsz : C.gates.length ≤ opt + 1)
    (v : Fin m) (b : Bool)
    (hinc : ∃ x : Fin m → Bool,
      circuitFun m C (Function.update x v false) = false ∧
      circuitFun m C (Function.update x v true) = true)
    (hopt_ge2 : 2 ≤ opt)
    (f0 f1 : (Fin m → Bool) → Bool)
    (hf0_eq : f0 = fun x => circuitFun m C (Function.update x v false))
    (hf1_eq : f1 = fun x => circuitFun m C (Function.update x v true))
    (hnc0 : ∃ x y : Fin m → Bool, f0 x ≠ f0 y)
    (hnc1 : ∃ x y : Fin m → Bool, f1 x ≠ f1 y)
    (hlb0 : ∀ s' < opt - 2, ¬ HasCircuitSize m f0 s')
    (hlb1 : ∀ s' < opt - 2, ¬ HasCircuitSize m f1 s')
    (hIHb : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
      circuitFun m D = (if b then f1 else f0) →
      D.size ≤ (opt - 2) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (hd3 : (elimDropped m C.gates (initVar m v b, [])).card = 3)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hj₀_op : C.gates[j₀].op = GateOp.not) :
    False := by
  classical
  let init := (initVar m v b, ([] : List Gate))
  let D := elimDropped m C.gates init
  have hnc_b : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    cases b
    · obtain ⟨x, x', hne⟩ := hnc0; exact ⟨x, x', by simpa [hf0_eq] using hne⟩
    · obtain ⟨x, x', hne⟩ := hnc1; exact ⟨x, x', by simpa [hf1_eq] using hne⟩
  have hlb_b : ∀ s' < opt - 2, ¬ HasCircuitSize m (if b then f1 else f0) s' := by
    cases b <;> assumption
  have hfb_eq : (if b then f1 else f0) = fun x => circuitFun m C (Function.update x v b) := by
    cases b <;> simp [hf0_eq, hf1_eq]
  obtain ⟨out, _, _, hcard, hfun_acc⟩ := elim_var_circuit C hnok v b hnc_b
  have hcard' : (elimPass m C.gates init).2.length + D.card = C.gates.length := hcard
  have hacc_ge : opt - 2 ≤ (elimPass m C.gates init).2.length := by
    by_contra hlt
    exact hlb_b (elimPass m C.gates init).2.length (by omega)
      ⟨⟨(elimPass m C.gates init).2, out⟩, elimPass_ok m C.gates init (by simp [init]), le_rfl,
        fun x => by rw [hfb_eq]; exact congrFun hfun_acc x⟩
  have hD3 : D.card = 3 := hd3
  have hacc_len : (elimPass m C.gates init).2.length = opt - 2 := by omega
  set C' : Circuit := ⟨(elimPass m C.gates init).2, out⟩ with hC'
  have hC'_len : C'.gates.length = (elimPass m C.gates init).2.length := rfl
  have hnok' : ∀ g ∈ C'.gates, NOkGate g := elimPass_nok m C.gates init (by simp [init])
  have hfun' : circuitFun m C' = (if b then f1 else f0) := hfun_acc.trans hfb_eq.symm
  have hmin' : ∀ s' < C'.gates.length, ¬ HasCircuitSize m (circuitFun m C') s' := by
    intro s' hs'; rw [hfun']; exact hlb_b s' (by omega)
  have hred' := min_reduced C' hnok' hmin' (by rw [hfun', hfb_eq]; exact hnc_b)
  have hnoNot' : ∀ g ∈ C'.gates, g.op ≠ GateOp.not :=
    hIHb C' hnok' hfun' (by show C'.gates.length ≤ (opt - 2) + 1; omega) hred'
  have hdrop_all_not : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j ∈ D := by
    intro j hj hop
    by_contra hnd
    obtain ⟨g', _, hg'op, hklt, hkeq, _⟩ := elim_emit_at m C.gates init j hj hnd
    have hne := hnoNot' (C'.gates[(elimState m C.gates init j).2.length]'hklt) (List.getElem_mem hklt)
    change ((elimPass m C.gates init).2[(elimState m C.gates init j).2.length]'hklt).op ≠ GateOp.not at hne
    rw [hkeq, hg'op, hop] at hne; exact hne rfl
  have hdrop_v : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j ∈ D := by
    intro j hj hmem
    apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hmem
    refine ⟨b, ?_⟩
    rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
      (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
    simp
  have hdrop_j₀ : j₀ ∈ D := hdrop_all_not j₀ hj₀ hj₀_op
  obtain ⟨a, c, ha, hins, hsta, hst_j₀, hne_v⟩ :=
    elim_dropped_not_const C hnok hred v b j₀ hj₀ hdrop_j₀ hj₀_op
  obtain ⟨_, k, hk, hjk, hmem_k, hdrop_k⟩ :=
    elim_const_not_output_and_consumer C hnok hred v b hnc_b j₀ hj₀ (!c) hst_j₀
  by_cases hav : a = (v : ℕ)
  ·
    have hnot_eq : C.gates[j₀] = ⟨GateOp.not, [(v : ℕ)]⟩ := by
      cases hg : C.gates[j₀] with
      | mk op ins =>
        rw [hg] at hj₀_op hins; simp only at hj₀_op hins
        subst hj₀_op; subst hins; subst hav; rfl
    by_cases hother_v : ∃ g₂ : ℕ, ∃ hg₂ : g₂ < C.gates.length, g₂ ≠ j₀ ∧ (v : ℕ) ∈ C.gates[g₂].inputs
    ·
      obtain ⟨g₂, hg₂, hg₂_ne, hg₂_v⟩ := hother_v
      have hg₂_ne_not : C.gates[g₂].op ≠ GateOp.not := by
        intro hop
        obtain ⟨u, _, hu_ins⟩ := (reduced_gate_wf C hnok hred g₂ hg₂).1 hop
        rw [hu_ins] at hg₂_v; simp at hg₂_v; subst hg₂_v
        have hsame : ∀ x : Fin m → Bool,
            (C.wires (List.ofFn x)).getD (m + j₀) false = (C.wires (List.ofFn x)).getD (m + g₂) false := by
          intro x
          rw [wire_eval_gate C j₀ hj₀ x, hnot_eq, wire_eval_gate C g₂ hg₂ x, hop, hu_ins]
          simp [show (v : ℕ) < m + j₀ by omega, show (v : ℕ) < m + g₂ by omega, GateOp.eval]
        by_cases hlt : j₀ < g₂
        · obtain ⟨x, hne⟩ := hred.2.1 (m + j₀) g₂ (by omega) hg₂
          exact hne (hsame x)
        · obtain ⟨x, hne⟩ := hred.2.1 (m + g₂) j₀ (by omega) hj₀
          exact hne (hsame x).symm
      have hg₂_bin : C.gates[g₂].op = GateOp.and ∨ C.gates[g₂].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hg₂)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hg₂_ne_not

      set b' : Bool := if C.gates[g₂].op = GateOp.and then false else true with hb'
      let init' := (initVar m v b', ([] : List Gate))
      let D' := elimDropped m C.gates init'
      have hnc_b' : ∃ x x' : Fin m → Bool,
          circuitFun m C (Function.update x v b') ≠ circuitFun m C (Function.update x' v b') := by
        cases b'
        · obtain ⟨x, x', hne⟩ := hnc0; exact ⟨x, x', by simpa [hf0_eq] using hne⟩
        · obtain ⟨x, x', hne⟩ := hnc1; exact ⟨x, x', by simpa [hf1_eq] using hne⟩
      have hlb_b' : ∀ s' < opt - 2, ¬ HasCircuitSize m (fun x => circuitFun m C (Function.update x v b')) s' := by
        cases b'
        · simpa [← hf0_eq] using hlb0
        · simpa [← hf1_eq] using hlb1
      have hv_st' : ∀ t ≤ C.gates.length,
          (elimState m C.gates init' t).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b' := by
        intro t ht
        rw [elimState_getD_mono m C.gates init' 0 t (v : ℕ) _ (Nat.zero_le _) ht (by simp [init', initVar]),
          elimState_zero]; dsimp only [init']; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
      have hdrop_j₀' : j₀ ∈ D' :=
        mem_elimDropped_of_const m C.gates init' j₀ hj₀ (hnok _ (List.getElem_mem hj₀)) (v : ℕ)
          (by rw [hnot_eq]; simp) ⟨b', hv_st' j₀ (by omega)⟩
      have hst_j₀' : (elimState m C.gates init' (j₀ + 1)).1.getD (m + j₀) (Sum.inl false) = Sum.inl (!b') := by
        have hget := elimState_getD_at m C.gates init' j₀ hj₀
        have hlen : init'.1.length = m := by simp [init', initVar]
        rw [hlen] at hget; rw [hget, hnot_eq]
        simp only [List.map_cons, List.map_nil, hv_st' j₀ (by omega), simplifyGate, simpNot]
      obtain ⟨_, k', hk', hjk', hmem_k', hdrop_k'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b' hnc_b' j₀ hj₀ (!b') hst_j₀'
      have hdrop_g₂' : g₂ ∈ D' :=
        mem_elimDropped_of_const m C.gates init' g₂ hg₂ (hnok _ (List.getElem_mem hg₂)) (v : ℕ)
          hg₂_v ⟨b', hv_st' g₂ (by omega)⟩
      have hst_g₂' : (elimState m C.gates init' (g₂ + 1)).1.getD (m + g₂) (Sum.inl false) = Sum.inl b' := by
        have hget := elimState_getD_at m C.gates init' g₂ hg₂
        have hlen : init'.1.length = m := by simp [init', initVar]
        rw [hlen] at hget; rw [hget]
        have hmem_v' : Sum.inl b' ∈ (C.gates[g₂].inputs.map fun i =>
            (elimState m C.gates init' g₂).1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨(v : ℕ), hg₂_v, hv_st' g₂ (by omega)⟩
        rcases hg₂_bin with hop | hop
        · have hb'f : b' = false := by simp [hb', hop]
          rw [hb'f] at hmem_v' ⊢; rw [hop]
          rw [simplifyGate_and_false _ _ (by simp [(hnok _ (List.getElem_mem hg₂)).1.2]) hmem_v']
        · have hb't : b' = true := by simp [hb', hop]
          rw [hb't] at hmem_v' ⊢; rw [hop]
          rw [simplifyGate_or_true _ _ (by simp [(hnok _ (List.getElem_mem hg₂)).1.2]) hmem_v']
      obtain ⟨_, r', hr', hg₂r', hmem_r', hdrop_r'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b' hnc_b' g₂ hg₂ b' hst_g₂'
      have hg₂_ne_k' : g₂ ≠ k' := fun heq =>
        elim_gate_not_both_a_and_not_a C hnok hred j₀ k' (v : ℕ) hj₀ hk' hjk' (by omega) hnot_eq hmem_k'
          (heq ▸ hg₂_v)
      have hr'_ne_j₀ : r' ≠ j₀ := by
        intro heq; subst heq; rw [hnot_eq] at hmem_r'; simp at hmem_r'; omega
      have hD'_ge4 : 4 ≤ D'.card := by
        by_cases hrk : r' = k'
        · subst hrk

          have hk'_ne_not := elim_not_consumer_ne_not C hnok hred j₀ r' (v : ℕ) hj₀ hk' hjk' (by omega) hnot_eq hmem_k'
          have hk'_bin : C.gates[r'].op = GateOp.and ∨ C.gates[r'].op = GateOp.or := by
            rcases (hnok _ (List.getElem_mem hk')).1.1 with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd h hk'_ne_not
          obtain ⟨u₁, u₂, _, _, hu12, hins_r'⟩ := (reduced_gate_wf C hnok hred r' hr').2 hk'_bin
          have hst_r'_const : ∃ e : Bool,
              (elimState m C.gates init' (r' + 1)).1.getD (m + r') (Sum.inl false) = Sum.inl e := by
            have hget := elimState_getD_at m C.gates init' r' hr'
            have hlen : init'.1.length = m := by simp [init', initVar]
            rw [hlen] at hget; rw [hget, hins_r']
            have h1 : (elimState m C.gates init' r').1.getD (m + j₀) (Sum.inl false) = Sum.inl (!b') := by
              rw [elimState_getD_mono m C.gates init' (j₀ + 1) r' (m + j₀) _ (by omega) (by omega)
                (by simp [init', initVar])]; exact hst_j₀'
            have h2 : (elimState m C.gates init' r').1.getD (m + g₂) (Sum.inl false) = Sum.inl b' := by
              rw [elimState_getD_mono m C.gates init' (g₂ + 1) r' (m + g₂) _ (by omega) (by omega)
                (by simp [init', initVar])]; exact hst_g₂'
            rw [hins_r'] at hmem_k' hmem_r'; simp at hmem_k' hmem_r'
            rcases hmem_k' with hk1 | hk1 <;> rcases hmem_r' with hr1 | hr1
            · exact absurd (hk1.trans hr1.symm) (by omega)
            · rw [← hk1, ← hr1]; simp only [List.map_cons, List.map_nil, h1, h2]
              obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[r'].op _ (!b') b' hk'_bin
              exact ⟨e, by rw [he]⟩
            · rw [← hk1, ← hr1]; simp only [List.map_cons, List.map_nil, h1, h2]
              obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[r'].op _ b' (!b') hk'_bin
              exact ⟨e, by rw [he]⟩
            · exact absurd (hk1.trans hr1.symm) (by omega)
          obtain ⟨e, he⟩ := hst_r'_const
          obtain ⟨_, s', hs', hr's', _, hdrop_s'⟩ :=
            elim_const_not_output_and_consumer C hnok hred v b' hnc_b' r' hr' e he
          have hsub : ({j₀, g₂, r', s'} : Finset ℕ) ⊆ D' := by
            intro u hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> assumption
          have hc4 : ({j₀, g₂, r', s'} : Finset ℕ).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
          exact hc4 ▸ Finset.card_le_card hsub
        · have hsub : ({j₀, g₂, k', r'} : Finset ℕ) ⊆ D' := by
            intro u hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> assumption
          have hc4 : ({j₀, g₂, k', r'} : Finset ℕ).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
          exact hc4 ▸ Finset.card_le_card hsub
      obtain ⟨out', _, _, hcard', hfun'⟩ := elim_var_circuit C hnok v b' hnc_b'
      exact hlb_b' (elimPass m C.gates init').2.length (by
        change (elimPass m C.gates (initVar m v b', [])).2.length < opt - 2
        have : (elimPass m C.gates (initVar m v b', [])).2.length + D'.card = C.gates.length := hcard'
        omega)
        ⟨⟨(elimPass m C.gates init').2, out'⟩, elimPass_ok m C.gates init' (by simp [init']), le_rfl,
          fun x => congrFun hfun' x⟩
    ·
      have hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₀ := by
        intro j hj hmem; by_contra hne; exact hother_v ⟨j, hj, hne, hmem⟩
      have hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀ := by
        intro j hj hop
        by_contra hne
        have hdj : j ∈ D := hdrop_all_not j hj hop
        obtain ⟨aj, cj, haj, hinsj, _, hstj, hnej⟩ :=
          elim_dropped_not_const C hnok hred v b j hj hdj hop
        have haj_ne_v : aj ≠ (v : ℕ) := fun heq =>
          hne (hv_uniq j hj (by rw [hinsj, heq]; simp))
        obtain ⟨hge_aj, hdrop_aj, _⟩ := hnej haj_ne_v
        have haj_ne_j₀ : aj - m ≠ j₀ := by
          intro heq
          have haj_eq : aj = m + j₀ := by omega
          exact elim_not_consumer_ne_not C hnok hred j₀ j (v : ℕ) hj₀ hj (by omega) (by omega) hnot_eq
            (by rw [hinsj, haj_eq]; simp) hop
        obtain ⟨_, kj, hkj, hjkj, hmem_kj, hdrop_kj⟩ :=
          elim_const_not_output_and_consumer C hnok hred v b hnc_b j hj (!cj) hstj
        have hkj_ne_j₀ : kj ≠ j₀ := by
          intro heq; subst heq; rw [hnot_eq] at hmem_kj; simp at hmem_kj; omega
        have hsub : ({j₀, aj - m, j, kj} : Finset ℕ) ⊆ D := by
          intro u hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> assumption
        have hc4 : ({j₀, aj - m, j, kj} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
        have := Finset.card_le_card hsub
        omega
      obtain ⟨x, hx0, hx1⟩ := hinc
      have hanti := single_not_antimono_direct C hnok hred v j₀ hj₀ hnot_eq hnot_uniq hv_uniq x hx1
      rw [hx0] at hanti; exact Bool.noConfusion hanti
  ·
    obtain ⟨hge, hdrop_j₁, hst_j₁⟩ := hne_v hav
    set j₁ := a - m with hj₁_def
    have ha_eq : a = m + j₁ := by omega
    have hj₁ : j₁ < C.gates.length := by omega
    have hD_eq : D = {j₁, j₀, k} := by
      have hsub : ({j₁, j₀, k} : Finset ℕ) ⊆ D := by
        intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
      have hc3 : ({j₁, j₀, k} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    have hnot_eq : C.gates[j₀] = ⟨GateOp.not, [m + j₁]⟩ := by
      cases hg : C.gates[j₀] with
      | mk op ins =>
        rw [hg] at hj₀_op hins; simp only at hj₀_op hins
        subst hj₀_op; subst hins; rw [ha_eq]

    have hk_ne_not : C.gates[k].op ≠ GateOp.not :=
      elim_not_consumer_ne_not C hnok hred j₀ k (m + j₁) hj₀ hk hjk (by omega) hnot_eq hmem_k
    have hj₁_ne_not : C.gates[j₁].op ≠ GateOp.not := by
      intro hop
      obtain ⟨u, hu, hins1⟩ := (reduced_gate_wf C hnok hred j₁ hj₁).1 hop
      have h1_eq : C.gates[j₁] = ⟨GateOp.not, [u]⟩ := by
        cases hg : C.gates[j₁] with
        | mk op ins =>
          rw [hg] at hop hins1; simp only at hop hins1; subst hop; subst hins1; rfl
      exact elim_not_consumer_ne_not C hnok hred j₁ j₀ u hj₁ hj₀ (by omega) hu h1_eq
        (by rw [hnot_eq]; simp) hj₀_op
    have hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀ := by
      intro j hj hop
      have hmem := hdrop_all_not j hj hop
      rw [hD_eq] at hmem; simp at hmem
      rcases hmem with hjeq | hjeq | hjeq
      · subst hjeq; exact absurd hop hj₁_ne_not
      · exact hjeq
      · subst hjeq; exact absurd hop hk_ne_not

    have hk_no_v : (v : ℕ) ∉ C.gates[k].inputs := by
      intro hv_k
      have hk_bin : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hk_ne_not
      obtain ⟨u₁, u₂, _, _, _, hins_k⟩ := (reduced_gate_wf C hnok hred k hk).2 hk_bin
      have hst_k_const : ∃ e : Bool,
          (elimState m C.gates init (k + 1)).1.getD (m + k) (Sum.inl false) = Sum.inl e := by
        have hget := elimState_getD_at m C.gates init k hk
        have hlen : init.1.length = m := by simp [init, initVar]
        rw [hlen] at hget; rw [hget, hins_k]
        have h1 : (elimState m C.gates init k).1.getD (m + j₀) (Sum.inl false) = Sum.inl (!c) := by
          rw [elimState_getD_mono m C.gates init (j₀ + 1) k (m + j₀) _ (by omega) (by omega)
            (by simp [init, initVar])]; exact hst_j₀
        have h2 : (elimState m C.gates init k).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
          rw [elimState_getD_mono m C.gates init 0 k (v : ℕ) _ (Nat.zero_le _) (by omega)
            (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
        rw [hins_k] at hmem_k hv_k; simp at hmem_k hv_k
        rcases hmem_k with hk1 | hk1 <;> rcases hv_k with hv1 | hv1
        · exact absurd (hk1.trans hv1.symm) (by omega)
        · rw [← hk1, ← hv1]; simp only [List.map_cons, List.map_nil, h1, h2]
          obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[k].op _ (!c) b hk_bin
          exact ⟨e, by rw [he]⟩
        · rw [← hk1, ← hv1]; simp only [List.map_cons, List.map_nil, h1, h2]
          obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[k].op _ b (!c) hk_bin
          exact ⟨e, by rw [he]⟩
        · exact absurd (hk1.trans hv1.symm) (by omega)
      obtain ⟨e, he⟩ := hst_k_const
      obtain ⟨_, s', hs', hks', _, hdrop_s'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b hnc_b k hk e he
      have hds' : s' ∈ D := hdrop_s'
      rw [hD_eq] at hds'; simp at hds'; omega

    have hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₁ := by
      intro j hj hmem
      have hdj := hdrop_v j hj hmem
      rw [hD_eq] at hdj; simp at hdj
      rcases hdj with hjeq | hjeq | hjeq
      · exact hjeq
      · subst hjeq; rw [hnot_eq] at hmem; simp at hmem; omega
      · subst hjeq; exact absurd hmem hk_no_v

    have hj₁_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (m + j₁) ∈ C.gates[j].inputs → j = j₀ := by
      intro j hj hmem
      have hlt : j₁ < j := by
        have := reduced_inputs_lt C hnok hred j hj (m + j₁) hmem; omega
      have hdj : j ∈ D := by
        apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (m + j₁) hmem
        refine ⟨c, ?_⟩
        rw [elimState_getD_mono m C.gates init (j₁ + 1) j (m + j₁) _ (by omega) (by omega)
          (by simp [init, initVar]), ← ha_eq]; exact hst_j₁
      rw [hD_eq] at hdj; simp at hdj
      rcases hdj with hjeq | hjeq | hjeq
      · omega
      · exact hjeq
      · subst hjeq
        exact absurd hmem
          (elim_gate_not_both_a_and_not_a C hnok hred j₀ j (m + j₁) hj₀ hj hjk (by omega) hnot_eq hmem_k)
    obtain ⟨x, hx0, hx1⟩ := hinc
    have hanti := single_not_antimono_one C hnok hred v j₁ j₀ hj₁ hj₀ (by omega)
      hv_uniq hnot_eq hnot_uniq hj₁_uniq x hx1
    rw [hx0] at hanti; exact Bool.noConfusion hanti

lemma elim_delta2_d2_extract {m opt : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hsz : C.gates.length ≤ opt + 1)
    (v : Fin m) (b : Bool)
    (hopt_ge2 : 2 ≤ opt)
    (f' : (Fin m → Bool) → Bool)
    (hf'_eq : f' = fun x => circuitFun m C (Function.update x v b))
    (hnc' : ∃ x y : Fin m → Bool, f' x ≠ f' y)
    (hlb' : ∀ s' < opt - 2, ¬ HasCircuitSize m f' s')
    (hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f' →
      D.size ≤ (opt - 2) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (hd2 : (elimDropped m C.gates (initVar m v b, [])).card = 2)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hj₀_op : C.gates[j₀].op = GateOp.not)
    (hnd_j₀ : j₀ ∉ elimDropped m C.gates (initVar m v b, [])) :
    ∃ j₁ : ℕ, ∃ hj₁ : j₁ < C.gates.length,
      (∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀) ∧
      (v : ℕ) ∈ (C.gates[j₁]'hj₁).inputs ∧
      (m + j₀) ∈ (C.gates[j₁]'hj₁).inputs ∧
      (∀ j : ℕ, (hj : j < C.gates.length) → (m + j₀) ∈ C.gates[j].inputs → j = j₁) ∧
      (∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₁) := by
  let init := (initVar m v b, ([] : List Gate))
  let D := elimDropped m C.gates init
  have hnc_upd : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    obtain ⟨x, x', hne⟩ := hnc'; exact ⟨x, x', by simpa [hf'_eq] using hne⟩
  obtain ⟨_, _, _, hcard, _⟩ := elim_var_circuit C hnok v b hnc_upd
  obtain ⟨out, hout_st, _, hout_ne, hdead, huniq_acc⟩ :=
    elim_not_survives_or_dead C hnok v b f' hf'_eq hnc' hlb' hIH' (by change (elimPass m C.gates (initVar m v b, [])).2.length ≤ opt - 2 + 1; omega) j₀ hj₀ hnd_j₀ hj₀_op
  obtain ⟨k, r, hk, hr, c, hj₀k, hkr, hdk, hdr, hst_k, ⟨u, hu_lt, hmem_uk, hst_uk⟩, hmem_kr⟩ :=
    dead_wire_in_elim C hnok hred v b hnc_upd j₀ hj₀ hnd_j₀ out hout_st hout_ne hdead
  change (elimState m C.gates init k).1.getD u (Sum.inl false) =
    Sum.inr (m + (elimState m C.gates init j₀).2.length) at hst_uk
  have hD2 : D.card = 2 := hd2
  have hD_eq : D = {k, r} := by
    have hsub : ({k, r} : Finset ℕ) ⊆ D := by
      intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption
    have hc2 : ({k, r} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

  have hu_eq : u = m + j₀ := by
    by_contra hne
    have hge_m : m ≤ u := by
      by_contra hlt
      have hlt' : u < m := by omega
      have h0 := elimState_getD_mono m C.gates init 0 k u (Sum.inl false) (Nat.zero_le _) (by omega)
        (by simp [init, initVar]; exact hlt')
      rw [h0, elimState_zero] at hst_uk; dsimp only [init] at hst_uk; rw [initVar, ofFn_getD_lt _ _ _ hlt'] at hst_uk
      by_cases hfv : (⟨u, hlt'⟩ : Fin m) = v
      · simp only [hfv, ↓reduceIte] at hst_uk; cases hst_uk
      · simp only [hfv, ↓reduceIte] at hst_uk; have := Sum.inr.inj hst_uk; omega
    set ju := u - m
    have hju_lt : ju < k := by omega
    have hju_ne : ju ≠ j₀ := by omega
    by_cases hnd_u : ju ∉ D
    · obtain ⟨_, _, _, _, _, hst_ju⟩ := elim_emit_at m C.gates init ju (by omega) hnd_u
      have hlen : init.1.length = m := by simp [init, initVar]
      rw [hlen] at hst_ju
      have hmono := elimState_getD_mono m C.gates init (ju + 1) k (m + ju) (Sum.inl false)
        (by omega) (by omega) (by rw [hlen]; omega)
      rw [show m + ju = u by omega] at hmono hst_ju
      rw [← hmono] at hst_ju
      rw [hst_ju] at hst_uk
      have heq_len : (elimState m C.gates init ju).2.length = (elimState m C.gates init j₀).2.length := by
        have h1 := Sum.inr.inj hst_uk
        omega
      exact hju_ne (elim_emit_inj m C.gates init ju j₀ (by omega) hj₀ hnd_u hnd_j₀ heq_len)
    · push Not at hnd_u
      rw [hD_eq] at hnd_u; simp at hnd_u; omega
  subst hu_eq

  have hk_ne_not : C.gates[k].op ≠ GateOp.not := by
    intro hop
    obtain ⟨w, _, hins⟩ := (reduced_gate_wf C hnok hred k hk).1 hop
    rw [hins] at hmem_uk; simp at hmem_uk; subst hmem_uk
    rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdk
    have h2 := hdk.2
    have hst_uk' : (elimState m C.gates (initVar m v b, []) k).1.getD (m + j₀) (Sum.inl false) =
        Sum.inr (m + (elimState m C.gates (initVar m v b, []) j₀).2.length) := hst_uk
    simp only [hk, ↓reduceDIte, hop, hins, List.map_cons, List.map_nil, hst_uk',
      simplifyGate, simpNot] at h2
    exact Bool.noConfusion h2
  have hk_bin : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
    rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hk_ne_not

  obtain ⟨u₁, u₂, hu₁, hu₂, hu12, hins_k⟩ := (reduced_gate_wf C hnok hred k hk).2 hk_bin
  have hv_in_k : (v : ℕ) ∈ C.gates[k].inputs := by
    have hnone_k : (simplifyGate C.gates[k].op (m + (elimState m C.gates init k).2.length)
        [(elimState m C.gates init k).1.getD u₁ (Sum.inl false),
         (elimState m C.gates init k).1.getD u₂ (Sum.inl false)]).1 = none := by
      rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdk
      have h2 := hdk.2
      simp only [hk, ↓reduceDIte, hins_k, List.map_cons, List.map_nil] at h2
      exact Option.isNone_iff_eq_none.1 h2
    have hother_const : ∃ w, w ∈ C.gates[k].inputs ∧ w ≠ m + j₀ ∧
        ∃ c', (elimState m C.gates init k).1.getD w (Sum.inl false) = Sum.inl c' := by
      rw [hins_k] at hmem_uk ⊢; simp at hmem_uk
      rcases hmem_uk with hm1 | hm1
      · rw [← hm1, hst_uk] at hnone_k
        cases hs2 : (elimState m C.gates init k).1.getD u₂ (Sum.inl false) with
        | inl c' => exact ⟨u₂, by simp, fun h => hu12 (hm1.symm.trans h.symm), c', hs2⟩
        | inr _ => rw [hs2] at hnone_k; rcases hk_bin with h | h <;> simp [h, simplifyGate, simpAnd, simpOr] at hnone_k
      · rw [← hm1, hst_uk] at hnone_k
        cases hs1 : (elimState m C.gates init k).1.getD u₁ (Sum.inl false) with
        | inl c' => exact ⟨u₁, by simp, fun h => hu12 (h.trans hm1), c', hs1⟩
        | inr _ => rw [hs1] at hnone_k; rcases hk_bin with h | h <;> simp [h, simplifyGate, simpAnd, simpOr] at hnone_k
    obtain ⟨w, hw_mem, _, c', hst_w⟩ := hother_const
    have hw_lt : w < m + k := reduced_inputs_lt C hnok hred k hk w hw_mem
    have hw_eq_v : w = (v : ℕ) := by
      by_contra hne_v
      by_cases hlt_m : w < m
      · have h0 := elimState_getD_mono m C.gates init 0 k w (Sum.inl false) (Nat.zero_le _) (by omega)
          (by simp [init, initVar]; exact hlt_m)
        rw [h0, elimState_zero] at hst_w; dsimp only [init] at hst_w; rw [initVar, ofFn_getD_lt _ _ _ hlt_m] at hst_w
        have hfin : (⟨w, hlt_m⟩ : Fin m) ≠ v := fun h => hne_v (congrArg Fin.val h)
        simp [hfin] at hst_w
      · set jw := w - m
        have hjw_lt : jw < k := by omega
        have hnd_w : jw ∉ D := by rw [hD_eq]; simp; omega
        obtain ⟨_, _, _, _, _, hst_jw⟩ := elim_emit_at m C.gates init jw (by omega) hnd_w
        have hlen : init.1.length = m := by simp [init, initVar]
        rw [hlen, show m + jw = w by omega] at hst_jw
        have hmono := elimState_getD_mono m C.gates init (jw + 1) k w (Sum.inl false)
          (by omega) (by omega) (by rw [hlen]; omega)
        rw [← hmono] at hst_jw
        rw [hst_jw] at hst_w; cases hst_w
    rwa [← hw_eq_v]

  have hr_ne_not : C.gates[r].op ≠ GateOp.not := by
    intro hop
    obtain ⟨w, _, hins_r⟩ := (reduced_gate_wf C hnok hred r hr).1 hop
    rw [hins_r] at hmem_kr; simp at hmem_kr; subst hmem_kr
    have hst_r : (elimState m C.gates init (r + 1)).1.getD (m + r) (Sum.inl false) = Sum.inl (!c) := by
      have hget := elimState_getD_at m C.gates init r hr
      have hlen : init.1.length = m := by simp [init, initVar]
      rw [hlen] at hget; rw [hget, hop, hins_r]
      have h1 : (elimState m C.gates init r).1.getD (m + k) (Sum.inl false) = Sum.inl c := by
        rw [elimState_getD_mono m C.gates init (k + 1) r (m + k) _ (by omega) (by omega)
          (by rw [hlen]; omega)]; exact hst_k
      simp only [List.map_cons, List.map_nil, h1, simplifyGate, simpNot]
    obtain ⟨_, s', hs', hrs', _, hds'⟩ :=
      elim_const_not_output_and_consumer C hnok hred v b hnc_upd r hr (!c) hst_r
    have hds : s' ∈ D := hds'
    rw [hD_eq] at hds; simp at hds; omega

  have hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀ := by
    intro j hj hop
    by_cases hdj : j ∈ D
    · rw [hD_eq] at hdj; simp at hdj
      rcases hdj with hjeq | hjeq
      · subst hjeq; exact absurd hop hk_ne_not
      · subst hjeq; exact absurd hop hr_ne_not
    · obtain ⟨g', _, hg'op, hklt, hkeq, _⟩ := elim_emit_at m C.gates init j hj hdj
      by_contra hne
      have hne_k : (elimState m C.gates init j).2.length ≠ (elimState m C.gates init j₀).2.length :=
        fun heq => hne (elim_emit_inj m C.gates init j j₀ hj hj₀ hdj hnd_j₀ heq)
      have hne_op := huniq_acc (elimState m C.gates init j).2.length hklt hne_k
      rw [hkeq, hg'op, hop] at hne_op; exact hne_op rfl

  have hj₀_cons_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (m + j₀) ∈ C.gates[j].inputs → j = k := by
    intro j hj hmem_j
    have hj_gt : j₀ < j := by
      have := reduced_inputs_lt C hnok hred j hj (m + j₀) hmem_j; omega
    by_cases hdj : j ∈ D
    · rw [hD_eq] at hdj; simp at hdj
      rcases hdj with hjeq | hjeq
      · exact hjeq
      · exfalso
        subst hjeq
        have hst_j₀_r : (elimState m C.gates init j).1.getD (m + j₀) (Sum.inl false) =
            Sum.inr (m + (elimState m C.gates init j₀).2.length) := by
          obtain ⟨_, _, _, _, _, hst0⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd_j₀
          have hlen : init.1.length = m := by simp [init, initVar]
          rw [hlen] at hst0
          rw [elimState_getD_mono m C.gates init (j₀ + 1) j (m + j₀) _ (by omega) (by omega)
            (by rw [hlen]; omega), hst0]
        cases hstr : (elimState m C.gates init (j + 1)).1.getD (m + j) (Sum.inl false) with
        | inl e =>
          obtain ⟨_, s', hs', hrs', _, hds'⟩ :=
            elim_const_not_output_and_consumer C hnok hred v b hnc_upd j hj e hstr
          have hds : s' ∈ D := hds'
          rw [hD_eq] at hds; simp at hds; omega
        | inr w' =>
          have hget := elimState_getD_at m C.gates init j hj
          have hlen : init.1.length = m := by simp [init, initVar]
          rw [hlen] at hget; rw [hget] at hstr
          have hnone_r : (simplifyGate C.gates[j].op (m + (elimState m C.gates init j).2.length)
              (C.gates[j].inputs.map fun i => (elimState m C.gates init j).1.getD i (Sum.inl false))).1 = none := by
            rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdr
            have h2 := hdr.2; simp only [hj, ↓reduceDIte] at h2
            exact Option.isNone_iff_eq_none.1 h2
          have hmem_ins : Sum.inr (m + (elimState m C.gates init j₀).2.length) ∈
              (C.gates[j].inputs.map fun i => (elimState m C.gates init j).1.getD i (Sum.inl false)) :=
            List.mem_map.2 ⟨m + j₀, hmem_j, hst_j₀_r⟩
          have hw'_eq := simplifyGate_none_of_inr_mem C.gates[j].op _ _
            (hnok _ (List.getElem_mem hj)).1.1 (by simp [(hnok _ (List.getElem_mem hj)).1.2])
            (fun hop => by simp [(hnok _ (List.getElem_mem hj)).2 hop]) hnone_r _ w' hmem_ins hstr
          have hout_ne_r : C.output ≠ m + j := by
            intro heq
            have hacc_r : (elimPass m C.gates init).1.getD (m + j) (Sum.inl false) =
                Sum.inr (m + (elimState m C.gates init j₀).2.length) := by
              rw [← elimState_end,
                elimState_getD_mono m C.gates init (j + 1) C.gates.length (m + j) _ (by omega) le_rfl (by omega),
                hget, hstr, hw'_eq]
            rw [heq, hacc_r] at hout_st
            exact hout_ne (Sum.inr.inj hout_st).symm
          obtain ⟨s', hs', hrs', hmem_rs'⟩ := (reduced_no_dead C hnok hred j hj).resolve_left hout_ne_r
          have hnd_s' : s' ∉ D := by rw [hD_eq]; simp; omega
          obtain ⟨g_s, hg_s, _, hs'_lt, hs'_eq, _⟩ := elim_emit_at m C.gates init s' hs' hnd_s'
          have hlt_s' : (elimState m C.gates init j₀).2.length < (elimState m C.gates init s').2.length := by
            obtain ⟨g0, hg0, _, _, _, _⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd_j₀
            have h1 : (elimState m C.gates init (j₀ + 1)).2.length =
                (elimState m C.gates init j₀).2.length + 1 := by
              rw [elimState_succ m C.gates init j₀ hj₀, elimStep, hg0]; simp
            have h2 := elimState_snd_mono m C.gates init (j₀ + 1) s' (by omega)
            omega
          have hst_rs' : (elimState m C.gates init s').1.getD (m + j) (Sum.inl false) =
              Sum.inr (m + (elimState m C.gates init j₀).2.length) := by
            rw [elimState_getD_mono m C.gates init (j + 1) s' (m + j) _ (by omega) (by omega)
              (by rw [hlen]; omega), hget, hstr, hw'_eq]
          have hmem_ins_s : Sum.inr (m + (elimState m C.gates init j₀).2.length) ∈
              (C.gates[s'].inputs.map fun i => (elimState m C.gates init s').1.getD i (Sum.inl false)) :=
            List.mem_map.2 ⟨m + j, hmem_rs', hst_rs'⟩
          have hmem_gs := simplifyGate_some_mem_inputs C.gates[s'].op _ _
            (fun hop => by simp [(hnok _ (List.getElem_mem hs')).2 hop]) g_s hg_s _ hmem_ins_s
          rw [← hs'_eq] at hmem_gs
          exact hdead _ hs'_lt hlt_s' hmem_gs
    ·
      exfalso
      obtain ⟨g_j, hg_j, _, hj'_lt, hj'_eq, _⟩ := elim_emit_at m C.gates init j hj hdj
      have hlt_j' : (elimState m C.gates init j₀).2.length < (elimState m C.gates init j).2.length := by
        obtain ⟨g0, hg0, _, _, _, _⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd_j₀
        have h1 : (elimState m C.gates init (j₀ + 1)).2.length =
            (elimState m C.gates init j₀).2.length + 1 := by
          rw [elimState_succ m C.gates init j₀ hj₀, elimStep, hg0]; simp
        have h2 := elimState_snd_mono m C.gates init (j₀ + 1) j (by omega)
        omega
      have hst_j₀_j : (elimState m C.gates init j).1.getD (m + j₀) (Sum.inl false) =
          Sum.inr (m + (elimState m C.gates init j₀).2.length) := by
        obtain ⟨_, _, _, _, _, hst0⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd_j₀
        have hlen : init.1.length = m := by simp [init, initVar]
        rw [hlen] at hst0
        rw [elimState_getD_mono m C.gates init (j₀ + 1) j (m + j₀) _ (by omega) (by omega)
          (by rw [hlen]; omega), hst0]
      have hmem_ins_j : Sum.inr (m + (elimState m C.gates init j₀).2.length) ∈
          (C.gates[j].inputs.map fun i => (elimState m C.gates init j).1.getD i (Sum.inl false)) :=
        List.mem_map.2 ⟨m + j₀, hmem_j, hst_j₀_j⟩
      have hmem_gj := simplifyGate_some_mem_inputs C.gates[j].op _ _
        (fun hop => by simp [(hnok _ (List.getElem_mem hj)).2 hop]) g_j hg_j _ hmem_ins_j
      rw [← hj'_eq] at hmem_gj
      exact hdead _ hj'_lt hlt_j' hmem_gj

  have hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = k := by
    intro j hj hmem_v
    have hdj : j ∈ D := by
      apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hmem_v
      refine ⟨b, ?_⟩
      rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
        (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
    rw [hD_eq] at hdj; simp at hdj
    rcases hdj with hjeq | hjeq
    · exact hjeq
    · exfalso
      subst hjeq
      have hr_bin : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hj)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hr_ne_not
      obtain ⟨w₁, w₂, _, _, _, hins_r⟩ := (reduced_gate_wf C hnok hred j hj).2 hr_bin
      have hst_r_const : ∃ e : Bool,
          (elimState m C.gates init (j + 1)).1.getD (m + j) (Sum.inl false) = Sum.inl e := by
        have hget := elimState_getD_at m C.gates init j hj
        have hlen : init.1.length = m := by simp [init, initVar]
        rw [hlen] at hget; rw [hget, hins_r]
        have h1 : (elimState m C.gates init j).1.getD (m + k) (Sum.inl false) = Sum.inl c := by
          rw [elimState_getD_mono m C.gates init (k + 1) j (m + k) _ (by omega) (by omega)
            (by rw [hlen]; omega)]; exact hst_k
        have h2 : (elimState m C.gates init j).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
          rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
            (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
        rw [hins_r] at hmem_kr hmem_v; simp at hmem_kr hmem_v
        rcases hmem_kr with hk1 | hk1 <;> rcases hmem_v with hv1 | hv1
        · exact absurd (hk1.trans hv1.symm) (by omega)
        · rw [← hk1, ← hv1]; simp only [List.map_cons, List.map_nil, h1, h2]
          obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[j].op _ c b hr_bin
          exact ⟨e, by rw [he]⟩
        · rw [← hk1, ← hv1]; simp only [List.map_cons, List.map_nil, h1, h2]
          obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[j].op _ b c hr_bin
          exact ⟨e, by rw [he]⟩
        · exact absurd (hk1.trans hv1.symm) (by omega)
      obtain ⟨e, he⟩ := hst_r_const
      obtain ⟨_, s', hs', hrs', _, hds'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b hnc_upd j hj e he
      have hds : s' ∈ D := hds'
      rw [hD_eq] at hds; simp at hds; omega
  exact ⟨k, hk, hnot_uniq, hv_in_k, hmem_uk, hj₀_cons_uniq, hv_uniq⟩

lemma elim_delta2_leaf {m opt : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hsz : C.gates.length ≤ opt + 1)
    (v : Fin m)
    (hinc : ∃ x : Fin m → Bool,
      circuitFun m C (Function.update x v false) = false ∧
      circuitFun m C (Function.update x v true) = true)
    (hopt_ge2 : 2 ≤ opt)
    (f0 f1 : (Fin m → Bool) → Bool)
    (hf0_eq : f0 = fun x => circuitFun m C (Function.update x v false))
    (hf1_eq : f1 = fun x => circuitFun m C (Function.update x v true))
    (hnc0 : ∃ x y : Fin m → Bool, f0 x ≠ f0 y)
    (hnc1 : ∃ x y : Fin m → Bool, f1 x ≠ f1 y)
    (hlb0 : ∀ s' < opt - 2, ¬ HasCircuitSize m f0 s')
    (hlb1 : ∀ s' < opt - 2, ¬ HasCircuitSize m f1 s')
    (hIH0 : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f0 →
      D.size ≤ (opt - 2) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (hIH1 : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f1 →
      D.size ≤ (opt - 2) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hj₀_op : C.gates[j₀].op = GateOp.not) :
    ∃ j_n j₁ : ℕ, ∃ (_hjn : j_n < C.gates.length) (hj₁ : j₁ < C.gates.length),
      (∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j_n) ∧
      (v : ℕ) ∈ (C.gates[j₁]'hj₁).inputs ∧
      (m + j_n) ∈ (C.gates[j₁]'hj₁).inputs ∧
      (∀ j : ℕ, (hj : j < C.gates.length) → (m + j_n) ∈ C.gates[j].inputs → j = j₁) := by
  classical
  have hnc_upd0 : ∃ x x', circuitFun m C (Function.update x v false) ≠ circuitFun m C (Function.update x' v false) := by
    obtain ⟨x, x', hne⟩ := hnc0; exact ⟨x, x', by simpa [hf0_eq] using hne⟩
  have hnc_upd1 : ∃ x x', circuitFun m C (Function.update x v true) ≠ circuitFun m C (Function.update x' v true) := by
    obtain ⟨x, x', hne⟩ := hnc1; exact ⟨x, x', by simpa [hf1_eq] using hne⟩
  have hdrop_bound : ∀ b : Bool, (elimDropped m C.gates (initVar m v b, [])).card ≤ 2 := by
    intro b
    have hncb : ∃ x x', circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
      cases b <;> assumption
    obtain ⟨out, _, _, hcard, hfun⟩ := elim_var_circuit C hnok v b hncb
    have hge : opt - 2 ≤ (elimPass m C.gates (initVar m v b, [])).2.length := by
      by_contra hlt
      have hcs : HasCircuitSize m (if b then f1 else f0) (elimPass m C.gates (initVar m v b, [])).2.length :=
        ⟨⟨(elimPass m C.gates (initVar m v b, [])).2, out⟩, elimPass_ok m C.gates _ (by simp), le_rfl,
          fun x => by cases b <;> simp [hf0_eq, hf1_eq] <;> exact congrFun hfun x⟩
      cases b
      · exact hlb0 _ (by omega) hcs
      · exact hlb1 _ (by omega) hcs
    have hle3 : (elimDropped m C.gates (initVar m v b, [])).card ≤ 3 := by omega
    by_contra hgt2
    have hd3 : (elimDropped m C.gates (initVar m v b, [])).card = 3 := by omega
    exact elim_delta2_d3_contra C hnok hred hsz v b hinc hopt_ge2 f0 f1 hf0_eq hf1_eq
      hnc0 hnc1 hlb0 hlb1 (by cases b <;> assumption) hd3 j₀ hj₀ hj₀_op
  have hfrom_d2 : ∀ b : Bool, (elimDropped m C.gates (initVar m v b, [])).card = 2 →
      ∃ j_n j₁ : ℕ, ∃ (_hjn : j_n < C.gates.length) (hj₁ : j₁ < C.gates.length),
        (∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j_n) ∧
        (v : ℕ) ∈ (C.gates[j₁]'hj₁).inputs ∧
        (m + j_n) ∈ (C.gates[j₁]'hj₁).inputs ∧
        (∀ j : ℕ, (hj : j < C.gates.length) → (m + j_n) ∈ C.gates[j].inputs → j = j₁) := by
    intro b hd2
    let init := (initVar m v b, ([] : List Gate))
    let D := elimDropped m C.gates init
    have hncb : ∃ x x', circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
      cases b <;> assumption
    by_cases hnd : j₀ ∉ D
    · obtain ⟨j₁, hj₁, huniq, hv1, hj01, hcons1, _⟩ :=
        elim_delta2_d2_extract C hnok hred hsz v b hopt_ge2 (if b then f1 else f0)
          (by cases b <;> simp [hf0_eq, hf1_eq]) (by cases b <;> assumption)
          (by cases b <;> assumption) (by cases b <;> assumption) hd2 j₀ hj₀ hj₀_op hnd
      exact ⟨j₀, j₁, hj₀, hj₁, huniq, hv1, hj01, hcons1⟩
    · exfalso
      push Not at hnd
      obtain ⟨a, c, ha, hins, _, hst_j₀, hne_v⟩ :=
        elim_dropped_not_const C hnok hred v b j₀ hj₀ hnd hj₀_op
      obtain ⟨_, k, hk, hjk, hmem_k, hdrop_k⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b hncb j₀ hj₀ (!c) hst_j₀
      have ha_eq_v : a = (v : ℕ) := by
        by_contra hne
        obtain ⟨_, hdrop_am, _⟩ := hne_v hne
        have hsub : ({a - m, j₀, k} : Finset ℕ) ⊆ D := by
          intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
        have hc3 : ({a - m, j₀, k} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
        have : ({a - m, j₀, k} : Finset ℕ).card ≤ D.card := Finset.card_le_card hsub
        have hd2' : D.card = 2 := hd2
        omega
      have hnot_eq : C.gates[j₀] = ⟨GateOp.not, [(v : ℕ)]⟩ := by
        cases hg : C.gates[j₀] with
        | mk op ins =>
          rw [hg] at hj₀_op hins; simp only at hj₀_op hins
          subst hj₀_op; subst hins; subst ha_eq_v; rfl
      have hk_ne_not := elim_not_consumer_ne_not C hnok hred j₀ k (v : ℕ) hj₀ hk hjk (by omega) hnot_eq hmem_k
      have hk_bin : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hk_ne_not
      set b' : Bool := if C.gates[k].op = GateOp.and then true else false with hb'
      let init' := (initVar m v b', ([] : List Gate))
      let D' := elimDropped m C.gates init'
      have hncb' : ∃ x x', circuitFun m C (Function.update x v b') ≠ circuitFun m C (Function.update x' v b') := by
        cases b' <;> assumption
      have hv_st' : (elimState m C.gates init' j₀).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b' := by
        rw [elimState_getD_mono m C.gates init' 0 j₀ (v : ℕ) _ (Nat.zero_le _) (by omega)
          (by simp [init', initVar]), elimState_zero]; dsimp only [init']; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
      have hdrop_j₀' : j₀ ∈ D' :=
        mem_elimDropped_of_const m C.gates init' j₀ hj₀ (hnok _ (List.getElem_mem hj₀)) (v : ℕ)
          (by rw [hnot_eq]; simp) ⟨b', hv_st'⟩
      have hst_j₀' : (elimState m C.gates init' (j₀ + 1)).1.getD (m + j₀) (Sum.inl false) = Sum.inl (!b') := by
        have hget := elimState_getD_at m C.gates init' j₀ hj₀
        have hlen : init'.1.length = m := by simp [init', initVar]
        rw [hlen] at hget; rw [hget, hnot_eq]
        simp only [List.map_cons, List.map_nil, hv_st', simplifyGate, simpNot]
      have hdrop_k' : k ∈ D' := by
        apply mem_elimDropped_of_const m C.gates init' k hk (hnok _ (List.getElem_mem hk)) (m + j₀) hmem_k
        refine ⟨!b', ?_⟩
        rw [elimState_getD_mono m C.gates init' (j₀ + 1) k (m + j₀) _ (by omega) (by omega)
          (by simp [init', initVar])]; exact hst_j₀'
      have hst_k' : (elimState m C.gates init' (k + 1)).1.getD (m + k) (Sum.inl false) = Sum.inl (!b') := by
        have hget := elimState_getD_at m C.gates init' k hk
        have hlen : init'.1.length = m := by simp [init', initVar]
        rw [hlen] at hget; rw [hget]
        have h1 : (elimState m C.gates init' k).1.getD (m + j₀) (Sum.inl false) = Sum.inl (!b') := by
          rw [elimState_getD_mono m C.gates init' (j₀ + 1) k (m + j₀) _ (by omega) (by omega)
            (by simp [init', initVar])]; exact hst_j₀'
        have hmem_ins : Sum.inl (!b') ∈ (C.gates[k].inputs.map fun i =>
            (elimState m C.gates init' k).1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨m + j₀, hmem_k, h1⟩
        rcases hk_bin with hop | hop
        · have hb't : b' = true := by simp [hb', hop]
          rw [hb't] at hmem_ins ⊢; simp only [Bool.not_true] at hmem_ins ⊢; rw [hop]
          rw [simplifyGate_and_false _ _ (by simp [(hnok _ (List.getElem_mem hk)).1.2]) hmem_ins]
        · have hb'f : b' = false := by simp [hb', hop]
          rw [hb'f] at hmem_ins ⊢; simp only [Bool.not_false] at hmem_ins ⊢; rw [hop]
          rw [simplifyGate_or_true _ _ (by simp [(hnok _ (List.getElem_mem hk)).1.2]) hmem_ins]
      obtain ⟨_, r', hr', hkr', _, hdrop_r'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b' hncb' k hk (!b') hst_k'
      have hsub : ({j₀, k, r'} : Finset ℕ) ⊆ D' := by
        intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
      have hc3 : ({j₀, k, r'} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have hge3 : 3 ≤ D'.card := hc3 ▸ Finset.card_le_card hsub
      have hle2 : D'.card ≤ 2 := hdrop_bound b'
      omega
  have hex_v : ∃ g₁ : ℕ, ∃ hg₁ : g₁ < C.gates.length, (v : ℕ) ∈ C.gates[g₁].inputs := by
    by_contra hno
    push Not at hno
    obtain ⟨x, hx0, hx1⟩ := hinc
    have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hout := hred.2.2.1 hne
    have heq := wire_indep_of_not_read C v hno C.gates.length le_rfl C.output (by omega) (by omega) x
    change circuitFun m C (Function.update x v false) = circuitFun m C (Function.update x v true) at heq
    rw [hx0, hx1] at heq; exact Bool.noConfusion heq
  obtain ⟨g₁, hg₁, hg₁_v⟩ := hex_v
  set b : Bool := if C.gates[g₁].op = GateOp.or then true else false with hb
  let init := (initVar m v b, ([] : List Gate))
  let D := elimDropped m C.gates init
  have hncb : ∃ x x', circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    cases b <;> assumption
  have hv_st : (elimState m C.gates init g₁).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
    rw [elimState_getD_mono m C.gates init 0 g₁ (v : ℕ) _ (Nat.zero_le _) (by omega)
      (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
  have hdrop_g₁ : g₁ ∈ D :=
    mem_elimDropped_of_const m C.gates init g₁ hg₁ (hnok _ (List.getElem_mem hg₁)) (v : ℕ) hg₁_v ⟨b, hv_st⟩
  have hst_g₁_const : ∃ c : Bool,
      (elimState m C.gates init (g₁ + 1)).1.getD (m + g₁) (Sum.inl false) = Sum.inl c := by
    have hget := elimState_getD_at m C.gates init g₁ hg₁
    have hlen : init.1.length = m := by simp [init, initVar]
    rw [hlen] at hget; rw [hget]
    have hmem_ins : Sum.inl b ∈ (C.gates[g₁].inputs.map fun i =>
        (elimState m C.gates init g₁).1.getD i (Sum.inl false)) :=
      List.mem_map.2 ⟨(v : ℕ), hg₁_v, hv_st⟩
    rcases (hnok _ (List.getElem_mem hg₁)).1.1 with hop | hop | hop
    · have hbf : b = false := by simp [hb, hop]
      rw [hbf] at hmem_ins; rw [hop]
      exact ⟨false, by rw [simplifyGate_and_false _ _ (by simp [(hnok _ (List.getElem_mem hg₁)).1.2]) hmem_ins]⟩
    · have hbt : b = true := by simp [hb, hop]
      rw [hbt] at hmem_ins; rw [hop]
      exact ⟨true, by rw [simplifyGate_or_true _ _ (by simp [(hnok _ (List.getElem_mem hg₁)).1.2]) hmem_ins]⟩
    · obtain ⟨u, _, hins⟩ := (reduced_gate_wf C hnok hred g₁ hg₁).1 hop
      rw [hins] at hg₁_v; simp at hg₁_v; subst hg₁_v
      rw [hop, hins]; exact ⟨!b, by simp only [List.map_cons, List.map_nil, hv_st, simplifyGate, simpNot]⟩
  obtain ⟨c, hc⟩ := hst_g₁_const
  obtain ⟨_, k, hk, hg₁k, _, hdrop_k⟩ :=
    elim_const_not_output_and_consumer C hnok hred v b hncb g₁ hg₁ c hc
  have hsub : ({g₁, k} : Finset ℕ) ⊆ D := by
    intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
  have hc2 : ({g₁, k} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have hge2 : 2 ≤ D.card := hc2 ▸ Finset.card_le_card hsub
  have hle2 : D.card ≤ 2 := hdrop_bound b
  exact hfrom_d2 b (by change D.card = 2; omega)

lemma base_single_A {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hA : A = {a}) (hnoE : ∀ u v : Fin n, ¬ K.Adj u v)
    (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hfun : circuitFun n C = forestFun0 K A) (hsz : C.gates.length ≤ 1)
    (hred : Reduced n C) :
    ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  intro g hg hop
  have hlen1 : C.gates.length = 1 := by
    have hpos : 0 < C.gates.length := List.length_pos_of_mem hg
    omega
  have hg0 : C.gates[0]'(by omega) = g := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have : j = 0 := by omega
    subst this; rfl
  have hout : C.output = n + 0 := by
    have := hred.2.2.1 (List.ne_nil_of_length_pos (by omega)); omega
  obtain ⟨u, hu, hins⟩ := (reduced_gate_wf C hnok hred 0 (by omega)).1 (by rw [hg0]; exact hop)
  have h0 : circuitFun n C (fun _ => false) = true := by
    show (C.wires (List.ofFn (fun _ : Fin n => false))).getD C.output false = true
    rw [hout, wire_eval_gate C 0 (by omega), hins, hg0, hop]
    have hwu : (C.wires (List.ofFn (fun _ : Fin n => false))).getD u false = false := by
      show (wiresFrom C.gates _).getD u false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]
    simp only [hu, ↓reduceIte, hwu, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_false]
  rw [hfun, forestFun0_false] at h0
  exact Bool.noConfusion h0

lemma base_single_edge {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (u v : Fin n) (huv : K.Adj u v) (hE1 : K.edgeFinset.card = 1)
    (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hfun : circuitFun n C = forestFun0 K ∅) (hsz : C.gates.length ≤ 2)
    (hred : Reduced n C) :
    ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  have hfun_uv : ∀ x : Fin n → Bool, forestFun0 K ∅ x = (x u && x v) := by
    intro x
    simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or]
    cases hxu : x u <;> cases hxv : x v <;> simp only [Bool.and_false, Bool.false_and, Bool.and_true]
    · simp only [decide_eq_false_iff_not]; rintro ⟨a, b, hab, hxa, hxb⟩
      have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 (show K.edgeFinset.card ≤ 1 by omega) s(a, b)
        (SimpleGraph.mem_edgeFinset.2 hab) s(u, v) (SimpleGraph.mem_edgeFinset.2 huv)
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hxu, hxv] at hxa hxb
    · simp only [decide_eq_false_iff_not]; rintro ⟨a, b, hab, hxa, hxb⟩
      have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 (show K.edgeFinset.card ≤ 1 by omega) s(a, b)
        (SimpleGraph.mem_edgeFinset.2 hab) s(u, v) (SimpleGraph.mem_edgeFinset.2 huv)
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hxu, hxv] at hxa hxb
    · simp only [decide_eq_false_iff_not]; rintro ⟨a, b, hab, hxa, hxb⟩
      have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 (show K.edgeFinset.card ≤ 1 by omega) s(a, b)
        (SimpleGraph.mem_edgeFinset.2 hab) s(u, v) (SimpleGraph.mem_edgeFinset.2 huv)
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hxu, hxv] at hxa hxb
    · simp only [decide_eq_true_eq]; exact ⟨u, v, huv, hxu, hxv⟩
  intro g hg hop
  obtain ⟨j₀, hj₀, rfl⟩ := List.getElem_of_mem hg
  have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hout := hred.2.2.1 hne
  have hin_val : ∀ (x : Fin n → Bool) (i : ℕ) (hi : i < n),
      (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    show (wiresFrom C.gates _).getD i false = _
    rw [wiresFrom_getD_lt _ _ _ (by simp; exact hi), ofFn_getD_lt _ _ _ hi]
  by_cases hlen1 : C.gates.length = 1
  · have hj0 : j₀ = 0 := by omega
    subst hj0
    obtain ⟨a, ha, hins⟩ := (reduced_gate_wf C hnok hred 0 hj₀).1 hop
    have h0 : circuitFun n C (fun _ => false) = true := by
      show (C.wires _).getD C.output false = true
      rw [show C.output = n + 0 by omega, wire_eval_gate C 0 hj₀, hop, hins]
      simp only [ha, ↓reduceIte, hin_val _ a (by omega), GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_false]
    rw [hfun, forestFun0_false] at h0; exact Bool.noConfusion h0
  · have hlen2 : C.gates.length = 2 := by omega
    have hout2 : C.output = n + 1 := by omega
    by_cases hj1 : j₀ = 1
    · subst hj1
      obtain ⟨a, ha, hins1⟩ := (reduced_gate_wf C hnok hred 1 hj₀).1 hop

      have ha_eq : a = n + 0 := by
        obtain ⟨k, hk, h0k, hmem⟩ := (reduced_no_dead C hnok hred 0 (by omega)).resolve_left (by omega)
        have : k = 1 := by omega
        subst this; rw [hins1] at hmem; simp at hmem; exact hmem.symm

      have hw0 : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + 0) false = !(x u && x v) := by
        intro x
        have hev := congrFun hfun x
        rw [hfun_uv x] at hev
        change (C.wires (List.ofFn x)).getD C.output false = (x u && x v) at hev
        rw [hout2, wire_eval_gate C 1 hj₀ x, hop, hins1, ha_eq] at hev
        simp only [show n + 0 < n + 1 by omega, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
          List.headD_cons] at hev
        rw [← hev, Bool.not_not]

      rcases (hnok _ (List.getElem_mem (show 0 < C.gates.length by omega))).1.1 with hop0 | hop0 | hop0
      · obtain ⟨p, q, hp, hq, _, hins0⟩ := (reduced_gate_wf C hnok hred 0 (by omega)).2 (Or.inl hop0)
        have h0 := hw0 (fun _ => false)
        rw [wire_eval_gate C 0 (by omega), hop0, hins0] at h0
        simp only [hp, hq, ↓reduceIte, hin_val _ p (by omega), hin_val _ q (by omega), GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_false, Bool.false_and, Bool.or_false, Bool.not_false] at h0; exact Bool.noConfusion h0
      · obtain ⟨p, q, hp, hq, _, hins0⟩ := (reduced_gate_wf C hnok hred 0 (by omega)).2 (Or.inr hop0)
        have h0 := hw0 (fun _ => false)
        rw [wire_eval_gate C 0 (by omega), hop0, hins0] at h0
        simp only [hp, hq, ↓reduceIte, hin_val _ p (by omega), hin_val _ q (by omega), GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_false, Bool.false_and, Bool.or_false, Bool.not_false] at h0; exact Bool.noConfusion h0
      · obtain ⟨p, hp, hins0⟩ := (reduced_gate_wf C hnok hred 0 (by omega)).1 hop0
        let fp : Fin n := ⟨p, by omega⟩
        have hval0 : ∀ x : Fin n → Bool, (!(x fp)) = !(x u && x v) := by
          intro x
          have h := hw0 x
          rw [wire_eval_gate C 0 (by omega) x, hop0, hins0] at h
          simpa only [hp, ↓reduceIte, hin_val x p (by omega), GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] using h
        by_cases hpu : fp = u
        · have h := hval0 (fun i => decide (i = u))
          simp [hpu, huv.ne.symm] at h
        · have h := hval0 (fun i => decide (i = fp))
          have hufp : u ≠ fp := Ne.symm hpu
          simp [hufp] at h
    ·
      have hj0 : j₀ = 0 := by omega
      subst hj0
      obtain ⟨p, hp, hins0⟩ := (reduced_gate_wf C hnok hred 0 hj₀).1 hop
      have h0_eq : C.gates[0] = ⟨GateOp.not, [p]⟩ := by
        cases hg0 : C.gates[0] with
        | mk op ins => rw [hg0] at hop hins0; simp only at hop hins0; subst hop; subst hins0; rfl
      obtain ⟨k, hk, h0k, hmem1⟩ := (reduced_no_dead C hnok hred 0 hj₀).resolve_left (by omega)
      have hk1 : k = 1 := by omega
      subst hk1
      have h1_ne_not := elim_not_consumer_ne_not C hnok hred 0 1 p hj₀ hk (by omega) hp h0_eq hmem1
      have h1_bin : C.gates[1].op = GateOp.and ∨ C.gates[1].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h h1_ne_not
      obtain ⟨a, b, ha, hb, hab, hins1⟩ := (reduced_gate_wf C hnok hred 1 hk).2 h1_bin
      have hval : ∀ x : Fin n → Bool,
          (C.wires (List.ofFn x)).getD n false = !(x ⟨p, by omega⟩) := by
        intro x
        have h := wire_eval_gate C 0 hj₀ x
        rw [Nat.add_zero, h0_eq] at h
        rw [h]
        simp only [show p < n by omega, ↓reduceIte, hin_val x p (by omega), GateOp.eval,
          List.map_cons, List.map_nil, List.headD_cons]
      rcases h1_bin with hop1 | hop1
      · have ht := congrFun hfun (fun _ => true)
        rw [hfun_uv] at ht
        change (C.wires _).getD C.output false = true at ht
        rw [hout2, wire_eval_gate C 1 hk, hop1, hins1] at ht
        rw [hins1] at hmem1; simp only [Nat.add_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem1
        rcases hmem1 with hm | hm
        · rw [← hm] at ht
          simp only [show n < n + 1 by omega, hb, ↓reduceIte, hval, GateOp.eval, List.map_cons,
            List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.not_true, Bool.false_and] at ht
          exact Bool.noConfusion ht
        · rw [← hm] at ht
          simp only [ha, show n < n + 1 by omega, ↓reduceIte, hval, GateOp.eval, List.map_cons,
            List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.not_true, Bool.false_and,
            Bool.and_false] at ht
          exact Bool.noConfusion ht
      · have hf := congrFun hfun (fun _ => false)
        rw [hfun_uv] at hf
        change (C.wires _).getD C.output false = false at hf
        rw [hout2, wire_eval_gate C 1 hk, hop1, hins1] at hf
        rw [hins1] at hmem1; simp only [Nat.add_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem1
        rcases hmem1 with hm | hm
        · rw [← hm] at hf
          simp only [show n < n + 1 by omega, hb, ↓reduceIte, hval, GateOp.eval, List.map_cons,
            List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.not_false, Bool.true_or] at hf
          exact Bool.noConfusion hf
        · rw [← hm] at hf
          simp only [ha, show n < n + 1 by omega, ↓reduceIte, hval, GateOp.eval, List.map_cons,
            List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.not_false, Bool.true_or,
            Bool.or_true] at hf
          exact Bool.noConfusion hf

lemma no_not_in_forest :
    ∀ (sz : ℕ) {n t : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
      (C : Circuit),
      A.card + 2 * K.edgeFinset.card = sz →
      K.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) →
      (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) →
      HasMinVC K t →
      (∀ g ∈ C.gates, NOkGate g) →
      circuitFun n C = forestFun0 K A →
      C.size ≤ A.card + K.edgeFinset.card + t →
      Reduced n C →
      ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  intro sz
  induction sz using Nat.strong_induction_on with
  | _ sz ih =>
    intro n t K _ A C hsz_eq hAcyc hA_iso hne hvc hnok hfun hCsz hred
    have hsz_pos : 1 ≤ A.card + K.edgeFinset.card := by
      rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
      · have := Finset.one_le_card.2 ⟨a, ha⟩; omega
      · have := Finset.one_le_card.2 ⟨s(u, v), SimpleGraph.mem_edgeFinset.2 huv⟩; omega
    by_cases hbase : A.card + K.edgeFinset.card = 1
    · by_cases hAne : A.Nonempty
      · obtain ⟨a, ha⟩ := hAne
        have hA1 : A.card = 1 := by
          have := Finset.one_le_card.2 ⟨a, ha⟩; omega
        have hAeq : A = {a} := Finset.card_eq_one.1 hA1 |> fun ⟨a', ha'⟩ => by
          rw [ha'] at ha; simp at ha; subst ha; exact ha'
        have hE0 : K.edgeFinset.card = 0 := by omega
        have hnoE : ∀ u v : Fin n, ¬ K.Adj u v := by
          intro u v huv
          have := Finset.one_le_card.2 ⟨s(u, v), SimpleGraph.mem_edgeFinset.2 huv⟩; omega
        have ht0 : t = 0 := hasMinVC_empty K hnoE hvc
        exact base_single_A K A a hAeq hnoE C hnok hfun (by simpa [Circuit.size, hA1, hE0, ht0] using hCsz) hred
      · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
        subst hA0
        obtain ⟨u, v, huv⟩ := hne.resolve_left (by simp)
        have hE1 : K.edgeFinset.card = 1 := by simp at hbase; exact hbase
        have ht1 : t = 1 := by
          have hge1 : 1 ≤ t := by
            obtain ⟨⟨S, hS, hSc⟩, _⟩ := hvc
            rcases hS u v huv with hu | hv
            · have := Finset.one_le_card.2 ⟨u, hu⟩; omega
            · have := Finset.one_le_card.2 ⟨v, hv⟩; omega
          have hle1 : t ≤ 1 := by
            have hvc_u : IsVC K {u} := by
              intro a b hab
              have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 (show K.edgeFinset.card ≤ 1 by omega) s(a, b)
                (SimpleGraph.mem_edgeFinset.2 hab) s(u, v) (SimpleGraph.mem_edgeFinset.2 huv)
              rw [Sym2.eq_iff] at heq
              rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
            simpa using hvc.2 {u} hvc_u
          omega
        exact base_single_edge K u v huv hE1 C hnok hfun
          (by simpa [Circuit.size, hE1, ht1] using hCsz) hred
    ·
      have hge2 : 2 ≤ A.card + K.edgeFinset.card := by omega
      set opt := A.card + K.edgeFinset.card + t - 1 with hopt_def
      have hopt_pos : 1 ≤ opt := by omega
      have hCsz' : C.gates.length ≤ opt + 1 := by
        show C.size ≤ opt + 1; omega
      intro g hg hop
      obtain ⟨j₀, hj₀, rfl⟩ := List.getElem_of_mem hg
      by_cases hAne : A.Nonempty
      ·
        obtain ⟨a, ha⟩ := hAne
        have hcardA : (A.erase a).card + 1 = A.card := by
          have := Finset.one_le_card.2 ⟨a, ha⟩
          rw [Finset.card_erase_of_mem ha]; omega
        have hne' : (A.erase a).Nonempty ∨ ∃ u v : Fin n, K.Adj u v := by
          by_cases hA2 : 2 ≤ A.card
          · left; exact Finset.card_pos.1 (by omega)
          · right
            have hEpos : 0 < K.edgeFinset.card := by omega
            obtain ⟨e, he⟩ := Finset.card_pos.1 hEpos
            induction e using Sym2.ind with
            | _ u v => exact ⟨u, v, SimpleGraph.mem_edgeFinset.1 he⟩
        have hA'_iso : ∀ b ∈ A.erase a, ∀ v : Fin n, ¬ K.Adj b v :=
          fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)
        have hrew := forestFun0_update_A K A a (hA_iso a ha)
        have hinc : ∃ x, circuitFun n C (Function.update x a false) = false ∧
            circuitFun n C (Function.update x a true) = true := by
          rw [hfun]; exact forestFun0_inc_A K A a ha
        have hlb' : ∀ s' < opt - 1, ¬ HasCircuitSize n (forestFun0 K (A.erase a)) s' := by
          intro s' hs' hcs
          have := forest_lower_bound s' K (A.erase a) hAcyc hA'_iso hne' hvc hcs
          omega
        have hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
            circuitFun n D = forestFun0 K (A.erase a) →
            D.size ≤ (opt - 1) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
          intro D hDnok hDfun hDsz hDred
          exact ih ((A.erase a).card + 2 * K.edgeFinset.card) (by omega) K (A.erase a) D rfl
            hAcyc hA'_iso hne' hvc hDnok hDfun (by omega) hDred
        exact elim_delta1_contra C hnok hred hCsz' a false hinc (forestFun0 K (A.erase a))
          (by rw [hfun]; exact hrew.symm) (forestFun0_nonconst K (A.erase a) hne')
          hlb' hopt_pos hIH' j₀ hj₀ hop
      ·
        have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
        subst hA0
        have hEge2 : 2 ≤ K.edgeFinset.card := by simp at hge2; exact hge2
        have hEdge : ∃ u v : Fin n, K.Adj u v := hne.resolve_left (by simp)
        by_cases hsib : ∃ ℓ ℓ' p : Fin n, ℓ' ≠ ℓ ∧ K.Adj ℓ p ∧ (∀ w, K.Adj ℓ w → w = p) ∧
            K.Adj ℓ' p ∧ (∀ w, K.Adj ℓ' w → w = p)
        ·
          classical
          obtain ⟨ℓ, ℓ', p, hℓ'ne, hlp, hleaf, hℓ'p, hℓ'leaf⟩ := hsib
          obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (K.deleteEdges {s(ℓ, p)})
          have ht₁ : t₁ = t := hasMinVC_deleteLeafEdge_eq K ℓ ℓ' p hℓ'ne hℓ'p hℓ'leaf hvc hvc₁
          have hedge := edgeFinset_card_deleteEdge K ℓ p hlp
          have hne' : (∅ : Finset (Fin n)).Nonempty ∨ ∃ u v, (K.deleteEdges {s(ℓ, p)}).Adj u v := by
            right; refine ⟨ℓ', p, SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, ?_⟩⟩
            simp only [Set.mem_singleton_iff, Sym2.eq_iff]
            rintro (⟨h1, _⟩ | ⟨_, h2⟩)
            · exact hℓ'ne h1
            · exact hlp.ne h2.symm
          have hrew := forestFun0_update_leaf_false K ℓ p hleaf
          have hinc : ∃ x, circuitFun n C (Function.update x ℓ false) = false ∧
              circuitFun n C (Function.update x ℓ true) = true := by
            rw [hfun]; exact forestFun0_inc_edge K ∅ (by simp) ℓ p hlp
          have hlb' : ∀ s' < opt - 1, ¬ HasCircuitSize n (forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅) s' := by
            intro s' hs' hcs
            have := forest_lower_bound s' (K.deleteEdges {s(ℓ, p)}) ∅
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne' hvc₁ hcs
            simp only [Finset.card_empty, zero_add] at this hopt_def; omega
          have hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
              circuitFun n D = forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅ →
              D.size ≤ (opt - 1) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
            intro D hDnok hDfun hDsz hDred
            exact ih ((∅ : Finset (Fin n)).card + 2 * (K.deleteEdges {s(ℓ, p)}).edgeFinset.card)
              (by simp at hsz_eq ⊢; omega) (K.deleteEdges {s(ℓ, p)}) ∅ D rfl
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne' hvc₁ hDnok hDfun
              (by simp only [Finset.card_empty, zero_add] at hopt_def ⊢; omega) hDred
          exact elim_delta1_contra C hnok hred hCsz' ℓ false hinc
            (forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅) (by rw [hfun]; exact hrew.symm)
            (forestFun0_nonconst (K.deleteEdges {s(ℓ, p)}) ∅ hne') hlb' hopt_pos hIH' j₀ hj₀ hop
        · by_cases hiso : ∃ ℓ p : Fin n, K.Adj ℓ p ∧ (∀ w, K.Adj ℓ w → w = p) ∧ (∀ w, K.Adj p w → w = ℓ)
          ·
            classical
            obtain ⟨ℓ, p, hlp, hleaf, hpdeg1⟩ := hiso
            obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges K p)
            have ht' : t' + 1 = t := hasMinVC_deleteVertex K ℓ p hlp hleaf hvc hvc'
            have hedge := edgeFinset_card_deleteVertex_deg1 K ℓ p hlp hpdeg1
            have hne' : ({p} : Finset (Fin n)).Nonempty ∨ ∃ u v, (deleteVertexEdges K p).Adj u v :=
              Or.inl (Finset.singleton_nonempty p)
            have hp_iso : ∀ a ∈ ({p} : Finset (Fin n)), ∀ v : Fin n, ¬ (deleteVertexEdges K p).Adj a v := by
              intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl
            have hrew := forestFun0_update_leaf_true K ℓ p hlp hleaf
            have hinc : ∃ x, circuitFun n C (Function.update x ℓ false) = false ∧
                circuitFun n C (Function.update x ℓ true) = true := by
              rw [hfun]; exact forestFun0_inc_edge K ∅ (by simp) ℓ p hlp
            have hlb' : ∀ s' < opt - 1, ¬ HasCircuitSize n (forestFun0 (deleteVertexEdges K p) {p}) s' := by
              intro s' hs' hcs
              have := forest_lower_bound s' (deleteVertexEdges K p) {p}
                (hAcyc.anti (deleteVertexEdges_le K p)) hp_iso hne' hvc' hcs
              simp only [Finset.card_singleton, Finset.card_empty, zero_add] at this hopt_def; omega
            have hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
                circuitFun n D = forestFun0 (deleteVertexEdges K p) {p} →
                D.size ≤ (opt - 1) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
              intro D hDnok hDfun hDsz hDred
              exact ih (({p} : Finset (Fin n)).card + 2 * (deleteVertexEdges K p).edgeFinset.card)
                (by simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hsz_eq ⊢; omega)
                (deleteVertexEdges K p) {p} D rfl
                (hAcyc.anti (deleteVertexEdges_le K p)) hp_iso hne' hvc' hDnok hDfun
                (by simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hopt_def ⊢; omega) hDred
            exact elim_delta1_contra C hnok hred hCsz' ℓ true hinc
              (forestFun0 (deleteVertexEdges K p) {p}) (by rw [hfun]; exact hrew.symm)
              (forestFun0_nonconst (deleteVertexEdges K p) {p} hne') hlb' hopt_pos hIH' j₀ hj₀ hop
          ·
            classical
            obtain ⟨ℓ₁, p₁, q₁, ℓ₂, p₂, q₂, h12ne,
              h1p, h1leaf, hq1ne, hp1q1, hp1deg2,
              h2p, h2leaf, hq2ne, hp2q2, hp2deg2⟩ :=
              acyclic_two_deg2_leaves K hAcyc hEdge hsib hiso
            have hopt_ge2 : 2 ≤ opt := by
              have ht_pos : 1 ≤ t := by
                obtain ⟨⟨S, hS, hSc⟩, _⟩ := hvc
                rcases hS ℓ₁ p₁ h1p with h1 | h2
                · have := Finset.one_le_card.2 ⟨ℓ₁, h1⟩; omega
                · have := Finset.one_le_card.2 ⟨p₁, h2⟩; omega
              simp only [Finset.card_empty, zero_add] at hopt_def; omega
            have hleaf_res : ∀ (ℓ p q : Fin n),
                K.Adj ℓ p → (∀ w, K.Adj ℓ w → w = p) → q ≠ ℓ → K.Adj p q →
                (∀ w, K.Adj p w → w = ℓ ∨ w = q) →
                ∃ j_n j₁ : ℕ, ∃ (_hjn : j_n < C.gates.length) (hj₁ : j₁ < C.gates.length),
                  (∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j_n) ∧
                  (ℓ : ℕ) ∈ (C.gates[j₁]'hj₁).inputs ∧
                  (n + j_n) ∈ (C.gates[j₁]'hj₁).inputs ∧
                  (∀ j : ℕ, (hj : j < C.gates.length) → (n + j_n) ∈ C.gates[j].inputs → j = j₁) := by
              intro ℓ p q hlp hleaf hqne hpq hpdeg2
              obtain ⟨t₀, hvc₀⟩ := hasMinVC_exists (K.deleteEdges {s(ℓ, p)})
              have ht₀ := hasMinVC_deleteEdge K ℓ p hvc hvc₀
              have hedge₀ := edgeFinset_card_deleteEdge K ℓ p hlp
              obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (deleteVertexEdges K p)
              have ht₁ : t₁ + 1 = t := hasMinVC_deleteVertex K ℓ p hlp hleaf hvc hvc₁
              have hedge₁ := edgeFinset_card_deleteVertex_deg2 K ℓ p q hlp hpq hqne hpdeg2
              have hne₀ : (∅ : Finset (Fin n)).Nonempty ∨ ∃ u v, (K.deleteEdges {s(ℓ, p)}).Adj u v := by
                right; refine ⟨p, q, SimpleGraph.deleteEdges_adj.2 ⟨hpq, ?_⟩⟩
                simp only [Set.mem_singleton_iff, Sym2.eq_iff]
                rintro (⟨h1, _⟩ | ⟨_, h2⟩)
                · exact hlp.ne h1.symm
                · exact hqne h2
              have hne₁ : ({p} : Finset (Fin n)).Nonempty ∨ ∃ u v, (deleteVertexEdges K p).Adj u v :=
                Or.inl (Finset.singleton_nonempty p)
              have hp_iso : ∀ a ∈ ({p} : Finset (Fin n)), ∀ v : Fin n, ¬ (deleteVertexEdges K p).Adj a v := by
                intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl
              have hrew0 := forestFun0_update_leaf_false K ℓ p hleaf
              have hrew1 := forestFun0_update_leaf_true K ℓ p hlp hleaf
              have hinc : ∃ x, circuitFun n C (Function.update x ℓ false) = false ∧
                  circuitFun n C (Function.update x ℓ true) = true := by
                rw [hfun]; exact forestFun0_inc_edge K ∅ (by simp) ℓ p hlp
              have hlb0 : ∀ s' < opt - 2, ¬ HasCircuitSize n (forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅) s' := by
                intro s' hs' hcs
                have := forest_lower_bound s' (K.deleteEdges {s(ℓ, p)}) ∅
                  (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne₀ hvc₀ hcs
                simp only [Finset.card_empty, zero_add] at this hopt_def; omega
              have hlb1 : ∀ s' < opt - 2, ¬ HasCircuitSize n (forestFun0 (deleteVertexEdges K p) {p}) s' := by
                intro s' hs' hcs
                have := forest_lower_bound s' (deleteVertexEdges K p) {p}
                  (hAcyc.anti (deleteVertexEdges_le K p)) hp_iso hne₁ hvc₁ hcs
                simp only [Finset.card_singleton, Finset.card_empty, zero_add] at this hopt_def; omega
              have hIH0 : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
                  circuitFun n D = forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅ →
                  D.size ≤ (opt - 2) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
                intro D hDnok hDfun hDsz hDred
                exact ih ((∅ : Finset (Fin n)).card + 2 * (K.deleteEdges {s(ℓ, p)}).edgeFinset.card)
                  (by simp only [Finset.card_empty, zero_add] at hsz_eq ⊢; omega)
                  (K.deleteEdges {s(ℓ, p)}) ∅ D rfl
                  (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne₀ hvc₀ hDnok hDfun
                  (by simp only [Finset.card_empty, zero_add] at hopt_def ⊢; omega) hDred
              have hIH1 : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
                  circuitFun n D = forestFun0 (deleteVertexEdges K p) {p} →
                  D.size ≤ (opt - 2) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
                intro D hDnok hDfun hDsz hDred
                exact ih (({p} : Finset (Fin n)).card + 2 * (deleteVertexEdges K p).edgeFinset.card)
                  (by simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hsz_eq ⊢; omega)
                  (deleteVertexEdges K p) {p} D rfl
                  (hAcyc.anti (deleteVertexEdges_le K p)) hp_iso hne₁ hvc₁ hDnok hDfun
                  (by simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hopt_def ⊢; omega) hDred
              exact elim_delta2_leaf C hnok hred hCsz' ℓ hinc hopt_ge2
                (forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅) (forestFun0 (deleteVertexEdges K p) {p})
                (by rw [hfun]; exact hrew0.symm) (by rw [hfun]; exact hrew1.symm)
                (forestFun0_nonconst _ _ hne₀) (forestFun0_nonconst _ _ hne₁)
                hlb0 hlb1 hIH0 hIH1 j₀ hj₀ hop
            obtain ⟨jn₁, j₁, hjn₁, hj₁, huniq₁, hℓ1_in, hjn1_in, hcons₁⟩ :=
              hleaf_res ℓ₁ p₁ q₁ h1p h1leaf hq1ne hp1q1 hp1deg2
            obtain ⟨jn₂, j₂, hjn₂, hj₂, huniq₂, hℓ2_in, hjn2_in, hcons₂⟩ :=
              hleaf_res ℓ₂ p₂ q₂ h2p h2leaf hq2ne hp2q2 hp2deg2
            have hjneq : jn₁ = jn₂ := (huniq₂ j₀ hj₀ hop).symm.trans (huniq₁ j₀ hj₀ hop) |> Eq.symm
            subst hjneq
            have hj12 : j₁ = j₂ := (hcons₂ j₁ hj₁ hjn1_in)
            subst hj12

            have hlen2 := (hnok _ (List.getElem_mem hj₁)).1.2
            rcases hins : C.gates[j₁].inputs with _ | ⟨w₁, _ | ⟨w₂, _ | ⟨w₃, l⟩⟩⟩
            · rw [hins] at hℓ1_in; simp at hℓ1_in
            · rw [hins] at hℓ1_in hjn1_in; simp at hℓ1_in hjn1_in; omega
            · rw [hins] at hℓ1_in hℓ2_in hjn1_in; simp at hℓ1_in hℓ2_in hjn1_in
              rcases hjn1_in with rfl | rfl
              · have h1 : (ℓ₁ : ℕ) = w₂ := hℓ1_in.resolve_left (by omega)
                have h2 : (ℓ₂ : ℕ) = w₂ := hℓ2_in.resolve_left (by omega)
                exact h12ne (Fin.ext (h1.trans h2.symm))
              · have h1 : (ℓ₁ : ℕ) = w₁ := hℓ1_in.resolve_right (by omega)
                have h2 : (ℓ₂ : ℕ) = w₁ := hℓ2_in.resolve_right (by omega)
                exact h12ne (Fin.ext (h1.trans h2.symm))
            · rw [hins] at hlen2; simp at hlen2

theorem forest_no_not : ∀ (n t : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), K.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) → (∀ i : Fin n, i ∈ A ∨ ∃ v : Fin n, K.Adj i v) → (∃ S : Finset (Fin n), K.IsVertexCover (S : Set (Fin n)) ∧ S.card = t) → (∀ S : Finset (Fin n), K.IsVertexCover (S : Set (Fin n)) → t ≤ S.card) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)) → C.size ≤ A.card + K.edgeFinset.card + t → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true) → ∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  intro n t K _ A C hAcyc hA_iso hne _ hex_vc hmin_vc hfan hfun hCsz hred g hg
  set C' : Circuit := ⟨C.gates.map normGate, C.output⟩ with hC'
  have hnok' : ∀ g' ∈ C'.gates, NOkGate g' := by
    intro g' hg'
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg'
    exact normGate_nok g0 (hfan g0 hg0)
  have hfun' : circuitFun n C' = forestFun0 K A := by
    have hfeq : forestFun0 K A = circuitFun n C := hfun.symm
    rw [hfeq]; funext x
    show (wiresFrom (C.gates.map normGate) (List.ofFn x)).getD C.output false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    rw [wiresFrom_norm]
  have hsz' : C'.size ≤ A.card + K.edgeFinset.card + t := by
    simpa [Circuit.size, hC'] using hCsz
  have hred' : Reduced n C' := reduced_norm n C hred
  have hvc : HasMinVC K t := by
    refine ⟨?_, ?_⟩
    · obtain ⟨S, hS, hSc⟩ := hex_vc
      exact ⟨S, (isVertexCover_iff_isVC K S).1 hS, hSc⟩
    · intro S hS
      exact hmin_vc S ((isVertexCover_iff_isVC K S).2 hS)
  have hnoNot := no_not_in_forest (A.card + 2 * K.edgeFinset.card) K A C' rfl
    hAcyc hA_iso hne hvc hnok' hfun' hsz' hred'
  have hg' : normGate g ∈ C'.gates := List.mem_map.2 ⟨g, hg, rfl⟩
  have hne_not := hnoNot (normGate g) hg'
  intro hop
  apply hne_not
  rcases g with ⟨op, ins⟩
  simp only at hop
  subst hop
  rfl
end PEqualNP.Outside.L_meta_173_aux.NoNot

namespace PEqualNP.Outside.L_meta_173_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem binary_gate (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hr : NoNot.Reduced n C) (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) ∧
    ∃ a b, a < n + j ∧ b < n + j ∧ a ≠ b ∧ C.gates[j].inputs = [a,b] := by
  have hnk : ∀ g ∈ C.gates, NoNot.NOkGate g := by
    intro g hg
    exact ⟨hf g hg, fun h => False.elim (hn g hg h)⟩
  have hop := (hf _ (List.getElem_mem hj)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hab : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
    rcases hop with ha | ho | hnot
    · exact Or.inl ha
    · exact Or.inr ho
    · exact False.elim (hn _ (List.getElem_mem hj) hnot)
  exact ⟨hab, (NoNot.reduced_gate_wf C hnk hr j hj).2 hab⟩

def parentWire (C : Circuit) (j : Fin C.size) (p : Bool) : ℕ :=
  (C.gates[j.val]'j.isLt).inputs.getD (if p then 1 else 0) 0

theorem parentWire_lt (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hr : NoNot.Reduced n C) (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not)
    (j : Fin C.size) (p : Bool) : parentWire C j p < n + j.val := by
  obtain ⟨_, a, b, ha, hb, _, hins⟩ := binary_gate n C hf hr hn j.val j.isLt
  cases p <;> simp [parentWire, hins] <;> assumption

theorem parentWire_ne (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hr : NoNot.Reduced n C) (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not)
    (j : Fin C.size) : parentWire C j false ≠ parentWire C j true := by
  obtain ⟨_, a, b, _, _, hab, hins⟩ := binary_gate n C hf hr hn j.val j.isLt
  simpa [parentWire, hins] using hab

theorem gate_eval_binary (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hr : NoNot.Reduced n C) (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not)
    (j : Fin C.size) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n+j.val) false =
      match (C.gates[j.val]'j.isLt).op with
      | GateOp.and => ((C.wires (List.ofFn x)).getD (parentWire C j false) false &&
         (C.wires (List.ofFn x)).getD (parentWire C j true) false)
      | _ => ((C.wires (List.ofFn x)).getD (parentWire C j false) false ||
         (C.wires (List.ofFn x)).getD (parentWire C j true) false) := by
  obtain ⟨hop, a, b, ha, hb, _, hins⟩ := binary_gate n C hf hr hn j.val j.isLt
  rw [NoNot.wire_eval_gate C j.val j.isLt x]
  rcases hop with hop | hop <;> simp [hop, hins, parentWire, GateOp.eval, ha, hb]

end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

structure Net (n m : ℕ) where
  src : Fin m → Bool → Fin (n+m)
  lt_src : ∀ j b, (src j b).val < n+j.val
  ne_src : ∀ j, src j false ≠ src j true
  isAnd : Fin m → Bool

namespace Net
variable {n m : ℕ}
abbrev Wire (n m : ℕ) := Fin (n+m)
def raw (i : Fin n) : Wire n m := ⟨i, by omega⟩
def site (j : Fin m) : Wire n m := ⟨n+j, by omega⟩
def ports (D : Net n m) (w : Wire n m) : Finset (Fin m × Bool) :=
  Finset.univ.filter fun p => D.src p.1 p.2 = w
def deg (D : Net n m) (w : Wire n m) : ℕ := (D.ports w).card

theorem deg_total (D : Net n m) : ∑ w, D.deg w = 2*m := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin m × Bool)))
    (t := (Finset.univ : Finset (Wire n m))) (f := fun p => D.src p.1 p.2)
    (fun _ _ => Finset.mem_univ _)
  simpa [deg, ports, Nat.mul_comm] using h.symm

def combine (D : Net n m) (j : Fin m) (a b : Bool) : Bool :=
  if D.isAnd j then a && b else a || b

def eval (D : Net n m) (x : Fin n → Bool) (cut : Wire n m → Option Bool)
    (w : Wire n m) : Bool :=
  match cut w with
  | some b => b
  | none =>
    if h : w.val < n then x ⟨w.val,h⟩ else
      let j : Fin m := ⟨w.val-n, by have := w.isLt; omega⟩
      D.combine j (D.eval x cut (D.src j false)) (D.eval x cut (D.src j true))
termination_by w.val
decreasing_by
  all_goals
    have hj : n+j.val=w.val := by dsimp [j]; omega
    first | exact (D.lt_src j false).trans_eq hj | exact (D.lt_src j true).trans_eq hj

theorem eval_raw (D : Net n m) (x : Fin n → Bool) (cut : Wire n m → Option Bool)
    (i : Fin n) (h : cut (raw i) = none) : D.eval x cut (raw i) = x i := by
  rw [eval, h]
  simp [raw]

theorem eval_site (D : Net n m) (x : Fin n → Bool) (cut : Wire n m → Option Bool)
    (j : Fin m) (h : cut (site j) = none) : D.eval x cut (site j) =
      D.combine j (D.eval x cut (D.src j false)) (D.eval x cut (D.src j true)) := by
  rw [eval, h]
  simp [site]

theorem eval_cut (D : Net n m) (x : Fin n → Bool) (cut : Wire n m → Option Bool)
    (w : Wire n m) (b : Bool) (h : cut w = some b) : D.eval x cut w = b := by
  rw [eval, h]

theorem cases_wire (w : Wire n m) : (∃ i : Fin n, w = raw i) ∨ (∃ j : Fin m, w = site j) := by
  by_cases h : w.val < n
  · exact Or.inl ⟨⟨w.val,h⟩,rfl⟩
  · exact Or.inr ⟨⟨w.val-n,by have := w.isLt; omega⟩, Fin.ext (by dsimp [site]; omega)⟩

theorem induction_wire (D : Net n m) {P : Wire n m → Prop} (hin : ∀ i, P (raw i))
    (hgate : ∀ j, P (D.src j false) → P (D.src j true) → P (site j))
    (w : Wire n m) : P w := by
  induction w using (measure (fun w : Wire n m => w.val)).wf.induction with
  | h w ih =>
    rcases cases_wire w with ⟨i,rfl⟩ | ⟨j,rfl⟩
    · exact hin i
    · exact hgate j (ih _ (D.lt_src j false)) (ih _ (D.lt_src j true))

end Net

def circuitNet (n : ℕ) (C : Circuit) (hf : FanInTwo C) (hr : NoNot.Reduced n C)
    (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not) : Net n C.size where
  src j p := ⟨parentWire C j p, by have := parentWire_lt n C hf hr hn j p; have := j.isLt; omega⟩
  lt_src := parentWire_lt n C hf hr hn
  ne_src j h := parentWire_ne n C hf hr hn j (congrArg Fin.val h)
  isAnd j := match (C.gates[j.val]'j.isLt).op with | .and => true | _ => false

theorem circuitNet_eval (n : ℕ) (C : Circuit) (hf : FanInTwo C) (hr : NoNot.Reduced n C)
    (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not) (x : Fin n → Bool) (w : Net.Wire n C.size) :
    (circuitNet n C hf hr hn).eval x (fun _ => none) w =
      (C.wires (List.ofFn x)).getD w.val false := by
  induction w using (circuitNet n C hf hr hn).induction_wire with
  | hin i =>
    rw [Net.eval_raw _ _ _ _ rfl]
    change x i = (NoNot.wiresFrom C.gates (List.ofFn x)).getD i.val false
    rw [NoNot.wiresFrom_getD_lt _ _ _ (by simp), NoNot.ofFn_getD_lt _ _ _ i.isLt]
  | hgate j h0 h1 =>
    rw [Net.eval_site _ _ _ _ rfl, h0, h1]
    change _ = (C.wires (List.ofFn x)).getD (n+j.val) false
    rw [gate_eval_binary n C hf hr hn j x]
    obtain ⟨hop,_⟩ := binary_gate n C hf hr hn j.val j.isLt
    rcases hop with hop|hop <;> simp [Net.combine,circuitNet,hop]

end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux.Net
variable {n m : ℕ}

inductive Path (D : Net n m) (s : Wire n m) : Wire n m → Type where
  | refl : Path D s s
  | step (j : Fin m) (p : Bool) : Path D s (D.src j p) → Path D s (site j)

namespace Path
variable {D : Net n m} {s w : Wire n m}

def edges : {w : Wire n m} → Path D s w → Finset (Fin m × Bool)
  | _, .refl => ∅
  | _, .step j b rest => insert (j,b) rest.edges

def nodes : {w : Wire n m} → Path D s w → Finset (Wire n m)
  | _, .refl => {s}
  | _, .step j _ rest => insert (site j) rest.nodes

theorem self_mem (p : Path D s w) : w ∈ p.nodes := by
  cases p <;> simp [nodes]

theorem start_mem (p : Path D s w) : s ∈ p.nodes := by
  induction p with
  | refl => simp [nodes]
  | step _ _ _ ih => simp [nodes,ih]

theorem node_le {z : Wire n m} (p : Path D s w) (hz : z ∈ p.nodes) :
    z.val ≤ w.val := by
  induction p with
  | refl => simpa [nodes] using (Finset.mem_singleton.mp hz).le
  | step j b q ih =>
    simp only [nodes, Finset.mem_insert] at hz
    rcases hz with rfl|hh
    · rfl
    · exact (ih hh).trans (D.lt_src j b).le

theorem src_mem {e : Fin m × Bool} (p : Path D s w) (he : e ∈ p.edges) :
    D.src e.1 e.2 ∈ p.nodes := by
  induction p with
  | refl => simp [edges] at he
  | step j b q ih =>
    simp only [edges,Finset.mem_insert] at he
    rcases he with rfl|hh
    · exact Finset.mem_insert_of_mem q.self_mem
    · exact Finset.mem_insert_of_mem (ih hh)

theorem dst_mem {e : Fin m × Bool} (p : Path D s w) (he : e ∈ p.edges) :
    site e.1 ∈ p.nodes := by
  induction p with
  | refl => simp [edges] at he
  | step j b q ih =>
    simp only [edges,Finset.mem_insert] at he
    rcases he with rfl|hh
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (ih hh)

theorem has_out {z : Wire n m} (p : Path D s w) (hz : z ∈ p.nodes) (hne : z ≠ w) :
    ∃ e ∈ p.edges, D.src e.1 e.2 = z := by
  induction p with
  | refl => exact (hne (Finset.mem_singleton.mp hz)).elim
  | step j b q ih =>
    have hz' : z ∈ q.nodes := (Finset.mem_insert.mp hz).resolve_left hne
    by_cases h : z = D.src j b
    · exact ⟨(j,b), Finset.mem_insert_self _ _, h.symm⟩
    · obtain ⟨e,he,hs⟩ := ih hz' h
      exact ⟨e,Finset.mem_insert_of_mem he,hs⟩

theorem has_in {z : Wire n m} (p : Path D s w) (hz : z ∈ p.nodes) (hne : z ≠ s) :
    ∃ e ∈ p.edges, site e.1 = z := by
  induction p with
  | refl => exact (hne (Finset.mem_singleton.mp hz)).elim
  | step j b q ih =>
    rcases Finset.mem_insert.mp hz with rfl|hz'
    · exact ⟨(j,b), Finset.mem_insert_self _ _, rfl⟩
    · obtain ⟨e,he,hs⟩ := ih hz'
      exact ⟨e,Finset.mem_insert_of_mem he,hs⟩

theorem outgoing_unique (p : Path D s w) {e f : Fin m × Bool} (he : e ∈ p.edges)
    (hf : f ∈ p.edges) (hs : D.src e.1 e.2 = D.src f.1 f.2) : e = f := by
  induction p with
  | refl => simp [edges] at he
  | step j b q ih =>
    rcases Finset.mem_insert.mp he with rfl|he' <;> rcases Finset.mem_insert.mp hf with rfl|hf'
    · rfl
    · have hl := q.node_le (q.dst_mem hf')
      have lt := D.lt_src f.1 f.2
      change n + f.1.val ≤ (D.src j b).val at hl
      rw [←hs] at lt
      exact (Nat.not_lt_of_ge hl lt).elim
    · have hl := q.node_le (q.dst_mem he')
      have lt := D.lt_src e.1 e.2
      change n + e.1.val ≤ (D.src j b).val at hl
      rw [hs] at lt
      exact (Nat.not_lt_of_ge hl lt).elim
    · exact ih he' hf'

end Path

theorem combine_witness (D : Net n m) (j : Fin m) (x y : Bool → Bool)
    (hx : D.combine j (x false) (x true) = true)
    (hy : D.combine j (y false) (y true) = false) : ∃ b, x b = true ∧ y b = false := by
  cases ha : D.isAnd j <;> cases h0 : x false <;> cases h1 : x true <;>
    cases k0 : y false <;> cases k1 : y true <;>
    simp_all [combine, Bool.exists_bool]

theorem trace (D : Net n m) (x y : Fin n → Bool) (cut : Wire n m → Option Bool)
    (w : Wire n m) (hx : D.eval x cut w = true) (hy : D.eval y cut w = false) :
    ∃ i : Fin n, ∃ p : Path D (raw i) w,
      ∀ z ∈ p.nodes, D.eval x cut z = true ∧ D.eval y cut z = false ∧ cut z = none := by
  induction w using D.induction_wire with
  | hin i =>
    have hn : cut (raw i) = none := by
      cases hc : cut (raw i) with
      | none => rfl
      | some b => rw [eval_cut _ _ _ _ _ hc] at hx hy; simp_all
    exact ⟨i,.refl,fun z hz => by obtain rfl := Finset.mem_singleton.mp hz; exact ⟨hx,hy,hn⟩⟩
  | hgate j ih0 ih1 =>
    have hn : cut (site j) = none := by
      cases hc : cut (site j) with
      | none => rfl
      | some b => rw [eval_cut _ _ _ _ _ hc] at hx hy; simp_all
    obtain ⟨b,hb,kb⟩ := D.combine_witness j (fun b => D.eval x cut (D.src j b))
      (fun b => D.eval y cut (D.src j b)) (by rwa [←eval_site _ _ _ _ hn])
      (by rwa [←eval_site _ _ _ _ hn])
    obtain ⟨i,p,hp⟩ := (by cases b <;> first | exact ih0 hb kb | exact ih1 hb kb :
      ∃ i, ∃ p : Path D (raw i) (D.src j b),
        ∀ z ∈ p.nodes, D.eval x cut z = true ∧ D.eval y cut z = false ∧ cut z = none)
    refine ⟨i,.step j b p,fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl|hh
    · exact ⟨hx,hy,hn⟩
    · exact hp z hh

end PEqualNP.Outside.L_meta_173_aux.Net

namespace PEqualNP.Outside.L_meta_173_aux.Net
variable {n m : ℕ} {D : Net n m}

def onlyExit (D : Net n m) (j : Fin m) (b : Bool) : Prop :=
  ∀ e : Fin m × Bool, D.src e.1 e.2 = D.src j b → e = (j,b)

theorem onlyExit_of_deg {j : Fin m} {b : Bool} (h : D.deg (D.src j b) = 1) :
    D.onlyExit j b := by
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp h
  have hj : (j,b) ∈ D.ports (D.src j b) := by simp [ports]
  rw [he] at hj
  intro f hf
  have hm : f ∈ D.ports (D.src j b) := by simp [ports,hf]
  rw [he] at hm
  exact (Finset.mem_singleton.mp hm).trans (Finset.mem_singleton.mp hj).symm

inductive Line (D : Net n m) (s : Wire n m) : Wire n m → Type where
  | first : Line D s s
  | step (j : Fin m) (b : Bool) (q : Line D s (D.src j b)) (hu : D.onlyExit j b) :
      Line D s (site j)

namespace Line
variable {s w : Wire n m}

def masks : {w : Wire n m} → Line D s w → Finset (Wire n m)
  | _, .first => ∅
  | _, .step j b q _ => if D.isAnd j then insert (D.src j (!b)) q.masks else q.masks

theorem dominates (q : Line D s w) {z : Wire n m} (p : Path D s z) (hle : w.val ≤ z.val) :
    w ∈ p.nodes := by
  induction q with
  | first => exact p.start_mem
  | step j b q hu ih =>
    have hl := D.lt_src j b
    have hw := ih (hl.le.trans hle)
    obtain ⟨e,he,hes⟩ := p.has_out hw (fun h => by
      have := congrArg Fin.val h
      change n+j.val ≤ z.val at hle
      omega)
    have heq := hu e hes
    subst e
    exact p.dst_mem he

theorem sibling_unreachable {j : Fin m} {b : Bool} (q : Line D s (D.src j b))
    (hu : D.onlyExit j b) (p : Path D s (D.src j (!b))) : False := by
  let whole := Path.step j (!b) p
  have h := q.dominates whole (D.lt_src j b).le
  have hn : D.src j b ≠ site j := fun hh => (D.lt_src j b).ne (congrArg Fin.val hh)
  have hp := (Finset.mem_insert.mp h).resolve_left hn
  have hd : D.src j b ≠ D.src j (!b) := by cases b <;> simpa using (by
    first | exact D.ne_src j | exact (D.ne_src j).symm)
  obtain ⟨f,hf,hs⟩ := p.has_out hp hd
  obtain rfl := hu f hs
  have hl := p.node_le (p.dst_mem hf)
  exact Nat.not_lt_of_ge hl (D.lt_src j (!b))

theorem masks_unreachable (q : Line D s w) {h : Wire n m} (hh : h ∈ q.masks)
    (p : Path D s h) : False := by
  induction q with
  | first => simp [masks] at hh
  | step j b q hu ih =>
    cases ha : D.isAnd j <;> simp [masks,ha] at hh
    · exact ih hh
    · rcases hh with rfl|hk
      · exact sibling_unreachable q hu p
      · exact ih hk

theorem until_fork (q : Line D s w) :
    ∃ v : Wire n m, ∃ q' : Line D s v, D.deg v ≠ 1 := by
  classical
  induction w using (measure (fun w : Wire n m => n+m-w.val)).wf.induction with
  | h w ih =>
    by_cases hh : D.deg w = 1
    · obtain ⟨e,he⟩ := Finset.card_eq_one.mp hh
      have hm : e ∈ D.ports w := by rw [he]; simp
      have hw : D.src e.1 e.2 = w := (Finset.mem_filter.mp hm).2
      rcases e with ⟨j,b⟩
      subst w
      apply ih (site j) _ (Line.step j b q (onlyExit_of_deg hh))
      have hl := D.lt_src j b
      have hj := j.isLt
      change n+m-(n+j.val) < n+m-(D.src j b).val
      omega
    · exact ⟨w,q,hh⟩

end Line

def force (w : Wire n m) : Wire n m → Option Bool := fun z => if z=w then some true else none

theorem eval_eq_of_nopath (D : Net n m) (cut : Wire n m → Option Bool)
    (i : Fin n) (x y : Fin n → Bool) (hagr : ∀ k ≠ i, x k = y k) (w : Wire n m)
    (hn : ∀ p : Path D (raw i) w, ∃ z ∈ p.nodes, cut z ≠ none) :
    D.eval x cut w = D.eval y cut w := by
  have hle (a b : Fin n → Bool) (ha : ∀ k ≠ i, a k = b k)
      (ht : D.eval a cut w = true) (hf : D.eval b cut w = false) : False := by
    obtain ⟨k,p,hp⟩ := D.trace a b cut w ht hf
    have ⟨h1,h2,h3⟩ := hp _ p.start_mem
    rw [eval_raw _ _ _ _ h3] at h1 h2
    have hki : k=i := by by_contra hne; rw [ha _ hne,h2] at h1; contradiction
    subst k
    obtain ⟨z,hz,hh⟩ := hn p
    exact hh (hp _ hz).2.2
  cases hx : D.eval x cut w <;> cases hy : D.eval y cut w
  · rfl
  · exact (hle y x (fun k hk => (hagr k hk).symm) hy hx).elim
  · exact (hle x y hagr hx hy).elim
  · rfl

theorem owner_independent {i : Fin n} {w z : Wire n m} (q : Line D (raw i) w)
    (hz : w.val ≤ z.val) (x y : Fin n → Bool) (h : ∀ k ≠ i, x k = y k) :
    D.eval x (force w) z = D.eval y (force w) z :=
  D.eval_eq_of_nopath _ i x y h z fun p =>
    ⟨w,q.dominates p hz,by simp [force]⟩

theorem mask_independent {i : Fin n} {w v : Wire n m} (q : Line D (raw i) w)
    (hv : v ∈ q.masks) (x y : Fin n → Bool) (h : ∀ k ≠ i, x k = y k) :
    D.eval x (fun _ => none) v = D.eval y (fun _ => none) v :=
  D.eval_eq_of_nopath _ i x y h v fun p => (q.masks_unreachable hv p).elim

end PEqualNP.Outside.L_meta_173_aux.Net

namespace PEqualNP.Outside.L_meta_173_aux.Net
variable {n m : ℕ} {D : Net n m}

abbrev base (D : Net n m) (x : Fin n → Bool) (w : Wire n m) := D.eval x (fun _ => none) w

theorem base_raw (D : Net n m) (x : Fin n → Bool) (i : Fin n) :
    D.base x (raw i) = x i := D.eval_raw _ _ _ rfl
theorem base_site (D : Net n m) (x : Fin n → Bool) (j : Fin m) :
    D.base x (site j) = D.combine j (D.base x (D.src j false)) (D.base x (D.src j true)) :=
  D.eval_site _ _ _ rfl

theorem mono_eval (D : Net n m) (cut : Wire n m → Option Bool) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) (w : Wire n m) (hx : D.eval x cut w = true) :
    D.eval y cut w = true := by
  cases he : D.eval y cut w with
  | true => rfl
  | false =>
    obtain ⟨i,p,hp⟩ := D.trace x y cut w hx he
    obtain ⟨ha,hb,hn⟩ := hp _ p.start_mem
    rw [eval_raw _ _ _ _ hn] at ha hb
    exact hb.symm.trans (h i ha)

theorem force_fixed (D : Net n m) (x : Fin n → Bool) (w : Wire n m)
    (hw : D.base x w = true) (z : Wire n m) : D.eval x (force w) z = D.base x z := by
  induction z using D.induction_wire with
  | hin i =>
    by_cases hi : raw i = w
    · subst w
      rw [eval_cut _ _ _ _ true (by simp [force]),hw]
    · rw [eval_raw _ _ _ _ (by simp [force,hi]),base_raw]
  | hgate j h0 h1 =>
    by_cases hj : site j = w
    · subst w
      rw [eval_cut _ _ _ _ true (by simp [force]),hw]
    · rw [eval_site _ _ _ _ (by simp [force,hj]), base_site,h0,h1]

theorem force_ge (D : Net n m) (x : Fin n → Bool) (w z : Wire n m)
    (hz : D.base x z = true) : D.eval x (force w) z = true := by
  induction z using D.induction_wire with
  | hin i =>
    by_cases hi : raw i = w
    · subst w; exact eval_cut _ _ _ _ _ (by simp [force])
    · rwa [eval_raw _ _ _ _ (by simp [force,hi]),←eval_raw D x (fun _ => none) _ rfl]
  | hgate j h0 h1 =>
    by_cases hj : site j = w
    · subst w; exact eval_cut _ _ _ _ _ (by simp [force])
    · rw [eval_site _ _ _ _ (by simp [force,hj])]
      rw [base_site] at hz
      cases ha : D.isAnd j <;> simp [combine,ha] at hz ⊢
      · exact hz.imp h0 h1
      · exact ⟨h0 hz.1,h1 hz.2⟩

theorem force_agrees_at_input {i : Fin n} {w z : Wire n m} (q : Line D (raw i) w)
    (hz : w.val ≤ z.val) (x y : Fin n → Bool) (h : ∀ k ≠ i, x k = y k)
    (hy : D.base y z = true) : D.eval x (force w) z = true := by
  rw [owner_independent q hz x y h]
  exact D.force_ge _ _ _ hy

theorem line_propagate {s w : Wire n m} (q : Line D s w) (x : Fin n → Bool)
    (hs : D.base x s = true) (hm : ∀ h ∈ q.masks, D.base x h = true) :
    D.base x w = true := by
  induction q with
  | first => exact hs
  | step j b q hu ih =>
    rw [base_site]
    have hi := ih (fun v hv => hm v (by cases ha : D.isAnd j <;> simp [Line.masks,ha,hv]))
    cases ha : D.isAnd j
    · cases b <;> simp_all [combine,base]
    · have hh := hm (D.src j (!b)) (by simp [Line.masks,ha])
      cases b <;> simp_all [combine,base]

theorem distinguishing_path (D : Net n m) (i : Fin n) (x y : Fin n → Bool)
    (h : ∀ k ≠ i, x k = y k) (o : Wire n m) (hy : D.base y o = true)
    (hx : D.base x o = false) :
    ∃ p : Path D (raw i) o, ∀ z ∈ p.nodes, D.base y z = true ∧ D.base x z = false := by
  obtain ⟨k,p,hp⟩ := D.trace y x (fun _ => none) o hy hx
  obtain ⟨ha,hb,hn⟩ := hp _ p.start_mem
  rw [eval_raw _ _ _ _ hn] at ha hb
  have hk : k=i := by by_contra hne; rw [h _ hne,ha] at hb; contradiction
  subst k
  exact ⟨p,fun z hz => ⟨(hp _ hz).1,(hp _ hz).2.1⟩⟩

theorem line_masks_accept {i : Fin n} {w o : Wire n m} (q : Line D (raw i) w)
    (ho : w.val ≤ o.val) (x y : Fin n → Bool) (h : ∀ k ≠ i, x k = y k)
    (hy : D.base y o = true) (hx : D.base x o = false) (z : Wire n m) (hz : z ∈ q.masks) :
    D.base x z = true := by
  have he : D.base x z = D.base y z := mask_independent q hz x y h
  rw [he]
  obtain ⟨p,hp⟩ := D.distinguishing_path i x y h o hy hx
  induction q with
  | first => simp [Line.masks] at hz
  | step j b q hu ih =>
    cases ha : D.isAnd j <;> simp [Line.masks,ha] at hz
    · exact ih ((D.lt_src j b).le.trans ho) hz
    · rcases hz with rfl|hh
      · have hj := (hp _ ((Line.step j b q hu).dominates p ho)).1
        rw [base_site] at hj
        cases b <;> simp_all [combine]
      · exact ih ((D.lt_src j b).le.trans ho) hh

end PEqualNP.Outside.L_meta_173_aux.Net

namespace PEqualNP.Outside.L_meta_173_aux
open Net
variable {n m : ℕ}

def onSet (S : Finset (Fin n)) (i : Fin n) := decide (i ∈ S)

theorem onSet_agree (c : Fin n) (S : Finset (Fin n)) (k : Fin n) (hk : k ≠ c) :
    onSet S k = onSet (insert c S) k := by simp [onSet,hk]

structure BipartiteNet (D : Net n m) where
  centers : Finset (Fin n)
  nbr : Fin n → Finset (Fin n)
  output : Wire n m
  last : ∀ z : Wire n m, z.val ≤ output.val
  live : ∀ z ≠ output, 0 < D.deg z
  sink : D.deg output = 0
  across : ∀ c ∈ centers, ∀ r ∈ nbr c, r ∉ centers
  large : ∀ c ∈ centers, 2 ≤ (nbr c).card
  distinguish : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → ∃ r ∈ nbr c, r ∉ nbr d
  thin : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → ∀ r ∈ nbr c, r ∈ nbr d →
    ∀ s ∈ nbr c, s ∈ nbr d → r=s
  result : ∀ S : Finset (Fin n), D.base (onSet S) output = true ↔
    ∃ c ∈ centers, c ∈ S ∧ ∃ r ∈ nbr c, r ∈ S

namespace BipartiteNet
variable {D : Net n m} (B : BipartiteNet D)

def right := Finset.univ \ B.centers
def avoid (c : Fin n) := B.right \ B.nbr c
def support (w : Wire n m) := B.right.filter fun r => D.base (onSet {r}) w = true

theorem pure_false {S : Finset (Fin n)} (hS : S ⊆ B.right) :
    D.base (onSet S) B.output = false := by
  cases h : D.base (onSet S) B.output with
  | false => rfl
  | true =>
    obtain ⟨c,hc,hs,_⟩ := (B.result S).1 h
    exact ((Finset.mem_sdiff.mp (hS hs)).2 hc).elim

theorem nbr_right {c : Fin n} (hc : c ∈ B.centers) : B.nbr c ⊆ B.right :=
  fun r hr => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,B.across c hc r hr⟩

theorem one_center {c : Fin n} (hc : c ∈ B.centers) (S : Finset (Fin n))
    (hs : S ⊆ B.right) : D.base (onSet (insert c S)) B.output = true ↔
    ∃ r ∈ B.nbr c, r ∈ S := by
  rw [B.result]
  constructor
  · rintro ⟨d,hd,hm,r,hr,hsr⟩
    have hdc : d=c := (Finset.mem_insert.mp hm).resolve_right (fun hh =>
      (Finset.mem_sdiff.mp (hs hh)).2 hd)
    subst d
    exact ⟨r,hr,(Finset.mem_insert.mp hsr).resolve_left (fun hh =>
      B.across c hc r hr (hh ▸ hc))⟩
  · rintro ⟨r,hr,hsr⟩
    exact ⟨c,hc,Finset.mem_insert_self _ _,r,hr,Finset.mem_insert_of_mem hsr⟩

theorem single_edge {c r : Fin n} (hc : c ∈ B.centers) (hr : r ∈ B.nbr c) :
    D.base (onSet (insert c {r})) B.output = true :=
  (B.one_center hc {r} (Finset.singleton_subset_iff.mpr (B.nbr_right hc hr))).2 ⟨r,hr,by simp⟩

theorem all_masks {c r : Fin n} (hc : c ∈ B.centers) (hr : r ∈ B.nbr c)
    {w : Wire n m} (q : Line D (raw c) w) (h : Wire n m) (hh : h ∈ q.masks) :
    D.base (onSet {r}) h = true :=
  line_masks_accept q (B.last _) _ _ (onSet_agree c {r}) (B.single_edge hc hr)
    (B.pure_false (Finset.singleton_subset_iff.mpr (B.nbr_right hc hr))) h hh

theorem cofactor_neigh {c r : Fin n} (hc : c ∈ B.centers) (hr : r ∈ B.nbr c)
    {w : Wire n m} (q : Line D (raw c) w) :
    D.eval (onSet {r}) (force w) B.output = true :=
  force_agrees_at_input q (B.last _) _ _ (onSet_agree c {r}) (B.single_edge hc hr)

theorem empty_support {c : Fin n} (hc : c ∈ B.centers) {w : Wire n m}
    (q : Line D (raw c) w) : B.support w = ∅ := by
  classical
  obtain ⟨r0,h0⟩ := Finset.card_pos.mp (show 0 < (B.nbr c).card by have := B.large c hc; omega)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hrR,hv⟩ := Finset.mem_filter.mp hr
  let S : Finset (Fin n) := {r,r0}
  have hS : S ⊆ B.right := Finset.insert_subset hrR
    (Finset.singleton_subset_iff.mpr (B.nbr_right hc h0))
  have h1 := D.mono_eval (fun _ => none) (onSet {r}) (onSet S) (by
    intro k hk; simpa [onSet,S] using (show k=r ∨ k=r0 from Or.inl (by simpa [onSet] using hk))) w hv
  have h2 := D.mono_eval (force w) (onSet {r0}) (onSet S) (by
    intro k hk; simpa [onSet,S] using (show k=r ∨ k=r0 from Or.inr (by simpa [onSet] using hk)))
    B.output (B.cofactor_neigh hc h0 q)
  rw [D.force_fixed _ _ h1] at h2
  rw [B.pure_false hS] at h2
  contradiction

theorem mask_or_cofactor {c : Fin n} (hc : c ∈ B.centers) {w : Wire n m} (q : Line D (raw c) w) :
    (∃ h ∈ q.masks, D.base (onSet (B.avoid c)) h = false) ∨
    D.eval (onSet (B.avoid c)) (force w) B.output = false := by
  classical
  by_cases hh : ∃ h ∈ q.masks, D.base (onSet (B.avoid c)) h = false
  · exact Or.inl hh
  right
  let S := B.avoid c
  have hs : S ⊆ B.right := Finset.sdiff_subset
  have hagr := onSet_agree c S
  rw [owner_independent q (B.last _) _ _ hagr]
  have hw : D.base (onSet (insert c S)) w = true := by
    apply line_propagate q
    · simp [base_raw,onSet]
    · intro h hm
      have he : D.base (onSet S) h = D.base (onSet (insert c S)) h := mask_independent q hm _ _ hagr
      rw [←he]
      cases hx : D.base (onSet S) h with
      | true => rfl
      | false => exact (hh ⟨h,hm,hx⟩).elim
  rw [D.force_fixed _ _ hw]
  cases hy : D.base (onSet (insert c S)) B.output with
  | false => rfl
  | true =>
    obtain ⟨r,hr,hS⟩ := (B.one_center hc S hs).1 hy
    exact ((Finset.mem_sdiff.mp hS).2 hr).elim

end BipartiteNet
end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux
open Net
variable {n m : ℕ} {D : Net n m}

theorem onSet_mono {S U : Finset (Fin n)} (hu : S ⊆ U) :
    ∀ i, onSet S i = true → onSet U i = true := by
  intro i hi
  simpa [onSet] using (hu (by simpa [onSet] using hi) : i ∈ U)

namespace Net

noncomputable def firstOwner (D : Net n m) (i : Fin n) : Wire n m :=
  Classical.choose ((Line.first : Line D (raw i) (raw i)).until_fork)
noncomputable def stem (D : Net n m) (i : Fin n) : Line D (raw i) (D.firstOwner i) :=
  Classical.choose (Classical.choose_spec ((Line.first : Line D (raw i) (raw i)).until_fork))
theorem stopped (D : Net n m) (i : Fin n) : D.deg (D.firstOwner i) ≠ 1 :=
  Classical.choose_spec (Classical.choose_spec ((Line.first : Line D (raw i) (raw i)).until_fork))

end Net
namespace BipartiteNet
variable (B : BipartiteNet D)

def Actual (c : Fin n) : Prop := ∃ h ∈ (D.stem c).masks, D.base (onSet (B.avoid c)) h = false
noncomputable def actuals := B.centers.filter (fun c => @decide (B.Actual c) (Classical.propDecidable _))
noncomputable def other := B.centers \ B.actuals
theorem mem_actual {c : Fin n} : c ∈ B.actuals ↔ c ∈ B.centers ∧ B.Actual c := by
  classical
  simp [actuals]
theorem mem_other {c : Fin n} : c ∈ B.other ↔ c ∈ B.centers ∧ ¬B.Actual c := by
  classical
  simp [other,mem_actual]
  tauto

noncomputable def mask (c : Fin n) (hc : c ∈ B.actuals) := Classical.choose (B.mem_actual.mp hc).2
theorem mask_mem (c : Fin n) (hc : c ∈ B.actuals) : B.mask c hc ∈ (D.stem c).masks :=
  (Classical.choose_spec (B.mem_actual.mp hc).2).1
theorem mask_false (c : Fin n) (hc : c ∈ B.actuals) : D.base (onSet (B.avoid c)) (B.mask c hc) = false :=
  (Classical.choose_spec (B.mem_actual.mp hc).2).2

theorem mask_support (c : Fin n) (hc : c ∈ B.actuals) : B.support (B.mask c hc) = B.nbr c := by
  classical
  ext r
  simp only [support,Finset.mem_filter]
  constructor
  · rintro ⟨hr,hy⟩
    by_contra h
    have hm : {r} ⊆ B.avoid c := Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨hr,h⟩)
    have hh := D.mono_eval (fun _ => none) _ _ (onSet_mono hm) _ hy
    have h0 := B.mask_false c hc
    exact Bool.noConfusion (h0.symm.trans hh)
  · intro hr
    have hl := (B.mem_actual.mp hc).1
    exact ⟨B.nbr_right hl hr,B.all_masks hl hr (D.stem c) _ (B.mask_mem c hc)⟩

theorem other_reject (c : Fin n) (hc : c ∈ B.other) :
    D.eval (onSet (B.avoid c)) (force (D.firstOwner c)) B.output = false :=
  (B.mask_or_cofactor (B.mem_other.mp hc).1 (D.stem c)).resolve_left (B.mem_other.mp hc).2

theorem other_owner_fork (c : Fin n) (hc : c ∈ B.other) : 2 ≤ D.deg (D.firstOwner c) := by
  have ho : D.firstOwner c ≠ B.output := by
    intro h
    have hv := B.other_reject c hc
    rw [h,eval_cut _ _ _ _ true (by simp [force])] at hv
    contradiction
  have := B.live _ ho
  have := D.stopped c
  omega

theorem other_owner_inj {c d : Fin n} (hc : c ∈ B.other) (hd : d ∈ B.other)
    (he : D.firstOwner c = D.firstOwner d) : c=d := by
  classical
  by_contra hcd
  have h1 := (B.mem_other.mp hc).1
  have h2 := (B.mem_other.mp hd).1
  obtain ⟨r,hr,hn⟩ := B.distinguish c h1 d h2 hcd
  have hrA : {r} ⊆ B.avoid d := Finset.singleton_subset_iff.mpr
    (Finset.mem_sdiff.mpr ⟨B.nbr_right h1 hr,hn⟩)
  have hok := B.cofactor_neigh h1 hr (D.stem c)
  rw [he] at hok
  have hall := D.mono_eval _ _ _ (onSet_mono hrA) _ hok
  exact Bool.noConfusion ((B.other_reject d hd).symm.trans hall)

end BipartiteNet
end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux.Net
variable {n m : ℕ} {D : Net n m}

theorem sum_count_excess {α : Type*} [DecidableEq α] (V B : Finset α) (f : α → ℕ)
    (hB : B ⊆ V) (hz : ∀ v ∈ V, f v = 0 ↔ v ∈ B) :
    (∑ v ∈ V, (f v - 1)) + V.card = (∑ v ∈ V, f v) + B.card := by
  classical
  have ht : ∑ v ∈ V, (f v - 1 + 1) = ∑ v ∈ V, (f v + if v ∈ B then 1 else 0) := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    by_cases hb : v ∈ B
    · simp [hb,(hz v hv).2 hb]
    · have hp : f v ≠ 0 := fun hh => hb ((hz v hv).1 hh)
      simp [hb]; omega
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at ht
  have hh : (∑ v ∈ V, if v ∈ B then 1 else 0 : ℕ) = B.card := by
    rw [←Finset.sum_filter]
    have he : V.filter (· ∈ B) = B := by ext v; simp only [Finset.mem_filter]; exact ⟨And.right,fun hv => ⟨hB hv,hv⟩⟩
    rw [he]; simp
  simpa [hh] using ht

structure Routes (D : Net n m) (s : Wire n m) where
  ends : Finset (Wire n m)
  path : ∀ t ∈ ends, Path D s t
  separate : ∀ t ht u, u ∈ ends → u ∈ (path t ht).nodes → u = t

namespace Routes
variable {s : Wire n m} (H : Routes D s)

def verts := H.ends.attach.biUnion (fun t => (H.path t.val t.property).nodes)
def arcs := H.ends.attach.biUnion (fun t => (H.path t.val t.property).edges)
def outs (v : Wire n m) := H.arcs.filter fun e => D.src e.1 e.2 = v
def ins (v : Wire n m) := H.arcs.filter fun e => site e.1 = v
def outdeg (v : Wire n m) := (H.outs v).card
def indeg (v : Wire n m) := (H.ins v).card

theorem mem_arcs {e : Fin m × Bool} :
    e ∈ H.arcs ↔ ∃ t, ∃ ht : t ∈ H.ends, e ∈ (H.path t ht).edges := by
  simp [arcs]
theorem mem_verts {v : Wire n m} :
    v ∈ H.verts ↔ ∃ t, ∃ ht : t ∈ H.ends, v ∈ (H.path t ht).nodes := by
  simp [verts]

theorem ends_sub : H.ends ⊆ H.verts := by
  intro t ht
  exact H.mem_verts.mpr ⟨t,ht,(H.path t ht).self_mem⟩

theorem src_in_V {e : Fin m × Bool} (he : e ∈ H.arcs) : D.src e.1 e.2 ∈ H.verts := by
  obtain ⟨t,ht,h⟩ := H.mem_arcs.mp he
  exact H.mem_verts.mpr ⟨t,ht,(H.path t ht).src_mem h⟩
theorem dst_in_V {e : Fin m × Bool} (he : e ∈ H.arcs) : site e.1 ∈ H.verts := by
  obtain ⟨t,ht,h⟩ := H.mem_arcs.mp he
  exact H.mem_verts.mpr ⟨t,ht,(H.path t ht).dst_mem h⟩

theorem out_zero (v : Wire n m) (hv : v ∈ H.verts) : H.outdeg v = 0 ↔ v ∈ H.ends := by
  classical
  constructor
  · intro hz
    obtain ⟨t,ht,hm⟩ := H.mem_verts.mp hv
    by_contra h
    obtain ⟨e,he,hs⟩ := (H.path t ht).has_out hm (fun heq => h (heq ▸ ht))
    have hf : e ∈ H.outs v := Finset.mem_filter.mpr ⟨H.mem_arcs.mpr ⟨t,ht,he⟩,hs⟩
    exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨e,hf⟩)) hz
  · intro ht
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp he
    obtain ⟨t,ht',hh⟩ := H.mem_arcs.mp hmem
    have heq := H.separate t ht' v ht (hs ▸ (H.path t ht').src_mem hh)
    have hl := (H.path t ht').node_le ((H.path t ht').dst_mem hh)
    have hlt := D.lt_src e.1 e.2
    change n+e.1.val ≤ t.val at hl
    rw [hs,heq] at hlt
    omega

theorem in_zero (v : Wire n m) (hv : v ∈ H.verts) : H.indeg v = 0 ↔ v = s := by
  constructor
  · intro hz
    obtain ⟨t,ht,hm⟩ := H.mem_verts.mp hv
    by_contra h
    obtain ⟨e,he,hs⟩ := (H.path t ht).has_in hm h
    have hf : e ∈ H.ins v := Finset.mem_filter.mpr ⟨H.mem_arcs.mpr ⟨t,ht,he⟩,hs⟩
    exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨e,hf⟩)) hz
  · intro hvs
    subst v
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp he
    obtain ⟨t,ht,hh⟩ := H.mem_arcs.mp hmem
    have hstart : ∀ {z : Wire n m} (p : Path D s z) e, e ∈ p.edges →
        s.val ≤ (D.src e.1 e.2).val := by
      intro z p
      induction p with
      | refl => simp [Path.edges]
      | step j b q ih =>
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl|hf'
        · exact q.node_le q.start_mem
        · exact ih _ hf'
    have hl := hstart (H.path t ht) _ hh
    have hlt : (D.src e.1 e.2).val < (site e.1 : Wire n m).val := D.lt_src _ _
    rw [hs] at hlt
    omega

theorem balance (hne : H.ends.Nonempty) :
    (∑ v ∈ H.verts, (H.outdeg v - 1)) + 1 =
      H.ends.card + ∑ v ∈ H.verts, (H.indeg v - 1) := by
  classical
  obtain ⟨t,ht⟩ := hne
  have hs : s ∈ H.verts := H.mem_verts.mpr ⟨t,ht,(H.path t ht).start_mem⟩
  have ho := sum_count_excess H.verts H.ends H.outdeg H.ends_sub H.out_zero
  have hi := sum_count_excess H.verts {s} H.indeg (by simpa) (fun v hv => by simpa using H.in_zero v hv)
  have h1 : (∑ v ∈ H.verts, H.outdeg v) = H.arcs.card :=
    (Finset.card_eq_sum_card_fiberwise (f := fun e : Fin m × Bool => D.src e.1 e.2)
      (fun _ he => H.src_in_V he)).symm
  have h2 : (∑ v ∈ H.verts, H.indeg v) = H.arcs.card :=
    (Finset.card_eq_sum_card_fiberwise (f := fun e : Fin m × Bool => (site e.1 : Wire n m))
      (fun _ he => H.dst_in_V he)).symm
  rw [h1] at ho
  rw [h2,Finset.card_singleton] at hi
  omega

end Routes
end PEqualNP.Outside.L_meta_173_aux.Net

namespace PEqualNP.Outside.L_meta_173_aux.BipartiteNet
open Net
variable {n m : ℕ} {D : Net n m} (B : BipartiteNet D)

noncomputable def requests (r : Fin n) := B.actuals.attach.filter (fun c => r ∈ B.nbr c.val)
noncomputable def hits (r : Fin n) := B.other.filter (fun c => r ∈ B.nbr c)
noncomputable def maskEnds (r : Fin n) := (B.requests r).image (fun c => B.mask c.val c.property)
noncomputable def ends (r : Fin n) := B.maskEnds r ∪ if (B.hits r).Nonempty then {B.output} else ∅

theorem mask_not_output (c : Fin n) (hc : c ∈ B.actuals) : B.mask c hc ≠ B.output := by
  intro hh
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < (B.nbr c).card by have := B.large c (B.mem_actual.mp hc).1; omega)
  have hpos := B.all_masks (B.mem_actual.mp hc).1 hr (D.stem c) _ (B.mask_mem c hc)
  rw [hh,B.pure_false (Finset.singleton_subset_iff.mpr (B.nbr_right (B.mem_actual.mp hc).1 hr))] at hpos
  contradiction

theorem mask_inj {c d : Fin n} (hc : c ∈ B.actuals) (hd : d ∈ B.actuals)
    (he : B.mask c hc = B.mask d hd) : c=d := by
  by_contra h
  obtain ⟨r,hr,hn⟩ := B.distinguish c (B.mem_actual.mp hc).1 d (B.mem_actual.mp hd).1 h
  rw [←B.mask_support c hc,he,B.mask_support d hd] at hr
  exact hn hr

theorem end_cases {r : Fin n} {t : Wire n m} (ht : t ∈ B.ends r) :
    (∃ c, ∃ hc : c ∈ B.actuals, r ∈ B.nbr c ∧ t = B.mask c hc) ∨
    (t=B.output ∧ ∃ a ∈ B.other, r ∈ B.nbr a) := by
  classical
  rcases Finset.mem_union.mp ht with hm|ho
  · obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hm
    exact Or.inl ⟨d.val,d.property,(Finset.mem_filter.mp hd).2,he.symm⟩
  · right
    by_cases hi : (B.hits r).Nonempty
    · obtain ⟨a,ha⟩ := id hi
      exact ⟨by simpa [hi] using ho,a,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2⟩
    · simp [hi] at ho

def maskCondition (r c : Fin n) (p : Wire n m) : Prop :=
  r ∈ B.support p ∧ B.support p ⊆ B.nbr c
def outerCondition (a : Fin n) (p : Wire n m) : Prop :=
  D.base (onSet (insert a (B.avoid a))) p = false

def Strand {r : Fin n} {t : Wire n m} (p : Path D (raw r) t) : Prop :=
  (∃ c, ∃ hc : c ∈ B.actuals, r ∈ B.nbr c ∧ t=B.mask c hc ∧
      ∀ z ∈ p.nodes, B.maskCondition r c z) ∨
  (∃ a ∈ B.other, r ∈ B.nbr a ∧ t=B.output ∧ ∀ z ∈ p.nodes, B.outerCondition a z)

theorem strand_exists {r : Fin n} {t : Wire n m} (ht : t ∈ B.ends r) :
    ∃ p : Path D (raw r) t, B.Strand p := by
  classical
  rcases B.end_cases ht with ⟨c,hc,hr,rfl⟩|⟨rfl,a,ha,hr⟩
  · have h1 := B.all_masks (B.mem_actual.mp hc).1 hr (D.stem c) _ (B.mask_mem c hc)
    obtain ⟨k,p,hp⟩ := D.trace (onSet {r}) (onSet (B.avoid c)) (fun _ => none) _
      h1 (B.mask_false c hc)
    have hk := (hp _ p.start_mem).1
    rw [eval_raw _ _ _ _ rfl] at hk
    obtain rfl : k=r := by simpa [onSet] using hk
    refine ⟨p,Or.inl ⟨c,hc,hr,rfl,fun z hz => ?_⟩⟩
    have hR := B.nbr_right (B.mem_actual.mp hc).1 hr
    refine ⟨Finset.mem_filter.mpr ⟨hR,(hp _ hz).1⟩,?_⟩
    intro v hv
    obtain ⟨hvR,hv1⟩ := Finset.mem_filter.mp hv
    by_contra hv0
    have hh : {v} ⊆ B.avoid c := Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨hvR,hv0⟩)
    exact Bool.noConfusion ((hp _ hz).2.1.symm.trans (D.mono_eval _ _ _ (onSet_mono hh) _ hv1))
  · have hA := (B.mem_other.mp ha).1
    have hR := B.nbr_right hA hr
    let S := insert a (B.avoid a)
    have hS : B.avoid a ⊆ B.right := Finset.sdiff_subset
    have h0 : D.base (onSet S) B.output = false := by
      cases h : D.base (onSet S) B.output
      · rfl
      · obtain ⟨v,hv,hm⟩ := (B.one_center hA _ hS).1 h
        exact ((Finset.mem_sdiff.mp hm).2 hv).elim
    have h1 : D.base (onSet (insert r S)) B.output = true := by
      apply (B.result _).2
      exact ⟨a,hA,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),r,hr,Finset.mem_insert_self _ _⟩
    obtain ⟨p,hp⟩ := D.distinguishing_path r (onSet S) _ (onSet_agree r S) _ h1 h0
    exact ⟨p, Or.inr ⟨a,ha,hr,rfl,fun z hz => (hp _ hz).2⟩⟩

theorem outer_support {a : Fin n} {z : Wire n m} (h : B.outerCondition a z) :
    B.support z ⊆ B.nbr a := by
  intro r hr
  obtain ⟨hR,hp⟩ := Finset.mem_filter.mp hr
  by_contra hnot
  have hs : {r} ⊆ insert a (B.avoid a) := Finset.singleton_subset_iff.mpr
    (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hR,hnot⟩))
  exact Bool.noConfusion (h.symm.trans (D.mono_eval _ _ _ (onSet_mono hs) _ hp))

theorem strand_separate {r : Fin n} {t u : Wire n m} {p : Path D (raw r) t}
    (h : B.Strand p) (hu : u ∈ B.ends r) (hm : u ∈ p.nodes) : u=t := by
  classical
  rcases h with ⟨c,hc,hr,rfl,hp⟩|⟨a,ha,hr,rfl,hp⟩
  · obtain ⟨hR,hs⟩ := hp _ hm
    rcases B.end_cases hu with ⟨d,hd,_,rfl⟩|⟨rfl,_⟩
    · rw [B.mask_support d hd] at hs
      by_cases hh : d=c
      · subst d; rfl
      · obtain ⟨v,hv,hn⟩ := B.distinguish d (B.mem_actual.mp hd).1 c (B.mem_actual.mp hc).1 hh
        exact (hn (hs hv)).elim
    · have h0 := B.pure_false (Finset.singleton_subset_iff.mpr (B.nbr_right (B.mem_actual.mp hc).1 hr))
      exact Bool.noConfusion (h0.symm.trans (Finset.mem_filter.mp hR).2)
  · rcases B.end_cases hu with ⟨d,hd,_,rfl⟩|⟨he,_⟩
    · have hsub := B.outer_support (hp _ hm)
      rw [B.mask_support d hd] at hsub
      have hh : d≠a := by intro e; subst a; exact (B.mem_other.mp ha).2 (B.mem_actual.mp hd).2
      obtain ⟨v,hv,hno⟩ := B.distinguish d (B.mem_actual.mp hd).1 a (B.mem_other.mp ha).1 hh
      exact (hno (hsub hv)).elim
    · exact he

noncomputable def routes (r : Fin n) : Routes D (raw r) where
  ends := B.ends r
  path := fun _ ht => Classical.choose (B.strand_exists ht)
  separate := fun _ ht _ hu hm => B.strand_separate (Classical.choose_spec (B.strand_exists ht)) hu hm

end PEqualNP.Outside.L_meta_173_aux.BipartiteNet

namespace PEqualNP.Outside.L_meta_173_aux.BipartiteNet
open Net
variable {n m : ℕ} {D : Net n m} (B : BipartiteNet D)

theorem path_strand {r : Fin n} {t : Wire n m} (h : t ∈ (B.routes r).ends) :
    B.Strand ((B.routes r).path t h) := Classical.choose_spec (B.strand_exists h)

theorem pair_support {r c d : Fin n} (hc : c ∈ B.centers) (hd : d ∈ B.centers)
    (hne : c≠d) (hrc : r∈B.nbr c) (hrd : r∈B.nbr d) {w : Wire n m}
    (hs : B.maskCondition r c w) (ht : B.support w ⊆ B.nbr d) :
    B.support w = {r} := by
  ext v
  constructor
  · intro hv
    exact Finset.mem_singleton.mpr (B.thin c hc d hd hne r hrc hrd v (hs.2 hv) (ht hv)).symm
  · intro hv
    obtain rfl := Finset.mem_singleton.mp hv
    exact hs.1

theorem branch_label (r : Fin n) (w : Wire n m) (h : 1 < (B.routes r).outdeg w) :
    B.support w = {r} := by
  classical
  let H := B.routes r
  obtain ⟨e,he,f,hf,hne⟩ := Finset.one_lt_card.mp h
  obtain ⟨hea,hes⟩ := Finset.mem_filter.mp he
  obtain ⟨hfa,hfs⟩ := Finset.mem_filter.mp hf
  obtain ⟨t,ht,hpt⟩ := H.mem_arcs.mp hea
  obtain ⟨u,hu,hpu⟩ := H.mem_arcs.mp hfa
  have htu : t≠u := by
    intro hh; subst u
    exact hne ((H.path t ht).outgoing_unique hpt hpu (hes.trans hfs.symm))
  have htw : w∈(H.path t ht).nodes := hes ▸ (H.path t ht).src_mem hpt
  have huw : w∈(H.path u hu).nodes := hfs ▸ (H.path u hu).src_mem hpu
  rcases B.path_strand ht with ⟨c,hc,hrc,rfl,hp⟩|⟨c,hc,hrc,rfl,hp⟩ <;>
    rcases B.path_strand hu with ⟨d,hd,hrd,rfl,hq⟩|⟨d,hd,hrd,rfl,hq⟩
  · have hcd : c≠d := by intro heq; subst d; exact htu rfl
    exact B.pair_support (B.mem_actual.mp hc).1 (B.mem_actual.mp hd).1 hcd hrc hrd
      (hp _ htw) (hq _ huw).2
  · have hcd : c≠d := by intro heq; subst d; exact (B.mem_other.mp hd).2 (B.mem_actual.mp hc).2
    exact B.pair_support (B.mem_actual.mp hc).1 (B.mem_other.mp hd).1 hcd hrc hrd
      (hp _ htw) (B.outer_support (hq _ huw))
  · have hdc : d≠c := by intro heq; subst c; exact (B.mem_other.mp hc).2 (B.mem_actual.mp hd).2
    exact B.pair_support (B.mem_actual.mp hd).1 (B.mem_other.mp hc).1 hdc hrd hrc
      (hq _ huw) (B.outer_support (hp _ htw))
  · exact (htu rfl).elim

theorem requests_card (r : Fin n) :
    (B.requests r).card = (B.actuals.filter (fun c => r ∈ B.nbr c)).card := by
  classical
  let s := B.actuals.filter fun c => r ∈ B.nbr c
  have he : (B.requests r).image Subtype.val = s := by
    ext c
    simp [requests,s,and_comm]
  change (B.requests r).card = s.card
  rw [←he, Finset.card_image_of_injective _ Subtype.val_injective]

theorem ends_card (r : Fin n) : ((B.routes r).ends).card =
    (B.actuals.filter fun c => r ∈ B.nbr c).card + if (B.hits r).Nonempty then 1 else 0 := by
  classical
  have hc : (B.maskEnds r).card = (B.requests r).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb h
    exact Subtype.ext (B.mask_inj a.property b.property h)
  have ho : B.output ∉ B.maskEnds r := by
    intro h
    obtain ⟨d,_,he⟩ := Finset.mem_image.mp h
    exact B.mask_not_output _ _ he
  change (B.ends r).card = _
  by_cases hh : (B.hits r).Nonempty <;> simp [ends,hh,ho,hc,B.requests_card]

theorem tight_node {r : Fin n} {w : Wire n m} (ha : B.other = ∅) (hw : w ∈ (B.routes r).verts) :
    r ∈ B.support w := by
  obtain ⟨t,ht,hp⟩ := (B.routes r).mem_verts.mp hw
  rcases B.path_strand ht with ⟨c,_,_,_,h⟩ | ⟨a,ha',_⟩
  · exact (h _ hp).1
  · simp [ha] at ha'

theorem tight_nodes_subset {r : Fin n} {w : Wire n m} (ha : B.other = ∅)
    (hw : w ∈ (B.routes r).verts) : ∃ c ∈ B.centers, B.support w ⊆ B.nbr c := by
  obtain ⟨t,ht,hp⟩ := (B.routes r).mem_verts.mp hw
  rcases B.path_strand ht with ⟨c,hc,_,_,h⟩ | ⟨a,ha',_⟩
  · exact ⟨c,(B.mem_actual.mp hc).1,(h _ hp).2⟩
  · simp [ha] at ha'

end PEqualNP.Outside.L_meta_173_aux.BipartiteNet

namespace PEqualNP.Outside.L_meta_173_aux

open PEqualNP.MetaComplexity

namespace GraphFacts

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {T : Finset (Fin n)}

theorem hasNeighbor (hconn : G.Connected) (hedges : 2 ≤ G.edgeFinset.card) (i : Fin n) :
    ∃ j, G.Adj i j := by
  classical
  obtain ⟨e,he⟩ := Finset.card_pos.mp (by omega : 0 < G.edgeFinset.card)
  obtain ⟨⟨a,b⟩,rfl⟩ := e.exists_rep
  have hab : G.Adj a b := by simpa using he
  let _ : Nontrivial (Fin n) := ⟨⟨a,b,hab.ne⟩⟩
  exact hconn.preconnected.exists_adj_of_nontrivial i

omit [DecidableRel G.Adj] in
theorem opposite (hc : CoverPromise.IsVertexCover G T)
    (hi : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) {u v} (he : G.Adj u v) : u ∈ T ↔ v ∉ T :=
  ⟨fun hu hv => hi u hu v hv he, fun hv => (hc u v he).resolve_right hv⟩

theorem centerDegree (hc : CoverPromise.IsVertexCover G T)
    (hi : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v)
    (hu : ∀ S : Finset _, CoverPromise.IsVertexCover G S → S.card = T.card → S = T)
    (hn : ∀ i, ∃ j, G.Adj i j) {c} (hct : c ∈ T) : 2 ≤ (G.neighborFinset c).card := by
  classical
  obtain ⟨p,hp⟩ := hn c
  have hpt := (opposite hc hi hp).mp hct
  have hpn : p ∈ G.neighborFinset c := by simpa using hp
  by_contra! hsmall
  have hsingle : ∀ q, G.Adj c q → q = p := by
    intro q hq
    exact Finset.card_le_one.mp (by omega : (G.neighborFinset c).card ≤ 1) q
      (by simpa using hq) p hpn
  let S := insert p (T.erase c)
  have hSc : CoverPromise.IsVertexCover G S := by
    intro u v h
    rcases hc u v h with h | h
    · by_cases he : u = c
      · subst u
        exact Or.inr (by simp [S, hsingle v ‹G.Adj c v›])
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,h⟩))
    · by_cases he : v = c
      · subst v
        exact Or.inl (by simp [S, hsingle u ‹G.Adj u c›.symm])
      · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,h⟩))
  have hcard : S.card = T.card := by
    rw [show S = insert p (T.erase c) from rfl, Finset.card_insert_of_notMem (by simp [hpt]),
      Finset.card_erase_of_mem hct]
    have := Finset.card_pos.mpr ⟨c,hct⟩
    omega
  have hpS : p ∈ S := Finset.mem_insert_self ..
  exact hpt (hu S hSc hcard ▸ hpS)

omit [DecidableRel G.Adj] in
theorem common_unique (ha : G.IsAcyclic) {c d r s} (hcd : c ≠ d)
    (hcr : G.Adj c r) (hdr : G.Adj d r) (hcs : G.Adj c s) (hds : G.Adj d s) : r = s := by
  let p : G.Walk c d := .cons hcr (.cons hdr.symm .nil)
  let q : G.Walk c d := .cons hcs (.cons hds.symm .nil)
  have hp : p.IsPath := by simp [p, SimpleGraph.Walk.cons_isPath_iff, hcr.ne, hdr.ne.symm, hcd]
  have hq : q.IsPath := by simp [q, SimpleGraph.Walk.cons_isPath_iff, hcs.ne, hds.ne.symm, hcd]
  have h := (ha.subsingleton_path c d).elim ⟨p,hp⟩ ⟨q,hq⟩
  exact congrArg (fun a : G.Path c d => a.val.snd) h

theorem separate (ha : G.IsAcyclic) {c d} (hcd : c ≠ d)
    (hd : 2 ≤ (G.neighborFinset c).card) : ∃ r, G.Adj c r ∧ ¬G.Adj d r := by
  classical
  obtain ⟨r,hr,s,hs,hrs⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset c).card)
  have hcr : G.Adj c r := by simpa using hr
  have hcs : G.Adj c s := by simpa using hs
  by_contra! h
  exact hrs (common_unique ha hcd hcr (h r hcr) hcs (h s hcs))

theorem bipartition (hc : CoverPromise.IsVertexCover G T)
    (hi : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) : G.IsBipartiteWith (T : Set _) (↑(Finset.univ \ T) : Set _) := by
  classical
  constructor
  · exact Set.disjoint_left.mpr (by simp)
  · intro u v h
    by_cases hT : u ∈ T
    · exact Or.inl ⟨hT, by simp [(opposite hc hi h).mp hT]⟩
    · exact Or.inr ⟨by simp [hT],(hc u v h).resolve_left hT⟩

theorem sum_center_degree (hc : CoverPromise.IsVertexCover G T)
    (hi : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) : ∑ c ∈ T, G.degree c = G.edgeFinset.card :=
  SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges (bipartition hc hi)

def branchCount (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T A : Finset (Fin n)) (r : Fin n) : ℕ :=
  ((G.neighborFinset r) ∩ (T \ A)).card + if ((G.neighborFinset r) ∩ A).Nonempty then 1 else 0

theorem branch_pos (hc : CoverPromise.IsVertexCover G T) (hn : ∀ i, ∃ j, G.Adj i j)
    (A : Finset (Fin n)) {r} (hr : r ∉ T) : 1 ≤ branchCount G T A r := by
  classical
  obtain ⟨j,hj⟩ := hn r
  have hjT := (hc r j hj).resolve_left hr
  have hjr : j ∈ G.neighborFinset r := by simpa using hj
  by_cases hA : j ∈ A
  · have hne : ((G.neighborFinset r) ∩ A).Nonempty := ⟨j,Finset.mem_inter.mpr ⟨hjr,hA⟩⟩
    simp [branchCount,hne]
  · have hne : ((G.neighborFinset r) ∩ (T \ A)).Nonempty :=
      ⟨j,Finset.mem_inter.mpr ⟨hjr,Finset.mem_sdiff.mpr ⟨hjT,hA⟩⟩⟩
    have := Finset.card_pos.mpr hne
    unfold branchCount
    omega

theorem incidence_deficit (ha : G.IsAcyclic) {A R : Finset (Fin n)} (hAR : Disjoint A R)
    (hA : A.Nonempty) :
    (∑ r ∈ R, (G.neighborFinset r ∩ A).card) + 1 ≤
      A.card + (R.filter (fun r => (G.neighborFinset r ∩ A).Nonempty)).card := by
  classical
  let B := R.filter (fun r => (G.neighborFinset r ∩ A).Nonempty)
  let S := A ∪ B
  have hAB : Disjoint A B := hAR.mono_right (Finset.filter_subset ..)
  let K := G.between (A : Set _) (B : Set _)
  have hbip : K.IsBipartiteWith (A : Set _) (B : Set _) :=
    SimpleGraph.between_isBipartiteWith (Finset.disjoint_coe.mpr hAB)
  have hsupp : K.support ⊆ (S : Set _) := by
    simpa [S] using SimpleGraph.isBipartiteWith_support_subset hbip
  have hne : Nonempty (↑(S : Set (Fin n))) := by
    obtain ⟨a,ha⟩ := hA
    exact ⟨⟨a, Finset.mem_union_left B ha⟩⟩
  have hbound := ((ha.anti (show K ≤ G from SimpleGraph.between_le)).induce
    (S : Set _)).ncard_edgeSet_add_one_le_card
  have hbound' : K.edgeFinset.card + 1 ≤ S.card := by
    rw [← SimpleGraph.card_edgeFinset_induce_of_support_subset hsupp]
    rw [Set.ncard_eq_toFinset_card'] at hbound
    simpa [SimpleGraph.edgeFinset, Nat.card_eq_fintype_card] using hbound
  have hsum : (∑ r ∈ B, (G.neighborFinset r ∩ A).card) = K.edgeFinset.card := by
    rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbip]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext x
    have hrA : r ∉ A := fun hrA => Finset.disjoint_left.mp hAB hrA hr
    simp [K,SimpleGraph.between_adj,hr,hrA]
  have hext : (∑ r ∈ B, (G.neighborFinset r ∩ A).card) = ∑ r ∈ R, (G.neighborFinset r ∩ A).card := by
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro r hr hnot
    have : ¬(G.neighborFinset r ∩ A).Nonempty := fun h => hnot (Finset.mem_filter.mpr ⟨hr,h⟩)
    simp [Finset.not_nonempty_iff_eq_empty.mp this]
  rw [← hext, hsum]
  simpa [S,Finset.card_union_of_disjoint hAB,B] using hbound'

theorem branch_deficit (ht : G.IsTree) (hc : CoverPromise.IsVertexCover G T)
    (hi : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) (hn : ∀ i, ∃ j, G.Adj i j)
    {A : Finset (Fin n)} (hAT : A ⊆ T) (hne : A.Nonempty) :
    T.card ≤ A.card + ∑ r ∈ Finset.univ \ T, (branchCount G T A r - 1) := by
  classical
  let R := Finset.univ \ T
  let a := fun r => (G.neighborFinset r ∩ A).card
  let p := fun r => (G.neighborFinset r ∩ (T \ A)).card
  let hit := fun r => (G.neighborFinset r ∩ A).Nonempty
  have hAR : Disjoint A R := Finset.disjoint_left.mpr (fun _ hA hR => (Finset.mem_sdiff.mp hR).2 (hAT hA))
  have hforest := incidence_deficit ht.isAcyclic hAR hne
  change (∑ r ∈ R, a r) + 1 ≤ A.card + (R.filter hit).card at hforest
  have hbip := bipartition hc hi
  have hs : (∑ r ∈ R, (a r + p r)) = G.edgeFinset.card := by
    rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbip]
    apply Finset.sum_congr rfl
    intro r hr
    have hsub := SimpleGraph.isBipartiteWith_neighborFinset_subset' hbip hr
    have hset : (G.neighborFinset r ∩ A) ∪ (G.neighborFinset r ∩ (T \ A)) = G.neighborFinset r := by
      ext x
      simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
      exact ⟨fun h => h.elim And.left And.left,fun h => by by_cases h' : x ∈ A; tauto; exact Or.inr ⟨h,hsub h,h'⟩⟩
    have hd : Disjoint (G.neighborFinset r ∩ A) (G.neighborFinset r ∩ (T \ A)) := by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_inter,Finset.mem_sdiff]
      tauto
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hset, Finset.card_union_of_disjoint hd]
  have hs' : (∑ r ∈ R, (branchCount G T A r - 1)) + R.card =
      (∑ r ∈ R, p r) + (R.filter hit).card := by
    calc
      _ = ∑ r ∈ R, ((branchCount G T A r - 1) + 1) := by simp [Finset.sum_add_distrib]
      _ = ∑ r ∈ R, (p r + if hit r then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hpos := branch_pos hc hn A (Finset.mem_sdiff.mp hr).2
        change branchCount G T A r - 1 + 1 = branchCount G T A r
        omega
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole]
  rw [Finset.sum_add_distrib] at hs
  have htree := ht.card_edgeFinset
  have hcard : R.card + T.card = n := by
    simpa [R] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  simp only [Fintype.card_fin] at htree
  change T.card ≤ A.card + ∑ r ∈ R, (branchCount G T A r - 1)
  omega

theorem empty_deficit (ht : G.IsTree) (hc : CoverPromise.IsVertexCover G T)
    (hi : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) (hn : ∀ i, ∃ j, G.Adj i j) :
    (∑ r ∈ Finset.univ \ T, (G.degree r - 1)) + 1 = T.card := by
  classical
  let R := Finset.univ \ T
  have hsum : (∑ r ∈ R, (G.degree r - 1)) + R.card = G.edgeFinset.card := by
    rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' (bipartition hc hi)]
    calc
      _ = ∑ r ∈ R, ((G.degree r - 1) + 1) := by simp [Finset.sum_add_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        obtain ⟨j,hj⟩ := hn r
        have hpos : 0 < G.degree r := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨j, by simpa using hj⟩
        omega
  have hcard : R.card + T.card = n := by
    simpa [R] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have htree := ht.card_edgeFinset
  simp only [Fintype.card_fin] at htree
  change (∑ r ∈ R, (G.degree r - 1)) + 1 = T.card
  omega

end GraphFacts
end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Net

theorem circuit_read_port {n : ℕ} {C : Circuit} (hf : FanInTwo C) (hr : NoNot.Reduced n C)
    (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not) (j : Fin C.size) (w : Wire n C.size)
    (hw : w.val ∈ (C.gates[j.val]'j.isLt).inputs) :
    ∃ p, (circuitNet n C hf hr hn).src j p = w := by
  obtain ⟨_,a,b,_,_,_,hs⟩ := binary_gate n C hf hr hn j.val j.isLt
  simp [hs] at hw
  rcases hw with ha|hb
  · exact ⟨false,Fin.ext (by simpa [circuitNet,parentWire,hs] using ha.symm)⟩
  · exact ⟨true,Fin.ext (by simpa [circuitNet,parentWire,hs] using hb.symm)⟩

theorem circuit_wires_used {n : ℕ} {C : Circuit} (hf : FanInTwo C) (hr : NoNot.Reduced n C)
    (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not) (hg : C.gates ≠ [])
    (he : ∀ i : Fin n, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i false) ≠ circuitFun n C (Function.update x i true))
    (w : Wire n C.size) (hw : w.val ≠ C.output) :
    0 < (circuitNet n C hf hr hn).deg w := by
  classical
  let D := circuitNet n C hf hr hn
  change 0 < (D.ports w).card
  apply Finset.card_pos.mpr
  suffices h : ∃ j : Fin C.size, w.val ∈ (C.gates[j.val]'j.isLt).inputs by
    obtain ⟨j,hj⟩ := h
    obtain ⟨p,hp⟩ := circuit_read_port hf hr hn j w hj
    exact ⟨(j,p), by simp [Net.ports,D,hp]⟩
  rcases cases_wire w with ⟨i,rfl⟩ | ⟨j,rfl⟩
  · by_contra! h
    obtain ⟨x,hx⟩ := he i
    have hol := hr.2.2.1 hg
    have hno := NoNot.wire_indep_of_not_read C i (fun k hk => h ⟨k,hk⟩)
    exact hx (hno C.gates.length (le_refl _) C.output (by omega) (Ne.symm hw) x)
  · have hnk : ∀ g ∈ C.gates, NoNot.NOkGate g :=
      fun g hm => ⟨hf g hm,fun ho => False.elim (hn g hm ho)⟩
    rcases NoNot.reduced_no_dead C hnk hr j.val j.isLt with ho | ⟨k,hk,_,hm⟩
    · exact False.elim (hw ho.symm)
    · exact ⟨⟨k,hk⟩,hm⟩

theorem circuit_output_unused {n : ℕ} {C : Circuit} (hf : FanInTwo C) (hr : NoNot.Reduced n C)
    (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not) (hg : C.gates ≠ [])
    (w : Wire n C.size) (hw : w.val = C.output) : (circuitNet n C hf hr hn).deg w = 0 := by
  classical
  simp only [Net.deg, Net.ports, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _
  intro h
  have hh := congrArg Fin.val h
  have hl := (circuitNet n C hf hr hn).lt_src p.1 p.2
  have hol := hr.2.2.1 hg
  have hj : p.1.val < C.gates.length := p.1.isLt
  omega

theorem excess_balance {n m : ℕ} (D : Net n m) (o : Wire n m)
    (ho : D.deg o = 0) (hu : ∀ w, w ≠ o → 0 < D.deg w) :
    (∑ w, (D.deg w - 1)) + (n+m-1) = 2*m := by
  classical
  let s := (Finset.univ : Finset (Wire n m)).erase o
  have hs : s.card = n+m-1 := by simp [s]
  have hh : ∑ w ∈ s, ((D.deg w - 1) + 1) = ∑ w ∈ s, D.deg w := by
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have hpos := hu w (Finset.mem_erase.mp hw).1
    omega
  rw [Finset.sum_add_distrib] at hh
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at hh
  have hx := Finset.sum_erase_add (s := (Finset.univ : Finset (Wire n m)))
    (fun w => D.deg w - 1) (Finset.mem_univ o)
  have hy := Finset.sum_erase_add (s := (Finset.univ : Finset (Wire n m)))
    D.deg (Finset.mem_univ o)
  change (∑ w ∈ s, _) + _ = _ at hx hy
  rw [ho] at hx hy
  have hd := D.deg_total
  omega

theorem graph_essential {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (he : ∀ i, ∃ p, G.Adj i p)
    (heval : circuitFun n C = NoNot.forestFun0 G ∅) :
    ∀ i : Fin n, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i false) ≠ circuitFun n C (Function.update x i true) := by
  intro i
  obtain ⟨p,hp⟩ := he i
  rw [heval]
  exact NoNot.forestFun0_dep_edge G ∅ (by simp) i p hp

end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux.Net

namespace Routes
variable {n m : ℕ} {D : Net n m} {s : Wire n m} (H : Routes D s)

theorem outs_subset (v : Wire n m) : H.outs v ⊆ D.ports v := by
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩

theorem outdeg_le (v : Wire n m) : H.outdeg v ≤ D.deg v := Finset.card_le_card (H.outs_subset v)

def cost (v : Wire n m) : ℕ := if v ∈ H.verts then H.outdeg v - 1 else 0

theorem total_cost : (∑ v, H.cost v) = ∑ v ∈ H.verts, (H.outdeg v - 1) := by
  classical
  simp [cost]

theorem cost_le (v : Wire n m) : H.cost v ≤ D.deg v - 1 := by
  unfold cost
  split
  · exact Nat.sub_le_sub_right (H.outdeg_le v) 1
  · omega

theorem cost_balance (hne : H.ends.Nonempty) :
    (∑ v, H.cost v) = (H.ends.card - 1) + ∑ v ∈ H.verts, (H.indeg v - 1) := by
  have h := H.balance hne
  have := Finset.card_pos.mpr hne
  rw [H.total_cost]
  omega

end Routes

namespace Ledger

variable {n m : ℕ} {D : Net n m} {R : Finset (Fin n)}
variable (H : ∀ r : Fin n, Routes D (raw r)) (supp : Wire n m → Finset (Fin n))

def BranchSupport (R : Finset (Fin n)) : Prop :=
  ∀ r ∈ R, ∀ v ∈ (H r).verts, 1 < (H r).outdeg v → supp v = {r}

theorem positive_support (hb : BranchSupport H supp R) {r v} (hr : r ∈ R)
    (hp : 0 < (H r).cost v) : supp v = {r} := by
  by_cases hv : v ∈ (H r).verts
  · have h := hp
    simp [Routes.cost,hv] at h
    exact hb r hr v hv (by omega)
  · simp [Routes.cost,hv] at hp

theorem row_zero_of_mem (hb : BranchSupport H supp R) {r i v} (hi : i ∈ R)
    (hrv : r ∈ supp v) (hne : i ≠ r) : (H i).cost v = 0 := by
  by_contra! h
  have hh := positive_support H supp hb hi (Nat.pos_of_ne_zero h)
  rw [hh] at hrv
  exact hne (Finset.mem_singleton.mp hrv).symm

theorem one_row (hb : BranchSupport H supp R) {r v} (hr : r ∈ R) (hrv : r ∈ supp v) :
    (∑ i ∈ R, (H i).cost v) = (H r).cost v := by
  apply Finset.sum_eq_single_of_mem r hr
  intro i hi hne
  exact row_zero_of_mem H supp hb hi hrv hne

theorem wire_charge (hb : BranchSupport H supp R) (v : Wire n m) :
    (∑ r ∈ R, (H r).cost v) ≤ D.deg v - 1 := by
  by_cases h : ∃ r ∈ R, 0 < (H r).cost v
  · obtain ⟨r,hr,hp⟩ := h
    have hsup := positive_support H supp hb hr hp
    rw [one_row H supp hb hr (by simp [hsup] : r ∈ supp v)]
    exact (H r).cost_le v
  · push Not at h
    have hz : (∑ r ∈ R, (H r).cost v) = 0 := Finset.sum_eq_zero (fun r hr => Nat.eq_zero_of_le_zero (h r hr))
    omega

theorem total_charge (hb : BranchSupport H supp R)
    (he : ∀ r ∈ R, (H r).ends.Nonempty) (A : Finset (Fin n)) (owner : Fin n → Wire n m)
    (hinj : Set.InjOn owner A) (hdark : ∀ c ∈ A, supp (owner c) = ∅)
    (hfork : ∀ c ∈ A, 2 ≤ D.deg (owner c)) :
    A.card + (∑ r ∈ R, ((H r).ends.card - 1)) ≤ ∑ v, (D.deg v - 1) := by
  classical
  let O := A.image owner
  have hcard : O.card = A.card := Finset.card_image_of_injOn hinj
  have hn : ∀ v, (if v ∈ O then 1 else 0) + (∑ r ∈ R, (H r).cost v) ≤ D.deg v - 1 := by
    intro v
    by_cases hv : v ∈ O
    · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
      have hz : (∑ r ∈ R, (H r).cost (owner c)) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        by_contra! hp
        have hh := positive_support H supp hb hr (Nat.pos_of_ne_zero hp)
        simp [hdark c hc] at hh
      simp only [ite_eq_left hv, hz, Nat.add_zero]
      have := hfork c hc
      omega
    · simpa [hv] using wire_charge H supp hb v
  have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hn v)
  have hcross : (∑ v, ∑ r ∈ R, (H r).cost v) = ∑ r ∈ R, ∑ v, (H r).cost v := Finset.sum_comm
  have howner : (∑ v, if v ∈ O then 1 else 0 : ℕ) = O.card := by simp
  rw [Finset.sum_add_distrib,howner,hcard,hcross] at h
  have hrow : (∑ r ∈ R, ((H r).ends.card - 1)) ≤ ∑ r ∈ R, ∑ v, (H r).cost v := by
    exact Finset.sum_le_sum (fun r hr => by rw [(H r).cost_balance (he r hr)]; omega)
  omega

theorem tight_cells (hb : BranchSupport H supp R) (he : ∀ r ∈ R, (H r).ends.Nonempty)
    (ht : (∑ r ∈ R, ((H r).ends.card - 1)) = ∑ v, (D.deg v - 1)) :
    (∀ v, (∑ r ∈ R, (H r).cost v) = D.deg v - 1) ∧
    (∀ r ∈ R, ∀ v ∈ (H r).verts, (H r).indeg v ≤ 1) := by
  classical
  have hrow : ∀ r ∈ R, (H r).ends.card - 1 ≤ ∑ v, (H r).cost v := by
    intro r hr
    rw [(H r).cost_balance (he r hr)]
    omega
  have hlow := Finset.sum_le_sum hrow
  have hhi := Finset.sum_le_sum (s := Finset.univ) (fun v _ => wire_charge H supp hb v)
  have hcross : (∑ v, ∑ r ∈ R, (H r).cost v) = ∑ r ∈ R, ∑ v, (H r).cost v := Finset.sum_comm
  constructor
  · intro v
    by_contra! hx
    have hlt : (∑ v, ∑ r ∈ R, (H r).cost v) < ∑ v, (D.deg v - 1) :=
      Finset.sum_lt_sum (fun w _ => wire_charge H supp hb w)
        ⟨v,Finset.mem_univ _,lt_of_le_of_ne (wire_charge H supp hb v) hx⟩
    omega
  · intro r hr v hv
    by_contra! hx
    have hpos : 0 < ∑ w ∈ (H r).verts, ((H r).indeg w - 1) := by
      have hh := Finset.single_le_sum (f := fun w => (H r).indeg w - 1) (fun _ _ => Nat.zero_le _) hv
      omega
    have hlt : (∑ r ∈ R, ((H r).ends.card - 1)) < ∑ r ∈ R, ∑ v, (H r).cost v := by
      apply Finset.sum_lt_sum hrow
      exact ⟨r,hr,by rw [(H r).cost_balance (he r hr)]; omega⟩
    omega

theorem tight_fork (hb : BranchSupport H supp R) (he : ∀ r ∈ R, (H r).ends.Nonempty)
    (ht : (∑ r ∈ R, ((H r).ends.card - 1)) = ∑ v, (D.deg v - 1))
    {v} (hv : 1 < D.deg v) : ∃ r ∈ R, supp v = {r} := by
  have hh := (tight_cells H supp hb he ht).1 v
  by_contra! hn
  have hz : (∑ r ∈ R, (H r).cost v) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_contra! hp
    exact hn r hr (positive_support H supp hb hr (Nat.pos_of_ne_zero hp))
  omega

theorem tight_exits (hb : BranchSupport H supp R) (he : ∀ r ∈ R, (H r).ends.Nonempty)
    (ht : (∑ r ∈ R, ((H r).ends.card - 1)) = ∑ v, (D.deg v - 1))
    {r v} (hr : r ∈ R) (hv : v ∈ (H r).verts) (hne : v ∉ (H r).ends)
    (hrv : r ∈ supp v) : (H r).outs v = D.ports v := by
  have hh := (tight_cells H supp hb he ht).1 v
  rw [one_row H supp hb hr hrv] at hh
  simp only [Routes.cost,ite_eq_left hv] at hh
  have hn := ((H r).out_zero v hv).not.mpr hne
  have hl := (H r).outdeg_le v
  apply Finset.eq_of_subset_of_card_le ((H r).outs_subset v)
  change D.deg v ≤ (H r).outdeg v
  omega

end Ledger
end PEqualNP.Outside.L_meta_173_aux.Net

namespace PEqualNP.Outside.L_meta_173_aux

open PEqualNP.MetaComplexity

namespace GraphLedger
open Net

variable {n m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {T A : Finset (Fin n)} {D : Net n m}

theorem branch_empty_eq_degree (hc : CoverPromise.IsVertexCover G T)
    (hi : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) {r : Fin n} (hr : r ∈ Finset.univ \ T) :
    GraphFacts.branchCount G T ∅ r = G.degree r := by
  have hsub := SimpleGraph.isBipartiteWith_neighborFinset_subset' (GraphFacts.bipartition hc hi) hr
  simp [GraphFacts.branchCount,Finset.inter_eq_left.mpr hsub]

theorem close (ht : G.IsTree) (hc : CoverPromise.IsVertexCover G T)
    (hi : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) (hn : ∀ i, ∃ j, G.Adj i j) (hAT : A ⊆ T)
    (H : ∀ r : Fin n, Routes D (raw r)) (supp : Wire n m → Finset (Fin n))
    (hb : Ledger.BranchSupport H supp (Finset.univ \ T))
    (hcount : ∀ r ∈ Finset.univ \ T, (H r).ends.card = GraphFacts.branchCount G T A r)
    (owner : Fin n → Wire n m) (hinj : Set.InjOn owner A)
    (hdark : ∀ c ∈ A, supp (owner c) = ∅) (hfork : ∀ c ∈ A, 2 ≤ D.deg (owner c))
    (hbudget : (∑ v, (D.deg v - 1)) + 1 ≤ T.card) :
    A = ∅ ∧ (∑ r ∈ Finset.univ \ T, ((H r).ends.card - 1)) = ∑ v, (D.deg v - 1) := by
  classical
  let R := Finset.univ \ T
  have hends : ∀ r ∈ R, (H r).ends.Nonempty := by
    intro r hr
    apply Finset.card_pos.mp
    rw [hcount r hr]
    exact GraphFacts.branch_pos hc hn A (Finset.mem_sdiff.mp hr).2
  have hpaid := Ledger.total_charge H supp hb hends A owner hinj hdark hfork
  have hsum : (∑ r ∈ R, ((H r).ends.card - 1)) = ∑ r ∈ R, (GraphFacts.branchCount G T A r - 1) :=
    Finset.sum_congr rfl (fun r hr => congrArg (· - 1) (hcount r hr))
  have hEmpty : A = ∅ := by
    by_contra h
    have hlow := GraphFacts.branch_deficit ht hc hi hn hAT (Finset.nonempty_iff_ne_empty.mpr h)
    change T.card ≤ A.card + ∑ r ∈ R, (GraphFacts.branchCount G T A r - 1) at hlow
    change A.card + (∑ r ∈ R, ((H r).ends.card - 1)) ≤ ∑ v, (D.deg v - 1) at hpaid
    omega
  refine ⟨hEmpty,?_⟩
  have hz := GraphFacts.empty_deficit ht hc hi hn
  change (∑ r ∈ R, (G.degree r - 1)) + 1 = T.card at hz
  have heq : (∑ r ∈ R, ((H r).ends.card - 1)) = ∑ r ∈ R, (G.degree r - 1) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [hcount r hr,hEmpty,branch_empty_eq_degree hc hi hr]
  change A.card + (∑ r ∈ R, ((H r).ends.card - 1)) ≤ ∑ v, (D.deg v - 1) at hpaid
  change (∑ r ∈ R, ((H r).ends.card - 1)) = ∑ v, (D.deg v - 1)
  omega

end GraphLedger
end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux
open Net
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {T : Finset (Fin n)}

def edgeValue (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :=
  decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

theorem gates_nonempty (hE : ∃ u v, G.Adj u v)
    (heval : circuitFun n C = edgeValue G) : C.gates ≠ [] := by
  intro hn
  have hz (x : Fin n → Bool) : circuitFun n C x = (List.ofFn x).getD C.output false := by
    simp [circuitFun,Circuit.eval,Circuit.wires,hn]
  by_cases ho : C.output < n
  · let c : Fin n := ⟨C.output,ho⟩
    have hv := hz (onSet {c})
    rw [heval,NoNot.ofFn_getD_lt _ _ _ ho] at hv
    have hh : ∃ u v, G.Adj u v ∧ onSet {c} u = true ∧ onSet {c} v = true := by
      apply of_decide_eq_true
      exact hv.trans (by simp [onSet,c])
    obtain ⟨u,v,hu,h1,h2⟩ := hh
    obtain rfl : u=c := by simpa [onSet] using h1
    obtain rfl : v=c := by simpa [onSet] using h2
    exact G.loopless.irrefl _ hu
  · have hv := hz (fun _ => true)
    rw [heval,List.getD_eq_default _ _ (by simp; omega)] at hv
    simp [edgeValue,hE] at hv

theorem edge_nonconst (hE : ∃ u v, G.Adj u v) (heval : circuitFun n C = edgeValue G) :
    ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y := by
  exact ⟨fun _ => false,fun _ => true,by simp [heval,edgeValue,hE]⟩

noncomputable def fromTree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (C : Circuit) (hf : FanInTwo C) (hr : NoNot.Reduced n C)
    (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not)
    (hconn : G.Connected) (hacyc : G.IsAcyclic) (he : 2 ≤ G.edgeFinset.card)
    (hc : CoverPromise.IsVertexCover G T)
    (hq : ∀ S : Finset _, CoverPromise.IsVertexCover G S → S.card = T.card → S = T)
    (hi : ∀ u ∈ T, ∀ v ∈ T, ¬G.Adj u v)
    (heval : circuitFun n C = edgeValue G) : BipartiteNet (circuitNet n C hf hr hn) := by
  classical
  have hneigh := GraphFacts.hasNeighbor hconn he
  have hE : ∃ u v, G.Adj u v := by
    obtain ⟨e,hem⟩ := Finset.card_pos.mp (show 0 < G.edgeFinset.card by omega)
    obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    exact ⟨u,v,by simpa using hem⟩
  have hC := gates_nonempty hE heval
  have hout := hr.2.2.1 hC
  let o : Wire n C.size := ⟨C.output,by change _ < n+C.gates.length; omega⟩
  refine {centers := T,nbr := fun c => G.neighborFinset c,output := o,last := ?_,live := ?_,sink := ?_,
          across := ?_,large := ?_,distinguish := ?_,thin := ?_,result := ?_}
  · intro z
    have hz : z.val < n+C.gates.length := z.isLt
    change z.val ≤ C.output
    omega
  · intro z hz
    apply circuit_wires_used hf hr hn hC _ z (fun hh => hz (Fin.ext hh))
    apply graph_essential G C hneigh
    rw [heval]; funext x; simp [edgeValue,NoNot.forestFun0]
  · exact circuit_output_unused hf hr hn hC o rfl
  · intro c hct r hrc
    exact (GraphFacts.opposite hc hi ((G.mem_neighborFinset _ _).mp hrc)).1 hct
  · exact fun _ hct => GraphFacts.centerDegree hc hi hq hneigh hct
  · intro c hct d hd hcd
    simpa using GraphFacts.separate hacyc hcd (GraphFacts.centerDegree hc hi hq hneigh hct)
  · intro c hct d hd hcd r hcr hdr s hcs hds
    exact GraphFacts.common_unique hacyc hcd (by simpa using hcr) (by simpa using hdr)
      (by simpa using hcs) (by simpa using hds)
  · intro S
    rw [show (circuitNet n C hf hr hn).base (onSet S) o = circuitFun n C (onSet S) from
      circuitNet_eval n C hf hr hn (onSet S) o,heval]
    simp only [edgeValue,onSet,decide_eq_true_eq,SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨u,v,hu,hs,ht⟩
      rcases hc u v hu with h|h
      · exact ⟨u,h,hs,v,hu,ht⟩
      · exact ⟨v,h,ht,u,hu.symm,hs⟩
    · rintro ⟨c,_,hc',r,hr,hs⟩
      exact ⟨c,r,hr,hc',hs⟩

theorem fork_budget (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (C : Circuit) (hminimum : IsMinimalCircuit n C) (hr : NoNot.Reduced n C)
    (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not)
    (ht : G.IsTree) (hc : CoverPromise.IsVertexCover G T) (hE : ∃ u v, G.Adj u v)
    (heval : circuitFun n C = edgeValue G) (B : BipartiteNet (circuitNet n C hminimum.1 hr hn)) :
    (∑ w, ((circuitNet n C hminimum.1 hr hn).deg w - 1)) + 1 ≤ T.card := by
  classical
  obtain ⟨Q,hQ,hsize,hov⟩ := Core.EdgeUpper.edge_upper n G T hE hc
  have hfun : circuitFun n Q = circuitFun n C := by
    rw [heval]; funext x; exact hov x
  have msize := (hminimum.2 Q hQ hfun).trans hsize
  have hb := excess_balance _ B.output B.sink B.live
  have hncount := ht.card_edgeFinset
  simp only [Fintype.card_fin] at hncount
  have hne : 0 < C.size := List.length_pos_iff.mpr (gates_nonempty hE heval)
  have hT : 0 < T.card := by
    obtain ⟨u,v,hv⟩ := hE
    rcases hc u v hv with h|h <;> exact Finset.card_pos.mpr ⟨_,h⟩
  omega

theorem no_raw_alias (n : ℕ) (C : Circuit) (hf : FanInTwo C) (hr : NoNot.Reduced n C)
    (hn : ∀ g ∈ C.gates, g.op ≠ GateOp.not) (j : Fin C.size) (i : Fin n) :
    ∃ x, (circuitNet n C hf hr hn).base x (site j) ≠ x i := by
  have hi := i.isLt
  obtain ⟨x,h⟩ := hr.2.1 i.val j.val (by omega) j.isLt
  refine ⟨x,?_⟩
  have hg := circuitNet_eval n C hf hr hn x (site j)
  have hr' := circuitNet_eval n C hf hr hn x (raw i)
  rw [eval_raw _ _ _ _ rfl] at hr'
  exact fun hh => h (hr'.symm.trans (hh.symm.trans hg))

end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux
open Net
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n m : ℕ} {D : Net n m}

namespace BipartiteNet

structure Tight (B : BipartiteNet D) : Prop where
  all_actual : B.other = ∅
  nonempty : ∀ r ∈ B.right, (B.routes r).ends.Nonempty
  fork : ∀ w, 1 < D.deg w → ∃ r ∈ B.right, B.support w = {r}
  incoming : ∀ r ∈ B.right, ∀ w ∈ (B.routes r).verts, (B.routes r).indeg w ≤ 1
  exits : ∀ r ∈ B.right, ∀ w ∈ (B.routes r).verts, w ∉ (B.routes r).ends →
    ∀ e ∈ D.ports w, e ∈ (B.routes r).arcs

theorem tree_endpoints (B : BipartiteNet D) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hN : ∀ c, B.nbr c = G.neighborFinset c) (r : Fin n) :
    (B.routes r).ends.card = GraphFacts.branchCount G B.centers B.other r := by
  classical
  rw [B.ends_card]
  have ha : (B.actuals.filter fun c => r ∈ B.nbr c) =
      G.neighborFinset r ∩ (B.centers \ B.other) := by
    ext c
    simp [hN,other,mem_actual,SimpleGraph.adj_comm (G := G) (u := c) (v := r)]
    tauto
  have hb : B.hits r = G.neighborFinset r ∩ B.other := by
    ext c
    simp [hits,hN,SimpleGraph.adj_comm (G := G) (u := c) (v := r),and_comm]
  rw [ha,hb]
  rfl

theorem tree_tight (B : BipartiteNet D) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hN : ∀ c, B.nbr c = G.neighborFinset c)
    (ht : G.IsTree) (hc : CoverPromise.IsVertexCover G B.centers)
    (hi : ∀ u ∈ B.centers, ∀ v ∈ B.centers, ¬G.Adj u v)
    (hn : ∀ i, ∃ j, G.Adj i j)
    (hbudget : (∑ w, (D.deg w-1))+1 ≤ B.centers.card) : Tight B := by
  classical
  have hb : Ledger.BranchSupport B.routes B.support B.right :=
    fun r _ w _ hw => B.branch_label r w hw
  have hcount := B.tree_endpoints G hN
  have hsub : B.other ⊆ B.centers := Finset.sdiff_subset
  have htight := GraphLedger.close ht hc hi hn hsub B.routes B.support hb
    (fun r _ => hcount r) D.firstOwner (fun _ hx _ hy h => B.other_owner_inj hx hy h)
    (fun c h => B.empty_support (B.mem_other.mp h).1 (D.stem c)) B.other_owner_fork hbudget
  have he : ∀ r ∈ B.right, (B.routes r).ends.Nonempty := by
    intro r hr
    apply Finset.card_pos.mp
    rw [hcount r]
    exact GraphFacts.branch_pos hc hn B.other (Finset.mem_sdiff.mp hr).2
  refine ⟨htight.1,he,fun _ h => Ledger.tight_fork _ _ hb he htight.2 h,
    (Ledger.tight_cells _ _ hb he htight.2).2,?_⟩
  intro r hr w hw ht' e hmem
  have hh := Ledger.tight_exits _ _ hb he htight.2 hr hw ht' (B.tight_node htight.1 hw)
  rw [←hh] at hmem
  exact (Finset.mem_filter.mp hmem).1

end BipartiteNet
end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux

theorem no_not_conjunct : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), G.Connected → G.IsAcyclic → 2 ≤ G.edgeFinset.card → PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → T.card ≤ S.card) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → S.card = T.card → S = T) → (∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) → PEqualNP.MetaComplexity.IsMinimalCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) := by
  classical
  intro n G _ T C hconn hacyc hecard hT hmin huniq hind hminimal hfun
  have hne : G ≠ ⊥ := by
    intro h
    have hz : G.edgeFinset.card = 0 :=
      Finset.card_eq_zero.mpr (G.edgeFinset_eq_empty.mpr h)
    omega
  obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  letI : Nontrivial (Fin n) := ⟨⟨u, v, G.ne_of_adj huv⟩⟩
  have hex : ∃ u v, G.Adj u v := ⟨u, v, huv⟩
  have hnc : ∃ x y : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n C x ≠
      PEqualNP.MetaComplexity.circuitFun n C y := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    simp [hfun, hex]
  have hred := reduced_min n C hminimal hnc
  obtain ⟨D, hD, hsizeD, hevalD⟩ := Core.EdgeUpper.edge_upper n G T hex hT
  have hDC : PEqualNP.MetaComplexity.circuitFun n D =
      PEqualNP.MetaComplexity.circuitFun n C := by
    funext x
    exact (hevalD x).trans (congrFun hfun x).symm
  have hsize : C.size ≤ G.edgeFinset.card + T.card - 1 :=
    (hminimal.2 D hD hDC).trans hsizeD
  apply NoNot.forest_no_not n T.card G ∅ C hacyc
  · simp
  · exact Or.inr hex
  · intro i
    exact Or.inr (hconn.preconnected.exists_adj_of_nontrivial i)
  · exact ⟨T, fun _ _ h => hT _ _ h, rfl⟩
  · intro S hS
    exact hmin S (fun _ _ h => hS h)
  · exact hminimal.1
  · simpa using hfun
  · simp only [Finset.card_empty, zero_add]
    omega
  · exact hred

end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux
open Net
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem final_glue (finish : ∀ {n m : ℕ} {D : Net n m} (B : BipartiteNet D),
    B.Tight → ∀ j : Fin m,
    (∃ c ∈ B.centers, ∃ A : Finset (Fin n), A.Nonempty ∧ A ⊆ B.nbr c ∧
      ∀ x : Fin n → Bool, D.base x (site j) = decide (∃ a ∈ A, x a = true)) ∨
    (∃ P : Finset (Fin n), P.Nonempty ∧ P ⊆ B.centers ∧ ∀ x : Fin n → Bool,
      D.base x (site j) = decide (∃ c ∈ P, x c = true ∧ ∃ a ∈ B.nbr c, x a = true))) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), G.Connected → G.IsAcyclic → 2 ≤ G.edgeFinset.card → PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → T.card ≤ S.card) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → S.card = T.card → S = T) → (∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) → PEqualNP.MetaComplexity.IsMinimalCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ t : ℕ, t < C.size → ((∃ c ∈ T, ∃ A : Finset (Fin n), A.Nonempty ∧ (∀ a ∈ A, G.Adj c a) ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = decide (∃ a ∈ A, x a = true)) ∨ (∃ P : Finset (Fin n), P.Nonempty ∧ P ⊆ T ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = decide (∃ c ∈ P, x c = true ∧ ∃ a : Fin n, G.Adj c a ∧ x a = true))) := by
  classical
  intro n G inst T C hconn hacyc he hc hmin huniq hi hminimum hfun
  have htree : G.IsTree := ⟨hconn,hacyc⟩
  have hE : ∃ u v, G.Adj u v := by
    obtain ⟨e,hem⟩ := Finset.card_pos.mp (show 0<G.edgeFinset.card by omega)
    obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    exact ⟨u,v,by simpa using hem⟩
  have hval : circuitFun n C = edgeValue G := hfun
  have hr : NoNot.Reduced n C := reduced_min n C hminimum (edge_nonconst hE hval)
  have hn := no_not_conjunct n G T C hconn hacyc he hc hmin huniq hi hminimum hfun
  refine ⟨hn,?_⟩
  let D := circuitNet n C hminimum.1 hr hn
  let B : BipartiteNet D := fromTree G T C hminimum.1 hr hn hconn hacyc he hc huniq hi hval
  have hN : ∀ c, B.nbr c = G.neighborFinset c := fun _ => rfl
  have hBasis : B.centers=T := rfl
  have hh := fork_budget G T C hminimum hr hn htree hc hE hval B
  have ht : B.Tight := B.tree_tight G hN htree hc hi (GraphFacts.hasNeighbor hconn he) hh
  intro t ht'
  let j : Fin C.size := ⟨t,ht'⟩
  have hw (x : Fin n → Bool) : D.base x (site j) = (C.wires (List.ofFn x)).getD (n+t) false :=
    circuitNet_eval n C hminimum.1 hr hn x (site j)
  obtain ⟨c,hmem,A,hne,hsub,hvalA⟩|⟨P,hne,hsub,hvalP⟩ := finish B ht j
  · refine Or.inl ⟨c,hBasis ▸ hmem,A,hne,?_,fun x => (hw x).symm.trans (hvalA x)⟩
    intro a ha
    exact (G.mem_neighborFinset c a).mp (hN c ▸ hsub ha)
  · refine Or.inr ⟨P,hne,hBasis ▸ hsub,fun x => ?_⟩
    rw [←hw,hvalP]
    simp only [hN,SimpleGraph.mem_neighborFinset]

end PEqualNP.Outside.L_meta_173_aux

namespace PEqualNP.Outside.L_meta_173_aux.FinishJoin

open Net

variable {n m : ℕ} {D : Net n m}

def Dep (B : BipartiteNet D) (w : Wire n m) : Prop :=
  ∃ c ∈ B.centers, Nonempty (Path D (raw c) w)

def PureGate (B : BipartiteNet D) (w : Wire n m) : Prop :=
  ∃ c ∈ B.centers, ∃ A : Finset (Fin n), A.Nonempty ∧ A ⊆ B.nbr c ∧
    ∀ x : Fin n → Bool, D.base x w = decide (∃ a ∈ A, x a = true)

def StarGate (B : BipartiteNet D) (w : Wire n m) : Prop :=
  ∃ P : Finset (Fin n), P.Nonempty ∧ P ⊆ B.centers ∧ ∀ x : Fin n → Bool,
    D.base x w = decide (∃ c ∈ P, x c = true ∧ ∃ a ∈ B.nbr c, x a = true)

private theorem raw_of_dep (B : BipartiteNet D) (i : Fin n) (hd : Dep B (raw i)) : i ∈ B.centers := by
  obtain ⟨c,hc,⟨p⟩⟩ := hd
  by_cases he : (raw i : Wire n m) = raw c
  · have hic : i = c := Fin.ext (congrArg (fun w : Wire n m => w.val) he)
    exact hic ▸ hc
  · obtain ⟨e,_,hh⟩ := p.has_in p.self_mem he
    have hv := congrArg Fin.val hh
    change n + e.1.val = i.val at hv
    have := i.isLt
    omega

private theorem join_stars (B : BipartiteNet D) (j : Fin m) (ho : D.isAnd j = false)
    (hl : StarGate B (D.src j false)) (hr : StarGate B (D.src j true)) : StarGate B (site j) := by
  obtain ⟨L,hL,hLc,hLv⟩ := hl
  obtain ⟨R,_,hRc,hRv⟩ := hr
  refine ⟨L ∪ R,hL.mono (Finset.subset_union_left),Finset.union_subset hLc hRc,?_⟩
  intro x
  rw [base_site,hLv,hRv]
  apply Bool.eq_iff_iff.mpr
  simp only [combine,ho,Bool.false_eq_true,ite_false,Bool.or_eq_true,decide_eq_true_eq,
    Finset.mem_union]
  constructor
  · rintro (⟨c,hc,h⟩|⟨c,hc,h⟩)
    · exact ⟨c,Or.inl hc,h⟩
    · exact ⟨c,Or.inr hc,h⟩
  · rintro ⟨c,hc,h⟩
    exact hc.elim (fun hc => Or.inl ⟨c,hc,h⟩) (fun hc => Or.inr ⟨c,hc,h⟩)

theorem finishGates (B : BipartiteNet D)
    (hpure : ∀ j : Fin m, ¬Dep B (site j) → PureGate B (site j))
    (hstar : ∀ j : Fin m, Dep B (site j) → (∃ b, ¬Dep B (D.src j b)) → StarGate B (site j))
    (hor : ∀ j : Fin m, Dep B (D.src j false) → Dep B (D.src j true) → D.isAnd j = false)
    (hcenter : ∀ (j : Fin m) (b : Bool) (c : Fin n), c ∈ B.centers →
      D.src j b = raw c → D.isAnd j = true) :
    ∀ j : Fin m, PureGate B (site j) ∨ StarGate B (site j) := by
  classical
  have allw (w : Wire n m) : Dep B w → (∃ c ∈ B.centers, w = raw c) ∨ StarGate B w := by
    induction w using D.induction_wire with
    | hin i => intro hd; exact Or.inl ⟨i,raw_of_dep B i hd,rfl⟩
    | hgate j ihl ihr =>
      intro hd
      right
      by_cases hl : Dep B (D.src j false)
      · by_cases hr : Dep B (D.src j true)
        · have hgate := hor j hl hr
          rcases ihl hl with ⟨c,hc,eq⟩|sl
          · have bad := hcenter j false c hc eq
            simp [hgate] at bad
          rcases ihr hr with ⟨c,hc,eq⟩|sr
          · have bad := hcenter j true c hc eq
            simp [hgate] at bad
          exact join_stars B j hgate sl sr
        · exact hstar j hd ⟨true,hr⟩
      · exact hstar j hd ⟨false,hl⟩
  intro j
  by_cases hd : Dep B (site j)
  · rcases allw _ hd with ⟨c,_,eq⟩|hs
    · have hv := congrArg Fin.val eq
      change n + j.val = c.val at hv
      have := c.isLt
      omega
    · exact Or.inr hs
  · exact Or.inl (hpure j hd)

end PEqualNP.Outside.L_meta_173_aux.FinishJoin

namespace PEqualNP.Outside.L_meta_173_aux.Finish
open Net

variable {n m : ℕ} {D : Net n m} (B : BipartiteNet D)

structure Tight : Prop where
  actual : B.other = ∅
  ends : ∀ r ∈ B.right, (B.routes r).ends.Nonempty
  fork : ∀ w, 1 < D.deg w → ∃ r ∈ B.right, B.support w = {r}
  incoming : ∀ r ∈ B.right, ∀ w ∈ (B.routes r).verts, (B.routes r).indeg w ≤ 1
  exhaust : ∀ r ∈ B.right, ∀ w ∈ (B.routes r).verts, w ∉ (B.routes r).ends →
    ∀ e ∈ D.ports w, e ∈ (B.routes r).arcs

def Dep (w : Wire n m) : Prop :=
  ∃ c ∈ B.centers, Nonempty (Path D (raw c) w)

def fromLine {s w : Wire n m} : Line D s w → Path D s w
  | .first => .refl
  | .step j b q _ => .step j b (fromLine q)

theorem center_line (h : Tight B) {c : Fin n} (hc : c ∈ B.centers) {w : Wire n m}
    (p : Path D (raw c) w) : Nonempty (Line D (raw c) w) := by
  induction p with
  | refl => exact ⟨.first⟩
  | step j b p ih =>
    obtain ⟨q⟩ := ih
    have empty := B.empty_support hc q
    have deg : D.deg (D.src j b) = 1 := by
      have pos : 0 < D.deg (D.src j b) := Finset.card_pos.mpr ⟨(j,b),by simp [ports]⟩
      by_contra! hn
      obtain ⟨r,_,e⟩ := h.fork _ (by omega : 1 < D.deg (D.src j b))
      rw [empty] at e; simp at e
    exact ⟨.step j b q (onlyExit_of_deg deg)⟩

theorem dep_empty (h : Tight B) {w : Wire n m} (dw : Dep B w) : B.support w = ∅ := by
  obtain ⟨c,hc,⟨p⟩⟩ := dw
  obtain ⟨q⟩ := center_line B h hc p
  exact B.empty_support hc q

theorem ancestor (w : Wire n m) : ∃ i : Fin n, Nonempty (Path D (raw i) w) := by
  induction w using D.induction_wire with
  | hin i => exact ⟨i,⟨.refl⟩⟩
  | hgate j hl hr =>
    obtain ⟨i,⟨p⟩⟩ := hl
    exact ⟨i,⟨.step j false p⟩⟩

theorem dep_step (j : Fin m) (b : Bool) (dep : Dep B (D.src j b)) : Dep B (site j) := by
  obtain ⟨c,hc,⟨p⟩⟩ := dep
  exact ⟨c,hc,⟨.step j b p⟩⟩

theorem mask_parents {c : Fin n} {w v : Wire n m} (q : Line D (raw c) w) (mem : v ∈ q.masks) :
    ∃ j b, D.isAnd j = true ∧ D.src j (!b) = v ∧ Nonempty (Line D (raw c) (D.src j b)) := by
  induction q with
  | first => simp [Line.masks] at mem
  | step j b q hu ih =>
    cases a : D.isAnd j <;> simp [Line.masks,a] at mem
    · exact ih mem
    · rcases mem with e|old
      · exact ⟨j,b,a,e.symm,⟨q⟩⟩
      · exact ih old

theorem mask_only_exit (h : Tight B) {c : Fin n} (hc : c ∈ B.actuals) {j : Fin m} {b : Bool}
    (mem : D.src j b = B.mask c hc) : D.onlyExit j b := by
  apply onlyExit_of_deg
  have pos : 0 < D.deg (D.src j b) := Finset.card_pos.mpr ⟨(j,b),by simp [ports]⟩
  by_contra! ne
  obtain ⟨r,_,e⟩ := h.fork _ (by omega : 1 < D.deg (D.src j b))
  rw [mem,B.mask_support c hc] at e
  have low := B.large c (B.mem_actual.mp hc).1
  rw [e,Finset.card_singleton] at low
  omega

theorem mask_consumer (h : Tight B) {c : Fin n} (hc : c ∈ B.actuals) {j : Fin m} {b : Bool}
    (mem : D.src j b = B.mask c hc) :
    D.isAnd j = true ∧ Nonempty (Line D (raw c) (D.src j (!b))) := by
  obtain ⟨k,t,op,hm,line⟩ := mask_parents (D.stem c) (B.mask_mem c hc)
  have eq := mask_only_exit B h hc hm (j,b) (mem.trans hm.symm)
  have jk : j=k := congrArg Prod.fst eq
  have be : b= !t := congrArg Prod.snd eq
  subst j; subst b
  simpa using And.intro op line

theorem end_is_mask (h : Tight B) {r : Fin n} {w : Wire n m} (e : w ∈ (B.routes r).ends) :
    ∃ c, ∃ hc : c ∈ B.actuals, w=B.mask c hc := by
  rcases B.end_cases e with ⟨c,hc,_,eq⟩|⟨_,a,ha,_⟩
  · exact ⟨c,hc,eq⟩
  · simp [h.actual] at ha

theorem follows (h : Tight B) {r : Fin n} (hr : r ∈ B.right) {j : Fin m} {b : Bool}
    (hv : D.src j b ∈ (B.routes r).verts) (pure : ¬ Dep B (site j)) :
    (j,b) ∈ (B.routes r).arcs := by
  apply h.exhaust r hr _ hv _ (j,b) (by simp [ports])
  intro endpt
  obtain ⟨c,hc,eq⟩ := end_is_mask B h endpt
  obtain ⟨_,⟨q⟩⟩ := mask_consumer B h hc eq
  exact pure ⟨c,(B.mem_actual.mp hc).1,⟨.step j (!b) (fromLine q)⟩⟩

theorem pure_path (h : Tight B) {r : Fin n} (hr : r ∈ B.right) {w : Wire n m}
    (p : Path D (raw r) w) (pure : ¬ Dep B w) : w ∈ (B.routes r).verts := by
  induction p with
  | refl =>
    obtain ⟨t,ht⟩ := h.ends r hr
    exact (B.routes r).mem_verts.mpr ⟨t,ht,((B.routes r).path t ht).start_mem⟩
  | step j b p ih =>
    have hv := ih (fun d => pure (dep_step B j b d))
    exact (B.routes r).dst_in_V (follows B h hr hv pure)

theorem pure_witness (h : Tight B) {w : Wire n m} (pure : ¬ Dep B w) :
    ∃ r ∈ B.right, w ∈ (B.routes r).verts ∧ r ∈ B.support w := by
  obtain ⟨r,⟨p⟩⟩ := ancestor w
  have hr : r ∈ B.right := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hc => pure ⟨r,hc,⟨p⟩⟩⟩
  have hv := pure_path B h hr p pure
  exact ⟨r,hr,hv,B.tight_node h.actual hv⟩

theorem zero_base (w : Wire n m) : D.base (onSet ∅) w = false := by
  induction w using D.induction_wire with
  | hin i => simp [base_raw,onSet]
  | hgate j hl hr => rw [base_site,hl,hr]; cases e : D.isAnd j <;> simp [combine,e]

theorem path_of_single {r : Fin n} {w : Wire n m} (val : D.base (onSet {r}) w = true) :
    Nonempty (Path D (raw r) w) := by
  obtain ⟨i,p,hp⟩ := D.trace (onSet {r}) (onSet ∅) (fun _ => none) w val (zero_base w)
  have eq := (hp _ p.start_mem).1
  rw [eval_raw _ _ _ _ rfl] at eq
  have ir : i=r := by simpa [onSet] using eq
  subst i; exact ⟨p⟩

theorem pure_is_or (h : Tight B) (j : Fin m) (pure : ¬ Dep B (site j)) : D.isAnd j = false := by
  cases op : D.isAnd j with
  | false => rfl
  | true =>
    obtain ⟨r,hr,hv,pos⟩ := pure_witness B h pure
    have fire := (Finset.mem_filter.mp pos).2
    change D.base (onSet {r}) (site j) = true at fire
    simp only [base_site,combine,op,↓reduceIte,Bool.and_eq_true] at fire
    have enter (b : Bool) (v : D.base (onSet {r}) (D.src j b) = true) :
        (j,b) ∈ (B.routes r).ins (site j) := by
      obtain ⟨p⟩ := path_of_single v
      have hx := pure_path B h hr p (fun d => pure (dep_step B j b d))
      exact Finset.mem_filter.mpr ⟨follows B h hr hx pure,rfl⟩
    have two : 1 < ((B.routes r).ins (site j)).card := Finset.one_lt_card.mpr
      ⟨(j,false),enter false fire.1,(j,true),enter true fire.2,by simp⟩
    have impossible := h.incoming r hr (site j) hv
    change ((B.routes r).ins (site j)).card ≤ 1 at impossible
    omega

theorem supp_or_gate {j : Fin m} (op : D.isAnd j = false) :
    B.support (site j) = B.support (D.src j false) ∪ B.support (D.src j true) := by
  ext i
  simp only [BipartiteNet.support,Finset.mem_filter,Finset.mem_union,base_site,combine,op,
    Bool.false_eq_true,↓reduceIte,Bool.or_eq_true]
  tauto

theorem pure_values (h : Tight B) (w : Wire n m) (pure : ¬ Dep B w) (x : Fin n → Bool) :
    D.base x w = decide (∃ a ∈ B.support w, x a=true) := by
  classical
  induction w using D.induction_wire with
  | hin i =>
    have hr : i∈B.right := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hc => pure ⟨i,hc,⟨.refl⟩⟩⟩
    have s : B.support (raw i) = {i} := by
      ext z
      simp only [BipartiteNet.support, Finset.mem_filter, base_raw, onSet,
        decide_eq_true_eq, Finset.mem_singleton]
      constructor
      · exact fun p => p.2.symm
      · rintro rfl; exact ⟨hr,rfl⟩
    rw [s,base_raw]
    cases eq : x i <;> simp [eq]
  | hgate j il ir =>
    have op := pure_is_or B h j pure
    rw [base_site, combine, op, supp_or_gate B op, il (fun d => pure (dep_step B j false d)),
      ir (fun d => pure (dep_step B j true d))]
    simp only [↓reduceIte, Bool.false_eq_true, Finset.mem_union]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    constructor
    · rintro (⟨a,ha,xa⟩|⟨a,ha,xa⟩)
      · exact ⟨a,Or.inl ha,xa⟩
      · exact ⟨a,Or.inr ha,xa⟩
    · rintro ⟨a,ha,xa⟩
      exact ha.elim (fun p => Or.inl ⟨a,p,xa⟩) (fun p => Or.inr ⟨a,p,xa⟩)

theorem pure_classification (h : Tight B) (j : Fin m) (pure : ¬Dep B (site j)) :
    ∃ c∈B.centers,∃ A : Finset (Fin n), A.Nonempty ∧ A⊆B.nbr c ∧
      ∀ x : Fin n→Bool, D.base x (site j)=decide (∃ a∈A,x a=true) := by
  obtain ⟨r,_,hv,rs⟩ := pure_witness B h pure
  obtain ⟨c,hc,sub⟩ := B.tight_nodes_subset h.actual hv
  exact ⟨c,hc,_,⟨r,rs⟩,sub,fun x => pure_values B h _ pure x⟩

theorem crossing (h : Tight B) {j : Fin m} {b : Bool} (pure : ¬Dep B (D.src j b))
    (dep : Dep B (site j)) : ∃ c, ∃ hc : c∈B.actuals, D.src j b=B.mask c hc := by
  obtain ⟨r,hr,hv,_⟩ := pure_witness B h pure
  by_cases endpt : D.src j b ∈ (B.routes r).ends
  · exact end_is_mask B h endpt
  · have arc := h.exhaust r hr _ hv endpt (j,b) (by simp [ports])
    have atSite := B.tight_node h.actual ((B.routes r).dst_in_V arc)
    rw [dep_empty B h dep] at atSite; simp at atSite

theorem dependent_port (h : Tight B) {j : Fin m} {b : Bool} (d : Dep B (D.src j b)) :
    D.onlyExit j b := by
  apply onlyExit_of_deg
  have pos : 0 < D.deg (D.src j b) := Finset.card_pos.mpr ⟨(j,b),by simp [ports]⟩
  by_contra! ne
  obtain ⟨r,_,eq⟩ := h.fork _ (by omega : 1 < D.deg (D.src j b))
  rw [dep_empty B h d] at eq; simp at eq

theorem partner_ancestor (h : Tight B) {c : Fin n} (hc : c∈B.actuals) {j : Fin m} {b : Bool}
    (mask : D.src j b = B.mask c hc) {d : Fin n} (hd : d∈B.centers)
    (p : Path D (raw d) (D.src j (!b))) : d=c := by
  classical
  obtain ⟨op,_⟩ := mask_consumer B h hc mask
  obtain ⟨q⟩ := center_line B h hd p
  have unique := dependent_port B h (show Dep B (D.src j (!b)) from ⟨d,hd,⟨p⟩⟩)
  let line := Line.step j (!b) q unique
  have mem : D.src j b ∈ line.masks := by simp [line,Line.masks,op]
  by_contra ne
  obtain ⟨r,rd,rc⟩ := B.distinguish d hd c (B.mem_actual.mp hc).1 ne
  have on := B.all_masks hd rd line _ mem
  have supp : r∈B.support (D.src j b) := Finset.mem_filter.mpr ⟨B.nbr_right hd rd,on⟩
  rw [mask,B.mask_support c hc] at supp
  exact rc supp

theorem partner_raw (h : Tight B) {c : Fin n} (hc : c∈B.actuals) {j : Fin m} {b : Bool}
    (mask : D.src j b = B.mask c hc) : D.src j (!b) = raw c := by
  obtain ⟨op,⟨q⟩⟩ := mask_consumer B h hc mask
  have fromC := fromLine q
  rcases cases_wire (D.src j (!b)) with ⟨i,eq⟩|⟨k,eq⟩
  · have endRaw (a d : Fin n) {s : Wire n m} (p : Path D (raw a) s) (es : s=raw d) : a=d := by
      cases p with
      | refl => exact Fin.ext (congrArg (fun w : Wire n m => w.val) es)
      | step k t prev =>
        have impossible := congrArg Fin.val es
        change n+k.val=d.val at impossible
        have := d.isLt; omega
    simpa [endRaw c i fromC eq] using eq
  · exfalso
    have partnerDep : Dep B (site k) := eq ▸ ⟨c,(B.mem_actual.mp hc).1,⟨fromC⟩⟩
    have lone (t : Bool) (dt : Dep B (D.src k t)) : Nonempty (Path D (raw c) (D.src k t)) := by
      obtain ⟨d,hd,⟨p⟩⟩ := dt
      have dc := partner_ancestor B h hc mask hd (eq.symm ▸ Path.step k t p)
      subst d; exact ⟨p⟩
    by_cases left : Dep B (D.src k false)
    · by_cases right : Dep B (D.src k true)
      · obtain ⟨l⟩ := lone false left
        obtain ⟨r⟩ := lone true right
        obtain ⟨ln⟩ := center_line B h (B.mem_actual.mp hc).1 l
        exact ln.sibling_unreachable (dependent_port B h left) r
      · obtain ⟨d,hd,dm⟩ := crossing B h right partnerDep
        obtain ⟨_,⟨dl⟩⟩ := mask_consumer B h hd dm
        have cd := partner_ancestor B h hc mask (B.mem_actual.mp hd).1
          (eq.symm ▸ Path.step k (!true) (fromLine dl))
        subst d
        have same := mask_only_exit B h hc mask (k,true) (dm.trans mask.symm)
        have kj : k=j := congrArg Prod.fst same
        subst k
        exact (D.lt_src j (!b)).ne (congrArg Fin.val eq)
    · obtain ⟨d,hd,dm⟩ := crossing B h left partnerDep
      obtain ⟨_,⟨dl⟩⟩ := mask_consumer B h hd dm
      have cd := partner_ancestor B h hc mask (B.mem_actual.mp hd).1
        (eq.symm ▸ Path.step k (!false) (fromLine dl))
      subst d
      have same := mask_only_exit B h hc mask (k,false) (dm.trans mask.symm)
      have kj : k=j := congrArg Prod.fst same
      subst k
      exact (D.lt_src j (!b)).ne (congrArg Fin.val eq)

theorem both_center_or (h : Tight B) (j : Fin m) (left : Dep B (D.src j false))
    (right : Dep B (D.src j true)) : D.isAnd j=false := by
  cases op : D.isAnd j with
  | false => rfl
  | true =>
    obtain ⟨c,hc,⟨p⟩⟩ := left
    obtain ⟨q⟩ := center_line B h hc p
    let line := Line.step j false q (dependent_port B h ⟨c,hc,⟨p⟩⟩)
    have mem : D.src j true∈line.masks := by simp [line,Line.masks,op]
    obtain ⟨r,hr⟩ := Finset.card_pos.mp (by have := B.large c hc; omega : 0 < (B.nbr c).card)
    have on := B.all_masks hc hr line _ mem
    have supp : r ∈ B.support (D.src j true) := Finset.mem_filter.mpr ⟨B.nbr_right hc hr,on⟩
    rw [dep_empty B h right] at supp; simp at supp

theorem raw_center_and (h : Tight B) (j : Fin m) (b : Bool) (c : Fin n) (hc : c∈B.centers)
    (rawInput : D.src j b=raw c) : D.isAnd j=true := by
  classical
  have act : c∈B.actuals := by
    by_contra no
    have oth : c∈B.other := Finset.mem_sdiff.mpr ⟨hc,no⟩
    simp [h.actual] at oth
  obtain ⟨k,t,op,mask,_⟩ := mask_parents (D.stem c) (B.mask_mem c act)
  have rawOther := partner_raw B h act mask
  have rawC : D.src k t = raw c := by simpa using rawOther
  have dep : Dep B (D.src k t) := rawC ▸ ⟨c,hc,⟨.refl⟩⟩
  have eq := dependent_port B h dep (j,b) (rawInput.trans rawC.symm)
  have jk : j=k := congrArg Prod.fst eq
  simpa [jk] using op

theorem crossing_star (h : Tight B) (j : Fin m) (dep : Dep B (site j))
    (port : ∃ b, ¬Dep B (D.src j b)) :
    ∃ P : Finset (Fin n), P.Nonempty ∧ P⊆B.centers ∧
      ∀ x : Fin n→Bool, D.base x (site j) =
        decide (∃ c∈P, x c=true ∧ ∃ a∈B.nbr c,x a=true) := by
  classical
  obtain ⟨b,pure⟩ := port
  obtain ⟨c,hc,eq⟩ := crossing B h pure dep
  have op := (mask_consumer B h hc eq).1
  have center := partner_raw B h hc eq
  have val (x : Fin n → Bool) : D.base x (D.src j b) = decide (∃ a∈B.nbr c,x a=true) := by
    rw [pure_values B h _ pure x,eq,B.mask_support c hc]
  refine ⟨{c},Finset.singleton_nonempty _,Finset.singleton_subset_iff.mpr (B.mem_actual.mp hc).1,?_⟩
  intro x
  have key : D.base x (site j) = (x c && decide (∃ a∈B.nbr c,x a=true)) := by
    rw [base_site,combine,op]
    cases b <;> simp_all only [Bool.not_false,Bool.not_true,↓reduceIte,base_raw,Bool.and_comm]
  rw [key]
  apply Bool.eq_iff_iff.mpr
  simp

theorem classify_gates (h : Tight B) (j : Fin m) :
    (∃ c ∈ B.centers, ∃ A : Finset (Fin n), A.Nonempty ∧ A ⊆ B.nbr c ∧
       ∀ x : Fin n → Bool, D.base x (site j) = decide (∃ a ∈ A, x a = true)) ∨
    (∃ P : Finset (Fin n), P.Nonempty ∧ P ⊆ B.centers ∧
       ∀ x : Fin n → Bool, D.base x (site j) =
         decide (∃ c ∈ P, x c = true ∧ ∃ a ∈ B.nbr c, x a = true)) := by
  exact FinishJoin.finishGates B (pure_classification B h) (crossing_star B h)
    (both_center_or B h) (raw_center_and B h) j

end PEqualNP.Outside.L_meta_173_aux.Finish

theorem PEqualNP.Outside.L_meta_173 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), G.Connected → G.IsAcyclic → 2 ≤ G.edgeFinset.card → PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → T.card ≤ S.card) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → S.card = T.card → S = T) → (∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) → PEqualNP.MetaComplexity.IsMinimalCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ t : ℕ, t < C.size → ((∃ c ∈ T, ∃ A : Finset (Fin n), A.Nonempty ∧ (∀ a ∈ A, G.Adj c a) ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = decide (∃ a ∈ A, x a = true)) ∨ (∃ P : Finset (Fin n), P.Nonempty ∧ P ⊆ T ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = decide (∃ c ∈ P, x c = true ∧ ∃ a : Fin n, G.Adj c a ∧ x a = true))) := by
  apply PEqualNP.Outside.L_meta_173_aux.final_glue
  intro n m D B h j
  exact PEqualNP.Outside.L_meta_173_aux.Finish.classify_gates B
    ⟨h.all_actual,h.nonempty,h.fork,h.incoming,h.exits⟩ j
