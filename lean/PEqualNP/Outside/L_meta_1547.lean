import Mathlib
import PEqualNP.Defs

-- Adapted from PEqualNP/MetaComplexity/Helpers/Shannon.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.MetaComplexity

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

end PEqualNP.Outside.L_meta_1547.Helpers

-- Adapted from PEqualNP/MetaComplexity/Helpers/Support.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.MetaComplexity

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

end PEqualNP.Outside.L_meta_1547.Helpers

-- Adapted from PEqualNP/MetaComplexity/Helpers/Elim.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [(Sum.inl b : Stat)]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_1547.Helpers

-- Adapted from PEqualNP/MetaComplexity/Helpers/Parity.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_1547.Helpers

-- Adapted from PEqualNP/MetaComplexity/Helpers/Parity3.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Sum.inl b : Stat) (fun k : Fin n => (Sum.inr (k : ℕ) : Stat)) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Sum.inl false) = Sum.inl b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Sum.inl false) = (Sum.inr (k : ℕ) : Stat) := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Sum.inl false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Sum.inl false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Sum.inl false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Sum.inl false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Sum.inl false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Sum.inl b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Sum.inl false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

theorem supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj

theorem exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Sum.inl c

theorem three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount

end PEqualNP.Outside.L_meta_1547.Helpers

-- Adapted from PEqualNP/MetaComplexity/Helpers/Parity4.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Sum.inl c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Sum.inl c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Sum.inl c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Sum.inl false) = Sum.inl c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Sum.inr q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Sum.inl false) = Sum.inr q from h] at h1
  exact h1.symm

theorem st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Sum.inr k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Sum.inl false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Sum.inl false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Sum.inl false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Sum.inl false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Sum.inl false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Sum.inl c) : ∃ c, (simplify op t ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Sum.inl c) :
    (simplify g.op t (g.inputs.map F)).2 = Sum.inr t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q =>
      cases hF' : F k with
      | inl c => exact absurd hF' (h2 c)
      | inr q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | inl c => exact absurd hF (h1 c)
    | inr q =>
      cases hF' : F k with
      | inl c => exact absurd hF' (h2 c)
      | inr q' => simp [simplify, simpOr, hF, hF']

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Sum.inl c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Sum.inr q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Sum.inl (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

theorem st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Sum.inl c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Sum.inl c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Sum.inl c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Sum.inl c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'

theorem four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount

end PEqualNP.Outside.L_meta_1547.Helpers

-- Adapted from PEqualNP/MetaComplexity/Helpers/PermInputs.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers.PermInputs
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem fix_many {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) :
    ∀ (L : List (Fin N)) (f : (Fin N → Bool) → Bool), L.Nodup → (∀ p ∈ L, p ∉ T) →
    (∀ (a : Fin N → Bool) (pre post : List (Fin N)) (p : Fin N), L = pre ++ p :: post →
      ∃ x : Fin N → Bool, (∀ q ∈ pre, x q = a q) ∧ f (Function.update x p (!x p)) ≠ f x) →
    (∀ (a : Fin N → Bool), ∀ i ∈ T, ∃ x : Fin N → Bool, (∀ q ∈ L, x q = a q) ∧
      f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, HasCircuitSize N f s → T.card + 2 * L.length ≤ s + 1 := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i0.2; omega⟩
  intro L
  induction L with
  | nil =>
    intro f _ _ _ hC s h
    have := dep_lower_set (n + 1) f T (fun i hi => by
      obtain ⟨x, _, hx⟩ := hC (fun _ => false) i hi
      exact ⟨x, hx⟩) s h
    simpa using this
  | cons p L ih =>
    intro f hnd hdis hA hC s h
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    have hpT : p ∉ T := hdis p List.mem_cons_self
    have hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x := by
      obtain ⟨x, _, hx⟩ := hA (fun _ => false) [] L p rfl
      exact ⟨x, hx⟩
    have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b) := by
      intro b
      obtain ⟨x, hxa, hx⟩ := hC (fun _ => b) i0 hi0
      have hxp : x p = b := hxa p List.mem_cons_self
      have hi0p : i0 ≠ p := fun e => hpT (e ▸ hi0)
      refine ⟨Function.update x i0 (!x i0), x, ?_⟩
      have e1 : Function.update (Function.update x i0 (!x i0)) p b
          = Function.update x i0 (!x i0) :=
        Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hi0p), hxp])
      have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
      rw [e1, e2]
      exact hx
    obtain ⟨b, s', hs, h'⟩ := gate_elim_at n f p s hdep hnc h
    have := ih (fun x => f (Function.update x p b)) (List.nodup_cons.1 hnd).2
      (fun q hq => hdis q (List.mem_cons_of_mem _ hq)) ?_ ?_ s' h'
    · simp only [List.length_cons]; omega
    · intro a pre post p' hL
      obtain ⟨x, hxa, hx⟩ := hA (Function.update a p b) (p :: pre) post p' (by rw [hL]; rfl)
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hp' : p' ≠ p := by
        intro e; apply hpL; rw [← e, hL]; simp
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro e; apply hpL; rw [← e, hL]; simp [hq]
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x p' (!x p')) p b
            = Function.update x p' (!x p') :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hp'), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
    · intro a i hi
      obtain ⟨x, hxa, hx⟩ := hC (Function.update a p b) i hi
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hip : i ≠ p := fun e => hpT (e ▸ hi)
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := fun e => hpL (e ▸ hq)
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x i (!x i)) p b
            = Function.update x i (!x i) :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hip), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx

end PEqualNP.Outside.L_meta_1547.Helpers.PermInputs

-- Adapted from PEqualNP/MetaComplexity/Helpers/ForestElim.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers.Forest
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1547.Helpers.PermInputs

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.Outside.L_meta_1547.Helpers.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.Outside.L_meta_1547.Helpers.Forest

-- Adapted from PEqualNP/MetaComplexity/Helpers/ForestGraph.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers.Forest
open PEqualNP.MetaComplexity

open SimpleGraph

theorem exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push_neg at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega

theorem forest_good_leaf {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : ∃ u v : V, G.Adj u v) :
    ∃ l p : V, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
        (∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  obtain ⟨u0, v0, h0⟩ := he
  haveI : Nonempty V := ⟨u0⟩
  obtain ⟨l, z, P, hP, hmax⟩ := exists_longest_path G
  have h1 : 1 ≤ P.length := by
    have := hmax u0 v0 (Walk.cons h0 Walk.nil) (by simp [Walk.cons_isPath_iff, h0.ne])
    simpa using this
  cases P with
  | nil => simp at h1
  | @cons _ p _ hlp P' =>
    rw [Walk.cons_isPath_iff] at hP
    obtain ⟨hP', hlP'⟩ := hP
    have hmax' : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P'.length + 1 := by
      intro c d Q hQ
      have := hmax c d Q hQ
      simpa using this
    have hPfull : (Walk.cons hlp P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hlP'⟩
    have hleaf : ∀ w, G.Adj l w → w = p := by
      intro w hw
      by_cases hm : w ∈ (Walk.cons hlp P').support
      · have := hG.eq_snd_of_adj_start hPfull hw hm
        simpa using this
      · exfalso
        have hQ : (Walk.cons hw.symm (Walk.cons hlp P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hPfull, hm⟩
        have := hmax' _ _ _ hQ
        simp at this
    refine ⟨l, p, hlp, hleaf, ?_⟩
    have hoff : ∀ w, G.Adj p w → w ∉ (Walk.cons hlp P').support →
        ∀ u, G.Adj w u → u = p := by
      intro w hw hwm u hu
      have hwP' : w ∉ P'.support := by
        intro h; exact hwm (by simp [h])
      have hQ : (Walk.cons hw.symm P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hwP'⟩
      by_cases hm : u ∈ (Walk.cons hw.symm P').support
      · have := hG.eq_snd_of_adj_start hQ hu hm
        simpa using this
      · exfalso
        have hQ2 : (Walk.cons hu.symm (Walk.cons hw.symm P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hQ, hm⟩
        have := hmax' _ _ _ hQ2
        simp at this
    by_cases hex : ∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p
    · exact Or.inr hex
    · left
      refine ⟨P'.snd, fun w hw => ?_⟩
      by_cases hwl : w = l
      · exact Or.inl hwl
      · right
        by_cases hm : w ∈ P'.support
        · exact hG.eq_snd_of_adj_start hP' hw hm
        · exfalso
          apply hex
          refine ⟨w, hwl, hw, hoff w hw ?_⟩
          simp [hwl, hm]

end PEqualNP.Outside.L_meta_1547.Helpers.Forest

-- Adapted from PEqualNP/MetaComplexity/Helpers/ForestBound.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers.Forest
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1547.Helpers.PermInputs
open SimpleGraph

noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

theorem F_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F G A x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem F_eq {n : ℕ} (G G' : SimpleGraph (Fin n)) (A A' : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ↔
      ((∃ a ∈ A', y a = true) ∨ ∃ i j : Fin n, G'.Adj i j ∧ y i = true ∧ y j = true)) :
    F G A x = F G' A' y := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  exact h

theorem F_zero {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F G A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp

theorem F_nc {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (h : A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) :
    ∃ x y : Fin n → Bool, F G A x ≠ F G A y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (fun _ => true) = true := by
    rw [F_true]
    rcases h with ⟨a, ha⟩ | ⟨i, j, hij⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨i, j, hij, rfl, rfl⟩
  rw [this]
  simp

theorem F_dep {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hv : v ∉ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x u (!x u)) ≠ F G A x := by
  have hne : u ≠ v := huv.ne
  refine ⟨Function.update (fun _ => false) v true, ?_⟩
  have h1 : F G A (Function.update (Function.update (fun _ => false) v true) u
      (!(Function.update (fun _ => false) v true u))) = true := by
    rw [F_true]
    right
    refine ⟨u, v, huv, ?_, ?_⟩
    · simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hne.symm]
  have h2 : F G A (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hav : a = v
      · exact hv (hav ▸ ha)
      · simp [Function.update_of_ne hav] at hx
    · have hiv : i = v := by
        by_contra h; simp [Function.update_of_ne h] at hi
      have hjv : j = v := by
        by_contra h; simp [Function.update_of_ne h] at hj
      exact hij.ne (hiv.trans hjv.symm)
  rw [h1, h2]
  simp

theorem F_dep_A {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x a (!x a)) ≠ F G A x := by
  refine ⟨fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (Function.update (fun _ => false) a (!false)) = true := by
    rw [F_true]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [this]
  simp

theorem restrict_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hleaf : ∀ w, G.Adj l w → w = p) (x : Fin n → Bool) :
    F G A (Function.update x l false) = F (G.deleteEdges {s(l, p)}) A x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at h⟩
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hil, hjl]
    · rintro ⟨i, j, hij, hi, hj⟩
      rw [deleteEdges_adj] at hij
      obtain ⟨hij, hne⟩ := hij
      have hil : i ≠ l := by
        rintro rfl
        have := hleaf j hij
        subst this
        exact hne rfl
      have hjl : j ≠ l := by
        rintro rfl
        have := hleaf i hij.symm
        subst this
        exact hne (Sym2.eq_swap)
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hil], by rwa [Function.update_of_ne hjl]⟩

theorem restrict_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlA : l ∉ A) (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (x : Fin n → Bool) :
    F G A (Function.update x l true) = F (G.deleteEdges {s(p, l), s(p, q)}) (insert p A) x := by
  have hpl : p ≠ l := hlp.ne.symm
  have hA : ∀ a ∈ A, Function.update x l true a = x a := fun a ha =>
    Function.update_of_ne (by rintro rfl; exact hlA ha) _ _
  have hG1 : ∀ i j, (G.deleteEdges {s(p, l), s(p, q)}).Adj i j → i ≠ p ∧ i ≠ l := by
    intro i j hij
    rw [deleteEdges_adj] at hij
    obtain ⟨hij, hne⟩ := hij
    constructor
    · rintro rfl
      rcases hp j hij with rfl | rfl
      · exact hne (by simp)
      · exact hne (by simp)
    · rintro rfl
      have := hleaf j hij
      subst this
      exact hne (by simp [Sym2.eq_swap])
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hA a ha] at h⟩
    · by_cases hip : i = p
      · subst hip
        exact Or.inl ⟨i, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hi⟩
      by_cases hjp : j = p
      · subst hjp
        exact Or.inl ⟨j, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hj⟩
      have hil : i ≠ l := by
        rintro rfl; exact hjp (hleaf j hij)
      have hjl : j ≠ l := by
        rintro rfl; exact hip (hleaf i hij.symm)
      right
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hip, hjp]
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · right
        exact ⟨l, a, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · exact Or.inl ⟨a, ha, by rwa [hA a ha]⟩
    · right
      have hi' := hG1 i j hij
      have hj' := hG1 j i hij.symm
      rw [deleteEdges_adj] at hij
      exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi'.2],
        by rwa [Function.update_of_ne hj'.2]⟩

def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T

theorem cov_insert {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (p : Fin n)
    (hS : ∀ e ∈ S, p ∈ e) (T : Finset (Fin n)) (hT : Cov (G.deleteEdges S) T) :
    Cov G (insert p T) := by
  intro i j hij
  by_cases he : s(i, j) ∈ S
  · have := hS _ he
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_self _ _)
  · rcases hT i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)

theorem cov_swap {n : ℕ} (G : SimpleGraph (Fin n)) (l p l' : Fin n) (k : ℕ)
    (hll' : l' ≠ l) (hl'p : G.Adj p l') (hleaf' : ∀ w, G.Adj l' w → w = p)
    (hk : ∀ T, Cov G T → k ≤ T.card) (T : Finset (Fin n))
    (hT : Cov (G.deleteEdges {s(l, p)}) T) : k ≤ T.card := by
  have hS : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  by_cases hpT : p ∈ T
  · have := hk _ (cov_insert G _ p hS T hT)
    rwa [Finset.insert_eq_of_mem hpT] at this
  · have hl'T : l' ∈ T := by
      have hpl' : p ≠ l' := hl'p.ne
      rcases hT p l' ((deleteEdges_adj).2 ⟨hl'p, by
          simp [Sym2.eq_iff, hll', hpl'.symm]⟩) with h | h
      · exact absurd h hpT
      · exact h
    have hcov : Cov G (insert p (T.erase l')) := by
      intro i j hij
      by_cases hip : i = p
      · exact Or.inl (hip ▸ Finset.mem_insert_self _ _)
      by_cases hjp : j = p
      · exact Or.inr (hjp ▸ Finset.mem_insert_self _ _)
      have h0 : (G.deleteEdges {s(l, p)}).Adj i j :=
        (deleteEdges_adj).2 ⟨hij, by simp [Sym2.eq_iff, hip, hjp]⟩
      rcases hT i j h0 with h | h
      · have hil' : i ≠ l' := by
          rintro rfl; exact hjp (hleaf' j hij)
        exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hil', h⟩))
      · have hjl' : j ≠ l' := by
          rintro rfl; exact hip (hleaf' i hij.symm)
        exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjl', h⟩))
    have h1 := hk _ hcov
    have h2 := Finset.card_insert_le p (T.erase l')
    have h3 := Finset.card_erase_add_one hl'T
    omega

theorem ncard_del1 {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n) (h : G.Adj l p) :
    (G.deleteEdges {s(l, p)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.2 h)

theorem ncard_del2 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n) (h : G.Adj l p) :
    G.edgeSet.ncard ≤ (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 2 ∧
      (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  constructor
  · have h1 := Set.ncard_le_ncard_sdiff_add_ncard G.edgeSet ({s(p, l), s(p, q)} : Set (Sym2 (Fin n)))
    have h2 := Set.ncard_insert_le (s(p, l)) ({s(p, q)} : Set (Sym2 (Fin n)))
    rw [Set.ncard_singleton] at h2
    omega
  · have hmem : s(l, p) ∈ G.edgeSet := G.mem_edgeSet.2 h
    have hsub : G.edgeSet \ {s(p, l), s(p, q)} ⊆ G.edgeSet \ {s(l, p)} := by
      intro e he
      refine ⟨he.1, ?_⟩
      intro he'
      apply he.2
      rw [Set.mem_singleton_iff] at he'
      rw [he', Sym2.eq_swap]
      exact Set.mem_insert _ _
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_singleton_lt_of_mem hmem
    omega

theorem noedge_ncard {n : ℕ} (G : SimpleGraph (Fin n)) (h : ∀ i j, ¬ G.Adj i j) :
    G.edgeSet.ncard = 0 := by
  have : G.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro e
    induction e using Sym2.ind with
    | _ i j => exact fun he => h i j (G.mem_edgeSet.1 he)
  rw [this, Set.ncard_empty]

theorem del_p_adj {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (i j : Fin n)
    (hij : (G.deleteEdges {s(p, l), s(p, q)}).Adj i j) : i ≠ p := by
  rw [deleteEdges_adj] at hij
  obtain ⟨hij, hne⟩ := hij
  rintro rfl
  rcases hp j hij with rfl | rfl
  · exact hne (by simp)
  · exact hne (by simp)

theorem claimQ : ∀ (m n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (k s : ℕ),
    G.edgeSet.ncard = m → G.IsAcyclic → (∀ i j, G.Adj i j → i ∉ A) →
    (∀ T, Cov G T → k ≤ T.card) → (A.Nonempty ∨ ∃ i j, G.Adj i j) →
    HasCircuitSize n (F G A) s → A.card + m + k ≤ s + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n G A k s hm hac hinv hk hne hC
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · push_neg at hE
    have hk0 : k ≤ (∅ : Finset (Fin n)).card := hk ∅ (fun i j h => absurd h (hE i j))
    have hm0 : m = 0 := by rw [← hm]; exact noedge_ncard G hE
    have := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    simp at hk0
    omega
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := forest_good_leaf G hac hE
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hdepl := F_dep G A l p hlp hpA
  have hdepp := F_dep G A p l hlp.symm hlA
  have hs1 : 2 ≤ s + 1 := by
    have := dep_lower_set _ (F G A) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hdepl
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact hdepp) s hC
    rwa [Finset.card_pair hlp.ne] at this
  set G0 := G.deleteEdges {s(l, p)} with hG0
  have hm0 : G0.edgeSet.ncard + 1 = m := by rw [← hm]; exact ncard_del1 G l p hlp
  have hac0 : G0.IsAcyclic := hac.anti (deleteEdges_le _)
  have hinv0 : ∀ i j, G0.Adj i j → i ∉ A := fun i j h => hinv i j ((deleteEdges_adj).1 h).1
  have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  have hrf : (fun x => F G A (Function.update x l false)) = F G0 A :=
    funext (restrict_false G A l p hlA hleaf)
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · set G1 := G.deleteEdges {s(p, l), s(p, q)} with hG1
    by_cases h0 : A.Nonempty ∨ ∃ i j, G0.Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F G1 (insert p A) :=
        funext (restrict_true G A l p q hlA hlp hleaf hq)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc G0 A h0
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrf x
          have e2 := congrFun hrf y
          rw [e1, e2]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrt x
          have e2 := congrFun hrt y
          rw [e1, e2]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have hk0 : ∀ T, Cov G0 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS0 T hT)
          have := Finset.card_insert_le p T
          omega
        have := ih G0.edgeSet.ncard (by omega) _ G0 A (k - 1) s' rfl hac0 hinv0 hk0 h0 hC'
        omega
      · rw [hrt] at hC'
        have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
          intro e he
          rcases he with rfl | he
          · exact Sym2.mem_mk_left _ _
          · rw [Set.mem_singleton_iff] at he
            subst he
            exact Sym2.mem_mk_left _ _
        have hk1 : ∀ T, Cov G1 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS1 T hT)
          have := Finset.card_insert_le p T
          omega
        have hac1 : G1.IsAcyclic := hac.anti (deleteEdges_le _)
        have hinv1 : ∀ i j, G1.Adj i j → i ∉ insert p A := by
          intro i j h hi
          rcases Finset.mem_insert.1 hi with heq | hi
          · exact del_p_adj G l p q hq i j h heq
          · exact hinv i j ((deleteEdges_adj).1 h).1 hi
        obtain ⟨hc1, hc2⟩ := ncard_del2 G l p q hlp
        rw [← hG1] at hc1 hc2
        have := ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k - 1) s' rfl hac1 hinv1
          hk1 (Or.inl (Finset.insert_nonempty _ _)) hC'
        rw [Finset.card_insert_of_notMem hpA] at this
        omega
    · push_neg at h0
      obtain ⟨hA0, hG00⟩ := h0
      have hm1 : m = 1 := by
        have := noedge_ncard G0 hG00
        omega
      have hk1 : k ≤ ({p} : Finset (Fin (n' + 1))).card := by
        apply hk
        intro i j hij
        have h1 := hG00 i j
        rw [deleteEdges_adj] at h1
        push_neg at h1
        have h2 := h1 hij
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
        rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (Finset.mem_singleton_self _)
        · exact Or.inl (Finset.mem_singleton_self _)
      rw [Finset.card_singleton] at hk1
      subst hA0
      simp only [Finset.card_empty]
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : G0.Adj p l' := (deleteEdges_adj).2 ⟨hpl', by
      simp [Sym2.eq_iff, hl'l, hpl'.ne.symm]⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc G0 A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      have e1 := congrFun hrf x
      have e2 := congrFun hrf y
      rw [e1, e2]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have hk0 : ∀ T, Cov G0 T → k ≤ T.card := cov_swap G l p l' k hl'l hpl' hleaf' hk
    have := ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl hac0 hinv0 hk0
      (Or.inr ⟨p, l', hpl'0⟩) hC'
    omega

end PEqualNP.Outside.L_meta_1547.Helpers.Forest

-- Adapted from PEqualNP/MetaComplexity/Helpers/Readers.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers.Readers
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.Outside.L_meta_1547.Helpers.PermInputs

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o = f x) ∧
  ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

theorem Least.hcl {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : CleanL m gs := L.1
theorem Least.hev {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : ∀ x : Fin m → Bool, vl gs x o = f x := L.2.1
theorem Least.hmin {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' →
      (∀ x : Fin m → Bool, vl gs' x o' = f x) → gs.length ≤ gs'.length := L.2.2

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Sum.inl c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | inr j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  PEqualNP.Outside.L_meta_1547.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS

theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

theorem Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega

theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end

end PEqualNP.Outside.L_meta_1547.Helpers.Readers

-- Adapted from PEqualNP/MetaComplexity/Helpers/ReadersPat.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers.Readers
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_1547.Helpers

theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)

end

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

theorem Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc

theorem Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc

theorem Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩

theorem Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩

end

end PEqualNP.Outside.L_meta_1547.Helpers.Readers

-- Adapted from PEqualNP/MetaComplexity/Helpers/ReadersFunnel.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers.Readers
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_1547.Helpers

theorem lit_contra {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool)
    (h : ∀ u, f u = xor (u v) c) : False := by
  have hd : Dep f v := ⟨fun _ => false, by rw [h, h]; cases c <;> simp⟩
  obtain ⟨x, y, hxy⟩ := hnc v hd false
  apply hxy
  rw [h, h]
  simp

theorem set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]

theorem set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]

theorem set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (r : ℕ) (hr : r < t)
    (g : Gate) (hg : gs[r]? = some g) : ∃ v : Fin (n + 1), g.inputs = [(v : ℕ)] := by
  rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
  · by_cases hjn : j < n + 1
    · exact ⟨⟨j, hjn⟩, hin⟩
    · exfalso
      obtain ⟨r', rfl⟩ : ∃ r', j = n + 1 + r' := ⟨j - (n + 1), by omega⟩
      have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      obtain ⟨g', hg'⟩ : ∃ g', gs[r']? = some g' :=
        ⟨gs[r'], List.getElem?_eq_getElem (by omega)⟩
      have hop' := ht r' (by omega) g' hg'
      rcases L.hcl r' g' hg' with ⟨_, j', hj', hin'⟩ | ⟨hop2, _⟩
      · exact L.no_alias hfnc r hrl j' (by omega) (fun u => by
          rw [vl_not gs L.hcl u r g hg _ hop hin, vl_not gs L.hcl u r' g' hg' _ hop' hin']
          simp)
      · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
  · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h

theorem Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (w : ℕ)
    (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) :
    ∃ (v : Fin (n + 1)) (c : Bool), (∀ u, vl gs u w = xor (u v) c) ∧
      (w = v ∨ ∃ r g, r < t ∧ w = n + 1 + r ∧ gs[r]? = some g ∧ g.op = GateOp.not ∧
        g.inputs = [(v : ℕ)]) := by
  by_cases hwn : w < n + 1
  · exact ⟨⟨w, hwn⟩, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, gs[r]? = some g := ⟨gs[r], List.getElem?_eq_getElem (by omega)⟩
    have hop := ht r (by omega) g hg
    obtain ⟨v, hin⟩ := L.not_input hfnc t ht r (by omega) g hg
    exact ⟨v, true, fun u => by
      rw [vl_not gs L.hcl u r g hg _ hop hin, vl_input gs u v v.isLt]; simp,
      Or.inr ⟨r, g, by omega, rfl, hg, hop, hin⟩⟩

theorem Least.funnel (L : Least (n + 1) f gs o) (hdep : ∃ p, Dep f p) (hnc : RestrNC f)
    (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ), Reads gs p i → Reads gs q i → p = q)
    (h2 : ∀ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g → g.op = GateOp.not →
      (i : ℕ) ∈ g.inputs → ∀ p q : ℕ, Reads gs p (n + 1 + r) → Reads gs q (n + 1 + r) → p = q) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  by_cases hex : ∃ (t : ℕ) (g : Gate), gs[t]? = some g ∧ g.op ≠ GateOp.not
  swap
  · exfalso
    push Not at hex
    have ht : ∀ r < gs.length, ∀ g, gs[r]? = some g → g.op = GateOp.not :=
      fun r _ g hg => hex r g hg
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨v, c, hv, _⟩ := L.lit_wire hfnc gs.length ht o hol hol
      exact lit_contra hnc v c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, y, hxy⟩ := hfnc
      apply hxy
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]
  obtain ⟨g, hg, hgop⟩ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht : ∀ r < t, ∀ g', gs[r]? = some g' → g'.op = GateOp.not := by
    intro r hr g' hg'
    by_contra hne
    exact Nat.find_min hex hr ⟨g', hg', hne⟩
  have htl : t < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rcases L.hcl t g hg with ⟨hop, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hop hgop
  obtain ⟨vj, cj, hvj, hsj⟩ := L.lit_wire hfnc t ht j hj (by omega)
  obtain ⟨vk, ck, hvk, hsk⟩ := L.lit_wire hfnc t ht k hk (by omega)
  have hRj : Reads gs t j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs t k := ⟨g, hg, by rw [hin]; simp⟩
  have hRv : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) → ∃ r, Reads gs r v := by
    intro w v hw hs
    rcases hs with e | ⟨r, g', _, _, hg', _, hin'⟩
    · exact ⟨t, by rw [← e]; exact hw⟩
    · exact ⟨r, g', hg', by rw [hin']; simp⟩
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = t := by
    intro w v hw hs p' a ha hr hne
    rcases hs with e | ⟨r, g', _, er, hg', hop', hin'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact h1 v p' t hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨g', hg', by rw [hin']; simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := h1 v p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact h2 v r g' hg' hop' (by rw [hin']; simp) p' t hr hw
  have hvjk : vj ≠ vk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc t htl j hj (fun u => by
        rw [vl_gate gs L.hcl u t g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, g1, hr1, ej, hg1, hop1, hin1⟩ <;>
      rcases hsk with ek | ⟨r2, g2, hr2, ek, hg2, hop2, hin2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := h1 vj t r2 (by rw [← ej]; exact hRj) ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      omega
    · have := h1 vk t r1 (by rw [← ek]; exact hRk) ⟨g1, hg1, by rw [hin1, e]; simp⟩
      omega
    · have := h1 vj r1 r2 ⟨g1, hg1, by rw [hin1]; simp⟩ ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  obtain ⟨rj, hrj⟩ := hRv j vj hRj hsj
  obtain ⟨rk, hrk⟩ := hRv k vk hRk hsk
  have hdj := L.read_dep hfnc vj rj hrj
  have hdk := L.read_dep hfnc vk rk hrk
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ vj → i ≠ vk → u i = u' i) →
      vl gs u (n + 1 + t) = vl gs u' (n + 1 + t) → f u = f u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (vj : ℕ) ∨ n + 1 + p' = (vk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = t := by
        rcases hBa' with e | e | e | e
        · exact hopnd j vj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j vj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (vj : ℕ) ∨ o = (vk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact lit_contra hnc vj false (fun x => by
          rw [← L.hev, e, vl_input gs x vj vj.isLt]; simp)
      · exact lit_contra hnc vk false (fun x => by
          rw [← L.hev, e, vl_input gs x vk vk.isLt]; simp)
      · exact lit_contra hnc vj cj (fun x => by rw [← L.hev, e, hvj])
      · exact lit_contra hnc vk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ vj → i ≠ vk →
      set2 x vj a vk b i = set2 x vj a' vk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x vj vk a b i e1 e2, set2_o x vj vk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x vj a vk b) (n + 1 + t) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ t g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  refine ⟨vj, vk, hvjk, hdj, hdk, ?_⟩
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

end

end PEqualNP.Outside.L_meta_1547.Helpers.Readers

-- Adapted from PEqualNP/MetaComplexity/Helpers/ReadersExport.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Helpers.Readers
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_1547.Helpers

theorem fanout_step (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    ∃ y : Fin (n + 1), Dep f y ∧ Pays f y s := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc h
  have mono : ∀ y, Pays f y gs.length → Pays f y s := by
    intro y hp
    rcases hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩
    · exact Or.inr (Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
    · exact Or.inr (Or.inr ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
  by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ), p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, p, q, hpq, hp, hq⟩ := hA
    have hd := L.read_dep hfnc i p hp
    exact ⟨i, hd, mono i (L.two_readers i (hnc i hd) p q hpq hp hq)⟩
  by_cases hB : ∃ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g ∧ g.op = GateOp.not ∧
      (i : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ, p ≠ q ∧ Reads gs p (n + 1 + r) ∧ Reads gs q (n + 1 + r)
  · obtain ⟨i, r, g, hr, hop, hin, p, q, hpq, hp, hq⟩ := hB
    have hd := L.read_dep hfnc i r ⟨g, hr, hin⟩
    obtain ⟨d1, d2⟩ := L.not_two_readers i (hnc i hd) r g hr hop hin p q hpq hp hq
    exact ⟨i, hd, mono i (Or.inl ⟨d1, d2⟩)⟩
  exfalso
  obtain ⟨p, q, hpq, hdp, hdq, hf⟩ := L.funnel hdep hnc
    (fun i p q hp hq => by
      by_contra hne
      exact hA ⟨i, p, q, hne, hp, hq⟩)
    (fun i r g hr hop hin p q hp hq => by
      by_contra hne
      exact hB ⟨i, r, g, hr, hop, hin, p, q, hne, hp, hq⟩)
  exact hnf p q hpq hdp hdq hf

theorem fanout_step_3_4 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨
      (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') := by
  obtain ⟨y, _, hp⟩ := fanout_step n f s hdep hnc hnf h
  rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
  · exact Or.inl ⟨y, s', h1, h2⟩
  · exact Or.inl ⟨y, s', by omega, h2⟩
  · exact Or.inr ⟨y, s', h1, h2⟩

theorem noFunnel_of_sep {m : ℕ} (f : (Fin m → Bool) → Bool)
    (h : ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q →
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p false q true) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q true))) : NoFunnel f := by
  intro p q hpq hdp hdq hf
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩⟩ := h p q hpq hdp hdq
  cases a <;> cases b
  · exact h3 (hab x3).1
  · exact h1 (hab x1).2.symm
  · exact h2 ((hab x2).1.trans (hab x2).2).symm
  · exact h1 (hab x1).2

end PEqualNP.Outside.L_meta_1547.Helpers.Readers

-- Adapted from PEqualNP/Outside/L_meta_568.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1547.Chain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    run (gs₁ ++ gs₂) w = run gs₂ (run gs₁ w) :=
  List.foldl_append

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma getD_snoc_lt {α : Type*} (w : List α) (b : α) (i : ℕ) (hi : i < w.length) (d : α) :
    (w ++ [b]).getD i d = w.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (w : List α) (b : α) (d : α) :
    (w ++ [b]).getD w.length d = b := by
  simp [List.getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD, hi]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOk (g : Gate) : Prop :=
  Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp only [normGate]
  cases ins <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := h
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
  rcases hop with rfl | rfl | rfl
  · exact ⟨⟨by simp [normGate], hlen⟩, by simp [normGate]⟩
  · exact ⟨⟨by simp [normGate], hlen⟩, by simp [normGate]⟩
  · refine ⟨⟨by simp [normGate], ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma run_norm (gs : List Gate) (w : List Bool) :
    run (gs.map normGate) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons]
    change run (gs.map normGate) (step w (normGate g)) = run gs (step w g)
    have hstep : step w (normGate g) = step w g := by
      simp only [step, normGate_eval]
    rw [hstep, ih]

abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (s : Stat) (m : ℕ) : Prop := match s with
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; exact ⟨by simp, by simp⟩)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; exact ⟨by simp, by simp⟩)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; exact ⟨by simp, by simp⟩)
  · simp at hg
  · simp at hg

lemma simplify_none_of_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  rcases hc with ⟨c, hc⟩
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simplify, simpAnd] at hc ⊢
    · cases a <;> cases b <;> simp [simplify, simpAnd] at hc ⊢
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simplify, simpOr] at hc ⊢
    · cases a <;> cases b <;> simp [simplify, simpOr] at hc ⊢
    · simp at hlen
  · have h1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hc
    · cases a <;> simp [simplify, simpNot] at hc ⊢
    · simp at h1

lemma simplify_valid (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1)
    (hval : ∀ s ∈ ins, Stat.Valid s m) :
    let res := simplify op m ins
    Stat.Valid res.2 (match res.1 with | none => m | some _ => m + 1) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid]
    · cases a with
      | inl c => simp [simplify, simpAnd, Stat.Valid]
      | inr j => exact hval (Sum.inr j) (by simp)
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp [simplify, simpAnd, Stat.Valid]
        | inr j =>
          cases c
          · simp [simplify, simpAnd, Stat.Valid]
          · simpa [simplify, simpAnd] using hval (Sum.inr j) (by simp)
      | inr j =>
        cases b with
        | inl d =>
          cases d
          · simp [simplify, simpAnd, Stat.Valid]
          · simpa [simplify, simpAnd] using hval (Sum.inr j) (by simp)
        | inr k =>
          simpa [simplify, simpAnd, Stat.Valid] using Nat.lt_succ_self m
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid]
    · cases a with
      | inl c => simp [simplify, simpOr, Stat.Valid]
      | inr j => exact hval (Sum.inr j) (by simp)
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp [simplify, simpOr, Stat.Valid]
        | inr j =>
          cases c
          · simpa [simplify, simpOr] using hval (Sum.inr j) (by simp)
          · simp [simplify, simpOr, Stat.Valid]
      | inr j =>
        cases b with
        | inl d =>
          cases d
          · simpa [simplify, simpOr] using hval (Sum.inr j) (by simp)
          · simp [simplify, simpOr, Stat.Valid]
        | inr k =>
          simpa [simplify, simpOr, Stat.Valid] using Nat.lt_succ_self m
    · simp at hlen
  · have h1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpNot, Stat.Valid]
    · cases a with
      | inl c => simp [simplify, simpNot, Stat.Valid]
      | inr j => simpa [simplify, simpNot, Stat.Valid] using Nat.lt_succ_self m
    · simp at h1

lemma simplify_eval (op : GateOp) (w : List Bool) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1) :
    let res := simplify op w.length ins
    let w' := match res.1 with | none => w | some g => step w g
    Stat.val w' res.2 = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.val, GateOp.eval]
    · cases a <;> simp [simplify, simpAnd, Stat.val, GateOp.eval]
    · cases a with
      | inl c => cases b with
        | inl d => simp [simplify, simpAnd, Stat.val, GateOp.eval]
        | inr j => cases c <;> simp [simplify, simpAnd, Stat.val, GateOp.eval]
      | inr j => cases b with
        | inl d => cases d <;> simp [simplify, simpAnd, Stat.val, GateOp.eval]
        | inr k =>
          simp [simplify, simpAnd, Stat.val, step, getD_snoc_eq, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.val, GateOp.eval]
    · cases a <;> simp [simplify, simpOr, Stat.val, GateOp.eval]
    · cases a with
      | inl c => cases b with
        | inl d => simp [simplify, simpOr, Stat.val, GateOp.eval]
        | inr j => cases c <;> simp [simplify, simpOr, Stat.val, GateOp.eval]
      | inr j => cases b with
        | inl d => cases d <;> simp [simplify, simpOr, Stat.val, GateOp.eval]
        | inr k =>
          simp [simplify, simpOr, Stat.val, step, getD_snoc_eq, GateOp.eval]
    · simp at hlen
  · have h1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpNot, Stat.val, GateOp.eval]
    · cases a with
      | inl c => simp [simplify, simpNot, Stat.val, GateOp.eval]
      | inr j =>
        simp [simplify, simpNot, Stat.val, step, getD_snoc_eq, GateOp.eval]
    · simp at h1

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  let (st, gs) := acc
  let ins := g.inputs.map fun i => st.getD i (Sum.inl false)
  let (og, s) := simplify g.op (n + gs.length) ins
  let gs' := match og with | none => gs | some g' => gs ++ [g']
  (st ++ [s], gs')

def elimPass (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma elimPass_main (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, NOk g) :
    ∀ (st : List Stat) (outGs : List Gate),
      (∀ s ∈ st, Stat.Valid s (n + outGs.length)) →
      (∀ g ∈ outGs, Ok g) →
      let res := elimPass n gs (st, outGs)
      (∀ s ∈ res.1, Stat.Valid s (n + res.2.length)) ∧
      (∀ g ∈ res.2, Ok g) ∧
      res.2.length ≤ outGs.length + gs.length ∧
      (∀ k < st.length, res.1.getD k (Sum.inl false) = st.getD k (Sum.inl false)) ∧
      ((∃ g ∈ gs, ∃ i ∈ g.inputs, i < st.length ∧ ∃ c, st.getD i (Sum.inl false) = Sum.inl c) →
        res.2.length + 1 ≤ outGs.length + gs.length) ∧
      (∀ (y : Fin n → Bool) (wOld : List Bool),
        wOld.length = st.length →
        (∀ i, wOld.getD i false = Stat.val (run outGs (List.ofFn y)) (st.getD i (Sum.inl false))) →
        ∀ i, (run gs wOld).getD i false =
          Stat.val (run res.2 (List.ofFn y)) (res.1.getD i (Sum.inl false))) := by
  induction gs with
  | nil =>
    intro st outGs hv ho
    refine ⟨hv, ho, le_rfl, fun _ _ => rfl, ?_, ?_⟩
    · rintro ⟨g, hg, _⟩; simp at hg
    · intro y wOld _ hag i; exact hag i
  | cons g gs ih =>
    intro st outGs hv ho
    have hg_nok : NOk g := hgs g (List.mem_cons_self ..)
    have hgs_nok : ∀ g' ∈ gs, NOk g' := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    set ins := g.inputs.map fun i => st.getD i (Sum.inl false)
    set res1 := simplify g.op (n + outGs.length) ins
    set outGs1 : List Gate := match res1.1 with | none => outGs | some g' => outGs ++ [g']
    set st1 : List Stat := st ++ [res1.2]
    have hins_val : ∀ s ∈ ins, Stat.Valid s (n + outGs.length) := by
      intro s hs
      rcases List.mem_map.mp hs with ⟨i, _, rfl⟩
      by_cases hi : i < st.length
      · exact hv _ (by simp [List.getD, hi])
      · rw [List.getD_eq_default _ _ (by omega)]; trivial
    have hstep_len : outGs1.length ≤ outGs.length + 1 := by
      cases h : res1.1 <;> simp [outGs1, h]
    have hstep_ok : ∀ g' ∈ outGs1, Ok g' := by
      cases h : res1.1 with
      | none => simpa [outGs1, h] using ho
      | some g' =>
        intro x hx
        simp only [outGs1, h, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact ho x hx
        · exact simplify_ok g.op (n + outGs.length) ins x h
    have hstep_valid : ∀ s ∈ st1, Stat.Valid s (n + outGs1.length) := by
      intro s hs
      simp only [st1, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      · have hvs := hv s hs
        cases s with
        | inl _ => trivial
        | inr j =>
          change j < n + outGs.length at hvs
          change j < n + outGs1.length
          cases h : res1.1 <;> simp [outGs1, h] <;> omega
      · have hvv := simplify_valid g.op (n + outGs.length) ins
          hg_nok.1.1 (by simpa [ins] using hg_nok.1.2)
          (fun hn => by simpa [ins] using hg_nok.2 hn) hins_val
        have hlen_m : (match res1.1 with | none => n + outGs.length | some _ => n + outGs.length + 1) =
            n + outGs1.length := by
          cases h : res1.1 <;> simp [outGs1, h] <;> omega
        simpa [res1, hlen_m] using hvv
    have hrec := ih hgs_nok st1 outGs1 hstep_valid hstep_ok
    obtain ⟨hv', ho', hlen', hget', hdrop', hev'⟩ := hrec
    have hpass_eq : elimPass n (g :: gs) (st, outGs) = elimPass n gs (st1, outGs1) := rfl
    dsimp only
    rw [hpass_eq]
    refine ⟨hv', ho', by simp; omega, ?_, ?_, ?_⟩
    · intro k hk
      rw [hget' k (by simp [st1]; omega)]
      exact getD_snoc_lt st res1.2 k hk (Sum.inl false)
    · rintro ⟨g0, hg0, i, hi, hist, c, hc⟩
      simp only [List.mem_cons] at hg0
      rcases hg0 with hg0eq | hg0
      · rw [hg0eq] at hi
        have hcin : Sum.inl c ∈ ins := List.mem_map.mpr ⟨i, hi, hc⟩
        have hnone : res1.1 = none :=
          simplify_none_of_const g.op (n + outGs.length) ins hg_nok.1.1
            (by simpa [ins] using hg_nok.1.2) (fun hn => by simpa [ins] using hg_nok.2 hn) ⟨c, hcin⟩
        have hout1_eq : outGs1 = outGs := by simp [outGs1, hnone]
        rw [hout1_eq] at hlen' ⊢
        simp; omega
      · have hdrop1 : (elimPass n gs (st1, outGs1)).2.length + 1 ≤ outGs1.length + gs.length :=
          hdrop' ⟨g0, hg0, i, hi, by simp [st1]; omega, c, by
            rw [getD_snoc_lt st res1.2 i hist (Sum.inl false)]; exact hc⟩
        simp; omega
    · intro y wOld hlen_old hag
      have hlen_run : (run outGs (List.ofFn y)).length = n + outGs.length := by
        rw [run_length, List.length_ofFn]
      have hrun1 : run outGs1 (List.ofFn y) =
          match res1.1 with
          | none => run outGs (List.ofFn y)
          | some g' => step (run outGs (List.ofFn y)) g' := by
        cases h : res1.1 with
        | none => simp [outGs1, h]
        | some g' =>
          simp only [outGs1, h]
          rw [run_append]
          rfl
      have hve2 := simplify_eval g.op (run outGs (List.ofFn y)) ins
        hg_nok.1.1 (by simpa [ins] using hg_nok.1.2)
        (fun hn => by simpa [ins] using hg_nok.2 hn)
      rw [hlen_run] at hve2
      have hres2_val : Stat.val (run outGs1 (List.ofFn y)) res1.2 =
          g.op.eval (g.inputs.map fun j => wOld.getD j false) := by
        rw [hrun1]
        have hres2 : Stat.val (match res1.1 with
            | none => run outGs (List.ofFn y)
            | some g' => step (run outGs (List.ofFn y)) g') res1.2 =
            g.op.eval (ins.map (Stat.val (run outGs (List.ofFn y)))) := by
          simpa [res1] using hve2
        rw [hres2]
        congr 1
        simp only [ins, List.map_map]
        apply List.map_congr_left
        intro j _
        exact (hag j).symm
      apply hev' y (step wOld g) (by simp [step, st1, hlen_old])
      intro i
      by_cases hlt : i < wOld.length
      · have hlt_st : i < st.length := by omega
        rw [step, getD_snoc_lt _ _ _ hlt, show st1 = st ++ [res1.2] from rfl,
          getD_snoc_lt _ _ _ hlt_st, hag i]
        have hvi : Stat.Valid (st.getD i (Sum.inl false)) (n + outGs.length) :=
          hv _ (by simp [List.getD, hlt_st])
        cases hs : st.getD i (Sum.inl false) with
        | inl c => rfl
        | inr j =>
          rw [hs] at hvi
          change j < n + outGs.length at hvi
          simp only [Stat.val]
          rw [hrun1]
          cases h : res1.1 with
          | none => rfl
          | some g' =>
            symm
            exact getD_snoc_lt _ _ _ (by rw [hlen_run]; exact hvi) false
      · by_cases heq : i = wOld.length
        · subst heq
          rw [step, getD_snoc_eq, hlen_old, show st1 = st ++ [res1.2] from rfl,
            getD_snoc_eq, hres2_val]
        · rw [List.getD_eq_default _ _ (by simp [step]; omega),
            List.getD_eq_default _ _ (by simp [st1]; omega)]
          rfl

lemma elimPass_append (n : ℕ) (L R : List Gate) (st : List Stat × List Gate) :
    elimPass n (L ++ R) st = elimPass n R (elimPass n L st) :=
  List.foldl_append

def gateArgs (st : List Stat × List Gate) (g : Gate) : List Stat :=
  g.inputs.map fun i => st.1.getD i (Sum.inl false)

def gateResult (n : ℕ) (st : List Stat × List Gate) (g : Gate) : Option Gate × Stat :=
  simplify g.op (n + st.2.length) (gateArgs st g)

lemma elimStep_env (n : ℕ) (st : List Stat × List Gate) (g : Gate) :
    (elimStep n st g).1 = st.1 ++ [(gateResult n st g).2] := by
  rcases st with ⟨env, out⟩
  rfl

lemma elimStep_size (n : ℕ) (st : List Stat × List Gate) (g : Gate) :
    (elimStep n st g).2.length ≤ st.2.length + 1 := by
  rcases st with ⟨env, out⟩
  simp only [elimStep]
  split <;> simp

lemma elimStep_no_gate (n : ℕ) (st : List Stat × List Gate) (g : Gate)
    (h : (gateResult n st g).1 = none) :
    (elimStep n st g).2 = st.2 := by
  rcases st with ⟨env, out⟩
  simpa [gateResult, gateArgs, elimStep] using
    (show (match (gateResult n (env, out) g).1 with
      | none => out
      | some gate => out ++ [gate]) = out by rw [h])

lemma elimPass_env (n : ℕ) (gs : List Gate) (st : List Stat × List Gate) :
    ∃ rest, (elimPass n gs st).1 = st.1 ++ rest := by
  induction gs generalizing st with
  | nil => exact ⟨[], by simp [elimPass]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (elimStep n st g)
    refine ⟨(gateResult n st g).2 :: tail, ?_⟩
    change (elimPass n gs (elimStep n st g)).1 = _
    rw [ht, elimStep_env, List.append_assoc]
    rfl

lemma elimPass_get (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i : ℕ) (hi : i < st.1.length) :
    (elimPass n gs st).1.getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
  obtain ⟨tail, ht⟩ := elimPass_env n gs st
  rw [ht, List.getD_append _ _ _ _ hi]

lemma gateResult_no_gate_of_constant (n : ℕ) (st : List Stat × List Gate) (g : Gate)
    (hg : NOk g) (i : ℕ) (hi : i ∈ g.inputs) (b : Bool)
    (hc : st.1.getD i (Sum.inl false) = Sum.inl b) :
    (gateResult n st g).1 = none := by
  apply simplify_none_of_const g.op _ _ hg.1.1
  · simpa [gateArgs] using hg.1.2
  · intro h
    simpa [gateArgs] using hg.2 h
  · exact ⟨b, List.mem_map.mpr ⟨i, hi, hc⟩⟩

def stateAt (n : ℕ) (gs : List Gate) (st : List Stat × List Gate) (i : ℕ) :
    List Stat × List Gate := elimPass n (gs.take i) st

lemma stateAt_succ (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    {i : ℕ} (hi : i < gs.length) :
    stateAt n gs st (i + 1) = elimStep n (stateAt n gs st i) gs[i] := by
  unfold stateAt
  rw [List.take_succ_eq_append_getElem hi, elimPass_append]
  rfl

lemma stateAt_size_bound (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ gs.length) :
    (stateAt n gs st j).2.length ≤ (stateAt n gs st i).2.length + (j - i) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj' ih =>
    have hjlt : j < gs.length := by omega
    rw [stateAt_succ n gs st hjlt]
    have hstep := elimStep_size n (stateAt n gs st j) gs[j]
    have hprev := ih (by omega)
    omega

lemma stateAt_preserves (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i j w : ℕ) (hij : i ≤ j) (hj : j ≤ gs.length)
    (hw : w < (stateAt n gs st i).1.length) :
    (stateAt n gs st j).1.getD w (Sum.inl false) =
      (stateAt n gs st i).1.getD w (Sum.inl false) := by
  have hsplit : gs.take j = gs.take i ++ (gs.take j).drop i := by
    calc
      gs.take j = (gs.take j).take i ++ (gs.take j).drop i := (List.take_append_drop _ _).symm
      _ = _ := by rw [List.take_take, min_eq_left hij]
  have he : stateAt n gs st j = elimPass n ((gs.take j).drop i) (stateAt n gs st i) :=
    (congrArg (fun sub => elimPass n sub st) hsplit).trans (elimPass_append _ _ _ _)
  rw [he]
  exact elimPass_get _ _ _ _ hw

lemma stateAt_two_drops (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i j : ℕ) (hij : i < j) (hj : j < gs.length)
    (hiDrop : (stateAt n gs st (i + 1)).2 = (stateAt n gs st i).2)
    (hjDrop : (stateAt n gs st (j + 1)).2 = (stateAt n gs st j).2) :
    (elimPass n gs st).2.length + 2 ≤ st.2.length + gs.length := by
  have hfirst := stateAt_size_bound n gs st 0 i (by omega) (by omega)
  have hmiddle := stateAt_size_bound n gs st (i + 1) j (by omega) (by omega)
  have hlast := stateAt_size_bound n gs st (j + 1) gs.length (by omega) le_rfl
  rw [hiDrop] at hmiddle
  rw [hjDrop] at hlast
  have hzero : stateAt n gs st 0 = st := rfl
  have hfull : stateAt n gs st gs.length = elimPass n gs st := by simp [stateAt]
  rw [hzero, Nat.sub_zero] at hfirst
  rw [hfull] at hlast
  omega

def wireEnv (k : ℕ) : List Stat := List.ofFn (fun i : Fin k => Sum.inr i.val)

lemma wireEnv_read (k i : ℕ) (hi : i < k) :
    (wireEnv k).getD i (Sum.inl false) = Sum.inr i := by
  simp [wireEnv, List.getD_eq_getElem?_getD, hi]

lemma statValid_wireEnv (k : ℕ) (u : Stat) (hu : u ∈ wireEnv k) : Stat.Valid u k := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
  exact i.isLt

lemma getD_set_same {α : Type*} (l : List α) (i : ℕ) (a d : α)
    (hi : i < l.length) : (l.set i a).getD i d = a := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma getD_set_other {α : Type*} (l : List α) (i j : ℕ) (a d : α)
    (hij : i ≠ j) : (l.set i a).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]

lemma initEnv_valid (k : ℕ) (w : ℕ) (b : Bool) (u : Stat)
    (hu : u ∈ (wireEnv k).set w (Sum.inl b)) : Stat.Valid u k := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
  by_cases hw : w = i
  · subst w
    simp [Stat.Valid]
  · rw [List.getElem_set_ne hw]
    apply statValid_wireEnv
    exact List.getElem_mem _

lemma env_represents (wires : List Bool) (k w : ℕ) (b : Bool)
    (hk : wires.length = k) (hw : w < k) (i : ℕ) :
    (wires.set w b).getD i false =
      Stat.val wires (((wireEnv k).set w (Sum.inl b)).getD i (Sum.inl false)) := by
  by_cases hiw : i = w
  · subst i
    rw [getD_set_same _ _ _ _ (by simpa [hk] using hw),
      getD_set_same _ _ _ _ (by simpa [wireEnv] using hw)]
    rfl
  · rw [getD_set_other _ _ _ _ _ (Ne.symm hiw), getD_set_other _ _ _ _ _ (Ne.symm hiw)]
    by_cases hi : i < k
    · rw [wireEnv_read _ _ hi]
      rfl
    · rw [List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by simp [wireEnv]; omega)]
      rfl

lemma run_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega), step, getD_snoc_lt _ _ _ hi]

lemma step_at (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) :=
  getD_snoc_eq _ _ _

lemma step_off (w : List Bool) (g : Gate) (i : ℕ) (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  by_cases hlt : i < w.length
  · exact getD_snoc_lt _ _ _ hlt _
  · rw [List.getD_eq_default _ _ (by simp [step]; omega),
      List.getD_eq_default _ _ (by omega)]

lemma run_agree (bad : ℕ → Prop) (gs : List Gate)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬ bad i)
    (x y : List Bool) (hlen : x.length = y.length)
    (hag : ∀ i, ¬ bad i → x.getD i false = y.getD i false) :
    ∀ i, ¬ bad i → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact hag
  | cons g gs ih =>
    change ∀ i, ¬ bad i → (run gs (step x g)).getD i false = (run gs (step y g)).getD i false
    apply ih (fun d hd => hread d (List.mem_cons_of_mem _ hd)) _ _ (by simp [step, hlen])
    intro i hi
    by_cases he : i = x.length
    · subst i
      rw [step_at, hlen, step_at]
      congr 1
      exact List.map_congr_left fun j hj => hag j (hread g (by simp) j hj)
    · rw [step_off _ _ _ he, step_off _ _ _ (by omega)]
      exact hag i hi

lemma set_getD_self (w : List Bool) (v : ℕ) (hv : v < w.length) :
    w.set v (w.getD v false) = w := by
  rw [List.getD_eq_getElem _ _ hv]
  exact List.set_getElem_self hv

lemma elimPass_out (n : ℕ) (gs : List Gate) (st : List Stat × List Gate) :
    ∃ rest, (elimPass n gs st).2 = st.2 ++ rest := by
  induction gs generalizing st with
  | nil => exact ⟨[], by simp [elimPass]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (elimStep n st g)
    rcases st with ⟨env, out⟩
    by_cases he : (gateResult n (env, out) g).1 = none
    · exact ⟨tail, ht.trans (congrArg (fun a => a ++ tail) (elimStep_no_gate _ _ _ he))⟩
    · cases hg : (gateResult n (env, out) g).1 with
      | none => exact False.elim (he hg)
      | some g' =>
        refine ⟨g' :: tail, ht.trans ?_⟩
        have hstep : (elimStep n (env, out) g).2 = out ++ [g'] := by
          change (match (gateResult n (env, out) g).1 with
            | none => out
            | some d => out ++ [d]) = _
          rw [hg]
        rw [hstep, List.append_assoc]
        rfl

def forceValue (C : Circuit) (m k v : ℕ) (b : Bool) (x : Fin m → Bool) : Bool :=
  (run (C.gates.drop k) ((run (C.gates.take k) (List.ofFn x)).set v b)).getD C.output false

def cutState (C : Circuit) (m k v : ℕ) : List Stat × List Gate :=
  ((wireEnv (m + k)).set v (Sum.inl false), C.gates.take k)

def compiledCut (C : Circuit) (m k v : ℕ) : List Stat × List Gate :=
  elimPass m (C.gates.drop k) (cutState C m k v)

lemma cut_prefix_length (C : Circuit) (m k : ℕ) (hk : k ≤ C.gates.length)
    (x : Fin m → Bool) :
    (run (C.gates.take k) (List.ofFn x)).length = m + k := by
  rw [run_length, List.length_ofFn, List.length_take_of_le hk]

lemma cut_actual (C : Circuit) (m k v : ℕ) (hk : k ≤ C.gates.length) (hv : v < m + k)
    (x : Fin m → Bool) :
    forceValue C m k v ((run (C.gates.take k) (List.ofFn x)).getD v false) x =
      circuitFun m C x := by
  unfold forceValue
  rw [set_getD_self _ _ (by rw [cut_prefix_length _ _ _ hk]; exact hv), ← run_append,
    List.take_append_drop]
  rfl

lemma cut_or (C : Circuit) (m k v : ℕ) (hk : k ≤ C.gates.length) (hv : v < m + k)
    (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true) (x : Fin m → Bool) :
    circuitFun m C x =
      ((run (C.gates.take k) (List.ofFn x)).getD v false || forceValue C m k v false x) := by
  have h := cut_actual C m k v hk hv x
  cases hb : (run (C.gates.take k) (List.ofFn x)).getD v false
  · rw [hb] at h
    simpa using h.symm
  · rw [hb, hot x] at h
    simpa using h.symm

lemma cut_compile (C : Circuit) (m k v : ℕ) (hk : k ≤ C.gates.length) (hv : v < m + k)
    (hlegal : ∀ g ∈ C.gates, NOk g) :
    let z := compiledCut C m k v
    (∀ g ∈ z.2, Ok g) ∧
    (∀ x : Fin m → Bool, forceValue C m k v false x =
      Stat.val (run z.2 (List.ofFn x)) (z.1.getD C.output (Sum.inl false))) ∧
    (∀ x : Fin m → Bool, (run z.2 (List.ofFn x)).getD v false =
      (run (C.gates.take k) (List.ofFn x)).getD v false) := by
  have hrest : ∀ g ∈ C.gates.drop k, NOk g := fun g hg => hlegal g ((List.drop_sublist _ _).subset hg)
  have hpre : ∀ g ∈ C.gates.take k, Ok g := fun g hg => (hlegal g ((List.take_sublist _ _).subset hg)).1
  have henv : ∀ s ∈ (wireEnv (m + k)).set v (Sum.inl false), Stat.Valid s (m + (C.gates.take k).length) := by
    rw [List.length_take_of_le hk]
    exact initEnv_valid _ _ _
  obtain ⟨_, hok, _, _, _, hsem⟩ := elimPass_main m (C.gates.drop k) hrest _ _ henv hpre
  refine ⟨hok, ?_, ?_⟩
  · intro x
    apply hsem x ((run (C.gates.take k) (List.ofFn x)).set v false)
    · simp [cut_prefix_length _ _ _ hk, wireEnv]
    · exact env_represents _ _ _ _ (cut_prefix_length _ _ _ hk _) hv
  · intro x
    obtain ⟨tail, ht⟩ := elimPass_out m (C.gates.drop k) (cutState C m k v)
    change (run (compiledCut C m k v).2 (List.ofFn x)).getD v false = _
    rw [show (compiledCut C m k v).2 = C.gates.take k ++ tail from ht, run_append]
    apply run_preserves
    rwa [cut_prefix_length _ _ _ hk]

def attachOr (m v : ℕ) (gs : List Gate) (s : Stat) : Circuit :=
  match s with
  | Sum.inl false => ⟨gs, v⟩
  | Sum.inl true => ⟨gs ++ [⟨GateOp.and, []⟩], m + gs.length⟩
  | Sum.inr w => ⟨gs ++ [⟨GateOp.or, [v, w]⟩], m + gs.length⟩

lemma attachOr_spec (m v : ℕ) (gs : List Gate) (s : Stat) (hg : ∀ g ∈ gs, Ok g) :
    FanInTwo (attachOr m v gs s) ∧ (attachOr m v gs s).size ≤ gs.length + 1 ∧
    ∀ x : Fin m → Bool, circuitFun m (attachOr m v gs s) x =
      ((run gs (List.ofFn x)).getD v false || Stat.val (run gs (List.ofFn x)) s) := by
  have appendOk (g : Gate) (h : Ok g) :
      FanInTwo ⟨gs ++ [g], m + gs.length⟩ := by
    intro g' h'
    rcases List.mem_append.mp h' with hm | hm
    · exact hg g' hm
    · simp only [List.mem_singleton] at hm
      subst g'
      exact h
  have output (g : Gate) (x : Fin m → Bool) :
      circuitFun m ⟨gs ++ [g], m + gs.length⟩ x =
        g.op.eval (g.inputs.map fun i => (run gs (List.ofFn x)).getD i false) := by
    change (run (gs ++ [g]) (List.ofFn x)).getD (m + gs.length) false = _
    have hl : (run gs (List.ofFn x)).length = m + gs.length := by simp [run_length]
    rw [run_append, ← hl]
    exact step_at _ _
  cases s with
  | inl b =>
    cases b
    · refine ⟨hg, by simp [attachOr, Circuit.size], ?_⟩
      intro x
      change (run gs (List.ofFn x)).getD v false = (_ || false)
      simp
    · refine ⟨appendOk _ ⟨by simp, by simp⟩, by simp [attachOr, Circuit.size], ?_⟩
      intro x
      rw [attachOr, output]
      simp [GateOp.eval, Stat.val]
  | inr w =>
    refine ⟨appendOk _ ⟨by simp, by simp⟩, by simp [attachOr, Circuit.size], ?_⟩
    intro x
    rw [attachOr, output]
    simp [GateOp.eval, Stat.val]

lemma too_many_drops (C : Circuit) (m k v : ℕ) (hk : k ≤ C.gates.length)
    (hv : v < m + k) (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true)
    (saved : (compiledCut C m k v).2.length + 2 ≤ C.gates.length) : False := by
  obtain ⟨hok, hsem, hprefix⟩ := cut_compile C m k v hk hv hlegal
  let z := compiledCut C m k v
  let D := attachOr m v z.2 (z.1.getD C.output (Sum.inl false))
  obtain ⟨hfan, hsize, hfun⟩ := attachOr_spec m v z.2 (z.1.getD C.output (Sum.inl false)) hok
  have heq : circuitFun m D = circuitFun m C := by
    funext x
    change circuitFun m (attachOr m v z.2 (z.1.getD C.output (Sum.inl false))) x = _
    rw [hfun x, hprefix x, ← hsem x, cut_or C m k v hk hv hot x]
  have hle := hmin.2 D hfan heq
  change C.gates.length ≤ D.size at hle
  change D.size ≤ (compiledCut C m k v).2.length + 1 at hsize
  omega

lemma wireEnv_represents (wires : List Bool) (k : ℕ) (hk : wires.length = k) (i : ℕ) :
    wires.getD i false = Stat.val wires ((wireEnv k).getD i (Sum.inl false)) := by
  by_cases hi : i < k
  · rw [wireEnv_read _ _ hi]
    rfl
  · rw [List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by simp [wireEnv]; omega)]
    rfl

lemma minimal_keeps_gate (C : Circuit) (m j : ℕ) (hj : j < C.gates.length)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y) :
    (gateResult m (wireEnv (m + j), C.gates.take j) C.gates[j]).1 ≠ none := by
  intro hd
  let rest := C.gates.drop j
  let pre := C.gates.take j
  let st := (wireEnv (m + j), pre)
  let z := elimPass m rest st
  have hrest : ∀ g ∈ rest, NOk g := fun g hg => hlegal g ((List.drop_sublist _ _).subset hg)
  have hpre : ∀ g ∈ pre, Ok g := fun g hg => (hlegal g ((List.take_sublist _ _).subset hg)).1
  have hprelen : pre.length = j := List.length_take_of_le (by omega)
  have hv : ∀ s ∈ st.1, Stat.Valid s (m + pre.length) := by
    rw [hprelen]
    exact statValid_wireEnv _
  obtain ⟨_, hok, _, _, _, hsem⟩ := elimPass_main m rest hrest st.1 pre hv hpre
  have hfun (x : Fin m → Bool) :
      circuitFun m C x = Stat.val (run z.2 (List.ofFn x)) (z.1.getD C.output (Sum.inl false)) := by
    change (run C.gates (List.ofFn x)).getD C.output false = _
    conv_lhs => rw [← List.take_append_drop j C.gates, run_append]
    apply hsem x (run pre (List.ofFn x))
    · simp [st, wireEnv, pre, cut_prefix_length _ _ _ (by omega : j ≤ C.gates.length)]
    · exact wireEnv_represents _ _ (cut_prefix_length C m j (by omega) x)
  have hlen : rest.length = C.gates.length - j := List.length_drop
  have hlt : 0 < rest.length := by omega
  have hr : rest[0] = C.gates[j] := by simp [rest]
  have hst0 : stateAt m rest st 0 = st := rfl
  have hst1 : (stateAt m rest st 1).2 = pre := by
    rw [stateAt_succ m rest st hlt, hr, hst0]
    exact elimStep_no_gate _ _ _ hd
  have hsize := stateAt_size_bound m rest st 1 rest.length (by omega) le_rfl
  have hz : stateAt m rest st rest.length = z := by simp [stateAt, z]
  rw [hz, hst1, hprelen, hlen] at hsize
  cases he : z.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, y, hxy⟩ := hvar
    apply hxy
    rw [hfun x, hfun y, he]
    rfl
  | inr w =>
    let D : Circuit := ⟨z.2, w⟩
    have hEq : circuitFun m D = circuitFun m C := by
      funext x
      rw [hfun x, he]
      rfl
    have hl := hmin.2 D hok hEq
    change C.gates.length ≤ z.2.length at hl
    omega

lemma minimal_inputs_before (C : Circuit) (m j : ℕ) (hj : j < C.gates.length)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y) :
    ∀ w ∈ (C.gates[j]).inputs, w < m + j := by
  intro w hw
  by_contra hn
  apply minimal_keeps_gate C m j hj hlegal hmin hvar
  have hg := hlegal C.gates[j] (List.getElem_mem _)
  apply gateResult_no_gate_of_constant _ _ _ hg w hw false
  exact List.getD_eq_default _ _ (by simp [wireEnv]; omega)

lemma minimal_or_binary (C : Circuit) (m j : ℕ) (hj : j < C.gates.length)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y)
    (hor : (C.gates[j]).op = GateOp.or) :
    (C.gates[j]).inputs.length = 2 := by
  have hg := (hlegal C.gates[j] (List.getElem_mem _)).1.2
  by_contra hn
  apply minimal_keeps_gate C m j hj hlegal hmin hvar
  rcases he : (C.gates[j]).inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [gateResult, gateArgs, hor, he, simplify, simpOr]
  · simp only [gateResult, gateArgs, hor, he, simplify, List.map_cons, List.map_nil]
    cases (wireEnv (m + j)).getD a (Sum.inl false) <;> rfl
  · simp only [he, List.length_cons] at hg hn
    omega

lemma drop_split (gs : List Gate) (k j : ℕ) (hk : k ≤ j) (hj : j < gs.length) :
    gs.drop k = (gs.drop k).take (j - k) ++ gs[j] :: gs.drop (j + 1) := by
  calc
    gs.drop k = (gs.drop k).take (j - k) ++ (gs.drop k).drop (j - k) :=
      (List.take_append_drop _ _).symm
    _ = _ := by
      rw [List.drop_drop, show k + (j - k) = j by omega, List.drop_eq_getElem_cons hj]

lemma take_split (gs : List Gate) (k j : ℕ) (hk : k ≤ j) (hj : j < gs.length) :
    gs.take (j + 1) = (gs.take k ++ (gs.drop k).take (j - k)) ++ [gs[j]] := by
  rw [List.take_succ_eq_append_getElem hj]
  have hs := (List.take_append_drop k (gs.take j)).symm
  rw [List.take_take, min_eq_left hk, List.drop_take] at hs
  rw [hs]

def Reads (C : Circuit) (v : ℕ) (j : Fin C.gates.length) : Prop :=
  v ∈ (C.gates.get j).inputs

lemma readers_avoid_middle (C : Circuit) (k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hu : ∀ r, Reads C v r → r = j) :
    ∀ g ∈ (C.gates.drop k).take (j.val - k), v ∉ g.inputs := by
  intro g hg hv
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hg
  have hr' : r < j.val - k := lt_of_lt_of_le hr (List.length_take_le _ _)
  have hlt : k + r < C.gates.length := by omega
  have hRead : Reads C v ⟨k + r, hlt⟩ := by simpa [Reads] using hv
  have he := congrArg Fin.val (hu _ hRead)
  change k + r = j.val at he
  omega

lemma readers_avoid_tail (C : Circuit) (v : ℕ) (j : Fin C.gates.length)
    (hu : ∀ r, Reads C v r → r = j) :
    ∀ g ∈ C.gates.drop (j.val + 1), v ∉ g.inputs := by
  intro g hg hv
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hg
  have hlt : j.val + 1 + r < C.gates.length := by
    simp only [List.length_drop] at hr
    omega
  have hRead : Reads C v ⟨j.val + 1 + r, hlt⟩ := by simpa [Reads] using hv
  have he := congrArg Fin.val (hu _ hRead)
  change j.val + 1 + r = j.val at he
  omega

def beforeReader (C : Circuit) (m k : ℕ) (j : Fin C.gates.length) (x : Fin m → Bool) : List Bool :=
  run ((C.gates.drop k).take (j.val - k)) (run (C.gates.take k) (List.ofFn x))

def forcedBeforeReader (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (x : Fin m → Bool) : List Bool :=
  run ((C.gates.drop k).take (j.val - k)) ((run (C.gates.take k) (List.ofFn x)).set v true)

lemma beforeReader_cut (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hv : v < m + k) (hu : ∀ r, Reads C v r → r = j)
    (x : Fin m → Bool) :
    let w := beforeReader C m k j x
    let u := forcedBeforeReader C m k v j x
    w.length = m + j.val ∧ u.length = w.length ∧
    u.getD v false = true ∧ (∀ i, i ≠ v → u.getD i false = w.getD i false) := by
  let B := (C.gates.drop k).take (j.val - k)
  let pre := run (C.gates.take k) (List.ofFn x)
  have hpre : pre.length = m + k := cut_prefix_length C m k (by omega) x
  have hB : B.length = j.val - k := by
    unfold B
    apply List.length_take_of_le
    simp only [List.length_drop]
    omega
  have hvpre : v < pre.length := hpre ▸ hv
  change (run B pre).length = _ ∧ (run B (pre.set v true)).length = (run B pre).length ∧ _ ∧ _
  refine ⟨by rw [run_length, hpre, hB]; omega, by simp [run_length], ?_, ?_⟩
  · change (run B (pre.set v true)).getD v false = true
    rw [run_preserves _ _ _ (by simpa using hvpre)]
    exact getD_set_same _ _ _ _ hvpre
  · refine run_agree (fun i => i = v) B ?_ (pre.set v true) pre (by simp) ?_
    · intro g hg i hi h
      subst i
      exact readers_avoid_middle C k v j hk hu g hg hi
    · intro i hi
      exact getD_set_other _ _ _ _ _ (Ne.symm hi)

lemma force_read_split (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (x : Fin m → Bool) :
    forceValue C m k v true x =
      (run (C.gates.drop (j.val + 1))
        (step (forcedBeforeReader C m k v j x) (C.gates.get j))).getD C.output false := by
  unfold forceValue forcedBeforeReader
  conv_lhs => rw [drop_split C.gates k j.val hk j.isLt, run_append]
  rfl

lemma actual_read_split (C : Circuit) (m k : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (x : Fin m → Bool) :
    circuitFun m C x = (run (C.gates.drop (j.val + 1))
      (step (beforeReader C m k j x) (C.gates.get j))).getD C.output false := by
  change (run C.gates (List.ofFn x)).getD C.output false = _
  conv_lhs => rw [← List.take_append_drop k C.gates, run_append,
    drop_split C.gates k j.val hk j.isLt, run_append]
  rfl

lemma prefix_read_split (C : Circuit) (m k : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (x : Fin m → Bool) :
    run (C.gates.take (j.val + 1)) (List.ofFn x) =
      step (beforeReader C m k j x) (C.gates.get j) := by
  rw [take_split C.gates k j.val hk j.isLt, run_append, run_append]
  rfl

lemma force_advance (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hv : v < m + k) (hout : C.output ≠ v)
    (hread : Reads C v j) (hu : ∀ r, Reads C v r → r = j)
    (hor : (C.gates.get j).op = GateOp.or) (x : Fin m → Bool) :
    forceValue C m k v true x = forceValue C m (j.val + 1) (m + j.val) true x := by
  rw [force_read_split C m k v j hk]
  unfold forceValue
  rw [prefix_read_split C m k j hk]
  let w := beforeReader C m k j x
  let u := forcedBeforeReader C m k v j x
  let g := C.gates.get j
  obtain ⟨hwl, hul, hhot, hag⟩ := beforeReader_cut C m k v j hk hv hu x
  change w.length = m + j.val at hwl
  change u.length = w.length at hul
  change u.getD v false = true at hhot
  have halt : (step u g).getD (m + j.val) false = true := by
    rw [← hwl, ← hul, step_at]
    change (C.gates.get j).op.eval _ = true
    rw [hor]
    exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨v, hread, hhot⟩, rfl⟩
  apply run_agree (fun i => i = v) _ _ (step u g)
    ((step w g).set (m + j.val) true) (by simp [step, hul]) _ C.output hout
  · intro d hd i hi he
    subst i
    exact readers_avoid_tail C v j hu d hd hi
  · intro i hi
    by_cases he : i = m + j.val
    · subst i
      rw [halt, getD_set_same _ _ _ _ (by simp [step, hwl])]
    · rw [getD_set_other _ _ _ _ _ (Ne.symm he), step_off _ _ _ (by omega), step_off _ _ _ (by omega)]
      exact hag i hi

lemma force_irrelevant_of_dead_reader (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hv : v < m + k) (hout : C.output ≠ v)
    (hu : ∀ r, Reads C v r → r = j) (hdead : ∀ r, ¬ Reads C (m + j.val) r)
    (houtJ : C.output ≠ m + j.val) (x : Fin m → Bool) :
    forceValue C m k v true x = circuitFun m C x := by
  rw [force_read_split C m k v j hk, actual_read_split C m k j hk]
  let w := beforeReader C m k j x
  let u := forcedBeforeReader C m k v j x
  let g := C.gates.get j
  obtain ⟨hwl, hul, _, hag⟩ := beforeReader_cut C m k v j hk hv hu x
  change w.length = m + j.val at hwl
  change u.length = w.length at hul
  apply run_agree (fun i => i = v ∨ i = m + j.val) _ _ (step u g) (step w g)
    (by simp [step, hul]) _ C.output (fun h => h.elim hout houtJ)
  · intro d hd i hi h
    rcases h with h | h
    · rw [h] at hi
      exact readers_avoid_tail C v j hu d hd hi
    · rw [h] at hi
      obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hd
      have hlt : j.val + 1 + r < C.gates.length := by
        simp only [List.length_drop] at hr
        omega
      apply hdead ⟨j.val + 1 + r, hlt⟩
      simpa [Reads] using hi
  · intro i hi
    rw [step_off _ _ _ (by intro h; apply hi; right; omega),
      step_off _ _ _ (by intro h; apply hi; right; omega)]
    exact hag i (fun he => hi (Or.inl he))

lemma force_irrelevant_without_reader (C : Circuit) (m k v : ℕ)
    (hn : ∀ j, ¬ Reads C v j) (ho : C.output ≠ v) (x : Fin m → Bool) :
    forceValue C m k v true x = circuitFun m C x := by
  change (run (C.gates.drop k) ((run (C.gates.take k) (List.ofFn x)).set v true)).getD C.output false =
    (run C.gates (List.ofFn x)).getD C.output false
  conv_rhs => rw [← List.take_append_drop k C.gates, run_append]
  apply run_agree (fun i => i = v) _ _ _ _ (by simp) _ C.output ho
  · intro d hd i hi h
    subst i
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hd
    have hlt : k + r < C.gates.length := by
      simp only [List.length_drop] at hr
      omega
    apply hn ⟨k + r, hlt⟩
    simpa [Reads] using hi
  · intro i hi
    exact getD_set_other _ _ _ _ _ (Ne.symm hi)

lemma stateAt_env_length (n : ℕ) (gs : List Gate) (st : List Stat × List Gate)
    (i : ℕ) (hi : i ≤ gs.length) :
    (stateAt n gs st i).1.length = st.1.length + i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [stateAt_succ n gs st (by omega : i < gs.length), elimStep_env, List.length_append,
      List.length_singleton, ih (by omega)]
    omega

def atReader (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length) : List Stat × List Gate :=
  stateAt m (C.gates.drop k) (cutState C m k v) (j.val - k)

lemma reader_index (C : Circuit) (k : ℕ) (j : Fin C.gates.length) (hk : k ≤ j.val) :
    j.val - k < (C.gates.drop k).length := by
  simp only [List.length_drop]
  omega

lemma reader_gate_eq (C : Circuit) (k : ℕ) (j : Fin C.gates.length) (hk : k ≤ j.val) :
    (C.gates.drop k)[j.val - k]'(reader_index C k j hk) = C.gates.get j := by
  simp [show k + (j.val - k) = j.val by omega]

lemma atReader_constant (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hv : v < m + k) :
    (atReader C m k v j).1.getD v (Sum.inl false) = Sum.inl false := by
  let st := cutState C m k v
  have hl : v < st.1.length := by simpa [st, cutState, wireEnv] using hv
  have h := stateAt_preserves m (C.gates.drop k) st 0 (j.val - k) v (by omega)
    (Nat.le_of_lt (reader_index C k j hk)) hl
  change (stateAt m (C.gates.drop k) st (j.val - k)).1.getD v (Sum.inl false) = _
  rw [h]
  exact getD_set_same _ _ _ _ (by simpa [wireEnv] using hv)

lemma reader_drop (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hk : k ≤ j.val) (hg : NOk (C.gates.get j)) (w : ℕ) (hr : Reads C w j)
    (b : Bool) (hc : (atReader C m k v j).1.getD w (Sum.inl false) = Sum.inl b) :
    (stateAt m (C.gates.drop k) (cutState C m k v) (j.val - k + 1)).2 =
      (atReader C m k v j).2 := by
  rw [stateAt_succ m _ _ (reader_index C k j hk), reader_gate_eq C k j hk]
  exact elimStep_no_gate _ _ _ (gateResult_no_gate_of_constant _ _ _ hg w hr b hc)

lemma both_readers_save (C : Circuit) (m k v : ℕ) (j t : Fin C.gates.length)
    (hkj : k ≤ j.val) (hjt : j < t) (hlegal : ∀ g ∈ C.gates, NOk g)
    (hj : Reads C v j) (hv : v < m + k)
    (w : ℕ) (ht : Reads C w t) (b : Bool)
    (hconst : (atReader C m k v t).1.getD w (Sum.inl false) = Sum.inl b) :
    (compiledCut C m k v).2.length + 2 ≤ C.gates.length := by
  have hkt : k ≤ t.val := by omega
  have hdrop := stateAt_two_drops m (C.gates.drop k) (cutState C m k v)
    (j.val - k) (t.val - k) (by omega) (reader_index C k t hkt)
    (reader_drop C m k v j hkj (hlegal _ (List.get_mem _ _)) v hj false
      (atReader_constant C m k v j hkj hv))
    (reader_drop C m k v t hkt (hlegal _ (List.get_mem _ _)) w ht b hconst)
  change (compiledCut C m k v).2.length + 2 ≤ _ at hdrop
  simpa [cutState, List.length_take_of_le (by omega : k ≤ C.gates.length),
    List.length_drop, Nat.add_sub_of_le (by omega : k ≤ C.gates.length)] using hdrop

lemma otherGateConstant (n : ℕ) (st : List Stat × List Gate) (g : Gate)
    (hg : NOk g) (v : ℕ) (hread : v ∈ g.inputs)
    (hc : st.1.getD v (Sum.inl false) = Sum.inl false)
    (hbad : g.op ≠ GateOp.or ∨ g.inputs = [v, v]) :
    ∃ b, (gateResult n st g).2 = Sum.inl b := by
  have hop := hg.1.1
  change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
  rcases hop with hop | hop | hop
  · rcases he : g.inputs with _ | ⟨a, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩
    · simp [he] at hread
    · have h : v = a := by simpa [he] using hread
      subst a
      exact ⟨false, by simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify, simpAnd]⟩
    · have hm : v = a ∨ v = d := by simpa [he] using hread
      rcases hm with h | h
      · subst a
        refine ⟨false, ?_⟩
        simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify]
        cases st.1.getD d (Sum.inl false) <;> rfl
      · subst d
        refine ⟨false, ?_⟩
        simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify]
        cases st.1.getD a (Sum.inl false) with
        | inl b => cases b <;> rfl
        | inr _ => rfl
    · have hh := hg.1.2
      simp only [he, List.length_cons] at hh
      omega
  · have he := hbad.resolve_left (fun hn => hn hop)
    exact ⟨false, by simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify, simpOr, Bool.false_or]⟩
  · have hs := hg.2 hop
    rcases he : g.inputs with _ | ⟨a, _ | ⟨d, rest⟩⟩
    · simp [he] at hread
    · have h : v = a := by simpa [he] using hread
      subst a
      exact ⟨true, by simp only [gateResult, gateArgs, hop, he, List.map_cons, List.map_nil, hc, simplify, simpNot, Bool.not_false]⟩
    · simp only [he, List.length_cons] at hs
      omega

lemma cut_remembers_result (C : Circuit) (m k v : ℕ) (j : Fin C.gates.length)
    (hkj : k ≤ j.val) (b : Bool)
    (he : (gateResult m (atReader C m k v j) (C.gates.get j)).2 = Sum.inl b) :
    let p := j.val - k + 1
    let st := cutState C m k v
    let gs := C.gates.drop k
    (∀ t, p ≤ t → t ≤ gs.length →
      (stateAt m gs st t).1.getD (m + j.val) (Sum.inl false) = Sum.inl b) := by
  intro p st gs t hpt htl
  have hj := reader_index C k j hkj
  have hz : st.1.length = m + k := by simp [st, cutState, wireEnv]
  have hlen := stateAt_env_length m gs st (j.val - k) (Nat.le_of_lt hj)
  have hidx : (stateAt m gs st (j.val - k)).1.length = m + j.val := by
    rw [hlen, hz]
    omega
  have hp : (stateAt m gs st p).1.getD (m + j.val) (Sum.inl false) = Sum.inl b := by
    change (stateAt m gs st (j.val - k + 1)).1.getD (m + j.val) (Sum.inl false) = _
    rw [stateAt_succ m _ _ hj, elimStep_env, reader_gate_eq C k j hkj, ← hidx, getD_snoc_eq]
    exact he
  have hpos : m + j.val < (stateAt m gs st p).1.length := by
    rw [stateAt_env_length m gs st p (by omega), hz]
    dsimp [p]
    omega
  rw [stateAt_preserves m gs st p t _ hpt htl hpos]
  exact hp

lemma constant_output_at_cut (C : Circuit) (m k v : ℕ)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hk : k < C.gates.length) (hv : v < m + k)
    (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true)
    (hfalse : ∃ x : Fin m → Bool, circuitFun m C x = false) (b : Bool)
    (hconst : (compiledCut C m k v).1.getD C.output (Sum.inl false) = Sum.inl b) : False := by
  have hn : ∀ x : Fin m → Bool, forceValue C m k v false x = b := by
    obtain ⟨_, hsem, _⟩ := cut_compile C m k v (by omega) hv hlegal
    intro x
    rw [hsem x, hconst]
    rfl
  cases b
  · let D : Circuit := ⟨C.gates.take k, v⟩
    have hd : FanInTwo D := fun g hg => (hlegal g ((List.take_sublist _ _).subset hg)).1
    have he : circuitFun m D = circuitFun m C := by
      funext x
      rw [cut_or C m k v (by omega) hv hot x, hn x, Bool.or_false]
      rfl
    have hle := hmin.2 D hd he
    change C.gates.length ≤ (C.gates.take k).length at hle
    rw [List.length_take_of_le (by omega)] at hle
    omega
  · obtain ⟨x, hx⟩ := hfalse
    rw [cut_or C m k v (by omega) hv hot x, hn x, Bool.or_true] at hx
    contradiction

def OrLink (C : Circuit) (m v : ℕ) (j : Fin C.gates.length) : Prop :=
  (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
    Reads C v j ∧ (∀ r, Reads C v r → r = j) ∧
    ∃ w ∈ (C.gates.get j).inputs, w ≠ v ∧ w < m + j.val

lemma next_or (C : Circuit) (m k v : ℕ) (hboundary : v + 1 = m + k)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y)
    (hfalse : ∃ x : Fin m → Bool, circuitFun m C x = false)
    (hout : C.output ≠ v) (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true) :
    ∃ j : Fin C.gates.length, k ≤ j.val ∧ OrLink C m v j := by
  have hv : v < m + k := by omega
  have hpos (r : Fin C.gates.length) (hr : Reads C v r) : k ≤ r.val := by
    have hi := minimal_inputs_before C m r.val r.isLt hlegal hmin hvar v hr
    omega
  have hex : ∃ j, Reads C v j := by
    by_contra! hn
    obtain ⟨x, hx⟩ := hfalse
    have he := force_irrelevant_without_reader C m k v hn hout x
    rw [hot x, hx] at he
    contradiction
  obtain ⟨j, hj⟩ := hex
  have hkj := hpos j hj
  have huniq (r : Fin C.gates.length) (hr : Reads C v r) : r = j := by
    by_contra hne
    have hkr := hpos r hr
    apply too_many_drops C m k v (by omega) hv hlegal hmin hot
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact both_readers_save C m k v r j hkr hlt hlegal hr hv v hj false
        (atReader_constant C m k v j hkj hv)
    · exact both_readers_save C m k v j r hkj hgt hlegal hj hv v hr false
        (atReader_constant C m k v r hkr hv)
  have hproper : ¬ ((C.gates.get j).op ≠ GateOp.or ∨ (C.gates.get j).inputs = [v, v]) := by
    intro hbad
    obtain ⟨b, he⟩ := otherGateConstant m (atReader C m k v j) (C.gates.get j)
      (hlegal _ (List.get_mem _ _)) v hj (atReader_constant C m k v j hkj hv) hbad
    have hrm := cut_remembers_result C m k v j hkj b he
    by_cases hoj : C.output = m + j.val
    · apply constant_output_at_cut C m k v hlegal hmin (by omega) hv hot hfalse b
      rw [hoj]
      have hend : j.val - k + 1 ≤ (C.gates.drop k).length := by
        have h := reader_index C k j hkj
        omega
      simpa only [stateAt, List.take_length, compiledCut] using hrm _ hend le_rfl
    · have hnext : ∃ t, Reads C (m + j.val) t := by
        by_contra! hdead
        obtain ⟨x, hx⟩ := hfalse
        have he := force_irrelevant_of_dead_reader C m k v j hkj hv hout huniq hdead hoj x
        rw [hot x, hx] at he
        contradiction
      obtain ⟨t, ht⟩ := hnext
      have hjt : j < t := by
        have hlt := minimal_inputs_before C m t.val t.isLt hlegal hmin hvar (m + j.val) ht
        change j.val < t.val
        omega
      have hkt : k ≤ t.val := by omega
      have hti := reader_index C k t hkt
      have hc := hrm (t.val - k) (by omega) (by omega)
      exact too_many_drops C m k v (by omega) hv hlegal hmin hot
        (both_readers_save C m k v j t hkj hjt hlegal hj hv (m + j.val) ht b hc)
  have hor : (C.gates.get j).op = GateOp.or := by
    by_contra hn
    exact hproper (Or.inl hn)
  have hlen := minimal_or_binary C m j.val j.isLt hlegal hmin hvar hor
  change (C.gates.get j).inputs.length = 2 at hlen
  refine ⟨j, hkj, hor, hlen, hj, huniq, ?_⟩
  rcases he : (C.gates.get j).inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rw [he] at hlen
    simp at hlen
  · rw [he] at hlen
    simp at hlen
  · have hnil : rest = [] := by
      apply List.length_eq_zero_iff.mp
      rw [he] at hlen
      simp only [List.length_cons] at hlen
      omega
    subst rest
    have hm : v = a ∨ v = b := by
      change v ∈ (C.gates.get j).inputs at hj
      rw [he] at hj
      simpa using hj
    rcases hm with ha | hb
    · refine ⟨b, by simp, ?_, ?_⟩
      · intro hb
        exact hproper (Or.inr (by simpa [ha, hb] using he))
      · have hm : b ∈ (C.gates.get j).inputs := by rw [he]; simp
        exact minimal_inputs_before C m j.val j.isLt hlegal hmin hvar b hm
    · refine ⟨a, by simp, ?_, ?_⟩
      · intro ha
        exact hproper (Or.inr (by simpa [ha, hb] using he))
      · have hm : a ∈ (C.gates.get j).inputs := by rw [he]; simp
        exact minimal_inputs_before C m j.val j.isLt hlegal hmin hvar a hm

def HasWireChain (C : Circuit) (m v : ℕ) : Prop :=
  ∃ (l : ℕ) (f : Fin (l + 1) → ℕ), f 0 = v ∧ f (Fin.last l) = C.output ∧
    ∀ i : Fin l, ∃ j : Fin C.gates.length,
      f i.succ = m + j.val ∧ OrLink C m (f i.castSucc) j ∧ f i.castSucc < f i.succ

lemma cut_chain (C : Circuit) (m : ℕ)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit m C)
    (hvar : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y)
    (hfalse : ∃ x : Fin m → Bool, circuitFun m C x = false)
    (k v : ℕ) (hboundary : v + 1 = m + k) (hk : k ≤ C.gates.length)
    (hot : ∀ x : Fin m → Bool, forceValue C m k v true x = true) :
    HasWireChain C m v := by
  by_cases hout : C.output = v
  · exact ⟨0, fun _ => v, rfl, hout.symm, fun i => Fin.elim0 i⟩
  obtain ⟨j, hjk, hj⟩ := next_or C m k v hboundary hlegal hmin hvar hfalse hout hot
  have hnow : v < m + j.val := by omega
  have hhot' (x : Fin m → Bool) : forceValue C m (j.val + 1) (m + j.val) true x = true :=
    (force_advance C m k v j hjk (by omega) hout hj.2.2.1 hj.2.2.2.1 hj.1 x).symm.trans (hot x)
  obtain ⟨l, f, hstart, hend, hf⟩ :=
    cut_chain C m hlegal hmin hvar hfalse (j.val + 1) (m + j.val) (by omega) (by omega) hhot'
  refine ⟨l + 1, Fin.cons v f, by simp, by simpa [← Fin.succ_last] using hend, ?_⟩
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · refine ⟨j, ?_, ?_, ?_⟩
    · simpa using hstart
    · simpa using hj
    · simpa [hstart] using hnow
  · obtain ⟨r, hr, hor, hlt⟩ := hf a
    exact ⟨r, by simpa using hr, by simpa using hor, by simpa using hlt⟩
termination_by C.gates.length - k
decreasing_by omega

lemma ofFn_set_last (n : ℕ) (x : Fin (n + 1) → Bool) (b : Bool) :
    (List.ofFn x).set n b = List.ofFn (Fin.snoc (fun i : Fin n => x i.castSucc) b) := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  have hi : i < n + 1 := by simpa using hi₁
  by_cases he : i = n
  · subst i
    rw [List.getElem_set_self, List.getElem_ofFn]
    change b = (Fin.snoc (fun i : Fin n => x i.castSucc) b : Fin (n + 1) → Bool) (Fin.last n)
    rw [Fin.snoc_last]
  · rw [List.getElem_set_ne (Ne.symm he)]
    simp only [List.getElem_ofFn]
    have hlt : i < n := by omega
    change x (⟨i, hlt⟩ : Fin n).castSucc =
      (Fin.snoc (fun p : Fin n => x p.castSucc) b : Fin (n + 1) → Bool) (⟨i, hlt⟩ : Fin n).castSucc
    rw [Fin.snoc_castSucc]

lemma output_within (C : Circuit) (m : ℕ) (x : Fin m → Bool)
    (ht : circuitFun m C x = true) : C.output < m + C.gates.length := by
  by_contra h
  have hout : (run C.gates (List.ofFn x)).getD C.output false = false :=
    List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
  change (run C.gates (List.ofFn x)).getD C.output false = true at ht
  rw [ht] at hout
  contradiction

lemma minimal_last_output (C : Circuit) (m : ℕ) (hmin : IsMinimalCircuit m C)
    (hge : m ≤ C.output) (hlt : C.output < m + C.gates.length) :
    C.output + 1 = m + C.gates.length := by
  let k := C.output + 1 - m
  have hk : k ≤ C.gates.length := by omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have hl : FanInTwo D := fun g hg => hmin.1 g ((List.take_sublist _ _).subset hg)
  have he : circuitFun m D = circuitFun m C := by
    funext x
    change (run (C.gates.take k) (List.ofFn x)).getD C.output false =
      (run C.gates (List.ofFn x)).getD C.output false
    conv_rhs => rw [← List.take_append_drop k C.gates, run_append]
    symm
    apply run_preserves
    rw [cut_prefix_length _ _ _ hk]
    omega
  have hb := hmin.2 D hl he
  change C.gates.length ≤ (C.gates.take k).length at hb
  rw [List.length_take_of_le hk] at hb
  omega

lemma h_false_and_true (n : ℕ) (H : (Fin n → Bool) → Bool)
    (hH : ∃ y y', H y ≠ H y') : (∃ x, H x = false) ∧ (∃ x, H x = true) := by
  obtain ⟨y, y', hn⟩ := hH
  cases hy : H y <;> cases hy' : H y'
  · rw [hy, hy'] at hn
    contradiction
  · exact ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
  · exact ⟨⟨y', hy'⟩, ⟨y, hy⟩⟩
  · rw [hy, hy'] at hn
    contradiction

lemma x_or_H_not_input (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (htrue : ∃ y, H y = true)
    (hfn : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) : n + 1 ≤ C.output := by
  by_contra! hout
  have ein (x : Fin (n + 1) → Bool) :
      circuitFun (n + 1) C x = x ⟨C.output, hout⟩ := by
    change (run C.gates (List.ofFn x)).getD C.output false = _
    rw [run_preserves _ _ _ (by simpa using hout)]
    exact getD_ofFn _ _ hout
  by_cases he : C.output = n
  · obtain ⟨y, hy⟩ := htrue
    let x : Fin (n + 1) → Bool := Fin.snoc y false
    have hx := ein x
    have hlast : (⟨C.output, hout⟩ : Fin (n + 1)) = Fin.last n := Fin.ext he
    rw [hlast] at hx
    have h := hfn x
    have hf : (fun i : Fin n => x i.castSucc) = y := by
      funext i
      exact Fin.snoc_castSucc _ _ _
    rw [hf, hy, Bool.or_true] at h
    rw [h] at hx
    simpa [x] using hx
  · let x : Fin (n + 1) → Bool := Fin.snoc (fun _ : Fin n => false) true
    let i : Fin n := ⟨C.output, by omega⟩
    have hx := ein x
    change circuitFun (n + 1) C x = x i.castSucc at hx
    have hh : circuitFun (n + 1) C x = true := by
      rw [hfn x]
      simp [x]
    rw [hh] at hx
    simpa [x] using hx

lemma start_chain (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hlegal : ∀ g ∈ C.gates, NOk g) (hmin : IsMinimalCircuit (n + 1) C)
    (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hfn : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    C.output + 1 = n + 1 + C.gates.length ∧ n + 1 ≤ C.output ∧
    HasWireChain C (n + 1) n ∧
    ∀ j : Fin C.gates.length, ∀ w, Reads C w j → w < n + 1 + j.val := by
  obtain ⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩ := h_false_and_true n H hH
  have hcase (y : Fin n → Bool) (b : Bool) :
      circuitFun (n + 1) C (Fin.snoc y b) = (b || H y) := by
    rw [hfn]
    simp
  have h0 : circuitFun (n + 1) C (Fin.snoc y₀ false) = false := by
    rw [hcase, hy₀]
    rfl
  have h1 : circuitFun (n + 1) C (Fin.snoc y₁ false) = true := by
    rw [hcase, hy₁]
    rfl
  have hvar : ∃ x y : Fin (n + 1) → Bool, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C y :=
    ⟨Fin.snoc y₀ false, Fin.snoc y₁ false, by rw [h0, h1]; decide⟩
  have hge := x_or_H_not_input n C H ⟨y₁, hy₁⟩ hfn
  have hlast := minimal_last_output C (n + 1) hmin hge (output_within C _ _ h1)
  have hstart (x : Fin (n + 1) → Bool) : forceValue C (n + 1) 0 n true x = true := by
    change (run C.gates ((List.ofFn x).set n true)).getD C.output false = true
    rw [ofFn_set_last]
    change circuitFun (n + 1) C (Fin.snoc (fun i : Fin n => x i.castSucc) true) = true
    rw [hcase]
    rfl
  refine ⟨hlast, hge, cut_chain C _ hlegal hmin hvar ⟨_, h0⟩ 0 n (by omega) (by omega) hstart, ?_⟩
  intro j w hw
  exact minimal_inputs_before C (n + 1) j.val j.isLt hlegal hmin hvar w hw

def normalized (C : Circuit) : Circuit := ⟨C.gates.map normGate, C.output⟩

lemma normalized_len (C : Circuit) : (normalized C).gates.length = C.gates.length := by
  simp [normalized]

lemma normalized_legal (C : Circuit) (h : FanInTwo C) :
    ∀ g ∈ (normalized C).gates, NOk g := by
  intro g hg
  obtain ⟨origin, ho, rfl⟩ := List.mem_map.mp hg
  exact normGate_nok origin (h origin ho)

lemma normalized_fun (C : Circuit) (m : ℕ) : circuitFun m (normalized C) = circuitFun m C := by
  funext x
  change (run (C.gates.map normGate) (List.ofFn x)).getD C.output false =
    (run C.gates (List.ofFn x)).getD C.output false
  rw [run_norm]

lemma normalized_min (C : Circuit) (m : ℕ) (hc : IsMinimalCircuit m C) :
    IsMinimalCircuit m (normalized C) := by
  refine ⟨fun g hg => (normalized_legal C hc.1 g hg).1, ?_⟩
  intro D hD he
  rw [normalized_fun] at he
  simpa [Circuit.size, normalized_len] using hc.2 D hD he

def EffRead (C : Circuit) (v : ℕ) (j : Fin C.gates.length) : Prop :=
  ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some v) ∨
    ((C.gates.get j).op ≠ GateOp.not ∧ v ∈ (C.gates.get j).inputs)

def Link (C : Circuit) (m a b : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, b = m + j.val ∧ EffRead C a j

lemma normGate_op (g : Gate) : (normGate g).op = g.op := by
  cases g with
  | mk op ins => cases op <;> rfl

lemma normGate_of_or (g : Gate) (hg : g.op = GateOp.or) : normGate g = g := by
  cases g with
  | mk op ins => change op = GateOp.or at hg; subst op; rfl

lemma norm_index (C : Circuit) (j : Fin (normalized C).gates.length) :
    (normalized C).gates.get j = normGate (C.gates.get (Fin.cast (normalized_len C) j)) := by
  have hj : j.val < C.gates.length := by simpa only [normalized_len] using j.isLt
  have hjm : j.val < (C.gates.map normGate).length := by simpa only [List.length_map] using hj
  change (C.gates.map normGate)[j.val]'hjm = normGate (C.gates[j.val]'hj)
  rw [List.getElem_map]

lemma norm_eff (C : Circuit) (v : ℕ) (j : Fin (normalized C).gates.length) :
    Reads (normalized C) v j ↔ EffRead C v (Fin.cast (normalized_len C) j) := by
  unfold Reads EffRead
  rw [norm_index]
  generalize (C.gates.get (Fin.cast (normalized_len C) j)) = g
  rcases g with ⟨op, ins⟩
  cases op <;> simp [normGate]
  cases ins <;> simp [eq_comm]

def EffOrLink (C : Circuit) (m v : ℕ) (j : Fin C.gates.length) : Prop :=
  (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
    EffRead C v j ∧ (∀ r, EffRead C v r → r = j) ∧
    ∃ w ∈ (C.gates.get j).inputs, w ≠ v ∧ w < m + j.val

lemma norm_link (C : Circuit) (m v : ℕ) (j : Fin (normalized C).gates.length)
    (h : OrLink (normalized C) m v j) :
    EffOrLink C m v (Fin.cast (normalized_len C) j) := by
  obtain ⟨ho, hl, hr, hu, hw⟩ := h
  have hop : (C.gates.get (Fin.cast (normalized_len C) j)).op = GateOp.or := by
    rw [norm_index, normGate_op] at ho
    exact ho
  have hg : (normalized C).gates.get j = C.gates.get (Fin.cast (normalized_len C) j) :=
    (norm_index C j).trans (normGate_of_or _ hop)
  refine ⟨hop, hg ▸ hl, (norm_eff C v j).mp hr, ?_, hg ▸ hw⟩
  intro r hRead
  let r' := Fin.cast (normalized_len C).symm r
  have hr' : Fin.cast (normalized_len C) r' = r := by simp [r']
  have he : Reads (normalized C) v r' := (norm_eff C v r').mpr (hr'.symm ▸ hRead)
  rw [← hr', hu r' he]

def HasEffChain (C : Circuit) (m v : ℕ) : Prop :=
  ∃ (l : ℕ) (f : Fin (l + 1) → ℕ), f 0 = v ∧ f (Fin.last l) = C.output ∧
    ∀ i : Fin l, ∃ j : Fin C.gates.length,
      f i.succ = m + j.val ∧ EffOrLink C m (f i.castSucc) j ∧ f i.castSucc < f i.succ

lemma transfer_chain (C : Circuit) (m v : ℕ) (h : HasWireChain (normalized C) m v) :
    HasEffChain C m v := by
  obtain ⟨l, f, h0, hend, hs⟩ := h
  refine ⟨l, f, h0, hend, ?_⟩
  intro i
  obtain ⟨j, hval, hj, hlt⟩ := hs i
  exact ⟨Fin.cast (normalized_len C) j, hval, norm_link C m (f i.castSucc) j hj, hlt⟩

lemma transfer_input_bound (C : Circuit) (m : ℕ)
    (h : ∀ j : Fin (normalized C).gates.length, ∀ w, Reads (normalized C) w j → w < m + j.val) :
    ∀ j : Fin C.gates.length, ∀ w, EffRead C w j → w < m + j.val := by
  intro j w hr
  let j' := Fin.cast (normalized_len C).symm j
  have hj' : Fin.cast (normalized_len C) j' = j := by simp [j']
  exact h j' w ((norm_eff C w j').mpr (hj'.symm ▸ hr))

lemma eff_or_read (C : Circuit) (v : ℕ) (j : Fin C.gates.length)
    (ho : (C.gates.get j).op = GateOp.or) :
    EffRead C v j ↔ v ∈ (C.gates.get j).inputs := by
  unfold EffRead
  rw [ho]
  simp

lemma reach_chain (C : Circuit) (m k : ℕ) (f : Fin (k + 1 + 1) → ℕ)
    (c : Fin (k + 1) → Fin C.gates.length)
    (hval : ∀ i : Fin (k + 1), f i.succ = m + (c i).val)
    (hlink : ∀ i : Fin (k + 1), EffOrLink C m (f i.castSucc) (c i))
    (hend : f (Fin.last (k + 1)) = C.output)
    (hfinal : ∀ j : Fin C.gates.length, ¬ EffRead C C.output j) :
    ∀ w, Relation.TransGen (Link C m) (f 0) w ↔ ∃ i : Fin (k + 1), f i.succ = w := by
  have hstep (i : Fin (k + 1)) : Link C m (f i.castSucc) (f i.succ) :=
    ⟨c i, hval i, (hlink i).2.2.1⟩
  intro w
  constructor
  · intro hw
    induction hw with
    | single h =>
      obtain ⟨j, he, hr⟩ := h
      have hu := (hlink 0).2.2.2.1 j (by simpa using hr)
      rw [hu] at he
      exact ⟨0, (hval 0).trans he.symm⟩
    | tail _ ht ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, he, hr⟩ := ht
      by_cases hlast : i.val = k
      · have hf : i.succ = Fin.last (k + 1) := Fin.ext (by simp [hlast])
        rw [← hi, hf, hend] at hr
        exact False.elim (hfinal j hr)
      · let t : Fin (k + 1) := ⟨i.val + 1, by omega⟩
        have hp : t.castSucc = i.succ := Fin.ext rfl
        have hread : EffRead C (f t.castSucc) j := by rwa [hp, hi]
        have hu := (hlink t).2.2.2.1 j hread
        rw [hu] at he
        exact ⟨t, (hval t).trans he.symm⟩
  · rintro ⟨i, rfl⟩
    have hInd (j : ℕ) (hj : j < k + 1) :
        Relation.TransGen (Link C m) (f 0) (f (⟨j, hj⟩ : Fin (k + 1)).succ) := by
      induction j with
      | zero => exact Relation.TransGen.single (hstep ⟨0, hj⟩)
      | succ j ih =>
        exact Relation.TransGen.tail (ih (by omega)) (hstep ⟨j + 1, hj⟩)
    exact hInd i.val i.isLt

lemma other_not_reachable (C : Circuit) (m k : ℕ) (f : Fin (k + 1 + 1) → ℕ)
    (c : Fin (k + 1) → Fin C.gates.length) (hf : StrictMono f) (hc : StrictMono c)
    (hval : ∀ i : Fin (k + 1), f i.succ = m + (c i).val)
    (hlink : ∀ i : Fin (k + 1), EffOrLink C m (f i.castSucc) (c i))
    (hreach : ∀ w, Relation.TransGen (Link C m) (f 0) w ↔ ∃ i : Fin (k + 1), f i.succ = w)
    (i : Fin (k + 1)) (w : ℕ)
    (hread : EffRead C w (c i)) (hne : w ≠ f i.castSucc) (hlt : w < m + (c i).val) :
    ¬ Relation.TransGen (Link C m) (f 0) w := by
  intro hr
  obtain ⟨t, ht⟩ := (hreach w).mp hr
  have hlt' : f t.succ < f i.succ := by rwa [ht, hval]
  have hti : t.val < i.val := by
    have hs := hf.lt_iff_lt.mp hlt'
    change t.val + 1 < i.val + 1 at hs
    omega
  have hne' : t.val + 1 ≠ i.val := by
    intro he
    have hf' : t.succ = i.castSucc := Fin.ext he
    apply hne
    rw [← ht, hf']
  let u : Fin (k + 1) := ⟨t.val + 1, by omega⟩
  have hu : u.castSucc = t.succ := Fin.ext rfl
  have hru : EffRead C (f u.castSucc) (c i) := by rwa [hu, ht]
  have hic := (hlink u).2.2.2.1 (c i) hru
  have hiu := congrArg Fin.val (hc.injective hic)
  change i.val = t.val + 1 at hiu
  omega

lemma finish_chain (C : Circuit) (m v : ℕ) (hv : v < m) (hout : m ≤ C.output)
    (hfinal : C.output + 1 = m + C.gates.length)
    (htop : ∀ j : Fin C.gates.length, ∀ w, EffRead C w j → w < m + j.val)
    (hchain : HasEffChain C m v) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
      StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧
      C.output = m + (c (Fin.last k)).val ∧
      (∀ i : Fin (k + 1), (C.gates.get (c i)).op = GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧
      v ∈ (C.gates.get (c 0)).inputs ∧
      (∀ i : Fin k, m + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧
      (∀ j, EffRead C v j → j = c 0) ∧
      (∀ (i : Fin k) j, EffRead C (m + (c i.castSucc).val) j → j = c i.succ) ∧
      (∀ j : Fin C.gates.length, Relation.TransGen (Link C m) v (m + j.val) ↔
        ∃ i : Fin (k + 1), c i = j) ∧
      (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ v ∧ w < m + (c 0).val ∧
        ¬ Relation.TransGen (Link C m) v w) ∧
      (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs,
        w ≠ m + (c i.castSucc).val ∧ w ≠ v ∧ w < m + (c i.succ).val ∧
          ¬ Relation.TransGen (Link C m) v w) := by
  obtain ⟨l, f, hstart, hend, hs⟩ := hchain
  cases l with
  | zero =>
    have he : (0 : Fin (0 + 1)) = Fin.last 0 := Fin.ext rfl
    rw [← he, hstart] at hend
    omega
  | succ k =>
    let c (i : Fin (k + 1)) : Fin C.gates.length := Classical.choose (hs i)
    have hstep (i : Fin (k + 1)) :=
      Classical.choose_spec (hs i)
    have hval (i : Fin (k + 1)) : f i.succ = m + (c i).val := (hstep i).1
    have hlink (i : Fin (k + 1)) : EffOrLink C m (f i.castSucc) (c i) := (hstep i).2.1
    have hf : StrictMono f := Fin.strictMono_iff_lt_succ.mpr fun i => (hstep i).2.2
    have hc : StrictMono c := by
      intro i j hij
      have h := hf (show i.succ < j.succ by simpa using hij)
      rw [hval i, hval j] at h
      change (c i).val < (c j).val
      omega
    have hout' : C.output = m + (c (Fin.last k)).val := by
      rw [← hend]
      simpa [Fin.succ_last] using hval (Fin.last k)
    have hno (j : Fin C.gates.length) : ¬ EffRead C C.output j := by
      intro hj
      have hb := htop j C.output hj
      omega
    have hr := reach_chain C m k f c hval hlink hend hno
    have hstart' : f (0 : Fin (k + 1)).castSucc = v := hstart
    have hpred (i : Fin k) : f i.succ.castSucc = m + (c i.castSucc).val := by
      have he : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [he, hval]
    have hr0 : EffRead C v (c 0) := by
      have he := (hlink 0).2.2.1
      rwa [hstart'] at he
    have hunique0 (j : Fin C.gates.length) (hj : EffRead C v j) : j = c 0 :=
      (hlink 0).2.2.2.1 j (hstart'.symm ▸ hj)
    have hrstep (i : Fin k) : EffRead C (m + (c i.castSucc).val) (c i.succ) := by
      have he := (hlink i.succ).2.2.1
      rwa [hpred i] at he
    have hunique (i : Fin k) (j : Fin C.gates.length)
        (hj : EffRead C (m + (c i.castSucc).val) j) : j = c i.succ :=
      (hlink i.succ).2.2.2.1 j ((hpred i).symm ▸ hj)
    have other (i : Fin (k + 1)) :
        ∃ w ∈ (C.gates.get (c i)).inputs, w ≠ f i.castSucc ∧ w < m + (c i).val ∧
          ¬ Relation.TransGen (Link C m) v w := by
      obtain ⟨w, hw, hne, hlt⟩ := (hlink i).2.2.2.2
      refine ⟨w, hw, hne, hlt, ?_⟩
      rw [← hstart]
      exact other_not_reachable C m k f c hf hc hval hlink hr i w
        ((eff_or_read C w (c i) (hlink i).1).mpr hw) hne hlt
    refine ⟨k, c, hc, by omega, hout', fun i => ⟨(hlink i).1, (hlink i).2.1⟩, ?_, ?_,
      hunique0, hunique, ?_, ?_, ?_⟩
    · exact (eff_or_read C v (c 0) (hlink 0).1).mp hr0
    · intro i
      exact (eff_or_read C _ _ (hlink i.succ).1).mp (hrstep i)
    · intro j
      rw [← hstart, hr]
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨i, Fin.ext ?_⟩
        rw [hval i] at hi
        omega
      · rintro ⟨i, h⟩
        exact ⟨i, by rw [hval i, h]⟩
    · simpa only [hstart'] using other 0
    · intro i
      obtain ⟨w, hw, hne, hlt, hnr⟩ := other i.succ
      have hnv : w ≠ v := by
        intro he
        have hread := (eff_or_read C w (c i.succ) (hlink i.succ).1).mpr hw
        rw [he] at hread
        have hEq := congrArg Fin.val (hc.injective (hunique0 _ hread))
        change i.val + 1 = 0 at hEq
        omega
      exact ⟨w, hw, by simpa only [hpred i] using hne, hnv, hlt, hnr⟩

lemma solve (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hmin : IsMinimalCircuit (n + 1) C)
    (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hfn : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
      StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧
      C.output = n + 1 + (c (Fin.last k)).val ∧
      (∀ i : Fin (k + 1), (C.gates.get (c i)).op = GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧
      n ∈ (C.gates.get (c 0)).inputs ∧
      (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧
      (∀ j, EffRead C n j → j = c 0) ∧
      (∀ (i : Fin k) j, EffRead C (n + 1 + (c i.castSucc).val) j → j = c i.succ) ∧
      (∀ j : Fin C.gates.length, Relation.TransGen (Link C (n + 1)) n (n + 1 + j.val) ↔
        ∃ i : Fin (k + 1), c i = j) ∧
      (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧
        ¬ Relation.TransGen (Link C (n + 1)) n w) ∧
      (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs,
        w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧
          ¬ Relation.TransGen (Link C (n + 1)) n w) := by
  have hn (x : Fin (n + 1) → Bool) :
      circuitFun (n + 1) (normalized C) x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)) := by
    rw [normalized_fun]
    exact hfn x
  obtain ⟨hlast, hge, hchain, htop⟩ :=
    start_chain n (normalized C) H (normalized_legal C hmin.1) (normalized_min C _ hmin) hH hn
  have hlast' : C.output + 1 = n + 1 + C.gates.length := by
    rw [normalized_len] at hlast
    exact hlast
  exact finish_chain C (n + 1) n (by omega) hge hlast'
    (transfer_input_bound C _ htop) (transfer_chain C _ _ hchain)

end PEqualNP.Outside.L_meta_1547.Chain

namespace PEqualNP.Outside.L_meta_1547.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.Outside.L_meta_1547.Helpers.Readers

-- Edge functions given by lists: the OR of the inputs in A and of the edges in E.
def ev (A : List (Fin 10)) (E : List (Fin 10 × Fin 10)) (x : Fin 10 → Bool) : Bool :=
  A.any (fun a => x a) || E.any (fun e => x e.1 && x e.2)

theorem ev_iff (A : List (Fin 10)) (E : List (Fin 10 × Fin 10)) (x : Fin 10 → Bool) :
    ev A E x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ e ∈ E, x e.1 = true ∧ x e.2 = true := by
  simp only [ev, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]

def gr (E : List (Fin 10 × Fin 10)) : SimpleGraph (Fin 10) where
  Adj i j := i ≠ j ∧ ((i, j) ∈ E ∨ (j, i) ∈ E)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem F_gr (A : List (Fin 10)) (E : List (Fin 10 × Fin 10)) (hE : ∀ e ∈ E, e.1 ≠ e.2) :
    Forest.F (gr E) A.toFinset = ev A E := by
  funext x
  rw [Bool.eq_iff_iff, Forest.F_true, ev_iff]
  apply or_congr
  · simp
  · constructor
    · rintro ⟨i, j, ⟨_, h | h⟩, hi, hj⟩
      · exact ⟨_, h, hi, hj⟩
      · exact ⟨_, h, hj, hi⟩
    · rintro ⟨⟨i, j⟩, h, hi, hj⟩
      exact ⟨i, j, ⟨hE _ h, Or.inl h⟩, hi, hj⟩

theorem gr_ncard (E : List (Fin 10 × Fin 10)) (hE : ∀ e ∈ E, e.1 ≠ e.2)
    (hn : (E.map fun e => s(e.1, e.2)).Nodup) : (gr E).edgeSet.ncard = E.length := by
  have h : (gr E).edgeSet = ↑((E.map fun e => s(e.1, e.2)).toFinset) := by
    ext z
    induction z using Sym2.ind with
    | _ i j =>
      rw [SimpleGraph.mem_edgeSet]
      simp only [List.coe_toFinset, List.mem_map, Set.mem_setOf_eq, Sym2.eq_iff, gr]
      constructor
      · rintro ⟨_, h | h⟩
        · exact ⟨_, h, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨_, h, Or.inr ⟨rfl, rfl⟩⟩
      · rintro ⟨⟨a, b⟩, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨hE _ h, Or.inl h⟩
        · exact ⟨(hE _ h).symm, Or.inr h⟩
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup hn, List.length_map]

theorem acyc (G : SimpleGraph (Fin 10)) (r : Fin 10 → ℕ) (hr : ∀ a b, r a = r b → a = b)
    (h : ∀ v a b, G.Adj v a → G.Adj v b → r a < r v → r b < r v → a = b) : G.IsAcyclic := by
  intro v c hc
  obtain ⟨m, hm, hmax⟩ := c.support.toFinset.exists_max_image r
    ⟨v, by rw [List.mem_toFinset]; exact c.start_mem_support⟩
  rw [List.mem_toFinset] at hm
  have hc' := hc.rotate hm
  have hne := hc'.snd_ne_penultimate
  have hnil := hc'.not_nil
  have h1 := (c.rotate m hm).adj_snd hnil
  have h2 := (c.rotate m hm).adj_penultimate hnil
  have hsup : ∀ w, w ∈ (c.rotate m hm).support → r w ≤ r m := by
    intro w hw
    apply hmax
    rw [List.mem_toFinset]
    exact (c.mem_support_rotate_iff m hm).1 hw
  have key : ∀ w, G.Adj m w → w ∈ (c.rotate m hm).support → r w < r m := by
    intro w ha hw
    exact lt_of_le_of_ne (hsup w hw) (fun e => ha.ne (hr _ _ e).symm)
  apply hne
  exact h m _ _ h1 h2.symm (key _ h1 (SimpleGraph.Walk.getVert_mem_support _ _))
    (key _ h2.symm (SimpleGraph.Walk.getVert_mem_support _ _))

theorem matching_le (M : List (Fin 10 × Fin 10)) : ∀ T : Finset (Fin 10),
    (M.flatMap fun e => [e.1, e.2]).Nodup → (∀ e ∈ M, e.1 ∈ T ∨ e.2 ∈ T) → M.length ≤ T.card := by
  induction M with
  | nil => intro T _ _; simp
  | cons e M ih =>
    intro T hn hT
    obtain ⟨t, ht, hte⟩ : ∃ t ∈ T, t = e.1 ∨ t = e.2 := by
      rcases hT e (by simp) with h | h
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr rfl⟩
    rw [List.flatMap_cons, List.nodup_append] at hn
    obtain ⟨_, hn2, hdis⟩ := hn
    have hmem : t ∈ [e.1, e.2] := by simpa using hte
    have hout : ∀ d ∈ M, d.1 ≠ t ∧ d.2 ≠ t := by
      intro d hd
      constructor
      · intro e'
        exact hdis t hmem d.1 (List.mem_flatMap.2 ⟨d, hd, by simp⟩) e'.symm
      · intro e'
        exact hdis t hmem d.2 (List.mem_flatMap.2 ⟨d, hd, by simp⟩) e'.symm
    have h := ih (T.erase t) hn2 (by
      intro d hd
      rcases hT d (List.mem_cons_of_mem _ hd) with h | h
      · exact Or.inl (Finset.mem_erase.2 ⟨(hout d hd).1, h⟩)
      · exact Or.inr (Finset.mem_erase.2 ⟨(hout d hd).2, h⟩))
    have := Finset.card_erase_add_one ht
    simp only [List.length_cons]
    omega

def down (E : List (Fin 10 × Fin 10)) (r : Fin 10 → ℕ) (v a : Fin 10) : Bool :=
  (decide ((v, a) ∈ E) || decide ((a, v) ∈ E)) && decide (r a < r v)

def goodB (A : List (Fin 10)) (E M : List (Fin 10 × Fin 10)) (r : Fin 10 → ℕ) : Bool :=
  decide (∀ e ∈ E, e.1 ≠ e.2) && decide (E.map fun e => s(e.1, e.2)).Nodup &&
  decide (∀ a b, r a = r b → a = b) &&
  decide (∀ v a b : Fin 10, (down E r v a && down E r v b && decide (a ≠ b)) = false) &&
  decide A.Nodup && decide (∀ e ∈ E, e.1 ∉ A ∧ e.2 ∉ A) && decide (∀ e ∈ M, e ∈ E) &&
  decide (M.flatMap fun e => [e.1, e.2]).Nodup && decide (E ≠ [])

def Good (A : List (Fin 10)) (E M : List (Fin 10 × Fin 10)) (r : Fin 10 → ℕ) : Prop :=
  goodB A E M r = true

theorem forest_lb (A : List (Fin 10)) (E M : List (Fin 10 × Fin 10)) (r : Fin 10 → ℕ)
    (hg : Good A E M r) (s : ℕ) (h : HasCircuitSize 10 (ev A E) s) :
    A.length + E.length + M.length ≤ s + 1 := by
  simp only [Good, goodB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hg
  rw [← F_gr A E h1] at h
  have hac : (gr E).IsAcyclic :=
    acyc _ r h3 (fun v a b ha hb hra hrb => by
      by_contra hab
      have := h4 v a b
      have e1 : down E r v a = true := by simpa [down, hra] using ha.2
      have e2 : down E r v b = true := by simpa [down, hrb] using hb.2
      rw [e1, e2] at this
      simp [hab] at this)
  have hA : ∀ i j, (gr E).Adj i j → i ∉ A.toFinset := by
    rintro i j ⟨_, hh | hh⟩ hi
    · exact (h6 _ hh).1 (List.mem_toFinset.1 hi)
    · exact (h6 _ hh).2 (List.mem_toFinset.1 hi)
  have hk : ∀ T, Forest.Cov (gr E) T → M.length ≤ T.card := by
    intro T hT
    apply matching_le M T h8
    intro e he
    exact hT e.1 e.2 ⟨h1 e (h7 e he), Or.inl (h7 e he)⟩
  have hne : ∃ i j, (gr E).Adj i j := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil E h9
    exact ⟨e.1, e.2, h1 e he, Or.inl he⟩
  have := Forest.claimQ _ 10 (gr E) A.toFinset M.length s (gr_ncard E h1 h2) hac hA hk
    (Or.inr hne) h
  rw [List.toFinset_card_of_nodup h5] at this
  exact this

theorem ev_false (A : List (Fin 10)) (E : List (Fin 10 × Fin 10)) (y : Fin 10) :
    (fun x => ev A E (Function.update x y false)) =
      ev (A.filter (fun a => a ≠ y)) (E.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y)) := by
  funext x
  rw [Bool.eq_iff_iff, ev_iff, ev_iff]
  have hu : ∀ i, Function.update x y false i = true ↔ i ≠ y ∧ x i = true := by
    intro i
    by_cases hi : i = y
    · subst hi; simp
    · simp [Function.update_of_ne hi, hi]
  simp only [hu, List.mem_filter, decide_eq_true_eq]
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h1, h2⟩; exact ⟨a, ⟨ha, h1⟩, h2⟩
    · rintro ⟨a, ⟨ha, h1⟩, h2⟩; exact ⟨a, ha, h1, h2⟩
  · constructor
    · rintro ⟨e, he, ⟨h1, h2⟩, h3, h4⟩; exact ⟨e, ⟨he, h1, h3⟩, h2, h4⟩
    · rintro ⟨e, ⟨he, h1, h3⟩, h2, h4⟩; exact ⟨e, he, ⟨h1, h2⟩, h3, h4⟩

-- The neighbours of y in the list E.
def nb (E : List (Fin 10 × Fin 10)) (y : Fin 10) : List (Fin 10) :=
  ((E.filter (fun e => e.1 = y)).map fun e => e.2) ++
    ((E.filter (fun e => e.2 = y)).map fun e => e.1)

theorem mem_nb (E : List (Fin 10 × Fin 10)) (y a : Fin 10) :
    a ∈ nb E y ↔ (y, a) ∈ E ∨ (a, y) ∈ E := by
  simp only [nb, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨⟨b, c⟩, ⟨h, rfl⟩, rfl⟩ | ⟨⟨b, c⟩, ⟨h, rfl⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨_, ⟨h, rfl⟩, rfl⟩
    · exact Or.inr ⟨_, ⟨h, rfl⟩, rfl⟩

theorem ev_true (E : List (Fin 10 × Fin 10)) (y : Fin 10) (hy : (y, y) ∉ E) :
    (fun x => ev [] E (Function.update x y true)) =
      ev (nb E y) (E.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y ∧ e.1 ∉ nb E y ∧ e.2 ∉ nb E y)) := by
  funext x
  rw [Bool.eq_iff_iff, ev_iff, ev_iff]
  have hu : ∀ i, Function.update x y true i = true ↔ i = y ∨ x i = true := by
    intro i
    by_cases hi : i = y
    · subst hi; simp
    · simp [Function.update_of_ne hi, hi]
  simp only [hu, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨a, ha, _⟩ | ⟨⟨a, b⟩, he, h1, h2⟩)
    · simp at ha
    · by_cases hN : ∃ c ∈ nb E y, x c = true
      · exact Or.inl hN
      · right
        have hN' : ∀ c, c ∈ nb E y → x c ≠ true := fun c hc hx => hN ⟨c, hc, hx⟩
        have ha : a ≠ y := by
          rintro rfl
          rcases h2 with h2 | h2
          · simp only at h2; subst h2; exact hy he
          · exact hN' b ((mem_nb E _ b).2 (Or.inl he)) h2
        have hb : b ≠ y := by
          rintro rfl
          rcases h1 with h1 | h1
          · exact ha h1
          · exact hN' a ((mem_nb E _ a).2 (Or.inr he)) h1
        have h1' : x a = true := h1.resolve_left ha
        have h2' : x b = true := h2.resolve_left hb
        exact ⟨(a, b), ⟨he, ha, hb, fun h => hN' a h h1', fun h => hN' b h h2'⟩, h1', h2'⟩
  · rintro (⟨a, ha, hx⟩ | ⟨e, ⟨he, _⟩, h1, h2⟩)
    · right
      rcases (mem_nb E y a).1 ha with h | h
      · exact ⟨_, h, Or.inl rfl, Or.inr hx⟩
      · exact ⟨_, h, Or.inr hx, Or.inl rfl⟩
    · exact Or.inr ⟨e, he, Or.inr h1, Or.inr h2⟩

-- The 7-cycle 0..6.
def cyc7 : List (Fin 10 × Fin 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0)]

def ind (r : Fin 10) : Fin 10 → Bool := fun i => decide (i = r)

theorem cyc7_dep (p : Fin 10) (h : Dep (ev [] cyc7) p) : p.val < 7 := by
  by_contra hp
  obtain ⟨x, hx⟩ := h
  apply hx
  rw [Bool.eq_iff_iff, ev_iff, ev_iff]
  have hu : ∀ i : Fin 10, i.val < 7 → Function.update x p (!x p) i = x i := by
    intro i hi
    exact Function.update_of_ne (fun e => hp (by rw [← e]; exact hi)) _ _
  have hE : ∀ e ∈ cyc7, e.1.val < 7 ∧ e.2.val < 7 := by decide
  apply or_congr
  · simp
  · constructor
    · rintro ⟨e, he, h1, h2⟩
      rw [hu _ (hE e he).1] at h1
      rw [hu _ (hE e he).2] at h2
      exact ⟨e, he, h1, h2⟩
    · rintro ⟨e, he, h1, h2⟩
      refine ⟨e, he, ?_, ?_⟩
      · rw [hu _ (hE e he).1]; exact h1
      · rw [hu _ (hE e he).2]; exact h2

theorem cyc7_sep : ∀ p q : Fin 10, p.val < 7 → q.val < 7 → p ≠ q →
    (∃ r, ev [] cyc7 (set2 (ind r) p true q false) ≠ ev [] cyc7 (set2 (ind r) p false q false)) ∧
    (∃ r, ev [] cyc7 (set2 (ind r) p false q true) ≠ ev [] cyc7 (set2 (ind r) p false q false)) ∧
    (∃ r, ev [] cyc7 (set2 (ind r) p true q false) ≠
      ev [] cyc7 (set2 (ind r) p false q true)) := by
  decide +kernel

theorem cyc7_nc : ∀ (p : Fin 10) (b : Bool),
    ev [] cyc7 (Function.update (fun _ => true) p b) ≠
      ev [] cyc7 (Function.update (fun _ => false) p b) := by
  decide +kernel

def rot (y v : Fin 10) : ℕ := if v.val < 7 then (v.val + 13 - y.val) % 7 else v.val

theorem cyc7_false : ∀ y : Fin 10, y.val < 7 →
    Good ([].filter (fun a => a ≠ y)) (cyc7.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y))
      ((cyc7.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y)).filter (fun e => rot y e.1 % 2 = 0)) (rot y) ∧
    (cyc7.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y)).length = 5 ∧
    ((cyc7.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y)).filter (fun e => rot y e.1 % 2 = 0)).length = 3 := by
  unfold Good
  decide +kernel

theorem cyc7_true : ∀ y : Fin 10, y.val < 7 → (y, y) ∉ cyc7 ∧ (nb cyc7 y).length = 2 ∧
    Good (nb cyc7 y)
      (cyc7.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y ∧ e.1 ∉ nb cyc7 y ∧ e.2 ∉ nb cyc7 y))
      ((cyc7.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y ∧ e.1 ∉ nb cyc7 y ∧ e.2 ∉ nb cyc7 y)).filter
        (fun e => rot y e.1 % 2 = 1)) (rot y) ∧
    (cyc7.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y ∧ e.1 ∉ nb cyc7 y ∧ e.2 ∉ nb cyc7 y)).length = 3 ∧
    ((cyc7.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y ∧ e.1 ∉ nb cyc7 y ∧ e.2 ∉ nb cyc7 y)).filter
        (fun e => rot y e.1 % 2 = 1)).length = 2 := by
  unfold Good
  decide +kernel

theorem cyc7_lb (s : ℕ) (h : HasCircuitSize 10 (ev [] cyc7) s) : 10 ≤ s := by
  have hdep : ∃ p, Dep (ev [] cyc7) p := by
    refine ⟨0, ind 1, ?_⟩
    decide +kernel
  have hnc : RestrNC (ev [] cyc7) := fun p _ b => ⟨_, _, cyc7_nc p b⟩
  have hnf : NoFunnel (ev [] cyc7) := by
    apply noFunnel_of_sep
    intro p q hpq hp hq
    obtain ⟨⟨r1, h1⟩, ⟨r2, h2⟩, ⟨r3, h3⟩⟩ := cyc7_sep p q (cyc7_dep p hp) (cyc7_dep q hq) hpq
    exact ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩
  obtain ⟨y, hy, hpay⟩ := fanout_step 9 (ev [] cyc7) s hdep hnc hnf h
  have hy7 := cyc7_dep y hy
  have hcase : Drop (ev [] cyc7) y false 3 s ∨ Drop (ev [] cyc7) y true 4 s := by
    rcases hpay with ⟨a, _⟩ | ⟨a, _⟩ | ⟨_, a⟩
    · exact Or.inl a
    · exact Or.inl (a.mono (by omega) le_rfl)
    · exact Or.inr a
  rcases hcase with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
  · rw [ev_false] at hc
    obtain ⟨hg, h1, h2⟩ := cyc7_false y hy7
    have := forest_lb _ _ _ _ hg t hc
    rw [h1, h2] at this
    simp at this
    omega
  · obtain ⟨h0, h1, hg, h2, h3⟩ := cyc7_true y hy7
    rw [ev_true cyc7 y h0] at hc
    have := forest_lb _ _ _ _ hg t hc
    rw [h1, h2, h3] at this
    omega

end PEqualNP.Outside.L_meta_1547.Main

namespace PEqualNP.Outside.L_meta_1547.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.Outside.L_meta_1547.Helpers.Readers

theorem eff_of_mem {m : ℕ} {g : Gate} (hg : CleanGate m g) {a : ℕ} (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs.head? = some a) ∨ (g.op ≠ GateOp.not ∧ a ∈ g.inputs) := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop, _⟩
  · left
    rw [hin] at ha ⊢
    simp at ha
    subst ha
    exact ⟨hop, rfl⟩
  · right
    refine ⟨?_, ha⟩
    rcases hop with h | h <;> rw [h] <;> simp

-- The chain of OR gates of a free OR input, at any input position.
theorem chain_at {n : ℕ} (gs : List Gate) (o : ℕ) (v : Fin (n + 1)) (hcl : CleanL (n + 1) gs)
    (hmin : ∀ s, HasCircuitSize (n + 1) (fun x => vl gs x o) s → gs.length ≤ s)
    (hv : ∀ x : Fin (n + 1) → Bool, x v = true → vl gs x o = true)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      vl gs (Function.update x v false) o ≠ vl gs (Function.update y v false) o) :
    ∃ (k : ℕ) (z : ℕ → ℕ), z 0 = v ∧
      (∀ r, r ≤ k → n + 1 ≤ z (r + 1) ∧ z (r + 1) < n + 1 + gs.length) ∧
      (∀ r, r ≤ k → z r < z (r + 1)) ∧ z (k + 1) = o ∧ o + 1 = n + 1 + gs.length ∧
      (∀ r, r ≤ k → ∃ g, gs[z (r + 1) - (n + 1)]? = some g ∧ g.op = GateOp.or ∧ z r ∈ g.inputs) ∧
      (∀ r, r ≤ k → ∀ j, Reads gs j (z r) → n + 1 + j = z (r + 1)) := by
  set π : Equiv.Perm (Fin (n + 1)) := Equiv.swap v (Fin.last n) with hπ
  set C : Circuit := PermInputs.relabel (n + 1) (n + 1) (⇑π) ⟨gs, o⟩ with hC
  have hππ : ∀ x : Fin (n + 1) → Bool, (x ∘ π) ∘ π = x := by
    intro x; funext j; simp [hπ, Equiv.swap_apply_self]
  have hCf : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x = vl gs (x ∘ π) o := by
    intro x
    exact (PermInputs.rel_fold (n + 1) (n + 1) π gs _ _
      (PermInputs.rel_init (n + 1) (n + 1) π x)).2.2 o
  have hlen : C.gates.length = gs.length := by simp [hC, PermInputs.relabel]
  have hfan : FanInTwo C := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := (clean_nok _ gs hcl g0 hg0).1
    exact ⟨this.1, by simpa [PermInputs.relGate] using this.2⟩
  have hCmin : IsMinimalCircuit (n + 1) C := by
    refine ⟨hfan, ?_⟩
    intro D hD he
    have h1 : HasCircuitSize (n + 1) (circuitFun (n + 1) C) D.size :=
      ⟨D, hD, le_rfl, fun x => congrFun he x⟩
    have h2 := PermInputs.relabel_size (⇑π) _ _ h1
    have e : (fun x : Fin (n + 1) → Bool => circuitFun (n + 1) C (x ∘ π)) =
        fun x => vl gs x o := by
      funext x
      rw [hCf, hππ]
    rw [e] at h2
    have := hmin _ h2
    show C.gates.length ≤ D.size
    omega
  have hlast : ∀ x : Fin (n + 1) → Bool, (x ∘ π) v = x (Fin.last n) := by
    intro x; simp [hπ]
  let H : (Fin n → Bool) → Bool := fun y => vl gs ((Fin.snoc y false : Fin (n + 1) → Bool) ∘ π) o
  have hfn : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C x =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)) := by
    intro x
    rw [hCf]
    cases hx : x (Fin.last n) with
    | true =>
      rw [hv _ ((hlast x).trans hx)]; rfl
    | false =>
      have e : (Fin.snoc (fun i : Fin n => x i.castSucc) false : Fin (n + 1) → Bool) = x := by
        rw [← hx]
        exact Fin.snoc_init_self x
      simp only [H, e, Bool.false_or]
  have hH : ∃ y y' : Fin n → Bool, H y ≠ H y' := by
    obtain ⟨x, y, hxy⟩ := hnc
    have key : ∀ x : Fin (n + 1) → Bool, vl gs (Function.update x v false) o =
        H (fun i : Fin n => (x ∘ π) i.castSucc) := by
      intro x
      have e : ((Fin.snoc (fun i : Fin n => (x ∘ π) i.castSucc) false : Fin (n + 1) → Bool) ∘ π) =
          Function.update x v false := by
        funext j
        by_cases hj : j = v
        · subst hj
          rw [Function.update_self, Function.comp_apply, hπ, Equiv.swap_apply_left, Fin.snoc_last]
        · rw [Function.update_of_ne hj, Function.comp_apply]
          have hne : π j ≠ Fin.last n := by
            intro h
            apply hj
            have := congrArg π h
            rw [hπ, Equiv.swap_apply_self, Equiv.swap_apply_right] at this
            exact this
          obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hne
          rw [← hi, Fin.snoc_castSucc, hi, Function.comp_apply, hπ, Equiv.swap_apply_self]
      simp only [H, e]
    exact ⟨_, _, fun e => hxy ((key x).trans (e.trans (key y).symm))⟩
  obtain ⟨k, c, hmono, hclast, hout, hor, hc0, hcs, hu0, hus, _⟩ :=
    Chain.solve n C H hCmin hH hfn
  have wm_gate : ∀ i, n + 1 ≤ i → PermInputs.wmap (n + 1) (n + 1) π i = i := by
    intro i hi
    unfold PermInputs.wmap
    rw [dif_neg (by omega)]
    omega
  have wm_lt : ∀ i, i < n + 1 → PermInputs.wmap (n + 1) (n + 1) π i < n + 1 := by
    intro i hi
    unfold PermInputs.wmap
    rw [dif_pos hi]
    exact (π ⟨i, hi⟩).isLt
  have wm_v : PermInputs.wmap (n + 1) (n + 1) π v = n := by
    unfold PermInputs.wmap
    rw [dif_pos v.isLt]
    simp [hπ]
  have wm_n : ∀ i, PermInputs.wmap (n + 1) (n + 1) π i = n → i = v := by
    intro i hi
    by_cases hlt : i < n + 1
    · unfold PermInputs.wmap at hi
      rw [dif_pos hlt] at hi
      have h1 : π ⟨i, hlt⟩ = Fin.last n := Fin.ext hi
      have := congrArg π h1
      rw [hπ, Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      rw [← this]
    · rw [wm_gate i (by omega)] at hi
      omega
  have wm_eq : ∀ i j, n + 1 ≤ j → PermInputs.wmap (n + 1) (n + 1) π i = j → i = j := by
    intro i j hj hi
    by_cases hlt : i < n + 1
    · have := wm_lt i hlt; omega
    · rw [wm_gate i (by omega)] at hi; exact hi
  have hget : ∀ (j : ℕ) (hj : j < gs.length) (hj' : j < C.gates.length),
      C.gates.get ⟨j, hj'⟩ = PermInputs.relGate (n + 1) (n + 1) π gs[j] := by
    intro j hj hj'
    simp [hC, PermInputs.relabel]
  let z : ℕ → ℕ := fun r => if r = 0 then (v : ℕ) else
    if h : r - 1 < k + 1 then n + 1 + (c ⟨r - 1, h⟩).val else 0
  have hz0 : z 0 = v := by simp [z]
  have hzs : ∀ r (h : r < k + 1), z (r + 1) = n + 1 + (c ⟨r, h⟩).val := by
    intro r h
    show (if r + 1 = 0 then (v : ℕ) else
      if h : r + 1 - 1 < k + 1 then n + 1 + (c ⟨r + 1 - 1, h⟩).val else 0) = _
    rw [if_neg (Nat.succ_ne_zero r)]
    exact dif_pos h
  have hclt : ∀ i, (c i).val < gs.length := fun i => by
    have := (c i).isLt
    omega
  have hmem : ∀ r (h : r < k + 1), z r ∈ (gs[(c ⟨r, h⟩).val]'(hclt _)).inputs := by
    intro r h
    cases r with
    | zero =>
      have h1 := hc0
      rw [show (0 : Fin (k + 1)) = ⟨0, h⟩ from rfl] at h1
      rw [show c ⟨0, h⟩ = ⟨(c ⟨0, h⟩).val, (c ⟨0, h⟩).isLt⟩ from rfl,
        hget _ (hclt _) (c ⟨0, h⟩).isLt] at h1
      obtain ⟨i, hi, hin⟩ := List.mem_map.1 h1
      rw [hz0, ← wm_n i hin]
      exact hi
    | succ r =>
      have h1 := hcs ⟨r, by omega⟩
      rw [show c (Fin.succ ⟨r, by omega⟩) = ⟨(c ⟨r + 1, h⟩).val, (c ⟨r + 1, h⟩).isLt⟩ from rfl,
        hget _ (hclt _) (c ⟨r + 1, h⟩).isLt] at h1
      obtain ⟨i, hi, hin⟩ := List.mem_map.1 h1
      have e := wm_eq i _ (by omega) hin
      rw [hzs r (by omega)]
      rw [e] at hi
      exact hi
  have heff : ∀ j w, Reads gs j w → ∃ hj : j < C.gates.length,
      (((C.gates.get ⟨j, hj⟩).op = GateOp.not ∧ (C.gates.get ⟨j, hj⟩).inputs.head? =
          some (PermInputs.wmap (n + 1) (n + 1) π w)) ∨
        ((C.gates.get ⟨j, hj⟩).op ≠ GateOp.not ∧
          PermInputs.wmap (n + 1) (n + 1) π w ∈ (C.gates.get ⟨j, hj⟩).inputs)) := by
    rintro j w ⟨g, hg, hw⟩
    obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.1 hg
    refine ⟨by omega, ?_⟩
    rw [hget j hj, hgj]
    rcases eff_of_mem (hcl j g hg) hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨h1, ?_⟩
      simp [PermInputs.relGate, h2]
    · right
      exact ⟨h1, List.mem_map.2 ⟨w, h2, rfl⟩⟩
  refine ⟨k, z, hz0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [hzs r (by omega)]
    have := hclt ⟨r, by omega⟩
    omega
  · intro r hr
    rw [hzs r (by omega)]
    cases r with
    | zero => rw [hz0]; have := v.isLt; omega
    | succ r =>
      rw [hzs r (by omega)]
      have : c ⟨r, by omega⟩ < c ⟨r + 1, by omega⟩ := hmono (by simp [Fin.lt_def])
      have := Fin.lt_def.1 this
      omega
  · rw [hzs k (by omega)]
    have h1 : PermInputs.wmap (n + 1) (n + 1) π o = n + 1 + (c (Fin.last k)).val := hout
    exact (wm_eq o _ (by omega) h1).symm
  · have h1 : PermInputs.wmap (n + 1) (n + 1) π o = n + 1 + (c (Fin.last k)).val := hout
    have := wm_eq o _ (by omega) h1
    omega
  · intro r hr
    have hr' : r < k + 1 := by omega
    refine ⟨gs[(c ⟨r, hr'⟩).val]'(hclt _), ?_, ?_, hmem r hr'⟩
    · rw [hzs r hr', Nat.add_sub_cancel_left]
      exact List.getElem?_eq_getElem _
    · have := (hor ⟨r, hr'⟩).1
      rw [show c ⟨r, hr'⟩ = ⟨(c ⟨r, hr'⟩).val, (c ⟨r, hr'⟩).isLt⟩ from rfl,
        hget _ (hclt _) (c ⟨r, hr'⟩).isLt] at this
      exact this
  · intro r hr j hj
    have hr' : r < k + 1 := by omega
    obtain ⟨hjl, he⟩ := heff j _ hj
    rw [hzs r hr']
    cases r with
    | zero =>
      rw [hz0, wm_v] at he
      have := hu0 ⟨j, hjl⟩ he
      have := congrArg Fin.val this
      simp only at this
      rw [this]
      rfl
    | succ r =>
      rw [hzs r (by omega), wm_gate _ (by omega)] at he
      have := hus ⟨r, by omega⟩ ⟨j, hjl⟩ he
      have := congrArg Fin.val this
      simp only at this
      rw [this]
      rfl

end PEqualNP.Outside.L_meta_1547.Main

namespace PEqualNP.Outside.L_meta_1547.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.Outside.L_meta_1547.Helpers.Readers

-- Wire renaming when gate a (constant true once the leaf l is true) and gate b
-- (then equal to wire w) are taken out of a circuit with ten inputs.
def tau0 (a w : ℕ) : ℕ := if w < 10 + a then w else w - 1

def tau (a b w l i : ℕ) : ℕ :=
  if i < 10 + a then i else if i = 10 + a then l else
    if i < 10 + b then i - 1 else if i = 10 + b then tau0 a w else i - 2

def dg (a b j : ℕ) : ℕ := if j < a then j else if j < b then j - 1 else j - 2

def mg (a b w l : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (tau a b w l)⟩

def dele (gs : List Gate) (a b w l : ℕ) : List Gate :=
  ((gs.eraseIdx b).eraseIdx a).map (mg a b w l)

theorem dele_len (gs : List Gate) (a b w l : ℕ) (hab : a < b) (hb : b < gs.length) :
    (dele gs a b w l).length + 2 = gs.length := by
  have h1 : (gs.eraseIdx b).length = gs.length - 1 := List.length_eraseIdx_of_lt hb
  have h2 : ((gs.eraseIdx b).eraseIdx a).length = (gs.eraseIdx b).length - 1 :=
    List.length_eraseIdx_of_lt (by omega)
  simp only [dele, List.length_map]
  omega

theorem dele_get (gs : List Gate) (a b w l : ℕ) (hab : a < b) (j : ℕ) (hja : j ≠ a) (hjb : j ≠ b)
    (g : Gate) (hg : gs[j]? = some g) : (dele gs a b w l)[dg a b j]? = some (mg a b w l g) := by
  rw [dele, List.getElem?_map, List.getElem?_eraseIdx, List.getElem?_eraseIdx]
  unfold dg
  rcases Nat.lt_trichotomy j a with h | h | h
  · rw [if_pos h, if_pos h, if_pos (by omega), hg]; rfl
  · exact absurd h hja
  · rcases Nat.lt_trichotomy j b with h' | h' | h'
    · rw [if_neg (show ¬ j < a by omega), if_pos h', if_neg (show ¬ j - 1 < a by omega),
        List.getElem?_eraseIdx, if_pos (show j - 1 + 1 < b by omega), show j - 1 + 1 = j by omega, hg]; rfl
    · exact absurd h' hjb
    · rw [if_neg (show ¬ j < a by omega), if_neg (show ¬ j < b by omega),
        if_neg (show ¬ j - 2 < a by omega), List.getElem?_eraseIdx, if_neg (show ¬ j - 2 + 1 < b by omega),
        show j - 2 + 1 + 1 = j by omega, hg]; rfl

theorem dele_inv (gs : List Gate) (a b w l : ℕ) (hab : a < b) (j' : ℕ) (g' : Gate)
    (h : (dele gs a b w l)[j']? = some g') :
    ∃ j g, j ≠ a ∧ j ≠ b ∧ gs[j]? = some g ∧ dg a b j = j' ∧ g' = mg a b w l g := by
  have hlen : j' < (dele gs a b w l).length := (List.getElem?_eq_some_iff.1 h).1
  have hex : ∃ j, j ≠ a ∧ j ≠ b ∧ dg a b j = j' ∧ j < gs.length := by
    have hl : (dele gs a b w l).length = ((gs.eraseIdx b).eraseIdx a).length := by
      simp [dele]
    rw [hl, List.length_eraseIdx, List.length_eraseIdx] at hlen
    unfold dg
    by_cases h1 : j' < a
    · refine ⟨j', by omega, by omega, if_pos h1, ?_⟩
      split_ifs at hlen <;> omega
    · by_cases h2 : j' + 1 < b
      · refine ⟨j' + 1, by omega, by omega, ?_, ?_⟩
        · rw [if_neg (by omega), if_pos h2]; omega
        · split_ifs at hlen <;> omega
      · by_cases h3 : b < gs.length
        · refine ⟨j' + 2, by omega, by omega, ?_, ?_⟩
          · rw [if_neg (by omega), if_neg (by omega)]; omega
          · split_ifs at hlen <;> omega
        · exfalso
          rw [if_neg h3] at hlen
          split_ifs at hlen <;> omega
  obtain ⟨j, hja, hjb, hj, hjl⟩ := hex
  refine ⟨j, gs[j], hja, hjb, List.getElem?_eq_getElem hjl, hj, ?_⟩
  have := dele_get gs a b w l hab j hja hjb gs[j] (List.getElem?_eq_getElem hjl)
  rw [hj, h] at this
  exact Option.some.inj this

theorem tau_low (a b w l i : ℕ) (h : i < 10) : tau a b w l i = i := by
  unfold tau
  rw [if_pos (by omega)]

theorem tau_a (a b w l : ℕ) : tau a b w l (10 + a) = l := by
  unfold tau
  rw [if_neg (by omega), if_pos rfl]

theorem tau_b (a b w l : ℕ) (hab : a < b) (hw : w < 10 + b) (hwa : w ≠ 10 + a) :
    tau a b w l (10 + b) = tau a b w l w := by
  unfold tau tau0
  split_ifs <;> omega

theorem tau_gate (a b w l j : ℕ) (hab : a < b) (hja : j ≠ a) (hjb : j ≠ b) :
    tau a b w l (10 + j) = 10 + dg a b j := by
  unfold tau dg
  split_ifs <;> omega

theorem tau_inj (a b w l i j : ℕ) (hab : a < b) (hia : i ≠ 10 + a) (hib : i ≠ 10 + b)
    (hja : j ≠ 10 + a) (hjb : j ≠ 10 + b) (h : tau a b w l i = tau a b w l j) : i = j := by
  unfold tau at h
  split_ifs at h <;> omega

theorem tau_bound (a b w l i j : ℕ) (hab : a < b) (hl : l < 10) (hw : w < 10 + b)
    (hwa : w ≠ 10 + a) (hja : j ≠ a) (hjb : j ≠ b) (hi : i < 10 + j) :
    tau a b w l i < 10 + dg a b j := by
  unfold tau tau0 dg
  split_ifs <;> omega

theorem dele_clean (gs : List Gate) (hcl : CleanL 10 gs) (a b w l : ℕ) (hab : a < b)
    (hl : l < 10) (hw : w < 10 + b) (hwa : w ≠ 10 + a) : CleanL 10 (dele gs a b w l) := by
  intro j' g' hg'
  obtain ⟨j, g, hja, hjb, hg, rfl, rfl⟩ := dele_inv gs a b w l hab j' g' hg'
  have hb : ∀ i, i < 10 + j → tau a b w l i < 10 + dg a b j := fun i hi =>
    tau_bound a b w l i j hab hl hw hwa hja hjb hi
  rcases hcl j g hg with ⟨hop, i, hi, hin⟩ | ⟨hop, i, i', hi, hi', hin⟩
  · exact Or.inl ⟨hop, _, hb i hi, by simp [mg, hin]⟩
  · exact Or.inr ⟨hop, _, _, hb i hi, hb i' hi', by simp [mg, hin]⟩

theorem dele_val (gs : List Gate) (hcl : CleanL 10 gs) (a b w : ℕ) (l : Fin 10) (hab : a < b)
    (hbl : b < gs.length) (hw : w < 10 + b) (hwa : w ≠ 10 + a) (x : Fin 10 → Bool)
    (ha : vl gs x (10 + a) = vl gs x l) (hb : vl gs x (10 + b) = vl gs x w) :
    ∀ i, vl (dele gs a b w l) x (tau a b w l i) = vl gs x i := by
  have hcl' := dele_clean gs hcl a b w l hab l.isLt hw hwa
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < 10
    · rw [tau_low a b w l i hi, vl_input _ _ _ hi, vl_input _ _ _ hi]
    · obtain ⟨j, rfl⟩ : ∃ j, i = 10 + j := ⟨i - 10, by omega⟩
      by_cases hja : j = a
      · subst hja
        rw [tau_a, ha, vl_input _ _ _ l.isLt, vl_input _ _ _ l.isLt]
      · by_cases hjb : j = b
        · subst hjb
          rw [tau_b a j w l hab hw hwa, hb]
          exact ih w hw
        · rw [tau_gate a b w l j hab hja hjb]
          cases hg : gs[j]? with
          | none =>
            have hl : gs.length ≤ j := List.getElem?_eq_none_iff.1 hg
            have hlen := dele_len gs a b w l hab hbl
            rw [vl_beyond gs x _ (by omega), vl_beyond _ x _ (by
              unfold dg
              split_ifs <;> omega)]
          | some g =>
            rw [vl_gate gs hcl x j g hg,
              vl_gate _ hcl' x _ _ (dele_get gs a b w l hab j hja hjb g hg)]
            show g.op.eval ((g.inputs.map (tau a b w l)).map _) = _
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro e he
            exact ih e ((hcl j g hg).lt e he)

end PEqualNP.Outside.L_meta_1547.Main

namespace PEqualNP.Outside.L_meta_1547.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.Outside.L_meta_1547.Helpers.Readers

theorem some_eq {gs : List Gate} {j : ℕ} {g g' : Gate} (h : gs[j]? = some g)
    (h' : gs[j]? = some g') : g = g' := by
  rw [h] at h'
  exact Option.some.inj h'

-- The shape of the circuit near a leaf l: one OR gate a reads l, one AND gate b reads gate a.
theorem shape (f : (Fin 10 → Bool) → Bool) (l : Fin 10) (gs : List Gate) (o : ℕ)
    (L : Least 10 f gs o) (hN : gs.length ≤ 13)
    (hB0 : ∀ s, HasCircuitSize 10 (fun x => f (Function.update x l false)) s → 12 ≤ s)
    (hB1 : ∀ s, HasCircuitSize 10 (fun x => f (Function.update x l true)) s → 11 ≤ s)
    (hnc : ∀ b : Bool, ∃ x y : Fin 10 → Bool,
      f (Function.update x l b) ≠ f (Function.update y l b))
    (hdep : Dep f l) :
    ∃ (a b u w : ℕ) (ga gb : Gate), a < b ∧ b < gs.length ∧ gs[a]? = some ga ∧
      ga.op = GateOp.or ∧ (ga.inputs = [(l : ℕ), u] ∨ ga.inputs = [u, (l : ℕ)]) ∧
      gs[b]? = some gb ∧ gb.op = GateOp.and ∧ (gb.inputs = [10 + a, w] ∨ gb.inputs = [w, 10 + a]) ∧
      (∀ x : Fin 10 → Bool, vl gs x (10 + a) = (vl gs x l || vl gs x u)) ∧
      (∀ x : Fin 10 → Bool, vl gs x (10 + b) = (vl gs x (10 + a) && vl gs x w)) ∧
      (∀ q, Reads gs q l → q = a) ∧ (∀ q, Reads gs q (10 + a) → q = b) ∧
      u < 10 + a ∧ w < 10 + b ∧ w ≠ 10 + a := by
  have hfnc : ∃ x y : Fin 10 → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc false
    exact ⟨_, _, h⟩
  obtain ⟨a, ha⟩ := L.dep_read l hdep hnc
  have hua : ∀ q, Reads gs q l → q = a := by
    intro q hq
    by_contra hne
    obtain ⟨t, ht, hc⟩ := Least.save2 (n := 9) L l false (hnc false) a q (Ne.symm hne)
      (rc_input false ha) (rc_input false hq)
    have := hB0 t hc
    omega
  obtain ⟨ga, hga, hla⟩ := ha
  have hal : a < gs.length := (List.getElem?_eq_some_iff.1 hga).1
  have hra : Reads gs a l := ⟨ga, hga, hla⟩
  have hnC : ¬ IsC 9 gs l false (9 + 1 + a) := by
    intro hc
    obtain ⟨q, hq, hr, hrc⟩ := Least.next (n := 9) L l false (hnc false) a hal hc
    obtain ⟨t, ht, hc⟩ := Least.save2 (n := 9) L l false (hnc false) a q (by omega)
      (rc_input false hra) hrc
    have := hB0 t hc
    omega
  obtain ⟨u, hin, hopa, hva⟩ : ∃ u, (ga.inputs = [(l : ℕ), u] ∨ ga.inputs = [u, (l : ℕ)]) ∧
      ga.op = GateOp.or ∧ ∀ x : Fin 10 → Bool, vl gs x (10 + a) = (vl gs x l || vl gs x u) := by
    rcases gate_cases gs L.hcl a ga hga l hla with ⟨hop, _⟩ | ⟨u, hin, ⟨hop, _⟩ | ⟨hop, hv⟩⟩
    · exact absurd (isC_reader (n := 9) L.hcl l a ga hga hla false (Or.inl hop)) hnC
    · exact absurd (isC_reader (n := 9) L.hcl l a ga hga hla false
        (Or.inr (by simp [fixBit, hop]))) hnC
    · exact ⟨u, hin, hop, hv⟩
  have hCa : IsC 9 gs l true (9 + 1 + a) :=
    isC_reader (n := 9) L.hcl l a ga hga hla true (Or.inr (by simp [fixBit, hopa]))
  obtain ⟨b, hab, hrb, hrcb⟩ := Least.next (n := 9) L l true (hnc true) a hal hCa
  have hub : ∀ q, Reads gs q (10 + a) → q = b := by
    intro q hq
    by_contra hne
    have hqa := reads_lt L.hcl hq
    obtain ⟨t, ht, hc⟩ := Least.save3 (n := 9) L l true (hnc true) a b q (by omega) (by omega)
      (Ne.symm hne) (rc_input true hra) hrcb (rc_of_reads (n := 9) hq hCa)
    have := hB1 t hc
    omega
  have hbl : b < gs.length := reads_len hrb
  obtain ⟨gb, hgb, hbin⟩ := hrb
  have hconst : stF 9 gs l true (9 + 1 + a) = Sum.inl true := by
    obtain ⟨c, hc⟩ := hCa
    have h1 := st_val_const 9 gs L.hcl l true (9 + 1 + a) c hc (fun _ => false)
    have h2 := hva (ins l true (fun _ => false))
    have h3 : vl gs (ins l true (fun _ : Fin 9 => false)) (l : ℕ) = true := by
      rw [vl_input gs _ _ l.isLt]
      exact Fin.insertNth_apply_same (α := fun _ => Bool) l true (fun _ : Fin 9 => false)
    rw [h3, Bool.true_or] at h2
    have h4 : c = true := h1.symm.trans h2
    rw [hc, h4]
  have hnCb : ¬ IsC 9 gs l true (9 + 1 + b) := by
    intro hc
    obtain ⟨q, hq, hr, hrc⟩ := Least.next (n := 9) L l true (hnc true) b hbl hc
    obtain ⟨t, ht, hc⟩ := Least.save3 (n := 9) L l true (hnc true) a b q (by omega) (by omega)
      (by omega) (rc_input true hra) hrcb hrc
    have := hB1 t hc
    omega
  obtain ⟨w, hwin, hopb, hvb⟩ : ∃ w, (gb.inputs = [10 + a, w] ∨ gb.inputs = [w, 10 + a]) ∧
      gb.op = GateOp.and ∧
      ∀ x : Fin 10 → Bool, vl gs x (10 + b) = (vl gs x (10 + a) && vl gs x w) := by
    rcases gate_cases gs L.hcl b gb hgb (10 + a) hbin with
      ⟨hop, hi, _⟩ | ⟨w, hin, ⟨hop, hv⟩ | ⟨hop, _⟩⟩
    · exfalso
      apply hnCb
      apply st_allconst 9 gs L.hcl l true b gb hgb
      intro e he
      rw [hi, List.mem_singleton] at he
      subst he
      exact hCa
    · exact ⟨w, hin, hop, hv⟩
    · exfalso
      apply hnCb
      apply const_read 9 gs L.hcl l true b gb hgb (9 + 1 + a) hbin
      rw [hconst]
      simp [fixBit, hop]
  have hult : u < 10 + a := by
    apply (L.hcl a ga hga).lt
    rcases hin with h | h <;> rw [h] <;> simp
  have hwlt : w < 10 + b := by
    apply (L.hcl b gb hgb).lt
    rcases hwin with h | h <;> rw [h] <;> simp
  refine ⟨a, b, u, w, ga, gb, hab, hbl, hga, hopa, hin, hgb, hopb, hwin, hva, hvb, hua, hub,
    hult, hwlt, ?_⟩
  rintro rfl
  apply L.no_alias hfnc b hbl (10 + a) (by omega)
  intro x
  rw [hvb, Bool.and_self]

theorem leaf (f : (Fin 10 → Bool) → Bool) (l p : Fin 10) (hlp : l ≠ p) (gs : List Gate) (o : ℕ)
    (L : Least 10 f gs o) (hN : gs.length ≤ 13)
    (hB0 : ∀ s, HasCircuitSize 10 (fun x => f (Function.update x l false)) s → 12 ≤ s)
    (hB1 : ∀ s, HasCircuitSize 10 (fun x => f (Function.update x l true)) s → 11 ≤ s)
    (hnc : ∀ b : Bool, ∃ x y : Fin 10 → Bool,
      f (Function.update x l b) ≠ f (Function.update y l b))
    (hP : ∀ x : Fin 10 → Bool, x l = true → x p = true → f x = true)
    (hQ : ∃ x : Fin 10 → Bool, x p = true ∧ x l = false ∧ f x = false)
    (hR : ∃ x y : Fin 10 → Bool, f (Function.update (Function.update x p false) l true) ≠
      f (Function.update (Function.update y p false) l true)) :
    ∃ (a b u w : ℕ) (ga gb : Gate), gs[a]? = some ga ∧
      ga.op = GateOp.or ∧ (ga.inputs = [(l : ℕ), u] ∨ ga.inputs = [u, (l : ℕ)]) ∧
      gs[b]? = some gb ∧ gb.op = GateOp.and ∧ (gb.inputs = [10 + a, w] ∨ gb.inputs = [w, 10 + a]) ∧
      (∀ x : Fin 10 → Bool, vl gs x (10 + a) = (vl gs x l || vl gs x u)) ∧
      (∀ x : Fin 10 → Bool, vl gs x (10 + b) = (vl gs x (10 + a) && vl gs x w)) ∧
      (∀ x : Fin 10 → Bool, vl gs x (10 + b) = true → f x = true) ∧
      (∀ x x' : Fin 10 → Bool, (∀ i, i ≠ p → x i = x' i) → ∀ j g, gs[j]? = some g →
        g.op = GateOp.and → vl gs x (10 + j) ≠ vl gs x' (10 + j) → j = b) ∧
      (∀ x x' : Fin 10 → Bool, (∀ i, i ≠ p → x i = x' i) → f x = false → f x' = true →
        vl gs x' (10 + b) = true) := by
  have hfnc : ∃ x y : Fin 10 → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc false
    exact ⟨_, _, h⟩
  have hdep : Dep f l := by
    obtain ⟨x, hx1, hx2, hx3⟩ := hQ
    refine ⟨x, ?_⟩
    rw [hx3, hx2, hP _ (by simp) (by rw [Function.update_of_ne (Ne.symm hlp)]; exact hx1)]
    simp
  obtain ⟨a, b, u, w, ga, gb, hab, hbl, hga, hopa, hain, hgb, hopb, hbin, hva, hvb, hua, hub,
    hult, hwlt, hwa⟩ := shape f l gs o L hN hB0 hB1 hnc hdep
  have hvl : ∀ x : Fin 10 → Bool, vl gs x l = x l := fun x => vl_input gs x l l.isLt
  have hua' : Reads gs a u := ⟨ga, hga, by rcases hain with h | h <;> rw [h] <;> simp⟩
  have hwb' : Reads gs b w := ⟨gb, hgb, by rcases hbin with h | h <;> rw [h] <;> simp⟩
  have hab' : Reads gs b (10 + a) := ⟨gb, hgb, by rcases hbin with h | h <;> rw [h] <;> simp⟩
  have hwl : w ≠ l := by
    rintro rfl
    have := hua b hwb'
    omega
  have hol : o ≠ l := by
    rintro rfl
    obtain ⟨x, y, hxy⟩ := hnc true
    apply hxy
    rw [← L.hev, ← L.hev, hvl, hvl]
    simp
  have hoa : o ≠ 10 + a := by
    rintro rfl
    obtain ⟨x, y, hxy⟩ := hnc true
    apply hxy
    rw [← L.hev, ← L.hev, hva, hva, hvl, hvl]
    simp
  -- the circuit without gates a and b
  set T : ℕ → ℕ := tau a b w l with hT
  set D : List Gate := dele gs a b w l with hDdef
  have hDlen : D.length + 2 = gs.length := dele_len gs a b w l hab hbl
  have hclD : CleanL 10 D := dele_clean gs L.hcl a b w l hab l.isLt hwlt hwa
  have hDv : ∀ x : Fin 10 → Bool, x l = true → ∀ i, vl D x (T i) = vl gs x i := by
    intro x hx
    apply dele_val gs L.hcl a b w l hab hbl hwlt hwa x
    · rw [hva, hvl, hx, Bool.true_or]
    · rw [hvb, hva, hvl, hx, Bool.true_or, Bool.true_and]
  have hTlow : ∀ i : Fin 10, T i = i := fun i => tau_low a b w l i i.isLt
  have hTa : T (10 + a) = l := tau_a a b w l
  have hTb : T (10 + b) = T w := tau_b a b w l hab hwlt hwa
  have hTinj : ∀ i j, i ≠ 10 + a → i ≠ 10 + b → j ≠ 10 + a → j ≠ 10 + b → T i = T j → i = j :=
    fun i j h1 h2 h3 h4 h => tau_inj a b w l i j hab h1 h2 h3 h4 h
  have hTg : ∀ j, j ≠ a → j ≠ b → T (10 + j) = 10 + dg a b j :=
    fun j h1 h2 => tau_gate a b w l j hab h1 h2
  have hTl : ∀ i, T i = l → i = l ∨ i = 10 + a := by
    intro i hi
    by_cases h1 : i = 10 + a
    · exact Or.inr h1
    · left
      have hl1 := l.isLt
      by_cases h2 : i = 10 + b
      · exfalso
        rw [h2, hTb] at hi
        exact hwl (hTinj w l hwa (by omega) (by omega) (by omega) (hi.trans (hTlow l).symm))
      · exact hTinj i l h1 h2 (by omega) (by omega) (hi.trans (hTlow l).symm)
  have hDl : ∀ j, ¬ Reads D j l := by
    rintro j ⟨g', hg', hlg⟩
    obtain ⟨j0, g, hja, hjb, hg, rfl, rfl⟩ := dele_inv gs a b w l hab j g' hg'
    obtain ⟨i, hi, hil⟩ := List.mem_map.1 hlg
    rcases hTl i hil with rfl | rfl
    · exact hja (hua _ ⟨g, hg, hi⟩)
    · exact hjb (hub _ ⟨g, hg, hi⟩)
  have hod : T o ≠ l := by
    intro h
    rcases hTl o h with h | h
    · exact hol h
    · exact hoa h
  have hDf : ∀ x : Fin 10 → Bool, vl D x (T o) = f (Function.update x l true) := by
    intro x
    have h1 : vl D x (T o) = vl D (Function.update x l true) (T o) := by
      apply agree_B D hclD x (Function.update x l true) (fun i => i = l) (T o + 1) _ _ (T o)
        (by omega) hod
      · intro j hj hjl
        rw [vl_input _ _ _ hj, vl_input _ _ _ hj,
          Function.update_of_ne (fun e => hjl (congrArg Fin.val e))]
      · rintro q g hg _ _ ⟨i, hi, hil⟩ _
        exfalso
        have hil' : i = l := hil
        subst hil'
        exact hDl q ⟨g, hg, hi⟩
    rw [h1, hDv _ (by simp), L.hev]
  obtain ⟨k, z, hz0, hzb, hzm, hzo, hoD, hzg, hzu⟩ := chain_at (n := 9) D (T o) p hclD
    (by
      intro s hs
      have e : (fun x : Fin 10 → Bool => vl D x (T o)) =
          fun x => f (Function.update x l true) := funext hDf
      have hs' : HasCircuitSize 10 (fun x : Fin 10 → Bool => vl D x (T o)) s := hs
      rw [e] at hs'
      have := hB1 s hs'
      omega)
    (by
      intro x hx
      rw [hDf]
      exact hP _ (by simp) (by rw [Function.update_of_ne (Ne.symm hlp)]; exact hx))
    (by
      obtain ⟨x, y, h⟩ := hR
      exact ⟨x, y, by rw [hDf, hDf]; exact h⟩)
  have hpl : (p : ℕ) ≠ l := fun e => hlp (Fin.ext e.symm)
  have hp10 := p.isLt
  have hl10 := l.isLt
  have hzl : ∀ r, r ≤ k + 1 → z r ≠ l := by
    intro r hr
    cases r with
    | zero => rw [hz0]; exact hpl
    | succ r => have := (hzb r (by omega)).1; omega
  have hmono : ∀ d r, r + d ≤ k + 1 → z r + d ≤ z (r + d) := by
    intro d
    induction d with
    | zero => intro r _; exact le_rfl
    | succ d ih =>
      intro r hr
      have h1 := ih r (by omega)
      have h2 := hzm (r + d) (by omega)
      rw [show r + (d + 1) = r + d + 1 by omega]
      omega
  have hzinj : ∀ r s, r ≤ k + 1 → s ≤ k + 1 → z r = z s → r = s := by
    intro r s hr hs h
    rcases Nat.lt_trichotomy r s with hh | hh | hh
    · have := hmono (s - r) r (by omega)
      rw [show r + (s - r) = s by omega] at this
      omega
    · exact hh
    · have := hmono (r - s) s (by omega)
      rw [show s + (r - s) = r by omega] at this
      omega
  -- a gate other than a and b that reads a chain wire is the next chain gate
  have hnext : ∀ j g i r, gs[j]? = some g → j ≠ a → j ≠ b → i ∈ g.inputs → r ≤ k + 1 →
      T i = z r → r ≤ k ∧ T (10 + j) = z (r + 1) := by
    intro j g i r hg hja hjb hi hr hTi
    have hrd : Reads D (dg a b j) (z r) :=
      ⟨_, dele_get gs a b w l hab j hja hjb g hg, List.mem_map.2 ⟨i, hi, hTi⟩⟩
    have h1 := reads_lt hclD hrd
    have h2 := reads_len hrd
    have hrk : r ≤ k := by
      by_contra hcon
      have : r = k + 1 := by omega
      rw [this, hzo] at h1
      omega
    refine ⟨hrk, ?_⟩
    rw [hTg j hja hjb]
    exact hzu r hrk _ hrd
  have hdown : ∀ i r, r ≤ k → T i = z (r + 1) → i ≠ 10 + b → ∃ j g, i = 10 + j ∧
      gs[j]? = some g ∧ g.op = GateOp.or ∧ ∃ i1 ∈ g.inputs, T i1 = z r := by
    intro i r hr hTi hib
    have hia : i ≠ 10 + a := by
      rintro rfl
      exact hzl (r + 1) (by omega) (hTi.symm.trans hTa)
    obtain ⟨g', hg', hop, hin⟩ := hzg r hr
    obtain ⟨j, g, hja, hjb, hg, hj, rfl⟩ := dele_inv gs a b w l hab _ g' hg'
    have h1 := (hzb r hr).1
    have h2 : T i = T (10 + j) := by
      rw [hTi, hTg j hja hjb]
      omega
    have h3 := hTinj i (10 + j) hia hib (by omega) (by omega) h2
    obtain ⟨i1, hi1, hT1⟩ := List.mem_map.1 hin
    exact ⟨j, g, h3, hg, hop, i1, hi1, hT1⟩
  let U : ℕ → Prop := fun i => ∃ r, r ≤ k + 1 ∧ T i = z r
  have hUa : ¬ U (10 + a) := by
    rintro ⟨r, hr, h⟩
    exact hzl r hr (h.symm.trans hTa)
  have hUl : ¬ U l := by
    rintro ⟨r, hr, h⟩
    exact hzl r hr (h.symm.trans (hTlow l))
  have hUp : U p := ⟨0, by omega, by rw [hTlow p, hz0]⟩
  have hM : ∀ i, U i → ¬ (U (10 + b) ∧ 10 + b ≤ i) → ∀ x : Fin 10 → Bool, x p = true →
      vl gs x i = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hU hnb x hx
      have hib : i ≠ 10 + b := by
        rintro rfl
        exact hnb ⟨hU, le_rfl⟩
      have hia : i ≠ 10 + a := by
        rintro rfl
        exact hUa hU
      obtain ⟨r, hr, hTi⟩ := hU
      cases r with
      | zero =>
        have e : i = p := hTinj i p hia hib (by omega) (by omega)
          (by rw [hTi, hz0, hTlow p])
        subst e
        rw [vl_input gs x p p.isLt]
        exact hx
      | succ r =>
        obtain ⟨j, g, rfl, hg, hop, i1, hi1, hT1⟩ := hdown i r (by omega) hTi hib
        have hlt := (L.hcl j g hg).lt i1 hi1
        have h1 := ih i1 hlt ⟨r, by omega, hT1⟩ (fun h => hnb ⟨h.1, by omega⟩) x hx
        rw [vl_gate gs L.hcl x j g hg, hop]
        show (g.inputs.map (vl gs x)).any id = true
        rw [List.any_eq_true]
        exact ⟨true, List.mem_map.2 ⟨i1, hi1, h1⟩, rfl⟩
  have hUw : U w := by
    by_contra h
    have hb' : ¬ U (10 + b) := by
      rintro ⟨r, hr, hh⟩
      exact h ⟨r, hr, hTb.symm.trans hh⟩
    obtain ⟨x, hx1, _, hx3⟩ := hQ
    have h1 := hM o ⟨k + 1, le_rfl, hzo.symm⟩ (fun h => hb' h.1) x hx1
    rw [L.hev, hx3] at h1
    exact absurd h1 (by simp)
  have hUu : ¬ U u := by
    intro h
    obtain ⟨x, hx1, hx2, hx3⟩ := hQ
    have hxp : Function.update x l true p = true := by
      rw [Function.update_of_ne (Ne.symm hlp)]; exact hx1
    have hu1 := hM u h (fun h => by omega) x hx1
    have hu2 := hM u h (fun h => by omega) (Function.update x l true) hxp
    have h1 : vl gs x o = vl gs (Function.update x l true) o := by
      apply agree_B gs L.hcl x (Function.update x l true) (fun i => i = l) (o + 1) _ _ o
        (by omega) hol
      · intro j hj hjl
        rw [vl_input _ _ _ hj, vl_input _ _ _ hj,
          Function.update_of_ne (fun e => hjl (congrArg Fin.val e))]
      · rintro q g hg _ _ ⟨i, hi, hil⟩ _
        have hil' : i = l := hil
        subst hil'
        have hq := hua q ⟨g, hg, hi⟩
        subst hq
        rw [hva, hva, hu1, hu2, Bool.or_true, Bool.or_true]
    rw [L.hev, L.hev, hx3, hP _ (by simp) hxp] at h1
    exact absurd h1 (by simp)
  -- gate b forces the output
  have hC1 : ∀ x : Fin 10 → Bool, vl gs x (10 + b) = true → f x = true := by
    intro x hx
    set x' := Function.update x l true with hx'
    have hx'l : x' l = true := by simp [hx']
    have hin : ∀ j, j < 10 → ¬ (j = (l : ℕ) ∨ j = 10 + a) → vl gs x j = vl gs x' j := by
      intro j hj hjl
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj, hx',
        Function.update_of_ne (fun e => hjl (Or.inl (congrArg Fin.val e)))]
    have hw1 : vl gs x w = vl gs x' w := by
      apply agree_B gs L.hcl x x' (fun i => i = (l : ℕ) ∨ i = 10 + a) (10 + b) hin _ w hwlt
        (by rintro (h | h); exacts [hwl h, hwa h])
      rintro q g hg hq hnB ⟨i, hi, rfl | rfl⟩ _
      · exact absurd (Or.inr (by rw [hua q ⟨g, hg, hi⟩])) hnB
      · have := hub q ⟨g, hg, hi⟩
        omega
    have hw2 : vl gs x w = true := by
      rw [hvb, Bool.and_eq_true] at hx
      exact hx.2
    have hw3 : vl gs x' w = true := by rw [← hw1]; exact hw2
    have hb3 : vl gs x' (10 + b) = true := by
      rw [hvb, hva, hvl, hx'l, hw3]; rfl
    have ho1 : vl gs x o = vl gs x' o := by
      apply agree_B gs L.hcl x x' (fun i => i = (l : ℕ) ∨ i = 10 + a) (o + 1) hin _ o (by omega)
        (by rintro (h | h); exacts [hol h, hoa h])
      rintro q g hg hq hnB ⟨i, hi, rfl | rfl⟩ _
      · exact absurd (Or.inr (by rw [hua q ⟨g, hg, hi⟩])) hnB
      · rw [hub q ⟨g, hg, hi⟩, hx, hb3]
    obtain ⟨r0, hr0, hTw⟩ := hUw
    have hup : ∀ d, r0 + d ≤ k + 1 → vl D x' (z (r0 + d)) = true := by
      intro d
      induction d with
      | zero =>
        intro _
        rw [Nat.add_zero, ← hTw, hDv x' hx'l]
        exact hw3
      | succ d ih =>
        intro hd
        have h1 := ih (by omega)
        obtain ⟨g, hg, hop, hi⟩ := hzg (r0 + d) (by omega)
        have h2 := (hzb (r0 + d) (by omega)).1
        rw [show r0 + (d + 1) = r0 + d + 1 by omega,
          show z (r0 + d + 1) = 10 + (z (r0 + d + 1) - 10) by omega,
          vl_gate D hclD x' _ g hg, hop]
        show (g.inputs.map (vl D x')).any id = true
        rw [List.any_eq_true]
        exact ⟨true, List.mem_map.2 ⟨_, hi, h1⟩, rfl⟩
    have h1 := hup (k + 1 - r0) (by omega)
    rw [show r0 + (k + 1 - r0) = k + 1 by omega, hzo, hDv x' hx'l, ← ho1, L.hev] at h1
    exact h1
  have hinU : ∀ x x' : Fin 10 → Bool, (∀ i, i ≠ p → x i = x' i) → ∀ j, j < 10 → j ≠ (p : ℕ) →
      vl gs x j = vl gs x' j := by
    intro x x' hxx j hj hne
    rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
    exact hxx _ (fun e => hne (congrArg Fin.val e))
  refine ⟨a, b, u, w, ga, gb, hga, hopa, hain, hgb, hopb, hbin, hva, hvb, hC1, ?_, ?_⟩
  · intro x x' hxx j g hg hop hne
    have hUj : U (10 + j) := by
      by_contra hnU
      apply hne
      apply agree_B gs L.hcl x x' U (10 + j + 1) _ _ (10 + j) (by omega) hnU
      · intro i hi hnUi
        apply hinU x x' hxx i hi
        rintro rfl
        exact hnUi hUp
      · rintro q g' hg' _ hnq ⟨i, hi, hUi⟩ _
        exfalso
        by_cases hqa : q = a
        · subst hqa
          have e := some_eq hga hg'
          subst e
          have : i = l ∨ i = u := by
            rcases hain with h | h <;> rw [h] at hi <;> simp at hi <;> tauto
          rcases this with rfl | rfl
          · exact hUl hUi
          · exact hUu hUi
        · by_cases hqb : q = b
          · subst hqb
            obtain ⟨r, hr, hh⟩ := hUw
            exact hnq ⟨r, hr, hTb.trans hh⟩
          · obtain ⟨r, hr, hh⟩ := hUi
            obtain ⟨h1, h2⟩ := hnext q g' i r hg' hqa hqb hi hr hh
            exact hnq ⟨r + 1, by omega, h2⟩
    by_contra hjb
    have hja : j ≠ a := by
      rintro rfl
      have e := some_eq hga hg
      subst e
      rw [hopa] at hop
      exact absurd hop (by simp)
    obtain ⟨r, hr, hh⟩ := hUj
    cases r with
    | zero =>
      rw [hTg j hja hjb, hz0] at hh
      omega
    | succ r =>
      obtain ⟨j', g', hj', hg', hop', _⟩ := hdown (10 + j) r (by omega) hh (by omega)
      have e1 : j' = j := by omega
      subst e1
      have e2 := some_eq hg hg'
      subst e2
      rw [hop] at hop'
      exact absurd hop' (by simp)
  · intro x x' hxx hfx hfx'
    by_contra hbx'
    have hb1 : vl gs x' (10 + b) = false := by simpa using hbx'
    have hb0 : vl gs x (10 + b) = false := by
      by_contra h
      have := hC1 x (by simpa using h)
      rw [hfx] at this
      exact absurd this (by simp)
    obtain ⟨r0, hr0, hTw⟩ := hUw
    have hw10b : w ≠ 10 + b := by omega
    -- gate b is the output or has a reader
    have hbread : ∀ r, r ≤ k + 1 → T w = z r → o ≠ 10 + b → r ≤ k ∧ ∃ q, q ≠ a ∧ q ≠ b ∧
        Reads gs q (10 + b) ∧ T (10 + q) = z (r + 1) := by
      intro r hr hh hob
      obtain ⟨q, hq, g, hg, hi⟩ := L.live hfnc b hbl hob
      have hqa : q ≠ a := by omega
      have hqb : q ≠ b := by omega
      obtain ⟨h1, h2⟩ := hnext q g (10 + b) r hg hqa hqb hi hr (hTb.trans hh)
      exact ⟨h1, q, hqa, hqb, ⟨g, hg, hi⟩, h2⟩
    let B : ℕ → Prop := fun i => i ≠ 10 + b ∧ ∃ r, r ≤ r0 ∧ T i = z r
    have hBU : ∀ i, B i → U i := by
      rintro i ⟨_, r, hr, hh⟩
      exact ⟨r, by omega, hh⟩
    have hoB : ¬ B o := by
      rintro ⟨hob, r, hr, hh⟩
      have hr1 : r = k + 1 := hzinj r (k + 1) (by omega) le_rfl (by rw [← hh, hzo])
      obtain ⟨h1, _⟩ := hbread r0 hr0 hTw hob
      omega
    have ho : vl gs x o = vl gs x' o := by
      apply agree_B gs L.hcl x x' B (o + 1) _ _ o (by omega) hoB
      · intro i hi hnB
        apply hinU x x' hxx i hi
        rintro rfl
        exact hnB ⟨by omega, 0, by omega, by rw [hTlow p, hz0]⟩
      · rintro q g' hg' _ hnq ⟨i, hi, hBi⟩ _
        by_cases hqa : q = a
        · exfalso
          subst hqa
          have e := some_eq hga hg'
          subst e
          have : i = l ∨ i = u := by
            rcases hain with h | h <;> rw [h] at hi <;> simp at hi <;> tauto
          rcases this with rfl | rfl
          · exact hUl (hBU _ hBi)
          · exact hUu (hBU _ hBi)
        · by_cases hqb : q = b
          · rw [hqb, hb0, hb1]
          · exfalso
            obtain ⟨hib, r, hr, hh⟩ := hBi
            obtain ⟨h1, h2⟩ := hnext q g' i r hg' hqa hqb hi (by omega) hh
            by_cases hrr : r < r0
            · exact hnq ⟨by omega, r + 1, by omega, h2⟩
            · have hre : r = r0 := by omega
              subst hre
              have hia : i ≠ 10 + a := by
                rintro rfl
                exact hUa ⟨r, hr0, hh⟩
              have hiw : i = w := hTinj i w hia hib hwa hw10b (hh.trans hTw.symm)
              subst hiw
              have hob : o ≠ 10 + b := by
                rintro rfl
                have : r = k + 1 := hzinj r (k + 1) hr0 le_rfl (by rw [hzo, hTb, hTw])
                omega
              obtain ⟨_, q2, hq2a, hq2b, hq2r, hq2⟩ := hbread r hr0 hTw hob
              have hqq : 10 + q2 = 10 + q := hTinj _ _ (by omega) (by omega) (by omega) (by omega)
                (hq2.trans h2.symm)
              have hqq' : q2 = q := by omega
              subst hqq'
              exact L.no_tri hfnc b q2 i hwb' ⟨g', hg', hi⟩ hq2r
    rw [L.hev, L.hev, hfx, hfx'] at ho
    exact absurd ho (by simp)

end PEqualNP.Outside.L_meta_1547.Main

namespace PEqualNP.Outside.L_meta_1547.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1547.Helpers
open PEqualNP.Outside.L_meta_1547.Helpers.Readers

def G10 : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0), (0, 7), (1, 8), (4, 9)]

def rk (t : List (Fin 10)) (v : Fin 10) : ℕ := t.idxOf v

theorem tree0 : (7, 7) ∉ G10 ∧ (nb G10 7).length = 1 ∧
    (G10.filter (fun e => e.1 ≠ 7 ∧ e.2 ≠ 7 ∧ e.1 ∉ nb G10 7 ∧ e.2 ∉ nb G10 7)).length = 7 ∧
    Good (nb G10 7)
      (G10.filter (fun e => e.1 ≠ 7 ∧ e.2 ≠ 7 ∧ e.1 ∉ nb G10 7 ∧ e.2 ∉ nb G10 7))
      [(1, 8), (2, 3), (4, 9), (5, 6)] (rk [8, 1, 2, 3, 4, 9, 5, 6, 0, 7]) := by
  unfold Good
  decide +kernel

theorem tree1 : (8, 8) ∉ G10 ∧ (nb G10 8).length = 1 ∧
    (G10.filter (fun e => e.1 ≠ 8 ∧ e.2 ≠ 8 ∧ e.1 ∉ nb G10 8 ∧ e.2 ∉ nb G10 8)).length = 7 ∧
    Good (nb G10 8)
      (G10.filter (fun e => e.1 ≠ 8 ∧ e.2 ≠ 8 ∧ e.1 ∉ nb G10 8 ∧ e.2 ∉ nb G10 8))
      [(0, 7), (2, 3), (4, 9), (5, 6)] (rk [7, 0, 6, 5, 4, 9, 3, 2, 1, 8]) := by
  unfold Good
  decide +kernel

theorem lb_true7 (s : ℕ)
    (h : HasCircuitSize 10 (fun x => ev [] G10 (Function.update x 7 true)) s) : 11 ≤ s := by
  obtain ⟨h0, h1, h2, hg⟩ := tree0
  rw [ev_true G10 7 h0] at h
  have := forest_lb _ _ _ _ hg s h
  rw [h1, h2] at this
  simp at this
  omega

theorem lb_true8 (s : ℕ)
    (h : HasCircuitSize 10 (fun x => ev [] G10 (Function.update x 8 true)) s) : 11 ≤ s := by
  obtain ⟨h0, h1, h2, hg⟩ := tree1
  rw [ev_true G10 8 h0] at h
  have := forest_lb _ _ _ _ hg s h
  rw [h1, h2] at this
  simp at this
  omega

-- One gate is saved when an input is fixed to false.
theorem drop_leaf (E : List (Fin 10 × Fin 10)) (y : Fin 10) (s : ℕ)
    (hd : ∃ r : Fin 10, ev [] E (Function.update (ind r) y (!(ind r y))) ≠ ev [] E (ind r))
    (hn : ∀ b : Bool, ev [] E (Function.update (fun _ => true) y b) ≠
      ev [] E (Function.update (fun _ => false) y b))
    (h : HasCircuitSize 10 (ev [] E) s) :
    ∃ t, t + 1 ≤ s ∧ HasCircuitSize 10 (ev [] (E.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y))) t := by
  obtain ⟨r, hr⟩ := hd
  obtain ⟨gs, o, L, hl⟩ := exists_least 10 (ev [] E) s ⟨_, _, hr⟩ h
  obtain ⟨q, hq⟩ := L.dep_read y ⟨_, hr⟩ (fun b => ⟨_, _, hn b⟩)
  obtain ⟨t, ht, hc⟩ := Least.save (n := 9) L y false ⟨_, _, hn false⟩ {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at ht
  rw [ev_false] at hc
  exact ⟨t, by omega, hc⟩

theorem lb_false7 (s : ℕ)
    (h : HasCircuitSize 10 (fun x => ev [] G10 (Function.update x 7 false)) s) : 12 ≤ s := by
  rw [ev_false] at h
  obtain ⟨t, ht, h1⟩ := drop_leaf _ 8 s ⟨1, by decide +kernel⟩ (by decide +kernel) h
  obtain ⟨t', ht', h2⟩ := drop_leaf _ 9 t ⟨4, by decide +kernel⟩ (by decide +kernel) h1
  have e : (((G10.filter (fun e => e.1 ≠ 7 ∧ e.2 ≠ 7)).filter (fun e => e.1 ≠ 8 ∧ e.2 ≠ 8)).filter
      (fun e => e.1 ≠ 9 ∧ e.2 ≠ 9)) = cyc7 := by decide +kernel
  rw [e] at h2
  have := cyc7_lb t' h2
  omega

theorem lb_false8 (s : ℕ)
    (h : HasCircuitSize 10 (fun x => ev [] G10 (Function.update x 8 false)) s) : 12 ≤ s := by
  rw [ev_false] at h
  obtain ⟨t, ht, h1⟩ := drop_leaf _ 7 s ⟨0, by decide +kernel⟩ (by decide +kernel) h
  obtain ⟨t', ht', h2⟩ := drop_leaf _ 9 t ⟨4, by decide +kernel⟩ (by decide +kernel) h1
  have e : (((G10.filter (fun e => e.1 ≠ 8 ∧ e.2 ≠ 8)).filter (fun e => e.1 ≠ 7 ∧ e.2 ≠ 7)).filter
      (fun e => e.1 ≠ 9 ∧ e.2 ≠ 9)) = cyc7 := by decide +kernel
  rw [e] at h2
  have := cyc7_lb t' h2
  omega

theorem G10_nc : ∀ (p : Fin 10) (b : Bool),
    ev [] G10 (Function.update (fun _ => true) p b) ≠
      ev [] G10 (Function.update (fun _ => false) p b) := by
  decide +kernel

theorem edge_true (i j : Fin 10) (h : (i, j) ∈ G10) (x : Fin 10 → Bool) (hi : x i = true)
    (hj : x j = true) : ev [] G10 x = true :=
  (ev_iff _ _ _).2 (Or.inr ⟨(i, j), h, hi, hj⟩)

theorem main (s : ℕ) (h : HasCircuitSize 10 (ev [] G10) s) : 14 ≤ s := by
  by_contra hs
  obtain ⟨gs, o, L, hl⟩ := exists_least 10 (ev [] G10) s ⟨_, _, G10_nc 0 false⟩ h
  obtain ⟨a0, b0, u0, w0, ga0, gb0, hga0, hopa0, hain0, hgb0, hopb0, hbin0, hva0, hvb0, hA1, hA3,
    hA4⟩ := leaf (ev [] G10) 7 0 (by decide) gs o L (by omega) lb_false7 lb_true7
      (fun b => ⟨_, _, G10_nc 7 b⟩)
      (fun x h1 h2 => edge_true 0 7 (by decide) x h2 h1)
      ⟨ind 0, by decide, by decide, by decide +kernel⟩
      ⟨fun _ => true, fun _ => false, by decide +kernel⟩
  obtain ⟨a1, b1, u1, w1, ga1, gb1, hga1, hopa1, hain1, hgb1, hopb1, hbin1, hva1, hvb1, hB1, hB3,
    hB4⟩ := leaf (ev [] G10) 8 1 (by decide) gs o L (by omega) lb_false8 lb_true8
      (fun b => ⟨_, _, G10_nc 8 b⟩)
      (fun x h1 h2 => edge_true 1 8 (by decide) x h2 h1)
      ⟨ind 1, by decide, by decide, by decide +kernel⟩
      ⟨fun _ => true, fun _ => false, by decide +kernel⟩
  let e0 : Fin 10 → Bool := ind 0
  let e1 : Fin 10 → Bool := ind 1
  let e01 : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 1)
  have f0 : ev [] G10 e0 = false := by decide +kernel
  have f1 : ev [] G10 e1 = false := by decide +kernel
  have f01 : ev [] G10 e01 = true := by decide +kernel
  have d0 : ∀ i : Fin 10, i ≠ 0 → e1 i = e01 i := by decide +kernel
  have d1 : ∀ i : Fin 10, i ≠ 1 → e0 i = e01 i := by decide +kernel
  have hb01 : vl gs e01 (10 + b0) = true := hA4 e1 e01 d0 f1 f01
  have hb00 : vl gs e0 (10 + b0) = false := by
    by_contra hcon
    have := hA1 e0 (by simpa using hcon)
    rw [f0] at this
    exact absurd this (by simp)
  have hbb : b0 = b1 := hB3 e0 e01 d1 b0 gb0 hgb0 hopb0 (by rw [hb00, hb01]; simp)
  subst hbb
  have hgg : gb0 = gb1 := some_eq hgb0 hgb1
  subst hgg
  have hin7 : ∀ x : Fin 10 → Bool, vl gs x ((7 : Fin 10) : ℕ) = x 7 :=
    fun x => vl_input gs x _ (7 : Fin 10).isLt
  have hin8 : ∀ x : Fin 10 → Bool, vl gs x ((8 : Fin 10) : ℕ) = x 8 :=
    fun x => vl_input gs x _ (8 : Fin 10).isLt
  by_cases haa : a0 = a1
  · subst haa
    have e := some_eq hga0 hga1
    subst e
    have hu : u0 = ((8 : Fin 10) : ℕ) := by
      rcases hain0 with h0 | h0 <;> rcases hain1 with h1 | h1 <;> rw [h0] at h1 <;>
        simp at h1 <;> omega
    have h1 : vl gs e01 (10 + a0) = true := by
      rw [hvb0, Bool.and_eq_true] at hb01
      exact hb01.1
    rw [hva0, hu, hin7, hin8] at h1
    exact absurd h1 (by decide)
  · have hw : w0 = 10 + a1 := by
      rcases hbin0 with h0 | h0 <;> rcases hbin1 with h1 | h1 <;> rw [h0] at h1 <;>
        simp at h1 <;> omega
    let e78 : Fin 10 → Bool := fun i => decide (i = 7 ∨ i = 8)
    have f78 : ev [] G10 e78 = false := by decide +kernel
    have h1 : vl gs e78 (10 + b0) = true := by
      rw [hvb0, hva0, hw, hva1, hin7, hin8]
      rfl
    have := hA1 e78 h1
    rw [f78] at this
    exact absurd this (by simp)

end PEqualNP.Outside.L_meta_1547.Main

theorem PEqualNP.Outside.L_meta_1547 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0), (0, 7), (1, 8), (4, 9)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) s → 14 ≤ s := by
  intro s h
  apply PEqualNP.Outside.L_meta_1547.Main.main s
  have e : (fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0), (0, 7), (1, 8), (4, 9)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) = PEqualNP.Outside.L_meta_1547.Main.ev [] PEqualNP.Outside.L_meta_1547.Main.G10 := by
    funext x
    simp only [PEqualNP.Outside.L_meta_1547.Main.ev, List.any_nil, Bool.false_or, PEqualNP.Outside.L_meta_1547.Main.G10]
  rw [← e]
  exact h
