import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_917_aux

namespace H917
open PEqualNP PEqualNP.MetaComplexity

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

end H917

namespace H917
open PEqualNP PEqualNP.MetaComplexity

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

end H917

namespace H917
open PEqualNP PEqualNP.MetaComplexity

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

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

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
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
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
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
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
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
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
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
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
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
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
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
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
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
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

end H917

namespace H917
open PEqualNP PEqualNP.MetaComplexity

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
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
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
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
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
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
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
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
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
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
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
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
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
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega

theorem parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega

end H917

namespace H917.PermInputs
open PEqualNP PEqualNP.MetaComplexity

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

end H917.PermInputs

namespace H917.Forest
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open H917.PermInputs

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
  have h' := H917.gate_elim n _ b s hdep' hnc' hg
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

end H917.Forest

namespace H917.Forest
open PEqualNP PEqualNP.MetaComplexity

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

end H917.Forest

namespace H917.Forest
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open H917.PermInputs
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

theorem forest_bound : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsAcyclic → (∃ i j : Fin n, G.Adj i j) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s →
    G.edgeFinset.card + k ≤ s + 1 := by
  intro n k s G _ hac hE hk hC
  have hf : (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) = F G ∅ := by
    funext x
    rw [Bool.eq_iff_iff, F_true, decide_eq_true_iff]
    simp
  rw [hf] at hC
  have := claimQ _ n G ∅ k s rfl hac (by simp) (fun T hT => hk T hT) (Or.inr hE) hC
  have he : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [Finset.card_empty] at this
  omega

end H917.Forest

namespace H917
open PEqualNP PEqualNP.MetaComplexity

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

end H917

namespace H917.EdgeUpper
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds H917

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

end H917.EdgeUpper

theorem acyc_of_lt {n : ℕ} (H : SimpleGraph (Fin n))
    (h : ∀ x u v : Fin n, H.Adj x u → H.Adj x v → u ≠ v → x < u ∨ x < v) : H.IsAcyclic := by
  classical
  intro z w cyc
  obtain ⟨m, hm, hmax⟩ := w.support.toFinset.exists_max_image id ⟨z, by simp⟩
  have hm' : m ∈ w.support := by simpa using hm
  have hq : (w.rotate m hm').IsCycle := cyc.rotate hm'
  have hs := (w.rotate m hm').adj_snd hq.not_nil
  have hp := ((w.rotate m hm').adj_penultimate hq.not_nil).symm
  have hne := hq.snd_ne_penultimate
  have m1 : (w.rotate m hm').snd ∈ w.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff w m hm']
    exact SimpleGraph.Walk.getVert_mem_support _ _
  have m2 : (w.rotate m hm').penultimate ∈ w.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff w m hm']
    exact SimpleGraph.Walk.getVert_mem_support _ _
  have b1 := hmax _ (by simpa using m1)
  have b2 := hmax _ (by simpa using m2)
  rcases h m _ _ hs hp hne with h1 | h1
  · exact absurd b1 (not_le.mpr h1)
  · exact absurd b2 (not_le.mpr h1)

def ad1 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0),(6,7),(7,6)])

def G1 : SimpleGraph (Fin 8) where
  Adj i j := ad1 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst1 : DecidableRel G1.Adj := fun i j => inferInstanceAs (Decidable (ad1 i j = true))

theorem hacyc1 : G1.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun1 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G1.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (g && h)) = decide (∃ i j : Fin 8, G1.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard1 : G1.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov1 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G1.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.singleton_subset_iff.mpr a2⟩))

theorem hcovb1 : ∀ i j : Fin 8, G1.Adj i j → i ∈ ({0, 6} : Finset (Fin 8)) ∨ j ∈ ({0, 6} : Finset (Fin 8)) := by
  decide

theorem main1 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 6 && x 7)) s ↔ 7 ≤ s := by
  intro s
  rw [hfun1]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 2 s G1 hacyc1 ⟨0, 1, by decide⟩ hcov1 h
    rw [hcard1] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G1 {0, 6} ⟨0, 1, by decide⟩ hcovb1
    rw [hcard1] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 6} : Finset (Fin 8)).card = 2 := by decide
    rw [this] at h2
    omega

def ad2 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(5,6),(6,5),(5,7),(7,5)])

def G2 : SimpleGraph (Fin 8) where
  Adj i j := ad2 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst2 : DecidableRel G2.Adj := fun i j => inferInstanceAs (Decidable (ad2 i j = true))

theorem hacyc2 : G2.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun2 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6) || (x 5 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G2.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (f && g) || (f && h)) = decide (∃ i j : Fin 8, G2.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard2 : G2.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov2 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G2.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 5 6 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.singleton_subset_iff.mpr a2⟩))

theorem hcovb2 : ∀ i j : Fin 8, G2.Adj i j → i ∈ ({0, 5} : Finset (Fin 8)) ∨ j ∈ ({0, 5} : Finset (Fin 8)) := by
  decide

theorem main2 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6) || (x 5 && x 7)) s ↔ 7 ≤ s := by
  intro s
  rw [hfun2]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 2 s G2 hacyc2 ⟨0, 1, by decide⟩ hcov2 h
    rw [hcard2] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G2 {0, 5} ⟨0, 1, by decide⟩ hcovb2
    rw [hcard2] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 5} : Finset (Fin 8)).card = 2 := by decide
    rw [this] at h2
    omega

def ad3 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,5),(5,1),(6,7),(7,6)])

def G3 : SimpleGraph (Fin 8) where
  Adj i j := ad3 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst3 : DecidableRel G3.Adj := fun i j => inferInstanceAs (Decidable (ad3 i j = true))

theorem hacyc3 : G3.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun3 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G3.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (g && h)) = decide (∃ i j : Fin 8, G3.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard3 : G3.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov3 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G3.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  intro T hT
  have e1 := hT 0 2 (by decide)
  have e2 := hT 1 5 (by decide)
  have e3 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.singleton_subset_iff.mpr a3⟩⟩))

theorem hcovb3 : ∀ i j : Fin 8, G3.Adj i j → i ∈ ({0, 1, 6} : Finset (Fin 8)) ∨ j ∈ ({0, 1, 6} : Finset (Fin 8)) := by
  decide

theorem main3 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 6 && x 7)) s ↔ 8 ≤ s := by
  intro s
  rw [hfun3]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 3 s G3 hacyc3 ⟨0, 1, by decide⟩ hcov3 h
    rw [hcard3] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G3 {0, 1, 6} ⟨0, 1, by decide⟩ hcovb3
    rw [hcard3] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 1, 6} : Finset (Fin 8)).card = 3 := by decide
    rw [this] at h2
    omega

def ad4 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(4,5),(5,4),(4,6),(6,4),(4,7),(7,4)])

def G4 : SimpleGraph (Fin 8) where
  Adj i j := ad4 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst4 : DecidableRel G4.Adj := fun i j => inferInstanceAs (Decidable (ad4 i j = true))

theorem hacyc4 : G4.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun4 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 4 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G4.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (a && d) || (e && f) || (e && g) || (e && h)) = decide (∃ i j : Fin 8, G4.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard4 : G4.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov4 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G4.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 4 5 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.singleton_subset_iff.mpr a2⟩))

theorem hcovb4 : ∀ i j : Fin 8, G4.Adj i j → i ∈ ({0, 4} : Finset (Fin 8)) ∨ j ∈ ({0, 4} : Finset (Fin 8)) := by
  decide

theorem main4 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 4 && x 7)) s ↔ 7 ≤ s := by
  intro s
  rw [hfun4]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 2 s G4 hacyc4 ⟨0, 1, by decide⟩ hcov4 h
    rw [hcard4] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G4 {0, 4} ⟨0, 1, by decide⟩ hcovb4
    rw [hcard4] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 4} : Finset (Fin 8)).card = 2 := by decide
    rw [this] at h2
    omega

def ad5 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(1,4),(4,1),(2,5),(5,2),(6,7),(7,6)])

def G5 : SimpleGraph (Fin 8) where
  Adj i j := ad5 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst5 : DecidableRel G5.Adj := fun i j => inferInstanceAs (Decidable (ad5 i j = true))

theorem hacyc5 : G5.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun5 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G5.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (b && d) || (b && e) || (c && f) || (g && h)) = decide (∃ i j : Fin 8, G5.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard5 : G5.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov5 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G5.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 2 5 (by decide)
  have e3 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.singleton_subset_iff.mpr a3⟩⟩))

theorem hcovb5 : ∀ i j : Fin 8, G5.Adj i j → i ∈ ({1, 2, 6} : Finset (Fin 8)) ∨ j ∈ ({1, 2, 6} : Finset (Fin 8)) := by
  decide

theorem main5 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 6 && x 7)) s ↔ 8 ≤ s := by
  intro s
  rw [hfun5]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 3 s G5 hacyc5 ⟨0, 1, by decide⟩ hcov5 h
    rw [hcard5] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G5 {1, 2, 6} ⟨0, 1, by decide⟩ hcovb5
    rw [hcard5] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({1, 2, 6} : Finset (Fin 8)).card = 3 := by decide
    rw [this] at h2
    omega

def ad6 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(1,5),(5,1),(6,7),(7,6)])

def G6 : SimpleGraph (Fin 8) where
  Adj i j := ad6 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst6 : DecidableRel G6.Adj := fun i j => inferInstanceAs (Decidable (ad6 i j = true))

theorem hacyc6 : G6.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun6 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G6.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (b && f) || (g && h)) = decide (∃ i j : Fin 8, G6.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard6 : G6.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov6 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G6.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  intro T hT
  have e1 := hT 0 2 (by decide)
  have e2 := hT 1 4 (by decide)
  have e3 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.singleton_subset_iff.mpr a3⟩⟩))

theorem hcovb6 : ∀ i j : Fin 8, G6.Adj i j → i ∈ ({0, 1, 6} : Finset (Fin 8)) ∨ j ∈ ({0, 1, 6} : Finset (Fin 8)) := by
  decide

theorem main6 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 6 && x 7)) s ↔ 8 ≤ s := by
  intro s
  rw [hfun6]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 3 s G6 hacyc6 ⟨0, 1, by decide⟩ hcov6 h
    rw [hcard6] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G6 {0, 1, 6} ⟨0, 1, by decide⟩ hcovb6
    rw [hcard6] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 1, 6} : Finset (Fin 8)).card = 3 := by decide
    rw [this] at h2
    omega

def ad7 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(5,6),(6,5),(5,7),(7,5)])

def G7 : SimpleGraph (Fin 8) where
  Adj i j := ad7 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst7 : DecidableRel G7.Adj := fun i j => inferInstanceAs (Decidable (ad7 i j = true))

theorem hacyc7 : G7.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun7 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6) || (x 5 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G7.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (f && g) || (f && h)) = decide (∃ i j : Fin 8, G7.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard7 : G7.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov7 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G7.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  intro T hT
  have e1 := hT 0 2 (by decide)
  have e2 := hT 1 4 (by decide)
  have e3 := hT 5 6 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.singleton_subset_iff.mpr a3⟩⟩))

theorem hcovb7 : ∀ i j : Fin 8, G7.Adj i j → i ∈ ({0, 1, 5} : Finset (Fin 8)) ∨ j ∈ ({0, 1, 5} : Finset (Fin 8)) := by
  decide

theorem main7 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6) || (x 5 && x 7)) s ↔ 8 ≤ s := by
  intro s
  rw [hfun7]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 3 s G7 hacyc7 ⟨0, 1, by decide⟩ hcov7 h
    rw [hcard7] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G7 {0, 1, 5} ⟨0, 1, by decide⟩ hcovb7
    rw [hcard7] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 1, 5} : Finset (Fin 8)).card = 3 := by decide
    rw [this] at h2
    omega

def ad8 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(4,5),(5,4),(4,6),(6,4),(5,7),(7,5)])

def G8 : SimpleGraph (Fin 8) where
  Adj i j := ad8 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst8 : DecidableRel G8.Adj := fun i j => inferInstanceAs (Decidable (ad8 i j = true))

theorem hacyc8 : G8.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun8 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G8.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (a && d) || (e && f) || (e && g) || (f && h)) = decide (∃ i j : Fin 8, G8.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard8 : G8.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov8 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G8.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 4 6 (by decide)
  have e3 := hT 5 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.singleton_subset_iff.mpr a3⟩⟩))

theorem hcovb8 : ∀ i j : Fin 8, G8.Adj i j → i ∈ ({0, 4, 5} : Finset (Fin 8)) ∨ j ∈ ({0, 4, 5} : Finset (Fin 8)) := by
  decide

theorem main8 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) s ↔ 8 ≤ s := by
  intro s
  rw [hfun8]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 3 s G8 hacyc8 ⟨0, 1, by decide⟩ hcov8 h
    rw [hcard8] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G8 {0, 4, 5} ⟨0, 1, by decide⟩ hcovb8
    rw [hcard8] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 4, 5} : Finset (Fin 8)).card = 3 := by decide
    rw [this] at h2
    omega

def ad9 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(1,4),(4,1),(2,5),(5,2),(6,7),(7,6)])

def G9 : SimpleGraph (Fin 8) where
  Adj i j := ad9 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst9 : DecidableRel G9.Adj := fun i j => inferInstanceAs (Decidable (ad9 i j = true))

theorem hacyc9 : G9.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun9 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G9.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (g && h)) = decide (∃ i j : Fin 8, G9.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard9 : G9.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov9 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G9.Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
  intro T hT
  have e1 := hT 0 3 (by decide)
  have e2 := hT 1 4 (by decide)
  have e3 := hT 2 5 (by decide)
  have e4 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3 <;> rcases e4 with a4 | a4
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.insert_subset_iff.mpr ⟨a3, Finset.singleton_subset_iff.mpr a4⟩⟩⟩))

theorem hcovb9 : ∀ i j : Fin 8, G9.Adj i j → i ∈ ({0, 1, 2, 6} : Finset (Fin 8)) ∨ j ∈ ({0, 1, 2, 6} : Finset (Fin 8)) := by
  decide

theorem main9 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 6 && x 7)) s ↔ 9 ≤ s := by
  intro s
  rw [hfun9]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 4 s G9 hacyc9 ⟨0, 1, by decide⟩ hcov9 h
    rw [hcard9] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G9 {0, 1, 2, 6} ⟨0, 1, by decide⟩ hcovb9
    rw [hcard9] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 1, 2, 6} : Finset (Fin 8)).card = 4 := by decide
    rw [this] at h2
    omega

def ad10 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(2,4),(4,2),(5,6),(6,5),(5,7),(7,5)])

def G10 : SimpleGraph (Fin 8) where
  Adj i j := ad10 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst10 : DecidableRel G10.Adj := fun i j => inferInstanceAs (Decidable (ad10 i j = true))

theorem hacyc10 : G10.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun10 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6) || (x 5 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G10.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (b && d) || (c && e) || (f && g) || (f && h)) = decide (∃ i j : Fin 8, G10.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard10 : G10.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov10 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G10.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 2 4 (by decide)
  have e3 := hT 5 6 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.singleton_subset_iff.mpr a3⟩⟩))

theorem hcovb10 : ∀ i j : Fin 8, G10.Adj i j → i ∈ ({1, 2, 5} : Finset (Fin 8)) ∨ j ∈ ({1, 2, 5} : Finset (Fin 8)) := by
  decide

theorem main10 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6) || (x 5 && x 7)) s ↔ 8 ≤ s := by
  intro s
  rw [hfun10]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 3 s G10 hacyc10 ⟨0, 1, by decide⟩ hcov10 h
    rw [hcard10] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G10 {1, 2, 5} ⟨0, 1, by decide⟩ hcovb10
    rw [hcard10] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({1, 2, 5} : Finset (Fin 8)).card = 3 := by decide
    rw [this] at h2
    omega

def ad11 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(2,4),(4,2),(3,5),(5,3),(6,7),(7,6)])

def G11 : SimpleGraph (Fin 8) where
  Adj i j := ad11 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst11 : DecidableRel G11.Adj := fun i j => inferInstanceAs (Decidable (ad11 i j = true))

theorem hacyc11 : G11.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun11 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G11.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (g && h)) = decide (∃ i j : Fin 8, G11.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard11 : G11.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov11 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G11.Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 2 4 (by decide)
  have e3 := hT 3 5 (by decide)
  have e4 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3 <;> rcases e4 with a4 | a4
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.insert_subset_iff.mpr ⟨a3, Finset.singleton_subset_iff.mpr a4⟩⟩⟩))

theorem hcovb11 : ∀ i j : Fin 8, G11.Adj i j → i ∈ ({0, 2, 3, 6} : Finset (Fin 8)) ∨ j ∈ ({0, 2, 3, 6} : Finset (Fin 8)) := by
  decide

theorem main11 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 6 && x 7)) s ↔ 9 ≤ s := by
  intro s
  rw [hfun11]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 4 s G11 hacyc11 ⟨0, 1, by decide⟩ hcov11 h
    rw [hcard11] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G11 {0, 2, 3, 6} ⟨0, 1, by decide⟩ hcovb11
    rw [hcard11] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 2, 3, 6} : Finset (Fin 8)).card = 4 := by decide
    rw [this] at h2
    omega

def ad12 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(4,5),(5,4),(4,6),(6,4),(5,7),(7,5)])

def G12 : SimpleGraph (Fin 8) where
  Adj i j := ad12 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst12 : DecidableRel G12.Adj := fun i j => inferInstanceAs (Decidable (ad12 i j = true))

theorem hacyc12 : G12.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun12 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G12.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (b && d) || (e && f) || (e && g) || (f && h)) = decide (∃ i j : Fin 8, G12.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard12 : G12.edgeFinset.card = 6 := by
  decide +kernel

theorem hcov12 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G12.Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
  intro T hT
  have e1 := hT 0 2 (by decide)
  have e2 := hT 1 3 (by decide)
  have e3 := hT 4 6 (by decide)
  have e4 := hT 5 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3 <;> rcases e4 with a4 | a4
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.insert_subset_iff.mpr ⟨a3, Finset.singleton_subset_iff.mpr a4⟩⟩⟩))

theorem hcovb12 : ∀ i j : Fin 8, G12.Adj i j → i ∈ ({0, 1, 4, 5} : Finset (Fin 8)) ∨ j ∈ ({0, 1, 4, 5} : Finset (Fin 8)) := by
  decide

theorem main12 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) s ↔ 9 ≤ s := by
  intro s
  rw [hfun12]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 4 s G12 hacyc12 ⟨0, 1, by decide⟩ hcov12 h
    rw [hcard12] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G12 {0, 1, 4, 5} ⟨0, 1, by decide⟩ hcovb12
    rw [hcard12] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 1, 4, 5} : Finset (Fin 8)).card = 4 := by decide
    rw [this] at h2
    omega

def ad13 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(4,5),(5,4),(6,7),(7,6)])

def G13 : SimpleGraph (Fin 8) where
  Adj i j := ad13 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst13 : DecidableRel G13.Adj := fun i j => inferInstanceAs (Decidable (ad13 i j = true))

theorem hacyc13 : G13.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun13 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G13.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (a && d) || (e && f) || (g && h)) = decide (∃ i j : Fin 8, G13.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard13 : G13.edgeFinset.card = 5 := by
  decide +kernel

theorem hcov13 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G13.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 4 5 (by decide)
  have e3 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.singleton_subset_iff.mpr a3⟩⟩))

theorem hcovb13 : ∀ i j : Fin 8, G13.Adj i j → i ∈ ({0, 4, 6} : Finset (Fin 8)) ∨ j ∈ ({0, 4, 6} : Finset (Fin 8)) := by
  decide

theorem main13 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 6 && x 7)) s ↔ 7 ≤ s := by
  intro s
  rw [hfun13]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 3 s G13 hacyc13 ⟨0, 1, by decide⟩ hcov13 h
    rw [hcard13] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G13 {0, 4, 6} ⟨0, 1, by decide⟩ hcovb13
    rw [hcard13] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 4, 6} : Finset (Fin 8)).card = 3 := by decide
    rw [this] at h2
    omega

def ad14 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(3,4),(4,3),(3,5),(5,3),(6,7),(7,6)])

def G14 : SimpleGraph (Fin 8) where
  Adj i j := ad14 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst14 : DecidableRel G14.Adj := fun i j => inferInstanceAs (Decidable (ad14 i j = true))

theorem hacyc14 : G14.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun14 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G14.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (d && e) || (d && f) || (g && h)) = decide (∃ i j : Fin 8, G14.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard14 : G14.edgeFinset.card = 5 := by
  decide +kernel

theorem hcov14 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G14.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 3 4 (by decide)
  have e3 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.singleton_subset_iff.mpr a3⟩⟩))

theorem hcovb14 : ∀ i j : Fin 8, G14.Adj i j → i ∈ ({0, 3, 6} : Finset (Fin 8)) ∨ j ∈ ({0, 3, 6} : Finset (Fin 8)) := by
  decide

theorem main14 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 6 && x 7)) s ↔ 7 ≤ s := by
  intro s
  rw [hfun14]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 3 s G14 hacyc14 ⟨0, 1, by decide⟩ hcov14 h
    rw [hcard14] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G14 {0, 3, 6} ⟨0, 1, by decide⟩ hcovb14
    rw [hcard14] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 3, 6} : Finset (Fin 8)).card = 3 := by decide
    rw [this] at h2
    omega

def ad15 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(1,3),(3,1),(4,5),(5,4),(6,7),(7,6)])

def G15 : SimpleGraph (Fin 8) where
  Adj i j := ad15 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst15 : DecidableRel G15.Adj := fun i j => inferInstanceAs (Decidable (ad15 i j = true))

theorem hacyc15 : G15.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun15 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G15.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (a && c) || (b && d) || (e && f) || (g && h)) = decide (∃ i j : Fin 8, G15.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard15 : G15.edgeFinset.card = 5 := by
  decide +kernel

theorem hcov15 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G15.Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
  intro T hT
  have e1 := hT 0 2 (by decide)
  have e2 := hT 1 3 (by decide)
  have e3 := hT 4 5 (by decide)
  have e4 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3 <;> rcases e4 with a4 | a4
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.insert_subset_iff.mpr ⟨a3, Finset.singleton_subset_iff.mpr a4⟩⟩⟩))

theorem hcovb15 : ∀ i j : Fin 8, G15.Adj i j → i ∈ ({0, 1, 4, 6} : Finset (Fin 8)) ∨ j ∈ ({0, 1, 4, 6} : Finset (Fin 8)) := by
  decide

theorem main15 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 6 && x 7)) s ↔ 8 ≤ s := by
  intro s
  rw [hfun15]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 4 s G15 hacyc15 ⟨0, 1, by decide⟩ hcov15 h
    rw [hcard15] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G15 {0, 1, 4, 6} ⟨0, 1, by decide⟩ hcovb15
    rw [hcard15] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 1, 4, 6} : Finset (Fin 8)).card = 4 := by decide
    rw [this] at h2
    omega

def ad16 (i j : Fin 8) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(2,3),(3,2),(4,5),(5,4),(6,7),(7,6)])

def G16 : SimpleGraph (Fin 8) where
  Adj i j := ad16 i j = true
  symm := by
    constructor
    decide
  loopless := by
    constructor
    decide

instance inst16 : DecidableRel G16.Adj := fun i j => inferInstanceAs (Decidable (ad16 i j = true))

theorem hacyc16 : G16.IsAcyclic := by
  apply acyc_of_lt
  decide

theorem hfun16 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5) || (x 6 && x 7)) = (fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, G16.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have key : ∀ a b c d e f g h : Bool, ((a && b) || (c && d) || (e && f) || (g && h)) = decide (∃ i j : Fin 8, G16.Adj i j ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) i = true ∧ (![a, b, c, d, e, f, g, h] : Fin 8 → Bool) j = true) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [key]
  rw [← hx]

theorem hcard16 : G16.edgeFinset.card = 4 := by
  decide +kernel

theorem hcov16 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, G16.Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
  intro T hT
  have e1 := hT 0 1 (by decide)
  have e2 := hT 2 3 (by decide)
  have e3 := hT 4 5 (by decide)
  have e4 := hT 6 7 (by decide)
  rcases e1 with a1 | a1 <;> rcases e2 with a2 | a2 <;> rcases e3 with a3 | a3 <;> rcases e4 with a4 | a4
  all_goals
    exact le_trans (by decide) (Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨a1, Finset.insert_subset_iff.mpr ⟨a2, Finset.insert_subset_iff.mpr ⟨a3, Finset.singleton_subset_iff.mpr a4⟩⟩⟩))

theorem hcovb16 : ∀ i j : Fin 8, G16.Adj i j → i ∈ ({0, 2, 4, 6} : Finset (Fin 8)) ∨ j ∈ ({0, 2, 4, 6} : Finset (Fin 8)) := by
  decide

theorem main16 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5) || (x 6 && x 7)) s ↔ 7 ≤ s := by
  intro s
  rw [hfun16]
  constructor
  · intro h
    have := H917.Forest.forest_bound 8 4 s G16 hacyc16 ⟨0, 1, by decide⟩ hcov16 h
    rw [hcard16] at this
    omega
  · intro hs
    have h := H917.EdgeUpper.edge_upper 8 G16 {0, 2, 4, 6} ⟨0, 1, by decide⟩ hcovb16
    rw [hcard16] at h
    obtain ⟨C, h1, h2, h3⟩ := h
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 2, 4, 6} : Finset (Fin 8)).card = 4 := by decide
    rw [this] at h2
    omega

end PEqualNP.Outside.L_meta_917_aux

open PEqualNP.Outside.L_meta_917_aux in
theorem PEqualNP.Outside.L_meta_917 : (∀ s1 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x1 : Fin 8 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 6 && x1 7)) s1 ↔ 7 ≤ s1) ∧ (∀ s2 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x2 : Fin 8 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 5 && x2 6) || (x2 5 && x2 7)) s2 ↔ 7 ≤ s2) ∧ (∀ s3 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x3 : Fin 8 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 0 && x3 3) || (x3 0 && x3 4) || (x3 1 && x3 5) || (x3 6 && x3 7)) s3 ↔ 8 ≤ s3) ∧ (∀ s4 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x4 : Fin 8 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 4 && x4 5) || (x4 4 && x4 6) || (x4 4 && x4 7)) s4 ↔ 7 ≤ s4) ∧ (∀ s5 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x5 : Fin 8 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 1 && x5 3) || (x5 1 && x5 4) || (x5 2 && x5 5) || (x5 6 && x5 7)) s5 ↔ 8 ≤ s5) ∧ (∀ s6 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x6 : Fin 8 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 0 && x6 3) || (x6 1 && x6 4) || (x6 1 && x6 5) || (x6 6 && x6 7)) s6 ↔ 8 ≤ s6) ∧ (∀ s7 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x7 : Fin 8 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 0 && x7 3) || (x7 1 && x7 4) || (x7 5 && x7 6) || (x7 5 && x7 7)) s7 ↔ 8 ≤ s7) ∧ (∀ s8 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x8 : Fin 8 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 0 && x8 3) || (x8 4 && x8 5) || (x8 4 && x8 6) || (x8 5 && x8 7)) s8 ↔ 8 ≤ s8) ∧ (∀ s9 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x9 : Fin 8 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 1 && x9 4) || (x9 2 && x9 5) || (x9 6 && x9 7)) s9 ↔ 9 ≤ s9) ∧ (∀ s10 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x10 : Fin 8 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 1 && x10 3) || (x10 2 && x10 4) || (x10 5 && x10 6) || (x10 5 && x10 7)) s10 ↔ 8 ≤ s10) ∧ (∀ s11 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x11 : Fin 8 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 1 && x11 3) || (x11 2 && x11 4) || (x11 3 && x11 5) || (x11 6 && x11 7)) s11 ↔ 9 ≤ s11) ∧ (∀ s12 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x12 : Fin 8 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 1 && x12 3) || (x12 4 && x12 5) || (x12 4 && x12 6) || (x12 5 && x12 7)) s12 ↔ 9 ≤ s12) ∧ (∀ s13 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x13 : Fin 8 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 4 && x13 5) || (x13 6 && x13 7)) s13 ↔ 7 ≤ s13) ∧ (∀ s14 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x14 : Fin 8 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 3 && x14 4) || (x14 3 && x14 5) || (x14 6 && x14 7)) s14 ↔ 7 ≤ s14) ∧ (∀ s15 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x15 : Fin 8 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 4 && x15 5) || (x15 6 && x15 7)) s15 ↔ 8 ≤ s15) ∧ (∀ s16 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x16 : Fin 8 → Bool => (x16 0 && x16 1) || (x16 2 && x16 3) || (x16 4 && x16 5) || (x16 6 && x16 7)) s16 ↔ 7 ≤ s16) :=
  ⟨main1, main2, main3, main4, main5, main6, main7, main8, main9, main10, main11, main12, main13, main14, main15, main16⟩
