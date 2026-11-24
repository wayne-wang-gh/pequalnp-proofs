import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1708_aux

-- Constant propagation adapted from Federico Devigili, L-meta-726, PR 984.

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

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
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  all_goals simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
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

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

theorem elim_count (n k : ℕ) (b : Bool) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → k < acc.1.length → acc.1.getD k (Sum.inl false) = Sum.inl b →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1
        · simpa using hnok.2
        · exact ⟨b, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, if_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false]
      simp
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

def initStats (n : ℕ) (v : Fin n) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => if i = v then Sum.inl b else Sum.inr i)

theorem inv_init (n : ℕ) (v : Fin n) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y v b)) (initStats n v b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · by_cases hv : (⟨i, hlt⟩ : Fin n) = v
    · subst hv
      simp [initStats, hlt, Stat.Valid, Stat.val]
    · simp [initStats, hlt, hv, Stat.Valid, Stat.val, wiresFrom, Function.update_of_ne hv]
  · rw [List.getD_eq_default _ _ (by simp [initStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem sum_eq_countP (l : List Gate) (k : ℕ) :
    (∑ i : Fin l.length, if k ∈ (l.get i).inputs then 1 else 0)
      = l.countP (fun g => decide (k ∈ g.inputs)) := by
  induction l with
  | nil => simp
  | cons g l ih =>
    show (∑ i : Fin (l.length + 1), if k ∈ ((g :: l).get i).inputs then 1 else 0) = _
    rw [Fin.sum_univ_succ, List.countP_cons]
    simp at ih
    by_cases h : k ∈ g.inputs <;> simp [h] <;> omega

theorem countP_eq_card (l : List Gate) (k : ℕ) :
    (Finset.univ.filter (fun j : Fin l.length => k ∈ (l.get j).inputs)).card
      = l.countP (fun g => decide (k ∈ g.inputs)) := by
  rw [Finset.card_filter]
  exact sum_eq_countP l k

theorem pinCircuit : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool), PEqualNP.MetaComplexity.Monotone2 C → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  intro n C v b hmono hy
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    simpa using h1
  set acc := elim n C.gates (initStats n v b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn (Function.update y v b))) acc := by
    intro y
    exact inv_elim n _ (by simp) C.gates _ _ hok (inv_init n v b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = C.eval (List.ofFn (Function.update y v b)) := by
    intro y
    exact ((hinv y).2 C.output).2
  have hcnt := elim_count n v.val b C.gates (initStats n v b, []) hok (by simp [initStats])
    (by simp [initStats])
  rw [← hacc] at hcnt
  simp only [List.length_nil, zero_add] at hcnt
  have hmD : ∀ out : ℕ, PEqualNP.MetaComplexity.Monotone2 ⟨acc.2, out⟩ := by
    intro out g hg
    obtain ⟨h1, h2⟩ := elim_ok n C.gates _ (by simp) g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h <;> simp [h]
  have hsz : ∀ out : ℕ, (⟨acc.2, out⟩ : PEqualNP.CircuitLowerBounds.Circuit).size
      + (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card
      ≤ C.size := by
    intro out
    rw [countP_eq_card]
    exact hcnt
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    cases c with
    | true =>
      exfalso
      obtain ⟨y, hy⟩ := hy
      have := hval y
      rw [hst] at this
      rw [← this] at hy
      exact absurd hy (by simp [Stat.val])
    | false =>
      refine ⟨⟨acc.2, n + acc.2.length⟩, hmD _, hsz _, ?_⟩
      intro x
      rw [← hval x, hst]
      show (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = false
      rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp)]
  | inr j =>
    refine ⟨⟨acc.2, j⟩, hmD _, hsz _, ?_⟩
    intro x
    have := hval x
    rw [hst] at this
    exact this

theorem wiresFrom_agree (gs : List Gate) (k : ℕ)
    (hread : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ a b : List Bool, a.length = b.length →
    (∀ i, i ≠ k → a.getD i false = b.getD i false) →
    ∀ i, i ≠ k → (wiresFrom gs a).getD i false = (wiresFrom gs b).getD i false := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    have hv : g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (fun e => hread g List.mem_cons_self (e ▸ hi))
    apply ih (fun g' hg' => hread g' (List.mem_cons_of_mem _ hg'))
      (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) (by simp [hl])
    intro i hik
    by_cases hil : i = a.length
    · rw [hil, getD_snoc_eq, hl, getD_snoc_eq]
      exact hv
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      exact h i hik

theorem input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (v : Fin n) :
    (C.wires (List.ofFn x)).getD v.val false = x v := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn x)
  change (wiresFrom C.gates (List.ofFn x)).getD v.val false = x v
  rw [ht, List.getD_append _ _ _ _ (by simpa using v.isLt)]
  simp

theorem singleton_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    decide (∃ a b : Fin n, G.Adj a b ∧ decide (a = v) = true ∧ decide (b = v) = true) = false := by
  simp

theorem reads_vertex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (hdeg : 0 < G.degree v) (C : Circuit)
    (hfun : PEqualNP.MetaComplexity.circuitFun n C =
      fun x : Fin n → Bool => decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) :
    ∃ j : Fin C.gates.length, v.val ∈ (C.gates.get j).inputs := by
  classical
  have hev (x : Fin n → Bool) : C.eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) := congrFun hfun x
  have hout : C.output ≠ v.val := by
    intro heq
    have h := hev (fun p => decide (p = v))
    rw [singleton_false] at h
    unfold Circuit.eval at h
    rw [heq, input_value] at h
    simp at h
  by_contra hnone
  have hread : ∀ g ∈ C.gates, v.val ∉ g.inputs := by
    intro g hg hv
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
    exact hnone ⟨j, hj ▸ hv⟩
  obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj v).mp hdeg
  have hne : v ≠ u := G.ne_of_adj hu
  let x : Fin n → Bool := fun p => decide (p = v ∨ p = u)
  let y : Fin n → Bool := fun p => decide (p = u)
  have hx : C.eval (List.ofFn x) = true := by
    rw [hev]
    apply decide_eq_true
    exact ⟨v, u, hu, by simp [x], by simp [x]⟩
  have hy : C.eval (List.ofFn y) = false := by
    rw [hev]
    exact singleton_false G u
  have hi : ∀ i, i ≠ v.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
    intro i hiv
    by_cases hin : i < n
    · have hfin : (⟨i, hin⟩ : Fin n) ≠ v := fun eq => hiv (congrArg Fin.val eq)
      simp [x, y, hin, hfin]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have h := wiresFrom_agree C.gates v.val hread (List.ofFn x) (List.ofFn y) (by simp) hi C.output hout
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at h
  rw [hx, hy] at h
  contradiction

theorem peel {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (hdeg : 0 < G.degree v) (C : Circuit)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hfun : PEqualNP.MetaComplexity.circuitFun n C =
      fun x : Fin n → Bool => decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size < C.size ∧
      PEqualNP.MetaComplexity.circuitFun n D =
      fun x : Fin n → Bool => decide (∃ a b, (G.deleteIncidenceSet v).Adj a b ∧ x a = true ∧ x b = true) := by
  classical
  have hev (x : Fin n → Bool) : C.eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) := congrFun hfun x
  obtain ⟨D, hmD, hsize, hD⟩ := pinCircuit n C v false hmono (by
    refine ⟨fun _ => false, ?_⟩
    rw [hev]
    simp)
  obtain ⟨j, hj⟩ := reads_vertex G v hdeg C hfun
  have hpos : 0 < (Finset.univ.filter (fun j : Fin C.gates.length =>
      v.val ∈ (C.gates.get j).inputs)).card := Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  refine ⟨D, hmD, by omega, ?_⟩
  funext x
  change D.eval (List.ofFn x) = _
  rw [hD, hev]
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hav : a ≠ v := by intro h; subst a; simp at ha
    have hbv : b ≠ v := by intro h; subst b; simp at hb
    exact ⟨a, b, SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hab, hav, hbv⟩,
      by simpa [Function.update_of_ne hav] using ha,
      by simpa [Function.update_of_ne hbv] using hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, hav, hbv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hab
    exact ⟨a, b, hab, by simpa [Function.update_of_ne hav] using ha,
      by simpa [Function.update_of_ne hbv] using hb⟩

end PEqualNP.Outside.L_meta_1708_aux

theorem PEqualNP.Outside.L_meta_1708 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Fin x1), (0 : ℕ) < x2.degree x4 → x2.degree x4 ≤ (2 : ℕ) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x1 x7 = fun (x9 : Fin x1 → Bool) => Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size < x7.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = fun (x11 : Fin x1 → Bool) => Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x1), (x2.deleteIncidenceSet x4).Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) := by
  intro n G inst v hdeg _ C hm hf
  exact PEqualNP.Outside.L_meta_1708_aux.peel G v hdeg C hm hf
