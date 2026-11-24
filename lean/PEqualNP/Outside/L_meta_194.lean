import Mathlib
import PEqualNP.Defs

-- Circuit reduction adapted from the checked L-meta-193 proof.
namespace PEqualNP.Outside.L_meta_194_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

abbrev Stat := Sum Bool ℕ

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

def reader (n h : ℕ) (p : Gate × ℕ) : Bool :=
  decide (h < n + p.2) && (normGate p.1).inputs.contains h

theorem savings (n m h : ℕ) (gs : List Gate) (j : ℕ) (acc : List Stat × List Gate)
    (ok : ∀ g ∈ gs, Ok g) (hh : h < acc.1.length)
    (fixed : acc.1.getD h (.inl false) = .inl false) :
    (elim m (gs.map normGate) acc).2.length + (gs.zipIdx j).countP (reader n h)
      ≤ acc.2.length + gs.length := by
  induction gs generalizing acc j with
  | nil => simp [elim]
  | cons g gs ih =>
    let a := elimStep m acc (normGate g)
    have tail := ih (j+1) a (fun g hg => ok g (by simp [hg]))
      (by simp [a, elimStep]; omega)
      (by change (acc.1 ++ [_]).getD h _ = _; rw [List.getD_append _ _ _ _ hh, fixed])
    change (elim m (gs.map normGate) a).2.length + _ ≤ _
    rw [List.zipIdx_cons, List.countP_cons, List.length_cons]
    let r := simplify (normGate g).op (m + acc.2.length)
      ((normGate g).inputs.map fun i => acc.1.getD i (.inl false))
    have ha : a.2.length = acc.2.length + r.1.toList.length := List.length_append
    by_cases hit : reader n h (g,j) = true
    · have mem : h ∈ (normGate g).inputs := by simpa [reader] using (Bool.and_eq_true_iff.mp hit).2
      have ng := normGate_nok g (ok g (by simp))
      have zero : r.1 = none := simplify_count _ _ _ ng.1.1
        (by simpa using ng.1.2) (fun e => by simpa using ng.2 e)
        ⟨false, List.mem_map.mpr ⟨h, mem, fixed⟩⟩
      simp [zero] at ha
      simp [hit]; omega
    · have := toList_length_le r.1
      simp [hit]; omega

def seed (m h : ℕ) : List Stat :=
  List.ofFn fun i : Fin m => if i.val = h then .inl false else .inr i.val

theorem seed_inv (w : List Bool) (m h : ℕ) (hw : w.length = m)
    (hz : w.getD h false = false) : Inv m w w (seed m h, []) := by
  refine ⟨by simp [seed, hw], fun i => ?_⟩
  by_cases hi : i < m
  · by_cases e : i = h
    · subst i; simpa [seed, hi, Stat.Valid, Stat.val] using hz
    · simp [seed, hi, e, Stat.Valid, Stat.val, wiresFrom]
  · have : m ≤ i := by omega
    simpa [seed, hi, Stat.Valid, Stat.val] using (List.getD_eq_default w false (by omega : w.length ≤ i))

def finish (h : ℕ) : Stat → Gate
  | .inl true => ⟨.and, []⟩
  | .inl false => ⟨.or, [h]⟩
  | .inr j => ⟨.or, [h,j]⟩

theorem finish_ok (h : ℕ) (s : Stat) : Ok (finish h s) := by
  cases s with
  | inl b => cases b <;> simp [finish, Ok]
  | inr j => simp [finish, Ok]

theorem finish_eval (w : List Bool) (h : ℕ) (s : Stat) :
    (wiresFrom [finish h s] w).getD w.length false = (w.getD h false || s.val w) := by
  cases s with
  | inl b => cases b <;> simp [finish, wiresFrom, GateOp.eval, Stat.val]
  | inr j => simp [finish, wiresFrom, GateOp.eval, Stat.val]

private theorem reduction : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (h : ℕ), PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains h) ≤ C.size + 1 := by
  intro n C h ok absorbs
  have form (g : Gate) : (GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs
      (g.inputs.take 1) (fun _ => g.inputs) g.inputs) = (normGate g).inputs := by
    cases g with | mk op ins => cases op <;> rfl
  simp_rw [form]
  change ∃ D, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
    D.size + C.gates.zipIdx.countP (reader n h) ≤ C.size + 1
  by_cases existsH : h < n + C.gates.length
  swap
  · refine ⟨C, ok, rfl, ?_⟩
    have z : C.gates.zipIdx.countP (reader n h) = 0 := by
      apply List.countP_eq_zero.mpr
      intro p hp
      have := List.snd_lt_of_mem_zipIdx hp
      simp [reader, show ¬h < n + p.2 by omega]
    omega
  let pre := C.gates.take (h+1-n)
  let rest := C.gates.drop (h+1-n)
  have splitG : pre ++ rest = C.gates := List.take_append_drop ..
  let m := n + pre.length
  have hpLen : pre.length = min (h+1-n) C.gates.length := List.length_take ..
  have hm : h < m := by dsimp [m]; omega
  let init : List Stat × List Gate := (seed m h, [])
  let pass := elim m (rest.map normGate) init
  let s := pass.1.getD C.output (.inl false)
  let D : Circuit := ⟨(pre ++ pass.2) ++ [finish h s], m + pass.2.length⟩
  have preOk (g) (hg : g ∈ pre) : Ok g := ok g (splitG ▸ List.mem_append_left _ hg)
  have restOk (g) (hg : g ∈ rest) : Ok g := ok g (splitG ▸ List.mem_append_right _ hg)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ (pre ++ pass.2) ++ [finish h s] at hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hp | hr) | rfl)
    · exact preOk g hp
    · exact elim_ok m _ init (by simp [init]) g hr
    · exact finish_ok h s
  · funext x
    let y := List.ofFn x
    let w := wiresFrom pre y
    let v := wiresFrom pass.2 w
    have lw : w.length = m := by simp [w, y, length_wiresFrom, m]
    have lv : v.length = m + pass.2.length := by simp [v, length_wiresFrom, lw]
    have hh : h < w.length := lw ▸ hm
    have old : C.wires y = wiresFrom rest w := by rw [wires_eq, ← splitG, wiresFrom_append]
    have origH : (C.wires y).getD h false = w.getD h false := by rw [old, getD_wiresFrom _ _ _ hh]
    have out : circuitFun n D x = (w.getD h false || s.val v) := by
      change (wiresFrom ((pre ++ pass.2) ++ [finish h s]) y).getD (m + pass.2.length) false = _
      rw [wiresFrom_append, wiresFrom_append]
      change (wiresFrom [finish h s] v).getD _ false = _
      rw [← lv, finish_eval, getD_wiresFrom _ _ _ hh]
    rw [out]
    cases hc : w.getD h false with
    | true => simpa using (absorbs x (origH.trans hc)).symm
    | false =>
      have hi := inv_elim m w lw (rest.map normGate) w init
        (by intro g hg; obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
            exact (normGate_nok _ (restOk _ hg')).1)
        (seed_inv w m h lw hc)
      have eq := (hi.2 C.output).2
      rw [wiresFrom_norm, ← old] at eq
      simpa [s, v, pass, circuitFun, Circuit.eval, y] using eq
  · have zero : pre.zipIdx.countP (reader n h) = 0 := by
      apply List.countP_eq_zero.mpr
      intro p hp
      have := List.snd_lt_of_mem_zipIdx hp
      simp [reader, show ¬ h < n + p.2 by omega]
    have save := savings n m h rest pre.length init restOk
      (by simpa [init, seed] using hm) (by simp [init, seed, hm])
    change pass.2.length + _ ≤ [].length + rest.length at save
    change ((pre ++ pass.2) ++ [finish h s]).length + _ ≤ C.gates.length + 1
    rw [← splitG, List.zipIdx_append, List.countP_append, zero]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at *
    omega

end PEqualNP.Outside.L_meta_194_aux

open PEqualNP.Outside.L_meta_194_aux

theorem PEqualNP.Outside.L_meta_194 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (h : ℕ), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains h) ≤ 1 := by
  intro n C h minimal absorbs
  obtain ⟨D, valid, same, bound⟩ := reduction n C h minimal.1 absorbs
  have least := minimal.2 D valid same
  omega
