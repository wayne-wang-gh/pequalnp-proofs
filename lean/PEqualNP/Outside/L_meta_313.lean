import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_313

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

lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := elimPass_len_lt m k gs (elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
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

lemma hardwire_prefix_nonconst {n k s : ℕ}
    {F : (Fin (n + k) → Bool) → Bool} {g : (Fin k → Bool) → Bool}
    (hC : HasCircuitSize (n + k) F s)
    (hFg : ∀ x : Fin (n + k) → Bool, F x = g (fun j : Fin k => x (Fin.natAdd n j)))
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y') :
    HasCircuitSize k g s := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  set init : List (Bool ⊕ ℕ) :=
    List.replicate n (Sum.inl false) ++ List.ofFn (fun j : Fin k => Sum.inr (j : ℕ)) with hinit
  set acc := elimPass k gs (init, []) with hacc
  have hinv : ∀ y : Fin k → Bool,
      ElimInv k (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.append (fun _ : Fin n => false) y : Fin (n + k) → Bool)))
        acc := by
    intro y
    apply elimInv_pass k (List.ofFn y) gs _ (init, []) (fun g hg => (hnok g hg).1)
    refine ⟨by simp, by simp [hinit], ?_⟩
    intro i
    by_cases h1 : i < n
    · have hi' : i < n + k := by omega
      have hget : init.getD i (Sum.inl false) = Sum.inl false := by
        rw [hinit, List.getD_eq_getElem _ _ (by simp; omega),
            List.getElem_append_left (by simp; exact h1)]
        simp
      rw [hget]
      refine ⟨trivial, ?_⟩
      simp only [statVal]
      rw [ofFn_getD_lt _ _ _ hi']
      have hcast : (⟨i, hi'⟩ : Fin (n + k)) = Fin.castAdd k ⟨i, h1⟩ := rfl
      rw [hcast, Fin.append_left]
    · by_cases h2 : i < n + k
      · have hsub : i - n < k := by omega
        have hget : init.getD i (Sum.inl false) = Sum.inr (i - n) := by
          rw [hinit, List.getD_eq_getElem _ _ (by simp; omega),
              List.getElem_append_right (by simp; omega)]
          simp [List.getElem_ofFn]
        rw [hget]
        refine ⟨by simp [statValid]; exact hsub, ?_⟩
        simp only [statVal, wiresFrom_nil]
        rw [ofFn_getD_lt _ _ _ hsub, ofFn_getD_lt _ _ _ h2]
        have hnat : (⟨i, h2⟩ : Fin (n + k)) = Fin.natAdd n ⟨i - n, hsub⟩ := by
          ext; simp [Fin.natAdd]; omega
        rw [hnat, Fin.append_right]
      · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
            List.getD_eq_default _ _ (by simp; omega)]
        exact ⟨trivial, rfl⟩
  have hval : ∀ y : Fin k → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = g y := by
    intro y
    rw [((hinv y).2.2 C.output).2, hgs, wiresFrom_norm]
    have h1 := hev (Fin.append (fun _ : Fin n => false) y)
    have h2 := hFg (Fin.append (fun _ : Fin n => false) y)
    have heq : (fun j : Fin k => (Fin.append (fun _ : Fin n => false) y : Fin (n + k) → Bool)
        (Fin.natAdd n j)) = y := by
      funext j; exact Fin.append_right _ _ j
    rw [heq] at h2
    exact h1.trans h2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y, y', hne⟩ := hg_nc
    have hy := hval y; have hy' := hval y'
    rw [hst] at hy hy'
    exact absurd (hy.symm.trans hy') hne
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elimPass_ok k gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s
      have := elimPass_len k gs (init, [])
      rw [← hacc] at this
      have hlen : gs.length = C.gates.length := by simp [hgs]
      have hsz' : C.gates.length ≤ s := hsz
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

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

def forestFun {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool) (x : Fin (n + k) → Bool) : Bool :=
  decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨
    ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) &&
  g (fun j : Fin k => x (Fin.natAdd n j))

lemma exists_false_true_of_nonconst {k : ℕ} {g : (Fin k → Bool) → Bool}
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y') :
    (∃ y₀, g y₀ = false) ∧ (∃ y₁, g y₁ = true) := by
  obtain ⟨y, y', hne⟩ := hg_nc
  cases hy : g y <;> cases hy' : g y'
  · exact absurd (hy.trans hy'.symm) hne
  · exact ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
  · exact ⟨⟨y', hy'⟩, ⟨y, hy⟩⟩
  · exact absurd (hy.trans hy'.symm) hne

lemma forestFun_nonconst {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hAct : A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) :
    ∃ x x' : Fin (n + k) → Bool, forestFun G A g x ≠ forestFun G A g x' := by
  obtain ⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩ := exists_false_true_of_nonconst hg_nc
  rcases hAct with hA | ⟨u, v, huv⟩
  · obtain ⟨a, ha⟩ := hA
    refine ⟨Fin.append (fun i : Fin n => decide (i = a)) y₀,
      Fin.append (fun i : Fin n => decide (i = a)) y₁, ?_⟩
    have hF : decide ((∃ b ∈ A, decide (b = a) = true) ∨
        ∃ u v : Fin n, G.Adj u v ∧ decide (u = a) = true ∧ decide (v = a) = true) = true := by
      apply decide_eq_true
      exact Or.inl ⟨a, ha, by simp⟩
    have h0 : forestFun G A g (Fin.append (fun i : Fin n => decide (i = a)) y₀) = false := by
      simp only [forestFun, Fin.append_left, Fin.append_right, hF, Bool.true_and, hy₀]
    have h1 : forestFun G A g (Fin.append (fun i : Fin n => decide (i = a)) y₁) = true := by
      simp only [forestFun, Fin.append_left, Fin.append_right, hF, Bool.true_and, hy₁]
    rw [h0, h1]
    decide
  · refine ⟨Fin.append (fun i : Fin n => decide (i = u ∨ i = v)) y₀,
      Fin.append (fun i : Fin n => decide (i = u ∨ i = v)) y₁, ?_⟩
    have hF : decide ((∃ b ∈ A, decide (b = u ∨ b = v) = true) ∨
        ∃ u' v' : Fin n, G.Adj u' v' ∧ decide (u' = u ∨ u' = v) = true ∧
          decide (v' = u ∨ v' = v) = true) = true := by
      apply decide_eq_true
      refine Or.inr ⟨u, v, huv, by simp, by simp⟩
    have h0 : forestFun G A g (Fin.append (fun i : Fin n => decide (i = u ∨ i = v)) y₀) = false := by
      simp only [forestFun, Fin.append_left, Fin.append_right, hF, Bool.true_and, hy₀]
    have h1 : forestFun G A g (Fin.append (fun i : Fin n => decide (i = u ∨ i = v)) y₁) = true := by
      simp only [forestFun, Fin.append_left, Fin.append_right, hF, Bool.true_and, hy₁]
    rw [h0, h1]
    decide

lemma forestFun_update_A_true {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (a : Fin n) (ha : a ∈ A) :
    (fun x => forestFun G A g (Function.update x (Fin.castAdd k a) true)) =
      fun x => g (fun j : Fin k => x (Fin.natAdd n j)) := by
  funext x
  simp only [forestFun]
  have ht : (∃ b ∈ A, Function.update x (Fin.castAdd k a) true (Fin.castAdd k b) = true) :=
    ⟨a, ha, by simp⟩
  have hg : (fun j : Fin k => Function.update x (Fin.castAdd k a) true (Fin.natAdd n j)) =
      (fun j : Fin k => x (Fin.natAdd n j)) := by
    funext j
    apply Function.update_of_ne
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd] at hval
    omega
  simp [ht, hg]

lemma forestFun_update_A {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (a : Fin n) (ha_iso : ∀ v : Fin n, ¬ G.Adj a v) :
    (fun x => forestFun G A g (Function.update x (Fin.castAdd k a) false)) =
      forestFun G (A.erase a) g := by
  funext x
  simp only [forestFun]
  have hnat : (fun j : Fin k => Function.update x (Fin.castAdd k a) false (Fin.natAdd n j)) =
      (fun j : Fin k => x (Fin.natAdd n j)) := by
    funext j
    apply Function.update_of_ne
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd] at hval
    omega
  rw [hnat]
  congr 1
  apply decide_eq_decide.2
  constructor
  · rintro (⟨b, hb, hbx⟩ | ⟨u, v, huv, hux, hvx⟩)
    · left
      have hba : b ≠ a := by
        intro h; subst h; simp at hbx
      refine ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, ?_⟩
      have hne : Fin.castAdd k b ≠ Fin.castAdd k a := fun h => hba (Fin.castAdd_injective n k h)
      rwa [Function.update_of_ne hne] at hbx
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      have hne1 : Fin.castAdd k u ≠ Fin.castAdd k a := fun h => hua (Fin.castAdd_injective n k h)
      have hne2 : Fin.castAdd k v ≠ Fin.castAdd k a := fun h => hva (Fin.castAdd_injective n k h)
      rw [Function.update_of_ne hne1] at hux
      rw [Function.update_of_ne hne2] at hvx
      exact ⟨u, v, huv, hux, hvx⟩
  · rintro (⟨b, hb, hbx⟩ | ⟨u, v, huv, hux, hvx⟩)
    · left
      obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
      have hne : Fin.castAdd k b ≠ Fin.castAdd k a := fun h => hba (Fin.castAdd_injective n k h)
      exact ⟨b, hbA, by rw [Function.update_of_ne hne]; exact hbx⟩
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      have hne1 : Fin.castAdd k u ≠ Fin.castAdd k a := fun h => hua (Fin.castAdd_injective n k h)
      have hne2 : Fin.castAdd k v ≠ Fin.castAdd k a := fun h => hva (Fin.castAdd_injective n k h)
      exact ⟨u, v, huv, by rw [Function.update_of_ne hne1]; exact hux,
        by rw [Function.update_of_ne hne2]; exact hvx⟩

lemma forestFun_update_leaf_false {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin k → Bool) → Bool) (ℓ p : Fin n) (hleaf : ∀ w, G.Adj ℓ w → w = p)
    [DecidableRel (G.deleteEdges {s(ℓ, p)}).Adj] :
    (fun x => forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) false)) =
      forestFun (G.deleteEdges {s(ℓ, p)}) ∅ g := by
  funext x
  simp only [forestFun]
  have hnat : (fun j : Fin k => Function.update x (Fin.castAdd k ℓ) false (Fin.natAdd n j)) =
      (fun j : Fin k => x (Fin.natAdd n j)) := by
    funext j
    apply Function.update_of_ne
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd] at hval
    omega
  rw [hnat]
  congr 1
  apply decide_eq_decide.2
  simp only [Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨u, v, huv, hux, hvx⟩
    have huℓ : u ≠ ℓ := by intro h; subst h; simp at hux
    have hvℓ : v ≠ ℓ := by intro h; subst h; simp at hvx
    have hne1 : Fin.castAdd k u ≠ Fin.castAdd k ℓ := fun h => huℓ (Fin.castAdd_injective n k h)
    have hne2 : Fin.castAdd k v ≠ Fin.castAdd k ℓ := fun h => hvℓ (Fin.castAdd_injective n k h)
    rw [Function.update_of_ne hne1] at hux
    rw [Function.update_of_ne hne2] at hvx
    refine ⟨u, v, SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩, hux, hvx⟩
    intro heq
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huℓ rfl
    · exact hvℓ rfl
  · rintro ⟨u, v, hadj, hux, hvx⟩
    obtain ⟨huv, hne⟩ := SimpleGraph.deleteEdges_adj.1 hadj
    simp only [Set.mem_singleton_iff] at hne
    have huℓ : u ≠ ℓ := by
      intro h; subst h
      have hv_eq : v = p := hleaf v huv
      subst hv_eq
      exact hne rfl
    have hvℓ : v ≠ ℓ := by
      intro h; subst h
      have hu_eq : u = p := hleaf u huv.symm
      subst hu_eq
      exact hne Sym2.eq_swap
    have hne1 : Fin.castAdd k u ≠ Fin.castAdd k ℓ := fun h => huℓ (Fin.castAdd_injective n k h)
    have hne2 : Fin.castAdd k v ≠ Fin.castAdd k ℓ := fun h => hvℓ (Fin.castAdd_injective n k h)
    exact ⟨u, v, huv, by rw [Function.update_of_ne hne1]; exact hux,
      by rw [Function.update_of_ne hne2]; exact hvx⟩

lemma forestFun_update_leaf_true {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin k → Bool) → Bool) (ℓ p : Fin n) (hlp : G.Adj ℓ p)
    (hleaf : ∀ w, G.Adj ℓ w → w = p) [DecidableRel (deleteVertexEdges G p).Adj] :
    (fun x => forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) true)) =
      forestFun (deleteVertexEdges G p) {p} g := by
  funext x
  simp only [forestFun]
  have hnat : (fun j : Fin k => Function.update x (Fin.castAdd k ℓ) true (Fin.natAdd n j)) =
      (fun j : Fin k => x (Fin.natAdd n j)) := by
    funext j
    apply Function.update_of_ne
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd] at hval
    omega
  rw [hnat]
  congr 1
  apply decide_eq_decide.2
  simp only [Finset.notMem_empty, false_and, exists_false, false_or, Finset.mem_singleton,
    exists_eq_left]
  have hpneℓ : Fin.castAdd k p ≠ Fin.castAdd k ℓ :=
    fun h => hlp.ne.symm (Fin.castAdd_injective n k h)
  constructor
  · rintro ⟨u, v, huv, hux, hvx⟩
    by_cases hup : u = p
    · subst hup
      rw [Function.update_of_ne hpneℓ] at hux
      exact Or.inl hux
    · by_cases hvp : v = p
      · subst hvp
        rw [Function.update_of_ne hpneℓ] at hvx
        exact Or.inl hvx
      · right
        have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
        have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
        have hne1 : Fin.castAdd k u ≠ Fin.castAdd k ℓ := fun h => huℓ (Fin.castAdd_injective n k h)
        have hne2 : Fin.castAdd k v ≠ Fin.castAdd k ℓ := fun h => hvℓ (Fin.castAdd_injective n k h)
        rw [Function.update_of_ne hne1] at hux
        rw [Function.update_of_ne hne2] at hvx
        exact ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩
  · rintro (hpx | ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩)
    · exact ⟨ℓ, p, hlp, by simp, by rw [Function.update_of_ne hpneℓ]; exact hpx⟩
    · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
      have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
      have hne1 : Fin.castAdd k u ≠ Fin.castAdd k ℓ := fun h => huℓ (Fin.castAdd_injective n k h)
      have hne2 : Fin.castAdd k v ≠ Fin.castAdd k ℓ := fun h => hvℓ (Fin.castAdd_injective n k h)
      exact ⟨u, v, huv, by rw [Function.update_of_ne hne1]; exact hux,
        by rw [Function.update_of_ne hne2]; exact hvx⟩

lemma forestFun_dep_A {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y') (a : Fin n) (ha : a ∈ A) :
    ∃ x : Fin (n + k) → Bool,
      forestFun G A g (Function.update x (Fin.castAdd k a) false) ≠
      forestFun G A g (Function.update x (Fin.castAdd k a) true) := by
  obtain ⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩ := exists_false_true_of_nonconst hg_nc
  refine ⟨Fin.append (fun _ : Fin n => false) y₁, ?_⟩
  have h0 : forestFun G A g
      (Function.update (Fin.append (fun _ : Fin n => false) y₁) (Fin.castAdd k a) false) = false := by
    have hupd : Function.update (Fin.append (fun _ : Fin n => false) y₁) (Fin.castAdd k a) false =
        Fin.append (fun _ : Fin n => false) y₁ := by
      funext i
      by_cases hi : i = Fin.castAdd k a
      · subst hi; simp [Fin.append_left]
      · rw [Function.update_of_ne hi]
    rw [hupd]
    simp only [forestFun, Fin.append_left, Fin.append_right]
    have hnoA : ¬ ∃ b ∈ A, false = true := by simp
    have hnoE : ¬ ∃ u v : Fin n, G.Adj u v ∧ false = true ∧ false = true := by simp
    simp [hnoA, hnoE]
  have h1 : forestFun G A g
      (Function.update (Fin.append (fun _ : Fin n => false) y₁) (Fin.castAdd k a) true) = true := by
    simp only [forestFun]
    have ht : (∃ b ∈ A, Function.update (Fin.append (fun _ : Fin n => false) y₁)
        (Fin.castAdd k a) true (Fin.castAdd k b) = true) := ⟨a, ha, by simp⟩
    have hg : (fun j : Fin k => Function.update (Fin.append (fun _ : Fin n => false) y₁)
        (Fin.castAdd k a) true (Fin.natAdd n j)) = y₁ := by
      funext j
      rw [Function.update_of_ne]
      · simp [Fin.append_right]
      · intro h
        have hval := congrArg Fin.val h
        simp [Fin.castAdd, Fin.natAdd] at hval
        omega
    simp [ht, hg, hy₁]
  rw [h0, h1]
  decide

lemma forestFun_dep_edge {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin k → Bool) → Bool) (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) :
    ∃ x : Fin (n + k) → Bool,
      forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) false) ≠
      forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) true) := by
  obtain ⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩ := exists_false_true_of_nonconst hg_nc
  set x0 : Fin (n + k) → Bool := Fin.append (fun i : Fin n => decide (i = p)) y₁ with hx0
  refine ⟨x0, ?_⟩
  have hpneℓ : Fin.castAdd k p ≠ Fin.castAdd k ℓ :=
    fun h => hlp.ne.symm (Fin.castAdd_injective n k h)
  have h0 : forestFun G ∅ g (Function.update x0 (Fin.castAdd k ℓ) false) = false := by
    have hupd : Function.update x0 (Fin.castAdd k ℓ) false = x0 := by
      funext i
      by_cases hi : i = Fin.castAdd k ℓ
      · subst hi; simp [hx0, Fin.append_left, hlp.ne]
      · rw [Function.update_of_ne hi]
    rw [hupd]
    simp only [forestFun, hx0, Fin.append_left, Fin.append_right]
    have hno : ¬ (∃ u v : Fin n, G.Adj u v ∧ decide (u = p) = true ∧ decide (v = p) = true) := by
      rintro ⟨u, v, huv, hu, hv⟩
      rw [decide_eq_true_eq] at hu hv
      subst hu; subst hv
      exact G.loopless.irrefl _ huv
    simp [hno]
  have h1 : forestFun G ∅ g (Function.update x0 (Fin.castAdd k ℓ) true) = true := by
    simp only [forestFun]
    have ht : ∃ u v : Fin n, G.Adj u v ∧
        Function.update x0 (Fin.castAdd k ℓ) true (Fin.castAdd k u) = true ∧
        Function.update x0 (Fin.castAdd k ℓ) true (Fin.castAdd k v) = true := by
      refine ⟨ℓ, p, hlp, by simp, ?_⟩
      rw [Function.update_of_ne hpneℓ]
      simp [hx0, Fin.append_left]
    have hg : (fun j : Fin k => Function.update x0 (Fin.castAdd k ℓ) true (Fin.natAdd n j)) = y₁ := by
      funext j
      rw [Function.update_of_ne]
      · simp [hx0, Fin.append_right]
      · intro h
        have hval := congrArg Fin.val h
        simp [Fin.castAdd, Fin.natAdd] at hval
        omega
    simp [ht, hg, hy₁]
  rw [h0, h1]
  decide

lemma lower_bound_aux {k c : ℕ} {g : (Fin k → Bool) → Bool}
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hg_sz : ∀ r : ℕ, HasCircuitSize k g r ↔ c ≤ r) :
    ∀ (s : ℕ) {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      G.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
      (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) →
      HasMinVC G t →
      HasCircuitSize (n + k) (forestFun G A g) s →
      A.card + G.edgeFinset.card + t + c ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro n t G _ A hAcyc hA_iso hAct hvc hC
    by_cases hAne : A.Nonempty
    · obtain ⟨a, ha⟩ := hAne
      have hdep := forestFun_dep_A G A g hg_nc a ha
      have hcard : (A.erase a).card + 1 = A.card := by
        have hpos : 1 ≤ A.card := Finset.one_le_card.2 ⟨a, ha⟩
        rw [Finset.card_erase_of_mem ha]; omega
      by_cases hRest : (A.erase a).Nonempty ∨ ∃ u v : Fin n, G.Adj u v
      · have hrew := forestFun_update_A G A g a (hA_iso a ha)
        have hnc : ∃ x x',
            forestFun G A g (Function.update x (Fin.castAdd k a) false) ≠
            forestFun G A g (Function.update x' (Fin.castAdd k a) false) := by
          simpa only [← congrFun hrew] using forestFun_nonconst G (A.erase a) g hg_nc hRest
        obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.castAdd k a) false hC hdep hnc
        rw [hrew] at hC'
        have hih := ih (s - 1) (by omega) G (A.erase a) hAcyc
          (fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)) hRest hvc hC'
        omega
      · have hrew := forestFun_update_A_true G A g a ha
        have hnc : ∃ x x',
            forestFun G A g (Function.update x (Fin.castAdd k a) true) ≠
            forestFun G A g (Function.update x' (Fin.castAdd k a) true) := by
          obtain ⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩ := exists_false_true_of_nonconst hg_nc
          refine ⟨Fin.append (fun _ : Fin n => false) y₀, Fin.append (fun _ : Fin n => false) y₁, ?_⟩
          have h0 : forestFun G A g (Function.update (Fin.append (fun _ : Fin n => false) y₀)
              (Fin.castAdd k a) true) = false := by
            rw [congrFun hrew _]; simp [Fin.append_right, hy₀]
          have h1 : forestFun G A g (Function.update (Fin.append (fun _ : Fin n => false) y₁)
              (Fin.castAdd k a) true) = true := by
            rw [congrFun hrew _]; simp [Fin.append_right, hy₁]
          rw [h0, h1]; decide
        obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.castAdd k a) true hC hdep hnc
        rw [hrew] at hC'
        have hCg : HasCircuitSize k g (s - 1) := hardwire_prefix_nonconst hC' (fun _ => rfl) hg_nc
        have hcs : c ≤ s - 1 := (hg_sz (s - 1)).1 hCg
        have hempty : ∀ u v : Fin n, ¬ G.Adj u v := by
          intro u v huv; exact hRest (Or.inr ⟨u, v, huv⟩)
        have ht0 : t = 0 := hasMinVC_empty G hempty hvc
        have he0 : G.edgeFinset.card = 0 := by
          apply Finset.card_eq_zero.2
          ext e
          induction e using Sym2.ind with
          | _ u v => simp [SimpleGraph.mem_edgeFinset, hempty u v]
        have hA1 : A.card = 1 := by
          have herase : A.erase a = ∅ :=
            Finset.not_nonempty_iff_eq_empty.1 (fun h => hRest (Or.inl h))
          have hzero : (A.erase a).card = 0 := by simp [herase]
          have herase_card := Finset.card_erase_of_mem ha
          omega
        omega
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
      subst hAempty
      by_cases hEdge : ∃ u v : Fin n, G.Adj u v
      · obtain ⟨ℓ, p, hlp, hleaf, hcases⟩ := acyclic_leaf_cases G hAcyc hEdge
        rcases hcases with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | ⟨q, hqne, hpq, hpdeg2⟩
        · classical
          obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (G.deleteEdges {s(ℓ, p)})
          have ht₁ : t₁ = t := hasMinVC_deleteLeafEdge_eq G ℓ ℓ' p hℓ'ne hℓ'p hℓ'leaf hvc hvc₁
          have hdep := forestFun_dep_edge G g hg_nc ℓ p hlp
          have hrew := forestFun_update_leaf_false G g ℓ p hleaf
          by_cases hRest : ∃ u v : Fin n, (G.deleteEdges {s(ℓ, p)}).Adj u v
          · have hnc : ∃ x x',
                forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) false) ≠
                forestFun G ∅ g (Function.update x' (Fin.castAdd k ℓ) false) := by
              obtain ⟨x, x', hne⟩ := forestFun_nonconst (G.deleteEdges {s(ℓ, p)}) ∅ g hg_nc (Or.inr hRest)
              refine ⟨x, x', ?_⟩
              rw [congrFun hrew x, congrFun hrew x']
              exact hne
            obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.castAdd k ℓ) false hC hdep hnc
            rw [hrew] at hC'
            have hih := ih (s - 1) (by omega) (G.deleteEdges {s(ℓ, p)}) ∅
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) (Or.inr hRest) hvc₁ hC'
            have hedge := edgeFinset_card_deleteEdge G ℓ p hlp
            simp only [Finset.card_empty, zero_add] at hih ⊢
            omega
          · have hrew1 := forestFun_update_leaf_true G g ℓ p hlp hleaf
            have hnc1 : ∃ x x',
                forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) true) ≠
                forestFun G ∅ g (Function.update x' (Fin.castAdd k ℓ) true) := by
              obtain ⟨x, x', hne⟩ := forestFun_nonconst (deleteVertexEdges G p) {p} g hg_nc
                (Or.inl (Finset.singleton_nonempty p))
              refine ⟨x, x', ?_⟩
              rw [congrFun hrew1 x, congrFun hrew1 x']
              exact hne
            obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.castAdd k ℓ) true hC hdep hnc1
            rw [hrew1] at hC'
            have hdepA := forestFun_dep_A (deleteVertexEdges G p) {p} g hg_nc p (by simp)
            have hrewA := forestFun_update_A_true (deleteVertexEdges G p) {p} g p (by simp)
            have hncA : ∃ x x',
                forestFun (deleteVertexEdges G p) {p} g
                  (Function.update x (Fin.castAdd k p) true) ≠
                forestFun (deleteVertexEdges G p) {p} g
                  (Function.update x' (Fin.castAdd k p) true) := by
              obtain ⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩ := exists_false_true_of_nonconst hg_nc
              refine ⟨Fin.append (fun _ : Fin n => false) y₀,
                Fin.append (fun _ : Fin n => false) y₁, ?_⟩
              have h0 : forestFun (deleteVertexEdges G p) {p} g
                  (Function.update (Fin.append (fun _ : Fin n => false) y₀)
                    (Fin.castAdd k p) true) = false := by
                rw [congrFun hrewA _]; simp [Fin.append_right, hy₀]
              have h1 : forestFun (deleteVertexEdges G p) {p} g
                  (Function.update (Fin.append (fun _ : Fin n => false) y₁)
                    (Fin.castAdd k p) true) = true := by
                rw [congrFun hrewA _]; simp [Fin.append_right, hy₁]
              rw [h0, h1]; decide
            obtain ⟨hs2, hC2⟩ := elim_one_var (Fin.castAdd k p) true hC' hdepA hncA
            rw [hrewA] at hC2
            have hCg : HasCircuitSize k g (s - 1 - 1) :=
              hardwire_prefix_nonconst hC2 (fun _ => rfl) hg_nc
            have hcs : c ≤ s - 2 := by
              have := (hg_sz (s - 1 - 1)).1 hCg
              omega
            have hedge := edgeFinset_card_deleteEdge G ℓ p hlp
            have ht0 : t₁ = 0 := by
              apply hasMinVC_empty (G.deleteEdges {s(ℓ, p)})
              · intro u v huv; exact hRest ⟨u, v, huv⟩
              · exact hvc₁
            have htEq : t = 0 := by rw [← ht₁]; exact ht0
            have he0 : (G.deleteEdges {s(ℓ, p)}).edgeFinset.card = 0 := by
              apply Finset.card_eq_zero.2
              ext e
              induction e using Sym2.ind with
              | _ u v =>
                simp only [Finset.notMem_empty, SimpleGraph.mem_edgeFinset]
                exact iff_false_intro fun h => hRest ⟨u, v, h⟩
            have hedge' : G.edgeFinset.card = 1 := by omega
            simp only [Finset.card_empty, zero_add, htEq, hedge']
            omega
        · classical
          obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges G p)
          have ht' : t' + 1 = t := hasMinVC_deleteVertex G ℓ p hlp hleaf hvc hvc'
          have hdep := forestFun_dep_edge G g hg_nc ℓ p hlp
          have hrew := forestFun_update_leaf_true G g ℓ p hlp hleaf
          have hnc : ∃ x x',
              forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) true) ≠
              forestFun G ∅ g (Function.update x' (Fin.castAdd k ℓ) true) := by
            obtain ⟨x, x', hne⟩ := forestFun_nonconst (deleteVertexEdges G p) {p} g hg_nc
              (Or.inl (Finset.singleton_nonempty p))
            refine ⟨x, x', ?_⟩
            rw [congrFun hrew x, congrFun hrew x']
            exact hne
          obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.castAdd k ℓ) true hC hdep hnc
          rw [hrew] at hC'
          have hih := ih (s - 1) (by omega) (deleteVertexEdges G p) {p}
            (hAcyc.anti (deleteVertexEdges_le G p))
            (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl)
            (Or.inl (Finset.singleton_nonempty p)) hvc' hC'
          have hedge := edgeFinset_card_deleteVertex_deg1 G ℓ p hlp hpdeg1
          simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
          omega
        · classical
          have hdep := forestFun_dep_edge G g hg_nc ℓ p hlp
          have hrew0 := forestFun_update_leaf_false G g ℓ p hleaf
          have hrew1 := forestFun_update_leaf_true G g ℓ p hlp hleaf
          have hRest0 : ∃ u v : Fin n, (G.deleteEdges {s(ℓ, p)}).Adj u v := ⟨p, q, by
            simp [SimpleGraph.deleteEdges_adj, hpq, hqne, hlp.ne.symm]⟩
          have hnc0 : ∃ x x',
              forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) false) ≠
              forestFun G ∅ g (Function.update x' (Fin.castAdd k ℓ) false) := by
            obtain ⟨x, x', hne⟩ := forestFun_nonconst (G.deleteEdges {s(ℓ, p)}) ∅ g hg_nc (Or.inr hRest0)
            refine ⟨x, x', ?_⟩
            rw [congrFun hrew0 x, congrFun hrew0 x']
            exact hne
          have hnc1 : ∃ x x',
              forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) true) ≠
              forestFun G ∅ g (Function.update x' (Fin.castAdd k ℓ) true) := by
            obtain ⟨x, x', hne⟩ := forestFun_nonconst (deleteVertexEdges G p) {p} g hg_nc
              (Or.inl (Finset.singleton_nonempty p))
            refine ⟨x, x', ?_⟩
            rw [congrFun hrew1 x, congrFun hrew1 x']
            exact hne
          obtain ⟨hs2, hC0 | hC1⟩ := elim_two_var (Fin.castAdd k ℓ) hC hdep hnc0 hnc1
          · rw [hrew0] at hC0
            obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (G.deleteEdges {s(ℓ, p)})
            have ht₁ := (hasMinVC_deleteEdge G ℓ p hvc hvc₁).2
            have hih := ih (s - 2) (by omega) (G.deleteEdges {s(ℓ, p)}) ∅
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) (Or.inr hRest0) hvc₁ hC0
            have hedge := edgeFinset_card_deleteEdge G ℓ p hlp
            simp only [Finset.card_empty, zero_add] at hih ⊢
            omega
          · rw [hrew1] at hC1
            obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges G p)
            have ht' : t' + 1 = t := hasMinVC_deleteVertex G ℓ p hlp hleaf hvc hvc'
            have hih := ih (s - 2) (by omega) (deleteVertexEdges G p) {p}
              (hAcyc.anti (deleteVertexEdges_le G p))
              (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl)
              (Or.inl (Finset.singleton_nonempty p)) hvc' hC1
            have hedge := edgeFinset_card_deleteVertex_deg2 G ℓ p q hlp hpq hqne hpdeg2
            simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
            omega
      · exact False.elim (hAct.elim hAne hEdge)

def shiftGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (· + n)⟩

lemma shiftGate_ok (n : ℕ) (g : Gate) (h : OkGate g) : OkGate (shiftGate n g) :=
  ⟨h.1, by simp [shiftGate]; exact h.2⟩

lemma wiresFrom_shift (n : ℕ) (gs : List Gate) (pref w : List Bool)
    (hpref : pref.length = n) :
    wiresFrom (gs.map (shiftGate n)) (pref ++ w) = pref ++ wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hmap : ((shiftGate n g).inputs.map fun i => (pref ++ w).getD i false) =
        (g.inputs.map fun i => w.getD i false) := by
      simp only [shiftGate, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < w.length
      · rw [List.getD_eq_getElem _ _ (by simp [hpref]; omega),
            List.getElem_append_right (by omega),
            List.getD_eq_getElem _ _ hi]
        congr 1; omega
      · rw [List.getD_eq_default _ _ (by simp [hpref]; omega),
            List.getD_eq_default _ _ (by omega)]
    rw [hmap, List.append_assoc, ih]
    rfl

lemma list_any_congr_mem {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hpx⟩; exact ⟨x, hx, by rw [← h x hx]; exact hpx⟩
  · rintro ⟨x, hx, hqx⟩; exact ⟨x, hx, by rw [h x hx]; exact hqx⟩

def pushOrList (m : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws => pushOrList m (gs ++ [⟨GateOp.or, [acc, w]⟩]) (m + gs.length) ws

lemma pushOrList_props (m : ℕ) (ws : List ℕ) :
    ∀ (gs : List Gate) (acc : ℕ),
      (∀ g ∈ gs, OkGate g) →
      acc < m + gs.length →
      (∀ w ∈ ws, w < m + gs.length) →
      (∀ g ∈ (pushOrList m gs acc ws).1, OkGate g) ∧
      (pushOrList m gs acc ws).1.length = gs.length + ws.length ∧
      (pushOrList m gs acc ws).2 < m + (pushOrList m gs acc ws).1.length ∧
      (∀ x : List Bool, x.length = m →
        (∀ i < m + gs.length,
          (wiresFrom (pushOrList m gs acc ws).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
        (wiresFrom (pushOrList m gs acc ws).1 x).getD (pushOrList m gs acc ws).2 false =
          ((wiresFrom gs x).getD acc false ||
            ws.any (fun w => (wiresFrom gs x).getD w false))) := by
  induction ws with
  | nil =>
    intro gs acc hok hacc _
    refine ⟨hok, by simp [pushOrList], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushOrList]⟩⟩
  | cons w ws ih =>
    intro gs acc hok hacc hws
    set gs' := gs ++ [⟨GateOp.or, [acc, w]⟩] with hgs'
    have hok' : ∀ g ∈ gs', OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok g h
      · simp at h; subst h; simp [OkGate]
    have hlen' : gs'.length = gs.length + 1 := by simp [hgs']
    have hacc' : m + gs.length < m + gs'.length := by omega
    have hws' : ∀ u ∈ ws, u < m + gs'.length := by
      intro u hu
      have := hws u (List.mem_cons_of_mem _ hu)
      omega
    obtain ⟨hok2, hlen2, hlt2, hev2⟩ := ih gs' (m + gs.length) hok' hacc' hws'
    refine ⟨hok2, ?_, hlt2, ?_⟩
    · show (pushOrList m gs' (m + gs.length) ws).1.length = gs.length + (w :: ws).length
      rw [hlen2, hlen']
      simp
      omega
    · intro x hx
      obtain ⟨hpres, hval⟩ := hev2 x hx
      have hstep_pres : ∀ i < m + gs.length,
          (wiresFrom gs' x).getD i false = (wiresFrom gs x).getD i false := by
        intro i hi
        rw [hgs', wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hstep_new : (wiresFrom gs' x).getD (m + gs.length) false =
          ((wiresFrom gs x).getD acc false || (wiresFrom gs x).getD w false) := by
        rw [hgs', wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      refine ⟨fun i hi => (hpres i (by omega)).trans (hstep_pres i hi), ?_⟩
      show (wiresFrom (pushOrList m gs' (m + gs.length) ws).1 x).getD
          (pushOrList m gs' (m + gs.length) ws).2 false = _
      rw [hval, hstep_new]
      have hany : ws.any (fun u => (wiresFrom gs' x).getD u false) =
          ws.any (fun u => (wiresFrom gs x).getD u false) :=
        list_any_congr_mem fun u hu => hstep_pres u (hws u (List.mem_cons_of_mem _ hu))
      rw [hany]
      simp [Bool.or_assoc]

def pushStarStep (m : ℕ) (gs : List Gate) (acc : ℕ) (u : ℕ) (vs : List ℕ) :
    List Gate × ℕ :=
  match vs with
  | [] => (gs, acc)
  | v₀ :: vs' =>
    let r1 := pushOrList m gs v₀ vs'
    let gs1 := r1.1 ++ [⟨GateOp.and, [u, r1.2]⟩]
    let w_and := m + r1.1.length
    let gs2 := gs1 ++ [⟨GateOp.or, [acc, w_and]⟩]
    (gs2, m + gs1.length)

lemma pushStarStep_props (m : ℕ) (gs : List Gate) (acc u : ℕ) (vs : List ℕ)
    (hok : ∀ g ∈ gs, OkGate g) (hacc : acc < m + gs.length) (hu : u < m + gs.length)
    (hvs : ∀ v ∈ vs, v < m + gs.length) :
    (∀ g ∈ (pushStarStep m gs acc u vs).1, OkGate g) ∧
    (pushStarStep m gs acc u vs).1.length ≤ gs.length + vs.length + 1 ∧
    (pushStarStep m gs acc u vs).2 < m + (pushStarStep m gs acc u vs).1.length ∧
    (∀ x : List Bool, x.length = m →
      (∀ i < m + gs.length,
        (wiresFrom (pushStarStep m gs acc u vs).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
      (wiresFrom (pushStarStep m gs acc u vs).1 x).getD (pushStarStep m gs acc u vs).2 false =
        ((wiresFrom gs x).getD acc false ||
          ((wiresFrom gs x).getD u false && vs.any (fun v => (wiresFrom gs x).getD v false)))) := by
  cases vs with
  | nil =>
    refine ⟨hok, by simp [pushStarStep], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushStarStep]⟩⟩
  | cons v₀ vs' =>
    obtain ⟨hok1, hlen1, hlt1, hev1⟩ := pushOrList_props m vs' gs v₀ hok
      (hvs v₀ List.mem_cons_self) (fun v hv => hvs v (List.mem_cons_of_mem _ hv))
    set r1 := pushOrList m gs v₀ vs' with hr1
    set gs1 := r1.1 ++ [⟨GateOp.and, [u, r1.2]⟩] with hgs1
    set w_and := m + r1.1.length with hwand
    set gs2 := gs1 ++ [⟨GateOp.or, [acc, w_and]⟩] with hgs2
    have hok1' : ∀ g ∈ gs1, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok1 g h
      · simp at h; subst h; simp [OkGate]
    have hok2 : ∀ g ∈ gs2, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok1' g h
      · simp at h; subst h; simp [OkGate]
    have hlen_gs2 : gs2.length = gs.length + (v₀ :: vs').length + 1 := by
      simp [hgs2, hgs1, hlen1]; omega
    refine ⟨hok2, ?_, ?_, ?_⟩
    · show gs2.length ≤ gs.length + (v₀ :: vs').length + 1; omega
    · show m + gs1.length < m + gs2.length; simp [hgs2]
    · intro x hx
      obtain ⟨hpres1, hval1⟩ := hev1 x hx
      have hpres_and : ∀ i < m + r1.1.length,
          (wiresFrom gs1 x).getD i false = (wiresFrom r1.1 x).getD i false := by
        intro i hi
        rw [hgs1, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hpres_or : ∀ i < m + gs1.length,
          (wiresFrom gs2 x).getD i false = (wiresFrom gs1 x).getD i false := by
        intro i hi
        rw [hgs2, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hval_and : (wiresFrom gs1 x).getD w_and false =
          ((wiresFrom r1.1 x).getD u false && (wiresFrom r1.1 x).getD r1.2 false) := by
        rw [hgs1, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      have hval_or : (wiresFrom gs2 x).getD (m + gs1.length) false =
          ((wiresFrom gs1 x).getD acc false || (wiresFrom gs1 x).getD w_and false) := by
        rw [hgs2, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      refine ⟨?_, ?_⟩
      · intro i hi
        have hlen_le : gs.length ≤ r1.1.length := by omega
        have hlen_le1 : r1.1.length ≤ gs1.length := by simp [hgs1]
        exact (hpres_or i (by omega)).trans ((hpres_and i (by omega)).trans (hpres1 i hi))
      · show (wiresFrom gs2 x).getD (m + gs1.length) false = _
        rw [hval_or, hpres_and acc (by omega), hpres1 acc hacc,
            hval_and, hpres1 u hu, hval1]
        simp

def pushStars (m : ℕ) (gs : List Gate) (acc : ℕ) : List (ℕ × List ℕ) → List Gate × ℕ
  | [] => (gs, acc)
  | (u, vs) :: rest =>
    let r := pushStarStep m gs acc u vs
    pushStars m r.1 r.2 rest

lemma pushStars_props (m : ℕ) (stars : List (ℕ × List ℕ)) :
    ∀ (gs : List Gate) (acc : ℕ),
      (∀ g ∈ gs, OkGate g) →
      acc < m + gs.length →
      (∀ p ∈ stars, p.1 < m ∧ ∀ v ∈ p.2, v < m) →
      (∀ g ∈ (pushStars m gs acc stars).1, OkGate g) ∧
      (pushStars m gs acc stars).1.length ≤
        gs.length + (stars.map (fun p => p.2.length + 1)).sum ∧
      (pushStars m gs acc stars).2 < m + (pushStars m gs acc stars).1.length ∧
      (∀ x : List Bool, x.length = m →
        (∀ i < m + gs.length,
          (wiresFrom (pushStars m gs acc stars).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
        (wiresFrom (pushStars m gs acc stars).1 x).getD (pushStars m gs acc stars).2 false =
          ((wiresFrom gs x).getD acc false ||
            stars.any (fun p => (wiresFrom gs x).getD p.1 false &&
              p.2.any (fun v => (wiresFrom gs x).getD v false)))) := by
  induction stars with
  | nil =>
    intro gs acc hok hacc _
    refine ⟨hok, by simp [pushStars], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushStars]⟩⟩
  | cons st rest ih =>
    obtain ⟨u, vs⟩ := st
    intro gs acc hok hacc hst
    have hst0 := hst (u, vs) List.mem_cons_self
    obtain ⟨hok1, hlen1, hlt1, hev1⟩ := pushStarStep_props m gs acc u vs hok hacc
      (by omega) (fun v hv => by have := hst0.2 v hv; omega)
    set r := pushStarStep m gs acc u vs with hr
    obtain ⟨hok2, hlen2, hlt2, hev2⟩ := ih r.1 r.2 hok1 hlt1
      (fun p hp => hst p (List.mem_cons_of_mem _ hp))
    refine ⟨hok2, ?_, hlt2, ?_⟩
    · show (pushStars m r.1 r.2 rest).1.length ≤
        gs.length + (((u, vs) :: rest).map (fun p => p.2.length + 1)).sum
      simp only [List.map_cons, List.sum_cons]
      omega
    · intro x hx
      obtain ⟨hpres1, hval1⟩ := hev1 x hx
      obtain ⟨hpres2, hval2⟩ := hev2 x hx
      have hlen_le : gs.length ≤ r.1.length := by
        cases vs with
        | nil => simp [hr, pushStarStep]
        | cons v₀ vs' =>
          have := (pushOrList_props m vs' gs v₀ hok (by have := hst0.2 v₀ List.mem_cons_self; omega)
            (fun v hv => by have := hst0.2 v (List.mem_cons_of_mem _ hv); omega)).2.1
          simp [hr, pushStarStep]
          omega
      refine ⟨fun i hi => (hpres2 i (by omega)).trans (hpres1 i hi), ?_⟩
      show (wiresFrom (pushStars m r.1 r.2 rest).1 x).getD (pushStars m r.1 r.2 rest).2 false = _
      rw [hval2, hval1]
      have hany : rest.any (fun p => (wiresFrom r.1 x).getD p.1 false &&
            p.2.any (fun v => (wiresFrom r.1 x).getD v false)) =
          rest.any (fun p => (wiresFrom gs x).getD p.1 false &&
            p.2.any (fun v => (wiresFrom gs x).getD v false)) := by
        refine list_any_congr_mem fun p hp => ?_
        have hpm := hst p (List.mem_cons_of_mem _ hp)
        rw [hpres1 p.1 (by omega)]
        congr 1
        exact list_any_congr_mem fun v hv => hpres1 v (by have := hpm.2 v hv; omega)
      rw [hany]
      simp [Bool.or_assoc]

def pushStarValue (m : ℕ) (gs : List Gate) (u : ℕ) (vs : List ℕ) : List Gate × ℕ :=
  match vs with
  | [] => (gs, m + gs.length)
  | v₀ :: vs' =>
    let r1 := pushOrList m gs v₀ vs'
    (r1.1 ++ [⟨GateOp.and, [u, r1.2]⟩], m + r1.1.length)

lemma pushStarValue_props (m : ℕ) (gs : List Gate) (u : ℕ) (vs : List ℕ)
    (hok : ∀ g ∈ gs, OkGate g) (hu : u < m + gs.length)
    (hvs : ∀ v ∈ vs, v < m + gs.length) (hne : vs ≠ []) :
    (∀ g ∈ (pushStarValue m gs u vs).1, OkGate g) ∧
    (gs.length ≤ (pushStarValue m gs u vs).1.length ∧
      (pushStarValue m gs u vs).1.length ≤ gs.length + vs.length) ∧
    (pushStarValue m gs u vs).2 < m + (pushStarValue m gs u vs).1.length ∧
    (∀ x : List Bool, x.length = m →
      (∀ i < m + gs.length,
        (wiresFrom (pushStarValue m gs u vs).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
      (wiresFrom (pushStarValue m gs u vs).1 x).getD (pushStarValue m gs u vs).2 false =
        ((wiresFrom gs x).getD u false &&
          vs.any (fun v => (wiresFrom gs x).getD v false))) := by
  match vs with
  | [] => exact absurd rfl hne
  | v₀ :: vs' =>
    obtain ⟨hok1, hlen1, hlt1, hev1⟩ := pushOrList_props m vs' gs v₀ hok
      (hvs v₀ List.mem_cons_self) (fun v hv => hvs v (List.mem_cons_of_mem _ hv))
    set r1 := pushOrList m gs v₀ vs' with hr1
    set gs1 := r1.1 ++ [⟨GateOp.and, [u, r1.2]⟩] with hgs1
    have hok1' : ∀ g ∈ gs1, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok1 g h
      · simp at h; subst h; simp [OkGate]
    have hlen_gs1 : gs1.length = gs.length + (v₀ :: vs').length := by
      simp [hgs1, hlen1]; omega
    refine ⟨hok1', ?_, ?_, ?_⟩
    · simp only [pushStarValue]
      change gs.length ≤ gs1.length ∧ gs1.length ≤ gs.length + (v₀ :: vs').length
      exact ⟨by omega, by omega⟩
    · show m + r1.1.length < m + gs1.length
      simp [hgs1]
    · intro x hx
      obtain ⟨hpres1, hval1⟩ := hev1 x hx
      have hpres_and : ∀ i < m + r1.1.length,
          (wiresFrom gs1 x).getD i false = (wiresFrom r1.1 x).getD i false := by
        intro i hi
        rw [hgs1, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hval_and : (wiresFrom gs1 x).getD (m + r1.1.length) false =
          ((wiresFrom r1.1 x).getD u false && (wiresFrom r1.1 x).getD r1.2 false) := by
        rw [hgs1, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      refine ⟨?_, ?_⟩
      · intro i hi
        have : gs.length ≤ r1.1.length := by omega
        exact (hpres_and i (by omega)).trans (hpres1 i hi)
      · show (wiresFrom gs1 x).getD (m + r1.1.length) false =
            ((wiresFrom gs x).getD u false &&
              (v₀ :: vs').any (fun v => (wiresFrom gs x).getD v false))
        rw [hval_and, hpres1 u hu, hval1]
        rfl

lemma upper_bound_aux {n k c t s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hg_sz : ∀ r : ℕ, HasCircuitSize k g r ↔ c ≤ r)
    (hAct : A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v)
    (hvc_ex : ∃ S : Finset (Fin n), IsVC G S ∧ S.card = t)
    (hs : A.card + G.edgeFinset.card + t + c ≤ s) :
    HasCircuitSize (n + k) (forestFun G A g) s := by
  obtain ⟨Cg, hCg_ok, hCg_sz, hCg_ev⟩ := (hg_sz c).2 (le_refl c)
  obtain ⟨_, ⟨y₁, hy₁⟩⟩ := exists_false_true_of_nonconst hg_nc
  have hCg_out : Cg.output < k + Cg.gates.length := by
    by_contra hge
    have h1 : Cg.eval (List.ofFn y₁) = false := by
      show (wiresFrom Cg.gates (List.ofFn y₁)).getD Cg.output false = false
      exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
    have h2 := hCg_ev y₁
    rw [h1, hy₁] at h2
    exact Bool.false_ne_true h2
  set gs0 : List Gate := Cg.gates.map (shiftGate n) with hgs0
  have hgs0_ok : ∀ g ∈ gs0, OkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact shiftGate_ok n g0 (hCg_ok g0 hg0)
  have hgs0_len : gs0.length = Cg.gates.length := by simp [hgs0]
  have hgs0_eval : ∀ x : Fin (n + k) → Bool,
      (wiresFrom gs0 (List.ofFn x)).getD (Cg.output + n) false =
        g (fun j : Fin k => x (Fin.natAdd n j)) := by
    intro x
    set pref := List.ofFn (fun i : Fin n => x (Fin.castAdd k i)) with hpref
    set suff := List.ofFn (fun j : Fin k => x (Fin.natAdd n j)) with hsuff
    have hsplit : List.ofFn x = pref ++ suff := by
      apply List.ext_getElem (by simp [hpref, hsuff])
      intro i h1 h2
      by_cases hi : i < n
      · rw [List.getElem_append_left (by simp [hpref]; exact hi)]
        simp [hpref, List.getElem_ofFn, Fin.castAdd]
      · rw [List.getElem_append_right (by simp [hpref]; omega)]
        simp only [hpref, hsuff, List.length_ofFn, List.getElem_ofFn]
        congr 1; ext; simp [Fin.natAdd]; omega
    rw [hsplit, hgs0, wiresFrom_shift n Cg.gates pref suff (by simp [hpref])]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_append, wiresFrom_length]; simp [hpref, hsuff]; omega),
        List.getElem_append_right (by simp [hpref])]
    have heq_idx : Cg.output + n - pref.length = Cg.output := by simp [hpref]
    simp only [heq_idx]
    rw [← List.getD_eq_getElem _ false (by rw [wiresFrom_length]; simp [hsuff]; omega)]
    exact hCg_ev (fun j : Fin k => x (Fin.natAdd n j))
  obtain ⟨S, hS_vc, hS_card⟩ := hvc_ex
  set N : Fin n → Finset (Fin n) :=
    fun u => Finset.univ.filter (fun v => G.Adj u v ∧ (v ∈ S → u < v)) with hN
  have hsum_N : ∑ u ∈ S, (N u).card = G.edgeFinset.card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_sigma] at hp
      rw [SimpleGraph.mem_edgeFinset]
      exact (Finset.mem_filter.1 hp.2).2.1
    · intro p₁ hp₁ p₂ hp₂ heq
      rw [Finset.mem_sigma] at hp₁ hp₂
      have h1 := (Finset.mem_filter.1 hp₁.2).2
      have h2 := (Finset.mem_filter.1 hp₂.2).2
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Sigma.ext ha (by simpa using hb)
      · exfalso
        have hlt1 : p₁.1 < p₁.2 := h1.2 (hb ▸ hp₂.1)
        have hlt2 : p₂.1 < p₂.2 := h2.2 (ha ▸ hp₁.1)
        rw [ha, hb] at hlt1
        exact lt_asymm hlt1 hlt2
    · intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeFinset] at he
        rcases hS_vc a b he with ha | hb
        · by_cases hba : b ∈ S ∧ b < a
          · refine ⟨⟨b, a⟩, Finset.mem_sigma.2 ⟨hba.1, Finset.mem_filter.2
              ⟨Finset.mem_univ a, he.symm, fun _ => hba.2⟩⟩, Sym2.eq_swap⟩
          · refine ⟨⟨a, b⟩, Finset.mem_sigma.2 ⟨ha, Finset.mem_filter.2
              ⟨Finset.mem_univ b, he, fun hb' => ?_⟩⟩, rfl⟩
            rcases lt_trichotomy a b with h | h | h
            · exact h
            · exact absurd h he.ne
            · exact absurd ⟨hb', h⟩ hba
        · by_cases hab : a ∈ S ∧ a < b
          · refine ⟨⟨a, b⟩, Finset.mem_sigma.2 ⟨hab.1, Finset.mem_filter.2
              ⟨Finset.mem_univ b, he, fun _ => hab.2⟩⟩, rfl⟩
          · refine ⟨⟨b, a⟩, Finset.mem_sigma.2 ⟨hb, Finset.mem_filter.2
              ⟨Finset.mem_univ a, he.symm, fun ha' => ?_⟩⟩, Sym2.eq_swap⟩
            rcases lt_trichotomy b a with h | h | h
            · exact h
            · exact absurd h he.ne.symm
            · exact absurd ⟨ha', h⟩ hab
  set stars : List (ℕ × List ℕ) :=
    S.toList.map (fun u : Fin n => ((u : ℕ), (N u).toList.map Fin.val)) with hstars
  have hstars_sum : (stars.map (fun p => p.2.length + 1)).sum = G.edgeFinset.card + t := by
    have hmap : stars.map (fun p => p.2.length + 1) =
        S.toList.map (fun u : Fin n => (N u).card + 1) := by
      simp [hstars, List.map_map, Function.comp_def]
    have hsum_list : (S.toList.map (fun u : Fin n => (N u).card + 1)).sum =
        ∑ u ∈ S, ((N u).card + 1) := by
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    rw [hmap, hsum_list, Finset.sum_add_distrib,
        hsum_N, Finset.sum_const, smul_eq_mul, mul_one, hS_card]
  have hstars_bound : ∀ p ∈ stars, p.1 < n + k ∧ ∀ v ∈ p.2, v < n + k := by
    intro p hp
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 hp
    refine ⟨by omega, ?_⟩
    intro v hv
    obtain ⟨v', _, rfl⟩ := List.mem_map.1 hv
    omega
  set gOut : ℕ := Cg.output + n
  have hwire0 : ∀ x : Fin (n + k) → Bool, ∀ u : Fin n,
      (wiresFrom gs0 (List.ofFn x)).getD (u : ℕ) false = x (Fin.castAdd k u) := by
    intro x u
    rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]
    rfl
  have hS_eq0 : ∀ x : Fin (n + k) → Bool,
      stars.any (fun p => (wiresFrom gs0 (List.ofFn x)).getD p.1 false &&
        p.2.any (fun v => (wiresFrom gs0 (List.ofFn x)).getD v false)) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧
        x (Fin.castAdd k v) = true) := by
    intro x
    apply Bool.eq_iff_iff.2
    simp only [hstars, List.any_map, List.any_eq_true, Function.comp_apply, Bool.and_eq_true,
      Finset.mem_toList, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, hux, v, hv, hvx⟩
      rw [hwire0 x u] at hux
      rw [hwire0 x v] at hvx
      exact ⟨u, v, (Finset.mem_filter.1 hv).2.1, hux, hvx⟩
    · rintro ⟨u, v, huv, hux, hvx⟩
      rcases hS_vc u v huv with hu | hv
      · by_cases hvu : v ∈ S ∧ v < u
        · exact ⟨v, hvu.1, by rw [hwire0 x v]; exact hvx,
            u, Finset.mem_filter.2 ⟨Finset.mem_univ u, huv.symm, fun _ => hvu.2⟩,
            by rw [hwire0 x u]; exact hux⟩
        · refine ⟨u, hu, by rw [hwire0 x u]; exact hux,
            v, Finset.mem_filter.2 ⟨Finset.mem_univ v, huv, fun hv' => ?_⟩,
            by rw [hwire0 x v]; exact hvx⟩
          rcases lt_trichotomy u v with h | h | h
          · exact h
          · exact absurd h huv.ne
          · exact absurd ⟨hv', h⟩ hvu
      · by_cases huv_lt : u ∈ S ∧ u < v
        · exact ⟨u, huv_lt.1, by rw [hwire0 x u]; exact hux,
            v, Finset.mem_filter.2 ⟨Finset.mem_univ v, huv, fun _ => huv_lt.2⟩,
            by rw [hwire0 x v]; exact hvx⟩
        · refine ⟨v, hv, by rw [hwire0 x v]; exact hvx,
            u, Finset.mem_filter.2 ⟨Finset.mem_univ u, huv.symm, fun hu' => ?_⟩,
            by rw [hwire0 x u]; exact hux⟩
          rcases lt_trichotomy v u with h | h | h
          · exact h
          · exact absurd h huv.ne.symm
          · exact absurd ⟨hu', h⟩ huv_lt
  by_cases hAne : A.Nonempty
  · obtain ⟨a0, ha0⟩ := hAne
    set acc0 : ℕ := (a0 : ℕ)
    set wsA' : List ℕ := (A.erase a0).toList.map Fin.val with hwsA'
    obtain ⟨hokA, hlenA, hltA, hevA⟩ := pushOrList_props (n + k) wsA' gs0 acc0
      hgs0_ok (by omega) (by
        intro w hw
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hw
        omega)
    set rA := pushOrList (n + k) gs0 acc0 wsA' with hrA
    obtain ⟨hokS, hlenS, hltS, hevS⟩ := pushStars_props (n + k) stars rA.1 rA.2
      hokA hltA hstars_bound
    set rF := pushStars (n + k) rA.1 rA.2 stars with hrF
    set gsAnd : List Gate := rF.1 ++ [⟨GateOp.and, [rF.2, gOut]⟩] with hgsAnd
    have hokAnd : ∀ g ∈ gsAnd, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hokS g h
      · simp at h; subst h; simp [OkGate]
    have hlen_tot : gsAnd.length ≤ s := by
      have hCg_sz' : Cg.gates.length ≤ c := hCg_sz
      have hws : wsA'.length = (A.erase a0).card := by simp [hwsA']
      have hAcard : (A.erase a0).card + 1 = A.card := by
        have hpos : 1 ≤ A.card := Finset.one_le_card.2 ⟨a0, ha0⟩
        rw [Finset.card_erase_of_mem ha0]; omega
      have hRA : rA.1.length = gs0.length + wsA'.length := hlenA
      have hRF : rF.1.length ≤ rA.1.length + (stars.map (fun p => p.2.length + 1)).sum := hlenS
      have hAnd : gsAnd.length = rF.1.length + 1 := by simp [hgsAnd]
      omega
    refine ⟨⟨gsAnd, n + k + rF.1.length⟩, hokAnd, hlen_tot, ?_⟩
    intro x
    have hxlen : (List.ofFn x).length = n + k := by simp
    obtain ⟨hpresA, hvalA⟩ := hevA (List.ofFn x) hxlen
    obtain ⟨hpresF, hvalF⟩ := hevS (List.ofFn x) hxlen
    have hand : (wiresFrom gsAnd (List.ofFn x)).getD (n + k + rF.1.length) false =
        ((wiresFrom rF.1 (List.ofFn x)).getD rF.2 false &&
          (wiresFrom rF.1 (List.ofFn x)).getD gOut false) := by
      simp only [hgsAnd, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
      rw [getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length]; simp [hxlen])]
      simp [GateOp.eval]
    have hg_pres : (wiresFrom rF.1 (List.ofFn x)).getD gOut false =
        g (fun j : Fin k => x (Fin.natAdd n j)) := by
      have hg0 : Cg.output + n < n + k + gs0.length := by
        have h1 := hCg_out; have h2 := hgs0_len; omega
      have hgA : Cg.output + n < n + k + rA.1.length := by
        have := hlenA; omega
      have h1 := hpresA (Cg.output + n) hg0
      have h2 := hpresF (Cg.output + n) hgA
      simpa [gOut] using (h2.trans (h1.trans (hgs0_eval x)))
    have hA_any :
        ((wiresFrom gs0 (List.ofFn x)).getD acc0 false ||
          wsA'.any (fun w => (wiresFrom gs0 (List.ofFn x)).getD w false)) =
          decide (∃ a ∈ A, x (Fin.castAdd k a) = true) := by
      apply Bool.eq_iff_iff.2
      simp only [hwsA', List.any_map, List.any_eq_true, Function.comp_apply,
        Finset.mem_toList, decide_eq_true_eq, acc0, Bool.or_eq_true]
      constructor
      · rintro (h | ⟨a, ha, hx⟩)
        · exact ⟨a0, ha0, by rw [← hwire0 x a0]; exact h⟩
        · exact ⟨a, Finset.mem_of_mem_erase ha, by rw [← hwire0 x a]; exact hx⟩
      · rintro ⟨a, ha, hx⟩
        by_cases heq : a = a0
        · left
          change (wiresFrom gs0 (List.ofFn x)).getD (a0 : ℕ) false = true
          rw [hwire0 x a0, ← heq]
          exact hx
        · right; exact ⟨a, Finset.mem_erase.2 ⟨heq, ha⟩, by rw [hwire0 x a]; exact hx⟩
    have hForest :
        (wiresFrom rF.1 (List.ofFn x)).getD rF.2 false =
          decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨
            ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧
              x (Fin.castAdd k v) = true) := by
      have hstars_pres : stars.any (fun p => (wiresFrom rA.1 (List.ofFn x)).getD p.1 false &&
            p.2.any (fun v => (wiresFrom rA.1 (List.ofFn x)).getD v false)) =
          stars.any (fun p => (wiresFrom gs0 (List.ofFn x)).getD p.1 false &&
            p.2.any (fun v => (wiresFrom gs0 (List.ofFn x)).getD v false)) := by
        refine list_any_congr_mem fun p hp => ?_
        have hpm := hstars_bound p hp
        rw [hpresA p.1 (by omega)]
        congr 1
        exact list_any_congr_mem fun v hv => hpresA v (by have := hpm.2 v hv; omega)
      rw [hvalF, hvalA, hstars_pres, hA_any, hS_eq0 x]
      simp [Bool.or_assoc]
    show (wiresFrom gsAnd (List.ofFn x)).getD (n + k + rF.1.length) false = forestFun G A g x
    simp only [forestFun]
    rw [hand, hForest, hg_pres]
  · have hE : ∃ u v : Fin n, G.Adj u v := hAct.resolve_left hAne
    have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
    have hcardA : A.card = 0 := by simp [hAempty]
    have huS_ex : ∃ u ∈ S, (N u).Nonempty := by
      by_contra h
      simp only [not_exists, not_and] at h
      have hz : ∀ u ∈ S, (N u).card = 0 := fun u hu =>
        Finset.card_eq_zero.2 (Finset.not_nonempty_iff_eq_empty.1 (h u hu))
      have hsum0 : ∑ u ∈ S, (N u).card = 0 := Finset.sum_eq_zero hz
      have hpos : 0 < G.edgeFinset.card := by
        obtain ⟨u, v, huv⟩ := hE
        exact Finset.card_pos.2 ⟨s(u, v), by rw [SimpleGraph.mem_edgeFinset]; exact huv⟩
      omega
    obtain ⟨uS, huS, hNu⟩ := huS_ex
    set vsU : List ℕ := (N uS).toList.map Fin.val with hvsU
    have hvsUne : vsU ≠ [] := by
      intro h
      simp only [hvsU, List.map_eq_nil_iff, Finset.toList_eq_nil] at h
      exact Finset.not_nonempty_iff_eq_empty.2 h hNu
    obtain ⟨hokV, ⟨hlenV_ge, hlenV⟩, hltV, hevV⟩ := pushStarValue_props (n + k) gs0 (uS : ℕ) vsU
      hgs0_ok (by omega) (by
        intro v hv
        obtain ⟨v', _, rfl⟩ := List.mem_map.1 hv
        omega) hvsUne
    set rV := pushStarValue (n + k) gs0 (uS : ℕ) vsU with hrV
    set starsRest : List (ℕ × List ℕ) :=
      (S.erase uS).toList.map (fun u : Fin n => ((u : ℕ), (N u).toList.map Fin.val))
      with hrest
    have hrest_bound : ∀ p ∈ starsRest, p.1 < n + k ∧ ∀ v ∈ p.2, v < n + k := by
      intro p hp
      obtain ⟨u, _, rfl⟩ := List.mem_map.1 hp
      refine ⟨by omega, ?_⟩
      intro v hv
      obtain ⟨v', _, rfl⟩ := List.mem_map.1 hv
      omega
    obtain ⟨hokS, hlenS, hltS, hevS⟩ := pushStars_props (n + k) starsRest rV.1 rV.2
      hokV hltV hrest_bound
    set rF := pushStars (n + k) rV.1 rV.2 starsRest with hrF
    set gsAnd : List Gate := rF.1 ++ [⟨GateOp.and, [rF.2, gOut]⟩] with hgsAnd
    have hokAnd : ∀ g ∈ gsAnd, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hokS g h
      · simp at h; subst h; simp [OkGate]
    have hrest_sum :
        (starsRest.map (fun p => p.2.length + 1)).sum + ((N uS).card + 1) =
          G.edgeFinset.card + t := by
      have hmap : starsRest.map (fun p => p.2.length + 1) =
          (S.erase uS).toList.map (fun u : Fin n => (N u).card + 1) := by
        simp [hrest, List.map_map, Function.comp_def]
      have hsum_list : ((S.erase uS).toList.map (fun u : Fin n => (N u).card + 1)).sum =
          ∑ u ∈ S.erase uS, ((N u).card + 1) := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
      have hsplit : ∑ u ∈ S, ((N u).card + 1) =
          ∑ u ∈ S.erase uS, ((N u).card + 1) + ((N uS).card + 1) := by
        rw [← Finset.sum_erase_add _ _ huS]
      have hfull : ∑ u ∈ S, ((N u).card + 1) = G.edgeFinset.card + t := by
        rw [Finset.sum_add_distrib, hsum_N, Finset.sum_const, smul_eq_mul, mul_one, hS_card]
      rw [hmap, hsum_list, ← hsplit, hfull]
    have hlen_tot : gsAnd.length ≤ s := by
      have hCg_sz' : Cg.gates.length ≤ c := hCg_sz
      have hvsUlen : vsU.length = (N uS).card := by simp [hvsU]
      have hAnd : gsAnd.length = rF.1.length + 1 := by simp [hgsAnd]
      have hRV : rV.1.length ≤ gs0.length + vsU.length := hlenV
      have hRF : rF.1.length ≤ rV.1.length + (starsRest.map (fun p => p.2.length + 1)).sum := hlenS
      omega
    refine ⟨⟨gsAnd, n + k + rF.1.length⟩, hokAnd, hlen_tot, ?_⟩
    intro x
    have hxlen : (List.ofFn x).length = n + k := by simp
    obtain ⟨hpresV, hvalV⟩ := hevV (List.ofFn x) hxlen
    obtain ⟨hpresF, hvalF⟩ := hevS (List.ofFn x) hxlen
    have hand : (wiresFrom gsAnd (List.ofFn x)).getD (n + k + rF.1.length) false =
        ((wiresFrom rF.1 (List.ofFn x)).getD rF.2 false &&
          (wiresFrom rF.1 (List.ofFn x)).getD gOut false) := by
      simp only [hgsAnd, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
      rw [getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length]; simp [hxlen])]
      simp [GateOp.eval]
    have hg_pres : (wiresFrom rF.1 (List.ofFn x)).getD gOut false =
        g (fun j : Fin k => x (Fin.natAdd n j)) := by
      have hg0 : Cg.output + n < n + k + gs0.length := by
        have h1 := hCg_out; have h2 := hgs0_len; omega
      have hgV : Cg.output + n < n + k + rV.1.length := by
        have hge := hlenV_ge; have h1 := hCg_out; have h2 := hgs0_len; omega
      have h1 := hpresV (Cg.output + n) hg0
      have h2 := hpresF (Cg.output + n) hgV
      simpa [gOut] using (h2.trans (h1.trans (hgs0_eval x)))
    have hstars_split :
        stars.any (fun p => (wiresFrom gs0 (List.ofFn x)).getD p.1 false &&
          p.2.any (fun v => (wiresFrom gs0 (List.ofFn x)).getD v false)) =
        (((wiresFrom gs0 (List.ofFn x)).getD (uS : ℕ) false &&
            vsU.any (fun v => (wiresFrom gs0 (List.ofFn x)).getD v false)) ||
          starsRest.any (fun p => (wiresFrom gs0 (List.ofFn x)).getD p.1 false &&
            p.2.any (fun v => (wiresFrom gs0 (List.ofFn x)).getD v false))) := by
      apply Bool.eq_iff_iff.2
      simp only [hstars, hrest, hvsU, List.any_map, List.any_eq_true, Function.comp_apply,
        Bool.and_eq_true, Bool.or_eq_true, Finset.mem_toList]
      constructor
      · rintro ⟨u, hu, hux, v, hv, hvx⟩
        by_cases heq : u = uS
        · subst heq
          exact Or.inl ⟨hux, v, hv, hvx⟩
        · exact Or.inr ⟨u, Finset.mem_erase.2 ⟨heq, hu⟩, hux, v, hv, hvx⟩
      · rintro (⟨hux, v, hv, hvx⟩ | ⟨u, hu, hux, v, hv, hvx⟩)
        · exact ⟨uS, huS, hux, v, hv, hvx⟩
        · exact ⟨u, Finset.mem_of_mem_erase hu, hux, v, hv, hvx⟩
    have hForest' :
        (wiresFrom rF.1 (List.ofFn x)).getD rF.2 false =
          decide (∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧
            x (Fin.castAdd k v) = true) := by
      have hrest_pres : starsRest.any (fun p => (wiresFrom rV.1 (List.ofFn x)).getD p.1 false &&
            p.2.any (fun v => (wiresFrom rV.1 (List.ofFn x)).getD v false)) =
          starsRest.any (fun p => (wiresFrom gs0 (List.ofFn x)).getD p.1 false &&
            p.2.any (fun v => (wiresFrom gs0 (List.ofFn x)).getD v false)) := by
        refine list_any_congr_mem fun p hp => ?_
        have hpm := hrest_bound p hp
        rw [hpresV p.1 (by omega)]
        congr 1
        exact list_any_congr_mem fun v hv => hpresV v (by have := hpm.2 v hv; omega)
      rw [hvalF, hvalV, hrest_pres, ← hstars_split, hS_eq0 x]
    show (wiresFrom gsAnd (List.ofFn x)).getD (n + k + rF.1.length) false = forestFun G A g x
    simp only [forestFun, hAempty, Finset.notMem_empty, false_and, exists_false, false_or]
    rw [hand, hForest', hg_pres]

end PEqualNP.Outside.L_meta_313

theorem PEqualNP.Outside.L_meta_313 :
    ∀ (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), G.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) && g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ A.card + G.edgeFinset.card + t + c ≤ s) := by
  intro n k c t s G _ A g hAcyc hA_iso hAct hg_nc hg_sz hvc_ex hvc_min
  exact ⟨PEqualNP.Outside.L_meta_313.lower_bound_aux hg_nc hg_sz s G A hAcyc hA_iso hAct ⟨hvc_ex, hvc_min⟩,
    PEqualNP.Outside.L_meta_313.upper_bound_aux G A g hg_nc hg_sz hAct hvc_ex⟩
