import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1576

open PEqualNP.CircuitLowerBounds

def r_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma r_step_len (w : List Bool) (g : Gate) : (r_step w g).length = w.length + 1 := by
  simp [r_step]

lemma r_step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (r_step w g).getD i false = w.getD i false := by
  simp [r_step, List.getD, List.getElem?_append_left hi]

lemma r_step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (r_step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [r_step, List.getD]

def r_W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl r_step (List.ofFn x)

lemma r_W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (r_W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl r_step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, r_step_len, List.length_cons]
      omega
  rw [r_W, h]
  simp

lemma r_W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    r_W (gs ++ [g]) x = r_step (r_W gs x) g := by
  simp [r_W, List.foldl_append]

lemma r_W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (r_W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (r_W gs x).getD i false)
      else (r_W gs x).getD t false := by
  rw [r_W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, r_step_last _ _ _ (by rw [r_W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact r_step_lt _ _ _ (by rw [r_W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [r_step_len, r_W_len]; omega),
        List.getD_eq_default _ _ (by rw [r_W_len]; omega)]

def r_Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (r_W new x).getD j false = f x)

def r_Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def r_Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ r_Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma r_rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : r_Rep new f) : r_Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma r_rep_mono {n : ℕ} {new new' : List Gate} (he : r_Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : r_Rep new f) : r_Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [r_W_val, if_neg hne]
      exact hv x

lemma r_rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : r_Rep new f)
    (hg : r_Rep new g) : ∃ new', r_Ext n new new' ∧ r_Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, r_rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (r_W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (r_W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [r_W_val, if_pos rfl]
      show GateOp.and.eval [(r_W new x).getD j false, (r_W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma r_rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : r_Rep new f)
    (hg : r_Rep new g) : ∃ new', r_Ext n new new' ∧ r_Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, r_rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (r_W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (r_W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [r_W_val, if_pos rfl]
      show GateOp.or.eval [(r_W new x).getD j false, (r_W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma r_rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    r_Rep ([] : List Gate) (fun x => (r_W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (r_W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (r_W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (r_W [] x).getD t false = (r_W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [r_W_len, List.length_nil]; omega)⟩

lemma r_gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, r_Rep new (fun x => (r_W old (ρ x)).getD t false)) :
    ∃ new', r_Ext n new new' ∧
      r_Rep new' (fun x => op.eval (l.map fun i => (r_W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, r_rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, r_rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := r_rep_and new _ _ (h a) (h b)
      exact ⟨new', he, r_rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := r_rep_or new _ _ (h a) (h b)
      exact ⟨new', he, r_rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def r_RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma r_rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : r_RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : r_RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def r_Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, r_Fan g) ∧ r_RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, r_Rep new (fun x => (r_W old (ρ x)).getD t false)

lemma r_inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : r_Inv ρ old) : r_Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := r_gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact r_rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact r_rep_congr (fun x => by
        show _ = (r_W (old ++ [g]) (ρ x)).getD t false
        rw [r_W_val, if_pos ht]) hr
    · exact r_rep_congr (fun x => by
        show _ = (r_W (old ++ [g]) (ρ x)).getD t false
        rw [r_W_val, if_neg ht]) (r_rep_mono he _ (hrep t))

lemma r_inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    r_Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → r_Inv ρ pre → r_Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (r_inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, r_rep_input ρ hρ⟩

lemma r_eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (r_W gs x).getD o false := rfl

def s_wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem s_eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (s_wf gs x).getD o false := rfl

theorem s_wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    s_wf (gs ++ [g]) w = s_wf gs w ++ [g.op.eval (g.inputs.map fun i => (s_wf gs w).getD i false)] := by
  simp [s_wf, List.foldl_append]

theorem s_wf_len (gs : List Gate) : ∀ w : List Bool, (s_wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [s_wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [s_wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem s_wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (s_wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [s_wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem s_wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (s_wf (pre ++ post) w).getD i false = (s_wf pre w).getD i false := by
  have : s_wf (pre ++ post) w = s_wf post (s_wf pre w) := by simp [s_wf, List.foldl_append]
  rw [this]
  exact s_wf_keep post _ i (by rw [s_wf_len]; exact hi)

theorem s_getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem s_getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem s_getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem s_wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (s_wf gates X).getD i false = (s_wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact s_wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem s_gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (s_wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (s_wf (gates.take k) X).getD i false) := by
  rw [s_wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, s_wf_snoc]
  have := s_getD_snoc_eq (s_wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (s_wf (gates.take k) X).getD i false))
  rw [s_wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def s_val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (s_wf gates (List.ofFn x)).getD w false

theorem s_iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (s_wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ s_val gates i x = true := by
  by_cases hi : i < n + k
  · rw [s_val, s_wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [s_wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem s_val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    s_val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ s_val gates i x = true := by
  have := s_gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [s_val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (s_iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (s_iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem s_val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    s_val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ s_val gates i x = true := by
  have := s_gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [s_val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (s_iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (s_iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem s_val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    s_val gates w x = x ⟨w, hw⟩ := by
  rw [s_val, s_wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem s_val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : s_val gates w x = false := by
  rw [s_val, List.getD_eq_default _ _ (by rw [s_wf_len]; simpa using hw)]

def s_Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → s_val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (s_val gates a (τ y) = true ∨ s_val gates b (τ y) = true) →
      (s_val gates a (τ y') = true ∨ s_val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def s_Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → s_Cl gates M c τ i X

def s_Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ s_val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      s_val gates w1 (τ r) = true ∧ s_val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ s_Con gates M c τ (g : ℕ) X

theorem s_single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : s_Con gates M c τ k X) :
    ∀ w, w < n + k → s_val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      s_val gates w (τ y) = true → s_val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [s_val_input gates _ w hwn] at hwc h1 h2
      have hm := hc _ hwc
      have e1 := (hτ y hy _ hm).1 h1
      have e2 := (hτ y' hy' _ hm).1 h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : 1 ≤ gates[w - n].inputs.length ∧ ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, s_val gates j c = false := by
          by_contra hne
          have hall : s_val gates (n + (w - n)) c = true := by
            apply (s_val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp.2 j hj, ?_⟩
            cases hv : s_val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp.2 j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((s_val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((s_val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, s_val gates j c = false := by
          intro j hj
          cases hv : s_val gates j c with
          | false => rfl
          | true =>
            have ht : s_val gates (n + (w - n)) c = true :=
              (s_val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp.2 j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (s_val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (s_val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp.2 a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : s_val gates a (τ y) = true ∨ s_val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : s_val gates a (τ y') = true ∨ s_val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem s_con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    s_Con gates M c τ (k + 1) X ↔ s_Con gates M c τ k X ∧ s_Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem s_con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : s_Con gates M c τ k X) :
    s_Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem s_con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : s_Con gates M c τ k X)
    (hY : s_Con gates M c τ k Y) : s_Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem s_con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : s_Con gates M c τ k X) :
    s_Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem s_cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, s_val gates a (τ y) = true → s_val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, s_val gates b (τ y) = true → s_val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, s_val gates a (τ y) = true → s_val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : s_Cl gates M c τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

theorem s_symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def s_P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => s_Con gates M c τ k X)

open Classical in
theorem s_symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ s_P gates M c τ k)
    (hY : Y ⊆ M) (hYc : s_Con gates M c τ k Y) : symmDiff X Y ∈ s_P gates M c τ k := by
  rw [s_P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, s_con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem s_step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (s_P gates M c τ ((g : ℕ) + 1)).card * (if s_Mrg gates M c τ g then 2 else 1)
      = (s_P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ s_val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ s_Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : s_P gates M c τ ((g : ℕ) + 1) = s_P gates M c τ (g : ℕ) := by
      unfold s_P
      apply Finset.filter_congr
      intro X _
      rw [s_con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    rw [hP, if_neg hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := (hin g).2 a hma
    have hb : b < n + (g : ℕ) := (hin g).2 b hmb
    have hac : s_val gates a c = false := by
      cases hv : s_val gates a c with
      | false => rfl
      | true =>
        have ht : s_val gates (n + (g : ℕ)) c = true :=
          (s_val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : s_val gates b c = false := by
      cases hv : s_val gates b c with
      | false => rfl
      | true =>
        have ht : s_val gates (n + (g : ℕ)) c = true :=
          (s_val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, s_Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, s_val gates a (τ y) = true →
        s_val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      s_single gates M c τ hc hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, s_Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, s_val gates b (τ y) = true →
        s_val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      s_single gates M c τ hc hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, s_val gates a (τ r) = true ∧ s_val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ s_Con gates M c τ (g : ℕ) X
    · have hmrg : s_Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [if_pos hmrg]
      have hP : s_P gates M c τ ((g : ℕ) + 1)
          = (s_P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold s_P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [s_con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, s_cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := s_P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := s_con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((s_P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((s_P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨s_symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (s_symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨s_symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (s_symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ s_Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [if_neg hnm, Nat.mul_one]
      congr 1
      unfold s_P
      apply Finset.filter_congr
      intro X _
      rw [s_con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, s_cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, s_con_compl gates M c τ g X h⟩

open Classical in
theorem s_count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (s_P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ s_Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : s_P gates M c τ 0 = M.powerset := by
      unfold s_P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (s_P gates M c τ (k + 1)).card * (if s_Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (s_P gates M c τ k).card := s_step gates M c τ hc hτ legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ s_Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ s_Mrg gates M c τ g then 1 else 0)
          + (if s_Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ s_Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ s_Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if s_Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring

open Classical in
theorem s_three {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : M.card = 4) (o : ℕ) (hoc : s_val gates o c = false)
    (hot : ∀ p ∈ M, s_val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if s_Mrg gates M c τ g then 1 else 0) = 3 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := s_val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : s_P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [s_P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := s_single gates M c τ hc hτ legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := s_count gates M c τ hc hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hM, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ s_Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if s_Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have h8 : 2 ^ (∑ g : Fin gates.length, if s_Mrg gates M c τ g then 1 else 0) = 2 ^ 3 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans (by norm_num))
  exact Nat.pow_right_injective (le_refl 2) h8

def s_lines (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

lemma s_card4 : ∀ t : Fin 13, (s_lines t).card = 4 := by
  decide +kernel

open Classical in
theorem s_total (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List Gate) (o : Fin 13 → ℕ)
    (mg : Fin gates.length → ℕ)
    (hT : ∀ t : Fin 13, ∀ p ∈ s_lines t, ∀ v ∈ s_lines t, T t p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hoc : ∀ t : Fin 13, s_val gates (o t) (fun v : Fin 13 => decide (v ∉ s_lines t)) = false)
    (hot : ∀ t : Fin 13, ∀ p ∈ s_lines t, s_val gates (o t) (T t p) = true)
    (hR : ∀ g : Fin gates.length, ∃ R : Finset (Fin 13),
      (∀ t : Fin 13, t ∈ R ↔
        s_Mrg gates (s_lines t) (fun v : Fin 13 => decide (v ∉ s_lines t)) (T t) g) ∧ mg g = R.card)
    (E : Finset (Fin gates.length))
    (hE : ∀ g : Fin gates.length, g ∈ E ↔
      ((gates.get g).op = GateOp.and ∨ ((gates.get g).op = GateOp.or ∧ mg g = 0))) :
    gates.length + ∑ g : Fin gates.length, (mg g - 1) = 39 + E.card := by
  have h3 : ∀ t : Fin 13, (∑ g : Fin gates.length,
      if s_Mrg gates (s_lines t) (fun v : Fin 13 => decide (v ∉ s_lines t)) (T t) g then 1 else 0) = 3 :=
    fun t => s_three gates (s_lines t) _ (T t) (fun v hv => by simpa using hv) (hT t) legal hin
      (s_card4 t) (o t) (hoc t) (hot t)
  have hmg : ∀ g : Fin gates.length, mg g = ∑ t : Fin 13,
      if s_Mrg gates (s_lines t) (fun v : Fin 13 => decide (v ∉ s_lines t)) (T t) g then 1 else 0 := by
    intro g
    obtain ⟨R, hR1, hR2⟩ := hR g
    have hRe : R = Finset.univ.filter
        (fun t => s_Mrg gates (s_lines t) (fun v : Fin 13 => decide (v ∉ s_lines t)) (T t) g) := by
      ext t
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      exact hR1 t
    rw [hR2, hRe, Finset.card_filter]
  have hsum : ∑ g : Fin gates.length, mg g = 39 := by
    rw [Finset.sum_congr rfl (fun g _ => hmg g), Finset.sum_comm,
      Finset.sum_congr rfl (fun t _ => h3 t)]
    simp
  have hE' : ∀ g : Fin gates.length, g ∈ E ↔ mg g = 0 := by
    intro g
    rw [hE g]
    constructor
    · rintro (ha | ⟨_, h0⟩)
      · rw [hmg g]
        apply Finset.sum_eq_zero
        intro t _
        rw [if_neg]
        rintro ⟨ho, _⟩
        rw [ha] at ho
        exact GateOp.noConfusion ho
      · exact h0
    · intro h0
      rcases (legal gates[(g : ℕ)] (List.getElem_mem g.2)).1 with ha | ho
      · exact Or.inl ha
      · exact Or.inr ⟨ho, h0⟩
  have hEc : E.card = ∑ g : Fin gates.length, if mg g = 0 then 1 else 0 := by
    have hEe : E = Finset.univ.filter (fun g => mg g = 0) := by
      ext g
      simp [hE' g]
    rw [hEe, Finset.card_filter]
  have hlen : (∑ _g : Fin gates.length, 1) = gates.length := by simp
  calc gates.length + ∑ g : Fin gates.length, (mg g - 1)
      = (∑ _g : Fin gates.length, 1) + ∑ g : Fin gates.length, (mg g - 1) := by rw [hlen]
    _ = ∑ g : Fin gates.length, (1 + (mg g - 1)) := Finset.sum_add_distrib.symm
    _ = ∑ g : Fin gates.length, (mg g + if mg g = 0 then 1 else 0) :=
        Finset.sum_congr rfl (fun g _ => by split_ifs <;> omega)
    _ = (∑ g : Fin gates.length, mg g) + ∑ g : Fin gates.length, if mg g = 0 then 1 else 0 :=
        Finset.sum_add_distrib
    _ = 39 + E.card := by rw [hsum, hEc]

def e_wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem e_eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (e_wf gs x).getD o false := rfl

theorem e_wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    e_wf (gs ++ [g]) w = e_wf gs w ++ [g.op.eval (g.inputs.map fun i => (e_wf gs w).getD i false)] := by
  simp [e_wf, List.foldl_append]

theorem e_wf_len (gs : List Gate) : ∀ w : List Bool, (e_wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [e_wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [e_wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem e_wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (e_wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [e_wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem e_wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (e_wf (pre ++ post) w).getD i false = (e_wf pre w).getD i false := by
  have : e_wf (pre ++ post) w = e_wf post (e_wf pre w) := by simp [e_wf, List.foldl_append]
  rw [this]
  exact e_wf_keep post _ i (by rw [e_wf_len]; exact hi)

theorem e_getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem e_getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem e_getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem e_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem e_ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem e_mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (e_wf gs U).getD i false = true → (e_wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [e_getD_snoc_lt _ _ _ ht, e_getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [e_getD_snoc_eq]
          have e2 := e_getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact e_eval_mono g.op hg g.inputs U V h
        · rw [e_getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [e_wf] using this

def e_Lf (s : Fin 13) : Finset (Fin 13) := {s, s + 1, s + 3, s + 9}

theorem e_meet_one : ∀ t u p q : Fin 13, t ≠ u → p ∈ e_Lf t → p ∈ e_Lf u → q ∈ e_Lf t → q ∈ e_Lf u →
    p = q := by decide

theorem e_half (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List Gate) (g : ℕ) (t u : Fin 13)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htu : t ≠ u)
    (hu : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ e_Lf u))) = false)
    (h2 : 2 ≤ ((e_Lf t).filter (fun p => Circuit.eval ⟨gates, g⟩ (List.ofFn (T t p)) = true)).card) :
    ∃ p ∈ e_Lf t \ e_Lf u, ∃ v ∈ e_Lf u, (T t p) v = true := by
  obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.1 h2
  rw [Finset.mem_filter] at hp1 hp2
  have key : ∀ p, p ∈ e_Lf t → p ∉ e_Lf u →
      Circuit.eval ⟨gates, g⟩ (List.ofFn (T t p)) = true →
      ∃ p ∈ e_Lf t \ e_Lf u, ∃ v ∈ e_Lf u, (T t p) v = true := by
    intro p hp hpu htrue
    refine ⟨p, Finset.mem_sdiff.2 ⟨hp, hpu⟩, ?_⟩
    by_contra hcon
    push_neg at hcon
    rw [e_eval_eq] at htrue hu
    have := e_mono2 gates hleg (List.ofFn (T t p)) (List.ofFn (fun v : Fin 13 => decide (v ∉ e_Lf u)))
      (by simp) (by
        apply e_ofFn_mono
        intro v hv
        have : v ∉ e_Lf u := fun hin => by
          have := hcon v hin
          rw [hv] at this
          exact absurd this (by simp)
        simp [this]) g htrue
    rw [this] at hu
    exact absurd hu (by simp)
  by_cases h1 : p1 ∈ e_Lf u
  · by_cases h2' : p2 ∈ e_Lf u
    · exact absurd (e_meet_one t u p1 p2 htu hp1.1 h1 hp2.1 h2') hne
    · exact key p2 hp2.1 h2' hp2.2
  · exact key p1 hp1.1 h1 hp1.2

def c_Ln (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

abbrev c_R (t u : Fin 13) : Prop := t ≠ u ∧ (∃ p ∈ c_Ln t \ c_Ln u, ∃ v ∈ c_Ln u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ c_Ln t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ c_Ln 0 else ∅))) v = true) ∧ (∃ p ∈ c_Ln u \ c_Ln t, ∃ v ∈ c_Ln t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ c_Ln u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ c_Ln 0 else ∅))) v = true)


abbrev c_G (t u : Fin 13) : Prop := (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13)))


theorem c_hR : ∀ t u : Fin 13, c_R t u ↔ c_G t u := by decide

theorem c_quad_b : ∀ a b c d : Fin 13, a ≠ b → a ≠ c → b ≠ c → d ≠ a → d ≠ b → d ≠ c → decide (c_G a b) = true → decide (c_G a c) = true → decide (c_G b c) = true → decide (c_G d a) = true → decide (c_G d b) = true → decide (c_G d c) = true → False := by decide +kernel

theorem c_quad : ∀ a b c d : Fin 13, a ≠ b → a ≠ c → b ≠ c → d ≠ a → d ≠ b → d ≠ c → c_G a b → c_G a c → c_G b c → c_G d a → c_G d b → c_G d c → False :=
  fun a b c d h1 h2 h3 h4 h5 h6 g1 g2 g3 g4 g5 g6 => c_quad_b a b c d h1 h2 h3 h4 h5 h6 (decide_eq_true g1) (decide_eq_true g2) (decide_eq_true g3) (decide_eq_true g4) (decide_eq_true g5) (decide_eq_true g6)

theorem c_tri_b : ∀ a b c : Fin 13, a ≠ b → a ≠ c → b ≠ c → decide (c_G a b) = true → decide (c_G a c) = true → decide (c_G b c) = true → ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ x : Fin 13, (x = a ∨ x = b ∨ x = c) ↔ (x = 0 ∨ x = l ∨ x = m) := by decide +kernel

theorem c_tri : ∀ a b c : Fin 13, a ≠ b → a ≠ c → b ≠ c → c_G a b → c_G a c → c_G b c → ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ x : Fin 13, (x = a ∨ x = b ∨ x = c) ↔ (x = 0 ∨ x = l ∨ x = m) :=
  fun a b c h1 h2 h3 g1 g2 g3 => c_tri_b a b c h1 h2 h3 (decide_eq_true g1) (decide_eq_true g2) (decide_eq_true g3)

theorem c_back : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ t ∈ ({0, l, m} : Finset (Fin 13)), ∀ u ∈ ({0, l, m} : Finset (Fin 13)), t ≠ u → c_G t u := by decide

theorem c_p2 (K : Finset (Fin 13)) (hK : 3 ≤ K.card) : (∀ t ∈ K, ∀ u ∈ K, t ≠ u → c_G t u) ↔ ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m} := by
  constructor
  · intro hc
    obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hK
    have hKe : K = {a, b, c} := by
      apply Finset.Subset.antisymm
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hne
        push Not at hne
        exact c_quad a b c d hab hac hbc hne.1 hne.2.1 hne.2.2 (hc a ha b hb hab) (hc a ha c hc' hac) (hc b hb c hc' hbc) (hc d hd a ha hne.1) (hc d hd b hb hne.2.1) (hc d hd c hc' hne.2.2)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    obtain ⟨l, hl, m, hm, h⟩ := c_tri a b c hab hac hbc (hc a ha b hb hab) (hc a ha c hc' hac) (hc b hb c hc' hbc)
    refine ⟨l, hl, m, hm, ?_⟩
    rw [hKe]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact h x
  · rintro ⟨l, hl, m, hm, rfl⟩
    exact c_back l hl m hm

abbrev c_Q (K : Finset (Fin 13)) : Prop := K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) + (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)


theorem c_one : ∀ a : Fin 13, c_Q {a} := by decide

theorem c_two : ∀ a b : Fin 13, a ≠ b → c_G a b → c_Q {a, b} := by decide

theorem c_three : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), c_Q {0, l, m} := by decide

theorem c_p3 (K : Finset (Fin 13)) (h1 : 1 ≤ K.card) (hc : ∀ t ∈ K, ∀ u ∈ K, t ≠ u → c_G t u) : c_Q K := by
  rcases (show K.card = 1 ∨ K.card = 2 ∨ 3 ≤ K.card by omega) with h | h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    exact c_one a
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h
    exact c_two a b hab (hc a (by simp) b (by simp) hab)
  · obtain ⟨l, hl, m, hm, rfl⟩ := (c_p2 K h).1 hc
    exact c_three l hl m hm

theorem c_main : (∀ t u : Fin 13, c_R t u ↔ c_G t u) ∧ (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → c_R t u) ↔ ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧ (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → c_R t u) → c_Q K) := by
  refine ⟨c_hR, fun K hK => ?_, fun K hK hc => ?_⟩
  · simp only [c_hR]
    exact c_p2 K hK
  · simp only [c_hR] at hc
    exact c_p3 K hK hc

set_option maxRecDepth 100000 in
theorem k_per_set : ∀ F : Finset (Fin 13),
    (∀ t ∈ F, ∀ u ∈ F, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) →
    F.card - 1 = (if (0 : Fin 13) ∈ F ∧ 2 ≤ F.card then 1 else 0) +
      (if ∃ l ∈ F, ∃ m ∈ F, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0) := by
  decide +kernel

theorem o_W_len (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem o_W_pre (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false
      = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp only [List.length_append]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem o_eval_lt (gs : List Gate) (o : ℕ) (x : List Bool) (h : o < x.length) :
    Circuit.eval ⟨gs, o⟩ x = x.getD o false := by
  unfold Circuit.eval Circuit.wires
  exact o_W_pre gs x o h

theorem o_eval_ge (gs : List Gate) (o : ℕ) (x : List Bool) (h : x.length + gs.length ≤ o) :
    Circuit.eval ⟨gs, o⟩ x = false := by
  unfold Circuit.eval Circuit.wires
  apply List.getD_eq_default
  rw [o_W_len]
  exact h

theorem o_getD_ofFn (f : Fin 13 → Bool) (i : ℕ) (h : i < 13) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  rfl

set_option maxRecDepth 100000 in
theorem o_fact_mem : ∀ t : Fin 13, t ≠ 0 →
    ((0 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∨
     (1 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13))) := by
  decide

set_option maxRecDepth 100000 in
theorem o_fact_ex : ∀ t : Fin 13, t ≠ 0 →
    ∃ v ∈ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)),
      v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  decide

set_option maxRecDepth 100000 in
theorem o_fact_no : ¬ ∃ v ∈ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)),
      v ∉ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)) := by
  decide

theorem o_main_aux : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _ _ hout
  have h0 := hout 0 (fun v => decide (v = 0)) (Or.inl (by decide))
  have h1 := hout 0 (fun v => decide (v = 1)) (Or.inr (Or.inl (by decide)))
  have h2 := hout 0 (fun v => decide (v ∉ L 0))
    (Or.inr (Or.inr (fun v hv => decide_eq_true hv)))
  have e0 : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true := by
    rw [h0, decide_eq_true_eq]
    refine ⟨0, ?_, by decide⟩
    rw [hL]
    decide
  have e1 : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true := by
    rw [h1, decide_eq_true_eq]
    refine ⟨1, ?_, by decide⟩
    rw [hL]
    decide
  have e2 : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false := by
    rw [h2, decide_eq_false_iff_not]
    rintro ⟨v, hv, hv2⟩
    exact (of_decide_eq_true hv2) hv
  have e3 : ∀ t : Fin 13, t ≠ 0 →
      Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
    intro t ht
    have hx : (fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨
        (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨
        ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true := by
      rcases o_fact_mem t ht with a | a
      · exact Or.inl (decide_eq_true (by rw [hL]; exact a))
      · exact Or.inr (Or.inl (decide_eq_true (by rw [hL]; exact a)))
    rw [hout 0 _ hx, decide_eq_true_eq]
    obtain ⟨v, hv, hv2⟩ := o_fact_ex t ht
    exact ⟨v, by rw [hL]; exact hv, decide_eq_true (by rw [hL]; exact hv2)⟩
  refine ⟨?_, ?_, e0, e1, e2, e3⟩
  · by_contra hlt
    have hlt2 : o 0 < 13 := by omega
    have a0 := o_eval_lt gates (o 0) (List.ofFn (fun v : Fin 13 => decide (v = 0)))
      (by rw [List.length_ofFn]; exact hlt2)
    have a1 := o_eval_lt gates (o 0) (List.ofFn (fun v : Fin 13 => decide (v = 1)))
      (by rw [List.length_ofFn]; exact hlt2)
    rw [e0, o_getD_ofFn _ _ hlt2] at a0
    rw [e1, o_getD_ofFn _ _ hlt2] at a1
    have b0 : (⟨o 0, hlt2⟩ : Fin 13) = 0 := of_decide_eq_true a0.symm
    have b1 : (⟨o 0, hlt2⟩ : Fin 13) = 1 := of_decide_eq_true a1.symm
    have c : (0 : Fin 13) = 1 := b0.symm.trans b1
    exact absurd c (by decide)
  · by_contra hge
    have a0 := o_eval_ge gates (o 0) (List.ofFn (fun v : Fin 13 => decide (v = 0)))
      (by rw [List.length_ofFn]; omega)
    rw [e0] at a0
    exact Bool.noConfusion a0

set_option maxRecDepth 100000 in
theorem t_main_aux : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ t : Fin 13, ∀ p ∈ L t,
      ((fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) 0 = true ∨ (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧
      (∀ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true ↔ v = p) ∧
      (∀ v : Fin 13, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true → v ≠ p → v ∉ L t) := by
  intro L hL
  obtain rfl : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  decide +kernel

theorem e_main : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t u : Fin 13),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → t ≠ u →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L u))) = false →
    2 ≤ ((L t).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (T t p)) = true)).card →
    2 ≤ ((L u).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (T u p)) = true)).card →
    (∃ p ∈ L t \ L u, ∃ v ∈ L u, (T t p) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (T u p) v = true) := by
  intro L hL T gates g t u _ hleg htu ht hu h2t h2u
  have hLf : L = e_Lf := by funext s; rw [hL s]; rfl
  subst hLf
  exact ⟨e_half T gates g t u hleg htu hu h2t, e_half T gates g u t hleg (Ne.symm htu) ht h2u⟩

theorem c_all : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ t u : Fin 13, (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true)) ↔
      (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13)))) ∧
    (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) ↔
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧
    (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) →
      K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
        (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)) := by
  intro L hL
  obtain rfl : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  exact c_main

theorem k_main : ∀ (k : ℕ) (K : Fin k → Finset (Fin 13)),
    (∀ i : Fin k, ∀ t ∈ K i, ∀ u ∈ K i, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) →
    ∑ i : Fin k, ((K i).card - 1) =
      (Finset.univ.filter (fun i : Fin k => (0 : Fin 13) ∈ K i ∧ 2 ≤ (K i).card)).card +
      (Finset.univ.filter (fun i : Fin k => ∃ l ∈ K i, ∃ m ∈ K i, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))).card := by
  classical
  intro k K hK
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact k_per_set (K i) (hK i)

abbrev f_P := Fin 13

def f_line (t : f_P) : Finset f_P := {t, t + 1, t + 3, t + 9}
def f_LS : Finset f_P := {4, 10, 12}
def f_MS : Finset f_P := {1, 5, 11}

def f_coline (t : f_P) : f_P → Bool := fun v => decide (v ∉ f_line t)

def f_testInp (t y : f_P) : f_P → Bool :=
  fun v => decide (v = y ∨ (t ∈ f_LS ∧ y ≠ 0 ∧ v = 1) ∨ (t ∈ f_MS ∧ y ≠ 1 ∧ v = 0))

def f_run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma f_run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    f_run (g :: gs) x = f_run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma f_run_length (gs : List Gate) (x : List Bool) :
    (f_run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [f_run]
  | cons g gs ih => rw [f_run_cons, ih]; simp; omega

lemma f_run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (f_run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [f_run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma f_run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    f_run gs x = f_run (gs.drop j) (f_run (gs.take j) x) := by
  simpa only [f_run, List.foldl_append] using
    congrArg (fun l : List Gate => f_run l x) (List.take_append_drop j gs).symm

def f_val (gates : List Gate) (w : ℕ) (x : f_P → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn x)

lemma f_val_input (gates : List Gate) (p : f_P) (x : f_P → Bool) :
    f_val gates p.val x = x p := by
  change (f_run gates (List.ofFn x)).getD p.val false = x p
  have hp : p.val < (List.ofFn x).length := by simp
  rw [f_run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp only [List.getElem_ofFn, Fin.eta]

lemma f_val_gate (gates : List Gate) (i : Fin gates.length) (x : f_P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val) :
    f_val gates (13 + i.val) x =
      (gates.get i).op.eval ((gates.get i).inputs.map fun a => f_val gates a x) := by
  let j := i.val
  have hj : j < gates.length := i.isLt
  let g := gates[j]
  let earlier := f_run (gates.take j) (List.ofFn x)
  have plen : earlier.length = 13 + j := by
    simp [earlier, f_run_length, j]
  have split : f_run gates (List.ofFn x) = f_run (g :: gates.drop (j + 1)) earlier := by
    rw [f_run_split gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (a : ℕ) (ha : a < 13 + j) : earlier.getD a false = f_val gates a x := by
    change earlier.getD a false = (f_run gates (List.ofFn x)).getD a false
    rw [split]
    exact (f_run_getD _ earlier a (by simpa only [plen] using ha)).symm
  change (f_run gates (List.ofFn x)).getD (13 + j) false =
    g.op.eval (g.inputs.map fun a => f_val gates a x)
  rw (occs := [1]) [split]
  rw (occs := [1]) [f_run_cons]
  rw [f_run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact read a (hwf a ha)

lemma f_val_mono (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (x y : f_P → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w : ℕ, w < 13 + gates.length → f_val gates w x = true → f_val gates w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hx
    by_cases hw : w < 13
    · let p : f_P := ⟨w, hw⟩
      have hp : p.val = w := rfl
      rw [← hp, f_val_input] at hx ⊢
      exact hxy p hx
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hi : 13 + i.val = w := by change 13 + (w - 13) = w; omega
      rw [← hi, f_val_gate gates i x (hWF i).2] at hx
      rw [← hi, f_val_gate gates i y (hWF i).2]
      obtain ⟨hop, _⟩ := hG (gates.get i) (List.get_mem _ _)
      rcases hop with hop | hop
      · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hx ⊢
        intro a ha
        have hlt_a := (hWF i).2 a ha
        exact ih a (by omega) (by omega) (hx a ha)
      · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hx ⊢
        obtain ⟨a, ha, hva⟩ := hx
        have hlt_a := (hWF i).2 a ha
        exact ⟨a, ha, ih a (by omega) (by omega) hva⟩

lemma f_val_or_iff (gates : List Gate) (i : Fin gates.length) (x : f_P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.or) :
    f_val gates (13 + i.val) x = true ↔ ∃ a ∈ (gates.get i).inputs, f_val gates a x = true := by
  rw [f_val_gate gates i x hwf, hop]
  simp [GateOp.eval]

lemma f_val_or_false (gates : List Gate) (i : Fin gates.length) (x : f_P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.or)
    (hf : f_val gates (13 + i.val) x = false) {a : ℕ} (ha : a ∈ (gates.get i).inputs) :
    f_val gates a x = false := by
  cases h : f_val gates a x with
  | false => rfl
  | true =>
    have ht : f_val gates (13 + i.val) x = true := (f_val_or_iff gates i x hwf hop).mpr ⟨a, ha, h⟩
    rw [hf] at ht
    exact Bool.noConfusion ht

lemma f_val_and_true (gates : List Gate) (i : Fin gates.length) (x : f_P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.and)
    (ht : f_val gates (13 + i.val) x = true) {a : ℕ} (ha : a ∈ (gates.get i).inputs) :
    f_val gates a x = true := by
  rw [f_val_gate gates i x hwf] at ht
  simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at ht
  exact ht a ha

lemma f_val_and_false_exists (gates : List Gate) (i : Fin gates.length) (x : f_P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.and)
    (hf : f_val gates (13 + i.val) x = false) :
    ∃ a ∈ (gates.get i).inputs, f_val gates a x = false := by
  rw [f_val_gate gates i x hwf, hop] at hf
  simpa only [GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id_eq, Bool.not_eq_true] using hf

def f_CutRespect (gates : List Gate) (t : f_P) (g : Fin gates.length) (X : Finset f_P) : Prop :=
  ∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
    f_val gates (13 + i.val) (f_coline t) = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ f_line t, ∀ y' ∈ f_line t,
      (f_val gates a (f_testInp t y) = true ∨ f_val gates b (f_testInp t y) = true) →
      (f_val gates a (f_testInp t y') = true ∨ f_val gates b (f_testInp t y') = true) →
      (y ∈ X ↔ y' ∈ X)

def f_Merges (gates : List Gate) (t : f_P) (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧
  f_val gates (13 + g.val) (f_coline t) = false ∧
  ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧
    ∃ r ∈ f_line t, ∃ r' ∈ f_line t,
      f_val gates w1 (f_testInp t r) = true ∧ f_val gates w2 (f_testInp t r') = true ∧
      ∃ X : Finset f_P, r ∈ X ∧ r' ∉ X ∧ f_CutRespect gates t g X

def f_OrReach (gates : List Gate) (start target : ℕ) : Prop :=
  ∀ S : Set ℕ, start ∈ S →
    (∀ i : Fin gates.length, 13 + i.val ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) →
    target ∈ S

lemma f_orReach_refl (gates : List Gate) (w : ℕ) : f_OrReach gates w w :=
  fun _ h _ => h

lemma f_orReach_trans (gates : List Gate) {u v w : ℕ}
    (h1 : f_OrReach gates u v) (h2 : f_OrReach gates v w) : f_OrReach gates u w :=
  fun S hu hstep => h2 S (h1 S hu hstep) hstep

lemma f_orReach_step (gates : List Gate) (i : Fin gates.length)
    (hop : (gates.get i).op = GateOp.or) {a : ℕ} (ha : a ∈ (gates.get i).inputs) :
    f_OrReach gates (13 + i.val) a :=
  fun _ hi hstep => hstep i hi hop a ha

lemma f_orReach_le (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    {u v : ℕ} (h : f_OrReach gates u v) : v ≤ u :=
  h {w | w ≤ u} (by simp) fun i hi _ a ha => le_trans (le_of_lt ((hWF i).2 a ha)) hi

lemma f_orReach_false (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    {u v : ℕ} (h : f_OrReach gates u v) (x : f_P → Bool)
    (hu : f_val gates u x = false) : f_val gates v x = false :=
  h {w | f_val gates w x = false} hu fun i hi hop _ ha =>
    f_val_or_false gates i x (hWF i).2 hop hi ha

lemma f_orReach_find_stop (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (x : f_P → Bool) :
    ∀ w : ℕ, w < 13 + gates.length → f_val gates w x = true →
      (∃ v : f_P, f_OrReach gates w v.val ∧ x v = true) ∨
      (∃ z : Fin gates.length, (gates.get z).op = GateOp.and ∧
        f_OrReach gates w (13 + z.val) ∧ f_val gates (13 + z.val) x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hval
    by_cases hw : w < 13
    · let p : f_P := ⟨w, hw⟩
      have hp : p.val = w := rfl
      rw [← hp, f_val_input] at hval
      exact Or.inl ⟨p, f_orReach_refl gates w, hval⟩
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hi : 13 + i.val = w := by change 13 + (w - 13) = w; omega
      obtain ⟨hop | hop, _⟩ := hG (gates.get i) (List.get_mem _ _)
      · exact Or.inr ⟨i, hop, hi ▸ f_orReach_refl gates w, hi.symm ▸ hval⟩
      · rw [← hi] at hval
        obtain ⟨a, ha, hva⟩ := (f_val_or_iff gates i x (hWF i).2 hop).mp hval
        have hlt_a := (hWF i).2 a ha
        have hstep : f_OrReach gates w a := hi ▸ f_orReach_step gates i hop ha
        rcases ih a (by omega) (by omega) hva with ⟨v, hrv, hxv⟩ | ⟨z, hzop, hrz, hvz⟩
        · exact Or.inl ⟨v, f_orReach_trans gates hstep hrv, hxv⟩
        · exact Or.inr ⟨z, hzop, f_orReach_trans gates hstep hrz, hvz⟩

lemma f_testInp_in_line_eq : ∀ t : f_P, t ∈ f_LS ∨ t ∈ f_MS → ∀ y ∈ f_line t, ∀ v ∈ f_line t,
    f_testInp t y v = true → v = y := by decide

lemma f_testInp_base_le_coline_LM : ∀ l ∈ f_LS, ∀ m ∈ f_MS, ∀ v : f_P,
    f_testInp l 0 v = true → f_coline m v = true := by decide

lemma f_testInp_base_le_coline_ML : ∀ m ∈ f_MS, ∀ l ∈ f_LS, ∀ v : f_P,
    f_testInp m 1 v = true → f_coline l v = true := by decide

lemma f_testInp_other_le_coline_LL : ∀ l1 ∈ f_LS, ∀ l2 ∈ f_LS, l1 ≠ l2 → ∀ y ∈ f_line l1, y ≠ 0 → ∀ v : f_P,
    f_testInp l1 y v = true → f_coline l2 v = true := by decide

lemma f_testInp_other_le_coline_MM : ∀ m1 ∈ f_MS, ∀ m2 ∈ f_MS, m1 ≠ m2 → ∀ y ∈ f_line m1, y ≠ 1 → ∀ v : f_P,
    f_testInp m1 y v = true → f_coline m2 v = true := by decide

lemma f_inter_LM_card : ∀ l ∈ f_LS, ∀ m ∈ f_MS, (f_line l ∩ f_line m).card = 1 := by decide
lemma f_inter_ML_card : ∀ m ∈ f_MS, ∀ l ∈ f_LS, (f_line m ∩ f_line l).card = 1 := by decide
lemma f_line_sdiff_base_L : ∀ l ∈ f_LS, (f_line l \ {0}).card = 3 := by decide
lemma f_line_sdiff_base_M : ∀ m ∈ f_MS, (f_line m \ {1}).card = 3 := by decide

lemma f_wire_same_comp (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (t : f_P) (ht : t ∈ f_LS ∨ t ∈ f_MS) (g : Fin gates.length) (X : Finset f_P)
    (hcut : f_CutRespect gates t g X) :
    ∀ w : ℕ, w < 13 + g.val → f_val gates w (f_coline t) = false →
      ∀ y ∈ f_line t, ∀ y' ∈ f_line t,
        f_val gates w (f_testInp t y) = true → f_val gates w (f_testInp t y') = true →
        (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hcol y hy y' hy' hvy hvy'
    by_cases hw : w < 13
    · let v : f_P := ⟨w, hw⟩
      have hv : v.val = w := rfl
      rw [← hv, f_val_input] at hcol hvy hvy'
      have hvl : v ∈ f_line t := by simpa [f_coline] using hcol
      have heq1 := f_testInp_in_line_eq t ht y hy v hvl hvy
      have heq2 := f_testInp_in_line_eq t ht y' hy' v hvl hvy'
      rw [← heq1, ← heq2]
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hi : 13 + i.val = w := by change 13 + (w - 13) = w; omega
      have hig : i < g := by change i.val < g.val; omega
      obtain ⟨hop | hop, hlen⟩ := hG (gates.get i) (List.get_mem _ _)
      · rw [← hi] at hcol hvy hvy'
        obtain ⟨a, ha, hfa⟩ := f_val_and_false_exists gates i (f_coline t) (hWF i).2 hop hcol
        have hlt_a := (hWF i).2 a ha
        have hya := f_val_and_true gates i (f_testInp t y) (hWF i).2 hop hvy ha
        have hya' := f_val_and_true gates i (f_testInp t y') (hWF i).2 hop hvy' ha
        exact ih a (by omega) (by omega) hfa y hy y' hy' hya hya'
      · have hpos := (hWF i).1
        match hlist : (gates.get i).inputs with
        | [] => rw [hlist] at hpos; simp at hpos
        | [a] =>
          rw [← hi] at hcol hvy hvy'
          have hmem : a ∈ (gates.get i).inputs := by rw [hlist]; simp
          have hlt_a := (hWF i).2 a hmem
          have hfa := f_val_or_false gates i (f_coline t) (hWF i).2 hop hcol hmem
          have hya : f_val gates a (f_testInp t y) = true := by
            obtain ⟨c, hc, hvc⟩ := (f_val_or_iff gates i (f_testInp t y) (hWF i).2 hop).mp hvy
            rw [hlist] at hc; simp at hc; rwa [← hc]
          have hya' : f_val gates a (f_testInp t y') = true := by
            obtain ⟨c, hc, hvc⟩ := (f_val_or_iff gates i (f_testInp t y') (hWF i).2 hop).mp hvy'
            rw [hlist] at hc; simp at hc; rwa [← hc]
          exact ih a (by omega) (by omega) hfa y hy y' hy' hya hya'
        | [a, b] =>
          rw [← hi] at hcol hvy hvy'
          have hyab : f_val gates a (f_testInp t y) = true ∨ f_val gates b (f_testInp t y) = true := by
            obtain ⟨c, hc, hvc⟩ := (f_val_or_iff gates i (f_testInp t y) (hWF i).2 hop).mp hvy
            rw [hlist] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact Or.inl hvc
            · exact Or.inr hvc
          have hyab' : f_val gates a (f_testInp t y') = true ∨ f_val gates b (f_testInp t y') = true := by
            obtain ⟨c, hc, hvc⟩ := (f_val_or_iff gates i (f_testInp t y') (hWF i).2 hop).mp hvy'
            rw [hlist] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact Or.inl hvc
            · exact Or.inr hvc
          exact hcut i hig hop hcol a b hlist y hy y' hy' hyab hyab'
        | _ :: _ :: _ :: _ => rw [hlist] at hlen; simp at hlen

lemma f_mem_of_card_three {α : Type*} [DecidableEq α] {S : Finset α} (hcard : S.card = 3)
    {a b c : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ x ∈ S, x = a ∨ x = b ∨ x = c := by
  have hsub : ({a, b, c} : Finset α) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hbc]
    · simp [hab, hac]
  have heq : ({a, b, c} : Finset α) = S := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro x hx
  rw [← heq] at hx
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

lemma f_two_ordered_of_one_lt {α : Type*} [LinearOrder α] {S : Finset α} (h : 1 < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a < b := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact ⟨x, hx, y, hy, hlt⟩
  · exact ⟨y, hy, x, hx, hlt⟩

lemma f_three_ordered_of_two_lt {α : Type*} [LinearOrder α] {S : Finset α} (h : 2 < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a < b ∧ b < c := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  have h1 : 1 < (S.erase x).card := by
    rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y, hy, z, hz, hyz⟩ := f_two_ordered_of_one_lt h1
  have hyS : y ∈ S := (Finset.mem_erase.mp hy).2
  have hzS : z ∈ S := (Finset.mem_erase.mp hz).2
  have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
  have hxz : x ≠ z := (Finset.mem_erase.mp hz).1.symm
  rcases lt_or_gt_of_ne hxy with h1 | h1
  · exact ⟨x, hx, y, hyS, z, hzS, h1, hyz⟩
  · rcases lt_or_gt_of_ne hxz with h2 | h2
    · exact ⟨y, hyS, x, hx, z, hzS, h1, h2⟩
    · exact ⟨y, hyS, z, hzS, x, hx, hyz, h2⟩

lemma f_ne_base_of_or_true (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (t base : f_P) (g : Fin gates.length) (w1 w2 : ℕ) (r : f_P)
    (hop : (gates.get g).op = GateOp.or) (hin : (gates.get g).inputs = [w1, w2])
    (hb : f_val gates (13 + g.val) (f_testInp t base) = false)
    (hvr : f_val gates w1 (f_testInp t r) = true ∨ f_val gates w2 (f_testInp t r) = true) :
    r ≠ base := by
  intro hreq
  rw [hreq] at hvr
  have ht : f_val gates (13 + g.val) (f_testInp t base) = true := by
    rw [f_val_or_iff gates g _ (hWF g).2 hop, hin]
    rcases hvr with h | h
    · exact ⟨w1, by simp, h⟩
    · exact ⟨w2, by simp, h⟩
  rw [hb] at ht
  exact Bool.noConfusion ht

lemma f_card_le_two_of_merges (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (t base : f_P) (hcard3 : (f_line t \ {base}).card = 3)
    (S : Finset (Fin gates.length))
    (hM : ∀ g ∈ S, f_Merges gates t g ∧ f_val gates (13 + g.val) (f_testInp t base) = false) :
    S.card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨g1, hg1, g2, hg2, g3, hg3, h12, h23⟩ := f_three_ordered_of_two_lt hgt
  have h13 : g1 < g3 := lt_trans h12 h23
  obtain ⟨⟨hop1, hcol1, w11, w12, hin1, r1, hr1, r1', hr1', hv11, hv12, X1, hr1X, hr1'X, _⟩, hb1⟩ := hM g1 hg1
  obtain ⟨⟨hop2, hcol2, w21, w22, hin2, r2, hr2, r2', hr2', hv21, hv22, X2, hr2X, hr2'X, hcut2⟩, hb2⟩ := hM g2 hg2
  obtain ⟨⟨hop3, _, w31, w32, hin3, r3, hr3, r3', hr3', hv31, hv32, X3, hr3X, hr3'X, hcut3⟩, hb3⟩ := hM g3 hg3
  have hr1_ne : r1 ≠ base := f_ne_base_of_or_true gates hWF t base g1 w11 w12 r1 hop1 hin1 hb1 (Or.inl hv11)
  have hr1'_ne : r1' ≠ base := f_ne_base_of_or_true gates hWF t base g1 w11 w12 r1' hop1 hin1 hb1 (Or.inr hv12)
  have hr2_ne : r2 ≠ base := f_ne_base_of_or_true gates hWF t base g2 w21 w22 r2 hop2 hin2 hb2 (Or.inl hv21)
  have hr2'_ne : r2' ≠ base := f_ne_base_of_or_true gates hWF t base g2 w21 w22 r2' hop2 hin2 hb2 (Or.inr hv22)
  have hr3_ne : r3 ≠ base := f_ne_base_of_or_true gates hWF t base g3 w31 w32 r3 hop3 hin3 hb3 (Or.inl hv31)
  have hr3'_ne : r3' ≠ base := f_ne_base_of_or_true gates hWF t base g3 w31 w32 r3' hop3 hin3 hb3 (Or.inr hv32)
  have h1neq : r1 ≠ r1' := fun h => hr1'X (h ▸ hr1X)
  have h2neq : r2 ≠ r2' := fun h => hr2'X (h ▸ hr2X)
  have h1_X2 : r1 ∈ X2 ↔ r1' ∈ X2 := hcut2 g1 h12 hop1 hcol1 w11 w12 hin1 r1 hr1 r1' hr1' (Or.inl hv11) (Or.inr hv12)
  have h1_X3 : r1 ∈ X3 ↔ r1' ∈ X3 := hcut3 g1 h13 hop1 hcol1 w11 w12 hin1 r1 hr1 r1' hr1' (Or.inl hv11) (Or.inr hv12)
  have h2_X3 : r2 ∈ X3 ↔ r2' ∈ X3 := hcut3 g2 h23 hop2 hcol2 w21 w22 hin2 r2 hr2 r2' hr2' (Or.inl hv21) (Or.inr hv22)
  have hc_ex : ∃ c ∈ f_line t \ {base}, c ≠ r1 ∧ c ≠ r1' ∧ (c = r2 ∨ c = r2') := by
    by_cases h2 : r2 ≠ r1 ∧ r2 ≠ r1'
    · exact ⟨r2, Finset.mem_sdiff.mpr ⟨hr2, by simp [hr2_ne]⟩, h2.1, h2.2, Or.inl rfl⟩
    · by_cases h2' : r2' ≠ r1 ∧ r2' ≠ r1'
      · exact ⟨r2', Finset.mem_sdiff.mpr ⟨hr2', by simp [hr2'_ne]⟩, h2'.1, h2'.2, Or.inr rfl⟩
      · exfalso
        have ha : r2 = r1 ∨ r2 = r1' := by
          by_cases h : r2 = r1
          · exact Or.inl h
          · by_contra hn; exact h2 ⟨h, fun heq => hn (Or.inr heq)⟩
        have hb : r2' = r1 ∨ r2' = r1' := by
          by_cases h : r2' = r1
          · exact Or.inl h
          · by_contra hn; exact h2' ⟨h, fun heq => hn (Or.inr heq)⟩
        have heq : r2 ∈ X2 ↔ r2' ∈ X2 := by
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · rfl
          · exact h1_X2
          · exact h1_X2.symm
          · rfl
        exact hr2'X (heq.mp hr2X)
  obtain ⟨c, hcS, hcr1, hcr1', hcr2⟩ := hc_ex
  have hall := f_mem_of_card_three hcard3
    (Finset.mem_sdiff.mpr ⟨hr1, by simp [hr1_ne]⟩)
    (Finset.mem_sdiff.mpr ⟨hr1', by simp [hr1'_ne]⟩)
    hcS h1neq hcr1.symm hcr1'.symm
  have hc_X3 : c ∈ X3 ↔ r1 ∈ X3 := by
    rcases hcr2 with rfl | rfl
    · rcases hall r2' (Finset.mem_sdiff.mpr ⟨hr2', by simp [hr2'_ne]⟩) with h | h | h
      · rw [h2_X3, h]
      · rw [h2_X3, h, ← h1_X3]
      · exact (h2neq h.symm).elim
    · rcases hall r2 (Finset.mem_sdiff.mpr ⟨hr2, by simp [hr2_ne]⟩) with h | h | h
      · rw [← h2_X3, h]
      · rw [← h2_X3, h, ← h1_X3]
      · exact (h2neq h).elim
  have hsame (x : f_P) (hx : x ∈ f_line t \ {base}) : x ∈ X3 ↔ r1 ∈ X3 := by
    rcases hall x hx with rfl | rfl | rfl
    · rfl
    · exact h1_X3.symm
    · exact hc_X3
  have h3a := hsame r3 (Finset.mem_sdiff.mpr ⟨hr3, by simp [hr3_ne]⟩)
  have h3b := hsame r3' (Finset.mem_sdiff.mpr ⟨hr3', by simp [hr3'_ne]⟩)
  exact hr3'X (h3b.mpr (h3a.mp hr3X))

lemma f_side_bound (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (A B : Finset f_P) (baseA baseB : f_P)
    (h_sub : ∀ a ∈ A, a ∈ f_LS ∨ a ∈ f_MS)
    (h_base_le : ∀ a ∈ A, ∀ b ∈ B, ∀ v : f_P, f_testInp a baseA v = true → f_coline b v = true)
    (h_other_A : ∀ a1 ∈ A, ∀ a2 ∈ A, a1 ≠ a2 → ∀ y ∈ f_line a1, y ≠ baseA → ∀ v : f_P,
      f_testInp a1 y v = true → f_coline a2 v = true)
    (h_other_B : ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → ∀ y ∈ f_line b1, y ≠ baseB → ∀ v : f_P,
      f_testInp b1 y v = true → f_coline b2 v = true)
    (h_inter : ∀ a ∈ A, ∀ b ∈ B, (f_line a ∩ f_line b).card = 1)
    (h_card3 : ∀ a ∈ A, (f_line a \ {baseA}).card = 3)
    (K J : Finset (Fin gates.length))
    (hK_side : ∀ g ∈ K, ∃ a ∈ A, ∃ b ∈ B, f_Merges gates a g ∧ f_Merges gates b g)
    (hJ_side : ∀ z : Fin gates.length, (gates.get z).op = GateOp.and →
      ∀ g : Fin gates.length, ∀ a ∈ A, ∀ b ∈ B,
        f_Merges gates a g → f_Merges gates b g →
        f_OrReach gates (13 + g.val) (13 + z.val) →
        f_val gates (13 + z.val) (f_coline a) = false →
        f_val gates (13 + z.val) (f_coline b) = false →
        (∃ p ∈ f_line a, p ∉ f_line b ∧ f_val gates (13 + z.val) (f_testInp a p) = true) →
        z ∈ J) :
    let JA (a : f_P) := J.filter (fun z => f_val gates (13 + z.val) (f_coline a) = false ∧
      ∃ p ∈ f_line a, p ≠ baseA ∧ f_val gates (13 + z.val) (f_testInp a p) = true)
    let JB (b : f_P) := J.filter (fun z => f_val gates (13 + z.val) (f_coline b) = false ∧
      ∃ s ∈ f_line b, s ≠ baseB ∧ f_val gates (13 + z.val) (f_testInp b s) = true)
    let JA_all := A.biUnion JA
    let JB_all := B.biUnion JB
    K.card ≤ 2 * (JA_all \ JB_all).card + (JA_all ∩ JB_all).card := by
  classical
  intro JA JB JA_all JB_all
  let KA (a : f_P) := K.filter (fun g => f_Merges gates a g)
  have hbase_false (g : Fin gates.length) (a : f_P) (ha : a ∈ A) (b : f_P) (hb : b ∈ B)
      (hMb : f_Merges gates b g) : f_val gates (13 + g.val) (f_testInp a baseA) = false := by
    cases h : f_val gates (13 + g.val) (f_testInp a baseA) with
    | false => rfl
    | true =>
      have ht := f_val_mono gates hG hWF _ _ (h_base_le a ha b hb) (13 + g.val) (by omega) h
      rw [hMb.2.1] at ht
      exact Bool.noConfusion ht
  have hKA_disj : Set.PairwiseDisjoint (A : Set f_P) KA := by
    intro a1 ha1 a2 ha2 hne
    show Disjoint (KA a1) (KA a2)
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have hgK : g ∈ K := (Finset.mem_filter.mp hg1).1
    have hM1 : f_Merges gates a1 g := (Finset.mem_filter.mp hg1).2
    have hM2 : f_Merges gates a2 g := (Finset.mem_filter.mp hg2).2
    obtain ⟨_, _, b, hb, _, hMb⟩ := hK_side g hgK
    have hb1 := hbase_false g a1 ha1 b hb hMb
    obtain ⟨hop1, _, w1, w2, hin1, r, hr, _, _, hv1, _, _⟩ := hM1
    have hr_ne : r ≠ baseA := f_ne_base_of_or_true gates hWF a1 baseA g w1 w2 r hop1 hin1 hb1 (Or.inl hv1)
    have hgt : f_val gates (13 + g.val) (f_testInp a1 r) = true := by
      rw [f_val_or_iff gates g _ (hWF g).2 hop1, hin1]
      exact ⟨w1, by simp, hv1⟩
    have hcol2 := f_val_mono gates hG hWF _ _ (h_other_A a1 ha1 a2 ha2 hne r hr hr_ne) (13 + g.val) (by omega) hgt
    rw [hM2.2.1] at hcol2
    exact Bool.noConfusion hcol2
  have hK_eq : K = A.biUnion KA := by
    ext g
    simp only [Finset.mem_biUnion, KA, Finset.mem_filter]
    constructor
    · intro hg
      obtain ⟨a, ha, _, _, hMa, _⟩ := hK_side g hg
      exact ⟨a, ha, hg, hMa⟩
    · rintro ⟨_, _, hg, _⟩
      exact hg
  have hJA_disj : Set.PairwiseDisjoint (A : Set f_P) JA := by
    intro a1 ha1 a2 ha2 hne
    show Disjoint (JA a1) (JA a2)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨_, _, p, hp, hpne, hvp⟩ := Finset.mem_filter.mp hz1
    obtain ⟨_, hcol2, _⟩ := Finset.mem_filter.mp hz2
    have ht := f_val_mono gates hG hWF _ _ (h_other_A a1 ha1 a2 ha2 hne p hp hpne) (13 + z.val) (by omega) hvp
    rw [hcol2] at ht
    exact Bool.noConfusion ht
  -- Helper: from g ∈ K with f_Merges a g ∧ f_Merges b g and p ∈ f_line a \ f_line b firing on input w of g, find z ∈ JA a
  have find_z (g : Fin gates.length) (a : f_P) (ha : a ∈ A) (b : f_P) (hb : b ∈ B)
      (hMa : f_Merges gates a g) (hMb : f_Merges gates b g)
      (w : ℕ) (hw : w ∈ (gates.get g).inputs) (p : f_P) (hpa : p ∈ f_line a) (hpb : p ∉ f_line b)
      (hvw : f_val gates w (f_testInp a p) = true) :
      ∃ z : Fin gates.length, z ∈ JA a ∧ z < g ∧
        f_val gates (13 + z.val) (f_coline b) = false ∧ f_val gates (13 + z.val) (f_testInp a p) = true := by
    have hstep : f_OrReach gates (13 + g.val) w := f_orReach_step gates g hMa.1 hw
    have hwlt : w < 13 + g.val := (hWF g).2 w hw
    rcases f_orReach_find_stop gates hG hWF (f_testInp a p) w (by omega) hvw with ⟨v, hrv, hxv⟩ | ⟨z, hzop, hrz, hvz⟩
    · exfalso
      have hrvg : f_OrReach gates (13 + g.val) v.val := f_orReach_trans gates hstep hrv
      have hfa := f_orReach_false gates hWF hrvg (f_coline a) hMa.2.1
      have hfb := f_orReach_false gates hWF hrvg (f_coline b) hMb.2.1
      rw [f_val_input] at hfa hfb
      have hva : v ∈ f_line a := by simpa [f_coline] using hfa
      have hvb : v ∈ f_line b := by simpa [f_coline] using hfb
      have heq := f_testInp_in_line_eq a (h_sub a ha) p hpa v hva hxv
      exact hpb (heq ▸ hvb)
    · have hrzg : f_OrReach gates (13 + g.val) (13 + z.val) := f_orReach_trans gates hstep hrz
      have hfa := f_orReach_false gates hWF hrzg (f_coline a) hMa.2.1
      have hfb := f_orReach_false gates hWF hrzg (f_coline b) hMb.2.1
      have hzJ : z ∈ J := hJ_side z hzop g a ha b hb hMa hMb hrzg hfa hfb ⟨p, hpa, hpb, hvz⟩
      have hpne : p ≠ baseA := by
        intro hpeq; subst hpeq
        have ht := f_val_mono gates hG hWF _ _ (h_base_le a ha b hb) (13 + z.val) (by omega) hvz
        rw [hfb] at ht; exact Bool.noConfusion ht
      have hzJA : z ∈ JA a := Finset.mem_filter.mpr ⟨hzJ, hfa, p, hpa, hpne, hvz⟩
      have hle := f_orReach_le gates hWF hrz
      have hzlt : z < g := by change z.val < g.val; omega
      exact ⟨z, hzJA, hzlt, hfb, hvz⟩
  -- Helper: given two distinct points r, r' ∈ f_line a and b ∈ B, not both lie in f_line b
  have not_both_in_b (a : f_P) (ha : a ∈ A) (b : f_P) (hb : b ∈ B) (r r' : f_P)
      (hr : r ∈ f_line a) (hr' : r' ∈ f_line a) (hne : r ≠ r') (h1 : r ∈ f_line b) : r' ∉ f_line b := by
    intro h2
    have hsub2 : ({r, r'} : Finset f_P) ⊆ f_line a ∩ f_line b := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_inter.mpr ⟨by assumption, by assumption⟩
    have hc2 : ({r, r'} : Finset f_P).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have hle := Finset.card_le_card hsub2
    have h1c := h_inter a ha b hb
    omega
  -- Per-f_line bound for each a ∈ A
  have hper (a : f_P) (ha : a ∈ A) :
      (KA a).card ≤ 2 * (JA a \ JB_all).card + (JA a ∩ JB_all).card := by
    have hJsplit : (JA a).card = (JA a \ JB_all).card + (JA a ∩ JB_all).card := by
      have := Finset.card_sdiff_add_card_inter (JA a) JB_all
      omega
    have hle2 : (KA a).card ≤ 2 := by
      apply f_card_le_two_of_merges gates hWF a baseA (h_card3 a ha) (KA a)
      intro g hg
      have hgK : g ∈ K := (Finset.mem_filter.mp hg).1
      have hMa : f_Merges gates a g := (Finset.mem_filter.mp hg).2
      obtain ⟨_, _, b, hb, _, hMb⟩ := hK_side g hgK
      exact ⟨hMa, hbase_false g a ha b hb hMb⟩
    have get_partner (g : Fin gates.length) (hg : g ∈ KA a) :
        ∃ b ∈ B, f_Merges gates a g ∧ f_Merges gates b g := by
      have hgK : g ∈ K := (Finset.mem_filter.mp hg).1
      have hMa : f_Merges gates a g := (Finset.mem_filter.mp hg).2
      obtain ⟨_, _, b, hb, _, hMb⟩ := hK_side g hgK
      exact ⟨b, hb, hMa, hMb⟩
    by_cases h0 : (KA a).card = 0
    · omega
    by_cases h1 : (KA a).card = 1
    · obtain ⟨g, hg⟩ := Finset.card_pos.mp (by omega : 0 < (KA a).card)
      obtain ⟨b, hb, hMa, hMb⟩ := get_partner g hg
      have ⟨hop, _, w1, w2, hin, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := hMa
      have hneq : r ≠ r' := fun h => hr'X (h ▸ hrX)
      have hz_ex : ∃ z, z ∈ JA a := by
        by_cases hrb : r ∉ f_line b
        · obtain ⟨z, hz, _⟩ := find_z g a ha b hb hMa hMb w1 (by rw [hin]; simp) r hr hrb hv1
          exact ⟨z, hz⟩
        · push Not at hrb
          have hr'b := not_both_in_b a ha b hb r r' hr hr' hneq hrb
          obtain ⟨z, hz, _⟩ := find_z g a ha b hb hMa hMb w2 (by rw [hin]; simp) r' hr' hr'b hv2
          exact ⟨z, hz⟩
      obtain ⟨z, hz⟩ := hz_ex
      have hpos : 1 ≤ (JA a).card := Finset.card_pos.mpr ⟨z, hz⟩
      omega
    · have h2 : (KA a).card = 2 := by omega
      obtain ⟨g1, hg1, g2, hg2, h12⟩ := f_two_ordered_of_one_lt (by omega : 1 < (KA a).card)
      obtain ⟨b1, hb1, hMa1, hMb1⟩ := get_partner g1 hg1
      obtain ⟨b2, hb2, hMa2, hMb2⟩ := get_partner g2 hg2
      have ⟨hop1, hcol1, w11, w12, hin1, r1, hr1, r1', hr1', hv11, hv12, X1, hr1X, hr1'X, hcut1⟩ := hMa1
      have ⟨hop2, hcol2, w21, w22, hin2, r2, hr2, r2', hr2', hv21, hv22, X2, hr2X, hr2'X, hcut2⟩ := hMa2
      have h1neq : r1 ≠ r1' := fun h => hr1'X (h ▸ hr1X)
      have h2neq : r2 ≠ r2' := fun h => hr2'X (h ▸ hr2X)
      -- Case 1: neither r1 nor r1' is in f_line b1
      by_cases hboth1 : r1 ∉ f_line b1 ∧ r1' ∉ f_line b1
      · obtain ⟨z1, hz1, hz1lt, _, hvz1⟩ := find_z g1 a ha b1 hb1 hMa1 hMb1 w11 (by rw [hin1]; simp) r1 hr1 hboth1.1 hv11
        obtain ⟨z2, hz2, _, _, hvz2⟩ := find_z g1 a ha b1 hb1 hMa1 hMb1 w12 (by rw [hin1]; simp) r1' hr1' hboth1.2 hv12
        have hzne : z1 ≠ z2 := by
          intro heq; subst heq
          have hcolz := (Finset.mem_filter.mp hz1).2.1
          have hsame := f_wire_same_comp gates hG hWF a (h_sub a ha) g1 X1 hcut1 (13 + z1.val) (by omega) hcolz r1 hr1 r1' hr1' hvz1 hvz2
          exact hr1'X (hsame.mp hr1X)
        have hcard2 : 2 ≤ (JA a).card := Finset.one_lt_card.mpr ⟨z1, hz1, z2, hz2, hzne⟩
        omega
      · -- At least one of r1, r1' lies in f_line b1; let q1 be the one in f_line b1 and p1 be the other
        have hqp1 : ∃ q1 ∈ f_line a, ∃ p1 ∈ f_line a, q1 ∈ f_line b1 ∧ p1 ∉ f_line b1 ∧
            (q1 = r1 ∧ p1 = r1' ∨ q1 = r1' ∧ p1 = r1) ∧
            ∃ wp1 ∈ (gates.get g1).inputs, f_val gates wp1 (f_testInp a p1) = true := by
          by_cases h : r1 ∈ f_line b1
          · exact ⟨r1, hr1, r1', hr1', h, not_both_in_b a ha b1 hb1 r1 r1' hr1 hr1' h1neq h,
              Or.inl ⟨rfl, rfl⟩, w12, by rw [hin1]; simp, hv12⟩
          · have h' : r1' ∈ f_line b1 := by
              by_contra hn
              exact hboth1 ⟨h, hn⟩
            exact ⟨r1', hr1', r1, hr1, h', h, Or.inr ⟨rfl, rfl⟩, w11, by rw [hin1]; simp, hv11⟩
        obtain ⟨q1, hq1, p1, hp1, hq1b1, hp1b1, hqp1eq, wp1, hwp1in, hvp1⟩ := hqp1
        obtain ⟨z1, hz1, hz1lt, hfb1, hvz1⟩ := find_z g1 a ha b1 hb1 hMa1 hMb1 wp1 hwp1in p1 hp1 hp1b1 hvp1
        -- At g2 > g1, r1 and r1' are on the same side of X2, while r2 ∈ X2 and r2' ∉ X2
        have h1_X2 : r1 ∈ X2 ↔ r1' ∈ X2 :=
          hcut2 g1 h12 hop1 hcol1 w11 w12 hin1 r1 hr1 r1' hr1' (Or.inl hv11) (Or.inr hv12)
        have hp1_X2 : (r1 ∈ X2 ↔ p1 ∈ X2) := by
          rcases hqp1eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h1_X2
          · rfl
        -- Pick p2 ∈ {r2, r2'} on the opposite side of X2 from p1, and let p2' be the other
        have hp2_ex : ∃ p2 ∈ f_line a, ∃ p2' ∈ f_line a, p2 ≠ p2' ∧ ¬ (p1 ∈ X2 ↔ p2 ∈ X2) ∧
            (∃ w ∈ (gates.get g2).inputs, f_val gates w (f_testInp a p2) = true) ∧
            (∃ w' ∈ (gates.get g2).inputs, f_val gates w' (f_testInp a p2') = true) := by
          by_cases hp : p1 ∈ X2
          · exact ⟨r2', hr2', r2, hr2, h2neq.symm, by simp [hp, hr2'X],
              ⟨w22, by rw [hin2]; simp, hv22⟩, ⟨w21, by rw [hin2]; simp, hv21⟩⟩
          · exact ⟨r2, hr2, r2', hr2', h2neq, by simp [hp, hr2X],
              ⟨w21, by rw [hin2]; simp, hv21⟩, ⟨w22, by rw [hin2]; simp, hv22⟩⟩
        obtain ⟨p2, hp2, p2', hp2', hp2neq, hopp, ⟨wp2, hwp2in, hvp2⟩, ⟨wp2', hwp2'in, hvp2'⟩⟩ := hp2_ex
        by_cases hp2b2 : p2 ∉ f_line b2
        · obtain ⟨z2, hz2, _, _, hvz2⟩ := find_z g2 a ha b2 hb2 hMa2 hMb2 wp2 hwp2in p2 hp2 hp2b2 hvp2
          have hzne : z1 ≠ z2 := by
            intro heq; subst heq
            have hcolz := (Finset.mem_filter.mp hz1).2.1
            have hlt2 : 13 + z1.val < 13 + g2.val := by
              have : z1.val < g1.val := hz1lt
              have : g1.val < g2.val := h12
              omega
            have hsame := f_wire_same_comp gates hG hWF a (h_sub a ha) g2 X2 hcut2 (13 + z1.val) hlt2 hcolz p1 hp1 p2 hp2 hvz1 hvz2
            exact hopp hsame
          have hcard2 : 2 ≤ (JA a).card := Finset.one_lt_card.mpr ⟨z1, hz1, z2, hz2, hzne⟩
          omega
        · push Not at hp2b2
          have hp2'b2 := not_both_in_b a ha b2 hb2 p2 p2' hp2 hp2' hp2neq hp2b2
          obtain ⟨z2, hz2, _, hfb2, _⟩ := find_z g2 a ha b2 hb2 hMa2 hMb2 wp2' hwp2'in p2' hp2' hp2'b2 hvp2'
          by_cases hzne : z1 ≠ z2
          · have hcard2 : 2 ≤ (JA a).card := Finset.one_lt_card.mpr ⟨z1, hz1, z2, hz2, hzne⟩
            omega
          · push Not at hzne
            subst hzne
            -- z1 = z2, so f_val z1 (f_coline b1) = false AND f_val z1 (f_coline b2) = false, and b1 ≠ b2!
            have hq1_X2 : p1 ∈ X2 ↔ q1 ∈ X2 := by
              rcases hqp1eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact h1_X2.symm
              · exact h1_X2
            have hp2_ne_q1 : p2 ≠ q1 := by
              intro h; subst h; exact hopp hq1_X2
            have hb12 : b1 ≠ b2 := by
              intro h; subst h
              exact not_both_in_b a ha b1 hb1 q1 p2 hq1 hp2 hp2_ne_q1.symm hq1b1 hp2b2
            have hz1_not_JB : z1 ∉ JB_all := by
              intro hmem
              obtain ⟨b3, hb3, hzb3⟩ := Finset.mem_biUnion.mp hmem
              obtain ⟨_, _, s, hs, hsne, hvs⟩ := Finset.mem_filter.mp hzb3
              by_cases h31 : b3 ≠ b1
              · have ht := f_val_mono gates hG hWF _ _ (h_other_B b3 hb3 b1 hb1 h31 s hs hsne) (13 + z1.val) (by omega) hvs
                rw [hfb1] at ht; exact Bool.noConfusion ht
              · push Not at h31
                subst h31
                have ht := f_val_mono gates hG hWF _ _ (h_other_B b3 hb3 b2 hb2 hb12 s hs hsne) (13 + z1.val) (by omega) hvs
                rw [hfb2] at ht; exact Bool.noConfusion ht
            have hpure : 1 ≤ (JA a \ JB_all).card := Finset.card_pos.mpr ⟨z1, Finset.mem_sdiff.mpr ⟨hz1, hz1_not_JB⟩⟩
            omega
  -- Sum hper over a ∈ A
  have hsumK : K.card = ∑ a ∈ A, (KA a).card := by
    rw [hK_eq, Finset.card_biUnion hKA_disj]
  have hsumPure : (JA_all \ JB_all).card = ∑ a ∈ A, (JA a \ JB_all).card := by
    have hdisj : Set.PairwiseDisjoint (A : Set f_P) (fun a => JA a \ JB_all) := by
      intro a1 ha1 a2 ha2 hne
      exact Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset (hJA_disj ha1 ha2 hne)
    have heq : JA_all \ JB_all = A.biUnion (fun a => JA a \ JB_all) := by
      ext z
      simp only [JA_all, Finset.mem_sdiff, Finset.mem_biUnion]
      exact ⟨fun ⟨⟨a, ha, hza⟩, hzb⟩ => ⟨a, ha, hza, hzb⟩,
             fun ⟨a, ha, hza, hzb⟩ => ⟨⟨a, ha, hza⟩, hzb⟩⟩
    rw [heq, Finset.card_biUnion hdisj]
  have hsumBoth : (JA_all ∩ JB_all).card = ∑ a ∈ A, (JA a ∩ JB_all).card := by
    have hdisj : Set.PairwiseDisjoint (A : Set f_P) (fun a => JA a ∩ JB_all) := by
      intro a1 ha1 a2 ha2 hne
      exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left (hJA_disj ha1 ha2 hne)
    have heq : JA_all ∩ JB_all = A.biUnion (fun a => JA a ∩ JB_all) := by
      ext z
      simp only [JA_all, Finset.mem_inter, Finset.mem_biUnion]
      exact ⟨fun ⟨⟨a, ha, hza⟩, hzb⟩ => ⟨a, ha, hza, hzb⟩,
             fun ⟨a, ha, hza, hzb⟩ => ⟨⟨a, ha, hza⟩, hzb⟩⟩
    rw [heq, Finset.card_biUnion hdisj]
  calc
    K.card = ∑ a ∈ A, (KA a).card := hsumK
    _ ≤ ∑ a ∈ A, (2 * (JA a \ JB_all).card + (JA a ∩ JB_all).card) := Finset.sum_le_sum hper
    _ = 2 * (∑ a ∈ A, (JA a \ JB_all).card) + ∑ a ∈ A, (JA a ∩ JB_all).card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (JA_all \ JB_all).card + (JA_all ∩ JB_all).card := by rw [hsumPure, hsumBoth]

lemma f_main_proof (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (K J : Finset (Fin gates.length))
    (hK : ∀ g : Fin gates.length, g ∈ K ↔ ∃ l ∈ f_LS, ∃ m ∈ f_MS, f_Merges gates l g ∧ f_Merges gates m g)
    (hJ : ∀ z : Fin gates.length,
      ((gates.get z).op = GateOp.and ∧
        ∃ g : Fin gates.length, ∃ l ∈ f_LS, ∃ m ∈ f_MS,
          f_Merges gates l g ∧ f_Merges gates m g ∧
          f_OrReach gates (13 + g.val) (13 + z.val) ∧
          f_val gates (13 + z.val) (f_coline l) = false ∧
          f_val gates (13 + z.val) (f_coline m) = false ∧
          ((∃ p ∈ f_line l, p ∉ f_line m ∧ f_val gates (13 + z.val) (f_testInp l p) = true) ∨
           (∃ p ∈ f_line m, p ∉ f_line l ∧ f_val gates (13 + z.val) (f_testInp m p) = true))) → z ∈ J) :
    K.card ≤ J.card := by
  classical
  let JL (l : f_P) := J.filter (fun z => f_val gates (13 + z.val) (f_coline l) = false ∧
    ∃ p ∈ f_line l, p ≠ 0 ∧ f_val gates (13 + z.val) (f_testInp l p) = true)
  let JM (m : f_P) := J.filter (fun z => f_val gates (13 + z.val) (f_coline m) = false ∧
    ∃ s ∈ f_line m, s ≠ 1 ∧ f_val gates (13 + z.val) (f_testInp m s) = true)
  let JL_all := f_LS.biUnion JL
  let JM_all := f_MS.biUnion JM
  have h1 : K.card ≤ 2 * (JL_all \ JM_all).card + (JL_all ∩ JM_all).card :=
    f_side_bound gates hG hWF f_LS f_MS 0 1
      (fun a ha => Or.inl ha)
      f_testInp_base_le_coline_LM
      f_testInp_other_le_coline_LL
      f_testInp_other_le_coline_MM
      f_inter_LM_card
      f_line_sdiff_base_L
      K J
      (fun g hg => (hK g).mp hg)
      (fun z hzop g l hl m hm hMl hMm hreach hfl hfm hp =>
        hJ z ⟨hzop, g, l, hl, m, hm, hMl, hMm, hreach, hfl, hfm, Or.inl hp⟩)
  have h2 : K.card ≤ 2 * (JM_all \ JL_all).card + (JM_all ∩ JL_all).card :=
    f_side_bound gates hG hWF f_MS f_LS 1 0
      (fun a ha => Or.inr ha)
      f_testInp_base_le_coline_ML
      f_testInp_other_le_coline_MM
      f_testInp_other_le_coline_LL
      f_inter_ML_card
      f_line_sdiff_base_M
      K J
      (fun g hg => by
        obtain ⟨l, hl, m, hm, hMl, hMm⟩ := (hK g).mp hg
        exact ⟨m, hm, l, hl, hMm, hMl⟩)
      (fun z hzop g m hm l hl hMm hMl hreach hfm hfl hp =>
        hJ z ⟨hzop, g, l, hl, m, hm, hMl, hMm, hreach, hfl, hfm, Or.inr hp⟩)
  have hcomm : (JM_all ∩ JL_all).card = (JL_all ∩ JM_all).card := by rw [Finset.inter_comm]
  have hsub : JL_all ∪ JM_all ⊆ J := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · obtain ⟨l, _, hzl⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hzl).1
    · obtain ⟨m, _, hzm⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hzm).1
  have hcard_union : (JL_all \ JM_all).card + (JM_all \ JL_all).card + (JL_all ∩ JM_all).card =
      (JL_all ∪ JM_all).card := by
    have ha := Finset.card_sdiff_add_card_inter JL_all JM_all
    have hb := Finset.card_sdiff_add_card_inter JM_all JL_all
    have hu := Finset.card_union_add_card_inter JL_all JM_all
    rw [Finset.inter_comm] at hb
    omega
  have hleJ := Finset.card_le_card hsub
  omega

theorem fl13 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ t : Fin 13, (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∨ t ∈ ({1, 5, 11} : Finset (Fin 13))) → (∀ X : Finset (Fin 13), (∀ i : Fin gates.length, True → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L t, ∀ y' ∈ L t,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true) → (y ∈ X ↔ y' ∈ X)) → ∀ y ∈ L t, ∀ y' ∈ L t, (y ∈ X ↔ y' ∈ X))) →
    ∀ K J : Finset (Fin gates.length),
      (∀ g : Fin gates.length, g ∈ K ↔ (∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin 13 => decide (v = r ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ r ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ r ≠ 1 ∧ v = 0)))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin 13 => decide (v = r' ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ r' ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ r' ≠ 1 ∧ v = 0)))) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true) → (y ∈ X ↔ y' ∈ X))) ∧ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin 13 => decide (v = r ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ r ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ r ≠ 1 ∧ v = 0)))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin 13 => decide (v = r' ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ r' ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ r' ≠ 1 ∧ v = 0)))) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true) → (y ∈ X ↔ y' ∈ X))))) →
      (∀ z : Fin gates.length, ((gates.get z).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ g : Fin gates.length, ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin 13 => decide (v = r ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ r ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ r ≠ 1 ∧ v = 0)))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin 13 => decide (v = r' ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ r' ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ r' ≠ 1 ∧ v = 0)))) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true) → (y ∈ X ↔ y' ∈ X))) ∧
          ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin 13 => decide (v = r ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ r ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ r ≠ 1 ∧ v = 0)))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin 13 => decide (v = r' ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ r' ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ r' ≠ 1 ∧ v = 0)))) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0)))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin 13 => decide (v = y' ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y' ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y' ≠ 1 ∧ v = 0)))) = true) → (y ∈ X ↔ y' ∈ X))) ∧ (∀ S : Set ℕ, 13 + (g : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → 13 + (z : ℕ) ∈ S) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (z : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (z : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
          ((∃ p ∈ L l, p ∉ L m ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (z : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 ∧ v = 1) ∨ (l ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ p ≠ 1 ∧ v = 0)))) = true) ∨ (∃ p ∈ L m, p ∉ L l ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (z : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (m ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 ∧ v = 1) ∨ (m ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ p ≠ 1 ∧ v = 0)))) = true))) → z ∈ J) →
      K.card ≤ J.card := by
  intro L hL gates hG hWF _hconn K J hK hJ
  have eq : L = f_line := funext hL
  subst L
  exact f_main_proof gates hG hWF K J hK hJ

def Ts (t p : Fin 13) : Fin 13 → Bool := fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ s_lines t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ s_lines 0 else ∅))

def Tp (t y : Fin 13) : Fin 13 → Bool := fun v : Fin 13 => decide (v = y ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ≠ 0 ∧ v = 1) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ y ≠ 1 ∧ v = 0))

def co (t : Fin 13) : Fin 13 → Bool := fun v : Fin 13 => decide (v ∉ s_lines t)

def F01 (x : Fin 13 → Bool) : Prop :=
  x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ s_lines 0 → x v = true

set_option maxRecDepth 100000 in
theorem ts_tp : ∀ t : Fin 13, (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∨ t ∈ ({1, 5, 11} : Finset (Fin 13))) →
    ∀ p v : Fin 13, Ts t p v = Tp t p v := by
  decide +kernel

theorem ts_eq (t : Fin 13) (ht : t ∈ ({4, 10, 12} : Finset (Fin 13)) ∨ t ∈ ({1, 5, 11} : Finset (Fin 13))) :
    Ts t = Tp t := funext fun p => funext fun v => ts_tp t ht p v

set_option maxRecDepth 100000 in
theorem co_F0 : ∀ t : Fin 13, (co t 0 = true ∨ co t 1 = true ∨ ∀ v : Fin 13, v ∉ s_lines 0 → co t v = true) := by
  decide +kernel

theorem co_F (t : Fin 13) : F01 (co t) := co_F0 t

theorem ts_F (t p : Fin 13) (hp : p ∈ s_lines t) : F01 (Ts t p) :=
  (t_main_aux s_lines (fun _ => rfl) t p hp).1

theorem ts_T (t : Fin 13) : ∀ p ∈ s_lines t, ∀ v ∈ s_lines t, Ts t p v = true ↔ v = p :=
  fun p hp => (t_main_aux s_lines (fun _ => rfl) t p hp).2.1

theorem lines_self (t : Fin 13) : t ∈ s_lines t := by
  simp [s_lines]

theorem ls_ne : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), l ≠ 0 := by decide

theorem val_eval (gates : List Gate) (w : ℕ) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = s_val gates w x := rfl

theorem mrg_two (gates : List Gate) (M : Finset (Fin 13)) (c : Fin 13 → Bool)
    (τ : Fin 13 → Fin 13 → Bool)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (g : Fin gates.length) (h : s_Mrg gates M c τ g) :
    2 ≤ (M.filter (fun p => Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (τ p)) = true)).card := by
  obtain ⟨ho, _, w1, w2, hw, r, hr, r', hr', h1, h2, X, hrX, hr'X, _⟩ := h
  have hne : r ≠ r' := fun e => hr'X (e ▸ hrX)
  have m1 : w1 ∈ (gates.get g).inputs := by rw [hw]; simp
  have m2 : w2 ∈ (gates.get g).inputs := by rw [hw]; simp
  have hg1 : s_val gates (13 + (g : ℕ)) (τ r) = true :=
    (s_val_or gates (τ r) g g.2 ho).2 ⟨w1, m1, (hin g).2 w1 m1, h1⟩
  have hg2 : s_val gates (13 + (g : ℕ)) (τ r') = true :=
    (s_val_or gates (τ r') g g.2 ho).2 ⟨w2, m2, (hin g).2 w2 m2, h2⟩
  have hsub : ({r, r'} : Finset (Fin 13)) ⊆
      M.filter (fun p => Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (τ p)) = true) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.2 ⟨hr, (val_eval gates _ _).trans hg1⟩
    · exact Finset.mem_filter.2 ⟨hr', (val_eval gates _ _).trans hg2⟩
  calc 2 = ({r, r'} : Finset (Fin 13)).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem k_abs (k : ℕ) (K : Fin k → Finset (Fin 13))
    (hK : ∀ i : Fin k, ∀ t ∈ K i, ∀ u ∈ K i, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) :
    ∃ A B : Finset (Fin k), (∀ i : Fin k, i ∈ A ↔ ((0 : Fin 13) ∈ K i ∧ 2 ≤ (K i).card)) ∧
      (∀ i : Fin k, i ∈ B ↔ ∃ l ∈ K i, ∃ m ∈ K i, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13))) ∧
      ∑ i : Fin k, ((K i).card - 1) = A.card + B.card :=
  ⟨_, _, fun i => by rw [Finset.mem_filter]; simp, fun i => by rw [Finset.mem_filter]; simp, k_main k K hK⟩

theorem fl13b (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (H1 : ∀ t : Fin 13, (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∨ t ∈ ({1, 5, 11} : Finset (Fin 13))) →
      ∀ X : Finset (Fin 13), s_Con gates (s_lines t) (co t) (Tp t) gates.length X →
        ∀ y ∈ s_lines t, ∀ y' ∈ s_lines t, (y ∈ X ↔ y' ∈ X))
    (K J : Finset (Fin gates.length))
    (hK : ∀ g : Fin gates.length, g ∈ K ↔ ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)),
      s_Mrg gates (s_lines l) (co l) (Tp l) g ∧ s_Mrg gates (s_lines m) (co m) (Tp m) g)
    (hJ : ∀ z : Fin gates.length, ((gates.get z).op = GateOp.and ∧
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), s_val gates (13 + (z : ℕ)) (co l) = false) → z ∈ J) :
    K.card ≤ J.card := by
  refine fl13 s_lines (fun _ => rfl) gates legal hin ?_ K J hK ?_
  · intro t ht X hX
    exact H1 t ht X (fun i _ => hX i trivial)
  · rintro z ⟨hz, g, l, hl, m, hm, _, _, _, hzl, _⟩
    exact hJ z ⟨hz, l, hl, hzl⟩

open Classical in
theorem core (gates : List Gate) (o : Fin 13 → ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hout : ∀ (t : Fin 13) (x : Fin 13 → Bool), F01 x →
      Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ s_lines t, x v = true)) :
    37 ≤ gates.length := by
  have hc : ∀ t : Fin 13, ∀ v, co t v = false → v ∈ s_lines t := by
    intro t v hv
    simpa [co] using hv
  have hoc : ∀ t : Fin 13, s_val gates (o t) (co t) = false := by
    intro t
    exact (hout t _ (co_F t)).trans (by simp [co])
  have hot : ∀ t : Fin 13, ∀ p ∈ s_lines t, s_val gates (o t) (Ts t p) = true := by
    intro t p hp
    exact (hout t _ (ts_F t p hp)).trans (decide_eq_true ⟨p, hp, (ts_T t p hp p hp).2 rfl⟩)
  have holt : ∀ t : Fin 13, o t < 13 + gates.length := by
    intro t
    by_contra h
    have hb := s_val_big gates (Ts t t) (o t) (by omega)
    rw [hot t t (lines_self t)] at hb
    exact Bool.noConfusion hb
  obtain ⟨R, hRm⟩ : ∃ R : Fin gates.length → Finset (Fin 13), ∀ g t, t ∈ R g ↔
      s_Mrg gates (s_lines t) (co t) (Ts t) g :=
    ⟨fun g => Finset.univ.filter (fun t => s_Mrg gates (s_lines t) (co t) (Ts t) g),
      fun g t => by rw [Finset.mem_filter]; simp⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset (Fin gates.length), ∀ g : Fin gates.length, g ∈ E ↔
      ((gates.get g).op = GateOp.and ∨ ((gates.get g).op = GateOp.or ∧ (R g).card = 0)) :=
    ⟨Finset.univ.filter (fun g => (gates.get g).op = GateOp.and ∨
      ((gates.get g).op = GateOp.or ∧ (R g).card = 0)), fun g => by rw [Finset.mem_filter]; simp⟩
  have h1 : gates.length + ∑ g : Fin gates.length, ((R g).card - 1) = 39 + E.card :=
    s_total Ts gates o (fun g => (R g).card) ts_T legal hin hoc hot
      (fun g => ⟨R g, hRm g, rfl⟩) E hE
  have hcl : ∀ i : Fin gates.length, ∀ t ∈ R i, ∀ u ∈ R i, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13)))) := by
    intro i t ht u hu htu
    have mt := (hRm i t).1 ht
    have mu := (hRm i u).1 hu
    have h68 := e_main s_lines (fun _ => rfl) Ts gates (13 + (i : ℕ)) t u ts_T legal htu mt.2.1 mu.2.1
      (mrg_two gates _ _ (Ts t) hin i mt) (mrg_two gates _ _ (Ts u) hin i mu)
    have h66 := ((c_all s_lines (fun _ => rfl)).1 t u).1 ⟨htu, h68.1, h68.2⟩
    rcases h66 with ⟨_, h⟩ | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨A, B, hA, hB, hS⟩ := k_abs gates.length R hcl
  rw [hS] at h1
  have H1 : ∀ t : Fin 13, (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∨ t ∈ ({1, 5, 11} : Finset (Fin 13))) →
      ∀ X : Finset (Fin 13), s_Con gates (s_lines t) (co t) (Tp t) gates.length X →
        ∀ y ∈ s_lines t, ∀ y' ∈ s_lines t, (y ∈ X ↔ y' ∈ X) := by
    intro t ht X hX y hy y' hy'
    rw [← ts_eq t ht] at hX
    exact s_single gates (s_lines t) (co t) (Ts t) (hc t) (ts_T t) legal hin gates.length le_rfl X hX
      (o t) (holt t) (hoc t) y hy y' hy' (hot t y hy) (hot t y' hy')
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin gates.length), ∀ z : Fin gates.length, z ∈ J ↔
      ((gates.get z).op = GateOp.and ∧
        ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), s_val gates (13 + (z : ℕ)) (co l) = false) :=
    ⟨Finset.univ.filter (fun z => (gates.get z).op = GateOp.and ∧
        ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), s_val gates (13 + (z : ℕ)) (co l) = false),
      fun z => by rw [Finset.mem_filter]; simp⟩
  have hK : ∀ g : Fin gates.length, g ∈ B ↔ ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)),
      s_Mrg gates (s_lines l) (co l) (Tp l) g ∧ s_Mrg gates (s_lines m) (co m) (Tp m) g := by
    intro g
    rw [hB g]
    constructor
    · rintro ⟨l, hl, m, hm, hlS, hmS⟩
      refine ⟨l, hlS, m, hmS, ?_, ?_⟩
      · have h := (hRm g l).1 hl
        rw [ts_eq l (Or.inl hlS)] at h
        exact h
      · have h := (hRm g m).1 hm
        rw [ts_eq m (Or.inr hmS)] at h
        exact h
    · rintro ⟨l, hlS, m, hmS, hl, hm⟩
      refine ⟨l, (hRm g l).2 ?_, m, (hRm g m).2 ?_, hlS, hmS⟩
      · rw [ts_eq l (Or.inl hlS)]
        exact hl
      · rw [ts_eq m (Or.inr hmS)]
        exact hm
  have hBJ : B.card ≤ J.card :=
    fl13b gates legal hin H1 B J hK (fun z hz => (hJ z).2 hz)
  obtain ⟨h13, hlt, _, _, _, hoth⟩ := o_main_aux s_lines (fun _ => rfl) gates o legal hin hout
  obtain ⟨z0, hz0⟩ : ∃ z0 : Fin gates.length, 13 + (z0 : ℕ) = o 0 :=
    ⟨⟨o 0 - 13, by omega⟩, by show 13 + (o 0 - 13) = o 0; omega⟩
  have halive : ∀ t : Fin 13, s_val gates (13 + (z0 : ℕ)) (co t) = false → t = 0 := by
    intro t h
    by_contra ht
    rw [hz0] at h
    have h2 : s_val gates (o 0) (co t) = true := hoth t ht
    rw [h2] at h
    exact Bool.noConfusion h
  have hJE : J ⊆ E := fun z hz => (hE z).2 (Or.inl ((hJ z).1 hz).1)
  have hz0J : z0 ∉ J := by
    intro hz
    obtain ⟨_, l, hl, hv⟩ := (hJ z0).1 hz
    exact ls_ne l hl (halive l hv)
  have h3 := s_three gates (s_lines 0) (co 0) (Ts 0) (hc 0) (ts_T 0) legal hin (s_card4 0) (o 0)
    (hoc 0) (hot 0)
  obtain ⟨M0, hM0, hM0c⟩ : ∃ M0 : Finset (Fin gates.length),
      (∀ g : Fin gates.length, g ∈ M0 ↔ s_Mrg gates (s_lines 0) (co 0) (Ts 0) g) ∧ M0.card = 3 :=
    ⟨Finset.univ.filter (fun g => s_Mrg gates (s_lines 0) (co 0) (Ts 0) g),
      fun g => by rw [Finset.mem_filter]; simp, by rw [Finset.card_filter]; convert h3⟩
  have hAsub : A ⊆ M0 := fun g hg => (hM0 g).2 ((hRm g 0).1 ((hA g).1 hg).1)
  by_cases hzE : z0 ∈ E
  · have hsub : J ⊆ E.erase z0 :=
      fun z hz => Finset.mem_erase.2 ⟨fun e => hz0J (e ▸ hz), hJE hz⟩
    have c1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hzE] at c1
    have c2 := Finset.card_le_card hAsub
    have c3 : 0 < E.card := Finset.card_pos.2 ⟨z0, hzE⟩
    omega
  · have hop : (gates.get z0).op = GateOp.or ∧ (R z0).card ≠ 0 := by
      rcases (legal gates[(z0 : ℕ)] (List.getElem_mem z0.2)).1 with ha | ho
      · exact absurd ((hE z0).2 (Or.inl ha)) hzE
      · exact ⟨ho, fun h0 => hzE ((hE z0).2 (Or.inr ⟨ho, h0⟩))⟩
    have hsub1 : R z0 ⊆ {0} := by
      intro t ht
      rw [Finset.mem_singleton]
      exact halive t ((hRm z0 t).1 ht).2.1
    obtain ⟨t, ht⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hop.2)
    have ht0 : t = 0 := Finset.mem_singleton.1 (hsub1 ht)
    rw [ht0] at ht
    have hzM : z0 ∈ M0 := (hM0 z0).2 ((hRm z0 0).1 ht)
    have hcard1 : (R z0).card ≤ 1 := by
      have := Finset.card_le_card hsub1
      rwa [Finset.card_singleton] at this
    have hzA : z0 ∉ A := fun h => by
      have := ((hA z0).1 h).2
      omega
    have hsub : A ⊆ M0.erase z0 :=
      fun g hg => Finset.mem_erase.2 ⟨fun e => hzA (e ▸ hg), hAsub hg⟩
    have c1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hzM] at c1
    have c2 := Finset.card_le_card hJE
    omega

theorem main_aux : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    37 ≤ gates.length := by
  intro L hL gates o legal hout
  obtain rfl : L = s_lines := funext hL
  obtain ⟨new, hfan, hrb, hl, hrep⟩ :=
    r_inv_all (fun (x : Fin 13 → Bool) => x) (fun i => Or.inr (fun x => rfl)) gates legal
  have hsel : ∀ t : Fin 13, ∃ j : ℕ, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨new, j⟩ (List.ofFn x) = Circuit.eval ⟨gates, o t⟩ (List.ofFn x) := by
    intro t
    rcases hrep (o t) with ⟨c, hc⟩ | ⟨j, _, hj⟩
    · exfalso
      have e1 := hout t (fun _ => true) (Or.inl rfl)
      have e2 := hout t (co t) (co_F t)
      have a1 : Circuit.eval ⟨gates, o t⟩ (List.ofFn (fun _ : Fin 13 => true)) = c := hc _
      have a2 : Circuit.eval ⟨gates, o t⟩ (List.ofFn (co t)) = c := hc _
      rw [a1] at e1
      rw [a2] at e2
      have l1 : decide (∃ v ∈ s_lines t, (fun _ : Fin 13 => true) v = true) = true :=
        decide_eq_true ⟨t, lines_self t, rfl⟩
      have l2 : decide (∃ v ∈ s_lines t, co t v = true) = false := by simp [co]
      rw [l1] at e1
      rw [l2] at e2
      rw [e1] at e2
      exact Bool.noConfusion e2
    · exact ⟨j, fun x => hj x⟩
  choose o' ho' using hsel
  have hlen : 37 ≤ new.length := by
    refine core new o' (fun g hg => ⟨(hfan g hg).1, le_of_eq (hfan g hg).2⟩) ?_
      (fun t x hx => (ho' t x).trans (hout t x hx))
    intro i
    have hf := (hfan new[(i : ℕ)] (List.getElem_mem i.2)).2
    refine ⟨?_, fun a ha => ?_⟩
    · show 1 ≤ new[(i : ℕ)].inputs.length
      rw [hf]
      norm_num
    · exact hrb i i.2 a (by rw [List.getD_eq_getElem _ _ i.2]; exact ha)
  exact le_trans hlen hl

end PEqualNP.Outside.L_meta_1576

theorem PEqualNP.Outside.L_meta_1576 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    37 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1576.main_aux
