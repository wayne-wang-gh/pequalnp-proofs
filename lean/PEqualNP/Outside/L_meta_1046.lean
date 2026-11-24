import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1046

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

abbrev Input := Fin 6 → Bool
abbrev Wire := Input → Bool

def S : Fin 7 → Finset (Fin 6) :=
  ![{0, 2}, {3, 4}, {1, 5}, {0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {0, 4, 5}]

def hit (l : Fin 7) (x : Input) := ∃ v ∈ S l, x v = true

def single (p : Fin 6) : Input := fun k => decide (k = p)

def outside (l : Fin 7) : Input := fun k => decide (k ∉ S l)

lemma same_line : ∀ (l m : Fin 7) (p q : Fin 6), p ∈ S l → q ∈ S l → p ≠ q →
    p ∈ S m → q ∈ S m → l = m := by
  unfold S
  decide

lemma two_points : ∀ l : Fin 7, ∃ p ∈ S l, ∃ q ∈ S l, p ≠ q := by
  unfold S
  decide

lemma hit_single (l : Fin 7) (p : Fin 6) : hit l (single p) ↔ p ∈ S l := by
  simp [hit, single]

lemma miss (l : Fin 7) : ¬ hit l (outside l) := by
  rintro ⟨v, hv, hx⟩
  simp [outside, hv] at hx

def Low (l : Fin 7) (f : Wire) := ∀ x, f x = true → hit l x
def High (l : Fin 7) (f : Wire) := ∀ x, hit l x → f x = true
def Exact (l : Fin 7) (f : Wire) := ∀ x, f x = true ↔ hit l x

def Good (l : Fin 7) (f : Wire) :=
  (Low l f ∨ High l f) ∧
  (∃ p ∈ S l, ∃ q ∈ S l, p ≠ q ∧ f (single p) = true ∧ f (single q) = true) ∧
  f (outside l) = false

lemma exact_good {l : Fin 7} {f : Wire} (h : Exact l f) : Good l f := by
  obtain ⟨p, hp, q, hq, hne⟩ := two_points l
  exact ⟨Or.inl (fun x => (h x).1),
    ⟨p, hp, q, hq, hne, (h _).2 ((hit_single _ _).2 hp), (h _).2 ((hit_single _ _).2 hq)⟩,
    Bool.eq_false_iff.mpr (fun ht => miss l ((h _).1 ht))⟩

lemma unique_line {l m : Fin 7} {f : Wire} (h : Good l f) (h' : Good m f) : l = m := by
  obtain ⟨_, ⟨p, hp, q, hq, hn, hpf, hqf⟩, hf⟩ := h
  rcases h'.1 with low | high
  · exact same_line l m p q hp hq hn ((hit_single _ _).1 (low _ hpf))
      ((hit_single _ _).1 (low _ hqf))
  · have inc (r : Fin 6) (hr : r ∈ S m) : r ∈ S l := by
      by_contra hh
      have ht := high (outside l) ⟨r, hr, by simp [outside, hh]⟩
      simp [hf] at ht
    obtain ⟨a, ha, b, hb, hab⟩ := two_points m
    exact (same_line m l a b ha hb hab (inc a ha) (inc b hb)).symm

def Falls (f : Wire) := ∀ x y : Input, (∀ k, x k = true → y k = true) →
  f y = true → f x = true

lemma good_rises {l : Fin 7} {f : Wire} (h : Good l f) : ¬ Falls f := by
  rintro hf
  obtain ⟨hl | hh, ⟨p, _, _, _, _, hc, _⟩, ho⟩ := h
  · have h0 := hf (fun _ => false) _ (by simp) hc
    obtain ⟨_, _, hn⟩ := hl _ h0
    simp at hn
  · obtain ⟨a, ha, _⟩ := two_points l
    have h1 := hh (fun _ => true) ⟨a, ha, rfl⟩
    have ht := hf (outside l) (fun _ => true) (by simp) h1
    simp [ho] at ht

lemma const_falls (b : Bool) : Falls (fun _ => b) := fun _ _ _ h => h

lemma good_or {l : Fin 7} {u v : Wire} (h3 : (S l).card = 3)
    (he : Exact l (fun x => u x || v x)) : Good l u ∨ Good l v := by
  obtain ⟨a, b, c, hab, hac, hbc, hS⟩ := Finset.card_eq_three.1 h3
  have lu : Low l u := fun x h => (he x).1 (by simp [h])
  have lv : Low l v := fun x h => (he x).1 (by simp [h])
  have fu : u (outside l) = false := Bool.eq_false_iff.mpr (fun h => miss l (lu _ h))
  have fv : v (outside l) = false := Bool.eq_false_iff.mpr (fun h => miss l (lv _ h))
  have ma : a ∈ S l := by rw [hS]; simp
  have mb : b ∈ S l := by rw [hS]; simp
  have mc : c ∈ S l := by rw [hS]; simp
  have cov (p : Fin 6) (hp : p ∈ S l) : u (single p) = true ∨ v (single p) = true := by
    have := (he (single p)).2 ((hit_single _ _).2 hp)
    simpa only [Bool.or_eq_true] using this
  have gu (p q : Fin 6) (hp : p ∈ S l) (hq : q ∈ S l) (hn : p ≠ q)
      (h1 : u (single p) = true) (h2 : u (single q) = true) : Good l u ∨ Good l v :=
    Or.inl ⟨Or.inl lu, ⟨p, hp, q, hq, hn, h1, h2⟩, fu⟩
  have gv (p q : Fin 6) (hp : p ∈ S l) (hq : q ∈ S l) (hn : p ≠ q)
      (h1 : v (single p) = true) (h2 : v (single q) = true) : Good l u ∨ Good l v :=
    Or.inr ⟨Or.inl lv, ⟨p, hp, q, hq, hn, h1, h2⟩, fv⟩
  rcases cov a ma with x | x <;> rcases cov b mb with y | y <;> rcases cov c mc with z | z
  all_goals first
    | exact gu a b ma mb hab x y
    | exact gu a c ma mc hac x z
    | exact gu b c mb mc hbc y z
    | exact gv a b ma mb hab x y
    | exact gv a c ma mc hac x z
    | exact gv b c mb mc hbc y z

lemma good_and {l : Fin 7} {u v : Wire}
    (he : Exact l (fun x => u x && v x)) : Good l u ∨ Good l v := by
  have hh (x : Input) (h : hit l x) : u x = true ∧ v x = true := by
    have ht := (he x).2 h
    simpa only [Bool.and_eq_true] using ht
  obtain ⟨p, hp, q, hq, hn⟩ := two_points l
  have makeGood (f : Wire) (h : High l f) (hf : f (outside l) = false) : Good l f :=
    ⟨Or.inr h, ⟨p, hp, q, hq, hn, h _ ((hit_single _ _).2 hp), h _ ((hit_single _ _).2 hq)⟩, hf⟩
  cases hu : u (outside l) with
  | false => exact Or.inl (makeGood _ (fun x h => (hh x h).1) hu)
  | true =>
    apply Or.inr (makeGood _ (fun x h => (hh x h).2) _)
    apply Bool.eq_false_iff.mpr
    intro hv
    exact miss l ((he _).1 (by simp [hu, hv]))

def wire (gs : List Gate) (i : ℕ) (x : Input) :=
  (wiresFrom gs (List.ofFn x)).getD i false

def prior (gs : List Gate) (k i : ℕ) : Wire :=
  if i < 6 + k then wire gs i else fun _ => false

lemma prior_apply (gs : List Gate) (k i : ℕ) (x : Input) :
    prior gs k i x = if i < 6 + k then wire gs i x else false := by
  by_cases h : i < 6 + k <;> simp [prior, h]

lemma wire_gate (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : Input) :
    wire gs (6 + k) x = gs[k].op.eval (gs[k].inputs.map (fun i => prior gs k i x)) := by
  simpa only [prior_apply, wire, List.length_ofFn] using
    getD_wiresFrom_gate gs (List.ofFn x) k hk

lemma good_in_range {gs : List Gate} {i : ℕ} {l : Fin 7} (h : Good l (wire gs i)) :
    6 ≤ i ∧ i < 6 + gs.length := by
  obtain ⟨_, ⟨p, _, q, _, hn, hc, hd⟩, _⟩ := h
  constructor
  · by_contra! hi
    have inp (x : Input) : wire gs i x = x ⟨i, hi⟩ := by
      unfold wire
      rw [getD_wiresFrom_lt _ _ _ (by simpa)]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] : i < (List.ofFn x).length),
        List.getElem_ofFn]
    rw [inp] at hc hd
    exact hn ((of_decide_eq_true hc).symm.trans (of_decide_eq_true hd))
  · by_contra! hi
    unfold wire at hc
    rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using hi)] at hc
    contradiction

lemma from_prior {gs : List Gate} {k i : ℕ} {l : Fin 7} (P : Wire → Prop)
    (hP : ∀ f, P f → Good l f) (h : P (prior gs k i)) :
    ∃ j < 6 + k, P (wire gs j) := by
  unfold prior at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · exact False.elim (good_rises (hP _ h) (const_falls false))

def Fan (gs : List Gate) := ∀ g ∈ gs,
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def OnlyOne (gs : List Gate) := ∀ i j : Fin gs.length,
  (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j

def Bin (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

lemma not_falls (gs : List Gate) (hf : Fan gs) (hu : OnlyOne gs)
    (k : ℕ) (hk : k < gs.length) (hop : gs[k].op = GateOp.not) :
    Falls (wire gs (6 + k)) := by
  have hm : ∀ g ∈ gs.take k, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hik : i < k := by simp only [List.length_take] at hi; omega
    have hil : i < gs.length := by omega
    rw [List.getElem_take]
    have hg' := (hf gs[i] (List.getElem_mem hil)).1
    rcases hg' with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have he := hu ⟨i, hil⟩ ⟨k, hk⟩ h hop
      have he' : i = k := congrArg Fin.val he
      omega
  intro x y hxy
  have hle (i : ℕ) : prior gs k i x = true → prior gs k i y = true := by
    have hv (z : Input) : prior gs k i z =
        (wiresFrom (gs.take k) (List.ofFn z)).getD i false := by
      rw [getD_wiresFrom_take _ _ _ _ (by omega)]
      simp only [prior_apply, wire, List.length_ofFn]
    rw [hv, hv]
    apply wiresFrom_mono _ hm _ _ (by simp)
    intro t ht
    by_cases h : t < 6
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at ht ⊢
      simp only [List.getElem_ofFn] at ht ⊢
      exact hxy ⟨t, h⟩ ht
    · rw [List.getD_eq_default _ _ (by simp; omega)] at ht
      contradiction
  rw [wire_gate _ _ hk, wire_gate _ _ hk, hop]
  cases he : gs[k].inputs with
  | nil => simp [GateOp.eval]
  | cons i is =>
    simp only [List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_true']
    exact fun hy => Bool.eq_false_iff.mpr (fun hx => by simpa [hy] using hle i hx)

lemma trace (gs : List Gate) (hf : Fan gs) (hu : OnlyOne gs) (l : Fin 7)
    (P : Wire → Prop) (hP : ∀ f, P f → Good l f) :
    ∀ i, P (wire gs i) → ∃ k, ∃ hk : k < gs.length, Bin gs[k] ∧ 6 + k ≤ i ∧
      P (wire gs (6 + k)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    obtain ⟨h6, hlt⟩ := good_in_range (hP _ h)
    obtain ⟨k, rfl⟩ : ∃ k, i = 6 + k := ⟨i - 6, by omega⟩
    have hk : k < gs.length := by omega
    have ha := hf gs[k] (List.getElem_mem hk)
    have eqn (x : Input) : wire gs (6 + k) x =
        gs[k].op.eval (gs[k].inputs.map (fun i => prior gs k i x)) := wire_gate _ _ hk x
    have bad (b : Bool) (hb : ∀ x, wire gs (6 + k) x = b) : False := by
      apply good_rises (hP _ h)
      intro x y _ ht
      rwa [hb x, ← hb y]
    rcases ha.1 with hop | hop | hop
    · cases hin : gs[k].inputs with
      | nil => exact (bad true (by simp [eqn, hin, hop, GateOp.eval])).elim
      | cons a rest =>
        cases rest with
        | nil =>
          have hw : wire gs (6 + k) = prior gs k a := by
            funext x
            simp [eqn, hin, hop, GateOp.eval]
          rw [hw] at h
          obtain ⟨j, hj, hpj⟩ := from_prior P hP h
          obtain ⟨k', hk', hb, hle, hp⟩ := ih j hj hpj
          exact ⟨k', hk', hb, by omega, hp⟩
        | cons b more =>
          have em : more = [] := by
            have := ha.2
            rw [hin] at this
            simpa using this
          exact ⟨k, hk, ⟨Or.inl hop, by rw [hin, em]; rfl⟩, le_refl _, h⟩
    · cases hin : gs[k].inputs with
      | nil => exact (bad false (by simp [eqn, hin, hop, GateOp.eval])).elim
      | cons a rest =>
        cases rest with
        | nil =>
          have hw : wire gs (6 + k) = prior gs k a := by
            funext x
            simp [eqn, hin, hop, GateOp.eval]
          rw [hw] at h
          obtain ⟨j, hj, hpj⟩ := from_prior P hP h
          obtain ⟨k', hk', hb, hle, hp⟩ := ih j hj hpj
          exact ⟨k', hk', hb, by omega, hp⟩
        | cons b more =>
          have em : more = [] := by
            have := ha.2
            rw [hin] at this
            simpa using this
          exact ⟨k, hk, ⟨Or.inr hop, by rw [hin, em]; rfl⟩, le_refl _, h⟩
    · exact (good_rises (hP _ h) (not_falls gs hf hu k hk hop)).elim

lemma second (gs : List Gate) (hf : Fan gs) (hu : OnlyOne gs) (l : Fin 7)
    (h3 : (S l).card = 3) (k : ℕ) (hk : k < gs.length) (hb : Bin gs[k])
    (he : Exact l (wire gs (6 + k))) :
    ∃ k', ∃ hk' : k' < gs.length, k' < k ∧ Bin gs[k'] ∧ Good l (wire gs (6 + k')) := by
  obtain ⟨hop, hlen⟩ := hb
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
  have eqn (x : Input) : wire gs (6 + k) x =
      gs[k].op.eval (gs[k].inputs.map (fun i => prior gs k i x)) := wire_gate _ _ hk x
  have hg : Good l (prior gs k a) ∨ Good l (prior gs k b) := by
    rcases hop with hop | hop
    · apply good_and
      intro x
      have := he x
      simpa [eqn, hab, hop, GateOp.eval] using this
    · apply good_or h3
      intro x
      have := he x
      simpa [eqn, hab, hop, GateOp.eval] using this
  have fin (c : ℕ) (hc : Good l (prior gs k c)) :
      ∃ k', ∃ hk' : k' < gs.length, k' < k ∧ Bin gs[k'] ∧ Good l (wire gs (6 + k')) := by
    obtain ⟨j, hj, hgj⟩ := from_prior (Good l) (fun _ h => h) hc
    obtain ⟨k', hk', hb', hle, hp⟩ := trace gs hf hu l (Good l) (fun _ h => h) j hgj
    exact ⟨k', hk', by omega, hb', hp⟩
  rcases hg with hg | hg
  · exact fin a hg
  · exact fin b hg

lemma card_P : (Finset.univ.filter
    (fun p : Fin 7 × Bool => p.2 = false ∨ (S p.1).card = 3)).card = 11 := by
  unfold S
  decide

lemma count (gs : List Gate) (out : Fin 7 → ℕ) (hf : Fan gs) (hu : OnlyOne gs)
    (he : ∀ l, Exact l (wire gs (out l))) (I : Finset (Fin gs.length))
    (hI : ∀ q : Fin gs.length, Bin (gs.get q) → q ∈ I) : 11 ≤ I.card := by
  classical
  have h1 : ∀ l : Fin 7, ∃ k : Fin gs.length, Bin (gs.get k) ∧ Exact l (wire gs (6 + k.val)) := by
    intro l
    obtain ⟨k, hk, hb, _, hp⟩ := trace gs hf hu l (Exact l) (fun _ h => exact_good h) _ (he l)
    exact ⟨⟨k, hk⟩, hb, hp⟩
  choose k1 hk1b hk1e using h1
  have h2 : ∀ l : Fin 7, ∃ k : Fin gs.length, (S l).card = 3 →
      (k ≠ k1 l ∧ Bin (gs.get k) ∧ Good l (wire gs (6 + k.val))) := by
    intro l
    by_cases h3 : (S l).card = 3
    · obtain ⟨k', hk', hlt, hb, hg⟩ :=
        second gs hf hu l h3 (k1 l).val (k1 l).isLt (hk1b l) (hk1e l)
      refine ⟨⟨k', hk'⟩, fun _ => ⟨?_, hb, hg⟩⟩
      intro heq
      have := congrArg Fin.val heq
      simp at this
      omega
    · exact ⟨k1 l, fun h => (h3 h).elim⟩
  choose k2 hk2 using h2
  let idx : Fin 7 × Bool → Fin gs.length := fun p => if p.2 then k2 p.1 else k1 p.1
  let P := Finset.univ.filter (fun p : Fin 7 × Bool => p.2 = false ∨ (S p.1).card = 3)
  have prop (p : Fin 7 × Bool) (hp : p ∈ P) :
      Bin (gs.get (idx p)) ∧ Good p.1 (wire gs (6 + (idx p).val)) := by
    rcases p with ⟨l, bb⟩
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    cases bb with
    | false => exact ⟨hk1b l, exact_good (hk1e l)⟩
    | true =>
      have h3 : (S l).card = 3 := by simpa using hp
      exact ⟨(hk2 l h3).2.1, (hk2 l h3).2.2⟩
  have inj : Set.InjOn idx P := by
    intro p hp p' hp' heq
    have g1 := (prop p hp).2
    have g2 := (prop p' hp').2
    rw [heq] at g1
    have hl : p.1 = p'.1 := unique_line g1 g2
    rcases p with ⟨l, bb⟩
    rcases p' with ⟨l', bb'⟩
    simp only at hl
    subst hl
    simp only [P, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hp'
    cases bb <;> cases bb'
    · rfl
    · have h3 : (S l).card = 3 := by simpa using hp'
      exact ((hk2 l h3).1 (by simpa [idx] using heq.symm)).elim
    · have h3 : (S l).card = 3 := by simpa using hp
      exact ((hk2 l h3).1 (by simpa [idx] using heq)).elim
    · rfl
  have hle := Finset.card_le_card_of_injOn idx (fun p hp => hI _ (prop p hp).1) inj
  rw [card_P] at hle
  exact hle

end PEqualNP.Outside.L_meta_1046


theorem PEqualNP.Outside.L_meta_1046 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (o : Fin 7) (x : Fin 6 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ (![{0, 2}, {3, 4}, {1, 5}, {0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {0, 4, 5}] : Fin 7 → Finset (Fin 6)) o, x v = true)) → ∀ I : Finset (Fin gates.length), (∀ q : Fin gates.length, ((gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q).inputs.length = 2 → q ∈ I) → 11 ≤ I.card := by
  intro gates out hf hnot hout I hI
  apply PEqualNP.Outside.L_meta_1046.count gates out hf _ _ I hI
  · obtain ⟨ι, hι⟩ := hnot
    intro i j hi hj
    obtain ⟨a, ha⟩ := hι i hi
    obtain ⟨b, hb⟩ := hι j hj
    rw [← ha, ← hb, Subsingleton.elim a b]
  · intro l x
    have h := hout l x
    show PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out l⟩ (List.ofFn x) = true ↔ _
    rw [h]
    simp only [decide_eq_true_eq]
    rfl
