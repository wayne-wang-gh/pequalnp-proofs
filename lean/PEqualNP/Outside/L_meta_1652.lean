import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1652

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega

open PEqualNP.TopForm

lemma fin2 : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide

lemma e10 : (1 - 0 : Fin 2) = 1 := by decide

lemma e11 : (1 - 1 : Fin 2) = 0 := by decide

lemma two_inputs {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {k : ℕ} (hk : k < C.gates.length) :
    ∃ p q, (gateAt C k).inputs = [p, q] ∧ p < n + k ∧ q < n + k ∧ opnd C k 0 = p ∧
      opnd C k 1 = q := by
  obtain ⟨_, hRB, h2⟩ := hA
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
  exact ⟨p, q, hin, hRB k hk p (by rw [hin]; simp), hRB k hk q (by rw [hin]; simp),
    by simp [opnd, hin], by simp [opnd, hin]⟩

lemma reach_input {n : ℕ} {C : Circuit} {w w' : ℕ} (hw : w < n)
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' = w := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hstep, _⟩
  · exact h.symm
  · obtain ⟨k, _, e, _⟩ := hstep
    omega

lemma reach_gate {n : ℕ} {C : Circuit} {k w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) (n + k) w') :
    w' = n + k ∨ (k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ c ∈ (gateAt C k).inputs, c < n + k ∧ Relation.ReflTransGen (OrStep n C) c w') := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hstep, hr⟩
  · exact Or.inl h.symm
  · obtain ⟨k', hk', e, hop, hin, hlt⟩ := hstep
    have hkk : k' = k := by omega
    subst hkk
    exact Or.inr ⟨hk', hop, c, hin, hlt, hr⟩

lemma orIn_card_input {n : ℕ} {C : Circuit} {w : ℕ} (hw : w < n) : (orIn n C w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have h1 := reach_input hw (mem_orIn_reach a ha)
  have h2 := reach_input hw (mem_orIn_reach b hb)
  exact Fin.ext (h1.trans h2.symm)

lemma orIn_gate {n : ℕ} {C : Circuit} {k : ℕ} (u : Fin n) (hu : u ∈ orIn n C (n + k)) :
    k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ c ∈ (gateAt C k).inputs, c < n + k ∧ u ∈ orIn n C c := by
  rcases reach_gate (mem_orIn_reach u hu) with h | ⟨hk, hop, c, hc, hlt, hr⟩
  · have := u.isLt
    omega
  · exact ⟨hk, hop, c, hc, hlt, reach_mem_orIn u hr⟩

lemma orIn_up {n : ℕ} {C : Circuit} {k c : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hc : c ∈ (gateAt C k).inputs) (hlt : c < n + k) :
    orIn n C c ⊆ orIn n C (n + k) := by
  intro u hu
  exact reach_mem_orIn u
    (Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hc, hlt⟩ (mem_orIn_reach u hu))

lemma orIn_mono {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : orIn n C w' ⊆ orIn n C w := by
  intro u hu
  exact reach_mem_orIn u (h.trans (mem_orIn_reach u hu))

lemma not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} {k : ℕ}
    (u : Fin n) (hu : u ∈ orIn n C (n + k)) : ¬ BelowF G C k := by
  intro hb
  have h1 : val C (List.ofFn (pairInput u u)) (n + k) = true :=
    reach_var_val _ _ u (mem_orIn_reach u hu) (pairInput_left u u)
  have h2 := hb (pairInput u u) h1
  exact G.irrefl ((graphFun_pair G u u).mp h2)

noncomputable def dset (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k => OrReaches n C w k ∧
    (gateAt C k).op = GateOp.or ∧
    (orIn n C (opnd C k 0)).Nonempty ∧ (orIn n C (opnd C k 1)).Nonempty

lemma mem_dset {n : ℕ} {C : Circuit} {w k : ℕ} : k ∈ dset n C w ↔ k < C.gates.length ∧
    OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
    (orIn n C (opnd C k 0)).Nonempty ∧ (orIn n C (opnd C k 1)).Nonempty := by
  unfold dset
  simp only [Finset.mem_filter, Finset.mem_range]

lemma count_abs {α : Type} [DecidableEq α] (f : ℕ → Finset α) (d : ℕ → Finset ℕ)
    (h : ∀ m, (f m).card ≤ 1 ∨ (∃ q, q < m ∧ f m ⊆ f q ∧ d q ⊆ d m) ∨
      (∃ p q k, p < m ∧ q < m ∧ f m ⊆ f p ∪ f q ∧ d p ⊆ d m ∧ d q ⊆ d m ∧ k ∈ d m ∧
        ∀ w, w < m → k ∉ d w)) :
    ∀ m (W : Finset ℕ), (∀ w ∈ W, w < m) →
      (W.biUnion f).card ≤ W.card + (W.biUnion d).card := by
  intro m
  induction m with
  | zero =>
    intro W hW
    have hW0 : W = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun w hw => by have := hW w hw; omega)
    subst hW0
    simp
  | succ m ih =>
    intro W hW
    by_cases hm : m ∈ W
    · have hW' : ∀ w ∈ W.erase m, w < m := by
        intro w hw
        have h1 := hW w (Finset.mem_of_mem_erase hw)
        have h2 := Finset.ne_of_mem_erase hw
        omega
      have hc : (W.erase m).card + 1 = W.card := Finset.card_erase_add_one hm
      have hD : (W.erase m).biUnion d ⊆ W.biUnion d :=
        Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset _ _)
      have hdm : d m ⊆ W.biUnion d := Finset.subset_biUnion_of_mem d hm
      have hU : W.biUnion f = f m ∪ (W.erase m).biUnion f := by
        rw [← Finset.biUnion_insert, Finset.insert_erase hm]
      rcases h m with h1 | ⟨q, hq, hfq, hdq⟩ | ⟨p, q, k, hp, hq, hf, hdp, hdq, hk, hkn⟩
      · have h0 := ih (W.erase m) hW'
        have h2 := Finset.card_union_le (f m) ((W.erase m).biUnion f)
        have h3 := Finset.card_le_card hD
        rw [hU]
        omega
      · have hW2 : ∀ w ∈ insert q (W.erase m), w < m := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hq
          · exact hW' w hw
        have h1 := ih _ hW2
        have h2 : W.biUnion f ⊆ (insert q (W.erase m)).biUnion f := by
          rw [hU, Finset.biUnion_insert]
          exact Finset.union_subset_union hfq (Finset.Subset.refl _)
        have h3 : (insert q (W.erase m)).biUnion d ⊆ W.biUnion d := by
          rw [Finset.biUnion_insert]
          exact Finset.union_subset (hdq.trans hdm) hD
        have h4 := Finset.card_insert_le q (W.erase m)
        have h5 := Finset.card_le_card h2
        have h6 := Finset.card_le_card h3
        omega
      · obtain ⟨W2, hW2def⟩ : ∃ W2, W2 = insert p (insert q (W.erase m)) := ⟨_, rfl⟩
        have hW2 : ∀ w ∈ W2, w < m := by
          intro w hw
          rw [hW2def] at hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hp
          · rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hq
            · exact hW' w hw
        have h1 := ih _ hW2
        have h2 : W.biUnion f ⊆ W2.biUnion f := by
          rw [hU, hW2def, Finset.biUnion_insert, Finset.biUnion_insert, ← Finset.union_assoc]
          exact Finset.union_subset_union hf (Finset.Subset.refl _)
        have h3 : insert k (W2.biUnion d) ⊆ W.biUnion d := by
          rw [hW2def, Finset.biUnion_insert, Finset.biUnion_insert]
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hdm hk
          · rcases Finset.mem_union.mp hx with hx | hx
            · exact hdm (hdp hx)
            · rcases Finset.mem_union.mp hx with hx | hx
              · exact hdm (hdq hx)
              · exact hD hx
        have hkn2 : k ∉ W2.biUnion d := by
          intro hx
          obtain ⟨w, hw, hkw⟩ := Finset.mem_biUnion.mp hx
          exact hkn w (hW2 w hw) hkw
        have h4 : W2.card ≤ (W.erase m).card + 2 := by
          have a1 := Finset.card_insert_le p (insert q (W.erase m))
          have a2 := Finset.card_insert_le q (W.erase m)
          rw [hW2def]
          omega
        have h5 := Finset.card_le_card h2
        have h6 := Finset.card_le_card h3
        rw [Finset.card_insert_of_notMem hkn2] at h6
        omega
    · apply ih W
      intro w hw
      have h1 := hW w hw
      have h2 : w ≠ m := fun e => hm (e ▸ hw)
      omega

lemma count_hyp {n : ℕ} {C : Circuit} (hA : IsAO2 n C) (m : ℕ) :
    (orIn n C m).card ≤ 1 ∨
    (∃ q, q < m ∧ orIn n C m ⊆ orIn n C q ∧ dset n C q ⊆ dset n C m) ∨
    (∃ p q k, p < m ∧ q < m ∧ orIn n C m ⊆ orIn n C p ∪ orIn n C q ∧
      dset n C p ⊆ dset n C m ∧ dset n C q ⊆ dset n C m ∧ k ∈ dset n C m ∧
      ∀ w, w < m → k ∉ dset n C w) := by
  by_cases hm : m < n
  · exact Or.inl (orIn_card_input hm)
  · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    by_cases hgo : k < C.gates.length ∧ (gateAt C k).op = GateOp.or
    · obtain ⟨hk, hop⟩ := hgo
      obtain ⟨p, q, hin, hp, hq, e0, e1⟩ := two_inputs hA hk
      have hsub : orIn n C (n + k) ⊆ orIn n C p ∪ orIn n C q := by
        intro u hu
        obtain ⟨_, _, c, hc, _, huc⟩ := orIn_gate u hu
        rw [hin] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact Finset.mem_union_left _ huc
        · exact Finset.mem_union_right _ huc
      have hd : ∀ c, c ∈ (gateAt C k).inputs → c < n + k →
          dset n C c ⊆ dset n C (n + k) := by
        intro c hc hlt g hg
        rw [mem_dset] at hg ⊢
        exact ⟨hg.1, (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hc, hlt, hg.2.1⟩⟩, hg.2.2⟩
      have hpin : p ∈ (gateAt C k).inputs := by rw [hin]; simp
      have hqin : q ∈ (gateAt C k).inputs := by rw [hin]; simp
      by_cases hpe : (orIn n C p).Nonempty
      · by_cases hqe : (orIn n C q).Nonempty
        · refine Or.inr (Or.inr ⟨p, q, k, hp, hq, hsub, hd p hpin hp, hd q hqin hq, ?_, ?_⟩)
          · rw [mem_dset]
            exact ⟨hk, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hop,
              by rw [e0]; exact hpe, by rw [e1]; exact hqe⟩
          · intro w hw hmem
            rw [mem_dset] at hmem
            have h3 := orStep_le (orReaches_reach k w hmem.2.1).1
            omega
        · refine Or.inr (Or.inl ⟨p, hp, ?_, hd p hpin hp⟩)
          intro u hu
          rcases Finset.mem_union.mp (hsub hu) with h | h
          · exact h
          · exact (hqe ⟨u, h⟩).elim
      · refine Or.inr (Or.inl ⟨q, hq, ?_, hd q hqin hq⟩)
        intro u hu
        rcases Finset.mem_union.mp (hsub hu) with h | h
        · exact (hpe ⟨u, h⟩).elim
        · exact h
    · left
      have he : orIn n C (n + k) = ∅ := Finset.eq_empty_of_forall_notMem
        (fun u hu => hgo ⟨(orIn_gate u hu).1, (orIn_gate u hu).2.1⟩)
      rw [he]
      simp

lemma lca {n : ℕ} {C : Circuit} (hA : IsAO2 n C) (h1 h2 : ℕ)
    (hn1 : ¬ Relation.ReflTransGen (OrStep n C) (n + h1) (n + h2))
    (hn2 : ¬ Relation.ReflTransGen (OrStep n C) (n + h2) (n + h1)) :
    ∀ r, Relation.ReflTransGen (OrStep n C) r (n + h1) →
      Relation.ReflTransGen (OrStep n C) r (n + h2) →
      ∃ g p q, g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧
        Relation.ReflTransGen (OrStep n C) r (n + g) ∧
        p ∈ (gateAt C g).inputs ∧ q ∈ (gateAt C g).inputs ∧ p < n + g ∧ q < n + g ∧
        opnd C g 0 = p ∧ opnd C g 1 = q ∧
        ((Relation.ReflTransGen (OrStep n C) p (n + h1) ∧
            Relation.ReflTransGen (OrStep n C) q (n + h2)) ∨
          (Relation.ReflTransGen (OrStep n C) p (n + h2) ∧
            Relation.ReflTransGen (OrStep n C) q (n + h1))) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr1 hr2
    rcases Relation.ReflTransGen.cases_head hr1 with e | ⟨c1, hs1, hc1⟩
    · rw [e] at hr2
      exact (hn1 hr2).elim
    rcases Relation.ReflTransGen.cases_head hr2 with e | ⟨c2, hs2, hc2⟩
    · rw [e] at hr1
      exact (hn2 hr1).elim
    obtain ⟨k, hk, hrk, hop, hin1, hlt1⟩ := hs1
    obtain ⟨k', hk', e, _, hin2, hlt2⟩ := hs2
    have hkk : k' = k := by omega
    subst hkk
    obtain ⟨p, q, hin, hp, hq, e0, e1⟩ := two_inputs hA hk
    have hpin : p ∈ (gateAt C k').inputs := by rw [hin]; simp
    have hqin : q ∈ (gateAt C k').inputs := by rw [hin]; simp
    by_cases hcc : c1 = c2
    · rw [← hcc] at hc2
      obtain ⟨g, p', q', hg, hgop, hrg, rest⟩ := ih c1 (by omega) hc1 hc2
      exact ⟨g, p', q', hg, hgop,
        Relation.ReflTransGen.head ⟨k', hk, hrk, hop, hin1, hlt1⟩ hrg, rest⟩
    · rw [hin] at hin1 hin2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1 hin2
      refine ⟨k', p, q, hk, hop, by rw [hrk], hpin, hqin, hp, hq, e0, e1, ?_⟩
      rcases hin1 with h1e | h1e <;> rcases hin2 with h2e | h2e
      · exact (hcc (h1e.trans h2e.symm)).elim
      · rw [h1e] at hc1
        rw [h2e] at hc2
        exact Or.inl ⟨hc1, hc2⟩
      · rw [h1e] at hc1
        rw [h2e] at hc2
        exact Or.inr ⟨hc2, hc1⟩
      · exact (hcc (h1e.trans h2e.symm)).elim

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (c : Fin n) (T M : Finset ℕ) (L : Finset (Fin n))
    (hT : ∀ t, t ∈ T ↔ t ∈ tops G C ∧ ∃ p : Fin 2, side (n := n) C t (1 - p) = {c})
    (hM : ∀ h, h ∈ M ↔ h ∈ lam G C ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
      side (n := n) C a (1 - b) = {c} ∧ OrReaches n C (opnd C a b) h)
    (hLd : ∀ v, v ∈ L ↔ ∃ d ∈ tops G C, ∃ q : Fin 2, side (n := n) C d (1 - q) = {c} ∧
      v ∈ side (n := n) C d q)
    (Bc : Finset (Finset (Fin n))) (hB : ∀ X ∈ Bc, ∃ k ∈ M, orIn n C (n + k) = X) :
    (∀ w ∈ L, G.Adj c w ∧ s(c, w) ∈ starEdges G C) ∧ L.card ≤ T.card + M.card ∧
    (Bc.Nonempty → Bc.card + 1 ≤ T.card + M.card) ∧
    (Bc.Nonempty → (∀ X' ∈ Bc, ∃ X'' ∈ Bc, ¬ X'' ⊆ X') → Bc.card + 2 ≤ T.card + M.card) := by
  classical
  have hA : IsAO2 n C := hL.1
  have tf := fun a ha => top_facts G C h4 hL a ha
  obtain ⟨phi, hphi⟩ : ∃ phi : ℕ → ℕ, ∀ t ∈ tops G C, ∀ p : Fin 2,
      side (n := n) C t (1 - p) = {c} → opnd C t p = phi t := by
    refine ⟨fun t => if side (n := n) C t 1 = {c} then opnd C t 0 else opnd C t 1, ?_⟩
    intro t ht p hp
    obtain ⟨hdis, _, _⟩ := tf t ht
    show opnd C t p = if side (n := n) C t 1 = {c} then opnd C t 0 else opnd C t 1
    split_ifs with h1
    · rcases fin2 p with rfl | rfl
      · rfl
      · rw [e11] at hp
        rw [hp, h1] at hdis
        exact ((Finset.disjoint_left.mp hdis) (Finset.mem_singleton_self c)
          (Finset.mem_singleton_self c)).elim
    · rcases fin2 p with rfl | rfl
      · rw [e10] at hp
        exact (h1 hp).elim
      · rfl
  have inM : ∀ t ∈ tops G C, ∀ p : Fin 2, side (n := n) C t (1 - p) = {c} → ∀ k,
      k < C.gates.length → OrReaches n C (opnd C t p) k → (gateAt C k).op = GateOp.or →
      (orIn n C (opnd C k 0)).Nonempty → (orIn n C (opnd C k 1)).Nonempty → k ∈ M := by
    intro t ht p hp k hk hr hop ne0 ne1
    rw [hM]
    refine ⟨?_, t, ht, p, hp, hr⟩
    obtain ⟨p', q', hin, hp', hq', e0, e1⟩ := two_inputs hA hk
    obtain ⟨u, hu⟩ := id ne0
    have hu2 : u ∈ orIn n C p' := by rw [← e0]; exact hu
    have hu' : u ∈ orIn n C (n + k) := orIn_up hk hop (by rw [hin]; simp) hp' hu2
    simp only [lam, orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨hk, hop, not_below G u hu'⟩, ne0, ne1, t, ht, p,
      by rw [hp]; exact Finset.card_singleton c, hr⟩
  have hneM : ∀ h ∈ M, h < C.gates.length ∧ (orIn n C (n + h)).Nonempty := by
    intro h hh
    have hl := ((hM h).mp hh).1
    simp only [lam, orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hl
    obtain ⟨⟨hk, hop, _⟩, ⟨u, hu⟩, _, _⟩ := hl
    obtain ⟨p', q', hin, hp', hq', e0, e1⟩ := two_inputs hA hk
    rw [e0] at hu
    exact ⟨hk, u, orIn_up hk hop (by rw [hin]; simp) hp' hu⟩
  have hBM : Bc.card ≤ M.card := by
    have hsub : Bc ⊆ M.image (fun k => orIn n C (n + k)) := by
      intro X hX
      obtain ⟨k, hk, rfl⟩ := hB X hX
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨d, hd, q, hq, hv⟩ := (hLd w).mp hw
    obtain ⟨_, hadj, _⟩ := tf d hd
    have hc : c ∈ side (n := n) C d (1 - q) := by rw [hq]; exact Finset.mem_singleton_self c
    rcases fin2 q with rfl | rfl
    · rw [e10] at hc
      refine ⟨(hadj w hv c hc).symm, ?_⟩
      simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
      exact ⟨d, hd, (w, c), ⟨hv, hc⟩, Sym2.eq_swap⟩
    · rw [e11] at hc
      refine ⟨hadj c hc w hv, ?_⟩
      simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
      exact ⟨d, hd, (c, w), ⟨hc, hv⟩, rfl⟩
  · have hLW : L ⊆ (T.image phi).biUnion (orIn n C) := by
      intro v hv
      obtain ⟨d, hd, q, hq, hvd⟩ := (hLd v).mp hv
      refine Finset.mem_biUnion.mpr ⟨phi d,
        Finset.mem_image.mpr ⟨d, (hT d).mpr ⟨hd, q, hq⟩, rfl⟩, ?_⟩
      rw [← hphi d hd q hq]
      exact hvd
    have hDM : (T.image phi).biUnion (dset n C) ⊆ M := by
      intro k hk
      obtain ⟨w, hw, hkw⟩ := Finset.mem_biUnion.mp hk
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨htop, p, hp⟩ := (hT t).mp ht
      rw [mem_dset, ← hphi t htop p hp] at hkw
      exact inM t htop p hp k hkw.1 hkw.2.1 hkw.2.2.1 hkw.2.2.2.1 hkw.2.2.2.2
    have hcount := count_abs (orIn n C) (dset n C) (count_hyp hA) ((T.image phi).sup id + 1)
      (T.image phi) (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw))
    have a1 := Finset.card_le_card hLW
    have a2 := Finset.card_le_card hDM
    have a3 : (T.image phi).card ≤ T.card := Finset.card_image_le
    omega
  · intro hne
    obtain ⟨X, hX⟩ := hne
    obtain ⟨k, hk, _⟩ := hB X hX
    obtain ⟨_, a, ha, b, hb, _⟩ := (hM k).mp hk
    have hTa : a ∈ T := (hT a).mpr ⟨ha, b, hb⟩
    have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨a, hTa⟩
    omega
  · intro hne hno
    obtain ⟨X, hX⟩ := hne
    obtain ⟨k, hk, _⟩ := hB X hX
    obtain ⟨_, a, ha, b, hb, _⟩ := (hM k).mp hk
    have hTa : a ∈ T := (hT a).mpr ⟨ha, b, hb⟩
    have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨a, hTa⟩
    by_cases hT2 : 2 ≤ T.card
    · omega
    · have hTone : ∀ t ∈ T, t = a := fun t ht =>
        Finset.card_le_one.mp (by omega) t ht a hTa
      have hroot : ∀ h ∈ M, Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + h) := by
        intro h hh
        obtain ⟨_, a', ha', b', hb', hr'⟩ := (hM h).mp hh
        have haa : a' = a := hTone a' ((hT a').mpr ⟨ha', b', hb'⟩)
        subst haa
        rw [hphi a' ha' b' hb', ← hphi a' ha' b hb] at hr'
        exact (orReaches_reach h _ hr').1
      obtain ⟨hs, hsM, hmax⟩ := Finset.exists_max_image M id ⟨k, hk⟩
      have hall : ∀ h ∈ M, Relation.ReflTransGen (OrStep n C) (n + hs) (n + h) := by
        intro h hh
        by_contra hcon
        have hle : h ≤ hs := hmax h hh
        have hn1 : ¬ Relation.ReflTransGen (OrStep n C) (n + h) (n + hs) := by
          intro hr
          have h3 := orStep_le hr
          have he : h = hs := by omega
          rw [he] at hcon
          exact hcon Relation.ReflTransGen.refl
        obtain ⟨g, p, q, hg, hgop, hrg, hpin, hqin, hp, hq, e0, e1, hcase⟩ :=
          lca hA hs h hcon hn1 (opnd C a b) (hroot hs hsM) (hroot h hh)
        have hnp : (orIn n C p).Nonempty ∧ (orIn n C q).Nonempty ∧ hs < g := by
          rcases hcase with ⟨c1, c2⟩ | ⟨c1, c2⟩
          · have b1 := orStep_le c1
            exact ⟨(hneM hs hsM).2.mono (orIn_mono c1), (hneM h hh).2.mono (orIn_mono c2),
              by omega⟩
          · have b1 := orStep_le c2
            exact ⟨(hneM h hh).2.mono (orIn_mono c1), (hneM hs hsM).2.mono (orIn_mono c2),
              by omega⟩
        have hgM : g ∈ M := inM a ha b hb g hg (reach_orReaches hrg g rfl hg) hgop
          (by rw [e0]; exact hnp.1) (by rw [e1]; exact hnp.2.1)
        have hgle : g ≤ hs := hmax g hgM
        omega
      have hMpos : 0 < M.card := Finset.card_pos.mpr ⟨k, hk⟩
      by_cases hin : orIn n C (n + hs) ∈ Bc
      · obtain ⟨X2, hX2, hns⟩ := hno _ hin
        obtain ⟨k2, hk2, rfl⟩ := hB X2 hX2
        exact (hns (orIn_mono (hall k2 hk2))).elim
      · have hsub : Bc ⊆ (M.erase hs).image (fun k => orIn n C (n + k)) := by
          intro Y hY
          obtain ⟨k2, hk2, rfl⟩ := hB Y hY
          refine Finset.mem_image.mpr ⟨k2, Finset.mem_erase.mpr ⟨?_, hk2⟩, rfl⟩
          intro e
          rw [e] at hY
          exact hin hY
        have c1 := (Finset.card_le_card hsub).trans Finset.card_image_le
        rw [Finset.card_erase_of_mem hsM] at c1
        omega

end PEqualNP.Outside.L_meta_1652

theorem PEqualNP.Outside.L_meta_1652 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ∀ (c : Fin n) (T M : Finset ℕ) (L : Finset (Fin n)), (∀ t, t ∈ T ↔ t ∈ PEqualNP.TopForm.tops G C ∧ ∃ p : Fin 2, PEqualNP.TopForm.side (n := n) C t (1 - p) = {c}) → (∀ h, h ∈ M ↔ h ∈ PEqualNP.TopForm.lam G C ∧ ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, PEqualNP.TopForm.side (n := n) C a (1 - b) = {c} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h) → (∀ v, v ∈ L ↔ ∃ d ∈ PEqualNP.TopForm.tops G C, ∃ q : Fin 2, PEqualNP.TopForm.side (n := n) C d (1 - q) = {c} ∧ v ∈ PEqualNP.TopForm.side (n := n) C d q) → ∀ (Bc : Finset (Finset (Fin n))), (∀ X ∈ Bc, ∃ k ∈ M, PEqualNP.TopForm.orIn n C (n + k) = X) → (∀ w ∈ L, G.Adj c w ∧ s(c, w) ∈ PEqualNP.TopForm.starEdges G C) ∧ L.card ≤ T.card + M.card ∧ (Bc.Nonempty → Bc.card + 1 ≤ T.card + M.card) ∧ (Bc.Nonempty → (∀ X' ∈ Bc, ∃ X'' ∈ Bc, ¬ X'' ⊆ X') → Bc.card + 2 ≤ T.card + M.card) := by
  intro n G _ C h4 _ hL _ c T M L hT hM hLd Bc hB
  exact PEqualNP.Outside.L_meta_1652.main n G C h4 hL c T M L hT hM hLd Bc hB
