import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1574

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_prefix (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, step_length, List.length_cons]
    omega

lemma fold_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by rw [step_length]; omega)]
    exact step_prefix w g i hi

lemma fold_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      rw [fold_prefix gs (step w g) (w.length + 0) (by rw [step_length]; omega)]
      have h0 : (step w g).getD (w.length + 0) false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [h0]
      simp only [List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases h : i < w.length
      · have h' : i < w.length + 0 := by omega
        simp only [h', ite_true]
        rw [fold_prefix gs (step w g) i (by rw [step_length]; omega)]
        exact (step_prefix w g i h).symm
      · have h' : ¬ i < w.length + 0 := by omega
        simp only [h', ite_false]
        exact List.getD_eq_default _ _ (by omega)
    | succ j =>
      have h := ih (step w g) j (by simpa using hj)
      rw [step_length] at h
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact h

def val (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (t : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD t false

lemma val_in (gs : List Gate) (n : ℕ) (t : ℕ) (h : t < n) (x : Fin n → Bool) :
    val gs n x t = x ⟨t, h⟩ := by
  unfold val
  rw [fold_prefix _ _ t (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_key (gs : List Gate) (n : ℕ) (j : ℕ) (hj : j < gs.length) (z : Fin n → Bool) :
    val gs n z (n + j) =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < n + j then val gs n z i else false) := by
  have h := fold_gate gs (List.ofFn z) j hj
  rw [List.length_ofFn] at h
  exact h

lemma ite_val (b : Prop) [Decidable b] (u : Bool) :
    (if b then u else false) = true ↔ b ∧ u = true := by
  by_cases h : b <;> simp [h]


def Closed (gs : List Gate) (S : Set ℕ) : Prop :=
  ∀ i : Fin gs.length, 13 + (i : ℕ) ∈ S → (gs.get i).op = GateOp.or →
    ∀ a ∈ (gs.get i).inputs, a ∈ S

def Cone (gs : List Gate) (h u : ℕ) : Prop :=
  ∀ S : Set ℕ, h ∈ S → Closed gs S → u ∈ S

def IsAnd (gs : List Gate) (A : ℕ) : Prop :=
  ∃ i : Fin gs.length, A = 13 + (i : ℕ) ∧ (gs.get i).op = GateOp.and

def Mg (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gs : List Gate)
    (l : Fin 13) (g : Fin gs.length) : Prop :=
  (gs.get g).op = GateOp.or ∧ val gs 13 (fun v : Fin 13 => decide (v ∉ L l)) (13 + (g : ℕ)) = false ∧
    ∃ w1 w2 : ℕ, (gs.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l,
      val gs 13 (T l r) w1 = true ∧ val gs 13 (T l r') w2 = true ∧
      ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gs.length, i < g →
        (gs.get i).op = GateOp.or →
        val gs 13 (fun v : Fin 13 => decide (v ∉ L l)) (13 + (i : ℕ)) = false →
        ∀ a b : ℕ, (gs.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (val gs 13 (T l y) a = true ∨ val gs 13 (T l y) b = true) →
          (val gs 13 (T l y') a = true ∨ val gs 13 (T l y') b = true) → (y ∈ X ↔ y' ∈ X))

lemma or_val (gs : List Gate) (i : Fin gs.length) (hop : (gs.get i).op = GateOp.or)
    (hin : ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ)) (x : Fin 13 → Bool) :
    val gs 13 x (13 + (i : ℕ)) = true ↔ ∃ a ∈ (gs.get i).inputs, val gs 13 x a = true := by
  rw [val_key gs 13 i i.2]
  have e : gs[(i : ℕ)] = gs.get i := rfl
  rw [e, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, hb⟩
    exact ⟨a, ha, ((ite_val _ _).mp hb).2⟩
  · rintro ⟨a, ha, hv⟩
    exact ⟨_, ⟨a, ha, rfl⟩, (ite_val _ _).mpr ⟨hin a ha, hv⟩⟩

lemma and_val (gs : List Gate) (i : Fin gs.length) (hop : (gs.get i).op = GateOp.and)
    (hin : ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ)) (x : Fin 13 → Bool) :
    val gs 13 x (13 + (i : ℕ)) = true ↔ ∀ a ∈ (gs.get i).inputs, val gs 13 x a = true := by
  rw [val_key gs 13 i i.2]
  have e : gs[(i : ℕ)] = gs.get i := rfl
  rw [e, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
  constructor
  · intro h a ha
    exact ((ite_val _ _).mp (h _ ⟨a, ha, rfl⟩)).2
  · rintro h b ⟨a, ha, rfl⟩
    exact (ite_val _ _).mpr ⟨hin a ha, h a ha⟩

lemma descend (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ))
    (x z1 z2 : Fin 13 → Bool) :
    ∀ w, w < 13 + gs.length → val gs 13 x w = true → val gs 13 z1 w = false →
      val gs 13 z2 w = false →
      ∃ u, u ≤ w ∧ Cone gs w u ∧ val gs 13 x u = true ∧ val gs 13 z1 u = false ∧
        val gs 13 z2 u = false ∧ (u < 13 ∨ IsAnd gs u) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx h1 h2
    by_cases hlt : w < 13
    · exact ⟨w, le_rfl, fun S hS _ => hS, hx, h1, h2, Or.inl hlt⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = 13 + j := ⟨w - 13, by omega⟩
      have hj : j < gs.length := by omega
      rcases (hg _ (List.get_mem gs ⟨j, hj⟩)).1 with hop | hop
      · exact ⟨13 + j, le_rfl, fun S hS _ => hS, hx, h1, h2, Or.inr ⟨⟨j, hj⟩, rfl, hop⟩⟩
      · have hi : ∀ a ∈ (gs.get ⟨j, hj⟩).inputs, a < 13 + j := (hin ⟨j, hj⟩).2
        obtain ⟨a, ha, hax⟩ := (or_val gs ⟨j, hj⟩ hop hi x).mp hx
        have f1 : val gs 13 z1 a = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          have := (or_val gs ⟨j, hj⟩ hop hi z1).mpr ⟨a, ha, hc⟩
          exact Bool.noConfusion (this.symm.trans h1)
        have f2 : val gs 13 z2 a = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          have := (or_val gs ⟨j, hj⟩ hop hi z2).mpr ⟨a, ha, hc⟩
          exact Bool.noConfusion (this.symm.trans h2)
        have hal := hi a ha
        obtain ⟨u, hu, hc, r1, r2, r3, r4⟩ := ih a hal (by omega) hax f1 f2
        exact ⟨u, by omega, fun S hS hcl => hc S (hcl ⟨j, hj⟩ hS hop a ha) hcl, r1, r2, r3, r4⟩

lemma cone_up (gs : List Gate)
    (hin : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ))
    (x : Fin 13 → Bool) (h u : ℕ) (hc : Cone gs h u) (hu : val gs 13 x u = true) :
    val gs 13 x h = true := by
  refine hc {w | val gs 13 x w = true → val gs 13 x h = true} (fun e => e) ?_ hu
  intro i hiS hop a ha hav
  exact hiS ((or_val gs i hop (hin i).2 x).mpr ⟨a, ha, hav⟩)

lemma atom (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gs : List Gate)
    (l m c : Fin 13)
    (hT : ∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ))
    (hL : L l ∩ L m = {c}) (h : Fin gs.length) (hop : (gs.get h).op = GateOp.or)
    (z1 : val gs 13 (fun v : Fin 13 => decide (v ∉ L l)) (13 + (h : ℕ)) = false)
    (z2 : val gs 13 (fun v : Fin 13 => decide (v ∉ L m)) (13 + (h : ℕ)) = false)
    (p : Fin 13) (hp : p ∈ L l) (hpc : p ≠ c) (hv : val gs 13 (T l p) (13 + (h : ℕ)) = true) :
    ∃ A, A < 13 + (h : ℕ) ∧ Cone gs (13 + (h : ℕ)) A ∧ IsAnd gs A ∧
      val gs 13 (T l p) A = true ∧ val gs 13 (fun v : Fin 13 => decide (v ∉ L l)) A = false := by
  obtain ⟨u, hu, hc, r1, r2, r3, r4⟩ :=
    descend gs hg hin (T l p) _ _ (13 + (h : ℕ)) (by have := h.2; omega) hv z1 z2
  rcases r4 with hlt | ⟨i, rfl, hi⟩
  · exfalso
    rw [val_in gs 13 u hlt] at r1 r2 r3
    have m1 : (⟨u, hlt⟩ : Fin 13) ∈ L l := by simpa using r2
    have m2 : (⟨u, hlt⟩ : Fin 13) ∈ L m := by simpa using r3
    have m3 : (⟨u, hlt⟩ : Fin 13) ∈ L l ∩ L m := Finset.mem_inter.mpr ⟨m1, m2⟩
    rw [hL, Finset.mem_singleton] at m3
    have m4 := (hT l p hp _ m1).mp r1
    exact hpc (m4.symm.trans m3)
  · refine ⟨13 + (i : ℕ), ?_, hc, ⟨i, rfl, hi⟩, r1, r2⟩
    have ne : i ≠ h := by
      rintro rfl
      rw [hop] at hi
      cases hi
    have ne' : (i : ℕ) ≠ (h : ℕ) := fun e => ne (Fin.ext e)
    omega

lemma noboth (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gs : List Gate)
    (l : Fin 13)
    (hT : ∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ))
    (g : Fin gs.length) (r r' : Fin 13) (hr : r ∈ L l) (hr' : r' ∈ L l)
    (X : Finset (Fin 13)) (hrX : r ∈ X) (hr'X : r' ∉ X)
    (hX : ∀ i : Fin gs.length, i < g →
        (gs.get i).op = GateOp.or →
        val gs 13 (fun v : Fin 13 => decide (v ∉ L l)) (13 + (i : ℕ)) = false →
        ∀ a b : ℕ, (gs.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (val gs 13 (T l y) a = true ∨ val gs 13 (T l y) b = true) →
          (val gs 13 (T l y') a = true ∨ val gs 13 (T l y') b = true) → (y ∈ X ↔ y' ∈ X)) :
    ∀ w, w < 13 + (g : ℕ) → val gs 13 (fun v : Fin 13 => decide (v ∉ L l)) w = false →
      val gs 13 (T l r) w = true → val gs 13 (T l r') w = true → False := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hz hx hx'
    by_cases hlt : w < 13
    · rw [val_in gs 13 w hlt] at hz hx hx'
      have m1 : (⟨w, hlt⟩ : Fin 13) ∈ L l := by simpa using hz
      have e1 := (hT l r hr _ m1).mp hx
      have e2 := (hT l r' hr' _ m1).mp hx'
      exact hr'X (by rw [← e2, e1]; exact hrX)
    · obtain ⟨j, rfl⟩ : ∃ j, w = 13 + j := ⟨w - 13, by omega⟩
      have hj : j < gs.length := by have := g.2; omega
      have hi : ∀ a ∈ (gs.get ⟨j, hj⟩).inputs, a < 13 + j := (hin ⟨j, hj⟩).2
      have h1 := (hin ⟨j, hj⟩).1
      have h2 := (hg _ (List.get_mem gs ⟨j, hj⟩)).2
      rcases (hg _ (List.get_mem gs ⟨j, hj⟩)).1 with hop | hop
      · have hall := (and_val gs ⟨j, hj⟩ hop hi (T l r)).mp hx
        have hall' := (and_val gs ⟨j, hj⟩ hop hi (T l r')).mp hx'
        have : ∃ a ∈ (gs.get ⟨j, hj⟩).inputs,
            val gs 13 (fun v : Fin 13 => decide (v ∉ L l)) a = false := by
          by_contra hc
          push_neg at hc
          have := (and_val gs ⟨j, hj⟩ hop hi (fun v : Fin 13 => decide (v ∉ L l))).mpr
            (fun a ha => by simpa using hc a ha)
          exact Bool.noConfusion (this.symm.trans hz)
        obtain ⟨a, ha, haz⟩ := this
        have hal := hi a ha
        exact ih a hal (by omega) haz (hall a ha) (hall' a ha)
      · have ox := (or_val gs ⟨j, hj⟩ hop hi (T l r)).mp hx
        have ox' := (or_val gs ⟨j, hj⟩ hop hi (T l r')).mp hx'
        have oz : ∀ a ∈ (gs.get ⟨j, hj⟩).inputs,
            val gs 13 (fun v : Fin 13 => decide (v ∉ L l)) a = false := by
          intro a ha
          by_contra hc
          rw [Bool.not_eq_false] at hc
          have := (or_val gs ⟨j, hj⟩ hop hi (fun v : Fin 13 => decide (v ∉ L l))).mpr ⟨a, ha, hc⟩
          exact Bool.noConfusion (this.symm.trans hz)
        rcases hinp : (gs.get ⟨j, hj⟩).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, tl⟩⟩⟩
        · rw [hinp] at h1
          simp at h1
        · rw [hinp] at ox ox' oz hi
          simp only [List.mem_singleton, exists_eq_left] at ox ox'
          have hal := hi a (by simp)
          exact ih a hal (by omega) (oz a (by simp)) ox ox'
        · rw [hinp] at ox ox'
          have q1 : val gs 13 (T l r) a = true ∨ val gs 13 (T l r) b = true := by
            simpa using ox
          have q2 : val gs 13 (T l r') a = true ∨ val gs 13 (T l r') b = true := by
            simpa using ox'
          have lt : (⟨j, hj⟩ : Fin gs.length) < g := by
            rw [Fin.lt_def]
            show j < (g : ℕ)
            omega
          exact hr'X ((hX ⟨j, hj⟩ lt hop hz a b hinp r hr r' hr' q1 q2).mp hrX)
        · rw [hinp] at h2
          simp at h2

lemma line (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gs : List Gate)
    (l m c : Fin 13)
    (hT : ∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ))
    (hL : L l ∩ L m = {c}) (g g' : Fin gs.length) (hlt : g < g')
    (M1 : Mg L T gs l g) (M2 : Mg L T gs l g')
    (zg : val gs 13 (fun v : Fin 13 => decide (v ∉ L m)) (13 + (g : ℕ)) = false)
    (zg' : val gs 13 (fun v : Fin 13 => decide (v ∉ L m)) (13 + (g' : ℕ)) = false) :
    ∃ A1 A2 : ℕ, A1 ≠ A2 ∧ (Cone gs (13 + (g : ℕ)) A1 ∨ Cone gs (13 + (g' : ℕ)) A1) ∧
      (Cone gs (13 + (g : ℕ)) A2 ∨ Cone gs (13 + (g' : ℕ)) A2) ∧ IsAnd gs A1 ∧ IsAnd gs A2 ∧
      (∃ p ∈ L l, p ≠ c ∧ val gs 13 (T l p) A1 = true) ∧
      (∃ p ∈ L l, p ≠ c ∧ val gs 13 (T l p) A2 = true) := by
  obtain ⟨hop, hz, w1, w2, hinp, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, hX⟩ := M1
  obtain ⟨hop', hz', w1', w2', hinp', q, hq, q', hq', hu1, hu2, X', hqX, hq'X, hX'⟩ := M2
  have sees : ∀ x : Fin 13 → Bool, val gs 13 x (13 + (g : ℕ)) = true ↔
      (val gs 13 x w1 = true ∨ val gs 13 x w2 = true) := by
    intro x
    rw [or_val gs g hop (hin g).2 x, hinp]
    simp
  have sees' : ∀ x : Fin 13 → Bool, val gs 13 x (13 + (g' : ℕ)) = true ↔
      (val gs 13 x w1' = true ∨ val gs 13 x w2' = true) := by
    intro x
    rw [or_val gs g' hop' (hin g').2 x, hinp']
    simp
  have sr := (sees (T l r)).mpr (Or.inl hv1)
  have sr' := (sees (T l r')).mpr (Or.inr hv2)
  have hcl : c ∈ L l := by
    have : c ∈ L l ∩ L m := by
      rw [hL]
      exact Finset.mem_singleton_self c
    exact (Finset.mem_inter.mp this).1
  have key : ∀ r0 ∈ L l, r0 ≠ c → val gs 13 (T l r0) (13 + (g : ℕ)) = true →
      val gs 13 (T l c) (13 + (g : ℕ)) = true →
      ∃ A1 A2 : ℕ, A1 ≠ A2 ∧ (Cone gs (13 + (g : ℕ)) A1 ∨ Cone gs (13 + (g' : ℕ)) A1) ∧
      (Cone gs (13 + (g : ℕ)) A2 ∨ Cone gs (13 + (g' : ℕ)) A2) ∧ IsAnd gs A1 ∧ IsAnd gs A2 ∧
      (∃ p ∈ L l, p ≠ c ∧ val gs 13 (T l p) A1 = true) ∧
      (∃ p ∈ L l, p ≠ c ∧ val gs 13 (T l p) A2 = true) := by
    intro r0 h0 h0c s0 sc
    obtain ⟨A, hAlt, hAc, hAand, hAv, _⟩ := atom L T gs l m c hT hg hin hL g hop hz zg r0 h0 h0c s0
    have cls : ∀ y ∈ L l, val gs 13 (T l y) (13 + (g : ℕ)) = true → (y ∈ X' ↔ c ∈ X') :=
      fun y hy sy => hX' g hlt hop hz w1 w2 hinp y hy c hcl ((sees _).mp sy) ((sees _).mp sc)
    have ex : ∃ q0 ∈ L l, val gs 13 (T l q0) (13 + (g' : ℕ)) = true ∧ ¬ (q0 ∈ X' ↔ c ∈ X') := by
      by_cases hcX : c ∈ X'
      · exact ⟨q', hq', (sees' _).mpr (Or.inr hu2), fun h => hq'X (h.mpr hcX)⟩
      · exact ⟨q, hq, (sees' _).mpr (Or.inl hu1), fun h => hcX (h.mp hqX)⟩
    obtain ⟨q0, hq0, sq0, hne⟩ := ex
    have hq0c : q0 ≠ c := by
      rintro rfl
      exact hne Iff.rfl
    obtain ⟨A', _, hA'c, hA'and, hA'v, _⟩ :=
      atom L T gs l m c hT hg hin hL g' hop' hz' zg' q0 hq0 hq0c sq0
    refine ⟨A, A', ?_, Or.inl hAc, Or.inr hA'c, hAand, hA'and, ⟨r0, h0, h0c, hAv⟩,
      ⟨q0, hq0, hq0c, hA'v⟩⟩
    rintro rfl
    exact hne (cls q0 hq0 (cone_up gs hin _ _ _ hAc hA'v))
  by_cases hc1 : r = c
  · have hc2 : r' ≠ c := by
      intro e
      exact hr'X (by rw [e, ← hc1]; exact hrX)
    exact key r' hr' hc2 sr' (hc1 ▸ sr)
  · by_cases hc2 : r' = c
    · exact key r hr hc1 sr (hc2 ▸ sr')
    · obtain ⟨A, hAlt, hAc, hAand, hAv, hAz⟩ :=
        atom L T gs l m c hT hg hin hL g hop hz zg r hr hc1 sr
      obtain ⟨A', _, hA'c, hA'and, hA'v, _⟩ :=
        atom L T gs l m c hT hg hin hL g hop hz zg r' hr' hc2 sr'
      refine ⟨A, A', ?_, Or.inl hAc, Or.inl hA'c, hAand, hA'and, ⟨r, hr, hc1, hAv⟩,
        ⟨r', hr', hc2, hA'v⟩⟩
      rintro rfl
      exact noboth L T gs l hT hg hin g r r' hr hr' X hrX hr'X hX A hAlt hAz hAv hA'v

end PEqualNP.Outside.L_meta_1574

theorem PEqualNP.Outside.L_meta_1574 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate) (l m c : Fin 13) (g g' : Fin gates.length),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ≠ m → L l ∩ L m = {c} → g ≠ g' →
    ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X))) → ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T m r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T m r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X))) →
    ((gates.get g').op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g' : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g').inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g' → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X))) → ((gates.get g').op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g' : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g').inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T m r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T m r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g' → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X))) →
    (∃ A1 A2 : ℕ, A1 ≠ A2 ∧ ((∀ S : Set ℕ, 13 + (g : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A1 ∈ S) ∨ (∀ S : Set ℕ, 13 + (g' : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A1 ∈ S)) ∧
        ((∀ S : Set ℕ, 13 + (g : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A2 ∈ S) ∨ (∀ S : Set ℕ, 13 + (g' : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A2 ∈ S)) ∧ (∃ i : Fin gates.length, A1 = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (∃ i : Fin gates.length, A2 = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        (∃ p ∈ L l, p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, A1⟩ (List.ofFn (T l p)) = true) ∧ (∃ p ∈ L l, p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, A2⟩ (List.ofFn (T l p)) = true)) ∧
    (∃ A1 A2 : ℕ, A1 ≠ A2 ∧ ((∀ S : Set ℕ, 13 + (g : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A1 ∈ S) ∨ (∀ S : Set ℕ, 13 + (g' : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A1 ∈ S)) ∧
        ((∀ S : Set ℕ, 13 + (g : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A2 ∈ S) ∨ (∀ S : Set ℕ, 13 + (g' : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A2 ∈ S)) ∧ (∃ i : Fin gates.length, A1 = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (∃ i : Fin gates.length, A2 = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        (∃ p ∈ L m, p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, A1⟩ (List.ofFn (T m p)) = true) ∧ (∃ p ∈ L m, p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, A2⟩ (List.ofFn (T m p)) = true)) := by
  intro L _ T gates l m c g g' hT hg hin _ hc hgg M1 M2 M3 M4
  have hc' : L m ∩ L l = {c} := by
    rw [Finset.inter_comm]
    exact hc
  rcases lt_or_gt_of_ne hgg with h | h
  · exact ⟨PEqualNP.Outside.L_meta_1574.line L T gates l m c hT hg hin hc g g' h M1 M3 M2.2.1 M4.2.1,
      PEqualNP.Outside.L_meta_1574.line L T gates m l c hT hg hin hc' g g' h M2 M4 M1.2.1 M3.2.1⟩
  · obtain ⟨A1, A2, h1, h2, h3, rest⟩ :=
      PEqualNP.Outside.L_meta_1574.line L T gates l m c hT hg hin hc g' g h M3 M1 M4.2.1 M2.2.1
    obtain ⟨B1, B2, k1, k2, k3, rest'⟩ :=
      PEqualNP.Outside.L_meta_1574.line L T gates m l c hT hg hin hc' g' g h M4 M2 M3.2.1 M1.2.1
    exact ⟨⟨A1, A2, h1, h2.symm, h3.symm, rest⟩, ⟨B1, B2, k1, k2.symm, k3.symm, rest'⟩⟩
