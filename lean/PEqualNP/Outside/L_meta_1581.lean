import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1581

open scoped Classical
open PEqualNP.CircuitLowerBounds

def L0 (t : Fin 13) : Finset (Fin 13) :=
  {t, t + 1, t + 3, t + 9}

def L' (t : Fin 13) : Finset (Fin 13) :=
  if t = 0 then {0, 1} else L0 t

def A0 : Finset (Fin 13) :=
  Finset.univ.filter (fun t : Fin 13 => t ≠ 0 ∧ (0 : Fin 13) ∈ L0 t)

def A1 : Finset (Fin 13) :=
  Finset.univ.filter (fun t : Fin 13 => t ≠ 0 ∧ (1 : Fin 13) ∈ L0 t)

def testIn (t p : Fin 13) : Fin 13 → Bool :=
  if t = 0 then fun v => decide (v = p)
  else if (0 : Fin 13) ∈ L0 t then
    if p = 0 then fun v => decide (v = 0) else fun v => decide (v = p ∨ v = 1)
  else
    if p = 1 then fun v => decide (v = 1) else fun v => decide (v = p ∨ v = 0)

def offL (t : Fin 13) : Fin 13 → Bool :=
  fun v => decide (v ∉ L0 t)

def F01 (x : Fin 13 → Bool) : Prop :=
  x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L0 0 → x v = true

lemma L0_card : ∀ t : Fin 13, (L0 t).card = 4 := by decide
lemma L'_sub : ∀ t : Fin 13, L' t ⊆ L0 t := by decide
lemma L'_nonempty : ∀ t : Fin 13, (L' t).Nonempty := by decide
lemma L'_sum : (∑ t : Fin 13, ((L' t).card - 1)) = 37 := by decide
lemma L0_thin : ∀ i j : Fin 13, i ≠ j → (L0 i ∩ L0 j).card ≤ 1 := by decide
lemma L0_zero_one : ∀ t : Fin 13, t ≠ 0 → (0 : Fin 13) ∉ L0 t ∨ (1 : Fin 13) ∉ L0 t := by decide
lemma A0_no_one : ∀ i ∈ A0, (1 : Fin 13) ∉ L0 i := by decide
lemma A1_no_zero : ∀ j ∈ A1, (0 : Fin 13) ∉ L0 j := by decide
lemma A0_inter_A1 : ∀ i ∈ A0, ∀ j ∈ A1, ∃ m : Fin 13, L0 i ∩ L0 j = {m} ∧ m ≠ 0 ∧ m ≠ 1 := by decide
lemma A0_card_sub : ∀ i ∈ A0, ((L0 i).erase 0).card = 3 := by decide
lemma A1_card_sub : ∀ j ∈ A1, ((L0 j).erase 1).card = 3 := by decide
lemma A0_inter_zero : ∀ i ∈ A0, ∀ i' ∈ A0, i ≠ i' → L0 i ∩ L0 i' = {0} := by decide
lemma A1_inter_one : ∀ j ∈ A1, ∀ j' ∈ A1, j ≠ j' → L0 j ∩ L0 j' = {1} := by decide
lemma A0_inter_L0_zero : ∀ i ∈ A0, L0 i ∩ L0 0 = {0} := by decide
lemma A1_inter_L0_zero : ∀ j ∈ A1, L0 j ∩ L0 0 = {1} := by decide
lemma testIn_diag : ∀ t : Fin 13, ∀ p ∈ L' t, ∀ v ∈ L0 t, testIn t p v = true ↔ v = p := by decide
lemma testIn_F01 : ∀ t : Fin 13, ∀ p ∈ L' t,
    testIn t p 0 = true ∨ testIn t p 1 = true := by decide

lemma offL_F01 (t : Fin 13) : F01 (offL t) := by
  by_cases ht : t = 0
  · subst ht
    exact Or.inr (Or.inr fun v hv => decide_eq_true hv)
  · rcases L0_zero_one t ht with h0 | h1
    · exact Or.inl (decide_eq_true h0)
    · exact Or.inr (Or.inl (decide_eq_true h1))

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value (gates : List Gate) (x : Fin 13 → Bool) (w : ℕ) : Bool :=
  (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD w false

lemma eval_eq_value (gates : List Gate) (w : ℕ) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = value gates x w :=
  rfl

lemma input_value (gates : List Gate) (x : Fin 13 → Bool) (p : Fin 13) :
    value gates x p = x p := by
  change (run gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  exact List.getElem_ofFn (f := x) (i := p.val) hp

lemma missing_value (gates : List Gate) (x : Fin 13 → Bool) (w : ℕ)
    (hw : 13 + gates.length ≤ w) : value gates x w = false := by
  change (run gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simp [run_length]; omega)

lemma gate_value (gates : List Gate) (x : Fin 13 → Bool) (i : Fin gates.length) :
    value gates x (13 + i.val) =
      (gates.get i).op.eval
        ((gates.get i).inputs.map fun r => if r < 13 + i.val then value gates x r else false) := by
  let g := gates.get i
  let earlier := run (gates.take i.val) (List.ofFn x)
  have plen : earlier.length = 13 + i.val := by
    simp [earlier, run_length]
  have split : run gates (List.ofFn x) = run (g :: gates.drop (i.val + 1)) earlier := by
    rw [run_split gates (List.ofFn x) i.val, List.drop_eq_getElem_cons i.isLt]
    rfl
  have read (r : ℕ) : earlier.getD r false = if r < 13 + i.val then value gates x r else false := by
    by_cases hr : r < 13 + i.val
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run gates (List.ofFn x)).getD (13 + i.val) false =
    g.op.eval (g.inputs.map fun r => if r < 13 + i.val then value gates x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma value_mono (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin 13 → Bool) (hxy : ∀ v : Fin 13, x v = true → y v = true) (w : ℕ) :
    value gates x w = true → value gates y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw13 : w < 13
    · let p : Fin 13 := ⟨w, hw13⟩
      have hx := input_value gates x p
      have hy := input_value gates y p
      change value gates x w = x p at hx
      change value gates y w = y p at hy
      rw [hx, hy]
      exact hxy p
    by_cases hwlen : w < 13 + gates.length
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hweq : 13 + i.val = w := by simp [i]; omega
      rw [← hweq, gate_value gates x i, gate_value gates y i]
      have step (r : ℕ) :
          (if r < 13 + i.val then value gates x r else false) = true →
          (if r < 13 + i.val then value gates y r else false) = true := by
        by_cases hr : r < 13 + i.val
        · simpa [hr] using ih r (by omega)
        · simp [hr]
      rcases (hgates (gates.get i) (List.get_mem gates i)).1 with hand | hor
      · simp only [hand, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        exact fun h r hr => step r (h r hr)
      · simp only [hor, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        exact fun ⟨r, hr, hvr⟩ => ⟨r, hr, step r hvr⟩
    · simp [missing_value gates x w (by omega)]

section LineMerges

variable (gates : List Gate)
variable (t : Fin 13)

def safe (w : ℕ) : Prop := value gates (offL t) w = false

def stepClosed (i : Fin gates.length) (X : Finset (Fin 13)) : Prop :=
  (gates.get i).op = GateOp.or → safe gates t (13 + i.val) →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → a < 13 + i.val → b < 13 + i.val →
      ∀ y ∈ L' t, ∀ y' ∈ L' t,
        (value gates (testIn t y) a = true ∨ value gates (testIn t y) b = true) →
        (value gates (testIn t y') a = true ∨ value gates (testIn t y') b = true) →
        (y ∈ X ↔ y' ∈ X)

def closedUpTo (k : ℕ) (X : Finset (Fin 13)) : Prop :=
  ∀ i : Fin gates.length, i.val < k → stepClosed gates t i X

def equiv (k : ℕ) (x y : Fin 13) : Prop :=
  ∀ X : Finset (Fin 13), closedUpTo gates t k X → (x ∈ X ↔ y ∈ X)

lemma equiv_refl (k : ℕ) (x : Fin 13) : equiv gates t k x x := fun _ _ => Iff.rfl

lemma equiv_symm (k : ℕ) {x y : Fin 13} (h : equiv gates t k x y) : equiv gates t k y x :=
  fun X hX => (h X hX).symm

lemma equiv_trans (k : ℕ) {x y z : Fin 13}
    (h1 : equiv gates t k x y) (h2 : equiv gates t k y z) : equiv gates t k x z :=
  fun X hX => (h1 X hX).trans (h2 X hX)

lemma equiv_mono {k1 k2 : ℕ} (hk : k1 ≤ k2) {x y : Fin 13}
    (h : equiv gates t k1 x y) : equiv gates t k2 x y :=
  fun X hX => h X (fun i hi => hX i (Nat.lt_of_lt_of_le hi hk))

noncomputable def cls (k : ℕ) (x : Fin 13) : Finset (Fin 13) := by
  classical
  exact (L' t).filter (fun y => equiv gates t k x y)

lemma mem_cls (k : ℕ) (x y : Fin 13) :
    y ∈ cls gates t k x ↔ y ∈ L' t ∧ equiv gates t k x y := by
  classical
  simp [cls]

lemma self_mem_cls (k : ℕ) {x : Fin 13} (hx : x ∈ L' t) : x ∈ cls gates t k x :=
  (mem_cls gates t k x x).mpr ⟨hx, equiv_refl gates t k x⟩

lemma cls_eq_iff (k : ℕ) {x y : Fin 13} (_hx : x ∈ L' t) (hy : y ∈ L' t) :
    cls gates t k x = cls gates t k y ↔ equiv gates t k x y := by
  constructor
  · intro heq
    have hmem : y ∈ cls gates t k x := heq ▸ self_mem_cls gates t k hy
    exact ((mem_cls gates t k x y).mp hmem).2
  · intro heq
    ext z
    simp only [mem_cls]
    exact ⟨fun ⟨hz, hxz⟩ => ⟨hz, equiv_trans gates t k (equiv_symm gates t k heq) hxz⟩,
      fun ⟨hz, hyz⟩ => ⟨hz, equiv_trans gates t k heq hyz⟩⟩

lemma cls_closed (k : ℕ) (x : Fin 13) : closedUpTo gates t k (cls gates t k x) := by
  intro i hi hor hsafe a b hin ha hb y hy y' hy' hya hy'a
  simp only [mem_cls, hy, hy', true_and]
  have hyy' : equiv gates t k y y' := fun X hX =>
    hX i hi hor hsafe a b hin ha hb y hy y' hy' hya hy'a
  exact ⟨fun hxy => equiv_trans gates t k hxy hyy',
    fun hxy' => equiv_trans gates t k hxy' (equiv_symm gates t k hyy')⟩

lemma not_equiv_iff_sep (k : ℕ) {r r' : Fin 13} (hr : r ∈ L' t) :
    ¬ equiv gates t k r r' ↔
      ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ closedUpTo gates t k X := by
  constructor
  · intro hne
    refine ⟨cls gates t k r, self_mem_cls gates t k hr, ?_, cls_closed gates t k r⟩
    intro hmem
    exact hne ((mem_cls gates t k r r').mp hmem).2
  · rintro ⟨X, hrX, hr'X, hX⟩ heq
    exact hr'X ((heq X hX).mp hrX)

noncomputable def parts (k : ℕ) : Finset (Finset (Fin 13)) := by
  classical
  exact (L' t).image (cls gates t k)

lemma safe_wire_equiv
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (w : ℕ) (hw : w < 13 + k) (hwlen : w < 13 + gates.length)
    (hsafe : safe gates t w)
    (r r' : Fin 13) (hr : r ∈ L' t) (hr' : r' ∈ L' t)
    (hvr : value gates (testIn t r) w = true) (hvr' : value gates (testIn t r') w = true) :
    equiv gates t k r r' := by
  induction w using Nat.strong_induction_on generalizing k with
  | ind w ih =>
    by_cases hw13 : w < 13
    · let p : Fin 13 := ⟨w, hw13⟩
      have hpL : p ∈ L0 t := by
        by_contra hpnotL
        have hv := input_value gates (offL t) p
        change value gates (offL t) w = decide (p ∉ L0 t) at hv
        rw [safe] at hsafe
        rw [hsafe, decide_eq_true hpnotL] at hv
        exact Bool.false_ne_true hv
      have hpr : p = r := by
        have hv := input_value gates (testIn t r) p
        change value gates (testIn t r) w = testIn t r p at hv
        rw [hvr] at hv
        exact (testIn_diag t r hr p hpL).mp hv.symm
      have hpr' : p = r' := by
        have hv := input_value gates (testIn t r') p
        change value gates (testIn t r') w = testIn t r' p at hv
        rw [hvr'] at hv
        exact (testIn_diag t r' hr' p hpL).mp hv.symm
      rw [← hpr, ← hpr']
      exact equiv_refl gates t k p
    · have hi_lt : w - 13 < gates.length := by omega
      let i : Fin gates.length := ⟨w - 13, hi_lt⟩
      have hweq : 13 + i.val = w := by simp [i]; omega
      have hik : i.val < k := by omega
      have h2len := (hgates (gates.get i) (List.get_mem gates i)).2
      have hop := (hgates (gates.get i) (List.get_mem gates i)).1
      cases hin : (gates.get i).inputs with
      | nil =>
        rcases hop with hand | hor
        · unfold safe at hsafe
          rw [← hweq, gate_value gates (offL t) i, hin, hand] at hsafe
          simp [GateOp.eval] at hsafe
        · rw [← hweq, gate_value gates (testIn t r) i, hin, hor] at hvr
          simp [GateOp.eval] at hvr
      | cons a rest =>
        cases rest with
        | nil =>
          by_cases ha : a < 13 + i.val
          · have hev (x : Fin 13 → Bool) : value gates x w = value gates x a := by
              rcases hop with h | h
              · rw [← hweq, gate_value gates x i, hin, h]; simp [GateOp.eval, ha]
              · rw [← hweq, gate_value gates x i, hin, h]; simp [GateOp.eval, ha]
            exact ih a (by omega) k (by omega) (by omega)
              (by unfold safe at hsafe ⊢; rwa [← hev]) (by rwa [← hev]) (by rwa [← hev])
          · rcases hop with h | h
            · rw [← hweq, gate_value gates (testIn t r) i, hin, h] at hvr
              simp [GateOp.eval, ha] at hvr
            · rw [← hweq, gate_value gates (testIn t r) i, hin, h] at hvr
              simp [GateOp.eval, ha] at hvr
        | cons b rest2 =>
          cases rest2 with
          | cons c rest3 => rw [hin] at h2len; simp at h2len
          | nil =>
            rcases hop with hand | hor
            · by_cases ha : a < 13 + i.val
              · by_cases hb : b < 13 + i.val
                · have hev (x : Fin 13 → Bool) :
                      value gates x w = (value gates x a && value gates x b) := by
                    rw [← hweq, gate_value gates x i, hin, hand]
                    simp [GateOp.eval, ha, hb]
                  have hsafe_ab : safe gates t a ∨ safe gates t b := by
                    unfold safe at hsafe ⊢
                    rw [hev] at hsafe
                    exact Bool.and_eq_false_iff.mp hsafe
                  have hvr_ab : value gates (testIn t r) a = true ∧ value gates (testIn t r) b = true := by
                    rw [hev] at hvr; simpa [Bool.and_eq_true] using hvr
                  have hvr'_ab : value gates (testIn t r') a = true ∧ value gates (testIn t r') b = true := by
                    rw [hev] at hvr'; simpa [Bool.and_eq_true] using hvr'
                  rcases hsafe_ab with hsa | hsb
                  · exact ih a (by omega) k (by omega) (by omega) hsa hvr_ab.1 hvr'_ab.1
                  · exact ih b (by omega) k (by omega) (by omega) hsb hvr_ab.2 hvr'_ab.2
                · rw [← hweq, gate_value gates (testIn t r) i, hin, hand] at hvr
                  simp [GateOp.eval, hb] at hvr
              · rw [← hweq, gate_value gates (testIn t r) i, hin, hand] at hvr
                simp [GateOp.eval, ha] at hvr
            · by_cases ha : a < 13 + i.val
              · by_cases hb : b < 13 + i.val
                · have hev (x : Fin 13 → Bool) :
                      value gates x w = (value gates x a || value gates x b) := by
                    rw [← hweq, gate_value gates x i, hin, hor]
                    simp [GateOp.eval, ha, hb]
                  have hvr_or : value gates (testIn t r) a = true ∨ value gates (testIn t r) b = true := by
                    rw [hev] at hvr; simpa [Bool.or_eq_true] using hvr
                  have hvr'_or : value gates (testIn t r') a = true ∨ value gates (testIn t r') b = true := by
                    rw [hev] at hvr'; simpa [Bool.or_eq_true] using hvr'
                  intro X hX
                  exact hX i hik hor (hweq.symm ▸ hsafe) a b hin ha hb r hr r' hr' hvr_or hvr'_or
                · have hev (x : Fin 13 → Bool) : value gates x w = value gates x a := by
                    rw [← hweq, gate_value gates x i, hin, hor]
                    simp [GateOp.eval, ha, hb]
                  exact ih a (by omega) k (by omega) (by omega)
                    (by unfold safe at hsafe ⊢; rwa [← hev]) (by rwa [← hev]) (by rwa [← hev])
              · by_cases hb : b < 13 + i.val
                · have hev (x : Fin 13 → Bool) : value gates x w = value gates x b := by
                    rw [← hweq, gate_value gates x i, hin, hor]
                    simp [GateOp.eval, ha, hb]
                  exact ih b (by omega) k (by omega) (by omega)
                    (by unfold safe at hsafe ⊢; rwa [← hev]) (by rwa [← hev]) (by rwa [← hev])
                · rw [← hweq, gate_value gates (testIn t r) i, hin, hor] at hvr
                  simp [GateOp.eval, ha, hb] at hvr

def isMerge (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ safe gates t (13 + g.val) ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ w1 < 13 + g.val ∧ w2 < 13 + g.val ∧
      ∃ r ∈ L' t, ∃ r' ∈ L' t,
        value gates (testIn t r) w1 = true ∧ value gates (testIn t r') w2 = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ closedUpTo gates t g.val X

lemma parts_zero_card : (parts gates t 0).card = (L' t).card := by
  classical
  have hcls0 : ∀ x ∈ L' t, cls gates t 0 x = {x} := by
    intro x hx
    ext y
    simp only [mem_cls, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hxy⟩
      have hX : closedUpTo gates t 0 ({x} : Finset (Fin 13)) := fun i hi => by omega
      exact Finset.mem_singleton.mp ((hxy {x} hX).mp (Finset.mem_singleton_self x))
    · rintro rfl
      exact ⟨hx, equiv_refl gates t 0 _⟩
  have heq : parts gates t 0 = (L' t).image (fun x => ({x} : Finset (Fin 13))) := by
    unfold parts
    exact Finset.image_congr hcls0
  rw [heq, Finset.card_image_of_injective _ Finset.singleton_injective]

lemma parts_step
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (g : Fin gates.length) :
    (parts gates t (g.val + 1)).card + (if isMerge gates t g then 1 else 0) =
      (parts gates t g.val).card := by
  classical
  by_cases hm : isMerge gates t g
  · simp only [hm, ↓reduceIte]
    obtain ⟨hor, hsafe, w1, w2, hin, hw1, hw2, r0, hr0L, r0', hr0'L, hvr0, hvr0',
      X0, hr0X0, hr0'X0, hX0⟩ := hm
    have hev_or (x : Fin 13 → Bool) :
        value gates x (13 + g.val) = (value gates x w1 || value gates x w2) := by
      rw [gate_value gates x g, hin, hor]; simp [GateOp.eval, hw1, hw2]
    have hsafe1 : safe gates t w1 := by
      unfold safe at hsafe ⊢; rw [hev_or] at hsafe
      exact (Bool.or_eq_false_iff.mp hsafe).1
    have hsafe2 : safe gates t w2 := by
      unfold safe at hsafe ⊢; rw [hev_or] at hsafe
      exact (Bool.or_eq_false_iff.mp hsafe).2
    have hne_eq : ¬ equiv gates t g.val r0 r0' :=
      (not_equiv_iff_sep gates t g.val hr0L).mpr ⟨X0, hr0X0, hr0'X0, hX0⟩
    let C1 := cls gates t g.val r0
    let C2 := cls gates t g.val r0'
    have hC1_ne_C2 : C1 ≠ C2 := fun h => hne_eq ((cls_eq_iff gates t g.val hr0L hr0'L).mp h)
    have hsw1 : ∀ y ∈ L' t, value gates (testIn t y) w1 = true → y ∈ C1 := fun y hy hvy =>
      (mem_cls gates t g.val r0 y).mpr ⟨hy,
        safe_wire_equiv gates t hgates g.val w1 hw1 (by omega) hsafe1 r0 y hr0L hy hvr0 hvy⟩
    have hsw2 : ∀ y ∈ L' t, value gates (testIn t y) w2 = true → y ∈ C2 := fun y hy hvy =>
      (mem_cls gates t g.val r0' y).mpr ⟨hy,
        safe_wire_equiv gates t hgates g.val w2 hw2 (by omega) hsafe2 r0' y hr0'L hy hvr0' hvy⟩
    have hclosed_union : closedUpTo gates t (g.val + 1) (C1 ∪ C2) := by
      intro i hi
      by_cases hil : i.val < g.val
      · intro hori hsafei a b hini ha hb y hy y' hy' hya hy'a
        have h1 := cls_closed gates t g.val r0 i hil hori hsafei a b hini ha hb y hy y' hy' hya hy'a
        have h2 := cls_closed gates t g.val r0' i hil hori hsafei a b hini ha hb y hy y' hy' hya hy'a
        simp only [C1, C2, Finset.mem_union]; tauto
      · have hig : i = g := Fin.ext (by omega)
        subst i
        intro _ _ a b hini _ _ y hy y' hy' hya hy'a
        rw [hin] at hini
        have ha : a = w1 := by simpa using (congrArg List.head? hini).symm
        have hb : b = w2 := by simpa using (congrArg (fun l => l.tail.head?) hini).symm
        subst a; subst b
        have hyU : y ∈ C1 ∪ C2 := by
          rcases hya with h1 | h2
          · exact Finset.mem_union_left _ (hsw1 y hy h1)
          · exact Finset.mem_union_right _ (hsw2 y hy h2)
        have hy'U : y' ∈ C1 ∪ C2 := by
          rcases hy'a with h1 | h2
          · exact Finset.mem_union_left _ (hsw1 y' hy' h1)
          · exact Finset.mem_union_right _ (hsw2 y' hy' h2)
        exact ⟨fun _ => hy'U, fun _ => hyU⟩
    have hcls_in : ∀ x ∈ C1 ∪ C2, cls gates t (g.val + 1) x = C1 ∪ C2 := by
      intro x hx
      ext z
      simp only [mem_cls]
      constructor
      · rintro ⟨_, hxz⟩
        exact (hxz (C1 ∪ C2) hclosed_union).mp hx
      · intro hz
        have hzL : z ∈ L' t := by
          rcases Finset.mem_union.mp hz with h1 | h2
          · exact ((mem_cls gates t g.val r0 z).mp h1).1
          · exact ((mem_cls gates t g.val r0' z).mp h2).1
        refine ⟨hzL, fun X hX => ?_⟩
        have hXk : closedUpTo gates t g.val X := fun i hi => hX i (by omega)
        have hr0_r0' : r0 ∈ X ↔ r0' ∈ X :=
          hX g (by omega) hor hsafe w1 w2 hin hw1 hw2 r0 hr0L r0' hr0'L (Or.inl hvr0) (Or.inr hvr0')
        have hmem_iff (u : Fin 13) (hu : u ∈ C1 ∪ C2) : u ∈ X ↔ r0 ∈ X := by
          rcases Finset.mem_union.mp hu with h1 | h2
          · exact (((mem_cls gates t g.val r0 u).mp h1).2 X hXk).symm
          · exact ((((mem_cls gates t g.val r0' u).mp h2).2 X hXk).symm).trans hr0_r0'.symm
        exact (hmem_iff x hx).trans (hmem_iff z hz).symm
    have hcls_out : ∀ x ∈ L' t, x ∉ C1 ∪ C2 →
        cls gates t (g.val + 1) x = cls gates t g.val x := by
      intro x hxL hxnot
      have hclosed_x : closedUpTo gates t (g.val + 1) (cls gates t g.val x) := by
        intro i hi
        by_cases hil : i.val < g.val
        · exact cls_closed gates t g.val x i hil
        · have hig : i = g := Fin.ext (by omega)
          subst i
          intro _ _ a b hini _ _ y hy y' hy' hya hy'a
          rw [hin] at hini
          have ha : a = w1 := by simpa using (congrArg List.head? hini).symm
          have hb : b = w2 := by simpa using (congrArg (fun l => l.tail.head?) hini).symm
          subst a; subst b
          have hnot_in (u : Fin 13) (huL : u ∈ L' t)
              (hu : value gates (testIn t u) w1 = true ∨ value gates (testIn t u) w2 = true) :
              u ∉ cls gates t g.val x := by
            intro hmem
            have hxu := ((mem_cls gates t g.val x u).mp hmem).2
            rcases hu with h1 | h2
            · have hr0u := ((mem_cls gates t g.val r0 u).mp (hsw1 u huL h1)).2
              have hxC1 : x ∈ C1 := (mem_cls gates t g.val r0 x).mpr
                ⟨hxL, equiv_trans gates t g.val hr0u (equiv_symm gates t g.val hxu)⟩
              exact hxnot (Finset.mem_union_left _ hxC1)
            · have hr0'u := ((mem_cls gates t g.val r0' u).mp (hsw2 u huL h2)).2
              have hxC2 : x ∈ C2 := (mem_cls gates t g.val r0' x).mpr
                ⟨hxL, equiv_trans gates t g.val hr0'u (equiv_symm gates t g.val hxu)⟩
              exact hxnot (Finset.mem_union_right _ hxC2)
          exact ⟨fun h => False.elim (hnot_in y hy hya h),
            fun h => False.elim (hnot_in y' hy' hy'a h)⟩
      ext z
      simp only [mem_cls]
      constructor
      · rintro ⟨hzL, hxz⟩
        have hzmem := (hxz (cls gates t g.val x) hclosed_x).mp (self_mem_cls gates t g.val hxL)
        exact ⟨hzL, ((mem_cls gates t g.val x z).mp hzmem).2⟩
      · rintro ⟨hzL, hxz⟩
        exact ⟨hzL, equiv_mono gates t (Nat.le_succ _) hxz⟩
    have hparts_eq : parts gates t (g.val + 1) =
        insert (C1 ∪ C2) (((parts gates t g.val).erase C1).erase C2) := by
      ext S
      simp only [parts, Finset.mem_insert, Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨x, hxL, rfl⟩
        by_cases hxU : x ∈ C1 ∪ C2
        · exact Or.inl (hcls_in x hxU)
        · refine Or.inr ⟨?_, ?_, x, hxL, (hcls_out x hxL hxU).symm⟩
          · intro hEq
            have hxC2 : x ∈ C2 := by
              have h1 := self_mem_cls gates t g.val hxL
              rw [← hcls_out x hxL hxU, hEq] at h1; exact h1
            exact hxU (Finset.mem_union_right _ hxC2)
          · intro hEq
            have hxC1 : x ∈ C1 := by
              have h1 := self_mem_cls gates t g.val hxL
              rw [← hcls_out x hxL hxU, hEq] at h1; exact h1
            exact hxU (Finset.mem_union_left _ hxC1)
      · rintro (rfl | ⟨hne2, hne1, x, hxL, rfl⟩)
        · exact ⟨r0, hr0L, hcls_in r0 (Finset.mem_union_left _ (self_mem_cls gates t g.val hr0L))⟩
        · have hxnot : x ∉ C1 ∪ C2 := by
            intro hxU
            rcases Finset.mem_union.mp hxU with hx1 | hx2
            · exact hne1 ((cls_eq_iff gates t g.val hxL hr0L).mpr
                (equiv_symm gates t g.val ((mem_cls gates t g.val r0 x).mp hx1).2))
            · exact hne2 ((cls_eq_iff gates t g.val hxL hr0'L).mpr
                (equiv_symm gates t g.val ((mem_cls gates t g.val r0' x).mp hx2).2))
          exact ⟨x, hxL, hcls_out x hxL hxnot⟩
    have hC1_mem : C1 ∈ parts gates t g.val := Finset.mem_image.mpr ⟨r0, hr0L, rfl⟩
    have hC2_mem : C2 ∈ (parts gates t g.val).erase C1 :=
      Finset.mem_erase.mpr ⟨hC1_ne_C2.symm, Finset.mem_image.mpr ⟨r0', hr0'L, rfl⟩⟩
    have hU_notMem : C1 ∪ C2 ∉ ((parts gates t g.val).erase C1).erase C2 := by
      intro hmem
      have hmem1 := (Finset.mem_erase.mp hmem).2
      have hne1 := (Finset.mem_erase.mp hmem1).1
      obtain ⟨x, hxL, hxEq⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hmem1).2
      have hr0in : r0 ∈ cls gates t g.val x := by
        rw [hxEq]; exact Finset.mem_union_left _ (self_mem_cls gates t g.val hr0L)
      have hxC1 : cls gates t g.val x = C1 :=
        (cls_eq_iff gates t g.val hxL hr0L).mpr ((mem_cls gates t g.val x r0).mp hr0in).2
      exact hne1 (hxEq.symm.trans hxC1)
    rw [hparts_eq, Finset.card_insert_of_notMem hU_notMem,
      Finset.card_erase_of_mem hC2_mem, Finset.card_erase_of_mem hC1_mem]
    have hcard_ge2 : 2 ≤ (parts gates t g.val).card := by
      have hsub : ({C1, C2} : Finset (Finset (Fin 13))) ⊆ parts gates t g.val := by
        intro S hS
        rcases Finset.mem_insert.mp hS with rfl | hS2
        · exact hC1_mem
        · rw [Finset.mem_singleton.mp hS2]; exact Finset.mem_image.mpr ⟨r0', hr0'L, rfl⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hC1_ne_C2] at this
      exact this
    omega
  · simp only [hm, ↓reduceIte, add_zero]
    have hclosed_same : ∀ X : Finset (Fin 13),
        closedUpTo gates t g.val X → closedUpTo gates t (g.val + 1) X := by
      intro X hX i hi
      by_cases hil : i.val < g.val
      · exact hX i hil
      · have hig : i = g := Fin.ext (by omega)
        subst i
        intro hor hsafe a b hin ha hb y hy y' hy' hya hy'a
        have hev_or (x : Fin 13 → Bool) :
            value gates x (13 + g.val) = (value gates x a || value gates x b) := by
          rw [gate_value gates x g, hin, hor]; simp [GateOp.eval, ha, hb]
        have hsafe_a : safe gates t a := by
          unfold safe at hsafe ⊢; rw [hev_or] at hsafe
          exact (Bool.or_eq_false_iff.mp hsafe).1
        have hsafe_b : safe gates t b := by
          unfold safe at hsafe ⊢; rw [hev_or] at hsafe
          exact (Bool.or_eq_false_iff.mp hsafe).2
        have heq_ab : ∀ r ∈ L' t, ∀ r' ∈ L' t,
            value gates (testIn t r) a = true → value gates (testIn t r') b = true →
            equiv gates t g.val r r' := by
          intro r hr r' hr' hvr hvr'
          by_contra hne
          obtain ⟨X1, hrX1, hr'X1, hX1⟩ := (not_equiv_iff_sep gates t g.val hr).mp hne
          exact hm ⟨hor, hsafe, a, b, hin, ha, hb, r, hr, r', hr', hvr, hvr', X1, hrX1, hr'X1, hX1⟩
        have heq_yy' : equiv gates t g.val y y' := by
          rcases hya with hya1 | hya2 <;> rcases hy'a with hy'a1 | hy'a2
          · exact safe_wire_equiv gates t hgates g.val a ha (by omega) hsafe_a y y' hy hy' hya1 hy'a1
          · exact heq_ab y hy y' hy' hya1 hy'a2
          · exact equiv_symm gates t g.val (heq_ab y' hy' y hy hy'a1 hya2)
          · exact safe_wire_equiv gates t hgates g.val b hb (by omega) hsafe_b y y' hy hy' hya2 hy'a2
        exact heq_yy' X hX
    have heq_equiv : ∀ x y : Fin 13,
        equiv gates t (g.val + 1) x y ↔ equiv gates t g.val x y := fun x y =>
      ⟨fun h X hX => h X (hclosed_same X hX), fun h => equiv_mono gates t (Nat.le_succ _) h⟩
    have hparts_same : parts gates t (g.val + 1) = parts gates t g.val := by
      unfold parts
      refine Finset.image_congr fun x _ => ?_
      ext z; simp only [mem_cls, heq_equiv]
    rw [hparts_same]

lemma line_merge_count
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (o : ℕ) (ho_off : value gates (offL t) o = false)
    (ho_on : ∀ p ∈ L' t, value gates (testIn t p) o = true) :
    (Finset.univ.filter (fun g : Fin gates.length => isMerge gates t g)).card = (L' t).card - 1 := by
  classical
  have htel : ∀ k : ℕ, k ≤ gates.length →
      (parts gates t k).card +
        (Finset.univ.filter (fun g : Fin gates.length => g.val < k ∧ isMerge gates t g)).card =
      (L' t).card := by
    intro k hk
    induction k with
    | zero =>
      simp only [Nat.not_lt_zero, false_and, Finset.filter_false, Finset.card_empty, add_zero]
      exact parts_zero_card gates t
    | succ k ih =>
      have hklt : k < gates.length := by omega
      let gk : Fin gates.length := ⟨k, hklt⟩
      have hstep := parts_step gates t hgates gk
      have hih := ih (by omega)
      have hfilt :
          (Finset.univ.filter (fun g : Fin gates.length => g.val < k + 1 ∧ isMerge gates t g)).card =
          (Finset.univ.filter (fun g : Fin gates.length => g.val < k ∧ isMerge gates t g)).card +
            (if isMerge gates t gk then 1 else 0) := by
        by_cases hmg : isMerge gates t gk
        · simp only [hmg, ↓reduceIte]
          have hset : Finset.univ.filter (fun g : Fin gates.length => g.val < k + 1 ∧ isMerge gates t g) =
              insert gk (Finset.univ.filter (fun g : Fin gates.length => g.val < k ∧ isMerge gates t g)) := by
            ext g
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hlt, hm⟩
              by_cases hge : g.val = k
              · exact Or.inl (Fin.ext hge)
              · exact Or.inr ⟨by omega, hm⟩
            · rintro (rfl | ⟨hlt, hm⟩)
              · exact ⟨by simp [gk], hmg⟩
              · exact ⟨by omega, hm⟩
          rw [hset, Finset.card_insert_of_notMem (by simp [gk])]
        · simp only [hmg, ↓reduceIte, add_zero]
          congr 1; ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hm⟩
            have hne : g ≠ gk := fun h => hmg (h ▸ hm)
            have hval : g.val ≠ k := fun h => hne (Fin.ext h)
            exact ⟨by omega, hm⟩
          · rintro ⟨hlt, hm⟩; exact ⟨by omega, hm⟩
      change (parts gates t (k + 1)).card + (if isMerge gates t gk then 1 else 0) =
        (parts gates t k).card at hstep
      omega
  have hfull := htel gates.length le_rfl
  have hfilter_all :
      Finset.univ.filter (fun g : Fin gates.length => g.val < gates.length ∧ isMerge gates t g) =
      Finset.univ.filter (fun g : Fin gates.length => isMerge gates t g) := by
    ext g; simp
  rw [hfilter_all] at hfull
  obtain ⟨p0, hp0L⟩ := L'_nonempty t
  have holt : o < 13 + gates.length := by
    by_contra hge
    have hmiss := missing_value gates (testIn t p0) o (by omega)
    rw [ho_on p0 hp0L] at hmiss
    exact Bool.false_ne_true hmiss.symm
  have hall_equiv : ∀ r ∈ L' t, ∀ r' ∈ L' t, equiv gates t gates.length r r' :=
    fun r hr r' hr' => safe_wire_equiv gates t hgates gates.length o holt holt
      ho_off r r' hr hr' (ho_on r hr) (ho_on r' hr')
  have hparts_end : parts gates t gates.length = {L' t} := by
    ext S
    simp only [parts, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨x, hxL, rfl⟩
      ext z; simp only [mem_cls]
      exact ⟨fun h => h.1, fun hzL => ⟨hzL, hall_equiv x hxL z hzL⟩⟩
    · rintro rfl
      refine ⟨p0, hp0L, ?_⟩
      ext z; simp only [mem_cls]
      exact ⟨fun h => h.1, fun hzL => ⟨hzL, hall_equiv p0 hp0L z hzL⟩⟩
  rw [hparts_end, Finset.card_singleton] at hfull
  omega

end LineMerges

lemma testIn_le_offL_of_disj (t p t' : Fin 13) (hp : p ∈ L' t) (hp' : p ∉ L0 t')
    (hanch : (t ≠ 0 ∧ (0 : Fin 13) ∈ L0 t ∧ p ≠ 0 → (1 : Fin 13) ∉ L0 t') ∧
      (t ≠ 0 ∧ (0 : Fin 13) ∉ L0 t ∧ p ≠ 1 → (0 : Fin 13) ∉ L0 t')) :
    ∀ v : Fin 13, testIn t p v = true → offL t' v = true := by
  intro v hv
  apply decide_eq_true
  unfold testIn at hv
  split_ifs at hv with h0 h1 h2 h3
  · have : v = p := of_decide_eq_true hv; exact this ▸ hp'
  · have : v = 0 := of_decide_eq_true hv; subst h2; exact this ▸ hp'
  · rcases of_decide_eq_true hv with rfl | rfl
    · exact hp'
    · exact hanch.1 ⟨h0, h1, h2⟩
  · have : v = 1 := of_decide_eq_true hv; subst h3; exact this ▸ hp'
  · rcases of_decide_eq_true hv with rfl | rfl
    · exact hp'
    · exact hanch.2 ⟨h0, h1, h3⟩

lemma merge_two_hits (gates : List Gate) (t : Fin 13) (g : Fin gates.length)
    (hm : isMerge gates t g) :
    ∃ r1 ∈ L' t, ∃ r2 ∈ L' t, r1 ≠ r2 ∧
      value gates (testIn t r1) (13 + g.val) = true ∧
      value gates (testIn t r2) (13 + g.val) = true := by
  obtain ⟨hor, _, w1, w2, hin, hw1, hw2, r1, hr1, r2, hr2, hv1, hv2, X, hr1X, hr2X, _⟩ := hm
  have hne : r1 ≠ r2 := fun h => hr2X (h ▸ hr1X)
  have hev (x : Fin 13 → Bool) :
      value gates x (13 + g.val) = (value gates x w1 || value gates x w2) := by
    rw [gate_value gates x g, hin, hor]; simp [GateOp.eval, hw1, hw2]
  exact ⟨r1, hr1, r2, hr2, hne, by rw [hev, hv1]; rfl, by rw [hev, hv2]; simp⟩

lemma merge_clash_only_A0_A1 (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (t t' : Fin 13) (hne : t ≠ t') (g : Fin gates.length)
    (hm : isMerge gates t g) (hm' : isMerge gates t' g) :
    (t ∈ A0 ∧ t' ∈ A1) ∨ (t ∈ A1 ∧ t' ∈ A0) := by
  have hclash (a b : Fin 13) (hab : a ≠ b) (hma : isMerge gates a g) (hmb : isMerge gates b g) :
      (a ∈ A0 ∧ (1 : Fin 13) ∈ L0 b) ∨ (a ≠ 0 ∧ (0 : Fin 13) ∉ L0 a ∧ (0 : Fin 13) ∈ L0 b) := by
    obtain ⟨r1, hr1, r2, hr2, hrne, hv1, hv2⟩ := merge_two_hits gates a g hma
    have hex : ∃ p ∈ L' a, p ∉ L0 b ∧ value gates (testIn a p) (13 + g.val) = true := by
      by_cases h1 : r1 ∈ L0 b
      · by_cases h2 : r2 ∈ L0 b
        · have hsub : ({r1, r2} : Finset (Fin 13)) ⊆ L0 a ∩ L0 b := by
            intro v hv
            rcases Finset.mem_insert.mp hv with rfl | hv2'
            · exact Finset.mem_inter.mpr ⟨L'_sub a hr1, h1⟩
            · rw [Finset.mem_singleton.mp hv2']
              exact Finset.mem_inter.mpr ⟨L'_sub a hr2, h2⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_pair hrne] at hc
          have ht := L0_thin a b hab
          omega
        · exact ⟨r2, hr2, h2, hv2⟩
      · exact ⟨r1, hr1, h1, hv1⟩
    obtain ⟨p, hp, hpb, hvp⟩ := hex
    by_contra hno
    have hle : ∀ v : Fin 13, testIn a p v = true → offL b v = true := by
      apply testIn_le_offL_of_disj a p b hp hpb
      constructor
      · rintro ⟨ha0, h0a, _⟩ h1b
        exact hno (Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha0, h0a⟩, h1b⟩)
      · rintro ⟨ha0, h0na, _⟩ h0b
        exact hno (Or.inr ⟨ha0, h0na, h0b⟩)
    have hbad := value_mono gates hgates _ _ hle (13 + g.val) hvp
    have hsf := hmb.2.1
    unfold safe at hsf
    rw [hsf] at hbad
    exact Bool.false_ne_true hbad
  have c1 := hclash t t' hne hm hm'
  have c2 := hclash t' t hne.symm hm' hm
  rcases c1 with ⟨htA0, h1t'⟩ | ⟨ht0, h0nt, h0t'⟩
  · rcases c2 with ⟨ht'A0, _⟩ | ⟨ht'0, h0nt', _⟩
    · exact False.elim (A0_no_one t' ht'A0 h1t')
    · exact Or.inl ⟨htA0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'0, h1t'⟩⟩
  · rcases c2 with ⟨ht'A0, h1t⟩ | ⟨_, h0nt', _⟩
    · exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0, h1t⟩, ht'A0⟩
    · exact False.elim (h0nt' h0t')

def inPair (gates : List Gate) (i j : Fin 13) (w : ℕ) : Prop :=
  safe gates i w ∧ safe gates j w ∧
    (∃ p ∈ L0 i, p ≠ 0 ∧ value gates (testIn i p) w = true) ∧
    (∃ q ∈ L0 j, q ≠ 1 ∧ value gates (testIn j q) w = true)

lemma inPair_unique (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i i' j j' : Fin 13) (hi : i ∈ A0) (hi' : i' ∈ A0) (hj : j ∈ A1) (hj' : j' ∈ A1)
    (w : ℕ) (h1 : inPair gates i j w) (h2 : inPair gates i' j' w) :
    i = i' ∧ j = j' := by
  constructor
  · by_contra hne
    obtain ⟨p, hpL, hp0, hvp⟩ := h1.2.2.1
    have hpnot : p ∉ L0 i' := by
      intro hpi'
      have hmem : p ∈ L0 i ∩ L0 i' := Finset.mem_inter.mpr ⟨hpL, hpi'⟩
      rw [A0_inter_zero i hi i' hi' hne, Finset.mem_singleton] at hmem
      exact hp0 hmem
    have hpL' : p ∈ L' i := by
      have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
      simpa [L', hi0] using hpL
    have hle : ∀ v : Fin 13, testIn i p v = true → offL i' v = true :=
      testIn_le_offL_of_disj i p i' hpL' hpnot
        ⟨fun _ => A0_no_one i' hi', fun h => False.elim (h.2.1 (Finset.mem_filter.mp hi).2.2)⟩
    have hbad := value_mono gates hgates _ _ hle w hvp
    have hsf := h2.1
    unfold safe at hsf
    rw [hsf] at hbad
    exact Bool.false_ne_true hbad
  · by_contra hne
    obtain ⟨q, hqL, hq1, hvq⟩ := h1.2.2.2
    have hqnot : q ∉ L0 j' := by
      intro hqj'
      have hmem : q ∈ L0 j ∩ L0 j' := Finset.mem_inter.mpr ⟨hqL, hqj'⟩
      rw [A1_inter_one j hj j' hj' hne, Finset.mem_singleton] at hmem
      exact hq1 hmem
    have hqL' : q ∈ L' j := by
      have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2.1
      simpa [L', hj0] using hqL
    have hle : ∀ v : Fin 13, testIn j q v = true → offL j' v = true :=
      testIn_le_offL_of_disj j q j' hqL' hqnot
        ⟨fun h => False.elim (A1_no_zero j hj h.2.1), fun _ => A1_no_zero j' hj'⟩
    have hbad := value_mono gates hgates _ _ hle w hvq
    have hsf := h2.2.1
    unfold safe at hsf
    rw [hsf] at hbad
    exact Bool.false_ne_true hbad

lemma inPair_not_merge_other (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i j : Fin 13) (hi : i ∈ A0) (hj : j ∈ A1) (e : Fin gates.length)
    (hip : inPair gates i j (13 + e.val)) (t : Fin 13) (hti : t ≠ i) (htj : t ≠ j) :
    ¬ isMerge gates t e := by
  intro hm
  by_cases ht0 : t = 0
  · subst ht0
    obtain ⟨r1, hr1, r2, hr2, hrne, hv1, hv2⟩ := merge_two_hits gates 0 e hm
    have h01 : r1 = 0 ∨ r1 = 1 := by simpa [L'] using hr1
    rcases h01 with rfl | rfl
    · have hle : ∀ v : Fin 13, testIn 0 0 v = true → offL j v = true := by
        intro v hv
        have : v = 0 := by simpa [testIn] using hv
        subst this; exact decide_eq_true (A1_no_zero j hj)
      have hbad := value_mono gates hgates _ _ hle (13 + e.val) hv1
      have hsf := hip.2.1; unfold safe at hsf; rw [hsf] at hbad; exact Bool.false_ne_true hbad
    · have hle : ∀ v : Fin 13, testIn 0 1 v = true → offL i v = true := by
        intro v hv
        have : v = 1 := by simpa [testIn] using hv
        subst this; exact decide_eq_true (A0_no_one i hi)
      have hbad := value_mono gates hgates _ _ hle (13 + e.val) hv1
      have hsf := hip.1; unfold safe at hsf; rw [hsf] at hbad; exact Bool.false_ne_true hbad
  · by_cases h0t : (0 : Fin 13) ∈ L0 t
    · have htA0 : t ∈ A0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0, h0t⟩
      obtain ⟨p, hpL, hp0, hvp⟩ := hip.2.2.1
      have hpnot : p ∉ L0 t := by
        intro hpt
        have hmem : p ∈ L0 i ∩ L0 t := Finset.mem_inter.mpr ⟨hpL, hpt⟩
        rw [A0_inter_zero i hi t htA0 hti.symm, Finset.mem_singleton] at hmem
        exact hp0 hmem
      have hpL' : p ∈ L' i := by
        have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
        simpa [L', hi0] using hpL
      have hle : ∀ v : Fin 13, testIn i p v = true → offL t v = true :=
        testIn_le_offL_of_disj i p t hpL' hpnot
          ⟨fun _ => A0_no_one t htA0, fun h => False.elim (h.2.1 (Finset.mem_filter.mp hi).2.2)⟩
      have hbad := value_mono gates hgates _ _ hle (13 + e.val) hvp
      have hsf := hm.2.1; unfold safe at hsf; rw [hsf] at hbad; exact Bool.false_ne_true hbad
    · obtain ⟨r1, hr1, r2, hr2, hrne, hv1, hv2⟩ := merge_two_hits gates t e hm
      have hex : ∃ p ∈ L' t, p ∉ L0 j ∧ value gates (testIn t p) (13 + e.val) = true := by
        by_cases h1 : r1 ∈ L0 j
        · by_cases h2 : r2 ∈ L0 j
          · have hsub : ({r1, r2} : Finset (Fin 13)) ⊆ L0 t ∩ L0 j := by
              intro v hv
              rcases Finset.mem_insert.mp hv with rfl | hv2'
              · exact Finset.mem_inter.mpr ⟨L'_sub t hr1, h1⟩
              · rw [Finset.mem_singleton.mp hv2']
                exact Finset.mem_inter.mpr ⟨L'_sub t hr2, h2⟩
            have hc := Finset.card_le_card hsub
            rw [Finset.card_pair hrne] at hc
            have ht := L0_thin t j htj
            omega
          · exact ⟨r2, hr2, h2, hv2⟩
        · exact ⟨r1, hr1, h1, hv1⟩
      obtain ⟨p, hp, hpj, hvp⟩ := hex
      have hle : ∀ v : Fin 13, testIn t p v = true → offL j v = true :=
        testIn_le_offL_of_disj t p j hp hpj
          ⟨fun h => False.elim (h0t h.2.1), fun _ => A1_no_zero j hj⟩
      have hbad := value_mono gates hgates _ _ hle (13 + e.val) hvp
      have hsf := hip.2.1; unfold safe at hsf; rw [hsf] at hbad; exact Bool.false_ne_true hbad

lemma exists_nonmerge_below (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i j m : Fin 13) (hi : i ∈ A0) (hj : j ∈ A1) (hijm : L0 i ∩ L0 j = {m})
    (P Q : Finset (Fin 13)) (hm_out : m ∉ P ∨ m ∉ Q)
    (w : ℕ) (hwlen : w < 13 + gates.length)
    (hip : inPair gates i j w)
    (hP : ∀ p ∈ L0 i, value gates (testIn i p) w = true → p ∈ P)
    (hQ : ∀ q ∈ L0 j, value gates (testIn j q) w = true → q ∈ Q) :
    ∃ e : Fin gates.length, 13 + e.val ≤ w ∧ inPair gates i j (13 + e.val) ∧
      ¬ isMerge gates i e ∧ ¬ isMerge gates j e ∧
      (∀ p ∈ L0 i, value gates (testIn i p) (13 + e.val) = true → p ∈ P) ∧
      (∀ q ∈ L0 j, value gates (testIn j q) (13 + e.val) = true → q ∈ Q) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw13 : w < 13
    · exfalso
      let v : Fin 13 := ⟨w, hw13⟩
      have hvi : v ∈ L0 i := by
        by_contra hnot
        have hv := input_value gates (offL i) v
        change value gates (offL i) w = decide (v ∉ L0 i) at hv
        have hsf := hip.1; unfold safe at hsf
        rw [hsf, decide_eq_true hnot] at hv
        exact Bool.false_ne_true hv
      have hvj : v ∈ L0 j := by
        by_contra hnot
        have hv := input_value gates (offL j) v
        change value gates (offL j) w = decide (v ∉ L0 j) at hv
        have hsf := hip.2.1; unfold safe at hsf
        rw [hsf, decide_eq_true hnot] at hv
        exact Bool.false_ne_true hv
      have hvm : v = m := by
        have hmem : v ∈ L0 i ∩ L0 j := Finset.mem_inter.mpr ⟨hvi, hvj⟩
        rw [hijm, Finset.mem_singleton] at hmem; exact hmem
      have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
      have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2.1
      have hmLi : m ∈ L0 i := hvm ▸ hvi
      have hmLj : m ∈ L0 j := hvm ▸ hvj
      have hmP : m ∈ P := by
        apply hP m hmLi
        have hv := input_value gates (testIn i m) v
        change value gates (testIn i m) w = testIn i m v at hv
        rw [hv, hvm]
        exact (testIn_diag i m (by simpa [L', hi0] using hmLi) m hmLi).mpr rfl
      have hmQ : m ∈ Q := by
        apply hQ m hmLj
        have hv := input_value gates (testIn j m) v
        change value gates (testIn j m) w = testIn j m v at hv
        rw [hv, hvm]
        exact (testIn_diag j m (by simpa [L', hj0] using hmLj) m hmLj).mpr rfl
      rcases hm_out with h | h
      · exact h hmP
      · exact h hmQ
    · let e : Fin gates.length := ⟨w - 13, by omega⟩
      have hweq : 13 + e.val = w := by simp [e]; omega
      by_cases hmi : isMerge gates i e
      · obtain ⟨hor, _, a, b, hin, ha, hb, r1, hr1, r2, hr2, hvr1, hvr2, _⟩ := hmi
        have hev (x : Fin 13 → Bool) :
            value gates x w = (value gates x a || value gates x b) := by
          rw [← hweq, gate_value gates x e, hin, hor]; simp [GateOp.eval, ha, hb]
        have hsai : safe gates i a := by
          have h := hip.1; unfold safe at h ⊢; rw [hev] at h; exact (Bool.or_eq_false_iff.mp h).1
        have hsbi : safe gates i b := by
          have h := hip.1; unfold safe at h ⊢; rw [hev] at h; exact (Bool.or_eq_false_iff.mp h).2
        have hsaj : safe gates j a := by
          have h := hip.2.1; unfold safe at h ⊢; rw [hev] at h; exact (Bool.or_eq_false_iff.mp h).1
        have hsbj : safe gates j b := by
          have h := hip.2.1; unfold safe at h ⊢; rw [hev] at h; exact (Bool.or_eq_false_iff.mp h).2
        have hnot0 (u : ℕ) (hsu : safe gates j u) (r : Fin 13) (hv : value gates (testIn i r) u = true) :
            r ≠ 0 := by
          rintro rfl
          have hle : ∀ v : Fin 13, testIn i 0 v = true → offL j v = true := by
            intro v hvv
            have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
            have h0i : (0 : Fin 13) ∈ L0 i := (Finset.mem_filter.mp hi).2.2
            have : v = 0 := by simpa [testIn, hi0, h0i] using hvv
            subst this; exact decide_eq_true (A1_no_zero j hj)
          have hbad := value_mono gates hgates _ _ hle u hv
          unfold safe at hsu; rw [hsu] at hbad; exact Bool.false_ne_true hbad
        obtain ⟨q, hqL, hq1, hvq⟩ := hip.2.2.2
        rw [hev] at hvq
        rcases Bool.or_eq_true_iff.mp hvq with hvqa | hvqb
        · obtain ⟨e', he'le, he'ip, he'mi, he'mj, he'P, he'Q⟩ :=
            ih a (by omega) (by omega)
              ⟨hsai, hsaj, ⟨r1, L'_sub i hr1, hnot0 a hsaj r1 hvr1, hvr1⟩, ⟨q, hqL, hq1, hvqa⟩⟩
              (fun p hp hv => hP p hp (by rw [hev, hv]; rfl))
              (fun q' hq' hv => hQ q' hq' (by rw [hev, hv]; rfl))
          exact ⟨e', by omega, he'ip, he'mi, he'mj, he'P, he'Q⟩
        · obtain ⟨e', he'le, he'ip, he'mi, he'mj, he'P, he'Q⟩ :=
            ih b (by omega) (by omega)
              ⟨hsbi, hsbj, ⟨r2, L'_sub i hr2, hnot0 b hsbj r2 hvr2, hvr2⟩, ⟨q, hqL, hq1, hvqb⟩⟩
              (fun p hp hv => hP p hp (by rw [hev, hv]; simp))
              (fun q' hq' hv => hQ q' hq' (by rw [hev, hv]; simp))
          exact ⟨e', by omega, he'ip, he'mi, he'mj, he'P, he'Q⟩
      · by_cases hmj : isMerge gates j e
        · obtain ⟨hor, _, a, b, hin, ha, hb, s1, hs1, s2, hs2, hvs1, hvs2, _⟩ := hmj
          have hev (x : Fin 13 → Bool) :
              value gates x w = (value gates x a || value gates x b) := by
            rw [← hweq, gate_value gates x e, hin, hor]; simp [GateOp.eval, ha, hb]
          have hsai : safe gates i a := by
            have h := hip.1; unfold safe at h ⊢; rw [hev] at h; exact (Bool.or_eq_false_iff.mp h).1
          have hsbi : safe gates i b := by
            have h := hip.1; unfold safe at h ⊢; rw [hev] at h; exact (Bool.or_eq_false_iff.mp h).2
          have hsaj : safe gates j a := by
            have h := hip.2.1; unfold safe at h ⊢; rw [hev] at h; exact (Bool.or_eq_false_iff.mp h).1
          have hsbj : safe gates j b := by
            have h := hip.2.1; unfold safe at h ⊢; rw [hev] at h; exact (Bool.or_eq_false_iff.mp h).2
          have hnot1 (u : ℕ) (hsu : safe gates i u) (s : Fin 13) (hv : value gates (testIn j s) u = true) :
              s ≠ 1 := by
            rintro rfl
            have hle : ∀ v : Fin 13, testIn j 1 v = true → offL i v = true := by
              intro v hvv
              have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2.1
              have h0nj : (0 : Fin 13) ∉ L0 j := A1_no_zero j hj
              have : v = 1 := by simpa [testIn, hj0, h0nj] using hvv
              subst this; exact decide_eq_true (A0_no_one i hi)
            have hbad := value_mono gates hgates _ _ hle u hv
            unfold safe at hsu; rw [hsu] at hbad; exact Bool.false_ne_true hbad
          obtain ⟨p, hpL, hp0, hvp⟩ := hip.2.2.1
          rw [hev] at hvp
          rcases Bool.or_eq_true_iff.mp hvp with hvpa | hvpb
          · obtain ⟨e', he'le, he'ip, he'mi, he'mj, he'P, he'Q⟩ :=
              ih a (by omega) (by omega)
                ⟨hsai, hsaj, ⟨p, hpL, hp0, hvpa⟩, ⟨s1, L'_sub j hs1, hnot1 a hsai s1 hvs1, hvs1⟩⟩
                (fun p' hp' hv => hP p' hp' (by rw [hev, hv]; rfl))
                (fun q' hq' hv => hQ q' hq' (by rw [hev, hv]; rfl))
            exact ⟨e', by omega, he'ip, he'mi, he'mj, he'P, he'Q⟩
          · obtain ⟨e', he'le, he'ip, he'mi, he'mj, he'P, he'Q⟩ :=
              ih b (by omega) (by omega)
                ⟨hsbi, hsbj, ⟨p, hpL, hp0, hvpb⟩, ⟨s2, L'_sub j hs2, hnot1 b hsbi s2 hvs2, hvs2⟩⟩
                (fun p' hp' hv => hP p' hp' (by rw [hev, hv]; simp))
                (fun q' hq' hv => hQ q' hq' (by rw [hev, hv]; simp))
            exact ⟨e', by omega, he'ip, he'mi, he'mj, he'P, he'Q⟩
        · exact ⟨e, by omega, hweq.symm ▸ hip, hmi, hmj,
            fun p hp hv => hP p hp (hweq ▸ hv), fun q hq hv => hQ q hq (hweq ▸ hv)⟩

lemma merge_inputs_inPair (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i j : Fin 13) (hi : i ∈ A0) (hj : j ∈ A1) (g : Fin gates.length)
    (hmi : isMerge gates i g) (hmj : isMerge gates j g) :
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ w1 < 13 + g.val ∧ w2 < 13 + g.val ∧
      inPair gates i j w1 ∧ inPair gates i j w2 ∧
      (∀ r1 ∈ L0 i, ∀ r2 ∈ L0 i, value gates (testIn i r1) w1 = true →
        value gates (testIn i r2) w2 = true → ¬ equiv gates i g.val r1 r2) ∧
      (∀ s1 ∈ L0 j, ∀ s2 ∈ L0 j, value gates (testIn j s1) w1 = true →
        value gates (testIn j s2) w2 = true → ¬ equiv gates j g.val s1 s2) := by
  obtain ⟨hor, hsfi, w1, w2, hin, hw1, hw2, r1, hr1, r2, hr2, hvr1, hvr2, Xi, hr1X, hr2X, hXi⟩ := hmi
  obtain ⟨_, hsfj, w1', w2', hin', _, _, s1, hs1, s2, hs2, hvs1, hvs2, Xj, hs1X, hs2X, hXj⟩ := hmj
  rw [hin] at hin'
  have hw1eq : w1 = w1' := by simpa using congrArg List.head? hin'
  have hw2eq : w2 = w2' := by simpa using congrArg (fun l => l.tail.head?) hin'
  subst hw1eq; subst hw2eq
  have hev (x : Fin 13 → Bool) :
      value gates x (13 + g.val) = (value gates x w1 || value gates x w2) := by
    rw [gate_value gates x g, hin, hor]; simp [GateOp.eval, hw1, hw2]
  have hs1i : safe gates i w1 := by unfold safe at hsfi ⊢; rw [hev] at hsfi; exact (Bool.or_eq_false_iff.mp hsfi).1
  have hs2i : safe gates i w2 := by unfold safe at hsfi ⊢; rw [hev] at hsfi; exact (Bool.or_eq_false_iff.mp hsfi).2
  have hs1j : safe gates j w1 := by unfold safe at hsfj ⊢; rw [hev] at hsfj; exact (Bool.or_eq_false_iff.mp hsfj).1
  have hs2j : safe gates j w2 := by unfold safe at hsfj ⊢; rw [hev] at hsfj; exact (Bool.or_eq_false_iff.mp hsfj).2
  have hnot0 (u : ℕ) (hsu : safe gates j u) (r : Fin 13) (hv : value gates (testIn i r) u = true) : r ≠ 0 := by
    rintro rfl
    have hle : ∀ v : Fin 13, testIn i 0 v = true → offL j v = true := by
      intro v hvv
      have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
      have h0i : (0 : Fin 13) ∈ L0 i := (Finset.mem_filter.mp hi).2.2
      have : v = 0 := by simpa [testIn, hi0, h0i] using hvv
      subst this; exact decide_eq_true (A1_no_zero j hj)
    have hbad := value_mono gates hgates _ _ hle u hv
    unfold safe at hsu; rw [hsu] at hbad; exact Bool.false_ne_true hbad
  have hnot1 (u : ℕ) (hsu : safe gates i u) (s : Fin 13) (hv : value gates (testIn j s) u = true) : s ≠ 1 := by
    rintro rfl
    have hle : ∀ v : Fin 13, testIn j 1 v = true → offL i v = true := by
      intro v hvv
      have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2.1
      have h0nj : (0 : Fin 13) ∉ L0 j := A1_no_zero j hj
      have : v = 1 := by simpa [testIn, hj0, h0nj] using hvv
      subst this; exact decide_eq_true (A0_no_one i hi)
    have hbad := value_mono gates hgates _ _ hle u hv
    unfold safe at hsu; rw [hsu] at hbad; exact Bool.false_ne_true hbad
  have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
  have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2.1
  refine ⟨w1, w2, hin, hw1, hw2,
    ⟨hs1i, hs1j, ⟨r1, L'_sub i hr1, hnot0 w1 hs1j r1 hvr1, hvr1⟩,
      ⟨s1, L'_sub j hs1, hnot1 w1 hs1i s1 hvs1, hvs1⟩⟩,
    ⟨hs2i, hs2j, ⟨r2, L'_sub i hr2, hnot0 w2 hs2j r2 hvr2, hvr2⟩,
      ⟨s2, L'_sub j hs2, hnot1 w2 hs2i s2 hvs2, hvs2⟩⟩, ?_, ?_⟩
  · intro a ha b hb hva hvb heq
    have ha' : a ∈ L' i := by simpa [L', hi0] using ha
    have hb' : b ∈ L' i := by simpa [L', hi0] using hb
    have h1 := safe_wire_equiv gates i hgates g.val w1 hw1 (by omega) hs1i r1 a hr1 ha' hvr1 hva
    have h2 := safe_wire_equiv gates i hgates g.val w2 hw2 (by omega) hs2i b r2 hb' hr2 hvb hvr2
    have h12 := equiv_trans gates i g.val (equiv_trans gates i g.val h1 heq) h2
    exact hr2X ((h12 Xi hXi).mp hr1X)
  · intro a ha b hb hva hvb heq
    have ha' : a ∈ L' j := by simpa [L', hj0] using ha
    have hb' : b ∈ L' j := by simpa [L', hj0] using hb
    have h1 := safe_wire_equiv gates j hgates g.val w1 hw1 (by omega) hs1j s1 a hs1 ha' hvs1 hva
    have h2 := safe_wire_equiv gates j hgates g.val w2 hw2 (by omega) hs2j b s2 hb' hs2 hvb hvs2
    have h12 := equiv_trans gates j g.val (equiv_trans gates j g.val h1 heq) h2
    exact hs2X ((h12 Xj hXj).mp hs1X)

lemma shared_pair_witness (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i j m : Fin 13) (hi : i ∈ A0) (hj : j ∈ A1) (hijm : L0 i ∩ L0 j = {m}) :
    let S := Finset.univ.filter (fun g : Fin gates.length => isMerge gates i g ∧ isMerge gates j g)
    let E := Finset.univ.filter (fun e : Fin gates.length =>
      inPair gates i j (13 + e.val) ∧ ¬ isMerge gates i e ∧ ¬ isMerge gates j e)
    S.card ≤ E.card ∧ S.card ≤ 2 ∧
    (S.card = 1 → ∃ e ∈ E, value gates (testIn i m) (13 + e.val) = false) ∧
    (S.card = 2 → ∃ e1 ∈ E, ∃ e2 ∈ E, ∃ ra rb : Fin 13, ra ≠ rb ∧
      value gates (testIn i m) (13 + e1.val) = false ∧
      value gates (testIn i m) (13 + e2.val) = false ∧
      (∀ p ∈ L0 i, value gates (testIn i p) (13 + e1.val) = true → p = ra) ∧
      (∀ p ∈ L0 i, value gates (testIn i p) (13 + e2.val) = true → p = rb)) := by
  classical
  intro S E
  have hmLi : m ∈ L0 i := by
    have : m ∈ L0 i ∩ L0 j := by rw [hijm]; simp
    exact (Finset.mem_inter.mp this).1
  have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
  have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2.1
  have hS_le2 : S.card ≤ 2 := by
    let subParts (k : ℕ) := ((L0 i).erase 0).image (cls gates i k)
    have htel : ∀ k : ℕ, k ≤ gates.length →
        (subParts k).card + (S.filter (fun g => g.val < k)).card ≤ 3 := by
      intro k hk
      induction k with
      | zero =>
        simp only [Nat.not_lt_zero, Finset.filter_false, Finset.card_empty, add_zero]
        have hle := Finset.card_image_le (s := (L0 i).erase 0) (f := cls gates i 0)
        rw [A0_card_sub i hi] at hle; exact hle
      | succ k ih =>
        have hklt : k < gates.length := by omega
        let gk : Fin gates.length := ⟨k, hklt⟩
        have hih := ih (by omega)
        have hcls_sub : ∀ x ∈ (L0 i).erase 0, ∀ y ∈ (L0 i).erase 0,
            cls gates i k x = cls gates i k y → cls gates i (k + 1) x = cls gates i (k + 1) y := by
          intro x hx y hy hxy
          have hx' : x ∈ L' i := by simpa [L', hi0] using (Finset.mem_erase.mp hx).2
          have hy' : y ∈ L' i := by simpa [L', hi0] using (Finset.mem_erase.mp hy).2
          exact (cls_eq_iff gates i (k + 1) hx' hy').mpr
            (equiv_mono gates i (Nat.le_succ _) ((cls_eq_iff gates i k hx' hy').mp hxy))
        have hsub_le : (subParts (k + 1)).card ≤ (subParts k).card := by
          have heq : subParts (k + 1) = (subParts k).image
              (fun C => if h : ∃ x ∈ (L0 i).erase 0, cls gates i k x = C then
                cls gates i (k + 1) (Classical.choose h) else ∅) := by
            ext D
            simp only [subParts, Finset.mem_image]
            constructor
            · rintro ⟨x, hx, rfl⟩
              refine ⟨cls gates i k x, ⟨x, hx, rfl⟩, ?_⟩
              have hex : ∃ y ∈ (L0 i).erase 0, cls gates i k y = cls gates i k x := ⟨x, hx, rfl⟩
              simp only [dite_eq_left hex]
              exact hcls_sub _ (Classical.choose_spec hex).1 x hx (Classical.choose_spec hex).2
            · rintro ⟨C, ⟨x, hx, rfl⟩, rfl⟩
              have hex : ∃ y ∈ (L0 i).erase 0, cls gates i k y = cls gates i k x := ⟨x, hx, rfl⟩
              simp only [dite_eq_left hex]
              exact ⟨Classical.choose hex, (Classical.choose_spec hex).1, rfl⟩
          rw [heq]; exact Finset.card_image_le
        by_cases hgk : gk ∈ S
        · have hgk_m := (Finset.mem_filter.mp hgk).2
          obtain ⟨w1, w2, hin, hw1, hw2, hip1, hip2, hne_i, _⟩ :=
            merge_inputs_inPair gates hgates i j hi hj gk hgk_m.1 hgk_m.2
          obtain ⟨r1, hr1L, hr10, hvr1⟩ := hip1.2.2.1
          obtain ⟨r2, hr2L, hr20, hvr2⟩ := hip2.2.2.1
          have hr1e : r1 ∈ (L0 i).erase 0 := Finset.mem_erase.mpr ⟨hr10, hr1L⟩
          have hr2e : r2 ∈ (L0 i).erase 0 := Finset.mem_erase.mpr ⟨hr20, hr2L⟩
          have hr1' : r1 ∈ L' i := by simpa [L', hi0] using hr1L
          have hr2' : r2 ∈ L' i := by simpa [L', hi0] using hr2L
          have hne_cls : cls gates i k r1 ≠ cls gates i k r2 := fun h =>
            hne_i r1 hr1L r2 hr2L hvr1 hvr2 ((cls_eq_iff gates i k hr1' hr2').mp h)
          have heq_cls1 : cls gates i (k + 1) r1 = cls gates i (k + 1) r2 := by
            apply (cls_eq_iff gates i (k + 1) hr1' hr2').mpr
            intro X hX
            exact hX gk (by simp [gk]) hgk_m.1.1 hgk_m.1.2.1 w1 w2 hin hw1 hw2
              r1 hr1' r2 hr2' (Or.inl hvr1) (Or.inr hvr2)
          have hdrop : (subParts (k + 1)).card + 1 ≤ (subParts k).card := by
            let f : Finset (Fin 13) → Finset (Fin 13) := fun C =>
              if h : ∃ x ∈ (L0 i).erase 0, cls gates i k x = C then
                cls gates i (k + 1) (Classical.choose h) else ∅
            have hC1 : cls gates i k r1 ∈ subParts k := Finset.mem_image.mpr ⟨r1, hr1e, rfl⟩
            have hC2 : cls gates i k r2 ∈ subParts k := Finset.mem_image.mpr ⟨r2, hr2e, rfl⟩
            have hf_eq : f (cls gates i k r1) = f (cls gates i k r2) := by
              have h1 : ∃ y ∈ (L0 i).erase 0, cls gates i k y = cls gates i k r1 := ⟨r1, hr1e, rfl⟩
              have h2 : ∃ y ∈ (L0 i).erase 0, cls gates i k y = cls gates i k r2 := ⟨r2, hr2e, rfl⟩
              simp only [f, dite_eq_left h1, dite_eq_left h2]
              rw [hcls_sub _ (Classical.choose_spec h1).1 r1 hr1e (Classical.choose_spec h1).2,
                hcls_sub _ (Classical.choose_spec h2).1 r2 hr2e (Classical.choose_spec h2).2, heq_cls1]
            have himg : subParts (k + 1) ⊆ ((subParts k).erase (cls gates i k r2)).image f := by
              intro D hD
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD
              by_cases hxr2 : cls gates i k x = cls gates i k r2
              · refine Finset.mem_image.mpr ⟨cls gates i k r1,
                  Finset.mem_erase.mpr ⟨hne_cls, hC1⟩, ?_⟩
                rw [hf_eq]
                have h2 : ∃ y ∈ (L0 i).erase 0, cls gates i k y = cls gates i k r2 := ⟨r2, hr2e, rfl⟩
                simp only [f, dite_eq_left h2]
                rw [hcls_sub _ (Classical.choose_spec h2).1 r2 hr2e (Classical.choose_spec h2).2,
                  ← hcls_sub x hx r2 hr2e hxr2]
              · refine Finset.mem_image.mpr ⟨cls gates i k x,
                  Finset.mem_erase.mpr ⟨hxr2, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩, ?_⟩
                have hxex : ∃ y ∈ (L0 i).erase 0, cls gates i k y = cls gates i k x := ⟨x, hx, rfl⟩
                simp only [f, dite_eq_left hxex]
                exact hcls_sub _ (Classical.choose_spec hxex).1 x hx (Classical.choose_spec hxex).2
            have hcard := (Finset.card_le_card himg).trans Finset.card_image_le
            rw [Finset.card_erase_of_mem hC2] at hcard
            have hpos : 1 ≤ (subParts k).card := Finset.card_pos.mpr ⟨_, hC2⟩
            omega
          have hfilt : (S.filter (fun g => g.val < k + 1)).card =
              (S.filter (fun g => g.val < k)).card + 1 := by
            have hset : S.filter (fun g => g.val < k + 1) = insert gk (S.filter (fun g => g.val < k)) := by
              ext g; simp only [Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨hgS, hlt⟩
                by_cases he : g.val = k
                · exact Or.inl (Fin.ext he)
                · exact Or.inr ⟨hgS, by omega⟩
              · rintro (rfl | ⟨hgS, hlt⟩)
                · exact ⟨hgk, by simp [gk]⟩
                · exact ⟨hgS, by omega⟩
            rw [hset, Finset.card_insert_of_notMem (by simp [gk])]
          omega
        · have hfilt : S.filter (fun g => g.val < k + 1) = S.filter (fun g => g.val < k) := by
            ext g; simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hgS, hlt⟩
              have hne : g ≠ gk := fun h => hgk (h ▸ hgS)
              have hval : g.val ≠ k := fun h => hne (Fin.ext h)
              exact ⟨hgS, by omega⟩
            · rintro ⟨hgS, hlt⟩; exact ⟨hgS, by omega⟩
          rw [hfilt]; omega
    have hfull := htel gates.length le_rfl
    have hall : S.filter (fun g => g.val < gates.length) = S := by
      ext g; simp
    rw [hall] at hfull
    have hne : (subParts gates.length).Nonempty := by
      have hne0 : ((L0 i).erase 0).Nonempty := Finset.card_pos.mp (by rw [A0_card_sub i hi]; omega)
      exact hne0.image _
    have hpos := Finset.Nonempty.card_pos hne
    omega
  by_cases hS0 : S.card = 0
  · exact ⟨by omega, hS_le2, fun h => by omega, fun h => by omega⟩
  by_cases hS1 : S.card = 1
  · obtain ⟨g, hgS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hgm := (Finset.mem_filter.mp hgS).2
    obtain ⟨w1, w2, _, hw1, hw2, hip1, hip2, hne_i, _⟩ :=
      merge_inputs_inPair gates hgates i j hi hj g hgm.1 hgm.2
    let P1 := (L0 i).filter (fun p => value gates (testIn i p) w1 = true)
    let P2 := (L0 i).filter (fun p => value gates (testIn i p) w2 = true)
    have hm_split : m ∉ P1 ∨ m ∉ P2 := by
      by_contra hboth
      push Not at hboth
      have h1 := (Finset.mem_filter.mp hboth.1)
      have h2 := (Finset.mem_filter.mp hboth.2)
      exact hne_i m h1.1 m h2.1 h1.2 h2.2 (equiv_refl gates i g.val m)
    rcases hm_split with hm1out | hm2out
    · obtain ⟨e, _, heip, hemi, hemj, heP, _⟩ := exists_nonmerge_below gates hgates i j m hi hj hijm
        P1 (L0 j) (Or.inl hm1out) w1 (by omega) hip1
        (fun p hp hv => Finset.mem_filter.mpr ⟨hp, hv⟩) (fun q hq _ => hq)
      have heE : e ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heip, hemi, hemj⟩
      have hpos : 1 ≤ E.card := Finset.card_pos.mpr ⟨e, heE⟩
      have hm_false : value gates (testIn i m) (13 + e.val) = false :=
        Bool.eq_false_iff.mpr fun h => hm1out (heP m hmLi h)
      exact ⟨by omega, hS_le2, fun _ => ⟨e, heE, hm_false⟩, fun h => by omega⟩
    · obtain ⟨e, _, heip, hemi, hemj, heP, _⟩ := exists_nonmerge_below gates hgates i j m hi hj hijm
        P2 (L0 j) (Or.inl hm2out) w2 (by omega) hip2
        (fun p hp hv => Finset.mem_filter.mpr ⟨hp, hv⟩) (fun q hq _ => hq)
      have heE : e ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heip, hemi, hemj⟩
      have hpos : 1 ≤ E.card := Finset.card_pos.mpr ⟨e, heE⟩
      have hm_false : value gates (testIn i m) (13 + e.val) = false :=
        Bool.eq_false_iff.mpr fun h => hm2out (heP m hmLi h)
      exact ⟨by omega, hS_le2, fun _ => ⟨e, heE, hm_false⟩, fun h => by omega⟩
  · have hS2 : S.card = 2 := by omega
    obtain ⟨g1, g2, hne_g, hSeq⟩ := Finset.card_eq_two.mp hS2
    have horder : ∃ ga gb : Fin gates.length, ga < gb ∧ ga ∈ S ∧ gb ∈ S := by
      have hg1 : g1 ∈ S := by rw [hSeq]; simp
      have hg2 : g2 ∈ S := by rw [hSeq]; simp
      rcases lt_or_gt_of_ne hne_g with h | h
      · exact ⟨g1, g2, h, hg1, hg2⟩
      · exact ⟨g2, g1, h, hg2, hg1⟩
    obtain ⟨g1, g2, hg12, hg1S, hg2S⟩ := horder
    have hgm1 := (Finset.mem_filter.mp hg1S).2
    have hgm2 := (Finset.mem_filter.mp hg2S).2
    obtain ⟨w1, w2, hin1, hw1, hw2, hip1, hip2, hne_i1, hne_j1⟩ :=
      merge_inputs_inPair gates hgates i j hi hj g1 hgm1.1 hgm1.2
    obtain ⟨u1, u2, _, hu1, hu2, hipu1, hipu2, hne_i2, _⟩ :=
      merge_inputs_inPair gates hgates i j hi hj g2 hgm2.1 hgm2.2
    obtain ⟨r1, hr1L, hr10, hvr1⟩ := hip1.2.2.1
    obtain ⟨r2, hr2L, hr20, hvr2⟩ := hip2.2.2.1
    obtain ⟨s1, hs1L, hs11, hvs1⟩ := hip1.2.2.2
    obtain ⟨s2, hs2L, hs21, hvs2⟩ := hip2.2.2.2
    have hr1_ne_r2 : r1 ≠ r2 := fun h =>
      hne_i1 r1 hr1L r2 hr2L hvr1 hvr2 (h ▸ equiv_refl gates i g1.val r1)
    have hs1_ne_s2 : s1 ≠ s2 := fun h =>
      hne_j1 s1 hs1L s2 hs2L hvs1 hvs2 (h ▸ equiv_refl gates j g1.val s1)
    have hcard_er : ((L0 i).erase 0).card = 3 := A0_card_sub i hi
    have hsub12 : ({r1, r2} : Finset (Fin 13)) ⊆ (L0 i).erase 0 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx2
      · exact Finset.mem_erase.mpr ⟨hr10, hr1L⟩
      · rw [Finset.mem_singleton.mp hx2]; exact Finset.mem_erase.mpr ⟨hr20, hr2L⟩
    have hex_r3 : (((L0 i).erase 0) \ {r1, r2}).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff_of_subset hsub12, hcard_er, Finset.card_pair hr1_ne_r2]; omega
    obtain ⟨r3, hr3mem⟩ := hex_r3
    have hr3e := (Finset.mem_sdiff.mp hr3mem).1
    have hr3_not12 := (Finset.mem_sdiff.mp hr3mem).2
    have hr30 : r3 ≠ 0 := (Finset.mem_erase.mp hr3e).1
    have hr3L : r3 ∈ L0 i := (Finset.mem_erase.mp hr3e).2
    have hr3_ne_r1 : r3 ≠ r1 := fun h => hr3_not12 (by simp [h])
    have hr3_ne_r2 : r3 ≠ r2 := fun h => hr3_not12 (by simp [h])
    have hLi_cover : ∀ p ∈ L0 i, p ≠ 0 → p = r1 ∨ p = r2 ∨ p = r3 := by
      intro p hpL hp0
      have hpe : p ∈ (L0 i).erase 0 := Finset.mem_erase.mpr ⟨hp0, hpL⟩
      have hsub123 : ({r1, r2, r3} : Finset (Fin 13)) ⊆ (L0 i).erase 0 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact Finset.mem_erase.mpr ⟨hr10, hr1L⟩
        · rcases Finset.mem_insert.mp hx' with rfl | hx''
          · exact Finset.mem_erase.mpr ⟨hr20, hr2L⟩
          · rw [Finset.mem_singleton.mp hx'']; exact hr3e
      have hcard123 : ({r1, r2, r3} : Finset (Fin 13)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hr1_ne_r2, hr3_ne_r1.symm]),
          Finset.card_pair hr3_ne_r2.symm]
      have heq := Finset.eq_of_subset_of_card_le hsub123 (by rw [hcard_er, hcard123])
      rw [← heq] at hpe
      simpa using hpe
    have hEq12_after : equiv gates i g2.val r1 r2 := by
      have hg1lt : g1.val < g2.val := hg12
      intro X hX
      exact hX g1 hg1lt hgm1.1.1 hgm1.1.2.1 w1 w2 hin1 hw1 hw2
        r1 (by simpa [L', hi0] using hr1L) r2 (by simpa [L', hi0] using hr2L)
        (Or.inl hvr1) (Or.inr hvr2)
    have hnot_eq_r3_r1 : ¬ equiv gates i g1.val r3 r1 := by
      intro h31
      have h31' := equiv_mono gates i (Nat.le_of_lt hg12) h31
      obtain ⟨a1, ha1L, ha10, hva1⟩ := hipu1.2.2.1
      obtain ⟨a2, ha2L, ha20, hva2⟩ := hipu2.2.2.1
      have halleq (x : Fin 13) (hxL : x ∈ L0 i) (hx0 : x ≠ 0) : equiv gates i g2.val x r1 := by
        rcases hLi_cover x hxL hx0 with hx | hx | hx
        · rw [hx]; exact equiv_refl gates i g2.val r1
        · rw [hx]; exact equiv_symm gates i g2.val hEq12_after
        · rw [hx]; exact h31'
      exact hne_i2 a1 ha1L a2 ha2L hva1 hva2
        (equiv_trans gates i g2.val (halleq a1 ha1L ha10) (equiv_symm gates i g2.val (halleq a2 ha2L ha20)))
    have hnot_eq_r3_r2 : ¬ equiv gates i g1.val r3 r2 := by
      intro h32
      have h32' := equiv_mono gates i (Nat.le_of_lt hg12) h32
      obtain ⟨a1, ha1L, ha10, hva1⟩ := hipu1.2.2.1
      obtain ⟨a2, ha2L, ha20, hva2⟩ := hipu2.2.2.1
      have halleq (x : Fin 13) (hxL : x ∈ L0 i) (hx0 : x ≠ 0) : equiv gates i g2.val x r2 := by
        rcases hLi_cover x hxL hx0 with hx | hx | hx
        · rw [hx]; exact hEq12_after
        · rw [hx]; exact equiv_refl gates i g2.val r2
        · rw [hx]; exact h32'
      exact hne_i2 a1 ha1L a2 ha2L hva1 hva2
        (equiv_trans gates i g2.val (halleq a1 ha1L ha10) (equiv_symm gates i g2.val (halleq a2 ha2L ha20)))
    have hnot0_w (u : ℕ) (hsu : safe gates j u) (p : Fin 13) (hv : value gates (testIn i p) u = true) :
        p ≠ 0 := by
      rintro rfl
      have hle : ∀ v : Fin 13, testIn i 0 v = true → offL j v = true := by
        intro v hvv
        have h0i : (0 : Fin 13) ∈ L0 i := (Finset.mem_filter.mp hi).2.2
        have : v = 0 := by simpa [testIn, hi0, h0i] using hvv
        subst this; exact decide_eq_true (A1_no_zero j hj)
      have hbad := value_mono gates hgates _ _ hle u hv
      unfold safe at hsu; rw [hsu] at hbad; exact Bool.false_ne_true hbad
    have hw1_only : ∀ p ∈ L0 i, value gates (testIn i p) w1 = true → p = r1 := by
      intro p hpL hvp
      have hp0 := hnot0_w w1 hip1.2.1 p hvp
      have heq := safe_wire_equiv gates i hgates g1.val w1 hw1 (by omega) hip1.1 p r1
        (by simpa [L', hi0] using hpL) (by simpa [L', hi0] using hr1L) hvp hvr1
      rcases hLi_cover p hpL hp0 with hp | hp | hp
      · exact hp
      · rw [hp] at heq
        exact False.elim (hne_i1 r1 hr1L r2 hr2L hvr1 hvr2 (equiv_symm gates i g1.val heq))
      · rw [hp] at heq
        exact False.elim (hnot_eq_r3_r1 heq)
    have hw2_only : ∀ p ∈ L0 i, value gates (testIn i p) w2 = true → p = r2 := by
      intro p hpL hvp
      have hp0 := hnot0_w w2 hip2.2.1 p hvp
      have heq := safe_wire_equiv gates i hgates g1.val w2 hw2 (by omega) hip2.1 p r2
        (by simpa [L', hi0] using hpL) (by simpa [L', hi0] using hr2L) hvp hvr2
      rcases hLi_cover p hpL hp0 with hp | hp | hp
      · rw [hp] at heq
        exact False.elim (hne_i1 r1 hr1L r2 hr2L hvr1 hvr2 heq)
      · exact hp
      · rw [hp] at heq
        exact False.elim (hnot_eq_r3_r2 heq)
    have hE_pair (e1 e2 : Fin gates.length) (h1 : e1 ∈ E) (h2 : e2 ∈ E) (hne : e1 ≠ e2) :
        2 ≤ E.card := by
      have hsub : ({e1, e2} : Finset (Fin gates.length)) ⊆ E := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx2
        · exact h1
        · rw [Finset.mem_singleton.mp hx2]; exact h2
      have hc := Finset.card_le_card hsub
      rw [Finset.card_pair hne] at hc; exact hc
    by_cases hm_eq_r3 : m = r3
    · have hm_ne_r1 : m ≠ r1 := hm_eq_r3 ▸ hr3_ne_r1
      have hm_ne_r2 : m ≠ r2 := hm_eq_r3 ▸ hr3_ne_r2
      obtain ⟨e1, _, he1ip, he1mi, he1mj, he1P, _⟩ := exists_nonmerge_below gates hgates i j m hi hj hijm
        {r1} (L0 j) (Or.inl (by simp [hm_ne_r1])) w1 (by omega) hip1
        (fun p hp hv => Finset.mem_singleton.mpr (hw1_only p hp hv)) (fun q hq _ => hq)
      obtain ⟨e2, _, he2ip, he2mi, he2mj, he2P, _⟩ := exists_nonmerge_below gates hgates i j m hi hj hijm
        {r2} (L0 j) (Or.inl (by simp [hm_ne_r2])) w2 (by omega) hip2
        (fun p hp hv => Finset.mem_singleton.mpr (hw2_only p hp hv)) (fun q hq _ => hq)
      have hne_e : e1 ≠ e2 := by
        rintro rfl
        obtain ⟨p, hpL, _, hvp⟩ := he1ip.2.2.1
        have h1 := Finset.mem_singleton.mp (he1P p hpL hvp)
        have h2 := Finset.mem_singleton.mp (he2P p hpL hvp)
        exact hr1_ne_r2 (h1.symm.trans h2)
      have he1E : e1 ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he1ip, he1mi, he1mj⟩
      have he2E : e2 ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he2ip, he2mi, he2mj⟩
      refine ⟨by rw [hS2]; exact hE_pair e1 e2 he1E he2E hne_e, hS_le2, fun h => by omega, fun _ =>
        ⟨e1, he1E, e2, he2E, r1, r2, hr1_ne_r2,
          Bool.eq_false_iff.mpr fun h => hm_ne_r1 (Finset.mem_singleton.mp (he1P m hmLi h)),
          Bool.eq_false_iff.mpr fun h => hm_ne_r2 (Finset.mem_singleton.mp (he2P m hmLi h)),
          fun p hp hv => Finset.mem_singleton.mp (he1P p hp hv),
          fun p hp hv => Finset.mem_singleton.mp (he2P p hp hv)⟩⟩
    · have hget_u3 : ∃ u : ℕ, u < 13 + g2.val ∧ inPair gates i j u ∧
          ∀ p ∈ L0 i, value gates (testIn i p) u = true → p = r3 := by
        obtain ⟨a1, ha1L, ha10, hva1⟩ := hipu1.2.2.1
        obtain ⟨a2, ha2L, ha20, hva2⟩ := hipu2.2.2.1
        have hcase : a1 = r3 ∨ a2 = r3 := by
          rcases hLi_cover a1 ha1L ha10 with h1 | h1 | h1
          · rcases hLi_cover a2 ha2L ha20 with h2 | h2 | h2
            · exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2 (by rw [h1, h2]; exact equiv_refl gates i g2.val r1))
            · exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2 (by rw [h1, h2]; exact hEq12_after))
            · exact Or.inr h2
          · rcases hLi_cover a2 ha2L ha20 with h2 | h2 | h2
            · exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2 (by rw [h1, h2]; exact equiv_symm gates i g2.val hEq12_after))
            · exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2 (by rw [h1, h2]; exact equiv_refl gates i g2.val r2))
            · exact Or.inr h2
          · exact Or.inl h1
        rcases hcase with h1 | h2
        · refine ⟨u1, hu1, hipu1, fun p hpL hvp => ?_⟩
          have hp0 := hnot0_w u1 hipu1.2.1 p hvp
          have hva1' : value gates (testIn i r3) u1 = true := h1 ▸ hva1
          have heq := safe_wire_equiv gates i hgates g2.val u1 hu1 (by omega) hipu1.1 p r3
            (by simpa [L', hi0] using hpL) (by simpa [L', hi0] using hr3L) hvp hva1'
          have ha2_12 : equiv gates i g2.val a2 r1 := by
            rcases hLi_cover a2 ha2L ha20 with ha2 | ha2 | ha2
            · rw [ha2]; exact equiv_refl gates i g2.val r1
            · rw [ha2]; exact equiv_symm gates i g2.val hEq12_after
            · exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2 (by rw [h1, ha2]; exact equiv_refl gates i g2.val r3))
          rcases hLi_cover p hpL hp0 with hp | hp | hp
          · rw [hp] at heq
            exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2
              (h1.symm ▸ equiv_trans gates i g2.val (equiv_symm gates i g2.val heq) (equiv_symm gates i g2.val ha2_12)))
          · rw [hp] at heq
            exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2
              (h1.symm ▸ equiv_trans gates i g2.val (equiv_symm gates i g2.val heq)
                (equiv_trans gates i g2.val (equiv_symm gates i g2.val hEq12_after)
                  (equiv_symm gates i g2.val ha2_12))))
          · exact hp
        · refine ⟨u2, hu2, hipu2, fun p hpL hvp => ?_⟩
          have hp0 := hnot0_w u2 hipu2.2.1 p hvp
          have hva2' : value gates (testIn i r3) u2 = true := h2 ▸ hva2
          have heq := safe_wire_equiv gates i hgates g2.val u2 hu2 (by omega) hipu2.1 p r3
            (by simpa [L', hi0] using hpL) (by simpa [L', hi0] using hr3L) hvp hva2'
          have ha1_12 : equiv gates i g2.val a1 r1 := by
            rcases hLi_cover a1 ha1L ha10 with ha1 | ha1 | ha1
            · rw [ha1]; exact equiv_refl gates i g2.val r1
            · rw [ha1]; exact equiv_symm gates i g2.val hEq12_after
            · exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2 (by rw [ha1, h2]; exact equiv_refl gates i g2.val r3))
          rcases hLi_cover p hpL hp0 with hp | hp | hp
          · rw [hp] at heq
            exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2
              (h2.symm ▸ equiv_trans gates i g2.val ha1_12 heq))
          · rw [hp] at heq
            exact False.elim (hne_i2 a1 ha1L a2 ha2L hva1 hva2
              (h2.symm ▸ equiv_trans gates i g2.val (equiv_trans gates i g2.val ha1_12 hEq12_after) heq))
          · exact hp
      obtain ⟨u, hult, hipu, hu_only⟩ := hget_u3
      obtain ⟨e3, _, he3ip, he3mi, he3mj, he3P, _⟩ := exists_nonmerge_below gates hgates i j m hi hj hijm
        {r3} (L0 j) (Or.inl (by simp [hm_eq_r3])) u (by omega) hipu
        (fun p hp hv => Finset.mem_singleton.mpr (hu_only p hp hv)) (fun q hq _ => hq)
      have h12 : m ≠ r1 ∨ m ≠ r2 := by
        by_contra hboth; push Not at hboth; exact hr1_ne_r2 (hboth.1.symm.trans hboth.2)
      rcases h12 with hm_ne_r1 | hm_ne_r2
      · obtain ⟨e1, _, he1ip, he1mi, he1mj, he1P, _⟩ := exists_nonmerge_below gates hgates i j m hi hj hijm
          {r1} (L0 j) (Or.inl (by simp [hm_ne_r1])) w1 (by omega) hip1
          (fun p hp hv => Finset.mem_singleton.mpr (hw1_only p hp hv)) (fun q hq _ => hq)
        have hne_e : e1 ≠ e3 := by
          rintro rfl
          obtain ⟨p, hpL, _, hvp⟩ := he1ip.2.2.1
          have h1 := Finset.mem_singleton.mp (he1P p hpL hvp)
          have h3 := Finset.mem_singleton.mp (he3P p hpL hvp)
          exact hr3_ne_r1 (h3.symm.trans h1)
        have he1E : e1 ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he1ip, he1mi, he1mj⟩
        have he3E : e3 ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he3ip, he3mi, he3mj⟩
        refine ⟨by rw [hS2]; exact hE_pair e1 e3 he1E he3E hne_e, hS_le2, fun h => by omega, fun _ =>
          ⟨e1, he1E, e3, he3E, r1, r3, hr3_ne_r1.symm,
            Bool.eq_false_iff.mpr fun h => hm_ne_r1 (Finset.mem_singleton.mp (he1P m hmLi h)),
            Bool.eq_false_iff.mpr fun h => hm_eq_r3 (Finset.mem_singleton.mp (he3P m hmLi h)),
            fun p hp hv => Finset.mem_singleton.mp (he1P p hp hv),
            fun p hp hv => Finset.mem_singleton.mp (he3P p hp hv)⟩⟩
      · obtain ⟨e2, _, he2ip, he2mi, he2mj, he2P, _⟩ := exists_nonmerge_below gates hgates i j m hi hj hijm
          {r2} (L0 j) (Or.inl (by simp [hm_ne_r2])) w2 (by omega) hip2
          (fun p hp hv => Finset.mem_singleton.mpr (hw2_only p hp hv)) (fun q hq _ => hq)
        have hne_e : e2 ≠ e3 := by
          rintro rfl
          obtain ⟨p, hpL, _, hvp⟩ := he2ip.2.2.1
          have h2 := Finset.mem_singleton.mp (he2P p hpL hvp)
          have h3 := Finset.mem_singleton.mp (he3P p hpL hvp)
          exact hr3_ne_r2 (h3.symm.trans h2)
        have he2E : e2 ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he2ip, he2mi, he2mj⟩
        have he3E : e3 ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he3ip, he3mi, he3mj⟩
        refine ⟨by rw [hS2]; exact hE_pair e2 e3 he2E he3E hne_e, hS_le2, fun h => by omega, fun _ =>
          ⟨e2, he2E, e3, he3E, r2, r3, hr3_ne_r2.symm,
            Bool.eq_false_iff.mpr fun h => hm_ne_r2 (Finset.mem_singleton.mp (he2P m hmLi h)),
            Bool.eq_false_iff.mpr fun h => hm_eq_r3 (Finset.mem_singleton.mp (he3P m hmLi h)),
            fun p hp hv => Finset.mem_singleton.mp (he2P p hp hv),
            fun p hp hv => Finset.mem_singleton.mp (he3P p hp hv)⟩⟩

lemma or_cone_and (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (t1 t2 : Fin 13) (x : Fin 13 → Bool)
    (hsep : ∀ v : Fin 13, x v = true → v ∉ L0 t1 ∨ v ∉ L0 t2)
    (w : ℕ) (hwlen : w < 13 + gates.length)
    (hs1 : value gates (offL t1) w = false) (hs2 : value gates (offL t2) w = false)
    (hx : value gates x w = true) :
    ∃ a : Fin gates.length, 13 + a.val ≤ w ∧ (gates.get a).op = GateOp.and ∧
      value gates (offL t1) (13 + a.val) = false ∧
      value gates (offL t2) (13 + a.val) = false ∧
      value gates x (13 + a.val) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw13 : w < 13
    · exfalso
      let v : Fin 13 := ⟨w, hw13⟩
      have hv1 : v ∈ L0 t1 := by
        by_contra hnot
        have hv := input_value gates (offL t1) v
        change value gates (offL t1) w = decide (v ∉ L0 t1) at hv
        rw [hs1, decide_eq_true hnot] at hv
        exact Bool.false_ne_true hv
      have hv2 : v ∈ L0 t2 := by
        by_contra hnot
        have hv := input_value gates (offL t2) v
        change value gates (offL t2) w = decide (v ∉ L0 t2) at hv
        rw [hs2, decide_eq_true hnot] at hv
        exact Bool.false_ne_true hv
      have hvx : x v = true := by
        have hv := input_value gates x v
        change value gates x w = x v at hv
        rw [← hv]; exact hx
      rcases hsep v hvx with h | h
      · exact h hv1
      · exact h hv2
    · let g : Fin gates.length := ⟨w - 13, by omega⟩
      have hweq : 13 + g.val = w := by simp [g]; omega
      rcases (hgates (gates.get g) (List.get_mem gates g)).1 with hand | hor
      · exact ⟨g, by omega, hand, hweq ▸ hs1, hweq ▸ hs2, hweq ▸ hx⟩
      · have hor_iff (y : Fin 13 → Bool) :
            value gates y w = true ↔
              ∃ r ∈ (gates.get g).inputs, r < w ∧ value gates y r = true := by
          rw [← hweq, gate_value gates y g, hor]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          constructor
          · rintro ⟨r, hr, hv⟩
            by_cases hlt : r < 13 + g.val
            · exact ⟨r, hr, by omega, by simpa [hlt] using hv⟩
            · simp [hlt] at hv
          · rintro ⟨r, hr, hlt, hv⟩
            exact ⟨r, hr, by simp [show r < 13 + g.val by omega, hv]⟩
        obtain ⟨r, hrin, hrlt, hrx⟩ := (hor_iff x).mp hx
        have hrs1 : value gates (offL t1) r = false := Bool.eq_false_iff.mpr fun h =>
          Bool.false_ne_true (hs1.symm.trans ((hor_iff (offL t1)).mpr ⟨r, hrin, hrlt, h⟩))
        have hrs2 : value gates (offL t2) r = false := Bool.eq_false_iff.mpr fun h =>
          Bool.false_ne_true (hs2.symm.trans ((hor_iff (offL t2)).mpr ⟨r, hrin, hrlt, h⟩))
        obtain ⟨a, hale, haand, has1, has2, hax⟩ := ih r hrlt (by omega) hrs1 hrs2 hrx
        exact ⟨a, by omega, haand, has1, has2, hax⟩

lemma safe0_or_split (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hno0 : ∀ a : Fin gates.length, (gates.get a).op = GateOp.and →
      value gates (offL 0) (13 + a.val) = true)
    (p : Fin 13) (w : ℕ) (hwlen : w < 13 + gates.length)
    (hs0 : value gates (offL 0) w = false)
    (hy : value gates (fun v : Fin 13 => offL 0 v || decide (v = p)) w = true) :
    value gates (fun v : Fin 13 => decide (v = p)) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw13 : w < 13
    · let q : Fin 13 := ⟨w, hw13⟩
      have h1 := input_value gates (offL 0) q
      have h2 := input_value gates (fun v => offL 0 v || decide (v = p)) q
      have h3 := input_value gates (fun v => decide (v = p)) q
      change value gates (offL 0) w = offL 0 q at h1
      change value gates (fun v => offL 0 v || decide (v = p)) w = (offL 0 q || decide (q = p)) at h2
      change value gates (fun v => decide (v = p)) w = decide (q = p) at h3
      rw [h1] at hs0; rw [h2] at hy; rw [h3]
      simp [hs0] at hy
      exact decide_eq_true hy
    · let g : Fin gates.length := ⟨w - 13, by omega⟩
      have hweq : 13 + g.val = w := by simp [g]; omega
      have hor : (gates.get g).op = GateOp.or := by
        rcases (hgates (gates.get g) (List.get_mem gates g)).1 with hand | hor
        · have ht := hno0 g hand
          rw [hweq, hs0] at ht
          exact False.elim (Bool.false_ne_true ht)
        · exact hor
      have hor_iff (y : Fin 13 → Bool) :
          value gates y w = true ↔
            ∃ r ∈ (gates.get g).inputs, r < w ∧ value gates y r = true := by
        rw [← hweq, gate_value gates y g, hor]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        constructor
        · rintro ⟨r, hr, hv⟩
          by_cases hlt : r < 13 + g.val
          · exact ⟨r, hr, by omega, by simpa [hlt] using hv⟩
          · simp [hlt] at hv
        · rintro ⟨r, hr, hlt, hv⟩
          exact ⟨r, hr, by simp [show r < 13 + g.val by omega, hv]⟩
      obtain ⟨r, hrin, hrlt, hry⟩ := (hor_iff _).mp hy
      have hrs0 : value gates (offL 0) r = false := Bool.eq_false_iff.mpr fun h =>
        Bool.false_ne_true (hs0.symm.trans ((hor_iff (offL 0)).mpr ⟨r, hrin, hrlt, h⟩))
      exact (hor_iff _).mpr ⟨r, hrin, hrlt, ih r hrlt (by omega) hrs0 hry⟩

lemma G0_cut (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hno0 : ∀ a : Fin gates.length, (gates.get a).op = GateOp.and →
      value gates (offL 0) (13 + a.val) = true)
    (G0 : Finset ℕ)
    (hG0 : ∀ w ∈ G0, 13 ≤ w ∧ w < 13 + gates.length ∧ value gates (offL 0) w = false)
    (k : ℕ) (F : Finset ℕ) (hFs0 : ∀ w ∈ F, value gates (offL 0) w = false)
    (hFk : ∀ w ∈ F, w ∈ G0 → w < k) :
    ∃ B : Finset ℕ, Disjoint B G0 ∧ (∀ w ∈ B, value gates (offL 0) w = false) ∧
      B.card ≤ F.card + (G0.filter (· < k)).card ∧
      ∀ x : Fin 13 → Bool, (∃ w ∈ F, value gates x w = true) → ∃ w ∈ B, value gates x w = true := by
  classical
  induction k generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr fun w hw hg => by have := hFk w hw hg; omega,
      hFs0, Nat.le_add_right .., fun _ h => h⟩
  | succ k ih =>
    by_cases hex : k ∈ F ∧ k ∈ G0
    · obtain ⟨hk13, hklen, hks0⟩ := hG0 k hex.2
      let gk : Fin gates.length := ⟨k - 13, by omega⟩
      have hkeq : 13 + gk.val = k := by simp [gk]; omega
      have hor : (gates.get gk).op = GateOp.or := by
        rcases (hgates (gates.get gk) (List.get_mem gates gk)).1 with hand | hor
        · have ht := hno0 gk hand
          rw [hkeq, hks0] at ht
          exact False.elim (Bool.false_ne_true ht)
        · exact hor
      have hor_iff (y : Fin 13 → Bool) :
          value gates y k = true ↔
            ∃ r ∈ (gates.get gk).inputs, r < k ∧ value gates y r = true := by
        rw [← hkeq, gate_value gates y gk, hor]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        constructor
        · rintro ⟨r, hr, hv⟩
          by_cases hlt : r < 13 + gk.val
          · exact ⟨r, hr, by omega, by simpa [hlt] using hv⟩
          · simp [hlt] at hv
        · rintro ⟨r, hr, hlt, hv⟩
          exact ⟨r, hr, by simp [show r < 13 + gk.val by omega, hv]⟩
      let P := (gates.get gk).inputs.toFinset.filter (· < k)
      have hPcard : P.card ≤ 2 := (Finset.card_filter_le _ _).trans
        ((List.toFinset_card_le _).trans (hgates (gates.get gk) (List.get_mem gates gk)).2)
      let F' := F.erase k ∪ P
      have hF's0 : ∀ w ∈ F', value gates (offL 0) w = false := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · exact hFs0 w (Finset.mem_erase.mp hw1).2
        · obtain ⟨hrin, hrlt⟩ := Finset.mem_filter.mp hw2
          exact Bool.eq_false_iff.mpr fun h =>
            Bool.false_ne_true (hks0.symm.trans ((hor_iff (offL 0)).mpr ⟨w, List.mem_toFinset.mp hrin, hrlt, h⟩))
      have hF'k : ∀ w ∈ F', w ∈ G0 → w < k := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · have hne := (Finset.mem_erase.mp hw1).1
          have hlt := hFk w (Finset.mem_erase.mp hw1).2 hg
          omega
        · exact (Finset.mem_filter.mp hw2).2
      obtain ⟨B, hd, hBs0, hBcard, hBhit⟩ := ih F' hF's0 hF'k
      have hF'card : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase k) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilt : G0.filter (· < k + 1) = insert k (G0.filter (· < k)) := by
        ext w; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = k
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, hBs0, ?_, ?_⟩
      · rw [hfilt, Finset.card_insert_of_notMem (by simp)]; omega
      · intro x ⟨w, hwF, hwx⟩
        apply hBhit x
        by_cases hwk : w = k
        · subst hwk
          obtain ⟨r, hrin, hrlt, hrx⟩ := (hor_iff x).mp hwx
          exact ⟨r, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hrin, hrlt⟩), hrx⟩
        · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hwF⟩), hwx⟩
    · have hF'k : ∀ w ∈ F, w ∈ G0 → w < k := by
        intro w hw hg
        have hne : w ≠ k := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hFk w hw hg
        omega
      obtain ⟨B, hd, hBs0, hBcard, hBhit⟩ := ih F hFs0 hF'k
      have hle : (G0.filter (· < k)).card ≤ (G0.filter (· < k + 1)).card :=
        Finset.card_le_card fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, hBs0, by omega, hBhit⟩

lemma main (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (gates : List Gate) (o : Fin 13 → ℕ)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hout : ∀ (t : Fin 13) (x : Fin 13 → Bool),
      (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) →
      Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) :
    38 ≤ gates.length := by
  classical
  have hLeq : L = L0 := funext hL
  subst hLeq
  let mg (g : Fin gates.length) : ℕ :=
    (Finset.univ.filter (fun t : Fin 13 => isMerge gates t g)).card
  have hline : ∀ t : Fin 13,
      (Finset.univ.filter (fun g : Fin gates.length => isMerge gates t g)).card = (L' t).card - 1 := by
    intro t
    refine line_merge_count gates t hgates (o t) ?_ ?_
    · rw [← eval_eq_value, hout t _ (offL_F01 t)]
      apply decide_eq_false
      rintro ⟨v, hvL, hvnot⟩
      exact (of_decide_eq_true hvnot) hvL
    · intro p hp
      have hF : F01 (testIn t p) := by
        rcases testIn_F01 t p hp with h0 | h1
        · exact Or.inl h0
        · exact Or.inr (Or.inl h1)
      rw [← eval_eq_value, hout t _ hF]
      exact decide_eq_true ⟨p, L'_sub t hp, (testIn_diag t p hp p (L'_sub t hp)).mpr rfl⟩
  have hsum_mg : ∑ g : Fin gates.length, mg g = 37 := by
    calc ∑ g : Fin gates.length, mg g
        = ∑ t : Fin 13, (Finset.univ.filter (fun g : Fin gates.length => isMerge gates t g)).card := by
          have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := (Finset.univ : Finset (Fin gates.length)))
            (t := (Finset.univ : Finset (Fin 13)))
            (r := fun g t => isMerge gates t g)
          simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, mg] using key
      _ = ∑ t : Fin 13, ((L' t).card - 1) := Finset.sum_congr rfl fun t _ => hline t
      _ = 37 := L'_sum
  have hmg_le2 : ∀ g : Fin gates.length, mg g ≤ 2 := by
    intro g
    by_contra! hgt
    have hge3 : 2 < (Finset.univ.filter (fun t : Fin 13 => isMerge gates t g)).card := hgt
    obtain ⟨t1, ht1, t2, ht2, t3, ht3, h12, h13, h23⟩ := Finset.two_lt_card.mp hge3
    have hm1 := (Finset.mem_filter.mp ht1).2
    have hm2 := (Finset.mem_filter.mp ht2).2
    have hm3 := (Finset.mem_filter.mp ht3).2
    have c12 := merge_clash_only_A0_A1 gates hgates t1 t2 h12 g hm1 hm2
    have c13 := merge_clash_only_A0_A1 gates hgates t1 t3 h13 g hm1 hm3
    have c23 := merge_clash_only_A0_A1 gates hgates t2 t3 h23 g hm2 hm3
    rcases c12 with ⟨h1A0, h2A1⟩ | ⟨h1A1, h2A0⟩
    · rcases c13 with ⟨_, h3A1⟩ | ⟨h1A1, _⟩
      · rcases c23 with ⟨h2A0, _⟩ | ⟨_, h3A0⟩
        · exact A0_no_one t2 h2A0 (Finset.mem_filter.mp h2A1).2.2
        · exact A0_no_one t3 h3A0 (Finset.mem_filter.mp h3A1).2.2
      · exact A0_no_one t1 h1A0 (Finset.mem_filter.mp h1A1).2.2
    · rcases c13 with ⟨h1A0, _⟩ | ⟨_, h3A0⟩
      · exact A0_no_one t1 h1A0 (Finset.mem_filter.mp h1A1).2.2
      · rcases c23 with ⟨_, h3A1⟩ | ⟨h2A1, _⟩
        · exact A0_no_one t3 h3A0 (Finset.mem_filter.mp h3A1).2.2
        · exact A0_no_one t2 h2A0 (Finset.mem_filter.mp h2A1).2.2
  let S_all := Finset.univ.filter (fun g : Fin gates.length => 2 ≤ mg g)
  let E_all := Finset.univ.filter (fun g : Fin gates.length => mg g = 0)
  have hpoint : ∀ g : Fin gates.length,
      1 + (if g ∈ S_all then 1 else 0) = mg g + (if g ∈ E_all then 1 else 0) := by
    intro g
    have hle := hmg_le2 g
    simp only [S_all, E_all, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> omega
  have hbalance : gates.length + S_all.card = 37 + E_all.card := by
    have htot := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin gates.length))) rfl
      (fun g _ => hpoint g)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, hsum_mg, Finset.sum_boole, Finset.sum_boole] at htot
    have h1 : (Finset.univ.filter (fun g : Fin gates.length => g ∈ S_all)).card = S_all.card := by
      congr 1; ext g; simp
    have h2 : (Finset.univ.filter (fun g : Fin gates.length => g ∈ E_all)).card = E_all.card := by
      congr 1; ext g; simp
    rw [h1, h2] at htot
    exact htot
  let pairS (p : Fin 13 × Fin 13) : Finset (Fin gates.length) :=
    Finset.univ.filter (fun g : Fin gates.length => isMerge gates p.1 g ∧ isMerge gates p.2 g)
  let pairE (p : Fin 13 × Fin 13) : Finset (Fin gates.length) :=
    Finset.univ.filter (fun e : Fin gates.length =>
      inPair gates p.1 p.2 (13 + e.val) ∧ ¬ isMerge gates p.1 e ∧ ¬ isMerge gates p.2 e)
  have hS_sub : S_all ⊆ (A0 ×ˢ A1).biUnion pairS := by
    intro g hg
    have hge2 : 1 < (Finset.univ.filter (fun t : Fin 13 => isMerge gates t g)).card :=
      Nat.lt_of_lt_of_le (by omega) (Finset.mem_filter.mp hg).2
    obtain ⟨t1, ht1, t2, ht2, h12⟩ := Finset.one_lt_card.mp hge2
    have hm1 := (Finset.mem_filter.mp ht1).2
    have hm2 := (Finset.mem_filter.mp ht2).2
    rcases merge_clash_only_A0_A1 gates hgates t1 t2 h12 g hm1 hm2 with ⟨h1A0, h2A1⟩ | ⟨h1A1, h2A0⟩
    · exact Finset.mem_biUnion.mpr ⟨(t1, t2), Finset.mem_product.mpr ⟨h1A0, h2A1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm1, hm2⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(t2, t1), Finset.mem_product.mpr ⟨h2A0, h1A1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm2, hm1⟩⟩
  have hE_disj : ((A0 ×ˢ A1 : Finset (Fin 13 × Fin 13)) : Set (Fin 13 × Fin 13)).PairwiseDisjoint pairE := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_product] at hp hq
    refine Finset.disjoint_left.mpr fun e hep heq => hpq ?_
    have hip1 := (Finset.mem_filter.mp hep).2.1
    have hip2 := (Finset.mem_filter.mp heq).2.1
    obtain ⟨h1, h2⟩ := inPair_unique gates hgates p.1 q.1 p.2 q.2 hp.1 hq.1 hp.2 hq.2 (13 + e.val) hip1 hip2
    exact Prod.ext h1 h2
  have hE_sub : (A0 ×ˢ A1).biUnion pairE ⊆ E_all := by
    intro e he
    obtain ⟨p, hp, hep⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hip, hni, hnj⟩ := (Finset.mem_filter.mp hep).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hempty : Finset.univ.filter (fun t : Fin 13 => isMerge gates t e) = ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hmt
      by_cases ht1 : t = p.1
      · exact hni (ht1 ▸ hmt)
      · by_cases ht2 : t = p.2
        · exact hnj (ht2 ▸ hmt)
        · exact inPair_not_merge_other gates hgates p.1 p.2 hp1 hp2 e hip t ht1 ht2 hmt
    change (Finset.univ.filter (fun t : Fin 13 => isMerge gates t e)).card = 0
    rw [hempty, Finset.card_empty]
  have hpair_le : ∀ p ∈ A0 ×ˢ A1, (pairS p).card ≤ (pairE p).card := by
    intro p hp
    obtain ⟨m, hijm, _, _⟩ := A0_inter_A1 p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2
    exact (shared_pair_witness gates hgates p.1 p.2 m
      (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2 hijm).1
  have hS_le_sum : S_all.card ≤ ∑ p ∈ A0 ×ˢ A1, (pairS p).card :=
    (Finset.card_le_card hS_sub).trans Finset.card_biUnion_le
  have hsum_le_sum : ∑ p ∈ A0 ×ˢ A1, (pairS p).card ≤ ∑ p ∈ A0 ×ˢ A1, (pairE p).card :=
    Finset.sum_le_sum hpair_le
  have hsum_eq_uE : ∑ p ∈ A0 ×ˢ A1, (pairE p).card = ((A0 ×ˢ A1).biUnion pairE).card :=
    (Finset.card_biUnion hE_disj).symm
  have huE_le_E : ((A0 ×ˢ A1).biUnion pairE).card ≤ E_all.card := Finset.card_le_card hE_sub
  by_contra! hlt
  have hE_eq_S : E_all.card = S_all.card := by omega
  have huE_eq : (A0 ×ˢ A1).biUnion pairE = E_all :=
    Finset.eq_of_subset_of_card_le hE_sub (by omega)
  have hpair_eq : ∀ p ∈ A0 ×ˢ A1, (pairS p).card = (pairE p).card := by
    intro p hp
    by_contra hne
    have hltp : (pairS p).card < (pairE p).card := Nat.lt_of_le_of_ne (hpair_le p hp) hne
    have hsum_lt : ∑ q ∈ A0 ×ˢ A1, (pairS q).card < ∑ q ∈ A0 ×ˢ A1, (pairE q).card :=
      Finset.sum_lt_sum hpair_le ⟨p, hp, hltp⟩
    omega
  have hno0 : ∀ a : Fin gates.length, (gates.get a).op = GateOp.and →
      value gates (offL 0) (13 + a.val) = true := by
    by_contra! hex_bad
    let Bad := Finset.univ.filter (fun a : Fin gates.length =>
      (gates.get a).op = GateOp.and ∧ value gates (offL 0) (13 + a.val) = false)
    have hBad_ne : (Bad.image Fin.val).Nonempty := by
      obtain ⟨a0, ha0and, ha0f⟩ := hex_bad
      exact ⟨a0.val, Finset.mem_image.mpr ⟨a0, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ha0and, Bool.eq_false_iff.mpr ha0f⟩, rfl⟩⟩
    let minVal := (Bad.image Fin.val).min' hBad_ne
    have hmin_mem : minVal ∈ Bad.image Fin.val := Finset.min'_mem _ hBad_ne
    obtain ⟨amin, hamin_Bad, hamin_val⟩ := Finset.mem_image.mp hmin_mem
    obtain ⟨hamin_and, hamin_s0⟩ := (Finset.mem_filter.mp hamin_Bad).2
    have hmin_prop : ∀ a : Fin gates.length, a.val < amin.val →
        (gates.get a).op = GateOp.and → value gates (offL 0) (13 + a.val) = true := by
      intro a halt haand
      apply Bool.eq_true_of_not_eq_false
      intro has0
      have hmem : a.val ∈ Bad.image Fin.val := Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haand, has0⟩, rfl⟩
      have hle := Finset.min'_le _ a.val hmem
      change minVal ≤ a.val at hle
      omega
    have hamin_E : amin ∈ E_all := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hempty : Finset.univ.filter (fun t : Fin 13 => isMerge gates t amin) = ∅ := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hm
        have hor := hm.1; rw [hamin_and] at hor; exact GateOp.noConfusion hor
      change (Finset.univ.filter (fun t : Fin 13 => isMerge gates t amin)).card = 0
      rw [hempty, Finset.card_empty]
    rw [← huE_eq] at hamin_E
    obtain ⟨⟨i, j⟩, hij_prod, hamin_pE⟩ := Finset.mem_biUnion.mp hamin_E
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij_prod
    obtain ⟨m, hijm, hm0, hm1⟩ := A0_inter_A1 i hi j hj
    have hamin_ip : inPair gates i j (13 + amin.val) := (Finset.mem_filter.mp hamin_pE).2.1
    obtain ⟨p0, hp0L, hp0ne0, hvp0⟩ := hamin_ip.2.2.1
    obtain ⟨q0, hq0L, hq0ne1, hvq0⟩ := hamin_ip.2.2.2
    have hsep_0i : ∀ v : Fin 13, testIn i p0 v = true → v ∉ L0 0 ∨ v ∉ L0 i := by
      intro v hv
      have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
      have h0i : (0 : Fin 13) ∈ L0 i := (Finset.mem_filter.mp hi).2.2
      have hvp : v = p0 ∨ v = 1 := by simpa [testIn, hi0, h0i, hp0ne0] using hv
      rcases hvp with hvp | hvp
      · rw [hvp]
        refine Or.inl fun hp0L0 => hp0ne0 ?_
        have hmem : p0 ∈ L0 i ∩ L0 0 := Finset.mem_inter.mpr ⟨hp0L, hp0L0⟩
        rw [A0_inter_L0_zero i hi, Finset.mem_singleton] at hmem; exact hmem
      · rw [hvp]; exact Or.inr (A0_no_one i hi)
    have hsep_0j : ∀ v : Fin 13, testIn j q0 v = true → v ∉ L0 0 ∨ v ∉ L0 j := by
      intro v hv
      have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2.1
      have h0nj : (0 : Fin 13) ∉ L0 j := A1_no_zero j hj
      have hvq : v = q0 ∨ v = 0 := by simpa [testIn, hj0, h0nj, hq0ne1] using hv
      rcases hvq with hvq | hvq
      · rw [hvq]
        refine Or.inl fun hq0L0 => hq0ne1 ?_
        have hmem : q0 ∈ L0 j ∩ L0 0 := Finset.mem_inter.mpr ⟨hq0L, hq0L0⟩
        rw [A1_inter_L0_zero j hj, Finset.mem_singleton] at hmem; exact hmem
      · rw [hvq]; exact Or.inr (A1_no_zero j hj)
    have hchild_safe_ij : ∃ v : ℕ, v < 13 + amin.val ∧ safe gates i v ∧ safe gates j v ∧
        (∀ x : Fin 13 → Bool, value gates x (13 + amin.val) = true → value gates x v = true) := by
      have h2len := (hgates (gates.get amin) (List.get_mem gates amin)).2
      cases hin : (gates.get amin).inputs with
      | nil =>
        rw [gate_value gates (offL 0) amin, hin, hamin_and] at hamin_s0
        simp [GateOp.eval] at hamin_s0
      | cons u rest =>
        cases rest with
        | nil =>
          by_cases hu : u < 13 + amin.val
          · have hev (x : Fin 13 → Bool) : value gates x (13 + amin.val) = value gates x u := by
              rw [gate_value gates x amin, hin, hamin_and]; simp [GateOp.eval, hu]
            obtain ⟨a', ha'le, ha'and, ha's0, _, _⟩ := or_cone_and gates hgates 0 i (testIn i p0)
              hsep_0i u (by omega) (by rw [← hev]; exact hamin_s0)
              (by rw [← hev]; exact hamin_ip.1) (by rw [← hev]; exact hvp0)
            have ht := hmin_prop a' (by omega) ha'and
            rw [ha's0] at ht; exact False.elim (Bool.false_ne_true ht)
          · rw [gate_value gates (testIn i p0) amin, hin, hamin_and] at hvp0
            simp [GateOp.eval, hu] at hvp0
        | cons v rest2 =>
          cases rest2 with
          | cons c rest3 => rw [hin] at h2len; simp at h2len
          | nil =>
            by_cases hu : u < 13 + amin.val
            · by_cases hv : v < 13 + amin.val
              · have hev (x : Fin 13 → Bool) :
                    value gates x (13 + amin.val) = (value gates x u && value gates x v) := by
                  rw [gate_value gates x amin, hin, hamin_and]; simp [GateOp.eval, hu, hv]
                have hs0_uv : value gates (offL 0) u = false ∨ value gates (offL 0) v = false :=
                  Bool.and_eq_false_iff.mp (by rw [← hev]; exact hamin_s0)
                have hsi_uv : safe gates i u ∨ safe gates i v :=
                  Bool.and_eq_false_iff.mp (by rw [← hev]; exact hamin_ip.1)
                have hsj_uv : safe gates j u ∨ safe gates j v :=
                  Bool.and_eq_false_iff.mp (by rw [← hev]; exact hamin_ip.2.1)
                have hp0_uv : value gates (testIn i p0) u = true ∧ value gates (testIn i p0) v = true :=
                  Bool.and_eq_true_iff.mp (by rw [← hev]; exact hvp0)
                have hq0_uv : value gates (testIn j q0) u = true ∧ value gates (testIn j q0) v = true :=
                  Bool.and_eq_true_iff.mp (by rw [← hev]; exact hvq0)
                have hkill_0i (w : ℕ) (hw : w < 13 + amin.val)
                    (h0 : value gates (offL 0) w = false) (hiw : safe gates i w)
                    (hpw : value gates (testIn i p0) w = true) : False := by
                  obtain ⟨a', ha'le, ha'and, ha's0, _, _⟩ := or_cone_and gates hgates 0 i (testIn i p0)
                    hsep_0i w (by omega) h0 hiw hpw
                  have ht := hmin_prop a' (by omega) ha'and
                  rw [ha's0] at ht; exact Bool.false_ne_true ht
                have hkill_0j (w : ℕ) (hw : w < 13 + amin.val)
                    (h0 : value gates (offL 0) w = false) (hjw : safe gates j w)
                    (hqw : value gates (testIn j q0) w = true) : False := by
                  obtain ⟨a', ha'le, ha'and, ha's0, _, _⟩ := or_cone_and gates hgates 0 j (testIn j q0)
                    hsep_0j w (by omega) h0 hjw hqw
                  have ht := hmin_prop a' (by omega) ha'and
                  rw [ha's0] at ht; exact Bool.false_ne_true ht
                rcases hs0_uv with hu0 | hv0
                · rcases hsi_uv with hui | hvi
                  · exact False.elim (hkill_0i u hu hu0 hui hp0_uv.1)
                  · rcases hsj_uv with huj | hvj
                    · exact False.elim (hkill_0j u hu hu0 huj hq0_uv.1)
                    · exact ⟨v, hv, hvi, hvj, fun x hx => (Bool.and_eq_true_iff.mp (by rw [← hev]; exact hx)).2⟩
                · rcases hsi_uv with hui | hvi
                  · rcases hsj_uv with huj | hvj
                    · exact ⟨u, hu, hui, huj, fun x hx => (Bool.and_eq_true_iff.mp (by rw [← hev]; exact hx)).1⟩
                    · exact False.elim (hkill_0j v hv hv0 hvj hq0_uv.2)
                  · exact False.elim (hkill_0i v hv hv0 hvi hp0_uv.2)
              · rw [gate_value gates (testIn i p0) amin, hin, hamin_and] at hvp0
                simp [GateOp.eval, hv] at hvp0
            · rw [gate_value gates (testIn i p0) amin, hin, hamin_and] at hvp0
              simp [GateOp.eval, hu] at hvp0
    obtain ⟨v_ch, hv_lt, hv_si, hv_sj, hv_ge⟩ := hchild_safe_ij
    obtain ⟨_, hS_le2, hW1, hW2⟩ := shared_pair_witness gates hgates i j m hi hj hijm
    change (pairS (i, j)).card ≤ 2 at hS_le2
    have hpeq := hpair_eq (i, j) hij_prod
    have hEpos : 1 ≤ (pairE (i, j)).card := Finset.card_pos.mpr ⟨amin, hamin_pE⟩
    have hcase_m : value gates (testIn i m) (13 + amin.val) = false := by
      apply Bool.eq_false_iff.mpr; intro hm_true
      by_cases hS1 : (pairS (i, j)).card = 1
      · obtain ⟨e1, he1E, he1m⟩ := hW1 hS1
        have hne : e1 ≠ amin := fun h => by rw [h, hm_true] at he1m; exact Bool.false_ne_true he1m.symm
        have hsub : ({e1, amin} : Finset (Fin gates.length)) ⊆ pairE (i, j) := by
          intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx2
          · exact he1E
          · rw [Finset.mem_singleton.mp hx2]; exact hamin_pE
        have hc := Finset.card_le_card hsub; rw [Finset.card_pair hne] at hc; omega
      · have hS2 : (pairS (i, j)).card = 2 := by omega
        obtain ⟨e1, he1E, e2, he2E, ra, rb, hrab, he1m, he2m, he1P, he2P⟩ := hW2 hS2
        have hne1 : e1 ≠ amin := fun h => by rw [h, hm_true] at he1m; exact Bool.false_ne_true he1m.symm
        have hne2 : e2 ≠ amin := fun h => by rw [h, hm_true] at he2m; exact Bool.false_ne_true he2m.symm
        have hne12 : e1 ≠ e2 := by
          rintro rfl
          obtain ⟨p, hpL, _, hvp⟩ := (Finset.mem_filter.mp he1E).2.1.2.2.1
          exact hrab ((he1P p hpL hvp).symm.trans (he2P p hpL hvp))
        have hsub : ({e1, e2, amin} : Finset (Fin gates.length)) ⊆ pairE (i, j) := by
          intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact he1E
          · rcases Finset.mem_insert.mp hx' with rfl | hx''
            · exact he2E
            · rw [Finset.mem_singleton.mp hx'']; exact hamin_pE
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [hne12, hne1]), Finset.card_pair hne2] at hc
        omega
    have hp0_ne_m : p0 ≠ m := fun h => by
      rw [h, hcase_m] at hvp0; exact Bool.false_ne_true hvp0
    have hsep_ij : ∀ v : Fin 13, testIn i p0 v = true → v ∉ L0 i ∨ v ∉ L0 j := by
      intro v hv
      have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
      have h0i : (0 : Fin 13) ∈ L0 i := (Finset.mem_filter.mp hi).2.2
      have hvp : v = p0 ∨ v = 1 := by simpa [testIn, hi0, h0i, hp0ne0] using hv
      rcases hvp with hvp | hvp
      · rw [hvp]
        refine Or.inr fun hp0Lj => hp0_ne_m ?_
        have hmem : p0 ∈ L0 i ∩ L0 j := Finset.mem_inter.mpr ⟨hp0L, hp0Lj⟩
        rw [hijm, Finset.mem_singleton] at hmem; exact hmem
      · rw [hvp]; exact Or.inl (A0_no_one i hi)
    obtain ⟨av, hav_le, hav_and, hav_si, hav_sj, hav_p0⟩ :=
      or_cone_and gates hgates i j (testIn i p0) hsep_ij v_ch (by omega) hv_si hv_sj
        (hv_ge (testIn i p0) hvp0)
    have hav_ne : av ≠ amin := fun h => by omega
    have hav_E : av ∈ E_all := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hempty : Finset.univ.filter (fun t : Fin 13 => isMerge gates t av) = ∅ := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hm; have hor := hm.1; rw [hav_and] at hor; exact GateOp.noConfusion hor
      change (Finset.univ.filter (fun t : Fin 13 => isMerge gates t av)).card = 0
      rw [hempty, Finset.card_empty]
    rw [← huE_eq] at hav_E
    obtain ⟨⟨i', j'⟩, hi'j'_prod, hav_pE'⟩ := Finset.mem_biUnion.mp hav_E
    obtain ⟨hi', hj'⟩ := Finset.mem_product.mp hi'j'_prod
    have hav_ip' : inPair gates i' j' (13 + av.val) := (Finset.mem_filter.mp hav_pE').2.1
    have hi_eq : i = i' := by
      by_contra hne
      have hp0not : p0 ∉ L0 i' := by
        intro hmem
        have : p0 ∈ L0 i ∩ L0 i' := Finset.mem_inter.mpr ⟨hp0L, hmem⟩
        rw [A0_inter_zero i hi i' hi' hne, Finset.mem_singleton] at this; exact hp0ne0 this
      have hi0 : i ≠ 0 := (Finset.mem_filter.mp hi).2.1
      have hle : ∀ v : Fin 13, testIn i p0 v = true → offL i' v = true :=
        testIn_le_offL_of_disj i p0 i' (by simpa [L', hi0] using hp0L) hp0not
          ⟨fun _ => A0_no_one i' hi', fun h => False.elim (h.2.1 (Finset.mem_filter.mp hi).2.2)⟩
      have hbad := value_mono gates hgates _ _ hle (13 + av.val) hav_p0
      have hsf := hav_ip'.1; unfold safe at hsf; rw [hsf] at hbad; exact Bool.false_ne_true hbad
    have hj_eq : j = j' := by
      by_contra hne
      obtain ⟨q', hq'L, hq'1, hvq'⟩ := hav_ip'.2.2.2
      have hq'not : q' ∉ L0 j := by
        intro hmem
        have : q' ∈ L0 j' ∩ L0 j := Finset.mem_inter.mpr ⟨hq'L, hmem⟩
        rw [A1_inter_one j' hj' j hj (Ne.symm hne), Finset.mem_singleton] at this; exact hq'1 this
      have hj'0 : j' ≠ 0 := (Finset.mem_filter.mp hj').2.1
      have hle : ∀ v : Fin 13, testIn j' q' v = true → offL j v = true :=
        testIn_le_offL_of_disj j' q' j (by simpa [L', hj'0] using hq'L) hq'not
          ⟨fun h => False.elim (A1_no_zero j' hj' h.2.1), fun _ => A1_no_zero j hj⟩
      have hbad := value_mono gates hgates _ _ hle (13 + av.val) hvq'
      rw [hav_sj] at hbad; exact Bool.false_ne_true hbad
    subst hi_eq; subst hj_eq
    by_cases hS1 : (pairS (i, j)).card = 1
    · have hsub : ({av, amin} : Finset (Fin gates.length)) ⊆ pairE (i, j) := by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx2
        · exact hav_pE'
        · rw [Finset.mem_singleton.mp hx2]; exact hamin_pE
      have hc := Finset.card_le_card hsub; rw [Finset.card_pair hav_ne] at hc; omega
    · have hS2 : (pairS (i, j)).card = 2 := by omega
      obtain ⟨e1, he1E, e2, he2E, ra, rb, hrab, _, _, he1P, he2P⟩ := hW2 hS2
      have hne12 : e1 ≠ e2 := by
        rintro rfl
        obtain ⟨p, hpL, _, hvp⟩ := (Finset.mem_filter.mp he1E).2.1.2.2.1
        exact hrab ((he1P p hpL hvp).symm.trans (he2P p hpL hvp))
      have hEeq : pairE (i, j) = {e1, e2} := by
        apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx2
          · exact he1E
          · rw [Finset.mem_singleton.mp hx2]; exact he2E
        · rw [Finset.card_pair hne12]; omega
      have hav_in : av = e1 ∨ av = e2 := by simpa [hEeq] using hav_pE'
      have hamin_in : amin = e1 ∨ amin = e2 := by simpa [hEeq] using hamin_pE
      rcases hav_in with rfl | rfl
      · rcases hamin_in with h | rfl
        · exact hav_ne h.symm
        · exact hrab ((he1P p0 hp0L hav_p0).symm.trans (he2P p0 hp0L hvp0))
      · rcases hamin_in with rfl | h
        · exact hrab ((he1P p0 hp0L hvp0).symm.trans (he2P p0 hp0L hav_p0))
        · exact hav_ne h.symm
  -- Now NO AND gate in gates is false on offL 0!
  have ho0_off : value gates (offL 0) (o 0) = false := by
    rw [← eval_eq_value, hout 0 _ (offL_F01 0)]
    apply decide_eq_false; rintro ⟨v, hvL, hvnot⟩; exact (of_decide_eq_true hvnot) hvL
  have ho0_lt : o 0 < 13 + gates.length := by
    by_contra hge
    have hmiss := missing_value gates (testIn 0 0) (o 0) (by omega)
    have hon : value gates (testIn 0 0) (o 0) = true := by
      rw [← eval_eq_value, hout 0 _ (Or.inl (by simp [testIn]))]
      exact decide_eq_true ⟨0, by simp [L0], by simp [testIn]⟩
    rw [hon] at hmiss; exact Bool.false_ne_true hmiss.symm
  have ho0_all : ∀ p ∈ L0 0, value gates (fun v : Fin 13 => decide (v = p)) (o 0) = true := by
    intro p hp
    apply safe0_or_split gates hgates hno0 p (o 0) ho0_lt ho0_off
    rw [← eval_eq_value, hout 0 (fun v : Fin 13 => offL 0 v || decide (v = p))
      (Or.inr (Or.inr fun v hv => by simp [offL, hv]))]
    exact decide_eq_true ⟨p, hp, by simp⟩
  let supp0 (w : ℕ) : Finset (Fin 13) :=
    (L0 0).filter (fun p => value gates (fun v : Fin 13 => decide (v = p)) w = true)
  let G0w : Finset ℕ := (Finset.Ico 13 (13 + gates.length)).filter
    (fun w => value gates (offL 0) w = false ∧ 2 ≤ (supp0 w).card)
  have hG0w_sub : G0w ⊆ (Finset.univ.filter (fun g : Fin gates.length => isMerge gates 0 g)).image
      (fun g : Fin gates.length => 13 + g.val) := by
    intro w hw
    obtain ⟨hIco, hws0, hw2⟩ := Finset.mem_filter.mp hw
    obtain ⟨hw13, hwlen⟩ := Finset.mem_Ico.mp hIco
    let g : Fin gates.length := ⟨w - 13, by omega⟩
    have hweq : 13 + g.val = w := by simp [g]; omega
    refine Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hweq⟩
    have hnot_safe_other : ∀ t : Fin 13, t ≠ 0 → ¬ safe gates t w := by
      intro t ht hst
      obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (supp0 w).card)
      obtain ⟨hp1L, hvp1⟩ := Finset.mem_filter.mp hp1
      obtain ⟨hp2L, hvp2⟩ := Finset.mem_filter.mp hp2
      have hex : ∃ p ∈ L0 0, p ∉ L0 t ∧ value gates (fun v => decide (v = p)) w = true := by
        by_cases h1 : p1 ∈ L0 t
        · by_cases h2 : p2 ∈ L0 t
          · have hsub : ({p1, p2} : Finset (Fin 13)) ⊆ L0 0 ∩ L0 t := by
              intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx2
              · exact Finset.mem_inter.mpr ⟨hp1L, h1⟩
              · rw [Finset.mem_singleton.mp hx2]; exact Finset.mem_inter.mpr ⟨hp2L, h2⟩
            have hc := Finset.card_le_card hsub; rw [Finset.card_pair hpne] at hc
            have hth := L0_thin 0 t ht.symm; omega
          · exact ⟨p2, hp2L, h2, hvp2⟩
        · exact ⟨p1, hp1L, h1, hvp1⟩
      obtain ⟨p, _, hpt, hvp⟩ := hex
      have hle : ∀ v : Fin 13, decide (v = p) = true → offL t v = true := by
        intro v hv; rw [of_decide_eq_true hv]; exact decide_eq_true hpt
      have hbad := value_mono gates hgates _ _ hle w hvp
      unfold safe at hst; rw [hst] at hbad; exact Bool.false_ne_true hbad
    have hg_notE : g ∉ E_all := by
      intro hgE
      rw [← huE_eq] at hgE
      obtain ⟨⟨i, j⟩, hijp, hgpE⟩ := Finset.mem_biUnion.mp hgE
      have hi0 : i ≠ 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hijp).1).2.1
      exact hnot_safe_other i hi0 (hweq ▸ (Finset.mem_filter.mp hgpE).2.1.1)
    have hmg_pos : 0 < mg g := by
      by_contra h0
      have : mg g = 0 := by omega
      exact hg_notE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩)
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hmg_pos
    have hmt := (Finset.mem_filter.mp ht).2
    by_cases ht0 : t = 0
    · exact ht0 ▸ hmt
    · exact False.elim (hnot_safe_other t ht0 (hweq ▸ hmt.2.1))
  have hG0w_le1 : G0w.card ≤ 1 := by
    have h1 := (Finset.card_le_card hG0w_sub).trans Finset.card_image_le
    rw [hline 0] at h1
    have hcard0 : (L' 0).card = 2 := by decide
    omega
  obtain ⟨B, hdB, hBs0, hBcard, hBhit⟩ := G0_cut gates hgates hno0 G0w
    (fun w hw => ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1).1,
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1).2, (Finset.mem_filter.mp hw).2.1⟩)
    (13 + gates.length) {o 0}
    (fun w hw => by rw [Finset.mem_singleton.mp hw]; exact ho0_off)
    (fun w _ hw => (Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1).2)
  have hBsmall : ∀ w ∈ B, (supp0 w).card ≤ 1 := by
    intro w hw
    by_cases hw13 : w < 13
    · let q : Fin 13 := ⟨w, hw13⟩
      have hsub : supp0 w ⊆ {q} := by
        intro p hp
        have hvp := (Finset.mem_filter.mp hp).2
        have hinp := input_value gates (fun v => decide (v = p)) q
        change value gates (fun v => decide (v = p)) w = decide (q = p) at hinp
        rw [hinp] at hvp
        exact Finset.mem_singleton.mpr (of_decide_eq_true hvp).symm
      exact (Finset.card_le_card hsub).trans (by simp)
    · by_cases hwlen : w < 13 + gates.length
      · by_contra! hbig
        exact Finset.disjoint_left.mp hdB hw (Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, hwlen⟩, hBs0 w hw, by omega⟩)
      · have hempty : supp0 w = ∅ := by
          ext p; simp [supp0, missing_value gates _ w (by omega)]
        simp [hempty]
  have hcover : L0 0 ⊆ B.biUnion supp0 := by
    intro p hp
    obtain ⟨w, hwB, hwp⟩ := hBhit (fun v => decide (v = p)) ⟨o 0, Finset.mem_singleton_self _, ho0_all p hp⟩
    exact Finset.mem_biUnion.mpr ⟨w, hwB, Finset.mem_filter.mpr ⟨hp, hwp⟩⟩
  have h4 := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul B supp0 1 hBsmall)
  have hfilt_le := Finset.card_filter_le G0w (· < 13 + gates.length)
  rw [L0_card 0, mul_one] at h4
  simp only [Finset.card_singleton] at hBcard
  omega


lemma value_mono_before_not (gates : List Gate) (j : Fin gates.length)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin 13 → Bool) (hxy : ∀ v : Fin 13, x v = true → y v = true)
    (w : ℕ) (hw : w < 13 + j.val) :
    value gates x w = true → value gates y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw13 : w < 13
    · let p : Fin 13 := ⟨w, hw13⟩
      have hx := input_value gates x p
      have hy := input_value gates y p
      change value gates x w = x p at hx
      change value gates y w = y p at hy
      rw [hx, hy]
      exact hxy p
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hweq : 13 + i.val = w := by simp [i]; omega
      have hop : (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or := by
        rcases (hgates (gates.get i) (List.get_mem gates i)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have hij := huniq i h
          have : i.val = j.val := congrArg Fin.val hij
          omega
      rw [← hweq, gate_value gates x i, gate_value gates y i]
      have step (r : ℕ) :
          (if r < 13 + i.val then value gates x r else false) = true →
          (if r < 13 + i.val then value gates y r else false) = true := by
        by_cases hr : r < 13 + i.val
        · simpa [hr] using ih r (by omega) (by omega)
        · simp [hr]
      rcases hop with hand | hor
      · simp only [hand, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        exact fun h r hr => step r (h r hr)
      · simp only [hor, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        exact fun ⟨r, hr, hvr⟩ => ⟨r, hr, step r hvr⟩

lemma value_append_lt (gs : List Gate) (gnew : Gate) (x : Fin 13 → Bool) (u : ℕ)
    (hu : u < 13 + gs.length) :
    value (gs ++ [gnew]) x u = value gs x u := by
  change (run (gs ++ [gnew]) (List.ofFn x)).getD u false = (run gs (List.ofFn x)).getD u false
  have hsplit : run (gs ++ [gnew]) (List.ofFn x) = run [gnew] (run gs (List.ofFn x)) := by
    simp [run, List.foldl_append]
  rw [hsplit]
  exact run_getD [gnew] (run gs (List.ofFn x)) u (by simp [run_length]; omega)

lemma value_append_last (gs : List Gate) (gnew : Gate) (x : Fin 13 → Bool) :
    value (gs ++ [gnew]) x (13 + gs.length) =
      gnew.op.eval (gnew.inputs.map fun r => if r < 13 + gs.length then value gs x r else false) := by
  let idx : Fin (gs ++ [gnew]).length := ⟨gs.length, by simp⟩
  have hv := gate_value (gs ++ [gnew]) x idx
  have hget : (gs ++ [gnew]).get idx = gnew := by simp [idx]
  change value (gs ++ [gnew]) x (13 + idx.val) = _
  rw [hv, hget]
  congr 1
  apply List.map_congr_left
  intro r _
  by_cases hr : r < 13 + gs.length
  · simp [idx, hr, value_append_lt gs gnew x r hr]
  · simp [idx, hr]

inductive SimpWire where
  | cfalse : SimpWire
  | ctrue : SimpWire
  | wire : ℕ → SimpWire

def SimpWire.eval (gs : List Gate) (x : Fin 13 → Bool) : SimpWire → Bool
  | SimpWire.cfalse => false
  | SimpWire.ctrue => true
  | SimpWire.wire u => value gs x u

lemma simplify_circuit (gates : List Gate) (j h : Fin gates.length)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hh_true : ∀ x : Fin 13 → Bool, F01 x → value gates x (13 + h.val) = true)
    (hj_false : ∀ x : Fin 13 → Bool, F01 x → value gates x (13 + j.val) = false)
    (k : ℕ) (hk : k ≤ gates.length) :
    ∃ (gs : List Gate) (f : ℕ → SimpWire),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ w < 13 + k, ∀ u, f w = SimpWire.wire u → u < 13 + gs.length) ∧
      gs.length + (Finset.univ.filter (fun i : Fin gates.length =>
        i.val < k ∧ (i = h ∨ i = j ∨ (j < i ∧ 13 + j.val ∈ (gates.get i).inputs)))).card ≤ k ∧
      (∀ w < 13 + k, ∀ x : Fin 13 → Bool, F01 x → SimpWire.eval gs x (f w) = value gates x w) ∧
      (j.val < k → f (13 + j.val) = SimpWire.cfalse) := by
  classical
  induction k with
  | zero =>
    refine ⟨[], fun w => SimpWire.wire w, by simp, fun w hw u hu => by injection hu with hu'; omega,
      by simp, ?_, fun h0 => by omega⟩
    intro w hw x _
    let p : Fin 13 := ⟨w, by omega⟩
    have h1 := input_value [] x p
    have h2 := input_value gates x p
    change value [] x w = x p at h1
    change value gates x w = x p at h2
    simp [SimpWire.eval, h1, h2]
  | succ k ih =>
    obtain ⟨gs, f, hgs, hwf, hlen, heval, hfj⟩ := ih (by omega)
    let gk : Fin gates.length := ⟨k, by omega⟩
    let isDrop (i : Fin gates.length) : Prop :=
      i = h ∨ i = j ∨ (j < i ∧ 13 + j.val ∈ (gates.get i).inputs)
    change gs.length + (Finset.univ.filter (fun i : Fin gates.length => i.val < k ∧ isDrop i)).card ≤ k at hlen
    have hfilt_card :
        (Finset.univ.filter (fun i : Fin gates.length => i.val < k + 1 ∧ isDrop i)).card =
        (Finset.univ.filter (fun i : Fin gates.length => i.val < k ∧ isDrop i)).card +
          (if isDrop gk then 1 else 0) := by
      by_cases hd : isDrop gk
      · simp only [hd, ↓reduceIte]
        have hset : Finset.univ.filter (fun i : Fin gates.length => i.val < k + 1 ∧ isDrop i) =
            insert gk (Finset.univ.filter (fun i : Fin gates.length => i.val < k ∧ isDrop i)) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hlt, hi⟩
            by_cases he : i.val = k
            · exact Or.inl (Fin.ext he)
            · exact Or.inr ⟨by omega, hi⟩
          · rintro (rfl | ⟨hlt, hi⟩)
            · exact ⟨by simp [gk], hd⟩
            · exact ⟨by omega, hi⟩
        rw [hset, Finset.card_insert_of_notMem (by simp [gk])]
      · simp only [hd, ↓reduceIte, add_zero]
        congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hlt, hi⟩
          have hne : i ≠ gk := fun e => hd (e ▸ hi)
          have hval : i.val ≠ k := fun e => hne (Fin.ext e)
          exact ⟨by omega, hi⟩
        · rintro ⟨hlt, hi⟩; exact ⟨by omega, hi⟩
    have hkeep (sw : SimpWire)
        (hsw_wf : ∀ u, sw = SimpWire.wire u → u < 13 + gs.length)
        (hsw_ev : ∀ x : Fin 13 → Bool, F01 x → SimpWire.eval gs x sw = value gates x (13 + k))
        (hsw_j : gk = j → sw = SimpWire.cfalse) :
        ∃ (gs' : List Gate) (f' : ℕ → SimpWire),
          (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
          (∀ w < 13 + (k + 1), ∀ u, f' w = SimpWire.wire u → u < 13 + gs'.length) ∧
          gs'.length + (Finset.univ.filter (fun i : Fin gates.length =>
            i.val < k + 1 ∧ isDrop i)).card ≤ k + 1 ∧
          (∀ w < 13 + (k + 1), ∀ x : Fin 13 → Bool, F01 x → SimpWire.eval gs' x (f' w) = value gates x w) ∧
          (j.val < k + 1 → f' (13 + j.val) = SimpWire.cfalse) := by
      let f' (w : ℕ) : SimpWire := if w = 13 + k then sw else f w
      refine ⟨gs, f', hgs, ?_, ?_, ?_, ?_⟩
      · intro w hw u hu
        by_cases hwk : w = 13 + k
        · simp only [f', hwk, ↓reduceIte] at hu; exact hsw_wf u hu
        · simp only [f', hwk, ↓reduceIte] at hu; exact hwf w (by omega) u hu
      · rw [hfilt_card]; split_ifs <;> omega
      · intro w hw x hx
        by_cases hwk : w = 13 + k
        · subst hwk; simp only [f', ↓reduceIte]; exact hsw_ev x hx
        · simp only [f', hwk, ↓reduceIte]; exact heval w (by omega) x hx
      · intro hjlt
        by_cases hjk : j.val = k
        · have hgj : gk = j := Fin.ext hjk.symm
          simp only [f', hjk, ↓reduceIte]; exact hsw_j hgj
        · simp only [f', show 13 + j.val ≠ 13 + k by omega, ↓reduceIte]; exact hfj (by omega)
    by_cases hgh : gk = h
    · refine hkeep SimpWire.ctrue (fun _ hc => by cases hc) ?_ ?_
      · intro x hx
        have hkeq : k = h.val := congrArg Fin.val hgh
        rw [hkeq]; exact (hh_true x hx).symm
      · intro hgj
        have hhj : h = j := hgh.symm.trans hgj
        have ht := hh_true (offL 0) (offL_F01 0)
        have hf := hj_false (offL 0) (offL_F01 0)
        rw [hhj, hf] at ht; exact False.elim (Bool.false_ne_true ht)
    by_cases hgj : gk = j
    · refine hkeep SimpWire.cfalse (fun _ hc => by cases hc) ?_ (fun _ => rfl)
      intro x hx
      have hkeq : k = j.val := congrArg Fin.val hgj
      rw [hkeq]; exact (hj_false x hx).symm
    have hgj_ne : gk ≠ j := hgj
    have hop : (gates.get gk).op = GateOp.and ∨ (gates.get gk).op = GateOp.or := by
      rcases (hgates (gates.get gk) (List.get_mem gates gk)).1 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact False.elim (hgj_ne (huniq gk h1))
    let evalIn (r : ℕ) : SimpWire := if r < 13 + k then f r else SimpWire.cfalse
    have hevalIn_wf (r : ℕ) (u : ℕ) (hu : evalIn r = SimpWire.wire u) : u < 13 + gs.length := by
      by_cases hr : r < 13 + k
      · simp only [evalIn, hr, ↓reduceIte] at hu; exact hwf r hr u hu
      · simp only [evalIn, hr, ↓reduceIte] at hu; cases hu
    have hevalIn_ev (r : ℕ) (x : Fin 13 → Bool) (hx : F01 x) :
        SimpWire.eval gs x (evalIn r) = if r < 13 + k then value gates x r else false := by
      by_cases hr : r < 13 + k
      · simp only [evalIn, hr, ↓reduceIte]; exact heval r hr x hx
      · simp only [evalIn, hr, ↓reduceIte, SimpWire.eval]
    have h2len := (hgates (gates.get gk) (List.get_mem gates gk)).2
    have hnot_j : ¬ gk = j := hgj
    cases hin : (gates.get gk).inputs with
    | nil =>
      rcases hop with hand | hor
      · refine hkeep SimpWire.ctrue (fun _ hc => by cases hc) ?_ (fun e => (hnot_j e).elim)
        intro x _
        have hv := gate_value gates x gk
        change value gates x (13 + k) = _ at hv
        rw [hv, hin, hand]; rfl
      · refine hkeep SimpWire.cfalse (fun _ hc => by cases hc) ?_ (fun e => (hnot_j e).elim)
        intro x _
        have hv := gate_value gates x gk
        change value gates x (13 + k) = _ at hv
        rw [hv, hin, hor]; rfl
    | cons a rest =>
      cases rest with
      | nil =>
        refine hkeep (evalIn a) (hevalIn_wf a) ?_ (fun e => (hnot_j e).elim)
        intro x hx
        have hv := gate_value gates x gk
        change value gates x (13 + k) = _ at hv
        rcases hop with hand | hor
        · rw [hv, hin, hand, hevalIn_ev a x hx]; simp [GateOp.eval, gk]
        · rw [hv, hin, hor, hevalIn_ev a x hx]; simp [GateOp.eval, gk]
      | cons b rest2 =>
        cases rest2 with
        | cons c rest3 => rw [hin] at h2len; simp at h2len
        | nil =>
          have hval_ab (x : Fin 13 → Bool) (hx : F01 x) :
              value gates x (13 + k) =
                (gates.get gk).op.eval [SimpWire.eval gs x (evalIn a), SimpWire.eval gs x (evalIn b)] := by
            have hv := gate_value gates x gk
            change value gates x (13 + k) = _ at hv
            rw [hv, hin]
            simp only [List.map_cons, List.map_nil]
            rw [hevalIn_ev a x hx, hevalIn_ev b x hx]
          have hadd_two (u v : ℕ) (hu : evalIn a = SimpWire.wire u) (hv : evalIn b = SimpWire.wire v) :
              ∃ (gs' : List Gate) (f' : ℕ → SimpWire),
                (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
                (∀ w < 13 + (k + 1), ∀ u', f' w = SimpWire.wire u' → u' < 13 + gs'.length) ∧
                gs'.length + (Finset.univ.filter (fun i : Fin gates.length =>
                  i.val < k + 1 ∧ isDrop i)).card ≤ k + 1 ∧
                (∀ w < 13 + (k + 1), ∀ x : Fin 13 → Bool, F01 x → SimpWire.eval gs' x (f' w) = value gates x w) ∧
                (j.val < k + 1 → f' (13 + j.val) = SimpWire.cfalse) := by
            have hnotDrop : ¬ isDrop gk := by
              rintro (h1 | h1 | ⟨hjlt, hjmem⟩)
              · exact hgh h1
              · exact hgj h1
              · rw [hin] at hjmem
                have hjlt' : j.val < k := hjlt
                have hfj' : f (13 + j.val) = SimpWire.cfalse := hfj hjlt'
                have hev_j : evalIn (13 + j.val) = SimpWire.cfalse := by
                  simp [evalIn, show 13 + j.val < 13 + k by omega, hfj']
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hjmem
                rcases hjmem with hja | hjb
                · rw [← hja, hev_j] at hu; cases hu
                · rw [← hjb, hev_j] at hv; cases hv
            have hult : u < 13 + gs.length := hevalIn_wf a u hu
            have hvlt : v < 13 + gs.length := hevalIn_wf b v hv
            let gnew : Gate := ⟨(gates.get gk).op, [u, v]⟩
            let gs' := gs ++ [gnew]
            let f' (w : ℕ) : SimpWire := if w = 13 + k then SimpWire.wire (13 + gs.length) else f w
            refine ⟨gs', f', ?_, ?_, ?_, ?_, ?_⟩
            · intro g hg
              rcases List.mem_append.mp hg with hg1 | hg2
              · exact hgs g hg1
              · rw [List.mem_singleton.mp hg2]
                exact ⟨hop, by simp [gnew]⟩
            · intro w hw u' hu'
              by_cases hwk : w = 13 + k
              · simp only [f', hwk, ↓reduceIte] at hu'; injection hu' with hu''; simp [gs']; omega
              · simp only [f', hwk, ↓reduceIte] at hu'
                have := hwf w (by omega) u' hu'; simp [gs']; omega
            · rw [hfilt_card]; simp only [hnotDrop, ↓reduceIte, add_zero, gs', List.length_append,
                List.length_singleton]; omega
            · intro w hw x hx
              by_cases hwk : w = 13 + k
              · subst hwk
                simp only [f', ↓reduceIte, SimpWire.eval, gs']
                rw [value_append_last gs gnew x, hval_ab x hx, hu, hv]
                simp [gnew, hult, hvlt, SimpWire.eval]
              · simp only [f', hwk, ↓reduceIte]
                have hev_old := heval w (by omega) x hx
                rw [← hev_old]
                cases hfw : f w with
                | cfalse => rfl
                | ctrue => rfl
                | wire u' =>
                  have hu'lt := hwf w (by omega) u' hfw
                  simp only [SimpWire.eval, gs']
                  exact value_append_lt gs gnew x u' hu'lt
            · intro hjlt
              have hjk : j.val ≠ k := fun e => hgj (Fin.ext e.symm)
              simp only [f', show 13 + j.val ≠ 13 + k by omega, ↓reduceIte]
              exact hfj (by omega)
          rcases hop with hand | hor
          · cases ha : evalIn a with
            | cfalse =>
              refine hkeep SimpWire.cfalse (fun _ hc => by cases hc) ?_ (fun e => (hnot_j e).elim)
              intro x hx; rw [hval_ab x hx, ha, hand]; simp [SimpWire.eval, GateOp.eval]
            | ctrue =>
              refine hkeep (evalIn b) (hevalIn_wf b) ?_ (fun e => (hnot_j e).elim)
              intro x hx; rw [hval_ab x hx, ha, hand]; simp [SimpWire.eval, GateOp.eval]
            | wire u =>
              cases hb : evalIn b with
              | cfalse =>
                refine hkeep SimpWire.cfalse (fun _ hc => by cases hc) ?_ (fun e => (hnot_j e).elim)
                intro x hx; rw [hval_ab x hx, hb, hand]; simp [SimpWire.eval, GateOp.eval]
              | ctrue =>
                refine hkeep (SimpWire.wire u) (fun _ h => by injection h with h'; subst h'; exact hevalIn_wf a u ha)
                  ?_ (fun e => (hnot_j e).elim)
                intro x hx; rw [hval_ab x hx, ha, hb, hand]; simp [SimpWire.eval, GateOp.eval]
              | wire v => exact hadd_two u v ha hb
          · cases ha : evalIn a with
            | ctrue =>
              refine hkeep SimpWire.ctrue (fun _ hc => by cases hc) ?_ (fun e => (hnot_j e).elim)
              intro x hx; rw [hval_ab x hx, ha, hor]; simp [SimpWire.eval, GateOp.eval]
            | cfalse =>
              refine hkeep (evalIn b) (hevalIn_wf b) ?_ (fun e => (hnot_j e).elim)
              intro x hx; rw [hval_ab x hx, ha, hor]; simp [SimpWire.eval, GateOp.eval]
            | wire u =>
              cases hb : evalIn b with
              | ctrue =>
                refine hkeep SimpWire.ctrue (fun _ hc => by cases hc) ?_ (fun e => (hnot_j e).elim)
                intro x hx; rw [hval_ab x hx, hb, hor]; simp [SimpWire.eval, GateOp.eval]
              | cfalse =>
                refine hkeep (SimpWire.wire u) (fun _ h => by injection h with h'; subst h'; exact hevalIn_wf a u ha)
                  ?_ (fun e => (hnot_j e).elim)
                intro x hx; rw [hval_ab x hx, ha, hb, hor]; simp [SimpWire.eval, GateOp.eval]
              | wire v => exact hadd_two u v ha hb

lemma main_1581 (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (gates : List Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hjop : (gates.get j).op = GateOp.not)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hhj : h < j)
    (hjin : ∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r)
    (hout : ∀ (t : Fin 13) (x : Fin 13 → Bool),
      Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true))
    (hh0 : Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true)
    (hh1 : Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true)
    (hhoff : Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true) :
    40 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card ≤
      gates.length := by
  classical
  have hLeq : L = L0 := funext hL
  subst hLeq
  have hh_true : ∀ x : Fin 13 → Bool, F01 x → value gates x (13 + h.val) = true := by
    intro x hx
    have hhlt : 13 + h.val < 13 + j.val := by have : h.val < j.val := hhj; omega
    rcases hx with hx0 | hx1 | hxoff
    · exact value_mono_before_not gates j hgates huniq _ x
        (fun v hv => by rw [of_decide_eq_true hv]; exact hx0) (13 + h.val) hhlt hh0
    · exact value_mono_before_not gates j hgates huniq _ x
        (fun v hv => by rw [of_decide_eq_true hv]; exact hx1) (13 + h.val) hhlt hh1
    · exact value_mono_before_not gates j hgates huniq _ x
        (fun v hv => hxoff v (of_decide_eq_true hv)) (13 + h.val) hhlt hhoff
  have hj_false : ∀ x : Fin 13 → Bool, F01 x → value gates x (13 + j.val) = false := by
    intro x hx
    obtain ⟨r, hr⟩ := hjin
    have hhlt : 13 + h.val < 13 + j.val := by have : h.val < j.val := hhj; omega
    rw [gate_value gates x j, hr, hjop]
    simp [GateOp.eval, hhlt, hh_true x hx]
  obtain ⟨gs, f, hgs, _, hlen, heval, _⟩ :=
    simplify_circuit gates j h hgates huniq hh_true hj_false gates.length le_rfl
  have ho_wire : ∀ t : Fin 13, ∃ u : ℕ, f (o t) = SimpWire.wire u := by
    intro t
    have holt : o t < 13 + gates.length := by
      by_contra hge
      obtain ⟨p0, hp0⟩ := L'_nonempty t
      have hmiss := missing_value gates (testIn t p0) (o t) (by omega)
      have hon : value gates (testIn t p0) (o t) = true := by
        rw [← eval_eq_value, hout t _]
        exact decide_eq_true ⟨p0, L'_sub t hp0, (testIn_diag t p0 hp0 p0 (L'_sub t hp0)).mpr rfl⟩
      rw [hon] at hmiss; exact Bool.false_ne_true hmiss.symm
    cases hf : f (o t) with
    | wire u => exact ⟨u, rfl⟩
    | cfalse =>
      obtain ⟨p0, hp0⟩ := L'_nonempty t
      have hF : F01 (testIn t p0) := by
        rcases testIn_F01 t p0 hp0 with h0 | h1; exact Or.inl h0; exact Or.inr (Or.inl h1)
      have h1 := heval (o t) holt (testIn t p0) hF
      rw [hf] at h1
      have hon : value gates (testIn t p0) (o t) = true := by
        rw [← eval_eq_value, hout t _]
        exact decide_eq_true ⟨p0, L'_sub t hp0, (testIn_diag t p0 hp0 p0 (L'_sub t hp0)).mpr rfl⟩
      rw [hon] at h1; exact False.elim (Bool.false_ne_true h1)
    | ctrue =>
      have h1 := heval (o t) holt (offL t) (offL_F01 t)
      rw [hf] at h1
      have hoff : value gates (offL t) (o t) = false := by
        rw [← eval_eq_value, hout t _]
        apply decide_eq_false; rintro ⟨v, hvL, hvnot⟩; exact (of_decide_eq_true hvnot) hvL
      rw [hoff] at h1; exact False.elim (Bool.false_ne_true h1.symm)
  choose o' ho' using ho_wire
  have hgs_bound : 38 ≤ gs.length := by
    refine main L0 (fun _ => rfl) gs o' hgs ?_
    intro t x hx
    have holt : o t < 13 + gates.length := by
      by_contra hge
      obtain ⟨p0, hp0⟩ := L'_nonempty t
      have hmiss := missing_value gates (testIn t p0) (o t) (by omega)
      have hon : value gates (testIn t p0) (o t) = true := by
        rw [← eval_eq_value, hout t _]
        exact decide_eq_true ⟨p0, L'_sub t hp0, (testIn_diag t p0 hp0 p0 (L'_sub t hp0)).mpr rfl⟩
      rw [hon] at hmiss; exact Bool.false_ne_true hmiss.symm
    have h1 := heval (o t) holt x hx
    rw [ho' t] at h1
    change Circuit.eval ⟨gs, o' t⟩ (List.ofFn x) = Circuit.eval ⟨gates, o t⟩ (List.ofFn x) at h1
    rw [h1, hout t x]
  let K := Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)
  have hdrop_eq : Finset.univ.filter (fun i : Fin gates.length =>
      i.val < gates.length ∧ (i = h ∨ i = j ∨ (j < i ∧ 13 + j.val ∈ (gates.get i).inputs))) =
      insert h (insert j K) := by
    ext i
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, i.isLt]
  have hh_ne_j : h ≠ j := ne_of_lt hhj
  have hj_notK : j ∉ K := by simp [K]
  have hh_notK : h ∉ K := by
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro hlt; exact False.elim (not_lt_of_gt hhj hlt)
  rw [hdrop_eq, Finset.card_insert_of_notMem (by simp [hh_ne_j, hh_notK]),
    Finset.card_insert_of_notMem hj_notK] at hlen
  change 40 + K.card ≤ gates.length
  omega

end PEqualNP.Outside.L_meta_1581

theorem PEqualNP.Outside.L_meta_1581 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = true →
    40 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card ≤ gates.length :=
  PEqualNP.Outside.L_meta_1581.main_1581
