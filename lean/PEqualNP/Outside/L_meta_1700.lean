import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1700

open PEqualNP.CircuitLowerBounds

-- One evaluation step of a circuit on a list of wire values.
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wstep_len (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wstep_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD, List.getElem?_append_left hi]

lemma wstep_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (wstep w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [wstep, List.getD]

lemma snoc_lt (T : List ℕ) (a i : ℕ) (h : i < T.length) :
    (T ++ [a]).getD i 0 = T.getD i 0 := by
  simp [List.getD, List.getElem?_append_left h]

lemma snoc_eq (T : List ℕ) (a i : ℕ) (h : i = T.length) : (T ++ [a]).getD i 0 = a := by
  subst h
  simp [List.getD]

lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma ff_ne (b : Bool) (hb : b = false) (h : b = true) {P : Prop} : P := by
  rw [hb] at h
  exact Bool.noConfusion h

-- Pointwise order on wire lists, and monotonicity of AND/OR gate lists.
def LeW (w1 w2 : List Bool) : Prop :=
  w1.length = w2.length ∧ ∀ i, w1.getD i false = true → w2.getD i false = true

lemma le_step (w1 w2 : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : LeW w1 w2) :
    LeW (wstep w1 g) (wstep w2 g) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨by rw [wstep_len, wstep_len, hl], fun i hi => ?_⟩
  by_cases hlt : i < w1.length
  · rw [wstep_lt _ _ _ hlt] at hi
    rw [wstep_lt _ _ _ (by omega)]
    exact hv i hi
  · by_cases heq : i = w1.length
    · rw [wstep_last _ _ _ heq] at hi
      rw [wstep_last _ _ _ (heq.trans hl)]
      rcases hop with hand | hor
      · rw [hand] at hi ⊢
        exact (all_true _ _).mpr (fun j hj => hv j ((all_true _ _).mp hi j hj))
      · rw [hor] at hi ⊢
        obtain ⟨j, hj, hjt⟩ := (any_true _ _).mp hi
        exact (any_true _ _).mpr ⟨j, hj, hv j hjt⟩
    · rw [List.getD_eq_default _ _ (by rw [wstep_len]; omega)] at hi
      exact Bool.noConfusion hi

lemma le_fold (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, LeW w1 w2 → LeW (gs.foldl wstep w1) (gs.foldl wstep w2) := by
  induction gs with
  | nil =>
    intro w1 w2 h
    exact h
  | cons g gs ih =>
    intro w1 w2 h
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (le_step w1 w2 g (hg g (List.mem_cons.mpr (Or.inl rfl))) h)

-- Truth tables as natural numbers: bit k of the table of a wire is its value on input number k.
def gtab (T : List ℕ) (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => Nat.land (T.getD a 0) (T.getD b 0)
  | GateOp.or, [a, b] => Nat.lor (T.getD a 0) (T.getD b 0)
  | _, _ => 0

def okb (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [_, _] => true
  | GateOp.or, [_, _] => true
  | _, _ => false

def tstep (T : List ℕ) (g : Gate) : List ℕ := T ++ [gtab T g]

lemma tb_and (u v k : ℕ) :
    Nat.testBit (Nat.land u v) k = (Nat.testBit u k && (Nat.testBit v k && true)) := by
  show Nat.testBit (u &&& v) k = (Nat.testBit u k && (Nat.testBit v k && true))
  rw [Nat.testBit_and, Bool.and_true]

lemma tb_or (u v k : ℕ) :
    Nat.testBit (Nat.lor u v) k = (Nat.testBit u k || (Nat.testBit v k || false)) := by
  show Nat.testBit (u ||| v) k = (Nat.testBit u k || (Nat.testBit v k || false))
  rw [Nat.testBit_or, Bool.or_false]

lemma ok_op (g : Gate) (h : okb g = true) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> cases op <;>
    first
    | exact ff_ne _ rfl h
    | exact Or.inl rfl
    | exact Or.inr rfl

lemma gtab_spec (T : List ℕ) (g : Gate) (h : okb g = true) (k : ℕ) :
    Nat.testBit (gtab T g) k =
      g.op.eval (g.inputs.map fun i => Nat.testBit (T.getD i 0) k) := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> cases op <;>
    first
    | exact ff_ne _ rfl h
    | exact tb_and (T.getD a 0) (T.getD b 0) k
    | exact tb_or (T.getD a 0) (T.getD b 0) k

def GoodT (w : ℕ → List Bool) (T : List ℕ) : Prop :=
  (∀ k, (w k).length = T.length) ∧ ∀ i k, Nat.testBit (T.getD i 0) k = (w k).getD i false

lemma good_step (w : ℕ → List Bool) (T : List ℕ) (g : Gate) (hg : okb g = true)
    (h : GoodT w T) : GoodT (fun k => wstep (w k) g) (tstep T g) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨fun k => ?_, fun i k => ?_⟩
  · show (wstep (w k) g).length = (T ++ [gtab T g]).length
    rw [wstep_len, List.length_append, List.length_singleton, hl k]
  · show Nat.testBit ((T ++ [gtab T g]).getD i 0) k = (wstep (w k) g).getD i false
    by_cases hlt : i < T.length
    · rw [snoc_lt T _ i hlt, wstep_lt _ _ _ (by rw [hl k]; exact hlt)]
      exact hv i k
    · by_cases heq : i = T.length
      · rw [snoc_eq T _ i heq, wstep_last _ _ _ (by rw [hl k]; exact heq), gtab_spec T g hg k]
        have hfun : (fun j => Nat.testBit (T.getD j 0) k) = fun j => (w k).getD j false :=
          funext (fun j => hv j k)
        rw [hfun]
      · rw [List.getD_eq_default (T ++ [gtab T g]) 0
            (by rw [List.length_append, List.length_singleton]; omega),
          List.getD_eq_default (wstep (w k) g) false (by rw [wstep_len, hl k]; omega)]
        exact Nat.zero_testBit k

lemma good_fold (gs : List Gate) (hg : ∀ g ∈ gs, okb g = true) :
    ∀ (w : ℕ → List Bool) (T : List ℕ), GoodT w T →
      GoodT (fun k => gs.foldl wstep (w k)) (gs.foldl tstep T) := by
  induction gs with
  | nil =>
    intro w T h
    exact h
  | cons g gs ih =>
    intro w T h
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (good_step w T g (hg g (List.mem_cons.mpr (Or.inl rfl))) h)

lemma getD_map_tb (T : List ℕ) (k i : ℕ) :
    (T.map fun t => Nat.testBit t k).getD i false = Nat.testBit (T.getD i 0) k := by
  by_cases h : i < T.length
  · rw [List.getD_eq_getElem (T.map fun t => Nat.testBit t k) false (by simpa using h),
      List.getD_eq_getElem T 0 h, List.getElem_map]
  · rw [List.getD_eq_default (T.map fun t => Nat.testBit t k) false (by simpa using h),
      List.getD_eq_default T 0 (by omega)]
    exact (Nat.zero_testBit k).symm

lemma good_map (T : List ℕ) : GoodT (fun k => T.map fun t => Nat.testBit t k) T :=
  ⟨fun k => by simp, fun i k => (getD_map_tb T k i).symm⟩

lemma eval_tab (gs : List Gate) (o : ℕ) (hg : gs.all okb = true) (T : List ℕ) (k : ℕ) :
    Circuit.eval ⟨gs, o⟩ (T.map fun t => Nat.testBit t k) =
      Nat.testBit ((gs.foldl tstep T).getD o 0) k := by
  have h := good_fold gs (fun g hgm => List.all_eq_true.mp hg g hgm) _ _ (good_map T)
  exact (h.2 o k).symm

lemma eval_le (gs : List Gate) (o : ℕ) (hg : gs.all okb = true) (w1 w2 : List Bool)
    (h : LeW w1 w2) (he : Circuit.eval ⟨gs, o⟩ w1 = true) :
    Circuit.eval ⟨gs, o⟩ w2 = true :=
  (le_fold gs (fun g hgm => ok_op g (List.all_eq_true.mp hg g hgm)) w1 w2 h).2 o he

-- The number coding a list of bits, lowest bit first.
def codeN : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (codeN l)

lemma code_lt : ∀ l : List Bool, codeN l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have ih := code_lt l
    have h2 : codeN (b :: l) = 2 * codeN l + b.toNat := Nat.bit_val b (codeN l)
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    rw [h2, List.length_cons, pow_succ]
    omega

lemma code_bit : ∀ (l : List Bool) (i : ℕ), Nat.testBit (codeN l) i = l.getD i false
  | [], i => by
    first
    | exact Nat.zero_testBit i
    | simp [codeN]
  | b :: l, 0 => by
    rw [List.getD_cons_zero]
    exact Nat.testBit_bit_zero b (codeN l)
  | b :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact (Nat.testBit_bit_succ i b (codeN l)).trans (code_bit l i)

-- The table, over the 2 ^ m numbers k below 2 ^ m, of bit p of k.
def tabX (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    if m = p then 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 else (2 ^ 2 ^ m + 1) * tabX p m

lemma bnd (A t : ℕ) (h : t < A) : A * t + t < A * A := by
  have h1 := Nat.mul_le_mul_left A (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at h1
  omega

lemma tabX_spec (p : ℕ) : ∀ m : ℕ, tabX p m < 2 ^ 2 ^ m ∧
    ∀ k : ℕ, k < 2 ^ m → Nat.testBit (tabX p m) k = Nat.testBit k p := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, fun k hk => ?_⟩
    · show (0 : ℕ) < 2 ^ 2 ^ 0
      exact Nat.two_pow_pos _
    · have hk0 : k = 0 := by simpa using hk
      rw [hk0]
      show Nat.testBit 0 0 = Nat.testBit 0 p
      rw [Nat.zero_testBit, Nat.zero_testBit]
  | succ m ih =>
    obtain ⟨hb, hbits⟩ := ih
    have hA : 0 < 2 ^ 2 ^ m := Nat.two_pow_pos _
    have hpm : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := Nat.two_pow_succ m
    have hpow : 2 ^ 2 ^ (m + 1) = 2 ^ 2 ^ m * 2 ^ 2 ^ m := by
      rw [hpm, Nat.pow_add]
    by_cases hmp : m = p
    · have hdef : tabX p (m + 1) = 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 := by
        rw [tabX, if_pos hmp]
      rw [hdef, ← hmp]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bnd (2 ^ 2 ^ m) (2 ^ 2 ^ m - 1) (by omega)
        rw [hpow]
        omega
      · rw [Nat.testBit_two_pow_mul_add (2 ^ 2 ^ m - 1) hA k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt, Nat.zero_testBit, Nat.testBit_lt_two_pow hlt]
        · rw [if_neg hlt, Nat.testBit_two_pow_sub_one]
          have h1 : Nat.testBit k m = true := by
            have h2 := Nat.testBit_two_pow_add_eq (k - 2 ^ m) m
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega,
              Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ m from by omega)] at h2
            exact h2
          rw [h1]
          exact decide_eq_true (by omega)
    · have hdef : tabX p (m + 1) = 2 ^ 2 ^ m * tabX p m + tabX p m := by
        rw [tabX, if_neg hmp]
        ring
      rw [hdef]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bnd (2 ^ 2 ^ m) (tabX p m) hb
        rw [hpow]
        exact h1
      · rw [Nat.testBit_two_pow_mul_add (tabX p m) hb k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt]
          exact hbits k hlt
        · rw [if_neg hlt, hbits (k - 2 ^ m) (by omega)]
          rcases Nat.lt_or_gt_of_ne hmp with hlt2 | hgt
          · have hle : 2 ^ (m + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hlt2
            rw [Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ p from by omega),
              Nat.testBit_lt_two_pow (show k < 2 ^ p from by omega)]
          · have h2 := Nat.testBit_two_pow_add_gt hgt (k - 2 ^ m)
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega] at h2
            exact h2.symm

-- Inputs: 16 points then 16 lines.
lemma getD_app_left (l1 l2 : List Bool) (i : ℕ) (h : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_app_right (l1 l2 : List Bool) (i : ℕ) :
    (l1 ++ l2).getD (l1.length + i) false = l2.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  first
  | rw [List.getElem_ofFn]
  | simp

lemma inp_len (x y : Fin 16 → Bool) : (List.ofFn x ++ List.ofFn y).length = 32 := by
  simp

lemma inp_x (x y : Fin 16 → Bool) (i : ℕ) (h : i < 16) :
    (List.ofFn x ++ List.ofFn y).getD i false = x ⟨i, h⟩ :=
  (getD_app_left _ _ i (by simpa using h)).trans (ofFn_getD x i h)

lemma inp_y (x y : Fin 16 → Bool) (i : ℕ) (h : i < 16) :
    (List.ofFn x ++ List.ofFn y).getD (16 + i) false = y ⟨i, h⟩ := by
  have e := getD_app_right (List.ofFn x) (List.ofFn y) i
  rw [List.length_ofFn] at e
  exact e.trans (ofFn_getD y i h)

lemma inp_true (x y : Fin 16 → Bool) (i : ℕ)
    (h : (List.ofFn x ++ List.ofFn y).getD i false = true) :
    (∃ hi : i < 16, x ⟨i, hi⟩ = true) ∨
      (∃ j, ∃ hj : j < 16, i = 16 + j ∧ y ⟨j, hj⟩ = true) := by
  by_cases h1 : i < 16
  · left
    exact ⟨h1, (inp_x x y i h1).symm.trans h⟩
  · by_cases h2 : i < 32
    · right
      have h3 : 16 + (i - 16) = i := by omega
      have h4 : i - 16 < 16 := by omega
      refine ⟨i - 16, h4, h3.symm, ?_⟩
      have h5 := inp_y x y (i - 16) h4
      rw [h3] at h5
      exact h5.symm.trans h
    · rw [List.getD_eq_default _ _ (by rw [inp_len]; omega)] at h
      exact Bool.noConfusion h

-- The concrete data.
def gsL : List Gate := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 62] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 80] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 86] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [94, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 104] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 106] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [109, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [111, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [112, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [114, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [115, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [117, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 120] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 122] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 124] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 126] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [61, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [128, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [129, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [130, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [131, 83] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [132, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [133, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [134, 101] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [135, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [136, 105] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [137, 107] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [138, 121] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [139, 123] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [140, 125] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [141, 127] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [143, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [153, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [158, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 145] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 158] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [163, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [173, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [178, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 165] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [183, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [184, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [186, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [187, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [189, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [190, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [192, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [193, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [196, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [194, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [198, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [199, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [203, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [204, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [206, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [207, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [209, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [210, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [212, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [213, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [216, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [214, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [218, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [219, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [159, 161] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [223, 162] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 156] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [225, 179] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [226, 181] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 182] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 176] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [229, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [230, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [231, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 196] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [233, 219] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [234, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 216] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [238, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [239, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [245, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [249, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [253, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [255, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 256] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [259, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 261] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [263, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [264, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [265, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 266] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [268, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [269, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [270, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 271] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [273, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [274, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [275, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 276] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [278, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [279, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [280, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 281] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [283, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [284, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [285, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 286] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [288, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [289, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [290, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 291] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [293, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [294, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [295, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 296] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [298, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [299, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [300, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 301] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [303, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [304, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [305, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 306] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [308, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [309, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [310, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 311] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [313, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [314, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [315, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 316] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [242, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [318, 252] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [319, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [320, 262] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [321, 267] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [322, 272] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [323, 277] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [324, 282] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [325, 287] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [326, 292] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [327, 297] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [328, 302] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [329, 307] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [330, 312] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [331, 317] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 332] }]

def IncL : List (ℕ × ℕ) := [(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)]

def ALLT : ℕ := 2 ^ 65536 - 1

def XTab (p : ℕ) : ℕ := tabX p 16

def ytab (l : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => ALLT
  | q :: L => if q.2 = l then Nat.land (Nat.xor ALLT (XTab q.1)) (ytab l L) else ytab l L

def YTab (l : ℕ) : ℕ := ytab l IncL

def T0L : List ℕ := (List.range 16).map XTab ++ (List.range 16).map YTab

def hotT (i : ℕ) : ℕ :=
  IncL.foldr (fun q acc => 2 * acc + (if i = q.1 ∨ i = 16 + q.2 then 1 else 0)) 0

def THL : List ℕ := (List.range 32).map hotT

lemma len302 : gsL.length = 302 := by decide +kernel

lemma reads_back : PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) ⟨gsL, 333⟩ := by
  unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack
  decide +kernel

lemma line_deg : HasLineDegree (16 + 16) (Finset.Ico 16 (16 + 16)) ⟨gsL, 333⟩ 3 := by
  decide +kernel

lemma gs_ok : gsL.all okb = true := by decide +kernel

lemma inc_len : IncL.length = 64 := by decide +kernel

lemma inc_bound : ∀ q ∈ IncL, q.1 < 16 := by decide +kernel

lemma TH_len : THL.length = 32 := by decide +kernel

lemma T0_len : T0L.length = 32 := by decide +kernel

lemma T0_x : ∀ p < 16, T0L.getD p 0 = XTab p := by decide +kernel

lemma T0_y : ∀ l < 16, T0L.getD (16 + l) 0 = YTab l := by decide +kernel

lemma hot_spec : ∀ j < 64, ∀ i < 32, Nat.testBit (THL.getD i 0) j = true →
    (i = (IncL.getD j (0, 0)).1 ∨ i = 16 + (IncL.getD j (0, 0)).2) := by
  decide +kernel

lemma certH : (gsL.foldl tstep THL).getD 333 0 = 2 ^ 64 - 1 := by decide +kernel

lemma cert0 : (gsL.foldl tstep T0L).getD 333 0 = 0 := by decide +kernel

lemma XTab_spec (p k : ℕ) (hk : k < 65536) : Nat.testBit (XTab p) k = Nat.testBit k p :=
  (tabX_spec p 16).2 k (by
    have h16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
    omega)

lemma all_bit (k : ℕ) (hk : k < 65536) : Nat.testBit ALLT k = true := by
  show Nat.testBit (2 ^ 65536 - 1) k = true
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hk

lemma and_xor_bit (A X R k : ℕ) (hA : Nat.testBit A k = true) (hX : Nat.testBit X k = false)
    (hR : Nat.testBit R k = true) : Nat.testBit (Nat.land (Nat.xor A X) R) k = true := by
  show Nat.testBit ((A ^^^ X) &&& R) k = true
  rw [Nat.testBit_and, Nat.testBit_xor, hA, hX, hR] <;> rfl

lemma ytab_true (k : ℕ) (hk : k < 65536) (l : ℕ) : ∀ L : List (ℕ × ℕ),
    (∀ q ∈ L, q.2 = l → Nat.testBit k q.1 = false) → Nat.testBit (ytab l L) k = true := by
  intro L
  induction L with
  | nil =>
    intro _
    exact all_bit k hk
  | cons q L ih =>
    intro h
    have ih' := ih (fun q' hq' => h q' (List.mem_cons.mpr (Or.inr hq')))
    show Nat.testBit (if q.2 = l then Nat.land (Nat.xor ALLT (XTab q.1)) (ytab l L)
      else ytab l L) k = true
    by_cases hq : q.2 = l
    · rw [if_pos hq]
      exact and_xor_bit _ _ _ k (all_bit k hk)
        ((XTab_spec q.1 k hk).trans (h q (List.mem_cons.mpr (Or.inl rfl)) hq)) ih'
    · rw [if_neg hq]
      exact ih'

lemma eval_ge (x y : Fin 16 → Bool) (p l : Fin 16) (hmem : ((p : ℕ), (l : ℕ)) ∈ IncL)
    (hx : x p = true) (hy : y l = true) :
    Circuit.eval ⟨gsL, 333⟩ (List.ofFn x ++ List.ofFn y) = true := by
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hmem
  have hj64 : j < 64 := lt_of_lt_of_eq hj inc_len
  have hget : IncL.getD j (0, 0) = ((p : ℕ), (l : ℕ)) := by
    rw [List.getD_eq_getElem _ _ hj]
    exact hjeq
  have hle : LeW (THL.map fun t => Nat.testBit t j) (List.ofFn x ++ List.ofFn y) := by
    refine ⟨by rw [List.length_map, TH_len, inp_len], fun i hi => ?_⟩
    rw [getD_map_tb] at hi
    by_cases hi32 : i < 32
    · have h := hot_spec j hj64 i hi32 hi
      rw [hget] at h
      rcases h with h | h
      · have h' : i = (p : ℕ) := h
        rw [h', inp_x x y p.val p.isLt]
        exact hx
      · have h' : i = 16 + (l : ℕ) := h
        rw [h', inp_y x y l.val l.isLt]
        exact hy
    · rw [List.getD_eq_default _ _ (by rw [TH_len]; omega), Nat.zero_testBit] at hi
      exact Bool.noConfusion hi
  refine eval_le gsL 333 gs_ok _ _ hle ?_
  rw [eval_tab gsL 333 gs_ok THL j, certH, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj64

lemma eval_le0 (x y : Fin 16 → Bool)
    (hF : ¬ ∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ IncL ∧ x p = true ∧ y l = true) :
    Circuit.eval ⟨gsL, 333⟩ (List.ofFn x ++ List.ofFn y) = false := by
  have hk : codeN (List.ofFn x) < 65536 := by
    have h := code_lt (List.ofFn x)
    rw [List.length_ofFn] at h
    have h16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
    omega
  have hbit : ∀ (i : ℕ) (hi : i < 16), Nat.testBit (codeN (List.ofFn x)) i = x ⟨i, hi⟩ := by
    intro i hi
    rw [code_bit, ofFn_getD x i hi]
  have hle : LeW (List.ofFn x ++ List.ofFn y)
      (T0L.map fun t => Nat.testBit t (codeN (List.ofFn x))) := by
    refine ⟨by rw [List.length_map, T0_len, inp_len], fun i hi => ?_⟩
    rw [getD_map_tb]
    rcases inp_true x y i hi with ⟨hi16, hxi⟩ | ⟨j, hj, hij, hyj⟩
    · rw [T0_x i hi16, XTab_spec i _ hk, hbit i hi16]
      exact hxi
    · rw [hij, T0_y j hj]
      refine ytab_true _ hk j IncL (fun q hq hq2 => ?_)
      obtain ⟨a, b⟩ := q
      have ha : a < 16 := inc_bound (a, b) hq
      have hb : b = j := hq2
      show Nat.testBit (codeN (List.ofFn x)) a = false
      rw [hbit a ha]
      cases hxa : x ⟨a, ha⟩
      · rfl
      · exfalso
        exact hF ⟨⟨a, ha⟩, ⟨j, hj⟩, (show (a, j) ∈ IncL from by rw [← hb]; exact hq), hxa, hyj⟩
  cases he : Circuit.eval ⟨gsL, 333⟩ (List.ofFn x ++ List.ofFn y)
  · rfl
  · exfalso
    have h := eval_le gsL 333 gs_ok _ _ hle he
    rw [eval_tab gsL 333 gs_ok T0L _, cert0, Nat.zero_testBit] at h
    exact Bool.noConfusion h

lemma key (x y : Fin 16 → Bool) :
    Circuit.eval ⟨gsL, 333⟩ (List.ofFn x ++ List.ofFn y) =
      decide (∃ p : Fin 16, ∃ l : Fin 16,
        ((p : ℕ), (l : ℕ)) ∈ IncL ∧ x p = true ∧ y l = true) := by
  by_cases hF : ∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ IncL ∧ x p = true ∧ y l = true
  · have h1 : Circuit.eval ⟨gsL, 333⟩ (List.ofFn x ++ List.ofFn y) = true := by
      obtain ⟨p, l, hmem, hx, hy⟩ := hF
      exact eval_ge x y p l hmem hx hy
    rw [h1]
    exact (decide_eq_true hF).symm
  · rw [eval_le0 x y hF]
    exact (decide_eq_false hF).symm

theorem main_aux : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 62] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 80] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 86] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [94, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 104] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 106] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [109, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [111, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [112, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [114, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [115, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [117, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 120] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 122] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 124] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 126] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [61, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [128, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [129, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [130, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [131, 83] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [132, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [133, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [134, 101] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [135, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [136, 105] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [137, 107] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [138, 121] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [139, 123] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [140, 125] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [141, 127] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [143, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [153, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [158, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 145] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 158] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [163, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [173, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [178, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 165] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [183, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [184, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [186, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [187, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [189, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [190, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [192, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [193, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [196, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [194, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [198, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [199, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [203, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [204, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [206, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [207, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [209, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [210, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [212, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [213, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [216, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [214, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [218, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [219, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [159, 161] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [223, 162] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 156] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [225, 179] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [226, 181] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 182] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 176] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [229, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [230, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [231, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 196] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [233, 219] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [234, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 216] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [238, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [239, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [245, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [249, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [253, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [255, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 256] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [259, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 261] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [263, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [264, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [265, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 266] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [268, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [269, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [270, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 271] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [273, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [274, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [275, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 276] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [278, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [279, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [280, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 281] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [283, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [284, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [285, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 286] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [288, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [289, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [290, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 291] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [293, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [294, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [295, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 296] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [298, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [299, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [300, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 301] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [303, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [304, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [305, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 306] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [308, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [309, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [310, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 311] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [313, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [314, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [315, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 316] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [242, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [318, 252] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [319, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [320, 262] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [321, 267] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [322, 272] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [323, 277] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [324, 282] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [325, 287] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [326, 292] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [327, 297] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [328, 302] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [329, 307] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [330, 312] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [331, 317] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 332] }], output := 333 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 302 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (16 + 16) (Finset.Ico 16 (16 + 16)) C 3 ∧
  ∀ (x y : Fin 16 → Bool), C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) := by
  intro C hC
  subst hC
  exact ⟨len302, reads_back, line_deg, key⟩

end PEqualNP.Outside.L_meta_1700

theorem PEqualNP.Outside.L_meta_1700 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 62] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 80] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 86] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [94, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 104] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 106] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [109, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [111, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [112, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [114, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [115, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [117, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 120] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 122] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 124] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 126] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [61, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [128, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [129, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [130, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [131, 83] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [132, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [133, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [134, 101] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [135, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [136, 105] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [137, 107] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [138, 121] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [139, 123] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [140, 125] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [141, 127] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [143, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [153, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [158, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 145] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 158] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [163, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [173, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [178, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 165] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [183, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [184, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [186, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [187, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [189, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [190, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [192, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [193, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [196, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [194, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [198, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [199, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [203, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [204, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [206, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [207, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [209, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [210, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [212, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [213, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [216, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [214, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [218, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [219, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [159, 161] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [223, 162] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 156] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [225, 179] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [226, 181] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 182] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 176] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [229, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [230, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [231, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 196] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [233, 219] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [234, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 216] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [238, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [239, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [245, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [249, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [253, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [255, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 256] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [259, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 261] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [263, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [264, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [265, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 266] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [268, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [269, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [270, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 271] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [273, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [274, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [275, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 276] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [278, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [279, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [280, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 281] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [283, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [284, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [285, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 286] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [288, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [289, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [290, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 291] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [293, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [294, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [295, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 296] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [298, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [299, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [300, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 301] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [303, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [304, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [305, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 306] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [308, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [309, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [310, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 311] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [313, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [314, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [315, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 316] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [242, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [318, 252] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [319, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [320, 262] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [321, 267] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [322, 272] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [323, 277] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [324, 282] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [325, 287] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [326, 292] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [327, 297] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [328, 302] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [329, 307] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [330, 312] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [331, 317] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 332] }], output := 333 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 302 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (16 + 16) (Finset.Ico 16 (16 + 16)) C 3 ∧
  ∀ (x y : Fin 16 → Bool), C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) :=
  PEqualNP.Outside.L_meta_1700.main_aux
