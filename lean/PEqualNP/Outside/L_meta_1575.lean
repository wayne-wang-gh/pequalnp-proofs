import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1575

open PEqualNP.CircuitLowerBounds

abbrev P := Fin 13

def line (t : P) : Finset P := {t, t + 1, t + 3, t + 9}
def LS : Finset P := {4, 10, 12}
def MS : Finset P := {1, 5, 11}

def coline (t : P) : P → Bool := fun v => decide (v ∉ line t)

def testInp (t y : P) : P → Bool :=
  fun v => decide (v = y ∨ (t ∈ LS ∧ y ≠ 0 ∧ v = 1) ∨ (t ∈ MS ∧ y ≠ 1 ∧ v = 0))

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

def val (gates : List Gate) (w : ℕ) (x : P → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn x)

lemma val_input (gates : List Gate) (p : P) (x : P → Bool) :
    val gates p.val x = x p := by
  change (run gates (List.ofFn x)).getD p.val false = x p
  have hp : p.val < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp only [List.getElem_ofFn, Fin.eta]

lemma val_gate (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val) :
    val gates (13 + i.val) x =
      (gates.get i).op.eval ((gates.get i).inputs.map fun a => val gates a x) := by
  let j := i.val
  have hj : j < gates.length := i.isLt
  let g := gates[j]
  let earlier := run (gates.take j) (List.ofFn x)
  have plen : earlier.length = 13 + j := by
    simp [earlier, run_length, j]
  have split : run gates (List.ofFn x) = run (g :: gates.drop (j + 1)) earlier := by
    rw [run_split gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (a : ℕ) (ha : a < 13 + j) : earlier.getD a false = val gates a x := by
    change earlier.getD a false = (run gates (List.ofFn x)).getD a false
    rw [split]
    exact (run_getD _ earlier a (by simpa only [plen] using ha)).symm
  change (run gates (List.ofFn x)).getD (13 + j) false =
    g.op.eval (g.inputs.map fun a => val gates a x)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact read a (hwf a ha)

lemma val_mono (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (x y : P → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w : ℕ, w < 13 + gates.length → val gates w x = true → val gates w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hx
    by_cases hw : w < 13
    · let p : P := ⟨w, hw⟩
      have hp : p.val = w := rfl
      rw [← hp, val_input] at hx ⊢
      exact hxy p hx
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hi : 13 + i.val = w := by change 13 + (w - 13) = w; omega
      rw [← hi, val_gate gates i x (hWF i).2] at hx
      rw [← hi, val_gate gates i y (hWF i).2]
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

lemma val_or_iff (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.or) :
    val gates (13 + i.val) x = true ↔ ∃ a ∈ (gates.get i).inputs, val gates a x = true := by
  rw [val_gate gates i x hwf, hop]
  simp [GateOp.eval]

lemma val_or_false (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.or)
    (hf : val gates (13 + i.val) x = false) {a : ℕ} (ha : a ∈ (gates.get i).inputs) :
    val gates a x = false := by
  cases h : val gates a x with
  | false => rfl
  | true =>
    have ht : val gates (13 + i.val) x = true := (val_or_iff gates i x hwf hop).mpr ⟨a, ha, h⟩
    rw [hf] at ht
    exact Bool.noConfusion ht

lemma val_and_true (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.and)
    (ht : val gates (13 + i.val) x = true) {a : ℕ} (ha : a ∈ (gates.get i).inputs) :
    val gates a x = true := by
  rw [val_gate gates i x hwf] at ht
  simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at ht
  exact ht a ha

lemma val_and_false_exists (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.and)
    (hf : val gates (13 + i.val) x = false) :
    ∃ a ∈ (gates.get i).inputs, val gates a x = false := by
  rw [val_gate gates i x hwf, hop] at hf
  simpa only [GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id_eq, Bool.not_eq_true] using hf

def CutRespect (gates : List Gate) (t : P) (g : Fin gates.length) (X : Finset P) : Prop :=
  ∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
    val gates (13 + i.val) (coline t) = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ line t, ∀ y' ∈ line t,
      (val gates a (testInp t y) = true ∨ val gates b (testInp t y) = true) →
      (val gates a (testInp t y') = true ∨ val gates b (testInp t y') = true) →
      (y ∈ X ↔ y' ∈ X)

def Merges (gates : List Gate) (t : P) (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧
  val gates (13 + g.val) (coline t) = false ∧
  ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧
    ∃ r ∈ line t, ∃ r' ∈ line t,
      val gates w1 (testInp t r) = true ∧ val gates w2 (testInp t r') = true ∧
      ∃ X : Finset P, r ∈ X ∧ r' ∉ X ∧ CutRespect gates t g X

def OrReach (gates : List Gate) (start target : ℕ) : Prop :=
  ∀ S : Set ℕ, start ∈ S →
    (∀ i : Fin gates.length, 13 + i.val ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) →
    target ∈ S

lemma orReach_refl (gates : List Gate) (w : ℕ) : OrReach gates w w :=
  fun _ h _ => h

lemma orReach_trans (gates : List Gate) {u v w : ℕ}
    (h1 : OrReach gates u v) (h2 : OrReach gates v w) : OrReach gates u w :=
  fun S hu hstep => h2 S (h1 S hu hstep) hstep

lemma orReach_step (gates : List Gate) (i : Fin gates.length)
    (hop : (gates.get i).op = GateOp.or) {a : ℕ} (ha : a ∈ (gates.get i).inputs) :
    OrReach gates (13 + i.val) a :=
  fun _ hi hstep => hstep i hi hop a ha

lemma orReach_le (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    {u v : ℕ} (h : OrReach gates u v) : v ≤ u :=
  h {w | w ≤ u} (by simp) fun i hi _ a ha => le_trans (le_of_lt ((hWF i).2 a ha)) hi

lemma orReach_false (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    {u v : ℕ} (h : OrReach gates u v) (x : P → Bool)
    (hu : val gates u x = false) : val gates v x = false :=
  h {w | val gates w x = false} hu fun i hi hop _ ha =>
    val_or_false gates i x (hWF i).2 hop hi ha

lemma orReach_find_stop (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (x : P → Bool) :
    ∀ w : ℕ, w < 13 + gates.length → val gates w x = true →
      (∃ v : P, OrReach gates w v.val ∧ x v = true) ∨
      (∃ z : Fin gates.length, (gates.get z).op = GateOp.and ∧
        OrReach gates w (13 + z.val) ∧ val gates (13 + z.val) x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hval
    by_cases hw : w < 13
    · let p : P := ⟨w, hw⟩
      have hp : p.val = w := rfl
      rw [← hp, val_input] at hval
      exact Or.inl ⟨p, orReach_refl gates w, hval⟩
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hi : 13 + i.val = w := by change 13 + (w - 13) = w; omega
      obtain ⟨hop | hop, _⟩ := hG (gates.get i) (List.get_mem _ _)
      · exact Or.inr ⟨i, hop, hi ▸ orReach_refl gates w, hi.symm ▸ hval⟩
      · rw [← hi] at hval
        obtain ⟨a, ha, hva⟩ := (val_or_iff gates i x (hWF i).2 hop).mp hval
        have hlt_a := (hWF i).2 a ha
        have hstep : OrReach gates w a := hi ▸ orReach_step gates i hop ha
        rcases ih a (by omega) (by omega) hva with ⟨v, hrv, hxv⟩ | ⟨z, hzop, hrz, hvz⟩
        · exact Or.inl ⟨v, orReach_trans gates hstep hrv, hxv⟩
        · exact Or.inr ⟨z, hzop, orReach_trans gates hstep hrz, hvz⟩

lemma testInp_in_line_eq : ∀ t : P, t ∈ LS ∨ t ∈ MS → ∀ y ∈ line t, ∀ v ∈ line t,
    testInp t y v = true → v = y := by decide

lemma testInp_base_le_coline_LM : ∀ l ∈ LS, ∀ m ∈ MS, ∀ v : P,
    testInp l 0 v = true → coline m v = true := by decide

lemma testInp_base_le_coline_ML : ∀ m ∈ MS, ∀ l ∈ LS, ∀ v : P,
    testInp m 1 v = true → coline l v = true := by decide

lemma testInp_other_le_coline_LL : ∀ l1 ∈ LS, ∀ l2 ∈ LS, l1 ≠ l2 → ∀ y ∈ line l1, y ≠ 0 → ∀ v : P,
    testInp l1 y v = true → coline l2 v = true := by decide

lemma testInp_other_le_coline_MM : ∀ m1 ∈ MS, ∀ m2 ∈ MS, m1 ≠ m2 → ∀ y ∈ line m1, y ≠ 1 → ∀ v : P,
    testInp m1 y v = true → coline m2 v = true := by decide

lemma inter_LM_card : ∀ l ∈ LS, ∀ m ∈ MS, (line l ∩ line m).card = 1 := by decide
lemma inter_ML_card : ∀ m ∈ MS, ∀ l ∈ LS, (line m ∩ line l).card = 1 := by decide
lemma line_sdiff_base_L : ∀ l ∈ LS, (line l \ {0}).card = 3 := by decide
lemma line_sdiff_base_M : ∀ m ∈ MS, (line m \ {1}).card = 3 := by decide

lemma wire_same_comp (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (t : P) (ht : t ∈ LS ∨ t ∈ MS) (g : Fin gates.length) (X : Finset P)
    (hcut : CutRespect gates t g X) :
    ∀ w : ℕ, w < 13 + g.val → val gates w (coline t) = false →
      ∀ y ∈ line t, ∀ y' ∈ line t,
        val gates w (testInp t y) = true → val gates w (testInp t y') = true →
        (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hcol y hy y' hy' hvy hvy'
    by_cases hw : w < 13
    · let v : P := ⟨w, hw⟩
      have hv : v.val = w := rfl
      rw [← hv, val_input] at hcol hvy hvy'
      have hvl : v ∈ line t := by simpa [coline] using hcol
      have heq1 := testInp_in_line_eq t ht y hy v hvl hvy
      have heq2 := testInp_in_line_eq t ht y' hy' v hvl hvy'
      rw [← heq1, ← heq2]
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hi : 13 + i.val = w := by change 13 + (w - 13) = w; omega
      have hig : i < g := by change i.val < g.val; omega
      obtain ⟨hop | hop, hlen⟩ := hG (gates.get i) (List.get_mem _ _)
      · rw [← hi] at hcol hvy hvy'
        obtain ⟨a, ha, hfa⟩ := val_and_false_exists gates i (coline t) (hWF i).2 hop hcol
        have hlt_a := (hWF i).2 a ha
        have hya := val_and_true gates i (testInp t y) (hWF i).2 hop hvy ha
        have hya' := val_and_true gates i (testInp t y') (hWF i).2 hop hvy' ha
        exact ih a (by omega) (by omega) hfa y hy y' hy' hya hya'
      · have hpos := (hWF i).1
        match hlist : (gates.get i).inputs with
        | [] => rw [hlist] at hpos; simp at hpos
        | [a] =>
          rw [← hi] at hcol hvy hvy'
          have hmem : a ∈ (gates.get i).inputs := by rw [hlist]; simp
          have hlt_a := (hWF i).2 a hmem
          have hfa := val_or_false gates i (coline t) (hWF i).2 hop hcol hmem
          have hya : val gates a (testInp t y) = true := by
            obtain ⟨c, hc, hvc⟩ := (val_or_iff gates i (testInp t y) (hWF i).2 hop).mp hvy
            rw [hlist] at hc; simp at hc; rwa [← hc]
          have hya' : val gates a (testInp t y') = true := by
            obtain ⟨c, hc, hvc⟩ := (val_or_iff gates i (testInp t y') (hWF i).2 hop).mp hvy'
            rw [hlist] at hc; simp at hc; rwa [← hc]
          exact ih a (by omega) (by omega) hfa y hy y' hy' hya hya'
        | [a, b] =>
          rw [← hi] at hcol hvy hvy'
          have hyab : val gates a (testInp t y) = true ∨ val gates b (testInp t y) = true := by
            obtain ⟨c, hc, hvc⟩ := (val_or_iff gates i (testInp t y) (hWF i).2 hop).mp hvy
            rw [hlist] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact Or.inl hvc
            · exact Or.inr hvc
          have hyab' : val gates a (testInp t y') = true ∨ val gates b (testInp t y') = true := by
            obtain ⟨c, hc, hvc⟩ := (val_or_iff gates i (testInp t y') (hWF i).2 hop).mp hvy'
            rw [hlist] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact Or.inl hvc
            · exact Or.inr hvc
          exact hcut i hig hop hcol a b hlist y hy y' hy' hyab hyab'
        | _ :: _ :: _ :: _ => rw [hlist] at hlen; simp at hlen

lemma mem_of_card_three {α : Type*} [DecidableEq α] {S : Finset α} (hcard : S.card = 3)
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

lemma two_ordered_of_one_lt {α : Type*} [LinearOrder α] {S : Finset α} (h : 1 < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a < b := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact ⟨x, hx, y, hy, hlt⟩
  · exact ⟨y, hy, x, hx, hlt⟩

lemma three_ordered_of_two_lt {α : Type*} [LinearOrder α] {S : Finset α} (h : 2 < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a < b ∧ b < c := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  have h1 : 1 < (S.erase x).card := by
    rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y, hy, z, hz, hyz⟩ := two_ordered_of_one_lt h1
  have hyS : y ∈ S := (Finset.mem_erase.mp hy).2
  have hzS : z ∈ S := (Finset.mem_erase.mp hz).2
  have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
  have hxz : x ≠ z := (Finset.mem_erase.mp hz).1.symm
  rcases lt_or_gt_of_ne hxy with h1 | h1
  · exact ⟨x, hx, y, hyS, z, hzS, h1, hyz⟩
  · rcases lt_or_gt_of_ne hxz with h2 | h2
    · exact ⟨y, hyS, x, hx, z, hzS, h1, h2⟩
    · exact ⟨y, hyS, z, hzS, x, hx, hyz, h2⟩

lemma ne_base_of_or_true (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (t base : P) (g : Fin gates.length) (w1 w2 : ℕ) (r : P)
    (hop : (gates.get g).op = GateOp.or) (hin : (gates.get g).inputs = [w1, w2])
    (hb : val gates (13 + g.val) (testInp t base) = false)
    (hvr : val gates w1 (testInp t r) = true ∨ val gates w2 (testInp t r) = true) :
    r ≠ base := by
  intro hreq
  rw [hreq] at hvr
  have ht : val gates (13 + g.val) (testInp t base) = true := by
    rw [val_or_iff gates g _ (hWF g).2 hop, hin]
    rcases hvr with h | h
    · exact ⟨w1, by simp, h⟩
    · exact ⟨w2, by simp, h⟩
  rw [hb] at ht
  exact Bool.noConfusion ht

lemma card_le_two_of_merges (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (t base : P) (hcard3 : (line t \ {base}).card = 3)
    (S : Finset (Fin gates.length))
    (hM : ∀ g ∈ S, Merges gates t g ∧ val gates (13 + g.val) (testInp t base) = false) :
    S.card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨g1, hg1, g2, hg2, g3, hg3, h12, h23⟩ := three_ordered_of_two_lt hgt
  have h13 : g1 < g3 := lt_trans h12 h23
  obtain ⟨⟨hop1, hcol1, w11, w12, hin1, r1, hr1, r1', hr1', hv11, hv12, X1, hr1X, hr1'X, _⟩, hb1⟩ := hM g1 hg1
  obtain ⟨⟨hop2, hcol2, w21, w22, hin2, r2, hr2, r2', hr2', hv21, hv22, X2, hr2X, hr2'X, hcut2⟩, hb2⟩ := hM g2 hg2
  obtain ⟨⟨hop3, _, w31, w32, hin3, r3, hr3, r3', hr3', hv31, hv32, X3, hr3X, hr3'X, hcut3⟩, hb3⟩ := hM g3 hg3
  have hr1_ne : r1 ≠ base := ne_base_of_or_true gates hWF t base g1 w11 w12 r1 hop1 hin1 hb1 (Or.inl hv11)
  have hr1'_ne : r1' ≠ base := ne_base_of_or_true gates hWF t base g1 w11 w12 r1' hop1 hin1 hb1 (Or.inr hv12)
  have hr2_ne : r2 ≠ base := ne_base_of_or_true gates hWF t base g2 w21 w22 r2 hop2 hin2 hb2 (Or.inl hv21)
  have hr2'_ne : r2' ≠ base := ne_base_of_or_true gates hWF t base g2 w21 w22 r2' hop2 hin2 hb2 (Or.inr hv22)
  have hr3_ne : r3 ≠ base := ne_base_of_or_true gates hWF t base g3 w31 w32 r3 hop3 hin3 hb3 (Or.inl hv31)
  have hr3'_ne : r3' ≠ base := ne_base_of_or_true gates hWF t base g3 w31 w32 r3' hop3 hin3 hb3 (Or.inr hv32)
  have h1neq : r1 ≠ r1' := fun h => hr1'X (h ▸ hr1X)
  have h2neq : r2 ≠ r2' := fun h => hr2'X (h ▸ hr2X)
  have h1_X2 : r1 ∈ X2 ↔ r1' ∈ X2 := hcut2 g1 h12 hop1 hcol1 w11 w12 hin1 r1 hr1 r1' hr1' (Or.inl hv11) (Or.inr hv12)
  have h1_X3 : r1 ∈ X3 ↔ r1' ∈ X3 := hcut3 g1 h13 hop1 hcol1 w11 w12 hin1 r1 hr1 r1' hr1' (Or.inl hv11) (Or.inr hv12)
  have h2_X3 : r2 ∈ X3 ↔ r2' ∈ X3 := hcut3 g2 h23 hop2 hcol2 w21 w22 hin2 r2 hr2 r2' hr2' (Or.inl hv21) (Or.inr hv22)
  have hc_ex : ∃ c ∈ line t \ {base}, c ≠ r1 ∧ c ≠ r1' ∧ (c = r2 ∨ c = r2') := by
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
  have hall := mem_of_card_three hcard3
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
  have hsame (x : P) (hx : x ∈ line t \ {base}) : x ∈ X3 ↔ r1 ∈ X3 := by
    rcases hall x hx with rfl | rfl | rfl
    · rfl
    · exact h1_X3.symm
    · exact hc_X3
  have h3a := hsame r3 (Finset.mem_sdiff.mpr ⟨hr3, by simp [hr3_ne]⟩)
  have h3b := hsame r3' (Finset.mem_sdiff.mpr ⟨hr3', by simp [hr3'_ne]⟩)
  exact hr3'X (h3b.mpr (h3a.mp hr3X))

lemma side_bound (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (A B : Finset P) (baseA baseB : P)
    (h_sub : ∀ a ∈ A, a ∈ LS ∨ a ∈ MS)
    (h_base_le : ∀ a ∈ A, ∀ b ∈ B, ∀ v : P, testInp a baseA v = true → coline b v = true)
    (h_other_A : ∀ a1 ∈ A, ∀ a2 ∈ A, a1 ≠ a2 → ∀ y ∈ line a1, y ≠ baseA → ∀ v : P,
      testInp a1 y v = true → coline a2 v = true)
    (h_other_B : ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → ∀ y ∈ line b1, y ≠ baseB → ∀ v : P,
      testInp b1 y v = true → coline b2 v = true)
    (h_inter : ∀ a ∈ A, ∀ b ∈ B, (line a ∩ line b).card = 1)
    (h_card3 : ∀ a ∈ A, (line a \ {baseA}).card = 3)
    (K J : Finset (Fin gates.length))
    (hK_side : ∀ g ∈ K, ∃ a ∈ A, ∃ b ∈ B, Merges gates a g ∧ Merges gates b g)
    (hJ_side : ∀ z : Fin gates.length, (gates.get z).op = GateOp.and →
      ∀ g : Fin gates.length, ∀ a ∈ A, ∀ b ∈ B,
        Merges gates a g → Merges gates b g →
        OrReach gates (13 + g.val) (13 + z.val) →
        val gates (13 + z.val) (coline a) = false →
        val gates (13 + z.val) (coline b) = false →
        (∃ p ∈ line a, p ∉ line b ∧ val gates (13 + z.val) (testInp a p) = true) →
        z ∈ J) :
    let JA (a : P) := J.filter (fun z => val gates (13 + z.val) (coline a) = false ∧
      ∃ p ∈ line a, p ≠ baseA ∧ val gates (13 + z.val) (testInp a p) = true)
    let JB (b : P) := J.filter (fun z => val gates (13 + z.val) (coline b) = false ∧
      ∃ s ∈ line b, s ≠ baseB ∧ val gates (13 + z.val) (testInp b s) = true)
    let JA_all := A.biUnion JA
    let JB_all := B.biUnion JB
    K.card ≤ 2 * (JA_all \ JB_all).card + (JA_all ∩ JB_all).card := by
  classical
  intro JA JB JA_all JB_all
  let KA (a : P) := K.filter (fun g => Merges gates a g)
  have hbase_false (g : Fin gates.length) (a : P) (ha : a ∈ A) (b : P) (hb : b ∈ B)
      (hMb : Merges gates b g) : val gates (13 + g.val) (testInp a baseA) = false := by
    cases h : val gates (13 + g.val) (testInp a baseA) with
    | false => rfl
    | true =>
      have ht := val_mono gates hG hWF _ _ (h_base_le a ha b hb) (13 + g.val) (by omega) h
      rw [hMb.2.1] at ht
      exact Bool.noConfusion ht
  have hKA_disj : Set.PairwiseDisjoint (A : Set P) KA := by
    intro a1 ha1 a2 ha2 hne
    show Disjoint (KA a1) (KA a2)
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have hgK : g ∈ K := (Finset.mem_filter.mp hg1).1
    have hM1 : Merges gates a1 g := (Finset.mem_filter.mp hg1).2
    have hM2 : Merges gates a2 g := (Finset.mem_filter.mp hg2).2
    obtain ⟨_, _, b, hb, _, hMb⟩ := hK_side g hgK
    have hb1 := hbase_false g a1 ha1 b hb hMb
    obtain ⟨hop1, _, w1, w2, hin1, r, hr, _, _, hv1, _, _⟩ := hM1
    have hr_ne : r ≠ baseA := ne_base_of_or_true gates hWF a1 baseA g w1 w2 r hop1 hin1 hb1 (Or.inl hv1)
    have hgt : val gates (13 + g.val) (testInp a1 r) = true := by
      rw [val_or_iff gates g _ (hWF g).2 hop1, hin1]
      exact ⟨w1, by simp, hv1⟩
    have hcol2 := val_mono gates hG hWF _ _ (h_other_A a1 ha1 a2 ha2 hne r hr hr_ne) (13 + g.val) (by omega) hgt
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
  have hJA_disj : Set.PairwiseDisjoint (A : Set P) JA := by
    intro a1 ha1 a2 ha2 hne
    show Disjoint (JA a1) (JA a2)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨_, _, p, hp, hpne, hvp⟩ := Finset.mem_filter.mp hz1
    obtain ⟨_, hcol2, _⟩ := Finset.mem_filter.mp hz2
    have ht := val_mono gates hG hWF _ _ (h_other_A a1 ha1 a2 ha2 hne p hp hpne) (13 + z.val) (by omega) hvp
    rw [hcol2] at ht
    exact Bool.noConfusion ht
  -- Helper: from g ∈ K with Merges a g ∧ Merges b g and p ∈ line a \ line b firing on input w of g, find z ∈ JA a
  have find_z (g : Fin gates.length) (a : P) (ha : a ∈ A) (b : P) (hb : b ∈ B)
      (hMa : Merges gates a g) (hMb : Merges gates b g)
      (w : ℕ) (hw : w ∈ (gates.get g).inputs) (p : P) (hpa : p ∈ line a) (hpb : p ∉ line b)
      (hvw : val gates w (testInp a p) = true) :
      ∃ z : Fin gates.length, z ∈ JA a ∧ z < g ∧
        val gates (13 + z.val) (coline b) = false ∧ val gates (13 + z.val) (testInp a p) = true := by
    have hstep : OrReach gates (13 + g.val) w := orReach_step gates g hMa.1 hw
    have hwlt : w < 13 + g.val := (hWF g).2 w hw
    rcases orReach_find_stop gates hG hWF (testInp a p) w (by omega) hvw with ⟨v, hrv, hxv⟩ | ⟨z, hzop, hrz, hvz⟩
    · exfalso
      have hrvg : OrReach gates (13 + g.val) v.val := orReach_trans gates hstep hrv
      have hfa := orReach_false gates hWF hrvg (coline a) hMa.2.1
      have hfb := orReach_false gates hWF hrvg (coline b) hMb.2.1
      rw [val_input] at hfa hfb
      have hva : v ∈ line a := by simpa [coline] using hfa
      have hvb : v ∈ line b := by simpa [coline] using hfb
      have heq := testInp_in_line_eq a (h_sub a ha) p hpa v hva hxv
      exact hpb (heq ▸ hvb)
    · have hrzg : OrReach gates (13 + g.val) (13 + z.val) := orReach_trans gates hstep hrz
      have hfa := orReach_false gates hWF hrzg (coline a) hMa.2.1
      have hfb := orReach_false gates hWF hrzg (coline b) hMb.2.1
      have hzJ : z ∈ J := hJ_side z hzop g a ha b hb hMa hMb hrzg hfa hfb ⟨p, hpa, hpb, hvz⟩
      have hpne : p ≠ baseA := by
        intro hpeq; subst hpeq
        have ht := val_mono gates hG hWF _ _ (h_base_le a ha b hb) (13 + z.val) (by omega) hvz
        rw [hfb] at ht; exact Bool.noConfusion ht
      have hzJA : z ∈ JA a := Finset.mem_filter.mpr ⟨hzJ, hfa, p, hpa, hpne, hvz⟩
      have hle := orReach_le gates hWF hrz
      have hzlt : z < g := by change z.val < g.val; omega
      exact ⟨z, hzJA, hzlt, hfb, hvz⟩
  -- Helper: given two distinct points r, r' ∈ line a and b ∈ B, not both lie in line b
  have not_both_in_b (a : P) (ha : a ∈ A) (b : P) (hb : b ∈ B) (r r' : P)
      (hr : r ∈ line a) (hr' : r' ∈ line a) (hne : r ≠ r') (h1 : r ∈ line b) : r' ∉ line b := by
    intro h2
    have hsub2 : ({r, r'} : Finset P) ⊆ line a ∩ line b := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_inter.mpr ⟨by assumption, by assumption⟩
    have hc2 : ({r, r'} : Finset P).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have hle := Finset.card_le_card hsub2
    have h1c := h_inter a ha b hb
    omega
  -- Per-line bound for each a ∈ A
  have hper (a : P) (ha : a ∈ A) :
      (KA a).card ≤ 2 * (JA a \ JB_all).card + (JA a ∩ JB_all).card := by
    have hJsplit : (JA a).card = (JA a \ JB_all).card + (JA a ∩ JB_all).card := by
      have := Finset.card_sdiff_add_card_inter (JA a) JB_all
      omega
    have hle2 : (KA a).card ≤ 2 := by
      apply card_le_two_of_merges gates hWF a baseA (h_card3 a ha) (KA a)
      intro g hg
      have hgK : g ∈ K := (Finset.mem_filter.mp hg).1
      have hMa : Merges gates a g := (Finset.mem_filter.mp hg).2
      obtain ⟨_, _, b, hb, _, hMb⟩ := hK_side g hgK
      exact ⟨hMa, hbase_false g a ha b hb hMb⟩
    have get_partner (g : Fin gates.length) (hg : g ∈ KA a) :
        ∃ b ∈ B, Merges gates a g ∧ Merges gates b g := by
      have hgK : g ∈ K := (Finset.mem_filter.mp hg).1
      have hMa : Merges gates a g := (Finset.mem_filter.mp hg).2
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
        by_cases hrb : r ∉ line b
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
      obtain ⟨g1, hg1, g2, hg2, h12⟩ := two_ordered_of_one_lt (by omega : 1 < (KA a).card)
      obtain ⟨b1, hb1, hMa1, hMb1⟩ := get_partner g1 hg1
      obtain ⟨b2, hb2, hMa2, hMb2⟩ := get_partner g2 hg2
      have ⟨hop1, hcol1, w11, w12, hin1, r1, hr1, r1', hr1', hv11, hv12, X1, hr1X, hr1'X, hcut1⟩ := hMa1
      have ⟨hop2, hcol2, w21, w22, hin2, r2, hr2, r2', hr2', hv21, hv22, X2, hr2X, hr2'X, hcut2⟩ := hMa2
      have h1neq : r1 ≠ r1' := fun h => hr1'X (h ▸ hr1X)
      have h2neq : r2 ≠ r2' := fun h => hr2'X (h ▸ hr2X)
      -- Case 1: neither r1 nor r1' is in line b1
      by_cases hboth1 : r1 ∉ line b1 ∧ r1' ∉ line b1
      · obtain ⟨z1, hz1, hz1lt, _, hvz1⟩ := find_z g1 a ha b1 hb1 hMa1 hMb1 w11 (by rw [hin1]; simp) r1 hr1 hboth1.1 hv11
        obtain ⟨z2, hz2, _, _, hvz2⟩ := find_z g1 a ha b1 hb1 hMa1 hMb1 w12 (by rw [hin1]; simp) r1' hr1' hboth1.2 hv12
        have hzne : z1 ≠ z2 := by
          intro heq; subst heq
          have hcolz := (Finset.mem_filter.mp hz1).2.1
          have hsame := wire_same_comp gates hG hWF a (h_sub a ha) g1 X1 hcut1 (13 + z1.val) (by omega) hcolz r1 hr1 r1' hr1' hvz1 hvz2
          exact hr1'X (hsame.mp hr1X)
        have hcard2 : 2 ≤ (JA a).card := Finset.one_lt_card.mpr ⟨z1, hz1, z2, hz2, hzne⟩
        omega
      · -- At least one of r1, r1' lies in line b1; let q1 be the one in line b1 and p1 be the other
        have hqp1 : ∃ q1 ∈ line a, ∃ p1 ∈ line a, q1 ∈ line b1 ∧ p1 ∉ line b1 ∧
            (q1 = r1 ∧ p1 = r1' ∨ q1 = r1' ∧ p1 = r1) ∧
            ∃ wp1 ∈ (gates.get g1).inputs, val gates wp1 (testInp a p1) = true := by
          by_cases h : r1 ∈ line b1
          · exact ⟨r1, hr1, r1', hr1', h, not_both_in_b a ha b1 hb1 r1 r1' hr1 hr1' h1neq h,
              Or.inl ⟨rfl, rfl⟩, w12, by rw [hin1]; simp, hv12⟩
          · have h' : r1' ∈ line b1 := by
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
        have hp2_ex : ∃ p2 ∈ line a, ∃ p2' ∈ line a, p2 ≠ p2' ∧ ¬ (p1 ∈ X2 ↔ p2 ∈ X2) ∧
            (∃ w ∈ (gates.get g2).inputs, val gates w (testInp a p2) = true) ∧
            (∃ w' ∈ (gates.get g2).inputs, val gates w' (testInp a p2') = true) := by
          by_cases hp : p1 ∈ X2
          · exact ⟨r2', hr2', r2, hr2, h2neq.symm, by simp [hp, hr2'X],
              ⟨w22, by rw [hin2]; simp, hv22⟩, ⟨w21, by rw [hin2]; simp, hv21⟩⟩
          · exact ⟨r2, hr2, r2', hr2', h2neq, by simp [hp, hr2X],
              ⟨w21, by rw [hin2]; simp, hv21⟩, ⟨w22, by rw [hin2]; simp, hv22⟩⟩
        obtain ⟨p2, hp2, p2', hp2', hp2neq, hopp, ⟨wp2, hwp2in, hvp2⟩, ⟨wp2', hwp2'in, hvp2'⟩⟩ := hp2_ex
        by_cases hp2b2 : p2 ∉ line b2
        · obtain ⟨z2, hz2, _, _, hvz2⟩ := find_z g2 a ha b2 hb2 hMa2 hMb2 wp2 hwp2in p2 hp2 hp2b2 hvp2
          have hzne : z1 ≠ z2 := by
            intro heq; subst heq
            have hcolz := (Finset.mem_filter.mp hz1).2.1
            have hlt2 : 13 + z1.val < 13 + g2.val := by
              have : z1.val < g1.val := hz1lt
              have : g1.val < g2.val := h12
              omega
            have hsame := wire_same_comp gates hG hWF a (h_sub a ha) g2 X2 hcut2 (13 + z1.val) hlt2 hcolz p1 hp1 p2 hp2 hvz1 hvz2
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
            -- z1 = z2, so val z1 (coline b1) = false AND val z1 (coline b2) = false, and b1 ≠ b2!
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
              · have ht := val_mono gates hG hWF _ _ (h_other_B b3 hb3 b1 hb1 h31 s hs hsne) (13 + z1.val) (by omega) hvs
                rw [hfb1] at ht; exact Bool.noConfusion ht
              · push Not at h31
                subst h31
                have ht := val_mono gates hG hWF _ _ (h_other_B b3 hb3 b2 hb2 hb12 s hs hsne) (13 + z1.val) (by omega) hvs
                rw [hfb2] at ht; exact Bool.noConfusion ht
            have hpure : 1 ≤ (JA a \ JB_all).card := Finset.card_pos.mpr ⟨z1, Finset.mem_sdiff.mpr ⟨hz1, hz1_not_JB⟩⟩
            omega
  -- Sum hper over a ∈ A
  have hsumK : K.card = ∑ a ∈ A, (KA a).card := by
    rw [hK_eq, Finset.card_biUnion hKA_disj]
  have hsumPure : (JA_all \ JB_all).card = ∑ a ∈ A, (JA a \ JB_all).card := by
    have hdisj : Set.PairwiseDisjoint (A : Set P) (fun a => JA a \ JB_all) := by
      intro a1 ha1 a2 ha2 hne
      exact Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset (hJA_disj ha1 ha2 hne)
    have heq : JA_all \ JB_all = A.biUnion (fun a => JA a \ JB_all) := by
      ext z
      simp only [JA_all, Finset.mem_sdiff, Finset.mem_biUnion]
      exact ⟨fun ⟨⟨a, ha, hza⟩, hzb⟩ => ⟨a, ha, hza, hzb⟩,
             fun ⟨a, ha, hza, hzb⟩ => ⟨⟨a, ha, hza⟩, hzb⟩⟩
    rw [heq, Finset.card_biUnion hdisj]
  have hsumBoth : (JA_all ∩ JB_all).card = ∑ a ∈ A, (JA a ∩ JB_all).card := by
    have hdisj : Set.PairwiseDisjoint (A : Set P) (fun a => JA a ∩ JB_all) := by
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

lemma main_proof (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (K J : Finset (Fin gates.length))
    (hK : ∀ g : Fin gates.length, g ∈ K ↔ ∃ l ∈ LS, ∃ m ∈ MS, Merges gates l g ∧ Merges gates m g)
    (hJ : ∀ z : Fin gates.length,
      ((gates.get z).op = GateOp.and ∧
        ∃ g : Fin gates.length, ∃ l ∈ LS, ∃ m ∈ MS,
          Merges gates l g ∧ Merges gates m g ∧
          OrReach gates (13 + g.val) (13 + z.val) ∧
          val gates (13 + z.val) (coline l) = false ∧
          val gates (13 + z.val) (coline m) = false ∧
          ((∃ p ∈ line l, p ∉ line m ∧ val gates (13 + z.val) (testInp l p) = true) ∨
           (∃ p ∈ line m, p ∉ line l ∧ val gates (13 + z.val) (testInp m p) = true))) → z ∈ J) :
    K.card ≤ J.card := by
  classical
  let JL (l : P) := J.filter (fun z => val gates (13 + z.val) (coline l) = false ∧
    ∃ p ∈ line l, p ≠ 0 ∧ val gates (13 + z.val) (testInp l p) = true)
  let JM (m : P) := J.filter (fun z => val gates (13 + z.val) (coline m) = false ∧
    ∃ s ∈ line m, s ≠ 1 ∧ val gates (13 + z.val) (testInp m s) = true)
  let JL_all := LS.biUnion JL
  let JM_all := MS.biUnion JM
  have h1 : K.card ≤ 2 * (JL_all \ JM_all).card + (JL_all ∩ JM_all).card :=
    side_bound gates hG hWF LS MS 0 1
      (fun a ha => Or.inl ha)
      testInp_base_le_coline_LM
      testInp_other_le_coline_LL
      testInp_other_le_coline_MM
      inter_LM_card
      line_sdiff_base_L
      K J
      (fun g hg => (hK g).mp hg)
      (fun z hzop g l hl m hm hMl hMm hreach hfl hfm hp =>
        hJ z ⟨hzop, g, l, hl, m, hm, hMl, hMm, hreach, hfl, hfm, Or.inl hp⟩)
  have h2 : K.card ≤ 2 * (JM_all \ JL_all).card + (JM_all ∩ JL_all).card :=
    side_bound gates hG hWF MS LS 1 0
      (fun a ha => Or.inr ha)
      testInp_base_le_coline_ML
      testInp_other_le_coline_MM
      testInp_other_le_coline_LL
      inter_ML_card
      line_sdiff_base_M
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

end PEqualNP.Outside.L_meta_1575

theorem PEqualNP.Outside.L_meta_1575 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
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
  have eq : L = PEqualNP.Outside.L_meta_1575.line := funext hL
  subst L
  exact PEqualNP.Outside.L_meta_1575.main_proof gates hG hWF K J hK hJ
