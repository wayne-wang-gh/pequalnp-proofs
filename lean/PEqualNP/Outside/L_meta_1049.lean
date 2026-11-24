import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1049_aux

open PEqualNP.CircuitLowerBounds

def Allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def Positive (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def gateValue (values : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun w => values.getD w false)

def appendGate (values : List Bool) (g : Gate) : List Bool :=
  values ++ [gateValue values g]

def run (gates : List Gate) (values : List Bool) : List Bool :=
  gates.foldl appendGate values

def Below (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ w, x.getD w false = true → y.getD w false = true

theorem gateValue_pos (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (a b : List Bool) (h : Below a b) :
    gateValue a g = true → gateValue b g = true := by
  unfold gateValue
  rcases hop with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro ha w hw
    exact h.2 w (ha w hw)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨w, hw, ha⟩
    exact ⟨w, hw, h.2 w ha⟩

theorem gateValue_neg (g : Gate) (hop : g.op = .not) (a b : List Bool) (h : Below a b) :
    gateValue b g = true → gateValue a g = true := by
  unfold gateValue
  rw [hop]
  cases hi : g.inputs with
  | nil => simp [GateOp.eval]
  | cons w ws =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro hf
    cases ha : a.getD w false
    · rfl
    · exact (Bool.false_ne_true (hf.symm.trans (h.2 w ha))).elim

theorem appendGate_below {a b : List Bool} (h : Below a b) (g : Gate)
    (hg : gateValue a g = true → gateValue b g = true) :
    Below (appendGate a g) (appendGate b g) := by
  refine ⟨by simp [appendGate, h.1], ?_⟩
  intro w
  unfold appendGate
  by_cases hw : w < a.length
  · have hwb : w < b.length := h.1 ▸ hw
    rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hwb]
    exact h.2 w
  · have ha := Nat.le_of_not_gt hw
    have hb : b.length ≤ w := h.1 ▸ ha
    rw [List.getD_append_right _ _ _ _ ha, List.getD_append_right _ _ _ _ hb, h.1]
    cases he : w - b.length with
    | zero => simpa using hg
    | succ k => simp

theorem initial_below {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    Below (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro w
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hw
    simpa using h ⟨w, hw⟩
  · simp

theorem run_cons (g : Gate) (gs : List Gate) (a : List Bool) :
    run (g :: gs) a = run gs (appendGate a g) := rfl

theorem run_keeps (gs : List Gate) (a : List Bool) {w : ℕ} (h : w < a.length) :
    (run gs a).getD w false = a.getD w false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp [appendGate]; omega), appendGate, List.getD_append _ _ _ _ h]

theorem value_first (g : Gate) (gs : List Gate) (a : List Bool) :
    (run (g :: gs) a).getD a.length false = gateValue a g := by
  rw [run_cons, run_keeps _ _ (by simp [appendGate]), appendGate]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl a.length)]
  simp

theorem next_index (g : Gate) (gs : List Gate) (a : List Bool) (j : ℕ) :
    (run gs (appendGate a g)).getD ((appendGate a g).length + j) false =
      (run (g :: gs) a).getD (a.length + (j + 1)) false := by
  congr 1
  simp [appendGate]
  omega

def AgreesNot (gs : List Gate) (a b : List Bool) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .not →
    (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false

theorem AgreesNot.tail {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) :
    AgreesNot gs (appendGate a g) (appendGate b g) := by
  intro j q hj hq
  rw [next_index, next_index]
  exact h (j+1) q (by simpa using hj) hq

theorem AgreesNot.first {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) (hg : g.op = .not) :
    gateValue a g = gateValue b g := by
  have h0 := h 0 g rfl hg
  simpa only [Nat.add_zero, value_first] using h0

theorem run_below (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (hnot : AgreesNot gs a b) :
    Below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons, run_cons]
    apply ih _ _ (appendGate_below h g ?_)
      (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    rcases (hops _ (List.mem_cons_self ..)).1 with ha | ho | hn
    · exact gateValue_pos g (Or.inl ha) a b h
    · exact gateValue_pos g (Or.inr ho) a b h
    · rw [hnot.first hn]
      exact id

def booleanGate : Bool → Gate
  | true => ⟨.and, []⟩
  | false => ⟨.or, []⟩

theorem booleanGate_pos (b : Bool) : Positive (booleanGate b) := by
  cases b <;> simp [Positive, booleanGate]

theorem booleanGate_runs (b : Bool) (x : List Bool) :
    gateValue x (booleanGate b) = b := by
  cases b <;> rfl

noncomputable def freezeGate (a : List Bool) (g : Gate) : Gate := by
  classical
  exact if g.op = .not then booleanGate (gateValue a g) else g

noncomputable def freeze (a : List Bool) : List Gate → List Gate
  | [] => []
  | g :: gs => freezeGate a g :: freeze (appendGate a g) gs

theorem freeze_length (gs : List Gate) (a : List Bool) : (freeze a gs).length = gs.length := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => simp [freeze, ih]

theorem freeze_pos (gs : List Gate) (a : List Bool) (h : ∀ g ∈ gs, Allowed g) :
    ∀ g ∈ freeze a gs, Positive g := by
  induction gs generalizing a with
  | nil => simp [freeze]
  | cons g gs ih =>
    intro q hq
    rw [freeze, List.mem_cons] at hq
    rcases hq with rfl | hq
    · classical
      unfold freezeGate
      split
      · exact booleanGate_pos _
      · rename_i hn
        obtain ⟨ha | ho | hh, hf⟩ := h g (List.mem_cons_self ..)
        · exact ⟨Or.inl ha, hf⟩
        · exact ⟨Or.inr ho, hf⟩
        · exact (hn hh).elim
    · exact ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq)) _ hq

theorem freeze_run (gs : List Gate) (a b z : List Bool)
    (haz : Below a z) (hzb : Below z b) (hops : ∀ g ∈ gs, Allowed g)
    (hnot : AgreesNot gs a b) : run (freeze a gs) z = run gs z := by
  induction gs generalizing a b z with
  | nil => rfl
  | cons g gs ih =>
    rw [freeze, run_cons, run_cons]
    have hA : g ∈ g :: gs := List.mem_cons_self
    have hop := (hops g hA).1
    rcases hop with h | h | h
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inl h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inl h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inr h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inr h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have he : gateValue a g = gateValue b g := hnot.first h
      have hze : gateValue z g = gateValue a g := by
        apply Bool.eq_iff_iff.mpr
        refine ⟨gateValue_neg g h a z haz, ?_⟩
        rw [he]
        exact gateValue_neg g h z b hzb
      have hf : appendGate z (freezeGate a g) = appendGate z g := by
        classical
        unfold appendGate
        simp [freezeGate, h, booleanGate_runs, hze]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (by rw [hze]; exact id))
        (appendGate_below hzb g (by rw [hze, he]; exact id))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail


theorem note_antitone (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (i : ℕ) (g : Gate) (hi : gs[i]? = some g)
    (hg : g.op = .not)
    (hprev : ∀ (j : ℕ) (q : Gate), j < i → gs[j]? = some q → q.op = .not →
      (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false) :
    (run gs b).getD (b.length + i) false = true →
      (run gs a).getD (a.length + i) false = true := by
  induction gs generalizing a b i g with
  | nil => simp at hi
  | cons q gs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst g
      simpa only [Nat.add_zero, value_first] using gateValue_neg q hg a b h
    | succ i =>
      have hb : Below (appendGate a q) (appendGate b q) := by
        apply appendGate_below h
        rcases (hops q (List.mem_cons_self ..)).1 with ha | ho | hn
        · exact gateValue_pos q (Or.inl ha) a b h
        · exact gateValue_pos q (Or.inr ho) a b h
        · have he := hprev 0 q (Nat.zero_lt_succ i) rfl hn
          simp only [Nat.add_zero, value_first] at he
          rw [he]
          exact id
      have hpre (j : ℕ) (r : Gate) (hji : j < i) (hj : gs[j]? = some r)
          (hr : r.op = .not) :
          (run gs (appendGate a q)).getD ((appendGate a q).length + j) false =
          (run gs (appendGate b q)).getD ((appendGate b q).length + j) false := by
        rw [next_index, next_index]
        exact hprev (j+1) r (by omega) (by simpa using hj) hr
      have got := ih _ _ hb (fun r hr => hops r (List.mem_cons_of_mem _ hr))
        i g (by simpa using hi) hg hpre
      rwa [next_index, next_index] at got

noncomputable def notIndices (gs : List Gate) : Finset (Fin gs.length) := by
  classical
  exact Finset.univ.filter (fun i => (gs.get i).op = .not)

theorem mem_notIndices (gs : List Gate) (j : Fin gs.length) :
    j ∈ notIndices gs ↔ (gs.get j).op = .not := by
  classical
  simp [notIndices]

noncomputable def notEmbedding (gs : List Gate) :
    Fin (notIndices gs).card ↪o Fin gs.length :=
  (notIndices gs).orderEmbOfFin rfl

theorem notEmbedding_mem (gs : List Gate) (j : Fin (notIndices gs).card) :
    notEmbedding gs j ∈ notIndices gs :=
  (notIndices gs).orderEmbOfFin_mem rfl j

theorem exists_notEmbedding (gs : List Gate) (j : Fin gs.length)
    (hj : j ∈ notIndices gs) : ∃ i, notEmbedding gs i = j := by
  have h := (notIndices gs).range_orderEmbOfFin rfl
  change Set.range (notEmbedding gs) = _ at h
  change j ∈ Set.range (notEmbedding gs)
  rw [h]
  exact hj

theorem card_notIndices (gs : List Gate) (t : ℕ)
    (h : ∃ f : Fin t → Fin gs.length,
      ∀ i : Fin gs.length, (gs.get i).op = .not → ∃ j, f j = i) :
    (notIndices gs).card ≤ t := by
  classical
  obtain ⟨f, h⟩ := h
  have hsub : notIndices gs ⊆ Finset.univ.image f := by
    intro j hj
    obtain ⟨i, hi⟩ := h j ((mem_notIndices gs j).1 hj)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

def trace {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length) : Bool :=
  (run gs (List.ofFn x)).getD (n + i.val) false

theorem trace_after {n m : ℕ} (gs : List Gate) (x : Fin m → Fin n → Bool)
    (hx : ∀ a b : Fin m, a ≤ b → ∀ w, x a w = true → x b w = true)
    (hg : ∀ g ∈ gs, Allowed g)
    (i : Fin (notIndices gs).card) (a b : Fin m) (hab : a ≤ b)
    (hprev : ∀ j : Fin (notIndices gs).card, j < i →
      trace gs (x a) (notEmbedding gs j) = trace gs (x b) (notEmbedding gs j)) :
    trace gs (x b) (notEmbedding gs i) = true →
      trace gs (x a) (notEmbedding gs i) = true := by
  let j := notEmbedding gs i
  have hj := (mem_notIndices gs j).1 (notEmbedding_mem gs i)
  have hi : gs[j.val]? = some (gs.get j) := List.getElem?_eq_getElem j.isLt
  have got := note_antitone gs (List.ofFn (x a)) (List.ofFn (x b))
    (initial_below _ _ (hx a b hab)) hg j.val (gs.get j) hi hj
  have earlier (k : ℕ) (q : Gate) (hk : k < j.val) (hq : gs[k]? = some q)
      (hqn : q.op = .not) :
      (run gs (List.ofFn (x a))).getD ((List.ofFn (x a)).length + k) false =
      (run gs (List.ofFn (x b))).getD ((List.ofFn (x b)).length + k) false := by
    have hkl : k < gs.length := by
      apply lt_trans hk
      exact j.isLt
    let k' : Fin gs.length := ⟨k, hkl⟩
    have hget : gs.get k' = q := by simpa [k', List.getElem?_eq_getElem hkl] using hq
    obtain ⟨p, hp⟩ := exists_notEmbedding gs k'
      ((mem_notIndices gs k').2 (hget ▸ hqn))
    have hpi : p < i := by
      have hlt : notEmbedding gs p < notEmbedding gs i := by
        rw [hp]
        exact hk
      exact (notEmbedding gs).lt_iff_lt.mp hlt
    have h := hprev p hpi
    rw [hp] at h
    simpa only [trace, List.length_ofFn, k'] using h
  simpa only [trace, List.length_ofFn, j] using got earlier

theorem trace_agrees {n : ℕ} (gs : List Gate) (a b : Fin n → Bool)
    (h : ∀ i : Fin (notIndices gs).card,
      trace gs a (notEmbedding gs i) = trace gs b (notEmbedding gs i)) :
    AgreesNot gs (List.ofFn a) (List.ofFn b) := by
  intro j g hj hg
  have hlt : j < gs.length := (List.getElem?_eq_some_iff.mp hj).choose
  let i : Fin gs.length := ⟨j, hlt⟩
  have he : gs.get i = g := by simpa [i, List.getElem?_eq_getElem hlt] using hj
  obtain ⟨p, hp⟩ := exists_notEmbedding gs i
    ((mem_notIndices gs i).2 (he ▸ hg))
  have hh := h p
  rw [hp] at hh
  simpa only [trace, List.length_ofFn, i] using hh

lemma existsCuts {t m : ℕ} (p : Fin t → Fin m → Bool)
    (h : ∀ (i : Fin t) (a b : Fin m), a ≤ b →
      (∀ j : Fin t, j < i → p j a = p j b) → (p i b = true → p i a = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.range m ∧ P.card + 1 ≤ 2 ^ t ∧
      ∀ a b : Fin m, a ≤ b → (∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) →
        ∀ i : Fin t, p i a = p i b := by
  induction t with
  | zero =>
      refine ⟨∅, by simp, by simp, ?_⟩
      intro _ _ _ _ i
      exact Fin.elim0 i
  | succ t ih =>
      let p₀ (i : Fin t) := p i.castSucc
      have h₀ : ∀ (i : Fin t) (a b : Fin m), a ≤ b →
          (∀ j : Fin t, j < i → p₀ j a = p₀ j b) →
          (p₀ i b = true → p₀ i a = true) := by
        intro i a b hab hearlier htrue
        apply h i.castSucc a b hab ?_ htrue
        intro j hj
        have hjt : j.val < t := lt_of_lt_of_le hj i.isLt.le
        exact hearlier ⟨j.val, hjt⟩ (by exact hj)
      obtain ⟨P, hP, hp, stable⟩ := ih p₀ h₀
      have hlast {a b : Fin m} (hab : a ≤ b)
          (hgood : ∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) :
          p (Fin.last t) b = true → p (Fin.last t) a = true := by
        apply h (Fin.last t) a b hab
        intro j hj
        exact stable a b hab hgood ⟨j.val, hj⟩
      let value (w : ℕ) : Bool := if hw : w < m then p (Fin.last t) ⟨w, hw⟩ else false
      have value_eq (w : ℕ) (hw : w < m) : value w = p (Fin.last t) ⟨w, hw⟩ := dite_eq_left hw
      let N := (Finset.range m).filter (fun w =>
        0 < w ∧ w ∉ P ∧ value (w - 1) = true ∧ value w = false)
      have hN {w : ℕ} (hw : w ∈ N) :
          w < m ∧ 0 < w ∧ w ∉ P ∧ value (w - 1) = true ∧ value w = false := by
        have he := Finset.mem_filter.mp hw
        exact ⟨Finset.mem_range.mp he.1, he.2⟩
      let before (w : ℕ) := P.filter (fun k => k ≤ w)
      have hsep {u v : ℕ} (hu : u ∈ N) (hv : v ∈ N) (hlt : u < v) :
          (before u).card ≠ (before v).card := by
        intro he
        have hsub : before u ⊆ before v := by
          intro k hk
          obtain ⟨hkP, hku⟩ := Finset.mem_filter.mp hk
          exact Finset.mem_filter.mpr ⟨hkP, le_trans hku hlt.le⟩
        have heq : before u = before v :=
          Finset.eq_of_subset_of_card_le hsub he.ge
        have hnocut : ∀ w ∈ P, ¬ (u < w ∧ w ≤ v - 1) := by
          intro w hw hinterval
          have hwv : w ∈ before v :=
            Finset.mem_filter.mpr ⟨hw, hinterval.2.trans (Nat.sub_le ..)⟩
          rw [← heq] at hwv
          exact (not_le_of_gt hinterval.1) (Finset.mem_filter.mp hwv).2
        have huu := hN hu
        have hvv := hN hv
        have hvlt : v - 1 < m := lt_of_le_of_lt (Nat.sub_le ..) hvv.1
        have htrans := hlast
          (a := ⟨u, huu.1⟩) (b := ⟨v - 1, hvlt⟩)
          (by show u ≤ v - 1; omega) hnocut
        have htrue : value u = true := by
          rw [value_eq _ huu.1]
          apply htrans
          rw [← value_eq _ hvlt]
          exact hvv.2.2.2.1
        rw [huu.2.2.2.2] at htrue
        contradiction
      have hcount : N.card ≤ P.card + 1 := by
        simpa only [Finset.card_range] using
          (Finset.card_le_card_of_injOn
            (s := N) (t := Finset.range (P.card + 1))
            (fun w => (before w).card)
            (fun w _ => Finset.mem_range.mpr (Nat.lt_succ_of_le
              (Finset.card_filter_le _ _)))
            (by
              intro u hu v hv he
              rcases lt_trichotomy u v with hlt | heq | hgt
              · exact False.elim (hsep hu hv hlt he)
              · exact heq
              · exact False.elim (hsep hv hu hgt he.symm)))
      refine ⟨P ∪ N, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hP hw
        · exact Finset.mem_range.mpr (hN hw).1
      · have hU := Finset.card_union_le P N
        rw [Nat.pow_succ]
        omega
      · intro a b hab hgood i
        have hprev : ∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val) :=
          fun w hw => hgood w (Finset.mem_union_left _ hw)
        by_cases hi : i.val < t
        · exact stable a b hab hprev ⟨i.val, hi⟩
        · have hie : i = Fin.last t := by
            apply Fin.ext
            have hi' := i.isLt
            change i.val = t
            omega
          subst i
          have hadj (w : ℕ) (haw : a.val < w) (hwb : w ≤ b.val) :
              value (w - 1) = value w := by
            have hw : w < m := hwb.trans_lt b.isLt
            have hw' : w - 1 < m := (Nat.sub_le ..).trans_lt hw
            have hpos : 0 < w := by omega
            have hpw : w ∉ P := fun hmem => hprev w hmem ⟨haw, hwb⟩
            have hnW : w ∉ N :=
              fun hmem => hgood w (Finset.mem_union_right _ hmem) ⟨haw, hwb⟩
            have hstep := hlast
              (a := ⟨w - 1, hw'⟩) (b := ⟨w, hw⟩)
              (Nat.sub_le ..)
              (by
                rintro k hk ⟨hkw, hwk⟩
                change w - 1 < k at hkw
                change k ≤ w at hwk
                have he : k = w := by omega
                exact hpw (he ▸ hk))
            have himp : value w = true → value (w - 1) = true := by
              rw [value_eq _ hw, value_eq _ hw']
              exact hstep
            cases hr : value w <;> cases hl : value (w - 1)
            · rfl
            · exact False.elim (hnW (Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr hw, hpos, hpw, hl, hr⟩))
            · exact False.elim (Bool.false_ne_true (hl.symm.trans (himp hr)))
            · rfl
          have hdist : ∀ d : ℕ, a.val + d ≤ b.val → value (a.val + d) = value a.val := by
            intro d
            induction d with
            | zero => simp
            | succ d ih =>
                intro hd
                have hprev' := ih (by omega)
                have hs := hadj (a.val + (d + 1)) (by omega) hd
                have he : a.val + (d + 1) - 1 = a.val + d := by omega
                rw [he] at hs
                exact hs.symm.trans hprev'
          have hab' : a.val ≤ b.val := hab
          have hdist' := hdist (b.val - a.val) (by omega)
          have he : a.val + (b.val - a.val) = b.val := by omega
          rw [he, value_eq _ b.isLt, value_eq _ a.isLt] at hdist'
          exact hdist'.symm

open Classical in
lemma cutGame_le (m t budget : ℕ) (cost : ℕ × ℕ → ℕ) (P : Finset ℕ)
    (hP : P ⊆ Finset.range m) (hcount : P.card + 1 ≤ 2 ^ t)
    (hcost : ∀ a b : Fin m, a ≤ b →
      (∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) → cost (a.val, b.val) ≤ budget) :
    WithTop.untopD 0 (((Finset.range m).powerset.filter
      (fun Q : Finset ℕ => Q.card + 1 ≤ 2 ^ t)).image
      (fun Q : Finset ℕ => ((Finset.range m ×ˢ Finset.range m).filter
        (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ Q, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup
        cost)).min ≤ budget := by
  let feasible := (Finset.range m).powerset.filter (fun Q : Finset ℕ => Q.card + 1 ≤ 2 ^ t)
  let score (Q : Finset ℕ) :=
    ((Finset.range m ×ˢ Finset.range m).filter
      (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ Q, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup cost
  change WithTop.untopD 0 (feasible.image score).min ≤ budget
  have hf : P ∈ feasible := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hP, hcount⟩
  have hmem : score P ∈ feasible.image score := Finset.mem_image_of_mem score hf
  have hscore : score P ≤ budget := by
    apply Finset.sup_le
    rintro ⟨u, v⟩ huv
    obtain ⟨hprod, huv', hnone⟩ := Finset.mem_filter.mp huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hprod
    exact hcost ⟨u, Finset.mem_range.mp hu⟩ ⟨v, Finset.mem_range.mp hv⟩ huv' hnone
  apply WithTop.coe_le_coe.mp
  exact (WithTop.coe_untopD_le _ _).trans
    ((Finset.min_le hmem).trans (WithTop.coe_le_coe.mpr hscore))

namespace Incidence

def through {n : ℕ} (S : Fin n → Finset (Fin n)) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p ∈ S i)

theorem through_card {n q : ℕ} (S : Fin n → Finset (Fin n))
    (hn : n = q*q + q + 1) (hq : 0 < q)
    (hS : ∀ i, (S i).card = q+1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hjoin : ∀ p p' : Fin n, p ≠ p' → ∃ i, p ∈ S i ∧ p' ∈ S i)
    (p : Fin n) : (through S p).card = q + 1 := by
  let T := through S p
  have hdis : (T : Set (Fin n)).PairwiseDisjoint (fun i => (S i).erase p) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hpi : p ∈ S i := by simpa [T, through] using hi
    have hpj : p ∈ S j := by simpa [T, through] using hj
    have hp : p ∈ S i ∩ S j := Finset.mem_inter.mpr ⟨hpi, hpj⟩
    have ha' : a ∈ S i ∩ S j := Finset.mem_inter.mpr
      ⟨Finset.mem_of_mem_erase ha, Finset.mem_of_mem_erase hb⟩
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hcross i j hij)
    have hpv : p = v := by simpa [hv] using hp
    have hav : a = v := by simpa [hv] using ha'
    exact (Finset.mem_erase.mp ha).1 (hav.trans hpv.symm)
  have hcover : T.biUnion (fun i => (S i).erase p) =
      (Finset.univ : Finset (Fin n)).erase p := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, hmem⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hmem).1, Finset.mem_univ _⟩
    · intro ha
      have hpa : p ≠ a := Ne.symm (Finset.mem_erase.mp ha).1
      obtain ⟨i, hpi, hai⟩ := hjoin p a hpa
      exact Finset.mem_biUnion.mpr ⟨i, by simpa [T, through] using hpi,
        Finset.mem_erase.mpr ⟨Ne.symm hpa, hai⟩⟩
  have hf (i : Fin n) (hi : i ∈ T) : ((S i).erase p).card = q := by
    have hpi : p ∈ S i := by simpa [T, through] using hi
    rw [Finset.card_erase_of_mem hpi, hS]
    omega
  have hcount := Finset.card_biUnion hdis
  rw [hcover, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  calc
    (through S p).card = T.card := rfl
    _ = q + 1 := by
      have hsum : (∑ i ∈ T, ((S i).erase p).card) = T.card * q := by
        rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul]
        rfl
      rw [hsum] at hcount
      have hmul : q * T.card = q * (q+1) := by
        rw [Nat.mul_comm q T.card, ← hcount, hn]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      exact Nat.eq_of_mul_eq_mul_left hq hmul

def missed {n : ℕ} (S : Fin n → Finset (Fin n)) (A : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Disjoint (S i) A)

theorem missed_card {n q d : ℕ} (S : Fin n → Finset (Fin n)) (A : Finset (Fin n))
    (hn : n = q*q + q + 1)
    (hreg : ∀ p, (through S p).card = q + 1)
    (hd : 0 < d) (hdvd : d ∣ q)
    (hA : A.card = (d - 1) * q + d)
    (hmeet : ∀ i, (S i ∩ A).card = 0 ∨ (S i ∩ A).card = d) :
    (missed S A).card = q * (q + 1) / d - q := by
  classical
  let H := Finset.univ.filter (fun i => ¬ Disjoint (S i) A)
  let hit : Fin n → Fin n → ℕ := fun i a => if a ∈ S i then 1 else 0
  have hcount1 (i : Fin n) : (∑ a ∈ A, hit i a) = (S i ∩ A).card := by
    change (∑ a ∈ A, if a ∈ S i then 1 else 0) = _
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one]
    have he : A.filter (fun a => a ∈ S i) = S i ∩ A := by
      ext a
      simp [and_comm]
    rw [he]
    rfl
  have hcount2 (a : Fin n) : (∑ i : Fin n, hit i a) = q+1 := by
    change (∑ i : Fin n, if a ∈ S i then 1 else 0) = _
    rw [← Finset.sum_filter]
    simpa [through] using hreg a
  have hm (i : Fin n) : (S i ∩ A).card = if ¬ Disjoint (S i) A then d else 0 := by
    by_cases hz : Disjoint (S i) A
    · simp [hz, Finset.disjoint_iff_inter_eq_empty.mp hz]
    · rcases hmeet i with he | he
      · exact (hz (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp he))).elim
      · simp [hz, he]
  have hcount : d * H.card = A.card * (q + 1) := by
    calc
      d * H.card = ∑ i ∈ H, d := by simp [Nat.mul_comm]
      _ = ∑ i : Fin n, (S i ∩ A).card := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun i _ => (hm i).symm)
      _ = ∑ i : Fin n, ∑ a ∈ A, hit i a := by
        exact Finset.sum_congr rfl (fun i _ => (hcount1 i).symm)
      _ = ∑ a ∈ A, ∑ i : Fin n, hit i a := by
        rw [← Finset.sum_product', Finset.sum_product_right]
      _ = A.card * (q+1) := by simp [hcount2]
  have hcountAll : (missed S A).card + H.card = n := by
    simpa [missed, H] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i => Disjoint (S i) A)
  obtain ⟨r, hr⟩ := hdvd
  have hdiv : q * (q+1) / d = r * (q+1) := by
    have he : q * (q+1) = d * (r * (q+1)) := by
      rw [← Nat.mul_assoc, ← hr]
    rw [he, Nat.mul_div_cancel_left _ hd]
  have hAc : A.card + q = d * (q+1) := by
    rw [hA]
    calc
      (d - 1) * q + d + q = ((d - 1) + 1) * q + d := by ring
      _ = _ := by rw [Nat.sub_add_cancel hd]; ring
  have he : d * (H.card + r * (q+1)) = d * (n+q) := by
    calc
      d * (H.card + r * (q+1)) = d * H.card + q * (q+1) := by
        rw [Nat.mul_add, ← Nat.mul_assoc, ← hr]
      _ = (A.card + q) * (q+1) := by rw [hcount, Nat.add_mul]
      _ = _ := by rw [hAc, hn]; ring
  have h := Nat.eq_of_mul_eq_mul_left hd he
  rw [hdiv]
  omega

def level {n h : ℕ} (K : Fin (h+1) → Finset (Fin n)) (j : ℕ) : Finset (Fin n) :=
  if j = 0 then ∅ else if hj : j ≤ h+1 then K ⟨j-1, by omega⟩ else Finset.univ

def missValue (h q n j : ℕ) : ℕ :=
  if j = 0 then n else if j = h+2 then 0 else q*(q+1)/2^(j-1)-q

def windowCharge (h q j : ℕ) : ℕ :=
  if j = h+2 then q else 2^(j-1)-1

theorem level_mono {n h : ℕ} (K : Fin (h+1) → Finset (Fin n))
    (hK : ∀ j j', j ≤ j' → K j ⊆ K j') : Monotone (level K) := by
  intro a b hab
  by_cases ha : a = 0
  · simp [level, ha]
  have hb : b ≠ 0 := by omega
  by_cases hb' : b ≤ h+1
  · have ha' := hab.trans hb'
    rw [level, ite_eq_right ha, dite_eq_left ha', level, ite_eq_right hb, dite_eq_left hb']
    apply hK
    show a-1 ≤ b-1
    omega
  · simp [level, hb, hb']

theorem missed_level_card {n h q : ℕ} (S : Fin n → Finset (Fin n))
    (K : Fin (h+1) → Finset (Fin n)) (hn : n = q*q + q + 1) (hq : q = 2^h)
    (hS : ∀ i, (S i).card = q+1) (hreg : ∀ p, (through S p).card = q+1)
    (hK : ∀ j : Fin (h+1), (K j).card = (2^(j:ℕ)-1)*q + 2^(j:ℕ))
    (hmeet : ∀ (j : Fin (h+1)) i, (S i ∩ K j).card = 0 ∨
        (S i ∩ K j).card = 2^(j:ℕ))
    (j : ℕ) (hj : j ≤ h+2) : (missed S (level K j)).card = missValue h q n j := by
  classical
  by_cases hz : j = 0
  · simp [level, hz, missed, missValue]
  by_cases hf : j = h+2
  · have hn' : ¬ j ≤ h+1 := by omega
    rw [level, ite_eq_right hz, dite_eq_right hn', missValue, ite_eq_right hz, ite_eq_left hf]
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro i hi
    have he : S i = ∅ := by
      have hd := (Finset.mem_filter.mp (show i ∈ missed S Finset.univ from hi)).2
      simpa using Finset.disjoint_iff_inter_eq_empty.mp hd
    have hE := hS i
    simp [he] at hE
  have hj' : j ≤ h+1 := by omega
  rw [level, ite_eq_right hz, dite_eq_left hj', missValue, ite_eq_right hz, ite_eq_right hf]
  apply missed_card S _ hn hreg (by positivity) _ (hK _) (hmeet _)
  rw [hq]
  exact pow_dvd_pow (2 : ℕ) (by omega)

theorem window_lines {n h : ℕ} (S : Fin n → Finset (Fin n))
    (K : Fin (h+1) → Finset (Fin n)) (q a b : ℕ)
    (hS : ∀ i, (S i).card = q+1)
    (hmeet : ∀ (j : Fin (h+1)) i, (S i ∩ K j).card = 0 ∨
        (S i ∩ K j).card = 2^(j:ℕ))
    (hb : b ≤ h+2)
    {i : Fin n} (hi : i ∈ missed S (level K a) \ missed S (level K b)) :
    (S i ∩ level K b).card = windowCharge h q b + 1 := by
  have hnon : ¬ Disjoint (S i) (level K b) := by
    intro he
    exact (Finset.mem_sdiff.mp hi).2 (show i ∈ missed S (level K b) by simp [missed, he])
  have hb0 : b ≠ 0 := by
    intro hz
    exact hnon (by simp [level, hz])
  by_cases hb' : b = h+2
  · have hj : ¬ b ≤ h+1 := by omega
    simpa [level, hb0, hj, windowCharge, hb'] using hS i
  have hb'' : b ≤ h+1 := by omega
  rw [level, ite_eq_right hb0, dite_eq_left hb''] at hnon ⊢
  rw [windowCharge, ite_eq_right hb', Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity : 0 < (2:ℕ)^(b-1)))]
  rcases hmeet ⟨b-1, by omega⟩ i with he | he
  · exact (hnon (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp he))).elim
  · exact he

theorem missed_anti {n : ℕ} (S : Fin n → Finset (Fin n)) : Antitone (missed S) := by
  intro A B hAB i hi
  have hi' : Disjoint (S i) B := by simpa [missed] using hi
  simpa [missed] using hi'.mono_right hAB

theorem window_card {n h q : ℕ} (S : Fin n → Finset (Fin n))
    (K : Fin (h+1) → Finset (Fin n)) (a b : ℕ) (hab : a ≤ b)
    (hK : ∀ j j', j ≤ j' → K j ⊆ K j')
    (ha : (missed S (level K a)).card = missValue h q n a)
    (hb : (missed S (level K b)).card = missValue h q n b) :
    (missed S (level K a) \ missed S (level K b)).card =
      missValue h q n a - missValue h q n b := by
  rw [Finset.card_sdiff_of_subset (missed_anti S (level_mono K hK hab)), ha, hb]

theorem window_free {n h : ℕ} (S : Fin n → Finset (Fin n))
    (K : Fin (h+1) → Finset (Fin n)) (a b : ℕ)
    {i : Fin n} (hi : i ∈ missed S (level K a) \ missed S (level K b)) :
    S i ∩ (level K b \ level K a) = S i ∩ level K b := by
  have hd : Disjoint (S i) (level K a) :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2
  ext p
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · tauto
  · rintro ⟨hpi, hpb⟩
    exact ⟨hpi, hpb, fun hpa => Finset.disjoint_left.mp hd hpi hpa⟩

end Incidence

-- This argument uses the circuit bounds from L-meta-529 and L-meta-669.

namespace Sums

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S gs i

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, ?_, ?_⟩
  · rw [val_snoc, ite_eq_right hne]; exact hz
  · rw [val_snoc, ite_eq_right hne]; exact hu
  · rw [val_snoc, ite_eq_right hne]; exact hv

theorem main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S gs l ∧ S.card ≤ (S.image l).card + (D S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, ite_eq_left hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, ite_eq_right hi]
    -- facts about the new wire from the old invariant
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [ite_eq_left h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [ite_eq_right h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S gs).card + 1 ≤ (D S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S gs g)
        omega

end Sums

open Sums in
theorem full_cost : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length := by
  classical
  intro n m S hS gates out hg hev
  have hval : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true) := fun w x => hev w x
  have hZ : ∀ w, val gates (Zof (S w)) (out w) = false := by
    intro w
    rw [hval]
    simp [Zof]
  have hE : ∀ w, ∀ u ∈ S w, val gates (eof u) (out w) = true := by
    intro w u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  choose l hinv hcard using fun w => main_inv (S w) gates hg
  have hbound : ∀ w, (S w).card - 1 ≤ (D (S w) gates).card := by
    intro w
    have h1 : ((S w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (hZ w) (hE w u hu) (hE w v hv)).2
    have := hcard w
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (S a) gates) (D (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, u, v, huv, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
    have hua := (hinv a i u u hza hu hu).1
    have hva := (hinv a i v v hza hv hv).1
    have hub := (hinv b i u u hzb hu hu).1
    have hvb := (hinv b i v v hzb hv hv).1
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, hub⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  calc ∑ w, ((S w).card - 1) ≤ ∑ w, (D (S w) gates).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ = (Finset.univ.biUnion fun w => D (S w) gates).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact hw.1
    _ = gates.length := by simp

namespace BoxSimplification

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [ite_eq_left ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [ite_eq_right ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, ite_eq_right hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
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
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, ite_eq_left rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
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
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, ite_eq_left rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, ite_eq_left ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, ite_eq_right ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
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
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, le_refl _, rep_input ρ hρ⟩

lemma inv_final {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (gates : List Gate)
    (h : Inv ρ gates) :
    ∃ (gates' : List Gate) (r : ℕ → ℕ), (∀ g ∈ gates', Fan g) ∧ gates'.length ≤ gates.length ∧
      ∀ o : ℕ, (∃ x y : Fin n → Bool,
        (W gates (ρ x)).getD o false ≠ (W gates (ρ y)).getD o false) →
        ∀ x : Fin n → Bool, (W gates' x).getD (r o) false = (W gates (ρ x)).getD o false := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  have hsel : ∀ o : ℕ, ∃ j : ℕ,
      (∃ c : Bool, ∀ x : Fin n → Bool, (W gates (ρ x)).getD o false = c) ∨
      (∀ x : Fin n → Bool, (W new x).getD j false = (W gates (ρ x)).getD o false) := by
    intro o
    rcases hrep o with hc | ⟨j, _, hj⟩
    · exact ⟨0, Or.inl hc⟩
    · exact ⟨j, Or.inr hj⟩
  choose r hr using hsel
  refine ⟨new, r, hfan, hl, ?_⟩
  intro o hne x
  rcases hr o with ⟨c, hc⟩ | hj
  · obtain ⟨x1, y1, hxy⟩ := hne
    exact absurd ((hc x1).trans (hc y1).symm) hxy
  · exact hj x

theorem main_aux : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) := by
  intro n gates T Z hg
  have hρ : ∀ i : Fin n,
      (∃ c : Bool, ∀ x : Fin n → Bool,
        (if i ∈ T then true else if i ∈ Z then false else x i) = c) ∨
      (∀ x : Fin n → Bool, (if i ∈ T then true else if i ∈ Z then false else x i) = x i) := by
    intro i
    by_cases h1 : i ∈ T
    · exact Or.inl ⟨true, fun x => by rw [ite_eq_left h1]⟩
    · by_cases h2 : i ∈ Z
      · exact Or.inl ⟨false, fun x => by rw [ite_eq_right h1, ite_eq_left h2]⟩
      · exact Or.inr (fun x => by rw [ite_eq_right h1, ite_eq_right h2])
  exact inv_final (fun (x : Fin n → Bool) (i : Fin n) =>
    if i ∈ T then true else if i ∈ Z then false else x i) gates
    (inv_all _ hρ gates hg)

end BoxSimplification

open PEqualNP.CircuitLowerBounds

lemma box_cost {n m : ℕ} (S : Fin m → Finset (Fin n)) (T Z : Finset (Fin n))
    (gs : List Gate) (out : Fin m → ℕ)
    (hsize : ∀ w, 2 ≤ (S w).card)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gs,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hval : ∀ (w : Fin m) (x : Fin n → Bool),
      (Circuit.eval ⟨gs, out w⟩ (List.ofFn (fun i =>
        if i ∈ T then true else if i ∈ Z then false else x i))) =
        decide (∃ v ∈ S w, x v = true)) :
    (∑ w : Fin m, ((S w).card - 1)) ≤ gs.length := by
  obtain ⟨rest, r, hrest, hlen, hrestrict⟩ := BoxSimplification.main_aux n gs T Z hg
  apply le_trans _ hlen
  apply full_cost n m S hinter rest (fun w => r (out w))
  · intro g hg'
    exact ⟨(hrest g hg').1, (hrest g hg').2.le⟩
  · intro w x
    have hnon : ∃ y y' : Fin n → Bool,
        (Circuit.eval ⟨gs, out w⟩ (List.ofFn (fun i =>
          if i ∈ T then true else if i ∈ Z then false else y i))) ≠
        (Circuit.eval ⟨gs, out w⟩ (List.ofFn (fun i =>
          if i ∈ T then true else if i ∈ Z then false else y' i))) := by
      have hp : 0 < (S w).card := (by decide : 0 < 2).trans_le (hsize w)
      obtain ⟨p, hwp⟩ := Finset.card_pos.mp hp
      refine ⟨fun _ => false, fun _ => true, ?_⟩
      rw [hval, hval]
      simpa using (show ∃ v, v ∈ S w from ⟨p, hwp⟩)
    exact (hrestrict (out w) hnon x).trans (hval w x)

open PEqualNP.CircuitLowerBounds

theorem window_cost {n m : ℕ} (S : Fin m → Finset (Fin n))
    (lo hi : Finset (Fin n)) (hsub : lo ⊆ hi)
    (gs : List Gate) (outs : Fin m → ℕ) (hc : ∀ g ∈ gs, Allowed g)
    (hs : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gs, outs w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true))
    (htrace : AgreesNot gs (List.ofFn (fun v => decide (v ∈ lo)))
      (List.ofFn (fun v => decide (v ∈ hi))))
    (d : ℕ) (hd : ∀ i, Disjoint (S i) lo → ¬Disjoint (S i) hi →
      (S i ∩ hi).card - 1 = d) :
    (((Finset.univ : Finset (Fin m)).filter (fun i => Disjoint (S i) lo)).card -
      ((Finset.univ : Finset (Fin m)).filter (fun i => Disjoint (S i) hi)).card) * d ≤
        gs.length := by
  classical
  by_cases hd0 : d = 0
  · simp [hd0]
  let Lost := (Finset.univ : Finset (Fin m)).filter (fun i => Disjoint (S i) lo)
  let Left := (Finset.univ : Finset (Fin m)).filter (fun i => Disjoint (S i) hi)
  let W := Lost \ Left
  let e := W.orderEmbOfFin rfl
  let R : Fin W.card → Finset (Fin n) := fun i => S (e i) ∩ hi
  let gs' := freeze (List.ofFn (fun v => decide (v ∈ lo))) gs
  have hLeft : Left ⊆ Lost := by
    intro w hw
    have hw' : Disjoint (S w) hi := (Finset.mem_filter.mp hw).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hw'.mono_right hsub⟩
  have hw (i : Fin W.card) : Disjoint (S (e i)) lo ∧ ¬Disjoint (S (e i)) hi := by
    have h := Finset.mem_sdiff.mp (W.orderEmbOfFin_mem rfl i)
    exact ⟨(Finset.mem_filter.mp h.1).2,
      fun hj => h.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
  have hr (i : Fin W.card) : (R i).card - 1 = d :=
    hd (e i) (hw i).1 (hw i).2
  have hR (i : Fin W.card) : 2 ≤ (R i).card := by
    have hh := hr i
    omega
  have hinter (i j : Fin W.card) (hne : i ≠ j) : (R i ∩ R j).card ≤ 1 := by
    refine (Finset.card_le_card ?_).trans (hs _ _ (fun hh => hne (e.injective hh)))
    intro v hv
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
  have hval (i : Fin W.card) (x : Fin n → Bool) :
      Circuit.eval ⟨gs', outs (e i)⟩ (List.ofFn (fun v =>
        if v ∈ lo then true else if v ∈ (Finset.univ \ hi : Finset (Fin n)) then false else x v)) =
        decide (∃ v ∈ R i, x v = true) := by
    let y : Fin n → Bool := fun v =>
      if v ∈ lo then true else if v ∈ (Finset.univ \ hi : Finset (Fin n)) then false else x v
    change Circuit.eval ⟨gs', outs (e i)⟩ (List.ofFn y) = _
    have hlow : Below (List.ofFn (fun v => decide (v ∈ lo))) (List.ofFn y) := by
      apply initial_below
      intro v hv
      have hv' : v ∈ lo := of_decide_eq_true hv
      simp [y, hv']
    have hhigh : Below (List.ofFn y) (List.ofFn (fun v => decide (v ∈ hi))) := by
      apply initial_below
      intro v hv
      by_cases hb : v ∈ hi
      · simp [hb]
      · have hnl : v ∉ lo := fun ha => hb (hsub ha)
        simp [y, hb, hnl] at hv
    have hsame := freeze_run gs (List.ofFn (fun v => decide (v ∈ lo)))
      (List.ofFn (fun v => decide (v ∈ hi))) (List.ofFn y) hlow hhigh hc htrace
    have hEq : Circuit.eval ⟨gs', outs (e i)⟩ (List.ofFn y) =
        Circuit.eval ⟨gs, outs (e i)⟩ (List.ofFn y) := by
      change (run gs' (List.ofFn y)).getD (outs (e i)) false =
        (run gs (List.ofFn y)).getD (outs (e i)) false
      rw [hsame]
    rw [hEq, hout, decide_eq_decide]
    constructor
    · rintro ⟨v, hv, hy⟩
      have hnl : v ∉ lo := Finset.disjoint_left.mp (hw i).1 hv
      by_cases hh : v ∈ hi
      · exact ⟨v, Finset.mem_inter.mpr ⟨hv, hh⟩, by simpa [y, hnl, hh] using hy⟩
      · simp [y, hnl, hh] at hy
    · rintro ⟨v, hv, hx⟩
      obtain ⟨hS, hI⟩ := Finset.mem_inter.mp hv
      have hnl : v ∉ lo := Finset.disjoint_left.mp (hw i).1 hS
      exact ⟨v, hS, by simpa [y, hnl, hI] using hx⟩
  have got := box_cost R lo (Finset.univ \ hi) gs' (fun i => outs (e i))
    hR hinter (freeze_pos gs _ hc) hval
  rw [freeze_length] at got
  have hsum : (∑ i : Fin W.card, ((R i).card - 1)) = W.card * d := by
    simp [hr, Nat.mul_comm]
  rw [hsum, Finset.card_sdiff_of_subset hLeft] at got
  exact got

end PEqualNP.Outside.L_meta_1049_aux

open PEqualNP.Outside.L_meta_1049_aux in
theorem PEqualNP.Outside.L_meta_1049 : ∀ (h q n t : ℕ) (S : Fin n → Finset (Fin n)) (K : Fin (h + 1) → Finset (Fin n)), 1 ≤ h → q = 2 ^ h → n = q * q + q + 1 → (∀ i : Fin n, (S i).card = q + 1) → (∀ i j : Fin n, i ≠ j → (S i ∩ S j).card = 1) → (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin n, p ∈ S i ∧ p' ∈ S i) → (∀ j : Fin (h + 1), (K j).card = (2 ^ (j : ℕ) - 1) * q + 2 ^ (j : ℕ)) → (∀ (j : Fin (h + 1)) (i : Fin n), (S i ∩ K j).card = 0 ∨ (S i ∩ K j).card = 2 ^ (j : ℕ)) → (∀ j j' : Fin (h + 1), j ≤ j' → K j ⊆ K j') → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin n → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin t → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin t, ι j = i) → (∀ (w : Fin n) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then n else if uv.1 = h + 2 then 0 else q * (q + 1) / 2 ^ (uv.1 - 1) - q) - (if uv.2 = 0 then n else if uv.2 = h + 2 then 0 else q * (q + 1) / 2 ^ (uv.2 - 1) - q)) * (if uv.2 = h + 2 then q else 2 ^ (uv.2 - 1) - 1)))).min) ≤ gates.length := by
  classical
  intro h q n t S K _hh hq hn hS hcross hjoin hKcard hmeet hKm gates out hc hnot hout
  have hall : ∀ g ∈ gates, Allowed g := hc
  let input (a : Fin (h+3)) (v : Fin n) : Bool := decide (v ∈ Incidence.level K a.val)
  have input_mono (a b : Fin (h+3)) (hab : a ≤ b) (v : Fin n)
      (hv : input a v = true) : input b v = true := by
    exact decide_eq_true (Incidence.level_mono K hKm hab (of_decide_eq_true hv))
  let tr (i : Fin (notIndices gates).card) (a : Fin (h+3)) : Bool :=
    trace gates (input a) (notEmbedding gates i)
  have tr_antitone (i : Fin (notIndices gates).card) (a b : Fin (h+3)) (hab : a ≤ b)
      (hprev : ∀ j : Fin (notIndices gates).card, j < i → tr j a = tr j b) :
      tr i b = true → tr i a = true :=
    trace_after gates input input_mono hall i a b hab hprev
  obtain ⟨P, hP, hPcount, hagree⟩ := existsCuts tr tr_antitone
  have hPcount' : P.card + 1 ≤ 2^t :=
    hPcount.trans (Nat.pow_le_pow_right (by decide) (card_notIndices gates t hnot))
  have hpos : 0 < q := by rw [hq]; positivity
  have hreg := Incidence.through_card S hn hpos hS hcross hjoin
  have hcounts (a : Fin (h+3)) :
      (Incidence.missed S (Incidence.level K a.val)).card =
        Incidence.missValue h q n a.val :=
    Incidence.missed_level_card S K hn hq hS hreg hKcard hmeet a.val (by omega)
  let cost (uv : ℕ × ℕ) : ℕ :=
    (Incidence.missValue h q n uv.1 - Incidence.missValue h q n uv.2) *
      Incidence.windowCharge h q uv.2
  have costs (a b : Fin (h+3)) (hab : a ≤ b)
      (hnone : ∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) : cost (a.val, b.val) ≤ gates.length := by
    have hnotagree := trace_agrees gates (input a) (input b) (hagree a b hab hnone)
    have hsize (i : Fin n) (ha : Disjoint (S i) (Incidence.level K a.val))
        (hb : ¬ Disjoint (S i) (Incidence.level K b.val)) :
        (S i ∩ Incidence.level K b.val).card - 1 = Incidence.windowCharge h q b.val := by
      have hi : i ∈ Incidence.missed S (Incidence.level K a.val) \
          Incidence.missed S (Incidence.level K b.val) := by
        simp [Incidence.missed, ha, hb]
      have hl := Incidence.window_lines S K q a.val b.val hS hmeet (by omega) hi
      omega
    have hcost := window_cost S (Incidence.level K a.val) (Incidence.level K b.val)
      (Incidence.level_mono K hKm hab) gates out hall (fun i j hij => (hcross i j hij).le)
      hout hnotagree (Incidence.windowCharge h q b.val) hsize
    change ((Incidence.missed S (Incidence.level K a.val)).card -
      (Incidence.missed S (Incidence.level K b.val)).card) *
        Incidence.windowCharge h q b.val ≤ gates.length at hcost
    simpa only [cost, hcounts] using hcost
  simpa only [cost, Incidence.missValue, Incidence.windowCharge] using
    cutGame_le (h+3) t gates.length cost P hP hPcount' costs
