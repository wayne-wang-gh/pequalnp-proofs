import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace PEqualNP.Outside.L_meta_244

open PEqualNP.MetaComplexity

def bWires (gs : List BinaryGate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w

lemma bWires_nil (w : List Bool) : bWires [] w = w := rfl

lemma bWires_cons (g : BinaryGate) (gs : List BinaryGate) (w : List Bool) :
    bWires (g :: gs) w =
      bWires gs (w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) := rfl

lemma bWires_append (gs₁ gs₂ : List BinaryGate) (w : List Bool) :
    bWires (gs₁ ++ gs₂) w = bWires gs₂ (bWires gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, bWires_cons, ih]

lemma bWires_length (gs : List BinaryGate) (w : List Bool) :
    (bWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [bWires]
  | cons g gs ih =>
    rw [bWires_cons, ih]
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

lemma bWires_getD_lt (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (bWires gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [bWires_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

abbrev Stat := Bool ⊕ (ℕ × Bool)

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr (j, neg) => xor (w.getD j false) neg

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr (j, _) => j < m

def simplifyUnary (f : Bool → Bool) (j : ℕ) : Option BinaryGate × Stat :=
  if f false == f true then (none, Sum.inl (f false))
  else (none, Sum.inr (j, f false))

lemma simplifyUnary_none (f : Bool → Bool) (j : ℕ) : (simplifyUnary f j).1 = none := by
  unfold simplifyUnary; split_ifs <;> rfl

lemma simplifyUnary_sound (f : Bool → Bool) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    statValid w.length (simplifyUnary f j).2 ∧
    statVal w (simplifyUnary f j).2 = f (w.getD j false) := by
  unfold simplifyUnary
  by_cases h : (f false == f true) = true
  · rw [if_pos h]
    have heq : f false = f true := beq_iff_eq.mp h
    refine ⟨trivial, ?_⟩
    simp only [statVal]
    cases hb : w.getD j false
    · rfl
    · exact heq
  · rw [if_neg h]
    have hne : f false ≠ f true := fun e => h (beq_iff_eq.mpr e)
    refine ⟨hj, ?_⟩
    simp only [statVal]
    cases hb : w.getD j false <;> cases hf0 : f false <;> cases hf1 : f true <;>
      simp_all

def simplifyBGate (op : Bool → Bool → Bool) (m : ℕ) (sL sR : Stat) :
    Option BinaryGate × Stat :=
  match sL, sR with
  | Sum.inl cL, Sum.inl cR => (none, Sum.inl (op cL cR))
  | Sum.inl cL, Sum.inr (j, negR) => simplifyUnary (fun b => op cL (xor b negR)) j
  | Sum.inr (i, negL), Sum.inl cR => simplifyUnary (fun a => op (xor a negL) cR) i
  | Sum.inr (i, negL), Sum.inr (j, negR) =>
    (some ⟨fun a b => op (xor a negL) (xor b negR), i, j⟩, Sum.inr (m, false))

lemma simplifyBGate_none_left (op : Bool → Bool → Bool) (m : ℕ) (c : Bool) (sR : Stat) :
    (simplifyBGate op m (Sum.inl c) sR).1 = none := by
  cases sR with
  | inl cR => rfl
  | inr p => exact simplifyUnary_none _ _

lemma simplifyBGate_none_right (op : Bool → Bool → Bool) (m : ℕ) (sL : Stat) (c : Bool) :
    (simplifyBGate op m sL (Sum.inl c)).1 = none := by
  cases sL with
  | inl cL => rfl
  | inr p => exact simplifyUnary_none _ _

lemma simplifyBGate_const_left (op : Bool → Bool → Bool) (m : ℕ) (c : Bool) (sR : Stat)
    (hconst : op c false = op c true) :
    simplifyBGate op m (Sum.inl c) sR = (none, Sum.inl (op c false)) := by
  cases sR with
  | inl cR =>
    cases cR
    · rfl
    · simp [simplifyBGate, hconst]
  | inr p =>
    obtain ⟨j, negR⟩ := p
    simp only [simplifyBGate, simplifyUnary]
    cases negR
    · simp [hconst]
    · simp [hconst]

lemma simplifyBGate_const_right (op : Bool → Bool → Bool) (m : ℕ) (sL : Stat) (c : Bool)
    (hconst : op false c = op true c) :
    simplifyBGate op m sL (Sum.inl c) = (none, Sum.inl (op false c)) := by
  cases sL with
  | inl cL =>
    cases cL
    · rfl
    · simp [simplifyBGate, hconst]
  | inr p =>
    obtain ⟨i, negL⟩ := p
    simp only [simplifyBGate, simplifyUnary]
    cases negL
    · simp [hconst]
    · simp [hconst]

lemma simplifyBGate_const_both (op : Bool → Bool → Bool) (m : ℕ) (cL cR : Bool) :
    simplifyBGate op m (Sum.inl cL) (Sum.inl cR) = (none, Sum.inl (op cL cR)) := rfl

lemma simplifyBGate_sound (op : Bool → Bool → Bool) (w : List Bool) (sL sR : Stat)
    (hL : statValid w.length sL) (hR : statValid w.length sR) :
    statValid (w.length + (simplifyBGate op w.length sL sR).1.toList.length)
      (simplifyBGate op w.length sL sR).2 ∧
    statVal (bWires (simplifyBGate op w.length sL sR).1.toList w)
      (simplifyBGate op w.length sL sR).2 = op (statVal w sL) (statVal w sR) := by
  cases sL with
  | inl cL =>
    cases sR with
    | inl cR =>
      simp [simplifyBGate, statValid, statVal]
    | inr pR =>
      obtain ⟨j, negR⟩ := pR
      have hu := simplifyUnary_sound (fun b => op cL (xor b negR)) w j hR
      simp only [simplifyBGate, simplifyUnary_none, Option.toList_none, List.length_nil,
        Nat.add_zero, bWires_nil, statVal]
      exact hu
  | inr pL =>
    obtain ⟨i, negL⟩ := pL
    cases sR with
    | inl cR =>
      have hu := simplifyUnary_sound (fun a => op (xor a negL) cR) w i hL
      simp only [simplifyBGate, simplifyUnary_none, Option.toList_none, List.length_nil,
        Nat.add_zero, bWires_nil, statVal]
      exact hu
    | inr pR =>
      obtain ⟨j, negR⟩ := pR
      simp only [simplifyBGate, Option.toList_some, List.length_singleton, statValid, statVal,
        bWires_cons, bWires_nil, getD_snoc_eq _ _ _ _ rfl, Bool.xor_false]
      exact ⟨by omega, trivial⟩

def elimStep (m : ℕ) (acc : List Stat × List BinaryGate) (g : BinaryGate) :
    List Stat × List BinaryGate :=
  let r := simplifyBGate g.op (m + acc.2.length)
    (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimPass (m : ℕ) (gs : List BinaryGate) (acc : List Stat × List BinaryGate) :
    List Stat × List BinaryGate :=
  gs.foldl (elimStep m) acc

lemma elimPass_nil (m : ℕ) (acc : List Stat × List BinaryGate) :
    elimPass m [] acc = acc := rfl

lemma elimPass_cons (m : ℕ) (g : BinaryGate) (gs : List BinaryGate)
    (acc : List Stat × List BinaryGate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List BinaryGate)
    (acc : List Stat × List BinaryGate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

lemma elimPass_fst_len (m : ℕ) (gs : List BinaryGate) (acc : List Stat × List BinaryGate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

lemma elimPass_getD_lt (m k : ℕ) (d : Stat) (gs : List BinaryGate)
    (acc : List Stat × List BinaryGate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimPass_len (m : ℕ) (gs : List BinaryGate) (acc : List Stat × List BinaryGate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyBGate g.op (m + acc.2.length)
        (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1
      omega
    omega

def readsWire (k : ℕ) (g : BinaryGate) : Bool :=
  decide (g.left = k ∨ g.right = k)

lemma elimStep_none_of_reads (m k : ℕ) (acc : List Stat × List BinaryGate) (g : BinaryGate)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) (hr : readsWire k g = true) :
    (elimStep m acc g).2.length = acc.2.length := by
  obtain ⟨c, hc⟩ := hc
  simp only [readsWire, decide_eq_true_eq] at hr
  rcases hr with hl | hr
  · have hnone : (simplifyBGate g.op (m + acc.2.length)
        (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1 = none := by
      rw [hl, hc]; exact simplifyBGate_none_left _ _ _ _
    simp only [elimStep, hnone, Option.toList_none, List.append_nil]
  · have hnone : (simplifyBGate g.op (m + acc.2.length)
        (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1 = none := by
      rw [hr, hc]; exact simplifyBGate_none_right _ _ _ _
    simp only [elimStep, hnone, Option.toList_none, List.append_nil]

lemma elimPass_len_lt (m k : ℕ) (gs : List BinaryGate) (acc : List Stat × List BinaryGate)
    (hk : k < acc.1.length) (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, readsWire k g = true) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : readsWire k g = true
    · have h2 := elimStep_none_of_reads m k acc g hc hkg
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, readsWire k g' = true := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (by simp [elimStep]; omega)
        (by obtain ⟨c, hc⟩ := hc; exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyBGate g.op (m + acc.2.length)
          (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1
        omega
      omega

lemma elimPass_len_two_pred (m : ℕ) (P : BinaryGate → Bool) (gs : List BinaryGate)
    (acc : List Stat × List BinaryGate)
    (hP : ∀ g ∈ gs, P g = true → ∀ acc' : List Stat × List BinaryGate,
      (∀ i < acc.1.length, acc'.1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false)) →
      (elimStep m acc' g).2.length = acc'.2.length)
    (htwo : 2 ≤ (gs.filter P).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  have h1 : ∀ (gs' : List BinaryGate) (acc' : List Stat × List BinaryGate),
      (∀ g ∈ gs', P g = true → ∀ acc'' : List Stat × List BinaryGate,
        (∀ i < acc'.1.length, acc''.1.getD i (Sum.inl false) = acc'.1.getD i (Sum.inl false)) →
        (elimStep m acc'' g).2.length = acc''.2.length) →
      1 ≤ (gs'.filter P).length →
      (elimPass m gs' acc').2.length + 1 ≤ acc'.2.length + gs'.length := by
    intro gs'
    induction gs' with
    | nil => intro acc' _ h; simp at h
    | cons g gs' ih =>
      intro acc' hP' hcnt
      rw [elimPass_cons, List.length_cons]
      cases hPg : P g with
      | true =>
        have hstep := hP' g List.mem_cons_self hPg acc' (fun _ _ => rfl)
        have := elimPass_len m gs' (elimStep m acc' g)
        omega
      | false =>
        have hcnt' : 1 ≤ (gs'.filter P).length := by simpa [hPg] using hcnt
        have hih := ih (elimStep m acc' g) (fun g' hg' hPg' acc'' hacc'' =>
          hP' g' (List.mem_cons_of_mem _ hg') hPg' acc'' (fun i hi => by
            rw [hacc'' i (by simp [elimStep]; omega)]
            exact getD_snoc_lt _ _ _ _ hi)) hcnt'
        have h2 : (elimStep m acc' g).2.length ≤ acc'.2.length + 1 := by
          simp only [elimStep, List.length_append]
          have := toList_opt_len_le (simplifyBGate g.op (m + acc'.2.length)
            (acc'.1.getD g.left (Sum.inl false)) (acc'.1.getD g.right (Sum.inl false))).1
          omega
        omega
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    cases hPg : P g with
    | true =>
      have hstep := hP g List.mem_cons_self hPg acc (fun _ _ => rfl)
      have hcnt' : 1 ≤ (gs.filter P).length := by
        simp only [List.filter_cons, hPg, ↓reduceIte, List.length_cons] at htwo
        omega
      have hrest := h1 gs (elimStep m acc g) (fun g' hg' hPg' acc'' hacc'' =>
        hP g' (List.mem_cons_of_mem _ hg') hPg' acc'' (fun i hi => by
          rw [hacc'' i (by simp [elimStep]; omega)]
          exact getD_snoc_lt _ _ _ _ hi)) hcnt'
      omega
    | false =>
      have htwo' : 2 ≤ (gs.filter P).length := by simpa [hPg] using htwo
      have hih := ih (elimStep m acc g) (fun g' hg' hPg' acc'' hacc'' =>
        hP g' (List.mem_cons_of_mem _ hg') hPg' acc'' (fun i hi => by
          rw [hacc'' i (by simp [elimStep]; omega)]
          exact getD_snoc_lt _ _ _ _ hi)) htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyBGate g.op (m + acc.2.length)
          (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1
        omega
      omega

def ElimInvOn (B : Set ℕ) (m : ℕ) (w_in w_old : List Bool)
    (acc : List Stat × List BinaryGate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ, i ∉ B →
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (bWires acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

lemma elimInvOn_step (B : Set ℕ) (m : ℕ) (w_in w_old : List Bool)
    (acc : List Stat × List BinaryGate) (g : BinaryGate)
    (hLnot : g.left ∉ B) (hRnot : g.right ∉ B)
    (hinv : ElimInvOn B m w_in w_old acc) :
    ElimInvOn B m w_in (w_old ++ [g.op (w_old.getD g.left false) (w_old.getD g.right false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := bWires acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, bWires_length, hwin]
  have hsound := simplifyBGate_sound g.op w_new
    (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))
    (by rw [hw_len]; exact (hi g.left hLnot).1) (by rw [hw_len]; exact (hi g.right hRnot).1)
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i hiB
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]; exact hsound.1
    · rw [bWires_append, ← hw_new, hsound.2, (hi g.left hLnot).2, (hi g.right hRnot).2]
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i hiB
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr p =>
        obtain ⟨j, neg⟩ := p
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => rw [hst] at hval; exact hval
      | inr p =>
        obtain ⟨j, neg⟩ := p
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [bWires_append, ← hw_new, bWires_getD_lt _ _ _ (by omega)]
        exact hval

lemma elimInvOn_pass (B : Set ℕ) (m : ℕ) (w_in : List Bool) (gs : List BinaryGate)
    (w_old : List Bool) (acc : List Stat × List BinaryGate)
    (hread : ∀ g ∈ gs, g.left ∉ B ∧ g.right ∉ B)
    (hinv : ElimInvOn B m w_in w_old acc) :
    ElimInvOn B m w_in (bWires gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [bWires_cons, elimPass_cons]
    have h0 := hread g List.mem_cons_self
    exact ih _ _ (fun g' hg' => hread g' (List.mem_cons_of_mem _ hg'))
      (elimInvOn_step B m w_in w_old acc g h0.1 h0.2 hinv)

lemma bWires_agree (gs : List BinaryGate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, g.left ∉ B ∧ g.right ∉ B) :
    (bWires gs w₁).length = (bWires gs w₂).length ∧
    ∀ i ∉ B, (bWires gs w₁).getD i false = (bWires gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [bWires_cons, bWires_cons]
    have h0 := hread g List.mem_cons_self
    rw [hagree g.left h0.1, hagree g.right h0.2]
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
    · intro g' hg'; exact hread g' (List.mem_cons_of_mem _ hg')

def flipGate (target : ℕ) (g : BinaryGate) : BinaryGate :=
  ⟨fun a b => g.op (if g.left = target then !a else a) (if g.right = target then !b else b),
   g.left, g.right⟩

lemma bWires_flip_tail (gs : List BinaryGate) (target : ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (ht : target < w₁.length)
    (hdiff : w₂.getD target false = !(w₁.getD target false))
    (hsame : ∀ i, i ≠ target → w₂.getD i false = w₁.getD i false) :
    ∀ i, (bWires (gs.map (flipGate target)) w₂).getD i false =
      if i = target then !(bWires gs w₁).getD i false else (bWires gs w₁).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil =>
    intro i
    by_cases hi : i = target
    · subst hi; simp only [bWires_nil, ↓reduceIte]; exact hdiff
    · simp only [bWires_nil, hi, ↓reduceIte]; exact hsame i hi
  | cons g gs ih =>
    rw [List.map_cons, bWires_cons, bWires_cons]
    have hval : (flipGate target g).op (w₂.getD (flipGate target g).left false)
          (w₂.getD (flipGate target g).right false) =
        g.op (w₁.getD g.left false) (w₁.getD g.right false) := by
      simp only [flipGate]
      congr 1
      · by_cases hl : g.left = target
        · simp only [hl, ↓reduceIte]; rw [hdiff, Bool.not_not]
        · simp only [hl, ↓reduceIte]; exact hsame _ hl
      · by_cases hr : g.right = target
        · simp only [hr, ↓reduceIte]; rw [hdiff, Bool.not_not]
        · simp only [hr, ↓reduceIte]; exact hsame _ hr
    rw [hval]
    apply ih
    · simp [hlen]
    · simp; omega
    · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ ht]; exact hdiff
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ hlt]; exact hsame i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ (by omega), getD_snoc_eq _ _ _ _ heq]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma negate_wire {m : ℕ} (gs : List BinaryGate) (j : ℕ) (hj1 : m ≤ j) (hj2 : j < m + gs.length) :
    ∃ gs' : List BinaryGate, gs'.length = gs.length ∧
      ∀ x : Fin m → Bool, (bWires gs' (List.ofFn x)).getD j false =
        !((bWires gs (List.ofFn x)).getD j false) := by
  set k := j - m with hk
  have hkl : k < gs.length := by omega
  have hsplit : gs = gs.take k ++ [gs[k]] ++ gs.drop (k + 1) := by simp
  set g0 : BinaryGate := ⟨fun a b => !(gs[k].op a b), gs[k].left, gs[k].right⟩ with hg0
  refine ⟨gs.take k ++ [g0] ++ (gs.drop (k + 1)).map (flipGate j), ?_, ?_⟩
  · simp [List.length_take, Nat.min_eq_left hkl.le]
    omega
  · intro x
    set w0 := bWires (gs.take k) (List.ofFn x) with hw0
    have hw0_len : w0.length = j := by
      rw [hw0, bWires_length, List.length_ofFn, List.length_take, Nat.min_eq_left hkl.le]
      omega
    have h1 : bWires (gs.take k ++ [g0] ++ (gs.drop (k + 1)).map (flipGate j)) (List.ofFn x) =
        bWires ((gs.drop (k + 1)).map (flipGate j))
          (w0 ++ [g0.op (w0.getD g0.left false) (w0.getD g0.right false)]) := by
      rw [bWires_append, bWires_append, ← hw0, bWires_cons, bWires_nil]
    have h2 : bWires gs (List.ofFn x) =
        bWires (gs.drop (k + 1))
          (w0 ++ [gs[k].op (w0.getD gs[k].left false) (w0.getD gs[k].right false)]) := by
      conv_lhs => rw [hsplit]
      rw [bWires_append, bWires_append, ← hw0, bWires_cons, bWires_nil]
    rw [h1, h2]
    have hfl := bWires_flip_tail (gs.drop (k + 1)) j
      (w0 ++ [gs[k].op (w0.getD gs[k].left false) (w0.getD gs[k].right false)])
      (w0 ++ [g0.op (w0.getD g0.left false) (w0.getD g0.right false)])
      (by simp) (by simp [hw0_len])
      (by rw [getD_snoc_eq _ _ _ _ hw0_len.symm, getD_snoc_eq _ _ _ _ hw0_len.symm])
      (fun i hi => by
        rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)])
      j
    simpa using hfl

lemma circuit_from_stat {m s : ℕ} {F : (Fin m → Bool) → Bool}
    (gs : List BinaryGate) (st : Stat) (hlen : gs.length ≤ s) (hval_st : statValid (m + gs.length) st)
    (heval : ∀ x : Fin m → Bool, statVal (bWires gs (List.ofFn x)) st = F x)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (hF0 : F (fun _ => false) = false) :
    HasBinarySize m F s := by
  cases st with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := heval x; have hx' := heval x'
    exact absurd (hx.symm.trans hx') hne
  | inr p =>
    obtain ⟨j, neg⟩ := p
    cases neg with
    | false =>
      refine ⟨⟨gs, j⟩, hlen, ?_⟩
      intro x
      have hx := heval x
      simpa [BinaryCircuit.eval, BinaryCircuit.wires, bWires, statVal] using hx
    | true =>
      by_cases hj : j < m
      · exfalso
        have h0 := heval (fun _ => false)
        rw [hF0] at h0
        simp only [statVal] at h0
        rw [bWires_getD_lt _ _ _ (by simp; exact hj), ofFn_getD_lt _ _ _ hj] at h0
        simp at h0
      · obtain ⟨gs', hlen', hev'⟩ := negate_wire gs j (by omega) hval_st
        refine ⟨⟨gs', j⟩, by simp [BinaryCircuit.size, hlen', hlen], ?_⟩
        intro x
        have hx := heval x
        simp only [statVal, Bool.xor_true] at hx
        show (bWires gs' (List.ofFn x)).getD j false = F x
        rw [hev' x]
        exact hx

def initVar (m : ℕ) (v : Fin m) (b : Bool) : List Stat :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i, false)

lemma elimInvOn_initVar (B : Set ℕ) (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInvOn B m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i _
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr (i, false) := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, bWires_nil, Bool.xor_false]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

lemma elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasBinarySize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b))
    (hF0 : F (Function.update (fun _ => false) v b) = false) :
    1 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hsz, hev⟩ := hC
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw : ∀ y : Fin m → Bool,
        (bWires C.gates (List.ofFn (Function.update y v b))).getD (v : ℕ) false = b := by
      intro y
      rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]; simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (bWires C.gates _).getD C.output false = b; rw [heq]; exact hw x
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (bWires C.gates _).getD C.output false = b; rw [heq]; exact hw x'
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ C.gates, readsWire (v : ℕ) g = true := by
    by_contra hno
    push_neg at hno
    obtain ⟨x, hne⟩ := hdep
    have hag := bWires_agree C.gates {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp) (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi; simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := fun h => hi (congrArg Fin.val h)
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg
        have hr := hno g hg
        simp only [readsWire, ne_eq, decide_eq_true_eq, not_or] at hr
        exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
    have hEq := hag.2 C.output (by simpa using hout_ne)
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m C.gates (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ C.gates.length := by
    have := elimPass_len_lt m (v : ℕ) C.gates (initVar m v b, [])
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hinv : ∀ x : Fin m → Bool,
      ElimInvOn ∅ m (List.ofFn x) (bWires C.gates (List.ofFn (Function.update x v b))) acc :=
    fun x => elimInvOn_pass ∅ m (List.ofFn x) C.gates _ (initVar m v b, [])
      (fun _ _ => ⟨by simp, by simp⟩) (elimInvOn_initVar ∅ m v b x)
  have hst_val : statValid (m + acc.2.length) (acc.1.getD C.output (Sum.inl false)) :=
    ((hinv (fun _ => false)).2.2 C.output (by simp)).1
  have heval_acc : ∀ x : Fin m → Bool,
      statVal (bWires acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    rw [((hinv x).2.2 C.output (by simp)).2]
    exact hev (Function.update x v b)
  exact ⟨by omega, circuit_from_stat acc.2 (acc.1.getD C.output (Sum.inl false)) (by omega)
    hst_val heval_acc hnc hF0⟩

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
      rw [hnil] at this; simp at this
    | false =>
      have h1 : (xs.filter p).length = 1 := by simpa [hpx] using h
      obtain ⟨l₁, a, l₂, rfl, hpa, hl₁, hl₂⟩ := ih h1
      refine ⟨x :: l₁, a, l₂, by simp, hpa, ?_, hl₂⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hpx
      · exact hl₁ y hy'

lemma xor_diag_const (op : Bool → Bool → Bool)
    (hL0 : op false false ≠ op false true) (hL1 : op true false ≠ op true true)
    (hR0 : op false false ≠ op true false) (hR1 : op false true ≠ op true true) :
    ∀ a : Bool, op a a = op false false := by
  intro a
  cases a
  · rfl
  · cases h00 : op false false <;> cases h01 : op false true <;>
      cases h10 : op true false <;> cases h11 : op true true <;> simp_all

lemma op_xor_of_nonconst_left (op : Bool → Bool → Bool)
    (hL0 : op false false ≠ op false true) (hL1 : op true false ≠ op true true)
    (hdepL : ¬ ∀ b : Bool, op false b = op true b) :
    op false false ≠ op true false ∧ op false true ≠ op true true := by
  cases h00 : op false false <;> cases h01 : op false true <;>
    cases h10 : op true false <;> cases h11 : op true true <;>
    simp_all [Bool.forall_bool]

lemma op_xor_of_nonconst_right (op : Bool → Bool → Bool)
    (hR0 : op false false ≠ op true false) (hR1 : op false true ≠ op true true)
    (hdepR : ¬ ∀ a : Bool, op a false = op a true) :
    op false false ≠ op false true ∧ op true false ≠ op true true := by
  cases h00 : op false false <;> cases h01 : op false true <;>
    cases h10 : op true false <;> cases h11 : op true true <;>
    simp_all [Bool.forall_bool]

lemma bWires_pair_factor {m : ℕ} (gs₁ gs₂ : List BinaryGate) (g₁ : BinaryGate)
    (ℓ p : Fin m) (hgs₁ : ∀ g ∈ gs₁, readsWire ℓ g = false ∧ readsWire p g = false)
    (hgs₂ : ∀ g ∈ gs₂, readsWire ℓ g = false ∧ readsWire p g = false)
    (x y : Fin m → Bool)
    (hxy : ∀ i : Fin m, i ≠ ℓ → i ≠ p → x i = y i)
    (hw1 : (bWires (gs₁ ++ [g₁]) (List.ofFn x)).getD (m + gs₁.length) false =
           (bWires (gs₁ ++ [g₁]) (List.ofFn y)).getD (m + gs₁.length) false)
    (o : ℕ) (hoℓ : o ≠ ℓ) (hop : o ≠ p) :
    (bWires (gs₁ ++ [g₁] ++ gs₂) (List.ofFn x)).getD o false =
    (bWires (gs₁ ++ [g₁] ++ gs₂) (List.ofFn y)).getD o false := by
  have hag1 := bWires_agree gs₁ {(ℓ : ℕ), (p : ℕ)} (List.ofFn x) (List.ofFn y)
    (by simp)
    (by intro b hb; rcases hb with rfl | rfl <;> simp)
    (by
      intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
      by_cases hlt : i < m
      · have h1 : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi.1 (congrArg Fin.val h)
        have h2 : (⟨i, hlt⟩ : Fin m) ≠ p := fun h => hi.2 (congrArg Fin.val h)
        rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt, hxy _ h1 h2]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
    (by
      intro g hg
      have ⟨h1, h2⟩ := hgs₁ g hg
      simp only [readsWire, decide_eq_false_iff_not, not_or] at h1 h2
      exact ⟨by simp [h1.1, h2.1], by simp [h1.2, h2.2]⟩)
  have hlen1 : (bWires (gs₁ ++ [g₁]) (List.ofFn x)).length =
      (bWires (gs₁ ++ [g₁]) (List.ofFn y)).length := by
    simp [bWires_length]
  have hag2 := bWires_agree gs₂ {(ℓ : ℕ), (p : ℕ)}
    (bWires (gs₁ ++ [g₁]) (List.ofFn x))
    (bWires (gs₁ ++ [g₁]) (List.ofFn y))
    hlen1
    (by intro b hb; rw [bWires_length, List.length_ofFn]; rcases hb with rfl | rfl <;> omega)
    (by
      intro i hi
      by_cases hieq : i = m + gs₁.length
      · subst hieq; exact hw1
      · have hlen_g1x : (bWires gs₁ (List.ofFn x)).length = m + gs₁.length := by
          rw [bWires_length, List.length_ofFn]
        have hlen_g1y : (bWires gs₁ (List.ofFn y)).length = m + gs₁.length := by
          rw [bWires_length, List.length_ofFn]
        rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil,
            getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
        exact hag1.2 i hi)
    (by
      intro g hg
      have ⟨h1, h2⟩ := hgs₂ g hg
      simp only [readsWire, decide_eq_false_iff_not, not_or] at h1 h2
      exact ⟨by simp [h1.1, h2.1], by simp [h1.2, h2.2]⟩)
  rw [bWires_append (gs₁ ++ [g₁]) gs₂, bWires_append (gs₁ ++ [g₁]) gs₂]
  exact hag2.2 o (by simp [hoℓ, hop])

lemma elim_leaf_parent {m s : ℕ} {F : (Fin m → Bool) → Bool} (ℓ p q : Fin m)
    (hℓp : ℓ ≠ p) (hqℓ : q ≠ ℓ) (hqp : q ≠ p)
    (hC : HasBinarySize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x ℓ false) ≠ F (Function.update x ℓ true))
    (hnc0 : ∃ x x' : Fin m → Bool, F (Function.update x ℓ false) ≠ F (Function.update x' ℓ false))
    (hnc1 : ∃ x x' : Fin m → Bool, F (Function.update x ℓ true) ≠ F (Function.update x' ℓ true))
    (hncp : ∃ x x' : Fin m → Bool, F (Function.update x p false) ≠ F (Function.update x' p false))
    (hF0_0 : F (Function.update (fun _ => false) ℓ false) = false)
    (hF0_1 : F (Function.update (fun _ => false) ℓ true) = false)
    (hF0_p : F (Function.update (fun _ => false) p false) = false)
    (hkill : ∀ x : Fin m → Bool, ∀ b : Bool,
      F (Function.update (Function.update x p false) ℓ b) = F (Function.update x p false))
    (h3sub : ∀ (x₀ : Fin m → Bool), (∀ i, i ≠ ℓ → i ≠ p → i ≠ q → x₀ i = false) →
      F (Function.update (Function.update (Function.update x₀ p false) ℓ false) q false) = false ∧
      F (Function.update (Function.update (Function.update x₀ p false) ℓ false) q true) = false ∧
      F (Function.update (Function.update (Function.update x₀ p true) ℓ false) q false) = false ∧
      F (Function.update (Function.update (Function.update x₀ p true) ℓ false) q true) = true ∧
      F (Function.update (Function.update (Function.update x₀ p true) ℓ true) q false) = true ∧
      F (Function.update (Function.update (Function.update x₀ p true) ℓ true) q true) = true) :
    (2 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x ℓ false)) (s - 2)) ∨
    (2 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x ℓ true)) (s - 2)) ∨
    (3 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x p false)) (s - 3)) := by
  obtain ⟨C, hsz, hev⟩ := hC
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne_ℓ : C.output ≠ (ℓ : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc0
    have hw : ∀ y : Fin m → Bool,
        (bWires C.gates (List.ofFn (Function.update y ℓ false))).getD (ℓ : ℕ) false = false := by
      intro y; rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt]; simp
    have e1 : F (Function.update x ℓ false) = false := by
      rw [← hev]; show (bWires C.gates _).getD C.output false = false; rw [heq]; exact hw x
    have e2 : F (Function.update x' ℓ false) = false := by
      rw [← hev]; show (bWires C.gates _).getD C.output false = false; rw [heq]; exact hw x'
    exact hne (e1.trans e2.symm)
  have hout_ne_p : C.output ≠ (p : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hncp
    have hw : ∀ y : Fin m → Bool,
        (bWires C.gates (List.ofFn (Function.update y p false))).getD (p : ℕ) false = false := by
      intro y; rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ p.isLt]; simp
    have e1 : F (Function.update x p false) = false := by
      rw [← hev]; show (bWires C.gates _).getD C.output false = false; rw [heq]; exact hw x
    have e2 : F (Function.update x' p false) = false := by
      rw [← hev]; show (bWires C.gates _).getD C.output false = false; rw [heq]; exact hw x'
    exact hne (e1.trans e2.symm)
  set cnt := (C.gates.filter (readsWire (ℓ : ℕ))).length with hcnt
  by_cases hge2 : 2 ≤ cnt
  · set acc := elimPass m C.gates (initVar m ℓ false, []) with hacc
    have hlen : acc.2.length + 2 ≤ C.gates.length := by
      have := elimPass_len_two_pred m (readsWire (ℓ : ℕ)) C.gates (initVar m ℓ false, [])
        (fun g _ hr acc' hacc' =>
          elimStep_none_of_reads m (ℓ : ℕ) acc' g
            ⟨false, by rw [hacc' (ℓ : ℕ) (by simp [initVar]), initVar, ofFn_getD_lt _ _ _ ℓ.isLt]; simp⟩ hr)
        (by rw [← hcnt]; exact hge2)
      rw [← hacc] at this
      simpa using this
    have hinv : ∀ x : Fin m → Bool,
        ElimInvOn ∅ m (List.ofFn x) (bWires C.gates (List.ofFn (Function.update x ℓ false))) acc :=
      fun x => elimInvOn_pass ∅ m (List.ofFn x) C.gates _ (initVar m ℓ false, [])
        (fun _ _ => ⟨by simp, by simp⟩) (elimInvOn_initVar ∅ m ℓ false x)
    exact Or.inl ⟨by omega, circuit_from_stat acc.2 (acc.1.getD C.output (Sum.inl false)) (by omega)
      ((hinv (fun _ => false)).2.2 C.output (by simp)).1
      (fun x => by rw [((hinv x).2.2 C.output (by simp)).2]; exact hev _) hnc0 hF0_0⟩
  · by_cases hzero : cnt = 0
    · exfalso
      have hnil : C.gates.filter (readsWire (ℓ : ℕ)) = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcnt]; exact hzero)
      obtain ⟨x, hne⟩ := hdep
      have hag := bWires_agree C.gates {(ℓ : ℕ)}
        (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
        (by simp) (by intro u hu; simp at hu; subst hu; simp)
        (by
          intro i hi; simp at hi
          by_cases hlt : i < m
          · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
            rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                Function.update_of_ne hne', Function.update_of_ne hne']
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg
          have hno : readsWire (ℓ : ℕ) g = false := by
            by_contra hr
            have hrt : readsWire (ℓ : ℕ) g = true := by cases h : readsWire (ℓ : ℕ) g <;> simp_all
            have : g ∈ C.gates.filter (readsWire (ℓ : ℕ)) := List.mem_filter.2 ⟨hg, hrt⟩
            rw [hnil] at this; simp at this
          simp only [readsWire, decide_eq_false_iff_not, not_or] at hno
          exact ⟨by simpa using hno.1, by simpa using hno.2⟩)
      exact hne ((hev _).symm.trans ((hag.2 C.output (by simpa using hout_ne_ℓ)).trans (hev _)))
    · have hone : (C.gates.filter (readsWire (ℓ : ℕ))).length = 1 := by rw [← hcnt]; omega
      obtain ⟨gs₁, g₁, gs₂, hsplit, hg₁in, hgs₁no, hgs₂no⟩ :=
        list_split_unique_filter (readsWire (ℓ : ℕ)) C.gates hone
      set w₁ := m + gs₁.length with hw₁
      have hex₂_w₁ : C.output ≠ w₁ → ∃ g ∈ gs₂, readsWire w₁ g = true := by
        intro hout_ne_w1
        by_contra hno₂
        push_neg at hno₂
        obtain ⟨x, hne⟩ := hdep
        have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
          (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
          (by simp) (by intro u hu; simp at hu; subst hu; simp)
          (by
            intro i hi; simp at hi
            by_cases hlt : i < m
            · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
              rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                  Function.update_of_ne hne', Function.update_of_ne hne']
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)])
          (by
            intro g hg
            have hr := hgs₁no g hg
            simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
            exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
        have hag2 := bWires_agree gs₂ {(ℓ : ℕ), w₁}
          (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ false)))
          (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ true)))
          (by simp [bWires_length])
          (by intro b hb; rw [bWires_length, List.length_ofFn, List.length_append, List.length_singleton]; rcases hb with rfl | rfl <;> omega)
          (by
            intro i hi
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
            rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil]
            have hl1 : (bWires gs₁ (List.ofFn (Function.update x ℓ false))).length = w₁ := by
              rw [bWires_length, List.length_ofFn]
            have hl2 : (bWires gs₁ (List.ofFn (Function.update x ℓ true))).length = w₁ := by
              rw [bWires_length, List.length_ofFn]
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag1.2 i (by simpa using hi.1))
          (by
            intro g hg
            have hr1 := hgs₂no g hg
            have hr2 := hno₂ g hg
            simp only [readsWire, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, not_or] at hr1 hr2
            exact ⟨by simp [hr1.1, hr2.1], by simp [hr1.2, hr2.2]⟩)
        have hEq : (bWires C.gates (List.ofFn (Function.update x ℓ false))).getD C.output false =
            (bWires C.gates (List.ofFn (Function.update x ℓ true))).getD C.output false := by
          rw [hsplit, bWires_append (gs₁ ++ [g₁]) gs₂, bWires_append (gs₁ ++ [g₁]) gs₂]
          exact hag2.2 C.output (by simp [hout_ne_ℓ, hout_ne_w1])
        exact hne ((hev _).symm.trans (hEq.trans (hev _)))
      have hconst_finish : ∀ (b : Bool),
          (∃ c : Bool,
            let acc₁ := elimPass m gs₁ (initVar m ℓ b, [])
            simplifyBGate g₁.op (m + acc₁.2.length)
              (acc₁.1.getD g₁.left (Sum.inl false)) (acc₁.1.getD g₁.right (Sum.inl false)) =
              (none, Sum.inl c)) →
          (2 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x ℓ false)) (s - 2)) ∨
          (2 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x ℓ true)) (s - 2)) := by
        intro b ⟨c, hc⟩
        set acc₁ := elimPass m gs₁ (initVar m ℓ b, []) with hacc₁
        set accM := elimStep m acc₁ g₁ with haccM
        set acc := elimPass m gs₂ accM with hacc
        have hacc_eq : acc = elimPass m C.gates (initVar m ℓ b, []) := by
          rw [hsplit, elimPass_append, elimPass_append, ← hacc₁, elimPass_cons, elimPass_nil, ← haccM]
        have hacc₁_len : acc₁.1.length = w₁ := by rw [hacc₁, elimPass_fst_len]; simp [initVar, hw₁]
        have hmid_len : accM.2.length = acc₁.2.length := by
          simp only [haccM, elimStep, hc, Option.toList_none, List.append_nil]
        have hmid_w₁ : accM.1.getD w₁ (Sum.inl false) = Sum.inl c := by
          simp only [haccM, elimStep, hc]
          exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
        have hinv : ∀ x : Fin m → Bool,
            ElimInvOn ∅ m (List.ofFn x) (bWires C.gates (List.ofFn (Function.update x ℓ b))) acc := by
          intro x; rw [hacc_eq]
          exact elimInvOn_pass ∅ m (List.ofFn x) C.gates _ (initVar m ℓ b, [])
            (fun _ _ => ⟨by simp, by simp⟩) (elimInvOn_initVar ∅ m ℓ b x)
        have hncb : ∃ x x' : Fin m → Bool,
            F (Function.update x ℓ b) ≠ F (Function.update x' ℓ b) := by
          cases b; exact hnc0; exact hnc1
        have hF0b : F (Function.update (fun _ => false) ℓ b) = false := by
          cases b; exact hF0_0; exact hF0_1
        have hout_ne_w1 : C.output ≠ w₁ := by
          intro heq
          have hw1acc : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
            rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, elimStep, hacc₁_len])]
            exact hmid_w₁
          obtain ⟨x, x', hne⟩ := hncb
          have hx := ((hinv x).2.2 C.output (by simp)).2.trans (hev _)
          have hx' := ((hinv x').2.2 C.output (by simp)).2.trans (hev _)
          rw [hw1acc] at hx hx'
          exact hne (hx.symm.trans hx')
        have hex₂ := hex₂_w₁ hout_ne_w1
        have hlen1 : acc₁.2.length ≤ gs₁.length := by
          have := elimPass_len m gs₁ (initVar m ℓ b, [])
          rw [← hacc₁] at this; simpa using this
        have hlen2 : acc.2.length + 1 ≤ accM.2.length + gs₂.length :=
          elimPass_len_lt m w₁ gs₂ accM (by simp [haccM, elimStep, hacc₁_len]) ⟨c, hmid_w₁⟩ hex₂
        have htot : C.gates.length = gs₁.length + 1 + gs₂.length := by rw [hsplit]; simp; omega
        have hres : HasBinarySize m (fun x => F (Function.update x ℓ b)) (s - 2) :=
          circuit_from_stat acc.2 (acc.1.getD C.output (Sum.inl false)) (by omega)
            ((hinv (fun _ => false)).2.2 C.output (by simp)).1
            (fun x => by rw [((hinv x).2.2 C.output (by simp)).2]; exact hev _) hncb hF0b
        cases b
        · exact Or.inl ⟨by omega, hres⟩
        · exact Or.inr ⟨by omega, hres⟩
      have hg₁reads : g₁.left = (ℓ : ℕ) ∨ g₁.right = (ℓ : ℕ) := by
        simpa [readsWire] using hg₁in
      have hacc₁_ℓ : ∀ b : Bool,
          (elimPass m gs₁ (initVar m ℓ b, [])).1.getD (ℓ : ℕ) (Sum.inl false) = Sum.inl b := by
        intro b
        rw [elimPass_getD_lt _ _ _ _ _ (by simp [initVar]), initVar, ofFn_getD_lt _ _ _ ℓ.isLt]
        simp
      by_cases hctrl :
          (g₁.left = (ℓ : ℕ) ∧ g₁.right = (ℓ : ℕ)) ∨
          (g₁.left = (ℓ : ℕ) ∧ (g₁.op false false = g₁.op false true ∨ g₁.op true false = g₁.op true true)) ∨
          (g₁.right = (ℓ : ℕ) ∧ (g₁.op false false = g₁.op true false ∨ g₁.op false true = g₁.op true true))
      · rcases hctrl with ⟨hl, hr⟩ | ⟨hl, h0 | h1⟩ | ⟨hr, h0 | h1⟩
        · refine (hconst_finish false ⟨g₁.op false false, ?_⟩).imp id Or.inl
          dsimp only; rw [hl, hr, hacc₁_ℓ false]; rfl
        · refine (hconst_finish false ⟨g₁.op false false, ?_⟩).imp id Or.inl
          dsimp only; rw [hl, hacc₁_ℓ false]; exact simplifyBGate_const_left _ _ _ _ h0
        · refine (hconst_finish true ⟨g₁.op true false, ?_⟩).imp id Or.inl
          dsimp only; rw [hl, hacc₁_ℓ true]; exact simplifyBGate_const_left _ _ _ _ h1
        · refine (hconst_finish false ⟨g₁.op false false, ?_⟩).imp id Or.inl
          dsimp only; rw [hr, hacc₁_ℓ false]; exact simplifyBGate_const_right _ _ _ _ h0
        · refine (hconst_finish true ⟨g₁.op false true, ?_⟩).imp id Or.inl
          dsimp only; rw [hr, hacc₁_ℓ true]; exact simplifyBGate_const_right _ _ _ _ h1
      · push Not at hctrl
        obtain ⟨hnotboth, hnotL, hnotR⟩ := hctrl
        set u : ℕ := if g₁.left = (ℓ : ℕ) then g₁.right else g₁.left with hu
        have hu_ne_ℓ : u ≠ (ℓ : ℕ) := by
          rcases hg₁reads with hl | hr
          · simp only [hu, hl, ↓reduceIte]; exact hnotboth hl
          · by_cases hl : g₁.left = (ℓ : ℕ)
            · exact absurd hr (hnotboth hl)
            · simp only [hu, hl, ↓reduceIte]; exact hl
        by_cases hu_ge : w₁ ≤ u
        · refine (hconst_finish false ⟨g₁.op false false, ?_⟩).imp id Or.inl
          have hgetu : (elimPass m gs₁ (initVar m ℓ false, [])).1.getD u (Sum.inl false) = Sum.inl false :=
            List.getD_eq_default _ _ (by rw [elimPass_fst_len]; simp [initVar]; omega)
          rcases hg₁reads with hl | hr
          · have hru : g₁.right = u := by simp [hu, hl]
            dsimp only; rw [hl, hru, hacc₁_ℓ false, hgetu]; rfl
          · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
            have hlu : g₁.left = u := by simp [hu, hlne]
            dsimp only; rw [hr, hlu, hacc₁_ℓ false, hgetu]; rfl
        · have hu_lt : u < w₁ := by omega
          have hnotindep :
              (g₁.left = (ℓ : ℕ) → ¬ ∀ b : Bool, g₁.op false b = g₁.op true b) ∧
              (g₁.right = (ℓ : ℕ) → ¬ ∀ a : Bool, g₁.op a false = g₁.op a true) := by
            have hcontra :
                (∀ x : Fin m → Bool,
                  (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ false))).getD w₁ false =
                  (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ true))).getD w₁ false) →
                False := by
              intro hsame_w1
              obtain ⟨x, hne⟩ := hdep
              have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
                (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
                (by simp) (by intro b hb; simp at hb; subst hb; simp)
                (by
                  intro i hi; simp at hi
                  by_cases hlt : i < m
                  · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                    rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                        Function.update_of_ne hne', Function.update_of_ne hne']
                  · rw [List.getD_eq_default _ _ (by simp; omega),
                        List.getD_eq_default _ _ (by simp; omega)])
                (by
                  intro g hg
                  have hr := hgs₁no g hg
                  simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
                  exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
              have hag2 := bWires_agree gs₂ {(ℓ : ℕ)}
                (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ false)))
                (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ true)))
                (by simp [bWires_length])
                (by intro b hb; simp at hb; subst hb; rw [bWires_length, List.length_ofFn, List.length_append, List.length_singleton]; omega)
                (by
                  intro i hi
                  by_cases hiw : i = w₁
                  · subst hiw; exact hsame_w1 x
                  · rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil]
                    have hl1 : (bWires gs₁ (List.ofFn (Function.update x ℓ false))).length = w₁ := by
                      rw [bWires_length, List.length_ofFn]
                    have hl2 : (bWires gs₁ (List.ofFn (Function.update x ℓ true))).length = w₁ := by
                      rw [bWires_length, List.length_ofFn]
                    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
                    exact hag1.2 i hi)
                (by
                  intro g hg
                  have hr := hgs₂no g hg
                  simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
                  exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
              have hEq : (bWires C.gates (List.ofFn (Function.update x ℓ false))).getD C.output false =
                  (bWires C.gates (List.ofFn (Function.update x ℓ true))).getD C.output false := by
                rw [hsplit, bWires_append (gs₁ ++ [g₁]) gs₂, bWires_append (gs₁ ++ [g₁]) gs₂]
                exact hag2.2 C.output (by simpa using hout_ne_ℓ)
              exact hne ((hev _).symm.trans (hEq.trans (hev _)))
            constructor
            · intro hl hind
              apply hcontra; intro x
              have hru : g₁.right = u := by simp [hu, hl]
              have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
                (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
                (by simp) (by intro b hb; simp at hb; subst hb; simp)
                (by
                  intro i hi; simp at hi
                  by_cases hlt : i < m
                  · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                    rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                        Function.update_of_ne hne', Function.update_of_ne hne']
                  · rw [List.getD_eq_default _ _ (by simp; omega),
                        List.getD_eq_default _ _ (by simp; omega)])
                (by
                  intro g hg
                  have hr := hgs₁no g hg
                  simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
                  exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
              rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil,
                  getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn]),
                  getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn]),
                  hru, hag1.2 u (by simpa using hu_ne_ℓ)]
              cases (bWires gs₁ (List.ofFn (Function.update x ℓ false))).getD g₁.left false <;>
                cases (bWires gs₁ (List.ofFn (Function.update x ℓ true))).getD g₁.left false
              · rfl
              · exact hind _
              · exact (hind _).symm
              · rfl
            · intro hr hind
              apply hcontra; intro x
              have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
              have hlu : g₁.left = u := by simp [hu, hlne]
              have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
                (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
                (by simp) (by intro b hb; simp at hb; subst hb; simp)
                (by
                  intro i hi; simp at hi
                  by_cases hlt : i < m
                  · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                    rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                        Function.update_of_ne hne', Function.update_of_ne hne']
                  · rw [List.getD_eq_default _ _ (by simp; omega),
                        List.getD_eq_default _ _ (by simp; omega)])
                (by
                  intro g hg
                  have hr' := hgs₁no g hg
                  simp only [readsWire, decide_eq_false_iff_not, not_or] at hr'
                  exact ⟨by simpa using hr'.1, by simpa using hr'.2⟩)
              rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil,
                  getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn]),
                  getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn]),
                  hlu, hag1.2 u (by simpa using hu_ne_ℓ)]
              cases (bWires gs₁ (List.ofFn (Function.update x ℓ false))).getD g₁.right false <;>
                cases (bWires gs₁ (List.ofFn (Function.update x ℓ true))).getD g₁.right false
              · rfl
              · exact hind _
              · exact (hind _).symm
              · rfl
          have hL0L1R0R1 :
              (g₁.op false false ≠ g₁.op false true ∧ g₁.op true false ≠ g₁.op true true) ∧
              (g₁.op false false ≠ g₁.op true false ∧ g₁.op false true ≠ g₁.op true true) := by
            rcases hg₁reads with hl | hr
            · have hL := hnotL hl
              exact ⟨hL, op_xor_of_nonconst_left g₁.op hL.1 hL.2 (hnotindep.1 hl)⟩
            · have hR := hnotR hr
              exact ⟨op_xor_of_nonconst_right g₁.op hR.1 hR.2 (hnotindep.2 hr), hR⟩
          have hL0 := hL0L1R0R1.1.1
          have hL1 := hL0L1R0R1.1.2
          have hR0 := hL0L1R0R1.2.1
          have hR1 := hL0L1R0R1.2.2
          set c₁ := g₁.op false false with hc₁
          have hdiag : ∀ a : Bool, g₁.op a a = c₁ := xor_diag_const g₁.op hL0 hL1 hR0 hR1
          set acc₁ := elimPass m gs₁ (initVar m p false, []) with hacc₁
          set accM : List Stat × List BinaryGate := (acc₁.1 ++ [Sum.inl c₁], acc₁.2) with haccM
          set acc := elimPass m gs₂ accM with hacc
          have hacc₁_len : acc₁.1.length = w₁ := by
            rw [hacc₁, elimPass_fst_len]; simp [initVar, hw₁]
          have hacc₁_p : acc₁.1.getD (p : ℕ) (Sum.inl false) = Sum.inl false := by
            rw [hacc₁, elimPass_getD_lt _ _ _ _ _ (by simp [initVar]), initVar, ofFn_getD_lt _ _ _ p.isLt]
            simp
          have haccM_p : accM.1.getD (p : ℕ) (Sum.inl false) = Sum.inl false := by
            simp only [haccM]
            rw [getD_snoc_lt _ _ _ _ (by rw [hacc₁_len]; omega)]
            exact hacc₁_p
          have haccM_w₁ : accM.1.getD w₁ (Sum.inl false) = Sum.inl c₁ := by
            simp only [haccM]
            exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
          have hinv_all : ∀ x : Fin m → Bool,
              let x' := Function.update x p false
              let σ := Function.update x' ℓ ((bWires gs₁ (List.ofFn x')).getD u false)
              ElimInvOn {(ℓ : ℕ)} m (List.ofFn x) (bWires C.gates (List.ofFn σ)) acc := by
            intro x
            set x' := Function.update x p false with hx'
            set bval := (bWires gs₁ (List.ofFn x')).getD u false with hbval
            set σ := Function.update x' ℓ bval with hσ
            have hinv0 : ElimInvOn {(ℓ : ℕ)} m (List.ofFn x) (List.ofFn σ) (initVar m p false, []) := by
              refine ⟨by simp, by simp [initVar], ?_⟩
              intro i hi
              simp only [Set.mem_singleton_iff] at hi
              by_cases him : i < m
              · have hiℓ : (⟨i, him⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                have hget : (initVar m p false).getD i (Sum.inl false) =
                    if (⟨i, him⟩ : Fin m) = p then Sum.inl false else Sum.inr (i, false) := by
                  rw [initVar, ofFn_getD_lt _ _ _ him]
                rw [hget]
                by_cases hip : (⟨i, him⟩ : Fin m) = p
                · simp only [hip, ↓reduceIte, statValid, statVal]
                  rw [ofFn_getD_lt _ _ _ him, hσ, Function.update_of_ne hiℓ, hx', hip, Function.update_self]
                  exact ⟨trivial, rfl⟩
                · simp only [hip, ↓reduceIte, statValid, statVal, bWires_nil, Bool.xor_false]
                  refine ⟨by omega, ?_⟩
                  rw [ofFn_getD_lt _ _ _ him, ofFn_getD_lt _ _ _ him, hσ, Function.update_of_ne hiℓ,
                      hx', Function.update_of_ne hip]
              · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
                    List.getD_eq_default _ _ (by simp; omega)]
                exact ⟨trivial, rfl⟩
            have hgs₁_notℓ : ∀ g ∈ gs₁, g.left ∉ ({(ℓ : ℕ)} : Set ℕ) ∧ g.right ∉ ({(ℓ : ℕ)} : Set ℕ) := by
              intro g hg
              have hr := hgs₁no g hg
              simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
              exact ⟨by simpa using hr.1, by simpa using hr.2⟩
            have hgs₂_notℓ : ∀ g ∈ gs₂, g.left ∉ ({(ℓ : ℕ)} : Set ℕ) ∧ g.right ∉ ({(ℓ : ℕ)} : Set ℕ) := by
              intro g hg
              have hr := hgs₂no g hg
              simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
              exact ⟨by simpa using hr.1, by simpa using hr.2⟩
            have hinv1 := elimInvOn_pass {(ℓ : ℕ)} m (List.ofFn x) gs₁ (List.ofFn σ)
              (initVar m p false, []) hgs₁_notℓ hinv0
            have hag_u : (bWires gs₁ (List.ofFn σ)).getD u false = bval := by
              have hag := bWires_agree gs₁ {(ℓ : ℕ)} (List.ofFn σ) (List.ofFn x')
                (by simp) (by intro b hb; simp at hb; subst hb; simp)
                (by
                  intro i hi; simp at hi
                  by_cases him : i < m
                  · have hiℓ : (⟨i, him⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                    rw [ofFn_getD_lt _ _ _ him, ofFn_getD_lt _ _ _ him, hσ, Function.update_of_ne hiℓ]
                  · rw [List.getD_eq_default _ _ (by simp; omega),
                        List.getD_eq_default _ _ (by simp; omega)])
                hgs₁_notℓ
              exact hag.2 u (by simpa using hu_ne_ℓ)
            have hval_ℓ : (bWires gs₁ (List.ofFn σ)).getD (ℓ : ℕ) false = bval := by
              rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt, hσ, Function.update_self]
            have hg₁_eval : g₁.op ((bWires gs₁ (List.ofFn σ)).getD g₁.left false)
                ((bWires gs₁ (List.ofFn σ)).getD g₁.right false) = c₁ := by
              rcases hg₁reads with hl | hr
              · have hru : g₁.right = u := by simp [hu, hl]
                rw [hl, hru, hval_ℓ, hag_u]; exact hdiag bval
              · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
                have hlu : g₁.left = u := by simp [hu, hlne]
                rw [hr, hlu, hval_ℓ, hag_u]; exact hdiag bval
            have hinvM : ElimInvOn {(ℓ : ℕ)} m (List.ofFn x)
                (bWires (gs₁ ++ [g₁]) (List.ofFn σ)) accM := by
              rw [bWires_append, bWires_cons, bWires_nil, hg₁_eval]
              refine ⟨hinv1.1, by
                simp only [haccM, List.length_append, List.length_singleton]
                rw [hacc₁_len, bWires_length, List.length_ofFn], ?_⟩
              intro i hi
              by_cases hieq : i = w₁
              · subst hieq
                have hlen_w : (bWires gs₁ (List.ofFn σ)).length = w₁ := by
                  rw [bWires_length, List.length_ofFn]
                rw [haccM_w₁, getD_snoc_eq _ _ _ _ hlen_w.symm]
                exact ⟨trivial, rfl⟩
              · have hlen_w : (bWires gs₁ (List.ofFn σ)).length = w₁ := by
                  rw [bWires_length, List.length_ofFn]
                simp only [haccM]
                rw [getD_snoc_ne _ _ _ _ (by rw [hacc₁_len]; exact hieq),
                    getD_snoc_ne _ _ _ _ (by rw [hlen_w]; exact hieq)]
                exact hinv1.2.2 i hi
            have hinv2 := elimInvOn_pass {(ℓ : ℕ)} m (List.ofFn x) gs₂ _ accM hgs₂_notℓ hinvM
            dsimp only
            rw [hsplit, bWires_append (gs₁ ++ [g₁]) gs₂]
            exact hinv2
          have heval_acc : ∀ x : Fin m → Bool,
              statVal (bWires acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
                F (Function.update x p false) := by
            intro x
            have h := ((hinv_all x).2.2 C.output (by simpa using hout_ne_ℓ)).2
            rw [h]
            exact (hev _).trans (hkill x _)
          have hst_val : statValid (m + acc.2.length) (acc.1.getD C.output (Sum.inl false)) :=
            ((hinv_all (fun _ => false)).2.2 C.output (by simpa using hout_ne_ℓ)).1
          have hout_ne_w1 : C.output ≠ w₁ := by
            intro heq
            have hw1acc : acc.1.getD C.output (Sum.inl false) = Sum.inl c₁ := by
              rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, hacc₁_len])]
              exact haccM_w₁
            obtain ⟨x, x', hne⟩ := hncp
            have hx := heval_acc x; have hx' := heval_acc x'
            rw [hw1acc] at hx hx'
            exact hne (hx.symm.trans hx')
          have hex₂ := hex₂_w₁ hout_ne_w1
          have htot : C.gates.length = gs₁.length + 1 + gs₂.length := by rw [hsplit]; simp; omega
          have hlen3 : acc.2.length + 3 ≤ C.gates.length := by
            by_cases hp1 : ∃ g ∈ gs₁, readsWire (p : ℕ) g = true
            · have h1 : acc₁.2.length + 1 ≤ gs₁.length := by
                have := elimPass_len_lt m (p : ℕ) gs₁ (initVar m p false, [])
                  (by simp [initVar])
                  ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ p.isLt]; simp⟩ hp1
                rw [← hacc₁] at this; simpa using this
              have h2 : acc.2.length + 1 ≤ accM.2.length + gs₂.length :=
                elimPass_len_lt m w₁ gs₂ accM (by simp [haccM, hacc₁_len]) ⟨c₁, haccM_w₁⟩ hex₂
              have hM : accM.2.length = acc₁.2.length := rfl
              omega
            · push Not at hp1
              have hgs₁_nop : ∀ g ∈ gs₁, readsWire (p : ℕ) g = false := fun g hg =>
                Bool.eq_false_iff.2 (hp1 g hg)
              have hp2 : ∃ g ∈ gs₂, readsWire (p : ℕ) g = true := by
                by_contra hnop2
                push Not at hnop2
                have hgs₂_nop : ∀ g ∈ gs₂, readsWire (p : ℕ) g = false := fun g hg =>
                  Bool.eq_false_iff.2 (hnop2 g hg)
                set x0 : Fin m → Bool := fun _ => false
                have h3 := h3sub x0 (fun _ _ _ _ => rfl)
                set f00 := Function.update (Function.update x0 p false) ℓ false
                set f10 := Function.update (Function.update x0 p true) ℓ false
                set f11 := Function.update (Function.update x0 p true) ℓ true
                have hw1_indep : ∀ y : Fin m → Bool,
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y q false))).getD w₁ false =
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y q true))).getD w₁ false →
                    False → False := fun _ _ h => h
                have hpig : ∀ a b c : Bool, a = b ∨ a = c ∨ b = c := by decide
                set v00 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f00 q false))).getD w₁ false
                set v10 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f10 q false))).getD w₁ false
                set v11 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f11 q false))).getD w₁ false
                set w00 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f00 q true))).getD w₁ false
                set w10 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f10 q true))).getD w₁ false
                set w11 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f11 q true))).getD w₁ false
                have hsub_eq : ∀ (y₁ y₂ : Fin m → Bool) (bq : Bool),
                    (∀ i, i ≠ ℓ → i ≠ p → y₁ i = y₂ i) →
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y₁ q bq))).getD w₁ false =
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y₂ q bq))).getD w₁ false →
                    F (Function.update y₁ q bq) = F (Function.update y₂ q bq) := by
                  intro y₁ y₂ bq hy hw1eq
                  rw [← hev, ← hev]
                  show (bWires C.gates _).getD C.output false = (bWires C.gates _).getD C.output false
                  rw [hsplit]
                  exact bWires_pair_factor gs₁ gs₂ g₁ ℓ p
                    (fun g hg => ⟨hgs₁no g hg, hgs₁_nop g hg⟩)
                    (fun g hg => ⟨hgs₂no g hg, hgs₂_nop g hg⟩)
                    (Function.update y₁ q bq) (Function.update y₂ q bq)
                    (fun i hiℓ hip => by
                      by_cases hiq : i = q
                      · subst hiq; simp
                      · rw [Function.update_of_ne hiq, Function.update_of_ne hiq]; exact hy i hiℓ hip)
                    hw1eq C.output hout_ne_ℓ hout_ne_p
                have hf00_10 : ∀ i, i ≠ ℓ → i ≠ p → f00 i = f10 i := by
                  intro i hiℓ hip; simp [f00, f10, Function.update_of_ne hiℓ, Function.update_of_ne hip]
                have hf00_11 : ∀ i, i ≠ ℓ → i ≠ p → f00 i = f11 i := by
                  intro i hiℓ hip; simp [f00, f11, Function.update_of_ne hiℓ, Function.update_of_ne hip]
                have hf10_11 : ∀ i, i ≠ ℓ → i ≠ p → f10 i = f11 i := by
                  intro i hiℓ hip; simp [f10, f11, Function.update_of_ne hiℓ, Function.update_of_ne hip]
                have hne_00_11_f : v00 ≠ v11 := fun heq => by
                  have := hsub_eq f00 f11 false hf00_11 heq
                  rw [h3.1, h3.2.2.2.2.1] at this; exact Bool.false_ne_true this
                have hne_10_11_f : v10 ≠ v11 := fun heq => by
                  have := hsub_eq f10 f11 false hf10_11 heq
                  rw [h3.2.2.1, h3.2.2.2.2.1] at this; exact Bool.false_ne_true this
                have hne_00_10_t : w00 ≠ w10 := fun heq => by
                  have := hsub_eq f00 f10 true hf00_10 heq
                  rw [h3.2.1, h3.2.2.2.1] at this; exact Bool.false_ne_true this
                have hne_00_11_t : w00 ≠ w11 := fun heq => by
                  have := hsub_eq f00 f11 true hf00_11 heq
                  rw [h3.2.1, h3.2.2.2.2.2] at this; exact Bool.false_ne_true this
                have h00_10_f : v00 = v10 := by
                  rcases hpig v00 v10 v11 with h | h | h
                  · exact h
                  · exact absurd h hne_00_11_f
                  · exact absurd h hne_10_11_f
                have h10_11_t : w10 = w11 := by
                  rcases hpig w00 w10 w11 with h | h | h
                  · exact absurd h hne_00_10_t
                  · exact absurd h hne_00_11_t
                  · exact h
                have h_g1_eq : ∀ (y₁ y₂ : Fin m → Bool) (bq : Bool),
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y₁ q bq))).getD w₁ false =
                    g₁.op ((bWires gs₁ (List.ofFn (Function.update y₁ q bq))).getD g₁.left false)
                          ((bWires gs₁ (List.ofFn (Function.update y₁ q bq))).getD g₁.right false) := by
                  intro y₁ _ bq
                  rw [bWires_append, bWires_cons, bWires_nil,
                      getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn])]
                have hag_gs1 : ∀ (y₁ y₂ : Fin m → Bool) (bq : Bool),
                    (∀ i, i ≠ ℓ → i ≠ p → y₁ i = y₂ i) →
                    (bWires gs₁ (List.ofFn (Function.update y₁ q bq))).getD u false =
                    (bWires gs₁ (List.ofFn (Function.update y₂ q bq))).getD u false := by
                  intro y₁ y₂ bq hy
                  have h := bWires_agree gs₁ {(ℓ : ℕ), (p : ℕ)}
                    (List.ofFn (Function.update y₁ q bq)) (List.ofFn (Function.update y₂ q bq))
                    (by simp) (by intro b hb; rcases hb with rfl | rfl <;> simp)
                    (by
                      intro i hi
                      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
                      by_cases him : i < m
                      · have h1 : (⟨i, him⟩ : Fin m) ≠ ℓ := fun e => hi.1 (congrArg Fin.val e)
                        have h2 : (⟨i, him⟩ : Fin m) ≠ p := fun e => hi.2 (congrArg Fin.val e)
                        rw [ofFn_getD_lt _ _ _ him, ofFn_getD_lt _ _ _ him]
                        by_cases hiq : (⟨i, him⟩ : Fin m) = q
                        · subst hiq; simp
                        · rw [Function.update_of_ne hiq, Function.update_of_ne hiq]; exact hy _ h1 h2
                      · rw [List.getD_eq_default _ _ (by simp; omega),
                            List.getD_eq_default _ _ (by simp; omega)])
                    (by
                      intro g hg
                      have h1 := hgs₁no g hg; have h2 := hgs₁_nop g hg
                      simp only [readsWire, decide_eq_false_iff_not, not_or] at h1 h2
                      exact ⟨by simp [h1.1, h2.1], by simp [h1.2, h2.2]⟩)
                  by_cases hup : u = (p : ℕ)
                  · exfalso
                    have hval_u : ∀ y : Fin m → Bool,
                        (bWires gs₁ (List.ofFn (Function.update y q true))).getD u false = y p := by
                      intro y
                      rw [hup, bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ p.isLt,
                          Function.update_of_ne hqp.symm]
                    have hval_ℓ' : ∀ y : Fin m → Bool,
                        (bWires gs₁ (List.ofFn (Function.update y q true))).getD (ℓ : ℕ) false = y ℓ := by
                      intro y
                      rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt,
                          Function.update_of_ne hqℓ.symm]
                    have hw10_e : w10 = g₁.op (if g₁.left = (ℓ : ℕ) then f10 ℓ else f10 p)
                        (if g₁.left = (ℓ : ℕ) then f10 p else f10 ℓ) := by
                      dsimp only [w10]
                      rw [h_g1_eq f10 f10 true]
                      rcases hg₁reads with hl | hr
                      · have hru : g₁.right = u := by simp [hu, hl]
                        simp only [hl, hru, hval_ℓ', hval_u, ↓reduceIte]
                      · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
                        have hlu : g₁.left = u := by simp [hu, hlne]
                        simp only [hr, hlu, hval_ℓ', hval_u, hu_ne_ℓ, ↓reduceIte]
                    have hw11_e : w11 = g₁.op (if g₁.left = (ℓ : ℕ) then f11 ℓ else f11 p)
                        (if g₁.left = (ℓ : ℕ) then f11 p else f11 ℓ) := by
                      dsimp only [w11]
                      rw [h_g1_eq f11 f11 true]
                      rcases hg₁reads with hl | hr
                      · have hru : g₁.right = u := by simp [hu, hl]
                        simp only [hl, hru, hval_ℓ', hval_u, ↓reduceIte]
                      · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
                        have hlu : g₁.left = u := by simp [hu, hlne]
                        simp only [hr, hlu, hval_ℓ', hval_u, hu_ne_ℓ, ↓reduceIte]
                    have hf10_l : f10 ℓ = false := by simp [f10]
                    have hf10_p : f10 p = true := by simp [f10, hℓp.symm]
                    have hf11_l : f11 ℓ = true := by simp [f11]
                    have hf11_p : f11 p = true := by simp [f11, hℓp.symm]
                    rw [hw10_e, hw11_e, hf10_l, hf10_p, hf11_l, hf11_p] at h10_11_t
                    by_cases hl : g₁.left = (ℓ : ℕ)
                    · simp only [hl, ↓reduceIte] at h10_11_t; exact hR1 h10_11_t
                    · simp only [hl, ↓reduceIte] at h10_11_t; exact hL1 h10_11_t
                  · exact h.2 u (by simp [hu_ne_ℓ, hup])
                have heq_w00_w10 : w00 = w10 := by
                  dsimp only [w00, w10]
                  rw [h_g1_eq f00 f00 true, h_g1_eq f10 f10 true]
                  have hℓ00 : (bWires gs₁ (List.ofFn (Function.update f00 q true))).getD (ℓ : ℕ) false = false := by
                    rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt,
                        Function.update_of_ne hqℓ.symm]; simp [f00]
                  have hℓ10 : (bWires gs₁ (List.ofFn (Function.update f10 q true))).getD (ℓ : ℕ) false = false := by
                    rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt,
                        Function.update_of_ne hqℓ.symm]; simp [f10]
                  have hu01 := hag_gs1 f00 f10 true hf00_10
                  rcases hg₁reads with hl | hr
                  · have hru : g₁.right = u := by simp [hu, hl]
                    rw [hl, hru, hℓ00, hℓ10, hu01]
                  · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
                    have hlu : g₁.left = u := by simp [hu, hlne]
                    rw [hr, hlu, hℓ00, hℓ10, hu01]
                exact hne_00_10_t heq_w00_w10
              set P2 : BinaryGate → Bool := fun g => readsWire (p : ℕ) g || readsWire w₁ g with hP2
              have hlen1 : acc₁.2.length ≤ gs₁.length := by
                have := elimPass_len m gs₁ (initVar m p false, [])
                rw [← hacc₁] at this; simpa using this
              have hM_len : accM.2.length = acc₁.2.length := rfl
              by_cases h2ge2 : 2 ≤ (gs₂.filter P2).length
              · have h2 := elimPass_len_two_pred m P2 gs₂ accM
                  (fun g _ hPg acc' hacc' => by
                    simp only [hP2, Bool.or_eq_true] at hPg
                    rcases hPg with hrp | hrw
                    · exact elimStep_none_of_reads m (p : ℕ) acc' g
                        ⟨false, by rw [hacc' (p : ℕ) (by simp [haccM, hacc₁_len]; omega)]; exact haccM_p⟩ hrp
                    · exact elimStep_none_of_reads m w₁ acc' g
                        ⟨c₁, by rw [hacc' w₁ (by simp [haccM, hacc₁_len])]; exact haccM_w₁⟩ hrw)
                  h2ge2
                rw [← hacc] at h2
                omega
              · have h2pos : 1 ≤ (gs₂.filter P2).length := by
                  obtain ⟨g, hg, hrg⟩ := hex₂
                  have hmem : g ∈ gs₂.filter P2 := List.mem_filter.2 ⟨hg, by simp [hP2, hrg]⟩
                  exact List.length_pos_of_mem hmem
                have h2one : (gs₂.filter P2).length = 1 := by omega
                obtain ⟨gs₂a, g₂, gs₂b, hsplit2, hg₂P, hgs₂a_no, hgs₂b_no⟩ :=
                  list_split_unique_filter P2 gs₂ h2one
                have hg₂_p : readsWire (p : ℕ) g₂ = true := by
                  obtain ⟨g, hg, hrp⟩ := hp2
                  rw [hsplit2] at hg
                  simp only [List.mem_append, List.mem_singleton] at hg
                  rcases hg with (hg | rfl) | hg
                  · have := hgs₂a_no g hg; simp [hP2, hrp] at this
                  · exact hrp
                  · have := hgs₂b_no g hg; simp [hP2, hrp] at this
                have hg₂_w₁ : readsWire w₁ g₂ = true := by
                  obtain ⟨g, hg, hrw⟩ := hex₂
                  rw [hsplit2] at hg
                  simp only [List.mem_append, List.mem_singleton] at hg
                  rcases hg with (hg | rfl) | hg
                  · have := hgs₂a_no g hg; simp [hP2, hrw] at this
                  · exact hrw
                  · have := hgs₂b_no g hg; simp [hP2, hrw] at this
                set acc2a := elimPass m gs₂a accM with hacc2a
                set acc2M := elimStep m acc2a g₂ with hacc2M
                have hacc_eq2 : acc = elimPass m gs₂b acc2M := by
                  rw [hacc, hsplit2, elimPass_append, elimPass_append, ← hacc2a,
                      elimPass_cons, elimPass_nil, ← hacc2M]
                set w₂ := w₁ + 1 + gs₂a.length with hw₂
                have hacc2a_len : acc2a.1.length = w₂ := by
                  rw [hacc2a, elimPass_fst_len]; simp [haccM, hacc₁_len, hw₂]
                have hacc2a_p : acc2a.1.getD (p : ℕ) (Sum.inl false) = Sum.inl false := by
                  rw [hacc2a, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, hacc₁_len]; omega)]
                  exact haccM_p
                have hacc2a_w₁ : acc2a.1.getD w₁ (Sum.inl false) = Sum.inl c₁ := by
                  rw [hacc2a, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, hacc₁_len])]
                  exact haccM_w₁
                have hp_ne_w1 : (p : ℕ) ≠ w₁ := by omega
                have hg₂_both : (g₂.left = (p : ℕ) ∧ g₂.right = w₁) ∨ (g₂.left = w₁ ∧ g₂.right = (p : ℕ)) := by
                  simp only [readsWire, decide_eq_true_eq] at hg₂_p hg₂_w₁
                  rcases hg₂_p with h1 | h1 <;> rcases hg₂_w₁ with h2 | h2
                  · exact absurd (h1.symm.trans h2) hp_ne_w1
                  · exact Or.inl ⟨h1, h2⟩
                  · exact Or.inr ⟨h2, h1⟩
                  · exact absurd (h1.symm.trans h2) hp_ne_w1
                obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Bool,
                    simplifyBGate g₂.op (m + acc2a.2.length)
                      (acc2a.1.getD g₂.left (Sum.inl false)) (acc2a.1.getD g₂.right (Sum.inl false)) =
                      (none, Sum.inl c₂) := by
                  rcases hg₂_both with ⟨hl, hr⟩ | ⟨hl, hr⟩
                  · exact ⟨g₂.op false c₁, by rw [hl, hr, hacc2a_p, hacc2a_w₁]; rfl⟩
                  · exact ⟨g₂.op c₁ false, by rw [hl, hr, hacc2a_w₁, hacc2a_p]; rfl⟩
                have hacc2M_len : acc2M.2.length = acc2a.2.length := by
                  simp only [hacc2M, elimStep, hc₂, Option.toList_none, List.append_nil]
                have hacc2M_w₂ : acc2M.1.getD w₂ (Sum.inl false) = Sum.inl c₂ := by
                  simp only [hacc2M, elimStep, hc₂]
                  exact getD_snoc_eq _ _ _ _ hacc2a_len.symm
                have hout_ne_w2 : C.output ≠ w₂ := by
                  intro heq
                  have hw2acc : acc.1.getD C.output (Sum.inl false) = Sum.inl c₂ := by
                    rw [heq, hacc_eq2, elimPass_getD_lt _ _ _ _ _ (by simp [hacc2M, elimStep, hacc2a_len])]
                    exact hacc2M_w₂
                  obtain ⟨x, x', hne⟩ := hncp
                  have hx := heval_acc x; have hx' := heval_acc x'
                  rw [hw2acc] at hx hx'
                  exact hne (hx.symm.trans hx')
                have hex2b : ∃ g ∈ gs₂b, readsWire w₂ g = true := by
                  by_contra hnob
                  push_neg at hnob
                  obtain ⟨x, hne⟩ := hdep
                  have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
                    (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
                    (by simp) (by intro u hu; simp at hu; subst hu; simp)
                    (by
                      intro i hi; simp at hi
                      by_cases hlt : i < m
                      · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                        rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                            Function.update_of_ne hne', Function.update_of_ne hne']
                      · rw [List.getD_eq_default _ _ (by simp; omega),
                            List.getD_eq_default _ _ (by simp; omega)])
                    (by
                      intro g hg
                      have hr := hgs₁no g hg
                      simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
                      exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
                  have hag2a := bWires_agree gs₂a {(ℓ : ℕ), w₁}
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ false)))
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ true)))
                    (by simp [bWires_length])
                    (by intro b hb; rw [bWires_length, List.length_ofFn, List.length_append, List.length_singleton]; rcases hb with rfl | rfl <;> omega)
                    (by
                      intro i hi
                      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
                      rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil]
                      have hl1 : (bWires gs₁ (List.ofFn (Function.update x ℓ false))).length = w₁ := by
                        rw [bWires_length, List.length_ofFn]
                      have hl2 : (bWires gs₁ (List.ofFn (Function.update x ℓ true))).length = w₁ := by
                        rw [bWires_length, List.length_ofFn]
                      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
                      exact hag1.2 i (by simpa using hi.1))
                    (by
                      intro g hg
                      have hr1 := hgs₂no g (by rw [hsplit2]; simp [hg])
                      have hr2 := hgs₂a_no g hg
                      simp only [hP2, Bool.or_eq_false_iff, readsWire, decide_eq_false_iff_not, not_or] at hr1 hr2
                      exact ⟨by simp [hr1.1, hr2.2.1], by simp [hr1.2, hr2.2.2]⟩)
                  have hag2b := bWires_agree gs₂b {(ℓ : ℕ), w₁, w₂}
                    (bWires (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) (List.ofFn (Function.update x ℓ false)))
                    (bWires (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) (List.ofFn (Function.update x ℓ true)))
                    (by simp [bWires_length])
                    (by intro b hb; rw [bWires_length, List.length_ofFn]; rcases hb with rfl | rfl | rfl <;> simp <;> omega)
                    (by
                      intro i hi
                      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
                      rw [bWires_append (gs₁ ++ [g₁] ++ gs₂a) [g₂], bWires_cons, bWires_nil,
                          bWires_append (gs₁ ++ [g₁] ++ gs₂a) [g₂], bWires_cons, bWires_nil]
                      have hl1 : (bWires (gs₁ ++ [g₁] ++ gs₂a) (List.ofFn (Function.update x ℓ false))).length = w₂ := by
                        simp [bWires_length, hw₂, hw₁]; omega
                      have hl2 : (bWires (gs₁ ++ [g₁] ++ gs₂a) (List.ofFn (Function.update x ℓ true))).length = w₂ := by
                        simp [bWires_length, hw₂, hw₁]; omega
                      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega),
                          bWires_append (gs₁ ++ [g₁]) gs₂a, bWires_append (gs₁ ++ [g₁]) gs₂a]
                      exact hag2a.2 i (by simp [hi.1, hi.2.1]))
                    (by
                      intro g hg
                      have hr1 := hgs₂no g (by rw [hsplit2]; simp [hg])
                      have hr2 := hgs₂b_no g hg
                      have hr3 := hnob g hg
                      simp only [hP2, ne_eq, Bool.or_eq_false_iff, readsWire, decide_eq_false_iff_not,
                        decide_eq_true_eq, not_or] at hr1 hr2 hr3
                      exact ⟨by simp [hr1.1, hr2.2.1, hr3.1], by simp [hr1.2, hr2.2.2, hr3.2]⟩)
                  have hEq : (bWires C.gates (List.ofFn (Function.update x ℓ false))).getD C.output false =
                      (bWires C.gates (List.ofFn (Function.update x ℓ true))).getD C.output false := by
                    have hcat : C.gates = (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) ++ gs₂b := by
                      rw [hsplit, hsplit2]; simp [List.append_assoc]
                    rw [hcat, bWires_append (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) gs₂b,
                        bWires_append (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) gs₂b]
                    exact hag2b.2 C.output (by simp [hout_ne_ℓ, hout_ne_w1, hout_ne_w2])
                  exact hne ((hev _).symm.trans (hEq.trans (hev _)))
                have h2a_len : acc2a.2.length ≤ accM.2.length + gs₂a.length :=
                  elimPass_len m gs₂a accM
                have h2b_len : acc.2.length + 1 ≤ acc2M.2.length + gs₂b.length := by
                  rw [hacc_eq2]
                  exact elimPass_len_lt m w₂ gs₂b acc2M (by simp [hacc2M, elimStep, hacc2a_len])
                    ⟨c₂, hacc2M_w₂⟩ hex2b
                have hgs2_len : gs₂.length = gs₂a.length + 1 + gs₂b.length := by rw [hsplit2]; simp; omega
                omega
          exact Or.inr (Or.inr ⟨by omega,
            circuit_from_stat acc.2 (acc.1.getD C.output (Sum.inl false)) (by omega)
              hst_val heval_acc hncp hF0_p⟩)

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
        intro hq; apply hℓ_not_Q; rw [← hq]; simp
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

def HasMinVC {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  (∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t) ∧
  (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card)

lemma hasMinVC_exists {n : ℕ} (G : SimpleGraph (Fin n)) : ∃ t : ℕ, HasMinVC G t := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = k :=
    ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro S hS
  exact Nat.find_min' hex ⟨S, hS, rfl⟩

lemma hasMinVC_empty {n t : ℕ} (G : SimpleGraph (Fin n))
    (hempty : ∀ u v : Fin n, ¬ G.Adj u v) (hvc : HasMinVC G t) : t = 0 := by
  have hle : t ≤ (∅ : Finset (Fin n)).card := hvc.2 ∅ (fun u v h => absurd h (hempty u v))
  simpa using hle

def deleteVertexEdges {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ≠ p ∧ v ≠ p
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

lemma deleteVertexEdges_le {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    deleteVertexEdges G p ≤ G := fun _ _ h => h.1

lemma hasMinVC_deleteEdge {n t t₁ : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (hvc : HasMinVC G t) (hvc₁ : HasMinVC (G.deleteEdges {s(ℓ, p)}) t₁) :
    t₁ ≤ t ∧ t ≤ t₁ + 1 := by
  obtain ⟨⟨S, hS, hSc⟩, hmin⟩ := hvc
  obtain ⟨⟨S₁, hS₁, hS₁c⟩, hmin₁⟩ := hvc₁
  constructor
  · rw [← hSc]; exact hmin₁ S (fun u v h => hS u v h.1)
  · have hcov : CoverPromise.IsVertexCover G (insert p S₁) := by
      intro u v huv
      by_cases hmem : s(u, v) = s(ℓ, p)
      · rw [Sym2.eq_iff] at hmem
        rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
        · exact Or.inr (hvp ▸ Finset.mem_insert_self p S₁)
        · exact Or.inl (hup ▸ Finset.mem_insert_self p S₁)
      · rcases hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with hu | hv
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
    · have hcov : CoverPromise.IsVertexCover G S₁ := by
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
          intro heq; rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hℓ'ne h1
          · exact hℓ'p.ne h1
        rcases hS₁ ℓ' p (SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, by simpa using hne_edge⟩) with h | h
        · exact h
        · exact absurd h hp
      set S' := insert p (S₁.erase ℓ')
      have hcov : CoverPromise.IsVertexCover G S' := by
        intro u v huv
        by_cases hmem : s(u, v) = s(ℓ, p)
        · rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
          · exact Or.inr (hvp ▸ Finset.mem_insert_self p _)
          · exact Or.inl (hup ▸ Finset.mem_insert_self p _)
        · rcases hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with hu | hv
          · by_cases huℓ : u = ℓ'
            · subst huℓ; exact Or.inr ((hℓ'leaf v huv) ▸ Finset.mem_insert_self p _)
            · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨huℓ, hu⟩))
          · by_cases hvℓ : v = ℓ'
            · subst hvℓ; exact Or.inl ((hℓ'leaf u huv.symm) ▸ Finset.mem_insert_self p _)
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
    have hcov : CoverPromise.IsVertexCover G (insert p S') := by
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
    · have hcov : CoverPromise.IsVertexCover (deleteVertexEdges G p) (S.erase p) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · exact Or.inl (Finset.mem_erase.2 ⟨huv.2.1, hu⟩)
        · exact Or.inr (Finset.mem_erase.2 ⟨huv.2.2, hv⟩)
      have h1 := hmin' (S.erase p) hcov
      have h2 := Finset.card_erase_of_mem hp
      have hpos : 1 ≤ S.card := Finset.one_le_card.2 ⟨p, hp⟩
      omega
    · have hℓ : ℓ ∈ S := (hS ℓ p hlp).resolve_right hp
      have hcov : CoverPromise.IsVertexCover (deleteVertexEdges G p) (S.erase ℓ) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · have huℓ : u ≠ ℓ := fun h => huv.2.2 (hleaf v (h ▸ huv.1))
          exact Or.inl (Finset.mem_erase.2 ⟨huℓ, hu⟩)
        · have hvℓ : v ≠ ℓ := fun h => huv.2.1 (hleaf u (h ▸ huv.1.symm))
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
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

lemma edgeFinset_card_deleteVertex_deg1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) (hpdeg : ∀ w, G.Adj p w → w = ℓ)
    [DecidableRel (deleteVertexEdges G p).Adj] :
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
        intro he; rw [Sym2.eq_iff] at he
        rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hvp h2
        · exact hup h1
      · rintro ⟨hne, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup; exact hne (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, hpdeg v huv⟩)
        · intro hvp; subst hvp; exact hne (by rw [Sym2.eq_iff]; exact Or.inl ⟨hpdeg u huv.symm, rfl⟩)
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

lemma edgeFinset_card_deleteVertex_deg2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p q : Fin n) (hlp : G.Adj ℓ p) (hpq : G.Adj p q)
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
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hlp.ne h1.symm
    · exact hqne h2
  have hmem2 : s(p, q) ∈ G.edgeFinset.erase s(ℓ, p) :=
    Finset.mem_erase.2 ⟨hne_edges, by rw [SimpleGraph.mem_edgeFinset]; exact hpq⟩
  have hpos2 : 1 ≤ (G.edgeFinset.erase s(ℓ, p)).card := Finset.one_le_card.2 ⟨s(p, q), hmem2⟩
  rw [Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hmem1]
  rw [Finset.card_erase_of_mem hmem1] at hpos2
  omega

def forestFun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

lemma forestFun_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) :
    forestFun G A (fun _ => false) = false := by
  simp [forestFun]

lemma forestFun_nonconst {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (hne : A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) :
    ∃ x x' : Fin n → Bool, forestFun G A x ≠ forestFun G A x' := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  rw [forestFun_false]
  have h1 : forestFun G A (fun _ => true) = true := by
    simp only [forestFun, decide_eq_true_eq]
    rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
    · exact Or.inl ⟨a, ha, trivial⟩
    · exact Or.inr ⟨u, v, huv, trivial, trivial⟩
  rw [h1]; decide

lemma forestFun_update_A {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha_iso : ∀ v : Fin n, ¬ G.Adj a v) :
    (fun x => forestFun G A (Function.update x a false)) = forestFun G (A.erase a) := by
  funext x
  simp only [forestFun]
  apply decide_eq_decide.2
  constructor
  · rintro (⟨b, hb, hbx⟩ | ⟨u, v, huv, hux, hvx⟩)
    · left
      have hba : b ≠ a := by intro h; subst h; simp at hbx
      refine ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, ?_⟩
      rwa [Function.update_of_ne hba] at hbx
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      rw [Function.update_of_ne hua] at hux
      rw [Function.update_of_ne hva] at hvx
      exact ⟨u, v, huv, hux, hvx⟩
  · rintro (⟨b, hb, hbx⟩ | ⟨u, v, huv, hux, hvx⟩)
    · left
      obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
      exact ⟨b, hbA, by rw [Function.update_of_ne hba]; exact hbx⟩
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      exact ⟨u, v, huv, by rw [Function.update_of_ne hua]; exact hux,
        by rw [Function.update_of_ne hva]; exact hvx⟩

lemma forestFun_update_leaf_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p : Fin n) (hleaf : ∀ w, G.Adj ℓ w → w = p) [DecidableRel (G.deleteEdges {s(ℓ, p)}).Adj] :
    (fun x => forestFun G ∅ (Function.update x ℓ false)) =
      forestFun (G.deleteEdges {s(ℓ, p)}) ∅ := by
  funext x
  simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hux, hvx⟩
    have huℓ : u ≠ ℓ := by intro h; subst h; simp at hux
    have hvℓ : v ≠ ℓ := by intro h; subst h; simp at hvx
    rw [Function.update_of_ne huℓ] at hux
    rw [Function.update_of_ne hvℓ] at hvx
    refine ⟨u, v, SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩, hux, hvx⟩
    intro heq
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huℓ rfl
    · exact hvℓ rfl
  · rintro ⟨u, v, hadj, hux, hvx⟩
    obtain ⟨huv, hne⟩ := SimpleGraph.deleteEdges_adj.1 hadj
    simp only [Set.mem_singleton_iff] at hne
    have huℓ : u ≠ ℓ := by intro h; subst h; rw [hleaf v huv] at hne; exact hne rfl
    have hvℓ : v ≠ ℓ := by intro h; subst h; rw [hleaf u huv.symm] at hne; exact hne Sym2.eq_swap
    exact ⟨u, v, huv, by rw [Function.update_of_ne huℓ]; exact hux,
      by rw [Function.update_of_ne hvℓ]; exact hvx⟩

lemma forestFun_update_leaf_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) (hleaf : ∀ w, G.Adj ℓ w → w = p)
    [DecidableRel (deleteVertexEdges G p).Adj] :
    (fun x => forestFun G ∅ (Function.update x ℓ true)) =
      forestFun (deleteVertexEdges G p) {p} := by
  funext x
  simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or,
    Finset.mem_singleton, exists_eq_left]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hux, hvx⟩
    by_cases hup : u = p
    · subst hup; rw [Function.update_of_ne hlp.ne.symm] at hux; exact Or.inl hux
    · by_cases hvp : v = p
      · subst hvp; rw [Function.update_of_ne hlp.ne.symm] at hvx; exact Or.inl hvx
      · right
        have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
        have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
        rw [Function.update_of_ne huℓ] at hux
        rw [Function.update_of_ne hvℓ] at hvx
        exact ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩
  · rintro (hpx | ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩)
    · exact ⟨ℓ, p, hlp, by simp, by rw [Function.update_of_ne hlp.ne.symm]; exact hpx⟩
    · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
      have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
      exact ⟨u, v, huv, by rw [Function.update_of_ne huℓ]; exact hux,
        by rw [Function.update_of_ne hvℓ]; exact hvx⟩

lemma forestFun_update_p_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : Fin n) [DecidableRel (deleteVertexEdges G p).Adj] :
    (fun x => forestFun G ∅ (Function.update x p false)) =
      forestFun (deleteVertexEdges G p) ∅ := by
  funext x
  simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hux, hvx⟩
    have hup : u ≠ p := by intro h; subst h; simp at hux
    have hvp : v ≠ p := by intro h; subst h; simp at hvx
    rw [Function.update_of_ne hup] at hux
    rw [Function.update_of_ne hvp] at hvx
    exact ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩
  · rintro ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩
    exact ⟨u, v, huv, by rw [Function.update_of_ne hup]; exact hux,
      by rw [Function.update_of_ne hvp]; exact hvx⟩

lemma forestFun_dep_A {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha : a ∈ A) :
    ∃ x : Fin n → Bool,
      forestFun G A (Function.update x a false) ≠ forestFun G A (Function.update x a true) := by
  refine ⟨fun _ => false, ?_⟩
  have h0 : forestFun G A (Function.update (fun _ => false) a false) = false := by
    have : Function.update (fun _ : Fin n => false) a false = fun _ => false := by
      funext i; by_cases hi : i = a <;> simp [hi]
    rw [this, forestFun_false]
  have h1 : forestFun G A (Function.update (fun _ => false) a true) = true := by
    simp only [forestFun, decide_eq_true_eq]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [h0, h1]; decide

lemma forestFun_dep_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) :
    ∃ x : Fin n → Bool,
      forestFun G ∅ (Function.update x ℓ false) ≠ forestFun G ∅ (Function.update x ℓ true) := by
  set x0 : Fin n → Bool := fun i => decide (i = p) with hx0
  refine ⟨x0, ?_⟩
  have h0 : forestFun G ∅ (Function.update x0 ℓ false) = false := by
    have hupd : Function.update x0 ℓ false = x0 := by
      funext i; by_cases hi : i = ℓ
      · subst hi; simp [hx0, hlp.ne]
      · rw [Function.update_of_ne hi]
    rw [hupd]
    simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [hx0, decide_eq_true_eq] at hu hv
    subst hu; subst hv; exact G.loopless.irrefl _ huv
  have h1 : forestFun G ∅ (Function.update x0 ℓ true) = true := by
    simp only [forestFun, decide_eq_true_eq]
    exact Or.inr ⟨ℓ, p, hlp, by simp, by rw [Function.update_of_ne hlp.ne.symm]; simp [hx0]⟩
  rw [h0, h1]; decide

lemma lower_bound_aux :
    ∀ (s : ℕ) {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      G.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
      (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) →
      HasMinVC G t →
      HasBinarySize n (forestFun G A) s →
      A.card + G.edgeFinset.card + t ≤ s + 1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro n t G _ A hAcyc hA_iso hne hvc hC
    by_cases hAne : A.Nonempty
    · obtain ⟨a, ha⟩ := hAne
      by_cases hrem : (A.erase a).Nonempty ∨ ∃ u v : Fin n, G.Adj u v
      · have hdep := forestFun_dep_A G A a ha
        have hrew := forestFun_update_A G A a (hA_iso a ha)
        have hnc : ∃ x x', forestFun G A (Function.update x a false) ≠
            forestFun G A (Function.update x' a false) := by
          simpa only [← congrFun hrew] using forestFun_nonconst G (A.erase a) hrem
        have hF0 : forestFun G A (Function.update (fun _ => false) a false) = false := by
          rw [congrFun hrew]; exact forestFun_false G (A.erase a)
        obtain ⟨hs1, hC'⟩ := elim_one_var a false hC hdep hnc hF0
        rw [hrew] at hC'
        have hih := ih (s - 1) (by omega) G (A.erase a) hAcyc
          (fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)) hrem hvc hC'
        have hcard : (A.erase a).card + 1 = A.card := Finset.card_erase_add_one ha
        omega
      · push Not at hrem
        have hA1 : A.card = 1 := by
          have he : (A.erase a).card = 0 := Finset.card_eq_zero.2 hrem.1
          have := Finset.card_erase_add_one ha; omega
        have ht0 : t = 0 := hasMinVC_empty G hrem.2 hvc
        have he0 : G.edgeFinset.card = 0 := by
          apply Finset.card_eq_zero.2; ext e
          induction e using Sym2.ind with
          | _ u v => simp [SimpleGraph.mem_edgeFinset, hrem.2 u v]
        omega
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
      subst hAempty
      have hEdge : ∃ u v : Fin n, G.Adj u v := hne.resolve_left (by simp)
      obtain ⟨ℓ, p, hlp, hleaf, hcases⟩ := acyclic_leaf_cases G hAcyc hEdge
      rcases hcases with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | ⟨q, hqne, hpq, hpdeg2⟩
      · classical
        obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (G.deleteEdges {s(ℓ, p)})
        have ht₁ : t₁ = t := hasMinVC_deleteLeafEdge_eq G ℓ ℓ' p hℓ'ne hℓ'p hℓ'leaf hvc hvc₁
        have hdep := forestFun_dep_edge G ℓ p hlp
        have hrew := forestFun_update_leaf_false G ℓ p hleaf
        have hEdge' : ∃ u v : Fin n, (G.deleteEdges {s(ℓ, p)}).Adj u v := by
          refine ⟨ℓ', p, SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, ?_⟩⟩
          intro heq; simp only [Set.mem_singleton_iff, Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hℓ'ne h1
          · exact hℓ'p.ne h1
        have hnc : ∃ x x', forestFun G ∅ (Function.update x ℓ false) ≠
            forestFun G ∅ (Function.update x' ℓ false) := by
          simpa only [← congrFun hrew] using forestFun_nonconst (G.deleteEdges {s(ℓ, p)}) ∅ (Or.inr hEdge')
        have hF0 : forestFun G ∅ (Function.update (fun _ => false) ℓ false) = false := by
          rw [congrFun hrew]; exact forestFun_false _ _
        obtain ⟨hs1, hC'⟩ := elim_one_var ℓ false hC hdep hnc hF0
        rw [hrew] at hC'
        have hih := ih (s - 1) (by omega) (G.deleteEdges {s(ℓ, p)}) ∅
          (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) (Or.inr hEdge') hvc₁ hC'
        have hedge := edgeFinset_card_deleteEdge G ℓ p hlp
        simp only [Finset.card_empty, zero_add] at hih ⊢
        omega
      · classical
        obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges G p)
        have ht' : t' + 1 = t := hasMinVC_deleteVertex G ℓ p hlp hleaf hvc hvc'
        have hdep := forestFun_dep_edge G ℓ p hlp
        have hrew := forestFun_update_leaf_true G ℓ p hlp hleaf
        have hnc : ∃ x x', forestFun G ∅ (Function.update x ℓ true) ≠
            forestFun G ∅ (Function.update x' ℓ true) := by
          simpa only [← congrFun hrew] using
            forestFun_nonconst (deleteVertexEdges G p) {p} (Or.inl (Finset.singleton_nonempty p))
        have hF0 : forestFun G ∅ (Function.update (fun _ => false) ℓ true) = false := by
          rw [congrFun hrew]; exact forestFun_false _ _
        obtain ⟨hs1, hC'⟩ := elim_one_var ℓ true hC hdep hnc hF0
        rw [hrew] at hC'
        have hih := ih (s - 1) (by omega) (deleteVertexEdges G p) {p}
          (hAcyc.anti (deleteVertexEdges_le G p))
          (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl)
          (Or.inl (Finset.singleton_nonempty p)) hvc' hC'
        have hedge := edgeFinset_card_deleteVertex_deg1 G ℓ p hlp hpdeg1
        simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
        omega
      · classical
        have hdep := forestFun_dep_edge G ℓ p hlp
        have hrew0 := forestFun_update_leaf_false G ℓ p hleaf
        have hrew1 := forestFun_update_leaf_true G ℓ p hlp hleaf
        have hrewp := forestFun_update_p_false G p
        have hEdge0 : ∃ u v : Fin n, (G.deleteEdges {s(ℓ, p)}).Adj u v := by
          refine ⟨p, q, SimpleGraph.deleteEdges_adj.2 ⟨hpq, ?_⟩⟩
          intro heq; simp only [Set.mem_singleton_iff, Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hlp.ne h1.symm
          · exact hqne h2
        have hnc0 : ∃ x x', forestFun G ∅ (Function.update x ℓ false) ≠
            forestFun G ∅ (Function.update x' ℓ false) := by
          simpa only [← congrFun hrew0] using forestFun_nonconst (G.deleteEdges {s(ℓ, p)}) ∅ (Or.inr hEdge0)
        have hnc1 : ∃ x x', forestFun G ∅ (Function.update x ℓ true) ≠
            forestFun G ∅ (Function.update x' ℓ true) := by
          simpa only [← congrFun hrew1] using
            forestFun_nonconst (deleteVertexEdges G p) {p} (Or.inl (Finset.singleton_nonempty p))
        have hF0_0 : forestFun G ∅ (Function.update (fun _ => false) ℓ false) = false := by
          rw [congrFun hrew0]; exact forestFun_false _ _
        have hF0_1 : forestFun G ∅ (Function.update (fun _ => false) ℓ true) = false := by
          rw [congrFun hrew1]; exact forestFun_false _ _
        have hF0_p : forestFun G ∅ (Function.update (fun _ => false) p false) = false := by
          rw [congrFun hrewp]; exact forestFun_false _ _
        by_cases hEdgep : ∃ u v : Fin n, (deleteVertexEdges G p).Adj u v
        · have hncp : ∃ x x', forestFun G ∅ (Function.update x p false) ≠
              forestFun G ∅ (Function.update x' p false) := by
            simpa only [← congrFun hrewp] using forestFun_nonconst (deleteVertexEdges G p) ∅ (Or.inr hEdgep)
          have hkill : ∀ (x : Fin n → Bool) (b : Bool),
              forestFun G ∅ (Function.update (Function.update x p false) ℓ b) =
              forestFun G ∅ (Function.update x p false) := by
            intro x b
            have hsw : Function.update (Function.update x p false) ℓ b =
                Function.update (Function.update x ℓ b) p false := Function.update_comm hlp.ne.symm _ _ x
            rw [hsw, congrFun hrewp, congrFun hrewp]
            simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or]
            apply decide_eq_decide.2
            have hℓ_iso : ∀ u v : Fin n, (deleteVertexEdges G p).Adj u v → u ≠ ℓ ∧ v ≠ ℓ := by
              intro u v huv
              exact ⟨fun h => huv.2.2 (hleaf v (h ▸ huv.1)), fun h => huv.2.1 (hleaf u (h ▸ huv.1.symm))⟩
            constructor
            · rintro ⟨u, v, huv, hux, hvx⟩
              have ⟨hu, hv⟩ := hℓ_iso u v huv
              rw [Function.update_of_ne hu] at hux
              rw [Function.update_of_ne hv] at hvx
              exact ⟨u, v, huv, hux, hvx⟩
            · rintro ⟨u, v, huv, hux, hvx⟩
              have ⟨hu, hv⟩ := hℓ_iso u v huv
              exact ⟨u, v, huv, by rw [Function.update_of_ne hu]; exact hux,
                by rw [Function.update_of_ne hv]; exact hvx⟩
          have h3sub : ∀ (x₀ : Fin n → Bool), (∀ i, i ≠ ℓ → i ≠ p → i ≠ q → x₀ i = false) →
              forestFun G ∅ (Function.update (Function.update (Function.update x₀ p false) ℓ false) q false) = false ∧
              forestFun G ∅ (Function.update (Function.update (Function.update x₀ p false) ℓ false) q true) = false ∧
              forestFun G ∅ (Function.update (Function.update (Function.update x₀ p true) ℓ false) q false) = false ∧
              forestFun G ∅ (Function.update (Function.update (Function.update x₀ p true) ℓ false) q true) = true ∧
              forestFun G ∅ (Function.update (Function.update (Function.update x₀ p true) ℓ true) q false) = true ∧
              forestFun G ∅ (Function.update (Function.update (Function.update x₀ p true) ℓ true) q true) = true := by
            intro x₀ hx₀
            have honly : ∀ (bp bℓ bq : Bool) (i : Fin n),
                Function.update (Function.update (Function.update x₀ p bp) ℓ bℓ) q bq i = true →
                (i = q ∧ bq = true) ∨ (i = ℓ ∧ bℓ = true) ∨ (i = p ∧ bp = true) := by
              intro bp bℓ bq i hi
              by_cases hiq : i = q
              · subst hiq; simp at hi; exact Or.inl ⟨rfl, hi⟩
              · rw [Function.update_of_ne hiq] at hi
                by_cases hiℓ : i = ℓ
                · subst hiℓ; simp at hi; exact Or.inr (Or.inl ⟨rfl, hi⟩)
                · rw [Function.update_of_ne hiℓ] at hi
                  by_cases hip : i = p
                  · subst hip; simp at hi; exact Or.inr (Or.inr ⟨rfl, hi⟩)
                  · rw [Function.update_of_ne hip, hx₀ i hiℓ hip hiq] at hi; exact Bool.noConfusion hi
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_false_iff_not]
              rintro ⟨u, v, _, hu, _⟩
              rcases honly false false false u hu with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact Bool.noConfusion h
            · simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_false_iff_not]
              rintro ⟨u, v, huv, hu, hv⟩
              rcases honly false false true u hu with ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
              · rcases honly false false true v hv with ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
                · exact G.loopless.irrefl _ huv
                · exact Bool.noConfusion h
                · exact Bool.noConfusion h
              · exact Bool.noConfusion h
              · exact Bool.noConfusion h
            · simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_false_iff_not]
              rintro ⟨u, v, huv, hu, hv⟩
              rcases honly true false false u hu with ⟨_, h⟩ | ⟨_, h⟩ | ⟨rfl, _⟩
              · exact Bool.noConfusion h
              · exact Bool.noConfusion h
              · rcases honly true false false v hv with ⟨_, h⟩ | ⟨_, h⟩ | ⟨rfl, _⟩
                · exact Bool.noConfusion h
                · exact Bool.noConfusion h
                · exact G.loopless.irrefl _ huv
            · simp only [forestFun, decide_eq_true_eq]
              exact Or.inr ⟨p, q, hpq,
                by rw [Function.update_of_ne hpq.ne, Function.update_of_ne hlp.ne.symm]; simp,
                by simp⟩
            · simp only [forestFun, decide_eq_true_eq]
              exact Or.inr ⟨ℓ, p, hlp,
                by rw [Function.update_of_ne hqne.symm]; simp,
                by rw [Function.update_of_ne hpq.ne, Function.update_of_ne hlp.ne.symm]; simp⟩
            · simp only [forestFun, decide_eq_true_eq]
              exact Or.inr ⟨ℓ, p, hlp,
                by rw [Function.update_of_ne hqne.symm]; simp,
                by rw [Function.update_of_ne hpq.ne, Function.update_of_ne hlp.ne.symm]; simp⟩
          rcases elim_leaf_parent ℓ p q hlp.ne hqne hpq.ne.symm hC hdep hnc0 hnc1 hncp
              hF0_0 hF0_1 hF0_p hkill h3sub with ⟨hs2, hC0⟩ | ⟨hs2, hC1⟩ | ⟨hs3, hCp⟩
          · rw [hrew0] at hC0
            obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (G.deleteEdges {s(ℓ, p)})
            have ht₁ := (hasMinVC_deleteEdge G ℓ p hvc hvc₁).2
            have hih := ih (s - 2) (by omega) (G.deleteEdges {s(ℓ, p)}) ∅
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) (Or.inr hEdge0) hvc₁ hC0
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
          · rw [hrewp] at hCp
            obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges G p)
            have ht' : t' + 1 = t := hasMinVC_deleteVertex G ℓ p hlp hleaf hvc hvc'
            have hih := ih (s - 3) (by omega) (deleteVertexEdges G p) ∅
              (hAcyc.anti (deleteVertexEdges_le G p)) (by simp) (Or.inr hEdgep) hvc' hCp
            have hedge := edgeFinset_card_deleteVertex_deg2 G ℓ p q hlp hpq hqne hpdeg2
            simp only [Finset.card_empty, zero_add] at hih ⊢
            omega
        · push_neg at hEdgep
          have ht' : t = 1 := by
            obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges G p)
            have h1 := hasMinVC_empty (deleteVertexEdges G p) hEdgep hvc'
            have h2 := hasMinVC_deleteVertex G ℓ p hlp hleaf hvc hvc'
            omega
          have he2 : G.edgeFinset.card = 2 := by
            have h0 : (deleteVertexEdges G p).edgeFinset.card = 0 := by
              apply Finset.card_eq_zero.2; ext e
              induction e using Sym2.ind with
              | _ u v => simp [SimpleGraph.mem_edgeFinset, hEdgep u v]
            have := edgeFinset_card_deleteVertex_deg2 G ℓ p q hlp hpq hqne hpdeg2
            omega
          obtain ⟨hs1, hC0⟩ := elim_one_var ℓ false hC hdep hnc0 hF0_0
          rw [hrew0] at hC0
          have hih := ih (s - 1) (by omega) (G.deleteEdges {s(ℓ, p)}) ∅
            (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) (Or.inr hEdge0)
            (by
              obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (G.deleteEdges {s(ℓ, p)})
              have hle : t₁ ≤ 1 := by
                have := (hasMinVC_deleteEdge G ℓ p hvc hvc₁).1; omega
              have hge : 1 ≤ t₁ := by
                obtain ⟨⟨S₁, hS₁, hSc⟩, _⟩ := hvc₁
                obtain ⟨u, v, huv⟩ := hEdge0
                rcases hS₁ u v huv with hu | hv
                · have := Finset.one_le_card.2 ⟨u, hu⟩; omega
                · have := Finset.one_le_card.2 ⟨v, hv⟩; omega
              have ht1eq : t₁ = 1 := by omega
              rwa [ht1eq] at hvc₁)
            hC0
          have hedge := edgeFinset_card_deleteEdge G ℓ p hlp
          simp only [Finset.card_empty, zero_add] at hih ⊢
          omega

def pushOrList (m : ℕ) (gs : List BinaryGate) (acc : ℕ) : List ℕ → List BinaryGate × ℕ
  | [] => (gs, acc)
  | w :: ws => pushOrList m (gs ++ [⟨or, acc, w⟩]) (m + gs.length) ws

lemma pushOrList_props (m : ℕ) (ws : List ℕ) :
    ∀ (gs : List BinaryGate) (acc : ℕ),
      acc < m + gs.length →
      (∀ w ∈ ws, w < m + gs.length) →
      (pushOrList m gs acc ws).1.length = gs.length + ws.length ∧
      (pushOrList m gs acc ws).2 < m + (pushOrList m gs acc ws).1.length ∧
      (∀ x : List Bool, x.length = m →
        (∀ i < m + gs.length,
          (bWires (pushOrList m gs acc ws).1 x).getD i false = (bWires gs x).getD i false) ∧
        (bWires (pushOrList m gs acc ws).1 x).getD (pushOrList m gs acc ws).2 false =
          ((bWires gs x).getD acc false || ws.any (fun w => (bWires gs x).getD w false))) := by
  induction ws with
  | nil =>
    intro gs acc hacc _
    exact ⟨by simp [pushOrList], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushOrList]⟩⟩
  | cons w ws ih =>
    intro gs acc hacc hws
    set gs' := gs ++ [⟨or, acc, w⟩] with hgs'
    have hlen' : gs'.length = gs.length + 1 := by simp [hgs']
    have hacc' : m + gs.length < m + gs'.length := by omega
    have hws' : ∀ u ∈ ws, u < m + gs'.length := fun u hu => by
      have := hws u (List.mem_cons_of_mem _ hu); omega
    obtain ⟨h1, h2, h3⟩ := ih gs' (m + gs.length) hacc' hws'
    refine ⟨by simp only [pushOrList, List.length_cons]; rw [← hgs', h1, hlen']; omega, by simpa [pushOrList] using h2, ?_⟩
    intro x hx
    obtain ⟨hpres, hval⟩ := h3 x hx
    have hstep_pres : ∀ i < m + gs.length,
        (bWires gs' x).getD i false = (bWires gs x).getD i false := by
      intro i hi
      rw [hgs', bWires_append, bWires_cons, bWires_nil,
          getD_snoc_lt _ _ _ _ (by rw [bWires_length, hx]; exact hi)]
    have hstep_new : (bWires gs' x).getD (m + gs.length) false =
        ((bWires gs x).getD acc false || (bWires gs x).getD w false) := by
      rw [hgs', bWires_append, bWires_cons, bWires_nil,
          getD_snoc_eq _ _ _ _ (by rw [bWires_length, hx])]
    refine ⟨fun i hi => by rw [pushOrList, hpres i (by omega), hstep_pres i hi], ?_⟩
    rw [pushOrList, hval, hstep_new]
    have hany : ws.any (fun u => (bWires gs' x).getD u false) =
        ws.any (fun u => (bWires gs x).getD u false) := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨u, hu, h⟩; exact ⟨u, hu, by rw [← hstep_pres u (hws u (List.mem_cons_of_mem _ hu))]; exact h⟩
      · rintro ⟨u, hu, h⟩; exact ⟨u, hu, by rw [hstep_pres u (hws u (List.mem_cons_of_mem _ hu))]; exact h⟩
    rw [hany, List.any_cons, Bool.or_assoc]

def buildStars (m : ℕ) (gs : List BinaryGate) (outs : List ℕ) :
    List (ℕ × List ℕ) → List BinaryGate × List ℕ
  | [] => (gs, outs)
  | (_, []) :: rest => buildStars m gs outs rest
  | (u, v :: vs) :: rest =>
    let r := pushOrList m gs v vs
    buildStars m (r.1 ++ [⟨and, u, r.2⟩]) (outs ++ [m + r.1.length]) rest

lemma buildStars_props (m : ℕ) (stars : List (ℕ × List ℕ)) :
    ∀ (gs : List BinaryGate) (outs : List ℕ),
      (∀ w ∈ outs, w < m + gs.length) →
      (∀ p ∈ stars, p.1 < m + gs.length ∧ ∀ v ∈ p.2, v < m + gs.length) →
      (buildStars m gs outs stars).1.length ≤ gs.length + (stars.map (fun p => p.2.length)).sum ∧
      (buildStars m gs outs stars).2.length ≤ outs.length + stars.length ∧
      (∀ w ∈ (buildStars m gs outs stars).2, w < m + (buildStars m gs outs stars).1.length) ∧
      (∀ x : List Bool, x.length = m →
        (∀ i < m + gs.length,
          (bWires (buildStars m gs outs stars).1 x).getD i false = (bWires gs x).getD i false) ∧
        (buildStars m gs outs stars).2.any (fun w => (bWires (buildStars m gs outs stars).1 x).getD w false) =
          (outs.any (fun w => (bWires gs x).getD w false) ||
           stars.any (fun p => (bWires gs x).getD p.1 false && p.2.any (fun v => (bWires gs x).getD v false)))) := by
  induction stars with
  | nil =>
    intro gs outs houts _
    refine ⟨by simp [buildStars], by simp [buildStars], houts,
      fun x _ => ⟨fun _ _ => rfl, by simp [buildStars]⟩⟩
  | cons p rest ih =>
    intro gs outs houts hst
    rcases p with ⟨u, vs⟩
    cases vs with
    | nil =>
      obtain ⟨h1, h2, h3, h4⟩ := ih gs outs houts (fun q hq => hst q (List.mem_cons_of_mem _ hq))
      refine ⟨by simp only [buildStars, List.map_cons, List.sum_cons, List.length_nil, zero_add]; exact h1,
        by simp only [buildStars, List.length_cons]; omega, h3, ?_⟩
      intro x hx
      obtain ⟨hp, hv⟩ := h4 x hx
      exact ⟨hp, by simpa [buildStars] using hv⟩
    | cons v vs =>
      have hp0 := hst (u, v :: vs) List.mem_cons_self
      obtain ⟨hrlen, hrlt, hrev⟩ := pushOrList_props m vs gs v
        (hp0.2 v List.mem_cons_self) (fun w hw => hp0.2 w (List.mem_cons_of_mem _ hw))
      set r := pushOrList m gs v vs with hr
      set gs1 := r.1 ++ [⟨and, u, r.2⟩] with hgs1
      set outs1 := outs ++ [m + r.1.length] with houts1
      have hgs1_len : gs1.length = gs.length + (v :: vs).length := by
        simp [hgs1, hrlen]; omega
      have houts1_lt : ∀ w ∈ outs1, w < m + gs1.length := by
        intro w hw
        rcases List.mem_append.1 hw with h | h
        · have := houts w h; omega
        · simp at h; subst h; simp [hgs1]
      have hrest_lt : ∀ q ∈ rest, q.1 < m + gs1.length ∧ ∀ w ∈ q.2, w < m + gs1.length := by
        intro q hq
        have h := hst q (List.mem_cons_of_mem _ hq)
        exact ⟨by omega, fun w hw => by have := h.2 w hw; omega⟩
      obtain ⟨h1, h2, h3, h4⟩ := ih gs1 outs1 houts1_lt hrest_lt
      have houts1_len : outs1.length = outs.length + 1 := by simp [houts1]
      refine ⟨by simp only [buildStars, List.map_cons, List.sum_cons]; rw [← hr, ← hgs1, ← houts1]; omega,
        by simp only [buildStars, List.length_cons]; rw [← hr, ← hgs1, ← houts1]; omega,
        by simpa [buildStars] using h3, ?_⟩
      intro x hx
      obtain ⟨hpres_r, hval_r⟩ := hrev x hx
      obtain ⟨hpres_rest, hval_rest⟩ := h4 x hx
      have hpres1 : ∀ i < m + gs.length, (bWires gs1 x).getD i false = (bWires gs x).getD i false := by
        intro i hi
        rw [hgs1, bWires_append, bWires_cons, bWires_nil,
            getD_snoc_lt _ _ _ _ (by rw [bWires_length, hx]; omega)]
        exact hpres_r i hi
      have hnew : (bWires gs1 x).getD (m + r.1.length) false =
          ((bWires gs x).getD u false && (v :: vs).any (fun w => (bWires gs x).getD w false)) := by
        rw [hgs1, bWires_append, bWires_cons, bWires_nil,
            getD_snoc_eq _ _ _ _ (by rw [bWires_length, hx]),
            hpres_r u hp0.1, hval_r, List.any_cons]
      refine ⟨fun i hi => by
          simp only [buildStars]
          rw [hpres_rest i (by omega), hpres1 i hi], ?_⟩
      simp only [buildStars]
      rw [hval_rest]
      have houts1_any : outs1.any (fun w => (bWires gs1 x).getD w false) =
          (outs.any (fun w => (bWires gs x).getD w false) ||
           ((bWires gs x).getD u false && (v :: vs).any (fun w => (bWires gs x).getD w false))) := by
        rw [houts1, List.any_append, List.any_cons, List.any_nil, Bool.or_false, hnew]
        congr 1
        apply Bool.eq_iff_iff.2
        simp only [List.any_eq_true]
        constructor
        · rintro ⟨w, hw, h⟩; exact ⟨w, hw, by rw [← hpres1 w (houts w hw)]; exact h⟩
        · rintro ⟨w, hw, h⟩; exact ⟨w, hw, by rw [hpres1 w (houts w hw)]; exact h⟩
      have hrest_any : rest.any (fun p => (bWires gs1 x).getD p.1 false &&
            p.2.any (fun v => (bWires gs1 x).getD v false)) =
          rest.any (fun p => (bWires gs x).getD p.1 false &&
            p.2.any (fun v => (bWires gs x).getD v false)) := by
        apply Bool.eq_iff_iff.2
        simp only [List.any_eq_true, Bool.and_eq_true]
        constructor
        · rintro ⟨q, hq, hq1, w, hw, hqw⟩
          have hqlt := hst q (List.mem_cons_of_mem _ hq)
          exact ⟨q, hq, by rw [← hpres1 q.1 hqlt.1]; exact hq1,
            w, hw, by rw [← hpres1 w (hqlt.2 w hw)]; exact hqw⟩
        · rintro ⟨q, hq, hq1, w, hw, hqw⟩
          have hqlt := hst q (List.mem_cons_of_mem _ hq)
          exact ⟨q, hq, by rw [hpres1 q.1 hqlt.1]; exact hq1,
            w, hw, by rw [hpres1 w (hqlt.2 w hw)]; exact hqw⟩
      rw [houts1_any, hrest_any, Bool.or_assoc]
      simp only [List.any_cons]

lemma upper_bound_aux {n t s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n))
    (hne : A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v)
    (hvc_ex : ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hs : A.card + G.edgeFinset.card + t ≤ s + 1) :
    HasBinarySize n (forestFun G A) s := by
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
  set wsA : List ℕ := A.toList.map Fin.val with hwsA
  obtain ⟨hblen, hbout_len, hbout_lt, hbev⟩ := buildStars_props n stars [] wsA
    (fun w hw => by obtain ⟨a, _, rfl⟩ := List.mem_map.1 hw; simp)
    (fun p hp => by
      obtain ⟨u, _, rfl⟩ := List.mem_map.1 hp
      exact ⟨by simp, fun v hv => by obtain ⟨v', _, rfl⟩ := List.mem_map.1 hv; simp⟩)
  set r1 := buildStars n [] wsA stars with hr1
  have hstars_sum : (stars.map (fun p => p.2.length)).sum = G.edgeFinset.card := by
    have hmap : stars.map (fun p => p.2.length) = S.toList.map (fun u : Fin n => (N u).card) := by
      simp [hstars, List.map_map, Function.comp_def]
    have hsum_list : (S.toList.map (fun u : Fin n => (N u).card)).sum = ∑ u ∈ S, (N u).card := by
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
    rw [hmap, hsum_list, hsum_N]
  have hr1_ne : r1.2 ≠ [] := by
    intro hnil
    obtain ⟨_, hval1⟩ := hbev (List.ofFn (fun _ : Fin n => true)) (by simp)
    rw [hnil, List.any_nil] at hval1
    have htrue : (wsA.any (fun w => (bWires [] (List.ofFn (fun _ : Fin n => true))).getD w false) ||
        stars.any (fun p => (bWires [] (List.ofFn (fun _ : Fin n => true))).getD p.1 false &&
          p.2.any (fun v => (bWires [] (List.ofFn (fun _ : Fin n => true))).getD v false))) = true := by
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
      · left
        exact ⟨(a : ℕ), List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩,
          by rw [bWires_nil, ofFn_getD_lt _ _ _ a.isLt]⟩
      · right
        have hex_pair : ∃ u' ∈ S, ∃ v' ∈ N u', True := by
          rcases hS_vc u v huv with hu | hv
          · by_cases hvu : v ∈ S ∧ v < u
            · exact ⟨v, hvu.1, u, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.symm, fun _ => hvu.2⟩, trivial⟩
            · refine ⟨u, hu, v, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, fun hv' => ?_⟩, trivial⟩
              rcases lt_trichotomy u v with h | h | h
              · exact h
              · exact absurd h huv.ne
              · exact absurd ⟨hv', h⟩ hvu
          · by_cases huv' : u ∈ S ∧ u < v
            · exact ⟨u, huv'.1, v, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, fun _ => huv'.2⟩, trivial⟩
            · refine ⟨v, hv, u, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.symm, fun hu' => ?_⟩, trivial⟩
              rcases lt_trichotomy v u with h | h | h
              · exact h
              · exact absurd h huv.ne.symm
              · exact absurd ⟨hu', h⟩ huv'
        obtain ⟨u', hu', v', hv', _⟩ := hex_pair
        refine ⟨((u' : ℕ), (N u').toList.map Fin.val),
          List.mem_map.2 ⟨u', Finset.mem_toList.2 hu', rfl⟩,
          by rw [bWires_nil, ofFn_getD_lt _ _ _ u'.isLt],
          (v' : ℕ), List.mem_map.2 ⟨v', Finset.mem_toList.2 hv', rfl⟩,
          by rw [bWires_nil, ofFn_getD_lt _ _ _ v'.isLt]⟩
    rw [htrue] at hval1
    exact Bool.false_ne_true hval1
  cases hr1_2 : r1.2 with
  | nil => exact absurd hr1_2 hr1_ne
  | cons w0 ws =>
    obtain ⟨h2len, _, h2ev⟩ := pushOrList_props n ws r1.1 w0
      (hbout_lt w0 (by rw [hr1_2]; simp))
      (fun w hw => hbout_lt w (by rw [hr1_2]; simp [hw]))
    set r2 := pushOrList n r1.1 w0 ws with hr2
    have hws_len : ws.length + 1 ≤ A.card + t := by
      have h1 : ws.length + 1 = r1.2.length := by rw [hr1_2]; simp
      have h2 : wsA.length = A.card := by simp [hwsA]
      have h3 : stars.length = t := by simp [hstars, hS_card]
      omega
    have htot_len : r2.1.length ≤ s := by
      simp only [List.length_nil, zero_add] at hblen
      rw [hstars_sum] at hblen
      omega
    refine ⟨⟨r2.1, r2.2⟩, htot_len, ?_⟩
    intro x
    obtain ⟨_, hval1⟩ := hbev (List.ofFn x) (by simp)
    obtain ⟨_, hval2⟩ := h2ev (List.ofFn x) (by simp)
    show (bWires r2.1 (List.ofFn x)).getD r2.2 false = forestFun G A x
    have hcons : ((bWires r1.1 (List.ofFn x)).getD w0 false ||
        ws.any (fun w => (bWires r1.1 (List.ofFn x)).getD w false)) =
        (w0 :: ws).any (fun w => (bWires r1.1 (List.ofFn x)).getD w false) := rfl
    rw [hval2, hcons, ← hr1_2, hval1]
    have hA_eq : wsA.any (fun w => (bWires [] (List.ofFn x)).getD w false) =
        decide (∃ a ∈ A, x a = true) := by
      apply Bool.eq_iff_iff.2
      simp only [hwsA, List.any_map, List.any_eq_true, Function.comp_apply, Finset.mem_toList,
        decide_eq_true_eq, bWires_nil]
      constructor
      · rintro ⟨a, ha, h⟩; rw [ofFn_getD_lt _ _ _ a.isLt] at h; exact ⟨a, ha, h⟩
      · rintro ⟨a, ha, h⟩; exact ⟨a, ha, by rw [ofFn_getD_lt _ _ _ a.isLt]; exact h⟩
    have hS_eq : stars.any (fun p => (bWires [] (List.ofFn x)).getD p.1 false &&
          p.2.any (fun v => (bWires [] (List.ofFn x)).getD v false)) =
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
      apply Bool.eq_iff_iff.2
      simp only [hstars, List.any_map, List.any_eq_true, Function.comp_apply, Bool.and_eq_true,
        Finset.mem_toList, decide_eq_true_eq, bWires_nil]
      constructor
      · rintro ⟨u, _, hux, v, hv, hvx⟩
        rw [ofFn_getD_lt _ _ _ u.isLt] at hux
        rw [ofFn_getD_lt _ _ _ v.isLt] at hvx
        exact ⟨u, v, (Finset.mem_filter.1 hv).2.1, hux, hvx⟩
      · rintro ⟨u, v, huv, hux, hvx⟩
        rcases hS_vc u v huv with hu | hv
        · by_cases hvu : v ∈ S ∧ v < u
          · exact ⟨v, hvu.1, by rw [ofFn_getD_lt _ _ _ v.isLt]; exact hvx,
              u, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.symm, fun _ => hvu.2⟩,
              by rw [ofFn_getD_lt _ _ _ u.isLt]; exact hux⟩
          · refine ⟨u, hu, by rw [ofFn_getD_lt _ _ _ u.isLt]; exact hux,
              v, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, fun hv' => ?_⟩,
              by rw [ofFn_getD_lt _ _ _ v.isLt]; exact hvx⟩
            rcases lt_trichotomy u v with h | h | h
            · exact h
            · exact absurd h huv.ne
            · exact absurd ⟨hv', h⟩ hvu
        · by_cases huv' : u ∈ S ∧ u < v
          · exact ⟨u, huv'.1, by rw [ofFn_getD_lt _ _ _ u.isLt]; exact hux,
              v, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, fun _ => huv'.2⟩,
              by rw [ofFn_getD_lt _ _ _ v.isLt]; exact hvx⟩
          · refine ⟨v, hv, by rw [ofFn_getD_lt _ _ _ v.isLt]; exact hvx,
              u, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.symm, fun hu' => ?_⟩,
              by rw [ofFn_getD_lt _ _ _ u.isLt]; exact hux⟩
            rcases lt_trichotomy v u with h | h | h
            · exact h
            · exact absurd h huv.ne.symm
            · exact absurd ⟨hu', h⟩ huv'
    rw [hA_eq, hS_eq]
    apply Bool.eq_iff_iff.2
    simp [forestFun]

end PEqualNP.Outside.L_meta_244

theorem PEqualNP.Outside.L_meta_244 : ∀ (n t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)), G.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (PEqualNP.MetaComplexity.HasBinarySize n (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) s ↔ A.card + G.edgeFinset.card + t ≤ s + 1) := by
  intro n t s G _ A hAcyc hA_iso hne hvc_ex hvc_min
  exact ⟨PEqualNP.Outside.L_meta_244.lower_bound_aux s G A hAcyc hA_iso hne ⟨hvc_ex, hvc_min⟩,
    PEqualNP.Outside.L_meta_244.upper_bound_aux G A hne hvc_ex⟩
