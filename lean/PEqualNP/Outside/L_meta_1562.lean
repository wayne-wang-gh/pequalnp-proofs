import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1562

open PEqualNP.CircuitLowerBounds

private def evalGates (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

private lemma evalGates_cons (g : Gate) (gs : List Gate) (xs : List Bool) :
    evalGates (g :: gs) xs =
      evalGates gs (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) :=
  rfl

private lemma evalGates_length (gs : List Gate) (xs : List Bool) :
    (evalGates gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalGates]
  | cons g gs ih =>
    rw [evalGates_cons, ih]
    simp
    omega

private lemma evalGates_prefix (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (evalGates gs xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalGates_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma evalGates_take_drop (gs : List Gate) (xs : List Bool) (k : ℕ) :
    evalGates gs xs = evalGates (gs.drop k) (evalGates (gs.take k) xs) := by
  simpa only [evalGates, List.foldl_append] using
    congrArg (fun l : List Gate => evalGates l xs) (List.take_append_drop k gs).symm

private def wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    wireVal C x p = x p := by
  change (evalGates C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [evalGates_prefix _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma wireVal_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wireVal C x w = false := by
  change (evalGates C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [evalGates_length] using hw)

private lemma wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.gates.length) :
    let g := C.gates[w - n]'(by omega)
    wireVal C x w = g.op.eval (g.inputs.map fun r => if r < w then wireVal C x r else false) := by
  let idx := w - n
  have hidx : idx < C.gates.length := by omega
  let g := C.gates[idx]
  let pref := evalGates (C.gates.take idx) (List.ofFn x)
  have hplen : pref.length = w := by
    simp [pref, evalGates_length, Nat.min_eq_left hidx.le, idx]
    omega
  have hsplit :
      evalGates C.gates (List.ofFn x) = evalGates (g :: C.gates.drop (idx + 1)) pref := by
    rw [evalGates_take_drop C.gates (List.ofFn x) idx, List.drop_eq_getElem_cons hidx]
  have hread (r : ℕ) : pref.getD r false = if r < w then wireVal C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change pref.getD r false = (evalGates C.gates (List.ofFn x)).getD r false
      rw [hsplit]
      exact (evalGates_prefix _ pref r (by omega)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (evalGates C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then wireVal C x r else false)
  rw (occs := [1]) [hsplit]
  rw (occs := [1]) [evalGates_cons]
  rw [evalGates_prefix _ _ _ (by simp [hplen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [hplen, Nat.sub_self, List.getD_cons_zero, hread]

private lemma gate_deps {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.gates.length) :
    ∃ D : Finset ℕ, D.card ≤ 2 ∧ (∀ r ∈ D, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ D, wireVal C x r = true → wireVal C y r = true) →
        wireVal C x w = true → wireVal C y w = true := by
  classical
  let g := C.gates[w - n]'(by omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let D := g.inputs.toFinset.filter (· < w)
  refine ⟨D, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hstep (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then wireVal C x r else false) = true →
        (if r < w then wireVal C y r else false) = true := by
      by_cases hlt : r < w
      · simpa [hlt] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hlt⟩)
      · simp [hlt]
    have hform (z : Fin n → Bool) :
        wireVal C z w = g.op.eval (g.inputs.map fun r => if r < w then wireVal C z r else false) :=
      wireVal_gate C z w hn hw
    rw [hform x] at hx
    rw [hform y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      exact hstep r hr (hx _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hbt⟩ := hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, hstep r hr hbt⟩

private lemma wireVal_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    wireVal C x w = true → wireVal C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change wireVal C x p = true → wireVal C y p = true
      simpa only [wireVal_input] using hxy p
    · by_cases hw : w < n + C.gates.length
      · obtain ⟨D, _, hD, hstep⟩ := gate_deps C hG w (by omega) hw
        exact hstep x y fun r hr => ih r (hD r hr)
      · simp [wireVal_oob C x w (by omega)]

private lemma peel_cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (A : Finset ℕ) (hA : ∀ w ∈ A, n ≤ w ∧ w < n + C.gates.length)
    (k : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ A → w < k) :
    ∃ B : Finset ℕ, Disjoint B A ∧ B.card ≤ F.card + (A.filter (· < k)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, wireVal C x w = true → wireVal C y w = true) →
        ∀ w ∈ F, wireVal C x w = true → wireVal C y w = true := by
  induction k generalizing F with
  | zero =>
    refine ⟨F, Finset.disjoint_left.mpr fun w hw ha => by have := hF w hw ha; omega,
      Nat.le_add_right _ _, fun _ _ h => h⟩
  | succ k ih =>
    by_cases hmem : k ∈ F ∧ k ∈ A
    · obtain ⟨D, hDcard, hDlt, hstep⟩ := gate_deps C hG k (hA k hmem.2).1 (hA k hmem.2).2
      let F' := F.erase k ∪ D
      have hF' : ∀ w ∈ F', w ∈ A → w < k := by
        intro w hw ha
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 ha
          omega
        · exact hDlt w hw
      obtain ⟨B, hdisj, hcard, hpres⟩ := ih F' hF'
      have hF'card : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase k) D
        have he := Finset.card_erase_add_one hmem.1
        change F'.card ≤ _ at hu
        omega
      have hflt : A.filter (· < k + 1) = insert k (A.filter (· < k)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨ha, hlt⟩
          by_cases heq : w = k
          · exact Or.inl heq
          · exact Or.inr ⟨ha, by omega⟩
        · rintro (rfl | ⟨ha, hlt⟩)
          · exact ⟨hmem.2, by omega⟩
          · exact ⟨ha, by omega⟩
      refine ⟨B, hdisj, ?_, ?_⟩
      · rw [hflt, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases heq : w = k
        · subst w
          exact hstep x y fun r hr => hpres x y hxy r (Finset.mem_union_right _ hr)
        · exact hpres x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ A → w < k := by
        intro w hw ha
        have hne : w ≠ k := fun h => hmem ⟨h ▸ hw, h ▸ ha⟩
        have hlt := hF w hw ha
        omega
      obtain ⟨B, hdisj, hcard, hpres⟩ := ih F hF'
      have hmono : (A.filter (· < k)).card ≤ (A.filter (· < k + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hdisj, by omega, hpres⟩

private def BelowSet {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wireVal C x w = true → ∃ p ∈ T, x p = true

private def firePts {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => wireVal C (fun v => decide (v ∈ Y ∨ v = p)) w = true

private lemma mem_firePts {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ firePts C Y w ↔ wireVal C (fun v => decide (v ∈ Y ∨ v = p)) w = true := by
  simp [firePts]

private noncomputable def chargedGates {n : ℕ} (C : Circuit)
    (Y T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.gates.length)).filter fun w =>
    BelowSet C T w ∧ 2 ≤ (firePts C Y w).card

private lemma mem_chargedGates {n : ℕ} (C : Circuit)
    (Y T : Finset (Fin n)) (w : ℕ) :
    w ∈ chargedGates C Y T ↔
      (n ≤ w ∧ w < n + C.gates.length) ∧ BelowSet C T w ∧ 2 ≤ (firePts C Y w).card := by
  classical
  unfold chargedGates
  rw [Finset.mem_filter, Finset.mem_Ico]

private lemma multi_fire_is_gate {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ)
    (hYT : Disjoint Y T) (hb : BelowSet C T w) (h2 : 2 ≤ (firePts C Y w).card) :
    n ≤ w ∧ w < n + C.gates.length := by
  constructor
  · by_contra! hlt
    let p0 : Fin n := ⟨w, hlt⟩
    have hp0Y : p0 ∉ Y := by
      intro hmem
      have hv : wireVal C (fun v => decide (v ∈ Y)) w = true := by
        change wireVal C (fun v => decide (v ∈ Y)) p0 = true
        rw [wireVal_input]
        simpa using hmem
      obtain ⟨q, hqT, hqY⟩ := hb _ hv
      exact Finset.disjoint_left.mp hYT (by simpa using hqY) hqT
    have hsub : firePts C Y w ⊆ {p0} := by
      intro q hq
      have hv := (mem_firePts C Y w q).mp hq
      change wireVal C (fun v => decide (v ∈ Y ∨ v = q)) p0 = true at hv
      rw [wireVal_input] at hv
      simp only [decide_eq_true_eq] at hv
      rcases hv with hmem | rfl
      · exact absurd hmem hp0Y
      · simp
    have hle := Finset.card_le_card hsub
    simp at hle
    omega
  · by_contra! hge
    have hempty : firePts (n := n) C Y w = ∅ := by
      ext q
      simp [mem_firePts, wireVal_oob C _ w hge]
    simp [hempty] at h2

private lemma per_family_bound {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (o : ℕ) (hYT : Disjoint Y T) (hbo : BelowSet C T o)
    (hfire : ∀ p ∈ T, wireVal C (fun v => decide (v ∈ Y ∨ v = p)) o = true) :
    T.card ≤ (chargedGates C Y T).card + 1 := by
  classical
  let A := chargedGates C Y T
  by_contra! hlt
  have hA : ∀ w ∈ A, n ≤ w ∧ w < n + C.gates.length :=
    fun w hw => ((mem_chargedGates C Y T w).mp hw).1
  obtain ⟨B, hdisj, hBcard, hcut⟩ :=
    peel_cut C hG A hA (n + C.gates.length) {o} fun w _ hw => (hA w hw).2
  have hBsmall : B.card ≤ A.card + 1 := by
    have hflt := Finset.card_filter_le A (fun w => w < n + C.gates.length)
    simp only [Finset.card_singleton] at hBcard
    omega
  let soundPts (w : ℕ) : Finset (Fin n) := if BelowSet C T w then firePts C Y w else ∅
  have hsoundCard : ∀ w ∈ B, (soundPts w).card ≤ 1 := by
    intro w hw
    by_cases hb : BelowSet C T w
    · simp only [soundPts, ite_eq_left hb]
      by_contra! h2
      have hgate := multi_fire_is_gate C Y T w hYT hb (by omega)
      exact Finset.disjoint_left.mp hdisj hw ((mem_chargedGates C Y T w).mpr ⟨hgate, hb, by omega⟩)
    · simp [soundPts, hb]
  have hcov : (B.biUnion soundPts).card < T.card := by
    have hle := Finset.card_biUnion_le_card_mul B soundPts 1 hsoundCard
    simp only [mul_one] at hle
    have hA' : A.card + 1 < T.card := hlt
    omega
  obtain ⟨p, hpT, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcov
  let Bad := B.filter fun w => ¬ BelowSet C T w
  have hexBad (w : {w // w ∈ Bad}) :
      ∃ x : Fin n → Bool, wireVal C x w.val = true ∧ ∀ q ∈ T, x q = false := by
    have hnb := (Finset.mem_filter.mp w.property).2
    unfold BelowSet at hnb
    push Not at hnb
    obtain ⟨x, hx, hxT⟩ := hnb
    exact ⟨x, hx, fun q hq => by simpa using hxT q hq⟩
  choose xBad hxBad using hexBad
  let z : Fin n → Bool := fun v => decide (v ∈ Y ∨ ∃ d : {w // w ∈ Bad}, xBad d v = true)
  have hzo_false : wireVal C z o = false := by
    by_contra hne
    have ht : wireVal C z o = true := by simpa using hne
    obtain ⟨q, hqT, hzq⟩ := hbo z ht
    simp only [z, decide_eq_true_eq] at hzq
    rcases hzq with hqY | ⟨d, hd⟩
    · exact Finset.disjoint_left.mp hYT hqY hqT
    · rw [(hxBad d).2 q hqT] at hd
      exact Bool.false_ne_true hd
  have hzo_true : wireVal C z o = true := by
    apply hcut (fun v => decide (v ∈ Y ∨ v = p)) z _ o (Finset.mem_singleton_self o) (hfire p hpT)
    intro w hw hwx
    by_cases hb : BelowSet C T w
    · refine False.elim (hpnot (Finset.mem_biUnion.mpr ⟨w, hw, ?_⟩))
      simp only [soundPts, ite_eq_left hb]
      exact (mem_firePts C Y w p).mpr hwx
    · let d : {w // w ∈ Bad} := ⟨w, Finset.mem_filter.mpr ⟨hw, hb⟩⟩
      apply wireVal_mono C hG (xBad d) z _ w (hxBad d).1
      intro v hv
      simp only [z, decide_eq_true_eq]
      exact Or.inr ⟨d, hv⟩
  rw [hzo_false] at hzo_true
  exact Bool.false_ne_true hzo_true

private lemma charged_non_disjoint {n : ℕ} (C : Circuit) (Yi Ti Tj : Finset (Fin n)) (w : ℕ)
    (hdi : Disjoint Yi Ti) (hbi : BelowSet C Ti w) (hbj : BelowSet C Tj w)
    (h2 : 2 ≤ (firePts C Yi w).card) (hint : (Ti ∩ Tj).card ≤ 1) : ¬ Disjoint Yi Tj := by
  intro hdj
  have hsub : firePts C Yi w ⊆ Ti ∩ Tj := by
    intro p hp
    have hv := (mem_firePts C Yi w p).mp hp
    obtain ⟨q, hqT, hqv⟩ := hbi _ hv
    obtain ⟨r, hrT, hrv⟩ := hbj _ hv
    simp only [decide_eq_true_eq] at hqv hrv
    rcases hqv with hqv | rfl
    · exact absurd hqT (Finset.disjoint_left.mp hdi hqv)
    rcases hrv with hrv | rfl
    · exact absurd hrT (Finset.disjoint_left.mp hdj hrv)
    exact Finset.mem_inter.mpr ⟨hqT, hrT⟩
  have hle := Finset.card_le_card hsub
  omega

end PEqualNP.Outside.L_meta_1562

open PEqualNP.Outside.L_meta_1562 in
theorem PEqualNP.Outside.L_meta_1562 : ¬ (∃ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧ (∀ i : Fin m, Disjoint (y i) (S i)) ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) ∧ (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) ∧ (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) ∧ D * C.gates.length + m < ∑ i : Fin m, (S i).card) := by
  classical
  rintro ⟨n, m, D, S, y, C, o, hinter, hdisj, hG, hbelow, hfire, hD, hstrict⟩
  have hper : ∀ i : Fin m, (S i).card ≤ (chargedGates C (y i) (S i)).card + 1 := fun i =>
    per_family_bound C hG (y i) (S i) (o i) (hdisj i)
      (fun x hx => hbelow i x hx) (fun p hp => hfire i p hp)
  have hdeg : ∀ w ∈ Finset.Ico n (n + C.gates.length),
      (Finset.univ.filter fun i : Fin m => w ∈ chargedGates C (y i) (S i)).card ≤ D := by
    intro w _
    apply hD
    intro i hi j hj hij
    have hi' := (mem_chargedGates C (y i) (S i) w).mp (Finset.mem_filter.mp hi).2
    have hj' := (mem_chargedGates C (y j) (S j) w).mp (Finset.mem_filter.mp hj).2
    exact charged_non_disjoint C (y i) (S i) (S j) w (hdisj i) hi'.2.1 hj'.2.1 hi'.2.2 (hinter i j hij)
  have hswap : ∑ i : Fin m, (chargedGates C (y i) (S i)).card =
      ∑ w ∈ Finset.Ico n (n + C.gates.length),
        (Finset.univ.filter fun i : Fin m => w ∈ chargedGates C (y i) (S i)).card := by
    calc ∑ i : Fin m, (chargedGates C (y i) (S i)).card
        = ∑ i : Fin m, ((Finset.Ico n (n + C.gates.length)).filter
            fun w => w ∈ chargedGates C (y i) (S i)).card := by
            refine Finset.sum_congr rfl fun i _ => congrArg Finset.card ?_
            ext w
            simp only [Finset.mem_filter, Finset.mem_Ico]
            exact ⟨fun hw => ⟨((mem_chargedGates C (y i) (S i) w).mp hw).1, hw⟩, fun hw => hw.2⟩
      _ = ∑ i : Fin m, ∑ w ∈ Finset.Ico n (n + C.gates.length),
            if w ∈ chargedGates C (y i) (S i) then 1 else 0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.card_filter]
      _ = ∑ w ∈ Finset.Ico n (n + C.gates.length), ∑ i : Fin m,
            if w ∈ chargedGates C (y i) (S i) then 1 else 0 := Finset.sum_comm
      _ = ∑ w ∈ Finset.Ico n (n + C.gates.length),
            (Finset.univ.filter fun i : Fin m => w ∈ chargedGates C (y i) (S i)).card := by
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [Finset.card_filter]
  have hbound : ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
    calc ∑ i : Fin m, (S i).card
        ≤ ∑ i : Fin m, ((chargedGates C (y i) (S i)).card + 1) :=
            Finset.sum_le_sum fun i _ => hper i
      _ = ∑ i : Fin m, (chargedGates C (y i) (S i)).card + m := by
            rw [Finset.sum_add_distrib]
            simp
      _ ≤ D * C.gates.length + m := by
            rw [hswap]
            have hsum := Finset.sum_le_sum hdeg
            rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.add_sub_cancel_left, Nat.mul_comm] at hsum
            exact Nat.add_le_add_right hsum m
  omega
