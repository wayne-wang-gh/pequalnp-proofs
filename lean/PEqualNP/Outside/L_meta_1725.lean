import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1725

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstp (d : List ℕ) (g : Gate) : List ℕ := d ++ [g.lineDegree d]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem ld_eq (C : Circuit) (n : ℕ) (M : Finset ℕ) :
    C.lineDegrees n M =
      C.gates.foldl dstp ((List.range n).map fun i => if i ∈ M then 1 else 0) := rfl

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem sum_mono (l : List ℕ) (f f' : ℕ → ℕ) (H : ∀ i, f i ≤ f' i) :
    (l.map f).sum ≤ (l.map f').sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (H a) ih

theorem max_mono (l : List ℕ) (f f' : ℕ → ℕ) (H : ∀ i, f i ≤ f' i) :
    (l.map f).foldr max 0 ≤ (l.map f').foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (H a) ih

theorem ldeg_mono (g : Gate) (d d' : List ℕ) (H : ∀ i, d.getD i 0 ≤ d'.getD i 0) :
    g.lineDegree d ≤ g.lineDegree d' := by
  unfold Gate.lineDegree
  split_ifs
  · exact sum_mono _ _ _ H
  · exact max_mono _ _ _ H

theorem mem_le_sum (l : List ℕ) (f : ℕ → ℕ) (c : ℕ) (hc : c ∈ l) : f c ≤ (l.map f).sum := by
  induction l with
  | nil => cases hc
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hc with rfl | h
    · exact Nat.le_add_right _ _
    · exact le_trans (ih h) (Nat.le_add_left _ _)

theorem ldeg_rep (g : Gate) (hg : g.op = GateOp.and) (c : ℕ) (hc : c ∈ g.inputs) (d : List ℕ) :
    Gate.lineDegree ⟨GateOp.or, [c, c]⟩ d ≤ g.lineDegree d := by
  have h1 : Gate.lineDegree ⟨GateOp.or, [c, c]⟩ d = d.getD c 0 := by
    simp [Gate.lineDegree]
  have h2 : g.lineDegree d = (g.inputs.map fun i => d.getD i 0).sum := by
    unfold Gate.lineDegree
    rw [if_pos hg]
  rw [h1, h2]
  exact mem_le_sum g.inputs (fun i => d.getD i 0) c hc

theorem dmono : ∀ (gs : List Gate) (d1 d2 : List ℕ), d1.length = d2.length →
    (∀ i, d1.getD i 0 ≤ d2.getD i 0) →
    ∀ i, (gs.foldl dstp d1).getD i 0 ≤ (gs.foldl dstp d2).getD i 0 := by
  intro gs
  induction gs with
  | nil => intro d1 d2 _ H; simpa using H
  | cons g gs ih =>
    intro d1 d2 hl H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (dstp d1 g) (dstp d2 g) (by simp [dstp, hl])
    intro i
    simp only [dstp, getD_snoc, hl]
    split_ifs
    · exact ldeg_mono g d1 d2 H
    · exact H i

theorem deg_repl (pre post : List Gate) (g g' : Gate) (d0 : List ℕ)
    (hle : ∀ d, g'.lineDegree d ≤ g.lineDegree d) (i : ℕ) :
    ((pre ++ g' :: post).foldl dstp d0).getD i 0 ≤
      ((pre ++ g :: post).foldl dstp d0).getD i 0 := by
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  apply dmono post _ _ (by simp [dstp])
  intro k
  simp only [dstp, getD_snoc]
  split_ifs
  · exact hle _
  · exact le_rfl

theorem val_repl_le (pre post : List Gate) (g g' : Gate) (x : List Bool)
    (hop : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hle : ∀ w : List Bool, g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g'.op.eval (g'.inputs.map fun i => w.getD i false) = true) (i : ℕ) :
    ((pre ++ g :: post).foldl stp x).getD i false = true →
      ((pre ++ g' :: post).foldl stp x).getD i false = true := by
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  apply mono post _ _ (by simp [stp]) hop
  intro k
  simp only [stp, getD_snoc]
  split_ifs
  · exact hle _
  · exact id

theorem val_repl_eq (pre post : List Gate) (g g' : Gate) (x : List Bool)
    (heq : g.op.eval (g.inputs.map fun i => (pre.foldl stp x).getD i false) =
      g'.op.eval (g'.inputs.map fun i => (pre.foldl stp x).getD i false)) :
    (pre ++ g :: post).foldl stp x = (pre ++ g' :: post).foldl stp x := by
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  have e : stp (pre.foldl stp x) g = stp (pre.foldl stp x) g' := by
    show pre.foldl stp x ++ [g.op.eval (g.inputs.map fun i => (pre.foldl stp x).getD i false)] =
      pre.foldl stp x ++ [g'.op.eval (g'.inputs.map fun i => (pre.foldl stp x).getD i false)]
    rw [heq]
  rw [e]

def rep (D : Circuit) (j c : ℕ) : Circuit :=
  ⟨D.gates.set j ⟨GateOp.or, [c, c]⟩, D.output⟩

theorem gates_split (D : Circuit) (j : ℕ) (hj : j < D.gates.length) :
    D.gates = D.gates.take j ++ gateAt D j :: D.gates.drop (j + 1) := by
  have h : gateAt D j = D.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [h, ← List.drop_eq_getElem_cons hj, List.take_append_drop]

theorem rep_split (D : Circuit) (j c : ℕ) (hj : j < D.gates.length) :
    (rep D j c).gates = D.gates.take j ++ ⟨GateOp.or, [c, c]⟩ :: D.gates.drop (j + 1) := by
  simp [rep, List.set_eq_take_append_cons_drop, hj]

theorem rep_gateAt_self (D : Circuit) (j c : ℕ) (hj : j < D.gates.length) :
    gateAt (rep D j c) j = ⟨GateOp.or, [c, c]⟩ := by
  simp [gateAt, rep, List.getD_eq_getElem?_getD, hj]

theorem rep_gateAt_ne (D : Circuit) (j c j' : ℕ) (hne : j' ≠ j) :
    gateAt (rep D j c) j' = gateAt D j' := by
  simp [gateAt, rep, List.getD_eq_getElem?_getD, Ne.symm hne]

theorem rep_deg (D : Circuit) (j c : ℕ) (hj : j < D.gates.length)
    (hop : (gateAt D j).op = GateOp.and) (hc : c ∈ (gateAt D j).inputs) (n : ℕ)
    (M : Finset ℕ) (i : ℕ) :
    ((rep D j c).lineDegrees n M).getD i 0 ≤ (D.lineDegrees n M).getD i 0 := by
  have h1 := deg_repl (D.gates.take j) (D.gates.drop (j + 1)) (gateAt D j) ⟨GateOp.or, [c, c]⟩
    ((List.range n).map fun i => if i ∈ M then 1 else 0) (ldeg_rep _ hop c hc) i
  rw [← gates_split D j hj, ← rep_split D j c hj] at h1
  rw [ld_eq, ld_eq]
  exact h1

theorem rep_up (D : Circuit) (hD : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (j c : ℕ) (hj : j < D.gates.length) (hop : (gateAt D j).op = GateOp.and)
    (hc : c ∈ (gateAt D j).inputs) (x : List Bool) (h : D.eval x = true) :
    (rep D j c).eval x = true := by
  have h1 := val_repl_le (D.gates.take j) (D.gates.drop (j + 1)) (gateAt D j)
    ⟨GateOp.or, [c, c]⟩ x (fun g hg => hD g (List.mem_of_mem_drop hg))
    (fun w hw => by
      rw [ev_and _ _ hop] at hw
      simpa [GateOp.eval] using hw c hc) D.output
  rw [← gates_split D j hj, ← rep_split D j c hj] at h1
  exact h1 h

theorem rep_eq (D : Circuit) (j c : ℕ) (hj : j < D.gates.length) (x : List Bool)
    (heq : (gateAt D j).op.eval ((gateAt D j).inputs.map fun i =>
      ((D.gates.take j).foldl stp x).getD i false) =
        ((D.gates.take j).foldl stp x).getD c false) :
    (rep D j c).eval x = D.eval x := by
  have h1 := val_repl_eq (D.gates.take j) (D.gates.drop (j + 1)) (gateAt D j)
    ⟨GateOp.or, [c, c]⟩ x (by rw [heq]; simp [GateOp.eval])
  rw [← gates_split D j hj, ← rep_split D j c hj] at h1
  show ((rep D j c).gates.foldl stp x).getD D.output false =
    (D.gates.foldl stp x).getD D.output false
  rw [h1]

def Bad (n : ℕ) (M1 M2 : Finset ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    ¬ ((∃ i ∈ (gateAt C j).inputs, (C.lineDegrees n M1).getD i 0 = 0) ∨
      (∀ h ∈ (gateAt C j).inputs, (C.lineDegrees n M2).getD h 0 = 0))

def Fan2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem rep_props (n : ℕ) (M1 M2 : Finset ℕ) (D : Circuit) (hD : Fan2 D)
    (hR : ReadsBack n D) (j c : ℕ) (hj : Bad n M1 M2 D j) (hc : c ∈ (gateAt D j).inputs) :
    Fan2 (rep D j c) ∧ ReadsBack n (rep D j c) ∧ (rep D j c).size = D.size ∧
      (∀ j', Bad n M1 M2 (rep D j c) j' → Bad n M1 M2 D j') ∧
      ¬ Bad n M1 M2 (rep D j c) j := by
  have hlen : (rep D j c).gates.length = D.gates.length := by simp [rep]
  refine ⟨?_, ?_, hlen, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ D.gates.set j ⟨GateOp.or, [c, c]⟩ := hg
    rcases List.mem_or_eq_of_mem_set hg' with h | h
    · exact hD g h
    · subst h
      exact ⟨Or.inr rfl, rfl⟩
  · intro j' hj' i hi
    by_cases e : j' = j
    · rw [e] at hi ⊢
      rw [rep_gateAt_self D j c hj.1] at hi
      have hic : i = c := by simpa using hi
      rw [hic]
      exact hR j hj.1 c hc
    · rw [rep_gateAt_ne D j c j' e] at hi
      exact hR j' (by omega) i hi
  · rintro j' ⟨h1, h2, h3⟩
    have e : j' ≠ j := by
      intro e
      rw [e, rep_gateAt_self D j c hj.1] at h2
      cases h2
    rw [rep_gateAt_ne D j c j' e] at h2 h3
    refine ⟨by omega, h2, fun hk => h3 ?_⟩
    rcases hk with ⟨i, hi, h0⟩ | hk
    · refine Or.inl ⟨i, hi, ?_⟩
      have := rep_deg D j c hj.1 hj.2.1 hc n M1 i
      omega
    · refine Or.inr fun h hh => ?_
      have := rep_deg D j c hj.1 hj.2.1 hc n M2 h
      have := hk h hh
      omega
  · rintro ⟨_, h2, _⟩
    rw [rep_gateAt_self D j c hj.1] at h2
    cases h2

theorem step (n : ℕ) (M1 M2 : Finset ℕ) (D : Circuit) (hD : Fan2 D) (hR : ReadsBack n D)
    (j : ℕ) (hj : Bad n M1 M2 D j) :
    ∃ D1 D2 : Circuit,
      (Fan2 D1 ∧ ReadsBack n D1 ∧ D1.size = D.size ∧
        (∀ j', Bad n M1 M2 D1 j' → Bad n M1 M2 D j') ∧ ¬ Bad n M1 M2 D1 j) ∧
      (Fan2 D2 ∧ ReadsBack n D2 ∧ D2.size = D.size ∧
        (∀ j', Bad n M1 M2 D2 j' → Bad n M1 M2 D j') ∧ ¬ Bad n M1 M2 D2 j) ∧
      ∀ x : List Bool, (D.eval x = true ↔ D1.eval x = true ∧ D2.eval x = true) := by
  have hmem : gateAt D j ∈ D.gates := by
    rw [gates_split D j hj.1]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨hgop, hglen⟩ := hD _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hglen
  have ha : a ∈ (gateAt D j).inputs := by rw [hab]; simp
  have hb : b ∈ (gateAt D j).inputs := by rw [hab]; simp
  have hmono : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hD g hg).1
  refine ⟨rep D j a, rep D j b, rep_props n M1 M2 D hD hR j a hj ha,
    rep_props n M1 M2 D hD hR j b hj hb, fun x =>
      ⟨fun h => ⟨rep_up D hmono j a hj.1 hj.2.1 ha x h, rep_up D hmono j b hj.1 hj.2.1 hb x h⟩,
        ?_⟩⟩
  rintro ⟨h1, h2⟩
  have hv : (gateAt D j).op.eval ((gateAt D j).inputs.map fun i =>
      ((D.gates.take j).foldl stp x).getD i false) =
      (((D.gates.take j).foldl stp x).getD a false &&
        ((D.gates.take j).foldl stp x).getD b false) := by
    rw [hj.2.1, hab]
    simp [GateOp.eval]
  cases hva : ((D.gates.take j).foldl stp x).getD a false
  · rw [← rep_eq D j a hj.1 x (by simp only [hv, hva, Bool.false_and])]
    exact h1
  · rw [← rep_eq D j b hj.1 x (by simp only [hv, hva, Bool.true_and])]
    exact h2

theorem bad_fin (n : ℕ) (M1 M2 : Finset ℕ) (D : Circuit) : {j | Bad n M1 M2 D j}.Finite :=
  (Set.finite_lt_nat D.gates.length).subset fun _ h => h.1

theorem split (n : ℕ) (M1 M2 : Finset ℕ) : ∀ (km : ℕ) (D : Circuit), Fan2 D → ReadsBack n D →
    Set.ncard {j | Bad n M1 M2 D j} ≤ km →
    ∃ L : List Circuit, L.length = 2 ^ km ∧
      (∀ E ∈ L, Fan2 E ∧ ReadsBack n E ∧ (∀ j, ¬ Bad n M1 M2 E j) ∧ E.size = D.size) ∧
      ∀ x : List Bool, (D.eval x = true ↔ ∀ E ∈ L, E.eval x = true) := by
  have good : ∀ (km : ℕ) (D : Circuit), Fan2 D → ReadsBack n D → (∀ j, ¬ Bad n M1 M2 D j) →
      ∃ L : List Circuit, L.length = 2 ^ km ∧
        (∀ E ∈ L, Fan2 E ∧ ReadsBack n E ∧ (∀ j, ¬ Bad n M1 M2 E j) ∧ E.size = D.size) ∧
        ∀ x : List Bool, (D.eval x = true ↔ ∀ E ∈ L, E.eval x = true) := by
    intro km D hD hR hem
    refine ⟨List.replicate (2 ^ km) D, by simp, fun E hE => ?_,
      fun x => ⟨fun h E hE => ?_, fun h => h D ?_⟩⟩
    · rw [List.eq_of_mem_replicate hE]
      exact ⟨hD, hR, hem, rfl⟩
    · rw [List.eq_of_mem_replicate hE]
      exact h
    · exact List.mem_replicate.2 ⟨by positivity, rfl⟩
  intro km
  induction km with
  | zero =>
    intro D hD hR hc
    refine good 0 D hD hR fun j hj => ?_
    have := (Set.ncard_pos (bad_fin n M1 M2 D)).2 ⟨j, hj⟩
    omega
  | succ km ih =>
    intro D hD hR hc
    by_cases hem : ∀ j, ¬ Bad n M1 M2 D j
    · exact good (km + 1) D hD hR hem
    · push_neg at hem
      obtain ⟨j, hj⟩ := hem
      obtain ⟨D1, D2, ⟨f1, r1, s1, b1, nb1⟩, ⟨f2, r2, s2, b2, nb2⟩, hev⟩ :=
        step n M1 M2 D hD hR j hj
      have c1 : Set.ncard {j | Bad n M1 M2 D1 j} ≤ km := by
        have := Set.ncard_lt_ncard (s := {j | Bad n M1 M2 D1 j}) (t := {j | Bad n M1 M2 D j})
          ⟨fun j' h => b1 j' h, fun h => nb1 (h hj)⟩ (bad_fin n M1 M2 D)
        omega
      have c2 : Set.ncard {j | Bad n M1 M2 D2 j} ≤ km := by
        have := Set.ncard_lt_ncard (s := {j | Bad n M1 M2 D2 j}) (t := {j | Bad n M1 M2 D j})
          ⟨fun j' h => b2 j' h, fun h => nb2 (h hj)⟩ (bad_fin n M1 M2 D)
        omega
      obtain ⟨L1, l1, p1, e1⟩ := ih D1 f1 r1 c1
      obtain ⟨L2, l2, p2, e2⟩ := ih D2 f2 r2 c2
      refine ⟨L1 ++ L2, by rw [List.length_append, l1, l2, pow_succ]; omega,
        fun E hE => ?_, fun x => ?_⟩
      · rcases List.mem_append.1 hE with h | h
        · obtain ⟨a, b, c, d⟩ := p1 E h
          exact ⟨a, b, c, d.trans s1⟩
        · obtain ⟨a, b, c, d⟩ := p2 E h
          exact ⟨a, b, c, d.trans s2⟩
      · rw [hev x, e1 x, e2 x]
        constructor
        · rintro ⟨h1, h2⟩ E hE
          rcases List.mem_append.1 hE with h | h
          · exact h1 E h
          · exact h2 E h
        · intro h
          exact ⟨fun E hE => h E (List.mem_append_left _ hE),
            fun E hE => h E (List.mem_append_right _ hE)⟩

end PEqualNP.Outside.L_meta_1725

theorem PEqualNP.Outside.L_meta_1725 : (∀ (q111 N111 k111 v111 t111 : ℕ) (I111 : Fin N111 → Fin N111 → Prop) [DecidableRel I111] (Cs111 : Fin v111 → PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q111 → N111 = q111 ^ 2 + q111 + 1 → (∀ l111a : Fin N111, (Finset.univ.filter (fun p111a => I111 p111a l111a)).card = q111 + 1) → (∀ pa111 pb111 : Fin N111, pa111 ≠ pb111 → ∃! lb111 : Fin N111, I111 pa111 lb111 ∧ I111 pb111 lb111) → 8 ≤ q111 → 1 ≤ v111 → v111 ≤ k111 → 8 * v111 ≤ q111 → (∀ i111 : Fin v111, ((∀ g111 ∈ (Cs111 i111).gates, (g111.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g111.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g111.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N111 + N111) (Cs111 i111)) ∧ (∀ j111 < (Cs111 i111).gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i111c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).inputs, ((Cs111 i111).lineDegrees (N111 + N111) (Finset.Ico N111 (N111 + N111))).getD i111c 0 = 0) ∨ (∀ h111 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).inputs, ((Cs111 i111).lineDegrees (N111 + N111) (Finset.range N111)).getD h111 0 = 0)) ∧ (Cs111 i111).size ≤ t111) → (∀ p111 l111 : Fin N111, I111 p111 l111 → ∀ i111a : Fin v111, PEqualNP.MetaComplexity.circuitFun (N111 + N111) (Cs111 i111a) (fun i111d => decide (i111d = Fin.castAdd N111 p111 ∨ i111d = Fin.natAdd N111 l111)) = true) → (∀ z111 : Fin (N111 + N111) → Bool, (Finset.univ.filter (fun l111b : Fin N111 => z111 (Fin.natAdd N111 l111b) = true)).card ≤ k111 → (¬ ∃ p111b l111c : Fin N111, I111 p111b l111c ∧ z111 (Fin.castAdd N111 p111b) = true ∧ z111 (Fin.natAdd N111 l111c) = true) → ∃ i111b : Fin v111, PEqualNP.MetaComplexity.circuitFun (N111 + N111) (Cs111 i111b) z111 = false) → N111 * (min k111 (q111 / 4) / v111) ≤ 20 * t111) → (∀ (N112 km112 : ℕ) (C112 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C112 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) C112 → Set.ncard {j112 : ℕ | j112 < C112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112 0 = 0) ∨ (∀ h112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112 0 = 0))} ≤ km112 → (∃ z112 z112a : Fin (N112 + N112) → Bool, PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112 ≠ PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112a) → ∃ D112 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g112 ∈ D112.gates, (g112.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g112.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g112.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) D112) ∧ Set.ncard {j112a : ℕ | j112a < D112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112a 0 = 0) ∨ (∀ h112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112a 0 = 0))} ≤ km112 ∧ D112.size ≤ C112.size ∧ PEqualNP.MetaComplexity.circuitFun (N112 + N112) D112 = PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112) → ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (km : ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → Set.ncard {j11 : ℕ | j11 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j11).inputs, (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i11 0 = 0) ∨ (∀ h11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j11).inputs, (C.lineDegrees (N + N) (Finset.range N)).getD h11 0 = 0))} ≤ km → 8 * 2 ^ km ≤ q → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * (min q (q / 4) / 2 ^ km) ≤ 20 * C.size := by
  intro HMV HNF q N I _ C km hq hN hlines hpts hmono hRB hcnt h8 hacc hrej
  have hNpos : 0 < N := by
    rw [hN]
    exact Nat.succ_pos _
  obtain ⟨p, hp⟩ : ∃ p : Fin N, I p ⟨0, hNpos⟩ := by
    have h := hlines ⟨0, hNpos⟩
    have hpos : 0 < (Finset.univ.filter (fun p => I p ⟨0, hNpos⟩)).card := by omega
    obtain ⟨p, hp⟩ := Finset.card_pos.1 hpos
    exact ⟨p, (Finset.mem_filter.1 hp).2⟩
  have hnc : ∃ z z' : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z ≠
        PEqualNP.MetaComplexity.circuitFun (N + N) C z' := by
    refine ⟨fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N ⟨0, hNpos⟩),
      fun _ => false, ?_⟩
    rw [hacc p ⟨0, hNpos⟩ hp, hrej (fun _ => false) (by simp) (by simp)]
    decide
  obtain ⟨D, ⟨hDf, hDR⟩, hDc, hDs, hDfun⟩ := HNF N km C hmono hRB hcnt hnc
  obtain ⟨L, hLlen, hLp, hLev⟩ := PEqualNP.Outside.L_meta_1725.split (N + N)
    (Finset.Ico N (N + N)) (Finset.range N) km D hDf hDR hDc
  have hLev' : ∀ z : Fin (N + N) → Bool,
      (PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
        ∀ E ∈ L, PEqualNP.MetaComplexity.circuitFun (N + N) E z = true) :=
    fun z => hLev (List.ofFn z)
  have h1 := Nat.one_le_two_pow (n := km)
  refine HMV q N q (2 ^ km) C.size I (fun i => L.get (i.cast hLlen.symm)) hq hN hlines hpts
    (by omega) h1 (by omega) h8 ?_ ?_ ?_
  · intro i
    obtain ⟨a, b, c, d⟩ := hLp _ (List.get_mem L (i.cast hLlen.symm))
    refine ⟨⟨a, b⟩, fun j hj hop => ?_, le_of_eq_of_le d hDs⟩
    by_contra hk
    exact c j ⟨hj, hop, hk⟩
  · intro p' l' hpl i
    have h := hacc p' l' hpl
    rw [← hDfun] at h
    exact (hLev' _).1 h _ (List.get_mem L (i.cast hLlen.symm))
  · intro z hz hni
    by_contra hcon
    push_neg at hcon
    have hD : PEqualNP.MetaComplexity.circuitFun (N + N) D z = true := by
      refine (hLev' z).2 fun E hE => ?_
      obtain ⟨m, rfl⟩ := List.mem_iff_get.1 hE
      have := hcon (m.cast hLlen)
      simpa using this
    have h := hrej z hz hni
    rw [← hDfun] at h
    exact Bool.false_ne_true (h.symm.trans hD)
