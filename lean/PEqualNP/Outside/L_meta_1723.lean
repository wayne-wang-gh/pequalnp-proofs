import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1723

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
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

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem eval_mono_fn {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (o : ℕ)
    (h : Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  refine mono gates _ _ (by simp) hg ?_ o h
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · exact hxy _
  · exact id

theorem cf_mono_fn {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (h : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    PEqualNP.MetaComplexity.circuitFun n C y = true :=
  eval_mono_fn C.gates (fun g hg' => (hg g hg').1) x y hxy C.output h

theorem band_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem in_pair {N : ℕ} (p l : Fin N) :
    (fun i : Fin (N + N) => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) =
      Fin.append (fun a => decide (a ∈ ({p} : Finset (Fin N))))
        (fun b => decide (b ∈ ({l} : Finset (Fin N)))) := by
  funext v
  refine Fin.addCases (fun i => ?_) (fun i => ?_) v
  · rw [Fin.append_left]
    have h1 : Fin.castAdd N i ≠ Fin.natAdd N l := by
      intro h
      have h2 := congrArg Fin.val h
      rw [Fin.val_castAdd, Fin.val_natAdd] at h2
      have h3 := i.isLt
      omega
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact Finset.mem_singleton.mpr (Fin.castAdd_inj.mp h)
      · exact absurd h h1
    · exact Or.inl (congrArg _ (Finset.mem_singleton.mp h))
  · rw [Fin.append_right]
    have h1 : Fin.natAdd N i ≠ Fin.castAdd N p := by
      intro h
      have h2 := congrArg Fin.val h
      rw [Fin.val_castAdd, Fin.val_natAdd] at h2
      have h3 := p.isLt
      omega
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact absurd h h1
      · have h2 := congrArg Fin.val h
        rw [Fin.val_natAdd, Fin.val_natAdd] at h2
        exact Finset.mem_singleton.mpr (Fin.ext (by omega))
    · exact Or.inr (congrArg _ (Finset.mem_singleton.mp h))

theorem comp_set {N : ℕ} (I : Fin N → Fin N → Prop) (Ca Cb : Circuit)
    (hcomp : ∀ p l : Fin N, I p l → (PEqualNP.MetaComplexity.circuitFun (N + N) Ca (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) && PEqualNP.MetaComplexity.circuitFun (N + N) Cb (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l))) = true)
    (p l : Fin N) (hpl : I p l) :
    PEqualNP.MetaComplexity.circuitFun (N + N) Ca (Fin.append (fun a => decide (a ∈ ({p} : Finset (Fin N)))) (fun b => decide (b ∈ ({l} : Finset (Fin N))))) = true ∧ PEqualNP.MetaComplexity.circuitFun (N + N) Cb (Fin.append (fun a => decide (a ∈ ({p} : Finset (Fin N)))) (fun b => decide (b ∈ ({l} : Finset (Fin N))))) = true := by
  have h := hcomp p l hpl
  rw [in_pair p l, Bool.and_eq_true] at h
  exact h

theorem sound_set {N : ℕ} (k : ℕ) (I : Fin N → Fin N → Prop) (Ca Cb : Circuit)
    (hsound : ∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ k → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (PEqualNP.MetaComplexity.circuitFun (N + N) Ca z && PEqualNP.MetaComplexity.circuitFun (N + N) Cb z) = false)
    (X Y : Finset (Fin N)) (hY : Y.card ≤ k) (hXY : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) :
    (PEqualNP.MetaComplexity.circuitFun (N + N) Ca (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ Y))) && PEqualNP.MetaComplexity.circuitFun (N + N) Cb (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ Y)))) = false := by
  refine hsound _ ?_ ?_
  · refine le_of_eq_of_le (congrArg Finset.card ?_) hY
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.append_right, decide_eq_true_eq]
  · rintro ⟨p, l, hpl, hp, hl⟩
    rw [Fin.append_left] at hp
    rw [Fin.append_right] at hl
    exact hXY p (of_decide_eq_true hp) l (of_decide_eq_true hl) hpl

theorem pt_eq {N : ℕ} (S : Finset (Fin N)) (p u : Fin N) (hp : p ∈ S) :
    (decide (u ∈ S) && decide (u = p)) = decide (u ∈ ({p} : Finset (Fin N))) := by
  by_cases hu : u = p
  · subst hu
    simp [hp]
  · simp [hu]

theorem pts_eq {N : ℕ} (S X : Finset (Fin N)) (u : Fin N) (hX : X ⊆ S) :
    (decide (u ∈ S) && decide (u ∈ X)) = decide (u ∈ X) := by
  by_cases hu : u ∈ X
  · simp [hu, hX hu]
  · simp [hu]

theorem lnA {N : ℕ} (W Y B Z : Finset (Fin N)) (hY : Y ⊆ W) (hB : ∀ t ∈ B, t ∉ W)
    (hZ : ∀ t, t ∈ Z ↔ t ∈ Y ∨ t ∈ B) (t : Fin N) :
    (if t ∈ W then decide (t ∈ Y) else decide (t ∈ B)) = decide (t ∈ Z) := by
  by_cases ht : t ∈ W
  · rw [if_pos ht]
    exact decide_eq_decide.mpr ⟨fun h => (hZ t).mpr (Or.inl h),
      fun h => ((hZ t).mp h).elim id (fun hb => absurd ht (hB t hb))⟩
  · rw [if_neg ht]
    exact decide_eq_decide.mpr ⟨fun h => (hZ t).mpr (Or.inr h),
      fun h => ((hZ t).mp h).elim (fun hy => absurd (hY hy) ht) id⟩

theorem lnB {N : ℕ} (W B Z : Finset (Fin N)) (l : Fin N) (hl : l ∈ W) (hB : ∀ t ∈ B, t ∉ W)
    (hZ : ∀ t, t ∈ Z ↔ t = l ∨ t ∈ B) (t : Fin N) :
    (if t ∈ W then decide (t = l) else decide (t ∈ B)) = decide (t ∈ Z) := by
  by_cases ht : t ∈ W
  · rw [if_pos ht]
    exact decide_eq_decide.mpr ⟨fun h => (hZ t).mpr (Or.inl h),
      fun h => ((hZ t).mp h).elim id (fun hb => absurd ht (hB t hb))⟩
  · rw [if_neg ht]
    exact decide_eq_decide.mpr ⟨fun h => (hZ t).mpr (Or.inr h),
      fun h => ((hZ t).mp h).elim (fun e => absurd (e ▸ hl) ht) id⟩

theorem meet_le_one {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (l t : Fin N) (h : l ≠ t) :
    (Finset.univ.filter (fun p => I p l ∧ I p t)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  obtain ⟨_, _, hu⟩ := huniq a b hab
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  exact h ((hu l ⟨ha'.1, hb'.1⟩).trans (hu t ⟨ha'.2, hb'.2⟩).symm)

theorem lines_through {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p0 : Fin N) : (Finset.univ.filter (fun l => I p0 l)).card = q + 1 := by
  have h1 : ∀ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
      ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card = 1 := by
    intro p hp
    have hne : p0 ≠ p := (Finset.ne_of_mem_erase hp).symm
    obtain ⟨l, hl, hu⟩ := huniq p0 p hne
    rw [Finset.card_eq_one]
    refine ⟨l, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      exact hu x hx
    · intro hx
      rw [hx]
      exact hl
  have h2 : ∀ l ∈ Finset.univ.filter (fun l => I p0 l),
      (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card = q := by
    intro l hl
    have hl' := (Finset.mem_filter.mp hl).2
    have e : ((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)
        = (Finset.univ.filter (fun p => I p l)).erase p0 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    have hmem : p0 ∈ Finset.univ.filter (fun p => I p l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩
    rw [e, Finset.card_erase_of_mem hmem, hline l]
    rfl
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
        ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card
      = ∑ l ∈ Finset.univ.filter (fun l => I p0 l),
        (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at h3
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ p0),
    Finset.card_univ, Fintype.card_fin] at h3
  have e : N - 1 = (q + 1) * q := by
    have : (q + 1) * q = q ^ 2 + q := by ring
    omega
  rw [e] at h3
  exact (Nat.eq_of_mul_eq_mul_right hq h3).symm

theorem inc_lower {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (S W : Finset (Fin N))
    (c r : ℕ) (h : ∀ l ∈ W, c ≤ (S.filter (fun p => I p l)).card + r) :
    W.card * c ≤ ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card + W.card * r := by
  have e : ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card
      = ∑ l ∈ W, (S.filter (fun p => I p l)).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.card_filter]
  rw [e]
  calc W.card * c = ∑ _l ∈ W, c := by simp
    _ ≤ ∑ l ∈ W, ((S.filter (fun p => I p l)).card + r) := Finset.sum_le_sum h
    _ = ∑ l ∈ W, (S.filter (fun p => I p l)).card + W.card * r := by
        rw [Finset.sum_add_distrib]
        simp

theorem countA {N : ℕ} (q m : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hlt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (p0 : Fin N) (T : Finset (Fin N)) (hT : T.card ≤ m) :
    N ≤ (Finset.univ.filter (fun l : Fin N => ¬ I p0 l ∧ l ∉ T)).card + (q + 1) + m := by
  have hsub : (Finset.univ : Finset (Fin N)) ⊆
      Finset.univ.filter (fun l : Fin N => ¬ I p0 l ∧ l ∉ T) ∪
        (Finset.univ.filter (fun l => I p0 l) ∪ T) := by
    intro l _
    by_cases h1 : I p0 l
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩))
    by_cases h2 : l ∈ T
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h2)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)
  have h1 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h2 := Finset.card_union_le (Finset.univ.filter (fun l => I p0 l)) T
  rw [Finset.card_univ, Fintype.card_fin] at h1
  rw [hlt p0] at h2
  omega

theorem countB {N : ℕ} (q m : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hlt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (l0 : Fin N) (Q : Finset (Fin N)) (hQ : Q.card ≤ m) :
    N ≤ (Finset.univ.filter (fun l : Fin N => l ≠ l0 ∧ ∀ p ∈ Q, ¬ I p l)).card + 1 + m * (q + 1) := by
  have hsub : (Finset.univ : Finset (Fin N)) ⊆
      Finset.univ.filter (fun l : Fin N => l ≠ l0 ∧ ∀ p ∈ Q, ¬ I p l) ∪
        (({l0} : Finset (Fin N)) ∪ Q.biUnion (fun p => Finset.univ.filter (fun l => I p l))) := by
    intro l _
    by_cases h1 : l = l0
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h1))
    by_cases h2 : ∀ p ∈ Q, ¬ I p l
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)
    · push_neg at h2
      obtain ⟨p, hp, hpl⟩ := h2
      exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩⟩))
  have h1 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h2 := Finset.card_union_le ({l0} : Finset (Fin N))
    (Q.biUnion (fun p => Finset.univ.filter (fun l => I p l)))
  have h3 : (Q.biUnion (fun p => Finset.univ.filter (fun l => I p l))).card ≤ Q.card * (q + 1) := by
    refine le_trans Finset.card_biUnion_le ?_
    rw [Finset.sum_congr rfl (fun p _ => hlt p)]
    simp
  have h4 : Q.card * (q + 1) ≤ m * (q + 1) := Nat.mul_le_mul_right _ hQ
  rw [Finset.card_univ, Fintype.card_fin] at h1
  rw [Finset.card_singleton] at h2
  omega

theorem lineA {N : ℕ} (q m : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p0 : Fin N) (T : Finset (Fin N)) (l : Fin N) (hT : T.card ≤ m)
    (hl1 : ¬ I p0 l) (hl2 : l ∉ T) :
    q + 1 ≤ ((Finset.univ.filter (fun u : Fin N => u ≠ p0 ∧ ∀ t ∈ T, ¬ I u t)).filter
      (fun p => I p l)).card + m := by
  have hsub : Finset.univ.filter (fun p => I p l) ⊆
      (Finset.univ.filter (fun u : Fin N => u ≠ p0 ∧ ∀ t ∈ T, ¬ I u t)).filter (fun p => I p l) ∪
        T.biUnion (fun t => Finset.univ.filter (fun p => I p l ∧ I p t)) := by
    intro p hp
    have hpl := (Finset.mem_filter.mp hp).2
    by_cases h : ∀ t ∈ T, ¬ I p t
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_, h⟩, hpl⟩)
      intro e
      rw [e] at hpl
      exact hl1 hpl
    · push_neg at h
      obtain ⟨t, ht, hpt⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨t, ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl, hpt⟩⟩)
  have h1 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [hline l] at h1
  have h3 : (T.biUnion (fun t => Finset.univ.filter (fun p => I p l ∧ I p t))).card ≤ T.card := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (fun t ht => meet_le_one I huniq l t ?_)) ?_
    · intro e
      rw [e] at hl2
      exact hl2 ht
    · simp
  omega

theorem lineB {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (l0 : Fin N) (Q : Finset (Fin N)) (l : Fin N)
    (hl1 : l ≠ l0) (hl2 : ∀ p ∈ Q, ¬ I p l) :
    q + 1 ≤ ((Finset.univ.filter (fun u : Fin N => ¬ I u l0 ∧ u ∉ Q)).filter
      (fun p => I p l)).card + 1 := by
  have hsub : Finset.univ.filter (fun p => I p l) ⊆
      (Finset.univ.filter (fun u : Fin N => ¬ I u l0 ∧ u ∉ Q)).filter (fun p => I p l) ∪
        Finset.univ.filter (fun p => I p l ∧ I p l0) := by
    intro p hp
    have hpl := (Finset.mem_filter.mp hp).2
    by_cases h : I p l0
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl, h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h, fun hq => hl2 p hq hpl⟩, hpl⟩)
  have h1 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [hline l] at h1
  have h3 := meet_le_one I huniq l l0 hl1
  omega

theorem arith0 (q m N sz inc : ℕ) (hq : 8 ≤ q) (hm : 1 ≤ m)
    (hinc : N * (q + 1) ≤ inc + N * 0)
    (h : m * inc ≤ 5 * q * sz + m * (N + N)) : N * m ≤ 10 * sz := by
  by_contra hc
  push_neg at hc
  zify at hq hm hinc h hc
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by linarith
  have k7 := mul_le_mul_of_nonneg_left hinc hm0
  have k9 : (q : ℤ) * (10 * (sz : ℤ) + 1) ≤ (q : ℤ) * ((N : ℤ) * (m : ℤ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have k10 : (0 : ℤ) ≤ ((q : ℤ) - 8) * ((m : ℤ) * (N : ℤ)) :=
    mul_nonneg (by linarith) (mul_nonneg hm0 (by positivity))
  nlinarith [k7, k9, k10, h]

theorem arithA (q m N w s sz inc : ℕ) (hq : 8 ≤ q) (hm : 1 ≤ m) (hmq : 4 * m ≤ q)
    (hN : N = q ^ 2 + q + 1) (hw : N ≤ w + (q + 1) + m) (hs : s ≤ N)
    (hinc : w * (q + 1) ≤ inc + w * m)
    (h : m * inc ≤ 5 * q * sz + m * (s + w)) : N * m ≤ 10 * sz := by
  by_contra hc
  push_neg at hc
  zify at hq hm hmq hN hw hs hinc h hc
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by linarith
  have hd : (0 : ℤ) ≤ (q : ℤ) - (m : ℤ) := by linarith
  have k5 : (0 : ℤ) ≤ ((q : ℤ) - 8) * (q : ℤ) := mul_nonneg (by linarith) (by linarith)
  have k4 : (0 : ℤ) ≤ ((q : ℤ) - 8) * (q : ℤ) ^ 2 := mul_nonneg (by linarith) (by positivity)
  have k1 : (0 : ℤ) ≤ ((w : ℤ) - ((q : ℤ) ^ 2 - (m : ℤ))) * ((q : ℤ) - (m : ℤ)) :=
    mul_nonneg (by linarith) hd
  have k2 : (0 : ℤ) ≤ ((q : ℤ) - 4 * (m : ℤ)) * ((q : ℤ) - (m : ℤ)) := mul_nonneg (by linarith) hd
  have k3 : (0 : ℤ) ≤ (4 * (q : ℤ) ^ 2 - (q : ℤ)) * ((q : ℤ) - 4 * (m : ℤ)) :=
    mul_nonneg (by nlinarith [k5]) (by linarith)
  have key : ((q : ℤ) + 2) * (N : ℤ) ≤ 2 * ((w : ℤ) * ((q : ℤ) - (m : ℤ))) := by
    rw [hN]
    nlinarith [k1, k2, k3, k4, k5]
  have k6 := mul_le_mul_of_nonneg_left key hm0
  have k7 := mul_le_mul_of_nonneg_left hinc hm0
  have k8 := mul_le_mul_of_nonneg_left hs hm0
  have k9 : (q : ℤ) * (10 * (sz : ℤ) + 1) ≤ (q : ℤ) * ((N : ℤ) * (m : ℤ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith [k6, k7, k8, k9, h]

theorem arithB (q m N w s sz inc : ℕ) (hq : 8 ≤ q) (hm : 1 ≤ m) (hmq : 4 * m ≤ q)
    (hN : N = q ^ 2 + q + 1) (hw : N ≤ w + 1 + m * (q + 1)) (hs : s ≤ N)
    (hinc : w * (q + 1) ≤ inc + w * 1)
    (h : m * inc ≤ 5 * q * sz + m * (s + w)) : N * m ≤ 10 * sz := by
  by_contra hc
  push_neg at hc
  zify at hq hm hmq hN hw hs hinc h hc
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by linarith
  have hd : (0 : ℤ) ≤ (q : ℤ) - 1 := by linarith
  have k5 : (0 : ℤ) ≤ ((q : ℤ) - 8) * (q : ℤ) := mul_nonneg (by linarith) (by linarith)
  have k4 : (0 : ℤ) ≤ ((q : ℤ) - 8) * (q : ℤ) ^ 2 := mul_nonneg (by linarith) (by positivity)
  have k1 : (0 : ℤ) ≤ ((w : ℤ) - ((q : ℤ) + 1) * ((q : ℤ) - (m : ℤ))) * ((q : ℤ) - 1) :=
    mul_nonneg (by nlinarith) hd
  have k2 : (0 : ℤ) ≤ ((q : ℤ) ^ 2 - 1) * ((q : ℤ) - 4 * (m : ℤ)) :=
    mul_nonneg (by nlinarith [k5]) (by linarith)
  have key : ((q : ℤ) + 2) * (N : ℤ) ≤ 2 * ((w : ℤ) * ((q : ℤ) - 1)) := by
    rw [hN]
    nlinarith [k1, k2, k4, k5]
  have k6 := mul_le_mul_of_nonneg_left key hm0
  have k7 := mul_le_mul_of_nonneg_left hinc hm0
  have k8 := mul_le_mul_of_nonneg_left hs hm0
  have k9 : (q : ℤ) * (10 * (sz : ℤ) + 1) ≤ (q : ℤ) * ((N : ℤ) * (m : ℤ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith [k6, k7, k8, k9, h]

end PEqualNP.Outside.L_meta_1723

open PEqualNP.Outside.L_meta_1723 in
theorem PEqualNP.Outside.L_meta_1723 : (∀ (N8 K8 : ℕ) (I8 : Fin N8 → Fin N8 → Prop) [DecidableRel I8] (Ca8 Cb8 : PEqualNP.CircuitLowerBounds.Circuit) (S8 W8 : Finset (Fin N8)), (∀ g8 ∈ Ca8.gates, (g8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Ca8 → (∀ g8a ∈ Cb8.gates, (g8a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8a.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Cb8 → (∀ X8 Y8 : Finset (Fin N8), X8 ⊆ S8 → Y8 ⊆ W8 → Y8.card ≤ K8 → (∀ p8 ∈ X8, ∀ l8 ∈ Y8, ¬ I8 p8 l8) → (PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8 => decide (a8 ∈ X8)) (fun b8 => decide (b8 ∈ Y8))) && PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8a => decide (a8a ∈ X8)) (fun b8a => decide (b8a ∈ Y8)))) = false) → (∀ pz8 ∈ S8, ∀ T8 ⊆ W8, (∀ l8a ∈ T8, ¬ I8 pz8 l8a) → T8.card ≤ K8 → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8b => decide (a8b ∈ ({pz8} : Finset (Fin N8)))) (fun b8b => decide (b8b ∈ T8))) = true → ∀ X8a Y8a : Finset (Fin N8), X8a ⊆ S8.filter (fun u8 => u8 ≠ pz8 ∧ ∀ l8b ∈ T8, ¬ I8 u8 l8b) → Y8a ⊆ W8.filter (fun l8c => ¬ I8 pz8 l8c ∧ l8c ∉ T8) → Y8a.card + T8.card ≤ K8 → (∀ p8a ∈ X8a, ∀ l8d ∈ Y8a, ¬ I8 p8a l8d) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8c => decide (a8c ∈ X8a)) (fun b8c => decide (b8c ∈ (Y8a ∪ T8)))) = false) ∧ (∀ wz8 ∈ W8, ∀ Q8 ⊆ S8, (∀ p8b ∈ Q8, ¬ I8 p8b wz8) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8d => decide (a8d ∈ Q8)) (fun b8d => decide (b8d ∈ ({wz8} : Finset (Fin N8))))) = true → ∀ X8b Y8b : Finset (Fin N8), X8b ⊆ S8.filter (fun u8a => ¬ I8 u8a wz8 ∧ u8a ∉ Q8) → Y8b ⊆ W8.filter (fun l8e => l8e ≠ wz8 ∧ ∀ p8c ∈ Q8, ¬ I8 p8c l8e) → Y8b.card + 1 ≤ K8 → (∀ p8e ∈ X8b, ∀ l8f ∈ Y8b, ¬ I8 p8e l8f) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8e => decide (a8e ∈ X8b)) (fun b8e => decide (b8e ∈ (insert wz8 Y8b)))) = false)) → (∀ (q90 N90 a90 b90 : ℕ) (I90 : Fin N90 → Fin N90 → Prop) [DecidableRel I90] (D90 : PEqualNP.CircuitLowerBounds.Circuit) (S90 W90 : Finset (Fin N90)) (nu90 : Fin N90 → Bool), 2 ≤ q90 → N90 = q90 ^ 2 + q90 + 1 → (∀ l90c : Fin N90, (Finset.univ.filter (fun p90c => I90 p90c l90c)).card = q90 + 1) → (∀ pa90 pb90 : Fin N90, pa90 ≠ pb90 → ∃! lb90 : Fin N90, I90 pa90 lb90 ∧ I90 pb90 lb90) → (∀ g90 ∈ D90.gates, (g90.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g90.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g90.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N90 + N90) D90 → (∀ j90 < D90.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i90 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).inputs, (D90.lineDegrees (N90 + N90) (Finset.Ico N90 (N90 + N90))).getD i90 0 = 0) ∨ (∀ h90 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).inputs, (D90.lineDegrees (N90 + N90) (Finset.range N90)).getD h90 0 = 0)) → 1 ≤ a90 → 1 ≤ b90 → (∀ p90 ∈ S90, ∀ l90 ∈ W90, I90 p90 l90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90 => decide (u90 ∈ S90) && decide (u90 = p90)) (fun t90 => if t90 ∈ W90 then decide (t90 = l90) else nu90 t90)) = true) → (∀ p90a ∈ S90, ∀ T90 ⊆ W90, (∀ l90a ∈ T90, ¬ I90 p90a l90a) → T90.card ≤ a90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90a => decide (u90a ∈ S90) && decide (u90a = p90a)) (fun t90a => if t90a ∈ W90 then decide (t90a ∈ T90) else nu90 t90a)) = false) → (∀ l90b ∈ W90, ∀ X90 ⊆ S90, (∀ p90b ∈ X90, ¬ I90 p90b l90b) → X90.card ≤ b90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90b => decide (u90b ∈ S90) && decide (u90b ∈ X90)) (fun t90b => if t90b ∈ W90 then decide (t90b = l90b) else nu90 t90b)) = false) → min (min a90 b90) q90 * ((S90 ×ˢ W90).filter (fun pl90 => I90 pl90.1 pl90.2)).card ≤ 5 * q90 * D90.size + min (min a90 b90) q90 * (S90.card + W90.card)) → ∀ (q9 N9 k9 : ℕ) (I9 : Fin N9 → Fin N9 → Prop) [DecidableRel I9] (Ca9 Cb9 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q9 → N9 = q9 ^ 2 + q9 + 1 → (∀ l9a : Fin N9, (Finset.univ.filter (fun p9a => I9 p9a l9a)).card = q9 + 1) → (∀ pa9 pb9 : Fin N9, pa9 ≠ pb9 → ∃! lb9 : Fin N9, I9 pa9 lb9 ∧ I9 pb9 lb9) → 8 ≤ q9 → 2 ≤ k9 → (∀ g9 ∈ Ca9.gates, (g9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g9.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g9.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N9 + N9) Ca9 → (∀ g9a ∈ Cb9.gates, (g9a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g9a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g9a.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N9 + N9) Cb9 → (∀ j9 < Ca9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt Ca9 j9).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i9b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Ca9 j9).inputs, (Ca9.lineDegrees (N9 + N9) (Finset.Ico N9 (N9 + N9))).getD i9b 0 = 0) ∨ (∀ h9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Ca9 j9).inputs, (Ca9.lineDegrees (N9 + N9) (Finset.range N9)).getD h9 0 = 0)) → (∀ j9a < Cb9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt Cb9 j9a).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i9c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Cb9 j9a).inputs, (Cb9.lineDegrees (N9 + N9) (Finset.Ico N9 (N9 + N9))).getD i9c 0 = 0) ∨ (∀ h9a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Cb9 j9a).inputs, (Cb9.lineDegrees (N9 + N9) (Finset.range N9)).getD h9a 0 = 0)) → (∀ p9 l9 : Fin N9, I9 p9 l9 → (PEqualNP.MetaComplexity.circuitFun (N9 + N9) Ca9 (fun i9 => decide (i9 = Fin.castAdd N9 p9 ∨ i9 = Fin.natAdd N9 l9)) && PEqualNP.MetaComplexity.circuitFun (N9 + N9) Cb9 (fun i9a => decide (i9a = Fin.castAdd N9 p9 ∨ i9a = Fin.natAdd N9 l9))) = true) → (∀ z9 : Fin (N9 + N9) → Bool, (Finset.univ.filter (fun l9b : Fin N9 => z9 (Fin.natAdd N9 l9b) = true)).card ≤ k9 → (¬ ∃ p9b l9c : Fin N9, I9 p9b l9c ∧ z9 (Fin.castAdd N9 p9b) = true ∧ z9 (Fin.natAdd N9 l9c) = true) → (PEqualNP.MetaComplexity.circuitFun (N9 + N9) Ca9 z9 && PEqualNP.MetaComplexity.circuitFun (N9 + N9) Cb9 z9) = false) → N9 * min (k9 / 2) (q9 / 4) ≤ 10 * max Ca9.size Cb9.size := by
  intro hSpill hKM q N k I instI Ca Cb hq2 hN hline huniq hq8 hk hga hra hgb hrb hka hkb hcomp hsound
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = min (k / 2) (q / 4) := ⟨_, rfl⟩
  rw [← hmdef]
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 * m ≤ k := by omega
  have hm4 : 4 * m ≤ q := by omega
  have hmin : min (min m m) q = m := by omega
  have hlt := lines_through q I (by omega) hN hline huniq
  have hcS := comp_set I Ca Cb hcomp
  have hsS := sound_set k I Ca Cb hsound
  have hcardS : ∀ S : Finset (Fin N), S.card ≤ N := fun S => by
    have h := Finset.card_le_univ S
    rwa [Fintype.card_fin] at h
  by_cases h1 : ∀ (p : Fin N) (T : Finset (Fin N)), (∀ l ∈ T, ¬ I p l) → T.card ≤ m → PEqualNP.MetaComplexity.circuitFun (N + N) Ca (Fin.append (fun a => decide (a ∈ ({p} : Finset (Fin N)))) (fun b => decide (b ∈ T))) = false
  · by_cases h2 : ∀ (l : Fin N) (X : Finset (Fin N)), (∀ p ∈ X, ¬ I p l) → X.card ≤ m → PEqualNP.MetaComplexity.circuitFun (N + N) Ca (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ ({l} : Finset (Fin N))))) = false
    · refine le_trans ?_ (Nat.mul_le_mul_left 10 (le_max_left Ca.size Cb.size))
      have hK := hKM q N m m I Ca Finset.univ Finset.univ (fun _ => false) hq2 hN hline huniq hga hra hka hm1 hm1
      rw [hmin] at hK
      have hinc := inc_lower I Finset.univ Finset.univ (q + 1) 0
        (fun l _ => le_of_eq_of_le (hline l).symm (Nat.le_add_right _ _))
      rw [Finset.card_univ, Fintype.card_fin] at hinc
      rw [Finset.card_univ, Fintype.card_fin] at hK
      refine arith0 q m N Ca.size _ hq8 hm1 hinc (hK ?_ ?_ ?_)
      · intro p _ l _ hpl
        refine Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) Ca) (congrArg₂ Fin.append (funext fun u => ?_) (funext fun t => ?_))) (hcS p l hpl).1
        · exact pt_eq Finset.univ p u (Finset.mem_univ p)
        · simp
      · intro p _ T _ hT hTm
        refine Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) Ca) (congrArg₂ Fin.append (funext fun u => ?_) (funext fun t => ?_))) (h1 p T hT hTm)
        · exact pt_eq Finset.univ p u (Finset.mem_univ p)
        · simp
      · intro l _ X _ hX hXm
        refine Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) Ca) (congrArg₂ Fin.append (funext fun u => ?_) (funext fun t => ?_))) (h2 l X hX hXm)
        · exact pts_eq Finset.univ X u (Finset.subset_univ X)
        · simp
    · obtain ⟨l0, Q, hQ, hQm, hacc⟩ : ∃ (l : Fin N) (X : Finset (Fin N)), (∀ p ∈ X, ¬ I p l) ∧ X.card ≤ m ∧ PEqualNP.MetaComplexity.circuitFun (N + N) Ca (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ ({l} : Finset (Fin N))))) = true := by
        by_contra hcon
        refine h2 (fun l X hX hXm => ?_)
        by_contra hf
        exact hcon ⟨l, X, hX, hXm, Bool.eq_true_of_ne_false hf⟩
      refine le_trans ?_ (Nat.mul_le_mul_left 10 (le_max_right Ca.size Cb.size))
      obtain ⟨_, hL⟩ := hSpill N k I Cb Ca Finset.univ Finset.univ hgb hrb hga hra
        (fun X Y _ _ hY hXY => (Bool.and_comm _ _).trans (hsS X Y hY hXY))
      have hL' := hL l0 (Finset.mem_univ _) Q (Finset.subset_univ _) hQ hacc
      have hB : ∀ t ∈ ({l0} : Finset (Fin N)), t ∉ (Finset.univ.filter (fun l : Fin N => l ≠ l0 ∧ ∀ p ∈ Q, ¬ I p l)) :=
        fun t ht hW => (Finset.mem_filter.mp hW).2.1 (Finset.mem_singleton.mp ht)
      have hK := hKM q N m m I Cb (Finset.univ.filter (fun u : Fin N => ¬ I u l0 ∧ u ∉ Q)) (Finset.univ.filter (fun l : Fin N => l ≠ l0 ∧ ∀ p ∈ Q, ¬ I p l)) (fun t => decide (t ∈ ({l0} : Finset (Fin N)))) hq2 hN hline huniq hgb hrb hkb hm1 hm1
      rw [hmin] at hK
      have hw := countB q m I hlt l0 Q hQm
      have hinc := inc_lower I (Finset.univ.filter (fun u : Fin N => ¬ I u l0 ∧ u ∉ Q)) (Finset.univ.filter (fun l : Fin N => l ≠ l0 ∧ ∀ p ∈ Q, ¬ I p l)) (q + 1) 1
        (fun l hl => lineB q I hline huniq l0 Q l (Finset.mem_filter.mp hl).2.1 (Finset.mem_filter.mp hl).2.2)
      refine arithB q m N _ _ Cb.size _ hq8 hm1 hm4 hN hw (hcardS _) hinc (hK ?_ ?_ ?_)
      · intro p hp l hl hpl
        refine cf_mono_fn Cb hgb _ _ ?_ (hcS p l hpl).2
        intro v
        refine Fin.addCases (fun i => ?_) (fun i => ?_) v
        · rw [Fin.append_left, Fin.append_left]
          intro h
          have hi : i = p := Finset.mem_singleton.mp (of_decide_eq_true h)
          subst hi
          exact band_intro (decide_eq_true hp) (decide_eq_true rfl)
        · rw [Fin.append_right, Fin.append_right]
          intro h
          have hi : i = l := Finset.mem_singleton.mp (of_decide_eq_true h)
          subst hi
          exact (if_pos hl).trans (decide_eq_true rfl)
      · intro p hp T' hT' hT'I hT'm
        have key := hL' {p} T' (Finset.singleton_subset_iff.mpr hp) hT' (by omega)
          (fun p' hp' l hl => by rw [Finset.mem_singleton.mp hp']; exact hT'I l hl)
        refine Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) Cb) (congrArg₂ Fin.append (funext fun u => ?_) (funext fun t => ?_))) key
        · exact pt_eq _ p u hp
        · exact lnA _ T' {l0} (insert l0 T') hT' hB
            (fun t => by rw [Finset.mem_insert, Finset.mem_singleton]; exact or_comm) t
      · intro l hl X hX hXI hXm
        have key := hL' X {l} hX (Finset.singleton_subset_iff.mpr hl)
          (by rw [Finset.card_singleton]; omega)
          (fun p' hp' l' hl' => by rw [Finset.mem_singleton.mp hl']; exact hXI p' hp')
        refine Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) Cb) (congrArg₂ Fin.append (funext fun u => ?_) (funext fun t => ?_))) key
        · exact pts_eq _ X u hX
        · exact lnB _ {l0} (insert l0 {l}) l hl hB
            (fun t => by rw [Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]; exact or_comm) t
  · obtain ⟨p0, T, hT, hTm, hacc⟩ : ∃ (p : Fin N) (T : Finset (Fin N)), (∀ l ∈ T, ¬ I p l) ∧ T.card ≤ m ∧ PEqualNP.MetaComplexity.circuitFun (N + N) Ca (Fin.append (fun a => decide (a ∈ ({p} : Finset (Fin N)))) (fun b => decide (b ∈ T))) = true := by
      by_contra hcon
      refine h1 (fun p T hT hTm => ?_)
      by_contra hf
      exact hcon ⟨p, T, hT, hTm, Bool.eq_true_of_ne_false hf⟩
    refine le_trans ?_ (Nat.mul_le_mul_left 10 (le_max_right Ca.size Cb.size))
    obtain ⟨hP, _⟩ := hSpill N k I Cb Ca Finset.univ Finset.univ hgb hrb hga hra
      (fun X Y _ _ hY hXY => (Bool.and_comm _ _).trans (hsS X Y hY hXY))
    have hP' := hP p0 (Finset.mem_univ _) T (Finset.subset_univ _) hT (by omega) hacc
    have hB : ∀ t ∈ T, t ∉ (Finset.univ.filter (fun l : Fin N => ¬ I p0 l ∧ l ∉ T)) :=
      fun t ht hW => (Finset.mem_filter.mp hW).2.2 ht
    have hK := hKM q N m m I Cb (Finset.univ.filter (fun u : Fin N => u ≠ p0 ∧ ∀ l ∈ T, ¬ I u l)) (Finset.univ.filter (fun l : Fin N => ¬ I p0 l ∧ l ∉ T)) (fun t => decide (t ∈ T)) hq2 hN hline huniq hgb hrb hkb hm1 hm1
    rw [hmin] at hK
    have hw := countA q m I hlt p0 T hTm
    have hinc := inc_lower I (Finset.univ.filter (fun u : Fin N => u ≠ p0 ∧ ∀ l ∈ T, ¬ I u l)) (Finset.univ.filter (fun l : Fin N => ¬ I p0 l ∧ l ∉ T)) (q + 1) m
      (fun l hl => lineA q m I hline huniq p0 T l hTm (Finset.mem_filter.mp hl).2.1 (Finset.mem_filter.mp hl).2.2)
    refine arithA q m N _ _ Cb.size _ hq8 hm1 hm4 hN hw (hcardS _) hinc (hK ?_ ?_ ?_)
    · intro p hp l hl hpl
      refine cf_mono_fn Cb hgb _ _ ?_ (hcS p l hpl).2
      intro v
      refine Fin.addCases (fun i => ?_) (fun i => ?_) v
      · rw [Fin.append_left, Fin.append_left]
        intro h
        have hi : i = p := Finset.mem_singleton.mp (of_decide_eq_true h)
        subst hi
        exact band_intro (decide_eq_true hp) (decide_eq_true rfl)
      · rw [Fin.append_right, Fin.append_right]
        intro h
        have hi : i = l := Finset.mem_singleton.mp (of_decide_eq_true h)
        subst hi
        exact (if_pos hl).trans (decide_eq_true rfl)
    · intro p hp T' hT' hT'I hT'm
      have key := hP' {p} T' (Finset.singleton_subset_iff.mpr hp) hT' (by omega)
        (fun p' hp' l hl => by rw [Finset.mem_singleton.mp hp']; exact hT'I l hl)
      refine Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) Cb) (congrArg₂ Fin.append (funext fun u => ?_) (funext fun t => ?_))) key
      · exact pt_eq _ p u hp
      · exact lnA _ T' T (T' ∪ T) hT' hB (fun _ => Finset.mem_union) t
    · intro l hl X hX hXI hXm
      have key := hP' X {l} hX (Finset.singleton_subset_iff.mpr hl)
        (by rw [Finset.card_singleton]; omega)
        (fun p' hp' l' hl' => by rw [Finset.mem_singleton.mp hl']; exact hXI p' hp')
      refine Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) Cb) (congrArg₂ Fin.append (funext fun u => ?_) (funext fun t => ?_))) key
      · exact pts_eq _ X u hX
      · exact lnB _ T ({l} ∪ T) l hl hB
          (fun t => by rw [Finset.mem_union, Finset.mem_singleton]) t
