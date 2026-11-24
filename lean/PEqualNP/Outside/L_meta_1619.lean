import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1619

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

lemma val_out (gs : List Gate) (n : ℕ) (t : ℕ) (h : n + gs.length ≤ t) (x : Fin n → Bool) :
    val gs n x t = false := by
  unfold val
  apply List.getD_eq_default
  rw [fold_length, List.length_ofFn]
  exact h

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

lemma gate_cases (gs : List Gate) (n : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (t : ℕ) (h1 : n ≤ t) (h2 : t < n + gs.length) :
    ∃ J : Finset ℕ, J.card ≤ 2 ∧ (∀ i ∈ J, i < t) ∧
      ((∀ x : Fin n → Bool, val gs n x t = true ↔ ∃ i ∈ J, val gs n x i = true) ∨
       (∀ x : Fin n → Bool, val gs n x t = true ↔ ∀ i ∈ J, val gs n x i = true)) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
  have hj : j < gs.length := by omega
  have hlen := (hg _ (List.getElem_mem hj)).2
  rcases (hg _ (List.getElem_mem hj)).1 with hop | hop
  · by_cases hall : ∀ i ∈ (gs[j]).inputs, i < n + j
    · refine ⟨(gs[j]).inputs.toFinset, (List.toFinset_card_le _).trans hlen,
        fun i hi => hall i (List.mem_toFinset.mp hi), Or.inr fun x => ?_⟩
      rw [val_key gs n j hj, hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id, List.mem_toFinset]
      constructor
      · intro h i hi
        exact ((ite_val _ _).mp (h _ ⟨i, hi, rfl⟩)).2
      · rintro h b ⟨i, hi, rfl⟩
        exact (ite_val _ _).mpr ⟨hall i hi, h i hi⟩
    · refine ⟨∅, by simp, by simp, Or.inl fun x => ?_⟩
      rw [val_key gs n j hj, hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id, Finset.notMem_empty,
        false_and, exists_false, iff_false, not_forall]
      rw [not_forall] at hall
      obtain ⟨i, hi⟩ := hall
      rw [Classical.not_imp] at hi
      refine ⟨_, ⟨i, hi.1, rfl⟩, ?_⟩
      simp [hi.2]
  · refine ⟨(gs[j]).inputs.toFinset.filter (fun i => i < n + j),
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen),
      fun i hi => (Finset.mem_filter.mp hi).2, Or.inl fun x => ?_⟩
    rw [val_key gs n j hj, hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id, Finset.mem_filter,
      List.mem_toFinset]
    constructor
    · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
      have := (ite_val _ _).mp hb
      exact ⟨i, ⟨hi, this.1⟩, this.2⟩
    · rintro ⟨i, ⟨hi, hlt⟩, hv⟩
      exact ⟨_, ⟨i, hi, rfl⟩, (ite_val _ _).mpr ⟨hlt, hv⟩⟩

def E (u : Fin 13) : Fin 13 → Bool := fun k => decide (k = u)

def S (gs : List Gate) (t : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun u => val gs 13 (E u) t = true)

def Pts (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => I p l)

def deg (B : Finset (Fin 13)) (ch : Fin 13 → Finset ℕ) (v : ℕ) : ℕ :=
  (B.filter (fun l => v ∈ ch l)).card

def wt (B : Finset (Fin 13)) (ch : Fin 13 → Finset ℕ) (l : Fin 13) (v : ℕ) : ℕ :=
  if v ∈ ch l then (if deg B ch v = 1 then 2 else if deg B ch v ≤ 4 then 1 else 0) else 0

lemma col (B : Finset (Fin 13)) (ch : Fin 13 → Finset ℕ) (v : ℕ) :
    ∑ l ∈ B, wt B ch l v ≤ 4 := by
  unfold wt
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have h : (B.filter (fun l => v ∈ ch l)).card = deg B ch v := rfl
  rw [h]
  generalize deg B ch v = d
  split_ifs <;> omega

lemma K (Pts : Fin 13 → Finset (Fin 13)) (S : ℕ → Finset (Fin 13)) (ch : Fin 13 → Finset ℕ)
    (B : Finset (Fin 13))
    (hU : ∀ l l' p q, p ≠ q → p ∈ Pts l → q ∈ Pts l → p ∈ Pts l' → q ∈ Pts l' → l = l')
    (hcard : ∀ l, (Pts l).card = 4)
    (hmeet : ∀ l l', ∃ P, P ∈ Pts l ∧ P ∈ Pts l')
    (hthru : ∀ P, (Finset.univ.filter (fun l => P ∈ Pts l)).card ≤ 4)
    (hsub : ∀ l ∈ B, ∀ v ∈ ch l, S v ⊆ Pts l ∨ Pts l ⊆ S v)
    (l : Fin 13) (a b : ℕ)
    (hab : S a ∩ S b = Pts l) (ha5 : 5 ≤ (S a).card) (hb5 : 5 ≤ (S b).card)
    (hdb : 2 ≤ deg B ch b) : deg B ch a ≤ 4 := by
  unfold deg at hdb ⊢
  obtain ⟨l', hl', hne⟩ := Finset.exists_mem_ne (s := B.filter (fun l => b ∈ ch l)) (by omega) l
  rw [Finset.mem_filter] at hl'
  have hl'b : Pts l' ⊆ S b := by
    rcases hsub l' hl'.1 b hl'.2 with h | h
    · have := Finset.card_le_card h
      rw [hcard] at this
      omega
    · exact h
  obtain ⟨P, hP, hP'⟩ := hmeet l l'
  refine le_trans (Finset.card_le_card ?_) (hthru P)
  intro l'' hl''
  rw [Finset.mem_filter] at hl'' ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have hl''a : Pts l'' ⊆ S a := by
    rcases hsub l'' hl''.1 a hl''.2 with h | h
    · have := Finset.card_le_card h
      rw [hcard] at this
      omega
    · exact h
  obtain ⟨Q, hQ, hQ'⟩ := hmeet l'' l'
  have hQl : Q ∈ Pts l := by
    rw [← hab]
    exact Finset.mem_inter.mpr ⟨hl''a hQ, hl'b hQ'⟩
  by_cases hQP : Q = P
  · rw [← hQP]
    exact hQ
  · exact absurd (hU l l' Q P hQP hQl hP hQ' hP').symm hne

lemma core (Pts : Fin 13 → Finset (Fin 13)) (S : ℕ → Finset (Fin 13)) (ch : Fin 13 → Finset ℕ)
    (B : Finset (Fin 13)) (X : Finset ℕ)
    (hU : ∀ l l' p q, p ≠ q → p ∈ Pts l → q ∈ Pts l → p ∈ Pts l' → q ∈ Pts l' → l = l')
    (hcard : ∀ l, (Pts l).card = 4)
    (hmeet : ∀ l l', ∃ P, P ∈ Pts l ∧ P ∈ Pts l')
    (hthru : ∀ P, (Finset.univ.filter (fun l => P ∈ Pts l)).card ≤ 4)
    (hsub : ∀ l ∈ B, ∀ v ∈ ch l, S v ⊆ Pts l ∨ Pts l ⊆ S v)
    (hch : ∀ l ∈ B, (∃ v ∈ ch l, v ∈ X ∧ S v ⊆ Pts l ∧ 2 ≤ (S v).card ∧ (S v).card ≤ 3) ∨
      (∃ a b, a ∈ ch l ∧ b ∈ ch l ∧ a ≠ b ∧ a ∈ X ∧ b ∈ X ∧ S a ∩ S b = Pts l ∧
        5 ≤ (S a).card ∧ 5 ≤ (S b).card)) :
    B.card ≤ 2 * X.card := by
  have row : ∀ l ∈ B, 2 ≤ ∑ v ∈ X, wt B ch l v := by
    intro l hl
    rcases hch l hl with ⟨v, hv, hvX, hvs, hv2, hv3⟩ | ⟨a, b, ha, hb, hab, haX, hbX, hI, ha5, hb5⟩
    · have hdeg : deg B ch v = 1 := by
        unfold deg
        rw [Finset.card_eq_one]
        refine ⟨l, ?_⟩
        ext l'
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hl', hv'⟩
          rcases hsub l' hl' v hv' with h | h
          · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (S v).card)
            exact hU l' l p q hpq (h hp) (h hq) (hvs hp) (hvs hq)
          · have := Finset.card_le_card h
            rw [hcard] at this
            omega
        · rintro rfl
          exact ⟨hl, hv⟩
      have hw : wt B ch l v = 2 := by
        unfold wt
        simp [hv, hdeg]
      calc 2 = wt B ch l v := hw.symm
        _ ≤ ∑ v ∈ X, wt B ch l v :=
          Finset.single_le_sum (f := fun v => wt B ch l v) (fun _ _ => Nat.zero_le _) hvX
    · have h1 := K Pts S ch B hU hcard hmeet hthru hsub l a b hI ha5 hb5
      have h2 := K Pts S ch B hU hcard hmeet hthru hsub l b a
        (by rw [Finset.inter_comm]; exact hI) hb5 ha5
      have hda : 1 ≤ deg B ch a := Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, ha⟩⟩
      have hdb : 1 ≤ deg B ch b := Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hb⟩⟩
      have hsum : wt B ch l a + wt B ch l b ≤ ∑ v ∈ X, wt B ch l v := by
        rw [← Finset.sum_pair (f := fun v => wt B ch l v) hab]
        apply Finset.sum_le_sum_of_subset
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact haX
        · exact hbX
      have h3 : 2 ≤ wt B ch l a + wt B ch l b := by
        unfold wt
        simp only [ha, hb, ite_true]
        split_ifs <;> omega
      omega
  have h1 : ∑ l ∈ B, 2 ≤ ∑ l ∈ B, ∑ v ∈ X, wt B ch l v := Finset.sum_le_sum row
  rw [Finset.sum_comm] at h1
  have h2 : ∑ v ∈ X, ∑ l ∈ B, wt B ch l v ≤ ∑ v ∈ X, 4 :=
    Finset.sum_le_sum (fun v _ => col B ch v)
  simp only [Finset.sum_const, smul_eq_mul] at h1 h2
  omega

lemma thru (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (h4 : ∀ l, (Pts I l).card = 4)
    (hu : ∀ p q : Fin 13, p ≠ q → ∃! l : Fin 13, I p l ∧ I q l) (p : Fin 13) :
    (Finset.univ.filter (fun l => I p l)).card = 4 := by
  classical
  have hb : ((Finset.univ.filter (fun l => I p l)).biUnion (fun l => (Pts I l).erase p))
      = Finset.univ.erase p := by
    ext q
    rw [Finset.mem_biUnion, Finset.mem_erase]
    constructor
    · rintro ⟨l, _, hq⟩
      exact ⟨(Finset.mem_erase.mp hq).1, Finset.mem_univ _⟩
    · rintro ⟨hq, _⟩
      obtain ⟨l, ⟨hl1, hl2⟩, _⟩ := hu p q (Ne.symm hq)
      exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl1⟩,
        Finset.mem_erase.mpr ⟨hq, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl2⟩⟩⟩
  have hd : ∀ l ∈ Finset.univ.filter (fun l => I p l), ∀ l' ∈ Finset.univ.filter (fun l => I p l),
      l ≠ l' → Disjoint ((Pts I l).erase p) ((Pts I l').erase p) := by
    intro l hl l' hl' hne
    rw [Finset.disjoint_left]
    intro q hq hq'
    rw [Finset.mem_erase] at hq hq'
    have a1 := (Finset.mem_filter.mp hl).2
    have a2 := (Finset.mem_filter.mp hl').2
    have b1 := (Finset.mem_filter.mp hq.2).2
    have b2 := (Finset.mem_filter.mp hq'.2).2
    exact hne ((hu p q (Ne.symm hq.1)).unique ⟨a1, b1⟩ ⟨a2, b2⟩)
  have hc := Finset.card_biUnion hd
  rw [hb] at hc
  have h3 : ∀ l ∈ Finset.univ.filter (fun l => I p l), ((Pts I l).erase p).card = 3 := by
    intro l hl
    have hp : p ∈ Pts I l := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
    rw [Finset.card_erase_of_mem hp, h4]
  rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hc
  omega

lemma meet (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (h4 : ∀ l, (Pts I l).card = 4)
    (hu : ∀ p q : Fin 13, p ≠ q → ∃! l : Fin 13, I p l ∧ I q l) (l l' : Fin 13) :
    ∃ P, I P l ∧ I P l' := by
  classical
  by_cases hll : l' = l
  · subst hll
    have hpos : 0 < (Pts I l').card := by
      rw [h4]
      omega
    obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
    exact ⟨P, (Finset.mem_filter.mp hP).2, (Finset.mem_filter.mp hP).2⟩
  · have hsub : ((Pts I l).biUnion (fun p => (Finset.univ.filter (fun m => I p m)).erase l))
        ⊆ Finset.univ.erase l := by
      intro m hm
      obtain ⟨p, _, hm⟩ := Finset.mem_biUnion.mp hm
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hm).1, Finset.mem_univ _⟩
    have hd : ∀ p ∈ Pts I l, ∀ q ∈ Pts I l, p ≠ q →
        Disjoint ((Finset.univ.filter (fun m => I p m)).erase l)
          ((Finset.univ.filter (fun m => I q m)).erase l) := by
      intro p hp q hq hne
      rw [Finset.disjoint_left]
      intro m hm hm'
      rw [Finset.mem_erase] at hm hm'
      have a1 := (Finset.mem_filter.mp hp).2
      have a2 := (Finset.mem_filter.mp hq).2
      have b1 := (Finset.mem_filter.mp hm.2).2
      have b2 := (Finset.mem_filter.mp hm'.2).2
      exact hm.1 ((hu p q hne).unique ⟨b1, b2⟩ ⟨a1, a2⟩)
    have hc := Finset.card_biUnion hd
    have h3 : ∀ p ∈ Pts I l, ((Finset.univ.filter (fun m => I p m)).erase l).card = 3 := by
      intro p hp
      have hl : l ∈ Finset.univ.filter (fun m => I p m) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
      rw [Finset.card_erase_of_mem hl, thru I h4 hu p]
    rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, h4] at hc
    have he := Finset.eq_of_subset_of_card_le hsub (by
      rw [hc, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin])
    have hl' : l' ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨hll, Finset.mem_univ _⟩
    rw [← he] at hl'
    obtain ⟨p, hp, hm⟩ := Finset.mem_biUnion.mp hl'
    exact ⟨p, (Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2⟩

lemma main (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (gates : List Gate) (out : Fin 13 → ℕ)
    (h4 : ∀ l, (Pts I l).card = 4)
    (hu : ∀ p q : Fin 13, p ≠ q → ∃! l : Fin 13, I p l ∧ I q l)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hout : ∀ l u : Fin 13, val gates 13 (E u) (out l) = true ↔ I u l)
    (B : Finset (Fin 13)) (H : Finset (Fin gates.length))
    (hH : ∀ k ∈ H, 2 ≤ (S gates (13 + k.val)).card ∧
      ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u : Fin 13, val gates 13 (E u) (13 + k.val) = true → I u l4) :
    3 * B.card + 2 * H.card ≤ 2 * gates.length := by
  classical
  have memS : ∀ t u, u ∈ S gates t ↔ val gates 13 (E u) t = true := by
    intro t u
    simp [S]
  have memP : ∀ l p, p ∈ Pts I l ↔ I p l := by
    intro l p
    simp [Pts]
  have hU : ∀ l l' p q, p ≠ q → p ∈ Pts I l → q ∈ Pts I l → p ∈ Pts I l' → q ∈ Pts I l' →
      l = l' := by
    intro l l' p q hpq h1 h2 h3 h5
    rw [memP] at h1 h2 h3 h5
    exact (hu p q hpq).unique ⟨h1, h2⟩ ⟨h3, h5⟩
  have hU2 : ∀ l l' (s : Finset (Fin 13)), 2 ≤ s.card → s ⊆ Pts I l → s ⊆ Pts I l' → l = l' := by
    intro l l' s hs h1 h2
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    exact hU l l' p q hpq (h1 hp) (h1 hq) (h2 hp) (h2 hq)
  have hmeet : ∀ l l', ∃ P, P ∈ Pts I l ∧ P ∈ Pts I l' := by
    intro l l'
    obtain ⟨P, h1, h2⟩ := meet I h4 hu l l'
    exact ⟨P, (memP _ _).mpr h1, (memP _ _).mpr h2⟩
  have hthru : ∀ P, (Finset.univ.filter (fun l => P ∈ Pts I l)).card ≤ 4 := by
    intro P
    have h := thru I h4 hu P
    have e : Finset.univ.filter (fun l => P ∈ Pts I l) = Finset.univ.filter (fun l => I P l) := by
      ext l
      simp [Pts]
    rw [e, h]
  have Sin : ∀ t, t < 13 → (S gates t).card ≤ 1 := by
    intro t ht
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [memS, val_in gates 13 t ht] at ha hb
    simp only [E, decide_eq_true_eq] at ha hb
    rw [← ha, ← hb]
  have Sout : ∀ t, 13 + gates.length ≤ t → (S gates t).card = 0 := by
    intro t ht
    rw [Finset.card_eq_zero]
    ext u
    rw [memS, val_out gates 13 t ht]
    simp
  have Sg : ∀ t, 2 ≤ (S gates t).card → 13 ≤ t ∧ t < 13 + gates.length := by
    intro t ht
    constructor
    · by_contra h
      have := Sin t (by omega)
      omega
    · by_contra h
      have := Sout t (by omega)
      omega
  have hex : ∀ l, ∃ t, S gates t = Pts I l := by
    intro l
    refine ⟨out l, ?_⟩
    ext u
    rw [memS, memP]
    exact hout l u
  obtain ⟨tl, htl, hmin⟩ : ∃ tl : Fin 13 → ℕ, (∀ l, S gates (tl l) = Pts I l) ∧
      ∀ l t, t < tl l → S gates t ≠ Pts I l :=
    ⟨fun l => Nat.find (hex l), fun l => Nat.find_spec (hex l),
      fun l t ht => Nat.find_min (hex l) ht⟩
  have hHs : ∀ k ∈ H, 2 ≤ (S gates (13 + k.val)).card ∧
      ∃ l4, l4 ∉ B ∧ S gates (13 + k.val) ⊆ Pts I l4 := by
    intro k hk
    obtain ⟨h2, l4, hl4, hs⟩ := hH k hk
    exact ⟨h2, l4, hl4, fun u hu' => (memP _ _).mpr (hs u ((memS _ _).mp hu'))⟩
  obtain ⟨X, hXdef⟩ : ∃ X : Finset ℕ, X = (Finset.Ico 13 (13 + gates.length)).filter
      (fun v => v ∉ B.image tl ∧ v ∉ H.image (fun k : Fin gates.length => 13 + k.val)) :=
    ⟨_, rfl⟩
  have hXbig : ∀ v, 5 ≤ (S gates v).card → v ∈ X := by
    intro v hv
    have hr := Sg v (by omega)
    rw [hXdef]
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hr, ?_, ?_⟩
    · intro hT
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hT
      rw [htl, h4] at hv
      omega
    · intro hH'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hH'
      obtain ⟨_, l4, _, hs⟩ := hHs k hk
      have := Finset.card_le_card hs
      rw [h4] at this
      omega
  have hXsmall : ∀ l ∈ B, ∀ v, S gates v ⊆ Pts I l → 2 ≤ (S gates v).card →
      (S gates v).card ≤ 3 → v ∈ X := by
    intro l hl v hs h2 h3
    rw [hXdef]
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (Sg v h2), ?_, ?_⟩
    · intro hT
      obtain ⟨l', _, rfl⟩ := Finset.mem_image.mp hT
      rw [htl, h4] at h3
      omega
    · intro hH'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hH'
      obtain ⟨_, l4, hl4, hs4⟩ := hHs k hk
      obtain rfl := hU2 l l4 _ h2 hs hs4
      exact hl4 hl
  have hchx : ∀ l, ∃ J : Finset ℕ, l ∈ B →
      ((∀ v ∈ J, S gates v ⊆ Pts I l ∨ Pts I l ⊆ S gates v) ∧
       ((∃ v ∈ J, v ∈ X ∧ S gates v ⊆ Pts I l ∧ 2 ≤ (S gates v).card ∧ (S gates v).card ≤ 3) ∨
        (∃ a b, a ∈ J ∧ b ∈ J ∧ a ≠ b ∧ a ∈ X ∧ b ∈ X ∧ S gates a ∩ S gates b = Pts I l ∧
          5 ≤ (S gates a).card ∧ 5 ≤ (S gates b).card))) := by
    intro l
    by_cases hl : l ∈ B
    swap
    · exact ⟨∅, fun h => absurd h hl⟩
    have hc4 : (S gates (tl l)).card = 4 := by rw [htl, h4]
    obtain ⟨hlo, hhi⟩ := Sg (tl l) (by omega)
    obtain ⟨J, hJ2, hJlt, hJ⟩ := gate_cases gates 13 hg (tl l) hlo hhi
    refine ⟨J, fun _ => ?_⟩
    rcases hJ with hor | hand
    · have hsubJ : ∀ v ∈ J, S gates v ⊆ Pts I l := by
        intro v hv u hu'
        rw [← htl l, memS]
        exact (hor (E u)).mpr ⟨v, hv, (memS _ _).mp hu'⟩
      refine ⟨fun v hv => Or.inl (hsubJ v hv), Or.inl ?_⟩
      have hlt3 : ∀ v ∈ J, (S gates v).card ≤ 3 := by
        intro v hv
        have hss : S gates v ⊂ Pts I l :=
          lt_of_le_of_ne (hsubJ v hv) (hmin l v (hJlt v hv))
        have := Finset.card_lt_card hss
        rw [h4] at this
        omega
      by_cases hex2 : ∃ v ∈ J, 2 ≤ (S gates v).card
      · obtain ⟨v, hv, h2⟩ := hex2
        exact ⟨v, hv, hXsmall l hl v (hsubJ v hv) h2 (hlt3 v hv), hsubJ v hv, h2, hlt3 v hv⟩
      · exfalso
        have h1 : ∀ v ∈ J, (S gates v).card ≤ 1 := by
          intro v hv
          by_contra h
          exact hex2 ⟨v, hv, by omega⟩
        have hcov : S gates (tl l) ⊆ J.biUnion (S gates) := by
          intro u hu'
          obtain ⟨v, hv, hvu⟩ := (hor (E u)).mp ((memS _ _).mp hu')
          exact Finset.mem_biUnion.mpr ⟨v, hv, (memS _ _).mpr hvu⟩
        have hc := Finset.card_le_card hcov
        have hb := Finset.card_biUnion_le (s := J) (t := S gates)
        have hs : ∑ v ∈ J, (S gates v).card ≤ ∑ v ∈ J, 1 := Finset.sum_le_sum h1
        rw [Finset.sum_const, smul_eq_mul, mul_one] at hs
        omega
    · have hsupJ : ∀ v ∈ J, Pts I l ⊆ S gates v := by
        intro v hv u hu'
        rw [← htl l, memS] at hu'
        exact (memS _ _).mpr ((hand (E u)).mp hu' v hv)
      refine ⟨fun v hv => Or.inr (hsupJ v hv), Or.inr ?_⟩
      have h5 : ∀ v ∈ J, 5 ≤ (S gates v).card := by
        intro v hv
        have hss : Pts I l ⊂ S gates v :=
          lt_of_le_of_ne (hsupJ v hv) (Ne.symm (hmin l v (hJlt v hv)))
        have := Finset.card_lt_card hss
        rw [h4] at this
        omega
      have hint : ∀ u, (∀ v ∈ J, u ∈ S gates v) → u ∈ Pts I l := by
        intro u hu'
        rw [← htl l, memS]
        exact (hand (E u)).mpr (fun v hv => (memS _ _).mp (hu' v hv))
      have hJ2' : J.card = 2 := by
        by_contra hne
        have hle : J.card ≤ 1 := by omega
        rw [Finset.card_le_one] at hle
        by_cases hemp : J = ∅
        · have hsb : (Finset.univ : Finset (Fin 13)) ⊆ Pts I l :=
            fun u _ => hint u (by rw [hemp]; simp)
          have := Finset.card_le_card hsb
          rw [h4] at this
          simp at this
        · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
          have hsb : S gates a ⊆ Pts I l :=
            fun u hu' => hint u (fun v hv => by rw [hle v hv a ha]; exact hu')
          have := Finset.card_le_card hsb
          rw [h4] at this
          have := h5 a ha
          omega
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hJ2'
      have ha : a ∈ ({a, b} : Finset ℕ) := by simp
      have hb : b ∈ ({a, b} : Finset ℕ) := by simp
      refine ⟨a, b, ha, hb, hab, hXbig a (h5 a ha), hXbig b (h5 b hb), ?_, h5 a ha, h5 b hb⟩
      apply Finset.Subset.antisymm
      · intro u hu'
        rw [Finset.mem_inter] at hu'
        apply hint
        intro v hv
        rw [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hu'.1
        · exact hu'.2
      · intro u hu'
        exact Finset.mem_inter.mpr ⟨hsupJ a ha hu', hsupJ b hb hu'⟩
  choose ch hch using hchx
  have hcore := core (Pts I) (S gates) ch B X hU h4 hmeet hthru
    (fun l hl => (hch l hl).1) (fun l hl => (hch l hl).2)
  have hTsub : B.image tl ⊆ Finset.Ico 13 (13 + gates.length) := by
    intro v hv
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_Ico.mpr (Sg _ (by have := h4 l; rw [htl]; omega))
  have hHsub : H.image (fun k : Fin gates.length => 13 + k.val) ⊆
      Finset.Ico 13 (13 + gates.length) := by
    intro v hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_Ico.mpr ⟨by omega, by have := k.isLt; omega⟩
  have hTcard : (B.image tl).card = B.card := by
    apply Finset.card_image_of_injOn
    intro l _ l' _ h
    have h' : tl l = tl l' := h
    have e : Pts I l = Pts I l' := by rw [← htl l, ← htl l', h']
    exact hU2 l l' (Pts I l) (by have := h4 l; omega) (Finset.Subset.refl _) (le_of_eq e)
  have hHcard : (H.image (fun k : Fin gates.length => 13 + k.val)).card = H.card := by
    apply Finset.card_image_of_injective
    intro a b h
    have h' : 13 + a.val = 13 + b.val := h
    exact Fin.ext (by omega)
  have hdisj1 : Disjoint (B.image tl) (H.image (fun k : Fin gates.length => 13 + k.val)) := by
    rw [Finset.disjoint_left]
    intro v hT hH'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp hH'
    obtain ⟨_, l4, hl4, hs⟩ := hHs k hk
    have hkv' : 13 + k.val = tl l := hkv
    rw [hkv', htl] at hs
    obtain rfl := hU2 l l4 _ (by have := h4 l; omega) (Finset.Subset.refl _) hs
    exact hl4 hl
  have hdisj2 : Disjoint (B.image tl ∪ H.image (fun k : Fin gates.length => 13 + k.val)) X := by
    rw [Finset.disjoint_left]
    intro v hv hX
    rw [hXdef] at hX
    have h := (Finset.mem_filter.mp hX).2
    rcases Finset.mem_union.mp hv with h' | h'
    · exact h.1 h'
    · exact h.2 h'
  have hXsub : X ⊆ Finset.Ico 13 (13 + gates.length) := by
    rw [hXdef]
    exact Finset.filter_subset _ _
  have hc := Finset.card_le_card (Finset.union_subset (Finset.union_subset hTsub hHsub) hXsub)
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1, hTcard, hHcard,
    Nat.card_Ico] at hc
  omega

end PEqualNP.Outside.L_meta_1619

theorem PEqualNP.Outside.L_meta_1619 : ∀ (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ l0 : Fin 13, (Finset.univ.filter (fun p0 : Fin 13 => I p0 l0)).card = 4) → (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (l2 u2 : Fin 13), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin 13 => decide (u2k = u2)))).getD (out l2) false = true ↔ I u2 l2) → ∀ (B : Finset (Fin 13)) (H : Finset (Fin gates.length)), (∀ k5 ∈ H, 2 ≤ (Finset.univ.filter (fun u5 : Fin 13 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin 13 => decide (u5k = u5)))).getD (13 + k5.val) false = true)).card ∧ ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u6 : Fin 13, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin 13 => decide (u6k = u6)))).getD (13 + k5.val) false = true → I u6 l4) → 3 * B.card + 2 * H.card ≤ 2 * gates.length := by
  intro I _ gates out h4 hu hg hout B H hH
  exact PEqualNP.Outside.L_meta_1619.main I gates out h4 hu hg hout B H hH
