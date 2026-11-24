import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1660

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Dep (n : ℕ) (D : Finset (Fin n)) (h : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i ∈ D, x i = y i) → h x = h y

def St (n : ℕ) (W : (Fin n → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin n)) : Prop :=
  (∀ x, (W x).length = m) ∧ ∀ i, Dep n (Sup i) (fun x => (W x).getD i false)

def sup0 (n : ℕ) (i : ℕ) : Finset (Fin n) := if h : i < n then {⟨i, h⟩} else ∅

lemma st_step (n : ℕ) (W : (Fin n → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin n))
    (h : St n W m Sup) (g : Gate) :
    St n (fun x => step (W x) g) (m + 1)
      (fun i => if i = m then g.inputs.toFinset.biUnion Sup else Sup i) := by
  obtain ⟨hm, hD⟩ := h
  refine ⟨fun x => by simp [step, hm x], fun i => ?_⟩
  intro x y hxy
  show (step (W x) g).getD i false = (step (W y) g).getD i false
  unfold step
  rcases lt_trichotomy i m with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by rw [hm x]; exact hi),
      List.getD_append _ _ _ _ (by rw [hm y]; exact hi)]
    refine hD i x y (fun j hj => hxy j ?_)
    simpa [hi.ne] using hj
  · rw [List.getD_append_right _ _ _ _ (by rw [hm x]; omega),
      List.getD_append_right _ _ _ _ (by rw [hm y]; omega), hm x, hm y]
    have e : (g.inputs.map fun k => (W x).getD k false) =
        (g.inputs.map fun k => (W y).getD k false) := by
      apply List.map_congr_left
      intro k hk
      refine hD k x y (fun j hj => hxy j ?_)
      have hmem : j ∈ g.inputs.toFinset.biUnion Sup :=
        Finset.mem_biUnion.mpr ⟨k, List.mem_toFinset.mpr hk, hj⟩
      simpa [hi] using hmem
    rw [e]
  · rw [List.getD_append_right _ _ _ _ (by rw [hm x]; omega),
      List.getD_append_right _ _ _ _ (by rw [hm y]; omega), hm x, hm y]
    obtain ⟨k, hk⟩ : ∃ k, i - m = k + 1 := ⟨i - m - 1, by omega⟩
    rw [hk]
    rfl

lemma st_init (n : ℕ) : St n (fun x : Fin n → Bool => List.ofFn x) n (sup0 n) := by
  refine ⟨fun x => List.length_ofFn, fun i x y hxy => ?_⟩
  show (List.ofFn x).getD i false = (List.ofFn y).getD i false
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    List.getElem?_ofFn]
  by_cases h : i < n
  · have hx := hxy ⟨i, h⟩ (by simp [sup0, h])
    simp [h, hx]
  · simp [h]

lemma sup0_card (n i : ℕ) : (sup0 n i).card ≤ 1 := by
  unfold sup0
  split <;> simp

lemma bound_step (n : ℕ) (Sup : ℕ → Finset (Fin n)) (k m : ℕ) (T : Finset ℕ)
    (hT : T.card ≤ 2) (h : ∀ Q : Finset ℕ, (Q.biUnion Sup).card ≤ Q.card + k) :
    ∀ Q : Finset ℕ,
      (Q.biUnion (fun i => if i = m then T.biUnion Sup else Sup i)).card ≤
        Q.card + (k + 1) := by
  intro Q
  by_cases hm : m ∈ Q
  · have e : Q.biUnion (fun i => if i = m then T.biUnion Sup else Sup i) =
        (T ∪ Q.erase m).biUnion Sup := by
      ext j
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase]
      constructor
      · rintro ⟨i, hi, hj⟩
        by_cases him : i = m
        · rw [if_pos him] at hj
          obtain ⟨t, ht, hjt⟩ := Finset.mem_biUnion.mp hj
          exact ⟨t, Or.inl ht, hjt⟩
        · rw [if_neg him] at hj
          exact ⟨i, Or.inr ⟨him, hi⟩, hj⟩
      · rintro ⟨t, ht | ⟨htm, htQ⟩, hj⟩
        · refine ⟨m, hm, ?_⟩
          rw [if_pos rfl]
          exact Finset.mem_biUnion.mpr ⟨t, ht, hj⟩
        · refine ⟨t, htQ, ?_⟩
          rw [if_neg htm]
          exact hj
    rw [e]
    have h1 := h (T ∪ Q.erase m)
    have h2 := Finset.card_union_le T (Q.erase m)
    have h3 := Finset.card_erase_of_mem hm
    have h4 : 0 < Q.card := Finset.card_pos.mpr ⟨m, hm⟩
    omega
  · have e : Q.biUnion (fun i => if i = m then T.biUnion Sup else Sup i) =
        Q.biUnion Sup := by
      apply Finset.biUnion_congr rfl
      intro i hi
      have him : i ≠ m := fun h' => hm (h' ▸ hi)
      simp [him]
    rw [e]
    have := h Q
    omega

lemma fold_sup (n : ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ (W : (Fin n → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin n)) (k : ℕ),
      St n W m Sup → (∀ Q : Finset ℕ, (Q.biUnion Sup).card ≤ Q.card + k) →
      ∃ Sup' : ℕ → Finset (Fin n),
        (∀ i, Dep n (Sup' i) (fun x => (gs.foldl step (W x)).getD i false)) ∧
        ∀ Q : Finset ℕ, (Q.biUnion Sup').card ≤ Q.card + (k + gs.length) := by
  intro gs
  induction gs with
  | nil =>
    intro _ W m Sup k hSt hb
    exact ⟨Sup, hSt.2, fun Q => by simpa using hb Q⟩
  | cons g gs ih =>
    intro hfan W m Sup k hSt hb
    have hg := hfan g List.mem_cons_self
    have hT : g.inputs.toFinset.card ≤ 2 := (List.toFinset_card_le _).trans hg
    obtain ⟨Sup', hdep, hb'⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      _ (m + 1) _ (k + 1) (st_step n W m Sup hSt g) (bound_step n Sup k m _ hT hb)
    refine ⟨Sup', hdep, fun Q => ?_⟩
    have := hb' Q
    simp only [List.length_cons]
    omega


lemma cast_ne_nat (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro e
  have h := congrArg Fin.val e
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h
  have := p.isLt
  omega

lemma nat_inj (N : ℕ) (m l : Fin N) (e : Fin.natAdd N m = Fin.natAdd N l) : m = l := by
  have h := congrArg Fin.val e
  simp only [Fin.coe_natAdd] at h
  exact Fin.ext (by omega)

end PEqualNP.Outside.L_meta_1660

open PEqualNP.Outside.L_meta_1660 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1660 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1 := by
  intro q N I _ C hq hN hline huniq hmono _ hacc hsound
  have h4 : 4 ≤ q ^ 2 := by
    have := Nat.pow_le_pow_left hq 2
    simpa using this
  have hN7 : 7 ≤ N := by omega
  obtain ⟨Sup, hdep, hb⟩ := fold_sup (N + N) C.gates (fun g hg => (hmono g hg).2) _ (N + N)
    (sup0 (N + N)) 0 (st_init (N + N)) (fun Q => by
      have := Finset.card_biUnion_le_card_mul Q (sup0 (N + N)) 1
        (fun a _ => sup0_card (N + N) a)
      omega)
  have hD := hdep C.output
  have h1 := hb {C.output}
  rw [Finset.singleton_biUnion, Finset.card_singleton] at h1
  have hall : ∀ v : Fin (N + N), v ∈ Sup C.output := by
    intro v
    by_contra hv
    have key : ∀ x y : Fin (N + N) → Bool, (∀ i, i ≠ v → x i = y i) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C x =
          PEqualNP.MetaComplexity.circuitFun (N + N) C y :=
      fun x y h => hD x y (fun i hi => h i (fun e => hv (e ▸ hi)))
    induction v using Fin.addCases with
    | left p =>
      have hne : ∃ pb : Fin N, p ≠ pb := by
        by_cases hp0 : p.val = 0
        · exact ⟨⟨1, by omega⟩, fun e => by
            have h := congrArg Fin.val e
            simp only at h
            omega⟩
        · exact ⟨⟨0, by omega⟩, fun e => by
            have h := congrArg Fin.val e
            simp only at h
            omega⟩
      obtain ⟨pb, hpb⟩ := hne
      obtain ⟨l, ⟨hpl, _⟩, _⟩ := huniq p pb hpb
      have e := key (fun k1 => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l))
        (fun k1 => decide (k1 = Fin.natAdd N l))
        (fun i hi => decide_eq_decide.mpr ⟨fun h => h.resolve_left hi, Or.inr⟩)
      rw [hacc p l hpl] at e
      have hs := hsound (fun k1 => decide (k1 = Fin.natAdd N l))
        (by
          refine le_trans (Finset.card_le_card (t := {l}) ?_) (by simp; omega)
          intro m hm
          have hm' := (Finset.mem_filter.mp hm).2
          exact Finset.mem_singleton.mpr (nat_inj N m l (of_decide_eq_true hm')))
        (by
          rintro ⟨p1, l1, _, hp1, _⟩
          exact cast_ne_nat N p1 l (of_decide_eq_true hp1))
      rw [hs] at e
      exact Bool.noConfusion e
    | right l =>
      have hc := hline l
      have hnon : (Finset.univ.filter (fun p0 => I p0 l)).Nonempty :=
        Finset.card_pos.mp (by rw [hc]; omega)
      obtain ⟨p, hp⟩ := hnon
      have hpl : I p l := (Finset.mem_filter.mp hp).2
      have e := key (fun k1 => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l))
        (fun k1 => decide (k1 = Fin.castAdd N p))
        (fun i hi => decide_eq_decide.mpr ⟨fun h => h.resolve_right hi, Or.inl⟩)
      rw [hacc p l hpl] at e
      have hs := hsound (fun k1 => decide (k1 = Fin.castAdd N p))
        (by
          refine le_trans (le_of_eq (Finset.card_eq_zero.mpr
            (Finset.filter_eq_empty_iff.mpr ?_))) (Nat.zero_le q)
          intro m _ hm
          exact cast_ne_nat N p m (of_decide_eq_true hm).symm)
        (by
          rintro ⟨p1, l1, _, _, hl1⟩
          exact cast_ne_nat N p l1 (of_decide_eq_true hl1).symm)
      rw [hs] at e
      exact Bool.noConfusion e
  have hu := Finset.eq_univ_iff_forall.mpr hall
  rw [hu, Finset.card_univ, Fintype.card_fin] at h1
  have hsz : C.size = C.gates.length := rfl
  omega
