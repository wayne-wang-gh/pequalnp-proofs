import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_252

open PEqualNP.MetaComplexity
open scoped BigOperators

private theorem splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
    (h : ((∃! i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, ¬ P (Fin.natAdd m j))) ∨
      ((∀ i : Fin m, ¬ P (Fin.castAdd n i)) ∧ (∃! j : Fin n, P (Fin.natAdd m j)))) :
    ∃! i, P i := by
  rcases h with ⟨⟨i, hi, hunique⟩, hnone⟩ | ⟨hnone, ⟨j, hj, hunique⟩⟩
  · refine ⟨Fin.castAdd n i, hi, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.castAdd n i) ?_ ?_ k
    · intro k hk
      exact congrArg (Fin.castAdd n) (hunique k hk)
    · intro k hk
      exact (hnone k hk).elim
  · refine ⟨Fin.natAdd m j, hj, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.natAdd m j) ?_ ?_ k
    · intro k hk
      exact (hnone k hk).elim
    · intro k hk
      exact congrArg (Fin.natAdd m) (hunique k hk)

private theorem formulaRectangles {n : ℕ}
    (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → φ.eval x = true ∧ x (label i) = true) ∧
        (∀ i y, Y i y → φ.eval y = false ∧ y (label i) = false) := by
  induction φ with
  | lit v c =>
      change c = true at mono
      subst c
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, fun _ => v, ?_, ?_, ?_⟩
      · intro x y hx hy
        change ∃! _i : Fin 1, x v = true ∧ y v = false
        exact ⟨0, ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx,
          by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy⟩,
          fun i _ => Subsingleton.elim i 0⟩
      · intro i x hx
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx, hx⟩
      · intro i y hy
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy, hy⟩
  | and a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ b.eval x = true) (fun i x => XB i x ∧ a.eval x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ a.eval y = true)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hx' : a.eval x = true ∧ b.eval x = true := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true_iff] using hx
        apply splitUnique
        cases ha : a.eval y with
        | false =>
            left
            constructor
            · simpa [X, Y, hx'.2] using totalA x y hx'.1 ha
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
        | true =>
            right
            have hb : b.eval y = false := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hy
            constructor
            · intro i hi
              have hLeft : YA i y := by simpa [Y] using hi.2
              have hFalse := (yA i y hLeft).1
              simp [ha] at hFalse
            · simpa [X, Y, hx'.1, ha, Fin.addCases_right] using totalB x y hx'.2 hb
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x ∧ b.eval x = true := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = true := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = true := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
  | or a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ a.eval x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ b.eval y = false) (fun i y => YB i y ∧ a.eval y = false)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hy' : a.eval y = false ∧ b.eval y = false := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_false_iff] using hy
        apply splitUnique
        cases ha : a.eval x with
        | false =>
            right
            have hb : b.eval x = true := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hx
            constructor
            · intro i hi
              have hLeft : XA i x := by simpa [X] using hi.1
              have hTrue := (xA i x hLeft).1
              simp [ha] at hTrue
            · simpa [X, Y, hy'.1, ha, Fin.addCases_right] using totalB x y hb hy'.2
        | true =>
            left
            constructor
            · simpa [X, Y, hy'.2] using totalA x y ha hy'.1
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = false := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y ∧ b.eval y = false := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = false := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩

private abbrev Monotone {n : ℕ} (φ : DMFormula n) : Prop :=
  DMFormula.rec (motive := fun _ : DMFormula n => Prop)
    (fun _ c => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

private abbrev Computes {n : ℕ} (G : SimpleGraph (Fin n)) (φ : DMFormula n) : Prop :=
  ∀ x, φ.eval x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

private abbrev NoSquare {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a

private lemma degreeTwo {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {v a b : V} (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b)
    (d : (Finset.univ.filter (G.Adj v)).card = 2) :
    ∀ w, G.Adj v w ↔ w = a ∨ w = b := by
  classical
  have he : ({a,b} : Finset V) = Finset.univ.filter (G.Adj v) := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp [ha, hb]
    · simp [d, hab]
  intro w
  have hm : w ∈ ({a,b} : Finset V) ↔ w ∈ Finset.univ.filter (G.Adj v) := by rw [he]
  simpa using hm.symm

private abbrev Ear {V : Type} (G : SimpleGraph V) (a b h : V) : Prop :=
  G.Adj a b ∧ G.Adj a h ∧ G.Adj b h ∧
    (∀ w, G.Adj a w ↔ w = b ∨ w = h) ∧ (∀ w, G.Adj b w ↔ w = a ∨ w = h)

private lemma ear_comm {V : Type} {G : SimpleGraph V} {a b h : V} (e : Ear G a b h) :
    Ear G b a h := ⟨e.1.symm, e.2.2.1, e.2.1, e.2.2.2.2, e.2.2.2.1⟩

private lemma clique_eq_of_tip {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {C : Finset V} {a b h : V} (e : Ear G a b h)
    (hc : G.IsNClique 3 C) (ha : a ∈ C) : C = {a,b,h} := by
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    by_cases eq : w = a
    · simp [eq]
    · have adj := hc.isClique ha hw (Ne.symm eq)
      simpa using Or.inr ((e.2.2.2.1 w).mp adj)
  · rw [hc.card_eq]
    simp [e.1.ne, e.2.1.ne, e.2.2.1.ne]

private abbrev Packing {V J : Type} [DecidableEq V] (G : SimpleGraph V)
    (a b h : J → V) : Prop :=
  (∀ j, Ear G (a j) (b j) (h j)) ∧
  (∀ i j, (a i = a j ∨ a i = b j ∨ b i = a j ∨ b i = b j) → i = j) ∧
  (∀ i j, h i ≠ a j ∧ h i ≠ b j) ∧
  (∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
    ∃ i, ({u,v,w} : Finset V) = {a i,b i,h i})

private lemma packing {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (weak : V → Prop)
    (ht : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      let d (v : V) := (Finset.univ.filter (G.Adj v)).card = 2
      (d a ∧ d b) ∨ (d a ∧ d c) ∨ (d b ∧ d c)) :
    ∃ (a b h : ↥(G.cliqueFinset 3) → V),
      Packing G a b h ∧ (∀ j, weak (a j) → weak (b j)) := by
  classical
  let J := ↥(G.cliqueFinset 3)
  have isClique (j : J) := SimpleGraph.mem_cliqueFinset_iff.mp j.prop
  have possible (j : J) :
      ∃ a b h, Ear G a b h ∧ j.val = {a,b,h} := by
    obtain ⟨u,v,w, huv,huw,hvw, he⟩ := SimpleGraph.is3Clique_iff.mp (isClique j)
    rcases ht u v w huv hvw huw with ⟨du,dv⟩ | ⟨du,dw⟩ | ⟨dv,dw⟩
    · exact ⟨u,v,w, ⟨huv,huw,hvw,degreeTwo huv huw hvw.ne du,
        degreeTwo huv.symm hvw huw.ne dv⟩, he⟩
    · refine ⟨u,w,v, ⟨huw,huv,hvw.symm,degreeTwo huw huv hvw.ne.symm du,
        degreeTwo huw.symm hvw.symm huv.ne dw⟩, ?_⟩
      rw [he]
      ext x
      simp [or_comm]
    · refine ⟨v,w,u, ⟨hvw,huv.symm,huw.symm,degreeTwo hvw huv.symm huw.ne.symm dv,
        degreeTwo hvw.symm huw.symm huv.ne.symm dw⟩, ?_⟩
      rw [he]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  have preferred (j : J) :
      ∃ a b h, Ear G a b h ∧ j.val = {a,b,h} ∧ (weak a → weak b) := by
    obtain ⟨a,b,h,e,eq⟩ := possible j
    by_cases ok : weak a → weak b
    · exact ⟨a,b,h,e,eq,ok⟩
    · have nb : ¬weak b := by tauto
      refine ⟨b,a,h,ear_comm e, ?_, fun hb => (nb hb).elim⟩
      rw [eq, Finset.insert_comm]
  choose a b h he using preferred
  have onlyA (i j : J) (hm : a i ∈ j.val) : i = j :=
    Subtype.ext ((he i).2.1.trans (clique_eq_of_tip (he i).1 (isClique j) hm).symm)
  have onlyB (i j : J) (hm : b i ∈ j.val) : i = j := by
    apply Subtype.ext
    rw [(he i).2.1, clique_eq_of_tip (ear_comm (he i).1) (isClique j) hm, Finset.insert_comm]
  have ma (i : J) : a i ∈ i.val := by simp [(he i).2.1]
  have mb (i : J) : b i ∈ i.val := by simp [(he i).2.1]
  have mh (i : J) : h i ∈ i.val := by simp [(he i).2.1]
  refine ⟨a,b,h, ⟨fun i => (he i).1, ?_, ?_, ?_⟩, fun i => (he i).2.2⟩
  · intro i j e
    rcases e with eq | eq | eq | eq
    · exact onlyA i j (eq ▸ ma j)
    · exact onlyA i j (eq ▸ mb j)
    · exact onlyB i j (eq ▸ ma j)
    · exact onlyB i j (eq ▸ mb j)
  · intro i j
    constructor
    · intro eq
      have ji := onlyA j i (eq ▸ mh i)
      subst j
      exact (he i).1.2.1.ne eq.symm
    · intro eq
      have ji := onlyB j i (eq ▸ mh i)
      subst j
      exact (he i).1.2.2.1.ne eq.symm
  · intro u v w huv huw hvw
    let i : J := ⟨{u,v,w}, SimpleGraph.mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv,huw,hvw⟩)⟩
    exact ⟨i, (he i).2.1⟩

private lemma unit_mem {I : Type} [Fintype I] [DecidableEq I]
    (W : Submodule ℚ (I → ℚ)) (i : I) (x : I → ℚ) (hx : x ∈ W) (hi : x i = 1)
    (rest : ∀ j ≠ i, x j = 0 ∨ Pi.single j (1 : ℚ) ∈ W) :
    Pi.single i (1 : ℚ) ∈ W := by
  classical
  let part : I → ℚ := ∑ j ∈ Finset.univ.erase i, x j • Pi.single j 1
  have hp : part ∈ W := by
    apply W.sum_mem
    intro j hj
    rcases rest j (Finset.mem_erase.mp hj).1 with hz | hu
    · simp [hz]
    · exact W.smul_mem _ hu
  have eq : x - part = Pi.single i 1 := by
    ext j
    change x j - (∑ k ∈ Finset.univ.erase i, x k • Pi.single k (1 : ℚ)) j = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases he : j = i
    · subst j
      rw [Finset.sum_eq_zero]
      · simp [hi]
      · intro k hk
        simp [Pi.single_eq_of_ne (Finset.mem_erase.mp hk).1.symm]
    · rw [Finset.sum_eq_single_of_mem j (Finset.mem_erase.mpr ⟨he, Finset.mem_univ _⟩)]
      · simp [Pi.single_eq_of_ne he]
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk.symm]
  rw [← eq]
  exact W.sub_mem hx hp

private lemma rank_bound {I L : Type} [Fintype I] [Fintype L] [DecidableEq I]
    (R : L → I → ℚ) (hu : ∀ i, Pi.single i (1 : ℚ) ∈ Submodule.span ℚ (Set.range R)) :
    Fintype.card I ≤ Fintype.card L := by
  classical
  let W := Submodule.span ℚ (Set.range R)
  have htop : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have eq : x = ∑ i, x i • Pi.single i (1 : ℚ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [eq]
    exact W.sum_mem fun i _ => W.smul_mem (x i) (hu i)
  have le : Module.finrank ℚ W ≤ Fintype.card L := by
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    exact Fintype.card_range_le R
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at le
  exact le

private lemma disjoin {I : Type} [DecidableEq I] {n : ℕ} (s : Finset I) (hs : s.Nonempty)
    (f : I → DMFormula n) (hf : ∀ i ∈ s, Monotone (f i)) :
    ∃ φ : DMFormula n, Monotone φ ∧ φ.leaves = ∑ i ∈ s, (f i).leaves ∧
      ∀ x, φ.eval x = true ↔ ∃ i ∈ s, (f i).eval x = true := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
      by_cases h : s.Nonempty
      · obtain ⟨ψ, hψ, hl, he⟩ := ih h (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        refine ⟨.or (f i) ψ, ⟨hf _ (Finset.mem_insert_self _ _), hψ⟩, ?_, ?_⟩
        · simp [DMFormula.leaves, hl, Finset.sum_insert hi]
        · intro x
          simp only [DMFormula.eval, Bool.or_eq_true_iff, he, Finset.mem_insert]
          constructor
          · rintro (hx | ⟨j,hj,hx⟩)
            · exact ⟨i, Or.inl rfl, hx⟩
            · exact ⟨j, Or.inr hj, hx⟩
          · rintro ⟨j,rfl | hj,hx⟩
            · exact Or.inl hx
            · exact Or.inr ⟨j,hj,hx⟩
      · rw [Finset.not_nonempty_iff_eq_empty.mp h] at *
        exact ⟨f i, hf i (by simp), by simp, by simp⟩

private lemma endpoints {V : Type} {G : SimpleGraph V} [Fintype G.edgeSet]
    (e : ↥G.edgeFinset) : ∃ u v, G.Adj u v ∧ Sym2.mk u v = e.val := by
  have mem := SimpleGraph.mem_edgeFinset.mp e.prop
  revert mem
  refine Sym2.inductionOn e.val ?_
  intro u v mem
  exact ⟨u,v,mem,rfl⟩

private lemma upper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : ∃ u v, G.Adj u v) (S : Finset (Fin n)) (hS : CoverPromise.IsVertexCover G S) :
    ∃ φ : DMFormula n, φ.leaves ≤ G.edgeFinset.card + S.card ∧ Monotone φ ∧ Computes G φ := by
  classical
  let E := ↥G.edgeFinset
  have orient (e : E) : ∃ u v, u ∈ S ∧ G.Adj u v ∧ Sym2.mk u v = e.val := by
    obtain ⟨u,v,had,eq⟩ := endpoints e
    rcases hS u v had with hs | hs
    · exact ⟨u,v,hs,had,eq⟩
    · exact ⟨v,u,hs,had.symm,Sym2.eq_swap.trans eq⟩
  choose center tip h using orient
  let C := Finset.univ.image center
  let fiber (v : Fin n) := (Finset.univ : Finset E).filter (fun e => center e = v)
  obtain ⟨u,v,huv⟩ := he
  let e : E := ⟨Sym2.mk u v,SimpleGraph.mem_edgeFinset.mpr huv⟩
  have hC : C.Nonempty := ⟨center e, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have stars (v : Fin n) (hv : v ∈ C) :
      ∃ φ : DMFormula n, Monotone φ ∧ φ.leaves = (fiber v).card + 1 ∧
        ∀ x, φ.eval x = true ↔ x v = true ∧ ∃ e ∈ fiber v, x (tip e) = true := by
    obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hv
    obtain ⟨ψ,hm,hl,hv⟩ := disjoin (fiber v) ⟨d, by simp [fiber, hd]⟩
      (fun e => DMFormula.lit (tip e) true) (fun _ _ => rfl)
    exact ⟨.and (.lit v true) ψ, ⟨rfl,hm⟩, by simp [DMFormula.leaves, hl, Nat.add_comm],
      by simp [DMFormula.eval, hv]⟩
  have starTotal (v : Fin n) : ∃ φ : DMFormula n, v ∈ C →
      Monotone φ ∧ φ.leaves = (fiber v).card + 1 ∧
        ∀ x, φ.eval x = true ↔ x v = true ∧ ∃ e ∈ fiber v, x (tip e) = true := by
    by_cases hv : v ∈ C
    · obtain ⟨φ, hφ⟩ := stars v hv
      exact ⟨φ, fun _ => hφ⟩
    · exact ⟨.lit v true, fun h => (hv h).elim⟩
  choose star hs using starTotal
  obtain ⟨φ,hm,hl,hev⟩ := disjoin C hC star (fun v hv => (hs v hv).1)
  refine ⟨φ, ?_, hm, ?_⟩
  · rw [hl, Finset.sum_congr rfl (fun v hv => (hs v hv).2.1), Finset.sum_add_distrib]
    have count := Finset.card_eq_sum_card_image (s := (Finset.univ : Finset E)) (f := center)
    have sub : C ⊆ S := by
      intro v hv
      obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hv
      exact (h d).1
    rw [show (∑ v ∈ C, (fiber v).card) = G.edgeFinset.card by
      simpa [C, fiber, E] using count.symm]
    simpa using Finset.card_le_card sub
  · intro x
    rw [hev]
    constructor
    · rintro ⟨v,hv,ht⟩
      obtain ⟨hval,d,hd,hdval⟩ := ((hs v hv).2.2 x).mp ht
      have eq : center d = v := (Finset.mem_filter.mp hd).2
      exact ⟨center d, tip d, (h d).2.1, eq ▸ hval, hdval⟩
    · rintro ⟨u,v,huv,hu,hv⟩
      let d : E := ⟨Sym2.mk u v, SimpleGraph.mem_edgeFinset.mpr huv⟩
      have hin : center d ∈ C := Finset.mem_image_of_mem _ (Finset.mem_univ _)
      have pair : center d = u ∧ tip d = v ∨ center d = v ∧ tip d = u :=
        Sym2.eq_iff.mp (h d).2.2
      have val : x (center d) = true ∧ x (tip d) = true := by
        rcases pair with ⟨hc,ht⟩ | ⟨hc,ht⟩ <;> simp [hc,ht,hu,hv]
      exact ⟨center d, hin, ((hs _ hin).2.2 x).mpr ⟨val.1,d,by simp [fiber],val.2⟩⟩

private abbrev Tip {J V : Type} (a b : J → V) (v : V) : Prop :=
  ∃ j, a j = v ∨ b j = v

private abbrev Star {J V : Type} (G : SimpleGraph V) (a b h : J → V)
    (v : V) (flip : J → Prop) (w : V) : Prop :=
  (G.Adj v w ∧ ¬ Tip a b w) ∨ ∃ j, h j = v ∧
    ((¬ flip j ∧ a j = w) ∨ (flip j ∧ b j = w))

private lemma star_adj {J V : Type} [DecidableEq V] {G : SimpleGraph V} {a b h : J → V}
    (hp : Packing G a b h) {v w : V} {flip : J → Prop} (hs : Star G a b h v flip w) :
    G.Adj v w := by
  rcases hs with ha | ⟨j,rfl,⟨_,rfl⟩ | ⟨_,rfl⟩⟩
  · exact ha.1
  · exact (hp.1 j).2.1.symm
  · exact (hp.1 j).2.2.1.symm

private lemma star_tip {J V : Type} [DecidableEq V] {G : SimpleGraph V} {a b h : J → V}
    (hp : Packing G a b h) (v : V) (flip : J → Prop) (j : J) :
    (Star G a b h v flip (a j) ↔ h j = v ∧ ¬ flip j) ∧
    (Star G a b h v flip (b j) ↔ h j = v ∧ flip j) := by
  constructor
  · constructor
    · rintro (⟨_,hn⟩ | ⟨i,eq,hf⟩)
      · exact (hn ⟨j,Or.inl rfl⟩).elim
      · rcases hf with ⟨hf,e⟩ | ⟨hf,e⟩
        · have ij := hp.2.1 i j (Or.inl e)
          subst i
          exact ⟨eq,hf⟩
        · have ij := hp.2.1 i j (Or.inr (Or.inr (Or.inl e)))
          subst i
          exact ((hp.1 j).1.ne e.symm).elim
    · rintro ⟨eq,hf⟩
      exact Or.inr ⟨j,eq,Or.inl ⟨hf,rfl⟩⟩
  · constructor
    · rintro (⟨_,hn⟩ | ⟨i,eq,hf⟩)
      · exact (hn ⟨j,Or.inr rfl⟩).elim
      · rcases hf with ⟨hf,e⟩ | ⟨hf,e⟩
        · have ij := hp.2.1 i j (Or.inr (Or.inl e))
          subst i
          exact ((hp.1 j).1.ne e).elim
        · have ij := hp.2.1 i j (Or.inr (Or.inr (Or.inr e)))
          subst i
          exact ⟨eq,hf⟩
    · rintro ⟨eq,hf⟩
      exact Or.inr ⟨j,eq,Or.inr ⟨hf,rfl⟩⟩

private lemma star_independent {J V : Type} [DecidableEq V] {G : SimpleGraph V}
    {a b h : J → V} (hp : Packing G a b h) {v : V} (hv : ¬ Tip a b v) (flip : J → Prop)
    {u w : V} (hu : Star G a b h v flip u) (hw : Star G a b h v flip w) : ¬ G.Adj u w := by
  intro huw
  obtain ⟨j,ej⟩ := hp.2.2.2 v u w (star_adj hp hu) (star_adj hp hw) huw
  have memV : v = a j ∨ v = b j ∨ v = h j := by
    have mem : v ∈ ({v,u,w} : Finset V) := by simp
    rw [ej] at mem
    simpa using mem
  have eqV : v = h j := by
    rcases memV with e | e | e
    · exact (hv ⟨j,Or.inl e.symm⟩).elim
    · exact (hv ⟨j,Or.inr e.symm⟩).elim
    · exact e
  have tips (z : V) (hz : z ∈ ({v,u,w} : Finset V)) (hn : z ≠ v) : z = a j ∨ z = b j := by
    rw [ej] at hz
    simpa [← eqV, hn] using hz
  rcases tips u (by simp) (star_adj hp hu).ne.symm with rfl | rfl <;>
    rcases tips w (by simp) (star_adj hp hw).ne.symm with rfl | rfl
  · exact G.loopless.irrefl _ huw
  · exact ((star_tip hp v flip j).1.mp hu).2 ((star_tip hp v flip j).2.mp hw).2
  · exact ((star_tip hp v flip j).1.mp hw).2 ((star_tip hp v flip j).2.mp hu).2
  · exact G.loopless.irrefl _ huw

private abbrev PairColumn {J V : Type} (G : SimpleGraph V) (a b h : J → V) (v w z : V) : Prop :=
  (Star G a b h v (fun _ => False) z ∨ Star G a b h w (fun _ => False) z) ∧ z ≠ v ∧ z ≠ w

private lemma pair_independent {J V : Type} [DecidableEq V] {G : SimpleGraph V}
    {a b h : J → V} (hp : Packing G a b h) (hs : NoSquare G) {v w : V} (hvw : G.Adj v w)
    (hv : ¬ Tip a b v) (hw : ¬ Tip a b w) {x y : V}
    (hx : PairColumn G a b h v w x) (hy : PairColumn G a b h v w y) : ¬ G.Adj x y := by
  intro hxy
  rcases hx.1 with hx' | hx' <;> rcases hy.1 with hy' | hy'
  · exact star_independent hp hv _ hx' hy' hxy
  · exact hs v x y w hx.2.1.symm hy.2.1.symm hvw.ne hxy.ne hx.2.2 hy.2.2
      (star_adj hp hx') hxy (star_adj hp hy').symm hvw.symm
  · exact hs w x y v hx.2.2.symm hy.2.2.symm hvw.ne.symm hxy.ne hx.2.1 hy.2.1
      (star_adj hp hx') hxy (star_adj hp hy').symm hvw
  · exact star_independent hp hw _ hx' hy' hxy

private lemma edge_count {V J : Type} [Fintype V] [DecidableEq V] [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b h : J → V} (hp : Packing G a b h)
    (E : Finset (Sym2 V)) (hE : E = G.edgeFinset.filter (fun e => ∀ v ∈ e, ¬ Tip a b v)) :
    G.edgeFinset.card ≤ E.card + 3 * Fintype.card J := by
  classical
  let A := Finset.univ.image fun j : J => Sym2.mk (a j) (b j)
  let B := Finset.univ.image fun j : J => Sym2.mk (a j) (h j)
  let C := Finset.univ.image fun j : J => Sym2.mk (b j) (h j)
  have fromA {j : J} {u w : V} (eq : a j = u) (had : G.Adj u w) :
      Sym2.mk u w ∈ A ∪ B ∪ C := by
    subst u
    rcases ((hp.1 j).2.2.2.1 w).mp had with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have fromB {j : J} {u w : V} (eq : b j = u) (had : G.Adj u w) :
      Sym2.mk u w ∈ A ∪ B ∪ C := by
    subst u
    rcases ((hp.1 j).2.2.2.2 w).mp had with rfl | rfl
    · rw [Sym2.eq_swap]
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have sub : G.edgeFinset ⊆ E ∪ (A ∪ B ∪ C) := by
    intro e he
    by_cases hem : e ∈ E
    · exact Finset.mem_union_left _ hem
    apply Finset.mem_union_right
    obtain ⟨u,w,had,eq⟩ := endpoints (⟨e,he⟩ : ↥G.edgeFinset)
    change Sym2.mk u w = e at eq
    subst e
    have ht : Tip a b u ∨ Tip a b w := by
      by_contra! hn
      apply hem
      rw [hE]
      exact Finset.mem_filter.mpr ⟨he,fun v hv => by
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · rintro ⟨j,eq | eq⟩
          · exact (hn.1 j).1 eq
          · exact (hn.1 j).2 eq
        · rintro ⟨j,eq | eq⟩
          · exact (hn.2 j).1 eq
          · exact (hn.2 j).2 eq⟩
    rcases ht with ⟨j,eq | eq⟩ | ⟨j,eq | eq⟩
    · exact fromA eq had
    · exact fromB eq had
    · rw [Sym2.eq_swap]
      exact fromA eq had.symm
    · rw [Sym2.eq_swap]
      exact fromB eq had.symm
  have h₁ := Finset.card_le_card sub
  have h₂ := Finset.card_union_le E (A ∪ B ∪ C)
  have h₃ := Finset.card_union_le (A ∪ B) C
  have h₄ := Finset.card_union_le A B
  have ha : A.card ≤ Fintype.card J := by
    simpa [A] using (Finset.card_image_le
      (s := (Finset.univ : Finset J)) (f := fun j => Sym2.mk (a j) (b j)))
  have hb : B.card ≤ Fintype.card J := by
    simpa [B] using (Finset.card_image_le
      (s := (Finset.univ : Finset J)) (f := fun j => Sym2.mk (a j) (h j)))
  have hc : C.card ≤ Fintype.card J := by
    simpa [C] using (Finset.card_image_le
      (s := (Finset.univ : Finset J)) (f := fun j => Sym2.mk (b j) (h j)))
  omega

private lemma tip_slots {V J I : Type} [DecidableEq V] [Fintype V] [DecidableEq J] [Fintype J] [Fintype I]
    {G : SimpleGraph V} {a b h : J → V} (hp : Packing G a b h) (label : I → V)
    (slots : V → Finset I) (hslots : ∀ v, slots v = Finset.univ.filter (fun i => label i = v))
    (A : Finset J) (ha : ∀ j, 2 ≤ (slots (a j)).card)
    (hb : ∀ j, (if j ∈ A then 1 else 2) ≤ (slots (b j)).card) :
    4 * Fintype.card J ≤
      A.card + (Finset.univ.filter (fun i => Tip a b (label i))).card := by
  classical
  let tips : J ⊕ J → V := Sum.elim a b
  have inj : Function.Injective tips := by
    intro x y he
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hp.2.1 i j (Or.inl he))
      | inr j =>
        have eq := hp.2.1 i j (Or.inr (Or.inl he))
        subst j
        exact ((hp.1 i).1.ne he).elim
    | inr i =>
      cases y with
      | inl j =>
        have eq := hp.2.1 i j (Or.inr (Or.inr (Or.inl he)))
        subst j
        exact ((hp.1 i).1.ne he.symm).elim
      | inr j => exact congrArg Sum.inr (hp.2.1 i j (Or.inr (Or.inr (Or.inr he))))
  have mem (v : V) : v ∈ Finset.univ.image tips ↔ Tip a b v := by
    constructor
    · intro hv
      obtain ⟨i,_,eq⟩ := Finset.mem_image.mp hv
      cases i with
      | inl j => exact ⟨j,Or.inl eq⟩
      | inr j => exact ⟨j,Or.inr eq⟩
    · rintro ⟨j,eq | eq⟩
      · exact Finset.mem_image.mpr ⟨Sum.inl j,Finset.mem_univ _,eq⟩
      · exact Finset.mem_image.mpr ⟨Sum.inr j,Finset.mem_univ _,eq⟩
  have eq :
      (Finset.univ.filter (fun i => Tip a b (label i))).card =
        (∑ j : J, (slots (a j)).card) + ∑ j : J, (slots (b j)).card := by
    rw [← show Finset.univ.filter (fun i => label i ∈ Finset.univ.image tips) =
        Finset.univ.filter (fun i => Tip a b (label i)) by ext i; simp only [Finset.mem_filter,
          Finset.mem_univ, true_and, mem],
      ← Finset.sum_card_fiberwise_eq_card_filter _ _ label]
    simp only [← hslots]
    rw [Finset.sum_image (fun _ _ _ _ eq => inj eq), Fintype.sum_sum_type]
    rfl
  rw [eq]
  have t₁ : 2 * Fintype.card J ≤ ∑ j : J, (slots (a j)).card := by
    simpa [Nat.mul_comm] using Finset.sum_le_sum (s := (Finset.univ : Finset J))
      (fun j _ => ha j)
  have t₂ := Finset.sum_le_sum (s := (Finset.univ : Finset J)) (fun j _ => hb j)
  have count : (∑ j : J, if j ∈ A then 1 else 2) + A.card = 2 * Fintype.card J := by
    rw [show A.card = ∑ j : J, if j ∈ A then 1 else 0 by
      simp]
    rw [← Finset.sum_add_distrib]
    have eq : ∀ j : J, (if j ∈ A then 1 else 2) + (if j ∈ A then 1 else 0) = 2 := by
      intro j
      split <;> simp_all
    simp [eq, Nat.mul_comm]
  omega

set_option maxHeartbeats 2500000 in
private lemma lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hs : NoSquare G)
    (ht : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      let d (v : Fin n) := (Finset.univ.filter (G.Adj v)).card = 2
      (d a ∧ d b) ∨ (d a ∧ d c) ∨ (d b ∧ d c))
    (t : ℕ) (hmin : ∀ S, CoverPromise.IsVertexCover G S → t ≤ S.card)
    (φ : DMFormula n) (hm : Monotone φ) (hf : Computes G φ) :
    G.edgeFinset.card + t ≤ φ.leaves := by
  classical
  let V := Fin n
  obtain ⟨X,Y,label,partition,goodX,goodY⟩ := formulaRectangles φ hm
  let row (v w : V) (z : V) : Bool := decide (z = v ∨ z = w)
  let colInput (P : V → Prop) (z : V) : Bool := decide (P z)
  let Indep (P : V → Prop) := ∀ v w, P v → P w → ¬ G.Adj v w
  have pos {v w : V} (e : G.Adj v w) : φ.eval (row v w) = true :=
    (hf _).mpr ⟨v,w,e,by simp [row],by simp [row]⟩
  have neg {P : V → Prop} (hP : Indep P) : φ.eval (colInput P) = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨v,w,had,hv,hw⟩ := (hf _).mp he
    exact hP v w (of_decide_eq_true hv) (of_decide_eq_true hw) had
  let route {v w : V} (e : G.Adj v w) {P : V → Prop} (hP : Indep P) :=
    Classical.choose (partition (row v w) (colInput P) (pos e) (neg hP))
  have routeMem {v w : V} (e : G.Adj v w) {P : V → Prop} (hP : Indep P) :
      X (route e hP) (row v w) ∧ Y (route e hP) (colInput P) :=
    (Classical.choose_spec (partition (row v w) (colInput P) (pos e) (neg hP))).1
  have routeEq {v w : V} (e : G.Adj v w) {P : V → Prop} (hP : Indep P) (i : Fin φ.leaves)
      (hx : X i (row v w)) (hy : Y i (colInput P)) : i = route e hP :=
    (Classical.choose_spec (partition (row v w) (colInput P) (pos e) (neg hP))).2 i ⟨hx,hy⟩
  let sel {v w : V} (e : G.Adj v w) {P : V → Prop} (hP : Indep P) :=
    label (route e hP)
  have selEnd {v w : V} (e : G.Adj v w) {P : V → Prop} (hP : Indep P) :
      sel e hP = v ∨ sel e hP = w :=
    of_decide_eq_true ((goodX _ _ (routeMem e hP).1).2)
  have selNot {v w : V} (e : G.Adj v w) {P : V → Prop} (hP : Indep P) :
      ¬ P (sel e hP) :=
    of_decide_eq_false ((goodY _ _ (routeMem e hP).2).2)
  have selComm {v w : V} (e : G.Adj v w) {P : V → Prop} (hP : Indep P) :
      sel e.symm hP = sel e hP := by
    apply congrArg label
    apply routeEq e hP _ _ (routeMem e.symm hP).2
    have eq : row v w = row w v := by funext z; simp [row, Bool.or_comm]
    rw [eq]
    exact (routeMem e.symm hP).1
  have force {v w : V} (e : G.Adj v w) {P : V → Prop} (hP : Indep P) (hw : P w) :
      sel e hP = v := by
    rcases selEnd e hP with hv | he
    · exact hv
    · exact (selNot e hP (he.symm ▸ hw)).elim
  let single (w : V) : Indep (fun v => v = w) := by
    rintro _ _ rfl rfl ha
    exact G.irrefl ha
  let slots (v : V) := Finset.univ.filter (fun i : Fin φ.leaves => label i = v)
  let weak (v : V) := (slots v).card = 1
  have slot_pos {v w : V} (e : G.Adj v w) : 0 < (slots v).card := by
    apply Finset.card_pos.mpr
    exact ⟨route e (single w), by simpa [slots] using force e (single w) rfl⟩
  have sync {v w z : V} (e : G.Adj v w) (e' : G.Adj v z) (hv : weak v)
      {P : V → Prop} (hP : Indep P) (he : sel e hP = v) : sel e' hP = v := by
    have hsame : route e hP = route e' (single z) := by
      apply Finset.card_le_one.mp (show (slots v).card ≤ 1 by exact hv.le)
      · simpa [slots] using he
      · simpa [slots] using force e' (single z) rfl
    have eq : route e hP = route e' hP := by
      apply routeEq e' hP _ _ (routeMem e hP).2
      rw [hsame]
      exact (routeMem e' (single z)).1
    exact (congrArg label eq).symm.trans he
  obtain ⟨a,b,h,hp,hpref⟩ := packing G weak ht
  let J := ↥(G.cliqueFinset 3)
  have hstrong (j : J) : ¬ weak (a j) := by
    intro wa
    have wb := hpref j wa
    have ea := hp.1 j
    have ab := sync ea.2.1 ea.1 wa (single (h j)) (force ea.2.1 (single (h j)) rfl)
    have ba := sync ea.2.2.1 ea.1.symm wb (single (h j)) (force ea.2.2.1 (single (h j)) rfl)
    exact ea.1.ne (ab.symm.trans ((selComm ea.1 (single (h j))).symm.trans ba))
  -- A triangle has at most one tip with a single leaf.
  let A : Finset J := Finset.univ.filter (fun j => weak (b j))
  have weakB (j : J) : j ∈ A ↔ weak (b j) := by simp [A]
  have weak_miss (j : ↥A) {P : V → Prop} (hP : Indep P) (ha : P (a j)) :
      sel (hp.1 j).2.2.1.symm hP ≠ h j := by
    have ea := hp.1 j
    have hbit := sync ea.1.symm ea.2.2.1 ((weakB j).mp j.prop) hP (force ea.1.symm hP ha)
    rw [selComm ea.2.2.1 hP, hbit]
    exact ea.2.2.1.ne
  have hhub (j : J) : ¬ Tip a b (h j) := by
    rintro ⟨i,eq | eq⟩
    · exact (hp.2.2.1 j i).1 eq.symm
    · exact (hp.2.2.1 j i).2 eq.symm
  let es := G.edgeFinset.filter (fun e => ∀ v ∈ e, ¬ Tip a b v)
  let E := ↥es
  have eorient (e : E) :
      ∃ v w, G.Adj v w ∧ Sym2.mk v w = e.val ∧ ¬ Tip a b v ∧ ¬ Tip a b w := by
    obtain ⟨he,hn⟩ := Finset.mem_filter.mp e.prop
    obtain ⟨v,w,evw,eq⟩ := endpoints (⟨e.val,he⟩ : ↥G.edgeFinset)
    change Sym2.mk v w = e.val at eq
    exact ⟨v,w,evw,eq, hn v (eq ▸ Sym2.mem_mk_left _ _), hn w (eq ▸ Sym2.mem_mk_right _ _)⟩
  choose u v hE using eorient
  let base (v : V) := Star G a b h v (fun _ => False)
  let pair (v w : V) := PairColumn G a b h v w
  have baseInd {v : V} (hv : ¬ Tip a b v) : Indep (base v) :=
    fun _ _ => star_independent hp hv _
  have pairInd {v w : V} (e : G.Adj v w) (hv : ¬ Tip a b v) (hw : ¬ Tip a b w) :
      Indep (pair v w) := fun _ _ => pair_independent hp hs e hv hw
  have pInd (e : E) : Indep (pair (u e) (v e)) :=
    pairInd (hE e).1 (hE e).2.2.1 (hE e).2.2.2
  let win (e : E) := sel (hE e).1 (pInd e)
  let lose (e : E) := if win e = u e then v e else u e
  have winLose (e : E) :
      G.Adj (lose e) (win e) ∧ Sym2.mk (lose e) (win e) = e.val ∧
      ¬ Tip a b (lose e) ∧ ¬ Tip a b (win e) := by
    rcases selEnd (hE e).1 (pInd e) with eq | eq
    · change win e = u e at eq
      simpa [lose,eq,Sym2.eq_swap] using
        And.intro (hE e).1.symm (And.intro (hE e).2.1
          (And.intro (hE e).2.2.2 (hE e).2.2.1))
    · change win e = v e at eq
      simpa [lose,eq,(hE e).1.ne.symm] using hE e
  have pairSwap (e : E) : pair (lose e) (win e) = pair (u e) (v e) := by
    rcases selEnd (hE e).1 (pInd e) with eq | eq
    · change win e = u e at eq
      funext z
      simp [lose,eq,pair,or_comm,and_comm]
    · change win e = v e at eq
      simp [lose,eq,(hE e).1.ne.symm]
  have loseMiss (e : E) :
      sel (winLose e).1 (pairInd (winLose e).1 (winLose e).2.2.1 (winLose e).2.2.2) ≠ lose e := by
    let hP := pairInd (winLose e).1 (winLose e).2.2.1 (winLose e).2.2.2
    have hr : row (lose e) (win e) = row (u e) (v e) := by
      rcases selEnd (hE e).1 (pInd e) with eq | eq
      · change win e = u e at eq
        funext z
        simp [row,lose,eq,Bool.or_comm]
      · change win e = v e at eq
        simp [lose,eq,(hE e).1.ne.symm]
    have he : route (winLose e).1 hP = route (hE e).1 (pInd e) := by
      apply routeEq (hE e).1 (pInd e)
      · rw [← hr]
        exact (routeMem (winLose e).1 hP).1
      · exact (congrArg (fun P => Y _ (colInput P)) (pairSwap e)).mp (routeMem (winLose e).1 hP).2
    change label (route (winLose e).1 hP) ≠ lose e
    rw [he]
    exact (winLose e).1.ne.symm
  have sameEdge {e d : E} (hl : lose e = lose d) (hw : win e = win d) : e = d := by
    apply Subtype.ext
    rw [← (winLose e).2.1, ← (winLose d).2.1, hl, hw]
  have swapEdge {e d : E} (hl : lose e = win d) (hw : win e = lose d) : e = d := by
    apply Subtype.ext
    rw [← (winLose e).2.1, ← (winLose d).2.1, hl, hw, Sym2.eq_swap]
  let U : Finset V := Finset.univ.image h ∪ Finset.univ.image win
  have hU (z : ↥U) : ¬ Tip a b z := by
    rcases Finset.mem_union.mp z.prop with hi | hi
    · obtain ⟨j,_,eq⟩ := Finset.mem_image.mp hi
      exact eq ▸ hhub j
    · obtain ⟨e,_,eq⟩ := Finset.mem_image.mp hi
      exact eq ▸ (winLose e).2.2.2
  have anchorEx (z : ↥U) : ∃ w, base z w ∧ ∀ e, lose e = z → w ≠ win e := by
    rcases Finset.mem_union.mp z.prop with hi | hi
    · obtain ⟨j,_,eq⟩ := Finset.mem_image.mp hi
      refine ⟨a j, (star_tip hp z _ j).1.mpr ⟨eq,not_false⟩, fun e _ he => ?_⟩
      exact (winLose e).2.2.2 ⟨j,Or.inl he⟩
    · obtain ⟨d,_,eq⟩ := Finset.mem_image.mp hi
      refine ⟨lose d, Or.inl ⟨eq ▸ (winLose d).1.symm,(winLose d).2.2.1⟩, ?_⟩
      intro e he hw
      have ed := swapEdge (he.trans eq.symm) hw.symm
      subst e
      exact (winLose d).1.ne hw
  choose anchor ha using anchorEx
  -- Count a coordinate per remaining edge, cover vertex, and single-leaf tip.
  let I := E ⊕ (↥U ⊕ ↥A)
  let coord : I → V × V := Sum.elim (fun e => (lose e, win e))
    (Sum.elim (fun z => (z.val,anchor z)) (fun j => (h j,b j)))
  have adjCoord (i : I) : G.Adj (coord i).1 (coord i).2 := by
    rcases i with e | z | j
    · exact (winLose e).1
    · exact star_adj hp (ha z).1
    · exact (hp.1 j).2.2.1.symm
  let live := Finset.univ.filter (fun i : Fin φ.leaves => ¬ Tip a b (label i))
  let raw (l : Fin φ.leaves) (i : I) : ℚ :=
    if (coord i).1 = label l ∧ X l (row (coord i).1 (coord i).2) then 1 else 0
  let R (l : ↥live) : I → ℚ := raw l.val
  let W := Submodule.span ℚ (Set.range R)
  let C (z : V) (P : V → Prop) : I → ℚ :=
    ∑ l : Fin φ.leaves, if Y l (colInput P) ∧ label l = z then raw l else 0
  have cmem (z : V) (P : V → Prop) (hz : ¬ Tip a b z) : C z P ∈ W := by
    apply W.sum_mem
    intro l _
    split
    · rename_i hcond
      have hl : l ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcond.2.symm ▸ hz⟩
      exact Submodule.subset_span ⟨⟨l,hl⟩,rfl⟩
    · exact W.zero_mem
  have cval (z : V) {P : V → Prop} (hP : Indep P) (i : I) :
      C z P i = if (coord i).1 = z ∧ sel (adjCoord i) hP = z then 1 else 0 := by
    simp only [C, Finset.sum_apply]
    rw [Finset.sum_eq_single (route (adjCoord i) hP)]
    · by_cases eq : label (route (adjCoord i) hP) = z
      · simp [raw, sel, eq, (routeMem (adjCoord i) hP).1, (routeMem (adjCoord i) hP).2]
      · simp [sel, eq]
    · intro l _ other
      by_cases hc : Y l (colInput P) ∧ label l = z
      · have nx : ¬ X l (row (coord i).1 (coord i).2) :=
          fun hx => other (routeEq (adjCoord i) hP l hx hc.1)
        simp [hc,raw,nx]
      · simp [hc]
    · simp
  have c_off {z : V} {P : V → Prop} (hP : Indep P) (i : I) (hz : (coord i).1 ≠ z) :
      C z P i = 0 := by simp [cval z hP i, hz]
  have c_hit {z : V} {P : V → Prop} (hP : Indep P) (i : I)
      (hz : (coord i).1 = z) (hv : P (coord i).2) : C z P i = 1 := by
    rw [cval z hP i, force (adjCoord i) hP hv, hz]
    simp
  have c_weak (j : ↥A) {P : V → Prop} (hP : Indep P) (hv : P (a j)) :
      C (h j) P (Sum.inr (Sum.inr j)) = 0 := by
    rw [cval _ hP]
    change (if h j = h j ∧ sel (hp.1 j).2.2.1.symm hP = h j then (1 : ℚ) else 0) = 0
    simp [weak_miss j hP hv]
  have base_core (e : E) : base (lose e) (win e) :=
    Or.inl ⟨(winLose e).1,(winLose e).2.2.2⟩
  have base_pref (j : J) : base (h j) (a j) :=
    (star_tip hp (h j) _ j).1.mpr ⟨rfl,not_false⟩
  let B (z : V) := C z (base z)
  let paired (e : E) := pair (lose e) (win e)
  have pind (e : E) : Indep (paired e) :=
    pairInd (winLose e).1 (winLose e).2.2.1 (winLose e).2.2.2
  have incl (e : E) {z : V} (hz : base (lose e) z) (hn : z ≠ win e) : paired e z :=
    ⟨Or.inl hz,(star_adj hp hz).ne.symm,hn⟩
  -- The two columns differ only on the coordinate of the removed edge.
  have edgeUnit (e : E) : Pi.single (Sum.inl e : I) (1 : ℚ) ∈ W := by
    let z := lose e
    have hz := (winLose e).2.2.1
    let D := B z - C z (paired e)
    have hD : D ∈ W := W.sub_mem (cmem z _ hz) (cmem z _ hz)
    apply unit_mem W _ D hD
    · change C z (base z) (Sum.inl e) - C z (paired e) (Sum.inl e) = 1
      rw [c_hit (z := z) (baseInd hz) (Sum.inl e) rfl (base_core e), cval _ (pind e)]
      change 1 - (if z = z ∧ sel (winLose e).1 (pind e) = z then (1 : ℚ) else 0) = 1
      simp [z, loseMiss e]
    · intro i hi
      left
      change C z (base z) i - C z (paired e) i = 0
      by_cases hz' : (coord i).1 = z
      · rcases i with d | w | j
        · change lose d = lose e at hz'
          have hn : win d ≠ win e := by
            intro he
            exact hi (congrArg Sum.inl (sameEdge hz' he))
          have hb : base (lose e) (win d) := hz' ▸ base_core d
          rw [c_hit (baseInd hz) (Sum.inl d) hz' hb,
            c_hit (pind e) (Sum.inl d) hz' (incl e hb hn), sub_self]
        · change w.val = lose e at hz'
          have hb : base (lose e) (anchor w) := hz' ▸ (ha w).1
          rw [c_hit (baseInd hz) (Sum.inr (Sum.inl w)) hz' hb,
            c_hit (pind e) (Sum.inr (Sum.inl w)) hz' (incl e hb ((ha w).2 e hz'.symm)), sub_self]
        · change h j = lose e at hz'
          have hb : base (lose e) (a j) := hz' ▸ base_pref j
          have hn : a j ≠ win e := fun he => (winLose e).2.2.2 ⟨j,Or.inl he⟩
          change C z (base z) (Sum.inr (Sum.inr j)) - C z (paired e) (Sum.inr (Sum.inr j)) = 0
          have eq1 : C z (base z) (Sum.inr (Sum.inr j)) = 0 := by
            rw [← show h j = z from hz']
            exact c_weak j (baseInd (hhub j)) (base_pref j)
          have eq2 : C z (paired e) (Sum.inr (Sum.inr j)) = 0 := by
            exact (congrArg (fun v => C v (paired e) (Sum.inr (Sum.inr j))) hz').symm.trans
              (c_weak j (pind e) (incl e hb hn))
          rw [eq1,eq2,sub_self]
      · rw [c_off (baseInd hz) _ hz', c_off (pind e) _ hz', sub_self]
  have anchorUnit (w : ↥U) : Pi.single (Sum.inr (Sum.inl w) : I) (1 : ℚ) ∈ W := by
    apply unit_mem W _ (B w) (cmem _ _ (hU w))
    · exact c_hit (baseInd (hU w)) _ rfl (ha w).1
    · intro i hi
      rcases i with e | z | j
      · exact Or.inr (edgeUnit e)
      · apply Or.inl
        apply c_off (baseInd (hU w))
        intro eq
        exact hi (congrArg (fun z : ↥U => Sum.inr (Sum.inl z)) (Subtype.ext eq))
      · left
        by_cases eq : h j = w.val
        · change C w.val (base w) (Sum.inr (Sum.inr j)) = 0
          rw [← eq]
          exact c_weak j (baseInd (hhub j)) (base_pref j)
        · exact c_off (baseInd (hU w)) _ eq
  -- Switching one selected tip supplies the extra coordinate for its triangle.
  have weakUnit (j : ↥A) : Pi.single (Sum.inr (Sum.inr j) : I) (1 : ℚ) ∈ W := by
    let P := Star G a b h (h j) (fun k => k = j.val)
    have hP : Indep P := fun _ _ => star_independent hp (hhub j) _
    apply unit_mem W _ (C (h j) P) (cmem _ _ (hhub j))
    · exact c_hit hP _ rfl ((star_tip hp (h j) _ j).2.mpr ⟨rfl,rfl⟩)
    · intro i hi
      rcases i with e | w | k
      · exact Or.inr (edgeUnit e)
      · exact Or.inr (anchorUnit w)
      · left
        by_cases eq : h k = h j
        · have nk : k.val ≠ j.val := fun he =>
            hi (congrArg (fun j : ↥A => Sum.inr (Sum.inr j)) (Subtype.ext he))
          exact eq ▸ c_weak k hP ((star_tip hp (h j) _ k).1.mpr ⟨eq,nk⟩)
        · exact c_off hP _ eq
  have rk : es.card + U.card + A.card ≤ live.card := by
    have bound := rank_bound R (fun i => by
      rcases i with e | w | j
      · exact edgeUnit e
      · exact anchorUnit w
      · exact weakUnit j)
    simpa only [I,E,Fintype.card_sum,Fintype.card_coe,Nat.add_assoc] using bound
  let S := U ∪ Finset.univ.image a
  have ma (j : J) : a j ∈ S := Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have mh (j : J) : h j ∈ S := Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have cut : CoverPromise.IsVertexCover G S := by
    intro v w e
    by_cases hv : Tip a b v
    · rcases hv with ⟨j,eq | eq⟩
      · exact Or.inl (eq ▸ ma j)
      · subst v
        rcases ((hp.1 j).2.2.2.2 w).mp e with rfl | rfl
        · exact Or.inr (ma j)
        · exact Or.inr (mh j)
    by_cases hw : Tip a b w
    · rcases hw with ⟨j,eq | eq⟩
      · exact Or.inr (eq ▸ ma j)
      · subst w
        rcases ((hp.1 j).2.2.2.2 v).mp e.symm with rfl | rfl
        · exact Or.inl (ma j)
        · exact Or.inl (mh j)
    have em : Sym2.mk v w ∈ es := Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr e,
      fun z hz => by rcases Sym2.mem_iff.mp hz with rfl | rfl; exact hv; exact hw⟩
    let d : E := ⟨Sym2.mk v w,em⟩
    have hwin : win d ∈ S := Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
    rcases Sym2.eq_iff.mp (winLose d).2.1 with ⟨_,q⟩ | ⟨_,q⟩
    · exact Or.inr (q ▸ hwin)
    · exact Or.inl (q ▸ hwin)
  have cover_le : t ≤ U.card + Fintype.card J := by
    have le := hmin S cut
    change t ≤ (U ∪ Finset.univ.image a).card at le
    have u := Finset.card_union_le U (Finset.univ.image a)
    have ac : (Finset.univ.image a).card ≤ Fintype.card J := by
      exact Finset.card_image_le.trans_eq (Finset.card_univ (α := J))
    omega
  have edge_le : G.edgeFinset.card ≤ es.card + 3 * Fintype.card J :=
    edge_count G hp es (by ext e; simp only [es, Finset.mem_filter])
  have low_le : 4 * Fintype.card J ≤
      A.card + (Finset.univ.filter (fun i => Tip a b (label i))).card :=
    tip_slots hp label slots (fun _ => rfl) A
    (fun j => by have pos := slot_pos (hp.1 j).1; have hs := hstrong j; dsimp [weak] at hs; omega)
    (fun j => by
      have pos := slot_pos (hp.1 j).1.symm
      split_ifs with hj
      · exact pos
      · have nw : (slots (b j)).card ≠ 1 := fun eq => hj ((weakB j).mpr eq)
        omega)
  have split := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin φ.leaves))) (fun i => Tip a b (label i))
  change _ + live.card = _ at split
  rw [Finset.card_univ, Fintype.card_fin] at split
  omega

end PEqualNP.Outside.L_meta_252

theorem PEqualNP.Outside.L_meta_252 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t s : ℕ), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj a c → ((Finset.univ.filter (G.Adj a)).card = 2 ∧ (Finset.univ.filter (G.Adj b)).card = 2) ∨ ((Finset.univ.filter (G.Adj a)).card = 2 ∧ (Finset.univ.filter (G.Adj c)).card = 2) ∨ ((Finset.univ.filter (G.Adj b)).card = 2 ∧ (Finset.univ.filter (G.Adj c)).card = 2)) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → ((∃ φ : PEqualNP.MetaComplexity.DMFormula n, φ.leaves ≤ s ∧ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ ∧ ∀ x : Fin n → Bool, (φ.eval x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) ↔ G.edgeFinset.card + t ≤ s) := by
  intro n G _ t s he hsq htri ⟨T,hT,hcard⟩ hmin
  constructor
  · rintro ⟨φ,hsize,hm,hf⟩
    exact (PEqualNP.Outside.L_meta_252.lower G hsq htri t hmin φ hm hf).trans hsize
  · intro hs
    obtain ⟨φ,hle,hm,hf⟩ := PEqualNP.Outside.L_meta_252.upper G he T hT
    rw [hcard] at hle
    exact ⟨φ,hle.trans hs,hm,hf⟩
