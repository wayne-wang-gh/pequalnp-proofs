import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_885

open PEqualNP.CircuitLowerBounds

abbrev CountHyp := (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size)

abbrev ReduceHyp := (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)))


theorem stable_base {n t k : ℕ} {J : Type*} [Fintype J]
    (hJ : Fintype.card J ≤ t) (act : Finset (Fin n) → Finset J) (ha : Monotone act) :
    ∃ Y : Finset (Fin n), Y.card ≤ (act Y).card*k ∧
      (act Y).card ≤ t ∧
      (∀ U : Finset (Fin n), U.card ≤ k → act (Y ∪ U) = act Y) ∧
      ((act Y).card = t → ∀ U : Finset (Fin n), act (Y ∪ U) = act Y) := by
  classical
  let P := Finset.univ.filter (fun Y : Finset (Fin n) => Y.card ≤ (act Y).card*k)
  have hP : P.Nonempty := ⟨∅,by simp [P]⟩
  obtain ⟨Y,hY,maximal⟩ := Finset.exists_max_image P (fun Y => (act Y).card) hP
  have hy : Y.card ≤ (act Y).card*k := (Finset.mem_filter.mp hY).2
  refine ⟨Y,hy,(Finset.card_le_univ _).trans hJ,?_,?_⟩
  · intro U hu
    have hsub : act Y ⊆ act (Y ∪ U) := ha Finset.subset_union_left
    by_contra hne
    have grow : (act Y).card+1 ≤ (act (Y ∪ U)).card := Finset.card_lt_card (hsub.ssubset_of_ne (Ne.symm hne))
    have had : Y.card + k ≤ (act (Y ∪ U)).card*k := by
      calc Y.card+k ≤ (act Y).card*k+k := Nat.add_le_add_right hy k
           _ = ((act Y).card+1)*k := by simp [Nat.add_mul]
           _ ≤ _ := Nat.mul_le_mul_right _ grow
    have hv : Y ∪ U ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.card_union_le _ _).trans ((Nat.add_le_add_left hu _).trans had)⟩
    have hmax := maximal (Y ∪ U) hv
    omega
  · intro hall U
    exact (Finset.eq_of_subset_of_card_le (ha Finset.subset_union_left)
      ((Finset.card_le_univ _).trans (hJ.trans hall.ge))).symm

theorem linesHit {n m q : ℕ} (F : Fin m → Finset (Fin n))
    (reg : ∀ p : Fin n,(Finset.univ.filter (fun i : Fin m => p ∈ F i)).card = q+1)
    (pair : ∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ F i ∧ v ∈ F i)
    (Y : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin m => ¬ Disjoint Y (F i))).card ≤ q*Y.card+1 := by
  classical
  let lines (p : Fin n) := Finset.univ.filter (fun i : Fin m => p ∈ F i)
  have aux (A : Finset (Fin n)) : (A.biUnion lines).card ≤ q*A.card+1 := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert p A hp ih =>
      rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hp,Nat.mul_add,Nat.mul_one]
      cases A.eq_empty_or_nonempty with
      | inl h => subst A; simpa [lines] using (reg p).le
      | inr h =>
        obtain ⟨r,hr⟩ := h
        have hpr : p ≠ r := fun eq => hp (eq ▸ hr)
        obtain ⟨i,hpi,hri⟩ := pair p r hpr
        have hi : i ∈ lines p ∩ A.biUnion lines := Finset.mem_inter.mpr
          ⟨by simpa [lines] using hpi,Finset.mem_biUnion.mpr ⟨r,hr,by simpa [lines] using hri⟩⟩
        have hpos : 0 < (lines p ∩ A.biUnion lines).card := Finset.card_pos.mpr ⟨i,hi⟩
        have hu := Finset.card_union_add_card_inter (lines p) (A.biUnion lines)
        have hcnt : (lines p).card = q+1 := reg p
        omega
  apply le_trans _ (aux Y)
  apply Finset.card_le_card
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨p,hp,hpi⟩ := h
  exact Finset.mem_biUnion.mpr ⟨p,hp,by simpa [lines] using hpi⟩

def run (L : List Gate) (W : List Bool) := (Circuit.mk L 0).wires W

def read (L : List Gate) (j : ℕ) (g : Gate) (W : List Bool) :=
  (g.inputs.map (fun i => (run (L.take j) W).getD i false)).headD false

def literal (b : Bool) : Gate := if b then ⟨GateOp.and,[]⟩ else ⟨GateOp.or,[]⟩

noncomputable def freeze (L : List Gate) (B : List Bool) : List Gate := by
  classical
  exact L.mapIdx (fun j (g : Gate) =>
    if g.op = GateOp.not then literal (!(read L j g B)) else g)

theorem freeze_arity (L : List Gate) (B : List Bool)
    (hf : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ freeze L B, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
  have hj' : j < L.length := by simpa [freeze] using (List.getElem?_eq_some_iff.mp hj).1
  have he := (List.getElem?_eq_some_iff.mp hj).2
  simp only [freeze,List.getElem_mapIdx] at he
  rw [←he]
  rcases hf L[j] (List.getElem_mem hj') with ⟨hop,hlen⟩
  split_ifs with hn
  · cases b : read L j L[j] B <;> simp [literal]
  · exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun h => (hn h).elim)),hlen⟩

theorem freeze_correct (L : List Gate) (B W : List Bool)
    (stable : ∀ j g, L[j]? = some g → g.op = GateOp.not → read L j g W = read L j g B) :
    run (freeze L B) W = run L W := by
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have allp (j : ℕ) (hj : j ≤ L.length) :
      ((freeze L B).take j).foldl step W = (L.take j).foldl step W := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j < L.length := hj
      have hjf : j < (freeze L B).length := by simpa [freeze] using hj'
      rw [List.take_succ_eq_append_getElem hjf,List.take_succ_eq_append_getElem hj',
        List.foldl_append,List.foldl_append,ih hj'.le]
      simp only [List.foldl_cons,List.foldl_nil,freeze,List.getElem_mapIdx]
      split_ifs with h
      · have hh := stable j L[j] (List.getElem?_eq_getElem hj') h
        dsimp [step]
        change _ ++ [_] = _ ++ [L[j].op.eval _]
        rw [h]
        change _ ++ [_] = _ ++ [!(read L j L[j] W)]
        rw [hh]
        cases b : read L j L[j] B <;> simp [literal,GateOp.eval]
      · rfl
  have hf : (freeze L B).length = L.length := by simp [freeze]
  have h := allp L.length le_rfl
  rw [←hf,List.take_length,hf,List.take_length] at h
  exact h

def bit {n : ℕ} (X : Finset (Fin n)) (i : Fin n) := decide (i ∈ X)
def supp {n : ℕ} (x : Fin n → Bool) := Finset.univ.filter (fun p => x p = true)
def untouched {n m : ℕ} (F : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) :=
  Finset.univ.filter (fun i => Disjoint Y (F i))

theorem local_count (hc : CountHyp) (hr : ReduceHyp) {n m q k : ℕ}
    (hk : 1 ≤ k) (hq : 1 ≤ q) (F : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (hs : ∀ i, (F i).card=q+1) (hd : ∀ i j, i≠j → (F i ∩ F j).card ≤ 1)
    (L : List Gate) (out : Fin m → ℕ)
    (ha : ∀ g ∈ L, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length ≤ 2)
    (win : ∀ i (X : Finset (Fin n)), X.card ≤ k → Circuit.eval ⟨L,out i⟩ (List.ofFn (bit (Y∪X))) =
      decide (∃ p ∈ F i, p ∈ Y∪X)) :
    (untouched F Y).card * min k q ≤ L.length := by
  classical
  let I := untouched F Y
  let e : Fin I.card ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
  obtain ⟨D,r,hD,hsize,respond⟩ := hr n L Y ∅ ha
  let newF (i : Fin I.card) := F (e i).val
  let newO (i : Fin I.card) := r (out (e i).val)
  have hdis (i : Fin I.card) : Disjoint Y (newF i) := (Finset.mem_filter.mp (e i).property).2
  have align (x : Fin n → Bool) :
      (fun i => if i ∈ Y then true else if i ∈ (∅ : Finset (Fin n)) then false else x i) =
      bit (Y ∪ supp x) := by
    funext p
    by_cases h : p ∈ Y <;> cases hx : x p <;> simp [bit,supp,h,hx]
  have answer (i : Fin I.card) (x : Fin n → Bool) (hx : (supp x).card ≤ k) :
      Circuit.eval ⟨L,out (e i).val⟩ (List.ofFn (bit (Y∪supp x))) =
      decide (∃ p ∈ newF i, x p = true) := by
    rw [win _ _ hx]
    congr 1
    apply propext
    constructor
    · rintro ⟨p,hp,hu⟩
      rcases Finset.mem_union.mp hu with hy | hb
      · exact (Finset.disjoint_left.mp (hdis i) hy hp).elim
      · exact ⟨p,hp,(Finset.mem_filter.mp hb).2⟩
    · rintro ⟨p,hp,hb⟩
      exact ⟨p,hp,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)⟩
  have emptyS : supp (fun _ : Fin n => false) = ∅ := by ext; simp [supp]
  have singS (p : Fin n) : supp (fun a => decide (a=p)) = {p} := by ext; simp [supp]
  have live (i : Fin I.card) : ∃ x y : Fin n → Bool,
      Circuit.eval ⟨L,out (e i).val⟩ (List.ofFn (fun p => if p ∈ Y then true else if p ∈ (∅ : Finset (Fin n)) then false else x p)) ≠
      Circuit.eval ⟨L,out (e i).val⟩ (List.ofFn (fun p => if p ∈ Y then true else if p ∈ (∅ : Finset (Fin n)) then false else y p)) := by
    have hcard : (newF i).card = q+1 := hs _
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (newF i).card by omega)
    refine ⟨fun _ => false,fun a => decide (a=p),?_⟩
    rw [align,align,answer i _ (by simp [emptyS]),answer i _ (by simpa [singS] using hk)]
    simp [hp]
  have result (i : Fin I.card) (x : Fin n → Bool) (hx : (supp x).card ≤ k) :
      Circuit.eval ⟨D,newO i⟩ (List.ofFn x) = decide (∃ p ∈ newF i, x p = true) := by
    rw [show Circuit.eval ⟨D,newO i⟩ (List.ofFn x) = _ from respond _ (live i) x,align,answer i x hx]
  have bound := hc n I.card k newF ⟨D,0⟩ newO (fun _ => min k q)
    (fun i j hij => hd _ _ (fun eq => hij (e.injective (Subtype.ext eq))))
    (fun i => by change 2 ≤ (F _).card; rw [hs]; omega) hD
    (fun i p => by
      change Circuit.eval ⟨D,newO i⟩ _ = true ↔ _
      rw [result i _ (by simpa [singS] using hk)]
      simp)
    (fun i x hx hnone => by
      change Circuit.eval ⟨D,newO i⟩ _ = false
      rw [result i x hx]
      simpa using hnone)
    (fun _ => min_le_left _ _) (fun i => by
      change min k q+1 ≤ (F _).card
      rw [hs]
      omega)
  simpa [I,Circuit.size] using le_trans bound hsize


end PEqualNP.Outside.L_meta_885

open PEqualNP.Outside.L_meta_885 PEqualNP.CircuitLowerBounds in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.L_meta_885 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (nP mL qO : ℕ) (Fam : Fin mL → Finset (Fin nP)), (∀ i1 : Fin mL, (Fam i1).card = qO + 1) → (∀ i7 i8 : Fin mL, i7 ≠ i8 → (Fam i7 ∩ Fam i8).card ≤ 1) → (∀ p1 p2 : Fin nP, p1 ≠ p2 → ∃ i3 : Fin mL, p1 ∈ Fam i3 ∧ p2 ∈ Fam i3) → (∀ p3 : Fin nP, (Finset.univ.filter (fun i4 : Fin mL => p3 ∈ Fam i4)).card = qO + 1) → ∀ (tN kW : ℕ) (L : List PEqualNP.CircuitLowerBounds.Gate) (outW : Fin mL → ℕ), 1 ≤ tN → 1 ≤ kW → (∀ g1 ∈ L, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g1.inputs.length ≤ 2) → Set.ncard {i5 : Fin L.length | (L.get i5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ tN → (∀ (j1 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), L[j1]? = some g2 → g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun x1 : Fin nP → Bool => (g2.inputs.map (fun i6 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L.take j1, 0⟩ (List.ofFn x1)).getD i6 false)).headD false)) → (∀ (w1 : Fin mL) (x2 : Fin nP → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L, outW w1⟩ (List.ofFn x2) = decide (∃ v1 ∈ Fam w1, x2 v1 = true)) → ∀ Kb : ℕ, ((tN = 1 ∧ Kb ≤ kW * mL ∧ Kb ≤ qO * mL) ∨ (Kb + kW * (tN * kW * qO + 1) ≤ kW * mL + kW * kW * qO ∧ Kb + qO * (tN * kW * qO + 1) ≤ qO * mL + qO * kW * qO)) → Kb + qO * (tN * kW * qO + 1) ≤ qO * mL → Kb ≤ L.length := by
  classical
  intro hc hr n m q F hs hd pair reg t k L out ht hk hgate hnum hmon hout K hcase hfinal
  by_cases hq : 1 ≤ q
  swap
  · have h : q=0 := by omega
    simpa [h] using (le_trans (show K ≤ K + q * (t * k * q + 1) by omega) hfinal |>.trans (show q*m ≤ L.length by simp [h]))
  let N : Set (Fin L.length) := { i | (L.get i).op = GateOp.not }
  let J := ↥N
  have hj : Fintype.card J ≤ t := by
    change N.ncard ≤ t at hnum
    exact (Set.fintypeCard_eq_ncard N).le.trans hnum
  let act (X : Finset (Fin n)) : Finset J := Finset.univ.filter
    (fun a : J => read L a.val.val (L.get a.val) (List.ofFn (bit X)) = true)
  have mono : Monotone act := by
    intro X Z hXZ a ha
    have ha' := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hle : bit X ≤ bit Z := by
      intro p
      by_cases hx : p ∈ X
      · simp [bit,hx,hXZ hx]
      · simp [bit,hx]
    have hm := hmon a.val.val (L.get a.val) (List.getElem?_eq_getElem a.val.isLt) a.property hle
    change read L _ _ (List.ofFn (bit X)) ≤ read L _ _ (List.ofFn (bit Z)) at hm
    rw [ha'] at hm
    exact Bool.eq_true_of_true_le hm
  obtain ⟨Y,hy,hdim,hstable,hglobal⟩ := stable_base hj act mono
  let good := (untouched F Y).card
  have price (a : ℕ) (ha : 1 ≤ a) (hwin : ∀ X : Finset (Fin n), X.card ≤ a → act (Y∪X) = act Y) :
      good * min a q ≤ L.length := by
    let B := List.ofFn (bit Y)
    have hfix (X : Finset (Fin n)) (hx : X.card ≤ a) :
        run (freeze L B) (List.ofFn (bit (Y∪X))) = run L (List.ofFn (bit (Y∪X))) := by
      apply freeze_correct
      intro j g hg hn
      obtain ⟨hj,rfl⟩ := List.getElem?_eq_some_iff.mp hg
      let ix : J := ⟨⟨j,hj⟩,hn⟩
      have same : ix ∈ act (Y∪X) ↔ ix ∈ act Y := by rw [hwin X hx]
      simp only [act,Finset.mem_filter,Finset.mem_univ,true_and] at same
      exact Bool.eq_iff_iff.mpr same
    have H := local_count hc hr ha hq F Y hs hd (freeze L B) out (freeze_arity L B hgate) (by
      intro i X hx
      change (run (freeze L B) _).getD _ _ = _
      rw [hfix X hx]
      simpa [Circuit.eval,Circuit.wires,run,bit] using hout i (bit (Y∪X)))
    simpa [good,freeze] using H
  let hit := (Finset.univ.filter (fun i : Fin m => ¬ Disjoint Y (F i))).card
  have splitm : good + hit = m := by
    simpa [good,hit,untouched] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m))) (fun i => Disjoint Y (F i)))
  have hitb : hit ≤ q*Y.card+1 := linesHit F reg pair Y
  by_cases full : (act Y).card = t
  · have cheap := price q hq (fun X _ => hglobal full X)
    rw [min_self] at cheap
    have hY := Nat.mul_le_mul_left q (hy.trans (Nat.mul_le_mul_right k hdim))
    have hh : hit ≤ t*k*q+1 := by nlinarith only [hitb,hY]
    have hcost := Nat.mul_le_mul_left q hh
    have he : q*m = q*good + q*hit := by rw [←splitm,Nat.mul_add]
    nlinarith only [hfinal,cheap,hcost,he]
  have hlt : (act Y).card + 1 ≤ t := by omega
  have cheap := price k hk hstable
  rcases hcase with ⟨ht1,hkm,hqm⟩ | ⟨hkm,hqm⟩
  · have hz : (act Y).card = 0 := by omega
    have hY : Y=∅ := Finset.card_eq_zero.mp (by simpa [hz] using hy)
    have hg : good = m := by simp [good,untouched,hY]
    rw [hg] at cheap
    rcases le_total k q with h | h
    · rw [min_eq_left h] at cheap
      simpa [Nat.mul_comm] using hkm.trans (by simpa [Nat.mul_comm] using cheap)
    · rw [min_eq_right h] at cheap
      exact hqm.trans (by simpa [Nat.mul_comm] using cheap)
  · have hY : Y.card+k ≤ t*k := by
      calc Y.card+k ≤ (act Y).card*k+k := Nat.add_le_add_right hy k
           _ = ((act Y).card+1)*k := by simp [Nat.add_mul]
           _ ≤ _ := Nat.mul_le_mul_right k hlt
    have hqY := Nat.mul_le_mul_right q hY
    have hh : hit+k*q ≤ t*k*q+1 := by nlinarith only [hitb,hqY]
    have finish (b : ℕ) (hbound : K+b*(t*k*q+1) ≤ b*m+b*k*q) (hp : good*b ≤ L.length) : K ≤ L.length := by
      have hscaled := Nat.mul_le_mul_left b hh
      have he : b*m = b*good+b*hit := by rw [←splitm,Nat.mul_add]
      nlinarith only [hbound,hp,hscaled,he]
    rcases le_total k q with h | h
    · rw [min_eq_left h] at cheap
      exact finish k hkm cheap
    · rw [min_eq_right h] at cheap
      exact finish q hqm cheap
