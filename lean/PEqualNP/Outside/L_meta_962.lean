import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_962

-- The circuit evaluation argument follows the checked L-meta-906 and L-meta-634.
namespace MoonPrize.Core

theorem card_add_card_le_union_add_inter {α : Type*} [DecidableEq α]
    (S D U : Finset α) (hDU : D ⊆ U)
    (h : ((S ∩ U) ∪ D).card ≤ S.card) :
    U.card + D.card ≤ (U ∪ S).card + (D ∩ S).card := by
  have h1 := Finset.card_union_add_card_inter U S
  have h2 := Finset.card_union_add_card_inter (S ∩ U) D
  have h3 : (S ∩ U) ∩ D = D ∩ S := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hs, _⟩, hd⟩
      exact ⟨hd, hs⟩
    · rintro ⟨hd, hs⟩
      exact ⟨⟨hs, hDU hd⟩, hd⟩
  have h4 : U ∩ S = S ∩ U := Finset.inter_comm U S
  rw [h3] at h2
  rw [h4] at h1
  omega

def Independent {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v ∈ S, ∀ w ∈ S, ¬G.Adj v w

def common {V : Type*} [DecidableEq V] (W : Finset V) (F : Finset (Finset V)) : Finset V :=
  W.filter (fun v => ∀ A ∈ F, v ∈ A)

theorem mem_common {V : Type*} [DecidableEq V] (W : Finset V) (F : Finset (Finset V)) (v : V) :
    v ∈ common W F ↔ v ∈ W ∧ ∀ A ∈ F, v ∈ A := by
  simp [common]

theorem hajnal {V : Type*} [DecidableEq V] (G : SimpleGraph V) (W : Finset V) (k : ℕ)
    (cap : ∀ S ⊆ W, Independent G S → S.card ≤ k) (F : Finset (Finset V))
    (ne : F.Nonempty) (full : ∀ S ∈ F, S ⊆ W ∧ Independent G S ∧ S.card = k) :
    2*k ≤ (F.biUnion id).card + (common W F).card := by
  classical
  induction F using Finset.induction_on with
  | empty => simp at ne
  | @insert S F hnot ih =>
    obtain ⟨sub,ind,sz⟩ := full S (Finset.mem_insert_self _ _)
    have rest (A) (h : A ∈ F) := full A (Finset.mem_insert_of_mem h)
    by_cases hF : F.Nonempty
    · have old := ih hF rest
      let U := F.biUnion id
      let D := common W F
      have memD {v} (hv : v ∈ D) (A) (ha : A ∈ F) : v ∈ A :=
        (Finset.mem_filter.mp hv).2 A ha
      have du : D ⊆ U := by
        intro v hv
        obtain ⟨A,ha⟩ := hF
        exact Finset.mem_biUnion.mpr ⟨A,ha,memD hv A ha⟩
      have dw : D ⊆ W := fun _ h => (Finset.mem_filter.mp h).1
      have oldD : Independent G D := by
        obtain ⟨A,ha⟩ := hF
        intro v hv w hw
        exact (rest A ha).2.1 v (memD hv A ha) w (memD hw A ha)
      have cross {v w} (hv : v ∈ U) (hw : w ∈ D) : ¬ G.Adj v w := by
        obtain ⟨A,ha,hv⟩ := Finset.mem_biUnion.mp hv
        exact (rest A ha).2.1 v hv w (memD hw A ha)
      have hybrid : Independent G ((S ∩ U) ∪ D) := by
        intro v hv w hw
        rcases Finset.mem_union.mp hv with hv|hv <;> rcases Finset.mem_union.mp hw with hw|hw
        · exact ind _ (Finset.mem_inter.mp hv).1 _ (Finset.mem_inter.mp hw).1
        · exact cross (Finset.mem_inter.mp hv).2 hw
        · exact fun adj => cross (Finset.mem_inter.mp hw).2 hv adj.symm
        · exact oldD _ hv _ hw
      have subs : (S ∩ U) ∪ D ⊆ W := Finset.union_subset
        (fun _ h => sub (Finset.mem_inter.mp h).1) dw
      have bound := card_add_card_le_union_add_inter S D U du (sz ▸ cap _ subs hybrid)
      have hi : common W (insert S F) = D ∩ S := by
        ext x
        simp [common,D]
        tauto
      rw [hi,Finset.biUnion_insert,Finset.union_comm]
      exact old.trans bound
    · have empty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      subst F
      have eq : common W {S} = S := by
        ext x
        simp [common]
        exact fun hx => sub hx
      change 2*k ≤ (({S} : Finset (Finset V)).biUnion id).card + (common W {S}).card
      rw [Finset.singleton_biUnion,eq]
      change 2*k ≤ S.card + S.card
      rw [sz]
      omega

def Hard {V : Type*} (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ A ⊆ W, Independent G A → A.card + 5 ≤ W.card

theorem small_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (cover : ∀ T : Finset V, (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 5 ≤ T.card) :
    ∃ W : Finset V, Hard G W ∧ W.card ≤ 10 ∧
      ∀ v ∈ W, ∃ A ⊆ W, Independent G A ∧ v ∉ A ∧ A.card + 5 = W.card := by
  classical
  have hu : Hard G Finset.univ := by
    intro A _ ai
    have hc := cover (Finset.univ \ A) (by
      intro v w adj
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
      by_cases hv : v ∈ A
      · exact Or.inr (fun hw => ai v hv w hw adj)
      · exact Or.inl hv)
    have eq := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    omega
  let pool := Finset.univ.filter (Hard G)
  have existsW : pool.Nonempty :=
    ⟨Finset.univ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩
  obtain ⟨W,hw,minimal⟩ := Finset.exists_min_image pool Finset.card existsW
  have hard : Hard G W := (Finset.mem_filter.mp hw).2
  have five : 5 ≤ W.card := by
    simpa using hard ∅ (Finset.empty_subset _) (by simp [Independent])
  have exclude (v) (hv : v ∈ W) :
      ∃ A ⊆ W, Independent G A ∧ v ∉ A ∧ A.card + 5 = W.card := by
    have nh : ¬Hard G (W.erase v) := by
      intro h
      have hm := minimal (W.erase v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have sz := Finset.card_erase_of_mem hv
      omega
    unfold Hard at nh
    push Not at nh
    obtain ⟨A,sub,ind,lt⟩ := nh
    have subW := sub.trans (Finset.erase_subset _ _)
    have up := hard A subW ind
    have sz := Finset.card_erase_of_mem hv
    exact ⟨A,subW,ind,(fun ha => Finset.notMem_erase _ _ (sub ha)),by omega⟩
  let k := W.card - 5
  let F := W.powerset.filter (fun A => Independent G A ∧ A.card = k)
  have rows (A) (ha : A ∈ F) : A ⊆ W ∧ Independent G A ∧ A.card = k := by
    obtain ⟨sub,ii,sz⟩ := Finset.mem_filter.mp ha
    exact ⟨Finset.mem_powerset.mp sub,ii,sz⟩
  have except (v) (hv : v ∈ W) : ∃ A ∈ F, v ∉ A := by
    obtain ⟨A,sub,ind,no,sz⟩ := exclude v hv
    exact ⟨A,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr sub,ind,by dsimp [k]; omega⟩,no⟩
  have someRow : F.Nonempty := by
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
    obtain ⟨A,hA,_⟩ := except v hv
    exact ⟨A,hA⟩
  have none : common W F = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hw,all⟩ := (mem_common W F v).mp hv
    obtain ⟨A,hA,ha⟩ := except v hw
    exact ha (all A hA)
  have cap (A) (ha : A ⊆ W) (h : Independent G A) : A.card ≤ k := by
    have := hard A ha h
    dsimp [k]; omega
  have h := hajnal G W k cap F someRow rows
  rw [none,Finset.card_empty,Nat.add_zero] at h
  have unionW : F.biUnion id ⊆ W := by
    intro v hv
    obtain ⟨A,ha,hv⟩ := Finset.mem_biUnion.mp hv
    exact (rows A ha).1 hv
  have upper := Finset.card_le_card unionW
  dsimp [k] at h
  exact ⟨W,hard,by omega,exclude⟩

end MoonPrize.Core

namespace MoonPrize.Projection

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  congr 1
  apply propext
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem sideTrue_mono {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

theorem fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      apply ih
      have : j.val < i.val := hji
      omega
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

theorem gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := fuel_succ C U C.size i i.isLt
  exact h.symm

def raw {n} (C : AndCountCircuit n) (i : Fin C.size) (s : Bool) :=
  cond s (C.rightVars i) (C.leftVars i)

def refs {n} (C : AndCountCircuit n) (i : Fin C.size) (s : Bool) :=
  cond s (C.rightGates i) (C.leftGates i)

def supportFuel {n} (C : AndCountCircuit n) (s : Fin C.size → Bool) :
    ℕ → Fin C.size → Finset (Fin n)
  | 0, _ => ∅
  | d+1, i => raw C i (s i) ∪ ((refs C i (s i)).filter (· < i)).biUnion (supportFuel C s d)

def support {n} (C : AndCountCircuit n) (s : Fin C.size → Bool) : Finset (Fin n) :=
  C.outVars ∪ C.outGates.biUnion (supportFuel C s C.size)

def choice {n} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue X (C.leftVars i) (C.leftGates i) i (C.gateVal X)

lemma side_fuel {n} (C : AndCountCircuit n) (s : Fin C.size → Bool) (X : Finset (Fin n)) :
    ∀ d (i : Fin C.size), C.gateValFuel X d i = true →
      ∃ v ∈ supportFuel C s d i, v ∈ X := by
  intro d
  induction d with
  | zero => simp [gateValFuel]
  | succ d ih =>
    intro i hg
    have both := Bool.and_eq_true_iff.mp hg
    have sel : sideTrue X (raw C i (s i)) (refs C i (s i)) i (C.gateValFuel X d) = true := by
      cases h : s i <;> simp only [raw,refs,Bool.cond_false,Bool.cond_true] <;> first | exact both.1 | exact both.2
    rcases (sideTrue_iff ..).mp sel with ⟨v,hv,hx⟩ | ⟨j,hj,lt,hg⟩
    · exact ⟨v, Finset.mem_union_left _ hv, hx⟩
    · obtain ⟨v,hv,hx⟩ := ih j hg
      exact ⟨v, Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j,Finset.mem_filter.mpr ⟨hj,lt⟩,hv⟩), hx⟩

lemma hit {n} (C : AndCountCircuit n) (s : Fin C.size → Bool) (X : Finset (Fin n))
    (h : C.eval X = true) : ∃ v ∈ support C s, v ∈ X := by
  rw [eval,decide_eq_true_eq] at h
  rcases h with ⟨v,hv,hx⟩ | ⟨i,hi,hg⟩
  · exact ⟨v,Finset.mem_union_left _ hv,hx⟩
  · obtain ⟨v,hv,hx⟩ := side_fuel C s X C.size i hg
    exact ⟨v,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,hv⟩),hx⟩

lemma chosen_blocked {n} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size)
    (off : C.gateVal X i = false) :
    sideTrue X (raw C i (choice C X i)) (refs C i (choice C X i)) i (C.gateVal X) = false := by
  rw [gateVal_rec] at off
  cases h : sideTrue X (C.leftVars i) (C.leftGates i) i (C.gateVal X) <;>
    simp [choice,raw,refs,h] at off ⊢
  exact off

lemma avoid_fuel {n} (C : AndCountCircuit n) (X : Finset (Fin n)) :
    ∀ d (i : Fin C.size), C.gateVal X i = false →
      ∀ v ∈ supportFuel C (choice C X) d i, v ∉ X := by
  intro d
  induction d with
  | zero => simp [supportFuel]
  | succ d ih =>
    intro i off v hv hx
    have blocked := chosen_blocked C X i off
    rw [← Bool.not_eq_true,sideTrue_iff] at blocked
    rcases Finset.mem_union.mp hv with a|a
    · exact blocked (Or.inl ⟨v,a,hx⟩)
    · obtain ⟨j,hj,hv⟩ := Finset.mem_biUnion.mp a
      obtain ⟨mem,lt⟩ := Finset.mem_filter.mp hj
      have no : C.gateVal X j = false := Bool.eq_false_iff.mpr (fun yes =>
        blocked (Or.inr ⟨j,mem,lt,yes⟩))
      exact ih j no v hv hx

lemma avoid {n} (C : AndCountCircuit n) (X : Finset (Fin n)) (h : C.eval X = false) :
    ∀ v ∈ support C (choice C X), v ∉ X := by
  rw [← Bool.not_eq_true,eval,decide_eq_true_eq] at h
  intro v hv hx
  rcases Finset.mem_union.mp hv with b|b
  · exact h (Or.inl ⟨v,b,hx⟩)
  · obtain ⟨i,mem,hv⟩ := Finset.mem_biUnion.mp b
    have no : C.gateVal X i = false := Bool.eq_false_iff.mpr (fun yes => h (Or.inr ⟨i,mem,yes⟩))
    exact avoid_fuel C X C.size i no v hv hx

theorem exact_certificate {n} (C : AndCountCircuit n) (X : Finset (Fin n)) (off : C.eval X = false)
    (on : ∀ v, v ∉ X → C.eval (insert v X) = true) :
    support C (choice C X) = Finset.univ \ X := by
  ext v
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
  constructor
  · exact avoid C X off v
  · intro hv
    obtain ⟨w,hw,hmem⟩ := hit C (choice C X) _ (on v hv)
    rcases Finset.mem_insert.mp hmem with rfl|hx
    · exact hw
    · exact (avoid C X off w hw hx).elim

end MoonPrize.Projection
namespace MoonPrize.Core

def Dominates {V : Type*} (G : SimpleGraph V) (W J : Finset V) : Prop :=
  ∀ u ∈ W, u ∉ J → ∃ v ∈ J, G.Adj u v

lemma maximal_extension {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (J : Finset V) (ind : Independent G J) :
    ∃ I : Finset V, J ⊆ I ∧ Independent G I ∧ ∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v := by
  classical
  let pool := Finset.univ.filter (fun I : Finset V => J ⊆ I ∧ Independent G I)
  have hj : J ∈ pool := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Subset.rfl, ind⟩
  obtain ⟨I,hI,maximal⟩ := Finset.exists_max_image pool Finset.card ⟨J,hj⟩
  obtain ⟨sub,ii⟩ := (Finset.mem_filter.mp hI).2
  refine ⟨I,sub,ii,?_⟩
  intro u hu
  by_contra! no
  have good : Independent G (insert u I) := by
    intro v hv w hw
    rcases Finset.mem_insert.mp hv with a|av <;> rcases Finset.mem_insert.mp hw with b|bw
    · rw [a,b]; exact G.loopless.irrefl _
    · rw [a]; exact no _ bw
    · rw [b]; exact fun edge => no _ av edge.symm
    · exact ii _ av _ bw
  have more := maximal (insert u I) (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,sub.trans (Finset.subset_insert _ _),good⟩)
  rw [Finset.card_insert_of_notMem hu] at more
  omega

lemma project_rows {n : ℕ} (G : SimpleGraph (Fin n)) (C : PEqualNP.AndCount.AndCountCircuit n)
    (promise : ∀ I : Finset (Fin n), Independent G I →
      (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true)
    (W J : Finset (Fin n)) (sub : J ⊆ W) (ind : Independent G J) (maxJ : Dominates G W J) :
    ∃ s : Fin C.size → Bool, W \ MoonPrize.Projection.support C s = J := by
  classical
  obtain ⟨I,ji,ii,maxI⟩ := maximal_extension G J ind
  obtain ⟨neg,pos⟩ := promise I ii maxI
  refine ⟨MoonPrize.Projection.choice C I,?_⟩
  rw [MoonPrize.Projection.exact_certificate C I neg pos]
  ext v
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not]
  constructor
  · rintro ⟨hw,hi⟩
    by_contra absent
    obtain ⟨u,hu,edge⟩ := maxJ v hw absent
    exact ii v hi u (ji hu) edge
  · exact fun h => ⟨sub h,ji h⟩

lemma bare_output_empty {n : ℕ} (G : SimpleGraph (Fin n)) (C : PEqualNP.AndCount.AndCountCircuit n)
    (promise : ∀ I : Finset (Fin n), Independent G I →
      (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) : C.outVars = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have sing : Independent G {v} := by
    simp [Independent]
  obtain ⟨I,ji,ii,maxI⟩ := maximal_extension G {v} sing
  have off := (promise I ii maxI).1
  have hit : v ∈ MoonPrize.Projection.support C (MoonPrize.Projection.choice C I) :=
    Finset.mem_union_left _ hv
  exact MoonPrize.Projection.avoid C I off _ hit (ji (Finset.mem_singleton_self _))

def rowsOn {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) : Finset (Finset V) :=
  W.powerset.filter (fun J => (∀ v ∈ J, ∀ w ∈ J, ¬G.Adj v w) ∧
    ∀ u ∈ W, u ∉ J → ∃ v ∈ J, G.Adj u v)

theorem few_rows {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.AndCount.AndCountCircuit n)
    (promise : ∀ I : Finset (Fin n), Independent G I →
      (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true)
    (W : Finset (Fin n)) : (rowsOn G W).card ≤ 2 ^ C.size := by
  classical
  let all := (Finset.univ : Finset (Fin C.size → Bool)).image
    (fun s => W \ MoonPrize.Projection.support C s)
  have sub : rowsOn G W ⊆ all := by
    intro J hj
    simp only [rowsOn,Finset.mem_filter,Finset.mem_powerset] at hj
    obtain ⟨hw,ii,dom⟩ := hj
    obtain ⟨s,hs⟩ := project_rows G C promise W J hw ii dom
    exact Finset.mem_image.mpr ⟨s,Finset.mem_univ _,hs⟩
  have cap := (Finset.card_le_card sub).trans Finset.card_image_le
  simpa using cap

end MoonPrize.Core
namespace MoonPrize.Shape

open PEqualNP.AndCount
open MoonPrize.Core MoonPrize.Projection

def tagsFuel {k : ℕ} (rs : Fin k → Bool → Finset (Fin k)) (s : Fin k → Bool) :
    ℕ → Fin k → Finset (Fin k × Bool)
  | 0, _ => ∅
  | d+1, i => insert (i,s i) (((rs i (s i)).filter (· < i)).biUnion (tagsFuel rs s d))

def mask {k : ℕ} (rs : Fin k → Bool → Finset (Fin k)) (outs : Finset (Fin k))
    (s : Fin k → Bool) : Finset (Fin k × Bool) :=
  outs.biUnion (tagsFuel rs s k)

def masks {k : ℕ} (rs : Fin k → Bool → Finset (Fin k)) (outs : Finset (Fin k)) :=
  (Finset.univ : Finset (Fin k → Bool)).image (mask rs outs)

def rawType {n} (C : AndCountCircuit n) (v : Fin n) : Finset (Fin C.size × Bool) :=
  Finset.univ.filter (fun t => v ∈ raw C t.1 t.2)

lemma decompose_fuel {n} (C : AndCountCircuit n) (s : Fin C.size → Bool) :
    ∀ d (i : Fin C.size) (v : Fin n), v ∈ supportFuel C s d i ↔
      ∃ t ∈ tagsFuel (refs C) s d i, v ∈ raw C t.1 t.2 := by
  intro d
  induction d with
  | zero => simp [supportFuel,tagsFuel]
  | succ d ih =>
    intro i v
    simp only [supportFuel,tagsFuel,Finset.mem_union,Finset.mem_biUnion,Finset.mem_insert]
    constructor
    · rintro (here|⟨j,hj,there⟩)
      · exact ⟨(i,s i),Or.inl rfl,here⟩
      · obtain ⟨t,ht,hv⟩ := (ih j v).mp there
        exact ⟨t,Or.inr ⟨j,hj,ht⟩,hv⟩
    · rintro ⟨t,atTag,hv⟩
      rcases atTag with h|⟨j,hj,there⟩
      · subst t; exact Or.inl hv
      · exact Or.inr ⟨j,hj,(ih j v).mpr ⟨t,there,hv⟩⟩

lemma mem_support_via_mask {n} (C : AndCountCircuit n) (bare : C.outVars = ∅)
    (s : Fin C.size → Bool) (v : Fin n) :
    v ∈ support C s ↔ ∃ t ∈ mask (refs C) C.outGates s, t ∈ rawType C v := by
  simp only [support,bare,Finset.empty_union,mask,Finset.mem_biUnion,rawType,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,h⟩
    obtain ⟨t,ht,hv⟩ := (decompose_fuel C s _ i v).mp h
    exact ⟨t,⟨i,hi,ht⟩,hv⟩
  · rintro ⟨t,⟨i,hi,ht⟩,hv⟩
    exact ⟨i,hi,(decompose_fuel C s _ i v).mpr ⟨t,ht,hv⟩⟩

theorem realizes {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : AndCountCircuit n)
    (promise : ∀ I : Finset (Fin n), Independent G I →
      (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true)
    (W : Finset (Fin n)) :
    ∃ f : Finset (Fin n) → Finset (Fin C.size × Bool),
      Set.InjOn f (rowsOn G W : Set (Finset (Fin n))) ∧
      ∀ J ∈ rowsOn G W, f J ∈ masks (refs C) C.outGates ∧
        ∀ v ∈ W, v ∈ J ↔ Disjoint (f J) (rawType C v) := by
  classical
  have projected : ∀ J ∈ rowsOn G W, ∃ s, W \ support C s = J := by
    intro J hj
    simp only [rowsOn,Finset.mem_filter,Finset.mem_powerset] at hj
    exact project_rows G C promise W J hj.1 hj.2.1 hj.2.2
  let pick (J : Finset (Fin n)) : Fin C.size → Bool :=
    if h : J ∈ rowsOn G W then (projected J h).choose else fun _ => false
  let f (J : Finset (Fin n)) := mask (refs C) C.outGates (pick J)
  have selected (J) (hj : J ∈ rowsOn G W) : W \ support C (pick J) = J := by
    simpa only [pick,dite_eq_left hj] using (projected J hj).choose_spec
  have eqn (J) (hj : J ∈ rowsOn G W) (v) (hw : v ∈ W) :
      v ∈ J ↔ Disjoint (f J) (rawType C v) := by
    have mem := Finset.ext_iff.mp (selected J hj) v
    rw [Finset.mem_sdiff,and_iff_right hw,mem_support_via_mask C (bare_output_empty G C promise)] at mem
    rw [Finset.disjoint_left]
    exact mem.symm.trans (by simp [f])
  have sub (J) (hj : J ∈ rowsOn G W) : J ⊆ W := by
    simp only [rowsOn,Finset.mem_filter,Finset.mem_powerset] at hj
    exact hj.1
  refine ⟨f,?_,?_⟩
  · intro A ha B hb eq
    ext v
    by_cases hw : v ∈ W
    · rw [eqn A ha v hw,eqn B hb v hw,eq]
    · exact iff_of_false (fun h => hw (sub A ha h)) (fun h => hw (sub B hb h))
  · intro J hj
    exact ⟨Finset.mem_image.mpr ⟨pick J,Finset.mem_univ _,rfl⟩,eqn J hj⟩

end MoonPrize.Shape

namespace MoonPrize.Finite

open MoonPrize.Core MoonPrize.Shape
open PEqualNP.AndCount

def NoSquare {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a

def Obstruction : Prop :=
  ∀ (m : Fin 11) (k : Fin 5) (H : SimpleGraph (Fin m.val)), NoSquare H →
    Hard H Finset.univ →
    (∀ v : Fin m.val, ∃ A : Finset (Fin m.val), Independent H A ∧ v ∉ A ∧
      A.card + 5 = m.val) →
    ∀ (rs : Fin k.val → Bool → Finset (Fin k.val)) (outs : Finset (Fin k.val))
      (column : Fin m.val → Finset (Fin k.val × Bool)),
      ¬ (∀ J : Finset (Fin m.val), Independent H J →
        (∀ u, u ∉ J → ∃ v ∈ J, H.Adj u v) →
        ∃ s ∈ masks rs outs, ∀ u, u ∈ J ↔ Disjoint s (column u))

lemma map_ind {A B : Type*} [DecidableEq B] (G : SimpleGraph B) (e : A ↪ B) (S : Finset A) :
    Independent G (S.map e) ↔ Independent (G.comap e) S := by
  constructor
  · intro h x hx y hy
    exact h (e x) (Finset.mem_map_of_mem _ hx) (e y) (Finset.mem_map_of_mem _ hy)
  · intro h x hx y hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hy
    exact h a ha b hb

theorem from_finite (missing : Obstruction) :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 5 ≤ T.card) → ∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed → (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → 5 ≤ C.size := by
  classical
  intro n G noSquare cover C _ promise
  by_contra small
  obtain ⟨W,hard,ten,exclude⟩ := small_core G cover
  let m : Fin 11 := ⟨W.card,by omega⟩
  let k : Fin 5 := ⟨C.size,by omega⟩
  let e : Fin m.val ↪ Fin n := W.equivFin.symm.toEmbedding.trans
    ⟨Subtype.val,Subtype.val_injective⟩
  let H := G.comap e
  have inside (a : Fin m.val) : e a ∈ W := (W.equivFin.symm a).property
  have onto (b : Fin n) (hb : b ∈ W) : ∃ a, e a = b := by
    refine ⟨W.equivFin ⟨b,hb⟩,?_⟩
    change ((W.equivFin.symm (W.equivFin ⟨b,hb⟩)) : Fin n) = b
    rw [Equiv.symm_apply_apply]
  have sub (S : Finset (Fin m.val)) : S.map e ⊆ W := by
    intro z hz
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hz
    exact inside a
  have hsq : NoSquare H := by
    intro a b c d ac bd ab bc cd da
    exact noSquare (e a) (e b) (e c) (e d) (e.injective.ne ac) (e.injective.ne bd) ab bc cd da
  have hh : Hard H Finset.univ := by
    intro S _ hi
    have h := hard (S.map e) (sub _) ((map_ind G e S).mpr hi)
    simpa [m] using h
  have ex (a : Fin m.val) : ∃ S : Finset (Fin m.val),
      Independent H S ∧ a ∉ S ∧ S.card + 5 = m.val := by
    obtain ⟨A,hw,ii,no,sz⟩ := exclude (e a) (inside a)
    let S := Finset.univ.filter (fun j : Fin m.val => e j ∈ A)
    have eq : S.map e = A := by
      ext z
      constructor
      · intro hz
        obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hz
        exact (Finset.mem_filter.mp hb).2
      · intro hz
        obtain ⟨b,hb⟩ := onto z (hw hz)
        exact Finset.mem_map.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb ▸ hz⟩,hb⟩
    have is : Independent H S := (map_ind G e S).mp (eq ▸ ii)
    have hc := congrArg Finset.card eq
    simp only [Finset.card_map] at hc
    exact ⟨S,is,fun ha => no (Finset.mem_filter.mp ha).2,hc ▸ sz⟩
  obtain ⟨f,_,represented⟩ := realizes G C promise W
  apply missing m k H hsq hh ex (MoonPrize.Projection.refs C) C.outGates (fun a => rawType C (e a))
  intro J ii dom
  have good : J.map e ∈ rowsOn G W := by
    simp only [rowsOn,Finset.mem_filter,Finset.mem_powerset]
    refine ⟨sub _,(map_ind G e J).mpr ii,?_⟩
    intro u hu hn
    obtain ⟨a,rfl⟩ := onto u hu
    have hna : a ∉ J := fun ha => hn (Finset.mem_map_of_mem e ha)
    obtain ⟨b,hb,ab⟩ := dom a hna
    exact ⟨e b,Finset.mem_map_of_mem e hb,ab⟩
  obtain ⟨hm,cols⟩ := represented _ good
  refine ⟨f (J.map e),hm,?_⟩
  intro a
  exact (Finset.mem_map' e).symm.trans (cols (e a) (inside a))

end MoonPrize.Finite

namespace MoonPrize.Wiring

def sh0 (o : ℕ) : ℕ := if o % 2 = 0 then 1 else 6

def sh1 (w o : ℕ) : ℕ :=
  if o.testBit 1 then ((sh0 (o % 2 ||| (w &&& 1))) <<< 4) |||
    ((sh0 (o % 2 ||| ((w >>> 1) &&& 1))) <<< 8)
  else sh0 (o % 2)

def sh2 (w o : ℕ) : ℕ :=
  if o.testBit 2 then ((sh1 w (o % 4 ||| ((w >>> 2) &&& 3))) <<< 16) |||
    ((sh1 w (o % 4 ||| ((w >>> 4) &&& 3))) <<< 32)
  else sh1 w (o % 4)

def top (w a b : ℕ) : ℕ := (sh2 w a <<< 64) ||| (sh2 w b <<< 128)

def encode (s : List ℕ) : ℕ := s.foldr (fun v e => (1 <<< v) ||| e) 0

lemma encode_spec (s : List ℕ) (v : ℕ) : (encode s).testBit v = true ↔ v ∈ s := by
  induction s with
  | nil => simp [encode]
  | cons a s ih =>
    change (((1 : ℕ) <<< a) ||| encode s).testBit v = true ↔ v ∈ a :: s
    simp [Nat.testBit_or,ih,Nat.one_shiftLeft,Nat.testBit_two_pow]
    tauto

def applyBits (mapping x : ℕ) : ℕ :=
  (List.range 8).foldr (fun i acc =>
    if x.testBit i then (1 <<< ((mapping >>> (3*i)) &&& 7)) ||| acc else acc) 0

def classes : List (List ℕ) := [[5,6,89,90,105,106,153,154,169,170],[5,22,25,26,102,105,106,166,169,170],[5,22,38,73,90,106,153,154,169,170],[5,22,38,89,90,105,106,153,154,169,170],[5,22,89,90,102,105,106,153,154,166,169,170],[5,86,89,90,102,105,106,150,153,154,166,169,170],[21,22,25,26,97,98,165,166,169,170],[21,22,25,26,97,102,106,161,166,170],[21,22,25,26,97,102,106,165,166,169,170],[21,22,25,26,101,102,105,106,165,166,169,170],[21,22,73,90,101,102,106,137,154,165,166,170],[21,22,88,101,102,105,106,152,165,166,169,170],[21,22,88,101,102,105,106,153,154,165,166,169,170],[21,22,89,90,101,102,104,153,154,165,166,168],[21,22,89,90,101,102,104,153,154,165,166,169,170],[21,22,89,90,101,102,105,106,153,154,165,166,169,170],[21,86,89,90,101,102,105,106,150,153,154,165,166,169,170],[85,86,89,90,101,102,105,106,149,150,153,154,165,166,169,170]]

def word0 : List ℕ := [1,6,272,352,1552,1632,4295032832,4295360512,4312793088,4318035968,4396679168,4401922048,25769869312,25770196992,25787629568,25792872448]
def witness0 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [0],Sum.inl [1,2],Sum.inl [4,8],Sum.inl [5,6,8],Sum.inl [4,9,10],Sum.inl [5,6,9,10],Sum.inl [16,32],Sum.inl [17,18,32],Sum.inl [20,24,32],Sum.inl [21,22,24,32],Sum.inl [20,25,26,32],Sum.inl [21,22,25,26,32],Sum.inl [16,33,34],Sum.inl [17,18,33,34],Sum.inl [20,24,33,34],Sum.inl [21,22,24,33,34]]

def word1 : List ℕ := [25871515648,25876758528,1168231170048,1168231497728,1168248930304,1168338059264,1511828553728,1511828881408,1511851556864,1511935442944,6665789308928,6665789636608,6665890955264,6665896198144,7009386692608,7009387020288]
def witness1 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [20,25,26,33,34],Sum.inl [21,22,25,26,33,34],Sum.inl [16,36,40],Sum.inl [17,18,36,40],Sum.inl [20,24,36,40],Sum.inl [21,22,25,26,36,40],Sum.inl [16,37,38,40],Sum.inl [17,18,37,38,40],Sum.inl [21,22,24,37,38,40],Sum.inl [21,22,25,26,37,38,40],Sum.inl [16,36,41,42],Sum.inl [17,18,36,41,42],Sum.inl [20,25,26,36,41,42],Sum.inl [21,22,25,26,36,41,42],Sum.inl [16,37,38,41,42],Sum.inl [17,18,37,38,41,42]]

def word2 : List ℕ := [7009404452864,7009409695744,7009488338944,7009493581824,340282366920938463481821351505477763072,340282366920938463574055071874025521152,340282366920938468480888995480766251008,340282366920938469956628521377530380288,340282366920938492092721409828992319488,340282366920938493568460935725756448768,340282367000167834903458559654486867968,340282367000173879532556632800360398848,340282367000495453800574124160832241664,340282367000592167866143294494808735744,340282367002042878849680849504456146944,340282367002139592915250019838432641024]
def witness2 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [20,24,37,38,41,42],Sum.inl [21,22,24,37,38,41,42],Sum.inl [20,25,26,37,38,41,42],Sum.inl [21,22,25,26,37,38,41,42],Sum.inl [64,128],Sum.inl [65,66,128],Sum.inl [68,72,128],Sum.inl [69,70,72,128],Sum.inl [68,73,74,128],Sum.inl [69,70,73,74,128],Sum.inl [80,96,128],Sum.inl [81,82,96,128],Sum.inl [84,88,96,128],Sum.inl [85,86,88,96,128],Sum.inl [84,89,90,96,128],Sum.inl [85,86,89,90,96,128]]

def word3 : List ℕ := [340282367396308647474780247622206619648,340282367396314692103878320768080150528,340282367396636266371895812128551993344,340282367396732980437464982462528487424,340282367398183691421002537472175898624,340282367398280405486571707806152392704,340282388470999876269094047504897409024,340282388471005920898192120650770939904,340282388471327495166209612011242782720,340282388472971634280885507688843182080,340282394809252877410241054988413435904,340282394809258922039339128134286966784,340282394809677210372925789828735303680,340282394811224635422032515172359208960,340282489883047894527446167241153839104,340282489883053939156544240387027369984]
def witness3 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [80,97,98,128],Sum.inl [81,82,97,98,128],Sum.inl [84,88,97,98,128],Sum.inl [85,86,88,97,98,128],Sum.inl [84,89,90,97,98,128],Sum.inl [85,86,89,90,97,98,128],Sum.inl [80,100,104,128],Sum.inl [81,82,100,104,128],Sum.inl [84,88,100,104,128],Sum.inl [85,86,89,90,100,104,128],Sum.inl [80,101,102,104,128],Sum.inl [81,82,101,102,104,128],Sum.inl [85,86,88,101,102,104,128],Sum.inl [85,86,89,90,101,102,104,128],Sum.inl [80,100,105,106,128],Sum.inl [81,82,100,105,106,128]]

def word4 : List ℕ := [340282489884922938473668457091123118080,340282489885019652539237627425099612160,340282496221300895668593174724669865984,340282496221306940297691247870543396864,340282496221628514565708739231015239680,340282496221725228631277909564991733760,340282496223175939614815464574639144960,340282496223272653680384634908615639040,2041694201525630780798694388664318820352,2041694201525630780890928109032866578432,2041694201525630785797762032639607308288,2041694201525630787273501558536371437568,2041694201525630809409594446987833376768,2041694201525630810885333972884597506048,2041694201604860152220331596813327925248,2041694201604866196849429669959201456128]
def witness4 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [84,89,90,100,105,106,128],Sum.inl [85,86,89,90,100,105,106,128],Sum.inl [80,101,102,105,106,128],Sum.inl [81,82,101,102,105,106,128],Sum.inl [84,88,101,102,105,106,128],Sum.inl [85,86,88,101,102,105,106,128],Sum.inl [84,89,90,101,102,105,106,128],Sum.inl [85,86,89,90,101,102,105,106,128],Sum.inl [64,129,130],Sum.inl [65,66,129,130],Sum.inl [68,72,129,130],Sum.inl [69,70,72,129,130],Sum.inl [68,73,74,129,130],Sum.inl [69,70,73,74,129,130],Sum.inl [80,96,129,130],Sum.inl [81,82,96,129,130]]

def word5 : List ℕ := [2041694201605187771117447161319673298944,2041694201605284485183016331653649793024,2041694201606735196166553886663297204224,2041694201606831910232123056997273698304,2041694202001000964791653284781047676928,2041694202001007009420751357926921207808,2041694202001328583688768849287393050624,2041694202001425297754338019621369544704,2041694202002876008737875574631016955904,2041694202002972722803444744964993449984,2041694223075692193585967084663738466304,2041694223075698238215065157809611997184,2041694223076019812483082649170083840000,2041694223077663951597758544847684239360,2041694229413945194727114092147254493184,2041694229413951239356212165293128024064]
def witness5 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [84,88,96,129,130],Sum.inl [85,86,88,96,129,130],Sum.inl [84,89,90,96,129,130],Sum.inl [85,86,89,90,96,129,130],Sum.inl [80,97,98,129,130],Sum.inl [81,82,97,98,129,130],Sum.inl [84,88,97,98,129,130],Sum.inl [85,86,88,97,98,129,130],Sum.inl [84,89,90,97,98,129,130],Sum.inl [85,86,89,90,97,98,129,130],Sum.inl [80,100,104,129,130],Sum.inl [81,82,100,104,129,130],Sum.inl [84,88,100,104,129,130],Sum.inl [85,86,89,90,100,104,129,130],Sum.inl [80,101,102,104,129,130],Sum.inl [81,82,101,102,104,129,130]]

def word6 : List ℕ := [2041694229414369527689798826987576360960,2041694229415916952738905552331200266240,2041694324487740211844319204399994896384,2041694324487746256473417277545868427264,2041694324489615255790541494249964175360,2041694324489711969856110664583940669440,2041694330825993212985466211883510923264,2041694330825999257614564285029384454144,2041694330826320831882581776389856296960,2041694330826417545948150946723832791040,2041694330827868256931688501733480202240,2041694330827964970997257672067456696320,92556803802495262062056339965514663067648,92556803802495262062148573685883210825728,92556803802495262067055407609489951555584,92556803802495262092142979549734941753344]
def witness6 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [85,86,88,101,102,104,129,130],Sum.inl [85,86,89,90,101,102,104,129,130],Sum.inl [80,100,105,106,129,130],Sum.inl [81,82,100,105,106,129,130],Sum.inl [84,89,90,100,105,106,129,130],Sum.inl [85,86,89,90,100,105,106,129,130],Sum.inl [80,101,102,105,106,129,130],Sum.inl [81,82,101,102,105,106,129,130],Sum.inl [84,88,101,102,105,106,129,130],Sum.inl [85,86,88,101,102,105,106,129,130],Sum.inl [84,89,90,101,102,105,106,129,130],Sum.inr (0,11644360),Sum.inl [64,132,136],Sum.inl [65,66,132,136],Sum.inl [68,72,132,136],Sum.inl [69,70,73,74,132,136]]

def word7 : List ℕ := [92556803802574491433477977173663672172544,92556803802574497478107075246809545703424,92556803802574819052375092738170017546240,92556803802576463191489768633847617945600,92556803802970632246049298861631391924224,92556803802970638290678396934777265455104,92556803802970959864946414426137737297920,92556803802972604004061090321815337697280,92556803824045323474843612661514082713600,92556803824045329519472710734659956244480,92556803824045651093740728226020428087296,92556803824047295232855404121698028486656,92556803931795624494243111788733855170560,92556803931795630538872209861879728701440,92556803931795952113140227353240200544256,92556803931797596252254903248917800943616]
def witness7 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [80,96,132,136],Sum.inl [81,82,96,132,136],Sum.inl [84,88,96,132,136],Sum.inl [85,86,89,90,96,132,136],Sum.inl [80,97,98,132,136],Sum.inl [81,82,97,98,132,136],Sum.inl [84,88,97,98,132,136],Sum.inl [85,86,89,90,97,98,132,136],Sum.inl [80,100,104,132,136],Sum.inl [81,82,100,104,132,136],Sum.inl [84,88,100,104,132,136],Sum.inl [85,86,89,90,100,104,132,136],Sum.inl [80,101,102,105,106,132,136],Sum.inl [81,82,101,102,105,106,132,136],Sum.inl [84,88,101,102,105,106,132,136],Sum.inr (0,11570650)]

def word8 : List ℕ := [119779393156170339139126308560056119984128,119779393156170339139218542280424667742208,119779393156170339145601115729928172601344,119779393156170339169212948144276398669824,119779393156249568510547945768205129089024,119779393156249574555177043841351002619904,119779393156249992843510630503045450956800,119779393156251540268559737228389074862080,119779393156645709323119267456172848840704,119779393156645715367748365529318722371584,119779393156646133656081952191013170708480,119779393156647681081131058916356794613760,119779393184058653553054728263539055656960,119779393184058659597683826336684929187840,119779393184059077886017412998379377524736,119779393184060625311066519723723001430016]
def witness8 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [64,133,134,136],Sum.inl [65,66,133,134,136],Sum.inl [69,70,72,133,134,136],Sum.inl [69,70,73,74,133,134,136],Sum.inl [80,96,133,134,136],Sum.inl [81,82,96,133,134,136],Sum.inl [85,86,88,96,133,134,136],Sum.inl [85,86,89,90,96,133,134,136],Sum.inl [80,97,98,133,134,136],Sum.inl [81,82,97,98,133,134,136],Sum.inl [85,86,88,97,98,133,134,136],Sum.inl [85,86,89,90,97,98,133,134,136],Sum.inl [80,101,102,104,133,134,136],Sum.inl [81,82,101,102,104,133,134,136],Sum.inl [85,86,88,101,102,104,133,134,136],Sum.inr (2,9735635)]

def word9 : List ℕ := [119779393285470701571313080383275312087040,119779393285470707615942178456421185617920,119779393285471125904275765118115633954816,119779393285472673329324871843459257860096,528118233461296495295175837478177973731328,528118233461296495295268071198546521489408,528118233461296495323786737536501488287744,528118233461296495325262477062398252417024,528118233461375724666597474686326982836224,528118233461375730711226572759472856367104,528118233461377599710543696976176952115200,528118233461377696424609266146510928609280,528118233461771865479168796374294702587904,528118233461771871523797894447440576118784,528118233461773740523115018664144671866880,528118233461773837237180587834478648360960]
def witness9 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [80,101,102,105,106,133,134,136],Sum.inl [81,82,101,102,105,106,133,134,136],Sum.inr (2,11570643),Sum.inr (3,11570643),Sum.inl [64,132,137,138],Sum.inl [65,66,132,137,138],Sum.inl [68,73,74,132,137,138],Sum.inl [69,70,73,74,132,137,138],Sum.inl [80,96,132,137,138],Sum.inl [81,82,96,132,137,138],Sum.inl [84,89,90,96,132,137,138],Sum.inl [85,86,89,90,96,132,137,138],Sum.inl [80,97,98,132,137,138],Sum.inl [81,82,97,98,132,137,138],Sum.inl [84,89,90,97,98,132,137,138],Sum.inl [85,86,89,90,97,98,132,137,138]]

def word10 : List ℕ := [528118233584258604726221462293913649807360,528118233584258610770850560367059523338240,528118233584260479770167684583763619086336,528118233584260576484233253754097595580416,528118233590596857727362609301397165834240,528118233590596863771991707374543039365120,528118233590598732771308831591247135113216,528118233590598829485374400761581111607296,555340822814971572372245806072719430647808,555340822814971572372338039793087978405888,555340822814971572377244873716694719135744,555340822814971572378720613242591483265024,555340822814971572400856706131042945204224,555340822814971572402332445656939709333504,555340822815050801743667443280868439752704,555340822815050807788296541354014313283584]
def witness10 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [80,100,105,106,132,137,138],Sum.inl [81,82,100,105,106,132,137,138],Sum.inl [84,89,90,100,105,106,132,137,138],Sum.inr (2,9735642),Sum.inl [80,101,102,105,106,132,137,138],Sum.inl [81,82,101,102,105,106,132,137,138],Sum.inr (2,11570650),Sum.inr (3,11570650),Sum.inl [64,133,134,137,138],Sum.inl [65,66,133,134,137,138],Sum.inl [68,72,133,134,137,138],Sum.inl [69,70,72,133,134,137,138],Sum.inl [68,73,74,133,134,137,138],Sum.inl [69,70,73,74,133,134,137,138],Sum.inl [80,96,133,134,137,138],Sum.inl [81,82,96,133,134,137,138]]

def word11 : List ℕ := [555340822815051129362564558845374785126400,555340822815051226076630128015708761620480,555340822815052676787613665570718409031680,555340822815052773501679234741052385525760,555340822815446942556238764968836159504384,555340822815446948600867863041982033035264,555340822815447270175135880533342504878080,555340822815447366889201449703676481372160,555340822815448817600184987258686128783360,555340822815448914314250556429020105277440,555340822836521633785033078768718850293760,555340822836521639829662176841864723824640,555340822836521961403930194333225195667456,555340822836523605543044870228902796066816,555340822842859886786174225776202366320640,555340822842859892830803323849348239851520]
def witness11 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [84,88,96,133,134,137,138],Sum.inl [85,86,88,96,133,134,137,138],Sum.inl [84,89,90,96,133,134,137,138],Sum.inl [85,86,89,90,96,133,134,137,138],Sum.inl [80,97,98,133,134,137,138],Sum.inl [81,82,97,98,133,134,137,138],Sum.inl [84,88,97,98,133,134,137,138],Sum.inl [85,86,88,97,98,133,134,137,138],Sum.inl [84,89,90,97,98,133,134,137,138],Sum.inr (6,9926280),Sum.inl [80,100,104,133,134,137,138],Sum.inl [81,82,100,104,133,134,137,138],Sum.inl [84,88,100,104,133,134,137,138],Sum.inr (6,9925146),Sum.inl [80,101,102,104,133,134,137,138],Sum.inl [81,82,101,102,104,133,134,137,138]]

def word12 : List ℕ := [555340822842860311119136910511042688188416,555340822842861858544186017236386312093696,555340822937933681803291430888455106723840,555340822937933687847920528961600980254720,555340822937935556847237653178305076002816,555340822937935653561303222348639052496896,555340822944271934804432577895938622750720,555340822944271940849061675969084496281600,555340822944272262423329693460444968124416,555340822944272359137395262630778944618496,555340822944273809848378800185788592029696,555340822944273906562444369356122568523776,1461523938076101448826826368453002412091148075008,1461523938076101448826826368545236132459695833088,1461523938076101448826826373452070056066436562944,1461523938076101448826826374927809581963200692224]
def witness12 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inr (7,11760147),Sum.inr (8,9925139),Sum.inl [80,100,105,106,133,134,137,138],Sum.inl [81,82,100,105,106,133,134,137,138],Sum.inr (7,11760154),Sum.inr (8,9925146),Sum.inl [80,101,102,105,106,133,134,137,138],Sum.inr (6,11761288),Sum.inr (6,11760154),Sum.inr (8,11760147),Sum.inr (8,11760154),Sum.inr (9,11761288),Sum.inl [64,144,160],Sum.inl [65,66,144,160],Sum.inl [68,72,144,160],Sum.inl [69,70,72,144,160]]

def word13 : List ℕ := [1461523938076101448826826397063902470414662631424,1461523938076101448826826398539641996311426760704,1461523938076101448906055739874639620240157179904,1461523938076101449302202597075059381353750462464,1461523938076101470377215400137390672596913094656,1461523938076101476715565115344106850414405615616,1461523938076101571790810843444849517676793430016,1461523938076101578129160558651565695494285950976,1461635441802094101942534047044365653898677977088,1461635441802094101942534047136599374267225735168,1461635441802094101942534052043433297873966465024,1461635441802094101942534053519172823770730594304,1461635441802094101942534075655265712222192533504,1461635441802094101942534077131005238118956662784,1461635441802094102021769463095100935193560612864,1461635441802094102417910275666422623161280364544]
def witness13 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [68,73,74,144,160],Sum.inl [69,70,73,74,144,160],Sum.inl [80,96,144,160],Sum.inl [81,82,97,98,144,160],Sum.inl [84,88,100,104,144,160],Sum.inl [85,86,88,101,102,104,144,160],Sum.inl [84,89,90,100,105,106,144,160],Sum.inr (0,6852076),Sum.inl [64,145,146,160],Sum.inl [65,66,145,146,160],Sum.inl [68,72,145,146,160],Sum.inl [69,70,72,145,146,160],Sum.inl [68,73,74,145,146,160],Sum.inl [69,70,73,74,145,146,160],Sum.inl [81,82,96,145,146,160],Sum.inl [81,82,97,98,145,146,160]]

def word14 : List ℕ := [1461635441802094123494567217843429810082043396096,1461635441802094129832820218984576817565559422976,1461635441802094224906615236101781929818299826176,1461635441802094231244868237242928937301815853056,1467567440024903247698182548104890118059268767744,1467567440024903247698182548197123838427816525824,1467567440024903247698182553103957762034557255680,1467567440024903247698182578191529702279547453440,1467567440024903247777739538423642890714623246336,1467567440024903248175524490109640474359943397376,1467567440024903269248571579789278378565033787392,1467567440024903377000516738303453401462406643712,1469351499640785697549505405566701986979747201024,1469351499640785697549505405658935707348294959104,1469351499640785697549505412041509156851799818240,1469351499640785697549505435653341571200025886720]
def witness14 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [85,86,89,90,100,104,145,146,160],Sum.inr (2,5017061),Sum.inr (2,6852069),Sum.inr (3,6852069),Sum.inl [64,148,152,160],Sum.inl [65,66,148,152,160],Sum.inl [68,72,148,152,160],Sum.inl [69,70,73,74,148,152,160],Sum.inl [84,88,96,148,152,160],Sum.inl [85,86,89,90,97,98,148,152,160],Sum.inl [84,88,100,104,148,152,160],Sum.inr (3,2207205),Sum.inl [64,149,150,152,160],Sum.inl [65,66,149,150,152,160],Sum.inl [69,70,72,149,150,152,160],Sum.inl [69,70,73,74,149,150,152,160]]

def word15 : List ℕ := [1469351499640785697629159109951023929969078173696,1469351499640785698026847347571452343280421830656,1469351499640785725438244152457806425303004741632,1469351499640785826851839595765265270382885076992,1496112393879022445319348267493880020786923700224,1496112393879022445319348267586113741155471458304,1496112393879022445319348296104780079110438256640,1496112393879022445319348297580519605007202385920,1496112393879022445400452682861739518785902084096,1496112393879022445796690209498630377087598329856,1496112393879022568283332742485727126372569055232,1496112393879022574621682457692443304190061576192,1497896453494904895170671124955691889707402133504,1497896453494904895170671125047925610075949891584,1497896453494904895170671129954759533682690621440,1497896453494904895170671131430499059579454750720]
def witness15 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [85,86,88,96,149,150,152,160],Sum.inr (2,5015927),Sum.inr (1,2178533),Sum.inr (4,2178533),Sum.inl [64,148,153,154,160],Sum.inl [65,66,148,153,154,160],Sum.inl [68,73,74,148,153,154,160],Sum.inl [69,70,73,74,148,153,154,160],Sum.inl [84,89,90,96,148,153,154,160],Sum.inr (2,6850935),Sum.inr (1,2207205),Sum.inr (4,2207205),Sum.inl [64,149,150,153,154,160],Sum.inl [65,66,149,150,153,154,160],Sum.inl [68,72,149,150,153,154,160],Sum.inl [69,70,72,149,150,153,154,160]]

def word16 : List ℕ := [1497896453494904895170671153566591948030916689920,1497896453494904895170671155042331473927680819200,1497896453494904895251872254389120558040357011456,1497896453494904895648013066960442246008076763136,1497896453494904916722704295754756045890767552512,1497896453494904923060957296895903053374283579392,1497896453494905018134752314013108165627023982592,1497896453494905024473005315154255173110540009472,8769032124730616039845250532034417510370810789888,8769032124730616039845250532126651230739358547968,8769032124730616039845250537033485154346099277824,8769032124730616039845250538509224680242863407104,8769032124730616039845250560645317568694325346304,8769032124730616039845250562121057094591089475584,8769032124730616040320620716027376406487539646464,8769032124730616040320626760656474479633413177344]
def witness16 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [68,73,74,149,150,153,154,160],Sum.inl [69,70,73,74,149,150,153,154,160],Sum.inr (0,6850942),Sum.inr (3,6850935),Sum.inr (3,2206071),Sum.inr (4,2177399),Sum.inr (4,2206071),Sum.inr (5,6852069),Sum.inl [64,144,161,162],Sum.inl [65,66,144,161,162],Sum.inl [68,72,144,161,162],Sum.inl [69,70,72,144,161,162],Sum.inl [68,73,74,144,161,162],Sum.inl [69,70,73,74,144,161,162],Sum.inl [80,97,98,144,161,162],Sum.inl [81,82,97,98,144,161,162]]

def word17 : List ℕ := [8769032124730616169145940583118304898096348266496,8769032124730616169146037297183874068430324760576,8769032124730616169147488008167411623439972171776,8769032124730616169147584722232980793773948665856,8769143628456608692960958210625780752178340691968,8769143628456608692960958210718014472546888450048,8769143628456608692960958215624848396153629179904,8769143628456608692960958217100587922050393309184,8769143628456608692960958239236680810501855248384,8769143628456608692960958240712420336398619377664,8769143628456608693040187582047417960327349796864,8769143628456608693040193626676516033473223327744,8769143628456608693436328394618739648295069548544,8769143628456608693436334439247837721440943079424,8769143628456608714511347242310169012684105711616,8769143628456608714512991381424844908361706110976]
def witness17 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [84,88,101,102,105,106,144,161,162],Sum.inr (2,5017068),Sum.inr (2,6852076),Sum.inr (3,6852076),Sum.inl [64,145,146,161,162],Sum.inl [65,66,145,146,161,162],Sum.inl [68,72,145,146,161,162],Sum.inl [69,70,72,145,146,161,162],Sum.inl [68,73,74,145,146,161,162],Sum.inl [69,70,73,74,145,146,161,162],Sum.inl [80,96,145,146,161,162],Sum.inl [81,82,96,145,146,161,162],Sum.inl [80,97,98,145,146,161,162],Sum.inl [81,82,97,98,145,146,161,162],Sum.inl [84,88,100,104,145,146,161,162],Sum.inr (7,7041573)]

def word18 : List ℕ := [8769143628456608720849696957516885190501598232576,8769143628456608720851244382565991915845222137856,8769143628456608815924942685617627857763986046976,8769143628456608815925039399683197028097962541056,8769143628456608822261648261709668139903878168576,8769143628456608822261744975775237310237854662656,8769143628456608822263195686758774865247502073856,8769143628456608822263292400824344035581478567936,8775075626679417838716606711686305216338931482624,8775075626679417838716606711778538936707479240704,8775075626679417838716606716685372860314219970560,8775075626679417838716606741772944800559210168320,8775075626679417839192304514576379676962005712896,8775075626679417839193948653691055572639606112256,8775075626679417968017296762770192604064468959232,8775075626679417968018940901884868499742069358592]
def witness18 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inr (6,5206572),Sum.inr (8,5206565),Sum.inr (6,7041580),Sum.inr (8,7041573),Sum.inr (7,7041580),Sum.inr (8,5206572),Sum.inr (8,7041580),Sum.inr (9,7043848),Sum.inl [64,148,152,161,162],Sum.inl [65,66,148,152,161,162],Sum.inl [68,72,148,152,161,162],Sum.inl [69,70,73,74,148,152,161,162],Sum.inl [84,88,97,98,148,152,161,162],Sum.inr (7,6967863),Sum.inr (7,2279095),Sum.inr (11,7043400)]

def word19 : List ℕ := [8776859686295300288567929569148117085259409915904,8776859686295300288567929569240350805627957673984,8776859686295300288567929575622924255131462533120,8776859686295300288567929599234756669479688601600,8776859686295300289043724086103760716216460640256,8776859686295300289045271511152867441560084545536,8776859686295300417868716334297573643318923886592,8776859686295300417870263759346680368662547791872,8803620580533537036337772431075295119066586415104,8803620580533537036337772431167528839435134173184,8803620580533537036337772459686195177390100971520,8803620580533537036337772461161934703286865100800,8803620580533537036815017659014476305033284550656,8803620580533537036815114373080045475367261044736,8803620580533537165640009907208289232135747796992,8803620580533537165640106621273858402469724291072]
def witness19 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [64,149,150,152,161,162],Sum.inl [65,66,149,150,152,161,162],Sum.inl [69,70,72,149,150,152,161,162],Sum.inl [69,70,73,74,149,150,152,161,162],Sum.inr (6,5132862),Sum.inr (8,5132855),Sum.inr (10,2177847),Sum.inr (12,5208392),Sum.inl [64,148,153,154,161,162],Sum.inl [65,66,148,153,154,161,162],Sum.inl [68,73,74,148,153,154,161,162],Sum.inl [69,70,73,74,148,153,154,161,162],Sum.inr (6,6967870),Sum.inr (8,6967863),Sum.inr (10,2206519),Sum.inr (12,7043400)]

def word20 : List ℕ := [8805404640149419486189095288537106987987064848384,8805404640149419486189095288629340708355612606464,8805404640149419486189095293536174631962353336320,8805404640149419486189095295011914157859117465600,8805404640149419486189095317148007046310579404800,8805404640149419486189095318623746572207343534080,8805404640149419486268652278855859760642419326976,8805404640149419486268748992921428930976395821056,8805404640149419486270199703904966485986043232256,8805404640149419486270296417970535656320019726336,8805404640149419486664793091427181448610139078656,8805404640149419486664889805492750618944115572736,8805404640149419486666340516476288173953762983936,8805404640149419486666437230541857344287739478016,8805404640149419507739484320221495248492829868032,8805404640149419507741128459336171144170430267392]
def witness20 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [64,149,150,153,154,161,162],Sum.inl [65,66,149,150,153,154,161,162],Sum.inl [68,72,149,150,153,154,161,162],Sum.inl [69,70,72,149,150,153,154,161,162],Sum.inl [68,73,74,149,150,153,154,161,162],Sum.inr (6,9954952),Sum.inl [84,88,96,149,150,153,154,161,162],Sum.inr (2,5015934),Sum.inr (2,6850942),Sum.inr (3,6850942),Sum.inr (7,6967870),Sum.inr (8,5132862),Sum.inr (8,6967870),Sum.inr (9,6971272),Sum.inr (7,2352805),Sum.inr (11,6970824)]

def word21 : List ℕ := [8805404640149419514077834035428211426310322388992,8805404640149419514079381460477318151653946294272,8805404640149419609153079763528954093572710203392,8805404640149419609153176477594523263906686697472,8805404640149419615489785339620994375712602324992,8805404640149419615489882053686563546046578819072,8805404640149419615491332764670101101056226230272,8805404640149419615491429478735670271390202724352,397528467654750792282025416034565700738848867221504,397528467654750792282025416034657934459217414979584,397528467654750792282025416039564768382824155709440,397528467654750792282025416064652340323069145907200,397528467654750792303575477447352973434848286867456,397528467654750792303575805066250088999354632241152,397528467654750792411325784511381570635213932855296,397528467654750792411327750224764264022252005097472]
def witness21 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inr (10,2178981),Sum.inr (12,5135816),Sum.inr (10,2207653),Sum.inr (12,6970824),Sum.inr (13,7043400),Sum.inr (14,5208392),Sum.inr (14,7043400),Sum.inr (15,7043400),Sum.inl [64,144,164,168],Sum.inl [65,66,144,164,168],Sum.inl [68,72,144,164,168],Sum.inl [69,70,73,74,144,164,168],Sum.inl [80,100,104,144,164,168],Sum.inl [84,88,100,104,144,164,168],Sum.inl [81,82,101,102,105,106,144,164,168],Sum.inr (3,2207212)]

def word22 : List ℕ := [397528579158476784935141123713157063980656397123584,397528579158476784935141123713249297701024944881664,397528579158476784935141123718156131624631685611520,397528579158476784935141123743243703564876675809280,397528579158476784956691191170573434749801690300416,397528579158476784956693156883956128136839762542592,397528579158476785064441492189972933877021462757376,397528579158476785064443457903355627264059534999552,397534511156699594080896772214217588444816987914240,397534511156699594080896772214309822165185535672320,397534511156699594080896772219216656088792276402176,397534511156699594080896772244304228029037266599936,397534511156699594080976001585639225652965997019136,397534511156699594080976329204536341217472342392832,397534511156699594081372148442839645414079590301696,397534511156699594081374114156222338801117662543872]
def witness22 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [64,145,146,164,168],Sum.inl [65,66,145,146,164,168],Sum.inl [68,72,145,146,164,168],Sum.inl [69,70,73,74,145,146,164,168],Sum.inl [81,82,100,104,145,146,164,168],Sum.inr (7,2250423),Sum.inr (7,6996535),Sum.inr (11,7043848),Sum.inl [64,148,152,164,168],Sum.inl [65,66,148,152,164,168],Sum.inl [68,72,148,152,164,168],Sum.inl [69,70,73,74,148,152,164,168],Sum.inl [80,96,148,152,164,168],Sum.inl [84,88,96,148,152,164,168],Sum.inl [81,82,97,98,148,152,164,168],Sum.inr (7,2324133)]

def word23 : List ℕ := [397534511156699594102446833627004861140816407560192,397534511156699594102447161245901976705322752933888,397534511156699594210197140691033458341182053548032,397534511156699594210199106404416151728220125790208,397564840170169595728369260791068390216465121280000,397564840170169595728369260791160623936833669038080,397564840170169595728369260796067457860440409767936,397564840170169595728369260821155029800685399965696,397564840170169595728448496207119125497760003915776,397564840170169595728450461920501818884798076157952,397564840170169595728844637019690447185727723667456,397564840170169595728846602733073140572765795909632,397564840170169595749919328248484760985610414456832,397564840170169595749921293961867454372648486699008,397564840170169595857669629267884260112830186913792,397564840170169595857671594981266953499868259155968]
def witness23 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [80,100,104,148,152,164,168],Sum.inl [84,88,100,104,148,152,164,168],Sum.inr (7,2324140),Sum.inr (9,2325274),Sum.inl [64,149,150,153,154,164,168],Sum.inl [65,66,149,150,153,154,164,168],Sum.inl [68,72,149,150,153,154,164,168],Sum.inr (6,9953818),Sum.inl [81,82,96,149,150,153,154,164,168],Sum.inr (3,2206078),Sum.inr (7,7070245),Sum.inr (11,6971272),Sum.inr (7,2250430),Sum.inr (9,2252698),Sum.inr (13,7072520),Sum.inr (15,2324826)]

def word24 : List ℕ := [514448598641223025738320202651868342311323470659584,514448598641223025738320202651960576031692018417664,514448598641223025738320202658343149481195523276800,514448598641223025738320202681954981895543749345280,514448598641223025766208517065796762014806406332416,514448598641223025766208941398759446749646728200192,514448598641223025867620571128684212207688536293376,514448598641223025867622536842066905594726608535552,514448710144949018391435910330459705553131000561664,514448710144949018391435910330551939273499548319744,514448710144949018391435910336934512723003053178880,514448710144949018391435910360546345137351279247360,514448710144949018419324230789017223329759809765376,514448710144949018419326196502399916716797882007552,514448710144949018520736278807275575449496066195456,514448710144949018520738244520658268836534138437632]
def witness24 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [64,144,165,166,168],Sum.inl [65,66,144,165,166,168],Sum.inl [69,70,72,144,165,166,168],Sum.inl [69,70,73,74,144,165,166,168],Sum.inl [80,101,102,104,144,165,166,168],Sum.inr (1,2178540),Sum.inr (2,5016375),Sum.inr (4,2178540),Sum.inl [64,145,146,165,166,168],Sum.inl [65,66,145,146,165,166,168],Sum.inl [69,70,72,145,146,165,166,168],Sum.inl [69,70,73,74,145,146,165,166,168],Sum.inr (6,5161534),Sum.inr (10,2177399),Sum.inr (8,5161527),Sum.inr (12,5208840)]

def word25 : List ℕ := [514456426202787709987042881688982041886212069785600,514456426202787709987042881689074275606580617543680,514456426202787709987042881695456849056084122402816,514456426202787709987042881719068681470432348471296,514456426202787709987122111060403679094361078890496,514456426202787709987122535393366363829201400758272,514456426202787709987518257917604098855474672173056,514456426202787709987520223630986792242512744415232,514456426202787710014931196102910461589695005458432,514456426202787710014931620435873146324535327326208,514456426202787710116343250165797911782577135419392,514456426202787710116345215879180605169615207661568,514484971156641829184664047408371031788939724718080,514484971156641829184664047408463265509308272476160,514484971156641829184664047414845838958811777335296,514484971156641829184664047438457671373160003403776]
def witness25 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [64,149,150,152,165,166,168],Sum.inl [65,66,149,150,152,165,166,168],Sum.inl [69,70,72,149,150,152,165,166,168],Sum.inr (7,11788819),Sum.inl [80,96,149,150,152,165,166,168],Sum.inr (1,2178981),Sum.inr (6,5235244),Sum.inr (10,2178533),Sum.inr (1,2178988),Sum.inr (9,2178988),Sum.inr (10,2178540),Sum.inr (15,2323692),Sum.inl [64,149,150,153,154,165,166,168],Sum.inl [65,66,149,150,153,154,165,166,168],Sum.inr (2,9736083),Sum.inr (8,9953811)]

def word26 : List ℕ := [514484971156641829184743282824421767070234607353856,514484971156641829184745248537804460457272679596032,514484971156641829185139423636993088758202327105536,514484971156641829185141389350375782145240399347712,514484971156641829212552367866928549565568533921792,514484971156641829212554333580311242952606606163968,514484971156641829313964415885186901685304790351872,514484971156641829313966381598569595072342862594048,2268250563438306527582742001911407965898442522230784,2268250563438306527582742001911500199618811069988864,2268250563438306527582742001940018865956766036787200,2268250563438306527582742001941494605482662800916480,2268250563438306527705704111342453590714178198306816,2268250563438306527705705986386399813004028167585792,2268250563438306527712042370388223835794807587864576,2268250563438306527712044336101606529181845660106752]
def witness26 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inr (2,5017509),Sum.inr (4,2177406),Sum.inr (8,5235237),Sum.inr (12,5136264),Sum.inr (10,2177406),Sum.inr (15,2249982),Sum.inr (14,5237512),Sum.inr (16,2324819),Sum.inl [64,144,164,169,170],Sum.inl [65,66,144,164,169,170],Sum.inl [68,73,74,144,164,169,170],Sum.inl [69,70,73,74,144,164,169,170],Sum.inl [80,100,105,106,144,164,169,170],Sum.inr (1,2207212),Sum.inr (2,6851383),Sum.inr (4,2207212)]

def word27 : List ℕ := [2268250674942032520235857709589999329140250052132864,2268250674942032520235857709590091562860618599890944,2268250674942032520235857709618610229198573566689280,2268250674942032520235857709620085968724470330818560,2268250674942032520358819825065674052029131601739776,2268250674942032520358821790779056745416169673981952,2268250674942032520365158078066815199036615117766656,2268250674942032520365160043780197892423653190008832,2268285151894109448579234523810448843507138297856000,2268285151894109448579234523810541077227506845614080,2268285151894109448579234523839059743565461812412416,2268285151894109448579234523840535483091358576541696,2268285151894109448579313753181870480715287306960896,2268285151894109448579315628225816703005137276239872,2268285151894109448579709900039070900476400900243456,2268285151894109448579711865752453593863438972485632]
def witness27 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [64,145,146,164,169,170],Sum.inl [65,66,145,146,164,169,170],Sum.inl [68,73,74,145,146,164,169,170],Sum.inl [69,70,73,74,145,146,164,169,170],Sum.inr (6,6996542),Sum.inr (10,2206071),Sum.inr (8,6996535),Sum.inr (12,7043848),Sum.inl [64,148,153,154,164,169,170],Sum.inl [65,66,148,153,154,164,169,170],Sum.inl [68,73,74,148,153,154,164,169,170],Sum.inr (7,11788826),Sum.inl [80,96,148,153,154,164,169,170],Sum.inr (1,2207653),Sum.inr (6,7070252),Sum.inr (10,2207205)]

def word28 : List ℕ := [2268285151894109448702196633241494468322873973932032,2268285151894109448702198508285440690612723943211008,2268285151894109448708534892287264713403503363489792,2268285151894109448708536858000647406790541435731968,2268286935953725331029085846667910655376058776289280,2268286935953725331029085846668002889096427324047360,2268286935953725331029085846696521555434382290845696,2268286935953725331029085846697997294960279054974976,2268286935953725331029165082083961390657353658925056,2268286935953725331029167047797344084044391731167232,2268286935953725331029561222896532712345321378676736,2268286935953725331029563188609915405732359450918912,2268286935953725331152047962143585378264940325896192,2268286935953725331152049927856968071651978398138368,2268286935953725331158386215144726525272423841923072,2268286935953725331158388180858109218659461914165248]
def witness28 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inr (1,2207660),Sum.inr (9,2207660),Sum.inr (10,2207212),Sum.inr (15,2324140),Sum.inl [64,149,150,153,154,164,169,170],Sum.inl [65,66,149,150,153,154,164,169,170],Sum.inr (2,9736090),Sum.inr (8,9953818),Sum.inr (2,6852517),Sum.inr (4,2206078),Sum.inr (8,7070245),Sum.inr (12,6971272),Sum.inr (10,2206078),Sum.inr (15,2250430),Sum.inr (14,7072520),Sum.inr (16,2324826)]

def word29 : List ℕ := [2385170694424778761039036788528710607470917125668864,2385170694424778761039036788528802841191285673426944,2385170694424778761039036788533709675114892414156800,2385170694424778761039036788535185414640789178286080,2385170694424778761039036788557321507529240640225280,2385170694424778761039036788558797247055137404354560,2385170694424778761168337150960897379294136317771776,2385170694424778761168337157005526477367282191302656,2385170694424778761168337478579794494858642663145472,2385170694424778761168337575293860064028976639639552,2385170694424778761168339026004843601583986287050752,2385170694424778761168339122718909170754320263544832,2385170805928504753692152496207301970712724655570944,2385170805928504753692152496207394204433093203329024,2385170805928504753692152496212301038356699944058880,2385170805928504753692152496213776777882596708188160]
def witness29 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [64,144,165,166,169,170],Sum.inl [65,66,144,165,166,169,170],Sum.inl [68,72,144,165,166,169,170],Sum.inl [69,70,72,144,165,166,169,170],Sum.inl [68,73,74,144,165,166,169,170],Sum.inl [69,70,73,74,144,165,166,169,170],Sum.inr (0,6851390),Sum.inr (3,6851383),Sum.inr (3,2206519),Sum.inr (4,2177847),Sum.inr (4,2206519),Sum.inr (5,6852076),Sum.inl [64,145,146,165,166,169,170],Sum.inl [65,66,145,146,165,166,169,170],Sum.inl [68,72,145,146,165,166,169,170],Sum.inl [69,70,72,145,146,165,166,169,170]]

def word30 : List ℕ := [2385170805928504753692152496235912870771048170127360,2385170805928504753692152496237388610296944934256640,2385170805928504753713702557620089243408724075216896,2385170805928504753713702563664718341481869948747776,2385170805928504753713702885238986358973230420590592,2385170805928504753713704529378101034868908020989952,2385170805928504753720040810621230390416207591243776,2385170805928504753720040816665859488489353464774656,2385170805928504753720041234954193075151047913111552,2385170805928504753720042782379242181876391537016832,2385170805928504753815114605638347595528460331646976,2385170805928504753815114611682976693601606205177856,2385170805928504753815116480682293817818310300925952,2385170805928504753815116577396359386988644277420032,2385170805928504753821452858639488742535943847673856,2385170805928504753821452864684117840609089721204736]
def witness30 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [68,73,74,145,146,165,166,169,170],Sum.inr (6,11789960),Sum.inl [80,100,104,145,146,165,166,169,170],Sum.inr (7,6996542),Sum.inr (7,2352812),Sum.inr (13,7043848),Sum.inr (2,5016382),Sum.inr (8,5161534),Sum.inr (10,2178988),Sum.inr (14,5208840),Sum.inr (2,6851390),Sum.inr (8,6996542),Sum.inr (10,2207660),Sum.inr (14,7043848),Sum.inr (3,6851390),Sum.inr (9,6999944)]

def word31 : List ℕ := [2385170805928504753821453186258385858100450193047552,2385170805928504753821453282972451427270784169541632,2385170805928504753821454733683434964825793816952832,2385170805928504753821454830397500533996127793446912,2385176737926727562837908144708362495176885246361600,2385176737926727562837908144708454728897253794119680,2385176737926727562837908144713361562820860534849536,2385176737926727562837908144738449134761105525047296,2385176737926727562838383514892355454073001975218176,2385176737926727562838383520936984552146147848749056,2385176737926727562838383842511252569637508320591872,2385176737926727562838385486650367245533185920991232,2385176737926727562967208507140549267000104438464512,2385176737926727562967208513185178365073250311995392,2385176737926727562967208834759446382564610783838208,2385176737926727562967210478898561058460288384237568]
def witness31 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inr (11,6999496),Sum.inr (12,5164488),Sum.inr (12,6999496),Sum.inr (15,7043848),Sum.inl [64,148,152,165,166,169,170],Sum.inl [65,66,148,152,165,166,169,170],Sum.inl [68,72,148,152,165,166,169,170],Sum.inr (6,11788826),Sum.inl [80,97,98,148,152,165,166,169,170],Sum.inr (7,7070252),Sum.inr (7,2279102),Sum.inr (13,7072072),Sum.inr (3,2206526),Sum.inr (11,6999944),Sum.inr (9,2281370),Sum.inr (15,2325274)]

def word32 : List ℕ := [2385178521986343445287759467565824307045805724794880,2385178521986343445287759467565916540766174272552960,2385178521986343445287759467572299114215677777412096,2385178521986343445287759467595910946630026003480576,2385178521986343445288234837749817265941922453651456,2385178521986343445288234843794446364015068327182336,2385178521986343445288235262082779950676762775519232,2385178521986343445288236809507829057402106399424512,2385178521986343445417059829998011078869024916897792,2385178521986343445417059836042640176942170790428672,2385178521986343445417060254330973763603865238765568,2385178521986343445417061801756022870329208862670848,2385205282880581682035529310427751485079612901294080,2385205282880581682035529310427843718799981449052160,2385205282880581682035529310456362385137936415850496,2385205282880581682035529310457838124663833179979776]
def witness32 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inl [64,149,150,152,165,166,169,170],Sum.inl [65,66,149,150,152,165,166,169,170],Sum.inr (2,11571091),Sum.inr (8,11788819),Sum.inr (2,5017516),Sum.inr (8,5235244),Sum.inr (10,2177854),Sum.inr (14,5237064),Sum.inr (4,2177854),Sum.inr (12,5164936),Sum.inr (15,2278654),Sum.inr (16,2325267),Sum.inl [64,148,153,154,165,166,169,170],Sum.inl [65,66,148,153,154,165,166,169,170],Sum.inr (2,11571098),Sum.inr (8,11788826)]

def word33 : List ℕ := [2385205282880581682036004680611744443975729630150656,2385205282880581682036004686656373542048875503681536,2385205282880581682036006555655690666265579599429632,2385205282880581682036006652369756235435913575923712,2385205282880581682164829672859938256902832093396992,2385205282880581682164829678904567354975977966927872,2385205282880581682164831547903884479192682062675968,2385205282880581682164831644617950048363016039170048,2385207066940197564485380633285213296948533379727360,2385207066940197564485380633285305530668901927485440,2385207066940197564485380633290212364592508668215296,2385207066940197564485380633291688104118405432344576,2385207066940197564485380633313824197006856894283776,2385207066940197564485380633315299936532753658413056,2385207066940197564485459862656634934156682388832256,2385207066940197564485459868701264032229828262363136]
def witness33 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inr (2,6852524),Sum.inr (8,7070252),Sum.inr (10,2206526),Sum.inr (14,7072072),Sum.inr (4,2206526),Sum.inr (12,6999944),Sum.inr (15,2279102),Sum.inr (16,2325274),Sum.inl [64,149,150,153,154,165,166,169,170],Sum.inr (0,11644808),Sum.inr (0,11571098),Sum.inr (3,11571091),Sum.inr (3,11571098),Sum.inr (9,11789960),Sum.inr (0,6852524),Sum.inr (3,6852517)]

def word34 : List ℕ := [2385207066940197564485460190275532049721188734205952,2385207066940197564485460286989597618891522710700032,2385207066940197564485461737700581156446532358111232,2385207066940197564485461834414646725616866334605312,2385207066940197564485856003469206255844650108583936,2385207066940197564485856009513835353917795982114816,2385207066940197564485856331088103371409156453957632,2385207066940197564485856427802168940579490430451712,2385207066940197564485857878513152478134500077862912,2385207066940197564485857975227218047304834054356992,2385207066940197564506930694698000569644532799373312,2385207066940197564506930700742629667717678672904192,2385207066940197564506931022316897685209039144747008,2385207066940197564506932666456012361104716745146368,2385207066940197564513268947699141716652016315400192,2385207066940197564513268953743770814725162188931072]
def witness34 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inr (3,2207653),Sum.inr (4,2178981),Sum.inr (4,2207653),Sum.inr (5,6852517),Sum.inr (3,6852524),Sum.inr (9,7072520),Sum.inr (11,7072072),Sum.inr (12,5237064),Sum.inr (12,7072072),Sum.inr (15,7072072),Sum.inr (3,2207660),Sum.inr (11,7072520),Sum.inr (9,2353946),Sum.inr (15,2353498),Sum.inr (4,2178988),Sum.inr (12,5237512)]

def word35 : List ℕ := [2385207066940197564513269372032104401386856637267968,2385207066940197564513270919457153508112200261173248,2385207066940197564608342742716258921764269055803392,2385207066940197564608342748760888019837414929334272,2385207066940197564608344617760205144054119025082368,2385207066940197564608344714474270713224453001576448,2385207066940197564614680995717400068771752571830272,2385207066940197564614681001762029166844898445361152,2385207066940197564614681323336297184336258917203968,2385207066940197564614681420050362753506592893698048,2385207066940197564614682870761346291061602541109248,2385207066940197564614682967475411860231936517603328]
def witness35 : List (List ℕ ⊕ (ℕ × ℕ)) := [Sum.inr (15,2352364),Sum.inr (16,2353491),Sum.inr (4,2207660),Sum.inr (12,7072520),Sum.inr (15,2352812),Sum.inr (16,2353498),Sum.inr (5,6852524),Sum.inr (15,7072520),Sum.inr (15,2353946),Sum.inr (16,2353939),Sum.inr (16,2353946),Sum.inr (17,16434824)]

def wordBlocks : List (List ℕ) := [word0,word1,word2,word3,word4,word5,word6,word7,word8,word9,word10,word11,word12,word13,word14,word15,word16,word17,word18,word19,word20,word21,word22,word23,word24,word25,word26,word27,word28,word29,word30,word31,word32,word33,word34,word35]
def wordAt (i : ℕ) := ((wordBlocks[i/16]?.getD [])[i % 16]?).getD 0

def checkWitness (f : ℕ) : List ℕ ⊕ (ℕ × ℕ) → Bool
  | .inl xs => decide (xs.length < 10) && (encode xs == f)
  | .inr (j,p) => decide (j < classes.length) && (((List.range 8).map (fun i => (p >>> (3*i)) &&& 7)).eraseDups.length == 8) && (encode (((classes[j]?).getD []).map (applyBits p)) == f)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class0 : word0.length = witness0.length ∧ (word0.zip witness0).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class1 : word1.length = witness1.length ∧ (word1.zip witness1).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class2 : word2.length = witness2.length ∧ (word2.zip witness2).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class3 : word3.length = witness3.length ∧ (word3.zip witness3).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class4 : word4.length = witness4.length ∧ (word4.zip witness4).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class5 : word5.length = witness5.length ∧ (word5.zip witness5).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class6 : word6.length = witness6.length ∧ (word6.zip witness6).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class7 : word7.length = witness7.length ∧ (word7.zip witness7).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class8 : word8.length = witness8.length ∧ (word8.zip witness8).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class9 : word9.length = witness9.length ∧ (word9.zip witness9).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class10 : word10.length = witness10.length ∧ (word10.zip witness10).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class11 : word11.length = witness11.length ∧ (word11.zip witness11).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class12 : word12.length = witness12.length ∧ (word12.zip witness12).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class13 : word13.length = witness13.length ∧ (word13.zip witness13).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class14 : word14.length = witness14.length ∧ (word14.zip witness14).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class15 : word15.length = witness15.length ∧ (word15.zip witness15).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class16 : word16.length = witness16.length ∧ (word16.zip witness16).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class17 : word17.length = witness17.length ∧ (word17.zip witness17).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class18 : word18.length = witness18.length ∧ (word18.zip witness18).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class19 : word19.length = witness19.length ∧ (word19.zip witness19).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class20 : word20.length = witness20.length ∧ (word20.zip witness20).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class21 : word21.length = witness21.length ∧ (word21.zip witness21).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class22 : word22.length = witness22.length ∧ (word22.zip witness22).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class23 : word23.length = witness23.length ∧ (word23.zip witness23).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class24 : word24.length = witness24.length ∧ (word24.zip witness24).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class25 : word25.length = witness25.length ∧ (word25.zip witness25).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class26 : word26.length = witness26.length ∧ (word26.zip witness26).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class27 : word27.length = witness27.length ∧ (word27.zip witness27).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class28 : word28.length = witness28.length ∧ (word28.zip witness28).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class29 : word29.length = witness29.length ∧ (word29.zip witness29).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class30 : word30.length = witness30.length ∧ (word30.zip witness30).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class31 : word31.length = witness31.length ∧ (word31.zip witness31).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class32 : word32.length = witness32.length ∧ (word32.zip witness32).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class33 : word33.length = witness33.length ∧ (word33.zip witness33).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class34 : word34.length = witness34.length ∧ (word34.zip witness34).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem class35 : word35.length = witness35.length ∧ (word35.zip witness35).all (fun t => checkWitness t.1 t.2) = true := by decide +kernel
def lut0 : ℕ := 2545710811297067931009880215615402881929191501533948963313810828383319499093623953112232093406158818802901626315855794212103583352745816250355225536165193202760598308027019985832131165365018660
def low0 : ℕ := 41343779798502762087424
def lut1 : ℕ := 2545884854594554208398507306158389890593005872688299076882980994244796390233257766165477340678426331775665542333972194384752337850732137675137191595341369665805083414556972490834003710590394404
def low1 : ℕ := 41348391484521190523904
def lut2 : ℕ := 2546058897892040485787134396701376899256820243842649190452151160106273281372891579218722587950693844748429458352088594557401092348718459099919157654517546128849568521086924995835876255815770148
def low2 : ℕ := 41353003170539618960384
def lut3 : ℕ := 2546581027784499222978141484237840683979610398645986262033937533182690580998179936163228974593212654976623825414395468476474094357599663521347330158816520150931541777266518691585637620178296868
def low3 : ℕ := 41361073621071867937792
def lut4 : ℕ := 2545763024336107977309321716125312019055370781970035877257920561880977247262501436502675321133121031112202757505883786772306448236002725041524070483528686047815659246477284440867388001441882148
def low4 : ℕ := 41344932721106880562176
def lut5 : ℕ := 2545937067633594254697948806668299027719185153124385990827090727742454138402135249555920568405388544084966673524000186944955202733989046466306036542704862510860144353007236945869260546667257892
def low5 : ℕ := 41349544407125308998656
def lut6 : ℕ := 2546111110931080532086575897211286036382999524278736104396260893603931029541769062609165815677656057057730589542116587117603957231975367891088002601881038973904629459537189450871133091892633636
def low6 : ℕ := 41354156093143737435136
def lut7 : ℕ := 2546581027834293409804713399739989619532690293241793906712285641036199129146598263768560011748115690677082515423826118475433170246995477114595822245466386333755391749649482451447464292750794788
def low7 : ℕ := 41361073622171379565568
def lut8 : ℕ := 2545711015337047484026065971587691140131037250419029552580886684608004787214099906099859220803626236055246957815601310917318381371523220127120232505033653602766815003149328875201948144533315620
def low8 : ℕ := 41343784304301412713472
def lut9 : ℕ := 2545885058667729885965741005798777435731172721238613238444671856164457435152133889335240651862399190393194051136025525887152013374111429784942907671024879436531616164563707828541353196135718948
def low9 : ℕ := 41348395991419352777728
def lut10 : ℕ := 2546059101998412287905416040009863731331308192058196924308457027720910083090167872570622082921172144731141144456449740856985645376699639442765582837016105270296417325978086781880758247738122276
def low10 : ℕ := 41353007678537292841984
def lut11 : ℕ := 2546581231940665211922995043048476451607178241457341649499980074373135213001470196250088933302912973540550680721192829994704301376657453119981207940489065390481839044958613250416148453886337060
def low11 : ℕ := 41361078130169053447168
def lut12 : ℕ := 2545763228442479779427603359433798851129858730185583611114220751068080489550945313257628605902627026816005108858982525423500395582801852198553596590014363827396710895271471900216258212969652260
def low12 : ℕ := 41344937229104554443776
def lut13 : ℕ := 2545937271739966056816230449976785859793673101339933724683390916929557380690579126310873853174894539788769024877098925596149150080788173623335562649190540290441196001801424405218130758195028004
def low13 : ℕ := 41349548915122982880256
def lut14 : ℕ := 2546111315037452334204857540519772868457487472494283838252561082791034271830212939364119100447162052761532940895215325768797904578774495048117528708366716753485681108331376910220003303420403748
def low14 : ℕ := 41354160601141411316736
def lut15 : ℕ := 2546581231940665211922995043048476451607178241457341649499980074373135213001470196250088933302912973540550680721192829994704301376657453119981207940489065390481839044958613250416148453886337060
def low15 : ℕ := 41361078130169053447168
def lut16 : ℕ := 2546319963087240558992884952782099185514461488812403837674313162402277625227369090375593355535887047595903724308020396939254753559493065014403236093869710515248338139954629485033028081428799524
def low16 : ℕ := 41357614863155114017792
def lut17 : ℕ := 2546372176076486497611483009183310289880828625426638802368587150633305635729915590009873324610265845413593305080531250854522063793975585803243457837950174095437890896144201200938488392121917476
def low17 : ℕ := 41358767784659721913344
def lut18 : ℕ := 2546424389065732436230081065584521394247195762040873767062861138864333646232462089644153293684644643231282885853042104769789374028458106592083679582030637675627443652333772916843948702815035428
def low18 : ℕ := 41359920706164329808896
def lut19 : ℕ := 2546581028033470157111001061748585361745009871625024485425678072450233321742795757997120163151598902369983086596885771074395741839487963872190259174130471502453114634545751324328629410969231396
def low19 : ℕ := 41361073627668937704448
def lut20 : ℕ := 2546581028116460167734852729623720170095495358374187370387733040592965468116517322784094823519942128618024362486481352182734977907405029272811399866102787911617330239003361146581682915614203940
def low20 : ℕ := 41361073628768446186496
def lut21 : ℕ := 2546581028116460246880581201017171069456367552473446104467165016828844497563036770578268665734868736085461747537500424666329159681971423207817485749491047734149390957204452247977981900499263524
def low21 : ℕ := 41361073628768447235072
def lut22 : ℕ := 2546581028116460326026309672410621968817239746572704838546596993064723527009556218372442507949795343552899132588519497149923341456537817142823571632879307556681451675405543349374280885384323108
def low22 : ℕ := 41361073628768448283648
def lut23 : ℕ := 2546581028116460468488620920918833587666809695951370559889574550256813557035312925266270855839299568710990152013960172880791933079324504116625149811347193185637597102882925738583193172362469412
def low23 : ℕ := 41361073628768449332224
def lut24 : ℕ := 2546320167160416236560118652422486734085027167428022859704085838577441102468473917359999283374571406630553254871154241214161731629409798673172597914326590046509377306111317217671334638947213348
def low24 : ℕ := 41357619368953764643840
def lut25 : ℕ := 2546372380182858299729764652491797125387715403707491396692974832503444869769420587176415436235455645813426012945972909926613919368494207695053528765222102997419246117185315381914327456017358884
def low25 : ℕ := 41358772291557884167168
def lut26 : ℕ := 2546424593205300362899410652561107516690403639986959933681863826429448637070367256992831589096339884996298771020791578639066107107578616716934459616117615948329114928259313546157320273087504420
def low26 : ℕ := 41359925214162003690496
def lut27 : ℕ := 2546581232272626457433474479729469355294377538762725947355617091447258189036078996736079602244318367666194926190182680827581728221379911075873986782261510490823117520755666512766037137396146212
def low27 : ℕ := 41361078136766123213824
def lut28 : ℕ := 2546581232272626156679706288434355937723063201185542757853775581777994729620953677731289475242066982859346424384975907244256373875281509520953304492038953277296960683082743950100548986205184036
def low28 : ℕ := 41361078136766120068096
def lut29 : ℕ := 2546581232272626235825434759827806837083935395284801491933207558013873759067473125525463317456993590326783809435994979727850555649847903455959390375427213099829021401283835051496847971090243620
def low29 : ℕ := 41361078136766121116672
def lut30 : ℕ := 2546581232272626314971163231221257736444807589384060226012639534249752788513992573319637159671920197794221194487014052211444737424414297390965476258815472922361082119484926152893146955975303204
def low30 : ℕ := 41361078136766122165248
def lut31 : ℕ := 2546581232272626457433474479729469355294377538762725947355617091447258189036078996736079602244318367666194926190182680827581728221379911075873986782261510490823117520755666512766037137396146212
def low31 : ℕ := 41361078136766123213824
def lut32 : ℕ := 2545711678678606325341600319381739840986222339604896149856194231881613064684187108678041849208103527483462411728706984442705334853952388155726666227085657626581822997449308519748989981196099620
def low32 : ℕ := 41343800077895224787968
def lut33 : ℕ := 2545885722142073225485467128265230327614041503090981696328659283727409658253917988871838909201610910940880514202315517665696489376002806405227713720406627111373517887214398250025260552818860068
def low33 : ℕ := 41348411768311699735552
def lut34 : ℕ := 2546059765605540125629333937148720814241860666577067242801124335573206251823648869065635969195118294398298616675924050888687643898053224654728761213727596596165212776979487980301531124441620516
def low34 : ℕ := 41353023458728174683136
def lut35 : ℕ := 2546581895680577547851104714859737728977813238708018718840720384726230698862641287777631674938289878920840138511257218175202311364849306147576551967439698440321054049730979330822443669288722468
def low35 : ℕ := 41361093913658470171648
def lut36 : ℕ := 2545763891701048309365517848057599332928041655175713848907521262761434630137766547342330205158595384668070091443745265914562503895206500016367443138230124179641769752663755460645793275326832676
def low36 : ℕ := 41344953000499343262720
def lut37 : ℕ := 2545937935164515209509384656941089819555860818661799395379986314607231223707497427536127265152102768125488193917353799137553658417256918265868490631551093664433464642428845190922063846949593124
def low37 : ℕ := 41349564690915818210304
def lut38 : ℕ := 2546111978627982109653251465824580306183679982147884941852451366453027817277228307729924325145610151582906296390962332360544812939307336515369538124872063149225159532193934921198334418572353572
def low38 : ℕ := 41354176381332293157888
def lut39 : ℕ := 2546581895780165921504248545864035600083973027899634008197416600433247795156953749563775870005377813223268640230419631757825306295599665264358551542090280337511770092886920853861885776702283812
def low39 : ℕ := 41361093914757981799424
def lut40 : ℕ := 2545711984697080499177069023755048105030894560573423325409920753385374668860787546075076357856572833451325706373231137079009924895974686616194503623448556199869169173193700012940560025058877476
def low40 : ℕ := 41343804583693875414016
def lut41 : ℕ := 2545886028160547399320935832638538591658713724059508871882385805231171262430518426268873417850080216908743808846839670302001079418025104865695551116769525684660864062958789743216830596681637924
def low41 : ℕ := 41348416274110350361600
def lut42 : ℕ := 2546060071624014299464802641522029078286532887545594418354850857076967856000249306462670477843587600366161911320448203524992233940075523115196598610090495169452558952723879473493101168304398372
def low42 : ℕ := 41353027964526825309184
def lut43 : ℕ := 2546582202014414904921528884079989251525324792116660986288721017760012955347148910625776953696304400807312330853926635763813866776845958668931635093136588386286859233551542337667965992250187812
def low43 : ℕ := 41361098422755655681024
def lut44 : ℕ := 2545764197736120545476510524264957242157073841009510239354030486883032417029665029465519585583535045760626837563259129639212789779231595407363348570812049044924230111643964467975816861135740964
def low44 : ℕ := 41344957506297993888768
def lut45 : ℕ := 2545938241199587445620377333148447728784893004495595785826495538728829010599395909659316645577042429218044940036867662862203944301282013656864396064133018529715925001409054198252087432758501412
def low45 : ℕ := 41349569196714468836352
def lut46 : ℕ := 2546112284663054345764244142031938215412712167981681332298960590574625604169126789853113705570549812675463042510476196085195098823332431906365443557453988014507619891174143928528358004381261860
def low46 : ℕ := 41354180887130943783936
def lut47 : ℕ := 2546582202014414904921528884079989251525324792116660986288721017760012955347148910625776953696304400807312330853926635763813866776845958668931635093136588386286859233551542337667965992250187812
def low47 : ℕ := 41361098422755655681024
def lut48 : ℕ := 2546320830734347949732988605893251552747264855895398029409515668643916618205107121257880530763587369163692740389898653027278332373434803760426540025680214179935801213472335916413051276764454948
def low48 : ℕ := 41357635149144646484992
def lut49 : ℕ := 2546373043723593888351586662294462657113631992509632994103789656874944628707653620892160499837966166981382321162409506942545642607917324549266761769760677760125353969661907632318511587457572900
def low49 : ℕ := 41358788070649254380544
def lut50 : ℕ := 2546425256712839826970184718695673761479999129123867958798063645105972639210200120526440468912344964799071901934920360857812952842399845338106983513841141340314906725851479348223971898150690852
def low50 : ℕ := 41359940992153862276096
def lut51 : ℕ := 2546581895680577547851104714859737728977813238708018718840720384726230698862641287777631674938289878920840138511257218175202311364849306147576551967439698440321054049730979330822443669288722468
def low51 : ℕ := 41361093913658470171648
def lut52 : ℕ := 2546581895780165620750480354568922182512658690322450818695575090742322853756509564468529364271550649560889289314301046633426355252785556865010139871955115365962053360040566408540486047740534820
def low52 : ℕ := 41361093914757978653696
def lut53 : ℕ := 2546581895780165699896208825962373081873530884421709552775007066978201883203029012262703206486477257028326674365320119117020537027351950800016225755343375188494114078241657509936785032625594404
def low53 : ℕ := 41361093914757979702272
def lut54 : ℕ := 2546581895780165779041937297355823981234403078520968286854439043214080912649548460056877048701403864495764059416339191600614718801918344735022311638731635011026174796442748611333084017510653988
def low54 : ℕ := 41361093914757980750848
def lut55 : ℕ := 2546581895780165921504248545864035600083973027899634008197416600433247795156953749563775870005377813223268640230419631757825306295599665264358551542090280337511770092886920853861885776702283812
def low55 : ℕ := 41361093914757981799424
def lut56 : ℕ := 2546321136819214372670553197602758404394174596455611782493413732056522333345616442332913098581325792049498058405109094713985112250130265525969971001474384020965153666149578610043641403216568356
def low56 : ℕ := 41357639654943297111040
def lut57 : ℕ := 2546373349858254498115723169506118440881222797600349534375085428600362283361861156875484123218680386357064267954917474514782995831217471478378969888588923263870136660459394288425087762232844324
def low57 : ℕ := 41358792577547416634368
def lut58 : ℕ := 2546425562897294623560893141409478477368270998745087286256757125144202233378105871418055147856034980664630477504725854315580879412304677430787968775703462506775119654769209966806534121249120292
def low58 : ℕ := 41359945500151536157696
def lut59 : ℕ := 2546582202014414904921528884079989251525324792116660986288721017760012955347148910625776953696304400807312330853926635763813866776845958668931635093136588386286859233551542337667965992250187812
def low59 : ℕ := 41361098422755655681024
def lut60 : ℕ := 2546582202014414604167760692784875833954010454539477796786879508063672643450375009007916353279583292431050267660080097754146516559852923558476291078023271475231252526911829921682588368845742116
def low60 : ℕ := 41361098422755652535296
def lut61 : ℕ := 2546582202014414683313489164178326733314882648638736530866311484299551672896894456802090195494509899898487652711099170237740698334419317493482376961411531297763313245112921023078887353730801700
def low61 : ℕ := 41361098422755653583872
def lut62 : ℕ := 2546582202014414762459217635571777632675754842737995264945743460535430702343413904596264037709436507365925037762118242721334880108985711428488462844799791120295373963314012124475186338615861284
def low62 : ℕ := 41361098422755654632448
def lut63 : ℕ := 2546582202014414904921528884079989251525324792116660986288721017760012955347148910625776953696304400807312330853926635763813866776845958668931635093136588386286859233551542337667965992250187812
def low63 : ℕ := 41361098422755655681024
def digit (x i : ℕ) := (x >>> (10*i)) &&& 1023
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels0 : (∀ a b : Fin 8, top 0 a b = wordAt (digit lut0 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 0 a = wordAt (digit low0 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels1 : (∀ a b : Fin 8, top 1 a b = wordAt (digit lut1 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 1 a = wordAt (digit low1 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels2 : (∀ a b : Fin 8, top 2 a b = wordAt (digit lut2 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 2 a = wordAt (digit low2 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels3 : (∀ a b : Fin 8, top 3 a b = wordAt (digit lut3 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 3 a = wordAt (digit low3 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels4 : (∀ a b : Fin 8, top 4 a b = wordAt (digit lut4 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 4 a = wordAt (digit low4 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels5 : (∀ a b : Fin 8, top 5 a b = wordAt (digit lut5 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 5 a = wordAt (digit low5 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels6 : (∀ a b : Fin 8, top 6 a b = wordAt (digit lut6 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 6 a = wordAt (digit low6 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels7 : (∀ a b : Fin 8, top 7 a b = wordAt (digit lut7 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 7 a = wordAt (digit low7 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels8 : (∀ a b : Fin 8, top 8 a b = wordAt (digit lut8 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 8 a = wordAt (digit low8 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels9 : (∀ a b : Fin 8, top 9 a b = wordAt (digit lut9 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 9 a = wordAt (digit low9 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels10 : (∀ a b : Fin 8, top 10 a b = wordAt (digit lut10 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 10 a = wordAt (digit low10 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels11 : (∀ a b : Fin 8, top 11 a b = wordAt (digit lut11 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 11 a = wordAt (digit low11 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels12 : (∀ a b : Fin 8, top 12 a b = wordAt (digit lut12 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 12 a = wordAt (digit low12 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels13 : (∀ a b : Fin 8, top 13 a b = wordAt (digit lut13 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 13 a = wordAt (digit low13 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels14 : (∀ a b : Fin 8, top 14 a b = wordAt (digit lut14 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 14 a = wordAt (digit low14 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels15 : (∀ a b : Fin 8, top 15 a b = wordAt (digit lut15 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 15 a = wordAt (digit low15 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels16 : (∀ a b : Fin 8, top 16 a b = wordAt (digit lut16 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 16 a = wordAt (digit low16 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels17 : (∀ a b : Fin 8, top 17 a b = wordAt (digit lut17 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 17 a = wordAt (digit low17 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels18 : (∀ a b : Fin 8, top 18 a b = wordAt (digit lut18 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 18 a = wordAt (digit low18 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels19 : (∀ a b : Fin 8, top 19 a b = wordAt (digit lut19 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 19 a = wordAt (digit low19 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels20 : (∀ a b : Fin 8, top 20 a b = wordAt (digit lut20 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 20 a = wordAt (digit low20 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels21 : (∀ a b : Fin 8, top 21 a b = wordAt (digit lut21 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 21 a = wordAt (digit low21 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels22 : (∀ a b : Fin 8, top 22 a b = wordAt (digit lut22 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 22 a = wordAt (digit low22 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels23 : (∀ a b : Fin 8, top 23 a b = wordAt (digit lut23 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 23 a = wordAt (digit low23 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels24 : (∀ a b : Fin 8, top 24 a b = wordAt (digit lut24 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 24 a = wordAt (digit low24 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels25 : (∀ a b : Fin 8, top 25 a b = wordAt (digit lut25 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 25 a = wordAt (digit low25 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels26 : (∀ a b : Fin 8, top 26 a b = wordAt (digit lut26 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 26 a = wordAt (digit low26 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels27 : (∀ a b : Fin 8, top 27 a b = wordAt (digit lut27 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 27 a = wordAt (digit low27 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels28 : (∀ a b : Fin 8, top 28 a b = wordAt (digit lut28 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 28 a = wordAt (digit low28 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels29 : (∀ a b : Fin 8, top 29 a b = wordAt (digit lut29 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 29 a = wordAt (digit low29 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels30 : (∀ a b : Fin 8, top 30 a b = wordAt (digit lut30 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 30 a = wordAt (digit low30 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels31 : (∀ a b : Fin 8, top 31 a b = wordAt (digit lut31 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 31 a = wordAt (digit low31 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels32 : (∀ a b : Fin 8, top 32 a b = wordAt (digit lut32 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 32 a = wordAt (digit low32 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels33 : (∀ a b : Fin 8, top 33 a b = wordAt (digit lut33 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 33 a = wordAt (digit low33 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels34 : (∀ a b : Fin 8, top 34 a b = wordAt (digit lut34 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 34 a = wordAt (digit low34 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels35 : (∀ a b : Fin 8, top 35 a b = wordAt (digit lut35 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 35 a = wordAt (digit low35 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels36 : (∀ a b : Fin 8, top 36 a b = wordAt (digit lut36 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 36 a = wordAt (digit low36 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels37 : (∀ a b : Fin 8, top 37 a b = wordAt (digit lut37 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 37 a = wordAt (digit low37 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels38 : (∀ a b : Fin 8, top 38 a b = wordAt (digit lut38 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 38 a = wordAt (digit low38 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels39 : (∀ a b : Fin 8, top 39 a b = wordAt (digit lut39 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 39 a = wordAt (digit low39 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels40 : (∀ a b : Fin 8, top 40 a b = wordAt (digit lut40 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 40 a = wordAt (digit low40 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels41 : (∀ a b : Fin 8, top 41 a b = wordAt (digit lut41 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 41 a = wordAt (digit low41 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels42 : (∀ a b : Fin 8, top 42 a b = wordAt (digit lut42 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 42 a = wordAt (digit low42 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels43 : (∀ a b : Fin 8, top 43 a b = wordAt (digit lut43 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 43 a = wordAt (digit low43 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels44 : (∀ a b : Fin 8, top 44 a b = wordAt (digit lut44 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 44 a = wordAt (digit low44 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels45 : (∀ a b : Fin 8, top 45 a b = wordAt (digit lut45 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 45 a = wordAt (digit low45 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels46 : (∀ a b : Fin 8, top 46 a b = wordAt (digit lut46 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 46 a = wordAt (digit low46 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels47 : (∀ a b : Fin 8, top 47 a b = wordAt (digit lut47 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 47 a = wordAt (digit low47 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels48 : (∀ a b : Fin 8, top 48 a b = wordAt (digit lut48 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 48 a = wordAt (digit low48 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels49 : (∀ a b : Fin 8, top 49 a b = wordAt (digit lut49 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 49 a = wordAt (digit low49 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels50 : (∀ a b : Fin 8, top 50 a b = wordAt (digit lut50 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 50 a = wordAt (digit low50 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels51 : (∀ a b : Fin 8, top 51 a b = wordAt (digit lut51 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 51 a = wordAt (digit low51 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels52 : (∀ a b : Fin 8, top 52 a b = wordAt (digit lut52 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 52 a = wordAt (digit low52 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels53 : (∀ a b : Fin 8, top 53 a b = wordAt (digit lut53 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 53 a = wordAt (digit low53 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels54 : (∀ a b : Fin 8, top 54 a b = wordAt (digit lut54 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 54 a = wordAt (digit low54 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels55 : (∀ a b : Fin 8, top 55 a b = wordAt (digit lut55 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 55 a = wordAt (digit low55 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels56 : (∀ a b : Fin 8, top 56 a b = wordAt (digit lut56 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 56 a = wordAt (digit low56 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels57 : (∀ a b : Fin 8, top 57 a b = wordAt (digit lut57 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 57 a = wordAt (digit low57 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels58 : (∀ a b : Fin 8, top 58 a b = wordAt (digit lut58 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 58 a = wordAt (digit low58 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels59 : (∀ a b : Fin 8, top 59 a b = wordAt (digit lut59 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 59 a = wordAt (digit low59 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels60 : (∀ a b : Fin 8, top 60 a b = wordAt (digit lut60 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 60 a = wordAt (digit low60 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels61 : (∀ a b : Fin 8, top 61 a b = wordAt (digit lut61 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 61 a = wordAt (digit low61 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels62 : (∀ a b : Fin 8, top 62 a b = wordAt (digit lut62 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 62 a = wordAt (digit low62 a.val)) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem labels63 : (∀ a b : Fin 8, top 63 a b = wordAt (digit lut63 (8*a.val+b.val))) ∧ (∀ a : Fin 8, sh2 63 a = wordAt (digit low63 a.val)) := by decide +kernel

end MoonPrize.Wiring

namespace MoonPrize.Bridge

open MoonPrize.Shape MoonPrize.Wiring

def bitsOf {α : Type*} (f : α → ℕ) (S : Finset α) : ℕ :=
  S.fold (· ||| ·) 0 (fun a => 2 ^ f a)

theorem testBit_bitsOf {α : Type*} [DecidableEq α] (f : α → ℕ) (S : Finset α) (v : ℕ) :
    (bitsOf f S).testBit v = true ↔ ∃ a ∈ S, f a = v := by
  induction S using Finset.induction_on with
  | empty => simp [bitsOf]
  | @insert a S ha ih =>
    unfold bitsOf at ih ⊢
    rw [Finset.fold_insert ha, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, ih]
    constructor
    · rintro (h | ⟨b, hb, h⟩)
      · exact ⟨a, Finset.mem_insert_self _ _, of_decide_eq_true h⟩
      · exact ⟨b, Finset.mem_insert_of_mem hb, h⟩
    · rintro ⟨b, hb, h⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact Or.inl (decide_eq_true h)
      · exact Or.inr ⟨b, hb, h⟩

theorem bitsOf_empty {α : Type*} (f : α → ℕ) : bitsOf f ∅ = 0 := by
  simp [bitsOf]

theorem bitsOf_insert {α : Type*} [DecidableEq α] (f : α → ℕ) (a : α) (S : Finset α) :
    bitsOf f (insert a S) = 2 ^ f a ||| bitsOf f S := by
  apply Nat.eq_of_testBit_eq
  intro v
  rw [Bool.eq_iff_iff, Nat.testBit_or, Bool.or_eq_true, testBit_bitsOf, testBit_bitsOf,
    Nat.testBit_two_pow]
  constructor
  · rintro ⟨b, hb, h⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr ⟨b, hb, h⟩
  · rintro (h | ⟨b, hb, h⟩)
    · exact ⟨a, Finset.mem_insert_self _ _, of_decide_eq_true h⟩
    · exact ⟨b, Finset.mem_insert_of_mem hb, h⟩

theorem bitsOf_injective {α : Type*} [DecidableEq α] (f : α → ℕ) (hf : Function.Injective f) :
    Function.Injective (bitsOf f) := by
  intro S T h
  ext a
  have e := congrArg (fun x => x.testBit (f a) = true) h
  simp only [testBit_bitsOf] at e
  constructor
  · intro ha
    obtain ⟨b, hb, hab⟩ := e.mp ⟨a, ha, rfl⟩
    exact hf hab ▸ hb
  · intro ha
    obtain ⟨b, hb, hab⟩ := e.mpr ⟨a, ha, rfl⟩
    exact hf hab ▸ hb

theorem land_eq_zero_iff (x y : ℕ) :
    x &&& y = 0 ↔ ∀ v, x.testBit v = true → y.testBit v = false := by
  constructor
  · intro h v hx
    have e := congrArg (fun z => z.testBit v) h
    simp only [Nat.testBit_and, hx, Bool.true_and, Nat.zero_testBit] at e
    exact e
  · intro h
    apply Nat.eq_of_testBit_eq
    intro v
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hx : x.testBit v
    · rfl
    · rw [h v hx]; rfl

def idx {k : ℕ} (t : Fin k × Bool) : ℕ := 2 * t.1.val + t.2.toNat

def maskCode {k : ℕ} (M : Finset (Fin k × Bool)) : ℕ := bitsOf idx M

def setCode {k : ℕ} (N : Finset (Fin k)) : ℕ := bitsOf (fun i : Fin k => i.val) N

def famCode {k : ℕ} (F : Finset (Finset (Fin k × Bool))) : ℕ := bitsOf maskCode F

theorem idx_injective {k : ℕ} : Function.Injective (idx (k := k)) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  simp only [idx] at h
  have hi : i = i' := by
    apply Fin.ext
    cases b <;> cases b' <;> simp only [Bool.toNat_false, Bool.toNat_true] at h <;> omega
  subst hi
  have hb : b = b' := by
    cases b <;> cases b' <;> simp only [Bool.toNat_false, Bool.toNat_true] at h <;>
      first | rfl | (exfalso; omega)
  rw [hb]

theorem maskCode_injective {k : ℕ} : Function.Injective (maskCode (k := k)) :=
  bitsOf_injective idx idx_injective

theorem testBit_maskCode {k : ℕ} (M : Finset (Fin k × Bool)) (v : ℕ) :
    (maskCode M).testBit v = true ↔ ∃ t ∈ M, idx t = v := testBit_bitsOf _ _ _

theorem testBit_setCode {k : ℕ} (N : Finset (Fin k)) (v : ℕ) :
    (setCode N).testBit v = true ↔ ∃ i ∈ N, i.val = v := testBit_bitsOf _ _ _

theorem testBit_famCode {k : ℕ} (F : Finset (Finset (Fin k × Bool))) (m : ℕ) :
    (famCode F).testBit m = true ↔ ∃ M ∈ F, maskCode M = m := testBit_bitsOf _ _ _

theorem disjoint_iff_land {k : ℕ} (M Y : Finset (Fin k × Bool)) :
    Disjoint M Y ↔ maskCode M &&& maskCode Y = 0 := by
  rw [land_eq_zero_iff, Finset.disjoint_left]
  constructor
  · intro hd v hv
    obtain ⟨a, ha, rfl⟩ := (testBit_maskCode M v).mp hv
    apply Bool.eq_false_iff.mpr
    intro hy
    obtain ⟨b, hb, e⟩ := (testBit_maskCode Y _).mp hy
    exact hd ha (idx_injective e ▸ hb)
  · intro h a ha hb
    have e := h (idx a) ((testBit_maskCode M _).mpr ⟨a, ha, rfl⟩)
    rw [(testBit_maskCode Y _).mpr ⟨a, hb, rfl⟩] at e
    exact Bool.noConfusion e

theorem maskCode_lt {k : ℕ} (hk : k ≤ 4) (Y : Finset (Fin k × Bool)) : maskCode Y < 256 := by
  show maskCode Y < 2 ^ 8
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨⟨g, b⟩, -, e⟩ := (testBit_maskCode Y i).mp h
  have hg := g.isLt
  simp only [idx] at e
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] at e <;> omega

section Abstract

variable {k : ℕ} (rs : Fin k → Bool → Finset (Fin k)) (s : Fin k → Bool)

theorem tagsFuel_succ : ∀ d : ℕ, ∀ i : Fin k, i.val < d →
    tagsFuel rs s (d + 1) i = tagsFuel rs s d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i _
    show insert (i, s i) (((rs i (s i)).filter (· < i)).biUnion (tagsFuel rs s (d + 1))) =
      insert (i, s i) (((rs i (s i)).filter (· < i)).biUnion (tagsFuel rs s d))
    congr 1
    apply Finset.biUnion_congr rfl
    intro r hr
    have hlt : r.val < i.val := (Finset.mem_filter.mp hr).2
    exact ih r (by omega)

theorem tagsFuel_stable (i : Fin k) : ∀ d : ℕ, i.val < d →
    tagsFuel rs s d i = tagsFuel rs s (i.val + 1) i := by
  intro d
  induction d with
  | zero => intro hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro hi
    by_cases h : i.val < d
    · rw [tagsFuel_succ rs s d i h, ih h]
    · have e : d = i.val := by omega
      rw [e]

theorem tags_unfold (i : Fin k) :
    tagsFuel rs s k i = insert (i, s i) (mask rs ((rs i (s i)).filter (· < i)) s) := by
  rw [tagsFuel_stable rs s i k i.isLt]
  show insert (i, s i) (((rs i (s i)).filter (· < i)).biUnion (tagsFuel rs s i.val)) =
    insert (i, s i) (((rs i (s i)).filter (· < i)).biUnion (tagsFuel rs s k))
  congr 1
  apply Finset.biUnion_congr rfl
  intro r hr
  have hlt : r.val < i.val := (Finset.mem_filter.mp hr).2
  rw [tagsFuel_stable rs s r k r.isLt, tagsFuel_stable rs s r i.val hlt]

theorem mask_step (N : Finset (Fin k)) (j : Fin k) (hj : j ∈ N) :
    mask rs N s =
      insert (j, s j) (mask rs (N.erase j ∪ (rs j (s j)).filter (· < j)) s) := by
  ext t
  simp only [mask, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro ⟨i, hi, ht⟩
    by_cases e : i = j
    · rw [e, tags_unfold] at ht
      rcases Finset.mem_insert.mp ht with h | h
      · exact Or.inl h
      · obtain ⟨r, hr, h⟩ := Finset.mem_biUnion.mp h
        exact Or.inr ⟨r, Or.inr hr, h⟩
    · exact Or.inr ⟨i, Or.inl ⟨e, hi⟩, ht⟩
  · rintro (h | ⟨r, ⟨-, hr⟩ | hr, h⟩)
    · exact ⟨j, hj, by rw [tags_unfold]; exact Finset.mem_insert.mpr (Or.inl h)⟩
    · exact ⟨r, hr, h⟩
    · refine ⟨j, hj, ?_⟩
      rw [tags_unfold]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, hr, h⟩)

end Abstract

def fam (L R : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | j+1, o => if o.testBit j then
      (fam L R j (o ||| L j) <<< 2 ^ (2*j)) ||| (fam L R j (o ||| R j) <<< 2 ^ (2*j+1))
    else fam L R j o

def nm (L R : ℕ → ℕ) (s : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j+1, o => if o.testBit j then
      2 ^ (2*j + (s j).toNat) ||| nm L R s j (o ||| cond (s j) (R j) (L j))
    else nm L R s j o

theorem fam_succ_pos (L R : ℕ → ℕ) {j o : ℕ} (h : o.testBit j = true) :
    fam L R (j+1) o =
      (fam L R j (o ||| L j) <<< 2 ^ (2*j)) ||| (fam L R j (o ||| R j) <<< 2 ^ (2*j+1)) := by
  simp [fam, h]

theorem fam_succ_neg (L R : ℕ → ℕ) {j o : ℕ} (h : o.testBit j = false) :
    fam L R (j+1) o = fam L R j o := by
  simp [fam, h]

theorem nm_succ_pos (L R : ℕ → ℕ) {j o : ℕ} (h : o.testBit j = true) (s : ℕ → Bool) :
    nm L R s (j+1) o =
      2 ^ (2*j + (s j).toNat) ||| nm L R s j (o ||| cond (s j) (R j) (L j)) := by
  simp [nm, h]

theorem nm_succ_neg (L R : ℕ → ℕ) {j o : ℕ} (h : o.testBit j = false) (s : ℕ → Bool) :
    nm L R s (j+1) o = nm L R s j o := by
  simp [nm, h]

theorem nm_lt (L R : ℕ → ℕ) (s : ℕ → Bool) : ∀ j o, nm L R s j o < 2 ^ (2*j) := by
  intro j
  induction j with
  | zero => intro o; simp [nm]
  | succ j ih =>
    intro o
    have up : (2:ℕ) ^ (2*j) < 2 ^ (2*(j+1)) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    cases hb : o.testBit j
    · rw [nm_succ_neg L R hb]
      exact (ih o).trans up
    · rw [nm_succ_pos L R hb]
      apply Nat.or_lt_two_pow
      · apply Nat.pow_lt_pow_right (by norm_num)
        cases s j <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      · exact (ih _).trans up

theorem nm_congr_s (L R : ℕ → ℕ) (s s' : ℕ → Bool) : ∀ j o, (∀ i, i < j → s i = s' i) →
    nm L R s j o = nm L R s' j o := by
  intro j
  induction j with
  | zero => intro o _; rfl
  | succ j ih =>
    intro o h
    have ih' : ∀ o, nm L R s j o = nm L R s' j o :=
      fun o => ih o (fun i hi => h i (Nat.lt_succ_of_lt hi))
    cases hb : o.testBit j
    · rw [nm_succ_neg L R hb, nm_succ_neg L R hb, ih']
    · rw [nm_succ_pos L R hb, nm_succ_pos L R hb, ih', h j (Nat.lt_succ_self j)]

theorem nm_congr_o (L R : ℕ → ℕ) (s : ℕ → Bool) : ∀ j o o',
    (∀ i, i < j → o.testBit i = o'.testBit i) → nm L R s j o = nm L R s j o' := by
  intro j
  induction j with
  | zero => intro o o' _; rfl
  | succ j ih =>
    intro o o' h
    have e := h j (Nat.lt_succ_self j)
    cases hb : o.testBit j
    · rw [nm_succ_neg L R hb, nm_succ_neg L R (e ▸ hb)]
      exact ih o o' (fun i hi => h i (Nat.lt_succ_of_lt hi))
    · rw [nm_succ_pos L R hb, nm_succ_pos L R (e ▸ hb)]
      rw [ih (o ||| cond (s j) (R j) (L j)) (o' ||| cond (s j) (R j) (L j))
        (fun i hi => by rw [Nat.testBit_or, Nat.testBit_or, h i (Nat.lt_succ_of_lt hi)])]

theorem testBit_fam (L R : ℕ → ℕ) : ∀ j o m,
    (fam L R j o).testBit m = true ↔ ∃ s, nm L R s j o = m := by
  intro j
  induction j with
  | zero =>
    intro o m
    show ((2:ℕ)^0).testBit m = true ↔ ∃ s : ℕ → Bool, 0 = m
    rw [Nat.testBit_two_pow]
    constructor
    · intro h; exact ⟨fun _ => false, of_decide_eq_true h⟩
    · rintro ⟨_, h⟩; exact decide_eq_true h
  | succ j ih =>
    intro o m
    cases hb : o.testBit j
    · rw [fam_succ_neg L R hb, ih]
      simp only [nm_succ_neg L R hb]
    · rw [fam_succ_pos L R hb, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft,
        Nat.testBit_shiftLeft]
      simp only [Bool.and_eq_true, decide_eq_true_eq, ih, nm_succ_pos L R hb]
      have key : ∀ (s : ℕ → Bool) (x : ℕ),
          2 ^ (2*j + (s j).toNat) ||| nm L R s j x = 2 ^ (2*j + (s j).toNat) + nm L R s j x := by
        intro s x
        have lt : nm L R s j x < 2 ^ (2*j + (s j).toNat) :=
          (nm_lt L R s j x).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
        have h1 := Nat.two_pow_add_eq_or_of_lt lt 1
        rw [Nat.mul_one] at h1
        exact h1.symm
      have upd : ∀ (s : ℕ → Bool) (b : Bool) (x : ℕ),
          nm L R (Function.update s j b) j x = nm L R s j x := by
        intro s b x
        apply nm_congr_s
        intro i hi
        exact Function.update_of_ne (Nat.ne_of_lt hi) _ _
      constructor
      · rintro (⟨hm, s, hs⟩ | ⟨hm, s, hs⟩)
        · refine ⟨Function.update s j false, ?_⟩
          rw [key, upd]
          simp only [Function.update_self, Bool.toNat_false, Bool.cond_false, Nat.add_zero]
          omega
        · refine ⟨Function.update s j true, ?_⟩
          rw [key, upd]
          simp only [Function.update_self, Bool.toNat_true, Bool.cond_true]
          omega
      · rintro ⟨s, hs⟩
        rw [key] at hs
        cases hsj : s j
        · rw [hsj] at hs
          simp only [Bool.toNat_false, Bool.cond_false, Nat.add_zero] at hs
          exact Or.inl ⟨by omega, s, by omega⟩
        · rw [hsj] at hs
          simp only [Bool.toNat_true, Bool.cond_true] at hs
          exact Or.inr ⟨by omega, s, by omega⟩

theorem fam_congr (L R L' R' : ℕ → ℕ) : ∀ j o o',
    (∀ i, i < j → o.testBit i = o'.testBit i) →
    (∀ i, i < j → ∀ v, v < i → (L i).testBit v = (L' i).testBit v) →
    (∀ i, i < j → ∀ v, v < i → (R i).testBit v = (R' i).testBit v) →
    fam L R j o = fam L' R' j o' := by
  intro j
  induction j with
  | zero => intro o o' _ _ _; rfl
  | succ j ih =>
    intro o o' ho hL hR
    have e := ho j (Nat.lt_succ_self j)
    have hL' : ∀ i, i < j → ∀ v, v < i → (L i).testBit v = (L' i).testBit v :=
      fun i hi => hL i (Nat.lt_succ_of_lt hi)
    have hR' : ∀ i, i < j → ∀ v, v < i → (R i).testBit v = (R' i).testBit v :=
      fun i hi => hR i (Nat.lt_succ_of_lt hi)
    cases hb : o.testBit j
    · rw [fam_succ_neg L R hb, fam_succ_neg L' R' (e ▸ hb)]
      exact ih o o' (fun i hi => ho i (Nat.lt_succ_of_lt hi)) hL' hR'
    · rw [fam_succ_pos L R hb, fam_succ_pos L' R' (e ▸ hb)]
      rw [ih (o ||| L j) (o' ||| L' j) (fun i hi => by
          rw [Nat.testBit_or, Nat.testBit_or, ho i (Nat.lt_succ_of_lt hi),
            hL j (Nat.lt_succ_self j) i hi]) hL' hR',
        ih (o ||| R j) (o' ||| R' j) (fun i hi => by
          rw [Nat.testBit_or, Nat.testBit_or, ho i (Nat.lt_succ_of_lt hi),
            hR j (Nat.lt_succ_self j) i hi]) hL' hR']

theorem fam_pad (L R : ℕ → ℕ) (j o : ℕ) (h : ∀ i, j ≤ i → o.testBit i = false) :
    ∀ d, fam L R (j + d) o = fam L R j o := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    show fam L R ((j + d) + 1) o = fam L R j o
    rw [fam_succ_neg L R (h (j + d) (Nat.le_add_right j d)), ih]

section Link

variable {k : ℕ} (rs : Fin k → Bool → Finset (Fin k))

def refCode (b : Bool) (j : ℕ) : ℕ :=
  if h : j < k then setCode ((rs ⟨j, h⟩ b).filter (· < ⟨j, h⟩)) else 0

def extend (s : Fin k → Bool) (j : ℕ) : Bool := if h : j < k then s ⟨j, h⟩ else false

theorem refCode_val (b : Bool) (J : Fin k) :
    refCode rs b J.val = setCode ((rs J b).filter (· < J)) := by
  simp [refCode]

theorem extend_val (s : Fin k → Bool) (J : Fin k) : extend s J.val = s J := by
  simp [extend]

theorem maskCode_step (s : Fin k → Bool) (J : Fin k) (N : Finset (Fin k))
    (hN : ∀ i ∈ N, i.val < J.val + 1)
    (ih : ∀ N' : Finset (Fin k), (∀ i ∈ N', i.val < J.val) →
      maskCode (mask rs N' s) =
        nm (refCode rs false) (refCode rs true) (extend s) J.val (setCode N')) :
    maskCode (mask rs N s) =
      nm (refCode rs false) (refCode rs true) (extend s) (J.val + 1) (setCode N) := by
  by_cases hJ : J ∈ N
  · have bit : (setCode N).testBit J.val = true := (testBit_setCode N _).mpr ⟨J, hJ, rfl⟩
    have small : ∀ i ∈ N.erase J ∪ (rs J (s J)).filter (· < J), i.val < J.val := by
      intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · have ne : i.val ≠ J.val := fun e => (Finset.mem_erase.mp h).1 (Fin.ext e)
        have := hN i (Finset.mem_of_mem_erase h)
        omega
      · exact (Finset.mem_filter.mp h).2
    have hc : cond (extend s J.val) (refCode rs true J.val) (refCode rs false J.val) =
        setCode ((rs J (s J)).filter (· < J)) := by
      rw [extend_val, refCode_val, refCode_val]
      cases s J <;> rfl
    rw [mask_step rs s N J hJ, nm_succ_pos _ _ bit, maskCode, bitsOf_insert, ← maskCode,
      ih _ small, hc, extend_val]
    congr 1
    apply nm_congr_o
    intro i hi
    rw [Bool.eq_iff_iff, Nat.testBit_or, Bool.or_eq_true, testBit_setCode, testBit_setCode,
      testBit_setCode]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases Finset.mem_union.mp ha with h | h
      · exact Or.inl ⟨a, Finset.mem_of_mem_erase h, rfl⟩
      · exact Or.inr ⟨a, h, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · have ne : a ≠ J := fun e => by rw [e] at hi; exact lt_irrefl _ hi
        exact ⟨a, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne, ha⟩), rfl⟩
      · exact ⟨a, Finset.mem_union_right _ ha, rfl⟩
  · have bit : (setCode N).testBit J.val = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨a, ha, e⟩ := (testBit_setCode N _).mp h
      exact hJ (Fin.ext e ▸ ha)
    rw [nm_succ_neg _ _ bit]
    apply ih
    intro i hi
    have ne : i.val ≠ J.val := fun e => hJ (Fin.ext e ▸ hi)
    have := hN i hi
    omega

theorem maskCode_mask_aux (s : Fin k → Bool) : ∀ j, j ≤ k → ∀ N : Finset (Fin k),
    (∀ i ∈ N, i.val < j) →
    maskCode (mask rs N s) =
      nm (refCode rs false) (refCode rs true) (extend s) j (setCode N) := by
  intro j
  induction j with
  | zero =>
    intro _ N hN
    have e : N = ∅ := Finset.eq_empty_of_forall_notMem
      (fun i hi => Nat.not_lt_zero _ (hN i hi))
    subst e
    show bitsOf idx (mask rs ∅ s) = 0
    rw [show mask rs ∅ s = ∅ from Finset.biUnion_empty, bitsOf_empty]
  | succ j ih =>
    intro hj N hN
    exact maskCode_step rs s ⟨j, hj⟩ N hN (ih (Nat.le_of_succ_le hj))

theorem maskCode_mask (outs : Finset (Fin k)) (s : Fin k → Bool) :
    maskCode (mask rs outs s) =
      nm (refCode rs false) (refCode rs true) (extend s) k (setCode outs) :=
  maskCode_mask_aux rs s k le_rfl outs (fun i _ => i.isLt)

theorem famCode_masks (outs : Finset (Fin k)) :
    famCode (masks rs outs) = fam (refCode rs false) (refCode rs true) k (setCode outs) := by
  apply Nat.eq_of_testBit_eq
  intro m
  rw [Bool.eq_iff_iff, testBit_famCode, testBit_fam]
  constructor
  · rintro ⟨M, hM, rfl⟩
    rw [masks, Finset.mem_image] at hM
    obtain ⟨s, -, rfl⟩ := hM
    exact ⟨extend s, (maskCode_mask rs outs s).symm⟩
  · rintro ⟨σ, rfl⟩
    refine ⟨mask rs outs (fun i => σ i.val), ?_, ?_⟩
    · rw [masks]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · rw [maskCode_mask]
      apply nm_congr_s
      intro i hi
      simp [extend, hi]

theorem setCode_high (outs : Finset (Fin k)) (i : ℕ) (hi : k ≤ i) :
    (setCode outs).testBit i = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨a, -, e⟩ := (testBit_setCode outs i).mp h
  have := a.isLt
  omega

end Link

def refFn (l1 l2 : ℕ) : ℕ → ℕ
  | 1 => l1
  | 2 => l2
  | _ => 0

def wOf (l1 r1 l2 r2 : ℕ) : ℕ := l1 ||| (r1 <<< 1) ||| (l2 <<< 2) ||| (r2 <<< 4)

theorem wOf_lt : ∀ (l1 r1 : Fin 2) (l2 r2 : Fin 4), wOf l1 r1 l2 r2 < 64 := by decide

set_option maxRecDepth 10000 in
theorem fam3_table : ∀ (l1 r1 : Fin 2) (l2 r2 : Fin 4) (o : Fin 8),
    fam (refFn l1 l2) (refFn r1 r2) 3 o = sh2 (wOf l1 r1 l2 r2) o := by decide +kernel

theorem testBit_mod_pow (x i v : ℕ) (h : v < i) : x.testBit v = (x % 2 ^ i).testBit v := by
  rw [Nat.testBit_mod_two_pow]
  simp [h]

theorem refFn_agree (L : ℕ → ℕ) : ∀ i, i < 3 → ∀ v, v < i →
    (L i).testBit v = (refFn (L 1 % 2) (L 2 % 4) i).testBit v := by
  intro i hi v hv
  interval_cases i
  · exact absurd hv (Nat.not_lt_zero _)
  · exact testBit_mod_pow (L 1) 1 v hv
  · exact testBit_mod_pow (L 2) 2 v hv

theorem fam3_eq (L R : ℕ → ℕ) : ∃ w, w < 64 ∧ ∀ o, fam L R 3 o = sh2 w (o % 8) := by
  have h2 : ∀ x : ℕ, x % 2 < 2 := fun x => Nat.mod_lt _ (by norm_num)
  have h4 : ∀ x : ℕ, x % 4 < 4 := fun x => Nat.mod_lt _ (by norm_num)
  have h8 : ∀ x : ℕ, x % 8 < 8 := fun x => Nat.mod_lt _ (by norm_num)
  refine ⟨wOf (L 1 % 2) (R 1 % 2) (L 2 % 4) (R 2 % 4),
    wOf_lt ⟨_, h2 _⟩ ⟨_, h2 _⟩ ⟨_, h4 _⟩ ⟨_, h4 _⟩, ?_⟩
  intro o
  rw [fam_congr L R (refFn (L 1 % 2) (L 2 % 4)) (refFn (R 1 % 2) (R 2 % 4)) 3 o (o % 8)
    (fun i hi => testBit_mod_pow o 3 i hi) (refFn_agree L) (refFn_agree R)]
  exact fam3_table ⟨_, h2 _⟩ ⟨_, h2 _⟩ ⟨_, h4 _⟩ ⟨_, h4 _⟩ ⟨_, h8 _⟩

theorem fam4_eq (L R : ℕ → ℕ) (o : ℕ) :
    ∃ w, w < 64 ∧ ((∃ a b, a < 8 ∧ b < 8 ∧ fam L R 4 o = top w a b) ∨
      (∃ a, a < 8 ∧ fam L R 4 o = sh2 w a)) := by
  obtain ⟨w, hw, h3⟩ := fam3_eq L R
  have h8 : ∀ x : ℕ, x % 8 < 8 := fun x => Nat.mod_lt _ (by norm_num)
  refine ⟨w, hw, ?_⟩
  cases hb : o.testBit 3
  · exact Or.inr ⟨o % 8, h8 _, by rw [fam_succ_neg L R hb, h3]⟩
  · refine Or.inl ⟨(o ||| L 3) % 8, (o ||| R 3) % 8, h8 _, h8 _, ?_⟩
    rw [fam_succ_pos L R hb, h3, h3]
    rfl

theorem masks_numeric {k : ℕ} (hk : k ≤ 4) (rs : Fin k → Bool → Finset (Fin k))
    (outs : Finset (Fin k)) :
    ∃ w, w < 64 ∧ ((∃ a b, a < 8 ∧ b < 8 ∧ famCode (masks rs outs) = top w a b) ∨
      (∃ a, a < 8 ∧ famCode (masks rs outs) = sh2 w a)) := by
  have pad := fam_pad (refCode rs false) (refCode rs true) k (setCode outs)
    (setCode_high outs) (4 - k)
  rw [show k + (4 - k) = 4 by omega] at pad
  rw [famCode_masks, ← pad]
  exact fam4_eq _ _ _

end MoonPrize.Bridge

namespace MoonPrize.Wiring

def witnessBlocks : List (List (List ℕ ⊕ (ℕ × ℕ))) := [witness0,witness1,witness2,witness3,witness4,witness5,witness6,witness7,witness8,witness9,witness10,witness11,witness12,witness13,witness14,witness15,witness16,witness17,witness18,witness19,witness20,witness21,witness22,witness23,witness24,witness25,witness26,witness27,witness28,witness29,witness30,witness31,witness32,witness33,witness34,witness35]

def Good (ws : List ℕ) (wt : List (List ℕ ⊕ (ℕ × ℕ))) : Prop :=
  ws.length = wt.length ∧ (ws.zip wt).all (fun t => checkWitness t.1 t.2) = true

end MoonPrize.Wiring

namespace MoonPrize.Bridge

open MoonPrize.Shape MoonPrize.Wiring

def PermCode (p : ℕ) : Prop :=
  ((List.range 8).map (fun i => (p >>> (3*i)) &&& 7)).eraseDups.length = 8

def witnessAt (i : ℕ) : List ℕ ⊕ (ℕ × ℕ) :=
  ((witnessBlocks[i/16]?.getD [])[i % 16]?).getD (Sum.inl [])

theorem good_get (ws : List ℕ) (wt : List (List ℕ ⊕ (ℕ × ℕ))) (h : Good ws wt) (r : ℕ) :
    checkWitness (ws[r]?.getD 0) (wt[r]?.getD (Sum.inl [])) = true := by
  induction ws generalizing wt r with
  | nil =>
    cases wt with
    | nil =>
      simp only [List.getElem?_nil, Option.getD_none]
      decide
    | cons b wt => exact absurd h.1 (by simp)
  | cons a ws ih =>
    cases wt with
    | nil => exact absurd h.1 (by simp)
    | cons b wt =>
      obtain ⟨hl, ha⟩ := h
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, List.length_cons,
        Nat.add_right_cancel_iff] at hl ha
      cases r with
      | zero => simpa using ha.1
      | succ r => simpa using ih wt ⟨hl, ha.2⟩ r

theorem forall2_get (wbs : List (List ℕ)) (wtbs : List (List (List ℕ ⊕ (ℕ × ℕ))))
    (h : List.Forall₂ Good wbs wtbs) (q : ℕ) :
    Good (wbs[q]?.getD []) (wtbs[q]?.getD []) := by
  induction h generalizing q with
  | nil =>
    simp only [List.getElem?_nil, Option.getD_none]
    exact ⟨rfl, rfl⟩
  | cons hab _ ih =>
    cases q with
    | zero => simpa using hab
    | succ q => simpa using ih q

theorem witness_prop (f : ℕ) (t : List ℕ ⊕ (ℕ × ℕ)) (h : checkWitness f t = true) :
    (∃ xs : List ℕ, xs.length < 10 ∧ f = encode xs) ∨
    (∃ c ∈ classes, ∃ p, PermCode p ∧ f = encode (c.map (applyBits p))) := by
  rcases t with xs | ⟨j, p⟩
  · simp only [checkWitness, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact Or.inl ⟨xs, h.1, h.2.symm⟩
  · simp only [checkWitness, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hj, hp⟩, hf⟩ := h
    refine Or.inr ⟨classes[j], List.getElem_mem hj, p, hp, ?_⟩
    rw [← hf, List.getElem?_eq_getElem hj, Option.getD_some]

theorem image_maskCode_eq {k : ℕ} (F : Finset (Finset (Fin k × Bool))) (xs : List ℕ)
    (e : famCode F = encode xs) : F.image maskCode = xs.toFinset := by
  ext m
  rw [Finset.mem_image, List.mem_toFinset, ← encode_spec, ← e, testBit_famCode]

theorem foldr_bits (c : ℕ → Bool) (g : ℕ → ℕ) (l : List ℕ) (v : ℕ) :
    (l.foldr (fun i acc => if c i = true then (1 <<< g i) ||| acc else acc) 0).testBit v = true ↔
      ∃ i, i ∈ l ∧ c i = true ∧ g i = v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hc : c a = true
    · rw [ite_eq_left hc, Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), hc, of_decide_eq_true h⟩
        · exact ⟨i, List.mem_cons_of_mem _ hi, h⟩
      · rintro ⟨i, hi, hci, h⟩
        rcases List.mem_cons.mp hi with e | hi
        · exact Or.inl (decide_eq_true (e ▸ h))
        · exact Or.inr ⟨i, hi, hci, h⟩
    · rw [ite_eq_right hc, ih]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i, List.mem_cons_of_mem _ hi, h⟩
      · rintro ⟨i, hi, hci, h⟩
        rcases List.mem_cons.mp hi with e | hi
        · exact absurd (e ▸ hci) hc
        · exact ⟨i, hi, hci, h⟩

theorem testBit_applyBits (p x v : ℕ) :
    (applyBits p x).testBit v = true ↔
      ∃ i, i < 8 ∧ x.testBit i = true ∧ (p >>> (3*i)) &&& 7 = v := by
  have h := foldr_bits (fun i => x.testBit i) (fun i => (p >>> (3*i)) &&& 7) (List.range 8) v
  simp only [List.mem_range] at h
  exact h

def unapply (p y : ℕ) : ℕ :=
  (List.range 8).foldr (fun i acc =>
    if y.testBit ((p >>> (3*i)) &&& 7) then (1 <<< i) ||| acc else acc) 0

theorem testBit_unapply (p y v : ℕ) :
    (unapply p y).testBit v = true ↔
      ∃ i, i < 8 ∧ y.testBit ((p >>> (3*i)) &&& 7) = true ∧ i = v := by
  have h := foldr_bits (fun i => y.testBit ((p >>> (3*i)) &&& 7)) (fun i => i) (List.range 8) v
  simp only [List.mem_range] at h
  exact h

theorem unapply_lt (p y : ℕ) : unapply p y < 256 := by
  show unapply p y < 2 ^ 8
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨i', h8, -, e⟩ := (testBit_unapply p y i).mp h
  omega

theorem applyBits_land (p x y : ℕ) : applyBits p x &&& y = 0 ↔ x &&& unapply p y = 0 := by
  rw [land_eq_zero_iff, land_eq_zero_iff]
  constructor
  · intro h i hx
    apply Bool.eq_false_iff.mpr
    intro hu
    obtain ⟨i', h8, hy, e⟩ := (testBit_unapply p y i).mp hu
    subst e
    have c := h _ ((testBit_applyBits p x _).mpr ⟨i', h8, hx, rfl⟩)
    rw [hy] at c
    exact Bool.noConfusion c
  · intro h v hv
    obtain ⟨i, h8, hx, e⟩ := (testBit_applyBits p x v).mp hv
    subst e
    apply Bool.eq_false_iff.mpr
    intro hy
    have c := h i hx
    rw [(testBit_unapply p y i).mpr ⟨i, h8, hy, rfl⟩] at c
    exact Bool.noConfusion c

theorem classified_of_word {k : ℕ} (hk : k ≤ 4) (F : Finset (Finset (Fin k × Bool)))
    (h : (∃ xs : List ℕ, xs.length < 10 ∧ famCode F = encode xs) ∨
      (∃ c ∈ classes, ∃ p, PermCode p ∧ famCode F = encode (c.map (applyBits p)))) :
    ∃ c : List ℕ, (c.length < 10 ∨ c ∈ classes) ∧
      ∃ col : Finset (Fin k × Bool) → ℕ, (∀ Y, col Y < 256) ∧
        ∀ M ∈ F, ∃ x ∈ c, ∀ Y, Disjoint M Y ↔ x &&& col Y = 0 := by
  rcases h with ⟨xs, hx, e⟩ | ⟨c, hc, p, -, e⟩
  · refine ⟨xs, Or.inl hx, maskCode, maskCode_lt hk, ?_⟩
    intro M hM
    have hb : (encode xs).testBit (maskCode M) = true := by
      rw [← e]
      exact (testBit_famCode _ _).mpr ⟨M, hM, rfl⟩
    exact ⟨maskCode M, (encode_spec xs _).mp hb, fun Y => disjoint_iff_land M Y⟩
  · refine ⟨c, Or.inr hc, fun Y => unapply p (maskCode Y), fun Y => unapply_lt _ _, ?_⟩
    intro M hM
    have hb : (encode (c.map (applyBits p))).testBit (maskCode M) = true := by
      rw [← e]
      exact (testBit_famCode _ _).mpr ⟨M, hM, rfl⟩
    obtain ⟨x, hx, hxM⟩ := List.mem_map.mp ((encode_spec _ _).mp hb)
    refine ⟨x, hx, fun Y => ?_⟩
    rw [disjoint_iff_land, ← hxM]
    exact applyBits_land p x _

def NumericObstruction : Prop :=
  ∀ (m : Fin 11) (H : SimpleGraph (Fin m.val)), MoonPrize.Finite.NoSquare H →
    MoonPrize.Core.Hard H Finset.univ →
    (∀ v : Fin m.val, ∃ A : Finset (Fin m.val), MoonPrize.Core.Independent H A ∧ v ∉ A ∧
      A.card + 5 = m.val) →
    ∀ c : List ℕ, (c.length < 10 ∨ c ∈ classes) →
    ∀ col : Fin m.val → ℕ, (∀ u, col u < 256) →
      ¬ (∀ J : Finset (Fin m.val), MoonPrize.Core.Independent H J →
        (∀ u, u ∉ J → ∃ v ∈ J, H.Adj u v) →
        ∃ x ∈ c, ∀ u, u ∈ J ↔ x &&& col u = 0)

end MoonPrize.Bridge

namespace MoonPrize.Wiring

theorem blocksGood : List.Forall₂ Good wordBlocks witnessBlocks :=
  .cons class0 (.cons class1 (.cons class2 (.cons class3 (.cons class4 (.cons class5 (.cons class6 (.cons class7 (.cons class8 (.cons class9 (.cons class10 (.cons class11 (.cons class12 (.cons class13 (.cons class14 (.cons class15 (.cons class16 (.cons class17 (.cons class18 (.cons class19 (.cons class20 (.cons class21 (.cons class22 (.cons class23 (.cons class24 (.cons class25 (.cons class26 (.cons class27 (.cons class28 (.cons class29 (.cons class30 (.cons class31 (.cons class32 (.cons class33 (.cons class34 (.cons class35 (.nil))))))))))))))))))))))))))))))))))))

theorem listed (w : ℕ) (hw : w < 64) :
    (∀ a b : Fin 8, ∃ i, top w a b = wordAt i) ∧ (∀ a : Fin 8, ∃ i, sh2 w a = wordAt i) := by
  interval_cases w
  · exact ⟨fun a b => ⟨_, labels0.1 a b⟩, fun a => ⟨_, labels0.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels1.1 a b⟩, fun a => ⟨_, labels1.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels2.1 a b⟩, fun a => ⟨_, labels2.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels3.1 a b⟩, fun a => ⟨_, labels3.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels4.1 a b⟩, fun a => ⟨_, labels4.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels5.1 a b⟩, fun a => ⟨_, labels5.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels6.1 a b⟩, fun a => ⟨_, labels6.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels7.1 a b⟩, fun a => ⟨_, labels7.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels8.1 a b⟩, fun a => ⟨_, labels8.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels9.1 a b⟩, fun a => ⟨_, labels9.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels10.1 a b⟩, fun a => ⟨_, labels10.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels11.1 a b⟩, fun a => ⟨_, labels11.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels12.1 a b⟩, fun a => ⟨_, labels12.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels13.1 a b⟩, fun a => ⟨_, labels13.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels14.1 a b⟩, fun a => ⟨_, labels14.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels15.1 a b⟩, fun a => ⟨_, labels15.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels16.1 a b⟩, fun a => ⟨_, labels16.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels17.1 a b⟩, fun a => ⟨_, labels17.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels18.1 a b⟩, fun a => ⟨_, labels18.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels19.1 a b⟩, fun a => ⟨_, labels19.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels20.1 a b⟩, fun a => ⟨_, labels20.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels21.1 a b⟩, fun a => ⟨_, labels21.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels22.1 a b⟩, fun a => ⟨_, labels22.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels23.1 a b⟩, fun a => ⟨_, labels23.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels24.1 a b⟩, fun a => ⟨_, labels24.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels25.1 a b⟩, fun a => ⟨_, labels25.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels26.1 a b⟩, fun a => ⟨_, labels26.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels27.1 a b⟩, fun a => ⟨_, labels27.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels28.1 a b⟩, fun a => ⟨_, labels28.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels29.1 a b⟩, fun a => ⟨_, labels29.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels30.1 a b⟩, fun a => ⟨_, labels30.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels31.1 a b⟩, fun a => ⟨_, labels31.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels32.1 a b⟩, fun a => ⟨_, labels32.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels33.1 a b⟩, fun a => ⟨_, labels33.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels34.1 a b⟩, fun a => ⟨_, labels34.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels35.1 a b⟩, fun a => ⟨_, labels35.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels36.1 a b⟩, fun a => ⟨_, labels36.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels37.1 a b⟩, fun a => ⟨_, labels37.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels38.1 a b⟩, fun a => ⟨_, labels38.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels39.1 a b⟩, fun a => ⟨_, labels39.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels40.1 a b⟩, fun a => ⟨_, labels40.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels41.1 a b⟩, fun a => ⟨_, labels41.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels42.1 a b⟩, fun a => ⟨_, labels42.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels43.1 a b⟩, fun a => ⟨_, labels43.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels44.1 a b⟩, fun a => ⟨_, labels44.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels45.1 a b⟩, fun a => ⟨_, labels45.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels46.1 a b⟩, fun a => ⟨_, labels46.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels47.1 a b⟩, fun a => ⟨_, labels47.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels48.1 a b⟩, fun a => ⟨_, labels48.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels49.1 a b⟩, fun a => ⟨_, labels49.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels50.1 a b⟩, fun a => ⟨_, labels50.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels51.1 a b⟩, fun a => ⟨_, labels51.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels52.1 a b⟩, fun a => ⟨_, labels52.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels53.1 a b⟩, fun a => ⟨_, labels53.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels54.1 a b⟩, fun a => ⟨_, labels54.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels55.1 a b⟩, fun a => ⟨_, labels55.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels56.1 a b⟩, fun a => ⟨_, labels56.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels57.1 a b⟩, fun a => ⟨_, labels57.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels58.1 a b⟩, fun a => ⟨_, labels58.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels59.1 a b⟩, fun a => ⟨_, labels59.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels60.1 a b⟩, fun a => ⟨_, labels60.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels61.1 a b⟩, fun a => ⟨_, labels61.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels62.1 a b⟩, fun a => ⟨_, labels62.2 a⟩⟩
  · exact ⟨fun a b => ⟨_, labels63.1 a b⟩, fun a => ⟨_, labels63.2 a⟩⟩

end MoonPrize.Wiring

namespace MoonPrize.Bridge

open MoonPrize.Shape MoonPrize.Wiring

theorem word_good (i : ℕ) : checkWitness (wordAt i) (witnessAt i) = true :=
  good_get _ _ (forall2_get _ _ blocksGood (i/16)) (i % 16)

theorem shape_classified {k : ℕ} (hk : k ≤ 4) (rs : Fin k → Bool → Finset (Fin k))
    (outs : Finset (Fin k)) :
    (∃ xs : List ℕ, xs.length < 10 ∧ famCode (masks rs outs) = encode xs) ∨
    (∃ c ∈ classes, ∃ p, PermCode p ∧
      famCode (masks rs outs) = encode (c.map (applyBits p))) := by
  obtain ⟨w, hw, h⟩ := masks_numeric hk rs outs
  obtain ⟨ht, hs⟩ := listed w hw
  rcases h with ⟨a, b, ha, hb, e⟩ | ⟨a, ha, e⟩
  · obtain ⟨i, hi⟩ := ht ⟨a, ha⟩ ⟨b, hb⟩
    have hi' : top w a b = wordAt i := hi
    rw [e, hi']
    exact witness_prop _ _ (word_good i)
  · obtain ⟨i, hi⟩ := hs ⟨a, ha⟩
    have hi' : sh2 w a = wordAt i := hi
    rw [e, hi']
    exact witness_prop _ _ (word_good i)

theorem masks_card_lt_or_class {k : ℕ} (hk : k ≤ 4) (rs : Fin k → Bool → Finset (Fin k))
    (outs : Finset (Fin k)) :
    (masks rs outs).card < 10 ∨
    (∃ c ∈ classes, ∃ p, PermCode p ∧
      (masks rs outs).image maskCode = (c.map (applyBits p)).toFinset) := by
  rcases shape_classified hk rs outs with ⟨xs, hx, e⟩ | ⟨c, hc, p, hp, e⟩
  · left
    calc (masks rs outs).card = ((masks rs outs).image maskCode).card :=
          (Finset.card_image_of_injective _ maskCode_injective).symm
      _ = xs.toFinset.card := by rw [image_maskCode_eq _ _ e]
      _ ≤ xs.length := List.toFinset_card_le xs
      _ < 10 := hx
  · exact Or.inr ⟨c, hc, p, hp, image_maskCode_eq _ _ e⟩

theorem classified {k : ℕ} (hk : k ≤ 4) (rs : Fin k → Bool → Finset (Fin k))
    (outs : Finset (Fin k)) :
    ∃ c : List ℕ, (c.length < 10 ∨ c ∈ classes) ∧
      ∃ col : Finset (Fin k × Bool) → ℕ, (∀ Y, col Y < 256) ∧
        ∀ M ∈ masks rs outs, ∃ x ∈ c, ∀ Y, Disjoint M Y ↔ x &&& col Y = 0 :=
  classified_of_word hk _ (shape_classified hk rs outs)

theorem obstruction_of_numeric (h : NumericObstruction) : MoonPrize.Finite.Obstruction := by
  intro m k H sq hard ex rs outs column hyp
  obtain ⟨c, hc, col, hcol, hM⟩ := classified (Nat.lt_succ_iff.mp k.isLt) rs outs
  apply h m H sq hard ex c hc (fun u => col (column u)) (fun u => hcol _)
  intro J hi hd
  obtain ⟨s, hs, hJ⟩ := hyp J hi hd
  obtain ⟨x, hx, hxY⟩ := hM s hs
  exact ⟨x, hx, fun u => (hJ u).trans (hxY _)⟩

theorem target_of_numeric (h : NumericObstruction) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 5 ≤ T.card) → ∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed → (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → 5 ≤ C.size :=
  MoonPrize.Finite.from_finite (obstruction_of_numeric h)

end MoonPrize.Bridge

namespace MoonPrize.Core

section
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {W : Finset V}

theorem independent_insert {S : Finset V} {x : V} (hS : Independent G S)
    (hx : ∀ w ∈ S, ¬G.Adj x w) : Independent G (insert x S) := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with h | h
  · rcases Finset.mem_insert.mp hb with h' | h'
    · rw [h, h'] at hab
      exact G.ne_of_adj hab rfl
    · rw [h] at hab
      exact hx b h' hab
  · rcases Finset.mem_insert.mp hb with h' | h'
    · rw [h'] at hab
      exact hx a h hab.symm
    · exact hS a h b h' hab

theorem exists_neighbor_sdiff (hard : Hard G W)
    (ex : ∀ v ∈ W, ∃ A ⊆ W, Independent G A ∧ v ∉ A ∧ A.card + 5 = W.card)
    {R : Finset V} (hR : Independent G R) {v : V} (hvW : v ∈ W) (hvR : v ∈ R) :
    ∃ t ∈ W \ R, G.Adj v t := by
  obtain ⟨A, hAW, hAi, hvA, hcard⟩ := ex v hvW
  by_contra hno
  have hnoW : ∀ w ∈ A, ¬G.Adj v w := by
    intro w hw hadj
    by_cases hwR : w ∈ R
    · exact hR v hvR w hwR hadj
    · exact hno ⟨w, Finset.mem_sdiff.mpr ⟨hAW hw, hwR⟩, hadj⟩
  have hins : Independent G (insert v A) := independent_insert hAi hnoW
  have hsub : insert v A ⊆ W := Finset.insert_subset hvW hAW
  have hc := hard _ hsub hins
  rw [Finset.card_insert_eq_ite, ite_eq_right hvA] at hc
  omega

theorem twins_two_common_neighbors (hard : Hard G W)
    (ex : ∀ v ∈ W, ∃ A ⊆ W, Independent G A ∧ v ∉ A ∧ A.card + 5 = W.card)
    {u v : V} (huW : u ∈ W) (hvW : v ∈ W) (huv : u ≠ v) (hnadj : ¬G.Adj u v)
    (htw : ∀ w ∈ W, (G.Adj u w ↔ G.Adj v w)) :
    ∃ a ∈ W, ∃ b ∈ W, a ≠ b ∧ G.Adj u a ∧ G.Adj v a ∧ G.Adj u b ∧ G.Adj v b := by
  obtain ⟨A, hAW, hAi, huA, hcard⟩ := ex u huW
  by_cases hN : ∃ a ∈ A, G.Adj u a
  · obtain ⟨a, haA, hua⟩ := hN
    have hva : G.Adj v a := (htw a (hAW haA)).mp hua
    have hvA : v ∉ A := fun h => hAi v h a haA hva
    by_contra hcon
    have hx : ∀ x ∈ A.erase a, ¬G.Adj u x := by
      intro x hx hux
      have hxA : x ∈ A := Finset.mem_of_mem_erase hx
      exact hcon ⟨a, hAW haA, x, hAW hxA, (Finset.ne_of_mem_erase hx).symm,
        hua, hva, hux, (htw x (hAW hxA)).mp hux⟩
    have hE : Independent G (A.erase a) := fun p hp q hq =>
      hAi p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq)
    have h1 : Independent G (insert v (A.erase a)) :=
      independent_insert hE (fun x hx' hvx =>
        hx x hx' ((htw x (hAW (Finset.mem_of_mem_erase hx'))).mpr hvx))
    have h2 : Independent G (insert u (insert v (A.erase a))) :=
      independent_insert h1 (by
        intro x hx' hux
        rcases Finset.mem_insert.mp hx' with h | h
        · rw [h] at hux
          exact hnadj hux
        · exact hx x h hux)
    have hv' : v ∉ A.erase a := fun h => hvA (Finset.mem_of_mem_erase h)
    have hu' : u ∉ insert v (A.erase a) := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact huv h
      · exact huA (Finset.mem_of_mem_erase h)
    have hsub : insert u (insert v (A.erase a)) ⊆ W :=
      Finset.insert_subset huW
        (Finset.insert_subset hvW (fun p hp => hAW (Finset.mem_of_mem_erase hp)))
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨a, haA⟩
    have hc := hard _ hsub h2
    rw [Finset.card_insert_eq_ite, ite_eq_right hu', Finset.card_insert_eq_ite, ite_eq_right hv',
      Finset.card_erase_of_mem haA] at hc
    omega
  · exfalso
    have hins : Independent G (insert u A) :=
      independent_insert hAi (fun w hw h => hN ⟨w, hw, h⟩)
    have hsub : insert u A ⊆ W := Finset.insert_subset huW hAW
    have hc := hard _ hsub hins
    rw [Finset.card_insert_eq_ite, ite_eq_right huA] at hc
    omega

theorem neighbors_sdiff_distinct (hard : Hard G W)
    (ex : ∀ v ∈ W, ∃ A ⊆ W, Independent G A ∧ v ∉ A ∧ A.card + 5 = W.card)
    (sqf : ∀ u v a b : V, u ≠ v → a ≠ b →
      G.Adj u a → G.Adj v a → G.Adj u b → G.Adj v b → False)
    {R : Finset V} (hRW : R ⊆ W) (hR : Independent G R)
    {u v : V} (huR : u ∈ R) (hvR : v ∈ R) (huv : u ≠ v) :
    ∃ t ∈ W \ R, ¬(G.Adj u t ↔ G.Adj v t) := by
  by_contra hno
  have htw : ∀ w ∈ W, (G.Adj u w ↔ G.Adj v w) := by
    intro w hw
    by_cases hwR : w ∈ R
    · exact ⟨fun h => absurd h (hR u huR w hwR), fun h => absurd h (hR v hvR w hwR)⟩
    · by_contra hne
      exact hno ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwR⟩, hne⟩
  obtain ⟨a, _, b, _, hab, hua, hva, hub, hvb⟩ :=
    twins_two_common_neighbors hard ex (hRW huR) (hRW hvR) huv (hR u huR v hvR) htw
  exact sqf u v a b huv hab hua hva hub hvb

end

end MoonPrize.Core

namespace MoonPrize.Label

open MoonPrize.Core MoonPrize.Finite

def pairIndex : ℕ → ℕ → ℕ
  | 0, 1 => 0 | 0, 2 => 1 | 0, 3 => 2 | 0, 4 => 3
  | 1, 2 => 4 | 1, 3 => 5 | 1, 4 => 6
  | 2, 3 => 7 | 2, 4 => 8
  | 3, 4 => 9
  | _, _ => 0

def codeAdj (f : ℕ) (qs : List ℕ) (a b : ℕ) : Bool :=
  if a < 5 then
    if b < 5 then
      (decide (a < b) && f.testBit (pairIndex a b)) || (decide (b < a) && f.testBit (pairIndex b a))
    else (qs.getD (b - 5) 0).testBit a
  else
    if b < 5 then (qs.getD (a - 5) 0).testBit b else false

lemma codeAdj_comm (f : ℕ) (qs : List ℕ) (a b : ℕ) : codeAdj f qs a b = codeAdj f qs b a := by
  unfold codeAdj
  split_ifs <;> simp [Bool.or_comm]

lemma codeAdj_self (f : ℕ) (qs : List ℕ) (a : ℕ) : codeAdj f qs a a = false := by
  unfold codeAdj
  split_ifs <;> simp

lemma codeAdj_cover_lt (f : ℕ) (qs : List ℕ) {a b : ℕ} (ab : a < b) (hb : b < 5) :
    codeAdj f qs a b = f.testBit (pairIndex a b) := by
  have ha : a < 5 := by omega
  have nba : ¬ b < a := by omega
  simp [codeAdj, ha, hb, ab, nba]

lemma codeAdj_cover_row (f : ℕ) (qs : List ℕ) {a : ℕ} (ha : a < 5) (i : ℕ) :
    codeAdj f qs a (5 + i) = (qs.getD i 0).testBit a := by
  simp [codeAdj, ha]

lemma codeAdj_row_row (f : ℕ) (qs : List ℕ) (i j : ℕ) :
    codeAdj f qs (5 + i) (5 + j) = false := by
  simp [codeAdj]

lemma codeAdj_lt (f : ℕ) (qs : List ℕ) {a b : ℕ} (h : codeAdj f qs a b = true) :
    a < 5 + qs.length := by
  by_contra hn
  have ha : ¬ a < 5 := by omega
  have hd : qs.getD (a - 5) 0 = 0 := by
    rw [List.getD_eq_default]
    omega
  unfold codeAdj at h
  rw [ite_eq_right ha, hd] at h
  simp at h

def codeGraph (f : ℕ) (qs : List ℕ) : SimpleGraph (Fin (5 + qs.length)) where
  Adj a b := codeAdj f qs a.val b.val = true
  symm := ⟨fun a b h => by rw [codeAdj_comm]; exact h⟩
  loopless := ⟨fun a h => by simp [codeAdj_self] at h⟩


lemma codeGraph_adj (f : ℕ) (qs : List ℕ) (a b : Fin (5 + qs.length)) :
    (codeGraph f qs).Adj a b ↔ codeAdj f qs a.val b.val = true := Iff.rfl

def mask (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => mask p k ||| (if p k then 2 ^ k else 0)

lemma mask_lt (p : ℕ → Bool) : ∀ k, mask p k < 2 ^ k
  | 0 => by simp [mask]
  | k + 1 => by
    have h := mask_lt p k
    have pos : 0 < 2 ^ k := Nat.two_pow_pos k
    have h1 : mask p k < 2 ^ (k + 1) := by rw [pow_succ]; omega
    have h2 : (if p k then 2 ^ k else 0) < 2 ^ (k + 1) := by
      rw [pow_succ]; split <;> omega
    exact Nat.or_lt_two_pow h1 h2

lemma testBit_mask (p : ℕ → Bool) (i : ℕ) :
    ∀ k, (mask p k).testBit i = (decide (i < k) && p i)
  | 0 => by simp [mask]
  | k + 1 => by
    rw [mask, Nat.testBit_or, testBit_mask p i k]
    rcases Nat.lt_trichotomy i k with h | h | h
    · have h1 : i < k + 1 := by omega
      have h2 : k ≠ i := by omega
      cases hp : p k <;> simp [h, h1, h2]
    · subst h
      cases hp : p i <;> simp
    · have h0 : ¬ i < k := by omega
      have h1 : ¬ i < k + 1 := by omega
      have h2 : k ≠ i := by omega
      cases hp : p k <;> simp [h0, h1, h2]

lemma pairIndex_lt : ∀ i j : Fin 5, i.val < j.val → pairIndex i.val j.val < 10 := by decide

lemma pairIndex_inj : ∀ i j i' j' : Fin 5, i.val < j.val → i'.val < j'.val →
    pairIndex i.val j.val = pairIndex i'.val j'.val → i = i' ∧ j = j' := by decide

lemma exists_equiv_of_label {V : Type*} [Fintype V] {N : ℕ} (lab : V → ℕ)
    (lt : ∀ v, lab v < N) (inj : Function.Injective lab) (card : Fintype.card V = N) :
    ∃ e : V ≃ Fin N, ∀ v, (e v).val = lab v := by
  let g : V → Fin N := fun v => ⟨lab v, lt v⟩
  have gi : Function.Injective g := fun a b h => inj (congrArg Fin.val h)
  have gb : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨gi, by simp [card]⟩
  exact ⟨Equiv.ofBijective g gb, fun v => rfl⟩

theorem encode_of_cover {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (R T : Finset V) (hT : ∀ v, v ∈ T ↔ v ∉ R) (ind : Independent H R)
    (τ : {x // x ∈ T} ≃ Fin 5)
    (nz : ∀ u ∈ R, ∃ t ∈ T, H.Adj u t)
    (dist : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∃ t ∈ T, ¬(H.Adj u t ↔ H.Adj v t)) :
    ∃ (f : ℕ) (qs : List ℕ) (e : V ≃ Fin (5 + qs.length)),
      f < 1024 ∧ qs.length = R.card ∧ qs.Pairwise (· < ·) ∧ (∀ q ∈ qs, 0 < q ∧ q < 32) ∧
      (∀ t : {x // x ∈ T}, (e t.1).val = (τ t).val) ∧
      (∀ v, v ∈ R ↔ 5 ≤ (e v).val) ∧
      ∀ a b, H.Adj a b ↔ codeAdj f qs (e a).val (e b).val = true := by
  classical
  
  let qOf : V → ℕ := fun r =>
    mask (fun i => decide (∃ t : {x // x ∈ T}, (τ t).val = i ∧ H.Adj r t.1)) 5
  have hq (r : V) (t : {x // x ∈ T}) : (qOf r).testBit (τ t).val = true ↔ H.Adj r t.1 := by
    simp only [qOf, testBit_mask, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, s, hs, adj⟩
      have st : s = t := τ.injective (Fin.ext hs)
      exact st ▸ adj
    · exact fun adj => ⟨(τ t).isLt, t, rfl, adj⟩
  
  let f : ℕ := mask (fun k => decide (∃ s t : {x // x ∈ T}, (τ s).val < (τ t).val ∧
    pairIndex (τ s).val (τ t).val = k ∧ H.Adj s.1 t.1)) 10
  have hf (s t : {x // x ∈ T}) (lt : (τ s).val < (τ t).val) :
      f.testBit (pairIndex (τ s).val (τ t).val) = true ↔ H.Adj s.1 t.1 := by
    simp only [f, testBit_mask, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, s', t', lt', eq, adj⟩
      obtain ⟨h1, h2⟩ := pairIndex_inj (τ s') (τ t') (τ s) (τ t) lt' lt eq
      rw [← τ.injective h1, ← τ.injective h2]
      exact adj
    · exact fun adj => ⟨pairIndex_lt _ _ lt, s, t, lt, rfl, adj⟩
  
  have qinj : Set.InjOn qOf (R : Set V) := by
    intro u hu v hv eq
    by_contra ne
    obtain ⟨t, ht, dis⟩ := dist u hu v hv ne
    apply dis
    rw [← hq u ⟨t, ht⟩, ← hq v ⟨t, ht⟩, eq]
  let Q := R.image qOf
  have hQ : Q.card = R.card := Finset.card_image_of_injOn qinj
  let o := Q.orderIsoOfFin hQ
  let qs : List ℕ := List.ofFn (fun i : Fin R.card => (o i : ℕ))
  have len : qs.length = R.card := List.length_ofFn
  have memQ (v : V) (hv : v ∈ R) : qOf v ∈ Q := Finset.mem_image_of_mem _ hv
  let idx : V → ℕ := fun v => if h : qOf v ∈ Q then (o.symm ⟨qOf v, h⟩).val else 0
  have idx_lt (v : V) (hv : v ∈ R) : idx v < R.card := by
    simp only [idx, dite_eq_left (memQ v hv)]
    exact (o.symm _).isLt
  have idx_get (v : V) (hv : v ∈ R) : qs.getD (idx v) 0 = qOf v := by
    have h := idx_lt v hv
    rw [List.getD_eq_getElem _ _ (by rw [len]; exact h)]
    simp [qs, idx, dite_eq_left (memQ v hv)]
  have idx_inj (u : V) (hu : u ∈ R) (v : V) (hv : v ∈ R) (eq : idx u = idx v) : u = v := by
    simp only [idx, dite_eq_left (memQ u hu), dite_eq_left (memQ v hv)] at eq
    have h := o.symm.injective (Fin.ext eq)
    exact qinj hu hv (congrArg Subtype.val h)
  
  let lab : V → ℕ := fun v => if h : v ∈ T then (τ ⟨v, h⟩).val else 5 + idx v
  have labT (v : V) (h : v ∈ T) : lab v = (τ ⟨v, h⟩).val := dite_eq_left h
  have labR (v : V) (h : v ∈ R) : lab v = 5 + idx v := dite_eq_right (fun hT' => (hT v).mp hT' h)
  have inR (v : V) (h : v ∉ T) : v ∈ R := by
    by_contra h'
    exact h ((hT v).mpr h')
  have adj (a b : V) : H.Adj a b ↔ codeAdj f qs (lab a) (lab b) = true := by
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · rw [labT a ha, labT b hb]
      rcases Nat.lt_trichotomy (τ ⟨a, ha⟩).val (τ ⟨b, hb⟩).val with lt | eq | gt
      · rw [codeAdj_cover_lt _ _ lt (τ _).isLt]
        exact (hf ⟨a, ha⟩ ⟨b, hb⟩ lt).symm
      · have ab : a = b := congrArg Subtype.val (τ.injective (Fin.ext eq))
        subst ab
        simp [codeAdj_self]
      · rw [codeAdj_comm, codeAdj_cover_lt _ _ gt (τ _).isLt]
        exact ⟨fun h => (hf ⟨b, hb⟩ ⟨a, ha⟩ gt).mpr h.symm,
          fun h => ((hf ⟨b, hb⟩ ⟨a, ha⟩ gt).mp h).symm⟩
    · have rb := inR b hb
      rw [labT a ha, labR b rb, codeAdj_cover_row _ _ (τ _).isLt, idx_get b rb, hq b ⟨a, ha⟩]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    · have ra := inR a ha
      rw [labT b hb, labR a ra, codeAdj_comm, codeAdj_cover_row _ _ (τ _).isLt, idx_get a ra,
        hq a ⟨b, hb⟩]
    · have ra := inR a ha
      have rb := inR b hb
      rw [labR a ra, labR b rb, codeAdj_row_row]
      simpa using ind a ra b rb
  have lab_lt (v : V) : lab v < 5 + qs.length := by
    by_cases hv : v ∈ T
    · rw [labT v hv]
      have := (τ ⟨v, hv⟩).isLt
      omega
    · rw [labR v (inR v hv), len]
      have := idx_lt v (inR v hv)
      omega
  have lab_inj : Function.Injective lab := by
    intro a b eq
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · rw [labT a ha, labT b hb] at eq
      exact congrArg Subtype.val (τ.injective (Fin.ext eq))
    · rw [labT a ha, labR b (inR b hb)] at eq
      have := (τ ⟨a, ha⟩).isLt
      omega
    · rw [labT b hb, labR a (inR a ha)] at eq
      have := (τ ⟨b, hb⟩).isLt
      omega
    · rw [labR a (inR a ha), labR b (inR b hb)] at eq
      exact idx_inj a (inR a ha) b (inR b hb) (by omega)
  have card : Fintype.card V = 5 + qs.length := by
    have tc : T.card = 5 := by
      rw [← Fintype.card_coe T, Fintype.card_congr τ, Fintype.card_fin]
    have tr : T = Rᶜ := by
      ext v
      simp [hT]
    have sum := Finset.card_add_card_compl R
    rw [← tr] at sum
    omega
  obtain ⟨e, he⟩ := exists_equiv_of_label lab lab_lt lab_inj card
  refine ⟨f, qs, e, mask_lt _ 10, len, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_ofFn]
    intro i j ij
    exact Subtype.coe_lt_coe.mpr (o.strictMono ij)
  · intro q hq'
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hq'
    obtain ⟨r, hr, eq⟩ := Finset.mem_image.mp (o i).2
    show 0 < (o i : ℕ) ∧ (o i : ℕ) < 32
    rw [← eq]
    refine ⟨?_, mask_lt _ 5⟩
    obtain ⟨t, ht, rt⟩ := nz r hr
    have bit := (hq r ⟨t, ht⟩).mpr rt
    by_contra zero
    have z : qOf r = 0 := by omega
    rw [z] at bit
    simp at bit
  · intro t
    rw [he, labT t.1 t.2]
  · intro v
    rw [he]
    by_cases hv : v ∈ T
    · rw [labT v hv]
      have := (τ ⟨v, hv⟩).isLt
      exact ⟨fun h => ((hT v).mp hv h).elim, fun h => by omega⟩
    · rw [labR v (inR v hv)]
      exact ⟨fun _ => by omega, fun _ => inR v hv⟩
  · intro a b
    rw [he, he]
    exact adj a b

section transport
variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}

lemma noSquare_iso (φ : G ≃g G') (h : NoSquare G) : NoSquare G' := by
  intro a b c d ac bd ab bc cd da
  exact h (φ.symm a) (φ.symm b) (φ.symm c) (φ.symm d)
    (φ.symm.injective.ne ac) (φ.symm.injective.ne bd)
    (φ.symm.map_adj_iff.mpr ab) (φ.symm.map_adj_iff.mpr bc)
    (φ.symm.map_adj_iff.mpr cd) (φ.symm.map_adj_iff.mpr da)

lemma independent_map_iso (φ : G ≃g G') {S : Finset V} (h : Independent G S) :
    Independent G' (S.map φ.toEquiv.toEmbedding) := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
  exact fun adj => h a ha b hb (φ.map_adj_iff.mp adj)

lemma hard_iso [Fintype V] [Fintype V'] (φ : G ≃g G') (h : Hard G Finset.univ) :
    Hard G' Finset.univ := by
  intro A _ hi
  have key := h (A.map φ.symm.toEquiv.toEmbedding) (Finset.subset_univ _)
    (independent_map_iso φ.symm hi)
  have c : Fintype.card V = Fintype.card V' := Fintype.card_congr φ.toEquiv
  rw [Finset.card_map, Finset.card_univ] at key
  rw [Finset.card_univ]
  omega

lemma exclude_iso (φ : G ≃g G') (k : ℕ)
    (h : ∀ v, ∃ A, Independent G A ∧ v ∉ A ∧ A.card + 5 = k) :
    ∀ v, ∃ A, Independent G' A ∧ v ∉ A ∧ A.card + 5 = k := by
  intro v
  obtain ⟨A, hi, hv, hc⟩ := h (φ.symm v)
  refine ⟨A.map φ.toEquiv.toEmbedding, independent_map_iso φ hi, ?_, by
    rw [Finset.card_map]; exact hc⟩
  intro hm
  obtain ⟨a, ha, eq⟩ := Finset.mem_map.mp hm
  have back : φ.symm v = a := by
    rw [← eq]
    exact φ.symm_apply_apply a
  exact hv (back ▸ ha)

end transport

def WellFormed (f : ℕ) (qs : List ℕ) : Prop :=
  f < 1024 ∧ 0 < qs.length ∧ qs.length ≤ 5 ∧ qs.Pairwise (· < ·) ∧ ∀ q ∈ qs, 0 < q ∧ q < 32

def Critical (f : ℕ) (qs : List ℕ) : Prop :=
  NoSquare (codeGraph f qs) ∧ Hard (codeGraph f qs) Finset.univ ∧
    ∀ v : Fin (5 + qs.length), ∃ A : Finset (Fin (5 + qs.length)),
      Independent (codeGraph f qs) A ∧ v ∉ A ∧ A.card + 5 = 5 + qs.length

theorem bridge (m : Fin 11) (H : SimpleGraph (Fin m.val)) (sq : NoSquare H)
    (hard : Hard H Finset.univ)
    (exclude : ∀ v : Fin m.val, ∃ A : Finset (Fin m.val), Independent H A ∧ v ∉ A ∧
      A.card + 5 = m.val) :
    ∃ (f : ℕ) (qs : List ℕ), WellFormed f qs ∧ m.val = 5 + qs.length ∧
      Nonempty (H ≃g codeGraph f qs) := by
  classical
  have ex' : ∀ v ∈ (Finset.univ : Finset (Fin m.val)), ∃ A ⊆ Finset.univ,
      Independent H A ∧ v ∉ A ∧ A.card + 5 = (Finset.univ : Finset (Fin m.val)).card := by
    intro v _
    obtain ⟨A, hi, hv, hc⟩ := exclude v
    exact ⟨A, Finset.subset_univ _, hi, hv, by simpa using hc⟩
  have five : 5 ≤ m.val := by
    simpa using hard ∅ (Finset.empty_subset _) (by simp [Independent])
  have six : 6 ≤ m.val := by
    have h := hard {⟨0, by omega⟩} (Finset.subset_univ _) (by simp [Independent])
    rw [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨R, ri, _, rc⟩ := exclude ⟨0, by omega⟩
  have tc : (Finset.univ \ R).card = 5 := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R)
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega
  have sqf : ∀ u v a b : Fin m.val, u ≠ v → a ≠ b →
      H.Adj u a → H.Adj v a → H.Adj u b → H.Adj v b → False :=
    fun u v a b uv ab ua va ub vb => sq u a v b uv ab ua va.symm vb ub.symm
  obtain ⟨f, qs, e, hf, len, sorted, bounds, _, _, adj⟩ :=
    encode_of_cover H R (Finset.univ \ R) (fun v => by simp) ri
      ((Finset.univ \ R).equivFinOfCardEq tc)
      (fun u hu => exists_neighbor_sdiff hard ex' ri (Finset.mem_univ u) hu)
      (fun u hu v hv ne =>
        neighbors_sdiff_distinct hard ex' sqf (Finset.subset_univ R) ri hu hv ne)
  have ten := m.isLt
  exact ⟨f, qs, ⟨hf, by omega, by omega, sorted, bounds⟩, by omega,
    ⟨{ toEquiv := e, map_rel_iff' := fun {a b} => (adj a b).symm }⟩⟩

theorem bridge_critical (m : Fin 11) (H : SimpleGraph (Fin m.val)) (sq : NoSquare H)
    (hard : Hard H Finset.univ)
    (exclude : ∀ v : Fin m.val, ∃ A : Finset (Fin m.val), Independent H A ∧ v ∉ A ∧
      A.card + 5 = m.val) :
    ∃ (f : ℕ) (qs : List ℕ), WellFormed f qs ∧ m.val = 5 + qs.length ∧
      Critical f qs ∧ Nonempty (H ≃g codeGraph f qs) := by
  obtain ⟨f, qs, wf, size, ⟨φ⟩⟩ := bridge m H sq hard exclude
  exact ⟨f, qs, wf, size, ⟨noSquare_iso φ sq, hard_iso φ hard,
    exclude_iso φ _ (size ▸ exclude)⟩, ⟨φ⟩⟩

end MoonPrize.Label

namespace MoonPrize.Trace

def lookup (xs : List ℕ) (i : ℕ) : ℕ := (xs[i]?).getD 0

def without (a b : ℕ) : ℕ := a ^^^ (a &&& b)

theorem without_bit (a b i : ℕ) :
    (without a b).testBit i = (a.testBit i && !b.testBit i) := by
  simp only [without, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

abbrev Compatibility := ℕ → ℕ → ℕ → ℕ → Bool

def blocked (cmp : Compatibility) (i j removed target : ℕ) : Bool :=
  removed.bitIndices.all (fun a => target.bitIndices.all (fun b => !(cmp i j a b)))

def bitset (x : ℕ) : ℕ := 2^x

def branch (d : List ℕ) (i : ℕ) : List (List ℕ) :=
  (lookup d i).bitIndices.map (fun v => d.set i (bitset v))

def step (cmp : Compatibility) (decodeMask : ℕ → ℕ) :
    Option (List (List ℕ)) → ℕ → Option (List (List ℕ))
  | some (d :: tail), code =>
    let i := code % 16
    if i < d.length then
      if code < 16 then
        if lookup d i = 0 then some tail else none
      else if code < 32 then some (branch d i ++ tail)
      else
        let j := (code / 16) % 16
        let keep := decodeMask (code / 256 - 1)
        if j < d.length && blocked cmp i j (without (lookup d i) keep) (lookup d j)
        then some (d.set i keep :: tail) else none
    else none
  | _, _ => none

def Fits (f : ℕ → ℕ) (d : List ℕ) : Prop :=
  ∀ i < d.length, (lookup d i).testBit (f i) = true

def Alive (f : ℕ → ℕ) (s : List (List ℕ)) : Prop := ∃ d ∈ s, Fits f d

theorem fits_set (f : ℕ → ℕ) (d : List ℕ) (i keep : ℕ) (hi : i < d.length)
    (fits : Fits f d) (hkeep : keep.testBit (f i) = true) : Fits f (d.set i keep) := by
  intro k hk
  have hb : k < d.length := by simpa using hk
  by_cases eq : k = i
  · subst k
    simpa [lookup, List.getElem?_set, hi] using hkeep
  · simpa [lookup, List.getElem?_set, Ne.symm eq, eq] using fits k hb

theorem blocked_sound (cmp : Compatibility) (f : ℕ → ℕ) (n i j old keep target : ℕ)
    (good : ∀ i < n, ∀ j < n, cmp i j (f i) (f j) = true)
    (hi : i < n) (hj : j < n)
    (b : blocked cmp i j (without old keep) target = true)
    (hx : old.testBit (f i) = true) (hy : target.testBit (f j) = true) :
    keep.testBit (f i) = true := by
  by_contra h
  have loss : f i ∈ (without old keep).bitIndices := by
    rw [Nat.mem_bitIndices,without_bit,hx]
    simpa using h
  have right : f j ∈ target.bitIndices := Nat.mem_bitIndices.mpr hy
  have first := List.all_eq_true.mp b _ loss
  have second := List.all_eq_true.mp first _ right
  simp [good i hi j hj] at second

def Good (f : ℕ → ℕ) (cmp : Compatibility) (d : List ℕ) : Prop :=
  Fits f d ∧ ∀ i < d.length, ∀ j < d.length, cmp i j (f i) (f j) = true

def Live (f : ℕ → ℕ) (cmp : Compatibility) (s : List (List ℕ)) : Prop :=
  ∃ d ∈ s, Good f cmp d

theorem step_sound (cmp : Compatibility) (decodeMask f : ℕ → ℕ) (s out : List (List ℕ))
    (op : ℕ) (accept : step cmp decodeMask (some s) op = some out)
    (live : Live f cmp s) : Live f cmp out := by
  rcases s with _ | ⟨d,tail⟩
  · simp [step] at accept
  obtain ⟨e,he,fit⟩ := live
  simp only [step] at accept
  split at accept
  next hi =>
    split at accept
    next low =>
      split at accept
      next empty =>
        cases accept
        rcases List.mem_cons.mp he with rfl | ht
        · have hx := fit.1 _ hi
          simp [empty] at hx
        · exact ⟨e,ht,fit⟩
      next _ => contradiction
    next high =>
      split at accept
      next mid =>
        cases accept
        rcases List.mem_cons.mp he with rfl | ht
        · let i := op % 16
          have hp : f i ∈ (lookup e i).bitIndices := Nat.mem_bitIndices.mpr (fit.1 i hi)
          refine ⟨e.set i (bitset (f i)), List.mem_append_left _ (List.mem_map.mpr ⟨_,hp,rfl⟩), ?_⟩
          constructor
          · exact fits_set _ _ _ _ hi fit.1 (by simp [bitset])
          · simpa using fit.2
        · exact ⟨e,List.mem_append_right _ ht,fit⟩
      next large =>
        split at accept
        next ok =>
          cases accept
          rcases List.mem_cons.mp he with rfl | ht
          · obtain ⟨hj,b⟩ := Bool.and_eq_true_iff.mp ok
            have hj' := of_decide_eq_true hj
            refine ⟨_,List.mem_cons_self,?_,?_⟩
            · exact fits_set _ _ _ _ hi fit.1
                (blocked_sound _ _ _ _ _ _ _ _ fit.2 hi hj' b (fit.1 _ hi) (fit.1 _ hj'))
            · simpa using fit.2
          · exact ⟨e,List.mem_cons_of_mem _ ht,fit⟩
        next _ => contradiction
  next _ => contradiction

theorem none_run (c : Compatibility) (m : ℕ → ℕ) (ops : List ℕ) :
    ops.foldl (step c m) none = none := by
  induction ops with
  | nil => rfl
  | cons a xs ih => exact ih

theorem refutes (cmp : Compatibility) (m : ℕ → ℕ) (ops : List ℕ) (dom : List ℕ)
    (closed : ops.foldl (step cmp m) (some [dom]) = some []) :
    ¬ ∃ f : ℕ → ℕ, Good f cmp dom := by
  rintro ⟨f,h⟩
  have loop (xs : List ℕ) (s t : List (List ℕ))
      (run : xs.foldl (step cmp m) (some s) = some t)
      (pre : Live f cmp s) : Live f cmp t := by
    induction xs generalizing s with
    | nil => cases run; exact pre
    | cons a l ih =>
      simp only [List.foldl_cons] at run
      cases eq : step cmp m (some s) a with
      | none => rw [eq,none_run] at run; contradiction
      | some mid => exact ih mid (eq ▸ run) (step_sound _ _ _ _ _ _ eq pre)
  obtain ⟨_,absurd,_⟩ := loop ops [dom] [] closed ⟨dom,by simp,h⟩
  simp at absurd

end MoonPrize.Trace

namespace MoonPrize.Trace

def pc8 (x : ℕ) : ℕ := (95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224 >>> (4*x)) &&& 15

def count16 (x : ℕ) : ℕ := pc8 (x &&& 255) + pc8 (x >>> 8)

def index3 (p : ℕ) := (p &&& 63) + 17 * ((p >>> 6) &&& 63) + 289 * ((p >>> 12) &&& 63)

def histogram (m a b : ℕ) : ℕ :=
  let x := count16 a
  let y := count16 b
  let z := count16 (a &&& b)
  z + 64*(x-z) + 4096*(y-z) + 262144*((m-x)-(y-z))

def rawColumn : List ℕ → ℕ → ℕ
  | [], _ => 0
  | h :: s, a => (if h &&& a == 0 then 1 else 0) + 2*rawColumn s a

def toBits (vs : List ℕ) := vs.foldr (fun j m => (1 <<< j) ||| m) 0

def admits (r s : ℕ) := (List.range 4).all (fun i => decide (((r >>> (6*i)) &&& 63) ≤ ((s >>> (6*i)) &&& 63)))

def holds (actual banned : List ℕ) : Bool :=
  banned.all (fun r => actual.all (fun s => !(admits r s)))

def tally : List ℕ → ℕ → ℕ
  | [], _ => 0
  | h :: xs, v => (if h.testBit v then 1 else 0) + 2*tally xs v

def packedAt (tab : List ℕ) (width block i : ℕ) : ℕ :=
  ((lookup tab (i / block)) >>> ((i % block) * width)) &&& (2^width - 1)

def unpack (tab : List ℕ) (len : ℕ) : List ℕ :=
  (List.range len).map (packedAt tab 20 32)

def unary (m t r p : ℕ) : Bool :=
  decide (count16 r ≤ count16 p ∧ count16 p + m ≤ t + count16 r)

def maskOf : List Bool → ℕ
  | [] => 0
  | h::tl => h.toNat + 2 * maskOf tl

def initial (rows pats : List ℕ) (n t : ℕ) : List ℕ :=
  (List.range n).map (fun i => maskOf (pats.map (unary rows.length t (tally rows i))))

def compatible (rs ps : List ℕ) (t : ℕ) : Compatibility :=
  fun i j a b => admits (histogram rs.length (tally rs i) (tally rs j))
                        (histogram t (lookup ps a) (lookup ps b))

end MoonPrize.Trace

namespace MoonPrize.Bits

def pc8 (x : ℕ) : ℕ := (95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224 >>> (4*x)) &&& 15

def count16 (x : ℕ) := pc8 (x &&& 255) + pc8 (x >>> 8)

def count : ℕ → ℕ → ℕ
  | 0,_ => 0
  | w+1,n => count w n + (if n.testBit w then 1 else 0)

def bits (w x : ℕ) : Finset ℕ := (Finset.range w).filter (fun i => x.testBit i)

theorem set_count (w x : ℕ) : (bits w x).card = count w x := by
  induction w with
  | zero => simp [bits,count]
  | succ w ih =>
    have no : w ∉ bits w x := by simp [bits]
    change ((Finset.range (w+1)).filter (fun i => x.testBit i)).card = _
    rw [Finset.range_add_one,Finset.filter_insert]
    by_cases b : x.testBit w = true
    · simp only [b,ite_true]
      change (insert w (bits w x)).card = _
      rw [Finset.card_insert_of_notMem no,ih]
      simp [count,b]
    · simp only [b]
      change (bits w x).card = _
      simp [ih,count,b]

theorem count_add (a b x : ℕ) : count (a+b) x = count a x + count b (x >>> a) := by
  induction b with
  | zero => simp [count]
  | succ b ih => simp [count,ih,Nat.testBit_shiftRight,Nat.add_assoc]

theorem count_congr (a x y : ℕ) (h : ∀ i < a, x.testBit i = y.testBit i) :
    count a x = count a y := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [count,ih (fun i hi => h i (by omega)),h a (by omega)]

set_option maxHeartbeats 2000000 in
theorem byte_correct : ∀ b : Fin 256, pc8 b.val = count 8 b.val := by decide +kernel

theorem count16_correct (x : ℕ) (bound : x < 65536) :
    count16 x = (bits 16 x).card := by
  have lo : x &&& 255 < 256 := by
    change x &&& (2^8-1) < 256
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hi : x >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have clip : count 8 (x &&& 255) = count 8 x := by
    apply count_congr
    intro i h
    have yes : (255 : ℕ).testBit i = true := by
      change ((2 : ℕ)^8-1).testBit i = true
      exact (Nat.testBit_two_pow_sub_one 8 i).trans (decide_eq_true h)
    simp [Nat.testBit_and,yes]
  rw [count16,byte_correct ⟨_,lo⟩,byte_correct ⟨_,hi⟩,clip,set_count]
  exact (count_add 8 8 x).symm

end MoonPrize.Bits

namespace MoonPrize.Marginals

def pairRows {A : Type*} [DecidableEq A] (D X Y : Finset A) (p q : Bool) : Finset A :=
  D.filter (fun a => decide (a ∈ X) = p ∧ decide (a ∈ Y) = q)

theorem pair_bound {A B : Type*} [DecidableEq A] [DecidableEq B] (f : A → B)
    (D X Y : Finset A) (S P Q : Finset B)
    (inside : ∀ a ∈ D, f a ∈ S) (inj : Set.InjOn f (D : Set A))
    (colX : ∀ a ∈ D, a ∈ X ↔ f a ∈ P) (colY : ∀ a ∈ D, a ∈ Y ↔ f a ∈ Q)
    (p q : Bool) : (pairRows D X Y p q).card ≤ (pairRows S P Q p q).card := by
  let M := pairRows D X Y p q
  have sub : M ⊆ D := Finset.filter_subset ..
  have mapped : M.image f ⊆ pairRows S P Q p q := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨ad,px,qy⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    exact ⟨inside a ad,(decide_eq_decide.mpr (colX a ad).symm).trans px,
      (decide_eq_decide.mpr (colY a ad).symm).trans qy⟩
  calc
    M.card = (M.image f).card := (Finset.card_image_of_injOn (inj.mono sub)).symm
    _ ≤ _ := Finset.card_le_card mapped

end MoonPrize.Marginals
namespace MoonPrize.Trace

def slice (m a : ℕ) : Finset ℕ := (Finset.range m).filter fun i => a.testBit i

theorem count_slice (m a : ℕ) (hm : m ≤ 16) (ha : a < 2^m) :
    count16 a = (slice m a).card := by
  have powle : 2^m ≤ (65536 : ℕ) := Nat.pow_le_pow_right (by decide) hm
  change MoonPrize.Bits.count16 a = _
  rw [MoonPrize.Bits.count16_correct a (lt_of_lt_of_le ha powle)]
  congr 1
  ext i
  simp only [MoonPrize.Bits.bits, slice, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_,b⟩
    refine ⟨?_,b⟩
    by_contra! h
    have z := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) h))
    simp [b] at z
  · rintro ⟨lt,b⟩
    exact ⟨lt_of_lt_of_le lt hm,b⟩

theorem slice_inter (m a b : ℕ) : slice m (a &&& b) = slice m a ∩ slice m b := by
  ext i
  simp [slice,Nat.testBit_and]
  tauto

theorem slice_sub (m a : ℕ) : slice m a ⊆ Finset.range m := Finset.filter_subset ..

def four (a b c d : ℕ) : ℕ := a + 64*b + 4096*c + 262144*d

lemma low_six (x : ℕ) : x &&& 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6

theorem four_admits {a b c d e f g h : ℕ} (ea : a ≤ e) (fb : b ≤ f) (gc : c ≤ g) (hd : d ≤ h)
    (he : e < 64) (hf : f < 64) (hg : g < 64) (hh : h < 64) :
    admits (four a b c d) (four e f g h) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi2 := List.mem_range.mp hi
  interval_cases i <;> simp only [decide_eq_true_eq, four,Nat.shiftRight_eq_div_pow,low_six] <;> norm_num <;> omega

def region (D X Y : Finset ℕ) (p q : Bool) := MoonPrize.Marginals.pairRows D X Y p q

lemma regionTT {D X Y : Finset ℕ} (hx : X ⊆ D) :
    region D X Y true true = X ∩ Y := by
  ext v
  simp [region,MoonPrize.Marginals.pairRows]
  tauto

lemma regionTF {D X Y : Finset ℕ} (hx : X ⊆ D) :
    region D X Y true false = X \ Y := by
  ext v
  simp [region,MoonPrize.Marginals.pairRows]
  tauto

lemma regionFT {D X Y : Finset ℕ} (hy : Y ⊆ D) :
    region D X Y false true = Y \ X := by
  ext v
  simp [region,MoonPrize.Marginals.pairRows]
  tauto

lemma regionFF {D X Y : Finset ℕ} :
    region D X Y false false = D \ (X ∪ Y) := by
  ext v
  simp [region,MoonPrize.Marginals.pairRows]

lemma hist_eq (m a b : ℕ) (hm : m ≤ 16) (ha : a < 2^m) (hb : b < 2^m) :
    histogram m a b =
    four (region (Finset.range m) (slice m a) (slice m b) true true).card
      (region (Finset.range m) (slice m a) (slice m b) true false).card
      (region (Finset.range m) (slice m a) (slice m b) false true).card
      (region (Finset.range m) (slice m a) (slice m b) false false).card := by
  have subA := slice_sub m a
  have subB := slice_sub m b
  have subAB := Finset.union_subset subA subB
  have un := Finset.card_union_add_card_inter (slice m a) (slice m b)
  have ua := Finset.card_le_card subAB
  have ia := Finset.card_le_card (Finset.inter_subset_left (s₂ := slice m b) (s₁ := slice m a))
  have ib := Finset.card_le_card (Finset.inter_subset_right (s₂ := slice m b) (s₁ := slice m a))
  simp only [histogram,count_slice m a hm ha,count_slice m b hm hb,
    count_slice m (a &&& b) hm (lt_of_le_of_lt Nat.and_le_left ha),slice_inter,
    regionTT subA,regionTF subA,regionFT subB,regionFF,Finset.card_sdiff_of_subset subAB,
    Finset.card_range,Finset.card_sdiff,Finset.inter_comm (slice m b) (slice m a),four]
  simp only [Finset.card_range] at ua
  omega

lemma region_card_lt {m a b} (hm : m ≤ 16) (p q : Bool) :
    (region (Finset.range m) (slice m a) (slice m b) p q).card < 64 := by
  have h := Finset.card_le_card (Finset.filter_subset (s := Finset.range m)
    (p := fun i => decide (i ∈ slice m a) = p ∧ decide (i ∈ slice m b) = q))
  change (region (Finset.range m) (slice m a) (slice m b) p q).card ≤ (Finset.range m).card at h
  rw [Finset.card_range] at h
  omega

lemma tally_eq (rows : List ℕ) (v : ℕ) :
    tally rows v = maskOf (rows.map (fun r => r.testBit v)) := by
  induction rows with
  | nil => rfl
  | cons x xs ih => cases h : x.testBit v <;> simp [tally,maskOf,h,ih]

lemma bit_mask (bs : List Bool) (i : ℕ) :
    (maskOf bs).testBit i = (bs[i]?).getD false := by
  induction bs generalizing i with
  | nil => simp [maskOf]
  | cons b xs ih =>
    have bit := Nat.bit_val b (maskOf xs)
    rw [Nat.add_comm] at bit
    simp only [maskOf,←bit]
    cases i with
    | zero => simp
    | succ j => simpa only [Nat.testBit_bit_succ,List.getElem?_cons_succ] using ih j

lemma mask_lt (bs : List Bool) : maskOf bs < 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b xs ih => cases b <;> simp only [maskOf,Bool.toNat_false,Bool.toNat_true,List.length_cons,pow_succ] <;> omega

lemma tally_lt (rows : List ℕ) (v : ℕ) : tally rows v < 2 ^ rows.length := by
  simpa [tally_eq] using mask_lt (rows.map (fun r => r.testBit v))

lemma tally_at (rows : List ℕ) (v i : ℕ) (hi : i < rows.length) :
    (tally rows v).testBit i = (lookup rows i).testBit v := by
  simp [tally_eq,bit_mask,lookup,hi]

def Realizes (rows pats : List ℕ) (n t : ℕ) : Prop :=
  ∃ e f : ℕ → ℕ, Set.InjOn e (↑(Finset.range rows.length) : Set ℕ) ∧
    (∀ r < rows.length, e r < t) ∧
    ∀ i < n, f i < pats.length ∧ lookup pats (f i) < 2^t ∧
      ∀ r < rows.length, (lookup rows r).testBit i = (lookup pats (f i)).testBit (e r)

theorem realization_good {rows pats : List ℕ} {n t : ℕ} (hm : rows.length ≤ 16) (ht : t ≤ 16)
    (real : Realizes rows pats n t) : ∃ f, Good f (compatible rows pats t) (initial rows pats n t) := by
  obtain ⟨e,f,inj,into,h⟩ := real
  let D := Finset.range rows.length
  let S := Finset.range t
  let X i := slice rows.length (tally rows i)
  let P i := slice t (lookup pats (f i))
  have maps : ∀ v ∈ D, e v ∈ S := by simpa [D,S] using into
  have equiv (i) (hi : i < n) (r) (hr : r ∈ D) : r ∈ X i ↔ e r ∈ P i := by
    have hr' : r < rows.length := Finset.mem_range.mp hr
    simp [X,P,slice,hr',into r hr',tally_at _ _ _ hr',(h i hi).2.2 r hr']
  have cap (i j) (hi : i<n) (hj : j<n) (p q : Bool) :
      (region D (X i) (X j) p q).card ≤ (region S (P i) (P j) p q).card :=
    MoonPrize.Marginals.pair_bound e D (X i) (X j) S (P i) (P j) maps inj (equiv i hi) (equiv j hj) p q
  have len : (initial rows pats n t).length = n := by simp [initial]
  refine ⟨f, ?_, ?_⟩
  · intro i hi
    have hi' : i < n := len ▸ hi
    have a := cap i i hi' hi' true true
    have b := cap i i hi' hi' false false
    have sa : X i ⊆ D := slice_sub .. 
    have sb : P i ⊆ S := slice_sub ..
    rw [regionTT sa,regionTT sb,Finset.inter_self,Finset.inter_self] at a
    rw [regionFF,regionFF,Finset.union_self,Finset.union_self,Finset.card_sdiff_of_subset sa,
      Finset.card_sdiff_of_subset sb] at b
    have l := Finset.card_le_card sa
    have k := Finset.card_le_card sb
    change (Finset.range rows.length).card - (X i).card ≤ (Finset.range t).card - (P i).card at b
    simp only [Finset.card_range] at b
    have l' : (X i).card ≤ rows.length := by simpa [D] using l
    have k' : (P i).card ≤ t := by simpa [S] using k
    have u : unary rows.length t (tally rows i) (lookup pats (f i)) = true := by
      simp only [unary,decide_eq_true_eq,count_slice _ _ hm (tally_lt ..),
        count_slice _ _ ht (h i hi').2.1]
      change (X i).card ≤ (P i).card ∧ (P i).card + rows.length ≤ t + (X i).card
      omega
    have hp := (h i hi').1
    simpa [initial,lookup,hi',bit_mask,List.getElem?_eq_getElem, hp] using u
  · intro i hi j hj
    have hi' := len ▸ hi
    have hj' := len ▸ hj
    unfold compatible
    rw [hist_eq _ _ _ hm (tally_lt ..) (tally_lt ..),
      hist_eq _ _ _ ht (h i hi').2.1 (h j hj').2.1]
    exact four_admits (cap i j hi' hj' _ _) (cap i j hi' hj' _ _) (cap i j hi' hj' _ _)
      (cap i j hi' hj' _ _) (region_card_lt ht _ _) (region_card_lt ht _ _)
      (region_card_lt ht _ _) (region_card_lt ht _ _)

end MoonPrize.Trace
namespace MoonPrize.Trace

def Embeds (rows paths : List ℕ) (n : ℕ) : Prop :=
  ∃ c : ℕ → ℕ, (∀ i < n, c i < 256) ∧ ∀ r ∈ rows, ∃ p ∈ paths,
    ∀ i < n, r.testBit i = (p &&& c i == 0)

lemma lookup_mem {l : List ℕ} {i : ℕ} (hi : i < l.length) : lookup l i ∈ l := by
  simp [lookup,hi]

lemma find_position {q : ℕ} {l : List ℕ} (h : q ∈ l) :
    ∃ i < l.length, lookup l i = q := by
  obtain ⟨i,hi,heq⟩ := List.getElem_of_mem h
  exact ⟨i,hi,by simpa [lookup,hi] using heq⟩

lemma raw_eq (paths : List ℕ) (c : ℕ) : rawColumn paths c = maskOf (paths.map (fun p => p &&& c == 0)) := by
  induction paths with
  | nil => rfl
  | cons a tl ih => by_cases h : a &&& c = 0 <;> simp [rawColumn,maskOf,h,ih]

lemma embeddings_rows {rows paths : List ℕ} {n : ℕ} (nd : rows.Nodup)
    (bounds : ∀ r ∈ rows, r < 2^n) {c : ℕ → ℕ}
    (real : ∀ r ∈ rows, ∃ p ∈ paths, ∀ i < n, r.testBit i = (p &&& c i == 0)) :
    ∃ e : ℕ → ℕ, Set.InjOn e (↑(Finset.range rows.length) : Set ℕ) ∧
      (∀ r < rows.length, e r < paths.length) ∧
      ∀ i < n, ∀ r < rows.length, (lookup rows r).testBit i = (lookup paths (e r) &&& c i == 0) := by
  classical
  have exists_e (r : ℕ) : ∃ j : ℕ, r < rows.length →
      j < paths.length ∧ ∀ i < n, (lookup rows r).testBit i = (lookup paths j &&& c i == 0) := by
    by_cases hr : r < rows.length
    · obtain ⟨p,hp,he⟩ := real _ (lookup_mem hr)
      obtain ⟨j,hj,eq⟩ := find_position hp
      exact ⟨j,fun _ => ⟨hj,eq ▸ he⟩⟩
    · exact ⟨0,fun h => (hr h).elim⟩
  choose e he using exists_e
  refine ⟨e,?_,fun r hr => (he r hr).1,fun i hi r hr => (he r hr).2 i hi⟩
  intro a ha b hb eq
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have eqr : lookup rows a = lookup rows b := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < n
    · rw [(he a ha').2 i hi,(he b hb').2 i hi,eq]
    · have pw : (2:ℕ)^n ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (bounds _ (lookup_mem ha')) pw),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (bounds _ (lookup_mem hb')) pw)]
  exact nd.getElem_inj_iff.mp (by simpa [lookup,ha',hb'] using eqr)

theorem embeddings_card {rows paths : List ℕ} {n : ℕ} (nd : rows.Nodup)
    (bounds : ∀ r ∈ rows, r < 2^n) (embed : Embeds rows paths n) : rows.length ≤ paths.length := by
  obtain ⟨c,_,real⟩ := embed
  obtain ⟨e,inj,into,_⟩ := embeddings_rows nd bounds real
  have sub : (Finset.range rows.length).image e ⊆ Finset.range paths.length := by
    intro u h
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_range.mpr (into r (Finset.mem_range.mp hr))
  simpa [Finset.card_image_of_injOn inj] using Finset.card_le_card sub

theorem embeddings_realize {rows paths pats : List ℕ} {n : ℕ} (nd : rows.Nodup)
    (bounds : ∀ r ∈ rows, r < 2^n)
    (options : (List.range 256).all (fun c => pats.contains (rawColumn paths c)) = true)
    (embed : Embeds rows paths n) : Realizes rows pats n paths.length := by
  classical
  obtain ⟨c,small,real⟩ := embed
  obtain ⟨e,inj,into,matched⟩ := embeddings_rows nd bounds real
  have opt (i : ℕ) : ∃ a : ℕ, i < n → a < pats.length ∧ lookup pats a = rawColumn paths (c i) := by
    by_cases hi : i < n
    · have hp := List.all_eq_true.mp options _ (List.mem_range.mpr (small i hi))
      obtain ⟨a,ha,eq⟩ := find_position (List.contains_iff_mem.mp hp)
      exact ⟨a,fun _ => ⟨ha,eq⟩⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose f hf using opt
  refine ⟨e,f,inj,into,?_⟩
  intro i hi
  refine ⟨(hf i hi).1,?_,?_⟩
  · rw [(hf i hi).2, raw_eq]
    simpa using mask_lt (paths.map fun p => p &&& c i == 0)
  · intro r hr
    have hv := into r hr
    rw [matched i hi r hr,(hf i hi).2,raw_eq,bit_mask]
    simp [lookup,hv]

end MoonPrize.Trace
namespace MoonPrize.Trace

abbrev Entry := ℕ × List ℕ × List ℕ × ℕ

namespace Entry
abbrev n (g : Entry) : ℕ := g.1
abbrev adj (g : Entry) : List ℕ := g.2.1
abbrev rows (g : Entry) : List ℕ := g.2.2.1
abbrev moves (g : Entry) : ℕ := g.2.2.2
end Entry


abbrev ShapeData := List ℕ × List ℕ

namespace ShapeData
abbrev paths (g : ShapeData) : List ℕ := g.1
abbrev pats (g : ShapeData) : List ℕ := g.2
end ShapeData


def listedOK (g : Entry) : Bool :=
  decide (10 ≤ g.rows.length ∧ g.rows.Nodup) &&
    g.rows.all (fun r => decide (r < 2^g.n) && (List.range g.n).all
      (fun i => r.testBit i == (lookup g.adj i &&& r == 0)))

def shortOps (x : ℕ) : List ℕ :=
  if x ≤ 10 then [x-1] else
    let i := (x-11)/10
    let j := (x-11) % 10
    [256+16*j+i,i]

def certified (g : Entry) (d : ShapeData) (s : ℕ) : Bool :=
  let x := (g.moves >>> (8*s)) &&& 255
  decide (x = 0 ∨ d.paths.length < g.rows.length) ||
    ((shortOps x).foldl (step (compatible g.rows d.pats d.paths.length) (fun _ => 0))
      (some [initial g.rows d.pats g.n d.paths.length]) == some [])

def supportsShape (d : ShapeData) : Bool :=
  decide (d.paths.length ≤ 16) && (List.range 256).all
    (fun c => d.pats.contains (rawColumn d.paths c))

def HardSlots (g : Entry) (si : ℕ) : Prop := (g.moves >>> (8*si)) &&& 255 = 0

theorem entry_rows {g : Entry} (ok : listedOK g = true) : 10 ≤ g.rows.length ∧ g.rows.Nodup ∧
    (∀ r ∈ g.rows, r < 2^g.n) ∧
    (∀ r ∈ g.rows, ∀ i < g.n, r.testBit i = (lookup g.adj i &&& r == 0)) := by
  obtain ⟨premises,each⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨sz,unique⟩ := of_decide_eq_true premises
  have h r (hr : r ∈ g.rows) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp each r hr)
  exact ⟨sz,unique,fun r hr => of_decide_eq_true (h r hr).1,
    fun r hr i hi => beq_iff_eq.mp (List.all_eq_true.mp (h r hr).2 i (List.mem_range.mpr hi))⟩

theorem short_sound (g : Entry) (sh : ShapeData) (si : ℕ)
    (gv : listedOK g = true) (sv : supportsShape sh = true)
    (cert : certified g sh si = true) (hard : ¬ HardSlots g si) : ¬ Embeds g.rows sh.paths g.n := by
  intro rep
  have eg := entry_rows gv
  have lens := embeddings_card eg.2.1 eg.2.2.1 rep
  have eq : ¬((g.moves >>> (8*si)) &&& 255 = 0 ∨ sh.paths.length < g.rows.length) := by
    exact not_or.mpr ⟨hard,not_lt_of_ge lens⟩
  simp only [certified,decide_eq_false eq,Bool.false_or,beq_iff_eq] at cert
  obtain ⟨tl,opts⟩ := Bool.and_eq_true_iff.mp sv
  have mt := of_decide_eq_true tl
  exact refutes _ _ _ _ cert (realization_good (lens.trans mt) mt (embeddings_realize eg.2.1 eg.2.2.1 opts rep))

theorem long_sound (g : Entry) (sh : ShapeData)
    (gv : listedOK g = true) (sv : supportsShape sh = true)
    (long : ¬ ∃ f, Good f (compatible g.rows sh.pats sh.paths.length)
        (initial g.rows sh.pats g.n sh.paths.length)) : ¬ Embeds g.rows sh.paths g.n := by
  intro rep
  have eg := entry_rows gv
  have lens := embeddings_card eg.2.1 eg.2.2.1 rep
  obtain ⟨tl,opts⟩ := Bool.and_eq_true_iff.mp sv
  have mt := of_decide_eq_true tl
  exact long (realization_good (lens.trans mt) mt (embeddings_realize eg.2.1 eg.2.2.1 opts rep))

end MoonPrize.Trace
namespace MoonPrize.Trace

theorem and_zero_iff (a r n : ℕ) (hr : r < 2^n) :
    a &&& r = 0 ↔ ∀ i < n, a.testBit i = true → r.testBit i = false := by
  constructor
  · intro h i _ ha
    have b := congrArg (fun t : ℕ => t.testBit i) h
    simpa [Nat.testBit_and,ha] using b
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and,Nat.zero_testBit]
    by_cases hi : i < n
    · cases ha : a.testBit i
      · rfl
      · simp [h i hi ha]
    · have large : r.testBit i = false := Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [large]

theorem from_graph {m : ℕ} (H : SimpleGraph (Fin m)) (g : Entry)
    (valid : listedOK g = true) (lab : Fin m ≃ Fin g.n)
    (edges : ∀ u v, H.Adj u v ↔ (lookup g.adj (lab u).val).testBit (lab v).val = true)
    (paths : List ℕ) (col : Fin m → ℕ) (bounded : ∀ u, col u < 256)
    (matchedRows : ∀ J : Finset (Fin m),
      (∀ a ∈ J, ∀ b ∈ J, ¬ H.Adj a b) →
      (∀ u, u ∉ J → ∃ v ∈ J, H.Adj u v) →
      ∃ p ∈ paths, ∀ u, u ∈ J ↔ p &&& col u = 0) : Embeds g.rows paths g.n := by
  classical
  let c (i : ℕ) := if h : i < g.n then col (lab.symm ⟨i,h⟩) else 0
  have eg := entry_rows valid
  refine ⟨c,fun i hi => by simp [c,hi,bounded],?_⟩
  intro r hr
  let J := Finset.univ.filter fun u : Fin m => r.testBit (lab u).val
  have memJ (u : Fin m) : u ∈ J ↔ r.testBit (lab u).val = true := by simp [J]
  have rowbit (u : Fin m) := eg.2.2.2 r hr (lab u).val (lab u).isLt
  have independent (u) (hu : u ∈ J) (v) (hv : v ∈ J) : ¬ H.Adj u v := by
    intro edge
    have eq := rowbit u
    rw [(memJ u).mp hu] at eq
    have zero := beq_iff_eq.mp eq.symm
    have impossible := (and_zero_iff _ _ _ (eg.2.2.1 r hr)).mp zero _ (lab v).isLt ((edges u v).mp edge)
    simp [(memJ v).mp hv] at impossible
  have dominant (u) (hu : u ∉ J) : ∃ v ∈ J, H.Adj u v := by
    by_contra! fail
    have zero := (and_zero_iff (lookup g.adj (lab u).val) r _ (eg.2.2.1 r hr)).mpr (by
      intro j hj edgepos
      let v := lab.symm ⟨j,hj⟩
      have idv : (lab v).val = j := by simp [v]
      by_contra bad
      have member : v ∈ J := (memJ _).mpr (by rw [idv]; simpa using bad)
      exact fail v member ((edges u v).mpr (by simpa [idv] using edgepos)))
    exact hu ((memJ u).mpr (by simp [rowbit u,zero]))
  obtain ⟨p,hp,good⟩ := matchedRows J independent dominant
  refine ⟨p,hp,?_⟩
  intro i hi
  let v := lab.symm ⟨i,hi⟩
  have idv : (lab v).val = i := by simp [v]
  have iff := (memJ v).symm.trans (good v)
  rw [idv] at iff
  have cv : c i = col v := by simp [c,hi,v]
  rw [cv]
  apply Bool.eq_iff_iff.mpr
  simpa using iff

end MoonPrize.Trace

namespace MoonPrize.Trace

def E0 : Entry := ⟨8, [72,144,32,65,130,4,9,18], [7,14,21,28,35,42,49,56,70,84,98,112,133,140,161,168,196,224], 0xffffffffffffffffffffffffffffffffffff⟩
def E1 : Entry := ⟨8, [200,144,32,65,130,4,9,19], [7,14,21,28,35,42,49,56,70,84,98,112,140,168,196,224], 0x2ffffffffffffffffffffffffffffffffff⟩
def E2 : Entry := ⟨8, [72,144,160,65,130,4,9,22], [7,14,21,28,35,42,49,56,70,84,98,112,161,168,224], 0x101ffffffffffffffffffffffffffffffff⟩
def E3 : Entry := ⟨8, [200,144,160,65,130,4,9,23], [7,14,21,28,35,42,49,56,70,84,98,112,168,224], 0x40404ffffffffffffffffffffffffffffff⟩
def E4 : Entry := ⟨8, [72,144,160,65,130,132,9,54], [7,14,21,28,35,42,49,56,70,84,98,112,129,136,192], 0x101ffffffffffffffffffffffffffffffff⟩
def E5 : Entry := ⟨8, [200,144,160,65,130,132,9,55], [7,14,21,28,35,42,49,56,70,84,98,112,136,192], 0x40404ffffffffffffffffffffffffffffff⟩
def E6 : Entry := ⟨8, [72,80,160,65,130,132,11,52], [7,14,21,28,35,42,49,56,84,112,131,138,192], 0xc0c0c01ff0cffffffffffff02ffffffffff⟩
def E7 : Entry := ⟨8, [200,80,160,65,130,132,11,53], [7,14,21,28,35,42,49,56,84,112,138,192], 0x181818170218021702ffffff1717ffffffff⟩
def E8 : Entry := ⟨8, [72,208,160,65,130,132,11,54], [7,14,21,28,35,42,49,56,84,112,129,136,192], 0xd0d0d01ff0dffffffffffff05ffffffffff⟩
def E9 : Entry := ⟨8, [72,208,160,65,2,132,139,102], [7,14,21,28,35,42,49,56,84,112,145,152], 0xe0e0e0d010e010d01ffffff0d0dffffffff⟩
def E10 : Entry := ⟨8, [104,208,160,65,130,133,11,54], [7,14,21,28,42,56,84,112,129,136,192], 0x220022000d0dffff00220dffffff⟩
def R10 := E10.rows
def E11 : Entry := ⟨8, [168,144,96,193,130,5,12,27], [7,14,21,28,42,56,67,81,98,112,132,224], 0x191919170219021702ffffff1717ffffffff⟩
def E12 : Entry := ⟨8, [168,208,96,65,130,5,14,19], [7,14,21,28,42,56,81,112,140,168,224], 0x24242424232423240d0dffff24230dffffff⟩
def E13 : Entry := ⟨8, [168,208,96,65,130,133,14,51], [7,14,21,28,42,56,81,112,140,192], 0x30d00000003030d⟩
def R13 := E13.rows
def E14 : Entry := ⟨8, [104,208,160,1,66,133,19,38], [7,14,21,28,42,56,76,104,145,152,200], 0x22222222042222220d0dffff22220dffffff⟩
def E15 : Entry := ⟨8, [168,208,96,129,66,5,22,11], [7,14,21,28,42,56,65,104,148,176,224], 0x24242424222422240d0dffff24220dffffff⟩
def E16 : Entry := ⟨8, [168,208,64,33,130,9,6,19], [7,14,21,28,38,52,81,88,112,140,164,200,224], 0xe0e0e04ff0effffffffffff05ffffffffff⟩
def E17 : Entry := ⟨8, [40,80,192,33,130,9,6,20], [7,14,21,28,38,52,81,88,112,131,138,162,193,200,224], 0x101ffffffffffffffffffffffffffffffff⟩
def E18 : Entry := ⟨8, [168,80,192,33,130,9,6,21], [7,14,21,28,38,52,81,88,112,138,162,200,224], 0xe0e0e02ff0effffffffffff03ffffffffff⟩
def E19 : Entry := ⟨8, [168,208,128,33,66,9,18,7], [7,14,21,28,38,52,69,76,100,152,176,200,224], 0x3030303ff03ffffffffffff03ffffffffff⟩
def E20 : Entry := ⟨8, [152,48,224,65,131,6,12,21], [7,14,28,56,67,97,112,138,168,194,224], 0x1a1a1a1a181a181a0c0cffff1a180cffffff⟩
def E21 : Entry := ⟨8, [88,176,96,193,3,134,13,42], [7,14,28,33,56,66,112,133,148,208], 0x30d00000003030d⟩
def R21 := E21.rows
def E22 : Entry := ⟨9, [272,32,64,128,257,2,4,8,17], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,270,300,330,360,390,420,450,480], 0xffffffffffffffffffffffffffffffffffff⟩
def E23 : Entry := ⟨9, [272,288,64,128,257,2,4,8,19], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,300,360,420,480], 0xffffffffffffffffffffffffffffffffffff⟩
def E24 : Entry := ⟨9, [272,288,320,128,257,2,4,8,23], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,360,480], 0xffffffffffffffffffffffffffffffffffff⟩
def E25 : Entry := ⟨9, [272,288,320,384,257,2,4,8,31], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,480], 0xffffffffffffffffffffffffffffffffffff⟩
def E26 : Entry := ⟨9, [272,288,64,128,257,258,4,8,51], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,268,328,388,448], 0xffffffffffffffffffffffffffffffffffff⟩
def E27 : Entry := ⟨9, [272,288,320,128,257,258,4,8,55], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,328,448], 0xffffffffffffffffffffffffffffffffffff⟩
def E28 : Entry := ⟨9, [272,288,320,384,257,258,4,8,63], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,448], 0xffffffffffffffffffffffffffffffffffff⟩
def E29 : Entry := ⟨9, [272,288,320,128,257,258,260,8,119], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,264,384], 0xffffffffffffffffffffffffffffffffffff⟩
def E30 : Entry := ⟨9, [272,288,320,384,257,258,260,8,127], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,384], 0xffffffffffffffffffffffffffffffffffff⟩
def E31 : Entry := ⟨9, [272,288,320,384,257,258,260,264,255], [15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,256], 0xffffffffffffffffffffffffffffffffffff⟩
def E32 : Entry := ⟨9, [400,288,64,128,257,2,4,9,19], [15,30,45,60,75,90,105,120,150,180,210,240,300,360,420,480], 0x2ffffffffffffffffffffffffffffffffff⟩
def E33 : Entry := ⟨9, [400,288,320,128,257,2,4,9,23], [15,30,45,60,75,90,105,120,150,180,210,240,360,480], 0x40404ffffffffffffffffffffffffffffff⟩
def E34 : Entry := ⟨9, [144,32,64,384,257,2,4,9,24], [15,30,45,60,75,90,105,120,150,180,210,240,263,293,323,353,390,420,450,480], 0xffffffffffffffffffffffffffffffffffff⟩
def E35 : Entry := ⟨9, [144,288,64,384,257,2,4,9,26], [15,30,45,60,75,90,105,120,150,180,210,240,293,353,420,480], 0x1ffffffffffffffffffffffffffffffffff⟩
def E36 : Entry := ⟨9, [144,288,320,384,257,2,4,9,30], [15,30,45,60,75,90,105,120,150,180,210,240,353,480], 0x10101ffffffffffffffffffffffffffffff⟩
def E37 : Entry := ⟨9, [144,288,64,128,1,258,4,9,34], [15,30,45,60,75,90,105,120,150,180,210,240,269,284,329,344,404,464], 0xffffffffffffffffffffffffffffffffffff⟩
def E38 : Entry := ⟨9, [400,288,64,128,1,258,4,9,35], [15,30,45,60,75,90,105,120,150,180,210,240,284,344,404,464], 0x2ffffffffffffffffffffffffffffffffff⟩
def E39 : Entry := ⟨9, [144,288,320,128,1,258,4,9,38], [15,30,45,60,75,90,105,120,150,180,210,240,329,344,464], 0x101ffffffffffffffffffffffffffffffff⟩
def E40 : Entry := ⟨9, [400,288,320,128,1,258,4,9,39], [15,30,45,60,75,90,105,120,150,180,210,240,344,464], 0x40404ffffffffffffffffffffffffffffff⟩
def E41 : Entry := ⟨9, [144,288,64,384,1,258,4,9,42], [15,30,45,60,75,90,105,120,150,180,210,240,261,321,404,464], 0x1ffffffffffffffffffffffffffffffffff⟩
def E42 : Entry := ⟨9, [144,288,320,384,1,258,4,9,46], [15,30,45,60,75,90,105,120,150,180,210,240,321,464], 0x10101ffffffffffffffffffffffffffffff⟩
def E43 : Entry := ⟨9, [400,288,64,128,257,258,4,9,51], [15,30,45,60,75,90,105,120,150,180,210,240,268,328,388,448], 0x2ffffffffffffffffffffffffffffffffff⟩
def E44 : Entry := ⟨9, [400,288,320,128,257,258,4,9,55], [15,30,45,60,75,90,105,120,150,180,210,240,328,448], 0x40404ffffffffffffffffffffffffffffff⟩
def E45 : Entry := ⟨9, [144,288,64,384,257,258,4,9,58], [15,30,45,60,75,90,105,120,150,180,210,240,261,321,388,448], 0x1ffffffffffffffffffffffffffffffffff⟩
def E46 : Entry := ⟨9, [144,288,320,384,257,258,4,9,62], [15,30,45,60,75,90,105,120,150,180,210,240,321,448], 0x10101ffffffffffffffffffffffffffffff⟩
def E47 : Entry := ⟨9, [144,288,320,128,1,258,260,9,102], [15,30,45,60,75,90,105,120,150,180,210,240,265,280,400], 0x101ffffffffffffffffffffffffffffffff⟩
def E48 : Entry := ⟨9, [400,288,320,128,1,258,260,9,103], [15,30,45,60,75,90,105,120,150,180,210,240,280,400], 0x40404ffffffffffffffffffffffffffffff⟩
def E49 : Entry := ⟨9, [144,288,320,384,1,258,260,9,110], [15,30,45,60,75,90,105,120,150,180,210,240,257,400], 0x10101ffffffffffffffffffffffffffffff⟩
def E50 : Entry := ⟨9, [400,288,320,128,257,258,260,9,119], [15,30,45,60,75,90,105,120,150,180,210,240,264,384], 0x40404ffffffffffffffffffffffffffffff⟩
def E51 : Entry := ⟨9, [144,288,320,384,257,258,260,9,126], [15,30,45,60,75,90,105,120,150,180,210,240,257,384], 0x10101ffffffffffffffffffffffffffffff⟩
def E52 : Entry := ⟨9, [400,288,64,128,1,258,4,265,163], [15,30,45,60,75,90,105,120,150,180,210,240,284,344], 0x40404ffffffffffffffffffffffffffffff⟩
def E53 : Entry := ⟨9, [400,288,320,128,1,258,4,265,167], [15,30,45,60,75,90,105,120,150,180,210,240,344], 0x4040404ff04ffffffffffff02ffffffffff⟩
def E54 : Entry := ⟨9, [400,288,320,128,1,258,260,265,231], [15,30,45,60,75,90,105,120,150,180,210,240,280], 0x4040404ff04ffffffffffff02ffffffffff⟩
def E55 : Entry := ⟨9, [144,160,320,384,257,2,4,11,28], [15,30,45,60,75,90,105,120,180,240,323,353,480], 0xc0c0c02ff0cffffffffffff01ffffffffff⟩
def E56 : Entry := ⟨9, [400,160,320,128,257,258,4,11,53], [15,30,45,60,75,90,105,120,180,240,330,448], 0x40404040204020402ffffff0404ffffffff⟩
def E57 : Entry := ⟨9, [144,160,64,384,257,258,4,11,56], [15,30,45,60,75,90,105,120,180,240,263,323,388,448], 0xc0c0cffffffffffffffffffffffffffffff⟩
def E58 : Entry := ⟨9, [144,160,320,384,257,258,4,11,60], [15,30,45,60,75,90,105,120,180,240,323,448], 0xc0c0c0c010c010c01ffffff0c0cffffffff⟩
def E59 : Entry := ⟨9, [144,160,320,384,1,2,260,11,76], [15,30,45,60,75,90,105,120,180,240,259,274,289,432], 0x30303ffffffffffffffffffffffffffffff⟩
def E60 : Entry := ⟨9, [144,160,320,128,257,2,260,11,84], [15,30,45,60,75,90,105,120,180,240,267,297,416], 0x4040402ff04ffffffffffff01ffffffffff⟩
def E61 : Entry := ⟨9, [400,160,320,128,257,2,260,11,85], [15,30,45,60,75,90,105,120,180,240,266,296,416], 0x4040402ff04ffffffffffff04ffffffffff⟩
def E62 : Entry := ⟨9, [144,416,320,128,257,2,260,11,86], [15,30,45,60,75,90,105,120,180,240,297,416], 0x40404040104010401ffffff0404ffffffff⟩
def E63 : Entry := ⟨9, [144,160,320,384,257,2,260,11,92], [15,30,45,60,75,90,105,120,180,240,259,289,416], 0xc0c0c02ff0cffffffffffff01ffffffffff⟩
def E64 : Entry := ⟨9, [144,160,320,128,257,258,260,11,116], [15,30,45,60,75,90,105,120,180,240,267,384], 0x40404040104010401ffffff0404ffffffff⟩
def E65 : Entry := ⟨9, [400,160,320,128,257,258,260,11,117], [15,30,45,60,75,90,105,120,180,240,266,384], 0x40404040204020402ffffff0404ffffffff⟩
def E66 : Entry := ⟨9, [144,160,320,384,257,258,260,11,124], [15,30,45,60,75,90,105,120,180,240,259,384], 0xc0c0c0c010c010c01ffffff0c0cffffffff⟩
def E67 : Entry := ⟨9, [400,160,320,128,1,2,260,267,197], [15,30,45,60,75,90,105,120,180,240,282,312], 0x40404040204020402ffffff0404ffffffff⟩
def E68 : Entry := ⟨9, [144,160,320,384,1,2,260,267,204], [15,30,45,60,75,90,105,120,180,240,259,274,289,304], 0x30303ffffffffffffffffffffffffffffff⟩
def E69 : Entry := ⟨9, [400,160,192,128,257,258,260,15,113], [15,30,45,60,75,90,105,120,240,270,384], 0x4040404040404040404ffff040404ffffff⟩
def E70 : Entry := ⟨9, [144,160,192,384,257,258,260,15,120], [15,30,45,60,75,90,105,120,240,263,384], 0xf0f0f0f040f0c0f0c0cffff0f0f0cffffff⟩
def E71 : Entry := ⟨9, [144,288,320,256,129,2,4,17,14], [15,30,45,60,75,90,105,120,142,172,202,232,353,368,480], 0x101ffffffffffffffffffffffffffffffff⟩
def E72 : Entry := ⟨9, [400,288,320,256,129,2,4,17,15], [15,30,45,60,75,90,105,120,142,172,202,232,368,480], 0x40404ffffffffffffffffffffffffffffff⟩
def E73 : Entry := ⟨9, [400,160,320,256,129,258,4,19,45], [15,30,45,60,75,90,105,120,172,232,338,448], 0x40404040204020402ffffff0404ffffffff⟩
def E74 : Entry := ⟨9, [336,416,64,128,257,2,5,10,19], [15,30,45,60,90,120,165,180,240,300,360,420,480], 0x6060606ff06ffffffffffff05ffffffffff⟩
def E75 : Entry := ⟨9, [80,160,320,128,257,2,5,10,20], [15,30,45,60,90,120,165,180,240,267,297,330,360,417,480], 0x101ffffffffffffffffffffffffffffffff⟩
def E76 : Entry := ⟨9, [80,416,320,128,257,2,5,10,22], [15,30,45,60,90,120,165,180,240,297,360,417,480], 0x6060601ff06ffffffffffff03ffffffffff⟩
def E77 : Entry := ⟨9, [80,160,320,384,257,2,5,10,28], [15,30,45,60,90,120,165,180,240,259,322,417,480], 0xc0c0c01ff0cffffffffffff03ffffffffff⟩
def E78 : Entry := ⟨9, [336,416,64,128,257,258,5,10,51], [15,30,45,60,90,120,165,180,240,268,328,388,448], 0xd0d0d07ff0dffffffffffff05ffffffffff⟩
def E79 : Entry := ⟨9, [80,416,320,128,257,258,5,10,54], [15,30,45,60,90,120,165,180,240,265,328,385,448], 0xd0d0d01ff0dffffffffffff03ffffffffff⟩
def E80 : Entry := ⟨9, [80,160,320,384,257,258,5,10,60], [15,30,45,60,90,120,165,180,240,259,322,385,448], 0xc0c0c01ff0cffffffffffff03ffffffffff⟩
def E81 : Entry := ⟨9, [336,416,64,128,1,258,261,10,99], [15,30,45,60,90,120,165,180,240,284,404], 0xd0d0d0d030d0d0d0d0dffff0d0d0dffffff⟩
def E82 : Entry := ⟨9, [336,160,64,384,1,258,261,10,105], [15,30,45,60,90,120,165,180,240,278,404], 0xd0d0d0d030d0d0d0d0dffff0d0d0dffffff⟩
def E83 : Entry := ⟨9, [208,416,320,128,257,258,5,11,54], [15,30,45,60,90,120,180,240,265,328,448], 0xe0e0e0e040e0e0e0d0dffff0e0e0dffffff⟩
def E84 : Entry := ⟨9, [208,160,320,384,257,258,5,11,60], [15,30,45,60,90,120,180,240,259,322,448], 0x1a1a1a1a171a171a0c0cffff1a170cffffff⟩
def E85 : Entry := ⟨9, [208,416,320,128,1,258,261,11,102], [15,30,45,60,90,120,180,240,265,280,400], 0xe0e0e0e040e0e0e0d0dffff0e0e0dffffff⟩
def E86 : Entry := ⟨9, [336,288,192,128,257,2,5,12,19], [15,30,45,60,90,120,131,161,210,240,300,360,480], 0x17171702ff17ffffffffffff05ffffffffff⟩
def E87 : Entry := ⟨9, [80,288,448,128,257,2,5,12,22], [15,30,45,60,90,120,131,210,240,297,360,417,480], 0xc0c0c01ff0cffffffffffff05ffffffffff⟩
def E88 : Entry := ⟨9, [80,32,192,384,257,2,5,12,24], [15,30,45,60,90,120,210,240,263,293,387,417,450,480], 0xd0d0dffffffffffffffffffffffffffffff⟩
def E89 : Entry := ⟨9, [336,32,192,384,257,2,5,12,25], [15,30,45,60,90,120,131,161,210,240,262,292,450,480], 0x222222ffffffffffffffffffffffffffffff⟩
def E90 : Entry := ⟨9, [80,288,192,384,257,2,5,12,26], [15,30,45,60,90,120,131,210,240,293,417,480], 0xd0d0d0c010d010c01ffffff0c0cffffffff⟩
def E91 : Entry := ⟨9, [336,288,192,384,257,2,5,12,27], [15,30,45,60,90,120,131,161,210,240,292,480], 0x222222170222021702ffffff1717ffffffff⟩
def E92 : Entry := ⟨9, [336,288,192,128,1,258,5,12,35], [15,30,45,60,90,120,131,161,210,240,284,344,464], 0x5050502ff05ffffffffffff05ffffffffff⟩
def E93 : Entry := ⟨9, [80,288,448,128,1,258,5,12,38], [15,30,45,60,90,120,131,161,210,240,265,344,385,464], 0x20202ffffffffffffffffffffffffffffff⟩
def E94 : Entry := ⟨9, [80,288,192,384,1,258,5,12,42], [15,30,45,60,90,120,131,161,210,240,261,276,385,464], 0x20202ffffffffffffffffffffffffffffff⟩
def E95 : Entry := ⟨9, [336,288,192,384,1,258,5,12,43], [15,30,45,60,90,120,131,161,210,240,276,464], 0x1919190f0219020f02ffffff1717ffffffff⟩
def E96 : Entry := ⟨9, [336,288,192,128,257,258,5,12,51], [15,30,45,60,90,120,131,161,210,240,268,328,448], 0x17171702ff17ffffffffffff05ffffffffff⟩
def E97 : Entry := ⟨9, [80,288,448,128,257,258,5,12,54], [15,30,45,60,90,120,131,161,210,240,265,328,385,448], 0x20202ffffffffffffffffffffffffffffff⟩
def E98 : Entry := ⟨9, [80,288,192,384,257,258,5,12,58], [15,30,45,60,90,120,131,161,210,240,261,385,448], 0xd0d0d02ff0dffffffffffff01ffffffffff⟩
def E99 : Entry := ⟨9, [336,288,192,384,257,258,5,12,59], [15,30,45,60,90,120,131,161,210,240,260,448], 0x1a1a1a17021a021702ffffff1717ffffffff⟩
def E100 : Entry := ⟨9, [80,288,448,128,1,2,261,12,70], [15,30,45,60,90,120,131,210,240,297,312,417,432], 0xc0c0c01ff0cffffffffffff0cffffffffff⟩
def E101 : Entry := ⟨9, [336,32,192,384,1,2,261,12,73], [15,30,45,60,90,120,131,161,210,240,278,308,402,432], 0x50505ffffffffffffffffffffffffffffff⟩
def E102 : Entry := ⟨9, [336,288,192,384,1,2,261,12,75], [15,30,45,60,90,120,131,161,210,240,308,432], 0x1919190f0219020f02ffffff1717ffffffff⟩
def E103 : Entry := ⟨9, [336,288,192,128,1,258,261,12,99], [15,30,45,60,90,120,131,161,210,240,284,400], 0x1919190f0219020f02ffffff1717ffffffff⟩
def E104 : Entry := ⟨9, [80,288,448,128,1,258,261,12,102], [15,30,45,60,90,120,131,161,210,240,265,280,385,400], 0x20202ffffffffffffffffffffffffffffff⟩
def E105 : Entry := ⟨9, [336,288,192,384,1,258,261,12,107], [15,30,45,60,90,120,131,161,210,240,276,400], 0x1919190f0219020f02ffffff1717ffffffff⟩
def E106 : Entry := ⟨9, [336,32,192,384,1,2,5,268,137], [15,30,45,60,90,120,131,161,210,240,278,308,338,368], 0x50505ffffffffffffffffffffffffffffff⟩
def E107 : Entry := ⟨9, [336,288,192,384,1,2,5,268,139], [15,30,45,60,90,120,131,161,210,240,308,368], 0x1919190f0219020f02ffffff1717ffffffff⟩
def E108 : Entry := ⟨9, [336,32,192,384,257,2,5,268,153], [15,30,45,60,90,120,131,161,210,240,262,292,322,352], 0x222222ffffffffffffffffffffffffffffff⟩
def E109 : Entry := ⟨9, [336,288,192,384,257,2,5,268,155], [15,30,45,60,90,120,131,161,210,240,292,352], 0x222222170222021702ffffff1717ffffffff⟩
def E110 : Entry := ⟨9, [336,288,192,128,1,258,5,268,163], [15,30,45,60,90,120,131,161,210,240,284,344], 0x1818180f0218020f02ffffff1717ffffffff⟩
def E111 : Entry := ⟨9, [336,288,192,384,1,258,5,268,171], [15,30,45,60,90,120,131,161,210,240,276,336], 0x1919190f0219020f02ffffff1717ffffffff⟩
def E112 : Entry := ⟨9, [336,288,192,384,257,258,5,268,187], [15,30,45,60,90,120,131,161,210,240,260,320], 0x1a1a1a17021a021702ffffff1717ffffffff⟩
def E113 : Entry := ⟨9, [336,416,192,128,257,2,5,14,19], [15,30,45,60,90,120,161,240,300,360,480], 0x18181818041818180d0dffff18180dffffff⟩
def E114 : Entry := ⟨9, [336,416,192,128,1,258,5,14,35], [15,30,45,60,90,120,161,240,284,344,464], 0x18181818041818180d0dffff18180dffffff⟩
def E115 : Entry := ⟨9, [336,160,192,384,1,258,5,14,41], [15,30,45,60,90,120,161,240,278,338,464], 0x1a1a1a1a051a171a0d0dffff1a1a0dffffff⟩
def E116 : Entry := ⟨9, [336,160,192,128,257,258,5,14,49], [15,30,45,60,90,120,161,240,270,330,448], 0x18181818041817180d0dffff18180dffffff⟩
def E117 : Entry := ⟨9, [336,416,192,128,257,258,5,14,51], [15,30,45,60,90,120,161,240,268,328,448], 0x18181818041818180d0dffff18180dffffff⟩
def E118 : Entry := ⟨9, [80,160,192,384,257,258,5,14,56], [15,30,45,60,90,120,161,240,263,322,385,448], 0xd0d0d0c010d010c01ffffff0c0cffffffff⟩
def E119 : Entry := ⟨9, [336,160,192,384,257,258,5,14,57], [15,30,45,60,90,120,161,240,262,322,448], 0x1a1a1a1a191a171a0d0dffff1a190dffffff⟩
def E120 : Entry := ⟨9, [336,160,192,384,1,2,261,14,73], [15,30,45,60,90,120,161,240,278,308,432], 0x19191919051919191717ffff191917ffffff⟩
def E121 : Entry := ⟨9, [80,416,192,128,1,258,261,14,98], [15,30,45,60,90,120,161,240,269,284,385,400], 0xe0e0e0e010e010e01ffffff0e0effffffff⟩
def E122 : Entry := ⟨9, [336,416,192,128,1,258,261,14,99], [15,30,45,60,90,120,161,240,284,400], 0x222222222222222222220304222222030304⟩
def E123 : Entry := ⟨9, [336,160,192,384,1,258,261,14,105], [15,30,45,60,90,120,161,240,278,400], 0x17170305000017030305⟩
def R123 := E123.rows
def E124 : Entry := ⟨9, [336,416,192,128,257,2,5,270,147], [15,30,45,60,90,120,161,240,300,360], 0x181818180418181818180306181818030306⟩
def E125 : Entry := ⟨9, [208,416,64,256,129,2,261,19,74], [15,30,45,60,90,120,172,232,293,308,420], 0xd0d0d0d030d0d0d0d0dffff0d0d0dffffff⟩
def E126 : Entry := ⟨9, [336,288,192,256,385,2,5,20,27], [15,30,45,60,90,120,139,169,202,232,292,480], 0x40404040204020402ffffff0404ffffffff⟩
def E127 : Entry := ⟨9, [336,416,192,256,129,2,5,22,11], [15,30,45,60,90,120,169,232,308,368,480], 0xe0e0e0e040e0e0e0d0dffff0e0e0dffffff⟩
def E128 : Entry := ⟨9, [336,416,192,256,129,2,261,22,75], [15,30,45,60,90,120,169,232,308,416], 0xe0e0e0e040e0e0e0e0e03060e0e0e030306⟩
def E129 : Entry := ⟨9, [336,160,192,256,129,258,261,22,105], [15,30,45,60,90,120,169,232,278,384], 0xe0e0e0e040e0e0e0e0e030d0e0e0e03030d⟩
def E130 : Entry := ⟨9, [336,288,192,384,129,2,5,28,11], [15,30,45,60,90,120,131,161,194,308,368,480], 0x222222170222021702ffffff1717ffffffff⟩
def E131 : Entry := ⟨9, [336,32,192,384,129,2,261,28,73], [15,30,45,60,90,120,131,161,194,224,278,308,386,416], 0x222222ffffffffffffffffffffffffffffff⟩
def E132 : Entry := ⟨9, [336,288,192,384,129,2,261,28,75], [15,30,45,60,90,120,131,161,194,224,308,416], 0x222222170222021702ffffff1717ffffffff⟩
def E133 : Entry := ⟨9, [336,160,192,256,1,130,261,38,73], [15,30,45,60,90,120,137,216,278,308,400], 0xe0e0e0e040e0e0e0e0effff0e0e0effffff⟩
def E134 : Entry := ⟨9, [80,416,192,256,1,130,261,38,74], [15,30,45,60,90,120,137,216,293,308,385,400], 0xe0e0e0e010e010e01ffffff0e0effffffff⟩
def E135 : Entry := ⟨9, [336,416,192,256,1,130,261,38,75], [15,30,45,60,90,120,137,216,308,400], 0xe0e0e0e040e0e0e0e0e03050e0e0e030305⟩
def E136 : Entry := ⟨9, [208,288,320,384,257,2,133,73,30], [15,30,45,60,90,120,150,180,289,352,416], 0x170000001717ffff000017ffffff⟩
def R136 := E136.rows
def E137 : Entry := ⟨9, [208,288,320,384,1,258,133,73,46], [15,30,45,60,90,120,150,180,257,336,400], 0x19191919051919191717ffff191917ffffff⟩
def E138 : Entry := ⟨9, [464,288,64,128,257,258,133,73,51], [15,30,45,60,90,120,150,180,268,328,388], 0x17171717031717171717ffff171717ffffff⟩
def E139 : Entry := ⟨9, [208,288,320,384,257,258,133,73,62], [15,30,45,60,90,120,150,180,257,320,384], 0x170000001717ffff000017ffffff⟩
def R139 := E139.rows
def E140 : Entry := ⟨9, [208,416,320,128,257,258,133,75,54], [15,30,45,60,90,120,180,265,328,384], 0xe0e0e0e040e0e0e0e0e030d0e0e0e03030d⟩
def E141 : Entry := ⟨9, [208,160,320,384,257,258,133,75,60], [15,30,45,60,90,120,180,259,322,384], 0x2222020c00002202020c⟩
def R141 := E141.rows
def E142 : Entry := ⟨9, [80,96,320,384,129,130,263,312,204], [15,30,45,60,120,135,192,259,274,289,304], 0xf0f0f0f0e0f0c0f0c0cffff0f0e0cffffff⟩
def E143 : Entry := ⟨9, [144,160,192,320,257,258,12,7,56], [15,30,45,60,82,97,184,240,263,323,448], 0xf0f0f0f0e0f0c0f0c0cffff0f0e0cffffff⟩
def E144 : Entry := ⟨9, [400,160,192,320,257,258,12,7,57], [15,30,45,60,67,82,97,184,240,262,322,448], 0x1a1a1a1a031a031a03ffffff1818ffffffff⟩
def E145 : Entry := ⟨9, [144,160,192,320,257,2,268,7,88], [15,30,45,60,67,82,97,184,240,263,293,416], 0xf0f0f0f020f020f02ffffff0d0dffffffff⟩
def E146 : Entry := ⟨9, [400,160,192,320,257,2,268,7,89], [15,30,45,60,67,82,97,184,240,262,292,416], 0x222222180222021802ffffff1818ffffffff⟩
def E147 : Entry := ⟨9, [144,416,192,320,257,2,268,7,90], [15,30,45,60,67,82,97,184,240,293,416], 0xf0f0f0f0e0f0d0f0d0dffff0f0e0dffffff⟩
def E148 : Entry := ⟨9, [400,160,192,64,257,258,268,7,113], [15,30,45,60,67,82,97,184,240,270,392], 0x1a1a1a1a191a171a1717ffff1a1917ffffff⟩
def E149 : Entry := ⟨9, [144,160,448,64,257,258,268,7,116], [15,30,45,60,67,82,97,184,240,267,392], 0xf0f0f0f0f0f0c0f0c0cffff0f0f0cffffff⟩
def E150 : Entry := ⟨9, [144,160,192,320,257,258,268,7,120], [15,30,45,60,67,82,97,184,240,263,384], 0xf0f0f0f0e0f0c0f0c0cffff0f0e0cffffff⟩
def E151 : Entry := ⟨9, [400,160,192,320,257,258,268,7,121], [15,30,45,60,67,82,97,184,240,262,384], 0x1a1a1a1a181a171a1717ffff1a1817ffffff⟩
def E152 : Entry := ⟨9, [144,288,192,320,257,2,396,69,90], [15,30,45,60,67,82,97,112,154,184,293,416], 0xd0d0d0c010d010c01ffffff0c0cffffffff⟩
def E153 : Entry := ⟨9, [336,416,128,256,65,2,17,6,11], [15,30,45,60,78,108,169,184,232,308,356,432,480], 0x4040404ff04ffffffffffff04ffffffffff⟩
def E154 : Entry := ⟨9, [80,416,128,256,65,2,17,262,138], [15,30,45,60,78,108,169,184,232,293,308,356], 0x30303030303030303ffffff0303ffffffff⟩
def E155 : Entry := ⟨9, [336,416,128,256,65,2,17,262,139], [15,30,45,60,78,108,169,184,232,308,356], 0x4040404030404040404ffff040404ffffff⟩
def E156 : Entry := ⟨9, [80,288,384,128,65,2,17,12,6], [15,30,45,60,78,108,131,146,194,297,312,360,417,432,480], 0x101ffffffffffffffffffffffffffffffff⟩
def E157 : Entry := ⟨9, [304,96,448,128,257,3,6,12,21], [15,30,60,73,120,131,146,193,240,266,360,386,480], 0x1a1a1a05ff1affffffffffff02ffffffffff⟩
def E158 : Entry := ⟨9, [48,96,192,384,257,3,6,12,24], [15,30,60,73,120,146,240,263,292,387,449,480], 0xc0c0c0c010c010c01ffffff0c0cffffffff⟩
def E159 : Entry := ⟨9, [304,96,192,384,257,3,6,12,25], [15,30,60,73,120,131,146,193,240,262,292,386,480], 0xd0d0d03ff0dffffffffffff02ffffffffff⟩
def E160 : Entry := ⟨9, [48,352,192,384,257,3,6,12,26], [15,30,60,73,120,131,146,240,261,292,449,480], 0xf0f0f0d010f010d01ffffff0d0dffffffff⟩
def E161 : Entry := ⟨9, [304,96,448,128,1,259,6,12,37], [15,30,60,73,120,131,193,240,282,344,402,464], 0x1919190f0219020f02ffffff1917ffffffff⟩
def E162 : Entry := ⟨9, [304,96,192,384,1,259,6,12,41], [15,30,60,73,120,131,193,240,278,402,464], 0x171717170f1717171717ffff171717ffffff⟩
def E163 : Entry := ⟨9, [48,352,192,384,1,259,6,12,42], [15,30,60,73,120,131,146,240,261,276,449,464], 0x2222220d0122010d01ffffff0d0dffffffff⟩
def E164 : Entry := ⟨9, [304,96,448,128,1,3,262,12,69], [15,30,60,73,120,131,193,240,282,312,402,432], 0x1919190f0219020f02ffffff1917ffffffff⟩
def E165 : Entry := ⟨9, [304,96,192,384,1,3,262,12,73], [15,30,60,73,120,131,193,240,278,308,402,432], 0x1717170d0217020d02ffffff1717ffffffff⟩
def E166 : Entry := ⟨9, [48,352,192,384,1,3,262,12,74], [15,30,60,73,120,131,146,193,240,261,308,385,432], 0x10101003ff10ffffffffffff01ffffffffff⟩
def E167 : Entry := ⟨9, [304,96,192,128,257,3,262,12,81], [15,30,60,73,120,131,146,193,240,270,300,386,416], 0xd0d0d03ff0dffffffffffff02ffffffffff⟩
def E168 : Entry := ⟨9, [304,96,448,128,257,3,262,12,85], [15,30,60,73,120,131,146,193,240,266,296,386,416], 0x1a1a1a05ff1affffffffffff02ffffffffff⟩
def E169 : Entry := ⟨9, [304,96,192,384,257,3,262,12,89], [15,30,60,73,120,131,146,193,240,262,292,386,416], 0xd0d0d03ff0dffffffffffff02ffffffffff⟩
def E170 : Entry := ⟨9, [48,352,192,384,257,3,262,12,90], [15,30,60,73,120,131,146,193,240,261,292,385,416], 0xf0f0f03ff0fffffffffffff01ffffffffff⟩
def E171 : Entry := ⟨9, [304,96,192,384,1,3,6,268,137], [15,30,60,73,120,131,146,193,240,278,308,368], 0x1717170d0217020d02ffffff1717ffffffff⟩
def E172 : Entry := ⟨9, [304,96,448,128,257,3,6,268,149], [15,30,60,73,120,131,146,193,240,266,360], 0x1b1b1b1b191b191b1717ffff1b1917ffffff⟩
def E173 : Entry := ⟨9, [304,96,192,384,257,3,6,268,153], [15,30,60,73,120,131,146,193,240,262,292,352], 0x1717170d0217020d02ffffff1717ffffffff⟩
def E174 : Entry := ⟨9, [304,96,448,128,1,259,6,268,165], [15,30,60,73,120,131,146,193,240,282,344], 0x1b1b1b1b0f1b1b1b1717ffff1b1b17ffffff⟩
def E175 : Entry := ⟨9, [176,352,192,384,1,3,262,13,74], [15,30,60,73,120,146,240,261,308,432], 0x383838383838383838380305383838030305⟩
def E176 : Entry := ⟨9, [176,352,192,384,257,3,262,13,90], [15,30,60,73,120,146,240,261,292,416], 0x30d00000003030d⟩
def R176 := E176.rows
def E177 : Entry := ⟨9, [304,96,448,256,129,3,6,20,13], [15,30,60,120,139,201,232,274,368,386,480], 0x1a1a1a1a191a191a0c0cffff1a190cffffff⟩
def E178 : Entry := ⟨9, [304,96,192,384,129,3,262,28,73], [15,30,60,73,120,131,193,224,278,308,386,416], 0x1717170d0217020d02ffffff1717ffffffff⟩
def E179 : Entry := ⟨9, [304,160,448,64,129,259,12,22,37], [15,30,60,67,112,137,168,193,224,282,338,392,448], 0x17171702ff17ffffffffffff07ffffffffff⟩
def E180 : Entry := ⟨9, [304,160,192,320,129,259,12,22,41], [15,30,60,67,112,137,168,193,224,278,338,448], 0x171717170217021702ffffff1717ffffffff⟩
def E181 : Entry := ⟨9, [176,288,448,64,257,131,268,37,86], [15,30,60,67,112,154,210,265,296,392], 0x204000000020204⟩
def R181 := E181.rows
def E182 : Entry := ⟨9, [432,32,192,320,257,131,268,37,89], [15,30,60,67,112,154,210,262,292,386], 0x22220302000022030302⟩
def R182 := E182.rows
def E183 : Entry := ⟨9, [176,288,192,320,257,131,268,37,90], [15,30,60,67,112,154,210,261,292,384], 0x1818020c00001802020c⟩
def R183 := E183.rows
def E184 : Entry := ⟨9, [304,160,448,64,1,259,140,70,37], [15,30,60,67,112,137,184,282,338,408], 0x2d2d2d2d2d2d2d2d2d2d02042d2d2d020204⟩
def E185 : Entry := ⟨9, [304,160,192,320,1,259,140,70,41], [15,30,60,67,112,137,184,278,338,400], 0x17170205000017020205⟩
def R185 := E185.rows
def E186 : Entry := ⟨9, [272,96,160,448,1,262,10,12,41], [15,30,41,56,69,131,225,240,278,340,402,464], 0x1717170c0117010c01ffffff0c0cffffffff⟩
def E187 : Entry := ⟨9, [272,352,160,192,257,262,10,12,51], [15,30,41,56,69,84,131,146,225,240,268,324,448], 0xe0e0e01ff0effffffffffff03ffffffffff⟩
def E188 : Entry := ⟨9, [272,96,160,448,257,262,10,12,57], [15,30,41,56,69,84,131,146,225,240,262,324,386,448], 0x10101ffffffffffffffffffffffffffffff⟩
def E189 : Entry := ⟨9, [400,352,160,192,257,6,10,13,19], [15,30,41,56,69,84,97,146,240,268,296,324,480], 0x19191905ff19ffffffffffff03ffffffffff⟩
def E190 : Entry := ⟨9, [400,352,160,192,1,262,10,13,35], [15,30,41,56,69,97,146,240,284,340,464], 0x2f2f2f2f0f2f222f1717ffff2f2517ffffff⟩
def E191 : Entry := ⟨9, [400,96,160,192,257,262,10,13,49], [15,30,41,56,69,84,97,146,240,270,324,386,448], 0xc0c0c02ff0cffffffffffff03ffffffffff⟩
def E192 : Entry := ⟨9, [144,352,160,192,257,262,10,13,50], [15,30,41,56,84,97,146,240,269,325,448], 0xf0f0f0f0f0f0d0f0d0dffff0f0f0dffffff⟩
def E193 : Entry := ⟨9, [400,352,160,192,257,262,10,13,51], [15,30,41,56,69,84,97,146,240,268,324,448], 0x2f2f2f2d042f041804ffffff2318ffffffff⟩
def E194 : Entry := ⟨9, [144,96,160,448,257,262,10,13,56], [15,30,41,56,84,97,146,240,263,325,386,448], 0xd0d0d0c010d010c01ffffff0c0cffffffff⟩
def E195 : Entry := ⟨9, [400,352,32,192,1,134,266,41,67], [15,30,41,69,97,112,150,212,284,312,404], 0x232323230f2323231818ffff232318ffffff⟩
def E196 : Entry := ⟨9, [400,96,288,192,1,134,266,41,69], [15,30,41,69,97,112,150,212,282,312,402], 0xc000c000c0cffff00220cffffff⟩
def R196 := E196.rows
def E197 : Entry := ⟨9, [144,96,288,192,257,134,266,41,84], [15,30,56,69,97,112,150,212,267,297,386], 0xf0f0f0f0c0f0c0f0e0cffff0f0c0cffffff⟩
def E198 : Entry := ⟨9, [48,192,320,384,33,17,6,10,12], [15,30,46,73,88,104,133,148,164,259,274,290,449,464,480], 0x101ffffffffffffffffffffffffffffffff⟩
def E199 : Entry := ⟨9, [304,192,320,384,33,17,6,10,13], [15,30,46,73,88,104,133,148,164,193,274,290,464,480], 0x20202ffffffffffffffffffffffffffffff⟩
def E200 : Entry := ⟨9, [48,336,416,192,259,5,10,12,22], [15,28,42,56,69,84,131,162,240,265,296,449,480], 0x10101001ff10ffffffffffff04ffffffffff⟩
def E201 : Entry := ⟨9, [48,336,416,192,3,261,266,12,102], [15,28,42,56,69,84,131,162,193,240,265,280,385,400], 0xf0f0fffffffffffffffffffffffffffffff⟩
def E202 : Entry := ⟨9, [176,336,288,192,3,133,266,41,70], [15,28,42,69,112,134,212,265,312,400], 0x30d00000003030d⟩
def R202 := E202.rows
def E203 : Entry := ⟨9, [72,336,224,385,130,260,7,28,42], [7,14,28,42,49,120,163,224,277,336,385,448], 0xf0100010f01ffffff0f0fffffffff⟩
def R203 := E203.rows
def E204 : Entry := ⟨10, [32,64,128,256,512,1,2,4,8,16], [31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,527,558,589,620,651,682,713,744,775,806,837,868,899,930,961,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E205 : Entry := ⟨10, [544,64,128,256,512,1,2,4,8,17], [31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,558,620,682,744,806,868,930,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E206 : Entry := ⟨10, [544,576,128,256,512,1,2,4,8,19], [31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,620,744,868,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E207 : Entry := ⟨10, [544,576,640,256,512,1,2,4,8,23], [31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,744,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E208 : Entry := ⟨10, [544,576,640,768,512,1,2,4,8,31], [31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E209 : Entry := ⟨10, [288,576,128,256,512,1,2,4,9,18], [31,62,93,124,155,186,217,248,310,372,434,496,589,620,713,744,868,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E210 : Entry := ⟨10, [800,576,128,256,512,1,2,4,9,19], [31,62,93,124,155,186,217,248,310,372,434,496,620,744,868,992], 0x2ffffffffffffffffffffffffffffffffff⟩
def E211 : Entry := ⟨10, [288,576,640,256,512,1,2,4,9,22], [31,62,93,124,155,186,217,248,310,372,434,496,713,744,992], 0x101ffffffffffffffffffffffffffffffff⟩
def E212 : Entry := ⟨10, [800,576,640,256,512,1,2,4,9,23], [31,62,93,124,155,186,217,248,310,372,434,496,744,992], 0x40404ffffffffffffffffffffffffffffff⟩
def E213 : Entry := ⟨10, [288,576,128,768,512,1,2,4,9,26], [31,62,93,124,155,186,217,248,310,372,434,496,581,705,868,992], 0x1ffffffffffffffffffffffffffffffffff⟩
def E214 : Entry := ⟨10, [288,576,640,768,512,1,2,4,9,30], [31,62,93,124,155,186,217,248,310,372,434,496,705,992], 0x10101ffffffffffffffffffffffffffffff⟩
def E215 : Entry := ⟨10, [800,64,128,256,512,1,2,4,521,273], [31,62,93,124,155,186,217,248,310,372,434,496,558,620,682,744], 0x4ffffffffffffffffffffffffffffffffff⟩
def E216 : Entry := ⟨10, [800,576,128,256,512,1,2,4,521,275], [31,62,93,124,155,186,217,248,310,372,434,496,620,744], 0x40404ffffffffffffffffffffffffffffff⟩
def E217 : Entry := ⟨10, [800,576,640,256,512,1,2,4,521,279], [31,62,93,124,155,186,217,248,310,372,434,496,744], 0x4040404ff04ffffffffffff02ffffffffff⟩
def E218 : Entry := ⟨10, [288,320,640,256,512,513,2,4,11,52], [31,62,93,124,155,186,217,248,372,496,651,713,960], 0x4040402ff04ffffffffffff01ffffffffff⟩
def E219 : Entry := ⟨10, [288,832,640,256,512,513,2,4,11,54], [31,62,93,124,155,186,217,248,372,496,713,960], 0x40404040104010401ffffff0404ffffffff⟩
def E220 : Entry := ⟨10, [288,320,128,256,512,513,514,4,11,112], [31,62,93,124,155,186,217,248,372,496,527,651,772,896], 0x40404ffffffffffffffffffffffffffffff⟩
def E221 : Entry := ⟨10, [288,320,640,256,512,513,514,4,11,116], [31,62,93,124,155,186,217,248,372,496,651,896], 0x40404040104010401ffffff0404ffffffff⟩
def E222 : Entry := ⟨10, [800,320,640,256,512,1,2,4,523,277], [31,62,93,124,155,186,217,248,372,496,682,744], 0x40404040204020402ffffff0404ffffffff⟩
def E223 : Entry := ⟨10, [288,320,896,256,512,513,514,4,15,116], [31,62,93,124,155,186,217,248,496,651,896], 0x4040404040404040404ffff040404ffffff⟩
def E224 : Entry := ⟨10, [288,320,384,256,512,513,514,516,15,240], [31,62,93,124,155,186,217,248,496,527,768], 0x4040404040404040404ffff040404ffffff⟩
def E225 : Entry := ⟨10, [544,64,128,768,256,1,2,4,24,9], [31,62,93,124,155,186,217,248,263,325,387,449,566,628,690,752,806,868,930,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E226 : Entry := ⟨10, [544,576,128,768,256,1,2,4,24,11], [31,62,93,124,155,186,217,248,263,294,325,387,418,449,628,752,868,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E227 : Entry := ⟨10, [544,576,640,768,256,1,2,4,24,15], [31,62,93,124,155,186,217,248,263,294,325,356,387,418,449,752,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E228 : Entry := ⟨10, [288,576,640,768,256,1,2,4,25,14], [31,62,93,124,155,186,217,248,294,356,418,721,752,992], 0x10101ffffffffffffffffffffffffffffff⟩
def E229 : Entry := ⟨10, [672,832,128,256,512,1,2,5,10,19], [31,62,93,124,186,248,341,372,496,620,744,868,992], 0x5050505ff05ffffffffffff05ffffffffff⟩
def E230 : Entry := ⟨10, [160,320,640,768,512,1,2,5,10,28], [31,62,93,124,186,248,341,372,496,515,674,833,992], 0x5050501ff05ffffffffffff03ffffffffff⟩
def E231 : Entry := ⟨10, [672,320,128,256,512,1,2,517,10,145], [31,62,93,124,186,248,341,372,496,558,620,868], 0x30303030303030303ffffff0303ffffffff⟩
def E232 : Entry := ⟨10, [672,832,128,256,512,1,2,517,10,147], [31,62,93,124,186,248,341,372,496,620,868], 0x5050505030505050505ffff050505ffffff⟩
def E233 : Entry := ⟨10, [672,320,128,768,512,1,2,517,10,153], [31,62,93,124,186,248,341,372,496,550,868], 0x5050505030505050505ffff050505ffffff⟩
def E234 : Entry := ⟨10, [672,832,128,256,512,1,2,517,522,403], [31,62,93,124,186,248,341,372,496,620], 0x50505050505050505050503050505050503⟩
def E235 : Entry := ⟨10, [416,832,128,256,512,1,2,517,11,146], [31,62,93,124,186,248,372,496,589,620,868], 0xd0d0d0d030d0d0d0d0dffff0d0d0dffffff⟩
def E236 : Entry := ⟨10, [928,320,128,256,512,1,514,517,11,209], [31,62,93,124,186,248,372,496,558,804], 0x191919190519191919190503191919050503⟩
def E237 : Entry := ⟨10, [672,576,384,256,512,1,2,5,12,19], [31,62,93,124,186,248,275,337,434,496,620,744,992], 0x5050502ff05ffffffffffff05ffffffffff⟩
def E238 : Entry := ⟨10, [672,64,384,768,512,1,2,5,12,25], [31,62,93,124,186,248,275,337,434,496,550,612,930,992], 0x50505ffffffffffffffffffffffffffffff⟩
def E239 : Entry := ⟨10, [160,576,384,768,512,1,2,5,12,26], [31,62,93,124,186,248,275,337,434,496,581,612,833,992], 0x20202ffffffffffffffffffffffffffffff⟩
def E240 : Entry := ⟨10, [672,576,384,768,512,1,2,5,12,27], [31,62,93,124,186,248,275,337,434,496,612,992], 0x50505050205020502ffffff0505ffffffff⟩
def E241 : Entry := ⟨10, [672,576,384,256,512,1,2,517,12,147], [31,62,93,124,186,248,275,337,434,496,620,864], 0x50505050205020502ffffff0505ffffffff⟩
def E242 : Entry := ⟨10, [672,64,384,256,512,1,2,5,524,273], [31,62,93,124,186,248,275,337,434,496,558,620,682,744], 0x40404ffffffffffffffffffffffffffffff⟩
def E243 : Entry := ⟨10, [672,576,384,256,512,1,2,5,524,275], [31,62,93,124,186,248,275,337,434,496,620,744], 0x50505050205020502ffffff0505ffffffff⟩
def E244 : Entry := ⟨10, [672,832,384,256,512,1,2,5,14,19], [31,62,93,124,186,248,337,496,620,744,992], 0xf0f0f0f040f0f0f0d0dffff0f0f0dffffff⟩
def E245 : Entry := ⟨10, [672,320,384,256,512,1,514,5,14,81], [31,62,93,124,186,248,337,496,558,682,928], 0xf0f0f0f040f0f0f0d0dffff0f0f0dffffff⟩
def E246 : Entry := ⟨10, [160,320,384,256,512,513,514,5,14,112], [31,62,93,124,186,248,337,496,527,650,769,896], 0xd0d0d0c010d010c01ffffff0c0cffffffff⟩
def E247 : Entry := ⟨10, [672,320,384,256,512,1,2,517,14,145], [31,62,93,124,186,248,337,496,558,620,864], 0xf0f0f0f040f0f0f0f0fffff0f0f0fffffff⟩
def E248 : Entry := ⟨10, [160,832,384,256,512,1,2,517,14,146], [31,62,93,124,186,248,337,496,589,620,833,864], 0x70707070107010701ffffff0707ffffffff⟩
def E249 : Entry := ⟨10, [672,832,384,256,512,1,2,517,14,147], [31,62,93,124,186,248,337,496,620,864], 0xf0f0f0f050f0f0f0f0f03040f0f0f030304⟩
def E250 : Entry := ⟨10, [672,320,384,256,512,1,514,517,14,209], [31,62,93,124,186,248,337,496,558,800], 0xf0f0f0f050f0f0f0f0f03040f0f0f030304⟩
def E251 : Entry := ⟨10, [160,832,384,256,512,513,2,5,526,306], [31,62,93,124,186,248,337,496,589,712], 0xe0e0e0e040e0e0e0d0d03070e0e0d030307⟩
def E252 : Entry := ⟨10, [160,576,128,768,256,1,2,5,24,10], [31,62,93,124,186,248,263,294,418,597,628,752,837,868,992], 0x101ffffffffffffffffffffffffffffffff⟩
def E253 : Entry := ⟨10, [672,576,128,768,256,1,2,5,24,11], [31,62,93,124,186,248,263,294,325,418,628,752,868,992], 0x30303ffffffffffffffffffffffffffffff⟩
def E254 : Entry := ⟨10, [160,576,640,768,256,1,2,5,24,14], [31,62,93,124,186,248,263,294,325,356,418,593,752,833,992], 0x101ffffffffffffffffffffffffffffffff⟩
def E255 : Entry := ⟨10, [672,64,128,768,256,1,2,517,24,137], [31,62,93,124,186,248,263,325,418,480,566,628,806,868], 0x30303ffffffffffffffffffffffffffffff⟩
def E256 : Entry := ⟨10, [672,576,128,768,256,1,2,517,24,139], [31,62,93,124,186,248,263,294,325,418,480,628,868], 0x3030303ff03ffffffffffff02ffffffffff⟩
def E257 : Entry := ⟨10, [672,576,384,768,256,1,2,5,28,11], [31,62,93,124,186,248,259,321,418,628,752,992], 0x191919100219021002ffffff1717ffffffff⟩
def E258 : Entry := ⟨10, [288,320,384,128,512,513,2,524,7,176], [31,62,93,124,147,178,209,376,496,527,589,840], 0x50505050205020502ffffff0505ffffffff⟩
def E259 : Entry := ⟨10, [288,832,384,128,512,513,2,524,7,178], [31,62,93,124,147,178,209,376,496,589,840], 0x5050505050505050505ffff050505ffffff⟩
def E260 : Entry := ⟨10, [288,320,384,128,512,513,514,524,7,240], [31,62,93,124,147,178,209,376,496,527,776], 0x5050505050505050505ffff050505ffffff⟩
def E261 : Entry := ⟨10, [288,320,640,128,256,513,514,12,19,100], [31,62,93,124,178,209,240,364,480,539,659,776,896], 0x5050501ff05ffffffffffff05ffffffffff⟩
def E262 : Entry := ⟨10, [544,576,896,128,256,1,2,12,20,7], [31,62,93,124,147,178,209,267,298,329,387,418,449,632,752,872,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E263 : Entry := ⟨10, [544,64,384,640,256,1,2,12,20,9], [31,62,93,124,147,209,267,298,329,360,387,449,566,628,690,752,930,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E264 : Entry := ⟨10, [544,576,384,640,256,1,2,12,20,11], [31,62,93,124,147,178,209,267,298,329,360,387,418,449,628,752,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E265 : Entry := ⟨10, [32,64,384,640,768,1,2,12,20,24], [31,62,93,124,147,178,209,240,267,298,329,360,519,550,581,612,899,930,961,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E266 : Entry := ⟨10, [544,64,384,640,768,1,2,12,20,25], [31,62,93,124,147,178,209,240,267,298,329,360,387,449,550,612,930,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E267 : Entry := ⟨10, [544,576,384,640,768,1,2,12,20,27], [31,62,93,124,147,178,209,240,267,298,329,360,387,418,449,612,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E268 : Entry := ⟨10, [288,576,384,640,768,1,2,12,21,26], [31,62,93,124,147,178,209,240,298,360,418,581,612,705,992], 0x101ffffffffffffffffffffffffffffffff⟩
def E269 : Entry := ⟨10, [608,192,896,256,512,1,3,6,12,21], [31,62,124,153,248,275,306,401,496,554,744,802,992], 0x5050505ff05ffffffffffff02ffffffffff⟩
def E270 : Entry := ⟨10, [608,192,384,768,512,1,3,6,12,25], [31,62,124,153,248,275,306,401,496,550,612,802,992], 0x5050503ff05ffffffffffff02ffffffffff⟩
def E271 : Entry := ⟨10, [608,192,384,256,512,1,3,518,12,145], [31,62,124,153,248,275,306,401,496,558,620,802,864], 0x5050503ff05ffffffffffff02ffffffffff⟩
def E272 : Entry := ⟨10, [608,192,384,256,512,1,3,6,524,273], [31,62,124,153,248,275,306,401,496,558,620,744], 0x50505050205020502ffffff0505ffffffff⟩
def E273 : Entry := ⟨10, [608,192,896,256,512,1,3,6,524,277], [31,62,124,153,248,275,306,401,496,554,744], 0x5050505050505050505ffff050505ffffff⟩
def E274 : Entry := ⟨10, [608,192,640,768,256,1,3,6,24,13], [31,62,124,153,248,263,294,356,385,562,752,802,992], 0x6060604ff06ffffffffffff02ffffffffff⟩
def E275 : Entry := ⟨10, [608,192,128,768,256,1,515,6,24,73], [31,62,124,153,248,263,356,385,480,566,688,806,928], 0x6060602ff06ffffffffffff06ffffffffff⟩
def E276 : Entry := ⟨10, [608,192,128,768,256,1,3,518,24,137], [31,62,124,153,248,263,385,480,566,628,806,868], 0x171717100217021002ffffff1717ffffffff⟩
def E277 : Entry := ⟨10, [608,320,640,128,256,1,515,268,146,69], [31,62,124,147,240,269,364,570,690,808], 0x191919191919191919190204191919020204⟩
def E278 : Entry := ⟨10, [608,64,896,128,256,1,515,268,148,69], [31,62,124,147,240,267,360,570,690,810], 0x181818181818181818181802181818181002⟩
def E279 : Entry := ⟨10, [800,704,320,384,512,1,6,10,13,19], [31,62,89,120,149,180,209,306,496,556,616,676,992], 0x5050505ff05ffffffffffff03ffffffffff⟩
def E280 : Entry := ⟨10, [800,192,320,384,512,1,518,10,13,81], [31,62,89,120,149,180,209,306,496,558,676,802,928], 0x5050502ff05ffffffffffff03ffffffffff⟩
def E281 : Entry := ⟨10, [288,192,320,384,512,513,518,10,13,112], [31,62,89,120,149,180,209,306,496,527,645,770,896], 0x5050502ff05ffffffffffff01ffffffffff⟩
def E282 : Entry := ⟨10, [288,192,576,640,256,1,6,10,17,12], [31,62,89,120,149,180,302,360,420,531,562,721,752,802,992], 0x101ffffffffffffffffffffffffffffffff⟩
def E283 : Entry := ⟨10, [800,192,576,640,256,1,6,10,17,13], [31,62,89,120,149,180,209,302,360,420,562,752,802,992], 0x20202ffffffffffffffffffffffffffffff⟩
def E284 : Entry := ⟨10, [288,192,576,640,768,1,6,10,17,28], [31,62,89,120,149,180,209,240,302,360,420,515,705,802,992], 0x101ffffffffffffffffffffffffffffffff⟩
def E285 : Entry := ⟨10, [800,704,64,128,256,1,6,10,529,259], [31,62,89,149,209,302,360,420,480,572,632,692,752], 0x5050505ff05ffffffffffff05ffffffffff⟩
def E286 : Entry := ⟨10, [800,192,576,128,256,1,6,10,529,261], [31,62,89,149,180,209,302,360,420,480,570,632,752], 0x5050505ff05ffffffffffff03ffffffffff⟩
def E287 : Entry := ⟨10, [800,192,576,640,256,1,6,10,529,269], [31,62,89,120,149,180,209,302,360,420,480,562,752], 0x5050505ff05ffffffffffff03ffffffffff⟩
def E288 : Entry := ⟨10, [544,192,320,640,256,1,6,10,20,9], [31,62,89,120,149,209,267,298,329,360,449,566,692,752,802,992], 0x1ffffffffffffffffffffffffffffffffff⟩
def E289 : Entry := ⟨10, [544,192,832,640,256,1,6,10,20,13], [31,62,89,120,149,180,209,267,298,329,360,449,562,752,802,992], 0x1ffffffffffffffffffffffffffffffffff⟩
def E290 : Entry := ⟨10, [32,192,320,640,768,1,6,10,20,24], [31,62,89,120,149,180,209,240,267,298,329,360,519,550,645,676,771,802,961,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E291 : Entry := ⟨10, [544,192,320,640,768,1,6,10,20,25], [31,62,89,120,149,180,209,240,267,298,329,360,449,550,676,802,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E292 : Entry := ⟨10, [800,576,64,384,128,1,262,536,73,131], [31,62,89,135,193,224,310,422,572,632,820], 0x17171717101717171717ffff171717ffffff⟩
def E293 : Entry := ⟨10, [288,576,64,384,128,513,262,536,73,162], [31,62,120,135,193,224,310,422,541,601,788], 0x101010100c100c100e0cffff100c0cffffff⟩
def E294 : Entry := ⟨10, [96,672,832,384,512,3,5,10,12,22], [31,60,90,120,149,180,275,338,401,496,521,616,897,992], 0x50505ffffffffffffffffffffffffffffff⟩
def E295 : Entry := ⟨10, [96,160,320,640,768,3,5,10,20,24], [31,60,90,120,149,180,240,267,330,360,519,645,676,771,834,897,992], 0xffffffffffffffffffffffffffffffffffff⟩
def E296 : Entry := ⟨10, [608,160,320,640,768,3,5,10,20,25], [31,60,90,120,149,180,240,267,330,360,385,518,676,834,992], 0x202ffffffffffffffffffffffffffffffff⟩
def E297 : Entry := ⟨10, [272,288,320,640,513,514,4,8,7,56], [15,30,45,60,75,90,105,150,165,180,210,225,376,496,647,707,960], 0xffffffffffffffffffffffffffffffffffff⟩
def E298 : Entry := ⟨10, [272,288,320,128,513,514,516,8,7,112], [30,45,60,75,90,105,150,165,180,195,210,225,376,496,527,647,776,896], 0xffffffffffffffffffffffffffffffffffff⟩
def E299 : Entry := ⟨10, [272,288,320,640,513,514,516,8,7,120], [15,30,45,60,75,90,105,150,165,180,195,210,225,376,496,647,896], 0xffffffffffffffffffffffffffffffffffff⟩
def E300 : Entry := ⟨10, [272,288,320,384,513,514,516,520,15,240], [30,45,60,75,90,105,120,135,150,165,180,195,210,225,496,527,768], 0xffffffffffffffffffffffffffffffffffff⟩
def E301 : Entry := ⟨10, [144,288,320,384,513,514,516,9,14,112], [30,45,60,75,90,105,120,150,180,210,353,496,527,646,769,896], 0x1ffffffffffffffffffffffffffffffffff⟩
def E302 : Entry := ⟨10, [144,288,320,384,1,514,516,521,14,224], [45,60,75,90,105,120,150,180,210,353,496,527,542,769,784], 0x101ffffffffffffffffffffffffffffffff⟩
def E303 : Entry := ⟨10, [336,288,192,384,513,514,5,524,11,176], [30,45,60,90,120,131,161,210,308,496,527,586,772,832], 0x181818ffffffffffffffffffffffffffffff⟩
def S0 : List ℕ := [5,6,89,90,105,106,153,154,169,170]
def P0 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,40,42,48,51,60,63,64,65,68,69,128,130,136,138,192,195,204,207,256,257,272,273,320,321,340,341,512,514,544,546,640,642,680,682,768,771,816,819,960,963,1020,1023]
def S1 : List ℕ := [5,22,25,26,102,105,106,166,169,170]
def P1 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,18,19,32,33,36,37,64,72,80,90,96,108,113,127,128,129,130,131,144,145,146,147,256,257,260,261,288,289,292,293,512,520,576,584,640,650,720,730,768,780,864,876,897,911,1009,1023]
def S2 : List ℕ := [5,22,38,73,90,106,153,154,169,170]
def P2 : List ℕ := [0,1,2,3,4,5,6,7,8,9,16,18,24,27,32,36,40,45,48,54,56,63,64,65,72,73,128,130,144,146,192,195,216,219,256,257,264,265,320,321,328,329,512,516,544,548,640,646,688,694,768,773,808,813,960,967,1016,1023]
def S3 : List ℕ := [5,22,38,89,90,105,106,153,154,169,170]
def P3 : List ℕ := [0,1,2,3,4,5,6,7,8,9,16,18,24,27,32,33,40,41,64,68,80,86,96,101,120,127,128,129,136,137,256,258,272,274,384,387,408,411,512,513,544,545,640,641,680,681,1024,1028,1088,1092,1280,1286,1360,1366,1536,1541,1632,1637,1920,1927,2040,2047]
def S4 : List ℕ := [5,22,89,90,102,105,106,153,154,166,169,170]
def P4 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,18,19,32,33,36,37,64,72,80,90,96,108,113,127,128,129,132,133,256,258,264,266,384,387,396,399,512,513,514,515,528,529,530,531,1024,1025,1056,1057,1152,1153,1188,1189,2048,2112,2304,2376,2560,2640,2818,2906,3072,3168,3456,3564,3585,3697,3971,4095]
def S5 : List ℕ := [5,86,89,90,102,105,106,150,153,154,166,169,170]
def P5 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,18,19,32,33,36,37,64,72,80,90,96,108,113,127,128,129,130,131,256,257,260,261,512,520,640,650,768,780,897,911,1024,1025,1040,1041,1152,1153,1170,1171,2048,2049,2080,2081,2304,2305,2340,2341,4096,4160,4608,4680,5120,5200,5760,5850,6144,6240,6912,7020,7169,7281,8065,8191]
def S6 : List ℕ := [21,22,25,26,97,98,165,166,169,170]
def P6 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,40,42,48,51,60,63,64,65,80,81,128,130,160,162,192,195,240,243,256,260,272,276,320,325,336,341,512,520,544,552,640,650,672,682,768,780,816,828,960,975,1008,1023]
def S7 : List ℕ := [21,22,25,26,97,102,106,161,166,170]
def P7 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,48,51,64,72,80,92,96,106,112,127,128,129,132,133,144,145,148,149,256,258,288,290,384,387,432,435,512,520,576,584,640,652,720,732,768,778,864,874,896,911,1008,1023]
def S8 : List ℕ := [21,22,25,26,97,102,106,165,166,169,170]
def P8 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,48,51,64,72,80,92,96,106,112,127,128,129,144,145,256,258,288,290,384,387,432,435,512,516,528,532,640,645,656,661,1024,1032,1088,1096,1280,1290,1376,1386,1536,1548,1616,1628,1920,1935,2032,2047]
def S9 : List ℕ := [21,22,25,26,101,102,105,106,165,166,169,170]
def P9 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255,256,257,272,273,512,514,544,546,768,771,816,819,1024,1028,1088,1092,1280,1285,1360,1365,2048,2056,2176,2184,2560,2570,2720,2730,3072,3084,3264,3276,3840,3855,4080,4095]
def S10 : List ℕ := [21,22,73,90,101,102,106,137,154,165,166,170]
def P10 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,48,51,64,68,72,76,96,106,116,127,128,129,132,133,256,258,264,266,384,387,396,399,512,513,528,529,640,641,660,661,1024,1026,1056,1058,1536,1539,1584,1587,2048,2112,2176,2244,2304,2376,2432,2508,3072,3168,3330,3434,3712,3828,3971,4095]
def S11 : List ℕ := [21,22,88,101,102,105,106,152,165,166,169,170]
def P11 : List ℕ := [0,1,2,3,4,5,6,7,8,9,16,18,24,27,32,36,40,45,64,68,80,86,96,100,120,127,128,129,130,131,132,133,134,135,256,257,264,265,512,514,528,530,768,771,792,795,1024,1056,1152,1188,1280,1320,1409,1453,2048,2112,2176,2244,2560,2640,2690,2774,3072,3168,3200,3300,3840,3960,3971,4095]
def S12 : List ℕ := [21,22,88,101,102,105,106,153,154,165,166,169,170]
def P12 : List ℕ := [0,1,2,3,4,5,6,7,8,9,16,18,24,27,32,36,40,45,64,68,80,86,96,100,120,127,128,129,132,133,256,258,260,262,384,387,388,391,512,513,520,521,1024,1026,1040,1042,1536,1539,1560,1563,2048,2080,2176,2212,2560,2600,2689,2733,4096,4160,4352,4420,5120,5200,5378,5462,6144,6240,6528,6628,7680,7800,8067,8191]
def S13 : List ℕ := [21,22,89,90,101,102,104,153,154,165,166,168]
def P13 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,72,76,80,85,96,106,112,127,128,129,132,133,256,258,264,266,384,387,396,399,512,513,528,529,1024,1026,1056,1058,1536,1539,1584,1587,2048,2112,2176,2244,2304,2376,2432,2508,2560,2640,2689,2773,3072,3168,3330,3434,3584,3696,3971,4095]
def S14 : List ℕ := [21,22,89,90,101,102,104,153,154,165,166,169,170]
def P14 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,72,76,80,85,96,106,112,127,128,129,132,133,256,258,264,266,384,387,396,399,512,513,528,529,1024,1026,1056,1058,1536,1539,1584,1587,2048,2112,2176,2244,2560,2640,2689,2773,4096,4160,4352,4424,5120,5216,5378,5482,6144,6208,6528,6604,7680,7792,8067,8191]
def S15 : List ℕ := [21,22,89,90,101,102,105,106,153,154,165,166,169,170]
def P15 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255,256,257,260,261,512,514,520,522,768,771,780,783,1024,1025,1040,1041,2048,2050,2080,2082,3072,3075,3120,3123,4096,4160,4352,4420,5120,5200,5377,5461,8192,8320,8704,8840,10240,10400,10754,10922,12288,12480,13056,13260,15360,15600,16131,16383]
def S16 : List ℕ := [21,86,89,90,101,102,105,106,150,153,154,165,166,169,170]
def P16 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255,256,257,258,259,512,513,516,517,1024,1032,1280,1290,1536,1548,1793,1807,2048,2049,2064,2065,4096,4128,4352,4386,6144,6192,6401,6451,8192,8256,8704,8772,10240,10320,10753,10837,16384,16512,17408,17544,20480,20640,21760,21930,24576,24768,26112,26316,30720,30960,32513,32767]
def S17 : List ℕ := [85,86,89,90,101,102,105,106,149,150,153,154,165,166,169,170]
def P17 : List ℕ := [0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255,256,257,512,514,768,771,1024,1028,1280,1285,2048,2056,2560,2570,3072,3084,3840,3855,4096,4112,4352,4369,8192,8224,8704,8738,12288,12336,13056,13107,16384,16448,17408,17476,20480,20560,21760,21845,32768,32896,34816,34952,40960,41120,43520,43690,49152,49344,52224,52428,61440,61680,65280,65535]
def shapes : List ShapeData := [⟨S0,P0⟩,⟨S1,P1⟩,⟨S2,P2⟩,⟨S3,P3⟩,⟨S4,P4⟩,⟨S5,P5⟩,⟨S6,P6⟩,⟨S7,P7⟩,⟨S8,P8⟩,⟨S9,P9⟩,⟨S10,P10⟩,⟨S11,P11⟩,⟨S12,P12⟩,⟨S13,P13⟩,⟨S14,P14⟩,⟨S15,P15⟩,⟨S16,P16⟩,⟨S17,P17⟩]
def shapeAt (s : ℕ) : ShapeData := (shapes[s]?).getD default
def harder : List Entry := [E10,E13,E21,E123,E136,E139,E141,E176,E181,E182,E183,E185,E196,E202,E203]
def batch0 : List Entry := [E0,E1,E2,E3,E4,E5,E6,E7]
def batch1 : List Entry := [E8,E9,E10,E11,E12,E13,E14,E15]
def batch2 : List Entry := [E16,E17,E18,E19,E20,E21,E22,E23]
def batch3 : List Entry := [E24,E25,E26,E27,E28,E29,E30,E31]
def batch4 : List Entry := [E32,E33,E34,E35,E36,E37,E38,E39]
def batch5 : List Entry := [E40,E41,E42,E43,E44,E45,E46,E47]
def batch6 : List Entry := [E48,E49,E50,E51,E52,E53,E54,E55]
def batch7 : List Entry := [E56,E57,E58,E59,E60,E61,E62,E63]
def batch8 : List Entry := [E64,E65,E66,E67,E68,E69,E70,E71]
def batch9 : List Entry := [E72,E73,E74,E75,E76,E77,E78,E79]
def batch10 : List Entry := [E80,E81,E82,E83,E84,E85,E86,E87]
def batch11 : List Entry := [E88,E89,E90,E91,E92,E93,E94,E95]
def batch12 : List Entry := [E96,E97,E98,E99,E100,E101,E102,E103]
def batch13 : List Entry := [E104,E105,E106,E107,E108,E109,E110,E111]
def batch14 : List Entry := [E112,E113,E114,E115,E116,E117,E118,E119]
def batch15 : List Entry := [E120,E121,E122,E123,E124,E125,E126,E127]
def batch16 : List Entry := [E128,E129,E130,E131,E132,E133,E134,E135]
def batch17 : List Entry := [E136,E137,E138,E139,E140,E141,E142,E143]
def batch18 : List Entry := [E144,E145,E146,E147,E148,E149,E150,E151]
def batch19 : List Entry := [E152,E153,E154,E155,E156,E157,E158,E159]
def batch20 : List Entry := [E160,E161,E162,E163,E164,E165,E166,E167]
def batch21 : List Entry := [E168,E169,E170,E171,E172,E173,E174,E175]
def batch22 : List Entry := [E176,E177,E178,E179,E180,E181,E182,E183]
def batch23 : List Entry := [E184,E185,E186,E187,E188,E189,E190,E191]
def batch24 : List Entry := [E192,E193,E194,E195,E196,E197,E198,E199]
def batch25 : List Entry := [E200,E201,E202,E203,E204,E205,E206,E207]
def batch26 : List Entry := [E208,E209,E210,E211,E212,E213,E214,E215]
def batch27 : List Entry := [E216,E217,E218,E219,E220,E221,E222,E223]
def batch28 : List Entry := [E224,E225,E226,E227,E228,E229,E230,E231]
def batch29 : List Entry := [E232,E233,E234,E235,E236,E237,E238,E239]
def batch30 : List Entry := [E240,E241,E242,E243,E244,E245,E246,E247]
def batch31 : List Entry := [E248,E249,E250,E251,E252,E253,E254,E255]
def batch32 : List Entry := [E256,E257,E258,E259,E260,E261,E262,E263]
def batch33 : List Entry := [E264,E265,E266,E267,E268,E269,E270,E271]
def batch34 : List Entry := [E272,E273,E274,E275,E276,E277,E278,E279]
def batch35 : List Entry := [E280,E281,E282,E283,E284,E285,E286,E287]
def batch36 : List Entry := [E288,E289,E290,E291,E292,E293,E294,E295]
def batch37 : List Entry := [E296,E297,E298,E299,E300,E301,E302,E303]
def batches : List (List Entry) := [batch0,batch1,batch2,batch3,batch4,batch5,batch6,batch7,batch8,batch9,batch10,batch11,batch12,batch13,batch14,batch15,batch16,batch17,batch18,batch19,batch20,batch21,batch22,batch23,batch24,batch25,batch26,batch27,batch28,batch29,batch30,batch31,batch32,batch33,batch34,batch35,batch36,batch37]
def entries := batches.flatten

def noHard (g : Entry) : Bool :=
  (List.range 18).all (fun i => ((g.moves >>> (8*i)) &&& 255) != 0)

def ledgerOK (g : Entry) : Bool :=
  listedOK g && ((List.range 18).all (fun s => certified g (shapeAt s) s)) &&
    (noHard g || harder.contains g)

def LongClear (g : Entry) : Prop := ∀ s : Fin 18, HardSlots g s.val → ¬ Embeds g.rows (shapeAt s.val).paths g.n

end MoonPrize.Trace

namespace Coverage

def gd : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: l, i + 1 => gd l i

theorem gd_mem : ∀ (l : List ℕ) (i : ℕ), i < l.length → gd l i ∈ l
  | [], i, h => by simp at h
  | x :: l, 0, _ => by simp [gd]
  | x :: l, i + 1, h => by
      have h' : i < l.length := by simpa using h
      have := gd_mem l i h'
      simp [gd, this]

def idx (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | y :: l => if y = x then 0 else idx x l + 1

theorem idx_lt (x : ℕ) : ∀ l : List ℕ, x ∈ l → idx x l < l.length
  | [], h => by simp at h
  | y :: l, h => by
      unfold idx
      split_ifs with e
      · simp
      · have hx : x ∈ l := by
          rcases List.mem_cons.mp h with h1 | h1
          · exact absurd h1.symm e
          · exact h1
        have := idx_lt x l hx
        simp only [List.length_cons]
        omega

theorem gd_idx (x : ℕ) : ∀ l : List ℕ, x ∈ l → gd l (idx x l) = x
  | [], h => by simp at h
  | y :: l, h => by
      unfold idx
      split_ifs with e
      · exact e
      · have hx : x ∈ l := by
          rcases List.mem_cons.mp h with h1 | h1
          · exact absurd h1.symm e
          · exact h1
        exact gd_idx x l hx

theorem mem_gd (l : List ℕ) (x : ℕ) (h : x ∈ l) : ∃ i, i < l.length ∧ gd l i = x :=
  ⟨idx x l, idx_lt x l h, gd_idx x l h⟩

theorem gd_inj : ∀ (l : List ℕ), l.Nodup → ∀ i j, i < l.length → j < l.length →
    gd l i = gd l j → i = j
  | [], _, i, j, hi, _, _ => by simp at hi
  | x :: l, hn, i, j, hi, hj, h => by
      rw [List.nodup_cons] at hn
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j =>
          exfalso
          have hj' : j < l.length := by simpa using hj
          have hm := gd_mem l j hj'
          have h' : x = gd l j := h
          rw [← h'] at hm
          exact hn.1 hm
      | succ i =>
        cases j with
        | zero =>
          exfalso
          have hi' : i < l.length := by simpa using hi
          have hm := gd_mem l i hi'
          have h' : gd l i = x := h
          rw [h'] at hm
          exact hn.1 hm
        | succ j =>
          have hi' : i < l.length := by simpa using hi
          have hj' : j < l.length := by simpa using hj
          have h' : gd l i = gd l j := h
          rw [gd_inj l hn.2 i j hi' hj' h']

theorem gd_map (g : ℕ → ℕ) (hg : g 0 = 0) : ∀ (l : List ℕ) (i : ℕ), gd (l.map g) i = g (gd l i)
  | [], i => by simp [gd, hg]
  | x :: l, 0 => rfl
  | x :: l, i + 1 => gd_map g hg l i

def nth {α : Type} : List α → ℕ → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: l, i + 1 => nth l i

theorem nth_mem {α : Type} : ∀ (l : List α) (i : ℕ) (x : α), nth l i = some x → x ∈ l
  | [], _, _, h => by simp [nth] at h
  | y :: l, 0, x, h => by
      have h' : some y = some x := h
      rw [Option.some.injEq] at h'
      rw [h']
      exact List.mem_cons_self
  | y :: l, i + 1, x, h => List.mem_cons_of_mem _ (nth_mem l i x h)

def nodupB : List ℕ → Bool
  | [] => true
  | x :: l => decide (x ∉ l) && nodupB l

theorem nodupB_sound : ∀ l : List ℕ, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
      simp only [nodupB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact List.nodup_cons.mpr ⟨h.1, nodupB_sound l h.2⟩

def ins (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: l => if x < y then x :: y :: l else y :: ins x l

def isort : List ℕ → List ℕ
  | [] => []
  | x :: l => ins x (isort l)

theorem mem_ins (a x : ℕ) : ∀ l : List ℕ, a ∈ ins x l ↔ a = x ∨ a ∈ l
  | [] => by simp [ins]
  | y :: l => by
      unfold ins
      split_ifs
      · simp
      · rw [List.mem_cons, mem_ins a x l, List.mem_cons]
        tauto

theorem length_ins (x : ℕ) : ∀ l : List ℕ, (ins x l).length = l.length + 1
  | [] => rfl
  | y :: l => by
      unfold ins
      split_ifs
      · simp
      · simp [length_ins x l]

theorem sorted_ins (x : ℕ) : ∀ l : List ℕ, l.Pairwise (· < ·) → x ∉ l →
    (ins x l).Pairwise (· < ·)
  | [], _, _ => by simp [ins]
  | y :: l, hp, hx => by
      rw [List.pairwise_cons] at hp
      have hxy : x ≠ y := fun e => hx (by simp [e])
      have hxl : x ∉ l := fun e => hx (by simp [e])
      unfold ins
      split_ifs with h
      · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr hp⟩
        intro a ha
        rcases List.mem_cons.mp ha with h1 | h1
        · rw [h1]; exact h
        · exact lt_trans h (hp.1 a h1)
      · refine List.pairwise_cons.mpr ⟨?_, sorted_ins x l hp.2 hxl⟩
        intro a ha
        rcases (mem_ins a x l).mp ha with h1 | h1
        · rw [h1]; omega
        · exact hp.1 a h1

theorem isort_spec : ∀ l : List ℕ, l.Nodup →
    (isort l).Pairwise (· < ·) ∧ (isort l).length = l.length ∧ ∀ a, a ∈ isort l ↔ a ∈ l
  | [], _ => by simp [isort]
  | x :: l, hn => by
      rw [List.nodup_cons] at hn
      obtain ⟨h1, h2, h3⟩ := isort_spec l hn.2
      refine ⟨sorted_ins x _ h1 (fun h => hn.1 ((h3 x).mp h)), ?_, ?_⟩
      · show (ins x (isort l)).length = (x :: l).length
        rw [length_ins, h2]; rfl
      · intro a
        show a ∈ ins x (isort l) ↔ a ∈ x :: l
        rw [mem_ins, h3, List.mem_cons]

theorem sublist_range' : ∀ (n lo : ℕ) (l : List ℕ), l.Pairwise (· < ·) →
    (∀ x ∈ l, lo ≤ x ∧ x < lo + n) → l.Sublist (List.range' lo n)
  | 0, lo, l, _, hb => by
      cases l with
      | nil => exact List.nil_sublist _
      | cons x xs =>
        have := hb x List.mem_cons_self
        omega
  | n + 1, lo, l, hp, hb => by
      show l.Sublist (lo :: List.range' (lo + 1) n)
      cases l with
      | nil => exact List.nil_sublist _
      | cons x xs =>
        rw [List.pairwise_cons] at hp
        have hx := hb x List.mem_cons_self
        by_cases hxl : x = lo
        · subst hxl
          apply List.cons_sublist_cons.mpr
          apply sublist_range' n (x + 1) xs hp.2
          intro y hy
          have h1 := hp.1 y hy
          have h2 := hb y (List.mem_cons_of_mem _ hy)
          omega
        · apply List.Sublist.cons
          apply sublist_range' n (lo + 1) (x :: xs) (List.pairwise_cons.mpr hp)
          intro y hy
          have h1 := hb y hy
          rcases List.mem_cons.mp hy with h2 | h2
          · omega
          · have := hp.1 y h2
            omega

def Indep (A : ℕ → ℕ → Bool) (S : Finset ℕ) : Prop := ∀ u ∈ S, ∀ v ∈ S, A u v = false

def SQF (n : ℕ) (A : ℕ → ℕ → Bool) : Prop :=
  ∀ u v a b, u < n → v < n → a < n → b < n → u ≠ v → a ≠ b →
    A u a = true → A v a = true → A u b = true → A v b = true → False

def Valid (n k : ℕ) (A : ℕ → ℕ → Bool) : Prop :=
  SQF n A ∧ (∀ S : Finset ℕ, S ⊆ Finset.range n → Indep A S → S.card ≤ k) ∧
    ∀ v < n, ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ Indep A S ∧ v ∉ S ∧ S.card = k

namespace Valid
theorem sqf {n k A} (h : Valid n k A) : SQF n A := h.1
theorem hard {n k A} (h : Valid n k A) : ∀ S : Finset ℕ, S ⊆ Finset.range n → Indep A S → S.card ≤ k := h.2.1
theorem crit {n k A} (h : Valid n k A) : ∀ v < n, ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ Indep A S ∧ v ∉ S ∧ S.card = k := h.2.2
end Valid

def Iso (n : ℕ) (A B : ℕ → ℕ → Bool) : Prop :=
  ∃ σ : ℕ → ℕ, (∀ u < n, σ u < n) ∧ (∀ u < n, ∀ v < n, σ u = σ v → u = v) ∧
    ∀ u < n, ∀ v < n, A u v = B (σ u) (σ v)

theorem Iso.trans {n : ℕ} {A B C : ℕ → ℕ → Bool} (h1 : Iso n A B) (h2 : Iso n B C) :
    Iso n A C := by
  obtain ⟨σ, s1, s2, s3⟩ := h1
  obtain ⟨τ, t1, t2, t3⟩ := h2
  refine ⟨fun u => τ (σ u), fun u hu => t1 _ (s1 u hu), fun u hu v hv h => ?_, fun u hu v hv => ?_⟩
  · exact s2 u hu v hv (t2 _ (s1 u hu) _ (s1 v hv) h)
  · rw [s3 u hu v hv, t3 _ (s1 u hu) _ (s1 v hv)]

theorem surj_of_inj {n : ℕ} {σ : ℕ → ℕ} (s1 : ∀ u < n, σ u < n)
    (s2 : ∀ u < n, ∀ v < n, σ u = σ v → u = v) : ∀ v < n, ∃ u, u < n ∧ σ u = v := by
  classical
  have himg : (Finset.range n).image σ = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (s1 u (Finset.mem_range.mp hu))
    · rw [Finset.card_image_of_injOn]
      intro a ha b hb hab
      exact s2 a (Finset.mem_range.mp (Finset.mem_coe.mp ha)) b
        (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab
  intro v hv
  have hm : v ∈ (Finset.range n).image σ := by
    rw [himg]; exact Finset.mem_range.mpr hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  exact ⟨u, Finset.mem_range.mp hu, rfl⟩

theorem Iso.symm {n : ℕ} {A B : ℕ → ℕ → Bool} (h : Iso n A B) : Iso n B A := by
  classical
  obtain ⟨σ, s1, s2, s3⟩ := h
  have sur := surj_of_inj s1 s2
  choose! τ ht using sur
  refine ⟨τ, fun v hv => (ht v hv).1, fun u hu v hv h => ?_, fun u hu v hv => ?_⟩
  · have h' := congrArg σ h
    rw [(ht u hu).2, (ht v hv).2] at h'
    exact h'
  · rw [s3 _ (ht u hu).1 _ (ht v hv).1, (ht u hu).2, (ht v hv).2]

theorem Valid.of_iso {n k : ℕ} {A B : ℕ → ℕ → Bool} (h : Iso n A B) (hv : Valid n k B) :
    Valid n k A := by
  classical
  obtain ⟨σ, s1, s2, s3⟩ := h
  have injOn : ∀ S : Finset ℕ, S ⊆ Finset.range n → Set.InjOn σ (S : Set ℕ) := by
    intro S hS a ha b hb hab
    exact s2 a (Finset.mem_range.mp (hS (Finset.mem_coe.mp ha))) b
      (Finset.mem_range.mp (hS (Finset.mem_coe.mp hb))) hab
  refine ⟨?_, ?_, ?_⟩
  · intro u v a b hu hv' ha hb huv hab h1 h2 h3 h4
    rw [s3 u hu a ha] at h1
    rw [s3 v hv' a ha] at h2
    rw [s3 u hu b hb] at h3
    rw [s3 v hv' b hb] at h4
    exact hv.sqf (σ u) (σ v) (σ a) (σ b) (s1 u hu) (s1 v hv') (s1 a ha) (s1 b hb)
      (fun e => huv (s2 u hu v hv' e)) (fun e => hab (s2 a ha b hb e)) h1 h2 h3 h4
  · intro S hS hI
    have hsub : S.image σ ⊆ Finset.range n := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (s1 u (Finset.mem_range.mp (hS hu)))
    have hind : Indep B (S.image σ) := by
      intro x hx y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      rw [← s3 u (Finset.mem_range.mp (hS hu)) w (Finset.mem_range.mp (hS hw))]
      exact hI u hu w hw
    have h := hv.hard (S.image σ) hsub hind
    rwa [Finset.card_image_of_injOn (injOn S hS)] at h
  · intro v hvn
    obtain ⟨S, hS, hI, hvS, hc⟩ := hv.crit (σ v) (s1 v hvn)
    refine ⟨(Finset.range n).filter (fun u => σ u ∈ S), Finset.filter_subset _ _, ?_, ?_, ?_⟩
    · intro u hu w hw
      rw [Finset.mem_filter] at hu hw
      rw [s3 u (Finset.mem_range.mp hu.1) w (Finset.mem_range.mp hw.1)]
      exact hI _ hu.2 _ hw.2
    · intro h
      exact hvS (Finset.mem_filter.mp h).2
    · have himg : ((Finset.range n).filter (fun u => σ u ∈ S)).image σ = S := by
        ext x
        constructor
        · intro hx
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_filter.mp hu).2
        · intro hx
          obtain ⟨u, hu, rfl⟩ := surj_of_inj s1 s2 x (Finset.mem_range.mp (hS hx))
          exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, hx⟩, rfl⟩
      have hcard := Finset.card_image_of_injOn
        (injOn ((Finset.range n).filter (fun u => σ u ∈ S)) (Finset.filter_subset _ _))
      rw [himg] at hcard
      exact hcard.symm.trans hc

def mk5 (b0 b1 b2 b3 b4 : Bool) : ℕ :=
  b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat

def sel5 (b0 b1 b2 b3 b4 : Bool) (v : ℕ) : Bool :=
  match v with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | _ => false

theorem mk5_testBit : ∀ b0 b1 b2 b3 b4 : Bool, ∀ v, v < 5 →
    (mk5 b0 b1 b2 b3 b4).testBit v = sel5 b0 b1 b2 b3 b4 v := by decide +kernel

theorem mk5_lt : ∀ b0 b1 b2 b3 b4 : Bool, mk5 b0 b1 b2 b3 b4 < 32 := by decide +kernel

def multi (x : ℕ) : Bool := (x &&& (x - 1)) != 0

theorem multi_spec : ∀ x, x < 32 → multi x = true →
    ∃ a, a < 5 ∧ ∃ b, b < 5 ∧ a ≠ b ∧ x.testBit a = true ∧ x.testBit b = true := by
  decide +kernel

theorem and_zero : ∀ q, q < 32 → ∀ t, t < 32 →
    (∀ j, j < 5 → ¬(q.testBit j = true ∧ t.testBit j = true)) → q &&& t = 0 := by
  decide +kernel

theorem bits_ext : ∀ q1, q1 < 32 → ∀ q2, q2 < 32 →
    (∀ w, w < 5 → q1.testBit w = q2.testBit w) → q1 = q2 := by
  decide +kernel

def pidx (u v : ℕ) : ℕ := u * (9 - u) / 2 + v - u - 1

def fadj (f u v : ℕ) : Bool :=
  if u < v then f.testBit (pidx u v) else if v < u then f.testBit (pidx v u) else false

theorem fadj_self (f u : ℕ) : fadj f u u = false := by simp [fadj]

theorem fadj_comm (f u v : ℕ) : fadj f u v = fadj f v u := by
  unfold fadj
  by_cases h1 : u < v
  · have h2 : ¬ v < u := by omega
    simp [h1, h2]
  · by_cases h2 : v < u
    · simp [h1, h2]
    · simp [h1, h2]

def mk10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : ℕ :=
  b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat + 32 * b5.toNat +
    64 * b6.toNat + 128 * b7.toNat + 256 * b8.toNat + 512 * b9.toNat

theorem mk10_fadj : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 0 1 = b0 ∧
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 0 2 = b1 ∧
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 0 3 = b2 ∧
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 0 4 = b3 ∧
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 1 2 = b4 ∧
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 1 3 = b5 ∧
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 1 4 = b6 ∧
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 2 3 = b7 ∧
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 2 4 = b8 ∧
    fadj (mk10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 3 4 = b9 := by decide +kernel

def pa (c v : ℕ) : ℕ := (c >>> (3 * v)) &&& 7

def pullF (c f : ℕ) : ℕ :=
  mk10 (fadj f (pa c 0) (pa c 1)) (fadj f (pa c 0) (pa c 2)) (fadj f (pa c 0) (pa c 3))
    (fadj f (pa c 0) (pa c 4)) (fadj f (pa c 1) (pa c 2)) (fadj f (pa c 1) (pa c 3))
    (fadj f (pa c 1) (pa c 4)) (fadj f (pa c 2) (pa c 3)) (fadj f (pa c 2) (pa c 4))
    (fadj f (pa c 3) (pa c 4))

theorem pullF_fadj_lt (c f u v : ℕ) (huv : u < v) (hv : v < 5) :
    fadj (pullF c f) u v = fadj f (pa c u) (pa c v) := by
  obtain ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩ :=
    mk10_fadj (fadj f (pa c 0) (pa c 1)) (fadj f (pa c 0) (pa c 2)) (fadj f (pa c 0) (pa c 3))
      (fadj f (pa c 0) (pa c 4)) (fadj f (pa c 1) (pa c 2)) (fadj f (pa c 1) (pa c 3))
      (fadj f (pa c 1) (pa c 4)) (fadj f (pa c 2) (pa c 3)) (fadj f (pa c 2) (pa c 4))
      (fadj f (pa c 3) (pa c 4))
  unfold pullF
  interval_cases v <;> interval_cases u <;> assumption

theorem pullF_fadj (c f u v : ℕ) (hu : u < 5) (hv : v < 5) :
    fadj (pullF c f) u v = fadj f (pa c u) (pa c v) := by
  rcases Nat.lt_trichotomy u v with h | h | h
  · exact pullF_fadj_lt c f u v h hv
  · subst h
    rw [fadj_self, fadj_self]
  · rw [fadj_comm (pullF c f) u v, pullF_fadj_lt c f v u h hu, fadj_comm f (pa c v) (pa c u)]

def pullQ (c q : ℕ) : ℕ :=
  mk5 (q.testBit (pa c 0)) (q.testBit (pa c 1)) (q.testBit (pa c 2)) (q.testBit (pa c 3))
    (q.testBit (pa c 4))

theorem pullQ_testBit (c q v : ℕ) (hv : v < 5) : (pullQ c q).testBit v = q.testBit (pa c v) := by
  unfold pullQ
  rw [mk5_testBit _ _ _ _ _ v hv]
  interval_cases v <;> rfl

theorem pullQ_zero (c : ℕ) : pullQ c 0 = 0 := by
  simp [pullQ, mk5]

theorem pullQ_lt (c q : ℕ) : pullQ c q < 32 := mk5_lt _ _ _ _ _

def row (f v : ℕ) : ℕ := mk5 (fadj f v 0) (fadj f v 1) (fadj f v 2) (fadj f v 3) (fadj f v 4)

theorem row_testBit (f v a : ℕ) (ha : a < 5) : (row f v).testBit a = fadj f v a := by
  unfold row
  rw [mk5_testBit _ _ _ _ _ a ha]
  interval_cases a <;> rfl

theorem row_lt (f v : ℕ) : row f v < 32 := mk5_lt _ _ _ _ _

def PermsOK (perms : List ℕ) : Prop :=
  ∀ c ∈ perms, (∀ u < 5, pa c u < 5) ∧ (∀ u < 5, ∀ v < 5, pa c u = pa c v → u = v)

def permsB (perms : List ℕ) : Bool :=
  perms.all fun c => (List.range 5).all fun u => decide (pa c u < 5) &&
    (List.range 5).all fun v => decide (pa c u = pa c v → u = v)

theorem permsB_sound {perms : List ℕ} (h : permsB perms = true) : PermsOK perms := by
  simp only [permsB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  intro c hc
  exact ⟨fun u hu => (h c hc u hu).1, fun u hu v hv => (h c hc u hu).2 v hv⟩

theorem pullQ_inj {perms : List ℕ} (hP : PermsOK perms) (c : ℕ) (hc : c ∈ perms)
    (a : ℕ) (ha : a < 32) (b : ℕ) (hb : b < 32) (e : pullQ c a = pullQ c b) : a = b := by
  obtain ⟨p1, p2⟩ := hP c hc
  apply bits_ext a ha b hb
  intro w hw
  obtain ⟨u, hu, rfl⟩ := surj_of_inj p1 p2 w hw
  rw [← pullQ_testBit c a u hu, ← pullQ_testBit c b u hu, e]

def padj (f : ℕ) (qs : List ℕ) (u v : ℕ) : Bool :=
  if u < 5 then (if v < 5 then fadj f u v else (gd qs (v - 5)).testBit u)
  else (if v < 5 then (gd qs (u - 5)).testBit v else false)

theorem padj_cc {f : ℕ} {qs : List ℕ} {u v : ℕ} (hu : u < 5) (hv : v < 5) :
    padj f qs u v = fadj f u v := by
  unfold padj; rw [if_pos hu, if_pos hv]

theorem padj_co {f : ℕ} {qs : List ℕ} {u v : ℕ} (hu : u < 5) (hv : ¬ v < 5) :
    padj f qs u v = (gd qs (v - 5)).testBit u := by
  unfold padj; rw [if_pos hu, if_neg hv]

theorem padj_oc {f : ℕ} {qs : List ℕ} {u v : ℕ} (hu : ¬ u < 5) (hv : v < 5) :
    padj f qs u v = (gd qs (u - 5)).testBit v := by
  unfold padj; rw [if_neg hu, if_pos hv]

theorem padj_oo {f : ℕ} {qs : List ℕ} {u v : ℕ} (hu : ¬ u < 5) (hv : ¬ v < 5) :
    padj f qs u v = false := by
  unfold padj; rw [if_neg hu, if_neg hv]

theorem padj_out {f : ℕ} {qs : List ℕ} (i : ℕ) {a : ℕ} (ha : a < 5) :
    padj f qs (5 + i) a = (gd qs i).testBit a := by
  have h : ¬ (5 + i < 5) := by omega
  rw [padj_oc h ha, Nat.add_sub_cancel_left]

def c4f (f : ℕ) : Bool :=
  (List.range 5).any fun u => (List.range 5).any fun v =>
    decide (u < v) && multi (row f u &&& row f v)

def c4q (f q : ℕ) : Bool := (List.range 5).any fun v => multi (q &&& row f v)

theorem c4f_bad {f : ℕ} (h : c4f f = true) (qs : List ℕ)
    (hsq : SQF (5 + qs.length) (padj f qs)) : False := by
  simp only [c4f, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨u, hu, v, hv, huv, hm⟩ := h
  obtain ⟨a, ha, b, hb, hab, h1, h2⟩ :=
    multi_spec _ (lt_of_le_of_lt Nat.and_le_left (row_lt f u)) hm
  rw [Nat.testBit_and, Bool.and_eq_true, row_testBit f u a ha, row_testBit f v a ha] at h1
  rw [Nat.testBit_and, Bool.and_eq_true, row_testBit f u b hb, row_testBit f v b hb] at h2
  exact hsq u v a b (by omega) (by omega) (by omega) (by omega) (by omega) hab
    (by rw [padj_cc hu ha]; exact h1.1) (by rw [padj_cc hv ha]; exact h1.2)
    (by rw [padj_cc hu hb]; exact h2.1) (by rw [padj_cc hv hb]; exact h2.2)

theorem adm_of_valid {f : ℕ} {qs : List ℕ} (hq : ∀ q ∈ qs, q < 32)
    (hsq : SQF (5 + qs.length) (padj f qs)) : ∀ q ∈ qs, c4q f q = false := by
  intro q hqm
  obtain ⟨i, hi, rfl⟩ := mem_gd qs q hqm
  by_contra hne
  have ht : c4q f (gd qs i) = true := by simpa using hne
  simp only [c4q, List.any_eq_true, List.mem_range] at ht
  obtain ⟨v, hv, hm⟩ := ht
  obtain ⟨a, ha, b, hb, hab, h1, h2⟩ :=
    multi_spec _ (lt_of_le_of_lt Nat.and_le_left (hq _ hqm)) hm
  rw [Nat.testBit_and, Bool.and_eq_true, row_testBit f v a ha] at h1
  rw [Nat.testBit_and, Bool.and_eq_true, row_testBit f v b hb] at h2
  exact hsq (5 + i) v a b (by omega) (by omega) (by omega) (by omega) (by omega) hab
    (by rw [padj_out i ha]; exact h1.1) (by rw [padj_cc hv ha]; exact h1.2)
    (by rw [padj_out i hb]; exact h2.1) (by rw [padj_cc hv hb]; exact h2.2)

theorem clean_of_valid {f : ℕ} {qs : List ℕ} (hq : ∀ q ∈ qs, q < 32)
    (hsq : SQF (5 + qs.length) (padj f qs)) :
    ∀ a ∈ qs, ∀ b ∈ qs, a ≠ b → multi (a &&& b) = false := by
  intro a ha b hb hne
  obtain ⟨i, hi, rfl⟩ := mem_gd qs a ha
  obtain ⟨j, hj, rfl⟩ := mem_gd qs b hb
  have hij : i ≠ j := fun e => hne (by rw [e])
  by_contra hcon
  have ht : multi (gd qs i &&& gd qs j) = true := by simpa using hcon
  obtain ⟨x, hx, y, hy, hxy, h1, h2⟩ :=
    multi_spec _ (lt_of_le_of_lt Nat.and_le_left (hq _ ha)) ht
  rw [Nat.testBit_and, Bool.and_eq_true] at h1 h2
  exact hsq (5 + i) (5 + j) x y (by omega) (by omega) (by omega) (by omega) (by omega) hxy
    (by rw [padj_out i hx]; exact h1.1) (by rw [padj_out j hx]; exact h1.2)
    (by rw [padj_out i hy]; exact h2.1) (by rw [padj_out j hy]; exact h2.2)

def memR (qs : List ℕ) (t v : ℕ) : Bool :=
  if v < 5 then t.testBit v else (gd qs (v - 5) &&& t) == 0

def rset (qs : List ℕ) (t : ℕ) : List ℕ := (List.range (5 + qs.length)).filter (memR qs t)

def indepB (f t : ℕ) : Bool :=
  (List.range 5).all fun u => (List.range 5).all fun v =>
    !(t.testBit u && t.testBit v && fadj f u v)

def indOf (f : ℕ) : List ℕ := (List.range 32).filter (indepB f)

def admOf (f : ℕ) : List ℕ := (List.range' 1 31).filter (fun q => !c4q f q)

theorem mem_rset (qs : List ℕ) (t x : ℕ) :
    x ∈ (rset qs t).toFinset ↔ x < 5 + qs.length ∧ memR qs t x = true := by
  simp only [rset, List.mem_toFinset, List.mem_filter, List.mem_range]

theorem rset_sub (qs : List ℕ) (t : ℕ) :
    (rset qs t).toFinset ⊆ Finset.range (5 + qs.length) := by
  intro x hx
  exact Finset.mem_range.mpr ((mem_rset qs t x).mp hx).1

theorem rset_card (qs : List ℕ) (t : ℕ) : (rset qs t).toFinset.card = (rset qs t).length := by
  apply List.toFinset_card_of_nodup
  unfold rset
  apply List.Nodup.filter
  first
  | exact List.nodup_range
  | exact List.nodup_range _

theorem rset_indep {f t : ℕ} (qs : List ℕ) (ht : indepB f t = true) :
    Indep (padj f qs) (rset qs t).toFinset := by
  intro u hu v hv
  obtain ⟨_, hum⟩ := (mem_rset qs t u).mp hu
  obtain ⟨_, hvm⟩ := (mem_rset qs t v).mp hv
  simp only [indepB, List.all_eq_true, List.mem_range] at ht
  by_cases h5u : u < 5 <;> by_cases h5v : v < 5
  · rw [padj_cc h5u h5v]
    have hu' : t.testBit u = true := by simpa [memR, h5u] using hum
    have hv' : t.testBit v = true := by simpa [memR, h5v] using hvm
    have h := ht u h5u v h5v
    rw [hu', hv'] at h
    simpa using h
  · rw [padj_co h5u h5v]
    have hu' : t.testBit u = true := by simpa [memR, h5u] using hum
    have hz : gd qs (v - 5) &&& t = 0 := by simpa [memR, h5v] using hvm
    have h := Nat.testBit_and (gd qs (v - 5)) t u
    rw [hz, hu'] at h
    simpa using h.symm
  · rw [padj_oc h5u h5v]
    have hv' : t.testBit v = true := by simpa [memR, h5v] using hvm
    have hz : gd qs (u - 5) &&& t = 0 := by simpa [memR, h5u] using hum
    have h := Nat.testBit_and (gd qs (u - 5)) t v
    rw [hz, hv'] at h
    simpa using h.symm
  · exact padj_oo h5u h5v

def node (ind : List ℕ) (wok : List ℕ → ℕ → Bool) (B : ℕ) (qs : List ℕ) (w : ℕ) : Option ℕ :=
  if ind.any (fun t => decide (qs.length < (rset qs t).length)) then some w
  else if (List.range (5 + qs.length)).any (fun v => ind.all (fun t =>
      memR qs t v || decide ((rset qs t).length ≠ qs.length))) then some w
  else if wok qs (w % B) then some (w / B) else none

theorem node_sound {f : ℕ} {ind : List ℕ} {wok : List ℕ → ℕ → Bool} {B : ℕ} {qs : List ℕ}
    {w w' : ℕ}
    (hind : ∀ t, t ∈ ind ↔ (t < 32 ∧ indepB f t = true))
    (hq : ∀ q ∈ qs, q < 32)
    (hv : Valid (5 + qs.length) qs.length (padj f qs))
    (h : node ind wok B qs w = some w') : ∃ x, wok qs x = true := by
  classical
  unfold node at h
  split_ifs at h with h1 h2 h3
  · exfalso
    simp only [List.any_eq_true, decide_eq_true_eq] at h1
    obtain ⟨t, ht, hlt⟩ := h1
    have hc := hv.hard (rset qs t).toFinset (rset_sub qs t) (rset_indep qs ((hind t).mp ht).2)
    rw [rset_card] at hc
    omega
  · exfalso
    simp only [List.any_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      decide_eq_true_eq] at h2
    obtain ⟨v, hvn, hall⟩ := h2
    obtain ⟨S, hS, hI, hvS, hcard⟩ := hv.crit v hvn
    obtain ⟨t, ht_def⟩ : ∃ t, t = mk5 (decide (0 ∈ S)) (decide (1 ∈ S)) (decide (2 ∈ S))
        (decide (3 ∈ S)) (decide (4 ∈ S)) := ⟨_, rfl⟩
    have htb : ∀ u, u < 5 → t.testBit u = decide (u ∈ S) := by
      intro u hu
      rw [ht_def, mk5_testBit _ _ _ _ _ u hu]
      interval_cases u <;> rfl
    have ht32 : t < 32 := by rw [ht_def]; exact mk5_lt _ _ _ _ _
    have hti : indepB f t = true := by
      simp only [indepB, List.all_eq_true, List.mem_range]
      intro a ha b hb
      by_cases e1 : t.testBit a = true
      · by_cases e2 : t.testBit b = true
        · have haS : a ∈ S := by
            rw [htb a ha] at e1
            simpa using e1
          have hbS : b ∈ S := by
            rw [htb b hb] at e2
            simpa using e2
          have e3 := hI a haS b hbS
          rw [padj_cc ha hb] at e3
          simp [e3]
        · simp [e2]
      · simp [e1]
    have hsub : S ⊆ (rset qs t).toFinset := by
      intro x hx
      have hxn := Finset.mem_range.mp (hS hx)
      refine (mem_rset qs t x).mpr ⟨hxn, ?_⟩
      by_cases h5 : x < 5
      · simp [memR, h5, htb x h5, hx]
      · have hz : gd qs (x - 5) &&& t = 0 := by
          apply and_zero _ (hq _ (gd_mem qs (x - 5) (by omega))) _ ht32
          intro j hj hjj
          obtain ⟨hj1, hj2⟩ := hjj
          rw [htb j hj] at hj2
          have hjS : j ∈ S := by simpa using hj2
          have e := hI j hjS x hx
          rw [padj_co hj h5, hj1] at e
          exact absurd e (by simp)
        simp [memR, h5, hz]
    have hc := hv.hard (rset qs t).toFinset (rset_sub qs t) (rset_indep qs hti)
    have heq : S = (rset qs t).toFinset :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hc)
    have hlen : (rset qs t).length = qs.length := by
      rw [← rset_card, ← heq, hcard]
    rcases hall t ((hind t).mpr ⟨ht32, hti⟩) with hm | hne
    · apply hvS
      rw [heq]
      exact (mem_rset qs t v).mpr ⟨hvn, hm⟩
    · exact hne hlen
  · exact ⟨_, h3⟩

def loop (k : ℕ → List ℕ → ℕ → Option ℕ) : List ℕ → ℕ → Option ℕ
  | [], w => some w
  | q :: rest, w =>
    match k q rest w with
    | none => none
    | some w' => loop k rest w'

def child (nd : List ℕ → ℕ → Option ℕ) (rec : List ℕ → List ℕ → ℕ → Option ℕ)
    (qs : List ℕ) (q : ℕ) (rest : List ℕ) (w : ℕ) : Option ℕ :=
  if qs.any (fun x => multi (x &&& q)) then some w
  else
    match nd (qs ++ [q]) w with
    | none => none
    | some w2 => rec rest (qs ++ [q]) w2

def walk (nd : List ℕ → ℕ → Option ℕ) : ℕ → List ℕ → List ℕ → ℕ → Option ℕ
  | 0, _, _, w => some w
  | d + 1, cands, qs, w => loop (child nd (walk nd d) qs) cands w

theorem loop_sound (k : ℕ → List ℕ → ℕ → Option ℕ) : ∀ (cands : List ℕ) (w w' : ℕ),
    loop k cands w = some w' → ∀ q ext, (q :: ext).Sublist cands →
      ∃ rest wa wb, ext.Sublist rest ∧ k q rest wa = some wb
  | [], _, _, _, q, ext, hs => by cases hs
  | c :: cs, w, w', h, q, ext, hs => by
      have h' : (match k c cs w with
        | none => none
        | some w1 => loop k cs w1) = some w' := h
      cases hk : k c cs w with
      | none => rw [hk] at h'; simp at h'
      | some w1 =>
        rw [hk] at h'
        rcases hs with _ | ⟨_, hs'⟩ | ⟨_, hs'⟩
        · exact loop_sound k cs w1 w' h' q ext hs'
        · exact ⟨cs, w, w1, hs', hk⟩

theorem child_some {nd : List ℕ → ℕ → Option ℕ} {rec : List ℕ → List ℕ → ℕ → Option ℕ}
    {qs : List ℕ} {q : ℕ} {rest : List ℕ} {w wb : ℕ}
    (h : child nd rec qs q rest w = some wb)
    (hc : ∀ x ∈ qs, multi (x &&& q) = false) :
    ∃ w2, nd (qs ++ [q]) w = some w2 ∧ rec rest (qs ++ [q]) w2 = some wb := by
  unfold child at h
  have hc' : (qs.any fun x => multi (x &&& q)) = false := by
    rw [List.any_eq_false]
    intro x hx
    simp [hc x hx]
  rw [hc'] at h
  simp only [Bool.false_eq_true, if_false] at h
  cases hn : nd (qs ++ [q]) w with
  | none => rw [hn] at h; simp at h
  | some w2 =>
    rw [hn] at h
    exact ⟨w2, rfl, h⟩

theorem walk_sound (nd : List ℕ → ℕ → Option ℕ) : ∀ (d : ℕ) (cands qs : List ℕ) (w w' : ℕ),
    walk nd d cands qs w = some w' → ∀ ext : List ℕ, ext ≠ [] → ext.Sublist cands →
      ext.length ≤ d → (qs ++ ext).Pairwise (fun a b => multi (a &&& b) = false) →
      ∃ wa wb, nd (qs ++ ext) wa = some wb
  | 0, _, _, _, _, _, ext, hne, _, hl, _ => by
      cases ext with
      | nil => exact absurd rfl hne
      | cons q ext' => simp at hl
  | d + 1, cands, qs, w, w', h, ext, hne, hs, hl, hp => by
      cases ext with
      | nil => exact absurd rfl hne
      | cons q ext' =>
        have h' : loop (child nd (walk nd d) qs) cands w = some w' := h
        obtain ⟨rest, wa, wb, hs', hk⟩ := loop_sound _ cands w w' h' q ext' hs
        have hcl : ∀ x ∈ qs, multi (x &&& q) = false := fun x hx =>
          (List.pairwise_append.mp hp).2.2 x hx q List.mem_cons_self
        obtain ⟨w2, hn, hr⟩ := child_some hk hcl
        by_cases he : ext' = []
        · subst he
          exact ⟨wa, w2, hn⟩
        · have hp' : ((qs ++ [q]) ++ ext').Pairwise (fun a b => multi (a &&& b) = false) := by
            rw [List.append_assoc]; exact hp
          have hl' : ext'.length ≤ d := by
            simp only [List.length_cons] at hl
            omega
          obtain ⟨a, b, hab⟩ := walk_sound nd d rest (qs ++ [q]) w2 wb hr ext' he hs' hl' hp'
          rw [List.append_assoc] at hab
          exact ⟨a, b, hab⟩

def walkTop (f B : ℕ) (wok : List ℕ → ℕ → Bool) (ind adm : List ℕ) (w : ℕ) : Bool :=
  (indOf f == ind) && (admOf f == adm) &&
    (match node ind wok B [] w with
     | none => false
     | some w1 => (walk (node ind wok B) 5 adm [] w1).isSome)

theorem top_sound {f B : ℕ} {wok : List ℕ → ℕ → Bool} {ind adm : List ℕ} {w : ℕ}
    (h : walkTop f B wok ind adm w = true) {qs : List ℕ}
    (hs : qs.Pairwise (· < ·)) (hq : ∀ q ∈ qs, 1 ≤ q ∧ q < 32) (hl : qs.length ≤ 5)
    (hv : Valid (5 + qs.length) qs.length (padj f qs)) : ∃ x, wok qs x = true := by
  unfold walkTop at h
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨⟨hi, ha⟩, hw⟩ := h
  have hind : ∀ t, t ∈ ind ↔ (t < 32 ∧ indepB f t = true) := by
    intro t
    rw [← hi]
    simp only [indOf, List.mem_filter, List.mem_range]
  have hq32 : ∀ q ∈ qs, q < 32 := fun q h => (hq q h).2
  cases h0 : node ind wok B [] w with
  | none => rw [h0] at hw; simp at hw
  | some w1 =>
    rw [h0] at hw
    have hw' : (walk (node ind wok B) 5 adm [] w1).isSome = true := hw
    obtain ⟨w2, h1⟩ := Option.isSome_iff_exists.mp hw'
    by_cases he : qs = []
    · subst he
      exact node_sound hind hq32 hv h0
    · have hsub : qs.Sublist adm := by
        rw [← ha]
        have s1 : qs.Sublist (List.range' 1 31) :=
          sublist_range' 31 1 qs hs (fun x hx => by have := hq x hx; omega)
        have s2 := s1.filter (fun q => !c4q f q)
        have s3 : qs.filter (fun q => !c4q f q) = qs := by
          apply List.filter_eq_self.mpr
          intro a haq
          simp [adm_of_valid hq32 hv.sqf a haq]
        rw [s3] at s2
        exact s2
      have hclean : qs.Pairwise (fun a b => multi (a &&& b) = false) :=
        List.Pairwise.imp_of_mem
          (fun {a b} ha hb hlt => clean_of_valid hq32 hv.sqf a ha b hb (Nat.ne_of_lt hlt)) hs
      obtain ⟨wa, wb, hn⟩ := walk_sound _ 5 adm [] w1 w2 h1 qs he hsub hl hclean
      exact node_sound hind hq32 hv hn

def sig1 (c u : ℕ) : ℕ := if u < 5 then pa c u else u

theorem iso_relabel {perms : List ℕ} (hP : PermsOK perms) {c : ℕ} (hc : c ∈ perms)
    (f : ℕ) (qs : List ℕ) :
    Iso (5 + qs.length) (padj (pullF c f) (qs.map (pullQ c))) (padj f qs) := by
  obtain ⟨p1, p2⟩ := hP c hc
  refine ⟨sig1 c, ?_, ?_, ?_⟩
  · intro u hu
    unfold sig1
    split_ifs with h
    · have := p1 u h
      omega
    · exact hu
  · intro u hu v hv e
    unfold sig1 at e
    split_ifs at e with h1 h2 h2
    · exact p2 u h1 v h2 e
    · have := p1 u h1
      omega
    · have := p1 v h2
      omega
    · exact e
  · intro u hu v hv
    by_cases h1 : u < 5 <;> by_cases h2 : v < 5
    · have e1 : sig1 c u = pa c u := if_pos h1
      have e2 : sig1 c v = pa c v := if_pos h2
      rw [e1, e2, padj_cc h1 h2, padj_cc (p1 u h1) (p1 v h2), pullF_fadj c f u v h1 h2]
    · have e1 : sig1 c u = pa c u := if_pos h1
      have e2 : sig1 c v = v := if_neg h2
      rw [e1, e2, padj_co h1 h2, padj_co (p1 u h1) h2, gd_map _ (pullQ_zero c),
        pullQ_testBit c _ u h1]
    · have e1 : sig1 c u = u := if_neg h1
      have e2 : sig1 c v = pa c v := if_pos h2
      rw [e1, e2, padj_oc h1 h2, padj_oc h1 (p1 v h2), gd_map _ (pullQ_zero c),
        pullQ_testBit c _ v h2]
    · have e1 : sig1 c u = u := if_neg h1
      have e2 : sig1 c v = v := if_neg h2
      rw [e1, e2, padj_oo h1 h2, padj_oo h1 h2]

def sig2 (L' L : List ℕ) (u : ℕ) : ℕ := if u < 5 then u else 5 + idx (gd L' (u - 5)) L

theorem iso_reorder (f : ℕ) {L' L : List ℕ} (hlen : L'.length = L.length) (hnd : L'.Nodup)
    (hsub : ∀ x ∈ L', x ∈ L) : Iso (5 + L'.length) (padj f L') (padj f L) := by
  have hm : ∀ u, ¬ u < 5 → u < 5 + L'.length → gd L' (u - 5) ∈ L :=
    fun u h1 h2 => hsub _ (gd_mem L' (u - 5) (by omega))
  refine ⟨sig2 L' L, ?_, ?_, ?_⟩
  · intro u hu
    unfold sig2
    split_ifs with h
    · exact hu
    · have := idx_lt _ L (hm u h hu)
      omega
  · intro u hu v hv e
    unfold sig2 at e
    split_ifs at e with h1 h2 h2
    · exact e
    · omega
    · omega
    · have e' : idx (gd L' (u - 5)) L = idx (gd L' (v - 5)) L := by omega
      have e2 := congrArg (gd L) e'
      rw [gd_idx _ L (hm u h1 hu), gd_idx _ L (hm v h2 hv)] at e2
      have := gd_inj L' hnd (u - 5) (v - 5) (by omega) (by omega) e2
      omega
  · intro u hu v hv
    by_cases h1 : u < 5 <;> by_cases h2 : v < 5
    · have e1 : sig2 L' L u = u := if_pos h1
      have e2 : sig2 L' L v = v := if_pos h2
      rw [e1, e2, padj_cc h1 h2, padj_cc h1 h2]
    · have e1 : sig2 L' L u = u := if_pos h1
      have e2 : sig2 L' L v = 5 + idx (gd L' (v - 5)) L := if_neg h2
      have h3 : ¬ (5 + idx (gd L' (v - 5)) L < 5) := by omega
      rw [e1, e2, padj_co h1 h2, padj_co h1 h3, Nat.add_sub_cancel_left,
        gd_idx _ L (hm v h2 hv)]
    · have e1 : sig2 L' L u = 5 + idx (gd L' (u - 5)) L := if_neg h1
      have e2 : sig2 L' L v = v := if_pos h2
      have h3 : ¬ (5 + idx (gd L' (u - 5)) L < 5) := by omega
      rw [e1, e2, padj_oc h1 h2, padj_oc h3 h2, Nat.add_sub_cancel_left,
        gd_idx _ L (hm u h1 hu)]
    · have e1 : sig2 L' L u = 5 + idx (gd L' (u - 5)) L := if_neg h1
      have e2 : sig2 L' L v = 5 + idx (gd L' (v - 5)) L := if_neg h2
      have h3 : ¬ (5 + idx (gd L' (u - 5)) L < 5) := by omega
      have h4 : ¬ (5 + idx (gd L' (v - 5)) L < 5) := by omega
      rw [e1, e2, padj_oo h1 h2, padj_oo h3 h4]

abbrev Cat := ℕ × List ℕ

namespace Cat
abbrev n (g : Cat) : ℕ := g.1
abbrev adj (g : Cat) : List ℕ := g.2
end Cat

def cadj (g : Cat) (u v : ℕ) : Bool := (gd g.adj u).testBit v

abbrev Entry := ℕ × List ℕ × List ℕ

namespace Entry
abbrev g (g : Entry) : ℕ := g.1
abbrev Q (g : Entry) : List ℕ := g.2.1
abbrev s (g : Entry) : List ℕ := g.2.2
end Entry

def isoB (n : ℕ) (A B : ℕ → ℕ → Bool) (s : List ℕ) : Bool :=
  (List.range n).all fun u => decide (gd s u < n) &&
    (List.range n).all fun v => decide (gd s u = gd s v → u = v) &&
      (A u v == B (gd s u) (gd s v))

theorem isoB_sound {n : ℕ} {A B : ℕ → ℕ → Bool} {s : List ℕ} (h : isoB n A B s = true) :
    Iso n A B := by
  simp only [isoB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact ⟨gd s, fun u hu => (h u hu).1, fun u hu v hv => ((h u hu).2 v hv).1,
    fun u hu v hv => ((h u hu).2 v hv).2⟩

def entOK (cat : List Cat) (F : ℕ) (e : Entry) : Bool :=
  match nth cat e.g with
  | none => false
  | some g =>
    decide (g.n = 5 + e.Q.length) && nodupB e.Q &&
      isoB (5 + e.Q.length) (padj F e.Q) (cadj g) e.s

theorem entOK_sound {cat : List Cat} {F : ℕ} {e : Entry} (h : entOK cat F e = true) :
    ∃ g, nth cat e.g = some g ∧ g.n = 5 + e.Q.length ∧ e.Q.Nodup ∧
      Iso (5 + e.Q.length) (padj F e.Q) (cadj g) := by
  unfold entOK at h
  cases hg : nth cat e.g with
  | none => rw [hg] at h; simp at h
  | some g =>
    rw [hg] at h
    have h' : (decide (g.n = 5 + e.Q.length) && nodupB e.Q &&
      isoB (5 + e.Q.length) (padj F e.Q) (cadj g) e.s) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact ⟨g, rfl, h'.1.1, nodupB_sound _ h'.1.2, isoB_sound h'.2⟩

def wokF (A : ℕ) (auts : List ℕ) (ents : List Entry) (qs : List ℕ) (x : ℕ) : Bool :=
  match nth auts (x % A) with
  | none => false
  | some c =>
    match nth ents (x / A) with
    | none => false
    | some e =>
      decide (e.Q.length = qs.length) && e.Q.all (fun y => decide (y ∈ qs.map (pullQ c)))

theorem wokF_sound {A : ℕ} {auts : List ℕ} {ents : List Entry} {qs : List ℕ} {x : ℕ}
    (h : wokF A auts ents qs x = true) :
    ∃ c, c ∈ auts ∧ ∃ e, e ∈ ents ∧ e.Q.length = qs.length ∧
      ∀ y ∈ e.Q, y ∈ qs.map (pullQ c) := by
  unfold wokF at h
  cases h1 : nth auts (x % A) with
  | none => rw [h1] at h; simp at h
  | some c =>
    rw [h1] at h
    have h' : (match nth ents (x / A) with
      | none => false
      | some e =>
        decide (e.Q.length = qs.length) &&
          e.Q.all (fun y => decide (y ∈ qs.map (pullQ c)))) = true := h
    cases h2 : nth ents (x / A) with
    | none => rw [h2] at h'; simp at h'
    | some e =>
      rw [h2] at h'
      have h'' : (decide (e.Q.length = qs.length) &&
          e.Q.all (fun y => decide (y ∈ qs.map (pullQ c)))) = true := h'
      rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h''
      refine ⟨c, nth_mem _ _ _ h1, e, nth_mem _ _ _ h2, h''.1, ?_⟩
      intro y hy
      exact of_decide_eq_true (h''.2 y hy)

abbrev FData := ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ × List Entry × ℕ

namespace FData
abbrev F (g : FData) : ℕ := g.1
abbrev A (g : FData) : ℕ := g.2.1
abbrev B (g : FData) : ℕ := g.2.2.1
abbrev ind (g : FData) : List ℕ := g.2.2.2.1
abbrev adm (g : FData) : List ℕ := g.2.2.2.2.1
abbrev auts (g : FData) : List ℕ := g.2.2.2.2.2.1
abbrev ents (g : FData) : List Entry := g.2.2.2.2.2.2.1
abbrev w (g : FData) : ℕ := g.2.2.2.2.2.2.2
end FData

def autsOK (perms : List ℕ) (d : FData) : Bool :=
  d.auts.all (fun c => decide (c ∈ perms) && (pullF c d.F == d.F))

def fOK (perms : List ℕ) (cat : List Cat) (d : FData) : Bool :=
  autsOK perms d && d.ents.all (entOK cat d.F) &&
    walkTop d.F d.B (wokF d.A d.auts d.ents) d.ind d.adm d.w

def canonB (perms Fs canon : List ℕ) : Bool :=
  (List.range 1024).all fun f =>
    c4f f || (decide (gd canon f ∈ perms) && decide (pullF (gd canon f) f ∈ Fs))

theorem canonB_sound {perms Fs canon : List ℕ} (h : canonB perms Fs canon = true)
    (f : ℕ) (hf : f < 1024) : c4f f = true ∨ ∃ c, c ∈ perms ∧ pullF c f ∈ Fs := by
  simp only [canonB, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h f hf with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨_, h1, h2⟩

theorem main {perms : List ℕ} {cat : List Cat} {ds : List FData} {canon : List ℕ}
    (hperm : permsB perms = true) (hcanon : canonB perms (ds.map FData.F) canon = true)
    (hds : ∀ d ∈ ds, fOK perms cat d = true)
    (f : ℕ) (qs : List ℕ) (hf : f < 1024) (hnd : qs.Nodup) (hq : ∀ q ∈ qs, 1 ≤ q ∧ q < 32)
    (hl : qs.length ≤ 5) (hv : Valid (5 + qs.length) qs.length (padj f qs)) :
    ∃ i g, nth cat i = some g ∧ g.n = 5 + qs.length ∧
      Iso (5 + qs.length) (padj f qs) (cadj g) := by
  have hP := permsB_sound hperm
  rcases canonB_sound hcanon f hf with hc4 | ⟨c, hc, hFm⟩
  · exact (c4f_bad hc4 qs hv.sqf).elim
  obtain ⟨d, hd, hdF⟩ := List.mem_map.mp hFm
  have hfd := hds d hd
  unfold fOK at hfd
  rw [Bool.and_eq_true, Bool.and_eq_true] at hfd
  obtain ⟨⟨hA0, hE0⟩, hW⟩ := hfd
  have hA : ∀ c2 ∈ d.auts, c2 ∈ perms ∧ pullF c2 d.F = d.F := by
    simp only [autsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hA0
    exact hA0
  have hE : ∀ e ∈ d.ents, entOK cat d.F e = true := List.all_eq_true.mp hE0
  have hL1len : (qs.map (pullQ c)).length = qs.length := List.length_map _
  have hL1nd : (qs.map (pullQ c)).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => pullQ_inj hP c hc a (hq a ha).2 b (hq b hb).2 e) hnd
  obtain ⟨hs, hslen, hsmem⟩ := isort_spec (qs.map (pullQ c)) hL1nd
  have hlen' : (isort (qs.map (pullQ c))).length = qs.length := hslen.trans hL1len
  have hsnd : (isort (qs.map (pullQ c))).Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  have iso1 : Iso (5 + qs.length) (padj d.F (isort (qs.map (pullQ c)))) (padj f qs) := by
    have r2 := iso_reorder d.F hslen hsnd (fun x hx => (hsmem x).mp hx)
    rw [hlen'] at r2
    have r1 := iso_relabel hP hc f qs
    rw [← hdF] at r1
    exact r2.trans r1
  have hv' : Valid (5 + (isort (qs.map (pullQ c))).length) (isort (qs.map (pullQ c))).length
      (padj d.F (isort (qs.map (pullQ c)))) := by
    rw [hlen']
    exact Valid.of_iso iso1 hv
  have hq' : ∀ q ∈ isort (qs.map (pullQ c)), 1 ≤ q ∧ q < 32 := by
    intro q hq1
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ((hsmem q).mp hq1)
    refine ⟨?_, pullQ_lt c a⟩
    by_contra h0
    have h00 : pullQ c a = pullQ c 0 := by
      rw [pullQ_zero]
      omega
    have e0 := pullQ_inj hP c hc a (hq a ha).2 0 (by norm_num) h00
    have := (hq a ha).1
    omega
  obtain ⟨x, hx⟩ := top_sound hW hs hq' (by rw [hlen']; exact hl) hv'
  obtain ⟨c2, hc2, e, he, hel, hesub⟩ := wokF_sound hx
  obtain ⟨hc2p, hc2F⟩ := hA c2 hc2
  obtain ⟨g, hg, hgn, hQnd, isoE⟩ := entOK_sound (hE e he)
  have helen : e.Q.length = qs.length := hel.trans hlen'
  have iso2 : Iso (5 + qs.length) (padj d.F e.Q) (padj d.F (isort (qs.map (pullQ c)))) := by
    have r2 := iso_reorder d.F (L' := e.Q) (L := (isort (qs.map (pullQ c))).map (pullQ c2))
      (by rw [List.length_map]; exact hel) hQnd hesub
    rw [helen] at r2
    have r1 := iso_relabel hP hc2p d.F (isort (qs.map (pullQ c)))
    rw [hc2F, hlen'] at r1
    exact r2.trans r1
  rw [helen] at isoE hgn
  exact ⟨e.g, g, hg, hgn, iso1.symm.trans (iso2.symm.trans isoE)⟩

end Coverage

namespace MoonPrize.Combine

open MoonPrize.Trace MoonPrize.Label

lemma gd_lookup (l : List ℕ) (i : ℕ) : Coverage.gd l i = lookup l i := by
  induction l generalizing i with
  | nil => simp [Coverage.gd,lookup]
  | cons a l ih => cases i with
    | zero => rfl
    | succ j => simpa [Coverage.gd,lookup] using ih j

lemma pair_index_checked : ∀ a b : Fin 5, a < b → pairIndex a.val b.val = Coverage.pidx a.val b.val := by
  decide +kernel

lemma adj_agrees (f : ℕ) (qs : List ℕ) (a b : ℕ) :
    codeAdj f qs a b = Coverage.padj f qs a b := by
  by_cases ha : a < 5 <;> by_cases hb : b < 5
  · cases lt_trichotomy a b with
    | inl h => simp [codeAdj,Coverage.padj,Coverage.fadj,ha,hb,h,not_lt_of_ge h.le,
        pair_index_checked ⟨a,ha⟩ ⟨b,hb⟩ h]
    | inr h => rcases h with rfl | h
               · simp [codeAdj,Coverage.padj,Coverage.fadj,ha]
               · simp [codeAdj,Coverage.padj,Coverage.fadj,ha,hb,h,not_lt_of_ge h.le,
                   pair_index_checked ⟨b,hb⟩ ⟨a,ha⟩ h]
  · simp [codeAdj,Coverage.padj,ha,hb,gd_lookup,lookup]
  · simp [codeAdj,Coverage.padj,ha,hb,gd_lookup,lookup]
  · simp [codeAdj,Coverage.padj,ha,hb]

theorem valid_of_critical {f : ℕ} {qs : List ℕ} (crit : Critical f qs) :
    Coverage.Valid (5+qs.length) qs.length (Coverage.padj f qs) := by
  classical
  let N := 5 + qs.length
  let H := codeGraph f qs
  have cv (u v : Fin N) : H.Adj u v ↔ Coverage.padj f qs u.val v.val = true := by
    change codeAdj f qs u.val v.val = true ↔ _
    rw [adj_agrees]
  refine ⟨?_,?_,?_⟩
  · intro u v a b hu hv ha hb uv ab nua nva nub nvb
    let U : Fin N := ⟨u,hu⟩
    let V : Fin N := ⟨v,hv⟩
    let A : Fin N := ⟨a,ha⟩
    let B : Fin N := ⟨b,hb⟩
    exact crit.1 U A V B (fun e => uv (congrArg Fin.val e)) (fun e => ab (congrArg Fin.val e))
      ((cv U A).mpr nua) ((cv V A).mpr nva).symm ((cv V B).mpr nvb) ((cv U B).mpr nub).symm
  · intro S sub ind
    let A := (Finset.univ : Finset (Fin N)).filter (fun v => v.val ∈ S)
    have am (v : Fin N) : v ∈ A ↔ v.val ∈ S := by simp [A]
    have ai : MoonPrize.Core.Independent H A := by
      intro v hv w hw edge
      have yes := (cv v w).mp edge
      have no := ind v.val ((am _).mp hv) w.val ((am _).mp hw)
      simp [no] at yes
    have equiv : A.map Fin.valEmbedding = S := by
      ext x
      constructor
      · intro h
        obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp h
        exact (am _).mp hv
      · intro h
        let v : Fin N := ⟨x,Finset.mem_range.mp (sub h)⟩
        exact Finset.mem_map.mpr ⟨v,(am v).mpr h,rfl⟩
    have cap := crit.2.1 A (Finset.subset_univ _) ai
    have cards := congrArg Finset.card equiv
    rw [Finset.card_map] at cards
    simp only [Finset.card_univ,Fintype.card_fin] at cap
    omega
  · intro v hv
    let V : Fin N := ⟨v,hv⟩
    obtain ⟨A,ind,absence,sz⟩ := crit.2.2 V
    refine ⟨A.map Fin.valEmbedding,?_,?_,?_,?_⟩
    · intro x hx
      obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_range.mpr u.isLt
    · intro x hx y hy
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
      by_contra wrong
      exact ind u hu v hv ((cv u v).mpr (by simpa using wrong))
    · intro mem
      obtain ⟨u,hu,eq⟩ := Finset.mem_map.mp mem
      exact absence ((Fin.ext eq : u = V) ▸ hu)
    · rw [Finset.card_map]
      omega

def asCat (g : Entry) : Coverage.Cat := ⟨g.n,g.adj⟩

def AllCriticalListed : Prop := ∀ (f : ℕ) (qs : List ℕ), f < 1024 → qs.Nodup →
    (∀ q ∈ qs, 1 ≤ q ∧ q < 32) → qs.length ≤ 5 →
    Coverage.Valid (5+qs.length) qs.length (Coverage.padj f qs) →
    ∃ i g, Coverage.nth (entries.map asCat) i = some g ∧ g.n = 5+qs.length ∧
      Coverage.Iso (5+qs.length) (Coverage.padj f qs) (Coverage.cadj g)

theorem graph_label (full : AllCriticalListed) (m : Fin 11) (H : SimpleGraph (Fin m.val))
    (sq : MoonPrize.Finite.NoSquare H) (hard : MoonPrize.Core.Hard H Finset.univ)
    (ex : ∀ v : Fin m.val, ∃ A : Finset (Fin m.val), MoonPrize.Core.Independent H A ∧ v ∉ A ∧ A.card+5=m.val) :
    ∃ g ∈ entries, ∃ lab : Fin m.val ≃ Fin g.n,
      ∀ u v, H.Adj u v ↔ (lookup g.adj (lab u).val).testBit (lab v).val = true := by
  classical
  obtain ⟨f,qs,wf,_,critical,⟨e⟩⟩ := bridge_critical m H sq hard ex
  obtain ⟨fsize,_,len,sorted,bounds⟩ := wf
  obtain ⟨i,c,ni,cn,ρ,rangeρ,one,edge⟩ :=
    full f qs fsize (sorted.imp (fun h => Nat.ne_of_lt h)) bounds len (valid_of_critical critical)
  obtain ⟨g,inside,rfl⟩ := List.mem_map.mp (Coverage.nth_mem _ _ _ ni)
  change g.n = 5+qs.length at cn
  let N := 5+qs.length
  let perm (u : Fin N) : Fin N := ⟨ρ u.val,rangeρ _ u.isLt⟩
  have inject : Function.Injective perm := by
    intro a b eq
    exact Fin.ext (one _ a.isLt _ b.isLt (congrArg Fin.val eq))
  let rename := Equiv.ofBijective perm ⟨inject,Finite.surjective_of_injective inject⟩
  let lab := e.toEquiv.trans (rename.trans (finCongr cn.symm))
  refine ⟨g,inside,lab,?_⟩
  intro u v
  have ae := edge (e u).val (e u).isLt (e v).val (e v).isLt
  change Coverage.padj f qs (e u).val (e v).val =
    (Coverage.gd g.adj (ρ (e u).val)).testBit (ρ (e v).val) at ae
  rw [gd_lookup] at ae
  have ce : H.Adj u v ↔ (codeGraph f qs).Adj (e u) (e v) := e.map_rel_iff.symm
  change H.Adj u v ↔ (lookup g.adj (ρ (e u).val)).testBit (ρ (e v).val) = true
  rw [ce]
  change codeAdj f qs (e u).val (e v).val = true ↔ _
  rw [adj_agrees,ae]

lemma all_shapes_agree : MoonPrize.Wiring.classes = shapes.map ShapeData.paths := by rfl

theorem class_number {paths : List ℕ} (hc : paths ∈ MoonPrize.Wiring.classes) :
    ∃ s : Fin 18, (shapeAt s.val).paths = paths := by
  rw [all_shapes_agree] at hc
  obtain ⟨sh,hsh,rfl⟩ := List.mem_map.mp hc
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hsh
  have len : shapes.length = 18 := rfl
  refine ⟨⟨i,len ▸ hi⟩,?_⟩
  simp [shapeAt,hi,eq]

theorem numeric_if (full : AllCriticalListed)
    (listed : ∀ g ∈ entries, listedOK g = true ∧ ∀ paths, (paths.length < 10 ∨
      ∃ s : Fin 18, (shapeAt s.val).paths = paths) → ¬ Embeds g.rows paths g.n) :
    MoonPrize.Bridge.NumericObstruction := by
  intro m H sq hard ex paths hc col hcol witness
  obtain ⟨g,mem,lab,edge⟩ := graph_label full m H sq hard ex
  obtain ⟨ok,closed⟩ := listed g mem
  exact closed paths (hc.imp_right class_number) (from_graph H g ok lab edge paths col hcol witness)

end MoonPrize.Combine

namespace MoonPrize.Trace

set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem documented_shapes : ∀ s : Fin 18, supportsShape (shapeAt s.val) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass0 : batch0.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass1 : batch1.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass2 : batch2.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass3 : batch3.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass4 : batch4.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass5 : batch5.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass6 : batch6.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass7 : batch7.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass8 : batch8.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass9 : batch9.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass10 : batch10.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass11 : batch11.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass12 : batch12.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass13 : batch13.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass14 : batch14.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass15 : batch15.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass16 : batch16.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass17 : batch17.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass18 : batch18.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass19 : batch19.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass20 : batch20.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass21 : batch21.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass22 : batch22.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass23 : batch23.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass24 : batch24.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass25 : batch25.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass26 : batch26.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass27 : batch27.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass28 : batch28.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass29 : batch29.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass30 : batch30.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass31 : batch31.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass32 : batch32.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass33 : batch33.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass34 : batch34.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass35 : batch35.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass36 : batch36.all ledgerOK = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 14000000 in
theorem pass37 : batch37.all ledgerOK = true := by decide +kernel

theorem entries_valid {g : Entry} (h : g ∈ entries) : ledgerOK g = true := by
  have b : batches.all (fun xs => xs.all ledgerOK) = true := by
    simp only [batches,List.all_cons,List.all_nil,pass0,pass1,pass2,pass3,pass4,pass5,pass6,pass7,pass8,pass9,pass10,pass11,pass12,pass13,pass14,pass15,pass16,pass17,pass18,pass19,pass20,pass21,pass22,pass23,pass24,pass25,pass26,pass27,pass28,pass29,pass30,pass31,pass32,pass33,pass34,pass35,pass36,pass37,Bool.and_self]
  obtain ⟨xs,hxs,hg⟩ := List.mem_flatten.mp h
  exact List.all_eq_true.mp (List.all_eq_true.mp b _ hxs) _ hg

end MoonPrize.Trace

namespace MoonPrize.Trace

abbrev Cell := ℕ × ℕ
abbrev Options := ℕ × List ℕ

def splitCells (x y : ℕ) (c : Cell) : List Cell :=
  [(c.1 &&& x,c.2 &&& y),(without c.1 x,without c.2 y)]

def capacity (p : Cell) : Bool := decide (count16 p.1 ≤ count16 p.2)

def halfFits (x y : ℕ) (c : Cell) : Bool :=
  capacity (c.1 &&& x,c.2 &&& y) && capacity (without c.1 x,without c.2 y)

def partitionFit : List Options → List Cell → Bool
  | [], _ => true
  | pair :: rest, cells => pair.2.any (fun y =>
      cells.all (halfFits pair.1 y) &&
      partitionFit rest ((cells.flatMap (splitCells pair.1 y)).filter (fun c => c.1 != 0)))

def fullCell (m t : ℕ) : Cell := (2^m - 1,2^t - 1)

def candidates (rows pats : List ℕ) (t : ℕ) (vs : List ℕ) : List Options :=
  vs.map (fun v =>
    let x := tally rows v
    (x,pats.filter (fun y => halfFits x y (fullCell rows.length t))))

def preserved (e : ℕ → ℕ) (m t : ℕ) (p : Cell) : Prop :=
  p.1 < 2^m ∧ p.2 < 2^t ∧ ∀ r < m, p.1.testBit r = true → p.2.testBit (e r) = true

lemma without_le (a b : ℕ) : without a b ≤ a := by
  apply Nat.le_of_testBit
  intro i h
  exact (Bool.and_eq_true_iff.mp ((without_bit a b i) ▸ h)).1

lemma capacity_of_preserve {e : ℕ → ℕ} {m t : ℕ} {c : Cell} (hm : m ≤ 16) (ht : t ≤ 16)
    (into : ∀ r < m, e r < t) (inj : Set.InjOn e (↑(Finset.range m) : Set ℕ))
    (hc : preserved e m t c) : capacity c = true := by
  obtain ⟨hn,hs,mapBits⟩ := hc
  have sub : (slice m c.1).image e ⊆ slice t c.2 := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨ar,bit⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (into a (Finset.mem_range.mp ar)),mapBits a (Finset.mem_range.mp ar) bit⟩
  have sz := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn (inj.mono (slice_sub ..))] at sz
  simpa [capacity,count_slice m _ hm hn,count_slice t _ ht hs] using sz

lemma holds_split {e : ℕ → ℕ} {m t : ℕ} {c : Cell} {x y : ℕ}
    (hc : preserved e m t c) (col : ∀ r < m, x.testBit r = y.testBit (e r)) :
    preserved e m t (c.1 &&& x,c.2 &&& y) ∧
    preserved e m t (without c.1 x,without c.2 y) := by
  obtain ⟨hn,hs,b⟩ := hc
  constructor
  · refine ⟨lt_of_le_of_lt Nat.and_le_left hn,lt_of_le_of_lt Nat.and_le_left hs,?_⟩
    intro r hr h
    have both := Bool.and_eq_true_iff.mp ((Nat.testBit_and ..) ▸ h)
    simp [Nat.testBit_and,b r hr both.1,←col r hr,both.2]
  · refine ⟨lt_of_le_of_lt (without_le ..) hn,lt_of_le_of_lt (without_le ..) hs,?_⟩
    intro r hr h
    have both := Bool.and_eq_true_iff.mp ((without_bit _ _ r) ▸ h)
    simp only [without_bit,b r hr both.1,←col r hr,Bool.true_and]
    exact both.2

lemma partition_of_map {e : ℕ → ℕ} {m t} (hm : m≤16) (ht : t≤16)
    (into : ∀ r < m,e r < t) (inj : Set.InjOn e (↑(Finset.range m) : Set ℕ)) :
    ∀ (os : List Options) (cs : List Cell), (∀ c∈cs, preserved e m t c) →
      (∀ o∈os, ∃ p ∈ o.2, ∀ r < m, o.1.testBit r = p.testBit (e r)) → partitionFit os cs = true := by
  intro os
  induction os with
  | nil => intro cs _ _; rfl
  | cons h tl ih =>
    intro cs hcs hopt
    obtain ⟨p,hp,hpcol⟩ := hopt h List.mem_cons_self
    apply List.any_eq_true.mpr
    refine ⟨p,hp,Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
    · apply List.all_eq_true.mpr
      intro c hc
      obtain ⟨a,b⟩ := holds_split (hcs c hc) hpcol
      exact Bool.and_eq_true_iff.mpr ⟨capacity_of_preserve hm ht into inj a,capacity_of_preserve hm ht into inj b⟩
    · apply ih _ _ (fun z hz => hopt z (List.mem_cons_of_mem _ hz))
      intro c hc
      obtain ⟨d,hd,hpart⟩ := List.mem_flatMap.mp (List.mem_filter.mp hc).1
      obtain ⟨a,b⟩ := holds_split (hcs d hd) hpcol
      simp only [splitCells,List.mem_cons,List.not_mem_nil,or_false] at hpart
      rcases hpart with rfl|rfl
      · exact a
      · exact b

end MoonPrize.Trace

namespace MoonPrize.Trace

abbrev Motion := ℕ × ℕ

def place (w i : ℕ) : ℕ := (w >>> (4*i)) &&& 15

def moveBits (t back x : ℕ) : ℕ :=
  maskOf ((List.range t).map (fun i => x.testBit (place back i)))

lemma moved_at (t back x i : ℕ) (hi : i<t) :
    (moveBits t back x).testBit i = x.testBit (place back i) := by
  simp [moveBits,bit_mask,hi]

def motionOK (ps : List ℕ) (t : ℕ) (m : Motion) : Bool :=
  (List.range t).all (fun z => decide (place m.1 z < t) && (place m.2 (place m.1 z) == z)) &&
    ps.all (fun p => ps.contains (moveBits t m.2 p))

def rootsOK (ps : List ℕ) (t : ℕ) (ms : List Motion) (rs : List ℕ) : Bool :=
  ms.all (motionOK ps t) &&
    ps.all (fun p => rs.contains p || ms.any (fun m => decide (moveBits t m.2 p < p)))

def ColumnMap (rows ps : List ℕ) (n t : ℕ) (e y : ℕ → ℕ) : Prop :=
  Set.InjOn e (↑(Finset.range rows.length) : Set ℕ) ∧
    (∀ r < rows.length, e r < t) ∧
    ∀ v < n, y v ∈ ps ∧ ∀ r < rows.length, (tally rows v).testBit r = (y v).testBit (e r)

theorem shift_columns {rows ps n t e y m} (h : ColumnMap rows ps n t e y)
    (ok : motionOK ps t m = true) :
    ColumnMap rows ps n t (fun r => place m.1 (e r)) (fun v => moveBits t m.2 (y v)) := by
  obtain ⟨indices,patterns⟩ := Bool.and_eq_true_iff.mp ok
  have index (z) (hz : z<t) : place m.1 z < t ∧ place m.2 (place m.1 z) = z := by
    simpa using List.all_eq_true.mp indices z (List.mem_range.mpr hz)
  obtain ⟨inj,into,cols⟩ := h
  refine ⟨?_,fun r hr => (index _ (into r hr)).1,?_⟩
  · intro r hr s hs eq
    apply inj hr hs
    have eq' := congrArg (place m.2) eq
    exact (index _ (into r (Finset.mem_range.mp hr))).2.symm.trans
      (eq'.trans (index _ (into s (Finset.mem_range.mp hs))).2)
  · intro v hv
    have p := cols v hv
    refine ⟨List.contains_iff_mem.mp (List.all_eq_true.mp patterns _ p.1),?_⟩
    intro r hr
    rw [moved_at _ _ _ _ (index _ (into r hr)).1,(index _ (into r hr)).2]
    exact p.2 r hr

theorem normalize_columns {rows ps n t ms rs} (ok : rootsOK ps t ms rs = true)
    (v : ℕ) (hv : v<n) (e y) (h : ColumnMap rows ps n t e y) :
    ∃ e' y', ColumnMap rows ps n t e' y' ∧ y' v ∈ rs := by
  obtain ⟨valid,all⟩ := Bool.and_eq_true_iff.mp ok
  suffices claim : ∀ k (f g : ℕ → ℕ), g v = k → ColumnMap rows ps n t f g →
      ∃ f' g', ColumnMap rows ps n t f' g' ∧ g' v ∈ rs by exact claim (y v) e y rfl h
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro f g val map
    have step := List.all_eq_true.mp all (g v) (map.2.2 v hv).1
    rcases Bool.or_eq_true_iff.mp step with root | smaller
    · exact ⟨f,g,map,List.contains_iff_mem.mp root⟩
    · obtain ⟨m,hm,down⟩ := List.any_eq_true.mp smaller
      have lt : moveBits t m.2 (g v) < k := val ▸ of_decide_eq_true down
      exact ih _ lt _ _ rfl (shift_columns map (List.all_eq_true.mp valid m hm))

def oneColumn (rows ps : List ℕ) (t v : ℕ) : Options :=
  let x := tally rows v
  (x,ps.filter (fun p => halfFits x p (fullCell rows.length t)))

def orbitRun (g : Entry) (sh : ShapeData) (rs vs : List ℕ) : Bool :=
  match vs with
  | [] => true
  | v::tl => partitionFit
      (oneColumn g.rows rs sh.paths.length v :: candidates g.rows sh.pats sh.paths.length tl)
      [fullCell g.rows.length sh.paths.length]

theorem orbit_excludes (g : Entry) (sh : ShapeData) (rs vs : List ℕ) (ms : List Motion)
    (gv : listedOK g = true) (sv : supportsShape sh = true)
    (ok : rootsOK sh.pats sh.paths.length ms rs = true) (vertices : ∀ v ∈ vs, v < g.n)
    (run : orbitRun g sh rs vs = false) : ¬Embeds g.rows sh.paths g.n := by
  intro rep
  cases vs with
  | nil => simp [orbitRun] at run
  | cons v tl =>
    have eg := entry_rows gv
    have lens := embeddings_card eg.2.1 eg.2.2.1 rep
    obtain ⟨bound,opts⟩ := Bool.and_eq_true_iff.mp sv
    have ht := of_decide_eq_true bound
    have hm := lens.trans ht
    obtain ⟨e,f,inj,into,data⟩ := embeddings_realize eg.2.1 eg.2.2.1 opts rep
    have pre : ColumnMap g.rows sh.pats g.n sh.paths.length e (fun z => lookup sh.pats (f z)) := by
      refine ⟨inj,into,?_⟩
      intro z hz
      exact ⟨lookup_mem (data z hz).1,fun r hr => (tally_at _ _ _ hr).trans ((data z hz).2.2 r hr)⟩
    obtain ⟨e',y,⟨inj',into',cols⟩,root⟩ := normalize_columns ok v (vertices v List.mem_cons_self) _ _ pre
    have base : preserved e' g.rows.length sh.paths.length (fullCell g.rows.length sh.paths.length) := by
      refine ⟨Nat.sub_lt (Nat.two_pow_pos _) (by decide),Nat.sub_lt (Nat.two_pow_pos _) (by decide),?_⟩
      intro r hr _
      exact (Nat.testBit_two_pow_sub_one _ _).trans (decide_eq_true (into' r hr))
    have option (z : ℕ) (hz : z < g.n) (ps : List ℕ) (member : y z ∈ ps) :
        ∃ p ∈ (oneColumn g.rows ps sh.paths.length z).2,
          ∀ r < g.rows.length, (tally g.rows z).testBit r = p.testBit (e' r) := by
      have col := (cols z hz).2
      obtain ⟨a,b⟩ := holds_split base col
      exact ⟨y z,List.mem_filter.mpr ⟨member,Bool.and_eq_true_iff.mpr
        ⟨capacity_of_preserve hm ht into' inj' a,capacity_of_preserve hm ht into' inj' b⟩⟩,col⟩
    have yes : orbitRun g sh rs (v::tl) = true := by
      apply partition_of_map hm ht into' inj'
      · simpa using base
      · intro o ho
        rcases List.mem_cons.mp ho with eq|rest
        · subst o
          exact option v (vertices v List.mem_cons_self) rs root
        · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp rest
          have hz' := vertices z (List.mem_cons_of_mem _ hz)
          exact option z hz' _ (cols z hz').1
    simp [run] at yes

end MoonPrize.Trace

namespace MoonPrize.Trace

def shapeRoots : List (List ℕ) := [[0,1,3,4,5,12,15,20,21,60,63,340,341,1020,1023],[0,1,2,3,8,10,15,16,17,18,19,64,72,80,90,113,127,144,145,146,147,576,584,720,730,1009,1023],[0,1,2,3,6,7,8,9,16,18,24,27,48,54,56,63,64,65,72,73,128,130,144,146,192,195,216,219,320,321,328,329,640,646,688,694,960,967,1016,1023],[0,1,2,3,6,7,8,9,16,18,24,27,40,41,80,86,120,127,136,137,272,274,408,411,680,681,1360,1366,2040,2047],[0,1,2,3,4,5,8,10,12,15,16,17,18,19,32,33,36,37,64,72,80,90,96,108,113,127,132,133,264,266,396,399,528,529,530,531,1056,1057,1188,1189,2112,2376,2640,2906,3168,3564,3697,4095],[0,1,2,3,8,10,15,18,19,72,90,127,1170,1171,4680,5850,8191],[0,1,3,5,15,16,17,21,48,51,63,64,65,80,81,192,195,240,243,320,325,336,341,960,975,1008,1023],[0,1,2,3,5,10,15,16,17,21,32,34,48,51,96,106,112,127,144,145,149,288,290,432,435,864,874,1008,1023],[0,1,2,3,5,10,15,16,17,21,32,34,48,51,96,106,112,127,128,129,144,145,256,258,288,290,384,387,432,435,640,645,656,661,1280,1290,1376,1386,1920,1935,2032,2047],[0,1,3,15,16,17,48,51,240,255,272,273,816,819,4080,4095],[0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,48,51,64,68,72,76,96,106,116,127,132,133,264,266,396,399,528,529,660,661,1056,1058,1584,1587,2112,2244,2376,2508,3168,3434,3828,4095],[0,1,3,5,7,8,9,24,27,40,45,96,100,120,127,135,792,795,3960,4095],[0,1,3,4,5,7,8,9,24,27,32,36,40,45,96,100,120,127,128,129,132,133,384,387,388,391,512,513,520,521,1536,1539,1560,1563,2048,2080,2176,2212,2560,2600,2689,2733,6144,6240,6528,6628,7680,7800,8067,8191],[0,1,3,4,5,12,15,76,85,127,396,399,4095],[0,1,3,4,5,12,15,64,68,76,85,127,128,129,132,133,384,387,396,399,2048,2112,2176,2244,2689,2773,6144,6208,6528,6604,8067,8191],[0,1,3,4,5,12,15,64,68,85,192,204,255,260,261,780,783,4160,4420,5461,12480,13260,16383],[0,1,2,3,8,10,15,128,136,170,255,258,259,1032,1290,1807,16512,17544,21930,32767],[0,1,3,15,255,65535]]
def shapeMoves : List (List Motion) := [[(442977830145,298653542145),(444682421505,444682421505),(590143103745,590143103745)],[(430997778720,430997778720),(650792743200,650792743200)],[(509360812320,509360812320)],[(4631459172640,4631459172640),(9322565620000,9322565620000)],[(111339169744656,111339169744656)],[(2665427388556368,1765586750314368),(2666086773449808,2666086773449808),(3566367001620768,3566367001620768)],[(444684632355,444684632355),(590143103745,590143103745),(509361786930,509361786930)],[(370585047090,370585047090),(590380011570,590380011570)],[(9322585395250,9322585395250)],[(76310993633571,76310993633571),(171018472002306,185514207813681),(204133175144736,204133175144736)],[(111339169744656,111339169744656)],[(80724237852711,144744848777586),(163509811433586,163509811433586),(94782055028481,94782055028481),(188606868308481,188606868308481)],[(3317946078413313,3317946078413313)],[(21464638507371,7873774200246),(201801825731841,201801825731841),(28966074479286,28966074479286),(204129163354881,204129163354881),(111339169744656,111339169744656)],[(3315618755593473,3315618755593473),(3317946093216513,3317946093216513),(3580536365929488,3580536365929488)],[(29030705309264641,29030705309264641),(57853739488462081,57853739488462081),(57890976857137921,57890976857137921),(62092421490693136,62092421490693136)],[(1065820089501180960,1057673610252144960),(528683754824902800,528683754824902800),(1066713786299461920,1066713786299461920)],[(14810444724202858275,7489281452709446025),(12158009240974353525,11208016698840078150),(16126998334132327170,17076990876266602545),(18152560703022715200,18282904370552071200),(18355225778678027280,18355225778678027280)]]
def rootsAt (i : ℕ) := (shapeRoots[i]?).getD []

def movesAt (i : ℕ) := (shapeMoves[i]?).getD []

def symmetryValid (i : ℕ) : Bool :=
  rootsOK (shapeAt i).pats (shapeAt i).paths.length (movesAt i) (rootsAt i)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem symmetry_valid : ∀ i : Fin 18, symmetryValid i.val = true := by decide +kernel

end MoonPrize.Trace

namespace MoonPrize.Trace

def orderedOK (g : Entry) (ord : List (List ℕ)) (i : ℕ) : Bool :=
  let vs := (ord[i]?).getD []
  ((g.moves >>> (8*i)) &&& 255 != 0) ||
    (vs.all (fun v => decide (v < g.n)) && !(orbitRun g (shapeAt i) (rootsAt i) vs))

theorem ordered_sound {g : Entry} (gv : listedOK g = true) (ord : List (List ℕ))
    (ok : (List.range 18).all (orderedOK g ord) = true) : LongClear g := by
  intro s hz
  have test := List.all_eq_true.mp ok s.val (List.mem_range.mpr s.isLt)
  unfold orderedOK at test
  change (g.moves >>> (8*s.val)) &&& 255 = 0 at hz
  simp [hz] at test
  exact orbit_excludes g (shapeAt s.val) (rootsAt s.val) _ (movesAt s.val) gv (documented_shapes s) (symmetry_valid s)
    test.1 test.2

def order10 : List (List ℕ) := [[],[],[],[],[],[3,4,7],[],[],[],[],[3,4,6,7],[],[2,4,7],[],[2,4,7],[2,7,4],[2,7,4],[2,7,4]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered10p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] : List ℕ).all (orderedOK E10 order10) = true := by decide +kernel
theorem basis10 (h : listedOK E10 = true) : LongClear E10 := by
  apply ordered_sound h order10
  exact ordered10p0
def order13 : List (List ℕ) := [[],[],[],[2,3,5],[2,3,4,6],[2,3,4,6],[],[],[2,3,5],[2,5,3],[2,3,4,5,6,7],[2,5,6,4],[2,5,3,4,0],[4,5,3,1,6],[3,1,2,4,6,7],[2,5,3,4,0],[2,5,0,3,4],[3,6,0,5,4]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered13p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13] : List ℕ).all (orderedOK E13 order13) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered13p14 : ([14,15] : List ℕ).all (orderedOK E13 order13) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered13p16 : ([16] : List ℕ).all (orderedOK E13 order13) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered13p17 : ([17] : List ℕ).all (orderedOK E13 order13) = true := by decide +kernel
theorem basis13 (h : listedOK E13 = true) : LongClear E13 := by
  apply ordered_sound h order13
  change (([0,1,2,3,4,5,6,7,8,9,10,11,12,13] : List ℕ) ++ ([14,15] : List ℕ) ++ ([16] : List ℕ) ++ ([17] : List ℕ)).all (orderedOK E13 order13) = true
  simp only [List.all_append,ordered13p0,ordered13p14,ordered13p16,ordered13p17,Bool.and_self]
def order21 : List (List ℕ) := [[],[],[],[4,5,7],[2,5,4,7],[2,5,4,7],[],[],[4,5,7],[4,5,7],[5,4,1,7,3,6],[4,5,7,3,6],[2,4,6,5,3,7,1],[4,5,6,7],[6,2,5,3,4,7],[2,4,6,5,3,7,1],[2,4,6,5,3,7,1],[4,6,3,5,7]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered21p0 : ([0,1,2,3,4,5,6,7,8,9] : List ℕ).all (orderedOK E21 order21) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered21p10 : ([10] : List ℕ).all (orderedOK E21 order21) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered21p11 : ([11] : List ℕ).all (orderedOK E21 order21) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered21p12 : ([12,13] : List ℕ).all (orderedOK E21 order21) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered21p14 : ([14] : List ℕ).all (orderedOK E21 order21) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered21p15 : ([15] : List ℕ).all (orderedOK E21 order21) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered21p16 : ([16] : List ℕ).all (orderedOK E21 order21) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered21p17 : ([17] : List ℕ).all (orderedOK E21 order21) = true := by decide +kernel
theorem basis21 (h : listedOK E21 = true) : LongClear E21 := by
  apply ordered_sound h order21
  change (([0,1,2,3,4,5,6,7,8,9] : List ℕ) ++ ([10] : List ℕ) ++ ([11] : List ℕ) ++ ([12,13] : List ℕ) ++ ([14] : List ℕ) ++ ([15] : List ℕ) ++ ([16] : List ℕ) ++ ([17] : List ℕ)).all (orderedOK E21 order21) = true
  simp only [List.all_append,ordered21p0,ordered21p10,ordered21p11,ordered21p12,ordered21p14,ordered21p15,ordered21p16,ordered21p17,Bool.and_self]
def order123 : List (List ℕ) := [[],[],[],[],[4,5,6],[4,6,5],[],[],[],[],[4,6,5],[4,6,5],[4,6,5],[4,6,5],[4,6,5],[4,6,5],[4,6,5],[4,6,5]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered123p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] : List ℕ).all (orderedOK E123 order123) = true := by decide +kernel
theorem basis123 (h : listedOK E123 = true) : LongClear E123 := by
  apply ordered_sound h order123
  exact ordered123p0
def order136 : List (List ℕ) := [[],[],[],[],[4,5,8],[4,5,8],[],[],[],[],[5,8,4],[5,4,8],[5,8,4],[],[5,8,4],[4,8,5],[4,8,5],[4,8,5]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered136p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] : List ℕ).all (orderedOK E136 order136) = true := by decide +kernel
theorem basis136 (h : listedOK E136 = true) : LongClear E136 := by
  apply ordered_sound h order136
  exact ordered136p0
def order139 : List (List ℕ) := [[],[],[],[],[4,5,8],[4,5,8],[],[],[],[],[4,5,8],[4,5,8],[4,5,8],[],[4,5,8],[4,5,8],[4,5,8],[4,5,8]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered139p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] : List ℕ).all (orderedOK E139 order139) = true := by decide +kernel
theorem basis139 (h : listedOK E139 = true) : LongClear E139 := by
  apply ordered_sound h order139
  exact ordered139p0
def order141 : List (List ℕ) := [[],[],[],[],[4,5,8],[4,5,8],[],[],[],[],[4,5,8],[4,5,8],[4,5,8],[4,5,8],[4,5,8],[4,5,8],[4,5,8],[4,5,8]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered141p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] : List ℕ).all (orderedOK E141 order141) = true := by decide +kernel
theorem basis141 (h : listedOK E141 = true) : LongClear E141 := by
  apply ordered_sound h order141
  exact ordered141p0
def order176 : List (List ℕ) := [[],[],[],[5,6,8],[4,8,5,6],[4,5,6,8],[],[],[5,6,8],[5,6,8],[4,5,6,7],[4,5,8],[4,5,6,7],[5,6,7,8],[4,5,6,7],[4,5,6,7],[4,6,5,8],[4,8,6,5]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered176p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12] : List ℕ).all (orderedOK E176 order176) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered176p13 : ([13,14,15] : List ℕ).all (orderedOK E176 order176) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered176p16 : ([16] : List ℕ).all (orderedOK E176 order176) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered176p17 : ([17] : List ℕ).all (orderedOK E176 order176) = true := by decide +kernel
theorem basis176 (h : listedOK E176 = true) : LongClear E176 := by
  apply ordered_sound h order176
  change (([0,1,2,3,4,5,6,7,8,9,10,11,12] : List ℕ) ++ ([13,14,15] : List ℕ) ++ ([16] : List ℕ) ++ ([17] : List ℕ)).all (orderedOK E176 order176) = true
  simp only [List.all_append,ordered176p0,ordered176p13,ordered176p16,ordered176p17,Bool.and_self]
def order181 : List (List ℕ) := [[],[],[],[4,5,7],[3,4,8],[3,8,4],[],[],[4,5,7],[4,5,7],[3,8,4],[3,8,4],[3,8,4],[4,5,6,7],[3,8,4],[4,8,3],[4,8,3],[5,4,7,6,8]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered181p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : List ℕ).all (orderedOK E181 order181) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered181p16 : ([16] : List ℕ).all (orderedOK E181 order181) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered181p17 : ([17] : List ℕ).all (orderedOK E181 order181) = true := by decide +kernel
theorem basis181 (h : listedOK E181 = true) : LongClear E181 := by
  apply ordered_sound h order181
  change (([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : List ℕ) ++ ([16] : List ℕ) ++ ([17] : List ℕ)).all (orderedOK E181 order181) = true
  simp only [List.all_append,ordered181p0,ordered181p16,ordered181p17,Bool.and_self]
def order182 : List (List ℕ) := [[],[],[],[],[4,3,8],[4,3,8],[],[],[],[],[4,3,8],[4,3,8],[4,3,8],[4,5,6,7],[4,3,8],[4,3,8],[4,3,8],[5,4,7,6,8]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered182p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] : List ℕ).all (orderedOK E182 order182) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered182p17 : ([17] : List ℕ).all (orderedOK E182 order182) = true := by decide +kernel
theorem basis182 (h : listedOK E182 = true) : LongClear E182 := by
  apply ordered_sound h order182
  change (([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] : List ℕ) ++ ([17] : List ℕ)).all (orderedOK E182 order182) = true
  simp only [List.all_append,ordered182p0,ordered182p17,Bool.and_self]
def order183 : List (List ℕ) := [[],[],[],[],[4,3,8],[4,3,8],[],[],[],[],[4,3,8],[4,3,8],[4,3,8],[4,5,6,7],[4,3,8],[4,3,8],[4,3,8],[5,4,7,6,8]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered183p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] : List ℕ).all (orderedOK E183 order183) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered183p17 : ([17] : List ℕ).all (orderedOK E183 order183) = true := by decide +kernel
theorem basis183 (h : listedOK E183 = true) : LongClear E183 := by
  apply ordered_sound h order183
  change (([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] : List ℕ) ++ ([17] : List ℕ)).all (orderedOK E183 order183) = true
  simp only [List.all_append,ordered183p0,ordered183p17,Bool.and_self]
def order185 : List (List ℕ) := [[],[],[],[],[4,5,8],[4,5,8],[],[],[],[],[4,5,8],[4,5,8],[4,5,8],[4,5,8],[4,5,8],[4,5,8],[4,5,8],[4,5,8]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered185p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : List ℕ).all (orderedOK E185 order185) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered185p16 : ([16,17] : List ℕ).all (orderedOK E185 order185) = true := by decide +kernel
theorem basis185 (h : listedOK E185 = true) : LongClear E185 := by
  apply ordered_sound h order185
  change (([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : List ℕ) ++ ([16,17] : List ℕ)).all (orderedOK E185 order185) = true
  simp only [List.all_append,ordered185p0,ordered185p16,Bool.and_self]
def order196 : List (List ℕ) := [[],[],[],[],[],[3,7,6],[],[],[],[],[7,3,6,5,8],[],[7,3,6,8,5],[],[3,6,7,8,5],[3,6,7,8,5],[3,6,7,8,5],[3,6,7]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered196p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] : List ℕ).all (orderedOK E196 order196) = true := by decide +kernel
theorem basis196 (h : listedOK E196 = true) : LongClear E196 := by
  apply ordered_sound h order196
  exact ordered196p0
def order202 : List (List ℕ) := [[],[],[],[4,6,8],[4,5,7,8,6],[4,5,7,8,6],[],[],[4,6,8],[4,6,8],[4,5,7,8,6],[4,5,7,8,6],[6,3,4,8,5,7],[4,6,7,8],[4,5,6,7,8],[4,5,7,8,6],[4,5,6,7,8],[4,5,7,8,6]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered202p0 : ([0,1,2,3,4] : List ℕ).all (orderedOK E202 order202) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered202p5 : ([5] : List ℕ).all (orderedOK E202 order202) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered202p6 : ([6,7,8,9,10] : List ℕ).all (orderedOK E202 order202) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered202p11 : ([11] : List ℕ).all (orderedOK E202 order202) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered202p12 : ([12,13] : List ℕ).all (orderedOK E202 order202) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered202p14 : ([14] : List ℕ).all (orderedOK E202 order202) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered202p15 : ([15] : List ℕ).all (orderedOK E202 order202) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered202p16 : ([16] : List ℕ).all (orderedOK E202 order202) = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered202p17 : ([17] : List ℕ).all (orderedOK E202 order202) = true := by decide +kernel
theorem basis202 (h : listedOK E202 = true) : LongClear E202 := by
  apply ordered_sound h order202
  change (([0,1,2,3,4] : List ℕ) ++ ([5] : List ℕ) ++ ([6,7,8,9,10] : List ℕ) ++ ([11] : List ℕ) ++ ([12,13] : List ℕ) ++ ([14] : List ℕ) ++ ([15] : List ℕ) ++ ([16] : List ℕ) ++ ([17] : List ℕ)).all (orderedOK E202 order202) = true
  simp only [List.all_append,ordered202p0,ordered202p5,ordered202p6,ordered202p11,ordered202p12,ordered202p14,ordered202p15,ordered202p16,ordered202p17,Bool.and_self]
def order203 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[8,5,2,3,6],[],[],[8,5,2,3,6],[8,5,2,3,6],[3,6,5]]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem ordered203p0 : ([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] : List ℕ).all (orderedOK E203 order203) = true := by decide +kernel
theorem basis203 (h : listedOK E203 = true) : LongClear E203 := by
  apply ordered_sound h order203
  exact ordered203p0

theorem ledger_parts {g : Entry} (h : ledgerOK g = true) :
    listedOK g = true ∧ (∀ s : Fin 18, certified g (shapeAt s.val) s.val = true) ∧
    (noHard g = true ∨ g ∈ harder) := by
  obtain ⟨first,last⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨v,all⟩ := Bool.and_eq_true_iff.mp first
  exact ⟨v, fun s => List.all_eq_true.mp all _ (List.mem_range.mpr s.isLt),
    (Bool.or_eq_true_iff.mp last).imp_right List.contains_iff_mem.mp⟩

theorem checkedHard {g : Entry} (gv : listedOK g = true) (inside : g ∈ harder) : LongClear g := by
  simp only [harder,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact basis10 gv
  · exact basis13 gv
  · exact basis21 gv
  · exact basis123 gv
  · exact basis136 gv
  · exact basis139 gv
  · exact basis141 gv
  · exact basis176 gv
  · exact basis181 gv
  · exact basis182 gv
  · exact basis183 gv
  · exact basis185 gv
  · exact basis196 gv
  · exact basis202 gv
  · exact basis203 gv

theorem all_listed (g : Entry) (mem : g ∈ entries) (paths : List ℕ)
    (hc : paths.length < 10 ∨ ∃ s : Fin 18, (shapeAt s.val).paths = paths) :
    ¬ Embeds g.rows paths g.n := by
  obtain ⟨gv,checks,other⟩ := ledger_parts (entries_valid mem)
  obtain short | ⟨s,rfl⟩ := hc
  · intro embed
    obtain ⟨ten,nd,bounds,_⟩ := entry_rows gv
    have len := embeddings_card nd bounds embed
    omega
  · by_cases hz : HardSlots g s.val
    · rcases other with small | difficult
      · have cmp := List.all_eq_true.mp small s.val (List.mem_range.mpr s.isLt)
        simp only [HardSlots] at hz
        simp [hz] at cmp
      · exact checkedHard gv difficult s hz
    · exact short_sound _ _ _ gv (documented_shapes s) (checks s) hz

end MoonPrize.Trace

namespace MoonPrize.CatalogueData

open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
def coverPerms : List ℕ := [18056,14472,17608,10440,13576,9992,18000,14416,17104,6352,13072,5904,17496,10328,17048,6296,8984,5400,13408,9824,12960,5792,8928,5344,18049,14465,17601,10433,13569,9985,17937,14353,16593,2257,12561,1809,17433,10265,16537,2201,8473,1305,13345,9761,12449,1697,8417,1249,17986,14402,17090,6338,13058,5890,17930,14346,16586,2250,12554,1802,16922,6170,16474,2138,4378,794,12834,5666,12386,1634,4322,738,17475,10307,17027,6275,8963,5379,17419,10251,16523,2187,8459,1291,16915,6163,16467,2131,4371,787,8739,5155,8291,1123,4259,675,13380,9796,12932,5764,8900,5316,13324,9740,12428,1676,8396,1228,12820,5652,12372,1620,4308,724,8732,5148,8284,1116,4252,668]
def canonCodes : List ℕ := [18056,18056,18000,18056,17496,17608,17104,18056,13408,13576,13072,14472,8984,10440,6352,18056,17937,18049,17986,18056,18056,18056,18000,18056,14472,14472,14416,14472,18056,18056,18000,18056,17433,17601,17608,17608,17475,17608,17496,17608,10440,10440,17608,17608,10328,10440,17496,17608,16593,18049,17937,18049,17433,17601,0,0,13569,13569,18056,18056,17608,17608,0,0,13345,13569,13576,13576,9992,9992,13576,13576,13380,13576,13408,13576,9824,9992,13408,13576,12561,14465,14353,14465,17601,17601,14472,14472,13345,13569,0,0,13576,13576,0,0,8473,10433,18049,18049,10265,10433,10440,10440,9761,9985,9992,9992,0,0,0,0,2257,18049,17937,18049,17433,17601,0,0,13345,13569,0,0,0,0,0,0,16922,17104,17090,17104,17027,17048,17104,17104,6352,17104,6352,17104,6296,17048,6352,17104,16586,16593,17986,17986,16922,0,17090,0,13058,18000,13058,18000,17104,0,17104,0,16523,16537,16474,0,17475,17475,17027,0,8963,17496,17048,0,8963,17496,17048,0,16593,16593,16586,0,16523,0,0,0,18056,18056,18000,0,17496,0,0,0,2257,16593,12554,17937,8459,17433,18049,18049,4308,14402,12834,14402,8739,10307,5764,18056,2257,16593,12554,17937,16537,0,17937,0,12386,14346,0,0,18056,0,0,0,2201,16537,16593,0,8459,17433,17433,0,8291,10251,17608,0,0,0,0,0,2257,16593,16593,0,16537,0,0,0,1676,18049,0,0,0,0,0,0,12834,13072,13058,13072,5904,13072,5904,13072,12932,12960,13072,13072,5792,12960,5904,13072,12554,12561,14402,14402,17090,14416,17090,14416,12834,0,13058,0,13072,0,13072,0,1809,12561,16586,14353,4371,17986,16922,17986,8396,13345,14465,14465,5155,9796,6275,14472,1809,12561,16586,14353,16474,17930,0,0,12449,0,14353,0,14472,0,0,0,12428,12449,12386,0,8900,13408,12960,0,13380,13380,12932,0,8900,13408,12960,0,12561,12561,12554,0,14472,14472,14416,0,12428,0,0,0,13408,0,0,0,1697,12449,12561,0,1123,9740,13576,0,8396,13345,13345,0,0,0,0,0,1809,12561,12561,0,2187,14465,0,0,12449,0,0,0,0,0,0,0,4378,17986,6338,17986,6170,6352,6338,6352,5666,5904,5890,5904,0,0,0,0,2250,17930,17986,17986,16922,0,17090,0,12834,0,13058,0,0,0,0,0,2138,2257,16474,0,4371,16922,16922,0,4259,17104,6163,0,0,0,0,0,2250,2257,16586,0,16474,0,0,0,1620,0,17986,0,0,0,0,0,1634,1809,12386,0,675,13072,5652,0,4308,12834,12834,0,0,0,0,0,1802,1809,12554,0,2131,0,14402,0,12386,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8739,8984,5400,8984,8963,8984,5400,8984,8900,8928,5344,8928,8984,8984,5400,8984,1305,8473,4378,17475,16523,10265,6170,17475,12428,9761,5666,13380,10433,10433,6338,10440,8459,8473,17027,10328,10307,10307,17027,10328,8739,0,8984,0,8963,0,8984,0,1305,8473,2138,17419,16523,10265,0,0,8417,0,10440,0,10265,0,0,0,8396,8417,12932,9824,8291,0,8928,0,9796,9796,12932,9824,8900,0,8928,0,1249,8417,1634,13324,8473,0,9992,0,12428,9761,0,0,9761,0,0,0,8473,8473,10440,10440,8459,0,10328,0,8396,0,9824,0,0,0,0,0,1305,8473,2250,10433,8473,0,0,0,8417,0,0,0,0,0,0,0,4371,17475,4378,6296,6275,17475,6275,6296,5155,5400,0,0,5379,5400,0,0,794,2201,4378,16915,16467,0,6170,0,4322,6352,0,0,6170,0,0,0,2187,17419,16915,0,17475,17475,17027,0,8739,0,0,0,8963,0,0,0,2187,2201,2138,0,16523,0,0,0,1116,0,0,0,17475,0,0,0,1123,1305,738,8984,8291,0,5148,0,4252,8739,0,0,8739,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1291,1305,2138,0,8459,0,10307,0,8291,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4308,13380,4322,5792,4259,5344,0,0,5764,13380,5764,5792,5316,5344,0,0,738,1697,4322,12820,4378,5904,0,0,12372,0,5666,0,5666,0,0,0,675,1249,794,5400,4259,8732,0,0,8284,0,5155,0,5155,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1676,13324,12820,0,8732,0,0,0,13380,13380,12932,0,8900,0,0,0,1676,1697,1634,0,1123,0,0,0,12428,0,0,0,13380,0,0,0,1228,1249,1634,0,1123,0,0,0,8396,0,9796,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4378,6352,4378,6352,4371,6296,0,0,4308,5792,0,0,0,0,0,0,794,2257,4378,6338,4378,0,0,0,4322,0,0,0,0,0,0,0,787,2201,794,0,4371,6275,0,0,4259,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,724,1697,738,0,675,0,0,0,4308,5764,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def D0 : FData := ⟨0,120,16384,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[18056,14472,17608,10440,13576,9992,18000,14416,17104,6352,13072,5904,17496,10328,17048,6296,8984,5400,13408,9824,12960,5792,8928,5344,18049,14465,17601,10433,13569,9985,17937,14353,16593,2257,12561,1809,17433,10265,16537,2201,8473,1305,13345,9761,12449,1697,8417,1249,17986,14402,17090,6338,13058,5890,17930,14346,16586,2250,12554,1802,16922,6170,16474,2138,4378,794,12834,5666,12386,1634,4322,738,17475,10307,17027,6275,8963,5379,17419,10251,16523,2187,8459,1291,16915,6163,16467,2131,4371,787,8739,5155,8291,1123,4259,675,13380,9796,12932,5764,8900,5316,13324,9740,12428,1676,8396,1228,12820,5652,12372,1620,4308,724,8732,5148,8284,1116,4252,668],[⟨204,[1,2,4,8,16],[5,6,7,8,9,0,1,2,3,4]⟩,⟨205,[1,2,4,8,17],[9,6,7,8,5,4,1,2,3,0]⟩,⟨206,[1,2,4,8,19],[0,1,7,8,4,5,6,2,3,9]⟩,⟨207,[1,2,4,8,23],[0,1,2,8,4,5,6,7,3,9]⟩,⟨208,[1,2,4,8,31],[0,1,2,3,4,5,6,7,8,9]⟩,⟨206,[1,2,4,9,17],[9,7,8,5,6,4,2,3,0,1]⟩,⟨209,[1,2,4,9,18],[8,9,7,5,6,3,4,2,0,1]⟩,⟨210,[1,2,4,9,19],[9,8,7,6,5,4,3,2,1,0]⟩,⟨211,[1,2,4,9,22],[8,1,2,5,4,3,6,7,0,9]⟩,⟨212,[1,2,4,9,23],[0,1,2,3,4,5,6,7,8,9]⟩,⟨225,[1,2,4,9,24],[8,6,7,9,5,4,1,2,3,0]⟩,⟨213,[1,2,4,9,26],[0,1,7,3,4,5,6,2,8,9]⟩,⟨214,[1,2,4,9,30],[0,1,2,3,4,5,6,7,8,9]⟩,⟨229,[1,2,4,11,21],[9,7,8,5,6,4,2,3,0,1]⟩,⟨226,[1,2,4,11,24],[0,1,7,3,4,5,6,2,9,8]⟩,⟨228,[1,2,4,11,28],[1,2,0,3,4,6,7,5,9,8]⟩,⟨227,[1,2,4,15,24],[0,1,2,3,4,5,6,7,9,8]⟩,⟨207,[1,2,5,9,17],[9,8,5,6,7,4,3,0,1,2]⟩,⟨211,[1,2,5,9,18],[9,8,6,7,5,4,3,1,2,0]⟩,⟨212,[1,2,5,9,19],[9,8,6,7,5,4,3,1,2,0]⟩,⟨213,[1,2,5,9,20],[9,7,8,6,5,4,2,3,1,0]⟩,⟨218,[1,2,5,9,22],[9,1,0,7,3,4,6,5,2,8]⟩,⟨220,[1,2,5,9,28],[9,7,0,1,3,4,2,5,6,8]⟩,⟨221,[1,2,5,9,30],[8,2,5,6,4,3,7,0,1,9]⟩,⟨229,[1,2,5,10,19],[0,1,2,3,4,5,6,7,8,9]⟩,⟨252,[1,2,5,10,20],[8,7,9,5,6,4,2,3,0,1]⟩,⟨237,[1,2,5,10,22],[8,9,7,6,5,3,4,2,1,0]⟩,⟨230,[1,2,5,10,28],[0,1,2,3,4,5,6,7,8,9]⟩,⟨237,[1,2,5,11,20],[0,1,2,4,3,5,6,7,9,8]⟩,⟨244,[1,2,5,11,22],[8,9,7,6,5,3,4,2,1,0]⟩,⟨253,[1,2,5,11,24],[0,1,2,3,4,5,6,7,9,8]⟩,⟨257,[1,2,5,11,28],[0,1,2,3,4,5,6,7,9,8]⟩,⟨226,[1,2,5,12,20],[8,7,9,5,6,4,2,3,0,1]⟩,⟨253,[1,2,5,12,22],[8,7,9,6,5,4,2,3,1,0]⟩,⟨263,[1,2,5,12,24],[8,6,7,9,5,4,1,2,3,0]⟩,⟨238,[1,2,5,12,25],[9,6,8,7,5,4,1,3,2,0]⟩,⟨239,[1,2,5,12,26],[0,1,2,3,4,5,6,7,8,9]⟩,⟨240,[1,2,5,12,27],[0,1,2,3,4,5,6,7,8,9]⟩,⟨254,[1,2,5,14,24],[0,1,2,3,4,5,6,7,9,8]⟩,⟨258,[1,2,5,14,25],[9,1,0,2,3,4,6,5,8,7]⟩,⟨262,[1,2,7,12,20],[7,8,9,5,6,3,4,2,0,1]⟩,⟨264,[1,2,7,12,24],[0,1,3,2,4,5,6,9,7,8]⟩,⟨269,[1,2,7,12,25],[9,8,7,6,5,4,3,2,1,0]⟩,⟨265,[1,2,12,20,24],[5,6,7,8,9,0,1,2,3,4]⟩,⟨266,[1,2,12,20,25],[0,6,2,3,4,5,1,7,8,9]⟩,⟨267,[1,2,12,20,27],[0,1,2,3,4,5,6,7,8,9]⟩,⟨268,[1,2,12,21,26],[0,1,2,3,4,5,6,7,8,9]⟩,⟨208,[1,3,5,9,17],[9,5,6,7,8,4,0,1,2,3]⟩,⟨214,[1,3,5,9,18],[9,8,6,7,5,4,3,1,2,0]⟩,⟨221,[1,3,5,9,22],[9,0,1,7,3,4,5,6,2,8]⟩,⟨224,[1,3,5,9,30],[9,0,1,2,3,4,5,6,7,8]⟩,⟨228,[1,3,5,10,18],[8,9,5,6,7,4,3,0,1,2]⟩,⟨230,[1,3,5,10,20],[9,7,8,5,6,4,2,3,0,1]⟩,⟨257,[1,3,5,10,22],[8,9,7,6,5,4,3,2,1,0]⟩,⟨239,[1,3,5,10,24],[9,8,6,7,5,4,3,1,2,0]⟩,⟨240,[1,3,5,10,25],[9,8,6,7,5,4,3,1,2,0]⟩,⟨246,[1,3,5,10,28],[9,0,1,2,3,4,5,6,7,8]⟩,⟨261,[1,3,5,14,24],[8,5,6,2,3,4,0,1,9,7]⟩,⟨260,[1,3,5,14,25],[9,0,1,2,3,4,5,6,8,7]⟩,⟨227,[1,3,6,10,18],[8,9,5,6,7,4,3,0,1,2]⟩,⟨254,[1,3,6,10,20],[8,9,7,6,5,4,3,2,1,0]⟩,⟨258,[1,3,6,10,21],[7,8,5,6,4,3,2,0,1,9]⟩,⟨261,[1,3,6,10,28],[7,9,0,1,4,3,2,5,6,8]⟩,⟨260,[1,3,6,10,29],[7,8,5,6,4,3,2,0,1,9]⟩,⟨264,[1,3,6,12,20],[8,7,9,5,6,4,2,3,0,1]⟩,⟨269,[1,3,6,12,21],[0,1,2,3,4,5,6,7,8,9]⟩,⟨288,[1,3,6,12,24],[8,6,7,9,5,4,2,1,3,0]⟩,⟨270,[1,3,6,12,25],[9,8,7,6,5,4,3,2,1,0]⟩,⟨274,[1,3,6,12,26],[8,9,7,6,5,4,3,2,1,0]⟩,⟨274,[1,3,6,13,24],[0,1,2,3,4,5,6,7,9,8]⟩,⟨293,[1,3,6,13,26],[6,9,0,3,4,2,1,5,8,7]⟩,⟨282,[1,3,12,20,24],[8,5,6,7,9,4,0,1,2,3]⟩,⟨283,[1,3,12,20,25],[0,4,1,2,3,5,8,6,7,9]⟩,⟨284,[1,3,12,20,26],[0,4,1,2,3,5,8,6,7,9]⟩,⟨281,[1,3,12,21,26],[9,0,1,3,2,4,5,7,6,8]⟩,⟨266,[1,6,10,12,18],[6,9,7,8,5,1,3,4,2,0]⟩,⟨283,[1,6,10,12,19],[8,9,6,7,5,4,2,3,1,0]⟩,⟨297,[1,6,10,13,18],[2,9,0,1,7,6,4,5,8,3]⟩,⟨279,[1,6,10,13,19],[9,8,6,7,5,4,2,3,1,0]⟩,⟨289,[1,6,10,13,20],[8,7,9,6,5,4,3,1,2,0]⟩,⟨298,[1,6,10,18,28],[7,9,0,1,2,3,4,5,6,8]⟩,⟨299,[1,6,10,18,29],[3,8,4,5,6,7,0,1,2,9]⟩,⟨302,[1,6,10,19,28],[0,9,1,2,3,4,5,6,7,8]⟩,⟨290,[1,6,10,20,24],[5,6,7,8,9,0,1,2,3,4]⟩,⟨291,[1,6,10,20,25],[0,1,2,3,4,5,6,7,8,9]⟩,⟨294,[1,6,11,21,24],[9,5,6,7,8,4,0,1,2,3]⟩,⟨267,[3,5,6,9,17],[9,7,8,5,6,3,4,2,0,1]⟩,⟨268,[3,5,6,9,18],[8,9,7,5,6,4,2,3,0,1]⟩,⟨284,[3,5,6,9,24],[9,6,7,8,5,2,3,1,4,0]⟩,⟨281,[3,5,6,9,26],[8,6,7,5,4,2,3,1,0,9]⟩,⟨299,[3,5,9,14,17],[9,0,1,2,7,4,5,6,8,3]⟩,⟨302,[3,5,9,14,18],[8,7,5,6,4,3,1,2,9,0]⟩,⟨300,[3,5,9,17,30],[9,0,1,2,3,4,5,6,7,8]⟩,⟨291,[3,5,9,18,20],[9,7,8,5,6,3,4,0,1,2]⟩,⟨301,[3,5,9,18,28],[9,0,1,2,3,4,5,6,7,8]⟩,⟨294,[3,5,10,12,22],[0,1,2,3,4,5,6,7,8,9]⟩,⟨295,[3,5,10,20,24],[5,6,7,8,9,0,1,2,3,4]⟩,⟨296,[3,5,10,20,25],[9,7,8,5,6,3,4,1,2,0]⟩,⟨303,[3,5,10,22,25],[0,9,2,1,3,4,6,5,7,8]⟩],0x1668ae017d95f4d7d15f42a996e85b9b6e657685d89760aa4dba05da5b956e4d75c5d6a8c068f5a3768eda355bc96ecaa45b9a5d8db945d75b915d62e4fa8bee4ea8bab1ab1f2147851994d8c65aaf652e3136ab5b19a2e9a3f68c5a3a5bcda2f5b9ae4da8b6e4cac6ea2cb1da145653e1448c7daa9652a3116c6daa7a85ea15b2c6b05a49e925b001dfd9415d0f7ba5d0d7f65ee37f4d85a88919bd66de8b468f9a3c5bd5a2b68a56e0b92ee4aac76a2ba8aac70850d94e850a31d65323176c85aa36a86a16ac0e926a84ec99a48ebfa77edd0e940dee8742dfd8617222a66fdedd7f359b1ac0aa14a492a12a48ac98afe1dfa7431d0a617a50288c1ee27f499b97b71fcc66ceb68aa06a7ba2a2a79b1928a2b17abe8a272c58af8abe0706a66a923648b79c248a79a9e64700895d256c95a21a9de5778dde29948b3d2cecb3a84be12d93b5cf673d247538392bf38312bd2938a4c84b9cf784ae4eb73ca473383d2be293ce0a4aeca4a64dded164d9ed06119e5837d8df72e7cc8f2e78c8e238a12c73d612a73ce4ea91c8e0d4af0a4d382d2ba292db896e21a278c1dfc1689a3057f022184a9d2a63294ca364d5ecb64d18447b29e5237d0b9d37d4c8d2e70c8c238db836895b828c05fbb68922ff8849fba4a94ca74a90ca25f05b815d45a1f5d2da976865a915b75b09669d9a12514b2528dca35233593364c98427b15ec47930df22e6cdf3322cb9a32288e56df5a236df22fb688a2f98831fb57ed12a332992a232917bb5d41b7b68757456a556db6c0d9a5684da8b666c9432c8ca3628cc8cb5ee574a5d116da6de5b01685da8f667da116a259992508b2228d0a3223296505ee17485d096d45d016ce5b20852aa41b985d85b925d6db905d66e37a8a6e36a8a2c82ac52141850231b6ad59478c55ab36515b18b87ea23b20ee1ea88ab0e8c85ab784ee13a65063146ac9b1a64fee31a846e19a82ecd9b1b6db9b6866e57616051812e29cb216e07a876e06a872b088c81ab68c69ab46c8213584d193b64e6e30a842c6bb6e2e01a816cd3b6266e3760e0508a8a045b1aae18a82ada0b802a04b622cd19b89d828aa204a8112a78abf2af6abc25f29b35d6d9b2dd6b9b29d6a9768eff3bf8efd3bf0ac53becefa2b0cac284a61288c25a9f80e63086a7a0388a40ee73b98d07341a3036a76123848a0338c09a9c8a2a0323b94ee43414d046e0174964bd9296c20aad8bf5a9b8bf1a9a8a1211d847202d80b0ee33b88d033409b7a5d0d92d6c099232aadb785d05b00649d9212aaa8b868e5a3368d16ed68b96e7b8d6a27b8d2b15b1dea2684fd9498c9613e6aae3106c759446a9a9ffb2ae9fdabb690fb00a90d93fdeef77ddd097f7dd077f45ee188899c361519b6b876a21b1f6e1cac3ea208c9dab184e594384e23126c71aac64fae2fa7e6cc1b84e9f3b746c55b66e0579b7dd7f812629ab30e9e7a796c08ab568f7a3d5fdd7f5e4f97bb5ee777c5d03740622067099bc613aca9b85ee11a7869dbb72edb3b0f6055813e6d975e6298a83e9f7a8269f1a77e9d9a646979a586415903e40986a2de9b78e9a9b76e9a5b7669a4a6a283d832e0c7634683c832a0c683058cb83020bd82f18c36306e2eabf6ae7a426c65b13ebf0b6c697bb70e98daf66d1195e5c9695f9c919f45f597d56c5fafaae16abded99ab3e8f1b0de963b70698cb442bc195cdc949f2df5f95f1c8b7d528a0a83a907a8228efa64239d80fe03d8ff656171fa55b71f238550951cf3659427437d1cd36510dd3a0ce8227589d4939ded78c3e6c77f163f7a0960b3959a7b35034fef57bd155490e12764c5ddf73c5a99759dfbf80de0af62e5c797d1d1b735f8fd744fcc168c35fc79385ed59b063f1a0920b29ee6564503d5ed455cfed4909a218499cef7b3e0ae431da937ee612164ae0317765ceb75860a962cdf4171cd1b535f113d3f54c14686dec98481ce982a10c58be1b0588299ab8be9b048a0a20866aa28086420a58291f3d7cf0e6b39a922b30b922a30b1a1c5b5592c60f1a9466918ab26f9a165b3da8e667992660d98a926f28b268e1a365bbda2d68a16e1b8cee32ac5ea25b1c6a2484f59488c8e13c8c59b236519aa56a829feabae90eb24e9fbaff290b93f5eee77d5d087f79d0588a19c56159fcb7b6d9b0b1fee05a86ee04ac26a1a8c99ab08c61b226aba13364f613264e2e2da7e2dd0b14ecbbb7ee9edb60e0569b75d7d8a82043b7a2de1a6aeddda68edd8a6aa9a2a0ee0cd83158d0a0ea0cc83120c383098c982ed8c582e98c0b8b2affab96908b19ec4db726993af62bf1b6ae975b42e578725e57f72427d07d6df53b2f6c09a73e9cdaaf68dfa375fdb7f564f37badee588999c466f9deb73f5cfb6122c91b7fedf9b716dada7269c3b09605381366d38a79d73a8369f5a80e9eba62e973a71e9c1a526413903640386bac59af92dfeabc6d81b702992b426ab7a366c1fa52eba995b5c929f15f5d95e9f5a721689aa832905a80a98aa35e39b80fa56071fe03b8fee55571ea383508d1ce365d4264378e853a109d7472cd92436c9d29395ed68c3a6c5a08e0b5959dfc38fd67ad502cfee57b9245454e12564c1ddd73c1a9875960ad62e1c787ef60357d151b635fcfd644f8c178c2dfc6a08a0b49ee24db7b4e6bb8fae56250395eb45592443fada208491ced82b1ecd431a2fe6c2e21066b63006c2a28882ae0aa7d0e20e66b22868659f4239b4e6c48b4c2f48b0c2a68796d764b983e6a598b166989bf6a35fb3846d92580ae0a362b5f3b774dce5756dc6d46ccd7a44ecfd33049a157b0e11a8289ce3430da105b25a88666192062a183026eaaeaa7f290ca7ea90ab24abf977d1d06741185893f22367b81fd066ededa7f299b5ad42a69a98e890b132a61b11abd0a22ac40af2a884af22664921e48579d9c149211e68798ac52b84ad9aa7cadfab60a9ecb2e66dc8ab9d7c8122042ab92a60ab7aad897b2c47af4ae10b662adfab26c31a5a68ebb6a6d0aa5d2bbb95c67c97d95c8e95d9c897d4a9f6a41a888a7c28e9a5e2397b106bccb7e2d80ab66da8b42297aaac6c19a5468d3ae8e56b9f0df6372325747d61c83a7d2904a20a9eaa5ca8d18e56c90af86bc9b2e2bb9ae8674b993246f91b5e5e9b1229697525599ec5f4d8dfe5539eadf4b8df67334c795764e553933dd951641950637771cee73b18406ff1d6471d9c743d7a4e4887a46c957a55c53f9ec87ee19a3794203071c5f404135ec27ec999d792a02a7ce9c6b412dbea255c95525508647735dcb98e9dca2cdcb352cd21179356115737a45d7370e084ae52b73818a48291a116737e4d3844e45b7368e094ae0a494ad4e042911eb9647deb86479e4060b8ddf3778c772e1cc762e188dc9ad5d559acdd539aca5c27548ef93be0ef72afcef63bd4abd3bd0abc844611080862f16a1e0208bc1a8689e0ecf3b38cef33ba0278f960259525c66950e36d71911c9507cd9050850d9471d0d73638e7d2740e7c273a4cf7afe6af8bde3df7eb654ea03609b9e6cfe94fd55d7453d23d771e10f7365919753da81807dfa771860976285f2f3efd19f35991272ffa0269521c678f8e02394f636b71891c8364541d50810d839fc9d139f91c54354d8c27324cd7afa6ad8bda54fa02e09d8f75fab9e54fe84fcd5d648fd14d7715cd884359187535a807182095628201d7e95f2d3ef919e359d1262ffe634915e455791a6ac96f227e95063679e65f3594ee3659e4df339c6d3063dc155e4df537b544105f4175be47711cd673518287531c5e7170f463f44fb93f40fb84c00f583d006891a204a90efc3b912a03be0ee02c846c519946c119855606111840df13764ee13b254074fbcd79358537719c46591d2443037c0dd83b80ec835e0d6050153ed4dd4670196074810c52a14a8140943055d1448540843015d044814f81d3c74e167c59e2c7d29f28c4c713b7caa733a51af42fd137399c9b9489cbf9411c4910e9c5f910645870cbc93f37b8b813b78d7639983a12c74a304a74c703b74aa533a0e6526e12252fe11ad42f513541144900e985f810605860cb893d37b0b803b70e6435d03a024f084c2c70a2e28b08c42a909b626d02b08451cdd8449cdb934a45a381d2b6291ce054ad0a456dc5b708bbdfa9683e2ed7ea1a0e880128f4a38c9f32762f57ebe4c99aa63d97af680c9e8609a95313f757551513f9d23c8439cd76825eb782590af8bcdfaea02a7a082724c39a8e3d37aee54a4fd95d3454123e3f9610c7355a088251eb542ba4cc9152206951a54453992894a213f1573d13942a53f0573513842a14e01d9c766166459837bd29e28bcc873f3d2261604ded4a70a2d32152243f345806475eb3647182c7ac9e3a3770b853774c752e10c742375b6b68362e96da9fa38b9e1fa6831fa24a34ca14a30c9c6da5a075ea573969fd73369e5a016bc598f5b159892c34a1f24b4a1d22d62eb6a1610b806e10a8baa2726a1201a3b34ced3b30cec645db685cc59116bc0a957e85a7b8426019644ddc17525cd38245f29626dc5b46751253590fbd2ff1eb1680e108734609042b62e687e1af366562e889c1af2824df2b824a1f689ba17e6651f2a395521530a4e544850c24645982668196bf69f989966389a77ac1e387e8198b8061c597ca10354a1cc892c1ca193b1cce72a3d197447d0a7393d20f30449a140bc47917844010e3c56f0c5cdd62dfc9273b18d5e3938389375cc6f4a18a173edd20e15a4b7e31b88c532108af3398bf63030311646d91a60a9ead7ab1e343768b83376cc732e08c72237db65682e2e36d922e187d1a0a7e75f9c4a2cca04a28c9e6d8da055e8d73869f572d6bad98d5b0da7367ed9832c2ca1e24aca1b22ce2e56a0e2e489b1a82841601584120143b2cceb3b28cea6455b625cadaea642ca938b821f26bb59938b8a26a6bb21f089a2178664a08d7c9608c7c90e53484cc28394921230999146091a045af5a7c66318932699f9b69d6103804d90d822df236255dbb750dccd715519b448cd623eecbfa7aad9fd840a08a732d0ab7aa9e327e699858049f22714d0334a14c882c14a183b14ce52a34e4d4834c10268119544750a540b447817804000e3856e0c58dd42df49253b10e4c35703883754c6d4a10a154830fb515a0b7c31b08c732188ad3390c0e2fd03105e857325cb16c26d85ae967fda77661d9f969c598124a8b0a2870a1a22c97a05cc172a5af16385ca16b65ac083a6d81ae85ca590f6424a9267f9a7666196b7643981e62449a467e1a7066016b1642189060609a22490b042858a1422b08342a3099e2670298a2c1a3268c16e968b1a2a5b8ee1bb86ab11b1cea1fa87a3228c71b2984dd94284d99406a91aa2b1e6e03b80ab0ba866a188c9231e6ca1aaa6aa213164f213064eade2b7829b1b772ddaa6c29a1a682839833e838833a0c983220bf632a0be63220b963120b8630a9e6ab4e8f6b236bfda78e8f393ddeec7f7222e671ddef7409cff6141fc97b659b2b856dcaa782c3bb28edf5b5f69d581526d78a99d778106e14abe6c61b722999ab368f0b0d6bc0afaed93b41695d95c9c9595f67ca7d85c8a7d46ca5b00e9ceaaee8dea72e8db7f6a4f17baa22c6719fcf7b7d9b877a5cfc73e584ab7f6dc4b22edf3b6569c8b08e9bd814a6d18a9204775c6c5bb7f2af3b70a998af96d7bb40eab5a362c1daea294595b1c939f1257b7d81f577212a07a806989a7769d3a56e9c5a6ee943904a40790061b4a262a06a802988a3b68d58e6a03c9569c7d80ea55471ee3fa8e094225090e873a191cc36550dc27551ca364d0da274e30ca0860b7937ded49afe5657f0a7ac8fbd40a57b12473fb11528c2a82082d9fc49eca4d97b4a6b9958e3e950315ea49191543faa3046c463066c420b182c221666be28e7d2621466ba28c7d2219c39bce6e48bd22e30b4c2b847d92a6a4a0a762c9dd773a9d5f71c9fb780bdf3f46d0d7d3f5113c3055a1a847a0a6739dec74311a185b459286a418b060e19a026f5a8c846592482858ac7ec60297ce5dd17391d5971b11b235ed13a3f48c1368521188281ec173850c268496cb6a2992262a999a60c89bbab4a9e4a3d2c8cafee9e2a3ca4f688d1ee67f599c177b9d0073f98527f21ed866d2e0fb6cac3aa76adf4b5f2ca1a7526d68ab204e75da040b83adb0ab86c49a606c2faeeaac7a3aad91b412bd3a5725779f21f6795c1c8f7221f50b0d2c2eaee2b38a946a4ba1e2a49a1cac28aecabb0a1b265e920647f79d247e79b9c0e7982accab1aa48ab025e6a77a8eea7628e8a1c29608e46df2b5ead90b40ac29aed2ac1a58ac13aaae950ae768cd9f065697d8a56e7d79c867206c8aaf8eca0af46bb1ae6e749a7728eca74a95aa1aa8cb8e3e6be8a5255f9ec1f4f991a469919de5c973a3799ea65517d2a7318ddd5744e5d31c4e49514419cf74418a4de8872558919a55653f1ece7ef99a980d9c777959f46413ddd673a1ce660e9d5e71c1bf671b8f5c7ec1ec066720287ce1e4871a504ab292c01aaea9cca3729caa36a4f088c9fd47b919c07f39ede66e9de873e9cf86132df7b6b2df1b652c89b08a9c2a6f26d08aaa04c8119d70b7dadaab10eadba602d79b406bcdb05eba2aabe8d2a5127c295d5f6695a9c8d7d59c82b7c2d92b5e2d00b0aeac3a5a2bb5b046b9caaa694aa3327c095bdf6495a1f5c721dc80b28abe9b222bcbaeceb999d22c1cb05aba0b042b9aae62b20a8e6a33a182a31a16a854996247b91e5e7291e1e6c7999c08aad2aaeaaa2a3097829c6a35a9c0a342948a16238ba7128d4a6ea942a32a8528e266b88a4a7aa9575f4e9ea25577d3273099024639185e5a97223738dc55724e593944c6951241990643dca4d8886a552954246053e9fbc7b319a880d1c757d11e544139fb67b199a280b9f3e71bde4e4131dd07389ce060d1d5871a9c686fc0f5aa7be9e9a5c69d7a746959a6fe9b9a50640c901a40086ea9eea7a2970a2028e7a33e394a75a9d0a5628e6a1a28c98e3a9bea6e2940a33a8c8a1423888fd23ee8fa21a28df23768dc1482950a024719653c8089c638f8a36a5078e815070e804718d8f43589cf4710d8d43509cda0262f4827e6a795364c77af27947eaa3d757512414fc8fe645328088bca09e9e69fac9a8654b9305eba8f455d249013f44538fe48bba0998bb20986be5af889d9f3187f999789d1f3087f199686112174858e573958c2730966a6951e79889f1f3798ba45196da361913de449e4671994e5f328d7d55c4dfd50e41853044de8f6e4172540931a204913a53e539201e717deb67e9999178f9f2e40de7929a8254589e9f369e4271894fdf3498a244b96c235b9125e428d6555a4df950c418137c4c0905e3db253a930220294e2448538a01c7175fa47ad19907cb1e3c40da3dc8d923d68f4218a8d7a35851a95ce48a55cc48a121148415564de54f641254de40c55544de14f441214dc40c14641f047c01bbc6ee1b5c6d614845205018e694fb8e514bf93761b4540439a13ec39413744bf06d046b8d7742f89b73f39136303cf56411850946b0d7542f09b544d0fcc30350443d50508841e08f6449a7a6269dbf7349d477169f9f805df274670d653ef11242ff61068239a02733deaf42b191069e189868016b960819882695dbe7341d467161cce6089bde7158f447e7a0167c99eae6629c5778d90344658d5f3ed911e2fdd0a6267cf3e40b84f1840608969d190c6251f998045f2176e5ccc7505c544668d634488fba2fee10082219fc7aa5cc942a9a72642989267e96b3660981a268df988041f207aa198478c1c5140c9db87329d407149cc86071c506f60f424650d5d4470fb42fd50a4267502c3cf04f06f48951253c94e2179db59889db376c8b312cbcb2e92f60ff83f64457319cc44acd2b13808e002908a409a75d3d9a6e69a96a9d3b74e8ef33bc4ab93bc8ef03bbcab73bb8ab68f3600f803653194ae3557139c4c470d419506d0d347050d13628d8839dc9ca39d89c883f9cc792ee44383edcc2380d2b2290d2af37f8a3e92de6978f1dea78b7df9594da7f59e0e0833f8d3dd56fd14948ddea1641dea078a19066058dc7317cdc62dbcc5e2db88d683e600983e22d969be0088b6226069b8eb7335ceb63359daf83ddd37801dcc17e3d90169a5c4981fdf176224fa7461d10f3538be694c200e713e3cb9496353802dc4a4708d8b50690d239e49cb505ce7846fd0cf36189c69a5653792d67f37a9a2de82163c59df5f933f895be48e53db451e61c90fe69496925298d3e43d9e05e2e8999f1d948e34d9dee7037c6d2ee3da95464d9550a4165363415ddad7301d3571220f581f590069a18888015f8d7c54fa64618d4f4438be76f31dac72f9d347119cbc6041c443cb8fcb3e84fca4ba0f523e80f281a0c4a30ef46820ecc4a20ef03b20b091ab46051aa5501180182c60a3b6d40137ad3d73704eb135cd35f352466b1cc464110a929b500d0bb4a695b9442540242e95b853c91081cdc59d1cd859c2c652993b64aa146a50b928ad1313164cd139849b348850412f8448b0e945f316144130cb4dea3b68d723700eb035213ff4f5535d19a86401cc042b24e4de83b60d702da4e600e6cb1728a8ed72a7ce5f26c9297487cc583340be0469d0b744bd03f12283a417c8412161032c24dced63978de62da0d6e0e689362118b1628a0a9e26c0a2622f89ae0aaa0fc73164ba910a0fa730ce014ac0a414ab8dff28fe4b19a463c18b75f977a967f49e2653482093df56f514b3f852368b5df916d65b5867de2d57e421e867d927749d8c99325e0f672fde9f67c607e425e7f29e222db7e5a0849a2e4ab8eee5327a8d5bb4f7914a48e0fdf92d243c94ba1ee94b14ce83d1cbd81f19f07a750964f655b744cd27149c109156d53d844c94c842407651d905931648de94a60a293f24c81488057b4a58de7289d21e31fcfc715e9e9b6415e9a78899046050dc53174dc42db4c5c2db08d783ce0038b4e0f269b62d2896a00269b0eb53354eb433520f18005da974c5f8972eda6363ee0797c45c43620d1854434fa53530be48b45f8b6d4d9f56d4a2cf8789f8a67d1275326d2743259e9983c1cb967ae0784255a676985b5167bd9e95e457215c6dad965dd9715ab4af5281ca05245489d63fd8f96d417196b60a7d8b4225881edf138b3a1e081e9adb65f5ada895a1de8599f1265f11fd38f4c2347f0e3c3079e9878820007105f8865cdf1040758fe6039a6662059ee5a9d976263ceaf333d17f441d26f320d08f2bbca0129dd1f738dcc0b405c98917244610fa45570ddc2ff36fcc573e7d26e27fd1f61544dbe2d9ceae351890f38d83713158b6622fccce2f78c7e225cc060be652a8031c4d94923ca8d4a00a712d41839ed1c036250d0272541639e91be4338d87271e68f94d67f192be2dc821dea49df23bf7e495bc48ecfe04f691469a3a52f985a439967a3499e024378991f1f78b27799c065218d1df1a5511367542105b4bb0f684d890569fc27828b6a0867e5268994ce4a98ee5ea256e923a4f711483f7a52892ba43687b252653322d6820625e7c662d482021e66b85ae065fe25c7c621e485b197e47fd1fe38fcc2138f8c1f8019c477a79e267e399797c5901f9dea7789c0268894b65278989f1e7c7261096624338d0e4318d05e2a55095064d9905a4d910584ba8f66948a52092a21ea90c14ca8f1234c8efa3468ee21728d014528011c457e31f147a71978789101e56d922354f936153c104356d122253191f947e101954f14ee4d81042531144c40607a91bb47a81bb06bf146c6be1469400398d2e64f58e394d786b946a0d7142e09b13f20f5044c0c0941005034ff8e624f5135c38e12e41ae11a642d8d6f26bd12e40f8fc6301cf4e1409da772e9d2f710a0ef81dd8fa69898827ffdf877c3cfa44610d4d4430be57699cb874b9c406f19cb66029c3e3cb20ee81d9cb767a9e9742518f8698188060219e85a859702635ffe7e19f0e70fde9665c9e1e4070f9e45f8d474418bdf3c9908e261d0161364fb33e6d2e23ec8f3a3e68f2212846810edc6800ec44a00ed83b00b0119345ed53a464917a18246084fa4ec34f44dd33aacdbb4d64d5b350c72b194c63b10a13eb4a0d0a356cd282440d5b253693ea42891021cd45971cd05964644ec14a050a12c04a894464a13332cc534825029392499b2f6c5db15b44730e343fb0c553d356c511b49ad08b49a95af53093d2446908a1d345911d305903ec4dd14a00a1131a5208158d1793aa510133252694224c6b2ba4a7127ed1f14044e312fcc983170c555116c3e30dd42fd3e64db9314526827e51f0152d5384d6d5b0536120b40ad5ae530120a47cd01347c953653594be511935a40a90121e8c6d51af45191e886d41af05184b813e8392d3d038cd3581accfb03ce119035650a026651182fc502813acf983c8117835051002f650882605010134c5f11ca472f15fc5d9159c74715e4561170454f15247a11b3c6b714046b113a44d108041a9064414d062c13504740e1122447111647a006246690e7c6510e1c7460f846ce04bc6680e646391cb83f90dbc6b6045c4880e783980aa05f0104057e0c3c5780bdc5000324dd23b08d5a36e8eaa35093e74f3d357194863a1ca84293740ec035609212d8ce480e0cdb83aa0d402d8490938c036b4f993ce4d58e4a38c92de1ac865018e072810443810da46b00444ebf391caff2848a87266927f481cc523328bda463d09f445d02711c838c17683fa15b03143af8e46247cdce2d88d560e08afe2840a86266091e20b8a0e22989960a4927e4818dcf283cc673ebc5623140cc82f60b60229cc662244bee0bcd18e42791164098d57265cfae2fbcf3613a84700e185d80fe05660c383800a405600bc44e802c590364098127a55e947870dc22dacdc3316cb6a31688d98b2e2c98771b4d67cdb4c67c9f857e11273326927232622cd8b3225469ada6a83b5ffd83b1ffc3acccd33ac8cd28b221da8b2a25287622508581ad565edad465ea0757c360747c30e3b47ecc2238e91fa3081b4b67b5a656b4d9755e2d7205c556ab696d9e365acaf32818913280c89b63f5b4a6b4971363cca7b63f180c67b1a6465d16a561ec98e7e0e0eb7fee0737c2da5d63d587d768dd2b72d5c3d460d10b3528fa32f89e9383aa0726795cb3424de927869f827fe9f0a65b5c3b406d26d3208ead3334e3547d4c0a2bb4a0029d498845f5105423501511805c80fa037615582fe36f0b653ab0e342434d440dc0dbd315526c47d09fd3e745502d90c542304c803330c082254bdc0be1b496b459e7697d96f5e2571a5c516aa69659e165a4af22810912280889a6d21ad063dd71163c4a7a6799a5e65b98f6601969f61e498c5e217185c496a45c4169e58816982089a58678196863c18785a658002628aec27f890c27f089429d098620709840a020e981c5f817fe5f0969718f461f1da174a5cb470f11824428d4b3e88be383a20707a459e472c50927e01ff87c21e90786196c70e501a69698f261e99e265a969b600898b7681d2872c9c3a72c1c386011bc03ca917c4410d453e70bdd42310142614f241360ea738bd26747bcc6a331cbf22b9c9fa29bc98245dd0ff421d00f11685c20f8837415502fc3a98e2e36d8b5f241cd3e0da926647b8db7313c9f73e5c54a31a0cc62fc0b5e31388a9223cbd60bc8ae627e0a6e260090627d888e205897e09e917643f90864038d3f3e58bd725fcf1e134845817003e00db854e0bd836815202f009e04d00265bba252c94925208589829d9d766dd9a2cacb292ca26859a0e6829649d25748dd223bb4eeb2acceec3ba8ee92ac4ee82ac24a590b60e78395cae72b12ad4aacdfc37e8a3c28ea3b594665138cf5ff77fd5c3670d11bd50550cd504d1bb432cd843608e712710e70270a4a390ae0e672be0e372a92ac37f4a3d4aa4df828e267f927e3af947a7dd9dade8f8b1df7d81acfdd569d3c5450d23194623b3943633b7fd9c377fcdc3246f14144330d8539cc9c55044e7246e50c936009c099f651f92767db8eb67657a3a2c681b5f7b3f715a648cd3c3450660499f258c909e5118cde4259da650b8cd67639bade168939f057c0d2d63d9152e541134d414d34b4145e897a21e1063bd8ee5ff8daf311cdae2d5cc462d588d08385ff183822c17fc22c08921a576958e9f32fce9e32f9d97747e0df7fbdca97dddc31819deff63a5a5161c4f8f45bd0f734d8bce7655d1d72a1c3083760657fb5f757bf58e869418703e3916e43d8d372f3dbb47651d1c7299c2e7291c2c5fe0f163f14fc44b40f4c3e24f883c4067d12743bb19f03ad12703ba0eb02bc46951a454a116945a060518112954ff50b54a515a14ff10b456814ec43c50f01c7c59b1c7859a3b553fb37953bf35b534736a4e9934c46651c646291090b133b4ca9b4a4d1a342cca2544ace5b26b521b40ecc4132e4bc912143a317b4583103432b3b50de435b13f94ef534536a0e9834c06641c6062810949333b48de235a8e5a2d443952c44ed12a64a2439649ac4a4521946850b144a50393100cb82f204840e885ec160840c0ca89313b40e583780d682d4039424c08402c40a9828889aa28809a822e02a4928a42a8391cad8389cab4aa8dfb28ed2a837e4a3999e64998ea67dc9dc651c8b15f7f7a3606a56953c74514fdb48c27da9dc2673924e3a3946a2c37dfa06c7a2d5a34f1914448c8fd99272424945a51487594b68afdf798af5f788741b416d019df677925f4978c9332460de729de8781999d941fe0dc72960647a159d841f959f4f0512d56753c044b14b0496525841e50781d8c762163458c4a48de3288cfc34868c7b15d52903784a214860fc131e4574944a50c8eca33a7fd1c357fc9c335048e7546e90ca360c9c35040e7446e10c836049c199de51d9f664979d923a78b1206f7a31f7a56912353f693c24502676945e5fe961a4218cc6768907e7619ba65098cbe24c7c1de147c0952c540934f41552d43d8934a41427d89daa671946e4918e862c281b9f7c7a295a248d13c44508fd89442496907a50e87514b49d8a7609ba2670945650f97e2580906e32b90663298929f067c11e1254a95004d390544d310524b48f60942a508924241887494b28eb23348e9a32e8e82328856943a8afa0698919f018af2068873a2447c021cc8551ac96b2196765991e74798e27306ce263065fee70bde867839f767bf9961401dfec70b5f747bf1e847831960401959e487552653a934940f559c48714ae54914e84d2103c52b143447851e040050001e446eb1e406ea1a9c5151a985144fe8e5d4b393be4d18e211a851a242c8d6b26acfc23d2912a40e8c0313f53f839713bc4d112cc38806a046810b035a49a944a10383f00f4830044fc7a0de8278298ed63b17fc36b4c4536b0b553110b5423460db7fae2bb836a2ba8909fea6955a543a74cbd3a70cbc8365fe97645d197dc5ca38185ef970ada4b638d86b45b50f53e34d342f322b97dce2b78729f726ced9dd6ce99dc4974c954970c907a060d87286060674d07d8ae2240818defb8ada1c8818a23e871a14e7be9ac36595ac265911e53894c1d4790e243061e807821fe870a5f707be195b4015a4f6925b39675d9d16b0595f65657795c257035a54add27bc9ed23f4885639d8e16ce1ac05c04a6563997f66939869675995e5a3c9773a5ccb7459d0ef495cc7d41dd1df387cc053ffcad727a4a5f25c45b111243d114fc35f0b9cda730fcf8749591de279c5393698b4f3a58d2e38788f70d64c3e2d388b932d8bc631e0c0021fc2e1763dd177289c2a835e05f7f9df6f7bdd8e2692986a3e3116c43d0d352f35d8e7459ca070a1bae7279c265fc8f14835a05e727de7f674907c7f99f6e7bd9c2779f9e0665690046381a4861a17f067419585a249753e1916643b8d2f2f1cf0e41d8ffe25bc4c13eb52ca3eb0f343e0cf823c2849b19ec3b519e83ab12683b40ea82ba46355224631163458860318093e549f509d566d27c56694d44f9109c43ad0ea1c745951c705944f8cebd4ee4dcd4d04d553a4cda334ac7131934623108918b49ed09b3aecafb2a0d1132835203408ce432654cb330ecbc3175456b11b438b0fd431356653bb445559752a93ba445125341cd25241c874b162c74a1628fab49e8dcb282d202318c55d54815985349343481502556594a8481151e53414a650b934240911db3fed1da3fe878b1b4c6a5144c78a1b486a414492c84f88e454ee1340386c69b3ea8f32462909a354c99344490222fac4e545850e93a44cb1494507131951d93fe4e192fb4ad129649e325ac5ab14f44430f2c35d0b94f813684c3949411d827845333e00f0845810e834a4bc141c0ff825a44bb17ac71715f4711174c5651d14573156c7891b3469f13ec699138c5a914dc53112e41e906a0179052c17304cc105036c48311ac7881104171198c39d192c3851d106cc0f2412d19883931c586210fcc69e0d5c0ff120839c0e482a217a857c102830d15c84fa0b7c0c33af0dcc35513e14edd33f3688e9234a864c1c48622108ceba3728d52246ce422d2c37d4f813b64cf8e444b18e1a1a68da03a40d282d24e1823c43531928710188040b0dec6980d440f93ae4e412be4a81283099449e52014625099444502130e8cb22f0846c0e285d415a83f40c48eb839009193720d502d2837c2be0a80282899224608282820990228028c49e12003724a093ea4c61157118842611104080d512644fa83cc0be91390c3832c0bc02d208a13180be821e42db11a838417485640fc830c0de828a15684e20b640ab79f5e7c78118eb63a97fa36acc4336a8b533108b52234e2b58ad223c8355fe58351fe4694da523a6ccbb3a68cba8ace2b18711f6d7db1b35676db34676925b325125a324a2b288ea2b0870a23887021488175ef58171ef46af59636af1962478ce2330711e23888c1a834dfe37dae05b7bcdd8b744dc9d7095a45637586545ad0f33e2cd322f29e7b834a05a726d9cd41ede7a7809fe27da9ef2708d955400da4d6ccd9d56aed95d690d9cb654d7735c216fd5a4cadb27b89eb23ec8836395b326ae98db5beca6363917f469319d465718635a349763a54cb54954c7c4774e1d301116543b50753ff4ad527a0a5d25c05b011203d014f835e0b98da530f52544770f8527945383690b4d3a50e1c34b08f50d60c3c2d308bb32d0c7a3008bc421f42e083460597f85f697bc5d897445c9c7091a44637186445a90f23e28d332f2e0d08161e7972659cc41e9fe07da1ef079e1e0070859544009d887441c9a7089c987081ba85fb0f1269098da61899ca65497ea5a0c97345910ec3e10d2d2f150743ff0f0c25b44c06cc5ab9691d9cf655da4167259515dc57025bf16922b689ec27a88fa2209b306ae18df63656f92989a46673995663797ee618568725d1a40672195063618605fa168125c97705c016fa5a316f85a19680582080a2b509e627908f421f0a5c25b896c2010268493d1d73a3ce1732bcc642fb115f439d06f3fdcacf2788a5725a85aa11083ca14f035c0b9124e4758d9f30dcf7f277c5323a38e163678b4734988ef0d48cae3188bea30d8b46228cbbe21dc2da45790e641b8ff63df8d272efcf06259c4ba2b389e0295896827788ee21d89661ff826216a04400f205360d582de14c03500b604b809800814b10f953e50f1c3df4f7c3c1049919e43af19e03a912603ae0ea02b8547117545d115d4570601180159556514bc4f353cc4995085499108443950e41c6c58f1c6858e564d59152913b54ed10fd43f124d41b524c41b07331624732162151a56494ba56414a254614b852814284cf533c47b500d47b100c4754ff54750ff41e146bb1a8c5111e106ba1a885104f2d3b34cecea536d4d3d3a34d9d349470d18d461d10812c24f293b24ce8e2d385469545cd263420d0fb47ad00b3a8ce2b2b8ca6b27d497d32b4c352ef45bd154c4550dcc3dd0becf9349891ea36cc9f3312c5453e48f1a45c908243e900a34ec97b2f4c4cd456d0e3492d06b474cff33a2ce1332acc4d2f54acb294c9dd25945a514ec43d0f1435b0b8cf7b49291d2366cc33276c52d3de8f0245690e241a8ff2348cbbb258c4b517a471515dc72d15c47831ad469d13e470b1a4c5bb1534543132c5a314d452b12cc1e30640178052816d046c10303644811e0845310ec16b19843971cb06b418cc36d0f0c11519803911c5069c186c3db0d540fd12003960e402a017a057615c04f810202f50b740c14f253b14ce4ea436d0d3c3a30d9c349070c18d061c10853c84ec13384b00e2c38506943a88db234e8e2a240cb450d94e8a3668d223848b4323ac34d1c2863218684091a483630d2c0f349851e945c508143e50093a84e292b84a6927d097c32b0c342ef05bc15484540dc83dc0be926047a0f9136c49f1312454445c108043e10083e40f1834e49792f444cc3a80e2836c0d382404b440d90ae029a09f225e89f025e0900204088809d0caa30c8bba3120bd02d0888921cc2d516e854c114836c0f682f415084ca0d882720b4c09349251d145650e141a4ff13a24e1132a4c4c2f50ac929449dc25905a414e843c0f1035a0b892484740f793664c31276452c45610e041a0ff03de0f003484bb925844b43a20e103660d202d048e90d30ca83128bd230c0bb82d0088b21c42d42b20a502768962276096023a08701fe025c168853410e83c20d502dc14a84b20d282d2096807b1e047271abc70f1a5c5d1157c55913847091a445b9151c54113245a114bc52912c41e1062817204c816c0468102036078011a445110e41691c986ae192437f18c43670f0410f1c38696192037918643d90d3c0f7174055e15604e011a037e0de02880fc02ef0b5c0a91c2069018c06180fc43610d240f116e054615004c811403660f602ee0d802700b44091168052e14a04b010e03c00d382d60d202d00960079078018805c012c05a811403f00c005a010e03d80a803c009001e0000⟩
def D1 : FData := ⟨1,12,4096,[0,1,2,4,5,6,8,9,10,12,13,14,16,17,18,20,21,22,24,25,26,28,29,30],[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[18056,14472,17608,10440,13576,9992,18049,14465,17601,10433,13569,9985],[⟨205,[1,2,4,8,16],[0,9,6,7,8,5,4,1,2,3]⟩,⟨206,[1,2,4,8,17],[9,0,7,8,6,4,5,2,3,1]⟩,⟨215,[1,2,4,8,19],[8,9,6,7,5,3,4,1,2,0]⟩,⟨209,[1,2,4,8,20],[0,8,9,7,6,5,3,4,2,1]⟩,⟨210,[1,2,4,8,21],[9,1,8,7,5,4,6,3,2,0]⟩,⟨216,[1,2,4,8,23],[0,8,1,7,4,5,3,6,2,9]⟩,⟨211,[1,2,4,8,28],[0,8,1,2,4,5,3,6,7,9]⟩,⟨212,[1,2,4,8,29],[0,8,1,2,4,5,3,6,7,9]⟩,⟨217,[1,2,4,8,31],[0,8,1,2,4,5,3,6,7,9]⟩,⟨207,[1,2,4,9,17],[9,0,8,6,7,4,5,3,1,2]⟩,⟨210,[1,2,4,9,18],[0,9,7,3,6,5,4,2,8,1]⟩,⟨216,[1,2,4,9,19],[9,8,7,6,5,4,3,2,1,0]⟩,⟨211,[1,2,4,9,20],[9,1,8,7,5,4,6,3,2,0]⟩,⟨212,[1,2,4,9,21],[9,1,8,7,5,4,6,3,2,0]⟩,⟨229,[1,2,4,9,22],[0,9,8,2,6,5,4,3,7,1]⟩,⟨222,[1,2,4,9,23],[9,0,1,7,3,4,5,6,2,8]⟩,⟨213,[1,2,4,9,24],[9,1,7,8,5,4,6,2,3,0]⟩,⟨242,[1,2,4,9,26],[8,9,6,7,5,3,4,1,2,0]⟩,⟨218,[1,2,4,9,28],[9,2,1,0,3,4,7,6,5,8]⟩,⟨219,[1,2,4,9,30],[8,1,2,5,4,3,6,7,0,9]⟩,⟨231,[1,2,4,11,20],[7,9,8,5,6,2,4,3,0,1]⟩,⟨232,[1,2,4,11,21],[9,7,8,5,6,4,2,3,0,1]⟩,⟨255,[1,2,4,11,24],[0,7,6,3,4,5,2,1,9,8]⟩,⟨247,[1,2,4,11,28],[0,9,1,2,3,5,4,6,7,8]⟩,⟨211,[1,2,4,12,20],[0,8,9,6,7,5,3,4,1,2]⟩,⟨229,[1,2,4,12,21],[1,8,0,2,4,6,3,5,7,9]⟩,⟨232,[1,2,4,12,23],[0,7,1,3,4,5,2,6,8,9]⟩,⟨252,[1,2,4,12,24],[0,7,8,9,6,5,2,4,3,1]⟩,⟨237,[1,2,4,12,25],[9,1,8,7,5,4,6,3,2,0]⟩,⟨233,[1,2,4,12,27],[0,7,1,3,4,5,2,6,8,9]⟩,⟨235,[1,2,4,13,22],[7,9,8,5,6,2,4,3,0,1]⟩,⟨253,[1,2,4,13,24],[0,7,1,3,4,5,2,6,9,8]⟩,⟨248,[1,2,4,13,26],[9,1,0,2,3,4,6,5,7,8]⟩,⟨256,[1,2,4,15,24],[0,7,1,3,4,5,2,6,9,8]⟩,⟨208,[1,2,5,9,17],[9,0,6,7,8,4,5,1,2,3]⟩,⟨212,[1,2,5,9,18],[9,0,6,7,3,4,5,1,2,8]⟩,⟨217,[1,2,5,9,19],[9,8,6,7,5,4,3,1,2,0]⟩,⟨214,[1,2,5,9,20],[9,1,8,7,5,4,6,3,2,0]⟩,⟨219,[1,2,5,9,22],[9,1,0,7,3,4,6,5,2,8]⟩,⟨221,[1,2,5,9,28],[9,2,0,1,3,4,7,5,6,8]⟩,⟨223,[1,2,5,9,30],[9,2,0,1,3,4,7,5,6,8]⟩,⟨222,[1,2,5,10,19],[8,9,6,7,5,3,4,1,2,0]⟩,⟨237,[1,2,5,10,20],[0,9,2,6,3,5,4,7,1,8]⟩,⟨243,[1,2,5,10,22],[8,9,7,6,5,3,4,2,1,0]⟩,⟨245,[1,2,5,10,28],[0,9,2,1,3,5,4,7,6,8]⟩,⟨233,[1,2,5,11,20],[9,7,8,5,6,4,2,3,0,1]⟩,⟨236,[1,2,5,11,22],[9,0,1,2,3,4,5,6,7,8]⟩,⟨241,[1,2,5,11,24],[9,0,6,2,3,4,5,1,7,8]⟩,⟨250,[1,2,5,11,28],[9,0,1,2,3,4,5,6,7,8]⟩,⟨228,[1,2,5,12,20],[8,0,9,6,7,4,5,3,1,2]⟩,⟨248,[1,2,5,12,22],[8,1,7,5,4,3,6,2,0,9]⟩,⟨239,[1,2,5,12,24],[9,1,8,7,5,4,6,3,2,0]⟩,⟨240,[1,2,5,12,25],[9,1,8,7,5,4,6,3,2,0]⟩,⟨272,[1,2,5,12,26],[8,9,7,6,5,3,4,2,1,0]⟩,⟨251,[1,2,5,12,27],[9,1,0,2,3,4,6,5,7,8]⟩,⟨271,[1,2,5,14,24],[0,9,1,2,3,5,4,6,7,8]⟩,⟨259,[1,2,5,14,25],[9,1,0,2,3,4,6,5,8,7]⟩,⟨285,[1,2,7,12,20],[0,8,1,2,3,5,4,9,6,7]⟩,⟨286,[1,2,7,12,24],[0,8,2,1,3,5,4,9,6,7]⟩,⟨273,[1,2,7,12,25],[9,8,7,6,5,4,3,2,1,0]⟩,⟨282,[1,2,12,20,24],[0,8,6,7,9,5,4,1,2,3]⟩,⟨283,[1,2,12,20,25],[0,8,1,2,3,5,4,6,7,9]⟩,⟨287,[1,2,12,20,27],[0,8,1,2,3,5,4,6,7,9]⟩,⟨280,[1,2,12,21,26],[0,9,3,1,2,5,4,7,8,6]⟩,⟨225,[1,4,6,8,16],[0,9,8,6,7,5,4,3,1,2]⟩,⟨213,[1,4,6,8,17],[9,3,0,7,6,4,5,8,2,1]⟩,⟨226,[1,4,6,8,18],[0,9,8,7,6,5,4,3,2,1]⟩,⟨255,[1,4,6,8,19],[7,9,8,6,5,2,4,3,1,0]⟩,⟨213,[1,4,6,8,20],[0,8,9,7,6,5,4,3,2,1]⟩,⟨242,[1,4,6,8,21],[0,7,8,6,4,5,3,2,1,9]⟩,⟨252,[1,4,6,8,24],[1,9,8,7,5,6,4,3,2,0]⟩,⟨237,[1,4,6,8,25],[0,7,8,1,4,5,3,2,6,9]⟩,⟨253,[1,4,6,8,26],[1,9,8,7,5,6,4,3,2,0]⟩,⟨241,[1,4,6,8,27],[0,7,8,1,4,5,3,2,6,9]⟩,⟨237,[1,4,6,8,28],[8,2,0,1,4,3,5,7,6,9]⟩,⟨243,[1,4,6,8,29],[0,7,8,1,4,5,3,2,6,9]⟩,⟨214,[1,4,6,9,17],[9,3,0,6,7,4,5,8,1,2]⟩,⟨253,[1,4,6,9,18],[0,9,8,2,6,5,4,3,7,1]⟩,⟨241,[1,4,6,9,19],[9,7,8,6,5,4,3,2,1,0]⟩,⟨218,[1,4,6,9,20],[9,5,8,7,6,4,3,0,2,1]⟩,⟨219,[1,4,6,9,21],[9,5,8,7,6,4,3,0,2,1]⟩,⟨230,[1,4,6,9,24],[9,2,0,8,6,4,5,7,3,1]⟩,⟨276,[1,4,6,9,26],[7,9,8,6,5,2,4,3,1,0]⟩,⟨245,[1,4,6,9,28],[8,1,9,7,5,3,4,6,2,0]⟩,⟨227,[1,4,6,10,18],[0,9,8,6,7,5,4,3,1,2]⟩,⟨256,[1,4,6,10,19],[7,9,8,6,5,2,4,3,1,0]⟩,⟨228,[1,4,6,10,20],[1,9,8,7,5,6,4,3,2,0]⟩,⟨248,[1,4,6,10,21],[9,7,8,5,6,4,3,2,0,1]⟩,⟨254,[1,4,6,10,24],[1,9,8,7,5,6,4,3,2,0]⟩,⟨271,[1,4,6,10,25],[9,7,8,6,5,4,3,2,1,0]⟩,⟨258,[1,4,6,10,28],[1,8,7,5,4,6,3,2,0,9]⟩,⟨259,[1,4,6,10,29],[1,8,7,5,4,6,3,2,0,9]⟩,⟨247,[1,4,6,11,20],[9,7,8,5,6,4,3,2,0,1]⟩,⟨249,[1,4,6,11,21],[9,7,8,5,6,4,3,2,0,1]⟩,⟨275,[1,4,6,11,24],[0,9,8,1,2,5,4,3,6,7]⟩,⟨277,[1,4,6,11,28],[0,9,7,1,4,5,3,2,6,8]⟩,⟨214,[1,4,6,12,20],[0,8,9,6,7,5,4,3,1,2]⟩,⟨219,[1,4,6,12,21],[8,0,9,7,6,3,4,5,2,1]⟩,⟨230,[1,4,6,12,24],[0,7,9,8,6,5,4,2,3,1]⟩,⟨245,[1,4,6,12,25],[9,6,8,7,5,4,3,1,2,0]⟩,⟨257,[1,4,6,12,26],[1,9,8,7,5,6,4,3,2,0]⟩,⟨250,[1,4,6,12,27],[0,7,8,6,4,5,3,2,1,9]⟩,⟨276,[1,4,6,13,24],[0,6,7,3,4,5,2,1,9,8]⟩,⟨292,[1,4,6,13,26],[0,9,6,3,4,5,2,1,8,7]⟩,⟨226,[1,4,8,14,16],[8,3,0,1,7,4,5,6,9,2]⟩,⟨228,[1,4,8,14,17],[8,3,1,2,5,4,6,7,9,0]⟩,⟨262,[1,4,8,14,18],[0,9,7,8,6,5,3,4,2,1]⟩,⟨285,[1,4,8,14,19],[8,9,6,7,5,4,2,3,1,0]⟩,⟨253,[1,4,8,14,20],[8,3,0,1,2,4,5,6,9,7]⟩,⟨248,[1,4,8,14,21],[8,2,9,0,6,3,4,5,7,1]⟩,⟨227,[1,4,8,16,30],[8,3,0,1,2,4,5,6,7,9]⟩,⟨263,[1,4,8,18,20],[0,9,8,6,7,5,4,1,3,2]⟩,⟨264,[1,4,8,18,28],[8,2,0,1,3,4,5,6,7,9]⟩,⟨254,[1,4,8,20,26],[8,3,0,1,2,4,5,6,7,9]⟩,⟨239,[1,4,9,18,20],[9,3,0,6,2,4,5,1,8,7]⟩,⟨264,[1,4,10,12,18],[0,9,8,7,6,5,4,3,2,1]⟩,⟨286,[1,4,10,12,19],[8,9,7,6,5,4,3,2,1,0]⟩,⟨239,[1,4,10,12,20],[0,7,9,8,6,5,4,2,3,1]⟩,⟨272,[1,4,10,12,21],[0,6,8,7,4,5,3,1,2,9]⟩,⟨269,[1,4,10,12,22],[8,2,0,1,4,3,5,7,6,9]⟩,⟨273,[1,4,10,12,23],[8,2,0,1,4,3,5,7,6,9]⟩,⟨254,[1,4,10,12,24],[0,7,8,9,6,5,4,2,3,1]⟩,⟨271,[1,4,10,12,25],[0,6,8,7,4,5,3,1,2,9]⟩,⟨266,[1,4,10,18,24],[0,9,6,7,8,5,1,3,4,2]⟩,⟨297,[1,4,10,18,28],[3,9,2,0,1,7,6,4,5,8]⟩,⟨288,[1,4,10,20,24],[0,9,8,7,6,5,4,3,2,1]⟩,⟨289,[1,4,10,22,24],[0,9,8,7,6,5,4,3,2,1]⟩,⟨261,[1,4,12,20,26],[7,2,8,5,6,3,4,0,1,9]⟩,⟨274,[1,4,12,22,24],[8,3,0,1,2,4,5,6,9,7]⟩,⟨283,[1,5,10,18,24],[0,9,4,6,7,5,8,2,3,1]⟩,⟨267,[1,6,10,12,18],[0,9,7,8,6,5,3,4,2,1]⟩,⟨287,[1,6,10,12,19],[8,9,6,7,5,4,2,3,1,0]⟩,⟨268,[1,6,10,12,20],[0,8,9,7,6,5,4,2,3,1]⟩,⟨280,[1,6,10,12,21],[9,6,8,7,5,4,2,1,3,0]⟩,⟨299,[1,6,10,18,28],[3,9,0,1,2,7,4,5,6,8]⟩,⟨291,[1,6,10,20,24],[0,9,7,8,6,5,3,4,1,2]⟩,⟨284,[1,6,12,20,24],[0,8,9,6,7,5,4,2,3,1]⟩,⟨302,[1,6,12,20,26],[0,7,8,5,6,4,3,1,2,9]⟩,⟨22,[3,4,8,16],[4,8,5,6,7,0,1,2,3]⟩,⟨23,[3,4,8,17],[8,4,6,7,5,0,2,3,1]⟩,⟨37,[3,4,8,20],[5,8,7,6,4,1,3,2,0]⟩,⟨38,[3,4,8,21],[8,5,7,6,4,1,3,2,0]⟩,⟨71,[3,4,8,28],[4,7,1,2,3,0,5,6,8]⟩,⟨72,[3,4,8,29],[0,7,1,2,3,4,5,6,8]⟩,⟨24,[3,4,9,17],[8,4,7,5,6,0,3,1,2]⟩,⟨32,[3,4,9,18],[0,8,6,3,5,4,2,7,1]⟩,⟨39,[3,4,9,20],[8,5,7,6,4,1,3,2,0]⟩,⟨40,[3,4,9,21],[8,5,7,6,4,1,3,2,0]⟩,⟨74,[3,4,9,22],[0,8,7,2,5,4,3,6,1]⟩,⟨41,[3,4,9,24],[8,5,6,7,4,1,2,3,0]⟩,⟨106,[3,4,9,26],[7,8,5,6,4,3,1,2,0]⟩,⟨60,[3,4,9,28],[8,6,1,0,3,2,5,4,7]⟩,⟨73,[3,4,9,30],[7,0,2,5,3,4,6,1,8]⟩,⟨71,[3,4,12,20],[4,7,8,5,6,0,3,1,2]⟩,⟨153,[3,4,12,21],[0,6,1,2,3,4,5,7,8]⟩,⟨156,[3,4,12,24],[4,6,7,8,5,0,3,2,1]⟩,⟨92,[3,4,12,25],[8,5,7,6,4,1,3,2,0]⟩,⟨125,[3,4,13,22],[0,7,8,2,5,4,3,6,1]⟩,⟨93,[3,4,13,24],[8,5,7,6,4,1,3,2,0]⟩,⟨121,[3,4,13,26],[8,1,0,2,3,5,4,6,7]⟩,⟨25,[3,5,9,17],[8,4,5,6,7,0,1,2,3]⟩,⟨33,[3,5,9,18],[8,0,5,6,3,4,1,2,7]⟩,⟨42,[3,5,9,20],[8,5,7,6,4,1,3,2,0]⟩,⟨56,[3,5,9,22],[8,0,1,6,3,4,5,2,7]⟩,⟨64,[3,5,9,28],[8,6,0,1,3,2,4,5,7]⟩,⟨69,[3,5,9,30],[8,0,1,2,3,4,5,6,7]⟩,⟨86,[3,5,10,20],[0,8,2,5,3,4,6,1,7]⟩,⟨107,[3,5,10,22],[7,8,6,5,4,3,2,1,0]⟩,⟨116,[3,5,10,28],[0,8,2,1,3,4,6,5,7]⟩,⟨59,[3,5,12,20],[8,6,7,4,5,2,3,0,1]⟩,⟨134,[3,5,12,22],[7,1,6,4,3,5,2,0,8]⟩,⟨94,[3,5,12,24],[8,5,7,6,4,1,3,2,0]⟩,⟨95,[3,5,12,25],[8,5,7,6,4,1,3,2,0]⟩,⟨171,[3,5,12,26],[7,8,6,5,4,3,2,1,0]⟩,⟨167,[3,5,14,24],[0,8,1,2,3,4,5,6,7]⟩,⟨148,[3,5,14,25],[8,0,1,2,3,4,5,7,6]⟩,⟨198,[3,12,20,24],[4,5,6,7,8,0,1,2,3]⟩,⟨199,[3,12,20,25],[0,5,1,2,3,4,6,7,8]⟩,⟨191,[3,12,21,26],[0,8,3,1,2,4,6,7,5]⟩,⟨263,[4,5,8,10,16],[3,7,0,8,6,5,9,4,2,1]⟩,⟨254,[4,5,8,10,17],[9,2,8,0,6,4,3,5,7,1]⟩,⟨275,[4,5,8,10,19],[6,9,7,8,5,2,1,4,3,0]⟩,⟨239,[4,5,8,10,20],[8,2,9,0,6,4,3,5,7,1]⟩,⟨271,[4,5,8,10,22],[1,7,0,8,4,5,6,3,2,9]⟩,⟨272,[4,5,8,10,28],[1,7,0,8,4,5,6,3,2,9]⟩,⟨264,[4,5,8,16,26],[7,3,8,0,1,4,2,5,6,9]⟩,⟨288,[4,5,8,18,24],[3,7,0,8,6,5,9,4,1,2]⟩,⟨284,[4,5,10,18,24],[4,9,0,6,7,5,8,2,3,1]⟩,⟨23,[4,7,8,16],[0,4,1,6,7,5,8,2,3]⟩,⟨32,[4,7,8,17],[8,4,7,6,5,3,0,2,1]⟩,⟨38,[4,7,8,20],[1,5,0,6,3,4,8,2,7]⟩,⟨39,[4,7,8,24],[1,5,2,7,4,6,8,3,0]⟩,⟨74,[4,7,8,25],[8,4,6,7,5,2,0,3,1]⟩,⟨153,[4,7,8,28],[4,6,8,7,5,3,0,2,1]⟩,⟨33,[4,7,9,17],[8,4,7,5,6,3,0,1,2]⟩,⟨100,[4,7,9,18],[6,8,7,4,5,3,2,0,1]⟩,⟨74,[4,7,9,20],[0,4,1,2,3,5,8,6,7]⟩,⟨86,[4,7,9,24],[0,4,1,2,3,5,8,6,7]⟩,⟨164,[4,7,9,26],[6,8,7,5,4,3,2,1,0]⟩,⟨113,[4,7,9,28],[0,4,1,2,3,5,8,6,7]⟩,⟨72,[4,7,12,20],[4,7,8,5,6,3,0,1,2]⟩,⟨92,[4,7,12,24],[1,5,0,2,3,4,8,6,7]⟩,⟨114,[4,7,12,25],[8,5,7,6,4,3,1,2,0]⟩,⟨24,[4,8,15,16],[0,4,1,2,7,5,6,8,3]⟩,⟨33,[4,8,15,17],[0,4,1,2,3,5,6,8,7]⟩,⟨40,[4,8,15,20],[1,5,0,2,3,4,6,8,7]⟩,⟨25,[4,8,16,31],[0,4,1,2,3,5,6,7,8]⟩,⟨34,[4,8,17,18],[4,8,5,6,7,1,2,0,3]⟩,⟨35,[4,8,17,22],[7,3,1,6,4,5,2,0,8]⟩,⟨36,[4,8,17,30],[7,3,1,2,4,5,6,0,8]⟩,⟨41,[4,8,19,20],[1,5,0,6,3,4,2,8,7]⟩,⟨59,[4,8,19,28],[2,6,0,1,3,4,5,8,7]⟩,⟨42,[4,8,20,27],[1,5,0,2,3,4,6,7,8]⟩,⟨55,[4,8,21,26],[0,4,1,2,3,5,6,7,8]⟩,⟨35,[4,9,10,17],[8,4,6,7,5,2,3,0,1]⟩,⟨101,[4,9,10,19],[6,8,5,7,4,1,2,3,0]⟩,⟨75,[4,9,10,20],[4,8,7,6,5,3,0,2,1]⟩,⟨76,[4,9,10,21],[8,4,7,6,5,3,2,0,1]⟩,⟨126,[4,9,10,23],[0,4,1,2,3,5,6,7,8]⟩,⟨35,[4,9,10,24],[0,7,6,8,5,2,4,3,1]⟩,⟨76,[4,9,10,28],[0,6,7,8,5,3,4,2,1]⟩,⟨55,[4,9,14,17],[8,3,1,0,6,5,4,7,2]⟩,⟨87,[4,9,14,18],[4,8,7,6,5,3,0,2,1]⟩,⟨161,[4,9,14,19],[5,8,7,6,4,3,1,2,0]⟩,⟨76,[4,9,14,20],[6,2,1,4,3,5,0,8,7]⟩,⟨127,[4,9,14,21],[7,4,8,6,5,3,2,0,1]⟩,⟨87,[4,9,14,24],[0,6,7,8,5,3,4,2,1]⟩,⟨57,[4,9,17,26],[8,3,6,0,1,2,4,5,7]⟩,⟨58,[4,9,17,30],[7,3,2,4,5,6,0,1,8]⟩,⟨88,[4,9,18,24],[4,8,5,6,7,1,0,3,2]⟩,⟨90,[4,9,18,28],[2,6,1,3,4,5,7,0,8]⟩,⟨86,[4,9,19,20],[8,4,7,5,6,3,1,0,2]⟩,⟨89,[4,9,19,24],[8,4,5,7,6,1,3,0,2]⟩,⟨145,[4,9,19,28],[8,3,1,0,2,5,4,6,7]⟩,⟨77,[4,9,20,26],[6,2,1,4,3,5,0,7,8]⟩,⟨130,[4,9,21,26],[0,4,1,2,3,5,6,8,7]⟩,⟨90,[4,9,22,24],[7,3,1,6,4,5,2,8,0]⟩,⟨91,[4,9,23,24],[0,4,1,2,3,5,6,8,7]⟩,⟨60,[4,11,12,20],[2,6,7,4,5,3,8,0,1]⟩,⟨113,[4,11,12,21],[8,4,7,6,5,3,0,2,1]⟩,⟨93,[4,11,12,24],[1,5,0,2,3,4,8,6,7]⟩,⟨94,[4,11,20,24],[1,5,0,3,2,4,8,6,7]⟩,⟨157,[4,11,21,24],[8,4,7,5,6,3,0,2,1]⟩,⟨64,[4,12,20,27],[2,6,7,4,5,3,0,1,8]⟩,⟨115,[4,12,21,26],[5,1,0,2,3,4,6,8,7]⟩,⟨95,[4,12,23,24],[1,5,0,2,3,4,6,8,7]⟩,⟨177,[4,13,22,24],[4,7,8,5,6,3,0,2,1]⟩,⟨36,[5,6,9,17],[8,4,7,5,6,3,0,1,2]⟩,⟨87,[5,6,9,18],[2,8,0,3,5,6,4,7,1]⟩,⟨102,[5,6,9,19],[8,6,7,5,4,3,2,1,0]⟩,⟨55,[5,6,9,20],[8,4,7,6,5,3,0,2,1]⟩,⟨77,[5,6,9,24],[8,4,6,7,5,2,0,3,1]⟩,⟨165,[5,6,9,26],[6,8,7,5,4,2,3,1,0]⟩,⟨115,[5,6,9,28],[7,1,8,6,4,3,5,2,0]⟩,⟨120,[5,6,11,20],[6,8,7,4,5,2,3,0,1]⟩,⟨166,[5,6,11,24],[6,8,7,5,4,2,3,1,0]⟩,⟨175,[5,6,11,28],[6,8,7,5,4,2,3,1,0]⟩,⟨36,[5,6,12,20],[0,7,8,5,6,4,3,1,2]⟩,⟨77,[5,6,12,24],[0,6,8,7,5,4,2,3,1]⟩,⟨115,[5,6,12,25],[8,5,7,6,4,3,1,2,0]⟩,⟨129,[5,6,12,27],[0,6,7,5,3,4,2,1,8]⟩,⟨58,[5,9,14,17],[8,3,0,1,6,4,5,7,2]⟩,⟨186,[5,9,14,18],[5,8,6,7,4,1,2,3,0]⟩,⟨149,[5,9,14,19],[8,2,0,1,3,4,5,7,6]⟩,⟨130,[5,9,14,20],[7,4,8,6,5,3,2,0,1]⟩,⟨70,[5,9,17,30],[8,3,0,1,2,4,5,6,7]⟩,⟨90,[5,9,18,20],[8,4,7,5,6,3,1,0,2]⟩,⟨143,[5,9,18,28],[8,3,0,1,2,4,5,6,7]⟩,⟨91,[5,9,19,20],[8,4,7,5,6,3,1,0,2]⟩,⟨150,[5,9,19,28],[8,3,0,1,2,4,5,6,7]⟩,⟨118,[5,9,20,26],[8,3,0,1,2,4,5,6,7]⟩,⟨162,[5,10,12,19],[5,8,6,7,4,1,3,2,0]⟩,⟨90,[5,10,12,20],[0,6,8,7,5,4,2,3,1]⟩,⟨177,[5,10,12,22],[7,2,0,1,3,4,6,5,8]⟩,⟨163,[5,10,19,20],[8,5,7,4,6,3,0,1,2]⟩,⟨192,[5,10,19,28],[1,8,3,0,2,6,4,5,7]⟩,⟨158,[5,10,20,24],[4,8,5,7,6,0,3,1,2]⟩,⟨160,[5,10,20,25],[8,4,7,5,6,3,0,2,1]⟩,⟨194,[5,10,22,25],[3,8,1,0,2,6,4,5,7]⟩,⟨145,[5,11,12,20],[6,3,7,4,5,2,8,0,1]⟩,⟨190,[5,11,12,22],[5,8,7,6,4,2,1,3,0]⟩,⟨157,[5,11,12,24],[0,4,1,2,3,5,8,6,7]⟩,⟨159,[5,11,20,24],[8,4,7,5,6,3,0,2,1]⟩,⟨200,[5,11,22,24],[4,8,5,6,7,0,1,2,3]⟩,⟨143,[5,12,20,26],[6,2,8,0,1,3,4,5,7]⟩,⟨150,[5,12,20,27],[6,3,7,4,5,2,0,1,8]⟩,⟨160,[5,12,22,24],[0,5,8,7,6,4,3,1,2]⟩,⟨197,[5,12,22,25],[5,1,8,0,3,2,4,6,7]⟩,⟨199,[7,12,20,24],[4,5,8,6,7,0,2,3,1]⟩,⟨189,[7,12,20,25],[8,4,7,5,6,0,2,3,1]⟩],0xc10964d66d60c35c34b68d96d7fd7ed54c2fc2eb75b74983982d90d5ad79d78c29c28b7bb7a97d97cd84d73d72d6dd6cc1dc1cb81b8db8cb80971970d2bd1fd25d19c05bedb3fb39b2dd94d8ed82d37d4fd43d31d49d3dbf9b45b63b5db51d35c6bcd1cc5be7bc3a97a8b95f93bd7dd71d29d4dcb3cd5d0dd01bdbb0fb03953d64d7cd58d70d1dd41c69cb1cc9d05cf5bcfaa3b27b1b947d2fcd7ccbc65be1bbda91a85959935d77d6bd23d47ccfd0bd07cadbd5b09afd94dd5ed52d76d6ad17d3bcc3cffcf3c63cabbc9a9db21b15941c33c2dc27c1bc03bf7be5bd9bcdbdfbd3bc7a55a3da37a31a25c0ec32c2cc26c1abebbc1bbba49b43aa1a9ba53a479a19118edb7fb25b1fa3b9f5b79b8bb3db61a95b0db13a35a0190bb73b8ab37b5bb19a8fb07a2f9ff905b66b72b78b7eb2bb4fa89b01a83afba2399f9f38f998197b96f95d95194595794b93f90f9099038f796298097a96e9399338eb8a589988d89d8918a389f89389788bd2ad1ed24d18c04becb3eb38b2cd92d8cd80d4ed42d36d48d3cd30bf8b62b5cb50b44d4cd40ca5c5dc9bce9cb9cddbb7af7a7fadfd28d1cd34c99ce1aebd46d3ace7cb7ce3c9fc57c95bb1af1a79ad9d22d16d2ecdbc93ae5c02beabf6bb5bafa19b60b5ab4eaf5a7dae9aefa77ae3a179e79ddb3cb36b2ab42addad79db88187fd33c6acd0cc4be6bc2a96a8a95e93ad7bd6fd4bd27cb2d0cd00cd3bdab0eb02952d7ad6ed62d56d3fd1bcafc67d03cf4cc7bceb26b1aaa2946d4ad3eca3c9ac5bce8cdccb8bb6af6adea7ed32d26d1ac97cdfaeacb0caeca2c98c96c72c45c43c8ac80c7eb9eabaa67a66922c68c66c5ac42c4eaae8c8d0acfed02cf2ce6cdacdec8bc82c4fc87c4bc7dba5acda6da72929ccecc2cd2cc6cb6c7fc7bac1be4bc0bd8bccbb4b9cba3a13b0cb00b24b18af4adcae8ab8a65aacacba6babfa119d59999cb8e7a94a88aa0a7ca64a709c98bd95c9389509449209278e58798c68bb87bd2dcd6ccac64be0bbca90a84958934d75d69d45d21d09d06ccdcacbd4b08afc94cd74d68d5cd50d39d15cfdcf1cc1ca9c61bc8b20b14a9c940d44d38ce5ce2cb5c9dc94c55bb0af0ad8a78d2cd20d14cd9c91ae4d08d04cfccf0ce4ce0cd8c8dc51c83c85c7cc49ba4acca73a6c928cd4cc8ccccc0cb4c81c79ac0caaca8c9cc92c90c84c7ac78c6cc3fc3db98ab4a61a6091cc62c60c54c48c3caa88cebdebbabd2bc6baeba2b96a0db06afab1eb12aeead6ae2acaa71abeab2a5faa6a0b9cf9939c58e1a8ea82a9aa76a6aa5e9c38c395693294a93e92691a8df8cc8c1875873c31c2bc25c19c01bf5be3bd7bcbbddbd1bc5a54a3ca36a30a24c30c2ac24c18c0cbe9bbfbb9a48c00bf4be8bb3bada18be2bd6bcabbebb2b9aba1a12bdcbd0bc4bb8bacba0b94a0ca52a3aa34a2ea22a46a16a10a0a9b7b41a9fa99a51a459a09108ecb7db23b1da399f4b89b77b5fb3bb0ba93b11a33a0090ab88b71b59b35b17b05a8da2d9fd904b7cb76b70b64b4db29affa87af9a81a219f199d8f8b5eb58b4caf3ae7a7baedae1a75a159e59dcb40b3ab34b28adbad59d9b22b0ab16afeaf2ae6adaab6aaaa63ac9abda69a0f9d39ca9978e6a9ea92a86a7aa62a6e9c78bcb1cb10b04af8aecae0ad4ac8abca6fab0aa4a5da099cd9c49918e0a98a8ca80a74a68a5c9c18c2a50a44a38a32a2ca20a14a0ea089b59f29fe9fc9f09e49da9d89d29c89c69cc9c29c09b49a89879858d499e99c9969909848b08b690e8ea9089028f68e48de8d28c08b48698ba8ae86797f97996d95b94f94395594993d90d9079018f597e97896c9609379318e995a94e94293691e9258e395494893c9309249188dd90c9069008f48e88e28dc8d08a489888c89b88f8808778ca8bf8748be8b28688a289688a89a88e87e8768728668a189e89289588987d8c48b987a8718b88ac8658a089c89089488887c8788708648038027f67fd7fc7f076174376073d74273c73085d85c85683f81b83e81a82182077975b77875a85b85985082782683981583881477f75577e75485a85485884e85284c84083380f83280e82d80982c80877376d74977276c74883d81982583180d7c57b97af7a37e57d97cd72b71f6ef6fb6e380183c8307ad7dd7138007f481882480c7a17d170781f83781382b8077e37df7d37bf7b37a979d7257196f56e96dd7fb83682a7d77a770d7fa7ee81e8128067cb79b70177775977d75377176b74772971d71170572371770b6ff6bd6b76ab6a76a169575f74177c7706ed6f36a575e73b77676a6f96e769f74073a72e7587527466e16db69383b82f81782380b7c37b77ae7a27e47d87cc72a71e6ee6fa6e283a82e7ff7ab7db71281682280a7fe7f279f7cf7067c27b67ac7a07aa79e7867926ca7e27d67ca7da7ce79378f6d172871c6ec6f86e07107046c86cf68d83582981d8118057e17de7d27bd7b17a879c7247186f46e86dc8348287f97d57a570c81c8108047f87ec7c97997007e07dc7d07d47c879578d6d07bc7b07a679a7a479878c7806c47227166f26e66da70a6fe6ce6c268777b76f77576975775174572771b70f7037217157096fd6bb6b56a96a66a069477a76e75d73f6eb6f16a377476875c7396f76e569d75675074473e73872c6df6d969172671a70e7026ea6f66de6c66cd68b7207147086fc6f06e46d86cc6c06856ba6b46a86a469e6926a269c69068a68467849749648a4c74c64af4ae6765fe4df4bb4de4ba66a60b60a4d34a34d24a247f46745b4733ef3cb3bf3e33d764763b5ab59359f58744f44341f4136455c343767466863965d5b75f35e742b5c15b552751b38f38334733b5a937759152535f60959d5f155736b5fc6085855e55195553534c54ad4dd4b94d14a147d4713ed3e13d544d44143542938d38137535d3693514954dc4d04653c941d3454944884c44ac4b84a04593bd41133947e46645a4723b362d57b40757950d32f47c4644584703b140532d3ee3ca3be3e23d63b239a6125623a65604f53173ec3c83bc3e03d43b03983a431564663a5aa59259e58644e44241e4126435c243667266665b6375f25e65b642a62b57a4066145633a765a64e62161f5da56f56e3fa64463864263662a61661e5ce5f05e45d856d5cc54950153f3235a859059c5845c05b457856156c53d44c44041c4104344284043a53f83215bf5b352651a38e38234633a5a737658f52335e6075ef59b55636a6065fa5e358355351735257750b32e55e4f33165ee5e25d65ca56b54753e4ff3225be5b25a658e59a58257655f56a53b55455254653c53a52e4e94e730a52451852251650a4f24fe4e638c38034433837435c36835032c3143203084db4cf4c34ab4b749f47b46f3eb3df3d344b43f43342738b37f37335b36734f4da4ce4934633c741b3434c24aa4b649e4924864573bb40f33747a46e4624563af40332b3ea3de3d23c63ba3ae3963a231344a43e43242641a40e4023a33f631f38a37e37235a36634e34233632a31231e3064914904844c14c06705f84d94b54d84b44a94a86646056044cd49d4cc49c47946145546d6416355a559958d58144943d41940d63f5bd43166e6626336575b15ed5e14253e93c53b93dd3d15bb5af52151538937d3413355a33716035975eb55136558b51f3595f660257f5df51354f34d4bf4d74b34a74cb49b47746b44743b42f4233e73db3cf38737b36f36335734b48f4d64ca45f4173c333f48e4824be4b24a649a45340b3b733347846045446c6275754013ad57350732947645e45246a3ff3ab3276406345a459858c58044843c41840c63d5bc43066c6606556315ec5e05b042462557440065464861b6195d45695683f463e63263c6306246186105c860e55d3a15ea5de5d25675c65434fb53931d5a259658a57e5ba5ae57256655b53744643a41640a42e4223fe3f239f31b3e83c43b83dc3d03ac60c55c3a039455a4ef3113e63c23b63da3ce3aa39e39230f5b95ad52051438837c3403345a13706015e959555036458951d3586005f45dd57d54d51134c5715053285e85dc5d05c45655415384f931c5b85ac5a059458857c5705645595355584ed31054e54c5405365345284e34e130451e51251c5105044f84ec4e038637a33e33236e36235634a32631a30e3024d54c94bd4b14a549947546944543942d4213e53d93cd38537936d3613553494d44c848d45d4153c133d4bc4b04a449848c4804514093b533147446845c4503fd3a932544443842c4204144083fc3f039d3193e43d83cc3c03b43a839c39030d38437836c36035434833c33032431830c3002b026326225625d25c25013d16d13716c13113c1361301242ec29329228d28c1611602f92f82e62cf2ce2ab27b2aa27a28128018515b18415a2f72f52e02c92c82872862a52752a427418b15518a1542ea2f62e42f42de2e82e22dc2d02bd2bc29f26f29e26e29926929826819117f17914919017e1781482cd2c72bb24b23322724522d2211191071010f52ae2cc2c62ba23f23910d2912a927928529d26d24923d1e91dd1d31c72152091fd0ef0e30bf0a70b309b2612a829c2311d120d0d726025429027828426c2251c52010cb28b27f2a327329726724323721320f2031e31d71cd1c10e90dd0b90ad0a109525b2a229622b2071cb0d125a24e28a27e27226621f1fb1bf0c515f18315918915318f17d17714711710b0ed0e10d50c90e70db0cf0c306305d05704b04103b03502913b18e0bd0b703f16b13518817c1050a50ab03916a12f1821760ff0b109f03313a13412e12215e1581521460f30990930272cb2c52b924a23222624422c2201181061000f42ca2c42b82ac23e23810c24823022423c1b91f108f24222a21e2361ef1b30891161040fe0f210a08d08701b2a729b28f27728326b24723b1e71db1d21c62142081fc0ee0e20be0a60b209a2a629a25f22f1cf20b0d628e27628226a25e2522231c31ff0ca24623a22e2221b71f008e1e61da1d01c41ce1c21b619e1aa0762122061fa20a1fe1ee1ab1a707d0ec0e00bc0a40b00980d40c808c07407b0152a129528927d27126524123521120e2021e11d51cc1c00e80dc0b80ac0a00942a02942592292051c90d028827c27026425824c21d1f91bd0c424023422821c1ed1b108821020c2002041f81ec1ad1a507c1e01d41ca1be1c81bc1b01a41980700e60da0b60aa09e0920ce0c208607a06e00f18d18717b18117515d1571511451151090eb0df0d30c70e50d90cd0c106105b05504904003a03402818c1390bb0b503d18617a1691331030a30a903718017416812d0fd0af09d03115c15615014413813212c1200f10970910251141081020fc0f008b0850190ea0de0d20c60ba0a20ae09608a0720790130e40d80cc0c00b40a809c09008407806c00d06005a05404803e03803202603c03603002401801200c000⟩
def D2 : FData := ⟨3,4,2048,[0,1,2,4,6,8,9,10,12,14,16,17,18,20,22,24,25,26,28,30],[1,2,3,4,5,8,9,10,11,12,13,16,17,18,19,20,21,24,25,26,27,28,29],[18056,14472,18000,14416],[⟨206,[1,2,4,8,16],[9,0,1,7,8,4,5,6,2,3]⟩,⟨207,[1,2,4,8,17],[9,0,1,8,7,4,5,6,3,2]⟩,⟨210,[1,2,4,8,18],[0,9,8,7,6,5,4,3,2,1]⟩,⟨216,[1,2,4,8,19],[9,8,1,7,5,4,3,6,2,0]⟩,⟨211,[1,2,4,8,24],[9,1,2,8,5,4,6,7,3,0]⟩,⟨212,[1,2,4,8,25],[9,1,2,8,5,4,6,7,3,0]⟩,⟨229,[1,2,4,8,26],[0,9,7,8,6,5,4,2,3,1]⟩,⟨222,[1,2,4,8,27],[9,0,2,1,3,4,5,7,6,8]⟩,⟨208,[1,2,4,9,17],[9,0,1,7,8,4,5,6,2,3]⟩,⟨212,[1,2,4,9,18],[9,0,1,7,3,4,5,6,2,8]⟩,⟨217,[1,2,4,9,19],[9,8,1,7,5,4,3,6,2,0]⟩,⟨214,[1,2,4,9,24],[9,1,2,8,5,4,6,7,3,0]⟩,⟨219,[1,2,4,9,26],[9,1,2,0,3,4,6,7,5,8]⟩,⟨212,[1,2,4,10,18],[0,9,8,6,7,5,4,3,1,2]⟩,⟨222,[1,2,4,10,19],[8,9,1,7,5,3,4,6,2,0]⟩,⟨229,[1,2,4,10,20],[9,0,1,2,3,4,5,6,7,8]⟩,⟨232,[1,2,4,10,21],[9,1,7,3,5,4,6,2,8,0]⟩,⟨237,[1,2,4,10,24],[9,0,1,2,3,4,5,6,7,8]⟩,⟨243,[1,2,4,10,25],[9,8,1,7,5,4,3,6,2,0]⟩,⟨244,[1,2,4,10,28],[1,8,9,7,5,6,3,4,2,0]⟩,⟨236,[1,2,4,10,29],[0,8,7,6,4,5,3,2,1,9]⟩,⟨234,[1,2,4,11,21],[9,7,8,5,6,4,2,3,0,1]⟩,⟨241,[1,2,4,11,24],[9,0,1,2,3,4,5,6,7,8]⟩,⟨249,[1,2,4,11,28],[9,0,1,2,3,4,5,6,7,8]⟩,⟨213,[1,2,8,12,16],[9,1,3,0,7,4,6,5,8,2]⟩,⟨214,[1,2,8,12,17],[9,1,3,0,7,4,6,5,8,2]⟩,⟨237,[1,2,8,12,18],[0,9,7,8,6,5,4,3,2,1]⟩,⟨233,[1,2,8,12,19],[9,7,3,1,5,4,2,6,8,0]⟩,⟨253,[1,2,8,12,20],[0,7,9,8,6,5,2,4,3,1]⟩,⟨241,[1,2,8,12,21],[9,1,7,8,5,4,6,3,2,0]⟩,⟨218,[1,2,8,12,24],[8,1,0,9,7,3,6,4,5,2]⟩,⟨219,[1,2,8,12,25],[9,2,5,8,6,4,7,3,0,1]⟩,⟨244,[1,2,8,12,26],[0,9,7,8,6,5,4,3,2,1]⟩,⟨236,[1,2,8,12,27],[9,7,6,8,5,4,2,3,1,0]⟩,⟨228,[1,2,8,16,28],[8,0,3,1,2,4,5,6,7,9]⟩,⟨238,[1,2,8,18,20],[0,9,7,6,8,5,4,1,3,2]⟩,⟨258,[1,2,8,18,28],[7,9,2,1,0,3,4,6,5,8]⟩,⟨239,[1,2,8,20,24],[9,1,3,0,2,4,6,5,8,7]⟩,⟨269,[1,2,8,20,26],[0,9,6,8,7,5,4,3,1,2]⟩,⟨240,[1,2,9,18,20],[9,0,3,6,2,4,5,1,7,8]⟩,⟨240,[1,2,10,12,18],[0,9,7,8,6,5,4,3,2,1]⟩,⟨251,[1,2,10,12,19],[9,8,5,7,6,4,3,2,0,1]⟩,⟨269,[1,2,10,12,20],[9,0,2,1,3,4,5,6,7,8]⟩,⟨273,[1,2,10,12,21],[9,0,2,1,3,4,5,6,7,8]⟩,⟨258,[1,2,10,12,24],[9,7,5,8,6,4,3,2,0,1]⟩,⟨259,[1,2,10,12,25],[9,7,5,8,6,4,3,2,0,1]⟩,⟨260,[1,2,10,18,28],[7,9,2,0,1,3,4,5,6,8]⟩,⟨270,[1,2,10,20,24],[0,9,6,8,7,5,4,3,1,2]⟩,⟨283,[1,2,12,20,24],[0,8,9,6,7,5,4,2,3,1]⟩,⟨279,[1,2,12,20,26],[0,9,8,6,7,5,4,2,3,1]⟩,⟨220,[1,8,10,12,16],[9,5,6,8,7,4,3,0,1,2]⟩,⟨221,[1,8,10,12,17],[9,5,6,8,7,4,3,0,1,2]⟩,⟨257,[1,8,10,12,18],[0,9,7,8,6,5,4,3,2,1]⟩,⟨250,[1,8,10,12,19],[9,7,6,8,5,4,3,2,1,0]⟩,⟨221,[1,8,10,12,24],[8,0,1,9,7,3,4,5,6,2]⟩,⟨223,[1,8,10,12,25],[9,5,6,8,7,4,3,0,1,2]⟩,⟨230,[1,8,10,16,20],[9,2,3,0,1,4,5,7,6,8]⟩,⟨257,[1,8,10,16,28],[8,2,3,0,1,4,5,7,6,9]⟩,⟨274,[1,8,10,18,20],[0,9,6,8,7,5,4,3,2,1]⟩,⟨293,[1,8,10,18,28],[7,9,3,6,0,4,2,1,5,8]⟩,⟨246,[1,8,10,20,24],[9,6,5,8,7,4,3,1,0,2]⟩,⟨261,[1,8,18,20,24],[8,0,1,7,9,4,3,5,6,2]⟩,⟨294,[1,10,12,18,20],[9,1,2,0,3,4,5,6,7,8]⟩,⟨281,[1,10,12,18,24],[9,6,5,8,7,4,2,0,1,3]⟩,⟨226,[2,4,8,9,16],[9,0,1,8,7,5,6,4,3,2]⟩,⟨227,[2,4,8,9,17],[9,0,1,8,7,5,6,4,3,2]⟩,⟨253,[2,4,8,9,18],[9,0,1,8,2,5,6,4,3,7]⟩,⟨256,[2,4,8,9,19],[9,7,1,8,5,2,6,4,3,0]⟩,⟨228,[2,4,8,9,24],[9,1,2,8,5,6,7,4,3,0]⟩,⟨248,[2,4,8,9,26],[7,9,0,8,6,4,5,3,2,1]⟩,⟨262,[2,4,8,16,25],[9,0,1,7,8,5,6,3,4,2]⟩,⟨264,[2,4,8,17,24],[9,0,1,8,7,5,6,4,3,2]⟩,⟨267,[2,4,9,17,24],[9,0,1,7,8,5,6,3,4,2]⟩,⟨23,[2,5,8,16],[8,1,4,6,7,5,0,2,3]⟩,⟨24,[2,5,8,17],[8,1,4,7,6,5,0,3,2]⟩,⟨38,[2,5,8,18],[8,0,5,6,3,4,1,2,7]⟩,⟨52,[2,5,8,19],[8,7,5,6,4,3,1,2,0]⟩,⟨32,[2,5,8,20],[0,7,8,6,5,3,4,2,1]⟩,⟨39,[2,5,8,24],[8,2,5,7,4,6,1,3,0]⟩,⟨40,[2,5,8,25],[8,2,5,7,4,6,1,3,0]⟩,⟨153,[2,5,8,26],[0,8,6,7,5,3,4,2,1]⟩,⟨67,[2,5,8,27],[8,0,6,1,3,4,2,5,7]⟩,⟨74,[2,5,8,28],[0,6,8,7,5,2,4,3,1]⟩,⟨25,[2,5,9,17],[8,1,4,6,7,5,0,2,3]⟩,⟨40,[2,5,9,18],[8,0,5,6,3,4,1,2,7]⟩,⟨53,[2,5,9,19],[8,7,5,6,4,3,1,2,0]⟩,⟨33,[2,5,9,20],[8,1,0,6,3,5,4,2,7]⟩,⟨42,[2,5,9,24],[8,2,5,7,4,6,1,3,0]⟩,⟨62,[2,5,9,26],[8,1,6,0,3,5,2,4,7]⟩,⟨56,[2,5,9,28],[8,2,0,1,3,6,4,5,7]⟩,⟨72,[2,5,10,18],[0,8,7,5,6,3,4,1,2]⟩,⟨67,[2,5,10,19],[8,7,6,5,4,3,2,1,0]⟩,⟨74,[2,5,10,20],[8,1,0,3,2,5,4,7,6]⟩,⟨92,[2,5,10,24],[8,0,5,2,3,4,1,6,7]⟩,⟨110,[2,5,10,25],[8,7,5,6,4,3,1,2,0]⟩,⟨114,[2,5,10,28],[1,7,8,6,4,3,5,2,0]⟩,⟨81,[2,5,11,20],[8,6,1,4,3,2,5,0,7]⟩,⟨103,[2,5,11,24],[8,0,5,2,3,4,1,6,7]⟩,⟨122,[2,5,11,28],[8,0,1,2,3,4,5,6,7]⟩,⟨33,[2,5,12,20],[0,7,8,5,6,3,4,1,2]⟩,⟨86,[2,5,12,24],[8,1,0,2,3,5,4,6,7]⟩,⟨107,[2,5,12,25],[8,1,7,6,4,5,3,2,0]⟩,⟨113,[2,5,12,26],[8,1,0,2,3,5,4,6,7]⟩,⟨124,[2,5,12,27],[8,1,0,2,3,5,4,6,7]⟩,⟨254,[2,8,9,16,20],[9,1,2,8,0,6,4,3,5,7]⟩,⟨274,[2,8,9,18,20],[9,0,2,8,1,5,4,3,6,7]⟩,⟨32,[2,8,13,16],[8,1,4,7,6,5,3,0,2]⟩,⟨33,[2,8,13,17],[8,1,4,7,6,5,3,0,2]⟩,⟨74,[2,8,13,18],[8,1,4,6,3,5,2,0,7]⟩,⟨81,[2,8,13,19],[8,6,5,7,4,2,3,1,0]⟩,⟨100,[2,8,13,20],[6,0,8,7,5,4,3,2,1]⟩,⟨74,[2,8,13,24],[0,6,4,1,3,2,5,8,7]⟩,⟨125,[2,8,13,26],[7,1,4,6,3,5,2,0,8]⟩,⟨33,[2,8,16,29],[0,7,4,1,2,3,5,6,8]⟩,⟨35,[2,8,17,20],[8,1,4,6,7,5,2,3,0]⟩,⟨55,[2,8,17,28],[8,2,3,1,0,6,5,4,7]⟩,⟨106,[2,8,18,21],[8,0,3,5,2,4,1,6,7]⟩,⟨56,[2,8,18,29],[0,7,4,2,5,3,6,1,8]⟩,⟨101,[2,8,19,20],[8,0,3,5,2,4,1,6,7]⟩,⟨120,[2,8,19,28],[8,0,3,1,2,4,5,6,7]⟩,⟨87,[2,8,20,25],[8,1,4,7,6,5,3,0,2]⟩,⟨102,[2,8,20,27],[6,0,2,1,3,4,5,7,8]⟩,⟨86,[2,8,21,24],[8,1,4,7,6,5,3,0,2]⟩,⟨134,[2,8,21,26],[1,8,5,0,2,3,4,7,6]⟩,⟨36,[2,9,12,17],[8,1,4,7,6,5,3,0,2]⟩,⟨76,[2,9,12,18],[8,1,4,6,3,5,2,0,7]⟩,⟨82,[2,9,12,19],[8,6,5,7,4,2,3,1,0]⟩,⟨87,[2,9,12,20],[2,7,8,0,5,3,6,4,1]⟩,⟨102,[2,9,12,21],[8,1,6,7,4,5,3,2,0]⟩,⟨55,[2,9,12,24],[7,1,0,8,6,5,3,4,2]⟩,⟨127,[2,9,12,26],[0,8,6,7,5,3,4,2,1]⟩,⟨58,[2,9,17,28],[8,2,3,0,1,6,4,5,7]⟩,⟨107,[2,9,18,21],[8,0,3,5,2,4,1,6,7]⟩,⟨115,[2,9,18,28],[8,0,3,1,2,4,5,6,7]⟩,⟨102,[2,9,19,20],[8,0,3,5,2,4,1,6,7]⟩,⟨123,[2,9,19,28],[8,0,3,1,2,4,5,6,7]⟩,⟨90,[2,9,20,24],[8,1,4,7,6,5,3,0,2]⟩,⟨177,[2,9,20,26],[0,8,5,7,6,3,4,1,2]⟩,⟨91,[2,9,21,24],[8,1,4,7,6,5,3,0,2]⟩,⟨147,[2,9,21,26],[8,1,3,0,2,5,4,6,7]⟩,⟨73,[2,10,13,18],[0,8,4,1,6,3,5,7,2]⟩,⟨124,[2,10,13,19],[8,7,4,6,5,3,2,0,1]⟩,⟨164,[2,10,13,20],[8,0,2,1,3,4,5,6,7]⟩,⟨121,[2,10,13,24],[1,7,5,6,4,3,2,8,0]⟩,⟨69,[2,10,18,29],[0,7,4,5,6,3,1,2,8]⟩,⟨126,[2,10,19,20],[4,8,7,5,6,3,1,0,2]⟩,⟨129,[2,10,19,28],[6,8,2,1,4,3,5,0,7]⟩,⟨165,[2,10,20,25],[8,0,3,1,2,4,5,7,6]⟩,⟨171,[2,10,21,24],[8,0,3,1,2,4,5,7,6]⟩,⟨161,[2,11,12,20],[8,0,2,1,3,4,5,6,7]⟩,⟨174,[2,11,12,21],[8,7,5,6,4,3,2,1,0]⟩,⟨161,[2,11,12,24],[5,0,1,2,3,4,8,6,7]⟩,⟨162,[2,11,20,24],[8,0,3,1,2,4,5,7,6]⟩,⟨172,[2,11,21,24],[8,7,4,6,5,3,2,0,1]⟩,⟨186,[2,12,20,25],[8,0,5,6,7,4,1,2,3]⟩,⟨149,[2,12,20,27],[2,6,7,4,5,3,0,1,8]⟩,⟨163,[2,12,21,24],[5,0,8,7,6,4,3,1,2]⟩,⟨190,[2,12,21,26],[8,0,1,3,2,4,6,5,7]⟩,⟨26,[3,5,8,16],[8,4,5,6,7,0,1,2,3]⟩,⟨27,[3,5,8,17],[8,4,5,7,6,0,1,3,2]⟩,⟨43,[3,5,8,18],[8,0,5,6,3,4,1,2,7]⟩,⟨47,[3,5,8,24],[8,5,6,7,4,1,2,3,0]⟩,⟨48,[3,5,8,25],[8,5,6,7,4,1,2,3,0]⟩,⟨61,[3,5,8,26],[8,0,6,1,3,4,2,5,7]⟩,⟨28,[3,5,9,17],[8,4,5,6,7,0,1,2,3]⟩,⟨44,[3,5,9,18],[8,0,5,6,3,4,1,2,7]⟩,⟨49,[3,5,9,24],[8,5,6,7,4,1,2,3,0]⟩,⟨65,[3,5,9,26],[8,0,6,1,3,4,2,5,7]⟩,⟨68,[3,5,10,18],[8,7,6,4,5,3,2,0,1]⟩,⟨78,[3,5,10,20],[8,0,1,2,3,4,5,6,7]⟩,⟨96,[3,5,10,24],[8,0,5,2,3,4,1,6,7]⟩,⟨111,[3,5,10,25],[8,7,5,6,4,3,1,2,0]⟩,⟨117,[3,5,10,28],[8,0,1,2,3,4,5,6,7]⟩,⟨41,[3,8,12,16],[8,5,3,0,6,1,4,7,2]⟩,⟨42,[3,8,12,17],[8,5,3,0,6,1,4,7,2]⟩,⟨86,[3,8,12,18],[0,8,6,7,5,4,3,2,1]⟩,⟨93,[3,8,12,20],[8,5,2,0,3,1,4,6,7]⟩,⟨103,[3,8,12,21],[8,5,6,7,4,1,3,2,0]⟩,⟨60,[3,8,12,24],[8,6,4,7,5,2,3,0,1]⟩,⟨62,[3,8,12,25],[8,6,4,7,5,2,3,0,1]⟩,⟨113,[3,8,12,26],[0,8,6,7,5,4,3,2,1]⟩,⟨43,[3,8,13,16],[8,5,4,7,6,1,3,0,2]⟩,⟨44,[3,8,13,17],[8,5,4,7,6,1,3,0,2]⟩,⟨78,[3,8,13,18],[8,0,5,7,2,4,3,1,6]⟩,⟨104,[3,8,13,20],[8,5,6,7,4,1,3,2,0]⟩,⟨61,[3,8,13,24],[8,6,4,7,5,2,3,0,1]⟩,⟨85,[3,8,13,26],[8,6,5,7,4,2,3,1,0]⟩,⟨59,[3,8,16,28],[8,6,3,0,1,2,4,5,7]⟩,⟨68,[3,8,16,29],[8,6,3,0,1,2,4,5,7]⟩,⟨45,[3,8,17,20],[8,5,4,6,7,1,2,3,0]⟩,⟨63,[3,8,17,28],[8,6,3,1,0,2,5,4,7]⟩,⟨89,[3,8,18,20],[0,8,6,5,7,4,1,3,2]⟩,⟨108,[3,8,18,21],[8,7,4,5,6,3,1,2,0]⟩,⟨145,[3,8,18,28],[6,8,2,1,0,3,5,4,7]⟩,⟨152,[3,8,18,29],[6,7,3,1,4,2,5,0,8]⟩,⟨94,[3,8,20,24],[8,5,3,0,2,1,4,7,6]⟩,⟨97,[3,8,20,25],[8,5,4,7,6,1,3,0,2]⟩,⟨157,[3,8,20,26],[0,8,5,7,6,4,3,1,2]⟩,⟨96,[3,8,21,24],[8,5,4,7,6,1,3,0,2]⟩,⟨146,[3,8,21,26],[8,0,3,1,2,4,5,6,7]⟩,⟨46,[3,9,12,17],[8,5,4,7,6,1,3,0,2]⟩,⟨79,[3,9,12,18],[8,1,4,6,3,5,2,0,7]⟩,⟨97,[3,9,12,20],[8,5,2,0,3,1,4,6,7]⟩,⟨105,[3,9,12,21],[8,5,6,7,4,1,3,2,0]⟩,⟨63,[3,9,12,24],[8,6,4,7,5,2,3,0,1]⟩,⟨83,[3,9,12,26],[8,1,2,0,3,5,4,6,7]⟩,⟨66,[3,9,17,28],[8,6,3,0,1,2,4,5,7]⟩,⟨91,[3,9,18,20],[8,0,3,5,2,4,1,6,7]⟩,⟨109,[3,9,18,21],[8,7,4,5,6,3,1,2,0]⟩,⟨119,[3,9,18,28],[8,0,3,1,2,4,5,6,7]⟩,⟨98,[3,9,20,24],[8,5,4,7,6,1,3,0,2]⟩,⟨144,[3,9,20,26],[8,0,3,1,2,4,5,6,7]⟩,⟨99,[3,9,21,24],[8,5,4,7,6,1,3,0,2]⟩,⟨151,[3,9,21,26],[8,0,3,1,2,4,5,6,7]⟩,⟨91,[3,10,12,18],[0,8,6,7,5,4,3,2,1]⟩,⟨157,[3,10,12,20],[8,0,2,1,3,4,5,6,7]⟩,⟨172,[3,10,12,21],[8,0,2,1,3,4,5,6,7]⟩,⟨145,[3,10,12,24],[8,6,4,7,5,3,2,0,1]⟩,⟨147,[3,10,12,25],[8,6,4,7,5,3,2,0,1]⟩,⟨152,[3,10,13,18],[6,8,2,0,5,3,4,7,1]⟩,⟨168,[3,10,13,20],[8,0,2,1,3,4,5,6,7]⟩,⟨146,[3,10,13,24],[8,6,4,7,5,3,2,0,1]⟩,⟨150,[3,10,18,28],[6,8,2,0,1,3,4,5,7]⟩,⟨142,[3,10,18,29],[8,7,2,0,1,3,4,5,6]⟩,⟨159,[3,10,20,24],[0,8,5,7,6,4,3,1,2]⟩,⟨169,[3,10,20,25],[8,0,3,1,2,4,5,7,6]⟩,⟨173,[3,10,21,24],[8,7,4,6,5,3,2,0,1]⟩,⟨199,[3,12,20,24],[0,5,8,6,7,4,2,3,1]⟩,⟨188,[3,12,20,25],[8,4,5,6,7,0,1,2,3]⟩,⟨189,[3,12,20,26],[0,8,7,5,6,4,2,3,1]⟩,⟨187,[3,12,21,24],[8,4,5,7,6,0,2,1,3]⟩,⟨193,[3,12,21,26],[8,0,1,3,2,4,6,5,7]⟩,⟨261,[8,9,16,18,20],[9,5,6,7,8,3,2,4,0,1]⟩,⟨106,[8,10,13,16],[7,2,3,0,5,4,6,8,1]⟩,⟨56,[8,10,13,17],[8,5,4,7,6,3,1,0,2]⟩,⟨121,[8,10,13,18],[8,6,5,7,4,3,2,1,0]⟩,⟨122,[8,10,13,19],[8,6,5,7,4,3,2,1,0]⟩,⟨164,[8,10,13,20],[6,1,2,0,3,4,5,8,7]⟩,⟨73,[8,10,13,24],[7,1,4,8,6,3,5,0,2]⟩,⟨86,[8,10,16,21],[0,6,4,7,1,3,2,5,8]⟩,⟨107,[8,10,16,29],[7,2,3,0,1,4,6,5,8]⟩,⟨77,[8,10,17,20],[8,3,4,1,6,5,7,2,0]⟩,⟨115,[8,10,17,28],[7,2,3,0,5,4,6,1,8]⟩,⟨167,[8,10,18,21],[8,6,4,7,5,3,2,1,0]⟩,⟨148,[8,10,18,29],[0,7,4,6,5,3,2,1,8]⟩,⟨166,[8,10,19,20],[8,1,3,0,2,4,5,6,7]⟩,⟨175,[8,10,19,28],[8,1,3,0,2,4,5,6,7]⟩,⟨165,[8,10,20,25],[6,1,2,0,3,4,5,7,8]⟩,⟨116,[8,10,21,24],[8,5,4,7,6,3,1,0,2]⟩,⟨78,[8,11,16,21],[8,4,5,6,7,2,0,3,1]⟩,⟨134,[8,11,16,28],[7,5,2,8,0,3,1,4,6]⟩,⟨79,[8,11,17,20],[8,5,4,7,6,3,1,2,0]⟩,⟨83,[8,11,17,28],[8,5,4,7,6,3,1,2,0]⟩,⟨163,[8,11,18,20],[1,8,6,0,7,4,5,3,2]⟩,⟨168,[8,11,18,21],[8,6,4,7,5,3,2,1,0]⟩,⟨190,[8,11,18,28],[5,1,2,0,3,4,8,6,7]⟩,⟨171,[8,11,20,24],[7,3,2,0,1,4,8,6,5]⟩,⟨117,[8,11,21,24],[8,5,4,7,6,3,1,0,2]⟩,⟨57,[8,17,18,20],[8,4,5,6,7,2,3,0,1]⟩,⟨130,[8,17,18,28],[7,2,3,1,0,5,4,6,8]⟩,⟨186,[8,18,20,25],[3,6,7,0,5,4,1,2,8]⟩,⟨167,[8,18,21,24],[0,5,4,7,6,3,1,8,2]⟩,⟨58,[9,10,12,17],[8,4,5,7,6,3,0,1,2]⟩,⟨130,[9,10,12,18],[0,8,6,7,5,4,3,2,1]⟩,⟨123,[9,10,12,19],[8,6,5,7,4,3,2,1,0]⟩,⟨58,[9,10,12,24],[7,0,1,8,6,3,4,5,2]⟩,⟨80,[9,10,17,20],[8,4,5,6,7,2,0,3,1]⟩,⟨84,[9,10,17,28],[8,5,4,7,6,3,1,2,0]⟩,⟨160,[9,10,18,20],[1,8,6,0,7,5,4,3,2]⟩,⟨169,[9,10,18,21],[8,6,4,7,5,3,2,1,0]⟩,⟨197,[9,10,18,28],[6,8,3,5,0,1,2,4,7]⟩,⟨170,[9,10,19,20],[8,6,4,7,5,3,2,1,0]⟩,⟨176,[9,10,19,28],[8,6,4,7,5,3,2,1,0]⟩,⟨118,[9,10,20,24],[8,5,4,7,6,3,1,0,2]⟩,⟨119,[9,10,21,24],[8,5,4,7,6,3,1,0,2]⟩,⟨143,[9,18,20,24],[8,4,5,6,7,3,0,1,2]⟩,⟨144,[9,18,21,24],[8,5,4,6,7,3,1,0,2]⟩,⟨200,[10,12,18,21],[8,2,1,3,0,7,6,5,4]⟩,⟨194,[10,12,18,25],[8,5,4,7,6,2,0,1,3]⟩,⟨192,[10,12,19,24],[8,5,4,7,6,2,0,1,3]⟩,⟨191,[10,13,18,24],[8,5,4,7,6,2,0,1,3]⟩,⟨201,[10,13,19,20],[8,5,6,4,7,0,1,2,3]⟩,⟨193,[10,13,19,24],[8,5,4,7,6,2,0,1,3]⟩,⟨200,[10,13,20,24],[4,0,1,2,3,5,8,6,7]⟩],0x425776ee635c5f88712611bdb80aecdf0c638db16e1dc4583effde9c0175ef75dac698bb12e20c2180ef8decbb18d518a374658af14e1bc3d82efede7bd58df1862cc4787307601bdf7faedde8bad8d91a2324608ab1461fc3582af5dfcbcd8bd16a2e4568b115226c33863045fbbf58a51422642f85b065f9bcb7e2eade4ba98850ea2543688d0fa1942e85303df6bc58911122043c8710d21842c851035f7bc784908a0f42083906204c168290420740c810fade1be974ef05d2bfe80cfea013f67e4fb9f53e577af69e93e279cf79eb3ca78cf09df404800ff1fc3f47e0fb1f43e477eee9d93ae76cea9d33e07b8f61ea3d0798f21e23c0778ee1da3b0758ea1d23a1740dddb5b6766eccd75ae75a6b3d65b7e6f4e29b7b86704d6da3b27616c1d6fabf716e7dcdb636aed4d97b1f636b1dbb36e6e4d0d81b87706e79cd37372ce49c735f69ed2d95b17626c3d71ac36d4d99ad3626bccfd7fb466acd49a134e694cf99d3235f6b6d5db36664c999732a644bdd8530663cc6981316624c397f2fa5ecbc9772d756eba9732de5c4b696b2d259cb295f2c6584ae95b23f4be82d039c337e92d332374c487cfd9df36e92921252466939232173ee75cd9a674a69dd39a5b45e8ad019ef3d68f91b23247484ce9a6349e9d93923b4dc9a92ba274467fcf39e337697923a5a4ac86ced9a743c8591722a4248991121a41c7cce79af414818fd1f64047f8f91cb3bc758f71ea3a4798f11da39c728e31ab3846f8db1b23746b8d51a334c689bab696cacd598ae95cab4566ac973ae65c4b616aad4596b1d632b15ce398728e41c6385702dc5aeb4d692ca58ab1161ab8560b88708e01be3786dad65a2b25612c156eabd6e8dc1b6341602da1b23606b8d619eafd6a8d41a6348688d019e338642be56cab9668cc196328648c817ab1c630c518830c610c11802fc5f0bd1782ec5aaad5742e45c0b716c2d45a0b31642c4580af15c2b4566abd55ab155aaa54fa9d532a3d46a8950aac9572aa544a954ba83560ab1542a4540a5540a9e538a614b2945209f54728c510a11412804f89e0c59872fe5ecbb99f33665cc99632ce57ca39432964fc9d98a30c5bcc11572665f8bd1762dc5a8b915325e678cd19632460cb998e2b64dcb11662bc558a915a29c4aca31422944f89d13225c4d8951264ba8f504a053826f53aa714ca96528a2d452804f69e94e89c1362684c295526a3944a884fe9e53c26e5322604928d50e9f93ba6d52e2584a89150c9d94a0931242444808c50a9f53aa6c51e2384688c1089d134a8b1142244408710c214420830f89cd35a821022003f87e0fa1f03927b0f41e43c0770ec1d43a0730e41c4352700de1b83686c0d61a8342690d019d332654c898930a5f4bc9752ca584ae94928a5049e939338660ca190318604b895926a620c21802da5549897c2f05d0b816c2d0544969642c0570ac1542a0530949482885009e1382684c09612824845c8a91121e42c869092404748291c2304048b1142204388510c210410800dd1b235c7f8ef1e234c6a8fd1e63b4688fe1f83e07a8eb1d23347a0e71ca324770f21d4398708f01d83a0720e01b83606b0d21a8340660c816e2cc438830fe1ec5386f1742f8518930d62bc3b8bf18c3085589b12e1cc5b0b214c288570aa13e23c4f0671242684b08e11418c430820fc1e83706a0ec1c83306216a2c4428810fa1e4568751883005e8a9132254388a50da2f05c0a11221a45a0b01582a0520a013a2344e0651302504808c110184420800f81e03a0700d81a0320600be16c2984f09611c2e8590a2134248450660c41681f0360740c8150221782d03b0aa1041580f0a4138250460740d82103d04e02c2e0580a810c1c82901a140260480881001e038068094048320600b0150260500901000503c0680e0180280400700a01802002000⟩
def D3 : FData := ⟨7,6,512,[0,1,2,4,6,8,10,12,14,16,17,18,20,22,24,26,28,30],[1,2,3,4,5,8,9,16,17,18,19,20,21,24,25],[18056,17608,18000,17104,17496,17048],[⟨207,[1,2,4,8,16],[9,0,1,2,8,4,5,6,7,3]⟩,⟨208,[1,2,4,8,17],[9,0,1,2,8,4,5,6,7,3]⟩,⟨212,[1,2,4,8,18],[9,0,1,2,3,4,5,6,7,8]⟩,⟨217,[1,2,4,8,19],[9,8,1,2,5,4,3,6,7,0]⟩,⟨214,[1,2,4,16,24],[9,1,2,3,0,4,6,7,5,8]⟩,⟨240,[1,2,4,18,24],[9,0,1,3,2,4,5,6,7,8]⟩,⟨221,[1,2,16,20,24],[9,2,5,6,8,4,7,3,0,1]⟩,⟨260,[1,2,18,20,24],[9,7,5,6,8,4,3,2,0,1]⟩,⟨224,[1,16,18,20,24],[9,5,6,7,8,4,3,0,1,2]⟩,⟨227,[2,4,8,16,17],[9,0,1,2,8,5,6,7,4,3]⟩,⟨24,[2,4,9,16],[8,1,2,4,7,5,6,0,3]⟩,⟨25,[2,4,9,17],[8,1,2,4,7,5,6,0,3]⟩,⟨40,[2,4,9,18],[8,0,2,5,3,4,6,1,7]⟩,⟨53,[2,4,9,19],[8,7,2,5,4,3,6,1,0]⟩,⟨33,[2,4,9,24],[8,1,2,0,3,5,6,4,7]⟩,⟨33,[2,4,16,25],[8,1,2,4,7,5,6,3,0]⟩,⟨36,[2,4,17,24],[8,1,2,4,7,5,6,3,0]⟩,⟨107,[2,4,18,25],[8,0,1,3,2,4,5,6,7]⟩,⟨102,[2,4,19,24],[8,0,1,3,2,4,5,6,7]⟩,⟨27,[2,5,9,16],[8,2,4,5,7,6,0,1,3]⟩,⟨28,[2,5,9,17],[8,2,4,5,7,6,0,1,3]⟩,⟨48,[2,5,9,18],[8,0,5,6,3,4,1,2,7]⟩,⟨54,[2,5,9,19],[8,7,5,6,4,3,1,2,0]⟩,⟨44,[2,5,9,20],[8,2,0,5,3,6,4,1,7]⟩,⟨42,[2,5,16,24],[8,2,5,3,0,6,1,4,7]⟩,⟨44,[2,5,16,25],[8,2,5,4,7,6,1,3,0]⟩,⟨46,[2,5,17,24],[8,2,5,4,7,6,1,3,0]⟩,⟨95,[2,5,18,24],[8,0,5,3,2,4,1,6,7]⟩,⟨111,[2,5,18,25],[8,0,5,3,2,4,1,6,7]⟩,⟨105,[2,5,19,24],[8,0,5,3,2,4,1,6,7]⟩,⟨91,[2,5,20,24],[8,1,0,3,2,5,4,6,7]⟩,⟨109,[2,5,20,25],[8,1,7,4,6,5,3,2,0]⟩,⟨56,[2,16,20,25],[8,2,5,4,7,6,3,1,0]⟩,⟨58,[2,17,20,24],[8,2,4,5,7,6,3,0,1]⟩,⟨148,[2,18,20,25],[8,6,5,4,7,3,2,1,0]⟩,⟨149,[2,19,20,24],[8,6,4,5,7,3,2,0,1]⟩,⟨29,[3,5,9,16],[8,4,5,6,7,0,1,2,3]⟩,⟨30,[3,5,9,17],[8,4,5,6,7,0,1,2,3]⟩,⟨50,[3,5,9,18],[8,0,5,6,3,4,1,2,7]⟩,⟨49,[3,5,16,24],[8,5,6,3,0,1,2,4,7]⟩,⟨50,[3,5,16,25],[8,5,6,4,7,1,2,3,0]⟩,⟨51,[3,5,17,24],[8,5,6,4,7,1,2,3,0]⟩,⟨99,[3,5,18,24],[8,0,5,3,2,4,1,6,7]⟩,⟨112,[3,5,18,25],[8,7,5,4,6,3,1,2,0]⟩,⟨64,[3,16,20,24],[8,6,4,5,7,2,3,0,1]⟩,⟨65,[3,16,20,25],[8,6,5,4,7,2,3,1,0]⟩,⟨66,[3,17,20,24],[8,6,4,5,7,2,3,0,1]⟩,⟨150,[3,18,20,24],[8,6,4,5,7,3,2,0,1]⟩,⟨151,[3,18,20,25],[8,6,5,4,7,3,2,1,0]⟩,⟨69,[16,18,20,25],[8,5,6,4,7,3,1,2,0]⟩,⟨70,[17,18,20,24],[8,4,5,6,7,3,0,1,2]⟩],0x4b2532793496491e8c44e250c68b41acca62b1247228e45a23108541e0b017fbe5e6ed56afd66a75ca85369567b519cc861b097aab5bac54a9f4ca4cd669389bcc65d90c82351487c3a11068040dfaf778bad58b2532f970a04d25208fe813f1ecf0753a1cce46f361108247a38f876582a948bc5b279309246a19008c3d1d0a64d2892cae451fb499acc6330580bb5aabd52a34ea5d226a381b4ce612dae968ae5428938964822d14843f1e0e452261549e49218f4dc6836198c05a2a140944e241087836180b8502c1308c421b15090441f0c8803c180b040280e090300c00⟩
def D4 : FData := ⟨15,24,128,[0,1,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30],[1,2,3,4,5,8,9,16,17],[18056,14472,17608,10440,13576,9992,18000,14416,17104,6352,13072,5904,17496,10328,17048,6296,8984,5400,13408,9824,12960,5792,8928,5344],[⟨208,[1,2,4,8,16],[9,0,1,2,3,4,5,6,7,8]⟩,⟨25,[2,4,8,17],[8,1,2,3,4,5,6,7,0]⟩,⟨28,[2,4,9,17],[8,2,3,4,5,6,7,0,1]⟩,⟨30,[2,5,9,17],[8,3,4,5,6,7,0,1,2]⟩,⟨31,[3,5,9,17],[8,4,5,6,7,0,1,2,3]⟩],0xc16aa409ce9c2190d191b6064c00⟩
def D5 : FData := ⟨19,12,512,[0,1,2,4,8,9,10,12,16,17,18,20,24,25,26,28],[1,2,4,8,9,10,12,16,17,18,20,24,25,26,28],[18056,14472,18000,14416,18049,14465,17937,14353,17986,14402,17930,14346],[⟨215,[1,2,4,8,16],[0,8,9,6,7,5,3,4,1,2]⟩,⟨216,[1,2,4,8,17],[9,0,8,7,6,4,5,3,2,1]⟩,⟨231,[1,2,4,8,24],[0,7,9,8,6,5,2,4,3,1]⟩,⟨232,[1,2,4,8,25],[9,0,7,8,6,4,5,2,3,1]⟩,⟨217,[1,2,4,9,17],[9,0,8,6,7,4,5,3,1,2]⟩,⟨222,[1,2,4,9,18],[8,9,0,6,7,3,4,5,1,2]⟩,⟨233,[1,2,4,9,24],[9,0,7,8,6,4,5,2,3,1]⟩,⟨236,[1,2,4,9,26],[9,0,7,1,3,4,5,2,6,8]⟩,⟨255,[1,2,8,12,16],[0,7,9,8,6,5,2,4,3,1]⟩,⟨241,[1,2,8,12,17],[9,0,7,8,6,4,5,3,2,1]⟩,⟨256,[1,2,8,12,20],[0,7,9,8,6,5,2,4,3,1]⟩,⟨247,[1,2,8,12,24],[0,9,7,8,6,5,4,3,2,1]⟩,⟨249,[1,2,8,12,25],[9,0,7,8,6,4,5,3,2,1]⟩,⟨285,[1,2,8,16,28],[0,8,9,6,7,5,4,2,3,1]⟩,⟨286,[1,2,8,20,24],[0,8,9,7,6,5,4,3,2,1]⟩,⟨287,[1,2,12,20,24],[0,8,9,6,7,5,4,2,3,1]⟩,⟨275,[1,8,10,16,20],[0,6,9,7,8,5,2,1,4,3]⟩,⟨101,[1,8,18,20],[0,6,8,5,7,4,1,2,3]⟩,⟨161,[1,8,18,28],[0,5,8,7,6,4,3,1,2]⟩,⟨126,[1,9,18,20],[8,0,4,5,2,3,1,6,7]⟩,⟨102,[1,10,12,18],[0,8,6,7,5,4,3,2,1]⟩,⟨120,[1,10,12,24],[0,6,8,7,5,4,2,3,1]⟩,⟨128,[1,10,12,25],[8,0,6,7,5,3,4,2,1]⟩,⟨149,[1,10,18,28],[6,8,2,0,1,3,4,5,7]⟩,⟨162,[1,10,20,24],[0,5,8,6,7,4,1,3,2]⟩,⟨166,[8,9,18,20],[1,6,8,0,7,4,5,2,3]⟩,⟨131,[8,17,18,20],[0,6,8,5,7,1,4,2,3]⟩,⟨179,[8,17,18,28],[0,5,8,6,7,3,4,1,2]⟩,⟨132,[9,10,12,17],[8,0,6,7,5,3,4,2,1]⟩,⟨136,[9,10,12,24],[0,6,7,8,5,4,2,3,1]⟩,⟨170,[9,10,17,20],[8,1,6,0,7,4,5,3,2]⟩,⟨180,[9,10,20,24],[0,5,8,7,6,4,1,3,2]⟩,⟨20,[9,18,28],[0,4,7,6,5,3,1,2]⟩],0x2bb87c1dd6b386c0ddeab7ab8db6972dc1602f751bb5c2d34798dd2d968a2cd6b958aa542734aa35127134984b223057647a52fb71ca238f970c4208ed7d3e1aae27035192c886c0635257bb7dd1248c3d5bb0c803d9d2f468b79b8d062b113697459dce6ba579fd5ca233a692c8a3b1c8fc6684bf62d2179b6e411478b6610fc793c1cacd72369b0cc60b013293439d56cab3d9bd549e31a6124863a1e8dc624aa450ab4549e4e26d54270c29448210f07036180be5d2896cb24d2b954922d14894325e2e14070431f854b45826108683d08958a8481f0f0600d160a048180a0401800⟩
def D6 : FData := ⟨20,8,2048,[0,1,2,3,4,5,8,10,12,16,17,18,19,20,21,24,26,28],[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[18056,18000,17601,17433,17090,16922,16523,16467],[⟨209,[1,2,4,8,16],[0,1,9,8,7,5,6,4,3,2]⟩,⟨211,[1,2,4,8,17],[9,0,8,1,7,4,5,3,6,2]⟩,⟨229,[1,2,4,8,19],[0,1,8,7,4,5,6,3,2,9]⟩,⟨231,[1,2,4,8,22],[1,7,9,8,5,6,2,4,3,0]⟩,⟨232,[1,2,4,8,23],[1,0,7,8,4,6,5,2,3,9]⟩,⟨234,[1,2,4,8,31],[0,1,8,7,4,5,6,3,2,9]⟩,⟨213,[1,2,4,10,16],[0,9,1,8,7,5,4,6,3,2]⟩,⟨218,[1,2,4,10,17],[9,8,1,5,7,4,3,6,0,2]⟩,⟨214,[1,2,4,10,18],[0,9,1,8,7,5,4,6,3,2]⟩,⟨219,[1,2,4,10,19],[8,9,2,0,6,3,4,7,5,1]⟩,⟨237,[1,2,4,10,20],[8,0,9,2,6,3,5,4,7,1]⟩,⟨244,[1,2,4,10,21],[8,0,9,2,6,3,5,4,7,1]⟩,⟨233,[1,2,4,10,22],[1,9,7,8,5,6,4,2,3,0]⟩,⟨236,[1,2,4,10,23],[8,9,7,1,5,3,4,2,6,0]⟩,⟨228,[1,2,4,10,24],[1,8,0,9,7,6,4,5,3,2]⟩,⟨247,[1,2,4,10,25],[9,8,1,7,5,4,3,6,2,0]⟩,⟨248,[1,2,4,10,28],[0,8,1,7,4,5,3,6,2,9]⟩,⟨249,[1,2,4,10,29],[0,8,1,7,4,5,3,6,2,9]⟩,⟨255,[1,2,4,14,16],[8,0,7,3,6,4,5,2,9,1]⟩,⟨247,[1,2,4,14,17],[8,0,9,2,6,3,5,4,7,1]⟩,⟨241,[1,2,4,14,18],[8,9,0,2,6,3,4,5,7,1]⟩,⟨249,[1,2,4,14,19],[8,9,0,2,6,3,4,5,7,1]⟩,⟨285,[1,2,4,14,24],[7,0,8,1,2,3,5,4,9,6]⟩,⟨278,[1,2,4,14,25],[6,7,8,9,5,1,3,4,2,0]⟩,⟨252,[1,2,4,16,24],[1,0,7,9,8,6,5,2,4,3]⟩,⟨253,[1,2,4,16,26],[8,0,7,3,1,4,5,2,6,9]⟩,⟨256,[1,2,4,16,30],[8,0,7,3,1,4,5,2,6,9]⟩,⟨239,[1,2,4,18,24],[0,9,1,7,8,5,4,6,3,2]⟩,⟨271,[1,2,4,18,28],[8,0,9,2,1,3,5,4,6,7]⟩,⟨286,[1,2,4,22,24],[7,0,8,1,2,3,5,4,9,6]⟩,⟨220,[1,2,5,10,16],[8,9,6,0,7,3,4,1,5,2]⟩,⟨221,[1,2,5,10,17],[9,8,0,6,7,4,3,5,1,2]⟩,⟨223,[1,2,5,10,19],[8,9,6,0,7,3,4,1,5,2]⟩,⟨257,[1,2,5,10,20],[8,0,9,2,6,4,5,3,7,1]⟩,⟨250,[1,2,5,10,22],[8,9,7,1,5,3,4,2,6,0]⟩,⟨292,[1,2,5,10,28],[6,7,9,8,5,2,4,1,3,0]⟩,⟨230,[1,2,5,16,24],[9,1,8,2,0,4,6,3,5,7]⟩,⟨257,[1,2,5,16,26],[8,0,7,3,1,4,5,2,6,9]⟩,⟨246,[1,2,5,18,24],[9,8,1,5,7,4,3,6,2,0]⟩,⟨254,[1,2,12,16,20],[0,1,9,7,8,5,6,2,4,3]⟩,⟨268,[1,2,12,20,24],[0,1,9,8,7,5,6,4,3,2]⟩,⟨275,[1,2,13,16,24],[0,7,1,9,8,5,2,6,4,3]⟩,⟨230,[1,2,16,20,24],[0,1,8,7,9,5,6,4,3,2]⟩,⟨276,[1,2,16,20,26],[8,0,6,3,7,4,5,2,1,9]⟩,⟨292,[1,2,16,21,26],[6,7,3,1,0,2,4,5,8,9]⟩,⟨238,[1,3,8,12,16],[0,2,8,9,6,5,7,4,3,1]⟩,⟨240,[1,3,8,12,17],[9,8,2,0,6,4,3,5,7,1]⟩,⟨258,[1,3,8,12,18],[7,8,0,9,6,3,2,4,5,1]⟩,⟨259,[1,3,8,12,21],[9,0,8,7,6,4,5,3,2,1]⟩,⟨277,[1,3,8,12,22],[7,9,6,8,5,3,2,4,1,0]⟩,⟨251,[1,3,8,12,25],[8,7,0,9,6,3,2,4,5,1]⟩,⟨239,[1,3,8,16,20],[9,8,2,1,0,4,3,6,5,7]⟩,⟨269,[1,3,8,16,28],[0,1,7,9,8,5,6,4,3,2]⟩,⟨270,[1,3,8,20,24],[0,1,7,9,8,5,6,4,2,3]⟩,⟨261,[1,3,12,16,20],[8,6,9,0,7,4,1,5,3,2]⟩,⟨274,[1,3,12,16,24],[0,1,7,9,8,5,6,2,4,3]⟩,⟨281,[1,3,12,20,24],[9,0,8,6,7,4,5,2,3,1]⟩,⟨246,[1,3,16,20,24],[9,0,7,6,8,4,5,3,2,1]⟩,⟨37,[1,6,8,16],[0,5,8,7,6,4,1,3,2]⟩,⟨71,[1,6,8,17],[8,4,7,1,6,3,0,5,2]⟩,⟨39,[1,6,8,18],[0,8,5,7,6,4,1,3,2]⟩,⟨153,[1,6,8,19],[1,0,6,7,3,5,4,2,8]⟩,⟨154,[1,6,8,25],[7,4,6,8,5,2,0,3,1]⟩,⟨155,[1,6,8,27],[1,0,6,7,3,5,4,2,8]⟩,⟨41,[1,6,10,16],[0,8,5,7,6,4,1,3,2]⟩,⟨60,[1,6,10,17],[7,8,6,0,5,3,2,4,1]⟩,⟨42,[1,6,10,18],[0,8,5,7,6,4,1,3,2]⟩,⟨62,[1,6,10,19],[7,8,6,0,5,3,2,4,1]⟩,⟨86,[1,6,10,20],[7,0,8,2,5,3,4,6,1]⟩,⟨113,[1,6,10,21],[7,0,8,2,5,3,4,6,1]⟩,⟨59,[1,6,10,24],[0,8,6,7,5,4,2,3,1]⟩,⟨133,[1,6,10,25],[8,7,5,6,4,3,1,2,0]⟩,⟨134,[1,6,10,28],[0,7,1,6,3,4,5,2,8]⟩,⟨135,[1,6,10,29],[0,7,1,6,3,4,5,2,8]⟩,⟨156,[1,6,16,24],[1,4,6,8,7,5,0,3,2]⟩,⟨93,[1,6,16,26],[0,8,5,6,7,4,1,3,2]⟩,⟨94,[1,6,18,24],[0,8,5,6,7,4,1,3,2]⟩,⟨167,[1,6,18,28],[7,0,8,2,1,3,4,5,6]⟩,⟨38,[1,7,8,16],[0,1,5,7,6,4,8,3,2]⟩,⟨72,[1,7,8,17],[8,4,7,1,6,3,0,5,2]⟩,⟨74,[1,7,8,18],[1,0,4,7,2,5,8,3,6]⟩,⟨153,[1,7,8,24],[8,4,6,1,2,3,0,5,7]⟩,⟨155,[1,7,8,25],[8,4,6,7,5,3,0,2,1]⟩,⟨125,[1,7,8,26],[6,7,4,8,5,2,0,3,1]⟩,⟨106,[1,7,10,16],[0,7,3,6,5,4,8,2,1]⟩,⟨73,[1,7,10,17],[8,7,4,5,6,3,0,1,2]⟩,⟨56,[1,7,10,18],[7,8,4,1,6,3,0,5,2]⟩,⟨164,[1,7,10,20],[0,6,2,5,3,4,8,1,7]⟩,⟨134,[1,7,10,24],[8,7,5,6,4,3,1,2,0]⟩,⟨135,[1,7,10,25],[8,7,5,6,4,3,1,2,0]⟩,⟨195,[1,7,10,28],[5,6,8,7,4,2,1,3,0]⟩,⟨92,[1,7,16,24],[0,1,5,6,7,4,8,3,2]⟩,⟨121,[1,7,16,26],[7,8,5,2,0,3,1,4,6]⟩,⟨171,[1,7,18,24],[0,7,3,5,6,4,8,2,1]⟩,⟨286,[1,8,11,16,20],[0,2,6,8,7,5,4,9,3,1]⟩,⟨52,[1,8,15,16],[0,1,5,7,6,4,3,8,2]⟩,⟨67,[1,8,15,17],[7,2,6,0,5,3,4,8,1]⟩,⟨81,[1,8,15,18],[0,1,5,6,3,4,2,8,7]⟩,⟨39,[1,8,16,22],[0,1,5,7,2,4,3,6,8]⟩,⟨40,[1,8,16,23],[0,1,5,7,2,4,3,6,8]⟩,⟨53,[1,8,16,31],[0,1,5,7,2,4,3,6,8]⟩,⟨60,[1,8,17,22],[7,2,6,1,4,3,5,0,8]⟩,⟨62,[1,8,17,30],[7,2,6,1,4,3,5,0,8]⟩,⟨75,[1,8,18,20],[1,4,8,7,6,5,3,0,2]⟩,⟨76,[1,8,18,21],[1,6,2,7,4,5,3,0,8]⟩,⟨82,[1,8,18,29],[0,7,3,6,5,4,2,1,8]⟩,⟨127,[1,8,19,28],[1,2,6,8,4,5,3,7,0]⟩,⟨133,[1,8,22,25],[0,1,5,8,2,4,3,7,6]⟩,⟨35,[1,10,12,16],[1,0,7,8,6,5,4,3,2]⟩,⟨76,[1,10,12,17],[1,0,6,8,3,5,4,2,7]⟩,⟨55,[1,10,12,18],[1,8,4,7,6,5,3,0,2]⟩,⟨127,[1,10,12,19],[8,7,2,0,5,3,4,6,1]⟩,⟨120,[1,10,12,22],[1,6,8,7,4,5,2,3,0]⟩,⟨128,[1,10,12,23],[1,0,6,7,3,5,4,2,8]⟩,⟨36,[1,10,12,24],[1,0,7,8,6,5,4,3,2]⟩,⟨82,[1,10,12,25],[6,1,7,8,4,2,5,3,0]⟩,⟨101,[1,10,13,16],[0,7,2,8,5,4,3,6,1]⟩,⟨126,[1,10,13,17],[8,2,7,0,5,3,6,4,1]⟩,⟨120,[1,10,13,18],[0,7,2,8,5,4,3,6,1]⟩,⟨128,[1,10,13,19],[8,7,4,6,5,3,2,0,1]⟩,⟨161,[1,10,13,20],[0,6,2,5,3,4,1,8,7]⟩,⟨184,[1,10,13,22],[6,5,8,7,4,3,1,2,0]⟩,⟨102,[1,10,13,24],[0,7,2,8,5,4,3,6,1]⟩,⟨86,[1,10,16,22],[7,0,4,2,1,3,6,5,8]⟩,⟨107,[1,10,16,23],[0,7,3,6,1,4,2,5,8]⟩,⟨87,[1,10,16,28],[1,0,6,8,7,5,4,3,2]⟩,⟨102,[1,10,16,29],[0,7,3,6,1,4,2,5,8]⟩,⟨116,[1,10,17,22],[7,8,4,1,6,3,5,2,0]⟩,⟨165,[1,10,17,28],[0,7,2,8,1,4,3,5,6]⟩,⟨77,[1,10,18,20],[1,8,4,7,6,5,3,2,0]⟩,⟨115,[1,10,18,21],[0,7,3,6,5,4,2,1,8]⟩,⟨130,[1,10,18,28],[1,7,4,8,6,5,3,2,0]⟩,⟨123,[1,10,18,29],[0,7,3,6,5,4,2,1,8]⟩,⟨165,[1,10,19,20],[0,6,2,5,3,4,1,8,7]⟩,⟨196,[1,10,19,28],[0,5,1,8,3,4,2,7,6]⟩,⟨90,[1,10,20,24],[1,0,6,8,7,5,4,2,3]⟩,⟨162,[1,10,20,25],[0,7,2,8,1,4,3,6,5]⟩,⟨177,[1,10,21,24],[8,1,6,0,7,3,5,2,4]⟩,⟨145,[1,10,22,24],[1,6,3,7,4,5,2,8,0]⟩,⟨185,[1,10,22,25],[0,6,2,8,1,4,3,7,5]⟩,⟨147,[1,10,23,24],[1,6,3,7,4,5,2,8,0]⟩,⟨161,[1,11,16,28],[0,1,6,8,7,4,5,3,2]⟩,⟨162,[1,11,20,24],[0,1,6,8,7,4,5,2,3]⟩,⟨93,[1,14,16,24],[7,1,5,2,0,3,8,4,6]⟩,⟨166,[1,14,18,20],[0,6,8,5,7,4,1,2,3]⟩,⟨157,[1,14,18,24],[7,0,4,2,1,3,8,5,6]⟩,⟨103,[1,15,16,24],[0,1,5,6,7,4,8,3,2]⟩,⟨172,[1,15,18,24],[7,0,4,2,1,3,8,5,6]⟩,⟨92,[1,16,22,24],[7,1,5,2,0,3,4,8,6]⟩,⟨110,[1,16,23,24],[0,1,5,6,7,4,3,8,2]⟩,⟨77,[1,18,20,24],[1,0,6,7,8,5,4,2,3]⟩,⟨165,[1,18,21,24],[0,7,3,5,6,4,2,8,1]⟩,⟨45,[3,5,9,16],[8,0,7,5,6,4,3,1,2]⟩,⟨46,[3,5,9,17],[8,0,7,5,6,4,3,1,2]⟩,⟨63,[3,5,9,18],[8,7,0,6,5,3,4,2,1]⟩,⟨137,[3,5,9,22],[8,6,7,5,4,2,3,1,0]⟩,⟨79,[3,5,9,24],[8,0,6,1,3,4,2,5,7]⟩,⟨83,[3,5,9,26],[8,0,6,1,3,4,2,5,7]⟩,⟨140,[3,5,9,30],[8,0,6,1,3,4,2,5,7]⟩,⟨57,[3,5,10,16],[7,8,5,0,6,3,1,4,2]⟩,⟨58,[3,5,10,17],[8,7,0,5,6,3,4,1,2]⟩,⟨130,[3,5,10,20],[7,0,8,2,5,4,3,6,1]⟩,⟨123,[3,5,10,22],[7,8,6,1,4,3,2,5,0]⟩,⟨196,[3,5,10,28],[5,6,8,7,4,1,2,3,0]⟩,⟨131,[3,5,14,16],[7,6,8,4,5,2,3,0,1]⟩,⟨136,[3,5,14,17],[8,6,7,4,5,2,3,0,1]⟩,⟨132,[3,5,14,18],[7,8,6,4,5,3,2,0,1]⟩,⟨179,[3,5,14,24],[7,0,5,2,3,4,1,8,6]⟩,⟨181,[3,5,14,25],[8,0,5,2,3,4,1,7,6]⟩,⟨77,[3,5,16,24],[8,0,6,3,1,4,2,5,7]⟩,⟨79,[3,5,16,25],[8,0,6,5,7,4,2,3,1]⟩,⟨130,[3,5,16,26],[7,0,6,3,1,4,2,5,8]⟩,⟨132,[3,5,16,30],[7,0,6,3,1,4,2,5,8]⟩,⟨80,[3,5,17,24],[8,0,6,5,7,4,2,3,1]⟩,⟨84,[3,5,17,26],[8,7,1,4,6,3,5,2,0]⟩,⟨141,[3,5,17,30],[8,0,6,3,1,4,2,5,7]⟩,⟨118,[3,5,18,24],[8,7,1,4,6,3,5,2,0]⟩,⟨119,[3,5,18,25],[8,7,1,4,6,3,5,2,0]⟩,⟨178,[3,5,18,28],[7,6,8,4,5,2,3,1,0]⟩,⟨180,[3,5,22,24],[7,0,5,2,3,4,1,8,6]⟩,⟨183,[3,5,22,25],[8,0,5,3,2,4,1,7,6]⟩,⟨89,[3,6,12,16],[2,0,8,7,5,6,4,3,1]⟩,⟨145,[3,6,12,17],[7,6,8,0,5,2,3,4,1]⟩,⟨91,[3,6,12,18],[7,8,0,2,5,3,4,6,1]⟩,⟨147,[3,6,12,21],[7,6,8,0,5,2,3,4,1]⟩,⟨185,[3,6,12,25],[5,7,6,8,4,1,2,3,0]⟩,⟨94,[3,6,16,24],[7,8,5,2,0,3,1,4,6]⟩,⟨97,[3,6,16,26],[0,8,5,6,7,4,1,3,2]⟩,⟨157,[3,6,16,28],[1,0,8,6,7,5,4,3,2]⟩,⟨98,[3,6,18,24],[0,8,5,6,7,4,1,3,2]⟩,⟨144,[3,6,18,28],[6,8,0,2,1,3,4,5,7]⟩,⟨159,[3,6,20,24],[1,0,8,6,7,5,4,3,2]⟩,⟨169,[3,6,20,26],[7,8,0,2,1,3,4,5,6]⟩,⟨186,[3,12,16,21],[3,1,5,7,0,6,2,4,8]⟩,⟨163,[3,12,16,22],[2,1,8,7,0,6,3,4,5]⟩,⟨143,[3,12,17,20],[7,5,8,0,6,1,4,2,3]⟩,⟨192,[3,12,17,22],[7,5,8,0,6,2,4,3,1]⟩,⟨160,[3,12,17,24],[1,2,7,8,0,6,3,5,4]⟩,⟨194,[3,12,17,26],[5,7,0,8,6,2,4,1,3]⟩,⟨203,[3,12,21,26],[1,7,2,8,0,4,5,6,3]⟩,⟨202,[3,12,22,25],[5,8,6,7,4,2,3,1,0]⟩,⟨167,[3,13,16,20],[0,1,6,4,7,5,8,3,2]⟩,⟨166,[3,13,16,24],[8,7,2,1,0,3,6,4,5]⟩,⟨179,[3,13,16,26],[5,7,4,8,6,1,0,3,2]⟩,⟨144,[3,13,17,20],[8,1,7,4,6,5,0,3,2]⟩,⟨170,[3,13,17,24],[8,0,5,6,7,4,1,3,2]⟩,⟨180,[3,13,18,24],[5,7,4,8,6,1,0,2,3]⟩,⟨200,[3,13,20,24],[4,5,2,1,3,0,8,7,6]⟩,⟨171,[3,16,20,25],[7,6,1,3,0,2,4,5,8]⟩,⟨165,[3,16,20,26],[7,6,1,3,0,2,4,5,8]⟩,⟨196,[3,16,21,26],[5,6,3,2,0,1,4,7,8]⟩,⟨118,[3,17,20,24],[8,0,6,5,7,4,3,2,1]⟩,⟨178,[3,17,20,26],[7,0,5,3,6,4,2,1,8]⟩,⟨0,[6,9,16],[3,4,7,6,5,1,0,2]⟩,⟨2,[6,9,17],[7,3,6,4,5,0,1,2]⟩,⟨19,[6,9,19],[0,1,6,5,2,4,3,7]⟩,⟨1,[6,11,16],[3,7,4,6,5,1,0,2]⟩,⟨16,[6,11,17],[1,0,5,4,2,3,7,6]⟩,⟨3,[6,11,18],[3,7,4,6,5,1,0,2]⟩,⟨16,[6,11,20],[3,7,1,5,2,4,0,6]⟩,⟨14,[6,11,21],[6,7,5,4,3,2,1,0]⟩,⟨2,[6,16,25],[1,3,6,4,2,0,5,7]⟩,⟨3,[6,16,27],[1,0,6,4,2,3,5,7]⟩,⟨17,[6,17,24],[4,3,5,7,6,0,1,2]⟩,⟨18,[6,17,26],[6,0,5,2,4,3,1,7]⟩,⟨6,[6,18,25],[0,7,5,3,1,2,4,6]⟩,⟨7,[6,18,29],[2,6,0,5,4,3,1,7]⟩,⟨12,[6,19,28],[2,1,7,5,3,4,6,0]⟩,⟨16,[7,16,25],[7,3,5,4,6,0,2,1]⟩,⟨18,[7,17,24],[7,3,5,4,6,0,2,1]⟩,⟨12,[7,17,26],[6,7,4,3,5,1,2,0]⟩,⟨180,[7,18,20,24],[3,0,5,6,7,8,4,1,2]⟩,⟨15,[7,18,25],[7,6,4,3,5,1,2,0]⟩,⟨20,[7,18,28],[3,4,7,6,5,0,1,2]⟩,⟨11,[15,17,24],[0,1,4,3,2,7,5,6]⟩,⟨19,[16,22,25],[3,4,6,5,7,2,1,0]⟩,⟨80,[17,18,20,24],[0,1,7,6,8,4,5,3,2]⟩,⟨18,[17,22,24],[1,3,5,6,7,4,0,2]⟩],0x76aed1d83ac752ea1cdfa3f36e9fd1ba772ee7dc9ba2f35e9bcd39674ce89cf3926a7d4ba7f4ee95d0fa3f46e85e87d2f99f32e55d2ba173ae4599f37e77cff97f27e57d4da7b51e9bd0da4f4768bd0799b3767eced93b2f656afd69abbd8faed65ec7596add67ac3d86aad59aafd5ea9dc4f85f1be0bc6b82703e05beb8970ade7bcb756d3dcbb3771ecbdb7b0efadedc0b7f6eede5bab7cef5e03bf776ef1dd399d3da6f4ef9af3ba6b4e698d2fe5f4b695d29a4fc9e92cbbd772e75ccb7a3bc6f39f1da371cee93d07a4740e71cc798728e419d736e65cfb9772ae4dce79af3de63cb794f25d46a5d4de9b53ea4db93716dad99b2b696c290d23e4747ee33c1f88f09e31c1b88708e03c037c6f1de1ba373ecfda3b876cec9d837df03defbff77ef3dd7dcdb3b706d8da1b2360606bed7faf75e6bbd75b5eebbd6dae75a6b8d65ac35426f4dc99d3325f4bc95b5269cd43a6742691d19a2740e64cf99b33a64ccb9952d258daf95d6cad74b39616b6594b19612b255daa9572a6671cf39a730e59ca39269ad44a594f29a524c8389b1261cc738db1a633c478af18e29c4386706613c238268ad07a2f4168ed0fa1b3f7025fcbe97b2f25dcba9712dddcbb6970ed9dbcb5717dffc2782f0de03c1f85f11e07c6789f15e1fbe77eef7df7acf55eadd6babf58ea9ddfbaf79eedde3bd774e718db1bebe37a700df9bb3786e8cf49db3726accc9d93926a4c4b8d726db5b9b836fad8da943e93d17a3f41e85d23a2746e81e5ecbc9692b25249d9392523ac6d5dabb172ae45b873646c849191f212c5d82aff61ac1d80b1962ac4d85b03622c3d7caf75fabed56ab3556ad558aaf552a6d4ca9b13225d4b89510ea1549a8f516a0d48a8d512a052ca57cae95529e4dc979278e91b1debcd76aeb5eabc574a534e61c43686f09a92d24a4148a8ff22e3f48e90f21a3d75169ad41a6341690d15a234067acc59ab3964acb594b3c670cd19832c650c9190313e38c6f8d712e22c358cb15630c518830c60ac25843045a2b1764ecd583af55ceb956ab2562ac1562ab754aad54aa6750a9d52aa6548a89d06a2d46e87503a173ef015fabe57aaf15daba570adedcab8b6d6d95bab55179ff43680d0ba2342682d07a0746689d15a1f3e67ecf79f72ce55cb595f2b658ca99df3ae79cf19db3d674c71cdb9bfc017e2f85e8bc1762e85c7b916dee05bfb716c2d44f29d736a69cea9c532a694c249c8b90f23e41c9191321646c81ad0598b23626c0d90b11602bc571ae15a2b0559ab1542a4540a714c698528a414668a50ca2341284d019f34628950aa21422815009f13c274ce89c136268cd0991301c737f6fce79b73866eedd9cb3668b91121a42c808ff23244c8a90f212414839031fa3e47d8f71e63c4778eb1ea3b4748b515e2cc558b115a2a438a6f4dab8c6fae11bab9c6f8db1ca3746c8931162444488f10e20c4688510214527e4f65dcba9652aa5149b93524a39c6b91720a4547a84716e19c1b8c714e09c4b7f700e15c0b8870edf1bdb7e6fad75aea5c6b896d2b3596b4d61aab576a8ce5a6b4c69a93125b4b49490da134968ed21a3345682d11a032c6578ad95329c4d8971268e51a9ddbcb766f4dd5bc374652e2d4428c512a2943a8650aa013fa84506a0940a7e4fa9f13da794f09e93ba754ec9d138a6f6e09b9b9a724de9b53726c4b495d2ca584aa9592a23866ecd9a4a4848a91123a4648690521240450c9f13b696d69a9b45668cb1a9343664ca9a5344684ce99131c634c4985b04604c297d2f353aa154a27c538a314227435a694cea9b506a494d28a4f4a09391ab34666cfd9ed3d678cfd1f23d8770f51da3c4748738e61dc37c6f0d619e338632f215e2b85f09e14e2985b096358690ce1843165ecc99743065ccbe16b0de13c4785f0fe0fc3384710e15c3b837394708d91ba2664ac919032263f88b11b21c3ec858f3354688cd1823145f4c91852ea5c8bd16a0dc2382f04e0fc0f8330860ac1183b0369732e2584a89412664c490913222404788e31a630c598a30c610c1989304620c3985302600bf97e2fa5f0bd98e11a1e8bc9772ec5e0ba97431822c4508911021c4308510820c410811001fc3f07d0f81ec3d0790f01dc3b0750e81cc390710e01bcb716f0dc1b436066cd6197351692d1da8341690d19a0338660ca19031e630c4183309610c017c2964fca7d43a9e50ca393b2f135e69ccfaf035c698cf2e95d0b85702d85a2b2560ab1572aa550ad0590b015c2b0550a814ca98520a2140a804f09c134a614d09812ca584a092520a3946286508a2944282500a484808e118228440861082084007e4f79f83dc7c0ef1e93c27a0f01d83a0724e09b93626a4d099930c644bb1892f2604bf1712d2584ae1592a25309a12c248524a093c272394760dd1c83706a0cd198310568a51782b04e0b41482503684d0ca1144687d0ba0f4428750aa0d4e41c03706c0d41a033061cc8177310600bf9782e05a0989292424648a10c2224047e1091f23c44606c0b8210320540f81301e0740880d0b015a2b0540a51482804e89c132254488718ea1b63886d0d2196328610ab1462e8590aa1342884906b09618c2188b0f620c3985b07614c199302504808c112214440841001f43e07808a1041a82d0620a41e83904a074108190e81c2364700d81a0324640c01702c0548a11502804c0901122043c8710d2184248410b21441c8311102003c0700d01802c0500901001c0300500981201504404c0d00e0400600880c02002804000⟩
def D7 : FData := ⟨21,2,512,[0,1,2,4,5,8,10,12,16,17,18,20,21,24,26,28],[1,2,3,4,6,8,9,12,16,17,18,19,20,22,24,25,28],[18056,17601],[⟨210,[1,2,4,8,16],[0,9,1,8,7,5,4,6,3,2]⟩,⟨212,[1,2,4,8,17],[9,0,8,1,7,4,5,3,6,2]⟩,⟨222,[1,2,4,8,19],[8,9,2,1,5,3,4,7,6,0]⟩,⟨229,[1,2,4,8,20],[1,9,0,8,2,6,4,5,3,7]⟩,⟨232,[1,2,4,8,22],[1,9,7,8,5,6,4,2,3,0]⟩,⟨235,[1,2,4,8,28],[0,7,9,8,6,5,2,4,3,1]⟩,⟨242,[1,2,4,12,16],[0,9,8,7,6,5,4,3,2,1]⟩,⟨219,[1,2,4,12,17],[9,1,8,5,7,4,6,3,0,2]⟩,⟨243,[1,2,4,12,18],[0,9,8,7,6,5,4,3,2,1]⟩,⟨236,[1,2,4,12,19],[9,0,8,6,2,4,5,3,1,7]⟩,⟨219,[1,2,4,12,20],[8,1,9,0,7,3,6,4,5,2]⟩,⟨236,[1,2,4,12,22],[8,0,9,1,2,3,5,4,6,7]⟩,⟨248,[1,2,4,12,24],[9,1,8,7,5,4,6,3,2,0]⟩,⟨249,[1,2,4,12,25],[9,1,8,7,5,4,6,3,2,0]⟩,⟨237,[1,2,4,16,24],[0,9,1,7,8,5,4,6,3,2]⟩,⟨248,[1,2,4,16,28],[8,1,9,2,0,3,6,4,5,7]⟩,⟨240,[1,2,4,18,24],[0,9,1,7,8,5,4,6,3,2]⟩,⟨259,[1,2,4,18,28],[7,9,1,2,0,3,4,6,5,8]⟩,⟨272,[1,2,4,20,24],[0,9,8,6,7,5,4,3,2,1]⟩,⟨273,[1,2,4,22,24],[0,9,8,6,7,5,4,3,2,1]⟩,⟨271,[1,2,12,16,20],[0,9,7,6,8,5,4,1,3,2]⟩,⟨280,[1,2,12,20,24],[0,9,6,8,7,5,4,2,1,3]⟩,⟨245,[1,2,16,20,24],[0,9,6,7,8,5,4,3,1,2]⟩,⟨253,[1,4,8,16,18],[0,9,1,7,8,5,6,2,4,3]⟩,⟨269,[1,4,8,18,24],[9,2,8,0,1,4,3,5,7,6]⟩,⟨276,[1,4,12,16,18],[0,9,7,6,8,5,2,1,4,3]⟩,⟨257,[1,4,16,18,24],[0,9,1,7,8,5,6,4,3,2]⟩,⟨292,[1,4,16,18,28],[7,9,0,3,6,4,5,2,1,8]⟩,⟨38,[1,6,8,16],[0,8,5,7,6,4,1,3,2]⟩,⟨72,[1,6,8,17],[8,0,7,1,6,3,4,5,2]⟩,⟨40,[1,6,8,18],[0,8,5,7,6,4,1,3,2]⟩,⟨67,[1,6,8,19],[7,8,6,1,4,3,2,5,0]⟩,⟨74,[1,6,8,20],[1,8,0,7,2,5,4,3,6]⟩,⟨153,[1,6,8,24],[8,0,6,1,2,3,4,5,7]⟩,⟨155,[1,6,8,25],[8,0,6,7,5,3,4,2,1]⟩,⟨125,[1,6,8,28],[6,0,7,8,5,2,4,3,1]⟩,⟨106,[1,6,12,16],[0,8,7,6,5,4,3,2,1]⟩,⟨73,[1,6,12,17],[8,0,7,5,6,3,4,1,2]⟩,⟨107,[1,6,12,18],[0,8,7,6,5,4,3,2,1]⟩,⟨124,[1,6,12,19],[7,8,0,2,5,3,4,6,1]⟩,⟨56,[1,6,12,20],[7,0,8,1,6,3,4,5,2]⟩,⟨134,[1,6,12,24],[8,1,7,6,4,3,5,2,0]⟩,⟨135,[1,6,12,25],[8,1,7,6,4,3,5,2,0]⟩,⟨92,[1,6,16,24],[0,8,5,6,7,4,1,3,2]⟩,⟨121,[1,6,16,28],[7,1,8,2,0,3,5,4,6]⟩,⟨95,[1,6,18,24],[0,8,5,6,7,4,1,3,2]⟩,⟨148,[1,6,18,28],[6,8,0,2,1,3,4,5,7]⟩,⟨171,[1,6,20,24],[0,8,7,5,6,4,3,2,1]⟩,⟨271,[1,8,12,16,18],[9,7,1,0,8,4,5,6,3,2]⟩,⟨74,[1,8,16,22],[1,8,4,7,6,5,3,2,0]⟩,⟨73,[1,8,17,22],[8,0,4,2,1,3,6,5,7]⟩,⟨76,[1,8,18,20],[1,8,4,7,6,5,3,2,0]⟩,⟨127,[1,8,18,28],[1,7,4,8,6,5,3,2,0]⟩,⟨126,[1,8,19,20],[8,4,7,1,6,3,5,0,2]⟩,⟨128,[1,8,19,28],[8,6,2,1,4,3,5,0,7]⟩,⟨113,[1,8,22,24],[1,8,4,7,6,5,3,0,2]⟩,⟨135,[1,8,22,25],[8,1,5,0,2,3,4,7,6]⟩,⟨164,[1,12,16,22],[0,8,6,5,7,4,1,3,2]⟩,⟨165,[1,12,18,20],[0,8,6,5,7,4,1,3,2]⟩,⟨177,[1,12,18,24],[8,2,7,0,1,3,4,6,5]⟩,⟨190,[1,12,22,24],[0,8,5,7,6,4,2,1,3]⟩,⟨114,[1,16,22,24],[0,8,5,6,7,4,3,1,2]⟩,⟨115,[1,18,20,24],[0,8,5,6,7,4,3,1,2]⟩,⟨32,[3,4,8,16],[0,8,1,7,6,4,5,3,2]⟩,⟨33,[3,4,8,17],[8,0,7,1,6,4,3,5,2]⟩,⟨74,[3,4,8,20],[0,8,1,6,3,4,5,2,7]⟩,⟨81,[3,4,8,22],[1,8,6,7,4,5,2,3,0]⟩,⟨125,[3,4,8,28],[0,7,1,6,3,4,5,2,8]⟩,⟨43,[3,4,9,16],[8,0,7,5,6,4,3,1,2]⟩,⟨44,[3,4,9,17],[8,0,7,5,6,4,3,1,2]⟩,⟨68,[3,4,9,18],[8,7,0,6,5,3,4,2,1]⟩,⟨61,[3,4,9,20],[8,0,7,6,5,4,3,2,1]⟩,⟨138,[3,4,9,22],[8,0,7,5,2,4,3,1,6]⟩,⟨78,[3,4,9,24],[8,1,7,0,2,5,3,4,6]⟩,⟨85,[3,4,9,28],[8,1,7,6,4,5,3,2,0]⟩,⟨106,[3,4,12,16],[7,8,0,2,5,3,4,6,1]⟩,⟨56,[3,4,12,17],[8,0,7,5,6,4,3,1,2]⟩,⟨107,[3,4,12,18],[7,8,0,2,5,3,4,6,1]⟩,⟨73,[3,4,12,20],[7,0,8,1,6,4,3,5,2]⟩,⟨124,[3,4,12,22],[0,8,7,6,5,4,3,2,1]⟩,⟨121,[3,4,12,24],[8,1,7,6,4,5,3,2,0]⟩,⟨122,[3,4,12,25],[8,1,7,6,4,5,3,2,0]⟩,⟨86,[3,4,16,24],[0,8,1,6,7,4,5,3,2]⟩,⟨78,[3,4,16,25],[8,0,6,5,7,4,2,3,1]⟩,⟨134,[3,4,16,28],[7,1,8,2,0,5,3,4,6]⟩,⟨79,[3,4,17,24],[8,1,7,4,6,5,3,2,0]⟩,⟨83,[3,4,17,28],[8,1,7,4,6,5,3,2,0]⟩,⟨91,[3,4,18,24],[0,8,1,6,7,4,5,3,2]⟩,⟨152,[3,4,18,25],[6,8,1,2,0,3,5,4,7]⟩,⟨147,[3,4,18,28],[6,8,1,2,0,3,5,4,7]⟩,⟨171,[3,4,20,24],[7,8,0,2,1,3,4,5,6]⟩,⟨117,[3,4,20,25],[8,1,7,4,6,5,3,2,0]⟩,⟨172,[3,4,22,24],[0,8,7,5,6,4,3,2,1]⟩,⟨182,[3,4,22,25],[8,0,5,3,2,4,1,7,6]⟩,⟨108,[3,6,12,16],[0,8,7,6,5,4,3,2,1]⟩,⟨152,[3,6,12,17],[8,6,7,4,5,3,2,0,1]⟩,⟨109,[3,6,12,18],[0,8,7,6,5,4,3,2,1]⟩,⟨152,[3,6,12,20],[7,6,8,0,5,2,3,4,1]⟩,⟨146,[3,6,12,24],[0,8,6,7,5,4,3,2,1]⟩,⟨182,[3,6,12,25],[0,8,6,7,1,4,3,2,5]⟩,⟨96,[3,6,16,24],[0,8,5,6,7,4,1,3,2]⟩,⟨146,[3,6,16,28],[6,8,0,2,1,3,4,5,7]⟩,⟨99,[3,6,18,24],[0,8,5,6,7,4,1,3,2]⟩,⟨151,[3,6,18,28],[6,8,0,2,1,3,4,5,7]⟩,⟨173,[3,6,20,24],[0,8,7,5,6,4,3,2,1]⟩,⟨167,[3,12,16,20],[0,8,6,5,7,4,1,3,2]⟩,⟨168,[3,12,16,22],[0,8,6,5,7,4,1,3,2]⟩,⟨144,[3,12,17,20],[8,0,7,5,6,4,1,3,2]⟩,⟨169,[3,12,17,24],[8,0,5,6,7,4,1,3,2]⟩,⟨191,[3,12,20,24],[0,8,5,7,6,4,2,1,3]⟩,⟨193,[3,12,20,25],[8,0,7,5,6,4,2,3,1]⟩,⟨116,[3,16,20,24],[0,8,5,6,7,4,3,1,2]⟩,⟨117,[3,16,20,25],[8,0,6,5,7,4,3,2,1]⟩,⟨119,[3,17,20,24],[8,0,6,5,7,4,3,2,1]⟩,⟨100,[4,8,16,19],[6,8,1,0,7,5,4,3,2]⟩,⟨87,[4,8,17,18],[2,8,1,7,0,5,3,6,4]⟩,⟨161,[4,8,17,22],[2,8,0,7,1,4,3,6,5]⟩,⟨164,[4,8,19,20],[2,8,0,7,1,4,3,6,5]⟩,⟨195,[4,8,19,28],[1,8,0,5,3,4,2,6,7]⟩,⟨184,[4,8,22,25],[2,8,0,6,1,4,3,5,7]⟩,⟨93,[4,9,16,18],[8,2,7,5,0,3,1,4,6]⟩,⟨104,[4,9,16,19],[8,6,0,5,7,4,1,3,2]⟩,⟨97,[4,9,17,18],[8,2,7,5,0,3,1,4,6]⟩,⟨157,[4,9,18,24],[8,2,7,0,1,3,4,6,5]⟩,⟨168,[4,9,19,24],[8,2,7,0,1,3,4,6,5]⟩,⟨164,[4,12,16,19],[6,8,0,1,7,4,5,3,2]⟩,⟨165,[4,12,17,18],[6,8,0,1,7,4,5,2,3]⟩,⟨121,[4,16,18,25],[8,6,0,5,7,4,3,2,1]⟩,⟨164,[4,16,19,24],[6,2,7,1,0,3,4,8,5]⟩,⟨195,[4,16,19,28],[6,8,0,3,5,4,2,1,7]⟩,⟨130,[4,17,18,24],[0,8,1,6,7,5,4,3,2]⟩,⟨196,[4,17,18,28],[6,8,0,3,5,4,1,2,7]⟩,⟨1,[6,9,16],[0,7,4,6,5,1,3,2]⟩,⟨3,[6,9,17],[7,0,6,4,5,3,1,2]⟩,⟨9,[6,9,19],[6,7,5,3,4,2,0,1]⟩,⟨16,[6,9,20],[0,7,1,5,2,4,3,6]⟩,⟨14,[6,9,28],[1,7,5,6,3,2,4,0]⟩,⟨167,[6,12,16,17],[6,8,0,1,7,4,5,3,2]⟩,⟨168,[6,12,16,19],[6,8,0,1,7,4,5,3,2]⟩,⟨169,[6,12,17,18],[6,8,0,1,7,4,5,2,3]⟩,⟨144,[6,12,17,20],[7,0,8,1,6,4,5,2,3]⟩,⟨16,[6,16,25],[7,0,5,4,6,3,2,1]⟩,⟨18,[6,17,24],[7,0,5,4,6,3,2,1]⟩,⟨12,[6,17,28],[6,1,7,3,5,4,2,0]⟩,⟨7,[6,18,25],[0,7,5,3,1,2,4,6]⟩,⟨11,[6,19,24],[3,7,4,6,5,1,0,2]⟩,⟨13,[6,19,28],[5,7,1,2,3,4,0,6]⟩,⟨15,[6,20,25],[7,1,6,3,5,4,2,0]⟩,⟨178,[12,17,18,20],[0,8,6,5,7,1,4,3,2]⟩,⟨20,[12,17,22],[2,7,0,6,1,3,5,4]⟩,⟨20,[12,19,20],[4,7,2,1,3,5,0,6]⟩,⟨21,[12,22,25],[3,7,5,6,4,2,1,0]⟩,⟨14,[16,22,25],[1,7,2,4,0,3,5,6]⟩,⟨84,[17,18,20,24],[0,7,1,6,8,4,3,5,2]⟩,⟨12,[17,22,24],[0,7,4,5,6,3,1,2]⟩,⟨20,[19,20,24],[0,4,1,3,2,7,5,6]⟩],0x9b4d66932984ba5b2c95caa532893c96471f8ec8637198bc56270782c0e02ff7ebee4d24914823d1c8d4622d14894421f0e8642e15087cbddeaf378c1a0902803f9f8fa7c3d9e8f2783b9d8eb753a5d0e67238dc4e170379badc6d35db2d86b355a6d4693459ecd65b2586c762afd82bd5dadd72b556aad66b157aa54ea54fa7546a14ca6d2ed06733194c86331184c05f2f12a9147a4d168d44ae970b65a2c960ae562a950a652289409e4e26930964a249208e46229108642a0d088240a00fc7d3d9e4ea773997cba5b2c95ca2552993c964d248dc6a33389bcda6b329a4ce633091c8245218fc763d1c8c45e7c3d1e0ec74391c0dc6c351a0cc6431180bc5c2d160ac54291409c4c251208c44211007c3c1d0e06c34190c05c2c150a450271288c421f0e85c2a1b0c84c1e1106898482210078381a0c058281208038180a0481c10060200c0400⟩
def D8 : FData := ⟨23,2,64,[0,1,2,4,8,10,12,16,17,18,20,24,26,28],[1,2,4,8,9,16,17,18,20,24,25],[18056,18000],[⟨216,[1,2,4,8,16],[9,0,8,1,7,4,5,3,6,2]⟩,⟨217,[1,2,4,8,17],[9,0,8,1,7,4,5,3,6,2]⟩,⟨222,[1,2,4,8,18],[8,9,0,1,7,3,4,5,6,2]⟩,⟨232,[1,2,4,8,24],[9,0,7,1,3,4,5,2,6,8]⟩,⟨234,[1,2,4,8,25],[9,0,7,8,6,4,5,2,3,1]⟩,⟨233,[1,2,4,16,24],[9,0,7,3,1,4,5,2,6,8]⟩,⟨251,[1,2,4,18,24],[9,8,1,5,7,4,3,6,2,0]⟩,⟨241,[1,2,8,16,20],[9,0,7,1,8,4,5,6,3,2]⟩,⟨273,[1,2,8,20,24],[9,8,2,0,1,4,3,5,7,6]⟩,⟨250,[1,2,16,20,24],[9,0,7,6,8,4,5,3,2,1]⟩,⟨126,[1,8,18,20],[8,0,4,1,2,3,5,6,7]⟩,⟨129,[1,18,20,24],[8,0,6,5,7,3,4,2,1]⟩,⟨256,[2,4,8,16,17],[9,0,7,1,8,5,2,6,4,3]⟩,⟨52,[2,4,9,16],[8,0,7,5,6,4,3,1,2]⟩,⟨53,[2,4,9,17],[8,0,7,5,6,4,3,1,2]⟩,⟨67,[2,4,9,18],[8,7,0,6,5,3,4,2,1]⟩,⟨81,[2,4,9,24],[8,0,6,1,3,4,2,5,7]⟩,⟨81,[2,4,16,25],[8,0,6,5,7,4,2,3,1]⟩,⟨82,[2,4,17,24],[8,0,6,5,7,4,2,3,1]⟩,⟨124,[2,4,18,25],[8,7,1,4,6,3,5,2,0]⟩,⟨102,[2,8,17,20],[8,0,6,1,7,4,5,3,2]⟩,⟨174,[2,8,20,25],[8,0,5,7,6,4,3,1,2]⟩,⟨103,[2,9,16,20],[8,0,6,5,7,4,1,3,2]⟩,⟨105,[2,9,17,20],[8,0,6,5,7,4,1,3,2]⟩,⟨172,[2,9,20,24],[8,7,2,0,1,3,4,6,5]⟩,⟨122,[2,16,20,25],[8,0,6,5,7,4,3,2,1]⟩,⟨123,[2,17,20,24],[8,0,6,5,7,4,3,2,1]⟩,⟨132,[8,17,18,20],[8,0,6,1,7,5,3,4,2]⟩,⟨11,[9,18,20],[7,0,3,4,2,1,5,6]⟩,⟨141,[17,18,20,24],[7,0,6,1,8,3,4,2,5]⟩,⟨13,[18,20,25],[7,0,5,4,6,3,2,1]⟩],0x3ceb8db5cf1bedae9d32c2eb2aa279a48a07de71a61651344f49038d30a206144080⟩
def D9 : FData := ⟨28,4,1024,[0,1,2,3,4,5,8,10,12,16,18,20,24,26,28],[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],[18056,14472,18000,14416],[⟨211,[1,2,4,8,16],[9,0,8,1,2,4,5,3,6,7]⟩,⟨218,[1,2,4,8,18],[9,8,1,2,5,4,3,6,7,0]⟩,⟨247,[1,2,4,8,22],[8,0,9,1,2,3,5,4,6,7]⟩,⟨221,[1,2,4,10,18],[8,9,2,0,1,3,4,7,5,6]⟩,⟨245,[1,2,4,10,20],[8,0,9,2,1,3,5,4,7,6]⟩,⟨250,[1,2,4,10,22],[8,9,0,1,2,3,4,5,6,7]⟩,⟨214,[1,2,5,8,16],[9,0,8,1,2,4,5,3,6,7]⟩,⟨221,[1,2,5,8,18],[9,8,0,2,6,4,3,5,7,1]⟩,⟨224,[1,2,5,10,18],[9,8,0,6,7,4,3,5,1,2]⟩,⟨237,[1,2,8,12,16],[9,8,2,0,1,4,3,5,7,6]⟩,⟨245,[1,2,8,12,18],[0,8,1,9,7,5,3,4,6,2]⟩,⟨258,[1,2,8,12,20],[9,1,8,7,5,4,6,3,2,0]⟩,⟨277,[1,2,8,12,22],[8,0,9,7,1,4,5,3,2,6]⟩,⟨241,[1,2,8,13,16],[9,8,2,0,1,4,3,5,7,6]⟩,⟨250,[1,2,8,13,18],[9,8,2,0,6,4,3,5,7,1]⟩,⟨240,[1,3,8,12,16],[9,8,2,0,1,4,3,5,7,6]⟩,⟨260,[1,3,8,12,20],[9,0,8,7,6,4,5,3,2,1]⟩,⟨71,[1,6,8,16],[8,4,7,1,2,3,0,5,6]⟩,⟨60,[1,6,8,18],[7,8,6,1,0,3,2,5,4]⟩,⟨64,[1,6,10,18],[7,8,6,0,1,3,2,4,5]⟩,⟨116,[1,6,10,20],[7,0,8,2,1,3,4,6,5]⟩,⟨72,[1,7,8,16],[8,4,7,1,2,3,0,5,6]⟩,⟨73,[1,7,8,18],[8,7,4,2,5,3,0,6,1]⟩,⟨69,[1,7,10,18],[7,8,4,1,2,3,0,5,6]⟩,⟨272,[1,8,10,16,20],[9,1,7,0,8,4,5,6,3,2]⟩,⟨273,[1,8,10,16,21],[9,1,7,0,8,4,5,6,3,2]⟩,⟨153,[1,8,14,16],[1,4,6,8,7,5,3,0,2]⟩,⟨113,[1,8,14,18],[7,0,4,1,2,3,5,8,6]⟩,⟨67,[1,8,15,16],[7,2,6,0,1,3,4,8,5]⟩,⟨124,[1,8,15,18],[7,0,4,1,2,3,5,8,6]⟩,⟨76,[1,8,18,20],[1,0,6,7,8,5,3,4,2]⟩,⟨126,[1,8,18,21],[8,2,7,1,0,3,5,6,4]⟩,⟨115,[1,10,12,18],[0,7,1,8,6,4,3,5,2]⟩,⟨175,[1,10,12,22],[0,6,8,7,5,4,2,3,1]⟩,⟨129,[1,10,13,18],[8,7,4,6,5,3,2,0,1]⟩,⟨228,[2,3,4,8,16],[9,8,0,1,2,4,3,5,6,7]⟩,⟨258,[2,3,4,8,20],[8,7,9,1,0,3,2,4,6,5]⟩,⟨260,[2,3,4,12,20],[8,7,9,0,1,3,2,4,5,6]⟩,⟨257,[2,3,8,12,16],[9,8,2,0,1,4,3,5,7,6]⟩,⟨293,[2,3,8,12,20],[9,6,8,7,5,2,1,4,3,0]⟩,⟨285,[2,4,7,8,16],[1,0,8,6,7,5,4,9,2,3]⟩,⟨39,[2,4,8,17],[8,0,7,2,5,4,3,6,1]⟩,⟨74,[2,4,8,19],[0,1,7,6,4,5,3,2,8]⟩,⟨81,[2,4,8,23],[1,0,6,7,5,4,2,3,8]⟩,⟨47,[2,4,9,17],[8,0,7,5,6,4,3,1,2]⟩,⟨60,[2,4,9,18],[8,7,1,6,4,3,5,2,0]⟩,⟨61,[2,4,9,19],[8,7,1,6,4,3,5,2,0]⟩,⟨133,[2,4,9,22],[7,0,8,5,2,4,3,1,6]⟩,⟨138,[2,4,9,23],[8,6,7,5,4,2,3,1,0]⟩,⟨73,[2,4,10,19],[7,8,2,1,4,3,6,5,0]⟩,⟨113,[2,4,10,21],[0,7,1,6,4,3,5,2,8]⟩,⟨124,[2,4,10,23],[0,7,1,6,4,3,5,2,8]⟩,⟨85,[2,4,11,21],[8,0,7,2,5,4,3,6,1]⟩,⟨135,[2,4,11,22],[7,8,0,5,2,3,4,1,6]⟩,⟨42,[2,5,8,17],[8,0,7,2,5,4,3,6,1]⟩,⟨56,[2,5,8,19],[8,7,1,2,4,3,5,6,0]⟩,⟨55,[2,5,8,20],[8,1,7,2,4,5,3,6,0]⟩,⟨120,[2,5,8,22],[7,0,8,1,2,4,3,5,6]⟩,⟨49,[2,5,9,17],[8,0,7,5,6,4,3,1,2]⟩,⟨64,[2,5,9,18],[8,7,0,6,5,3,4,2,1]⟩,⟨65,[2,5,9,19],[8,7,1,6,4,3,5,2,0]⟩,⟨63,[2,5,9,20],[8,1,7,6,4,5,3,2,0]⟩,⟨137,[2,5,9,22],[8,0,7,5,2,4,3,1,6]⟩,⟨69,[2,5,10,19],[8,7,1,6,4,3,5,2,0]⟩,⟨115,[2,5,10,20],[7,0,8,2,1,4,3,6,5]⟩,⟨129,[2,5,10,22],[7,8,6,1,4,3,2,5,0]⟩,⟨83,[2,5,11,20],[8,7,0,5,2,3,4,1,6]⟩,⟨140,[2,5,11,22],[8,7,6,5,4,3,2,1,0]⟩,⟨58,[2,5,12,20],[7,2,8,0,1,6,3,4,5]⟩,⟨123,[2,5,12,22],[7,0,8,1,2,4,3,5,6]⟩,⟨161,[2,7,8,20],[2,0,5,7,6,4,8,3,1]⟩,⟨149,[2,7,12,20],[7,6,8,0,1,3,2,4,5]⟩,⟨92,[2,8,12,17],[8,7,2,0,5,3,4,6,1]⟩,⟨114,[2,8,12,19],[8,7,2,0,5,3,4,6,1]⟩,⟨121,[2,8,12,21],[1,0,6,7,5,4,3,2,8]⟩,⟨122,[2,8,12,23],[1,0,6,7,5,4,3,2,8]⟩,⟨103,[2,8,13,17],[8,7,2,0,5,3,4,6,1]⟩,⟨122,[2,8,13,19],[8,7,2,0,5,3,4,6,1]⟩,⟨161,[2,8,13,20],[5,7,2,0,1,3,4,8,6]⟩,⟨184,[2,8,13,22],[7,0,8,6,1,4,3,2,5]⟩,⟨174,[2,8,15,20],[2,0,5,7,6,4,3,8,1]⟩,⟨86,[2,8,17,20],[8,7,2,1,0,3,5,4,6]⟩,⟨164,[2,8,19,20],[2,0,5,7,6,4,3,8,1]⟩,⟨96,[2,9,12,17],[8,7,2,0,5,3,4,6,1]⟩,⟨116,[2,9,12,18],[0,7,1,8,6,3,4,5,2]⟩,⟨117,[2,9,12,19],[8,7,2,0,5,3,4,6,1]⟩,⟨145,[2,9,12,20],[8,1,7,6,4,5,3,2,0]⟩,⟨146,[2,9,12,21],[8,1,7,6,4,5,3,2,0]⟩,⟨185,[2,9,12,22],[7,0,8,6,1,4,2,3,5]⟩,⟨182,[2,9,12,23],[8,5,7,6,4,1,3,2,0]⟩,⟨190,[2,11,12,20],[1,0,7,5,6,4,8,2,3]⟩,⟨36,[3,5,8,16],[8,0,7,1,2,4,3,5,6]⟩,⟨46,[3,5,8,17],[8,0,7,2,5,4,3,6,1]⟩,⟨58,[3,5,8,18],[8,7,0,2,5,3,4,6,1]⟩,⟨136,[3,5,8,22],[8,6,7,1,4,2,3,5,0]⟩,⟨51,[3,5,9,17],[8,0,7,5,6,4,3,1,2]⟩,⟨66,[3,5,9,18],[8,7,0,6,5,3,4,2,1]⟩,⟨139,[3,5,9,22],[8,6,7,5,4,2,3,1,0]⟩,⟨70,[3,5,10,18],[8,7,0,5,6,3,4,1,2]⟩,⟨84,[3,5,10,20],[8,0,7,2,5,4,3,6,1]⟩,⟨141,[3,5,10,22],[8,7,6,5,4,3,2,1,0]⟩,⟨59,[3,6,8,16],[7,8,6,0,1,3,2,4,5]⟩,⟨63,[3,6,8,18],[7,8,6,1,0,3,2,5,4]⟩,⟨145,[3,6,8,20],[7,6,8,1,0,2,3,5,4]⟩,⟨66,[3,6,10,18],[7,8,6,0,1,3,2,4,5]⟩,⟨119,[3,6,10,20],[7,8,0,1,2,3,4,5,6]⟩,⟨150,[3,6,12,20],[7,6,8,0,1,2,3,4,5]⟩,⟨95,[3,8,12,17],[8,7,2,0,5,3,4,6,1]⟩,⟨115,[3,8,12,18],[8,7,2,0,5,3,4,6,1]⟩,⟨148,[3,8,12,21],[8,1,7,6,4,5,3,2,0]⟩,⟨175,[3,8,12,22],[7,8,1,0,2,3,4,5,6]⟩,⟨102,[3,8,13,16],[8,7,2,0,1,3,4,6,5]⟩,⟨105,[3,8,13,17],[8,7,2,0,5,3,4,6,1]⟩,⟨123,[3,8,13,18],[8,7,2,0,5,3,4,6,1]⟩,⟨149,[3,8,13,20],[8,0,7,6,5,4,3,2,1]⟩,⟨181,[3,8,13,22],[8,5,7,6,4,1,3,2,0]⟩,⟨134,[3,8,14,16],[6,7,5,8,0,2,3,1,4]⟩,⟨83,[3,8,14,18],[0,8,5,7,6,4,3,1,2]⟩,⟨190,[3,8,14,20],[7,5,1,0,3,2,4,8,6]⟩,⟨91,[3,8,17,20],[8,7,2,1,0,3,5,4,6]⟩,⟨130,[3,8,18,20],[8,7,2,1,0,3,5,4,6]⟩,⟨132,[3,8,18,21],[8,7,4,1,6,3,5,2,0]⟩,⟨99,[3,9,12,17],[8,7,2,0,5,3,4,6,1]⟩,⟨119,[3,9,12,18],[8,7,2,0,5,3,4,6,1]⟩,⟨150,[3,9,12,20],[8,0,7,6,5,4,3,2,1]⟩,⟨151,[3,9,12,21],[8,1,7,6,4,5,3,2,0]⟩,⟨183,[3,9,12,22],[8,5,7,6,4,1,3,2,0]⟩,⟨84,[3,10,12,18],[0,8,5,7,6,4,3,1,2]⟩,⟨197,[3,10,12,20],[8,5,7,6,4,2,1,3,0]⟩,⟨176,[3,10,12,22],[0,8,6,7,5,4,3,2,1]⟩,⟨141,[3,10,13,18],[7,8,4,6,1,3,2,0,5]⟩,⟨2,[6,8,17],[7,3,6,2,4,0,5,1]⟩,⟨16,[6,8,19],[1,0,5,6,4,3,2,7]⟩,⟨4,[6,9,17],[7,3,6,4,5,0,1,2]⟩,⟨6,[6,9,18],[7,6,3,5,4,0,2,1]⟩,⟨8,[6,9,19],[7,6,3,5,4,0,2,1]⟩,⟨7,[6,10,19],[6,7,5,1,3,2,4,0]⟩,⟨15,[6,10,21],[6,0,7,2,4,3,5,1]⟩,⟨10,[6,11,21],[7,0,6,2,4,3,5,1]⟩,⟨3,[7,8,17],[7,3,6,2,4,0,5,1]⟩,⟨179,[7,8,18,20],[2,0,5,6,7,8,3,4,1]⟩,⟨5,[7,9,17],[7,3,6,4,5,0,1,2]⟩,⟨7,[7,9,18],[7,6,3,5,4,0,2,1]⟩,⟨20,[7,10,20],[2,0,4,6,5,7,3,1]⟩,⟨171,[8,10,17,20],[8,1,6,0,7,4,5,3,2]⟩,⟨174,[8,11,16,21],[8,1,6,0,7,4,5,3,2]⟩,⟨172,[8,11,17,20],[8,6,1,7,0,3,2,4,5]⟩,⟨19,[8,14,17],[0,4,6,7,5,2,1,3]⟩,⟨14,[8,14,19],[6,7,2,0,4,3,5,1]⟩,⟨9,[8,15,17],[7,0,3,1,5,4,6,2]⟩,⟨79,[8,17,18,20],[1,0,6,7,8,3,5,4,2]⟩,⟨16,[8,17,22],[1,3,5,6,7,2,4,0]⟩,⟨119,[9,10,12,18],[0,7,1,8,6,4,3,5,2]⟩,⟨183,[9,10,12,22],[6,0,5,8,2,3,4,1,7]⟩,⟨173,[9,10,17,20],[8,1,6,0,7,4,5,3,2]⟩,⟨8,[9,14,17],[7,0,3,1,5,4,6,2]⟩,⟨15,[9,14,18],[0,6,4,7,5,3,1,2]⟩,⟨10,[9,14,19],[7,6,3,5,4,2,0,1]⟩,⟨18,[9,18,20],[0,1,6,5,7,3,4,2]⟩,⟨11,[9,18,21],[7,2,6,4,0,1,5,3]⟩,⟨12,[10,12,19],[7,6,2,0,4,3,5,1]⟩,⟨13,[10,12,23],[1,0,5,6,4,3,2,7]⟩,⟨13,[10,13,19],[7,6,3,5,4,2,0,1]⟩,⟨20,[10,13,20],[4,6,2,0,1,3,7,5]⟩,⟨21,[10,13,22],[0,5,7,6,4,2,3,1]⟩],0x285a4e919968ba0e7794e8d9ce63a26819d651a4a8aa3a7fa3e7198690a32889f684a0a809e67e9f2789b655936769ca749c26c97669926419a24b90e6498a609665c9625494a509324a91642922449023d8ee3c8e6318ea388d22d8c22c88e298961f84e2289a1b8a2278861d846248821987a1a872188520d84a10832077edcf6ee0b7fdef75dc76cdf76de0a79e037cddb72e067fa0278deb70daf7e9ee7d9f27a9df799e2779d36fdd6769d2739c6729c26f9ba6c9b66b9a26999b69daa67d9a6799659d2f58d3f55d3749d5357d2b5ad5b50d3b5a94b53d3348d66589565495e5694e51d4a519424f9364e9324b9264a9224791b4689f26c9e26a057e5cd6e5f56d6017c5d9726097f5ed755c56c60879604801fc785e9705ad7e1f47c1ec7a1dd791e0771d16f5d8751d0731c8711c06f1b86d1b06b1a86959d691a06659c6619464d91615796498a635835dd906318860575611826017c5c5785d9745c16c43d0745cfb39d0e3fd0a3ccdf418fe408ef4590b40d123dce33e8f23b8f63a8db398de388da5952d5853d575295a5595053955535495685255153531485645815c561545414c51548511404f1384d1304b128491204711946115435053e4e545110425013d4e1431083f4f137504400fc3b4f83d0f03b0e8364e4380dc360cf334c12b4d7354bd358c7344c92ecab338c6328b7350d032cc52e4a9330c8310b5300bc2e8b62e0b42c0a52b0aa2a0a42809624c922389d2649c26094244902308522c831dc6f2287f224811d46d2207d21082200791f87c1e0711a4761d0701b86c1a0651986119c641805e16c5c1645a160541385112c501304912848110430fc420f8330ec2b0bc3709c3a0d8320a82e098410f4400f02207c1e068310b4390a435094380d0300b028090200741c06017054090580e0440705010030050200601000⟩
def D10 : FData := ⟨29,2,128,[0,1,2,4,5,8,10,12,16,18,20,24,26,28],[1,2,3,4,6,8,9,12,16,17,20],[18056,14472],[⟨212,[1,2,4,8,16],[9,0,8,1,2,4,5,3,6,7]⟩,⟨219,[1,2,4,8,20],[9,1,8,2,5,4,6,3,7,0]⟩,⟨223,[1,2,4,12,20],[9,2,8,5,6,4,7,3,0,1]⟩,⟨243,[1,2,8,12,16],[9,0,7,8,1,4,5,3,2,6]⟩,⟨259,[1,2,8,12,20],[9,1,8,7,5,4,6,3,2,0]⟩,⟨72,[1,6,8,16],[8,0,7,1,2,3,4,5,6]⟩,⟨73,[1,6,8,20],[8,0,7,2,5,3,4,6,1]⟩,⟨69,[1,6,12,20],[7,0,8,1,2,3,4,5,6]⟩,⟨40,[2,4,8,17],[8,0,7,2,5,4,3,6,1]⟩,⟨48,[2,4,9,17],[8,0,7,5,6,4,3,1,2]⟩,⟨62,[2,4,9,20],[8,1,7,6,4,5,3,2,0]⟩,⟨110,[2,8,12,17],[8,0,6,7,5,4,3,2,1]⟩,⟨107,[2,8,17,20],[8,0,6,1,7,4,5,3,2]⟩,⟨111,[2,9,12,17],[8,0,6,7,5,4,3,2,1]⟩,⟨147,[2,9,12,20],[8,1,7,6,4,5,3,2,0]⟩,⟨33,[3,4,8,16],[8,0,7,1,2,4,3,5,6]⟩,⟨44,[3,4,8,17],[8,0,7,2,5,4,3,6,1]⟩,⟨56,[3,4,8,20],[8,0,7,2,5,4,3,6,1]⟩,⟨50,[3,4,9,17],[8,0,7,5,6,4,3,1,2]⟩,⟨65,[3,4,9,20],[8,0,7,6,5,4,3,2,1]⟩,⟨69,[3,4,12,20],[8,0,7,5,6,4,3,1,2]⟩,⟨68,[3,6,8,16],[7,8,6,0,1,3,2,4,5]⟩,⟨152,[3,6,8,20],[8,6,7,1,4,3,2,5,0]⟩,⟨142,[3,6,12,20],[7,8,6,4,5,3,2,0,1]⟩,⟨107,[3,8,12,16],[8,7,2,0,1,3,4,6,5]⟩,⟨111,[3,8,12,17],[8,7,2,0,5,3,4,6,1]⟩,⟨148,[3,8,12,20],[8,0,7,6,5,4,3,2,1]⟩,⟨109,[3,8,17,20],[8,0,6,1,7,4,5,3,2]⟩,⟨112,[3,9,12,17],[8,0,6,7,5,4,3,2,1]⟩,⟨151,[3,9,12,20],[8,0,7,6,5,4,3,2,1]⟩,⟨3,[6,8,17],[7,0,6,2,4,3,5,1]⟩,⟨5,[6,9,17],[7,0,6,4,5,3,1,2]⟩,⟨7,[6,9,20],[7,0,6,5,4,3,2,1]⟩],0x10603e7af1db572cdd386ed98b464c172d58a942746992214480f1d365ce1a3260b1528488901c3460a121c406080c100⟩
def D11 : FData := ⟨31,4,16,[0,1,2,4,8,10,12,16,18,20,24,26,28],[1,2,4,8,9,16,17],[18056,14472,18000,14416],[⟨217,[1,2,4,8,16],[9,0,8,1,2,4,5,3,6,7]⟩,⟨53,[2,4,8,17],[8,0,7,2,5,4,3,6,1]⟩,⟨54,[2,4,9,17],[8,0,7,5,6,4,3,1,2]⟩],0x8540⟩
def D12 : FData := ⟨58,2,128,[0,1,2,3,4,8,9,12,16,18,20,24,28],[1,2,4,5,6,8,9,10,16,17,18,24,25,26],[18056,14465],[⟨229,[1,2,4,8,16],[0,1,9,8,7,5,6,4,3,2]⟩,⟨219,[1,2,4,8,18],[8,9,1,2,0,3,4,6,7,5]⟩,⟨244,[1,2,4,8,24],[0,1,9,8,7,5,6,4,3,2]⟩,⟨249,[1,2,4,8,26],[8,9,1,0,2,3,4,6,5,7]⟩,⟨223,[1,2,4,9,18],[8,9,2,6,0,3,4,7,1,5]⟩,⟨248,[1,4,8,16,18],[1,7,9,0,8,6,4,5,3,2]⟩,⟨259,[1,4,9,16,18],[9,8,1,0,7,4,6,5,3,2]⟩,⟨153,[1,4,10,16],[1,0,8,6,7,5,3,4,2]⟩,⟨62,[1,4,10,18],[7,8,1,6,0,3,5,2,4]⟩,⟨113,[1,4,10,24],[7,8,1,0,2,3,5,4,6]⟩,⟨125,[1,4,16,26],[8,7,1,4,6,3,5,2,0]⟩,⟨127,[1,4,18,24],[1,0,8,6,7,5,3,4,2]⟩,⟨128,[1,4,18,25],[8,7,1,4,6,3,5,2,0]⟩,⟨74,[1,6,8,16],[1,0,8,6,7,5,4,2,3]⟩,⟨56,[1,6,8,18],[7,8,0,2,1,3,4,6,5]⟩,⟨114,[1,6,8,24],[0,1,8,7,6,4,5,3,2]⟩,⟨122,[1,6,8,26],[7,8,1,0,2,3,5,4,6]⟩,⟨73,[1,6,9,16],[8,7,0,1,2,3,4,5,6]⟩,⟨69,[1,6,9,18],[7,8,0,6,1,3,4,2,5]⟩,⟨61,[1,6,10,16],[7,8,0,6,1,3,4,2,5]⟩,⟨65,[1,6,10,18],[7,8,0,6,1,3,4,2,5]⟩,⟨117,[1,6,10,24],[7,8,1,0,2,3,5,4,6]⟩,⟨113,[1,6,16,24],[1,0,8,6,7,5,4,3,2]⟩,⟨135,[1,6,16,25],[8,7,1,2,0,3,5,4,6]⟩,⟨85,[1,6,16,26],[0,8,6,5,7,4,2,3,1]⟩,⟨83,[1,6,18,24],[7,8,1,2,0,3,5,4,6]⟩,⟨140,[1,6,18,25],[7,8,1,4,6,3,5,2,0]⟩,⟨292,[4,8,9,16,18],[8,9,0,7,6,5,4,3,2,1]⟩,⟨134,[4,8,17,18],[1,6,8,0,7,3,4,5,2]⟩,⟨195,[4,8,18,25],[8,7,0,5,6,4,2,3,1]⟩,⟨147,[4,9,10,18],[7,8,1,6,0,5,2,3,4]⟩,⟨83,[4,9,10,24],[0,1,7,8,6,3,4,5,2]⟩,⟨196,[4,9,18,24],[7,8,0,6,5,4,3,2,1]⟩,⟨19,[4,10,17],[0,1,7,6,5,2,4,3]⟩,⟨14,[4,10,25],[6,5,0,7,4,3,2,1]⟩,⟨78,[5,6,8,16],[0,1,8,7,6,4,5,3,2]⟩,⟨152,[5,6,8,18],[7,8,6,1,0,2,3,5,4]⟩,⟨117,[5,6,8,24],[0,1,8,7,6,4,5,3,2]⟩,⟨182,[5,6,8,26],[6,0,8,5,2,3,4,1,7]⟩,⟨142,[5,6,9,18],[6,7,8,5,0,2,3,1,4]⟩,⟨121,[5,8,16,18],[1,6,8,0,7,5,4,3,2]⟩,⟨146,[5,8,17,18],[8,7,0,1,6,4,5,3,2]⟩,⟨148,[5,9,16,18],[8,7,0,1,6,4,5,3,2]⟩,⟨151,[5,9,17,18],[8,7,0,1,6,4,5,3,2]⟩,⟨16,[5,10,16],[1,0,7,5,6,4,3,2]⟩,⟨8,[5,10,17],[7,6,1,3,5,4,0,2]⟩,⟨7,[5,10,18],[6,7,0,5,1,3,2,4]⟩,⟨15,[5,10,24],[0,1,7,6,5,3,4,2]⟩,⟨10,[5,10,25],[7,0,5,6,4,2,3,1]⟩,⟨14,[5,16,26],[6,7,1,2,0,4,3,5]⟩,⟨10,[5,17,26],[7,6,1,3,5,4,2,0]⟩,⟨12,[5,18,24],[1,0,7,5,6,4,3,2]⟩,⟨13,[5,18,25],[7,6,1,3,5,4,2,0]⟩],0x186fe5b7a73ddaf4f1d9ab47466c98b05eb96ac56a94a84d973a4cc95223457f121407aedf3c72e9c365684fb5669549d5ec56a34e6c9992e44a8f1a2da3260b962a50992224078e1a3058a12203860a0e144030c10100⟩
def D13 : FData := ⟨59,2,16,[0,1,2,4,8,9,12,16,18,20,24,28],[1,2,4,8,10,16,17,24],[18056,14465],[⟨222,[1,2,4,8,16],[8,9,0,2,1,3,4,5,7,6]⟩,⟨236,[1,2,4,8,24],[9,0,7,8,6,4,5,2,3,1]⟩,⟨67,[1,4,10,16],[7,8,0,6,1,3,4,2,5]⟩,⟨124,[1,4,10,24],[7,8,1,0,2,3,5,4,6]⟩,⟨9,[4,10,17],[6,7,1,5,3,4,2,0]⟩],0x87564320⟩
def D14 : FData := ⟨184,12,512,[0,1,2,3,4,5,8,9,16,18,20,24],[1,2,3,4,5,8,9,16,17,18,19,20,21,24,25],[18056,17608,18000,17104,17496,17048,1676,1228,1620,724,1116,668],[⟨231,[1,2,4,8,16],[1,0,7,9,8,6,5,2,4,3]⟩,⟨233,[1,2,4,8,18],[1,9,0,7,8,6,4,5,2,3]⟩,⟨247,[1,2,4,9,16],[8,0,9,7,1,3,5,4,2,6]⟩,⟨250,[1,2,4,9,18],[8,9,0,7,1,3,4,5,2,6]⟩,⟨278,[1,2,4,16,25],[7,0,6,9,8,3,5,1,4,2]⟩,⟨277,[1,2,5,16,24],[7,0,9,6,8,3,5,2,4,1]⟩,⟨120,[1,2,20,24],[1,0,6,8,7,5,4,2,3]⟩,⟨184,[1,2,20,25],[6,0,5,8,7,3,4,1,2]⟩,⟨175,[1,3,20,24],[0,1,6,8,7,4,5,2,3]⟩,⟨136,[1,18,20,24],[1,0,6,7,8,5,4,2,3]⟩,⟨181,[1,18,20,25],[6,0,5,7,8,3,4,1,2]⟩,⟨251,[2,3,4,8,20],[0,9,8,1,7,4,5,3,6,2]⟩,⟨129,[2,3,20,24],[1,8,0,6,7,3,5,4,2]⟩,⟨154,[2,4,8,17],[4,1,7,8,6,5,2,3,0]⟩,⟨155,[2,4,8,19],[4,8,1,7,6,3,5,2,0]⟩,⟨133,[2,4,9,17],[7,0,8,6,5,4,3,2,1]⟩,⟨135,[2,4,9,19],[7,8,0,6,5,3,4,2,1]⟩,⟨82,[2,4,9,24],[1,0,6,8,7,4,2,5,3]⟩,⟨137,[2,5,9,17],[8,0,6,7,5,4,2,3,1]⟩,⟨140,[2,5,9,19],[8,7,0,6,5,3,4,2,1]⟩,⟨123,[2,5,9,20],[7,0,8,6,1,4,3,2,5]⟩,⟨185,[2,5,17,24],[6,0,8,5,7,4,3,2,1]⟩,⟨181,[2,5,20,25],[0,6,8,2,5,3,4,1,7]⟩,⟨139,[3,5,9,17],[8,0,6,7,5,4,2,3,1]⟩,⟨141,[3,5,9,18],[8,7,0,6,5,3,4,2,1]⟩,⟨183,[3,5,17,24],[8,0,5,7,6,4,1,3,2]⟩,⟨176,[3,5,18,24],[0,8,1,6,7,4,5,3,2]⟩,⟨21,[3,20,25],[0,1,5,7,6,4,2,3]⟩],0x11aa4d225532773892947a34a2673d9dcbd026686bee025f7638216f97f97596c95e8bd242da2d124d359e4e65a7f34431f5002f4ea712c3f1aa492290450e4e84d3d5e8dc29429f0fe2e3cdcc9879368a0c561b3d6eea6f425eefd2db298ebb17421ecfc2d3c5e0e44b3609cc466b056ac8632e998c2602d158aa5427112880b0b10e860a240562a42a10247b3c9e0d8642c96098622095cac4a1f8cc4260200f852270d954a8481e8c43e3c1409432300f0984818080381800⟩
def D15 : FData := ⟨185,2,32,[0,1,2,4,5,8,9,16,18,20,24],[1,2,3,4,8,16,17,20,24],[18056,17608],[⟨232,[1,2,4,8,16],[1,9,0,7,8,6,4,5,2,3]⟩,⟨236,[1,2,4,8,20],[8,0,9,7,1,3,5,4,2,6]⟩,⟨249,[1,2,4,16,24],[1,9,0,7,8,6,4,5,3,2]⟩,⟨128,[1,2,20,24],[1,8,0,6,7,5,3,4,2]⟩,⟨155,[2,4,8,17],[0,8,1,7,6,3,5,2,4]⟩,⟨135,[2,4,17,24],[1,8,0,6,7,3,4,5,2]⟩,⟨140,[2,17,20,24],[1,7,0,6,8,3,5,4,2]⟩,⟨81,[3,4,8,16],[1,8,0,6,7,5,4,2,3]⟩,⟨138,[3,4,8,17],[8,0,6,7,5,4,2,3,1]⟩,⟨124,[3,4,8,20],[0,8,7,1,6,4,3,5,2]⟩,⟨122,[3,4,16,24],[1,8,0,6,7,5,4,3,2]⟩,⟨182,[3,4,17,24],[8,0,5,7,6,4,1,3,2]⟩,⟨13,[3,20,24],[1,7,0,5,6,4,3,2]⟩],0x62f5b52728398b520c520c40⟩
def D16 : FData := ⟨207,8,8,[0,1,2,4,6,8,10,16,20,24],[1,2,4,8,16],[18056,17608,14416,13072,10328,8984,5792,5344],[⟨234,[1,2,4,8,16],[9,0,1,8,7,4,5,6,3,2]⟩],0x0⟩
def D17 : FData := ⟨220,10,64,[0,1,2,3,4,5,8,10,16,20,24],[1,2,4,6,8,9,12,16,17,18],[18056,14416,17601,10265,13058,5666,8459,1123,4308,668],[⟨235,[1,2,4,8,16],[0,1,9,7,8,5,6,4,2,3]⟩,⟨125,[1,2,12,16],[1,6,0,7,8,5,2,4,3]⟩,⟨85,[1,6,8,18],[0,8,1,7,6,4,5,3,2]⟩,⟨14,[1,12,18],[0,1,7,5,6,3,2,4]⟩,⟨10,[6,9,17],[7,0,6,1,5,3,4,2]⟩],0x30bacaa89a489981758f35e55444b280⟩
def ds : List FData := [D0,D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14,D15,D16,D17]
end MoonPrize.CatalogueData

namespace Coverage

def pop5 (t : ℕ) := ((List.range 5).filter (fun j => t.testBit j)).length

lemma gd_range_list (l : List ℕ) : (List.range l.length).map (gd l) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map]
    simpa [Function.comp_def,gd] using congrArg (List.cons x) ih

lemma row_len (qs : List ℕ) (t : ℕ) : (rset qs t).length =
    pop5 t + (qs.filter (fun q => q &&& t == 0)).length := by
  rw [rset,List.range_add,List.filter_append,List.length_append]
  congr 1
  rw [← List.countP_eq_length_filter, List.countP_map,← List.countP_eq_length_filter]
  conv_rhs => rw [←gd_range_list qs]
  rw [List.countP_map]
  congr 1
  funext i
  simp [Function.comp_def,memR]

def word : List ℕ → ℕ
  | [] => 0
  | a::xs => (2^a) ||| word xs

lemma word_bits (xs : List ℕ) (j : ℕ) : (word xs).testBit j = true ↔ j∈xs := by
  induction xs with
  | nil => simp [word]
  | cons a xs ih =>
    simp only [word,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    tauto

def seed (ind : List ℕ) := word (ind.map (fun t => 32*pop5 t+t))

def hitLow (q : ℕ) : ℕ := ([0,2863311530,3435973836,4008636142,4042322160,4210752250,4244438268,4278124286,4278255360,4289396650,4291624908,4293853166,4293984240,4294639610,4294770684,4294901758,4294901760,4294945450,4294954188,4294962926,4294963440,4294966010,4294966524,4294967038,4294967040,4294967210,4294967244,4294967278,4294967280,4294967290,4294967292,4294967294] : List ℕ)[q]?.getD 0
def spread (x : ℕ) : ℕ := x * 1461501637671185285203851458712368708759249223681
def touched (q : ℕ) : ℕ := spread (hitLow q)
def missed (q : ℕ) : ℕ := spread (4294967295 ^^^ hitLow q)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma mask_at : ∀ q < 32, ∀ s < 6, ∀ t < 32,
    (missed q).testBit (32*s+t) = (q &&& t == 0) ∧
    (touched q).testBit (32*s+t) = (q &&& t != 0) ∧
    (hitLow q).testBit t = (q &&& t != 0) := by decide +kernel

def plane (ind : List ℕ) : List ℕ → ℕ
  | [] => seed ind
  | q::qs =>
    let old := plane ind qs
    (old &&& missed q) ||| ((old &&& touched q) >>> 32)

lemma seed_bound (ind : List ℕ) (hi : ∀ a∈ind, a < 32) : seed ind < 2^192 := by
  by_contra! hn
  have lt (a) (ha : a ∈ ind) : 32*pop5 a+a<192 := by
    have k := List.length_filter_le (fun j => Nat.testBit a j) (List.range 5)
    have z : pop5 a ≤ 5 := by simpa [pop5] using k
    have v := hi a ha
    omega
  have le : seed ind ≤ 2^192-1 := by
    apply Nat.le_of_testBit
    intro j hj
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ((word_bits _ j).mp hj)
    exact (Nat.testBit_two_pow_sub_one _ _).trans (decide_eq_true (lt a ha))
  omega

lemma plane_bound (ind qs : List ℕ) (hi : ∀ a∈ind,a<32) : plane ind qs < 2^192 := by
  induction qs with
  | nil => exact seed_bound ind hi
  | cons q qs ih =>
    apply Nat.or_lt_two_pow
    · exact lt_of_le_of_lt Nat.and_le_left ih
    · exact lt_of_le_of_lt ((Nat.shiftRight_le _ _).trans Nat.and_le_left) ih

lemma plane_at {ind qs : List ℕ} (hi : ∀ a∈ind,a<32) (hq : ∀ a∈qs,a<32)
    (s t : ℕ) (ht : t<32) :
    (plane ind qs).testBit (32*s+t) = true ↔ t∈ind ∧
      pop5 t + (qs.filter (fun q => q &&& t == 0)).length = qs.length + s := by
  induction qs generalizing s with
  | nil =>
    change (seed ind).testBit (32*s+t) = true ↔ _
    rw [seed,word_bits,List.mem_map]
    simp only [List.filter_nil,List.length_nil,Nat.add_zero,Nat.zero_add]
    constructor
    · rintro ⟨u,hu,e⟩
      have b := hi u hu
      have eq : u = t := by omega
      subst u
      exact ⟨hu,by omega⟩
    · rintro ⟨inT,eq⟩
      exact ⟨t,inT,by omega⟩
  | cons q qs ih =>
    have tail : ∀ a∈qs, a<32 := fun a h => hq a (List.mem_cons_of_mem _ h)
    have qlt := hq q List.mem_cons_self
    have cap : pop5 t ≤ 5 := by
      simpa [pop5] using List.length_filter_le (fun j => Nat.testBit t j) (List.range 5)
    have sub := List.length_filter_le (fun v => v &&& t == 0) qs
    by_cases hs : s<6
    · have at0 := mask_at q qlt s hs t ht
      have high : 32+(32*s+t) = 32*(s+1)+t := by omega
      simp only [plane,Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftRight,
        Bool.or_eq_true,Bool.and_eq_true,high,at0.1,ih tail s,ih tail (s+1)]
      by_cases last : q &&& t = 0
      · have zz : (touched q).testBit (32*(s+1)+t) = false := by
          by_cases hn : s+1<6
          · simp [(mask_at q qlt _ hn _ ht).2.1,last]
          · have b : touched q < 2^192 := by
              have test : ∀ x : Fin 32, touched x.val < 2^192 := by decide +kernel
              exact test ⟨q,qlt⟩
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le b (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [zz,last] <;> omega 
      · have both (eq : pop5 t + (qs.filter (fun v => v &&& t == 0)).length = qs.length+(s+1)) :
            (touched q).testBit (32*(s+1)+t) = true := by
          have h : s+1<6 := by omega
          simp [(mask_at q qlt _ h _ ht).2.1,last]
        simp [last]
        constructor
        · rintro ⟨⟨mem,eq⟩,_⟩; exact ⟨mem,by omega⟩
        · rintro ⟨mem,eq⟩
          have eq2 : pop5 t + (qs.filter (fun v => v &&& t == 0)).length = qs.length+(s+1) := by omega
          exact ⟨⟨mem,eq2⟩,both eq2⟩
    · have too : (plane ind (q::qs)).testBit (32*s+t) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (plane_bound ind _ hi) (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [too]
      have k := List.length_filter_le (fun v => v &&& t == 0) (q::qs)
      simp only [Bool.false_eq_true,false_iff,not_and]
      omega

end Coverage

namespace Coverage

lemma bit_nonzero {a : ℕ} (h : a ≠ 0) : ∃ j, a.testBit j = true := by
  by_contra! none
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  have := none i
  simpa using this

def noCover (j : ℕ) : ℕ := 4294967295 ^^^ hitLow (2^j)

lemma noCover_at : ∀ j<5, ∀ t<32, (noCover j).testBit t = !(t.testBit j) := by decide +kernel

def canSkip (state : ℕ) (qs : List ℕ) : Bool :=
  ((state >>> 32) != 0) || (List.range 5).any (fun j => (state &&& noCover j) == 0) ||
    qs.any (fun q => (state &&& hitLow q) == 0)

lemma no_common_bit {a b i : ℕ} (z : a &&& b = 0) (ha : a.testBit i = true) :
    b.testBit i = false := by
  have h := congrArg (fun x : ℕ => x.testBit i) z
  simpa [Nat.testBit_and,ha] using h

theorem slow_reason {ind qs : List ℕ} (hi : ∀ a∈ind, a<32) (hq : ∀ a∈qs, a<32)
    (skip : canSkip (plane ind qs) qs = true) :
    ind.any (fun t => decide (qs.length < (rset qs t).length)) = true ∨
    (List.range (5+qs.length)).any (fun v => ind.all (fun t =>
      memR qs t v || decide ((rset qs t).length ≠ qs.length))) = true := by
  simp only [canSkip,Bool.or_eq_true,List.any_eq_true,List.mem_range,beq_iff_eq] at skip
  rcases skip with (high | ⟨j,hj,empty⟩) | ⟨q,qmem,empty⟩
  · left
    have nz : plane ind qs >>> 32 ≠ 0 := by simpa using high
    obtain ⟨b,bb⟩ := bit_nonzero nz
    rw [Nat.testBit_shiftRight] at bb
    let s := (32+b)/32
    let t := (32+b) % 32
    have hst : 32*s+t = 32+b := by dsimp [s,t]; omega
    have ht : t<32 := Nat.mod_lt _ (by decide)
    have hs : 0<s := by dsimp [s]; omega
    obtain ⟨inT,eq⟩ := (plane_at hi hq s t ht).mp (hst ▸ bb)
    exact List.any_eq_true.mpr ⟨t,inT,decide_eq_true (by rw [row_len];omega)⟩
  · right
    apply List.any_eq_true.mpr
    refine ⟨j,List.mem_range.mpr (by omega),List.all_eq_true.mpr ?_⟩
    intro t it
    have ht := hi t it
    by_cases full : (rset qs t).length = qs.length
    · have bit := (plane_at hi hq 0 t ht).mpr ⟨it,by simpa [row_len] using full⟩
      simp only [Nat.mul_zero,Nat.zero_add] at bit
      have b := no_common_bit empty bit
      rw [noCover_at j hj t ht] at b
      simpa [memR,hj,full] using b
    · simp [full]
  · right
    obtain ⟨i,hix,qi⟩ := mem_gd qs q qmem
    refine List.any_eq_true.mpr ⟨5+i,List.mem_range.mpr (by omega),List.all_eq_true.mpr ?_⟩
    intro t it
    have ht := hi t it
    by_cases full : (rset qs t).length = qs.length
    · have bit := (plane_at hi hq 0 t ht).mpr ⟨it,by simpa [row_len] using full⟩
      simp only [Nat.mul_zero,Nat.zero_add] at bit
      have b := no_common_bit empty bit
      rw [(mask_at q (hq q qmem) 0 (by decide) t ht).2.2] at b
      simpa [memR,full,qi] using b
    · simp [full]

def quick (ind : List ℕ) (wok : List ℕ → ℕ → Bool) (B : ℕ) (qs : List ℕ) (w : ℕ) : Option ℕ :=
  if canSkip (plane ind qs) qs then some w
  else if wok qs (w % B) then some (w/B) else none

theorem quick_sound {f : ℕ} {ind : List ℕ} {wok : List ℕ → ℕ → Bool} {B : ℕ} {qs : List ℕ}
    {w w' : ℕ}
    (hind : ∀ t, t ∈ ind ↔ (t < 32 ∧ indepB f t = true)) (hq : ∀ q ∈ qs, q < 32)
    (hv : Valid (5 + qs.length) qs.length (padj f qs))
    (h : quick ind wok B qs w = some w') : ∃ x, wok qs x = true := by
  unfold quick at h
  split at h
  next sk =>
    have slow : node ind (fun _ _ => false) B qs w = some w := by
      rcases slow_reason (fun a ha => ((hind a).mp ha).1) hq sk with yes|yes
      · unfold node
        rw [ite_eq_left yes]
      · unfold node
        rw [ite_eq_left yes]
        simp only [ite_self]
    obtain ⟨_,impossible⟩ := node_sound hind hq hv slow
    contradiction
  next _ =>
    split at h
    next yes => exact ⟨_,yes⟩
    next _ => contradiction

end Coverage

namespace Coverage

def fastTop (f B : ℕ) (wok : List ℕ → ℕ → Bool) (ind adm : List ℕ) (w : ℕ) : Bool :=
  (indOf f == ind) && (admOf f == adm) &&
    (match quick ind wok B [] w with
     | none => false
     | some w1 => (walk (quick ind wok B) 5 adm [] w1).isSome)

theorem fast_top_sound {f B : ℕ} {wok : List ℕ → ℕ → Bool} {ind adm : List ℕ} {w : ℕ}
    (h : fastTop f B wok ind adm w = true) {qs : List ℕ}
    (hs : qs.Pairwise (· < ·)) (hq : ∀ q ∈ qs, 1 ≤ q ∧ q < 32) (hl : qs.length ≤ 5)
    (hv : Valid (5 + qs.length) qs.length (padj f qs)) : ∃ x, wok qs x = true := by
  unfold fastTop at h
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨⟨hi, ha⟩, hw⟩ := h
  have hind : ∀ t, t ∈ ind ↔ (t < 32 ∧ indepB f t = true) := by
    intro t
    rw [← hi]
    simp only [indOf, List.mem_filter, List.mem_range]
  have hq32 : ∀ q ∈ qs, q < 32 := fun q h => (hq q h).2
  cases h0 : quick ind wok B [] w with
  | none => rw [h0] at hw; simp at hw
  | some w1 =>
    rw [h0] at hw
    have hw' : (walk (quick ind wok B) 5 adm [] w1).isSome = true := hw
    obtain ⟨w2, h1⟩ := Option.isSome_iff_exists.mp hw'
    by_cases he : qs = []
    · subst he
      exact quick_sound hind hq32 hv h0
    · have hsub : qs.Sublist adm := by
        rw [← ha]
        have s1 : qs.Sublist (List.range' 1 31) :=
          sublist_range' 31 1 qs hs (fun x hx => by have := hq x hx; omega)
        have s2 := s1.filter (fun q => !c4q f q)
        have s3 : qs.filter (fun q => !c4q f q) = qs := by
          apply List.filter_eq_self.mpr
          intro a haq
          simp [adm_of_valid hq32 hv.sqf a haq]
        rw [s3] at s2
        exact s2
      have hclean : qs.Pairwise (fun a b => multi (a &&& b) = false) :=
        List.Pairwise.imp_of_mem
          (fun {a b} ha hb hlt => clean_of_valid hq32 hv.sqf a ha b hb (Nat.ne_of_lt hlt)) hs
      obtain ⟨wa, wb, hn⟩ := walk_sound _ 5 adm [] w1 w2 h1 qs he hsub hl hclean
      exact quick_sound hind hq32 hv hn

def fastOK (perms : List ℕ) (cat : List Cat) (d : FData) : Bool :=
  autsOK perms d && d.ents.all (entOK cat d.F) &&
    fastTop d.F d.B (wokF d.A d.auts d.ents) d.ind d.adm d.w

theorem mainFast {perms : List ℕ} {cat : List Cat} {ds : List FData} {canon : List ℕ}
    (hperm : permsB perms = true) (hcanon : canonB perms (ds.map FData.F) canon = true)
    (hds : ∀ d ∈ ds, fastOK perms cat d = true)
    (f : ℕ) (qs : List ℕ) (hf : f < 1024) (hnd : qs.Nodup) (hq : ∀ q ∈ qs, 1 ≤ q ∧ q < 32)
    (hl : qs.length ≤ 5) (hv : Valid (5 + qs.length) qs.length (padj f qs)) :
    ∃ i g, nth cat i = some g ∧ g.n = 5 + qs.length ∧
      Iso (5 + qs.length) (padj f qs) (cadj g) := by
  have hP := permsB_sound hperm
  rcases canonB_sound hcanon f hf with hc4 | ⟨c, hc, hFm⟩
  · exact (c4f_bad hc4 qs hv.sqf).elim
  obtain ⟨d, hd, hdF⟩ := List.mem_map.mp hFm
  have hfd := hds d hd
  unfold fastOK at hfd
  rw [Bool.and_eq_true, Bool.and_eq_true] at hfd
  obtain ⟨⟨hA0, hE0⟩, hW⟩ := hfd
  have hA : ∀ c2 ∈ d.auts, c2 ∈ perms ∧ pullF c2 d.F = d.F := by
    simp only [autsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hA0
    exact hA0
  have hE : ∀ e ∈ d.ents, entOK cat d.F e = true := List.all_eq_true.mp hE0
  have hL1len : (qs.map (pullQ c)).length = qs.length := List.length_map _
  have hL1nd : (qs.map (pullQ c)).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => pullQ_inj hP c hc a (hq a ha).2 b (hq b hb).2 e) hnd
  obtain ⟨hs, hslen, hsmem⟩ := isort_spec (qs.map (pullQ c)) hL1nd
  have hlen' : (isort (qs.map (pullQ c))).length = qs.length := hslen.trans hL1len
  have hsnd : (isort (qs.map (pullQ c))).Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  have iso1 : Iso (5 + qs.length) (padj d.F (isort (qs.map (pullQ c)))) (padj f qs) := by
    have r2 := iso_reorder d.F hslen hsnd (fun x hx => (hsmem x).mp hx)
    rw [hlen'] at r2
    have r1 := iso_relabel hP hc f qs
    rw [← hdF] at r1
    exact r2.trans r1
  have hv' : Valid (5 + (isort (qs.map (pullQ c))).length) (isort (qs.map (pullQ c))).length
      (padj d.F (isort (qs.map (pullQ c)))) := by
    rw [hlen']
    exact Valid.of_iso iso1 hv
  have hq' : ∀ q ∈ isort (qs.map (pullQ c)), 1 ≤ q ∧ q < 32 := by
    intro q hq1
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ((hsmem q).mp hq1)
    refine ⟨?_, pullQ_lt c a⟩
    by_contra h0
    have h00 : pullQ c a = pullQ c 0 := by
      rw [pullQ_zero]
      omega
    have e0 := pullQ_inj hP c hc a (hq a ha).2 0 (by norm_num) h00
    have := (hq a ha).1
    omega
  obtain ⟨x, hx⟩ := fast_top_sound hW hs hq' (by rw [hlen']; exact hl) hv'
  obtain ⟨c2, hc2, e, he, hel, hesub⟩ := wokF_sound hx
  obtain ⟨hc2p, hc2F⟩ := hA c2 hc2
  obtain ⟨g, hg, hgn, hQnd, isoE⟩ := entOK_sound (hE e he)
  have helen : e.Q.length = qs.length := hel.trans hlen'
  have iso2 : Iso (5 + qs.length) (padj d.F e.Q) (padj d.F (isort (qs.map (pullQ c)))) := by
    have r2 := iso_reorder d.F (L' := e.Q) (L := (isort (qs.map (pullQ c))).map (pullQ c2))
      (by rw [List.length_map]; exact hel) hQnd hesub
    rw [helen] at r2
    have r1 := iso_relabel hP hc2p d.F (isort (qs.map (pullQ c)))
    rw [hc2F, hlen'] at r1
    exact r2.trans r1
  rw [helen] at isoE hgn
  exact ⟨e.g, g, hg, hgn, iso1.symm.trans (iso2.symm.trans isoE)⟩

end Coverage

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData

open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)

def judge (d : FData) := quick d.ind (wokF d.A d.auts d.ents) d.B

def atBit (d : FData) (i : ℕ) := d.w >>> i

abbrev job (d : FData) (pre : List ℕ) (q a b : ℕ) :=
  child (judge d) (walk (judge d) (4-pre.length)) pre q (d.adm.filter (fun v => decide (q < v)))
    (atBit d a) = some (atBit d b)

theorem link {k : ℕ → List ℕ → ℕ → Option ℕ} {q : ℕ} {tail : List ℕ} {a b c : ℕ}
    (head : k q tail a = some b) (rest : loop k tail b = some c) :
    loop k (q::tail) a = some c := by simp [loop,head,rest]

theorem join {nd : List ℕ → ℕ → Option ℕ} {rec : List ℕ → List ℕ → ℕ → Option ℕ}
    {qs : List ℕ} {q : ℕ} {tail : List ℕ} {w mid last : ℕ}
    (clean : qs.any (fun x => multi (x &&& q)) = false)
    (first : nd (qs++[q]) w = some mid)
    (sub : rec tail (qs++[q]) mid = some last) :
    child nd rec qs q tail w = some last := by
  simp [child,clean,first,sub]

theorem result {d : FData} {z : ℕ}
    (header : (autsOK coverPerms d && d.ents.all (entOK (entries.map asCat) d.F) &&
      ((indOf d.F == d.ind) && (admOf d.F == d.adm))) = true)
    (root : judge d [] d.w = some d.w)
    (forest : walk (judge d) 5 d.adm [] d.w = some z) :
    fastOK coverPerms (entries.map asCat) d = true := by
  obtain ⟨ab,cd⟩ := Bool.and_eq_true_iff.mp header
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp ab
  obtain ⟨c,h⟩ := Bool.and_eq_true_iff.mp cd
  unfold judge at root forest
  simp [fastOK,fastTop,a,b,c,h,root,forest]

end MoonPrize.FastCatalogue

namespace MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem permutations_checked : permsB coverPerms = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem cover_types_checked : canonB coverPerms (ds.map FData.F) canonCodes = true := by decide +kernel
end MoonPrize.CatalogueData

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData

open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p1x2 : job D0 [1] 2 0 7532 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p1x3 : job D0 [1] 3 7532 12544 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p1x4 : job D0 [1] 4 12544 17500 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p1x5 : job D0 [1] 5 17500 20636 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p1x6 : job D0 [1] 6 20636 23660 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p1x7 : job D0 [1] 7 23660 25088 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p1x8 : job D0 [1] 8 25088 26908 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p1x9 : job D0 [1] 9 26908 27874 := by decide +kernel
theorem J0p1x10 : job D0 [1] 10 27874 28700 := by decide +kernel
theorem J0p1x11 : job D0 [1] 11 28700 29078 := by decide +kernel
theorem J0p1x12 : job D0 [1] 12 29078 29358 := by decide +kernel
theorem J0p1x13 : job D0 [1] 13 29358 29526 := by decide +kernel
theorem J0p1x14 : job D0 [1] 14 29526 29750 := by decide +kernel
theorem J0p1x15 : job D0 [1] 15 29750 29848 := by decide +kernel
theorem J0p1x16 : job D0 [1] 16 29848 29904 := by decide +kernel
theorem J0p1x17 : job D0 [1] 17 29904 29918 := by decide +kernel
theorem J0p1x18 : job D0 [1] 18 29918 29918 := by decide +kernel
theorem J0p1x19 : job D0 [1] 19 29918 29918 := by decide +kernel
theorem J0p1x20 : job D0 [1] 20 29918 29918 := by decide +kernel
theorem J0p1x21 : job D0 [1] 21 29918 29918 := by decide +kernel
theorem J0p1x22 : job D0 [1] 22 29918 29918 := by decide +kernel
theorem J0p1x23 : job D0 [1] 23 29918 29918 := by decide +kernel
theorem J0p1x24 : job D0 [1] 24 29918 29918 := by decide +kernel
theorem J0p1x25 : job D0 [1] 25 29918 29918 := by decide +kernel
theorem J0p1x26 : job D0 [1] 26 29918 29918 := by decide +kernel
theorem J0p1x27 : job D0 [1] 27 29918 29918 := by decide +kernel
theorem J0p1x28 : job D0 [1] 28 29918 29918 := by decide +kernel
theorem J0p1x29 : job D0 [1] 29 29918 29918 := by decide +kernel
theorem J0p1x30 : job D0 [1] 30 29918 29918 := by decide +kernel
theorem J0p1x31 : job D0 [1] 31 29918 29918 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p1 : job D0 [] 1 0 29918 := by
  apply join (mid := atBit D0 0) (by decide +kernel) (by decide +kernel)
  exact link J0p1x2 (link J0p1x3 (link J0p1x4 (link J0p1x5 (link J0p1x6 (link J0p1x7 (link J0p1x8 (link J0p1x9 (link J0p1x10 (link J0p1x11 (link J0p1x12 (link J0p1x13 (link J0p1x14 (link J0p1x15 (link J0p1x16 (link J0p1x17 (link J0p1x18 (link J0p1x19 (link J0p1x20 (link J0p1x21 (link J0p1x22 (link J0p1x23 (link J0p1x24 (link J0p1x25 (link J0p1x26 (link J0p1x27 (link J0p1x28 (link J0p1x29 (link J0p1x30 (link J0p1x31 (rfl))))))))))))))))))))))))))))))
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p2x3 : job D0 [2] 3 29918 34930 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p2x4 : job D0 [2] 4 34930 39886 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p2x5 : job D0 [2] 5 39886 43722 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p2x6 : job D0 [2] 6 43722 46046 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p2x7 : job D0 [2] 7 46046 47474 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p2x8 : job D0 [2] 8 47474 49294 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p2x9 : job D0 [2] 9 49294 50484 := by decide +kernel
theorem J0p2x10 : job D0 [2] 10 50484 51086 := by decide +kernel
theorem J0p2x11 : job D0 [2] 11 51086 51464 := by decide +kernel
theorem J0p2x12 : job D0 [2] 12 51464 51744 := by decide +kernel
theorem J0p2x13 : job D0 [2] 13 51744 51968 := by decide +kernel
theorem J0p2x14 : job D0 [2] 14 51968 52136 := by decide +kernel
theorem J0p2x15 : job D0 [2] 15 52136 52234 := by decide +kernel
theorem J0p2x16 : job D0 [2] 16 52234 52290 := by decide +kernel
theorem J0p2x17 : job D0 [2] 17 52290 52304 := by decide +kernel
theorem J0p2x18 : job D0 [2] 18 52304 52304 := by decide +kernel
theorem J0p2x19 : job D0 [2] 19 52304 52304 := by decide +kernel
theorem J0p2x20 : job D0 [2] 20 52304 52304 := by decide +kernel
theorem J0p2x21 : job D0 [2] 21 52304 52304 := by decide +kernel
theorem J0p2x22 : job D0 [2] 22 52304 52304 := by decide +kernel
theorem J0p2x23 : job D0 [2] 23 52304 52304 := by decide +kernel
theorem J0p2x24 : job D0 [2] 24 52304 52304 := by decide +kernel
theorem J0p2x25 : job D0 [2] 25 52304 52304 := by decide +kernel
theorem J0p2x26 : job D0 [2] 26 52304 52304 := by decide +kernel
theorem J0p2x27 : job D0 [2] 27 52304 52304 := by decide +kernel
theorem J0p2x28 : job D0 [2] 28 52304 52304 := by decide +kernel
theorem J0p2x29 : job D0 [2] 29 52304 52304 := by decide +kernel
theorem J0p2x30 : job D0 [2] 30 52304 52304 := by decide +kernel
theorem J0p2x31 : job D0 [2] 31 52304 52304 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p2 : job D0 [] 2 29918 52304 := by
  apply join (mid := atBit D0 29918) (by decide +kernel) (by decide +kernel)
  exact link J0p2x3 (link J0p2x4 (link J0p2x5 (link J0p2x6 (link J0p2x7 (link J0p2x8 (link J0p2x9 (link J0p2x10 (link J0p2x11 (link J0p2x12 (link J0p2x13 (link J0p2x14 (link J0p2x15 (link J0p2x16 (link J0p2x17 (link J0p2x18 (link J0p2x19 (link J0p2x20 (link J0p2x21 (link J0p2x22 (link J0p2x23 (link J0p2x24 (link J0p2x25 (link J0p2x26 (link J0p2x27 (link J0p2x28 (link J0p2x29 (link J0p2x30 (link J0p2x31 (rfl)))))))))))))))))))))))))))))
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p3 : job D0 [] 3 52304 66836 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p4 : job D0 [] 4 66836 78554 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p5 : job D0 [] 5 78554 85414 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p6 : job D0 [] 6 85414 89838 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p7 : job D0 [] 7 89838 92204 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p8 : job D0 [] 8 92204 94808 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p9 : job D0 [] 9 94808 95942 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J0p10 : job D0 [] 10 95942 96516 := by decide +kernel
theorem J0p11 : job D0 [] 11 96516 96824 := by decide +kernel
theorem J0p12 : job D0 [] 12 96824 96922 := by decide +kernel
theorem J0p13 : job D0 [] 13 96922 97020 := by decide +kernel
theorem J0p14 : job D0 [] 14 97020 97118 := by decide +kernel
theorem J0p15 : job D0 [] 15 97118 97188 := by decide +kernel
theorem J0p16 : job D0 [] 16 97188 97202 := by decide +kernel
theorem J0p17 : job D0 [] 17 97202 97202 := by decide +kernel
theorem J0p18 : job D0 [] 18 97202 97202 := by decide +kernel
theorem J0p19 : job D0 [] 19 97202 97202 := by decide +kernel
theorem J0p20 : job D0 [] 20 97202 97202 := by decide +kernel
theorem J0p21 : job D0 [] 21 97202 97202 := by decide +kernel
theorem J0p22 : job D0 [] 22 97202 97202 := by decide +kernel
theorem J0p23 : job D0 [] 23 97202 97202 := by decide +kernel
theorem J0p24 : job D0 [] 24 97202 97202 := by decide +kernel
theorem J0p25 : job D0 [] 25 97202 97202 := by decide +kernel
theorem J0p26 : job D0 [] 26 97202 97202 := by decide +kernel
theorem J0p27 : job D0 [] 27 97202 97202 := by decide +kernel
theorem J0p28 : job D0 [] 28 97202 97202 := by decide +kernel
theorem J0p29 : job D0 [] 29 97202 97202 := by decide +kernel
theorem J0p30 : job D0 [] 30 97202 97202 := by decide +kernel
theorem J0p31 : job D0 [] 31 97202 97202 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem fastD0 : fastOK coverPerms (entries.map asCat) D0 = true := by
  apply result (z := atBit D0 97202) (by decide +kernel) (by decide +kernel)
  exact link J0p1 (link J0p2 (link J0p3 (link J0p4 (link J0p5 (link J0p6 (link J0p7 (link J0p8 (link J0p9 (link J0p10 (link J0p11 (link J0p12 (link J0p13 (link J0p14 (link J0p15 (link J0p16 (link J0p17 (link J0p18 (link J0p19 (link J0p20 (link J0p21 (link J0p22 (link J0p23 (link J0p24 (link J0p25 (link J0p26 (link J0p27 (link J0p28 (link J0p29 (link J0p30 (link J0p31 (rfl)))))))))))))))))))))))))))))))

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData

open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p1x2 : job D1 [1] 2 0 6456 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p1x3 : job D1 [1] 3 6456 6456 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p1x4 : job D1 [1] 4 6456 8316 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p1x5 : job D1 [1] 5 8316 8580 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p1x6 : job D1 [1] 6 8580 9444 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p1x7 : job D1 [1] 7 9444 9660 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p1x8 : job D1 [1] 8 9660 10416 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p1x9 : job D1 [1] 9 10416 10476 := by decide +kernel
theorem J1p1x10 : job D1 [1] 10 10476 10728 := by decide +kernel
theorem J1p1x11 : job D1 [1] 11 10728 10776 := by decide +kernel
theorem J1p1x12 : job D1 [1] 12 10776 10860 := by decide +kernel
theorem J1p1x13 : job D1 [1] 13 10860 10884 := by decide +kernel
theorem J1p1x14 : job D1 [1] 14 10884 10956 := by decide +kernel
theorem J1p1x15 : job D1 [1] 15 10956 10980 := by decide +kernel
theorem J1p1x16 : job D1 [1] 16 10980 11016 := by decide +kernel
theorem J1p1x17 : job D1 [1] 17 11016 11016 := by decide +kernel
theorem J1p1x18 : job D1 [1] 18 11016 11016 := by decide +kernel
theorem J1p1x19 : job D1 [1] 19 11016 11016 := by decide +kernel
theorem J1p1x20 : job D1 [1] 20 11016 11016 := by decide +kernel
theorem J1p1x21 : job D1 [1] 21 11016 11016 := by decide +kernel
theorem J1p1x22 : job D1 [1] 22 11016 11016 := by decide +kernel
theorem J1p1x23 : job D1 [1] 23 11016 11016 := by decide +kernel
theorem J1p1x24 : job D1 [1] 24 11016 11016 := by decide +kernel
theorem J1p1x25 : job D1 [1] 25 11016 11016 := by decide +kernel
theorem J1p1x26 : job D1 [1] 26 11016 11016 := by decide +kernel
theorem J1p1x27 : job D1 [1] 27 11016 11016 := by decide +kernel
theorem J1p1x28 : job D1 [1] 28 11016 11016 := by decide +kernel
theorem J1p1x29 : job D1 [1] 29 11016 11016 := by decide +kernel
theorem J1p1x30 : job D1 [1] 30 11016 11016 := by decide +kernel
theorem J1p1x31 : job D1 [1] 31 11016 11016 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p1 : job D1 [] 1 0 11016 := by
  apply join (mid := atBit D1 0) (by decide +kernel) (by decide +kernel)
  exact link J1p1x2 (link J1p1x3 (link J1p1x4 (link J1p1x5 (link J1p1x6 (link J1p1x7 (link J1p1x8 (link J1p1x9 (link J1p1x10 (link J1p1x11 (link J1p1x12 (link J1p1x13 (link J1p1x14 (link J1p1x15 (link J1p1x16 (link J1p1x17 (link J1p1x18 (link J1p1x19 (link J1p1x20 (link J1p1x21 (link J1p1x22 (link J1p1x23 (link J1p1x24 (link J1p1x25 (link J1p1x26 (link J1p1x27 (link J1p1x28 (link J1p1x29 (link J1p1x30 (link J1p1x31 (rfl))))))))))))))))))))))))))))))
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p2x3 : job D1 [2] 3 11016 11016 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p2x4 : job D1 [2] 4 11016 12876 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p2x5 : job D1 [2] 5 12876 13740 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p2x6 : job D1 [2] 6 13740 14004 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p2x7 : job D1 [2] 7 14004 14220 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p2x8 : job D1 [2] 8 14220 14976 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p2x9 : job D1 [2] 9 14976 15228 := by decide +kernel
theorem J1p2x10 : job D1 [2] 10 15228 15288 := by decide +kernel
theorem J1p2x11 : job D1 [2] 11 15288 15336 := by decide +kernel
theorem J1p2x12 : job D1 [2] 12 15336 15420 := by decide +kernel
theorem J1p2x13 : job D1 [2] 13 15420 15492 := by decide +kernel
theorem J1p2x14 : job D1 [2] 14 15492 15516 := by decide +kernel
theorem J1p2x15 : job D1 [2] 15 15516 15540 := by decide +kernel
theorem J1p2x16 : job D1 [2] 16 15540 15576 := by decide +kernel
theorem J1p2x17 : job D1 [2] 17 15576 15576 := by decide +kernel
theorem J1p2x18 : job D1 [2] 18 15576 15576 := by decide +kernel
theorem J1p2x19 : job D1 [2] 19 15576 15576 := by decide +kernel
theorem J1p2x20 : job D1 [2] 20 15576 15576 := by decide +kernel
theorem J1p2x21 : job D1 [2] 21 15576 15576 := by decide +kernel
theorem J1p2x22 : job D1 [2] 22 15576 15576 := by decide +kernel
theorem J1p2x23 : job D1 [2] 23 15576 15576 := by decide +kernel
theorem J1p2x24 : job D1 [2] 24 15576 15576 := by decide +kernel
theorem J1p2x25 : job D1 [2] 25 15576 15576 := by decide +kernel
theorem J1p2x26 : job D1 [2] 26 15576 15576 := by decide +kernel
theorem J1p2x27 : job D1 [2] 27 15576 15576 := by decide +kernel
theorem J1p2x28 : job D1 [2] 28 15576 15576 := by decide +kernel
theorem J1p2x29 : job D1 [2] 29 15576 15576 := by decide +kernel
theorem J1p2x30 : job D1 [2] 30 15576 15576 := by decide +kernel
theorem J1p2x31 : job D1 [2] 31 15576 15576 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p2 : job D1 [] 2 11016 15576 := by
  apply join (mid := atBit D1 11016) (by decide +kernel) (by decide +kernel)
  exact link J1p2x3 (link J1p2x4 (link J1p2x5 (link J1p2x6 (link J1p2x7 (link J1p2x8 (link J1p2x9 (link J1p2x10 (link J1p2x11 (link J1p2x12 (link J1p2x13 (link J1p2x14 (link J1p2x15 (link J1p2x16 (link J1p2x17 (link J1p2x18 (link J1p2x19 (link J1p2x20 (link J1p2x21 (link J1p2x22 (link J1p2x23 (link J1p2x24 (link J1p2x25 (link J1p2x26 (link J1p2x27 (link J1p2x28 (link J1p2x29 (link J1p2x30 (link J1p2x31 (rfl)))))))))))))))))))))))))))))
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p3 : job D1 [] 3 15576 19872 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p4 : job D1 [] 4 19872 22908 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p5 : job D1 [] 5 22908 25404 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p6 : job D1 [] 6 25404 27204 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p7 : job D1 [] 7 27204 28236 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p8 : job D1 [] 8 28236 29160 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p9 : job D1 [] 9 29160 29928 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J1p10 : job D1 [] 10 29928 30384 := by decide +kernel
theorem J1p11 : job D1 [] 11 30384 30660 := by decide +kernel
theorem J1p12 : job D1 [] 12 30660 30816 := by decide +kernel
theorem J1p13 : job D1 [] 13 30816 30936 := by decide +kernel
theorem J1p14 : job D1 [] 14 30936 31056 := by decide +kernel
theorem J1p15 : job D1 [] 15 31056 31116 := by decide +kernel
theorem J1p16 : job D1 [] 16 31116 31128 := by decide +kernel
theorem J1p17 : job D1 [] 17 31128 31140 := by decide +kernel
theorem J1p18 : job D1 [] 18 31140 31140 := by decide +kernel
theorem J1p19 : job D1 [] 19 31140 31140 := by decide +kernel
theorem J1p20 : job D1 [] 20 31140 31140 := by decide +kernel
theorem J1p21 : job D1 [] 21 31140 31140 := by decide +kernel
theorem J1p22 : job D1 [] 22 31140 31140 := by decide +kernel
theorem J1p23 : job D1 [] 23 31140 31140 := by decide +kernel
theorem J1p24 : job D1 [] 24 31140 31140 := by decide +kernel
theorem J1p25 : job D1 [] 25 31140 31140 := by decide +kernel
theorem J1p26 : job D1 [] 26 31140 31140 := by decide +kernel
theorem J1p27 : job D1 [] 27 31140 31140 := by decide +kernel
theorem J1p28 : job D1 [] 28 31140 31140 := by decide +kernel
theorem J1p29 : job D1 [] 29 31140 31140 := by decide +kernel
theorem J1p30 : job D1 [] 30 31140 31140 := by decide +kernel
theorem J1p31 : job D1 [] 31 31140 31140 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem fastD1 : fastOK coverPerms (entries.map asCat) D1 = true := by
  apply result (z := atBit D1 31140) (by decide +kernel) (by decide +kernel)
  exact link J1p1 (link J1p2 (link J1p3 (link J1p4 (link J1p5 (link J1p6 (link J1p7 (link J1p8 (link J1p9 (link J1p10 (link J1p11 (link J1p12 (link J1p13 (link J1p14 (link J1p15 (link J1p16 (link J1p17 (link J1p18 (link J1p19 (link J1p20 (link J1p21 (link J1p22 (link J1p23 (link J1p24 (link J1p25 (link J1p26 (link J1p27 (link J1p28 (link J1p29 (link J1p30 (link J1p31 (rfl)))))))))))))))))))))))))))))))

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData

open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p1x2 : job D2 [1] 2 0 1364 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p1x3 : job D2 [1] 3 1364 1364 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p1x4 : job D2 [1] 4 1364 1892 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p1x5 : job D2 [1] 5 1892 1892 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p1x8 : job D2 [1] 8 1892 2134 := by decide +kernel
theorem J2p1x9 : job D2 [1] 9 2134 2145 := by decide +kernel
theorem J2p1x10 : job D2 [1] 10 2145 2255 := by decide +kernel
theorem J2p1x11 : job D2 [1] 11 2255 2266 := by decide +kernel
theorem J2p1x12 : job D2 [1] 12 2266 2310 := by decide +kernel
theorem J2p1x13 : job D2 [1] 13 2310 2321 := by decide +kernel
theorem J2p1x16 : job D2 [1] 16 2321 2343 := by decide +kernel
theorem J2p1x17 : job D2 [1] 17 2343 2343 := by decide +kernel
theorem J2p1x18 : job D2 [1] 18 2343 2343 := by decide +kernel
theorem J2p1x19 : job D2 [1] 19 2343 2343 := by decide +kernel
theorem J2p1x20 : job D2 [1] 20 2343 2343 := by decide +kernel
theorem J2p1x21 : job D2 [1] 21 2343 2343 := by decide +kernel
theorem J2p1x24 : job D2 [1] 24 2343 2343 := by decide +kernel
theorem J2p1x25 : job D2 [1] 25 2343 2343 := by decide +kernel
theorem J2p1x26 : job D2 [1] 26 2343 2343 := by decide +kernel
theorem J2p1x27 : job D2 [1] 27 2343 2343 := by decide +kernel
theorem J2p1x28 : job D2 [1] 28 2343 2343 := by decide +kernel
theorem J2p1x29 : job D2 [1] 29 2343 2343 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p1 : job D2 [] 1 0 2343 := by
  apply join (mid := atBit D2 0) (by decide +kernel) (by decide +kernel)
  exact link J2p1x2 (link J2p1x3 (link J2p1x4 (link J2p1x5 (link J2p1x8 (link J2p1x9 (link J2p1x10 (link J2p1x11 (link J2p1x12 (link J2p1x13 (link J2p1x16 (link J2p1x17 (link J2p1x18 (link J2p1x19 (link J2p1x20 (link J2p1x21 (link J2p1x24 (link J2p1x25 (link J2p1x26 (link J2p1x27 (link J2p1x28 (link J2p1x29 (rfl))))))))))))))))))))))
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p2 : job D2 [] 2 2343 4356 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p3 : job D2 [] 3 4356 6666 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p4 : job D2 [] 4 6666 7799 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p5 : job D2 [] 5 7799 9009 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p8 : job D2 [] 8 9009 9735 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J2p9 : job D2 [] 9 9735 10208 := by decide +kernel
theorem J2p10 : job D2 [] 10 10208 10604 := by decide +kernel
theorem J2p11 : job D2 [] 11 10604 10835 := by decide +kernel
theorem J2p12 : job D2 [] 12 10835 10967 := by decide +kernel
theorem J2p13 : job D2 [] 13 10967 11066 := by decide +kernel
theorem J2p16 : job D2 [] 16 11066 11088 := by decide +kernel
theorem J2p17 : job D2 [] 17 11088 11099 := by decide +kernel
theorem J2p18 : job D2 [] 18 11099 11099 := by decide +kernel
theorem J2p19 : job D2 [] 19 11099 11099 := by decide +kernel
theorem J2p20 : job D2 [] 20 11099 11099 := by decide +kernel
theorem J2p21 : job D2 [] 21 11099 11099 := by decide +kernel
theorem J2p24 : job D2 [] 24 11099 11099 := by decide +kernel
theorem J2p25 : job D2 [] 25 11099 11099 := by decide +kernel
theorem J2p26 : job D2 [] 26 11099 11099 := by decide +kernel
theorem J2p27 : job D2 [] 27 11099 11099 := by decide +kernel
theorem J2p28 : job D2 [] 28 11099 11099 := by decide +kernel
theorem J2p29 : job D2 [] 29 11099 11099 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem fastD2 : fastOK coverPerms (entries.map asCat) D2 = true := by
  apply result (z := atBit D2 11099) (by decide +kernel) (by decide +kernel)
  exact link J2p1 (link J2p2 (link J2p3 (link J2p4 (link J2p5 (link J2p8 (link J2p9 (link J2p10 (link J2p11 (link J2p12 (link J2p13 (link J2p16 (link J2p17 (link J2p18 (link J2p19 (link J2p20 (link J2p21 (link J2p24 (link J2p25 (link J2p26 (link J2p27 (link J2p28 (link J2p29 (rfl)))))))))))))))))))))))

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD3 : fastOK coverPerms (entries.map asCat) D3 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD4 : fastOK coverPerms (entries.map asCat) D4 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD5 : fastOK coverPerms (entries.map asCat) D5 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData

open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p1x2 : job D6 [1] 2 0 1342 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p1x3 : job D6 [1] 3 1342 1782 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p1x4 : job D6 [1] 4 1782 2233 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p1x5 : job D6 [1] 5 2233 2409 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p1x6 : job D6 [1] 6 2409 2838 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p1x7 : job D6 [1] 7 2838 3135 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p1x8 : job D6 [1] 8 3135 3564 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p1x9 : job D6 [1] 9 3564 3564 := by decide +kernel
theorem J6p1x10 : job D6 [1] 10 3564 3949 := by decide +kernel
theorem J6p1x11 : job D6 [1] 11 3949 4048 := by decide +kernel
theorem J6p1x12 : job D6 [1] 12 4048 4246 := by decide +kernel
theorem J6p1x13 : job D6 [1] 13 4246 4268 := by decide +kernel
theorem J6p1x14 : job D6 [1] 14 4268 4312 := by decide +kernel
theorem J6p1x15 : job D6 [1] 15 4312 4345 := by decide +kernel
theorem J6p1x16 : job D6 [1] 16 4345 4367 := by decide +kernel
theorem J6p1x17 : job D6 [1] 17 4367 4367 := by decide +kernel
theorem J6p1x18 : job D6 [1] 18 4367 4389 := by decide +kernel
theorem J6p1x19 : job D6 [1] 19 4389 4400 := by decide +kernel
theorem J6p1x20 : job D6 [1] 20 4400 4400 := by decide +kernel
theorem J6p1x21 : job D6 [1] 21 4400 4400 := by decide +kernel
theorem J6p1x22 : job D6 [1] 22 4400 4400 := by decide +kernel
theorem J6p1x23 : job D6 [1] 23 4400 4400 := by decide +kernel
theorem J6p1x24 : job D6 [1] 24 4400 4400 := by decide +kernel
theorem J6p1x25 : job D6 [1] 25 4400 4400 := by decide +kernel
theorem J6p1x26 : job D6 [1] 26 4400 4400 := by decide +kernel
theorem J6p1x27 : job D6 [1] 27 4400 4400 := by decide +kernel
theorem J6p1x28 : job D6 [1] 28 4400 4400 := by decide +kernel
theorem J6p1x29 : job D6 [1] 29 4400 4400 := by decide +kernel
theorem J6p1x30 : job D6 [1] 30 4400 4400 := by decide +kernel
theorem J6p1x31 : job D6 [1] 31 4400 4400 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p1 : job D6 [] 1 0 4400 := by
  apply join (mid := atBit D6 0) (by decide +kernel) (by decide +kernel)
  exact link J6p1x2 (link J6p1x3 (link J6p1x4 (link J6p1x5 (link J6p1x6 (link J6p1x7 (link J6p1x8 (link J6p1x9 (link J6p1x10 (link J6p1x11 (link J6p1x12 (link J6p1x13 (link J6p1x14 (link J6p1x15 (link J6p1x16 (link J6p1x17 (link J6p1x18 (link J6p1x19 (link J6p1x20 (link J6p1x21 (link J6p1x22 (link J6p1x23 (link J6p1x24 (link J6p1x25 (link J6p1x26 (link J6p1x27 (link J6p1x28 (link J6p1x29 (link J6p1x30 (link J6p1x31 (rfl))))))))))))))))))))))))))))))
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p2x3 : job D6 [2] 3 4400 4840 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p2x4 : job D6 [2] 4 4840 5940 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p2x5 : job D6 [2] 5 5940 6578 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p2x6 : job D6 [2] 6 6578 6578 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p2x7 : job D6 [2] 7 6578 6688 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p2x8 : job D6 [2] 8 6688 6776 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p2x9 : job D6 [2] 9 6776 6963 := by decide +kernel
theorem J6p2x10 : job D6 [2] 10 6963 6974 := by decide +kernel
theorem J6p2x11 : job D6 [2] 11 6974 7106 := by decide +kernel
theorem J6p2x12 : job D6 [2] 12 7106 7304 := by decide +kernel
theorem J6p2x13 : job D6 [2] 13 7304 7348 := by decide +kernel
theorem J6p2x14 : job D6 [2] 14 7348 7370 := by decide +kernel
theorem J6p2x15 : job D6 [2] 15 7370 7403 := by decide +kernel
theorem J6p2x16 : job D6 [2] 16 7403 7425 := by decide +kernel
theorem J6p2x17 : job D6 [2] 17 7425 7447 := by decide +kernel
theorem J6p2x18 : job D6 [2] 18 7447 7447 := by decide +kernel
theorem J6p2x19 : job D6 [2] 19 7447 7458 := by decide +kernel
theorem J6p2x20 : job D6 [2] 20 7458 7458 := by decide +kernel
theorem J6p2x21 : job D6 [2] 21 7458 7458 := by decide +kernel
theorem J6p2x22 : job D6 [2] 22 7458 7458 := by decide +kernel
theorem J6p2x23 : job D6 [2] 23 7458 7458 := by decide +kernel
theorem J6p2x24 : job D6 [2] 24 7458 7458 := by decide +kernel
theorem J6p2x25 : job D6 [2] 25 7458 7458 := by decide +kernel
theorem J6p2x26 : job D6 [2] 26 7458 7458 := by decide +kernel
theorem J6p2x27 : job D6 [2] 27 7458 7458 := by decide +kernel
theorem J6p2x28 : job D6 [2] 28 7458 7458 := by decide +kernel
theorem J6p2x29 : job D6 [2] 29 7458 7458 := by decide +kernel
theorem J6p2x30 : job D6 [2] 30 7458 7458 := by decide +kernel
theorem J6p2x31 : job D6 [2] 31 7458 7458 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p2 : job D6 [] 2 4400 7458 := by
  apply join (mid := atBit D6 4400) (by decide +kernel) (by decide +kernel)
  exact link J6p2x3 (link J6p2x4 (link J6p2x5 (link J6p2x6 (link J6p2x7 (link J6p2x8 (link J6p2x9 (link J6p2x10 (link J6p2x11 (link J6p2x12 (link J6p2x13 (link J6p2x14 (link J6p2x15 (link J6p2x16 (link J6p2x17 (link J6p2x18 (link J6p2x19 (link J6p2x20 (link J6p2x21 (link J6p2x22 (link J6p2x23 (link J6p2x24 (link J6p2x25 (link J6p2x26 (link J6p2x27 (link J6p2x28 (link J6p2x29 (link J6p2x30 (link J6p2x31 (rfl)))))))))))))))))))))))))))))
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p3 : job D6 [] 3 7458 10450 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p4 : job D6 [] 4 10450 11506 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p5 : job D6 [] 5 11506 13222 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p6 : job D6 [] 6 13222 13860 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p7 : job D6 [] 7 13860 14300 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p8 : job D6 [] 8 14300 14509 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p9 : job D6 [] 9 14509 14993 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J6p10 : job D6 [] 10 14993 15356 := by decide +kernel
theorem J6p11 : job D6 [] 11 15356 15532 := by decide +kernel
theorem J6p12 : job D6 [] 12 15532 15631 := by decide +kernel
theorem J6p13 : job D6 [] 13 15631 15730 := by decide +kernel
theorem J6p14 : job D6 [] 14 15730 15829 := by decide +kernel
theorem J6p15 : job D6 [] 15 15829 15851 := by decide +kernel
theorem J6p16 : job D6 [] 16 15851 15862 := by decide +kernel
theorem J6p17 : job D6 [] 17 15862 15884 := by decide +kernel
theorem J6p18 : job D6 [] 18 15884 15895 := by decide +kernel
theorem J6p19 : job D6 [] 19 15895 15895 := by decide +kernel
theorem J6p20 : job D6 [] 20 15895 15895 := by decide +kernel
theorem J6p21 : job D6 [] 21 15895 15895 := by decide +kernel
theorem J6p22 : job D6 [] 22 15895 15895 := by decide +kernel
theorem J6p23 : job D6 [] 23 15895 15895 := by decide +kernel
theorem J6p24 : job D6 [] 24 15895 15895 := by decide +kernel
theorem J6p25 : job D6 [] 25 15895 15895 := by decide +kernel
theorem J6p26 : job D6 [] 26 15895 15895 := by decide +kernel
theorem J6p27 : job D6 [] 27 15895 15895 := by decide +kernel
theorem J6p28 : job D6 [] 28 15895 15895 := by decide +kernel
theorem J6p29 : job D6 [] 29 15895 15895 := by decide +kernel
theorem J6p30 : job D6 [] 30 15895 15895 := by decide +kernel
theorem J6p31 : job D6 [] 31 15895 15895 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem fastD6 : fastOK coverPerms (entries.map asCat) D6 = true := by
  apply result (z := atBit D6 15895) (by decide +kernel) (by decide +kernel)
  exact link J6p1 (link J6p2 (link J6p3 (link J6p4 (link J6p5 (link J6p6 (link J6p7 (link J6p8 (link J6p9 (link J6p10 (link J6p11 (link J6p12 (link J6p13 (link J6p14 (link J6p15 (link J6p16 (link J6p17 (link J6p18 (link J6p19 (link J6p20 (link J6p21 (link J6p22 (link J6p23 (link J6p24 (link J6p25 (link J6p26 (link J6p27 (link J6p28 (link J6p29 (link J6p30 (link J6p31 (rfl)))))))))))))))))))))))))))))))

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD7 : fastOK coverPerms (entries.map asCat) D7 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD8 : fastOK coverPerms (entries.map asCat) D8 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData

open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p1x2 : job D9 [1] 2 0 310 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p1x3 : job D9 [1] 3 310 390 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p1x4 : job D9 [1] 4 390 510 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p1x5 : job D9 [1] 5 510 550 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p1x6 : job D9 [1] 6 550 640 := by decide +kernel
theorem J9p1x7 : job D9 [1] 7 640 710 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p1x8 : job D9 [1] 8 710 880 := by decide +kernel
theorem J9p1x9 : job D9 [1] 9 880 880 := by decide +kernel
theorem J9p1x10 : job D9 [1] 10 880 980 := by decide +kernel
theorem J9p1x11 : job D9 [1] 11 980 1000 := by decide +kernel
theorem J9p1x12 : job D9 [1] 12 1000 1040 := by decide +kernel
theorem J9p1x13 : job D9 [1] 13 1040 1040 := by decide +kernel
theorem J9p1x14 : job D9 [1] 14 1040 1050 := by decide +kernel
theorem J9p1x15 : job D9 [1] 15 1050 1050 := by decide +kernel
theorem J9p1x16 : job D9 [1] 16 1050 1050 := by decide +kernel
theorem J9p1x17 : job D9 [1] 17 1050 1050 := by decide +kernel
theorem J9p1x18 : job D9 [1] 18 1050 1050 := by decide +kernel
theorem J9p1x19 : job D9 [1] 19 1050 1050 := by decide +kernel
theorem J9p1x20 : job D9 [1] 20 1050 1050 := by decide +kernel
theorem J9p1x21 : job D9 [1] 21 1050 1050 := by decide +kernel
theorem J9p1x22 : job D9 [1] 22 1050 1050 := by decide +kernel
theorem J9p1x23 : job D9 [1] 23 1050 1050 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p1 : job D9 [] 1 0 1050 := by
  apply join (mid := atBit D9 0) (by decide +kernel) (by decide +kernel)
  exact link J9p1x2 (link J9p1x3 (link J9p1x4 (link J9p1x5 (link J9p1x6 (link J9p1x7 (link J9p1x8 (link J9p1x9 (link J9p1x10 (link J9p1x11 (link J9p1x12 (link J9p1x13 (link J9p1x14 (link J9p1x15 (link J9p1x16 (link J9p1x17 (link J9p1x18 (link J9p1x19 (link J9p1x20 (link J9p1x21 (link J9p1x22 (link J9p1x23 (rfl))))))))))))))))))))))
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p2 : job D9 [] 2 1050 2280 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p3 : job D9 [] 3 2280 3390 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p4 : job D9 [] 4 3390 3840 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p5 : job D9 [] 5 3840 4410 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p6 : job D9 [] 6 4410 4660 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p7 : job D9 [] 7 4660 4770 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem J9p8 : job D9 [] 8 4770 4890 := by decide +kernel
theorem J9p9 : job D9 [] 9 4890 5110 := by decide +kernel
theorem J9p10 : job D9 [] 10 5110 5220 := by decide +kernel
theorem J9p11 : job D9 [] 11 5220 5300 := by decide +kernel
theorem J9p12 : job D9 [] 12 5300 5330 := by decide +kernel
theorem J9p13 : job D9 [] 13 5330 5370 := by decide +kernel
theorem J9p14 : job D9 [] 14 5370 5400 := by decide +kernel
theorem J9p15 : job D9 [] 15 5400 5410 := by decide +kernel
theorem J9p16 : job D9 [] 16 5410 5410 := by decide +kernel
theorem J9p17 : job D9 [] 17 5410 5410 := by decide +kernel
theorem J9p18 : job D9 [] 18 5410 5410 := by decide +kernel
theorem J9p19 : job D9 [] 19 5410 5410 := by decide +kernel
theorem J9p20 : job D9 [] 20 5410 5410 := by decide +kernel
theorem J9p21 : job D9 [] 21 5410 5410 := by decide +kernel
theorem J9p22 : job D9 [] 22 5410 5410 := by decide +kernel
theorem J9p23 : job D9 [] 23 5410 5410 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem fastD9 : fastOK coverPerms (entries.map asCat) D9 = true := by
  apply result (z := atBit D9 5410) (by decide +kernel) (by decide +kernel)
  exact link J9p1 (link J9p2 (link J9p3 (link J9p4 (link J9p5 (link J9p6 (link J9p7 (link J9p8 (link J9p9 (link J9p10 (link J9p11 (link J9p12 (link J9p13 (link J9p14 (link J9p15 (link J9p16 (link J9p17 (link J9p18 (link J9p19 (link J9p20 (link J9p21 (link J9p22 (link J9p23 (rfl)))))))))))))))))))))))

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD10 : fastOK coverPerms (entries.map asCat) D10 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD11 : fastOK coverPerms (entries.map asCat) D11 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD12 : fastOK coverPerms (entries.map asCat) D12 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD13 : fastOK coverPerms (entries.map asCat) D13 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD14 : fastOK coverPerms (entries.map asCat) D14 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD15 : fastOK coverPerms (entries.map asCat) D15 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData

open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
theorem J16p1 : job D16 [] 1 0 3 := by decide +kernel
theorem J16p2 : job D16 [] 2 3 3 := by decide +kernel
theorem J16p4 : job D16 [] 4 3 3 := by decide +kernel
theorem J16p8 : job D16 [] 8 3 3 := by decide +kernel
theorem J16p16 : job D16 [] 16 3 3 := by decide +kernel
set_option maxRecDepth 5000 in
set_option maxHeartbeats 9000000 in
theorem fastD16 : fastOK coverPerms (entries.map asCat) D16 = true := by
  apply result (z := atBit D16 3) (by decide +kernel) (by decide +kernel)
  exact link J16p1 (link J16p2 (link J16p4 (link J16p8 (link J16p16 (rfl)))))

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 160000000 in
theorem fastD17 : fastOK coverPerms (entries.map asCat) D17 = true := by decide +kernel

end MoonPrize.FastCatalogue

namespace MoonPrize.FastCatalogue
open MoonPrize.CatalogueData
open Coverage
open MoonPrize.Trace (entries)
open MoonPrize.Combine (asCat)

theorem complete_cover : MoonPrize.Combine.AllCriticalListed := by
  apply Coverage.mainFast (perms := coverPerms) (ds := ds) (canon := canonCodes) permutations_checked cover_types_checked
  intro d hd
  simp only [ds,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fastD0
  · exact fastD1
  · exact fastD2
  · exact fastD3
  · exact fastD4
  · exact fastD5
  · exact fastD6
  · exact fastD7
  · exact fastD8
  · exact fastD9
  · exact fastD10
  · exact fastD11
  · exact fastD12
  · exact fastD13
  · exact fastD14
  · exact fastD15
  · exact fastD16
  · exact fastD17

end MoonPrize.FastCatalogue

namespace MoonPrize.Combine

theorem numeric_all : MoonPrize.Bridge.NumericObstruction :=
  numeric_if MoonPrize.FastCatalogue.complete_cover (fun g hg =>
    ⟨(MoonPrize.Trace.ledger_parts (MoonPrize.Trace.entries_valid hg)).1,
      MoonPrize.Trace.all_listed g hg⟩)

end MoonPrize.Combine

end PEqualNP.Outside.L_meta_962

open PEqualNP.Outside.L_meta_962

theorem PEqualNP.Outside.L_meta_962 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 5 ≤ T.card) → ∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed → (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → 5 ≤ C.size :=
  MoonPrize.Bridge.target_of_numeric MoonPrize.Combine.numeric_all
