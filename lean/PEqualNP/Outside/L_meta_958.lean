import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_958_aux

open PEqualNP.AndCount AndCountCircuit

variable {n : Nat}

def left (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def right (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

private theorem side_congr {k : Nat} (I B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) {a b : Fin k → Bool} (h : ∀ j, j < i → a j = b j) :
    sideTrue I B F i a = sideTrue I B F i b := by
  unfold sideTrue
  congr 1
  apply propext
  constructor <;> rintro (raw | ⟨j, hj, lt, val⟩)
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt) ▸ val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt).symm ▸ val⟩

private theorem stable (C : AndCountCircuit n) (I : Finset (Fin n)) (m : Nat) :
    ∀ i : Fin C.size, i.val < m → ∀ a b : Nat, i.val < a → i.val < b →
    C.gateValFuel I a i = C.gateValFuel I b i := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi a b ha hb
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [gateValFuel]
        have eq (j : Fin C.size) (lt : j < i) :
            C.gateValFuel I a j = C.gateValFuel I b j :=
          ih j (by change j.val < i.val at lt; omega) a b
            (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
        rw [side_congr I _ _ i eq, side_congr I _ _ i eq]

theorem gate_eq (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal I i = (left C I i && right C I i) := by
  have h := stable C I C.size i i.isLt C.size (C.size + 1) i.isLt (by omega)
  exact h

def vars (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightVars i else C.leftVars i

def parents (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightGates i else C.leftGates i

def support (C : AndCountCircuit n) (q : Fin C.size → Bool) :
    Nat → Fin C.size → Finset (Fin n)
  | 0, _ => ∅
  | d+1, i => vars C q i ∪ ((parents C q i).filter (· < i)).biUnion (support C q d)

def hits (I S : Finset (Fin n)) := ∃ v ∈ S, v ∈ I

theorem hit_step (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i : Fin C.size) (I : Finset (Fin n)) :
    hits I (support C q (d+1) i) ↔ hits I (vars C q i) ∨
      ∃ j ∈ parents C q i, j < i ∧ hits I (support C q d j) := by
  simp only [hits, support, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv | ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩
    · exact Or.inl ⟨v, hv, hI⟩
    · exact Or.inr ⟨j, hj, lt, v, hv, hI⟩
  · rintro (⟨v, hv, hI⟩ | ⟨j, hj, lt, v, hv, hI⟩)
    · exact ⟨v, Or.inl hv, hI⟩
    · exact ⟨v, Or.inr ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩

def clause (C : AndCountCircuit n) (q : Fin C.size → Bool) :=
  C.outVars ∪ C.outGates.biUnion (support C q C.size)

theorem clause_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n)) :
    hits I (clause C q) ↔ hits I C.outVars ∨ ∃ j ∈ C.outGates, hits I (support C q C.size j) := by
  simp only [hits, clause, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv | ⟨j, hj, hv⟩, hi⟩
    · exact Or.inl ⟨v, hv, hi⟩
    · exact Or.inr ⟨j, hj, v, hv, hi⟩
  · rintro (⟨v, hv, hi⟩ | ⟨j, hj, v, hv, hi⟩)
    · exact ⟨v, Or.inl hv, hi⟩
    · exact ⟨v, Or.inr ⟨j, hj, hv⟩, hi⟩

theorem dominates (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (d : Nat) (i : Fin C.size) (hd : i.val < d) :
    C.gateVal I i = true → hits I (support C q d i) := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    rw [gate_eq, Bool.and_eq_true] at h
    apply (hit_step C q d i I).2
    have hs : sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = true := by
      cases e : q i <;> simp [vars, parents, e]
      · exact h.1
      · exact h.2
    rw [sideTrue, decide_eq_true_eq] at hs
    rcases hs with raw | ⟨j, hj, lt, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩

theorem chosen (C : AndCountCircuit n) (I : Finset (Fin n)) (d : Nat)
    (i : Fin C.size) (hd : i.val < d) :
    hits I (support C (left C I) d i) → C.gateVal I i = true := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    have hs : sideTrue I (vars C (left C I) i) (parents C (left C I) i) i (C.gateVal I) = true := by
      rw [sideTrue, decide_eq_true_eq]
      rcases (hit_step _ _ _ _ _).1 h with raw | ⟨j, hj, lt, val⟩
      · exact Or.inl raw
      · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩
    rw [gate_eq, Bool.and_eq_true]
    cases hl : left C I i with
    | false =>
      simp [vars, parents, hl] at hs
      change left C I i = true at hs
      simp [hl] at hs
    | true =>
      exact ⟨rfl, by simpa [vars, parents, hl, right] using hs⟩

theorem gives_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (h : C.eval I = true) : hits I (clause C q) := by
  rw [eval, decide_eq_true_eq] at h
  apply (clause_hit _ _ _).2
  rcases h with raw | ⟨j, hj, val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, dominates C q I C.size j j.isLt val⟩

theorem avoids (C : AndCountCircuit n) (I : Finset (Fin n)) (h : C.eval I = false) :
    ¬ hits I (clause C (left C I)) := by
  intro hit
  have ht : C.eval I = true := by
    rw [eval, decide_eq_true_eq]
    rcases (clause_hit _ _ _).1 hit with raw | ⟨j, hj, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, chosen C I C.size j j.isLt val⟩
  simp [h] at ht

theorem complement_clause (C : AndCountCircuit n) (I : Finset (Fin n))
    (h : C.eval I = false) (positive : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∀ u, u ∈ I ↔ u ∉ clause C (left C I) := by
  intro u
  constructor
  · intro hu hc
    exact avoids C I h ⟨u, hc, hu⟩
  · intro absent
    by_contra missing
    obtain ⟨v, hv, hin⟩ := gives_hit C (left C I) _ (positive u missing)
    rcases Finset.mem_insert.mp hin with rfl | inside
    · exact absent hv
    · exact avoids C I h ⟨v, hv, inside⟩

def indep (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :=
  ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b

def maximalIndep (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :=
  indep G I ∧ ∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v

theorem extend_indep (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (hU : indep G U) :
    ∃ I, U ⊆ I ∧ maximalIndep G I := by
  classical
  let sets := Finset.univ.filter fun I : Finset (Fin n) => U ⊆ I ∧ indep G I
  have hm : U ∈ sets := by simp [sets, hU]
  obtain ⟨I, hi, biggest⟩ := Finset.exists_max_image sets Finset.card ⟨U, hm⟩
  obtain ⟨sub, ind⟩ := (Finset.mem_filter.mp hi).2
  refine ⟨I, sub, ind, ?_⟩
  intro u hu
  by_contra h
  have miss : ∀ v ∈ I, ¬ G.Adj u v := by grind
  have ind' : indep G (insert u I) := by
    intro a ha b hb
    simp only [Finset.mem_insert] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · subst a; subst b; exact G.loopless.irrefl _
    · subst a; exact miss _ hb
    · subst b; exact fun e => miss _ ha e.symm
    · exact ind _ ha _ hb
  have larger : insert u I ∈ sets :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub.trans (Finset.subset_insert _ _), ind'⟩
  have := biggest _ larger
  rw [Finset.card_insert_of_notMem hu] at this
  omega

noncomputable def corners (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) :
    Finset (Fin C.size → Bool) := by
  classical
  exact (Finset.univ.filter (maximalIndep G)).image (left C)

noncomputable def profile (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (v : Fin n) :=
  (corners C G).filter fun q => v ∉ clause C q

def correctOn (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) :=
  ∀ I, maximalIndep G I → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

theorem enclosed_iff (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (U : Finset (Fin n)) :
    indep G U ↔ ∃ q ∈ corners C G, ∀ v ∈ U, q ∈ profile C G v := by
  classical
  constructor
  · intro hu
    obtain ⟨I, incl, maximal⟩ := extend_indep G U hu
    have inC : left C I ∈ corners C G :=
      Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ _, maximal⟩, rfl⟩
    refine ⟨left C I, inC, fun v hv => Finset.mem_filter.mpr ⟨inC, ?_⟩⟩
    exact (complement_clause C I (h I maximal).1 (h I maximal).2 v).mp (incl hv)
  · rintro ⟨q, hq, contains⟩
    obtain ⟨I, hi, rfl⟩ := Finset.mem_image.mp hq
    have maximal : maximalIndep G I := (Finset.mem_filter.mp hi).2
    have incl (v) (hv : v ∈ U) : v ∈ I :=
      (complement_clause C I (h I maximal).1 (h I maximal).2 v).mpr
        (Finset.mem_filter.mp (contains v hv)).2
    exact fun a ha b hb => maximal.1 a (incl a ha) b (incl b hb)

theorem profile_adj (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (a b : Fin n) : G.Adj a b ↔ Disjoint (profile C G a) (profile C G b) := by
  classical
  have e := enclosed_iff C G h {a,b}
  have eq : indep G {a,b} ↔ ¬ G.Adj a b := by
    constructor
    · exact fun t => t a (by simp) b (by simp)
    · intro t v hv w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
      · exact G.loopless.irrefl _
      · exact t
      · exact fun bad => t bad.symm
      · exact G.loopless.irrefl _
  rw [eq] at e
  constructor
  · intro adj
    rw [Finset.disjoint_left]
    intro q ha hb
    apply e.mpr _ adj
    refine ⟨q, (Finset.mem_filter.mp ha).1, ?_⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ha
    · exact hb
  · intro disj
    by_contra missing
    obtain ⟨q, _, hp⟩ := e.mp missing
    exact (Finset.disjoint_left.mp disj) (hp a (by simp)) (hp b (by simp))

theorem class_star {α : Type} [Nonempty (Fin n)] (f : Fin n → α) (G : SimpleGraph (Fin n))
    (same : ∀ a b v, f a = f b → (G.Adj a v ↔ G.Adj b v))
    (square : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (t : α) : ∃ z : Fin n, ∀ a b, f a = t → G.Adj a b → z = a ∨ z = b := by
  classical
  by_cases edge : ∃ a b, f a = t ∧ G.Adj a b
  · obtain ⟨a, b, atype, ab⟩ := edge
    by_cases second : ∃ c, f c = t ∧ c ≠ a
    · obtain ⟨c, ctype, ca⟩ := second
      refine ⟨b, ?_⟩
      intro u v ut uv
      right
      by_contra ne
      have av := (same u a v (ut.trans atype.symm)).mp uv
      have cv := (same u c v (ut.trans ctype.symm)).mp uv
      have cb := (same a c b (atype.trans ctype.symm)).mp ab
      exact square a b c v (Ne.symm ca) ne ab cb.symm cv av.symm
    · exact ⟨a, fun u _ ut _ => Or.inl (by by_contra h; exact second ⟨u, ut, Ne.symm h⟩)⟩
  · exact ⟨Classical.choice inferInstance, fun a b ha hb => False.elim (edge ⟨a,b,ha,hb⟩)⟩

theorem lift_cover {α : Type} [DecidableEq α] [Nonempty (Fin n)] (f : Fin n → α)
    (G : SimpleGraph (Fin n)) (star : ∀ t, ∃ z : Fin n, ∀ a b, f a = t → G.Adj a b → z = a ∨ z = b)
    (T : Finset α) (covers : ∀ a b, G.Adj a b → f a ∈ T ∨ f b ∈ T) :
    ∃ Q : Finset (Fin n), Q.card ≤ T.card ∧ ∀ a b, G.Adj a b → a ∈ Q ∨ b ∈ Q := by
  classical
  choose center hc using star
  refine ⟨T.image center, Finset.card_image_le, ?_⟩
  intro a b edge
  rcases covers a b edge with ha | hb
  · rcases hc (f a) a b rfl edge with e | e
    · exact Or.inl (Finset.mem_image.mpr ⟨f a, ha, e⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨f a, ha, e⟩)
  · rcases hc (f b) b a rfl edge.symm with e | e
    · exact Or.inr (Finset.mem_image.mpr ⟨f b, hb, e⟩)
    · exact Or.inl (Finset.mem_image.mpr ⟨f b, hb, e⟩)

abbrev maskCover (A T : Finset Nat) :=
  ∀ a ∈ A, ∀ b ∈ A, a &&& b = 0 → a ∈ T ∨ b ∈ T

abbrev forbidden (four : Bool) (a b c d : Nat) :=
  if four then a ≠ c ∧ b ≠ d ∧ a &&& b = 0 ∧ b &&& c = 0 ∧ c &&& d = 0 ∧ d &&& a = 0
  else a &&& b ≠ 0 ∧ b &&& c ≠ 0 ∧ c &&& a ≠ 0 ∧ a &&& b &&& c = 0

def blockSet (four : Bool) (a b c d : Nat) : Finset Nat :=
  if four then {a,b,c,d} else {a,b,c}

def admissible (X : Finset Nat) :=
  ∀ four a b c d, forbidden four a b c d → ¬ blockSet four a b c d ⊆ X

def arg (H : Array Nat) (word slot : Nat) :=
  H[(word >>> (2 + 5*slot)) % 32]?.getD 0

def leafSet (H : Array Nat) (w : Nat) : Finset Nat :=
  {arg H w 0, arg H w 1, arg H w 2}

def block (H : Array Nat) (w : Nat) :=
  blockSet (decide (w % 4 = 3)) (arg H w 0) (arg H w 1) (arg H w 2) (arg H w 3)

abbrev badWord (H : Array Nat) (w : Nat) :=
  forbidden (decide (w % 4 = 3)) (arg H w 0) (arg H w 1) (arg H w 2) (arg H w 3)

def wordAt (code : Array Nat) (pc : Nat) :=
  (code[pc / 32]?.getD 0 >>> (22 * (pc % 32))) % 4194304

def packBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k+1, f => Nat.bit (f 0) (packBits k (fun j => f (j+1)))

theorem pack_test (k j : Nat) (f : Nat → Bool) :
    (packBits k f).testBit j = (decide (j < k) && f j) := by
  induction k generalizing j f with
  | zero => simp [packBits]
  | succ k ih =>
    cases j with
    | zero => simp [packBits]
    | succ j => simp [packBits, Nat.testBit_bit_succ, ih]

theorem pack_lt (k : Nat) (f : Nat → Bool) : packBits k f < 2^k := by
  induction k generalizing f with
  | zero => simp [packBits]
  | succ k ih =>
    have h := ih (fun j => f (j+1))
    cases hb : f 0 <;> simp [packBits, hb, Nat.bit, pow_succ] <;> omega

def maskOf (S : Finset (Fin 8)) :=
  packBits 8 fun j => if h : j < 8 then decide ((⟨j,h⟩ : Fin 8) ∈ S) else false

theorem mask_bit (S : Finset (Fin 8)) (i : Fin 8) :
    (maskOf S).testBit i.val = decide (i ∈ S) := by simp [maskOf, pack_test, i.isLt]

theorem mask_inter (S T : Finset (Fin 8)) :
    maskOf (S ∩ T) = maskOf S &&& maskOf T := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8 <;> simp [maskOf, pack_test, Nat.testBit_and, hi]

theorem mask_zero (S : Finset (Fin 8)) : maskOf S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have e := mask_bit S v
    simp [h, hv] at e
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8 <;> simp [maskOf, pack_test, hi]

def sideChoice (C : AndCountCircuit n) (c : Fin 8) (i : Fin C.size) := c.val.testBit i.val

theorem all_choices (C : AndCountCircuit n) (bound : C.size ≤ 3) :
    Function.Surjective (sideChoice C) := by
  intro q
  let f (i : Nat) := if h : i < C.size then q ⟨i,h⟩ else false
  refine ⟨⟨packBits 3 f, pack_lt 3 f⟩, ?_⟩
  funext i
  have hi : i.val < 3 := lt_of_lt_of_le i.isLt bound
  simp [sideChoice, pack_test, hi, f, i.isLt]

noncomputable def maskSites (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) : Finset (Fin 8) := by
  classical
  exact Finset.univ.filter fun c => sideChoice C c ∈ corners C G

noncomputable def maskProfile (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (v : Fin n) :=
  (maskSites C G).filter fun c => v ∉ clause C (sideChoice C c)

theorem mask_enclosed (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (bound : C.size ≤ 3) (U : Finset (Fin n)) :
    indep G U ↔ ∃ c : Fin 8, c ∈ maskSites C G ∧ ∀ v ∈ U, c ∈ maskProfile C G v := by
  classical
  rw [enclosed_iff C G h U]
  constructor
  · rintro ⟨q, hq, all⟩
    obtain ⟨c, rfl⟩ := all_choices C bound q
    have hc : c ∈ maskSites C G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    exact ⟨c, hc, fun v hv => Finset.mem_filter.mpr ⟨hc, (Finset.mem_filter.mp (all v hv)).2⟩⟩
  · rintro ⟨c, hc, all⟩
    have hq : sideChoice C c ∈ corners C G := (Finset.mem_filter.mp hc).2
    exact ⟨_, hq, fun v hv => Finset.mem_filter.mpr ⟨hq, (Finset.mem_filter.mp (all v hv)).2⟩⟩

theorem mask_adj (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (bound : C.size ≤ 3) (u v : Fin n) :
    G.Adj u v ↔ maskOf (maskProfile C G u) &&& maskOf (maskProfile C G v) = 0 := by
  classical
  rw [← mask_inter, mask_zero, ← Finset.disjoint_iff_inter_eq_empty, profile_adj C G h]
  rw [Finset.disjoint_left, Finset.disjoint_left]
  constructor
  · intro no c hu hv
    have corner : sideChoice C c ∈ corners C G := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    exact no (Finset.mem_filter.mpr ⟨corner, (Finset.mem_filter.mp hu).2⟩)
      (Finset.mem_filter.mpr ⟨corner, (Finset.mem_filter.mp hv).2⟩)
  · intro no q hu hv
    obtain ⟨c, rfl⟩ := all_choices C bound q
    have corner : c ∈ maskSites C G :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).1⟩
    exact no (Finset.mem_filter.mpr ⟨corner, (Finset.mem_filter.mp hu).2⟩)
      (Finset.mem_filter.mpr ⟨corner, (Finset.mem_filter.mp hv).2⟩)

theorem mask_triple (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (h : correctOn C G) (bound : C.size ≤ 3) (a b c : Fin n)
    (hab : ¬ G.Adj a b) (hbc : ¬ G.Adj b c) (hca : ¬ G.Adj c a) :
    maskOf (maskProfile C G a) &&& maskOf (maskProfile C G b) &&&
      maskOf (maskProfile C G c) ≠ 0 := by
  classical
  have independent : indep G {a,b,c} := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first | exact G.loopless.irrefl _ | assumption |
      exact fun e => hab e.symm | exact fun e => hbc e.symm | exact fun e => hca e.symm
  obtain ⟨q, _, all⟩ := (mask_enclosed C G h bound _).mp independent
  rw [← mask_inter, ← mask_inter, ne_eq, mask_zero]
  exact Finset.Nonempty.ne_empty ⟨q, Finset.mem_inter.mpr
    ⟨Finset.mem_inter.mpr ⟨all a (by simp), all b (by simp)⟩, all c (by simp)⟩⟩

theorem image_admissible (G : SimpleGraph (Fin n)) (f : Fin n → Nat)
    (pair : ∀ u v, G.Adj u v ↔ f u &&& f v = 0)
    (triple : ∀ a b c, ¬ G.Adj a b → ¬ G.Adj b c → ¬ G.Adj c a →
      f a &&& f b &&& f c ≠ 0)
    (square : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) :
    admissible (Finset.univ.image f) := by
  classical
  intro four a b c d bad sub
  have pre (x) (hx : x ∈ blockSet four a b c d) : ∃ i, f i = x := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (sub hx)
    exact ⟨i, hi⟩
  obtain ⟨u, rfl⟩ := pre a (by cases four <;> simp [blockSet])
  obtain ⟨v, rfl⟩ := pre b (by cases four <;> simp [blockSet])
  obtain ⟨w, rfl⟩ := pre c (by cases four <;> simp [blockSet])
  cases four with
  | false =>
    obtain ⟨ab, bc, ca, abc⟩ := bad
    exact triple u v w (fun e => ab ((pair _ _).mp e))
      (fun e => bc ((pair _ _).mp e)) (fun e => ca ((pair _ _).mp e)) abc
  | true =>
    obtain ⟨z, rfl⟩ := pre d (by simp [blockSet])
    obtain ⟨ac, bd, ab, bc, cd, da⟩ := bad
    exact square u v w z (fun e => ac (congrArg f e)) (fun e => bd (congrArg f e))
      ((pair _ _).mpr ab) ((pair _ _).mpr bc) ((pair _ _).mpr cd) ((pair _ _).mpr da)

theorem transfer_host [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) (f : Fin n → Nat)
    (pair : ∀ u v, G.Adj u v ↔ f u &&& f v = 0)
    (triple : ∀ a b c, ¬ G.Adj a b → ¬ G.Adj b c → ¬ G.Adj c a →
      f a &&& f b &&& f c ≠ 0)
    (square : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (T : Finset Nat) (host : ∀ X ⊆ T, admissible X → ∃ Q : Finset Nat, Q.card ≤ 3 ∧ maskCover X Q)
    (contained : ∀ v, f v ∈ T) :
    ∃ Q : Finset (Fin n), Q.card ≤ 3 ∧ ∀ a b, G.Adj a b → a ∈ Q ∨ b ∈ Q := by
  classical
  have sub : Finset.univ.image f ⊆ T := by
    rintro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact contained v
  obtain ⟨Q, card, cover⟩ := host _ sub (image_admissible G f pair triple square)
  have star := class_star f G (fun a b v e => by rw [pair, pair, e]) square
  obtain ⟨V, bound, full⟩ := lift_cover f G star Q (fun a b edge =>
    cover _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
      _ (Finset.mem_image_of_mem _ (Finset.mem_univ b)) ((pair a b).mp edge))
  exact ⟨V, bound.trans card, full⟩

def wiring (C : AndCountCircuit n) (i : Nat) (b : Bool) (j : Nat) : Bool :=
  if hi : i < C.size then
    if hj : j < C.size then decide ((⟨j,hj⟩ : Fin C.size) ∈
      if b then C.rightGates ⟨i,hi⟩ else C.leftGates ⟨i,hi⟩) else false
  else false

def outputFlag (C : AndCountCircuit n) (i : Nat) : Bool :=
  if h : i < C.size then decide ((⟨i,h⟩ : Fin C.size) ∈ C.outGates) else false

def topology (C : AndCountCircuit n) := packBits 9 fun k => match k with
  | 0 => wiring C 1 false 0
  | 1 => wiring C 1 true 0
  | 2 => wiring C 2 false 0
  | 3 => wiring C 2 false 1
  | 4 => wiring C 2 true 0
  | 5 => wiring C 2 true 1
  | k+6 => outputFlag C k

def wireSlot (i : Nat) (b : Bool) (j : Nat) :=
  if i = 1 then b.toNat else 2 + 2*b.toNat + j

theorem topology_wire (C : AndCountCircuit n) (i j : Nat) (b : Bool)
    (hi : i < 3) (hj : j < i) :
    (topology C).testBit (wireSlot i b j) = wiring C i b j := by
  unfold topology
  rw [pack_test]
  interval_cases i <;> interval_cases j <;> cases b <;> rfl

theorem topology_out (C : AndCountCircuit n) (i : Nat) (hi : i < 3) :
    (topology C).testBit (6+i) = outputFlag C i := by
  unfold topology
  rw [pack_test]
  interval_cases i <;> rfl

def rawFlag (C : AndCountCircuit n) (v : Fin n) (i : Nat) (b : Bool) : Bool :=
  if hi : i < C.size then
    decide (v ∈ if b then C.rightVars ⟨i,hi⟩ else C.leftVars ⟨i,hi⟩)
  else false

def patternOf (C : AndCountCircuit n) (v : Fin n) := packBits 6 fun k =>
  rawFlag C v (k/2) (k.testBit 0)

theorem pattern_raw (C : AndCountCircuit n) (v : Fin n) (i : Nat) (b : Bool) (hi : i < 3) :
    (patternOf C v).testBit (2*i + b.toNat) = rawFlag C v i b := by
  unfold patternOf
  rw [pack_test]
  interval_cases i <;> cases b <;> rfl

def numGate (t p c : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | d+1, i =>
    let b := c.testBit i
    p.testBit (2*i + b.toNat) || (List.range i).any fun j =>
      t.testBit (wireSlot i b j) && numGate t p c d j

theorem num_support (C : AndCountCircuit n) (bound : C.size ≤ 3) (v : Fin n) (c : Fin 8)
    (d : Nat) (i : Fin C.size) :
    numGate (topology C) (patternOf C v) c.val d i.val = true ↔
      v ∈ support C (sideChoice C c) d i := by
  induction d generalizing i with
  | zero => simp [numGate, support]
  | succ d ih =>
    have h3 := lt_of_lt_of_le i.isLt bound
    simp only [numGate, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      support, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, pattern_raw C v _ _ h3]
    apply or_congr
    · cases e : c.val.testBit i.val <;> simp [rawFlag, vars, sideChoice, i.isLt, e]
    · constructor
      · rintro ⟨j, lt, wire, pass⟩
        let k : Fin C.size := ⟨j, lt_trans lt i.isLt⟩
        rw [topology_wire _ _ _ _ h3 lt] at wire
        have mem : k ∈ parents C (sideChoice C c) i := by
          cases e : c.val.testBit i.val <;> simpa [wiring, parents, sideChoice, i.isLt, k, lt_trans lt i.isLt, e] using wire
        exact ⟨k, ⟨mem, lt⟩, (ih k).mp pass⟩
      · rintro ⟨k, ⟨mem, lt⟩, pass⟩
        refine ⟨k.val, lt, ?_, (ih k).mpr pass⟩
        rw [topology_wire _ _ _ _ h3 lt]
        cases e : c.val.testBit i.val <;> simpa [wiring, parents, sideChoice, i.isLt, k.isLt, e] using mem

theorem support_stable (C : AndCountCircuit n) (q : Fin C.size → Bool)
    (a : Nat) (i : Fin C.size) (ha : i.val < a) (b : Nat) (hb : i.val < b) :
    support C q a i = support C q b i := by
  induction a generalizing i b with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [support]
      congr 1
      apply Finset.biUnion_congr rfl
      intro j hj
      have lt : j.val < i.val := (Finset.mem_filter.mp hj).2
      exact ih j (by omega) b (by omega)

theorem no_outVar (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (v : Fin n) : v ∉ C.outVars := by
  have single : indep G {v} := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b; exact G.loopless.irrefl _
  obtain ⟨I, sub, maximal⟩ := extend_indep G {v} single
  intro member
  exact avoids C I (h I maximal).1 ⟨v, Finset.mem_union_left _ member, sub (by simp)⟩

def numOut (t p c : Nat) :=
  (List.range 3).any fun i => t.testBit (6+i) && numGate t p c 3 i

theorem num_clause (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (bound : C.size ≤ 3) (v : Fin n) (c : Fin 8) :
    numOut (topology C) (patternOf C v) c.val = true ↔ v ∈ clause C (sideChoice C c) := by
  simp only [numOut, List.any_eq_true, List.mem_range, Bool.and_eq_true, clause, Finset.mem_union,
    no_outVar C G h v, false_or, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, flag, ok⟩
    rw [topology_out C i hi] at flag
    by_cases inside : i < C.size
    · let j : Fin C.size := ⟨i, inside⟩
      refine ⟨j, by simpa [outputFlag, inside, j] using flag, ?_⟩
      rw [support_stable C _ C.size j j.isLt 3 hi]
      exact (num_support C bound v c 3 j).mp ok
    · simp [outputFlag, inside] at flag
  · rintro ⟨j, hout, hv⟩
    have hi := lt_of_lt_of_le j.isLt bound
    refine ⟨j.val, hi, ?_, (num_support C bound v c 3 j).mpr ?_⟩
    · simpa [topology_out C _ hi, outputFlag, j.isLt] using hout
    · rwa [support_stable C _ 3 j hi C.size j.isLt]

def wholeProfile (t p : Nat) := packBits 8 fun c => !numOut t p c

theorem numeric_profile (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : correctOn C G)
    (bound : C.size ≤ 3) (v : Fin n) :
    maskOf (maskProfile C G v) =
      maskOf (maskSites C G) &&& wholeProfile (topology C) (patternOf C v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 8
  · let c : Fin 8 := ⟨i,hi⟩
    rw [show i = c.val from rfl, mask_bit, mask_bit]
    have eq := num_clause C G h bound v c
    have small : c.val < 8 := c.isLt
    cases val : numOut (topology C) (patternOf C v) c.val <;>
      simp_all [maskProfile, wholeProfile, pack_test]
  · simp [maskOf, wholeProfile, pack_test, hi]

def oldIndex (perm j : Nat) := (perm >>> (3*j)) % 8
def relabel (perm a : Nat) := packBits 8 fun j => a.testBit (oldIndex perm j)
abbrev permOK (perm : Nat) := ∀ i : Fin 8, ∃ j : Fin 8, oldIndex perm j.val = i.val
theorem relabel_inter (p a b : Nat) : relabel p (a &&& b) = relabel p a &&& relabel p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8 <;> simp [relabel, pack_test, Nat.testBit_and, hi]

theorem relabel_zero (p a : Nat) (hp : permOK p) (ha : a < 256) :
    relabel p a = 0 ↔ a = 0 := by
  constructor
  · intro eq
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · obtain ⟨j,hj⟩ := hp ⟨i,hi⟩
      have bit := congrArg (fun x : Nat => x.testBit j.val) eq
      simpa [relabel, pack_test, j.isLt, hj] using bit
    · have large : 2^8 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha large)
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    simp [relabel, pack_test]

theorem relabeled_pair (perm : Nat) (ok : permOK perm) (a b : Nat) (ha : a < 256) :
    relabel perm a &&& relabel perm b = 0 ↔ a &&& b = 0 := by
  rw [← relabel_inter]
  exact relabel_zero _ _ ok (lt_of_le_of_lt Nat.and_le_left ha)

theorem relabeled_triple (perm : Nat) (ok : permOK perm) (a b c : Nat) (ha : a < 256) :
    relabel perm a &&& relabel perm b &&& relabel perm c = 0 ↔ a &&& b &&& c = 0 := by
  rw [← relabel_inter, ← relabel_inter]
  exact relabel_zero _ _ ok (lt_of_le_of_lt (Nat.and_le_left.trans Nat.and_le_left) ha)

def off (a v : Nat) := a ^^^ (a &&& (2^v))
def on (a v : Nat) := a ||| (2^v)

theorem off_bit (a v i : Nat) : (off a v).testBit i = (a.testBit i && decide (i ≠ v)) := by
  by_cases eq : i = v
  · subst i; cases h : a.testBit v <;> simp [off, Nat.testBit_xor, Nat.testBit_and, h]
  · cases h : a.testBit i <;> simp [off, Nat.testBit_xor, Nat.testBit_and, h, eq, Ne.symm eq]

theorem on_bit (a v i : Nat) : (on a v).testBit i = (a.testBit i || decide (i = v)) := by
  by_cases eq : i = v
  · subst i; simp [on, Nat.testBit_or]
  · simp [on, Nat.testBit_or, eq, Ne.symm eq]

def lookup (a : Array Nat) (i : Nat) := a[i]?.getD 0
def hit3 (H : Array Nat) (w A : Nat) := off (off (off A (arg H w 0)) (arg H w 1)) (arg H w 2)
def fastLeaf (H N : Array Nat) (w A : Nat) :=
  let left := hit3 H w A
  (List.range H.size).all fun i =>
    !(left.testBit (lookup H i)) || (lookup N i &&& left == 0)

def listed (H : Array Nat) (x : Nat) := ∃ i < H.size, lookup H i = x
def validRows (H N : Array Nat) := ∀ i < H.size, ∀ j < H.size,
  lookup H i &&& lookup H j = 0 → (lookup N i).testBit (lookup H j) = true

theorem fast_leaf_sound (H N : Array Nat) (rows : validRows H N) (w A : Nat)
    (X : Finset Nat) (inside : ∀ x ∈ X, listed H x) (active : ∀ x ∈ X, A.testBit x = true)
    (ok : fastLeaf H N w A = true) : maskCover X (leafSet H w) := by
  intro a ha b hb disj
  by_contra miss
  push Not at miss
  have outside (z : Nat) (hz : z ∈ X) (hout : z ∉ leafSet H w) :
      (hit3 H w A).testBit z = true := by
    simpa [hit3, off_bit, active z hz, leafSet, and_assoc] using hout
  obtain ⟨i, hi, ei⟩ := inside a ha
  obtain ⟨j, hj, ej⟩ := inside b hb
  have leftA := outside a ha miss.1
  have leftB := outside b hb miss.2
  have test := List.all_eq_true.mp ok i (List.mem_range.mpr hi)
  change (!(hit3 H w A).testBit (lookup H i) || (lookup N i &&& hit3 H w A == 0)) = true at test
  rw [ei, leftA] at test
  have zero : lookup N i &&& hit3 H w A = 0 := by simpa using test
  have neighbor : (lookup N i).testBit b = true := by
    simpa [ej] using rows i hi j hj (by simpa [ei,ej] using disj)
  have bit := congrArg (fun m : Nat => m.testBit b) zero
  simp [Nat.testBit_and, neighbor, leftB] at bit

def fastCheck (H N code : Array Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | fuel+1, pc, A, P =>
    let w := wordAt code pc
    let v := arg H w 0
    if w % 4 = 0 then fastLeaf H N w A
    else if w % 4 = 1 then
      fastCheck H N code fuel (pc+1) (off A v) P &&
        fastCheck H N code fuel (pc + (w >>> 7)) A (on P v)
    else
      decide (badWord H w) &&
        decide (∀ z ∈ (block H w).erase v, P.testBit z = true) &&
        (P.testBit v || fastCheck H N code fuel (pc+1) (off A v) P)

theorem fast_sound (H N code : Array Nat) (rows : validRows H N) (fuel pc A P : Nat)
    (X : Finset Nat) (good : admissible X) (inside : ∀ x ∈ X, listed H x)
    (low : ∀ x, P.testBit x = true → x ∈ X) (high : ∀ x ∈ X, A.testBit x = true)
    (ok : fastCheck H N code fuel pc A P = true) :
    ∃ T : Finset Nat, T.card ≤ 3 ∧ maskCover X T := by
  induction fuel generalizing pc A P with
  | zero => simp [fastCheck] at ok
  | succ fuel ih =>
    let w := wordAt code pc
    let v := arg H w 0
    have shrink (absent : v ∉ X) : ∀ x ∈ X, (off A v).testBit x = true := by
      intro x hx
      simp [off_bit, high x hx, show x ≠ v from fun e => absent (e ▸ hx)]
    unfold fastCheck at ok
    by_cases leaf : w % 4 = 0
    · rw [ite_eq_left leaf] at ok
      refine ⟨leafSet H w, ?_, fast_leaf_sound H N rows w A X inside high ok⟩
      unfold leafSet
      exact (Finset.card_insert_le _ _).trans (by
        have := Finset.card_insert_le (arg H w 1) ({arg H w 2} : Finset Nat)
        simp only [Finset.card_singleton] at this
        omega)
    · rw [ite_eq_right leaf] at ok
      by_cases fork : w % 4 = 1
      · rw [ite_eq_left fork, Bool.and_eq_true] at ok
        by_cases included : v ∈ X
        · refine ih _ _ _ ?_ high ok.2
          intro z hz
          rw [on_bit, Bool.or_eq_true, decide_eq_true_eq] at hz
          rcases hz with hold | rfl
          · exact low z hold
          · exact included
        · exact ih _ _ _ low (shrink included) ok.1
      · rw [ite_eq_right fork, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ok
        obtain ⟨⟨bad, others⟩, step⟩ := ok
        have absent : v ∉ X := by
          intro contained
          apply good _ _ _ _ _ bad
          intro z hz
          by_cases e : z = v
          · exact e ▸ contained
          · exact low z (others z (Finset.mem_erase.mpr ⟨e,hz⟩))
        have notNeeded : P.testBit v = false := by
          cases eq : P.testBit v <;> simp_all
        rw [show arg H (wordAt code pc) 0 = v from rfl, notNeeded, Bool.false_or] at step
        exact ih _ _ _ low (shrink absent) step

def bookOK (H N : Array Nat) (A : Nat) :=
  (List.range H.size).all fun i =>
    A.testBit (lookup H i) && (List.range H.size).all fun j =>
      (lookup H i &&& lookup H j != 0) || (lookup N i).testBit (lookup H j)

def hostSafe (H : Array Nat) := ∀ X ⊆ H.toList.toFinset, admissible X →
  ∃ Q : Finset Nat, Q.card ≤ 3 ∧ maskCover X Q

theorem certify (H N D : Array Nat) (A fuel : Nat)
    (book : bookOK H N A = true) (certificate : fastCheck H N D fuel 0 A 0 = true) :
    hostSafe H := by
  intro X sub good
  have entry (i : Nat) (hi : i < H.size) := List.all_eq_true.mp book i (List.mem_range.mpr hi)
  have rows : validRows H N := by
    intro i hi j hj eq
    have both := entry i hi
    simp only [Bool.and_eq_true] at both
    have v := List.all_eq_true.mp both.2 j (List.mem_range.mpr hj)
    simpa [eq] using v
  have inside (x) (hx : x ∈ X) : listed H x := by
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem (show x ∈ H.toList by simpa using sub hx)
    have hlen : i < H.size := by simpa using hi
    exact ⟨i, hlen, by simpa [lookup, Array.getElem?_eq_getElem hlen] using he⟩
  apply fast_sound H N D rows fuel 0 A 0 X good inside _ _ certificate
  · simp
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := inside x hx
    have both := entry i hi
    simp only [Bool.and_eq_true] at both
    exact both.1

def region (H : Array Nat) (A P : Nat) := ∀ X : Finset Nat, admissible X →
  (∀ x ∈ X, listed H x) → (∀ x, P.testBit x = true → x ∈ X) →
  (∀ x ∈ X, A.testBit x = true) → ∃ Q : Finset Nat, Q.card ≤ 3 ∧ maskCover X Q

theorem regionFork (H : Array Nat) (A P v : Nat)
    (no : region H (off A v) P) (yes : region H A (on P v)) : region H A P := by
  intro X good inside low high
  by_cases included : v ∈ X
  · apply yes X good inside _ high
    intro z hz
    rw [on_bit, Bool.or_eq_true, decide_eq_true_eq] at hz
    rcases hz with kept | rfl
    · exact low z kept
    · exact included
  · apply no X good inside low
    intro x hx
    simp [off_bit, high x hx, show x ≠ v from fun e => included (e ▸ hx)]

theorem regionDrop (H : Array Nat) (A P w : Nat) (bad : badWord H w)
    (other : ∀ z ∈ (block H w).erase (arg H w 0), P.testBit z = true)
    (next : region H (off A (arg H w 0)) P) : region H A P := by
  intro X good inside low high
  have absent : arg H w 0 ∉ X := by
    intro present
    apply good _ _ _ _ _ bad
    intro z hz
    by_cases eq : z = arg H w 0
    · exact eq ▸ present
    · exact low z (other z (Finset.mem_erase.mpr ⟨eq,hz⟩))
  apply next X good inside low
  intro x hx
  simp [off_bit, high x hx, show x ≠ arg H w 0 from fun e => absent (e ▸ hx)]

theorem regionTerm (H N D : Array Nat) (rows : validRows H N) (A P fuel : Nat)
    (certificate : fastCheck H N D fuel 0 A P = true) : region H A P :=
  fun X good inside low high => fast_sound H N D rows fuel 0 A P X good inside low high certificate

theorem rows_of_book (H N : Array Nat) (A : Nat) (book : bookOK H N A = true) :
    validRows H N := by
  intro i hi j hj eq
  have both := List.all_eq_true.mp book i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true] at both
  have v := List.all_eq_true.mp both.2 j (List.mem_range.mpr hj)
  simpa [eq] using v

theorem regionHost (H N : Array Nat) (A : Nat) (book : bookOK H N A = true)
    (solved : region H A 0) : hostSafe H := by
  intro X sub good
  have inside (x) (hx : x ∈ X) : listed H x := by
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem (show x ∈ H.toList by simpa using sub hx)
    have hlen : i < H.size := by simpa using hi
    exact ⟨i, hlen, by simpa [lookup, Array.getElem?_eq_getElem hlen] using he⟩
  apply solved X good inside _ _
  · simp
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := inside x hx
    have both := List.all_eq_true.mp book i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true] at both
    exact both.1

def familyAt (families : Array (Array Nat)) (index : Nat) := families[index]?.getD #[]

def topologyOK (t : Nat) (T : Array Nat) :=
  (List.range 64).all fun p => T.toList.contains (wholeProfile t p)

def cutOK (s word : Nat) (T : Array Nat) (hosts : Array (Array Nat)) :=
  let perm := word >>> 6
  let host := familyAt hosts (word % 64)
  decide (word % 64 < hosts.size) && decide (permOK perm) &&
    T.toList.all fun z => (s &&& z == 0) || host.toList.contains (relabel perm (s &&& z))

theorem classify_graph (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (h : correctOn C G) (bound : C.size ≤ 3) (hosts : Array (Array Nat))
    (classification : ∀ t < 512, ∀ s < 256, ∃ T : Array Nat, ∃ w : Nat,
      topologyOK t T = true ∧ cutOK s w T hosts = true)
    (safe : ∀ i < hosts.size, hostSafe (familyAt hosts i)) [Nonempty (Fin n)]
    (square : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) :
    ∃ Q : Finset (Fin n), Q.card ≤ 3 ∧ ∀ a b, G.Adj a b → a ∈ Q ∨ b ∈ Q := by
  classical
  let s := maskOf (maskSites C G)
  let f := fun v => maskOf (maskProfile C G v)
  have bounded (v : Fin n) : f v < 256 := pack_lt 8 _
  obtain ⟨T,w,top,cut⟩ := classification (topology C) (pack_lt 9 _) s (pack_lt 8 _)
  let perm := w >>> 6
  let H := familyAt hosts (w % 64)
  simp only [cutOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at cut
  have hp : permOK perm := cut.1.2
  apply transfer_host G (fun v => relabel perm (f v)) _ _ square H.toList.toFinset
    (safe _ cut.1.1)
  · intro v
    have nonzero : f v ≠ 0 := by
      intro e
      exact G.loopless.irrefl v ((mask_adj C G h bound v v).mpr (by change f v &&& f v = 0; simp [e]))
    have full := List.all_eq_true.mp top (patternOf C v) (List.mem_range.mpr (pack_lt 6 _))
    have member : wholeProfile (topology C) (patternOf C v) ∈ T.toList := by simpa using full
    have ok := cut.2 _ member
    have eq : f v = s &&& wholeProfile (topology C) (patternOf C v) := numeric_profile C G h bound v
    rw [← eq] at ok
    simpa [nonzero, H, perm] using ok
  · intro a b
    exact (mask_adj C G h bound a b).trans (relabeled_pair perm hp _ _ (bounded a)).symm
  · intro a b c ab bc ca zero
    exact mask_triple C G h bound a b c ab bc ca ((relabeled_triple perm hp _ _ _ (bounded a)).mp zero)



-- The finite classification uses eight-bit masks for corners and their intersections.
def H0 : Array Nat := #[1]
def D0 : Array Nat := #[0x0]
def N0 : Array Nat := #[0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe0 : hostSafe H0 := certify H0 N0 D0 0x2 2 (by decide +kernel) (by decide +kernel)

def H1 : Array Nat := #[1, 2, 3]
def D1 : Array Nat := #[0x0]
def N1 : Array Nat := #[0x4, 0x2, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe1 : hostSafe H1 := certify H1 N1 D1 0xe 4 (by decide +kernel) (by decide +kernel)

def H2 : Array Nat := #[1, 2, 3, 4, 5, 6, 7]
def D2 : Array Nat := #[0x2080]
def N2 : Array Nat := #[0x54, 0x32, 0x10, 0xe, 0x4, 0x2, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe2 : hostSafe H2 := certify H2 N2 D2 0xfe 8 (by decide +kernel) (by decide +kernel)

def H3 : Array Nat := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def D3 : Array Nat := #[0x4840c2aa030a980628041403d05007020e300010101c600001210010c407184020cd80832601c6000933200c2006101f0182000010d01860000105018610001010012940062100c20000119002454012110096b403409,
  0xa412438f490e0c094000004740030502506806204404e5d0138f39020c0808000047408380000414004a50208d80418022407c89007024e100010101c2000012500108400ea9018a010500f41401c0838400040407080,
  0x4040b49601c2000012502c8a80b2220002002b00f28028c2b01f014600001050146100010102caa80b2a600c20000115001a4400c190188112408f49020c0938c000414071840004940a2360288580520449023d24083,
  0x4040030502d0680618840ce5d0338738860c0818000047408380000434004ad0204d8081260082004b01f12c03c0b38c000404071800004b400421003c4401ab101c2000b32a02cc980b3220106008901f22401c04184,
  0x304d80c1260304580b20012c27c4b08f0104004b01f12c03c093880004040030502c8a80b2220106008919f22461c072000004340912201c610001250012b4041360104580b40012c27c4b08f0144004b01f12c03c05188,
  0x208012c27c4b08f02ce300010501c6100012d]
def N3 : Array Nat := #[0x5554, 0x3332, 0x1110, 0xf0e, 0x504, 0x302, 0x100, 0xfe, 0x54, 0x32, 0x10, 0xe, 0x4, 0x2, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe3 : hostSafe H3 := certify H3 N3 D3 0xfffe 16 (by decide +kernel) (by decide +kernel)

def H4 : Array Nat := #[1, 2, 3, 4, 5, 8, 10, 11, 16, 20, 21, 24, 26, 28, 31]
def D4 : Array Nat := #[0x1cc4000109000c540920800048407236025020001110020a406288328a9cca2a3328a4c05208000464062080004540a132018a20a8127408a4c062080004540920800048400429018a40001090028740180d00c41405981,
  0x10620881b32206bc8819b018620861b32186bc041880004640032101862000111001a7401015018a20ca2a7328a8cca2930250500011902506000115028ed80a3b2028eb8072903a0a9d0521b410a2c082082204bce8127,
  0x40ca4d0518b01ca20851b32146bc8519b000a312519f49466d2518b02862000125000e4400621018620e332738cc8c083880004640a3b6028ec80a3ae01c8310719b41c62c0720c49c66d2718b01062000125000c8400529,
  0x4540a3b6028ec80a3ae028410aa0a72a824c0610432829cca09301041000119000c540051d010410450b71142bc450a7024810490b71242bc041040004940031502481000109001aa4010210064340028c41467d0519b,
  0x10c2bc430a701c610811b32046bc071840004440030900166400821002e54082842a02aca80a741424d0128b029040480b71202bc480a701cc10c80ab32029cc809301c81000119000e2400615028410aa0a72a824c09304,
  0x18400001110304a8061000004c4062000004240051d0026b400ea100525401d8d00b214001841942bca30ab28c29ca30a328c24ca118b000610680af40467d0119b40c24d0118b00c410c30ab30c29cc3093010610430b7,
  0xe4400621031060480371200bc4802701c800880332200bc8801b01cc0000111000e240c59812c0dc4b02701c8008b03322c06c0730000044400309024c000a3b6028ec80920001c8d809100000444002a90104008c01b,
  0x40062c0b3801ac0cc6b01b58062c0418048067d2019b48062c0d60c1b006c0d30c0004c4002a50014b4007a1002c54072802a009d0501b400a4d0028b035250850332140bc8501b028400450371140bc4502702920000109,
  0x2802aca102728024c0b5000ac0dc2b02758024c020803002acc00a730024c0d6040b409c0c4840004d4002990014b400795002c8400f0d014600650331940bca302728c08c6501b28062c041801a00cc6802f40067d0301b,
  0xc200230371840cc6102f08c09c6102318406c61017020200280370a00bc2802740406d0101740024c020800940dc2502f]
def N4 : Array Nat := #[0x15110514, 0x11310132, 0x11110110, 0x5010d0e, 0x5010504, 0x31003e, 0x310032, 0x110010, 0xd3e, 0xd0e, 0x504, 0x3e, 0x32, 0xe, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe4 : hostSafe H4 := certify H4 N4 D4 0x95310d3e 16 (by decide +kernel) (by decide +kernel)

def H5 : Array Nat := #[1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 31]
def D5 : Array Nat := #[0x14810001190148a806284000444004b1001a740620400045400a09018a40a722f31c89cc72a329c82c094082888bc062900004240029d018ad80522a018820001150188c8062880004440520800046400a0500740403d8d,
  0x1a740628000044400a09004c140010411c28ce209b38445ce2093018820a20b32882bca20a3010410c112b30449cc112301041000119000e540061d01cc40a70b329c2bca70a3030c40ac0af2b028c0b404018ad8c1227,
  0x11c09ce201b38805ce0113018a20820372080bc82027014400c012b30049cc012301440000119000e440061d01cc508703721c0bc87027034c508d02f23409c0b4800188c8c02a3014800001190148a806200000454004b5,
  0x44400a9d00422401e8500c404020800880bc4102710028c4101f08806c4101710024c0008009c0bce101b38405ce0093018a10810372040bc81027018200a00b32802bca00a301820000115000e440061d00242400100,
  0x164400a9d01c830a71b30148a8a71a30188300011521c6dc871af21c69c0628c0004440620c0188c8c91ab32468c0520c000464891b72246bc0520c22c6dcab1b32ac68c0d6200004b40522a018830001150014940628c,
  0x30469c051840004640032100164400a9d0038240618819c4ac6712719c48ce311738c44c000082886cc0522a28868c06188000454821b72086bc821a70186206812b1a049d03117018620a21b32886bc0618800045400321,
  0x2a7400e09004a14031041882cc620af1844ac6112718828c6209f10c24c0518419c2cc670af19c28ce309b38c24c000040188c8c11ab30468c05184000464811b72046bc811a7014610680b31a02bd0309b014610c11ab,
  0x1880bc6012b18809c6012318807c430170106006703719c0bc6702738c06ce3017000000062b63006acc01a7010600001192806cca01af28068c041801a40dc6902f48c06c041803006acc01a301060000119000c9400595,
  0x30801840dc600b31840bc6102718028c6101f08c06c6100b00c40062037]
def N5 : Array Nat := #[0x551514, 0x331312, 0xf0706, 0x7f0016, 0x550014, 0x330012, 0xf0006, 0x1716, 0x1514, 0x1312, 0x1110, 0x706, 0x504, 0x302, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe5 : hostSafe H5 := certify H5 N5 D5 0x807f1716 16 (by decide +kernel) (by decide +kernel)

def H6 : Array Nat := #[1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 21, 22, 27, 31]
def D6 : Array Nat := #[0x18a200010531ca8c001042882bca20ab30449cc1123018a1000109018a2000105001474062b201841000115002a4401935010410a20af2882aca20a328827c0520400042404104000454052080004140061900a8040498d,
  0x18a40062b229c8acc72a329c82c06208000454c722731c81c041042082acc1123029010062b201881000115000a24c1227025020a222b018a4000109018ac806208000454004050024740622e018a10a70af29c2ace608b,
  0x292000012d018ac8c02a3300a7c062000004540520000046400689003e140720831c49cc712331c41c0628431c28ce6093018a4000105000c240010430449cc112302501000109025020001050010740d332034cb80d32a,
  0x980acc102730028c050802040cc8102b20409c050800004440039900227400b890004004702738806ce201738044c062882080cc8202b20809c051002880ac4502728048c06100000454003910018740628002ccd80b312,
  0x32468c0c5200004940622e018a30001110014d40520c00046400889003a7401505009004020800880ac4102710028c4101f08806c4101710024c0008009c0ace101b38405ce00930002000b33602cc49610170102000012d,
  0x1e7400b090186206712719c48ce311738c44c0b41c21c6cc871ab21c69c0628c0004440038902d020821b32086ac821a7018620a21af2886aca21a301862000115000e440940c034cc80d32e034ca80620c2246cc891ab,
  0xc6400529001e7400b09003c14031041882bc620ab18449c620a318827c43093014610670af19c2ac670a338c26ce3093028c306a0af1a828d43093031610c11a730468c051842046cc811a701461000111000c6400529,
  0x1802bc6102b18409c600a318407c2301b18402c031001880cc6202b18809c6012318807c430170106006703319c0ac6702738c06ce3017028c306a0331a809d43017031600c01a730068c041802806bca01a301060000115,
  0x20061033]
def N6 : Array Nat := #[0x551514, 0x331312, 0x8070706, 0x770016, 0x550014, 0x330012, 0x70006, 0x1716, 0x1514, 0x1312, 0x706, 0x504, 0x302, 0x10, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe6 : hostSafe H6 := certify H6 N6 D6 0x88771716 16 (by decide +kernel) (by decide +kernel)

def H7 : Array Nat := #[3, 4, 7, 8, 11, 12, 15, 16, 19, 20, 23, 24, 27, 28, 31]
def D7 : Array Nat := #[0x4840c2aa030a980628041403d05007020e300010101c600001210010c407184020cd80832601c6000933200c2006101f0182000010d01860000105018610001010012940062100c20000119002454012110096b403409,
  0xa412438f490e0c094000004740030502506806204404e5d0138f39020c0808000047408380000414004a50208d80418022407c89007024e100010101c2000012500108400ea9018a010500f41401c0838400040407080,
  0x4040b49601c2000012502c8a80b2220002002b00f28028c2b01f014600001050146100010102caa80b2a600c20000115001a4400c190188112408f49020c0938c000414071840004940a2360288580520449023d24083,
  0x4040030502d0680618840ce5d0338738860c0818000047408380000434004ad0204d8081260082004b01f12c03c0b38c000404071800004b400421003c4401ab101c2000b32a02cc980b3220106008901f22401c04184,
  0x304d80c1260304580b20012c27c4b08f0104004b01f12c03c093880004040030502c8a80b2220106008919f22461c072000004340912201c610001250012b4041360104580b40012c27c4b08f0144004b01f12c03c05188,
  0x208012c27c4b08f02ce300010501c6100012d]
def N7 : Array Nat := #[0x11111110, 0x9090908, 0x1010100, 0x990098, 0x110010, 0x90008, 0x10000, 0x9998, 0x1110, 0x908, 0x100, 0x98, 0x10, 0x8, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe7 : hostSafe H7 := certify H7 N7 D7 0x99999998 16 (by decide +kernel) (by decide +kernel)

def H8 : Array Nat := #[3, 4, 7, 8, 11, 16, 19, 32, 36, 40, 47, 48, 52, 56, 63]
def D8 : Array Nat := #[0x18a400010d31c88c0020c2146cc851af30ca9cc32a301883000115018a400010d00147406236018a3000111002a2401929014620851b32146bc851a321467c0418800045405188000444052080004340061900a81404b01,
  0x188200623621c4bcc722321c45c06288000444c712731c43c041881944bcc32a302d0300623601862000111000a54c31270250508512f018820001150188d8062880004440040d00247406132018830871b321c6bce6197,
  0x424002a90188d8c122330487c0610400044404104000464008150044340728831ca9cc72a331ca3c0620c31c68ce618b0188200010d000c540518830ca9cc32a3020c20001150250500010d0010740a336028cc80a32e,
  0x10610430b710c2bc430a701061000109000e640089d002e540028429c29ce509b39424ce128b018a40450b71142bc450a7014810850af29029ca1223018a1000111000e240061d0184100a332028cb80b4840184c806204,
  0x184c806200000424005290104000011900225400e9d00543402405014610650af28c29ca11a328c27c6509b28c24ca118b000610670af38c26ce309338462c00184030ca80c30a60c24c031040004c4660af30c29cc11a3,
  0x29c09ca7023380a4ce028b0310704703711c0bc4702701880000109000e540c4141140dc4502f11409c062802140cc8502f21408c06280000444003890250000a336028cc80a32e018400490371240bcc902303568000125,
  0x2c5400f0d014600650331940bca302728c08ca301f28062c0418019c0cc6702f19c08ce019b38062c0b3001ac0cc6b02358062c0d60c30c09cc30230106004303710c09c04180000424003190014b40079d002c5406280,
  0x18408c6101f18026c61017014200250370940bca102728408ca101f28024c0208009c0dc2702f09c09ce009b38024c0b3000ac0dc2b02758024c0d60430409cc10230082008103320408c02080000444003190014b40079d,
  0x208008c0dc610331840bc23027]
def N8 : Array Nat := #[0x111011100010110, 0x101010100090908, 0x101010100010100, 0x11001100090098, 0x11001100010010, 0x811100000998, 0x11100000110, 0x90998, 0x90908, 0x90098, 0x10000, 0x998, 0x908, 0x98, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe8 : hostSafe H8 := certify H8 N8 D8 0x8111811100090998 16 (by decide +kernel) (by decide +kernel)

def H9 : Array Nat := #[3, 4, 7, 8, 11, 16, 20, 23, 32, 40, 43, 48, 52, 56, 63]
def D9 : Array Nat := #[0x1cc4000109000c540920800048407236025020001110020a406288328a9cca2a3328a4c05208000464062080004540a132018a20a8127408a4c062080004540920800048400429018a40001090028740180d00c41405981,
  0x10620881b32206bc8819b018620861b32186bc041880004640032101862000111001a7401015018a20ca2a7328a8cca2930250500011902506000115028ed80a3b2028eb8072903a0a9d0521b410a2c082082204bce8127,
  0x40ca4d0518b01ca20851b32146bc8519b000a312519f49466d2518b02862000125000e4400621018620e332738cc8c083880004640a3b6028ec80a3ae01c8310719b41c62c0720c49c66d2718b01062000125000c8400529,
  0x4540a3b6028ec80a3ae028410aa0a72a824c0610432829cca09301041000119000c540051d010410450b71142bc450a7024810490b71242bc041040004940031502481000109001aa4010210064340028c41467d0519b,
  0x10c2bc430a701c610811b32046bc071840004440030900166400821002e54082842a02aca80a741424d0128b029040480b71202bc480a701cc10c80ab32029cc809301c81000119000e2400615028410aa0a72a824c09304,
  0x18400001110304a8061000004c4062000004240051d0026b400ea100525401d8d00b214001841942bca30ab28c29ca30a328c24ca118b000610680af40467d0119b40c24d0118b00c410c30ab30c29cc3093010610430b7,
  0xe4400621031060480371200bc4802701c800880332200bc8801b01cc0000111000e240c59812c0dc4b02701c8008b03322c06c0730000044400309024c000a3b6028ec80920001c8d809100000444002a90104008c01b,
  0x40062c0b3801ac0cc6b01b58062c0418048067d2019b48062c0d60c1b006c0d30c0004c4002a50014b4007a1002c54072802a009d0501b400a4d0028b035250850332140bc8501b028400450371140bc4502702920000109,
  0x2802aca102728024c0b5000ac0dc2b02758024c020803002acc00a730024c0d6040b409c0c4840004d4002990014b400795002c8400f0d014600650331940bca302728c08c6501b28062c041801a00cc6802f40067d0301b,
  0xc200230371840cc6102f08c09c6102318406c61017020200280370a00bc2802740406d0101740024c020800940dc2502f]
def N9 : Array Nat := #[0x111010100110110, 0x101090100010908, 0x101010100010100, 0x11000100910098, 0x11000100110010, 0x90100000998, 0x90100000908, 0x10100000100, 0x910998, 0x910098, 0x110010, 0x998, 0x908, 0x98, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe9 : hostSafe H9 := certify H9 N9 D9 0x8111090100910998 16 (by decide +kernel) (by decide +kernel)

def H10 : Array Nat := #[3, 12, 15, 16, 19, 28, 31, 32, 35, 44, 47, 48, 51, 60, 63]
def D10 : Array Nat := #[0x4840c2aa030a980628041403d05007020e300010101c600001210010c407184020cd80832601c6000933200c2006101f0182000010d01860000105018610001010012940062100c20000119002454012110096b403409,
  0xa412438f490e0c094000004740030502506806204404e5d0138f39020c0808000047408380000414004a50208d80418022407c89007024e100010101c2000012500108400ea9018a010500f41401c0838400040407080,
  0x4040b49601c2000012502c8a80b2220002002b00f28028c2b01f014600001050146100010102caa80b2a600c20000115001a4400c190188112408f49020c0938c000414071840004940a2360288580520449023d24083,
  0x4040030502d0680618840ce5d0338738860c0818000047408380000434004ad0204d8081260082004b01f12c03c0b38c000404071800004b400421003c4401ab101c2000b32a02cc980b3220106008901f22401c04184,
  0x304d80c1260304580b20012c27c4b08f0104004b01f12c03c093880004040030502c8a80b2220106008919f22461c072000004340912201c610001250012b4041360104580b40012c27c4b08f0144004b01f12c03c05188,
  0x208012c27c4b08f02ce300010501c6100012d]
def N10 : Array Nat := #[0x1001100110011000, 0x9000900090008, 0x1000100010000, 0x900900009008, 0x100100001000, 0x900000008, 0x100000000, 0x90099008, 0x10011000, 0x90008, 0x10000, 0x9008, 0x1000, 0x8, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe10 : hostSafe H10 := certify H10 N10 D10 0x9009900990099008 16 (by decide +kernel) (by decide +kernel)

def H11 : Array Nat := #[3, 12, 15, 48, 51, 60, 63, 64, 67, 76, 79, 112, 115, 124, 127]
def D11 : Array Nat := #[0x4840c2aa030a980628041403d05007020e300010101c600001210010c407184020cd80832601c6000933200c2006101f0182000010d01860000105018610001010012940062100c20000119002454012110096b403409,
  0xa412438f490e0c094000004740030502506806204404e5d0138f39020c0808000047408380000414004a50208d80418022407c89007024e100010101c2000012500108400ea9018a010500f41401c0838400040407080,
  0x4040b49601c2000012502c8a80b2220002002b00f28028c2b01f014600001050146100010102caa80b2a600c20000115001a4400c190188112408f49020c0938c000414071840004940a2360288580520449023d24083,
  0x4040030502d0680618840ce5d0338738860c0818000047408380000434004ad0204d8081260082004b01f12c03c0b38c000404071800004b400421003c4401ab101c2000b32a02cc980b3220106008901f22401c04184,
  0x304d80c1260304580b20012c27c4b08f0104004b01f12c03c093880004040030502c8a80b2220106008919f22461c072000004340912201c610001250012b4041360104580b40012c27c4b08f0144004b01f12c03c05188,
  0x208012c27c4b08f02ce300010501c6100012d]
def N11 : Array Nat := #[0x10010000000010011001000000001000, 0x90000000000090009000000000008, 0x10000000000010001000000000000, 0x90090000000000009008, 0x10010000000000001000, 0x90000000000000008, 0x10000000000000000, 0x9009000000009008, 0x1001000000001000, 0x9000000000008, 0x1000000000000, 0x9008, 0x1000, 0x8, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe11 : hostSafe H11 := certify H11 N11 D11 0x90090000000090099009000000009008 16 (by decide +kernel) (by decide +kernel)

def H12 : Array Nat := #[3, 12, 15, 48, 51, 60, 63, 192, 195, 204, 207, 240, 243, 252, 255]
def D12 : Array Nat := #[0x4840c2aa030a980628041403d05007020e300010101c600001210010c407184020cd80832601c6000933200c2006101f0182000010d01860000105018610001010012940062100c20000119002454012110096b403409,
  0xa412438f490e0c094000004740030502506806204404e5d0138f39020c0808000047408380000414004a50208d80418022407c89007024e100010101c2000012500108400ea9018a010500f41401c0838400040407080,
  0x4040b49601c2000012502c8a80b2220002002b00f28028c2b01f014600001050146100010102caa80b2a600c20000115001a4400c190188112408f49020c0938c000414071840004940a2360288580520449023d24083,
  0x4040030502d0680618840ce5d0338738860c0818000047408380000434004ad0204d8081260082004b01f12c03c0b38c000404071800004b400421003c4401ab101c2000b32a02cc980b3220106008901f22401c04184,
  0x304d80c1260304580b20012c27c4b08f0104004b01f12c03c093880004040030502c8a80b2220106008919f22461c072000004340912201c610001250012b4041360104580b40012c27c4b08f0144004b01f12c03c05188,
  0x208012c27c4b08f02ce300010501c6100012d]
def N12 : Array Nat := #[0x1001000000001001000000000000000000000000000000001001000000001000, 0x9000000000009000000000000000000000000000000000009000000000008, 0x1000000000001000000000000000000000000000000000001000000000000, 0x9009000000000000000000000000000000000000000000009008, 0x1001000000000000000000000000000000000000000000001000, 0x9000000000000000000000000000000000000000000000008, 0x1000000000000000000000000000000000000000000000000, 0x9009000000009008, 0x1001000000001000, 0x9000000000008, 0x1000000000000, 0x9008, 0x1000, 0x8, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe12 : hostSafe H12 := certify H12 N12 D12 0x9009000000009009000000000000000000000000000000009009000000009008 16 (by decide +kernel) (by decide +kernel)

def H13 : Array Nat := #[7, 8, 15, 16, 23, 24, 31, 32, 39, 40, 47, 48, 55, 56, 63]
def D13 : Array Nat := #[0x4840c2aa030a980628041403d05007020e300010101c600001210010c407184020cd80832601c6000933200c2006101f0182000010d01860000105018610001010012940062100c20000119002454012110096b403409,
  0xa412438f490e0c094000004740030502506806204404e5d0138f39020c0808000047408380000414004a50208d80418022407c89007024e100010101c2000012500108400ea9018a010500f41401c0838400040407080,
  0x4040b49601c2000012502c8a80b2220002002b00f28028c2b01f014600001050146100010102caa80b2a600c20000115001a4400c190188112408f49020c0938c000414071840004940a2360288580520449023d24083,
  0x4040030502d0680618840ce5d0338738860c0818000047408380000434004ad0204d8081260082004b01f12c03c0b38c000404071800004b400421003c4401ab101c2000b32a02cc980b3220106008901f22401c04184,
  0x304d80c1260304580b20012c27c4b08f0104004b01f12c03c093880004040030502c8a80b2220106008919f22461c072000004340912201c610001250012b4041360104580b40012c27c4b08f0144004b01f12c03c05188,
  0x208012c27c4b08f02ce300010501c6100012d]
def N13 : Array Nat := #[0x101010101010100, 0x81008100810080, 0x1000100010000, 0x818100008180, 0x10100000100, 0x8100000080, 0x100000000, 0x81818180, 0x1010100, 0x810080, 0x10000, 0x8180, 0x100, 0x80, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe13 : hostSafe H13 := certify H13 N13 D13 0x8181818181818180 16 (by decide +kernel) (by decide +kernel)

def H14 : Array Nat := #[7, 24, 31, 32, 39, 56, 63, 64, 71, 88, 95, 96, 103, 120, 127]
def D14 : Array Nat := #[0x4840c2aa030a980628041403d05007020e300010101c600001210010c407184020cd80832601c6000933200c2006101f0182000010d01860000105018610001010012940062100c20000119002454012110096b403409,
  0xa412438f490e0c094000004740030502506806204404e5d0138f39020c0808000047408380000414004a50208d80418022407c89007024e100010101c2000012500108400ea9018a010500f41401c0838400040407080,
  0x4040b49601c2000012502c8a80b2220002002b00f28028c2b01f014600001050146100010102caa80b2a600c20000115001a4400c190188112408f49020c0938c000414071840004940a2360288580520449023d24083,
  0x4040030502d0680618840ce5d0338738860c0818000047408380000434004ad0204d8081260082004b01f12c03c0b38c000404071800004b400421003c4401ab101c2000b32a02cc980b3220106008901f22401c04184,
  0x304d80c1260304580b20012c27c4b08f0104004b01f12c03c093880004040030502c8a80b2220106008919f22461c072000004340912201c610001250012b4041360104580b40012c27c4b08f0144004b01f12c03c05188,
  0x208012c27c4b08f02ce300010501c6100012d]
def N14 : Array Nat := #[0x1000001010000010100000101000000, 0x81000000810000008100000080, 0x1000000010000000100000000, 0x810000810000000081000080, 0x10000010000000001000000, 0x810000000000000080, 0x10000000000000000, 0x8100008181000080, 0x100000101000000, 0x8100000080, 0x100000000, 0x81000080, 0x1000000, 0x80, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe14 : hostSafe H14 := certify H14 N14 D14 0x81000081810000818100008181000080 16 (by decide +kernel) (by decide +kernel)

def H15 : Array Nat := #[15, 16, 31, 32, 47, 48, 63, 64, 79, 80, 95, 96, 111, 112, 127]
def D15 : Array Nat := #[0x4840c2aa030a980628041403d05007020e300010101c600001210010c407184020cd80832601c6000933200c2006101f0182000010d01860000105018610001010012940062100c20000119002454012110096b403409,
  0xa412438f490e0c094000004740030502506806204404e5d0138f39020c0808000047408380000414004a50208d80418022407c89007024e100010101c2000012500108400ea9018a010500f41401c0838400040407080,
  0x4040b49601c2000012502c8a80b2220002002b00f28028c2b01f014600001050146100010102caa80b2a600c20000115001a4400c190188112408f49020c0938c000414071840004940a2360288580520449023d24083,
  0x4040030502d0680618840ce5d0338738860c0818000047408380000434004ad0204d8081260082004b01f12c03c0b38c000404071800004b400421003c4401ab101c2000b32a02cc980b3220106008901f22401c04184,
  0x304d80c1260304580b20012c27c4b08f0104004b01f12c03c093880004040030502c8a80b2220106008919f22461c072000004340912201c610001250012b4041360104580b40012c27c4b08f0144004b01f12c03c05188,
  0x208012c27c4b08f02ce300010501c6100012d]
def N15 : Array Nat := #[0x10001000100010001000100010000, 0x8001000080010000800100008000, 0x1000000010000000100000000, 0x800180010000000080018000, 0x100010000000000010000, 0x80010000000000008000, 0x10000000000000000, 0x8001800180018000, 0x1000100010000, 0x800100008000, 0x100000000, 0x80018000, 0x10000, 0x8000, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe15 : hostSafe H15 := certify H15 N15 D15 0x80018001800180018001800180018000 16 (by decide +kernel) (by decide +kernel)

def H16 : Array Nat := #[15, 48, 63, 64, 79, 112, 127, 128, 143, 176, 191, 192, 207, 240, 255]
def D16 : Array Nat := #[0x4840c2aa030a980628041403d05007020e300010101c600001210010c407184020cd80832601c6000933200c2006101f0182000010d01860000105018610001010012940062100c20000119002454012110096b403409,
  0xa412438f490e0c094000004740030502506806204404e5d0138f39020c0808000047408380000414004a50208d80418022407c89007024e100010101c2000012500108400ea9018a010500f41401c0838400040407080,
  0x4040b49601c2000012502c8a80b2220002002b00f28028c2b01f014600001050146100010102caa80b2a600c20000115001a4400c190188112408f49020c0938c000414071840004940a2360288580520449023d24083,
  0x4040030502d0680618840ce5d0338738860c0818000047408380000434004ad0204d8081260082004b01f12c03c0b38c000404071800004b400421003c4401ab101c2000b32a02cc980b3220106008901f22401c04184,
  0x304d80c1260304580b20012c27c4b08f0104004b01f12c03c093880004040030502c8a80b2220106008919f22461c072000004340912201c610001250012b4041360104580b40012c27c4b08f0144004b01f12c03c05188,
  0x208012c27c4b08f02ce300010501c6100012d]
def N16 : Array Nat := #[0x1000000000001000100000000000100010000000000010001000000000000, 0x8001000000000000800100000000000080010000000000008000, 0x1000000000000000100000000000000010000000000000000, 0x800100000000800100000000000000008001000000008000, 0x100000000000100000000000000000001000000000000, 0x800100000000000000000000000000008000, 0x100000000000000000000000000000000, 0x80010000000080018001000000008000, 0x10000000000010001000000000000, 0x80010000000000008000, 0x10000000000000000, 0x8001000000008000, 0x1000000000000, 0x8000, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe16 : hostSafe H16 := certify H16 N16 D16 0x8001000000008001800100000000800180010000000080018001000000008000 16 (by decide +kernel) (by decide +kernel)

def H17 : Array Nat := #[1, 2, 3, 4, 8, 9, 12, 13, 16, 18, 20, 22, 24, 26, 28, 31]
def D17 : Array Nat := #[0x10440b33602ccc80030849905d2641349903c0818800049409188000484004ad003ca4001881904cca322f28c89c05188000444a312b28c48c052080004340513601483000109010620001150020640231d00ee1406201,
  0x22848c0620c000424003950000214219730869cc21a3018a3000109018a200010d0012440a336028cc80620c59105cc822732082c0620c59125cc920b02c62000125000c840628c32069cc818b024a2000121018a200010d,
  0x51065d4418b024a20001110292200010d0010840a3b6028ec8071881a04cce81a740c46d0219740c44c09408000434091880004840713602503000109001ca40122d014820aa22f2a889caa2232a883c0020822843cc2227,
  0x38468c07284000434051840004740041900284401409000a40ab22b2ac89cab2232ac83c09410000454094140004440b3b602cec80b38a000e212741b49d05d2741349d03c0818850905d4241302903000109000c940920c,
  0x10a122f2848aca122728488ca120f000810880ab41027d0409b41023c0020449027d2409b49023c04184000494003a1001a540030441827d0609741823c0030449827d2609749823c05184000494003a1014610e11a7,
  0x10c28c4309b10c24c072901102ec440b31102ac440a311026c073141182ec460b31182ac460a3028e504a0bb1282cc4a0a301c410480bb1202cd070970244100012101c4d80712e0144100011d0016a400819002c4400e8d,
  0x4440031d00146400a29003e840000048107d2041b48105d204130208008802f2200ad0401b020a0000111000e940730058145d605130292000012d02d2000012900108400a890080340320501ca30430bb10c2cc430ab,
  0x4544803b1200cc4802b12006c48013014400051362a80bcaa02701c400001151280ec4a03312806c4a0130184000d32e0344780d11602d260001351180ec4603311804c0910001c4d80712e0148004403b1100cc05100,
  0x600640371900cc8302f20c0ac8302720062c031000144d8a302f28c09c071800004544303b10c0cc4302b10c06c071801a40dc6903348c06d201970146000012500102400991003684081000144d8a802f2a009c07100,
  0x58025c020800004b42603b0980cc2602b30409c0a3800a80ec2a03350025c020802840bca1027008200e10270082000011d000a54004a9001c6400c210040440148d01c600680371a00cc6802740c06d0019740c04d0018b,
  0x208008c0ec610371840cc2302b18409c6102308c06c6009718404c020800900ec240332040bc8102b20409c8102309006c020800a00ec280330a00ad0009f40406d000970082000b336]
def N17 : Array Nat := #[0x15551114, 0x11113312, 0x11111110, 0x505030e, 0x55001e, 0x550014, 0x5000e, 0x50004, 0x331e, 0x3312, 0x30e, 0x302, 0x1e, 0x12, 0xe, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe17 : hostSafe H17 := certify H17 N17 D17 0x9555331e 17 (by decide +kernel) (by decide +kernel)

def H18 : Array Nat := #[1, 2, 3, 4, 8, 9, 12, 13, 16, 18, 20, 22, 24, 27, 28, 31]
def D18 : Array Nat := #[0x24a200012101c620001150010440a3b6028ec80038849d05d2741349d03c0818800049409188000484004a9003cb40018828c8bca322b28c89ca32230148200010d010620001150146200011100187401b9900de1405d01,
  0x49903c08188000494091880004840052d0042a4002902ac8acab2272ac88cab20f01c8300011501ca300011102ced80b3b202ce280720c51105d4440b3a089c0720c51065d4418b0292200010d000c840728c51502ce82a7,
  0x4940928800048400491028cd80a33202c620c222730888c0518830869cc21a3018a200010d000c440b11e0000612641f49905d2641349903c0b40c0004940b48c0004840050902ccd80b332000c212641f49905d26413,
  0x49827d2609749823c05184000494003a1014610e11a738468c072840004340518400047400419002844014090208314441732089d4440b014820aa22f2a889caa20f02482000115000e840030849907d2641749903c08288,
  0x1c4b805104000474002a10012a40071900284400d8d000010a122f2848aca122728488ca120f000810880ab41027d0409b41023c0020449027d2409b49023c04184000494003a1001a540030441827d0609741823c00304,
  0x246000012d0010a400a210050240258501ca30430bb10c2cc430ab10c28c4309b10c24c072901102ec440b31102ac440a311026c073141182ec460b31182ac460a3028e504a0bb1282cc4a0a3020e50480bb1202cc09104,
  0x48105d2041348103c082002200bc8802b41006d0400f020a00a802f2a00aca800f02060000115000e44006a50148008a02f22809c8a00f000a00aa02f2a809caa00f02460000115000e440918058065d6019302d2000010d,
  0x10c06c4301302d2804803b1200cc4802b12006c4801302d4904a03b1280cc4a01b12804c0b4981180ec4603311804c0b4901100ec440330144000b11e0244000012d000a4400499001ca400a210036340000048107d2041b,
  0xa00cc2802b40027d0101b40025c0b3040980ec260330980acc1027028e002a03b0a80cd40097008200a102f28409c0208038409c02080000474002950012a40071900288400e11004a340b48c10c0ec4303310c0ac43023,
  0x308008c0ec6103308c0ac6102718408c2301b18025c610130082002403b0900cc8102f2040ac8102720408c2401b0082002803b]
def N18 : Array Nat := #[0x11551114, 0x11113312, 0x11111110, 0x905030e, 0x55001e, 0x550014, 0x5000e, 0x50004, 0x331e, 0x3312, 0x30e, 0x302, 0x1e, 0x10, 0xe, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe18 : hostSafe H18 := certify H18 N18 D18 0x9955331e 17 (by decide +kernel) (by decide +kernel)

def H19 : Array Nat := #[3, 4, 7, 8, 11, 15, 16, 20, 32, 35, 40, 43, 48, 51, 56, 63]
def D19 : Array Nat := #[0x10040e2360388980039061103d8440b61100c0838c0004c40c38c000484004b9003ca40710010c0ec6703338069c07188000404e312b38c48c071000004340713600c4000011d01c600001090020440231500ee6406205,
  0x3a808c041800004740038901c830871b351c62c871a30106200011d01c8200010d0012040a2360288980418070102c8803322007c0418070182c8c01f01c40000131000c84041882206cc8819f030e200012101c8200010d,
  0x20e2000101000ec40710019c0cce302b030e20001010314700010d001084072ba0000518541361503d8540b61500c081000004c40c1000004840051d0040940163501c4004a03b1280cc4a02312803c0720021c0ccea00f,
  0x29848c0628c00042406188000454004110028040141d0310300d2ba034aa80d29e000e518541361503d8540b61500c0838c0004c40c38c000484092ba024aa80039461504d8540f61502d85403020e00e802b400e4d0700f,
  0x184004603b1180cc4602b11808c4600f000c00c802b400c5d0031341803c00300600c5d80313600c3c061800004c4003a1001a2400310410c5d0430f410c2c00310610c5d8430f610c2c061880004c4003a1018620a6133,
  0x38cc8ce331338cc0c05100380cbce032b380c9ce0323380c4c05208390cbce432b390c9ce4323028a20ea32f3a8c9cea32301cc50e832f3a0c9d0530b030e600012101cae8072b601cc20001150016a400811002c0400e8d,
  0x4040031500144400a29003e840000460505d8141360502d814030202002803b0a00ad0009302041000101000ec40520470542dc1503031410001390398100012900108400a9d00803403219014620e332f38ccace3327,
  0x424e80af3a02ace80a73a024ce808301c4104a0bb01c4d84a0b301ca10001093a82bcea0a73a824cea0830008100d23a034e580d38a039840001353902bce40a739020c0c38401cae8072b6008200e00af38029c07104,
  0x82002303b1802dc6103308c0ac600a718407c0310410c2ec0713610c2cc05184000424e30af38c2ace30a738c24c051841b02dc6c0a760c24d8118b00c4100013100107400981003684081041202ec071361202cc07284,
  0x704c2c062040004e4860b33102bcc40ab31029c0a2843282bcca0a7504c2c073041182ec460b301cc10a60b301cc1000115000a24004a9001c4400c210040040148d014610680b71a02cc680a740467d0309340462d03083,
  0x51841982dc660b330c2bcc30ab30c29cc30a330c24cc118b30c20c060800980ec260333002bcc102b30029cc102330024c073043202bcc80ab32029d0131741824d0130b0148100e236]
def N19 : Array Nat := #[0x101010100110110, 0x109090900010908, 0x101010100010100, 0x9000900110098, 0x1000100110010, 0x1000100010000, 0x90900008998, 0x90900000908, 0x118998, 0x110110, 0x110098, 0x110010, 0x8998, 0x110, 0x98, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe19 : hostSafe H19 := certify H19 N19 D19 0x8109090900118998 17 (by decide +kernel) (by decide +kernel)

def H20 : Array Nat := #[3, 4, 7, 8, 11, 15, 16, 20, 32, 35, 40, 43, 48, 55, 56, 63]
def D20 : Array Nat := #[0x30e200012101ca30001090010040a2b6028a980039461503d8540b61500c0838c0004c40c38c000484004a9003ce40718010c0ec4303310c0ac4302301c4000010d01c6000010901c6200010100185401b9100de6405d05,
  0x61100c0838c0004c40c38c000484005390042a4001001380cc4e02b13808c4e00f0146000010901462000101038ad80e2a6038a78051802a00cd4041f50102c0518050067d4018b0314700010d000c84051882a04cd4241f,
  0x4c40c388000484004810288d80a22601c4008703321c08c0718821c6cc871a301c8200010d000c040e3960000418441761103d8440b61100c081000004c40c1000004840051d0388d80e226000e418441761103d8440b,
  0x610c5d8430f610c2c061880004c4003a1018620a613329848c0628c00042406188000454004110028040141d0206008803350102d4041f01c4004a03b1280cc4a00f030e0000109000e840039061105d8440f61102c08388,
  0x1cae807308000454002a10012a40071100280400d8d0184004603b1180cc4602b11808c4600f000c00c802b400c5d0031341803c00300600c5d80313600c3c061800004c4003a1001a2400310410c5d0430f410c2c00310,
  0x30610001390010a400a2100507402599014620e332f38ccace332738cc8ce331338cc0c05100380cbce032b380c9ce0323380c4c05208390cbce432b390c9ce4323028a20ea32f3a8c9cea323020a20e832f3a0c9c0c398,
  0x60503d8140b60500c080800a00ec2802b40024d0100f020410480bb1202ac4808f02061000109000e04006b10082002a03b0a80cc2a00f0004104a0bb1282cc4a08f03061000109000e040c18470462dc11830398100010d,
  0x38c24ce3083039880e80af3a02ace80a73a024ce80830398a0ea0af3a829cea0933a820c0e6103902bce40a739020c0e6003802bce00a701c4100e396030e1000139000a0400491001ca400a210036340000460505d81413,
  0x3202acc80a7404c5d06093404c2c0e3102182ccc40af3102acc40a7028a10ca0af32829d4130b01cc10460bb1182cc073042982cc07304000454002890012a40071100288400e01004a340e60c38c2bce30ab38c29ce30a3,
  0x51841982ccc30af30c2acc30a730c28cc309330462cc30830182002603b0980ccc00af3040acc00a730408cc009301cc10c80af]
def N20 : Array Nat := #[0x101010100110110, 0x101090900010908, 0x101010100010100, 0x81000900110098, 0x1000100110010, 0x1000100010000, 0x90900008998, 0x90900000908, 0x118998, 0x110110, 0x110098, 0x110010, 0x8998, 0x100, 0x98, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe20 : hostSafe H20 := certify H20 N20 D20 0x8181090900118998 17 (by decide +kernel) (by decide +kernel)

def H21 : Array Nat := #[3, 4, 7, 8, 16, 19, 24, 27, 32, 36, 40, 44, 48, 55, 56, 63]
def D21 : Array Nat := #[0x24a200012101c620001150010440a3b6028ec80038849d05d2741349d03c0818800049409188000484004a9003cb40018828c8bca322b28c89ca32230148200010d010620001150146200011100187401b9900de1405d01,
  0x49903c08188000494091880004840052d0042a4002902ac8acab2272ac88cab20f01c8300011501ca300011102ced80b3b202ce280720c51105d4440b3a089c0720c51065d4418b0292200010d000c840728c51502ce82a7,
  0x4940928800048400491028cd80a33202c620c222730888c0518830869cc21a3018a200010d000c440b11e0000612641f49905d2641349903c0b40c0004940b48c0004840050902ccd80b332000c212641f49905d26413,
  0x49827d2609749823c05184000494003a1014610e11a738468c072840004340518400047400419002844014090208314441732089d4440b014820aa22f2a889caa20f02482000115000e840030849907d2641749903c08288,
  0x1c4b805104000474002a10012a40071900284400d8d000010a122f2848aca122728488ca120f000810880ab41027d0409b41023c0020449027d2409b49023c04184000494003a1001a540030441827d0609741823c00304,
  0x246000012d0010a400a210050240258501ca30430bb10c2cc430ab10c28c4309b10c24c072901102ec440b31102ac440a311026c073141182ec460b31182ac460a3028e504a0bb1282cc4a0a3020e50480bb1202cc09104,
  0x48105d2041348103c082002200bc8802b41006d0400f020a00a802f2a00aca800f02060000115000e44006a50148008a02f22809c8a00f000a00aa02f2a809caa00f02460000115000e440918058065d6019302d2000010d,
  0x10c06c4301302d2804803b1200cc4802b12006c4801302d4904a03b1280cc4a01b12804c0b4981180ec4603311804c0b4901100ec440330144000b11e0244000012d000a4400499001ca400a210036340000048107d2041b,
  0xa00cc2802b40027d0101b40025c0b3040980ec260330980acc1027028e002a03b0a80cd40097008200a102f28409c0208038409c02080000474002950012a40071900288400e11004a340b48c10c0ec4303310c0ac43023,
  0x308008c0ec6103308c0ac6102718408c2301b18025c610130082002403b0900cc8102f2040ac8102720408c2401b0082002803b]
def N21 : Array Nat := #[0x101111101010110, 0x101010109090108, 0x101010101010100, 0x81001100090098, 0x111100000198, 0x111100000110, 0x1100000098, 0x1100000010, 0x9090198, 0x9090108, 0x90098, 0x90008, 0x198, 0x100, 0x98, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe21 : hostSafe H21 := certify H21 N21 D21 0x8181111109090198 17 (by decide +kernel) (by decide +kernel)

def H22 : Array Nat := #[3, 12, 15, 16, 19, 32, 44, 47, 64, 76, 80, 95, 96, 108, 112, 127]
def D22 : Array Nat := #[0x288200012101ca40001090010140c3ae030e980039051d05d4740b51d01c082900004a40a290000484004b1003ce4052041142ec450b31142ac450a301041000115014810001090148200010500187401b9900de3405d01,
  0x51901c082900004a40a290000484005390042c4001041382cc4e0ab13828c4e09701ca100010901ca2000105038eb80e3a6038e480728460504d8140b3a02ac07284604a4d8128b03144000115000c840728860904ce812b,
  0x4a40a20800048400485030cb80c326010410c40ab31028c00208310aacc42a301882000115000c140e21e0000614641f51905d4640b51901c081040004a40a10400048400511038cb80e326000c414641f51905d4640b,
  0x51867d4619751862c051880004a4003a1014620e312b38c48c0728c000424051880004740041900281401411020a118140b3202ad814130104104c0bb1302ac4c09702881000109000e840031051907d4641751902c08208,
  0x1c8e804188000474002a10012c40071900281400d9500c410430bb10c2cc430ab10c28c43097000610680b340467d0119b40c25c0018450467d4119b50465c051840004a4003a1001a240030c41867d0619741862c0030c,
  0x28a00001390010c400a210050440258d01ca20851b72146cc851a721468c8519b21461c071042046dc811b320469c811a320466c073082186dc861b321869c861a3030e208c1b723069c8c1a3020e20881b722069c0a20c,
  0x50105d4040b50101c080800a00ec2803340406d010170204004803b1200cc48017020a0000109000e14006a90082002c03b0b00ac2c0170004004c03b1300ac4c017028a0000109000e140a280700a2dc028703940000115,
  0x21406c85007039480880372200cc8802722006c880070398a08c03723009c8c01b23001c0e5182180dc8602721801c0e5042040dc810270104000e21e02880000139000a1400499001cc400a210036540000050107d4041b,
  0x1a00cc6802740067d0301b40062c0e30c1980dc6603330c0ac66027030e006c0371b009d8018b0106004303b10c0ac0418038c0ac04180000474002890012c40071900288400e05004a540e5142140dc8503321409c85023,
  0x51801940dc6503328c0aca302728c08c6501b28062ca300700c2002303b1840dc6103308c0ac6102718408c6101b01060068037]
def N22 : Array Nat := #[0x11001000110010000100100011000, 0x10001000100010000000100090008, 0x10001000100010000000100010000, 0x1001000010010000900100009008, 0x1001000010010000100100001000, 0x800110010000000000099008, 0x100010000000000090008, 0x100010000000000010000, 0x900100099008, 0x100090008, 0x900100009008, 0x100000000, 0x99008, 0x90008, 0x9008, 0x0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem safe22 : hostSafe H22 := certify H22 N22 D22 0x80011001800110010000900100099008 17 (by decide +kernel) (by decide +kernel)

def H23 : Array Nat := #[0x1, 0x2, 0x3, 0x4, 0x5, 0x7, 0x8, 0xa, 0xb, 0x10, 0x14, 0x15, 0x20, 0x28, 0x2a, 0x30, 0x34, 0x38, 0x3f]
def N23 : Array Nat := #[0x111050100110514, 0x111010100310132, 0x111010100110110, 0x101050100010d0e, 0x101050100010504, 0x101010100010100, 0x110001003100be, 0x11000100310032, 0x11000100110010, 0x50100000dbe, 0x50100000d0e, 0x50100000504, 0x310dbe, 0x3100be, 0x310032, 0xdbe, 0xd0e, 0xbe, 0x0]
private theorem bk23 : bookOK H23 N23 0x8111050100310dbe = true := by decide +kernel
private theorem adj23 : validRows H23 N23 := rows_of_book _ _ _ bk23
def prog23k4 : Array Nat := #[0x2b491cad23f03d070af2470450700013d000ad40a394428f0d0a3bf020e5000129028e50001210290500011d001444009b9020e414723b51c8dc0a41c000444083900004a40a41000047400515005ab402b890164c4080a5, 0x5b887c0b5145b94dd6e51f02ce5000129000c440b3946aceadab393034a400011d01ca40001350010e400921000a40ad2472b48fdc46ab03ca41c43ab03d440af247028a400013d000a740043503d45000111038b080d41c, 0x44400415041a7000139001b1400da90072f408390428f0d0a3bf59d4ed6753703d0716723b59c8dc10594440efc0f594000504002910012a40b41472daadcb69303dc800013503da80001390010740b446038a416e237, 0x4b400311028a21ca3af728e4c1151c0004e4117280004740043500270410588889a5e22693045c216e21f0460b000111044e2000139045688118100004b4005350356400e2c20390216e2375b887c102080004b410588, 0x3bc50cef12b038a200011d2bc51caf13702ce20ef1433bc4ac0b50800047400315001c8400b11001421ca6af729a4c0e2080004d410716045a200013980948e0251f0350208d1475348ed4d21f045aa16d53b5b547c0a288, 0x2ce5000129000a840c4145b14ed6c53702d050001290290500012d001074009110054240f5903bc50cef12b03dc210f14343c4ac0f7080004840031d23c51c8f13703d620af1472bc4dc0f5880004550f14343c4ac0f588, 0x1ca400cb5003ef4106102b091cac237020e40001153b08fd843af610eac004106918bda462b69185c0e6202b091cac23f001041c462f7118ac0c4100004e4003150014d40079d0316510c3c3430efd0c3ab028e518a3af, 0x78988de261f78985de2613020e21a262f6898ada261768984c0c20823051d4c23b039820ac14702d42000115000a458252360947c0c2082b051c102ba02c8200011580988e0261f0316222261788984c0c59000051400341, 0x24e500012d000c8400529001e440e4a02a491ca923f2a48dc0d4104b48ec0e4100004d4002950392514e4b753928c0b494424afc0b4940004840e2c202d280001150010a40d4140004e4007110030740180900aac40b508, 0x40ae80e208000456024a380927c0b48888925e2249302d24000145000d04007350032a400fbd045271093c3424eac07290000484e923f49c8ed27237000e51474bb51d2dd474a302d251093c3424efc0039459d2ed674b7, 0x53128c0b4944b0add854a302d28000115000ca40059d00224400c09039a21e24a378927de249778924c052085092ed424b750928d4249f024e20e91436a4ebc0b48842450c0b4880004840029d68925da2493014820a9147, 0xb4884b04dd8912b60928d8249f60925d824930312412c23b4b08dd844a362487d84497001271893af624ead874a361d25c0c4945312ed4c4b7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg23k4 : region H23 0x8111050100310ca8 0x0 := regionTerm _ _ prog23k4 adj23 _ _ 20 (by decide +kernel)
def prog23k377 : Array Nat := #[0x28c5000121000cb40051d001e241059829851ca613f2984dc0f58833c50c105880004f400295040c50f033f3c0cbc10594440cfc0b314000484102ba02d060001150010740f594000504007090030a40181100a4c403925, 0x38b0810208000455c432f710cac08310890c5e2430b020c2000145000ce40073d002c7400e350454616653b59947c0a2880004b4ca1433284fd46137028c50ea3433a8cfcea32f020c516653b5994dc0a314428d0d0a33f, 0x30c50ec3433b0cfcec32f020c50cc2bf614cbc0b4180004540031d0016a40088900304410790690cbda432b690c5da430b014820e4343390cfce432f390cac0f59043cd0d0f32b038c4000121790c5de430b014820a6247, 0x4e4c92bf498adc0b498424d0d0933f02d26000121000c540072900264400c9d00402401431020c40cc23f610cbd8432b61887d84317610c2c0c30833050ccc13f608cbd8612b608c5c00518628cbd8652361947d8a317, 0x624cad864a361927d89317624c4d8930b02d220c91433244fd261373244ad22317488c4c093143a4d0ce933f3a4cbce932b3a4c4c083103248fd2623b4988dd24317000c51464bb5192dd464a3024c500e2c2724cbc08314, 0x12618932f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg23k377 : region H23 0x8111050100310da8 0x100 := regionTerm _ _ prog23k377 adj23 _ _ 20 (by decide +kernel)
private theorem reg23k3 : region H23 0x8111050100310da8 0x0 := regionFork _ _ _ 8 reg23k4 reg23k377
def prog23k539 : Array Nat := #[0x2b471cad1bf03503000115000ce400511001e241170c40c50d0313f40c4ac0f7081bc51c117080004f4002a1045030911bf2446ec117202c46fc0e40c0004540029103dc800014500162400ab5005a74027a500dec404e19, 0x1c6200b44640cf0c11388000485671bb59c6dc0728c81c68e0718b01462000141000cb40073d002c4400e29041a31c36af70da4c0d4080004e46d1471b44fda312b0350308d1c72346fc8d1bb020a31c36af70daac0d40c, 0x68d25da3493025030891c72246fc891bb020a31091bf4a06ec0e28c000484003110016d4008890030741179c51c6ed471b751c68d4718b020e20871c721c6fc871bb21c6dc0f71c2bc71caf1b702ce300011579c68de718b, 0x68d8ada3617039880ac1c72b06fc0b40c4306fd8342b02d43000121000c5400535001e7400a910038240122501ca30e91bf49c6ed271b749c68d2339349c62c091881a451c6913f4886ed2313748868c0d48c4b46ed2d1a3, 0x2ca400e910048c4017250312312c1bb4b06dd891a362467d8349760d24d8918b0398206c1471b04fc6c13760c4ad821a360867c0c40c23071c8c1bf2306ec8c1b723067c0728c3b06fd833af60cead871a3001031a362f, 0x21871c861bf2186ec861b721867c0628c5186ed461b751868d4619f51862c0b30c19851cc314330c4fc66137000a30e334338ccfce332f039060a61c72986fca61b702cc310334340ccfc0b30c0004840031500167400809, 0xc30c91bf4986ed261b74986cd261a349867d2331748cc4d2618b000c30cc1bf60ccbd8332b61868d8619f60cc5d8331361862c08308]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg23k539 : region H23 0x8111050100310db8 0x10 := regionTerm _ _ prog23k539 adj23 _ _ 20 (by decide +kernel)
private theorem reg23k2 : region H23 0x8111050100310db8 0x0 := regionFork _ _ _ 4 reg23k3 reg23k539
def prog23k751 : Array Nat := #[0x2bc2dc0f58400045400341001424007910460116123b5848dd6121f041a408d0c704604000135000ab41158414430c510b70460b0b10b704161000115000a24106ac00051400591002af4016a9009e64037b101389406a8d, 0x2d1196153b0454400012d42830d0a0bf028a11ca0af72824c052040004e400321001cd400b090038740f704805e8e0178b03dc100014123c31c8f0b778487c0f58413c31c4f0c313c2dc0b284805e8e0179f03d610af0c7, 0x784c2c0b30411831c460c31182dc0b28432c30d660b7040a100012d000c24005bd00224400c29045aa0ea0c33a82fcea0af3a824c0e50412831c4a0c31282fc4a0b7041aa0ad0c72b42fc0a404000455aa0af6a824c00404, 0x78585c1062c2b031cac0b7020e10ec0c33b02bc0b404000474003150014f4007a9002a2400e110048640a28432830cca0bf5182dcca0af32824d4130b018810860c731030cc40bf2182dcc40af03cc10cf0c333c2bde1317, 0x3a2401231005c640c30433030ccc0bf6182bd860ab604c5d86093604c2c1061023031c8c0bf2302dd840af6102ad8121f0316104c0c713030c4c0bf1302dc4c0ab028a114c0b76282bd8152360547c0058478588de161f, 0x12430c490bf1242dc490ab024a10e90c33a42fce90af3a42ace9093025010890c72242fd2123b4902dc002845052ed414b750528c105a42a431ca90bf2a42dc0b48442430d090bf02d21000121000c54005a900204400b1d, 0x10c30c11404000424003390014a4007bd002a7400e35004894017190072c40930432430cc90bf4982dd260b33242bcc90ab484c5d26093484c2c004844b02dd890af6242ad814a360527d8149762424d8148b02d240490c7, 0x48c2dd211a348467d2309348462c1068c1b431c6d0bf68c2bda30ab68c24da118b044610e30c338c2fce30af38c2ace309303dc106f0c778468de309378462c111845046ed411a350462c1180c70c2bdc309300c410430c7, 0x146106c0c71b02fc6c0b760c2bd830ab60c29d811a360467d8309b60c24d8118b014610660c730c30cc30bf1982dcc30af30c2acc30a730c24cc118b014610690c71a42fd211bb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg23k751 : region H23 0x8111050100310dbc 0x4 := regionTerm _ _ prog23k751 adj23 _ _ 20 (by decide +kernel)
private theorem reg23k1 : region H23 0x8111050100310dbc 0x0 := regionFork _ _ _ 2 reg23k2 reg23k751
def prog23k1033 : Array Nat := #[0x3dc0000121000d1400509001e7411800700ebdc03ab700e4c1151c3a810c1181c0004a4002b9041c00500471400ac118384400ac1170000048400289045ca00014100167400abd005ad40278d00de1404c2501a0c408a99, 0x5b407c102800004b4ad0472b40fc0b4005b40ed6d01f020e000012d000c5400729002c2400e1103d60220797881e2c0f580000514ef0433bc0ade039303dc004f04713c10c4f02b03900220797881e4c0f70043c10d0f02b, 0x386004304710c10c4302b0390006e04770c0ac114000004e4003090016f40089d0030d4106a823411c8d03f2340ec8d01f0356004d04713410c4d03f1340ac116a842810d0a03f034a00001215340ed4d01f0350016d03b, 0x40200810472040ec8101f0416003004780407c11580000504003110016d4008a90030f40100d0350006d0471b40fc6d03b68c0ac6d01f68062c0718019c11ce304338c0fc6703b38c0ac0f1801bc11c6f03b78068de018b, 0x14f4007b5002a2400e1d0048340168500c2006104708c10c6103f1840ec6103708c0ac6101f03d6002f0470bc10c2f0370bc0ade101f78024c0a0800a811c2a0435040ed4103750407c0d0800b411c2d0436802bda0093, 0x48062c1149c3a410ce903f49c0ed270373a40ad203930392004904712410c4903f1240dc4902b0350012d03b6a40ada049768124c0e48078128de049778124c1172442410d0902b014800890472240ec0e28000044400321, 0x4300fd0c02b039800ac0472b00fc0b500000454003210016d40081d002c4400e890048940170d007214090800a411c290430a40fd2103b4840dc2902b48407d2009348403c091801a411c6903f48c0ed2303748068d2301f, 0x2d2012c03b4b00dd8902b60128d8901f60125d8049360122c0e61c13011c4c0431300fc4c0371300ac0c40023011c8c03f2300ec8c03723007c0c2803b010cec03f600ebd8702b001001a062f6818ada0617045cc10c043, 0x40a0000109000cb400535001ef400a910038a401205005ac401c0d0088940c0800b011c2c0430b00fc2c0376002bd8102b60409d8101f60024d8100f0306006c0471b00fc6c03b1b00dd8302b60c09d801a360c07d8018b, 0x980dcc00af3040acc0093045460ca0433280fd4603b5180dd4601f500c2c1030021811c8603f2180ec8603721807c0f58033c10de601f780c5de030b040c01a032f680c5da030b0460616603b59807c0510011811c46043, 0x3240ad2601f480c5d2031349803d2030b49801c0618019811cc304330c0fc6603b1980dcc303330c0ac6601f30062cc3007020c00cc0433300fd8032f6180ad8601f600c5d80313600c2d860070182002604730410cc103f, 0x20c00c90433240fd2603b4980dd26033]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg23k1033 : region H23 0x8111050100310dbe 0x2 := regionTerm _ _ prog23k1033 adj23 _ _ 20 (by decide +kernel)
private theorem reg23k0 : region H23 0x8111050100310dbe 0x0 := regionFork _ _ _ 1 reg23k1 reg23k1033
private theorem safe23 : hostSafe H23 := regionHost _ _ _ bk23 reg23k0
def H24 : Array Nat := #[0x1, 0x2, 0x3, 0x4, 0x5, 0x8, 0xa, 0xc, 0xf, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x18, 0x1a, 0x1c, 0x1f]
def N24 : Array Nat := #[0x15151514, 0x11331132, 0x11111110, 0x50f050e, 0x5050504, 0x3f003e, 0x330032, 0xf000e, 0x10000, 0x953e, 0x1514, 0x1132, 0x1110, 0x50e, 0x504, 0x3e, 0x32, 0xe, 0x0]
private theorem bk24 : bookOK H24 N24 0x953f953e = true := by decide +kernel
private theorem adj24 : validRows H24 N24 := rows_of_book _ _ _ bk24
def prog24k2 : Array Nat := #[0x4440d3c2034ef80729003962805208388acce22ab388a9c0729000042407208000454004ad038f080e3be000820e22b3388abce22ab388a9c0729000042407208000454005390030d40520800047401299012c34077a1, 0x169407308035448ea327024c2000129034f080d3be01cc20ea327024c2000129038f080e3be028820ea32702482000129000ae4006350188200011d002c54013b10092b4092883a48bc0b2880004940d2320348a807288, 0x39820ce29303082000139000aa400525024e401013a0404a80731000042409398000504004150030d40c346030cf809288324aecc92b7324aacc9293028a20ca2bb328adcca293018a20ce2b7338a4c0d2080004e400329, 0x328a4c07314334aeccd293039640eb2b3018a400011d000ad4004a9001e940731000045400c0902cd180b33e035820cd2bb334aaccd2a701cc200011503584806288324aed8549f324aacc9293018a20ca2bb61547cca293, 0x3886bce21ab38869c0730c000424061880004740051100725406288324add65493034a400012559447c0d39033449c093900004d40029502c4e80b12a000c50c92bb324add6549f324aad65493000c50ca2bb328add6551f, 0x4a48b1c322c6fc8b19b03ce308f1c303d868106183b06acec18b0188300011d000cf40c2460308d8105082406fc9019b03d460ea18b03cc300011d0289180a23603cc2000129001304006b10032b401225018620e21b3, 0x2886bca21ab01ca30851c32146fc851af21466c0728c30caecc32b730caac0728c00046400391001a2400c2501c830e91b33a46ace918b0106200011d22470c891bf2246bc8919b0008300a2460288d96351f02d4280c588, 0x390f80918822470c891bf22466c8919701062000125024620001110248200010d0018e400bb50046c40262d00cca40728c2a46cca91af2a46ad2519b48ca4d2518b014620851c321466c0e1880004446513f28c4dca21b3, 0x1ca40ec2a73b0a2c09290000474093900004540040d0024e40c4460310f80c436018a20cd2bb334a9ccd293334a3c09288000464093080004540d4420350f806288338a9cce293338a3c09288000464093080004540e442, 0x2d1180b43e02d0e80b436024a21c549b61527d8548f01ca31c519b2b062c073140004340032501cc30ec1a73b062c0930c00047409398000434004150391080920c60d27d834970106218311f60c45c0c20c00042400325, 0x3a862c0930c00047409398000434004950291180a4420290f80a4360290b80728c2ac6ccab1a758ca4cab18b0316208b1c322c69c8b19b024e3000111000e54072903acacceb2a73aca2c09290000474093900004540048d, 0x728c2a86ccaa1a751466caa18b031420ca2bb328a9cca293024e5000119000e340730c3a86ccea1a7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg24k2 : region H24 0x953f9538 0x0 := regionTerm _ _ prog24k2 adj24 _ _ 20 (by decide +kernel)
def prog24k369 : Array Nat := #[0x42409384000514004190018b400ac101c4101162204586811612000e122138b59c24c04104000474115a20456680410414429c5109f02481000109000cb400731024e4000145002ae4017bd0086a4036350118540580d, 0x3d0c80f42e000810c40bb23c29c073040004440f33203ccb80720400046400521001e2406204041c881071e041c280730402cd18ce0a733824c072040004640e5a20396281171c33829cce093000410510a714427c09384, 0x1cc100c346030cf80a1040004c40032d3282ecca0a732824c0410412431c490bf50527c001041442fc1151214427c0f384000514003a50285080a12e01c8100010900206400f2103dc404f0c713c29c4f09f0248100f43a, 0x68546c0d5120284b80e6900004a44d0c71342fc4d0a713427c073043342eccd0ab33429ccd09301c8100011900102400a2101cc10ca0bb32829cca093024e10001190291180a4420290f80a42e01cc100b34602ccf80b50a, 0x2902ac0628411431c450bf1142dc4509f018a10aa0bb2a82dd4509f018a10e12b3384abc0628400047400329001624008910038940610413431c4d0a713427c093040004240d4420350f80d4320350b80d42a0004100a142, 0x2046bc8119b0006106a0bf50c27d4119b01c610c30bb30c2dc07184000464003290016440088900389401215024a10a90bb2a42dca90ab49427d25093484a2c052040309198509f010410001312142fca40bb2902dca122f, 0x610650bf28c2eca30b72846cca11af28c2aca30a728c24ca118b020610690bf1a42ad2309f48466d2309348462c0310420470c811af20466c06184000444430c710c2fc430b710c27c0718420470c811bf]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg24k369 : region H24 0x953f953c 0x4 := regionTerm _ _ prog24k369 adj24 _ _ 20 (by decide +kernel)
private theorem reg24k1 : region H24 0x953f953c 0x0 := regionFork _ _ _ 2 reg24k2 reg24k369
def prog24k591 : Array Nat := #[0x24e000014500104400629002ae4071000458881161a04584800380880e2d4701b0184000011d045488115120184005102714407c0930000042400329001cc40939800051400ac1005ed4021ad00d8f40461501603406f85, 0x350a80620021810ccd02701c800001190348c80d22a01cc00001110014840078901880010722041c781070a01c8000a24624009c9001b01cc00001110414881050a0460709002724006c0010014409c5101f024e0000109, 0x309180c23602c40000131000ca48b04322c09c8b01b018400490471240dd6049f000400510370456685101f034e0000145000e940b13a02c4a80730000042400811003c841069813411c4d02713407c093000351080d432, 0x2c4e80b12a041e600012d13c11c4f03713c09c4f01f01c8008f04323c0bc8f02723c06c07300000444004090028840720022c10c8b02722c06c093800004440b44602d0e80b43602d0a8072000289180a23602d42807200, 0x1ca00c02bb300adcc02ab300a4c002802ac0dd6501f580a4c0728021410c8503f01ca0000111000cb40059900222400e250104004f04713c09c4f01f0248000010903d0e80f43603d0c80f42e03d0a80010003d669e0593, 0x10c07c041801ac10c6b03f58c07c041803806cce01ab0106000011d000cb40058900226400e25004854082802a40dca902f49407d2501b480a4d2028b014400850432140bc8501b018a000011111411c4503f1140dc4501f, 0x5e340518019410c6503f28c0dca01b328c0bca01ab28c09c6501b28062c091801a410c6903f1a40bd2301f48c06d2018b0186000c34660c07c061000004c4660431980fcc30371980bcc01ab0106004304710c0fc43037, 0x48407d2101b48024c07080038f09c101b01c8000013909c11c2703f09c0dce102f3802ac0208020410c8103f2040bc8101b0082002d0470b40fda101b008200c00bb3002ac02080000464003350016440089d00389401215, 0x308008c11c610431840fc230371840bc600ab18409c2301f18406c61017014200250470940fca00bb2840dca102f2802aca102709407ca0093024200290470a40fc29037]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg24k591 : region H24 0x953f953e 0x2 := regionTerm _ _ prog24k591 adj24 _ _ 20 (by decide +kernel)
private theorem reg24k0 : region H24 0x953f953e 0x0 := regionFork _ _ _ 1 reg24k1 reg24k591
private theorem safe24 : hostSafe H24 := regionHost _ _ _ bk24 reg24k0
def H25 : Array Nat := #[0x1, 0x2, 0x3, 0x4, 0x8, 0x10, 0x11, 0x14, 0x15, 0x18, 0x19, 0x20, 0x22, 0x24, 0x26, 0x28, 0x2a, 0x3c, 0x3f]
def N25 : Array Nat := #[0x1000055501110114, 0x1000011103330112, 0x1000011101110110, 0x5050303010e, 0x550033001e, 0x5550000011e, 0x55500000114, 0x5050000010e, 0x50500000104, 0x550000001e, 0x5500000014, 0x333011e, 0x3330112, 0x303010e, 0x3030102, 0x33001e, 0x330012, 0xe, 0x0]
private theorem bk25 : bookOK H25 N25 0x900005550333011e = true := by decide +kernel
private theorem adj25 : validRows H25 N25 := rows_of_book _ _ _ bk25
def prog25k3 : Array Nat := #[0x34e214d4bb038e2000135000ac40a3880004940a142024e2000129001e840c524430f0d0c3bf029270001210292800011d03d4910f3c30414900013d029270001210292800011d0012c400889006a64034910154b407d15, 0x819e8e0679f041c200013d03dc20001410010d400ab1041221103bf440ecc094080004741012a0314210c3bf61c49c0c4085312dc094080004a40a4080004940039d03da2000131001b040813a0292214c4bb5312dd8911f, 0x3b0cfc0c308430d0d0c33f030c2000121530ced4c337030c212c33b4b0cdc083080004950c343430cfc0930800048400529002474073083344fc0e122020e6000109719aadc66a7041ed1e668b041a200013d000ae40e308, 0x18940089d0310712c23b4b08dc0c41c5308ed4c237020e4000129000c940a490410f0d043bf039a7000121039a800011d0010c4009090058640c3984b0ced2c3374b0e2c0c308530ced4c337030c2000129000c94ec343, 0x69882c0e30881888e0621f03882000141000cd40053d001ec400208410f0c0813a038e20001213904fc871373888cc082084888ed222374888cc0c2085308dc0a2080004c40a142020820001294104fc0813a02882000121, 0x4250b3c342cefd0b3b30292712b3b34ace2c0a3880004940032102d0214b4bb52d2dd4b4b3029020001250250200012900127400c11005c640c3083308eccc23761888d8621f039a61e622379887de620b041a40cd23b, 0x71969c105880004e40053d001ed400a310034440a20822c4dd6412758888d6411f000041845ab61169d845a361167c0b41c4ac8ed2b23702d0714b23b52c8dc083900004a4003250014c40080902d4200813a59c49c0b524, 0x3dc20001410012d400c11005cc40282d02cc40cb23b32c8dccb23359888d6621f59882c003086196ad865a761968d8659f020e61a65ab69969da658b029261e65a379967de658b020e610b34303902807308000485c65ab, 0x310adc0e690390b0ce42bf039a41042c3410afc0e6940004840031d0014640080901ca20ad13f03848808394000425c56ab715a9dc569b041ed1e569b795a2c106880004f400339038a22057a3815e7e0579b041c200013d, 0x330aeccc2b7039ac0ec2c33b0afcec28b0310512c2bb4b0add2c28b030a214c2bb530adc082880004a50c2c3430afc0a28800048400525001e7400a19003444102082904fca223b2904dc8511f000040c42c3310afcc42bb, 0x2ca210b2c30204e80a288000484ab13f2ac4dd6512759447c0e6ac3acb0ceb2bf02d0512b2bb4acadc0a4140004940031d00142400a3100346401091030a40ac23b2b08dd8522361487d8521b2b082c0c288330b0ccc2bf, 0xb2902ac8ecab2372ac8cd6522359487d6521b59482c0b28832cb0ccb2bf32caeccb2b732cacc002886156ad855a761568d8559f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg25k3 : region H25 0x9000055503330108 0x0 := regionTerm _ _ prog25k3 adj25 _ _ 20 (by decide +kernel)
def prog25k374 : Array Nat := #[0x4c40813a02862000121028509431370206200012900189400a9d031490ec1c33b06fc0c52443070d0c1bf02923000121000c740838c50d2ed434b7041e9000129041ea0001250010c400909005864020ad00be5404311, 0x6186ad861a7041e61a61ab69869da618b03dc30cf1c379862c103087186adc61a704062000139000cf400535001ec40a48838870ce21bf3886cc00188028509434bb041220001291a44fd231374886cc0c1884306fc08188, 0x2cc30cb1c332c6fccb1b35986ad661a759862c081881ac4fd621ab58c49d6311f000031835ab60d69d835a360d67c0b5243ac70ceb1bf02d4910b1c342c6fc0a48c0004840031d0014c400809002c640c30833070ccc1bf, 0x59466d6518b030a30ac1c32b06fd851ab61469d8519b2b062c0e18828870ca313f28c4dc65127000030c32c330cafcc32bb30cadc1078c48caed232b7041e31432bb50cadc107940004a40032500146400809002cc400f2d, 0x2086cc6412720c47c0020c6106ad841a760c88d8321f029240e41c33906fc0820c48c8ed23237028831041c34106fc0a20c000484003250014740073100282400f99004eb40181502ca30ab1c32ac6fcab1b35946ad651a7, 0x20c29070ca41bf28c8eca32372906cca41af21466ca418b0008308b1b35906ad641a758c88d6321f59066d6418b000830c41c33106fcc323b30c8dcc41b321862c0418841070c0813a038620001211904fc83137]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg25k374 : region H25 0x9000055503330118 0x10 := regionTerm _ _ prog25k374 adj25 _ _ 20 (by decide +kernel)
private theorem reg25k2 : region H25 0x9000055503330118 0x0 := regionFork _ _ _ 4 reg25k3 reg25k374
def prog25k565 : Array Nat := #[0x1211890ab62428c0a4040004940031d029211013c3404efc003845052ed414b7024e1000129028e1000125001084004045052ed414b7025010001290290100012500107400a31003e2401b9900a8b40381101345406b8d, 0x4e40032100147400735002ec40a41c11c31c470bf11c2dc470a7029280490c71242fc490b70354804d0c71342fc0810402850941433020410001290204e80a104000484004b5001a940091d000e11870ab61c29d870a3, 0x12112b0b75a42ad690a302901000125000e7400689002864061046182ad860a761828d8609f0350604d0c713427c10304000424cd0bf6982ada60a7038410e1343384cfc0e104404d0d0133f018411c60ab71829c06104, 0x6902ada40a723428c8d09f038e10e40bf21c28c0e404000474003350018c400909003264010ad018410cb0bf32c2dd660ab59829d660a359827c0b52012c31c4b0bf12c2dc4b0a712c27c003843ac2fd670ab59c29d670a3, 0x1e6400a890042c40142d0064440020422c2dd640ab59029d640a359027d6409b58482c061043102fcc123b3102dcc123321828c8609f029040440c71102fc440b711029c4409f000811840ab61029d840a361027c00204, 0x61427d8509b014411c50ab038489c509b0404100013911431c450bf1142dc450a711427c00004304b0cc12bf304aecc12b7040a10ad0bf6942ada50a7038a10e12c3384afc0e284404b0d012bf038a1000121000c7400535, 0x4141000125000cf40063100242400c990042b401515006a44052042902fca123b2902dca12332902bc850a321427c8509b28482c002842ac2fcab0b75942ad650a759428d6509f59426d6128b014411850ab61429d850a3, 0x58c2ad630a758c28d6309f58c26d6118b018410c11c330c2fcc30b73046cc660ab19829c0a40c10c31c430bf10c2dc430a710c27c0018460c2ad830a760c28d8309f0006106f0ab1bc29de30a378c27c1048448c2dc690ab, 0x10610640bf20c2dc811b320c2bc640ab19029c830a320c27c8309b20c25c8118b014610a11c328c2fca30b72846cca30af1942ac650a719426ca118b0006106b0bf]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg25k565 : region H25 0x900005550333011c 0x4 := regionTerm _ _ prog25k565 adj25 _ _ 20 (by decide +kernel)
private theorem reg25k1 : region H25 0x900005550333011c 0x0 := regionFork _ _ _ 2 reg25k2 reg25k565
def prog25k845 : Array Nat := #[0x33c10ccf03b041c000013d000cd408380701aadc06a7029202007a3801e7c0f680000504106800004f400439029202007a3801e7c0f700000504107000004f40043500286400f89006ec402c1500e84404f2d01ae3408c85, 0x4840052500247400d99041cd04d0471340fc4d02713407c107b813c11c4f02713c07c1071c11c11c470270244020071b0404a80e1000005040e12204040000139001274006bd0024d40d30033410ccd03f3340ec0f300, 0x4f4003b5001a2400a31030400cc0433300fccc03b3300dc0e61c11c11c47037031400001093b010cec03f61c09c1062412411c4903f031000001094b00ed2c0370304014c03b5300dc081000004a50c0434300fc0a100, 0x2340eda402703900000135000c740061900242400cb10042540c1002b010cac03f2b00ecac03761409d8501f041c50450471140fc4503711409c4501f034a00ad0432b40fcad03b69409c0f2802bc10caf03b79407c10700, 0x800a40432900fca403b2900dca403321407ca020b0304008c03b2300dd8402760088d8401f60086c1071011011c4403f1100dc4402711007c0020031010cc403f3100ecc4037000800e40433900fc8703b21c0dc0d400, 0x32c0cc0b10042c10c0813a42c0cc0a1000004844b04712c0fc4b03712c09c4b01f000001805ab60169d805a360167c0b5003ac10ceb03f59c09c0b4004ac0ed2b03702900000125000c74005b100222400e9900485401711, 0x4f400325001864009090032c4010950054b401a910288008b03b22c0dc8b03359009d6022359007d6021b59005d6020b02ca00ab0432ac0fcab03b2ac0dcab03359409d6501f580a2c0b10032c10ccb03f32c0eccb037, 0x28c0eca303728c0cc6502728062c0c1001b010c6c03f6006ad8302760c07d8019b041c304304710c0fc4303710c09c4301f000600c304330c0fcc303b30c0dc001801a410c6903f48c0ed2303703d4006f04378c07c10500, 0x209400b99003c740132d00605401d910090340418019010c6403f20c0ec8303720c0cc8302f19009c8301f20066c8301720062c081801ac10c6b03f1ac0cd601ab58c09d6301f58066d6301758062c0018028c10ca303f, 0x38410ce103f09c0dce103309c09c0208030410cc103f3040ecc10373040cc104840a411c2903f4840ed210374840cc0d4000b411c2d03f6802ac1170440410d0103f4040cc020805040ed4103300820000129000c84005b5, 0x9011c2403f2040ec810372040cc8102f09009c800a320407c8009b20405c0208009411ca10432840fca103b2840dca10332840bc2502709407c020800ac11c2b03f0ac0dd600ab58409d600a358407d6009b038e1027047, 0x82002304718410c6103f08c0dc610331840bc600ab18409c2301f18026c6101718404c02080]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg25k845 : region H25 0x900005550333011e 0x2 := regionTerm _ _ prog25k845 adj25 _ _ 20 (by decide +kernel)
private theorem reg25k0 : region H25 0x900005550333011e 0x0 := regionFork _ _ _ 1 reg25k1 reg25k845
private theorem safe25 : hostSafe H25 := regionHost _ _ _ bk25 reg25k0
def H26 : Array Nat := #[0x3, 0x4, 0x7, 0x8, 0xb, 0xc, 0xf, 0x10, 0x13, 0x14, 0x17, 0x20, 0x23, 0x28, 0x2b, 0x30, 0x33, 0x3c, 0x3f]
def N26 : Array Nat := #[0x1001010100111110, 0x9090900090908, 0x1010100010100, 0x9000900990098, 0x1000100110010, 0x9000900090008, 0x1000100010000, 0x90900009998, 0x10100001110, 0x90900000908, 0x10100000100, 0x999998, 0x111110, 0x990098, 0x110010, 0x9998, 0x1110, 0x8, 0x0]
private theorem bk26 : bookOK H26 N26 0x9009090900999998 = true := by decide +kernel
private theorem adj26 : validRows H26 N26 := rows_of_book _ _ _ bk26
def prog26k2 : Array Nat := #[0x4940f43a03d0c80f5a40288580a48078166de059778162c0f5940004040f2800004b40049103d4e80f532001251e559b79564de558b79560c0f5a40004540f4940004b4005290030840b4940004f4012b5012c74077c5, 0x16040d288789a0c08126034a000010903d0e80f432034a21e2683034a000010903d4e80f532024a21e2683024a0000109000aa4006210352500013d002cb4013990092440b28078124c0b2900004040941a0250280f594, 0x28c51aa5a7024c5000129000a240050103d2000e2aa038a280f6a40004540f6800004e40042d0030840d342034cc8002806816ada05a768168da058b000a21a25ab68969da25a3001451aa5a76a968c094140004a400309, 0x68968c083106a16ada85a7028c41aa5a7024c4000129000a8400489001e040f6a40004b400c150349080d232020c51a85ab6a162da858303da500012d020c980628032c0fda05ab68169da058b018a20cb13f6896ada25a7, 0x794e4de538b794e0c0f69c0004540d3940004f4005250072b40b20068169da05a302d280001012ac8fc0f4a06a0a0c0f480000484002ad0148a80520a0188008b03f6816ada05a368162da05a70188208b13f6896ada25a7, 0x425243bb490edd243b303d8712c3bb4b0edc0e698798e5de638b0352700013d000cc409342024c880e2884b8edd2e3b3030a212c3b7034a200013102450809122035850001090012e40069900324401201034e51e539b, 0x594e4d6538b02cc212b3bb4acedd2b3b34ace4c0731069d6ada75a369d62c0f59c0004d4003a5001a5400c01000001e039b780e5de038b01ca000013d480eed203b7480ecd203930188200914221c4fc0912201045806290, 0x454c800280480eed203b7480ecd203af024e500010101ca0000125024a000011d0018a400ba10046640261100cc240b3803ac0dd67027580e6d67017580e4d6038b02ce512b3bb4acedc0a394000494eb2b359ca8d6539b, 0x1261e659779960c0b4800004f40f4800004b40041d0024a411342044cc811322001051a85ab6a169da859f6a160c0b2800004d40d2800004b41143a0450c8005146a969daa59f6a960c0b2800004d40d2800004b41153a, 0x44908112320448a81122202ca00cb03f52c0dccb01f02ce614b3b7598e5c0f6ac00047400301034e61e6397798e0c0d3800004f40f6800004740042d0454e80938031c0fcc702f024e50c72bf31cabc0939800045400301, 0x788e0c0d3800004f40f680000474004ad0445081113a0444c8111220444480039059c89d6439b590e5d64383018a41243bb490edd2438303ce0000125000eb40049079166de459779160c0b4800004f40f4800004b40049d, 0xb3883ac4dd6239b588e5d62383018a21a25ab68969da258303d60000135000e740d388788e6de2397]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg26k2 : region H26 0x9009090900999888 0x0 := regionTerm _ _ prog26k2 adj26 _ _ 20 (by decide +kernel)
def prog26k369 : Array Nat := #[0x4540f1800005040043500184400ab9041e0010346040cd8103260106020379723c69c104800004f4102460408d80928c2c06fcb018302460000115000c440071903d20000141002aa4017b1008624036210118b40581d, 0x4586811612000601a01ab68069c0a48c0004040d61a0358480f48c0004d400545001e540d48c0395180e53e0394580f50c034909aa1a76a860c0f48c0004d40a246028858107a86a869daa183000a30b01bf2c060c06180, 0x3c6200d342034cc805188000464003116886ada21a768860c0310028070ca01bf2806cc051882c06fcb01b30404980f60c000504003810144e80511203d230001150020d400f45031490ac1c32b06fcac1830246001162a, 0x40c4dc081260144480a4a0000424a81c32a06fca81b32a060c0f40c6a06ada81a76a062da818303d2300013500105400a4503c621a21ab68869da218303c600001350445081113a0444c81111203c6200d2420348c804116, 0x5a462c0b5082ac70cab1bf2ac6ccab1a302c6206b13f5886ad621a3029031e359b78d64c0d58c0004f400309001654008a50038040d28c2a070ca81bf2a060c0d1800004541143a0450c81141a0450481140a0146200513a, 0x48cecd2339301c6206713f38c4dce21b303ce31a71ab69c68c0f38c0004d400309001694008950038040122d02c6006b03f5806ad6302758068d6301758062c0b48c024d08cb1bf024a30001194ac6cd691ab5a468d63493, 0xe30eb1b359c6ad671a759c68d6339b58ce5d6339359c62d6718301c6006703f38c0dce01b319c09ce301738062c0718848ceed233b748ce4c0a388000494a71c329c6fca71b329c68c0618848ceed233b7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg26k369 : region H26 0x9009090900999988 0x100 := regionTerm _ _ prog26k369 adj26 _ _ 20 (by decide +kernel)
private theorem reg26k1 : region H26 0x9009090900999988 0x0 := regionFork _ _ _ 8 reg26k2 reg26k369
def prog26k591 : Array Nat := #[0x3c2000014100109400609002aa410780040d1810336040c9802080805e5c4f0b7041a000013d04051810126034a10b00bf2c020c0d08000045400309001c640f68000050400ab9005e840219100d8c40462d01607406f8d, 0x45028000804802ed200b7035210001010250680940a03da1000125001514007950352100e5460394f80e51603d210091424b82dd2e08303da10001250385180e116041ee12e0b74b820c002842c02fcb008301820000115, 0x24d080932201481000119000c25240bb4902dd24083000200a00c32802fca00a3000a10b00bf0408d8b00a303d01000141000e040522a0148280f68400045400825003d140e6a02a030ca80bf2a020c0d0800450e81141a, 0x148a80520a039ac0001112b030cac0bf2b028cac08303d2112c0bb4b02dd2c0934b020c0f684000494004150029140f2044902ed240b749020c0f080000494112420448a8112220448280f204024508091220104580f204, 0x18811a15ab68569da15a368562c0b10422c2fd6122759028c0f5844ac2ed2b0b303d61000125000c44005b500225400e01024a10ac0c32b02fcac083024200001150458a81162204586811612045828002840308d981227, 0x29c28c0720421c2fce40bb3902cc09384784e6de138b024e100013d000c44005950022d400e010048b40b0800ac0fc2b03758409d600a358405d6009302c4112b0bb4ac2dd2b093035610001252ac30cab0bf2ac2ccab0a3, 0x5e740b3843ac2eceb0b73ac2cd670a3584e6d6139759c24d6138b59c20c0708009c0fce00bb3840dce00b338405ce0093034e100d34231c2fc0d284000464ed0bb3b42cda70a33b424da138b024e10a70c329c2fca70b3, 0x1802cc6102718028c0f18403d4e9430b703d210001291bc30c6f0b31bc28de309378462c0518448c2ed230b748c2cd23093014610680c340c2dc680b3014611a11ab68462c051840004d400321001694008bd0038040122d, 0x718419c30c670bf38c2ece30b738c2cce30af19c28ce309338462ce308302c6106b0c31ac2fc6b0b35846ad611a758c28d6309358462d6308300c200600c31840fc23037]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg26k591 : region H26 0x9009090900999998 0x10 := regionTerm _ _ prog26k591 adj26 _ _ 20 (by decide +kernel)
private theorem reg26k0 : region H26 0x9009090900999998 0x0 := regionFork _ _ _ 4 reg26k1 reg26k591
private theorem safe26 : hostSafe H26 := regionHost _ _ _ bk26 reg26k0
def H27 : Array Nat := #[0x3, 0x4, 0x7, 0x8, 0xb, 0x10, 0x14, 0x18, 0x1f, 0x20, 0x23, 0x24, 0x27, 0x28, 0x2b, 0x30, 0x34, 0x38, 0x3f]
def N27 : Array Nat := #[0x111011101110110, 0x101090901010908, 0x101010101010100, 0x11009900110098, 0x11001100110010, 0x99900000998, 0x90900000908, 0x9900000098, 0x100000000, 0x81110998, 0x1110110, 0x1010908, 0x1010100, 0x110098, 0x110010, 0x998, 0x908, 0x98, 0x0]
private theorem bk27 : bookOK H27 N27 0x8111099981110998 = true := by decide +kernel
private theorem adj27 : validRows H27 N27 := rows_of_book _ _ _ bk27
def prog27k2 : Array Nat := #[0x4440d3c2034ef80729003962805208388acce22ab388a9c0729000042407208000454004ad038f080e3be000820e22b3388abce22ab388a9c0729000042407208000454005390030d40520800047401299012c34077a1, 0x169407308035448ea327024c2000129034f080d3be01cc20ea327024c2000129038f080e3be028820ea32702482000129000ae4006350188200011d002c54013b10092b4092883a48bc0b2880004940d2320348a807288, 0x39820ce29303082000139000aa400525024e401013a0404a80731000042409398000504004150030d40c346030cf809288324aecc92b7324aacc9293028a20ca2bb328adcca293018a20ce2b7338a4c0d2080004e400329, 0x328a4c07314334aeccd293039640eb2b3018a400011d000ad4004a9001e940731000045400c0902cd180b33e035820cd2bb334aaccd2a701cc200011503584806288324aed8549f324aacc9293018a20ca2bb61547cca293, 0x3886bce21ab38869c0730c000424061880004740051100725406288324add65493034a400012559447c0d39033449c093900004d40029502c4e80b12a000c50c92bb324add6549f324aad65493000c50ca2bb328add6551f, 0x4a48b1c322c6fc8b19b03ce308f1c303d868106183b06acec18b0188300011d000cf40c2460308d8105082406fc9019b03d460ea18b03cc300011d0289180a23603cc2000129001304006b10032b401225018620e21b3, 0x2886bca21ab01ca30851c32146fc851af21466c0728c30caecc32b730caac0728c00046400391001a2400c2501c830e91b33a46ace918b0106200011d22470c891bf2246bc8919b0008300a2460288d96351f02d4280c588, 0x390f80918822470c891bf22466c8919701062000125024620001110248200010d0018e400bb50046c40262d00cca40728c2a46cca91af2a46ad2519b48ca4d2518b014620851c321466c0e1880004446513f28c4dca21b3, 0x1ca40ec2a73b0a2c09290000474093900004540040d0024e40c4460310f80c436018a20cd2bb334a9ccd293334a3c09288000464093080004540d4420350f806288338a9cce293338a3c09288000464093080004540e442, 0x2d1180b43e02d0e80b436024a21c549b61527d8548f01ca31c519b2b062c073140004340032501cc30ec1a73b062c0930c00047409398000434004150391080920c60d27d834970106218311f60c45c0c20c00042400325, 0x3a862c0930c00047409398000434004950291180a4420290f80a4360290b80728c2ac6ccab1a758ca4cab18b0316208b1c322c69c8b19b024e3000111000e54072903acacceb2a73aca2c09290000474093900004540048d, 0x728c2a86ccaa1a751466caa18b031420ca2bb328a9cca293024e5000119000e340730c3a86ccea1a7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg27k2 : region H27 0x8111099981110980 0x0 := regionTerm _ _ prog27k2 adj27 _ _ 20 (by decide +kernel)
def prog27k369 : Array Nat := #[0x42409384000514004190018b400ac101c4101162204586811612000e122138b59c24c04104000474115a20456680410414429c5109f02481000109000cb400731024e4000145002ae4017bd0086a4036350118540580d, 0x3d0c80f42e000810c40bb23c29c073040004440f33203ccb80720400046400521001e2406204041c881071e041c280730402cd18ce0a733824c072040004640e5a20396281171c33829cce093000410510a714427c09384, 0x1cc100c346030cf80a1040004c40032d3282ecca0a732824c0410412431c490bf50527c001041442fc1151214427c0f384000514003a50285080a12e01c8100010900206400f2103dc404f0c713c29c4f09f0248100f43a, 0x68546c0d5120284b80e6900004a44d0c71342fc4d0a713427c073043342eccd0ab33429ccd09301c8100011900102400a2101cc10ca0bb32829cca093024e10001190291180a4420290f80a42e01cc100b34602ccf80b50a, 0x2902ac0628411431c450bf1142dc4509f018a10aa0bb2a82dd4509f018a10e12b3384abc0628400047400329001624008910038940610413431c4d0a713427c093040004240d4420350f80d4320350b80d42a0004100a142, 0x2046bc8119b0006106a0bf50c27d4119b01c610c30bb30c2dc07184000464003290016440088900389401215024a10a90bb2a42dca90ab49427d25093484a2c052040309198509f010410001312142fca40bb2902dca122f, 0x610650bf28c2eca30b72846cca11af28c2aca30a728c24ca118b020610690bf1a42ad2309f48466d2309348462c0310420470c811af20466c06184000444430c710c2fc430b710c27c0718420470c811bf]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg27k369 : region H27 0x8111099981110990 0x10 := regionTerm _ _ prog27k369 adj27 _ _ 20 (by decide +kernel)
private theorem reg27k1 : region H27 0x8111099981110990 0x0 := regionFork _ _ _ 4 reg27k2 reg27k369
def prog27k591 : Array Nat := #[0x24e000014500104400629002ae4071000458881161a04584800380880e2d4701b0184000011d045488115120184005102714407c0930000042400329001cc40939800051400ac1005ed4021ad00d8f40461501603406f85, 0x350a80620021810ccd02701c800001190348c80d22a01cc00001110014840078901880010722041c781070a01c8000a24624009c9001b01cc00001110414881050a0460709002724006c0010014409c5101f024e0000109, 0x309180c23602c40000131000ca48b04322c09c8b01b018400490471240dd6049f000400510370456685101f034e0000145000e940b13a02c4a80730000042400811003c841069813411c4d02713407c093000351080d432, 0x2c4e80b12a041e600012d13c11c4f03713c09c4f01f01c8008f04323c0bc8f02723c06c07300000444004090028840720022c10c8b02722c06c093800004440b44602d0e80b43602d0a8072000289180a23602d42807200, 0x1ca00c02bb300adcc02ab300a4c002802ac0dd6501f580a4c0728021410c8503f01ca0000111000cb40059900222400e250104004f04713c09c4f01f0248000010903d0e80f43603d0c80f42e03d0a80010003d669e0593, 0x10c07c041801ac10c6b03f58c07c041803806cce01ab0106000011d000cb40058900226400e25004854082802a40dca902f49407d2501b480a4d2028b014400850432140bc8501b018a000011111411c4503f1140dc4501f, 0x5e340518019410c6503f28c0dca01b328c0bca01ab28c09c6501b28062c091801a410c6903f1a40bd2301f48c06d2018b0186000c34660c07c061000004c4660431980fcc30371980bcc01ab0106004304710c0fc43037, 0x48407d2101b48024c07080038f09c101b01c8000013909c11c2703f09c0dce102f3802ac0208020410c8103f2040bc8101b0082002d0470b40fda101b008200c00bb3002ac02080000464003350016440089d00389401215, 0x308008c11c610431840fc230371840bc600ab18409c2301f18406c61017014200250470940fca00bb2840dca102f2802aca102709407ca0093024200290470a40fc29037]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg27k591 : region H27 0x8111099981110998 0x8 := regionTerm _ _ prog27k591 adj27 _ _ 20 (by decide +kernel)
private theorem reg27k0 : region H27 0x8111099981110998 0x0 := regionFork _ _ _ 3 reg27k1 reg27k591
private theorem safe27 : hostSafe H27 := regionHost _ _ _ bk27 reg27k0
def H28 : Array Nat := #[0x3, 0xc, 0xf, 0x10, 0x13, 0x1c, 0x1f, 0x20, 0x23, 0x2c, 0x2f, 0x40, 0x4c, 0x50, 0x5c, 0x60, 0x6c, 0x73, 0x7f]
def N28 : Array Nat := #[0x1001100110010000100110011000, 0x80001000100010000000900090008, 0x1000100010000000100010000, 0x1001000010010000900900009008, 0x1001000010010000100100001000, 0x1000000010000000900000008, 0x1000000010000000100000000, 0x100110010000000090099008, 0x100110010000000010011000, 0x100010000000000090008, 0x100010000000000010000, 0x900990099008, 0x900090008, 0x900900009008, 0x900000008, 0x90099008, 0x90008, 0x1000, 0x0]
private theorem bk28 : bookOK H28 N28 0x80081001100110010000900990099008 = true := by decide +kernel
private theorem adj28 : validRows H28 N28 := rows_of_book _ _ _ bk28
def prog28k2 : Array Nat := #[0x4840f4ba03d2c80f5a0028a480a40478566de159378562c0f5900004140f2040004b40049503d4e80f532001041e459b79165de458b79161c0f5a00004440f4100004b4005290030940b4100004f4012b5012c74077c5, 0x16140d208789a1c091220348100010903d2e80f4b2034821e26870348100010903d4e80f532020821e268702081000109000aa4006250350400013d002cb4013990092540b20478505c0b2900004140941a0250280f590, 0x28c41aa5a3020c4000129000a240050503d0100e22a0388280f6a00004440f6840004e40042d0030940d342034cc8002046856ada15a768568da158b000821a25ab68969da25a3001441aa5a76a968c094100004a400309, 0x68968c093146a56ada95a3028c51aa5a3020c5000129000a9400489001e140f6a00004b400c11034b080d2b2024c41a95ab6a562da958703da400012d024c880620432c2fda15ab68568da158b018820cb13f6896ada25a3, 0x790e5de438b790e1c0f69c0004440d3900004f4005210072b40b20468569da15a302d280001052ac8fc0f4a06a481c0f404000494002ad0148a80520a018a10ab0bf6856ada15a768562da15a3018a20ab13f6896ada25a7, 0x425053bb414edd053b303d8710c3bb430edc0e698798e4de638b0350700013d000cc408342020c980e208438edd0e3b30308210c3b70348200013102050808126035840001090012e40069900325401205034e41e439b, 0x590e5d6438b02cc210b3bb42cedd0b3b342ce5c0731469d6ada75a769d62c0f59c0004d4003a1001a4400c05000011e139b784e4de138b01c8100013d404eed013b7404ecd01397018a200814229c4fc0812601444806290, 0x454c800204404eed013b7404ecd013af020e400010501c810001210208100011d0018a400ba50046640261500cc240b3843ac2dd670a3584e6d6139759c24d6138b02ce410b3bb42cedc0a390000484eb23359c89d6439b, 0x1061e659379961c0b4040004f40f4040004b40041d0024a411342044cc811326001241a95ab6a568da959f6a561c0b2040004d40d2040004b4114ba0452c8005106a968daa59f6a961c0b2040004d40d2040004b41153a, 0x44b08112b2044aa8112a602c810cb0bf52c2dccb09f02ce614b3b7598e4c0f6ac00047400305034e61e6393798e1c0d3840004f40f6840004740042d0454e80838431c2fcc70af020e40c723f31c8bc0839800044400305, 0x788e1c0d3840004f40f684000474004ad0445081113a0444c8111260444580039459ca8d6539b594e4d65387018a41053bb414edd0538703ce1000121000eb40041479566de559379561c0b4040004f40f4040004b40049d, 0xb3883ac4dd6239b588e4d62387018821a25ab68968da258703d61000135000e740d388788e6de2393]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg28k2 : region H28 0x80081001100110010000900990089000 0x0 := regionTerm _ _ prog28k2 adj28 _ _ 20 (by decide +kernel)
def prog28k369 : Array Nat := #[0x4440f1840005040043500185400ab9041e1010346040cd810322014612037932bc68c104040004f4102c6040ad80820c2406fc9018702061000111000c540071903d01000141002aa4017b1008624036250118b40581d, 0x4586811616000611a11ab68468c0a40c0004140d61a0358580f40c0004d400545001e440d40c0395180e53e0394480f50c034b09aa1a36a861c0f40c0004d40a2c6028a48107a86a868daa187000830901bf24061c06184, 0x3c6200d342034cc804188000464003156886ada21a368861c0310420470c811bf2046cc041882406fc901b30404880f60c000504003850104e80411603d030001110020d400f450314808c1c32306fc8c1870206101162a, 0x48c4dc091220104580a4a0000424891c32246fc891b322461c0f48c6a46ada91a36a462da918703d0300013500104400a4503c621a21ab68868da218703c610001350445081113a0444c81111603c6200d2c2034ac805112, 0x5a062c0b50822c70c8b1bf22c6cc8b1a702c6206b13f5886ad621a7029231e359b78d65c0d58c0004f400309001644008a10038140d20c22470c891bf22461c0d184000444114ba0452c81149a0452581148a0106200413a, 0x40cecd0339701c6206713f38c4dce21b303ce31a71ab69c69c0f38c0004d400309001684008910038140122d02c6106b0bf5846ad611a758c28d6309358462c0b40c020d08cb1bf0208300011942c6cd681ab5a069d63417, 0xe30eb1b359c6ad671a759c68d6339b58ce5d6339359c62d6718701c610670bf38c2dce11b319c28ce309338462c0718840ceed033b740ce5c0a388000484871c321c6fc871b321c69c0618840ceed033b7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg28k369 : region H28 0x80081001100110010000900990099000 0x10000 := regionTerm _ _ prog28k369 adj28 _ _ 20 (by decide +kernel)
private theorem reg28k1 : region H28 0x80081001100110010000900990099000 0x0 := regionFork _ _ _ 16 reg28k2 reg28k369
def prog28k591 : Array Nat := #[0x3c2000014100108400609002aa40f200040d1810336040c8802080801e4c4f0370348000013d040518101220348009003f24001c0d08000044400309001c640f68400050400ab9005e940219500d8c40462d01607406f8d, 0x45228000804040ed200b7035000001050250680940a03da0000121001514007910350000e5460394f80e51203d000081424380dd0e00703da00001210385180e112041ee10e03743801c002002400fc9000701820000111, 0x20d080832601480000119000c250503b4140dd05007000200810432802fc810270008009003f040ad89002703d20000141000e140522a0148280f68000044400821003d140e6a422410c8903f22401c0d0800452e81149a, 0x148a80520a039ac00011523010c8c03f23009c8c00703d0010c03b4300dd0c01743001c0f680000484004110029140f2804140ed0503741401c0f080000484112c2044aa8112a6044a280f280020508081260144480f280, 0x18a01a05ab68169da05a368162c0b1002ac0fd65027580a8c0f58042c0ed0b03303d60000121000c54005b500224400e050208008c0432300fc8c007020200001110458a8116260458681161604582800200030ad9802a3, 0x21c09c0728029c0fce503b3940cc08380780e6de038b020e000013d000c54005910022d400e050048b40b0800ac0fc2b03758409d600a358405d6009302c4010b03b42c0dd0b0170356000012122c10c8b03f22c0cc8b027, 0x5e740b3803ac0eceb0373ac0cd67027580e6d67017580e4d6038b59c01c0708009c0fce103b3840dce103338405ce0093034e000d34231c0fc0d200000464ed03b3b40cda70273b405da038b020e008704321c0fc87033, 0x1840cc6102718028c0f18003d4e94303703d000001291bc10c6f0331bc09de301778062c0418040c0ed0303740c0cd030170106006904348c0dc69033010601a01ab68062c041800004d400325001684008bd0038140122d, 0x718019c10c6703f38c0ece303738c0cce302f19c09ce301738062ce300702c6006b0431ac0fc6b0335806ad6302758068d6301758062d6300700c200610431840fc23037]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg28k591 : region H28 0x80081001100110010000900990099008 0x8 := regionTerm _ _ prog28k591 adj28 _ _ 20 (by decide +kernel)
private theorem reg28k0 : region H28 0x80081001100110010000900990099008 0x0 := regionFork _ _ _ 3 reg28k1 reg28k591
private theorem safe28 : hostSafe H28 := regionHost _ _ _ bk28 reg28k0
def H29 : Array Nat := #[0x3, 0xc, 0xf, 0x10, 0x13, 0x20, 0x2c, 0x30, 0x3f, 0x40, 0x43, 0x4c, 0x4f, 0x50, 0x53, 0x60, 0x6c, 0x70, 0x7f]
def N29 : Array Nat := #[0x11001000110010001100100011000, 0x10001000900090001000100090008, 0x10001000100010001000100010000, 0x1001000090090000100100009008, 0x1001000010010000100100001000, 0x990090000000000099008, 0x900090000000000090008, 0x90090000000000009008, 0x10000000000000000, 0x8001100100099008, 0x1100100011000, 0x1000100090008, 0x1000100010000, 0x100100009008, 0x100100001000, 0x99008, 0x90008, 0x9008, 0x0]
private theorem bk29 : bookOK H29 N29 0x80011001000990098001100100099008 = true := by decide +kernel
private theorem adj29 : validRows H29 N29 := rows_of_book _ _ _ bk29
def prog29k2 : Array Nat := #[0x4440d3c2034ef80729003962805208388acce22ab388a9c0729000042407208000454004ad038f080e3be000820e22b3388abce22ab388a9c0729000042407208000454005390030d40520800047401299012c34077a1, 0x169407308035448ea327024c2000129034f080d3be01cc20ea327024c2000129038f080e3be028820ea32702482000129000ae4006350188200011d002c54013b10092b4092883a48bc0b2880004940d2320348a807288, 0x39820ce29303082000139000aa400525024e401013a0404a80731000042409398000504004150030d40c346030cf809288324aecc92b7324aacc9293028a20ca2bb328adcca293018a20ce2b7338a4c0d2080004e400329, 0x328a4c07314334aeccd293039640eb2b3018a400011d000ad4004a9001e940731000045400c0902cd180b33e035820cd2bb334aaccd2a701cc200011503584806288324aed8549f324aacc9293018a20ca2bb61547cca293, 0x3886bce21ab38869c0730c000424061880004740051100725406288324add65493034a400012559447c0d39033449c093900004d40029502c4e80b12a000c50c92bb324add6549f324aad65493000c50ca2bb328add6551f, 0x4a48b1c322c6fc8b19b03ce308f1c303d868106183b06acec18b0188300011d000cf40c2460308d8105082406fc9019b03d460ea18b03cc300011d0289180a23603cc2000129001304006b10032b401225018620e21b3, 0x2886bca21ab01ca30851c32146fc851af21466c0728c30caecc32b730caac0728c00046400391001a2400c2501c830e91b33a46ace918b0106200011d22470c891bf2246bc8919b0008300a2460288d96351f02d4280c588, 0x390f80918822470c891bf22466c8919701062000125024620001110248200010d0018e400bb50046c40262d00cca40728c2a46cca91af2a46ad2519b48ca4d2518b014620851c321466c0e1880004446513f28c4dca21b3, 0x1ca40ec2a73b0a2c09290000474093900004540040d0024e40c4460310f80c436018a20cd2bb334a9ccd293334a3c09288000464093080004540d4420350f806288338a9cce293338a3c09288000464093080004540e442, 0x2d1180b43e02d0e80b436024a21c549b61527d8548f01ca31c519b2b062c073140004340032501cc30ec1a73b062c0930c00047409398000434004150391080920c60d27d834970106218311f60c45c0c20c00042400325, 0x3a862c0930c00047409398000434004950291180a4420290f80a4360290b80728c2ac6ccab1a758ca4cab18b0316208b1c322c69c8b19b024e3000111000e54072903acacceb2a73aca2c09290000474093900004540048d, 0x728c2a86ccaa1a751466caa18b031420ca2bb328a9cca293024e5000119000e340730c3a86ccea1a7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg29k2 : region H29 0x80011001000990098001100100098000 0x0 := regionTerm _ _ prog29k2 adj29 _ _ 20 (by decide +kernel)
def prog29k369 : Array Nat := #[0x42409384000514004190018b400ac101c4101162204586811612000e122138b59c24c04104000474115a20456680410414429c5109f02481000109000cb400731024e4000145002ae4017bd0086a4036350118540580d, 0x3d0c80f42e000810c40bb23c29c073040004440f33203ccb80720400046400521001e2406204041c881071e041c280730402cd18ce0a733824c072040004640e5a20396281171c33829cce093000410510a714427c09384, 0x1cc100c346030cf80a1040004c40032d3282ecca0a732824c0410412431c490bf50527c001041442fc1151214427c0f384000514003a50285080a12e01c8100010900206400f2103dc404f0c713c29c4f09f0248100f43a, 0x68546c0d5120284b80e6900004a44d0c71342fc4d0a713427c073043342eccd0ab33429ccd09301c8100011900102400a2101cc10ca0bb32829cca093024e10001190291180a4420290f80a42e01cc100b34602ccf80b50a, 0x2902ac0628411431c450bf1142dc4509f018a10aa0bb2a82dd4509f018a10e12b3384abc0628400047400329001624008910038940610413431c4d0a713427c093040004240d4420350f80d4320350b80d42a0004100a142, 0x2046bc8119b0006106a0bf50c27d4119b01c610c30bb30c2dc07184000464003290016440088900389401215024a10a90bb2a42dca90ab49427d25093484a2c052040309198509f010410001312142fca40bb2902dca122f, 0x610650bf28c2eca30b72846cca11af28c2aca30a728c24ca118b020610690bf1a42ad2309f48466d2309348462c0310420470c811af20466c06184000444430c710c2fc430b710c27c0718420470c811bf]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg29k369 : region H29 0x80011001000990098001100100099000 0x1000 := regionTerm _ _ prog29k369 adj29 _ _ 20 (by decide +kernel)
private theorem reg29k1 : region H29 0x80011001000990098001100100099000 0x0 := regionFork _ _ _ 12 reg29k2 reg29k369
def prog29k591 : Array Nat := #[0x24e000014500104400629002ae4071000458881161a04584800380880e2d4701b0184000011d045488115120184005102714407c0930000042400329001cc40939800051400ac1005ed4021ad00d8f40461501603406f85, 0x350a80620021810ccd02701c800001190348c80d22a01cc00001110014840078901880010722041c781070a01c8000a24624009c9001b01cc00001110414881050a0460709002724006c0010014409c5101f024e0000109, 0x309180c23602c40000131000ca48b04322c09c8b01b018400490471240dd6049f000400510370456685101f034e0000145000e940b13a02c4a80730000042400811003c841069813411c4d02713407c093000351080d432, 0x2c4e80b12a041e600012d13c11c4f03713c09c4f01f01c8008f04323c0bc8f02723c06c07300000444004090028840720022c10c8b02722c06c093800004440b44602d0e80b43602d0a8072000289180a23602d42807200, 0x1ca00c02bb300adcc02ab300a4c002802ac0dd6501f580a4c0728021410c8503f01ca0000111000cb40059900222400e250104004f04713c09c4f01f0248000010903d0e80f43603d0c80f42e03d0a80010003d669e0593, 0x10c07c041801ac10c6b03f58c07c041803806cce01ab0106000011d000cb40058900226400e25004854082802a40dca902f49407d2501b480a4d2028b014400850432140bc8501b018a000011111411c4503f1140dc4501f, 0x5e340518019410c6503f28c0dca01b328c0bca01ab28c09c6501b28062c091801a410c6903f1a40bd2301f48c06d2018b0186000c34660c07c061000004c4660431980fcc30371980bcc01ab0106004304710c0fc43037, 0x48407d2101b48024c07080038f09c101b01c8000013909c11c2703f09c0dce102f3802ac0208020410c8103f2040bc8101b0082002d0470b40fda101b008200c00bb3002ac02080000464003350016440089d00389401215, 0x308008c11c610431840fc230371840bc600ab18409c2301f18406c61017014200250470940fca00bb2840dca102f2802aca102709407ca0093024200290470a40fc29037]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg29k591 : region H29 0x80011001000990098001100100099008 0x8 := regionTerm _ _ prog29k591 adj29 _ _ 20 (by decide +kernel)
private theorem reg29k0 : region H29 0x80011001000990098001100100099008 0x0 := regionFork _ _ _ 3 reg29k1 reg29k591
private theorem safe29 : hostSafe H29 := regionHost _ _ _ bk29 reg29k0
def H30 : Array Nat := #[0x3, 0xc, 0xf, 0x30, 0x33, 0x3c, 0x3f, 0x40, 0x43, 0x70, 0x73, 0x80, 0x8c, 0xb0, 0xbc, 0xc0, 0xcf, 0xf0, 0xff]
def N30 : Array Nat := #[0x1000000000001100100000000100100010000000000011001000000001000, 0x1000000000001000100000000000100090000000000090009000000000008, 0x1000000000001000100000000000100010000000000010001000000000000, 0x8001000000000000100100000000000000090000000000009008, 0x1000000000000100100000000000000010000000000001000, 0x1000000000000000100000000000000090000000000000008, 0x1000000000000000100000000000000010000000000000000, 0x100100000000100100000000000000009009000000009008, 0x100100000000100100000000000000001001000000001000, 0x100100000000000000000000000000009008, 0x100100000000000000000000000000001000, 0x90000000000099009000000009008, 0x90000000000090009000000000008, 0x90000000000009008, 0x90000000000000008, 0x9009000000009008, 0x1000000000000, 0x9008, 0x0]
private theorem bk30 : bookOK H30 N30 0x8001000000008001100100000000100100090000000000099009000000009008 = true := by decide +kernel
private theorem adj30 : validRows H30 N30 := rows_of_book _ _ _ bk30
def prog30k2 : Array Nat := #[0x4840f4ba03d2d80f5a0028a280a40878966de259378963c0f58c0004240f1880004b40049503d4e80f536001021e259b78965de259378963c0f5a00004240f4080004b4005290030940b4080004f4012b1012c74077c1, 0x16340c20879183c092220306200011103d2e80f4b6030821e460f0306200011103d4e80f536020821e460f02062000111000aa4006250310200013d002cb4013990092540b18878d05c0b2880004340941a0250480f588, 0x28c218a5a3020c2000129000a440050d03d0300e12a0384480f6200004240f60c0004e40042d0030940c346030cd80018860d6ad835a760d68d83593000821845ab61169d845a30014218a5a762968c094080004a400311, 0x61168c093146256ad895a3028c518a5a3020c5000129000a9400491001e340f6200004b400c09030b180c2b6024c21895ab62564d8958f03d8200012d024c880618832c6fd835ab60d68d83593018820cb23f6116ad845a3, 0x788e5de2393788e3c0f61c0004240c3880004f4005210072b40b18860d69d835a302d2800010d2ac4fc0f4a062443c0f40c000494002ad0144a805112018a30ab1bf60d6ad835a760d64d835a3018a40ab23f6116ad845a7, 0x445053bb414edd053b303da710d3bb434ecc0e618798e4de638b0310700013d000cd408346020c980e208438edd0e3b30348210d3b30308200013502091808226035820001110012e4006990032540120d030e21e239b, 0x588e5d6239302cc410b3bb42cedd0b3b342ce5c0731461d6ad875a761d64c0f59c0004c4003a1001a2400c0d000031e339b78ce4de338b01c6200013d40ceed033b740cecd03397018a400824629c8fc0822601482806288, 0x414d80018840ceed033b740cecd033af020e200010d01c620001210206200011d0018a400ba50046640261500cc440b38c3ac6cd671a358ce6d6339758ce4d6718b02ce210b3bb42cecc0a388000484eb13759c49d6239b, 0x1061e658f79962c0b40c0004f40f40c0004b40041d0024a410346040cd810326001221895ab62568d8959f62563c0b1880004c40c1880004b4104ba0412d80050862968d8a59f62963c0b1880004c40c1880004b41053a, 0x40b18102b6040aa8102a602c620cb1bf52c6cccb19f02ce614b3b3598e2c0f62c0004740030d030e61e638f798e2c0c38c0004f40f60c0004740042d0414e80838c31c6fcc71af020e20c713f31c4bc083980004240030d, 0x790e2c0c38c0004f40f60c000474004ad0409181023a0408d8102260408580039459ca8d6539b594e3d6538b018a21053bb414ecd0538f03ce3000121000eb40041479566de558f79562c0b40c0004f40f40c0004b40049d, 0xb3903ac8cd6439b590e3d6438b018821845ab61168d8458f03d63000131000e740c390790e6de438f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg30k2 : region H30 0x8001000000008001100100000000100100090000000000099009000000008000 0x0 := regionTerm _ _ prog30k2 adj30 _ _ 20 (by decide +kernel)
def prog30k369 : Array Nat := #[0x4240f1840005140043100185400ab903c41011342044cc8113220146122178b2bc28c081040004f4112c2044ac8081041442fc5108f02061000109000c540071903d03000145002aa4017b5008644036250118b40581d, 0x41a6810696000611830ab68468c0a4040004340d61a0358580f4040004c400541001e240c4040395080e53e0394280f504030b198a0a362823c0f4040004c40a2c2028a28117a862828d8a08f000410510bf14423c06184, 0x3c8100c346030cd804104000464003156102ad840a361023c0310410c31c811bf10c2dc001041442fc510b70448880f6840005140038d0104e80411603d010001090020c400f410354804d0c71342fc4d08f020610106aa, 0x4848cc092220104580a4a0000444490c71242fc490b712423c0f4846242ad890a362424d8908f03d0100013100102400a4103c811840ab61028d8408f03c610001310409181023a0408d81021603c8100c2c6030ad80520a, 0x5a024c0c58412c31c4b0bf12c2dc4b0a702c8108b0bf5902ad640a7029211e159b78565c0c5840004f400311001624008a10038340c10412431c490bf12423c0c184000424104ba0412d81049a041258104920004100413a, 0x404ecd0139701c810870bf3902dce123303ce11870ab61c29c0f3840004c400311001684008890038340122d02c6106b0bf58c2ad630a758c28d6309358462c0b404020d18cb0bf0204100011942c2dd680ab5a029d61417, 0xe10eb0b759c2ad670a759c28d6139b584e5d6709359c23d6138b01c610670bf38c2dce11b319c28ce309338462c07104404eed013b3404e5c0c384000484470c711c2fc470b711c29c06204404eed013b7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg30k369 : region H30 0x8001000000008001100100000000100100090000000000099009000000009000 0x1000 := regionTerm _ _ prog30k369 adj30 _ _ 20 (by decide +kernel)
private theorem reg30k1 : region H30 0x8001000000008001100100000000100100090000000000099009000000009000 0x0 := regionFork _ _ _ 12 reg30k2 reg30k369
def prog30k591 : Array Nat := #[0x3c6000014500108400611002aa40f100044d0811332044c8804180881e2c8f0330304000013d044908112220304005103f14403c0c18000042400311001c640f60c00051400ab9005e940219500d8d40462d01607406f85, 0x412480018040c0ed201b30310000010d0250680941203d80000121001504007890310000e5420394f80e50a03d000082464380cd0e00f03d800001210389080e20a045ee10e03343803c001001440fc5100f01860000109, 0x20d180832601440000119000c450503b4140cd0500f00c400430472806fc430270004005103f044ac85102703d20000145000e340512a0144480f60000042400821003d040e62412411c4903f12403c0c1800412e81049a, 0x144a805112039ac00011513411c4d03f13409c4d00f03d0010d03b4340cd0d01743403c0f600000484004090029040f2804140ed0503341403c0f180000484102c6040aa8102a6040a480f280020918082260148280f280, 0x18a01805ab60169d805a360164c0b2002ac0fd65027580a8c0f58042c0ed0b03703d60000121000c54005b100222400e0d0204004d0471340fc4d00f02060000109041aa8106a6041a6810696041a4800100034ac9a02a3, 0x11c09c0728029c0fce503b3940dc08380780e6de0393020e000013d000c54005890022c400e0d0048b40b1801ac0fc6b03358c09d601a358c05d6018b02c4010b03b42c0cd0b0170316000012112c11c4b03f12c0dc4b027, 0x5e740b3803ac0eceb0373ac0cd67027580e6d67017580e4d6700f580e2c0718019c0fce303b38c0dce303338c05ce018b030e000c34631c0fc0c100000464ec03b3b00dd870273b005d80393020e004704711c0fc47037, 0x1840cc2302718028c0f08003d4e94103303d000001290bc11c2f0370bc09de101778024c020804040ed010374040cd01017008200290470a40dd21033008201800ab60024c020800004c400325001684008bd0038340122d, 0x708009c11c2703f3840ece10373840cce102f09c09ce101738024ce100f02c2002b0470ac0fc2b0375802ad6102758028d6101758024d6100f00c200230471840fc23037]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg30k591 : region H30 0x8001000000008001100100000000100100090000000000099009000000009008 0x8 := regionTerm _ _ prog30k591 adj30 _ _ 20 (by decide +kernel)
private theorem reg30k0 : region H30 0x8001000000008001100100000000100100090000000000099009000000009008 0x0 := regionFork _ _ _ 3 reg30k1 reg30k591
private theorem safe30 : hostSafe H30 := regionHost _ _ _ bk30 reg30k0
def H31 : Array Nat := #[0x7, 0x8, 0xf, 0x10, 0x17, 0x18, 0x1f, 0x20, 0x27, 0x28, 0x2f, 0x40, 0x47, 0x50, 0x57, 0x60, 0x67, 0x78, 0x7f]
def N31 : Array Nat := #[0x1000001000100010000010101010100, 0x81008100810000008100810080, 0x1000100010000000100010000, 0x81000000810000818100008180, 0x1000000010000010100000100, 0x81000000810000008100000080, 0x1000000010000000100000000, 0x8100810000000081818180, 0x100010000000001010100, 0x8100810000000000810080, 0x100010000000000010000, 0x818181818180, 0x10101010100, 0x818100008180, 0x10100000100, 0x81818180, 0x1010100, 0x80, 0x0]
private theorem bk31 : bookOK H31 N31 0x81000081008100810000818181818180 = true := by decide +kernel
private theorem adj31 : validRows H31 N31 := rows_of_book _ _ _ bk31
def prog31k2 : Array Nat := #[0x4940f43a03d0c80f5a40288580a48078166de059778162c0f5940004040f2800004b40049103d4e80f532001251e559b79564de558b79560c0f5a40004540f4940004b4005290030840b4940004f4012b5012c74077c5, 0x16040d288789a0c08126034a000010903d0e80f432034a21e2683034a000010903d4e80f532024a21e2683024a0000109000aa4006210352500013d002cb4013990092440b28078124c0b2900004040941a0250280f594, 0x28c51aa5a7024c5000129000a240050103d2000e2aa038a280f6a40004540f6800004e40042d0030840d342034cc8002806816ada05a768168da058b000a21a25ab68969da25a3001451aa5a76a968c094140004a400309, 0x68968c083106a16ada85a7028c41aa5a7024c4000129000a8400489001e040f6a40004b400c150349080d232020c51a85ab6a162da858303da500012d020c980628032c0fda05ab68169da058b018a20cb13f6896ada25a7, 0x794e4de538b794e0c0f69c0004540d3940004f4005250072b40b20068169da05a302d280001012ac8fc0f4a06a0a0c0f480000484002ad0148a80520a0188008b03f6816ada05a368162da05a70188208b13f6896ada25a7, 0x425243bb490edd243b303d8712c3bb4b0edc0e698798e5de638b0352700013d000cc409342024c880e2884b8edd2e3b3030a212c3b7034a200013102450809122035850001090012e40069900324401201034e51e539b, 0x594e4d6538b02cc212b3bb4acedd2b3b34ace4c0731069d6ada75a369d62c0f59c0004d4003a5001a5400c01000001e039b780e5de038b01ca000013d480eed203b7480ecd203930188200914221c4fc0912201045806290, 0x454c800280480eed203b7480ecd203af024e500010101ca0000125024a000011d0018a400ba10046640261100cc240b3803ac0dd67027580e6d67017580e4d6038b02ce512b3bb4acedc0a394000494eb2b359ca8d6539b, 0x1261e659779960c0b4800004f40f4800004b40041d0024a411342044cc811322001051a85ab6a169da859f6a160c0b2800004d40d2800004b41143a0450c8005146a969daa59f6a960c0b2800004d40d2800004b41153a, 0x44908112320448a81122202ca00cb03f52c0dccb01f02ce614b3b7598e5c0f6ac00047400301034e61e6397798e0c0d3800004f40f6800004740042d0454e80938031c0fcc702f024e50c72bf31cabc0939800045400301, 0x788e0c0d3800004f40f680000474004ad0445081113a0444c8111220444480039059c89d6439b590e5d64383018a41243bb490edd2438303ce0000125000eb40049079166de459779160c0b4800004f40f4800004b40049d, 0xb3883ac4dd6239b588e5d62383018a21a25ab68969da258303d60000135000e740d388788e6de2397]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg31k2 : region H31 0x81000081008100810000818181808080 0x0 := regionTerm _ _ prog31k2 adj31 _ _ 20 (by decide +kernel)
def prog31k369 : Array Nat := #[0x4540f1800005040043500184400ab9041e0010346040cd8103260106020379723c69c104800004f4102460408d80928c2c06fcb018302460000115000c440071903d20000141002aa4017b1008624036210118b40581d, 0x4586811612000601a01ab68069c0a48c0004040d61a0358480f48c0004d400545001e540d48c0395180e53e0394580f50c034909aa1a76a860c0f48c0004d40a246028858107a86a869daa183000a30b01bf2c060c06180, 0x3c6200d342034cc805188000464003116886ada21a768860c0310028070ca01bf2806cc051882c06fcb01b30404980f60c000504003810144e80511203d230001150020d400f45031490ac1c32b06fcac1830246001162a, 0x40c4dc081260144480a4a0000424a81c32a06fca81b32a060c0f40c6a06ada81a76a062da818303d2300013500105400a4503c621a21ab68869da218303c600001350445081113a0444c81111203c6200d2420348c804116, 0x5a462c0b5082ac70cab1bf2ac6ccab1a302c6206b13f5886ad621a3029031e359b78d64c0d58c0004f400309001654008a50038040d28c2a070ca81bf2a060c0d1800004541143a0450c81141a0450481140a0146200513a, 0x48cecd2339301c6206713f38c4dce21b303ce31a71ab69c68c0f38c0004d400309001694008950038040122d02c6006b03f5806ad6302758068d6301758062c0b48c024d08cb1bf024a30001194ac6cd691ab5a468d63493, 0xe30eb1b359c6ad671a759c68d6339b58ce5d6339359c62d6718301c6006703f38c0dce01b319c09ce301738062c0718848ceed233b748ce4c0a388000494a71c329c6fca71b329c68c0618848ceed233b7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg31k369 : region H31 0x81000081008100810000818181818080 0x10000 := regionTerm _ _ prog31k369 adj31 _ _ 20 (by decide +kernel)
private theorem reg31k1 : region H31 0x81000081008100810000818181818080 0x0 := regionFork _ _ _ 16 reg31k2 reg31k369
def prog31k591 : Array Nat := #[0x3c2000014100109400609002aa410780040d1810336040c9802080805e5c4f0b7041a000013d04051810126034a10b00bf2c020c0d08000045400309001c640f68000050400ab9005e840219100d8c40462d01607406f8d, 0x45028000804802ed200b7035210001010250680940a03da1000125001514007950352100e5460394f80e51603d210091424b82dd2e08303da10001250385180e116041ee12e0b74b820c002842c02fcb008301820000115, 0x24d080932201481000119000c25240bb4902dd24083000200a00c32802fca00a3000a10b00bf0408d8b00a303d01000141000e040522a0148280f68400045400825003d140e6a02a030ca80bf2a020c0d0800450e81141a, 0x148a80520a039ac0001112b030cac0bf2b028cac08303d2112c0bb4b02dd2c0934b020c0f684000494004150029140f2044902ed240b749020c0f080000494112420448a8112220448280f204024508091220104580f204, 0x18811a15ab68569da15a368562c0b10422c2fd6122759028c0f5844ac2ed2b0b303d61000125000c44005b500225400e01024a10ac0c32b02fcac083024200001150458a81162204586811612045828002840308d981227, 0x29c28c0720421c2fce40bb3902cc09384784e6de138b024e100013d000c44005950022d400e010048b40b0800ac0fc2b03758409d600a358405d6009302c4112b0bb4ac2dd2b093035610001252ac30cab0bf2ac2ccab0a3, 0x5e740b3843ac2eceb0b73ac2cd670a3584e6d6139759c24d6138b59c20c0708009c0fce00bb3840dce00b338405ce0093034e100d34231c2fc0d284000464ed0bb3b42cda70a33b424da138b024e10a70c329c2fca70b3, 0x1802cc6102718028c0f18403d4e9430b703d210001291bc30c6f0b31bc28de309378462c0518448c2ed230b748c2cd23093014610680c340c2dc680b3014611a11ab68462c051840004d400321001694008bd0038040122d, 0x718419c30c670bf38c2ece30b738c2cce30af19c28ce309338462ce308302c6106b0c31ac2fc6b0b35846ad611a758c28d6309358462d6308300c200600c31840fc23037]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg31k591 : region H31 0x81000081008100810000818181818180 0x100 := regionTerm _ _ prog31k591 adj31 _ _ 20 (by decide +kernel)
private theorem reg31k0 : region H31 0x81000081008100810000818181818180 0x0 := regionFork _ _ _ 8 reg31k1 reg31k591
private theorem safe31 : hostSafe H31 := regionHost _ _ _ bk31 reg31k0
def H32 : Array Nat := #[0xf, 0x10, 0x1f, 0x20, 0x2f, 0x30, 0x3f, 0x40, 0x4f, 0x50, 0x5f, 0x80, 0x8f, 0xa0, 0xaf, 0xc0, 0xcf, 0xf0, 0xff]
def N32 : Array Nat := #[0x1000000000001000000010000000100000000000100010001000100010000, 0x8001000080010000800100000000000080010000800100008000, 0x1000000010000000100000000000000010000000100000000, 0x8001000000000000800100000000800180010000000080018000, 0x1000000000000000100000000000100010000000000010000, 0x8001000000000000800100000000000080010000000000008000, 0x1000000000000000100000000000000010000000000000000, 0x80010000800100000000000000008001800180018000, 0x10000000100000000000000000001000100010000, 0x80010000800100000000000000000000800100008000, 0x10000000100000000000000000000000100000000, 0x800180018001800180018000, 0x100010001000100010000, 0x800180010000000080018000, 0x100010000000000010000, 0x8001800180018000, 0x1000100010000, 0x8000, 0x0]
private theorem bk32 : bookOK H32 N32 0x8001000000008001000080010000800100000000800180018001800180018000 = true := by decide +kernel
private theorem adj32 : validRows H32 N32 := rows_of_book _ _ _ bk32
def prog32k2 : Array Nat := #[0x4940f43a03d0c80f5a40288580a48078166de059778162c0f5940004040f2800004b40049103d4e80f532001251e559b79564de558b79560c0f5a40004540f4940004b4005290030840b4940004f4012b5012c74077c5, 0x16040d288789a0c08126034a000010903d0e80f432034a21e2683034a000010903d4e80f532024a21e2683024a0000109000aa4006210352500013d002cb4013990092440b28078124c0b2900004040941a0250280f594, 0x28c51aa5a7024c5000129000a240050103d2000e2aa038a280f6a40004540f6800004e40042d0030840d342034cc8002806816ada05a768168da058b000a21a25ab68969da25a3001451aa5a76a968c094140004a400309, 0x68968c083106a16ada85a7028c41aa5a7024c4000129000a8400489001e040f6a40004b400c150349080d232020c51a85ab6a162da858303da500012d020c980628032c0fda05ab68169da058b018a20cb13f6896ada25a7, 0x794e4de538b794e0c0f69c0004540d3940004f4005250072b40b20068169da05a302d280001012ac8fc0f4a06a0a0c0f480000484002ad0148a80520a0188008b03f6816ada05a368162da05a70188208b13f6896ada25a7, 0x425243bb490edd243b303d8712c3bb4b0edc0e698798e5de638b0352700013d000cc409342024c880e2884b8edd2e3b3030a212c3b7034a200013102450809122035850001090012e40069900324401201034e51e539b, 0x594e4d6538b02cc212b3bb4acedd2b3b34ace4c0731069d6ada75a369d62c0f59c0004d4003a5001a5400c01000001e039b780e5de038b01ca000013d480eed203b7480ecd203930188200914221c4fc0912201045806290, 0x454c800280480eed203b7480ecd203af024e500010101ca0000125024a000011d0018a400ba10046640261100cc240b3803ac0dd67027580e6d67017580e4d6038b02ce512b3bb4acedc0a394000494eb2b359ca8d6539b, 0x1261e659779960c0b4800004f40f4800004b40041d0024a411342044cc811322001051a85ab6a169da859f6a160c0b2800004d40d2800004b41143a0450c8005146a969daa59f6a960c0b2800004d40d2800004b41153a, 0x44908112320448a81122202ca00cb03f52c0dccb01f02ce614b3b7598e5c0f6ac00047400301034e61e6397798e0c0d3800004f40f6800004740042d0454e80938031c0fcc702f024e50c72bf31cabc0939800045400301, 0x788e0c0d3800004f40f680000474004ad0445081113a0444c8111220444480039059c89d6439b590e5d64383018a41243bb490edd2438303ce0000125000eb40049079166de459779160c0b4800004f40f4800004b40049d, 0xb3883ac4dd6239b588e5d62383018a21a25ab68969da258303d60000135000e740d388788e6de2397]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg32k2 : region H32 0x8001000000008001000080010000800100000000800180018001800080008000 0x0 := regionTerm _ _ prog32k2 adj32 _ _ 20 (by decide +kernel)
def prog32k369 : Array Nat := #[0x4540f1800005040043500184400ab9041e0010346040cd8103260106020379723c69c104800004f4102460408d80928c2c06fcb018302460000115000c440071903d20000141002aa4017b1008624036210118b40581d, 0x4586811612000601a01ab68069c0a48c0004040d61a0358480f48c0004d400545001e540d48c0395180e53e0394580f50c034909aa1a76a860c0f48c0004d40a246028858107a86a869daa183000a30b01bf2c060c06180, 0x3c6200d342034cc805188000464003116886ada21a768860c0310028070ca01bf2806cc051882c06fcb01b30404980f60c000504003810144e80511203d230001150020d400f45031490ac1c32b06fcac1830246001162a, 0x40c4dc081260144480a4a0000424a81c32a06fca81b32a060c0f40c6a06ada81a76a062da818303d2300013500105400a4503c621a21ab68869da218303c600001350445081113a0444c81111203c6200d2420348c804116, 0x5a462c0b5082ac70cab1bf2ac6ccab1a302c6206b13f5886ad621a3029031e359b78d64c0d58c0004f400309001654008a50038040d28c2a070ca81bf2a060c0d1800004541143a0450c81141a0450481140a0146200513a, 0x48cecd2339301c6206713f38c4dce21b303ce31a71ab69c68c0f38c0004d400309001694008950038040122d02c6006b03f5806ad6302758068d6301758062c0b48c024d08cb1bf024a30001194ac6cd691ab5a468d63493, 0xe30eb1b359c6ad671a759c68d6339b58ce5d6339359c62d6718301c6006703f38c0dce01b319c09ce301738062c0718848ceed233b748ce4c0a388000494a71c329c6fca71b329c68c0618848ceed233b7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg32k369 : region H32 0x8001000000008001000080010000800100000000800180018001800180008000 0x100000000 := regionTerm _ _ prog32k369 adj32 _ _ 20 (by decide +kernel)
private theorem reg32k1 : region H32 0x8001000000008001000080010000800100000000800180018001800180008000 0x0 := regionFork _ _ _ 32 reg32k2 reg32k369
def prog32k591 : Array Nat := #[0x3c2000014100109400609002aa410780040d1810336040c9802080805e5c4f0b7041a000013d04051810126034a10b00bf2c020c0d08000045400309001c640f68000050400ab9005e840219100d8c40462d01607406f8d, 0x45028000804802ed200b7035210001010250680940a03da1000125001514007950352100e5460394f80e51603d210091424b82dd2e08303da10001250385180e116041ee12e0b74b820c002842c02fcb008301820000115, 0x24d080932201481000119000c25240bb4902dd24083000200a00c32802fca00a3000a10b00bf0408d8b00a303d01000141000e040522a0148280f68400045400825003d140e6a02a030ca80bf2a020c0d0800450e81141a, 0x148a80520a039ac0001112b030cac0bf2b028cac08303d2112c0bb4b02dd2c0934b020c0f684000494004150029140f2044902ed240b749020c0f080000494112420448a8112220448280f204024508091220104580f204, 0x18811a15ab68569da15a368562c0b10422c2fd6122759028c0f5844ac2ed2b0b303d61000125000c44005b500225400e01024a10ac0c32b02fcac083024200001150458a81162204586811612045828002840308d981227, 0x29c28c0720421c2fce40bb3902cc09384784e6de138b024e100013d000c44005950022d400e010048b40b0800ac0fc2b03758409d600a358405d6009302c4112b0bb4ac2dd2b093035610001252ac30cab0bf2ac2ccab0a3, 0x5e740b3843ac2eceb0b73ac2cd670a3584e6d6139759c24d6138b59c20c0708009c0fce00bb3840dce00b338405ce0093034e100d34231c2fc0d284000464ed0bb3b42cda70a33b424da138b024e10a70c329c2fca70b3, 0x1802cc6102718028c0f18403d4e9430b703d210001291bc30c6f0b31bc28de309378462c0518448c2ed230b748c2cd23093014610680c340c2dc680b3014611a11ab68462c051840004d400321001694008bd0038040122d, 0x718419c30c670bf38c2ece30b738c2cce30af19c28ce309338462ce308302c6106b0c31ac2fc6b0b35846ad611a758c28d6309358462d6308300c200600c31840fc23037]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg32k591 : region H32 0x8001000000008001000080010000800100000000800180018001800180018000 0x10000 := regionTerm _ _ prog32k591 adj32 _ _ 20 (by decide +kernel)
private theorem reg32k0 : region H32 0x8001000000008001000080010000800100000000800180018001800180018000 0x0 := regionFork _ _ _ 16 reg32k1 reg32k591
private theorem safe32 : hostSafe H32 := regionHost _ _ _ bk32 reg32k0
def H33 : Array Nat := #[0x1, 0x2, 0x4, 0x5, 0x6, 0x7, 0x8, 0xc, 0x10, 0x11, 0x18, 0x1d, 0x20, 0x22, 0x28, 0x2e, 0x30, 0x32, 0x38, 0x3f]
def N33 : Array Nat := #[0x105410501011154, 0x101010121031132, 0x105010501030106, 0x105010501010104, 0x101010101030102, 0x101010101010100, 0x50005000300f6, 0x5000500030006, 0x4105000011f6, 0x410500001154, 0x5000000f6, 0x500000004, 0x210311f6, 0x21031132, 0x300f6, 0x30002, 0x11f6, 0x1132, 0xf6, 0x0]
private theorem bk33 : bookOK H33 N33 0x81054105210311f6 = true := by decide +kernel
private theorem adj33 : validRows H33 N33 := rows_of_book _ _ _ bk33
def prog33k4 : Array Nat := #[0x416f8105ba01cc50f03373c0cccf0327024c500011d024e50001190012b400f29000c51a662f6998ada662769987c004946a58bda962b6a587c0d614000494003990312500013503525000131002304022c500d0440620d, 0x6a987c0c3940004d40039901cc50f03373c0c9c0d3140004740d394000464004310414f81053a02d2620661f81985d6c33702d272076175b0edc0b4940004740031901cc50f03373c0c9c0d3140004740d39400046400431, 0x456f8115ba0456580a49889927c0a49c0004641149601cc50f13433c4cdcf1333028c500011d028e50001190012941153e0454e80939804525807314000494002a9002cb40c49881987d4c33781985c005146a98bdaa627, 0x4988ed243374988cc004904b08ed8922b61127c093905112dc093900004a4002b100146407310510cdd44333028e400011901cc400012900109400c2d006054003983c4d0cf13373c4cccf13270358600011d03587000119, 0x49a9000139000b04004c5001aa400bb10042640d61081187e0461b0352420449f81126c10690000494003310416f8105ba02d2412c23b5b12dd8922b61127d8921b03584000125035240001310017040b246045240c9243, 0x514a624b29890ca623b2988cca622b01ca40112ae044a980d624000514ac24b2b090cac23b2b08ac0a3900454f8112ae044a980d524000514aa24b2a890caa23b01ca40112ae044a98106a42c092cb023b039a90ae24b, 0x4e40938c000444003b500145400829003eb40e6a423872c8e1ab039a90ae1cb2b86ac0d48c000454003110352324351790d44c0d524000524126a40004a40043900251401b9900a304039b101cc40112ae044a980d498, 0x4d4003950022440d38c0456f8115ba04565811592028e30aa1cb044a980a20c88da7daa22701c8300013522872c0d38c000444004950454f81153a038e30ae1cb048e3000139044a980920c88da7c1172423872c128a4, 0x41a40001450416f81048c0004b4004c9001a74008a9002ce400e19034c30cd1c769889c114980004d4861cb2186ec861ab044a30d11b7044ab8112a60352600014529872ca61bb2986ac0d30c33471da61ab68cc9c1148c, 0x31230ec1c73b070c0c48c0004740033500185400b910044641048c34071cd01b780cc5e03313024e301072e041caa0371780dc4c0d38c0414fa0351780d44c128243c071cf01b702d2324381790e04c0b48c04565811592, 0x33071ccc1c33306dd861ab60cc9d8331760cc4c0520c68d8bda362768d87c116240004d48c1cb23070c8c1bb2306ac0028c68d8bda362768d87c116240004d4ac1cb2b070cac1bb2b06ac0000c68d8bda362b68d89da361f, 0xc30c]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg33k4 : region H33 0x81054105210211e0 0x0 := regionTerm _ _ prog33k4 adj33 _ _ 21 (by decide +kernel)
def prog33k357 : Array Nat := #[0x4bd0dd2f41f034e500013d000ce40d3940414f81053a034e501153e0454e80d4140005140034102d070115be0456e811596034e50105be0416e80d41400050400345020e500012d001aa400ba500443401c1100c464041b1, 0x20e400012d0014a4006a500265400f8d020a30112ae044a9a2341f035280001452a072ca81c32a06eca81ab025030e81c73a070ce81b703da310d1bb6a06ac0940c0004d40031d001654094144b90fd2e4374b907c09414, 0x49107c116a0000494881cb22070c881bb2206ac00290024b192443f4910dd2441f02d070001252a092ca82432a08eca822b0000412443f4910ed2443749107c083905110dc0b4100416f8105ba81107c0d4100005040b246, 0x4186ed061b740cc5d03313045040c82434188ed0433732089d04317000c512643f4990ed2643749907c11414320b0d062bb414cdc083983a0d1ce83433a0cdc0d41800047400395001894009110032340520c4910fd24437, 0x62089d8441f62086d844170310512c43f4b10ed2c4374b107d2c41b001051a862f6a18ada861f6a186c0b414430aed882ab61507d8829b0310618641f03107000119000a54005b500229400c110040340940c32071cc81c3, 0xf60c4306ed0c1b76206ad8341f62066d8341760d04c0b4104308ed8822b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg33k357 : region H33 0x81054105210311e0 0x10000 := regionTerm _ _ prog33k357 adj33 _ _ 21 (by decide +kernel)
private theorem reg33k3 : region H33 0x81054105210311e0 0x0 := regionFork _ _ _ 16 reg33k4 reg33k357
def prog33k528 : Array Nat := #[0x456f8115ba045658115920452207114b1c44ec711370248222249f045258128b83c44dc05208000474002a50012340072d03522242717909c4e4270f039a9000149049a9000139001314010a900770402e9900fcc405521, 0x2a4400d8d0352200e54670945dc251370943c0d3880454f80d4880005164251790944e4250f0000222249f045259424b750924c116a80004941153e88943c0d524000514006490028e40b488889a7e2268f01c62000135, 0x3234104881c052c701471c04ec701371c04ac1183424052c9013b2404ac9012701ca20f01473c04dcf0127034a200b2c60416f8092880004b40031d2c052cb013b2c04ac003883c051cf01373c049c0d48800047400395, 0x44640930819852c6614719850c6613b1984dc6612b045a608614b21850c8613b2184ac8612701cc20d01473404dcd0127808c5c0928832451d2613b4984dc1169829852ca613b2984ac11688000454003a500190400911, 0x1b052c6c1471b050c6c13b1b04dc6c12b045ac08c14b23050c8c13b2304ac8c127000a21a262f6898ada262768987c116242b052cac1432b04ecac12b030e20ec1473b050cec1270312200011d000e54006b500264400d0d, 0xa212243f4890ed2243748907c116a02a052ca81432a04eca812b020e20e81473a050ce81370350200011d000e54006a500264400d0d00446401631030c20cc14733050ccc1376184ad86127608c5d82313608c3c0c488, 0x2d0210c13b4304dd8812b62049d8241f62046d8241760904d8240f020c20c814732050d0613b4184dcc8127408c5d02313408c3c094081a052c681471a050c6813b1a04dc6812b045a808814b22050c8813b2204ac88127]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg33k528 : region H33 0x81054105210311f0 0x10 := regionTerm _ _ prog33k528 adj33 _ _ 21 (by decide +kernel)
private theorem reg33k2 : region H33 0x81054105210311f0 0x0 := regionFork _ _ _ 4 reg33k3 reg33k528
def prog33k752 : Array Nat := #[0x18d4008b90006122309f5846dc0b384000434115be0456e8115960456481272c6ac27dab08f049c1000135000d141270438471ce11b7049c300011d049c700010d0010b400c25006504026a900e4c404a2101886407e09, 0x5852dc1058c000494105be0412300012d001274006c9002ae409284039719614b7024a100012d4b827dc149372423c124846a42bda909f6a423c1148422432c1122e0246122309f024e100010d000a441149604921000145, 0x448b88a0a7045410112ae044a9807184000454003110454f80a484000514006c90024d400c39003d0409384041cba01717805c4e0170f034e10105be024e100012d90605e4181390603c1059c3c029e0708f01461201493, 0x62427c0c59c2b032cac0c32b02ec0b384000454003a50018a4009110032340d3840414f81053a80545e0151380543c0d484039519c151770544dc150f049411aa0af6a829daa09f6a823c0938490545e4151390543c11504, 0x6a02bda80ab6a027c083840004d400395001a9400991003434013310306106c0cb1b030c6c0bb60c2bd830ab60c29d8309f0316708c0cb23030c8c0bb2302ac8c0a70014118a0af62829d8a09f60545c092844b02ed890af, 0x62027d8141760504d8808f0146112143f48504c08184000494680cb1a030d030bb4046dc680ab40c27c0b41c22032c880c32202ec880ab22029c002844850fd2143b4850dd2141f02d070a80cb2a030ca80bb2a02ac00404, 0x21832c860c32182ec860ab21829c00284384d1ce1343384cdce132702d260a60cb29830ca60bb2982ac003046982bda60ab69829c093040004d400395001a7400991003434011b1005a84004044302ed880af6202ad880a7, 0x390401219005cc401ca1020c10c80c34182ed013374182ccc80a741827d01317404c4d0608f000c10cc0c36182bd860ab61829d8609f604c5d8131361823c0618419832cc11c730c30c660bb3046dc660ab30c29c0b398, 0x1402ec500ab14029e0209f80823c1150412832c4a0bb5044dc4a0a750823c1148412432d220bb4844dd2209f0000106114b18451c6113b1844dc1270438451ce11370396204e0cb04962000139000a740048d001e9400aa9, 0x20410480cb12030d020bb4044dd020b31202ac480a740827d0209b40823c0c10413032c4c0c31302ed820af6082ad820a760827d8209b60823c0610411832cc114730830c460bb3044dc460ab30829cc208f041620500cb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg33k752 : region H33 0x81054105210311f4 0x4 := regionTerm _ _ prog33k752 adj33 _ _ 21 (by decide +kernel)
private theorem reg33k1 : region H33 0x81054105210311f4 0x0 := regionFork _ _ _ 2 reg33k2 reg33k752
def prog33k1073 : Array Nat := #[0x4541153e88143c041804900fd2401f0452007104b024e000010d000a441149604a200001250018a400a2d024e024051790144e4050f029200001490492000012900131401135006d0402c3900f0c4050a101a86408a89, 0x3520000115001474009910038340d28003d519e06a7034a000013d6a807d4d01368143c128b44b40fd2d01f4b404c12580881a7e2068f049a0000145000c94005a901c600115be04565811592028e00aa04b044a9807200, 0xc94005c100204400c8d0412007004b1c011c700371c00ac052004900fd240370416000012524012c9002b81007c07280041eb8107aa780e9c072800004f4f00473c00dc0d28002cb18105be024a000012d2c012cb002b, 0x4940039500247400c910042340e4801b812c6e0471b810c6e0371b80ac0e380045cb80e6800005148e04b23810c8e02b70089c09380041cb81072a801c5c092804b80fd2e0374b807c07280045cb81172a034a0000145, 0x1b010c6c03b1b00dc6c02b0316008c04b23010c8c03b6100ad8022761007c0c2803b011cec0433b00dd8702b600e9c0c280024b192c03f4b00dc0b280000494ac04b2b010cac03b2b00ac0c4804b00fd2c03b4b00dc0b500, 0x1a00ec680371a00ac072803a011ce804341c0fd0703b41c0dc08280044ab8112a603da80001452a012ca80432a00eca802b0350010d03f4340eda802b02500000135000e540089d003034010110052c40c4801b012c6c047, 0x380d1ce0343380c9c09300000474003950024d400c8d00424401531006a840c4004300fd0c03b4300dd8802b62007d8041762004d8040f0450408804b22010d0403f4100ed040372200ad0401f0250006804b1a011c68043, 0x186008604b31011cc40432180ecc40372180acc0227024c006604b19811c660431980ec660371980ac0d28033411ccd0436980ada032769807c06280024b192603f49807c11280000494a604b29810ca603b2980ac00000, 0x48807d2201304a20000125000ea4006350026e400dc1004864017310074840030032011cc80434180fd0603b4180dd0603341807d0031741804d0030f02cc00cc04733010ccc0376180ad8032761807d8031761804d8030f, 0x1180ecc20371180acc012730804c1048014012c500471400ec500371400ae0201f80804c0e10013812c4e0471380dc4e02b70049dc20130344004d04b13411da202b68049da201f0292004a04b12811d4201304a2212203f, 0x810012012c4804712010d0203f4080ed020374080cc4802b40807d0201b40804c0c10013012c4c04713010c4c03b1300dd8202b60049d8201f60806d820130184004604b30811cc2043]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg33k1073 : region H33 0x81054105210311f2 0x2 := regionTerm _ _ prog33k1073 adj33 _ _ 21 (by decide +kernel)
def prog33k1420 : Array Nat := #[0x2002704b38411ce10433840dce00a70242006104b18411c610431840dc0b08020032c800c320029c050804840fd21037014201610370142000012d000a9400491001c3400a1d0036e4011a900602401d31008c8402999, 0x60407d8101360023d8100b0002004104b10411c410431040ec410371040ac400a708807c0508003d519e00a70142000013d0a812c2a0430a80ed410370a807d4101350023c0e5800b812c2e04370029c2e01f70404dc008f, 0x9812cc104730410c2603b3040dcc10330980acc00a730408c2601f30404cc008f30402c050800a012c280434040fd0103b4040dd010330a00ad0101f40404d0008f40402c050800b012c2c0430b00ed800af6040ad800a7, 0x5080]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg33k1420 : region H33 0x81054105210311f6 0x6 := regionTerm _ _ prog33k1420 adj33 _ _ 21 (by decide +kernel)
private theorem reg33k1072 : region H33 0x81054105210311f6 0x2 := regionFork _ _ _ 2 reg33k1073 reg33k1420
private theorem reg33k0 : region H33 0x81054105210311f6 0x0 := regionFork _ _ _ 1 reg33k1 reg33k1072
private theorem safe33 : hostSafe H33 := regionHost _ _ _ bk33 reg33k0
def H34 : Array Nat := #[0x3, 0x4, 0x7, 0x8, 0x10, 0x13, 0x20, 0x23, 0x28, 0x2b, 0x30, 0x33, 0x40, 0x44, 0x48, 0x4c, 0x50, 0x57, 0x78, 0x7f]
def N34 : Array Nat := #[0x1000000000111110001010100010110, 0x1000000000101010009090900090108, 0x1000000000101010001010100010100, 0x8100110009000900090098, 0x11110000090900000198, 0x11110000010100000110, 0x8111110000000000090198, 0x111110000000000010110, 0x8100110000000000090098, 0x100110000000000010010, 0x11110000000000000198, 0x11110000000000000110, 0x9090900090198, 0x9090900090108, 0x9000900090098, 0x9000900090008, 0x90900000198, 0x10100000100, 0x98, 0x0]
private theorem bk34 : bookOK H34 N34 0x81000000008111110009090900090198 = true := by decide +kernel
private theorem adj34 : validRows H34 N34 := rows_of_book _ _ _ bk34
def prog34k4 : Array Nat := #[0x538adc0e4085b8afd6e2b7020a200012d000ca408288795abde56ab0350200013d03d020001350010e40d4085b54fd6d53b0390216e53f03d02000139000ad40a4080004b40b4080004a400695003e4401a2501147407999, 0x356a12d44302d490001210416a000135000e440098900565402545020821c46af711aadc4697020821e46af791aade46970350200013d000ee408208791cbde472b791c5c0e4080004f40f4080004e4004b50390214e2bf, 0x248200012d6904ada92230388200013549050c0d5884b510da812b0352216d53b0292200012d02d22000129000e84107080004d4006910244f80b51049110d244370352414d23f5348ec0b4900004a40f7240004d400421, 0x3d240af23b2bc8dcaf2230416516f2bb5bcadc094140004b40031103d2280520849110ca823b4910dc0d4882b48ec0e4880004d4002a1039a812d443041c8000135041cd000121000e44008bd024b28092aa0348216d23b, 0x2ce22076a781da8c0d3885b4efd6d3bb034e200012d000d0400529040e21e772f79dcac107080004f4107880004e400435002c44013c50096540820849110d2443703522000121041a8000111045328114be0452e8114aa, 0x5b4efd6d3bb041c816e3bf041e8000139000ad4083880004b400591003494113ca044ea80d3883b48fced23b69c89da722303dc720722781c88e0720b038e40ee23f71c82c0f2080004e4003410016d410688534efd4d3bb, 0x81c88e0720b03d04000141041e80001110012e400a3501cb28072aa020821243c3490edc106a0000444114be0452e80d3883b48fced23b69c88c0e41c3b88fdc720b02ce420722381c82c0f410000504003390014d4106a0, 0x41e60092ca024aa80f308000494003210014741078800045400a450048e401e9100b2d40d38869c89da7223041a80001113b4afced2bb038a20ee1432b848cee113041c40ae223041c8000111000a24ee2bf03ce4207227, 0x390600011d045c981071400051400509001ef40f418444d0d11317444c2c10308045328114be0452a810798044f28113aa03cc200011d000c94005a103cc5105343414c2c10798000484072ca01caa80f314414d0d0530b, 0x410c5d0430b03d261e621f790c5ccf20b018a420622781887e0620b01882000141000ef4006210024e40941803d3180f48a020c2000125799cbde672b799c7de6717045c20ce1437184adc2317045c50113ca044ea8ee343, 0x24c2000121799abde66ab799a7de6697034e610d347434d0d0d317434c2c0d308819a9e0669f034c2000141000c840063d002ee401111038c400e4c6490d0c0e418000494ce23f71887dc431771882c0f310410d1d04343, 0x34c40cd23f3348eda622769888da621f690c5ccd20b0250610d347434d0d0d30b024c2000121719abdc66ab719a7dc66970250610d347434d0d0d30b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg34k4 : region H34 0x81000000008111100009090900090080 0x0 := regionTerm _ _ prog34k4 adj34 _ _ 21 (by decide +kernel)
def prog34k378 : Array Nat := #[0x14810c52023041e8000149000ca4107a001cb28072aa041e80092ca024aa80f4000004940031d041000114ca0452f8114aa041e80113ca044ea80f40000047400325041e0000145001a5400b890044d401c3900c44404199, 0x41c0000145001454006890026f400fb50250000f4c64b410c0f48a02040000125781abde06ab781a7de0697049a810d0436a00ada0417034402006a7801a7c0d100000504003210016f40f10012812c4a04312808c0f100, 0x13808c09400000425c06af701aadc069f701a5c0010013812c4e04303c4984e02302500000109781cbde072b781c7de07170384004e04b13810c4e02b13808c107002b808c0e400044f28113aa3b810c0e40000047411726, 0x6900ada022769008da021f0392008e03f7100ac8e02370087dc020b03c8004404b11010c4402b11008c0f4807900ac8f02378087c0000080089e0022380087c08200000504003bd001824009390032d40910013812c4e043, 0x7180adc031771804dc030b03cc004604b11810c4602b11808c4601303cc0100347400d0d00317400c4c0f30033c10de602b780c5de6013018800c4043040c0000111000af4005a100222400c390040d40d1002340fc8d03b, 0x1269833410ccd03f3340eda602b69808da031769804c1170033810cce03f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg34k378 : region H34 0x81000000008111100009090900090088 0x8 := regionTerm _ _ prog34k378 adj34 _ _ 21 (by decide +kernel)
private theorem reg34k3 : region H34 0x81000000008111100009090900090088 0x0 := regionFork _ _ _ 3 reg34k4 reg34k378
def prog34k549 : Array Nat := #[0x45328114be0452e8114aa001221a962f6a58ada96230398212c1430244f80c5a84b110c0b524000484002890012d4007450310216c53f5b14ed6c5370290200012d02d020001290012940109500767402f9101006405601, 0x2ee400eb50310214c2bf530aed4c2b7028a9810620024b280c4080004956c2bf5b0aed6c2b7024a212c1430244f8ac13b2b048c09414000424092ca4b0adc082880004940062d0028a40c4084b110d2c43702d22000121, 0x69d8bda762b69d89da762369d85c0941c71d8bdc762b71d85dc760b041880072ca3b0afc072aa02d4720762781d88e0760b030e200a3c6530efc0941c03d3180f48a020e200012579d8bc0c4080004f4004a9001b0400915, 0x6918bda462b69189da462369187da4617025041c462f7118adc461f71185dc460b030e40ec23f61c89d8722361c82c0f6086104ad8222761048c094107918bde462b79185c0c4a00004f400389001874009390032d400388, 0x69989da662369987da6617025061c662f7198adc661f71985dc660b03d8610c347430d0d0c317430c2c093087998bde662b79987de6617030c520662781987e0660b030c2000141000ef4006a10026e400d3500444400208, 0x13010c4c02b13008c094007818bde062b78187de0617030a020062780188e0061f03100000141000ef4006890026e400d3500444401619030c40cc23f3308eccc23761889d8622361887d8431761882c003086998bda662b, 0x3300fccc03b3300dd8602b61808d8031761804d8030b0308008c03f2300ec8c0376100ad8022761008d8021f60082c001006818bda062b68189da062368187da0617025001c062f7018adc061f70185dc060b03d8004c04b, 0x30c00cc043]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg34k549 : region H34 0x81000000008111110009090900090088 0x10000000000000000 := regionTerm _ _ prog34k549 adj34 _ _ 21 (by decide +kernel)
private theorem reg34k2 : region H34 0x81000000008111110009090900090088 0x0 := regionFork _ _ _ 64 reg34k3 reg34k549
def prog34k775 : Array Nat := #[0x22a40040c44470d111b702d23000121045328114be0452e8114aa0456a1111c34446dc0b50c000484003250250316353f58d4ed63537041aa00012d041ab00012900131400c89006c740289500e46404a0101884407e31, 0x34e2000145001304006ad002aa4001880293180913e03c621021c703c62000121000a946a14350c4ed421b702c621021c740870d021b70246200e4c67086bc0d1884b470c091880004d4002b90244f80b18800049400621, 0x244f8a313b024a3000109024b2805188000494004ad001c8400a2900347410188028f19433bf50ceed433b7041030113ca0406200014558cefd633bb58cedc1181c3c06de0718b024e322312338c4ec1169c000424113ca, 0x1984ac118187986bde61ab79867c1180c0004f400389001854009390032d41040c01cb28e32bf38caece32b701caa80818850cafd432bb50cadc0a2a602ca31051c741470d051b741462c0918858cafd632bb58cadc1068c, 0x40071d001c340065c10180000484003bd001a24009b90034d401319034c30cd1c733470da61af6986ada619f69865ccd18b046061c61af7186adc619f71865dc618b000a30c51c731470cc32bf31462c0f18830871cc3143, 0x30c0dc6602b30065cc018b0246004304b10c0ec091800004246d0436806bda302b68c08da019f68065c118007006bdc01ab70067dc019770062c0f18010c12c4304310c0ac43023046001e01af7806ade019f78065c00180, 0x7106bdc41ab71067dc419771062c0f20c80c89e0322380c87e0320b044821e41af7906ade419f79065c0020c41071d0419741062c04188000484003bd001b04009b90034d401199005a040018030071cc304330c0fcc303b, 0x387401211005c6401c810106006404320c0fc8303b20c0dc6402b20c08c8019f20c06c8018b000830c41c731070cc323f30c8ecc41b721867cc419731062c0020c6906bda41ab68c89da322369067da419723462c11810, 0x3b06dd871af61c6ad8719761c62c0928c2b06dd851af6146ad832a361462c091881b050d821af60c4ad83123000031a362f68d8ada362768d88c0c5a843071d0c1c30292318a1af02d23000129000a84004b5001e2400a95, 0x246006c0431b00dd801af60c0ad8302360067d8301b60065d8301360062c0c30c33071ccc1c33306dd861af6186ad8619f61865d8619361862c0020c2306dd841af6106ad8322760c88d8419f61065d8418b045870ec1c3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg34k775 : region H34 0x81000000008111110009090900090188 0x100 := regionTerm _ _ prog34k775 adj34 _ _ 21 (by decide +kernel)
private theorem reg34k1 : region H34 0x81000000008111110009090900090188 0x0 := regionFork _ _ _ 8 reg34k2 reg34k775
def prog34k1096 : Array Nat := #[0xab4092ca484adc0e68413832c4e0c3024411614b70244100012d000ae40913e02d2100010900185400bc5000411612bf584aed612b70144100012d02c41000115001294012a100727402da900f6640520101ae4408c31, 0x26e400e3503d010122a690502c0f404000525050c32a02ed012b702d280480cb12030c480bb02d011214434850dc0b4040004940030900165410684045328114be0452e809104584afd612bb041c100913e024a1000109, 0x32d40710469c2bda70a769c28da709701c4104e0cb13828c08384000424ee0c371c2bdc709702ce10123c690602c12396041e100014981c29e070a3000e100f4c603d2281241c000495e70af79c25c081040004f400541, 0x32e4010b5028411aa0af6a829daa0a36a827daa0970414100e4c6029010001257282bdca09f72825dc150b0404100a3c6504efc0a39603c4104a0cb12830c4a0a3041e100a4c60292580f4040004940030900167400839, 0x69825c0830433830dc60af7182adc609f71825dc130b03cc12060a781828e0609f34025e0130b018410460cb03c498460a3020c10001097982bde60ab79827de6097018410460cb1182ac460a3044a1000109000ef400941, 0x41e103004b0c00ae000a780408e0009f0002000f4c603d22812400000495e00af7802ade009f78025c080800a012c2802b40025c02080000484003bd00230400c350040e401499018411a60af6982ada60a769828da609f, 0x1041000141000ef4009210032d4010b900546401a810182002604b30410cc103f3040ecc10370980ac2602330025c0e4800b812c2e0437002bdc102b0b808dc009f70025c020806802bda00ab68029da00a368027da0097, 0x23829c8e0a371027dc409770482c041046902bda40ab69029da40a369027da409703d011040c322029c8809f41025d0120b010410440cb11030c0f126024810001097902bde40ab79027de40970000120122780487e0120b, 0x42400395001884009a900367401211005c6401d010082002404b09010c8103f2040ec810370900ac800a720408c8009f20406c0620431030cc123f3102ecc123721829c860a321827cc409730482c002047102bdc40ab, 0x61025d8120b01c410ec0c33b02ed870af61c2ad870a761c28d870970014114c0bb6282bd8a0a762828d8a09760542c0040443030d880af62029d8809760502c051042b02ed850af61429c0c5a413032c4c0c31302ec0b484, 0x82002c04b0b010c2c03b6002bd8102b60029d8102360027d8101b60025d81013000c10cc0c33302ed860af6182ad860a761828d8609f61825d86093604c2c002042302ed840af6102ad840a761028d8409f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg34k1096 : region H34 0x81000000008111110009090900090098 0x10 := regionTerm _ _ prog34k1096 adj34 _ _ 21 (by decide +kernel)
def prog34k1446 : Array Nat := #[0x610700af80c29e030a380c27e0118b00c411a30af68c29da30a368c27c081847046bdc119f70462c0f18410c32c430a3044e10670af0456100011d000a24004b9001cd400a410036a4011950060c401d19008c0402991, 0x1982ac6609f30c25cc118b0006106c0c360c2bd830ab60c29d830a360c27d8309760462c05184048a9a4118b0146100014919430ca30bb2846dc650af1942aca30a319427c115041a830d430bb5046dc6a0af1a827d4118b, 0x19030c830bb2046dc830b31902bc640ab20c29c830a320c27c8309b19025c8118b20c20c0308008c12c6104308c0ec610371840cc600af1840ac2302318027c6101b18025c0618430471cc30c330c2ecc11b730c2cc660af, 0x4184]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg34k1446 : region H34 0x81000000008111110009090900090198 0x110 := regionTerm _ _ prog34k1446 adj34 _ _ 21 (by decide +kernel)
private theorem reg34k1095 : region H34 0x81000000008111110009090900090198 0x10 := regionFork _ _ _ 8 reg34k1096 reg34k1446
private theorem reg34k0 : region H34 0x81000000008111110009090900090198 0x0 := regionFork _ _ _ 4 reg34k1 reg34k1095
private theorem safe34 : hostSafe H34 := regionHost _ _ _ bk34 reg34k0
def H35 : Array Nat := #[0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0x10, 0x12, 0x18, 0x1b, 0x20, 0x24, 0x28, 0x2d, 0x30, 0x36, 0x38, 0x3f]
def N35 : Array Nat := #[0x141011101050154, 0x101211101010332, 0x101011101010110, 0x10101010905030e, 0x101010101050104, 0x101010101010302, 0x101010101010100, 0x410011000500fe, 0x41001100050054, 0x2111000003fe, 0x211100000332, 0x11000000fe, 0x1100000010, 0x90503fe, 0x905030e, 0x500fe, 0x50004, 0x3fe, 0x302, 0xfe, 0x0]
private theorem bk35 : bookOK H35 N35 0x81412111090503fe = true := by decide +kernel
private theorem adj35 : validRows H35 N35 := rows_of_book _ _ _ bk35
def prog35k5 : Array Nat := #[0x4192810646001861cc6ab731a9dcc6a3035060001390390600013500130400ebd0292614d4c35352fd4d4bb53528c0041852130d484bf5212ec0a498000484003b502506000129029060001250022c40222d00f67406215, 0x7a5a6d8d4bb03926000135000ca40c5207a9a6d8d53b03106000129039460001350010940f64a03d9180a4985412ed504b754128c0d4986352ec0e4980004d4002a9001861cc6ab731a8c0d5180004e40e5180004d400425, 0x825aad6d49b03546000125000ce40a4985412ed504a303926000129039460001250010d4105ca0417180059872dacdcb6ab72da9dcb6a303506000139039060001350015040103d0292614f4c353d2ed4f4b753d28c0c4a0, 0x52400845003ed4018a5035281e96ab5b52ede969b0292614f4c353d2ed4f4a303926000129000ed40059872dacdcb6ab72da8c0d5180004e40e5180004d4004a503d7280f5c6001661cb6b372daadcb6a772da8c0d4a0, 0x3547000119000ee400621020e61113cb444eed113ab038e60115c20456f80e3980459081163e028e6000131000cb400521020e61123bb448eac0e398049708125be038e60126420498f80a3980004c40032d0014840e518, 0x424edd093ab000e61474c351d2fd474bb51d2dc093983a4d1d2733f498eed273370352712d3bb03927000135000a64005a90022840d398434f2d0d3c7434eed0d3ab000e61c76b371dabdc76ab030e60ed34769ccbda63ab, 0x16f40c2c2041051092c74a0afd2543b4a0adc00414434b1da82af6950ac0a4145950ec0a4140004b4002b50014940a4945952ed654b702d450001250292500012d00108400c3100606402f9d024e61093cb424f1d093bb, 0x5140c2c2045480d12cf04d48000145000ac4005bd0026b400e35004a940e694795aade56a7039051e542b79509c0f7140004840033503d9280f6460310510d2c76350eda82af6950ada82a7039a500012103905000135, 0x504c92cf324b1cc92bf324adcc92af039a800c2c203548000131334b3ccd2c7334afccd2af02d480105ca040ac80e5a0000504cb2cf32cb1ccb2bf03dc800f64a030b080f5200004c4cf2cf33cb1c11720344b3c13720, 0x414eed053ab0314700012131cb3cc72c731cafcc72af000051053cb414f1d053bb414eac0a394594eec0c39403d9280f646794eac0e3940004f40c2c2028e50001310014b4006a100266400f35004a940a4a0040ac80e4a0, 0x103943a4b1d272bf494eed272b749ca8d2539b030e50ed2c769cabda53ab69ca8da539b000c51053cb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg35k5 : region H35 0x81412111090503c0 0x0 := regionTerm _ _ prog35k5 adj35 _ _ 22 (by decide +kernel)
def prog35k340 : Array Nat := #[0x4a40e5100004d4005c5030928125103a891d4723f510eed472370014414d23f6a88bda45230290416453b0290400012d000ad40051d020e41643bb590edc0b410000474083900004b4004290030c40181900be9404615, 0x3dca0cf24f04dca00013d0309280f52033c93c135200004f4002b1001714009ad0038d40129d039a42246a3891a7c0e51089148e2451f045c4000129000cd4116420458f80c5105348fd8d53b6a88bda45236a887c0e690, 0x29070122320394700014931c93cc724731c8fcc723731c8bc0e6a80309280d5200004c4cd24f33491ccd23f3348bc0b520049708122320396a00014932c93ccb24732c8fc11728030928116420454800013134493cd123f, 0x69126c0031051130d444bb51128c0c4a00004a4c924f32491cc923f3248bc0001051130d444bf5112ed444a3025041644bb031240116420458fa244a303924000145030928094100004c40052d001aa400999003cd40129d, 0x2b491cad23f2b48bc0b5202ac93cab2472ac8fc0f5202bc93caf247045480b124f04d48000145000af4004ad001cd400a2500367405232049240e924749c8fd243bb49c8dce922b490e6c0c4904b48fda922f6a48ada44a3, 0xa41c29c93ca724729c8fca723729c8bca7227029280a924f2a491ca923f2a48dca922f035480ad24f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg35k340 : region H35 0x81412111090503e0 0x20 := regionTerm _ _ prog35k340 adj35 _ _ 22 (by decide +kernel)
private theorem reg35k4 : region H35 0x81412111090503e0 0x0 := regionFork _ _ _ 5 reg35k5 reg35k340
def prog35k515 : Array Nat := #[0x39420001250017141014a049c20ee14771c4bdc23ab71c49c0e4884b84fdc912f70928c0e408789cac0e4080004f4002a500147408388788eade23a703d0200011d020e200013d0010e400c4100606402fb501185405811, 0x32c53c137280004b41014a039680cb14f04dc800012d000b04005c50026f400e25004a740a48888928e2249f00142222723889c7c115080004e4003250460c81182e0312220972b4b84fdc912f70928dc911f02922000139, 0x485080e51c000524c714f31c51cc713f31c4bcc71270394901014a0392800014132453cc91473244fcc912f03dc8012142049ec80f728000524cf14f33c51ccf12f045ca01014a0460c811720000504d114f3444bc0e5a8, 0xc21c26b3709aadc26a30354800013933453ccd1473344fccd12f000021c26b3709abdc26ab709a8c0d408789aac005080460c81182e889a8c0d5080005141014a035020001410014f4006b900266400f25004a740e41c, 0x2a44fca912f03dc80af14f2bc51caf12f039680ab14f2ac51c117202c453c13720000514002ad0012f4007250028d400d9d014508126883b451ced13b69c4bda23ab69c49da239b041a212d13f4b44eda912f68928da249b, 0x2444fc9112f0396a08b14f22c4fc0f72823c53c137280004f4002ad0013140071d0028d400da501052804116039070a714f29c51ca713f29c4dca712f29c49c0e6a02b453cad1472b44fcad12f2b449c0e4a02a453ca9147, 0x394908914f22451c8913f2244dc8912f22447c0e6a823453c8d1472344fc8d12f23447c0e51c21c53c8714721c4fc8712f045ca09114f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg35k515 : region H35 0x81412111090503e8 0x8 := regionTerm _ _ prog35k515 adj35 _ _ 22 (by decide +kernel)
private theorem reg35k3 : region H35 0x81412111090503e8 0x0 := regionFork _ _ _ 3 reg35k4 reg35k515
def prog35k727 : Array Nat := #[0x405281011604d03000141000c44005390288308a1cf60d4ec1370c0004a40c24a0308581360c7306adcc1a3028c301064a0418581340c00050400339001444135200004c400a0900471401dbd00b4b40413501569406f9d, 0x31140e40c0459080a40c0004c66389b98e25e6389398e22c116204446ae234178a062c11608030928911ab0308581170c0004441164204542000131001484007cd04c621c21b37086adc21a304d4300414a0104581350c, 0x26e400cc50040f40a40c045eca2379b88de5e2379388de2c0e50c03d9280a40c0004c66379b98de5e6379398de2c0f62853c68de35137a862c0f608030b08af1a3030a480f70c0004540f64a03d020001310014a4007cd, 0x78d65de359378d62c0e40c04570a2359b88d65e2359388d62c1358c72c6cdcb1ab72c68dcb18b0290326359b98d65e6359398d62c0b40c22c6ac0b50c040ac81028a2ac68c0b50c000454105ca02d03000141001444006cd, 0x68d66da359768d64c0d62023473c8d1c72346fc8d1ab0358a0ad1cf2b471cad1bf2b468c0830c43471da81b36a06ac0d62833473ccd1c73346fc0c50c000464003a1001854009110030b4010090394300f5ca03d719e359b, 0x50d2fd434bb50d28c0c4a032473cc91c73246fcc91af001231c91b37246bdc91a302503000139000e64006a900265400d11004224014b50346206d14f1b451c6d13f6886cda312f6886ada21a3001631ab1b36ac6adab1a3, 0x68940048c4b46fda91b36a46bda91ab6a468da349b68d25da34936a462c0a48c1a453c6914748c4fd2313b1a44bd221a3031280891cf22471c891bf2246bc891ab031490a91cf2a471ca91bf2a46bca91a3000c31434c3, 0x29c71ca71bf29c6bca71a3031070871cf21c71c871bf21c6bc871ab000c31033cb40cf1d033bb40ceac0c51c31c73cc71c731c6fcc71af000e31c71b371c6bdc71ab028e3000139000e64006a100264400d15004224014b5, 0x24e30e91c749c6fd233bb49c6dce91ab49c68d2339b48ce5d2339349c62c0038c3b471da71b369c6bda71ab69c68da339b68ce5da339369c62c0838c19c53ce314719c4fce313b19c4bce21ab031470a71cf]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg35k727 : region H35 0x81412111090503f8 0x10 := regionTerm _ _ prog35k727 adj35 _ _ 22 (by decide +kernel)
private theorem reg35k2 : region H35 0x81412111090503f8 0x0 := regionFork _ _ _ 4 reg35k3 reg35k727
def prog35k1013 : Array Nat := #[0x30858134040004c4003090014a4135045402ed500a304dc10001290405281011604d411500bb54028c0e3040419281061604d01000131000ca40050904dc8000141002844011c50076b402d3d010434057b501c6940919d, 0x29010118320390100014198626e6189798624e6188b046081110bb88505e280930454101014a1442ec10116045410001090460c81171000050400521001f341320451030d440bb51028c137040105280411604dc100c24a, 0x33140102d039010115c288566e2159788564e2158b039410105ca0390100014198566e6159798564e6158b041cb1cb0a35b824dc158b02d410102b2040a28ab0a302d410001150417280b41000050400539001f3400c45, 0x78564de158b029010117b2885e6e21797885e4e2178b04de114f0c353c2ed4f0a353c24c0c404985e6e61797985e4e6178b03d0104f0bb03d8100c2c22bc28c0c29203dc100011503d9280f4040004c400509001b34009a9, 0x60c2ec115040004c4710cf88c28e2309388462c1318450c30d430bb50c28d4309304c611c11b370468dc118b04c610730a398c24e6118b0206100014d000ee40062900251400e3d0048b40e50403d7280f5c678566de1597, 0x33431ccd0bf3342bc0d50453430d4d0bf53428c0d4040004a400399001ae400995003424010910052341058c1ac33c6b0c71ac2fd630bb1ac28d6309358462c0f6041bc33c6f0c77846ac6f0a378c24de118b04461011642, 0x6846cda30af6846ada30a368c24da118b039a108d0cf23431c8d0bf6902bda122b69028c106a013433c4d0c71342fc4d0bb1342bc107342b433cad0c72b42fcad0af2b428c00304705acdc16af705aadc16a3041a80cd0cf, 0x78522c104a012433c490c71242ec490af041c90a90cf2a431ca90af2a428c0830442431d280c34a02ec1072432433cc90c73242bc10704000464003a1001854009090030f4010110052d401a0d0346106d0cf1b431c6d0bf, 0x48c30d230bf48c2ed230b71a42bd230a348c24d2118b0352112d0c34b42fd2d0bb6a42bda90a368526da14976a424da148b024810890cf22431d240c34902fd240bb2242bd240a30292112f0c34bc2ed2f0a378526de1497, 0x11c33c470c711c2fc470bb11c2bc00304404f2d013c7404eed013ab041c70c70cf31c31cc70bf31c2bc0038451c30d470bf51c2ec0e3840004a400399001a8400989003454010910052d401a25008034091841a433c690c7, 0x49c2fd270bb49c2dd270a3484e6d2139749c24d2138b030e10ed0c73b42eda70af684eada70a3684e6da139769c24da138b020e10870cf39031c870bf3902ec870af3848ac1071c29c33ca70c729c2fca70af29c28c1041c, 0x718419c33ce30c719c2fce30bb38c2dc670af3846ace30a719c28ce309338462c003843a431d270c3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg35k1013 : region H35 0x81412111090503fc 0x4 := regionTerm _ _ prog35k1013 adj35 _ _ 22 (by decide +kernel)
private theorem reg35k1 : region H35 0x81412111090503fc 0x0 := regionFork _ _ _ 2 reg35k2 reg35k1013
def prog35k1381 : Array Nat := #[0x30a48135000004c400309001484134004480ed1202b04dc00001210485081211204d0011203b4480ac0e3000499081261204d40000131000c840050904dca000149002854011bd0076b402d450104340578501cad4092a5, 0x29000127b203940000149981e6e60797981e4e6078b049ea14f03b7a805de051303d000121420484484f03b03d00000109049ec80f71400052400529001f341328041412d0503b4140ac137000145080511204dc000c2c2, 0x32f40102d0394000f5ca78166de059778164de058b039000125c20394000014998166e6059798164e6058b049cb1cb02b5b805dc058b02d000122320488288b02b02d000001110497080b51400052400539001f3400c3d, 0x88164e2058b029000117b2881e6e20797881e4e2078b04e2011104b4440ed1102b44405c0c50098226e6089798224e6088b0454005103b0458000c24a2440ac0c216045c0000111045908115000004c400509001b34009a1, 0x60c0ec0f4000004c46f04f78c0ade301778062c1318040c12d0303b40c0ad0301704c601c01b37006adc018b04c6007302b98c05e6018b0286000014d000ee4006210024f400e450048b40e400045708115be88166e20597, 0x50030d400bb50024c130800cc0ee6101798024c0e080000534003a90018840092d003834011c50058f41258c1ac13c6b0471ac0fd6303b1ac0ad6301758062c116001c413c7103f1c40ae201a388c05e2018b03c6000f64a, 0x78405de009378403c118000c413c3103b0c40be200a388405e2009388403c0308018413c2303b1840bc6102b18028c0b08004172a0102b02d000001410ac13d6103b58405d6009304c2010104b4040ed0102b40405c13080, 0x2340fc8d02f2340ac00300701acdc06af701aadc06a3049aa0cd04f33411ccd03f3340bc0d40043412d0d0474340ac0d50000048400399001ae4009910034240109500523401a05049e102f04f0bc11c2f03b0bc0bde102b, 0x6840bda102b68028da101768024da100f0346006d04f1b411c6d03f6806cda302f68c0ada01a368c05da018b039a00ad04f2b411cad03f6940bda502b680a8c126a813413c4d0471340fc4d03b1340bc1273423413c8d047, 0x1240fc4903b1240bc0030050130d404bf5012ed404a3049c90c904f32411cc903f3240bc0940042412d090474240ec0e48000048400399001aa4009890034440109500523401a050080d40d0800b413c2d0470b40fc2d03b, 0x4840ec2902f48028d2101748024d2100f0246006904f1a411d2303f48c0ec6902f1a40ad201a348c05d2018b029200a904f2a411d2503f4940eca902f480a8c1272422413c890472240fc8902f2240ac1252412413c49047, 0xc4804b40fd2d03b6a40bda902b68128da049b6a405da04936a403da048b6a401c090800a413c2904748030d2103f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg35k1381 : region H35 0x81412111090502fe 0x2 := regionTerm _ _ prog35k1381 adj35 _ _ 22 (by decide +kernel)
def prog35k1750 : Array Nat := #[0x880e6e20393880e2c1251c11c13c4703f11c0ec4702f049c708704f21c0fc8702f21c0ac0a3003a812d4703f51c0ec1271c31c13cc703f31c0bc12700000464003a900184400909003114010150052d401a2500803402685, 0x3a412ce904749c0fd2703b49c0dce902b480e6d27017480e4d2038b034e00ed04b3b411ced03b69c0bda702b680e6da7017680e4da038b01ca00a704f39412ce504729c0fce503b29c0bce502b020e00f104b3c40ecf102b, 0x1c2002704f38412ce104709c0fce103b3840dc2702f3840ace102738405ce009338403c0718019c13ce304b38c11c6703f38c0ece303719c0bce302b38c09ce301738062c09380]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg35k1750 : region H35 0x81412111090503fe 0x102 := regionTerm _ _ prog35k1750 adj35 _ _ 22 (by decide +kernel)
private theorem reg35k1380 : region H35 0x81412111090503fe 0x2 := regionFork _ _ _ 8 reg35k1381 reg35k1750
private theorem reg35k0 : region H35 0x81412111090503fe 0x0 := regionFork _ _ _ 1 reg35k1 reg35k1380
private theorem safe35 : hostSafe H35 := regionHost _ _ _ bk35 reg35k0
def H36 : Array Nat := #[0x1, 0x2, 0x4, 0x8, 0x9, 0xa, 0xb, 0x10, 0x11, 0x14, 0x15, 0x20, 0x22, 0x24, 0x26, 0x28, 0x2a, 0x30, 0x34, 0x39, 0x3f]
def N36 : Array Nat := #[0x11055500110514, 0x211011100330312, 0x201050500030f06, 0x11005500330016, 0x11005500110014, 0x11001100330012, 0x11001100110010, 0x55500000f16, 0x55500000514, 0x50500000f06, 0x50500000504, 0x330f16, 0x330312, 0x30f06, 0x30302, 0x330016, 0x330012, 0xf16, 0xf06, 0x14, 0x0]
private theorem bk36 : bookOK H36 N36 0x8211055500330f16 = true := by decide +kernel
private theorem adj36 : validRows H36 N36 := rows_of_book _ _ _ bk36
def prog36k4 : Array Nat := #[0x29021c811302904000109000ac40052d028820001210395380e54602c8214b14352c4fd4b1330308214c1435304fc0f20853c50c102080004f4002b10012b40a410000424008390048d4082080004a401d990122940959d, 0x2244012b10090e40a40852d10d4b43f6a164d4b4330290214c4435310fda86130290410d23b43482c0a408000444003310016b40a2080004840d54e0355180a40852d10d4b43f72164d4b4330290214c4435310fdc8613, 0x3088dcc222f035480cd24b33491ccd22f02d480cb24b32c91c1152034492c12520000514002ad0012d400709028c20cb14759848c0a30869848c00308809eae027a303cc2000141040c200013d0010d4005ad02906000109, 0x2304bc0031032c92ccb24732c8dd845ab61168c0a31033492ccd24769188c1183034492c12830000514002b50014b400889030c210c143408cdd0c12f028c2000121029060001090012440c34e030cf80a40830892cc2247, 0x4a400321029280c924b32491c10790000464107980004440042d0024c401135008a24030b9000820c224b30891dc41233088dcc222f020c4000109020c2000111038d380e33e038ca80a20830892c8c1473088dd84123, 0x4bd10c104180004f4002b10012b40a498000484008910353380d4c6001261895ab62568d89593001241e962b7a588c0f61a024c420962b82588c0c3100005040033d0016b40b3104ad10d2b43f02cc414b4c352d2fc09310, 0x353380d4c6040c2000135000cf400511001ec400aad029241a45a34ac8cc0a49069188c00490825eae097a303d040001410410400013d0010c4005ad69126c0a4a04ad10d2b43f6a166d2b4330310612c4434b10fc0f418, 0x4440f4104bd10c104100004f40a49000048400389001cc400d2d0050640e4ce0393180b4084ac50d2b13f4ac4cd2b11b4ac44c0c4084b050d2c13f4b046d2c113020821241434904fd2411b03d0212f1434bc46c10418, 0xe440e33e038ca80b4084ad10d2b43f72164d2b4330292212b1434ac4fd2b1334ac44c0a490000424004210310212c1434b04fd2c1130292812c4434b10fdc861302924000121000e240020849050d2413f71048c107a0, 0x434efc0f31043cf0c103100004f4002b50012e4007310028b40a39031c92cc724731c8dcc722f028e4000119028e6000111001484012a50096240941032492cc92373248bcc920b020c21261434984cd2612f02506000109, 0x3b48ec0a49c000444003a10353380d4c603d0712f3c34bce4c107100004f40033500286400cb1003eb40b31042cf0d0b3bf42ceed0b3b742cecc0c310430f0d0c3bf430eed0c3b7038c410e3c3438efd0e3b7034c410d3c3, 0x3b04fc0f3883bc50c103880004f4002b10012b400719002c8400f1102d0712b3c34acefd2b3b34ace6d2b3930310712c3c34b0efd2c39b4b0e4c08398498f0d263bf498e4c08390434f0d0d3bf434eec00390490f0d243bf, 0x20821c51ce41433904fce223b3888dce41333904bce411b000c21023c3408efd023bb408edd023b3408ebc0730831c51ce61433984fce23373984cce612f02ce20eb1433ac4fceb133030e20ec143]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg36k4 : region H36 0x8211055500330a10 0x0 := regionTerm _ _ prog36k4 adj36 _ _ 22 (by decide +kernel)
def prog36k417 : Array Nat := #[0x895a6e256930290524569b915a4c0d520000524003450016b40b5202ac92cab24702d480cb2cb32cb1c0a41400046400311018a41454435150fc128a00004a4128a80004840042d0024d4011250080e403e310150240651d, 0x59526d65493001051254434950fc0a4940004840d4ce035319a549b69524c0a4a02a492ca9247000c51254434950fc0a494324b2cc92c702925000119000c8400511001cd400c2d001451a55a369566da5593001050116aa, 0x2ac89c0a494000444003a1028a40ad24b711a8cad227024a42092ab824a8c08290000504a924b020a4145443020a4000129028a4000121000e940073504105000111002ab4011190063140e2ce038af8004945a4aad692a3, 0x30b380c2be045040b124b2c48dcb122f020c5000111045ca81172602d040cb2cb32cadccb2a7025040c92cb324adc0d410334b2c124100004d4002a50012b40e32a001051c859342cadd682ab5a0a9c0a2902ac92cab237, 0x45040b124b049040001454308ed0c2374308bc08314000445882ab045440b124b2c48dcb122f028c5000111018a40ab24b2ac8dd845ab028c5000111035440cd2cb04944000135028a4000119000eb400745002a8401025, 0x48a20001392a051d051434144fd022b74144cd0512f028820c22cb308b1cc22b7308abc0520851450d4513f5144cd4512f0148200012900106400721003494092902a492ca92472a48dd2c22f024c5000111624aad892a3, 0x414f0d053bf414eed053b7414ecd053af028e40a724b29c91ca723729c8bc0a39431cb2cc72c731cadcc72af028e500011900104400721002c9400f09020a21251434944fd251334944bd2511b49444c08314038b39c8113, 0x1ca20a714739450ce513f388adce51333944bca712339446ce5113020e51253c3494efd253b3494ebd2539b494e4c06290]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg36k417 : region H36 0x8211055500330e10 0x400 := regionTerm _ _ prog36k417 adj36 _ _ 22 (by decide +kernel)
private theorem reg36k3 : region H36 0x8211055500330e10 0x0 := regionFork _ _ _ 10 reg36k4 reg36k417
def prog36k659 : Array Nat := #[0xaa50123b4048cc0a2040395380e5460394681150424432c12504000514002b95048cc062040004a4006a10030d40122d020c11414435050fd414335050bc0a304000484083040004a400511006a5402aa500ee7405309, 0x38af8124040004e400331001514007290026d400cad0188108b0cb22c31c8b0b75902ad640a30354100a33a02881000119035539412330188100012923432c8d0c769028c0620450510d4143f045010910cb04901000145, 0x32432cc90c73242dcc90af025010001190010a4007110034540b2042ac32cab0c72ac2dcab0ab2ac28c0d2042b432cad0c72b42acad0a3028810aa0cb2a831caa0a3044810b10cb2c428c12410030b380c2be0490400e2ce, 0x31c2dc0a384000464003a5001a8400a11003a54012ad024810a90cb2a431ca90b72a42bca90ab2a428c0a490039339c40a30412100013922432c890c74902fc890b74848cd240af020c11414c35052fd414b35052bc09404, 0x584e6d6139759c24c0720429c32ca70c729c2dca70ab29c29ca70a3040e10870cb21c31ce40bf3848ece40b73848cc870a7000c11013c3404efd013bb404edd013b3000e11213c3484efd213b3484e6c0a38431c32cc70c7, 0x28829ca20a3020c10480cf12031d011434082fd020b74044cc0010448450d2113f4844cd2111b028410c20cb30831cc20b702841000119000e94006a1002a5400e91004eb40191d000e10eb0bf3ac2dd670ab59c29d670a3, 0x3882fce20b73844cce20af11c28ce111b38445ce20930004104b0cf12c31c4b0bf5882ad620a758828d6111b58445d62093028820440cf20832c820c71102fc820b72044cc820a711028c0010428832ca20c72882dca20ab, 0x1c410470cf11c31ce1143]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg36k659 : region H36 0x8211055500330e14 0x4 := regionTerm _ _ prog36k659 adj36 _ _ 22 (by decide +kernel)
private theorem reg36k2 : region H36 0x8211055500330e14 0x0 := regionFork _ _ _ 2 reg36k3 reg36k659
def prog36k887 : Array Nat := #[0x2346ec8d1b30394808e1cb23871c8e1b30314808c1cb23071c1152024472c12520000514002b10012e4007350028b40830c50d10d4343f50d0cd4342f020c3000129028c300012100144401295009614039a501382406c1d, 0x2a868c0820c23072c8c1c72306ec0828c2a072ca81c74306ec0628c00048400391030b380c2be044830b11cb2c468c12720000514003310028a400cb5003eb40b52022c72c8b1c722c6ec8b1b722c6cc0d52023472c8d1c7, 0x5046cd430af02c6106b0cb1ac31c6b0b70346106d0cb1b431c111841c432c12184000514002b50012b400729002c4400f2102c830ab1cb2ac71cab1b72ac6acab1a3034830ad1cb2b471cad1ab2b468c0a20c2a872caa1c7, 0xc31434c350d2fd434b350d2bc0930c0004a400421001c4400b15003c14081841a032c680c740c2fd011bb40c2dd011b340c2bc680ab028610811cb20471c811bb2046dc811b32046bc0a1841a832c6a0c750c2fc6a0b7, 0x3a54012ad005e14091841a432c690c748c2fc690b74846cd230af1a42ac690a348c24c0920c2a472ca91c72a46dca91af2a46aca91a3029280891cb22471c891bb2246dc891b32246bc0830c48d10d2343f48d0cd2342f, 0x2886dca21ab28869ca21a3029020821cb20871c821bb2086dc821b320869c061881a051d0314340c4fd021bb4086dd031330006212314348c4fd2313348c46c0a18830872cc21c73086dc0a188000464003a5001a8400a91, 0x464003a5001a8400a110038540122d005e2401e0500c410430cf18832c620c710c2fc620b71844cc620af1882ac620a718828c430930006206b1471ac4cd621ab58869d6312358c46d6311758c44c0418828872ca21c7, 0x58ce5d6339301c830a71cb29c71ca71b729c6aca71a729c68c0a41c21c72c871c721c6ec871b721c6cc871a7000c31033c340cefd033bb40cedd033b3000e31233c348cefd233b348ce6c0a38c31c72cc71c731c6dc0a38c, 0x19c32c670c738c2fce11bb38c2dce11b338c2bc670ab19c29c670a338c24ce308b0006206714738c50ce313f3886ece21b738c4cce312f19c48ce311b38c45ce3113000e30eb1bb3ac6dceb1b359c6ad671a759c68d6339b, 0x7184]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg36k887 : region H36 0x8211055500330f14 0x100 := regionTerm _ _ prog36k887 adj36 _ _ 22 (by decide +kernel)
private theorem reg36k1 : region H36 0x8211055500330f14 0x0 := regionFork _ _ _ 8 reg36k2 reg36k887
def prog36k1177 : Array Nat := #[0x4300fd0c03b4300dc0830043410d0d03f4340ec0830043810d0e03f03cc010f043040c000013d000ae4004b5001cc40a48032412cc90473240dc0a3000004940a480000464004a1003a4401c2d009e5404609019c740898d, 0x28c000012500108400791041ed08d04b23411c8d03b2340cc8d027041ec08c04b23011c8c03b23009c107b823812c8e04723809c107a422412c890470460f09104b04a0f000145000a94004b9001cc400a35030c010c043, 0x2c412e2071304880000145038b380e2be04a200001390014c4009b5002ea40132d00588401a25041eb08b04b22c11c8b03b22c0dc8b03322c09c0b30042c10d0b03f42c0ed0b03742c0cc0a4804ac10d2b03f4ac0cd6049b, 0x4140bc0b2002ac12cab0472ac0dd602ab039a500d54e2b412c0d5460148000e54e0395180e51a04a25000139000ed5450435140fd45033034800ad04b2b411c0020023012c8c0472300ec062800004440c2ce030af806280, 0x30809c0a10013c11c4f04378809de0123000401020434080ed0203704040000121000ef4006990032c401291005ab401b95039250a904b2a411d250434940fca90374940cd2502f04a251050434140fd0503b4140dd05033, 0x58809d6012358046d60113041e208204b20811c8203b2080dc8203320809c0a100030d38c204b3080dc0a1000004644c04713010c4c03f60809d801230004000e34e038cf80e32a70048c107880004e4c204b30811cc2037, 0x700e4c1079c21c12c87047041e70c704b31c11c10780000464003110014e4007a5002ad400e310048b4017150072240e28828812ca204711410c4503f2880dc450332880bca202728048c0a10012c11c4b04312c0fc4b033, 0x3940bca702702ce00eb0433ac0fceb03b3ac0dceb03359c09d6039b580e4c0c3003b010cec03f3b00ecec03761c09d80393020e00ed0433b40fced03b680e6da0393020e01203c3480efd2039b480e4c0e3003b810cee03f, 0x50c10d4303f04a20000129000c8400539001e5400ab10038d40122d005c9401c9d008a240010011c11ce20433880fce203b3880dce20333880bce011b38805ce011301ca00a704b29c11ce50433940fce503b3940dce5033, 0x1ac0ec6b0371ac0cd601ab58068d630170354006d04b1b411c6d03b1b40cda01a368c05c041801b012c6c0471b00ed801ab60068c0418028072ca01c72806aca01a30394006e04b1b811dc01a304a2310304340c0fc1288c, 0x1880ec620371880cc6202f18809c6012318807c4301701c6006704b19c11ce304338c0fce303b38c0dce303338c0bc6702738c05c091801a412c6904748c10d2303f1a40ec6903748c0cd2302f48c05c0b1801ac12c6b047, 0x310018812c6204710c10c4303f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg36k1177 : region H36 0x8211055500330f12 0x2 := regionTerm _ _ prog36k1177 adj36 _ _ 22 (by decide +kernel)
def prog36k1534 : Array Nat := #[0x68024c000800395380e546039469c009304a2100013950410d4103f5040cd410170182003104b0c40fe2101788024c0008020412c8103b2040cc12080000444003c5001aa400cb5004a84016ad006e940210d009c7402e09, 0x4840fc290374840cd2102f48405d200930182002b04b0ac11c2b03f0ac0dd600ab58028d6101758024c1288440410d0103f4040ed010374040cd010170182000d54e50410d41033018200001290b412c2d0470b40fda1017, 0x10407c4101710024c4100f0182002704b09c11ce10433840fce103b3840dce10333840bc2702738405ce009338403c0008018412c6104708c0fc6103b1840dc610331840bc600ab18409c600a30392102904b0a411d21043, 0x208010033c2204b10411c410431040fc220371040cc4102f08809c400a3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg36k1534 : region H36 0x8211055500330f16 0x6 := regionTerm _ _ prog36k1534 adj36 _ _ 22 (by decide +kernel)
private theorem reg36k1176 : region H36 0x8211055500330f16 0x2 := regionFork _ _ _ 2 reg36k1177 reg36k1534
private theorem reg36k0 : region H36 0x8211055500330f16 0x0 := regionFork _ _ _ 1 reg36k1 reg36k1176
private theorem safe36 : hostSafe H36 := regionHost _ _ _ bk36 reg36k0
def H37 : Array Nat := #[0x3, 0x4, 0x7, 0x8, 0xb, 0xc, 0xf, 0x10, 0x13, 0x20, 0x24, 0x30, 0x37, 0x40, 0x48, 0x50, 0x5b, 0x60, 0x6c, 0x70, 0x7f]
def N37 : Array Nat := #[0x11001000101010001001100011110, 0x10001080101010001000100090908, 0x10001000101010001000100010100, 0x10001000100010081001100090098, 0x10001000100010001001100010010, 0x10001000100010001000100090008, 0x10001000100010001000100010000, 0x1001000001010000001100009998, 0x1001000001010000001100001110, 0x80101010000000000099998, 0x80101010000000000090908, 0x1010000000000009998, 0x1010000000000000100, 0x81001100099998, 0x81001100090098, 0x1100009998, 0x1100000010, 0x99998, 0x90008, 0x9998, 0x0]
private theorem bk37 : bookOK H37 N37 0x80011001080101010081001100099998 = true := by decide +kernel
private theorem adj37 : validRows H37 N37 := rows_of_book _ _ _ bk37
def prog37k5 : Array Nat := #[0x4192810646001861cc6ab731a9dcc6a3035060001390390600013500130400ebd0292614d4c35352fd4d4bb53528c0041852130d484bf5212ec0a498000484003b502506000129029060001250022c40222d00f67406215, 0x7a5a6d8d4bb03926000135000ca40c5207a9a6d8d53b03106000129039460001350010940f64a03d9180a4985412ed504b754128c0d4986352ec0e4980004d4002a9001861cc6ab731a8c0d5180004e40e5180004d400425, 0x825aad6d49b03546000125000ce40a4985412ed504a303926000129039460001250010d4105ca0417180059872dacdcb6ab72da9dcb6a303506000139039060001350015040103d0292614f4c353d2ed4f4b753d28c0c4a0, 0x52400845003ed4018a5035281e96ab5b52ede969b0292614f4c353d2ed4f4a303926000129000ed40059872dacdcb6ab72da8c0d5180004e40e5180004d4004a503d7280f5c6001661cb6b372daadcb6a772da8c0d4a0, 0x3547000119000ee400621020e61113cb444eed113ab038e60115c20456f80e3980459081163e028e6000131000cb400521020e61123bb448eac0e398049708125be038e60126420498f80a3980004c40032d0014840e518, 0x424edd093ab000e61474c351d2fd474bb51d2dc093983a4d1d2733f498eed273370352712d3bb03927000135000a64005a90022840d398434f2d0d3c7434eed0d3ab000e61c76b371dabdc76ab030e60ed34769ccbda63ab, 0x16f40c2c2041051092c74a0afd2543b4a0adc00414434b1da82af6950ac0a4145950ec0a4140004b4002b50014940a4945952ed654b702d450001250292500012d00108400c3100606402f9d024e61093cb424f1d093bb, 0x5140c2c2045480d12cf04d48000145000ac4005bd0026b400e35004a940e694795aade56a7039051e542b79509c0f7140004840033503d9280f6460310510d2c76350eda82af6950ada82a7039a500012103905000135, 0x504c92cf324b1cc92bf324adcc92af039a800c2c203548000131334b3ccd2c7334afccd2af02d480105ca040ac80e5a0000504cb2cf32cb1ccb2bf03dc800f64a030b080f5200004c4cf2cf33cb1c11720344b3c13720, 0x414eed053ab0314700012131cb3cc72c731cafcc72af000051053cb414f1d053bb414eac0a394594eec0c39403d9280f646794eac0e3940004f40c2c2028e50001310014b4006a100266400f35004a940a4a0040ac80e4a0, 0x103943a4b1d272bf494eed272b749ca8d2539b030e50ed2c769cabda53ab69ca8da539b000c51053cb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg37k5 : region H37 0x80011001080101010081001100099000 0x0 := regionTerm _ _ prog37k5 adj37 _ _ 22 (by decide +kernel)
def prog37k340 : Array Nat := #[0x4a40e5100004d4005c5030928125103a891d4723f510eed472370014414d23f6a88bda45230290416453b0290400012d000ad40051d020e41643bb590edc0b410000474083900004b4004290030c40181900be9404615, 0x3dca0cf24f04dca00013d0309280f52033c93c135200004f4002b1001714009ad0038d40129d039a42246a3891a7c0e51089148e2451f045c4000129000cd4116420458f80c5105348fd8d53b6a88bda45236a887c0e690, 0x29070122320394700014931c93cc724731c8fcc723731c8bc0e6a80309280d5200004c4cd24f33491ccd23f3348bc0b520049708122320396a00014932c93ccb24732c8fc11728030928116420454800013134493cd123f, 0x69126c0031051130d444bb51128c0c4a00004a4c924f32491cc923f3248bc0001051130d444bf5112ed444a3025041644bb031240116420458fa244a303924000145030928094100004c40052d001aa400999003cd40129d, 0x2b491cad23f2b48bc0b5202ac93cab2472ac8fc0f5202bc93caf247045480b124f04d48000145000af4004ad001cd400a2500367405232049240e924749c8fd243bb49c8dce922b490e6c0c4904b48fda922f6a48ada44a3, 0xa41c29c93ca724729c8fca723729c8bca7227029280a924f2a491ca923f2a48dca922f035480ad24f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg37k340 : region H37 0x80011001080101010081001100099800 0x800 := regionTerm _ _ prog37k340 adj37 _ _ 22 (by decide +kernel)
private theorem reg37k4 : region H37 0x80011001080101010081001100099800 0x0 := regionFork _ _ _ 11 reg37k5 reg37k340
def prog37k515 : Array Nat := #[0x39420001250017141014a049c20ee14771c4bdc23ab71c49c0e4884b84fdc912f70928c0e408789cac0e4080004f4002a500147408388788eade23a703d0200011d020e200013d0010e400c4100606402fb501185405811, 0x32c53c137280004b41014a039680cb14f04dc800012d000b04005c50026f400e25004a740a48888928e2249f00142222723889c7c115080004e4003250460c81182e0312220972b4b84fdc912f70928dc911f02922000139, 0x485080e51c000524c714f31c51cc713f31c4bcc71270394901014a0392800014132453cc91473244fcc912f03dc8012142049ec80f728000524cf14f33c51ccf12f045ca01014a0460c811720000504d114f3444bc0e5a8, 0xc21c26b3709aadc26a30354800013933453ccd1473344fccd12f000021c26b3709abdc26ab709a8c0d408789aac005080460c81182e889a8c0d5080005141014a035020001410014f4006b900266400f25004a740e41c, 0x2a44fca912f03dc80af14f2bc51caf12f039680ab14f2ac51c117202c453c13720000514002ad0012f4007250028d400d9d014508126883b451ced13b69c4bda23ab69c49da239b041a212d13f4b44eda912f68928da249b, 0x2444fc9112f0396a08b14f22c4fc0f72823c53c137280004f4002ad0013140071d0028d400da501052804116039070a714f29c51ca713f29c4dca712f29c49c0e6a02b453cad1472b44fcad12f2b449c0e4a02a453ca9147, 0x394908914f22451c8913f2244dc8912f22447c0e6a823453c8d1472344fc8d12f23447c0e51c21c53c8714721c4fc8712f045ca09114f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg37k515 : region H37 0x80011001080101010081001100099880 0x80 := regionTerm _ _ prog37k515 adj37 _ _ 22 (by decide +kernel)
private theorem reg37k3 : region H37 0x80011001080101010081001100099880 0x0 := regionFork _ _ _ 7 reg37k4 reg37k515
def prog37k727 : Array Nat := #[0x405281011604d03000141000c44005390288308a1cf60d4ec1370c0004a40c24a0308581360c7306adcc1a3028c301064a0418581340c00050400339001444135200004c400a0900471401dbd00b4b40413501569406f9d, 0x31140e40c0459080a40c0004c66389b98e25e6389398e22c116204446ae234178a062c11608030928911ab0308581170c0004441164204542000131001484007cd04c621c21b37086adc21a304d4300414a0104581350c, 0x26e400cc50040f40a40c045eca2379b88de5e2379388de2c0e50c03d9280a40c0004c66379b98de5e6379398de2c0f62853c68de35137a862c0f608030b08af1a3030a480f70c0004540f64a03d020001310014a4007cd, 0x78d65de359378d62c0e40c04570a2359b88d65e2359388d62c1358c72c6cdcb1ab72c68dcb18b0290326359b98d65e6359398d62c0b40c22c6ac0b50c040ac81028a2ac68c0b50c000454105ca02d03000141001444006cd, 0x68d66da359768d64c0d62023473c8d1c72346fc8d1ab0358a0ad1cf2b471cad1bf2b468c0830c43471da81b36a06ac0d62833473ccd1c73346fc0c50c000464003a1001854009110030b4010090394300f5ca03d719e359b, 0x50d2fd434bb50d28c0c4a032473cc91c73246fcc91af001231c91b37246bdc91a302503000139000e64006a900265400d11004224014b50346206d14f1b451c6d13f6886cda312f6886ada21a3001631ab1b36ac6adab1a3, 0x68940048c4b46fda91b36a46bda91ab6a468da349b68d25da34936a462c0a48c1a453c6914748c4fd2313b1a44bd221a3031280891cf22471c891bf2246bc891ab031490a91cf2a471ca91bf2a46bca91a3000c31434c3, 0x29c71ca71bf29c6bca71a3031070871cf21c71c871bf21c6bc871ab000c31033cb40cf1d033bb40ceac0c51c31c73cc71c731c6fcc71af000e31c71b371c6bdc71ab028e3000139000e64006a100264400d15004224014b5, 0x24e30e91c749c6fd233bb49c6dce91ab49c68d2339b48ce5d2339349c62c0038c3b471da71b369c6bda71ab69c68da339b68ce5da339369c62c0838c19c53ce314719c4fce313b19c4bce21ab031470a71cf]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg37k727 : region H37 0x80011001080101010081001100099980 0x100 := regionTerm _ _ prog37k727 adj37 _ _ 22 (by decide +kernel)
private theorem reg37k2 : region H37 0x80011001080101010081001100099980 0x0 := regionFork _ _ _ 8 reg37k3 reg37k727
def prog37k1013 : Array Nat := #[0x30858134040004c4003090014a4135045402ed500a304dc10001290405281011604d411500bb54028c0e3040419281061604d01000131000ca40050904dc8000141002844011c50076b402d3d010434057b501c6940919d, 0x29010118320390100014198626e6189798624e6188b046081110bb88505e280930454101014a1442ec10116045410001090460c81171000050400521001f341320451030d440bb51028c137040105280411604dc100c24a, 0x33140102d039010115c288566e2159788564e2158b039410105ca0390100014198566e6159798564e6158b041cb1cb0a35b824dc158b02d410102b2040a28ab0a302d410001150417280b41000050400539001f3400c45, 0x78564de158b029010117b2885e6e21797885e4e2178b04de114f0c353c2ed4f0a353c24c0c404985e6e61797985e4e6178b03d0104f0bb03d8100c2c22bc28c0c29203dc100011503d9280f4040004c400509001b34009a9, 0x60c2ec115040004c4710cf88c28e2309388462c1318450c30d430bb50c28d4309304c611c11b370468dc118b04c610730a398c24e6118b0206100014d000ee40062900251400e3d0048b40e50403d7280f5c678566de1597, 0x33431ccd0bf3342bc0d50453430d4d0bf53428c0d4040004a400399001ae400995003424010910052341058c1ac33c6b0c71ac2fd630bb1ac28d6309358462c0f6041bc33c6f0c77846ac6f0a378c24de118b04461011642, 0x6846cda30af6846ada30a368c24da118b039a108d0cf23431c8d0bf6902bda122b69028c106a013433c4d0c71342fc4d0bb1342bc107342b433cad0c72b42fcad0af2b428c00304705acdc16af705aadc16a3041a80cd0cf, 0x78522c104a012433c490c71242ec490af041c90a90cf2a431ca90af2a428c0830442431d280c34a02ec1072432433cc90c73242bc10704000464003a1001854009090030f4010110052d401a0d0346106d0cf1b431c6d0bf, 0x48c30d230bf48c2ed230b71a42bd230a348c24d2118b0352112d0c34b42fd2d0bb6a42bda90a368526da14976a424da148b024810890cf22431d240c34902fd240bb2242bd240a30292112f0c34bc2ed2f0a378526de1497, 0x11c33c470c711c2fc470bb11c2bc00304404f2d013c7404eed013ab041c70c70cf31c31cc70bf31c2bc0038451c30d470bf51c2ec0e3840004a400399001a8400989003454010910052d401a25008034091841a433c690c7, 0x49c2fd270bb49c2dd270a3484e6d2139749c24d2138b030e10ed0c73b42eda70af684eada70a3684e6da139769c24da138b020e10870cf39031c870bf3902ec870af3848ac1071c29c33ca70c729c2fca70af29c28c1041c, 0x718419c33ce30c719c2fce30bb38c2dc670af3846ace30a719c28ce309338462c003843a431d270c3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg37k1013 : region H37 0x80011001080101010081001100099990 0x10 := regionTerm _ _ prog37k1013 adj37 _ _ 22 (by decide +kernel)
private theorem reg37k1 : region H37 0x80011001080101010081001100099990 0x0 := regionFork _ _ _ 4 reg37k2 reg37k1013
def prog37k1381 : Array Nat := #[0x30a48135000004c400309001484134004480ed1202b04dc00001210485081211204d0011203b4480ac0e3000499081261204d40000131000c840050904dca000149002854011bd0076b402d450104340578501cad4092a5, 0x29000127b203940000149981e6e60797981e4e6078b049ea14f03b7a805de051303d000121420484484f03b03d00000109049ec80f71400052400529001f341328041412d0503b4140ac137000145080511204dc000c2c2, 0x32f40102d0394000f5ca78166de059778164de058b039000125c20394000014998166e6059798164e6058b049cb1cb02b5b805dc058b02d000122320488288b02b02d000001110497080b51400052400539001f3400c3d, 0x88164e2058b029000117b2881e6e20797881e4e2078b04e2011104b4440ed1102b44405c0c50098226e6089798224e6088b0454005103b0458000c24a2440ac0c216045c0000111045908115000004c400509001b34009a1, 0x60c0ec0f4000004c46f04f78c0ade301778062c1318040c12d0303b40c0ad0301704c601c01b37006adc018b04c6007302b98c05e6018b0286000014d000ee4006210024f400e450048b40e400045708115be88166e20597, 0x50030d400bb50024c130800cc0ee6101798024c0e080000534003a90018840092d003834011c50058f41258c1ac13c6b0471ac0fd6303b1ac0ad6301758062c116001c413c7103f1c40ae201a388c05e2018b03c6000f64a, 0x78405de009378403c118000c413c3103b0c40be200a388405e2009388403c0308018413c2303b1840bc6102b18028c0b08004172a0102b02d000001410ac13d6103b58405d6009304c2010104b4040ed0102b40405c13080, 0x2340fc8d02f2340ac00300701acdc06af701aadc06a3049aa0cd04f33411ccd03f3340bc0d40043412d0d0474340ac0d50000048400399001ae4009910034240109500523401a05049e102f04f0bc11c2f03b0bc0bde102b, 0x6840bda102b68028da101768024da100f0346006d04f1b411c6d03f6806cda302f68c0ada01a368c05da018b039a00ad04f2b411cad03f6940bda502b680a8c126a813413c4d0471340fc4d03b1340bc1273423413c8d047, 0x1240fc4903b1240bc0030050130d404bf5012ed404a3049c90c904f32411cc903f3240bc0940042412d090474240ec0e48000048400399001aa4009890034440109500523401a050080d40d0800b413c2d0470b40fc2d03b, 0x4840ec2902f48028d2101748024d2100f0246006904f1a411d2303f48c0ec6902f1a40ad201a348c05d2018b029200a904f2a411d2503f4940eca902f480a8c1272422413c890472240fc8902f2240ac1252412413c49047, 0xc4804b40fd2d03b6a40bda902b68128da049b6a405da04936a403da048b6a401c090800a413c2904748030d2103f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg37k1381 : region H37 0x80011001080101010081001100089998 0x8 := regionTerm _ _ prog37k1381 adj37 _ _ 22 (by decide +kernel)
def prog37k1750 : Array Nat := #[0x880e6e20393880e2c1251c11c13c4703f11c0ec4702f049c708704f21c0fc8702f21c0ac0a3003a812d4703f51c0ec1271c31c13cc703f31c0bc12700000464003a900184400909003114010150052d401a2500803402685, 0x3a412ce904749c0fd2703b49c0dce902b480e6d27017480e4d2038b034e00ed04b3b411ced03b69c0bda702b680e6da7017680e4da038b01ca00a704f39412ce504729c0fce503b29c0bce502b020e00f104b3c40ecf102b, 0x1c2002704f38412ce104709c0fce103b3840dc2702f3840ace102738405ce009338403c0718019c13ce304b38c11c6703f38c0ece303719c0bce302b38c09ce301738062c09380]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg37k1750 : region H37 0x80011001080101010081001100099998 0x10008 := regionTerm _ _ prog37k1750 adj37 _ _ 22 (by decide +kernel)
private theorem reg37k1380 : region H37 0x80011001080101010081001100099998 0x8 := regionFork _ _ _ 16 reg37k1381 reg37k1750
private theorem reg37k0 : region H37 0x80011001080101010081001100099998 0x0 := regionFork _ _ _ 3 reg37k1 reg37k1380
private theorem safe37 : hostSafe H37 := regionHost _ _ _ bk37 reg37k0
def H38 : Array Nat := #[0x3, 0x4, 0x7, 0x8, 0xb, 0xf, 0x10, 0x20, 0x23, 0x24, 0x27, 0x30, 0x34, 0x40, 0x43, 0x48, 0x4b, 0x50, 0x58, 0x73, 0x7f]
def N38 : Array Nat := #[0x10101010011001100010110, 0x80000010109090001000900010908, 0x10101010001000100010100, 0x80000000100090011009900010098, 0x100010011001100010010, 0x100010001000100010000, 0x9090000009900008998, 0x10109090000000000018998, 0x10101010000000000010110, 0x10109090000000000010908, 0x10101010000000000010100, 0x9090000000000008998, 0x9090000000000000908, 0x11009900018998, 0x11001100010110, 0x11009900010098, 0x11001100010010, 0x9900008998, 0x9900000098, 0x110, 0x0]
private theorem bk38 : bookOK H38 N38 0x80080000010109090011009900018998 = true := by decide +kernel
private theorem adj38 : validRows H38 N38 := rows_of_book _ _ _ bk38
def prog38k5 : Array Nat := #[0xa240050104963000145048b38122ba02c602401ab90068e4018b04a2b00010d02c622421ab90868c128ac0004340b52054911d5240f02d0300012902d4300012100102400701002a5401491045630001490080c4052bd, 0x9022ae408a390222c9102f044622428ab90a28c9112f04a2b22459789163c1288c0004b4003090016041258c0005141224e0488e8051809022ae408a390222cb102f014622428ab90a28cb112f04a230b11af04a2b00010d, 0x4e40028d001244007010498306c0476006ec128b00004341260c23071c128b00004341224e0488e81160c0005240060c50d12d434470314800010d0310300012903143000121001444009810032b40168900ae5411180, 0x10c12c6c0476006ec0c18850c52d431470306208c1c703062000111000aa40048104a2c00010d0020b40c14e0304880a40060170d805bb60164d8058f029041845c36116ed8458f029031835c360d6ec0e52063970c10520, 0x60d60c1162c0004341160c0004b40c2ce030b280c2a20286206b14760d70d835bb60d64d835830004004b04b12c11d805c36016ed805930288208b14761170d845bb0394218e5c304142000139000a44005010022340c180, 0x53c52d4f14703162000129000c840058103d8b10f04b43c11c0f62c53c12d4f04703160000129000c840f62c53d12d4f447031680001290316a000121001004009090044440228d00c254051882ac71d835c360d6ed83593, 0x48400409001605eb233000802207ab881e8e2078b2440cc0c208889eae227a3031042287ab03144000121000a2400481049ec0001450022b40f24e03c8e80f60013c12c4f04713c0bc0f58843c52d0f1470204c80f62c, 0x10621e21b37886bde21ab78868c0b20c7ac6cdeb1ab7ac68c0820c7a06cde81ab0458a00f24e03c8e80c50c000444003210014b400789002a04127ac22c11de058b049eb08b14703d6414f44b53d11c0b4100004a40b510, 0x14822227ab889e8cb112f049eb000145000e340b20c2ac71deb1ab7ac68c115200004b40f59053d12d4f447045680001290456a00012100103400789003604014b103cb380f2ba010601e01b37806bde01ab78068de018b, 0x117ac63d70d8f59363d63d8f583045831ec1ab7b062dec183045ec00010d000eb40c2ca030a8811180881eae207a3881e2cb102f000001e01af7806ade01a378062c127ac00043400445044621e21af7886ade21a3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg38k5 : region H38 0x80080000010109080011008800008988 0x0 := regionTerm _ _ prog38k5 adj38 _ _ 22 (by decide +kernel)
def prog38k324 : Array Nat := #[0x31622226ab889a8e22697889a4c0c594895aae256a3895a4c0c590891aae246a3031682286ab0316a000121000a4400495001c2400a01049ab18d5c36356ed8d59363560c126ac0004c4126b00004b400545004af40250d, 0x789a8c0c2907b1abdec6ab7b1a8c0829043491de86af7a1aac0a2902b491cad22f02d44000115000c840f24e03c8e8004147a1abde86ab02d45000121000c44009b100302400f01031602206ab881a8e20697881a4e2068b, 0x6346edac1ab6b068da36136b062dac183034601a01ab68068da018b034621a21ab68868c0d40c6a06ac0d50c0004840028900120400731002d1400f2d014801e06b3781abde06ab781a8de068b014821e26b3789abde26ab, 0x58c5b46edab1b36ac6adab1a368d65da35936ac62dab183001832236ab88da8e2369788da4e2368b88da0c0c28c]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg38k324 : region H38 0x80080000010109090011008800008988 0x10000000000000000 := regionTerm _ _ prog38k324 adj38 _ _ 22 (by decide +kernel)
private theorem reg38k4 : region H38 0x80080000010109090011008800008988 0x0 := regionFork _ _ _ 64 reg38k5 reg38k324
def prog38k437 : Array Nat := #[0x7248cdc922f04a292092338248bc12890000504003390016041288058130d604bb04a201804c36012ec128a40004c40032d02928209733825cbc128b8000504128c00004e4004010024440113d00785403c09014a34063b5, 0x24a880f4804bc12d2f0477a40cde902f03d2412f44b4bd11c0a4900004840f24e03c8e9e92337a48bc107b84bd12d2f44703d4916f4c35bd2ec0c5240004b40032100144400a01049200890472240cc8902f0452400e24a, 0x88124c1228058130d604bf58124c0a4800004b4003c5048a40ab24759130d644bf03d2514f4cb53d31c0b4940004a56f4c3046051514cb04a0500014502d25000129000ef4007110454900012d002a04011310062e4092ce, 0x1004007b9002d14010bd02453809122045c516e4c35b924d6e4830458900012d038b280e2be044a01804c36012fd80493044a41844c36112fc1179463d30c118140004f4002910012040c2ca0452013104b4c40fcb102f, 0x4b52f14b4bc51c117085b930c118080004e62259788964e225830458900012d4c452c1272c5b930d6e4935b920c126240004b40510012c12d604c358124c126240004b40a4888248ce0922f0496400014104a0b000111, 0x45890092ce2c46bc1048c000455311bb8a46ae291a388d24e2918b8a460c1258c60d30d834bb60d24d8348302d232491ab92468e4918b92460c0b48c00052400431001d1400d3d03ca216f4c35bd2ed6f4935bd20c0f624, 0x7a5a2de9683031692296ab8a5a8e296978a5a4e2968b8a5a0c126ac5b530d6d4bb5b524d6d483049a218d4c36352ed8d49363520c126a40004c40042d001d1400b3d003c341148c7a46cde91af7a46ade91a37a462de9183, 0x928c4b471d2d1bb6a46cda91af6a46ada91a368d24da918b6a460c092907a5acde96af7a5aade96a3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg38k437 : region H38 0x80080000010109090011009800008988 0x1000000000 := regionTerm _ _ prog38k437 adj38 _ _ 22 (by decide +kernel)
private theorem reg38k3 : region H38 0x80080000010109090011009800008988 0x0 := regionFork _ _ _ 36 reg38k4 reg38k437
def prog38k676 : Array Nat := #[0x31610001495b830c0c58412c32c10284030b380c2ca030a88125840004c412804000454004890018e4009c5003c4401501045812418ab90628e4188b90620c12604000514116040005240052d00769402dbd00fad40560d, 0x264400c8102c2002b04b0ac11d600c35802ed60093049610122b20488100011504893a4158b02c8100014922c31d640c35902ec0c5849062ae418a3045c116e0c304601000139000b262159788562c12704049c5a4158b, 0x11240072d0034940b08048032d200c748030d200bb48024c0b20449032d240c749030d240bb049611320c74c830d320bb0396112e0c74b830c1182c024538091220460b0092ce024a8811804000454003090014e400749, 0x3a940128103d6112f0cb4bc31d2f0c34bc2ed2f0934bc20c127ac03cb38ab0c703d410001155bc30d6f0bb7ac28d6f09378562deb083045812417ab905e8e4178b905e0c1178463c30d8f0bb63c24d8f083045e1000131, 0x4b430d2d0bf4b42ed2d0930354116d0c35b42fd6d0bb6ac28da15976ac24da158b001812216ab885a8e21697885a4e2168b014811e16b3785aade16a3785a2c1268463430d8d0bb63424c126840004c4003bd001b1400a2d, 0x88c28e2309388462c001847846cde11ab78468de118b048611830c360c2ed8309304861000131000ef4006c5002a9400ead004e04019350342002d04b0b411c2d03f6840cda102f68409da00a368024c0d5844b432d2d0c7, 0x68462da308300c200600cf08c12c6104708c0fc600bb1840cc6102f18409c600a30496306b0cf1ac31d630c358c2fd630bb1ac28d6309358462c0310448c32d230c748c30d230bf48c2ed23093045810710cf1c42ee211ab, 0x146106d0cf1b431c6d0bb6846cda30af6846ada11a768c28da3093]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg38k676 : region H38 0x80080000010109090011009800008998 0x10 := regionTerm _ _ prog38k676 adj38 _ _ 22 (by decide +kernel)
private theorem reg38k2 : region H38 0x80080000010109090011009800008998 0x0 := regionFork _ _ _ 4 reg38k3 reg38k676
def prog38k910 : Array Nat := #[0x590e5d6438b04a251653c3594eed6538b04a221623c3588eec128b85b8f0c128c00004e400289001254007110028041161c91e2ae478a391e22e4788304587000149049870001450014b4012a5009614039bd01383406c35, 0x4c8eec11388588f0d623bb588e5c113884c4f0d313bb888e5c0c49c000514003ad02453809122038e512e3c74b8f0c118140004e40030900292400c91003e0412880580f0d603bb580e5d60393580e2c12890590f0d643bb, 0x904e2e4708301c200e00c33802ece009301c810e40c33902ec0e3843b830c103840004e40029100120400749002cb400f45014401203cb480f1d203c3480eed20393014821243cb490f1d243c3490eec122884c8f1d323c3, 0x30e42477ab91de8e4778b91de0c0f61c00052400445001cb400b25003c14113843c432cf10c33c42ee270a3884e5e27093884e2e27083048e11613c3584eed61397584e4d6138b584e0c122843c830cf20bb91c28cf2093, 0x3a9401281005e140f2843bc32cef0c73bc30cef0bb79c2bde70a33bc24de138b79c20c0f2884bcf2d2f3c74bcf0d2f3bb4bce4d2f38304a2f16f3c35bceed6f3975bce4d6f38b5bce0c1161c89deae277a389de2e27783, 0x48cf0d233bf48ceed2339304a231633c358cefd633bb58ce5d6339358ce2c0c38c3c46ee271ab89c68e2339788ce4e2718b01c831e71b379c6ade71a379c62c1238c60cf0d833bb60ce4c1238c0004c4003bd001b1400aad, 0x4c4003bd001b1400a2d00389401201005e3401e05014610670cf38c32ce30c738c30ce30bf38c2ec670af19c28ce309338462ce308301c600e304b38c11ce303f3806ec6703319c0bc6702738062c0518848cf2d233c7, 0x680e4da038b034a212d3cb4b4f1d2d3c34b4efd2d3bb4b4e4c128b45b4f0d6d3bf5b4eed6d3975b4e4d6d38b001872276ab89da8e2769789da4e2768b01ca41e76b379daade76a379da2c1269c634f0d8d3bb634e4c1269c, 0x3b432ced0c73b430ced0bf3b42eda70af69c28da139769c24da708f684e2da7083000e30ed1c73b46eda71b369c6bda71ab69c69da71a368ce5da339369c62da7183034e00ed04b3b411ced03f69c0cda702f69c09da0397, 0xd384]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg38k910 : region H38 0x80080000010109090011009900008998 0x100000000 := regionTerm _ _ prog38k910 adj38 _ _ 22 (by decide +kernel)
private theorem reg38k1 : region H38 0x80080000010109090011009900008998 0x0 := regionFork _ _ _ 32 reg38k2 reg38k910
def prog38k1200 : Array Nat := #[0x2cc522532b894c8c1259800051400331001ef40f5205bcd0d6f33b03d4818f34363ccec0a4180004c40032d0316614644b51911c107200004a4107280004840043d00245401789008a4402c8100e0940570d01e0d409a9d, 0x30c214614b51851d4613f030c20a6147030c2000115000aa40052d00208408314418b1de832b020ac80f514030b298f343028c5000131000c840f2ce03cae9e62af028c5165343594cec116180004b40c2ce030b280c2a2, 0x4f400445001eb40a410590d0d6433f590ced64317590c2c0c310890cae24323890c5e2430b048c4184343610cfd8433b049e6000131000f14006ad02cc210614b41851d0613f0204c80a308588d0d6233f588ced62317, 0x24b38092a2041c924932b924c8c107180005240031500264400e09004e04016c5006af40a400580d0d6033f580ced60317580c4d6030b030c022032b880c8e20317880c4e2030b018801e6033780cade0323780c2c12618, 0x49812d20343480ced20313000c2162343588ced62317588c4c0c4980004b40914e49852c09122048c40092ce2988bc092a2048c4000115490d0d2433b038c500e2ca4b8d0dc62af041250122b2924cac1031400052400339, 0x41871d0333f3206ecc81ab000c322332b88cc5e23313028c3000145000e84006b1003224012ad005a0401ba503d2512f3434bccede932b7a4c8d2f3137a4c2de9303041c922932b8a4c8e293178a4c4e2930b8a4c0c0b300, 0x30068cc018b0290316334358ccfd6333b58cc5d6331358cc2c051880305398334360cc4c061880004c46614730c4fcc21bb3086acc21a3018a300c2ce030b28a61c7030a880a40c0004558334360ccfd8333b60cc4c0830c, 0x5b4d0d6d33b0354818d343634cec0a4180004c40032d001454007bd002a4400e09004804017250072340928c49871d2334348ccfd261bb3246acc91a348cc4cc918b49860c0618019811cc303f3006ec660331980bcc01ab, 0xc00cd03f6980cda602f680cada0323680c5da0313680c2c0c3083344fda612f688cada2323688c5da2313000c41a62336988bda432b690c8da4317000c51e66b3799abde66ab799a8c0c314698abda532b694c8c0d520, 0x41c7000129000c8400515001e9400a8900384401201005cf401cb5008a340030c3346eda61b36986bda61ab69869da61a368cc5da331369862da61830352612d3434b4cfd2d33b6a4cada93236a4c5da93136a4c2da9303, 0x31c09ce0317380c4ce030b048c40e6247390d0ce433b31c89ce4317390c2c0030839852ce6147388d0ce233b388c5c00314498f2d263c7498f0d263bb048c50e62c7394d0ce533b041c61063cb418f1c10718518f2d463c7, 0x31c69cc71a338cc5ce331339862ce6183034e60ed3433b4cfced33b69ccada732769cc8da731769cc4da730b69cc0c0f3983bcd0cef33b79ccade732779cc8cef3173bcc4de730b79cc0c0030039812ce6047380d0ce033b, 0x730c39871ce334338ccfce61bb3986dcc71ab]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg38k1200 : region H38 0x80080000010109090011009900018988 0x10000 := regionTerm _ _ prog38k1200 adj38 _ _ 22 (by decide +kernel)
def prog38k1591 : Array Nat := #[0x31028c06284048b38122ba048ac8a60af041c1000115904cae41327904c8e4130b030c10ce0c37182bdc132733828c00304584d0d61317584c2c103040004b4003b9001b2400c91004b1401681006ef40211d009cd402e0d, 0x784cade132779828ccf093784c2de60830182002604b09811cc00c33002ec2602f30409cc00a330024c10704884cae21327884c8e21317884c4e2130b0148101224e904cae4130b0188100014931030cc40bb2182bcc1227, 0x30c27cc309330462cc3083030c10cd0c33342fccd0bb6982bda132b684c9da60a369827da131769824da130b69820c0030439832ce60c739830ce60bf3982ecc70a3384c5ce6093384c2ce608303ca10cf0c333c2ede60af, 0x518419833c660c730c30cc30bf30c2ecc30b71982bcc11ab30469cc30a3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg38k1591 : region H38 0x80080000010109090011009900018998 0x10010 := regionTerm _ _ prog38k1591 adj38 _ _ 22 (by decide +kernel)
private theorem reg38k1199 : region H38 0x80080000010109090011009900018998 0x10000 := regionFork _ _ _ 4 reg38k1200 reg38k1591
private theorem reg38k0 : region H38 0x80080000010109090011009900018998 0x0 := regionFork _ _ _ 16 reg38k1 reg38k1199
private theorem safe38 : hostSafe H38 := regionHost _ _ _ bk38 reg38k0
def H39 : Array Nat := #[0x3, 0xc, 0xf, 0x10, 0x13, 0x20, 0x23, 0x30, 0x33, 0x40, 0x4c, 0x50, 0x5f, 0x80, 0x8c, 0xa0, 0xaf, 0xc0, 0xcc, 0xf0, 0xff]
def N39 : Array Nat := #[0x1000000001001000000010000100100000000000110010001000100011000, 0x1000000000001000000010000000100000000000100010009000900090008, 0x1000000000001000000010000000100000000000100010001000100010000, 0x1001000080010000100100000000000010010000000900009008, 0x1001000000010000100100000000000010010000000100001000, 0x1001000000000000100100000000800110010000000000099008, 0x1001000000000000100100000000000110010000000000011000, 0x1001000000000000100100000000000010010000000000009008, 0x1001000000000000100100000000000010010000000000001000, 0x80010000100100000000000000000009000900099008, 0x10000000100000000000000000009000900090008, 0x80010000100100000000000000000000000900009008, 0x10000000100000000000000000000000100000000, 0x800110010009000900099008, 0x100010009000900090008, 0x800110010000000000099008, 0x100010000000000010000, 0x9000900099008, 0x9000900090008, 0x9008, 0x0]
private theorem bk39 : bookOK H39 N39 0x8001000000001001000080010000100100000000800110010009000900099008 = true := by decide +kernel
private theorem adj39 : validRows H39 N39 := rows_of_book _ _ _ bk39
def prog39k5 : Array Nat := #[0x4193810646001881ec6af7b1a9dec68b0350200013d03d0200013500130400eb902d2816d4c35b52fd6d4bb5b522c0040858930d624bf5892ec0b4a0000424003b50250200012d02d020001250022c40222900f67406d19, 0x6352fdc96a303d28000135000cb40c5886356fdcb6a30310200012d03d680001350010940e64e0399180b4a05c12fd704b75c122c0d4a06352fc0f4a00004d4002ad001881ec6af7b1a2c0d5a00004f40f5a00004d400425, 0x825abd4d4a303568000125000cf40b4a05c12fd7048b03d2800012d03d680001250010d41054e041518005207a9acdea6af7a9a9dea68b0350200013d03d020001350015040103902d2816e4c35b92fd6e4b75b922c0c488, 0x4a4004090030c4018210352214d4bf725abdc96a302d2816e4c35b92fd6e48b03d2800012d000ed4005207a9acdea6af7a9a2c0d5a00004f40f5a00004d4004a50395380e546001481ea6b37a9abdea6a77a9a2c0d488, 0x3b451d8d13f69c4bda23ab69c49c0f69c0004240f3880004d4005b9030f08103883a451d2713f488eed27137000e20ed14769c4bda23ab02ce214713f02ce2000129000ad40052502d271474bf51d2dc0b51c0004940b49c, 0x399380c3c203962000131438f2d0e3c7045e21113cb049e2000145030f0811588444f2c12588000514002b10016e4009a90038d4012a503da71c76af71da9c0f38871c4bdc712703dc7000109000cd40e64e0399180c388, 0x2cc200012900108400e310084940339d02d220103b203d22000141424f2d093c7424eed093b7424eac0f688030f080d5880004c50d3cb434f1d0d3bb434eac0b508041538103b203d42000141428f2d0a3c7428eec0f708, 0x49eb000139000aa40f598000484005b50031140c34e0356210d34b434d1d0d33b434cac0b508428d2d0a347428cec11588444d2d1133b0396210e34b04962000139000b14004a9001cd40b3085994fd66537028c200012d, 0x1ab4009a1003cd4117ac444d2d11337444cac0f3083444dcd112f03da6000109000c84116420458e8126ac6356fd6d33b6accada658b0358210d34b434ced0d32b03da6000121000eb40f5a8428d2d0a33b03dcb10e34b, 0x4b4ceda932f6a4cada64a369922c0041859930d664bf59922c0c4880004b50934b424d1d0933b424cac0001859930d664bf5992ed6648b024c21464bf031260116420458ea2648b03d26000145030d38093080004c400529, 0x2d220e934b3a4d1ce933b3a4cdce932b035620ed34b3b4d1ced33b3b4cac0b5083a8d2cea3473a8cec0e5883b8d2cee347045620f134b04962000145000ae4004a9001cd400a2501ccc80c498]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg39k5 : region H39 0x8001000000001001000080010000100100000000800110010009000800008000 0x0 := regionTerm _ _ prog39k5 adj39 _ _ 22 (by decide +kernel)
def prog39k353 : Array Nat := #[0x409380f48842492d092474248ed0922b03dc210e24b43891d0e22b045e211124b4448ac0f50842892c127880004a4002c50012e40072503c821e472f791c9c0e2080004f40f2080004e4004210039040213500ce7404199, 0x2c8209113f24449c0b490000424003210460c81182a049e92097af4bc8ede922b79122c0b48842492d0923b4248ac0b490000484003bd03dcb10e24b4388ac0f5a842892c127ac0004a4002b903d6400012100169400c45, 0x791abde468b0356200013d43492d0d2474348ed0d22b000041e46b3791abde46ab791a2c0d208711abc005900460c81182a891a2c0d5900005141024e034820001410014e4006bd00268400f25045eb11124b4448ed11227, 0x3b48eced22b3b489c0f4883a492ce92473a48ece922b03dc20ee24b3b891cee22b03d420ea24b3a891c117883c492c12788000514002a90012e4007250028d407242041a412d23f4b48eda922b69128da448b001041e46b3, 0xf5a432492cc92473248ecc92373248ac0f6ac33492ccd2473348eccd22b045eb0d124b3448ecd122b03d6a0ca24b3288ec0f72c33892c127ac0004e4002a9001314007350028940624e0188780f6883b492ced247]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg39k353 : region H39 0x8001000000001001000080010000100100000000800110010009000800088000 0x80000 := regionTerm _ _ prog39k353 adj39 _ _ 22 (by decide +kernel)
private theorem reg39k4 : region H39 0x8001000000001001000080010000100100000000800110010009000800088000 0x0 := regionFork _ _ _ 19 reg39k5 reg39k353
def prog39k512 : Array Nat := #[0x1442bc0f4040455081153a03d010116420458e80b4040004c4003290014240810414c2fc530af03d0101354204d4e80f40404d9081363a02d01000131000ca40050903d6800014d00211400f99006e4402b1d00fcd4055a5, 0x4c908115900005340053d001e8400c1902c4101333203d6100014d404d2d01347404ced0132b04d660cb0c75982fd6133b0184101354204d4e9460bf0184100012904ccc8117980005340052d001e840810414433c510bf, 0x30f080b3840004c400529001a84009890032640101103d6100624e30492cc12473048ecc122b03c4101324203d6100014d40492d012474048ed0122b04de408f0c77902bde122b0104101373204dca9c40af01041000139, 0x48440f10438492ce124701c908e123b3848ac0721a02c410e134b384d1ce133b01ccc8e132b020e10470cf11c31c470bf11c2bc0c584404f2d013c7404eed013ab02ce11470bf030e100e64e039919c70af03ce1000139, 0x684eada70a369c26da138b034c100c34e6342fc061040004c4cd0c76982bda132b69828c0d40413433c4d0c71342fc4d0af001011e16b3785abde16ab0310110d0c76a02bda142b03561000121000ef40060900246400e1d, 0x25010490cf12431c490bf1242bc0040458530d614bf5852ec0940442431d280bf4850ec0f484000484003ad001824009110038d40119d0058641369023431c8d0bf6902bda122b69028da409f69026c0c3843b431da70af, 0x4d260c90c74982fd2133b4982dcc90af49828d2609f49824c103843a431d270bf484eed270b749c28d27093484e2c0d4844b42fda90af6a428da909368522c0920404093a090af0104100014122431d240bf4848ed240a3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg39k512 : region H39 0x8001000000001001000080010000100100000000800110010009000800089000 0x1000 := regionTerm _ _ prog39k512 adj39 _ _ 22 (by decide +kernel)
private theorem reg39k3 : region H39 0x8001000000001001000080010000100100000000800110010009000800089000 0x0 := regionFork _ _ _ 12 reg39k4 reg39k512
def prog39k736 : Array Nat := #[0x409381021e048a2000141000c640053d02ca20cb2cb6156fc126080004b40c34e030c78126147b0abdec28b02d0501064e041878122880005040033d001464125880004c400a1100471401db900b4a40413501569406f85, 0x31140f2880459080b2880004c6458a391627e4589b91624c116082c44be2511f888a4c11610030d38d12af030c78117940004641164204564000131001424007c9048a41e42b3790abde428b0496500624e01887812594, 0x26f400cc50040e40b288045cca25723895c7e2571b895c4c0f5940399380b2880004c645723915c7e4571b915c4c0e62c71566dcb2935b8a2c0e610030f08ee28b030e680f7140004740e64e038820001310014b4007c9, 0x71547dc551b71544c0f28804550a2552389547e2551b89544c125147a8acdea2af7a8a4dea28b02ca224552391547e4551b91544c0a288328abc0b514040ec8103923a8a2c0b5140004741054e028a2000141001464006c9, 0x69547da551b6a8a2c0d608334b2ccd2c7334aeccd2af0358b0ed2cb3b4b1ced2bb3b4a2c082882b451da22b36944bc0d62c434b2d0d2c7434aec0c59400048400389001874009190030a40101103d6500e54e039519c5523, 0x5952fd654bb59522c0c488424b2d092c7424aed092ab001251e92b37a4aade928b024a200013d000e84006ad00267400d19004244014b5034a40ad24b2b491cad23b690acda42af6948ada428b001451aa2b36a8abda5523, 0x6894004944b4aeda92b36a4abda92ab69528da549f69526da92936a4a2c0b4942a492ca92474948fd2523b2a48ad2428b031220c92cb324b1cc92bb324abcc92ab031690e92cb3a4b1ce92bb3a4aace928b001051654c3, 0x384b1ce12bb384aace128b030410c12cb304b1cc12bb304abcc12ab020a10450cf11431c450bf1142bc0c584404b2d012c7404aed012ab000a11e12b3784abde12ab02ca100013d000e840068900266400d1d004244014b5, 0x24a10a90c74942fd212bb4942dca90af49428d2509f49426d25093484a2c002842b431da12b36942bda12ab69428da509f69426da5093684a2c0510428492ca40c72142fca123b2902bca122b031610e12cb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg39k736 : region H39 0x8001000000001001000080010000100100000000800110010009000900089000 0x100000000 := regionTerm _ _ prog39k736 adj39 _ _ 22 (by decide +kernel)
private theorem reg39k2 : region H39 0x8001000000001001000080010000100100000000800110010009000900089000 0x0 := regionFork _ _ _ 32 reg39k3 reg39k736
def prog39k1022 : Array Nat := #[0x30c78121880004c4003110014b41258c5c06fd7018b049e300012d0409381021e049631701bf5c062c0f40c0419381061e04862000131000cb400511049e2000141002864011c50076a402d39010454057b501c69409185, 0x2c6201183203c6200014190e28e4389f90e26e438930460207113f88c47e2219b0456301024e2446fc1021e045630001110460c81179800050400509001f241230c59870d661bf59862c1278c0189380621e049e300c34e, 0x33140102903c6201154288d48e2351f88d46e2351303d6301054e03c6200014190d48e4351f90d46e43513041ea14f19b78d44dea18b02d430103b2040e48ea18b02d4300011d0415380a3080005040053d001f2400c45, 0x70d46dc351302c6201173288dc8e2371f88dc6e23713049c316e1c35b86fd6e19b5b862c0c18890dc8e4371f90dc6e437130386208e1bf0398300c3c23b862c0c39a03dc300011d0399380e1880004c400511001b24009ad, 0x6146fc1158c0004c4b11cb89466e2329389462c1228c59470d651bf59466d6518b048a31e32b378ca4de328b048a324519b90ca4cb218b01462000149000ef40062d00251400e390048a40f58c0395380e54670d48dc351f, 0x43471d0d1bb4346ac0d50c5b470d6d1bb5b462c0d1880004b4003a1001af40099d00344401099005254105142a872caa1c75146fcaa1bb51466d432932a862c0e60c2b872cae1c770cabdc519b70ca4cae18b044a3011642, 0x68cacda32af6946ada519b68ca4da518b03da30cd1cb33471ccd1bb68ccbda61ab69862c1068823472c8d1c72346fc8d1bb2346ac107b43b472ced1c73b46eced1ab3b462c0040c78dacde36af78daade368b041a210d1cb, 0x4b862c1048822472c891c72246fc891ab041e90e91cb3a471ce91ab3a462c081881a451d221c348c4fc107a442472d091c74246ac1078c00048400389001874009110030e4010190052d401a15034a30ad1cb2b471cad1bb, 0x49470d251bf4946ed251b72a46ad2519b48ca4d2518b0352312d1c34b46fd2d1bb6a46ada34a368d27da919b68d24da918b024c30c91cb32471d261c34986fd261bb3246ad2618b02d2312e1c34b86fdc34a370d27dc3493, 0x20472c811c72046fc811bb2046ac0818410c33c430c710c2fc430af041e11011cb40471d011bb4046ac0018458470d611bf5846ec0f1840004b4003a1001a2400991003474010990052d401a250080540928c2a472ca91c7, 0x48c2fd211bb48c2dd230a348c27d2309b48c24d2118b0306106d0c71b42fda30af6846ada30a368c27da309b68c24da118b00c410c11cb30c31c660bf3046ecc30af3046ac1078438472ce11c73846ece11ab38462c10104, 0x518428472ca30c71942fca11bb28c2dca30af2846aca30a719426ca309328462c001841a431d211c3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg39k1022 : region H39 0x8001000000001001000080010000100100000000800110010009000900099000 0x10000 := regionTerm _ _ prog39k1022 adj39 _ _ 22 (by decide +kernel)
private theorem reg39k1 : region H39 0x8001000000001001000080010000100100000000800110010009000900099000 0x0 := regionFork _ _ _ 16 reg39k2 reg39k1022
def prog39k1390 : Array Nat := #[0x1c9080721a049e000c3c2030e68125800004c4003110014241210014c0fc5302f049e001324204c8680f40004d9081361a04960000131000c4400509049eb00014d00207400fb9006ea402b4500fc540558d01c2d4090a5, 0x5340053d001f2400c3902c4001373203d6000014d901c8e4071f901c6e4071304dcb16e03f72c07dc059b0384001324204c8688e03f0384000011104dcc80f71c0005340052d001f241210011c13c4703f11c0bc12780, 0x4c400511001b24009890032e40102903d6000e54e70148dc051f70146dc051303c4001354203d6000014d90148e4051f90146e4051304dea1ea02f53c07de05130284001333204cc48ca02f0284000011904d5080b51c, 0x455081153a88148e2051f88146e2051302c40011732881c8e2071f881c6e2071304a2005104f1440fc5102f14407c0c58090228e4089f90226e408930456009103f0458000c34e3440bc0c31e045e000011904590811580, 0x880a4e2028b038a000e64e6140fc0e1000004c4ae04b7140bdc501f700a4c1228011413c4503f1140bc4501f048a01e02b3780abde0293048a00b202f91407e4029302ca0000149000ef4006090024e400e450048a40f100, 0x10c0fc4302f10c07c1218058070d601bf58066c121801c80fe4301f90066c0f180000524003ad00182400929003854011c50058e4135142a812caa0475140fcaa03b2a80bd4501f500a4c116002c412cb103b2c40be2501f, 0x1b811c6e03f70c0bc6e02b70c07dc019b70c05c118001c412c7103f1c40ae2301f88066e2301788062c0518028c12c6503f28c0bca302b28062c0a18004153a0302f028400001411a812d4303f50c07d4019b0486004304f, 0x2340ac137b433412ccd0473340eccd02f3340ac00400781acde06af781aade068b04dab10d04b43411d0d03b4340ac0d10013413c4d0471340bc0d580000424003a1001af4009990034440109d00525401a0d04dc306e04b, 0x1b412c6d0471b40fc6d03b68c0bda302b68c07da019b68c05da018b034a00ad04b2b411cad03b680acda502f6940ada501f680a4da028b03da00ed04b3b411ced03b69c0bda702b680e2c136ac23412c8d0472340fc8d03b, 0x3240ac135a422412c890472240fc8903b2240ac0040058130d604bf5812ed6048b04de910904b42411d0903b4240ac0910012413c490471240fc0f480000424003a1001ab4009910034640109d00525401a0d0080d40d180, 0x1a412c6904748070d2303f48c0ec6902b48c07d2019b48c05d2018b024a00a904b2a411d2503f4940eca902f2a40ad2501f480a4d2028b02d200e904b3a411d2703f49c0ece902b480e2c137a432412cc90473240ecc902f, 0xc4804b40fd2d03b6a40bda902b68128da901f68126da901768124da900f68122c09180]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg39k1390 : region H39 0x8001000000001001000080010000100100000000800110010009000900098008 0x8 := regionTerm _ _ prog39k1390 adj39 _ _ 22 (by decide +kernel)
def prog39k1755 : Array Nat := #[0x88028e2009b88024c1358420412c8103f2040ec8102b04de10c104b3040ecc102f3040ac0b4000ac13d6103f5840ec1378440412d0103b4040ac13780000484003ad001864009110031140101d0052d401a250080540268d, 0xa413c290474840fd2103b4840dc2902f48028d2101f48026d200930342002d04f0b411c2d03f6840bda102b68028da101f68026da00930082002704f38412ce104709c0fce103b09c0bce102b0082003104f0c40fc3102f, 0xc2002304f18412c610471840fc6103b1840dc2302f1840ac6102708c07c6009b18405c0508009413ca104b28411c2503f2840eca10372840bca102b28409c2501f28024c09080]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg39k1755 : region H39 0x8001000000001001000080010000100100000000800110010009000900099008 0x1008 := regionTerm _ _ prog39k1755 adj39 _ _ 22 (by decide +kernel)
private theorem reg39k1389 : region H39 0x8001000000001001000080010000100100000000800110010009000900099008 0x8 := regionFork _ _ _ 12 reg39k1390 reg39k1755
private theorem reg39k0 : region H39 0x8001000000001001000080010000100100000000800110010009000900099008 0x0 := regionFork _ _ _ 3 reg39k1 reg39k1389
private theorem safe39 : hostSafe H39 := regionHost _ _ _ bk39 reg39k0
def H40 : Array Nat := #[0x1, 0x2, 0x4, 0x8, 0x10, 0x11, 0x12, 0x13, 0x18, 0x20, 0x21, 0x24, 0x25, 0x28, 0x39, 0x40, 0x42, 0x44, 0x46, 0x48, 0x5a, 0x6c, 0x7f]
def N40 : Array Nat := #[0x1000040001550000011101050114, 0x1000000001110200013301030112, 0x400010502000103010f0106, 0x5500000033000f0016, 0x1000000001550000013300000116, 0x1000000001550000011100000114, 0x1000000001110000013300000112, 0x1000000001110000011100000110, 0x550000003300000016, 0x400015500000000010f0116, 0x40001550000000001050114, 0x400010500000000010f0106, 0x40001050000000001050104, 0x5500000000000f0016, 0x550000000000000014, 0x2000133010f0116, 0x200013301030112, 0x2000103010f0106, 0x200010301030102, 0x33000f0016, 0x3300000012, 0xf0006, 0x0]
private theorem bk40 : bookOK H40 N40 0x800010000400015502000133010f0116 = true := by decide +kernel
private theorem adj40 : validRows H40 N40 := rows_of_book _ _ _ bk40
def prog40k8 : Array Nat := #[0x64173c1389c64d74c1489c000534002c1041871d06c70458700014103587000139039870001350012b400949041671d06cb741b1c1159c745b2c1259c000514002c10356700013903967000135001ac4016a100ac6405aa9, 0x475885d362173c128ac8a167c1259c000514002b1031072488bb9222dc1261c0005141161c0005240042d002b041073464174d905cf039ac00012d04dcd1935d3051cd00014d039ac00012d000f041261e046071905d3, 0x5140d6180004e4003c10398600013500188400f1d0074b4105a06c167e0b4330418700012d6c112db04470416720b4330418700012d74112dd044702d0720b4330310700012d000ae4006350010700c3ca42cf1c0e6a0, 0x55c800014d048ec8138303ccd5c15830000534002c9001714009b5045061b144b6c510c0e4180004d511333041061b044b834ccc1061874112c0c4180004e4002b5049860001410017140e698834ccc11618745b2c12618, 0x496600014142cd1c11598745b2c125980005140d5980004e5a65c303966000135001484009b10032740c398030f29a6643039a80001313b4d5ced34f3b4d1c11730030f2a26623045c80001313c4d5cf134f04dc80f3357, 0x4e471735530524700014d0494700012d000ec4006450032840171900ad040039861974c0c3ca61970d865a3039680001313acd5ceb34f3acd1ceb337039a61865d361973d865c361968c1059874112c0b4180004e60b337, 0x515685535a153c1252054911c1261e0450700014962154d8854f0454715144b04947000145000ac4006ad02d471513cf048ec80c5a80004764a8bb92a2dc149c49aa27c1489c000534002c904e471935530524700014d, 0x30f28117280004c4f13570394618655303946000131000a755134f8a8cde26523048e618655361953d86523028e61a654b04e4a0f33570564a00014d0494600011d000ed400531001f1400f2d0454815144b8a167c1241c, 0x4147000139000cd5705535c153c0c51c8aa0ee2a83704a0719055364153c0051c92a0ee4a83704147000149000cc400545001cb400d99005884123983acd5ceb3473accdc128980004756655359953d66523044e6186553, 0x414600011d828cdc1051c0004655044b54111e0a4338290bc0a398544d3e2a83b04dca0f3357055ca00014d0394600011d74152c0a3980004e400545828cde0a333828cbc105a86c152db05476c167c1051c74152dd0547, 0x4e0a0f33570560a00014d]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k8 : region H40 0x800010000400015402000132010c0000 0x0 := regionTerm _ _ prog40k8 adj40 _ _ 24 (by decide +kernel)
def prog40k332 : Array Nat := #[0x62154c149140004841261e049aa0001316c946c126b00004a40d628000524006d50558a00c3ca048c518655361948c1241462154c14914000484002990564c000129001674159280004c40083500513401ec100d6b405645, 0x49241351454cb2e6a33304e4c00012934cb5cd32b7048e526592b048ec8149a0000524f32d73ccadc0c51454cb2c126140004a40029d001a641241462154c125140004c4126140004a414914000486a569fa95a6c12414, 0x40e50001199960ce6582b041a50cd2d7834cce0d32b0560a20a3330560c000129000ad41039464154d90523041aa0ed2d70560a0001350414500011d000ec4106b03b4b5c158300004d410614000474003a900246400e4d, 0x1051685535a153c0c5940004a50b2cb04d4517355354cb2c1391464d74c125940004c4002a90524500014d0016840091d003664014c1030c51902cf049878073140004c64583b9160de4582b91608c1381434cb5cd32b7, 0x3acb5c1071464174c0e5940004c40029d0018a4008195c0b3e0b2b781568c0b31442cb2d0b33342ccac0e594a2ccce8b32b04966000151000c84cb2d732cb3ccb2b70496a0123b291568c145a0000524eb2d73acb3ceb2b7, 0x4545000131544b3c116140004a5112af04e251935d3045650001310458500012d9962ac148940005340052100272400c9d004b0401819039650cb2d782ccce0b32b040e5170553540b2c1039464174c0c3ca03965000131, 0x344b5cd12cf344adcd12af030e50f12d73c4b3cf12af0316500011d8960ee258378960ae25823000e52458bb9162ae458a3048ec8148a0000524f12d73c4b3cf12b73c4abc0c5949162ee458b79162ae458a304505188553, 0x11314444b2d112c3444ccd1132b052261512cb544b0c11614744b2dd12c304585000139000ca400521]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k332 : region H40 0x800010000400015402000132010e0000 0x20000 := regionTerm _ _ prog40k332 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k7 : region H40 0x800010000400015402000132010e0000 0x0 := regionFork _ _ _ 17 reg40k8 reg40k332
def prog40k571 : Array Nat := #[0x30e3000139000cb400535001e840038c030f28eb1c7039a300011d60d74d835cf60d68c128ac88d68e2359f04967000145000cc40c38c90e2ee438b790e28c1261c0005141161c000524004ad0031040169900a0a403a15, 0x33071d861c3039030e335738cd3ce3347040c31101cb44071c0e30c000484128980005040041d001ac400b350038b41038c44072d101c74406cd101af0418b1b01cb6c071db019f0396320b1b35c067c1061c74072dd01c7, 0x9a86be6a19f052231511cb8a867c1251ca286ce8a1af048e3000151000d140054d001e8400ac10038641259858cd3ccb1c759870ccb1b359867c0c30c69872da61c769870da619f030c30e3357030f28126180004758334f, 0xa9467ea519b031431432cb04983000129000b540063500233400bc10042b401645028e614334f51872d461c751870cca1b33286bc1051c54072d501c78286ce0a1af80d48c0a38c42872d0a1c74286cd0a1af04a2a26a1b3, 0x2ca310b1b342c6ac1428c000485632cf2ac72d651c359467d6519b040a30c32d730cb3c10394000464b01cb80cade051b38146ac1228c9946ce651ab99467e6519b031451a51cb69467da519b031451432cb04985000129, 0x45850b11cb2c470e232b72c46be251ab89467e2519b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k571 : region H40 0x800010000400015402000132010e0100 0x100 := regionTerm _ _ prog40k571 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k6 : region H40 0x800010000400015402000132010e0100 0x0 := regionFork _ _ _ 8 reg40k7 reg40k571
def prog40k739 : Array Nat := #[0x5240032d001514007c103dc700c3ca7acedc0f7340004758f5d363d73d8f5c3039ab1af5c36bd67c0e59c0004d40033103d871cf6cb73db1dcf6c303587000139039870001350012b400c21005a640282900fa5405e8d, 0x79988c0f7203bcd5cef34f3bccdc0f4186bd12daf44303906000135039a6000121001074006b1002d1400e2d001072087bb821ede087b3821ebc0c5a08a1eee287b78a1e7c127ac7ad0cde859f031072487bb921edc0f61c, 0x316a18f5530498780b51c0004c64a7bb929edc1479c0005240054d001f1400a21003504010990396616f34f7accddeb33379968de659f001862267bb899ede267a3899e7c0f7303bcd5c0c3ca0398600011d63cd3dec337, 0x4f14017ad055ea1cf54b73d50c0a3980004e54f34f53cd1dea3377a8ccdea32f79948c0051c829eee0a7b7829ece0a7af829e8c0f51c53d12d4f4477a90cdea42f0316a22a7bb8a9ede2a79f039aa26a7b39a9ebe6a79f, 0x49e52657b3995eae6579f995e6c073143bcb5c123b2030c500011d915eee457b7915eae457a303d8a0cf2d733cadc147a03bcb5cef2b703d4518f55363d48c0f5140004c40f6140004a40041d0018640084900353401041, 0x3a64014290064540f5145bd54d4f2cb53cb1c1479473cb2dcf2c703165000139000ca56f2cf5bcb0deb2b779568de559f79566c00614895eee257b7895eae257a3895e7e2579b01cc52057bb815ede057b3815eae057a3, 0x78ccdde61b37986bde619f03ce310f1cb43c71d0f1c343c6cd0f1af000e32037bb80dede037b380debc0e38c3bc71de33b779c6cde71af03d8b1af1cb6bc71c0f62c73c72dcf1c703163000139000cd40051d00210400b21, 0xf28c2bc72caf1c72bc70de32b77946cde51af7946ade519f79466c0f50c53c72d4f1c753c70dea1b37a86bde35237a867dea19b03cc310f1cb43c70c0e30c000484cf1c7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k739 : region H40 0x800010000400015502000132010e0100 0x10000000000000000 := regionTerm _ _ prog40k739 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k5 : region H40 0x800010000400015502000132010e0100 0x0 := regionFork _ _ _ 64 reg40k6 reg40k739
def prog40k988 : Array Nat := #[0xd140052d001ea40b49c4c4f3c123b20316900011d9262ee498b79262ac149c49a62ae6989f0522700014d000d241249ca266ce899afa266ac1391c0005441491c000534004c50030840169500a10403e99017a3407d3d, 0x51280e92d73a4b3ce92b7001051484d352133c0c4940004a4149940004840041d001b2400b2d0039140041c52134d484cf52132d484c704a281684d35a133d6849f0458913144b8a127c1241c62134d884cf04927000131, 0x74132dd04c70312700013964134d904cf039270001310014d4007ad00288400d29004254148944c4b3d312cb8a4ade254a389527c1249459534d654cf59528d6549f049490e92d7048ec814914000475322cf924ade454a3, 0x5f1415824a260ce8982b040e50001514c0b3d302cb4c0b1e092b7824abe054a3041271504d354133d504cb54131d504a30412713044b4c111e094338250bc128c05c134d704cf5c127c106246c132db04c76c127c1049c, 0x69932da64c369927da649701cc50e9357030f2812314000475864d361933d864c361928c12824324b5cc92cf039280e93573a4d3c004989260ee498230412600014904926000141001074006150020c400d350040a4013ad, 0x5104019190012622983b824cce0932f03926289333a24cbc0e498000544003414c4d3e293378a4cae264a389927e26497049261664d359933d664c359928d6649f59925c0731451934d464cf51932d464c351928c0c498, 0x49471ca91af49467c0938c42472d091c74246cd091af4246ac0038c50d34d434cf50d32d434c7050e31233cf49c72d271c73a46bc1288c58d34d634cf04a231834d360d33c128a40004c40032d00147400829002c8400e95, 0x290400d290042840151900685401f8d024c312334f49872d261c749870cc91b33246bcc91ab49867d26197041231301cb4c071e091b38246be091ab80d28d3019f82465c0928c4246cd091ab050a300012148cb3d251cb, 0x7a50ade849f03d2714f4d353d33d4f4cb53d31d4f4c3001272097bb825ede097b3825ebc0f49c63d34c0c3ca039270001314bcf3d2f3c77a4edde93af04a2f16f4d35bd33c0f6246bd32daf4c703989000135000cb40051d, 0x7a46cde91af7a46ade34a37a467de919b7a465c147944bcb3d2f2cb4bcb1d2f2c37a4adde92af79528de549f79526c0e4984bcd3d2f3477a4cdde93337a4cbde932b79928de649f03d2812f44b4bd11d2f4437a50cde942f, 0x3d2312f1cb4bc71d2f1c3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k988 : region H40 0x800010000400015502000133010e0100 0x100000000 := regionTerm _ _ prog40k988 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k4 : region H40 0x800010000400015502000133010e0100 0x0 := regionFork _ _ _ 32 reg40k5 reg40k988
def prog40k1312 : Array Nat := #[0x146400795030c419024f049878073100004c64483b91208e448170567026483399205c1583000053400349049842a499fa9266ea499704e4c0001550564c00014d00130400c35005aa40284500fab405e8d01f4f40a2a5, 0x61154d8454f61148c0d5102b495cad24f028e40001150566a0001350010c4006c9002c6400e41035840ad2572b493cad24b2b490c1283433495ccd24f3348cc103906c092e0d233049ac0ed2573b493c1261000047400341, 0x74490c0c3900004e4f12573c493c0e61000047400521001e6400a35003454010a90560a15024f54092e0a2378288ce04523049440ca25732893cca2373288cc1229061154c1261e0564a00013154893e4a23791148c07290, 0x52242a489fa9225c148900005555124f54492d512438a88de2452389146c116102c495cb124f2c492cb12432c48dc116106c492db1243891a7e2469b04a300d125734493cd1233044e411124b44490d11233045841d124b, 0x42c91d0b23342c8ac0039061174c0c3ca0496a0001313ac95ceb24f3ac91ceb23704a2416455359153c0e69061174d845cf001642448bb9122dc1159000052412590000514004310018a40081d00348401015004e64017c1, 0x64b4005908920ee2459f89166c0e590a9167ea459b03964000155000d157024f82c8de0b23382c8ae045a381165c1259032c95ccb24f32c91ccb23732c8cccb22b0316a0ab2572ac93cab24b2ac91cab23702ce410b24b, 0x2286cd4419b030830a325728c93ca324b28c90ca3237030831a41cb69070da419f69066c1560c60c93c8c1cb61070d8419b04a030c325730c93c1280c38c95ce324f04a0400011d000c64005310020d400b15003aa401445, 0x3454010b50054b401a29007e340b20c58c93c8b1cb22c71d641c322c6cc8b1ab59067d6419b59065c1120c24472c911c388c8dc911b38906ae2419f89066e24197028830a325728c8dc0a3900004554324f51072d441c3, 0x791a5c0f6102bc95caf24f2bc92caf2472bc90c00610891eee247a3891e7e2479b03d840ef257030f280e6100004758f24f63c90de462379186c1283c33c95ccf24f03ce410f24b43c90c0e390000484003190014c400a45, 0x7906cde41af7906ade419f79066de4197055ea14f24f53c92d4f24753c90dea2377a88cdea22f79148de451b0396416f24f5bc90deb2377ac8cde45a379167de459b79165c0f4106bc92daf2476bc90ded233791a7de469b, 0x59125c0e4903a495c123b20524400011d9248de4922b91128e44497031490a92572a48dc093904248cd0922b050e4000121000c54005490028b400d190043340154500690401f8d0096f40f20c23c72c8f1c723c70de3237, 0x8248ce0922f8248ae044a381125c148904c493d3124b8a48de2922b89128e2449f89126e244970250413324b9a48ce6922f9a48ae6449f99126e64497049240c92573248dcc92333248bcc922b049241644d359128d6449f, 0x392412f24f4bc92d2f2474bc90de92377a48cde922f7a48ade44a379127de449b79125de920f0248312324f49072d241c749070c891b32246bc891ab49067d2419b49065c158244c093d3024b4c091e09237]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k1312 : region H40 0x800010000400015502000133010f0100 0x10000 := regionTerm _ _ prog40k1312 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k3 : region H40 0x800010000400015502000133010f0100 0x0 := regionFork _ _ _ 16 reg40k4 reg40k1312
def prog40k1728 : Array Nat := #[0x30e2000139000b040c3ca038e20001310018d400aad041cd1701535c053c1073464054d9014f039a2000131000cb40c588709b2dc26c70526d0001390526e0001350011040091d0058a4020a100c66404d1501c2f408ea5, 0x526a22a13b8a84de2a11f04e421531539a847c1451c9284ee4a137050e2000149000d3400545001f040e69c59c54d6714f59c50c0d3889344ec123b2030e20001493b453da23c769c50c1071c64054d9014f030e21c23c7, 0x20e220813b8204de024338090bc0e6a05a054d6814f5a047c0c4088a04ee281378a047c004089204ee48137049878083880005258815362053c123880004c4005c50020b400ac10036a41051c54054d5014f8284ee0a137, 0x69847c0e39861854d8614f61850d86123000c222613b89848e2611f039020e2357388d3c0030870912dc2443020c2000139038c2000121001074006450022c400bb50048b4015a9020e214815352053d4244b50911d48143, 0x34b40104d005d1401b41048c20e2357388cbc123080004754615351853d4234751850cca13751848c0e69859854d6614f59850d6612359847c0030868912d02333048c2186153048c2000131000a84cd14f688d1da6143, 0x99447e6511b048a216515359448d6511f59446c00288388b5c123b2050c500011d9144ee451379144ae45123031420c22d7308adc14408388b5ce22b7000a2282433a090ac08288000544142880004840041d00186400849, 0x308b1e02333030a20e22d7388b1c0c288000474003192c053e0513b8144de022af8144ae051230526522513b8944de2512b89448e2511f89446c002889890cd022cb04dc5193153038a2000131000a84b3137988abe6512b, 0x7a04ede81377890cde242f7a047c00388809eee027b7809ece027af030e20ef14f79c4ede7137788ebc0f7345bc54d6f14f03dcd18f15363c53c0e6880004c40032d00147400841002c8400f19004ea401895000a20c22d7, 0x4f04018990078f40c2882bc53caf1437944ede5137788abde512b79448de511f79446c0f50853c54d4f14f53c50dea13b7a84ddea1237a847dea11b000c20cf14f7984ede6137788ccde232f79848de611f0010210f143, 0x49448d2511f001021281534a053d2244b48911d0912b4a047c0038850934d424cf50932d424c7048e212715349c53d223c73a44dc1498868932da24c7052621c24cb70931c149a40004e40033500147400829002c8400f15, 0x7a44ede91377a44ade91237a447de911b7a445c1230849854d2614f488d1d261433244dcc912b49848d2611f49845c104884c054d3014f8244ee091378244ae091234c047e09117000a212515349453d222cb488b1ca9137, 0x3d2212f1534bc53d2f143]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k1728 : region H40 0x800010000400015502000133010e0010 0x10 := regionTerm _ _ prog40k1728 adj40 _ _ 24 (by decide +kernel)
def prog40k2084 : Array Nat := #[0x4086cd021af01c62183153030f28123880004c4e314f38871ce31373886bc0e68c58c54d6314f030621a21cb68871c0e18860c54d8314f03862000131000cd40052d001c7400c21003d0401329005e6401c950088f402825, 0x28c4dca21af1944ac6511f19446c1230830c53cc21c719850cc31373086ccc21af30c4ac6611f0006214315350c53d421cb50871d4314350c48c6a11f0006220313b80c4de021b38086be031231c047c0718840872d021c7, 0x6212315348c53d221cb48871d2314348c4fc6912b48c48d2311f48c46d231170006206f14378c4ede31377886cde21af78c4ade312378c47de311b78c45c0c28828c53ca21cb28871ca3143]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k2084 : region H40 0x800010000400015502000133010e0110 0x110 := regionTerm _ _ prog40k2084 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k1727 : region H40 0x800010000400015502000133010e0110 0x10 := regionFork _ _ _ 8 reg40k1728 reg40k2084
def prog40k2176 : Array Nat := #[0x38893ce22473888dce222f0008210224b40891d022334088bc1420823453da224b68891c0e20859054d6414f0388218415361053c0e2080004c40032d0014d4007a1002a7400e4100486401615006aa40218d00a0f402f25, 0x51054d4414f50892d4224751050c8a13751048d4411b030820a225728893ca224b28891ca22432888dca222f04a020c225730893cc22473088dcc22333088bc0720824053e0413b8104de022338088be04123049820e2257, 0x49045d2410f0008208f14f23c50de413b7904dde22337888bde412b79048de411f79046de411779043c0418820c53c821cb20871c8314320c4dc821b32086bc8312b19047c6411b19045c0020828895ca222f01c82000115, 0x8212415349053d2224b48891d241434904fc891372244ad2412349047d2411b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k2176 : region H40 0x800010000400015502000133010f0110 0x10010 := regionTerm _ _ prog40k2176 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k1726 : region H40 0x800010000400015502000133010f0110 0x10 := regionFork _ _ _ 16 reg40k1727 reg40k2176
private theorem reg40k2 : region H40 0x800010000400015502000133010f0110 0x0 := regionFork _ _ _ 4 reg40k3 reg40k1726
def prog40k2287 : Array Nat := #[0x30e1000139000b140c3ca0398100011d00188400a99045c80d10d734433c117203c435cf10cf0390100011d000c640730470512dc1443056680001390566e00012100111400931005854020b500c6b404d2901c2f408e91, 0x56652050bb8142ce050a304e410b30d79942cc156149142ee450a305581000149000d3400541001f140e62033035ccc0cf33031c0c4049202ec1261e030e100014962033d0c0c760510c117303c435cf10cf030e11c1643, 0x358122d0bb8b428e2169f885a6c0e6a033435ccd0cf3342cc0d3848342ee0d0b383428c0d3849342ee4d0a3048ec80c384000524ed0d73b433c12604000474005c100206400ac5003654116142c435cb10cf8942ee250a3, 0x42c2cc0e62c3ac35ceb0cf3ac31ceb0b70016120b0bb82c2de0b0b3039a11815d360573c00584705b2dc16c703561000139039610001350010c40064100227400ba100486401595035810ad0d72b433da12cb69431da12c3, 0x34640104d005d0401b45049611815d360566c125840004c4ab0d759433cab0c7584b0cab0b759428c0e5a032c35ccb0cf32c31ccb0b732c2cc0b40468512da159f049610eb0d70496100011d000ad5680cf42c31d61443, 0x98546e6a097049410ca0d73282dcca0b33282bc0050460554c1261e0556a0001319282ee4a0b792828e4a09701ca116155358548c0728460554d81523029012a169fa85a5c0d504000554155040004d4004310018b400849, 0x88567d61543028e118155360550c0a3840004c40032d54433e2a0bb8a82de2a0a388546e2a0970566a20a0bb8282de0a0b38282be0a0a382825c00504985a7da154b04dca0f30d70394100011d000ad66a0b39a82bd530a3, 0x7b42eded0b37b428de169f785a6c00604885eee217a3885e7e2179b030e118f0cf7b02edec0a378586c0f72033c35ccf0cf03dc80ef0d73bc33c0e404000474003190014c400845002cd400f2d004e54018a900141161553, 0x4f14018ad0078f40a38453c33d4f0c77a82edea0b77a82cdea0af7a828de151b7a825c0f2842bc35caf0cf2bc31de50bb7942dde50b37942bde50a30016116f0cf7ac2edeb0b77ac2cdeb0a378567de159b001a11af0c7, 0x2282cd440a30348108d0d723433da124b68490c8d0b369025c0c20428495ca124f28492ca12430498108c0d761033d8124361028c1598440492d01243056611c124b70490c159900004e4003210014c400815002cd400f29, 0x7902ede40b77902cde40af7902ade40a379025c1258422c35d640cf22c31d6124322c2dc8b0b322c2ad640a359025c1120424435c910cf8902ee240b72442ce240ab89028e240970288108a0d751033d4124b50490c8a0b7, 0x3c8108f0d723c33c8f0c7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k2287 : region H40 0x800010000400015502000132010f0004 0x4 := regionTerm _ _ prog40k2287 adj40 _ _ 24 (by decide +kernel)
def prog40k2643 : Array Nat := #[0x68467da119b030610e30d7030f2812604000475830cf60470d830a360466c0e40c30c35cc30cf01c611011cb40470c0e18438c35ce30cf0386100011d000c8400519001cc400c35003d140132d005e5401ca90088f402811, 0x1a82cc6a0af50c28d4119b1a825c0018428c35ca30cf28472ca30c728470ca30b71942cca30af049611630cf1ac31d611c31ac2cd630a358467d6119b000612230bb88c2dc710b388c28e2119f88466c0c18468472da11c3, 0x610830d720c33c811cb20c31c811c320c2fc830b720c2cc830af20c2ac640970006106f0c778c2ede30b778c2cde30af78c2ade30a378467de119b78c25c0a38450c33d411cb50c31d411c3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k2643 : region H40 0x800010000400015502000132010f0104 0x104 := regionTerm _ _ prog40k2643 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k2286 : region H40 0x800010000400015502000132010f0104 0x4 := regionFork _ _ _ 8 reg40k2287 reg40k2643
def prog40k2735 : Array Nat := #[0x3a433ce90c73a42dce90af001212090bb8242de090b38242bc144844c433e290bb8a42dc1248458534d614cf049211814d360533c124840004c40032d001514007c1002a7400e2100486401629006a540218d00a0f402f11, 0x2a435d250cf484b2d250c7484b0ca90b72a42bd250a3000e11414d350533d414cb50531d414c350528d4149b039280c90d732433cc90c73242dcc90b33242bc093844a033d2144b4a031d214434242cd090af039890e90d7, 0x49025d2408f0012112f0cf4bc31de90bb7a42dde90b37a42bde90ab7a428de149f78526de90977a423c0918448c33d211cb48c31d211c31a42cc690af1a42ad230a348467d2119b48c25c092843242ccc90ab05121000119, 0x24810890d749033d2124b49031d212434902fc890b72242cc890af2242ad240a3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k2735 : region H40 0x800010000400015502000133010f0104 0x100000004 := regionTerm _ _ prog40k2735 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k2285 : region H40 0x800010000400015502000133010f0104 0x4 := regionFork _ _ _ 32 reg40k2286 reg40k2735
def prog40k2843 : Array Nat := #[0x39820e20d738833ce20c73882dce20af000412020bb8082de020b38082bc0010414c2ec530b79882ce620af051a11a20c71342ec147040004d40034d0019040091d003264010a10054a401a15007ef4025a500b2440340d, 0x28833ca20c728450c450bb2882dca20af1142ac450a3028e114115350833d420c750450c4a0bb1282dd420a350446c1540812033d020c740450c480bb1202dd020b34082bc0e10430835cc20cf30831cc20b73082ccc20af, 0x2082cc820af2082ac820a711028c440970244112115348833d220c748450d220bf1242ec490b71242ad220a348447d2111b48825c0010413c33de20bb7882dde20b37882bde20ab78828de111f78446de2097030a20a20d7, 0xc410430cf18831c611431882fc430bb10c2dc620b31882bc620ab18829c430a318447c6111b18825c62093010410820d720833c820c720450c820bf1102ec820b7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k2843 : region H40 0x800010000400015502000133010f0114 0x14 := regionTerm _ _ prog40k2843 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k2284 : region H40 0x800010000400015502000133010f0114 0x4 := regionFork _ _ _ 4 reg40k2285 reg40k2843
private theorem reg40k1 : region H40 0x800010000400015502000133010f0114 0x0 := regionFork _ _ _ 2 reg40k2 reg40k2284
def prog40k2967 : Array Nat := #[0x49878159000004c6480379010ac149002c815cb2037048e0152053048e0000129048ec8149000004740041500188407280a010ce8042b055a80001510568d00012100112400e2d0056640204d00c51404cc101c09408e11, 0x59808c1569851814d4604b51808c0d60033415da604b0564618605361808c159000004c4003350014a4007ad051680ab0572ac12cab037020e016805342c12c1492c3ac15ceb0370524000011d000c840051505648188053, 0x980cac139005cc14d7302398167e60597052680b30572cc12cb303704ce015305354c12d53023030e019305364c08c0c3ca048e00001313cc15cf30370498000011d0016a400815002ab400d99049660cb05759814ccb037, 0x4440be2042b052510f10573c413cf10373c40bc1150054414d5104f54412c0c5809022ee408b7039a02809b3a026bc1388000054414880000534004490018a40089d002e84012150056641390034c15cd3037980cce6602f, 0x20c400d150040d401729006cb4116009022ee408970458000014934415cd104f8980dcd102f880cae26023052280b10572c413cb104b2c40dcb102f0390026089f9810cc116003c415c11600000474002cd44412e28037, 0x83408db001b801a5c106002c015cb004f2c012cb0047040e01d004b74011c0c3800004e59005364013d9002364006c073008820ee2082301cc024083b90208c0e400a8267ea099b04e000001550560000014d00112400645, 0x8820ee2082b88167c103809020ee4082b040e0000149000d15700535c013e0b03782c08d7001b80165c1583454014d5004f54012d5004754008d5001b039a0260833981a7c148343b415c10600000474002cd6c012db0047, 0x4cc14d3304b9a40bd3302398127e60497049201604d358128d6049f58125c123804c814e4903792408e40497051280a90572a40dc144a03a415ce90370510000011d000c54005490020b400b4d003d14013990063040c580, 0x3d04013ad00631401e25040e01300534c013d3004b4c011e090378240be090234c006e00497024c00c905749814d2604f49812d260473240dcc902f49808c114804c414d3104f4c412e290378a408e2049f88125c13480, 0x8008ce0022b81008c1320024c15c9304b24c0de602339808ae6401b048800c02573008dcc02333008ac1260024815e440379008ae44023055a01002334008ac15680a008ce8022b055a4000151000c840054900206400b4d, 0x49013d2404b49011d240432240dc8902f49008d2401b0458009105724413c9104b24410e240372440be2022b89008e2401b02c8008b05759014d6404f22c12d6404322c0dd6402359006c1020024015c9004f24012e04037, 0x920022415d24053]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k2967 : region H40 0x800010000400015402000133010f0002 0x2 := regionTerm _ _ prog40k2967 adj40 _ _ 24 (by decide +kernel)
def prog40k3322 : Array Nat := #[0x98067e60197038600e3057048ec812600000476430379006ae4302390065c1440c28c15ca303701c601001b34006ac1418038c15ce30370506000011d000c8400515001d2400c4d003cb401345005e6401cc100889402811, 0x80c0be001ab80c08c7001b80065c0018030c15cc304f19812cc304730c0dcc01b330c0bcc01ab0458007104b88c0dc7102f8806ae2302388067e201970006016305358c13c6b04b58c08d6019f58065c121809806ce601ab, 0x6008305720c13c8304b20c11c8304320c0dc801b320c0bc801ab20c09c6401b0006012305348c13d2304b48c11d230431a40bd2302348067d2301b48065c103801c012c7004780c0de001b3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k3322 : region H40 0x800010000400015402000133010f0102 0x102 := regionTerm _ _ prog40k3322 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k2966 : region H40 0x800010000400015402000133010f0102 0x2 := regionFork _ _ _ 8 reg40k2967 reg40k3322
def prog40k3414 : Array Nat := #[0x7a00bde042b0524f0ef0573bc13cef0473bc0dcef02f03d4014f05353c13d4f04b53c11c0f7005bc14d6f04f7ac0dc0f6006bc12daf04703980000135000cb4005a900227400c210040540144100626401f8d00989402d11, 0x2bc12caf04303dc000011533c15ccf04f33c11de6037780ccde602f780cade6023000e02007bb801ede007b3801ebe007ab801e8e00797051e80af0572bc13caf04b2bc11caf0372bc0bc0f38043c12d0f0477a00dde0433, 0x7900bde022b79009de402379006de400f03d2012f0534bc13d2f04b4bc11d2f0437a40dde902f7a408de049f7a406de04977a403c0e1801bc12c6f0471bc10de30377806cde302f7806ade302378067de301b78065c0f280, 0x3c8008f05723c13c8f04b23c11c8f0437900dde0233]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k3414 : region H40 0x800010000400015502000133010f0102 0x10000000000000002 := regionTerm _ _ prog40k3414 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k2965 : region H40 0x800010000400015502000133010f0102 0x2 := regionFork _ _ _ 64 reg40k2966 reg40k3414
def prog40k3518 : Array Nat := #[0x52420e205738813ce20473880dce202f0004014205350813d4204b50811c0010013414c4d04f68812da204704dc00530539880bc14700000534003350018a40091d003254010a100550401a19007e94025bd00b2440340d, 0x11814cc204f30811c460433080dcc202f3004ac46023040e005005314013e0013b8080de0202f8004ae0202380045c1540812014c4804f40812d020471200dd0202f4004ac1410028815ca204f28812ca20472880dca202f, 0x2080dc8202f2004ac8202711008c4401b0304004f05313c13c4f0437804ede20377880bde012b78809de202378047de201b78045c0010048814d2204f48812d2204748810c4903748808d2011f48806d20117048c20c2057, 0xc4004305310c13c6204b18811c620431880fc430371880bc6012b18809c4302318047c6201b18045c620130104008205711014c8204f20812c8204720810c8203f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k3518 : region H40 0x800010000400015502000133010f0112 0x12 := regionTerm _ _ prog40k3518 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k2964 : region H40 0x800010000400015502000133010f0112 0x2 := regionFork _ _ _ 4 reg40k2965 reg40k3518
def prog40k3638 : Array Nat := #[0x60414d8104f60410d8102360406c0008028415ca104f28412ca1043000200280570a013d0104b40410c137000cc15e6101b055c000014d000c84006150024c400ca90042d4015450068b401f910096f402ca500d03403c89, 0x58413c2b04758410c2b03758408d6101b58025c116000c415c3104f8802ee210378802ae2102388406e20097051a102d0570b413da104b68410c2d02368406da00970542014105350413d4104b50410d4102350406c15904, 0xa40bd2102348406d2009748404c070800bc15c2f04f0bc11de00bb7840dde00b37840bde00ab78408de101b78025de10130002008105720413c8104b20411c810432040dc800b32040bc800ab09008c125840ac15d61053, 0x1002ac4102710408c4101b10025c4101310403c0308008c15c2304f18412c6104718410c6103f08c0dc600b31840bc600ab18409c2302318406c6009718404c070800a415d2105348413d2104b48411d210434840fc29037, 0x82002205710414c4104f08811c410431040fc400bb1040dc2202f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg40k3638 : region H40 0x800010000400015502000133010f0116 0x6 := regionTerm _ _ prog40k3638 adj40 _ _ 24 (by decide +kernel)
private theorem reg40k2963 : region H40 0x800010000400015502000133010f0116 0x2 := regionFork _ _ _ 2 reg40k2964 reg40k3638
private theorem reg40k0 : region H40 0x800010000400015502000133010f0116 0x0 := regionFork _ _ _ 1 reg40k1 reg40k2963
private theorem safe40 : hostSafe H40 := regionHost _ _ _ bk40 reg40k0
def H41 : Array Nat := #[0x1, 0x2, 0x3, 0x4, 0x5, 0x8, 0x9, 0x10, 0x12, 0x14, 0x17, 0x20, 0x22, 0x28, 0x2b, 0x40, 0x44, 0x48, 0x4d, 0x50, 0x54, 0x60, 0x68, 0x72, 0x7f]
def N41 : Array Nat := #[0x40101001101110000010500150114, 0x101001121110000010100110332, 0x101001101110000010100110110, 0x4010100010101000009050005030e, 0x40101000101010000010500050104, 0x4000100110011000000050095003e, 0x40001001100110000000500150014, 0x10100002111000009050000033e, 0x101000021110000010100000332, 0x10100000101000009050000030e, 0x101000001010000010100000100, 0x112111000000000095033e, 0x1121110000000000110332, 0x110011000000000095003e, 0x1100110000000000110010, 0x9050095033e, 0x9050005030e, 0x50095003e, 0x500050004, 0x9050000033e, 0x9050000030e, 0x95033e, 0x95003e, 0x332, 0x0]
private theorem bk41 : bookOK H41 N41 0x8004010100112111000009050095033e = true := by decide +kernel
private theorem adj41 : validRows H41 N41 := rows_of_book _ _ _ bk41
def prog41k10 : Array Nat := #[0x50c400012105106000111001304009cd041041d065374193c1341074d94c14410000534002c103904000131001664014490087140831032097cc825732093cc8233030c400012103104000119031060001110018e403629, 0x41041d035305104000141000b340e410000464005b1049d7812756038c40d325f34c95cd323334c88c13418000445d335374cd0c1041032097c0e41800044510357820ccc10310000485d0353051040c825f32095cc8233, 0x504002cd0014841341074cd4dd3343041041d035305104000141000b340e410000464005b1045d7811756041841d065374193e4c8230398819241b64904c1361074d94c14610000534002a10013041341074cd4dd3343, 0x4641699800054416a1800053400555001462869bba1a6cc0e628000464135180005441451800053400521003e440234500ef0405c490398819144b64510d9141b64504c0e61874d94e6c89374d90c1061074194c14610, 0x32097cc823305a8c0cc25f05ed4000131000a84004cd05a641d365305a8400014d05984000139059c400013100126400bd5029062869bba1a6cc157300004641599800054415a180005355545b029062869bba1a6cc16730, 0x52710d3223045c60001110522800014d045c40001190012c400add003f6401655056840d525f35493cd523335488c1599074d94c15a10000534156100004e4157100004c40049955496c16a4c34c97cd323334c88c16a20, 0x1ca28e9b3a3a66c13628000544146280005341175e03146000139b2a28eca893028c40d724f35c8ccd7223045840001190458600011105e2e8148b064493e2c22304e261933530522600014d8b0c8c1173000046400411, 0x45cc0001190460c00015154496c0a310a1a0ee86833059cc00011905a0c000151001114008d5001ca28e833a3a06c10628045d5810518000514002d103146000139001644011a10415781054e031460158baaaa28eaa893, 0x45c800011954516d514578a20cc16820740d4c164180004e510357820ccc1572055516c16720000556082330569015545b05a90000155000a4400599002514157183548cc157300004655525b55491c0a310a1a0ee86833, 0x544148b00005055125b028c428683ba1a0cc167300004641683000054416a30000504005450014628683ba1a0cc0e628000464106280005441462800050400511003e8401c550495781254e046081d035304506000139, 0xc841593a05a9219244764910d9241b64904c11820740d4c148a0000504114180004e4117200004655145b05a081d035305a8800014105906000139059c8000119001314009b1028c428683ba1a0cc1173000046411830, 0xc52064910d9241b64904c154180004c55545b55511c1561855496d5524703146000111]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k10 : region H41 0x80040101001121100000080400840220 0x0 := regionTerm _ _ prog41k10 adj41 _ _ 26 (by decide +kernel)
def prog41k375 : Array Nat := #[0x5ab32a299b05a66000155000a44004d1050c22c2aabb0aa8ec2a93054c40d515305684000119000b6416a2032097cc823305a8c0cc25f05ed4000131000a8416a1000046416a18000444006d5002f34014c900af1404141, 0x55880d5153055022482330558200012105692000111000e64005590564e816a4864906d9241305a8800013105a8c00012100115400c4d0485780020824c56c9315702902000111a0a6ee829b3a0a66c1331024c56c93157, 0x546628930522800014d001374009b1003964012d5031022a299ba8a64c1593a020822829bba0a6ce8299b04d8809315b04d0224833304d8200012105a72000119000e4400551001f541392a030c22c2aabb0aa8ec2a93, 0xa8a2aea28a3a8a24c0c30864454d9114f038c2000131b0a2aec28a3b0a24c1140864512d9141b64504c178b00004859115364453c17a4435c88c112080004649114f044c200011105c528178ba029022829bba0a66c138a0, 0x35c8cc10308000444d0157040820001190011141714a05e0a8000080562eaa28aba8a24e22833039822c2aabb0aa4c1583000056400345a8a06c168c088a0cc16830000514002d500257401051004a8401c4d030c20158ba, 0x820898a0ee6283304e0aa6281b0410219015364112d9041b64104c10308b9904cd01530520400011905c5281782a0520800015d0014c51015b44055d101470288228283ba0a0ce8281b018820178ba88a0cc17b40]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k375 : region H41 0x80040101001121100000080400840228 0x8 := regionTerm _ _ prog41k375 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k9 : region H41 0x80040101001121100000080400840228 0x0 := regionFork _ _ _ 3 reg41k10 reg41k375
def prog41k566 : Array Nat := #[0x51a600014d53456d4d15704cc21b3153050c200014d000aa4006210354828d9bba366ce8d99b04d4826d41b04d46000121000b441469853516d4d457051060001290514600012100113400909004c44024c100e72406045, 0x6cc88e6468b050c42a46aba91a8ea468b050c42c46abb11a8ec468b034c41a4653035020c825f6a0d4c17a34000484146900004640043100176400855002b34136886cc54e6d41b051a600014d43456d0d15704da61b3153, 0x53496d4d25705e0d08d15b23455c10310000424003298348cc1069853456d4d15704146000109041578103080004a400491002a8400d510047341351034c97cd32576ccd4c0e69053496d4d257039a4000129000c666d233, 0x51ac14d15b051820001290518a000109000e44006a1003104018cd049b78126d60350426d83b9b60ce6d81b9b602c1382a0354420d22303548000111a360ee8d833a3606e8d80b0414820d41b6c104e0868b041a201055e, 0x821a2c0d510a360ee8d833a3606e8d80b05a0d20d233041ac14d15b041820001290418a000109000e440055100208414620b21aaec8693b21a2c1493464906d92413051a8000131000d6414610b11aaec468b051ac000159, 0x350426d83b9b60ce6d81b9b602c0d410a366ee8d9b3a3666e8d98b04cc426d2336cc88e6468b04e4d10d15b04d880001099b506c1360800048400411001b44009c104e4a80e6a053516c0e6a00004a64883383506db0413, 0x39a4000119052640001410010c6246ab0000d26d83b9b60ce6d81b04e0a8006a8a366ee8d9b3a3666c13628000544003c1001aa28d83ba360ce8d81b0418a0001510518a00014100133400b11004824018a1045b78116d6, 0x6a0d0c136206cd94c146200005359144b64510c0e6a00004c4004998a1aae286938a1a2c103086c054db014f88a0cc133086cc54e628b30518200014d000d06226ab889a4c0c31069194d9124f69190c103106c0d4db034f, 0x1061a83536a0d3e28333]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k566 : region H41 0x80040101001121100000090400840228 0x10000000000 := regionTerm _ _ prog41k566 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k8 : region H41 0x80040101001121100000090400840228 0x0 := regionFork _ _ _ 40 reg41k9 reg41k566
def prog41k826 : Array Nat := #[0x931e8c0f520000524003c573d94dcf64f73d90c0c5200004e4009190014801055e04153a087bb821e6c147a00495781254e03dc6000149000d054f45b53d15d4f44703946000121039060001290026c40193500d04405089, 0x49b5a4c7a303d48000149000f15af6536bd93daf643035480001310024e40139903d8a01255e03d4600014953cd5d8f5470398600012963cd4d8f34f63cd0dec323001cc01175e045d5a2c7ab8b1e8c0e628049d7812756, 0xd55af3536bcd3daf3436bcc8c0e6a08a1ece287ab03d8a000121045d7811756039a82487b37a1aac0f6280004841275e049d580f5200005240054573db4dcf6cf73db0c006b0045b78116d68b1eae2c7a30358a0126de, 0x5d52817542b91e6c0f718000574003cd53c96d4f25753c91d4f23703cc41af3536bcd0c0e3100004d4cf25f33c95ccf24f039a40001190016a400e310054840f618055b28156c6a99eac0f51805db28176c603d8a00015d, 0x49d780f710000525cf24f73d10c0a4100004e50f25b43c95d0f2477a08dde823379106c0f61073d94dcf6430314400013953c96d4f2570398400012963c93d8f2477b08dde461b0014401354a04d50a647bb991e6c0e510, 0x63c51c00708a89eaea27a3a89e6c0a40804d52a627bb989e6c147a004957814798000524002cd53c56d4f147059e601774a05dd180f408000575cf15373c53c083080004e400529002d5400db100630401b9100a8d40f720, 0x12e4006b10024648f15b23c55c8f14f23c51c00508809eee027b3809e8e0279b03d0210f15b43c55d8f44b63d06c0f61853c56d4f1570018201593aa89e6c0f6080005541215e03cc20001490012a4006a163c54d8f14f, 0x49b78126d603cc2000149000d15af1536bc53daf143789aade26a3789a4c0f20833c97ccf15333c50ccf23333c88c0f61063c54d8f1437b088c0f41073c54dcf1430008201782a809e8c0f2080005041714a03d0200015d, 0xf308045b78116d6889ecc0f608]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k826 : region H41 0x80040101001121110000090400840228 0x10000000000000000 := regionTerm _ _ prog41k826 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k7 : region H41 0x80040101001121110000090400840228 0x0 := regionFork _ _ _ 64 reg41k8 reg41k826
def prog41k1088 : Array Nat := #[0x555c915372453c152084d456c16208000554002b90018c40e624b26aaec9aa3b26a4c15730aa584c157100004c4002d9059241c965372593c166100004e4167100004c40045500242401319009314039c9018104082bd, 0xa9922c163109992ee664b399922c16310a192ee864b3a1922c0931049916c0c48833097d2c25b05ec900013105926000111001084005d100213400ad50552213515baa584c164900005558915362453c154904d456c16490, 0x724d3c178a432454cc914f044c4000109000ce629323045241c915372453c117100004241175e0448200013900126400ab1003564011d5055c60d525f4d496cd524f029261c9353724d3c0a4980004e4003114d4ccea9323, 0x72454c164080004e41672000042400399001ac400c45006354124de0493380c4980562eaa98abaa628ea9893aa622c0e4988a4ccc0e624000466c98abb2628ec9893b2622c1173064526e296138b122c11488045d79c9353, 0x39262c98abb2628ec9893b2622c148a48a4c8c114a072454c114080004e41172000042400399001564008310598828c4bba3126e8c48b05a4919241b64904c1662400048400351059062864bba1922c164a0000544164a0, 0xaa62aea98a3aa624ea988b031262c9aabb26a8ec9a93b26a2c153104d4ccea9323a9922c1592462454c15620000426a961305502000131001064006d90027141593a045cc1514db0398900012993228d9149b8a584e2c48b, 0x44416a98000514004218192ec000240562eaa98abaa628ea9893001c92c9aabb26a8ec9a93055c8000159000f1400724b262aec98a3b2624c1172000056416720000514004d5002c64012090062c4104de0413380c498, 0x558813545b0598800015564112d90447031490001210012460c4bb83126e0c48b0448213115b4c455e228230548213515ba8a08c16408000554003458092ee0249b020c412645b440d5d26447044c413125b4c495c0a498, 0x3dcc0001490015054f4db53d35d4f4c7001280104de04133a087bb821ecc0e4a0049378124ce921ecc0f730000524003c14bd16d2f4574bd11c0e62400048400929004e4401b190084240c4904b096d2c2574b091e0c223, 0x4bcd5de64bb7a4ccde932303d040134ca04d30a647bb03dc40174ca05d3080f7200005740034d4bc96d2f2574bc91d2f2330314920c7a3831eec0f7200004c41055e0415380c524931e8dec4bb03dc80001310495781254e, 0xf208041378104ce809e8c0f408049378124ce03c82000149000d052f15b4bc55d2f1477892ede24b378926c0f31033c97d2f25b33c93d2f24702926000111]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k1088 : region H41 0x80040101001121110000080400940228 0x100000 := regionTerm _ _ prog41k1088 adj41 _ _ 26 (by decide +kernel)
def prog41k1431 : Array Nat := #[0x5668d4bba352ce8d49b031262c96abb25a8ec969303528248233049a90001114b506c0d624000484126de05da91a9323035240001194b48cc0d4980004440044900236400b510041540134d00631401f4100a2240343d, 0x1a90134ca9b52ee6d4b39b526c14624000534116de045b5a296ab8a5a8e29693001a92a96abaa5a8ea9693059a400015504d32a6d4bb9b52ce6d49b051260156caaa5aaea96a3aa5a4c006a4b25aaec96a3b25a4c0d410, 0x5da91a9323035240001194b48cc0d498000444004494b456d2d1576a454da914f4b451da9143001a90156ca055b1aa96abaa5a8ea9693001a92296ab8a5a8e29693059a8000145000f54104de04133a0d4bb8352ce0d49b, 0x1a91ed4bb7b52cde96ab7a5a8ded49b7a5a4ded48b03528248233049a90001114b506c0d624000484126de]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k1431 : region H41 0x80040101001121110000090400940228 0x10000100000 := regionTerm _ _ prog41k1431 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k1087 : region H41 0x80040101001121110000090400940228 0x100000 := regionFork _ _ _ 40 reg41k1088 reg41k1431
private theorem reg41k6 : region H41 0x80040101001121110000090400940228 0x0 := regionFork _ _ _ 20 reg41k7 reg41k1087
def prog41k1543 : Array Nat := #[0x514003490015340e59874d74c1392a0516a00014d049d781275604d6a1d35d30516a00014d045d781175604d461d35d30514600014d000b140064902d46000139002cd401231006a8402c89011504061910212940a8bd, 0x5268000149001114007b50026a400e9904d6a1935d364d72d935c764d66c0c5a864974d925c764966c0c5a864574d9159b05146000145000d24005cd04d661b35d36cd6ac145a8049b78126d60516a0116de045b5814518, 0x1ea400c4d0046840a41842cd5d683535a0d3d6644b59911c1492c0495781254e0398b00014952d16d4b45752d11d4b437031681a85d36a173c0c5a064574d915cf039680001315c512c0c5a064974d925cf03968000131, 0x396201215e9ae4cc1392a04d420001495cc54d731479ac4de6259b0518b01255e0516600014952c56d4b15752c51d4b13705242174147a2c4de8259b0316201593a0564daa259b031620001550485781130800052400551, 0x16a28b83ba2e06c0e59805e0a810518055d281574602d460001390416a000155001174005d1001f3400a21003ed4012b10058240b3085a0d4d6834f59912c1392c5cc54c1492c0005340029942c56d0b15742c51d0b137, 0x4a5701535c053d7014782c4de025a380966c1052064174d905cf64172d905c764166c105986c174db05cf6c16adb05a30396801055e52d16d4b4570415380e5a00004a57044b5c111e0b41b0000b26b83b9ae06c1382a, 0x4d5281354299166c1451005d52817542b9166c0e598000574003cd52c96d4b25752c91c105905c0d4c14590000504cb25f32c95ccb24f039640001190014a400cb5003ec4013890078841062c0415794b15b52c55c12808, 0x61174d845cb61170d8459b02c820cb25f32c54ccb1430416417015305164000141000a640053122c56c8b15722c53c8b14722c4dc0051061174d845cf61172d845c761170d8459b02cc41a45d369173da45c36916ac0e590, 0x3964000149000f052b45b4ad15d2b4470396414b4db52d35d4b4c702d241c95d372573dc95c302d24000139000ea400621003a64014b50062c401d090516410b25b42c95d6824f59112d6824759110d0b23759106c0a208, 0x62571d895c362566d8959302d261a95d36a573da95c36a56ada95a36a564c0a49805d32ae65930596900015d4acd5d693535a4d3d664c75a4d0d6932302d280104de0413397044b82d2ed70413039680124de04933972413, 0x63d71d8f5c30396816f44b5bd11d6f4437a16ac0e5a800048400431001ed400b19003c44013a50062240b4a004937a4b4b302d240001494ac56d2b1575a454d6914f5a451d691434ac4dd6249b029281895d362573d895cb, 0x7ad2edeb4b77ad2cde95ab7a568deb49b7a564c0e5905bc93d6f2477ac8ddeb2337916adeb22379166c0f5985bcd4d6f34f5bcd0deb3337996adeb32303d8b1af5d36bd73daf5c36bd6adaf5a303d4818f5d363d73d8f5cb, 0x127885bc54d6f14f5bc51d6f1437ac4dde25ab7ac49de25a378966de25930016916f4c7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k1543 : region H41 0x80040101001121110000090500940228 0x100000000 := regionTerm _ _ prog41k1543 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k5 : region H41 0x80040101001121110000090500940228 0x0 := regionFork _ _ _ 32 reg41k6 reg41k1543
def prog41k1941 : Array Nat := #[0x524003450015040e61405e0a9d02d30514500014105dd2817746041451d02d305145000141055d28157460418a1d02d30518a000141000b540065d03145000139002cd401219006a4402c89011534061a1021a940aabd, 0x520400015d001154007b50026a400eb1041450d02df340b5cd02d3340acc0a31435cb5cd72d335cacc0a314354b4cd52b30518a000155000d74005c1041851b02d36c0aac14628045b78116d60518a0126de049b5814514, 0x1ea400c410046440c5102b097cac257610b4d85247610b0c17a1405d52817542038c500015d51496d4525751491d45237018a41a42d3690b0c06290354b4cd52c3038a40001192d497c0629035cb4cd72c3038a4000119, 0x38a201714a05e0aae581b0414200015d2c055cb01538144de022b3050c501754a0518500015d51456d4515751451d4513705e820b4157a144de822b3018a20178ba05e2da222b3018a200014505c5281560800057400551, 0x1452859bba166cc0e61404e4a813628045d78117560314500013904d45000145001124005d1001f0400a11003ed4012990058240c2882b097d842d3610b0c178142c054c17a14000504002b121456c8515721451c85137, 0x4a4b31572cc54cb31439944de622b3988a4c1351034cb7cd32d734cb4cd32c334cacc136146ccb4db32c36ccaadb3293038a414525b04d5281354251491c0e2900004a4b325f2cc95e652330000526583b9960cc1382a, 0x415781054e820acc0e4140495781254e920acc0e614000524003c151516d4545751511c1341464cb4c144140005358544b61511d85443039050001310014a400cb5003e64013890080441331451456c1354a51451c17988, 0xa218515361453d8544b04d020b315304e4a8144140005341215e038a20001490012c40071941456d0515741451d051434144dc0a414320b7cc82d7320b4cc82cf320b0cc82b3031051a82d36a0b3da82c36a0aac0e414, 0x49495d25247039051454db51535d454c7025051c92d3724b3dc92c302505000139000ea400611003ac4014b500626401d09051050a825f41496d052572a093d05247410b0d052372a08cc08288320b7cc82d3320b3cc82b3, 0x31251a92d36a4b3da92c36a4aada92a36a4a4c0c52404937a4c2a3059250001494b0b5d892d3624b3d854c7624b0d89293000a40b325f04d328134c29952ecb3223038a40174ca05d308b72230390500015d000f352525b, 0x63cb3d8f2c37b0aac0e5140004c400435001c6400b11004484015a5006a240929005d32ae549b0250500015d49456d251572a454ca914f49451ca91434944dd222b3029240c92df324b5cc92d3324b3cc92c3324accc92a3, 0x43cb5d0f2c37950dde82b37a0aade541b7a0a4c0f29033cb4ccf2c3038a40001192bc97caf2572bc93de52377948cde42ab03d450cf2df33cb5ccf2d333cb3ccf2c333cacc0f6146bcb4daf2cf6bcb0daf2ab0398518f2d3, 0x177882bc55caf1532bc53caf1437944dde22b3788aade5127788a8de22930012512f2d77952ede54b77a4acde92ab7a4a8de549b7a4a4c0e414]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k1941 : region H41 0x80040101001121110000090400940328 0x100 := regionTerm _ _ prog41k1941 adj41 _ _ 26 (by decide +kernel)
def prog41k2346 : Array Nat := #[0x61573d855cb61571d855c36156fc0b51452cb5d6a2d35a8b3d655475a8b0d6a2bf03d6516f2d35bcb3d6f2c3041651702d35c0b3c135945ccb4c14594000534002c10012f400729002cc400f19004e2401a21008044026a5, 0x42cb5d682d35a0b3d6544b59511d682c35a0afd682ab59506d6828b02ca201215e92cacc06288000524ab15759454d6514f59451d651435944fd622ab02d450cb2df32cb5ccb2d332cb3ccb2c332cafccb2b3001451855d3, 0x2d2512b2d75a4b4d692cf59531d692c35a4afd2b2b35a4aad692a359526d692935a4a2c0b2902ac97cab257590b4d6524f59491d642c35948fcab233590aad65223590a2c00414]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k2346 : region H41 0x80040101001121110000090500940328 0x100000100 := regionTerm _ _ prog41k2346 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k1940 : region H41 0x80040101001121110000090500940328 0x100 := regionFork _ _ _ 32 reg41k1941 reg41k2346
private theorem reg41k4 : region H41 0x80040101001121110000090500940328 0x0 := regionFork _ _ _ 8 reg41k5 reg41k1940
def prog41k2438 : Array Nat := #[0x504003490015540a390554f6c1593a059c70001550495781254e055c71553db059c70001550415781054e055c41553db059c4000155000b0400649038e4000129002c9401221006ac402c89011514061990212d40a8bd, 0x5aac000149001104007a50026e400e91055c71153db454f2d153c3454e4c0e41c448f6d123c3448e4c0e41c440f6d10393059c4000141000d24005d5054e41353db4d4eec1671c049378124ce059c70104de04133816710, 0x1ee400c550046c40e6103b096cec25761c93d843cb610f0c1691c049d78127560290700014971d94dc764f71d90dc76270310712c3db4b0f5c0c41c440f6d103d703147000121640f2c0c41c448f6d123d703147000121, 0x28e201215e0564eaa7923055c20001493d456cf5143a9c49ea23930590701275e058e400014971c54dc714f71c50dc712705a420f6143b1c49ec2393020e201392a04e49a62393020e200014d0485781020800052400559, 0x1c72c78abb1e24c0a39005e2e81171004d52813542038e4000129045c700014d001174005d9001f5400a31003e94012a1005824072083b096cec257610f2c1591c3d456c1691c0005540029161c54d8714f61c50d87127, 0x4e4f115b3c455cf1143888ece27127888e4c11730444f6d113d7444f2d113c3444e4c113904c4f6d313d74c4eed313b30314701175e045d59c765371d93c0c51c0004e5913cb644f0e2c393000070158baa9e2aea7893, 0x55d2815746a98e4c0a39805dd2817746b98e4c0a390000574003d571cd4dc734f71cd0c113983c496c16398000514c725f31c95cc724f028e60001110014e400ca5003e84013890078c41141c045d79c715371c53c12888, 0x418f6d063cb418f1d0639301c820c725f21c56c87147044e60f115b058e6000145000a440052131c55cc715331c53cc714331c49c0e398418f6d063d7418f2d063c7418f0d0639301cc41263db498f5d263c7498eec0a398, 0x28e6000149000f15a765369d93da7643028e61c76d371db3dc76c3034e614d3db534f5d4d3c7034e6000129000ee400631003a44014a500628401d09058e60ec35761cd4d8734f618f2d863c761cd0d87327618e4c07308, 0x434f1d0d3c3434e6d0d393034e412d3db4b4f5d2d3c74b4eed2d3b34b4e6c0e69005db2ae439b051a700015d3b496ced25769c93ced247690f0ced233001870116de045b59913cb89daad9139b031470126de049b599239b, 0x43cf1d0f3c30314718f3cb63cf1d8f3c37b0eec0e51c0004c400421001e9400b11003c64013b50062240d61c049b7a476a3034e60001493b456ced15769c54da714f3b451da714369c49da2393039ac10d3db434f5d0d3cb, 0x7b4eeded3b379daade76a779da8ded39b7b4e4c0a3983bcd5cef343798eede733379cc9de7323798e4c0f3903bc96cef2573bc91de43bb79c8cde722303d0712f3db4bcf5d2f3c74bceed2f3b303dcc10f3db43cf5d0f3cb, 0x127883bc56cef1573bc51cef143788eede7137788ecde7127788e6de2393001a71af3c3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k2438 : region H41 0x80040101001121110000090400950228 0x10000 := regionTerm _ _ prog41k2438 adj41 _ _ 26 (by decide +kernel)
def prog41k2835 : Array Nat := #[0x414f6d053d7414f2d053c7414f0d053b7028e50ec2d761cb4d872cf614f2d853c761cb0c0039469cb4da72cf69cb0da72ab038e51453db514f5d453c7038e5000129000ed4006b1002a8400ea5004a6401791007c240273d, 0x388a4c0729031cb4cc72a7038e500011929c97ce525b39495ca724f39491ce42c33948dce523329c88c0a39431cb7cc72d731cb4cc72cf31cb0cc72b331ca9cc72a3020e51253db494f5d253c7494eed253b7494ecc0e614, 0xe50ef2d73bcb0de53bb794edde72b379caade72a779ca8de539b79ca4de728b01ca201215e91ca8c07314000524e515b39455ca715329c53ce514739450ce5137388acca7127]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k2835 : region H41 0x80040101001121110000090400950328 0x10100 := regionTerm _ _ prog41k2835 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k2437 : region H41 0x80040101001121110000090400950328 0x10000 := regionFork _ _ _ 8 reg41k2438 reg41k2835
def prog41k2925 : Array Nat := #[0x42cf6d0b3d742cf2d0b3c742cf0d0b3b7001471875d361d73d875cb61d71d875c3001671a75d369d73da75c369d6ac0e59c52cf6d4b3d752cf1c0e59c0004a4003b5001ac400a2100389401219005e4401d890090f402b15, 0x59c49d6239b588e4c0e5903ac96ceb25759c93d643cb59c91d643c33ac8dceb23359c88d6439b028e60eb35759cd4d6734f598f2d663c759cd0ceb33359cc9d6732302d0712b3db4acf5d2b3c74aceed2b3b74acecc0e62c, 0x594f1d672c359cafceb2b359caad672a759ca8d6539b59ca4d6728b0016716f3cb5bcf1d6f3c37aceedeb3b77acecde75ab79d69de75a37ace6deb3937ace2c0b3883ac56ceb15759c54d6714f588f2d6714759c50ceb137, 0x3943acb5d672d359cb3d653cb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k2925 : region H41 0x80040101001121110000090500950328 0x100010000 := regionTerm _ _ prog41k2925 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k2436 : region H41 0x80040101001121110000090500950328 0x10000 := regionFork _ _ _ 32 reg41k2437 reg41k2925
private theorem reg41k3 : region H41 0x80040101001121110000090500950328 0x0 := regionFork _ _ _ 16 reg41k4 reg41k2436
def prog41k3029 : Array Nat := #[0x524003410015140a40c05e2e9511db059c300014505d52817542045c31511db059c300014504d52813542045c81511db059c8000145000b340065d03903000129002c9401211006a6402c89011554061b1021ad40aabd, 0x5a2600015d001134007a50026e400ea1045c30911df24476c911cf24468c0e20c25c76c971cf25c68c0e20c24c76c931a3059c800014d000d74005c5045031311db4c46ec16720041378104ce059c80124de0493381670c, 0x1ee400c450046640e41832077d061db32073d061c740cd0c17b0c05dd28177460288300015d70cd4dc334f70cd0dc3327018831261db49871c0620c24c76c931c7028c300011134c77c0620c25c76c971c7028c3000111, 0x286201714a05e2eae3893045c200015d1c456c7114f88c49e221a30588301774a0590300015d70c54dc314f70c50dc312705ec207614fb0c49ec21a30106201782a05e09a021a30106200014105c5281340800057400559, 0x1c32c3aabb0ea8c0a40c0564e8157200415781054e03903000129055c3000141001124005d9001f1400a19003e94012910058240818832077d061db41871c1788c1c456c17b0c000514002a130c54cc314f30c50cc3127, 0x4e47515b1d453c75147a8c49ea21a3a8866c1571825477c951db25473c951c725468c1540c4d476d351c74d46ed3519b028c301574a055d19c335370cd0c0a30c0004e4d51df35473ea61a3000030158baa8e2aea38a3, 0x45d78117568b068c0c50c049d781275693068c0a40c000524003c570d94dc364f70d90c1560c45476c1660c0005558344b60d11d83443031430001210014e400ca5003e44013890080641520c055d29c315370c50c17a88, 0x6210315b40c55d8344b0558207515b0564e81660c0005541215e028620001490012840071160c54d8314f60c51d8314360c49c0e60c23077c8c1db23075c8c1cf23071c8c1a30310312c1db4b075d2c1c74b06ec0c50c, 0x68cd3da3343031431c36d370db3dc36c30358314d1db53475d4d1c703583000129000ee400619003a84014a500624401d09059830cc1df33075d8335361873d861c760cd0d8332733068c0c18823077c8c1db23075c8c1a3, 0x350312d1db4b475d2d1c74b46ed2d1b34b466c0e6a0049b7a481b3051a300014943476d0d1d76a073d0d1c768d10d0d19b000c30d51df055b28156c6a8daacd51b3028c30176ca05db18d71b30314300015d000f55a3353, 0x43c75d0f1c77a06ec0e50c00048400425001c4400b190044c4015b5006a240d30c05db2ae36930358300015d1b456c6d15768c54da314f1b451da314368c49da21a3039a608d1df23476c8d1d723473c8d1c72346cc8d1a3, 0x63c73d8f1c77b06ede36277b068dec19b78d84c0f30c23c76c8f1c7028c300011133c77ccf1d733c73de61bb78cc9de61a303dc308f1df23c76c8f1d723c73c8f1c723c68c0f40c4bc76d2f1d74bc71d2f1bb0290310f1db, 0x177881bc56c6f1571bc53c6f1477886ede31377886cde312778868de219b001a31af1cf7b46eded1b378daade36a77b468ded19b78da4c0c50c]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k3029 : region H41 0x80040101001121110000090400940238 0x10 := regionTerm _ _ prog41k3029 adj41 _ _ 26 (by decide +kernel)
def prog41k3434 : Array Nat := #[0x40cf5d033cb40cf1d033c340cefc0e38c3b876cee1d771c73cee1c770cf0dc71bf03ce30ef1db3bc75cef1c7044e30f11db3c475c1538c3d476c1638c000554002c50012f400739002c8400f11004e2401a31008064026b5, 0x3b076cec1d761c73d833cb61c71d833c361c6fcec1bb60ce4cec18b01c6201215e91c68c04188000524e315b38c55c6714f38c51ce314338c4fce21bb038e30871df21c76c871d721c73c871c721c6fc871a3038e31033db, 0x34e30ed1db3b475da71cf3b471da33c369c6fced1bb3b46cda71a33b466da339369c62c0730c31c77ce61db39875cc71cf39871ce33433986fce61bb3986ccc71a339862c0c38c]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k3434 : region H41 0x80040101001121110000090400950238 0x10010 := regionTerm _ _ prog41k3434 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k3028 : region H41 0x80040101001121110000090400950238 0x10 := regionFork _ _ _ 16 reg41k3029 reg41k3434
def prog41k3524 : Array Nat := #[0x42c75d681cf58d12d681c758d10d0b1b7001431835d360d73d835cb60d71d835c3001631a35d368d73da35c368d6ac0e58c52c76d4b1d752c71c0e58c0004a4003b5001ac400a21003a9401291005e6401f09009cf402d9d, 0x2c8308b1db22c6dc0b50c000444cb1df32c75d6335359873d661c758cd0ccb1b358cc9d661a30396308b1df22c76c8b1d722c73c8b1c722c6dc8b1b322c68c0b40c4ac76d2b1d74ac71d2b1bb4ac6dd2b1b30516310b1db, 0x3ac6cd671a359c66d6339359c62c0058c5bc73d6f1c77ac6edeb1b77ac6cde35ab78d69deb1a37ac66de35937ac62c0b18804857a4b1b302c830001491ac56c6b15758c54d6314f58c51d631431ac4dd6312758868d6219b, 0x2ce30eb1db3ac75d671cf58cf2d671c758cf0d671bf3ac6eceb1b7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k3524 : region H41 0x80040101001121110000090500950238 0x100000010 := regionTerm _ _ prog41k3524 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k3027 : region H41 0x80040101001121110000090500950238 0x10 := regionFork _ _ _ 32 reg41k3028 reg41k3524
def prog41k3630 : Array Nat := #[0x21476c851d721473c851c72146dc0a28c30cb7cc32d730cb4cc32cf30cb0c0028c68cb4da32cf68cb0da32ab038a31451db51475d451c7038a3000129000ed40069900284400e250048c4017a10076240243d00acb40331d, 0x28c49ca21a3039050a81df41476d051d72a073d051c740cb0d051b72a06cd0519b40ca4c0c50c2b077cac1d760cb4d851cf61471d832c360ca9d8519b60ca4c0520c49476d251d749471d251bb4946dd2519b038c50851df, 0x58cb0d651bf2ac6cd632ab58ca9d651a359466d6329359462c0028c2bc77caf1d72bc73de51bb7946dde51b378caade32a779468de519b78ca4de518b014620a21df19456ca315728c54ca314f19451ca31431944dca21b3, 0x1ca30a71df39476ce51d729c73ce51c738cb0ce51bf3946ece51b73946cce51af29c68ce519b38ca4ce518b02ca30ab1df2ac75d632d359473d651c7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k3630 : region H41 0x80040101001121110000090500950338 0x110 := regionTerm _ _ prog41k3630 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k3026 : region H41 0x80040101001121110000090500950338 0x10 := regionFork _ _ _ 8 reg41k3027 reg41k3630
private theorem reg41k2 : region H41 0x80040101001121110000090500950338 0x0 := regionFork _ _ _ 4 reg41k3 reg41k3026
def prog41k3753 : Array Nat := #[0x5e4e81792a05e42816ac864834d9209b054410550db15434c0a3040004241593a05a810001550012c4006dd00248414304b06aaec1aa3b06a2c15a1800056416a18000554004c900413401f1100dd1404dc101a2d409225, 0xa066ce8199ba0662c00004a8666ea198b0564eaa192304d011120db44826c13104048578530db038c1000109000c84005559864cc1392a05ab32a199ba8662c16998000554003490031441490444836d120d744826c0c304, 0xa8488c1620461034d840cf61032c1620415834c0020405e4e81792a059c100015d05a84000149001024960cfb0488c0020405e4e81792a05e42814984000576412230526400014900156400bb100395401499029012819bb, 0xc10158baa862ac1350474c34c145040005341175e028c10001390011540063100248400c09003c4416a0430497cc125730493cc123330488c15104048578550d3028810001090564ea412330568400014925436c950cf, 0x3e2401321005cc41120405c528510d30288100010905e2eae409b0522100015d24436c910d724433e2123388488c1289814436c510d714434c510cf052711110db44435d110cb44426c0c50464434d910cf64432d9109b, 0x14033c500c70008126183b04e0aa6181b038c101782ab9824c0e304b062aec18930460100015905a01000145001174d00d734034c1570455436d550c7045c11510db059c1000145000b541055e0388100012900186400d4d, 0x49b78126d6051a614d0db53435c143040004a40034900233400dc5004d0401b21007c240231105ab01900d364033d900cb64031d9009b64024c149c044036d100d744032d100c744026d1009305e010500db14035c500d3, 0x524003c56c034db00cf83426c0060464434d910cf64432d9109b05261000131045b78116d6885aac0e684049b78126d69864cc1392a04d410001496cc34e6d09b001411a1353904ccc1493453436c146040004a400299, 0x5248d0db23435da40d369033c8d0c769030da1223049a604d0db13435c4d0d313433c4d0c713430c149b443436d0d0d743432d0d0c743430d0d09b039a10116de045b5a21833885aac10504049b78126d69060cc10504, 0x4933815704000525350dbaa424c0e48448496e41223039011120db059c1000121000a44124de0493381649072434dc90cf05881000139000d24008d500370401345006cc401f09008c64029b5034410126de9048cc0d310, 0x62431d890c362424c0a484041378104ce88608e014bb045c10124de04933a418a3045c1000149000f05310db4c435e29093001011100db44035d100cb44024c16a84000484104de04133a014bb029210124de0564eaa1923, 0x4b436d2d0d76a434da90cf4b431da90c34b426da909368522c0910404937a41323024c400014949836d260d732434cc90cf49831cc90c3484ccc1249012436c490d712434c490cf12431c490c305aa91890d362433d890cb, 0x126a4]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k3753 : region H41 0x8004010100112110000009040094022c 0x4 := regionTerm _ _ prog41k3753 adj41 _ _ 26 (by decide +kernel)
def prog41k4138 : Array Nat := #[0x13c30c16abc63c34d8f0cf63c32d8f0c763c30d8f09b03dc110f0db43c35d0f0cb43c31d0f0c343c26c0f30453c36d4f0c7038c100012933c35ccf0d333c33ccf0c30394100011900188400a3100382401211006ad401fa5, 0x78522c0f6046bc34daf0cf6bc30de16ab785a8ded09b7b424de168b03c8104f0d313c30c0f20473c34dcf0c302881000139000c248f0db23c35c8f0cf23c31de123378488de409b049e604f0db13c35c4f0d313c33c4f0c7, 0xf4044bc36d2f0d74bc31de14bb7a42dde14b37a426de9093]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k4138 : region H41 0x8004010100112111000009040094022c 0x10000000000000004 := regionTerm _ _ prog41k4138 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k3752 : region H41 0x8004010100112111000009040094022c 0x4 := regionFork _ _ _ 64 reg41k3753 reg41k4138
def prog41k4211 : Array Nat := #[0x32c35d660d359833d660cb584c8c1258412c36c4b0d712c34c4b0cf049411720d35c833e415a30526b10b0db42c35c149ac52c36d4b0d705261000129000c8400549001e2400a990038d4011c500590401b11008494027bd, 0x59034d640cf59032d640c759030c8b0b758488d6409b041411700d35c033d700cb5c031e0b0b780568e0b09b80562c0c5845c434d710cf5c432e215ab88568d7109b88562c1230468574da15cf6856ada15a368562c16598, 0x3d6116f0d35bc33d6f0cb5bc31d6f0c37ac2dde15ab7ac29de15a37ac26deb09378562c0b4844ac36d2b0d75a434d690cf5a432d690c75a430d2b0b75a426d6909358522c0b20422c36c8b0d7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k4211 : region H41 0x8004010100112111000009050094022c 0x100000004 := regionTerm _ _ prog41k4211 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k3751 : region H41 0x8004010100112111000009050094022c 0x4 := regionFork _ _ _ 32 reg41k3752 reg41k4211
def prog41k4303 : Array Nat := #[0x4142dc0e2842cc34c1354a984acc14914000535450db51435d450c75142dc0e2842cc35cb30d39942de612b3000a11850d361432d850c7050a1000131000f34006a900308400f99004e24017c1007c440252500aef4032ad, 0x41579450db51431c0e2840004a4b00d72c034cb00cf8142de012b3804a8e0509b804a2c1231411436c450d711434c450cf11431c450b7028a10c12df304b5cc12d3304b3cc12b3304a8c1499441436d050d741432d050c7, 0x7942dde12b3784aade50a7784a8de509b79424de128b049251250db49435ca90d32a433d250c72a430d250b7484acd2509b2a424d2128b014410a125f21436ca40d729034ca40cf21431ca40c32142dca123328488c0e284, 0x2842ac35d650d359433d650cb59431d650c35942fd612ab59429d612a359426d65093584a2c0e2842bc35caf0d32bc33caf0c3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k4303 : region H41 0x8004010100112111000009050094032c 0x104 := regionTerm _ _ prog41k4303 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k3750 : region H41 0x8004010100112111000009050094032c 0x4 := regionFork _ _ _ 8 reg41k3751 reg41k4303
def prog41k4418 : Array Nat := #[0x21c33ce40cb3848cc1238411c36c470d711c34c470cf049c10f20db3c835e413b305aa71870d361c33c16a9c71c34dc70cf05aa1000139000cc400549001e2400a91003894011c100591401b190084d4027bd00bab403615, 0x39832ce60c739830ce133331c29ce6093045c10f10db3c435cf10cb3c430e213b389c29e27093884e2c083843c036cf00d73c032e013bb804eccf0093804e2c12204484f6d213d7484eed213b3484e2c1439039036ce40d7, 0x59c24d6138b03ce10ef0db3bc35cef0cb3bc31cef0c3784eede70b7784ecde70a779c26de7093784e2c0d3843b436ced0d769c34da70cf3b432ced0c769c30da70a73b426da7093684e2c0730439836ce60d731c34cc70cf, 0x1ca10e50db39435ca70d329c33ce50cb39431ce50c33942fce50b7384acce50af29c29ce509b39424ce128b02ce10eb0db3ac35d670d359c33d670cb59c31d670c359c2fceb0b759c29d6709b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k4418 : region H41 0x8004010100112111000009050095032c 0x10004 := regionTerm _ _ prog41k4418 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k3749 : region H41 0x8004010100112111000009050095032c 0x4 := regionFork _ _ _ 16 reg41k3750 reg41k4418
def prog41k4542 : Array Nat := #[0x1d436c1574aa8468c1690c000555c30d370c33dc30c370c29c0a1841d436c750cfa8c29ea11a3000611030db40c32d030c305861000121000f54006b90030c400f91004e24017c5007c640253500aef40329d00e8b404295, 0x70c30c0a1840004e4710db1c435c710cf8846ce230a788468e2309388462c1220c10c36c430d710c34c430cf10c30c430a7038610811df20476c811d720473c811b320468c16a8c60c34d830cf60c32d830c360c29c0a184, 0x7846cde30a778468de309b78c24de118b049a306d0db1b435da30d368c33c6d0c768c30da30a768468c6d09b68c24da118b00c410c11df19836cc30d730c34cc30cf19831cc30c33046ccc30a730468c0a184045d79c30d3, 0x58c32d630c758c30d630bf1ac2dd630a758468d6309f58c26d6309358462c0018438c36ce30d719c33ce30cb38c31ce30c338c2fce11bb38c2dce11b338c26ce309338462c0a1841bc36c6f0d71bc33c6f0c77846ede30b7, 0x518428477c650db28c35ca30d328c33c650c728c30ca30bf1942dca11b328c2bca30a728468ca309f19426ca309328462c0a1841ac36c6b0d758c34d630cf]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k4542 : region H41 0x8004010100112111000009050095033c 0x14 := regionTerm _ _ prog41k4542 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k3748 : region H41 0x8004010100112111000009050095033c 0x4 := regionFork _ _ _ 4 reg41k3749 reg41k4542
private theorem reg41k1 : region H41 0x8004010100112111000009050095033c 0x0 := regionFork _ _ _ 2 reg41k2 reg41k3748
def prog41k4699 : Array Nat := #[0x5e4e81792a05e42817b4435c14cd70330444005105b14414c0c500000424178ba05a80000145001264006c900244414600b022aec0893b0222c148b000056416a30000514004dd00410401f2100dd5404dcd01a2d409225, 0xa020ce8081ba0202c0000005e2eae08938820ce2080b0408009705b25c0cc1010005c5285005b03980000109000c440054505e0aae081b05a3022083388202c168300005140035d00314417a0025c16c9704725c0cc0c300, 0x88104c1640032017cc805332010c1640015814c0040005e4e81792a05a8800015d059c000014900102516043b0104c0040005e4e81792a05e42814800000526e04130520800015d00156400b99003914014b10288028083b, 0x1800158baa822ac1050074014c145000005041574a031400001390011140061900244400c09003c8416a0060112d8044760110d8041b60104c1110005c528510530290000010905e2eae041b0522800015d44416d11043, 0x3e2401311005c641540004857855053029000001090564ea480330568000014945416d1504745410ea041ba8104c17ab015416c5505315411c550430569009505f25416c950472540cc0a30035417cd505335410cd5033, 0x14c11c530430010026083b9820cc1382a0398001392a93008c0e600b02aaec0aa30566000015905a600001550011259305364c11c1170054416d51057055c015505b059c0000155000b141354a039000001290018c400d41, 0x5db28176c6051ac14d05b53411c146000004a40035d001d3400bd5004504019a1007e240251105a710d305f34c15cd305334c10cd303334c08c149c024c17c9305b24c15c9304724c0cc9302304e4005305b14c15c53053, 0x5db181782ab8206c10500000574004556c014db004f8340cc0030035417cd505335413cd503305260000119055b28156c6a81aac13500b8266c176ca05db1813500000575b30539b40cc0a30035c14cd703305140000119, 0x23413c8d0472340cc8d023034c00176ca0358800015d13416c4d05713414c4d04f13411c4d043029000126de9200cc0d3000005250d05b43415da80536a013d0d0476a010c0e680055b28156c6a8206ea06ab039a00176ca, 0x55c02e0a9305d328174c2055c000015d4d416ea90230388009705b25c08c16700000444174ca05d308164a072414dc904305900000139000d7400755002f34011450066c401f89009464029b50520d08d05f23416c8d057, 0x4b016d2c05762414d8904f62411d89043029200134ca98224c134c29812ec0a48005d328178bab8224c174c2045c000015d0011353105b4c415e290230008009305f24c16c9305724c08c16a80000444134ca04d30a604bb, 0x4b416d2d0576a414da904f4b411da90434b40cda902368122c168a432417cc905732414cc904f32410cc903332408c0920005d3280c4a00005744905b12415c4905312413c4904712410c0c48004937a4c02302480000149, 0x176a4]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k4699 : region H41 0x8004010100112110000009040094022a 0x2 := regionTerm _ _ prog41k4699 adj41 _ _ 26 (by decide +kernel)
def prog41k5084 : Array Nat := #[0x13c15c4f05313c13c4f04713c10c0f40073c14dcf04f0290000013943c16d0f05743c11d0f0437a00cc0f60053c16d4f0570398000012963c14d8f04f63c11d8f0430394000013100188400b89003e64014110062d401da5, 0x7a40dde90337a408de049b78122c0f3006bc14daf04f6bc10ded033781aaded023781a4de068b0520f08f05f23c16c8f05723c13c8f04723c0cc8f02305a2f0cf05f33c15ccf05333c13ccf04333c0cccf023049e004f05b, 0xf2004bc16d2f0574bc11de04bb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k5084 : region H41 0x8004010100112111000009040094022a 0x10000000000000002 := regionTerm _ _ prog41k5084 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k4698 : region H41 0x8004010100112111000009040094022a 0x2 := regionFork _ _ _ 64 reg41k4699 reg41k5084
def prog41k5153 : Array Nat := #[0x2b017d8505361411d85043600a4c1728011416c4505311411c4504305d400b70532dc10ee02930520508505b21411c1481451416d4504705200000129000c440055d001e2400ab10038d4011d500593401b21008494027bd, 0x41415ca80532a013d0504741410d050372a00cd0029304d400b305f2cc15cb30532cc10e650379940ce60293980a2c062802d417cb50532d410cb5033a80aaea0293a80a2c17600680b4da02c3680aada0293680a2c16614, 0x3ca00af05f2bc15caf0532bc13caf0437940dde5033780aade502779408de0293780a2c092802a417d2505b49415ca90532a413d250472a410d250374940cca9023480a2c082802a017d0505b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k5153 : region H41 0x8004010100112111000009040094032a 0x102 := regionTerm _ _ prog41k5153 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k4697 : region H41 0x8004010100112111000009040094032a 0x2 := regionFork _ _ _ 8 reg41k4698 reg41k5153
def prog41k5245 : Array Nat := #[0x60166c0e5800415797005380166c17a2c0005054b05b52c15d4b04752c0dc0e5805c014d7004782c0de0059b02cc00cb05f32c15ccb05305160000119000f04006a90030c400f91004e24017cd007c840252500aef403295, 0x52c16d4b05704d5280e5800004a5730535cc11d730439ac0de6b03398166e6059398162c1762c12c16c4b05712c14c4b04712c10c4b0370520b08b05f22c16c8b05722c11c8b03722c0cc0050060174d805cb60171d805c3, 0x7ac0ddeb0337816adeb0277ac08de059b78164de058b05d6912b05b4ac15d690535a413d690475a410d2b0374ac0cd6902358126d6048b02c4010b05b42c15d680535a013d6044b5a011d6804342c0dd6041b58104c13500, 0xb2802ac17cab05759414d6504f59411d650435940fcab033580aad6502759408d60293580a2c0e5805bc14d6f04f5bc11d6f043]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k5245 : region H41 0x8004010100112111000009050094032a 0x100000002 := regionTerm _ _ prog41k5245 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k4696 : region H41 0x8004010100112111000009050094032a 0x2 := regionFork _ _ _ 32 reg41k4697 reg41k5245
def prog41k5360 : Array Nat := #[0x40c11d0304340066c1718010c16c4305310c11c4304305dc007705b1dc11ee019b05a230c305330c10c1688c70c14dc304305a20000139000c640055d001e2400aa1003894011cd00595401b310084d4027bd00ba540362d, 0x60c13d8304760c10d830271b008d8019b055c007505f1d416c7504f1d411ea3027a8c08ea019ba8062c041801cc17c7305b1cc11e601bb1cc08e6019b98062c1740048076d201c74806ed2019b48062c1440c1a017d0305b, 0x28c08ca018b03c6006f05f1bc16c6f0571bc13c6f0477806ede303778c0cde302778c08de019b78062c0d1801b417c6d05b1b415da305368c13c6d04768c10c6d03368c09da302368062c0c1801b017c6c05b1b015d83053, 0x2c6006b05f1ac16c6b05758c14d6304f58c11d6304358c0fc6b0371ac0cd6302758c08d6019b58c05d6018b014600a305f19416ca305728c14ca304f19411ca304328c0fc6503728c0cca3027]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k5360 : region H41 0x8004010100112111000009050094033a 0x12 := regionTerm _ _ prog41k5360 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k4695 : region H41 0x8004010100112111000009050094033a 0x2 := regionFork _ _ _ 4 reg41k4696 reg41k5360
def prog41k5484 : Array Nat := #[0xa8408ea009b050201000db40032d000b740026c140800d016e81037a040ce8009b059a10c105f3040cc126800b416c169000004d400299001344007a1002b5400e4d00491401691006f040212500a2f402fad00dc5403f0d, 0x8040de0103380408e0009b0502008105f20416c8105720413c810472040dc8103320408c178840c416c310570c414c3104f0c40de2103388408c139000cc16c330570cc14e610379840ce6009b0564003505b0d414c35037, 0xbc16c2f0570bc14c2f04f0bc11c2f0437840dde103378409de102378026de0093024200124de90408c092000005252105b48415c290530a413d210470a410d210374840cd2009b05e0103005b0c015c300530c013c30047, 0x18026c61017014200a105f09416ca105728414ca104f09411ca10432840fc250372840cca102f28409ca102328024c0b0800ac16c2b05758414d6104f58032d6104758410d6103f0ac0dd6102758408d6009b58024c0f080, 0xc2006105f18416c6105708c14c6104f18411c230431840fc610371840cc6102f08c09c61023]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k5484 : region H41 0x8004010100112111000009050094033e 0x6 := regionTerm _ _ prog41k5484 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k4694 : region H41 0x8004010100112111000009050094033e 0x2 := regionFork _ _ _ 2 reg41k4695 reg41k5484
def prog41k5626 : Array Nat := #[0x3c416e2039305ec700014571c14dc704f71c10dc7027028e00f105b3c410e27027880e4c0720021c17c8705b21c13c16380000444003c5001ae400c21003e6401389005f5401f310094d402bbd00ca3403a0501085404b2d, 0x28e00001393d416cf50473d410ea7027a9c08ea039ba80e4ea038b05d0704705b11c14c4704f11c11c4704311c09c1689c31c17cc705331c13cc704331c09cc7023038e01003db400f2d003c7400f0d00393028e001175e, 0x79c09de7023780e6de0393780e2c1769c3b416ced05769c14da704f3b411da70433b40cda702769c08da0393680e2c071003b016cec05761c14d8704f600f2d8704761c10d87027600e6d80393028e001574a71c14dc704f, 0x38032ce104738410ce103f3840dce103309c09ce009b38024ce100f01c6006705f38c16ce305719c13ce304738c10ce303f3806ece303738c0cc6702338066ce018b028e00ef05b3bc15cef0473bc10de03bb79c0dde7033, 0x3ac0dceb03359c09d67023580e6d67017580e4d6700f580e2d6700701ca00a705f39416ce505729c14ca704f39411ce50433940fce50373940cca702729c08ce029339403ce028b39401c0708038416ce105709c14c2704f, 0xa3803ac16ceb05759c14d6704f580f2d6704759c10d6703f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg41k5626 : region H41 0x8004010100112111000009050095033e 0x10002 := regionTerm _ _ prog41k5626 adj41 _ _ 26 (by decide +kernel)
private theorem reg41k4693 : region H41 0x8004010100112111000009050095033e 0x2 := regionFork _ _ _ 16 reg41k4694 reg41k5626
private theorem reg41k0 : region H41 0x8004010100112111000009050095033e 0x0 := regionFork _ _ _ 1 reg41k1 reg41k4693
private theorem safe41 : hostSafe H41 := regionHost _ _ _ bk41 reg41k0
def H42 : Array Nat := #[0x3, 0x4, 0x7, 0x8, 0xb, 0xc, 0xf, 0x10, 0x13, 0x20, 0x23, 0x30, 0x33, 0x40, 0x44, 0x50, 0x57, 0x80, 0x88, 0xa0, 0xab, 0xc0, 0xcc, 0xf0, 0xff]
def N42 : Array Nat := #[0x1000000001001000000010000010100000000000100110001000100011110, 0x1000000000001000008010000010100000000000100010009000900090908, 0x1000000000001000000010000010100000000000100010001000100010100, 0x1000000000001000000010000000100000000008100110009000900090098, 0x1000000000001000000010000000100000000000100110001000100010010, 0x1000000000001000000010000000100000000000100010009000900090008, 0x1000000000001000000010000000100000000000100010001000100010000, 0x1001000008010000010100000000000000110000000900009998, 0x1001000000010000010100000000000000110000000100001110, 0x1001000000000000010100000000008100110000000000099998, 0x1001000000000000010100000000000100110000000000011110, 0x1001000000000000010100000000000000110000000000009998, 0x1001000000000000010100000000000000110000000000001110, 0x8010000010100000000000000000009000900099998, 0x8010000010100000000000000000009000900090908, 0x8010000010100000000000000000000000900009998, 0x10000010100000000000000000000000100000100, 0x8100110009000900099998, 0x8100110009000900090098, 0x8100110000000000099998, 0x100110000000000010010, 0x9000900099998, 0x9000900090008, 0x9998, 0x0]
private theorem bk42 : bookOK H42 N42 0x8001000000001001000008010000010100000000008100110009000900099998 = true := by decide +kernel
private theorem adj42 : validRows H42 N42 := rows_of_book _ _ _ bk42
def prog42k10 : Array Nat := #[0x52400329049e6000139001a2400b91049c22e299bb8a64c12710b9266c127180004440028905e4e00014d0016f401641008e84127b87c9d4df274f7c9cadf271304dee00014904e4e00013d04e4f00013900197403859, 0xa44179380004f4005cd05e1481782a001841e4753791d3de474b791cac127900004e6e479bb91e2c126087c9d4c0f6080004e5f214f909eac0f708000526e279b031461ea7537a9d3dea74b049861f27537c9d3c0f718, 0xb91e6ee478b049c22e279b049c6000109000a44179380004f4005cd05d1481742a04d822e299bb8a64e1314b05e7227093f9c24ec13610b9266c13618000444002c900122412610b91e6ee478b049822e279b04986000109, 0x4440053103d840cf25f33c93c0c3100004f40f6100004640f61800044400529003ee40232100ee2405ac105e722689439a24fe6893b9a242c13410b9266ee498b44c8ec13708b8a66c137180004240029100152412710, 0x518600014d000b240049104dcc0d325f05dcc00014d03984000119039860001110012f400ba9059e40cf25f33c93c163100004f416790000464167980004459654b03d440cf25f33c93c0a3100004f40f5100004640f518, 0x5dc800013d0490600011100133400ad1003ec401629001461ea7537a9d3dea74b7a9c4c1372834c97c177280005340e5100004640e518000444004bdb29ccc0c310791d4de474f791d2c126187c9d4df274f04d861f3753, 0x464169980004441745205a6f00015d65912d9643b051061f474f7d1d2df471304dc800013d04de80001390511781341874d12e6871303d0426479b03d060001117cd12c083100004f40043903dc80cf25f04904000119, 0x4641752205a6f00015d0012e40f62033c57ccf14f04d880d315f05d8800014d000af4169886590ec134080004c413608000484003990020a4010490585481611205a6f00a45e55912d5643b058c40d724f35c8fc16990, 0x466c8933b224ad1214f049ec0cf15f049820001197c853e427ab028c226293b05e4a00014db2a4cc0c30898a4ec17930000534002a90016f400921028c21ea74f05e6a00013db29cceca723058c20d714f35c4fc16788, 0x5a660001096590ec0830833c57ccf14f05e6800013d04d0200011904d060001090014c40c30833c57ccf14f05e6c00013d04d8200011904d8600010900148400fc90070a41685205a048127a033c57c179200004f412408, 0x41578106189c24fe7093b9c248e7090b049e80cf15f05e4800013d0490200011904906000109b224cc127b033c57c179300004f41260800046412618000424004a10027341630833c57ccf14f05ed300013d05a62000119, 0x414627093f9c24ee7090b049ea00014db2a4ceca92304dea2ca733b29c8c169bc0004e400349]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k10 : region H42 0x8001000000001000000008010000010000000000008100100008000800088880 0x0 := regionTerm _ _ prog42k10 adj42 _ _ 26 (by decide +kernel)
def prog42k376 : Array Nat := #[0x314415523f03d84000129000ae400499055e619555b65552d9553b03dca2aa79b0394600013d000ac4126187c9d4df274f04d861f37530518600014d000b240e6180004f40f6180004e4006a9002e44014c100ae8404209, 0x4e4a2aa79b0494621274f04d4600014904146000139000ef400531041578106189c24fe7093b0498600014d04d860001490010a400c110561480e310a91ccea472b0558a00013935497cd524f3548fc0f710a91ccea472b, 0x4651523b0490600011100134400acd003cc4013a90567201055e5548fd5523b0564e0d525f35493cd523f04e442a4733049842127cf04d840001490418400013d000ee400519001ea41025a0566f19555b65552d9553b, 0x5550ec159bcaa266ea899305eaf00014d65516d9544b6550ec000209a250e6893f9a24ec149a0000526a899baa264c157a04548ec144187d1d2c0e4180004f40f4180004e40039105117815a42056080d525f3548fc12410, 0x4f40f6080004e4003a90014841415a056908154080291795545b45453d5543b0560219555b6554ec135080004c4003215544fc0c40845453c13608000484002a900254401119004f2401d110566f00a45e55516d5544b, 0x25453c9513f000022a299b98a50e6293f98a4ec0e30835457cd513f03dc200011905056815a42048c2000151001536a2933a8a4aea292305aae0d515f35453cd513f055ee01445e45453c157085544fc146087d1d3c0e608, 0x1593825457c0415a]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k376 : region H42 0x8001000000001001000008010000010000000000008100100008000800088880 0x1000000000000000000000000000000000000000000000000 := regionTerm _ _ prog42k376 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k9 : region H42 0x8001000000001001000008010000010000000000008100100008000800088880 0x0 := regionFork _ _ _ 192 reg42k10 reg42k376
def prog42k571 : Array Nat := #[0x5548fc1579065576c0f5900004c4002a9059e400015500172400919049e617255b5c955c1279864976d925d703d66000131000ca40f598b2eacecbaab055e6000159059e6000155001124009110054e40268900ef0406121, 0x5b955d6e54b03dc618e5db63975d8e5cb03dcb26e59b03dcb1f27537c966c145980005240e5980004f40044d0016c400829002a440c5a832c97ccb25732c93ccb23f0494417255b5c955c0c5900004a64b23f0554417555b, 0xaadcac0f7080005540035972c53c0f588b2eacecbaab059e200015505854815788000564004b9002b2400d190046440c590791d4de472b79166c1772cb2dccecb72b038c4000159000cf56e25772c93dc45cb03dc616e55b, 0xae4135980004c4005c9002c2401791041748105aa049cb08b15f0105688b15722c53c8b13f059cb1cb14b05a4b00013932c57ccb15732c53ccb13f05a4217215792c4fe425bb00162016152b2dccecb72b051622ab733, 0x32c57ccb15732c53ccb13f031621cb14f056621955db05a6200015504d62000131000ee4005190021241391864976d925d76496ec105989c24fe7093b0496600014d000cc41371863976d8e5d7056661955db05a66000155, 0x22c55c8b14f22c4fc1272c32c97ccb25732c93ccb23f0316416e25772c93dc45cb04a041925d70416400013192c8fc1599000052400439001a64009890409681262c32c57c169080004657215784853e4b13f9096ec0c588, 0x38c40001090011356e45b0188208b15f0105688b14f22c4fc1631032c97ccb24f32c8fc1699000046400389058c20cb15f32c53ccb13f05a6200011905a6600010900124400b39004954018c902d1480b42a049cb08b15f, 0x99166c12418000446689439a242c1792c000534004bd5c916d724575c90ec1540845453ea259ba8964c1541045493ea459b05666000111000c257545b5d50ec137209b966e6e58b9b964c0e58822c57c8b13f038c2000111, 0x49681f244f7c966df25937c962c12410]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k571 : region H42 0x8001000000001001000008010000010000000000008100100009000800088880 0x1000000000000 := regionTerm _ _ prog42k571 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k8 : region H42 0x8001000000001001000008010000010000000000008100100009000800088880 0x0 := regionFork _ _ _ 48 reg42k9 reg42k571
def prog42k833 : Array Nat := #[0x84c12c0c500000504003a1b8266ee0993b8262c169c80005740093d0404005205f058548161121480fc1230005a1481681205de0000141000c26c0933b024aec092305ecf00014905e4f0001590027340192d00d0e4050d5, 0x84c12c105aa05a40000141000e866059b98164e6058b05a4b00014d002574013bd04d8001685203d80000141b0268ec07ab04de00001597cc12e6079b981e4e6078b0410001745205d0a91305b44c12c1060005e1481782a, 0xca5e05cb78166de059378162c124005c916d1204f05a6000014905d1481742a0496017205b84813c168000005241785205e0a81690000050400521b8166ee0593b8162c1040044c16c0b45244c12c0b42a05a000105d2, 0x5a90816a0aa380fc0610000054400391b01ccec072fb01caec072303dc004f05f13c0bc0e300000425e0753781cade071305dcb00013d00176400e4d0055240f50053c16c0b54202d48816780051708145a205a60000151, 0x5e1480e300000506e090bb81c4c12700000575d204f9380fe407339380be4072b901c8c10700b8266ee098b04dc000015db01ccec072b05e6e0001599b80fdd302f981c8e607130388008e05f0589081620a2380fc0e300, 0x5ea015505b55412d5503f0188009505f0589089503f040c00d505f3540fc1078000046400311b02acec0aa303d80017a2205e90815900000546e0a9bb82a4c1593c00057400559002ea400e4d005c2401a39009ab412300, 0x561480e300000504002cd0012240073da81ccea072ba81c8ea071305aa005505f15413c5504b1540fc00000a824cea092b98250e6093f0560015505b5540fc136000561480f600000504002a9001326a09a3a8266ea0993, 0x550011504f02d1480b42a056600158520416a815780000504003215d416d7504b5d40eea059ba8164ea058b000002a079ba81e2de0753781d3de074b055c005505f15413c5504b041c02a099b74c12c12300]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k833 : region H42 0x8001000000001001000008010000010000000000008100100009000800088888 0x8 := regionTerm _ _ prog42k833 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k7 : region H42 0x8001000000001001000008010000010000000000008100100009000800088888 0x0 := regionFork _ _ _ 3 reg42k8 reg42k833
def prog42k1088 : Array Nat := #[0x55ca0d52df03945000119000a4417728000554005cd0024c4137302cc97cb325704dcc0d32df34cb5c0e61400046400311039852e5a9bb96a4c15730000574177300005540044d0024a40153d009a8403bc101842408381, 0x2bc93c0f73033cb7ccf2d733cb3c0f71493cacc0f7147cdd4dd32b30518500014d03d850001390011240059900204400aa9018a418555b61555d8554b6154ec135102cc97cb3257028c50001119954ec155102d497d5523b, 0x3dc8000155000d75e544b039052e5a9bb96a4c1772000055417452055c800015d0012f400acd0034c4011a9028c51ea7537a9c4dca2b3059e52e579bb95e4c167940005740033953cb5dea2cf79552c0f7302bc97caf257, 0x498500011900173400b21005ea4102d2040a48137940291794545b51515d4544b5150ec1779479513c179940004f58545b61515d8544b6150ec179a044cb5e682bf9950ec0041405d14ae579bb95e4c14414a95e6ea5793, 0x61515d8544b6150ec0831479512c15920354b7c1792000055412414000464003bd0014c40084d04e4c0d32df34cb5cd32bf0418527093f9c24ec1361400052400319049ec0cf2df33cb5c15930354b7c17930000554002bd, 0x51512d4543b04de518555b61555d8554b6154ec0a31453cb5dea2cf79552c1382834cb5c105140004666553b0564a00014d0010f4006b10026841055e05a650d32df05a6500011944cb5e1344b9a0afe6543b000c518545b, 0x484004492bc57c000140291794545b51512d4543b018a218555b61552d8553b05e4a000131000e840628861516d8544b6150ec179200004c417930000484004a9002cf401255006334051520144481379451516d45457, 0x4d8200012998a50e6292305a650001490012e4b315f2cc55cb313f0550211514baa0acea82ab0554215514baa8acc159300004a4003212d457cb513f049e224f2b393caae4f2a303ca214545b5150ec0f6200004a40f628, 0x1426c02b3b00aaec02a30404005205f0145485204f01444817800040b4a1204f040a481798000050400389900ace402ab900a8c1799400052400959004ee401b3d0085541328874c52dd32b374caadd32a304d4224a2b3, 0x79412de02ab0388008e05f0149080520a05dc00142c2050a281790000054400311700b3dc02b3700aadc02a304c400b315f14c12c1790000053416152058448132802cc17e1304b05e0000014d05a1481681205e60000141, 0x1510015412c051520144481590005614810292055c0000141000c24b505f2d413cb503fa80acea02aba80a8c0f100781d4de0713700acdc02a3059e50001392bc17de504f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k1088 : region H42 0x8001000000001001000008010000010000000000008100100008000800089888 0x1000 := regionTerm _ _ prog42k1088 adj42 _ _ 26 (by decide +kernel)
def prog42k1433 : Array Nat := #[0x4c4cb2df32cb3ccb2bf041e51855db61572d855bb0496521274f0416500013992cafc13594000524105d2051651e55cb0396500013d72cb3c0f5940004e4004410022c400b190040a40131100628401f0900a35403401, 0x18a40ab25f2ac93c052422ac8fc133140004456545b02d1496544b5950ec0b42a018a416555b59552d6553b0398b0001292ac97cab24f014908ab23f03cc516555b59552c0b5425954ec0031461576d855cb6156ec1072c, 0x51651e55cb0396500013d72cb3c0f5940004e400441aacaceab2abaaca8ea559ba9564ea558b018a216555b59552c0b5425954ec0b522018a216545b59512d6543b0498b000121000ea4ab15f014548ab14f2ac4fc05112, 0x2ca00ab05f59416d650572ac13d6504b2ac0fd6503b0496521274f0416500013992cafc1359400052415852]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k1433 : region H42 0x8001000000001001000008010000010000000000008100100009000800089888 0x1000000001000 := regionTerm _ _ prog42k1433 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k1087 : region H42 0x8001000000001001000008010000010000000000008100100009000800089888 0x1000 := regionFork _ _ _ 48 reg42k1088 reg42k1433
private theorem reg42k6 : region H42 0x8001000000001001000008010000010000000000008100100009000800089888 0x0 := regionFork _ _ _ 12 reg42k7 reg42k1087
def prog42k1545 : Array Nat := #[0x5440032900144409410b9126c1025a0592600011105e1481782a059242e449b0592600011105d1481742a059e42e449b059e6000111000a8400641059e900015d002cb40124d006b2402cd5011424061b90212540a881, 0x48c4000141001084007ad00276400ebd059242644c39912fe644a399126c168249c12fe704a39c126c164a09a12fe6849b059e6000121000d040059103d241644db59126c1679802d5080b522059e60145c205168816498, 0x1f6400c110047241693c93d30e497ab93d28df249b7c924c1049805a14816812024c4000141b264cec992fb264aec992304a0817249b5c924c124a09a126e6849305e4900014d92130c128249c126e7049305e4900014d, 0x552401025a05614a0924f05aa40001414d48fea922fa9128ea449b04d2601685203d26000141b26acec9aafb26aaec9aa30560613533faa4cbea64a30560801055e5552fc1052e05669000129056148157a000050400519, 0x59220c915f3244fc0f4880505681678805d50817522059e900015d0592200012900114400599001e4400a49003eb4012cd005954007a493d30ea979baa5e4c10490a9126c10498000444002bdaa64cea992faa64aea9923, 0x5653514b4d44fea912fa8928ea249ba8924c1690898930e624bf98928e6249b98924c0f48858936d624cb58926d62493024c2016152b264cec992b05844817924000566424c39244fe424a30248208915f0105688913f, 0x589081620a4b88fc0e49805a90816a0aa392fc0930800054400391b25ccec972bb25c8c0e48878926c0e498000425e97537a5cade971305dc900013d00156400cad003f34013d500792410488b26acec9aab05854815808, 0x9b930e6e4bf9b926e6e48b000092a979baa5e2de9753039222a249b03926000109000af40054daa5ccea972faa5caea9723aa5c4c167249b930e6e4bf9b928e6e49b9b924e6e48b03dc916e4db5b926d6e4935b922c17724, 0x5dc9000141000e26492b3924aae492a305dc92c92b3b24aaec92a3039252e549bb9524ee548b0392500015d000f6400649003af4014ad00633401d550392624e4c39392fe49733925cbe4972b93928dd249393922c00724, 0x99528e6549b99524e6548b03d251654db59532d654bb59526d6549359522c16794050b0a8f4bb0312500015179532de92ab4bca8de549b79524de548b024a20a915f01454a424c39092ec0511205e090102d29412ec10292, 0x98124e6048b05e4913205b90130e404a390122c17b240005240044d001eb400b3d003ce4013950063541249405614a092cf039250001414d4afea92b3aa4abea92abaa4a8ea549ba9524ea548b05a452654c39952fe654bb, 0x49416ca904f49412d2503f4940eca902f480a8c177244b816dc904f72412d2e03f7240bdc04a370124c0f4804bc16de904f7a412de049b78124de048b041001604db58132d6049b58124d6048b05a402604c398128e6049b, 0x158004d416d3504b4d40fd3503baa40bea04a3a8126ea9017a8124ea048b024a00a905f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k1545 : region H42 0x8001000000001001000008010000010000000000008100100009000900089888 0x100000000 := regionTerm _ _ prog42k1545 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k5 : region H42 0x8001000000001001000008010000010000000000008100100009000900089888 0x0 := regionFork _ _ _ 32 reg42k6 reg42k1545
def prog42k1943 : Array Nat := #[0x5040032100142400388b88e6c1415a058e600010905e90817a22058e22e239b058e600010905d5081752205a622e239b05a66000109000aa40065105a6700015d002cb40123d006ae402cd5011444061c90212540a881, 0x38c20001510010a4007ad00276400ecd058e21e23d3788f3de23ab788e6c1679c7d0f3df43ab7d0e6c1651c7a8f3dea39b05a66000129000d440058904ce21623db588e6c1699802d1480b42a05a660105d20416a816398, 0x1f6400c090046e4169b874cf4dd33ab99dc8e6e39b9b8e2c1439805a90816a0a01cc2000151b1dccec772fb1dcaec772303dc716e39b5b8e2c0e51c7a8e6dea38b05dc700013d728f4c0f71c7d0e6df438b05dc700013d, 0x54e201415a05690a8713f05aa20001513d453ea712fa88eaea239b03ce6016a4204ce6000151b1eacec7aafb1eaaec7aa3056860f534fa9ccbea63ab055e701445e454f3c1442e055e7000121056908159a800054400519, 0x58e40c725f31c93c133900409681699005d1481742a05a6700015d058e400012100110400599001e2400a39003eb4012bd0059541371c74cf4ea799ba9e62c14388a88e6c14398000424002cda9dccea772fa9dcaea7723, 0x564f524f3d48eea722fa90eaea439ba90e2c16710790f4de43cf790eade439b790e2c13390590f6d643bb590e6d6438b01cc4016242b1dccec77230588281771c000565c43d371c93dc43ab01c8208715f0105688714f, 0x58548161123c853c1039805a14816812848f3c0731000050400389b1e4cec792bb1e48c12390990e6c123980004466794399e48e6790b05e4700014d00156400cad003ef4013d50078e40f390b1eacec7aa305890815a10, 0x7c8f4df23cf7c8e6df2393000072a799ba9e64e67943040e42a439b040e6000111000b340053da9e4cea792fa9e4aea7923a9e42c1691c7c8f4df23cf7c8eadf239b7c8e4df238b04e471723db5c8e6d723935c8e2c1791c, 0x5e47000151000e45c72b371caadc72a305e472c72b3b1caaec72a3048e52e539bb94e4ee538b048e500015d000f6400639003b34014ad0062f401d55048e61d23d3748f3e4773391dcbe4e3ab91dc8dd2393938e2c1079c, 0x794eade539b794e4de538b04ce51653db594f2d653bb594e6d65393594e2c16994040b4a133cb030e5000141994eecf32ab99ca8e6539b994e4e6538b01ca40a725f710f4dc43cb0149080520a05dc71d43cb050b081428a, 0x580e4d6038b04ce00f305b980e6e60393980e2c17b1c0005340042d001cf400b3900452401595006b540e39405690a872bf048e50001513d4b3ea72b3a9cabea72aba9ca8ea539ba94e4ea538b059c51e53d3794f3de53cb, 0x3940eca702f380aac1791c3c816cf204f91c0fe4703b91c0be403ab900e2c0e38011c17c4703f038c00001093b816dc03d371c13dc702f700eadc0393058e01e03d3780f3de03ab780e6de0393780e2c13380580f6d6039b, 0x15a003d416cf504f3d412cf503ba9c0bea03aba80e6ea7017a80e4ea038b01ca00a705f39416ce504f39412ca703f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k1943 : region H42 0x8001000000001001000008010000010000000000008100100009000800099888 0x10000 := regionTerm _ _ prog42k1943 adj42 _ _ 26 (by decide +kernel)
def prog42k2344 : Array Nat := #[0xa9d28ea939baa4e4c1649c7a4f4de93cf7a4eade939b7a4e4c1649c99d30e674a399d26e67493059272c93abb1d28d3639b4d8e4c09390490e6c09398000444002d9001734008bd0031540118900560401a490080e402695, 0x4c8f6d323d791d30e474bf924eae474a34c8e6d32393924e2e49383024e012705b49c15ce904f49c0fd2039b480e4d2038b024e21223db49c55ce914f49c4fd2239b488e4c1549c05614a093cf055e70001414d4f6ea93ab, 0x24e51253db49cb5ce92cf494f2d272bf494eece92ab49ca8d2539b494e4d2538b49ca0c0e49c4b8f6d2e3d7724f4dc93cf724f2dc93ab71d28d2e39b724e4d2e38b724e0c1249c]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k2344 : region H42 0x8001000000001001000008010000010000000000008100100009000900099888 0x100010000 := regionTerm _ _ prog42k2344 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k1942 : region H42 0x8001000000001001000008010000010000000000008100100009000900099888 0x10000 := regionFork _ _ _ 32 reg42k1943 reg42k2344
private theorem reg42k4 : region H42 0x8001000000001001000008010000010000000000008100100009000900099888 0x0 := regionFork _ _ _ 16 reg42k5 reg42k1942
def prog42k2436 : Array Nat := #[0x544003110014a40a18804157aca1b305d8300012905a1481681205d432ca1b305d830001290585481611205dca2ca1b305dcc000129000a240064105dc3000159002c5401249006b3402cd5011484061bd0212b40a881, 0x4d8a0001410010240079500277400eb905d4324a1c39286ee4a1b392862c1780c9406ee501b394062c171889086ee421b305dcc000109000d04005a9039430aa1df2a86cc177300149080520a05dcc0142c2050a281760c, 0x1f7400c29004734179b89b870dd31b374c6ae637139b862c1060c05e1481782a03143000141b8e66ee3997b8e64ee398b04e020b31b32cc6ac131889086ce421ab05a6300014998870c1380c9406ce501ab05a63000149, 0x554301055e05614a0354b05eaa0001415546eeaa1b3a8d45eaa18b0498301785203983000141b8ea6ee3a97b8ea4ee3a8b0560c1951bba8d85eac18b0560201025a2546ec10216056430001110561481570800050400531, 0x5c6218345b60d0ec0e40c051178177200589081620a05dc300015905d03000111001144005b1001ea400a4d003e54012c90059540070c9b870ea3733a8dcac1050caa86cc1060c0004a4002b9a8e66ea3997a8e64ea398b, 0x575151cf4546eea81b3aa06aea3417aa062c179a092070e481bb9206ce481ab92062c0e40c2a077ca81cf2a06cca81ab03103017452b8e66ee399305d0a81698c000576681c39a06ee6818b0006200a45e50d16d4343b, 0x5d5081752253c6ec0f60c05e90817a22a3c6ec0c40c000544003a9b8de6ee3793b8de2c0f40c7206cc0f60c000485e375378dcade3713059e300013900157400c95003f24013d50079341040cb8ea6ee3a9305d14815820, 0x93c70e4f1bb93c6ce4f1a3000032a3733a8dc8de375303d032a81b303d83000121000ae400549a8deaea379ba8de5ea3793a8de2c1778c93c70e4f1bb93c6ce4f1ab93c68e4f18b03dc30af1df2bc6ccaf1ab2bc68c1678c, 0x59e3000141000e866359b98d64e6358b059e32e359bb8d64ee358b03d632cb1b3b2c6aecb1a303d63000159000f740064d003ae40149500632401d5503d8326f1c39bc6edf31ab9bc68e6379b98de5e637939bc62c0078c, 0x92c6ce4b1ab92c68e4b18b039630ab1df2ac73cab1bf2ac6ccab1ab2ac68c1772c05170a8e1bf02cc300015172c73dcb1b372c6adcb1a370d64d6e18b0010316345b02d14a681c39a06fc0b42a05a030105d29c06fc105aa, 0x90068e4018b05a6307305f98070e601a398062c17b0c00053400449001e5400b39003cf4013ad0063541358c05614a035cb03d630001415d46eeab1b3aac6aeab1a3a8d66ea3597a8d64eab18b05e6b24b1c392c6fe4b1bb, 0x58c16c6b04f58c12c6b03f58c0ed6301758062c1678c1bc17de304f78c12c6f03b7806ade301778062c0e1801b817dc304f70c12dc01b37006adc01a3040400a01df28073ca01b32806aca01a305e602401c39006ce401ab, 0x158001d417c7504f1d40fc7503ba806cea302fa806aea01a3a8c05ea018b02c6006b05f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k2436 : region H42 0x8001000000001001000008010000010000000000008100100009000800089988 0x100 := regionTerm _ _ prog42k2436 adj42 _ _ 26 (by decide +kernel)
def prog42k2833 : Array Nat := #[0x91c70e471b391c6be471ab91c68e4718b058e32671c33cc6ae671a398ce6e6339399c62c0038c58cf6d6339b58ce4d6338b05ce32c71b3b1c6aec71a305ce3000159000eb4006cd002b2400e95004af4017b9007d5402701, 0xa9c62c0728c29c77ca71bf01cc300011570cf4dc71cf70cf2dc71b371c6bdc71ab71c68dc33933b862c1638c78cf4de33cf78cf2de33ab78ce6de339778ce4de338b040e20a71df29c73ca71b329c6bca71ab29c68c1799c, 0x1c6006705f38c16ce305738c13ce304b19c0fce303b19c0bce01ab38c05ce018b000e301585280cf2c0f38c000504f51cf3d46eea71b3a9c6bea71aba9c68ea339ba8ce5ea3393]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k2833 : region H42 0x8001000000001001000008010000010000000000008100100009000800099988 0x10100 := regionTerm _ _ prog42k2833 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k2435 : region H42 0x8001000000001001000008010000010000000000008100100009000800099988 0x100 := regionFork _ _ _ 16 reg42k2436 reg42k2833
def prog42k2923 : Array Nat := #[0x92470e491b39246be491ab92468e4918b059232634c398d28e6349b98d24e6348b025031634db58d26d6349358d22c1748cb246cec91abb2468c1748c000564003ad001b3400a490038540123d005ee401dd500900402b1d, 0xa8d25ea3493aa462c1772472473dc34cb4b870d2e1bf7246cdc91af7246adc91a370d24d2e18b059e31e91cf78d32d2f1c37a46ad2f1a378d26de349778d24de918b041220a91df2a473ca91b32a46bca91ab2a468c179a4, 0x49c70d271bf49c6ece91ab49c68d2339b48ce5d2339349c62d271830246006905f48c16d230571a413d2304b48070d2303f48c0ec6902f48068d2301748062c0048c4d470d351bf4d46eea91b3aa46bea91abaa468ea349b, 0x38c48cf6d271d73a473d233cb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k2923 : region H42 0x8001000000001001000008010000010000000000008100100009000900099988 0x100000100 := regionTerm _ _ prog42k2923 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k2434 : region H42 0x8001000000001001000008010000010000000000008100100009000900099988 0x100 := regionFork _ _ _ 32 reg42k2435 reg42k2923
private theorem reg42k3 : region H42 0x8001000000001001000008010000010000000000008100100009000900099988 0x0 := regionFork _ _ _ 8 reg42k4 reg42k2434
def prog42k3027 : Array Nat := #[0x504003090014840040405117ac80b305d8100012105a90816a0a05d012c80b305d810001210589081620a05e482c80b305e4c000121000a440065105e41000159002c5401239006af402cd50114a4061cd0212b40a881, 0x3d880001510010440079500277400ec905d011c80d372032dc80b372024c1770475032dd40b375024c1720471032dc40b305e4c000111000d44005a1049010a80df2a02cc179300145480511205e4c0102d2040a4817604, 0x1f7400c210046f41793c7c834e4f0b393c28df2093905e2c1460405e90817a2203101000151b85e6ee1797b85e4ee178b03dc10af0b32bc28c0f2047102cdc40a3059e100013979034c0f7047502cdd40a3059e1000139, 0x550101445e05690a8143b05ea800015145432ea80b3a8505ea809303981017a4204981000151b86a6ee1a97b86a4ee1a8b0568c1950cba8585eac093055c101415a15432c14116055c10001090569081591000054400531, 0x5c4118155b60552c12504041578179280585481611205e4100015905d41000109001104005b1001e8400a3d003e54012b9005954127047c834ea1933a8648c14404aa02cc14604000484002c9a85e6ea1797a85e4ea178b, 0x575550cb5542feaa0b3aa828ea1517aa824c177a872834dca0cb7282cdca0a372824c125042a837caa0bf2a82ccaa0a303141017542b85e6ee178b05d48816784000575ea0d37a832dea0930000100a45e50516d4144b, 0x5d1481742a44c32c1060405e1481782a84c32c0c504000504003a1b8666ee1993b8662c135049282cc136040004a66194398648e6190b05a6100014900157400c95003ee4013d50078f40e504b86a6ee1a8b05d50815a28, 0x74c34dd30cb74c2cdd30ab000012a1933a864ae61943041412aa0b304181000129000b2400539a8668ea199ba8665ea1993a8662c1798474c34dd30cb74c2cdd30ab74c28dd309304e410b30df2cc2ccb30ab2cc28c16984, 0x5a61000151000ea5e159b78564de158b05a612e159bb8564ee158b04d612cb0b3b2c2aecb0a304d61000159000f740063d003b24014950062e401d5504d811f30d37cc32df30ab9bc28e6179b985e5e6f093985e2c10704, 0x72c2cdcb0ab72c28dcb093049610ab0df2ac33cab0bf2ac2ccab0ab2ac28c1792c04174a120cf02cc100014192c2fe4b0b392c2ae4b0a35c824e4158b0014116155b7a834dea0cf02d5080b522059e11f40cf051708145a2, 0x2802aca00a30482003205f9002ce400ab90028c17b0400052400415001ce400b3d004534015ad006b540f58405690a815bb04d610001515d432eab0b3aac2aeab0a3a8566ea1597aac24ea158b05deb1cb0d372c33dcb0cb, 0x5840ed6101758024c169840cc17c3304b9840fe6103b98028e6101798024c0f08040416d0103b03d800001210bc17de00d378412de00ab78405de009305c201c00d370032dc00b37002adc00a370024c1208028037ca00b3, 0x15a000d417c3504f0d412c3503fa802cea102fa802aea00a3a8405ea009302c2002b05f58416c2b04f58412c2b03f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k3027 : region H42 0x8001000000001001000008010000010000000000008100100009000800089898 0x10 := regionTerm _ _ prog42k3027 adj42 _ _ 26 (by decide +kernel)
def prog42k3428 : Array Nat := #[0xa8c2aea3093a8462c1718470c34dc30cb70c2cdc30ab70c24c1718490470e411b39046ae4118b05c610770b31dc2aee3093b8462c0a1841a82cc0c1840004a4002dd001724008b9003154011a100560401a4d0080f4026ad, 0x1cc37c730d798470e611bb1cc2cc730ab98c28e6309398462e6308300c2006105f18415c2304b1840ec600b31802ac600a3020610680df40c35d030cb4046ec680b31a02ac1518405614a030cb055c10001411d437ea30b3, 0x2c6106b0df58c35c6b0cf58c32c6b0bf5846ec6b0b31ac2ac6b0a358c24d6118b58c20c0f1841bc37c6f0d778c34de30cf78c32c6f0b378c2ac6f0a378c24de118b78c20c13184]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k3428 : region H42 0x8001000000001001000008010000010000000000008100100009000800089998 0x110 := regionTerm _ _ prog42k3428 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k3026 : region H42 0x8001000000001001000008010000010000000000008100100009000800089998 0x10 := regionFork _ _ _ 8 reg42k3027 reg42k3428
def prog42k3518 : Array Nat := #[0x9242ce490af9242ae490a34c824e4148b059212614c398528e6149b98524e6148b025011614db58526d6149358522c17484b242cec90abb2428c17484000564003ad001b3400a49003a54012b9005ef401f55009c0402d8d, 0x1211614db5852ec0c4840004b5e90d37a433de90cb7a42ad2f0a378526de14977a424de148b05d211c90d372433dc90cb7242cdc90af7242adc90a372424c124842a437ca90cf2a42cca90af2a42aca90a3024c12414c3, 0x1a42ad230a348c24d2118b48c20c090800a417d2105b48415c2904f48412d2103f4840ec2902f48028d2101748024c0048405614a090cf039210001414d432d350bfaa42cea90afaa42aea90a3a8526ea1497aa424ea148b, 0x24610690df48c35c690cf48c32d211c348c2fd211bb1a42cc690af]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k3518 : region H42 0x8001000000001001000008010000010000000000008100100009000900089998 0x100000010 := regionTerm _ _ prog42k3518 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k3025 : region H42 0x8001000000001001000008010000010000000000008100100009000900089998 0x10 := regionFork _ _ _ 32 reg42k3026 reg42k3518
def prog42k3624 : Array Nat := #[0x71c2cdc70af71c2adc70a371c24c16384784f4de13ab784e6de1393784e2c00384584f6d6139b584e4d6138b05ce12c70b3b1c2aec70a305ce1000159000eb4006bd0028e400e15004934017c90077540240100ac940330d, 0xa9c24ea138b05e470f20d33c833e470bf904eee470b391c2be470ab91c28cf2093904e2c169843cc34e670bf984eecf30ab99c28e6139b984e5e67093984e2c0e38429c37ca70bf29c2cca70af29c2aca70a305de71c70d3, 0x49c2fd213bb3a42ad270a3484e6d2139749c24d2138b49c20c0708009c17ce105b38415ce00d338413ce104b09c0fce103b09c0bce00ab38405ce0093000e10f50d33d433cf50cba9c2cea70afa9c2aea70a3a84e6ea1397, 0x1c610670df38c35ce30d338c33ce30cb19c2fce11bb19c2cc670af38c2ace30a719c28ce309338462ce3083024e11213db49c35ce90d33a433d270cb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k3624 : region H42 0x8001000000001001000008010000010000000000008100100009000900099998 0x10010 := regionTerm _ _ prog42k3624 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k3024 : region H42 0x8001000000001001000008010000010000000000008100100009000900099998 0x10 := regionFork _ _ _ 16 reg42k3025 reg42k3624
private theorem reg42k2 : region H42 0x8001000000001001000008010000010000000000008100100009000900099998 0x0 := regionFork _ _ _ 4 reg42k3 reg42k3024
def prog42k3747 : Array Nat := #[0x521781485a052158106289c22fe7089b041ea2aa8b3aaa26c168bc0005541055e04586000129001334006d10025241179864556d9155764552c0f5180004c40f6180004a4004c100404401d3900d48404b89019ab408e95, 0x38a4014bd05a510d125f34495cd124f3448fc115100415795125784552d5123f045e419125784592c107900004c40032904096a1124f031441512575448fc0f6100004a400341002864008189422fe508b39422ac138bc, 0x394600014174552e2a7338a9c4c007309ba30e6e89b9ba24c10730ab226c117180521781485a0458600015103986000141001155d164b8b1c4c117100521781485a052158113100005461174b038c40001410014c400bcd, 0x9a230e688bf9a226e68893045e400a45e54516c16890b9226c168980004441745205a2f00015d0010a40064d00252400c55003ce4116187c5d4df174f7c5d2df172b7c5c4c11718052168148560454600015104157a1174f, 0x5e2e0001590018f400d11003f5401349005d3411718052168148560390600014105117a8e8bf0450600015174513dd144b8a1cce2872b8a1c4c107a0aa22cea88abaa226ea8893020c42488c39222fe488b39222ac0c520, 0x52222a28b3a8a2aea28a3a8a26ea2893045c209115f0105689113f045e201415aa3e2ec1140864516d9143b0450200013104582000121001146227ab889e6c178a8b2a2ceca8a305e282c88b305e2c000121000aa416152, 0x844d3e2b33f05a71000119041748105aa03d662cb8b3b2e2ac1179800056400341001c4400c21004624019c9007754021b9031422628c398a2fe628bb98a28e6289b98a24c0620890a30e428bf90a2ee428b390a2ae428a3, 0x44453c0b42a05a220105d284453c105aa05a22000141000e862b13f88966e22593031682688c39a22fe6889b9a224c113100005357145b02d1480b42a0456401025a04174a1124f0416a8168900005062b23f89166c16898, 0x7754021bd00a0b41172c04174a1174f03dcb00014174572e2b7338adcae2b7238b966e2e5938b962c107acaae2ceab8abaae28eab89baae24eab88b02cc424b8c392e2fe4b8b392e2ae4b8a392e22c114085c516c0b452, 0x90a2ac11628000524b115f014548051120454501055e040b4a1154b040a48178a80005062553b8a8acc178b084592e2563b05e51000131040b4810292039852e589bb9624c1173000057400341001ca400c09004684019cd, 0xa962cea58aba9628ea589ba9624ea588b031452658c39962ee658a399626e6589399622c114082c457c0515244452c0511205e280102d284512c1029205e28000141000e262543b8a0ace282ab018a22428c390a2ee428b3, 0x105945c4b5e2b2bf8956ee2b2b38acaae2b2a389566e2559389562c11714040b4a117cb03dc50001417c4b3e2f2b38bcaae2f2a3895e6e25793895e2c10714]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k3747 : region H42 0x8001000000001001000008010000010100000000008100100009000800089880 0x100000000000000000000000000000000 := regionTerm _ _ prog42k3747 adj42 _ _ 26 (by decide +kernel)
def prog42k4122 : Array Nat := #[0xa8222c0c50098230e608bf98228e6089b98224e6088b018802408c39022fe408b39022ae408a390222c10780b022cec08a3045e0000159881eae2079b881e4e2078b05ed100013d00192400a4d00395401239006ab401f95, 0x880a8c138805c416d710575c412e2b03f8ac0ee2059b88164e2058b045c005105f14415c1170034417cd1057041c0000119000c25d104f74412e2e03f881cce2072b881c8e20713041e02a08b3a822aea08a3a8226ea0893, 0x128802c417cb10572c413e2503f8940ee202b38940be202ab]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k4122 : region H42 0x8001000000001001000008010000010100000000008100100009000800089888 0x100000000000000000000000000000008 := regionTerm _ _ prog42k4122 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k3746 : region H42 0x8001000000001001000008010000010100000000008100100009000800089888 0x100000000000000000000000000000000 := regionFork _ _ _ 3 reg42k3747 reg42k4122
def prog42k4195 : Array Nat := #[0x8a48be2449b001262498c39262fe498b39262be498ab041e92a98b3aa62bea98abaa626c1689889930e2933f8a4cbc107a4b262cec98afb262ac1183c000564003990019540094900324401221005a2401bb900865402801, 0x8a5cce2972f8a5cae2e4a38b926e2e4938b922c168884c455d3114b88930e2913f8a44be224a388926e224930452813145b4c515d3144b8a130e284bf8a126e28493045241514db54532c0c4900004a53125789130e2923f, 0x114804c416d310574c412e204c38a40fe2903b8a40be204a388126e2901788124e2048b001251312d789530e292bf8952ee292b38a4abe292ab8a4a8e2549b89524e2548b001c91d14cb8b930e2e4bf]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k4195 : region H42 0x8001000000001001000008010000010100000000008100100009000900089888 0x100000000000000000000000100000000 := regionTerm _ _ prog42k4195 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k3745 : region H42 0x8001000000001001000008010000010100000000008100100009000900089888 0x100000000000000000000000000000000 := regionFork _ _ _ 32 reg42k3746 reg42k4195
def prog42k4288 : Array Nat := #[0x91e28c00390058908f124f890e6c10398000446c78b3b1e2bec78abb1e28c113903c493e2722f890eae2439b045472678c399e28e6789b044e600014d000e44006d900312400fbd004f5401789007ce40251500ae04032a5, 0x5854ac78b3b1e28c11388000564f11573c453cf114b89c4fe2712f888eae2239b888e4c1079ca9e2cea78afa9e2aea78a3a9e26ea789305a271f13d37c4f3df13cb7c4eadf139b7c4e4c0731091e30e478b391e2be478ab, 0x89c0fe2703b89c0be203ab880e6e27017880e4e2038b040e50f12d73c4b3e272bf894eee272b389cabe272ab89ca8e2539b894e4e2538b045c71d13d3744f3dd13cb89dcce2772f8b8eae277238b8e6e2e3938b8e2c10388, 0x1149c4c4f6d313d74c4f2e274c389d2fe293bb8a4eae274a38a4e6e293978a4e4e2938b8a4e0c113803c416cf10573c413cf104b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k4288 : region H42 0x8001000000001001000008010000010100000000008100100009000900099888 0x100000000000000000000000000010000 := regionTerm _ _ prog42k4288 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k3744 : region H42 0x8001000000001001000008010000010100000000008100100009000900099888 0x100000000000000000000000000000000 := regionFork _ _ _ 16 reg42k3745 reg42k4288
def prog42k4403 : Array Nat := #[0x8b86ce2e1ab88dc4c0080ca8e2cea38aba8e26ea389305e302111cf8c06ce301ab0458a0911df24473c1162834477cd11cf03143000119000c4400541001f5400ab90038540118900588401b3d0084b40278100ba940361d, 0x8bc6ae2f1a388de6e2379788de4e2f18b05e281111d744473e281c38a06ee281b38a06ae234178a062c111881c457c711571c453e221c38886ee221b38886ac118382c477cb11d72c473cb11b32c46ac0e30c74473e2e1c3, 0x8a462e291830446007105f1c415c7104f88070e2303f88c0ee201b388c0be201ab88068e2301788062c0058c5c475e2b1c38ac6fe2b1bb8ac6ce2b1ab8ac68e2359b88d65e235938ac62c0078c7c473e2f1c38bc6ee2f1b3, 0xe30f11d73c473e271c389c6fe271bb89c6ce271af89c6ae271a789c68e2339b88ce5e2339389c62e27183001231311d78a470e291bf8a46ee291b38a46be291ab8a468e2349b88d25e23493]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k4403 : region H42 0x8001000000001001000008010000010100000000008100100009000900099988 0x100000000000000000000000000000100 := regionTerm _ _ prog42k4403 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k3743 : region H42 0x8001000000001001000008010000010100000000008100100009000900099988 0x100000000000000000000000000000000 := regionFork _ _ _ 8 reg42k3744 reg42k4403
def prog42k4527 : Array Nat := #[0x5d509510cb8a82cc106040004a6e189bb8625ee1893b8622c1150454432e2a0b388545e2a093044812418c39062ce4188b04581000149000ea4006dd00313400fb9004f54017a1007cf40252d00ae040328d00e8940429d, 0xb8622c11404000575110d744433d110cb8850ee280b38a02ae214178a024c10704a862cea18aba8626ea1897a8624ea188b05e211d10d374433dd10cb7442cdd10ab74424c0c50498630e6189b98625e6189398622c00504, 0x8802ce2102f8802ae200a388405e20093041611710d75c432e2b0bf8856ee2b0b38ac2ae2b0a388566e215978ac24e2158b045c11f10d37c433df10cb8bc2ce2f0ab8bc28e2179b885e5e2f093885e2c1040405d14ae189b, 0x8852ee290b38a42be290ab8a428e2149b88525e290938a423e2148b8a420c111841c437c710d71c433e211c388c2fe211bb88c2ce230af88c2ae230a388c24e2118b88c20c110800c417c310570c413c3104b8840fe2103b, 0x103843c435cf10d33c433cf10cb89c2fe213bb89c2ce270af89c2ae270a789c28e2139b884e5e2709389c23e2138b89c20c004844c435d310cb88530e290bf]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k4527 : region H42 0x8001000000001001000008010000010100000000008100100009000900099998 0x100000000000000000000000000000010 := regionTerm _ _ prog42k4527 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k3742 : region H42 0x8001000000001001000008010000010100000000008100100009000900099998 0x100000000000000000000000000000000 := regionFork _ _ _ 4 reg42k3743 reg42k4527
private theorem reg42k1 : region H42 0x8001000000001001000008010000010100000000008100100009000900099998 0x0 := regionFork _ _ _ 128 reg42k2 reg42k3742
def prog42k4684 : Array Nat := #[0x521781485a052158146207d1b3df469b001a82a86b3aa1a6c169b40005541445e035860001210012f4006c10024e41369863516d8d4576350ec134180004c413618000484004d100402401d4900d4a404b91019ab409015, 0x3884014cd059cd0cd15f33455ccd14f3344fc0d4080511790d157a350ed0d14f041a218d157a358ec149880004c40032105056a8d13f0310210d15743453c136080004840035100286414698751b3dd46b3751a8c137b4, 0x49060001519350ee486b3921a2c126b07c9b4df269b7c9a2c106b0ab1a6c126980521781485a04986000151035860001410011564d63b931a2c106880521781485a0521580d3080005068d93b048c20001510014c400bbd, 0x7a9b4dea6cf7a9a6dea68b04da200a45e53516c16688b89a6c166980004241754205a6d00015d0010840063d0024e400c55003d240d6189b650e6d93f9b64ee6d9239b642c12698052168148560350600014105117a8d93f, 0x5e4d00015900193400d09003f5401339005cf412698052168148560494600015104157a126cf035460001419354fe4d53b929ace4a6a3929a2c149a8aa9aceaa6a3aa9a6eaa68b028c21ca6d3729b3dca6b3729a8c0c520, 0x41a42a46b3a91aaea46a3a91a6ea468b049a208d15f0105688d14f041a401025a84db2c0d51063556d8d54b0354400013103584000129001106646a3991a6c176a0b21acec86ab05daa2ca6b305dac000129000a8416242, 0xa34cfdab34f059ed000119051708145a204d662cb6b3b2da8c1369800056400351001c4400ba9004424019c9007f5402539031041e46d3791b3de46cb791aade469b791a2c06208711b4dc46cf711b2dc46b3711aadc46a3, 0x5344fc0b5220356201415a05170a8d13f05168816688000544004296ac53da259b68964c0c5a87a9b4dea6cf7a9a6dea693034c400013d5b556c0b54202d4881669005170a8d23f05168816690000545ab24f69166c16698, 0x2cc21cb6d372db3dcb6cb72dacdcb6ab72da8dcb69303dab015a4204e4b000151aadaceab6abaada8eab69baada4eab68b049ab0105d2849b3c0f6ac0005064b6b392daae4b6a36c966db259393562c0d5085b556c0b542, 0x4e4ad25f0149080520a05daa0142c2a354ec1428a05daa00015169552daa2b305dac28d63b69592c177340004c4142c2050a2812614b95a6ee568b049ac00015d000d4400729002e440112100673401fd50094f4029ad, 0x40b4a136cb039a50001416ccacdb32ab9b4a8e6569b995a4e6568b035040ad25f0149090d23b0148280d414051178142c2a350ec1428a05da8000151001045a544b6a0acda82ab018a41c46d3711b2dc46b3711aac0d628, 0x145945b4b5dab2cf69572dab2b36acaadab2a369566da559369562c0c414795b4de56cf795b2de56ab795a6de5693795a2c0e69405690813914000546a56b3a95aaea56a3a95a6ea5693a95a2c13694]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k4684 : region H42 0x8001000000001001000008010000010000000000008100110009000800089880 0x10000000000000000 := regionTerm _ _ prog42k4684 adj42 _ _ 26 (by decide +kernel)
def prog42k5065 : Array Nat := #[0xa81aaea06a3a81a6ea0693a81a2c10680b81a6ee0693041a000015d6c813e406b3901aae406a3901a2c10680b01acec06ab041a0000159981a8e6069b981a4e6068b05ecd00014d00192400bd5003ef4014390062b401d95, 0x2b40fda02b36940bda02ab680a8c0f6805b416d6d0576ac13dab04b5b40eda059b68164da058b018401c06d3701b3dc06cb701acdc06ab701a8dc0693031001e06d3781b3de06cb781aade069b781a4de068b041a02a06b3, 0xe6802b417cad05769413da504b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k5065 : region H42 0x8001000000001001000008010000010000000000008100110009000800089888 0x10000000000000008 := regionTerm _ _ prog42k5065 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k4683 : region H42 0x8001000000001001000008010000010000000000008100110009000800089888 0x10000000000000000 := regionFork _ _ _ 3 reg42k4684 reg42k5065
def prog42k5134 : Array Nat := #[0x69c4bda239b000e61c76d371db3dc76b371dabdc76a3052672a76b3a9dabea76a3a9da6c16698698f4da734f69ccbc1499cb1dacec76afb1da8c149b4000564003990019540093900322401229005a4401bc900865402801, 0x91dace476af934eae476a36c8e6db2393934e2c166903b495da43d369c93ced23b69c8bda43ab690e6da438b0354714d3db534f5daa3d36a8f3d4d3bb6a8e6daa38b034e210d3db434eec0c388000484ed157688f4da714f, 0xd3803b416ced057680f4da704f69c12ced03b69c0bda03ab680e6da7017680e4da038b000e50ed2d7694f4da72cf694f2da72b369cabda72ab69ca8da539b694e4da538b049a71b23d36c8f3e4d3bb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k5134 : region H42 0x8001000000001001000008010000010000000000008100110009000800099888 0x10000000000010000 := regionTerm _ _ prog42k5134 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k4682 : region H42 0x8001000000001001000008010000010000000000008100110009000800099888 0x10000000000000000 := regionFork _ _ _ 16 reg42k4683 reg42k5134
def prog42k5227 : Array Nat := #[0x9b522c004880585492d13f68926c14498000426c96b3b25abec96abb25a8c0d4884b44fda912f68928da249b035281e96d37a5aade969b0352600013d000e24006d900313400fb9004f5401791007d240251500ae040329d, 0x5890ac96b3b25aac0d4900005652d2576a493d2d23f4b48eda922f69128da449b69122c149a4aa5acea96afaa5aaea96a3aa5a6ea968b024c21c96d3725b3dc96b3725abdc96ab725a8c166a49b530e6d4bf9b528e6d49b, 0x4b40fd2d03b6a40bda04a368126da901768124da048b0512512d2d76a4b3da54cb4b4afda92b36a4abda92ab6a4a8da549b69524da548b001a924d4c39352fe4d4bb925ace496af925aae4d4a36c926db249393522c0d490, 0xd49c4b4f6d2d3d76a4f4da93cf6a4f2d2d3bb6a4eada74a36a4e6da93976a4e4da938b6a4e0c0d4804b416d2d0576a413da904b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k5227 : region H42 0x8001000000001001000008010000010000000000008100110009000900099888 0x10000000100000000 := regionTerm _ _ prog42k5227 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k4681 : region H42 0x8001000000001001000008010000010000000000008100110009000900099888 0x10000000000000000 := regionFork _ _ _ 32 reg42k4682 reg42k5227
def prog42k5342 : Array Nat := #[0x8a9ace2a6af8a9a6c0069893630e4d8bf9362ce4d8af041a61b134f8b4cfe266b38b4cbc1162c7c5b4df16cf041ab22b6b3041ac00012d000af400499001f2400aa900384401221005ae401b890084540288100be940371d, 0x8b44be226ab889a8e2269b889a4c11698745b4dd16cf745b2dd16b3745abdd16ab745a8dd1693052281b144f6c512e286b38a1abe286ab8a1a6e28693041a41b124f8b48fe246b38b48be246ab891a6c106a86c552e2d53f, 0x41a01b104f6c412e2d03f8b40ee206b38b40be206ab881a8e2069b8b405e20693881a2c11694040b4a116cb039a50001416c4b3e2d2bf8b4ace2d2af8b4aae2d2a3895a6e25693895a2c148886c453db114b8b44fe226b3, 0x1169c6c4f4db13cf6c4f2e2d3bb89dace276af8b4eae2d3a789da8e2d39b8b4e5e2d3938b4e2e2d383001a91b14cb8b530e2d4bf8b52ee296b38a5abe296ab8b528e2d49b8b525e2d4938b522e2d483]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k5342 : region H42 0x8001000000001001000008010000010100000000008100110009000900099888 0x100000000000000010000000000000000 := regionTerm _ _ prog42k5342 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k4680 : region H42 0x8001000000001001000008010000010100000000008100110009000900099888 0x10000000000000000 := regionFork _ _ _ 128 reg42k4681 reg42k5342
def prog42k5467 : Array Nat := #[0x93428e4168b051a12a16b3a85a8ea169ba85a2c17a34a342fdb40b36d028c0d62013437c4d0bf035880cd0df3342fc0c40400046400309001544007d5002b2400e1500464401629006d340212d009e0402ec500d87403e25, 0x9b428e6169b985a5e6d093985a2c176a853435daa0d36a832d4d0bf6a82cdaa0a368545daa0930348108d0df23435da40d369032c8d0bf6902cda40a30524d0ad0df2b435cad0bf2b42ccad0a3048c11b20d39342fe4d0b3, 0x8b420c0d0800b417c2d05768034da104f68412c2d03f6802cda102f6802ada00a368405da00930016116d0d76ac34dab0cf6ac32dab0b36ac2adab0a368566da15976ac24da158b04da11b30d36cc32e6d0bf6cc2cdb30ab, 0x68525da909368522da9083000e10ed0d769c34da70cf69c32da70c769c2cda70af69c2ada70a3684e6da139769c24da138b69c20c116846c434db10cf6c432e2d0bf8b42ce2d0af8b42ae2d0a3885a6e216978b424e2168b, 0x4844b435da90d36a433da90cb6a431d2d0bf6a42cda90af6a42ada90a36a427da149b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k5467 : region H42 0x8001000000001001000008010000010100000000008100110009000900099898 0x10000000000000010 := regionTerm _ _ prog42k5467 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k4679 : region H42 0x8001000000001001000008010000010100000000008100110009000900099898 0x10000000000000000 := regionFork _ _ _ 4 reg42k4680 reg42k5467
def prog42k5608 : Array Nat := #[0x4346eda81b305183000121b8da6ee3697b8da4ee368b0350310d1bb6a06cda34176a062c0d18870db4dc36b370da4c0d60c0004e4003a1001b7400c49003ef4013d5005ea401f4d0094b402b8100ca1403a4501087404b25, 0x354300015d53475da354b5346fd4d1bb6a86cdaa1a368d45daa18b052432a36b3a8da8ea369ba8da5ea3693a8da2c0c40c78db4de36cb78da6de369778da4de368b05da324d1c39346ee4d1b393468e4d18b00103017452, 0x68c0bda01ab68068da301768062c1458c5b475dab1cf68d72d6d1bb6ac6cdab1ab6ac68da359b68d65da35936ac62c0068c9b470e6d1bf9b46edb31b36cc6ae6d1a398da6e6369798da4e6d18b03543017542b8da6ee3693, 0x8b46ce2d1af8b46ae2d1a388da6e2369788da4e2d18b8b461e2d1830346106d0df1b435da30d368c33da30cb1b42fda30b368c2bda30ab68c28da309368462da30830346006d05f1b415da304f68c12c6d03f1b40eda01b3, 0x6a46bda91ab6a468da919f68d26da349768d24da918b6a461da9183000e30ed1d768cf4da71cf68cf2da71c73b46eda71b369c6bda71ab69c68da339b68ce5da339369c62da718769c60c0068c6c473e2d1c38b46fe2d1bb, 0xd48c4b475da91cf68d32da91c74b470d2d1bf4b46eda91b3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg42k5608 : region H42 0x8001000000001001000008010000010100000000008100110009000900099998 0x10000000000000100 := regionTerm _ _ prog42k5608 adj42 _ _ 26 (by decide +kernel)
private theorem reg42k4678 : region H42 0x8001000000001001000008010000010100000000008100110009000900099998 0x10000000000000000 := regionFork _ _ _ 8 reg42k4679 reg42k5608
private theorem reg42k0 : region H42 0x8001000000001001000008010000010100000000008100110009000900099998 0x0 := regionFork _ _ _ 64 reg42k1 reg42k4678
private theorem safe42 : hostSafe H42 := regionHost _ _ _ bk42 reg42k0
def H43 : Array Nat := #[0x1, 0x2, 0x3, 0x4, 0x5, 0x8, 0x9, 0x10, 0x12, 0x14, 0x17, 0x20, 0x22, 0x28, 0x2b, 0x40, 0x44, 0x48, 0x4d, 0x80, 0x90, 0xa0, 0xb2, 0xc0, 0xd4, 0xe8, 0xff]
def N43 : Array Nat := #[0x10000100001000400010001000100000000000001110000010500150114, 0x10000100001000000010001000100000000000021110000010100110332, 0x10000100001000000010001000100000000000001110000010100110110, 0x1000000000100040001000100010000000000000101000009050005030e, 0x10000000001000400010001000100000000000001010000010500050104, 0x10000100040001000100010000000000000011000000050095003e, 0x100001000400010001000100000000000000110000000500150014, 0x1000000000100000001000000010000000000002111000009050000033e, 0x10000000001000000010000000100000000000021110000010100000332, 0x1000000000100000001000000010000000000000101000009050000030e, 0x10000000001000000010000000100000000000001010000010100000100, 0x10000100000000000100010000000000002111000000000095033e, 0x100001000000000001000100000000000021110000000000110332, 0x10000100000000000100010000000000000011000000000095003e, 0x100001000000000001000100000000000000110000000000110010, 0x40001000100010000000000000000000009050095033e, 0x40001000100010000000000000000000009050005030e, 0x40001000100010000000000000000000000050095003e, 0x400010001000100000000000000000000000500050004, 0x2111000009050095033e, 0x2111000009050000033e, 0x2111000000000095033e, 0x21110000000000000332, 0x9050095033e, 0x9050000030e, 0x95003e, 0x0]
private theorem bk43 : bookOK H43 N43 0x800001000010000100040001000100010000000000002111000009050095033e = true := by decide +kernel
private theorem adj43 : validRows H43 N43 := rows_of_book _ _ _ bk43
def prog43k12 : Array Nat := #[0x75db8c18aa895636c18b28000554188a800052418928000514004dd055aa2558db059aa000155045aa000149049aa0001450012e41572895636c167280005541172800052412728000514004b5004b4401cc100c294062b1, 0x5641672800055400435002944149448d1aac14928000515d46e3751b7c128b48d1aac126a8000514002b9051ca2548db95235c11728000524127280005140043505eaa2558db05eca00015505e2a00014905e4a000145, 0xa360ec147280004d63485b8d215c146a8a360ec147280004d65485b95215c106a8a360ec107280004d4002c9001914128c0ac1aac16828000555d06e3741b7c16ab4ac1aac166a8000554002b9041ca2d0acbb42b1c15728, 0x8d616e3585304a090001458552ec148248d216e914bb051c925485b041c9000149000b1416724000544005d504a292914bb055c92558db059c9000155045c9000149000f441272400051400641003ca4020350520d2346ab, 0x5a2e00015154539d514df54535c159408552ec15938000505554e755537c17a3895216c17b380005441783800052417938000505574e70668e25485b066ce0001510660e0001490664e000141001374009d500351415824, 0x4e54d4e753537d4d4d753531c128a4725b8dc96df725b4dc96c3051a925485b041a9000149a3531c166a40005460d4d7055a92558db059a9000155045a90001498a5b4c126a4000514005410026e400ca904a302914bb, 0xa4592c12628000514002b90018d40e6b0bb22ac186280005764c8db93235c18bc4bb22ac188a8000574002c90498a30cbbbc32edc1792800058418928000574004450029440142500a70412524725b8dc96d3725b0c12834, 0x8b135e29653049491c966372597dc9653031492a964b05e4c1574e70664c00015d04989000129000f5400539001f1400eb50522c29164b8d1aac14928000515b46636d197c148a8a4592c14928000515d466375197c11628, 0x4a60c4d70418a000125001524007c50028e400f35000092a964baa591ea96ab0494914d4e753531c166240004a4003556a598da965f6a594c128a472598c128b00004e5514e7059891c966305989000139000aa5914df, 0x418a2d064bb4191c10628000564003556c198db065f6c194db06270398a22c85b8b215c12828000515d066374197dd065374189c0c5248b216e2c8578b214c0c52493216e4c85793214c1783055d39c1983000057410624, 0x41ac2b064bac191eb06ab]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k12 : region H43 0x8000010000100001000400010001000000000000000021100000090400900000 0x0 := regionTerm _ _ prog43k12 adj43 _ _ 28 (by decide +kernel)
def prog43k336 : Array Nat := #[0x4c728aabca2a9c15730aa592c15a4875198c18ac8000544159300004e4003a50564e0001310019941992472598dc9653066921d466306712000151000a94199300004e4199380004c4006d500497401c4100cad405245, 0x41c8000129000ec4009250039740124905d8819744bbb12ec179380004c5374674dd15c1773065d12c179380004c55746755d15c0e62065d12c127200004c4002a90018941492075198c18920000544126200004e412720, 0x92214e4883305e081374674dd15c10520000496e883bba20cc158204d519e154bb8552cc198308312ec198380004c4002d5041481d066374194c1583055519c19830000554106200004a4003b90560e1554670660e000155, 0xa3512c189340005454d46753517d4d457051881b46636d197c0e6a00004c68d44b05d881b766365d12c1792075db8c126a00004e4002b10624800015d0017440092900349401441029282e883b065c800015d92216e48857, 0x41481b066364112c12834741b8c166a00004e54d46704a081d06e3059a8000139000aa4005b1001e95b045f83515e086d30352828d44ba352ee8d4b3049a830d4bbc352cc126a4000584003514b519d2d45f4b515c0e6b0, 0x5450dc0e6a092236e488d792234e488b3052281d466304588000139a450dc188a00005459145f05e281d76e30622800015d045a80001398a1b4c117200004d40053100272400ca9004904019a5059a812d4678352ee0d4b3, 0xb4510c1172000056400331001545314674c517d314574c50dc00020ba22aee883bba20dc0e52054519d51437039a8000129000d762885b8a215e288538a20cc0e52092236e488d39222cc117300005255146754517d51457, 0x452829144ba4510e914bba452cc188a464512d91443045c82d144b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k336 : region H43 0x8000010000100001000400010001000000000000000021100000090400940000 0x40000 := regionTerm _ _ prog43k336 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k11 : region H43 0x8000010000100001000400010001000000000000000021100000090400940000 0x0 := regionFork _ _ _ 18 reg43k12 reg43k336
def prog43k570 : Array Nat := #[0x740d8dd035f0554621535b05946000155000ae400635039a62e6aab0614600015db1ab2ec6ac7062f52e6aab062aa00015d000b6416518c1aeef06bb705eca000161062ca00015d00115400a41005094029d10108c405821, 0x4e4002a94d4d7ea64c7aa4d0c16524724d8dc935f724d0c0a4988a4d6c17b1855d39c19b18000574164980004a4003c50014e4007d5003ad415818854d6eb06ab05a0a0001556c0d8db035f0560a21535b05a0a000155, 0x668600015d05126000129a1931c1451800049400559001f5400a390044d4004988a4d6e293578a5aac1652453539d4d4d704926000129000d15a93636a4d7da934305aa91c93630564600013955539c12498724d8c12498, 0x950d6e5435705146000149000d15b43636d0d7db43436d0c9c145188d0d6e343570514625435b950d5c0e51800052400345750d8dd435f750d0dd4327029262a6a4ba9a91ea6a43029262c6a4bb1a91ec6a4305e861574e7, 0x5146194363650d7e8664ba1991c1761865cd8eec8ab0618a00015d8b0d6e2c35705d8a1973630618a00015d930d6e4c35705d461973630614600015d000b240064500294400d41004294146988d0d6e343578d1aac14518, 0x5106000129000f8418a9855519c19c18000554184180004a4003d10024d400b5d003f2401745007a94024c10314924c35b02926000149624d8d8935f4b0d5d8935361931d893430418a190363640d7e0c35b830d5e0c353, 0x29061a83636a0d7c18ba055d19c0e4180004a418520000574003b5920d6e48357920d4e48333066e61d736375cd4c0a4180004e517357b990dee8333029061a83636a0d4c0a418c1a8ef06a330568615546706686000155, 0xa951035f820d6e08357820d4e06437820ccc00498624d8d8935361912c127180004c52646749917d2645749911d26437001061a83636a0d7e286ab0614815146754517c0e4180004a4003358a0d6e283578a0d4e28333, 0x10612646749911e064bb041481d036302906000139]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k570 : region H43 0x8000010000100001000400010001000000000000000021100000090400940200 0x200 := regionTerm _ _ prog43k570 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k10 : region H43 0x8000010000100001000400010001000000000000000021100000090400940200 0x0 := regionFork _ _ _ 9 reg43k11 reg43k570
def prog43k834 : Array Nat := #[0xc9229c117188a4d6c168c0740d8c18b44000504168980004e4003a505a2e00011900199419b24724d8dc9343066d01d036306716000141000a9419b180004e419b38000464006c500497401c5100c2d40505501cec40a021, 0x514005990031740105905cc40d725bb992ec17b38000465372674dc91c1771835c96c17b380004655726755c91c0e31035c96c16710000464002a900189416810740d8c18b10000504163100004e416710000467248ab, 0xb1292ec4a47b1290ec4a1b05e841372674dc91c14510000496e4a3bb9286c14510750d8dd4343750c9c1489854499c143100004a634327066860001450010e4148904c499e914bb0522e151267051c4000129000a9419a38, 0x4b491c0e69883496c18b340005054d26753497d4d247040c41b03636c0d7c0e6900004660d25b05cc41b736335c96c17b1075db8c166900004e400299062c400015d0017040092900349401451029242e4a3b065c400015d, 0x35096db4327049a412d267a352ec16a34751b8c126900004e54d267052441d46e3049a4000139000aa4005a5001e65b425fa3491e846c30352420d25b8352ee0d49b049a430d4bbc3526c166a4000584003414b499d2d25f, 0x55497d552475548dc0e690b12b2ec4ac7b12b0ec4a9b056041d0363054c40001398548dc18a90000504d525f05ea41d76e3062a400015d055a4000139a91b0c157100004d40051900276400ca9004944019a5051441b4363, 0x55c425525b95494c1571000052400319001505352674d497d352474d48dc00010b92aaee4a3bb928dc0e51055499d55237039a4000129000d76a4a4ba9291ea4a43a9286c0e510b12b2ec4ac3b12a6c1571800056555267, 0x69190c0c510c320ef0c81b0460c1512670660c00014504184000129000f84188b054499c19c30000514186100004a4003c10024d400b5d003f6401755007a94024d10552421525b85494e154bb85526c1571835496cd5253, 0x55497c0e6100004a400335a9192ea4647a9190ea461b001441a466369197c18b9055c99c0e6100004a418510000574003b5b1192ec4647b1190ec461b066ec1d766375d90c0c5100004e597247bb08dee461b031441a4663, 0x312412c2674b095e8c4bb051441d466303144000139000a959425fa1192e8c247a1190e8c237a1186c0c490624d8ccc25b624d0c167300004652c2674b097d2c2574b091d2c237000041a466369197ea46ab06144155267, 0x670400015106584000139000e958445f61112d8444305d04117267ba20ec197200005760825b82094c1772045c99c197200005764825b92094c1771045c99c19710000574002c900190400a31004264017b5008754029c5, 0x3208cc0a41069198d8444b69189c0e6a092096c0e690000524002b10014650d2676a097da825369110c0e41849919c19820740d8c19c20000504194180004e4003a532097cc825b32094cc82330398412c267066841d4663, 0x504114180004e628327045c800011944499d1125f8a096e282578a094d112378a08cc15a1075198c18a90000544156100004e6a4627055c400013145499d1525fa9112ea44434548dea441b029041a836332096da8327, 0x11820740d8c188a0]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k834 : region H43 0x8000010000100001000400010001000000000000000021100000090400940220 0x20 := regionTerm _ _ prog43k834 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k9 : region H43 0x8000010000100001000400010001000000000000000021100000090400940220 0x0 := regionFork _ _ _ 5 reg43k10 reg43k834
def prog43k1255 : Array Nat := #[0x670824825b9208cc19c1000052400319067042c464bb1186c19c3000056419c580004c4004210670824835b920ccc19c30930d6c19c580004c4002a10670600014906712000119001a4400fb50092940445501774408145, 0x33096ccc223049a400011969198c0d4086a0d8cc825b061a824825b061a4000149000a6418b34000484005b1049a61a8363061ac24c35b061a6000149062cd000131000e841893400046400611003d9419c2032096cc8233, 0x6524000149000a6419b24000484005b1049261264670658924c35b06526000149066c9000131000e841992400046400611003cd4019610618224c35b060c2000149062c200013106242000119c89aaf226a3c89a4c0d608, 0xc092cf0249b0352824825b035240001494b506c166a40004852d2330358924c35b03526000149059a90001316a4c8c126a4000464005114b459c0c48833096ccc223049240001194b099c0940849919cc825b0652824825b, 0x55241c9163054820001394d48cc18a900004940044905522189163aa592c1592472458c159080004e4002b1062b200012500164400c19004394015350650224825b06482000149066c200012106642000111c092ef024b7, 0x31540106100524401ca5048c20d516306242000119a89aaea26a7a89a8ea2693048c20d516306242000119c8aaaf22aa7c8aa8f22a93054820d525b3548ccd52230564600011135458cd5127055c225525b9548ce55223, 0xc0a8cf02a1b056821151674544dc14508000486a2a4ba8a86c14508950d6e54333950c8c1469853459c143080004a5b4323066860001350011241468843459e8d44b0524d14d16705242000129000a8419a480004d400599, 0xa8a92ea2a130488209416706642000111000b56824bba092de824b3a0926c1420835058cd425b3508ccd4223051c225425b9508ce5422306284000149000e649416725055c94137029022a2a4b06642000155c0a8ef02a37, 0x8a4d6e293230622822835b062d1000121000a9411708b4512ed1413045281c91630450200013906228000125000f64168a472458c168880004e418b44000494003a100246400e31004b9401735006f54024d105502135167, 0xac400499a8a2aeb1127a8a28ea289305982191163062c2000131889aae226a7889a8e2269305982191163062c2000131c8a2af228a7c8a28f228930450219144b64506d9141305a2c00012164458d91127045220c9163, 0x8d0c8c1170844459e9144b052511d416304a2200013954459c16a0875058c128880004e4002a9001684007998d055e91137a0a2ce34127a0a24c1530835458e3535b8d4ccc1160864458eb164b062a22558db06222000149, 0x1450835058e3435b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k1255 : region H43 0x8000010000100000000400010001000000000000000021000000090400940228 0x8 := regionTerm _ _ prog43k1255 adj43 _ _ 28 (by decide +kernel)
def prog43k1610 : Array Nat := #[0x23459e0d25b8348cc1983083096c19b400004c4002b5041422d064bb4186c106b053459c198300004d4106080004a4003d905a0d14d167066d000013505a02000129000ec40091100391401261005a8401ea500975403251, 0x80926c1040864058d9044b64106d90413041c22d044bb4106ed041306208000159000ec51016744051d101370288222285b066c2000145c0a0ef02837c0a0cf0281b046020911672444dc105080004462285b88a0cc10688, 0x4142190163ac192c1594074058c16a880004e55516704a021d016304a02000139000aa4005b1001e46b01478544deb0127a8a08ea281b0448213116788a16e2282305902110167066c2000121000b16024bb8092de024b3, 0x1420825059e1425b85088c1040844059e9044b0668225485b06602000149000a840049185055e90147a0a0ee90137a0a0ce8281b055c209516785496e15233]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k1610 : region H43 0x8000010000100000000400010001000000000000000021100000090400940228 0x100000000000000008 := regionTerm _ _ prog43k1610 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k1254 : region H43 0x8000010000100000000400010001000000000000000021100000090400940228 0x8 := regionFork _ _ _ 68 reg43k1255 reg43k1610
def prog43k1729 : Array Nat := #[0x5d0219716365c54d9744b05e421d716375c54c179080004e40033145c59d17157049422e2a3bb8a8cc18bc855c59d5715700242302bbbc0aecc1790800058400329001544007210037140161900850402d1100f0d4048a5, 0xb8a2cee28ab05e4615716705d8224c35b05cc200014905ec2000131000ea400545001c84d716335c55cd715304a222e2a3b8d055c1570895636c1670800055411708000525d716304a22000139001546e28b3b8a2aee28a3, 0x25c59c9715725c54c97147000022e28ab88a16e2285788a14c12808b8aaae151530514225485b059420001510414200014955c59c128080004a400555001d16e283bb8a0cee2823b8a06c1791845c59d17147ba0ccc17b08, 0x1465b71636dc54db7143b89aaee26a3b89a4c1720835c58cd725b35c50cd723335c88c1791065c58d97143bb088c17b08b8a0eee282305e441d716305d0224825b05c8200014905ec2000121000ee400541001cc400999, 0x5ec200015105e02000149b8a08c17908000504005114dc59d371574dc51ee24bbba44dee24b3b8926c17608930d6c173080005259714705ec200013135c55c17a8895636c17b0800055417888000526e28b305e42000145, 0x5d0224825b05c8200014945c50c17b080004849715305e8225485b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k1729 : region H43 0x8000010000100001000400010001000000000000000021100000090400940228 0x1000000000000000000000000000000000000000000000008 := regionTerm _ _ prog43k1729 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k1253 : region H43 0x8000010000100001000400010001000000000000000021100000090400940228 0x8 := regionFork _ _ _ 192 reg43k1254 reg43k1729
private theorem reg43k8 : region H43 0x8000010000100001000400010001000000000000000021100000090400940228 0x0 := regionFork _ _ _ 3 reg43k9 reg43k1253
def prog43k1900 : Array Nat := #[0x1aa28d9cba3671e8d9bb04e4a1d36e3049aa0001396cd57e6d54704e511d36e374db7c128b40004e400329001b441372894e36e538d794e34c1172800052412728000514004b50037040182500a4c403b2101566407791, 0x54d31c138248ce16e3385304a0900014504a290001410010a4006b9002b5400db50020a2909cba4271e909bba426dc10734ac272eb09c7ac26ac169b49b60ee706ab041ca2d09cbb4271c1372800056400335001554007d1, 0x9b22ac12628c326ef0c9b704e4a000161000d140055d001f4400ac1003894126a46cd37e6d4c79a5b0e6d4bb9a5aac00724aa672ea99c7aa670ea99ab04e4e1534e7049c900012974d37e6e4c79a5d0c1394054d39d534df, 0x4e4e000131000b940065500237400bc10042d401645031491934df9a592e6c4c79a590e6c4bb9b12dc1062884d94e7064b9c191e6c83b9b20dc00628a3272e8c9c7a326ee8c9b704a2c2ec9bbbb26deec9ab0627127164b, 0x4c5b345f9b512e6d4439a1aae686a704e081334674cd17c10520000496134579c112e6883b9a20cc00920ba26eee89b3ba26aee89a7039882a89cbaa26aea89a70398819344b049c8000131ca26af289a704dcc19344b, 0x4a262e69bbb9a6dee69ab001463069bbc1a6dc13518000586c69cbb1a71c189a80005640055d001f5400a41003544010a5005ac401b21045c82334579c512e714439c50de688b39a22ae688a704d881b36636cd94c0e6a0, 0x64cd7d9335399992e666479b0d0e6c3270666625335b94cd4c0a4980005253335f4ccd5e664c79a4d0e664bb9992dc00518a1a72e869c7a1a70e869bba1a6dc1351884cd6e1335799a0ee66837039a62a69cba9a71ea69ab, 0x54c91c1331074cd8dd334304cc400013904dc40001190010a40062500216400d5d004144013d5005ed402031009c841999874cd8dd33530290600013944cd7d1335799912e664479a0d0e664379a0cce6832704d46193363, 0x1c42a49cba9271ea49c3a926aea49a7a9266c0a490a1272e849c7a1270e849bba1266c16990b926eee49abb9269ee499b001c43249abc9269c13710000596c49cbb1271ec49c3b1266c137184cc99d3324704dc6153267, 0x9a08de6823399106c1899054c99d532570398400012964c97d9325399192e6c24799190e6c23799189e6461b04cc41b336334c96cd32570626425325b94c95c0e690000524003196cc97db32539b491e646c3991aae646a7, 0x1371044c99d1325f44c95e6444b9a091e64443]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k1900 : region H43 0x8000010000100001000400010001000100000000000021100000090400940220 0x100000000000000000000000000000000 := regionTerm _ _ prog43k1900 adj43 _ _ 28 (by decide +kernel)
def prog43k2227 : Array Nat := #[0x2423229abc8a68c13908000597029bbc0a6df029b3c0a66c1391844c59d1313704e4615316754c4dc1330894cd6e5333304cc200014904e420001190010a40062100218400d55004144013dd005f140201100af0403525, 0x34c57e3335b05a621d316374c57c128880004e4003198cc55e331539c44de628b398a2ae628a3002422e29bbb8a6dee29b3b8a6aee29a3b8a66c0a408a0a72e829bba0a6de829b3a0a66c18988a8a72ea29aba8a68ea299b, 0x84c55e131539c051e6283b9c04de6283398a08e6281b04c820d316334c96cd323334c88c1320864c58e6464b9b088c1370894c96e5322306264000149000cc40059924c59c9315f24c55c9315324c51c9313704cc20d3163, 0x4d022829cba0a64c1320894c96e5322304c8200014904e42000111001145331674cc57d331579a451e691439892ee691379892ce6249b04c8209316724c57e1325b05a6215316754c57c128080004a400311]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k2227 : region H43 0x8000010000100001000400010001000100000000000021100000090400940228 0x100000000000000000000000000000008 := regionTerm _ _ prog43k2227 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k1899 : region H43 0x8000010000100001000400010001000100000000000021100000090400940228 0x100000000000000000000000000000000 := regionFork _ _ _ 3 reg43k1900 reg43k2227
private theorem reg43k7 : region H43 0x8000010000100001000400010001000100000000000021100000090400940228 0x0 := regionFork _ _ _ 128 reg43k8 reg43k1899
def prog43k2355 : Array Nat := #[0x1aa20d7db835f5e0d7bb059ea1cf6e3059aa0001396bd57ded55704a2f1cf6e373db7c16ab40004e400329001b040f728b3eb2ecfac7b3eb0c1572800056416728000554004b50037440182500a46403b110156c4077a1, 0x53d35c147a4851f6e147d7049e900014105aa90001510010a4006b9002b1400db5051ea2147db851f5e147bb851edc147348d1f6e347d78d1eac127b4a35eedf46ab051ca2547db951f5c0f72800052400335001514007c1, 0xa99eac16518c19eef067b7059ea000161000d540055d001f0400ad1003894166a46bd37ded4d77a5b4ded4bb7a5aac007248a5f6e297d78a5f4e297ab059ee14f4e7059c900012973d37dee4d77a5d4c1283c53d39d4f4df, 0x59ee000119000b940064500237400bd10042d4016550292612f35f7a4d6de93577a4d4de64bb7992dc145187d0d6df4357a3cd0e867bba19edc00518819f6e067d7819eee067b705aa62e67bbb99edee67ab062af1f535b, 0x465af25f7b496ded253791aade46a7051e412f2674bc97c14510000495f425ba3c91e847bba11e6c16790b91eeee47abb91e9ee479b038c42247db891eae247a7038c40cf25b059c4000119c91eaf247a703dc60cf25b, 0x49ec2ec7bbbb1edeec7ab0018a30c7bbc31edc0f6280005864c7db931f5c187a80005240055d001f1400a51003504010a5005a6401b11055c41f525b7d494eaf2477d48dea47aba91e9ea479b03cc41af3636bcd0c0e690, 0x63cd7dec35b7b0d5dec35363cd0dec327065ec2cf64bb3d90c0c5240005658f4df7b135de965363d31dec4bb7b12dc00628831f6e0c7d7831f4e0c7bb831edc0f628a3d92e8f647a31eee8c7b7039ac22c7db8b1f5e2c7ab, 0x53d15c0f62073d98dcf65303d8800013903dc80001310010a40062500212400d5d004104013c5005ed402019009c44197b073d98dcf6430314400013963c97dec25b7b095dec25363c91dec23779189de461b03d8a18f363, 0x1c82287db8a1f5e287d38a1ece287ab8a1e9c0a4a0821f6e087d7821f4e087bb821ecc127a0ba1eeee87b3ba1eaee87a7001c83287abca1e9c0f720000596487db921f5e487d3921ecc0f7304bd19d2f45703dcc14f467, 0x7a08dde823379106c187a053d19d4f4470390600012943cd7de835b7a0d5de835343cd0de64377a0ccde832703d881af66363d12d8f447061e82cf44bb3d11c0e6a0000564003316bd17ded4577a1b4daf4437a1aade86a7, 0xf72043c99d0f25f7a096de82577a094d0f247]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k2355 : region H43 0x8000010000100001000400010001000000000000000021110000090400940220 0x10000000000000000 := regionTerm _ _ prog43k2355 adj43 _ _ 28 (by decide +kernel)
def prog43k2682 : Array Nat := #[0x49e23227abc89e4c16788000597027bbc09edf027b3c09e6c167b023c59c8f137049e614f16753c4dc0f608b3d92ecf61b03d82000159059e20001310010a40061100218400d45004104013dd005f540202100af4403525, 0x63c57eaf64b049e21cf16373c57c127880004e400331abc51eaf1437d44dea27aba89e6ea2793059e22e27bbb89edee27b3b89eaee279bb89e4c0a208809f6e027bb809ede027b3809e6c18788889f6e227b3889eae22793, 0x7d055e8f147a3c50e827bba3c4de827b3a09e6e8279303d0218f16363d12d8f41b63d04c0f40833c58de835b79904c0f708b3d12ecf413061e8000159000c64005b143c59d0f15f43c55d0f14743c50d0f13703d8218f163, 0x3c822027db809e8c0f408b3d12ecf41303d02000159059e20001210011052f1674bc57de91577a454d2f1477892ede91377892cde249b03d0210f16743c57e8f44b049e214f16753c57c127880004a400321]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k2682 : region H43 0x8000010000100001000400010001000000000000000021110000090400940228 0x10000000000000008 := regionTerm _ _ prog43k2682 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k2354 : region H43 0x8000010000100001000400010001000000000000000021110000090400940228 0x10000000000000000 := regionFork _ _ _ 3 reg43k2355 reg43k2682
def prog43k2808 : Array Nat := #[0x84df5e137d384deee137b7001ea28f9cba3e71e8f9bba3e6dc127a87cd55e6f5479a9eee6f53704dcd2337db8cdf5c1373494df6e537d703dcd000149000d140052900214400b41003a940143100648401e9900924402b09, 0x9bcc8c007a07cd15e6f44b9bd11e6f4439a1eee6f4379a1ece687ab9a1e9c007b07cd94e6f64b9bd91e6f6439b1eee6c7b79b1eae6f62704de92137db84df4c127a4000505f34d79bd31e6f4bb9bd2de697ab04dea2137db, 0x9bc51e6f143989eee6f137989ece627ab9bc49e627a3989e6e6279304de41f325b7cc95df32539bc91e647bb9bc8de6f233991eae647a79bc88e6479b04de61f335b7ccd5df33539bcd0e667bb999ede6f333999eae6f327, 0x127887cc55df3153]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k2808 : region H43 0x8000010000100001000400010001000100000000000021110000090400940228 0x100000000000000010000000000000000 := regionTerm _ _ prog43k2808 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k2353 : region H43 0x8000010000100001000400010001000100000000000021110000090400940228 0x10000000000000000 := regionFork _ _ _ 128 reg43k2354 reg43k2808
private theorem reg43k6 : region H43 0x8000010000100001000400010001000100000000000021110000090400940228 0x0 := regionFork _ _ _ 64 reg43k7 reg43k2353
def prog43k2910 : Array Nat := #[0x64572c165a86a978c0e5a892e36c188a8000524002b55c557e2b557039ab24b8db92e35c18bc4000524003290020c4125a8c2eeef0bbb7c2eecc1792800058418928000574004c5003d44019a100aa6403c89015d0407925, 0x65177c0e5a00004c418ba000054400429001b2400ab5003714145a865178d945df65172d945c7052511b45e36d177db45ab045cb2915cb8d16ac1492875178dd45df0496a000139000d1400535001ec4115a864578d915df, 0xb1971c185a80005640035d001554007b1002b4400e210622817145f8ad15e285d35c512e285ab049681a85e36a177da85d36a16ac1892c52d19c189200004a57245f92d15e485d30398b14b46752d17d4b457051681945e3, 0x18d4008d5002f44010c50059740a4185a0d8d6835f42cd5d6835359912d66447051461743635d0d7e865cba1971e8b333001461865e361977d865cb61971c18b98a9972ea65c7a996ac17b2c5dcd8ee65ab061462c65cb, 0x8ac54e225ab88968c1458842c59d0b157051420001215d058e825cba2c4de8259b061622a25cba896aea25a3a8966c1230868978da25ab68968c1230832c58c18908000467225abc8968c1259832c58c1892c000464002e5, 0xac16ac105a8b4172ed05c70396a00015974178dd05df0596a000139001554007b500294400d3100428401699006c24179085dc58d771535dc51eeb137b896aee25a3b8966c0b3088acd6e2b33304a220001195c458e2b157, 0x82cd4e0b33382cc8c1982cc2e0ef0b833041480001615c117e0b45782174d7044b5c111e0b4370416a1905e364177d905d364172d905c70416a2905cba4171e8b83ba2e0dc128c06c178db05df6c16ac1072cac172eb05c7, 0x92e14c105a4000524125a4000504004290018840083900355401031004ed4017c5008064027090660b24b85b92e0cc10508000525701635c057e0b15782c54d7014782c4de025a380966c105a85c0d8d7035f82cd6e0b357, 0x6a574da95c36a56ada95a3029281895e362577d895d362572d895c3039692a95cbaa570ea95abaa568c125a4ca56af295a30496900016572578dc95df72574dc95c304a0b12b4674ad17c1282c52d39d4b4df0016924b85b, 0x596914b4e752d2dc124980004a5693635a4d7d2b3575a4d4d664c75a4d0d2b3335a4c8c005a48ae16e0b4bb82d2dc165a4c2d2ef0b4b705969000161000d05714df8ad35e295d38ad2ce295ab8a568c125a46a578da95df, 0x496912b1675a458d6915f4ac55d691535a451d691434ac4dd6249b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k2910 : region H43 0x8000010000100001000400010001000000000000000021100000090500940208 0x100000000 := regionTerm _ _ prog43k2910 adj43 _ _ 28 (by decide +kernel)
def prog43k3240 : Array Nat := #[0x39643245abc9162c18590000596c45cbb1171ec45c3b1166c1882c22c59c8b1470396614b26752c91c00590c2e0ef0b81b04164000161061640001410010a40060900216400d350040c4013d5005f740202500af4403521, 0x82c96e0b2570396424b25b92c95c0e590000524003415dc91eeb237bac8cee45abb9166ee458b061642a45cba9171ea45c3a916aea459ba9162c0a20861178d845cb61171d845c361166c1659069178da45c36916ada458b, 0x5d097e845cba2c91e845c3a2c8de8b233a1166e8458b02d2420b25b82d2ee0b49b82d22c0b4905a4d8ccb25b59922c12590c2d2ef0b48b05969000161000c64005c14ac99d2b25f4ac95d2b2474ac8dd2b233001642eb83b, 0x2c821845e361169c0b410c2d2ef0b48b02d24000161061640001250010c50b2675a097d0b2575a094d6444b5a091d6444342c8dd6441b02d2412b2674ac95e8b4bb0396414b26752c95c0e5900004a400325]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k3240 : region H43 0x8000010000100001000400010001000000000000000021100000090500940228 0x100000020 := regionTerm _ _ prog43k3240 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k2909 : region H43 0x8000010000100001000400010001000000000000000021100000090500940228 0x100000000 := regionFork _ _ _ 5 reg43k2910 reg43k3240
def prog43k3366 : Array Nat := #[0x64d77d935d364d72d935c70016a28b9cba2e71e8b9bba2e6dc0e5a85cd57e6a5cb9ad51e6b53704e511b35e36cd77c1394474d78dd35df04a2b000139000cd40052900214400b31003a840144100649401e9900922402b11, 0x9acc8c005a45cd37e695cb9ad31e695c39ad2ee6b4b79ad2ce695ab9a568c0082c84d74e705cb9c171e6b83b9ae0de6b8339c16ae705a304d681935e364d74c0e5a00004c57345f9ad12e6b4479ad0de685ab04d6a1935e3, 0x99172e6b24799170e6b2379ac8ce645ab99169e6b22399166e6458b04d621731635cc57d7315398972e6b1479ac50e6b1379896ae6b12798968e6259b04d661733635ccd7d7335399972e665c79acd0e6b3339996ae6b327, 0xe5905cc97d73253]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k3366 : region H43 0x8000010000100001000400010001000100000000000021100000090500940228 0x100000000000000000000000100000000 := regionTerm _ _ prog43k3366 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k2908 : region H43 0x8000010000100001000400010001000100000000000021100000090500940228 0x100000000 := regionFork _ _ _ 128 reg43k2909 reg43k3366
def prog43k3465 : Array Nat := #[0x82dedc127a873d78c165a80004e56f55f7ad55d6f5477ad4dc128bc6bd78daf5df001cb22b7db8adf5c127ac73d78dcf5df049eb000139000d1400535001ca400bc1003ac401251005a9401ba10084640271100b624034cd, 0x5bd11d6f4437ad0dde85ab7a169c165a45bd37deb4d77a574d6f4c77ad2edeb4b77ad2cde95ab001eb28f5cba3d71e8f5c3a2deee8b7b7a2decdf45ab03d6a18f5e363d77d8f5cb63d71d8f5c30016a20b7db82df5e0b7bb, 0x7ac49de25a378966de25930396416f25f7ac96deb2577ac94d6f2477ac8ddeb2337916ade45a77ac88de459b03d6616f3635bcd7deb35b7acd5deb3535bcd0deb3337996adeb3277acc8c187a05bd17deb4577a174d6f44b, 0x7ac7cd74e6f5cb9bd71e6f5c39adeee6b7b79adece6f5ab9bd69e6f5a39bd66e6f5939bd62c127885bc58d6f15f7ac55deb1535bc51d6f1437ac4dde25ab]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k3465 : region H43 0x8000010000100001000400010001000100000000000021110000090500940228 0x10000000100000000 := regionTerm _ _ prog43k3465 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k2907 : region H43 0x8000010000100001000400010001000100000000000021110000090500940228 0x100000000 := regionFork _ _ _ 64 reg43k2908 reg43k3465
private theorem reg43k5 : region H43 0x8000010000100001000400010001000100000000000021110000090500940228 0x0 := regionFork _ _ _ 32 reg43k6 reg43k2907
def prog43k3588 : Array Nat := #[0x354b6c125146a8b8c18aa8954b6c0e514000524002b5554b7ea5547039a52c5acbb16b1c18bd40005640032900206416514c16eef05bb7c16e6c17b2800058418b28000574004d5003d040199100b0c403e0901634407aa5, 0x340b7c0e29000046418b9000050400429001b6400c35003d5410514340b8cd02df340b6cd02d705ab01b02e36c0b7db02ab055c52152dbac0aac16828740b8dd02df05945000139000d5400535001e6415514354b8cd52df, 0xd7400545001e6400ac100384418a902d497cb525ba9491ea42c3a90aac16290690b8da42df690b0da42ab059440d62e3059c5145267062c4000129000a64b625fb1491ec42c3038c514526751497d45247040a40d02e3, 0x43540165d031441842e361497cac25b2b095d85247610b0c10628640b8d902df830b6e0c2d781586c0c514330b8ccc2df330b6ccc2d7062ec22c2db8b0b5e2c2ab05e451972e3bb0aac18628930b6e4c2d706145000149, 0x40a208516721451c10508000444b0163808b6e05137808acc18288888b6e222b3888aae22293059821a22e3688aada229305982185163062c2000131c88aaf2229305985185163062c5000131000b940063500231400bc1, 0x950b5c0e514000525d42e3750b7c125140004e400545001ed400a4100346401091005ac401b0905ec20b71632dc55cb7143b944dee22b3b88aaee2293054a20d52db354acc12288000464b5163a9451ea5143a88aaea2293, 0x6685305a3bc1686c14510000584b425f2d096cb4257a1491e842c3a148dc14514350b8cd42df350b6cd42d7350b0c14514850b6e142d7a160ee8583705ab41b42e36d0b7db42ab051c52342db8d0b5e342ab051452542db, 0x59250001510010a4006110020e400d45004064013b5005f5402031009c2419a14b1692ec5a1b051420001592d058cb415f2d055e85147a1450e85137a08ace82293051451942e3650b7e8564ba1591e8c2c3a1586e8c293, 0x6a4a4c0a490324b8cc92df324b6cc92d3324b0c0e4948a4b6e292d38a4aae29293049253292abca4a4c16494000595c92e3724b7dc92d3724b0c16a1449499d2525f04a051454e751537c00494b1692ec5a4305125000159, 0x4925000129624b8d892df4b0b5d892d361531d892c361526d89293001252a5a4ba152ee854b7049253054bbc152dc12494000584003514d4b7ea54c7aa4b0ea92aba9526ea9293059251a92e36a4b7da92d36a4b0da92ab, 0x1649449459ca916349457d251572a454d251472a450d25137488acc1249451539d454b7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k3588 : region H43 0x8000010000100001000400010001000000000000000021100000090400900328 0x100 := regionTerm _ _ prog43k3588 adj43 _ _ 28 (by decide +kernel)
def prog43k3921 : Array Nat := #[0x39053282abca0a2c18414000596482db920b5e482d3920acc18a1441459d051570398514546751515c00414c168ef05a3305105000161061050001510010a40060900212400d35004064013c5005f740202500af0403511, 0xa1512e85447039052c544bb1511c0e4140005640035145cb5ee5437ba0acee82abb9506ee828b061052282db8a0b5e282d38a0ace282ab8a0a2c0a408320b8cc82db320b5cc82d3320acc124146a0b8da82d36a0aada828b, 0x440b7e082db820b5e082d38150de082b381506e0828b0000528544ba152ee854b3a1522c00494624b8d8544b4b0a2c12414c152ef0548b04925000161000cc4005d149519d2545f49515d254474950dd2541b001052e5a3b, 0x20a20c82e3320a9c08290c152ef0548b02505000161061050001250010650526741497ca825b41495ca825341491d042c34148dca82330010512546749511e054bb0390514546751511c0e4140004a400325]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k3921 : region H43 0x8000010000100001000400010001000000000000000021100000090400940328 0x40100 := regionTerm _ _ prog43k3921 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k3587 : region H43 0x8000010000100001000400010001000000000000000021100000090400940328 0x100 := regionFork _ _ _ 18 reg43k3588 reg43k3921
def prog43k4047 : Array Nat := #[0x33cb7ccf2db33cb5ccf2c3001452057db815f5e057bb815edc0e51453cb7dea2db7a8b5de553705aaf1af2e36bcb7c16abc73cb8dcf2df05aa5000139000cd40052900210400b19003a440145100649401eb100922402b21, 0x7b0a4c004944bcb7de92db7a4b5de92d37952ede54b77a4aade549b7a4a4c147947d0b6df42d7a3cb0e857bba15eddf42aba15e6e8f29303ca40cf2e333cb0c0e290000464af25f79496de52577948dde42ab03d450cf2e3, 0x7a0b5de82d343cb0de54377a0acde82ab7a0a9de541b7a0a4de828b03ca20af1632bc57de22db79455de51532bc50de5137788acde22ab79449de229303d8518f2e363cb7dec2db7b0b5dec2d363cb0dec2ab7b0a9de561b, 0xe41443cb7de82db]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k4047 : region H43 0x8000010000100001000400010001000000000000000021110000090400940328 0x10000000000000100 := regionTerm _ _ prog43k4047 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k3586 : region H43 0x8000010000100001000400010001000000000000000021110000090400940328 0x100 := regionFork _ _ _ 64 reg43k3587 reg43k4047
def prog43k4146 : Array Nat := #[0x32cb6ccb2d732cacc0051461578d855df61572d855c70494516a2e35a8b7d4b2d759551c18bac8acb6e2b2d7062eb24b2db92cb5c18b94000524003450014a400831002c6400e8900514401921007b040249100ac940323d, 0x1051682e35a0b7d0b2d75a0b4d6544b59511d682ab59506d6828b051651742e35d0b7e855cba1571e8b2b35d0aae8559ba2ca2c0b28832cb6ccb2b3048a200011959458d6515f2ac55d65147588aac0b51432cb8ccb2df, 0x5a4b4d654c75a4b0d2b2b35a4aad692a359526d692935a4a2c0b290590b8d6525f2ac96cab25759494d65247590b0cab233590aad65223590a2c105945c0b8d702df82cb6e0b2d782cb4e0b2b35c0aae0b2a381566e0b28b, 0x3d6516f2e35bcb7deb2db7acb5deb2d35bcb0deb2b37acaadeb2a77aca8de559b7aca4deb28b049251692e35a4b7d2b2d7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k4146 : region H43 0x8000010000100001000400010001000000000000000021110000090500940328 0x100000100 := regionTerm _ _ prog43k4146 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k3585 : region H43 0x8000010000100001000400010001000000000000000021110000090500940328 0x100 := regionFork _ _ _ 32 reg43k3586 reg43k4146
def prog43k4260 : Array Nat := #[0xa1672e859c7a166ee859b705a6a1d32e30494500013954cb7d532d799551e6553705ab31b32e36ccb7c137148ccb6e332d7049c5000145000cd40052900274400cc10042c40152500688401f9900944402b8900caf403a2d, 0x99512e654479a0b0e654379a0ace682ab9a0a9c124944ccb7d332d799531e692c39952ee654b79a4ace692ab04d851932e364cb7d932d399592e656479b0b0e6c2ab04e052132db84cb5e132d39960ee658379c0aac00514, 0x99450e65137988ace622ab99449e622a3988a4c189902cc97cb325b2cc95cb325399491e642c39948de65233990aae642a799488c1351434cb8cd32df34cb6cd32d734cb4cd32c334caccd32a734ca8c0e41444cb7d132d7, 0x5ccb4e655cb99571e6b2c39acafe6b2b39acaae6b2a79aca8e6559b9aca4e6b28b04de51f32db7ccb5df32d39bcb0e657bb995ede6f2b39bcaae6f2a79bca8e6579b9bca4e6f28b05a620b31632cc57cb31572cc54e65147, 0x135945ccb8d732df]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k4260 : region H43 0x8000010000100001000400010001000100000000000021110000090500940328 0x100000000000000000000000000000100 := regionTerm _ _ prog43k4260 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k3584 : region H43 0x8000010000100001000400010001000100000000000021110000090500940328 0x100 := regionFork _ _ _ 128 reg43k3585 reg43k4260
private theorem reg43k4 : region H43 0x8000010000100001000400010001000100000000000021110000090500940328 0x0 := regionFork _ _ _ 8 reg43k5 reg43k3584
def prog43k4396 : Array Nat := #[0x440f2c1671c4b8f9c0e51c91e16c19838000524002a5740f7e077530292724785b91e14c19bc0000524003390020841271cc9eeaf27ba7c9ee8c1793800059419938000574004c1003d54019b100b04403e0901631407ab5, 0x454f7c0c51c00048419bb000055400439001b2400c25003d041571c454f9d153df454f2d153c3056501353e74d4f7d353bb041472b03cb854eec15938554f9d553df049c7000129000d0400525001e841071c440f9d103df, 0xd7400551001e8400ad50038c419830640f7e0c3d781d94d903cb830eec1261c4b0f9d2c3df4b0f5d2c3bb062471123e7049471c76630664c000139000a85923df930f5e47653029071c766371d97dc7653055871153e7, 0x43040165d039840ec26761c97cec25761c94d843cb610f0c157103d499cf525fa90f2ea43c3a9c88c0e390410f9d043df410f2d043c3066e42843cba10f0e843bb05ec70f7267b90eec19710b10f2ec43c3065c7000159, 0x54e218716361c54c157080004c4f5167a88f2ea7127a88e4c19388a08f2e823bba08ece82393048821223e7488eed223b30488208716706642000111c08eef023b3048e408716706647000111000b840062500234400bd5, 0xb44f0c0e51c000565513e7544f7c1671c0004a400551001e9400a55003484010b1005a4401b0905e420f71673dc55cf7143b88eeee23b3b9c49ee239301c8220725b81c88c12808000444f016781c55e07153808eee023b3, 0x62273278abc9e28c1889c000595913df8b0f5e27653644f2d913c389d89c1171c444f9d113df444f5d113cb444f0c1171cac4f2eb13c3a9e2aea78a704a301313e74c4f7d313bb045472913cba44f0e913bb045c72d13cb, 0x49a70001450010e4006310020a400d51004084013a5005f0402011009c241889c91e36e478a3045c20001493c459cf115f89c55e271533c450e223b389c49e22393045c70f12673c497e2725b89c95e2725389c8ce27223, 0x4b4ecc0e6b0434f9d0d3df434f5d0d3cb434f1c0d51ca34f2e8d3c7a34eee8d3b3049a730d3bbc34ecc1251c0005854d3e7534f7d4d3d7534f1c1289c69d98da765f04a271c76e371db7c0069c91e36e478d7045a7000149, 0x49a40001393b499da725f3b495da72533b491da43c33b48cda7223001a722785b89daae276a7059a73276abc9da9c1669c000594003456c0f7e0d3d781db4e0d3bb834ece076a3049a712d3e74b4f7d2d3d74b4f1d2d3bb, 0x1269c3b459da716369c57ced15769c54ced14769c50da7127688e4c1669c71db8dc76a7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k4396 : region H43 0x8000010000100001000400010001000000000000000021100000090400950028 0x10000 := regionTerm _ _ prog43k4396 adj43 _ _ 28 (by decide +kernel)
def prog43k4729 : Array Nat := #[0x28e63063bbc18e2c19398000586c63cbb18f1ec63c3b18e4c1989c31c58cc7143028e41c736371cd0c00398c9e2af27893044e6000165064e60001450010e40060900216400d25004084013d1005f740203500af5403531, 0x89cd6e27353028e624735b91cd4c0a398000524003453dcd0ee63bbb9cc9ee7323b98e4ee638b064e62863cba18f1e863c3a18eee86393a18e2c0e308418f9d063cb418f1d063c3418e4c16398498f9d263c7498eed2638b, 0x3d4d7ea63cba98f1ea7343a9cc9ea7323a98e4ea638b000e622735b89daae2769389da2c0a3903b499cc725b690e2c12398c9daaf2768b059a7000165000c44005c569cd8da735f69cd4da734369cc9da7323000e62e78ab, 0x1cc21063e7418edc00398c9daaf2768b034e6000165064e60001350010858736361cd7cec35761cd4d863cb618f1d8734361cc9d86393000e61a7363a9daada7353028e61c736371cd4c0a3980004e400335]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k4729 : region H43 0x8000010000100001000400010001000000000000000021100000090400950228 0x10200 := regionTerm _ _ prog43k4729 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k4395 : region H43 0x8000010000100001000400010001000000000000000021100000090400950228 0x10000 := regionFork _ _ _ 9 reg43k4396 reg43k4729
def prog43k4855 : Array Nat := #[0x44cf7d133d744cf2d133c3001c72a79cba9e70ea79aba9e69c0e51c74cf7e6e3cb9b8f0e6772704e501333e74ccf7c1394054cf9d533df04a07000129000c940053900215400b21003ac4014450064d401e9100922402b19, 0x99c88c0069c6ccf7e6d3cb9b4f1e6d3c39b4eee6d3b399daae676a799da8c0089c8ccf5e713cb9c4f0e713bb9c4ece678ab99e29e678a304d871133e744cf5c0c51c000485933df9b0f2e6c3c39b0eee6762704dc71133e7, 0x998f2e663c799cd0e663bb998ede6733399cc9e67323998e4e6638b04ce20f31673cc57cf3157988f2e6714799c50e623bb99c4de623b399c49e6239304ce40f32673cc97cf3257990f2e67247990f0e643bb99c8de67233, 0xa3983ccd7cf3357]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k4855 : region H43 0x8000010000100001000400010001000100000000000021100000090400950228 0x100000000000000000000000000010000 := regionTerm _ _ prog43k4855 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k4394 : region H43 0x8000010000100001000400010001000100000000000021100000090400950228 0x10000 := regionFork _ _ _ 128 reg43k4395 reg43k4855
def prog43k4954 : Array Nat := #[0x514f5d453c7514edc00394a14f2e853c7a14eee853b7060e50f52dfa94f2ea53c7058e51a72e369cb7c1639471cb8dc72df058e5000139000cd400555001f4400aa90039040122500588401ab10086640271100bc24037cd, 0x61cb7cec2d761cb4d853cb614f1d872c361ca9c0e394414f9d053df414f5d053cb414f1d053c3414edc12814494f9d253df494f5d253c7494eed253b7028e50f02df81cb6e072d781cb4e053bb814edc12714514f9d453df, 0x388a4c0729031cb8cc72a7038e500011939499ce525f29c96ce525729c94ce5247390b0ce52373948cca7223028e50c72e331cb7cc72db31cb5cc72d331cb0cc72b331ca9cc72a3000e51053e7414edc0a394000485872e3, 0xe50f32df3ccb5e653cb994f1e672c3994eee653b799cace672ab99ca9e672a3994e6e6729399ca2c0728831cb6cc72a3048e500011939459ca716339457ce515729c54ce514739450ce5137388acca7127]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k4954 : region H43 0x8000010000100001000400010001000100000000000021100000090400950328 0x10100 := regionTerm _ _ prog43k4954 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k4393 : region H43 0x8000010000100001000400010001000100000000000021100000090400950328 0x10000 := regionFork _ _ _ 8 reg43k4394 reg43k4954
def prog43k5080 : Array Nat := #[0x49ee14f3e7059c700012973cf7de775373cf0de772704a0f12f3e74bcf7c0051c81df6e077d3049e714f3e753cf7c1279c0004a40034100149400739002f1400ea1004954016b5006ec402111009c6402d8900d33403c15, 0x63cf0dec3bb7b0edde7627059a71af3df7b4f5de76d36bcf0ded3bb79daade76a779da8c0079cabcf2eaf3c7abcf0df53bba9deaea77a7a9de8c0f71c43cf9d0f3df43cf2d0f3c743cf0c0071c89df6e277d389deae277a7, 0x79c49de239b788e4c0a3983bcd7de735b79cd5de73533bcd0de63bb798edde733379cc9de7323798e4c0f3903bc99cef25f79c96de725779c94cef247790eede723779c8cde7223065ec18f3df7b0f5de765363cf2d8f3c7, 0x794edde72b379caade72a779ca8de539b79ca4de728b001e71f33d79bcf2e6f3c79bcf0e6f3bb9bcede6f3b399deae677a799de8e6f39b9bce4e6f38b049e20ef1673bc57de715779c54cef1473bc50de23bb79c4dde23b3, 0xe50ef2df79cb6de72d779cb4de72cf3bcb0de53bb]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k5080 : region H43 0x8000010000100001000400010001000100000000000021110000090400950328 0x10000000000010000 := regionTerm _ _ prog43k5080 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k4392 : region H43 0x8000010000100001000400010001000100000000000021110000090400950328 0x10000 := regionFork _ _ _ 64 reg43k4393 reg43k5080
def prog43k5216 : Array Nat := #[0x52cf9c1891c0004a64b3d791d74e4b3b391d68c0e62c42cf9d0b3d7001471875e361d74c0e59c52cf9d4b3d703967000129000cc400521001d2400bb5003a940125d005b1401bc10084240271900b644034cd00f054044bd, 0x82cede0b3b381d68c1889c5c4f7e2b3d789d74d713cb8acece275ab89d69e275a3001671773cbbaceeeeb3b7bacecee75abb9d69ee75a30496712b3e74acf5d2b3bb4acedd2b3b3049671a75e369d74da75ab69d68c1272c, 0x590e6d6438b028e616736359cd7ceb35759cd4d663cb598f1d673433acccd6732759cc8d6638b02ce20eb16759c58d6715f3ac55d67153588f2d6714759c50ceb13759c49c1982c5c0f7e0b3d781d74d703cb5c0f1e0b3bb, 0x3acacd672ab59ca9d672a3594e6d6729359ca2c0059c5ccf7e6b3cb9acf1e6b3c39aceee6b3b79acece675ab99d69e675a39ace6e6b3939ace2c0e5903ac99d6725f3ac95d67253590f2d67247590f0ceb2373ac8cd67223, 0xf59c5bcf7deb3d779d74deb3cf5bcf2d6f3c75bcf0deb3bb7aceddeb3b379d6ade75a779d68deb39b7ace5deb3937ace2c0039459cb8d672df3acb5d672d359cb3d653cb594f1d672c3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k5216 : region H43 0x8000010000100001000400010001000100000000000021110000090500950328 0x100010000 := regionTerm _ _ prog43k5216 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k4391 : region H43 0x8000010000100001000400010001000100000000000021110000090500950328 0x10000 := regionFork _ _ _ 32 reg43k4392 reg43k5216
private theorem reg43k3 : region H43 0x8000010000100001000400010001000100000000000021110000090500950328 0x0 := regionFork _ _ _ 16 reg43k4 reg43k4391
def prog43k5377 : Array Nat := #[0x25076c1270c4b879c19a3895076c0e50c000524002a575077e83743029232c3a4bb0e90c19bd0000564003390020441670cc8eeaf23ba7c8ee4c17b3800059419b38000574004d1003d140199900b08403e0901635407ab5, 0x24477c0a30c00044419b9800051400439001b6400c25003d441170c24479c911df24476c911d305a911311e74c477d311bb051432341dba446ec168b854479d511df059c3000129000d4400525001e441470c25079c941df, 0xd7400541001e4400ac500386419a1835077cd41dba1871e83343a186ec1630c49879d261df49871d261bb062c30961e7059431c3363066c6000139000a44d61dfb1871ec3343028831c336370cd7dc3343044c30911e7, 0x43440165d039061061e741877cc81db32074d061c740cd0c1172044479d111df8a076e281d388d04c0e40c22079c881df22076c881d3066e82081db82074e081bb05e431171e7ba06ec1972092076e481d3065c3000149, 0x44620c316330c50c117080004647116788876e2312788868c1918880876e021bb80868e0219b059021221e74886ed2219b05902103167066c2000121c086ef0219b05903103167066c3000121000b840062500230400bc5, 0x95474c0e50c000525551e755477c1270c0004a400541001e9400a4500344401099005a8401b0905ec20771671dc54c77147b886eee3127b8868ee219b050620941db25068c1218800044474167a0c51e83143a086ee8219b, 0x62a3323aabc8ea4c18a8c000594d51df35476cd51d3a9871ea3343a8cc9c1570c25479c951df25476c951d325471c1570c8d476e351d3a8e2aea38a705ab41351e74d477d351bb055432151db85474e151bb055c32551db, 0x59a30001550010e4006190020a400d41004044013a5005f4402021009c2418a8cb0eb2ec3a93055c20001591d459c7515f1d454ea3147a8c50ea3127a8868ea219b055c31151e745477ea344baa071ea3443aa066ea3413, 0x4b466c0e69823479c8d1df23476c8d1d723471c0d50c83476e0d1d78346ee0d19b049a330d1bbc3466c1650c0005854d1e753477d4d1d753471c16a8c68cd8da335f04a231c36e370db7c0068cb0eb2ec3ac7055a3000159, 0x49a300013943479da81df43475da81d343471da344343466da3413001a32a3a4ba8daaea36a7049a33236abc8da9c1268c000594003556d077e8d1c7a0db0e8d1bba3466e83693059a312d1e74b477d2d1d74b471d2d1bb, 0x1668c1b459da316368c57c6d15768c54c6d14768c50da312768868c1268c70db8dc36a7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k5377 : region H43 0x8000010000100001000400010001000000000000000021100000090000940238 0x10 := regionTerm _ _ prog43k5377 adj43 _ _ 28 (by decide +kernel)
def prog43k5710 : Array Nat := #[0x314330c1bbc3062c1960c0005864c1db93075e4c1d393068c19a8c60c58d83153029031c366370d94c0060cc8eaaf23aa305583000165065830001550010e40060900212400d25004044013c1005f740203500af1403519, 0xa8d92ea3643031432c364bb0d90c0c50c0005640035565c74eec1bbb8d89eec1a3b8d84eec18b0658320c1db83075e0c1d38306ee0c1a383062c0e60823079c8c1db23075c8c1d323068c1260c4b079d2c1d74b06ed2c18b, 0x64477e2c1db8b075e2c1d388d89e2c1a388d84e2c18b000032a364ba8daaea36a3a8da2c0a40c43479d8344b6a062c1260cc8daaf2368b049a3000165000c84005d568d98da365f68d94da364368d89da3613001832e3aab, 0x306208c1e72306dc0c30cc8daaf2368b03583000165065830001350010458336361877ccc1db33075d861d361871d8334360cc9ccc1a3001831a366388daada3643031431c366370d90c0c50c0004e400335]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k5710 : region H43 0x8000010000100001000400010001000000000000000021100000090400940238 0x400000010 := regionTerm _ _ prog43k5710 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k5376 : region H43 0x8000010000100001000400010001000000000000000021100000090400940238 0x10 := regionFork _ _ _ 34 reg43k5377 reg43k5710
def prog43k5836 : Array Nat := #[0x23c77c8f1db23c74c8f1c7001c32237db88df4e237ab88de9c0e50c73c77dee1db7b874de372705a8f12f1e74bc77c16a3c53c79d4f1df05a83000129000c940053900211400b11003a64014550064d401ea100922402b31, 0x78d04c0068c6bc77ded1db7b475ded1d37b46ede36ab78da9ded19b78da4c1578c7d476df51d3abc71df51bba8deaea37a7abc66ea379303cc308f1e723c71c0a30c000444cf1df79876de61d37986ede332703dc308f1e7, 0x7b075dec1d363c71dec1bb7b06dde36277b068dec19b78d84dec18b03c6206f1671bc57de21db78c55de31531bc51de21bb78c4dde312778868de219b03d0310f1e743c77de81db7a075de81d343c71de81bb7a06dde819b, 0xc50c63c77dec1db]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k5836 : region H43 0x8000010000100001000400010001000000000000000021110000090400940238 0x10000000000000010 := regionTerm _ _ prog43k5836 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k5375 : region H43 0x8000010000100001000400010001000000000000000021110000090400940238 0x10 := regionFork _ _ _ 64 reg43k5376 reg43k5836
def prog43k5935 : Array Nat := #[0x21c76c871d321c68c0e38c40cf9d033df40cf2d033c3049c30ee1e771c77dc71d370cf0c19b9c81c76e071d3066e72471db91c74c19b8c000524003410014e400821002c4400e8900515401931007b140249900acd40323d, 0x30e30ec1e761c77cec1d761c74d833cb60cf0cec1bb60ce4cec18b054e30f51e73d477ea33cba8cf0cf51bba9c68ea3393a9c62c0718821c76c871a30486200011138c59ce315f19c54ce31433886ec0e38c21c79c871df, 0x69c74ced1c768cf0ced1bb3b46cda71a33b466da339369c62c0730c39879ce61df31c76ce61d731c74ce61c738cd0ce61bb3986ccc71a339862c1138c3c479cf11df89c76e271d789c74cf11bb89c6ce271a388ce4e2718b, 0x3ce30ef1e73bc77de71db79c75de71d33bc71de71bb79c6dde71b379c68de719b78ce4de718b049a30ed1e769c77ced1d7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k5935 : region H43 0x8000010000100001000400010001000000000000000021110000090400950238 0x10010 := regionTerm _ _ prog43k5935 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k5374 : region H43 0x8000010000100001000400010001000000000000000021110000090400950238 0x10 := regionFork _ _ _ 16 reg43k5375 reg43k5935
def prog43k6049 : Array Nat := #[0xa8e72ea39c3a8e6aea39a705a6e1531e7049c300012974c77dd31d398dd0e6372705a931331e74cc77c1350c84c76e131d304943000141000c940053900275400cc50042d4015210068c401f9100946402b8900caf403a1d, 0x98d92e6c1c798d90e6c1bb9b06de636279b068c1340c44c79d131df44c75e6344b9a071e634439a06ee681b7049a31b31df6cc74e6d1c798db0e6d1bb98daae636a704e032331db8cc75e331d39c46ee638ab98e29c0070c, 0x98c50e621bb98c4de621b398c49e621a398866c1999834c77cd31db34c75cd31d399871e633439986ee661b79986ce6332799868c1370c24c79c931df24c76c931d724c74c931c724c6dc931b324c68c0c50c64c77d931d3, 0x3cc75e633cb99c71e633c399c6fe671bb99c6de671b399c68e6719b98ce4e6718b04de31f31db7cc75df31d39bc71e6f1bb9bc6de6f1b398deae637a79bc68e6f19b98de4e6f18b05a620731671cc57c731571cc54e63147, 0x1338c3cc79cf31df]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k6049 : region H43 0x8000010000100001000400010001000100000000000021110000090400950238 0x100000000000000000000000000000010 := regionTerm _ _ prog43k6049 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k5373 : region H43 0x8000010000100001000400010001000100000000000021110000090400950238 0x10 := regionFork _ _ _ 128 reg43k5374 reg43k6049
def prog43k6180 : Array Nat := #[0x52c6dc0058c82c76e0b1d782c6ee0b1b7061631711df8ac76e2b1d7049631a35e368d77c1258c70d78dc35df04963000139000cd400545001f0400aa9003944012250058c401aa10086440271900bc24037cd00fef40481d, 0x5a074d6344b5a071d6344342c6dc0050c60d78d835df60d74d835cb60d71d835c360d69c16a2c4ac79d2b1df4ac75d2b1c74ac6ed2b1b702d431741dfa0d72e8b1c7a0d70e8b1bba2c6dc1672c52c79d4b1df52c75d4b1c7, 0x22c79c8b1b702d4300011158cd8d661df32c76ccb1d759874d661c758cd0ccb1b358cc9d661a30396308b1e722c77c8b1db22c75c8b1d322c71c8b1b722c6cc8b1a302d0312b1bb4ac6cc1858c0004950b1e75a077d0b1d7, 0x1631731df5cc74e635cb9ac71e635c39ac6ee6b1b79ac6ce635ab98d69e6b1a39ac66e635939ac62c0b18822c76c8b1b3049630001111ac59d6316358c57c6b15758c54d6314758c50c6b13758c49d621a358866c0b20c, 0x3ac79d671df3ac75d671d359c73d633cb59c71d633c359c6fceb1bb3ac6dceb1b359c68d6719b58ce4d6718b0016316f1df7ac76deb1d77ac74deb1cf5bc71deb1bb7ac6ddeb1b378d6ade35a77ac68deb19b78d64deb18b, 0xb38c]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k6180 : region H43 0x8000010000100001000400010001000100000000000021110000090500950238 0x100000010 := regionTerm _ _ prog43k6180 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k5372 : region H43 0x8000010000100001000400010001000100000000000021110000090500950238 0x10 := regionFork _ _ _ 32 reg43k5373 reg43k6180
def prog43k6341 : Array Nat := #[0x62c3000129b1471ec32c3b1466ec3293038c50851e721471c0a28c30cb8cc32c3038a31451e751471c0e28c0004a40031900144400759002ed400ea5004974016d5006f4402109009cc402da100d2f403c2d01127404dcd, 0xa1466e83293062a30b51df2d476ea51c7a8cb0ea32aba8ca9ea519ba8ca4c0028c2dc76ee51bbb946dee32abb8ca9ee519bb8ca4c1628c49479d251c74946ed251b749466c1628c68cb8da32c368caada3293059c51451e7, 0x2a062c0c50c60cb8d851df2b076cac1d761474d851c760cb0d832a761466d832932b062c0518819459ca316328c57ca21db28c55ca315319451ca31431944dca3127066850b41df2d076cb41d7a1471e832c3a146ee851b7, 0x58caad632a759468d6519b58ca4d6518b000a30af1df79476de51d779474de51bb7946dde51b378caade32a779468de519b78ca4de518b039051051e741477ca81db41475ca81d341471d032c34146dca81b341466d03293, 0x99468e6519f99466e6329399462c0728c39479ce51df29c76ce51d729c74ce51c738cb0ce51bf3946ece51b73946cce51af29c68ce519b38ca4ce518b02ca31632e359477cab1db2ac75d651d359471d632c35946fcab1b3, 0x48a30b31df2cc76cb31d72cc74e651c798cb0e651bf9946ee651b79946ce651af98caae632a7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k6341 : region H43 0x8000010000100001000400010001000100000000000021110000090500950338 0x110 := regionTerm _ _ prog43k6341 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k5371 : region H43 0x8000010000100001000400010001000100000000000021110000090500950338 0x10 := regionFork _ _ _ 8 reg43k5372 reg43k6341
private theorem reg43k2 : region H43 0x8000010000100001000400010001000100000000000021110000090500950338 0x0 := regionFork _ _ _ 4 reg43k3 reg43k5371
def prog43k6522 : Array Nat := #[0x15035c1270444839c19a4875038c125040004e4002a195035e8193302901301a3bc068cc19ad00005840034900202418904c86aaf21aa3c86a2c18ac800059419c48000554004d1003cd40199900b09403e1101637407ac5, 0x13435c0a30400042419a980004d400449001b8400c21003d441268413439c4d0e313435c4d0d30628d10d0e743435d0d0cb051411b40e3a3432c1893453439d4d0d706241000129000d4400521001e241490415039c540e3, 0xd5400531001e2400ab500386419a1835038cd40d7a1832e860b7a04ccc1830441839d060d741832d060b7062c10580e70614124135b06706000149000a24d80d7c182df013330284124135b904d5e41333034c104d0e7, 0x434401655049261260e732438d260d732434d260b7484ccc126a44b439da90e34b435da90d368522c1248412439c490e312435c490d3066a91890e362434d890cb055c11350e7aa432c1992472438dc90d306641000139, 0x34410c125b3048cc126900004648d0e769038da40a768488c1920461038d840cb61029d8409b061241040e741032d0409b0612412126706704000125b1032ec409b0612112126706701000125000b64006210022c400bb5, 0x75c34c125040004e5570e755c35c127040004a400531001e8400a3500342401099005a9401b11062a40950e725434ea40cb2542dea40a7a8488ea409b050810540e315029c0e204000424940e7a1032e840b7a048ce8409b, 0x5ec1321babc86e2c17b04000594d70e335c35cd70d3b982dee1333b84c8c1790415c39c570e315c35c570d315c2dc179046dc38db70d3b85aaee16a3062f41170e745c35d170cb05d411970e365c34d970cb05e411d70e3, 0x622100015d001124006190020a400d31004024013a1005f4402025009c4417b04c06eef01b8b05ec100016125c39c970d725c34ee40b7b848cee40a7b8488ee409b05e411370e74dc35ee14bbba42dee14b3ba426ee148b, 0x44426c1289814439c510e314437c510d71442dc1150464438d910df64432d9109b045c12d10cbb4426c18504000565510e754437d510d75442dc18b84884d6e21357039a12418db90635c00884c06eef01bb705e21000161, 0x45c10001494c439d310df8a435e290d34c42de214b34c426e2148b002212e1a3bb862aee18a3045c13218abc8628c117040005940035d8d035e910cba442de818b3a4426e8188b062211110e744437d110d744432d110b7, 0x1888424439c910df88496e240d789034c910b78848ce240a788488c1170490636e418a3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k6522 : region H43 0x800001000010000100040001000100000000000000002100000009040094022c 0x4 := regionTerm _ _ prog43k6522 adj43 _ _ 28 (by decide +kernel)
def prog43k6855 : Array Nat := #[0x41412d00cbb4024c19704000565d00e374037dd00d374029c19b8480496e012530292124185b90614c00804c86eaf21ba705e010001650660100015d001124006110020e400d21004024013b1005f540204500aed403519, 0xb860eee18330414130183bc060cc105040005840035d85434eb00cbac029ea1823ac024ea180b066011900e364037d900d364032d900a764024c1281014039c500e314037c500d314029c1070444039d100df44032d10093, 0x6c038db00df83435e0d0d36c029e016a36c024e0168b000012e18abb8629ee1893b860ec0a4844c439e290938052ec00704c862af21893045c1000165000c94005dd88616e2185788614e2183388608e2180b002012e1aab, 0x40410500e714031c0e304c862af218930460100016506601000145001024d00e334037e0135b81835e060d38182de0133334029e01323039a122185b8860ce216ab0414124185b9060cc1050400052400345]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k6855 : region H43 0x800001000010000100040001000100000000000000002110000009040094022c 0x100000000000000004 := regionTerm _ _ prog43k6855 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k6521 : region H43 0x800001000010000100040001000100000000000000002110000009040094022c 0x4 := regionFork _ _ _ 68 reg43k6522 reg43k6855
def prog43k6981 : Array Nat := #[0x12c38c4b0d712c34c4b0b7049611a15e368574da15ab68568c125045c838e4b0d792c34e415a30628b10b0e742c35c18a2c52c39d4b0d706281000129000c84005490020d400b09003a640145d00651401ea500924402b41, 0x58522c115845c438d710df8ac35e2b0d35c432e215ab88568d7109b88562c175845dc38d770d35dc32eeb0b7b856aee15a3bac26ee158b02cc104b0e712c2dc0a304000425660e332c35d660d359832d613230496104b0e7, 0x82c35e0b0d35c032d700c782c2dd700a780568e0b09b5c024e0158b02c8108b0e759038d640df22c35d640d359032d640c722c2dd640a758488d6409b02d2112b0e75a438d690df4ac35d690d35a432d690c74ac2dd6909b, 0x105045c038d700df]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k6981 : region H43 0x800001000010000100040001000100000000000000002110000009050094022c 0x100000004 := regionTerm _ _ prog43k6981 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k6520 : region H43 0x800001000010000100040001000100000000000000002110000009050094022c 0x4 := regionFork _ _ _ 32 reg43k6521 reg43k6981
def prog43k7080 : Array Nat := #[0x11c35c470d311c29c12384484f9d213d7484eed213b3049c10f20e791c35e470d3904ecc19a9c61c38d870d3066a71c70e371c34c19a840004e40033100152400825002c2400e9100517401941007ad40249900ad140322d, 0x40e10f00e73c037e070d781c34cf00cb804eee013b33c024e0138b05ce10f70e73dc35cf70cbb84eeee13b3b9c29ee7093b84e2c0720411c38c470a70388100010939039ce40d721c34ce40cb3848cc1238411c39c470e3, 0x89c34cf10cb3c430cf10b7884ece270a73c426e27093884e2c0730439839cc70e339837ce60d731c34ce60cb39830ce60b7384cccc70a739824c0d3843b439da70e369c37ced0d769c34ced0cb69c30da70a769c24da138b, 0x2ce10eb0e759c38d670df3ac35d670d359c32d670c759c30ceb0b759c29d6709b59c24d6138b045c10f10e73c437e270d7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k7080 : region H43 0x800001000010000100040001000100000000000000002110000009050095022c 0x10004 := regionTerm _ _ prog43k7080 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k6519 : region H43 0x800001000010000100040001000100000000000000002110000009050095022c 0x4 := regionFork _ _ _ 16 reg43k6520 reg43k7080
def prog43k7194 : Array Nat := #[0xb866eee19b3b866aee19a3062721530e7049c100012994c35e530d39864ce61923062931130e744c35c1350464c38d930d303941000131000c840054900277400cb50043140152500690401f8900946402b9100cab403a1d, 0x9c032e700c79860ee700b79860ce700a798608c134044cc39d330df4cc35e690cb9a431e614bb9a42de614b3045c12330d78cc34e710cb9c42de618b39862ae618a304d811b30e36cc37db30d39b432e616ab985a8c00904, 0x99031e640c39902de6123399029e6122399026c1999834c38cd30df34c35cd30d399832e660c799830e660b7984cce660a7984c8c1390414c39c530e314c37c530d714c34c530c714c30c530b714c29c1050484c35e130d3, 0x3cc35e670cb99c31e670c3984eee670b7984ece670af99c29e6709b99c24e6138b04d611730e35cc37d730d39ac32e6b0c79ac30e6b0b79856ae6b0a798568e6b09b9ac24e6158b062640930e724c37c930d724c34e640cb, 0x133843cc39cf30df]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k7194 : region H43 0x800001000010000100040001000100010000000000002110000009050095022c 0x100000000000000000000000000000004 := regionTerm _ _ prog43k7194 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k6518 : region H43 0x800001000010000100040001000100010000000000002110000009050095022c 0x4 := regionFork _ _ _ 128 reg43k6519 reg43k7194
def prog43k7325 : Array Nat := #[0x53c2dc0f60463c38d8f0df63c32d8f0c7059e11af0e36bc37ded0d7001c12217db885f5c1278473c38dcf0df049e1000139000d1400535001ec400aa90039440122100590401aa50086240271900bc44037cd00feb40481d, 0x7a434d2f0c77852ede90b77852cc00504805f6e017d7805f4e017bb805ede017b3805e8c18a3c43c39d0f0df43c35d0f0cb43c31d0f0b703d411f40d7a3c32e8f0c7a05eee8f0b7a05ecc1893c53c39d4f0df53c35d4f0c7, 0x13c39c4f0c703d4100010933c38ccf0df784d6de60d779834ccf0c37982dde133379829de1323049e104f0e713c38c4f0df13c35c4f0d313c31c4f0c313c2dc4f0a703d0110f0cb43c30c167840004852f0e74bc37de90d7, 0x1e11f30d77cc34e6f0cb9bc31e6f0c3985eee6f0b7985ece617ab9bc29e617a39bc26e6f093985e2c0f10413c38c4f0c303dc100010923c39c8f0df78496de40d779034c8f0c77902dde123379029de122379026c0f104, 0x3bc39cef0df79c35de70d379c33cef0cb3bc31cef0c3784eede70b7784ecde70af79c29de709b79c24de138b03d6116f0e35bc37deb0d77ac34deb0cf5bc32d6f0c75bc30deb0b77856adeb0a778568deb09b7ac24de158b, 0xf384]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k7325 : region H43 0x800001000010000100040001000100010000000000002111000009050095022c 0x10000000000000004 := regionTerm _ _ prog43k7325 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k6517 : region H43 0x800001000010000100040001000100010000000000002111000009050095022c 0x4 := regionFork _ _ _ 64 reg43k6518 reg43k7325
def prog43k7486 : Array Nat := #[0x62c1000129c142df012b3c1426f0128b048c50450e71142dc0a284304b6cc12b3048a11450e75142dc122840004a40031900142400761002f1400ea1004954016dd006f4402111009d0402da500d2b403c3d01127404dcd, 0xa1426e8128b05ec10b70e32dc35ee50b7b84acee12abb84a8ee509bb84a2c002842d438ea50cba9431ea12aba84a8ea509ba84a2c1828441439d050cb41431d050b741426c18284884b6e212b3884aae2128b062451450e7, 0x484a2c105042c038cb00df804b6e050d781434e050b7804ace012a381426cb0093804a2c0510421439ca40e329037ca125b29035ca40d321431c850b72848cca1223066850b40e32d037cb40d7a1432e850c7a142de812b3, 0x784aade50a7784a8de509b79424de128b000a11650e359437cab0d759434d650cb59431d650c3584aad650a7584a8d6509b59424d6128b049251250e72a438d250df49435ca90d349431ca90c34942dd212b349426ca9093, 0x984a8e6509f99426e65093984a2c0728439439ca70e339437ce50d729c34ce50cb39431ce50c33942fce50b7384acce50af29c29ce509b39424ce128b038a10af0e32bc37de12db79435de50d32bc30de50b7784acde50af, 0x38a10b30e32cc37cb30d72cc34e650cb99431e650c39942fe650b7984ace650af984aae650a7]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k7486 : region H43 0x800001000010000100040001000100010000000000002111000009050095032c 0x104 := regionTerm _ _ prog43k7486 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k6516 : region H43 0x800001000010000100040001000100010000000000002111000009050095032c 0x4 := regionFork _ _ _ 8 reg43k6517 reg43k7486
def prog43k7660 : Array Nat := #[0x4e7230a7c8468f23093c8462c1220c10c38c430a7038610811db20468c1218470c38dc30a704861000139000c4400509001d9400bc1003ac401251005b7401bd50084640274500b6d40349d00f0f4044ad01373405795, 0xa8462c17b041dc39c770d3b846eee11b3b8c29ee11a3b8c24ee118b000610740e7a0c32e830c3a046ee811b3a0c24e8118b064611830e360c32d830c360c29d83093064612011db8046ee011a380462c1990c70c38c19b04, 0x45c10710e71c437e211db88c35e230d38846ce230a788468c7109b88c24e2118b00c410660e730c38cc30df30476cc30d730c34cc30c33046ccc30a730468c18a8c1d439c750df1d434ea30cba8c30ea30a7a8468ea3093, 0x78468de309f78c26de309378462c0018438c39ce30df38c35c670d338c32ce30c738c30ce11bb38c2dce11b338c26ce309338462c1268c1b439da30e368c37c6d0d768c34c6d0c768c30da30a768468c6d09b68c24da118b, 0x98c27e6309b98c24e6118b0286106b0e758c38d630df1ac35d630d358c32d630c758c30d630bf1ac2dd630a758468d6309f58c26d6309358462c0a1841bc39c6f0df78476de30d778c34c6f0c77846ede30b77846cde30a7, 0x28c37ca11db28c35ca30d328c33c650c728c30ca30bf1942dca11b328c2bca30a728468ca309f19426ca309328462c0a1841cc39c730df1cc35c730d398c32e630c798c30e630bf9846ee630b79846ce630af98c29e611a3, 0x518419439ca30e3]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k7660 : region H43 0x800001000010000100040001000100010000000000002111000009050095033c 0x14 := regionTerm _ _ prog43k7660 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k6515 : region H43 0x800001000010000100040001000100010000000000002111000009050095033c 0x4 := regionFork _ _ _ 4 reg43k6516 reg43k7660
private theorem reg43k1 : region H43 0x800001000010000100040001000100010000000000002111000009050095033c 0x0 := regionFork _ _ _ 2 reg43k2 reg43k6515
def prog43k7863 : Array Nat := #[0x14011c1670025819c19b4074018c165000004e400291b4011ec081b0288030083bc0206c198c00005840035900202418b00c822af20893c8222c18b4400059419c58000514004c1003cd4019b100b09403e2101637407ad5, 0x13411c0c500000424198b00004d400459001b8400c11003d041668013419c4d06313411c4d0430620d08d06723416c8d047041401b006383416c18b3453419d4d047062c0000129000d0400511001e241680014019c50063, 0xd1400519001e2400ab50038c41983064018e0c05b64011e0c03780186c1860023019c8c05b23011c8c037062400580670670c24c05b06140000149000a2598047c300df0061b028402c064bb0191ec061b0358004d067, 0x4304016450598912c06762418d8904762410d2c03760126c166a44b419da90634b411da904368122c1648012419c4906312411c49043066290c906332416cc9043045c01310678a416c19b2472418dc9043066c0000139, 0x35000c805b3200cc126800004650d0676a018da802768104c1940032018cc805b3200ccc80270612808806722016c88033061281204670670800012592016e480330612012046706700000125000b240061100226400bb5, 0x75c10c165000004e55706755c11c167000004a400519001e4400a35003424010b1005a9401b21062281110678a016d110434440de280338a009e204130410005006314009c0e4000004251006782016e080378200ce0041b, 0x5e40320babc82e2c179000005959706365c11d97043bb00dee061bb8184c17b0015c19c5706315c11c5704315c0dc17b006dc18db7043b81aaee0693062f009706725c16c9704705d400d706335c16cd704305e401d7063, 0x62a000015d001164006310020a400d1900402401391005f0402025009c8417900c02eef00b8b05e4000016145c19d1704745c10ee8037ba00cee8027b8106ee041305ec01370674dc11ee04bbba40dee9033b8126ee048b, 0x2540cc16ab015419c5506315417c550471540dc1550035418cd505f35416cd5033055c025505b9540cc185000005255506755417d550475540dc18b80a8192ea0647039a02c0acbb02b1c12880c02eef00bb705ea0000161, 0x55c00001594d419d3505faa411ea90434d40dd35033a8126ea048b04a002e0aabb82a4ee083b055c0320aabc82a4c157000005940035d85416eb00478540de15033a8206ea080b062a009506725417c9505b25411c95037, 0x18a8045419d1505fa8112ea8047aa010d15037aa009ea041ba8104c15700b02b2ec0a93]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k7863 : region H43 0x800001000010000100040001000000000000000000002110000009040094022a 0x2 := regionTerm _ _ prog43k7863 adj43 _ _ 28 (by decide +kernel)
def prog43k8196 : Array Nat := #[0x514025405b95008c19700000525d406375017dd404375009c19b80a0112e80443029202c0a4bb0290c12800c82eaf20ba705e800001650668000015d001164006210020e400d1100402401399005f140205500aed403531, 0xb8286ee08ab05140300a3bc0286c145000005840035d8d016e910438d009e34023a0224e8088b066800d406335017cd405b35010cd402735008c16a2015019c5406315017c5404315009c1470025019c9405f25016c94023, 0x6d018db405fa3411e8d0436d009db4023a01a4e8068b000002e0aabb82a9ee0aa3b828ec0a4804d419ea9023a012ec00700c82aaf20aa3055c0000165000c94005dda8292ea0a47a8290ea0a1ba8284ea0a0b04a202e0a3b, 0x504005406715015c0e600c82aaf20aa305680000165066800001550010259406365017e8064ba3011e8c043a300dd94027a0186e80613039a02a0a4ba8286ea06ab051402c0a4bb0286c1450000056400355]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k8196 : region H43 0x800001000010000100040001000100000000000000002110000009040094022a 0x1000000000000000000000000000000000002 := regionTerm _ _ prog43k8196 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k7862 : region H43 0x800001000010000100040001000100000000000000002110000009040094022a 0x2 := regionFork _ _ _ 144 reg43k7863 reg43k8196
def prog43k8322 : Array Nat := #[0x11418c4504711410c45037058a01a02e3680b0da02ab680a4c165002d818ec5047b1410ec02930620508506721411c1881451419d4504706200000129000c44005590020d400b09003ac40145d00655401ea500928402b51, 0x480a2c152802d418cb505f2d416ea5047a9410cb5033a80aaea0293a80a2c172802dc18cb705b2dc10ee5037b940cee02abb80a4ee028b030a00450671140dc0c500000425850632b016d8504761410d80293058a0045067, 0x2d016cb4057a1411e85043a140de850332d009cb4023a00a4e8028b020a01050672a018d0505f2a016d0505741411d050434140dca80332a009d00293024a01250672a418d2505f2a416d2505749411ca90434940dd25033, 0x145002d018cb405f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k8322 : region H43 0x800001000010000100040001000100000000000000002110000009040094032a 0x102 := regionTerm _ _ prog43k8322 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k7861 : region H43 0x800001000010000100040001000100000000000000002110000009040094032a 0x2 := regionFork _ _ _ 8 reg43k7862 reg43k8322
def prog43k8421 : Array Nat := #[0x10c11c4304310c09c1618048079d201c74806ed2019b059c0076067b0c11ec3043b0066c1988c30c18cc3043066231c306370c10c198800004e40031900156400825002c2400ea100517401951007ad4024b100ad5403215, 0x50600740671d017c7405ba0c11e83043a006ec74023a0066e8018b05c600770671dc16c77047b806eee3027b8c08ee019bb8062c0818010c18c430270390000010940c19c6805b40c11d0304340066c1618010c19c43063, 0x1d414ea3047a8c10c750371d40cea3027a8c08ea019ba8062c0c1801b019d8306360c17c6c05b60c14d8304760c10c6c03760c09c6c02360066c0d1801b419da306368c17c6d05b68c14c6d04768c10da302768c08da018b, 0x146006506728c18ca305f28c16ca305728c14c6504728c10c6503728c0cca302728c08ca018b055c00750671d417c7505b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k8421 : region H43 0x800001000010000100040001000100000000000000002110000009040094033a 0x12 := regionTerm _ _ prog43k8421 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k7860 : region H43 0x800001000010000100040001000100000000000000002110000009040094033a 0x2 := regionFork _ _ _ 4 reg43k7861 reg43k8421
def prog43k8535 : Array Nat := #[0x2040cc81023060201000e740032d000b740026c189000e019f01037c040cf0009b065a10c105b3040cc1968490416e41033065a0000149000c640056100208400b11003a940145500654401ec500930402b5d00c8540398d, 0xd019c340630d015e800cba040de810330d009e8009ba0024c150800d419c35063a8032c35037a8409ea1023a8026ea00930242008105b20408c12480000445210670a418d210374840cd2009b0602008106720416c81037, 0xdc11c37043b840dee1033b8409ee1023b8026ee0093040200300670c018e0105b80415e010530c011e010378040cc3002780408e0009b044200310670c418e2105b88415e210530c40de2103388409e2102388024c14080, 0x8c18c6105f18416c6105718414c6104708c10c610371840cc2302718408c6009b18405c0508009419ca106328417ca105b28415ca105309411ca10430940dca103328409ca102328024c179000dc19c370630dc15c37053, 0xc20061067]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k8535 : region H43 0x800001000010000100040001000100000000000000002110000009040094033e 0x6 := regionTerm _ _ prog43k8535 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k7859 : region H43 0x800001000010000100040001000100000000000000002110000009040094033e 0x2 := regionFork _ _ _ 2 reg43k7860 reg43k8535
def prog43k8665 : Array Nat := #[0xb81eaee079bb81e4c18b3c53c19c167000004a6cf047b3c10ec079bb01e4c1883c23c19c8f04703d400cf06333c10c0e50000046400311001564009dd0032d4010d500549401a51007e240253100ae840329500e83404205, 0xa3c10e807bba3c0ddf4027a01e6e8079303c8012f0674bc17de905b7a415d2f0477812ede903778126c157007d416eaf047abc10df5037a81eaea079ba81e4c0f3006bc18daf05f7b416daf043781aade0693059e02e07bb, 0x43c10de80377a00cde802778106de0413065ec18f06363c17dec05b7b015dec05363c11d8f0437b00ddec02778186de0613059e004f06713c18c4f05f13c15c4f05313c11c4f04313c0dc4f027051401f405b7d015e8f047, 0x78c15de30531bc11de01bb78c0dde303378c09de302378066de301778062c0f2802bc18caf05f79416de505779414caf0437940dde5033780aade502779408de0293780a2c187a043c19d0f05f7a016de80577a014d0f047, 0xf0800bc19c2f0630bc17de105b78415de10530bc11c2f0437840dde103378409de102378026de101778024de100f03c6006f0671bc17de305b]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k8665 : region H43 0x800001000010000100040001000100000000000000002111000009040094033e 0x10000000000000002 := regionTerm _ _ prog43k8665 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k7858 : region H43 0x800001000010000100040001000100000000000000002111000009040094033e 0x2 := regionFork _ _ _ 64 reg43k7859 reg43k8665
def prog43k8814 : Array Nat := #[0xa8166ea058b062cb14b06706240000129c2c0df0b033c0166f0058b0598b04b06712c0dc0b50032c16ccb03304940000119000c240056100275400cc50043740152100694401f9100950402ba500ca5403a0501083404b3d, 0xa2c0de8b0335d008e8059ba0162c0b10042c19d680635a017d0b05758112d6804742c0dd6041b05e401770635dc11eeb037bac0cee05abb8166ee058b02cc01710638ac16e2b0578ac0ce205ab88162c18580a8172ea05ab, 0x4ac0dd2b0335a408d6049b58122c1982c5c018d7005f82c16e0b05782c14d7004782c0de0b03382c08e0059b80162c1858022c19c8b05f22c16c8b05722c14c8b04722c0dc8b03322c08c145005d018d7405fa0172e8b047, 0x58414d600cb58411d610430ac0dd6102758408d6009b58405d6009302ca016506359417cab05b2ac15d6505359411d650432ac0cd602ab59409d65023580a4d6028b0596912b0675a418d6905f4ac15d690535a411d69043, 0x7ac0cde05ab7ac09deb02378166deb01778164deb00f78162deb00702c6006b06758c18d6305f1ac16c6b05758c14d6304758c10c6b0371ac0cd6302758c08d6019b58c05d6018b58c01c0b0800ac19d6106358417c2b057, 0xe5805bc18d6f05f7ac16deb0577ac14d6f0475bc10deb037]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k8814 : region H43 0x800001000010000100040001000100000000000000002111000009050094033e 0x100000002 := regionTerm _ _ prog43k8814 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k7857 : region H43 0x800001000010000100040001000100000000000000002111000009050094033e 0x2 := regionFork _ _ _ 32 reg43k7858 reg43k8814
def prog43k8983 : Array Nat := #[0x54c15d5304754c0dc1330034c18cd305f34c16cd305704e401b30636cc17e6d04704dc023305b8cc15c1270000051400335001664008a900310401011005024018b1007f440252500b484035bd00f6540462d013c3405885, 0x64c17e6064b9b011e6c0439b00de6061b98184c1698014c19c5306314c17c5305714c11c5304314c0dc189c024c19c9305f24c16c9305724c11c9303704d4021305b84c15e700479820ee7003798206c18b4c54c19d5305f, 0x98104c1320024c16c9305304e400001114cc19d3305f4cc15e690479a410e604bb9a40de6903398126e6048b001402809cba0271e809c3a026ee809b7a026ce8099ba0264e8098b04c4005306714c15c1350000042593063, 0x980a4e6028b049e01f305b7cc15df30539bc11e6f043981eee6f0379bc0ce607ab9bc09e6f023981e6e60793981e2c1310014c18c5305304dc000010944c19d1305f44c15e6044b9a011e680439a00de680339a009e6041b, 0x98062c0e5805cc18d7305f5cc14e605cb9ac11e6b0439ac0fe6b0379ac0ce605ab9ac09e6b02398166e6b01798164e6058b04ca00b30632cc17cb305b2cc15cb305399411e650439940fe650379940ce602ab99409e65023, 0xcc15c3305398032e6104798410e6103f9840de610339840be6102798408e6009b98405e6009398403c131801cc19c7305f1cc16c730571cc14e6304798c10e6303f9806ee6303798c0ce6302f98c09e6302398066e63017, 0x4c200330670cc18c3305f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k8983 : region H43 0x800001000010000100040001000100010000000000002111000009050094033e 0x100000000000000000000000000000002 := regionTerm _ _ prog43k8983 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k7856 : region H43 0x800001000010000100040001000100010000000000002111000009050094033e 0x2 := regionFork _ _ _ 128 reg43k7857 reg43k8983
def prog43k9179 : Array Nat := #[0x66c71c706306640000139c9c09f27023c80e4f2038b0590704706311c09c0e38021c16c87023049c0000111000c240056500274400cc10043740153100695401f9900951402bb500ca3403a0501093404b150152f405f2d, 0xa9c08ea0393a80e2c071003b019d8706361c17d87053600f2d8704361c09d8039305e400f70673dc10ee03bbb9c09ee7023b80e4ee038b01c800f006781c16e07053800eee07023800e2c19380a00f2e803bba00e4e8038b, 0x69c08da0393680e2c1889c3c419cf105f89c16e2705789c14cf104389c0ce2702789c08e20393880e2c1938031c18cc705f31c16cc705731c14cc704331c0ccc702731c08c157003d419cf505fa80f2ea70433d40cea7027, 0x38411ce10433840dce103309c09ce009b38024ce100f01c600e306738c17c6705b38c15c6705338c11ce30433806ece303738c0cc6702338066ce018b059a70ed06769c18da705f3b415da70533b411da70433b40cda7027, 0x3940dce503329c09ca7023380a4ce500f380a2ce5007028e00f30673cc17cf3057980f2e6704799c10e603bb99c0de6703399c09e67023980e6e6039399c03e6038b99c01c0708038419c2706338417ce105709c14ce00cb, 0x580e2d67007028e00ef0673bc17de705b79c15de705379c13cef0473bc10de03bb79c0dde703379c09de7023780e6de7017780e4de700f780e2de700701ca00e506729c18ce505f29c16ce505729c14ce504f39411ce5043, 0xa3803ac19d6706359c17ceb05759c14d6704f580f2d6704759c10d6703f3ac0dceb03359c09d67023580e6d67017580e4d6700f]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem reg43k9179 : region H43 0x800001000010000100040001000100010000000000002111000009050095033e 0x10002 := regionTerm _ _ prog43k9179 adj43 _ _ 28 (by decide +kernel)
private theorem reg43k7855 : region H43 0x800001000010000100040001000100010000000000002111000009050095033e 0x2 := regionFork _ _ _ 16 reg43k7856 reg43k9179
private theorem reg43k0 : region H43 0x800001000010000100040001000100010000000000002111000009050095033e 0x0 := regionFork _ _ _ 1 reg43k1 reg43k7855
private theorem safe43 : hostSafe H43 := regionHost _ _ _ bk43 reg43k0
def allHosts : Array (Array Nat) := #[H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, H32, H33, H34, H35, H36, H37, H38, H39, H40, H41, H42, H43]
private theorem hosts_safe (i : Nat) (hi : i < allHosts.size) : hostSafe (familyAt allHosts i) := by
  change i < 44 at hi
  interval_cases i
  · exact safe0
  · exact safe1
  · exact safe2
  · exact safe3
  · exact safe4
  · exact safe5
  · exact safe6
  · exact safe7
  · exact safe8
  · exact safe9
  · exact safe10
  · exact safe11
  · exact safe12
  · exact safe13
  · exact safe14
  · exact safe15
  · exact safe16
  · exact safe17
  · exact safe18
  · exact safe19
  · exact safe20
  · exact safe21
  · exact safe22
  · exact safe23
  · exact safe24
  · exact safe25
  · exact safe26
  · exact safe27
  · exact safe28
  · exact safe29
  · exact safe30
  · exact safe31
  · exact safe32
  · exact safe33
  · exact safe34
  · exact safe35
  · exact safe36
  · exact safe37
  · exact safe38
  · exact safe39
  · exact safe40
  · exact safe41
  · exact safe42
  · exact safe43
def T0 : Array Nat := #[0, 1, 2, 3, 12, 13, 14, 15, 240, 241, 242, 243, 252, 253, 254, 255]
def T1 : Array Nat := #[0, 3, 4, 7, 8, 11, 12, 15, 240, 243, 244, 247, 248, 251, 252, 255]
def T2 : Array Nat := #[0, 3, 12, 15, 80, 83, 92, 95, 160, 163, 172, 175, 240, 243, 252, 255]
def T3 : Array Nat := #[0, 5, 10, 15, 48, 53, 58, 63, 192, 197, 202, 207, 240, 245, 250, 255]
def T4 : Array Nat := #[0, 15, 16, 31, 32, 47, 48, 63, 192, 207, 208, 223, 224, 239, 240, 255]
def T5 : Array Nat := #[0, 15, 48, 63, 64, 79, 112, 127, 128, 143, 176, 191, 192, 207, 240, 255]
def T6 : Array Nat := #[0, 1, 2, 3, 4, 5, 8, 10, 12, 15, 240, 241, 242, 243, 244, 245, 248, 250, 252, 255]
def T7 : Array Nat := #[0, 1, 2, 3, 12, 13, 14, 15, 80, 81, 92, 93, 160, 162, 172, 174, 240, 243, 252, 255]
def T8 : Array Nat := #[0, 3, 4, 7, 8, 11, 12, 15, 80, 83, 84, 87, 160, 163, 168, 171, 240, 243, 252, 255]
def T9 : Array Nat := #[0, 5, 10, 15, 16, 21, 32, 42, 48, 63, 192, 197, 202, 207, 208, 213, 224, 234, 240, 255]
def T10 : Array Nat := #[0, 5, 10, 15, 48, 53, 58, 63, 64, 69, 112, 117, 128, 138, 176, 186, 192, 207, 240, 255]
def T11 : Array Nat := #[0, 15, 16, 31, 32, 47, 48, 63, 64, 79, 80, 95, 128, 143, 160, 175, 192, 207, 240, 255]
def T12 : Array Nat := #[0, 1, 2, 3, 4, 5, 8, 10, 12, 15, 48, 49, 50, 51, 192, 196, 200, 204, 240, 245, 250, 255]
def T13 : Array Nat := #[0, 1, 2, 3, 4, 5, 8, 10, 12, 15, 80, 81, 84, 85, 160, 162, 168, 170, 240, 243, 252, 255]
def T14 : Array Nat := #[0, 1, 2, 3, 12, 13, 14, 15, 16, 17, 32, 34, 48, 51, 192, 204, 208, 221, 224, 238, 240, 255]
def T15 : Array Nat := #[0, 3, 4, 7, 8, 11, 12, 15, 48, 51, 64, 68, 112, 119, 128, 136, 176, 187, 192, 204, 240, 255]
def T16 : Array Nat := #[0, 3, 12, 15, 16, 19, 32, 35, 48, 51, 64, 76, 80, 95, 128, 140, 160, 175, 192, 204, 240, 255]
def T17 : Array Nat := #[0, 5, 10, 15, 16, 21, 32, 42, 48, 63, 64, 69, 80, 85, 128, 138, 160, 170, 192, 207, 240, 255]
def T18 : Array Nat := #[0, 1, 2, 3, 4, 5, 8, 10, 12, 15, 16, 17, 32, 34, 48, 51, 192, 196, 200, 204, 208, 213, 224, 234, 240, 255]
def T19 : Array Nat := #[0, 1, 2, 3, 4, 5, 8, 10, 12, 15, 48, 49, 50, 51, 64, 68, 112, 117, 128, 136, 176, 186, 192, 204, 240, 255]
def T20 : Array Nat := #[0, 1, 2, 3, 12, 13, 14, 15, 16, 17, 32, 34, 48, 51, 64, 76, 80, 93, 128, 140, 160, 174, 192, 204, 240, 255]
def T21 : Array Nat := #[0, 3, 4, 7, 8, 11, 12, 15, 16, 19, 32, 35, 48, 51, 64, 68, 80, 87, 128, 136, 160, 171, 192, 204, 240, 255]
def T22 : Array Nat := #[0, 1, 2, 3, 4, 5, 8, 10, 12, 15, 16, 17, 32, 34, 48, 51, 64, 68, 80, 85, 128, 136, 160, 170, 192, 204, 240, 255]
set_option maxRecDepth 2048 in
def cuts0 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051756167, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049921159, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047038727, 1044666562, 1044825603, 1044563523, 1045203719, 1042466435, 1042437784, 1040602776, 1042466442, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033406087, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030262023, 1027893442, 1028081155, 1027819075, 1028427015, 1025721987, 1025664664, 1023829656, 1025721994, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013484871, 1011116738, 1011308035, 1011045955, 1011649863, 1008948867, 1008920216, 1007085208, 1008948874, 994339586, 994531331, 994269251, 995658503, 992172163, 993594119, 991501063, 994339597, 975395011, 976849671, 974756615, 979659533, 958056088, 969066122, 952551050, 957180686, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899450503, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 896044807, 893679810, 893896195, 893634115, 894209799, 891537027, 891451032, 889616024, 891537034, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 879267655, 876903106, 877123075, 876860995, 877432647, 874763907, 874706584, 872871576, 874763914, 860125954, 860346371, 860084291, 861702919, 857987203, 859638535, 857545479, 860125965, 841210051, 842894087, 840801031, 845445901, 824100504, 836945546, 820430474, 822967054, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745049991, 742685890, 742909443, 742647363, 743214983, 740550275, 740521624, 738686616, 740550282, 725908738, 726132739, 725870659, 727485703, 723773571, 725421319, 723328263, 725908749, 706996419, 708676871, 706583815, 711228685, 689915544, 702760586, 686245514, 688749838, 591691074, 591915523, 591653443, 593268039, 589556355, 591203655, 589110599, 591691085, 572779203, 574459207, 572366151, 577011021, 555701912, 568546954, 552031882, 554532174, 438561539, 440274247, 438181191, 438557962, 421408071, 423877898, 407362826, 438561551, 287194439, 291757322, 275242250, 321121039, 150652570, 168742806, 36622230, 141290256]
set_option maxRecDepth 2048 in
def cuts1 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828743, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993735, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047183896, 1044666562, 1044825603, 1044563523, 1045348888, 1042466435, 1043139335, 1041046279, 1047183882, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478663, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030439448, 1027893442, 1028081155, 1027819075, 1028604440, 1025721987, 1026362631, 1024269575, 1030439434, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013666328, 1011116738, 1011308035, 1011045955, 1011831320, 1008948867, 1009585479, 1007492423, 1013666314, 994339586, 994531331, 994269251, 995803672, 992172163, 993594119, 991501063, 994479387, 975395011, 976849671, 974756615, 979799323, 957983495, 963144461, 946400013, 994339598, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523079, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 896254488, 893679810, 893896195, 893634115, 894419480, 891537027, 892145415, 890052359, 896254474, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 879481368, 876903106, 877123075, 876860995, 877646360, 874763907, 875368263, 873275207, 879481354, 860125954, 860346371, 860084291, 861848088, 857987203, 859638535, 857545479, 860262171, 841210051, 842894087, 840801031, 845582107, 824027911, 828930829, 812186381, 860125966, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745267736, 742685890, 742909443, 742647363, 743432728, 740550275, 741150599, 739057543, 745267722, 725908738, 726132739, 725870659, 727663128, 723773571, 725421319, 723328263, 726077211, 706996419, 708676871, 706583815, 711397147, 689810695, 694713613, 677969165, 725908750, 591691074, 591915523, 591653443, 593449496, 589556355, 591203655, 589110599, 591859547, 572779203, 574459207, 572366151, 577179483, 555593031, 560495949, 543751501, 591691086, 438561539, 440274247, 438181191, 452641306, 421408071, 423877898, 407362826, 452411915, 287194439, 291757322, 275242250, 334971403, 141286666, 189000463, 55044879, 438561552]
set_option maxRecDepth 2048 in
def cuts2 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047929351, 1044666562, 1044825603, 1044563523, 1045836295, 1042466435, 1043728007, 1041634951, 1051828746, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030439448, 1027893442, 1028081155, 1027819075, 1028604440, 1025721987, 1025664664, 1023829656, 1037148698, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014669831, 1011116738, 1011308035, 1011045955, 1012576775, 1008948867, 1010468487, 1008375431, 1020633610, 994339586, 994531331, 994269251, 995678226, 992172163, 993332487, 991239431, 1001079306, 975395011, 976588039, 974494983, 984564234, 957995154, 967001738, 950486666, 1037148683, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897458695, 893679810, 893896195, 893634115, 895365639, 891537027, 893257351, 891164295, 905028106, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 879481368, 876903106, 877123075, 876860995, 877646360, 874763907, 874706584, 872871576, 888513050, 860125954, 860346371, 860084291, 861131288, 857987203, 858853191, 856760135, 864801290, 841210051, 842108743, 840015687, 848286218, 823383704, 830723722, 814208650, 888513035, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 746529287, 742685890, 742909443, 742647363, 744436231, 740550275, 742327943, 740234887, 754557450, 725908738, 726132739, 725870659, 727663128, 723773571, 725421319, 723328263, 736838154, 706996419, 708676871, 706583815, 720323082, 689915544, 702760586, 686245514, 802267659, 591691074, 591915523, 591653443, 593291794, 589556355, 590942023, 588848967, 600560138, 572779203, 574197575, 572104519, 584045066, 555608722, 566482570, 549967498, 653632011, 438561539, 438561560, 436726552, 452641306, 420211480, 423877898, 407362826, 452411915, 286255896, 291757322, 275242250, 334971403, 150652570, 150423179, 32982667, 1037148684]
set_option maxRecDepth 2048 in
def cuts3 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047038727, 1044666562, 1044825603, 1044563523, 1044534872, 1042466435, 1043252248, 1041046279, 1051542051, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1031410695, 1027893442, 1028081155, 1027819075, 1029310023, 1025721987, 1027224583, 1025123911, 1037145098, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014666247, 1011116738, 1011308035, 1011045955, 1012565575, 1008948867, 1010480135, 1008379463, 1020630026, 994339586, 994531331, 994269251, 995658503, 992172163, 993707032, 991501063, 1002882058, 975395011, 976849671, 974833240, 985843274, 957983495, 969851914, 952813130, 1051825163, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897455111, 893679810, 893896195, 893634115, 895354439, 891537027, 893268999, 891168327, 905024522, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880710663, 876903106, 877123075, 876860995, 878609991, 874763907, 876524551, 874423879, 888509450, 860125954, 860346371, 860084291, 861702919, 857987203, 859751448, 857545479, 870761482, 841210051, 842894087, 840877656, 853722698, 824027911, 837731338, 820692554, 934384651, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745049991, 742685890, 742909443, 742647363, 742618712, 740550275, 741336088, 739057543, 753754659, 725908738, 726132739, 725870659, 726699911, 723773571, 724821016, 722542471, 730326026, 706996419, 707891079, 705947224, 713287242, 689024903, 697295882, 680257098, 754553867, 591691074, 591915523, 591653443, 592744327, 589556355, 590865432, 588586887, 598205450, 572779203, 573935495, 571991640, 581166666, 555069319, 565175306, 548136522, 637113355, 438561539, 438532888, 436697880, 438561546, 420182808, 435864602, 407366410, 435864587, 286227224, 291760906, 284870234, 284870219, 141290250, 200983563, 49989195, 1051825164]
set_option maxRecDepth 2048 in
def cuts4 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047921735, 1044666562, 1044825603, 1044563523, 1045825095, 1042466435, 1043728007, 1041634951, 1051828746, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1031406663, 1027893442, 1028081155, 1027819075, 1029310023, 1025721987, 1027212935, 1025119879, 1037148682, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014662215, 1011116738, 1011308035, 1011045955, 1012565575, 1008948867, 1010468487, 1008375431, 1020633610, 994339586, 994531331, 994269251, 995803655, 992172163, 993707015, 991609927, 1003889165, 975395011, 976930311, 974833223, 987116045, 958056071, 970339341, 953562189, 1051828751, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897451079, 893679810, 893896195, 893634115, 895354439, 891537027, 893257351, 891164295, 905028106, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880706631, 876903106, 877123075, 876860995, 878609991, 874763907, 876512903, 874419847, 888513034, 860125954, 860346371, 860084291, 861848071, 857987203, 859751431, 857654343, 871768589, 841210051, 842974727, 840877639, 854995469, 824100487, 838218765, 821441613, 934388239, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 744725638, 742685890, 742909443, 742647363, 742628550, 740550275, 740535494, 738700486, 754557466, 725908738, 726132739, 725870659, 726917656, 723773571, 724821016, 722723928, 730326026, 706996419, 708044312, 705947224, 713549322, 689170072, 697034250, 680257098, 746529294, 591691074, 591915523, 591653443, 592962072, 589556355, 590865432, 588768344, 598205450, 572779203, 574088728, 571991640, 581428746, 555214488, 564913674, 548136522, 629088782, 438561539, 439750535, 437657479, 447996426, 420884359, 431219722, 414442570, 496968206, 286670727, 297002506, 280225354, 362754574, 146007690, 228537358, 94319694, 754557456]
set_option maxRecDepth 2048 in
def cuts5 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1046648966, 1044666562, 1044825603, 1044563523, 1044551878, 1042466435, 1042458822, 1040623814, 1051828762, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1031406663, 1027893442, 1028081155, 1027819075, 1029310023, 1025721987, 1027212935, 1025119879, 1037148682, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014662215, 1011116738, 1011308035, 1011045955, 1012565575, 1008948867, 1010468487, 1008375431, 1020633610, 994339586, 994531331, 994269251, 995803672, 992172163, 993707032, 991609944, 1002619978, 975395011, 976930328, 974833240, 985843274, 958056088, 969066122, 952551050, 1051828751, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897451079, 893679810, 893896195, 893634115, 895354439, 891537027, 893257351, 891164295, 905028106, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880706631, 876903106, 877123075, 876860995, 878609991, 874763907, 876512903, 874419847, 888513034, 860125954, 860346371, 860084291, 861848088, 857987203, 859751448, 857654360, 870499402, 841210051, 842974744, 840877656, 853722698, 824100504, 836945546, 820430474, 934388239, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 746521671, 742685890, 742909443, 742647363, 744425031, 740550275, 742327943, 740234887, 754557450, 725908738, 726132739, 725870659, 727663111, 723773571, 725566471, 723469383, 737813005, 706996419, 708789767, 706692679, 721039885, 689915527, 704263181, 687486029, 802267663, 591691074, 591915523, 591653443, 593449479, 589556355, 591352839, 589255751, 603628045, 572779203, 574576135, 572479047, 586854925, 555701895, 570078221, 553301069, 668312079, 438561539, 440339207, 438246151, 452641290, 421473031, 435864586, 419087434, 534127118, 287259399, 301647370, 284870218, 399913486, 150652554, 265696270, 131478606, 1051828752]
set_option maxRecDepth 2048 in
def cuts6 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047038727, 1044666562, 1044825603, 1044563523, 1045203719, 1042466435, 1043139335, 1041046279, 1047038746, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030262023, 1027893442, 1028081155, 1027819075, 1028427015, 1025721987, 1026362631, 1024269575, 1030262042, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013484871, 1011116738, 1011308035, 1011045955, 1011649863, 1008948867, 1009585479, 1007492423, 1013484890, 994339586, 994531331, 994269251, 995658503, 992172163, 993594119, 991501063, 994339597, 975395011, 976849671, 974756615, 979659533, 957983495, 963144461, 946400013, 994339615, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 896044807, 893679810, 893896195, 893634115, 894209799, 891537027, 892145415, 890052359, 896044826, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 879267655, 876903106, 877123075, 876860995, 877432647, 874763907, 875368263, 873275207, 879267674, 860125954, 860346371, 860084291, 861702919, 857987203, 859638535, 857545479, 860125965, 841210051, 842894087, 840801031, 845445901, 824027911, 828930829, 812186381, 860125983, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745049991, 742685890, 742909443, 742647363, 743214983, 740550275, 741150599, 739057543, 745050010, 725908738, 726132739, 725870659, 727485703, 723773571, 725421319, 723328263, 725908749, 706996419, 708676871, 706583815, 711228685, 689810695, 694713613, 677969165, 725908767, 591691074, 591915523, 591653443, 593268039, 589556355, 591203655, 589110599, 591691085, 572779203, 574459207, 572366151, 577011021, 555593031, 560495949, 543751501, 591691103, 438561539, 440274247, 438181191, 438557962, 421408071, 423877898, 407362826, 438561551, 287194439, 291757322, 275242250, 321121039, 141286666, 189000463, 55044879, 438561568]
set_option maxRecDepth 2048 in
def cuts7 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051756167, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049921159, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047183896, 1044666562, 1044825603, 1044563523, 1045348888, 1042466435, 1043728007, 1041634951, 1051756186, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033406087, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030262023, 1027893442, 1028081155, 1027819075, 1028427015, 1025721987, 1025664664, 1023829656, 1025721994, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013637656, 1011116738, 1011308035, 1011045955, 1011802648, 1008948867, 1010468487, 1008375431, 1018726042, 994339586, 994531331, 994269251, 995803672, 992172163, 993332487, 991239431, 994479387, 975395011, 976588039, 974494983, 979799323, 957995154, 967001738, 950486666, 966896924, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899450503, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 896254488, 893679810, 893896195, 893634115, 894419480, 891537027, 893257351, 891164295, 904955546, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 879267655, 876903106, 877123075, 876860995, 877432647, 874763907, 874706584, 872871576, 874763914, 860125954, 860346371, 860084291, 861848088, 857987203, 858853191, 856760135, 859971419, 841210051, 842108743, 840015687, 845291355, 823383704, 830723722, 814208650, 814067548, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745267736, 742685890, 742909443, 742647363, 743432728, 740550275, 742327943, 740234887, 754484890, 725908738, 726132739, 725870659, 727433297, 723773571, 725421319, 723328263, 726109467, 706996419, 708676871, 706583815, 711429403, 689915544, 702760586, 686245514, 702655772, 591691074, 591915523, 591653443, 593219665, 589556355, 590942023, 588848967, 591601499, 572779203, 574197575, 572104519, 576921435, 555608722, 566482570, 549967498, 549826396, 438561539, 438561560, 436726552, 452257827, 420211480, 423877898, 407362826, 438557981, 286255896, 291757322, 275242250, 321117469, 150652570, 150423179, 32982667, 141286686]
set_option maxRecDepth 2048 in
def cuts8 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828743, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993735, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047929351, 1044666562, 1044825603, 1044563523, 1045836295, 1042466435, 1042466456, 1040631448, 1051828762, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478663, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030439448, 1027893442, 1028081155, 1027819075, 1028604440, 1025721987, 1026362631, 1024269575, 1030439434, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014669831, 1011116738, 1011308035, 1011045955, 1012576775, 1008948867, 1008920216, 1007085208, 1018798618, 994339586, 994531331, 994269251, 995678226, 992172163, 993332487, 991239431, 1001079306, 975395011, 976588039, 974494983, 984564234, 958056088, 957263131, 942583067, 1000901916, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523079, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897458695, 893679810, 893896195, 893634115, 895365639, 891537027, 891537048, 889702040, 905028122, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 879481368, 876903106, 877123075, 876860995, 877646360, 874763907, 875368263, 873275207, 879481354, 860125954, 860346371, 860084291, 861131288, 857987203, 858853191, 856760135, 864801290, 841210051, 842108743, 840015687, 848286218, 824100504, 822755163, 808075099, 848072540, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 746529287, 742685890, 742909443, 742647363, 744436231, 740550275, 740550296, 738715288, 754557466, 725908738, 726132739, 725870659, 727663128, 723773571, 725421319, 723328263, 736838154, 706996419, 708676871, 706583815, 720323082, 689685713, 688893211, 674213147, 736660764, 591691074, 591915523, 591653443, 593291794, 589556355, 590942023, 588848967, 600560138, 572779203, 574197575, 572104519, 584045066, 555472081, 554385243, 539705179, 583831388, 438561539, 438561560, 436726552, 452641306, 420211480, 423877898, 407362826, 452411915, 286255896, 291757322, 275242250, 334971403, 150333603, 141286685, 23846173, 438557982]
set_option maxRecDepth 2048 in
def cuts9 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1046827268, 1044666562, 1044825603, 1044563523, 1045336337, 1042466435, 1042458822, 1041126469, 1051509795, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1031410695, 1027893442, 1028081155, 1027819075, 1029310023, 1025721987, 1027224583, 1025123911, 1037145098, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014666247, 1011116738, 1011308035, 1011045955, 1012565575, 1008948867, 1010480135, 1008379463, 1020630026, 994339586, 994531331, 994269251, 995803672, 992172163, 993707015, 991581272, 1003885595, 975395011, 976930328, 974833223, 986875483, 958056088, 970339355, 953329243, 1051825181, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897455111, 893679810, 893896195, 893634115, 895354439, 891537027, 893268999, 891168327, 905024522, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880710663, 876903106, 877123075, 876860995, 878609991, 874763907, 876524551, 874423879, 888509450, 860125954, 860346371, 860084291, 861848088, 857987203, 859751431, 857625688, 871765019, 841210051, 842974744, 840877639, 854754907, 824100504, 838218779, 821208667, 934384669, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745049991, 742685890, 742909443, 742647363, 742618712, 740550275, 741336088, 739057543, 753754659, 725908738, 726132739, 725870659, 726699911, 723773571, 724821016, 722542471, 730326026, 706996419, 707891079, 705947224, 713287242, 689024903, 697295882, 680257098, 754553867, 591691074, 591915523, 591653443, 592744327, 589556355, 590865432, 588586887, 598205450, 572779203, 573935495, 571991640, 581166666, 555069319, 565175306, 548136522, 637113355, 438561539, 439750535, 437657479, 447778714, 420884359, 431219722, 412426138, 495445020, 286670727, 296849306, 280225354, 346285660, 145862554, 227533852, 78374492, 754553886]
set_option maxRecDepth 2048 in
def cuts10 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047038727, 1044666562, 1044825603, 1044563523, 1044534872, 1042466435, 1043252248, 1041046279, 1051542051, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1031410695, 1027893442, 1028081155, 1027819075, 1029310023, 1025721987, 1027224583, 1025123911, 1037145098, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014666247, 1011116738, 1011308035, 1011045955, 1012565575, 1008948867, 1010480135, 1008379463, 1020630026, 994339586, 994531331, 994269251, 995658503, 992172163, 993707032, 991501063, 1002882058, 975395011, 976849671, 974833240, 985843274, 957983495, 969851914, 952813130, 1051825163, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897455111, 893679810, 893896195, 893634115, 895354439, 891537027, 893268999, 891168327, 905024522, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880710663, 876903106, 877123075, 876860995, 878609991, 874763907, 876524551, 874423879, 888509450, 860125954, 860346371, 860084291, 861702919, 857987203, 859751448, 857545479, 870761482, 841210051, 842894087, 840877656, 853722698, 824027911, 837731338, 820692554, 934384651, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 744845700, 742685890, 742909443, 742647363, 743412113, 740550275, 740535494, 739210309, 753722403, 725908738, 726132739, 725870659, 726917656, 723773571, 725566471, 722695256, 731845659, 706996419, 708044312, 706692679, 714835547, 689170072, 698299419, 681289307, 754553885, 591691074, 591915523, 591653443, 592962072, 589556355, 591352839, 588739672, 599725083, 572779203, 574088728, 572479047, 582714971, 555214488, 566178843, 549168731, 637113373, 438561539, 440339207, 438246151, 452496154, 421473031, 435864586, 417143578, 533120028, 287259399, 301566746, 284870218, 383960668, 150579994, 265208860, 116049500, 1051825182]
set_option maxRecDepth 2048 in
def cuts11 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047921735, 1044666562, 1044825603, 1044563523, 1045825095, 1042466435, 1043728007, 1041634951, 1051828746, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1031406663, 1027893442, 1028081155, 1027819075, 1029310023, 1025721987, 1027212935, 1025119879, 1037148682, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014662215, 1011116738, 1011308035, 1011045955, 1012565575, 1008948867, 1010468487, 1008375431, 1020633610, 994339586, 994531331, 994269251, 995803655, 992172163, 993707015, 991609927, 1003889165, 975395011, 976930311, 974833223, 987116045, 958056071, 970339341, 953562189, 1051828751, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897451079, 893679810, 893896195, 893634115, 895354439, 891537027, 893257351, 891164295, 905028106, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880706631, 876903106, 877123075, 876860995, 878609991, 874763907, 876512903, 874419847, 888513034, 860125954, 860346371, 860084291, 861848071, 857987203, 859751431, 857654343, 871768589, 841210051, 842974727, 840877639, 854995469, 824100487, 838218765, 821441613, 934388239, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 746521671, 742685890, 742909443, 742647363, 744425031, 740550275, 742327943, 740234887, 754557450, 725908738, 726132739, 725870659, 727663111, 723773571, 725566471, 723469383, 737813005, 706996419, 708789767, 706692679, 721039885, 689915527, 704263181, 687486029, 802267663, 591691074, 591915523, 591653443, 593449479, 589556355, 591352839, 589255751, 603628045, 572779203, 574576135, 572479047, 586854925, 555701895, 570078221, 553301069, 668312079, 438561539, 438561560, 436726552, 452641306, 420211480, 435864602, 419087450, 534127135, 286255896, 301647386, 284870234, 399913503, 150652570, 265696287, 131478623, 1051828768]
set_option maxRecDepth 2048 in
def cuts12 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047038727, 1044666562, 1044825603, 1044563523, 1045203719, 1042466435, 1043139335, 1041046279, 1047038746, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030757522, 1027893442, 1028081155, 1027819075, 1027819096, 1025721987, 1026507800, 1025091666, 1036861987, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014242450, 1011116738, 1011308035, 1011045955, 1011045976, 1008948867, 1009734680, 1008314962, 1020088867, 994339586, 994531331, 994269251, 995658503, 992172163, 993476753, 991501063, 990440212, 975395011, 976849671, 974602961, 974068507, 957983495, 963316507, 947460885, 995658533, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 896540306, 893679810, 893896195, 893634115, 893634136, 891537027, 892322840, 891136082, 904741411, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880025234, 876903106, 877123075, 876860995, 876861016, 874763907, 875549720, 874359378, 887968291, 860125954, 860346371, 860084291, 861702919, 857987203, 859291793, 857545479, 856226580, 841210051, 842894087, 840418001, 839883547, 824027911, 829131547, 813505301, 861702949, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745049991, 742685890, 742909443, 742647363, 743214983, 740550275, 741150599, 739057543, 745050010, 725908738, 726132739, 725870659, 726699911, 723773571, 725566488, 722542471, 722513813, 706996419, 707891079, 706692696, 705052571, 689024903, 694300571, 677728148, 689024933, 591691074, 591915523, 591653443, 592744327, 589556355, 591352856, 588586887, 588558229, 572779203, 573935495, 572479064, 570867611, 555069319, 560115611, 543514516, 555069349, 438561539, 438532888, 436697880, 438561546, 420182808, 432769811, 407366410, 405458838, 286227224, 291760906, 282041107, 286183318, 141290250, 174320406, 55044886, 438561575]
set_option maxRecDepth 2048 in
def cuts13 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047183896, 1044666562, 1044825603, 1044563523, 1045348888, 1042466435, 1042466456, 1040631448, 1051509795, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030262023, 1027893442, 1028081155, 1027819075, 1028427015, 1025721987, 1026362631, 1024269575, 1030262042, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013637656, 1011116738, 1011308035, 1011045955, 1011802648, 1008948867, 1008920216, 1007085208, 1017963555, 994339586, 994531331, 994269251, 995803672, 992172163, 993332487, 991239431, 994479387, 975395011, 976588039, 974494983, 979799323, 958056088, 957263131, 942583067, 993332517, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 896254488, 893679810, 893896195, 893634115, 894419480, 891537027, 891537048, 889702040, 904709155, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 879267655, 876903106, 877123075, 876860995, 877432647, 874763907, 875368263, 873275207, 879267674, 860125954, 860346371, 860084291, 861848088, 857987203, 858853191, 856760135, 859971419, 841210051, 842108743, 840015687, 845291355, 824100504, 822755163, 808075099, 840015717, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745267736, 742685890, 742909443, 742647363, 743432728, 740550275, 740550296, 738715288, 753722403, 725908738, 726132739, 725870659, 727433297, 723773571, 725421319, 723328263, 726109467, 706996419, 708676871, 706583815, 711429403, 689685713, 688893211, 674213147, 725421349, 591691074, 591915523, 591653443, 593219665, 589556355, 590942023, 588848967, 591601499, 572779203, 574197575, 572104519, 576921435, 555472081, 554385243, 539705179, 572104549, 438561539, 438561560, 436726552, 452257827, 420211480, 423877898, 407362826, 438557981, 286255896, 291757322, 275242250, 321117469, 150333603, 141286685, 23846173, 423877927]
set_option maxRecDepth 2048 in
def cuts14 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051756167, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049921159, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047183896, 1044666562, 1044825603, 1044563523, 1045348888, 1042466435, 1043728007, 1041634951, 1051756186, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033406087, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030233362, 1027893442, 1028081155, 1027819075, 1028398354, 1025721987, 1026498833, 1025119879, 1024517780, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013142616, 1011116738, 1011308035, 1011045955, 1011045976, 1008948867, 1010468487, 1007625041, 1010067092, 994339586, 994531331, 994269251, 995803672, 992172163, 993678354, 991122520, 1003889187, 975395011, 976901650, 974345816, 987116067, 958056071, 966428309, 949425819, 1033406117, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899450503, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 896016146, 893679810, 893896195, 893634115, 894181138, 891537027, 892313873, 891164295, 890304148, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 878957656, 876903106, 877123075, 876860995, 876861016, 874763907, 876512903, 873440081, 875853460, 860125954, 860346371, 860084291, 861848088, 857987203, 859722770, 856937560, 871768611, 841210051, 842946066, 840160856, 854995491, 824100487, 832472725, 815240859, 899450533, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745049991, 742685890, 742909443, 742647363, 743214983, 740550275, 740521624, 738686616, 740550282, 725908738, 726132739, 725870659, 726699911, 723773571, 725566488, 722542471, 721997717, 706996419, 708789784, 705798023, 705482645, 689170072, 703792788, 679995018, 674344854, 591691074, 591915523, 591653443, 592744327, 589556355, 590679943, 589255768, 587640731, 572779203, 573935495, 572479064, 570867611, 555214488, 564389514, 553064084, 555069334, 438561539, 439750535, 437657479, 447778714, 420884359, 427995028, 411479963, 420138917, 286670727, 293781396, 277266331, 286183333, 146007690, 212067990, 92792470, 740550311]
set_option maxRecDepth 2048 in
def cuts15 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828743, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993735, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047183896, 1044666562, 1044825603, 1044563523, 1045348888, 1042466435, 1043139335, 1041046279, 1047183882, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478663, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1029904518, 1027893442, 1028081155, 1027819075, 1029321223, 1025721987, 1026507800, 1024410712, 1031414299, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013127814, 1011116738, 1011308035, 1011045955, 1012576775, 1008948867, 1009734680, 1007637592, 1014669851, 994339586, 994531331, 994269251, 995803672, 992172163, 993476753, 991380113, 992496545, 975395011, 976849671, 974756615, 986628618, 957983495, 963316507, 946543387, 980978454, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523079, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897458695, 893679810, 893896195, 893634115, 893622470, 891537027, 892088082, 890023698, 897401364, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880714247, 876903106, 877123075, 876860995, 876845766, 874763907, 875310930, 873246546, 880628244, 860125954, 860346371, 860084291, 861848088, 857987203, 859638535, 857545479, 871023114, 841210051, 842514641, 840418001, 841763809, 824027911, 828472085, 811957013, 861702934, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 746529287, 742685890, 742909443, 742647363, 744436231, 740550275, 740550296, 738715288, 754557466, 725908738, 726132739, 725870659, 727663111, 723773571, 725566488, 723469400, 737813019, 706996419, 708732434, 706635346, 720581141, 689170072, 704263203, 687486051, 802267685, 591691074, 591915523, 591653443, 593449479, 589556355, 591352856, 589255768, 603628059, 572779203, 574547474, 572450386, 586625557, 555214488, 570078243, 553301091, 668312101, 438561539, 440339207, 438246151, 452641290, 421473031, 432769812, 415996692, 518701590, 287259399, 300878612, 284105492, 399426070, 150579994, 189000485, 55044901, 1047183911]
set_option maxRecDepth 2048 in
def cuts16 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047929351, 1044666562, 1044825603, 1044563523, 1045836295, 1042466435, 1043728007, 1041634951, 1051828746, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1029904518, 1027893442, 1028081155, 1027819075, 1027807430, 1025721987, 1026498833, 1024402193, 1024505249, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014669831, 1011116738, 1011308035, 1011045955, 1012576775, 1008948867, 1010468487, 1008375431, 1020633610, 994339586, 994531331, 994269251, 995803655, 992172163, 993025170, 990960786, 999989780, 975395011, 976248018, 974183634, 983216660, 958056071, 964880021, 948364949, 1018726038, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897458695, 893679810, 893896195, 893634115, 895365639, 891537027, 893257351, 891164295, 905028106, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 878942854, 876903106, 877123075, 876860995, 876845766, 874763907, 875536721, 873440081, 873772513, 860125954, 860346371, 860084291, 861848071, 857987203, 859034648, 856937560, 866034203, 841210051, 842257944, 840160856, 849261083, 824100487, 832013979, 815240859, 899450518, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 746529287, 742685890, 742909443, 742647363, 744436231, 740550275, 742327943, 740234887, 754557450, 725908738, 726132739, 725870659, 727663111, 723773571, 725566488, 723469400, 737813019, 706996419, 708789784, 706692696, 721039899, 689915527, 703792795, 687019675, 787587606, 591691074, 591915523, 591653443, 593449479, 589556355, 591227410, 589130322, 602624533, 572779203, 574482962, 572385874, 586109461, 555701895, 569837204, 553064084, 668312086, 438561539, 438561560, 436726552, 452641306, 420211480, 435771427, 418994275, 533381669, 286255896, 301586467, 284809315, 399426085, 150652570, 226748069, 92792485, 1051828775]
set_option maxRecDepth 2048 in
def cuts17 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1046827268, 1044666562, 1044825603, 1044563523, 1045336337, 1042466435, 1042458822, 1041126469, 1051509795, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1031410695, 1027893442, 1028081155, 1027819075, 1029310023, 1025721987, 1027224583, 1025123911, 1037145098, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014666247, 1011116738, 1011308035, 1011045955, 1012565575, 1008948867, 1010480135, 1008379463, 1020630026, 994339586, 994531331, 994269251, 995803672, 992172163, 993707015, 991581272, 1003885595, 975395011, 976930328, 974833223, 986875483, 958056088, 970339355, 953329243, 1051825181, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897455111, 893679810, 893896195, 893634115, 895354439, 891537027, 893268999, 891168327, 905024522, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880710663, 876903106, 877123075, 876860995, 878609991, 874763907, 876524551, 874423879, 888509450, 860125954, 860346371, 860084291, 861848088, 857987203, 859751431, 857625688, 871765019, 841210051, 842974744, 840877639, 854754907, 824100504, 838218779, 821208667, 934384669, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 744845700, 742685890, 742909443, 742647363, 743412113, 740550275, 740535494, 739210309, 753722403, 725908738, 726132739, 725870659, 726917656, 723773571, 725566471, 722695256, 731845659, 706996419, 708044312, 706692679, 714835547, 689170072, 698299419, 681289307, 754553885, 591691074, 591915523, 591653443, 592962072, 589556355, 591352839, 588739672, 599725083, 572779203, 574088728, 572479047, 582714971, 555214488, 566178843, 549168731, 637113373, 438561539, 438561560, 436726552, 452257827, 420211480, 435864602, 416381539, 531055653, 286255896, 301328419, 284870234, 377738853, 150333603, 263144485, 109827685, 1037145127]
set_option maxRecDepth 2048 in
def cuts18 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047183896, 1044666562, 1044825603, 1044563523, 1045348888, 1042466435, 1042941777, 1040631448, 1051509795, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1029904518, 1027893442, 1028081155, 1027819075, 1027655556, 1025721987, 1026507800, 1024402193, 1031340833, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013208452, 1011116738, 1011308035, 1011045955, 1011045976, 1008948867, 1009463633, 1008314962, 1012502881, 994339586, 994531331, 994269251, 995803672, 992172163, 993678354, 991380113, 1002046113, 975395011, 976441553, 974345816, 983208161, 958056088, 970020388, 953533540, 1051599401, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 895719558, 893679810, 893896195, 893634115, 893437892, 891537027, 892322840, 890217233, 897385249, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 878990788, 876903106, 877123075, 876860995, 876861016, 874763907, 875278673, 874359378, 878547297, 860125954, 860346371, 860084291, 861848088, 857987203, 859722770, 857195153, 868090529, 841210051, 842256593, 840160856, 849252577, 824100504, 837899812, 821412964, 934158889, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745049991, 742685890, 742909443, 742647363, 743214983, 740550275, 741150599, 739057543, 745050010, 725908738, 726132739, 725870659, 726699911, 723773571, 725566488, 722542471, 721825672, 706996419, 707891079, 705798023, 705052553, 689024903, 694300571, 677728147, 677957538, 591691074, 591915523, 591653443, 592744327, 589556355, 590679943, 588586887, 589475721, 572779203, 573935495, 572479064, 570867611, 555069319, 557965203, 543514516, 558653346, 438561539, 439750535, 437657479, 447778714, 420884359, 427995028, 413544339, 414232482, 286670727, 293781395, 277266331, 294928290, 145862554, 205701030, 90582950, 145862570]
set_option maxRecDepth 2048 in
def cuts19 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047038727, 1044666562, 1044825603, 1044563523, 1045203719, 1042466435, 1043139335, 1041046279, 1047038746, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030757522, 1027893442, 1028081155, 1027819075, 1027999633, 1025721987, 1026507800, 1024058116, 1026566049, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014242450, 1011116738, 1011308035, 1011045955, 1011255185, 1008948867, 1009734680, 1007280964, 1010050977, 994339586, 994531331, 994269251, 995658503, 992172163, 993476753, 991501063, 990440212, 975395011, 976849671, 974756615, 975989523, 957983495, 963316507, 944708361, 975301410, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 895620561, 893679810, 893896195, 893634115, 893634136, 891537027, 892170500, 890121798, 890287585, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 878876113, 876903106, 877123075, 876860995, 876861016, 874763907, 875393348, 873377350, 873772513, 860125954, 860346371, 860084291, 861702919, 857987203, 859638535, 857545479, 856226579, 841210051, 842894087, 840418001, 839883547, 824027911, 829131529, 812358408, 855997218, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745267736, 742685890, 742909443, 742647363, 743432728, 740550275, 740550296, 738715288, 753722403, 725908738, 726132739, 725870659, 726917656, 723773571, 725566488, 723154001, 731411108, 706996419, 708732433, 706635346, 714924260, 689170072, 703800865, 684962913, 753338025, 591691074, 591915523, 591653443, 592962072, 589556355, 591352856, 588969041, 599290532, 572779203, 574547473, 572450386, 582803684, 555214488, 569845281, 551007329, 635897513, 438561539, 440339207, 438246151, 452496154, 421473031, 432769812, 415996691, 504077094, 287259399, 300878611, 284105492, 388959014, 150579994, 184126242, 64822050, 452496170]
set_option maxRecDepth 2048 in
def cuts20 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051756167, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049921159, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047183896, 1044666562, 1044825603, 1044563523, 1045348888, 1042466435, 1043728007, 1041634951, 1051756186, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033406087, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1030233362, 1027893442, 1028081155, 1027819075, 1028398354, 1025721987, 1026498833, 1025119879, 1024517780, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013255057, 1011116738, 1011308035, 1011045955, 1011190673, 1008948867, 1010468487, 1008375431, 1010067091, 994339586, 994531331, 994269251, 995803672, 992172163, 993090566, 991093380, 992496545, 975395011, 976346118, 974316228, 975981473, 958056071, 966198920, 949425801, 1008920226, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899450503, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 895556049, 893679810, 893896195, 893634115, 893491665, 891537027, 893257351, 891164295, 890304147, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 878957656, 876903106, 877123075, 876860995, 876861016, 874763907, 876512903, 873440081, 875853460, 860125954, 860346371, 860084291, 861848088, 857987203, 859205764, 856937560, 856218081, 841210051, 842428612, 840160856, 839703009, 824100487, 833848969, 815240859, 889616034, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745267736, 742685890, 742909443, 742647363, 743432728, 740550275, 742327943, 740234887, 754484890, 725908738, 726132739, 725870659, 726917656, 723773571, 725566488, 723089489, 727216932, 706996419, 708789784, 706345041, 712536868, 689915527, 703792795, 684955283, 773035686, 591691074, 591915523, 591653443, 592962072, 589556355, 591227409, 589130322, 593289572, 572779203, 574482961, 572385874, 578609508, 555701895, 569837203, 553064084, 657917606, 438561539, 438561560, 436726552, 452257827, 420211480, 434850337, 416012385, 451349289, 286255896, 300894753, 282056801, 333908777, 150652570, 217745058, 98440866, 754484906]
set_option maxRecDepth 2048 in
def cuts21 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828743, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993735, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047929351, 1044666562, 1044825603, 1044563523, 1045836295, 1042466435, 1042466456, 1040631448, 1051828762, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478663, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1029904518, 1027893442, 1028081155, 1027819075, 1029321223, 1025721987, 1026507800, 1024410712, 1031414299, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1014669831, 1011116738, 1011308035, 1011045955, 1012576775, 1008948867, 1009270097, 1007205713, 1012519443, 994339586, 994531331, 994269251, 995803655, 992172163, 993025170, 990960786, 999989780, 975395011, 976248017, 974183633, 983216659, 958056088, 957437860, 942757796, 1012576806, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523079, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 897458695, 893679810, 893896195, 893634115, 895365639, 891537027, 892088081, 890023697, 897401363, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 880714247, 876903106, 877123075, 876860995, 876845766, 874763907, 875310930, 873246546, 880628244, 860125954, 860346371, 860084291, 861848071, 857987203, 859066001, 857001617, 868098579, 841210051, 842257944, 840160856, 849261083, 824100504, 823510500, 808830436, 897458726, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 746529287, 742685890, 742909443, 742647363, 744436231, 740550275, 740550296, 738715288, 754557466, 725908738, 726132739, 725870659, 727663111, 723773571, 725566488, 723469400, 737813019, 706996419, 708560388, 706463300, 719204873, 689170072, 694251297, 677736225, 778813986, 591691074, 591915523, 591653443, 593449479, 589556355, 591352836, 589255748, 603628041, 572779203, 574384838, 572320454, 586854920, 555214488, 557972833, 541457761, 659509794, 438561539, 438561560, 436726552, 452641306, 420211480, 430075553, 413560481, 515088930, 286255896, 293797089, 277282017, 395784738, 150333603, 145633193, 28192681, 1051828778]
set_option maxRecDepth 2048 in
def cuts22 : Array Nat := #[1051828736, 1051828736, 1051828288, 1051828737, 1051824256, 1051825153, 1051821121, 1051828738, 1051791552, 1051792897, 1051788865, 1051800066, 1051756161, 1051767810, 1051735106, 1051828739, 1051529472, 1051531265, 1051527233, 1051542018, 1051494529, 1051509762, 1051477058, 1051599363, 1051232449, 1051248130, 1051215426, 1051341315, 1050953346, 1051079683, 1050817603, 1051828760, 1049432384, 1049434625, 1049430593, 1049448962, 1049397889, 1049416706, 1049384002, 1049534979, 1049135809, 1049155074, 1049122370, 1049276931, 1048860290, 1049015299, 1048753219, 1049993752, 1047038721, 1047058434, 1047025730, 1047183875, 1046763650, 1046922243, 1046660163, 1047183896, 1044666562, 1044825603, 1044563523, 1045348888, 1042466435, 1042941777, 1040631448, 1051509795, 1032655232, 1032657921, 1032653889, 1032675842, 1032621185, 1032643586, 1032610882, 1032790531, 1032359105, 1032381954, 1032349250, 1032532483, 1032087170, 1032270851, 1032008771, 1033478680, 1030262017, 1030285314, 1030252610, 1030439427, 1029990530, 1030177795, 1029915715, 1029904518, 1027893442, 1028081155, 1027819075, 1027999633, 1025721987, 1026507800, 1024402193, 1036861987, 1013484865, 1013508610, 1013475906, 1013666307, 1013213826, 1013404675, 1013142595, 1013208452, 1011116738, 1011308035, 1011045955, 1011308037, 1008948867, 1009444357, 1007280964, 1011191129, 994339586, 994531331, 994269251, 995803672, 992172163, 993025170, 991380113, 992496545, 975395011, 976349701, 974183633, 981896409, 958056088, 965413593, 953243223, 1011116776, 898437568, 898440705, 898436673, 898462210, 898403969, 898429954, 898397250, 898605571, 898141889, 898168322, 898135618, 898347523, 897873538, 898085891, 897823811, 899523096, 896044801, 896071682, 896038978, 896254467, 895776898, 895992835, 895730755, 895730757, 893679810, 893896195, 893634115, 894181138, 891537027, 892088082, 890139717, 895557401, 879267649, 879294978, 879262274, 879481347, 879000194, 879219715, 878957635, 878990788, 876903106, 877123075, 876860995, 876861016, 874763907, 875549720, 873246546, 873772513, 860125954, 860346371, 860084291, 861848088, 857987203, 859034648, 857045061, 866262681, 841210051, 842256593, 840160856, 854758945, 824100504, 838190103, 816814233, 895547560, 745049985, 745077762, 745045058, 745267715, 744782978, 745006083, 744744003, 745267736, 742685890, 742909443, 742647363, 743432728, 740550275, 740550296, 738715288, 753722403, 725908738, 726132739, 725870659, 726917656, 723773571, 725566488, 723056773, 734146137, 706996419, 708042961, 706692696, 721011223, 689170072, 703800865, 684697689, 778139752, 591691074, 591915523, 591653443, 592962072, 589556355, 591227410, 589255768, 603628055, 572779203, 574384837, 572385874, 585546777, 555214488, 569063961, 551007329, 658893352, 438561539, 438561560, 436726552, 452257827, 420211480, 430075553, 416793689, 513963112, 286255896, 301159961, 277282017, 394716712, 150333603, 260789800, 112182376, 1051599403]
def allTemplates : Array (Array Nat) := #[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
def allCuts : Array (Array Nat) := #[cuts0, cuts1, cuts2, cuts3, cuts4, cuts5, cuts6, cuts7, cuts8, cuts9, cuts10, cuts11, cuts12, cuts13, cuts14, cuts15, cuts16, cuts17, cuts18, cuts19, cuts20, cuts21, cuts22]
set_option maxRecDepth 2048 in
def topFamily : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 12, 14, 15, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 0, 0, 0, 0, 3, 3, 3, 3, 0, 0, 1, 6, 6, 6, 6, 6, 2, 2, 2, 2, 13, 13, 13, 13, 2, 7, 8, 13, 13, 13, 13, 13, 3, 4, 5, 11, 3, 9, 10, 17, 12, 14, 15, 22, 12, 18, 19, 22, 11, 11, 11, 11, 17, 17, 17, 17, 16, 20, 21, 22, 22, 22, 22, 22, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 17, 17, 17, 17, 17, 17, 17, 17, 22, 22, 22, 22, 22, 22, 22, 22, 17, 17, 17, 17, 17, 17, 17, 17, 22, 22, 22, 22, 22, 22, 22, 22, 12, 14, 15, 22, 12, 18, 19, 22, 12, 14, 15, 22, 12, 18, 19, 22, 16, 20, 21, 22, 22, 22, 22, 22, 16, 20, 21, 22, 22, 22, 22, 22, 12, 14, 15, 22, 12, 18, 19, 22, 12, 14, 15, 22, 12, 18, 19, 22, 16, 20, 21, 22, 22, 22, 22, 22, 16, 20, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22]

def topGroup (g : Nat) := (List.range 16).all fun i =>
  let t := 16*g+i
  let j := lookup topFamily t
  decide (j < 23) && topologyOK t (familyAt allTemplates j)
def cutGroup (j : Nat) := (List.range 256).all fun s =>
  cutOK s (lookup (familyAt allCuts j) s) (familyAt allTemplates j) allHosts
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock0 : topGroup 0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock1 : topGroup 1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock2 : topGroup 2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock3 : topGroup 3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock4 : topGroup 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock5 : topGroup 5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock6 : topGroup 6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock7 : topGroup 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock8 : topGroup 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock9 : topGroup 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock10 : topGroup 10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock11 : topGroup 11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock12 : topGroup 12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock13 : topGroup 13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock14 : topGroup 14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock15 : topGroup 15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock16 : topGroup 16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock17 : topGroup 17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock18 : topGroup 18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock19 : topGroup 19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock20 : topGroup 20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock21 : topGroup 21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock22 : topGroup 22 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock23 : topGroup 23 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock24 : topGroup 24 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock25 : topGroup 25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock26 : topGroup 26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock27 : topGroup 27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock28 : topGroup 28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock29 : topGroup 29 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock30 : topGroup 30 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem topBlock31 : topGroup 31 = true := by decide +kernel
private theorem topBlockAll (i : Nat) (hi : i < 32) : topGroup i = true := by
  interval_cases i
  · exact topBlock0
  · exact topBlock1
  · exact topBlock2
  · exact topBlock3
  · exact topBlock4
  · exact topBlock5
  · exact topBlock6
  · exact topBlock7
  · exact topBlock8
  · exact topBlock9
  · exact topBlock10
  · exact topBlock11
  · exact topBlock12
  · exact topBlock13
  · exact topBlock14
  · exact topBlock15
  · exact topBlock16
  · exact topBlock17
  · exact topBlock18
  · exact topBlock19
  · exact topBlock20
  · exact topBlock21
  · exact topBlock22
  · exact topBlock23
  · exact topBlock24
  · exact topBlock25
  · exact topBlock26
  · exact topBlock27
  · exact topBlock28
  · exact topBlock29
  · exact topBlock30
  · exact topBlock31

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock0 : cutGroup 0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock1 : cutGroup 1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock2 : cutGroup 2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock3 : cutGroup 3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock4 : cutGroup 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock5 : cutGroup 5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock6 : cutGroup 6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock7 : cutGroup 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock8 : cutGroup 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock9 : cutGroup 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock10 : cutGroup 10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock11 : cutGroup 11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock12 : cutGroup 12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock13 : cutGroup 13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock14 : cutGroup 14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock15 : cutGroup 15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock16 : cutGroup 16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock17 : cutGroup 17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock18 : cutGroup 18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock19 : cutGroup 19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock20 : cutGroup 20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock21 : cutGroup 21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem cutBlock22 : cutGroup 22 = true := by decide +kernel
private theorem cutBlockAll (i : Nat) (hi : i < 23) : cutGroup i = true := by
  interval_cases i
  · exact cutBlock0
  · exact cutBlock1
  · exact cutBlock2
  · exact cutBlock3
  · exact cutBlock4
  · exact cutBlock5
  · exact cutBlock6
  · exact cutBlock7
  · exact cutBlock8
  · exact cutBlock9
  · exact cutBlock10
  · exact cutBlock11
  · exact cutBlock12
  · exact cutBlock13
  · exact cutBlock14
  · exact cutBlock15
  · exact cutBlock16
  · exact cutBlock17
  · exact cutBlock18
  · exact cutBlock19
  · exact cutBlock20
  · exact cutBlock21
  · exact cutBlock22


theorem classification (t : Nat) (ht : t < 512) (s : Nat) (hs : s < 256) :
    ∃ T : Array Nat, ∃ w : Nat, topologyOK t T = true ∧ cutOK s w T allHosts = true := by
  have g := topBlockAll (t/16) (by omega)
  have step := List.all_eq_true.mp g (t % 16) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have decomp : 16 * (t/16) + t % 16 = t := by omega
  simp only [decomp, Bool.and_eq_true, decide_eq_true_eq] at step
  have cut := cutBlockAll _ step.1
  exact ⟨_, _, step.2, List.all_eq_true.mp cut s (List.mem_range.mpr hs)⟩

end PEqualNP.Outside.L_meta_958_aux

open PEqualNP.Outside.L_meta_958_aux in
theorem PEqualNP.Outside.L_meta_958 :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
    (∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 4 ≤ T.card) →
    ∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed →
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) →
        (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧
          ∀ u, u ∉ I → C.eval (insert u I) = true) → 4 ≤ C.size := by
  intro n G square large C _ correct
  by_contra no
  have bound : C.size ≤ 3 := by omega
  cases n with
  | zero =>
    have impossible := large ∅ (fun v => Fin.elim0 v)
    simp at impossible
  | succ n =>
    have h : correctOn C G := fun I maxI => correct I maxI.1 maxI.2
    obtain ⟨Q, small, cover⟩ := classify_graph C G h bound allHosts classification hosts_safe square
    have := large Q cover
    omega
