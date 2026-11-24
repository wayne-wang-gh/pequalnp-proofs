import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1402_aux

private def rowMask : ℕ → ℕ
  | 0 => 3
  | 1 => 65
  | 2 => 34
  | 3 => 96
  | 4 => 6
  | 5 => 130
  | 6 => 68
  | 7 => 192
  | 8 => 12
  | 9 => 260
  | 10 => 136
  | 11 => 384
  | 12 => 24
  | 13 => 520
  | 14 => 272
  | 15 => 768
  | 16 => 17
  | 17 => 48
  | 18 => 513
  | 19 => 544
  | 20 => 165
  | 21 => 330
  | 22 => 660
  | 23 => 297
  | 24 => 594
  | _ => 0

private def rowInput (r : ℕ) (i : Fin 10) : Bool := (rowMask r).testBit i.val

private def b2n : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | k + 1, g => 2 * b2n k (fun i => g (i + 1)) + if g 0 then 1 else 0

private lemma b2n_testBit (k : ℕ) (g : ℕ → Bool) (i : ℕ) :
    (b2n k g).testBit i = (decide (i < k) && g i) := by
  induction k generalizing g i with
  | zero => simp [b2n]
  | succ k ih =>
    cases i with
    | zero =>
      simp only [b2n, Nat.zero_lt_succ, decide_true, Bool.true_and, Nat.testBit_zero]
      cases g 0 <;> simp
    | succ i =>
      simp only [b2n, Nat.succ_lt_succ_iff, Nat.testBit_succ]
      have hdiv : (2 * b2n k (fun j => g (j + 1)) + if g 0 then 1 else 0) / 2 =
          b2n k (fun j => g (j + 1)) := by
        cases g 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      rw [hdiv, ih]

private def maskOf (f : (Fin 10 → Bool) → Bool) : ℕ :=
  b2n 25 (fun r => f (rowInput r))

private lemma maskOf_and (f g : (Fin 10 → Bool) → Bool) :
    maskOf (fun y => f y && g y) = maskOf f &&& maskOf g := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [maskOf, Nat.testBit_and, b2n_testBit]
  cases decide (i < 25) <;> simp

private lemma maskOf_or (f g : (Fin 10 → Bool) → Bool) :
    maskOf (fun y => f y || g y) = maskOf f ||| maskOf g := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [maskOf, Nat.testBit_or, b2n_testBit]
  cases decide (i < 25) <;> simp

private def popFast : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m => (if m % 2 = 1 then 1 else 0) + popFast k (m / 2)

private lemma range_succ_eq_insert_image (k : ℕ) :
    Finset.range (k + 1) = insert 0 ((Finset.range k).image Nat.succ) := by
  ext x
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
  cases x with
  | zero => simp
  | succ x => simp

private lemma popFast_eq_card (k m : ℕ) :
    popFast k m = ((Finset.range k).filter (fun i => m.testBit i = true)).card := by
  induction k generalizing m with
  | zero => simp [popFast]
  | succ k ih =>
    rw [popFast, ih (m / 2), range_succ_eq_insert_image, Finset.filter_insert]
    have h0 : 0 ∉ ((Finset.range k).image Nat.succ).filter (fun i => m.testBit i = true) := by
      simp
    have himg : ((Finset.range k).image Nat.succ).filter (fun i => m.testBit i = true) =
        ((Finset.range k).filter (fun i => (m / 2).testBit i = true)).image Nat.succ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hb⟩
        exact ⟨a, ⟨ha, by simpa [Nat.testBit_succ] using hb⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, by simpa [Nat.testBit_succ] using hb⟩
    have hcard : (((Finset.range k).image Nat.succ).filter (fun i => m.testBit i = true)).card =
        ((Finset.range k).filter (fun i => (m / 2).testBit i = true)).card := by
      rw [himg, Finset.card_image_of_injective _ Nat.succ_injective]
    have htb0 : m.testBit 0 = true ↔ m % 2 = 1 := by
      simp [Nat.testBit_zero]
    by_cases hm : m % 2 = 1
    · have htb : m.testBit 0 = true := htb0.mpr hm
      rw [ite_eq_left hm, ite_eq_left htb, Finset.card_insert_of_notMem h0, hcard]
      omega
    · have htb : ¬ (m.testBit 0 = true) := fun h => hm (htb0.mp h)
      rw [ite_eq_right hm, ite_eq_right htb, hcard]
      omega

private def popA (m : ℕ) : ℕ := popFast 20 m
private def popB (m : ℕ) : ℕ := popFast 5 (m >>> 20)

private def setA (m : ℕ) : Finset ℕ := (Finset.range 20).filter (fun i => m.testBit i = true)
private def setB (m : ℕ) : Finset ℕ := (Finset.range 5).filter (fun i => (m >>> 20).testBit i = true)

private lemma popA_eq (m : ℕ) : popA m = (setA m).card := popFast_eq_card 20 m
private lemma popB_eq (m : ℕ) : popB m = (setB m).card := popFast_eq_card 5 (m >>> 20)

private lemma setA_and (u v : ℕ) : setA (u &&& v) = setA u ∩ setA v := by
  ext i
  simp only [setA, Finset.mem_filter, Finset.mem_inter, Nat.testBit_and, Bool.and_eq_true]
  tauto

private lemma setA_or (u v : ℕ) : setA (u ||| v) = setA u ∪ setA v := by
  ext i
  simp only [setA, Finset.mem_filter, Finset.mem_union, Nat.testBit_or, Bool.or_eq_true]
  tauto

private lemma setB_and (u v : ℕ) : setB (u &&& v) = setB u ∩ setB v := by
  ext i
  simp only [setB, Finset.mem_filter, Finset.mem_inter, Nat.testBit_shiftRight, Nat.testBit_and,
    Bool.and_eq_true]
  tauto

private lemma setB_or (u v : ℕ) : setB (u ||| v) = setB u ∪ setB v := by
  ext i
  simp only [setB, Finset.mem_filter, Finset.mem_union, Nat.testBit_shiftRight, Nat.testBit_or,
    Bool.or_eq_true]
  tauto

private lemma popA_le_20 (m : ℕ) : popA m ≤ 20 := by
  rw [popA_eq]
  exact (Finset.card_filter_le _ _).trans (by simp)

private lemma popA_and_le_left (u v : ℕ) : popA (u &&& v) ≤ popA u := by
  rw [popA_eq, popA_eq, setA_and]
  exact Finset.card_le_card Finset.inter_subset_left

private lemma popA_and_le_right (u v : ℕ) : popA (u &&& v) ≤ popA v := by
  rw [popA_eq, popA_eq, setA_and]
  exact Finset.card_le_card Finset.inter_subset_right

private lemma popA_or_le_add (u v : ℕ) : popA (u ||| v) ≤ popA u + popA v := by
  rw [popA_eq, popA_eq, popA_eq, setA_or]
  exact Finset.card_union_le _ _

private lemma popB_and_zero_sum (u v : ℕ) (h : popB (u &&& v) = 0) :
    popB u + popB v ≤ 5 := by
  rw [popB_eq, setB_and] at h
  rw [popB_eq, popB_eq]
  have h1 := Finset.card_union_add_card_inter (setB u) (setB v)
  have h2 : (setB u ∪ setB v).card ≤ (Finset.range 5).card := by
    apply Finset.card_le_card
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi <;> exact (Finset.mem_filter.mp hi).1
  simp only [Finset.card_range] at h2
  omega

private lemma popB_le_or_left (u v : ℕ) : popB u ≤ popB (u ||| v) := by
  rw [popB_eq, popB_eq, setB_or]
  exact Finset.card_le_card Finset.subset_union_left

private lemma popB_le_or_right (u v : ℕ) : popB v ≤ popB (u ||| v) := by
  rw [popB_eq, popB_eq, setB_or]
  exact Finset.card_le_card Finset.subset_union_right

private def bound2 (m : ℕ) : Bool :=
  let a := popA m
  let b := popB m
  decide (a ≤ 16) && (decide (2 < b) || decide (a ≤ 9)) && (decide (0 < b) || decide (a ≤ 4))

private lemma bound2_spec {m : ℕ} (h : bound2 m = true) :
    popA m ≤ 16 ∧ (popB m ≤ 2 → popA m ≤ 9) ∧ (popB m = 0 → popA m ≤ 4) := by
  simp only [bound2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, fun hb => ?_, fun hb => ?_⟩
  · rcases h.1.2 with h1 | h2
    · omega
    · exact h2
  · rcases h.2 with h1 | h2
    · omega
    · exact h2

private def S0 : List ℕ :=
  [9764867, 18874421, 5243728, 10499328, 21188608, 10092556, 18874570, 5246112, 10537472, 21798912]

private def S1 : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
   262144, 524288, 1048576, 2097152, 4194304, 5242880, 5243728, 5246112, 5246960, 8388608, 9437184,
   9764867, 10092556, 10420239, 10485760, 10499328, 10537472, 10551040, 11875587, 11913731,
   12203276, 12241420, 13960019, 13962403, 14287708, 14290092, 15742800, 15744416, 15780688,
   15781536, 16777216, 18874368, 18874421, 18874570, 18874623, 20971520, 21188608, 21798912,
   22016000, 22238032, 22240416, 22848336, 22850720, 23285813, 23285962, 23896117, 23896266,
   24118133, 24118234, 24120501, 24120554, 27276597, 27276746, 27314741, 27314890, 28639287,
   28639435, 28966973, 28967118, 30887939, 31150092, 31301635, 31367180, 31683840, 31709696,
   32290048, 32303616]

private lemma vars_in_S0 : ∀ i : Fin 10, maskOf (fun x : Fin 10 → Bool => x i) ∈ S0 := by
  decide

private lemma S0_sub_S1 : S0.all (fun u => S1.contains u) = true := by
  decide

private lemma S0_pairs_in_S1 :
    S0.all (fun u => S0.all (fun v => S1.contains (u &&& v) && S1.contains (u ||| v))) = true := by
  decide

private lemma S1_bound2 : S1.all bound2 = true := by
  decide

private def checkPairsAux (u : ℕ) : List ℕ → Bool
  | [] => true
  | v :: vs => bound2 (u &&& v) && bound2 (u ||| v) && checkPairsAux u vs

private def checkAllPairs : List ℕ → Bool
  | [] => true
  | u :: us => checkPairsAux u (u :: us) && checkAllPairs us

private lemma checkPairsAux_spec (u : ℕ) (l : List ℕ) (h : checkPairsAux u l = true) :
    ∀ v ∈ l, bound2 (u &&& v) = true ∧ bound2 (u ||| v) = true := by
  induction l with
  | nil => intro v hv; cases hv
  | cons x xs ih =>
    simp only [checkPairsAux, Bool.and_eq_true] at h
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.1
    · exact ih h.2 v hv

private lemma checkAllPairs_spec (l : List ℕ) (h : checkAllPairs l = true) :
    ∀ u ∈ l, ∀ v ∈ l, bound2 (u &&& v) = true ∧ bound2 (u ||| v) = true := by
  induction l with
  | nil => intro u hu; cases hu
  | cons x xs ih =>
    simp only [checkAllPairs, Bool.and_eq_true] at h
    have hx := checkPairsAux_spec x (x :: xs) h.1
    have hxs := ih h.2
    intro u hu v hv
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hx v hv
    · rcases List.mem_cons.mp hv with hv | hv
      · rw [hv, Nat.and_comm, Nat.or_comm]
        exact hx u (List.mem_cons_of_mem x hu)
      · exact hxs u hu v hv

private lemma S1_pairs_bound2_bool : checkAllPairs S1 = true := by
  decide +kernel

private def P2 (m : ℕ) : Prop :=
  popA m ≤ 16 ∧ (popB m ≤ 2 → popA m ≤ 9) ∧ (popB m = 0 → popA m ≤ 4)

private def P3 (m : ℕ) : Prop :=
  (popB m = 0 → popA m ≤ 9) ∧ (popA m = 20 → 3 ≤ popB m)

private def P4 (m : ℕ) : Prop :=
  ¬ (popA m = 20 ∧ popB m = 0)

private lemma P2_imp_P3 {m : ℕ} (h : P2 m) : P3 m :=
  ⟨fun hb => by have := h.2.2 hb; omega, fun ha => by have := h.1; omega⟩

private lemma P2_and_P3 {u v : ℕ} (hu : P2 u) (hv : P2 v) : P3 (u &&& v) := by
  refine ⟨fun hb => ?_, fun ha => ?_⟩
  · have hsum := popB_and_zero_sum u v hb
    have h1 := popA_and_le_left u v
    have h2 := popA_and_le_right u v
    by_cases hbu : popB u ≤ 2
    · have := hu.2.1 hbu; omega
    · have hbv : popB v ≤ 2 := by omega
      have := hv.2.1 hbv; omega
  · have h1 := popA_and_le_left u v
    have h2 := hu.1
    omega

private lemma P2_or_P3 {u v : ℕ} (hu : P2 u) (hv : P2 v) : P3 (u ||| v) := by
  refine ⟨fun hb => ?_, fun ha => ?_⟩
  · have hbu : popB u = 0 := by have := popB_le_or_left u v; omega
    have hbv : popB v = 0 := by have := popB_le_or_right u v; omega
    have h1 := hu.2.2 hbu
    have h2 := hv.2.2 hbv
    have h3 := popA_or_le_add u v
    omega
  · by_contra hlt
    have hbu : popB u ≤ 2 := by have := popB_le_or_left u v; omega
    have hbv : popB v ≤ 2 := by have := popB_le_or_right u v; omega
    have h1 := hu.2.1 hbu
    have h2 := hv.2.1 hbv
    have h3 := popA_or_le_add u v
    omega

private lemma P3_imp_P4 {m : ℕ} (h : P3 m) : P4 m := by
  rintro ⟨ha, hb⟩
  have := h.1 hb
  omega

private lemma P3_and_P4 {u v : ℕ} (hu : P3 u) (hv : P3 v) : P4 (u &&& v) := by
  rintro ⟨ha, hb⟩
  have hau : popA u = 20 := by have := popA_and_le_left u v; have := popA_le_20 u; omega
  have hav : popA v = 20 := by have := popA_and_le_right u v; have := popA_le_20 v; omega
  have hbu := hu.2 hau
  have hbv := hv.2 hav
  have hsum := popB_and_zero_sum u v hb
  omega

private lemma P3_or_P4 {u v : ℕ} (hu : P3 u) (hv : P3 v) : P4 (u ||| v) := by
  rintro ⟨ha, hb⟩
  have hbu : popB u = 0 := by have := popB_le_or_left u v; omega
  have hbv : popB v = 0 := by have := popB_le_or_right u v; omega
  have h1 := hu.1 hbu
  have h2 := hv.1 hbv
  have h3 := popA_or_le_add u v
  omega

private def T_cert : ℕ → Set ((Fin 10 → Bool) → Bool)
  | 0 => {f | maskOf f ∈ S0}
  | 1 => {f | maskOf f ∈ S1}
  | 2 => {f | P2 (maskOf f)}
  | 3 => {f | P3 (maskOf f)}
  | 4 => {f | P4 (maskOf f)}
  | _ + 5 => Set.univ

private def targetFn (z : Fin 10 → Bool) : Bool :=
  ((z 0 || z 5) && (z 1 || z 6)) || ((z 1 || z 6) && (z 2 || z 7)) ||
  ((z 2 || z 7) && (z 3 || z 8)) || ((z 3 || z 8) && (z 4 || z 9)) ||
  ((z 4 || z 9) && (z 0 || z 5))

private lemma target_pop : popA (maskOf targetFn) = 20 ∧ popB (maskOf targetFn) = 0 := by
  decide

theorem main_proof :
    ¬ (∀ T : ℕ → Set ((Fin 10 → Bool) → Bool), (∀ i : Fin 10, (fun x : Fin 10 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 10 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 10 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 10 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 10 → Bool => f y || g y) ∈ T (k + 1)) → targetFn ∈ T 4) := by
  intro hall
  have h4 : targetFn ∈ T_cert 4 := hall T_cert
    (fun i => vars_in_S0 i)
    (fun k f hf => by
      match k with
      | 0 => exact List.contains_iff_mem.mp (List.all_eq_true.mp S0_sub_S1 (maskOf f) hf)
      | 1 => exact bound2_spec (List.all_eq_true.mp S1_bound2 (maskOf f) hf)
      | 2 => exact P2_imp_P3 hf
      | 3 => exact P3_imp_P4 hf
      | _ + 4 => trivial)
    (fun k f g hf hg => by
      match k with
      | 0 =>
        have hp := List.all_eq_true.mp (List.all_eq_true.mp S0_pairs_in_S1 (maskOf f) hf) (maskOf g) hg
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hp
        constructor
        · change maskOf (fun y => f y && g y) ∈ S1
          rw [maskOf_and]; exact hp.1
        · change maskOf (fun y => f y || g y) ∈ S1
          rw [maskOf_or]; exact hp.2
      | 1 =>
        have hp := checkAllPairs_spec S1 S1_pairs_bound2_bool (maskOf f) hf (maskOf g) hg
        constructor
        · change P2 (maskOf (fun y => f y && g y))
          rw [maskOf_and]; exact bound2_spec hp.1
        · change P2 (maskOf (fun y => f y || g y))
          rw [maskOf_or]; exact bound2_spec hp.2
      | 2 =>
        constructor
        · change P3 (maskOf (fun y => f y && g y))
          rw [maskOf_and]; exact P2_and_P3 hf hg
        · change P3 (maskOf (fun y => f y || g y))
          rw [maskOf_or]; exact P2_or_P3 hf hg
      | 3 =>
        constructor
        · change P4 (maskOf (fun y => f y && g y))
          rw [maskOf_and]; exact P3_and_P4 hf hg
        · change P4 (maskOf (fun y => f y || g y))
          rw [maskOf_or]; exact P3_or_P4 hf hg
      | _ + 4 => exact ⟨trivial, trivial⟩)
  exact h4 target_pop

end PEqualNP.Outside.L_meta_1402_aux

theorem PEqualNP.Outside.L_meta_1402 : ¬ (∀ T : ℕ → Set ((Fin 10 → Bool) → Bool), (∀ i : Fin 10, (fun x : Fin 10 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 10 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 10 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 10 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 10 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 10 → Bool => ((z 0 || z 5) && (z 1 || z 6)) || ((z 1 || z 6) && (z 2 || z 7)) || ((z 2 || z 7) && (z 3 || z 8)) || ((z 3 || z 8) && (z 4 || z 9)) || ((z 4 || z 9) && (z 0 || z 5))) ∈ T 4) :=
  PEqualNP.Outside.L_meta_1402_aux.main_proof
