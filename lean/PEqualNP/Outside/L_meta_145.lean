import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_145_aux

open PEqualNP.MetaComplexity

private def occ {n : ℕ} : DMFormula n → Fin n → ℕ
  | .lit j _, i => if i = j then 1 else 0
  | .and L R, i => occ L i + occ R i
  | .or L R, i => occ L i + occ R i

private theorem occ_sum {n : ℕ} (F : DMFormula n) : (∑ i, occ F i) = F.leaves := by
  classical
  induction F with
  | lit i b => simp [occ, DMFormula.leaves]
  | and L R hl hr => simp [occ, Finset.sum_add_distrib, hl, hr, DMFormula.leaves]
  | or L R hl hr => simp [occ, Finset.sum_add_distrib, hl, hr, DMFormula.leaves]

private theorem eval_agree {n : ℕ} (F : DMFormula n) (x y : Fin n → Bool)
    (h : ∀ i, 0 < occ F i → x i = y i) : F.eval x = F.eval y := by
  induction F with
  | lit i b =>
    have e : x i = y i := h i (by simp [occ])
    simp [DMFormula.eval, e]
  | and L R hl hr =>
    have eL := hl (fun i hi => h i (by simp only [occ]; omega))
    have eR := hr (fun i hi => h i (by simp only [occ]; omega))
    simp [DMFormula.eval, eL, eR]
  | or L R hl hr =>
    have eL := hl (fun i hi => h i (by simp only [occ]; omega))
    have eR := hr (fun i hi => h i (by simp only [occ]; omega))
    simp [DMFormula.eval, eL, eR]

private abbrev Table := Bool → Bool → Bool

private def merge (isOr : Bool) (a b : Bool) : Bool := if isOr then a || b else a && b

private theorem merge_comm (t a b : Bool) : merge t a b = merge t b a := by
  cases t <;> simp [merge, Bool.or_comm, Bool.and_comm]

private def ignoresLeft (a : Table) : Prop := ∀ v, a false v = a true v

private def ignoresRight (a : Table) : Prop := ∀ u, a u false = a u true

private theorem one_constant : ∀ (t s : Bool) (a b : Table),
    (∀ u v, b u v = b false false) →
    (∀ u v, merge t (a u v) (b u v) = merge s u v) →
    ∀ u v, a u v = merge s u v := by
  decide

private theorem split_impossible : ∀ (t : Bool) (a b : Table),
    (∀ v, a false v = a true v) → (∀ u, b u false = b u true) →
    (∀ u v, merge t (a u v) (b u v) = merge (!t) u v) → False := by
  decide

private theorem constant_table (a : Table) (hl : ignoresLeft a) (hr : ignoresRight a) :
    ∀ u v, a u v = a false false := by
  intro u v
  cases u <;> cases v
  · rfl
  · exact (hr false).symm
  · exact (hl false).symm
  · exact (hl true).symm.trans (hr false).symm

private def table {n : ℕ} (F : DMFormula n) (x : Fin n → Bool) (i j : Fin n) : Table :=
  fun b c => F.eval (Function.update (Function.update x i b) j c)

private theorem no_left {n : ℕ} (F : DMFormula n) (x : Fin n → Bool) (i j : Fin n)
    (absent : occ F i = 0) : ignoresLeft (table F x i j) := by
  intro c
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  by_cases kj : k = j <;> simp [ne, kj]

private theorem no_right {n : ℕ} (F : DMFormula n) (x : Fin n → Bool) (i j : Fin n)
    (absent : occ F j = 0) : ignoresRight (table F x i j) := by
  intro b
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [Function.update_of_ne ne]

private theorem factor {n : ℕ} (L R : DMFormula n) (i j : Fin n) (low high : Fin n → Bool)
    (isOr : Bool) (hi : occ L i + occ R i ≤ 1) (hj : occ L j + occ R j ≤ 1)
    (atLow : ∀ u v, merge isOr (table L low i j u v) (table R low i j u v) = (u && v))
    (atHigh : ∀ u v, merge isOr (table L high i j u v) (table R high i j u v) = (u || v)) :
    ((∀ u v, table L low i j u v = (u && v)) ∧ (∀ u v, table L high i j u v = (u || v))) ∨
    ((∀ u v, table R low i j u v = (u && v)) ∧ (∀ u v, table R high i j u v = (u || v))) := by
  have il : occ L i = 0 ∨ occ R i = 0 := by omega
  have jl : occ L j = 0 ∨ occ R j = 0 := by omega
  have split (A B : DMFormula n) (ha : occ A i = 0) (hb : occ B j = 0)
      (hl : ∀ u v, merge isOr (table A low i j u v) (table B low i j u v) = (u && v))
      (hh : ∀ u v, merge isOr (table A high i j u v) (table B high i j u v) = (u || v)) : False := by
    cases isOr
    · exact split_impossible false _ _ (no_left A high i j ha) (no_right B high i j hb) hh
    · exact split_impossible true _ _ (no_left A low i j ha) (no_right B low i j hb) hl
  have reverse (x : Fin n → Bool) (u v : Bool) :=
    merge_comm isOr (table R x i j u v) (table L x i j u v)
  rcases il with il | ir <;> rcases jl with jl | jr
  · exact Or.inr ⟨one_constant isOr false _ _
      (constant_table _ (no_left L low i j il) (no_right L low i j jl))
      (fun u v => (reverse low u v).trans (atLow u v)),
      one_constant isOr true _ _ (constant_table _ (no_left L high i j il) (no_right L high i j jl))
        (fun u v => (reverse high u v).trans (atHigh u v))⟩
  · exact (split L R il jr atLow atHigh).elim
  · exact (split R L ir jl (fun u v => (reverse low u v).trans (atLow u v))
      (fun u v => (reverse high u v).trans (atHigh u v))).elim
  · exact Or.inl ⟨one_constant isOr false _ _
      (constant_table _ (no_left R low i j ir) (no_right R low i j jr)) atLow,
      one_constant isOr true _ _
        (constant_table _ (no_left R high i j ir) (no_right R high i j jr)) atHigh⟩

-- If i and j each occur once, their first common gate fixes which operation can combine them.
private theorem cannot_change_operator {n : ℕ} (F : DMFormula n) (i j : Fin n)
    (low high : Fin n → Bool) (ne : i ≠ j) (hi : occ F i ≤ 1) (hj : occ F j ≤ 1)
    (atLow : ∀ u v, table F low i j u v = (u && v))
    (atHigh : ∀ u v, table F high i j u v = (u || v)) : False := by
  induction F with
  | lit k p =>
    by_cases hk : i = k
    · have hzero : occ (DMFormula.lit k p) j = 0 := by simp [occ, hk ▸ ne.symm]
      have h := no_right (.lit k p) low i j hzero true
      rw [atLow, atLow] at h
      contradiction
    · have hzero : occ (DMFormula.lit k p) i = 0 := by simp [occ, hk]
      have h := no_left (.lit k p) low i j hzero true
      rw [atLow, atLow] at h
      contradiction
  | and L R hl hr =>
    change occ L i + occ R i ≤ 1 at hi
    change occ L j + occ R j ≤ 1 at hj
    rcases factor L R i j low high false hi hj atLow atHigh with h | h
    · exact hl (by omega) (by omega) h.1 h.2
    · exact hr (by omega) (by omega) h.1 h.2
  | or L R hl hr =>
    change occ L i + occ R i ≤ 1 at hi
    change occ L j + occ R j ≤ 1 at hj
    rcases factor L R i j low high true hi hj atLow atHigh with h | h
    · exact hl (by omega) (by omega) h.1 h.2
    · exact hr (by omega) (by omega) h.1 h.2

private def fibre {n : ℕ} (part : Fin n → Fin 4) (k : Fin 4) : Finset (Fin n) :=
  Finset.univ.filter (fun i => part i = k)

private def hit {n : ℕ} (part : Fin n → Fin 4) (k : Fin 4) (x : Fin n → Bool) : Bool :=
  decide (∃ i : Fin n, part i = k ∧ x i = true)

private theorem hit_true {n : ℕ} (part : Fin n → Fin 4) (k : Fin 4) (x : Fin n → Bool) :
    hit part k x = true ↔ ∃ i : Fin n, part i = k ∧ x i = true := by simp [hit]

private def path (a b c d : Bool) := (a && b) || (b && c) || (c && d)

private def goal {n : ℕ} (part : Fin n → Fin 4) (x : Fin n → Bool) :=
  path (hit part 0 x) (hit part 1 x) (hit part 2 x) (hit part 3 x)

private def upd₂ {n : ℕ} (x : Fin n → Bool) (i j : Fin n) (a b : Bool) :=
  Function.update (Function.update x i a) j b

private theorem hit_update {n : ℕ} (part : Fin n → Fin 4) (k : Fin 4)
    (x : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    hit part k (upd₂ x i j a b) =
      ((decide (part i = k) && a) || (decide (part j = k) && b) ||
        decide (∃ w : Fin n, part w = k ∧ w ≠ i ∧ w ≠ j ∧ x w = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [hit_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, hx⟩
    by_cases e : w = i
    · subst w
      exact Or.inl (Or.inl ⟨hw, by simpa [upd₂, Function.update_of_ne hij] using hx⟩)
    by_cases eq : w = j
    · subst w
      exact Or.inl (Or.inr ⟨hw, by simpa [upd₂] using hx⟩)
    exact Or.inr ⟨w, hw, e, eq,
      by simpa [upd₂, Function.update_of_ne e, Function.update_of_ne eq] using hx⟩
  · rintro ((⟨h, e⟩ | ⟨h, e⟩) | ⟨w, h, wi, wj, e⟩)
    · exact ⟨i, h, by simpa [upd₂, Function.update_of_ne hij] using e⟩
    · exact ⟨j, h, by simpa [upd₂] using e⟩
    · exact ⟨w, h, by simpa [upd₂, Function.update_of_ne wi, Function.update_of_ne wj] using e⟩

private def pairBit (p q k : Fin 4) (a b : Bool) :=
  (decide (p = k) && a) || (decide (q = k) && b)

private theorem hit_zero {n : ℕ} (part : Fin n → Fin 4) (k : Fin 4)
    (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    hit part k (upd₂ (fun _ => false) i j a b) = pairBit (part i) (part j) k a b := by
  simp [hit_update _ _ _ _ _ hij, pairBit]

private def mate : Fin 4 → Fin 4 := ![1, 0, 3, 2]

private def pairGoal (p q : Fin 4) (a b : Bool) :=
  path (pairBit p q 0 a b) (pairBit p q 1 a b) (pairBit p q 2 a b) (pairBit p q 3 a b)

private theorem mate_ne : ∀ p, p ≠ mate p := by decide

private theorem mate_row : ∀ p, pairGoal p (mate p) true true = true ∧
    pairGoal p (mate p) false true = false := by decide

private theorem each_occurs {n : ℕ} (part : Fin n → Fin 4) (onto : Function.Surjective part)
    (F : DMFormula n) (computes : ∀ x, F.eval x = goal part x) (i : Fin n) : 1 ≤ occ F i := by
  obtain ⟨j, hj⟩ := onto (mate (part i))
  have hij : i ≠ j := fun h => mate_ne (part i) ((congrArg part h).trans hj)
  have actual (u : Bool) : goal part (upd₂ (fun _ => false) i j u true) =
      pairGoal (part i) (mate (part i)) u true := by
    simp [goal, pairGoal, hj, hit_zero _ _ _ _ hij]
  by_contra! absent
  have h := no_left F (fun _ => false) i j (by omega) true
  change F.eval (upd₂ (fun _ => false) i j false true) =
    F.eval (upd₂ (fun _ => false) i j true true) at h
  rw [computes, computes, actual, actual, (mate_row _).1, (mate_row _).2] at h
  contradiction

private theorem middle_rows {n : ℕ} (part : Fin n → Fin 4) (onto : Function.Surjective part)
    (i j : Fin n) (hi : part i = 1) (hj : part j = 2) :
    ∃ low high : Fin n → Bool,
      (∀ a b, goal part (upd₂ low i j a b) = (a && b)) ∧
      (∀ a b, goal part (upd₂ high i j a b) = (a || b)) := by
  have ne : i ≠ j := by
    intro eq
    exact (by decide : (1 : Fin 4) ≠ 2) (hi.symm.trans ((congrArg part eq).trans hj))
  let high := fun w : Fin n => decide (part w = 0 ∨ part w = 3)
  have outer0 : ∃ w : Fin n, part w = 0 ∧ w ≠ i ∧ w ≠ j ∧ high w = true := by
    obtain ⟨w, hw⟩ := onto 0
    refine ⟨w, hw, ?_, ?_, by simp [high, hw]⟩
    · intro e; exact (by decide : (0 : Fin 4) ≠ 1) (hw.symm.trans (e ▸ hi))
    · intro e; exact (by decide : (0 : Fin 4) ≠ 2) (hw.symm.trans (e ▸ hj))
  have outer3 : ∃ w : Fin n, part w = 3 ∧ w ≠ i ∧ w ≠ j ∧ high w = true := by
    obtain ⟨w, hw⟩ := onto 3
    refine ⟨w, hw, ?_, ?_, by simp [high, hw]⟩
    · intro e; exact (by decide : (3 : Fin 4) ≠ 1) (hw.symm.trans (e ▸ hi))
    · intro e; exact (by decide : (3 : Fin 4) ≠ 2) (hw.symm.trans (e ▸ hj))
  have inner1 : ¬ ∃ w : Fin n, part w = 1 ∧ w ≠ i ∧ w ≠ j ∧ high w = true := by
    rintro ⟨w, hw, _, _, h⟩
    simp [high, hw] at h
  have inner2 : ¬ ∃ w : Fin n, part w = 2 ∧ w ≠ i ∧ w ≠ j ∧ high w = true := by
    rintro ⟨w, hw, _, _, h⟩
    simp [high, hw] at h
  refine ⟨fun _ => false, high, ?_, ?_⟩
  · intro a b
    simp [goal, path, pairBit, hi, hj, hit_zero _ _ _ _ ne]
  · intro a b
    rw [goal]
    simp only [hit_update _ _ _ _ _ ne, hi, hj, outer0, outer3, inner1, inner2]
    cases a <;> cases b <;> decide

private theorem enough_repeats {n : ℕ} (F : DMFormula n) (part : Fin n → Fin 4)
    (once : ∀ i, 1 ≤ occ F i) (k : Fin 4)
    (repeats : ∀ i, part i = k → 2 ≤ occ F i) : n + (fibre part k).card ≤ F.leaves := by
  rw [← occ_sum]
  have sum : (∑ i : Fin n, (1 + (if part i = k then 1 else 0))) ≤ ∑ i : Fin n, occ F i := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : part i = k
    · simpa [h] using repeats i h
    · simpa [h] using once i
  simpa [Finset.sum_add_distrib, Finset.sum_ite, fibre] using sum

-- With fewer extra leaves than either middle block has variables, each block has a single occurrence.
private theorem lower_bound {n : ℕ} (part : Fin n → Fin 4) (onto : Function.Surjective part)
    (F : DMFormula n) (computes : ∀ x, F.eval x = goal part x) :
    n + min (fibre part 1).card (fibre part 2).card ≤ F.leaves := by
  by_contra! small
  have once := each_occurs part onto F computes
  have unique_var (k : Fin 4) (hc : min (fibre part 1).card (fibre part 2).card ≤ (fibre part k).card) :
      ∃ i, part i = k ∧ occ F i ≤ 1 := by
    by_contra! many
    have big := enough_repeats F part once k (fun i hi => by have := many i hi; omega)
    omega
  obtain ⟨i, hi, hfi⟩ := unique_var 1 (min_le_left ..)
  obtain ⟨j, hj, hfj⟩ := unique_var 2 (min_le_right ..)
  have ne : i ≠ j := by
    intro eq
    exact (by decide : (1 : Fin 4) ≠ 2) (hi.symm.trans ((congrArg part eq).trans hj))
  obtain ⟨low, high, hl, hh⟩ := middle_rows part onto i j hi hj
  exact cannot_change_operator F i j low high ne hfi hfj
    (fun a b => (computes _).trans (hl a b)) (fun a b => (computes _).trans (hh a b))

private def orList {n : ℕ} (i : Fin n) : List (Fin n) → DMFormula n
  | [] => .lit i true
  | j :: rest => .or (.lit i true) (orList j rest)

private theorem orList_leaves {n : ℕ} (i : Fin n) (rest : List (Fin n)) :
    (orList i rest).leaves = (i :: rest).length := by
  induction rest generalizing i with
  | nil => rfl
  | cons j rest ih => simp [orList, DMFormula.leaves, ih, Nat.add_comm]

private theorem orList_eval {n : ℕ} (i : Fin n) (rest : List (Fin n)) (x : Fin n → Bool) :
    (orList i rest).eval x = true ↔ ∃ j ∈ i :: rest, x j = true := by
  induction rest generalizing i with
  | nil => simp [orList, DMFormula.eval]
  | cons j rest ih =>
    simp only [orList, DMFormula.eval, ite_true, Bool.or_eq_true]
    rw [ih]
    constructor
    · rintro (hi | ⟨k, hk, hv⟩)
      · exact ⟨i, by simp, hi⟩
      · exact ⟨k, List.mem_cons_of_mem _ hk, hv⟩
    · rintro ⟨k, hk, hv⟩
      rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inl hv
      · exact Or.inr ⟨k, hk, hv⟩

private theorem component_formula {n : ℕ} (part : Fin n → Fin 4) (onto : Function.Surjective part)
    (k : Fin 4) : ∃ F : DMFormula n, F.leaves = (fibre part k).card ∧ ∀ x, F.eval x = hit part k x := by
  classical
  obtain ⟨a, ha⟩ := onto k
  have ha' : a ∈ (fibre part k).toList := by simp [fibre, ha]
  cases hlist : (fibre part k).toList with
  | nil => simp [hlist] at ha'
  | cons i rest =>
    refine ⟨orList i rest, ?_, ?_⟩
    · rw [orList_leaves, ← hlist, Finset.length_toList]
    · intro x
      apply Bool.eq_iff_iff.mpr
      rw [orList_eval, hit_true, ← hlist]
      simp [fibre]

private theorem factored_right : ∀ a b c d : Bool, path a b c d = (((a || c) && b) || (c && d)) := by
  decide

private theorem factored_left : ∀ a b c d : Bool, path a b c d = ((a && b) || ((b || d) && c)) := by
  decide

private theorem upper_bound {n : ℕ} (part : Fin n → Fin 4) (onto : Function.Surjective part) :
    HasLeafSize n (goal part) ((fibre part 0).card + (fibre part 1).card + (fibre part 2).card +
      (fibre part 3).card + min (fibre part 1).card (fibre part 2).card) := by
  obtain ⟨A, a, av⟩ := component_formula part onto 0
  obtain ⟨B, b, bv⟩ := component_formula part onto 1
  obtain ⟨C, c, cv⟩ := component_formula part onto 2
  obtain ⟨D, d, dv⟩ := component_formula part onto 3
  by_cases smaller : (fibre part 1).card ≤ (fibre part 2).card
  · refine ⟨.or (.and A B) (.and (.or B D) C), ?_, ?_⟩
    · simp only [DMFormula.leaves, a, b, c, d, min_eq_left smaller]
      omega
    · intro x
      simpa [DMFormula.eval, av, bv, cv, dv, goal] using (factored_left _ _ _ _).symm
  · refine ⟨.or (.and (.or A C) B) (.and C D), ?_, ?_⟩
    · simp only [DMFormula.leaves, a, b, c, d, min_eq_right (by omega : (fibre part 2).card ≤
        (fibre part 1).card)]
      omega
    · intro x
      simpa [DMFormula.eval, av, bv, cv, dv, goal] using (factored_right _ _ _ _).symm

private def slot {n : ℕ} (ka kb kc : ℕ) (i : Fin n) : Fin 4 :=
  if i.val < ka then 0 else if i.val < ka + kb then 1 else if i.val < ka + kb + kc then 2 else 3

private theorem slot0 {n ka kb kc : ℕ} (i : Fin n) : slot ka kb kc i = 0 ↔ i.val < ka := by
  by_cases ha : i.val < ka
  · simp [slot, ha]
  · by_cases hb : i.val < ka + kb <;> by_cases hc : i.val < ka + kb + kc <;> simp [slot, ha, hb, hc]

private theorem slot1 {n ka kb kc : ℕ} (i : Fin n) :
    slot ka kb kc i = 1 ↔ ka ≤ i.val ∧ i.val < ka + kb := by
  by_cases ha : i.val < ka
  · simp [slot, ha, show ¬ ka ≤ i.val by omega]
  · by_cases hb : i.val < ka + kb <;> by_cases hc : i.val < ka + kb + kc <;>
      simp [slot, ha, hb, hc, show ka ≤ i.val by omega]

private theorem slot2 {n ka kb kc : ℕ} (i : Fin n) :
    slot ka kb kc i = 2 ↔ ka + kb ≤ i.val ∧ i.val < ka + kb + kc := by
  by_cases ha : i.val < ka
  · simp [slot, ha, show ¬ ka + kb ≤ i.val by omega]
  · by_cases hb : i.val < ka + kb <;> by_cases hc : i.val < ka + kb + kc <;>
      simp [slot, ha, hb, hc, ← Nat.not_lt]

private theorem slot3 {n ka kb kc : ℕ} (i : Fin n) :
    slot ka kb kc i = 3 ↔ ka + kb + kc ≤ i.val := by
  by_cases ha : i.val < ka
  · simp [slot, ha, show ¬ ka + kb + kc ≤ i.val by omega]
  · by_cases hb : i.val < ka + kb
    · simp [slot, ha, hb, show ¬ ka + kb + kc ≤ i.val by omega]
    · by_cases hc : i.val < ka + kb + kc <;> simp [slot, ha, hb, hc, ← Nat.not_lt]

private theorem card_interval {n : ℕ} (start len : ℕ) (fits : start + len ≤ n)
    (S : Finset (Fin n)) (mem : ∀ i : Fin n, i ∈ S ↔ start ≤ i.val ∧ i.val < start + len) :
    S.card = len := by
  let shift : Fin len ↪ Fin n :=
    ⟨fun i => ⟨start + i.val, by have := i.isLt; omega⟩,
      fun a b h => Fin.ext (by have hval := congrArg Fin.val h; dsimp at hval; omega)⟩
  have same : S = Finset.univ.map shift := by
    ext i
    rw [mem, Finset.mem_map]
    constructor
    · rintro ⟨hs, he⟩
      have bound : i.val - start < len := by omega
      refine ⟨⟨i.val - start, bound⟩, Finset.mem_univ _, Fin.ext ?_⟩
      change start + (i.val - start) = i.val
      omega
    · rintro ⟨j, _, rfl⟩
      have bound := j.isLt
      change start ≤ start + j.val ∧ start + j.val < start + len
      omega
  rw [same, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem result (ka kb kc kd s : ℕ) (ha : 1 ≤ ka) (hb : 1 ≤ kb) (hc : 1 ≤ kc) (hd : 1 ≤ kd)
    (f : (Fin (ka + kb + kc + kd) → Bool) → Bool)
    (transfer : ∀ x, f x = goal (slot ka kb kc) x) :
    HasLeafSize (ka + kb + kc + kd) f s ↔ ka + kb + kc + kd + min kb kc ≤ s := by
  let n := ka + kb + kc + kd
  let part : Fin n → Fin 4 := slot ka kb kc
  have a : (fibre part 0).card = ka := card_interval 0 ka (by dsimp [n]; omega) _ (by
    intro i
    simp [fibre, part, slot0])
  have b : (fibre part 1).card = kb := card_interval ka kb (by dsimp [n]; omega) _ (by
    intro i
    simp [fibre, part, slot1])
  have c : (fibre part 2).card = kc := card_interval (ka + kb) kc (by dsimp [n]; omega) _ (by
    intro i
    simp [fibre, part, slot2])
  have d : (fibre part 3).card = kd := card_interval (ka + kb + kc) kd (le_refl n) _ (by
    intro i
    have ilt : i.val < ka + kb + kc + kd := i.isLt
    simp [fibre, part, slot3, ilt])
  have surj : Function.Surjective part := by
    intro k
    fin_cases k
    · exact ⟨⟨0, by dsimp [n]; omega⟩, (slot0 _).mpr (by dsimp [n]; omega)⟩
    · exact ⟨⟨ka, by dsimp [n]; omega⟩, (slot1 _).mpr ⟨le_rfl, by change ka < ka + kb; omega⟩⟩
    · exact ⟨⟨ka+kb, by dsimp [n]; omega⟩, (slot2 _).mpr ⟨le_rfl, by change ka + kb < ka + kb + kc; omega⟩⟩
    · exact ⟨⟨ka+kb+kc, by dsimp [n]; omega⟩, (slot3 _).mpr le_rfl⟩
  constructor
  · rintro ⟨F, hs, hf⟩
    have low := (lower_bound part surj F (fun x => (hf x).trans (transfer x))).trans hs
    simpa only [n, b, c] using low
  · intro hs
    obtain ⟨F, hle, hh⟩ := upper_bound part surj
    have size : F.leaves ≤ ka + kb + kc + kd + min kb kc := by simpa only [a,b,c,d] using hle
    exact ⟨F, size.trans hs, fun x => (hh x).trans (transfer x).symm⟩

end PEqualNP.Outside.L_meta_145_aux

open PEqualNP.Outside.L_meta_145_aux in
theorem PEqualNP.Outside.L_meta_145 :
    ∀ (ka kb kc kd s : ℕ), 1 ≤ ka → 1 ≤ kb → 1 ≤ kc → 1 ≤ kd → (PEqualNP.MetaComplexity.HasLeafSize (ka + kb + kc + kd) (fun x : Fin (ka + kb + kc + kd) → Bool => decide (((∃ i : Fin (ka + kb + kc + kd), i.val < ka ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true)) ∨ ((∃ i : Fin (ka + kb + kc + kd), ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true)) ∨ ((∃ i : Fin (ka + kb + kc + kd), ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka + kb + kc ≤ i.val ∧ x i = true)))) s ↔ ka + kb + kc + kd + min kb kc ≤ s) := by
  intro ka kb kc kd s ha hb hc hd
  apply result ka kb kc kd s ha hb hc hd
  intro x
  apply Bool.eq_iff_iff.mpr
  simp [goal, path, hit, slot0, slot1, slot2, slot3, or_assoc, and_assoc]
