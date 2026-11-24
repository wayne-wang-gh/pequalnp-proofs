import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_122

def step {n : ℕ} (i : Fin n) (k : ℕ) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

lemma step_zero {n : ℕ} (i : Fin n) : step i 0 = i := by
  apply Fin.ext
  simp [step, Nat.mod_eq_of_lt i.isLt]

lemma step_add {n : ℕ} (i : Fin n) (k l : ℕ) :
    step (step i k) l = step i (k + l) := by
  apply Fin.ext
  simp [step, Nat.add_assoc]

lemma step_ne {n : ℕ} (i : Fin n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (hne : a ≠ b) : step i a ≠ step i b := by
  intro h
  have e : i.val + a ≡ i.val + b [MOD n] := congrArg Fin.val h
  exact hne ((e.add_left_cancel' i.val).eq_of_lt_of_lt ha hb)

lemma windowDistinct {n : ℕ} (hn : 5 ≤ n) (i : Fin n) :
    i ≠ step i 1 ∧ i ≠ step i 2 ∧ i ≠ step i 3 ∧
    step i 1 ≠ step i 2 ∧ step i 1 ≠ step i 3 ∧ step i 2 ≠ step i 3 := by
  have h (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (h : a ≠ b) : step i a ≠ step i b :=
    step_ne i (by omega) (by omega) h
  exact ⟨by simpa [step_zero] using h 0 1 (by decide) (by decide) (by decide),
    by simpa [step_zero] using h 0 2 (by decide) (by decide) (by decide),
    by simpa [step_zero] using h 0 3 (by decide) (by decide) (by decide),
    h 1 2 (by decide) (by decide) (by decide), h 1 3 (by decide) (by decide) (by decide),
    h 2 3 (by decide) (by decide) (by decide)⟩

lemma windowEval {n : ℕ} (hn : 5 ≤ n) (i : Fin n) (x : Fin n → Bool)
    (hx : ∀ v, v ≠ i → v ≠ step i 1 → v ≠ step i 2 → v ≠ step i 3 → x v = false) :
    decide (∃ u v : Fin n, (u.val + 1) % n = v.val ∧ x u = true ∧ x v = true) =
      ((x i && x (step i 1)) || (x (step i 1) && x (step i 2)) ||
        (x (step i 2) && x (step i 3))) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff, Bool.or_eq_true, Bool.and_eq_true]
  have nextEq (a : ℕ) : ((step i a).val + 1) % n = (step i (a + 1)).val :=
    congrArg Fin.val (step_add i a 1)
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have he : v = step u 1 := Fin.ext huv.symm
    subst v
    by_cases h0 : u = i
    · subst u
      exact Or.inl (Or.inl ⟨hu, hv⟩)
    by_cases h1 : u = step i 1
    · subst u
      rw [step_add] at hv
      exact Or.inl (Or.inr ⟨hu, hv⟩)
    by_cases h2 : u = step i 2
    · subst u
      rw [step_add] at hv
      exact Or.inr ⟨hu, hv⟩
    by_cases h3 : u = step i 3
    · subst u
      have h (k : ℕ) (hk : k ≤ 3) : step i 4 ≠ step i k :=
        step_ne i (by omega) (by omega) (by omega)
      have hf := hx (step i 4) (by simpa [step_zero] using h 0 (by decide))
        (h 1 (by decide)) (h 2 (by decide)) (h 3 (by decide))
      rw [step_add] at hv
      exact absurd hv (by simpa only [hf] using Bool.false_ne_true)
    exact absurd hu (by simp [hx u h0 h1 h2 h3])
  · rintro ((⟨h0, h1⟩ | ⟨h1, h2⟩) | ⟨h2, h3⟩)
    · exact ⟨i, step i 1, rfl, h0, h1⟩
    · exact ⟨step i 1, step i 2, nextEq 1, h1, h2⟩
    · exact ⟨step i 2, step i 3, nextEq 2, h2, h3⟩

def wire {n : ℕ} (l a b r j : Fin n) : BitVec 8 :=
  if j = a then 170 else if j = b then 204 else if j = l ∨ j = r then 240 else 0

def table {n : ℕ} (l a b r : Fin n) : DMFormula n → BitVec 8
  | .lit j s => if s then wire l a b r j else ~~~(wire l a b r j)
  | .and p q => table l a b r p &&& table l a b r q
  | .or p q => table l a b r p ||| table l a b r q

lemma bit_table {n : ℕ} (l a b r : Fin n) (p : DMFormula n) (i : ℕ) (hi : i < 8) :
    (table l a b r p).getLsbD i = p.eval (fun j => (wire l a b r j).getLsbD i) := by
  induction p with
  | lit j s => cases s <;> simp [table, DMFormula.eval, hi]
  | and p q pIH qIH => simp [table, DMFormula.eval, pIH, qIH]
  | or p q pIH qIH => simp [table, DMFormula.eval, pIH, qIH]

def occ {n : ℕ} : DMFormula n → Fin n → ℕ
  | .lit j _, i => if j = i then 1 else 0
  | .and p q, i => occ p i + occ q i
  | .or p q, i => occ p i + occ q i

def cost {n : ℕ} (a b : Fin n) (p : DMFormula n) : ℕ :=
  occ p a + occ p b

def allowed : ℕ → List (BitVec 8)
  | 0 => [0, 15, 240, 255]
  | 1 => [0, 3, 5, 10, 12, 15, 48, 51, 63, 80, 85, 95, 160, 170, 175, 192, 204, 207, 240, 243, 245, 250, 252, 255]
  | _ => [0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 31, 32, 34, 35, 42, 47, 48, 49, 50, 51, 53, 55, 58, 59, 60, 63, 64, 68, 69, 76, 79, 80, 81, 83, 84, 85, 87, 90, 92, 93, 95, 112, 115, 117, 119, 127, 128, 136, 138, 140, 143, 160, 162, 163, 165, 168, 170, 171, 172, 174, 175, 176, 179, 186, 187, 191, 192, 195, 196, 197, 200, 202, 204, 205, 206, 207, 208, 213, 220, 221, 223, 224, 234, 236, 238, 239, 240, 241, 242, 243, 244, 245, 247, 248, 250, 251, 252, 253, 254, 255]

def combines (i j : ℕ) : Bool :=
  (allowed i).all fun x => (allowed j).all fun y =>
    (allowed (i+j)).contains (x &&& y) && (allowed (i+j)).contains (x ||| y)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
lemma closure : ∀ i j : Fin 3, i.val+j.val ≤ 2 → combines i j = true := by decide

lemma combine {i j : ℕ} (h : i+j ≤ 2) (x y : BitVec 8)
    (hx : x ∈ allowed i) (hy : y ∈ allowed j) :
    (x &&& y) ∈ allowed (i+j) ∧ (x ||| y) ∈ allowed (i+j) := by
  have hc := closure ⟨i, by omega⟩ ⟨j, by omega⟩ h
  change (allowed i).all _ = true at hc
  have hxy := List.all_eq_true.mp (List.all_eq_true.mp hc x hx) y hy
  simpa using hxy

lemma in_allowed {n : ℕ} (l a b r : Fin n) (hab : a ≠ b) (p : DMFormula n)
    (h : cost a b p ≤ 2) : table l a b r p ∈ allowed (cost a b p) := by
  induction p with
  | lit j s =>
    by_cases hja : j = a
    · subst j
      cases s <;> simp [cost, occ, table, wire, hab, allowed]
    · by_cases hjb : j = b
      · subst j
        cases s <;> simp [cost, occ, table, wire, hja, allowed]
      · cases s <;> simp [cost, occ, table, wire, hja, hjb]
        all_goals split <;> decide
  | and p q pIH qIH =>
    have he : cost a b (.and p q) = cost a b p + cost a b q := by
      simp [cost, occ, Nat.add_add_add_comm]
    rw [he] at h ⊢
    exact (combine h _ _ (pIH (by omega)) (qIH (by omega))).1
  | or p q pIH qIH =>
    have he : cost a b (.or p q) = cost a b p + cost a b q := by
      simp [cost, occ, Nat.add_add_add_comm]
    rw [he] at h ⊢
    exact (combine h _ _ (pIH (by omega)) (qIH (by omega))).2

lemma excludesMajority : ∀ i : Fin 3, (232 : BitVec 8) ∉ allowed i := by decide

lemma middle_three {n : ℕ} (p : DMFormula n) (l a b r : Fin n)
    (hla : l ≠ a) (hlb : l ≠ b) (har : a ≠ r) (hbr : b ≠ r) (hab : a ≠ b)
    (h : ∀ x : Fin n → Bool,
      (∀ j, j ≠ l → j ≠ a → j ≠ b → j ≠ r → x j = false) →
      p.eval x = ((x l && x a) || (x a && x b) || (x b && x r))) :
    3 ≤ occ p a + occ p b := by
  change 3 ≤ cost a b p
  by_contra! hsmall
  have hmem := in_allowed l a b r hab p (by omega)
  have ht : table l a b r p = 232 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [bit_table l a b r p i hi, h]
    · simp [wire, hla, hlb, Ne.symm har, Ne.symm hbr, Ne.symm hab]
      interval_cases i <;> decide
    · intro j hjl hja hjb hjr
      simp [wire, hjl, hja, hjb, hjr]
  rw [ht] at hmem
  exact excludesMajority ⟨cost a b p, by omega⟩ hmem

lemma sum_occ {n : ℕ} (p : DMFormula n) :
    (∑ i : Fin n, occ p i) = p.leaves := by
  induction p with
  | lit j b => simp [occ, DMFormula.leaves]
  | and p q hp hq => simp [occ, DMFormula.leaves, Finset.sum_add_distrib, hp, hq]
  | or p q hp hq => simp [occ, DMFormula.leaves, Finset.sum_add_distrib, hp, hq]

lemma sum_shift {n : ℕ} (k : ℕ) (hk : k < n) (f : Fin n → ℕ) :
    (∑ i : Fin n, f (step i k)) = ∑ i : Fin n, f i := by
  have : NeZero n := ⟨by omega⟩
  exact Fintype.sum_equiv (Equiv.addRight (⟨k, hk⟩ : Fin n)) _ f (fun _ => rfl)

lemma leaves_from_pairs {n : ℕ} (hn : 5 ≤ n) (p : DMFormula n)
    (h : ∀ i : Fin n, 3 ≤ occ p (step i 1) + occ p (step i 2)) :
    n + (n + 1) / 2 ≤ p.leaves := by
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i _ => h i)
  rw [Finset.sum_add_distrib, sum_shift 1 (by omega), sum_shift 2 (by omega), sum_occ] at total
  have bound : n * 3 ≤ p.leaves + p.leaves := by simpa using total
  omega

def cycleIndex {n : ℕ} (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

def cycleLiteral {n : ℕ} (hn : 0 < n) (i : ℕ) : DMFormula n :=
  .lit (cycleIndex hn i) true

def cycleStar {n : ℕ} (hn : 0 < n) (k : ℕ) : DMFormula n :=
  .and (cycleLiteral hn (2 * k + 1))
    (.or (cycleLiteral hn (2 * k)) (cycleLiteral hn (2 * k + 2)))

def cycleStars {n : ℕ} (hn : 0 < n) : ℕ → DMFormula n
  | 0 => cycleStar hn 0
  | k + 1 => .or (cycleStars hn k) (cycleStar hn (k + 1))

lemma cycleStars_leaves {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (cycleStars hn k).leaves = 3 * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [cycleStars, cycleStar, cycleLiteral, DMFormula.leaves, ih]
    omega

lemma cycleStar_eval {n : ℕ} (hn : 0 < n) (k : ℕ) (x : Fin n → Bool) :
    (cycleStar hn k).eval x = true ↔
      ∃ e, 2 * k ≤ e ∧ e < 2 * (k + 1) ∧
        x (cycleIndex hn e) = true ∧ x (cycleIndex hn (e + 1)) = true := by
  simp only [cycleStar, cycleLiteral, DMFormula.eval, ite_true, Bool.and_eq_true,
    Bool.or_eq_true]
  constructor
  · rintro ⟨hc, hl | hr⟩
    · exact ⟨2 * k, by omega, by omega, hl, hc⟩
    · refine ⟨2 * k + 1, by omega, by omega, hc, ?_⟩
      simpa only [Nat.add_assoc] using hr
  · rintro ⟨e, hlo, hhi, ha, hb⟩
    have he : e = 2 * k ∨ e = 2 * k + 1 := by omega
    rcases he with he | he <;> subst e
    · exact ⟨hb, Or.inl ha⟩
    · exact ⟨ha, Or.inr (by simpa only [Nat.add_assoc] using hb)⟩

lemma cycleStars_eval {n : ℕ} (hn : 0 < n) (k : ℕ) (x : Fin n → Bool) :
    (cycleStars hn k).eval x = true ↔
      ∃ e, e < 2 * (k + 1) ∧
        x (cycleIndex hn e) = true ∧ x (cycleIndex hn (e + 1)) = true := by
  induction k with
  | zero => simp only [cycleStars, cycleStar_eval, Nat.mul_zero, Nat.zero_le, true_and]
  | succ k ih =>
    simp only [cycleStars, DMFormula.eval, Bool.or_eq_true, ih, cycleStar_eval]
    constructor
    · rintro (⟨e, he, ha, hb⟩ | ⟨e, hlo, hhi, ha, hb⟩)
      · exact ⟨e, by omega, ha, hb⟩
      · exact ⟨e, hhi, ha, hb⟩
    · rintro ⟨e, he, ha, hb⟩
      by_cases h : e < 2 * (k + 1)
      · exact Or.inl ⟨e, h, ha, hb⟩
      · exact Or.inr ⟨e, by omega, he, ha, hb⟩

lemma cycleEdge_exists {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (∃ e, e < n ∧ x (cycleIndex hn e) = true ∧ x (cycleIndex hn (e + 1)) = true) ↔
      ∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true := by
  constructor
  · rintro ⟨e, he, ha, hb⟩
    exact ⟨cycleIndex hn e, cycleIndex hn (e + 1),
      by simp only [cycleIndex, Nat.mod_eq_of_lt he], ha, hb⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have h₁ : cycleIndex hn i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    have h₂ : cycleIndex hn (i.val + 1) = j := Fin.ext hij
    exact ⟨i.val, i.isLt, by simpa only [h₁] using hi, by simpa only [h₂] using hj⟩

lemma cycle_upper (n s : ℕ) (hn : 5 ≤ n) (hs : n + (n + 1) / 2 ≤ s) :
    HasLeafSize n (fun x : Fin n → Bool => decide
      (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s := by
  have hn' : 0 < n := by omega
  let k := n / 2 - 1
  have parity : n = 2 * (k + 1) ∨ n = 2 * (k + 1) + 1 := by
    dsimp [k]
    omega
  rcases parity with even | odd
  · refine ⟨cycleStars hn' k, ?_, ?_⟩
    · rw [cycleStars_leaves]
      omega
    · intro x
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, ← cycleEdge_exists hn', cycleStars_eval]
      simp only [← even]
  · refine ⟨.or (cycleStars hn' k)
        (.and (cycleLiteral hn' (2 * (k + 1))) (cycleLiteral hn' (2 * (k + 1) + 1))),
      ?_, ?_⟩
    · simp only [DMFormula.leaves, cycleStars_leaves, cycleLiteral]
      omega
    · intro x
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, ← cycleEdge_exists hn']
      simp only [DMFormula.eval, Bool.or_eq_true, Bool.and_eq_true, cycleStars_eval,
        cycleLiteral, ite_true]
      constructor
      · rintro (⟨e, he, ha, hb⟩ | ⟨ha, hb⟩)
        · exact ⟨e, by omega, ha, hb⟩
        · exact ⟨2 * (k + 1), by omega, ha, hb⟩
      · rintro ⟨e, he, ha, hb⟩
        by_cases h : e < 2 * (k + 1)
        · exact Or.inl ⟨e, h, ha, hb⟩
        · have he' : e = 2 * (k + 1) := by omega
          subst e
          exact Or.inr ⟨ha, hb⟩

lemma cycle_lower (n s : ℕ) (hn : 5 ≤ n)
    (h : HasLeafSize n (fun x : Fin n → Bool => decide
      (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s) :
    n + (n + 1) / 2 ≤ s := by
  obtain ⟨p, hsize, heval⟩ := h
  apply Nat.le_trans (leaves_from_pairs hn p ?_) hsize
  intro i
  obtain ⟨hla, hlb, _, hab, har, hbr⟩ := windowDistinct hn i
  apply middle_three p i (step i 1) (step i 2) (step i 3) hla hlb har hbr hab
  intro x hx
  exact (heval x).trans (windowEval hn i x hx)

end PEqualNP.Outside.L_meta_122

theorem PEqualNP.Outside.L_meta_122 : ∀ n s : ℕ, 5 ≤ n → (PEqualNP.MetaComplexity.HasLeafSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s ↔ n + (n + 1) / 2 ≤ s) := by
  intro n s hn
  exact ⟨PEqualNP.Outside.L_meta_122.cycle_lower n s hn,
    PEqualNP.Outside.L_meta_122.cycle_upper n s hn⟩
