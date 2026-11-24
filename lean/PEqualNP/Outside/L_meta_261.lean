import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_261_aux

open PEqualNP.MetaComplexity

def revl {n : ℕ} : Bool ⊕ DMFormula n → (Fin n → Bool) → Bool
  | Sum.inl b, _ => b
  | Sum.inr ψ, x => ψ.eval x

def rcost {n : ℕ} : Bool ⊕ DMFormula n → ℕ
  | Sum.inl _ => 0
  | Sum.inr ψ => ψ.leaves

theorem revl_inr {n : ℕ} (ψ : DMFormula n) (x : Fin n → Bool) :
    revl (Sum.inr ψ) x = ψ.eval x := rfl

theorem rcost_inr {n : ℕ} (ψ : DMFormula n) : rcost (Sum.inr ψ) = ψ.leaves := rfl

def sAnd {n : ℕ} : Bool ⊕ DMFormula n → Bool ⊕ DMFormula n → Bool ⊕ DMFormula n
  | Sum.inl false, _ => Sum.inl false
  | Sum.inl true, r => r
  | Sum.inr a, Sum.inl true => Sum.inr a
  | Sum.inr _, Sum.inl false => Sum.inl false
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.and a b)

def sOr {n : ℕ} : Bool ⊕ DMFormula n → Bool ⊕ DMFormula n → Bool ⊕ DMFormula n
  | Sum.inl true, _ => Sum.inl true
  | Sum.inl false, r => r
  | Sum.inr a, Sum.inl false => Sum.inr a
  | Sum.inr _, Sum.inl true => Sum.inl true
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.or a b)

theorem revl_sAnd {n : ℕ} (r s : Bool ⊕ DMFormula n) (x : Fin n → Bool) :
    revl (sAnd r s) x = (revl r x && revl s x) := by
  rcases r with c | a <;> rcases s with d | b <;> (try cases c) <;> (try cases d) <;>
    simp [sAnd, revl, DMFormula.eval]

theorem revl_sOr {n : ℕ} (r s : Bool ⊕ DMFormula n) (x : Fin n → Bool) :
    revl (sOr r s) x = (revl r x || revl s x) := by
  rcases r with c | a <;> rcases s with d | b <;> (try cases c) <;> (try cases d) <;>
    simp [sOr, revl, DMFormula.eval]

theorem rcost_sAnd {n : ℕ} (r s : Bool ⊕ DMFormula n) :
    rcost (sAnd r s) ≤ rcost r + rcost s := by
  rcases r with c | a <;> rcases s with d | b <;> (try cases c) <;> (try cases d) <;>
    simp [sAnd, rcost, DMFormula.leaves]

theorem rcost_sOr {n : ℕ} (r s : Bool ⊕ DMFormula n) :
    rcost (sOr r s) ≤ rcost r + rcost s := by
  rcases r with c | a <;> rcases s with d | b <;> (try cases c) <;> (try cases d) <;>
    simp [sOr, rcost, DMFormula.leaves]

def cnt {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | DMFormula.lit j _ => if j = i then 1 else 0
  | DMFormula.and a b => cnt i a + cnt i b
  | DMFormula.or a b => cnt i a + cnt i b

def restr {n : ℕ} (i : Fin n) (c : Bool) : DMFormula n → Bool ⊕ DMFormula n
  | DMFormula.lit j b =>
    if j = i then Sum.inl (if b then c else !c) else Sum.inr (DMFormula.lit j b)
  | DMFormula.and a b => sAnd (restr i c a) (restr i c b)
  | DMFormula.or a b => sOr (restr i c a) (restr i c b)

theorem restr_ev {n : ℕ} (i : Fin n) (c : Bool) (φ : DMFormula n) (x : Fin n → Bool)
    (h : x i = c) : revl (restr i c φ) x = φ.eval x := by
  induction φ with
  | lit j b =>
    by_cases hj : j = i
    · subst hj
      cases b <;> simp [restr, revl, DMFormula.eval, h]
    · simp [restr, hj, revl]
  | and a b iha ihb => simp [restr, revl_sAnd, iha, ihb, DMFormula.eval]
  | or a b iha ihb => simp [restr, revl_sOr, iha, ihb, DMFormula.eval]

theorem restr_cost {n : ℕ} (i : Fin n) (c : Bool) (φ : DMFormula n) :
    rcost (restr i c φ) + cnt i φ ≤ φ.leaves := by
  induction φ with
  | lit j b =>
    by_cases hj : j = i
    · simp [restr, cnt, rcost, hj, DMFormula.leaves]
    · simp [restr, cnt, rcost, hj, DMFormula.leaves]
  | and a b iha ihb =>
    have h1 := rcost_sAnd (restr i c a) (restr i c b)
    simp only [restr, cnt, DMFormula.leaves]
    omega
  | or a b iha ihb =>
    have h1 := rcost_sOr (restr i c a) (restr i c b)
    simp only [restr, cnt, DMFormula.leaves]
    omega

theorem cnt_eq {n : ℕ} (i : Fin n) (B : DMFormula n) :
    DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0)
      (fun _ _ p q => p + q) (fun _ _ p q => p + q) B = cnt i B := by
  induction B with
  | lit j b => rfl
  | and a b iha ihb =>
    rw [cnt, ← iha, ← ihb]
  | or a b iha ihb =>
    rw [cnt, ← iha, ← ihb]

theorem lit_ev {n : ℕ} (j : Fin n) (b : Bool) (x : Fin n → Bool) :
    (DMFormula.lit j b).eval x = (x j == b) := by
  cases b <;> cases h : x j <;> simp [DMFormula.eval, h]

end PEqualNP.Outside.L_meta_261_aux

theorem PEqualNP.Outside.L_meta_261 : ∀ (n : ℕ) (φ : PEqualNP.MetaComplexity.DMFormula n), (∃ x y : Fin n → Bool, φ.eval x ≠ φ.eval y) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (_ : Fin n) (_ : Bool) => False) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) φ → ∃ ψ : PEqualNP.MetaComplexity.DMFormula n, ψ.leaves < φ.leaves ∧ ∀ x : Fin n → Bool, ψ.eval x = φ.eval x := by
  intro n φ hnc hP
  open PEqualNP.Outside.L_meta_261_aux PEqualNP.MetaComplexity in
  suffices key : ∃ R : Bool ⊕ DMFormula n, rcost R < φ.leaves ∧ ∀ x, revl R x = φ.eval x by
    obtain ⟨R, hc, he⟩ := key
    rcases R with b | ψ
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      rw [← he x, ← he y]
      rfl
    · exact ⟨ψ, hc, he⟩
  clear hnc
  open PEqualNP.Outside.L_meta_261_aux PEqualNP.MetaComplexity in
  induction φ with
  | lit j b => exact hP.elim
  | and A B ihA ihB =>
    rcases hP with hA | hB | ⟨i, hAi, hcnt⟩ | ⟨i, hBi, hcnt⟩
    · obtain ⟨R, hc, he⟩ := ihA hA
      refine ⟨sAnd R (Sum.inr B), ?_, ?_⟩
      · have h1 := rcost_sAnd R (Sum.inr B)
        simp only [rcost_inr, DMFormula.leaves] at h1 ⊢
        omega
      · intro x
        rw [revl_sAnd, he]
        rfl
    · obtain ⟨R, hc, he⟩ := ihB hB
      refine ⟨sAnd (Sum.inr A) R, ?_, ?_⟩
      · have h1 := rcost_sAnd (Sum.inr A) R
        simp only [rcost_inr, DMFormula.leaves] at h1 ⊢
        omega
      · intro x
        rw [revl_sAnd, he]
        rfl
    · cases A with
      | lit j b =>
        change j = i at hAi
        subst hAi
        rw [cnt_eq] at hcnt
        refine ⟨sAnd (Sum.inr (DMFormula.lit j b)) (restr j b B), ?_, ?_⟩
        · have h1 := rcost_sAnd (Sum.inr (DMFormula.lit j b)) (restr j b B)
          have h2 := restr_cost j b B
          simp only [rcost_inr, DMFormula.leaves] at h1 h2 ⊢
          omega
        · intro x
          rw [revl_sAnd]
          simp only [revl_inr, DMFormula.eval]
          by_cases hx : x j = b
          · rw [restr_ev j b B x hx]
          · have hl : (DMFormula.lit j b).eval x = false := by
              rw [lit_ev]; simpa using hx
            simp only [DMFormula.eval] at hl
            rw [hl]
            rfl
      | and _ _ => exact hAi.elim
      | or _ _ => exact hAi.elim
    · cases B with
      | lit j b =>
        change j = i at hBi
        subst hBi
        rw [cnt_eq] at hcnt
        refine ⟨sAnd (restr j b A) (Sum.inr (DMFormula.lit j b)), ?_, ?_⟩
        · have h1 := rcost_sAnd (restr j b A) (Sum.inr (DMFormula.lit j b))
          have h2 := restr_cost j b A
          simp only [rcost_inr, DMFormula.leaves] at h1 h2 ⊢
          omega
        · intro x
          rw [revl_sAnd]
          simp only [revl_inr, DMFormula.eval]
          by_cases hx : x j = b
          · rw [restr_ev j b A x hx]
          · have hl : (DMFormula.lit j b).eval x = false := by
              rw [lit_ev]; simpa using hx
            simp only [DMFormula.eval] at hl
            rw [hl]
            simp
      | and _ _ => exact hBi.elim
      | or _ _ => exact hBi.elim
  | or A B ihA ihB =>
    rcases hP with hA | hB | ⟨i, hAi, hcnt⟩ | ⟨i, hBi, hcnt⟩
    · obtain ⟨R, hc, he⟩ := ihA hA
      refine ⟨sOr R (Sum.inr B), ?_, ?_⟩
      · have h1 := rcost_sOr R (Sum.inr B)
        simp only [rcost_inr, DMFormula.leaves] at h1 ⊢
        omega
      · intro x
        rw [revl_sOr, he]
        rfl
    · obtain ⟨R, hc, he⟩ := ihB hB
      refine ⟨sOr (Sum.inr A) R, ?_, ?_⟩
      · have h1 := rcost_sOr (Sum.inr A) R
        simp only [rcost_inr, DMFormula.leaves] at h1 ⊢
        omega
      · intro x
        rw [revl_sOr, he]
        rfl
    · cases A with
      | lit j b =>
        change j = i at hAi
        subst hAi
        rw [cnt_eq] at hcnt
        refine ⟨sOr (Sum.inr (DMFormula.lit j b)) (restr j (!b) B), ?_, ?_⟩
        · have h1 := rcost_sOr (Sum.inr (DMFormula.lit j b)) (restr j (!b) B)
          have h2 := restr_cost j (!b) B
          simp only [rcost_inr, DMFormula.leaves] at h1 h2 ⊢
          omega
        · intro x
          rw [revl_sOr]
          simp only [revl_inr, DMFormula.eval]
          by_cases hx : x j = !b
          · rw [restr_ev j (!b) B x hx]
          · have hl : (DMFormula.lit j b).eval x = true := by
              rw [lit_ev]; cases b <;> simp_all
            simp only [DMFormula.eval] at hl
            rw [hl]
            rfl
      | and _ _ => exact hAi.elim
      | or _ _ => exact hAi.elim
    · cases B with
      | lit j b =>
        change j = i at hBi
        subst hBi
        rw [cnt_eq] at hcnt
        refine ⟨sOr (restr j (!b) A) (Sum.inr (DMFormula.lit j b)), ?_, ?_⟩
        · have h1 := rcost_sOr (restr j (!b) A) (Sum.inr (DMFormula.lit j b))
          have h2 := restr_cost j (!b) A
          simp only [rcost_inr, DMFormula.leaves] at h1 h2 ⊢
          omega
        · intro x
          rw [revl_sOr]
          simp only [revl_inr, DMFormula.eval]
          by_cases hx : x j = !b
          · rw [restr_ev j (!b) A x hx]
          · have hl : (DMFormula.lit j b).eval x = true := by
              rw [lit_ev]; cases b <;> simp_all
            simp only [DMFormula.eval] at hl
            rw [hl]
            simp
      | and _ _ => exact hBi.elim
      | or _ _ => exact hBi.elim
