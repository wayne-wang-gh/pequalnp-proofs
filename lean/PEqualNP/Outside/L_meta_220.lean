import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_220

open PEqualNP.MetaComplexity

def cvar {α : Type} (L : ℕ) (v1 v2 : ℕ → α) (k : ℕ) : α := if k < L then v1 k else v2 (k - L)

lemma cvar_lt {α : Type} (L : ℕ) (v1 v2 : ℕ → α) (k : ℕ) (h : k < L) :
    cvar L v1 v2 k = v1 k := by
  simp [cvar, h]

lemma cvar_add {α : Type} (L : ℕ) (v1 v2 : ℕ → α) (k : ℕ) :
    cvar L v1 v2 (L + k) = v2 k := by
  simp [cvar]

lemma own_exists {n : ℕ} (φ : DMFormula n) :
    ∃ (own : (Fin n → Bool) → (Fin n → Bool) → ℕ) (var : ℕ → Fin n) (pol : ℕ → Bool),
      (∀ s t, φ.eval s = true → φ.eval t = false →
        own s t < φ.leaves ∧ s (var (own s t)) = pol (own s t) ∧
          t (var (own s t)) = !(pol (own s t))) ∧
      (∀ s t s' t', φ.eval s = true → φ.eval t = false → φ.eval s' = true →
        φ.eval t' = false → own s t = own s' t' → own s t' = own s t) := by
  induction φ with
  | lit i c =>
    refine ⟨fun _ _ => 0, fun _ => i, fun _ => c, ?_, ?_⟩
    · intro s t hs ht
      cases c with
      | true =>
        simp only [DMFormula.eval, ↓reduceIte, Bool.not_true] at hs ht ⊢
        exact ⟨by simp [DMFormula.leaves], hs, ht⟩
      | false =>
        simp only [DMFormula.eval, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true',
          Bool.not_eq_false', Bool.not_false] at hs ht ⊢
        exact ⟨by simp [DMFormula.leaves], hs, ht⟩
    · intro _ _ _ _ _ _ _ _ _
      rfl
  | and φ ψ ih1 ih2 =>
    obtain ⟨o1, v1, p1, a1, r1⟩ := ih1
    obtain ⟨o2, v2, p2, a2, r2⟩ := ih2
    have key : ∀ s t, (DMFormula.and φ ψ).eval s = true → (DMFormula.and φ ψ).eval t = false →
        φ.eval s = true ∧ ψ.eval s = true ∧ (φ.eval t = false ∨ (φ.eval t = true ∧ ψ.eval t = false)) := by
      intro s t hs ht
      simp only [DMFormula.eval, Bool.and_eq_true] at hs
      simp only [DMFormula.eval, Bool.and_eq_false_iff] at ht
      refine ⟨hs.1, hs.2, ?_⟩
      by_cases h : φ.eval t = false
      · exact Or.inl h
      · rcases ht with ht | ht
        · exact absurd ht h
        · exact Or.inr ⟨by simpa using h, ht⟩
    refine ⟨fun s t => if φ.eval t = true then φ.leaves + o2 s t else o1 s t,
      cvar φ.leaves v1 v2, cvar φ.leaves p1 p2, ?_, ?_⟩
    · intro s t hs ht
      obtain ⟨hs1, hs2, hc⟩ := key s t hs ht
      rcases hc with h | ⟨h, h'⟩
      · obtain ⟨b1, b2, b3⟩ := a1 s t hs1 h
        simp only [h, Bool.false_eq_true, ↓reduceIte, DMFormula.leaves]
        rw [cvar_lt _ _ _ _ b1, cvar_lt _ _ _ _ b1]
        exact ⟨by omega, b2, b3⟩
      · obtain ⟨b1, b2, b3⟩ := a2 s t hs2 h'
        simp only [h, ↓reduceIte, DMFormula.leaves]
        rw [cvar_add, cvar_add]
        exact ⟨by omega, b2, b3⟩
    · intro s t s' t' hs ht hs' ht' he
      obtain ⟨hs1, hs2, hc⟩ := key s t hs ht
      obtain ⟨hs1', hs2', hc'⟩ := key s' t' hs' ht'
      rcases hc with h | ⟨h, h2⟩ <;> rcases hc' with h' | ⟨h', h2'⟩
      · simp only [h, h', Bool.false_eq_true, ↓reduceIte] at he ⊢
        exact r1 s t s' t' hs1 h hs1' h' he
      · simp only [h, h', Bool.false_eq_true, ↓reduceIte] at he
        have := (a1 s t hs1 h).1
        omega
      · simp only [h, h', Bool.false_eq_true, ↓reduceIte] at he
        have := (a1 s' t' hs1' h').1
        omega
      · simp only [h, h', ↓reduceIte] at he ⊢
        have he' : o2 s t = o2 s' t' := by omega
        rw [r2 s t s' t' hs2 h2 hs2' h2' he']
  | or φ ψ ih1 ih2 =>
    obtain ⟨o1, v1, p1, a1, r1⟩ := ih1
    obtain ⟨o2, v2, p2, a2, r2⟩ := ih2
    have key : ∀ s t, (DMFormula.or φ ψ).eval s = true → (DMFormula.or φ ψ).eval t = false →
        φ.eval t = false ∧ ψ.eval t = false ∧ (φ.eval s = true ∨ (φ.eval s = false ∧ ψ.eval s = true)) := by
      intro s t hs ht
      simp only [DMFormula.eval, Bool.or_eq_true] at hs
      simp only [DMFormula.eval, Bool.or_eq_false_iff] at ht
      refine ⟨ht.1, ht.2, ?_⟩
      by_cases h : φ.eval s = true
      · exact Or.inl h
      · rcases hs with hs | hs
        · exact absurd hs h
        · exact Or.inr ⟨by simpa using h, hs⟩
    refine ⟨fun s t => if φ.eval s = true then o1 s t else φ.leaves + o2 s t,
      cvar φ.leaves v1 v2, cvar φ.leaves p1 p2, ?_, ?_⟩
    · intro s t hs ht
      obtain ⟨ht1, ht2, hc⟩ := key s t hs ht
      rcases hc with h | ⟨h, h'⟩
      · obtain ⟨b1, b2, b3⟩ := a1 s t h ht1
        simp only [h, ↓reduceIte, DMFormula.leaves]
        rw [cvar_lt _ _ _ _ b1, cvar_lt _ _ _ _ b1]
        exact ⟨by omega, b2, b3⟩
      · obtain ⟨b1, b2, b3⟩ := a2 s t h' ht2
        simp only [h, Bool.false_eq_true, ↓reduceIte, DMFormula.leaves]
        rw [cvar_add, cvar_add]
        exact ⟨by omega, b2, b3⟩
    · intro s t s' t' hs ht hs' ht' he
      obtain ⟨ht1, ht2, hc⟩ := key s t hs ht
      obtain ⟨ht1', ht2', hc'⟩ := key s' t' hs' ht'
      rcases hc with h | ⟨h, h2⟩ <;> rcases hc' with h' | ⟨h', h2'⟩
      · simp only [h, h', ↓reduceIte] at he ⊢
        exact r1 s t s' t' h ht1 h' ht1' he
      · simp only [h, h', Bool.false_eq_true, ↓reduceIte] at he
        have := (a1 s t h ht1).1
        omega
      · simp only [h, h', Bool.false_eq_true, ↓reduceIte] at he
        have := (a1 s' t' h' ht1').1
        omega
      · simp only [h, h', Bool.false_eq_true, ↓reduceIte] at he ⊢
        have he' : o2 s t = o2 s' t' := by omega
        rw [r2 s t s' t' h2 ht2 h2' ht2' he']

def vx (b k : ℕ) : Fin (2 * b + 1) := ⟨k % (2 * b + 1), Nat.mod_lt _ (by omega)⟩

lemma vx_val (b k : ℕ) (h : k ≤ 2 * b) : (vx b k).val = k := by
  simp only [vx]
  exact Nat.mod_eq_of_lt (by omega)

lemma vx_eq (b : ℕ) (j : Fin (2 * b + 1)) (k : ℕ) (h : j.val = k) : vx b k = j := by
  apply Fin.ext
  rw [vx_val b k (by omega), h]

def orChain (b : ℕ) : ℕ → DMFormula (2 * b + 1)
  | 0 => DMFormula.lit (vx b 1) true
  | k + 1 => DMFormula.or (orChain b k) (DMFormula.lit (vx b (k + 2)) true)

lemma orChain_leaves (b k : ℕ) : (orChain b k).leaves = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [orChain, DMFormula.leaves, ih]

lemma orChain_eval (b k : ℕ) (x : Fin (2 * b + 1) → Bool) :
    (orChain b k).eval x = true ↔ ∃ m ≤ k, x (vx b (m + 1)) = true := by
  induction k with
  | zero =>
    simp [orChain, DMFormula.eval]
  | succ k ih =>
    simp only [orChain, DMFormula.eval, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨m, hm, hx⟩ | hx)
      · exact ⟨m, by omega, hx⟩
      · exact ⟨k + 1, le_rfl, hx⟩
    · rintro ⟨m, hm, hx⟩
      by_cases hmk : m ≤ k
      · exact Or.inl ⟨m, hmk, hx⟩
      · have hmeq : m = k + 1 := by omega
        subst hmeq
        exact Or.inr hx

def rimChain (b : ℕ) : ℕ → DMFormula (2 * b + 1)
  | 0 => DMFormula.and (DMFormula.lit (vx b 1) true) (DMFormula.lit (vx b 2) true)
  | i + 1 => DMFormula.or (rimChain b i)
      (DMFormula.and (DMFormula.lit (vx b (2 * (i + 1) + 1)) true)
        (DMFormula.lit (vx b (2 * (i + 1) + 2)) true))

lemma rimChain_leaves (b i : ℕ) : (rimChain b i).leaves = 2 * i + 2 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [rimChain, DMFormula.leaves, ih]
    omega

lemma rimChain_eval (b i : ℕ) (x : Fin (2 * b + 1) → Bool) :
    (rimChain b i).eval x = true ↔
      ∃ m ≤ i, x (vx b (2 * m + 1)) = true ∧ x (vx b (2 * m + 2)) = true := by
  induction i with
  | zero =>
    simp [rimChain, DMFormula.eval]
  | succ i ih =>
    simp only [rimChain, DMFormula.eval, Bool.or_eq_true, Bool.and_eq_true, ih]
    constructor
    · rintro (⟨m, hm, hx⟩ | hx)
      · exact ⟨m, by omega, hx⟩
      · exact ⟨i + 1, le_rfl, hx⟩
    · rintro ⟨m, hm, hx⟩
      by_cases hmi : m ≤ i
      · exact Or.inl ⟨m, hmi, hx⟩
      · have hmeq : m = i + 1 := by omega
        subst hmeq
        exact Or.inr hx

def bigF (b : ℕ) : DMFormula (2 * b + 1) :=
  DMFormula.or
    (DMFormula.and (DMFormula.lit (vx b 0) true) (orChain b (2 * b - 1)))
    (rimChain b (b - 1))

lemma bigF_leaves (b : ℕ) (hb : 1 ≤ b) : (bigF b).leaves = 4 * b + 1 := by
  simp only [bigF, DMFormula.leaves, orChain_leaves, rimChain_leaves]
  omega

lemma bigF_eval (b : ℕ) (hb : 1 ≤ b) (x : Fin (2 * b + 1) → Bool) :
    (bigF b).eval x = true ↔ ∃ u v : Fin (2 * b + 1),
      ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧
        x u = true ∧ x v = true := by
  simp only [bigF, DMFormula.eval, Bool.or_eq_true, Bool.and_eq_true,
    orChain_eval, rimChain_eval, ↓reduceIte]
  constructor
  · rintro (⟨h0, m, hm, hxm⟩ | ⟨m, hm, hx1, hx2⟩)
    · exact ⟨vx b 0, vx b (m + 1),
        Or.inl ⟨vx_val b 0 (by omega), by rw [vx_val b (m + 1) (by omega)]; omega⟩, h0, hxm⟩
    · exact ⟨vx b (2 * m + 1), vx b (2 * m + 2),
        Or.inr ⟨by rw [vx_val b _ (by omega)]; omega,
          by rw [vx_val b _ (by omega), vx_val b _ (by omega)]⟩, hx1, hx2⟩
  · rintro ⟨u, v, hE, hu, hv⟩
    have hul := u.isLt
    have hvl := v.isLt
    rcases hE with ⟨h0, hpos⟩ | ⟨hodd, hsucc⟩
    · left
      refine ⟨by rw [vx_eq b u 0 h0]; exact hu, v.val - 1, by omega, ?_⟩
      rw [vx_eq b v (v.val - 1 + 1) (by omega)]
      exact hv
    · right
      refine ⟨(u.val - 1) / 2, by omega, ?_, ?_⟩
      · rw [vx_eq b u (2 * ((u.val - 1) / 2) + 1) (by omega)]
        exact hu
      · rw [vx_eq b v (2 * ((u.val - 1) / 2) + 2) (by omega)]
        exact hv

def sp (b k : ℕ) : Fin (2 * b + 1) → Bool := fun j => decide (j.val = 0 ∨ j.val = k)

def rim (b i : ℕ) : Fin (2 * b + 1) → Bool :=
  fun j => decide (j.val = 2 * i + 1 ∨ j.val = 2 * i + 2)

def sng (b k : ℕ) : Fin (2 * b + 1) → Bool := fun j => decide (j.val = k)

def trD (b : ℕ) (D : Finset ℕ) (c : ℕ → Bool) : Fin (2 * b + 1) → Bool :=
  fun j => decide (0 < j.val ∧ ((j.val - 1) / 2) ∈ D ∧
    (j.val % 2 = 1 ↔ c ((j.val - 1) / 2) = true))

def kk (i : ℕ) (p : Bool) : ℕ := if p = true then 2 * i + 1 else 2 * i + 2

lemma kk_cases (i : ℕ) (p : Bool) :
    (p = true ∧ kk i p = 2 * i + 1) ∨ (p = false ∧ kk i p = 2 * i + 2) := by
  cases p <;> simp [kk]

lemma kk_bd (b i : ℕ) (p : Bool) (hi : i < b) : 1 ≤ kk i p ∧ kk i p ≤ 2 * b := by
  rcases kk_cases i p with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

lemma trD_kk (b : ℕ) (D : Finset ℕ) (c : ℕ → Bool) (i : ℕ) (hiD : i ∈ D) (p : Bool)
    (j : Fin (2 * b + 1)) (hj : j.val = kk i p) : trD b D c j = true ↔ c i = p := by
  rcases kk_cases i p with ⟨hp, hk⟩ | ⟨hp, hk⟩
  · have e : (j.val - 1) / 2 = i := by omega
    simp only [trD, decide_eq_true_eq, e, hiD, true_and, hp]
    constructor
    · rintro ⟨_, h⟩
      exact h.mp (by omega)
    · intro h
      exact ⟨by omega, fun _ => h, fun _ => by omega⟩
  · have e : (j.val - 1) / 2 = i := by omega
    simp only [trD, decide_eq_true_eq, e, hiD, true_and, hp]
    constructor
    · rintro ⟨_, h⟩
      by_contra hc
      have hc' : c i = true := by simpa using hc
      have := h.mpr hc'
      omega
    · intro h
      refine ⟨by omega, fun _ => by omega, fun h1 => ?_⟩
      rw [h] at h1
      exact absurd h1 (by simp)

def Sys (b L : ℕ) (P : (Fin (2 * b + 1) → Bool) → Bool)
    (own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ)
    (var : ℕ → Fin (2 * b + 1)) (pol : ℕ → Bool) : Prop :=
  (∀ x, P x = true ↔ ∃ u v : Fin (2 * b + 1),
    ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧
      x u = true ∧ x v = true) ∧
  (∀ s t, P s = true → P t = false →
    own s t < L ∧ s (var (own s t)) = pol (own s t) ∧
      t (var (own s t)) = !(pol (own s t))) ∧
  (∀ s t s' t', P s = true → P t = false → P s' = true → P t' = false →
    own s t = own s' t' → own s t' = own s t)

lemma P_sp {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * b) : P (sp b k) = true := by
  rw [h.1]
  refine ⟨vx b 0, vx b k, Or.inl ⟨vx_val b 0 (by omega), by rw [vx_val b k hk2]; omega⟩, ?_, ?_⟩
  · simp [sp, vx_val b 0 (by omega)]
  · simp [sp, vx_val b k hk2]

lemma P_rim {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (i : ℕ) (hi : i < b) : P (rim b i) = true := by
  rw [h.1]
  refine ⟨vx b (2 * i + 1), vx b (2 * i + 2),
    Or.inr ⟨by rw [vx_val b _ (by omega)]; omega,
      by rw [vx_val b _ (by omega), vx_val b _ (by omega)]⟩, ?_, ?_⟩
  · simp [rim, vx_val b (2 * i + 1) (by omega)]
  · simp [rim, vx_val b (2 * i + 2) (by omega)]

lemma P_sng {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (k : ℕ) : P (sng b k) = false := by
  by_contra hne
  have ht : P (sng b k) = true := by simpa using hne
  obtain ⟨u, v, hE, hu, hv⟩ := (h.1 _).mp ht
  simp only [sng, decide_eq_true_eq] at hu hv
  rcases hE with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

lemma P_trD {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (D : Finset ℕ) (c : ℕ → Bool) : P (trD b D c) = false := by
  by_contra hne
  have ht : P (trD b D c) = true := by simpa using hne
  obtain ⟨u, v, hE, hu, hv⟩ := (h.1 _).mp ht
  simp only [trD, decide_eq_true_eq] at hu hv
  rcases hE with ⟨h0, _⟩ | ⟨hodd, hs⟩
  · omega
  · have e : (v.val - 1) / 2 = (u.val - 1) / 2 := by omega
    rw [e] at hv
    have c1 := hu.2.2.mp hodd
    have := hv.2.2.mpr c1
    omega

lemma own_pos_of_le {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (s t : Fin (2 * b + 1) → Bool) (hs : P s = true) (ht : P t = false)
    (hle : ∀ j, t j = true → s j = true) :
    own s t < L ∧ pol (own s t) = true ∧
      s (var (own s t)) = true ∧ t (var (own s t)) = false := by
  obtain ⟨l1, l2, l3⟩ := h.2.1 s t hs ht
  cases hp : pol (own s t) with
  | true =>
    rw [hp] at l2 l3
    exact ⟨l1, rfl, l2, by simpa using l3⟩
  | false =>
    rw [hp] at l2 l3
    simp only [Bool.not_false] at l3
    have := hle _ l3
    rw [l2] at this
    exact absurd this (by simp)

lemma var_R {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (i : ℕ) (hi : i < b) (p : Bool) :
    (var (own (sp b (kk i p)) (sng b 0))).val = kk i p ∧
      pol (own (sp b (kk i p)) (sng b 0)) = true ∧
      own (sp b (kk i p)) (sng b 0) < L := by
  obtain ⟨l1, lp, l2, l3⟩ := own_pos_of_le h _ _
    (P_sp h _ (kk_bd b i p hi).1 (kk_bd b i p hi).2) (P_sng h 0)
    (by intro j hj; simp only [sng, sp, decide_eq_true_eq] at hj ⊢; exact Or.inl hj)
  simp only [sp, sng, decide_eq_true_eq, decide_eq_false_iff_not] at l2 l3
  exact ⟨by omega, lp, l1⟩

lemma var_M {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (i : ℕ) (hi : i < b) (p : Bool) :
    (var (own (rim b i) (sng b (kk i (!p))))).val = kk i p ∧
      pol (own (rim b i) (sng b (kk i (!p)))) = true ∧
      own (rim b i) (sng b (kk i (!p))) < L := by
  obtain ⟨l1, lp, l2, l3⟩ := own_pos_of_le h _ _
    (P_rim h i hi) (P_sng h (kk i (!p)))
    (by
      intro j hj
      simp only [sng, rim, decide_eq_true_eq] at hj ⊢
      cases p <;> simp [kk] at hj <;> omega)
  simp only [rim, sng, decide_eq_true_eq, decide_eq_false_iff_not] at l2 l3
  refine ⟨?_, lp, l1⟩
  cases p <;> simp [kk] at l2 l3 ⊢ <;> omega

lemma card3 (x y z : ℕ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Finset ℕ).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
    Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]

lemma card4 (x y z w : ℕ) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) : ({x, y, z, w} : Finset ℕ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxz, hxw]),
    Finset.card_insert_of_notMem (by simp [hyz, hyw]),
    Finset.card_insert_of_notMem (by simp [hzw]), Finset.card_singleton]

lemma ne_of_var {b : ℕ} (var : ℕ → Fin (2 * b + 1)) (x y : ℕ) (h : (var x).val ≠ (var y).val) :
    x ≠ y := by
  intro e
  rw [e] at h
  exact h rfl

def triLeaves (L : ℕ) (var : ℕ → Fin (2 * b + 1)) (i : ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun l => (var l).val = 2 * i + 1 ∨ (var l).val = 2 * i + 2)

lemma tri3_pos {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (i : ℕ) (hi : i < b) :
    ∃ A : Finset ℕ, 3 ≤ A.card ∧ A ⊆ triLeaves L var i ∧ ∀ l ∈ A, pol l = true := by
  have hb1 := kk_bd b i true hi
  have hb2 := kk_bd b i false hi
  obtain ⟨r1, r1p, r1L⟩ := var_R h i hi true
  obtain ⟨r2, r2p, r2L⟩ := var_R h i hi false
  obtain ⟨m1, m1p, m1L⟩ := var_M h i hi true
  obtain ⟨m2, m2p, m2L⟩ := var_M h i hi false
  simp only [Bool.not_true, Bool.not_false] at m1 m1p m1L m2 m2p m2L
  have k1 : kk i true = 2 * i + 1 := by simp [kk]
  have k2 : kk i false = 2 * i + 2 := by simp [kk]
  have r1' := r1.trans k1
  have m1' := m1.trans k1
  have r2' := r2.trans k2
  have m2' := m2.trans k2
  by_cases e1 : own (rim b i) (sng b (kk i false)) = own (sp b (kk i true)) (sng b 0)
  · have q1 := h.2.2 (rim b i) (sng b (kk i false)) (sp b (kk i true)) (sng b 0)
      (P_rim h i hi) (P_sng h _) (P_sp h _ hb1.1 hb1.2) (P_sng h 0) e1
    have ne2 : own (rim b i) (sng b (kk i true)) ≠ own (sp b (kk i false)) (sng b 0) := by
      intro e2
      have q2 := h.2.2 (rim b i) (sng b (kk i true)) (sp b (kk i false)) (sng b 0)
        (P_rim h i hi) (P_sng h _) (P_sp h _ hb2.1 hb2.2) (P_sng h 0) e2
      have eq12 : own (rim b i) (sng b (kk i false)) = own (rim b i) (sng b (kk i true)) :=
        q1.symm.trans q2
      have hv := congrArg (fun l => (var l).val) eq12
      omega
    refine ⟨{own (sp b (kk i true)) (sng b 0), own (rim b i) (sng b (kk i true)),
      own (sp b (kk i false)) (sng b 0)}, ?_, ?_, ?_⟩
    · rw [card3 _ _ _ (ne_of_var var _ _ (by omega)) (ne_of_var var _ _ (by omega)) ne2]
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      simp only [triLeaves, Finset.mem_filter, Finset.mem_range]
      rcases hl with rfl | rfl | rfl
      · exact ⟨r1L, Or.inl r1'⟩
      · exact ⟨m2L, Or.inr m2'⟩
      · exact ⟨r2L, Or.inr r2'⟩
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · exact r1p
      · exact m2p
      · exact r2p
  · refine ⟨{own (rim b i) (sng b (kk i false)), own (sp b (kk i true)) (sng b 0),
      own (sp b (kk i false)) (sng b 0)}, ?_, ?_, ?_⟩
    · rw [card3 _ _ _ e1 (ne_of_var var _ _ (by omega)) (ne_of_var var _ _ (by omega))]
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      simp only [triLeaves, Finset.mem_filter, Finset.mem_range]
      rcases hl with rfl | rfl | rfl
      · exact ⟨m1L, Or.inl m1'⟩
      · exact ⟨r1L, Or.inl r1'⟩
      · exact ⟨r2L, Or.inr r2'⟩
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · exact m1p
      · exact r1p
      · exact r2p

lemma tight_all_pos {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (i : ℕ) (hi : i < b) (hle : (triLeaves L var i).card ≤ 3) :
    ∀ l ∈ triLeaves L var i, pol l = true := by
  obtain ⟨A, hA3, hAsub, hApos⟩ := tri3_pos h i hi
  have heq : A = triLeaves L var i := Finset.eq_of_subset_of_card_le hAsub (by omega)
  rw [← heq]
  exact hApos

lemma own_trD_pos {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (D : Finset ℕ) (hDsub : ∀ j ∈ D, j < b)
    (hDpos : ∀ j ∈ D, ∀ l ∈ triLeaves L var j, pol l = true)
    (s : Fin (2 * b + 1) → Bool) (hs : P s = true) (c : ℕ → Bool) :
    own s (trD b D c) < L ∧ pol (own s (trD b D c)) = true ∧
      s (var (own s (trD b D c))) = true ∧ trD b D c (var (own s (trD b D c))) = false := by
  obtain ⟨l1, l2, l3⟩ := h.2.1 s (trD b D c) hs (P_trD h D c)
  cases hp : pol (own s (trD b D c)) with
  | true =>
    rw [hp] at l2 l3
    exact ⟨l1, rfl, l2, by simpa using l3⟩
  | false =>
    exfalso
    rw [hp] at l3
    simp only [Bool.not_false, trD, decide_eq_true_eq] at l3
    obtain ⟨hpos, hjD, _⟩ := l3
    set j := ((var (own s (trD b D c))).val - 1) / 2
    have hjb := hDsub j hjD
    have hvlt := (var (own s (trD b D c))).isLt
    have hmem : own s (trD b D c) ∈ triLeaves L var j := by
      simp only [triLeaves, Finset.mem_filter, Finset.mem_range]
      exact ⟨l1, by omega⟩
    have hpt := hDpos j hjD _ hmem
    rw [hp] at hpt
    exact absurd hpt (by simp)

lemma var_D {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (D : Finset ℕ) (hDsub : ∀ j ∈ D, j < b)
    (hDpos : ∀ j ∈ D, ∀ l ∈ triLeaves L var j, pol l = true)
    (i : ℕ) (hiD : i ∈ D) (c : ℕ → Bool) :
    (var (own (rim b i) (trD b D c))).val = kk i (!(c i)) ∧ own (rim b i) (trD b D c) < L := by
  have hi := hDsub i hiD
  obtain ⟨l1, _, l2, l3⟩ := own_trD_pos h D hDsub hDpos (rim b i) (P_rim h i hi) c
  simp only [rim, decide_eq_true_eq] at l2
  refine ⟨?_, l1⟩
  rcases l2 with e | e
  · have ht := trD_kk b D c i hiD true _ (by rw [e]; simp [kk])
    have hc : c i = false := by
      by_contra hcc
      have hc' : c i = true := by simpa using hcc
      rw [ht.mpr hc'] at l3
      exact absurd l3 (by simp)
    rw [hc, e]
    simp [kk]
  · have ht := trD_kk b D c i hiD false _ (by rw [e]; simp [kk])
    have hc : c i = true := by
      by_contra hcc
      have hc' : c i = false := by simpa using hcc
      rw [ht.mpr hc'] at l3
      exact absurd l3 (by simp)
    rw [hc, e]
    simp [kk]

lemma var_S {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (D : Finset ℕ) (hDsub : ∀ j ∈ D, j < b)
    (hDpos : ∀ j ∈ D, ∀ l ∈ triLeaves L var j, pol l = true)
    (i : ℕ) (hiD : i ∈ D) (p : Bool) (c : ℕ → Bool) :
    own (sp b (kk i p)) (trD b D c) < L ∧
      ((var (own (sp b (kk i p)) (trD b D c))).val = 0 ∨
        (var (own (sp b (kk i p)) (trD b D c))).val = kk i p) ∧
      (c i = p → (var (own (sp b (kk i p)) (trD b D c))).val = 0) := by
  have hi := hDsub i hiD
  obtain ⟨l1, _, l2, l3⟩ := own_trD_pos h D hDsub hDpos (sp b (kk i p))
    (P_sp h _ (kk_bd b i p hi).1 (kk_bd b i p hi).2) c
  simp only [sp, decide_eq_true_eq] at l2
  refine ⟨l1, l2, fun hc => ?_⟩
  rcases l2 with e | e
  · exact e
  · rw [(trD_kk b D c i hiD p _ e).mpr hc] at l3
    exact absurd l3 (by simp)

lemma tri4_D {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (D : Finset ℕ) (hDsub : ∀ j ∈ D, j < b)
    (hDpos : ∀ j ∈ D, ∀ l ∈ triLeaves L var j, pol l = true)
    (i : ℕ) (hiD : i ∈ D)
    (hn : ∀ p : Bool, ∃ c : ℕ → Bool, c i ≠ p ∧
      (var (own (sp b (kk i p)) (trD b D c))).val ≠ kk i p) :
    4 ≤ (triLeaves L var i).card := by
  have hi := hDsub i hiD
  have hb1 := kk_bd b i true hi
  have hb2 := kk_bd b i false hi
  obtain ⟨r1, _, r1L⟩ := var_R h i hi true
  obtain ⟨r2, _, r2L⟩ := var_R h i hi false
  obtain ⟨c1, hc1, hv1⟩ := hn true
  obtain ⟨c2, hc2, hv2⟩ := hn false
  have hc1' : c1 i = false := by simpa using hc1
  have hc2' : c2 i = true := by simpa using hc2
  obtain ⟨d1, d1L⟩ := var_D h D hDsub hDpos i hiD c1
  obtain ⟨d2, d2L⟩ := var_D h D hDsub hDpos i hiD c2
  have k1 : kk i true = 2 * i + 1 := by simp [kk]
  have k2 : kk i false = 2 * i + 2 := by simp [kk]
  rw [hc1'] at d1
  rw [hc2'] at d2
  simp only [Bool.not_false, Bool.not_true] at d1 d2
  have s1 : (var (own (sp b (kk i true)) (trD b D c1))).val = 0 := by
    rcases (var_S h D hDsub hDpos i hiD true c1).2.1 with e | e
    · exact e
    · exact absurd e hv1
  have s2 : (var (own (sp b (kk i false)) (trD b D c2))).val = 0 := by
    rcases (var_S h D hDsub hDpos i hiD false c2).2.1 with e | e
    · exact e
    · exact absurd e hv2
  have ne1 : own (sp b (kk i true)) (sng b 0) ≠ own (rim b i) (trD b D c1) := by
    intro e
    have q := h.2.2 (sp b (kk i true)) (sng b 0) (rim b i) (trD b D c1)
      (P_sp h _ hb1.1 hb1.2) (P_sng h 0) (P_rim h i hi) (P_trD h D _) e
    rw [q] at s1
    omega
  have ne2 : own (sp b (kk i false)) (sng b 0) ≠ own (rim b i) (trD b D c2) := by
    intro e
    have q := h.2.2 (sp b (kk i false)) (sng b 0) (rim b i) (trD b D c2)
      (P_sp h _ hb2.1 hb2.2) (P_sng h 0) (P_rim h i hi) (P_trD h D _) e
    rw [q] at s2
    omega
  have r1' := r1.trans k1
  have d1' := d1.trans k1
  have r2' := r2.trans k2
  have d2' := d2.trans k2
  let S4 : Finset ℕ := {own (sp b (kk i true)) (sng b 0), own (rim b i) (trD b D c1),
    own (sp b (kk i false)) (sng b 0), own (rim b i) (trD b D c2)}
  have hcard : S4.card = 4 :=
    card4 _ _ _ _ ne1 (ne_of_var var _ _ (by omega)) (ne_of_var var _ _ (by omega))
      (ne_of_var var _ _ (by omega)) (ne_of_var var _ _ (by omega)) ne2
  have hsub : S4 ⊆ triLeaves L var i := by
    intro l hl
    simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hl
    simp only [triLeaves, Finset.mem_filter, Finset.mem_range]
    rcases hl with rfl | rfl | rfl | rfl
    · exact ⟨r1L, Or.inl r1'⟩
    · exact ⟨d1L, Or.inl d1'⟩
    · exact ⟨r2L, Or.inr r2'⟩
    · exact ⟨d2L, Or.inr d2'⟩
  rw [← hcard]
  exact Finset.card_le_card hsub

lemma hub_D {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool} (h : Sys b L P own var pol)
    (hb : 1 ≤ b) (D : Finset ℕ) (hDsub : ∀ j ∈ D, j < b)
    (hDpos : ∀ j ∈ D, ∀ l ∈ triLeaves L var j, pol l = true)
    (dir : ℕ → Bool)
    (hdir : ∀ i ∈ D, ∀ c : ℕ → Bool, c i ≠ dir i →
      (var (own (sp b (kk i (dir i))) (trD b D c))).val = kk i (dir i)) :
    ∃ A : Finset ℕ, D.card + 1 ≤ A.card ∧ ∀ l ∈ A, l < L ∧ (var l).val = 0 := by
  classical
  by_cases hDne : D.Nonempty
  · obtain ⟨i0, hi0D⟩ := hDne
    have hnp : ∀ j, (!(dir j)) ≠ dir j := fun j => by cases dir j <;> simp
    have hH : ∀ i ∈ D,
        own (sp b (kk i (dir i))) (trD b D (fun j => if j = i then dir i else !(dir j))) < L ∧
        (var (own (sp b (kk i (dir i)))
          (trD b D (fun j => if j = i then dir i else !(dir j))))).val = 0 := by
      intro i hiD
      obtain ⟨l1, _, l3⟩ := var_S h D hDsub hDpos i hiD (dir i)
        (fun j => if j = i then dir i else !(dir j))
      exact ⟨l1, l3 (by simp)⟩
    have h0 : own (sp b (kk i0 (!(dir i0)))) (trD b D (fun j => !(dir j))) < L ∧
        (var (own (sp b (kk i0 (!(dir i0)))) (trD b D (fun j => !(dir j))))).val = 0 := by
      obtain ⟨l1, _, l3⟩ := var_S h D hDsub hDpos i0 hi0D (!(dir i0)) (fun j => !(dir j))
      exact ⟨l1, l3 rfl⟩
    have hinj : Set.InjOn
        (fun i => own (sp b (kk i (dir i)))
          (trD b D (fun j => if j = i then dir i else !(dir j))))
        (D : Set ℕ) := by
      intro i hi j hj e
      by_contra hij
      have bi := kk_bd b i (dir i) (hDsub i hi)
      have bj := kk_bd b j (dir j) (hDsub j hj)
      have q := h.2.2 (sp b (kk j (dir j))) (trD b D (fun m => if m = j then dir j else !(dir m)))
        (sp b (kk i (dir i))) (trD b D (fun m => if m = i then dir i else !(dir m)))
        (P_sp h _ bj.1 bj.2) (P_trD h D _) (P_sp h _ bi.1 bi.2) (P_trD h D _) e.symm
      have v1 := hdir j hj (fun m => if m = i then dir i else !(dir m))
        (by
          have hji : ¬ j = i := fun e' => hij e'.symm
          simp only [hji, ↓reduceIte]
          exact hnp j)
      rw [q, (hH j hj).2] at v1
      omega
    have hnot : own (sp b (kk i0 (!(dir i0)))) (trD b D (fun j => !(dir j))) ∉
        D.image (fun i => own (sp b (kk i (dir i)))
          (trD b D (fun j => if j = i then dir i else !(dir j)))) := by
      intro hmem
      obtain ⟨j, hj, e⟩ := Finset.mem_image.mp hmem
      have bj := kk_bd b j (dir j) (hDsub j hj)
      have b0 := kk_bd b i0 (!(dir i0)) (hDsub i0 hi0D)
      have q := h.2.2 (sp b (kk j (dir j))) (trD b D (fun m => if m = j then dir j else !(dir m)))
        (sp b (kk i0 (!(dir i0)))) (trD b D (fun m => !(dir m)))
        (P_sp h _ bj.1 bj.2) (P_trD h D _) (P_sp h _ b0.1 b0.2) (P_trD h D _) e
      have v1 := hdir j hj (fun m => !(dir m)) (hnp j)
      rw [q, (hH j hj).2] at v1
      omega
    refine ⟨insert (own (sp b (kk i0 (!(dir i0)))) (trD b D (fun j => !(dir j))))
      (D.image (fun i => own (sp b (kk i (dir i)))
        (trD b D (fun j => if j = i then dir i else !(dir j))))), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj]
    · intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact h0
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
        exact hH j hj
  · have hDemp : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDne
    subst hDemp
    obtain ⟨l1, _, l2, l3⟩ := own_pos_of_le h (sp b 1) (sng b 1)
      (P_sp h 1 le_rfl (by omega)) (P_sng h 1)
      (by intro j hj; simp only [sng, sp, decide_eq_true_eq] at hj ⊢; exact Or.inr hj)
    simp only [sp, sng, decide_eq_true_eq, decide_eq_false_iff_not] at l2 l3
    have hv0 : (var (own (sp b 1) (sng b 1))).val = 0 := by omega
    refine ⟨{own (sp b 1) (sng b 1)}, by simp, ?_⟩
    intro l hl
    rw [Finset.mem_singleton] at hl
    subst hl
    exact ⟨l1, hv0⟩

lemma count {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} {pol : ℕ → Bool}
    (hb : 1 ≤ b) (h : Sys b L P own var pol) : 4 * b + 1 ≤ L := by
  classical
  let D : Finset ℕ := (Finset.range b).filter (fun i => (triLeaves L var i).card ≤ 3)
  have hDsub : ∀ i ∈ D, i < b := fun i hi => Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hDpos : ∀ i ∈ D, ∀ l ∈ triLeaves L var i, pol l = true := by
    intro i hi
    exact tight_all_pos h i (hDsub i hi) (Finset.mem_filter.mp hi).2
  have hex : ∀ i, ∃ p : Bool, i ∈ D →
      ∀ c : ℕ → Bool, c i ≠ p → (var (own (sp b (kk i p)) (trD b D c))).val = kk i p := by
    intro i
    by_cases hiD : i ∈ D
    · by_contra hcon
      have hn : ∀ p : Bool, ∃ c : ℕ → Bool, c i ≠ p ∧
          (var (own (sp b (kk i p)) (trD b D c))).val ≠ kk i p := by
        intro p
        by_contra hp
        apply hcon
        refine ⟨p, fun _ c hc => ?_⟩
        by_contra hv
        exact hp ⟨c, hc, hv⟩
      have h4 := tri4_D h D hDsub hDpos i hiD hn
      have h3 := (Finset.mem_filter.mp hiD).2
      omega
    · exact ⟨true, fun h' => absurd h' hiD⟩
  choose dir hdir using hex
  obtain ⟨AH, hAH1, hAH2⟩ := hub_D h hb D hDsub hDpos dir hdir
  have htri_ge : ∀ i ∈ Finset.range b,
      (if i ∈ D then 3 else 4) ≤ (triLeaves L var i).card := by
    intro i hi
    by_cases hiD : i ∈ D
    · simp only [hiD, ↓reduceIte]
      obtain ⟨A, hA3, hAsub, _⟩ := tri3_pos h i (Finset.mem_range.mp hi)
      exact hA3.trans (Finset.card_le_card hAsub)
    · simp only [hiD, ↓reduceIte]
      have hnot : ¬ (triLeaves L var i).card ≤ 3 := by
        intro hle
        exact hiD (Finset.mem_filter.mpr ⟨hi, hle⟩)
      omega
  have hdisj1 : Disjoint AH ((Finset.range b).biUnion (triLeaves L var)) := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    obtain ⟨i, _, hl⟩ := Finset.mem_biUnion.mp h2
    have hv0 := (hAH2 l h1).2
    have hvi := (Finset.mem_filter.mp hl).2
    omega
  have hdisj2 : ∀ i ∈ Finset.range b, ∀ j ∈ Finset.range b, i ≠ j →
      Disjoint (triLeaves L var i) (triLeaves L var j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro l h1 h2
    have hv1 := (Finset.mem_filter.mp h1).2
    have hv2 := (Finset.mem_filter.mp h2).2
    omega
  have hsub : AH ∪ (Finset.range b).biUnion (triLeaves L var) ⊆ Finset.range L := by
    intro l hl
    rcases Finset.mem_union.mp hl with h1 | h2
    · exact Finset.mem_range.mpr (hAH2 l h1).1
    · obtain ⟨i, _, hl⟩ := Finset.mem_biUnion.mp h2
      exact (Finset.mem_filter.mp hl).1
  have hc1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj1, Finset.card_biUnion hdisj2, Finset.card_range] at hc1
  have hc2 : ∑ i ∈ Finset.range b, (if i ∈ D then 3 else 4) ≤
      ∑ i ∈ Finset.range b, (triLeaves L var i).card :=
    Finset.sum_le_sum htri_ge
  have hc3 : ∑ i ∈ Finset.range b, (if i ∈ D then 3 else 4) + D.card = 4 * b := by
    have e1 : ∑ i ∈ Finset.range b, ((if i ∈ D then 3 else 4) + (if i ∈ D then 1 else 0)) =
        ∑ _i ∈ Finset.range b, 4 :=
      Finset.sum_congr rfl (fun i _ => by split_ifs <;> rfl)
    rw [Finset.sum_add_distrib] at e1
    have e2 : ∑ i ∈ Finset.range b, (if i ∈ D then 1 else 0) = D.card := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h' => h'.2, fun h' => ⟨hDsub i h', h'⟩⟩
    rw [e2] at e1
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at e1
    omega
  omega

lemma main_thm (b s : ℕ) (hb : 1 ≤ b) :
    HasLeafSize (2 * b + 1)
      (fun x : Fin (2 * b + 1) → Bool => decide (∃ u v : Fin (2 * b + 1),
        ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧
          x u = true ∧ x v = true)) s ↔ 4 * b + 1 ≤ s := by
  constructor
  · rintro ⟨φ, hle, heval⟩
    obtain ⟨own, var, pol, a1, r1⟩ := own_exists φ
    have hspec : ∀ x : Fin (2 * b + 1) → Bool, φ.eval x = true ↔
        ∃ u v : Fin (2 * b + 1),
          ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧
            x u = true ∧ x v = true := by
      intro x
      rw [heval x, decide_eq_true_eq]
    have hc := count hb (L := φ.leaves) (P := φ.eval) (own := own) (var := var) (pol := pol)
      ⟨hspec, a1, r1⟩
    omega
  · intro hs
    refine ⟨bigF b, ?_, ?_⟩
    · rw [bigF_leaves b hb]
      exact hs
    · intro x
      apply Bool.eq_iff_iff.mpr
      rw [bigF_eval b hb x, decide_eq_true_eq]

end PEqualNP.Outside.L_meta_220

theorem PEqualNP.Outside.L_meta_220 : ∀ b s : ℕ, 1 ≤ b → (PEqualNP.MetaComplexity.HasLeafSize (2 * b + 1) (fun x : Fin (2 * b + 1) → Bool => decide (∃ u v : Fin (2 * b + 1), ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧ x u = true ∧ x v = true)) s ↔ 4 * b + 1 ≤ s) :=
  PEqualNP.Outside.L_meta_220.main_thm
