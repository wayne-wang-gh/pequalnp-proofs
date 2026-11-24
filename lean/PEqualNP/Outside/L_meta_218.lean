import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_218

open PEqualNP.MetaComplexity

def Mono {n : ℕ} (φ : DMFormula n) : Prop :=
  DMFormula.rec (motive := fun _ : DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

def cvar {α : Type} (L : ℕ) (v1 v2 : ℕ → α) (k : ℕ) : α := if k < L then v1 k else v2 (k - L)

lemma cvar_lt {α : Type} (L : ℕ) (v1 v2 : ℕ → α) (k : ℕ) (h : k < L) :
    cvar L v1 v2 k = v1 k := by
  simp [cvar, h]

lemma cvar_add {α : Type} (L : ℕ) (v1 v2 : ℕ → α) (k : ℕ) :
    cvar L v1 v2 (L + k) = v2 k := by
  simp [cvar]

lemma own_exists {n : ℕ} (φ : DMFormula n) (hm : Mono φ) :
    ∃ (own : (Fin n → Bool) → (Fin n → Bool) → ℕ) (var : ℕ → Fin n),
      (∀ s t, φ.eval s = true → φ.eval t = false →
        own s t < φ.leaves ∧ s (var (own s t)) = true ∧ t (var (own s t)) = false) ∧
      (∀ s t s' t', φ.eval s = true → φ.eval t = false → φ.eval s' = true →
        φ.eval t' = false → own s t = own s' t' → own s t' = own s t) := by
  induction φ with
  | lit i c =>
    have hc : c = true := hm
    subst hc
    refine ⟨fun _ _ => 0, fun _ => i, ?_, ?_⟩
    · intro s t hs ht
      simp only [DMFormula.eval, ↓reduceIte] at hs ht
      exact ⟨by simp [DMFormula.leaves], hs, ht⟩
    · intro s t s' t' _ _ _ _ _
      rfl
  | and φ ψ ih1 ih2 =>
    obtain ⟨hm1, hm2⟩ := hm
    obtain ⟨o1, v1, a1, r1⟩ := ih1 hm1
    obtain ⟨o2, v2, a2, r2⟩ := ih2 hm2
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
      cvar φ.leaves v1 v2, ?_, ?_⟩
    · intro s t hs ht
      obtain ⟨hs1, hs2, hc⟩ := key s t hs ht
      rcases hc with h | ⟨h, h'⟩
      · obtain ⟨b1, b2, b3⟩ := a1 s t hs1 h
        simp only [h, Bool.false_eq_true, ↓reduceIte, DMFormula.leaves]
        rw [cvar_lt _ _ _ _ b1]
        exact ⟨by omega, b2, b3⟩
      · obtain ⟨b1, b2, b3⟩ := a2 s t hs2 h'
        simp only [h, ↓reduceIte, DMFormula.leaves]
        rw [cvar_add]
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
    obtain ⟨hm1, hm2⟩ := hm
    obtain ⟨o1, v1, a1, r1⟩ := ih1 hm1
    obtain ⟨o2, v2, a2, r2⟩ := ih2 hm2
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
      cvar φ.leaves v1 v2, ?_, ?_⟩
    · intro s t hs ht
      obtain ⟨ht1, ht2, hc⟩ := key s t hs ht
      rcases hc with h | ⟨h, h'⟩
      · obtain ⟨b1, b2, b3⟩ := a1 s t h ht1
        simp only [h, ↓reduceIte, DMFormula.leaves]
        rw [cvar_lt _ _ _ _ b1]
        exact ⟨by omega, b2, b3⟩
      · obtain ⟨b1, b2, b3⟩ := a2 s t h' ht2
        simp only [h, Bool.false_eq_true, ↓reduceIte, DMFormula.leaves]
        rw [cvar_add]
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

def orL {n : ℕ} (φ : DMFormula n) (l : List (DMFormula n)) : DMFormula n :=
  l.foldl DMFormula.or φ

lemma orL_leaves {n : ℕ} (l : List (DMFormula n)) (φ : DMFormula n) :
    (orL φ l).leaves = φ.leaves + (l.map DMFormula.leaves).sum := by
  induction l generalizing φ with
  | nil => simp [orL]
  | cons ψ l ih =>
    have h := ih (DMFormula.or φ ψ)
    simp only [orL, List.foldl_cons] at h ⊢
    rw [h]
    simp only [DMFormula.leaves, List.map_cons, List.sum_cons]
    omega

lemma orL_eval {n : ℕ} (l : List (DMFormula n)) (φ : DMFormula n) (x : Fin n → Bool) :
    (orL φ l).eval x = true ↔ φ.eval x = true ∨ ∃ ψ ∈ l, ψ.eval x = true := by
  induction l generalizing φ with
  | nil => simp [orL]
  | cons ψ l ih =>
    have h := ih (DMFormula.or φ ψ)
    simp only [orL, List.foldl_cons] at h ⊢
    rw [h]
    simp only [DMFormula.eval, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    tauto

lemma orL_mono {n : ℕ} (l : List (DMFormula n)) (φ : DMFormula n) (h1 : Mono φ)
    (h2 : ∀ ψ ∈ l, Mono ψ) : Mono (orL φ l) := by
  induction l generalizing φ with
  | nil => exact h1
  | cons ψ l ih =>
    have h := ih (DMFormula.or φ ψ) ⟨h1, h2 ψ (List.mem_cons_self)⟩
      (fun χ hχ => h2 χ (List.mem_cons_of_mem _ hχ))
    simpa only [orL, List.foldl_cons] using h

def vx (b k : ℕ) : Fin (2 * b + 1) := ⟨k % (2 * b + 1), Nat.mod_lt _ (by omega)⟩

lemma vx_val (b k : ℕ) (h : k ≤ 2 * b) : (vx b k).val = k := by
  simp only [vx]
  exact Nat.mod_eq_of_lt (by omega)

lemma vx_eq (b : ℕ) (j : Fin (2 * b + 1)) (k : ℕ) (h : j.val = k) : vx b k = j := by
  apply Fin.ext
  rw [vx_val b k (by omega), h]

def bigF (b : ℕ) : DMFormula (2 * b + 1) :=
  orL (DMFormula.and (DMFormula.lit (vx b 0) true)
      (orL (DMFormula.lit (vx b 1) true)
        (List.ofFn (fun k : Fin (2 * b - 1) => DMFormula.lit (vx b (k.val + 2)) true))))
    (List.ofFn (fun i : Fin b => DMFormula.and (DMFormula.lit (vx b (2 * i.val + 1)) true)
      (DMFormula.lit (vx b (2 * i.val + 2)) true)))

lemma bigF_leaves (b : ℕ) (hb : 1 ≤ b) : (bigF b).leaves = 4 * b + 1 := by
  simp only [bigF, orL_leaves, DMFormula.leaves, List.map_ofFn, Function.comp_def,
    List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

lemma bigF_mono (b : ℕ) : Mono (bigF b) := by
  apply orL_mono
  · refine ⟨rfl, ?_⟩
    apply orL_mono
    · rfl
    · intro ψ hψ
      obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).mp hψ
      rfl
  · intro ψ hψ
    obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).mp hψ
    exact ⟨rfl, rfl⟩

lemma bigF_eval (b : ℕ) (hb : 1 ≤ b) (x : Fin (2 * b + 1) → Bool) :
    (bigF b).eval x = true ↔ ∃ u v : Fin (2 * b + 1),
      ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧
        x u = true ∧ x v = true := by
  simp only [bigF, orL_eval, DMFormula.eval, Bool.and_eq_true, List.mem_ofFn', ↓reduceIte]
  constructor
  · rintro (⟨h0, h1 | ⟨ψ, ⟨k, rfl⟩, hk⟩⟩ | ⟨ψ, ⟨i, rfl⟩, hi⟩)
    · exact ⟨vx b 0, vx b 1, Or.inl ⟨vx_val b 0 (by omega), by rw [vx_val b 1 (by omega)]; omega⟩,
        h0, h1⟩
    · simp only [DMFormula.eval, ↓reduceIte] at hk
      have := k.isLt
      exact ⟨vx b 0, vx b (k.val + 2),
        Or.inl ⟨vx_val b 0 (by omega), by rw [vx_val b _ (by omega)]; omega⟩, h0, hk⟩
    · simp only [DMFormula.eval, ↓reduceIte, Bool.and_eq_true] at hi
      have := i.isLt
      exact ⟨vx b (2 * i.val + 1), vx b (2 * i.val + 2),
        Or.inr ⟨by rw [vx_val b _ (by omega)]; omega,
          by rw [vx_val b _ (by omega), vx_val b _ (by omega)]⟩, hi.1, hi.2⟩
  · rintro ⟨u, v, hE, hu, hv⟩
    have hvl := v.isLt
    have hul := u.isLt
    rcases hE with ⟨h0, hpos⟩ | ⟨hodd, hsucc⟩
    · left
      refine ⟨by rw [vx_eq b u 0 h0]; exact hu, ?_⟩
      by_cases h1 : v.val = 1
      · left
        rw [vx_eq b v 1 h1]
        exact hv
      · right
        refine ⟨_, ⟨⟨v.val - 2, by omega⟩, rfl⟩, ?_⟩
        simp only [DMFormula.eval, ↓reduceIte]
        rw [vx_eq b v _ (by show v.val = v.val - 2 + 2; omega)]
        exact hv
    · right
      refine ⟨_, ⟨⟨(u.val - 1) / 2, by omega⟩, rfl⟩, ?_⟩
      simp only [DMFormula.eval, ↓reduceIte, Bool.and_eq_true]
      rw [vx_eq b u _ (by show u.val = 2 * ((u.val - 1) / 2) + 1; omega),
        vx_eq b v _ (by show v.val = 2 * ((u.val - 1) / 2) + 2; omega)]
      exact ⟨hu, hv⟩

def sp (b k : ℕ) : Fin (2 * b + 1) → Bool := fun j => decide (j.val = 0 ∨ j.val = k)

def rim (b i : ℕ) : Fin (2 * b + 1) → Bool :=
  fun j => decide (j.val = 2 * i + 1 ∨ j.val = 2 * i + 2)

def z0 (b : ℕ) : Fin (2 * b + 1) → Bool := fun j => decide (j.val = 0)

def tr (b : ℕ) (c : ℕ → Bool) : Fin (2 * b + 1) → Bool :=
  fun j => decide (0 < j.val ∧ (j.val % 2 = 1 ↔ c ((j.val - 1) / 2) = true))

def kk (i : ℕ) (p : Bool) : ℕ := if p = true then 2 * i + 1 else 2 * i + 2

lemma kk_cases (i : ℕ) (p : Bool) :
    (p = true ∧ kk i p = 2 * i + 1) ∨ (p = false ∧ kk i p = 2 * i + 2) := by
  cases p <;> simp [kk]

lemma kk_bd (b i : ℕ) (p : Bool) (hi : i < b) : 1 ≤ kk i p ∧ kk i p ≤ 2 * b := by
  rcases kk_cases i p with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

lemma tr_kk (b : ℕ) (c : ℕ → Bool) (i : ℕ) (p : Bool) (j : Fin (2 * b + 1))
    (hj : j.val = kk i p) : tr b c j = true ↔ c i = p := by
  rcases kk_cases i p with ⟨hp, hk⟩ | ⟨hp, hk⟩
  · have e : (j.val - 1) / 2 = i := by omega
    simp only [tr, decide_eq_true_eq, e, hp]
    constructor
    · rintro ⟨_, h⟩
      exact h.mp (by omega)
    · intro h
      exact ⟨by omega, fun _ => h, fun _ => by omega⟩
  · have e : (j.val - 1) / 2 = i := by omega
    simp only [tr, decide_eq_true_eq, e, hp]
    constructor
    · rintro ⟨_, h⟩
      by_contra hc
      have hc' : c i = true := by simpa using hc
      have := h.mpr hc'
      omega
    · intro h
      refine ⟨by omega, fun h1 => by omega, fun h1 => ?_⟩
      rw [h] at h1
      exact absurd h1 (by simp)

def Sys (b L : ℕ) (P : (Fin (2 * b + 1) → Bool) → Bool)
    (own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ)
    (var : ℕ → Fin (2 * b + 1)) : Prop :=
  (∀ x, P x = true ↔ ∃ u v : Fin (2 * b + 1),
    ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧
      x u = true ∧ x v = true) ∧
  (∀ s t, P s = true → P t = false →
    own s t < L ∧ s (var (own s t)) = true ∧ t (var (own s t)) = false) ∧
  (∀ s t s' t', P s = true → P t = false → P s' = true → P t' = false →
    own s t = own s' t' → own s t' = own s t)

lemma P_sp {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * b) :
    P (sp b k) = true := by
  rw [h.1]
  refine ⟨vx b 0, vx b k, Or.inl ⟨vx_val b 0 (by omega), by rw [vx_val b k hk2]; omega⟩, ?_, ?_⟩
  · simp [sp, vx_val b 0 (by omega)]
  · simp [sp, vx_val b k hk2]

lemma P_rim {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) (i : ℕ) (hi : i < b) : P (rim b i) = true := by
  rw [h.1]
  refine ⟨vx b (2 * i + 1), vx b (2 * i + 2),
    Or.inr ⟨by rw [vx_val b _ (by omega)]; omega,
      by rw [vx_val b _ (by omega), vx_val b _ (by omega)]⟩, ?_, ?_⟩
  · simp [rim, vx_val b (2 * i + 1) (by omega)]
  · simp [rim, vx_val b (2 * i + 2) (by omega)]

lemma P_z0 {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) : P (z0 b) = false := by
  by_contra hne
  have ht : P (z0 b) = true := by simpa using hne
  obtain ⟨u, v, hE, hu, hv⟩ := (h.1 _).mp ht
  simp only [z0, decide_eq_true_eq] at hu hv
  omega

lemma P_tr {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) (c : ℕ → Bool) : P (tr b c) = false := by
  by_contra hne
  have ht : P (tr b c) = true := by simpa using hne
  obtain ⟨u, v, hE, hu, hv⟩ := (h.1 _).mp ht
  simp only [tr, decide_eq_true_eq] at hu hv
  rcases hE with ⟨h0, _⟩ | ⟨hodd, hs⟩
  · omega
  · have e : (v.val - 1) / 2 = (u.val - 1) / 2 := by omega
    rw [e] at hv
    have c1 := hu.2.mp hodd
    have := hv.2.mpr c1
    omega

lemma var_R {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) (i : ℕ) (hi : i < b) (p : Bool) :
    (var (own (sp b (kk i p)) (z0 b))).val = kk i p ∧ own (sp b (kk i p)) (z0 b) < L := by
  obtain ⟨l1, l2, l3⟩ := h.2.1 _ _ (P_sp h _ (kk_bd b i p hi).1 (kk_bd b i p hi).2) (P_z0 h)
  simp only [sp, z0, decide_eq_true_eq, decide_eq_false_iff_not] at l2 l3
  exact ⟨by omega, l1⟩

lemma var_D {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) (i : ℕ) (hi : i < b) (c : ℕ → Bool) :
    (var (own (rim b i) (tr b c))).val = kk i (!(c i)) ∧ own (rim b i) (tr b c) < L := by
  obtain ⟨l1, l2, l3⟩ := h.2.1 _ _ (P_rim h i hi) (P_tr h c)
  simp only [rim, decide_eq_true_eq] at l2
  refine ⟨?_, l1⟩
  rcases l2 with e | e
  · have ht := tr_kk b c i true _ (by rw [e]; simp [kk])
    have hc : c i = false := by
      by_contra hcc
      have hc' : c i = true := by simpa using hcc
      rw [ht.mpr hc'] at l3
      exact absurd l3 (by simp)
    rw [hc, e]
    simp [kk]
  · have ht := tr_kk b c i false _ (by rw [e]; simp [kk])
    have hc : c i = true := by
      by_contra hcc
      have hc' : c i = false := by simpa using hcc
      rw [ht.mpr hc'] at l3
      exact absurd l3 (by simp)
    rw [hc, e]
    simp [kk]

lemma var_S {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) (i : ℕ) (hi : i < b) (p : Bool) (c : ℕ → Bool) :
    own (sp b (kk i p)) (tr b c) < L ∧
      ((var (own (sp b (kk i p)) (tr b c))).val = 0 ∨
        (var (own (sp b (kk i p)) (tr b c))).val = kk i p) ∧
      (c i = p → (var (own (sp b (kk i p)) (tr b c))).val = 0) := by
  obtain ⟨l1, l2, l3⟩ := h.2.1 _ _ (P_sp h _ (kk_bd b i p hi).1 (kk_bd b i p hi).2) (P_tr h c)
  simp only [sp, decide_eq_true_eq] at l2
  refine ⟨l1, l2, fun hc => ?_⟩
  rcases l2 with e | e
  · exact e
  · rw [(tr_kk b c i p _ e).mpr hc] at l3
    exact absurd l3 (by simp)

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

lemma tri3 {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) (i : ℕ) (hi : i < b) :
    ∃ A : Finset ℕ, 3 ≤ A.card ∧
      ∀ l ∈ A, l < L ∧ ((var l).val = 2 * i + 1 ∨ (var l).val = 2 * i + 2) := by
  have hb1 := kk_bd b i true hi
  have hb2 := kk_bd b i false hi
  obtain ⟨r1, r1L⟩ := var_R h i hi true
  obtain ⟨r2, r2L⟩ := var_R h i hi false
  obtain ⟨d1, d1L⟩ := var_D h i hi (fun _ => false)
  obtain ⟨d2, d2L⟩ := var_D h i hi (fun _ => true)
  have k1 : kk i true = 2 * i + 1 := by simp [kk]
  have k2 : kk i false = 2 * i + 2 := by simp [kk]
  simp only [Bool.not_false, Bool.not_true] at d1 d2
  have r1 := r1.trans k1
  have d1 := d1.trans k1
  have r2 := r2.trans k2
  have d2 := d2.trans k2
  by_cases e1 : own (rim b i) (tr b (fun _ => false)) = own (sp b (kk i true)) (z0 b)
  · have q1 := h.2.2 (rim b i) (tr b (fun _ => false)) (sp b (kk i true)) (z0 b)
      (P_rim h i hi) (P_tr h _) (P_sp h _ hb1.1 hb1.2) (P_z0 h) e1
    have ne : own (rim b i) (tr b (fun _ => true)) ≠ own (sp b (kk i false)) (z0 b) := by
      intro e2
      have q2 := h.2.2 (rim b i) (tr b (fun _ => true)) (sp b (kk i false)) (z0 b)
        (P_rim h i hi) (P_tr h _) (P_sp h _ hb2.1 hb2.2) (P_z0 h) e2
      have e3 : own (rim b i) (tr b (fun _ => false)) = own (rim b i) (tr b (fun _ => true)) :=
        q1.symm.trans q2
      rw [e3] at d1
      omega
    refine ⟨{own (sp b (kk i true)) (z0 b), own (sp b (kk i false)) (z0 b),
      own (rim b i) (tr b (fun _ => true))}, ?_, ?_⟩
    · rw [card3 _ _ _ (ne_of_var var _ _ (by omega)) (ne_of_var var _ _ (by omega)) (Ne.symm ne)]
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · exact ⟨r1L, Or.inl r1⟩
      · exact ⟨r2L, Or.inr r2⟩
      · exact ⟨d2L, Or.inr d2⟩
  · refine ⟨{own (sp b (kk i true)) (z0 b), own (rim b i) (tr b (fun _ => false)),
      own (sp b (kk i false)) (z0 b)}, ?_, ?_⟩
    · rw [card3 _ _ _ (Ne.symm e1) (ne_of_var var _ _ (by omega)) (ne_of_var var _ _ (by omega))]
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · exact ⟨r1L, Or.inl r1⟩
      · exact ⟨d1L, Or.inl d1⟩
      · exact ⟨r2L, Or.inr r2⟩

lemma tri4 {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) (i : ℕ) (hi : i < b)
    (hn : ∀ p : Bool, ∃ c : ℕ → Bool, c i ≠ p ∧
      (var (own (sp b (kk i p)) (tr b c))).val ≠ kk i p) :
    ∃ A : Finset ℕ, 4 ≤ A.card ∧
      ∀ l ∈ A, l < L ∧ ((var l).val = 2 * i + 1 ∨ (var l).val = 2 * i + 2) := by
  have hb1 := kk_bd b i true hi
  have hb2 := kk_bd b i false hi
  obtain ⟨r1, r1L⟩ := var_R h i hi true
  obtain ⟨r2, r2L⟩ := var_R h i hi false
  obtain ⟨c1, hc1, hv1⟩ := hn true
  obtain ⟨c2, hc2, hv2⟩ := hn false
  have hc1' : c1 i = false := by simpa using hc1
  have hc2' : c2 i = true := by simpa using hc2
  obtain ⟨d1, d1L⟩ := var_D h i hi c1
  obtain ⟨d2, d2L⟩ := var_D h i hi c2
  have k1 : kk i true = 2 * i + 1 := by simp [kk]
  have k2 : kk i false = 2 * i + 2 := by simp [kk]
  rw [hc1'] at d1
  rw [hc2'] at d2
  simp only [Bool.not_false, Bool.not_true] at d1 d2
  have s1 : (var (own (sp b (kk i true)) (tr b c1))).val = 0 := by
    rcases (var_S h i hi true c1).2.1 with e | e
    · exact e
    · exact absurd e hv1
  have s2 : (var (own (sp b (kk i false)) (tr b c2))).val = 0 := by
    rcases (var_S h i hi false c2).2.1 with e | e
    · exact e
    · exact absurd e hv2
  have ne1 : own (sp b (kk i true)) (z0 b) ≠ own (rim b i) (tr b c1) := by
    intro e
    have q := h.2.2 (sp b (kk i true)) (z0 b) (rim b i) (tr b c1)
      (P_sp h _ hb1.1 hb1.2) (P_z0 h) (P_rim h i hi) (P_tr h _) e
    rw [q] at s1
    omega
  have ne2 : own (sp b (kk i false)) (z0 b) ≠ own (rim b i) (tr b c2) := by
    intro e
    have q := h.2.2 (sp b (kk i false)) (z0 b) (rim b i) (tr b c2)
      (P_sp h _ hb2.1 hb2.2) (P_z0 h) (P_rim h i hi) (P_tr h _) e
    rw [q] at s2
    omega
  have r1 := r1.trans k1
  have d1 := d1.trans k1
  have r2 := r2.trans k2
  have d2 := d2.trans k2
  refine ⟨{own (sp b (kk i true)) (z0 b), own (rim b i) (tr b c1),
    own (sp b (kk i false)) (z0 b), own (rim b i) (tr b c2)}, ?_, ?_⟩
  · rw [card4 _ _ _ _ ne1 (ne_of_var var _ _ (by omega)) (ne_of_var var _ _ (by omega))
      (ne_of_var var _ _ (by omega)) (ne_of_var var _ _ (by omega)) ne2]
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact ⟨r1L, Or.inl r1⟩
    · exact ⟨d1L, Or.inl d1⟩
    · exact ⟨r2L, Or.inr r2⟩
    · exact ⟨d2L, Or.inr d2⟩

lemma hub {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (h : Sys b L P own var) (hb : 1 ≤ b) (B : Finset ℕ) (hB : ∀ i ∈ B, i < b)
    (pol : ℕ → Bool)
    (hpol : ∀ i ∈ B, ∀ c : ℕ → Bool, c i ≠ pol i →
      (var (own (sp b (kk i (pol i))) (tr b c))).val = kk i (pol i)) :
    ∃ A : Finset ℕ, B.card + 1 ≤ A.card ∧ ∀ l ∈ A, l < L ∧ (var l).val = 0 := by
  classical
  have hnp : ∀ j, (!(pol j)) ≠ pol j := by
    intro j
    cases pol j <;> simp
  have hH : ∀ i, i < b → own (sp b (kk i (pol i))) (tr b (fun j => if j = i then pol i else !(pol j))) < L ∧
      (var (own (sp b (kk i (pol i))) (tr b (fun j => if j = i then pol i else !(pol j))))).val = 0 := by
    intro i hi
    obtain ⟨l1, _, l3⟩ := var_S h i hi (pol i) (fun j => if j = i then pol i else !(pol j))
    exact ⟨l1, l3 (by simp)⟩
  have h0 : own (sp b (kk 0 (!(pol 0)))) (tr b (fun j => !(pol j))) < L ∧
      (var (own (sp b (kk 0 (!(pol 0)))) (tr b (fun j => !(pol j))))).val = 0 := by
    obtain ⟨l1, _, l3⟩ := var_S h 0 (by omega) (!(pol 0)) (fun j => !(pol j))
    exact ⟨l1, l3 rfl⟩
  have hinj : Set.InjOn
      (fun i => own (sp b (kk i (pol i))) (tr b (fun j => if j = i then pol i else !(pol j))))
      (B : Set ℕ) := by
    intro i hi j hj e
    by_contra hij
    have hib := hB i hi
    have hjb := hB j hj
    have bi := kk_bd b i (pol i) hib
    have bj := kk_bd b j (pol j) hjb
    have q := h.2.2 (sp b (kk j (pol j))) (tr b (fun m => if m = j then pol j else !(pol m)))
      (sp b (kk i (pol i))) (tr b (fun m => if m = i then pol i else !(pol m)))
      (P_sp h _ bj.1 bj.2) (P_tr h _) (P_sp h _ bi.1 bi.2) (P_tr h _) e.symm
    have v1 := hpol j hj (fun m => if m = i then pol i else !(pol m))
      (by
        have hji : ¬ j = i := fun e' => hij e'.symm
        simp only [hji, ↓reduceIte]
        exact hnp j)
    rw [q, (hH j hjb).2] at v1
    omega
  have hnot : own (sp b (kk 0 (!(pol 0)))) (tr b (fun j => !(pol j))) ∉
      B.image (fun i => own (sp b (kk i (pol i)))
        (tr b (fun j => if j = i then pol i else !(pol j)))) := by
    intro hmem
    obtain ⟨j, hj, e⟩ := Finset.mem_image.mp hmem
    have hjb := hB j hj
    have bj := kk_bd b j (pol j) hjb
    have b0 := kk_bd b 0 (!(pol 0)) (by omega)
    have q := h.2.2 (sp b (kk j (pol j))) (tr b (fun m => if m = j then pol j else !(pol m)))
      (sp b (kk 0 (!(pol 0)))) (tr b (fun m => !(pol m)))
      (P_sp h _ bj.1 bj.2) (P_tr h _) (P_sp h _ b0.1 b0.2) (P_tr h _) e
    have v1 := hpol j hj (fun m => !(pol m)) (hnp j)
    rw [q, (hH j hjb).2] at v1
    omega
  refine ⟨insert (own (sp b (kk 0 (!(pol 0)))) (tr b (fun j => !(pol j))))
    (B.image (fun i => own (sp b (kk i (pol i)))
      (tr b (fun j => if j = i then pol i else !(pol j))))), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj]
  · intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact h0
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
      exact hH j (hB j hj)

lemma count {b L : ℕ} {P : (Fin (2 * b + 1) → Bool) → Bool}
    {own : (Fin (2 * b + 1) → Bool) → (Fin (2 * b + 1) → Bool) → ℕ}
    {var : ℕ → Fin (2 * b + 1)} (hb : 1 ≤ b) (h : Sys b L P own var) : 4 * b + 1 ≤ L := by
  classical
  have hBsub : ∀ i ∈ (Finset.range b).filter (fun i => ∃ p : Bool, ∀ c : ℕ → Bool, c i ≠ p →
      (var (own (sp b (kk i p)) (tr b c))).val = kk i p), i < b :=
    fun i hi => Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hex : ∀ i, ∃ p : Bool, i ∈ (Finset.range b).filter (fun i => ∃ p : Bool,
      ∀ c : ℕ → Bool, c i ≠ p → (var (own (sp b (kk i p)) (tr b c))).val = kk i p) →
      ∀ c : ℕ → Bool, c i ≠ p → (var (own (sp b (kk i p)) (tr b c))).val = kk i p := by
    intro i
    by_cases hi : i ∈ (Finset.range b).filter (fun i => ∃ p : Bool, ∀ c : ℕ → Bool, c i ≠ p →
      (var (own (sp b (kk i p)) (tr b c))).val = kk i p)
    · obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hi).2
      exact ⟨p, fun _ => hp⟩
    · exact ⟨true, fun h' => absurd h' hi⟩
  choose pol hpol using hex
  generalize hBdef : (Finset.range b).filter (fun i => ∃ p : Bool, ∀ c : ℕ → Bool, c i ≠ p →
      (var (own (sp b (kk i p)) (tr b c))).val = kk i p) = B at hBsub hpol
  obtain ⟨AH, hAH1, hAH2⟩ := hub h hb B hBsub pol hpol
  have htri : ∀ i, ∃ A : Finset ℕ, i ∈ Finset.range b →
      (if i ∈ B then 3 else 4) ≤ A.card ∧
        ∀ l ∈ A, l < L ∧ ((var l).val = 2 * i + 1 ∨ (var l).val = 2 * i + 2) := by
    intro i
    by_cases hi : i ∈ Finset.range b
    · have hib := Finset.mem_range.mp hi
      by_cases hiB : i ∈ B
      · obtain ⟨A, h1, h2⟩ := tri3 h i hib
        exact ⟨A, fun _ => ⟨by simp only [hiB, ↓reduceIte]; exact h1, h2⟩⟩
      · have hn : ∀ p : Bool, ∃ c : ℕ → Bool, c i ≠ p ∧
            (var (own (sp b (kk i p)) (tr b c))).val ≠ kk i p := by
          intro p
          by_contra hcon
          apply hiB
          rw [← hBdef]
          refine Finset.mem_filter.mpr ⟨hi, p, fun c hc => ?_⟩
          by_contra hv
          exact hcon ⟨c, hc, hv⟩
        obtain ⟨A, h1, h2⟩ := tri4 h i hib hn
        exact ⟨A, fun _ => ⟨by simp only [hiB, ↓reduceIte]; exact h1, h2⟩⟩
    · exact ⟨∅, fun h' => absurd h' hi⟩
  choose A hA using htri
  have hdisj1 : Disjoint AH ((Finset.range b).biUnion A) := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    obtain ⟨i, hi, hl⟩ := Finset.mem_biUnion.mp h2
    have := (hAH2 l h1).2
    have := ((hA i hi).2 l hl).2
    omega
  have hdisj2 : ∀ i ∈ Finset.range b, ∀ j ∈ Finset.range b, i ≠ j → Disjoint (A i) (A j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro l h1 h2
    have := ((hA i hi).2 l h1).2
    have := ((hA j hj).2 l h2).2
    omega
  have hsub : AH ∪ (Finset.range b).biUnion A ⊆ Finset.range L := by
    intro l hl
    rcases Finset.mem_union.mp hl with h1 | h2
    · exact Finset.mem_range.mpr (hAH2 l h1).1
    · obtain ⟨i, hi, hl⟩ := Finset.mem_biUnion.mp h2
      exact Finset.mem_range.mpr ((hA i hi).2 l hl).1
  have hc1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj1, Finset.card_biUnion hdisj2, Finset.card_range] at hc1
  have hc2 : ∑ i ∈ Finset.range b, (if i ∈ B then 3 else 4) ≤ ∑ i ∈ Finset.range b, (A i).card :=
    Finset.sum_le_sum (fun i hi => (hA i hi).1)
  have hc3 : ∑ i ∈ Finset.range b, (if i ∈ B then 3 else 4) + B.card = 4 * b := by
    have e1 : ∑ i ∈ Finset.range b, ((if i ∈ B then 3 else 4) + (if i ∈ B then 1 else 0)) =
        ∑ _i ∈ Finset.range b, 4 :=
      Finset.sum_congr rfl (fun i _ => by split_ifs <;> rfl)
    rw [Finset.sum_add_distrib] at e1
    have e2 : ∑ i ∈ Finset.range b, (if i ∈ B then 1 else 0) = B.card := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h' => h'.2, fun h' => ⟨hBsub i h', h'⟩⟩
    rw [e2] at e1
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at e1
    omega
  omega

end PEqualNP.Outside.L_meta_218

theorem PEqualNP.Outside.L_meta_218 : ∀ b s : ℕ, 1 ≤ b → ((∃ φ : PEqualNP.MetaComplexity.DMFormula (2 * b + 1), φ.leaves ≤ s ∧ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula (2 * b + 1) => Prop) (fun (_ : Fin (2 * b + 1)) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ ∧ ∀ x : Fin (2 * b + 1) → Bool, (φ.eval x = true ↔ ∃ u v : Fin (2 * b + 1), ((u.val = 0 ∧ 0 < v.val) ∨ (u.val % 2 = 1 ∧ v.val = u.val + 1)) ∧ x u = true ∧ x v = true)) ↔ 4 * b + 1 ≤ s) := by
  intro b s hb
  constructor
  · rintro ⟨φ, hle, hmono, hspec⟩
    obtain ⟨own, var, a1, r1⟩ := PEqualNP.Outside.L_meta_218.own_exists φ hmono
    have := PEqualNP.Outside.L_meta_218.count hb (L := φ.leaves) (P := φ.eval) (own := own) (var := var) ⟨hspec, a1, r1⟩
    omega
  · intro hs
    exact ⟨PEqualNP.Outside.L_meta_218.bigF b, by rw [PEqualNP.Outside.L_meta_218.bigF_leaves b hb]; exact hs, PEqualNP.Outside.L_meta_218.bigF_mono b, PEqualNP.Outside.L_meta_218.bigF_eval b hb⟩
