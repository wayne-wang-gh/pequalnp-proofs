import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_258_aux

open PEqualNP.MetaComplexity

variable {n : ℕ}

def posC (i : Fin n) : DMFormula n → ℕ
  | .lit j c => if j = i ∧ c = true then 1 else 0
  | .and p q => posC i p + posC i q
  | .or p q => posC i p + posC i q

def negC (i : Fin n) : DMFormula n → ℕ
  | .lit j c => if j = i ∧ c = false then 1 else 0
  | .and p q => negC i p + negC i q
  | .or p q => negC i p + negC i q

def ev (i : Fin n) (x : Fin n → Bool) (a b : Bool) : DMFormula n → Bool
  | .lit j c => if j = i then (if c then a else b) else (if c then x j else !x j)
  | .and p q => ev i x a b p && ev i x a b q
  | .or p q => ev i x a b p || ev i x a b q

theorem rec_tot (i : Fin n) (φ : DMFormula n) :
    DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0)
      (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = posC i φ + negC i φ := by
  induction φ with
  | lit j c =>
    show (if j = i then 1 else 0) = _
    simp only [posC, negC]
    by_cases h : j = i <;> cases c <;> simp [h]
  | and p q hp hq =>
    show _ + _ = _
    rw [hp, hq]
    simp only [posC, negC]
    ring
  | or p q hp hq =>
    show _ + _ = _
    rw [hp, hq]
    simp only [posC, negC]
    ring

theorem rec_neg (i : Fin n) (φ : DMFormula n) :
    DMFormula.rec (motive := fun _ => ℕ)
      (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0)
      (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = negC i φ := by
  induction φ with
  | lit j c =>
    show (if j = i ∧ c = false then 1 else 0) = _
    simp only [negC]
  | and p q hp hq =>
    show _ + _ = _
    rw [hp, hq]
    simp only [negC]
  | or p q hp hq =>
    show _ + _ = _
    rw [hp, hq]
    simp only [negC]

theorem eval_ev (i : Fin n) (x : Fin n → Bool) (φ : DMFormula n) :
    φ.eval x = ev i x (x i) (!x i) φ := by
  induction φ with
  | lit j c =>
    simp only [DMFormula.eval, ev]
    by_cases h : j = i
    · subst h
      cases c <;> simp
    · simp [h]
  | and p q hp hq => simp only [DMFormula.eval, ev, hp, hq]
  | or p q hp hq => simp only [DMFormula.eval, ev, hp, hq]

theorem ev_upd (i : Fin n) (x : Fin n → Bool) (v a b : Bool) (φ : DMFormula n) :
    ev i (Function.update x i v) a b φ = ev i x a b φ := by
  induction φ with
  | lit j c =>
    simp only [ev]
    by_cases h : j = i
    · simp [h]
    · simp [h]
  | and p q hp hq => simp only [ev, hp, hq]
  | or p q hp hq => simp only [ev, hp, hq]

theorem ev_pos0 (i : Fin n) (x : Fin n → Bool) (a a2 b : Bool) (φ : DMFormula n)
    (h : posC i φ = 0) : ev i x a b φ = ev i x a2 b φ := by
  induction φ with
  | lit j c =>
    simp only [posC] at h
    simp only [ev]
    by_cases hj : j = i
    · cases c
      · simp [hj]
      · simp [hj] at h
    · simp [hj]
  | and p q hp hq =>
    simp only [posC] at h
    simp only [ev, hp (by omega), hq (by omega)]
  | or p q hp hq =>
    simp only [posC] at h
    simp only [ev, hp (by omega), hq (by omega)]

theorem ev_neg0 (i : Fin n) (x : Fin n → Bool) (a b b2 : Bool) (φ : DMFormula n)
    (h : negC i φ = 0) : ev i x a b φ = ev i x a b2 φ := by
  induction φ with
  | lit j c =>
    simp only [negC] at h
    simp only [ev]
    by_cases hj : j = i
    · cases c
      · simp [hj] at h
      · simp [hj]
    · simp [hj]
  | and p q hp hq =>
    simp only [negC] at h
    simp only [ev, hp (by omega), hq (by omega)]
  | or p q hp hq =>
    simp only [negC] at h
    simp only [ev, hp (by omega), hq (by omega)]

theorem ev_mono_b (i : Fin n) (x : Fin n → Bool) (a : Bool) (φ : DMFormula n) :
    ev i x a false φ = true → ev i x a true φ = true := by
  induction φ with
  | lit j c =>
    simp only [ev]
    by_cases hj : j = i
    · cases c <;> simp [hj]
    · simp [hj]
  | and p q hp hq =>
    simp only [ev, Bool.and_eq_true]
    exact fun h => ⟨hp h.1, hq h.2⟩
  | or p q hp hq =>
    simp only [ev, Bool.or_eq_true]
    exact fun h => h.imp hp hq

theorem ro (i : Fin n) (y1 y2 : Fin n → Bool) (φ : DMFormula n) (hp : posC i φ ≤ 1)
    (hn : negC i φ ≤ 1)
    (h1 : ev i y1 false false φ = false) (h2 : ev i y1 true false φ = true)
    (h3 : ev i y1 false true φ = true)
    (h4 : ev i y2 true true φ = true) (h5 : ev i y2 true false φ = false)
    (h6 : ev i y2 false true φ = false) : False := by
  induction φ with
  | lit j c =>
    simp only [ev] at h1 h2 h3
    by_cases hj : j = i
    · cases c <;> simp_all
    · simp only [hj, ↓reduceIte] at h1 h2
      rw [h1] at h2
      exact Bool.false_ne_true h2
  | and p q ihp ihq =>
    simp only [posC] at hp
    simp only [negC] at hn
    simp only [ev] at h1 h2 h3 h4 h5 h6
    rcases (show (posC i p = 0 ∧ negC i p = 0) ∨ (posC i q = 0 ∧ negC i q = 0) ∨
        (posC i p = 0 ∧ negC i q = 0) ∨ (negC i p = 0 ∧ posC i q = 0) by omega) with
      ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩
    · have e : ∀ y a b, ev i y a b p = ev i y false false p := fun y a b =>
        (ev_pos0 i y a false b p a1).trans (ev_neg0 i y false b false p a2)
      rw [e y1 true false] at h2
      rw [e y1 false true] at h3
      rw [e y2 true true] at h4
      rw [e y2 true false] at h5
      rw [e y2 false true] at h6
      simp only [Bool.and_eq_true] at h2 h4
      rw [h2.1, Bool.true_and] at h1 h3
      rw [h4.1, Bool.true_and] at h5 h6
      exact ihq (by omega) (by omega) h1 h2.2 h3 h4.2 h5 h6
    · have e : ∀ y a b, ev i y a b q = ev i y false false q := fun y a b =>
        (ev_pos0 i y a false b q a1).trans (ev_neg0 i y false b false q a2)
      rw [e y1 true false] at h2
      rw [e y1 false true] at h3
      rw [e y2 true true] at h4
      rw [e y2 true false] at h5
      rw [e y2 false true] at h6
      simp only [Bool.and_eq_true] at h2 h4
      rw [h2.2, Bool.and_true] at h1 h3
      rw [h4.2, Bool.and_true] at h5 h6
      exact ihp (by omega) (by omega) h1 h2.1 h3 h4.1 h5 h6
    · rw [ev_pos0 i y1 true false false p a1] at h2
      rw [ev_neg0 i y1 false true false q a2] at h3
      simp only [Bool.and_eq_true] at h2 h3
      simp [h2.1, h3.2] at h1
    · rw [ev_neg0 i y1 false true false p a1] at h3
      rw [ev_pos0 i y1 true false false q a2] at h2
      simp only [Bool.and_eq_true] at h2 h3
      simp [h2.2, h3.1] at h1
  | or p q ihp ihq =>
    simp only [posC] at hp
    simp only [negC] at hn
    simp only [ev] at h1 h2 h3 h4 h5 h6
    rcases (show (posC i p = 0 ∧ negC i p = 0) ∨ (posC i q = 0 ∧ negC i q = 0) ∨
        (posC i p = 0 ∧ negC i q = 0) ∨ (negC i p = 0 ∧ posC i q = 0) by omega) with
      ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩
    · have e : ∀ y a b, ev i y a b p = ev i y false false p := fun y a b =>
        (ev_pos0 i y a false b p a1).trans (ev_neg0 i y false b false p a2)
      rw [e y1 true false] at h2
      rw [e y1 false true] at h3
      rw [e y2 true true] at h4
      rw [e y2 true false] at h5
      rw [e y2 false true] at h6
      simp only [Bool.or_eq_false_iff] at h1 h5
      rw [h1.1, Bool.false_or] at h2 h3
      rw [h5.1, Bool.false_or] at h4 h6
      exact ihq (by omega) (by omega) h1.2 h2 h3 h4 h5.2 h6
    · have e : ∀ y a b, ev i y a b q = ev i y false false q := fun y a b =>
        (ev_pos0 i y a false b q a1).trans (ev_neg0 i y false b false q a2)
      rw [e y1 true false] at h2
      rw [e y1 false true] at h3
      rw [e y2 true true] at h4
      rw [e y2 true false] at h5
      rw [e y2 false true] at h6
      simp only [Bool.or_eq_false_iff] at h1 h5
      rw [h1.2, Bool.or_false] at h2 h3
      rw [h5.2, Bool.or_false] at h4 h6
      exact ihp (by omega) (by omega) h1.1 h2 h3 h4 h5.1 h6
    · rw [ev_pos0 i y2 true false true p a1, ev_neg0 i y2 true true false q a2] at h4
      simp only [Bool.or_eq_false_iff] at h5 h6
      simp [h5.2, h6.1] at h4
    · rw [ev_neg0 i y2 true true false p a1, ev_pos0 i y2 true false true q a2] at h4
      simp only [Bool.or_eq_false_iff] at h5 h6
      simp [h5.1, h6.2] at h4

def mkAnd : Bool ⊕ DMFormula n → Bool ⊕ DMFormula n → Bool ⊕ DMFormula n
  | Sum.inl true, s => s
  | Sum.inl false, _ => Sum.inl false
  | Sum.inr p, Sum.inl true => Sum.inr p
  | Sum.inr _, Sum.inl false => Sum.inl false
  | Sum.inr p, Sum.inr q => Sum.inr (DMFormula.and p q)

def mkOr : Bool ⊕ DMFormula n → Bool ⊕ DMFormula n → Bool ⊕ DMFormula n
  | Sum.inl true, _ => Sum.inl true
  | Sum.inl false, s => s
  | Sum.inr _, Sum.inl true => Sum.inl true
  | Sum.inr p, Sum.inl false => Sum.inr p
  | Sum.inr p, Sum.inr q => Sum.inr (DMFormula.or p q)

def sv (x : Fin n → Bool) : Bool ⊕ DMFormula n → Bool
  | Sum.inl b => b
  | Sum.inr ψ => ψ.eval x

def sz : Bool ⊕ DMFormula n → ℕ
  | Sum.inl _ => 0
  | Sum.inr ψ => ψ.leaves

theorem sv_mkAnd (x : Fin n → Bool) (r s : Bool ⊕ DMFormula n) :
    sv x (mkAnd r s) = (sv x r && sv x s) := by
  rcases r with b | p <;> rcases s with c | q <;> (try cases b) <;> (try cases c) <;>
    simp [mkAnd, sv, DMFormula.eval]

theorem sv_mkOr (x : Fin n → Bool) (r s : Bool ⊕ DMFormula n) :
    sv x (mkOr r s) = (sv x r || sv x s) := by
  rcases r with b | p <;> rcases s with c | q <;> (try cases b) <;> (try cases c) <;>
    simp [mkOr, sv, DMFormula.eval]

theorem sz_mkAnd (r s : Bool ⊕ DMFormula n) : sz (mkAnd r s) ≤ sz r + sz s := by
  rcases r with b | p <;> rcases s with c | q <;> (try cases b) <;> (try cases c) <;>
    simp [mkAnd, sz, DMFormula.leaves]

theorem sz_mkOr (r s : Bool ⊕ DMFormula n) : sz (mkOr r s) ≤ sz r + sz s := by
  rcases r with b | p <;> rcases s with c | q <;> (try cases b) <;> (try cases c) <;>
    simp [mkOr, sz, DMFormula.leaves]

def sub (i : Fin n) (c : Bool) : DMFormula n → Bool ⊕ DMFormula n
  | .lit j b => if j = i ∧ b = false then Sum.inl c else Sum.inr (.lit j b)
  | .and p q => mkAnd (sub i c p) (sub i c q)
  | .or p q => mkOr (sub i c p) (sub i c q)

theorem sv_sub (i : Fin n) (c : Bool) (x : Fin n → Bool) (φ : DMFormula n) :
    sv x (sub i c φ) = ev i x (x i) c φ := by
  induction φ with
  | lit j b =>
    by_cases hj : j = i
    · subst hj
      cases b <;> simp [sub, ev, sv, DMFormula.eval]
    · simp [sub, ev, sv, DMFormula.eval, hj]
  | and p q hp hq => simp only [sub, ev, sv_mkAnd, hp, hq]
  | or p q hp hq => simp only [sub, ev, sv_mkOr, hp, hq]

theorem sz_sub (i : Fin n) (c : Bool) (φ : DMFormula n) :
    sz (sub i c φ) + negC i φ ≤ φ.leaves := by
  induction φ with
  | lit j b =>
    by_cases hj : j = i
    · subst hj
      cases b <;> simp [sub, sz, negC, DMFormula.leaves]
    · simp [sub, sz, negC, DMFormula.leaves, hj]
  | and p q hp hq =>
    simp only [sub, negC, DMFormula.leaves]
    have := sz_mkAnd (sub i c p) (sub i c q)
    omega
  | or p q hp hq =>
    simp only [sub, negC, DMFormula.leaves]
    have := sz_mkOr (sub i c p) (sub i c q)
    omega

theorem bool_aux {a b : Bool} (h : a ≠ b) (hab : a = true → b = true) :
    a = false ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem bool_aux2 {a b : Bool} (hab : a = true → b = true) (hb : b = false) : a = false := by
  cases a <;> simp_all

end PEqualNP.Outside.L_meta_258_aux

open PEqualNP.Outside.L_meta_258_aux in
theorem PEqualNP.Outside.L_meta_258 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)) → (∀ x : Fin n → Bool, φ.eval x = f x) → (∀ ψ : PEqualNP.MetaComplexity.DMFormula n, (∀ x : Fin n → Bool, ψ.eval x = f x) → φ.leaves ≤ ψ.leaves) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ ≤ 2 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 := by
  intro n f φ i hmono hess hcomp hmin htot
  rw [rec_tot] at htot
  rw [rec_neg]
  have hF : ∀ y v, f (Function.update y i v) = ev i y v (!v) φ := by
    intro y v
    rw [← hcomp, eval_ev i, ev_upd]
    simp
  have hM : ∀ y, ev i y false true φ = true → ev i y true false φ = true := by
    intro y h
    have h1 := hF y false
    have h2 := hF y true
    simp only [Bool.not_false, Bool.not_true] at h1 h2
    rw [← h1] at h
    rw [← h2]
    apply hmono _ _ _ h
    intro j hj
    by_cases hji : j = i
    · subst hji
      simp
    · simpa [Function.update_of_ne hji] using hj
  obtain ⟨x0, hx0⟩ := hess
  have hx1 : ev i x0 true false φ ≠ ev i x0 false true φ := by
    rw [hF, hF] at hx0
    simpa only [Bool.not_false, Bool.not_true] using hx0
  by_contra hneg
  by_cases hp0 : posC i φ = 0
  · have e1 : ev i x0 true false φ = ev i x0 false false φ := ev_pos0 i x0 true false false φ hp0
    have m1 := ev_mono_b i x0 false φ
    have m2 := hM x0
    rw [e1] at hx1 m2
    exact hx1 (Bool.eq_iff_iff.mpr ⟨m1, m2⟩)
  have hp1 : posC i φ ≤ 1 := by omega
  have hn1 : negC i φ ≤ 1 := by omega
  have key : ∃ c, ∀ y : Fin n → Bool, ev i y (y i) c φ = ev i y (y i) (!y i) φ := by
    by_cases hc : ∀ y : Fin n → Bool, ev i y false false φ = ev i y false true φ
    · refine ⟨false, fun y => ?_⟩
      cases hy : y i
      · exact hc y
      · rfl
    · refine ⟨true, fun y => ?_⟩
      cases hy : y i
      · rfl
      · simp only [Bool.not_true]
        obtain ⟨y1, hy1⟩ := not_forall.mp hc
        by_contra hne
        obtain ⟨a1, a3⟩ := bool_aux hy1 (ev_mono_b i y1 false φ)
        have a2 := hM y1 a3
        obtain ⟨c1, c2⟩ := bool_aux (fun h => hne h.symm) (ev_mono_b i y true φ)
        have c3 := bool_aux2 (hM y) c1
        exact ro i y1 y φ hp1 hn1 a1 a2 a3 c2 c1 c3
  obtain ⟨c, hc⟩ := key
  have hsv : ∀ x, sv x (sub i c φ) = f x := by
    intro x
    rw [sv_sub, hc, ← eval_ev, hcomp]
  have hsz := sz_sub i c φ
  rcases hr : sub i c φ with b | ψ
  · rw [hr] at hsv
    apply hx0
    have e1 := hsv (Function.update x0 i true)
    have e2 := hsv (Function.update x0 i false)
    simp only [sv] at e1 e2
    rw [← e1, ← e2]
  · rw [hr] at hsv hsz
    have hψ : ∀ x, ψ.eval x = f x := fun x => hsv x
    have := hmin ψ hψ
    simp only [sz] at hsz
    omega
