import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_255

open PEqualNP.MetaComplexity

private noncomputable def positives {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun j c => if j = i ∧ c = true then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

private lemma lower_input {n : ℕ} (i : Fin n) (x : Fin n → Bool) (φ : DMFormula n) :
    positives i φ = 0 →
    φ.eval (Function.update x i true) = true → φ.eval (Function.update x i false) = true := by
  induction φ with
  | lit j polarity =>
    by_cases h : j = i
    · subst j
      cases polarity <;> simp [positives, DMFormula.eval]
    · simp [DMFormula.eval, Function.update_of_ne h]
  | and a b ha hb =>
    intro h
    have h' : positives i a + positives i b = 0 := h
    simp only [DMFormula.eval, Bool.and_eq_true]
    exact fun e => ⟨ha (by omega) e.1, hb (by omega) e.2⟩
  | or a b ha hb =>
    intro h
    have h' : positives i a + positives i b = 0 := h
    simp only [DMFormula.eval, Bool.or_eq_true]
    exact fun e => e.elim (fun k => Or.inl (ha (by omega) k)) (fun k => Or.inr (hb (by omega) k))

end PEqualNP.Outside.L_meta_255

open PEqualNP.Outside.L_meta_255 in
theorem PEqualNP.Outside.L_meta_255 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = true then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 → ∀ x : Fin n → Bool, f (Function.update x i true) = f (Function.update x i false) := by
  intro n f φ i monotone computes count x
  have down : f (Function.update x i true) = true → f (Function.update x i false) = true := by
    rw [← computes, ← computes]
    exact lower_input i x φ count
  have up : f (Function.update x i false) = true → f (Function.update x i true) = true := by
    apply monotone
    intro j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update_of_ne h]
  cases ht : f (Function.update x i true) <;> cases hf : f (Function.update x i false) <;>
    simp_all
