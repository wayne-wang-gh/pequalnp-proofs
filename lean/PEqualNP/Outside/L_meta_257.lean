import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_257_aux

open PEqualNP.MetaComplexity

private noncomputable def total {n : ℕ} (i : Fin n) : DMFormula n → ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j = i then 1 else 0)
    (fun _ _ a b => a + b) (fun _ _ a b => a + b)

private noncomputable def negCount {n : ℕ} (i : Fin n) : DMFormula n → ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j b => if j = i ∧ b = false then 1 else 0)
    (fun _ _ a b => a + b) (fun _ _ a b => a + b)

private def rise (hi lo : Bool) : ℕ := if hi && !lo then 1 else 0

private theorem rise_and (h₁ l₁ h₂ l₂ : Bool) :
    rise (h₁ && h₂) (l₁ && l₂) ≤ rise h₁ l₁ + rise h₂ l₂ := by
  cases h₁ <;> cases l₁ <;> cases h₂ <;> cases l₂ <;> decide

private theorem rise_or (h₁ l₁ h₂ l₂ : Bool) :
    rise (h₁ || h₂) (l₁ || l₂) ≤ rise h₁ l₁ + rise h₂ l₂ := by
  cases h₁ <;> cases l₁ <;> cases h₂ <;> cases l₂ <;> decide

private theorem count_rise {n : ℕ} (i : Fin n) (x : Fin n → Bool) (φ : DMFormula n) :
    negCount i φ + rise (φ.eval (Function.update x i true))
      (φ.eval (Function.update x i false)) ≤ total i φ := by
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · subst j
      cases b <;> simp [total,negCount,DMFormula.eval,rise]
    · cases b <;> cases hbit : x j <;>
        simp [total,negCount,DMFormula.eval,rise,h,hbit]
  | and a b ha hb =>
    have h := rise_and (a.eval (Function.update x i true)) (a.eval (Function.update x i false))
      (b.eval (Function.update x i true)) (b.eval (Function.update x i false))
    change (negCount i a + negCount i b) + _ ≤ total i a + total i b
    simp only [DMFormula.eval]
    omega
  | or a b ha hb =>
    have h := rise_or (a.eval (Function.update x i true)) (a.eval (Function.update x i false))
      (b.eval (Function.update x i true)) (b.eval (Function.update x i false))
    change (negCount i a + negCount i b) + _ ≤ total i a + total i b
    simp only [DMFormula.eval]
    omega

theorem finish {n : ℕ} (f : (Fin n → Bool) → Bool) (φ : DMFormula n) (i : Fin n)
    (hm : ∀ x y : Fin n → Bool, (∀ j, x j = true → y j = true) → f x = true → f y = true)
    (he : ∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false))
    (hf : ∀ x, φ.eval x = f x) (h1 : total i φ = 1) : negCount i φ = 0 := by
  obtain ⟨x,hx⟩ := he
  have hu := hm (Function.update x i false) (Function.update x i true) (by
    intro j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h])
  have h := count_rise i x φ
  rw [hf,hf,h1] at h
  cases hH : f (Function.update x i true) <;> cases hL : f (Function.update x i false) <;>
    simp_all [rise]

end PEqualNP.Outside.L_meta_257_aux

theorem PEqualNP.Outside.L_meta_257 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 1 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 := by
  intro n f φ i hm he hf h1
  exact PEqualNP.Outside.L_meta_257_aux.finish f φ i hm he hf h1
