import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_259

open PEqualNP.MetaComplexity

noncomputable def cnt {n : ℕ} (a : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = a then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

def E {n : ℕ} (a b c : Fin n) (p q r : Bool) : Fin n → Bool :=
  fun j => if j = a then p else if j = b then q else if j = c then r else false

def nt (h : Bool → Bool → Bool) : ℕ :=
  [h false false, h false true, h true false, h true true].count true

def xl (h : Bool → Bool → Bool) : Prop :=
  h false false = h true true ∧ h false true = h true false ∧ h false false ≠ h false true

def ga (h : Bool → Bool → Bool) : Prop := nt h ≠ 3 ∧ ¬ xl h
def go (h : Bool → Bool → Bool) : Prop := nt h ≠ 1 ∧ ¬ xl h

def Q (g : Bool → Bool → Bool → Bool) : Prop :=
  (∀ r, ga (fun p q => g p q r)) ∨ (∀ r, go (fun p q => g p q r))

theorem ga_and (h : Bool → Bool → Bool) (k : Bool) (H : ga h) : ga (fun p q => h p q && k) := by
  revert H
  cases h1 : h false false <;> cases h2 : h false true <;> cases h3 : h true false <;>
    cases h4 : h true true <;> cases k <;> simp [ga, nt, xl, h1, h2, h3, h4]

theorem ga_or (h : Bool → Bool → Bool) (k : Bool) (H : ga h) : ga (fun p q => h p q || k) := by
  revert H
  cases h1 : h false false <;> cases h2 : h false true <;> cases h3 : h true false <;>
    cases h4 : h true true <;> cases k <;> simp [ga, nt, xl, h1, h2, h3, h4]

theorem go_and (h : Bool → Bool → Bool) (k : Bool) (H : go h) : go (fun p q => h p q && k) := by
  revert H
  cases h1 : h false false <;> cases h2 : h false true <;> cases h3 : h true false <;>
    cases h4 : h true true <;> cases k <;> simp [go, nt, xl, h1, h2, h3, h4]

theorem go_or (h : Bool → Bool → Bool) (k : Bool) (H : go h) : go (fun p q => h p q || k) := by
  revert H
  cases h1 : h false false <;> cases h2 : h false true <;> cases h3 : h true false <;>
    cases h4 : h true true <;> cases k <;> simp [go, nt, xl, h1, h2, h3, h4]

theorem ga_uv (u v : Bool → Bool) : ga (fun p q => u p && v q) := by
  cases h1 : u false <;> cases h2 : u true <;> cases h3 : v false <;> cases h4 : v true <;>
    simp [ga, nt, xl, h1, h2, h3, h4]

theorem go_uv (u v : Bool → Bool) : go (fun p q => u p || v q) := by
  cases h1 : u false <;> cases h2 : u true <;> cases h3 : v false <;> cases h4 : v true <;>
    simp [go, nt, xl, h1, h2, h3, h4]

theorem ga_l (u : Bool → Bool) : ga (fun p _ => u p) := by
  cases h1 : u false <;> cases h2 : u true <;> simp [ga, nt, xl, h1, h2]

theorem ga_r (u : Bool → Bool) : ga (fun _ q => u q) := by
  cases h1 : u false <;> cases h2 : u true <;> simp [ga, nt, xl, h1, h2]

theorem indA {n : ℕ} (a b c : Fin n) (φ : DMFormula n) (h : cnt a φ = 0) (p p' q r : Bool) :
    φ.eval (E a b c p q r) = φ.eval (E a b c p' q r) := by
  induction φ with
  | lit j s =>
    have : j ≠ a := by
      intro e; simp [cnt, e] at h
    simp [DMFormula.eval, E, this]
  | and φ ψ ih1 ih2 =>
    have h' : cnt a φ + cnt a ψ = 0 := h
    simp only [DMFormula.eval, ih1 (by omega), ih2 (by omega)]
  | or φ ψ ih1 ih2 =>
    have h' : cnt a φ + cnt a ψ = 0 := h
    simp only [DMFormula.eval, ih1 (by omega), ih2 (by omega)]

theorem indB {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (φ : DMFormula n) (h : cnt b φ = 0)
    (p q q' r : Bool) :
    φ.eval (E a b c p q r) = φ.eval (E a b c p q' r) := by
  induction φ with
  | lit j s =>
    have : j ≠ b := by
      intro e; simp [cnt, e] at h
    simp [DMFormula.eval, E, this]
  | and φ ψ ih1 ih2 =>
    have h' : cnt b φ + cnt b ψ = 0 := h
    simp only [DMFormula.eval, ih1 (by omega), ih2 (by omega)]
  | or φ ψ ih1 ih2 =>
    have h' : cnt b φ + cnt b ψ = 0 := h
    simp only [DMFormula.eval, ih1 (by omega), ih2 (by omega)]

theorem qA {n : ℕ} (a b c : Fin n) (φ : DMFormula n) (h : cnt a φ = 0) :
    Q (fun p q r => φ.eval (E a b c p q r)) := by
  left; intro r
  have := ga_r (fun q => φ.eval (E a b c false q r))
  simpa [indA a b c φ h _ false] using this

theorem qB {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (φ : DMFormula n) (h : cnt b φ = 0) :
    Q (fun p q r => φ.eval (E a b c p q r)) := by
  left; intro r
  have := ga_l (fun p => φ.eval (E a b c p false r))
  simpa [indB a b c hab φ h _ _ false] using this

theorem main {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (φ : DMFormula n) :
    cnt a φ ≤ 1 → cnt b φ ≤ 1 → Q (fun p q r => φ.eval (E a b c p q r)) := by
  induction φ with
  | lit j s =>
    intro _ _
    by_cases hj : j = a
    · subst hj
      exact qB _ _ _ hab _ (by simp [cnt, hab])
    · exact qA _ _ _ _ (by simp [cnt, hj])
  | and φ ψ ih1 ih2 =>
    intro ha hb
    have ha' : cnt a φ + cnt a ψ ≤ 1 := ha
    have hb' : cnt b φ + cnt b ψ ≤ 1 := hb
    by_cases z1 : cnt a φ + cnt a ψ = 0
    · exact qA _ _ _ _ z1
    by_cases z2 : cnt b φ + cnt b ψ = 0
    · exact qB _ _ _ hab _ z2
    simp only [DMFormula.eval]
    by_cases c1 : cnt a φ = 1 <;> by_cases c2 : cnt b φ = 1
    · have e1 : cnt a ψ = 0 := by omega
      have e2 : cnt b ψ = 0 := by omega
      rcases ih1 (by omega) (by omega) with H | H
      · left; intro r
        have := ga_and _ (ψ.eval (E a b c false false r)) (H r)
        simpa [indA a b c ψ e1 _ false, indB a b c hab ψ e2 _ _ false] using this
      · right; intro r
        have := go_and _ (ψ.eval (E a b c false false r)) (H r)
        simpa [indA a b c ψ e1 _ false, indB a b c hab ψ e2 _ _ false] using this
    · have e1 : cnt a ψ = 0 := by omega
      have e2 : cnt b φ = 0 := by omega
      left; intro r
      have := ga_uv (fun p => φ.eval (E a b c p false r)) (fun q => ψ.eval (E a b c false q r))
      simpa [indA a b c ψ e1 _ false, indB a b c hab φ e2 _ _ false] using this
    · have e1 : cnt a φ = 0 := by omega
      have e2 : cnt b ψ = 0 := by omega
      left; intro r
      have := ga_uv (fun p => ψ.eval (E a b c p false r)) (fun q => φ.eval (E a b c false q r))
      simp only [indA a b c φ e1 _ false, indB a b c hab ψ e2 _ _ false] at this ⊢
      simpa [Bool.and_comm] using this
    · have e1 : cnt a φ = 0 := by omega
      have e2 : cnt b φ = 0 := by omega
      rcases ih2 (by omega) (by omega) with H | H
      · left; intro r
        have := ga_and _ (φ.eval (E a b c false false r)) (H r)
        simp only [indA a b c φ e1 _ false, indB a b c hab φ e2 _ _ false] at this ⊢
        simpa [Bool.and_comm] using this
      · right; intro r
        have := go_and _ (φ.eval (E a b c false false r)) (H r)
        simp only [indA a b c φ e1 _ false, indB a b c hab φ e2 _ _ false] at this ⊢
        simpa [Bool.and_comm] using this
  | or φ ψ ih1 ih2 =>
    intro ha hb
    have ha' : cnt a φ + cnt a ψ ≤ 1 := ha
    have hb' : cnt b φ + cnt b ψ ≤ 1 := hb
    by_cases z1 : cnt a φ + cnt a ψ = 0
    · exact qA _ _ _ _ z1
    by_cases z2 : cnt b φ + cnt b ψ = 0
    · exact qB _ _ _ hab _ z2
    simp only [DMFormula.eval]
    by_cases c1 : cnt a φ = 1 <;> by_cases c2 : cnt b φ = 1
    · have e1 : cnt a ψ = 0 := by omega
      have e2 : cnt b ψ = 0 := by omega
      rcases ih1 (by omega) (by omega) with H | H
      · left; intro r
        have := ga_or _ (ψ.eval (E a b c false false r)) (H r)
        simpa [indA a b c ψ e1 _ false, indB a b c hab ψ e2 _ _ false] using this
      · right; intro r
        have := go_or _ (ψ.eval (E a b c false false r)) (H r)
        simpa [indA a b c ψ e1 _ false, indB a b c hab ψ e2 _ _ false] using this
    · have e1 : cnt a ψ = 0 := by omega
      have e2 : cnt b φ = 0 := by omega
      right; intro r
      have := go_uv (fun p => φ.eval (E a b c p false r)) (fun q => ψ.eval (E a b c false q r))
      simpa [indA a b c ψ e1 _ false, indB a b c hab φ e2 _ _ false] using this
    · have e1 : cnt a φ = 0 := by omega
      have e2 : cnt b ψ = 0 := by omega
      right; intro r
      have := go_uv (fun p => ψ.eval (E a b c p false r)) (fun q => φ.eval (E a b c false q r))
      simp only [indA a b c φ e1 _ false, indB a b c hab ψ e2 _ _ false] at this ⊢
      simpa [Bool.or_comm] using this
    · have e1 : cnt a φ = 0 := by omega
      have e2 : cnt b φ = 0 := by omega
      rcases ih2 (by omega) (by omega) with H | H
      · left; intro r
        have := ga_or _ (φ.eval (E a b c false false r)) (H r)
        simp only [indA a b c φ e1 _ false, indB a b c hab φ e2 _ _ false] at this ⊢
        simpa [Bool.or_comm] using this
      · right; intro r
        have := go_or _ (φ.eval (E a b c false false r)) (H r)
        simp only [indA a b c φ e1 _ false, indB a b c hab φ e2 _ _ false] at this ⊢
        simpa [Bool.or_comm] using this

end PEqualNP.Outside.L_meta_259

theorem PEqualNP.Outside.L_meta_259 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (a b c : Fin n), a ≠ b → b ≠ c → a ≠ c → (∀ x : Fin n → Bool, φ.eval x = f x) → (∀ x : Fin n → Bool, (∀ j : Fin n, j ≠ a → j ≠ b → j ≠ c → x j = false) → f x = (x a && x b || x b && x c || x c && x a)) → 3 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = a then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ + PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = b then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ := by
  intro n f φ a b c hab hbc hac hφ hf
  have key : ∀ p q r : Bool, φ.eval (PEqualNP.Outside.L_meta_259.E a b c p q r) =
      (p && q || q && r || r && p) := by
    intro p q r
    rw [hφ, hf]
    · simp [PEqualNP.Outside.L_meta_259.E, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
    · intro j h1 h2 h3
      simp [PEqualNP.Outside.L_meta_259.E, h1, h2, h3]
  show 3 ≤ PEqualNP.Outside.L_meta_259.cnt a φ + PEqualNP.Outside.L_meta_259.cnt b φ
  by_contra hlt
  by_cases z1 : PEqualNP.Outside.L_meta_259.cnt a φ = 0
  · have := PEqualNP.Outside.L_meta_259.indA a b c φ z1 true false true false
    rw [key, key] at this
    simp at this
  by_cases z2 : PEqualNP.Outside.L_meta_259.cnt b φ = 0
  · have := PEqualNP.Outside.L_meta_259.indB a b c hab φ z2 true true false false
    rw [key, key] at this
    simp at this
  have H := PEqualNP.Outside.L_meta_259.main a b c hab φ (by omega) (by omega)
  simp only [key] at H
  rcases H with H | H
  · have := H true
    simp [PEqualNP.Outside.L_meta_259.ga, PEqualNP.Outside.L_meta_259.nt] at this
  · have := H false
    simp [PEqualNP.Outside.L_meta_259.go, PEqualNP.Outside.L_meta_259.nt] at this
