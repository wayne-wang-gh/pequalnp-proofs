import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_180

def rename {N M : ℕ} (e : Fin N → Fin M) : DMFormula N → DMFormula M
  | DMFormula.lit i b => DMFormula.lit (e i) b
  | DMFormula.and φ ψ => DMFormula.and (rename e φ) (rename e ψ)
  | DMFormula.or φ ψ => DMFormula.or (rename e φ) (rename e ψ)

lemma rename_eval {N M : ℕ} (e : Fin N → Fin M) (φ : DMFormula N) (z : Fin M → Bool) :
    (rename e φ).eval z = φ.eval (fun i => z (e i)) := by
  induction φ with
  | lit i b => simp [rename, DMFormula.eval]
  | and φ ψ ih1 ih2 => simp [rename, DMFormula.eval, ih1, ih2]
  | or φ ψ ih1 ih2 => simp [rename, DMFormula.eval, ih1, ih2]

lemma rename_leaves {N M : ℕ} (e : Fin N → Fin M) (φ : DMFormula N) :
    (rename e φ).leaves = φ.leaves := by
  induction φ with
  | lit i b => simp [rename, DMFormula.leaves]
  | and φ ψ ih1 ih2 => simp [rename, DMFormula.leaves, ih1, ih2]
  | or φ ψ ih1 ih2 => simp [rename, DMFormula.leaves, ih1, ih2]

def andR {M : ℕ} : Bool ⊕ DMFormula M → Bool ⊕ DMFormula M → Bool ⊕ DMFormula M
  | Sum.inl false, _ => Sum.inl false
  | Sum.inl true, r => r
  | Sum.inr _, Sum.inl false => Sum.inl false
  | Sum.inr a, Sum.inl true => Sum.inr a
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.and a b)

def orR {M : ℕ} : Bool ⊕ DMFormula M → Bool ⊕ DMFormula M → Bool ⊕ DMFormula M
  | Sum.inl true, _ => Sum.inl true
  | Sum.inl false, r => r
  | Sum.inr _, Sum.inl true => Sum.inl true
  | Sum.inr a, Sum.inl false => Sum.inr a
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.or a b)

def ev {M : ℕ} (x : Fin M → Bool) : Bool ⊕ DMFormula M → Bool
  | Sum.inl c => c
  | Sum.inr ψ => ψ.eval x

def sz {M : ℕ} : Bool ⊕ DMFormula M → ℕ
  | Sum.inl _ => 0
  | Sum.inr ψ => ψ.leaves

lemma ev_andR {M : ℕ} (x : Fin M → Bool) (r t : Bool ⊕ DMFormula M) :
    ev x (andR r t) = (ev x r && ev x t) := by
  rcases r with (_ | _) | a <;> rcases t with (_ | _) | b <;> simp [andR, ev, DMFormula.eval]

lemma ev_orR {M : ℕ} (x : Fin M → Bool) (r t : Bool ⊕ DMFormula M) :
    ev x (orR r t) = (ev x r || ev x t) := by
  rcases r with (_ | _) | a <;> rcases t with (_ | _) | b <;> simp [orR, ev, DMFormula.eval]

lemma sz_andR {M : ℕ} (r t : Bool ⊕ DMFormula M) : sz (andR r t) ≤ sz r + sz t := by
  rcases r with (_ | _) | a <;> rcases t with (_ | _) | b <;> simp [andR, sz, DMFormula.leaves]

lemma sz_orR {M : ℕ} (r t : Bool ⊕ DMFormula M) : sz (orR r t) ≤ sz r + sz t := by
  rcases r with (_ | _) | a <;> rcases t with (_ | _) | b <;> simp [orR, sz, DMFormula.leaves]

def red {N M : ℕ} (sel : Fin N → Option (Fin M)) (c : Fin N → Bool) :
    DMFormula N → Bool ⊕ DMFormula M
  | DMFormula.lit i b =>
    match sel i with
    | some j => Sum.inr (DMFormula.lit j b)
    | none => Sum.inl (if b then c i else !c i)
  | DMFormula.and φ ψ => andR (red sel c φ) (red sel c ψ)
  | DMFormula.or φ ψ => orR (red sel c φ) (red sel c ψ)

def cnt {N M : ℕ} (sel : Fin N → Option (Fin M)) : DMFormula N → ℕ
  | DMFormula.lit i _ => if (sel i).isSome then 1 else 0
  | DMFormula.and φ ψ => cnt sel φ + cnt sel ψ
  | DMFormula.or φ ψ => cnt sel φ + cnt sel ψ

lemma red_ev {N M : ℕ} (sel : Fin N → Option (Fin M)) (c : Fin N → Bool)
    (x : Fin M → Bool) (z : Fin N → Bool)
    (h1 : ∀ i j, sel i = some j → z i = x j) (h2 : ∀ i, sel i = none → z i = c i)
    (φ : DMFormula N) : ev x (red sel c φ) = φ.eval z := by
  induction φ with
  | lit i b =>
    cases hs : sel i with
    | none => simp [red, hs, ev, DMFormula.eval, h2 i hs]
    | some j => simp [red, hs, ev, DMFormula.eval, h1 i j hs]
  | and φ ψ ih1 ih2 => simp [red, ev_andR, ih1, ih2, DMFormula.eval]
  | or φ ψ ih1 ih2 => simp [red, ev_orR, ih1, ih2, DMFormula.eval]

lemma red_sz {N M : ℕ} (sel : Fin N → Option (Fin M)) (c : Fin N → Bool)
    (φ : DMFormula N) : sz (red sel c φ) ≤ cnt sel φ := by
  induction φ with
  | lit i b =>
    cases hs : sel i with
    | none => simp [red, hs, sz]
    | some j => simp [red, hs, sz, cnt, DMFormula.leaves]
  | and φ ψ ih1 ih2 =>
    have := sz_andR (red sel c φ) (red sel c ψ)
    simp only [red, cnt]
    omega
  | or φ ψ ih1 ih2 =>
    have := sz_orR (red sel c φ) (red sel c ψ)
    simp only [red, cnt]
    omega

lemma cnt_add {N M1 M2 : ℕ} (s1 : Fin N → Option (Fin M1)) (s2 : Fin N → Option (Fin M2))
    (h : ∀ i, (if (s1 i).isSome then 1 else 0) + (if (s2 i).isSome then 1 else 0) = 1)
    (φ : DMFormula N) : cnt s1 φ + cnt s2 φ = φ.leaves := by
  induction φ with
  | lit i b => simpa [cnt, DMFormula.leaves] using h i
  | and φ ψ ih1 ih2 => simp only [cnt, DMFormula.leaves]; omega
  | or φ ψ ih1 ih2 => simp only [cnt, DMFormula.leaves]; omega

def selL (n k : ℕ) : Fin (n + k) → Option (Fin n) :=
  Fin.addCases (fun i => some i) (fun _ => none)

def selR (n k : ℕ) : Fin (n + k) → Option (Fin k) :=
  Fin.addCases (fun _ => none) (fun j => some j)

lemma sel_sum (n k : ℕ) (i : Fin (n + k)) :
    (if (selL n k i).isSome then 1 else 0) + (if (selR n k i).isSome then 1 else 0) = 1 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [selL, selR]

lemma lower (n k : ℕ) (f : (Fin n → Bool) → Bool) (g : (Fin k → Bool) → Bool)
    (hf1 : ∃ x : Fin n → Bool, f x = true) (hf0 : ∃ x : Fin n → Bool, f x = false)
    (hg1 : ∃ y : Fin k → Bool, g y = true) (hg0 : ∃ y : Fin k → Bool, g y = false)
    (φ : DMFormula (n + k))
    (hφ : ∀ z : Fin (n + k) → Bool,
      φ.eval z = (f (fun i : Fin n => z (Fin.castAdd k i)) || g (fun j : Fin k => z (Fin.natAdd n j)))) :
    HasLeafSize n f (cnt (selL n k) φ) ∧ HasLeafSize k g (cnt (selR n k) φ) := by
  obtain ⟨x1, hx1⟩ := hf1
  obtain ⟨x0, hx0⟩ := hf0
  obtain ⟨y1, hy1⟩ := hg1
  obtain ⟨y0, hy0⟩ := hg0
  constructor
  · have key : ∀ x : Fin n → Bool, ev x (red (selL n k) (Fin.addCases (fun _ => false) y0) φ) = f x := by
      intro x
      rw [red_ev (selL n k) _ x (Fin.addCases x y0)]
      · rw [hφ]; simp [hy0]
      · intro i j hij
        revert hij
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [selL]
        intro h; rw [h]
      · intro i hi
        revert hi
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [selL]
    cases hr : red (selL n k) (Fin.addCases (fun _ => false) y0) φ with
    | inl c =>
      have e1 := key x1
      have e0 := key x0
      rw [hr] at e1 e0
      simp only [ev] at e1 e0
      rw [hx1] at e1
      rw [hx0] at e0
      rw [e1] at e0
      exact absurd e0 (by simp)
    | inr ψ =>
      refine ⟨ψ, ?_, fun x => ?_⟩
      · have := red_sz (selL n k) (Fin.addCases (fun _ => false) y0) φ
        rw [hr] at this
        simpa [sz] using this
      · have := key x
        rw [hr] at this
        simpa [ev] using this
  · have key : ∀ y : Fin k → Bool, ev y (red (selR n k) (Fin.addCases x0 (fun _ => false)) φ) = g y := by
      intro y
      rw [red_ev (selR n k) _ y (Fin.addCases x0 y)]
      · rw [hφ]; simp [hx0]
      · intro i j hij
        revert hij
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [selR]
        intro h; rw [h]
      · intro i hi
        revert hi
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [selR]
    cases hr : red (selR n k) (Fin.addCases x0 (fun _ => false)) φ with
    | inl c =>
      have e1 := key y1
      have e0 := key y0
      rw [hr] at e1 e0
      simp only [ev] at e1 e0
      rw [hy1] at e1
      rw [hy0] at e0
      rw [e1] at e0
      exact absurd e0 (by simp)
    | inr ψ =>
      refine ⟨ψ, ?_, fun y => ?_⟩
      · have := red_sz (selR n k) (Fin.addCases x0 (fun _ => false)) φ
        rw [hr] at this
        simpa [sz] using this
      · have := key y
        rw [hr] at this
        simpa [ev] using this

end PEqualNP.Outside.L_meta_180

theorem PEqualNP.Outside.L_meta_180 : ∀ (n k : ℕ) (f : (Fin n → Bool) → Bool) (g : (Fin k → Bool) → Bool) (a b : ℕ), (∃ x : Fin n → Bool, f x = true) → (∃ x : Fin n → Bool, f x = false) → (∃ y : Fin k → Bool, g y = true) → (∃ y : Fin k → Bool, g y = false) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize n f r ↔ a ≤ r) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize k g r ↔ b ≤ r) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasLeafSize (n + k) (fun z : Fin (n + k) → Bool => f (fun i : Fin n => z (Fin.castAdd k i)) || g (fun j : Fin k => z (Fin.natAdd n j))) s ↔ a + b ≤ s) := by
  intro n k f g a b hf1 hf0 hg1 hg0 ha hb s
  constructor
  · rintro ⟨φ, hφs, hφ⟩
    obtain ⟨hL, hR⟩ := PEqualNP.Outside.L_meta_180.lower n k f g hf1 hf0 hg1 hg0 φ hφ
    have h1 := (ha _).mp hL
    have h2 := (hb _).mp hR
    have h3 := PEqualNP.Outside.L_meta_180.cnt_add _ _ (PEqualNP.Outside.L_meta_180.sel_sum n k) φ
    omega
  · intro hs
    obtain ⟨φ, hφs, hφ⟩ := (ha a).mpr le_rfl
    obtain ⟨ψ, hψs, hψ⟩ := (hb b).mpr le_rfl
    refine ⟨DMFormula.or (PEqualNP.Outside.L_meta_180.rename (Fin.castAdd k) φ)
      (PEqualNP.Outside.L_meta_180.rename (Fin.natAdd n) ψ), ?_, fun z => ?_⟩
    · simp only [DMFormula.leaves, PEqualNP.Outside.L_meta_180.rename_leaves]
      omega
    · simp only [DMFormula.eval, PEqualNP.Outside.L_meta_180.rename_eval, hφ, hψ]
