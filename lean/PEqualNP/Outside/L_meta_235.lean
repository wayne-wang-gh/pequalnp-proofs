import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_235_aux

open PEqualNP.MetaComplexity

-- The rank-minor argument is adapted from bluish's majority proof in PR 1791.
abbrev Input := Fin 6 → Bool

def target (x : Input) : Bool :=
  ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) ||
    ((x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))

def pos (b : Bool) (i : Fin 3) : Fin 6 :=
  if b then ⟨i.val + 3, by omega⟩ else ⟨i.val, by omega⟩

def hi (b : Bool) (i : Fin 3) (p : Fin 6) : Bool :=
  decide (∃ j : Fin 3, j ≠ i ∧ pos b j = p)

def lo (b : Bool) (i : Fin 3) (p : Fin 6) : Bool := decide (p = pos b i)

theorem block_lower (τ : Input → Input → ℕ) (valid : IsTyping 6 target τ) (b : Bool) :
    5 ≤ ∑ k : Fin 3, (typedMatrix 6 target τ (pos b k) true).rank := by
  let M (k : Fin 3) := typedMatrix 6 target τ (pos b k) true
  have yes : ∀ b i, target (hi b i) = true := by decide +kernel
  have no : ∀ b i, target (lo b i) = false := by decide +kernel
  have only : ∀ b, ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      ∀ p, hi b i p ≠ lo b j p → p = pos b k := by decide +kernel
  have on : ∀ b, ∀ i k : Fin 3, i ≠ k → hi b i (pos b k) = true := by decide +kernel
  have forced (i j k : Fin 3) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
      M k (hi b i) (lo b j) = 1 := by
    obtain ⟨p, hp, hd⟩ := valid _ _ (yes b i) (no b j)
    obtain rfl := only b i j k ij ik jk p hd
    exact ite_eq_left ⟨yes b i, no b j, hp, on b i k ik⟩
  have distinct : ∀ k : Fin 3, ∃ i j, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide
  have nonzero (k : Fin 3) : 1 ≤ (M k).rank := by
    obtain ⟨i, j, ij, ik, jk⟩ := distinct k
    have sub : (M k).submatrix (fun _ : Unit => hi b i) (fun _ : Unit => lo b j) = 1 := by
      ext a c
      simpa [Matrix.submatrix_apply, Matrix.one_apply] using forced i j k ij ik jk
    simpa [sub] using (M k).rank_submatrix_le (fun _ : Unit => hi b i) (fun _ : Unit => lo b j)
  have diagonal (i j k : Fin 3) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
      (small : (M k).rank ≤ 1) : τ (hi b i) (lo b i) = (pos b k).val := by
    by_contra absent
    have zero : M k (hi b i) (lo b i) = 0 := ite_eq_right (fun h => absent h.2.2.1)
    let B := (M k).submatrix ![hi b i, hi b j] ![lo b i, lo b j]
    have det : B.det ≠ 0 := by
      rw [Matrix.det_fin_two]
      change M k (hi b i) (lo b i) * M k (hi b j) (lo b j) -
        M k (hi b i) (lo b j) * M k (hi b j) (lo b i) ≠ 0
      simp [zero, forced i j k ij ik jk, forced j i k ij.symm jk ik]
    have rankTwo : 2 ≤ (M k).rank := by
      have h : B.rank ≤ (M k).rank := (M k).rank_submatrix_le _ _
      simpa [Matrix.rank_of_det_ne_zero det] using h
    omega
  have unique (k l : Fin 3) (kl : k ≠ l) : ¬ ((M k).rank ≤ 1 ∧ (M l).rank ≤ 1) := by
    rintro ⟨hk, hl⟩
    have third : ∀ a c : Fin 3, ∃ i, i ≠ a ∧ i ≠ c := by decide
    obtain ⟨i, ik, il⟩ := third k l
    have e := (diagonal i l k il ik kl.symm hk).symm.trans (diagonal i k l ik il kl hl)
    apply kl
    apply Fin.ext
    cases b <;> simp [pos] at e <;> omega
  change 5 ≤ ∑ k : Fin 3, (M k).rank
  rw [Fin.sum_univ_three]
  have h0 := nonzero 0
  have h1 := nonzero 1
  have h2 := nonzero 2
  have h01 := unique 0 1 (by decide)
  have h02 := unique 0 2 (by decide)
  have h12 := unique 1 2 (by decide)
  omega

theorem lower : ¬ HasTypedRank 6 target 9 := by
  rintro ⟨τ, valid, bound⟩
  have first := block_lower τ valid false
  have last := block_lower τ valid true
  have positive : ∑ k : Fin 6, (typedMatrix 6 target τ k true).rank ≤ 9 := by
    apply le_trans _ bound
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (f := fun b => (typedMatrix 6 target τ i b).rank)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ true)
  simp only [Fin.sum_univ_three, pos, Bool.false_eq_true, ite_false, ite_true] at first last
  rw [Fin.sum_univ_six] at positive
  norm_num at first last
  omega

end PEqualNP.Outside.L_meta_235_aux

theorem PEqualNP.Outside.L_meta_235 :
    ¬ PEqualNP.MetaComplexity.HasTypedRank 6 (fun x : Fin 6 → Bool =>
      ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) ||
      ((x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))) 9 := by
  exact PEqualNP.Outside.L_meta_235_aux.lower
