import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The mixed truth-table entry counts exactly the OR gates of a monotone circuit.
-- The large-order cases separate global soundness from a minimal dense error.
theorem PEqualNP.Outside.R_meta_1629_1 :
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      2 * q ^ 2 + 1 ≤ (C.gates.filter (fun g => g.op.eval [true, false])).length) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      199 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      N * q ≤ 100 * C.size) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      199 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      ∀ z : Fin (N + N) → Bool,
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = true → q < Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} →
      (∀ l : Fin N, z (Fin.natAdd N l) = true →
        circuitFun (N + N) C (Function.update z (Fin.natAdd N l) false) = false) →
      N * q ≤ 100 * C.size) →
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      N * q ≤ 100 * C.size := by
  intro pencil exactCase errorCase q N I dec C hq order lines pairs mono on sparse
  have lineSize (l : Fin N) : Fintype.card {p : Fin N // I p l} = q+1 := by
    simpa only [Fintype.card_subtype] using lines l
  have sparseSize (z : Fin (N+N) → Bool)
      (small : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q) :=
    sparse z (by simpa only [Fintype.card_subtype] using small)
  by_cases large : 199 ≤ q
  · classical
    let neg (z : Fin (N+N) → Bool) :=
      ¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
    let act (z : Fin (N+N) → Bool) := Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)
    let P (k : ℕ) := ∃ z, neg z ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C z = true ∧ (act z).card = k
    by_cases failure : ∃ k, P k
    · obtain ⟨z,hz,yes,sz⟩ := Nat.find_spec failure
      apply errorCase q N I C large order lineSize pairs mono on sparseSize z hz yes
      · by_contra! small
        have contra := sparseSize z small hz
        simp_all
      · intro l hl
        let y := Function.update z (Fin.natAdd N l) false
        have sub (k : Fin (N+N)) (hy : y k = true) : z k = true := by
          by_cases eq : k = Fin.natAdd N l
          · simp [y,eq] at hy
          · simpa only [y,Function.update_of_ne eq] using hy
        have ny : neg y := by
          rintro ⟨p,m,pm,hp,hm⟩
          exact hz ⟨p,m,pm,sub _ hp,sub _ hm⟩
        have acty : act y = (act z).erase l := by
          ext m
          by_cases eq : m = l
          · subst m
            simp [act,y]
          · have ne : Fin.natAdd N m ≠ Fin.natAdd N l := fun he => eq (Fin.ext (by
              have val := congrArg Fin.val he
              simp only [Fin.val_natAdd] at val
              omega))
            simp only [act,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,y,
              Function.update_of_ne ne,ne_eq,eq,not_false_eq_true]
        cases ey : PEqualNP.MetaComplexity.circuitFun (N+N) C y with
        | false => rfl
        | true =>
          have lower := Nat.find_min' failure (show P (act y).card from ⟨y,ny,ey,rfl⟩)
          rw [acty] at lower
          have less := Finset.card_erase_lt_of_mem (s := act z) (a := l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩)
          omega
    · apply exactCase q N I C large order lineSize pairs mono on
      intro z hz
      cases e : PEqualNP.MetaComplexity.circuitFun (N+N) C z with
      | false => rfl
      | true => exact (failure ⟨(act z).card,z,hz,e,rfl⟩).elim
  · have bound := pencil q N I C hq order lineSize pairs mono on sparseSize
    have lengthBound := List.length_filter_le (fun g : PEqualNP.CircuitLowerBounds.Gate =>
      g.op.eval [true,false]) C.gates
    change N * q ≤ 100 * C.gates.length
    have helper : (q^2+q+1)*q ≤ 100*(2*q^2+1) := by
      have h := Nat.mul_le_mul_right (q^2) (show q + 2 ≤ 200 by omega)
      have h' := Nat.mul_le_mul_right q (show 1 ≤ q by omega)
      nlinarith only [h,h']
    calc
      _ = (q^2+q+1)*q := congrArg (fun n : ℕ => n*q) order
      _ ≤ _ := helper
      _ ≤ _ := Nat.mul_le_mul_left 100 (bound.trans lengthBound)
