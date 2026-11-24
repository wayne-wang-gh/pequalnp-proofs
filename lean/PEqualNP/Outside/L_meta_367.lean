import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_367_aux

private def edges : List (Fin 6 × Fin 6) := [(0,1),(1,2),(2,3),(3,4),(4,5),(0,5)]

private def sets : Fin 5 → Finset (Fin 6) := ![{0,2,4},{1,3,5},{0,3},{1,4},{2,5}]

private theorem independent : ∀ i : Fin 5, ∀ e ∈ edges,
    ¬ (e.1 ∈ sets i ∧ e.2 ∈ sets i) := by decide

private theorem cross : ∀ i j : Fin 5, i ≠ j →
    ∃ e ∈ edges, (e.1 ∈ sets i ∧ e.2 ∈ sets j) ∨ (e.1 ∈ sets j ∧ e.2 ∈ sets i) := by decide

private theorem cover : PEqualNP.MetaComplexity.SingleLevel.vc edges ≤ 3 := by
  apply Nat.sInf_le
  exact ⟨{0,2,4}, by decide, by decide⟩

end PEqualNP.Outside.L_meta_367_aux

open PEqualNP.Outside.L_meta_367_aux

theorem PEqualNP.Outside.L_meta_367 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)] → ∀ O : Finset (Fin 6) → Finset (Fin 6 × Fin 6), (∀ J : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) → (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧ (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) → PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) {w : Fin 6 × Fin 6 → ZMod 2 | ∃ J : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  rintro E rfl O h
  classical
  let S : Set (Fin 6 × Fin 6 → ZMod 2) :=
    {w | ∃ J : Finset (Fin 6), (∀ e ∈ edges, ¬ (e.1 ∈ J ∧ e.2 ∈ J)) ∧
      w = fun d => if d ∈ O J then 1 else 0}
  let p (i : Fin 5) : Fin 6 × Fin 6 → ZMod 2 := fun d => if d ∈ O (sets i) then 1 else 0
  have member (i : Fin 5) : p i ∈ S := ⟨sets i, independent i, rfl⟩
  have disjoint (i j : Fin 5) (same : p i = p j) :
      ∀ d ∈ O (sets i), d.2 ∉ sets j := by
    intro d hd
    have eq := congrFun same d
    have hj : d ∈ O (sets j) := by
      by_contra hn
      simp [p, hd, hn] at eq
    exact (h (sets j) (independent j)).2.2 d hj
  have inj : Function.Injective p := by
    intro i j eq
    by_contra neq
    obtain ⟨e, he, crossMem⟩ := cross i j neq
    have ori := ((h (sets i) (independent i)).2.1 e he).1
    have self := (h (sets i) (independent i)).2.2
    have other := disjoint i j eq
    rcases ori with forward | backward <;> rcases crossMem with ab | ba
    · exact other _ forward ab.2
    · exact self _ forward ba.2
    · exact self _ backward ab.1
    · exact other _ backward ba.1
  let V := vectorSpan (ZMod 2) S
  let f (i : Fin 5) : V := ⟨p i -ᵥ p 0, vsub_mem_vectorSpan _ (member i) (member 0)⟩
  have fi : Function.Injective f := by
    intro i j eq
    exact inj ((vsub_left_injective (p 0)) (congrArg Subtype.val eq))
  have card := Nat.card_le_card_of_injective f fi
  rw [Nat.card_fin, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at card
  apply cover.trans
  change 3 ≤ Module.finrank (ZMod 2) V
  by_contra hn
  have le : Module.finrank (ZMod 2) V ≤ 2 := by omega
  have upper := Nat.pow_le_pow_right (by decide : 0 < 2) le
  omega
