import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_366

abbrev Vertex := Fin 5
abbrev Edge := Vertex × Vertex
abbrev Vector := Edge → ZMod 2

def cycle : List Edge := [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]

def stable (i : Fin 5) : Finset Vertex :=
  ![{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}] i

lemma separate : ∀ i j : Fin 5, i ≠ j →
    ∃ e ∈ cycle, e.1 ∈ stable i ∪ stable j ∧ e.2 ∈ stable i ∪ stable j := by decide

lemma independent : ∀ i : Fin 5, ∀ e ∈ cycle, ¬ (e.1 ∈ stable i ∧ e.2 ∈ stable i) := by decide

lemma cover : PEqualNP.MetaComplexity.SingleLevel.vc cycle ≤ 3 := by
  apply Nat.sInf_le
  exact ⟨({0, 2, 3} : Finset Vertex), by decide, by decide⟩

def vector (O : Finset Vertex → Finset Edge) (J : Finset Vertex) : Vector :=
  fun d => if d ∈ O J then 1 else 0

lemma same_orientation (O : Finset Vertex → Finset Edge) (J K : Finset Vertex)
    (h : vector O J = vector O K) : O J = O K := by
  ext d
  have hd := congrFun h d
  by_cases hj : d ∈ O J <;> by_cases hk : d ∈ O K <;> simp_all [vector]

lemma distinguish (O : Finset Vertex → Finset Edge)
    (direct : ∀ i : Fin 5, ∀ e ∈ cycle, e ∈ O (stable i) ∨ (e.2, e.1) ∈ O (stable i))
    (avoid : ∀ i : Fin 5, ∀ d ∈ O (stable i), d.2 ∉ stable i) :
    Function.Injective (fun i => vector O (stable i)) := by
  intro i j heq
  by_contra hij
  have same := same_orientation O (stable i) (stable j) heq
  have avoids_union (d : Edge) (hd : d ∈ O (stable i)) : d.2 ∉ stable i ∪ stable j := by
    intro h
    rcases Finset.mem_union.mp h with hi | hj
    · exact avoid i d hd hi
    · exact avoid j d (same ▸ hd) hj
  obtain ⟨e, he, h₁, h₂⟩ := separate i j hij
  rcases direct i e he with forward | backward
  · exact avoids_union e forward h₂
  · exact avoids_union (e.2, e.1) backward h₁

lemma dimension (S : Set Vector) (f : Fin 5 → Vector) (hinj : Function.Injective f)
    (hf : ∀ i, f i ∈ S) : 3 ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) S) := by
  classical
  let D := vectorSpan (ZMod 2) S
  let shift (i : Fin 5) : D := ⟨f i - f 0, vsub_mem_vectorSpan (ZMod 2) (hf i) (hf 0)⟩
  have injective : Function.Injective shift := by
    intro i j h
    apply hinj
    exact sub_left_injective (show f i - f 0 = f j - f 0 from congrArg Subtype.val h)
  let _ : Fintype D := Fintype.ofFinite D
  have enough : 5 ≤ Fintype.card D := by simpa using Fintype.card_le_of_injective shift injective
  have size : Fintype.card D = 2 ^ Module.finrank (ZMod 2) D := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)]
    simp
  rw [size] at enough
  change 3 ≤ Module.finrank (ZMod 2) D
  by_contra! h
  have small := Nat.pow_le_pow_right (by decide : 0 < 2) (show Module.finrank (ZMod 2) D ≤ 2 by omega)
  omega

end PEqualNP.Outside.L_meta_366

open PEqualNP.Outside.L_meta_366

theorem PEqualNP.Outside.L_meta_366 :
  ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)] → ∀ O : Finset (Fin 5) → Finset (Fin 5 × Fin 5), (∀ J : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) → (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧ (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) → PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) {w : Fin 5 × Fin 5 → ZMod 2 | ∃ J : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  intro E rfl O hypotheses
  apply cover.trans
  apply dimension _ (fun i => vector O (stable i))
  · apply distinguish
    · intro i e he
      exact ((hypotheses (stable i) (independent i)).2.1 e he).1
    · intro i
      exact (hypotheses (stable i) (independent i)).2.2
  · intro i
    exact ⟨stable i, independent i, rfl⟩
