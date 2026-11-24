import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_142

open PEqualNP.MetaComplexity

def F (x : Fin 5 → Bool) : Bool :=
  (x 0 && (x 1 || x 2)) || ((x 1 || x 2) && x 3) || (x 3 && x 4)

def occ : DMFormula 5 → Fin 5 → ℕ
  | DMFormula.lit j _, i => if j = i then 1 else 0
  | DMFormula.and A B, i => occ A i + occ B i
  | DMFormula.or A B, i => occ A i + occ B i

lemma leaves_eq (φ : DMFormula 5) : φ.leaves = ∑ i, occ φ i := by
  induction φ with
  | lit j b => simp [DMFormula.leaves, occ]
  | and A B ha hb => simp [DMFormula.leaves, occ, Finset.sum_add_distrib, ha, hb]
  | or A B ha hb => simp [DMFormula.leaves, occ, Finset.sum_add_distrib, ha, hb]

lemma eval_congr (φ : DMFormula 5) (x y : Fin 5 → Bool)
    (h : ∀ i, 0 < occ φ i → x i = y i) : φ.eval x = φ.eval y := by
  induction φ with
  | lit j b =>
    have : x j = y j := h j (by simp [occ])
    simp [DMFormula.eval, this]
  | and A B ha hb =>
    simp only [DMFormula.eval]
    rw [ha (fun i hi => h i (by simp [occ]; omega)), hb (fun i hi => h i (by simp [occ]; omega))]
  | or A B ha hb =>
    simp only [DMFormula.eval]
    rw [ha (fun i hi => h i (by simp [occ]; omega)), hb (fun i hi => h i (by simp [occ]; omega))]

lemma exists_occ (φ : DMFormula 5) : ∃ i, 0 < occ φ i := by
  induction φ with
  | lit j b => exact ⟨j, by simp [occ]⟩
  | and A B ha hb => obtain ⟨i, hi⟩ := ha; exact ⟨i, by simp [occ]; omega⟩
  | or A B ha hb => obtain ⟨i, hi⟩ := ha; exact ⟨i, by simp [occ]; omega⟩

lemma dep (i : Fin 5) : ∃ x : Fin 5 → Bool, F x ≠ F (Function.update x i (!x i)) := by
  fin_cases i
  · exact ⟨![false, true, false, false, false], by decide⟩
  · exact ⟨![true, false, false, false, false], by decide⟩
  · exact ⟨![true, false, false, false, false], by decide⟩
  · exact ⟨![false, false, false, false, true], by decide⟩
  · exact ⟨![false, false, false, true, false], by decide⟩

lemma kor_b : ∀ s0 s1 s2 s3 s4 : Bool, (s0 || s1 || s2 || s3 || s4) = true →
    (s0 && s1 && s2 && s3 && s4) = false →
    ∃ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool, F ![a0, a1, a2, a3, a4] = false ∧
      F ![b0, b1, b2, b3, b4] = false ∧
      F ![if s0 then a0 else b0, if s1 then a1 else b1, if s2 then a2 else b2,
        if s3 then a3 else b3, if s4 then a4 else b4] = true := by
  decide +kernel

lemma kand_b : ∀ s0 s1 s2 s3 s4 : Bool, (s0 || s1 || s2 || s3 || s4) = true →
    (s0 && s1 && s2 && s3 && s4) = false →
    ∃ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool, F ![a0, a1, a2, a3, a4] = true ∧
      F ![b0, b1, b2, b3, b4] = true ∧
      F ![if s0 then a0 else b0, if s1 then a1 else b1, if s2 then a2 else b2,
        if s3 then a3 else b3, if s4 then a4 else b4] = false := by
  decide +kernel

lemma vec5 (z : Fin 5 → Bool) : z = ![z 0, z 1, z 2, z 3, z 4] := by
  funext i; fin_cases i <;> rfl

lemma mix_eq (s z1 z2 : Fin 5 → Bool) :
    (fun i => if s i then z1 i else z2 i) =
      ![if s 0 then z1 0 else z2 0, if s 1 then z1 1 else z2 1, if s 2 then z1 2 else z2 2,
        if s 3 then z1 3 else z2 3, if s 4 then z1 4 else z2 4] := by
  funext i; fin_cases i <;> rfl

lemma or_split (s : Fin 5 → Bool) (h1 : ∃ i, s i = true) (h2 : ∃ j, s j = false) :
    ∃ z1 z2 : Fin 5 → Bool, F z1 = false ∧ F z2 = false ∧
      F (fun i => if s i then z1 i else z2 i) = true := by
  have hs1 : (s 0 || s 1 || s 2 || s 3 || s 4) = true := by
    obtain ⟨i, hi⟩ := h1; fin_cases i <;> simp_all
  have hs2 : (s 0 && s 1 && s 2 && s 3 && s 4) = false := by
    obtain ⟨i, hi⟩ := h2; fin_cases i <;> simp_all
  obtain ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, e1, e2, e3⟩ :=
    kor_b (s 0) (s 1) (s 2) (s 3) (s 4) hs1 hs2
  refine ⟨![a0, a1, a2, a3, a4], ![b0, b1, b2, b3, b4], e1, e2, ?_⟩
  rw [mix_eq]; exact e3

lemma and_split (s : Fin 5 → Bool) (h1 : ∃ i, s i = true) (h2 : ∃ j, s j = false) :
    ∃ z1 z2 : Fin 5 → Bool, F z1 = true ∧ F z2 = true ∧
      F (fun i => if s i then z1 i else z2 i) = false := by
  have hs1 : (s 0 || s 1 || s 2 || s 3 || s 4) = true := by
    obtain ⟨i, hi⟩ := h1; fin_cases i <;> simp_all
  have hs2 : (s 0 && s 1 && s 2 && s 3 && s 4) = false := by
    obtain ⟨i, hi⟩ := h2; fin_cases i <;> simp_all
  obtain ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, e1, e2, e3⟩ :=
    kand_b (s 0) (s 1) (s 2) (s 3) (s 4) hs1 hs2
  refine ⟨![a0, a1, a2, a3, a4], ![b0, b1, b2, b3, b4], e1, e2, ?_⟩
  rw [mix_eq]; exact e3

lemma lower (φ : DMFormula 5) (hφ : ∀ x, φ.eval x = F x) : 6 ≤ φ.leaves := by
  by_contra hlt
  have hall : ∀ i, 0 < occ φ i := by
    intro i
    by_contra h0
    obtain ⟨x, hx⟩ := dep i
    apply hx
    rw [← hφ, ← hφ]
    exact eval_congr φ _ _ (fun j hj => by
      have : j ≠ i := by rintro rfl; omega
      simp [Function.update, this])
  have hsum := leaves_eq φ
  rw [Fin.sum_univ_five] at hsum
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  have h3 := hall 3
  have h4 := hall 4
  cases φ with
  | lit j b => simp [DMFormula.leaves] at hsum; omega
  | and A B =>
    have hone : ∀ i, occ A i + occ B i = 1 := by
      have g : ∀ k, 0 < occ A k + occ B k := fun k => by simpa [occ] using hall k
      have g0 := g 0
      have g1 := g 1
      have g2 := g 2
      have g3 := g 3
      have g4 := g 4
      have hs : (DMFormula.and A B).leaves = occ A 0 + occ B 0 + (occ A 1 + occ B 1) +
          (occ A 2 + occ B 2) + (occ A 3 + occ B 3) + (occ A 4 + occ B 4) := by
        simpa [occ] using hsum
      intro i
      fin_cases i <;> simp <;> omega
    obtain ⟨i, hi⟩ := exists_occ A
    obtain ⟨j, hj⟩ := exists_occ B
    obtain ⟨z1, z2, e1, e2, e3⟩ := and_split (fun k => decide (0 < occ A k))
      ⟨i, by simpa using hi⟩ ⟨j, by have := hone j; simp; omega⟩
    have hA : (DMFormula.and A B).eval z1 = true := by rw [hφ]; exact e1
    have hB : (DMFormula.and A B).eval z2 = true := by rw [hφ]; exact e2
    have hm := hφ (fun k => if decide (0 < occ A k) then z1 k else z2 k)
    simp only [DMFormula.eval, Bool.and_eq_true] at hA hB hm
    rw [eval_congr A _ z1 (fun k hk => by simp [hk]),
      eval_congr B _ z2 (fun k hk => by have := hone k; simp; omega), hA.1, hB.2, e3] at hm
    simp at hm
  | or A B =>
    have hone : ∀ i, occ A i + occ B i = 1 := by
      have g : ∀ k, 0 < occ A k + occ B k := fun k => by simpa [occ] using hall k
      have g0 := g 0
      have g1 := g 1
      have g2 := g 2
      have g3 := g 3
      have g4 := g 4
      have hs : (DMFormula.or A B).leaves = occ A 0 + occ B 0 + (occ A 1 + occ B 1) +
          (occ A 2 + occ B 2) + (occ A 3 + occ B 3) + (occ A 4 + occ B 4) := by
        simpa [occ] using hsum
      intro i
      fin_cases i <;> simp <;> omega
    obtain ⟨i, hi⟩ := exists_occ A
    obtain ⟨j, hj⟩ := exists_occ B
    obtain ⟨z1, z2, e1, e2, e3⟩ := or_split (fun k => decide (0 < occ A k))
      ⟨i, by simpa using hi⟩ ⟨j, by have := hone j; simp; omega⟩
    have hA : (DMFormula.or A B).eval z1 = false := by rw [hφ]; exact e1
    have hB : (DMFormula.or A B).eval z2 = false := by rw [hφ]; exact e2
    have hm := hφ (fun k => if decide (0 < occ A k) then z1 k else z2 k)
    simp only [DMFormula.eval, Bool.or_eq_false_iff] at hA hB hm
    rw [eval_congr A _ z1 (fun k hk => by simp [hk]),
      eval_congr B _ z2 (fun k hk => by have := hone k; simp; omega), hA.1, hB.2, e3] at hm
    simp at hm

def phi6 : DMFormula 5 :=
  DMFormula.or
    (DMFormula.and (DMFormula.or (DMFormula.lit 1 true) (DMFormula.lit 2 true))
      (DMFormula.or (DMFormula.lit 0 true) (DMFormula.lit 3 true)))
    (DMFormula.and (DMFormula.lit 3 true) (DMFormula.lit 4 true))

lemma phi6_eval (x : Fin 5 → Bool) : phi6.eval x = F x := by
  rw [vec5 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  revert b0 b1 b2 b3 b4
  decide

end PEqualNP.Outside.L_meta_142

open PEqualNP.Outside.L_meta_142

theorem PEqualNP.Outside.L_meta_142 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 5 (fun x : Fin 5 → Bool => (x 0 && (x 1 || x 2)) || ((x 1 || x 2) && x 3) || (x 3 && x 4)) s ↔ 6 ≤ s := by
  intro s
  constructor
  · rintro ⟨φ, hl, hφ⟩
    have := lower φ hφ
    omega
  · intro hs
    exact ⟨phi6, by simp [phi6, PEqualNP.MetaComplexity.DMFormula.leaves]; omega, phi6_eval⟩
