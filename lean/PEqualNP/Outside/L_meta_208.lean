import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_208 :
    PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 2 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 1 := by
  let f (x : Fin 2 → Bool) := x 0 && x 1
  let ones := fun _ : Fin 2 => true
  have accepts (x) : f x = true ↔ x = ones := by
    simp [f, ones, funext_iff, Fin.forall_fin_two]
  have total (τ) (valid : IsTyping 2 f τ) :
      (∑ i : Fin 2, ∑ b : Bool, (typedMatrix 2 f τ i b).rank) = 2 := by
    have negative (i) : typedMatrix 2 f τ i false = 0 := by
      ext x y
      by_cases hx : f x = true
      · obtain rfl := (accepts x).mp hx
        simp [typedMatrix, ones]
      · simp [typedMatrix, hx]
    have positive (i) : (typedMatrix 2 f τ i true).rank = 1 := by
      let M := typedMatrix 2 f τ i true
      apply le_antisymm
      · apply le_trans (M.rank_le_card_of_support_subset {ones} ?_) (by simp)
        apply Function.support_subset_iff'.mpr
        intro x hx
        have h : f x ≠ true := fun h => hx (by simpa using (accepts x).mp h)
        funext y
        simp [M, Matrix.row, typedMatrix, h]
      · let y (j : Fin 2) := decide (j ≠ i)
        have hy : f y = false := by fin_cases i <;> rfl
        obtain ⟨j, hj, hd⟩ := valid ones y rfl hy
        have : j = i := by simpa [ones, y] using hd
        subst j
        have entry : M ones y = 1 := ite_eq_left ⟨rfl, hy, hj, rfl⟩
        have sub : M.submatrix (fun _ : Unit => ones) (fun _ : Unit => y) = 1 := by
          ext a b
          simpa [Matrix.submatrix_apply, Matrix.one_apply] using entry
        simpa [sub] using M.rank_submatrix_le (fun _ : Unit => ones) (fun _ : Unit => y)
    simp [negative, positive]
  have valid : IsTyping 2 f (fun _ y => if y 0 then 1 else 0) := by
    intro x y hx hy
    obtain rfl := (accepts x).mp hx
    cases h : y 0 with
    | false => exact ⟨0, by simp [h], by simp [ones, h]⟩
    | true => exact ⟨1, by simp [h], by simpa [ones, f, h] using hy⟩
  refine ⟨⟨_, valid, (total _ valid).le⟩, ?_⟩
  rintro ⟨τ, ht, h⟩
  exact Nat.not_succ_le_self 1 ((total τ ht).ge.trans h)
