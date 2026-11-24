import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_369_aux

private abbrev E7 : List (Fin 7 × Fin 7) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6)]

private abbrev IsInd (J : Finset (Fin 7)) : Prop :=
  ∀ f ∈ E7, ¬ (f.1 ∈ J ∧ f.2 ∈ J)

private theorem vc_E7_le_four : PEqualNP.MetaComplexity.SingleLevel.vc E7 ≤ 4 := by
  unfold PEqualNP.MetaComplexity.SingleLevel.vc
  exact Nat.sInf_le ⟨({0, 2, 4, 6} : Finset (Fin 7)), by decide, by decide⟩

private def projMap : (Fin 7 × Fin 7 → ZMod 2) →ₗ[ZMod 2] (Fin 7 → ZMod 2) where
  toFun w i := w (i, i + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def dot (α x : Fin 7 → ZMod 2) : ZMod 2 :=
  ∑ i : Fin 7, α i * x i

private theorem edge_mem_E7 (i : Fin 7) : (i, i + 1) ∈ E7 ∨ (i + 1, i) ∈ E7 := by
  fin_cases i <;> decide

private theorem cyc_edge_val (O : Finset (Fin 7) → Finset (Fin 7 × Fin 7))
    (hO : ∀ J : Finset (Fin 7), IsInd J →
      (∀ d ∈ O J, d ∈ E7 ∨ (d.2, d.1) ∈ E7) ∧
      (∀ e ∈ E7, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧
      (∀ d ∈ O J, d.2 ∉ J))
    (J : Finset (Fin 7)) (hJ : IsInd J) (i : Fin 7) :
    (i ∈ J → (if (i, i + 1) ∈ O J then (1 : ZMod 2) else 0) = 1) ∧
    (i + 1 ∈ J → (if (i, i + 1) ∈ O J then (1 : ZMod 2) else 0) = 0) := by
  have hspec := hO J hJ
  have hcov : ((i, i + 1) ∈ O J ∨ (i + 1, i) ∈ O J) := by
    rcases edge_mem_E7 i with h1 | h2
    · exact (hspec.2.1 (i, i + 1) h1).1
    · exact (hspec.2.1 (i + 1, i) h2).1.symm
  constructor
  · intro hi
    have hnot : (i + 1, i) ∉ O J := fun h => hspec.2.2 (i + 1, i) h hi
    have hin : (i, i + 1) ∈ O J := hcov.resolve_right hnot
    simp [hin]
  · intro hi1
    have hnot : (i, i + 1) ∉ O J := fun h => hspec.2.2 (i, i + 1) h hi1
    simp [hnot]

private def evalDual (W : Submodule (ZMod 2) (Fin 7 → ZMod 2)) :
    (Fin 7 → ZMod 2) →ₗ[ZMod 2] (W →ₗ[ZMod 2] ZMod 2) where
  toFun α :=
    { toFun := fun x => dot α x.1
      map_add' := fun x y => by
        simp only [dot, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [dot, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring) }
  map_add' α β := by
    ext x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, dot, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
  map_smul' c α := by
    ext x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, dot, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)

private theorem finrank_ker_add_finrank_ge (W : Submodule (ZMod 2) (Fin 7 → ZMod 2)) :
    7 ≤ Module.finrank (ZMod 2) (LinearMap.ker (evalDual W)) + Module.finrank (ZMod 2) W := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (evalDual W)
  have hdom : Module.finrank (ZMod 2) (Fin 7 → ZMod 2) = 7 := by simp
  have hrange : Module.finrank (ZMod 2) (LinearMap.range (evalDual W)) ≤
      Module.finrank (ZMod 2) (W →ₗ[ZMod 2] ZMod 2) :=
    Submodule.finrank_le _
  have hdual : Module.finrank (ZMod 2) (W →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) W := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  omega

private def coordTriple (a b c : Fin 7) : (Fin 7 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun α j := match j.val with | 0 => α a | 1 => α b | _ => α c
  map_add' _ _ := by
    funext j; fin_cases j <;> rfl
  map_smul' _ _ := by
    funext j; fin_cases j <;> rfl

private theorem finrank_ker_coordTriple_ge (a b c : Fin 7) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.ker (coordTriple a b c)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (coordTriple a b c)
  have hdom : Module.finrank (ZMod 2) (Fin 7 → ZMod 2) = 7 := by simp
  have hrange : Module.finrank (ZMod 2) (LinearMap.range (coordTriple a b c)) ≤ 3 := by
    have h1 : Module.finrank (ZMod 2) (LinearMap.range (coordTriple a b c)) ≤
        Module.finrank (ZMod 2) (Fin 3 → ZMod 2) := Submodule.finrank_le _
    simpa [Module.finrank_fin_fun] using h1
  omega

private theorem exists_nonzero_inter (U Z : Submodule (ZMod 2) (Fin 7 → ZMod 2))
    (hU : 4 ≤ Module.finrank (ZMod 2) U) (hZ : 4 ≤ Module.finrank (ZMod 2) Z) :
    ∃ α : Fin 7 → ZMod 2, α ∈ U ∧ α ∈ Z ∧ α ≠ 0 := by
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq U Z
  have hsup : Module.finrank (ZMod 2) (U ⊔ Z : Submodule (ZMod 2) (Fin 7 → ZMod 2)) ≤ 7 := by
    have h1 := Submodule.finrank_le (U ⊔ Z : Submodule (ZMod 2) (Fin 7 → ZMod 2))
    simpa [Module.finrank_fin_fun] using h1
  have hpos : 0 < Module.finrank (ZMod 2) (U ⊓ Z : Submodule (ZMod 2) (Fin 7 → ZMod 2)) := by
    omega
  have hne : (U ⊓ Z : Submodule (ZMod 2) (Fin 7 → ZMod 2)) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    omega
  obtain ⟨α, hα_mem, hα_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨α, hα_mem.1, hα_mem.2, hα_ne⟩

private theorem ind_J1 (k : Fin 7) : IsInd ({k + 1, k + 3, k + 6} : Finset (Fin 7)) := by
  fin_cases k <;> decide

private theorem ind_J2 (k : Fin 7) : IsInd ({k + 1, k + 4, k + 6} : Finset (Fin 7)) := by
  fin_cases k <;> decide

private theorem ind_J3 (k : Fin 7) : IsInd ({k + 1, k + 5} : Finset (Fin 7)) := by
  fin_cases k <;> decide

private theorem ind_J4 (k : Fin 7) : IsInd ({k + 1, k + 6} : Finset (Fin 7)) := by
  fin_cases k <;> decide

private theorem ind_J5 (k : Fin 7) : IsInd ({k, k + 2} : Finset (Fin 7)) := by
  fin_cases k <;> decide

private theorem ind_J6 (k : Fin 7) : IsInd ({k + 1} : Finset (Fin 7)) := by
  fin_cases k <;> decide

private theorem sum_shift (k : Fin 7) (f : Fin 7 → ZMod 2) :
    ∑ i : Fin 7, f i =
      f k + f (k + 1) + f (k + 2) + f (k + 3) + f (k + 4) + f (k + 5) + f (k + 6) := by
  have hbi : ∑ i : Fin 7, f i = ∑ i : Fin 7, f (k + i) := by
    refine Fintype.sum_equiv (Equiv.addLeft k).symm _ _ (fun i => ?_)
    simp
  rw [hbi, Fin.sum_univ_seven]
  simp only [Fin.isValue, add_zero]

private theorem pair_mem_ker (O : Finset (Fin 7) → Finset (Fin 7 × Fin 7))
    (hO : ∀ J : Finset (Fin 7), IsInd J →
      (∀ d ∈ O J, d ∈ E7 ∨ (d.2, d.1) ∈ E7) ∧
      (∀ e ∈ E7, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧
      (∀ d ∈ O J, d.2 ∉ J))
    (U : Submodule (ZMod 2) (Fin 7 → ZMod 2))
    (hdot : ∀ α ∈ U, ∀ J1 J2 : Finset (Fin 7), IsInd J1 → IsInd J2 →
      dot α (fun i => if (i, i + 1) ∈ O J1 then 1 else 0) =
      dot α (fun i => if (i, i + 1) ∈ O J2 then 1 else 0))
    (hU : 4 ≤ Module.finrank (ZMod 2) U)
    (k : Fin 7) :
    (fun i : Fin 7 => if i = k ∨ i = k + 1 then (1 : ZMod 2) else 0) ∈ U := by
  let Z := LinearMap.ker (coordTriple (k + 2) (k + 4) (k + 6))
  have hZ : 4 ≤ Module.finrank (ZMod 2) Z := finrank_ker_coordTriple_ge (k + 2) (k + 4) (k + 6)
  obtain ⟨α, hαU, hαZ, hαne⟩ := exists_nonzero_inter U Z hU hZ
  have hz_eq : coordTriple (k + 2) (k + 4) (k + 6) α = 0 := LinearMap.mem_ker.mp hαZ
  have h2 : α (k + 2) = 0 := congrFun hz_eq 0
  have h4 : α (k + 4) = 0 := congrFun hz_eq 1
  have h6 : α (k + 6) = 0 := congrFun hz_eq 2
  have hv := fun J hJ i => cyc_edge_val O hO J hJ i
  -- Step 1: kill α (k + 3) using J1 = {k+1, k+3, k+6} and J2 = {k+1, k+4, k+6}
  have h3 : α (k + 3) = 0 := by
    have heq := hdot α hαU {k + 1, k + 3, k + 6} {k + 1, k + 4, k + 6} (ind_J1 k) (ind_J2 k)
    unfold dot at heq
    rw [sum_shift k, sum_shift k] at heq
    have ha0 : (if (k, k + 1) ∈ O {k + 1, k + 3, k + 6} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J1 k) k).2 (by simp)
    have ha1 : (if (k + 1, k + 1 + 1) ∈ O {k + 1, k + 3, k + 6} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ (ind_J1 k) (k + 1)).1 (by simp)
    have ha3 : (if (k + 3, k + 3 + 1) ∈ O {k + 1, k + 3, k + 6} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ (ind_J1 k) (k + 3)).1 (by simp)
    have ha5 : (if (k + 5, k + 5 + 1) ∈ O {k + 1, k + 3, k + 6} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J1 k) (k + 5)).2 (by rw [add_assoc]; simp)
    have hb0 : (if (k, k + 1) ∈ O {k + 1, k + 4, k + 6} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J2 k) k).2 (by simp)
    have hb1 : (if (k + 1, k + 1 + 1) ∈ O {k + 1, k + 4, k + 6} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ (ind_J2 k) (k + 1)).1 (by simp)
    have hb3 : (if (k + 3, k + 3 + 1) ∈ O {k + 1, k + 4, k + 6} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J2 k) (k + 3)).2 (by rw [add_assoc]; simp)
    have hb5 : (if (k + 5, k + 5 + 1) ∈ O {k + 1, k + 4, k + 6} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J2 k) (k + 5)).2 (by rw [add_assoc]; simp)
    simp only [h2, h4, h6, ha0, ha1, ha3, ha5, hb0, hb1, hb3, hb5,
      mul_zero, mul_one, zero_mul, add_zero, zero_add] at heq
    have := congrArg (fun x => x - α (k + 1)) heq
    simpa using this
  -- Step 2: kill α (k + 5) using J3 = {k+1, k+5} and J4 = {k+1, k+6}
  have h5 : α (k + 5) = 0 := by
    have heq := hdot α hαU {k + 1, k + 5} {k + 1, k + 6} (ind_J3 k) (ind_J4 k)
    unfold dot at heq
    rw [sum_shift k, sum_shift k] at heq
    have ha0 : (if (k, k + 1) ∈ O {k + 1, k + 5} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J3 k) k).2 (by simp)
    have ha1 : (if (k + 1, k + 1 + 1) ∈ O {k + 1, k + 5} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ (ind_J3 k) (k + 1)).1 (by simp)
    have ha5 : (if (k + 5, k + 5 + 1) ∈ O {k + 1, k + 5} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ (ind_J3 k) (k + 5)).1 (by simp)
    have hb0 : (if (k, k + 1) ∈ O {k + 1, k + 6} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J4 k) k).2 (by simp)
    have hb1 : (if (k + 1, k + 1 + 1) ∈ O {k + 1, k + 6} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ (ind_J4 k) (k + 1)).1 (by simp)
    have hb5 : (if (k + 5, k + 5 + 1) ∈ O {k + 1, k + 6} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J4 k) (k + 5)).2 (by rw [add_assoc]; simp)
    simp only [h2, h3, h4, h6, ha0, ha1, ha5, hb0, hb1, hb5,
      mul_zero, mul_one, zero_mul, add_zero, zero_add] at heq
    have := congrArg (fun x => x - α (k + 1)) heq
    simpa using this
  -- Step 3: force α k = α (k + 1) using J5 = {k, k+2} and J6 = {k+1}
  have h01 : α k = α (k + 1) := by
    have heq := hdot α hαU {k, k + 2} {k + 1} (ind_J5 k) (ind_J6 k)
    unfold dot at heq
    rw [sum_shift k, sum_shift k] at heq
    have ha0 : (if (k, k + 1) ∈ O {k, k + 2} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ (ind_J5 k) k).1 (by simp)
    have ha1 : (if (k + 1, k + 1 + 1) ∈ O {k, k + 2} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J5 k) (k + 1)).2 (by rw [add_assoc]; simp)
    have hb0 : (if (k, k + 1) ∈ O {k + 1} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ (ind_J6 k) k).2 (by simp)
    have hb1 : (if (k + 1, k + 1 + 1) ∈ O {k + 1} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ (ind_J6 k) (k + 1)).1 (by simp)
    simp only [h2, h3, h4, h5, h6, ha0, ha1, hb0, hb1,
      mul_zero, mul_one, zero_mul, add_zero, zero_add] at heq
    exact heq
  -- Step 4: since α ≠ 0 and ZMod 2 has only 0 and 1, α k = 1 and α = indicator of {k, k+1}
  have h01_val : α k = 0 ∨ α k = 1 :=
    (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (α k)
  have hk_one : α k = 1 := by
    rcases h01_val with hαk | hαk
    · exfalso
      apply hαne
      funext i
      have hi : i = k ∨ i = k + 1 ∨ i = k + 2 ∨ i = k + 3 ∨ i = k + 4 ∨ i = k + 5 ∨ i = k + 6 := by
        fin_cases k <;> fin_cases i <;> decide
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hαk
      · rw [← h01]; exact hαk
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h6
    · exact hαk
  have hα_eq : α = (fun i : Fin 7 => if i = k ∨ i = k + 1 then (1 : ZMod 2) else 0) := by
    funext i
    have hi : i = k ∨ i = k + 1 ∨ i = k + 2 ∨ i = k + 3 ∨ i = k + 4 ∨ i = k + 5 ∨ i = k + 6 := by
      fin_cases k <;> fin_cases i <;> decide
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [hk_one]
    · simp [← h01, hk_one]
    · simp [h2]
    · simp [h3]
    · simp [h4]
    · simp [h5]
    · simp [h6]
  rwa [← hα_eq]

theorem main_thm (O : Finset (Fin 7) → Finset (Fin 7 × Fin 7))
    (hO : ∀ J : Finset (Fin 7), IsInd J →
      (∀ d ∈ O J, d ∈ E7 ∨ (d.2, d.1) ∈ E7) ∧
      (∀ e ∈ E7, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧
      (∀ d ∈ O J, d.2 ∉ J)) :
    PEqualNP.MetaComplexity.SingleLevel.vc E7 ≤
      Module.finrank (ZMod 2)
        (vectorSpan (ZMod 2)
          {w : Fin 7 × Fin 7 → ZMod 2 |
            ∃ J : Finset (Fin 7), IsInd J ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  let S : Set (Fin 7 × Fin 7 → ZMod 2) :=
    {w | ∃ J : Finset (Fin 7), IsInd J ∧ w = fun d => if d ∈ O J then 1 else 0}
  let V : Submodule (ZMod 2) (Fin 7 × Fin 7 → ZMod 2) := vectorSpan (ZMod 2) S
  let W : Submodule (ZMod 2) (Fin 7 → ZMod 2) := V.map projMap
  let U : Submodule (ZMod 2) (Fin 7 → ZMod 2) := LinearMap.ker (evalDual W)
  have hvc : PEqualNP.MetaComplexity.SingleLevel.vc E7 ≤ 4 := vc_E7_le_four
  have hmap : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) V :=
    Submodule.finrank_map_le projMap V
  have hrn : 7 ≤ Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) W :=
    finrank_ker_add_finrank_ge W
  have hdot : ∀ α ∈ U, ∀ J1 J2 : Finset (Fin 7), IsInd J1 → IsInd J2 →
      dot α (fun i => if (i, i + 1) ∈ O J1 then 1 else 0) =
      dot α (fun i => if (i, i + 1) ∈ O J2 then 1 else 0) := by
    intro α hα J1 J2 hJ1 hJ2
    have hw1 : (fun d => if d ∈ O J1 then (1 : ZMod 2) else 0) ∈ S := ⟨J1, hJ1, rfl⟩
    have hw2 : (fun d => if d ∈ O J2 then (1 : ZMod 2) else 0) ∈ S := ⟨J2, hJ2, rfl⟩
    have hdiffV : (fun d => if d ∈ O J1 then (1 : ZMod 2) else 0) -
        (fun d => if d ∈ O J2 then (1 : ZMod 2) else 0) ∈ V :=
      vsub_mem_vectorSpan (ZMod 2) hw1 hw2
    have hdiffW : projMap ((fun d => if d ∈ O J1 then (1 : ZMod 2) else 0) -
        (fun d => if d ∈ O J2 then (1 : ZMod 2) else 0)) ∈ W :=
      Submodule.mem_map_of_mem hdiffV
    have hzero : dot α (projMap ((fun d => if d ∈ O J1 then (1 : ZMod 2) else 0) -
        (fun d => if d ∈ O J2 then (1 : ZMod 2) else 0))) = 0 := by
      have hk := LinearMap.mem_ker.mp hα
      have hk' := LinearMap.congr_fun hk ⟨_, hdiffW⟩
      exact hk'
    have hsub : dot α (projMap ((fun d => if d ∈ O J1 then (1 : ZMod 2) else 0) -
        (fun d => if d ∈ O J2 then (1 : ZMod 2) else 0))) =
        dot α (fun i => if (i, i + 1) ∈ O J1 then 1 else 0) -
        dot α (fun i => if (i, i + 1) ∈ O J2 then 1 else 0) := by
      simp only [dot, map_sub, projMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
        mul_sub, Finset.sum_sub_distrib]
    rw [hsub] at hzero
    exact sub_eq_zero.mp hzero
  have hUle : Module.finrank (ZMod 2) U ≤ 3 := by
    by_contra hgt
    push Not at hgt
    have hp0 := pair_mem_ker O hO U hdot hgt 0
    have hp1 := pair_mem_ker O hO U hdot hgt 1
    have hsum0 : (fun i : Fin 7 => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) +
        (fun i : Fin 7 => if i = 1 ∨ i = 2 then (1 : ZMod 2) else 0) ∈ U :=
      U.add_mem hp0 hp1
    have hsum_eq : (fun i : Fin 7 => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) +
        (fun i : Fin 7 => if i = 1 ∨ i = 2 then (1 : ZMod 2) else 0) =
        (fun i : Fin 7 => if i = 0 ∨ i = 2 then (1 : ZMod 2) else 0) := by
      funext i; fin_cases i <;> decide
    have hsum : (fun i : Fin 7 => if i = 0 ∨ i = 2 then (1 : ZMod 2) else 0) ∈ U :=
      hsum_eq ▸ hsum0
    have hJ02 : IsInd ({0, 2} : Finset (Fin 7)) := by decide
    have hJ03 : IsInd ({0, 3} : Finset (Fin 7)) := by decide
    have heq := hdot _ hsum {0, 2} {0, 3} hJ02 hJ03
    have hv := fun J hJ i => cyc_edge_val O hO J hJ i
    have ha0 : (if ((0 : Fin 7), (1 : Fin 7)) ∈ O {0, 2} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ hJ02 0).1 (by simp)
    have ha2 : (if ((2 : Fin 7), (2 : Fin 7) + 1) ∈ O {0, 2} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ hJ02 2).1 (by simp)
    have hb0 : (if ((0 : Fin 7), (1 : Fin 7)) ∈ O {0, 3} then (1 : ZMod 2) else 0) = 1 :=
      (hv _ hJ03 0).1 (by simp)
    have hb2 : (if ((2 : Fin 7), (2 : Fin 7) + 1) ∈ O {0, 3} then (1 : ZMod 2) else 0) = 0 :=
      (hv _ hJ03 2).2 (by decide)
    unfold dot at heq
    rw [Fin.sum_univ_seven, Fin.sum_univ_seven] at heq
    have h1 : (if (1 : Fin 7) = 0 ∨ (1 : Fin 7) = 2 then (1 : ZMod 2) else 0) = 0 := by decide
    have h3' : (if (3 : Fin 7) = 0 ∨ (3 : Fin 7) = 2 then (1 : ZMod 2) else 0) = 0 := by decide
    have h4' : (if (4 : Fin 7) = 0 ∨ (4 : Fin 7) = 2 then (1 : ZMod 2) else 0) = 0 := by decide
    have h5' : (if (5 : Fin 7) = 0 ∨ (5 : Fin 7) = 2 then (1 : ZMod 2) else 0) = 0 := by decide
    have h6' : (if (6 : Fin 7) = 0 ∨ (6 : Fin 7) = 2 then (1 : ZMod 2) else 0) = 0 := by decide
    simp only [Fin.isValue, true_or, or_true, ↓reduceIte, h1, h3', h4', h5', h6',
      ha0, ha2, hb0, hb2, zero_mul, mul_zero, mul_one, add_zero, zero_add] at heq
    revert heq; decide
  change PEqualNP.MetaComplexity.SingleLevel.vc E7 ≤ Module.finrank (ZMod 2) V
  omega

end PEqualNP.Outside.L_meta_369_aux

theorem PEqualNP.Outside.L_meta_369 : ∀ E : List (Fin 7 × Fin 7), E = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6)] → ∀ O : Finset (Fin 7) → Finset (Fin 7 × Fin 7), (∀ J : Finset (Fin 7), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) → (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧ (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) → PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) {w : Fin 7 × Fin 7 → ZMod 2 | ∃ J : Finset (Fin 7), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  intro E hE O hO
  subst hE
  exact PEqualNP.Outside.L_meta_369_aux.main_thm O hO
