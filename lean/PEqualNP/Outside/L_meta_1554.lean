import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1554

/-- The line number `s` of Z13. -/
def Lf (s : Fin 13) : Finset (Fin 13) := {s, s + 1, s + 3, s + 9}

/-- The set of points where `x` is true. -/
def psi (x : Fin 13 → Bool) : Finset (Fin 13) := Finset.univ.filter fun v => x v = true

theorem mem_psi (x : Fin 13 → Bool) (v : Fin 13) : v ∈ psi x ↔ x v = true := by simp [psi]

theorem psi_inj (x y : Fin 13 → Bool) (h : psi x = psi y) : x = y := by
  funext v
  have := congrArg (fun F => v ∈ F) h
  simp only [mem_psi, eq_iff_iff] at this
  cases hx : x v <;> cases hy : y v <;> simp_all

theorem psi_surj (F : Finset (Fin 13)) : psi (fun v => decide (v ∈ F)) = F := by
  ext v; simp [mem_psi]

theorem card_transport (Q : Finset (Fin 13) → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun x : Fin 13 → Bool => Q (psi x)).card
      = (Finset.univ.filter fun F : Finset (Fin 13) => Q F).card := by
  apply Finset.card_bij (fun x _ => psi x)
  · intro x hx
    simpa using hx
  · intro x _ y _ h; exact psi_inj x y h
  · intro F hF
    refine ⟨fun v => decide (v ∈ F), ?_, psi_surj F⟩
    rw [Finset.mem_filter] at hF ⊢
    exact ⟨Finset.mem_univ _, by rw [psi_surj]; exact hF.2⟩

set_option maxRecDepth 100000 in
theorem count : (Finset.univ.filter (fun F : Finset (Fin 13) =>
    ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), F ⊆ Lf t)).card = 8134 := by
  decide +kernel

/-- The line through 0 that holds a point other than 0. -/
def cls (v : Fin 13) : Fin 13 :=
  if v ∈ Lf 0 then 0 else if v ∈ Lf 4 then 4 else if v ∈ Lf 10 then 10 else 12

theorem cls_mem : ∀ v : Fin 13, v ∈ Lf (cls v) ∧ cls v ∈ ({0, 4, 10, 12} : Finset (Fin 13)) := by
  decide

theorem zero_mem : ∀ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), (0 : Fin 13) ∈ Lf t := by decide

theorem cross_of_cls : ∀ a b : Fin 13, a ≠ 0 → b ≠ 0 → cls a ≠ cls b →
    ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Lf t ∧ b ∈ Lf t := by decide

theorem colines : ∀ t : Fin 13, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Lf t ∧ b ∈ Lf t) ∧ (fun v : Fin 13 => decide (v ∉ Lf t)) a = true ∧ (fun v : Fin 13 => decide (v ∉ Lf t)) b = true) ∧ ∀ p ∈ Lf t, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Lf t ∧ b ∈ Lf t) ∧ (fun v : Fin 13 => decide (v ∉ Lf t ∨ v = p)) a = true ∧ (fun v : Fin 13 => decide (v ∉ Lf t ∨ v = p)) b = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1554

open PEqualNP.Outside.L_meta_1554 in
theorem PEqualNP.Outside.L_meta_1554 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true) ↔ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), ∀ v : Fin 13, x v = true → v ∈ L t) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true))).card = 8134 ∧
    (∀ x y : Fin 13 → Bool, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true) → (∀ v : Fin 13, x v = true → y v = true) → (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ y a = true ∧ y b = true)) ∧
    (∀ t : Fin 13, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v ∉ L t)) a = true ∧ (fun v : Fin 13 => decide (v ∉ L t)) b = true) ∧ ∀ p ∈ L t, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v ∉ L t ∨ v = p)) a = true ∧ (fun v : Fin 13 => decide (v ∉ L t ∨ v = p)) b = true)) := by
  classical
  intro L hL
  have hLf : L = Lf := by funext t; rw [hL t]; rfl
  subst hLf
  have main : ∀ x : Fin 13 → Bool, (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧
      ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Lf t ∧ b ∈ Lf t) ∧ x a = true ∧ x b = true) ↔
      ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), ∀ v : Fin 13, x v = true → v ∈ Lf t := by
    intro x
    constructor
    · rintro ⟨a, b, ⟨_, _, hno⟩, ha, hb⟩ ⟨t, ht, hsub⟩
      exact hno ⟨t, ht, hsub a ha, hsub b hb⟩
    · intro hno
      by_contra hcon
      -- some true point other than 0
      have hex : ∃ a : Fin 13, a ≠ 0 ∧ x a = true := by
        by_contra hne
        push_neg at hne
        apply hno
        refine ⟨0, by decide, fun v hv => ?_⟩
        have : v = 0 := by
          by_contra h0
          have := hne v h0
          rw [hv] at this
          exact absurd this (by simp)
        subst this
        decide
      obtain ⟨a, ha0, ha⟩ := hex
      apply hno
      refine ⟨cls a, (cls_mem a).2, fun v hv => ?_⟩
      by_cases hv0 : v = 0
      · subst hv0; exact zero_mem _ (cls_mem a).2
      · by_cases hc : cls a = cls v
        · rw [hc]; exact (cls_mem v).1
        · exact absurd ⟨a, v, ⟨ha0, hv0, cross_of_cls a v ha0 hv0 hc⟩, ha, hv⟩ hcon
  refine ⟨main, ?_, ?_, colines⟩
  · have e : (Finset.univ.filter (fun x : Fin 13 → Bool => (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧
        ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Lf t ∧ b ∈ Lf t) ∧ x a = true ∧ x b = true)))
        = Finset.univ.filter (fun x : Fin 13 → Bool =>
          ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), psi x ⊆ Lf t) := by
      apply Finset.filter_congr
      intro x _
      rw [main x]
      constructor
      · rintro h ⟨t, ht, hsub⟩
        exact h ⟨t, ht, fun v hv => hsub ((mem_psi x v).2 hv)⟩
      · rintro h ⟨t, ht, hsub⟩
        exact h ⟨t, ht, fun v hv => hsub v ((mem_psi x v).1 hv)⟩
    rw [e, card_transport (fun F => ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), F ⊆ Lf t)]
    exact count
  · rintro x y ⟨a, b, hab, ha, hb⟩ hxy
    exact ⟨a, b, hab, hxy a ha, hxy b hb⟩
