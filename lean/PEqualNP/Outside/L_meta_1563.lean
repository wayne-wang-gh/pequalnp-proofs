import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563

/-- The line number `s` of Z13. -/
def Lf (s : Fin 13) : Finset (Fin 13) := {s, s + 1, s + 3, s + 9}

/-- The set of points where `x` is false. -/
def phi (x : Fin 13 → Bool) : Finset (Fin 13) := Finset.univ.filter fun v => x v = false

theorem mem_phi (x : Fin 13 → Bool) (v : Fin 13) : v ∈ phi x ↔ x v = false := by simp [phi]

theorem phi_inj (x y : Fin 13 → Bool) (h : phi x = phi y) : x = y := by
  funext v
  have := congrArg (fun F => v ∈ F) h
  simp only [mem_phi, eq_iff_iff] at this
  cases hx : x v <;> cases hy : y v <;> simp_all

theorem phi_surj (F : Finset (Fin 13)) : phi (fun v => decide (v ∉ F)) = F := by
  ext v; simp [mem_phi]

theorem card_transport (Q : Finset (Fin 13) → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun x : Fin 13 → Bool => Q (phi x)).card
      = (Finset.univ.filter fun F : Finset (Fin 13) => Q F).card := by
  apply Finset.card_bij (fun x _ => phi x)
  · intro x hx
    simpa using hx
  · intro x _ y _ h; exact phi_inj x y h
  · intro F hF
    refine ⟨fun v => decide (v ∉ F), ?_, phi_surj F⟩
    rw [Finset.mem_filter] at hF ⊢
    exact ⟨Finset.mem_univ _, by rw [phi_surj]; exact hF.2⟩

set_option maxRecDepth 100000 in
theorem count_all : (Finset.univ.filter (fun F : Finset (Fin 13) =>
    (0 : Fin 13) ∉ F ∨ (1 : Fin 13) ∉ F ∨ F ⊆ Lf 0)).card = 6148 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem count_01 : (Finset.univ.filter (fun F : Finset (Fin 13) =>
    (0 : Fin 13) ∉ F ∨ (1 : Fin 13) ∉ F)).card = 6144 := by
  decide +kernel

theorem zero_cases : ∀ v : Fin 13, v ∈ Lf 0 → v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 9 := by decide

theorem colines : ∀ t : Fin 13, (decide ((0 : Fin 13) ∉ Lf t) = true ∨
    decide ((1 : Fin 13) ∉ Lf t) = true ∨ ∀ v : Fin 13, v ∉ Lf 0 → decide (v ∉ Lf t) = true) := by
  decide +kernel

theorem t_iff (x : Fin 13 → Bool) (v : Fin 13) : x v = true ↔ v ∉ phi x := by
  rw [mem_phi]; cases x v <;> simp

theorem off_iff (x : Fin 13 → Bool) :
    (∀ v : Fin 13, v ∉ Lf 0 → x v = true) ↔ phi x ⊆ Lf 0 := by
  constructor
  · intro h v hv
    by_contra hne
    rw [mem_phi, h v hne] at hv
    exact absurd hv (by simp)
  · intro h v hv
    by_contra hne
    exact hv (h ((mem_phi x v).2 (by simpa using hne)))

end PEqualNP.Outside.L_meta_1563

open PEqualNP.Outside.L_meta_1563 in
theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  classical
  intro L hL
  have hLf : L = Lf := by funext t; rw [hL t]; rfl
  subst hLf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y h hxy
    rcases h with h | h | h
    · exact Or.inl (hxy 0 h)
    · exact Or.inr (Or.inl (hxy 1 h))
    · exact Or.inr (Or.inr fun v hv => hxy v (h v hv))
  · have e : (Finset.univ.filter (fun x : Fin 13 → Bool =>
        (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ Lf 0 → x v = true)))
        = Finset.univ.filter (fun x : Fin 13 → Bool =>
          (0 : Fin 13) ∉ phi x ∨ (1 : Fin 13) ∉ phi x ∨ phi x ⊆ Lf 0) := by
      apply Finset.filter_congr
      intro x _
      rw [t_iff x 0, t_iff x 1, off_iff]
    rw [e, card_transport (fun F => (0 : Fin 13) ∉ F ∨ (1 : Fin 13) ∉ F ∨ F ⊆ Lf 0)]
    exact count_all
  · exact colines
  · have e : (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true))
        = Finset.univ.filter (fun x : Fin 13 → Bool =>
          (0 : Fin 13) ∉ phi x ∨ (1 : Fin 13) ∉ phi x) := by
      apply Finset.filter_congr
      intro x _
      rw [t_iff x 0, t_iff x 1]
    rw [e, card_transport (fun F => (0 : Fin 13) ∉ F ∨ (1 : Fin 13) ∉ F)]
    exact count_01
  · intro x
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · cases h0 : x 0
        · cases h1 : x 1
          · right; right
            have key : ∀ (e : Fin 13 → Bool), e 0 = false → e 1 = false → e 3 = x 3 → e 9 = x 9 →
                (∀ v, v ∉ Lf 0 → e v = true) → x = e := by
              intro e e0 e1 e3 e9 eo
              funext v
              by_cases hv : v ∈ Lf 0
              · rcases zero_cases v hv with rfl | rfl | rfl | rfl
                · rw [h0, e0]
                · rw [h1, e1]
                · rw [e3]
                · rw [e9]
              · rw [h v hv, eo v hv]
            have m0 : (0 : Fin 13) ∈ Lf 0 := by decide
            have m1 : (1 : Fin 13) ∈ Lf 0 := by decide
            have m3 : (3 : Fin 13) ∈ Lf 0 := by decide
            have m9 : (9 : Fin 13) ∈ Lf 0 := by decide
            cases h3 : x 3 <;> cases h9 : x 9
            · left
              exact key _ (by simp [m0]) (by simp [m1]) (by simp [m3, h3]) (by simp [m9, h9])
                (fun v hv => by simp [hv])
            · right; right; left
              exact key _ (by simp [m0]) (by simp [m1]) (by simp [m3, h3])
                (by simp [h9]) (fun v hv => by simp [hv])
            · right; left
              exact key _ (by simp [m0]) (by simp [m1]) (by simp [h3])
                (by simp [m9, h9]) (fun v hv => by simp [hv])
            · right; right; right
              exact key _ (by simp [m0]) (by simp [m1]) (by simp [h3])
                (by simp [h9]) (fun v hv => by simp [hv])
          · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
    · rintro (h | h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      all_goals
        right; right
        intro v hv
        rw [h]
        simp [hv]
