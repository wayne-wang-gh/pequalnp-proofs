import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1560

def L0 : Fin 21 → Finset (Fin 21) := fun t => {t, t + 1, t + 4, t + 14, t + 16}

def e (a : Fin 21) : Fin 21 → Bool := fun v => decide (v = a)

def pr (a s : Fin 21) : Fin 21 → Bool := fun v => decide (v = a ∨ v = s)

def co (t : Fin 21) : Fin 21 → Bool := fun v => decide (v ∉ L0 t)

theorem self_mem : ∀ a : Fin 21, a ∈ L0 a := by decide +kernel

theorem sep : ∀ a s : Fin 21, a ≠ s → ∃ t, s ∈ L0 t ∧ a ∉ L0 t := by decide +kernel

theorem line_inj : ∀ t u : Fin 21, t ≠ u → ∃ v, v ∈ L0 t ∧ v ∉ L0 u := by decide +kernel

theorem off3 : ∀ t a s : Fin 21, ∃ v, v ≠ a ∧ v ≠ s ∧ v ∉ L0 t := by decide +kernel

theorem part1 (T : Finset (Fin 21)) (hT : ∀ t : Fin 21, ¬ T ⊆ L0 t)
    (f : (Fin 21 → Bool) → Bool)
    (hf : ∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) → f x = true → f y = true)
    (t : Fin 21) :
    ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ L0 t, x v = true)) ↔
          ((∀ a ∈ T ∩ L0 t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
           (∀ a ∈ T \ L0 t, ∀ s ∈ L0 t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
           f (fun v : Fin 21 => decide (v ∉ L0 t)) = false)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_inter] at ha
      have h1 := h (fun v : Fin 21 => decide (v = a)) ⟨a, ha.1, by simp⟩
      rw [h1]
      exact decide_eq_true ⟨a, ha.2, by simp⟩
    · intro a ha s hs
      rw [Finset.mem_sdiff] at ha hs
      have h1 := h (fun v : Fin 21 => decide (v = a ∨ v = s)) ⟨a, ha.1, by simp⟩
      rw [h1]
      exact decide_eq_true ⟨s, hs.1, by simp⟩
    · obtain ⟨v, hvT, hv⟩ := Finset.not_subset.mp (hT t)
      have h1 := h (fun v : Fin 21 => decide (v ∉ L0 t)) ⟨v, hvT, by simpa using hv⟩
      rw [h1]
      apply decide_eq_false
      rintro ⟨w, hw, hw2⟩
      have hw3 : w ∉ L0 t := by simpa using hw2
      exact hw3 hw
  · rintro ⟨ha, hb, hc⟩ x ⟨v, hvT, hxv⟩
    by_cases hex : ∃ s ∈ L0 t, x s = true
    · rw [decide_eq_true hex]
      obtain ⟨s, hs, hxs⟩ := hex
      by_cases hvL : v ∈ L0 t
      · refine hf _ x ?_ (ha v (Finset.mem_inter.mpr ⟨hvT, hvL⟩))
        intro w hw
        have hwv : w = v := by simpa using hw
        rw [hwv]
        exact hxv
      · by_cases hsT : s ∈ T
        · refine hf _ x ?_ (ha s (Finset.mem_inter.mpr ⟨hsT, hs⟩))
          intro w hw
          have hws : w = s := by simpa using hw
          rw [hws]
          exact hxs
        · refine hf _ x ?_ (hb v (Finset.mem_sdiff.mpr ⟨hvT, hvL⟩) s (Finset.mem_sdiff.mpr ⟨hs, hsT⟩))
          intro w hw
          have hws : w = v ∨ w = s := by simpa using hw
          rcases hws with h1 | h1
          · rw [h1]
            exact hxv
          · rw [h1]
            exact hxs
    · rw [decide_eq_false hex]
      cases hfx : f x with
      | false => rfl
      | true =>
        have h2 : f (fun v : Fin 21 => decide (v ∉ L0 t)) = true := by
          refine hf x _ ?_ hfx
          intro w hw
          apply decide_eq_true
          intro hwL
          exact hex ⟨w, hwL, hw⟩
        rw [hc] at h2
        exact absurd h2 (by simp)

theorem e_inj : Function.Injective e := by
  intro a b h
  have h1 : e a a = e b a := congrFun h a
  have h2 : e a a = true := by simp [e]
  rw [h2] at h1
  simpa [e] using h1.symm

theorem co_inj : Function.Injective co := by
  intro t u h
  by_contra hne
  obtain ⟨v, hv1, hv2⟩ := line_inj t u hne
  have h1 : co t v = co u v := congrFun h v
  have h2 : co t v = false := by simp [co, hv1]
  have h3 : co u v = true := by simp [co, hv2]
  rw [h2, h3] at h1
  exact absurd h1 (by simp)

theorem pr_injOn (T : Finset (Fin 21)) :
    Set.InjOn (fun q : Fin 21 × Fin 21 => pr q.1 q.2) (↑(T ×ˢ Tᶜ) : Set (Fin 21 × Fin 21)) := by
  rintro ⟨a, s⟩ h1 ⟨a', s'⟩ h2 h
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_compl] at h1 h2
  have e1 : a = a' ∨ a = s' := by
    have h3 : pr a s a = pr a' s' a := congrFun h a
    have h4 : pr a s a = true := by simp [pr]
    rw [h4] at h3
    simpa [pr] using h3.symm
  have e2 : s = a' ∨ s = s' := by
    have h3 : pr a s s = pr a' s' s := congrFun h s
    have h4 : pr a s s = true := by simp [pr]
    rw [h4] at h3
    simpa [pr] using h3.symm
  have ha : a = a' := by
    rcases e1 with h3 | h3
    · exact h3
    · exact absurd (by rw [← h3]; exact h1.1) h2.2
  have hs : s = s' := by
    rcases e2 with h3 | h3
    · exact absurd (by rw [h3]; exact h2.1) h1.2
    · exact h3
  rw [ha, hs]

theorem cntA (T : Finset (Fin 21)) :
    Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ L0 t, x = e a) = T.image e := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨t, a, ⟨haT, -⟩, rfl⟩
    exact ⟨a, haT, rfl⟩
  · rintro ⟨a, haT, rfl⟩
    exact ⟨a, a, ⟨haT, self_mem a⟩, rfl⟩

theorem cntB (T : Finset (Fin 21)) :
    Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ L0 t, ∃ s ∈ L0 t \ T, x = pr a s)
      = (T ×ˢ Tᶜ).image (fun q : Fin 21 × Fin 21 => pr q.1 q.2) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_sdiff,
    Finset.mem_product, Finset.mem_compl, Prod.exists]
  constructor
  · rintro ⟨t, a, ⟨haT, -⟩, s, ⟨-, hsT⟩, rfl⟩
    exact ⟨a, s, ⟨haT, hsT⟩, rfl⟩
  · rintro ⟨a, s, ⟨haT, hsT⟩, rfl⟩
    have hne : a ≠ s := by
      intro h
      exact hsT (h ▸ haT)
    obtain ⟨t, hs, ha⟩ := sep a s hne
    exact ⟨t, a, ⟨haT, ha⟩, s, ⟨hs, hsT⟩, rfl⟩

theorem cntC :
    Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = co t) = Finset.univ.image co := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

theorem cardA (T : Finset (Fin 21)) : (T.image e).card = T.card :=
  Finset.card_image_of_injective T e_inj

theorem cardB (T : Finset (Fin 21)) :
    ((T ×ˢ Tᶜ).image (fun q : Fin 21 × Fin 21 => pr q.1 q.2)).card = T.card * (21 - T.card) := by
  rw [Finset.card_image_of_injOn (pr_injOn T), Finset.card_product, Finset.card_compl, Fintype.card_fin]

theorem cardC : (Finset.univ.image co).card = 21 := by
  rw [Finset.card_image_of_injective _ co_inj, Finset.card_univ, Fintype.card_fin]

theorem dAB (T : Finset (Fin 21)) :
    Disjoint (T.image e) ((T ×ˢ Tᶜ).image (fun q : Fin 21 × Fin 21 => pr q.1 q.2)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨⟨a', s⟩, hq, hEq⟩ := hx'
  simp only [Finset.mem_product, Finset.mem_compl] at hq
  have h1 : pr a' s a' = e a a' := congrFun hEq a'
  have h2 : pr a' s s = e a s := congrFun hEq s
  have h3 : pr a' s a' = true := by simp [pr]
  have h4 : pr a' s s = true := by simp [pr]
  rw [h3] at h1
  rw [h4] at h2
  have h5 : a' = a := by simpa [e] using h1.symm
  have h6 : s = a := by simpa [e] using h2.symm
  exact hq.2 (by rw [h6, ← h5]; exact hq.1)

theorem dAC (T : Finset (Fin 21)) : Disjoint (T.image e) (Finset.univ.image co) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨t, -, hEq⟩ := hx'
  obtain ⟨v, hva, -, hvt⟩ := off3 t a a
  have h1 : co t v = e a v := congrFun hEq v
  have h2 : co t v = true := by simp [co, hvt]
  have h3 : e a v = false := by simp [e, hva]
  rw [h2, h3] at h1
  exact absurd h1 (by simp)

theorem dBC (T : Finset (Fin 21)) :
    Disjoint ((T ×ˢ Tᶜ).image (fun q : Fin 21 × Fin 21 => pr q.1 q.2)) (Finset.univ.image co) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨⟨a, s⟩, -, rfl⟩ := hx
  obtain ⟨t, -, hEq⟩ := hx'
  obtain ⟨v, hva, hvs, hvt⟩ := off3 t a s
  have h1 : co t v = pr a s v := congrFun hEq v
  have h2 : co t v = true := by simp [co, hvt]
  have h3 : pr a s v = false := by simp [pr, hva, hvs]
  rw [h2, h3] at h1
  exact absurd h1 (by simp)

theorem cntAll (T : Finset (Fin 21)) :
    Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, (∃ a ∈ T ∩ L0 t, x = e a) ∨
      (∃ a ∈ T \ L0 t, ∃ s ∈ L0 t \ T, x = pr a s) ∨ x = co t)
    = Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ L0 t, x = e a) ∪
      (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ L0 t, ∃ s ∈ L0 t \ T, x = pr a s) ∪
       Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = co t)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨t, h | h | h⟩
    · exact Or.inl ⟨t, h⟩
    · exact Or.inr (Or.inl ⟨t, h⟩)
    · exact Or.inr (Or.inr ⟨t, h⟩)
  · rintro (⟨t, h⟩ | ⟨t, h⟩ | ⟨t, h⟩)
    · exact ⟨t, Or.inl h⟩
    · exact ⟨t, Or.inr (Or.inl h)⟩
    · exact ⟨t, Or.inr (Or.inr h)⟩

theorem cardAll (T : Finset (Fin 21)) (hT3 : T.card = 3) :
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, (∃ a ∈ T ∩ L0 t, x = e a) ∨
      (∃ a ∈ T \ L0 t, ∃ s ∈ L0 t \ T, x = pr a s) ∨ x = co t)).card = 78 := by
  rw [cntAll, cntA, cntB, cntC,
    Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨dAB T, dAC T⟩),
    Finset.card_union_of_disjoint (dBC T), cardA, cardB, cardC, hT3]

end PEqualNP.Outside.L_meta_1560

theorem PEqualNP.Outside.L_meta_1560 : ∀ L : Fin 21 → Finset (Fin 21), (∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16}) →
    ∀ T : Finset (Fin 21), T.card = 3 → (∀ t : Fin 21, ¬ T ⊆ L t) →
    (∀ f : (Fin 21 → Bool) → Bool,
      (∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) → f x = true → f y = true) →
      ∀ t : Fin 21,
        ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ L t, x v = true)) ↔
          ((∀ a ∈ T ∩ L t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
           (∀ a ∈ T \ L t, ∀ s ∈ L t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
           f (fun v : Fin 21 => decide (v ∉ L t)) = false))) ∧
    (∀ t : Fin 21, ∃ v ∈ T, v ∉ L t) ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a)))).card = 3 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ L t, ∃ s ∈ L t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s)))).card = 54 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 21 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, (∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ L t, ∃ s ∈ L t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 78 := by
  intro L hL T hT3 hT
  obtain rfl : L = PEqualNP.Outside.L_meta_1560.L0 := funext hL
  refine ⟨fun f hf t => PEqualNP.Outside.L_meta_1560.part1 T hT f hf t,
    fun t => Finset.not_subset.mp (hT t), ?_, ?_, ?_, ?_⟩
  · exact ((congrArg Finset.card (PEqualNP.Outside.L_meta_1560.cntA T)).trans
      (PEqualNP.Outside.L_meta_1560.cardA T)).trans hT3
  · refine ((congrArg Finset.card (PEqualNP.Outside.L_meta_1560.cntB T)).trans
      (PEqualNP.Outside.L_meta_1560.cardB T)).trans ?_
    rw [hT3]
  · exact (congrArg Finset.card PEqualNP.Outside.L_meta_1560.cntC).trans
      PEqualNP.Outside.L_meta_1560.cardC
  · exact PEqualNP.Outside.L_meta_1560.cardAll T hT3
