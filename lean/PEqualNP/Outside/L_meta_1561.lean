import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1561

def Ln (t : Fin 21) : Finset (Fin 21) := {t, t + 1, t + 4, t + 14, t + 16}

def Bb (a : Bool) (s p : Fin 21) : Finset (Fin 21) :=
  if p ∈ ({0, 1, 2} : Finset (Fin 21)) then (∅ : Finset (Fin 21))
  else if (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 then ({0, 1, 2} : Finset (Fin 21)) \ Ln s
  else if (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 then
    (if a then (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).image (fun v : Fin 21 => if v = 2 then 0 else v + 1)
     else (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).image (fun v : Fin 21 => if v = 0 then 2 else v - 1))
  else {0}

def Bf (c : Fin 21 → Bool) (s p : Fin 21) : Finset (Fin 21) := Bb (c s) s p

def cf (a b : Bool) (s s' : Fin 21) : Bool :=
  decide ((∃ p ∈ Ln s \ Ln s', (Bb a s p ∩ Ln s').Nonempty) ∧ (∃ p ∈ Ln s' \ Ln s, (Bb b s' p ∩ Ln s).Nonempty))

def Fc (c : Fin 21 → Bool) : Finset (Fin 21 × Fin 21) :=
  (Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ cf (c e.1) (c e.2) e.1 e.2 = true)

theorem mem_Fc (c : Fin 21 → Bool) (e : Fin 21 × Fin 21) :
    e ∈ Fc c ↔ e.1 < e.2 ∧ cf (c e.1) (c e.2) e.1 e.2 = true := by
  unfold Fc
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem bridge (c : Fin 21 → Bool) (s s' : Fin 21) :
    ((∃ p ∈ Ln s \ Ln s', ((Bf c) s p ∩ Ln s').Nonempty) ∧ (∃ p ∈ Ln s' \ Ln s, ((Bf c) s' p ∩ Ln s).Nonempty)) ↔
      cf (c s) (c s') s s' = true :=
  decide_eq_true_iff.symm

theorem p1 : ∀ s s' : Fin 21, s ≠ s' → (cf true true s s' = true ↔
      (((Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (Ln s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2) ∨
       ((Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (Ln s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ Ln s' ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ Ln s = ∅) ∨
       ((Ln s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ Ln s ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ Ln s' = ∅))) := by
  decide +kernel

theorem card_true : (Fc (fun _ => true)).card = 12 := by
  decide +kernel

theorem mono : ∀ a b : Bool, ∀ s s' : Fin 21, cf true true s s' = true → cf a b s s' = true := by
  decide +kernel

theorem eqT : ∀ a b : Bool, ∀ s s' : Fin 21,
    ((Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → a = true) →
    ((Ln s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → b = true) →
    cf a b s s' = cf true true s s' := by
  decide +kernel

theorem eqF : ∀ a b : Bool, ∀ s s' : Fin 21,
    ((Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → a = false) →
    ((Ln s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → b = false) →
    cf a b s s' = cf true true s s' := by
  decide +kernel

theorem chainP : ∀ e ∈ [((2 : Fin 21), (17 : Fin 21)), (8, 19), (5, 6), (6, 9), (9, 20)], ∀ a b : Bool,
    (cf a b e.1 e.2 = true → cf true true e.1 e.2 = true) → a = true → b = true := by
  decide +kernel

theorem chainQ : ∀ e ∈ [((18 : Fin 21), (20 : Fin 21)), (2, 18), (8, 17), (5, 19)], ∀ a b : Bool,
    (cf a b e.1 e.2 = true → cf true true e.1 e.2 = true) → b = true → a = true := by
  decide +kernel

theorem onesec : ∀ s : Fin 21, (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 →
    s = 20 ∨ s = 18 ∨ s = 2 ∨ s = 17 ∨ s = 8 ∨ s = 19 ∨ s = 5 ∨ s = 6 ∨ s = 9 := by
  decide +kernel

theorem key : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 : Bool,
    (x0 = true → x1 = true) → (x1 = true → x2 = true) → (x2 = true → x3 = true) →
    (x3 = true → x4 = true) → (x4 = true → x5 = true) → (x5 = true → x6 = true) →
    (x6 = true → x7 = true) → (x7 = true → x8 = true) → (x8 = true → x0 = true) →
    (x0 = true ∧ x1 = true ∧ x2 = true ∧ x3 = true ∧ x4 = true ∧ x5 = true ∧ x6 = true ∧ x7 = true ∧ x8 = true) ∨
    (x0 = false ∧ x1 = false ∧ x2 = false ∧ x3 = false ∧ x4 = false ∧ x5 = false ∧ x6 = false ∧ x7 = false ∧ x8 = false) := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 x8 i1 i2 i3 i4 i5 i6 i7 i8 i9
  by_cases h0 : x0 = true
  · have h1 := i1 h0
    have h2 := i2 h1
    have h3 := i3 h2
    have h4 := i4 h3
    have h5 := i5 h4
    have h6 := i6 h5
    have h7 := i7 h6
    have h8 := i8 h7
    exact Or.inl ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · have n8 : x8 ≠ true := fun h => h0 (i9 h)
    have n7 : x7 ≠ true := fun h => n8 (i8 h)
    have n6 : x6 ≠ true := fun h => n7 (i7 h)
    have n5 : x5 ≠ true := fun h => n6 (i6 h)
    have n4 : x4 ≠ true := fun h => n5 (i5 h)
    have n3 : x3 ≠ true := fun h => n4 (i4 h)
    have n2 : x2 ≠ true := fun h => n3 (i3 h)
    have n1 : x1 ≠ true := fun h => n2 (i2 h)
    exact Or.inr ⟨Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr n1, Bool.eq_false_iff.mpr n2,
      Bool.eq_false_iff.mpr n3, Bool.eq_false_iff.mpr n4, Bool.eq_false_iff.mpr n5,
      Bool.eq_false_iff.mpr n6, Bool.eq_false_iff.mpr n7, Bool.eq_false_iff.mpr n8⟩

theorem p3 : ∀ B' : Fin 21 → Fin 21 → Finset (Fin 21), (∀ s p : Fin 21, B' s p ⊆ ({0, 1, 2} : Finset (Fin 21))) →
      ∀ s s' : Fin 21, Ln s ∩ ({0, 1, 2} : Finset (Fin 21)) = ∅ → ¬ ((∃ p ∈ Ln s \ Ln s', (B' s p ∩ Ln s').Nonempty) ∧ (∃ p ∈ Ln s' \ Ln s, (B' s' p ∩ Ln s).Nonempty)) := by
  intro B' hB' s s' hs h
  obtain ⟨_, p, _, x, hx⟩ := h
  rw [Finset.mem_inter] at hx
  have hmem : x ∈ Ln s ∩ ({0, 1, 2} : Finset (Fin 21)) := Finset.mem_inter.mpr ⟨hx.2, hB' s' p hx.1⟩
  rw [hs] at hmem
  simp at hmem

theorem p4 (c : Fin 21 → Bool) : 12 ≤ (Fc c).card ∧ ((Fc c).card = 12 ↔
    ((∀ s : Fin 21, (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = true) ∨
     (∀ s : Fin 21, (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = false))) := by
  have hsub : Fc (fun _ => true) ⊆ Fc c := by
    intro e he
    rw [mem_Fc] at he ⊢
    exact ⟨he.1, mono (c e.1) (c e.2) e.1 e.2 he.2⟩
  have hle : 12 ≤ (Fc c).card := by
    have h := Finset.card_le_card hsub
    rwa [card_true] at h
  refine ⟨hle, ?_, ?_⟩
  · intro h12
    have heq : Fc (fun _ => true) = Fc c :=
      Finset.eq_of_subset_of_card_le hsub (by rw [h12, card_true])
    have H : ∀ s s' : Fin 21, s < s' → cf (c s) (c s') s s' = true → cf true true s s' = true := by
      intro s s' hlt hcf
      have hmem : (s, s') ∈ Fc c := (mem_Fc c (s, s')).mpr ⟨hlt, hcf⟩
      rw [← heq] at hmem
      exact ((mem_Fc _ (s, s')).mp hmem).2
    have i1 : c 20 = true → c 18 = true := chainQ (18, 20) (by decide) (c 18) (c 20) (H 18 20 (by decide))
    have i2 : c 18 = true → c 2 = true := chainQ (2, 18) (by decide) (c 2) (c 18) (H 2 18 (by decide))
    have i3 : c 2 = true → c 17 = true := chainP (2, 17) (by decide) (c 2) (c 17) (H 2 17 (by decide))
    have i4 : c 17 = true → c 8 = true := chainQ (8, 17) (by decide) (c 8) (c 17) (H 8 17 (by decide))
    have i5 : c 8 = true → c 19 = true := chainP (8, 19) (by decide) (c 8) (c 19) (H 8 19 (by decide))
    have i6 : c 19 = true → c 5 = true := chainQ (5, 19) (by decide) (c 5) (c 19) (H 5 19 (by decide))
    have i7 : c 5 = true → c 6 = true := chainP (5, 6) (by decide) (c 5) (c 6) (H 5 6 (by decide))
    have i8 : c 6 = true → c 9 = true := chainP (6, 9) (by decide) (c 6) (c 9) (H 6 9 (by decide))
    have i9 : c 9 = true → c 20 = true := chainP (9, 20) (by decide) (c 9) (c 20) (H 9 20 (by decide))
    rcases key _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 i5 i6 i7 i8 i9 with
      ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · left
      intro s hs
      rcases onesec s hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · right
      intro s hs
      rcases onesec s hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · intro h
    rcases h with h | h
    · have heq : Fc c = Fc (fun _ => true) := by
        ext e
        rw [mem_Fc, mem_Fc]
        exact and_congr Iff.rfl (by rw [eqT (c e.1) (c e.2) e.1 e.2 (h e.1) (h e.2)])
      rw [heq, card_true]
    · have heq : Fc c = Fc (fun _ => true) := by
        ext e
        rw [mem_Fc, mem_Fc]
        exact and_congr Iff.rfl (by rw [eqF (c e.1) (c e.2) e.1 e.2 (h e.1) (h e.2)])
      rw [heq, card_true]

theorem main :
    (∀ s s' : Fin 21, s ≠ s' → (((∃ p ∈ Ln s \ Ln s', ((Bf (fun _ => true)) s p ∩ Ln s').Nonempty) ∧ (∃ p ∈ Ln s' \ Ln s, ((Bf (fun _ => true)) s' p ∩ Ln s).Nonempty)) ↔
      (((Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (Ln s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2) ∨
       ((Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (Ln s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ Ln s' ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ Ln s = ∅) ∨
       ((Ln s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ Ln s ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ Ln s' = ∅)))) ∧
    ((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ Ln e.1 \ Ln e.2, ((Bf (fun _ => true)) e.1 p ∩ Ln e.2).Nonempty) ∧ (∃ p ∈ Ln e.2 \ Ln e.1, ((Bf (fun _ => true)) e.2 p ∩ Ln e.1).Nonempty)))).card = 12 ∧
    (∀ B' : Fin 21 → Fin 21 → Finset (Fin 21), (∀ s p : Fin 21, B' s p ⊆ ({0, 1, 2} : Finset (Fin 21))) →
      ∀ s s' : Fin 21, Ln s ∩ ({0, 1, 2} : Finset (Fin 21)) = ∅ → ¬ ((∃ p ∈ Ln s \ Ln s', (B' s p ∩ Ln s').Nonempty) ∧ (∃ p ∈ Ln s' \ Ln s, (B' s' p ∩ Ln s).Nonempty))) ∧
    (∀ c : Fin 21 → Bool, 12 ≤ ((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ Ln e.1 \ Ln e.2, ((Bf c) e.1 p ∩ Ln e.2).Nonempty) ∧ (∃ p ∈ Ln e.2 \ Ln e.1, ((Bf c) e.2 p ∩ Ln e.1).Nonempty)))).card ∧
      (((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ Ln e.1 \ Ln e.2, ((Bf c) e.1 p ∩ Ln e.2).Nonempty) ∧ (∃ p ∈ Ln e.2 \ Ln e.1, ((Bf c) e.2 p ∩ Ln e.1).Nonempty)))).card = 12 ↔
        ((∀ s : Fin 21, (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = true) ∨ (∀ s : Fin 21, (Ln s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = false)))) := by
  have hF : ∀ c : Fin 21 → Bool, ((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ Ln e.1 \ Ln e.2, ((Bf c) e.1 p ∩ Ln e.2).Nonempty) ∧ (∃ p ∈ Ln e.2 \ Ln e.1, ((Bf c) e.2 p ∩ Ln e.1).Nonempty)))) = Fc c := by
    intro c
    unfold Fc
    exact Finset.filter_congr (fun e _ => and_congr Iff.rfl (bridge c e.1 e.2))
  refine ⟨fun s s' hne => (bridge (fun _ => true) s s').trans (p1 s s' hne), ?_, p3, ?_⟩
  · rw [hF]
    exact card_true
  · intro c
    rw [hF c]
    exact p4 c

end PEqualNP.Outside.L_meta_1561

theorem PEqualNP.Outside.L_meta_1561 : ∀ L : Fin 21 → Finset (Fin 21), (∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16}) →
    ∀ B : (Fin 21 → Bool) → Fin 21 → Fin 21 → Finset (Fin 21),
    (∀ (c : Fin 21 → Bool) (s p : Fin 21), B c s p =
      if p ∈ ({0, 1, 2} : Finset (Fin 21)) then (∅ : Finset (Fin 21))
      else if (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 then ({0, 1, 2} : Finset (Fin 21)) \ L s
      else if (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 then
        (if c s then (L s ∩ ({0, 1, 2} : Finset (Fin 21))).image (fun v : Fin 21 => if v = 2 then 0 else v + 1)
         else (L s ∩ ({0, 1, 2} : Finset (Fin 21))).image (fun v : Fin 21 => if v = 0 then 2 else v - 1))
      else {0}) →
    (∀ s s' : Fin 21, s ≠ s' → (((∃ p ∈ L s \ L s', ((B (fun _ => true)) s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, ((B (fun _ => true)) s' p ∩ L s).Nonempty)) ↔
      (((L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (L s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2) ∨
       ((L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (L s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ L s' ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ L s = ∅) ∨
       ((L s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ L s ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ L s' = ∅)))) ∧
    ((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, ((B (fun _ => true)) e.1 p ∩ L e.2).Nonempty) ∧ (∃ p ∈ L e.2 \ L e.1, ((B (fun _ => true)) e.2 p ∩ L e.1).Nonempty)))).card = 12 ∧
    (∀ B' : Fin 21 → Fin 21 → Finset (Fin 21), (∀ s p : Fin 21, B' s p ⊆ ({0, 1, 2} : Finset (Fin 21))) →
      ∀ s s' : Fin 21, L s ∩ ({0, 1, 2} : Finset (Fin 21)) = ∅ → ¬ ((∃ p ∈ L s \ L s', (B' s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B' s' p ∩ L s).Nonempty))) ∧
    (∀ c : Fin 21 → Bool, 12 ≤ ((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, ((B c) e.1 p ∩ L e.2).Nonempty) ∧ (∃ p ∈ L e.2 \ L e.1, ((B c) e.2 p ∩ L e.1).Nonempty)))).card ∧
      (((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, ((B c) e.1 p ∩ L e.2).Nonempty) ∧ (∃ p ∈ L e.2 \ L e.1, ((B c) e.2 p ∩ L e.1).Nonempty)))).card = 12 ↔
        ((∀ s : Fin 21, (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = true) ∨ (∀ s : Fin 21, (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = false)))) := by
  intro L hL B hB
  obtain rfl : L = PEqualNP.Outside.L_meta_1561.Ln := funext hL
  obtain rfl : B = PEqualNP.Outside.L_meta_1561.Bf := by
    funext c s p
    exact hB c s p
  exact PEqualNP.Outside.L_meta_1561.main
