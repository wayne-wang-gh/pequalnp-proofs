import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1541

theorem modlem (N a : ℕ) (h : a < 2 * N) : a % N = if a < N then a else a - N := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The next residue. -/
def s {N : ℕ} (hN : 0 < N) (z : Fin N) : Fin N := ⟨(z.val + 1) % N, Nat.mod_lt _ hN⟩

/-- The previous residue. -/
def r {N : ℕ} (hN : 0 < N) (z : Fin N) : Fin N :=
  if z.val = 0 then ⟨N - 1, by omega⟩ else ⟨z.val - 1, by have := z.isLt; omega⟩

theorem sval {N : ℕ} (hN : 0 < N) (z : Fin N) :
    (s hN z).val = if z.val + 1 < N then z.val + 1 else 0 := by
  have hz := z.isLt
  simp only [s]
  rw [modlem N _ (by omega)]
  split_ifs <;> omega

theorem rval {N : ℕ} (hN : 0 < N) (z : Fin N) :
    (r hN z).val = if z.val = 0 then N - 1 else z.val - 1 := by
  simp only [r]
  split_ifs <;> rfl

theorem rs {N : ℕ} (hN : 0 < N) (z : Fin N) : r hN (s hN z) = z := by
  have hz := z.isLt
  apply Fin.ext
  rw [rval, sval]
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
  split_ifs with h1 h2 h2
  all_goals first | omega | contradiction

theorem s_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : s hN z ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [sval] at this
  split_ifs at this <;> omega

theorem ss_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : s hN (s hN z) ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [sval, sval] at this
  split_ifs at this <;> omega

theorem r_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : r hN z ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [rval] at this
  split_ifs at this <;> omega

theorem rr_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : r hN (r hN z) ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [rval, rval] at this
  split_ifs at this <;> omega

end PEqualNP.Outside.L_meta_1541

open PEqualNP.Outside.L_meta_1541 in
theorem PEqualNP.Outside.L_meta_1541 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)) (w : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = q → w ∈ L i0 → w ∉ T0 →
    ((∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, sigma x ≠ x ∧ sigma (sigma x) ≠ x)) ↔ 3 ≤ q) ∧
    ∀ (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, sigma x ≠ x ∧ sigma (sigma x) ≠ x) → x0 ∈ T0 →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s → B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x}) →
    (∀ s : Fin N, s ≠ i0 → w ∈ L s → ∀ p ∈ L s, B s p = {x0}) →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = false → v ∈ L s)) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  classical
  intro q N L i0 T0 w hq _ hcard hmeet _ hT0 hT0c hw hwT
  have uniq : ∀ s : Fin N, s ≠ i0 → ∀ u ∈ L s, u ∈ L i0 → ∀ u' ∈ L s, u' ∈ L i0 → u = u' := by
    intro s hs u hu hu0 u' hu' hu0'
    exact Finset.card_le_one.1 (hmeet s i0 hs).le u (Finset.mem_inter.2 ⟨hu, hu0⟩) u'
      (Finset.mem_inter.2 ⟨hu', hu0'⟩)
  have hL0 : ∀ v, v ∈ L i0 → v ∈ T0 ∨ v = w := by
    have he : insert w T0 = L i0 := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        rcases Finset.mem_insert.1 hv with rfl | h
        · exact hw
        · exact hT0 h
      · rw [Finset.card_insert_of_notMem hwT, hT0c, hcard]
    intro v hv
    rw [← he] at hv
    rcases Finset.mem_insert.1 hv with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- a line through `w` other than the base line holds no point of `T0`
  have now : ∀ s : Fin N, s ≠ i0 → w ∈ L s → ∀ v ∈ T0, v ∉ L s := by
    intro s hs hws v hv hvs
    exact hwT ((uniq s hs v hvs (hT0 hv) w hws hw) ▸ hv)
  have types : ∀ s : Fin N, s ≠ i0 → (∃ x ∈ T0, x ∈ L s) ∨ w ∈ L s := by
    intro s hs
    obtain ⟨z, hz⟩ := Finset.card_eq_one.1 (hmeet s i0 hs)
    have hzm : z ∈ L s ∩ L i0 := by rw [hz]; simp
    obtain ⟨hzs, hz0⟩ := Finset.mem_inter.1 hzm
    rcases hL0 z hz0 with h | h
    · exact Or.inl ⟨z, h, hzs⟩
    · exact Or.inr (h ▸ hzs)
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨sigma, hmap, _, hno⟩
      by_contra hq3
      have hq2 : q = 2 := by omega
      rw [hq2] at hT0c
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hT0c
      have ha : a ∈ ({a, b} : Finset (Fin N)) := by simp
      have hb : b ∈ ({a, b} : Finset (Fin N)) := by simp
      have h1 : sigma a = b := by
        have := hmap a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · exact absurd h (hno a ha).1
        · exact h
      have h2 : sigma b = a := by
        have := hmap b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · exact h
        · exact absurd h (hno b hb).1
      exact (hno a ha).2 (by rw [h1, h2])
    · intro hq3
      have hqpos : 0 < q := by omega
      let e : T0 ≃ Fin q := Finset.equivFinOfCardEq hT0c
      let sigma : Fin N → Fin N := fun v =>
        if h : v ∈ T0 then ((e.symm (s hqpos (e ⟨v, h⟩)) : T0) : Fin N) else v
      have hs1 : ∀ (v : Fin N) (h : v ∈ T0),
          sigma v = ((e.symm (s hqpos (e ⟨v, h⟩)) : T0) : Fin N) := by
        intro v h; simp only [sigma]; rw [dif_pos h]
      have hmem : ∀ v ∈ T0, sigma v ∈ T0 := by
        intro v h; rw [hs1 v h]; exact (e.symm _).2
      have hcode : ∀ (v : Fin N) (h : v ∈ T0), e ⟨sigma v, hmem v h⟩ = s hqpos (e ⟨v, h⟩) := by
        intro v h
        have : (⟨sigma v, hmem v h⟩ : T0) = e.symm (s hqpos (e ⟨v, h⟩)) := Subtype.ext (hs1 v h)
        rw [this]; simp
      refine ⟨sigma, hmem, ?_, ?_⟩
      · intro x hx y hy hxy
        have hx' : x ∈ T0 := hx
        have hy' : y ∈ T0 := hy
        have h1 : e ⟨sigma x, hmem x hx'⟩ = e ⟨sigma y, hmem y hy'⟩ := by
          congr 1; exact Subtype.ext hxy
        rw [hcode x hx', hcode y hy'] at h1
        have h2 := congrArg (r hqpos) h1
        rw [rs, rs] at h2
        exact congrArg Subtype.val (e.injective h2)
      · intro x hx
        constructor
        · intro h
          have h1 := hcode x hx
          have : (⟨sigma x, hmem x hx⟩ : T0) = ⟨x, hx⟩ := Subtype.ext h
          rw [this] at h1
          exact s_ne hqpos hq3 _ h1.symm
        · intro h
          have h1 := hcode (sigma x) (hmem x hx)
          have : (⟨sigma (sigma x), hmem _ (hmem x hx)⟩ : T0) = ⟨x, hx⟩ := Subtype.ext h
          rw [this, hcode x hx] at h1
          exact ss_ne hqpos hq3 _ h1.symm
  · rintro sigma x0 B ⟨hmap, _, hno⟩ hx0 hB1 hB2
    -- every member of a base is a point of `T0` off the line, of one of two kinds
    have memB : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ v ∈ B s p,
        v ∈ T0 ∧ v ∉ L s ∧ ((∃ x ∈ T0, x ∈ L s ∧ v = sigma x) ∨ w ∈ L s) := by
      intro s hs p hp v hv
      rcases types s hs with ⟨x, hx, hxs⟩ | hws
      · rw [hB1 s hs p hp x hx hxs] at hv
        by_cases hpx : p = x
        · rw [if_pos hpx] at hv; simp at hv
        · rw [if_neg hpx, Finset.mem_singleton] at hv
          subst hv
          refine ⟨hmap x hx, fun hin => ?_, Or.inl ⟨x, hx, hxs, rfl⟩⟩
          exact (hno x hx).1 (uniq s hs _ hin (hT0 (hmap x hx)) x hxs (hT0 hx))
      · rw [hB2 s hs hws p hp, Finset.mem_singleton] at hv
        subst hv
        exact ⟨hx0, now s hs hws _ hx0, Or.inr hws⟩
    constructor
    · intro s hs p hp
      constructor
      · apply Finset.eq_empty_of_forall_notMem
        intro v hv
        rw [Finset.mem_inter] at hv
        exact (memB s hs p hp v hv.1).2.1 hv.2
      · left
        rcases types s hs with ⟨x, hx, hxs⟩ | hws
        · by_cases hpx : p = x
          · exact ⟨x, hx, by simp [hpx]⟩
          · refine ⟨sigma x, hmap x hx, ?_⟩
            rw [hB1 s hs p hp x hx hxs, if_neg hpx]; simp
        · refine ⟨x0, hx0, ?_⟩
          rw [hB2 s hs hws p hp]; simp
    · rintro s s' hs hs' hss ⟨⟨p, hp, v, hv⟩, ⟨p', hp', v', hv'⟩⟩
      rw [Finset.mem_sdiff] at hp hp'
      rw [Finset.mem_inter] at hv hv'
      obtain ⟨hvT, _, hk⟩ := memB s hs p hp.1 v hv.1
      obtain ⟨hvT', _, hk'⟩ := memB s' hs' p' hp'.1 v' hv'.1
      rcases hk with ⟨x, hx, hxs, rfl⟩ | hws
      · rcases hk' with ⟨x', hx', hxs', rfl⟩ | hws'
        · have e1 : sigma x = x' := uniq s' hs' _ hv.2 (hT0 hvT) x' hxs' (hT0 hx')
          have e2 : sigma x' = x := uniq s hs _ hv'.2 (hT0 hvT') x hxs (hT0 hx)
          exact (hno x hx).2 (by rw [e1, e2])
        · exact now s' hs' hws' _ hvT hv.2
      · exact now s hs hws _ hvT' hv'.2
