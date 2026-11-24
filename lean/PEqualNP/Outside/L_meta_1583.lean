import Mathlib.GroupTheory.Perm.Cycle.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1583_aux

lemma cycle_exists {N : ℕ} (T : Finset (Fin N)) :
    ∃ sigma : Fin N → Fin N, (∀ x ∈ T, sigma x ∈ T) ∧ Set.InjOn sigma ↑T ∧
      (∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, sigma^[k] x = y) := by
  classical
  obtain ⟨f, hf, _⟩ := T.exists_cycleOn
  refine ⟨f, hf.1.1, hf.1.2.1, ?_⟩
  intro x hx y hy
  obtain ⟨k, _, hk⟩ := hf.exists_pow_eq hx hy
  exact ⟨k, by simpa only [Equiv.Perm.coe_pow] using hk⟩

lemma no_two_cycle {N : ℕ} (T : Finset (Fin N)) (sigma : Fin N → Fin N)
    (hsize : 3 ≤ T.card)
    (horbit : ∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, sigma^[k] x = y)
    (x : Fin N) (hx : x ∈ T) : sigma (sigma x) ≠ x := by
  intro h2
  have hit : ∀ k : ℕ, sigma^[k] x = x ∨ sigma^[k] x = sigma x := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with hi | hi
      · exact Or.inr (congrArg sigma hi)
      · exact Or.inl ((congrArg sigma hi).trans h2)
  have hsub : T ⊆ {x, sigma x} := by
    intro y hy
    obtain ⟨k, rfl⟩ := horbit x hx y hy
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hit k
  have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
  omega

lemma intersection_point {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 s : Fin N)
    (h : (L s ∩ L i0).card = 1) :
    ∃ r, r ∈ L s ∧ r ∈ L i0 ∧ ∀ x, x ∈ L s → x ∈ L i0 → x = r := by
  obtain ⟨r, heq⟩ := Finset.card_eq_one.mp h
  have hr : r ∈ L s ∩ L i0 := by rw [heq]; simp
  refine ⟨r, (Finset.mem_inter.mp hr).1, (Finset.mem_inter.mp hr).2, ?_⟩
  intro x hs hi
  have hx : x ∈ L s ∩ L i0 := Finset.mem_inter.mpr ⟨hs, hi⟩
  rwa [heq, Finset.mem_singleton] at hx

end PEqualNP.Outside.L_meta_1583_aux

open PEqualNP.Outside.L_meta_1583_aux in
theorem PEqualNP.Outside.L_meta_1583 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)) ∧
    ∀ (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) → x0 ∈ T0 →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s → B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x}) →
    (∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  classical
  intro q m N L i0 T0 hq hm hmq hN hcard hmeet hpairs hT hTm
  refine ⟨cycle_exists T0, ?_⟩
  intro sigma x0 B hsigma hx0 hB1 hB2
  have hsize : 3 ≤ T0.card := by omega
  have htwo := no_two_cycle T0 sigma hsize hsigma.2.2
  have hfixed : ∀ x ∈ T0, sigma x ≠ x := by
    intro x hx he
    apply htwo x hx
    rw [he, he]
  let f : Fin N → Fin N := fun r => if r ∈ T0 then sigma r else x0
  have hfT : ∀ r, f r ∈ T0 := by
    intro r
    by_cases hr : r ∈ T0
    · simpa [f, hr] using hsigma.1 r hr
    · simpa [f, hr] using hx0
  have describe : ∀ s : Fin N, s ≠ i0 → ∃ r : Fin N,
      r ∈ L s ∧ r ∈ L i0 ∧
      (∀ x, x ∈ L s → x ∈ L i0 → x = r) ∧
      ∀ p ∈ L s, B s p = if r ∈ T0 then (if p = r then ∅ else {sigma r}) else {x0} := by
    intro s hsi
    obtain ⟨r, hrs, hri, hu⟩ := intersection_point L i0 s (hmeet s i0 hsi)
    refine ⟨r, hrs, hri, hu, ?_⟩
    intro p hp
    by_cases hr : r ∈ T0
    · simpa [hr] using hB1 s hsi p hp r hr hrs
    · simpa [hr] using hB2 s hsi r (Finset.mem_sdiff.mpr ⟨hri, hr⟩) hrs p hp
  have bases : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s,
      B s p ⊆ T0 ∧ Disjoint (B s p) (L s) ∧ (p ∈ T0 ∨ (B s p).Nonempty) := by
    intro s hsi p hp
    obtain ⟨r, hrs, hri, hu, hb⟩ := describe s hsi
    rw [hb p hp]
    by_cases hr : r ∈ T0
    · rw [if_pos hr]
      by_cases hpr : p = r
      · subst p
        simp [hr]
      · rw [if_neg hpr]
        have hout : sigma r ∉ L s := by
          intro hi
          exact hfixed r hr (hu (sigma r) hi (hT (hsigma.1 r hr)))
        simp [hsigma.1 r hr, hout]
    · rw [if_neg hr]
      have hout : x0 ∉ L s := by
        intro hi
        exact hr ((hu x0 hi (hT hx0)) ▸ hx0)
      simp [hx0, hout]
  refine ⟨?_, ?_⟩
  · intro s hsi p hp
    obtain ⟨hsub, hd, hh⟩ := bases s hsi p hp
    refine ⟨Finset.disjoint_iff_inter_eq_empty.mp hd, Or.inl ?_, ?_⟩
    · rcases hh with hpT | hb
      · exact ⟨p, hpT, by simp⟩
      · obtain ⟨v, hv⟩ := hb
        exact ⟨v, hsub hv, by simp [hv]⟩
    · intro v hv
      simp only [decide_eq_true_eq]
      constructor
      · rintro (he | hb)
        · exact he
        · exact False.elim ((Finset.disjoint_left.mp hd) hb hv)
      · exact Or.inl
  · intro s s' hs hs' hne hconf
    obtain ⟨r, hrs, hri, hu, hb⟩ := describe s hs
    obtain ⟨r', hrs', hri', hu', hb'⟩ := describe s' hs'
    have base_value : ∀ p ∈ L s, ∀ v ∈ B s p, v = f r := by
      intro p hp v hv
      rw [hb p hp] at hv
      by_cases hr : r ∈ T0
      · rw [if_pos hr] at hv
        by_cases he : p = r
        · simp [he] at hv
        · simpa [he, f, hr] using hv
      · simpa [hr, f] using hv
    have base_value' : ∀ p ∈ L s', ∀ v ∈ B s' p, v = f r' := by
      intro p hp v hv
      rw [hb' p hp] at hv
      by_cases hr : r' ∈ T0
      · rw [if_pos hr] at hv
        by_cases he : p = r'
        · simp [he] at hv
        · simpa [he, f, hr] using hv
      · simpa [hr, f] using hv
    obtain ⟨⟨p, hp, v, hv⟩, ⟨p', hp', v', hv'⟩⟩ := hconf
    have hvB := (Finset.mem_inter.mp hv).1
    have hvS := (Finset.mem_inter.mp hv).2
    have hvB' := (Finset.mem_inter.mp hv').1
    have hvS' := (Finset.mem_inter.mp hv').2
    have he : f r = r' := by
      have hvf := base_value p (Finset.mem_sdiff.mp hp).1 v hvB
      exact hvf.symm.trans (hu' v hvS (hT (hvf.symm ▸ hfT r)))
    have he' : f r' = r := by
      have hvf := base_value' p' (Finset.mem_sdiff.mp hp').1 v' hvB'
      exact hvf.symm.trans (hu v' hvS' (hT (hvf.symm ▸ hfT r')))
    have hr' : r' ∈ T0 := he ▸ hfT r
    have hr : r ∈ T0 := he' ▸ hfT r'
    have he0 : sigma r = r' := by simpa [f, hr] using he
    have he1 : sigma r' = r := by simpa [f, hr'] using he'
    exact htwo r hr (by rw [he0, he1])
