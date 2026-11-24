import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1719_aux

open Finset

lemma two_lines {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (l m : Fin N) (hlm : l ≠ m) :
    (univ.filter (fun u => I u l ∧ I u m)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  exact hlm ((hu a b hab).unique ⟨ha.1, hb.1⟩ ⟨ha.2, hb.2⟩)

lemma lines_through {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p : Fin N) :
    (univ.filter (fun l => I p l)).card ≤ q + 1 := by
  have h1 : ∀ l ∈ univ.filter (fun l => I p l),
      (univ.filter (fun x => I x l ∧ x ≠ p)).card = q := by
    intro l hl'
    have hpl : I p l := by simpa using hl'
    have he : univ.filter (fun x => I x l ∧ x ≠ p) = (univ.filter (fun x => I x l)).erase p := by
      ext x
      simp [and_comm]
    rw [he, Finset.card_erase_of_mem (by simpa using hpl), hl l]
    simp
  have hdisj : (↑(univ.filter (fun l => I p l)) : Set (Fin N)).PairwiseDisjoint
      (fun l => univ.filter (fun x => I x l ∧ x ≠ p)) := by
    intro l hl' m hm' hlm
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl' hm'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx2
    exact hlm ((hu x p hx.2).unique ⟨hx.1, hl'⟩ ⟨hx2.1, hm'⟩)
  have hc := Finset.card_biUnion hdisj
  rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul] at hc
  have hsub : (univ.filter (fun l => I p l)).biUnion
      (fun l => univ.filter (fun x => I x l ∧ x ≠ p)) ⊆ univ.erase p := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨l, _, hx⟩ := hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_erase.mpr ⟨hx.2.2, Finset.mem_univ _⟩
  have h3 := Finset.card_le_card hsub
  have h4 : N - 1 = q ^ 2 + q := by
    rw [hN, Nat.add_sub_cancel]
  rw [hc, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
    h4] at h3
  by_contra hcon
  push_neg at hcon
  nlinarith

end PEqualNP.Outside.L_meta_1719_aux

open Finset PEqualNP.Outside.L_meta_1719_aux in
theorem PEqualNP.Outside.L_meta_1719 : ∀ (q131 N131 r131 : ℕ) (I131 : Fin N131 → Fin N131 → Prop) [DecidableRel I131] (S131 W131 : Finset (Fin N131)), 2 ≤ q131 → N131 = q131 ^ 2 + q131 + 1 → (∀ l131f : Fin N131, (Finset.univ.filter (fun p131b => I131 p131b l131f)).card = q131 + 1) → (∀ pa131 pb131 : Fin N131, pa131 ≠ pb131 → ∃! lb131 : Fin N131, I131 pa131 lb131 ∧ I131 pb131 lb131) → (∀ (pz131 : Fin N131) (T131 : Finset (Fin N131)), T131.card ≤ r131 → (W131 \ W131.filter (fun l131 => ¬ I131 pz131 l131 ∧ l131 ∉ T131)).card ≤ q131 + 1 + r131 ∧ ∀ l131b ∈ W131.filter (fun l131a => ¬ I131 pz131 l131a ∧ l131a ∉ T131), (S131.filter (fun u131 => I131 u131 l131b)).card ≤ ((S131.filter (fun u131a => u131a ≠ pz131 ∧ ∀ m131 ∈ T131, ¬ I131 u131a m131)).filter (fun u131b => I131 u131b l131b)).card + r131) ∧ (∀ (wz131 : Fin N131) (Q131 : Finset (Fin N131)), Q131.card ≤ r131 → (W131 \ W131.filter (fun l131c => l131c ≠ wz131 ∧ ∀ p131 ∈ Q131, ¬ I131 p131 l131c)).card ≤ 1 + r131 * (q131 + 1) ∧ ∀ l131e ∈ W131.filter (fun l131d => l131d ≠ wz131 ∧ ∀ p131a ∈ Q131, ¬ I131 p131a l131d), (S131.filter (fun u131c => I131 u131c l131e)).card ≤ ((S131.filter (fun u131d => ¬ I131 u131d wz131 ∧ u131d ∉ Q131)).filter (fun u131e => I131 u131e l131e)).card + 1) := by
  intro q N r I _ S W hq hN hl hu
  refine ⟨fun pz T hT => ⟨?_, ?_⟩, fun wz Q hQ => ⟨?_, ?_⟩⟩
  · refine (Finset.card_le_card (t := univ.filter (fun l => I pz l) ∪ T) ?_).trans ?_
    · intro l hl'
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
        true_and] at hl' ⊢
      by_contra h
      push_neg at h
      exact hl'.2 ⟨hl'.1, h.1, h.2⟩
    · have h1 := lines_through I hq hN hl hu pz
      have h2 := Finset.card_union_le (univ.filter (fun l => I pz l)) T
      omega
  · intro l hl'
    rw [Finset.mem_filter] at hl'
    obtain ⟨_, hpl, hlT⟩ := hl'
    refine (Finset.card_le_card (t := ((S.filter (fun u => u ≠ pz ∧ ∀ m ∈ T, ¬ I u m)).filter
      (fun u => I u l)) ∪ T.biUnion (fun m => univ.filter (fun u => I u l ∧ I u m))) ?_).trans ?_
    · intro u hu'
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
        true_and] at hu' ⊢
      by_cases h : ∀ m ∈ T, ¬ I u m
      · left
        refine ⟨⟨hu'.1, ?_, h⟩, hu'.2⟩
        intro e
        rw [e] at hu'
        exact hpl hu'.2
      · right
        push_neg at h
        obtain ⟨m, hm, hum⟩ := h
        exact ⟨m, hm, hu'.2, hum⟩
    · refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
      have h1 := Finset.card_biUnion_le_card_mul T
        (fun m => univ.filter (fun u => I u l ∧ I u m)) 1
        (fun m hm => two_lines I hu l m (fun e => hlT (e ▸ hm)))
      omega
  · refine (Finset.card_le_card (t := {wz} ∪ Q.biUnion (fun p => univ.filter (fun l => I p l))) ?_).trans ?_
    · intro l hl'
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_biUnion, Finset.mem_univ, true_and] at hl' ⊢
      by_contra h
      push_neg at h
      exact hl'.2 ⟨hl'.1, h.1, fun p hp => h.2 p hp⟩
    · refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_singleton]
      refine Nat.add_le_add_left ?_ _
      exact (Finset.card_biUnion_le_card_mul Q (fun p => univ.filter (fun l => I p l)) (q + 1)
        (fun p _ => lines_through I hq hN hl hu p)).trans (Nat.mul_le_mul_right _ hQ)
  · intro l hl'
    rw [Finset.mem_filter] at hl'
    obtain ⟨_, hlw, hlQ⟩ := hl'
    refine (Finset.card_le_card (t := ((S.filter (fun u => ¬ I u wz ∧ u ∉ Q)).filter
      (fun u => I u l)) ∪ univ.filter (fun u => I u l ∧ I u wz)) ?_).trans ?_
    · intro u hu'
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hu' ⊢
      by_cases h : I u wz
      · right
        exact ⟨hu'.2, h⟩
      · left
        exact ⟨⟨hu'.1, h, fun hq' => hlQ u hq' hu'.2⟩, hu'.2⟩
    · exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (two_lines I hu l wz hlw) _)
