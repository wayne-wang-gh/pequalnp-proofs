import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1721

theorem arith1 (s q k m : ℕ) (hs : s ≤ q + 1) (hmq : m ≤ q) (hmk : m ≤ k) :
    s * m ≤ q * min (s - 1) k + m := by
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · subst h0
    simp
  · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hs' : s' ≤ q := by omega
    have e : (s' + 1) * m = s' * m + m := by ring
    rw [Nat.add_sub_cancel, e]
    rcases le_total s' k with h | h
    · rw [min_eq_left h]
      have h1 : s' * m ≤ q * s' := by
        rw [Nat.mul_comm q s']
        exact Nat.mul_le_mul_left _ hmq
      omega
    · rw [min_eq_right h]
      have h1 : s' * m ≤ q * k := Nat.mul_le_mul hs' hmk
      omega

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

end PEqualNP.Outside.L_meta_1721

theorem PEqualNP.Outside.L_meta_1721 : (∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size) → (∀ (q20 N20 k20 : ℕ) (I20 : Fin N20 → Fin N20 → Prop) [DecidableRel I20] (C20 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q20 → N20 = q20 ^ 2 + q20 + 1 → (∀ l20c : Fin N20, (Finset.univ.filter (fun p20f => I20 p20f l20c)).card = q20 + 1) → (∀ pa20 pb20 : Fin N20, pa20 ≠ pb20 → ∃! lb20 : Fin N20, I20 pa20 lb20 ∧ I20 pb20 lb20) → 1 ≤ k20 → (∀ g20 ∈ C20.gates, (g20.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N20 + N20) C20 → (∀ j20 < C20.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.Ico N20 (N20 + N20))).getD i20 0 = 0) ∨ (∀ h20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.range N20)).getD h20 0 = 0)) → (∀ p20g l20d : Fin N20, I20 p20g l20d → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 (fun i20a => decide (i20a = Fin.castAdd N20 p20g ∨ i20a = Fin.natAdd N20 l20d)) = true) → (∀ z20 : Fin (N20 + N20) → Bool, (Finset.univ.filter (fun l20e : Fin N20 => z20 (Fin.natAdd N20 l20e) = true)).card ≤ k20 → (¬ ∃ p20h l20f : Fin N20, I20 p20h l20f ∧ z20 (Fin.castAdd N20 p20h) = true ∧ z20 (Fin.natAdd N20 l20f) = true) → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 z20 = false) → ∃ (X20 Y20 : PEqualNP.CircuitLowerBounds.Circuit) (ps20 rh20 : Fin N20 → ℕ), ((∀ g20a ∈ X20.gates, (g20a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 X20) ∧ ((∀ g20b ∈ Y20.gates, (g20b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 Y20) ∧ X20.size + Y20.size ≤ 5 * C20.size ∧ (∀ w20 p20 : Fin N20, (X20.wires (List.ofFn (fun a20 => decide (a20 = p20)))).getD (ps20 w20) false = true → I20 p20 w20) ∧ (∀ (w20a : Fin N20) (x20 : Fin N20 → Bool), (∀ p20a : Fin N20, I20 p20a w20a → x20 p20a = false) → (X20.wires (List.ofFn x20)).getD (ps20 w20a) false = false) ∧ (∀ p20b l20 : Fin N20, (Y20.wires (List.ofFn (fun a20a => decide (a20a = l20)))).getD (rh20 p20b) false = true → I20 p20b l20) ∧ (∀ (p20c : Fin N20) (y20 : Fin N20 → Bool), (Finset.univ.filter (fun l20a : Fin N20 => y20 l20a = true)).card ≤ k20 → (∀ l20b : Fin N20, I20 p20c l20b → y20 l20b = false) → (Y20.wires (List.ofFn y20)).getD (rh20 p20c) false = false) ∧ (∀ p20d w20b : Fin N20, I20 p20d w20b → (X20.wires (List.ofFn (fun a20b => decide (a20b = p20d)))).getD (ps20 w20b) false = true ∨ (Y20.wires (List.ofFn (fun a20c => decide (a20c = w20b)))).getD (rh20 p20d) false = true)) → ∀ (q3 N3 k3 : ℕ) (I3 : Fin N3 → Fin N3 → Prop) [DecidableRel I3] (C3 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q3 → N3 = q3 ^ 2 + q3 + 1 → (∀ l3 : Fin N3, (Finset.univ.filter (fun p3 => I3 p3 l3)).card = q3 + 1) → (∀ pa3 pb3 : Fin N3, pa3 ≠ pb3 → ∃! lb3 : Fin N3, I3 pa3 lb3 ∧ I3 pb3 lb3) → (∀ g3 ∈ C3.gates, (g3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g3.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N3 + N3) C3 → (∀ j3 < C3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C3 j3).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C3 j3).inputs, (C3.lineDegrees (N3 + N3) (Finset.Ico N3 (N3 + N3))).getD i3 0 = 0) ∨ (∀ h3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C3 j3).inputs, (C3.lineDegrees (N3 + N3) (Finset.range N3)).getD h3 0 = 0)) → (∀ p3a l3a : Fin N3, I3 p3a l3a → PEqualNP.MetaComplexity.circuitFun (N3 + N3) C3 (fun i3a => decide (i3a = Fin.castAdd N3 p3a ∨ i3a = Fin.natAdd N3 l3a)) = true) → (∀ z3 : Fin (N3 + N3) → Bool, (Finset.univ.filter (fun l3b : Fin N3 => z3 (Fin.natAdd N3 l3b) = true)).card ≤ k3 → (¬ ∃ p3b l3c : Fin N3, I3 p3b l3c ∧ z3 (Fin.castAdd N3 p3b) = true ∧ z3 (Fin.natAdd N3 l3c) = true) → PEqualNP.MetaComplexity.circuitFun (N3 + N3) C3 z3 = false) → N3 * q3 * min k3 q3 ≤ 5 * q3 * C3.size + N3 * min k3 q3 := by
  intro H1 H2 q N k I inst C hq hN hl hu hg hrb hkm hcomp hsound
  have key : ∀ (n k : ℕ) (U S : Fin n → Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit)
      (o : Fin n → ℕ),
      (∀ i j : Fin n, i ≠ j → (U i ∩ U j).card ≤ 1) → (∀ i, S i ⊆ U i) →
      (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n D →
      (∀ (i : Fin n) (p : Fin n), (D.wires (List.ofFn (fun a : Fin n => decide (a = p)))).getD (o i) false = true ↔ p ∈ S i) →
      (∀ (i : Fin n) (x : Fin n → Bool), (Finset.univ.filter (fun b : Fin n => x b = true)).card ≤ k → (∀ b ∈ U i, x b = false) → (D.wires (List.ofFn x)).getD (o i) false = false) →
      ∑ i : Fin n, min ((S i).card - 1) k ≤ D.size := by
    intro n k U S D o hU hS hg hrb hex hsd
    obtain ⟨T, hT⟩ : ∃ T : Finset (Fin n), ∀ i, i ∈ T ↔ 2 ≤ (S i).card :=
      ⟨Finset.univ.filter (fun i => 2 ≤ (S i).card), fun i => by simp⟩
    obtain ⟨e⟩ : Nonempty (Fin T.card ≃ T) := ⟨T.equivFin.symm⟩
    have h := H1 n T.card k (fun j => U (e j)) (fun j => S (e j)) D (fun j => o (e j))
      (fun j => min ((S (e j)).card - 1) k)
      (fun i j hij => hU _ _ (fun h => hij (e.injective (Subtype.ext h))))
      (fun i => hS _)
      (fun i => (hT _).1 (e i).2)
      hg hrb (fun i p => hex _ p) (fun i x hx hz => hsd _ x hx hz)
      (fun i => min_le_right _ _)
      (fun i => by
        have h2 := (hT _).1 (e i).2
        have h3 := min_le_left ((S (e i)).card - 1) k
        omega)
    calc ∑ i : Fin n, min ((S i).card - 1) k = ∑ i ∈ T, min ((S i).card - 1) k := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          have h2 : ¬ 2 ≤ (S i).card := fun h => hi ((hT i).2 h)
          have h3 : (S i).card - 1 = 0 := by omega
          rw [h3]
          simp
      _ = ∑ i : T, min ((S i).card - 1) k :=
          (Finset.sum_coe_sort T (fun i => min ((S i).card - 1) k)).symm
      _ = ∑ j : Fin T.card, min ((S (e j)).card - 1) k :=
          (Equiv.sum_comp e (fun i : T => min ((S i).card - 1) k)).symm
      _ ≤ D.size := h
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp
  obtain ⟨X, Y, ps, rh, ⟨hXg, hXr⟩, ⟨hYg, hYr⟩, hsz, hX1, hX2, hY1, hY2, hcov⟩ :=
    H2 q N k I C hq hN hl hu hkpos hg hrb hkm hcomp hsound
  obtain ⟨m, hm⟩ : ∃ m, m = min k q := ⟨_, rfl⟩
  rw [← hm]
  have hmq : m ≤ q := hm ▸ min_le_right _ _
  have hmk : m ≤ k := hm ▸ min_le_left _ _
  obtain ⟨SX, hSX⟩ : ∃ SX : Fin N → Finset (Fin N), ∀ w p, p ∈ SX w ↔
      (X.wires (List.ofFn (fun a => decide (a = p)))).getD (ps w) false = true :=
    ⟨fun w => Finset.univ.filter (fun p =>
      (X.wires (List.ofFn (fun a => decide (a = p)))).getD (ps w) false = true), fun w p => by simp⟩
  obtain ⟨SY, hSY⟩ : ∃ SY : Fin N → Finset (Fin N), ∀ p l, l ∈ SY p ↔
      (Y.wires (List.ofFn (fun a => decide (a = l)))).getD (rh p) false = true :=
    ⟨fun p => Finset.univ.filter (fun l =>
      (Y.wires (List.ofFn (fun a => decide (a = l)))).getD (rh p) false = true), fun p l => by simp⟩
  obtain ⟨UX, hUXe⟩ : ∃ UX : Fin N → Finset (Fin N), ∀ w, UX w = Finset.univ.filter (fun p => I p w) :=
    ⟨fun w => Finset.univ.filter (fun p => I p w), fun w => rfl⟩
  obtain ⟨UY, hUYe⟩ : ∃ UY : Fin N → Finset (Fin N), ∀ p, UY p = Finset.univ.filter (fun l => I p l) :=
    ⟨fun p => Finset.univ.filter (fun l => I p l), fun p => rfl⟩
  have hUX : ∀ w p, p ∈ UX w ↔ I p w := fun w p => by rw [hUXe]; simp
  have hUY : ∀ p l, l ∈ UY p ↔ I p l := fun p l => by rw [hUYe]; simp
  have hUXc : ∀ w, (UX w).card = q + 1 := fun w => by rw [hUXe]; exact hl w
  have hUYc : ∀ p, (UY p).card = q + 1 := fun p => by
    rw [hUYe]
    exact PEqualNP.Outside.L_meta_1721.lines_through q N I hq hN hl hu p
  have hSUX : ∀ w, SX w ⊆ UX w := fun w p hp => (hUX w p).2 (hX1 w p ((hSX w p).1 hp))
  have hSUY : ∀ p, SY p ⊆ UY p := fun p l hl' => (hUY p l).2 (hY1 p l ((hSY p l).1 hl'))
  have hSXc : ∀ w, (SX w).card ≤ q + 1 := fun w => (Finset.card_le_card (hSUX w)).trans_eq (hUXc w)
  have hSYc : ∀ p, (SY p).card ≤ q + 1 := fun p => (Finset.card_le_card (hSUY p)).trans_eq (hUYc p)
  have hUXint : ∀ i j : Fin N, i ≠ j → (UX i ∩ UX j).card ≤ 1 := by
    intro i j hij
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    rw [Finset.mem_inter, hUX, hUX] at ha hb
    exact hij ((hu a b hab).unique ⟨ha.1, hb.1⟩ ⟨ha.2, hb.2⟩)
  have hUYint : ∀ i j : Fin N, i ≠ j → (UY i ∩ UY j).card ≤ 1 := by
    intro i j hij
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_inter, hUY, hUY] at ha hb
    exact (hu i j hij).unique ⟨ha.1, ha.2⟩ ⟨hb.1, hb.2⟩
  have keyX : ∑ w : Fin N, min ((SX w).card - 1) q ≤ X.size :=
    key N q UX SX X ps hUXint hSUX hXg hXr (fun w p => (hSX w p).symm)
      (fun w x _ hz => hX2 w x (fun p hp => hz p ((hUX w p).2 hp)))
  have keyY : ∑ p : Fin N, min ((SY p).card - 1) k ≤ Y.size :=
    key N k UY SY Y rh hUYint hSUY hYg hYr (fun p l => (hSY p l).symm)
      (fun p y hc hz => hY2 p y hc (fun l hl' => hz l ((hUY p l).2 hl')))
  have sX : (∑ w : Fin N, (SX w).card) * m ≤ q * X.size + N * m := by
    calc (∑ w : Fin N, (SX w).card) * m = ∑ w : Fin N, (SX w).card * m := Finset.sum_mul _ _ _
      _ ≤ ∑ w : Fin N, (q * min ((SX w).card - 1) q + m) :=
          Finset.sum_le_sum (fun w _ => PEqualNP.Outside.L_meta_1721.arith1 _ q q m (hSXc w) hmq hmq)
      _ = q * ∑ w : Fin N, min ((SX w).card - 1) q + N * m := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
      _ ≤ q * X.size + N * m := Nat.add_le_add_right (Nat.mul_le_mul_left _ keyX) _
  have sY : (∑ p : Fin N, (SY p).card) * m ≤ q * Y.size + N * m := by
    calc (∑ p : Fin N, (SY p).card) * m = ∑ p : Fin N, (SY p).card * m := Finset.sum_mul _ _ _
      _ ≤ ∑ p : Fin N, (q * min ((SY p).card - 1) k + m) :=
          Finset.sum_le_sum (fun p _ => PEqualNP.Outside.L_meta_1721.arith1 _ q k m (hSYc p) hmq hmk)
      _ = q * ∑ p : Fin N, min ((SY p).card - 1) k + N * m := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
      _ ≤ q * Y.size + N * m := Nat.add_le_add_right (Nat.mul_le_mul_left _ keyY) _
  have hcovc : ∀ w : Fin N, q + 1 ≤ (SX w).card + (Finset.univ.filter (fun p => w ∈ SY p)).card := by
    intro w
    rw [← hUXc w]
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro p hp
    rw [Finset.mem_union]
    rcases hcov p w ((hUX w p).1 hp) with h | h
    · exact Or.inl ((hSX w p).2 h)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hSY p w).2 h⟩)
  have hswap : ∑ w : Fin N, (Finset.univ.filter (fun p => w ∈ SY p)).card
      = ∑ p : Fin N, (SY p).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp
  have htot : N * (q + 1) ≤ ∑ w : Fin N, (SX w).card + ∑ p : Fin N, (SY p).card := by
    rw [← hswap, ← Finset.sum_add_distrib]
    calc N * (q + 1) = ∑ _w : Fin N, (q + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun w _ => hcovc w)
  have h1 := Nat.mul_le_mul_right m htot
  have h2 := Nat.mul_le_mul_left q hsz
  nlinarith [h1, h2, sX, sY]
