import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.WellFounded

namespace PEqualNP.Outside.L_meta_353_aux

abbrev leftVars : Fin 7 → Finset (Fin 12) :=
  ![{1, 2, 4, 5, 8, 11}, {0}, {1}, {4}, {6}, {8}, {9}]

abbrev rightVars : Fin 7 → Finset (Fin 12) :=
  ![{0, 3, 6, 7, 9, 10}, {3}, {2}, {5}, {7}, {11}, {10}]

abbrev edges : List (Fin 12 × Fin 12) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 6), (2, 9), (3, 4), (3, 5),
   (4, 5), (4, 7), (5, 10), (6, 7), (6, 8), (7, 8), (8, 11),
   (9, 10), (9, 11), (10, 11)]

abbrev Q (X : Finset (Fin 12)) : Prop :=
  ∃ e ∈ edges, e.1 ∈ X ∧ e.2 ∈ X

abbrev Hit (S X : Finset (Fin 12)) : Prop := ∃ v ∈ S, v ∈ X

abbrev Seed (g : Fin 7) (X : Finset (Fin 12)) : Prop :=
  Hit (leftVars g) X ∧ Hit (rightVars g) X

abbrev matching : Fin 7 → Finset (Fin 12) :=
  ![∅, {0, 3}, {1, 2}, {4, 5}, {6, 7}, {8, 11}, {9, 10}]

abbrev badLeft : Fin 7 → Finset (Fin 12) :=
  ![∅, {0, 4}, {1, 7}, {4, 6}, {2, 6}, {0, 8}, {1, 9}]

abbrev badRight : Fin 7 → Finset (Fin 12) :=
  ![∅, {3, 8}, {2, 7}, {5, 6}, {2, 7}, {0, 11}, {1, 10}]

set_option maxRecDepth 10000 in
lemma singleton_false : ∀ v : Fin 12, ¬ Q {v} := by decide

set_option maxRecDepth 10000 in
lemma matching_edge : ∀ g : Fin 7, g ≠ 0 → Q (matching g) := by decide

set_option maxRecDepth 10000 in
lemma matching_unique : ∀ g h : Fin 7, h ≠ 0 →
    Seed g (matching h) → g = h := by decide

set_option maxRecDepth 10000 in
lemma matching_disjoint : ∀ g h : Fin 7, g ≠ 0 → g ≠ h →
    ¬ Hit (leftVars g) (matching h) ∧
    ¬ Hit (rightVars g) (matching h) := by decide

set_option maxRecDepth 10000 in
lemma badLeft_spec : ∀ g : Fin 7, g ≠ 0 →
    Seed 0 (badLeft g) ∧ Hit (leftVars g) (badLeft g) ∧ ¬ Q (badLeft g) := by
  decide

set_option maxRecDepth 10000 in
lemma badRight_spec : ∀ g : Fin 7, g ≠ 0 →
    Seed 0 (badRight g) ∧ Hit (rightVars g) (badRight g) ∧ ¬ Q (badRight g) := by
  decide

set_option maxRecDepth 10000 in
lemma cross_unique : ∀ g : Fin 7, Seed g {0, 1} → g = 0 := by decide

abbrev Rule (σ : Equiv.Perm (Fin 7)) (PG RG : Fin 7 → Finset (Fin 7))
    (val : Finset (Fin 12) → Fin 7 → Prop) : Prop :=
  ∀ X i, val X i ↔
    (Hit (leftVars (σ i)) X ∨ ∃ j ∈ PG i, val X j) ∧
    (Hit (rightVars (σ i)) X ∨ ∃ j ∈ RG i, val X j)

lemma ancestor (σ : Equiv.Perm (Fin 7)) (PG RG : Fin 7 → Finset (Fin 7))
    (val : Finset (Fin 12) → Fin 7 → Prop)
    (hp : ∀ i, ∀ j ∈ PG i, j < i)
    (hr : ∀ i, ∀ j ∈ RG i, j < i)
    (hv : Rule σ PG RG val) (X : Finset (Fin 12)) :
    ∀ i, val X i → ∃ j, j ≤ i ∧ Seed (σ j) X := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro hi
    obtain ⟨hl, hright⟩ := (hv X i).mp hi
    rcases hl with hl | ⟨j, hj, hjv⟩
    · rcases hright with hright | ⟨j, hj, hjv⟩
      · exact ⟨i, le_rfl, hl, hright⟩
      · obtain ⟨k, hkj, hk⟩ := ih j (hr i j hj) hjv
        exact ⟨k, le_trans hkj (le_of_lt (hr i j hj)), hk⟩
    · obtain ⟨k, hkj, hk⟩ := ih j (hp i j hj) hjv
      exact ⟨k, le_trans hkj (le_of_lt (hp i j hj)), hk⟩

lemma matching_bound (σ : Equiv.Perm (Fin 7)) (PG RG : Fin 7 → Finset (Fin 7))
    (val : Finset (Fin 12) → Fin 7 → Prop)
    (hp : ∀ i, ∀ j ∈ PG i, j < i)
    (hr : ∀ i, ∀ j ∈ RG i, j < i)
    (hv : Rule σ PG RG val) (i j : Fin 7) (hi : σ i ≠ 0)
    (hj : val (matching (σ i)) j) : i ≤ j := by
  obtain ⟨k, hkj, hk⟩ := ancestor σ PG RG val hp hr hv _ j hj
  have hki : k = i := σ.injective (matching_unique (σ k) (σ i) hi hk)
  exact hki ▸ hkj

lemma impossible (σ : Equiv.Perm (Fin 7)) (PG RG : Fin 7 → Finset (Fin 7))
    (OV : Finset (Fin 12)) (OG : Finset (Fin 7))
    (val : Finset (Fin 12) → Fin 7 → Prop)
    (hp : ∀ i, ∀ j ∈ PG i, j < i)
    (hr : ∀ i, ∀ j ∈ RG i, j < i)
    (hv : Rule σ PG RG val)
    (hc : ∀ X, (Hit OV X ∨ ∃ j ∈ OG, val X j) ↔ Q X) : False := by
  classical
  let b : Fin 7 := σ.symm 0
  have hb : σ b = 0 := σ.apply_symm_apply 0
  have eq_big : ∀ i, σ i = 0 → i = b := by
    intro i hi
    exact σ.injective (hi.trans hb.symm)
  have after_ne : ∀ i, b < i → σ i ≠ 0 := by
    intro i hbi hi
    have hib := eq_big i hi
    exact (ne_of_lt hbi) hib.symm
  have nov : ∀ v, v ∉ OV := by
    intro v hvOV
    exact singleton_false v ((hc {v}).mp
      (Or.inl ⟨v, hvOV, Finset.mem_singleton_self v⟩))
  have big_true : ∀ X, Seed 0 X → val X b := by
    intro X hX
    apply (hv X b).mpr
    exact ⟨Or.inl (by simpa only [hb] using hX.1),
      Or.inl (by simpa only [hb] using hX.2)⟩
  have nobout : b ∉ OG := by
    intro hOG
    have hseed : Seed 0 {0, 4} := by decide
    have hbad : ¬ Q {0, 4} := by decide
    exact hbad ((hc {0, 4}).mp (Or.inr ⟨b, hOG, big_true _ hseed⟩))
  have safe : ∀ i, b < i → ∀ X, val X i → Q X := by
    intro i hbi X hiX
    have hin : σ i ≠ 0 := after_ne i hbi
    have transfer : ∀ j, val (matching (σ i)) j → val X j := by
      intro j
      induction j using WellFoundedLT.induction with
      | ind j ih =>
        intro hj
        by_cases hji : j = i
        · subst j
          exact hiX
        have hjn : σ j ≠ 0 := by
          intro hjzero
          have hij := matching_bound σ PG RG val hp hr hv i j hin hj
          have hjb := eq_big j hjzero
          have hib : i ≤ b := hjb ▸ hij
          exact (not_le_of_gt hbi) hib
        have hjni : σ j ≠ σ i := fun h => hji (σ.injective h)
        obtain ⟨hleft, hright⟩ := matching_disjoint (σ j) (σ i) hjn hjni
        obtain ⟨hl, hr'⟩ := (hv (matching (σ i)) j).mp hj
        rcases hl with hl | ⟨k, hk, hkv⟩
        · exact (hleft hl).elim
        rcases hr' with hr' | ⟨l, hl, hlv⟩
        · exact (hright hr').elim
        exact (hv X j).mpr
          ⟨Or.inr ⟨k, hk, ih k (hp j k hk) hkv⟩,
           Or.inr ⟨l, hl, ih l (hr j l hl) hlv⟩⟩
    have hq : Q (matching (σ i)) := matching_edge (σ i) hin
    rcases (hc (matching (σ i))).mpr hq with ⟨v, hvOV, hvM⟩ | ⟨j, hjOG, hjv⟩
    · exact (nov v hvOV).elim
    · exact (hc X).mp (Or.inr ⟨j, hjOG, transfer j hjv⟩)
  have noPG : ∀ i, b ∉ PG i := by
    intro i hmem
    have hbi := hp i b hmem
    obtain ⟨hseed, hbare, hbad⟩ := badRight_spec (σ i) (after_ne i hbi)
    apply hbad
    apply safe i hbi (badRight (σ i))
    exact (hv _ i).mpr ⟨Or.inr ⟨b, hmem, big_true _ hseed⟩, Or.inl hbare⟩
  have noRG : ∀ i, b ∉ RG i := by
    intro i hmem
    have hbi := hr i b hmem
    obtain ⟨hseed, hbare, hbad⟩ := badLeft_spec (σ i) (after_ne i hbi)
    apply hbad
    apply safe i hbi (badLeft (σ i))
    exact (hv _ i).mpr ⟨Or.inl hbare, Or.inr ⟨b, hmem, big_true _ hseed⟩⟩
  have onlyBig : ∀ i, val {0, 1} i → i = b := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro hi
      obtain ⟨hl, hr'⟩ := (hv {0, 1} i).mp hi
      rcases hl with hl | ⟨j, hj, hjv⟩
      · rcases hr' with hr' | ⟨j, hj, hjv⟩
        · exact eq_big i (cross_unique (σ i) ⟨hl, hr'⟩)
        · have hjb : j = b := ih j (hr i j hj) hjv
          exact (noRG i (hjb ▸ hj)).elim
      · have hjb : j = b := ih j (hp i j hj) hjv
        exact (noPG i (hjb ▸ hj)).elim
  have hq : Q {0, 1} := by decide
  rcases (hc {0, 1}).mpr hq with ⟨v, hvOV, hvX⟩ | ⟨j, hjOG, hjv⟩
  · exact nov v hvOV
  · exact nobout (onlyBig j hjv ▸ hjOG)

end PEqualNP.Outside.L_meta_353_aux

theorem PEqualNP.Outside.L_meta_353 :
    ∀ E : List (Fin 12 × Fin 12),
    E = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 6), (2, 9), (3, 4), (3, 5),
      (4, 5), (4, 7), (5, 10), (6, 7), (6, 8), (7, 8), (8, 11),
      (9, 10), (9, 11), (10, 11)] →
    ∀ (σ : Equiv.Perm (Fin 7)) (PG RG : Fin 7 → Finset (Fin 7))
      (OV : Finset (Fin 12)) (OG : Finset (Fin 7))
      (val : Finset (Fin 12) → Fin 7 → Prop),
    (∀ i : Fin 7, ∀ j ∈ PG i, j < i) →
    (∀ i : Fin 7, ∀ j ∈ RG i, j < i) →
    (∀ (X : Finset (Fin 12)) (i : Fin 7),
      val X i ↔
        (((∃ v ∈ (![{1, 2, 4, 5, 8, 11}, {0}, {1}, {4}, {6}, {8}, {9}] :
          Fin 7 → Finset (Fin 12)) (σ i), v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧
        ((∃ v ∈ (![{0, 3, 6, 7, 9, 10}, {3}, {2}, {5}, {7}, {11}, {10}] :
          Fin 7 → Finset (Fin 12)) (σ i), v ∈ X) ∨ ∃ j ∈ RG i, val X j))) →
    ¬ ∀ X : Finset (Fin 12),
      ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔
        ∃ e ∈ E, e.1 ∈ X ∧ e.2 ∈ X := by
  intro E hE σ PG RG OV OG val hp hr hv hc
  subst E
  exact PEqualNP.Outside.L_meta_353_aux.impossible σ PG RG OV OG val hp hr hv hc
