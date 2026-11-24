import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1716

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem eval_mono_fn {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (o : ℕ)
    (h : Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  refine mono gates _ _ (by simp) hg ?_ o h
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · exact hxy _
  · exact id

theorem cf_mono {N : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (X X' Y Y' : Finset (Fin N)) (hX : X ⊆ X') (hY : Y ⊆ Y')
    (h : PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ Y))) = true) :
    PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun a => decide (a ∈ X')) (fun b => decide (b ∈ Y'))) = true := by
  refine eval_mono_fn C.gates (fun g' hg' => (hg g' hg').1) _ _ (fun v => ?_) C.output h
  refine Fin.addCases (fun i => ?_) (fun i => ?_) v
  · rw [Fin.append_left, Fin.append_left]
    intro hv
    have hv' : i ∈ X := by simpa using hv
    simpa using hX hv'
  · rw [Fin.append_right, Fin.append_right]
    intro hv
    have hv' : i ∈ Y := by simpa using hv
    simpa using hY hv'

end PEqualNP.Outside.L_meta_1716

open PEqualNP.Outside.L_meta_1716 in
theorem PEqualNP.Outside.L_meta_1716 : ∀ (N8 K8 : ℕ) (I8 : Fin N8 → Fin N8 → Prop) [DecidableRel I8] (Ca8 Cb8 : PEqualNP.CircuitLowerBounds.Circuit) (S8 W8 : Finset (Fin N8)), (∀ g8 ∈ Ca8.gates, (g8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Ca8 → (∀ g8a ∈ Cb8.gates, (g8a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g8a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g8a.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N8 + N8) Cb8 → (∀ X8 Y8 : Finset (Fin N8), X8 ⊆ S8 → Y8 ⊆ W8 → Y8.card ≤ K8 → (∀ p8 ∈ X8, ∀ l8 ∈ Y8, ¬ I8 p8 l8) → (PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8 => decide (a8 ∈ X8)) (fun b8 => decide (b8 ∈ Y8))) && PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8a => decide (a8a ∈ X8)) (fun b8a => decide (b8a ∈ Y8)))) = false) → (∀ pz8 ∈ S8, ∀ T8 ⊆ W8, (∀ l8a ∈ T8, ¬ I8 pz8 l8a) → T8.card ≤ K8 → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8b => decide (a8b ∈ ({pz8} : Finset (Fin N8)))) (fun b8b => decide (b8b ∈ T8))) = true → ∀ X8a Y8a : Finset (Fin N8), X8a ⊆ S8.filter (fun u8 => u8 ≠ pz8 ∧ ∀ l8b ∈ T8, ¬ I8 u8 l8b) → Y8a ⊆ W8.filter (fun l8c => ¬ I8 pz8 l8c ∧ l8c ∉ T8) → Y8a.card + T8.card ≤ K8 → (∀ p8a ∈ X8a, ∀ l8d ∈ Y8a, ¬ I8 p8a l8d) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8c => decide (a8c ∈ X8a)) (fun b8c => decide (b8c ∈ (Y8a ∪ T8)))) = false) ∧ (∀ wz8 ∈ W8, ∀ Q8 ⊆ S8, (∀ p8b ∈ Q8, ¬ I8 p8b wz8) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Cb8 (Fin.append (fun a8d => decide (a8d ∈ Q8)) (fun b8d => decide (b8d ∈ ({wz8} : Finset (Fin N8))))) = true → ∀ X8b Y8b : Finset (Fin N8), X8b ⊆ S8.filter (fun u8a => ¬ I8 u8a wz8 ∧ u8a ∉ Q8) → Y8b ⊆ W8.filter (fun l8e => l8e ≠ wz8 ∧ ∀ p8c ∈ Q8, ¬ I8 p8c l8e) → Y8b.card + 1 ≤ K8 → (∀ p8e ∈ X8b, ∀ l8f ∈ Y8b, ¬ I8 p8e l8f) → PEqualNP.MetaComplexity.circuitFun (N8 + N8) Ca8 (Fin.append (fun a8e => decide (a8e ∈ X8b)) (fun b8e => decide (b8e ∈ (insert wz8 Y8b)))) = false) := by
  intro N K I _ Ca Cb S W hga _ hgb _ hF
  refine ⟨?_, ?_⟩
  · intro pz hpz T hT hTI hTK hb X Y hX hY hcard hXY
    by_contra hcon
    have ha : PEqualNP.MetaComplexity.circuitFun (N + N) Ca
        (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ (Y ∪ T)))) = true := by
      simpa using hcon
    have hXS : insert pz X ⊆ S := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hpz
      · exact (Finset.mem_filter.mp (hX hu)).1
    have hYW : Y ∪ T ⊆ W := by
      intro l hl
      rcases Finset.mem_union.mp hl with hl | hl
      · exact (Finset.mem_filter.mp (hY hl)).1
      · exact hT hl
    have hc : (Y ∪ T).card ≤ K := le_trans (Finset.card_union_le _ _) hcard
    have hinc : ∀ p ∈ insert pz X, ∀ l ∈ Y ∪ T, ¬ I p l := by
      intro p hp l hl
      rcases Finset.mem_insert.mp hp with rfl | hp <;> rcases Finset.mem_union.mp hl with hl | hl
      · exact (Finset.mem_filter.mp (hY hl)).2.1
      · exact hTI l hl
      · exact hXY p hp l hl
      · exact (Finset.mem_filter.mp (hX hp)).2.2 l hl
    have h1 := cf_mono Ca hga X (insert pz X) (Y ∪ T) (Y ∪ T) (Finset.subset_insert _ _) (Finset.Subset.refl _) ha
    have h2 := cf_mono Cb hgb {pz} (insert pz X) T (Y ∪ T)
      (by intro u hu; rw [Finset.mem_singleton.mp hu]; exact Finset.mem_insert_self _ _)
      Finset.subset_union_right hb
    have h3 := hF (insert pz X) (Y ∪ T) hXS hYW hc hinc
    rw [h1, h2] at h3
    exact absurd h3 (by decide)
  · intro wz hwz Q hQ hQI hb X Y hX hY hcard hXY
    by_contra hcon
    have ha : PEqualNP.MetaComplexity.circuitFun (N + N) Ca
        (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ (insert wz Y)))) = true := by
      simpa using hcon
    have hXS : X ∪ Q ⊆ S := by
      intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact (Finset.mem_filter.mp (hX hu)).1
      · exact hQ hu
    have hYW : insert wz Y ⊆ W := by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hwz
      · exact (Finset.mem_filter.mp (hY hl)).1
    have hc : (insert wz Y).card ≤ K := le_trans (Finset.card_insert_le _ _) hcard
    have hinc : ∀ p ∈ X ∪ Q, ∀ l ∈ insert wz Y, ¬ I p l := by
      intro p hp l hl
      rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_insert.mp hl with rfl | hl
      · exact (Finset.mem_filter.mp (hX hp)).2.1
      · exact hXY p hp l hl
      · exact hQI p hp
      · exact (Finset.mem_filter.mp (hY hl)).2.2 p hp
    have h1 := cf_mono Ca hga X (X ∪ Q) (insert wz Y) (insert wz Y) Finset.subset_union_left (Finset.Subset.refl _) ha
    have h2 := cf_mono Cb hgb Q (X ∪ Q) {wz} (insert wz Y) Finset.subset_union_right
      (by intro u hu; rw [Finset.mem_singleton.mp hu]; exact Finset.mem_insert_self _ _) hb
    have h3 := hF (X ∪ Q) (insert wz Y) hXS hYW hc hinc
    rw [h1, h2] at h3
    exact absurd h3 (by decide)
