import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1577

open PEqualNP.CircuitLowerBounds

def Lstd (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def coLine (t : Fin 13) : Fin 13 → Bool := fun v => decide (v ∉ Lstd t)

def test0 (p : Fin 13) : Fin 13 → Bool :=
  fun v => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ Lstd 0))

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def evalW (gs : List Gate) (w : ℕ) (x : Fin 13 → Bool) : Bool :=
  Circuit.eval ⟨gs, w⟩ (List.ofFn x)

lemma inter_card_one (t : Fin 13) (ht : t ≠ 0) : (Lstd 0 ∩ Lstd t).card = 1 := by
  revert t ht; decide

lemma mem_L0_cases (p : Fin 13) (hp : p ∈ Lstd 0) : p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9 := by
  revert p hp; decide

lemma evalW_eq_wiresOf (gs : List Gate) (w : ℕ) (x : Fin 13 → Bool) :
    evalW gs w x = (wiresOf gs (List.ofFn x)).getD w false := rfl

lemma wiresOf_nil (x : List Bool) : wiresOf [] x = x := rfl

lemma wiresOf_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wiresOf (g :: gs) x =
      wiresOf gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  simp [wiresOf, List.foldl_append]

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    rw [wiresOf_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresOf_cons, ih]
    · exact getD_append_left x _ i false hi
    · simp; omega

lemma evalW_input (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) (hw : w < 13) :
    evalW gs w x = x ⟨w, hw⟩ := by
  rw [evalW_eq_wiresOf, wiresOf_getD_lt]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]
  · simp [hw]

lemma evalW_ge_len (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) (hw : 13 + gs.length ≤ w) :
    evalW gs w x = false := by
  rw [evalW_eq_wiresOf]
  have hlen : (wiresOf gs (List.ofFn x)).length = 13 + gs.length := by
    rw [wiresOf_length, List.length_ofFn]
  have hge : (wiresOf gs (List.ofFn x)).length ≤ w := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]

lemma evalW_gate (gs : List Gate) (x : Fin 13 → Bool) (j : Fin gs.length) :
    evalW gs (13 + (j : ℕ)) x =
      (gs.get j).op.eval
        ((gs.get j).inputs.map fun i => if i < 13 + (j : ℕ) then evalW gs i x else false) := by
  have hsplit : gs = gs.take (j : ℕ) ++ [gs.get j] ++ gs.drop ((j : ℕ) + 1) := by
    have h1 := (List.take_append_drop (j : ℕ) gs).symm
    have h2 : gs.drop (j : ℕ) = gs.get j :: gs.drop ((j : ℕ) + 1) := by
      rw [← List.getElem_cons_drop j.isLt]
      rfl
    exact h1.trans (by rw [h2]; simp)
  set p := gs.take (j : ℕ)
  set g := gs.get j
  set q := gs.drop ((j : ℕ) + 1)
  have hplen : p.length = (j : ℕ) := List.length_take_of_le (Nat.le_of_lt j.isLt)
  have hwp_len : (wiresOf p (List.ofFn x)).length = 13 + (j : ℕ) := by
    rw [wiresOf_length, List.length_ofFn, hplen]
  have hprefix_eq : ∀ i, i < 13 + (j : ℕ) →
      (wiresOf p (List.ofFn x)).getD i false = (wiresOf gs (List.ofFn x)).getD i false := by
    intro i hi
    have hw_eq : wiresOf gs (List.ofFn x) = wiresOf ([g] ++ q) (wiresOf p (List.ofFn x)) := by
      rw [← wiresOf_append, ← List.append_assoc, ← hsplit]
    rw [hw_eq]
    exact (wiresOf_getD_lt ([g] ++ q) (wiresOf p (List.ofFn x)) i (by omega)).symm
  have hmap : (g.inputs.map fun i => (wiresOf p (List.ofFn x)).getD i false) =
      (g.inputs.map fun i => if i < 13 + (j : ℕ) then evalW gs i x else false) := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < 13 + (j : ℕ)
    · simp only [hi, ↓reduceIte, evalW_eq_wiresOf]
      exact hprefix_eq i hi
    · simp only [hi, ↓reduceIte]
      have hge : (wiresOf p (List.ofFn x)).length ≤ i := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
  rw [evalW_eq_wiresOf]
  have hw_eq : wiresOf gs (List.ofFn x) = wiresOf q (wiresOf [g] (wiresOf p (List.ofFn x))) := by
    rw [← wiresOf_append, ← wiresOf_append, ← List.append_assoc, ← hsplit]
  rw [hw_eq, wiresOf_getD_lt q]
  · rw [wiresOf_cons, wiresOf_nil]
    rw [getD_append_right (wiresOf p (List.ofFn x)) _ (13 + (j : ℕ)) false (by omega)]
    rw [hwp_len, Nat.sub_self, hmap]
    rfl
  · rw [wiresOf_cons, wiresOf_nil, List.length_append, hwp_len]
    simp

lemma evalW_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 13 → Bool) (hxy : ∀ v : Fin 13, x v = true → y v = true) :
    ∀ w : ℕ, evalW gs w x = true → evalW gs w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwx
    by_cases h13 : w < 13
    · rw [evalW_input gs x w h13] at hwx
      rw [evalW_input gs y w h13]
      exact hxy ⟨w, h13⟩ hwx
    · by_cases hlt : w < 13 + gs.length
      · let j : Fin gs.length := ⟨w - 13, by omega⟩
        have hj : 13 + (j : ℕ) = w := by dsimp [j]; omega
        rw [← hj] at hwx ⊢
        rw [evalW_gate gs x j] at hwx
        rw [evalW_gate gs y j]
        rcases hgs _ (List.get_mem gs j) with hand | hor
        · rw [hand] at hwx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at hwx ⊢
          intro i hi
          have hix := hwx i hi
          by_cases hilt : i < 13 + (j : ℕ)
          · simp only [hilt, ↓reduceIte] at hix ⊢
            exact ih i (by omega) hix
          · simp [hilt] at hix
        · rw [hor] at hwx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hwx ⊢
          obtain ⟨_, ⟨i, hi, rfl⟩, hix⟩ := hwx
          refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
          by_cases hilt : i < 13 + (j : ℕ)
          · simp only [hilt, ↓reduceIte] at hix ⊢
            exact ih i (by omega) hix
          · simp [hilt] at hix
      · rw [evalW_ge_len gs x w (by omega)] at hwx
        exact Bool.noConfusion hwx

lemma find_and_atom (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (t s : Fin 13) (hs_not : s ∉ Lstd t) :
    ∀ w : ℕ,
      evalW gs w (coLine 0) = false →
      evalW gs w (coLine t) = false →
      evalW gs w (test0 s) = true →
      ∃ Y : ℕ,
        (∀ S : Set ℕ, w ∈ S →
          (∀ i : Fin gs.length, 13 + (i : ℕ) ∈ S → (gs.get i).op = GateOp.or →
            ∀ a ∈ (gs.get i).inputs, a ∈ S) → Y ∈ S) ∧
        (∃ i : Fin gs.length, Y = 13 + (i : ℕ) ∧ (gs.get i).op = GateOp.and) ∧
        evalW gs Y (coLine 0) = false ∧
        evalW gs Y (coLine t) = false ∧
        evalW gs Y (test0 s) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hc0 hct hts
    by_cases h13 : w < 13
    · exfalso
      rw [evalW_input gs (coLine 0) w h13] at hc0
      rw [evalW_input gs (coLine t) w h13] at hct
      rw [evalW_input gs (test0 s) w h13] at hts
      simp only [coLine, decide_eq_false_iff_not, not_not] at hc0 hct
      simp only [test0, decide_eq_true_eq] at hts
      rcases hts with heq | ⟨_, hnot⟩
      · rw [heq] at hct
        exact hs_not hct
      · exact hnot hc0
    · by_cases hlt : w < 13 + gs.length
      · let j : Fin gs.length := ⟨w - 13, by omega⟩
        have hj : 13 + (j : ℕ) = w := by dsimp [j]; omega
        rcases hgs _ (List.get_mem gs j) with hand | hor
        · refine ⟨w, fun S hw _ => hw, ⟨j, hj.symm, hand⟩, hc0, hct, hts⟩
        · have hc0' := hc0
          have hct' := hct
          have hts' := hts
          rw [← hj] at hc0' hct' hts'
          rw [evalW_gate gs (coLine 0) j, hor] at hc0'
          rw [evalW_gate gs (coLine t) j, hor] at hct'
          rw [evalW_gate gs (test0 s) j, hor] at hts'
          simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq,
            forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hc0' hct'
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hts'
          obtain ⟨_, ⟨a, ha_mem, rfl⟩, ha_ts⟩ := hts'
          have ha_lt : a < 13 + (j : ℕ) := by
            by_contra h
            simp [h] at ha_ts
          simp only [ha_lt, ↓reduceIte] at ha_ts
          have ha_c0 : evalW gs a (coLine 0) = false := by
            have h := hc0' a ha_mem
            simp only [ha_lt, ↓reduceIte] at h
            cases hv : evalW gs a (coLine 0)
            · rfl
            · exact absurd hv h
          have ha_ct : evalW gs a (coLine t) = false := by
            have h := hct' a ha_mem
            simp only [ha_lt, ↓reduceIte] at h
            cases hv : evalW gs a (coLine t)
            · rfl
            · exact absurd hv h
          obtain ⟨Y, hreach, handY, hYc0, hYct, hYts⟩ := ih a (by omega) ha_c0 ha_ct ha_ts
          refine ⟨Y, ?_, handY, hYc0, hYct, hYts⟩
          intro S hwS hclosed
          apply hreach S _ hclosed
          exact hclosed j (by rw [hj]; exact hwS) hor a ha_mem
      · exfalso
        rw [evalW_ge_len gs (test0 s) w (by omega)] at hts
        exact Bool.noConfusion hts

lemma main_proof
    (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (gates : List Gate) (g : ℕ) (t : Fin 13)
    (hgs : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (_hwf : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (ht : t ≠ 0)
    (hc0 : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false)
    (hct : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false)
    (hcard : 2 ≤ ((L 0).filter (fun p => Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0)))) = true)).card) :
    ∃ Y : ℕ,
      (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧
      Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false ∧
      ∃ s : Fin 13, (s = 3 ∨ s = 9) ∧ s ∉ L t ∧
        Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true := by
  have hLeq : L = Lstd := funext hL
  subst hLeq
  have hgs_op : ∀ x ∈ gates, x.op = GateOp.and ∨ x.op = GateOp.or := fun x hx => (hgs x hx).1
  let A : Finset (Fin 13) := (Lstd 0).filter (fun p => evalW gates g (test0 p) = true)
  have hA_card : 2 ≤ A.card := hcard
  have hA_sub : A ⊆ Lstd 0 := Finset.filter_subset _ _
  have hci : (A ∩ Lstd t).card ≤ 1 := by
    calc (A ∩ Lstd t).card ≤ (Lstd 0 ∩ Lstd t).card :=
          Finset.card_le_card (Finset.inter_subset_inter_right hA_sub)
      _ = 1 := inter_card_one t ht
  have hsd := Finset.card_sdiff_add_card_inter A (Lstd t)
  obtain ⟨s, hs_mem⟩ := Finset.card_pos.mp (by omega : 0 < (A \ Lstd t).card)
  rw [Finset.mem_sdiff] at hs_mem
  have hs_not : s ∉ Lstd t := hs_mem.2
  have hsA := hs_mem.1
  simp only [A, Finset.mem_filter] at hsA
  have hs_L0 : s ∈ Lstd 0 := hsA.1
  have hs_ts : evalW gates g (test0 s) = true := hsA.2
  have hs_39 : s = 3 ∨ s = 9 := by
    rcases mem_L0_cases s hs_L0 with rfl | rfl | rfl | rfl
    · exfalso
      have hmono : evalW gates g (coLine t) = true := by
        apply evalW_mono gates hgs_op (test0 0) (coLine t) _ g hs_ts
        intro v hv
        simp only [test0, decide_eq_true_eq] at hv
        simp only [coLine, decide_eq_true_eq]
        rcases hv with rfl | ⟨h0, _⟩
        · exact hs_not
        · exfalso; rcases h0 with h | h <;> exact absurd h (by decide)
      change evalW gates g (coLine t) = false at hct
      rw [hct] at hmono
      exact Bool.noConfusion hmono
    · exfalso
      have hmono : evalW gates g (coLine t) = true := by
        apply evalW_mono gates hgs_op (test0 1) (coLine t) _ g hs_ts
        intro v hv
        simp only [test0, decide_eq_true_eq] at hv
        simp only [coLine, decide_eq_true_eq]
        rcases hv with rfl | ⟨h1, _⟩
        · exact hs_not
        · exfalso; rcases h1 with h | h <;> exact absurd h (by decide)
      change evalW gates g (coLine t) = false at hct
      rw [hct] at hmono
      exact Bool.noConfusion hmono
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨Y, hreach, handY, hYc0, hYct, hYts⟩ :=
    find_and_atom gates hgs_op t s hs_not g hc0 hct hs_ts
  exact ⟨Y, hreach, handY, hYc0, hYct, s, hs_39, hs_not, hYts⟩

end PEqualNP.Outside.L_meta_1577

theorem PEqualNP.Outside.L_meta_1577 :
    ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → t ≠ 0 →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
    2 ≤ ((L 0).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0)))) = true)).card →
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false ∧
      ∃ s : Fin 13, (s = 3 ∨ s = 9) ∧ s ∉ L t ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true :=
  PEqualNP.Outside.L_meta_1577.main_proof
