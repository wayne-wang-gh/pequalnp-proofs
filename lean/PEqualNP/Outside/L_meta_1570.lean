import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds

-- adapted from L_meta_693
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma eval_input {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (ho : o < n) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = x ⟨o, ho⟩ := by
  change (gates.foldl step (List.ofFn x)).getD o false = x ⟨o, ho⟩
  rw [foldl_step_getD_lt gates (List.ofFn x) o (by simp [ho]), ofFn_getD_lt]

lemma eval_oob {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (ho : n + gates.length ≤ o) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = false := by
  change (gates.foldl step (List.ofFn x)).getD o false = false
  exact foldl_step_getD_ge gates (List.ofFn x) o (by simp [ho])

end PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _ _ ho
  have he0 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true := by
    rw [ho 0 _ (Or.inl rfl)]
    have h0 : (0 : Fin 13) ∈ L 0 := by rw [hL 0]; simp
    exact decide_eq_true ⟨0, h0, rfl⟩
  have he1 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true := by
    rw [ho 0 _ (Or.inr (Or.inl rfl))]
    have h1 : (1 : Fin 13) ∈ L 0 := by rw [hL 0]; simp
    exact decide_eq_true ⟨1, h1, rfl⟩
  have heL0 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false := by
    rw [ho 0 _ (Or.inr (Or.inr fun v hv => by simp [hv]))]
    simp
  have heLt : ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
    intro t ht
    have h01 : ∀ s : Fin 13, s ≠ 0 → (0 : Fin 13) ∉ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) ∨ (1 : Fin 13) ∉ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) := by decide
    have hex : ∀ s : Fin 13, s ≠ 0 → ∃ v ∈ ({(0 : Fin 13), 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)), v ∉ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) := by decide
    have h01t := h01 t ht
    have hext := hex t ht
    rw [← hL t] at h01t hext
    rw [← hL 0] at hext
    have hcond : decide ((0 : Fin 13) ∉ L t) = true ∨ decide ((1 : Fin 13) ∉ L t) = true ∨ ∀ v : Fin 13, v ∉ L 0 → decide (v ∉ L t) = true := by
      rcases h01t with h0 | h1
      · exact Or.inl (decide_eq_true h0)
      · exact Or.inr (Or.inl (decide_eq_true h1))
    rw [ho 0 _ hcond]
    obtain ⟨v, hv0, hvt⟩ := hext
    exact decide_eq_true ⟨v, hv0, decide_eq_true hvt⟩
  have hge13 : 13 ≤ o 0 := by
    by_contra hlt
    push_neg at hlt
    have h0 := he0
    have h1 := he1
    rw [PEqualNP.Outside.L_meta_1570.eval_input gates (o 0) _ hlt] at h0 h1
    have hv0 : (⟨o 0, hlt⟩ : Fin 13) = 0 := of_decide_eq_true h0
    have hv1 : (⟨o 0, hlt⟩ : Fin 13) = 1 := of_decide_eq_true h1
    have h01 : (0 : Fin 13) = 1 := hv0.symm.trans hv1
    exact absurd h01 (by decide)
  have hltlen : o 0 < 13 + gates.length := by
    by_contra hge
    push_neg at hge
    have h0 := he0
    rw [PEqualNP.Outside.L_meta_1570.eval_oob gates (o 0) _ hge] at h0
    exact Bool.false_ne_true h0
  exact ⟨hge13, hltlen, he0, he1, heL0, heLt⟩
