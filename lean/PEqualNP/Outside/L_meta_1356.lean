import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1356

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc (L : List Bool) (v : Bool) (k : ℕ) :
    (L ++ [v]).getD k false = if k < L.length then L.getD k false else if k = L.length then v else false := by
  by_cases h1 : k < L.length
  · rw [if_pos h1, List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h1,
      List.getElem_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : k = L.length
    · subst h2
      simp
    · rw [if_neg h2, List.getD_eq_default _ _ (by simp; omega)]

lemma prefix_getD (gs : List Gate) : ∀ (W : List Bool) (k : ℕ), k < W.length →
    (gs.foldl step W).getD k false = W.getD k false := by
  induction gs with
  | nil =>
    intro W k _
    rfl
  | cons g gs ih =>
    intro W k hk
    rw [List.foldl_cons, ih (step W g) k (by simp [step]; omega)]
    simp only [step]
    rw [getD_snoc, if_pos hk]

lemma inv_eq (p : ℕ) (gs : List Gate)
    (hand : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hab : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) → p ∉ g.inputs)
    (hn : ∀ g ∈ gs, g.op = GateOp.not → g.inputs.head? ≠ some p) :
    ∀ W0 W1 : List Bool, W0.length = W1.length →
      (∀ k, k ≠ p → W0.getD k false = W1.getD k false) →
      ∀ k, k ≠ p → (gs.foldl step W0).getD k false = (gs.foldl step W1).getD k false := by
  induction gs with
  | nil =>
    intro W0 W1 _ h k hk
    exact h k hk
  | cons g gs ih =>
    intro W0 W1 hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hand g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hab g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hn g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro k hk
      have hv : g.op.eval (g.inputs.map fun i => W0.getD i false) =
          g.op.eval (g.inputs.map fun i => W1.getD i false) := by
        rcases hand g List.mem_cons_self with h1 | h1 | h1
        · congr 1
          apply List.map_congr_left
          intro i hi
          exact h i (fun e => hab g List.mem_cons_self (Or.inl h1) (e ▸ hi))
        · congr 1
          apply List.map_congr_left
          intro i hi
          exact h i (fun e => hab g List.mem_cons_self (Or.inr h1) (e ▸ hi))
        · rw [h1]
          simp only [GateOp.eval]
          cases hin : g.inputs with
          | nil => rfl
          | cons i t =>
            have hip : i ≠ p := by
              intro e
              apply hn g List.mem_cons_self h1
              rw [hin, e]
              rfl
            simp only [List.map_cons, List.headD_cons]
            rw [h i hip]
      simp only [step]
      rw [getD_snoc, getD_snoc, hl, hv]
      split_ifs
      · exact h k hk
      · rfl
      · rfl

lemma inv_le (p : ℕ) (gs : List Gate)
    (hand : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hab : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) → p ∉ g.inputs)
    (hn : ∀ g ∈ gs, g.op = GateOp.not → g.inputs.head? = some p) :
    ∀ W0 W1 : List Bool, W0.length = W1.length → p < W1.length → W1.getD p false = true →
      (∀ k, k ≠ p → W1.getD k false = true → W0.getD k false = true) →
      ∀ k, k ≠ p → (gs.foldl step W1).getD k false = true →
        (gs.foldl step W0).getD k false = true := by
  induction gs with
  | nil =>
    intro W0 W1 _ _ _ h k hk
    exact h k hk
  | cons g gs ih =>
    intro W0 W1 hl hpl hp1 h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hand g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hab g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hn g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · simp [step]
      omega
    · simp only [step]
      rw [getD_snoc, if_pos hpl]
      exact hp1
    · intro k hk hk1
      have hv : g.op.eval (g.inputs.map fun i => W1.getD i false) = true →
          g.op.eval (g.inputs.map fun i => W0.getD i false) = true := by
        rcases hand g List.mem_cons_self with h1 | h1 | h1
        · rw [h1]
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
          intro hall b hb
          obtain ⟨i, hi, rfl⟩ := hb
          have hip : i ≠ p := fun e => hab g List.mem_cons_self (Or.inl h1) (e ▸ hi)
          exact h i hip (hall _ ⟨i, hi, rfl⟩)
        · rw [h1]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
          have hip : i ≠ p := fun e => hab g List.mem_cons_self (Or.inr h1) (e ▸ hi)
          exact ⟨W0.getD i false, ⟨i, hi, rfl⟩, h i hip hb⟩
        · rw [h1]
          have hh := hn g List.mem_cons_self h1
          cases hin : g.inputs with
          | nil =>
            rw [hin] at hh
            simp at hh
          | cons i t =>
            rw [hin] at hh
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst hh
            simp only [GateOp.eval, List.map_cons, List.headD_cons]
            rw [hp1]
            simp
      simp only [step] at hk1 ⊢
      rw [getD_snoc] at hk1 ⊢
      rw [hl]
      split_ifs at hk1 ⊢ with ha hb
      all_goals first
        | exact h k hk hk1
        | exact hv hk1
        | exact hk1
        | simp at hk1

lemma main : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i9 : Fin m, 2 ≤ (S i9).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ (p : Fin n) (i0 : Fin m), p ∈ S i0 → ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get a).inputs := by
  intro n m S hS gates out hgates hcomp ι hι p i0 hp
  by_contra hcon
  have hab : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) → p.val ∉ g.inputs := by
    intro g hg hop hmem
    obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hg
    exact hcon ⟨a, hop, hmem⟩
  have hnot : ∀ g ∈ gates, g.op = GateOp.not → g = gates.get (ι 0) := by
    intro g hg hop
    obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hg
    obtain ⟨r, hr⟩ := hι a hop
    rw [← hr, Subsingleton.elim r 0]
  have hand : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hgates g hg).1
  have heval : ∀ (o : ℕ) (x : Fin n → Bool),
      Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (gates.foldl step (List.ofFn x)).getD o false :=
    fun o x => rfl
  have hin : ∀ (x : Fin n → Bool) (k : ℕ) (hk : k < n), (List.ofFn x).getD k false = x ⟨k, hk⟩ := by
    intro x k hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
  have hout : ∀ (x : Fin n → Bool) (k : ℕ), n ≤ k → (List.ofFn x).getD k false = false := by
    intro x k hk
    rw [List.getD_eq_default _ _ (by simpa using hk)]
  have h0 : (gates.foldl step (List.ofFn (fun _ : Fin n => false))).getD (out i0) false = false := by
    rw [← heval, hcomp]
    simp
  have h1 : (gates.foldl step (List.ofFn (fun i : Fin n => decide (i = p)))).getD (out i0) false =
      true := by
    rw [← heval, hcomp]
    simpa using hp
  by_cases hop : out i0 = p.val
  · obtain ⟨q, hq, hqp⟩ : ∃ q ∈ S i0, q ≠ p := by
      by_contra hc
      push_neg at hc
      have hsub : S i0 ⊆ {p} := fun v hv => Finset.mem_singleton.mpr (hc v hv)
      have := Finset.card_le_card hsub
      have := hS i0
      simp at *
      omega
    have h2 := hcomp i0 (fun i : Fin n => decide (i = q))
    rw [heval, hop, prefix_getD _ _ _ (by simp), hin _ _ p.isLt] at h2
    have h3 : decide (∃ v ∈ S i0, decide (v = q) = true) = true := by simpa using hq
    rw [h3] at h2
    simp only [Fin.eta, decide_eq_true_eq] at h2
    exact hqp h2.symm
  · by_cases hcase : (gates.get (ι 0)).op = GateOp.not ∧ (gates.get (ι 0)).inputs.head? = some p.val
    · have key := inv_le p.val gates hand hab
        (fun g hg hgop => by rw [hnot g hg hgop]; exact hcase.2)
        (List.ofFn (fun _ : Fin n => false)) (List.ofFn (fun i : Fin n => decide (i = p)))
        (by simp) (by simp) (by rw [hin _ _ p.isLt]; simp)
        (by
          intro k hk hk1
          by_cases hkn : k < n
          · rw [hin _ _ hkn] at hk1
            simp only [decide_eq_true_eq] at hk1
            exact absurd (congrArg Fin.val hk1) hk
          · rw [hout _ _ (by omega)] at hk1
            exact absurd hk1 (by simp))
        (out i0) hop h1
      rw [h0] at key
      exact absurd key (by simp)
    · have key := inv_eq p.val gates hand hab
        (fun g hg hgop => by
          have e := hnot g hg hgop
          rw [e] at hgop ⊢
          exact fun hh => hcase ⟨hgop, hh⟩)
        (List.ofFn (fun _ : Fin n => false)) (List.ofFn (fun i : Fin n => decide (i = p)))
        (by simp)
        (by
          intro k hk
          by_cases hkn : k < n
          · rw [hin _ _ hkn, hin _ _ hkn]
            simp only [Bool.false_eq, decide_eq_false_iff_not]
            intro e
            exact hk (congrArg Fin.val e)
          · rw [hout _ _ (by omega), hout _ _ (by omega)])
        (out i0) hop
      rw [h0, h1] at key
      exact absurd key (by simp)

end PEqualNP.Outside.L_meta_1356

theorem PEqualNP.Outside.L_meta_1356 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i9 : Fin m, 2 ≤ (S i9).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ (p : Fin n) (i0 : Fin m), p ∈ S i0 → ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get a).inputs := by
  exact PEqualNP.Outside.L_meta_1356.main
