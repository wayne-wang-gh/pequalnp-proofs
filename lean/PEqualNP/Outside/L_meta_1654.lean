import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1654

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

private lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

private def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

private lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

private lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

private lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

private lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

private lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private def Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (W gs x).getD t false = true → (W gs y).getD t false = true

private lemma mono_nil {n : ℕ} : Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := ofFn_getD_true x t ht
  exact (ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

private lemma mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Mono (n := n) gs) :
    Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [W_val] at ht ⊢
  by_cases htt : t = n + gs.length
  · rw [if_pos htt] at ht ⊢
    rcases hop with hand | hor
    · rw [hand] at ht ⊢
      exact (all_true _ _).mpr (fun i hi => h x y hxy i ((all_true _ _).mp ht i hi))
    · rw [hor] at ht ⊢
      obtain ⟨i, hi, hti⟩ := (any_true _ _).mp ht
      exact (any_true _ _).mpr ⟨i, hi, h x y hxy i hti⟩
  · rw [if_neg htt] at ht ⊢
    exact h x y hxy t ht

private lemma mono_all {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => exact mono_nil
  | append_singleton gs g ih =>
    exact mono_step gs g (hg g (by simp)) (ih (fun g' hg' => hg g' (by simp [hg'])))

theorem main_aux : ∀ (n L : ℕ) (line : Fin L → Finset (Fin n)) (l : Fin L) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G K : ℕ) (I : Finset (Fin n)),
  (∀ p r : Fin n, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
  (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (¬ ∃ X : Finset (Fin n), Disjoint X (line l) ∧
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true) →
  Disjoint I (line l) →
  (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ I)))).getD K false = true →
  ∀ v : Fin n, v ∉ line l →
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = v)))).getD G false = true →
    v ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j := by
  intro n L line l gates G K I huniq hint hg hord hno hdisj harc hK v hvl hG
  have mono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      ∀ t, (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD t false = true →
        (Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD t false = true :=
    mono_all (n := n) gates (fun g hgm => (hg g hgm).1)
  have key : ∀ X : Finset (Fin n), Disjoint X (line l) →
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c →
        ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true →
      False := fun X h1 h2 h3 h4 => hno ⟨X, h1, h2, h3, h4⟩
  have hvI : v ∉ I := by
    intro hvI
    refine key I hdisj harc ?_ hK
    refine mono (fun u : Fin n => decide (u = v)) (fun u : Fin n => decide (u ∈ I)) ?_ G hG
    intro i hi
    have hiv : i = v := of_decide_eq_true hi
    exact decide_eq_true (by rw [hiv]; exact hvI)
  refine ⟨hvI, ?_⟩
  by_contra hno2
  refine key (insert v I) ?_ ?_ ?_ ?_
  · exact Finset.disjoint_insert_left.mpr ⟨hvl, hdisj⟩
  · intro a ha b hb c hc hab hac hbc hex
    obtain ⟨j, haj, hbj, hcj⟩ := hex
    rw [Finset.mem_insert] at ha hb hc
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact hab (ha.trans hb.symm)
      · rcases hc with hc | hc
        · exact hac (ha.trans hc.symm)
        · exact hno2 ⟨b, hb, c, hc, hbc, j, hbj, hcj, by rw [← ha]; exact haj⟩
    · rcases hb with hb | hb
      · rcases hc with hc | hc
        · exact hbc (hb.trans hc.symm)
        · exact hno2 ⟨a, ha, c, hc, hac, j, haj, hcj, by rw [← hb]; exact hbj⟩
      · rcases hc with hc | hc
        · exact hno2 ⟨a, ha, b, hb, hab, j, haj, hbj, by rw [← hc]; exact hcj⟩
        · exact harc a ha b hb c hc hab hac hbc ⟨j, haj, hbj, hcj⟩
  · refine mono (fun u : Fin n => decide (u = v)) (fun u : Fin n => decide (u ∈ insert v I)) ?_ G hG
    intro i hi
    have hiv : i = v := of_decide_eq_true hi
    exact decide_eq_true (Finset.mem_insert.mpr (Or.inl hiv))
  · refine mono (fun u : Fin n => decide (u ∈ I)) (fun u : Fin n => decide (u ∈ insert v I)) ?_ K hK
    intro i hi
    have hiI : i ∈ I := of_decide_eq_true hi
    exact decide_eq_true (Finset.mem_insert_of_mem hiI)

end PEqualNP.Outside.L_meta_1654

theorem PEqualNP.Outside.L_meta_1654 : ∀ (n L : ℕ) (line : Fin L → Finset (Fin n)) (l : Fin L) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G K : ℕ) (I : Finset (Fin n)),
  (∀ p r : Fin n, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
  (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (¬ ∃ X : Finset (Fin n), Disjoint X (line l) ∧
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true) →
  Disjoint I (line l) →
  (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ I)))).getD K false = true →
  ∀ v : Fin n, v ∉ line l →
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = v)))).getD G false = true →
    v ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j :=
  PEqualNP.Outside.L_meta_1654.main_aux
