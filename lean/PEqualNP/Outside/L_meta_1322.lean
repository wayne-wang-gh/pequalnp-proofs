import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1322

open PEqualNP.CircuitLowerBounds

def dualGate (k : ℕ) : Gate → Gate
  | ⟨GateOp.and, l⟩ => if l.all (fun i => decide (i < k)) then ⟨GateOp.or, l⟩ else ⟨GateOp.and, []⟩
  | ⟨GateOp.or, l⟩ => ⟨GateOp.and, l.filter (fun i => decide (i < k))⟩
  | ⟨GateOp.not, l⟩ => if l.headD k < k then ⟨GateOp.not, l⟩ else ⟨GateOp.or, []⟩
  | ⟨GateOp.mod m, l⟩ => ⟨GateOp.mod m, l⟩
  | ⟨GateOp.maj, l⟩ => ⟨GateOp.maj, l⟩

def dualList : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => dualGate k g :: dualList (k + 1) gs

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc_lt (L : List Bool) (v : Bool) (j : ℕ) (hj : j < L.length) :
    (L ++ [v]).getD j false = L.getD j false := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

lemma getD_snoc_eq (L : List Bool) (v : Bool) (k : ℕ) (hk : L.length = k) :
    (L ++ [v]).getD k false = v := by
  subst hk
  simp

lemma any_neg (l : List ℕ) (k : ℕ) (W W' : List Bool)
    (hneg : ∀ i < k, W'.getD i false = !(W.getD i false)) (hl : ∀ i ∈ l, i < k) :
    (l.map fun i => W'.getD i false).any id = !((l.map fun i => W.getD i false).all id) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, List.all_cons, id_eq]
    rw [ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)), hneg a (hl a List.mem_cons_self)]
    cases W.getD a false <;> simp

lemma all_neg (l : List ℕ) (k : ℕ) (W W' : List Bool)
    (hneg : ∀ i < k, W'.getD i false = !(W.getD i false))
    (hbig : ∀ i, k ≤ i → W.getD i false = false) :
    ((l.filter fun i => decide (i < k)).map fun i => W'.getD i false).all id =
      !((l.map fun i => W.getD i false).any id) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a < k
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, List.all_cons, id_eq]
      rw [ih, hneg a ha]
      cases W.getD a false <;> simp
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, id_eq]
      rw [ih, hbig a (by omega)]
      simp

lemma gate_dual (k : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (W W' : List Bool) (hW : W.length = k)
    (hneg : ∀ i < k, W'.getD i false = !(W.getD i false)) :
    (dualGate k g).op.eval ((dualGate k g).inputs.map fun i => W'.getD i false) =
      !(g.op.eval (g.inputs.map fun i => W.getD i false)) := by
  have hbig : ∀ i, k ≤ i → W.getD i false = false := by
    intro i hi
    rw [List.getD_eq_default _ _ (by omega)]
  obtain ⟨op, l⟩ := g
  simp only at hg
  rcases hg with h | h | h <;> subst h
  · by_cases hall : l.all (fun i => decide (i < k)) = true
    · simp only [dualGate, hall, if_true, GateOp.eval]
      apply any_neg l k W W' hneg
      intro i hi
      rw [List.all_eq_true] at hall
      simpa using hall i hi
    · simp only [dualGate, hall, GateOp.eval]
      simp only [Bool.false_eq_true, if_false, List.map_nil, List.all_nil]
      have hex : ∃ i ∈ l, ¬ i < k := by
        simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at hall
        obtain ⟨i, hi, hik⟩ := hall
        exact ⟨i, hi, hik⟩
      obtain ⟨i, hi, hik⟩ := hex
      have hf : (l.map fun i => W.getD i false).all id = false := by
        rw [Bool.eq_false_iff]
        intro hcon
        rw [List.all_eq_true] at hcon
        have h1 := hcon (W.getD i false) (List.mem_map_of_mem hi)
        rw [hbig i (by omega)] at h1
        simp at h1
      rw [hf]
      rfl
  · simp only [dualGate, GateOp.eval]
    exact all_neg l k W W' hneg hbig
  · cases l with
    | nil =>
      simp [dualGate, GateOp.eval]
    | cons a t =>
      by_cases ha : a < k
      · simp only [dualGate, List.headD_cons, ha, if_true, GateOp.eval, List.map_cons]
        rw [hneg a ha]
      · simp only [dualGate, List.headD_cons, ha, if_false, GateOp.eval, List.map_cons]
        rw [hbig a (by omega)]
        rfl

lemma fold_dual (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (k : ℕ) (W W' : List Bool), W.length = k → W'.length = k →
      (∀ i < k, W'.getD i false = !(W.getD i false)) →
      ∀ i < k + gs.length,
        ((dualList k gs).foldl step W').getD i false = !((gs.foldl step W).getD i false) := by
  induction gs with
  | nil =>
    intro k W W' hW hW' hneg i hi
    simp only [List.length_nil, Nat.add_zero] at hi
    exact hneg i hi
  | cons g gs ih =>
    intro k W W' hW hW' hneg i hi
    simp only [dualList, List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) (k + 1)
    · simp [step, hW]
    · simp [step, hW']
    · intro j hj
      by_cases hjk : j < k
      · rw [step, step, getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact hneg j hjk
      · have hj' : j = k := by omega
        subst hj'
        rw [step, step, getD_snoc_eq _ _ _ hW, getD_snoc_eq _ _ _ hW']
        exact gate_dual j g (hg g List.mem_cons_self) W W' hW hneg
    · simp only [List.length_cons] at hi
      omega

lemma dualList_length : ∀ (k : ℕ) (gs : List Gate), (dualList k gs).length = gs.length
  | _, [] => rfl
  | k, g :: gs => by simp [dualList, dualList_length (k + 1) gs]

lemma mem_dualList : ∀ (gs : List Gate) (k : ℕ) (g' : Gate), g' ∈ dualList k gs →
    ∃ k' : ℕ, ∃ g ∈ gs, g' = dualGate k' g := by
  intro gs
  induction gs with
  | nil =>
    intro k g' h
    simp [dualList] at h
  | cons g gs ih =>
    intro k g' h
    simp only [dualList, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, g, List.mem_cons_self, h⟩
    · obtain ⟨k', g0, hg0, he⟩ := ih (k + 1) g' h
      exact ⟨k', g0, List.mem_cons_of_mem _ hg0, he⟩

lemma getElem?_dualList : ∀ (gs : List Gate) (k i : ℕ),
    (dualList k gs)[i]? = (gs[i]?).map (dualGate (k + i)) := by
  intro gs
  induction gs with
  | nil =>
    intro k i
    simp [dualList]
  | cons g gs ih =>
    intro k i
    cases i with
    | zero => simp [dualList]
    | succ i =>
      simp only [dualList, List.getElem?_cons_succ]
      rw [ih (k + 1) i]
      congr 2
      omega

lemma dualGate_ok (k : ℕ) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((dualGate k g).op = GateOp.and ∨ (dualGate k g).op = GateOp.or ∨
      (dualGate k g).op = GateOp.not) ∧ (dualGate k g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hl⟩ := h
  simp only at hop hl
  rcases hop with h | h | h <;> subst h
  · simp only [dualGate]
    split <;> simp [hl]
  · simp only [dualGate]
    refine ⟨by simp, ?_⟩
    exact le_trans (List.length_filter_le _ _) hl
  · simp only [dualGate]
    split <;> simp [hl]

lemma dualGate_not (k : ℕ) (g : Gate) (h : (dualGate k g).op = GateOp.not) :
    g.op = GateOp.not := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and =>
    simp only [dualGate] at h
    split at h <;> simp at h
  | or => simp [dualGate] at h
  | not => rfl
  | mod m => simp [dualGate] at h
  | maj => simp [dualGate] at h

lemma main : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  intro n gates hgates
  refine ⟨dualList n gates, dualList_length n gates, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨k, g, hg, rfl⟩ := mem_dualList gates n g' hg'
    exact dualGate_ok k g (hgates g hg)
  · intro i g' hi hop
    rw [getElem?_dualList] at hi
    cases hgi : gates[i]? with
    | none => simp [hgi] at hi
    | some g =>
      rw [hgi] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      subst hi
      exact ⟨g, rfl, dualGate_not _ g hop⟩
  · intro w x hw
    have hneg : ∀ i < n, (List.ofFn x).getD i false =
        !((List.ofFn (fun p : Fin n => !x p)).getD i false) := by
      intro i hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    exact fold_dual gates (fun g hg => (hgates g hg).1) n (List.ofFn (fun p : Fin n => !x p))
      (List.ofFn x) (by simp) (by simp) hneg w hw

end PEqualNP.Outside.L_meta_1322

theorem PEqualNP.Outside.L_meta_1322 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  exact PEqualNP.Outside.L_meta_1322.main
