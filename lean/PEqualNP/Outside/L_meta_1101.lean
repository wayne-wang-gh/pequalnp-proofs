import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1101

open PEqualNP.CircuitLowerBounds

-- One gate appended to the wire list.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- Running a list of gates.
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (step w g) := rfl

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_pre (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step; exact List.getD_append _ _ _ _ h

theorem step_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

theorem run_len (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run_nil]
  | cons g gs ih => intro w; rw [run_cons, ih, step_len]; simp; omega

theorem run_pre (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [run_cons, ih _ _ (by rw [step_len]; omega), step_pre _ _ _ h]

-- One block per input k: wire p is s AND k, wire p+1 is t OR p, wire p+2 is s OR k.
def blk : ℕ → ℕ → ℕ → List ℕ → List Gate
  | _, _, _, [] => []
  | p, s, t, k :: ks =>
      ⟨GateOp.and, [s, k]⟩ :: ⟨GateOp.or, [t, p]⟩ :: ⟨GateOp.or, [s, k]⟩ :: blk (p + 3) (p + 2) (p + 1) ks

def res : ℕ → ℕ → ℕ → List ℕ → ℕ
  | _, _, t, [] => t
  | p, _, _, _ :: ks => res (p + 3) (p + 2) (p + 1) ks

-- The running pair: some true so far, two true so far.
def G : Bool → Bool → List Bool → Bool
  | _, b, [] => b
  | a, b, c :: l => G (a || c) (b || (a && c)) l

theorem blk_len : ∀ (ks : List ℕ) (p s t : ℕ), (blk p s t ks).length = 3 * ks.length := by
  intro ks
  induction ks with
  | nil => intro p s t; rfl
  | cons k ks ih => intro p s t; simp [blk, ih]; omega

theorem blk_fan : ∀ (ks : List ℕ) (p s t : ℕ), ∀ g ∈ blk p s t ks,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro ks
  induction ks with
  | nil => intro p s t g hg; simp [blk] at hg
  | cons k ks ih =>
    intro p s t g hg
    simp only [blk, List.mem_cons] at hg
    rcases hg with hg | hg | hg | hg
    · subst hg; simp
    · subst hg; simp
    · subst hg; simp
    · exact ih _ _ _ g hg

theorem blk_val (v : ℕ → Bool) : ∀ (ks : List ℕ) (p s t : ℕ) (w : List Bool) (a b : Bool),
    w.length = p → s < p → t < p → (∀ k ∈ ks, k < p ∧ w.getD k false = v k) →
    w.getD s false = a → w.getD t false = b →
    (run (blk p s t ks) w).getD (res p s t ks) false = G a b (ks.map v) := by
  intro ks
  induction ks with
  | nil => intro p s t w a b _ _ _ _ _ hb; simp only [blk, res, run_nil, List.map_nil, G]; exact hb
  | cons k ks ih =>
    intro p s t w a b hl hs ht hk ha hb
    simp only [blk, res, run_cons, List.map_cons, G]
    have hk0 := hk k (by simp)
    set w1 := step w ⟨GateOp.and, [s, k]⟩ with hw1
    set w2 := step w1 ⟨GateOp.or, [t, p]⟩ with hw2
    set w3 := step w2 ⟨GateOp.or, [s, k]⟩ with hw3
    have l1 : w1.length = p + 1 := by rw [hw1, step_len, hl]
    have l2 : w2.length = p + 2 := by rw [hw2, step_len, l1]
    have l3 : w3.length = p + 3 := by rw [hw3, step_len, l2]
    have e1 : ∀ i < p, w1.getD i false = w.getD i false := fun i hi =>
      step_pre _ _ _ (by omega)
    have e2 : ∀ i < p + 1, w2.getD i false = w1.getD i false := fun i hi =>
      step_pre _ _ _ (by omega)
    have e3 : ∀ i < p + 2, w3.getD i false = w2.getD i false := fun i hi =>
      step_pre _ _ _ (by omega)
    have vp : w1.getD p false = (a && v k) := by
      rw [← hl, hw1, step_last]
      simp only [GateOp.eval, List.map_cons, List.map_nil]
      rw [ha, hk0.2]; simp
    have vp1 : w2.getD (p + 1) false = (b || (a && v k)) := by
      rw [← l1, hw2, step_last]
      simp only [GateOp.eval, List.map_cons, List.map_nil]
      rw [vp, e1 _ ht, hb]; simp
    have vp2 : w3.getD (p + 2) false = (a || v k) := by
      rw [← l2, hw3, step_last]
      simp only [GateOp.eval, List.map_cons, List.map_nil]
      rw [e2 _ (by omega), e1 _ hs, ha, e2 _ (by omega), e1 _ hk0.1, hk0.2]; simp
    apply ih (p + 3) (p + 2) (p + 1) w3 _ _ l3 (by omega) (by omega)
    · intro k' hk'
      have := hk k' (by simp [hk'])
      refine ⟨by omega, ?_⟩
      rw [e3 _ (by omega), e2 _ (by omega), e1 _ this.1]; exact this.2
    · exact vp2
    · rw [e3 _ (by omega)]; exact vp1

theorem G_iff : ∀ (l : List Bool) (a b : Bool), G a b l = true ↔
    (b = true ∨ (a = true ∧ 1 ≤ l.count true) ∨ 2 ≤ l.count true) := by
  intro l
  induction l with
  | nil => intro a b; simp [G]
  | cons c l ih =>
    intro a b
    simp only [G]
    rw [ih, List.count_cons]
    generalize List.count true l = q
    cases a <;> cases b <;> cases c <;> simp <;> omega

theorem map_rest (x0 x1 : Bool) (rest : List Bool) :
    (List.range' 2 rest.length).map (fun i => (x0 :: x1 :: rest).getD i false) = rest := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range']
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [show 2 + 1 * i = i + 2 by omega, List.getElem_cons_succ]

end PEqualNP.Outside.L_meta_1101

open PEqualNP.Outside.L_meta_1101 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1101 : ∀ n : ℕ, 2 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.size ≤ 3 * n ∧ ∀ x : List Bool, x.length = n → (C.eval x = true ↔ 2 ≤ x.count true) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨⟨⟨GateOp.and, [0, 1]⟩ :: ⟨GateOp.or, [0, 1]⟩ :: blk (m + 4) (m + 3) (m + 2) (List.range' 2 m),
    res (m + 4) (m + 3) (m + 2) (List.range' 2 m)⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with hg | hg | hg
    · subst hg; simp
    · subst hg; simp
    · exact (blk_fan _ _ _ _ g hg).1
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with hg | hg | hg
    · subst hg; simp
    · subst hg; simp
    · have := (blk_fan _ _ _ _ g hg).2; omega
  · show (_ :: _ :: blk (m + 4) (m + 3) (m + 2) (List.range' 2 m)).length ≤ 3 * (m + 2)
    simp only [List.length_cons, blk_len, List.length_range']
    omega
  · intro x hx
    match x, hx with
    | x0 :: x1 :: rest, hx =>
    have hr : rest.length = m := by simp at hx; omega
    show (run _ _).getD _ false = true ↔ _
    rw [run_cons, run_cons]
    set w := step (step (x0 :: x1 :: rest) ⟨GateOp.and, [0, 1]⟩) ⟨GateOp.or, [0, 1]⟩ with hw
    have l0 : (x0 :: x1 :: rest).length = m + 2 := hx
    have l1 : (step (x0 :: x1 :: rest) ⟨GateOp.and, [0, 1]⟩).length = m + 3 := by
      rw [step_len, l0]
    have lw : w.length = m + 4 := by rw [hw, step_len, l1]
    have pre : ∀ i < m + 2, w.getD i false = (x0 :: x1 :: rest).getD i false := by
      intro i hi; rw [hw, step_pre _ _ _ (by omega), step_pre _ _ _ (by omega)]
    have vt : w.getD (m + 2) false = (x0 && x1) := by
      rw [hw, step_pre _ _ _ (by omega), ← l0, step_last]; simp [GateOp.eval]
    have vs : w.getD (m + 3) false = (x0 || x1) := by
      rw [hw, ← l1, step_last]
      simp only [GateOp.eval, List.map_cons, List.map_nil]
      rw [step_pre _ _ _ (by simp), step_pre _ _ _ (by simp)]; simp
    rw [blk_val (fun i => (x0 :: x1 :: rest).getD i false) _ (m + 4) (m + 3) (m + 2) w _ _ lw
      (by omega) (by omega)
      (fun k hk => by
        simp [List.mem_range'_1] at hk
        exact ⟨by omega, pre k (by omega)⟩) vs vt]
    rw [← hr, map_rest, G_iff, List.count_cons, List.count_cons]
    generalize List.count true rest = q
    cases x0 <;> cases x1 <;> simp <;> omega
