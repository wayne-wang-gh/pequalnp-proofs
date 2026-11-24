import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1701

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

private def Le (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ t, u.getD t false = true → v.getD t false = true

private lemma step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : List Bool) (h : Le u v) : Le (step u g) (step v g) := by
  refine ⟨by rw [step_len, step_len, h.1], fun t ht => ?_⟩
  by_cases hlt : t < u.length
  · rw [step_lt _ _ _ hlt] at ht
    rw [step_lt _ _ _ (by rw [← h.1]; exact hlt)]
    exact h.2 t ht
  · by_cases heq : t = u.length
    · rw [step_last _ _ _ heq] at ht
      rw [step_last _ _ _ (heq.trans h.1)]
      rcases hop with hand | hor
      · rw [hand] at ht ⊢
        exact (all_true _ _).mpr (fun i hi => h.2 i ((all_true _ _).mp ht i hi))
      · rw [hor] at ht ⊢
        obtain ⟨i, hi, hti⟩ := (any_true _ _).mp ht
        exact (any_true _ _).mpr ⟨i, hi, h.2 i hti⟩
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega)] at ht
      exact Bool.noConfusion ht

private lemma wires_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ u v : List Bool, Le u v → Le (gs.foldl step u) (gs.foldl step v) := by
  induction gs with
  | nil =>
    intro u v h
    exact h
  | cons g gs ih =>
    intro u v h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (step_mono g (hg g (List.mem_cons.mpr (Or.inl rfl))) u v h)

private lemma eval_fold (gs : List Gate) (o : ℕ) (u : List Bool) :
    Circuit.eval ⟨gs, o⟩ u = (gs.foldl step u).getD o false := rfl

private lemma eval_mono (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (u v : List Bool) (h : Le u v)
    (he : Circuit.eval ⟨gs, o⟩ u = true) : Circuit.eval ⟨gs, o⟩ v = true := by
  rw [eval_fold] at he ⊢
  exact (wires_mono gs hg u v h).2 o he

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

private lemma le_ofFn {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i = true → g i = true) :
    Le (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, fun t ht => ?_⟩
  obtain ⟨hlt, hx⟩ := ofFn_getD_true f t ht
  exact (ofFn_getD_val g ⟨t, hlt⟩).trans (h _ hx)

private lemma le_app (a x b y : Fin 16 → Bool) (h1 : ∀ i, a i = true → x i = true)
    (h2 : ∀ i, b i = true → y i = true) :
    Le (List.ofFn a ++ List.ofFn b) (List.ofFn x ++ List.ofFn y) := by
  rw [← List.ofFn_fin_append a b, ← List.ofFn_fin_append x y]
  refine le_ofFn _ _ (fun i => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, Fin.append_left]
    exact h1 j
  · rw [Fin.append_right, Fin.append_right]
    exact h2 j

set_option maxRecDepth 100000 in
private def gs : List Gate := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 78] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 93] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [104, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [105, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [106, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [107, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [109, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [111, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [112, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [114, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [115, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [116, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [119, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [120, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [121, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [122, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [140, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [141, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [157, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [160, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [161, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [162, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [171, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [177, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [180, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [181, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [182, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [184, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [188, 189] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 190] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [196, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [200, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [204, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [212, 213] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [220, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 225] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 230] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 233] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 238] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [187, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [195, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [203, 207] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 249] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [256, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 259] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }]

set_option maxRecDepth 100000 in
private def inc : List (ℕ × ℕ) := [(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)]

private def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

private lemma isAO_spec (op : GateOp) (h : isAO op = true) :
    op = GateOp.and ∨ op = GateOp.or := by
  cases op with
  | and => exact Or.inl rfl
  | or => exact Or.inr rfl
  | not => exact Bool.noConfusion (show false = true from h)
  | mod m => exact Bool.noConfusion (show false = true from h)
  | maj => exact Bool.noConfusion (show false = true from h)

set_option maxRecDepth 100000 in
private lemma gs_all : gs.all (fun g => isAO g.op) = true := by decide +kernel

private lemma gs_ao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg =>
  isAO_spec g.op (List.all_eq_true.mp gs_all g hg)

set_option maxRecDepth 100000 in
private lemma chk_len : (⟨gs, 262⟩ : Circuit).gates.length = 231 := by decide +kernel

set_option maxRecDepth 100000 in
private lemma chk_rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) ⟨gs, 262⟩ := by
  decide +kernel

private def mop (K : ℕ) (op : GateOp) (l : List ℕ) : ℕ :=
  match op with
  | GateOp.and => l.foldr Nat.land (2 ^ K - 1)
  | GateOp.or => l.foldr Nat.lor 0
  | _ => 0

private def mstep (K : ℕ) (m : List ℕ) (g : Gate) : List ℕ :=
  m ++ [mop K g.op (g.inputs.map fun i => m.getD i 0)]

private lemma mstep_len (K : ℕ) (m : List ℕ) (g : Gate) :
    (mstep K m g).length = m.length + 1 := by
  simp [mstep]

private lemma mstep_lt (K : ℕ) (m : List ℕ) (g : Gate) (i : ℕ) (hi : i < m.length) :
    (mstep K m g).getD i 0 = m.getD i 0 := by
  simp [mstep, List.getD, List.getElem?_append_left hi]

private lemma mstep_last (K : ℕ) (m : List ℕ) (g : Gate) (k : ℕ) (hk : k = m.length) :
    (mstep K m g).getD k 0 = mop K g.op (g.inputs.map fun i => m.getD i 0) := by
  subst hk
  simp [mstep, List.getD]

private lemma gate_bit (K k : ℕ) (hk : k < K) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (inputs : List ℕ) (fm : ℕ → ℕ) (fw : ℕ → Bool)
    (h : ∀ i, fw i = Nat.testBit (fm i) k) :
    Nat.testBit (mop K op (inputs.map fm)) k = op.eval (inputs.map fw) := by
  rcases hop with rfl | rfl
  · show Nat.testBit (List.foldr Nat.land (2 ^ K - 1) (List.map fm inputs)) k =
      (List.map fw inputs).all id
    induction inputs with
    | nil => simp [Nat.testBit_two_pow_sub_one, hk]
    | cons a l ih =>
      show Nat.testBit (fm a &&& List.foldr Nat.land (2 ^ K - 1) (List.map fm l)) k =
        (fw a && (List.map fw l).all id)
      rw [Nat.testBit_and, ih, h a]
  · show Nat.testBit (List.foldr Nat.lor 0 (List.map fm inputs)) k =
      (List.map fw inputs).any id
    induction inputs with
    | nil => simp
    | cons a l ih =>
      show Nat.testBit (fm a ||| List.foldr Nat.lor 0 (List.map fm l)) k =
        (fw a || (List.map fw l).any id)
      rw [Nat.testBit_or, ih, h a]

private def Rep (k : ℕ) (w : List Bool) (m : List ℕ) : Prop :=
  w.length = m.length ∧ ∀ t, w.getD t false = Nat.testBit (m.getD t 0) k

private lemma rep_step (K k : ℕ) (hk : k < K) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : List Bool) (m : List ℕ)
    (h : Rep k w m) : Rep k (step w g) (mstep K m g) := by
  have h1 := h.1
  refine ⟨by rw [step_len, mstep_len, h.1], fun t => ?_⟩
  by_cases hlt : t < w.length
  · rw [step_lt w g t hlt, mstep_lt K m g t (by omega)]
    exact h.2 t
  · by_cases heq : t = w.length
    · rw [step_last w g t heq, mstep_last K m g t (heq.trans h.1)]
      exact (gate_bit K k hk g.op hop g.inputs (fun i => m.getD i 0)
        (fun i => w.getD i false) h.2).symm
    · rw [List.getD_eq_default (step w g) false (by rw [step_len]; omega),
        List.getD_eq_default (mstep K m g) 0 (by rw [mstep_len]; omega)]
      exact (Nat.zero_testBit k).symm

private lemma rep_fold (K k : ℕ) (hk : k < K) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w : List Bool) (m : List ℕ), Rep k w m →
      Rep k (gs.foldl step w) (gs.foldl (mstep K) m) := by
  induction gs with
  | nil =>
    intro w m h
    exact h
  | cons g gs ih =>
    intro w m h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (rep_step K k hk g (hg g (List.mem_cons.mpr (Or.inl rfl))) w m h)

private lemma eval_bit (K k : ℕ) (hk : k < K) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (w : List Bool) (m : List ℕ)
    (h : Rep k w m) :
    Circuit.eval ⟨gs, o⟩ w = Nat.testBit ((gs.foldl (mstep K) m).getD o 0) k := by
  rw [eval_fold]
  exact (rep_fold K k hk gs hg w m h).2 o

private lemma rep_init (k : ℕ) (w : List Bool) (m : List ℕ) (hw : w.length = 32)
    (hm : m.length = 32) (h : ∀ t < 32, w.getD t false = Nat.testBit (m.getD t 0) k) :
    Rep k w m := by
  refine ⟨hw.trans hm.symm, fun t => ?_⟩
  by_cases ht : t < 32
  · exact h t ht
  · rw [List.getD_eq_default w false (by omega), List.getD_eq_default m 0 (by omega)]
    exact (Nat.zero_testBit k).symm

private def m0 : List ℕ := [204590034789694012353307774444279333600051359130119682272427885003772966056983619054902028637720753779309205997244701661915006831207789889367048257535, 409180069579388024706615548888558667200102718260239364544855770504831226235120953443534691376178640840180834696341822326831797252277699848603871150080, 818360139158776049413231097777117334400205436520478729089744130104066680681277247455507870663629400695841700201550085337634765706588389847419636940800, 1636720278317552098826462195554234668800410873040957460315116782770440938304259376193230286841826666315612473543506992183042655016672398482504207564800, 3273440556635104197652924391108469337600821746082054864093452662167934483238487175290614899986227396348129357052216881185273343283462972288797056696320, 6546881113270208395305848782216938675201643501333204823147236645379500944127316651673870553612332251915214523693181637961829217856531887264129613824000, 13093762226540416790611697564433877350403887614919209609323131328460329466981686177248096327688317337976794792242937470631933920256510636209270832496640, 26187524453080833581223395128867754740131021894796275474631987173397211089578249949215244275647072713724203675317077876720424501381761944956777560801280, 52375048906161667162446790257738081525175642372519137025200235835929518501280967152382928922863169529516244738041731062787513560062109433353790480711680, 104750097812323334324893580683376652626071353099818109644634918226468333169096861351767747192778597872491972776399662780195900205917206600443817696952320, 209500195624646668649798078248632310304658540423402299182659049018768440242833263380438146186023737282353417767775614460447965967298371219086762080993280, 419000391249293338003688245544476767173124308733252929614208630905249361239241992045840987284373562910067621052618408798598491507402199193651850363535360, 838000782498631330843530641915516610331243198107556371959423885109728621692045546313060670285869640449246497166960125694270725560281735596448466327306240, 1676001567728655696622155053813254836435567503258800411767364986876209706361902943122612619133232826970780194810715054901533496858634126982028062663639040, 3352156567057343279730759213380514165620335317335191000348494346325414495509127080130167721274943014112239591938431757076897552267880282692070203426078720, 13407705638046998437713325827737016542199152306144080746015354951953759904400198682690353362675628909186629748954637232325951325762322171487420735857623040, 25921761997888976601359038064773566096456962966795229959861867852842933838815457507505161486253524973294911249790950569777023954254521916053748285567991809, 25027908133187373791819937441280952960902100501445519613221011389032977537118942920839358196117694147227891399588194426720674726676440759887799094029189122, 23240050383786922002990987229001866144002046916550642989520735701969810038563619754722319033202643141416038524001024196250051219524641711008926303120523268, 13407903403835327403372714153884149409034304919691714383251684447158112915951604409077498643523839004374088168389009958621183446471883046217493140476526600, 13407906922099628062665018829140044519409170335702439642706711683895441275687514344229359226389406107347001284379267121536118516174118160734994189444448272, 23040782730484848042213102345218459468149279365049022752076022060605923050017808913607989388810148503318750820849702046693957724099111207679970183475101728, 25060233358676619257555361040667522501119452743662053444905782516772073000222870782478699553681459464353099390935478555375019518946292362986521896907964480, 25858134497069381989564002602697997778279182875432944486049721693777553719376992573270815138181999778254606913149899356716859772595015649183915030899327104, 24707315548746565912679495581659817312809021932133703866320532369230042674503707260053060728953434705771322455218651834646141246538860967396808104131690752, 25741518177239256816820679817867504886381440832709187399560611387556676314422770008854524101263544000968013402715388053189406960899481627984564420970807808, 13407908561042625264040702990006597954275423861626855619350096531946192325615778967492576344909730516433549700425452377851534201066953756174841413187404800, 23402901566567672385294412170748449500384994898273009721497160599625051483519230373999696893924927498908687157210326186015239363860165596447849400842061824, 23332319081568477810049840815090954392305203934837658033604104673366512854509045432315738208491942696748210625463005304836230020205039113874039059100209152, 13407909216619824144590974507952271921880631378908295725043460569289358488134428653446826902164739100784603078858400897414578378450048159634076868192247808, 25551249444884842060633840145820893554234689953643950872677428319345090637834054483346691976021966140175587332288449846740306873199703788843342937001574400, 24925203935746859717141556732211151765224109727942364227714808855086219431076834094722524865798047553259486109761854364800466493919352511342009220811751424]

private lemma m0_len : m0.length = 32 := by decide +kernel

set_option maxRecDepth 100000 in
private lemma out_eq : (gs.foldl (mstep 513) m0).getD 262 0 = 16325833504635217515997997160459086407416256927044605023023015165074167959825 := by
  decide +kernel

set_option maxRecDepth 100000 in
private lemma chk_out_lo : ∀ p l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ inc →
    Nat.testBit 16325833504635217515997997160459086407416256927044605023023015165074167959825 (16 * p.val + l.val) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private lemma chk_out_hi : ∀ a b : Fin 16,
    Nat.testBit 16325833504635217515997997160459086407416256927044605023023015165074167959825 (256 + 16 * a.val + b.val) = false := by
  decide +kernel

private lemma chk_out_empty : Nat.testBit 16325833504635217515997997160459086407416256927044605023023015165074167959825 512 = false := by
  decide +kernel

set_option maxRecDepth 100000 in
private lemma chk_lo_rep : ∀ p l : Fin 16, ∀ t < 32,
    (List.ofFn (fun i : Fin 16 => decide (i = p)) ++
      List.ofFn (fun i : Fin 16 => decide (i = l))).getD t false =
      Nat.testBit (m0.getD t 0) (16 * p.val + l.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
private lemma chk_hi_rep : ∀ a b : Fin 16, a ≤ b → ∀ t < 32,
    (List.ofFn (fun i : Fin 16 => decide (i = a ∨ i = b)) ++
      List.ofFn (fun l : Fin 16 =>
        decide (((a : ℕ), (l : ℕ)) ∉ inc ∧ ((b : ℕ), (l : ℕ)) ∉ inc))).getD t false =
      Nat.testBit (m0.getD t 0) (256 + 16 * a.val + b.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
private lemma chk_empty_rep : ∀ t < 32,
    (List.ofFn (fun _ : Fin 16 => false) ++ List.ofFn (fun _ : Fin 16 => true)).getD t false =
      Nat.testBit (m0.getD t 0) 512 := by
  decide +kernel

private lemma chk_lo : ∀ p l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ inc →
    Circuit.eval ⟨gs, 262⟩ (List.ofFn (fun i : Fin 16 => decide (i = p)) ++
      List.ofFn (fun i : Fin 16 => decide (i = l))) = true := by
  intro p l hpl
  have hk : 16 * p.val + l.val < 513 := by
    have h1 := p.isLt
    have h2 := l.isLt
    omega
  have e := eval_bit 513 (16 * p.val + l.val) hk gs 262 gs_ao _ m0
    (rep_init _ _ m0 (by simp) m0_len (chk_lo_rep p l))
  rw [out_eq] at e
  exact e.trans (chk_out_lo p l hpl)

private lemma chk_hi : ∀ a b : Fin 16, a ≤ b →
    Circuit.eval ⟨gs, 262⟩ (List.ofFn (fun i : Fin 16 => decide (i = a ∨ i = b)) ++
      List.ofFn (fun l : Fin 16 =>
        decide (((a : ℕ), (l : ℕ)) ∉ inc ∧ ((b : ℕ), (l : ℕ)) ∉ inc))) = false := by
  intro a b hab
  have hk : 256 + 16 * a.val + b.val < 513 := by
    have h1 := a.isLt
    have h2 := b.isLt
    omega
  have e := eval_bit 513 (256 + 16 * a.val + b.val) hk gs 262 gs_ao _ m0
    (rep_init _ _ m0 (by simp) m0_len (chk_hi_rep a b hab))
  rw [out_eq] at e
  exact e.trans (chk_out_hi a b)

private lemma chk_empty : Circuit.eval ⟨gs, 262⟩
    (List.ofFn (fun _ : Fin 16 => false) ++ List.ofFn (fun _ : Fin 16 => true)) = false := by
  have e := eval_bit 513 512 (by decide) gs 262 gs_ao _ m0
    (rep_init _ _ m0 (by simp) m0_len chk_empty_rep)
  rw [out_eq] at e
  exact e.trans chk_out_empty

private lemma lower (x y : Fin 16 → Bool) (p l : Fin 16) (hpl : ((p : ℕ), (l : ℕ)) ∈ inc)
    (hx : x p = true) (hy : y l = true) :
    Circuit.eval ⟨gs, 262⟩ (List.ofFn x ++ List.ofFn y) = true := by
  refine eval_mono gs 262 gs_ao _ _
    (le_app (fun i : Fin 16 => decide (i = p)) x (fun i : Fin 16 => decide (i = l)) y
      (fun i hi => ?_) (fun i hi => ?_)) (chk_lo p l hpl)
  · have e : i = p := of_decide_eq_true hi
    rw [e]
    exact hx
  · have e : i = l := of_decide_eq_true hi
    rw [e]
    exact hy

private lemma upper_core (x y : Fin 16 → Bool) (a b : Fin 16) (hab : a ≤ b)
    (hx : ∀ p, x p = true → p = a ∨ p = b)
    (hya : ∀ l, y l = true → ((a : ℕ), (l : ℕ)) ∉ inc)
    (hyb : ∀ l, y l = true → ((b : ℕ), (l : ℕ)) ∉ inc) :
    Circuit.eval ⟨gs, 262⟩ (List.ofFn x ++ List.ofFn y) = false := by
  refine Bool.eq_false_iff.mpr (fun he => ?_)
  have h2 := eval_mono gs 262 gs_ao _ _
    (le_app x (fun i : Fin 16 => decide (i = a ∨ i = b)) y
      (fun l : Fin 16 => decide (((a : ℕ), (l : ℕ)) ∉ inc ∧ ((b : ℕ), (l : ℕ)) ∉ inc))
      (fun i hi => decide_eq_true (hx i hi))
      (fun i hi => decide_eq_true ⟨hya i hi, hyb i hi⟩)) he
  exact Bool.noConfusion ((chk_hi a b hab).symm.trans h2)

private lemma upper_empty (x y : Fin 16 → Bool) (hx : ∀ p, x p ≠ true) :
    Circuit.eval ⟨gs, 262⟩ (List.ofFn x ++ List.ofFn y) = false := by
  refine Bool.eq_false_iff.mpr (fun he => ?_)
  have h2 := eval_mono gs 262 gs_ao _ _
    (le_app x (fun _ : Fin 16 => false) y (fun _ : Fin 16 => true)
      (fun i hi => absurd hi (hx i)) (fun _ _ => rfl)) he
  exact Bool.noConfusion (chk_empty.symm.trans h2)

private lemma main (x y : Fin 16 → Bool)
    (hc : (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2) :
    Circuit.eval ⟨gs, 262⟩ (List.ofFn x ++ List.ofFn y) =
      decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ inc ∧ x p = true ∧ y l = true) := by
  by_cases hQ : ∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ inc ∧ x p = true ∧ y l = true
  · obtain ⟨p, l, hpl, hx, hy⟩ := hQ
    exact (lower x y p l hpl hx hy).trans (decide_eq_true ⟨p, l, hpl, hx, hy⟩).symm
  · refine Eq.trans ?_ (decide_eq_false hQ).symm
    by_cases hne : ∃ a, x a = true
    · obtain ⟨a, ha⟩ := hne
      have hex : ∃ b, x b = true ∧ ∀ q, x q = true → q = a ∨ q = b := by
        by_cases h2 : ∃ b, b ≠ a ∧ x b = true
        · obtain ⟨b, hba, hb⟩ := h2
          refine ⟨b, hb, fun q hq => ?_⟩
          by_contra hcon
          have hqa : q ≠ a := fun h => hcon (Or.inl h)
          have hqb : q ≠ b := fun h => hcon (Or.inr h)
          have h3 : ({a, b, q} : Finset (Fin 16)).card = 3 :=
            Finset.card_eq_three.mpr ⟨a, b, q, hba.symm, hqa.symm, hqb.symm, rfl⟩
          have hsub : ({a, b, q} : Finset (Fin 16)) ⊆
              Finset.univ.filter (fun p : Fin 16 => x p = true) := by
            intro r hr
            rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ r, ?_⟩
            rcases hr with hr | hr | hr
            · rw [hr]
              exact ha
            · rw [hr]
              exact hb
            · rw [hr]
              exact hq
          have h4 := Finset.card_le_card hsub
          rw [h3] at h4
          exact absurd (le_trans h4 hc) (by decide)
        · refine ⟨a, ha, fun q hq => ?_⟩
          by_contra hcon
          exact h2 ⟨q, fun h => hcon (Or.inl h), hq⟩
      obtain ⟨b, hb, hall⟩ := hex
      have hya : ∀ c, x c = true → ∀ l, y l = true → ((c : ℕ), (l : ℕ)) ∉ inc :=
        fun c hc' l hl hin => hQ ⟨c, l, hin, hc', hl⟩
      rcases le_total a b with hab | hab
      · exact upper_core x y a b hab hall (hya a ha) (hya b hb)
      · exact upper_core x y b a hab (fun q hq => (hall q hq).symm) (hya b hb) (hya a ha)
    · exact upper_empty x y (fun p hp => hne ⟨p, hp⟩)

set_option maxRecDepth 100000 in
theorem main_aux : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 78] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 93] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [104, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [105, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [106, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [107, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [109, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [111, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [112, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [114, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [115, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [116, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [119, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [120, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [121, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [122, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [140, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [141, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [157, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [160, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [161, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [162, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [171, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [177, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [180, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [181, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [182, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [184, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [188, 189] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 190] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [196, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [200, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [204, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [212, 213] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [220, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 225] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 230] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 233] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 238] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [187, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [195, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [203, 207] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 249] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [256, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 259] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }], output := 262 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 231 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C ∧ ∀ (x y : Fin 16 → Bool), (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2 →
    C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) := by
  intro C hC
  have hC2 : C = (⟨gs, 262⟩ : Circuit) := hC
  subst hC2
  exact ⟨chk_len, chk_rb, fun x y hc => main x y hc⟩

end PEqualNP.Outside.L_meta_1701

theorem PEqualNP.Outside.L_meta_1701 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 78] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 93] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [104, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [105, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [106, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [107, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [109, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [111, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [112, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [114, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [115, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [116, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [119, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [120, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [121, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [122, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [140, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [141, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [157, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [160, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [161, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [162, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [171, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [177, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [180, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [181, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [182, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [184, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [188, 189] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 190] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [196, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [200, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [204, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [212, 213] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [220, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 225] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 230] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 233] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 238] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [187, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [195, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [203, 207] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 249] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [256, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 259] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }], output := 262 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 231 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C ∧ ∀ (x y : Fin 16 → Bool), (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2 →
    C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) :=
  PEqualNP.Outside.L_meta_1701.main_aux
