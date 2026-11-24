import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1334

open PEqualNP.CircuitLowerBounds

lemma getD_snoc_len (L : List Bool) (v : Bool) : (L ++ [v]).getD L.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (v : Bool) (i : ℕ) (h : L.length < i) : (L ++ [v]).getD i false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]
  rfl

lemma agree (j : ℕ) : ∀ (gs1 gs2 : List Gate) (w1 w2 : List Bool),
    gs1.length = gs2.length → w1.length = w2.length →
    (∀ i, i ≠ j → w1.getD i false = w2.getD i false) →
    (∀ (k : ℕ) (h1 : k < gs1.length) (h2 : k < gs2.length), w1.length + k ≠ j →
      gs1[k] = gs2[k] ∧ j ∉ (gs2[k]).inputs) →
    ∀ i, i ≠ j →
      (gs1.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false =
      (gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false := by
  intro gs1
  induction gs1 with
  | nil =>
    intro gs2 w1 w2 hl hw ha hg i hi
    cases gs2 with
    | nil => simpa using ha i hi
    | cons _ _ => simp at hl
  | cons g1 t1 ih =>
    intro gs2 w1 w2 hl hw ha hg i hi
    cases gs2 with
    | nil => simp at hl
    | cons g2 t2 =>
      simp only [List.foldl_cons]
      refine ih t2 _ _ (by simpa using hl) (by simp [hw]) ?_ ?_ i hi
      · intro i' hi'
        rcases lt_trichotomy i' w1.length with h | h | h
        · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (by omega)]
          exact ha i' hi'
        · subst h
          have hk := hg 0 (by simp) (by simp) (by omega)
          simp only [List.getElem_cons_zero] at hk
          obtain ⟨he, hj⟩ := hk
          subst he
          rw [getD_snoc_len, hw, getD_snoc_len]
          congr 1
          apply List.map_congr_left
          intro a ha'
          apply ha a
          intro hEq
          exact hj (hEq ▸ ha')
        · rw [getD_snoc_gt _ _ _ h, getD_snoc_gt _ _ _ (by omega)]
      · intro k h1 h2 hk
        have := hg (k + 1) (by simp; omega) (by simp; omega) (by simp at hk; omega)
        simpa using this

end PEqualNP.Outside.L_meta_1334

theorem PEqualNP.Outside.L_meta_1334 : ∀ (n q w : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g' : PEqualNP.CircuitLowerBounds.Gate), (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gates[k]? = some g → n + q ∉ g.inputs) → w ≠ n + q → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set q g', w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) := by
  intro n q w gates g' hno hw x
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  exact PEqualNP.Outside.L_meta_1334.agree (n + q) (gates.set q g') gates (List.ofFn x) (List.ofFn x)
    (by simp) rfl (fun i _ => rfl) (by
      intro k h1 h2 hk
      simp only [List.length_ofFn] at hk
      have hkq : q ≠ k := by omega
      refine ⟨by simp [List.getElem_set, hkq], ?_⟩
      exact hno k _ (List.getElem?_eq_getElem h2)) w hw
