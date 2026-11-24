import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1106

theorem count_split (x : List Bool) (i : ℕ) (h : i < x.length) :
    x.count true = (x.eraseIdx i).count true + (if x.getD i false = true then 1 else 0) := by
  have hx : x.count true = (x.take i ++ x.drop i).count true := by
    rw [List.take_append_drop]
  have hd : x.drop i = x[i] :: x.drop (i+1) := List.drop_eq_getElem_cons h
  have he : x.eraseIdx i = x.take i ++ x.drop (i+1) := List.eraseIdx_eq_take_drop_succ x i
  have hg : x.getD i false = x[i] := by
    simp [List.getD_eq_getElem?_getD, h]
  rw [hx, he, hg, hd, List.count_append, List.count_append, List.count_cons]
  cases x[i] <;> simp <;> omega

end PEqualNP.Outside.L_meta_1106

theorem PEqualNP.Outside.L_meta_1106 : ∀ (x : List Bool) (i k : ℕ), i < x.length → x.count true = k → ((!(x.getD i false)) = decide (k ≤ (x.eraseIdx i).count true)) := by
  intro x i k h hk
  have hs := PEqualNP.Outside.L_meta_1106.count_split x i h
  rw [hk] at hs
  cases hb : x.getD i false
  · rw [hb] at hs
    simp only [Bool.false_eq_true, if_false, add_zero] at hs
    simp [hs]
  · rw [hb] at hs
    simp only [if_true] at hs
    simp [hs]
