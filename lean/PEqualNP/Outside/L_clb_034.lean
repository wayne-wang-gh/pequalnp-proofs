import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_034_aux
open PEqualNP.CircuitLowerBounds

lemma pair (n k : ℕ) (hn : 2 ≤ n) :
    ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
      x.all id = true ∧ y.all id ≠ true ∧ x.getD k false = y.getD k false := by
  let j : Fin n := ⟨if k = 0 then 1 else 0, by split <;> omega⟩
  have hj : j.val ≠ k := by dsimp [j]; split <;> omega
  refine ⟨List.ofFn (fun _ : Fin n => true),
    List.ofFn (fun i : Fin n => decide (i ≠ j)), by simp, by simp, by simp, ?_, ?_⟩
  · intro h
    have hfalse : false ∈ List.ofFn (fun i : Fin n => decide (i ≠ j)) := by
      exact List.mem_ofFn.mpr ⟨j, by simp⟩
    have := List.all_eq_true.mp h false hfalse
    simp at this
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split
    · simp only [Option.getD_some]
      have : (⟨k, by assumption⟩ : Fin n) ≠ j := by
        intro h; have := congrArg Fin.val h; exact hj this.symm
      simp [this]
    · simp

lemma one (C : Circuit) (n : ℕ) (hs : C.size ≤ 1)
    (hi : ∀ g ∈ C.gates, g.inputs.length ≤ 1) :
    ∃ k : ℕ, ∀ x y : List Bool, x.length = n → y.length = n →
      x.getD k false = y.getD k false → C.eval x = C.eval y := by
  rcases C with ⟨gs, out⟩
  cases gs with
  | nil => exact ⟨out, by intros; assumption⟩
  | cons g gs =>
    have hz : gs = [] := by
      have hh : gs.length = 0 := by simpa [Circuit.size] using hs
      simpa using hh
    subst gs
    by_cases ho : out < n
    · refine ⟨out, ?_⟩
      intro x y hx hy he
      simpa only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
        List.getD_append _ _ _ _ (by omega : out < x.length),
        List.getD_append _ _ _ _ (by omega : out < y.length)] using he
    · have hg := hi g (by simp)
      rcases g with ⟨op, ins⟩
      cases ins with
      | nil =>
        refine ⟨0, ?_⟩
        intro x y hx hy he
        simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
          List.map_nil, List.getD_append_right _ _ _ _ (by omega : x.length ≤ out),
          List.getD_append_right _ _ _ _ (by omega : y.length ≤ out), hx, hy]
      | cons k ks =>
        have hz : ks = [] := by
          have hh : ks.length = 0 := by simpa using hg
          simpa using hh
        subst ks
        refine ⟨k, ?_⟩
        intro x y hx hy he
        simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
          List.map_cons, List.map_nil, List.getD_append_right _ _ _ _ (by omega : x.length ≤ out),
          List.getD_append_right _ _ _ _ (by omega : y.length ≤ out), hx, hy, he]
end PEqualNP.Outside.L_clb_034_aux

theorem PEqualNP.Outside.L_clb_034 : ∀ (n d : ℕ), 2 ≤ n → ({x : List Bool | x.all id = true} : Language Bool) ∉ PEqualNP.CircuitLowerBounds.SizeDepth {PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} (fun m : ℕ => if m = n then 1 else m + 2) d := by
  intro n d hn h
  obtain ⟨C, hg, hs, hd, hc⟩ := h n
  simp only [if_pos rfl] at hg hs
  obtain ⟨k, hk⟩ := PEqualNP.Outside.L_clb_034_aux.one C n hs (fun g hgm => (hg g hgm).2)
  obtain ⟨x, y, hx, hy, hxt, hyf, he⟩ := PEqualNP.Outside.L_clb_034_aux.pair n k hn
  have hce := hk x y hx hy he
  have hcx := (hc x hx).mpr hxt
  have hcy := (hc y hy).mp (hce ▸ hcx)
  exact hyf hcy
