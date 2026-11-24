import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1331

def W (gs : List Gate) (x : List Bool) : List Bool := Circuit.wires ⟨gs, 0⟩ x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, Circuit.wires, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W, Circuit.wires]
  | append_singleton gs g ih =>
    rw [W_snoc, List.length_append, ih]
    simp
    omega

theorem key (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, ∀ u ∈ g.inputs, n ≤ u)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n) :
    ∀ i, n ≤ i → (W gs x).getD i false = (W gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    have e1 : W [] x = x := by simp [W, Circuit.wires]
    have e2 : W [] y = y := by simp [W, Circuit.wires]
    rw [e1, e2, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hg g' (List.mem_append_left _ hg'))
    intro i hi
    rw [W_snoc, W_snoc]
    have hlx := W_length gs x
    have hly := W_length gs y
    by_cases h1 : i < n + gs.length
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ih' i hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      have hv : (g.inputs.map fun i => (W gs x).getD i false) =
          (g.inputs.map fun i => (W gs y).getD i false) := by
        apply List.map_congr_left
        intro u hu
        exact ih' u (hg g (List.mem_append_right _ (List.mem_singleton_self g)) u hu)
      rw [hv, hlx, hly, hx, hy]

end PEqualNP.Outside.L_meta_1331

theorem PEqualNP.Outside.L_meta_1331 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G : Finset (Fin gates.length)), (∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u) → ∀ k ∈ G, (∀ i ∈ G, k ≤ i) → ∀ w ∈ (gates.get k).inputs, n ≤ w → ∀ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn y) := by
  intro n gates G hG k hk hmin w hw hnw x y
  have hgs : ∀ g ∈ gates.take k.val, ∀ u ∈ g.inputs, n ≤ u := by
    intro g hg u hu
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
    have hik : i < k.val := by
      have := List.length_take_le' k.val gates
      simp only [List.length_take] at hi
      omega
    have hil : i < gates.length := by
      simp only [List.length_take] at hi
      omega
    let j : Fin gates.length := ⟨i, hil⟩
    have hj : j ∉ G := by
      intro hjG
      have := hmin j hjG
      have : k.val ≤ i := this
      omega
    have hgj : gates.get j = g := by
      rw [← hgi, List.getElem_take]
      rfl
    exact hG j hj u (hgj ▸ hu)
  change (PEqualNP.Outside.L_meta_1331.W (gates.take k.val) (List.ofFn x)).getD w false =
    (PEqualNP.Outside.L_meta_1331.W (gates.take k.val) (List.ofFn y)).getD w false
  exact PEqualNP.Outside.L_meta_1331.key n _ hgs _ _ (by simp) (by simp) w hnw
