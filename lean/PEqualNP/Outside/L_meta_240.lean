import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_240

open PEqualNP.MetaComplexity

-- Reading past the end of a list gives `false`, so a run of `false` inputs stays `false`.
theorem getD_ofFn_false (n i : ℕ) :
    (List.ofFn (fun _ : Fin n => false)).getD i false = false := by
  simp [List.getD_eq_getElem?_getD]

-- Reading the last wire of a list appended with one value of `true` gives `true`.
theorem getD_append_true (l : List Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [true]).getD i false = true := by
  subst h
  simp [List.getD_eq_getElem?_getD]

theorem one_gate (n s : ℕ) (hs : 1 ≤ s) :
    HasBinarySize n (fun _ : Fin n → Bool => true) s := by
  refine ⟨⟨[⟨fun _ _ => true, 0, 0⟩], n⟩, ?_, ?_⟩
  · simp [BinaryCircuit.size]
    omega
  · intro x
    have hlen : (List.ofFn x).length = n := by simp
    simp only [BinaryCircuit.eval, BinaryCircuit.wires, List.foldl_cons, List.foldl_nil]
    exact getD_append_true _ _ hlen.symm

theorem no_gate (n s : ℕ)
    (h : HasBinarySize n (fun _ : Fin n → Bool => true) s) : 1 ≤ s := by
  by_contra hs
  have hs0 : s = 0 := by omega
  rw [hs0] at h
  obtain ⟨C, hsize, hfun⟩ := h
  have hlen : C.gates.length = 0 := by
    simp only [BinaryCircuit.size] at hsize
    omega
  have hg : C.gates = [] := List.eq_nil_of_length_eq_zero hlen
  have h0 := hfun (fun _ : Fin n => false)
  simp only [BinaryCircuit.eval, BinaryCircuit.wires, hg, List.foldl_nil] at h0
  rw [getD_ofFn_false] at h0
  exact Bool.false_ne_true h0

end PEqualNP.Outside.L_meta_240

theorem PEqualNP.Outside.L_meta_240 :
    ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => true) s
      ↔ 1 ≤ s := by
  intro n s
  exact ⟨PEqualNP.Outside.L_meta_240.no_gate n s,
    PEqualNP.Outside.L_meta_240.one_gate n s⟩
