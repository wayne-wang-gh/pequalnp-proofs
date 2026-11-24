import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_241 : ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => false) s := by
  intro n s
  refine ⟨⟨[], n⟩, Nat.zero_le s, ?_⟩
  intro x
  simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires]
