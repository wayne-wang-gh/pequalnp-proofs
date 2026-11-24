import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_237

-- Keep the original operation, passing it just the arguments it actually reads.
private def encode (g : Gate) : BinaryGate :=
  match g.inputs with
  | [] => ⟨fun _ _ => g.op.eval [], 0, 0⟩
  | [i] => ⟨fun a _ => g.op.eval [a], i, 0⟩
  | i :: j :: _ => ⟨fun a b => g.op.eval [a, b], i, j⟩

private theorem encode_value (g : Gate) (h : g.inputs.length ≤ 2) (w : List Bool) :
    (encode g).op (w.getD (encode g).left false) (w.getD (encode g).right false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩⟩ <;> first | rfl | simp at h

private theorem run (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) (w : List Bool) :
    (BinaryCircuit.mk (gs.map encode) 0).wires w = (Circuit.mk gs 0).wires w := by
  unfold BinaryCircuit.wires Circuit.wires
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [encode_value g (h g List.mem_cons_self)]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) _

end PEqualNP.Outside.L_meta_237

open PEqualNP.Outside.L_meta_237 in
theorem PEqualNP.Outside.L_meta_237 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.MetaComplexity.HasBinarySize n f s := by
  rintro n f s ⟨C, h, hs, hf⟩
  refine ⟨⟨C.gates.map encode, C.output⟩, ?_, ?_⟩
  · simpa only [BinaryCircuit.size, Circuit.size, List.length_map] using hs
  · intro x
    rw [← hf x]
    exact congrArg (fun w : List Bool => w.getD C.output false)
      (run C.gates (fun g hg => (h g hg).2) (List.ofFn x))
