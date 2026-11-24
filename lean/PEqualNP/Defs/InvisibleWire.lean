import PEqualNP.Defs.BlindGate

/-!
# Invisible wires of a circuit

A semantic label on the wires of a root circuit (`PEqualNP.CircuitLowerBounds.Circuit`) on `n`
inputs. An input `x : Fin n → Bool` is LIGHT when at most one of its bits is true (weight 0 or
1). A wire is INVISIBLE when its value is `false` on every light input. The invisible count of a
circuit is its number of invisible gate wires.

Examples: the AND of two distinct inputs; any wire below `(x1 OR x3) AND (x2 OR x6)` on the
light inputs. Non-examples: any input wire (true at its own single input); any OR of a
nonempty set of inputs (true at a single input of the set).

Names:
* `IsLight n x`: at most one bit of `x : Fin n → Bool` is true.
* `IsInvisible C n w`: wire `w` of `C` reads `false` on every light input. Decidable.
* `invisibleCount C n`: the number of `j < C.gates.length` such that the gate wire `n + j` is
  invisible.
* `wireValue C n x w` is reused from `Defs/BlindGate.lean`.

Caveats a statement must respect:
* The wire index `w` counts the inputs first: wires `0 .. n - 1` are the inputs, gate `j` is
  wire `n + j`. The number of inputs `n` is an argument and must be the same `n` as in
  `Circuit.Decides` or `NotPremium.Computes`.
* A wire index that does not exist reads `false` (as `wireValue` does), so a MISSING wire is
  invisible. `invisibleCount` counts only existing gate wires, so it is not affected; a
  statement about `IsInvisible C n w` for an arbitrary `w` must say `w` exists if that matters.
* A constant `false` gate (for instance `OR []`) is invisible; a constant `true` gate is not.
* The notion is SEMANTIC and any gate operation is allowed, NOT, MOD and MAJORITY included: it
  looks only at the wire's values on the `n + 1` light inputs, not at how the wire is built.
* When `n = 0` the only input is the empty one, which is light.
* Counts (`shadowCount`, `invisibleCount`) include gates no output depends on, so "at least `k`
  such gates" can be met by padding a circuit: speak of least circuits, or count only gates an
  output depends on.
-/

namespace PEqualNP.InvisibleWire

open PEqualNP.CircuitLowerBounds PEqualNP.BlindGate

/-- At most one bit of `x` is true (weight 0 or 1). -/
def IsLight (n : ℕ) (x : Fin n → Bool) : Prop :=
  (Finset.univ.filter fun i => x i = true).card ≤ 1

instance (n : ℕ) (x : Fin n → Bool) : Decidable (IsLight n x) := by
  unfold IsLight; infer_instance

/-- Wire `w` of `C` on `n` inputs is invisible: it reads `false` on every light input. A wire
that does not exist reads `false`, so it is invisible. -/
def IsInvisible (C : Circuit) (n w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, IsLight n x → wireValue C n x w = false

instance (C : Circuit) (n w : ℕ) : Decidable (IsInvisible C n w) := by
  unfold IsInvisible; infer_instance

/-- The number of gates of `C` on `n` inputs whose wire (`n + j` for gate `j`) is invisible. -/
def invisibleCount (C : Circuit) (n : ℕ) : ℕ :=
  ((List.range C.gates.length).filter fun j => decide (IsInvisible C n (n + j))).length

end PEqualNP.InvisibleWire
