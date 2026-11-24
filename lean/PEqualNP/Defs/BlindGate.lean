import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card

/-!
# Blind and visible gates of a circuit on 2-light inputs

A semantic label on the gates of a root circuit (`PEqualNP.CircuitLowerBounds.Circuit`) on `n`
inputs. An input `x : Fin n → Bool` is 2-LIGHT when at most two of its bits are true. A gate is
BLIND when, on every 2-light input, its value equals the value of one of the wires it reads,
or its value is the same on all 2-light inputs (constant there). Otherwise it is VISIBLE. The
blind count of a circuit is its number of blind gates.

The notion was stated for circuits of AND and OR gates of fan-in two, `g = op(a, b)`: blind
when `g` equals `a` on every 2-light input, or equals `b` on every 2-light input, or takes one
value on all of them. For such a gate this file's definition is exactly that one.

Names:
* `IsTwoLight n x`: at most two bits of `x : Fin n → Bool` are true.
* `wireValue C n x w`: the value of wire `w` of `C` on the input `x` (`false` if there is no
  such wire), read off `Circuit.wires` at `List.ofFn x`.
* `gateInputs C j`: the list of the wires gate `j` reads (`[]` if there is no gate `j`).
* `IsBlind C n j`: gate `j` (wire `n + j`) exists and is blind.
* `IsVisible C n j`: gate `j` exists and is not blind.
* `blindCount C n`: the number of `j < C.size` with `IsBlind C n j`.

Caveats a statement must respect:
* Gate `j` is wire `n + j`: the number of inputs `n` is an argument and must be the same `n`
  as in `Circuit.Decides`.
* The notion is SEMANTIC, on 2-light inputs only, and depends on the operands as wires, not on
  the operands' functions on all inputs.
* Only AND and OR gates can be blind, and only through a read wire BELOW their own wire (an
  earlier input or gate): a NOT, MOD or MAJORITY gate is never blind, so it is visible whenever it
  exists (even a NOT of a constant), and a gate reading its own or a later wire is not blind
  through that read. A fan-in-one AND or OR (a copy) of an earlier wire is blind, and an AND or OR
  with no input (a constant) is blind. For AND/OR fan-in-two circuits reading earlier wires this
  is exactly the stated notion; any other use is a convention.
* "Constant" is over the 2-light inputs only; when `n = 0` the only input is light, so every
  existing AND or OR gate is blind and every other gate is visible.
* `j` at or past `C.size` is neither blind nor visible.
-/

namespace PEqualNP.BlindGate

open PEqualNP.CircuitLowerBounds

/-- At most two bits of `x` are true. -/
def IsTwoLight (n : ℕ) (x : Fin n → Bool) : Prop :=
  (Finset.univ.filter fun i => x i = true).card ≤ 2

instance (n : ℕ) (x : Fin n → Bool) : Decidable (IsTwoLight n x) := by
  unfold IsTwoLight; infer_instance

/-- The value of wire `w` of `C` on the input `x` (`false` if the wire does not exist). -/
def wireValue (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

/-- The wires gate `j` of `C` reads, in order (`[]` if there is no gate `j`). -/
def gateInputs (C : Circuit) (j : ℕ) : List ℕ :=
  ((C.gates[j]?).map Gate.inputs).getD []

/-- The operation is AND or OR. -/
def opIsAndOr : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

/-- Gate `j` of `C` exists and is an AND or an OR gate. -/
def gateIsAndOr (C : Circuit) (j : ℕ) : Bool :=
  ((C.gates[j]?).map fun g => opIsAndOr g.op).getD false

/-- Gate `j` of `C` on `n` inputs (wire `n + j`) exists, is an AND or an OR gate, and is blind:
on every 2-light input it equals one fixed wire it reads that lies BELOW its own wire (an earlier
input or gate), or it takes one value on all 2-light inputs. A gate reading its own or a later wire
is never blind through that read. -/
def IsBlind (C : Circuit) (n j : ℕ) : Prop :=
  j < C.gates.length ∧ gateIsAndOr C j = true ∧
    ((∃ a ∈ gateInputs C j, a < n + j ∧ ∀ x : Fin n → Bool, IsTwoLight n x →
        wireValue C n x (n + j) = wireValue C n x a) ∨
      (∀ x y : Fin n → Bool, IsTwoLight n x → IsTwoLight n y →
        wireValue C n x (n + j) = wireValue C n y (n + j)))

instance (C : Circuit) (n j : ℕ) : Decidable (IsBlind C n j) := by
  unfold IsBlind; infer_instance

/-- Gate `j` of `C` on `n` inputs exists and is not blind. -/
def IsVisible (C : Circuit) (n j : ℕ) : Prop :=
  j < C.gates.length ∧ ¬ IsBlind C n j

instance (C : Circuit) (n j : ℕ) : Decidable (IsVisible C n j) := by
  unfold IsVisible; infer_instance

/-- The number of blind gates of `C` on `n` inputs. -/
def blindCount (C : Circuit) (n : ℕ) : ℕ :=
  ((List.range C.gates.length).filter fun j => decide (IsBlind C n j)).length

end PEqualNP.BlindGate
