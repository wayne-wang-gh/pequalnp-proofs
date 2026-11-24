import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.LineDegree
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-!
# Line set, specific gates and pencil gates of a circuit on a plane

A plane (projective or not) is given as data: `n` points `Fin n` and `m` lines, a family
`S : Fin m → Finset (Fin n)` of point sets. A circuit is a root circuit
(`PEqualNP.CircuitLowerBounds.Circuit`) on `n` inputs, input `i` being the point `i`; the notion
is meant for lists of AND and OR gates (`IsMonotoneCircuit`), but is defined for any circuit.

A gate is named by its WIRE index `w`, as in the netlists on file: wires `0 .. n - 1` are the
inputs (the points), and gate number `j` of the list is wire `n + j`.

* The LINE SET of wire `w` is the set of lines `l` such that wire `w` is true on the input whose
  true points are exactly the points of `l`.
* Wire `w` is SPECIFIC if its line set is a single line.
* Wire `w` is a PENCIL GATE if its line set has at least two lines and some point lies on all of
  them. In a projective plane two lines meet in exactly one point, so the point is then unique.

Names:
* `lineInput S l`: the input (a list of `n` bits) whose true points are the points of `S l`.
* `wireValue C x w`: the value of wire `w` of `C` on input `x` (`false` if there is no such wire).
* `lineSet S C w`: the line set of wire `w`.
* `IsSpecificGate S C w`: the line set of `w` is a single line.
* `IsPencilAt S C w p`: the line set has at least two lines, all through the point `p`.
* `IsPencilGate S C w`: `IsPencilAt S C w p` for some point `p`.
* `pencilGateCount S C`, `specificGateCount S C`: the numbers of GATES (wires `n` to
  `n + C.size - 1`, inputs not counted) that are pencil gates, resp. specific.
* `fanoLines`: the plane of order 2 as data, lines `{0, 1, 3} + w` mod 7, line `w` for `w : Fin 7`.

Caveats a statement must respect:
* The notion is SEMANTIC but sees only the `m` line inputs: two gates computing different
  functions can have the same line set, and the line set says nothing about other inputs.
* Wire indices are absolute (`ℕ`): an input wire `w < n` also has a line set (the lines through
  point `w`, so it is a pencil gate whenever at least two lines pass through it). The two counts
  skip input wires; a statement about "a gate of the list" should range over `n ≤ w < n + C.size`.
* A wire at or beyond `n + C.size` reads `false`, so its line set is empty.
* `S` is arbitrary data: nothing here assumes it is a projective plane. Uniqueness of the point
  of a pencil gate, and every other plane fact, must be assumed or proved by the statement.
-/

namespace PEqualNP.CircuitLowerBounds

/-- The input on `n` points whose true points are exactly the points of the line `S l`. -/
def lineInput {n m : ℕ} (S : Fin m → Finset (Fin n)) (l : Fin m) : List Bool :=
  List.ofFn fun i : Fin n => decide (i ∈ S l)

/-- The value of wire `w` of `C` on input `x` (`false` if `w` is not a wire of `C` on `x`). -/
def wireValue (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

/-- The LINE SET of wire `w`: the lines `l` on which `w` is true when exactly the points of `l`
are true. -/
def lineSet {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (w : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun l => wireValue C (lineInput S l) w = true

/-- Wire `w` is SPECIFIC: its line set is a single line. -/
def IsSpecificGate {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (w : ℕ) : Prop :=
  (lineSet S C w).card = 1

/-- Wire `w` is a pencil gate AT the point `p`: its line set has at least two lines, and every
line of it passes through `p`. -/
def IsPencilAt {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (w : ℕ) (p : Fin n) :
    Prop :=
  2 ≤ (lineSet S C w).card ∧ ∀ l ∈ lineSet S C w, p ∈ S l

/-- Wire `w` is a PENCIL GATE: its line set has at least two lines and some point lies on all
of them. -/
def IsPencilGate {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (w : ℕ) : Prop :=
  ∃ p : Fin n, IsPencilAt S C w p

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (w : ℕ) :
    Decidable (IsSpecificGate S C w) := by
  unfold IsSpecificGate; infer_instance

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (w : ℕ) (p : Fin n) :
    Decidable (IsPencilAt S C w p) := by
  unfold IsPencilAt; infer_instance

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (w : ℕ) :
    Decidable (IsPencilGate S C w) := by
  unfold IsPencilGate; infer_instance

/-- The number of gates of `C` (wires `n` to `n + C.size - 1`) that are pencil gates. -/
def pencilGateCount {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) : ℕ :=
  ((Finset.range C.size).filter fun j => IsPencilGate S C (n + j)).card

/-- The number of gates of `C` (wires `n` to `n + C.size - 1`) that are specific. -/
def specificGateCount {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) : ℕ :=
  ((Finset.range C.size).filter fun j => IsSpecificGate S C (n + j)).card

/-- The plane of order 2 (Fano plane) as data: points `Fin 7`, line `w` is `{0, 1, 3} + w`
mod 7. -/
def fanoLines (w : Fin 7) : Finset (Fin 7) :=
  Finset.univ.filter fun p : Fin 7 => (p.val + 7 - w.val) % 7 ∈ ({0, 1, 3} : Finset ℕ)

end PEqualNP.CircuitLowerBounds
