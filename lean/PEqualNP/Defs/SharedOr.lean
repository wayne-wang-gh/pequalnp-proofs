import PEqualNP.Defs.PencilGate
import PEqualNP.Defs.EdgeOwnership

/-!
# True users of a gate and shared OR gates of an AND/OR list on a plane

A new notion, defined here.

The setting. A plane (projective or not) is data, as in `PEqualNP.Defs.PencilGate`: `n` points
`Fin n` and `m` lines, a family `S : Fin m → Finset (Fin n)` of point sets. A list of gates is a
root circuit `C` (`PEqualNP.CircuitLowerBounds.Circuit`) on `n` inputs, input `i` being the point
`i`, with one OUTPUT WIRE per line given by a map `out : Fin m → ℕ` (the wire meant to compute the
AND of the points of `S l`). The field `C.output` plays no part. A gate is named by its WIRE index
`w`, as in the netlists on file: wires `0 .. n - 1` are the inputs, gate number `j` is wire `n + j`.

* The CONE of the output of line `l` is the set of wires `w` with `w = out l`, or `w` and `out l`
  both gate wires and gate `w - n` strictly inside the cone of gate `out l - n` in the sense of
  `PEqualNP.EdgeOwnership.InCone` (the gate reads it, directly or through a chain of gates). The
  cone CONTAINS the output wire itself (the thinker's `Conj(g)` contains the output, so `o_l` is a
  true user of itself).
* The TRUE USERS of wire `w`: the lines `l` such that `w` is in the cone of `out l` AND `w` is true
  on the light input `lineInput S l` (true exactly at the points of `S l`).
* A SHARED OR gate: a gate wire `w` (`n ≤ w < n + C.gates.length`) whose gate is an OR gate and
  whose true users are NOT CONCURRENT: no point lies on every line of them.

Names:
* `InOutCone n C w v`: wire `w` is in the cone of wire `v` (reflexive).
* `IsTrueUser S C out w l`, `trueUsers S C out w : Finset (Fin m)`.
* `IsConcurrent S U`: some point lies on every line of `U : Finset (Fin m)`.
* `IsOrWire n C w`: `w` is a gate wire whose gate is an OR gate.
* `IsSharedOr S C out w`: `IsOrWire n C w` and the true users of `w` are not concurrent.
* `HasSharedOr S C out`: some gate wire of `C` is a shared OR gate.
* `sharedOrCount S C out`: the number of gates of `C` that are shared OR gates.

Caveats a statement must respect:
* NO TRUE USERS IS NOT SHARED. An empty set of lines is concurrent whenever `n ≥ 1` (every point
  lies on all of its lines), and a single line is concurrent when it has a point; so with `n ≥ 1`
  a shared OR gate has at least two true users, and in a projective plane (two lines meet) at least
  three. This is the thinker's reading: "SH gate: an OR gate g with U(g) not concurrent (no point
  on every line of U(g))", and "in a projective plane two lines always meet, so an SH gate has at
  least three true users" (column-sharing.md, sections 0 and 2.1). A gate no output uses is a dead
  gate, not a shared one. Degenerate: with `n = 0` (no points) every OR gate is shared.
* Wire indices, not gate indices. `IsSharedOr` holds only for gate wires; an input wire is never an
  OR gate. Inside `HasSharedOr` and `sharedOrCount` the gates are `n + j`, `j < C.gates.length`.
* The cone of an input wire is that wire alone: if `out l` is an input wire (a projection) only
  that wire is in its cone. An input wire below a gate is not counted in the cone (`InCone` is on
  gates); this does not matter for OR gates, which are gate wires.
* `InCone` sees only wires a gate really reads: a wire index at or past the gate's own wire reads
  `false` in the root model and is not in its cone.
* The notion is SEMANTIC only on the `m` light inputs `lineInput S l`; a gate's values elsewhere
  play no part. It does not assume that `C` computes the line-ANDs, that it is monotone, of fan-in
  two, or that `S` is a projective plane: state those as hypotheses.
* `out` need not be injective, and an output wire past the end of the list reads `false` and has
  only itself in its cone (so it has no true users).
-/

namespace PEqualNP.SharedOr

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

/-- Wire `w` is in the (reflexive) cone of wire `v`: `w = v`, or both are gate wires and gate
`w - n` lies strictly inside the cone of gate `v - n`. -/
def InOutCone (n : ℕ) (C : Circuit) (w v : ℕ) : Prop :=
  w = v ∨ (n ≤ w ∧ n ≤ v ∧ InCone n C (w - n) (v - n))

instance (n : ℕ) (C : Circuit) (w v : ℕ) : Decidable (InOutCone n C w v) := by
  unfold InOutCone; infer_instance

/-- Line `l` is a TRUE USER of wire `w`: `w` is in the cone of the output wire `out l`, and `w` is
true on the input whose true points are exactly those of `S l`. -/
def IsTrueUser {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ)
    (l : Fin m) : Prop :=
  InOutCone n C w (out l) ∧ wireValue C (lineInput S l) w = true

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ)
    (l : Fin m) : Decidable (IsTrueUser S C out w l) := by
  unfold IsTrueUser; infer_instance

/-- The TRUE USERS of wire `w`. -/
def trueUsers {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ) :
    Finset (Fin m) :=
  Finset.univ.filter fun l => IsTrueUser S C out w l

/-- The lines of `U` are CONCURRENT: some point lies on every one of them (true for `U = ∅` when
there is a point). -/
def IsConcurrent {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin m)) : Prop :=
  ∃ p : Fin n, ∀ l ∈ U, p ∈ S l

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin m)) :
    Decidable (IsConcurrent S U) := by
  unfold IsConcurrent; infer_instance

/-- Wire `w` is a gate wire of `C` (on `n` inputs) whose gate is an OR gate. -/
def IsOrWire (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or

instance (n : ℕ) (C : Circuit) (w : ℕ) : Decidable (IsOrWire n C w) := by
  unfold IsOrWire; infer_instance

/-- Wire `w` is a SHARED OR gate: an OR gate whose true users have no common point. -/
def IsSharedOr {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ) :
    Prop :=
  IsOrWire n C w ∧ ¬ IsConcurrent S (trueUsers S C out w)

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) (w : ℕ) :
    Decidable (IsSharedOr S C out w) := by
  unfold IsSharedOr; infer_instance

/-- Some gate of `C` (wire `n + j`, `j < C.gates.length`) is a shared OR gate. -/
def HasSharedOr {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) : Prop :=
  ∃ j < C.gates.length, IsSharedOr S C out (n + j)

instance {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) :
    Decidable (HasSharedOr S C out) := by
  unfold HasSharedOr; infer_instance

/-- The number of gates of `C` (wires `n` to `n + C.gates.length - 1`) that are shared OR
gates. -/
def sharedOrCount {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (out : Fin m → ℕ) : ℕ :=
  ((Finset.range C.gates.length).filter fun j => IsSharedOr S C out (n + j)).card

end PEqualNP.SharedOr
