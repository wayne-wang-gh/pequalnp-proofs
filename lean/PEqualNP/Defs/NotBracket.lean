import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.LineDegree
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Lattice.Nat

/-!
# NOT brackets of a family of monotone outputs, and the bracket cost

A family of `m` monotone Boolean functions on `n` inputs, `f : Fin m → ((Fin n → Bool) → Bool)`
(for a Boolean sum, output `i` is the OR of the inputs in set `i`), has a NOT bracket `(G, h)`
when:

* `h : (Fin n → Bool) → Bool` is ONE monotone function of the `n` inputs, shared by all outputs;
* `G : Fin m → ((Fin (n + 1) → Bool) → Bool)` gives `m` functions of `(x, z)`, each monotone in
  all `n + 1` arguments, with the extra input `z` LAST (position `n`, written `Fin.snoc x z`);
* `G i (x, NOT h x) = f i x` for every output `i` and every `x`.

Plugging `NOT h` into the `z` input costs one NOT gate, so a bracket is a multi-output circuit
for `f` with exactly one NOT gate, cut open at that gate.

The bracket cost counts `G` and `h` together, as ONE list of gates on the root circuit model
(`PEqualNP.CircuitLowerBounds.Circuit`) with `m + 1` marked wires:

* the list reads `n + 1` input wires: wires `0` to `n - 1` carry `x`, wire `n` carries `z`;
* every gate is an AND or an OR (`IsMonotoneCircuit`) reading at most two wires;
* wire `oG i` carries `G i`, for each output `i`: any existing wire (input, `z` or gate);
* wire `oh` carries `h`: any existing wire that does NOT depend on `z` syntactically
  (`zReach`): an input of `x`, or a gate none of whose ancestors is wire `n`. So the trivial
  bracket `G i (x, z) = f i x`, `h = x 0` costs the plain monotone size of `f`;
* gates are shared freely between the outputs and `h`, and each gate is counted once.

Names:
* `withZ x z`: the point `(x, z)` on `n + 1` inputs, `z` last (`Fin.snoc x z`).
* `IsNotBracket n m f G h`: every `f i`, every `G i` and `h` are monotone, and
  `G i (withZ x (!h x)) = f i x` for all `i` and `x`.
* `wireValue C y o`: the value of wire `o` of `C` on input `y` (`false` if there is none).
* `zReach n C`: for each wire of `C` on `n + 1` inputs, whether it depends syntactically on wire
  `n` (the wire `n` itself does; a gate does when some wire it reads does).
* `IsBracketCircuit n C oG oh`: `C` is a NOT-free fan-in-two list on `n + 1` inputs, every `oG i`
  is an existing wire, and `oh` is an existing wire that does not depend on `z`.
* `ComputesBracket n C oG oh G h`: on every `(x, z)`, wire `oG i` carries `G i (x, z)` for every
  `i`, and wire `oh` carries `h x`.
* `HasBracketCost n m f s`: some bracket of `f` is computed together by such a list of at most
  `s` gates.
* `bracketCost n m f`: the least such `s` (`sInf`; it is `0` if no `s` exists, which happens
  only when some `f i` is not monotone).
* `notCount C`: the number of NOT gates of `C`.
* `HasOneNotCost n m f s`: some list of AND, OR, NOT gates of fan-in at most two, with EXACTLY
  one NOT gate (it may read an input wire) and at most `s` gates, has one existing wire per
  output `i` carrying `f i` on every input of length `n`.
* `OneNotSizeIdentity n m f`: the thinker's identity, as a CANDIDATE statement only (not proved,
  not a theorem of this file): for monotone `f`, `HasOneNotCost n m f (s + 1) ↔
  HasBracketCost n m f s` for every `s`.
* `booleanSum n m S`: the Boolean sum of the sets `S i ⊆ Fin n`: output `i` is the OR of the
  inputs in `S i` (the OR of an empty set is `false`).

Caveats a statement must respect:
* Monotonicity of every `f i` is part of `IsNotBracket`. Without it `G (x, NOT h x)` need not be
  monotone (for instance `G = z`, `h = x 0` gives `NOT x 0`).
* `h` is independent of `z` SYNTACTICALLY (no path from wire `n` to wire `oh`), which is what
  lets the NOT gate be inserted without a cycle. A wire whose value happens not to depend on `z`
  but which reads `z` does not qualify.
* The circuit is the root model: a wire index that does not exist yet reads `false`, an AND
  reading no wire is the constant `true`, an OR reading no wire the constant `false`. Every gate
  counts, constant gates and copies included; inputs are not counted. The `output` field of the
  `Circuit` is ignored here: the marked wires are `oG` and `oh`.
* Several outputs may share one wire (`oG` need not be injective); `oh` may equal some `oG i`.
* `HasOneNotCost` counts EXACTLY one NOT gate. With "at most one", a NOT-free circuit would
  count. Its degenerate cases (a NOT reading a wire that does not exist, or reading nothing) are
  not excluded; the identity is a candidate, and a statement assumes what it needs.
* Fan-in two is built in, for `G` and `h` alike.
* Inputs in the thinker's text are numbered from `1`; here they are numbered from `0`, so the
  sum `{123, 14, 24, 34}` is `booleanSum 4 4 ![{0,1,2}, {0,3}, {1,3}, {2,3}]`.
-/

namespace PEqualNP.NotBracket

open PEqualNP.CircuitLowerBounds

attribute [local instance] lineDegreeGateOpDecEq

/-- The point `(x, z)` on `n + 1` inputs: `x` first, the extra input `z` last (position `n`). -/
def withZ {n : ℕ} (x : Fin n → Bool) (z : Bool) : Fin (n + 1) → Bool :=
  Fin.snoc x z

/-- `(G, h)` is a NOT bracket of the family `f` of `m` monotone functions on `n` inputs: every
`f i`, every `G i` and `h` are monotone, `G i` reads `(x, z)` with `z` last, and
`G i (x, NOT h x) = f i x` for every `i` and `x`. One `h` serves all outputs. -/
def IsNotBracket (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool)
    (G : Fin m → (Fin (n + 1) → Bool) → Bool) (h : (Fin n → Bool) → Bool) : Prop :=
  (∀ i, Monotone (f i)) ∧ (∀ i, Monotone (G i)) ∧ Monotone h ∧
    ∀ (i : Fin m) (x : Fin n → Bool), G i (withZ x (!h x)) = f i x

/-- The value of wire `o` of `C` on input `y` (`false` if the wire does not exist). -/
def wireValue (C : Circuit) (y : List Bool) (o : ℕ) : Bool :=
  (C.wires y).getD o false

/-- For each wire of `C` on `n + 1` inputs, in the order of `Circuit.wires`: whether it depends
syntactically on the input wire `n` (the `z` wire). Input wires below `n` do not, wire `n` does,
and a gate does exactly when some wire it reads does (a wire that does not exist does not). -/
def zReach (n : ℕ) (C : Circuit) : List Bool :=
  C.gates.foldl (fun d g => d ++ [g.inputs.any fun i => d.getD i false])
    (List.replicate n false ++ [true])

/-- `C` is a list for a bracket on `n` inputs with `m` outputs: AND and OR gates of fan-in at
most two, on `n + 1` input wires (wire `n` is `z`); every output wire `oG i` exists; the wire
`oh` of `h` exists and does not depend on `z`. -/
def IsBracketCircuit (n : ℕ) {m : ℕ} (C : Circuit) (oG : Fin m → ℕ) (oh : ℕ) : Prop :=
  IsMonotoneCircuit C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    (∀ i, oG i < n + 1 + C.size) ∧ oh < n + 1 + C.size ∧ (zReach n C).getD oh true = false

/-- On every `(x, z)`, wire `oG i` of `C` carries `G i (x, z)` for every `i`, and wire `oh`
carries `h x`. The input list is `x` then `z`. -/
def ComputesBracket (n : ℕ) {m : ℕ} (C : Circuit) (oG : Fin m → ℕ) (oh : ℕ)
    (G : Fin m → (Fin (n + 1) → Bool) → Bool) (h : (Fin n → Bool) → Bool) : Prop :=
  ∀ (x : Fin n → Bool) (z : Bool),
    (∀ i, wireValue C (List.ofFn x ++ [z]) (oG i) = G i (withZ x z)) ∧
      wireValue C (List.ofFn x ++ [z]) oh = h x

/-- Bracket cost at most `s`: some NOT bracket `(G, h)` of `f` is computed together by one
NOT-free fan-in-two list of at most `s` gates, as in `IsBracketCircuit` and `ComputesBracket`. -/
def HasBracketCost (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (G : Fin m → (Fin (n + 1) → Bool) → Bool) (h : (Fin n → Bool) → Bool),
    IsNotBracket n m f G h ∧
      ∃ (C : Circuit) (oG : Fin m → ℕ) (oh : ℕ),
        IsBracketCircuit n C oG oh ∧ C.size ≤ s ∧ ComputesBracket n C oG oh G h

/-- The bracket cost `br f`: the least `s` with `HasBracketCost n m f s` (`0` if none). -/
noncomputable def bracketCost (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool) : ℕ :=
  sInf {s | HasBracketCost n m f s}

/-- The number of NOT gates of `C`. -/
def notCount (C : Circuit) : ℕ :=
  (C.gates.filter fun g => decide (g.op = GateOp.not)).length

/-- Some list of AND, OR and NOT gates of fan-in at most two, with exactly one NOT gate and at
most `s` gates, has for each output `i` an existing wire carrying `f i` on `n` inputs. -/
def HasOneNotCost (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (C : Circuit) (oF : Fin m → ℕ),
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) ∧
    notCount C = 1 ∧ C.size ≤ s ∧ (∀ i, oF i < n + C.size) ∧
      ∀ (i : Fin m) (x : Fin n → Bool), wireValue C (List.ofFn x) (oF i) = f i x

/-- The thinker's size identity, as a CANDIDATE statement only: for a family of monotone
outputs, the least list with exactly one NOT gate has one gate more than the bracket cost. -/
def OneNotSizeIdentity (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool) : Prop :=
  (∀ i, Monotone (f i)) → ∀ s : ℕ, HasOneNotCost n m f (s + 1) ↔ HasBracketCost n m f s

/-- The Boolean sum of the sets `S i`: output `i` is the OR of the inputs in `S i`. -/
def booleanSum (n m : ℕ) (S : Fin m → Finset (Fin n)) : Fin m → (Fin n → Bool) → Bool :=
  fun i x => decide (∃ j ∈ S i, x j = true)

end PEqualNP.NotBracket
