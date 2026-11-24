import PEqualNP.Defs.EdgeOwnership

/-!
# The pair shadow of a gate, and shadow-free AND/OR circuits on a graph

The setting. A circuit of the root model (`PEqualNP.Defs.CircuitLowerBounds`) on the inputs
`Fin n`: wire `i < n` is the input `x_i`, gate number `j` is wire `n + j`, and a gate reads the
wires named in its input list (a wire that does not exist yet reads `false`). The inputs are the
vertices of a graph `G` on `Fin n`; the circuit is meant to compute the edge function of `G`
(true exactly when both ends of some edge are true), `graphFun G ∅` of the nested cover module.

The object (a notion of the fleet, founders' point 0i). Let `1_u` be the input true exactly at
`u` and `1_uv` the input true exactly at `u` and `v`. The PAIR SHADOW of gate `j` is the set of
NON-EDGE pairs `{u, v}`, `u ≠ v`, such that gate `j` is true at `1_uv` and false at both `1_u`
and `1_v`. For a monotone gate these are exactly the two-element prime implicants of the gate
that are not edges of `G`. The circuit is SHADOW-FREE when every gate has an empty shadow.

* `unitInput u`: the input `1_u`, true exactly at `u`.
* `InShadow n G C j u v`: the pair `u, v` lies in the pair shadow of gate `j` (wire `n + j`).
* `ShadowFree n G C`: no gate of `C` has a pair in its shadow.
* `shadowGates n G C`: the gate indices, in order, whose shadow is not empty.
* `shadowCount n G C`: the number of those gates.

The pair input `1_uv` is `pairInput u v` and the gate value is `gateVal n C j x`, both of the
edge ownership module (`PEqualNP.Defs.EdgeOwnership`); the graph of a small row is written with
its `edgeGraph`.

Caveats a statement must respect.
* Gate index `j` is wire `n + j`: the number of inputs `n` is an argument and must be the `n`
  of the circuit's input list. Input wires carry no shadow (they are not gates here).
* A wire that does not exist reads `false`, so a gate index at or past `C.gates.length` is false
  at `1_uv` and has an empty shadow; `ShadowFree` quantifies over existing gates only, which is
  the same thing.
* `InShadow` is stated on ORDERED vertices `u, v` but is symmetric in them (a lemma of the
  scratch helper): the shadow of a gate, as a set of unordered pairs, is read off either order.
  It requires `u ≠ v` and `¬ G.Adj u v`.
* The definition reads only the inputs of weight one and two; it does not itself require `C`
  to compute the edge function of `G`, to be monotone, of fan-in two, or to use only AND and
  OR gates: state those as hypotheses (`circuitFun n C = graphFun G ∅`, `AndOrOnly C`, ...).
  For a gate with NOT gates below it the "prime implicant" reading is lost; the 2-slice reading
  stays the definition.
* Counts (`shadowCount`, `invisibleCount`) include gates no output depends on, so "at least `k`
  such gates" can be met by padding a circuit: speak of least circuits, or count only gates an
  output depends on.
-/

namespace PEqualNP.PairShadow

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

/-- The input `1_u` on `Fin n`: true exactly at `u`. -/
def unitInput {n : ℕ} (u : Fin n) : Fin n → Bool :=
  fun w => decide (w = u)

/-- The pair `u, v` lies in the PAIR SHADOW of gate `j` of `C` (wire `n + j`) with respect to
`G`: `u ≠ v`, `uv` is not an edge of `G`, the gate is true at `1_uv` and false at `1_u` and at
`1_v`. -/
def InShadow (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) (u v : Fin n) : Prop :=
  u ≠ v ∧ ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
    gateVal n C j (unitInput u) = false ∧ gateVal n C j (unitInput v) = false

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ)
    (u v : Fin n) : Decidable (InShadow n G C j u v) := by
  unfold InShadow; infer_instance

/-- `C` is SHADOW-FREE with respect to `G`: no gate of `C` has a pair in its shadow. -/
def ShadowFree (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, ∀ u v : Fin n, ¬ InShadow n G C j u v

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Decidable (ShadowFree n G C) := by
  unfold ShadowFree; infer_instance

/-- The indices, in order, of the gates of `C` whose pair shadow is not empty. -/
def shadowGates (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    List ℕ :=
  (List.range C.gates.length).filter fun j => decide (∃ u v : Fin n, InShadow n G C j u v)

/-- The number of gates of `C` whose pair shadow is not empty. -/
def shadowCount (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : ℕ :=
  (shadowGates n G C).length

end PEqualNP.PairShadow
