import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs.NestedCoverCircuit

/-!
# Edge ownership and the star profile of an AND/OR circuit on a graph

The setting. A circuit of the root model (`PEqualNP.Defs.CircuitLowerBounds`) on the inputs
`Fin n`: wire `i < n` is the input `x_i`, gate number `j` is wire `n + j`, and a gate reads the
wires named in its input list (a wire that does not exist yet reads `false`). The inputs are the
vertices of a graph `G` on `Fin n`; the circuit is meant to compute the edge function of `G`
(true exactly when both ends of some edge are true), `graphFun G ∅` of the nested cover module.

The object (a notion of the fleet, founders' point 0i). For an edge `uv` let `1_uv` be the input
true exactly at `u` and `v`. An AND gate `g` OWNS `uv` when `g` is true at `1_uv` and no AND gate
strictly inside the cone of `g` is true at `1_uv`. The circuit has a STAR PROFILE (with respect
to `G`) when, for every AND gate, the edges of `G` it owns share a common vertex.

* `pairInput u v`: the input `1_uv`, true exactly at `u` and `v` (at one vertex when `u = v`).
* `gateVal n C j x`: the value of gate number `j` (wire `n + j`) at the input `x`.
* `coneStep`, `cones n C`: the list, gate by gate, of the gates in the strict cone of each gate.
* `InCone n C i j`: gate `i` lies strictly inside the cone of gate `j`: `j` reads `i`, directly
  or through a chain of gates. Gate `j` itself is NOT in its own cone.
* `Owns n C j u v`: gate `j` is an AND gate of `C` that owns the pair `uv`.
* `HasStarProfile n G C`: for every AND gate, the edges of `G` it owns share a vertex.
* `EveryEdgeOwned n G C`: every edge of `G` is owned by some AND gate.
* `AndOrOnly C`: every gate is an AND or an OR gate.
* `edgeGraph n l`: the simple graph on `Fin n` with the edges listed in `l` as pairs of numbers
  (loops and out-of-range numbers are dropped), with decidable adjacency, for small rows.

Caveats a statement must respect.
* The cone is the STRICT cone: "no AND gate inside the cone of `g`" can only mean the gates
  below `g`, since `g` itself is true at `1_uv`. A gate is in the cone of `j` only through wires
  `j` really reads: a wire index at or past `n + j` (not yet existing) reads `false` in the
  root model and contributes nothing, so `InCone n C i j` implies `i < j`.
* `Owns` is a property of a pair of vertices, symmetric in `u` and `v`, and does not mention
  `G`: a gate may own a non-edge pair, or a single vertex (`u = v`). The star profile and
  `EveryEdgeOwned` only look at pairs with `G.Adj u v`.
* An AND gate owning no edge of `G` satisfies the star condition VACUOUSLY (stated as an
  explicit disjunct, so the convention holds also when `n = 0`).
* Nothing here assumes the circuit is monotone, of fan-in two, or computes the edge function of
  `G`: state those as hypotheses (`AndOrOnly C`, `FanInTwo C`, `circuitFun n C = graphFun G ∅`).
  With NOT gates the notion is still defined but is not the thinker's.
* Gate indices are plain numbers; a gate index at or past `C.gates.length` owns nothing.
* The gate operation is read through `gateAt` of the nested cover module (an OR gate with no
  input past the end of the list).
-/

namespace PEqualNP.EdgeOwnership

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

/-- The input `1_uv` on `Fin n`: true exactly at `u` and at `v`. -/
def pairInput {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun w => decide (w = u ∨ w = v)

/-- The value of gate number `j` of `C` (wire `n + j`) at the input `x` on `n` inputs. -/
def gateVal (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD (n + j) false

/-- One step of the cone computation: given the strict cones `cs` of the gates so far (gate
`cs.length` is the next one, wire `n + cs.length`), the strict cone of gate `g` is the union,
over the wires it reads that are earlier gates, of that gate and its own strict cone. -/
def coneStep (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List (List ℕ) :=
  cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])]

/-- The strict cones of all gates of `C` on `n` inputs, in gate order (as lists, repetitions
allowed; only membership matters). -/
def cones (n : ℕ) (C : Circuit) : List (List ℕ) :=
  C.gates.foldl (coneStep n) []

/-- Gate `i` lies strictly inside the cone of gate `j`: `j` reads the wire of `i`, directly or
through a chain of gates. -/
def InCone (n : ℕ) (C : Circuit) (i j : ℕ) : Prop :=
  i ∈ (cones n C).getD j []

instance (n : ℕ) (C : Circuit) (i j : ℕ) : Decidable (InCone n C i j) := by
  unfold InCone; infer_instance

/-- Gate `j` of `C` OWNS the pair `uv`: it is an AND gate, it is true at `1_uv`, and no AND gate
strictly inside its cone is true at `1_uv`. -/
def Owns (n : ℕ) (C : Circuit) (j : ℕ) (u v : Fin n) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true ∧
    ∀ i < j, InCone n C i j → (gateAt C i).op = GateOp.and →
      gateVal n C i (pairInput u v) = false

instance (n : ℕ) (C : Circuit) (j : ℕ) (u v : Fin n) : Decidable (Owns n C j u v) := by
  unfold Owns; infer_instance

/-- `C` has a STAR PROFILE with respect to `G`: for every AND gate, either it owns no edge of
`G`, or some vertex `c` lies on every edge of `G` it owns. -/
def HasStarProfile (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    (∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
      ∃ c : Fin n, ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = c ∨ v = c

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Decidable (HasStarProfile n G C) := by
  unfold HasStarProfile
  have : ∀ j : ℕ, Decidable ((∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
      ∃ c : Fin n, ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = c ∨ v = c) :=
    fun _ => inferInstance
  infer_instance

/-- Every edge of `G` is owned by some AND gate of `C`. -/
def EveryEdgeOwned (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ u v : Fin n, G.Adj u v → ∃ j < C.gates.length, Owns n C j u v

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Decidable (EveryEdgeOwned n G C) := by
  unfold EveryEdgeOwned; infer_instance

/-- Every gate of `C` is an AND or an OR gate. -/
def AndOrOnly (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or

instance (C : Circuit) : Decidable (AndOrOnly C) := by
  unfold AndOrOnly; infer_instance

/-- The simple graph on `Fin n` whose edges are the pairs of numbers listed in `l` (in either
order); a loop `(a, a)` is dropped, and a pair naming a number `≥ n` names no vertex. -/
def edgeGraph (n : ℕ) (l : List (ℕ × ℕ)) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ ((a.val, b.val) ∈ l ∨ (b.val, a.val) ∈ l)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (n : ℕ) (l : List (ℕ × ℕ)) : DecidableRel (edgeGraph n l).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ ((a.val, b.val) ∈ l ∨ (b.val, a.val) ∈ l)))

end PEqualNP.EdgeOwnership
