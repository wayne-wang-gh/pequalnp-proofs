import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Disjoint
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Biclique-block cost of a graph

A BLOCK of a simple graph `G` on `Fin n` is a pair `(A, B)` of disjoint nonempty vertex sets with
every vertex of `A` adjacent to every vertex of `B`. As a circuit it is
`(OR of the inputs of A) AND (OR of the inputs of B)`, with `|A| + |B| - 1` gates, and it is true
exactly on the inputs that switch on some `a ∈ A` and some `b ∈ B`. The BICLIQUE-BLOCK COST
`bc G` is the least value, over finite families of blocks whose pairs together cover every edge
of `G`, of the sum of the block costs plus the number of blocks minus one (the OR gates that join
the blocks). It is the size of one AND/OR circuit for the edge function of `G`.

* `Block n`: a pair of vertex sets `(A, B)`, the candidate blocks.
* `IsBlock G p`: `p.1` and `p.2` are disjoint and nonempty, and `G.Adj a b` for all
  `a ∈ p.1`, `b ∈ p.2`.
* `blockCost p`: `p.1.card + p.2.card - 1`.
* `BlockCovers p u v`: the pair `{u, v}` is split by `p`, one end in `p.1` and the other in `p.2`
  (either way round).
* `IsBlockCover G F`: every member of the finite family `F` is a block of `G`, and every edge of
  `G` is covered by some member of `F`.
* `familyCost F`: the sum of `blockCost` over `F`, plus `F.card - 1`.
* `HasBlockCost G c`: some block cover of `G` has `familyCost` at most `c`. This is the form to
  state rows in; it is decidable when `G.Adj` is.
* `bc G`: the least `c` with `HasBlockCost G c` (an `sInf`, for statements only).

Caveats a statement must respect.

* A family is a `Finset` of blocks, not a list: a repeated block only adds cost, so the least
  value is the same as over lists.
* The pair is ordered: `(A, B)` and `(B, A)` are two blocks with the same cost and the same
  covered edges.
* Subtraction is on `ℕ`. A block has `|A|, |B| ≥ 1`, so `blockCost` is never truncated. The
  family term `F.card - 1` is truncated only for the empty family, which covers only the graph
  with no edge: there `bc = 0`, not `-1`, so the formula `|E| + τ - 1` reads `0` at the empty
  graph as well.
* The decidability instance enumerates all families of pairs of vertex sets, so `decide` is only
  usable to CHECK a given cover (an upper bound); lower bounds need an argument.
* The block cost is an upper bound on the least circuit size only (a cover gives a circuit). It
  is NOT the least size where the graph has a 4-cycle: on small graphs with a 4-cycle a circuit
  below it often exists (computed by script, not checked). Do not read it as a predicted size.
-/

namespace PEqualNP.BicliqueBlockCost

/-- A candidate block on `Fin n`: a pair of vertex sets `(A, B)`. -/
abbrev Block (n : ℕ) : Type := Finset (Fin n) × Finset (Fin n)

/-- `p = (A, B)` is a block of `G`: `A`, `B` disjoint, nonempty, and completely joined. -/
def IsBlock {n : ℕ} (G : SimpleGraph (Fin n)) (p : Block n) : Prop :=
  Disjoint p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty ∧ ∀ a ∈ p.1, ∀ b ∈ p.2, G.Adj a b

/-- The gate count of a block: `|A| - 1` ORs, `|B| - 1` ORs and one AND. -/
def blockCost {n : ℕ} (p : Block n) : ℕ :=
  p.1.card + p.2.card - 1

/-- The block `p` covers the pair `{u, v}`: one end in `p.1`, the other in `p.2`. -/
def BlockCovers {n : ℕ} (p : Block n) (u v : Fin n) : Prop :=
  (u ∈ p.1 ∧ v ∈ p.2) ∨ (v ∈ p.1 ∧ u ∈ p.2)

/-- `F` is a family of blocks of `G` covering every edge of `G`. -/
def IsBlockCover {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Block n)) : Prop :=
  (∀ p ∈ F, IsBlock G p) ∧ ∀ u v : Fin n, G.Adj u v → ∃ p ∈ F, BlockCovers p u v

/-- The gate count of the OR of the blocks of `F`: the block costs plus `|F| - 1` ORs. -/
def familyCost {n : ℕ} (F : Finset (Block n)) : ℕ :=
  (∑ p ∈ F, blockCost p) + (F.card - 1)

/-- Some block cover of `G` costs at most `c`. -/
def HasBlockCost {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ) : Prop :=
  ∃ F : Finset (Block n), IsBlockCover G F ∧ familyCost F ≤ c

/-- The biclique-block cost: the least `c` with `HasBlockCost G c`. -/
noncomputable def bc {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {c : ℕ | HasBlockCost G c}

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Block n) :
    Decidable (IsBlock G p) := by
  unfold IsBlock; infer_instance

instance {n : ℕ} (p : Block n) (u v : Fin n) : Decidable (BlockCovers p u v) := by
  unfold BlockCovers; infer_instance

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (F : Finset (Block n)) :
    Decidable (IsBlockCover G F) := by
  unfold IsBlockCover; infer_instance

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : ℕ) :
    Decidable (HasBlockCost G c) := by
  unfold HasBlockCost; infer_instance

end PEqualNP.BicliqueBlockCost
