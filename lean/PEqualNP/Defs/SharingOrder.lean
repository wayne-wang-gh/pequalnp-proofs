import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs.LineDegree

/-!
# The sharing order of a family of outputs

A family `F : Fin m → (Fin n → Bool) → Bool` of `m` Boolean functions on `n` inputs, and a
domain `D : Set (Fin n → Bool)` of inputs on which circuits must be right. Circuits are root
circuits (`PEqualNP.CircuitLowerBounds.Circuit`) of AND and OR gates (`IsMonotoneCircuit`), each
gate reading at most two wires, with no NOT; every gate counts in the size.

* The JOINT least size of a subfamily `I : Finset (Fin m)` is the least number of gates of one
  such circuit with, for each `i ∈ I`, a chosen wire (an input wire or a gate wire) that agrees
  with `F i` on every input of `D`. It is `⊤` when no such circuit exists (for instance when some
  `F i` is not monotone on `D`).
* The single least size of output `i` is the joint least size of `{i}`.
* The SHARING ORDER is the least `k` such that some subfamily of `k` outputs has joint least size
  strictly below the sum of the single least sizes of its members; `⊤` if no subfamily saves.

Names:
* `IsMonoFanInTwo C`: every gate of `C` is AND or OR and reads at most two wires.
* `Circuit.wireOn C x j`: the value of wire `j` of `C` on the input `x : Fin n → Bool`.
* `JointComputes D F I C out`: wire `out i` of `C` agrees with `F i` on `D`, for each `i ∈ I`.
* `JointSizeAtMost D F I s`: some `IsMonoFanInTwo` circuit with at most `s` gates jointly
  computes `F` on `I` over `D`.
* `jointSize D F I : ℕ∞`: the joint least size.
* `singleSize D F i : ℕ∞`: `jointSize D F {i}`.
* `Saves D F I`: `jointSize D F I < ∑ i ∈ I, singleSize D F i`.
* `sharingOrder D F : ℕ∞`: the least card of a saving subfamily, `⊤` if none.
* Helpers for rows: `andOf S` (the AND of the inputs in `S`, `true` on `S = ∅`) and
  `weightBand n a b` (the inputs with between `a` and `b` true bits, both ends included).

Caveats a statement must respect:
* The field `Circuit.output` plays no part: the outputs are the wires `out i`. An output wire may
  be an input wire (size `0` for a projection) and may be shared by several outputs.
* A wire index that does not exist reads `false` (root convention), so the constant `false` costs
  no gate; the constant `true` costs one gate (an AND reading no wire).
* Fan-in two (and zero or one) is built in; a gate with fan-in one copies its wire.
* The domain matters: on a partial `D` a function can be cheaper, and a function that is not
  monotone can still have a monotone circuit right on `D`.
* Subfamilies of size `0` and `1` never save, so `sharingOrder` is `⊤` or at least `2`.
* The sum is in `ℕ∞`: if some single size is `⊤` then so is the joint size, and that subfamily
  does not save.
* Unused gates count; the least size never uses them.
* Degenerate families: two outputs that agree on `D`, or an output constant on `D`, can make the
  order `2` for a trivial reason. A statement about the sharing order of a family
  should carry the hypothesis "outputs pairwise different and not constant on `D`".
-/

namespace PEqualNP.CircuitLowerBounds

open Finset

/-- Every gate of `C` is an AND or an OR gate reading at most two wires. -/
def IsMonoFanInTwo (C : Circuit) : Prop :=
  IsMonotoneCircuit C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2

/-- The value of wire `j` of `C` on the input `x` (`false` if the wire does not exist). -/
def Circuit.wireOn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD j false

/-- For each `i ∈ I`, the wire `out i` of `C` agrees with `F i` on every input of `D`. -/
def JointComputes {n m : ℕ} (D : Set (Fin n → Bool)) (F : Fin m → (Fin n → Bool) → Bool)
    (I : Finset (Fin m)) (C : Circuit) (out : Fin m → ℕ) : Prop :=
  ∀ i ∈ I, ∀ x ∈ D, C.wireOn x (out i) = F i x

/-- Some AND/OR circuit of fan-in at most two with at most `s` gates computes every `F i`,
`i ∈ I`, on `D`, each on a wire of its own choice. -/
def JointSizeAtMost {n m : ℕ} (D : Set (Fin n → Bool)) (F : Fin m → (Fin n → Bool) → Bool)
    (I : Finset (Fin m)) (s : ℕ) : Prop :=
  ∃ C : Circuit, ∃ out : Fin m → ℕ, IsMonoFanInTwo C ∧ C.size ≤ s ∧ JointComputes D F I C out

/-- The joint least size of the subfamily `I` on `D` (`⊤` if no circuit exists). -/
noncomputable def jointSize {n m : ℕ} (D : Set (Fin n → Bool))
    (F : Fin m → (Fin n → Bool) → Bool) (I : Finset (Fin m)) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ k : ℕ, s = (k : ℕ∞) ∧ JointSizeAtMost D F I k}

/-- The single least size of output `i` on `D`. -/
noncomputable def singleSize {n m : ℕ} (D : Set (Fin n → Bool))
    (F : Fin m → (Fin n → Bool) → Bool) (i : Fin m) : ℕ∞ :=
  jointSize D F {i}

/-- The subfamily `I` saves: its joint least size is below the sum of its single least sizes. -/
def Saves {n m : ℕ} (D : Set (Fin n → Bool)) (F : Fin m → (Fin n → Bool) → Bool)
    (I : Finset (Fin m)) : Prop :=
  jointSize D F I < ∑ i ∈ I, singleSize D F i

/-- The sharing order: the least number of outputs of a saving subfamily, `⊤` if none saves. -/
noncomputable def sharingOrder {n m : ℕ} (D : Set (Fin n → Bool))
    (F : Fin m → (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {k : ℕ∞ | ∃ I : Finset (Fin m), (I.card : ℕ∞) = k ∧ Saves D F I}

/-- The AND of the inputs in `S` (`true` when `S` is empty). -/
def andOf {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∀ i ∈ S, x i = true)

/-- The inputs on `n` bits with at least `a` and at most `b` true bits. -/
def weightBand (n a b : ℕ) : Set (Fin n → Bool) :=
  {x | a ≤ (univ.filter fun i => x i = true).card ∧ (univ.filter fun i => x i = true).card ≤ b}

end PEqualNP.CircuitLowerBounds
