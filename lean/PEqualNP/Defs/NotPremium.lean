import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.WithBot

/-!
# The NOT premium of a family of Boolean functions

Built on the root circuits of `Defs/CircuitLowerBounds` (`Gate`, `Circuit`, `Circuit.eval`),
with the encoding the one-NOT rows use: a list of gates `gates`, one output wire `out w` per
member `w` of the family, every gate an AND, OR or NOT reading at most two wires, every gate
counted, and "at most one NOT gate" as a map `Fin 1 → Fin gates.length` hitting every NOT
position.

For a family `F = (F 0, .., F (m - 1))` of functions on `n` inputs:

* the PLAIN size is the least number of gates of a NOT-free list (AND and OR, at most two
  wires each) computing all of `F` at once;
* a NOT gate at position `q` of a list is ESSENTIAL if replacing that gate by the constant
  `false`, and also by the constant `true`, each changes the value of some output wire on some
  input (both replacements must change something, not just one of them);
* the ONE-NOT size is the least number of gates of a list computing `F` with exactly one NOT
  gate, that gate essential;
* the NOT PREMIUM is the one-NOT size minus the plain size, an integer, or `⊤` when either
  size does not exist.

Names.
* `Basis2 gates`: every gate is AND, OR or NOT and reads at most two wires.
* `MonoBasis2 gates`: every gate is AND or OR and reads at most two wires.
* `Computes n gates out F`: output wire `out w` computes `F w`, for every `w` and every input.
* `orFamily S`: the family of ORs of the sets `S w` (the line-ORs of the rows).
* `constGate b`: the gate with no inputs and constant value `b` (`AND []` is `true`,
  `OR []` is `false`, as on the root).
* `replaceByConst gates q b`: the list with position `q` replaced by `constGate b`.
* `ChangesSomeOutput n gates gates' out`: some output wire differs between the two lists on
  some input.
* `EssentialNot n gates out q`: the gate at `q` is a NOT gate and both constant replacements
  change some output.
* `AtMostOneNot gates`: the row encoding, a map from `Fin 1` covering every NOT position.
* `EssentialOneNot n gates out`: at most one NOT gate and an essential NOT gate exists, that is
  exactly one NOT gate and it is essential.
* `plainSize n F : ℕ∞` (the thinker's `J_0`) and `oneNotSize n F : ℕ∞` (`J_{=1}`), as `sInf`
  of the attained sizes (`⊤` when none).
* `notPremium n F : WithTop ℤ`, `oneNotSize - plainSize` when both are finite, else `⊤`.

Caveats for statements.
* The value `⊤` is real, not a junk value: the constant `false` family has no list with an
  essential NOT gate (an output after a single NOT is monotone in the NOT wire, so replacing
  by `false` cannot change a constant `false` output), and a non-monotone `F` has no plain
  list. The thinker's notion is for monotone `F`; state monotonicity where it is used.
* `⊤` also arises for monotone, non-constant families (on paper): on one
  input, `F = x0` has no list with one essential NOT gate. So "the premium is at least `c`" can
  hold for that trivial reason; a statement of that form must also assert that the one-NOT size
  is finite, or be worded as "every list with one essential NOT gate has at least .. gates".
* Wire indices that do not exist read `false`, and a gate may have zero or one input (a
  constant or a copy), as on the root and in the rows: such gates are allowed and counted.
* "Changes some output" compares the replaced list with the original list. Under `Computes`
  the original values are `F`, so this is the thinker's "changes some output of F".
* The replaced gate is the constant itself (a gate with no inputs), so the replaced list has
  the same length and every later wire keeps its index.
* Plain size uses `MonoBasis2` (no NOT gate at all). The one-NOT size counts the NOT gate.
* `notPremium` is in `WithTop ℤ`; the premium is negative exactly when one essential NOT gate
  saves gates.
-/

namespace PEqualNP.NotPremium

open PEqualNP.CircuitLowerBounds

/-- Every gate is an AND, OR or NOT gate reading at most two wires. -/
def Basis2 (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2

/-- Every gate is an AND or OR gate reading at most two wires (no NOT gate). -/
def MonoBasis2 (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

/-- The list `gates` with output wires `out` computes the family `F` on `n` inputs. -/
def Computes {m : ℕ} (n : ℕ) (gates : List Gate) (out : Fin m → ℕ)
    (F : Fin m → (Fin n → Bool) → Bool) : Prop :=
  ∀ (w : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = F w x

/-- The family of ORs of the sets `S w`, as in the line-OR rows. -/
def orFamily {n m : ℕ} (S : Fin m → Finset (Fin n)) : Fin m → (Fin n → Bool) → Bool :=
  fun w x => decide (∃ v ∈ S w, x v = true)

/-- The constant gate of value `b`: no inputs, AND (value `true`) or OR (value `false`). -/
def constGate (b : Bool) : Gate :=
  if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

/-- The list with the gate at position `q` replaced by the constant `b`. -/
def replaceByConst (gates : List Gate) (q : ℕ) (b : Bool) : List Gate :=
  gates.set q (constGate b)

/-- Some output wire takes a different value in `gates'` than in `gates` on some input. -/
def ChangesSomeOutput {m : ℕ} (n : ℕ) (gates gates' : List Gate) (out : Fin m → ℕ) : Prop :=
  ∃ (w : Fin m) (x : Fin n → Bool),
    Circuit.eval ⟨gates', out w⟩ (List.ofFn x) ≠ Circuit.eval ⟨gates, out w⟩ (List.ofFn x)

/-- The gate at position `q` is an ESSENTIAL NOT gate: it is a NOT gate, and replacing it by
the constant `false` changes some output, and replacing it by the constant `true` also changes
some output. -/
def EssentialNot {m : ℕ} (n : ℕ) (gates : List Gate) (out : Fin m → ℕ)
    (q : Fin gates.length) : Prop :=
  (gates.get q).op = GateOp.not ∧
    ChangesSomeOutput n gates (replaceByConst gates q.val false) out ∧
    ChangesSomeOutput n gates (replaceByConst gates q.val true) out

/-- At most one NOT gate, in the row encoding: a map from `Fin 1` covering every NOT
position. -/
def AtMostOneNot (gates : List Gate) : Prop :=
  ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
    (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i

/-- Exactly one NOT gate, and it is essential. -/
def EssentialOneNot {m : ℕ} (n : ℕ) (gates : List Gate) (out : Fin m → ℕ) : Prop :=
  AtMostOneNot gates ∧ ∃ q : Fin gates.length, EssentialNot n gates out q

/-- The plain size `J_0`: the least number of gates of a NOT-free list computing `F`
(`⊤` if there is none). -/
noncomputable def plainSize {m : ℕ} (n : ℕ) (F : Fin m → (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ (gates : List Gate) (out : Fin m → ℕ),
    MonoBasis2 gates ∧ Computes n gates out F ∧ (gates.length : ℕ∞) = s}

/-- The one-NOT size `J_{=1}`: the least number of gates of a list computing `F` with exactly
one NOT gate, that gate essential (`⊤` if there is none). -/
noncomputable def oneNotSize {m : ℕ} (n : ℕ) (F : Fin m → (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ (gates : List Gate) (out : Fin m → ℕ),
    Basis2 gates ∧ EssentialOneNot n gates out ∧ Computes n gates out F ∧
      (gates.length : ℕ∞) = s}

/-- The NOT premium `pi(F) = J_{=1}(F) - J_0(F)`, an integer when both sizes are finite,
`⊤` otherwise. -/
noncomputable def notPremium {m : ℕ} (n : ℕ) (F : Fin m → (Fin n → Bool) → Bool) :
    WithTop ℤ :=
  if oneNotSize n F = ⊤ ∨ plainSize n F = ⊤ then ⊤
  else (((oneNotSize n F).toNat : ℤ) - ((plainSize n F).toNat : ℤ) : ℤ)

end PEqualNP.NotPremium
