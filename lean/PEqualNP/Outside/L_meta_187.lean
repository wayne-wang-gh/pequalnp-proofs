import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_187_aux

-- Bit i of each mask records that the restricted truth table i has cost zero, one, or two.
-- The gate inequalities and literal bounds below certify the masks directly.
def cost (v : BitVec 8) : Nat :=
  if (57897811465722876096115075801844696845150819816717157638686913610157857472513 : Nat).testBit v.toNat then 0
  else if (9116930854256694546005339522344648671249218315661829394411436755101843199016 : Nat).testBit v.toNat then 1
  else if (47759339376693896097267924959784927255589313973711399759709182518321748863382 : Nat).testBit v.toNat then 2
  else 3

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem cost_gates :
    ∀ a b : BitVec 8,
      cost (a &&& b) ≤ cost a + cost b ∧ cost (a ||| b) ≤ cost a + cost b := by
  decide +kernel

theorem cost_and (a b : BitVec 8) : cost (a &&& b) ≤ cost a + cost b :=
  (cost_gates a b).1

theorem cost_or (a b : BitVec 8) : cost (a ||| b) ≤ cost a + cost b :=
  (cost_gates a b).2

end PEqualNP.Outside.L_meta_187_aux

namespace PEqualNP.Outside.L_meta_187_aux
open PEqualNP.MetaComplexity

-- Bit order is the common value of the outside inputs, followed by the two middle inputs.
def posBits (j : Fin 4) : BitVec 8 :=
  if j = 1 then 204 else if j = 2 then 170 else 240

def inputAt (k : Fin 8) (j : Fin 4) : Bool := (posBits j).getLsbD k.val

def bits : DMFormula 4 → BitVec 8
  | .lit j b => if b then posBits j else ~~~(posBits j)
  | .and f g => bits f &&& bits g
  | .or f g => bits f ||| bits g

theorem bits_spec (f : DMFormula 4) (k : Fin 8) :
    (bits f).getLsbD k.val = f.eval (inputAt k) := by
  induction f with
  | lit j b => cases b <;> simp [bits, DMFormula.eval, inputAt, k.isLt]
  | and f g hf hg => simp only [bits, BitVec.getLsbD_and, DMFormula.eval, hf, hg]
  | or f g hf hg => simp only [bits, BitVec.getLsbD_or, DMFormula.eval, hf, hg]

theorem target_rows : ∀ k : Fin 8,
    ((inputAt k 0 && inputAt k 1) || (inputAt k 1 && inputAt k 2) ||
     (inputAt k 2 && inputAt k 3)) = (232 : BitVec 8).getLsbD k.val := by decide

theorem target_bits (f : DMFormula 4)
    (h : ∀ x : Fin 4 → Bool, f.eval x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3))) :
    bits f = 232 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (bits_spec f ⟨i, hi⟩).trans ((h (inputAt ⟨i, hi⟩)).trans (target_rows ⟨i, hi⟩))

noncomputable def occ (i : Fin 4) : DMFormula 4 → Nat :=
  DMFormula.rec (motive := fun _ => Nat) (fun j _ => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q)

theorem cost_bound (c : BitVec 8 → Nat)
    (ca : ∀ a b, c (a &&& b) ≤ c a + c b)
    (co : ∀ a b, c (a ||| b) ≤ c a + c b)
    (cl : ∀ (j : Fin 4) (b : Bool), c (bits (.lit j b)) ≤ occ 1 (.lit j b) + occ 2 (.lit j b))
    (f : DMFormula 4) : c (bits f) ≤ occ 1 f + occ 2 f := by
  induction f with
  | lit j b => exact cl j b
  | and f g hf hg =>
    change c (bits f &&& bits g) ≤ (occ 1 f + occ 1 g) + (occ 2 f + occ 2 g)
    have h := ca (bits f) (bits g)
    omega
  | or f g hf hg =>
    change c (bits f ||| bits g) ≤ (occ 1 f + occ 1 g) + (occ 2 f + occ 2 g)
    have h := co (bits f) (bits g)
    omega

end PEqualNP.Outside.L_meta_187_aux

open PEqualNP.Outside.L_meta_187_aux

theorem PEqualNP.Outside.L_meta_187 :
∀ φ : PEqualNP.MetaComplexity.DMFormula 4, (∀ x : Fin 4 → Bool, φ.eval x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3))) → 3 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 4) (_ : Bool) => if j = 1 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ + PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 4) (_ : Bool) => if j = 2 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ := by
  intro f h
  change 3 ≤ occ 1 f + occ 2 f
  have hl : ∀ (j : Fin 4) (b : Bool), cost (bits (.lit j b)) ≤ occ 1 (.lit j b) + occ 2 (.lit j b) := by decide +kernel
  have hb := cost_bound cost cost_and cost_or hl f
  rw [target_bits f h] at hb
  exact (show 3 ≤ cost 232 by decide +kernel).trans hb
