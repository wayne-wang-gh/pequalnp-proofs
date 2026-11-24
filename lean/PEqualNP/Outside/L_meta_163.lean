import Mathlib
import PEqualNP.Defs

-- The signature search is adapted from Vivek Rajkumar's submission in pull request 1413.
-- The lower bound below applies to any circuit that passes the sampled inputs.

namespace PEqualNP.Outside.L_meta_163_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev B := BitVec 90
abbrev Sig := B × B

def targetFun (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)

def pairs : List (ℕ × ℕ) :=
  [(3, 9), (3, 10), (3, 12), (3, 17), (3, 18), (3, 20), (3, 33),
   (3, 34), (3, 36), (5, 9), (5, 10), (5, 12), (5, 17), (5, 18),
   (5, 20), (5, 33), (5, 34), (5, 36), (6, 9), (6, 10), (6, 12),
   (6, 17), (6, 18), (6, 20), (6, 33), (6, 34), (6, 36), (24, 9),
   (24, 10), (24, 12), (24, 17), (24, 18), (24, 20), (24, 33), (24, 34),
   (24, 36), (40, 9), (40, 10), (40, 12), (40, 17), (40, 18), (40, 20),
   (40, 33), (40, 34), (40, 36), (48, 9), (48, 10), (48, 12), (48, 17),
   (48, 18), (48, 20), (48, 33), (48, 34), (48, 36), (11, 9), (13, 9),
   (25, 9), (41, 9), (11, 10), (14, 10), (26, 10), (42, 10), (13, 12),
   (14, 12), (28, 12), (44, 12), (19, 17), (21, 17), (25, 17), (49, 17),
   (19, 18), (22, 18), (26, 18), (50, 18), (21, 20), (22, 20), (28, 20),
   (52, 20), (35, 33), (37, 33), (41, 33), (49, 33), (35, 34), (38, 34),
   (42, 34), (50, 34), (37, 36), (38, 36), (44, 36), (52, 36)]

def maskFun (m : ℕ) : Fin 6 → Bool := fun i => m.testBit i.val

def pairA (r : Fin 90) : Fin 6 → Bool := maskFun (pairs.getD r.val (0, 0)).1
def pairB (r : Fin 90) : Fin 6 → Bool := maskFun (pairs.getD r.val (0, 0)).2

def mkBVLoop : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, p => 2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0

def mkBV (p : Fin 90 → Bool) : B :=
  BitVec.ofNat 90 (mkBVLoop 90 (fun i => if h : i < 90 then p ⟨i, h⟩ else false))

lemma testBit_mkBVLoop (n : ℕ) : ∀ (p : ℕ → Bool) (i : ℕ), i < n →
    (mkBVLoop n p).testBit i = p i := by
  induction n with
  | zero => intro p i hi; omega
  | succ n ih =>
    intro p i hi
    cases i with
    | zero =>
      simp only [mkBVLoop]
      cases p 0 <;> simp
    | succ i =>
      simp only [mkBVLoop]
      have hbit : (2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0).testBit (i + 1) =
          (mkBVLoop n (fun k => p (k + 1))).testBit i := by
        cases p 0 <;> simp [Nat.testBit_succ, Nat.mul_add_div]
      rw [hbit, ih (fun k => p (k + 1)) i (by omega)]

lemma getElem_mkBV (p : Fin 90 → Bool) (i : ℕ) (hi : i < 90) :
    (mkBV p)[i] = p ⟨i, hi⟩ := by
  unfold mkBV
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  simp only [decide_eq_true hi, Bool.true_and]
  rw [testBit_mkBVLoop 90 _ i hi]
  simp [hi]

lemma zero_bit (i : ℕ) (hi : i < 90) : (0 : B)[i] = false := by simp

def top : B := BitVec.allOnes 90
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)

def neg (a : Sig) : Sig := (~~~ a.1, ~~~ a.2)

def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)

def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~ a.2

def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a :: l => sep d a ||| unionSep d l

def before (a b : Sig) : Bool :=
  if a.1 == b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)

def dropped (del v : List Sig) : List Sig :=
  v.filter (fun x => !del.contains x)

def tryGate (k t : ℕ) (r : List Sig → Bool) (v rest : List Sig) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  g != zero && g != one && !v.contains g &&
    (let d := decide (0 < t)
     let base := sep d g ||| unionSep d rest
     keep.any (fun h => decide (rest.length + h.length + 1 ≤ k - t + 1) &&
       (base ||| unionSep d h == top) && r (g :: (h ++ rest))))

def search : ℕ → ℕ → List Sig → Bool
  | 0, _, v => v.contains target
  | k + 1, t, v =>
    v.contains target ||
    (decide (0 < t) &&
      v.any (fun a => tryGate k (t - 1) (search k (t - 1)) v (dropped [a] v) (neg a) [[], [a]])) ||
    (decide (t ≤ k) &&
      v.any (fun a => v.any (fun b =>
        before a b &&
        (let rest := dropped [a, b] v
         let keep := [[], [a], [b], [a, b]]
         tryGate k t (search k t) v rest (bin false a b) keep ||
         tryGate k t (search k t) v rest (bin true a b) keep))))

def wiresToSigs (wa wb : Fin 90 → List Bool) (len : ℕ) : List Sig :=
  (List.range len).map (fun idx =>
    (mkBV (fun r => (wa r).getD idx false),
     mkBV (fun r => (wb r).getD idx false)))

def initList : List Sig :=
  [(BitVec.ofNat 90 86761609589678634072014847, BitVec.ofNat 90 4534578900988745121829449),
   (BitVec.ofNat 90 227635860700446033081795071, BitVec.ofNat 90 72553262379791124930307218),
   (BitVec.ofNat 90 1171130576830714384782196224, BitVec.ofNat 90 1160852198004600404846987556),
   (BitVec.ofNat 90 330117397901904808582840320, BitVec.ofNat 90 73769208668911046151),
   (BitVec.ofNat 90 660375674867217346922020864, BitVec.ofNat 90 302157669901543114043448),
   (BitVec.ofNat 90 1237798997948165218747023360, BitVec.ofNat 90 1237637807846270062874034624)]

def evalGateSig (g : Gate) (W : List Sig) : Sig :=
  match g.op, g.inputs with
  | GateOp.and, [] => one
  | GateOp.and, [p] => W.getD p zero
  | GateOp.and, [p, q] => bin false (W.getD p zero) (W.getD q zero)
  | GateOp.or, [] => zero
  | GateOp.or, [p] => W.getD p zero
  | GateOp.or, [p, q] => bin true (W.getD p zero) (W.getD q zero)
  | GateOp.not, [] => one
  | GateOp.not, p :: _ => neg (W.getD p zero)
  | _, _ => zero

def evalGates (gs : List Gate) (W : List Sig) : List Sig :=
  gs.foldl (fun W g => W ++ [evalGateSig g W]) W

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_cons (g : Gate) (rest : List Gate) (W : List Sig) :
    evalGates (g :: rest) W = evalGates rest (W ++ [evalGateSig g W]) := rfl

lemma evalWires_cons (g : Gate) (rest : List Gate) (w : List Bool) :
    evalWires (g :: rest) w =
      evalWires rest (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma initList_eq :
    wiresToSigs (fun r => List.ofFn (pairA r)) (fun r => List.ofFn (pairB r)) 6 = initList := by
  decide

lemma pairA_true : ∀ r : Fin 90, targetFun (pairA r) = true := by decide
lemma pairB_false : ∀ r : Fin 90, targetFun (pairB r) = false := by decide
lemma initList_nodup : initList.Nodup := by decide
lemma initList_len : initList.length = 6 := by decide
lemma target_ne_zero : target ≠ zero := by decide
lemma target_ne_one : target ≠ one := by decide

lemma all_init_needed_bool :
    initList.all (fun s => unionSep true (initList.erase s) != top) = true := by decide

lemma all_init_needed : ∀ s ∈ initList, unionSep true (initList.erase s) ≠ top := by
  intro s hs
  have h := List.all_eq_true.1 all_init_needed_bool s hs
  exact bne_iff_ne.1 h

def cellNot (k t : ℕ) (v : List Sig) (a : Sig) : Bool :=
  tryGate k (t - 1) (search k (t - 1)) v (dropped [a] v) (neg a) [[], [a]]

def cell (k t : ℕ) (v : List Sig) (a b : Sig) : Bool :=
  before a b &&
    (let rest := dropped [a, b] v
     let keep := [[], [a], [b], [a, b]]
     tryGate k t (search k t) v rest (bin false a b) keep ||
     tryGate k t (search k t) v rest (bin true a b) keep)

lemma search_succ (k t : ℕ) (v : List Sig) :
    search (k + 1) t v = (v.contains target ||
      (decide (0 < t) && v.any (fun a => cellNot k t v a)) ||
      (decide (t ≤ k) && v.any (fun a => v.any (fun b => cell k t v a b)))) := rfl

lemma any_init_false {p : Sig → Bool} (h : ∀ i : Fin 6, p (initList.getD i zero) = false) :
    initList.any p = false := by
  rw [List.any_eq_false]
  intro a ha hpa
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hin : i < 6 := by simpa [initList_len] using hi
  have h' := h ⟨i, hin⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h'
  rw [h'] at hpa
  exact Bool.false_ne_true hpa

lemma target_not_init : initList.contains target = false := by decide

lemma search_succ_false (k t : ℕ)
    (hnot : t = 0 ∨ ∀ i : Fin 6, cellNot k t initList (initList.getD i zero) = false)
    (hbin : ∀ i j : Fin 6, cell k t initList (initList.getD i zero) (initList.getD j zero) = false) :
    search (k + 1) t initList = false := by
  rw [search_succ]
  have h1 : (decide (0 < t) && initList.any (fun a => cellNot k t initList a)) = false := by
    rcases hnot with rfl | hn
    · simp
    · rw [any_init_false hn, Bool.and_false]
  have h2 : initList.any (fun a => initList.any (fun b => cell k t initList a b)) = false :=
    any_init_false (fun i => any_init_false (fun j => hbin i j))
  rw [target_not_init, h1, h2]
  simp

set_option maxRecDepth 20000 in
lemma search_5_0 : search 5 0 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_6_0 : search 6 0 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_6_1 : search 6 1 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_7_0 : search 7 0 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_7_1 : search 7 1 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_7_2 : search 7 2 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_0_0 :
    cell 7 0 initList (initList.getD 0 zero) (initList.getD 0 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_0_1 :
    cell 7 0 initList (initList.getD 0 zero) (initList.getD 1 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_0_2 :
    cell 7 0 initList (initList.getD 0 zero) (initList.getD 2 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_0_3 :
    cell 7 0 initList (initList.getD 0 zero) (initList.getD 3 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_0_4 :
    cell 7 0 initList (initList.getD 0 zero) (initList.getD 4 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_0_5 :
    cell 7 0 initList (initList.getD 0 zero) (initList.getD 5 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_1_0 :
    cell 7 0 initList (initList.getD 1 zero) (initList.getD 0 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_1_1 :
    cell 7 0 initList (initList.getD 1 zero) (initList.getD 1 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_1_2 :
    cell 7 0 initList (initList.getD 1 zero) (initList.getD 2 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_1_3 :
    cell 7 0 initList (initList.getD 1 zero) (initList.getD 3 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_1_4 :
    cell 7 0 initList (initList.getD 1 zero) (initList.getD 4 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_1_5 :
    cell 7 0 initList (initList.getD 1 zero) (initList.getD 5 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_2_0 :
    cell 7 0 initList (initList.getD 2 zero) (initList.getD 0 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_2_1 :
    cell 7 0 initList (initList.getD 2 zero) (initList.getD 1 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_2_2 :
    cell 7 0 initList (initList.getD 2 zero) (initList.getD 2 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_2_3 :
    cell 7 0 initList (initList.getD 2 zero) (initList.getD 3 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_2_4 :
    cell 7 0 initList (initList.getD 2 zero) (initList.getD 4 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_2_5 :
    cell 7 0 initList (initList.getD 2 zero) (initList.getD 5 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_3_0 :
    cell 7 0 initList (initList.getD 3 zero) (initList.getD 0 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_3_1 :
    cell 7 0 initList (initList.getD 3 zero) (initList.getD 1 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_3_2 :
    cell 7 0 initList (initList.getD 3 zero) (initList.getD 2 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_3_3 :
    cell 7 0 initList (initList.getD 3 zero) (initList.getD 3 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_3_4 :
    cell 7 0 initList (initList.getD 3 zero) (initList.getD 4 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_3_5 :
    cell 7 0 initList (initList.getD 3 zero) (initList.getD 5 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_4_0 :
    cell 7 0 initList (initList.getD 4 zero) (initList.getD 0 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_4_1 :
    cell 7 0 initList (initList.getD 4 zero) (initList.getD 1 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_4_2 :
    cell 7 0 initList (initList.getD 4 zero) (initList.getD 2 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_4_3 :
    cell 7 0 initList (initList.getD 4 zero) (initList.getD 3 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_4_4 :
    cell 7 0 initList (initList.getD 4 zero) (initList.getD 4 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_4_5 :
    cell 7 0 initList (initList.getD 4 zero) (initList.getD 5 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_5_0 :
    cell 7 0 initList (initList.getD 5 zero) (initList.getD 0 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_5_1 :
    cell 7 0 initList (initList.getD 5 zero) (initList.getD 1 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_5_2 :
    cell 7 0 initList (initList.getD 5 zero) (initList.getD 2 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_5_3 :
    cell 7 0 initList (initList.getD 5 zero) (initList.getD 3 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_5_4 :
    cell 7 0 initList (initList.getD 5 zero) (initList.getD 4 zero) = false := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma cell_8_0_5_5 :
    cell 7 0 initList (initList.getD 5 zero) (initList.getD 5 zero) = false := by
  decide +kernel

lemma search_8_0 : search 8 0 initList = false :=
  search_succ_false 7 0 (Or.inl rfl) (fun i j => by
    fin_cases i <;> fin_cases j
    · exact cell_8_0_0_0
    · exact cell_8_0_0_1
    · exact cell_8_0_0_2
    · exact cell_8_0_0_3
    · exact cell_8_0_0_4
    · exact cell_8_0_0_5
    · exact cell_8_0_1_0
    · exact cell_8_0_1_1
    · exact cell_8_0_1_2
    · exact cell_8_0_1_3
    · exact cell_8_0_1_4
    · exact cell_8_0_1_5
    · exact cell_8_0_2_0
    · exact cell_8_0_2_1
    · exact cell_8_0_2_2
    · exact cell_8_0_2_3
    · exact cell_8_0_2_4
    · exact cell_8_0_2_5
    · exact cell_8_0_3_0
    · exact cell_8_0_3_1
    · exact cell_8_0_3_2
    · exact cell_8_0_3_3
    · exact cell_8_0_3_4
    · exact cell_8_0_3_5
    · exact cell_8_0_4_0
    · exact cell_8_0_4_1
    · exact cell_8_0_4_2
    · exact cell_8_0_4_3
    · exact cell_8_0_4_4
    · exact cell_8_0_4_5
    · exact cell_8_0_5_0
    · exact cell_8_0_5_1
    · exact cell_8_0_5_2
    · exact cell_8_0_5_3
    · exact cell_8_0_5_4
    · exact cell_8_0_5_5
    )

set_option maxRecDepth 20000 in
lemma search_8_1 : search 8 1 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_8_2 : search 8 2 initList = false := by decide +kernel

set_option maxRecDepth 20000 in
lemma search_8_3 : search 8 3 initList = false := by decide +kernel

lemma bin_comm (isOr : Bool) (a b : Sig) : bin isOr a b = bin isOr b a := by
  cases isOr <;> simp only [bin, BitVec.or_comm, BitVec.and_comm]

lemma bin_self (isOr : Bool) (a : Sig) : bin isOr a a = a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, Bool.false_eq_true, ↓reduceIte, BitVec.and_self]
  · simp only [bin, ↓reduceIte, BitVec.or_self]

lemma bin_zero_left (isOr : Bool) (a : Sig) : bin isOr zero a = if isOr then a else zero := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, zero, Bool.false_eq_true, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp
  · simp only [bin, zero, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp

lemma bin_zero_right (isOr : Bool) (a : Sig) : bin isOr a zero = if isOr then a else zero := by
  rw [bin_comm, bin_zero_left]

lemma bin_one_left (isOr : Bool) (a : Sig) : bin isOr one a = if isOr then one else a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, one, top, Bool.false_eq_true, ↓reduceIte, BitVec.allOnes_and]
  · simp only [bin, one, top, ↓reduceIte, BitVec.allOnes_or]

lemma bin_one_right (isOr : Bool) (a : Sig) : bin isOr a one = if isOr then one else a := by
  rw [bin_comm, bin_one_left]

lemma neg_zero : neg zero = one := by decide
lemma neg_one : neg one = zero := by decide

lemma before_trichotomy {a b : Sig} (hne : a ≠ b) : before a b = true ∨ before b a = true := by
  unfold before
  by_cases h1 : a.1 = b.1
  · have h2 : a.2 ≠ b.2 := fun h => hne (Prod.ext h1 h)
    have h2n : a.2.toNat ≠ b.2.toNat := fun h => h2 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = true := by rw [beq_iff_eq]; exact h1
    have hb2 : (b.1 == a.1) = true := by rw [beq_iff_eq]; exact h1.symm
    rw [hb1, hb2]
    simp only [↓reduceIte, decide_eq_true_eq]
    omega
  · have h1n : a.1.toNat ≠ b.1.toNat := fun h => h1 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = false := beq_false_of_ne h1
    have hb2 : (b.1 == a.1) = false := beq_false_of_ne (Ne.symm h1)
    rw [hb1, hb2]
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    omega

lemma unionSep_perm {d : Bool} {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    unionSep d v₁ = unionSep d v₂ := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp only [unionSep, ih]
  | swap a b l =>
    simp only [unionSep]
    rw [← BitVec.or_assoc, ← BitVec.or_assoc, BitVec.or_comm (sep d a) (sep d b)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma unionSep_append (d : Bool) (l₁ l₂ : List Sig) :
    unionSep d (l₁ ++ l₂) = unionSep d l₁ ||| unionSep d l₂ := by
  induction l₁ with
  | nil => simp [unionSep]
  | cons a t ih => simp only [List.cons_append, unionSep, ih, BitVec.or_assoc]

lemma unionSep_bit_iff (d : Bool) (v : List Sig) (i : ℕ) (hi : i < 90) :
    (unionSep d v)[i] = true ↔ ∃ s ∈ v, (sep d s)[i] = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a t ih =>
    simp only [unionSep, BitVec.getElem_or, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨s, hs, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨s, Or.inr hs, h⟩
    · rintro ⟨s, rfl | hs, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, hs, h⟩

lemma bv_eq_top_of_bits {x : B} (h : ∀ i (hi : i < 90), x[i] = true) : x = top := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [top, BitVec.getElem_allOnes]
  exact h i hi

lemma top_bit (i : ℕ) (hi : i < 90) : top[i] = true := by
  rw [top, BitVec.getElem_allOnes]

lemma sep_mono_true (d : Bool) (a : Sig) (i : ℕ) (hi : i < 90) :
    (sep d a)[i] = true → (sep true a)[i] = true := by
  cases d
  · simp only [sep, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not,
      BitVec.getElem_xor, Bool.and_eq_true, Bool.not_eq_true']
    intro h
    simp [h.1, h.2]
  · exact id

lemma sep_neg_true (a : Sig) (i : ℕ) (hi : i < 90) :
    (sep true (neg a))[i] = (sep true a)[i] := by
  simp only [sep, neg, ↓reduceIte, BitVec.getElem_xor, BitVec.getElem_not]
  cases a.1[i] <;> cases a.2[i] <;> rfl

lemma sep_bin_bit (d isOr : Bool) (a b : Sig) (i : ℕ) (hi : i < 90) :
    (sep d (bin isOr a b))[i] = true → (sep d a)[i] = true ∨ (sep d b)[i] = true := by
  cases d <;> cases isOr <;>
    simp only [sep, bin, ↓reduceIte, Bool.false_eq_true, BitVec.getElem_and,
      BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_not] <;>
    cases a.1[i] <;> cases a.2[i] <;> cases b.1[i] <;> cases b.2[i] <;> decide

lemma unionSep_target_eq_top : unionSep false [target] = top := by decide

lemma dropped_perm {del v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    (dropped del v₁).Perm (dropped del v₂) :=
  hp.filter _

lemma contains_perm {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) (x : Sig) :
    v₁.contains x = v₂.contains x := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem]
  exact hp.mem_iff

lemma list_any_eq_of_eq {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = g a) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

lemma search_perm : ∀ k t {v₁ v₂ : List Sig}, v₁.Perm v₂ → search k t v₁ = search k t v₂ := by
  intro k
  induction k with
  | zero =>
    intro t v₁ v₂ hp
    exact contains_perm hp target
  | succ k ih =>
    intro t v₁ v₂ hp
    have htry : ∀ (t' : ℕ) (rest₁ rest₂ : List Sig) (g : Sig) (keep : List (List Sig)),
        rest₁.Perm rest₂ →
        tryGate k t' (search k t') v₁ rest₁ g keep =
          tryGate k t' (search k t') v₂ rest₂ g keep := by
      intro t' rest₁ rest₂ g keep hrest
      have hlen : rest₁.length = rest₂.length := hrest.length_eq
      have hcont : v₁.contains g = v₂.contains g := contains_perm hp g
      have husep : unionSep (decide (0 < t')) rest₁ = unionSep (decide (0 < t')) rest₂ :=
        unionSep_perm hrest
      simp only [tryGate, hcont, hlen, husep]
      congr 1
      refine list_any_eq_of_eq keep _ _ (fun h _ => ?_)
      have hp' : (g :: (h ++ rest₁)).Perm (g :: (h ++ rest₂)) :=
        List.Perm.cons g (List.Perm.append_left h hrest)
      rw [ih t' hp']
    have hcontT : v₁.contains target = v₂.contains target := contains_perm hp target
    have hunary : v₁.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₁ (dropped [a] v₁) (neg a) [[], [a]]) =
        v₂.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₂ (dropped [a] v₂) (neg a) [[], [a]]) := by
      apply Bool.eq_iff_iff.2
      rw [List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.1 ha, ?_⟩
        rw [← htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.2 ha, ?_⟩
        rw [htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
    have hbinary :
        v₁.any (fun a => v₁.any (fun b => before a b &&
          (let rest := dropped [a, b] v₁
           let keep := [[], [a], [b], [a, b]]
           tryGate k t (search k t) v₁ rest (bin false a b) keep ||
           tryGate k t (search k t) v₁ rest (bin true a b) keep))) =
        v₂.any (fun a => v₂.any (fun b => before a b &&
          (let rest := dropped [a, b] v₂
           let keep := [[], [a], [b], [a, b]]
           tryGate k t (search k t) v₂ rest (bin false a b) keep ||
           tryGate k t (search k t) v₂ rest (bin true a b) keep))) := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.1 ha, b, hp.mem_iff.1 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.2 ha, b, hp.mem_iff.2 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
    simp only [search, hcontT, hunary, hbinary]

lemma getD_mem_of_ne {W : List Sig} {p : ℕ} (hne : W.getD p zero ≠ zero) :
    W.getD p zero ∈ W := by
  by_cases hp : p < W.length
  · rw [List.getD_eq_getElem _ _ hp]
    exact List.getElem_mem hp
  · rw [List.getD_eq_default _ _ (by omega)] at hne
    exact absurd rfl hne

lemma perm_of_nodup_same_mem {l₁ l₂ : List Sig} (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ :=
  (List.perm_ext_iff_of_nodup h1 h2).2 hmem

lemma mem_dropped_iff {del v : List Sig} {x : Sig} :
    x ∈ dropped del v ↔ x ∈ v ∧ x ∉ del := by
  simp only [dropped, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, fun hm => ?_⟩
    have hc : del.contains x = true := List.contains_iff_mem.2 hm
    rw [hc] at hnot
    cases hnot
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    cases hc : del.contains x
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot

lemma tryGate_eq_true {k t : ℕ} {r : List Sig → Bool} {v rest : List Sig} {g : Sig}
    {keep : List (List Sig)} (h0 : g ≠ zero) (h1 : g ≠ one) (hnot : g ∉ v)
    (h : List Sig) (hh : h ∈ keep)
    (hlen : rest.length + h.length + 1 ≤ k - t + 1)
    (hsep : (sep (decide (0 < t)) g ||| unionSep (decide (0 < t)) rest) |||
      unionSep (decide (0 < t)) h = top)
    (hr : r (g :: (h ++ rest)) = true) :
    tryGate k t r v rest g keep = true := by
  unfold tryGate
  have hb0 : (g != zero) = true := bne_iff_ne.2 h0
  have hb1 : (g != one) = true := bne_iff_ne.2 h1
  have hbn : (!v.contains g) = true := by
    cases hc : v.contains g
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot
  rw [hb0, hb1, hbn]
  simp only [Bool.true_and, List.any_eq_true]
  refine ⟨h, hh, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨hlen, hsep⟩, hr⟩

lemma extract_binary_step {k t : ℕ} {isOr : Bool} {W V' U : List Sig} {sg a0 b0 : Sig}
    (ht : t ≤ k) (hVnd : V'.Nodup) (hVlen : V'.length ≤ k - t + 1)
    (hVsep : unionSep (decide (0 < t)) V' = top) (hVsearch : search k t V' = true)
    (hsgW : sg ∉ W) (hsg0 : sg ≠ zero) (hsg1 : sg ≠ one)
    (hUnd : U.Nodup) (hsgU : sg ∉ U) (hPermV' : V'.Perm (sg :: U))
    (hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one) (hUlen : U.length + 1 = V'.length)
    (ha0W : a0 ∈ W) (hb0W : b0 ∈ W) (ha0_ne0 : a0 ≠ zero) (ha0_ne1 : a0 ≠ one)
    (hb0_ne0 : b0 ≠ zero) (hb0_ne1 : b0 ≠ one) (hab_ne : a0 ≠ b0)
    (hsgeq : sg = bin isOr a0 b0) :
    ∃ V : List Sig,
      V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
      V.length ≤ (k + 1) - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
      search (k + 1) t V = true := by
  obtain ⟨a, b, hab_ord, haW, hbW, ha0, ha1, hb0, hb1, hab, hbin⟩ :
      ∃ a b : Sig, before a b = true ∧ a ∈ W ∧ b ∈ W ∧ a ≠ zero ∧ a ≠ one ∧
        b ≠ zero ∧ b ≠ one ∧ a ≠ b ∧ sg = bin isOr a b := by
    rcases before_trichotomy hab_ne with h | h
    · exact ⟨a0, b0, h, ha0W, hb0W, ha0_ne0, ha0_ne1, hb0_ne0, hb0_ne1, hab_ne, hsgeq⟩
    · exact ⟨b0, a0, h, hb0W, ha0W, hb0_ne0, hb0_ne1, ha0_ne0, ha0_ne1, hab_ne.symm,
        by rw [hsgeq, bin_comm]⟩
  let addA : List Sig := if a ∈ U then [] else [a]
  let addB : List Sig := if b ∈ U then [] else [b]
  let V : List Sig := addA ++ addB ++ U
  have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x = b ∨ x ∈ U := by
    intro x
    simp only [V, addA, addB, List.mem_append]
    constructor
    · intro hx
      rcases hx with (hx | hx) | hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inl hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · rintro (rfl | rfl | hx)
      · by_cases haU : x ∈ U
        · exact Or.inr haU
        · exact Or.inl (Or.inl (by simp [haU]))
      · by_cases hbU : x ∈ U
        · exact Or.inr hbU
        · exact Or.inl (Or.inr (by simp [hbU]))
      · exact Or.inr hx
  have hV_nd : V.Nodup := by
    simp only [V, addA, addB]
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [haU, hbU, hUnd, hab]
  have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
    intro s hs
    rw [hV_mem] at hs
    rcases hs with rfl | rfl | hsU
    · exact ⟨haW, ha0, ha1⟩
    · exact ⟨hbW, hb0, hb1⟩
    · exact hUsub s hsU
  have hV_len : V.length ≤ (k + 1) - t + 1 := by
    have hA : addA.length ≤ 1 := by simp only [addA]; split_ifs <;> simp
    have hB : addB.length ≤ 1 := by simp only [addB]; split_ifs <;> simp
    have hlenV : V.length = addA.length + addB.length + U.length := by
      simp only [V, List.length_append]
    omega
  have hV_sep : unionSep (decide (0 < t)) V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hsV', hsi⟩ := htop
    rw [hPermV'.mem_iff, List.mem_cons] at hsV'
    rcases hsV' with rfl | hsU
    · rw [hbin] at hsi
      rcases sep_bin_bit _ _ a b i hi hsi with ha_b | hb_b
      · exact ⟨a, (hV_mem a).2 (Or.inl rfl), ha_b⟩
      · exact ⟨b, (hV_mem b).2 (Or.inr (Or.inl rfl)), hb_b⟩
    · exact ⟨s, (hV_mem s).2 (Or.inr (Or.inr hsU)), hsi⟩
  let hkeep : List Sig :=
    if a ∈ U then (if b ∈ U then [a, b] else [a]) else (if b ∈ U then [b] else [])
  have hhkeep_mem : hkeep ∈ [[], [a], [b], [a, b]] := by
    simp only [hkeep]; split_ifs <;> simp
  have hdrop_nd : (dropped [a, b] V).Nodup := hV_nd.filter _
  have hperm_next : (sg :: (hkeep ++ dropped [a, b] V)).Perm V' := by
    refine perm_of_nodup_same_mem ?_ hVnd ?_
    · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
      have hkh_nd : hkeep.Nodup := by
        simp only [hkeep]; split_ifs <;> simp [hab]
      rw [List.nodup_cons, List.nodup_append]
      refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
      · intro hm
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · apply hsgU
          simp only [hkeep] at hm
          split_ifs at hm <;> simp at hm <;> rcases hm with rfl | rfl <;> assumption
        · exact hsgV_not (mem_dropped_iff.1 hm).1
      · intro x hx y hy hxy
        subst hxy
        have hynot := (mem_dropped_iff.1 hy).2
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hynot
        simp only [hkeep] at hx
        split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
    · intro x
      rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
      constructor
      · rintro (rfl | hx | hx)
        · exact Or.inl rfl
        · right
          simp only [hkeep] at hx
          split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl <;> assumption
        · right
          have hx' := mem_dropped_iff.1 hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
          rw [hV_mem] at hx'
          rcases hx'.1 with rfl | rfl | hxU
          · exact absurd rfl hx'.2.1
          · exact absurd rfl hx'.2.2
          · exact hxU
      · rintro (rfl | hxU)
        · exact Or.inl rfl
        · right
          by_cases hxa : x = a
          · subst hxa; left; simp only [hkeep]; split_ifs <;> simp
          · by_cases hxb : x = b
            · subst hxb; left; simp only [hkeep]; split_ifs <;> simp
            · right
              rw [mem_dropped_iff]
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨(hV_mem x).2 (Or.inr (Or.inr hxU)), hxa, hxb⟩
  have htry_ok : tryGate k t (search k t) V (dropped [a, b] V) (bin isOr a b)
      [[], [a], [b], [a, b]] = true := by
    have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
    rw [← hbin]
    refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
    · have := hperm_next.length_eq
      simp only [List.length_cons, List.length_append] at this
      omega
    · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
      rw [hVsep] at husep
      simp only [unionSep, unionSep_append] at husep
      rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a, b] V)) (unionSep _ hkeep)]
      exact husep
    · rw [search_perm k t hperm_next]
      exact hVsearch
  have hsearch_new : search (k + 1) t V = true := by
    simp only [search, Bool.or_eq_true]
    right
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine ⟨ht, a, (hV_mem a).2 (Or.inl rfl), b, (hV_mem b).2 (Or.inr (Or.inl rfl)),
      hab_ord, ?_⟩
    cases isOr
    · simp only [Bool.or_eq_true]; exact Or.inl htry_ok
    · simp only [Bool.or_eq_true]; exact Or.inr htry_ok
  exact ⟨V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

lemma extract_live (gs : List Gate) (hfan : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ W : List Sig, target ∈ evalGates gs W →
      ∃ k ≤ gs.length, ∃ t ≤ k, ∃ V : List Sig,
        V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
        V.length ≤ k - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
        search k t V = true := by
  induction gs with
  | nil =>
    intro W hT
    refine ⟨0, le_rfl, 0, le_rfl, [target], by simp, ?_, by simp, unionSep_target_eq_top, ?_⟩
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst hs
      exact ⟨hT, target_ne_zero, target_ne_one⟩
    · exact List.contains_iff_mem.2 (List.mem_singleton_self target)
  | cons g rest ih =>
    intro W hT
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    rw [evalGates_cons] at hT
    set sg := evalGateSig g W
    obtain ⟨k, hk, t, ht, V', hVnd, hVsub, hVlen, hVsep, hVsearch⟩ := ih hrest (W ++ [sg]) hT
    by_cases hskip : sg ∉ V' ∨ sg ∈ W
    · refine ⟨k, by simp; omega, t, ht, V', hVnd, ?_, hVlen, hVsep, hVsearch⟩
      intro s hs
      obtain ⟨hsmem, hs0, hs1⟩ := hVsub s hs
      rw [List.mem_append, List.mem_singleton] at hsmem
      rcases hsmem with hsmem | rfl
      · exact ⟨hsmem, hs0, hs1⟩
      · rcases hskip with hnot | hin
        · exact absurd hs hnot
        · exact ⟨hin, hs0, hs1⟩
    · push Not at hskip
      obtain ⟨hsgV, hsgW⟩ := hskip
      have hsg01 := hVsub sg hsgV
      have hsg0 : sg ≠ zero := hsg01.2.1
      have hsg1 : sg ≠ one := hsg01.2.2
      set U := V'.erase sg
      have hUnd : U.Nodup := hVnd.erase sg
      have hsgU : sg ∉ U := List.Nodup.not_mem_erase hVnd
      have hPermV' : V'.Perm (sg :: U) := List.perm_cons_erase hsgV
      have hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
        intro s hs
        have hsV : s ∈ V' := List.mem_of_mem_erase hs
        have hsne : s ≠ sg := fun h => hsgU (h ▸ hs)
        obtain ⟨hsm, hs0, hs1⟩ := hVsub s hsV
        rw [List.mem_append, List.mem_singleton] at hsm
        exact ⟨hsm.resolve_right hsne, hs0, hs1⟩
      have hUlen : U.length + 1 = V'.length := by
        have := hPermV'.length_eq
        simp at this
        omega
      rcases hg with ⟨hop, hinlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin false (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_left]; rfl
          have hb0_ne0 : b0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_right]; rfl
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_left]; simpa using hb0W
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_right]; simpa using ha0W
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          exact ⟨k + 1, by simp; omega, t, by omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg0; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin true (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h
            have hsgeq' : sg = b0 := by rw [hsgeq, h, bin_zero_left]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have hb0_ne0 : b0 ≠ zero := by
            intro h
            have hsgeq' : sg = a0 := by rw [hsgeq, h, bin_zero_right]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_left]; rfl
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_right]; rfl
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          exact ⟨k + 1, by simp; omega, t, by omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · have hsgeq : sg = neg (W.getD p zero) := by simp [sg, evalGateSig, hop, hin]
          set a := W.getD p zero
          have ha0 : a ≠ zero := by intro h; apply hsg1; rw [hsgeq, h, neg_zero]
          have ha1 : a ≠ one := by intro h; apply hsg0; rw [hsgeq, h, neg_one]
          have haW : a ∈ W := getD_mem_of_ne ha0
          let V : List Sig := if a ∈ U then U else a :: U
          have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x ∈ U := by
            intro x
            simp only [V]
            by_cases haU : a ∈ U
            · simp only [haU, ↓reduceIte]
              exact ⟨Or.inr, fun h => h.elim (fun hxa => hxa ▸ haU) id⟩
            · simp only [haU, ↓reduceIte, List.mem_cons]
          have hV_nd : V.Nodup := by
            simp only [V]
            by_cases haU : a ∈ U <;> simp [haU, hUnd]
          have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
            intro s hs
            rw [hV_mem] at hs
            rcases hs with rfl | hsU
            · exact ⟨haW, ha0, ha1⟩
            · exact hUsub s hsU
          have hV_len : V.length ≤ (k + 1) - (t + 1) + 1 := by
            have : V.length ≤ U.length + 1 := by simp only [V]; split_ifs <;> simp
            omega
          have hV_sep : unionSep (decide (0 < t + 1)) V = top := by
            apply bv_eq_top_of_bits
            intro i hi
            rw [unionSep_bit_iff _ _ i hi]
            have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
            rw [unionSep_bit_iff _ _ i hi] at htop
            obtain ⟨s, hsV', hsi⟩ := htop
            have hsi' : (sep true s)[i] = true := sep_mono_true _ s i hi hsi
            rw [hPermV'.mem_iff, List.mem_cons] at hsV'
            rcases hsV' with rfl | hsU
            · rw [hsgeq, sep_neg_true a i hi] at hsi'
              exact ⟨a, (hV_mem a).2 (Or.inl rfl), by simpa using hsi'⟩
            · exact ⟨s, (hV_mem s).2 (Or.inr hsU), by simpa using hsi'⟩
          let hkeep : List Sig := if a ∈ U then [a] else []
          have hhkeep_mem : hkeep ∈ [[], [a]] := by simp only [hkeep]; split_ifs <;> simp
          have hdrop_nd : (dropped [a] V).Nodup := hV_nd.filter _
          have hperm_next : (sg :: (hkeep ++ dropped [a] V)).Perm V' := by
            refine perm_of_nodup_same_mem ?_ hVnd ?_
            · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
              have hkh_nd : hkeep.Nodup := by simp only [hkeep]; split_ifs <;> simp
              rw [List.nodup_cons, List.nodup_append]
              refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
              · intro hm
                rw [List.mem_append] at hm
                rcases hm with hm | hm
                · apply hsgU
                  simp only [hkeep] at hm
                  split_ifs at hm <;> simp at hm
                  rw [hm]; assumption
                · exact hsgV_not (mem_dropped_iff.1 hm).1
              · intro x hx y hy hxy
                subst hxy
                have hynot := (mem_dropped_iff.1 hy).2
                simp only [List.mem_singleton] at hynot
                simp only [hkeep] at hx
                split_ifs at hx <;> simp at hx
                exact hynot hx
            · intro x
              rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
              constructor
              · rintro (rfl | hx | hx)
                · exact Or.inl rfl
                · right
                  simp only [hkeep] at hx
                  split_ifs at hx <;> simp at hx
                  subst hx; assumption
                · right
                  have hx' := mem_dropped_iff.1 hx
                  simp only [List.mem_singleton] at hx'
                  rw [hV_mem] at hx'
                  exact hx'.1.resolve_left hx'.2
              · rintro (rfl | hxU)
                · exact Or.inl rfl
                · right
                  by_cases hxa : x = a
                  · subst hxa; left; simp only [hkeep]; split_ifs; simp
                  · right
                    rw [mem_dropped_iff]
                    simp only [List.mem_singleton]
                    exact ⟨(hV_mem x).2 (Or.inr hxU), hxa⟩
          have hsearch_new : search (k + 1) (t + 1) V = true := by
            simp only [search, Bool.or_eq_true]
            left
            right
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
            refine ⟨by omega, a, (hV_mem a).2 (Or.inl rfl), ?_⟩
            simp only [Nat.add_sub_cancel]
            have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
            rw [← hsgeq]
            refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
            · have := hperm_next.length_eq
              simp only [List.length_cons, List.length_append] at this
              omega
            · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
              rw [hVsep] at husep
              simp only [unionSep, unionSep_append] at husep
              rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a] V)) (unionSep _ hkeep)]
              exact husep
            · rw [search_perm k t hperm_next]
              exact hVsearch
          exact ⟨k + 1, by simp; omega, t + 1, by omega, V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

lemma wiresToSigs_getD (wa wb : Fin 90 → List Bool) (len : ℕ)
    (hwa : ∀ r, (wa r).length = len) (hwb : ∀ r, (wb r).length = len) (i : ℕ) :
    (wiresToSigs wa wb len).getD i zero =
      (mkBV (fun r => (wa r).getD i false),
       mkBV (fun r => (wb r).getD i false)) := by
  by_cases hi : i < len
  · have hlen : (wiresToSigs wa wb len).length = len := by simp [wiresToSigs]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp [wiresToSigs]
  · have hlen : (wiresToSigs wa wb len).length = len := by simp [wiresToSigs]
    rw [List.getD_eq_default _ _ (by omega)]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [zero, getElem_mkBV]
      rw [zero_bit r hr, List.getD_eq_default _ _ (by rw [hwa ⟨r, hr⟩]; omega)]
    · simp only [zero, getElem_mkBV]
      rw [zero_bit r hr, List.getD_eq_default _ _ (by rw [hwb ⟨r, hr⟩]; omega)]

lemma wiresToSigs_step (wa wb : Fin 90 → List Bool) (len : ℕ)
    (hwa : ∀ r, (wa r).length = len) (hwb : ∀ r, (wb r).length = len)
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    wiresToSigs
      (fun r => wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])
      (fun r => wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])
      (len + 1) =
    wiresToSigs wa wb len ++ [evalGateSig g (wiresToSigs wa wb len)] := by
  have hprefix :
      (List.range len).map (fun idx =>
        (mkBV (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD idx false),
         mkBV (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD idx false))) =
      wiresToSigs wa wb len := by
    unfold wiresToSigs
    apply List.map_congr_left
    intro idx hidx
    rw [List.mem_range] at hidx
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [getElem_mkBV]
      rw [List.getD_eq_getElem _ _ (by simp [hwa ⟨r, hr⟩]; omega),
        List.getElem_append_left (by rw [hwa ⟨r, hr⟩]; omega),
        List.getD_eq_getElem _ _ (by rw [hwa ⟨r, hr⟩]; omega)]
    · simp only [getElem_mkBV]
      rw [List.getD_eq_getElem _ _ (by simp [hwb ⟨r, hr⟩]; omega),
        List.getElem_append_left (by rw [hwb ⟨r, hr⟩]; omega),
        List.getD_eq_getElem _ _ (by rw [hwb ⟨r, hr⟩]; omega)]
  have hlast :
      (mkBV (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD len false),
       mkBV (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD len false)) =
      evalGateSig g (wiresToSigs wa wb len) := by
    have hgetLast : ∀ (w : List Bool) (v : Bool), w.length = len → (w ++ [v]).getD len false = v := by
      intro w v hw
      rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_append_right (by omega)]
      simp [hw]
    have hA : (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD len false) =
        fun r => g.op.eval (g.inputs.map fun i => (wa r).getD i false) := by
      funext r; exact hgetLast (wa r) _ (hwa r)
    have hB : (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD len false) =
        fun r => g.op.eval (g.inputs.map fun i => (wb r).getD i false) := by
      funext r; exact hgetLast (wb r) _ (hwb r)
    rw [hA, hB]
    rcases hg with ⟨hop, hinlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop | hop
    · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.all_nil]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [one, top, getElem_mkBV, BitVec.getElem_allOnes]
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact (wiresToSigs_getD wa wb len hwa hwb p).symm
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [wiresToSigs_getD wa wb len hwa hwb p, wiresToSigs_getD wa wb len hwa hwb q]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [bin, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, getElem_mkBV]
      · rw [hin] at hinlen; simp at hinlen
    · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.any_nil]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          (simp only [zero, getElem_mkBV]; exact (zero_bit r hr).symm)
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact (wiresToSigs_getD wa wb len hwa hwb p).symm
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        rw [wiresToSigs_getD wa wb len hwa hwb p, wiresToSigs_getD wa wb len hwa hwb q]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [bin, ↓reduceIte, BitVec.getElem_or, getElem_mkBV]
      · rw [hin] at hinlen; simp at hinlen
    · rcases hin : g.inputs with _ | ⟨p, _⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.headD_nil, Bool.not_false]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [one, top, getElem_mkBV, BitVec.getElem_allOnes]
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.headD_cons]
        rw [wiresToSigs_getD wa wb len hwa hwb p]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [neg, BitVec.getElem_not, getElem_mkBV]
  show (List.range (len + 1)).map _ = _
  rw [List.range_succ, List.map_append, List.map_singleton, hprefix, hlast]

lemma evalWires_len (gs : List Gate) (w : List Bool) :
    (evalWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalWires]
  | cons g rest ih =>
    rw [evalWires_cons, ih]
    simp
    omega

lemma wiresToSigs_evalGates (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (wa wb : Fin 90 → List Bool) (len : ℕ),
      (∀ r, (wa r).length = len) → (∀ r, (wb r).length = len) →
      wiresToSigs (fun r => evalWires gs (wa r)) (fun r => evalWires gs (wb r)) (len + gs.length) =
        evalGates gs (wiresToSigs wa wb len) := by
  induction gs with
  | nil =>
    intro wa wb len _ _
    simp [evalWires, evalGates]
  | cons g rest ih =>
    intro wa wb len hwa hwb
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    have h1 := ih hrest
      (fun r => wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])
      (fun r => wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])
      (len + 1)
      (fun r => by simp [hwa r])
      (fun r => by simp [hwb r])
    simp only [List.length_cons]
    rw [show len + (rest.length + 1) = len + 1 + rest.length by omega]
    have hwa_eq : (fun r => evalWires (g :: rest) (wa r)) =
        (fun r => evalWires rest (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])) := rfl
    have hwb_eq : (fun r => evalWires (g :: rest) (wb r)) =
        (fun r => evalWires rest (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])) := rfl
    rw [hwa_eq, hwb_eq, evalGates_cons, h1, wiresToSigs_step wa wb len hwa hwb g hg]

lemma sample_lower (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (accepts : ∀ r : Fin 90, C.eval (List.ofFn (pairA r)) = true)
    (rejects : ∀ r : Fin 90, C.eval (List.ofFn (pairB r)) = false) :
    9 ≤ C.size := by
  by_contra small
  have hlen : C.gates.length ≤ 8 := by
    change ¬ 9 ≤ C.gates.length at small
    omega
  have hW := wiresToSigs_evalGates C.gates hfan
    (fun r => List.ofFn (pairA r)) (fun r => List.ofFn (pairB r)) 6
    (fun r => by simp) (fun r => by simp)
  have htarget_eq : (evalGates C.gates initList).getD C.output zero = target := by
    rw [← initList_eq, ← hW]
    rw [wiresToSigs_getD _ _ (6 + C.gates.length)
      (fun r => by rw [evalWires_len]; simp)
      (fun r => by rw [evalWires_len]; simp) C.output]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [target, top, getElem_mkBV, BitVec.getElem_allOnes]
      exact accepts ⟨r, hr⟩
    · simp only [target, getElem_mkBV]
      rw [zero_bit r hr]
      exact rejects ⟨r, hr⟩
  have hTmem : target ∈ evalGates C.gates initList :=
    htarget_eq ▸ getD_mem_of_ne (by rw [htarget_eq]; exact target_ne_zero)
  obtain ⟨k, hk, t, ht, V, hVnd, hVsub, hVlen, hVsep, hVsearch⟩ :=
    extract_live C.gates hfan initList hTmem
  have hVsep_true : unionSep true V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V)[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hs, hsi⟩ := htop
    exact ⟨s, hs, sep_mono_true _ s i hi hsi⟩
  have hall_in_V : ∀ s ∈ initList, s ∈ V := by
    intro s hs
    by_contra hnot
    apply all_init_needed s hs
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep true V)[i] = true := by rw [hVsep_true]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨u, huV, hui⟩ := htop
    have huInit : u ∈ initList := (hVsub u huV).1
    have hune : u ≠ s := fun h => hnot (h ▸ huV)
    exact ⟨u, (List.mem_erase_of_ne hune).2 huInit, hui⟩
  have hPermInit : V.Perm initList :=
    perm_of_nodup_same_mem hVnd initList_nodup (fun x => ⟨fun h => (hVsub x h).1, hall_in_V x⟩)
  have hVlen6 : V.length = 6 := hPermInit.length_eq.trans initList_len
  have hk8 : k ≤ 8 := le_trans hk hlen
  have hsearch_init : search k t initList = true := by
    rw [← search_perm k t hPermInit]
    exact hVsearch
  have hcases : (k = 5 ∧ t = 0) ∨
      (k = 6 ∧ t = 0) ∨
      (k = 6 ∧ t = 1) ∨
      (k = 7 ∧ t = 0) ∨
      (k = 7 ∧ t = 1) ∨
      (k = 7 ∧ t = 2) ∨
      (k = 8 ∧ t = 0) ∨
      (k = 8 ∧ t = 1) ∨
      (k = 8 ∧ t = 2) ∨
      (k = 8 ∧ t = 3) := by omega
  rcases hcases with ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · rw [search_5_0] at hsearch_init; simp at hsearch_init
  · rw [search_6_0] at hsearch_init; simp at hsearch_init
  · rw [search_6_1] at hsearch_init; simp at hsearch_init
  · rw [search_7_0] at hsearch_init; simp at hsearch_init
  · rw [search_7_1] at hsearch_init; simp at hsearch_init
  · rw [search_7_2] at hsearch_init; simp at hsearch_init
  · rw [search_8_0] at hsearch_init; simp at hsearch_init
  · rw [search_8_1] at hsearch_init; simp at hsearch_init
  · rw [search_8_2] at hsearch_init; simp at hsearch_init
  · rw [search_8_3] at hsearch_init; simp at hsearch_init

lemma sample_counts :
    (pairs.map Prod.fst).eraseDups.length = 24 ∧ (pairs.map Prod.snd).eraseDups.length = 9 := by
  decide

private def triangleUnion : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [7, 8]⟩,
    ⟨.or, [3, 4]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 12]⟩,
    ⟨.or, [9, 13]⟩], 14⟩

lemma upper (s : ℕ) (hs : 9 ≤ s) : HasCircuitSize 6 targetFun s := by
  refine ⟨triangleUnion, ?_, hs, ?_⟩
  · intro gate hg
    simp only [triangleUnion, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Set.mem_insert_iff]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    rw [inputs]
    change ((([x 2, [x 0, x 1].any id].all id) ||
      ([x 0, x 1].all id || false)) ||
      ((([x 5, [x 3, x 4].any id].all id) ||
        ([x 3, x 4].all id || false)) || false)) = targetFun x
    simp only [List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq,
      Bool.or_false, Bool.and_true, targetFun]
    grind

end PEqualNP.Outside.L_meta_163_aux

theorem PEqualNP.Outside.L_meta_163 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) s ↔ 9 ≤ s := by
  intro s
  constructor
  · rintro ⟨C, hfan, hsize, hcorrect⟩
    refine le_trans (PEqualNP.Outside.L_meta_163_aux.sample_lower C hfan ?_ ?_) hsize
    · intro r
      exact (hcorrect _).trans (PEqualNP.Outside.L_meta_163_aux.pairA_true r)
    · intro r
      exact (hcorrect _).trans (PEqualNP.Outside.L_meta_163_aux.pairB_false r)
  · exact PEqualNP.Outside.L_meta_163_aux.upper s
