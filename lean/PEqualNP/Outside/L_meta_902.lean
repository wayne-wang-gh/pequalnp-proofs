import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_902_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev B := BitVec 66
abbrev Sig := B × B

def maskFun (m : ℕ) : Fin 7 → Bool := fun i => m.testBit i.val

def pA (prs : List (ℕ × ℕ)) (r : Fin 66) : Fin 7 → Bool := maskFun (prs.getD r.val (0, 0)).1
def pB (prs : List (ℕ × ℕ)) (r : Fin 66) : Fin 7 → Bool := maskFun (prs.getD r.val (0, 0)).2

def mkBVLoop : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, p => 2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0

def mkBV (p : Fin 66 → Bool) : B :=
  BitVec.ofNat 66 (mkBVLoop 66 (fun i => if h : i < 66 then p ⟨i, h⟩ else false))

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

lemma getElem_mkBV (p : Fin 66 → Bool) (i : ℕ) (hi : i < 66) :
    (mkBV p)[i] = p ⟨i, hi⟩ := by
  unfold mkBV
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  simp only [decide_eq_true hi, Bool.true_and]
  rw [testBit_mkBVLoop 66 _ i hi]
  simp [hi]

lemma zero_bit (i : ℕ) (hi : i < 66) : (0 : B)[i] = false := by simp

def top : B := BitVec.allOnes 66
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

def wiresToSigs (wa wb : Fin 66 → List Bool) (len : ℕ) : List Sig :=
  (List.range len).map (fun idx =>
    (mkBV (fun r => (wa r).getD idx false),
     mkBV (fun r => (wb r).getD idx false)))

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
lemma target_ne_zero : target ≠ zero := by decide
lemma target_ne_one : target ≠ one := by decide

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

lemma unionSep_bit_iff (d : Bool) (v : List Sig) (i : ℕ) (hi : i < 66) :
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

lemma bv_eq_top_of_bits {x : B} (h : ∀ i (hi : i < 66), x[i] = true) : x = top := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [top, BitVec.getElem_allOnes]
  exact h i hi

lemma top_bit (i : ℕ) (hi : i < 66) : top[i] = true := by
  rw [top, BitVec.getElem_allOnes]

lemma sep_mono_true (d : Bool) (a : Sig) (i : ℕ) (hi : i < 66) :
    (sep d a)[i] = true → (sep true a)[i] = true := by
  cases d
  · simp only [sep, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not,
      BitVec.getElem_xor, Bool.and_eq_true, Bool.not_eq_true']
    intro h
    simp [h.1, h.2]
  · exact id

lemma sep_neg_true (a : Sig) (i : ℕ) (hi : i < 66) :
    (sep true (neg a))[i] = (sep true a)[i] := by
  simp only [sep, neg, ↓reduceIte, BitVec.getElem_xor, BitVec.getElem_not]
  cases a.1[i] <;> cases a.2[i] <;> rfl

lemma sep_bin_bit (d isOr : Bool) (a b : Sig) (i : ℕ) (hi : i < 66) :
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
                  · subst hxa; left; simp only [hkeep]; split_ifs <;> simp
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

lemma wiresToSigs_getD (wa wb : Fin 66 → List Bool) (len : ℕ)
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

lemma wiresToSigs_step (wa wb : Fin 66 → List Bool) (len : ℕ)
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
    ∀ (wa wb : Fin 66 → List Bool) (len : ℕ),
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


lemma lower (f : (Fin 7 → Bool) → Bool) (prs : List (ℕ × ℕ)) (init : List Sig)
    (hinit : wiresToSigs (fun r => List.ofFn (pA prs r)) (fun r => List.ofFn (pB prs r)) 7 = init)
    (hA : ∀ r : Fin 66, f (pA prs r) = true) (hB : ∀ r : Fin 66, f (pB prs r) = false)
    (hnd : init.Nodup) (hl : init.length = 7)
    (hneed : init.all (fun s => unionSep true (init.erase s) != top) = true)
    (L : ℕ) (hL : L ≤ 8) (h6 : 7 ≤ L → search 6 0 init = false)
    (h7 : 8 ≤ L → search 7 0 init = false ∧ search 7 1 init = false)
    {s : ℕ} (hs : s < L) (hC : HasCircuitSize 7 f s) : False := by
  obtain ⟨C, hfan, hsz, hev⟩ := hC
  have hlen : C.gates.length < L := lt_of_le_of_lt hsz hs
  have hW := wiresToSigs_evalGates C.gates hfan
    (fun r => List.ofFn (pA prs r)) (fun r => List.ofFn (pB prs r)) 7
    (fun r => by simp) (fun r => by simp)
  have htarget_eq : (evalGates C.gates init).getD C.output zero = target := by
    rw [← hinit, ← hW]
    rw [wiresToSigs_getD _ _ (7 + C.gates.length)
      (fun r => by rw [evalWires_len]; simp)
      (fun r => by rw [evalWires_len]; simp) C.output]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [target, top, getElem_mkBV, BitVec.getElem_allOnes]
      have h1 := hev (pA prs ⟨r, hr⟩)
      rw [hA ⟨r, hr⟩] at h1
      exact h1
    · simp only [target, getElem_mkBV]
      rw [zero_bit r hr]
      have h1 := hev (pB prs ⟨r, hr⟩)
      rw [hB ⟨r, hr⟩] at h1
      exact h1
  have hTmem : target ∈ evalGates C.gates init :=
    htarget_eq ▸ getD_mem_of_ne (by rw [htarget_eq]; exact target_ne_zero)
  obtain ⟨k, hk, t, ht, V, hVnd, hVsub, hVlen, hVsep, hVsearch⟩ :=
    extract_live C.gates hfan init hTmem
  have hVsep_true : unionSep true V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V)[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hs, hsi⟩ := htop
    exact ⟨s, hs, sep_mono_true _ s i hi hsi⟩
  have hall_in_V : ∀ s ∈ init, s ∈ V := by
    intro s hs
    by_contra hnot
    have hne : unionSep true (init.erase s) ≠ top := bne_iff_ne.1 (List.all_eq_true.1 hneed s hs)
    apply hne
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep true V)[i] = true := by rw [hVsep_true]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨u, huV, hui⟩ := htop
    have huInit : u ∈ init := (hVsub u huV).1
    have hune : u ≠ s := fun h => hnot (h ▸ huV)
    exact ⟨u, (List.mem_erase_of_ne hune).2 huInit, hui⟩
  have hPermInit : V.Perm init :=
    perm_of_nodup_same_mem hVnd hnd (fun x => ⟨fun h => (hVsub x h).1, hall_in_V x⟩)
  have hVlen7 : V.length = 7 := hPermInit.length_eq.trans hl
  have hsearch_init : search k t init = true := by
    rw [← search_perm k t hPermInit]
    exact hVsearch
  have hcases : (k = 6 ∧ t = 0 ∧ 7 ≤ L) ∨ (k = 7 ∧ t = 0 ∧ 8 ≤ L) ∨ (k = 7 ∧ t = 1 ∧ 8 ≤ L) := by
    omega
  rcases hcases with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
  · rw [h6 h] at hsearch_init; simp at hsearch_init
  · rw [(h7 h).1] at hsearch_init; simp at hsearch_init
  · rw [(h7 h).2] at hsearch_init; simp at hsearch_init

theorem ofFn7 (x : Fin 7 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

def prs1 : List (ℕ × ℕ) :=
  [(3, 1), (5, 1), (9, 1), (17, 1), (33, 1), (65, 1), (127, 126), (3, 1), (3, 126), (5, 1), (5, 126), (9, 1), (9, 126), (17, 1), (17, 126), (33, 1), (33, 126), (65, 1), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126), (65, 126)]

def init1 : List Sig :=
  [(BitVec.ofNat 66 73786976294838206463, BitVec.ofNat 66 174783),
   (BitVec.ofNat 66 449, BitVec.ofNat 66 73786976294838031680),
   (BitVec.ofNat 66 1602, BitVec.ofNat 66 73786976294838031680),
   (BitVec.ofNat 66 6212, BitVec.ofNat 66 73786976294838031680),
   (BitVec.ofNat 66 24648, BitVec.ofNat 66 73786976294838031680),
   (BitVec.ofNat 66 98384, BitVec.ofNat 66 73786976294838031680),
   (BitVec.ofNat 66 73786976294838075488, BitVec.ofNat 66 73786976294838031680)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init1_eq :
    wiresToSigs (fun r => List.ofFn (pA prs1 r)) (fun r => List.ofFn (pB prs1 r)) 7 = init1 := by
  decide

theorem c1 : ∀ s1 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x1 : Fin 7 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 0 && x1 6)) s1 ↔ 6 ≤ s1 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x1 : Fin 7 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 0 && x1 6)) prs1 init1 init1_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 6 (by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩], 12⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs2 : List (ℕ × ℕ) :=
  [(63, 62), (126, 62), (67, 65), (69, 65), (73, 65), (81, 65), (97, 65), (125, 124), (126, 124), (3, 62), (3, 65), (3, 124), (5, 62), (5, 65), (5, 124), (9, 62), (9, 65), (9, 124), (17, 62), (17, 65), (17, 124), (33, 62), (33, 65), (33, 124), (66, 62), (66, 65), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124)]

def init2 : List Sig :=
  [(BitVec.ofNat 66 16776957, BitVec.ofNat 66 38347900),
   (BitVec.ofNat 66 73786976294821433095, BitVec.ofNat 66 19173891),
   (BitVec.ofNat 66 29067, BitVec.ofNat 66 73786976294799858563),
   (BitVec.ofNat 66 229779, BitVec.ofNat 66 73786976294799858563),
   (BitVec.ofNat 66 1835427, BitVec.ofNat 66 73786976294799858563),
   (BitVec.ofNat 66 14680515, BitVec.ofNat 66 73786976294799858563),
   (BitVec.ofNat 66 73786976294821429758, BitVec.ofNat 66 73786976294819032572)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init2_eq :
    wiresToSigs (fun r => List.ofFn (pA prs2 r)) (fun r => List.ofFn (pB prs2 r)) 7 = init2 := by
  decide

lemma s60_2 : search 6 0 init2 = false := by decide

theorem c2 : ∀ s2 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x2 : Fin 7 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 0 && x2 5) || (x2 1 && x2 6)) s2 ↔ 7 ≤ s2 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x2 : Fin 7 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 0 && x2 5) || (x2 1 && x2 6)) prs2 init2 init2_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 7 (by decide) (fun _ => s60_2) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [11, 12]⟩], 13⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs3 : List (ℕ × ℕ) :=
  [(7, 6), (14, 6), (22, 6), (38, 6), (70, 6), (61, 60), (62, 60), (124, 60), (67, 66), (70, 66), (74, 66), (82, 66), (98, 66), (123, 121), (125, 121), (3, 6), (3, 60), (3, 66), (3, 121), (5, 6), (5, 60), (5, 66), (5, 121), (10, 6), (10, 60), (10, 66), (10, 121), (18, 6), (18, 60), (18, 66), (18, 121), (34, 6), (34, 60), (34, 66), (34, 121), (68, 6), (68, 60), (68, 66), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121)]

def init3 : List Sig :=
  [(BitVec.ofNat 66 8380705, BitVec.ofNat 66 73786976038285500416),
   (BitVec.ofNat 66 34351857503, BitVec.ofNat 66 183251935007),
   (BitVec.ofNat 66 73786976260486349567, BitVec.ofNat 66 109951156479),
   (BitVec.ofNat 66 125854946, BitVec.ofNat 66 73786976111586271456),
   (BitVec.ofNat 66 2013292772, BitVec.ofNat 66 73786976111586271456),
   (BitVec.ofNat 66 32212283624, BitVec.ofNat 66 73786976111586271456),
   (BitVec.ofNat 66 73786976260478500752, BitVec.ofNat 66 73786976184887049984)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init3_eq :
    wiresToSigs (fun r => List.ofFn (pA prs3 r)) (fun r => List.ofFn (pB prs3 r)) 7 = init3 := by
  decide

lemma s60_3 : search 6 0 init3 = false := by decide

theorem c3 : ∀ s3 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x3 : Fin 7 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 1 && x3 3) || (x3 1 && x3 4) || (x3 1 && x3 5) || (x3 2 && x3 6)) s3 ↔ 7 ≤ s3 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x3 : Fin 7 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 1 && x3 3) || (x3 1 && x3 4) || (x3 1 && x3 5) || (x3 2 && x3 6)) prs3 init3 init3_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 7 (by decide) (fun _ => s60_3) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [0, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs4 : List (ℕ × ℕ) :=
  [(31, 30), (62, 30), (94, 30), (99, 97), (101, 97), (105, 97), (113, 97), (125, 124), (126, 124), (3, 30), (3, 97), (3, 124), (5, 30), (5, 97), (5, 124), (9, 30), (9, 97), (9, 124), (17, 30), (17, 97), (17, 124), (34, 30), (34, 97), (34, 124), (66, 30), (66, 97), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124), (66, 124)]

def init4 : List Sig :=
  [(BitVec.ofNat 66 2096889, BitVec.ofNat 66 38347896),
   (BitVec.ofNat 66 73786976294836113167, BitVec.ofNat 66 19173895),
   (BitVec.ofNat 66 29079, BitVec.ofNat 66 73786976294799858567),
   (BitVec.ofNat 66 229799, BitVec.ofNat 66 73786976294799858567),
   (BitVec.ofNat 66 1835463, BitVec.ofNat 66 73786976294799858567),
   (BitVec.ofNat 66 14680570, BitVec.ofNat 66 73786976294819032568),
   (BitVec.ofNat 66 73786976294821429756, BitVec.ofNat 66 73786976294819032568)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init4_eq :
    wiresToSigs (fun r => List.ofFn (pA prs4 r)) (fun r => List.ofFn (pB prs4 r)) 7 = init4 := by
  decide

lemma s60_4 : search 6 0 init4 = false := by decide

theorem c4 : ∀ s4 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x4 : Fin 7 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 0 && x4 4) || (x4 1 && x4 5) || (x4 1 && x4 6)) s4 ↔ 7 ≤ s4 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x4 : Fin 7 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 0 && x4 4) || (x4 1 && x4 5) || (x4 1 && x4 6)) prs4 init4 init4_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 7 (by decide) (fun _ => s60_4) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs5 : List (ℕ × ℕ) :=
  [(31, 30), (62, 30), (94, 30), (61, 60), (62, 60), (124, 60), (91, 90), (94, 90), (122, 90), (99, 97), (101, 97), (105, 97), (113, 97), (121, 120), (122, 120), (124, 120), (3, 30), (3, 60), (3, 90), (3, 97), (3, 120), (5, 30), (5, 60), (5, 90), (5, 97), (5, 120), (9, 30), (9, 60), (9, 90), (9, 97), (9, 120), (17, 30), (17, 60), (17, 90), (17, 97), (17, 120), (34, 30), (34, 60), (34, 90), (34, 97), (34, 120), (68, 30), (68, 60), (68, 90), (68, 97), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120)]

def init5 : List Sig :=
  [(BitVec.ofNat 66 68719427145, BitVec.ofNat 66 18159675907584),
   (BitVec.ofNat 66 2130305827799, BitVec.ofNat 66 11349797437895),
   (BitVec.ofNat 66 73786974095879996607, BitVec.ofNat 66 6809878462527),
   (BitVec.ofNat 66 2080434687, BitVec.ofNat 66 73786958135162298879),
   (BitVec.ofNat 66 66572055039, BitVec.ofNat 66 73786958135162298879),
   (BitVec.ofNat 66 2130303844154, BitVec.ofNat 66 73786964945040768568),
   (BitVec.ofNat 66 73786974095815016420, BitVec.ofNat 66 73786969484959743936)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init5_eq :
    wiresToSigs (fun r => List.ofFn (pA prs5 r)) (fun r => List.ofFn (pB prs5 r)) 7 = init5 := by
  decide

lemma s60_5 : search 6 0 init5 = false := by decide

lemma s70_5 : search 7 0 init5 = false := by decide

lemma s71_5 : search 7 1 init5 = false := by decide

theorem c5 : ∀ s5 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x5 : Fin 7 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 0 && x5 3) || (x5 0 && x5 4) || (x5 1 && x5 5) || (x5 2 && x5 6)) s5 ↔ 8 ≤ s5 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x5 : Fin 7 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 0 && x5 3) || (x5 0 && x5 4) || (x5 1 && x5 5) || (x5 2 && x5 6)) prs5 init5 init5_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 8 (by decide) (fun _ => s60_5) (fun _ => ⟨s70_5, s71_5⟩) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs6 : List (ℕ × ℕ) :=
  [(7, 6), (14, 6), (22, 6), (38, 6), (70, 6), (29, 28), (30, 28), (60, 28), (92, 28), (99, 98), (102, 98), (106, 98), (114, 98), (123, 121), (125, 121), (3, 6), (3, 28), (3, 98), (3, 121), (5, 6), (5, 28), (5, 98), (5, 121), (10, 6), (10, 28), (10, 98), (10, 121), (18, 6), (18, 28), (18, 98), (18, 121), (36, 6), (36, 28), (36, 98), (36, 121), (68, 6), (68, 28), (68, 98), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121), (68, 121)]

def init6 : List Sig :=
  [(BitVec.ofNat 66 8380961, BitVec.ofNat 66 73786976038285500416),
   (BitVec.ofNat 66 2139602527, BitVec.ofNat 66 183251934751),
   (BitVec.ofNat 66 73786976292698605055, BitVec.ofNat 66 109951156735),
   (BitVec.ofNat 66 125856226, BitVec.ofNat 66 73786976111586271712),
   (BitVec.ofNat 66 2013295076, BitVec.ofNat 66 73786976111586271712),
   (BitVec.ofNat 66 32212287112, BitVec.ofNat 66 73786976184887049728),
   (BitVec.ofNat 66 73786976260478500624, BitVec.ofNat 66 73786976184887049728)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init6_eq :
    wiresToSigs (fun r => List.ofFn (pA prs6 r)) (fun r => List.ofFn (pB prs6 r)) 7 = init6 := by
  decide

lemma s60_6 : search 6 0 init6 = false := by decide

theorem c6 : ∀ s6 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x6 : Fin 7 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 1 && x6 3) || (x6 1 && x6 4) || (x6 2 && x6 5) || (x6 2 && x6 6)) s6 ↔ 7 ≤ s6 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x6 : Fin 7 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 1 && x6 3) || (x6 1 && x6 4) || (x6 2 && x6 5) || (x6 2 && x6 6)) prs6 init6 init6_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 7 (by decide) (fun _ => s60_6) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [0, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs7 : List (ℕ × ℕ) :=
  [(35, 34), (38, 34), (42, 34), (50, 34), (98, 34), (59, 57), (61, 57), (121, 57), (71, 70), (78, 70), (86, 70), (102, 70), (91, 89), (93, 89), (121, 89), (93, 92), (94, 92), (124, 92), (3, 34), (3, 57), (3, 70), (3, 89), (3, 92), (5, 34), (5, 57), (5, 70), (5, 89), (5, 92), (10, 34), (10, 57), (10, 70), (10, 89), (10, 92), (18, 34), (18, 57), (18, 70), (18, 89), (18, 92), (36, 34), (36, 57), (36, 70), (36, 89), (36, 92), (96, 34), (96, 57), (96, 70), (96, 89), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92)]

def init7 : List Sig :=
  [(BitVec.ofNat 66 268235233, BitVec.ofNat 66 90798379528416),
   (BitVec.ofNat 66 274617671487, BitVec.ofNat 66 45399189753631),
   (BitVec.ofNat 66 8521475403586, BitVec.ofNat 66 73786876416620728064),
   (BitVec.ofNat 66 8321757924, BitVec.ofNat 66 73786930895648452832),
   (BitVec.ofNat 66 266288231656, BitVec.ofNat 66 73786930895648452832),
   (BitVec.ofNat 66 73786976019960449279, BitVec.ofNat 66 27239513850111),
   (BitVec.ofNat 66 73786967498745446288, BitVec.ofNat 66 73786949055324356352)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init7_eq :
    wiresToSigs (fun r => List.ofFn (pA prs7 r)) (fun r => List.ofFn (pB prs7 r)) 7 = init7 := by
  decide

lemma s60_7 : search 6 0 init7 = false := by decide

lemma s70_7 : search 7 0 init7 = false := by decide

lemma s71_7 : search 7 1 init7 = false := by decide

theorem c7 : ∀ s7 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x7 : Fin 7 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 1 && x7 3) || (x7 1 && x7 4) || (x7 2 && x7 5) || (x7 5 && x7 6)) s7 ↔ 8 ≤ s7 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x7 : Fin 7 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 1 && x7 3) || (x7 1 && x7 4) || (x7 2 && x7 5) || (x7 5 && x7 6)) prs7 init7 init7_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 8 (by decide) (fun _ => s60_7) (fun _ => ⟨s70_7, s71_7⟩) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs8 : List (ℕ × ℕ) :=
  [(29, 28), (30, 28), (60, 28), (92, 28), (51, 49), (53, 49), (57, 49), (113, 49), (57, 56), (58, 56), (60, 56), (120, 56), (79, 78), (94, 78), (110, 78), (99, 97), (101, 97), (105, 97), (113, 97), (107, 106), (110, 106), (122, 106), (3, 28), (3, 49), (3, 56), (3, 78), (3, 97), (3, 106), (5, 28), (5, 49), (5, 56), (5, 78), (5, 97), (5, 106), (9, 28), (9, 49), (9, 56), (9, 78), (9, 97), (9, 106), (18, 28), (18, 49), (18, 56), (18, 78), (18, 97), (18, 106), (36, 28), (36, 49), (36, 56), (36, 78), (36, 97), (36, 106), (80, 28), (80, 49), (80, 56), (80, 78), (80, 97), (80, 106), (80, 106), (80, 106), (80, 106), (80, 106), (80, 106), (80, 106), (80, 106), (80, 106)]

def init8 : List Sig :=
  [(BitVec.ofNat 66 1099508453873, BitVec.ofNat 66 82351536042639600),
   (BitVec.ofNat 66 69269500523026, BitVec.ofNat 66 73681749332117188608),
   (BitVec.ofNat 66 4433247795770415, BitVec.ofNat 66 41175768021102607),
   (BitVec.ofNat 66 1082335592271, BitVec.ofNat 66 73704624758795566863),
   (BitVec.ofNat 66 73782541964445757439, BitVec.ofNat 66 32025597349728255),
   (BitVec.ofNat 66 4433230887374836, BitVec.ofNat 66 73745800526817103856),
   (BitVec.ofNat 66 73782472695215028360, BitVec.ofNat 66 73754950697488478208)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init8_eq :
    wiresToSigs (fun r => List.ofFn (pA prs8 r)) (fun r => List.ofFn (pB prs8 r)) 7 = init8 := by
  decide

lemma s60_8 : search 6 0 init8 = false := by decide

lemma s70_8 : search 7 0 init8 = false := by decide

lemma s71_8 : search 7 1 init8 = false := by decide

theorem c8 : ∀ s8 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x8 : Fin 7 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 0 && x8 3) || (x8 1 && x8 4) || (x8 2 && x8 5) || (x8 4 && x8 6)) s8 ↔ 8 ≤ s8 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x8 : Fin 7 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 0 && x8 3) || (x8 1 && x8 4) || (x8 2 && x8 5) || (x8 4 && x8 6)) prs8 init8 init8_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 8 (by decide) (fun _ => s60_8) (fun _ => ⟨s70_8, s71_8⟩) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs9 : List (ℕ × ℕ) :=
  [(15, 14), (30, 14), (46, 14), (78, 14), (61, 60), (62, 60), (124, 60), (75, 74), (78, 74), (90, 74), (106, 74), (115, 113), (117, 113), (121, 113), (121, 120), (122, 120), (124, 120), (3, 14), (3, 60), (3, 74), (3, 113), (3, 120), (5, 14), (5, 60), (5, 74), (5, 113), (5, 120), (9, 14), (9, 60), (9, 74), (9, 113), (9, 120), (18, 14), (18, 60), (18, 74), (18, 113), (18, 120), (34, 14), (34, 60), (34, 74), (34, 113), (34, 120), (68, 14), (68, 60), (68, 74), (68, 113), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120), (68, 120)]

def init9 : List Sig :=
  [(BitVec.ofNat 66 4294867089, BitVec.ofNat 66 36319351814144),
   (BitVec.ofNat 66 4393755643823, BitVec.ofNat 66 22699594876815),
   (BitVec.ofNat 66 73786971896921788799, BitVec.ofNat 66 13619756925055),
   (BitVec.ofNat 66 4160874495, BitVec.ofNat 66 73786939975486392319),
   (BitVec.ofNat 66 133144115826, BitVec.ofNat 66 73786953595243329648),
   (BitVec.ofNat 66 4260607687796, BitVec.ofNat 66 73786953595243329648),
   (BitVec.ofNat 66 73786971896791826376, BitVec.ofNat 66 73786962675081281408)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init9_eq :
    wiresToSigs (fun r => List.ofFn (pA prs9 r)) (fun r => List.ofFn (pB prs9 r)) 7 = init9 := by
  decide

lemma s60_9 : search 6 0 init9 = false := by decide

lemma s70_9 : search 7 0 init9 = false := by decide

lemma s71_9 : search 7 1 init9 = false := by decide

theorem c9 : ∀ s9 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x9 : Fin 7 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 1 && x9 4) || (x9 1 && x9 5) || (x9 2 && x9 6)) s9 ↔ 8 ≤ s9 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x9 : Fin 7 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 1 && x9 4) || (x9 1 && x9 5) || (x9 2 && x9 6)) prs9 init9 init9_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 8 (by decide) (fun _ => s60_9) (fun _ => ⟨s70_9, s71_9⟩) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs10 : List (ℕ × ℕ) :=
  [(15, 14), (30, 14), (46, 14), (78, 14), (29, 28), (30, 28), (60, 28), (92, 28), (43, 42), (46, 42), (58, 42), (106, 42), (57, 56), (58, 56), (60, 56), (120, 56), (71, 70), (78, 70), (86, 70), (102, 70), (85, 84), (86, 84), (92, 84), (116, 84), (99, 98), (102, 98), (106, 98), (114, 98), (115, 113), (117, 113), (121, 113), (3, 14), (3, 28), (3, 42), (3, 56), (3, 70), (3, 84), (3, 98), (3, 113), (5, 14), (5, 28), (5, 42), (5, 56), (5, 70), (5, 84), (5, 98), (5, 113), (9, 14), (9, 28), (9, 42), (9, 56), (9, 70), (9, 84), (9, 98), (9, 113), (18, 14), (18, 28), (18, 42), (18, 56), (18, 70), (18, 84), (18, 98), (18, 113), (36, 14), (36, 28), (36, 42)]

def init10 : List Sig :=
  [(BitVec.ofNat 66 36028796768424209, BitVec.ofNat 66 4629771062438002688),
   (BitVec.ofNat 66 9187343787967328047, BitVec.ofNat 66 49191317529428954895),
   (BitVec.ofNat 66 64563744446303126271, BitVec.ofNat 66 29514790517522497791),
   (BitVec.ofNat 66 35888060675850239, BitVec.ofNat 66 65106155554142748671),
   (BitVec.ofNat 66 9187343241865131250, BitVec.ofNat 66 24595658765409251568),
   (BitVec.ofNat 66 64563604260123115332, BitVec.ofNat 66 44272185777315708672),
   (BitVec.ofNat 66 2147453064, BitVec.ofNat 66 8680820740695457792)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init10_eq :
    wiresToSigs (fun r => List.ofFn (pA prs10 r)) (fun r => List.ofFn (pB prs10 r)) 7 = init10 := by
  decide

lemma s60_10 : search 6 0 init10 = false := by decide

lemma s70_10 : search 7 0 init10 = false := by decide

lemma s71_10 : search 7 1 init10 = false := by decide

theorem c10 : ∀ s10 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x10 : Fin 7 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 0 && x10 3) || (x10 1 && x10 4) || (x10 2 && x10 5) || (x10 3 && x10 6)) s10 ↔ 8 ≤ s10 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x10 : Fin 7 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 0 && x10 3) || (x10 1 && x10 4) || (x10 2 && x10 5) || (x10 3 && x10 6)) prs10 init10 init10_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 8 (by decide) (fun _ => s60_10) (fun _ => ⟨s70_10, s71_10⟩) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs11 : List (ℕ × ℕ) :=
  [(35, 33), (37, 33), (41, 33), (49, 33), (97, 33), (63, 62), (126, 62), (67, 65), (69, 65), (73, 65), (81, 65), (97, 65), (95, 94), (126, 94), (3, 33), (3, 62), (3, 65), (3, 94), (5, 33), (5, 62), (5, 65), (5, 94), (9, 33), (9, 62), (9, 65), (9, 94), (17, 33), (17, 62), (17, 65), (17, 94), (96, 33), (96, 62), (96, 65), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94), (96, 94)]

def init11 : List Sig :=
  [(BitVec.ofNat 66 1073733567, BitVec.ofNat 66 5726621599),
   (BitVec.ofNat 66 258273, BitVec.ofNat 66 73786976289111584864),
   (BitVec.ofNat 66 3944802, BitVec.ofNat 66 73786976289111584864),
   (BitVec.ofNat 66 62927460, BitVec.ofNat 66 73786976289111584864),
   (BitVec.ofNat 66 1006646376, BitVec.ofNat 66 73786976289111584864),
   (BitVec.ofNat 66 73786976293764475007, BitVec.ofNat 66 3435970687),
   (BitVec.ofNat 66 73786976293764480976, BitVec.ofNat 66 73786976291402235776)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init11_eq :
    wiresToSigs (fun r => List.ofFn (pA prs11 r)) (fun r => List.ofFn (pB prs11 r)) 7 = init11 := by
  decide

theorem c11 : ∀ s11 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x11 : Fin 7 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 0 && x11 3) || (x11 0 && x11 4) || (x11 5 && x11 6)) s11 ↔ 6 ≤ s11 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x11 : Fin 7 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 0 && x11 3) || (x11 0 && x11 4) || (x11 5 && x11 6)) prs11 init11 init11_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 6 (by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs12 : List (ℕ × ℕ) :=
  [(19, 17), (21, 17), (25, 17), (49, 17), (81, 17), (31, 30), (62, 30), (94, 30), (99, 97), (101, 97), (105, 97), (113, 97), (111, 110), (126, 110), (3, 17), (3, 30), (3, 97), (3, 110), (5, 17), (5, 30), (5, 97), (5, 110), (9, 17), (9, 30), (9, 97), (9, 110), (48, 17), (48, 30), (48, 97), (48, 110), (80, 17), (80, 30), (80, 97), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110), (80, 110)]

def init12 : List Sig :=
  [(BitVec.ofNat 66 67100479, BitVec.ofNat 66 5726621471),
   (BitVec.ofNat 66 258529, BitVec.ofNat 66 73786976289111584992),
   (BitVec.ofNat 66 3945186, BitVec.ofNat 66 73786976289111584992),
   (BitVec.ofNat 66 62928100, BitVec.ofNat 66 73786976289111584992),
   (BitVec.ofNat 66 73786976294771108095, BitVec.ofNat 66 3435970815),
   (BitVec.ofNat 66 1006649160, BitVec.ofNat 66 73786976291402235648),
   (BitVec.ofNat 66 73786976293764480912, BitVec.ofNat 66 73786976291402235648)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init12_eq :
    wiresToSigs (fun r => List.ofFn (pA prs12 r)) (fun r => List.ofFn (pB prs12 r)) 7 = init12 := by
  decide

theorem c12 : ∀ s12 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x12 : Fin 7 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 0 && x12 3) || (x12 4 && x12 5) || (x12 4 && x12 6)) s12 ↔ 6 ≤ s12 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x12 : Fin 7 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 0 && x12 3) || (x12 4 && x12 5) || (x12 4 && x12 6)) prs12 init12 init12_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 6 (by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs13 : List (ℕ × ℕ) :=
  [(47, 46), (62, 46), (110, 46), (51, 49), (53, 49), (57, 49), (113, 49), (61, 60), (62, 60), (124, 60), (79, 78), (94, 78), (110, 78), (83, 81), (85, 81), (89, 81), (113, 81), (93, 92), (94, 92), (124, 92), (3, 46), (3, 49), (3, 60), (3, 78), (3, 81), (3, 92), (5, 46), (5, 49), (5, 60), (5, 78), (5, 81), (5, 92), (9, 46), (9, 49), (9, 60), (9, 78), (9, 81), (9, 92), (18, 46), (18, 49), (18, 60), (18, 78), (18, 81), (18, 92), (96, 46), (96, 49), (96, 60), (96, 78), (96, 81), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92), (96, 92)]

def init13 : List Sig :=
  [(BitVec.ofNat 66 274877113593, BitVec.ofNat 66 321685687492728),
   (BitVec.ofNat 66 17317374475535, BitVec.ofNat 66 160842843692039),
   (BitVec.ofNat 66 4228800407, BitVec.ofNat 66 73786654609150713735),
   (BitVec.ofNat 66 270583898023, BitVec.ofNat 66 73786654609150713735),
   (BitVec.ofNat 66 17317309180922, BitVec.ofNat 66 73786815451994514424),
   (BitVec.ofNat 66 73786958702652756991, BitVec.ofNat 66 125099989533695),
   (BitVec.ofNat 66 73786958702653210180, BitVec.ofNat 66 73786851194848672768)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init13_eq :
    wiresToSigs (fun r => List.ofFn (pA prs13 r)) (fun r => List.ofFn (pB prs13 r)) 7 = init13 := by
  decide

lemma s60_13 : search 6 0 init13 = false := by decide

theorem c13 : ∀ s13 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x13 : Fin 7 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 1 && x13 4) || (x13 5 && x13 6)) s13 ↔ 7 ≤ s13 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x13 : Fin 7 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 1 && x13 4) || (x13 5 && x13 6)) prs13 init13 init13_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 7 (by decide) (fun _ => s60_13) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs14 : List (ℕ × ℕ) :=
  [(39, 38), (46, 38), (54, 38), (102, 38), (45, 44), (46, 44), (60, 44), (108, 44), (51, 50), (54, 50), (58, 50), (114, 50), (59, 57), (61, 57), (121, 57), (71, 70), (78, 70), (86, 70), (102, 70), (77, 76), (78, 76), (92, 76), (108, 76), (83, 82), (86, 82), (90, 82), (114, 82), (91, 89), (93, 89), (121, 89), (3, 38), (3, 44), (3, 50), (3, 57), (3, 70), (3, 76), (3, 82), (3, 89), (5, 38), (5, 44), (5, 50), (5, 57), (5, 70), (5, 76), (5, 82), (5, 89), (10, 38), (10, 44), (10, 50), (10, 57), (10, 70), (10, 76), (10, 82), (10, 89), (20, 38), (20, 44), (20, 50), (20, 57), (20, 70), (20, 76), (20, 82), (20, 89), (96, 38), (96, 44), (96, 50), (96, 57)]

def init14 : List Sig :=
  [(BitVec.ofNat 66 70368618934545, BitVec.ofNat 66 39353054024280600576),
   (BitVec.ofNat 66 17944303831064367, BitVec.ofNat 66 24595658764714479375),
   (BitVec.ofNat 66 4593741714077754111, BitVec.ofNat 66 14757395258761249023),
   (BitVec.ofNat 66 17944030746342642, BitVec.ofNat 66 49191317530123727088),
   (BitVec.ofNat 66 4593671620985519940, BitVec.ofNat 66 59029581036076957440),
   (BitVec.ofNat 66 69175290277019287551, BitVec.ofNat 66 69446565924490477567),
   (BitVec.ofNat 66 69175290277484546184, BitVec.ofNat 66 4340410370347728896)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init14_eq :
    wiresToSigs (fun r => List.ofFn (pA prs14 r)) (fun r => List.ofFn (pB prs14 r)) 7 = init14 := by
  decide

lemma s60_14 : search 6 0 init14 = false := by decide

theorem c14 : ∀ s14 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x14 : Fin 7 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 1 && x14 3) || (x14 2 && x14 4) || (x14 5 && x14 6)) s14 ↔ 7 ≤ s14 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x14 : Fin 7 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 1 && x14 3) || (x14 2 && x14 4) || (x14 5 && x14 6)) prs14 init14 init14_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 7 (by decide) (fun _ => s60_14) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs15 : List (ℕ × ℕ) :=
  [(23, 22), (30, 22), (54, 22), (86, 22), (27, 25), (29, 25), (57, 25), (89, 25), (29, 28), (30, 28), (60, 28), (92, 28), (103, 102), (110, 102), (118, 102), (107, 105), (109, 105), (121, 105), (109, 108), (110, 108), (124, 108), (3, 22), (3, 25), (3, 28), (3, 102), (3, 105), (3, 108), (5, 22), (5, 25), (5, 28), (5, 102), (5, 105), (5, 108), (10, 22), (10, 25), (10, 28), (10, 102), (10, 105), (10, 108), (48, 22), (48, 25), (48, 28), (48, 102), (48, 105), (48, 108), (80, 22), (80, 25), (80, 28), (80, 102), (80, 105), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108), (80, 108)]

def init15 : List Sig :=
  [(BitVec.ofNat 66 8588333553, BitVec.ofNat 66 643371374969072),
   (BitVec.ofNat 66 541298586143, BitVec.ofNat 66 321685687398415),
   (BitVec.ofNat 66 8457649967, BitVec.ofNat 66 73786332923463237391),
   (BitVec.ofNat 66 541167955954, BitVec.ofNat 66 73786654609150808048),
   (BitVec.ofNat 66 73786975745083592703, BitVec.ofNat 66 250199979069439),
   (BitVec.ofNat 66 34634618369092, BitVec.ofNat 66 73786726094859137024),
   (BitVec.ofNat 66 73786941110468212872, BitVec.ofNat 66 73786726094859137024)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init15_eq :
    wiresToSigs (fun r => List.ofFn (pA prs15 r)) (fun r => List.ofFn (pB prs15 r)) 7 = init15 := by
  decide

lemma s60_15 : search 6 0 init15 = false := by decide

theorem c15 : ∀ s15 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x15 : Fin 7 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 4 && x15 5) || (x15 4 && x15 6)) s15 ↔ 7 ≤ s15 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x15 : Fin 7 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 4 && x15 5) || (x15 4 && x15 6)) prs15 init15 init15_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 7 (by decide) (fun _ => s60_15) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

def prs16 : List (ℕ × ℕ) :=
  [(43, 41), (45, 41), (57, 41), (105, 41), (47, 46), (62, 46), (110, 46), (51, 49), (53, 49), (57, 49), (113, 49), (55, 54), (62, 54), (118, 54), (75, 73), (77, 73), (89, 73), (105, 73), (79, 78), (94, 78), (110, 78), (83, 81), (85, 81), (89, 81), (113, 81), (87, 86), (94, 86), (118, 86), (3, 41), (3, 46), (3, 49), (3, 54), (3, 73), (3, 78), (3, 81), (3, 86), (5, 41), (5, 46), (5, 49), (5, 54), (5, 73), (5, 78), (5, 81), (5, 86), (24, 41), (24, 46), (24, 49), (24, 54), (24, 73), (24, 78), (24, 81), (24, 86), (96, 41), (96, 46), (96, 49), (96, 54), (96, 73), (96, 78), (96, 81), (96, 86), (96, 86), (96, 86), (96, 86), (96, 86), (96, 86), (96, 86)]

def init16 : List Sig :=
  [(BitVec.ofNat 66 17591983132575, BitVec.ofNat 66 384307168144508815),
   (BitVec.ofNat 66 68689885425, BitVec.ofNat 66 73402669126693697648),
   (BitVec.ofNat 66 17523707525490, BitVec.ofNat 66 73402669126693697648),
   (BitVec.ofNat 66 4486007518909055, BitVec.ofNat 66 230584300869763199),
   (BitVec.ofNat 66 4486007708270500, BitVec.ofNat 66 73556391993968443264),
   (BitVec.ofNat 66 73782472695363026943, BitVec.ofNat 66 67818912019922943),
   (BitVec.ofNat 66 73782472695479264328, BitVec.ofNat 66 73719157382818283520)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma init16_eq :
    wiresToSigs (fun r => List.ofFn (pA prs16 r)) (fun r => List.ofFn (pB prs16 r)) 7 = init16 := by
  decide

theorem c16 : ∀ s16 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x16 : Fin 7 → Bool => (x16 0 && x16 1) || (x16 0 && x16 2) || (x16 3 && x16 4) || (x16 5 && x16 6)) s16 ↔ 6 ≤ s16 := by
  intro s
  constructor
  · intro hC
    by_contra hn
    exact lower (fun x16 : Fin 7 → Bool => (x16 0 && x16 1) || (x16 0 && x16 2) || (x16 3 && x16 4) || (x16 5 && x16 6)) prs16 init16 init16_eq (by decide) (by decide) (by decide) (by decide)
      (by decide) 6 (by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (Nat.lt_of_not_le hn) hC
  · intro hs
    refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩, ?_, hs, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro x
      dsimp only
      rw [ofFn7 x]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> rfl

end PEqualNP.Outside.L_meta_902_aux

theorem PEqualNP.Outside.L_meta_902 : (∀ s1 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x1 : Fin 7 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 0 && x1 6)) s1 ↔ 6 ≤ s1) ∧ (∀ s2 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x2 : Fin 7 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 0 && x2 5) || (x2 1 && x2 6)) s2 ↔ 7 ≤ s2) ∧ (∀ s3 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x3 : Fin 7 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 1 && x3 3) || (x3 1 && x3 4) || (x3 1 && x3 5) || (x3 2 && x3 6)) s3 ↔ 7 ≤ s3) ∧ (∀ s4 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x4 : Fin 7 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 0 && x4 4) || (x4 1 && x4 5) || (x4 1 && x4 6)) s4 ↔ 7 ≤ s4) ∧ (∀ s5 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x5 : Fin 7 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 0 && x5 3) || (x5 0 && x5 4) || (x5 1 && x5 5) || (x5 2 && x5 6)) s5 ↔ 8 ≤ s5) ∧ (∀ s6 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x6 : Fin 7 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 1 && x6 3) || (x6 1 && x6 4) || (x6 2 && x6 5) || (x6 2 && x6 6)) s6 ↔ 7 ≤ s6) ∧ (∀ s7 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x7 : Fin 7 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 1 && x7 3) || (x7 1 && x7 4) || (x7 2 && x7 5) || (x7 5 && x7 6)) s7 ↔ 8 ≤ s7) ∧ (∀ s8 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x8 : Fin 7 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 0 && x8 3) || (x8 1 && x8 4) || (x8 2 && x8 5) || (x8 4 && x8 6)) s8 ↔ 8 ≤ s8) ∧ (∀ s9 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x9 : Fin 7 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 1 && x9 4) || (x9 1 && x9 5) || (x9 2 && x9 6)) s9 ↔ 8 ≤ s9) ∧ (∀ s10 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x10 : Fin 7 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 0 && x10 3) || (x10 1 && x10 4) || (x10 2 && x10 5) || (x10 3 && x10 6)) s10 ↔ 8 ≤ s10) ∧ (∀ s11 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x11 : Fin 7 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 0 && x11 3) || (x11 0 && x11 4) || (x11 5 && x11 6)) s11 ↔ 6 ≤ s11) ∧ (∀ s12 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x12 : Fin 7 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 0 && x12 3) || (x12 4 && x12 5) || (x12 4 && x12 6)) s12 ↔ 6 ≤ s12) ∧ (∀ s13 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x13 : Fin 7 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 1 && x13 4) || (x13 5 && x13 6)) s13 ↔ 7 ≤ s13) ∧ (∀ s14 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x14 : Fin 7 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 1 && x14 3) || (x14 2 && x14 4) || (x14 5 && x14 6)) s14 ↔ 7 ≤ s14) ∧ (∀ s15 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x15 : Fin 7 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 4 && x15 5) || (x15 4 && x15 6)) s15 ↔ 7 ≤ s15) ∧ (∀ s16 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x16 : Fin 7 → Bool => (x16 0 && x16 1) || (x16 0 && x16 2) || (x16 3 && x16 4) || (x16 5 && x16 6)) s16 ↔ 6 ≤ s16) :=
  ⟨PEqualNP.Outside.L_meta_902_aux.c1, PEqualNP.Outside.L_meta_902_aux.c2, PEqualNP.Outside.L_meta_902_aux.c3, PEqualNP.Outside.L_meta_902_aux.c4, PEqualNP.Outside.L_meta_902_aux.c5, PEqualNP.Outside.L_meta_902_aux.c6, PEqualNP.Outside.L_meta_902_aux.c7, PEqualNP.Outside.L_meta_902_aux.c8, PEqualNP.Outside.L_meta_902_aux.c9, PEqualNP.Outside.L_meta_902_aux.c10, PEqualNP.Outside.L_meta_902_aux.c11, PEqualNP.Outside.L_meta_902_aux.c12, PEqualNP.Outside.L_meta_902_aux.c13, PEqualNP.Outside.L_meta_902_aux.c14, PEqualNP.Outside.L_meta_902_aux.c15, PEqualNP.Outside.L_meta_902_aux.c16⟩
