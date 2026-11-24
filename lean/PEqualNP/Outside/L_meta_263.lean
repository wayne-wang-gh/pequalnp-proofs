import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_263

private abbrev Budget := Fin 5 → ℕ
private abbrev Table := BitVec 32
private abbrev Bounds := Table × Table

private noncomputable def reads (φ : DMFormula 5) (i : Fin 5) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun j _ => if j = i then 1 else 0)
    (fun _ _ a b => a + b) (fun _ _ a b => a + b) φ

private lemma leaves_eq (φ : DMFormula 5) : φ.leaves = ∑ i, reads φ i := by
  induction φ with
  | lit i b => simp [DMFormula.leaves, reads]
  | and a b ha hb => simp [DMFormula.leaves, reads, ← Finset.sum_add_distrib, ha, hb]
  | or a b ha hb => simp [DMFormula.leaves, reads, ← Finset.sum_add_distrib, ha, hb]

private lemma leaves_pos (φ : DMFormula 5) : 0 < φ.leaves := by
  induction φ <;> simp [DMFormula.leaves, *]

private def indices : List (Fin 5) := [0, 1, 2, 3, 4]

private lemma mem_indices (i : Fin 5) : i ∈ indices := by
  fin_cases i <;> decide

private def live (o : Budget) : Bool := indices.any (fun i => o i != 0)

private lemma live_of_reads {φ : DMFormula 5} {o : Budget}
    (h : ∀ i, reads φ i ≤ o i) : live o = true := by
  by_contra he
  have hz (i : Fin 5) : o i = 0 := by
    by_contra hi
    exact he (List.any_eq_true.mpr ⟨i, mem_indices i, by simpa⟩)
  have hreads (i : Fin 5) : reads φ i = 0 := by
    exact Nat.eq_zero_of_le_zero (hz i ▸ h i)
  have hp := leaves_pos φ
  rw [leaves_eq] at hp
  simp [hreads] at hp

private def splits (o : Budget) : List (Budget × Budget) := do
  let a ← List.range (o 0 + 1)
  let b ← List.range (o 1 + 1)
  let c ← List.range (o 2 + 1)
  let d ← List.range (o 3 + 1)
  let e ← List.range (o 4 + 1)
  let p : Budget := ![a, b, c, d, e]
  pure (p, fun i => o i - p i)

private lemma mem_splits {p o : Budget} (h : ∀ i, p i ≤ o i) :
    (p, fun i => o i - p i) ∈ splits o := by
  unfold splits
  simp only [List.bind_eq_flatMap, List.pure_def, List.mem_flatMap, List.mem_range,
    List.mem_singleton, Nat.lt_succ_iff]
  have hp : (![p 0, p 1, p 2, p 3, p 4] : Budget) = p := by
    funext i
    fin_cases i <;> rfl
  exact ⟨p 0, h 0, p 1, h 1, p 2, h 2, p 3, h 3, p 4, h 4, by rw [hp]⟩

private def mask : Fin 5 → Table :=
  ![0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

private def literal (i : Fin 5) (s : Bool) : Table := if s then mask i else ~~~(mask i)

private def table : DMFormula 5 → Table
  | .lit i s => literal i s
  | .and p q => table p &&& table q
  | .or p q => table p ||| table q

private def input (a : Fin 32) (i : Fin 5) : Bool := (mask i).getLsbD a

private lemma table_eval (φ : DMFormula 5) (a : Fin 32) :
    (table φ).getLsbD a = φ.eval (input a) := by
  induction φ with
  | lit i s => cases s <;> simp [table, literal, DMFormula.eval, input, a.isLt]
  | and p q hp hq => simp only [table, DMFormula.eval, BitVec.getLsbD_and, hp, hq]
  | or p q hp hq => simp only [table, DMFormula.eval, BitVec.getLsbD_or, hp, hq]

private def flipped (i : Fin 5) (a : Fin 32) : Fin 32 := Fin.ofNat 32 (a.val ^^^ (2 ^ i.val))

private lemma flip_input : ∀ (i j : Fin 5) (a : Fin 32), i ≠ j →
    input (flipped i a) j = input a j := by decide +kernel

private lemma flip_eval (φ : DMFormula 5) (i : Fin 5) (h : reads φ i = 0) (a : Fin 32) :
    φ.eval (input (flipped i a)) = φ.eval (input a) := by
  induction φ with
  | lit j s =>
    have hij : i ≠ j := by rintro rfl; simp [reads] at h
    simp [DMFormula.eval, flip_input i j a hij]
  | and p q hp hq =>
    simp only [reads, Nat.add_eq_zero_iff] at h
    simp [DMFormula.eval, hp h.1, hq h.2]
  | or p q hp hq =>
    simp only [reads, Nat.add_eq_zero_iff] at h
    simp [DMFormula.eval, hp h.1, hq h.2]

private def flip (i : Fin 5) (t : Table) : Table :=
  let d := 2 ^ i.val
  ((t &&& mask i) >>> d) ||| ((t &&& ~~~(mask i)) <<< d)

private lemma flip_facts : ∀ (i : Fin 5) (a : Fin 32),
    let d := 2 ^ i.val
    let left := !decide (a.val < d) && (~~~(mask i)).getLsbD (a.val - d)
    let right := (mask i).getLsbD (d + a.val)
    if input a i then
      left = true ∧ right = false ∧ a.val - d = (flipped i a).val
    else
      left = false ∧ right = true ∧ d + a.val = (flipped i a).val := by decide +kernel

private lemma flip_bit (i : Fin 5) (t : Table) (a : Fin 32) :
    (flip i t).getLsbD a = t.getLsbD (flipped i a) := by
  simp only [flip, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, a.isLt, decide_true, Bool.true_and]
  have h := flip_facts i a
  cases hi : input a i <;> simp only [hi, Bool.false_eq_true, ite_false, ite_true] at h <;>
    obtain ⟨hl, hr, he⟩ := h <;>
    simp only [hr, Bool.and_true, Bool.and_false, Bool.false_or]
  · rw [Bool.and_left_comm, hl, Bool.and_false, Bool.or_false, he]
  · rw [Bool.and_left_comm, hl, Bool.and_true, he]

private def Sub (l r : Table) : Prop :=
  ∀ a : Fin 32, l.getLsbD a ≤ r.getLsbD a

private def fits (l r : Table) : Bool := l &&& r == l

private lemma fits_iff (l r : Table) : fits l r = true ↔ Sub l r := by
  simp only [fits, beq_iff_eq]
  constructor
  · intro h a
    have hb := congrArg (fun (t : Table) => t.getLsbD a) h
    simp only [BitVec.getLsbD_and] at hb
    exact Bool.le_iff_imp.mpr (Bool.and_eq_left_iff_imp.mp hb)
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hb := h ⟨i, hi⟩
    change l.getLsbD i ≤ r.getLsbD i at hb
    simp only [BitVec.getLsbD_and]
    exact Bool.and_eq_left_iff_imp.mpr (Bool.le_iff_imp.mp hb)

private def Inside (v : Table) (b : Bounds) : Prop := Sub b.1 v ∧ Sub v b.2

private lemma fits_of_inside {v : Table} {b : Bounds} (h : Inside v b) :
    fits b.1 b.2 = true :=
  (fits_iff _ _).mpr (fun a => (h.1 a).trans (h.2 a))

private def empty : Bounds := (~~~0, 0)

private lemma not_inside_empty (v : Table) : ¬ Inside v empty := by
  intro h
  have hf := fits_of_inside h
  change fits (~~~0) 0 = true at hf
  exact (by decide : fits (~~~0) 0 ≠ true) hf

private def merge (x y : Bounds) : Bounds := (x.1 &&& y.1, x.2 ||| y.2)

private lemma inside_merge {v : Table} {x y : Bounds} (h : Inside v x ∨ Inside v y) :
    Inside v (merge x y) := by
  rcases h with h | h <;> constructor <;> intro a <;>
    have hl := h.1 a <;> have hu := h.2 a <;>
    simp only [merge, BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.le_iff_imp,
      Bool.and_eq_true, Bool.or_eq_true] at * <;> tauto

private lemma inside_fold {α : Type} {v : Table} (f : α → Bounds) (l : List α)
    (x : Bounds) (h : Inside v x ∨ ∃ a ∈ l, Inside v (f a)) :
    Inside v (l.foldl (fun b a => merge b (f a)) x) := by
  induction l generalizing x with
  | nil => simpa using h
  | cons a l ih =>
    apply ih
    rcases h with hx | ⟨d, hd, hf⟩
    · exact .inl (inside_merge (.inl hx))
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact .inl (inside_merge (.inr hf))
      · exact .inr ⟨d, hd, hf⟩

private def project (o : Budget) (b : Bounds) : Bounds :=
  indices.foldl (fun (q : Bounds) i =>
    if o i = 0 then (q.1 ||| flip i q.1, q.2 &&& flip i q.2) else q) b

private lemma inside_project {φ : DMFormula 5} {o : Budget} (ho : ∀ i, reads φ i ≤ o i)
    {b : Bounds} (h : Inside (table φ) b) : Inside (table φ) (project o b) := by
  unfold project
  generalize indices = l
  induction l generalizing b with
  | nil => exact h
  | cons i l ih =>
    apply ih
    dsimp only
    split_ifs with hz
    · have hzero : reads φ i = 0 := by have := ho i; omega
      have he (a : Fin 32) :
          (table φ).getLsbD (flipped i a) = (table φ).getLsbD a := by
        rw [table_eval, table_eval, flip_eval φ i hzero]
      constructor <;> intro a
      · have h₀ := h.1 a
        have h₁ := h.1 (flipped i a)
        rw [he a] at h₁
        simp only [BitVec.getLsbD_or, flip_bit, Bool.le_iff_imp, Bool.or_eq_true] at *
        tauto
      · have h₀ := h.2 a
        have h₁ := h.2 (flipped i a)
        rw [he a] at h₁
        simp only [BitVec.getLsbD_and, flip_bit, Bool.le_iff_imp, Bool.and_eq_true] at *
        tauto
    · exact h

private lemma bit_not (t : Table) (a : Fin 32) :
    (~~~t).getLsbD a = !(t.getLsbD a) := by
  simp only [BitVec.getLsbD_not, a.isLt, decide_true, Bool.true_and]

private lemma bottom (t : Table) : Sub 0 t := by
  intro a
  simp [Bool.le_iff_imp]

private lemma top (t : Table) : Sub t (~~~0) := by
  intro a
  have hz : (0 : Table).getLsbD a = false := BitVec.getLsbD_zero
  rw [bit_not, hz]
  exact Bool.le_iff_imp.mpr (fun _ => rfl)

private def clip (b c : Bounds) : Bounds :=
  let d : Bounds := (b.1 ||| c.1, b.2 &&& c.2)
  if fits d.1 d.2 then d else empty

private lemma inside_clip {v : Table} {b c : Bounds} (hb : Inside v b) (hc : Inside v c) :
    Inside v (clip b c) := by
  have h : Inside v (b.1 ||| c.1, b.2 &&& c.2) := by
    constructor <;> intro a
    · have h₁ := hb.1 a
      have h₂ := hc.1 a
      simp only [BitVec.getLsbD_or, Bool.le_iff_imp, Bool.or_eq_true] at *
      tauto
    · have h₁ := hb.2 a
      have h₂ := hc.2 a
      simp only [BitVec.getLsbD_and, Bool.le_iff_imp, Bool.and_eq_true] at *
      tauto
  simpa only [clip, fits_of_inside h, ite_true] using h

private def gate (isOr : Bool) (search : Budget → Bounds → Bounds) (b : Bounds)
    (o₁ o₂ : Budget) : Bounds :=
  if isOr then
    let u₁ := (project o₁ (0, b.2)).2
    let u₂ := (project o₂ (0, b.2)).2
    if fits b.1 (u₁ ||| u₂) then
      let p := search o₁ (b.1 &&& ~~~u₂, u₁)
      if fits p.1 p.2 then
        let q := search o₂ (b.1 &&& ~~~p.2, u₂)
        if fits q.1 q.2 then clip b (p.1 ||| q.1, p.2 ||| q.2) else empty
      else empty
    else empty
  else
    let l₁ := (project o₁ (b.1, ~~~0)).1
    let l₂ := (project o₂ (b.1, ~~~0)).1
    if fits (l₁ &&& l₂) b.2 then
      let p := search o₁ (l₁, b.2 ||| ~~~l₂)
      if fits p.1 p.2 then
        let q := search o₂ (l₂, b.2 ||| ~~~p.1)
        if fits q.1 q.2 then clip b (p.1 &&& q.1, p.2 &&& q.2) else empty
      else empty
    else empty

-- Each child's bounds constrain the assignments the other child must cover.
private lemma gate_or_sound {p q : DMFormula 5} {o₁ o₂ : Budget} {b : Bounds}
    {search : Budget → Bounds → Bounds}
    (hp : ∀ i, reads p i ≤ o₁ i) (hq : ∀ i, reads q i ≤ o₂ i)
    (sp : ∀ c, Inside (table p) c → Inside (table p) (search o₁ c))
    (sq : ∀ c, Inside (table q) c → Inside (table q) (search o₂ c))
    (h : Inside (table p ||| table q) b) :
    Inside (table p ||| table q) (gate true search b o₁ o₂) := by
  let u₁ := (project o₁ (0, b.2)).2
  let u₂ := (project o₂ (0, b.2)).2
  have up : Sub (table p) u₁ := (inside_project hp (b := (0, b.2))
    ⟨bottom _, fun a => by
      have hh := h.2 a
      simp only [BitVec.getLsbD_or, Bool.le_iff_imp, Bool.or_eq_true] at *
      tauto⟩).2
  have uq : Sub (table q) u₂ := (inside_project hq (b := (0, b.2))
    ⟨bottom _, fun a => by
      have hh := h.2 a
      simp only [BitVec.getLsbD_or, Bool.le_iff_imp, Bool.or_eq_true] at *
      tauto⟩).2
  have hf : fits b.1 (u₁ ||| u₂) = true := (fits_iff _ _).2 (fun a => by
    have hh := h.1 a
    have hp := up a
    have hq := uq a
    simp only [BitVec.getLsbD_or, Bool.le_iff_imp, Bool.or_eq_true] at *
    tauto)
  let r := search o₁ (b.1 &&& ~~~u₂, u₁)
  have hr : Inside (table p) r := sp _ ⟨fun a => by
    have hh := h.1 a
    have hq := uq a
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, bit_not, Bool.le_iff_imp,
      Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff] at *
    tauto, up⟩
  let s := search o₂ (b.1 &&& ~~~r.2, u₂)
  have hs : Inside (table q) s := sq _ ⟨fun a => by
    have hh := h.1 a
    have hp := hr.2 a
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, bit_not, Bool.le_iff_imp,
      Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff] at *
    tauto, uq⟩
  have hc : Inside (table p ||| table q) (r.1 ||| s.1, r.2 ||| s.2) := by
    constructor <;> intro a
    · have hp := hr.1 a
      have hq := hs.1 a
      simp only [BitVec.getLsbD_or, Bool.le_iff_imp, Bool.or_eq_true] at *
      tauto
    · have hp := hr.2 a
      have hq := hs.2 a
      simp only [BitVec.getLsbD_or, Bool.le_iff_imp, Bool.or_eq_true] at *
      tauto
  unfold gate
  simp only [ite_true]
  change Inside (table p ||| table q)
    (if fits b.1 (u₁ ||| u₂) then
      if fits r.1 r.2 then
        if fits s.1 s.2 then clip b (r.1 ||| s.1, r.2 ||| s.2) else empty
      else empty
    else empty)
  simpa only [hf, fits_of_inside hr, fits_of_inside hs, ite_true] using inside_clip h hc

private lemma gate_and_sound {p q : DMFormula 5} {o₁ o₂ : Budget} {b : Bounds}
    {search : Budget → Bounds → Bounds}
    (hp : ∀ i, reads p i ≤ o₁ i) (hq : ∀ i, reads q i ≤ o₂ i)
    (sp : ∀ c, Inside (table p) c → Inside (table p) (search o₁ c))
    (sq : ∀ c, Inside (table q) c → Inside (table q) (search o₂ c))
    (h : Inside (table p &&& table q) b) :
    Inside (table p &&& table q) (gate false search b o₁ o₂) := by
  let l₁ := (project o₁ (b.1, ~~~0)).1
  let l₂ := (project o₂ (b.1, ~~~0)).1
  have lp : Sub l₁ (table p) := (inside_project hp (b := (b.1, ~~~0))
    ⟨fun a => by
      have hh := h.1 a
      simp only [BitVec.getLsbD_and, Bool.le_iff_imp, Bool.and_eq_true] at *
      tauto, top _⟩).1
  have lq : Sub l₂ (table q) := (inside_project hq (b := (b.1, ~~~0))
    ⟨fun a => by
      have hh := h.1 a
      simp only [BitVec.getLsbD_and, Bool.le_iff_imp, Bool.and_eq_true] at *
      tauto, top _⟩).1
  have hf : fits (l₁ &&& l₂) b.2 = true := (fits_iff _ _).2 (fun a => by
    have hh := h.2 a
    have hp := lp a
    have hq := lq a
    simp only [BitVec.getLsbD_and, Bool.le_iff_imp, Bool.and_eq_true] at *
    tauto)
  let r := search o₁ (l₁, b.2 ||| ~~~l₂)
  have hr : Inside (table p) r := sp _ ⟨lp, fun a => by
    have hh := h.2 a
    have hq := lq a
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, bit_not, Bool.le_iff_imp,
      Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff] at *
    tauto⟩
  let s := search o₂ (l₂, b.2 ||| ~~~r.1)
  have hs : Inside (table q) s := sq _ ⟨lq, fun a => by
    have hh := h.2 a
    have hp := hr.1 a
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, bit_not, Bool.le_iff_imp,
      Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff] at *
    tauto⟩
  have hc : Inside (table p &&& table q) (r.1 &&& s.1, r.2 &&& s.2) := by
    constructor <;> intro a
    · have hp := hr.1 a
      have hq := hs.1 a
      simp only [BitVec.getLsbD_and, Bool.le_iff_imp, Bool.and_eq_true] at *
      tauto
    · have hp := hr.2 a
      have hq := hs.2 a
      simp only [BitVec.getLsbD_and, Bool.le_iff_imp, Bool.and_eq_true] at *
      tauto
  unfold gate
  simp only [Bool.false_eq_true, ite_false]
  change Inside (table p &&& table q)
    (if fits (l₁ &&& l₂) b.2 then
      if fits r.1 r.2 then
        if fits s.1 s.2 then clip b (r.1 &&& s.1, r.2 &&& s.2) else empty
      else empty
    else empty)
  simpa only [hf, fits_of_inside hr, fits_of_inside hs, ite_true] using inside_clip h hc

private def leafBounds (o : Budget) (b : Bounds) (i : Fin 5) : Bounds :=
  if o i = 0 then empty else
    merge (clip b (literal i true, literal i true))
      (clip b (literal i false, literal i false))

private def splitBounds (search : Budget → Bounds → Bounds) (b : Bounds)
    (o : Budget × Budget) : Bounds :=
  if live o.1 && live o.2 then
    merge (gate false search b o.1 o.2) (gate true search b o.1 o.2)
  else empty

private def search : ℕ → Budget → Bounds → Bounds
  | 0, _, _ => empty
  | n + 1, o, b =>
    if fits b.1 b.2 then
      let leaves := indices.foldl (fun c i => merge c (leafBounds o b i)) empty
      (splits o).foldl (fun c part => merge c (splitBounds (search n) b part)) leaves
    else empty

private lemma search_sound : ∀ (n : ℕ) (φ : DMFormula 5) (o : Budget) (b : Bounds),
    φ.leaves ≤ n → (∀ i, reads φ i ≤ o i) → Inside (table φ) b →
    Inside (table φ) (search n o b) := by
  intro n
  induction n with
  | zero =>
    intro φ _ _ hn
    exact (Nat.not_lt_of_ge hn (leaves_pos φ)).elim
  | succ n ih =>
    intro φ o b hn ho h
    simp only [search, fits_of_inside h, ite_true]
    have split (p q : DMFormula 5) (g : Bool)
        (hn : p.leaves + q.leaves ≤ n + 1) (ho : ∀ i, reads p i + reads q i ≤ o i)
        (h : Inside (if g then table p ||| table q else table p &&& table q) b) :
        ∃ part ∈ splits o,
          Inside (if g then table p ||| table q else table p &&& table q)
            (splitBounds (search n) b part) := by
      let o₁ := reads p
      let o₂ : Budget := fun i => o i - o₁ i
      have hp (i : Fin 5) : reads p i ≤ o₁ i := le_rfl
      have hq (i : Fin 5) : reads q i ≤ o₂ i := by
        have := ho i
        dsimp [o₂, o₁]
        omega
      refine ⟨(o₁, o₂), mem_splits (fun i => by have := ho i; change reads p i ≤ o i; omega), ?_⟩
      simp only [splitBounds, live_of_reads hp, live_of_reads hq, Bool.and_self, ite_true]
      have sp := ih p o₁
      have sq := ih q o₂
      have hn₁ : p.leaves ≤ n := by have := leaves_pos q; omega
      have hn₂ : q.leaves ≤ n := by have := leaves_pos p; omega
      apply inside_merge
      cases g
      · exact .inl (gate_and_sound hp hq (fun c => sp c hn₁ hp) (fun c => sq c hn₂ hq) h)
      · exact .inr (gate_or_sound hp hq (fun c => sp c hn₁ hp) (fun c => sq c hn₂ hq) h)
    apply inside_fold
    cases φ with
    | lit i s =>
      left
      apply inside_fold
      right
      refine ⟨i, mem_indices i, ?_⟩
      have hi : o i ≠ 0 := by
        have := ho i
        simp [reads] at this
        omega
      simp only [leafBounds, hi, ite_false, table]
      have hc : Inside (literal i s) (literal i s, literal i s) :=
        ⟨fun _ => le_rfl, fun _ => le_rfl⟩
      apply inside_merge
      cases s
      · exact .inr (inside_clip h hc)
      · exact .inl (inside_clip h hc)
    | and p q => exact .inr (split p q false hn ho h)
    | or p q => exact .inr (split p q true hn ho h)

private def butterfly : Table := 0xffeaeae8

private lemma butterfly_bit : ∀ a : Fin 32,
    butterfly.getLsbD a =
      (input a 0 && input a 1 || input a 0 && input a 2 || input a 1 && input a 2 ||
        input a 0 && input a 3 || input a 0 && input a 4 || input a 3 && input a 4) := by
  decide +kernel

private def budget (a b : Fin 4) : Budget := ![2, a.val, 3 - a.val, b.val, 3 - b.val]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private lemma reject_budget (a b : Fin 4) :
    search 8 (budget a b) (butterfly, butterfly) = empty := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private lemma lower (φ : DMFormula 5)
    (he : ∀ x, φ.eval x =
      (x 0 && x 1 || x 0 && x 2 || x 1 && x 2 || x 0 && x 3 || x 0 && x 4 || x 3 && x 4))
    (h₁ : reads φ 1 + reads φ 2 = 3) (h₂ : reads φ 3 + reads φ 4 = 3) :
    3 ≤ reads φ 0 := by
  by_contra h
  have hl : φ.leaves ≤ 8 := by
    rw [leaves_eq, Fin.sum_univ_five]
    omega
  let a : Fin 4 := ⟨reads φ 1, by omega⟩
  let b : Fin 4 := ⟨reads φ 3, by omega⟩
  have ho (i : Fin 5) : reads φ i ≤ budget a b i := by
    fin_cases i <;> dsimp [budget, a, b] <;> omega
  have ht (i : Fin 32) : (table φ).getLsbD i = butterfly.getLsbD i := by
    rw [table_eval, he, butterfly_bit]
  have hi : Inside (table φ) (butterfly, butterfly) :=
    ⟨fun i => (ht i).symm.le, fun i => (ht i).le⟩
  have hh := search_sound 8 φ _ _ hl ho hi
  rw [reject_budget] at hh
  exact not_inside_empty _ hh

end PEqualNP.Outside.L_meta_263

theorem PEqualNP.Outside.L_meta_263 : ∀ φ : PEqualNP.MetaComplexity.DMFormula 5, (∀ x : Fin 5 → Bool, φ.eval x = (x 0 && x 1 || x 0 && x 2 || x 1 && x 2 || x 0 && x 3 || x 0 && x 4 || x 3 && x 4)) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 1 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ + PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 2 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 3 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 3 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ + PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 4 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 3 → 3 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 0 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ := by
  exact PEqualNP.Outside.L_meta_263.lower
