import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_1037

abbrev Word := BitVec 32

def bit (q : Fin 32) (v : Word) : Bool := v[q.val]

def wordOp : GateOp → List Word → Word
  | .and, l => l.foldr (· &&& ·) (BitVec.allOnes 32)
  | .or, l => l.foldr (· ||| ·) 0
  | .not, l => ~~~(l.headD 0)
  | _, _ => 0

def value (env : List Word) (g : Gate) : Word :=
  wordOp g.op (g.inputs.map fun a => env.getD a 0)

def generated : List Word → List Gate → List Word
  | _, [] => []
  | env, g :: gs => let w := value env g; w :: generated (env ++ [w]) gs

def legal (g : Gate) : Prop := g.op = .and ∨ g.op = .or ∨ g.op = .not

lemma bitWordOp (q : Fin 32) (op : GateOp) (l : List Word)
    (h : op = .and ∨ op = .or ∨ op = .not) :
    bit q (wordOp op l) = op.eval (l.map (bit q)) := by
  rcases h with rfl | rfl | rfl
  · induction l with
    | nil => exact BitVec.getElem_allOnes _ q.isLt
    | cons x xs ih =>
      simpa [wordOp, bit, GateOp.eval, Bool.and_comm] using congrArg (fun t => bit q x && t) ih
  · induction l with
    | nil => simp [wordOp, bit, GateOp.eval]
    | cons x xs ih =>
      simpa [wordOp, bit, GateOp.eval, Bool.or_comm] using congrArg (fun t => bit q x || t) ih
  · cases l with
    | nil => exact BitVec.getElem_allOnes _ q.isLt
    | cons a l => simp [wordOp, bit, GateOp.eval]

lemma readBit (q : Fin 32) (env : List Word) (a : ℕ) :
    (env.map (bit q)).getD a false = bit q (env.getD a 0) := by
  simpa [bit] using (List.getD_map env (0 : Word) (n := a) (bit q))

lemma simulate (q : Fin 32) (env : List Word) (gs : List Gate)
    (h : ∀ g ∈ gs, legal g) :
    (env ++ generated env gs).map (bit q) =
      gs.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])
        (env.map (bit q)) := by
  induction gs generalizing env with
  | nil => simp [generated]
  | cons g gs ih =>
    have hstep : bit q (value env g) = g.op.eval (g.inputs.map fun a =>
        (env.map (bit q)).getD a false) := by
      rw [value, bitWordOp q _ _ (h g (by simp))]
      simp only [List.map_map, Function.comp_def, readBit]
    simpa [generated, List.append_assoc, hstep] using
      ih (env ++ [value env g]) (fun a ha => h a (by simp [ha]))

lemma observe (q : Fin 32) (env : List Word) (gs : List Gate) (h : ∀ g ∈ gs, legal g)
    (j : ℕ) :
    bit q ((env ++ generated env gs).getD j 0) =
      Circuit.eval ⟨gs,j⟩ (env.map (bit q)) := by
  rw [← readBit, simulate q env gs h]
  rfl

lemma generatedLength (env : List Word) (gs : List Gate) :
    (generated env gs).length = gs.length := by
  induction gs generalizing env with
  | nil => rfl
  | cons g gs ih => simp [generated, ih]


-- Each word stores one wire on all thirty-two input assignments.
def inputWords : List Word := [2863311530, 3435973836, 4042322160, 4278255360, 4294901760]
-- The circuit uses the complement of the three-of-five threshold once.
def candidate : List Gate := [
  ⟨.or, [0, 3]⟩,
  ⟨.and, [0, 3]⟩,
  ⟨.or, [5, 1]⟩,
  ⟨.and, [5, 1]⟩,
  ⟨.or, [6, 8]⟩,
  ⟨.and, [6, 1]⟩,
  ⟨.and, [7, 2]⟩,
  ⟨.or, [9, 11]⟩,
  ⟨.and, [9, 2]⟩,
  ⟨.or, [10, 13]⟩,
  ⟨.and, [12, 4]⟩,
  ⟨.or, [14, 15]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [17, 1]⟩,
  ⟨.or, [4, 0]⟩,
  ⟨.or, [19, 2]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.or, [21, 2]⟩,
  ⟨.or, [4, 1]⟩,
  ⟨.and, [20, 7]⟩,
  ⟨.and, [24, 22]⟩,
  ⟨.and, [25, 23]⟩,
  ⟨.and, [26, 18]⟩,
  ⟨.and, [2, 0]⟩,
  ⟨.and, [28, 1]⟩,
  ⟨.and, [3, 2]⟩,
  ⟨.and, [30, 1]⟩,
  ⟨.and, [0, 1]⟩,
  ⟨.and, [32, 4]⟩,
  ⟨.and, [4, 2]⟩,
  ⟨.and, [34, 0]⟩,
  ⟨.and, [34, 1]⟩,
  ⟨.and, [6, 4]⟩,
  ⟨.and, [3, 4]⟩,
  ⟨.and, [38, 1]⟩,
  ⟨.or, [29, 33]⟩,
  ⟨.or, [40, 37]⟩,
  ⟨.or, [41, 36]⟩,
  ⟨.or, [42, 35]⟩,
  ⟨.or, [43, 31]⟩,
  ⟨.or, [44, 39]⟩,
  ⟨.not, [16]⟩,
  ⟨.and, [27, 46]⟩,
  ⟨.or, [47, 45]⟩]
def outputs : List ℕ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 48]
def required : List Word := [4289396650, 2852170240, 4293853166, 3431517320, 4001951368, 2281736192, 4041273568, 4276682472, 3766542464, 3900762240, 4276617216, 4276676736, 4210752250, 4278124286, 4294945450, 4294966010, 4294967040, 4294967280, 4294954188, 4293851882, 4293851872, 4293839040, 4277061824, 2694881440, 2155905152, 4026593280, 3221274624, 2290649224, 2290614272, 4042260480, 2694840320, 3233808384, 2852126720, 4278190080, 3422552064, 2290647168, 2861072512, 3939008640, 3941105792, 3941122176, 4008231040, 4008624320]
def tables : List Word := [2863311530, 3435973836, 4042322160, 4278255360, 4294901760, 4289396650, 2852170240, 4293853166, 3431517320, 4001951368, 2281736192, 4041273568, 4276682472, 3766542464, 3900762240, 4276617216, 4276676736, 4210752250, 4278124286, 4294945450, 4294966010, 4294967040, 4294967280, 4294954188, 4293851882, 4293851872, 4293839040, 4277061824, 2694881440, 2155905152, 4026593280, 3221274624, 2290649224, 2290614272, 4042260480, 2694840320, 3233808384, 2852126720, 4278190080, 3422552064, 2290647168, 2861072512, 3939008640, 3941105792, 3941122176, 4008231040, 18290559, 393280, 4008624320]
def distinguished : Word := 4008624320
-- Restricting to six input assignments suffices for the last output.
def testMask : Word := 268830816
def basis : List Word := [0, 32, 2048, 133152, 264256, 268435456, 268435552, 268437504, 268437600, 268568608, 268568672, 268828672, 268830720, 268830752, 268830784, 268830816]
def thresholdIndex : ℕ := 16
def negIndex : Fin candidate.length := ⟨41, by decide⟩

def isNot : GateOp → Bool
  | .not => true
  | _ => false

def valid : GateOp → Bool
  | .and | .or | .not => true
  | _ => false

lemma candidateLegal : ∀ g ∈ candidate, legal g ∧ g.inputs.length ≤ 2 := by
  have certified : candidate.all (fun g => valid g.op && decide (g.inputs.length ≤ 2)) = true := by decide +kernel
  intro g hg
  have hh := List.all_eq_true.mp certified g hg
  rcases Bool.and_eq_true_iff.mp hh with ⟨ha,hb⟩
  refine ⟨?_, of_decide_eq_true hb⟩
  unfold legal
  cases e : g.op <;> simp_all [valid]

def sample (q : Fin 32) (i : Fin 5) : Bool := bit q (inputWords.getD i.val 0)
def output (j : Fin 42) : ℕ := outputs.getD j.val 0
def specification (j : Fin 42) (x : Fin 5 → Bool) : Bool :=
  Circuit.eval ⟨candidate, output j⟩ (List.ofFn x)

lemma sampleList (q : Fin 32) : List.ofFn (sample q) = inputWords.map (bit q) := by
  revert q
  decide +kernel

lemma covers (x : Fin 5 → Bool) : ∃ q : Fin 32, sample q = x := by
  revert x
  decide +kernel

lemma tableCheck : inputWords ++ generated inputWords candidate = tables := by decide +kernel

lemma outputCheck (j : Fin 42) : tables.getD (output j) 0 = required.getD j.val 0 := by
  revert j
  decide +kernel

lemma onSample (q : Fin 32) (j : Fin 42) :
    specification j (sample q) = bit q (required.getD j.val 0) := by
  rw [specification, sampleList, ← observe q _ _ (fun g hg => (candidateLegal g hg).1),
      tableCheck, outputCheck]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma sampleMono : ∀ (v : Word), v ∈ required → ∀ (q r : Fin 32),
    (∀ i : Fin 5, sample q i ≤ sample r i) → bit q v ≤ bit r v := by
  have checked : required.all (fun v => decide (∀ q r : Fin 32,
      (∀ i : Fin 5, sample q i ≤ sample r i) → bit q v ≤ bit r v)) = true := by decide +kernel
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp checked v hv)

lemma specMono (j : Fin 42) (x y : Fin 5 → Bool) (h : ∀ i, x i ≤ y i) :
    specification j x ≤ specification j y := by
  obtain ⟨q,rfl⟩ := covers x
  obtain ⟨r,rfl⟩ := covers y
  rw [onSample, onSample]
  have hm : required.getD j.val 0 ∈ required := by revert j; decide
  exact sampleMono _ hm q r h

lemma negAt (i : Fin candidate.length) (h : (candidate.get i).op = .not) : i = negIndex := by
  have hc : ∀ t : Fin candidate.length, isNot (candidate.get t).op = true → t = negIndex := by decide +kernel
  exact hc i (by rw [h]; rfl)

lemma atThreshold (x : Fin 5 → Bool) :
    (Circuit.wires ⟨candidate,0⟩ (List.ofFn x)).getD thresholdIndex false =
      decide (3 ≤ (Finset.univ.filter (fun i : Fin 5 => x i = true)).card) := by
  obtain ⟨q,rfl⟩ := covers x
  change Circuit.eval ⟨candidate,thresholdIndex⟩ (List.ofFn (sample q)) = _
  rw [sampleList, ← observe q _ _ (fun g hg => (candidateLegal g hg).1), tableCheck]
  revert q
  decide +kernel

def project (w : Word) : Word := w &&& testMask

lemma projectAnd (a b : Word) : project (a &&& b) = project a &&& project b := by
  apply BitVec.eq_of_getElem_eq
  intro i h
  simp only [project, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases testMask[i] <;> rfl

lemma projectOr (a b : Word) : project (a ||| b) = project a ||| project b := by
  apply BitVec.eq_of_getElem_eq
  intro i h
  simp only [project, BitVec.getElem_and, BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> cases testMask[i] <;> rfl

def choices (s : List Word) : List Word :=
  (s ++ s.flatMap (fun a => s.flatMap (fun b => [a &&& b, a ||| b]))).eraseDups

lemma choiceOld {s : List Word} {a : Word} (ha : a ∈ s) : a ∈ choices s := by
  simp [choices, ha]

lemma choiceAnd {s : List Word} {a b : Word} (ha : a ∈ s) (hb : b ∈ s) :
    a &&& b ∈ choices s := by
  simp only [choices, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    List.mem_cons, List.mem_nil_iff, or_false]
  exact Or.inr ⟨a, ha, b, hb, Or.inl rfl⟩

lemma choiceOr {s : List Word} {a b : Word} (ha : a ∈ s) (hb : b ∈ s) :
    a ||| b ∈ choices s := by
  simp only [choices, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    List.mem_cons, List.mem_nil_iff, or_false]
  exact Or.inr ⟨a, ha, b, hb, Or.inr rfl⟩

lemma getD_cases (env : List Word) (j : ℕ) : env.getD j 0 ∈ env ∨ env.getD j 0 = 0 := by
  by_cases h : j < env.length
  · left; rw [List.getD_eq_getElem env _ h]; exact List.getElem_mem ..
  · right; exact List.getD_eq_default env _ (Nat.le_of_not_gt h)

def pureGate (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

lemma wordOrZero (x : Word) : x ||| (0 : Word) = x := BitVec.or_zero

lemma choiceGate (env pool : List Word) (hbase : ∀ a ∈ basis, a ∈ pool)
    (he : ∀ a ∈ env, project a ∈ pool) (g : Gate) (hg : pureGate g) :
    project (value env g) ∈ choices pool := by
  have hz : project 0 ∈ pool := hbase _ (by decide)
  have ho : project (BitVec.allOnes 32) ∈ pool := hbase _ (by decide)
  have read (i : ℕ) : project (env.getD i 0) ∈ pool := by
    rcases getD_cases env i with h | h
    · exact he _ h
    · simpa only [h] using hz
  obtain ⟨op, args⟩ := g
  rcases hg with ⟨hop,hlen⟩
  change args.length ≤ 2 at hlen
  change op = .and ∨ op = .or at hop
  rcases hop with rfl | rfl <;> cases args with
  | nil => first | exact choiceOld ho | exact choiceOld hz
  | cons i rest =>
    cases rest with
    | nil =>
      simpa only [value, wordOp, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, BitVec.and_allOnes, wordOrZero] using choiceOld (read i)
    | cons j tail =>
      cases tail with
      | nil =>
        first
        | simpa only [value, wordOp, List.map_cons, List.map_nil, List.foldr_cons,
            List.foldr_nil, BitVec.and_allOnes, projectAnd] using choiceAnd (read i) (read j)
        | simpa only [value, wordOp, List.map_cons, List.map_nil, List.foldr_cons,
            List.foldr_nil, wordOrZero, projectOr] using choiceOr (read i) (read j)
      | cons y ys => simp at hlen

def noNext (s : List Word) : Bool :=
  !(s.contains (project distinguished)) && s.all (fun a => s.all (fun b =>
    decide (a &&& b ≠ project distinguished ∧ a ||| b ≠ project distinguished)))

lemma noNextSound (s : List Word) (ok : noNext s = true) :
    project distinguished ∉ choices s := by
  have hc := Bool.and_eq_true_iff.mp ok
  intro hm
  simp only [choices, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with hold | ⟨a,ha,b,hb,hab⟩
  · have hnot : project distinguished ∉ s := by simpa using hc.1
    exact hnot hold
  · have both : a &&& b ≠ project distinguished ∧ a ||| b ≠ project distinguished :=
      of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hc.2 a ha) b hb)
    rcases hab with he | he
    · exact both.1 he.symm
    · exact both.2 he.symm

-- Allow all required outputs except the distinguished one as free wires.
-- Each unit of fuel allows one additional wire before checking the next gate.
def safe : ℕ → List Word → Bool
  | 0, s => noNext s
  | t+1, s => noNext s &&
      (choices s).all (fun v => safe t (v :: s))

lemma safeAvoid {t : ℕ} {s : List Word} (hs : safe t s = true) :
    project distinguished ∉ choices s := by
  cases t with
  | zero => exact noNextSound s hs
  | succ t =>
    have h := (Bool.and_eq_true_iff.mp hs).1
    exact noNextSound s h

lemma safeNext {t : ℕ} {s : List Word} {v : Word}
    (hs : safe (t+1) s = true) (hv : v ∈ choices s) : safe t (v::s) = true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp hs).2 v hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma startSafe : safe 2 basis = true := by decide +kernel

def outside (l : List Word) : ℕ := (l.filter (fun w => !(required.contains w))).length

lemma inBasis (w : Word) (hw : w ∈ required) (hne : w ≠ distinguished) :
    project w ∈ basis := by
  have h : required.all (fun a => decide (a ≠ distinguished → project a ∈ basis)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h _ hw) hne

lemma cannotGenerate (gs : List Gate) (env pool : List Word) (t : ℕ)
    (hs : safe t pool = true) (hb : ∀ a ∈ basis, a ∈ pool)
    (he : ∀ a ∈ env, project a ∈ pool)
    (hp : ∀ g ∈ gs, pureGate g) (hn : outside (generated env gs) ≤ t) :
    distinguished ∉ generated env gs := by
  induction gs generalizing env pool t with
  | nil => simp [generated]
  | cons g gs ih =>
    let w := value env g
    have hw : project w ∈ choices pool := choiceGate _ _ hb he _ (hp g (by simp))
    have hne : w ≠ distinguished := fun e => safeAvoid hs (e ▸ hw)
    have hp' : ∀ a ∈ gs, pureGate a := fun a ha => hp a (by simp [ha])
    change distinguished ∉ w :: generated (env ++ [w]) gs
    simp only [List.mem_cons, not_or]
    refine ⟨Ne.symm hne, ?_⟩
    by_cases hr : w ∈ required
    · refine ih (env ++ [w]) pool t hs hb ?_ hp' ?_
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact he _ ha
        · have eq : a = w := by simpa using ha
          rw [eq]
          exact hb _ (inBasis _ hr hne)
      · simpa [generated, outside, ← show w = value env g from rfl, hr] using hn
    · have bound : outside (generated (env ++ [w]) gs) + 1 ≤ t := by
        simpa [generated, outside, ← show w = value env g from rfl, hr] using hn
      cases t with
      | zero => omega
      | succ t =>
        apply ih (env ++ [w]) (project w :: pool) t (safeNext hs hw) _ _ hp' (by omega)
        · exact fun a ha => List.mem_cons_of_mem _ (hb _ ha)
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact List.mem_cons_of_mem _ (he _ ha)
          · have eq : a = w := by simpa using ha
            simp [eq]

lemma countOutside (l : List Word) : outside l +
    (l.filter (fun w => required.contains w)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    unfold outside at *
    by_cases ha : a ∈ required <;> simp [ha] at * <;> omega

-- Forty-two distinct noninput outputs already require forty-two gate positions.
-- In a circuit of size at most forty-four only two other positions are available.
lemma lowerBound (gs : List Gate) (out : Fin 42 → ℕ)
    (hp : ∀ g ∈ gs, pureGate g)
    (hc : ∀ j x, Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = specification j x) :
    candidate.length < gs.length := by
  by_contra! hlen
  let made := generated inputWords gs
  have hlegal : ∀ g ∈ gs, legal g := by
    intro g hg
    rcases (hp g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hreq (w : Word) (hw : w ∈ required) : w ∈ made := by
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hw
    let j : Fin 42 := ⟨i, hi⟩
    have hwj : required.getD j.val 0 = w := by
      rw [List.getD_eq_getElem required 0 hi]
      exact eq
    have table : (inputWords ++ made).getD (out j) 0 = w := by
      apply BitVec.eq_of_getElem_eq
      intro pos hpos
      let q : Fin 32 := ⟨pos,hpos⟩
      change bit q _ = bit q w
      calc
        _ = Circuit.eval ⟨gs,out j⟩ (inputWords.map (bit q)) := observe q inputWords gs hlegal _
        _ = specification j (sample q) := by rw [← sampleList, hc]
        _ = bit q w := by rw [onSample, hwj]
    have clean : required.all (fun a => decide (a ∉ inputWords ∧ a ≠ 0)) = true := by decide
    have disj : w ∉ inputWords ∧ w ≠ 0 := of_decide_eq_true (List.all_eq_true.mp clean w hw)
    rcases getD_cases (inputWords ++ made) (out j) with hm | hz
    · rw [table, List.mem_append] at hm
      exact hm.resolve_left disj.1
    · exact (disj.2 (table.symm.trans hz)).elim
  have hs : required.toFinset ⊆ (made.filter (fun w => required.contains w)).toFinset := by
    intro w hw
    have hw' := List.mem_toFinset.mp hw
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hreq w hw', by simpa using hw'⟩)
  have cardinal := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  have hc42 : required.toFinset.card = 42 := by decide
  have hc44 : candidate.length = 44 := by decide
  have split := countOutside made
  have hsize : made.length = gs.length := generatedLength inputWords gs
  have budget : outside made ≤ 2 := by omega
  have initial : ∀ a ∈ inputWords, project a ∈ basis := by
    have cert : inputWords.all (fun w => decide (project w ∈ basis)) = true := by decide
    exact fun a ha => of_decide_eq_true (List.all_eq_true.mp cert a ha)
  exact cannotGenerate gs inputWords basis 2 startSafe (fun _ h => h) initial hp budget
    (hreq distinguished (by decide))

end PEqualNP.Outside.L_meta_1037

open PEqualNP.Outside.L_meta_1037

theorem PEqualNP.Outside.L_meta_1037 : ∃ (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool), n ≤ 6 ∧ (∀ (j : Fin m) (x y : Fin n → Bool), (∀ i : Fin n, x i ≤ y i) → f j x ≤ f j y) ∧ ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out j⟩ (List.ofFn x) = f j x) ∧ (∀ t : Fin gates.length, (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ a k : ℕ, (gates.get t).inputs.head? = some a ∧ ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD a false = decide (k ≤ (Finset.univ.filter (fun i : Fin n => x i = true)).card)) ∧ ∀ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' j⟩ (List.ofFn x) = f j x) → gates.length < gates'.length := by
  refine ⟨5, 42, specification, by decide, specMono, candidate, output, candidateLegal, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj
    exact (negAt i hi).trans (negAt j hj).symm
  · exact fun _ _ => rfl
  · intro t ht
    obtain rfl := negAt t ht
    exact ⟨thresholdIndex, 3, by decide, atThreshold⟩
  · exact lowerBound
