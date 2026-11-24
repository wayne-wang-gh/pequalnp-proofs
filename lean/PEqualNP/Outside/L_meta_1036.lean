import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1036
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first twenty outputs are distinct signals in a sorting circuit on five inputs.
-- The last output tests for at least two true values among the four inputs other than input two.
-- A positive circuit with at most twenty-three gates has room for only two other gate values.
abbrev Sig := BitVec 32
def Makes (xs : List Sig) (v : Sig) : Prop :=
  ∃ a ∈ xs, ∃ b ∈ xs, v = (a &&& b) ∨ v = (a ||| b)

def Built : List Sig → List Sig → Prop
  | _, [] => True
  | xs, t :: ts => Makes xs t ∧ Built (t :: xs) ts

def baseSignals : List Sig := [0, 4294967295, 2863311530, 3435973836, 4042322160, 4278255360, 4294901760, 4293984240, 4026593280, 4294770684, 3435187392, 4240506048, 3221274624, 4294967292, 4294705152, 4294769856, 4240441344, 4240490496, 3221225472, 4294967294, 2863311528, 4294901480, 2863179904, 4276676736, 2826993664, 3900735488, 2147483648]
def targetSig : Sig := 4293848712
def requiredSigs : List Sig := [4293984240, 4026593280, 4294770684, 3435187392, 4240506048, 3221274624, 4294967292, 4294705152, 4294769856, 4240441344, 4240490496, 3221225472, 4294967294, 2863311528, 4294901480, 2863179904, 4276676736, 2826993664, 3900735488, 2147483648, 4293848712]

def encode5 (x : Fin 5 → Bool) : ℕ :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
  (if x 3 then 8 else 0) + (if x 4 then 16 else 0)

def family (j : Fin 21) (x : Fin 5 → Bool) : Bool :=
  (requiredSigs.getD j.val 0).getLsbD (encode5 x)


-- The sampled evaluator below adapts sanchan's proof of L-meta-607 in PR 741.
private abbrev Table := BitVec 32
private def sample (j : Fin 32) (i : Fin 5) : Bool :=
  j.val.testBit i.val

private def readTable (j : Fin 32) (t : Table) : Bool := t.getLsbD j.val
private theorem read_zero (j : Fin 32) : readTable j 0 = false := BitVec.getLsbD_zero
private theorem read_not (j : Fin 32) (t : Table) : readTable j (~~~t) = !(readTable j t) := by
  simp [readTable, j.isLt]
private def inputs : List Table := [2863311530, 3435973836, 4042322160, 4278255360, 4294901760]
private theorem inputTables (j : Fin 32) : List.ofFn (sample j) = inputs.map (readTable j) := by
  fin_cases j <;> decide
private theorem table_ext (a b : Table) (h : ∀ j, readTable j a = readTable j b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  exact fun i hi => h ⟨i,hi⟩

private theorem getD_table (x : Fin 32) (ws : List Table) (i : ℕ) :
    (ws.map (readTable x)).getD i false = readTable x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [readTable]

private def gateTable (ws : List Table) (g : Gate) : Table :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(ws.getD i 0)
  | _, _ => 0

private theorem read_gateTable (x : Fin 32) (ws : List Table) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (readTable x)).getD i false) =
      readTable x (gateTable ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_table]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateTable, GateOp.eval, readTable]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | cons i is =>
      exact (read_not x (ws.getD i 0)).symm
  | mod m => simp at hop
  | maj => simp at hop

private def wireTables (gs : List Gate) (ws : List Table) : List Table :=
  gs.foldl (fun vs g => vs ++ [gateTable vs g]) ws

private theorem read_wireTables (x : Fin 32) (gs : List Gate) (ws : List Table)
    (h : FanInTwo ⟨gs, 0⟩) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (readTable x))) = (wireTables gs ws).map (readTable x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := read_gateTable x ws g (h g List.mem_cons_self)
    change Circuit.wires ⟨gs, 0⟩
        (ws.map (readTable x) ++ [g.op.eval (g.inputs.map fun i =>
          (ws.map (readTable x)).getD i false)]) =
      (wireTables gs (ws ++ [gateTable ws g])).map (readTable x)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

private theorem wires_match (C : Circuit) (h : FanInTwo C) (j : Fin 32) (o : ℕ) :
    (C.wires (List.ofFn (sample j))).getD o false =
    readTable j ((wireTables C.gates inputs).getD o 0) := by
  change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn (sample j))).getD o false = _
  rw [inputTables, read_wireTables j C.gates inputs h, getD_table]


private def outputsFrom : List Gate → List Table → List Table
  | [], _ => []
  | g :: gs, ws => gateTable ws g :: outputsFrom gs (ws ++ [gateTable ws g])

private lemma outputs_length (gs : List Gate) (ws : List Table) :
    (outputsFrom gs ws).length = gs.length := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => simp [outputsFrom, ih]

private lemma outputs_append (gs : List Gate) (ws : List Table) :
    wireTables gs ws = ws ++ outputsFrom gs ws := by
  induction gs generalizing ws with
  | nil => simp [wireTables, outputsFrom]
  | cons g gs ih =>
    change wireTables gs (ws ++ [gateTable ws g]) = ws ++ gateTable ws g :: _
    rw [ih]
    simp

private lemma makes_self {xs : List Sig} {v : Sig} (hv : v ∈ xs) : Makes xs v :=
  ⟨v, hv, v, hv, Or.inl (by simp)⟩

private lemma getD_avail (ws env : List Table) (i : ℕ) (z : 0 ∈ env)
    (hw : ∀ v ∈ ws, v ∈ env) : ws.getD i 0 ∈ env := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hw _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact z

private lemma made_gate (ws env : List Table) (g : Gate) (h : g.op = .and ∨ g.op = .or)
    (z : 0 ∈ env) (one : (~~~(0 : Table)) ∈ env) (hw : ∀ v ∈ ws, v ∈ env) :
    Makes env (gateTable ws g) := by
  obtain ⟨op, ins⟩ := g
  rcases h with h | h <;> change op = _ at h <;> subst op
  · cases ins with
    | nil => exact makes_self one
    | cons i is =>
      cases is with
      | nil => exact makes_self (getD_avail _ _ _ z hw)
      | cons j _ => exact ⟨_, getD_avail _ _ i z hw, _, getD_avail _ _ j z hw, Or.inl rfl⟩
  · cases ins with
    | nil => exact makes_self z
    | cons i is =>
      cases is with
      | nil => exact makes_self (getD_avail _ _ _ z hw)
      | cons j _ => exact ⟨_, getD_avail _ _ i z hw, _, getD_avail _ _ j z hw, Or.inr rfl⟩

private lemma built_outputs (gs : List Gate) (ws env : List Table)
    (hp : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (z : 0 ∈ env) (one : (~~~(0 : Table)) ∈ env) (hw : ∀ v ∈ ws, v ∈ env) :
    Built env (outputsFrom gs ws) := by
  induction gs generalizing ws env with
  | nil => trivial
  | cons g gs ih =>
    let t := gateTable ws g
    refine ⟨made_gate ws env g (hp g List.mem_cons_self) z one hw, ?_⟩
    apply ih (ws ++ [t]) (t :: env) (fun g' hg' => hp g' (List.mem_cons_of_mem _ hg'))
      (List.mem_cons_of_mem _ z) (List.mem_cons_of_mem _ one)
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_cons_of_mem _ (hw v h)
    · have he : v = t := by simpa using h
      exact List.mem_cons.mpr (Or.inl he)

private lemma family_sample (j : Fin 21) (r : Fin 32) :
    family j (sample r) = readTable r (requiredSigs.getD j.val 0) := by
  have he : ∀ r : Fin 32, encode5 (sample r) = r.val := by decide +kernel
  simp only [family, he, readTable]

private lemma required_index (v : Sig) (hv : v ∈ requiredSigs.toFinset) :
    ∃ j : Fin 21, requiredSigs.getD j.val 0 = v := by
  obtain ⟨i, hi, eq⟩ := List.getElem_of_mem (List.mem_toFinset.mp hv)
  have len : requiredSigs.length = 21 := by decide
  exact ⟨⟨i, by omega⟩, (List.getD_eq_getElem _ _ hi).trans eq⟩

private lemma required_in_outputs (gs : List Gate) (out : Fin 21 → ℕ)
    (hp : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (he : ∀ j x, Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = family j x) :
    ∀ v ∈ requiredSigs.toFinset, v ∈ outputsFrom gs inputs := by
  intro v hv
  obtain ⟨j, rfl⟩ := required_index v hv
  have hh : FanInTwo ⟨gs, 0⟩ := by
    intro g hg
    obtain ⟨ha | ho, hl⟩ := hp g hg
    · exact ⟨Or.inl ha, hl⟩
    · exact ⟨Or.inr (Or.inl ho), hl⟩
  have hval : (wireTables gs inputs).getD (out j) 0 = requiredSigs.getD j.val 0 :=
    table_ext _ _ (fun r => (wires_match ⟨gs, 0⟩ hh r (out j)).symm.trans ((he j (sample r)).trans (family_sample j r)))
  have bounds : ∀ j : Fin 21, requiredSigs.getD j.val 0 ≠ 0 ∧ requiredSigs.getD j.val 0 ∉ inputs := by decide +kernel
  have hi : out j < (wireTables gs inputs).length := by
    by_contra! hh'
    rw [List.getD_eq_default _ _ hh'] at hval
    exact (bounds j).1 hval.symm
  rw [List.getD_eq_getElem _ _ hi] at hval
  have hm : requiredSigs.getD j.val 0 ∈ wireTables gs inputs := hval ▸ List.getElem_mem hi
  rw [outputs_append] at hm
  exact (List.mem_append.mp hm).resolve_left (bounds j).2

private lemma ready_trace (gs : List Gate) (hp : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Built baseSignals (outputsFrom gs inputs) := by
  apply built_outputs gs inputs baseSignals (fun g hg => (hp g hg).1) (by decide) (by decide)
  intro v hv
  have sub : inputs ⊆ baseSignals := by decide
  exact sub hv



lemma two_other_gates {α : Type*} [DecidableEq α] (vals : List α) (required : Finset α)
    (hcard : required.card = 21) (hmem : ∀ v ∈ required, v ∈ vals)
    (hlen : vals.length ≤ 23) :
    (vals.filter (fun v => decide (v ∉ required))).length ≤ 2 := by
  have hsub : required ⊆ (vals.filter (fun v => decide (v ∈ required))).toFinset := by
    intro v hv
    apply List.mem_toFinset.mpr
    exact List.mem_filter.mpr ⟨hmem v hv, by simp [hv]⟩
  have hinside := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  have htotal := List.length_eq_length_filter_add (l := vals) (fun v => decide (v ∈ required))
  have hneg : (fun v => !(decide (v ∈ required))) = (fun v => decide (v ∉ required)) := by
    funext v
    by_cases h : v ∈ required <;> simp [h]
  rw [hneg] at htotal
  omega


private theorem trace_makes_weaken {xs ys : List Sig} {v : Sig}
    (h : ∀ z ∈ xs, z ∈ ys) (hv : Makes xs v) : Makes ys v := by
  obtain ⟨a, ha, b, hb, he⟩ := hv
  exact ⟨a, h a ha, b, h b hb, he⟩

private theorem trace_prefix {vals src xs : List Sig} {R : Finset Sig} {t : Sig}
    (hb : Built src vals) (hm : t ∈ vals) (hs : ∀ z ∈ src, z ∈ xs)
    (hr : ∀ v ∈ R, v ≠ t → v ∈ xs) :
    ∃ ws : List Sig, ws.length ≤ (vals.filter (fun v => decide (v ∉ R))).length ∧
      Built xs ws ∧ Makes (ws.reverse ++ xs) t := by
  induction vals generalizing src xs with
  | nil => simp at hm
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := hb
    have hmake := trace_makes_weaken hs hv
    by_cases he : v = t
    · subst v
      exact ⟨[], Nat.zero_le _, trivial, by simpa using hmake⟩
    have hm' : t ∈ vs := (List.mem_cons.mp hm).resolve_left (Ne.symm he)
    by_cases hR : v ∈ R
    · have havev := hr v hR he
      have hsrc : ∀ z ∈ v :: src, z ∈ xs := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact havev
        · exact hs _ hz
      obtain ⟨ws, hw, hbuilt, hfinal⟩ := ih hvs hm' hsrc hr
      exact ⟨ws, by simpa [hR] using hw, hbuilt, hfinal⟩
    · have hsrc : ∀ z ∈ v :: src, z ∈ v :: xs := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs _ hz)
      have hR' : ∀ z ∈ R, z ≠ t → z ∈ v :: xs :=
        fun z hz he' => List.mem_cons_of_mem _ (hr z hz he')
      obtain ⟨ws, hw, hbuilt, hfinal⟩ := ih hvs hm' hsrc hR'
      exact ⟨v :: ws, by simpa [hR] using Nat.succ_le_succ hw, ⟨hmake, hbuilt⟩,
        by simpa [List.reverse_cons, List.append_assoc] using hfinal⟩

theorem trace_three {xs vals : List Sig} {R : Finset Sig} {t : Sig}
    (hb : Built xs vals) (hmem : t ∈ vals) (hr : ∀ v ∈ R, v ≠ t → v ∈ xs)
    (hc : (vals.filter (fun v => decide (v ∉ R))).length ≤ 2)
    (h0 : 0 ∈ xs) :
    ∃ a b, Makes xs a ∧ Makes (a :: xs) b ∧ Makes (b :: a :: xs) t := by
  obtain ⟨ws, hl, hbuilt, hfinal⟩ := trace_prefix hb hmem (fun _ h => h) hr
  have hle := hl.trans hc
  have hz : Makes xs 0 := ⟨0, h0, 0, h0, Or.inl (by decide)⟩
  cases ws with
  | nil =>
    simp only [List.reverse_nil, List.nil_append] at hfinal
    refine ⟨0, 0, hz, trace_makes_weaken (fun _ h => List.mem_cons_of_mem _ h) hz, ?_⟩
    exact trace_makes_weaken (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) hfinal
  | cons a ws =>
    cases ws with
    | nil =>
      obtain ⟨ha, _⟩ := hbuilt
      have hm : Makes (a :: xs) t := by simpa using hfinal
      exact ⟨a, 0, ha, trace_makes_weaken (fun _ h => List.mem_cons_of_mem _ h) hz,
        trace_makes_weaken (fun _ h => List.mem_cons_of_mem _ h) hm⟩
    | cons b ws =>
      cases ws with
      | nil =>
        obtain ⟨ha, hb, _⟩ := hbuilt
        exact ⟨a, b, ha, hb, by simpa using hfinal⟩
      | cons c ws => simp at hle

def upperGates : List Gate := [
  ⟨GateOp.or, [2, 3]⟩,
  ⟨GateOp.and, [2, 3]⟩,
  ⟨GateOp.or, [5, 1]⟩,
  ⟨GateOp.and, [5, 1]⟩,
  ⟨GateOp.or, [6, 8]⟩,
  ⟨GateOp.and, [6, 8]⟩,
  ⟨GateOp.or, [7, 4]⟩,
  ⟨GateOp.and, [7, 4]⟩,
  ⟨GateOp.or, [9, 12]⟩,
  ⟨GateOp.and, [9, 12]⟩,
  ⟨GateOp.or, [10, 14]⟩,
  ⟨GateOp.and, [10, 14]⟩,
  ⟨GateOp.or, [11, 0]⟩,
  ⟨GateOp.and, [11, 0]⟩,
  ⟨GateOp.or, [13, 18]⟩,
  ⟨GateOp.and, [13, 18]⟩,
  ⟨GateOp.or, [15, 20]⟩,
  ⟨GateOp.and, [15, 20]⟩,
  ⟨GateOp.or, [16, 22]⟩,
  ⟨GateOp.and, [16, 22]⟩,
  ⟨GateOp.not, [2]⟩,
  ⟨GateOp.and, [19, 25]⟩,
  ⟨GateOp.or, [21, 26]⟩]

def upperOut (j : Fin 21) : ℕ := if j.val < 20 then 5+j.val else 27

lemma upShape (x : Fin 5 → Bool) : x = ![x 0, x 1, x 2, x 3, x 4] := by
  funext i
  fin_cases i <;> rfl

lemma upList (x : Fin 5 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
  simp [List.ofFn_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma upMonoTest : ∀ a b c d e A B C D E : Bool,
    (a ≤ A ∧ b ≤ B ∧ c ≤ C ∧ d ≤ D ∧ e ≤ E) →
    ∀ j : Fin 21, family j ![a,b,c,d,e] ≤ family j ![A,B,C,D,E] := by
  decide +kernel

lemma family_mono : ∀ (j : Fin 21) (x y : Fin 5 → Bool),
    (∀ i : Fin 5, x i ≤ y i) → family j x ≤ family j y := by
  intro j x y h
  have hm := upMonoTest (x 0) (x 1) (x 2) (x 3) (x 4) (y 0) (y 1) (y 2) (y 3) (y 4)
    ⟨h 0, h 1, h 2, h 3, h 4⟩ j
  rw [← upShape x, ← upShape y] at hm
  exact hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma upEval : ∀ a b c d e : Bool, ∀ j : Fin 21,
    Circuit.eval ⟨upperGates, upperOut j⟩ [a,b,c,d,e] = family j ![a,b,c,d,e] := by
  decide +kernel

def upIsNot : GateOp → Bool
  | .not => true
  | _ => false

lemma upNotIndex : ∀ i : Fin upperGates.length,
    upIsNot (upperGates.get i).op = true ↔ i.val = 20 := by decide +kernel

theorem upper_data : ∃ (gs : List Gate) (out : Fin 21 → ℕ), gs.length = 23 ∧
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
    (∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) ∧
    (∀ (j : Fin 21) (x : Fin 5 → Bool), Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = family j x) := by
  refine ⟨upperGates, upperOut, rfl, ?_, ?_, ?_⟩
  · intro g hg
    simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · intro i j hi hj
    have pi := (upNotIndex i).1 (by rw [hi]; rfl)
    have pj := (upNotIndex j).1 (by rw [hj]; rfl)
    exact Fin.ext (pi.trans pj.symm)
  · intro j x
    have hv := upEval (x 0) (x 1) (x 2) (x 3) (x 4) j
    rw [← upShape x] at hv
    rw [upList]
    exact hv


private lemma positive_lower (no3 : ∀ {a b : Sig}, Makes baseSignals a →
    Makes (a :: baseSignals) b → ¬ Makes (b :: a :: baseSignals) targetSig)
    (gs : List Gate) (out : Fin 21 → ℕ)
    (hp : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (he : ∀ j x, Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = family j x) :
    23 < gs.length := by
  by_contra! hsmall
  let vals := outputsFrom gs inputs
  let R := requiredSigs.toFinset
  have req : ∀ v ∈ R, v ∈ vals := required_in_outputs _ _ hp he
  have hc := two_other_gates vals R (by decide) req (by simpa [vals, outputs_length] using hsmall)
  have inside : ∀ v ∈ R, v ≠ targetSig → v ∈ baseSignals := by
    intro v hv hne
    obtain ⟨j, rfl⟩ := required_index v hv
    have cert : ∀ j : Fin 21, requiredSigs.getD j.val 0 ≠ targetSig →
        requiredSigs.getD j.val 0 ∈ baseSignals := by decide +kernel
    exact cert j hne
  obtain ⟨a,b,ha,hb,ht⟩ := trace_three (ready_trace gs hp) (req targetSig (by decide))
    inside hc (by decide)
  exact no3 ha hb ht

private def certFirst : List Sig := [0, 2147483648, 2147516416, 2290122752, 2290124928, 2290649216, 2290649224, 2684387328, 2684395520, 2692775936, 2694881408, 2694881440, 2818605056, 2826960896, 2826993664, 2827004032, 2852169728, 2852170240, 2862655616, 2862656160, 2863136768, 2863179904, 2863180456, 2863267840, 2863311528, 2863311530, 3221225472, 3221258240, 3221274624, 3233857728, 3363864576, 3422604288, 3435134976, 3435184128, 3435186304, 3435187392, 3435710592, 3435921408, 3435973824, 3435973832, 3435973836, 3758129152, 3766517760, 3892346880, 3900702720, 3900735488, 3900751872, 3936921728, 3936938112, 3937053352, 3937053354, 3937069736, 3937069738, 3972058304, 3972844748, 4008242368, 4008373992, 4008373994, 4008504524, 4008636140, 4008636142, 4026531840, 4026580992, 4026589184, 4026593280, 4039114752, 4039163904, 4039176384, 4041269376, 4042260480, 4042322112, 4042322144, 4042322160, 4169199616, 4176539888, 4205377664, 4205509288, 4205509290, 4210620656, 4210752248, 4210752250, 4227858432, 4227907584, 4227922944, 4240441344, 4240474112, 4240490496, 4240493760, 4240500864, 4240502784, 4240506048, 4241280204, 4241292492, 4243648752, 4243651824, 4244438268, 4261472256, 4276152448, 4276617216, 4276660352, 4276676736, 4276677824, 4276680832, 4276681920, 4276791976, 4276791978, 4276808360, 4276808362, 4276813544, 4276813546, 4276939980, 4277729520, 4278190080, 4278254592, 4278255104, 4278255360, 4286643968, 4289265536, 4289396648, 4289396650, 4290838272, 4290838464, 4291624908, 4293459840, 4293918720, 4293983424, 4293983968, 4293984240, 4294508528, 4294639608, 4294639610, 4294705152, 4294737920, 4294748288, 4294754304, 4294757568, 4294757580, 4294764672, 4294766592, 4294766832, 4294769856, 4294769868, 4294769904, 4294770408, 4294770432, 4294770624, 4294770672, 4294770684, 4294836224, 4294879912, 4294879914, 4294901480, 4294901482, 4294901484, 4294901496, 4294901736, 4294901752, 4294901756, 4294901758, 4294901760, 4294934528, 4294944896, 4294945448, 4294945450, 4294950912, 4294954176, 4294954188, 4294961280, 4294963200, 4294963440, 4294966464, 4294967016, 4294967040, 4294967280, 4294967292, 4294967294, 4294967295]

private abbrev certSeparate (x y : Sig) : Prop :=
  targetSig ≠ (x &&& y) ∧ targetSig ≠ (x ||| y)

private abbrev certSafe (xs : List Sig) (b : Sig) : Prop :=
  targetSig ≠ b ∧ ∀ y ∈ xs, certSeparate b y

private def certGood (xs : List Sig) (b : Sig) : Bool :=
  decide (targetSig ≠ b) &&
    ((if b &&& targetSig = targetSig then xs.all (fun y => decide (targetSig ≠ (b &&& y))) else true) &&
     (if b ||| targetSig = targetSig then xs.all (fun y => decide (targetSig ≠ (b ||| y))) else true))

private theorem certGood_sound {xs : List Sig} {b : Sig} (h : certGood xs b = true) : certSafe xs b := by
  have hh : targetSig ≠ b ∧
      ((b &&& targetSig = targetSig) → ∀ y ∈ xs, targetSig ≠ (b &&& y)) ∧
      ((b ||| targetSig = targetSig) → ∀ y ∈ xs, targetSig ≠ (b ||| y)) := by
    by_cases h1 : b &&& targetSig = targetSig <;> by_cases h2 : b ||| targetSig = targetSig <;>
      simpa [certGood, h1, h2] using h
  refine ⟨hh.1, ?_⟩
  intro y hy
  constructor
  · intro e
    exact hh.2.1 (by rw [e]; simp [← BitVec.and_assoc]) y hy e
  · intro e
    exact hh.2.2 (by rw [e]; simp [← BitVec.or_assoc]) y hy e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem cert_base_mem : ∀ x ∈ baseSignals, x ∈ certFirst := by
  have h : baseSignals.all (fun x => certFirst.contains x) = true := by decide +kernel
  simpa [List.contains_iff_mem] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem cert_first_ops : ∀ x ∈ baseSignals, ∀ y ∈ baseSignals,
    (x &&& y) ∈ certFirst ∧ (x ||| y) ∈ certFirst := by
  have h : baseSignals.all (fun x => baseSignals.all (fun y =>
    certFirst.contains (x &&& y) && certFirst.contains (x ||| y))) = true := by decide +kernel
  simpa [List.contains_iff_mem] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem cert_first_sep : ∀ x ∈ certFirst, ∀ y ∈ certFirst, certSeparate x y := by
  have h : certFirst.all (certGood certFirst) = true := by decide +kernel
  intro x hx
  exact (certGood_sound (List.all_eq_true.mp h x hx)).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem cert_mixed_safe : ∀ a ∈ certFirst, ∀ x ∈ baseSignals,
    certSafe (a :: baseSignals) (a &&& x) ∧ certSafe (a :: baseSignals) (a ||| x) := by
  have h : certFirst.all (fun a => baseSignals.all (fun x =>
    certGood (a :: baseSignals) (a &&& x) && certGood (a :: baseSignals) (a ||| x))) = true := by
    decide +kernel
  intro a ha x hx
  have e := List.all_eq_true.mp (List.all_eq_true.mp h a ha) x hx
  exact ⟨certGood_sound (Bool.and_eq_true_iff.mp e).1, certGood_sound (Bool.and_eq_true_iff.mp e).2⟩

private theorem cert_first_made {a : Sig} (hm : Makes baseSignals a) : a ∈ certFirst := by
  rcases hm with ⟨x, hx, y, hy, h | h⟩
  · exact h ▸ (cert_first_ops x hx y hy).1
  · exact h ▸ (cert_first_ops x hx y hy).2

private theorem cert_first_subset {a : Sig} (ha : a ∈ certFirst) :
    ∀ x ∈ a :: baseSignals, x ∈ certFirst := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · exact h ▸ ha
  · exact cert_base_mem x h

private theorem cert_no_sub {xs : List Sig} (hs : ∀ x ∈ xs, x ∈ certFirst) :
    ¬ Makes xs targetSig := by
  rintro ⟨x, hx, y, hy, he⟩
  exact he.elim (cert_first_sep x (hs x hx) y (hs y hy)).1
    (cert_first_sep x (hs x hx) y (hs y hy)).2

private theorem cert_no_cons {xs : List Sig} {b : Sig} (hs : ¬ Makes xs targetSig)
    (hb : certSafe xs b) : ¬ Makes (b :: xs) targetSig := by
  rintro ⟨x, hx, y, hy, he⟩
  rcases List.mem_cons.mp hx with rfl | hx <;> rcases List.mem_cons.mp hy with rfl | hy
  · rcases he with h | h <;> exact hb.1 (by simpa using h)
  · exact he.elim (hb.2 y hy).1 (hb.2 y hy).2
  · rcases he with h | h
    · exact (hb.2 x (by assumption)).1 (by simpa only [BitVec.and_comm] using h)
    · exact (hb.2 x (by assumption)).2 (by simpa only [BitVec.or_comm] using h)
  · exact hs ⟨x, hx, y, hy, he⟩

theorem certificate_no_three {a b : Sig} (ha0 : Makes baseSignals a)
    (hb : Makes (a :: baseSignals) b) : ¬ Makes (b :: a :: baseSignals) targetSig := by
  have ha := cert_first_made ha0
  have hs := cert_first_subset ha
  have first_case (h : b ∈ certFirst) : ¬ Makes (b :: a :: baseSignals) targetSig := by
    apply cert_no_sub
    intro x hx
    rcases List.mem_cons.mp hx with e | e
    · exact e ▸ h
    · exact hs x e
  have mixed_case := cert_no_cons (b := b) (cert_no_sub hs)
  rcases hb with ⟨x, hx, y, hy, he⟩
  rcases List.mem_cons.mp hx with rfl | hx <;> rcases List.mem_cons.mp hy with rfl | hy
  · apply first_case
    rcases he with h | h <;> simpa [h] using ha
  · apply mixed_case
    rcases he with h | h
    · exact h ▸ (cert_mixed_safe x ha y hy).1
    · exact h ▸ (cert_mixed_safe x ha y hy).2
  · apply mixed_case
    rcases he with h | h
    · exact (h.trans (BitVec.and_comm _ _)) ▸ (cert_mixed_safe y ha x (by assumption)).1
    · exact (h.trans (BitVec.or_comm _ _)) ▸ (cert_mixed_safe y ha x (by assumption)).2
  · apply first_case
    exact cert_first_made ⟨x, hx, y, hy, he⟩

end PEqualNP.Outside.L_meta_1036
theorem PEqualNP.Outside.L_meta_1036 : ∃ (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool), n ≤ 7 ∧ (∀ (j : Fin m) (x y : Fin n → Bool), (∀ i : Fin n, x i ≤ y i) → f j x ≤ f j y) ∧ ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out j⟩ (List.ofFn x) = f j x) ∧ ∀ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' j⟩ (List.ofFn x) = f j x) → gates.length < gates'.length := by
  obtain ⟨gs, out, hsize, hlegal, hone, heval⟩ := PEqualNP.Outside.L_meta_1036.upper_data
  refine ⟨5, 21, PEqualNP.Outside.L_meta_1036.family, by decide, PEqualNP.Outside.L_meta_1036.family_mono, gs, out, hlegal, hone, heval, ?_⟩
  intro gs' out' hp hc
  rw [hsize]
  exact PEqualNP.Outside.L_meta_1036.positive_lower PEqualNP.Outside.L_meta_1036.certificate_no_three gs' out' hp hc
