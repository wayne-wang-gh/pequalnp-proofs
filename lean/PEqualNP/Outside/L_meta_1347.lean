import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1347

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

lemma prefix_getD (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j ≤ gs.length) (i : ℕ) :
    (run (gs.take j) x).getD i false = if i < x.length + j then (run gs x).getD i false else false := by
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take, Nat.min_eq_left hj]
  by_cases hi : i < x.length + j
  · simp only [hi, ↓reduceIte]
    rw [run_split gs x j, run_getD (gs.drop j) _ _ (by omega)]
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

-- the gate after a wire r it lists is known to carry the constant c
def fix (c : Bool) (r : ℕ) (g : Gate) : Gate :=
  match g.op, c with
  | GateOp.and, false => ⟨GateOp.or, []⟩
  | GateOp.and, true => ⟨GateOp.and, g.inputs.filter (fun i => decide (i ≠ r))⟩
  | GateOp.or, false => ⟨GateOp.or, g.inputs.filter (fun i => decide (i ≠ r))⟩
  | GateOp.or, true => ⟨GateOp.and, []⟩
  | _, _ => g

-- the gate after input p is set false
def rp (p : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if p ∈ g.inputs then ⟨GateOp.or, []⟩ else g
  | GateOp.or => ⟨GateOp.or, g.inputs.filter (fun i => decide (i ≠ p))⟩
  | GateOp.not => if g.inputs.head? = some p then ⟨GateOp.and, []⟩ else g
  | _ => g

lemma filter_lt (r : ℕ) (l : List ℕ) (h : r ∈ l) :
    (l.filter (fun i => decide (i ≠ r))).length < l.length := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a = r
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      have := List.length_filter_le (fun i => decide (i ≠ r)) l
      simp only [List.length_cons]
      omega
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      have h2 : r ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm ha
        · exact h
      have := ih h2
      simp only [List.length_cons]
      omega

lemma any_filter (r : ℕ) (f f' : ℕ → Bool) (h : ∀ i, i ≠ r → f' i = f i) (hf : f r = false)
    (l : List ℕ) :
    ((l.filter (fun i => decide (i ≠ r))).map f').any id = (l.map f).any id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a = r
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      subst ha
      simp only [List.map_cons, List.any_cons, id, ih, hf, Bool.false_or]
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, id, ih, h a ha]

lemma all_filter (r : ℕ) (f f' : ℕ → Bool) (h : ∀ i, i ≠ r → f' i = f i) (hf : f r = true)
    (l : List ℕ) :
    ((l.filter (fun i => decide (i ≠ r))).map f').all id = (l.map f).all id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a = r
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      subst ha
      simp only [List.map_cons, List.all_cons, id, ih, hf, Bool.true_and]
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.all_cons, id, ih, h a ha]

lemma all_false (r : ℕ) (f : ℕ → Bool) (hf : f r = false) (l : List ℕ) (hr : r ∈ l) :
    (l.map f).all id = false := by
  rw [List.all_eq_false]
  exact ⟨false, List.mem_map.mpr ⟨r, hr, hf⟩, by simp⟩

lemma any_true (r : ℕ) (f : ℕ → Bool) (hf : f r = true) (l : List ℕ) (hr : r ∈ l) :
    (l.map f).any id = true := by
  rw [List.any_eq_true]
  exact ⟨true, List.mem_map.mpr ⟨r, hr, hf⟩, rfl⟩

lemma rp_eval (p : ℕ) (f f' : ℕ → Bool) (h : ∀ i, i ≠ p → f' i = f i) (hf : f p = false)
    (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (rp p g).op.eval ((rp p g).inputs.map f') = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, inputs⟩ := g
  simp only at hg
  rcases hg with rfl | rfl | rfl
  · simp only [rp]
    split_ifs with hp
    · simp only [GateOp.eval, all_false p f hf inputs hp]
      rfl
    · have : inputs.map f' = inputs.map f :=
        List.map_congr_left (fun i hi => h i (fun e => hp (e ▸ hi)))
      rw [this]
  · simp only [rp, GateOp.eval]
    exact any_filter p f f' h hf inputs
  · simp only [rp]
    cases inputs with
    | nil => simp [GateOp.eval]
    | cons a l =>
      by_cases ha : a = p
      · subst ha
        simp [GateOp.eval, hf]
      · simp [GateOp.eval, ha, h a ha]

lemma rp_not (p : ℕ) (g : Gate) (h : (rp p g).op = GateOp.not) : g.op = GateOp.not := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and => exfalso; simp only [rp] at h; split_ifs at h
  | or => simp [rp] at h
  | not => rfl
  | mod k => simp [rp] at h
  | maj => simp [rp] at h

lemma rp_shape (p : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((rp p g).op = GateOp.and ∨ (rp p g).op = GateOp.or ∨ (rp p g).op = GateOp.not) ∧
      (rp p g).inputs.length ≤ 2 := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · simp only [rp]
    split_ifs <;> simp [hlen]
  · simp only [rp]
    exact ⟨by simp, le_trans (List.length_filter_le _ _) hlen⟩
  · simp only [rp]
    split_ifs <;> simp [hlen]

lemma rp_two (p : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ((rp p g).op = GateOp.and ∨ (rp p g).op = GateOp.or) ∧ (rp p g).inputs.length = 2) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ p ∉ g.inputs := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · simp only [rp] at h
    split_ifs at h with hp
    · simp at h
    · exact ⟨Or.inl rfl, h.2, hp⟩
  · simp only [rp] at h
    have h2 := h.2
    have h3 := List.length_filter_le (fun i => decide (i ≠ p)) inputs
    refine ⟨Or.inr rfl, by simp only; omega, fun hp => ?_⟩
    have := filter_lt p inputs hp
    omega
  · simp only [rp] at h
    split_ifs at h with hp
    · simp at h
    · simp at h

lemma sim (p : ℕ) (G G' : List Gate) (hlen : G'.length = G.length) (x y : List Bool)
    (hxy : y.length = x.length) (hoff : ∀ i, i ≠ p → y.getD i false = x.getD i false)
    (H : ∀ (j : ℕ) (h1 : j < G.length) (h2 : j < G'.length) (w' : List Bool),
      w'.length = (run (G.take j) x).length →
      (∀ i, i ≠ p → w'.getD i false = (run (G.take j) x).getD i false) →
      G'[j].op.eval (G'[j].inputs.map fun i => w'.getD i false) =
        G[j].op.eval (G[j].inputs.map fun i => (run (G.take j) x).getD i false)) :
    ∀ i, i ≠ p → (run G' y).getD i false = (run G x).getD i false := by
  induction G generalizing G' x y with
  | nil =>
    have : G' = [] := List.length_eq_zero_iff.mp hlen
    subst this
    exact hoff
  | cons g gs ih =>
    cases G' with
    | nil => simp at hlen
    | cons g' gs' =>
      have h0 := H 0 (by simp) (by simp) y hxy hoff
      change g'.op.eval (g'.inputs.map fun i => y.getD i false) =
        g.op.eval (g.inputs.map fun i => x.getD i false) at h0
      rw [run_cons, run_cons, h0]
      refine ih gs' (by simpa using hlen) _ _ (by simp [hxy]) ?_ ?_
      · intro i hi
        by_cases hix : i < x.length
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hix]
          exact hoff i hi
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
            hxy]
      · intro j h1 h2 w' hw1 hw2
        exact H (j + 1) (by simp; omega) (by simp; omega) w' hw1 hw2

lemma ofFn_off {n : ℕ} (p : Fin n) (x : Fin n → Bool) (i : ℕ) (hi : i ≠ p.val) :
    (List.ofFn x).getD i false =
      (List.ofFn (fun v => if v = p then false else x v)).getD i false := by
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
    have : (⟨i, h⟩ : Fin n) ≠ p := fun e => hi (congrArg Fin.val e)
    simp [this]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma ofFn_p {n : ℕ} (p : Fin n) (x : Fin n → Bool) :
    (List.ofFn (fun v => if v = p then false else x v)).getD p.val false = false := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma finish (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
    (hsem : ∀ (o : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true))
    (p : Fin n) (gl : List Gate) (hlen : gl.length = gates.length)
    (hshape : ∀ h ∈ gl, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
      h.inputs.length ≤ 2)
    (hnot : ∀ (i : ℕ) (h1 : i < gl.length) (h2 : i < gates.length),
      gl[i].op = GateOp.not → gates[i].op = GateOp.not)
    (a b : Fin gates.length) (hab : a ≠ b)
    (htwo : ∀ (i : ℕ) (h1 : i < gl.length) (h2 : i < gates.length),
      (gl[i].op = GateOp.and ∨ gl[i].op = GateOp.or) ∧ gl[i].inputs.length = 2 →
      ((gates[i].op = GateOp.and ∨ gates[i].op = GateOp.or) ∧ gates[i].inputs.length = 2) ∧
        i ≠ a.val ∧ i ≠ b.val)
    (hrun : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ p.val →
      (run gl (List.ofFn x)).getD i false =
        (run gates (List.ofFn (fun v => if v = p then false else x v))).getD i false)
    (t : ℕ) (ι : Fin t → Fin gates.length)
    (hι : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → ∃ r : Fin t, ι r = q)
    (I : Finset (Fin gates.length)) (ha : a ∈ I) (hb : b ∈ I)
    (hI : ∀ q2 : Fin gates.length, ((gates.get q2).op = GateOp.and ∨ (gates.get q2).op = GateOp.or) ∧
      (gates.get q2).inputs.length = 2 → q2 ∈ I) :
    ∃ (gl : List Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)),
      (∀ h ∈ gl, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2) ∧
      (∀ q3 : Fin gl.length, (gl.get q3).op = GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧
      (∀ q4 : Fin gl.length, ((gl.get q4).op = GateOp.and ∨ (gl.get q4).op = GateOp.or) ∧
        (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧
      J.card + 2 ≤ I.card ∧
      ∀ (o2 : Fin m) (x2 : Fin n → Bool),
        Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  refine ⟨gl, fun o => if out o = p.val then n + gates.length else out o,
    fun r => Fin.cast hlen.symm (ι r),
    ((I.erase a).erase b).map (finCongr hlen.symm).toEmbedding, hshape, ?_, ?_, ?_, ?_⟩
  · intro q3 hq
    obtain ⟨r, hr⟩ := hι (Fin.cast hlen q3) (hnot q3.val q3.isLt (by omega) hq)
    exact ⟨r, Fin.ext (by have := congrArg Fin.val hr; exact this)⟩
  · intro q4 hq4
    obtain ⟨h1, h2, h3⟩ := htwo q4.val q4.isLt (by omega) hq4
    rw [Finset.mem_map]
    refine ⟨Fin.cast hlen q4, ?_, rfl⟩
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun e => h3 (congrArg Fin.val e), fun e => h2 (congrArg Fin.val e), hI _ h1⟩
  · rw [Finset.card_map]
    have hb' : b ∈ I.erase a := Finset.mem_erase.mpr ⟨fun e => hab e.symm, hb⟩
    have h1 := Finset.card_erase_of_mem ha
    have h2 := Finset.card_erase_of_mem hb'
    have h3 := Finset.card_pos.mpr ⟨b, hb'⟩
    have h4 := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  · intro o x2
    have hs := hsem o (fun v => if v = p then false else x2 v)
    change (run gates _).getD (out o) false = _ at hs
    have key : decide (∃ v ∈ S o, (if v = p then false else x2 v) = true) =
        decide (∃ v2 ∈ S o, v2 ≠ p ∧ x2 v2 = true) := by
      apply decide_eq_decide.mpr
      constructor <;> rintro ⟨v, hv, h⟩ <;> refine ⟨v, hv, ?_⟩ <;> by_cases e : v = p <;> simp_all
    rw [← key, ← hs]
    change (run gl (List.ofFn x2)).getD (if out o = p.val then n + gates.length else out o) false = _
    split_ifs with e
    · have h1 : (run gl (List.ofFn x2)).getD (n + gates.length) false = false :=
        List.getD_eq_default _ _ (by rw [run_length, hlen]; simp)
      have h2 : (run gates (List.ofFn fun v => if v = p then false else x2 v)).getD (out o) false
          = false := by
        rw [e, run_getD gates _ _ (by simp)]
        exact ofFn_p p x2
      rw [h1, h2]
    · exact hrun x2 (out o) e

-- one pass: every gate after p is set false
lemma rp_run {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) (p : Fin n) (x : Fin n → Bool) (i : ℕ) (hi : i ≠ p.val) :
    (run (gates.map (rp p.val)) (List.ofFn x)).getD i false =
      (run gates (List.ofFn (fun v => if v = p then false else x v))).getD i false := by
  refine sim p.val gates _ (by simp) _ _ (by simp) (fun i hi => ofFn_off p x i hi) ?_ i hi
  intro j h1 h2 w' hw1 hw2
  rw [List.getElem_map]
  refine rp_eval p.val _ _ hw2 ?_ _ (hg _ (List.getElem_mem h1)).1
  rw [run_getD _ _ _ (by simp)]
  exact ofFn_p p x

lemma fix_op (c : Bool) (r : ℕ) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (fix c r g).op = GateOp.and ∨ (fix c r g).op = GateOp.or := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop
  rcases hop with rfl | rfl <;> cases c <;> simp [fix]

lemma fix_sub (c : Bool) (r : ℕ) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i ∈ (fix c r g).inputs, i ∈ g.inputs := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop
  rcases hop with rfl | rfl <;> cases c <;> simp only [fix] <;> intro i hi <;>
    first | exact List.mem_of_mem_filter hi | cases hi

lemma fix_len (c : Bool) (r : ℕ) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hr : r ∈ g.inputs) (hl : g.inputs.length ≤ 2) : (fix c r g).inputs.length ≤ 1 := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop hr hl
  have := filter_lt r inputs hr
  rcases hop with rfl | rfl <;> cases c <;> simp only [fix] <;>
    first | omega | simp

lemma fix_eval (c : Bool) (r : ℕ) (g : Gate) (f : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hr : r ∈ g.inputs) (hf : f r = c) :
    (fix c r g).op.eval ((fix c r g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop hr
  rcases hop with rfl | rfl
  · cases c
    · simp only [fix, GateOp.eval]
      rw [all_false r f hf inputs hr]
      rfl
    · simp only [fix, GateOp.eval]
      exact all_filter r f f (fun _ _ => rfl) hf inputs
  · cases c
    · simp only [fix, GateOp.eval]
      exact any_filter r f f (fun _ _ => rfl) hf inputs
    · simp only [fix, GateOp.eval]
      rw [any_true r f hf inputs hr]
      rfl

def U {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD i false

lemma U_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (r : ℕ) (hr : r < n) :
    U gs x r = x ⟨r, hr⟩ := by
  unfold U
  rw [run_getD _ _ _ (by simpa using hr), List.getD_eq_getElem _ _ (by simpa using hr)]
  simp

lemma U_big {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (r : ℕ) (hr : n + gs.length ≤ r) :
    U gs x r = false := by
  unfold U
  exact List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; exact hr)

lemma U_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    U gs x (n + j) =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then U gs x i else false) := by
  unfold U
  have hl : (run (gs.take j) (List.ofFn x)).length = n + j := by
    rw [run_length, List.length_take, Nat.min_eq_left hj.le, List.length_ofFn]
  have e : (fun i => if i < n + j then (run gs (List.ofFn x)).getD i false else false) =
      fun i => (run (gs.take j) (List.ofFn x)).getD i false := by
    funext i
    rw [prefix_getD gs _ j hj.le i, List.length_ofFn]
  rw [e, run_split gs _ j, List.drop_eq_getElem_cons hj, run_cons]
  rw [run_getD _ _ _ (by simp [hl]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [hl, Nat.sub_self, List.getD_cons_zero]

lemma not_val {n : ℕ} (gates : List Gate) (p : Fin n) (N : ℕ) (hN : N < gates.length)
    (hop : gates[N].op = GateOp.not) (hh : gates[N].inputs.head? = some p.val)
    (x : Fin n → Bool) : U gates x (n + N) = !(x p) := by
  rw [U_gate gates x N hN, hop]
  obtain ⟨l, hl⟩ : ∃ l, gates[N].inputs = p.val :: l := by
    cases h : gates[N].inputs with
    | nil => rw [h] at hh; simp at hh
    | cons c l =>
      rw [h] at hh
      simp only [List.head?_cons, Option.some.injEq] at hh
      exact ⟨l, by rw [hh]⟩
  rw [hl]
  have h1 : p.val < n + N := by have := p.isLt; omega
  simp only [List.map_cons, h1, ↓reduceIte, GateOp.eval, List.headD_cons]
  rw [U_input _ _ _ p.isLt]

lemma core : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → (∀ jr : Fin gates.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gates.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gates.length, (∃ oq : Fin m, out oq = n + jr3.val) ∨ ∃ kr : Fin gates.length, ((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gates.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gates.get kr).inputs)) ∧ (∀ jr4 : Fin gates.length, ((gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gates.get jr4).inputs = [ar, br]) → ∀ p : Fin n, (gates.get (ι 0)).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get (ι 0)).inputs.head? = some p.val → ∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin 1, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ (∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true)) := by
  intro n m S gates out hg hsem ι hι hred p hNop hNhead a haop halen hap I hI
  obtain ⟨R1, R2, R3, R4⟩ := hred
  have hNv : ∀ x : Fin n → Bool, U gates x (n + (ι 0).val) = !(x p) :=
    fun x => not_val gates p (ι 0).val (ι 0).isLt hNop hNhead x
  have hUp : ∀ x : Fin n → Bool, U gates x p.val = x p := fun x => U_input _ _ _ p.isLt
  have hb : ∃ b : Fin gates.length, ((gates.get b).op = GateOp.and ∨ (gates.get b).op = GateOp.or) ∧
      n + (ι 0).val ∈ (gates.get b).inputs := by
    rcases R3 (ι 0) with ⟨oq, ho⟩ | ⟨kr, h | h⟩
    · exfalso
      have h1 := hsem oq (fun _ => false)
      rw [ho] at h1
      change U gates _ (n + (ι 0).val) = _ at h1
      rw [hNv] at h1
      simp at h1
    · exfalso
      obtain ⟨r, hr⟩ := hι kr h.1
      have hr0 : r = 0 := Subsingleton.elim _ _
      rw [hr0] at hr
      have h2 := h.2
      rw [← hr, hNhead] at h2
      have h3 : p.val = n + (ι 0).val := by simpa using h2
      have := p.isLt
      omega
    · exact ⟨kr, h⟩
  obtain ⟨b, hbop, hbN⟩ := hb
  have hblen : (gates.get b).inputs.length = 2 := by
    obtain ⟨ar, br, _, hbin⟩ := R4 b hbop
    rw [hbin]
    rfl
  have hab : a ≠ b := by
    intro e
    subst e
    obtain ⟨ar, br, hne, hbin⟩ := R4 a haop
    have hpa : p.val < n + a.val := by have := p.isLt; omega
    have hval : ∀ x : Fin n → Bool, U gates x (n + a.val) = (gates.get a).op.eval
        ([ar, br].map fun i => if i < n + a.val then U gates x i else false) := fun x => by
      rw [← hbin]
      exact U_gate gates x a.val a.isLt
    obtain ⟨x1, y1, h1⟩ := R1 a
    obtain ⟨x2, h2⟩ := R2 a p.val hpa
    change U gates x1 _ ≠ U gates y1 _ at h1
    change U gates x2 _ ≠ U gates x2 _ at h2
    rw [hval, hval] at h1
    rw [hval, hUp] at h2
    rw [hbin] at hap hbN
    have e1 : (ar = p.val ∧ br = n + (ι 0).val) ∨ (ar = n + (ι 0).val ∧ br = p.val) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hap hbN
      have := p.isLt
      omega
    by_cases hNa : (ι 0).val < a.val <;> rcases e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases haop with ho | ho <;> rw [ho] at h1 h2 <;>
      simp [GateOp.eval, hpa, hNa, hUp, hNv] at h1 h2
  have hconst : ∀ x : Fin n → Bool, x p = false →
      (if n + (ι 0).val < n + b.val then U gates x (n + (ι 0).val) else false) =
        decide ((ι 0).val < b.val) := by
    intro x hx
    by_cases h : (ι 0).val < b.val <;> simp [h, hNv, hx]
  by_cases hpb : p.val ∈ (gates.get b).inputs
  · refine finish n m S gates out hsem p (gates.map (rp p.val)) (by simp) ?_ ?_ a b hab ?_
      (fun x i hi => rp_run gates hg p x i hi) 1 ι hι I (hI a ⟨haop, halen⟩) (hI b ⟨hbop, hblen⟩) hI
    · intro g hgm
      obtain ⟨g0, hg1, rfl⟩ := List.mem_map.mp hgm
      exact rp_shape p.val g0 (hg g0 hg1)
    · intro i h1 h2 hn
      rw [List.getElem_map] at hn
      exact rp_not p.val _ hn
    · intro i h1 h2 h'
      rw [List.getElem_map] at h'
      obtain ⟨k1, k2, k3⟩ := rp_two p.val _ (hg _ (List.getElem_mem h2)) h'
      refine ⟨⟨k1, k2⟩, fun e2 => k3 ?_, fun e2 => k3 ?_⟩
      · subst e2
        exact hap
      · subst e2
        exact hpb
  · have hbop' : gates[b.val].op = GateOp.and ∨ gates[b.val].op = GateOp.or := hbop
    have hbN' : n + (ι 0).val ∈ gates[b.val].inputs := hbN
    have hblen' : gates[b.val].inputs.length = 2 := hblen
    have hpn : p.val ∉ gates[b.val].inputs := hpb
    refine finish n m S gates out hsem p ((gates.map (rp p.val)).set b.val
      (fix (decide ((ι 0).val < b.val)) (n + (ι 0).val) gates[b.val]))
      (by simp) ?_ ?_ a b hab ?_ ?_ 1 ι hι I
      (hI a ⟨haop, halen⟩) (hI b ⟨hbop, hblen⟩) hI
    · intro g hgm
      rcases List.mem_or_eq_of_mem_set hgm with h1 | rfl
      · obtain ⟨g0, hg1, rfl⟩ := List.mem_map.mp h1
        exact rp_shape p.val g0 (hg g0 hg1)
      · have h1 := fix_op (decide ((ι 0).val < b.val)) (n + (ι 0).val) gates[b.val] hbop'
        have h2 := fix_len (decide ((ι 0).val < b.val)) (n + (ι 0).val) gates[b.val] hbop' hbN'
          hblen'.le
        exact ⟨by tauto, by omega⟩
    · intro i h1 h2 hn
      rw [List.getElem_set] at hn
      split_ifs at hn with e
      · exfalso
        have h3 := fix_op (decide ((ι 0).val < b.val)) (n + (ι 0).val) gates[b.val] hbop'
        rw [hn] at h3
        simp at h3
      · rw [List.getElem_map] at hn
        exact rp_not p.val _ hn
    · intro i h1 h2 h'
      rw [List.getElem_set] at h'
      split_ifs at h' with e
      · exfalso
        have h3 := fix_len (decide ((ι 0).val < b.val)) (n + (ι 0).val) gates[b.val] hbop' hbN'
          hblen'.le
        have h4 := h'.2
        omega
      · rw [List.getElem_map] at h'
        obtain ⟨k1, k2, k3⟩ := rp_two p.val _ (hg _ (List.getElem_mem h2)) h'
        refine ⟨⟨k1, k2⟩, fun e2 => k3 ?_, fun e2 => e e2.symm⟩
        subst e2
        exact hap
    · intro x i hi
      refine sim p.val gates _ (by simp) _ _ (by simp) (fun i hi => ofFn_off p x i hi) ?_ i hi
      intro j h1 h2 w' hw1 hw2
      rw [List.getElem_set]
      split_ifs with e
      · subst e
        have e1 : (fix (decide ((ι 0).val < b.val)) (n + (ι 0).val) gates[b.val]).inputs.map
            (fun i => w'.getD i false) =
            (fix (decide ((ι 0).val < b.val)) (n + (ι 0).val) gates[b.val]).inputs.map
              (fun i => (run (gates.take b.val)
              (List.ofFn (fun v => if v = p then false else x v))).getD i false) :=
          List.map_congr_left (fun i hi2 => hw2 i (fun e => hpn (e ▸ fix_sub _ _ _ hbop' i hi2)))
        rw [e1]
        refine fix_eval _ _ _ _ hbop' hbN' ?_
        rw [prefix_getD gates _ b.val b.isLt.le (n + (ι 0).val), List.length_ofFn]
        exact hconst _ (by simp)
      · rw [List.getElem_map]
        refine rp_eval p.val _ _ hw2 ?_ _ (hg _ (List.getElem_mem h1)).1
        rw [run_getD _ _ _ (by simp)]
        exact ofFn_p p x

end PEqualNP.Outside.L_meta_1347

theorem PEqualNP.Outside.L_meta_1347 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → (∀ jr : Fin gates.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gates.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gates.length, (∃ oq : Fin m, out oq = n + jr3.val) ∨ ∃ kr : Fin gates.length, ((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gates.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gates.get kr).inputs)) ∧ (∀ jr4 : Fin gates.length, ((gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gates.get jr4).inputs = [ar, br]) → ∀ p : Fin n, (gates.get (ι 0)).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get (ι 0)).inputs.head? = some p.val → ∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin 1, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ (∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true)) := by
  exact PEqualNP.Outside.L_meta_1347.core
