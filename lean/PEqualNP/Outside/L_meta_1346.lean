import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1346

def gv (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [gv g w]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [gv g x]) :=
  rfl

lemma run_append (A B : List Gate) (x : List Bool) : run (A ++ B) x = run B (run A x) := by
  simp only [run, List.foldl_append]

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

lemma eval_eq (gl : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gl, o⟩ x = (run gl x).getD o false :=
  rfl

lemma wire_k (A : List Gate) (g : Gate) (B : List Gate) (x : List Bool) :
    (run (A ++ g :: B) x).getD (x.length + A.length) false = gv g (run A x) := by
  rw [run_append, run_cons, run_getD _ _ _ (by simp [run_length]),
    List.getD_append_right _ _ _ _ (by simp [run_length])]
  simp [run_length]

lemma wire_lt (A : List Gate) (g : Gate) (B : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + A.length) :
    (run (A ++ g :: B) x).getD i false = (run A x).getD i false := by
  rw [run_append, run_cons,
    run_getD _ _ _ (by simp only [List.length_append, run_length, List.length_cons,
      List.length_nil]; omega),
    List.getD_append _ _ _ _ (by simp only [run_length]; omega)]

lemma split (l : List Gate) (k : Fin l.length) :
    ∃ A B, l = A ++ l.get k :: B ∧ A.length = k.val :=
  ⟨l.take k, l.drop (k + 1), by simp, by simp [Nat.le_of_lt k.isLt]⟩

def mu (gl : List Gate) : ℕ := (gl.map fun g => g.inputs.length + 1).sum

def mapIn (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

lemma mu_set (A B : List Gate) (g g' : Gate) (h : g'.inputs.length < g.inputs.length) :
    mu (A ++ g' :: B) < mu (A ++ g :: B) := by
  simp only [mu, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  omega

lemma mu_del (A B : List Gate) (g : Gate) (f : ℕ → ℕ) :
    mu (A ++ B.map (mapIn f)) < mu (A ++ g :: B) := by
  have : (B.map (mapIn f)).map (fun g => g.inputs.length + 1) =
      B.map (fun g => g.inputs.length + 1) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro b _
    simp [mapIn]
  simp only [mu, List.map_append, List.map_cons, List.sum_append, List.sum_cons, this]
  omega

def isNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

def two (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (g.inputs.length = 2)
  | GateOp.or => decide (g.inputs.length = 2)
  | _ => false

lemma isNot_iff (g : Gate) : isNot g = true ↔ g.op = GateOp.not := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [isNot]

lemma two_iff (g : Gate) :
    two g = true ↔ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [two]

lemma cnt (l : List Gate) (p : Gate → Bool) :
    (Finset.univ.filter (fun q : Fin l.length => p (l.get q) = true)).card = l.countP p := by
  have h := List.countP_ofFn l.get p
  rw [List.ofFn_get] at h
  exact h.symm

lemma countP_set_le (p : Gate → Bool) (A B : List Gate) (g g' : Gate) (h : p g' = false) :
    (A ++ g' :: B).countP p ≤ (A ++ g :: B).countP p := by
  simp only [List.countP_append, List.countP_cons, h]
  split_ifs <;> first | omega | contradiction

lemma countP_del (p : Gate → Bool) (f : Gate → Gate) (hf : ∀ b, p (f b) = p b)
    (A B : List Gate) (g : Gate) :
    (A ++ B.map f).countP p ≤ (A ++ g :: B).countP p := by
  have e : (p ∘ f) = p := funext hf
  rw [List.countP_append, List.countP_append, List.countP_map, e, List.countP_cons]
  omega

def reads (b : Gate) (i : ℕ) : Prop :=
  (b.op = GateOp.not ∧ b.inputs.head? = some i) ∨
    ((b.op = GateOp.and ∨ b.op = GateOp.or) ∧ i ∈ b.inputs)

lemma gv_congr (b : Gate) (hb : b.op = GateOp.and ∨ b.op = GateOp.or ∨ b.op = GateOp.not)
    (f f' : ℕ → Bool) (h : ∀ i, reads b i → f' i = f i) :
    b.op.eval (b.inputs.map f') = b.op.eval (b.inputs.map f) := by
  obtain ⟨op, inputs⟩ := b
  dsimp only at hb
  rcases hb with rfl | rfl | rfl
  · have : inputs.map f' = inputs.map f :=
      List.map_congr_left (fun i hi => h i (Or.inr ⟨Or.inl rfl, hi⟩))
    rw [this]
  · have : inputs.map f' = inputs.map f :=
      List.map_congr_left (fun i hi => h i (Or.inr ⟨Or.inr rfl, hi⟩))
    rw [this]
  · cases inputs with
    | nil => rfl
    | cons a l =>
      have := h a (Or.inl ⟨rfl, rfl⟩)
      simp [GateOp.eval, this]

lemma sim_pair (R : List Bool → List Bool → Prop)
    (hR : ∀ w w' v, R w w' → R (w ++ [v]) (w' ++ [v])) (f : Gate → Gate) (B : List Gate)
    (H : ∀ b ∈ B, ∀ w w', R w w' → gv (f b) w' = gv b w) (w w' : List Bool) (h : R w w') :
    R (run B w) (run (B.map f) w') := by
  induction B generalizing w w' with
  | nil => exact h
  | cons b B ih =>
    rw [List.map_cons, run_cons, run_cons, H b List.mem_cons_self w w' h]
    exact ih (fun b hb => H b (List.mem_cons_of_mem _ hb)) _ _ (hR _ _ _ h)

def sg (c w0 i : ℕ) : ℕ := if i < c then i else if i = c then w0 else i - 1

def rel (c w0 : ℕ) (q : Prop) (w w' : List Bool) : Prop :=
  w.length = w'.length + 1 ∧ c ≤ w'.length ∧ (q → w0 < c) ∧
    ∀ i, (i ≠ c ∨ q) → w'.getD (sg c w0 i) false = w.getD i false

lemma rel_step (c w0 : ℕ) (q : Prop) (w w' : List Bool) (v : Bool) (h : rel c w0 q w w') :
    rel c w0 q (w ++ [v]) (w' ++ [v]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp; omega, by simp; omega, h3, fun i hi => ?_⟩
  have hw0 : i = c → w0 < c := fun e => h3 (hi.resolve_left (not_not.mpr e))
  by_cases c1 : i < w.length
  · have hs : sg c w0 i < w'.length := by
      unfold sg
      split_ifs <;> omega
    rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ c1]
    exact h4 i hi
  · by_cases c2 : i = w.length
    · have hs : sg c w0 i = w'.length := by
        unfold sg
        split_ifs <;> omega
      rw [hs, c2, List.getD_append_right _ _ _ _ (le_refl _),
        List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · have hs : w'.length + 1 ≤ sg c w0 i := by
        unfold sg
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Valid (n m : ℕ) (S : Fin m → Finset (Fin n)) (c : ℕ) (gl : List Gate) (ol : Fin m → ℕ) :
    Prop :=
  (∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2) ∧
  gl.countP isNot ≤ 1 ∧ gl.countP two ≤ c ∧
  ∀ (o : Fin m) (x : Fin n → Bool),
    Circuit.eval ⟨gl, ol o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)

lemma case_set {n m : ℕ} (S : Fin m → Finset (Fin n)) (c : ℕ) (A B : List Gate) (g g' : Gate)
    (ol : Fin m → ℕ) (hv : Valid n m S c (A ++ g :: B) ol)
    (hs : (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length < g.inputs.length)
    (hval : ∀ x : Fin n → Bool, gv g' (run A (List.ofFn x)) = gv g (run A (List.ofFn x))) :
    Valid n m S c (A ++ g' :: B) ol := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hg := h1 g (by simp)
  have hn : isNot g' = false := by
    rw [Bool.eq_false_iff]
    intro e
    rw [isNot_iff] at e
    rcases hs.1 with h | h <;> rw [h] at e <;> cases e
  have ht : two g' = false := by
    rw [Bool.eq_false_iff]
    intro e
    rw [two_iff] at e
    have := e.2
    have := hs.2
    have := hg.2
    omega
  refine ⟨?_, le_trans (countP_set_le isNot A B g g' hn) h2,
    le_trans (countP_set_le two A B g g' ht) h3, ?_⟩
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact h1 h (List.mem_append_left _ hh)
    · rcases List.mem_cons.mp hh with rfl | hh
      · refine ⟨?_, by have := hs.2; have := hg.2; omega⟩
        rcases hs.1 with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact h1 h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  · intro o x
    have e : (run (A ++ g :: B) (List.ofFn x)).getD (ol o) false =
        decide (∃ v ∈ S o, x v = true) := h4 o x
    rw [run_append, run_cons] at e
    rw [eval_eq, run_append, run_cons, hval x]
    exact e

lemma case_del {n m : ℕ} (S : Fin m → Finset (Fin n)) (c : ℕ) (A B : List Gate) (g : Gate)
    (ol : Fin m → ℕ) (hv : Valid n m S c (A ++ g :: B) ol) (w0 : ℕ) (q : Prop)
    (hq : q → w0 < n + A.length)
    (hcopy : q → ∀ x : Fin n → Bool,
      gv g (run A (List.ofFn x)) = (run A (List.ofFn x)).getD w0 false)
    (hreads : ¬q → ∀ b ∈ B, ¬reads b (n + A.length))
    (hout : ¬q → ∀ o, ol o ≠ n + A.length) :
    Valid n m S c (A ++ B.map (mapIn (sg (n + A.length) w0)))
      (fun o => sg (n + A.length) w0 (ol o)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  refine ⟨?_, le_trans (countP_del isNot (mapIn (sg (n + A.length) w0)) (fun b => rfl) A B g) h2,
    le_trans (countP_del two (mapIn (sg (n + A.length) w0)) (fun b => ?_) A B g) h3, ?_⟩
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact h1 h (List.mem_append_left _ hh)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hh
      have := h1 b (List.mem_append_right _ (List.mem_cons_of_mem _ hb))
      exact ⟨this.1, by simpa [mapIn] using this.2⟩
  · simp [two, mapIn]
  · intro o x
    have e : (run (A ++ g :: B) (List.ofFn x)).getD (ol o) false =
        decide (∃ v ∈ S o, x v = true) := h4 o x
    rw [run_append, run_cons] at e
    rw [eval_eq, run_append, ← e]
    have hu : (run A (List.ofFn x)).length = n + A.length := by
      rw [run_length, List.length_ofFn]
    have h0 : rel (n + A.length) w0 q
        (run A (List.ofFn x) ++ [gv g (run A (List.ofFn x))]) (run A (List.ofFn x)) := by
      refine ⟨by simp, by omega, hq, fun i hi => ?_⟩
      by_cases c1 : i < n + A.length
      · have : sg (n + A.length) w0 i = i := by simp [sg, c1]
        rw [this, List.getD_append _ _ _ _ (by omega)]
      · by_cases c2 : i = n + A.length
        · have hq' : q := hi.resolve_left (not_not.mpr c2)
          have : sg (n + A.length) w0 i = w0 := by simp [sg, c2]
          rw [this, c2, List.getD_append_right _ _ _ _ (by omega), hu, ← hcopy hq' x]
          simp
        · have : sg (n + A.length) w0 i = i - 1 := by simp [sg, c1, c2]
          rw [this, List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by simp; omega)]
    have H : ∀ b ∈ B, ∀ w w', rel (n + A.length) w0 q w w' →
        gv (mapIn (sg (n + A.length) w0) b) w' = gv b w := by
      intro b hb w w' hr
      have hsh := (h1 b (List.mem_append_right _ (List.mem_cons_of_mem _ hb))).1
      simp only [gv, mapIn, List.map_map]
      refine gv_congr b hsh (fun i => w.getD i false) _ (fun i hi => ?_)
      apply hr.2.2.2 i
      by_cases hq' : q
      · exact Or.inr hq'
      · exact Or.inl (fun e => hreads hq' b hb (e ▸ hi))
    have h5 := sim_pair (rel (n + A.length) w0 q) (rel_step _ _ _) _ B H _ _ h0
    apply h5.2.2.2 (ol o)
    by_cases hq' : q
    · exact Or.inr hq'
    · exact Or.inl (hout hq' o)

def fix (c : Bool) (r : ℕ) (g : Gate) : Gate :=
  match g.op, c with
  | GateOp.and, false => ⟨GateOp.or, []⟩
  | GateOp.and, true => ⟨GateOp.and, g.inputs.filter (fun i => decide (i ≠ r))⟩
  | GateOp.or, false => ⟨GateOp.or, g.inputs.filter (fun i => decide (i ≠ r))⟩
  | GateOp.or, true => ⟨GateOp.and, []⟩
  | GateOp.not, false => ⟨GateOp.and, []⟩
  | GateOp.not, true => ⟨GateOp.or, []⟩
  | _, _ => g

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

lemma fix_ok (c : Bool) (p : ℕ) (g : Gate) (hg : reads g p) :
    (fix c p g).inputs.length < g.inputs.length ∧
      ((fix c p g).op = GateOp.and ∨ (fix c p g).op = GateOp.or) ∧
      ∀ w : List Bool, w.getD p false = c → gv (fix c p g) w = gv g w := by
  obtain ⟨op, inputs⟩ := g
  rcases hg with ⟨h1, h2⟩ | ⟨h1 | h1, h2⟩
  · dsimp only at h1 h2
    subst h1
    cases inputs with
    | nil => simp at h2
    | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at h2
      subst h2
      cases c
      · exact ⟨by simp [fix], by simp [fix], fun w hw => by
          have e : gv ⟨GateOp.not, a :: l⟩ w = !(w.getD a false) := rfl
          rw [e, hw]
          rfl⟩
      · exact ⟨by simp [fix], by simp [fix], fun w hw => by
          have e : gv ⟨GateOp.not, a :: l⟩ w = !(w.getD a false) := rfl
          rw [e, hw]
          rfl⟩
  · dsimp only at h1 h2
    subst h1
    cases c
    · refine ⟨by simp only [fix]; exact List.length_pos_of_mem h2, by simp [fix],
        fun w hw => ?_⟩
      simp only [fix, gv, GateOp.eval]
      rw [all_false p _ hw inputs h2]
      rfl
    · refine ⟨by simp only [fix]; exact filter_lt p inputs h2, by simp [fix], fun w hw => ?_⟩
      simp only [fix, gv, GateOp.eval]
      exact all_filter p _ _ (fun _ _ => rfl) hw inputs
  · dsimp only at h1 h2
    subst h1
    cases c
    · refine ⟨by simp only [fix]; exact filter_lt p inputs h2, by simp [fix], fun w hw => ?_⟩
      simp only [fix, gv, GateOp.eval]
      exact any_filter p _ _ (fun _ _ => rfl) hw inputs
    · refine ⟨by simp only [fix]; exact List.length_pos_of_mem h2, by simp [fix],
        fun w hw => ?_⟩
      simp only [fix, gv, GateOp.eval]
      rw [any_true p _ hw inputs h2]
      rfl

lemma case_fix {n m : ℕ} (S : Fin m → Finset (Fin n)) (c : ℕ) (A : List Gate) (r : Gate)
    (B : List Gate) (ol : Fin m → ℕ) (hv : Valid n m S c (A ++ r :: B) ol) (p : ℕ) (cv : Bool)
    (hc : ∀ x : Fin n → Bool, (run A (List.ofFn x)).getD p false = cv) (hr : reads r p) :
    ∃ r' : Gate, r'.inputs.length < r.inputs.length ∧ Valid n m S c (A ++ r' :: B) ol := by
  obtain ⟨h1, h2, h3⟩ := fix_ok cv p r hr
  exact ⟨fix cv p r, h1, case_set S c A B r _ ol hv ⟨h2, h1⟩ (fun x => h3 _ (hc x))⟩

lemma out_ne {n m : ℕ} (S : Fin m → Finset (Fin n)) (hS : ∀ ic : Fin m, 2 ≤ (S ic).card)
    (c : ℕ) (gl : List Gate) (ol : Fin m → ℕ) (hv : Valid n m S c gl ol) (o : Fin m) :
    ∃ x y : Fin n → Bool, Circuit.eval ⟨gl, ol o⟩ (List.ofFn x) ≠
      Circuit.eval ⟨gl, ol o⟩ (List.ofFn y) := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  rw [hv.2.2.2 o, hv.2.2.2 o]
  obtain ⟨v, hv'⟩ := Finset.card_pos.mp (by have := hS o; omega : 0 < (S o).card)
  simp
  exact ⟨v, hv'⟩

lemma gl_pos {n m : ℕ} (S : Fin m → Finset (Fin n)) (hS : ∀ ic : Fin m, 2 ≤ (S ic).card)
    (c : ℕ) (gl : List Gate) (ol : Fin m → ℕ) (hv : Valid n m S c gl ol) (o : Fin m) :
    0 < gl.length := by
  rcases gl with _ | ⟨g, gl⟩
  swap
  · simp
  exfalso
  have h4 : ∀ x : Fin n → Bool,
      (List.ofFn x).getD (ol o) false = decide (∃ v ∈ S o, x v = true) :=
    fun x => hv.2.2.2 o x
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (hS o)
  have hv' : ∃ v ∈ S o, v.val ≠ ol o := by
    by_cases e : a.val = ol o
    · exact ⟨b, hb, fun e2 => hab (Fin.ext (e.trans e2.symm))⟩
    · exact ⟨a, ha, e⟩
  obtain ⟨v, hvS, hne⟩ := hv'
  have h := h4 (fun u => decide (u = v))
  have hr : decide (∃ w ∈ S o, decide (w = v) = true) = true :=
    decide_eq_true ⟨v, hvS, by simp⟩
  rw [hr] at h
  by_cases hlt : ol o < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at h
    simp at h
    exact hne (by rw [← h])
  · rw [List.getD_eq_default _ _ (by simpa using hlt)] at h
    exact Bool.false_ne_true h

def Red (n m : ℕ) (gl : List Gate) (ol : Fin m → ℕ) : Prop :=
  (∀ jr : Fin gl.length, ∃ xr yr : Fin n → Bool,
    Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn xr) ≠ Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn yr)) ∧
  (∀ jr2 : Fin gl.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool,
    Circuit.eval ⟨gl, n + jr2.val⟩ (List.ofFn xr2) ≠ Circuit.eval ⟨gl, wr⟩ (List.ofFn xr2)) ∧
  (∀ jr3 : Fin gl.length, (∃ oq : Fin m, ol oq = n + jr3.val) ∨
    ∃ kr : Fin gl.length, reads (gl.get kr) (n + jr3.val)) ∧
  (∀ jr4 : Fin gl.length, ((gl.get jr4).op = GateOp.and ∨ (gl.get jr4).op = GateOp.or) →
    ∃ ar br : ℕ, ar ≠ br ∧ (gl.get jr4).inputs = [ar, br])

lemma main {n m : ℕ} (S : Fin m → Finset (Fin n)) (hS : ∀ ic : Fin m, 2 ≤ (S ic).card)
    (c : ℕ) : ∀ (N : ℕ) (gl : List Gate) (ol : Fin m → ℕ), mu gl = N → Valid n m S c gl ol →
    ∃ (gl' : List Gate) (ol' : Fin m → ℕ), Valid n m S c gl' ol' ∧ Red n m gl' ol' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro gl ol hN hv
  by_cases h3 : ∀ jr3 : Fin gl.length, (∃ oq : Fin m, ol oq = n + jr3.val) ∨
    ∃ kr : Fin gl.length, reads (gl.get kr) (n + jr3.val)
  swap
  · simp only [not_forall, not_or, not_exists] at h3
    obtain ⟨k, hk1, hk2⟩ := h3
    obtain ⟨A, B, hl, hA⟩ := split gl k
    generalize gl.get k = g at hl
    subst hl
    rw [← hA] at hk1 hk2
    have hrd : ∀ b ∈ B, ¬reads b (n + A.length) := by
      intro b hb hr
      obtain ⟨kr, hkr⟩ := List.mem_iff_get.mp
        (List.mem_append_right A (List.mem_cons_of_mem g hb))
      exact hk2 kr (hkr ▸ hr)
    exact ih _ (by rw [← hN]; exact mu_del A B g _) _ _ rfl
      (case_del S c A B g ol hv 0 False (fun h => h.elim) (fun h => h.elim)
        (fun _ => hrd) (fun _ o => hk1 o))
  by_cases h2 : ∀ jr2 : Fin gl.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool,
    Circuit.eval ⟨gl, n + jr2.val⟩ (List.ofFn xr2) ≠ Circuit.eval ⟨gl, wr⟩ (List.ofFn xr2)
  swap
  · simp only [not_forall, not_exists, ne_eq, not_not] at h2
    obtain ⟨k, wr, hwr, heq⟩ := h2
    obtain ⟨A, B, hl, hA⟩ := split gl k
    generalize gl.get k = g at hl
    subst hl
    rw [← hA] at hwr heq
    refine ih _ (by rw [← hN]; exact mu_del A B g _) _ _ rfl
      (case_del S c A B g ol hv wr True (fun _ => hwr) (fun _ x => ?_)
        (fun h => (h trivial).elim) (fun h => (h trivial).elim))
    have e : (run (A ++ g :: B) (List.ofFn x)).getD (n + A.length) false =
        (run (A ++ g :: B) (List.ofFn x)).getD wr false := heq x
    have e1 := wire_k A g B (List.ofFn x)
    have e2 := wire_lt A g B (List.ofFn x) wr (by rw [List.length_ofFn]; exact hwr)
    rw [List.length_ofFn] at e1
    rw [← e1, e, e2]
  by_cases h1 : ∀ jr : Fin gl.length, ∃ xr yr : Fin n → Bool,
    Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn xr) ≠ Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn yr)
  swap
  · simp only [not_forall, not_exists, ne_eq, not_not] at h1
    obtain ⟨k, hk⟩ := h1
    rcases h3 k with ⟨o, ho⟩ | ⟨kr, hkr⟩
    · exfalso
      obtain ⟨x, y, hxy⟩ := out_ne S hS c gl ol hv o
      apply hxy
      rw [ho]
      exact hk x y
    · obtain ⟨A, B, hl, hA⟩ := split gl kr
      generalize gl.get kr = r at hl hkr
      subst hl
      have hc : ∀ x : Fin n → Bool, (run A (List.ofFn x)).getD (n + k.val) false =
          (run A (List.ofFn (fun _ : Fin n => false))).getD (n + k.val) false := by
        intro x
        by_cases hlt : k.val < A.length
        · rw [← wire_lt A r B (List.ofFn x) _ (by rw [List.length_ofFn]; omega),
            ← wire_lt A r B (List.ofFn (fun _ : Fin n => false)) _ (by rw [List.length_ofFn]; omega)]
          exact hk x _
        · rw [List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega),
            List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
      obtain ⟨r', hr1, hr2⟩ := case_fix S c A r B ol hv (n + k.val) _ hc hkr
      exact ih _ (by rw [← hN]; exact mu_set A B r r' hr1) _ _ rfl hr2
  by_cases h4 : ∀ jr4 : Fin gl.length,
    ((gl.get jr4).op = GateOp.and ∨ (gl.get jr4).op = GateOp.or) →
    ∃ ar br : ℕ, ar ≠ br ∧ (gl.get jr4).inputs = [ar, br]
  · exact ⟨gl, ol, hv, h1, h2, h3, h4⟩
  rw [not_forall] at h4
  obtain ⟨k, hk⟩ := h4
  rw [Classical.not_imp] at hk
  obtain ⟨hop, hno⟩ := hk
  obtain ⟨A, B, hl, hA⟩ := split gl k
  generalize gl.get k = g at hl hop hno
  subst hl
  have hsh := hv.1 g (by simp)
  have hw : ∀ x : Fin n → Bool,
      Circuit.eval ⟨A ++ g :: B, n + k.val⟩ (List.ofFn x) = gv g (run A (List.ofFn x)) := by
    intro x
    have := wire_k A g B (List.ofFn x)
    rw [List.length_ofFn, hA] at this
    exact this
  obtain ⟨op, inputs⟩ := g
  dsimp only at hop hno hsh
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c3, l⟩⟩⟩
  · exfalso
    obtain ⟨x, y, hxy⟩ := h1 k
    apply hxy
    rw [hw x, hw y]
    rcases hop with rfl | rfl <;> simp [gv, GateOp.eval]
  · have hval : ∀ w : List Bool, gv ⟨op, [a]⟩ w = w.getD a false := by
      intro w
      rcases hop with rfl | rfl <;> simp [gv, GateOp.eval]
    exfalso
    by_cases ha : a < n + k.val
    · obtain ⟨x, hx⟩ := h2 k a ha
      apply hx
      rw [hw x, hval]
      exact (wire_lt A ⟨op, [a]⟩ B (List.ofFn x) a (by rw [List.length_ofFn]; omega)).symm
    · obtain ⟨x, y, hxy⟩ := h1 k
      apply hxy
      rw [hw x, hw y, hval, hval,
        List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega),
        List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
  · by_cases hab : a = b
    · subst hab
      exact ih _ (by rw [← hN]; exact mu_set A B _ ⟨op, [a]⟩ (by simp)) _ _ rfl
        (case_set S c A B _ ⟨op, [a]⟩ ol hv ⟨hop, by simp⟩
          (fun x => by rcases hop with rfl | rfl <;> simp [gv, GateOp.eval]))
    · exact (hno ⟨a, b, hab, rfl⟩).elim
  · exact absurd hsh.2 (by simp)

lemma finish (n m : ℕ) (S : Fin m → Finset (Fin n)) (hS : ∀ ic : Fin m, 2 ≤ (S ic).card)
    (hm : 0 < m) (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hsem : ∀ (o : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true))
    (ι : Fin 1 → Fin gates.length)
    (hι : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → ∃ r : Fin 1, ι r = q)
    (I : Finset (Fin gates.length))
    (hI : ∀ q2 : Fin gates.length, ((gates.get q2).op = GateOp.and ∨
      (gates.get q2).op = GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) :
    ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin 1, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card ≤ I.card ∧ (∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, x2 v2 = true)) ∧ (∀ jr : Fin gl.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gl.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gl.length, (∃ oq : Fin m, ol oq = n + jr3.val) ∨ ∃ kr : Fin gl.length, ((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gl.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gl.get kr).inputs)) ∧ (∀ jr4 : Fin gl.length, ((gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gl.get jr4).inputs = [ar, br]) := by
  have hcnt : gates.countP two ≤ I.card := by
    rw [← cnt gates two]
    apply Finset.card_le_card
    intro q hq
    rw [Finset.mem_filter] at hq
    exact hI q ((two_iff _).mp hq.2)
  have hnot : gates.countP isNot ≤ 1 := by
    rw [← cnt gates isNot]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    obtain ⟨r, hr⟩ := hι a ((isNot_iff _).mp ha.2)
    obtain ⟨s, hs⟩ := hι b ((isNot_iff _).mp hb.2)
    rw [← hr, ← hs, Subsingleton.elim r s]
  obtain ⟨gl, ol, hv, h1, h2, h3, h4⟩ := main S hS I.card _ gates out rfl ⟨hg, hnot, hcnt, hsem⟩
  have hpos := gl_pos S hS I.card gl ol hv ⟨0, hm⟩
  classical
  refine ⟨gl, ol, fun _ => if h : ∃ q : Fin gl.length, (gl.get q).op = GateOp.not then h.choose
    else ⟨0, hpos⟩, Finset.univ.filter (fun q => two (gl.get q) = true), hv.1, ?_, ?_, ?_,
    hv.2.2.2, h1, h2, h3, h4⟩
  · intro q3 hq
    refine ⟨0, ?_⟩
    have hex : ∃ q : Fin gl.length, (gl.get q).op = GateOp.not := ⟨q3, hq⟩
    simp only [hex, ↓reduceDIte]
    have h5 := hv.2.1
    rw [← cnt gl isNot] at h5
    exact Finset.card_le_one.mp h5 _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (isNot_iff _).mpr hex.choose_spec⟩) _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (isNot_iff _).mpr hq⟩)
  · intro q4 hq4
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (two_iff _).mpr hq4⟩
  · rw [cnt]
    exact hv.2.2.1

end PEqualNP.Outside.L_meta_1346

theorem PEqualNP.Outside.L_meta_1346 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ ic : Fin m, 2 ≤ (S ic).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → (∃ c : PEqualNP.CircuitLowerBounds.GateOp, (c = PEqualNP.CircuitLowerBounds.GateOp.and ∨ c = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (o1 : Fin m) (x1 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set (ι 0).val ⟨c, []⟩, out o1⟩ (List.ofFn x1) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o1⟩ (List.ofFn x1)) ∨ ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin 1, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card ≤ I.card ∧ (∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, x2 v2 = true)) ∧ (∀ jr : Fin gl.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gl.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gl.length, (∃ oq : Fin m, ol oq = n + jr3.val) ∨ ∃ kr : Fin gl.length, ((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gl.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gl.get kr).inputs)) ∧ (∀ jr4 : Fin gl.length, ((gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gl.get jr4).inputs = [ar, br]) := by
  intro n m S hS gates out hg hsem ι hι I hI
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact Or.inl ⟨PEqualNP.CircuitLowerBounds.GateOp.and, Or.inl rfl, fun o => o.elim0⟩
  · exact Or.inr (PEqualNP.Outside.L_meta_1346.finish n m S hS hm gates out hg hsem ι hι I hI)
