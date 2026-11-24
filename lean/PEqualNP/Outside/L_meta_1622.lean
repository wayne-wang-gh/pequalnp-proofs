import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_1622

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def dflt : Gate := Gate.mk GateOp.or []

-- generic gate-list fold
def run {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem run_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    run f (gs ++ [g]) w = run f gs w ++ [f (run f gs w) g] := by
  simp [run]

theorem run_append {α : Type} (f : List α → Gate → α) (g1 g2 : List Gate) (w : List α) :
    run f (g1 ++ g2) w = run f g2 (run f g1 w) := by
  simp [run]

theorem run_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (run f gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem run_lt {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α) (i : ℕ)
    (h : i < w.length) : (run f gs w).getD i d = w.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih]

theorem run_gate {α : Type} (f : List α → Gate → α) (d : α)
    (hf : ∀ (g : Gate) (w w' : List α), (∀ i ∈ g.inputs, w.getD i d = w'.getD i d) → f w g = f w' g)
    (gs : List Gate) (w : List α) (L : ℕ) (hL : w.length = L) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k dflt).inputs, i < L + k) :
    (run f gs w).getD (L + k) d = f (run f gs w) (gs.getD k dflt) := by
  subst hL
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g ih =>
    rw [run_snoc]
    rcases Nat.lt_or_ge k gs.length with h | h
    · have e : (gs ++ [g]).getD k dflt = gs.getD k dflt := getD_app_lt _ _ _ _ h
      rw [e] at hr ⊢
      rw [getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih h hr]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)
    · have hk' : k = gs.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst hk'
      have e : (gs ++ [g]).getD gs.length dflt = g := getD_app_len _ _ _
      rw [e] at hr ⊢
      have e2 : w.length + gs.length = (run f gs w).length := (run_length f gs w).symm
      rw [e2, getD_app_len]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)

def evf (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def ldf (d : List ℕ) (g : Gate) : ℕ := g.lineDegree d

theorem evf_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : evf w g = evf w' g := by
  unfold evf
  rw [List.map_congr_left h]

theorem ldf_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : ldf w g = ldf w' g := by
  unfold ldf Gate.lineDegree
  rw [List.map_congr_left h]

-- reads-back for bare lists
def RBL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j dflt).inputs, i < n + j

theorem RBL_append (n : ℕ) (g1 g2 : List Gate) (h1 : RBL n g1) (h2 : RBL (n + g1.length) g2) :
    RBL n (g1 ++ g2) := by
  intro j hj i hi
  rcases Nat.lt_or_ge j g1.length with h | h
  · rw [getD_app_lt _ _ _ _ h] at hi
    exact h1 j h i hi
  · rw [List.getD_append_right _ _ _ _ h] at hi
    simp only [List.length_append] at hj
    have := h2 (j - g1.length) (by omega) i hi
    omega

theorem RBL_empty (n : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, g.inputs = []) : RBL n gs := by
  intro j hj i hi
  have hm : gs.getD j dflt ∈ gs := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  rw [h _ hm] at hi
  simp at hi

theorem RBL_snoc (n : ℕ) (gs : List Gate) (g : Gate) (h1 : RBL n gs)
    (h2 : ∀ i ∈ g.inputs, i < n + gs.length) : RBL n (gs ++ [g]) := by
  apply RBL_append _ _ _ h1
  intro j hj i hi
  simp only [List.length_singleton] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  have := h2 i (by simpa using hi)
  omega

-- the state of the reverse pass: accumulator wire per wire, and the appended gates
def Good (B : ℕ) (st : (ℕ → ℕ) × List Gate) : Prop :=
  (∀ w, st.1 w < B + st.2.length) ∧
  (∀ g ∈ st.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  RBL B st.2

def link (B : ℕ) (st : (ℕ → ℕ) × List Gate) (a src : ℕ) : (ℕ → ℕ) × List Gate :=
  (Function.update st.1 a (B + st.2.length), st.2 ++ [Gate.mk GateOp.or [st.1 a, src]])

def andl (B : ℕ) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ) : (ℕ → ℕ) × List Gate :=
  link B (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) tgt (B + st.2.length)

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def proc (B : ℕ) (deg : List ℕ) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) : (ℕ → ℕ) × List Gate :=
  if 0 < deg.getD W 0 then
    if isAnd op = true ∧ l.length = 2 then
      if 0 < deg.getD (l.getD 0 0) 0 then andl B st W (l.getD 0 0) (l.getD 1 0)
      else andl B st W (l.getD 1 0) (l.getD 0 0)
    else l.foldl (fun s a => link B s a (st.1 W)) st
  else st

def aval (base : List Bool) (st : (ℕ → ℕ) × List Gate) (w : ℕ) : Bool :=
  (run evf st.2 base).getD (st.1 w) false

theorem link_spec (B : ℕ) (base : List Bool) (st : (ℕ → ℕ) × List Gate) (a src : ℕ)
    (hB : base.length = B) (hg : Good B st) (hs : src < B + st.2.length) :
    Good B (link B st a src) ∧ (link B st a src).2.length = st.2.length + 1 ∧
    (∀ i < B + st.2.length,
      (run evf (link B st a src).2 base).getD i false = (run evf st.2 base).getD i false) ∧
    ∀ w, aval base (link B st a src) w =
      (aval base st w || (decide (w = a) && (run evf st.2 base).getD src false)) := by
  obtain ⟨g1, g2, g3⟩ := hg
  have hlen : (run evf st.2 base).length = B + st.2.length := by rw [run_length, hB]
  have hrun : run evf (link B st a src).2 base = run evf st.2 base ++
      [((run evf st.2 base).getD (st.1 a) false || (run evf st.2 base).getD src false)] := by
    simp [link, run_snoc, evf, GateOp.eval]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w
    simp only [link, List.length_append, List.length_singleton, Function.update_apply]
    split_ifs
    · omega
    · have := g1 w
      omega
  · intro g hg
    simp only [link, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact g2 g hg
    · exact ⟨Or.inr rfl, by simp⟩
  · apply RBL_snoc _ _ _ g3
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact g1 a
    · exact hs
  · simp [link]
  · intro i hi
    rw [hrun]
    exact getD_app_lt _ _ _ _ (by omega)
  · intro w
    unfold aval
    rw [hrun]
    by_cases hw : w = a
    · subst hw
      have e : (link B st w src).1 w = (run evf st.2 base).length := by simp [link, hlen]
      rw [e, getD_app_len]
      simp
    · have e : (link B st a src).1 w = st.1 w := by simp [link, hw]
      rw [e, getD_app_lt _ _ _ _ (by have := g1 w; omega)]
      simp [hw]

theorem ite_p {α : Type} (c : Prop) [Decidable c] (a b : α) (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_n {α : Type} (c : Prop) [Decidable c] (a b : α) (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem bool_aux (p q r s : Bool) : ((p || (q && s)) || (r && s)) = (p || ((q || r) && s)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem fold_spec (B : ℕ) (base : List Bool) (src : ℕ) (hB : base.length = B) (l : List ℕ) :
    ∀ (st : (ℕ → ℕ) × List Gate), Good B st → src < B + st.2.length →
    Good B (l.foldl (fun s a => link B s a src) st) ∧
    (l.foldl (fun s a => link B s a src) st).2.length = st.2.length + l.length ∧
    (∀ i < B + st.2.length,
      (run evf (l.foldl (fun s a => link B s a src) st).2 base).getD i false =
        (run evf st.2 base).getD i false) ∧
    ∀ w, aval base (l.foldl (fun s a => link B s a src) st) w =
      (aval base st w || (decide (w ∈ l) && (run evf st.2 base).getD src false)) := by
  induction l with
  | nil =>
    intro st hg _
    simp [hg]
  | cons a l ih =>
    intro st hg hs
    obtain ⟨k1, k2, k3, k4⟩ := link_spec B base st a src hB hg hs
    obtain ⟨j1, j2, j3, j4⟩ := ih (link B st a src) k1 (by omega)
    rw [List.foldl_cons]
    refine ⟨j1, ?_, ?_, ?_⟩
    · rw [j2, k2, List.length_cons]
      omega
    · intro i hi
      rw [j3 i (by omega), k3 i hi]
    · intro w
      rw [j4 w, k4 w, k3 src hs, bool_aux]
      congr 2
      simp [Bool.decide_or]

theorem andl_spec (B : ℕ) (base : List Bool) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ)
    (hB : base.length = B) (hg : Good B st) (hs : side < B) :
    Good B (andl B st W tgt side) ∧ (andl B st W tgt side).2.length = st.2.length + 2 ∧
    ∀ w, aval base (andl B st W tgt side) w =
      (aval base st w || (decide (w = tgt) && (aval base st W && base.getD side false))) := by
  have hg' := hg
  obtain ⟨g1, g2, g3⟩ := hg
  have hlen : (run evf st.2 base).length = B + st.2.length := by rw [run_length, hB]
  have hrun : run evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base = run evf st.2 base ++
      [((run evf st.2 base).getD (st.1 W) false && (run evf st.2 base).getD side false)] := by
    simp [run_snoc, evf, GateOp.eval]
  have hg1 : Good B (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      have := g1 w
      show st.1 w < B + (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]).length
      simp only [List.length_append, List.length_singleton]
      omega
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact g2 g hg
      · exact ⟨Or.inl rfl, by simp⟩
    · apply RBL_snoc _ _ _ g3
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h
      · rw [h]; exact g1 W
      · rw [h]; omega
  obtain ⟨k1, k2, _, k4⟩ := link_spec B base (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]])
    tgt (B + st.2.length) hB hg1 (by simp)
  refine ⟨k1, ?_, ?_⟩
  · unfold andl
    rw [k2]
    simp
  · intro w
    unfold andl
    rw [k4 w]
    have e1 : aval base (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) w = aval base st w := by
      unfold aval
      show (run evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base).getD (st.1 w) false = _
      rw [hrun]
      exact getD_app_lt _ _ _ _ (by have := g1 w; omega)
    have e2 : (run evf (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]).2 base).getD
        (B + st.2.length) false = (aval base st W && base.getD side false) := by
      show (run evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base).getD _ _ = _
      rw [hrun, ← hlen, getD_app_len]
      unfold aval
      rw [run_lt evf st.2 base false side (by omega)]
    rw [e1, e2]

-- the logical invariant of the reverse pass
def Tinv (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (bound : ℕ) (A : ℕ → Bool) : Prop :=
  (∀ w < bound, Dp w → A w = true → u w = true → uo = true) ∧
  (∀ w < bound, Dp w → A w = true → v w = true → vo = true) ∧
  (uo = true → vo = true ∨ ∃ w < bound, Dp w ∧ A w = true ∧ u w = true)

theorem tinv_skip (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W : ℕ) (A : ℕ → Bool)
    (hD : ¬ Dp W) (hI : Tinv Dp u v uo vo (W + 1) A) : Tinv Dp u v uo vo W A := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨fun w hw => h1 w (by omega), fun w hw => h2 w (by omega), ?_⟩
  intro huo
  rcases h3 huo with h | ⟨w, hw, hd, ha, hz⟩
  · left; exact h
  · right
    refine ⟨w, ?_, hd, ha, hz⟩
    rcases Nat.lt_or_ge w W with hlt | hge
    · exact hlt
    · have e : w = W := by omega
      subst e
      exact absurd hd hD

theorem tinv_or (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W : ℕ) (l : List ℕ)
    (A A' : ℕ → Bool) (hr : ∀ i ∈ l, i < W) (hD : Dp W)
    (hA : ∀ w, A' w = (A w || (decide (w ∈ l) && A W)))
    (hx : ∀ w, ¬ Dp w → u w = v w)
    (p1u : ∀ i ∈ l, u i = true → u W = true) (p1v : ∀ i ∈ l, v i = true → v W = true)
    (p2 : u W = true → v W = true ∨ ∃ i ∈ l, u i = true)
    (hI : Tinv Dp u v uo vo (W + 1) A) : Tinv Dp u v uo vo W A' := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW⟩
    · exact h1 w (by omega) hd ha hz
    · exact h1 W (by omega) hD haW (p1u w hm hz)
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW⟩
    · exact h2 w (by omega) hd ha hz
    · exact h2 W (by omega) hD haW (p1v w hm hz)
  · intro huo
    rcases h3 huo with h | ⟨w, hw, hd, ha, hz⟩
    · left; exact h
    · rcases Nat.lt_or_ge w W with hlt | hge
      · right
        exact ⟨w, hlt, hd, by rw [hA, ha]; rfl, hz⟩
      · have e : w = W := by omega
        subst e
        rcases p2 hz with hvW | ⟨i, hi, hui⟩
        · left; exact h2 w (by omega) hd ha hvW
        · by_cases hdi : Dp i
          · right
            exact ⟨i, hr i hi, hdi, by simp [hA, hi, ha], hui⟩
          · left
            have e := hx i hdi
            exact h2 w (by omega) hd ha (p1v i hi (by rw [← e]; exact hui))

theorem tinv_and (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W tgt side : ℕ)
    (A A' : ℕ → Bool) (ht : tgt < W) (hD : Dp W) (hs : ¬ Dp side)
    (hA : ∀ w, A' w = (A w || (decide (w = tgt) && (A W && v side))))
    (hx : ∀ w, ¬ Dp w → u w = v w)
    (hu : u W = (u tgt && u side)) (hv : v W = (v tgt && v side))
    (hI : Tinv Dp u v uo vo (W + 1) A) : Tinv Dp u v uo vo W A' := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hsd := hx side hs
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW, hvs⟩
    · exact h1 w (by omega) hd ha hz
    · subst hm
      exact h1 W (by omega) hD haW (by rw [hu, hz, hsd, hvs]; rfl)
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW, hvs⟩
    · exact h2 w (by omega) hd ha hz
    · subst hm
      exact h2 W (by omega) hD haW (by rw [hv, hz, hvs]; rfl)
  · intro huo
    rcases h3 huo with h | ⟨w, hw, hd, ha, hz⟩
    · left; exact h
    · rcases Nat.lt_or_ge w W with hlt | hge
      · right
        exact ⟨w, hlt, hd, by rw [hA, ha]; rfl, hz⟩
      · have e : w = W := by omega
        subst e
        rw [hu] at hz
        simp only [Bool.and_eq_true] at hz
        have hvs : v side = true := by rw [← hsd]; exact hz.2
        by_cases hdt : Dp tgt
        · right
          exact ⟨tgt, ht, hdt, by simp [hA, ha, hvs], hz.1⟩
        · left
          have e := hx tgt hdt
          exact h2 w (by omega) hd ha (by rw [hv, ← e, hz.1, hvs]; rfl)

theorem fold_case (B : ℕ) (deg : List ℕ) (base : List Bool) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hB : base.length = B) (hl : l.length ≤ 2)
    (hr : ∀ i ∈ l, i < W) (hg : Good B st) (hD : 0 < deg.getD W 0) :
    Good B (l.foldl (fun s a => link B s a (st.1 W)) st) ∧
    (l.foldl (fun s a => link B s a (st.1 W)) st).2.length ≤ st.2.length + 2 ∧
    ∀ (u v : ℕ → Bool) (uo vo : Bool), (∀ w, ¬ 0 < deg.getD w 0 → u w = v w) →
      (∀ i ∈ l, u i = true → u W = true) → (∀ i ∈ l, v i = true → v W = true) →
      (u W = true → v W = true ∨ ∃ i ∈ l, u i = true) →
      Tinv (fun w => 0 < deg.getD w 0) u v uo vo (W + 1) (aval base st) →
      Tinv (fun w => 0 < deg.getD w 0) u v uo vo W
        (aval base (l.foldl (fun s a => link B s a (st.1 W)) st)) := by
  obtain ⟨j1, j2, _, j4⟩ := fold_spec B base (st.1 W) hB l st hg (hg.1 W)
  refine ⟨j1, by omega, ?_⟩
  intro u v uo vo hx p1u p1v p2 hI
  exact tinv_or _ u v uo vo W l _ _ hr hD j4 hx p1u p1v p2 hI

theorem proc_spec (B : ℕ) (deg : List ℕ) (base : List Bool) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hB : base.length = B) (hW : W < B)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2) (hr : ∀ i ∈ l, i < W)
    (hc : op = GateOp.and → l.length = 2 → ∃ i ∈ l, deg.getD i 0 = 0)
    (hg : Good B st) :
    Good B (proc B deg op l W st) ∧
    (proc B deg op l W st).2.length ≤ st.2.length + (if 0 < deg.getD W 0 then 2 else 0) ∧
    ∀ (u v : ℕ → Bool) (uo vo : Bool),
      (∀ i < W, ¬ 0 < deg.getD i 0 → base.getD i false = v i) →
      u W = op.eval (l.map u) → v W = op.eval (l.map v) →
      (∀ w, ¬ 0 < deg.getD w 0 → u w = v w) →
      Tinv (fun w => 0 < deg.getD w 0) u v uo vo (W + 1) (aval base st) →
      Tinv (fun w => 0 < deg.getD w 0) u v uo vo W (aval base (proc B deg op l W st)) := by
  by_cases hD : 0 < deg.getD W 0
  · rcases hop with rfl | rfl
    · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · have e : proc B deg GateOp.and [] W st
            = ([] : List ℕ).foldl (fun s a => link B s a (st.1 W)) st := by
          unfold proc
          rw [ite_p _ _ _ hD, ite_n _ _ _ (by simp)]
        rw [e]
        obtain ⟨f1, f2, f3⟩ := fold_case B deg base [] W st hB hl hr hg hD
        refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
        intro u v uo vo _ hu hv hx hI
        refine f3 u v uo vo hx (by simp) (by simp) ?_ hI
        intro _
        left
        simpa [GateOp.eval] using hv
      · have e : proc B deg GateOp.and [a] W st
            = [a].foldl (fun s a => link B s a (st.1 W)) st := by
          unfold proc
          rw [ite_p _ _ _ hD, ite_n _ _ _ (by simp)]
        rw [e]
        obtain ⟨f1, f2, f3⟩ := fold_case B deg base [a] W st hB hl hr hg hD
        refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
        intro u v uo vo _ hu hv hx hI
        have hu' : u W = u a := by simpa [GateOp.eval] using hu
        have hv' : v W = v a := by simpa [GateOp.eval] using hv
        refine f3 u v uo vo hx ?_ ?_ ?_ hI
        · intro i hi h
          simp only [List.mem_singleton] at hi
          subst hi
          rw [hu']; exact h
        · intro i hi h
          simp only [List.mem_singleton] at hi
          subst hi
          rw [hv']; exact h
        · intro h
          right
          exact ⟨a, by simp, by rw [← hu']; exact h⟩
      · have e : proc B deg GateOp.and [a, b] W st
            = if 0 < deg.getD a 0 then andl B st W a b else andl B st W b a := by
          unfold proc
          rw [ite_p _ _ _ hD, ite_p _ _ _ (by simp [isAnd])]
          rfl
        have ha : a < W := hr a (by simp)
        have hb : b < W := hr b (by simp)
        obtain ⟨i, hi, hi0⟩ := hc rfl rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rw [e]
        by_cases hda : 0 < deg.getD a 0
        · simp only [hda, ↓reduceIte]
          have hdb : ¬ 0 < deg.getD b 0 := by
            rcases hi with h | h
            · rw [h] at hi0; omega
            · rw [h] at hi0; omega
          obtain ⟨k1, k2, k3⟩ := andl_spec B base st W a b hB hg (by omega)
          refine ⟨k1, by simp only [hD, ↓reduceIte]; omega, ?_⟩
          intro u v uo vo hbv hu hv hx hI
          have hu' : u W = (u a && u b) := by simpa [GateOp.eval] using hu
          have hv' : v W = (v a && v b) := by simpa [GateOp.eval] using hv
          refine tinv_and _ u v uo vo W a b _ _ ha hD hdb ?_ hx hu' hv' hI
          intro w
          rw [k3 w, hbv b hb hdb]
        · simp only [hda, ↓reduceIte]
          obtain ⟨k1, k2, k3⟩ := andl_spec B base st W b a hB hg (by omega)
          refine ⟨k1, by simp only [hD, ↓reduceIte]; omega, ?_⟩
          intro u v uo vo hbv hu hv hx hI
          have hu' : u W = (u b && u a) := by
            rw [Bool.and_comm]; simpa [GateOp.eval] using hu
          have hv' : v W = (v b && v a) := by
            rw [Bool.and_comm]; simpa [GateOp.eval] using hv
          refine tinv_and _ u v uo vo W b a _ _ hb hD hda ?_ hx hu' hv' hI
          intro w
          rw [k3 w, hbv a ha hda]
      · simp at hl
    · have e : proc B deg GateOp.or l W st
          = l.foldl (fun s a => link B s a (st.1 W)) st := by
        unfold proc
        rw [ite_p _ _ _ hD, ite_n _ _ _ (by simp [isAnd])]
      rw [e]
      obtain ⟨f1, f2, f3⟩ := fold_case B deg base l W st hB hl hr hg hD
      refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
      intro u v uo vo _ hu hv hx hI
      have hu' : u W = true ↔ ∃ i ∈ l, u i = true := by
        rw [hu]; simp [GateOp.eval]
      have hv' : v W = true ↔ ∃ i ∈ l, v i = true := by
        rw [hv]; simp [GateOp.eval]
      refine f3 u v uo vo hx ?_ ?_ ?_ hI
      · intro i hi h
        exact hu'.2 ⟨i, hi, h⟩
      · intro i hi h
        exact hv'.2 ⟨i, hi, h⟩
      · intro h
        right
        exact hu'.1 h
  · have e : proc B deg op l W st = st := by
      unfold proc
      rw [ite_n _ _ _ hD]
    rw [e]
    refine ⟨hg, by simp, ?_⟩
    intro u v uo vo _ _ _ _ hI
    exact tinv_skip _ u v uo vo W _ hD hI

-- the reverse pass over the gate list, last gate first
def stAt (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate) :
    ℕ → (ℕ → ℕ) × List Gate
  | 0 => st0
  | d + 1 => proc B deg (gs.getD (gs.length - 1 - d) dflt).op
      (gs.getD (gs.length - 1 - d) dflt).inputs (N + (gs.length - 1 - d)) (stAt B N deg gs st0 d)

def cnt (N : ℕ) (deg : List ℕ) (b : ℕ) : ℕ :=
  ((Finset.range b).filter (fun k => 0 < deg.getD (N + k) 0)).card

theorem cnt_succ (N : ℕ) (deg : List ℕ) (b : ℕ) :
    cnt N deg (b + 1) = cnt N deg b + (if 0 < deg.getD (N + b) 0 then 1 else 0) := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

def GateHyp (N : ℕ) (deg : List ℕ) (gs : List Gate) : Prop :=
  ∀ k < gs.length, ((gs.getD k dflt).op = GateOp.and ∨ (gs.getD k dflt).op = GateOp.or) ∧
    (gs.getD k dflt).inputs.length ≤ 2 ∧ (∀ i ∈ (gs.getD k dflt).inputs, i < N + k) ∧
    ((gs.getD k dflt).op = GateOp.and → (gs.getD k dflt).inputs.length = 2 →
      ∃ i ∈ (gs.getD k dflt).inputs, deg.getD i 0 = 0)

theorem iter_good (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (hNB : N + gs.length ≤ B) (hgs : GateHyp N deg gs) (hg0 : Good B st0) :
    ∀ d ≤ gs.length, Good B (stAt B N deg gs st0 d) ∧
      (stAt B N deg gs st0 d).2.length + 2 * cnt N deg (gs.length - d)
        ≤ st0.2.length + 2 * cnt N deg gs.length := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨hg0, by simp [stAt]⟩
  | succ d ih =>
    intro hd
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, k = gs.length - 1 - d := ⟨_, rfl⟩
    have hks : k < gs.length := by omega
    obtain ⟨a1, a2, a3, a4⟩ := hgs k hks
    have e : stAt B N deg gs st0 (d + 1) = proc B deg (gs.getD k dflt).op
        (gs.getD k dflt).inputs (N + k) (stAt B N deg gs st0 d) := by
      rw [hk]; rfl
    obtain ⟨p1, p2, _⟩ := proc_spec B deg (List.replicate B false) (gs.getD k dflt).op
      (gs.getD k dflt).inputs (N + k) (stAt B N deg gs st0 d) List.length_replicate
      (by omega) a1 a2 a3 a4 i1
    rw [e]
    refine ⟨p1, ?_⟩
    have e1 : gs.length - d = k + 1 := by omega
    have e2 : gs.length - (d + 1) = k := by omega
    rw [e1, cnt_succ] at i2
    rw [e2]
    split_ifs at p2 i2 <;> omega

theorem iter_inv (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (base : List Bool) (u v : ℕ → Bool) (uo vo : Bool)
    (hB : base.length = B) (hNB : N + gs.length ≤ B) (hgs : GateHyp N deg gs) (hg0 : Good B st0)
    (hv : ∀ i < N + gs.length, ¬ 0 < deg.getD i 0 → base.getD i false = v i)
    (hu : ∀ k < gs.length, u (N + k) = (gs.getD k dflt).op.eval ((gs.getD k dflt).inputs.map u))
    (hvv : ∀ k < gs.length, v (N + k) = (gs.getD k dflt).op.eval ((gs.getD k dflt).inputs.map v))
    (hx : ∀ w, ¬ 0 < deg.getD w 0 → u w = v w)
    (hI : Tinv (fun w => 0 < deg.getD w 0) u v uo vo (N + gs.length) (aval base st0)) :
    ∀ d ≤ gs.length, Tinv (fun w => 0 < deg.getD w 0) u v uo vo (N + (gs.length - d))
      (aval base (stAt B N deg gs st0 d)) := by
  intro d
  induction d with
  | zero =>
    intro _
    simpa [stAt] using hI
  | succ d ih =>
    intro hd
    have i1 := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, k = gs.length - 1 - d := ⟨_, rfl⟩
    have hks : k < gs.length := by omega
    obtain ⟨a1, a2, a3, a4⟩ := hgs k hks
    have e : stAt B N deg gs st0 (d + 1) = proc B deg (gs.getD k dflt).op
        (gs.getD k dflt).inputs (N + k) (stAt B N deg gs st0 d) := by
      rw [hk]; rfl
    obtain ⟨_, _, p3⟩ := proc_spec B deg base (gs.getD k dflt).op
      (gs.getD k dflt).inputs (N + k) (stAt B N deg gs st0 d) hB
      (by omega) a1 a2 a3 a4 (iter_good B N deg gs st0 hNB hgs hg0 d (by omega)).1
    have e1 : gs.length - d = k + 1 := by omega
    have e2 : gs.length - (d + 1) = k := by omega
    rw [e1] at i1
    rw [e, e2]
    exact p3 u v uo vo (fun i hi => hv i (by omega)) (hu k hks) (hvv k hks) hx i1

-- wire values and degrees of the given circuit
def wv (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD w false

theorem wires_run (C : Circuit) (inp : List Bool) : C.wires inp = run evf C.gates inp := rfl

theorem wv_input (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : w < N) :
    wv C N z w = z ⟨w, h⟩ := by
  unfold wv
  rw [wires_run, run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem wv_ge (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : N + C.gates.length ≤ w) :
    wv C N z w = false := by
  unfold wv
  rw [wires_run]
  exact getD_ge _ _ _ (by rw [run_length]; simpa using h)

theorem wv_gate (C : Circuit) (N : ℕ) (z : Fin N → Bool) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    wv C N z (N + k) = (C.gates.getD k dflt).op.eval ((C.gates.getD k dflt).inputs.map (wv C N z)) := by
  unfold wv
  rw [wires_run]
  exact run_gate evf false evf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem deg_run (C : Circuit) (N : ℕ) (M : Finset ℕ) : C.lineDegrees N M =
    run ldf C.gates ((List.range N).map fun i => if i ∈ M then 1 else 0) := rfl

theorem deg_input (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : w < N) :
    (C.lineDegrees N M).getD w 0 = if w ∈ M then 1 else 0 := by
  rw [deg_run, run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem deg_ge (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : N + C.gates.length ≤ w) :
    (C.lineDegrees N M).getD w 0 = 0 := by
  rw [deg_run]
  exact getD_ge _ _ _ (by rw [run_length]; simpa using h)

theorem deg_gate (C : Circuit) (N : ℕ) (M : Finset ℕ) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.lineDegrees N M).getD (N + k) 0 = (C.gates.getD k dflt).lineDegree (C.lineDegrees N M) := by
  rw [deg_run]
  exact run_gate ldf 0 ldf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem app_lt {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : w < n) : Fin.append x y ⟨w, h⟩ = x ⟨w, hw⟩ :=
  Fin.append_left x y ⟨w, hw⟩

theorem app_ge {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : n ≤ w) : Fin.append x y ⟨w, h⟩ = y ⟨w - n, by omega⟩ := by
  have e : (⟨w, h⟩ : Fin (n + m)) = Fin.natAdd n ⟨w - n, by omega⟩ := by
    ext
    simp only [Fin.natAdd_mk]
    omega
  rw [e, Fin.append_right]

theorem gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : C.gates.getD k dflt ∈ C.gates := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem gate_ops (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((C.gates.getD k dflt).op = GateOp.and ∨ (C.gates.getD k dflt).op = GateOp.or) ∧
    (C.gates.getD k dflt).inputs.length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hM _ (gate_mem C k hk)
  refine ⟨?_, h2⟩
  simpa using h1

-- forward pass: wires of degree zero ignore the line inputs, and all wires are monotone in them
theorem fwd (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) :
    ((C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 = 0 →
      wv C (n + m) (Fin.append x y) w = wv C (n + m) (Fin.append x (fun _ => false)) w) ∧
    (wv C (n + m) (Fin.append x (fun _ => false)) w = true →
      wv C (n + m) (Fin.append x y) w = true) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w (n + m) with h | h
    · rw [wv_input _ _ _ _ h, wv_input _ _ _ _ h, deg_input _ _ _ _ h]
      rcases Nat.lt_or_ge w n with hw | hw
      · rw [app_lt _ _ _ _ hw, app_lt _ _ _ _ hw]
        exact ⟨fun _ => rfl, fun h => h⟩
      · rw [app_ge _ (fun _ => false) _ _ hw]
        have : w ∈ Finset.Ico n (n + m) := by simp; omega
        simp [this]
    · rcases Nat.lt_or_ge (w - (n + m)) C.gates.length with hk | hk
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + m + k := ⟨w - (n + m), by omega⟩
        have hk' : k < C.gates.length := by omega
        have hu := wv_gate C (n + m) (Fin.append x y) hR k hk'
        have hv := wv_gate C (n + m) (Fin.append x (fun _ => false)) hR k hk'
        have hd := deg_gate C (n + m) (Finset.Ico n (n + m)) hR k hk'
        have hr : ∀ i ∈ (C.gates.getD k dflt).inputs, i < n + m + k := hR k hk'
        obtain ⟨hop, hl⟩ := gate_ops C hM k hk'
        generalize C.gates.getD k dflt = g at hu hv hd hr hop hl
        obtain ⟨op, l⟩ := g
        simp only at hop hl hr
        rw [hu, hv, hd]
        rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · rcases hop with rfl | rfl <;> simp [GateOp.eval]
        · obtain ⟨a1, a2⟩ := ih a (hr a (by simp))
          rcases hop with rfl | rfl
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.all_cons,
              List.all_nil, id, Bool.and_true, ↓reduceIte, add_zero]
            exact ⟨a1, a2⟩
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.any_cons,
              List.any_nil, id, Bool.or_false, reduceCtorEq, ↓reduceIte, Nat.max_zero]
            exact ⟨a1, a2⟩
        · obtain ⟨a1, a2⟩ := ih a (hr a (by simp))
          obtain ⟨b1, b2⟩ := ih b (hr b (by simp))
          rcases hop with rfl | rfl
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.all_cons,
              List.all_nil, id, Bool.and_true, ↓reduceIte, add_zero]
            constructor
            · intro h0
              rw [a1 (by omega), b1 (by omega)]
            · intro hh
              simp only [Bool.and_eq_true] at hh ⊢
              exact ⟨a2 hh.1, b2 hh.2⟩
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.any_cons,
              List.any_nil, id, Bool.or_false, reduceCtorEq, ↓reduceIte, Nat.max_zero]
            constructor
            · intro h0
              rw [a1 (by omega), b1 (by omega)]
            · intro hh
              simp only [Bool.or_eq_true] at hh ⊢
              exact hh.imp a2 b2
        · simp at hl
      · rw [wv_ge _ _ _ _ (by omega), wv_ge _ _ _ _ (by omega)]
        exact ⟨fun _ => rfl, fun h => h⟩

theorem run_false (m : ℕ) (w : List Bool) :
    run evf (List.replicate m (Gate.mk GateOp.or [])) w = w ++ List.replicate m false := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    rw [List.replicate_succ', run_snoc, ih, List.replicate_succ', ← List.append_assoc]
    simp [evf, GateOp.eval]

theorem ofFn_app {n m : ℕ} (x : Fin n → Bool) :
    List.ofFn (Fin.append x (fun _ : Fin m => false)) = List.ofFn x ++ List.replicate m false := by
  rw [List.ofFn_fin_append, List.ofFn_const]

theorem ncard_cnt (N s : ℕ) (deg : List ℕ) :
    Set.ncard {j : ℕ | j < s ∧ 0 < deg.getD (N + j) 0} = cnt N deg s := by
  unfold cnt
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp

theorem gate_hyp (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (hX : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → (gateAt C j).inputs.length = 2 →
      ∃ i ∈ (gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) :
    GateHyp (n + m) (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates := by
  intro k hk
  obtain ⟨h1, h2⟩ := gate_ops C hM k hk
  exact ⟨h1, h2, hR k hk, hX k hk⟩

theorem tinv_init (Dp : ℕ → Prop) (u v : ℕ → Bool) (r bound : ℕ) (A : ℕ → Bool)
    (hA : ∀ w, A w = decide (w = r)) (hx : ∀ w, ¬ Dp w → u w = v w)
    (hb : u r = true → r < bound) :
    Tinv Dp u v (u r) (v r) bound A := by
  refine ⟨?_, ?_, ?_⟩
  · intro w _ _ ha hz
    rw [hA] at ha
    simp only [decide_eq_true_eq] at ha
    subst ha
    exact hz
  · intro w _ _ ha hz
    rw [hA] at ha
    simp only [decide_eq_true_eq] at ha
    subst ha
    exact hz
  · intro h
    by_cases hd : Dp r
    · right
      exact ⟨r, hb h, hd, by simp [hA], h⟩
    · left
      rw [← hx r hd]
      exact h

theorem main (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (hX : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → (gateAt C j).inputs.length = 2 →
      ∃ i ∈ (gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) :
    ∃ (D : Circuit) (o : Fin m → ℕ), Monotone2 D ∧ ReadsBack n D ∧
      D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧
        0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧
      ∀ (x : Fin n → Bool) (j : Fin m),
        circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) =
          (circuitFun (n + m) C (Fin.append x (fun _ => false)) ||
            (D.wires (List.ofFn x)).getD (o j) false) := by
  have hF := fun (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) => fwd n m C hM hR x y w
  have hcf : ∀ z : Fin (n + m) → Bool, circuitFun (n + m) C z = wv C (n + m) z C.output :=
    fun _ => rfl
  rw [ncard_cnt]
  by_cases hout : 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD C.output 0
  · rcases Nat.lt_or_ge C.output (n + m) with hlt | hge
    · -- the output is a line input
      have hdi := deg_input C (n + m) (Finset.Ico n (n + m)) C.output hlt
      have hn : n ≤ C.output := by
        by_contra hcon
        have : C.output ∉ Finset.Ico n (n + m) := by simp; omega
        rw [hdi] at hout
        simp [this] at hout
      refine ⟨Circuit.mk [Gate.mk GateOp.and []] 0,
        fun j => if n + j.val = C.output then n else n + 1, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg
        simp
      · show RBL n [Gate.mk GateOp.and []]
        exact RBL_empty _ _ (by simp)
      · simp only [Circuit.size, List.length_singleton]
        omega
      · intro x j
        rw [hcf, hcf, wv_input _ _ _ _ hlt, wv_input _ _ _ _ hlt, app_ge _ _ _ _ hn,
          app_ge _ _ _ _ hn]
        have hw : (Circuit.mk [Gate.mk GateOp.and []] 0).wires (List.ofFn x)
            = List.ofFn x ++ [true] := by
          simp [Circuit.wires, GateOp.eval]
        rw [hw]
        have hlen : (List.ofFn x).length = n := by simp
        by_cases hj : n + j.val = C.output
        · have e1 : (⟨C.output - n, by omega⟩ : Fin m) = j := by
            ext
            simp only
            omega
          have e2 : (List.ofFn x ++ [true]).getD n false = true := by
            have h2 := getD_app_len (List.ofFn x) true false
            rw [hlen] at h2
            exact h2
          simp only [hj, ↓reduceIte, e1]
          rw [e2]
          simp
        · have e1 : (⟨C.output - n, by omega⟩ : Fin m) ≠ j := by
            intro hcon
            apply hj
            rw [← hcon]
            simp only
            omega
          simp only [hj, ↓reduceIte, e1, decide_false]
          rw [getD_ge _ _ _ (by simp)]
          rfl
    · -- the output is a line-dependent gate: the reverse pass
      have hks : C.output - (n + m) < C.gates.length := by
        by_contra hcon
        rw [deg_ge _ _ _ _ (by omega)] at hout
        omega
      have hcpos : 1 ≤ cnt (n + m) (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates.length := by
        unfold cnt
        apply Finset.card_pos.mpr
        refine ⟨C.output - (n + m), ?_⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨hks, ?_⟩
        have e : n + m + (C.output - (n + m)) = C.output := by omega
        rw [e]
        exact hout
      have hgs := gate_hyp n m C hM hR hX
      have hg0 : Good (n + m + C.gates.length + 1)
          ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate)) := by
        refine ⟨?_, ?_, ?_⟩
        · intro w
          simp only [List.length_nil]
          split_ifs <;> omega
        · intro g hg
          simp at hg
        · intro j hj
          simp at hj
      obtain ⟨q1, q2⟩ := iter_good (n + m + C.gates.length + 1) (n + m)
        (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates _ (by omega) hgs hg0
        C.gates.length (le_refl _)
      obtain ⟨q11, q12, q13⟩ := q1
      refine ⟨Circuit.mk (List.replicate m (Gate.mk GateOp.or []) ++ (C.gates ++
        ([Gate.mk GateOp.and []] ++ (stAt (n + m + C.gates.length + 1) (n + m)
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates
          ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate))
          C.gates.length).2))) 0,
        fun j => (stAt (n + m + C.gates.length + 1) (n + m)
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates
          ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate))
          C.gates.length).1 (n + j.val), ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hg
        rcases hg with ⟨_, rfl⟩ | hg | rfl | hg
        · simp
        · exact hM g hg
        · simp
        · obtain ⟨h1, h2⟩ := q12 g hg
          refine ⟨?_, h2⟩
          rcases h1 with h1 | h1 <;> simp [h1]
      · show RBL n _
        apply RBL_append
        · exact RBL_empty _ _ (by
            intro g hg
            simp only [List.mem_replicate] at hg
            rw [hg.2])
        · rw [List.length_replicate]
          apply RBL_append _ _ _ hR
          apply RBL_append
          · exact RBL_empty _ _ (by simp)
          · exact q13
      · simp only [Circuit.size, List.length_append, List.length_replicate, List.length_singleton]
        simp only [List.length_nil] at q2
        omega
      · intro x j
        obtain ⟨st, hst⟩ : ∃ st, st = stAt (n + m + C.gates.length + 1) (n + m)
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates
          ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate))
          C.gates.length := ⟨_, rfl⟩
        rw [← hst]
        obtain ⟨base, hbase⟩ : ∃ base, base =
          C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false))) ++ [true] := ⟨_, rfl⟩
        have hvl : (C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false)))).length
            = n + m + C.gates.length := by
          rw [wires_run, run_length]
          simp
        have hBl : base.length = n + m + C.gates.length + 1 := by
          rw [hbase, List.length_append, hvl]
          rfl
        have hw : (Circuit.mk (List.replicate m (Gate.mk GateOp.or []) ++ (C.gates ++
            ([Gate.mk GateOp.and []] ++ st.2))) 0).wires (List.ofFn x) = run evf st.2 base := by
          rw [wires_run]
          simp only []
          rw [run_append, run_append, run_append, run_false, ← ofFn_app, hbase, wires_run]
          congr 1
        rw [hw, hcf, hcf]
        have hv : ∀ i < n + m + C.gates.length,
            base.getD i false = wv C (n + m) (Fin.append x (fun _ => false)) i := by
          intro i hi
          rw [hbase, getD_app_lt _ _ _ _ (by omega)]
          rfl
        have hT : base.getD (n + m + C.gates.length) false = true := by
          rw [hbase, ← hvl, getD_app_len]
        have hFl : base.getD n false = false := by
          rw [hv n (by have := j.isLt; omega), wv_input _ _ _ _ (by have := j.isLt; omega),
            app_ge _ _ _ _ (le_refl _)]
        have hx : ∀ w, ¬ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 →
            wv C (n + m) (Fin.append x (fun l => decide (l = j))) w
              = wv C (n + m) (Fin.append x (fun _ => false)) w := by
          intro w hw0
          exact (hF x _ w).1 (by omega)
        have hI0 := tinv_init (fun w => 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0)
          (wv C (n + m) (Fin.append x (fun l => decide (l = j))))
          (wv C (n + m) (Fin.append x (fun _ => false))) C.output (n + m + C.gates.length)
          (aval base ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate)))
          (by
            intro w
            unfold aval
            show (base).getD (if w = C.output then n + m + C.gates.length else n) false = _
            by_cases hwo : w = C.output
            · rw [ite_p _ _ _ hwo, hT]; simp [hwo]
            · rw [ite_n _ _ _ hwo, hFl]; simp [hwo])
          hx
          (by
            intro hu
            by_contra hcon
            rw [wv_ge _ _ _ _ (by omega)] at hu
            exact Bool.false_ne_true hu)
        have hfin := iter_inv (n + m + C.gates.length + 1) (n + m)
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates _ base _ _ _ _ hBl (by omega)
          hgs hg0 (fun i hi _ => hv i hi)
          (fun k hk => wv_gate C (n + m) _ hR k hk) (fun k hk => wv_gate C (n + m) _ hR k hk)
          hx hI0 C.gates.length (le_refl _)
        rw [← hst] at hfin
        obtain ⟨f1, _, f3⟩ := hfin
        have hjlt : n + j.val < n + m := by have := j.isLt; omega
        have hdj : 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + j.val) 0 := by
          rw [deg_input _ _ _ _ hjlt]
          have : n + j.val ∈ Finset.Ico n (n + m) := by simp
          simp [this]
        have huj : wv C (n + m) (Fin.append x (fun l => decide (l = j))) (n + j.val) = true := by
          rw [wv_input _ _ _ _ hjlt, app_ge _ _ _ _ (by omega)]
          simp only [decide_eq_true_eq]
          ext
          simp
        show _ = (_ || aval base st (n + j.val))
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true]
        constructor
        · intro huo
          rcases f3 huo with h | ⟨w, hw, hd, ha, hz⟩
          · left; exact h
          · right
            have hwN : w < n + m := by omega
            have hwn : n ≤ w := by
              by_contra hcon
              have hd' : 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 := hd
              rw [deg_input _ _ _ _ hwN] at hd'
              have : w ∉ Finset.Ico n (n + m) := by simp; omega
              simp [this] at hd'
            rw [wv_input _ _ _ _ hwN, app_ge _ _ _ _ hwn] at hz
            simp only [decide_eq_true_eq] at hz
            have e : w = n + j.val := by
              rw [← hz]
              simp only
              omega
            rw [← e]
            exact ha
        · rintro (h | h)
          · exact (hF x _ C.output).2 h
          · exact f1 (n + j.val) (by omega) hdj h huj
  · -- the output does not depend on the lines
    refine ⟨Circuit.mk [] 0, fun _ => n, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · intro j hj
      simp at hj
    · simp [Circuit.size]
    · intro x j
      rw [hcf, hcf, (hF x _ C.output).1 (by omega)]
      have : ((Circuit.mk [] 0).wires (List.ofFn x)).getD n false = false := by
        apply getD_ge
        simp [Circuit.wires]
      rw [this]
      simp

end PEqualNP.Outside.L_meta_1622

theorem PEqualNP.Outside.L_meta_1622 : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧ ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || (D.wires (List.ofFn x)).getD (o j) false) :=
  fun n m C hM hR hX => PEqualNP.Outside.L_meta_1622.main n m C hM hR hX
