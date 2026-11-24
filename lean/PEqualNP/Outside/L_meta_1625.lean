import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1625

section Sec1622

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace P1622

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

end P1622

theorem P1622_main : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧ ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || (D.wires (List.ofFn x)).getD (o j) false) :=
  fun n m C hM hR hX => PEqualNP.Outside.L_meta_1625.P1622.main n m C hM hR hX

end Sec1622

section Sec1623

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace P1623

theorem aj_getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem aj_getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem aj_getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def aj_dflt : Gate := Gate.mk GateOp.or []

-- generic gate-list fold
def aj_run {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem aj_run_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    aj_run f (gs ++ [g]) w = aj_run f gs w ++ [f (aj_run f gs w) g] := by
  simp [aj_run]

theorem aj_run_append {α : Type} (f : List α → Gate → α) (g1 g2 : List Gate) (w : List α) :
    aj_run f (g1 ++ g2) w = aj_run f g2 (aj_run f g1 w) := by
  simp [aj_run]

theorem aj_run_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (aj_run f gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [aj_run]
  | append_singleton gs g ih => rw [aj_run_snoc]; simp [ih]; omega

theorem aj_run_lt {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α) (i : ℕ)
    (h : i < w.length) : (aj_run f gs w).getD i d = w.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [aj_run_snoc, aj_getD_app_lt _ _ _ _ (by rw [aj_run_length]; omega), ih]

theorem aj_run_gate {α : Type} (f : List α → Gate → α) (d : α)
    (hf : ∀ (g : Gate) (w w' : List α), (∀ i ∈ g.inputs, w.getD i d = w'.getD i d) → f w g = f w' g)
    (gs : List Gate) (w : List α) (L : ℕ) (hL : w.length = L) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k aj_dflt).inputs, i < L + k) :
    (aj_run f gs w).getD (L + k) d = f (aj_run f gs w) (gs.getD k aj_dflt) := by
  subst hL
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g ih =>
    rw [aj_run_snoc]
    rcases Nat.lt_or_ge k gs.length with h | h
    · have e : (gs ++ [g]).getD k aj_dflt = gs.getD k aj_dflt := aj_getD_app_lt _ _ _ _ h
      rw [e] at hr ⊢
      rw [aj_getD_app_lt _ _ _ _ (by rw [aj_run_length]; omega), ih h hr]
      apply hf
      intro i hi
      symm
      exact aj_getD_app_lt _ _ _ _ (by rw [aj_run_length]; have := hr i hi; omega)
    · have hk' : k = gs.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst hk'
      have e : (gs ++ [g]).getD gs.length aj_dflt = g := aj_getD_app_len _ _ _
      rw [e] at hr ⊢
      have e2 : w.length + gs.length = (aj_run f gs w).length := (aj_run_length f gs w).symm
      rw [e2, aj_getD_app_len]
      apply hf
      intro i hi
      symm
      exact aj_getD_app_lt _ _ _ _ (by rw [aj_run_length]; have := hr i hi; omega)

def aj_evf (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def aj_ldf (d : List ℕ) (g : Gate) : ℕ := g.lineDegree d

theorem aj_evf_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : aj_evf w g = aj_evf w' g := by
  unfold aj_evf
  rw [List.map_congr_left h]

theorem aj_ldf_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : aj_ldf w g = aj_ldf w' g := by
  unfold aj_ldf Gate.lineDegree
  rw [List.map_congr_left h]

-- reads-back for bare lists
def aj_RBL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j aj_dflt).inputs, i < n + j

theorem aj_RBL_append (n : ℕ) (g1 g2 : List Gate) (h1 : aj_RBL n g1) (h2 : aj_RBL (n + g1.length) g2) :
    aj_RBL n (g1 ++ g2) := by
  intro j hj i hi
  rcases Nat.lt_or_ge j g1.length with h | h
  · rw [aj_getD_app_lt _ _ _ _ h] at hi
    exact h1 j h i hi
  · rw [List.getD_append_right _ _ _ _ h] at hi
    simp only [List.length_append] at hj
    have := h2 (j - g1.length) (by omega) i hi
    omega

theorem aj_RBL_empty (n : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, g.inputs = []) : aj_RBL n gs := by
  intro j hj i hi
  have hm : gs.getD j aj_dflt ∈ gs := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  rw [h _ hm] at hi
  simp at hi

theorem aj_RBL_snoc (n : ℕ) (gs : List Gate) (g : Gate) (h1 : aj_RBL n gs)
    (h2 : ∀ i ∈ g.inputs, i < n + gs.length) : aj_RBL n (gs ++ [g]) := by
  apply aj_RBL_append _ _ _ h1
  intro j hj i hi
  simp only [List.length_singleton] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  have := h2 i (by simpa using hi)
  omega

-- the state of the reverse pass: accumulator wire per wire, and the appended gates
def aj_Good (B : ℕ) (st : (ℕ → ℕ) × List Gate) : Prop :=
  (∀ w, st.1 w < B + st.2.length) ∧
  (∀ g ∈ st.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  aj_RBL B st.2

def aj_link (B : ℕ) (st : (ℕ → ℕ) × List Gate) (a src : ℕ) : (ℕ → ℕ) × List Gate :=
  (Function.update st.1 a (B + st.2.length), st.2 ++ [Gate.mk GateOp.or [st.1 a, src]])

def aj_andl (B : ℕ) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ) : (ℕ → ℕ) × List Gate :=
  aj_link B (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) tgt (B + st.2.length)

def aj_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def aj_proc (B : ℕ) (deg : List ℕ) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) : (ℕ → ℕ) × List Gate :=
  if 0 < deg.getD W 0 then
    if aj_isAnd op = true ∧ l.length = 2 then
      if 0 < deg.getD (l.getD 0 0) 0 then aj_andl B st W (l.getD 0 0) (l.getD 1 0)
      else aj_andl B st W (l.getD 1 0) (l.getD 0 0)
    else l.foldl (fun s a => aj_link B s a (st.1 W)) st
  else st

def aj_aval (base : List Bool) (st : (ℕ → ℕ) × List Gate) (w : ℕ) : Bool :=
  (aj_run aj_evf st.2 base).getD (st.1 w) false

theorem aj_link_spec (B : ℕ) (base : List Bool) (st : (ℕ → ℕ) × List Gate) (a src : ℕ)
    (hB : base.length = B) (hg : aj_Good B st) (hs : src < B + st.2.length) :
    aj_Good B (aj_link B st a src) ∧ (aj_link B st a src).2.length = st.2.length + 1 ∧
    (∀ i < B + st.2.length,
      (aj_run aj_evf (aj_link B st a src).2 base).getD i false = (aj_run aj_evf st.2 base).getD i false) ∧
    ∀ w, aj_aval base (aj_link B st a src) w =
      (aj_aval base st w || (decide (w = a) && (aj_run aj_evf st.2 base).getD src false)) := by
  obtain ⟨g1, g2, g3⟩ := hg
  have hlen : (aj_run aj_evf st.2 base).length = B + st.2.length := by rw [aj_run_length, hB]
  have hrun : aj_run aj_evf (aj_link B st a src).2 base = aj_run aj_evf st.2 base ++
      [((aj_run aj_evf st.2 base).getD (st.1 a) false || (aj_run aj_evf st.2 base).getD src false)] := by
    simp [aj_link, aj_run_snoc, aj_evf, GateOp.eval]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w
    simp only [aj_link, List.length_append, List.length_singleton, Function.update_apply]
    split_ifs
    · omega
    · have := g1 w
      omega
  · intro g hg
    simp only [aj_link, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact g2 g hg
    · exact ⟨Or.inr rfl, by simp⟩
  · apply aj_RBL_snoc _ _ _ g3
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact g1 a
    · exact hs
  · simp [aj_link]
  · intro i hi
    rw [hrun]
    exact aj_getD_app_lt _ _ _ _ (by omega)
  · intro w
    unfold aj_aval
    rw [hrun]
    by_cases hw : w = a
    · subst hw
      have e : (aj_link B st w src).1 w = (aj_run aj_evf st.2 base).length := by simp [aj_link, hlen]
      rw [e, aj_getD_app_len]
      simp
    · have e : (aj_link B st a src).1 w = st.1 w := by simp [aj_link, hw]
      rw [e, aj_getD_app_lt _ _ _ _ (by have := g1 w; omega)]
      simp [hw]

theorem aj_ite_p {α : Type} (c : Prop) [Decidable c] (a b : α) (h : c) : (if c then a else b) = a := by
  simp [h]

theorem aj_ite_n {α : Type} (c : Prop) [Decidable c] (a b : α) (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem aj_bool_aux (p q r s : Bool) : ((p || (q && s)) || (r && s)) = (p || ((q || r) && s)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem aj_fold_spec (B : ℕ) (base : List Bool) (src : ℕ) (hB : base.length = B) (l : List ℕ) :
    ∀ (st : (ℕ → ℕ) × List Gate), aj_Good B st → src < B + st.2.length →
    aj_Good B (l.foldl (fun s a => aj_link B s a src) st) ∧
    (l.foldl (fun s a => aj_link B s a src) st).2.length = st.2.length + l.length ∧
    (∀ i < B + st.2.length,
      (aj_run aj_evf (l.foldl (fun s a => aj_link B s a src) st).2 base).getD i false =
        (aj_run aj_evf st.2 base).getD i false) ∧
    ∀ w, aj_aval base (l.foldl (fun s a => aj_link B s a src) st) w =
      (aj_aval base st w || (decide (w ∈ l) && (aj_run aj_evf st.2 base).getD src false)) := by
  induction l with
  | nil =>
    intro st hg _
    simp [hg]
  | cons a l ih =>
    intro st hg hs
    obtain ⟨k1, k2, k3, k4⟩ := aj_link_spec B base st a src hB hg hs
    obtain ⟨j1, j2, j3, j4⟩ := ih (aj_link B st a src) k1 (by omega)
    rw [List.foldl_cons]
    refine ⟨j1, ?_, ?_, ?_⟩
    · rw [j2, k2, List.length_cons]
      omega
    · intro i hi
      rw [j3 i (by omega), k3 i hi]
    · intro w
      rw [j4 w, k4 w, k3 src hs, aj_bool_aux]
      congr 2
      simp [Bool.decide_or]

theorem aj_andl_spec (B : ℕ) (base : List Bool) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ)
    (hB : base.length = B) (hg : aj_Good B st) (hs : side < B) :
    aj_Good B (aj_andl B st W tgt side) ∧ (aj_andl B st W tgt side).2.length = st.2.length + 2 ∧
    ∀ w, aj_aval base (aj_andl B st W tgt side) w =
      (aj_aval base st w || (decide (w = tgt) && (aj_aval base st W && base.getD side false))) := by
  have hg' := hg
  obtain ⟨g1, g2, g3⟩ := hg
  have hlen : (aj_run aj_evf st.2 base).length = B + st.2.length := by rw [aj_run_length, hB]
  have hrun : aj_run aj_evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base = aj_run aj_evf st.2 base ++
      [((aj_run aj_evf st.2 base).getD (st.1 W) false && (aj_run aj_evf st.2 base).getD side false)] := by
    simp [aj_run_snoc, aj_evf, GateOp.eval]
  have hg1 : aj_Good B (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) := by
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
    · apply aj_RBL_snoc _ _ _ g3
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h
      · rw [h]; exact g1 W
      · rw [h]; omega
  obtain ⟨k1, k2, _, k4⟩ := aj_link_spec B base (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]])
    tgt (B + st.2.length) hB hg1 (by simp)
  refine ⟨k1, ?_, ?_⟩
  · unfold aj_andl
    rw [k2]
    simp
  · intro w
    unfold aj_andl
    rw [k4 w]
    have e1 : aj_aval base (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) w = aj_aval base st w := by
      unfold aj_aval
      show (aj_run aj_evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base).getD (st.1 w) false = _
      rw [hrun]
      exact aj_getD_app_lt _ _ _ _ (by have := g1 w; omega)
    have e2 : (aj_run aj_evf (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]).2 base).getD
        (B + st.2.length) false = (aj_aval base st W && base.getD side false) := by
      show (aj_run aj_evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base).getD _ _ = _
      rw [hrun, ← hlen, aj_getD_app_len]
      unfold aj_aval
      rw [aj_run_lt aj_evf st.2 base false side (by omega)]
    rw [e1, e2]

-- the logical invariant of the reverse pass
def aj_Tinv (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (bound : ℕ) (A : ℕ → Bool) : Prop :=
  (∀ w < bound, Dp w → A w = true → u w = true → uo = true) ∧
  (∀ w < bound, Dp w → A w = true → v w = true → vo = true) ∧
  (uo = true → vo = true ∨ ∃ w < bound, Dp w ∧ A w = true ∧ u w = true)

theorem aj_tinv_skip (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W : ℕ) (A : ℕ → Bool)
    (hD : ¬ Dp W) (hI : aj_Tinv Dp u v uo vo (W + 1) A) : aj_Tinv Dp u v uo vo W A := by
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

theorem aj_tinv_or (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W : ℕ) (l : List ℕ)
    (A A' : ℕ → Bool) (hr : ∀ i ∈ l, i < W) (hD : Dp W)
    (hA : ∀ w, A' w = (A w || (decide (w ∈ l) && A W)))
    (hx : ∀ w, ¬ Dp w → u w = v w)
    (p1u : ∀ i ∈ l, u i = true → u W = true) (p1v : ∀ i ∈ l, v i = true → v W = true)
    (p2 : u W = true → v W = true ∨ ∃ i ∈ l, u i = true)
    (hI : aj_Tinv Dp u v uo vo (W + 1) A) : aj_Tinv Dp u v uo vo W A' := by
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

theorem aj_tinv_and (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W tgt side : ℕ)
    (A A' : ℕ → Bool) (ht : tgt < W) (hD : Dp W) (hs : ¬ Dp side)
    (hA : ∀ w, A' w = (A w || (decide (w = tgt) && (A W && v side))))
    (hx : ∀ w, ¬ Dp w → u w = v w)
    (hu : u W = (u tgt && u side)) (hv : v W = (v tgt && v side))
    (hI : aj_Tinv Dp u v uo vo (W + 1) A) : aj_Tinv Dp u v uo vo W A' := by
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

theorem aj_fold_case (B : ℕ) (deg : List ℕ) (base : List Bool) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hB : base.length = B) (hl : l.length ≤ 2)
    (hr : ∀ i ∈ l, i < W) (hg : aj_Good B st) (hD : 0 < deg.getD W 0) :
    aj_Good B (l.foldl (fun s a => aj_link B s a (st.1 W)) st) ∧
    (l.foldl (fun s a => aj_link B s a (st.1 W)) st).2.length ≤ st.2.length + 2 ∧
    ∀ (u v : ℕ → Bool) (uo vo : Bool), (∀ w, ¬ 0 < deg.getD w 0 → u w = v w) →
      (∀ i ∈ l, u i = true → u W = true) → (∀ i ∈ l, v i = true → v W = true) →
      (u W = true → v W = true ∨ ∃ i ∈ l, u i = true) →
      aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo (W + 1) (aj_aval base st) →
      aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo W
        (aj_aval base (l.foldl (fun s a => aj_link B s a (st.1 W)) st)) := by
  obtain ⟨j1, j2, _, j4⟩ := aj_fold_spec B base (st.1 W) hB l st hg (hg.1 W)
  refine ⟨j1, by omega, ?_⟩
  intro u v uo vo hx p1u p1v p2 hI
  exact aj_tinv_or _ u v uo vo W l _ _ hr hD j4 hx p1u p1v p2 hI

theorem aj_proc_spec (B : ℕ) (deg : List ℕ) (base : List Bool) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hB : base.length = B) (hW : W < B)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2) (hr : ∀ i ∈ l, i < W)
    (hc : op = GateOp.and → l.length = 2 → ∃ i ∈ l, deg.getD i 0 = 0)
    (hg : aj_Good B st) :
    aj_Good B (aj_proc B deg op l W st) ∧
    (aj_proc B deg op l W st).2.length ≤ st.2.length + (if 0 < deg.getD W 0 then 2 else 0) ∧
    ∀ (u v : ℕ → Bool) (uo vo : Bool),
      (∀ i < W, ¬ 0 < deg.getD i 0 → base.getD i false = v i) →
      u W = op.eval (l.map u) → v W = op.eval (l.map v) →
      (∀ w, ¬ 0 < deg.getD w 0 → u w = v w) →
      aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo (W + 1) (aj_aval base st) →
      aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo W (aj_aval base (aj_proc B deg op l W st)) := by
  by_cases hD : 0 < deg.getD W 0
  · rcases hop with rfl | rfl
    · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · have e : aj_proc B deg GateOp.and [] W st
            = ([] : List ℕ).foldl (fun s a => aj_link B s a (st.1 W)) st := by
          unfold aj_proc
          rw [aj_ite_p _ _ _ hD, aj_ite_n _ _ _ (by simp)]
        rw [e]
        obtain ⟨f1, f2, f3⟩ := aj_fold_case B deg base [] W st hB hl hr hg hD
        refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
        intro u v uo vo _ hu hv hx hI
        refine f3 u v uo vo hx (by simp) (by simp) ?_ hI
        intro _
        left
        simpa [GateOp.eval] using hv
      · have e : aj_proc B deg GateOp.and [a] W st
            = [a].foldl (fun s a => aj_link B s a (st.1 W)) st := by
          unfold aj_proc
          rw [aj_ite_p _ _ _ hD, aj_ite_n _ _ _ (by simp)]
        rw [e]
        obtain ⟨f1, f2, f3⟩ := aj_fold_case B deg base [a] W st hB hl hr hg hD
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
      · have e : aj_proc B deg GateOp.and [a, b] W st
            = if 0 < deg.getD a 0 then aj_andl B st W a b else aj_andl B st W b a := by
          unfold aj_proc
          rw [aj_ite_p _ _ _ hD, aj_ite_p _ _ _ (by simp [aj_isAnd])]
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
          obtain ⟨k1, k2, k3⟩ := aj_andl_spec B base st W a b hB hg (by omega)
          refine ⟨k1, by simp only [hD, ↓reduceIte]; omega, ?_⟩
          intro u v uo vo hbv hu hv hx hI
          have hu' : u W = (u a && u b) := by simpa [GateOp.eval] using hu
          have hv' : v W = (v a && v b) := by simpa [GateOp.eval] using hv
          refine aj_tinv_and _ u v uo vo W a b _ _ ha hD hdb ?_ hx hu' hv' hI
          intro w
          rw [k3 w, hbv b hb hdb]
        · simp only [hda, ↓reduceIte]
          obtain ⟨k1, k2, k3⟩ := aj_andl_spec B base st W b a hB hg (by omega)
          refine ⟨k1, by simp only [hD, ↓reduceIte]; omega, ?_⟩
          intro u v uo vo hbv hu hv hx hI
          have hu' : u W = (u b && u a) := by
            rw [Bool.and_comm]; simpa [GateOp.eval] using hu
          have hv' : v W = (v b && v a) := by
            rw [Bool.and_comm]; simpa [GateOp.eval] using hv
          refine aj_tinv_and _ u v uo vo W b a _ _ hb hD hda ?_ hx hu' hv' hI
          intro w
          rw [k3 w, hbv a ha hda]
      · simp at hl
    · have e : aj_proc B deg GateOp.or l W st
          = l.foldl (fun s a => aj_link B s a (st.1 W)) st := by
        unfold aj_proc
        rw [aj_ite_p _ _ _ hD, aj_ite_n _ _ _ (by simp [aj_isAnd])]
      rw [e]
      obtain ⟨f1, f2, f3⟩ := aj_fold_case B deg base l W st hB hl hr hg hD
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
  · have e : aj_proc B deg op l W st = st := by
      unfold aj_proc
      rw [aj_ite_n _ _ _ hD]
    rw [e]
    refine ⟨hg, by simp, ?_⟩
    intro u v uo vo _ _ _ _ hI
    exact aj_tinv_skip _ u v uo vo W _ hD hI

-- the reverse pass over the gate list, last gate first
def aj_stAt (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate) :
    ℕ → (ℕ → ℕ) × List Gate
  | 0 => st0
  | d + 1 => aj_proc B deg (gs.getD (gs.length - 1 - d) aj_dflt).op
      (gs.getD (gs.length - 1 - d) aj_dflt).inputs (N + (gs.length - 1 - d)) (aj_stAt B N deg gs st0 d)

def aj_cnt (N : ℕ) (deg : List ℕ) (b : ℕ) : ℕ :=
  ((Finset.range b).filter (fun k => 0 < deg.getD (N + k) 0)).card

theorem aj_cnt_succ (N : ℕ) (deg : List ℕ) (b : ℕ) :
    aj_cnt N deg (b + 1) = aj_cnt N deg b + (if 0 < deg.getD (N + b) 0 then 1 else 0) := by
  unfold aj_cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

def aj_GateHyp (N : ℕ) (deg : List ℕ) (gs : List Gate) : Prop :=
  ∀ k < gs.length, ((gs.getD k aj_dflt).op = GateOp.and ∨ (gs.getD k aj_dflt).op = GateOp.or) ∧
    (gs.getD k aj_dflt).inputs.length ≤ 2 ∧ (∀ i ∈ (gs.getD k aj_dflt).inputs, i < N + k) ∧
    ((gs.getD k aj_dflt).op = GateOp.and → (gs.getD k aj_dflt).inputs.length = 2 →
      ∃ i ∈ (gs.getD k aj_dflt).inputs, deg.getD i 0 = 0)

theorem aj_iter_good (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (hNB : N + gs.length ≤ B) (hgs : aj_GateHyp N deg gs) (hg0 : aj_Good B st0) :
    ∀ d ≤ gs.length, aj_Good B (aj_stAt B N deg gs st0 d) ∧
      (aj_stAt B N deg gs st0 d).2.length + 2 * aj_cnt N deg (gs.length - d)
        ≤ st0.2.length + 2 * aj_cnt N deg gs.length := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨hg0, by simp [aj_stAt]⟩
  | succ d ih =>
    intro hd
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, k = gs.length - 1 - d := ⟨_, rfl⟩
    have hks : k < gs.length := by omega
    obtain ⟨a1, a2, a3, a4⟩ := hgs k hks
    have e : aj_stAt B N deg gs st0 (d + 1) = aj_proc B deg (gs.getD k aj_dflt).op
        (gs.getD k aj_dflt).inputs (N + k) (aj_stAt B N deg gs st0 d) := by
      rw [hk]; rfl
    obtain ⟨p1, p2, _⟩ := aj_proc_spec B deg (List.replicate B false) (gs.getD k aj_dflt).op
      (gs.getD k aj_dflt).inputs (N + k) (aj_stAt B N deg gs st0 d) List.length_replicate
      (by omega) a1 a2 a3 a4 i1
    rw [e]
    refine ⟨p1, ?_⟩
    have e1 : gs.length - d = k + 1 := by omega
    have e2 : gs.length - (d + 1) = k := by omega
    rw [e1, aj_cnt_succ] at i2
    rw [e2]
    split_ifs at p2 i2 <;> omega

theorem aj_iter_inv (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (base : List Bool) (u v : ℕ → Bool) (uo vo : Bool)
    (hB : base.length = B) (hNB : N + gs.length ≤ B) (hgs : aj_GateHyp N deg gs) (hg0 : aj_Good B st0)
    (hv : ∀ i < N + gs.length, ¬ 0 < deg.getD i 0 → base.getD i false = v i)
    (hu : ∀ k < gs.length, u (N + k) = (gs.getD k aj_dflt).op.eval ((gs.getD k aj_dflt).inputs.map u))
    (hvv : ∀ k < gs.length, v (N + k) = (gs.getD k aj_dflt).op.eval ((gs.getD k aj_dflt).inputs.map v))
    (hx : ∀ w, ¬ 0 < deg.getD w 0 → u w = v w)
    (hI : aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo (N + gs.length) (aj_aval base st0)) :
    ∀ d ≤ gs.length, aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo (N + (gs.length - d))
      (aj_aval base (aj_stAt B N deg gs st0 d)) := by
  intro d
  induction d with
  | zero =>
    intro _
    simpa [aj_stAt] using hI
  | succ d ih =>
    intro hd
    have i1 := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, k = gs.length - 1 - d := ⟨_, rfl⟩
    have hks : k < gs.length := by omega
    obtain ⟨a1, a2, a3, a4⟩ := hgs k hks
    have e : aj_stAt B N deg gs st0 (d + 1) = aj_proc B deg (gs.getD k aj_dflt).op
        (gs.getD k aj_dflt).inputs (N + k) (aj_stAt B N deg gs st0 d) := by
      rw [hk]; rfl
    obtain ⟨_, _, p3⟩ := aj_proc_spec B deg base (gs.getD k aj_dflt).op
      (gs.getD k aj_dflt).inputs (N + k) (aj_stAt B N deg gs st0 d) hB
      (by omega) a1 a2 a3 a4 (aj_iter_good B N deg gs st0 hNB hgs hg0 d (by omega)).1
    have e1 : gs.length - d = k + 1 := by omega
    have e2 : gs.length - (d + 1) = k := by omega
    rw [e1] at i1
    rw [e, e2]
    exact p3 u v uo vo (fun i hi => hv i (by omega)) (hu k hks) (hvv k hks) hx i1

-- wire values and degrees of the given circuit
def aj_wv (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD w false

theorem aj_wires_run (C : Circuit) (inp : List Bool) : C.wires inp = aj_run aj_evf C.gates inp := rfl

theorem aj_wv_input (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : w < N) :
    aj_wv C N z w = z ⟨w, h⟩ := by
  unfold aj_wv
  rw [aj_wires_run, aj_run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem aj_wv_ge (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : N + C.gates.length ≤ w) :
    aj_wv C N z w = false := by
  unfold aj_wv
  rw [aj_wires_run]
  exact aj_getD_ge _ _ _ (by rw [aj_run_length]; simpa using h)

theorem aj_wv_gate (C : Circuit) (N : ℕ) (z : Fin N → Bool) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    aj_wv C N z (N + k) = (C.gates.getD k aj_dflt).op.eval ((C.gates.getD k aj_dflt).inputs.map (aj_wv C N z)) := by
  unfold aj_wv
  rw [aj_wires_run]
  exact aj_run_gate aj_evf false aj_evf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem aj_deg_run (C : Circuit) (N : ℕ) (M : Finset ℕ) : C.lineDegrees N M =
    aj_run aj_ldf C.gates ((List.range N).map fun i => if i ∈ M then 1 else 0) := rfl

theorem aj_deg_input (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : w < N) :
    (C.lineDegrees N M).getD w 0 = if w ∈ M then 1 else 0 := by
  rw [aj_deg_run, aj_run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem aj_deg_ge (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : N + C.gates.length ≤ w) :
    (C.lineDegrees N M).getD w 0 = 0 := by
  rw [aj_deg_run]
  exact aj_getD_ge _ _ _ (by rw [aj_run_length]; simpa using h)

theorem aj_deg_gate (C : Circuit) (N : ℕ) (M : Finset ℕ) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.lineDegrees N M).getD (N + k) 0 = (C.gates.getD k aj_dflt).lineDegree (C.lineDegrees N M) := by
  rw [aj_deg_run]
  exact aj_run_gate aj_ldf 0 aj_ldf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem aj_app_lt {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : w < n) : Fin.append x y ⟨w, h⟩ = x ⟨w, hw⟩ :=
  Fin.append_left x y ⟨w, hw⟩

theorem aj_app_ge {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : n ≤ w) : Fin.append x y ⟨w, h⟩ = y ⟨w - n, by omega⟩ := by
  have e : (⟨w, h⟩ : Fin (n + m)) = Fin.natAdd n ⟨w - n, by omega⟩ := by
    ext
    simp only [Fin.natAdd_mk]
    omega
  rw [e, Fin.append_right]

theorem aj_gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : C.gates.getD k aj_dflt ∈ C.gates := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem aj_gate_ops (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((C.gates.getD k aj_dflt).op = GateOp.and ∨ (C.gates.getD k aj_dflt).op = GateOp.or) ∧
    (C.gates.getD k aj_dflt).inputs.length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hM _ (aj_gate_mem C k hk)
  refine ⟨?_, h2⟩
  simpa using h1

-- forward pass: wires of degree zero ignore the line inputs, and all wires are monotone in them
theorem aj_fwd (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) :
    ((C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 = 0 →
      aj_wv C (n + m) (Fin.append x y) w = aj_wv C (n + m) (Fin.append x (fun _ => false)) w) ∧
    (aj_wv C (n + m) (Fin.append x (fun _ => false)) w = true →
      aj_wv C (n + m) (Fin.append x y) w = true) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w (n + m) with h | h
    · rw [aj_wv_input _ _ _ _ h, aj_wv_input _ _ _ _ h, aj_deg_input _ _ _ _ h]
      rcases Nat.lt_or_ge w n with hw | hw
      · rw [aj_app_lt _ _ _ _ hw, aj_app_lt _ _ _ _ hw]
        exact ⟨fun _ => rfl, fun h => h⟩
      · rw [aj_app_ge _ (fun _ => false) _ _ hw]
        have : w ∈ Finset.Ico n (n + m) := by simp; omega
        simp [this]
    · rcases Nat.lt_or_ge (w - (n + m)) C.gates.length with hk | hk
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + m + k := ⟨w - (n + m), by omega⟩
        have hk' : k < C.gates.length := by omega
        have hu := aj_wv_gate C (n + m) (Fin.append x y) hR k hk'
        have hv := aj_wv_gate C (n + m) (Fin.append x (fun _ => false)) hR k hk'
        have hd := aj_deg_gate C (n + m) (Finset.Ico n (n + m)) hR k hk'
        have hr : ∀ i ∈ (C.gates.getD k aj_dflt).inputs, i < n + m + k := hR k hk'
        obtain ⟨hop, hl⟩ := aj_gate_ops C hM k hk'
        generalize C.gates.getD k aj_dflt = g at hu hv hd hr hop hl
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
      · rw [aj_wv_ge _ _ _ _ (by omega), aj_wv_ge _ _ _ _ (by omega)]
        exact ⟨fun _ => rfl, fun h => h⟩

theorem aj_run_false (m : ℕ) (w : List Bool) :
    aj_run aj_evf (List.replicate m (Gate.mk GateOp.or [])) w = w ++ List.replicate m false := by
  induction m with
  | zero => simp [aj_run]
  | succ m ih =>
    rw [List.replicate_succ', aj_run_snoc, ih, List.replicate_succ', ← List.append_assoc]
    simp [aj_evf, GateOp.eval]

theorem aj_ofFn_app {n m : ℕ} (x : Fin n → Bool) :
    List.ofFn (Fin.append x (fun _ : Fin m => false)) = List.ofFn x ++ List.replicate m false := by
  rw [List.ofFn_fin_append, List.ofFn_const]

theorem aj_ncard_cnt (N s : ℕ) (deg : List ℕ) :
    Set.ncard {j : ℕ | j < s ∧ 0 < deg.getD (N + j) 0} = aj_cnt N deg s := by
  unfold aj_cnt
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp

theorem aj_gate_hyp (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (hX : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → (gateAt C j).inputs.length = 2 →
      ∃ i ∈ (gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) :
    aj_GateHyp (n + m) (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates := by
  intro k hk
  obtain ⟨h1, h2⟩ := aj_gate_ops C hM k hk
  exact ⟨h1, h2, hR k hk, hX k hk⟩

theorem aj_tinv_init (Dp : ℕ → Prop) (u v : ℕ → Bool) (r bound : ℕ) (A : ℕ → Bool)
    (hA : ∀ w, A w = decide (w = r)) (hx : ∀ w, ¬ Dp w → u w = v w)
    (hb : u r = true → r < bound) :
    aj_Tinv Dp u v (u r) (v r) bound A := by
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

theorem aj_ld_zero (g : Gate) (d : List ℕ) (h : ∀ i ∈ g.inputs, d.getD i 0 = 0) : aj_ldf d g = 0 := by
  have key : ∀ l : List ℕ, (∀ i ∈ l, d.getD i 0 = 0) →
      (l.map fun i => d.getD i 0).sum = 0 ∧ (l.map fun i => d.getD i 0).foldr max 0 = 0 := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro hl
      obtain ⟨i1, i2⟩ := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      have ha := hl a (by simp)
      simp only [List.map_cons, List.sum_cons, List.foldr_cons]
      rw [i1, i2, ha]
      simp
  unfold aj_ldf Gate.lineDegree
  split_ifs
  · exact (key _ h).1
  · exact (key _ h).2

theorem aj_deg_zero (K : ℕ) (gs : List Gate) (w0 : List ℕ) (hK : w0.length = K)
    (h : ∀ g ∈ gs, ∀ i ∈ g.inputs, K ≤ i ∨ w0.getD i 0 = 0) :
    ∀ i, K ≤ i → (aj_run aj_ldf gs w0).getD i 0 = 0 := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    show w0.getD i 0 = 0
    exact aj_getD_ge _ _ _ (by omega)
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => h g' (List.mem_append_left _ hg'))
    intro i hi
    rw [aj_run_snoc]
    have hlen := aj_run_length aj_ldf gs w0
    rcases Nat.lt_trichotomy i (aj_run aj_ldf gs w0).length with hlt | heq | hgt
    · rw [aj_getD_app_lt _ _ _ _ hlt]
      exact ih' i hi
    · rw [heq, aj_getD_app_len]
      apply aj_ld_zero
      intro j hj
      rcases Nat.lt_or_ge j K with hjK | hjK
      · rw [aj_run_lt _ _ _ _ _ (by omega)]
        rcases h g (by simp) j hj with h1 | h1
        · omega
        · exact h1
      · exact ih' j hjK
    · exact aj_getD_ge _ _ _ (by simp only [List.length_append, List.length_singleton]; omega)

def aj_Syn (K : ℕ) (deg : List ℕ) (st : (ℕ → ℕ) × List Gate) : Prop :=
  (∀ w, K ≤ st.1 w) ∧ ∀ g ∈ st.2, ∀ i ∈ g.inputs, K ≤ i ∨ deg.getD i 0 = 0

theorem aj_link_syn (K B : ℕ) (deg : List ℕ) (st : (ℕ → ℕ) × List Gate) (a src : ℕ) (hKB : K ≤ B)
    (h : aj_Syn K deg st) (hs : K ≤ src) : aj_Syn K deg (aj_link B st a src) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro w
    simp only [aj_link, Function.update_apply]
    split_ifs
    · omega
    · exact h1 w
  · intro g hg i hi
    simp only [aj_link, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact h2 g hg i hi
    · rw [hg] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with e | e
      · left; rw [e]; exact h1 a
      · left; rw [e]; exact hs

theorem aj_fold_syn (K B : ℕ) (deg : List ℕ) (src : ℕ) (hKB : K ≤ B) (hs : K ≤ src) (l : List ℕ) :
    ∀ st : (ℕ → ℕ) × List Gate, aj_Syn K deg st →
      aj_Syn K deg (l.foldl (fun s a => aj_link B s a src) st) := by
  induction l with
  | nil => intro st h; exact h
  | cons a l ih =>
    intro st h
    rw [List.foldl_cons]
    exact ih _ (aj_link_syn K B deg st a src hKB h hs)

theorem aj_andl_syn (K B : ℕ) (deg : List ℕ) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ)
    (hKB : K ≤ B) (h : aj_Syn K deg st) (hd : deg.getD side 0 = 0) :
    aj_Syn K deg (aj_andl B st W tgt side) := by
  unfold aj_andl
  obtain ⟨h1, h2⟩ := h
  apply aj_link_syn K B deg _ _ _ hKB _ (by omega)
  refine ⟨h1, ?_⟩
  intro g hg i hi
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | hg
  · exact h2 g hg i hi
  · rw [hg] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with e | e
    · left; rw [e]; exact h1 W
    · right; rw [e]; exact hd

theorem aj_proc_syn (K B : ℕ) (deg : List ℕ) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hKB : K ≤ B)
    (hc : op = GateOp.and → l.length = 2 → ∃ i ∈ l, deg.getD i 0 = 0)
    (h : aj_Syn K deg st) : aj_Syn K deg (aj_proc B deg op l W st) := by
  unfold aj_proc
  by_cases hD : 0 < deg.getD W 0
  · rw [aj_ite_p _ _ _ hD]
    by_cases hA : aj_isAnd op = true ∧ l.length = 2
    · rw [aj_ite_p _ _ _ hA]
      have hop : op = GateOp.and := by
        obtain ⟨hA1, _⟩ := hA
        cases op <;> first | rfl | (simp [aj_isAnd] at hA1)
      obtain ⟨i, hi, hi0⟩ := hc hop hA.2
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hA.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      by_cases hda : 0 < deg.getD a 0
      · have e : (if 0 < deg.getD ([a, b].getD 0 0) 0
            then aj_andl B st W ([a, b].getD 0 0) ([a, b].getD 1 0)
            else aj_andl B st W ([a, b].getD 1 0) ([a, b].getD 0 0)) = aj_andl B st W a b :=
          aj_ite_p _ _ _ hda
        rw [e]
        apply aj_andl_syn K B deg st W a b hKB h
        rcases hi with e | e
        · rw [e] at hi0; omega
        · rw [e] at hi0; exact hi0
      · have e : (if 0 < deg.getD ([a, b].getD 0 0) 0
            then aj_andl B st W ([a, b].getD 0 0) ([a, b].getD 1 0)
            else aj_andl B st W ([a, b].getD 1 0) ([a, b].getD 0 0)) = aj_andl B st W b a :=
          aj_ite_n _ _ _ hda
        rw [e]
        apply aj_andl_syn K B deg st W b a hKB h
        omega
    · rw [aj_ite_n _ _ _ hA]
      exact aj_fold_syn K B deg (st.1 W) hKB (h.1 W) l st h
  · rw [aj_ite_n _ _ _ hD]
    exact h

theorem aj_iter_syn (K B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (hKB : K ≤ B) (hgs : aj_GateHyp N deg gs) (h0 : aj_Syn K deg st0) :
    ∀ d ≤ gs.length, aj_Syn K deg (aj_stAt B N deg gs st0 d) := by
  intro d
  induction d with
  | zero => intro _; exact h0
  | succ d ih =>
    intro hd
    show aj_Syn K deg (aj_proc B deg _ _ _ (aj_stAt B N deg gs st0 d))
    exact aj_proc_syn K B deg _ _ _ _ hKB (hgs _ (by omega)).2.2.2 (ih (by omega))

theorem aj_deg_app (n m : ℕ) (G A : List Gate)
    (hA : ∀ g ∈ A, ∀ i ∈ g.inputs, n + m + G.length ≤ i ∨
      ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) :
    ∀ i, n + m + G.length ≤ i →
      ((Circuit.mk (G ++ A) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0 := by
  intro i hi
  rw [aj_deg_run]
  show (aj_run aj_ldf (G ++ A) _).getD i 0 = 0
  rw [aj_run_append]
  exact aj_deg_zero _ A _ (by show (aj_run aj_ldf G _).length = _; rw [aj_run_length]; simp) hA i hi

theorem aj_snoc_val (w : List Bool) (K : ℕ) (hK : w.length = K) (b : Bool) :
    (w ++ [b]).getD K false = b := by
  subst hK
  exact aj_getD_app_len _ _ _

theorem aj_single (n m : ℕ) (G : List Gate) (g : Gate) (hg : g.inputs = [])
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (∀ g' ∈ [g], g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
    (∀ k < [g].length, ∀ i ∈ ([g].getD k (Gate.mk GateOp.or [])).inputs, i < n + m + G.length + k) ∧
    (∀ k < [g].length,
      ((Circuit.mk (G ++ [g]) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD
        (n + m + G.length + k) 0 = 0) ∧
    (n + m + G.length < n + m + G.length + [g].length ∧
      ((Circuit.mk (G ++ [g]) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD
        (n + m + G.length) 0 = 0) ∧
    ∀ (z : Fin (n + m) → Bool), ((Circuit.mk (G ++ [g]) 0).wires (List.ofFn z)).getD
      (n + m + G.length) false = g.op.eval [] := by
  have hd := aj_deg_app n m G [g] (by
    intro g' hg' i hi
    simp only [List.mem_singleton] at hg'
    rw [hg', hg] at hi
    simp at hi)
  refine ⟨?_, ?_, ?_, ⟨by simp, hd _ (le_refl _)⟩, ?_⟩
  · intro g' hg'
    simp only [List.mem_singleton] at hg'
    rw [hg', hg]
    refine ⟨?_, by simp⟩
    rcases hop with h | h <;> simp [h]
  · exact aj_RBL_empty _ _ (by
      intro g' hg'
      simp only [List.mem_singleton] at hg'
      rw [hg', hg])
  · intro k _
    exact hd _ (by omega)
  · intro z
    rw [aj_wires_run]
    show (aj_run aj_evf (G ++ [g]) _).getD _ _ = _
    rw [aj_run_snoc]
    have e : aj_evf (aj_run aj_evf G (List.ofFn z)) g = g.op.eval [] := by
      unfold aj_evf
      rw [hg]
      rfl
    rw [e]
    exact aj_snoc_val _ _ (by rw [aj_run_length]; simp) _

def AdjointSpec (n m : ℕ) (G : List Gate) (r : ℕ) : Prop :=
  Monotone2 (Circuit.mk G 0) →
  ReadsBack (n + m) (Circuit.mk G 0) →
  (∀ j < G.length, (gateAt (Circuit.mk G 0) j).op = GateOp.and →
    (gateAt (Circuit.mk G 0) j).inputs.length = 2 →
    ∃ i ∈ (gateAt (Circuit.mk G 0) j).inputs,
      ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) →
  r < n + m + G.length →
  ∃ (A : List Gate) (o : Fin m → ℕ),
    (∀ g ∈ A, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
    (∀ k < A.length, ∀ i ∈ (A.getD k (Gate.mk GateOp.or [])).inputs, i < n + m + G.length + k) ∧
    A.length ≤ 3 * Set.ncard {j : ℕ | j < G.length ∧
      0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧
    (∀ k < A.length,
      ((Circuit.mk (G ++ A) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD
        (n + m + G.length + k) 0 = 0) ∧
    (∀ j : Fin m, o j < n + m + G.length + A.length ∧
      ((Circuit.mk (G ++ A) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD (o j) 0 = 0) ∧
    ∀ (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m),
      ((Circuit.mk G 0).wires (List.ofFn (Fin.append x (fun l => decide (l = j))))).getD r false =
        (((Circuit.mk G 0).wires (List.ofFn (Fin.append x (fun _ : Fin m => false)))).getD r false ||
         ((Circuit.mk (G ++ A) 0).wires (List.ofFn (Fin.append x y))).getD (o j) false)

theorem aj_adjoint (n m : ℕ) (G : List Gate) (r : ℕ) : AdjointSpec n m G r := by
  intro hM hR hX hr
  have hF := fun (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) =>
    aj_fwd n m (Circuit.mk G 0) hM hR x y w
  rw [aj_ncard_cnt]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨[], fun j => j.elim0, by simp, by simp, by simp, by simp, fun j => j.elim0,
      fun x y j => j.elim0⟩
  by_cases hout : 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD r 0
  · by_cases hbig : 2 ≤ aj_cnt (n + m) ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m)))
        G.length + m
    · -- the reverse pass, after a true and a false constant
      have hgs : aj_GateHyp (n + m) ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G :=
        aj_gate_hyp n m (Circuit.mk G 0) hM hR hX
      have hg0 : aj_Good (n + m + G.length + 2)
          ((fun w => if w = r then n + m + G.length else n + m + G.length + 1),
            ([] : List Gate)) := by
        refine ⟨?_, ?_, ?_⟩
        · intro w
          simp only [List.length_nil]
          split_ifs <;> omega
        · intro g hg
          simp at hg
        · intro j hj
          simp at hj
      have hs0 : aj_Syn (n + m + G.length)
          ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m)))
          ((fun w => if w = r then n + m + G.length else n + m + G.length + 1),
            ([] : List Gate)) := by
        refine ⟨?_, ?_⟩
        · intro w
          show n + m + G.length ≤ (if w = r then n + m + G.length else n + m + G.length + 1)
          split_ifs <;> omega
        · intro g hg
          simp at hg
      obtain ⟨q1, q2⟩ := aj_iter_good (n + m + G.length + 2) (n + m)
        ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G _ (by omega) hgs hg0
        G.length (le_refl _)
      have q3 := aj_iter_syn (n + m + G.length) (n + m + G.length + 2) (n + m)
        ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G _ (by omega) hgs hs0
        G.length (le_refl _)
      obtain ⟨st, hst⟩ : ∃ st, st = aj_stAt (n + m + G.length + 2) (n + m)
        ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G
        ((fun w => if w = r then n + m + G.length else n + m + G.length + 1), ([] : List Gate))
        G.length := ⟨_, rfl⟩
      rw [← hst] at q1 q2 q3
      obtain ⟨q11, q12, q13⟩ := q1
      obtain ⟨q31, q32⟩ := q3
      have hsyn : ∀ g ∈ [Gate.mk GateOp.and [], Gate.mk GateOp.or []] ++ st.2, ∀ i ∈ g.inputs,
          n + m + G.length ≤ i ∨
          ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0 := by
        intro g hg i hi
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with (hg | hg) | hg
        · rw [hg] at hi; simp at hi
        · rw [hg] at hi; simp at hi
        · exact q32 g hg i hi
      have hd := aj_deg_app n m G _ hsyn
      refine ⟨[Gate.mk GateOp.and [], Gate.mk GateOp.or []] ++ st.2,
        fun j => st.1 (n + j.val), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with (hg | hg) | hg
        · rw [hg]; simp
        · rw [hg]; simp
        · obtain ⟨h1, h2⟩ := q12 g hg
          refine ⟨?_, h2⟩
          rcases h1 with h1 | h1 <;> simp [h1]
      · show aj_RBL (n + m + G.length) _
        apply aj_RBL_append
        · exact aj_RBL_empty _ _ (by
            intro g hg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with hg | hg <;> rw [hg])
        · exact q13
      · simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_nil] at q2
        omega
      · intro k _
        exact hd _ (by omega)
      · intro j
        refine ⟨?_, hd _ (q31 _)⟩
        have := q11 (n + j.val)
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro x y j
        obtain ⟨base, hbase⟩ : ∃ base, base =
          (Circuit.mk G 0).wires (List.ofFn (Fin.append x y)) ++ [true, false] := ⟨_, rfl⟩
        have hvl : ((Circuit.mk G 0).wires (List.ofFn (Fin.append x y))).length
            = n + m + G.length := by
          rw [aj_wires_run, aj_run_length]
          simp
        have hBl : base.length = n + m + G.length + 2 := by
          rw [hbase, List.length_append, hvl]
          rfl
        have hw : (Circuit.mk (G ++ ([Gate.mk GateOp.and [], Gate.mk GateOp.or []] ++ st.2)) 0).wires
            (List.ofFn (Fin.append x y)) = aj_run aj_evf st.2 base := by
          rw [aj_wires_run]
          show aj_run aj_evf (G ++ ([Gate.mk GateOp.and [], Gate.mk GateOp.or []] ++ st.2)) _ = _
          rw [aj_run_append, aj_run_append, hbase, aj_wires_run]
          congr 1
          show aj_run aj_evf [Gate.mk GateOp.and [], Gate.mk GateOp.or []] (aj_run aj_evf G _) =
            aj_run aj_evf G _ ++ [true, false]
          simp [aj_run, aj_evf, GateOp.eval]
        rw [hw]
        have hv : ∀ i < n + m + G.length,
            ¬ 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 →
            base.getD i false = aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) i := by
          intro i hi hi0
          rw [hbase, aj_getD_app_lt _ _ _ _ (by omega)]
          exact (hF x y i).1 (by omega)
        have hT : base.getD (n + m + G.length) false = true := by
          rw [hbase, List.getD_append_right _ _ _ _ (by omega), hvl, Nat.sub_self]
          rfl
        have hFl : base.getD (n + m + G.length + 1) false = false := by
          rw [hbase, List.getD_append_right _ _ _ _ (by omega), hvl, Nat.add_sub_cancel_left]
          rfl
        have hx : ∀ w, ¬ 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 →
            aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))) w
              = aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) w := by
          intro w hw0
          exact (hF x _ w).1 (by omega)
        have hI0 := aj_tinv_init
          (fun w => 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0)
          (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))))
          (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false))) r (n + m + G.length)
          (aj_aval base ((fun w => if w = r then n + m + G.length else n + m + G.length + 1),
            ([] : List Gate)))
          (by
            intro w
            unfold aj_aval
            show (base).getD (if w = r then n + m + G.length else n + m + G.length + 1) false = _
            by_cases hwo : w = r
            · rw [aj_ite_p _ _ _ hwo, hT]; simp [hwo]
            · rw [aj_ite_n _ _ _ hwo, hFl]; simp [hwo])
          hx (fun _ => hr)
        have hfin := aj_iter_inv (n + m + G.length + 2) (n + m)
          ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G _ base _ _ _ _ hBl
          (by omega) hgs hg0 hv
          (fun k hk => aj_wv_gate (Circuit.mk G 0) (n + m) _ hR k hk)
          (fun k hk => aj_wv_gate (Circuit.mk G 0) (n + m) _ hR k hk)
          hx hI0 G.length (le_refl _)
        rw [← hst] at hfin
        obtain ⟨f1, _, f3⟩ := hfin
        have hjlt : n + j.val < n + m := by have := j.isLt; omega
        have hdj : 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD
            (n + j.val) 0 := by
          rw [aj_deg_input _ _ _ _ hjlt]
          have : n + j.val ∈ Finset.Ico n (n + m) := by simp
          simp [this]
        have huj : aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j)))
            (n + j.val) = true := by
          rw [aj_wv_input _ _ _ _ hjlt, aj_app_ge _ _ _ _ (by omega)]
          simp only [decide_eq_true_eq]
          ext
          simp
        show aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))) r =
          (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) r ||
            aj_aval base st (n + j.val))
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
              have hd' : 0 < ((Circuit.mk G 0).lineDegrees (n + m)
                (Finset.Ico n (n + m))).getD w 0 := hd
              rw [aj_deg_input _ _ _ _ hwN] at hd'
              have : w ∉ Finset.Ico n (n + m) := by simp; omega
              simp [this] at hd'
            rw [aj_wv_input _ _ _ _ hwN, aj_app_ge _ _ _ _ hwn] at hz
            simp only [decide_eq_true_eq] at hz
            have e : w = n + j.val := by
              rw [← hz]
              simp only
              omega
            rw [← e]
            exact ha
        · rintro (h | h)
          · exact (hF x _ r).2 h
          · exact f1 (n + j.val) (by omega) hdj h huj
    · -- one line and no line-dependent gate: the target is the line input
      have hrN : r < n + m := by
        by_contra hcon
        apply hbig
        have : 1 ≤ aj_cnt (n + m) ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m)))
            G.length := by
          unfold aj_cnt
          apply Finset.card_pos.mpr
          refine ⟨r - (n + m), ?_⟩
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          have e : n + m + (r - (n + m)) = r := by omega
          rw [e]
          exact hout
        omega
      have hn : n ≤ r := by
        by_contra hcon
        have : r ∉ Finset.Ico n (n + m) := by simp; omega
        rw [aj_deg_input _ _ _ _ hrN] at hout
        simp [this] at hout
      obtain ⟨s1, s2, s3, s4, s5⟩ := aj_single n m G (Gate.mk GateOp.and []) rfl (Or.inl rfl)
      refine ⟨[Gate.mk GateOp.and []], fun _ => n + m + G.length, s1, s2, ?_, s3,
        fun _ => s4, ?_⟩
      · simp only [List.length_singleton]
        omega
      · intro x y j
        rw [s5]
        show aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))) r =
          (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) r || _)
        rw [aj_wv_input _ _ _ _ hrN, aj_wv_input _ _ _ _ hrN, aj_app_ge _ _ _ _ hn, aj_app_ge _ _ _ _ hn]
        have e1 : (⟨r - n, by omega⟩ : Fin m) = j := by
          ext
          have := j.isLt
          simp only
          omega
        simp [e1, GateOp.eval]
  · obtain ⟨s1, s2, s3, s4, s5⟩ := aj_single n m G (Gate.mk GateOp.or []) rfl (Or.inr rfl)
    refine ⟨[Gate.mk GateOp.or []], fun _ => n + m + G.length, s1, s2, ?_, s3,
      fun _ => s4, ?_⟩
    · simp only [List.length_singleton]
      omega
    · intro x y j
      rw [s5]
      show aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))) r =
        (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) r || _)
      rw [(hF x _ r).1 (by omega)]
      simp [GateOp.eval]


def dflt : Gate := Gate.mk GateOp.or []

def W (G : List Gate) (x : List Bool) : List Bool :=
  G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def val (G : List Gate) (x : List Bool) (i : ℕ) : Bool := (W G x).getD i false

def d0 (n m : ℕ) : List ℕ :=
  (List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0

def Dg (G : List Gate) (d : List ℕ) : List ℕ :=
  G.foldl (fun d g => d ++ [g.lineDegree d]) d

def dg (n m : ℕ) (G : List Gate) (i : ℕ) : ℕ := (Dg G (d0 n m)).getD i 0

def RB (N : ℕ) (G : List Gate) : Prop :=
  ∀ j < G.length, ∀ i ∈ (G.getD j dflt).inputs, i < N + j

def Mono (G : List Gate) : Prop :=
  ∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def NC (n m : ℕ) (G : List Gate) : Prop :=
  ∀ j < G.length, (G.getD j dflt).op = GateOp.and → (G.getD j dflt).inputs.length = 2 →
    ∃ i ∈ (G.getD j dflt).inputs, dg n m G i = 0

theorem W_snoc (G : List Gate) (g : Gate) (x : List Bool) :
    W (G ++ [g]) x = W G x ++ [g.op.eval (g.inputs.map (val G x))] := by
  unfold W
  rw [List.foldl_append]
  rfl

theorem W_length (G : List Gate) (x : List Bool) : (W G x).length = x.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton G g ih => rw [W_snoc]; simp [ih]; omega

theorem val_prefix (G A : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + G.length) :
    val (G ++ A) x i = val G x i := by
  induction A using List.reverseRecOn with
  | nil => simp
  | append_singleton A a ih =>
    rw [← List.append_assoc]
    unfold val at *
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_length]; simp; omega)]
    exact ih

theorem val_input (G : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val G x i = x.getD i false := by
  have := val_prefix [] G x i (by simpa using hi)
  simpa [val, W] using this

theorem val_new (G : List Gate) (g : Gate) (x : List Bool) :
    val (G ++ [g]) x (x.length + G.length) = g.op.eval (g.inputs.map (val G x)) := by
  unfold val
  rw [W_snoc, List.getD_append_right _ _ _ _ (by rw [W_length])]
  simp [W_length]
  rfl

theorem RB_of_snoc (N : ℕ) (G : List Gate) (g : Gate) (h : RB N (G ++ [g])) : RB N G := by
  intro j hj i hi
  have := h j (by simp; omega) i
  rw [List.getD_append _ _ _ _ hj] at this
  exact this hi

theorem getD_app (G A : List Gate) (k : ℕ) :
    (G ++ A).getD (G.length + k) dflt = A.getD k dflt := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem val_gate (G : List Gate) (x : List Bool) (j : ℕ) (hrb : RB x.length G)
    (hj : j < G.length) :
    val G x (x.length + j) =
      (G.getD j dflt).op.eval ((G.getD j dflt).inputs.map (val G x)) := by
  induction G using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton G g ih =>
    by_cases hlt : j < G.length
    · rw [val_prefix _ _ _ _ (by omega), ih (RB_of_snoc _ _ _ hrb) hlt,
        List.getD_append _ _ _ _ hlt]
      congr 1
      apply List.map_congr_left
      intro i hi
      have := hrb j hj i (by rw [List.getD_append _ _ _ _ hlt]; exact hi)
      exact (val_prefix _ _ _ _ (by omega)).symm
    · have hje : j = G.length := by simp at hj; omega
      subst hje
      have hg : (G ++ [g]).getD G.length dflt = g := by
        simp
      rw [val_new, hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      have := hrb G.length hj i (by rw [hg]; exact hi)
      exact (val_prefix _ _ _ _ (by omega)).symm

theorem Dg_snoc (G : List Gate) (g : Gate) (d : List ℕ) :
    Dg (G ++ [g]) d = Dg G d ++ [g.lineDegree (Dg G d)] := by
  simp [Dg, List.foldl_append]

theorem Dg_length (G : List Gate) (d : List ℕ) : (Dg G d).length = d.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [Dg]
  | append_singleton G g ih => rw [Dg_snoc]; simp [ih]; omega

theorem d0_length (n m : ℕ) : (d0 n m).length = n + m := by simp [d0]

theorem dg_prefix (n m : ℕ) (G A : List Gate) (i : ℕ) (hi : i < n + m + G.length) :
    dg n m (G ++ A) i = dg n m G i := by
  induction A using List.reverseRecOn with
  | nil => simp
  | append_singleton A a ih =>
    rw [← List.append_assoc]
    unfold dg at *
    rw [Dg_snoc, List.getD_append _ _ _ _ (by rw [Dg_length, d0_length]; simp; omega)]
    exact ih

theorem dg_input (n m : ℕ) (G : List Gate) (i : ℕ) (hi : i < n + m) :
    dg n m G i = if n ≤ i then 1 else 0 := by
  have := dg_prefix n m [] G i (by simpa using hi)
  simp only [List.nil_append] at this
  rw [this]
  simp [dg, Dg, d0, hi]

theorem lineDegree_congr (g : Gate) (d d' : List ℕ)
    (h : ∀ i ∈ g.inputs, d.getD i 0 = d'.getD i 0) : g.lineDegree d = g.lineDegree d' := by
  have : g.inputs.map (fun i => d.getD i 0) = g.inputs.map (fun i => d'.getD i 0) :=
    List.map_congr_left h
  unfold Gate.lineDegree
  rw [this]

theorem dg_new (n m : ℕ) (G : List Gate) (g : Gate) :
    dg n m (G ++ [g]) (n + m + G.length) = g.lineDegree (Dg G (d0 n m)) := by
  unfold dg
  rw [Dg_snoc, List.getD_append_right _ _ _ _ (by rw [Dg_length, d0_length])]
  simp [Dg_length, d0_length]

theorem dg_gate (n m : ℕ) (G : List Gate) (j : ℕ) (hrb : RB (n + m) G) (hj : j < G.length) :
    dg n m G (n + m + j) = (G.getD j dflt).lineDegree (Dg G (d0 n m)) := by
  induction G using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton G g ih =>
    by_cases hlt : j < G.length
    · rw [dg_prefix _ _ _ _ _ (by omega), ih (RB_of_snoc _ _ _ hrb) hlt,
        List.getD_append _ _ _ _ hlt]
      apply lineDegree_congr
      intro i hi
      have := hrb j hj i (by rw [List.getD_append _ _ _ _ hlt]; exact hi)
      exact (dg_prefix n m G [g] i (by omega)).symm
    · have hje : j = G.length := by simp at hj; omega
      subst hje
      have hg : (G ++ [g]).getD G.length dflt = g := by
        simp
      rw [dg_new, hg]
      apply lineDegree_congr
      intro i hi
      have := hrb G.length hj i (by rw [hg]; exact hi)
      exact (dg_prefix n m G [g] i (by omega)).symm

theorem lineDegree_and (g : Gate) (d : List ℕ) (h : g.op = GateOp.and) :
    g.lineDegree d = (g.inputs.map fun i => d.getD i 0).sum := by
  unfold Gate.lineDegree
  simp [h]

theorem lineDegree_or (g : Gate) (d : List ℕ) (h : g.op = GateOp.or) :
    g.lineDegree d = (g.inputs.map fun i => d.getD i 0).foldr max 0 := by
  unfold Gate.lineDegree
  simp [h]


def xy {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) : List Bool := List.ofFn (Fin.append x y)

theorem xy_length {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) : (xy x y).length = n + m := by
  simp [xy]

theorem xy_left {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ) (hi : i < n) :
    (xy x y).getD i false = x ⟨i, hi⟩ := by
  unfold xy
  have hl : i < (List.ofFn (Fin.append x y)).length := by simp; omega
  rw [List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
  exact Fin.append_left x y ⟨i, hi⟩

theorem xy_right {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (l : Fin m) :
    (xy x y).getD (n + l) false = y l := by
  unfold xy
  have hl : n + (l : ℕ) < (List.ofFn (Fin.append x y)).length := by simp
  rw [List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
  exact Fin.append_right x y l

theorem val_x {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ)
    (hi : i < n) : val G (xy x y) i = x ⟨i, hi⟩ := by
  rw [val_input _ _ _ (by rw [xy_length]; omega), xy_left]

theorem val_y {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (l : Fin m) :
    val G (xy x y) (n + l) = y l := by
  rw [val_input _ _ _ (by rw [xy_length]; omega), xy_right]

theorem val_out (G : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + G.length ≤ i) :
    val G x i = false := by
  unfold val
  exact List.getD_eq_default _ _ (by rw [W_length]; exact hi)

theorem val_g {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (j : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) :
    val G (xy x y) (n + m + j) =
      (G.getD j dflt).op.eval ((G.getD j dflt).inputs.map (val G (xy x y))) := by
  have := val_gate G (xy x y) j (by rw [xy_length]; exact hrb) hj
  rw [xy_length] at this
  exact this

theorem dg_out (n m : ℕ) (G : List Gate) (i : ℕ) (hi : n + m + G.length ≤ i) :
    dg n m G i = 0 := by
  unfold dg
  exact List.getD_eq_default _ _ (by rw [Dg_length, d0_length]; exact hi)

theorem shape (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

theorem getD_mem (G : List Gate) (j : ℕ) (hj : j < G.length) : G.getD j dflt ∈ G := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem opcase (G : List Gate) (hm : Mono G) (j : ℕ) (hj : j < G.length) :
    ((G.getD j dflt).op = GateOp.and ∨ (G.getD j dflt).op = GateOp.or) ∧
      (G.getD j dflt).inputs.length ≤ 2 := by
  have := hm _ (getD_mem G j hj)
  refine ⟨?_, this.2⟩
  have h1 := this.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem le_foldr_max (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem lineDegree_zero (g : Gate) (d : List ℕ) (h : g.lineDegree d = 0) :
    ∀ a ∈ g.inputs, d.getD a 0 = 0 := by
  intro a ha
  have hmem : d.getD a 0 ∈ g.inputs.map (fun i => d.getD i 0) := List.mem_map.mpr ⟨a, ha, rfl⟩
  unfold Gate.lineDegree at h
  split_ifs at h
  · exact List.sum_eq_zero_iff.mp h _ hmem
  · have := le_foldr_max _ _ hmem
    omega

theorem indep (n m : ℕ) (G : List Gate) (hrb : RB (n + m) G) (x : Fin n → Bool)
    (y y' : Fin m → Bool) :
    ∀ i, dg n m G i = 0 → val G (xy x y) i = val G (xy x y') i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hd
    by_cases h1 : i < n
    · rw [val_x _ _ _ _ h1, val_x _ _ _ _ h1]
    by_cases h2 : i < n + m
    · rw [dg_input _ _ _ _ h2] at hd
      simp [show n ≤ i by omega] at hd
    by_cases h3 : i < n + m + G.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + m + j := ⟨i - (n + m), by omega⟩
      have hj : j < G.length := by omega
      rw [val_g G x y j hrb hj, val_g G x y' j hrb hj]
      congr 1
      apply List.map_congr_left
      intro a ha
      have ha' := hrb j hj a ha
      apply ih a (by omega)
      rw [dg_gate n m G j hrb hj] at hd
      exact lineDegree_zero _ _ hd a ha
    · rw [val_out _ _ _ (by rw [xy_length]; omega), val_out _ _ _ (by rw [xy_length]; omega)]

theorem ex_or {m : ℕ} (Y : Finset (Fin m)) (f g : Fin m → Bool) :
    decide (∃ j ∈ Y, (f j || g j) = true) =
      (decide (∃ j ∈ Y, f j = true) || decide (∃ j ∈ Y, g j = true)) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨j, hj, h | h⟩
    · exact Or.inl ⟨j, hj, h⟩
    · exact Or.inr ⟨j, hj, h⟩
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · exact ⟨j, hj, Or.inl h⟩
    · exact ⟨j, hj, Or.inr h⟩

theorem ex_and {m : ℕ} (Y : Finset (Fin m)) (c : Bool) (g : Fin m → Bool) :
    decide (∃ j ∈ Y, (c && g j) = true) = (c && decide (∃ j ∈ Y, g j = true)) := by
  cases c <;> simp

theorem ex_and' {m : ℕ} (Y : Finset (Fin m)) (c : Bool) (g : Fin m → Bool) :
    decide (∃ j ∈ Y, (g j && c) = true) = (decide (∃ j ∈ Y, g j = true) && c) := by
  cases c <;> simp

theorem and_lin {m : ℕ} (Y : Finset (Fin m)) (c bY b0 : Bool) (bj : Fin m → Bool)
    (h : bY = (b0 || decide (∃ j ∈ Y, bj j = true))) :
    (c && bY) = ((c && b0) || decide (∃ j ∈ Y, (c && bj j) = true)) := by
  rw [ex_and, h]
  cases c <;> simp

theorem and_lin' {m : ℕ} (Y : Finset (Fin m)) (c bY b0 : Bool) (bj : Fin m → Bool)
    (h : bY = (b0 || decide (∃ j ∈ Y, bj j = true))) :
    (bY && c) = ((b0 && c) || decide (∃ j ∈ Y, (bj j && c) = true)) := by
  rw [ex_and', h]
  cases c <;> simp

theorem or_lin {m : ℕ} (Y : Finset (Fin m)) (fY f0 : ℕ → Bool) (fj : Fin m → ℕ → Bool)
    (l : List ℕ)
    (h : ∀ a ∈ l, fY a = (f0 a || decide (∃ j ∈ Y, fj j a = true))) :
    (l.map fY).any id =
      ((l.map f0).any id || decide (∃ j ∈ Y, (l.map (fj j)).any id = true)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), h a List.mem_cons_self, ex_or]
    generalize decide (∃ j ∈ Y, fj j a = true) = p
    generalize decide (∃ j ∈ Y, (List.map (fj j) l).any id = true) = q
    cases f0 a <;> cases p <;> cases q <;> simp

theorem linear (n m : ℕ) (G : List Gate) (hm : Mono G) (hrb : RB (n + m) G) (hnc : NC n m G)
    (x : Fin n → Bool) (Y : Finset (Fin m)) :
    ∀ i, val G (xy x (fun l => decide (l ∈ Y))) i =
      (val G (xy x (fun _ : Fin m => false)) i ||
        decide (∃ j ∈ Y, val G (xy x (fun l => decide (l = j))) i = true)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · simp only [val_x _ _ _ _ h1]
      cases x ⟨i, h1⟩ <;> simp
    by_cases h2 : i < n + m
    · obtain ⟨l, rfl⟩ : ∃ l : Fin m, i = n + (l : ℕ) := ⟨⟨i - n, by omega⟩, by simp; omega⟩
      simp only [val_y]
      simp
    by_cases h3 : i < n + m + G.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + m + j := ⟨i - (n + m), by omega⟩
      have hj : j < G.length := by omega
      have e : ∀ y : Fin m → Bool, val G (xy x y) (n + m + j) =
          (G.getD j dflt).op.eval ((G.getD j dflt).inputs.map (val G (xy x y))) :=
        fun y => val_g G x y j hrb hj
      simp only [e]
      have hr := hrb j hj
      have hc := hnc j hj
      obtain ⟨ho, hlen⟩ := opcase G hm j hj
      generalize G.getD j dflt = g at hr hc ho hlen ⊢
      rcases ho with ho | ho
      · rcases shape _ hlen with h | ⟨a, h⟩ | ⟨a, b, h⟩
        · simp [ho, h, GateOp.eval]
        · simp only [ho, h, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, Bool.and_true, id_eq]
          exact ih a (hr a (by simp [h]))
        · simp only [ho, h, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, Bool.and_true, id_eq]
          have ha := hr a (by simp [h])
          have hb := hr b (by simp [h])
          obtain ⟨i, hi, hz⟩ := hc ho (by simp [h])
          rw [h] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · obtain ⟨c, hc0⟩ : ∃ c, val G (xy x (fun _ : Fin m => false)) i = c := ⟨_, rfl⟩
            have hcY : val G (xy x (fun l => decide (l ∈ Y))) i = c := by
              rw [← hc0]; exact indep n m G hrb x _ _ i hz
            have hcj : ∀ j : Fin m, val G (xy x (fun l => decide (l = j))) i = c := by
              intro j; rw [← hc0]; exact indep n m G hrb x _ _ i hz
            simp only [hc0, hcY, hcj]
            exact and_lin Y c _ _ _ (ih b hb)
          · obtain ⟨c, hc0⟩ : ∃ c, val G (xy x (fun _ : Fin m => false)) i = c := ⟨_, rfl⟩
            have hcY : val G (xy x (fun l => decide (l ∈ Y))) i = c := by
              rw [← hc0]; exact indep n m G hrb x _ _ i hz
            have hcj : ∀ j : Fin m, val G (xy x (fun l => decide (l = j))) i = c := by
              intro j; rw [← hc0]; exact indep n m G hrb x _ _ i hz
            simp only [hc0, hcY, hcj]
            exact and_lin' Y c _ _ _ (ih a ha)
      · simp only [ho, GateOp.eval]
        exact or_lin Y _ _ _ g.inputs (fun a ha => ih a (hr a ha))
    · have hv : ∀ y : Fin m → Bool, val G (xy x y) i = false :=
        fun y => val_out _ _ _ (by rw [xy_length]; omega)
      simp only [hv]
      simp

def cnt (n m : ℕ) (G : List Gate) : ℕ :=
  ((Dg G (d0 n m)).drop (n + m)).countP (fun a => decide (0 < a))

theorem cnt_snoc (n m : ℕ) (G : List Gate) (g : Gate) :
    cnt n m (G ++ [g]) =
      cnt n m G + (if 0 < dg n m (G ++ [g]) (n + m + G.length) then 1 else 0) := by
  rw [dg_new]
  unfold cnt
  rw [Dg_snoc, List.drop_append_of_le_length (by rw [Dg_length, d0_length]; omega),
    List.countP_append]
  simp [List.countP_cons]

theorem cnt_snoc_le (n m : ℕ) (G : List Gate) (g : Gate) :
    cnt n m (G ++ [g]) ≤ cnt n m G + 1 := by
  rw [cnt_snoc]
  split_ifs <;> omega

theorem cnt_append_le (n m : ℕ) (G A : List Gate) :
    cnt n m (G ++ A) ≤ cnt n m G + A.length := by
  induction A using List.reverseRecOn with
  | nil => simp
  | append_singleton A a ih =>
    rw [← List.append_assoc]
    have := cnt_snoc_le n m (G ++ A) a
    simp only [List.length_append, List.length_singleton]
    omega

theorem cnt_append_zero (n m : ℕ) (G A : List Gate)
    (h : ∀ k < A.length, dg n m (G ++ A) (n + m + G.length + k) = 0) :
    cnt n m (G ++ A) = cnt n m G := by
  induction A using List.reverseRecOn with
  | nil => simp
  | append_singleton A a ih =>
    have h1 : cnt n m (G ++ A) = cnt n m G := by
      apply ih
      intro k hk
      have := h k (by simp; omega)
      rw [← List.append_assoc, dg_prefix _ _ _ _ _ (by simp; omega)] at this
      exact this
    have h2 := h A.length (by simp)
    rw [← List.append_assoc] at h2 ⊢
    rw [cnt_snoc, h1]
    have e : n + m + (G ++ A).length = n + m + G.length + A.length := by simp; omega
    rw [e, h2]
    simp

theorem ncard_le_cnt (n m : ℕ) (G : List Gate) :
    Set.ncard {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} ≤ cnt n m G := by
  induction G using List.reverseRecOn with
  | nil => simp
  | append_singleton G g ih =>
    have hfin : Set.Finite {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} :=
      (Set.finite_Iio G.length).subset (fun j hj => hj.1)
    rw [cnt_snoc]
    by_cases hpos : 0 < dg n m (G ++ [g]) (n + m + G.length)
    · have hsub : {j : ℕ | j < (G ++ [g]).length ∧ 0 < dg n m (G ++ [g]) (n + m + j)} ⊆
          insert G.length {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} := by
        intro j hj
        obtain ⟨h1, h2⟩ := hj
        by_cases hjl : j < G.length
        · right
          rw [dg_prefix _ _ _ _ _ (by omega)] at h2
          exact ⟨hjl, h2⟩
        · left
          simp at h1
          show j = G.length
          omega
      have h1 := Set.ncard_le_ncard hsub (hfin.insert _)
      have h2 := Set.ncard_insert_le G.length {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)}
      simp only [hpos, ite_true]
      omega
    · have hsub : {j : ℕ | j < (G ++ [g]).length ∧ 0 < dg n m (G ++ [g]) (n + m + j)} ⊆
          {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} := by
        intro j hj
        obtain ⟨h1, h2⟩ := hj
        by_cases hjl : j < G.length
        · rw [dg_prefix _ _ _ _ _ (by omega)] at h2
          exact ⟨hjl, h2⟩
        · simp at h1
          have : j = G.length := by omega
          subst this
          exact absurd h2 hpos
      have h1 := Set.ncard_le_ncard hsub hfin
      simp only [hpos, ite_false]
      omega

theorem RB_append (N : ℕ) (G A : List Gate) (h : RB N G)
    (hA : ∀ k < A.length, ∀ i ∈ (A.getD k dflt).inputs, i < N + G.length + k) :
    RB N (G ++ A) := by
  intro j hj i hi
  by_cases hlt : j < G.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h j hlt i hi
  · obtain ⟨k, rfl⟩ : ∃ k, j = G.length + k := ⟨j - G.length, by omega⟩
    rw [getD_app] at hi
    have := hA k (by simp at hj; omega) i hi
    omega

theorem Mono_append (G A : List Gate) (h : Mono G)
    (hA : ∀ g ∈ A, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Mono (G ++ A) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · exact hA g hg

theorem NC_append (n m : ℕ) (G A : List Gate) (hrb : RB (n + m) (G ++ A)) (h : NC n m G)
    (hA : ∀ k < A.length, (A.getD k dflt).op = GateOp.and → (A.getD k dflt).inputs.length = 2 →
      ∃ i ∈ (A.getD k dflt).inputs, dg n m (G ++ A) i = 0) :
    NC n m (G ++ A) := by
  intro j hj ho hl
  by_cases hlt : j < G.length
  · have hr := hrb j hj
    rw [List.getD_append _ _ _ _ hlt] at ho hl hr ⊢
    obtain ⟨i, hi, hz⟩ := h j hlt ho hl
    refine ⟨i, hi, ?_⟩
    rw [dg_prefix _ _ _ _ _ (by have := hr i hi; omega)]
    exact hz
  · obtain ⟨k, rfl⟩ : ∃ k, j = G.length + k := ⟨j - G.length, by omega⟩
    rw [getD_app] at ho hl ⊢
    exact hA k (by simp at hj; omega) ho hl

theorem lineDegree_eq_zero (g : Gate) (d : List ℕ) (h : ∀ a ∈ g.inputs, d.getD a 0 = 0) :
    g.lineDegree d = 0 := by
  have e : g.inputs.map (fun i => d.getD i 0) = g.inputs.map (fun _ => 0) :=
    List.map_congr_left h
  have e2 : ∀ l : List ℕ, (l.map (fun _ => 0)).foldr max 0 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      show max 0 (List.foldr max 0 (List.map (fun _ => 0) l)) = 0
      rw [ih]
      rfl
  unfold Gate.lineDegree
  rw [e]
  split_ifs
  · simp
  · exact e2 _

-- a block of gates of degree zero keeps everything
theorem zero_block (n m : ℕ) (G A : List Gate) (hm : Mono G) (hrb : RB (n + m) G)
    (hnc : NC n m G)
    (hA1 : ∀ g ∈ A, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hA2 : ∀ k < A.length, ∀ i ∈ (A.getD k dflt).inputs, i < n + m + G.length + k)
    (hA3 : ∀ k < A.length, dg n m (G ++ A) (n + m + G.length + k) = 0) :
    Mono (G ++ A) ∧ RB (n + m) (G ++ A) ∧ NC n m (G ++ A) ∧ cnt n m (G ++ A) = cnt n m G := by
  have hrb' := RB_append _ G A hrb hA2
  refine ⟨Mono_append G A hm hA1, hrb', ?_, cnt_append_zero n m G A hA3⟩
  apply NC_append n m G A hrb' hnc
  intro k hk ho hl
  have hz := hA3 k hk
  have e : n + m + G.length + k = n + m + (G.length + k) := by omega
  rw [e, dg_gate n m (G ++ A) (G.length + k) hrb' (by simp; omega), getD_app] at hz
  have hall := lineDegree_zero _ _ hz
  rcases shape _ (le_of_eq hl) with h | ⟨a, h⟩ | ⟨a, b, h⟩
  · rw [h] at hl; simp at hl
  · rw [h] at hl; simp at hl
  · exact ⟨a, by rw [h]; exact List.mem_cons_self, hall a (by rw [h]; exact List.mem_cons_self)⟩

-- zero copy
def qx (n m : ℕ) (i : ℕ) : Bool := decide (i < n ∨ n + m ≤ i)

def zc (n m : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => Gate.mk GateOp.or (g.inputs.filter (qx n m))
  | _ => if g.inputs.all (qx n m) = true then g else Gate.mk GateOp.or []

theorem zc_or (n m : ℕ) (g : Gate) (h : g.op = GateOp.or) :
    zc n m g = Gate.mk GateOp.or (g.inputs.filter (qx n m)) := by
  simp [zc, h]

theorem zc_and (n m : ℕ) (g : Gate) (h : g.op = GateOp.and) :
    zc n m g = if g.inputs.all (qx n m) = true then g else Gate.mk GateOp.or [] := by
  simp [zc, h]

theorem getD_map (C : List Gate) (f : Gate → Gate) (j : ℕ) (hj : j < C.length) :
    (C.map f).getD j dflt = f (C.getD j dflt) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]
  simp

theorem zc_in (n m : ℕ) (g : Gate) (ho : g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i ∈ (zc n m g).inputs, i ∈ g.inputs ∧ qx n m i = true := by
  intro i hi
  rcases ho with ho | ho
  · rw [zc_and n m g ho] at hi
    split_ifs at hi with hall
    · exact ⟨hi, List.all_eq_true.mp hall i hi⟩
    · simp at hi
  · rw [zc_or n m g ho] at hi
    exact List.mem_filter.mp hi

theorem zc_mono (n m : ℕ) (g : Gate) (ho : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hl : g.inputs.length ≤ 2) :
    ((zc n m g).op = GateOp.and ∨ (zc n m g).op = GateOp.or) ∧ (zc n m g).inputs.length ≤ 2 := by
  rcases ho with ho | ho
  · rw [zc_and n m g ho]
    split_ifs
    · exact ⟨Or.inl ho, hl⟩
    · exact ⟨Or.inr rfl, by simp⟩
  · rw [zc_or n m g ho]
    exact ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) hl⟩

theorem Z_mono (n m : ℕ) (C : List Gate) (hm : Mono C) : Mono (C.map (zc n m)) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have h := hm g0 hg0
  have ho : g0.op = GateOp.and ∨ g0.op = GateOp.or := by
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  have := zc_mono n m g0 ho h.2
  refine ⟨?_, this.2⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact this.1

theorem Z_in (n m : ℕ) (C : List Gate) (hm : Mono C) (j : ℕ) (hj : j < C.length) :
    ∀ i ∈ ((C.map (zc n m)).getD j dflt).inputs,
      i ∈ (C.getD j dflt).inputs ∧ (i < n ∨ n + m ≤ i) := by
  intro i hi
  rw [getD_map C _ j hj] at hi
  have := zc_in n m _ (opcase C hm j hj).1 i hi
  refine ⟨this.1, ?_⟩
  have h2 := this.2
  simp only [qx, decide_eq_true_eq] at h2
  exact h2

theorem Z_rb (n m : ℕ) (C : List Gate) (hm : Mono C) (hrb : RB (n + m) C) :
    RB (n + m) (C.map (zc n m)) := by
  intro j hj i hi
  have hj' : j < C.length := by simpa using hj
  exact hrb j hj' i (Z_in n m C hm j hj' i hi).1

theorem Z_dg (n m : ℕ) (C : List Gate) (hm : Mono C) (hrb : RB (n + m) C) :
    ∀ i, (i < n ∨ n + m ≤ i) → dg n m (C.map (zc n m)) i = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hq
    by_cases h1 : i < n
    · rw [dg_input _ _ _ _ (by omega)]
      simp; omega
    by_cases h3 : i < n + m + C.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + m + j := ⟨i - (n + m), by omega⟩
      have hj : j < C.length := by omega
      rw [dg_gate n m _ j (Z_rb n m C hm hrb) (by simpa using hj)]
      apply lineDegree_eq_zero
      intro a ha
      have := Z_in n m C hm j hj a ha
      have hlt := hrb j hj a this.1
      exact ih a (by omega) this.2
    · exact dg_out _ _ _ _ (by simp; omega)

theorem val_y0 {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (a : ℕ) (h1 : n ≤ a)
    (h2 : a < n + m) : val G (xy x (fun _ : Fin m => false)) a = false := by
  have := val_y G x (fun _ : Fin m => false) ⟨a - n, by omega⟩
  have e : n + ((⟨a - n, by omega⟩ : Fin m) : ℕ) = a := by simp; omega
  rw [e] at this
  exact this

theorem any_filter (l : List ℕ) (q : ℕ → Bool) (f f' : ℕ → Bool)
    (h1 : ∀ a ∈ l, q a = true → f a = f' a) (h2 : ∀ a ∈ l, q a = false → f' a = false) :
    ((l.filter q).map f).any id = (l.map f').any id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
      (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
    cases hq : q a
    · rw [List.filter_cons_of_neg (by simp [hq]), ih']
      simp [h2 a List.mem_cons_self hq]
    · rw [List.filter_cons_of_pos (by simp [hq])]
      simp only [List.map_cons, List.any_cons, id_eq]
      rw [ih', h1 a List.mem_cons_self hq]

theorem Z_val (n m : ℕ) (C : List Gate) (hm : Mono C) (hrb : RB (n + m) C)
    (x : Fin n → Bool) (y : Fin m → Bool) :
    ∀ i, (i < n ∨ n + m ≤ i) →
      val (C.map (zc n m)) (xy x y) i = val C (xy x (fun _ : Fin m => false)) i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hq
    by_cases h1 : i < n
    · rw [val_x _ _ _ _ h1, val_x _ _ _ _ h1]
    by_cases h3 : i < n + m + C.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + m + j := ⟨i - (n + m), by omega⟩
      have hj : j < C.length := by omega
      rw [val_g _ x y j (Z_rb n m C hm hrb) (by simpa using hj), val_g C x _ j hrb hj,
        getD_map C _ j hj]
      have hr := hrb j hj
      obtain ⟨ho, hlen⟩ := opcase C hm j hj
      generalize C.getD j dflt = g at hr ho hlen ⊢
      rcases ho with ho | ho
      · rw [zc_and n m g ho]
        split_ifs with hall
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hqa := List.all_eq_true.mp hall a ha
          simp only [qx, decide_eq_true_eq] at hqa
          exact ih a (by have := hr a ha; omega) hqa
        · have hex : ∃ a ∈ g.inputs, qx n m a = false := by
            by_contra hcon
            apply hall
            apply List.all_eq_true.mpr
            intro a ha
            by_contra hna
            exact hcon ⟨a, ha, by simpa using hna⟩
          obtain ⟨a, ha, hqa⟩ := hex
          simp only [qx, decide_eq_false_iff_not, not_or, not_lt, not_le] at hqa
          have hv := val_y0 C x a hqa.1 hqa.2
          rw [ho]
          symm
          simp only [GateOp.eval, List.map_nil, List.any_nil]
          apply List.all_eq_false.mpr
          exact ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, by simp [hv]⟩
      · rw [zc_or n m g ho, ho]
        simp only [GateOp.eval]
        apply any_filter
        · intro a ha hqa
          simp only [qx, decide_eq_true_eq] at hqa
          exact ih a (by have := hr a ha; omega) hqa
        · intro a ha hqa
          simp only [qx, decide_eq_false_iff_not, not_or, not_lt, not_le] at hqa
          exact val_y0 C x a hqa.1 hqa.2
    · rw [val_out _ _ _ (by rw [xy_length]; simp; omega),
        val_out _ _ _ (by rw [xy_length]; omega)]

def St (n m : ℕ) (G : List Gate) : Prop := Mono G ∧ RB (n + m) G ∧ NC n m G

theorem val_or2 {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (j a b : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) (hg : G.getD j dflt = Gate.mk GateOp.or [a, b]) :
    val G (xy x y) (n + m + j) = (val G (xy x y) a || val G (xy x y) b) := by
  rw [val_g G x y j hrb hj, hg]
  simp [GateOp.eval]

theorem val_and2 {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (j a b : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) (hg : G.getD j dflt = Gate.mk GateOp.and [a, b]) :
    val G (xy x y) (n + m + j) = (val G (xy x y) a && val G (xy x y) b) := by
  rw [val_g G x y j hrb hj, hg]
  simp [GateOp.eval]

theorem dg_or2 (n m : ℕ) (G : List Gate) (j a b : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) (hg : G.getD j dflt = Gate.mk GateOp.or [a, b]) :
    dg n m G (n + m + j) = max (dg n m G a) (dg n m G b) := by
  rw [dg_gate n m G j hrb hj, hg, lineDegree_or _ _ rfl]
  simp [dg]

theorem dg_and2 (n m : ℕ) (G : List Gate) (j a b : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) (hg : G.getD j dflt = Gate.mk GateOp.and [a, b]) :
    dg n m G (n + m + j) = dg n m G a + dg n m G b := by
  rw [dg_gate n m G j hrb hj, hg, lineDegree_and _ _ rfl]
  simp [dg]

def muxA1 (N len zu zv b c : ℕ) : List Gate :=
  [Gate.mk GateOp.or [zu, b], Gate.mk GateOp.or [zv, c],
    Gate.mk GateOp.and [N + (len + 0), N + (len + 1)]]

def muxA2 (N len yl e : ℕ) : List Gate :=
  [Gate.mk GateOp.and [yl, N + (len + 2)], Gate.mk GateOp.or [e, N + (len + 3)]]

theorem mux_step (n m : ℕ) (G : List Gate) (hst : St n m G) (zu zv b c e : ℕ) (l : Fin m)
    (hzu : zu < n + m + G.length) (hzv : zv < n + m + G.length) (hb : b < n + m + G.length)
    (hc : c < n + m + G.length) (he : e < n + m + G.length)
    (dzu : dg n m G zu = 0) (dzv : dg n m G zv = 0) (db : dg n m G b = 0)
    (dc : dg n m G c = 0) (de : dg n m G e ≤ 1) :
    St n m (G ++ (muxA1 (n + m) G.length zu zv b c ++ muxA2 (n + m) G.length (n + l) e)) ∧
    cnt n m (G ++ (muxA1 (n + m) G.length zu zv b c ++ muxA2 (n + m) G.length (n + l) e)) ≤
      cnt n m G + 2 ∧
    dg n m (G ++ (muxA1 (n + m) G.length zu zv b c ++ muxA2 (n + m) G.length (n + l) e))
      (n + m + (G.length + 4)) ≤ 1 ∧
    ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val (G ++ (muxA1 (n + m) G.length zu zv b c ++ muxA2 (n + m) G.length (n + l) e))
        (xy x y) (n + m + (G.length + 4)) =
      (val G (xy x y) e || (y l && ((val G (xy x y) zu || val G (xy x y) b) &&
        (val G (xy x y) zv || val G (xy x y) c)))) := by
  obtain ⟨hm, hrb, hnc⟩ := hst
  have hl := l.isLt
  generalize hA1 : muxA1 (n + m) G.length zu zv b c = A1
  generalize hA2 : muxA2 (n + m) G.length (n + l) e = A2
  have hlen : (A1 ++ A2).length = 5 := by rw [← hA1, ← hA2]; rfl
  have hrb' : RB (n + m) (G ++ (A1 ++ A2)) := by
    apply RB_append _ _ _ hrb
    intro k hk i hi
    rw [hlen] at hk
    rw [← hA1, ← hA2] at hi
    interval_cases k <;> simp [muxA1, muxA2] at hi <;> omega
  have g0 : (G ++ (A1 ++ A2)).getD (G.length + 0) dflt = Gate.mk GateOp.or [zu, b] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have g1 : (G ++ (A1 ++ A2)).getD (G.length + 1) dflt = Gate.mk GateOp.or [zv, c] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have g2 : (G ++ (A1 ++ A2)).getD (G.length + 2) dflt =
      Gate.mk GateOp.and [n + m + (G.length + 0), n + m + (G.length + 1)] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have g3 : (G ++ (A1 ++ A2)).getD (G.length + 3) dflt =
      Gate.mk GateOp.and [n + l, n + m + (G.length + 2)] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have g4 : (G ++ (A1 ++ A2)).getD (G.length + 4) dflt =
      Gate.mk GateOp.or [e, n + m + (G.length + 3)] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have lt : ∀ k < 5, G.length + k < (G ++ (A1 ++ A2)).length := by
    intro k hk
    rw [List.length_append, hlen]
    omega
  have p : ∀ i, i < n + m + G.length → dg n m (G ++ (A1 ++ A2)) i = dg n m G i :=
    fun i hi => dg_prefix n m G _ i hi
  have d_0 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 0)) = 0 := by
    rw [dg_or2 n m _ _ zu b hrb' (lt 0 (by omega)) g0, p zu hzu, p b hb, dzu, db]
    rfl
  have d_1 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 1)) = 0 := by
    rw [dg_or2 n m _ _ zv c hrb' (lt 1 (by omega)) g1, p zv hzv, p c hc, dzv, dc]
    rfl
  have d_2 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 2)) = 0 := by
    rw [dg_and2 n m _ _ _ _ hrb' (lt 2 (by omega)) g2, d_0, d_1]
  have d_3 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 3)) = 1 := by
    rw [dg_and2 n m _ _ _ _ hrb' (lt 3 (by omega)) g3, d_2, p _ (by omega),
      dg_input _ _ _ _ (by omega)]
    simp
  have d_4 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 4)) ≤ 1 := by
    rw [dg_or2 n m _ _ _ _ hrb' (lt 4 (by omega)) g4, d_3, p e he]
    exact max_le de (le_refl 1)
  have hmono' : Mono (G ++ (A1 ++ A2)) := by
    apply Mono_append G _ hm
    intro g hg
    rw [← hA1, ← hA2] at hg
    simp only [muxA1, muxA2, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  have hnc' : NC n m (G ++ (A1 ++ A2)) := by
    apply NC_append n m G _ hrb' hnc
    intro k hk ho hl2
    rw [hlen] at hk
    have h0 := g0
    have h1 := g1
    have h2 := g2
    have h3 := g3
    have h4 := g4
    rw [getD_app] at h0 h1 h2 h3 h4
    interval_cases k
    · rw [h0] at ho; simp at ho
    · rw [h1] at ho; simp at ho
    · rw [h2]
      exact ⟨n + m + (G.length + 0), List.mem_cons_self, d_0⟩
    · rw [h3]
      exact ⟨n + m + (G.length + 2), by simp, d_2⟩
    · rw [h4] at ho; simp at ho
  have hA1len : A1.length = 3 := by rw [← hA1]; rfl
  have hA2len : A2.length = 2 := by rw [← hA2]; rfl
  have c1 : cnt n m (G ++ A1) = cnt n m G := by
    apply cnt_append_zero
    intro k hk
    rw [hA1len] at hk
    rw [← dg_prefix n m (G ++ A1) A2 _ (by rw [List.length_append, hA1len]; omega),
      List.append_assoc]
    interval_cases k
    · exact d_0
    · exact d_1
    · exact d_2
  have c2 := cnt_append_le n m (G ++ A1) A2
  rw [List.append_assoc, hA2len, c1] at c2
  refine ⟨⟨hmono', hrb', hnc'⟩, c2, d_4, ?_⟩
  intro x y
  have pv : ∀ i, i < n + m + G.length →
      val (G ++ (A1 ++ A2)) (xy x y) i = val G (xy x y) i :=
    fun i hi => val_prefix G _ _ i (by rw [xy_length]; exact hi)
  rw [val_or2 _ x y _ _ _ hrb' (lt 4 (by omega)) g4,
    val_and2 _ x y _ _ _ hrb' (lt 3 (by omega)) g3,
    val_and2 _ x y _ _ _ hrb' (lt 2 (by omega)) g2,
    val_or2 _ x y _ _ _ hrb' (lt 0 (by omega)) g0,
    val_or2 _ x y _ _ _ hrb' (lt 1 (by omega)) g1,
    pv e he, pv zu hzu, pv b hb, pv zv hzv, pv c hc, val_y]

theorem ex_succ {m : ℕ} (P : Fin m → Bool) (l : ℕ) (hl : l < m) :
    decide (∃ j : Fin m, (j : ℕ) < l + 1 ∧ P j = true) =
      (decide (∃ j : Fin m, (j : ℕ) < l ∧ P j = true) || P ⟨l, hl⟩) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨j, hj, hp⟩
    by_cases h : (j : ℕ) < l
    · exact Or.inl ⟨j, h, hp⟩
    · right
      have : j = ⟨l, hl⟩ := Fin.ext (by simp; omega)
      rw [← this]
      exact hp
  · rintro (⟨j, hj, hp⟩ | hp)
    · exact ⟨j, by omega, hp⟩
    · exact ⟨⟨l, hl⟩, by simp, hp⟩

theorem mux_loop (n m : ℕ) (G : List Gate) (hst : St n m G) (zu zv e0 : ℕ) (b c : Fin m → ℕ)
    (hzu : zu < n + m + G.length) (hzv : zv < n + m + G.length)
    (hb : ∀ j, b j < n + m + G.length) (hc : ∀ j, c j < n + m + G.length)
    (he : e0 < n + m + G.length)
    (dzu : dg n m G zu = 0) (dzv : dg n m G zv = 0) (db : ∀ j, dg n m G (b j) = 0)
    (dc : ∀ j, dg n m G (c j) = 0) (de : dg n m G e0 ≤ 1) :
    ∀ l ≤ m, ∃ (H : List Gate) (e : ℕ),
      St n m (G ++ H) ∧ H.length = 5 * l ∧ cnt n m (G ++ H) ≤ cnt n m G + 2 * l ∧
      e < n + m + (G ++ H).length ∧ dg n m (G ++ H) e ≤ 1 ∧
      ∀ (x : Fin n → Bool) (y : Fin m → Bool),
        val (G ++ H) (xy x y) e =
          (val G (xy x y) e0 || decide (∃ j : Fin m, (j : ℕ) < l ∧
            (y j && ((val G (xy x y) zu || val G (xy x y) (b j)) &&
              (val G (xy x y) zv || val G (xy x y) (c j)))) = true)) := by
  intro l
  induction l with
  | zero =>
    intro _
    refine ⟨[], e0, by simpa using hst, rfl, by simp, by simpa using he, by simpa using de, ?_⟩
    intro x y
    simp
  | succ l ih =>
    intro hl
    obtain ⟨H, e, hst', hlen, hcnt, he', hde, hval⟩ := ih (by omega)
    have hlt : l < m := by omega
    have hGH : (G ++ H).length = G.length + H.length := List.length_append
    obtain ⟨s1, s2, s3, s4⟩ := mux_step n m (G ++ H) hst' zu zv (b ⟨l, hlt⟩) (c ⟨l, hlt⟩) e
      ⟨l, hlt⟩ (by omega) (by omega) (by have := hb ⟨l, hlt⟩; omega)
      (by have := hc ⟨l, hlt⟩; omega) he'
      (by rw [dg_prefix _ _ _ _ _ hzu]; exact dzu) (by rw [dg_prefix _ _ _ _ _ hzv]; exact dzv)
      (by rw [dg_prefix _ _ _ _ _ (hb _)]; exact db _)
      (by rw [dg_prefix _ _ _ _ _ (hc _)]; exact dc _) hde
    refine ⟨H ++ (muxA1 (n + m) (G ++ H).length zu zv (b ⟨l, hlt⟩) (c ⟨l, hlt⟩) ++
      muxA2 (n + m) (G ++ H).length (n + l) e), n + m + ((G ++ H).length + 4), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← List.append_assoc]; exact s1
    · rw [List.length_append, hlen]
      show 5 * l + 5 = 5 * (l + 1)
      omega
    · rw [← List.append_assoc]
      refine le_trans s2 ?_
      omega
    · rw [← List.append_assoc, List.length_append (as := G ++ H)]
      show n + m + ((G ++ H).length + 4) < n + m + ((G ++ H).length + 5)
      omega
    · rw [← List.append_assoc]; exact s3
    · intro x y
      have pv : ∀ i, i < n + m + G.length → val (G ++ H) (xy x y) i = val G (xy x y) i :=
        fun i hi => val_prefix G _ _ i (by rw [xy_length]; exact hi)
      rw [← List.append_assoc, s4 x y, hval x y, pv zu hzu, pv zv hzv, pv _ (hb _), pv _ (hc _),
        ex_succ (fun j : Fin m => (y j && ((val G (xy x y) zu || val G (xy x y) (b j)) &&
              (val G (xy x y) zv || val G (xy x y) (c j))))) l hlt, Bool.or_assoc]

theorem adj' (n m : ℕ) (hadj : ∀ (G : List Gate) (r : ℕ), AdjointSpec n m G r) (G : List Gate)
    (hst : St n m G) (r : ℕ) (hr : r < n + m + G.length) :
    ∃ (A : List Gate) (o : Fin m → ℕ), St n m (G ++ A) ∧ cnt n m (G ++ A) = cnt n m G ∧
      A.length ≤ 3 * cnt n m G + m ∧
      (∀ j : Fin m, o j < n + m + (G ++ A).length ∧ dg n m (G ++ A) (o j) = 0) ∧
      ∀ (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m),
        val G (xy x (fun l => decide (l = j))) r =
          (val G (xy x (fun _ : Fin m => false)) r || val (G ++ A) (xy x y) (o j)) := by
  obtain ⟨hm, hrb, hnc⟩ := hst
  obtain ⟨A, o, h1, h2, h3, h4, h5, h6⟩ := hadj G r hm hrb hnc hr
  obtain ⟨z1, z2, z3, z4⟩ := zero_block n m G A hm hrb hnc h1 h2 h4
  have h3' : A.length ≤
      3 * Set.ncard {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} + m := h3
  have hle := ncard_le_cnt n m G
  refine ⟨A, o, ⟨z1, z2, z3⟩, z4, by omega, ?_, h6⟩
  intro j
  have := h5 j
  refine ⟨?_, this.2⟩
  rw [List.length_append]
  omega

def Wok (n m : ℕ) (C G : List Gate) (w pw : ℕ) : Prop :=
  pw < n + m + G.length ∧ dg n m G pw ≤ dg n m C w ∧
  ∀ x : Fin n → Bool,
    val G (xy x (fun _ : Fin m => false)) pw = val C (xy x (fun _ : Fin m => false)) w ∧
    ∀ j : Fin m, val G (xy x (fun l => decide (l = j))) pw =
      val C (xy x (fun l => decide (l = j))) w

theorem Wok_append (n m : ℕ) (C G : List Gate) (w pw : ℕ) (h : Wok n m C G w pw)
    (B : List Gate) : Wok n m C (G ++ B) w pw := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [List.length_append]; omega, by rw [dg_prefix _ _ _ _ _ h1]; exact h2,
    fun x => ⟨?_, fun j => ?_⟩⟩
  · rw [val_prefix _ _ _ _ (by rw [xy_length]; exact h1)]; exact (h3 x).1
  · rw [val_prefix _ _ _ _ (by rw [xy_length]; exact h1)]; exact (h3 x).2 j

theorem sum_map_le (l : List ℕ) (f f' : ℕ → ℕ) (h : ∀ a ∈ l, f a ≤ f' a) :
    (l.map f).sum ≤ (l.map f').sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem foldr_map_le (l : List ℕ) (f f' : ℕ → ℕ) (h : ∀ a ∈ l, f a ≤ f' a) :
    (l.map f).foldr max 0 ≤ (l.map f').foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (h a List.mem_cons_self) (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

def Inv (n m : ℕ) (C G : List Gate) (p : ℕ → ℕ) (i κ : ℕ) : Prop :=
  St n m G ∧ (∃ A, G = C.map (zc n m) ++ A) ∧ (∀ w < n + m + i, Wok n m C G w (p w)) ∧
  G.length ≤ C.length + i + κ * (6 * (i + κ * (2 * m + 1)) + 7 * m + 2) ∧
  cnt n m G ≤ i + κ * (2 * m + 1)

theorem copy_step (n m : ℕ) (C G : List Gate) (p : ℕ → ℕ) (i κ : ℕ) (hmC : Mono C)
    (hrbC : RB (n + m) C) (hi : i < C.length) (hinv : Inv n m C G p i κ)
    (hnx : (C.getD i dflt).op = GateOp.and → (C.getD i dflt).inputs.length = 2 →
      ∃ a ∈ (C.getD i dflt).inputs, dg n m C a = 0) :
    ∃ (G' : List Gate) (p' : ℕ → ℕ), Inv n m C G' p' (i + 1) κ := by
  obtain ⟨⟨hm, hrb, hnc⟩, ⟨A, hA⟩, hw, hsz, hcn⟩ := hinv
  have hr := hrbC i hi
  obtain ⟨ho, hlen⟩ := opcase C hmC i hi
  have dC := dg_gate n m C i hrbC hi
  have vC : ∀ (x : Fin n → Bool) (y : Fin m → Bool), val C (xy x y) (n + m + i) =
      (C.getD i dflt).op.eval ((C.getD i dflt).inputs.map (val C (xy x y))) :=
    fun x y => val_g C x y i hrbC hi
  generalize C.getD i dflt = g at hr ho hlen hnx dC vC
  have hin : ∀ a ∈ g.inputs, Wok n m C G a (p a) :=
    fun a ha => hw a (by have := hr a ha; omega)
  have hrb' : RB (n + m) (G ++ [Gate.mk g.op (g.inputs.map p)]) := by
    apply RB_append _ _ _ hrb
    intro k hk b hb
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [List.getD_cons_zero, List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have := (hin a ha).1
    omega
  have hm' : Mono (G ++ [Gate.mk g.op (g.inputs.map p)]) := by
    apply Mono_append G _ hm
    intro q hq
    have hq' : q = Gate.mk g.op (g.inputs.map p) := by simpa using hq
    subst hq'
    refine ⟨?_, by simpa using hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ho
  have hnc' : NC n m (G ++ [Gate.mk g.op (g.inputs.map p)]) := by
    apply NC_append n m G _ hrb' hnc
    intro k hk ho' hl'
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [List.getD_cons_zero, List.length_map] at ho' hl' ⊢
    obtain ⟨a, ha, hz⟩ := hnx ho' hl'
    refine ⟨p a, List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [dg_prefix _ _ _ _ _ (hin a ha).1]
    have := (hin a ha).2.1
    omega
  have hnew : Wok n m C (G ++ [Gate.mk g.op (g.inputs.map p)]) (n + m + i)
      (n + m + G.length) := by
    refine ⟨by simp, ?_, fun x => ⟨?_, fun j => ?_⟩⟩
    · rw [dg_new, dC]
      rcases ho with ho | ho
      · rw [lineDegree_and g _ ho, lineDegree_and (Gate.mk g.op (g.inputs.map p)) _ ho]
        show ((g.inputs.map p).map _).sum ≤ _
        rw [List.map_map]
        apply sum_map_le
        intro a ha
        exact (hin a ha).2.1
      · rw [lineDegree_or g _ ho, lineDegree_or (Gate.mk g.op (g.inputs.map p)) _ ho]
        show ((g.inputs.map p).map _).foldr max 0 ≤ _
        rw [List.map_map]
        apply foldr_map_le
        intro a ha
        exact (hin a ha).2.1
    · have e := val_new G (Gate.mk g.op (g.inputs.map p)) (xy x (fun _ : Fin m => false))
      rw [xy_length] at e
      rw [e, vC]
      show g.op.eval ((g.inputs.map p).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ((hin a ha).2.2 x).1
    · have e := val_new G (Gate.mk g.op (g.inputs.map p)) (xy x (fun l => decide (l = j)))
      rw [xy_length] at e
      rw [e, vC]
      show g.op.eval ((g.inputs.map p).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ((hin a ha).2.2 x).2 j
  refine ⟨G ++ [Gate.mk g.op (g.inputs.map p)],
    fun w => if w = n + m + i then n + m + G.length else p w,
    ⟨hm', hrb', hnc'⟩, ⟨A ++ [Gate.mk g.op (g.inputs.map p)], by rw [hA, List.append_assoc]⟩,
    ?_, ?_, ?_⟩
  · intro w hw'
    by_cases hwe : w = n + m + i
    · subst hwe
      simp only [↓reduceIte]
      exact hnew
    · simp only [hwe, ↓reduceIte]
      exact Wok_append n m C G w _ (hw w (by omega)) _
  · simp only [List.length_append, List.length_singleton]
    have : κ * (6 * (i + κ * (2 * m + 1)) + 7 * m + 2) ≤
        κ * (6 * (i + 1 + κ * (2 * m + 1)) + 7 * m + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · have := cnt_snoc_le n m G (Gate.mk g.op (g.inputs.map p))
    omega

theorem add_zero (n m : ℕ) (G : List Gate) (hst : St n m G) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ a ∈ g.inputs, a < n + m + G.length ∧ dg n m G a = 0) :
    St n m (G ++ [g]) ∧ cnt n m (G ++ [g]) = cnt n m G ∧
      dg n m (G ++ [g]) (n + m + G.length) = 0 ∧
      ∀ (x : Fin n → Bool) (y : Fin m → Bool),
        val (G ++ [g]) (xy x y) (n + m + G.length) = g.op.eval (g.inputs.map (val G (xy x y))) := by
  obtain ⟨hm, hrb, hnc⟩ := hst
  have hd : dg n m (G ++ [g]) (n + m + G.length) = 0 := by
    rw [dg_new]
    exact lineDegree_eq_zero _ _ (fun a ha => (hin a ha).2)
  obtain ⟨z1, z2, z3, z4⟩ := zero_block n m G [g] hm hrb hnc
    (by
      intro q hq
      have hq' : q = g := by simpa using hq
      subst hq'
      refine ⟨?_, hlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hop)
    (by
      intro k hk a ha
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      simp only [List.getD_cons_zero] at ha
      have := (hin a ha).1
      omega)
    (by
      intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      exact hd)
  refine ⟨⟨z1, z2, z3⟩, z4, hd, ?_⟩
  intro x y
  have e := val_new G g (xy x y)
  rw [xy_length] at e
  exact e

theorem zf (n m : ℕ) (C G3 : List Gate) (hmC : Mono C) (hrbC : RB (n + m) C) (B : List Gate)
    (hG3 : G3 = C.map (zc n m) ++ B) (Fw : ℕ) (hF1 : Fw < n + m + G3.length)
    (hF2 : dg n m G3 Fw = 0) (hF3 : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val G3 (xy x y) Fw = false) (u : ℕ) (hu : u < n + m + C.length) :
    (if n ≤ u ∧ u < n + m then Fw else u) < n + m + G3.length ∧
    dg n m G3 (if n ≤ u ∧ u < n + m then Fw else u) = 0 ∧
    ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val G3 (xy x y) (if n ≤ u ∧ u < n + m then Fw else u) =
        val C (xy x (fun _ : Fin m => false)) u := by
  split_ifs with h
  · exact ⟨hF1, hF2, fun x y => by rw [hF3, val_y0 C x u h.1 h.2]⟩
  · have hq : u < n ∨ n + m ≤ u := by omega
    subst hG3
    refine ⟨by simp; omega, ?_, fun x y => ?_⟩
    · rw [dg_prefix _ _ _ _ _ (by simp; omega)]
      exact Z_dg n m C hmC hrbC u hq
    · rw [val_prefix _ _ _ _ (by rw [xy_length]; simp; omega)]
      exact Z_val n m C hmC hrbC x y u hq

theorem ex_single {m : ℕ} (P : Fin m → Bool) (l : Fin m) :
    decide (∃ j : Fin m, (decide (j = l) && P j) = true) = P l := by
  rw [Bool.eq_iff_iff]
  simp

theorem cross_step (n m : ℕ) (hadj : ∀ (G : List Gate) (r : ℕ), AdjointSpec n m G r)
    (C G : List Gate) (p : ℕ → ℕ) (i κ : ℕ) (hmC : Mono C)
    (hrbC : RB (n + m) C) (hi : i < C.length) (hinv : Inv n m C G p i κ) (u v : ℕ)
    (hg : C.getD i dflt = Gate.mk GateOp.and [u, v]) (hu : 0 < dg n m C u)
    (hv : 0 < dg n m C v) :
    ∃ (G' : List Gate) (p' : ℕ → ℕ), Inv n m C G' p' (i + 1) (κ + 1) := by
  obtain ⟨hst, ⟨A, hA⟩, hw, hsz, hcn⟩ := hinv
  have hr := hrbC i hi
  rw [hg] at hr
  have hul : u < n + m + i := hr u (by simp)
  have hvl : v < n + m + i := hr v (by simp)
  have wu := hw u hul
  have wv := hw v hvl
  have hold : ∀ (H : List Gate), ∀ w < n + m + i,
      Wok n m C (G ++ H) w (p w) := fun H w hlt => Wok_append n m C G w _ (hw w hlt) H
  -- first adjoint
  obtain ⟨A1, o1, st1, c1, len1, ho1, eq1⟩ := adj' n m hadj G hst (p u) wu.1
  have l1 : (G ++ A1).length = G.length + A1.length := List.length_append
  have pv1 : ∀ (X : List Bool) (a : ℕ), X.length = n + m → a < n + m + G.length →
      val (G ++ A1) X a = val G X a :=
    fun X a hX ha => val_prefix G A1 X a (by rw [hX]; exact ha)
  have hG1 : ∃ B1, G ++ A1 = G ++ B1 := ⟨A1, rfl⟩
  generalize G ++ A1 = G1 at st1 c1 ho1 eq1 l1 pv1 hG1
  -- second adjoint
  obtain ⟨A2, o2, st2, c2, len2, ho2, eq2⟩ :=
    adj' n m hadj G1 st1 (p v) (by have := wv.1; omega)
  have l2 : (G1 ++ A2).length = G1.length + A2.length := List.length_append
  have pv2 : ∀ (X : List Bool) (a : ℕ), X.length = n + m → a < n + m + G1.length →
      val (G1 ++ A2) X a = val G1 X a :=
    fun X a hX ha => val_prefix G1 A2 X a (by rw [hX]; exact ha)
  have pd2 : ∀ a, a < n + m + G1.length → dg n m (G1 ++ A2) a = dg n m G1 a :=
    fun a ha => dg_prefix n m G1 A2 a ha
  have hG2 : ∃ B2, G1 ++ A2 = G ++ B2 := by
    obtain ⟨B1, hB1⟩ := hG1
    exact ⟨B1 ++ A2, by rw [hB1, List.append_assoc]⟩
  generalize G1 ++ A2 = G2 at st2 c2 ho2 eq2 l2 pv2 pd2 hG2
  -- the constant false
  obtain ⟨st3, c3, d3, v3⟩ := add_zero n m G2 st2 (Gate.mk GateOp.or []) (Or.inr rfl)
    (by simp) (by intro a ha; cases ha)
  have l3 : (G2 ++ [Gate.mk GateOp.or []]).length = G2.length + 1 := by simp
  have pv3 : ∀ (X : List Bool) (a : ℕ), X.length = n + m → a < n + m + G2.length →
      val (G2 ++ [Gate.mk GateOp.or []]) X a = val G2 X a :=
    fun X a hX ha => val_prefix G2 _ X a (by rw [hX]; exact ha)
  have pd3 : ∀ a, a < n + m + G2.length →
      dg n m (G2 ++ [Gate.mk GateOp.or []]) a = dg n m G2 a :=
    fun a ha => dg_prefix n m G2 _ a ha
  have hG3 : ∃ B3, G2 ++ [Gate.mk GateOp.or []] = G ++ B3 := by
    obtain ⟨B2, hB2⟩ := hG2
    exact ⟨B2 ++ [Gate.mk GateOp.or []], by rw [hB2, List.append_assoc]⟩
  have v3' : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val (G2 ++ [Gate.mk GateOp.or []]) (xy x y) (n + m + G2.length) = false := by
    intro x y
    rw [v3]
    simp [GateOp.eval]
  generalize G2 ++ [Gate.mk GateOp.or []] = G3 at st3 c3 d3 l3 pv3 pd3 hG3 v3'
  have hG3Z : ∃ B, G3 = C.map (zc n m) ++ B := by
    obtain ⟨B3, hB3⟩ := hG3
    exact ⟨A ++ B3, by rw [hB3, hA, List.append_assoc]⟩
  obtain ⟨BZ, hBZ⟩ := hG3Z
  obtain ⟨zu1, zu2, zu3⟩ := zf n m C G3 hmC hrbC BZ hBZ (n + m + G2.length) (by omega) d3 v3'
    u (by omega)
  obtain ⟨zv1, zv2, zv3⟩ := zf n m C G3 hmC hrbC BZ hBZ (n + m + G2.length) (by omega) d3 v3'
    v (by omega)
  generalize (if n ≤ u ∧ u < n + m then n + m + G2.length else u) = zu at zu1 zu2 zu3
  generalize (if n ≤ v ∧ v < n + m then n + m + G2.length else v) = zv at zv1 zv2 zv3
  -- the gate zu AND zv
  obtain ⟨st4, c4, d4, v4⟩ := add_zero n m G3 st3 (Gate.mk GateOp.and [zu, zv]) (Or.inl rfl)
    (by simp) (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨zu1, zu2⟩
      · exact ⟨zv1, zv2⟩)
  have l4 : (G3 ++ [Gate.mk GateOp.and [zu, zv]]).length = G3.length + 1 := by simp
  have pv4 : ∀ (X : List Bool) (a : ℕ), X.length = n + m → a < n + m + G3.length →
      val (G3 ++ [Gate.mk GateOp.and [zu, zv]]) X a = val G3 X a :=
    fun X a hX ha => val_prefix G3 _ X a (by rw [hX]; exact ha)
  have pd4 : ∀ a, a < n + m + G3.length →
      dg n m (G3 ++ [Gate.mk GateOp.and [zu, zv]]) a = dg n m G3 a :=
    fun a ha => dg_prefix n m G3 _ a ha
  have hG4 : ∃ B4, G3 ++ [Gate.mk GateOp.and [zu, zv]] = G ++ B4 := by
    obtain ⟨B3, hB3⟩ := hG3
    exact ⟨B3 ++ [Gate.mk GateOp.and [zu, zv]], by rw [hB3, List.append_assoc]⟩
  have v4' : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val (G3 ++ [Gate.mk GateOp.and [zu, zv]]) (xy x y) (n + m + G3.length) =
        (val C (xy x (fun _ : Fin m => false)) u && val C (xy x (fun _ : Fin m => false)) v) := by
    intro x y
    rw [v4]
    simp [GateOp.eval, zu3, zv3]
  generalize G3 ++ [Gate.mk GateOp.and [zu, zv]] = G4 at st4 c4 d4 l4 pv4 pd4 hG4 v4'
  have hzu4 : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val G4 (xy x y) zu = val C (xy x (fun _ : Fin m => false)) u := by
    intro x y
    rw [pv4 _ _ (xy_length x y) zu1, zu3]
  have hzv4 : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val G4 (xy x y) zv = val C (xy x (fun _ : Fin m => false)) v := by
    intro x y
    rw [pv4 _ _ (xy_length x y) zv1, zv3]
  have hU : ∀ (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m),
      (val C (xy x (fun _ : Fin m => false)) u || val G4 (xy x y) (o1 j)) =
        val C (xy x (fun l => decide (l = j))) u := by
    intro x y j
    have hb := (ho1 j).1
    rw [pv4 _ _ (xy_length x y) (by omega), pv3 _ _ (xy_length x y) (by omega),
      pv2 _ _ (xy_length x y) hb, ← (wu.2.2 x).1, ← (wu.2.2 x).2 j]
    exact (eq1 x y j).symm
  have hV : ∀ (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m),
      (val C (xy x (fun _ : Fin m => false)) v || val G4 (xy x y) (o2 j)) =
        val C (xy x (fun l => decide (l = j))) v := by
    intro x y j
    have hb := (ho2 j).1
    have e2 := eq2 x y j
    rw [pv1 _ _ (xy_length x _) wv.1, pv1 _ _ (xy_length x _) wv.1, (wv.2.2 x).1,
      (wv.2.2 x).2 j] at e2
    rw [pv4 _ _ (xy_length x y) (by omega), pv3 _ _ (xy_length x y) hb]
    exact e2.symm
  -- the multiplexer
  obtain ⟨H, e, st5, lenH, c5, he, hde, hval⟩ := mux_loop n m G4 st4 zu zv (n + m + G3.length)
    o1 o2 (by omega) (by omega) (fun j => by have := (ho1 j).1; omega)
    (fun j => by have := (ho2 j).1; omega) (by omega)
    (by rw [pd4 _ zu1]; exact zu2) (by rw [pd4 _ zv1]; exact zv2)
    (fun j => by
      have hb := (ho1 j).1
      rw [pd4 _ (by omega), pd3 _ (by omega), pd2 _ hb]
      exact (ho1 j).2)
    (fun j => by
      have hb := (ho2 j).1
      rw [pd4 _ (by omega), pd3 _ hb]
      exact (ho2 j).2)
    (by omega) m (le_refl m)
  have key : ∀ (x : Fin n → Bool) (y : Fin m → Bool), val (G4 ++ H) (xy x y) e =
      ((val C (xy x (fun _ : Fin m => false)) u && val C (xy x (fun _ : Fin m => false)) v) ||
        decide (∃ j : Fin m, (y j && (val C (xy x (fun l => decide (l = j))) u &&
          val C (xy x (fun l => decide (l = j))) v)) = true)) := by
    intro x y
    rw [hval x y, v4']
    simp only [hzu4, hzv4, hU, hV, Fin.is_lt, true_and]
  have dCi := dg_and2 n m C i u v hrbC hi hg
  have hnew : Wok n m C (G4 ++ H) (n + m + i) e := by
    refine ⟨he, by omega, fun x => ⟨?_, fun l => ?_⟩⟩
    · rw [key, val_and2 C x _ i u v hrbC hi hg]
      simp
    · rw [key, val_and2 C x _ i u v hrbC hi hg, ex_single]
      have h1 := hU x (fun _ => false) l
      have h2 := hV x (fun _ => false) l
      rw [← h1, ← h2]
      generalize val C (xy x (fun _ : Fin m => false)) u = a
      generalize val C (xy x (fun _ : Fin m => false)) v = b
      generalize val G4 (xy x (fun _ : Fin m => false)) (o1 l) = c
      generalize val G4 (xy x (fun _ : Fin m => false)) (o2 l) = d
      cases a <;> cases b <;> cases c <;> cases d <;> rfl
  obtain ⟨B4, hB4⟩ := hG4
  have e1 : (κ + 1) * (2 * m + 1) = κ * (2 * m + 1) + (2 * m + 1) := by ring
  refine ⟨G4 ++ H, fun w => if w = n + m + i then e else p w, st5,
    ⟨A ++ B4 ++ H, by rw [hB4, hA]; simp [List.append_assoc]⟩, ?_, ?_, ?_⟩
  · intro w hw'
    by_cases hwe : w = n + m + i
    · subst hwe
      simp only [↓reduceIte]
      exact hnew
    · simp only [hwe, ↓reduceIte]
      rw [hB4, List.append_assoc]
      exact hold _ w (by omega)
  · rw [List.length_append, lenH]
    have e3 : κ * (6 * (i + κ * (2 * m + 1)) + 7 * m + 2) ≤
        κ * (6 * (i + 1 + (κ * (2 * m + 1) + (2 * m + 1))) + 7 * m + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : (κ + 1) * (6 * (i + 1 + (κ * (2 * m + 1) + (2 * m + 1))) + 7 * m + 2) =
        κ * (6 * (i + 1 + (κ * (2 * m + 1) + (2 * m + 1))) + 7 * m + 2) +
          (6 * (i + 1 + (κ * (2 * m + 1) + (2 * m + 1))) + 7 * m + 2) := by ring
    rw [e1, e2]
    omega
  · rw [e1]
    omega

def crossB (n m : ℕ) (C : List Gate) (j : ℕ) : Bool :=
  match (C.getD j dflt).op, (C.getD j dflt).inputs with
  | GateOp.and, [a, b] => decide (0 < dg n m C a) && decide (0 < dg n m C b)
  | _, _ => false

theorem crossB_true (n m : ℕ) (C : List Gate) (j : ℕ) (h : crossB n m C j = true) :
    ∃ u v, C.getD j dflt = Gate.mk GateOp.and [u, v] ∧ 0 < dg n m C u ∧ 0 < dg n m C v := by
  unfold crossB at h
  split at h
  · rename_i a b h1 h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨a, b, ?_, h.1, h.2⟩
    cases hgd : C.getD j dflt with
    | mk op inp =>
      rw [hgd] at h1 h2
      simp only at h1 h2
      rw [h1, h2]
  · simp at h

theorem crossB_false (n m : ℕ) (C : List Gate) (j : ℕ) (h : crossB n m C j = false)
    (ho : (C.getD j dflt).op = GateOp.and) (hl : (C.getD j dflt).inputs.length = 2) :
    ∃ a ∈ (C.getD j dflt).inputs, dg n m C a = 0 := by
  rcases shape _ (le_of_eq hl) with hs | ⟨a, hs⟩ | ⟨a, b, hs⟩
  · rw [hs] at hl; simp at hl
  · rw [hs] at hl; simp at hl
  · unfold crossB at h
    rw [ho, hs] at h
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt, Nat.le_zero] at h
    rw [hs]
    rcases h with h | h
    · exact ⟨a, by simp, h⟩
    · exact ⟨b, by simp, h⟩

def kap (n m : ℕ) (C : List Gate) (i : ℕ) : ℕ :=
  ((Finset.range i).filter (fun j => crossB n m C j = true)).card

theorem kap_succ (n m : ℕ) (C : List Gate) (i : ℕ) :
    kap n m C (i + 1) = kap n m C i + (if crossB n m C i = true then 1 else 0) := by
  unfold kap
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem kap_le (n m : ℕ) (C : List Gate) :
    kap n m C C.length ≤ Set.ncard {j : ℕ | j < C.length ∧
      (C.getD j dflt).op = GateOp.and ∧ (C.getD j dflt).inputs.length = 2 ∧
      ∀ i ∈ (C.getD j dflt).inputs, 0 < dg n m C i} := by
  unfold kap
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj
    obtain ⟨u, v, hg, hu, hv⟩ := crossB_true n m C j hj.2
    refine ⟨hj.1, ?_, ?_, ?_⟩
    · rw [hg]
    · rw [hg]; rfl
    · rw [hg]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv
  · exact (Set.finite_Iio C.length).subset (fun j hj => hj.1)

theorem cnt_nil (n m : ℕ) : cnt n m [] = 0 := by
  unfold cnt
  rw [List.drop_eq_nil_of_le (by rw [Dg_length, d0_length]; simp)]
  rfl

theorem main_ind (n m : ℕ) (hadj : ∀ (G : List Gate) (r : ℕ), AdjointSpec n m G r)
    (C : List Gate) (hmC : Mono C) (hrbC : RB (n + m) C) :
    ∀ i ≤ C.length, ∃ (G : List Gate) (p : ℕ → ℕ), Inv n m C G p i (kap n m C i) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hZrb := Z_rb n m C hmC hrbC
    have hZd := Z_dg n m C hmC hrbC
    refine ⟨C.map (zc n m), fun w => w, ⟨Z_mono n m C hmC, hZrb, ?_⟩, ⟨[], by simp⟩, ?_, ?_, ?_⟩
    · intro j hj ho hl
      have hj' : j < C.length := by simpa using hj
      rcases shape _ (le_of_eq hl) with hs | ⟨a, hs⟩ | ⟨a, b, hs⟩
      · rw [hs] at hl; simp at hl
      · rw [hs] at hl; simp at hl
      · have hin := Z_in n m C hmC j hj' a (by rw [hs]; exact List.mem_cons_self)
        exact ⟨a, by rw [hs]; exact List.mem_cons_self, hZd a hin.2⟩
    · intro w hw
      refine ⟨by show w < _; omega, ?_, fun x => ⟨?_, fun j => ?_⟩⟩
      · rw [dg_input _ _ _ _ (by omega), dg_input _ _ _ _ (by omega)]
      · rw [val_input _ _ _ (by rw [xy_length]; omega), val_input _ _ _ (by rw [xy_length]; omega)]
      · rw [val_input _ _ _ (by rw [xy_length]; omega), val_input _ _ _ (by rw [xy_length]; omega)]
    · simp
    · have h0 := cnt_append_zero n m [] (C.map (zc n m)) (by
        intro k hk
        exact hZd _ (by simp))
      simp only [List.nil_append] at h0
      rw [h0, cnt_nil]
      omega
  | succ i ih =>
    intro hi
    obtain ⟨G, p, hinv⟩ := ih (by omega)
    rw [kap_succ]
    cases hc : crossB n m C i
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact copy_step n m C G p i _ hmC hrbC (by omega) hinv (crossB_false n m C i hc)
    · simp only [↓reduceIte]
      obtain ⟨u, v, hg, hu, hv⟩ := crossB_true n m C i hc
      exact cross_step n m hadj C G p i _ hmC hrbC (by omega) hinv u v hg hu hv

theorem main (hadj : ∀ (n m : ℕ) (G : List Gate) (r : ℕ), AdjointSpec n m G r) :
    (∀ (n m s k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + k * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true))) := by
  intro n m s k C hM hR hs hk
  obtain ⟨G, p, hinv⟩ := main_ind n m (hadj n m) C.gates hM hR C.gates.length le_rfl
  obtain ⟨⟨hm, hrb, hnc⟩, _, hw, hsz, hcn⟩ := hinv
  have hκ : kap n m C.gates C.gates.length ≤ k := le_trans (kap_le n m C.gates) hk
  generalize kap n m C.gates C.gates.length = κ at hsz hcn hκ
  have hs' : C.gates.length ≤ s := hs
  refine ⟨Circuit.mk G (if C.output < n + m + C.gates.length then p C.output
    else n + m + G.length), hm, hrb, hnc, ?_, ?_, ?_⟩
  · show G.length ≤ _
    have h1 : κ * (6 * (C.gates.length + κ * (2 * m + 1)) + 7 * m + 2) ≤
        k * (6 * (s + k * (2 * m + 1)) + 7 * m + 2) :=
      Nat.mul_le_mul hκ (by have := Nat.mul_le_mul_right (2 * m + 1) hκ; omega)
    have h2 : k * (6 * (s + k * (2 * m + 1)) + 7 * m + 2) + 3 * s =
        (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k := by ring
    omega
  · have h1 := ncard_le_cnt n m G
    have h2 := Nat.mul_le_mul_right (2 * m + 1) hκ
    exact le_trans h1 (by omega)
  · intro x Y
    show val G (xy x (fun l => decide (l ∈ Y))) _ =
      (val C.gates (xy x (fun _ : Fin m => false)) C.output ||
        decide (∃ j ∈ Y, val C.gates (xy x (fun l => decide (l = j))) C.output = true))
    rw [linear n m G hm hrb hnc x Y]
    split_ifs with h
    · have hwo := (hw _ h).2.2 x
      simp only [hwo.1, hwo.2]
    · have e1 : ∀ y : Fin m → Bool, val G (xy x y) (n + m + G.length) = false :=
        fun y => val_out _ _ _ (by rw [xy_length])
      have e2 : ∀ y : Fin m → Bool, val C.gates (xy x y) C.output = false :=
        fun y => val_out _ _ _ (by rw [xy_length]; omega)
      simp only [e1, e2]

end P1623

theorem P1623_main : ∀ (n m s k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + k * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true)) :=
  PEqualNP.Outside.L_meta_1625.P1623.main
    (fun n m G r => PEqualNP.Outside.L_meta_1625.P1623.aj_adjoint n m G r)

end Sec1623

section Sec1624

open PEqualNP.CircuitLowerBounds

namespace P1624

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

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

def Sv {n : ℕ} {ι : Type*} (C : Circuit) (l : ι → Fin n → Bool) (y : Fin n → Bool)
    (p : ι) (w : ℕ) : Prop :=
  value C (l p) w = true ∧ value C y w = false

def Multi {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Sv C l y p w ∧ Sv C l y p' w

lemma list_cases (L : List ℕ) (hL : L.length ≤ 2) (Q : ℕ → Prop) :
    (L.length = 2 ∧ ∀ r ∈ L, Q r) ∨ ∃ c, ∀ r ∈ L, Q r → r = c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · exact Or.inr ⟨0, fun r hr => absurd hr (by simp)⟩
  · exact Or.inr ⟨a, fun r hr _ => by simpa using hr⟩
  · by_cases ha : Q a
    · by_cases hb : Q b
      · refine Or.inl ⟨rfl, fun r hr => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · exact ha
        · exact hb
      · refine Or.inr ⟨a, fun r hr hq => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · rfl
        · exact absurd hq hb
    · refine Or.inr ⟨b, fun r hr hq => ?_⟩
      rcases List.mem_pair.mp hr with rfl | rfl
      · exact absurd hq ha
      · rfl
  · simp at hL

lemma step_cases {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < C.gates.length) (hm : Multi C T l y (n + k)) :
    (∃ r ∈ C.gates[k].inputs, r < n + k ∧ ∀ p ∈ T, Sv C l y p (n + k) → Sv C l y p r) ∨
    (C.gates[k].op = GateOp.or ∧ C.gates[k].inputs.length = 2 ∧
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) ∧
      ∀ p ∈ T, Sv C l y p (n + k) → ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Sv C l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
  · left
    have hy := hs0.2
    by_contra hcon
    have hall : ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C y r = true := by
      intro r hr
      by_contra hr2
      apply hcon
      have hlt := ((and_value C k hk hop (l p0)).mp hs0.1 r hr).1
      refine ⟨r, hr, hlt, fun p _ hsp => ⟨((and_value C k hk hop (l p)).mp hsp.1 r hr).2, ?_⟩⟩
      by_contra hne
      exact hr2 ⟨hlt, by simpa using hne⟩
    rw [(and_value C k hk hop y).mpr hall] at hy
    exact Bool.noConfusion hy
  · have hyall : ∀ r ∈ C.gates[k].inputs, r < n + k → value C y r = false := by
      intro r hr hlt
      by_contra h
      have h2 : value C y (n + k) = true :=
        (or_value C k hk hop y).mpr ⟨r, hr, hlt, by simpa using h⟩
      rw [hs0.2] at h2
      exact Bool.noConfusion h2
    have hsv : ∀ p ∈ T, Sv C l y p (n + k) →
        ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C (l p) r = true ∧ Sv C l y p r := by
      intro p _ hsp
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C k hk hop (l p)).mp hsp.1
      exact ⟨r, hr, hlt, hv, hv, hyall r hr hlt⟩
    rcases list_cases C.gates[k].inputs (hC _ (List.getElem_mem hk)).2
      (fun r => ∃ p ∈ T, r < n + k ∧ value C (l p) r = true) with ⟨hlen, hQ⟩ | ⟨c, hc⟩
    · right
      refine ⟨hop, hlen, fun r hr => ?_, fun p hp hsp => ?_⟩
      · obtain ⟨p, hp, _, hv⟩ := hQ r hr
        exact ⟨p, hp, hv⟩
      · obtain ⟨r, hr, hlt, _, hs⟩ := hsv p hp hsp
        exact ⟨r, hr, hlt, hs⟩
    · left
      obtain ⟨r, hr, hlt, hv, _⟩ := hsv p0 hp0 hs0
      have hrc := hc r hr ⟨p0, hp0, hlt, hv⟩
      refine ⟨r, hr, hlt, fun p hp hsp => ?_⟩
      obtain ⟨r', hr', hlt', hv', hs'⟩ := hsv p hp hsp
      have hrc' := hc r' hr' ⟨p, hp, hlt', hv'⟩
      rw [hrc, ← hrc']
      exact hs'

lemma frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < C.gates.length, Multi C T l y (n + k) →
      C.gates[k].op = GateOp.or → C.gates[k].inputs.length = 2 →
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) → n + k ∈ W)
    (hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, Multi C T l y w → w < t)
    (T' : Finset ι) (hT' : T' ⊆ T) (hs : ∀ p ∈ T', ∃ w ∈ F, Sv C l y p w) :
    T'.card ≤ F.card + (W.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T' := by
      intro p hp p' hp' e
      by_contra hne
      have hc : Multi C T l y (f p) :=
        ⟨p, hT' hp, p', hT' hp', hne, hfs p hp, by rw [e]; exact hfs p' hp'⟩
      have := hF (f p) (hfF p hp) hc
      omega
    have := Finset.card_le_card_of_injOn f (fun p hp => hfF p hp) hinj
    omega
  | succ t ih =>
    have hle : (W.filter (· < t)).card ≤ (W.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ Multi C T l y t
    · obtain ⟨h1, h2⟩ := hlen t hex.2
      have hk : t - n < C.gates.length := by omega
      have htk : t = n + (t - n) := by omega
      have hm : Multi C T l y (n + (t - n)) := by rw [← htk]; exact hex.2
      have he := Finset.card_erase_add_one hex.1
      rcases step_cases C T l y hC (t - n) hk hm with ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
      · rw [← htk] at hlt hall
        let F' := insert r (F.erase t)
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with hw | hw
          · rw [hw]; exact hlt
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsv⟩ := hs p hp
          by_cases h : w = t
          · subst h
            exact ⟨r, Finset.mem_insert_self _ _, hall p (hT' hp) hsv⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_insert_le r (F.erase t)
        change F'.card ≤ _ at hu
        omega
      · rw [← htk] at hsv
        have htW : t ∈ W := by
          have := hW (t - n) hk hm hop hlen2 hQ
          rwa [← htk] at this
        let P : Finset ℕ := (C.gates[t - n].inputs.filter (· < t)).toFinset
        have hPcard : P.card ≤ 2 := by
          have h1 := List.toFinset_card_le (C.gates[t - n].inputs.filter (· < t))
          have h2 := List.length_filter_le (fun r => decide (r < t)) C.gates[t - n].inputs
          change P.card ≤ _ at h1
          omega
        let F' := F.erase t ∪ P
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsvp⟩ := hs p hp
          by_cases h : w = t
          · subst h
            obtain ⟨r, hr, hlt, hsr⟩ := hsv p (hT' hp) hsvp
            exact ⟨r, Finset.mem_union_right _ (List.mem_toFinset.mpr
              (List.mem_filter.mpr ⟨hr, by simpa using hlt⟩)), hsr⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hsvp⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_union_le (F.erase t) P
        change F'.card ≤ _ at hu
        have hfilter : W.filter (· < t + 1) = insert t (W.filter (· < t)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hlt⟩
            by_cases h : w = t
            · exact Or.inl h
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, hlt⟩)
            · exact ⟨htW, by omega⟩
            · exact ⟨hg, by omega⟩
        rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
    · have hF' : ∀ w ∈ F, Multi C T l y w → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      have := ih F hF' hs
      omega

lemma family {n : ℕ} {ι : Type*} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset ι) (l : ι → Fin n → Bool) (y : Fin n → Bool) (o : ℕ)
    (ho : ∀ p ∈ T, Sv C l y p o)
    (hin : ∀ w, w < n → ¬ Multi C T l y w)
    (K : Finset (Fin C.gates.length))
    (hK : ∀ g : Fin C.gates.length, Multi C T l y (n + (g : ℕ)) → g ∈ K) :
    T.card ≤ K.card + 1 := by
  classical
  let W : Finset ℕ := Finset.image (fun g : Fin C.gates.length => n + (g : ℕ)) K
  have hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length := by
    intro w hc
    refine ⟨Nat.le_of_not_lt fun h => hin w h hc, ?_⟩
    by_contra hge
    obtain ⟨p, _, _, _, _, hsv, _⟩ := hc
    have hm := missing_value C (l p) w (by unfold Circuit.size; omega)
    have h1 := hsv.1
    rw [hm] at h1
    exact Bool.noConfusion h1
  have h := frontier C T l y hC W
    (fun k hk hm _ _ _ => Finset.mem_image.mpr ⟨(⟨k, hk⟩ : Fin C.gates.length), hK ⟨k, hk⟩ hm, rfl⟩)
    hlen (n + C.gates.length) {o}
    (fun w _ hc => (hlen w hc).2) T (Finset.Subset.refl T)
    (fun p hp => ⟨o, Finset.mem_singleton_self o, ho p hp⟩)
  have h1 := Finset.card_filter_le W (· < n + C.gates.length)
  have h2 : W.card ≤ K.card := Finset.card_image_le
  rw [Finset.card_singleton] at h
  omega

lemma main : ∀ (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack n D → (∀ j : Fin m, A j ⊆ L j) → (∀ (j : Fin m) (p : Fin n), p ∈ A j → (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true) → (∀ j : Fin m, (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) → ∑ j : Fin m, ((A j).card - 1) ≤ D.size := by
  classical
  intro n m L A D o hint hmono _ hAL htrue hfalse
  have hC : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hmono g hg
    refine ⟨?_, h.2⟩
    rcases h.1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  let l : Fin n → Fin n → Bool := fun p i => decide (i = p)
  let y : Fin m → Fin n → Bool := fun j i => decide (i ∉ L j)
  let K : Fin m → Finset (Fin D.gates.length) := fun j =>
    Finset.univ.filter fun g => Multi D (A j) l (y j) (n + (g : ℕ))
  have hK : ∀ j, (A j).card ≤ (K j).card + 1 := by
    intro j
    refine family D hC (A j) l (y j) (o j) (fun p hp => ⟨htrue j p hp, hfalse j⟩) ?_ (K j)
      (fun g hm => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hm⟩)
    rintro w hw ⟨p, _, p', _, hne, hs1, hs2⟩
    have e1 : l p ⟨w, hw⟩ = true := (input_value D (l p) ⟨w, hw⟩).symm.trans hs1.1
    have e2 : l p' ⟨w, hw⟩ = true := (input_value D (l p') ⟨w, hw⟩).symm.trans hs2.1
    exact hne ((of_decide_eq_true e1).symm.trans (of_decide_eq_true e2))
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (K i) (K j) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
    obtain ⟨a, ha, b, hb, hab, hsa, hsb⟩ := (Finset.mem_filter.mp hgi).2
    obtain ⟨c, _, _, _, _, hsc, _⟩ := (Finset.mem_filter.mp hgj).2
    have hyj : value D (y j) (n + (g : ℕ)) = false := hsc.2
    have key : ∀ p : Fin n, value D (l p) (n + (g : ℕ)) = true → p ∈ L j := by
      intro p hv
      by_contra hn
      have h2 := mono D hC (l p) (y j) (fun v hv' => by
        have hvp : v = p := of_decide_eq_true hv'
        rw [hvp]
        exact decide_eq_true hn) _ hv
      exact Bool.noConfusion (hyj.symm.trans h2)
    exact hab (Finset.card_le_one.mp (hint i j hij) a
      (Finset.mem_inter.mpr ⟨hAL i ha, key a hsa.1⟩) b
      (Finset.mem_inter.mpr ⟨hAL i hb, key b hsb.1⟩))
  have h1 : ∑ j : Fin m, ((A j).card - 1) ≤ ∑ j : Fin m, (K j).card :=
    Finset.sum_le_sum fun j _ => by
      have := hK j
      omega
  rw [← Finset.card_biUnion hd] at h1
  have h2 := Finset.card_le_univ (Finset.univ.biUnion K)
  rw [Fintype.card_fin] at h2
  exact h1.trans h2

end P1624

theorem P1624_main : ∀ (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack n D → (∀ j : Fin m, A j ⊆ L j) → (∀ (j : Fin m) (p : Fin n), p ∈ A j → (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true) → (∀ j : Fin m, (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) → ∑ j : Fin m, ((A j).card - 1) ≤ D.size :=
  PEqualNP.Outside.L_meta_1625.P1624.main

end Sec1624

theorem glue (h22 : (∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧ ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || (D.wires (List.ofFn x)).getD (o j) false))) (h23 : (∀ (n m s k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + k * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true)))) (h24 : (∀ (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack n D → (∀ j : Fin m, A j ⊆ L j) → (∀ (j : Fin m) (p : Fin n), p ∈ A j → (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true) → (∀ j : Fin m, (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) → ∑ j : Fin m, ((A j).card - 1) ≤ D.size)) : (∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k) := by
  intro n m s k L C hL hmono hrb hs hk hsound
  obtain ⟨M, hMm, hMrb, hMx, hMs, hMt, hMf⟩ := h23 n m s k C hmono hrb hs hk
  obtain ⟨D, o, hDm, hDrb, hDs, hDf⟩ := h22 n m M hMm hMrb hMx
  have hC0 : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append x (fun _ => false)) = false := by
    intro x
    by_contra hne
    have h1 := hsound x ∅ (by simp) (by simpa using hne)
    obtain ⟨j, hj, _⟩ := h1
    simp at hj
  have hM1 : ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) M
      (Fin.append x (fun l => decide (l = j))) = PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append x (fun l => decide (l = j))) := by
    intro x j
    have h1 := hMf x {j}
    simp only [Finset.mem_singleton, exists_eq_left] at h1
    rw [h1, hC0]
    simp
  have hM0 : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) M
      (Fin.append x (fun _ => false)) = false := by
    intro x
    have h1 := hMf x ∅
    simp only [Finset.notMem_empty, decide_false, false_and, exists_false, Bool.or_false] at h1
    rw [h1, hC0]
  have hD : ∀ (x : Fin n → Bool) (j : Fin m), (D.wires (List.ofFn x)).getD (o j) false =
      PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) := by
    intro x j
    have h1 := hDf x j
    rw [hM1, hM0, Bool.false_or] at h1
    exact h1.symm
  have h := h24 n m L (fun j => (L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)) D o hL hDm hDrb
    (fun j => Finset.filter_subset _ _)
    (by
      intro j p hp
      rw [hD]
      exact (Finset.mem_filter.mp hp).2)
    (by
      intro j
      rw [hD]
      by_contra hne
      have h1 := hsound (fun i : Fin n => decide (i ∉ L j)) {j} (by simp)
        (by
          have h2 : (fun l : Fin m => decide (l ∈ ({j} : Finset (Fin m)))) = fun l => decide (l = j) := by
            funext l
            simp
          rw [h2]
          simpa using hne)
      obtain ⟨j', hj', p, hp, hx⟩ := h1
      rw [Finset.mem_singleton] at hj'
      subst hj'
      simp [hp] at hx)
  have hcard : (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧
      PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1))
        (fun l => decide (l = e.2))) = true)).card ≤
      ∑ j : Fin m, ((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun e => ⟨e.2, e.1⟩) ?_ ?_
    · intro e he
      have he' := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
      exact Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr he'⟩)
    · intro a _ b _ hab
      simp only [Sigma.mk.injEq, heq_eq_eq] at hab
      exact Prod.ext hab.2 hab.1
  have hsum : ∑ j : Fin m, ((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card ≤
      ∑ j : Fin m, (((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card - 1) + m := by
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin m)), ((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card ≤
      (((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card - 1) + 1 := by
      intro j _
      omega
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib] at h2
    simpa using h2
  have hDs' : D.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k +
      3 * (s + k * (2 * m + 1)) + m := by
    have h3 := Nat.mul_le_mul_left 3 hMt
    omega
  have hfin : (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k +
      3 * (s + k * (2 * m + 1)) + m + m = (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
    ring
  omega

end PEqualNP.Outside.L_meta_1625

theorem PEqualNP.Outside.L_meta_1625 : ∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k :=
  PEqualNP.Outside.L_meta_1625.glue PEqualNP.Outside.L_meta_1625.P1622_main PEqualNP.Outside.L_meta_1625.P1623_main PEqualNP.Outside.L_meta_1625.P1624_main
