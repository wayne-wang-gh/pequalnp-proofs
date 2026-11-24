import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1713

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem difp {α : Type} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬ c → α} :
    dite c a b = a h := by simp [h]

theorem difn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a : c → α} {b : ¬ c → α} :
    dite c a b = b h := by simp [h]

def fd {α : Type} (F : Gate → List α → α) (X : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [F g w]) X

theorem fd_len {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α), (fd F X gs).length = X.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro X; simp [fd]
  | cons g gs ih =>
    intro X
    have := ih (X ++ [F g X])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp
    omega

theorem fd_pre {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α) (i : ℕ), i < X.length → (fd F X gs)[i]? = X[i]? := by
  intro gs
  induction gs with
  | nil => intro X i _; simp [fd]
  | cons g gs ih =>
    intro X i hi
    have := ih (X ++ [F g X]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this, List.getElem?_append_left hi]

theorem fd_app {α : Type} (F : Gate → List α → α) (X : List α) (gs hs : List Gate) :
    fd F X (gs ++ hs) = fd F (fd F X gs) hs := by
  simp [fd, List.foldl_append]

theorem fd_gate' {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (as : List Gate) (g : Gate) (bs : List Gate) (X : List α)
    (hrb : ∀ i ∈ g.inputs, i < X.length + as.length) :
    (fd F X (as ++ g :: bs)).getD (X.length + as.length) dflt = F g (fd F X (as ++ g :: bs)) := by
  have e1 : fd F X (as ++ g :: bs) = fd F (fd F X as ++ [F g (fd F X as)]) bs := by
    simp [fd, List.foldl_append]
  have hWl : (fd F X as).length = X.length + as.length := fd_len F as X
  have key : ∀ i, i < (fd F X as).length + 1 →
      (fd F X (as ++ g :: bs))[i]? = (fd F X as ++ [F g (fd F X as)])[i]? := by
    intro i hi
    rw [e1]
    exact fd_pre F bs _ i (by simp; omega)
  rw [List.getD_eq_getElem?_getD, key _ (by omega), ← hWl,
    List.getElem?_append_right (le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  apply hF
  intro i hi
  have hi' := hrb i hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, key i (by omega),
    List.getElem?_append_left (by omega)]

theorem fd_gate {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (gs : List Gate) (X : List α) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < X.length + j) :
    (fd F X gs).getD (X.length + j) dflt = F (gs.getD j ⟨GateOp.or, []⟩) (fd F X gs) := by
  have h1 : gs.take j ++ gs[j] :: gs.drop (j + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hj]
    exact List.take_append_drop j gs
  have h2 : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := by
    simp [List.getD_eq_getElem?_getD, hj]
  have h3 := fd_gate' F dflt hF (gs.take j) gs[j] (gs.drop (j + 1)) X (by
    rw [List.length_take, min_eq_left hj.le, ← h2]
    exact hrb)
  rw [h1, List.length_take, min_eq_left hj.le] at h3
  rw [h2]
  exact h3

def stpF : Gate → List Bool → Bool :=
  fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

theorem stpF_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : stpF g w = stpF g w' := by
  unfold stpF
  rw [List.map_congr_left h]

theorem ld_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : g.lineDegree w = g.lineDegree w' := by
  unfold Gate.lineDegree
  rw [List.map_congr_left h]

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ifn (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ifn (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (fd stpF W1 gs).getD i false = true → (fd stpF W2 gs).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa [fd] using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    have := ih (W1 ++ [stpF g W1]) (W2 ++ [stpF g W2]) (by simp [hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) (by
        intro i
        simp only [getD_snoc, hl]
        split_ifs
        · unfold stpF
          rcases hop g List.mem_cons_self with ha | ho
          · rw [ev_and g _ ha, ev_and g _ ha]
            intro h k hk
            exact H k (h k hk)
          · rw [ev_or g _ ho, ev_or g _ ho]
            rintro ⟨k, hk, h⟩
            exact ⟨k, hk, H k h⟩
        · exact H i)
    simpa only [fd, List.foldl_cons] using this

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem app_getD {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ) :
    (List.ofFn (Fin.append x y)).getD i false =
      if h : i < n then x ⟨i, h⟩ else if h2 : i - n < m then y ⟨i - n, h2⟩ else false := by
  rw [ofFn_getD]
  by_cases h : i < n
  · rw [difp (by omega), difp h]
    exact Fin.append_left x y ⟨i, h⟩
  · rw [difn h]
    by_cases h2 : i - n < m
    · rw [difp (by omega), difp h2]
      have hh : (⟨i, by omega⟩ : Fin (n + m)) = Fin.natAdd n ⟨i - n, h2⟩ := by
        apply Fin.ext
        show i = n + (i - n)
        omega
      rw [hh, Fin.append_right]
    · rw [difn (by omega), difn h2]


theorem ble (a b : Bool) (h : a ≤ b) (ha : a = true) : b = true := by
  subst ha
  revert h
  cases b <;> decide

theorem mono_of {α : Type} [Preorder α] (f : α → Bool)
    (h : ∀ a b, a ≤ b → f a = true → f b = true) : Monotone f := by
  intro a b hab
  cases ha : f a
  · exact Bool.false_le _
  · rw [h a b hab ha]

theorem of_mono {α : Type} [Preorder α] (f : α → Bool) (h : Monotone f) (a b : α) (hab : a ≤ b)
    (ha : f a = true) : f b = true := ble _ _ (h hab) ha

def V (C : Circuit) (X : List Bool) (w : ℕ) : Bool := (C.wires X).getD w false

def D (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) : ℕ := (C.lineDegrees K M).getD w 0

theorem wires_fd (C : Circuit) (X : List Bool) : C.wires X = fd stpF X C.gates := rfl

theorem V_in (C : Circuit) (X : List Bool) (w : ℕ) (hw : w < X.length) :
    V C X w = X.getD w false := by
  unfold V
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, fd_pre _ _ _ _ hw]

theorem V_out (C : Circuit) (X : List Bool) (w : ℕ) (hw : X.length + C.gates.length ≤ w) :
    V C X w = false := by
  unfold V
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    rw [fd_len]; exact hw)]
  rfl

theorem V_gate (K : ℕ) (C : Circuit) (hrb : ReadsBack K C) (X : List Bool) (hX : X.length = K)
    (j : ℕ) (hj : j < C.gates.length) :
    V C X (K + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C X)) := by
  have h := fd_gate stpF false stpF_congr C.gates X j hj (by
    intro i hi
    have := hrb j hj i hi
    rw [hX]
    exact this)
  rw [hX] at h
  exact h

theorem D_len (K : ℕ) (M : Finset ℕ) (C : Circuit) :
    (C.lineDegrees K M).length = K + C.gates.length := by
  have := fd_len Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0)
  simpa [fd, Circuit.lineDegrees] using this

theorem D_in (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : w < K) :
    D K M C w = if w ∈ M then 1 else 0 := by
  unfold D Circuit.lineDegrees
  have := fd_pre Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) w
    (by simpa using hw)
  unfold fd at this
  rw [List.getD_eq_getElem?_getD, this]
  simp [hw]

theorem D_out (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : K + C.gates.length ≤ w) :
    D K M C w = 0 := by
  unfold D
  have hl := D_len K M C
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem foldr_max_zero : ∀ (l : List ℕ), l.foldr max 0 = 0 ↔ ∀ a ∈ l, a = 0 := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    omega

theorem D_zero_iff (K : ℕ) (M : Finset ℕ) (C : Circuit) (hrb : ReadsBack K C) (j : ℕ)
    (hj : j < C.gates.length) :
    D K M C (K + j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, D K M C i = 0 := by
  have h := fd_gate Gate.lineDegree 0 ld_congr C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) j hj (by
    intro i hi
    have := hrb j hj i hi
    simpa using this)
  simp only [List.length_map, List.length_range] at h
  have h' : D K M C (K + j) = (gateAt C j).lineDegree (C.lineDegrees K M) := h
  rw [h']
  unfold Gate.lineDegree
  split_ifs
  · rw [List.sum_eq_zero_iff]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl
  · rw [foldr_max_zero]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl

theorem indep (K : ℕ) (M : Finset ℕ) (C : Circuit) (hrb : ReadsBack K C) (X X' : List Bool)
    (hX : X.length = K) (hX' : X'.length = K)
    (h : ∀ i, i < K → i ∉ M → X.getD i false = X'.getD i false) :
    ∀ w, D K M C w = 0 → V C X w = V C X' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd
    by_cases h1 : w < K
    · rw [D_in K M C w h1] at hd
      have hwn : w ∉ M := by
        intro hc
        rw [ifp hc] at hd
        omega
      rw [V_in _ _ _ (by omega), V_in _ _ _ (by omega)]
      exact h w h1 hwn
    · by_cases h2 : w < K + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = K + j := ⟨w - K, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [V_gate K C hrb X hX j hj, V_gate K C hrb X' hX' j hj]
        congr 1
        apply List.map_congr_left
        intro i hi
        have := hrb j hj i hi
        exact ih i (by omega) ((D_zero_iff K M C hrb j hj).mp hd i hi)
      · rw [V_out _ _ _ (by omega), V_out _ _ _ (by omega)]

theorem V_mono (C : Circuit) (hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (X X' : List Bool) (hl : X.length = X'.length)
    (h : ∀ i, X.getD i false = true → X'.getD i false = true) (w : ℕ)
    (hw : V C X w = true) : V C X' w = true := by
  unfold V at hw ⊢
  rw [wires_fd] at hw ⊢
  exact mono C.gates _ _ hl hm h w hw

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

theorem V_false (K : ℕ) (C : Circuit) (hrb : ReadsBack K C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (X : List Bool) (hX : X.length = K) (h0 : ∀ i, X.getD i false = false) :
    ∀ w, V C X w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < K
    · rw [V_in _ _ _ (by omega)]
      exact h0 w
    · by_cases hlt : w < K + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = K + j := ⟨w - K, by omega⟩
        have hj : j < C.gates.length := by omega
        have hg := h2 _ (gateAt_mem C j hj)
        have hne : ∃ a, a ∈ (gateAt C j).inputs := by
          rcases hin : (gateAt C j).inputs with _ | ⟨a, t⟩
          · rw [hin] at hg
            simp at hg
          · exact ⟨a, by simp⟩
        obtain ⟨a, ha⟩ := hne
        by_contra hc
        have hc' : V C X (K + j) = true := by simpa using hc
        rw [V_gate K C hrb X hX j hj] at hc'
        rcases hg.1 with hop | hop
        · rw [ev_and _ _ hop] at hc'
          have h3 := hc' a ha
          rw [ih a (by have := hrb j hj a ha; omega)] at h3
          cases h3
        · rw [ev_or _ _ hop] at hc'
          obtain ⟨i, hi, h3⟩ := hc'
          rw [ih i (by have := hrb j hj i hi; omega)] at h3
          cases h3
      · exact V_out _ _ _ (by omega)

def W (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

def DL (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

def DP (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD w 0

theorem W_indL (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (x y y' : Fin N → Bool) (w : ℕ)
    (h : DL N C w = 0) : W N C x y w = W N C x y' w := by
  refine indep (N + N) (Finset.Ico N (N + N)) C hrb _ _ (by simp) (by simp) ?_ w h
  intro i hi hni
  have hlt : i < N := by
    by_contra hc
    exact hni (Finset.mem_Ico.mpr ⟨by omega, hi⟩)
  rw [app_getD, app_getD, difp hlt, difp hlt]

theorem W_indP (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (x x' y : Fin N → Bool) (w : ℕ)
    (h : DP N C w = 0) : W N C x y w = W N C x' y w := by
  refine indep (N + N) (Finset.range N) C hrb _ _ (by simp) (by simp) ?_ w h
  intro i hi hni
  have hlt : ¬ i < N := by
    intro hc
    exact hni (Finset.mem_range.mpr hc)
  rw [app_getD, app_getD, difn hlt, difn hlt]

theorem W_zero (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) (w : ℕ) :
    W N C (fun _ => false) (fun _ => false) w = false := by
  refine V_false (N + N) C hrb h2 _ (by simp) ?_ w
  intro i
  rw [app_getD]
  split_ifs <;> rfl

theorem W_monoX (N : ℕ) (C : Circuit)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x x' y : Fin N → Bool) (hx : x ≤ x') (w : ℕ) (h : W N C x y w = true) :
    W N C x' y w = true := by
  refine V_mono C (fun g hg => (h2 g hg).1) _ _ (by simp) ?_ w h
  intro i
  rw [app_getD, app_getD]
  split_ifs with ha hb
  · exact ble _ _ (hx ⟨i, ha⟩)
  · exact id
  · exact id

theorem W_gate (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (x y : Fin N → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    W N C x y (N + N + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W N C x y)) :=
  V_gate (N + N) C hrb _ (by simp) j hj

def Fr (N : ℕ) (C : Circuit) (h : ℕ) : Prop :=
  DP N C h = 0 ∧ 0 < DL N C h ∧ ∃ j < C.gates.length, h ∈ (gateAt C j).inputs ∧
    0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)

def NF (N : ℕ) (C : Circuit) (u : ℕ) : Prop :=
  ∃ c : ℕ → (Fin N → Bool) → Bool, (∀ h : ℕ, Monotone (c h)) ∧ ∀ x y : Fin N → Bool,
    (W N C x y u = true ↔ (W N C x (fun _ => false) u = true ∨
      ∃ h : ℕ, Fr N C h ∧ W N C (fun _ => false) y h = true ∧ c h x = true))

theorem nf_in (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) (hP : 0 < DP N C (N + N + j)) (hL : 0 < DL N C (N + N + j))
    (ih : ∀ u, u < N + N + j → 0 < DP N C u → 0 < DL N C u → NF N C u)
    (u : ℕ) (hu : u ∈ (gateAt C j).inputs) : NF N C u := by
  by_cases hl : DL N C u = 0
  · refine ⟨fun _ _ => false, fun _ => monotone_const, fun x y => ?_⟩
    rw [W_indL N C hrb x y (fun _ => false) u hl]
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨h, _, _, hc⟩)
      · exact h
      · cases hc
  · by_cases hp : DP N C u = 0
    · refine ⟨fun h _ => decide (h = u), fun _ => monotone_const, fun x y => ?_⟩
      have hfr : Fr N C u := ⟨hp, by omega, j, hj, hu, hP, hL⟩
      constructor
      · intro h
        refine Or.inr ⟨u, hfr, ?_, by simp⟩
        rw [W_indP N C hrb _ x y u hp]
        exact h
      · rintro (h | ⟨h, _, hy, hc⟩)
        · rw [W_indP N C hrb x (fun _ => false) _ u hp, W_zero N C hrb h2] at h
          cases h
        · have : h = u := by simpa using hc
          subst this
          rw [W_indP N C hrb x (fun _ => false) y h hp]
          exact hy
    · exact ih u (by have := hrb j hj u hu; omega) (by omega) (by omega)

theorem nf_or (N : ℕ) (C : Circuit) (w a b : ℕ) (ha : NF N C a) (hb : NF N C b)
    (hg : ∀ x y, W N C x y w = true ↔ (W N C x y a = true ∨ W N C x y b = true)) :
    NF N C w := by
  obtain ⟨ca, hma, hca⟩ := ha
  obtain ⟨cb, hmb, hcb⟩ := hb
  refine ⟨fun h x => ca h x || cb h x, fun h => ?_, fun x y => ?_⟩
  · apply mono_of
    intro p q hpq hh
    rcases (Bool.or_eq_true _ _).mp hh with h1 | h1
    · exact (Bool.or_eq_true _ _).mpr (Or.inl (of_mono _ (hma h) p q hpq h1))
    · exact (Bool.or_eq_true _ _).mpr (Or.inr (of_mono _ (hmb h) p q hpq h1))
  · rw [hg x y, hg x (fun _ => false), hca x y, hcb x y]
    constructor
    · rintro ((h | ⟨h, hf, hy, hc⟩) | (h | ⟨h, hf, hy, hc⟩))
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨h, hf, hy, (Bool.or_eq_true _ _).mpr (Or.inl hc)⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨h, hf, hy, (Bool.or_eq_true _ _).mpr (Or.inr hc)⟩
    · rintro ((h | h) | ⟨h, hf, hy, hc⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · rcases (Bool.or_eq_true _ _).mp hc with h1 | h1
        · exact Or.inl (Or.inr ⟨h, hf, hy, h1⟩)
        · exact Or.inr (Or.inr ⟨h, hf, hy, h1⟩)

theorem nf_and (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w p q : ℕ) (hp : DL N C p = 0) (hq : NF N C q)
    (hg : ∀ x y, W N C x y w = true ↔ (W N C x y p = true ∧ W N C x y q = true)) :
    NF N C w := by
  obtain ⟨cq, hmq, hcq⟩ := hq
  refine ⟨fun h x => cq h x && W N C x (fun _ => false) p, fun h => ?_, fun x y => ?_⟩
  · apply mono_of
    intro s t hst hh
    obtain ⟨h1, h3⟩ := (Bool.and_eq_true _ _).mp hh
    exact (Bool.and_eq_true _ _).mpr ⟨of_mono _ (hmq h) s t hst h1,
      W_monoX N C h2 s t _ hst p h3⟩
  · rw [hg x y, hg x (fun _ => false), hcq x y, W_indL N C hrb x y (fun _ => false) p hp]
    constructor
    · rintro ⟨h1, (h | ⟨h, hf, hy, hc⟩)⟩
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h, hf, hy, (Bool.and_eq_true _ _).mpr ⟨hc, h1⟩⟩
    · rintro (⟨h1, h⟩ | ⟨h, hf, hy, hc⟩)
      · exact ⟨h1, Or.inl h⟩
      · obtain ⟨h1, h3⟩ := (Bool.and_eq_true _ _).mp hc
        exact ⟨h3, Or.inr ⟨h, hf, hy, h1⟩⟩

theorem main (N : ℕ) (C : Circuit)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hand : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0)) :
    ∀ w, 0 < DP N C w → 0 < DL N C w → NF N C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hP hL
    by_cases h1 : w < N + N
    · exfalso
      have e1 : DP N C w = if w ∈ Finset.range N then 1 else 0 := D_in _ _ C w h1
      have e2 : DL N C w = if w ∈ Finset.Ico N (N + N) then 1 else 0 := D_in _ _ C w h1
      rw [e1] at hP
      rw [e2] at hL
      split_ifs at hP hL with ha hb
      · have := Finset.mem_range.mp ha
        have := (Finset.mem_Ico.mp hb).1
        omega
      all_goals omega
    · by_cases hlt : w < N + N + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj : j < C.gates.length := by omega
        have hgm := h2 _ (gateAt_mem C j hj)
        have hin := nf_in N C hrb h2 j hj hP hL ih
        obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C j).inputs = [a, b] := by
          rcases hi : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
          · rw [hi] at hgm; simp at hgm
          · rw [hi] at hgm; simp at hgm
          · exact ⟨a, b, rfl⟩
          · rw [hi] at hgm; simp at hgm
        have hna : NF N C a := hin a (by rw [hab]; simp)
        have hnb : NF N C b := hin b (by rw [hab]; simp)
        rcases hgm.1 with hop | hop
        · have hg : ∀ x y, W N C x y (N + N + j) = true ↔
              (W N C x y a = true ∧ W N C x y b = true) := by
            intro x y
            rw [W_gate N C hrb x y j hj, ev_and _ _ hop, hab]
            simp
          rcases hand j hj hop with ⟨i, hi, hi0⟩ | hall
          · rw [hab] at hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · exact nf_and N C hrb h2 _ i b hi0 hnb hg
            · exact nf_and N C hrb h2 _ i a hi0 hna (fun x y => by rw [hg x y, and_comm])
          · exfalso
            have : DP N C (N + N + j) = 0 :=
              (D_zero_iff (N + N) (Finset.range N) C hrb j hj).mpr hall
            omega
        · have hg : ∀ x y, W N C x y (N + N + j) = true ↔
              (W N C x y a = true ∨ W N C x y b = true) := by
            intro x y
            rw [W_gate N C hrb x y j hj, ev_or _ _ hop, hab]
            simp
          exact nf_or N C _ a b hna hnb hg
      · exfalso
        have : DP N C w = 0 := D_out _ _ C w (by omega)
        omega

end PEqualNP.Outside.L_meta_1713

theorem PEqualNP.Outside.L_meta_1713 : ∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true))) := by
  intro N C h2 hrb hand
  refine ⟨fun w xa xb ya yb => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun h => PEqualNP.Outside.L_meta_1713.W_indL N C hrb xa ya yb w h
  · exact fun h => PEqualNP.Outside.L_meta_1713.W_indP N C hrb xa xb ya w h
  · exact PEqualNP.Outside.L_meta_1713.W_zero N C hrb h2 w
  · exact PEqualNP.Outside.L_meta_1713.main N C h2 hrb hand
