import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1714

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

abbrev VV (C : Circuit) (X : List Bool) (w : ℕ) : Bool := (C.wires X).getD w false

abbrev DD (n : ℕ) (mk : Finset ℕ) (C : Circuit) (w : ℕ) : ℕ := (C.lineDegrees n mk).getD w 0

theorem wires_fd (C : Circuit) (X : List Bool) : C.wires X = fd stpF X C.gates := rfl

theorem VV_in (C : Circuit) (X : List Bool) (w : ℕ) (hw : w < X.length) :
    VV C X w = X.getD w false := by
  show (C.wires X).getD w false = X.getD w false
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, fd_pre _ _ _ _ hw]

theorem VV_out (C : Circuit) (X : List Bool) (w : ℕ) (hw : X.length + C.gates.length ≤ w) :
    VV C X w = false := by
  show (C.wires X).getD w false = false
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    rw [fd_len]; exact hw)]
  rfl

theorem VV_gate (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (X : List Bool) (hX : X.length = n)
    (j : ℕ) (hj : j < C.gates.length) :
    VV C X (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (VV C X)) := by
  have h := fd_gate stpF false stpF_congr C.gates X j hj (by
    intro i hi
    have := hrb j hj i hi
    rw [hX]
    exact this)
  rw [hX] at h
  exact h

theorem DD_len (n : ℕ) (mk : Finset ℕ) (C : Circuit) :
    (C.lineDegrees n mk).length = n + C.gates.length := by
  have := fd_len Gate.lineDegree C.gates ((List.range n).map fun i => if i ∈ mk then 1 else 0)
  simpa [fd, Circuit.lineDegrees] using this

theorem DD_in (n : ℕ) (mk : Finset ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    DD n mk C w = if w ∈ mk then 1 else 0 := by
  show (C.lineDegrees n mk).getD w 0 = _
  unfold Circuit.lineDegrees
  have := fd_pre Gate.lineDegree C.gates
    ((List.range n).map fun i => if i ∈ mk then 1 else 0) w (by simpa using hw)
  unfold fd at this
  rw [List.getD_eq_getElem?_getD, this]
  simp [hw]

theorem DD_out (n : ℕ) (mk : Finset ℕ) (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    DD n mk C w = 0 := by
  show (C.lineDegrees n mk).getD w 0 = 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [DD_len]; exact hw)]
  rfl

theorem DD_gate (n : ℕ) (mk : Finset ℕ) (C : Circuit) (hrb : ReadsBack n C) (j : ℕ)
    (hj : j < C.gates.length) :
    DD n mk C (n + j) = (gateAt C j).lineDegree (C.lineDegrees n mk) := by
  have h := fd_gate Gate.lineDegree 0 ld_congr C.gates
    ((List.range n).map fun i => if i ∈ mk then 1 else 0) j hj (by
    intro i hi
    have := hrb j hj i hi
    simpa using this)
  simp only [List.length_map, List.length_range] at h
  exact h

theorem gate_shape (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, gateAt C j = ⟨GateOp.and, [a, b]⟩ ∨ gateAt C j = ⟨GateOp.or, [a, b]⟩ := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨hop, hlen⟩ := hg _ hmem
  obtain ⟨a, b, hins⟩ := List.length_eq_two.mp hlen
  refine ⟨a, b, ?_⟩
  have e : gateAt C j = ⟨(gateAt C j).op, (gateAt C j).inputs⟩ := rfl
  rcases hop with h | h
  · left
    rw [e, h, hins]
  · right
    rw [e, h, hins]

theorem V_and (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (X : List Bool) (hX : X.length = n)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ) (h : gateAt C j = ⟨GateOp.and, [a, b]⟩) :
    VV C X (n + j) = (VV C X a && VV C X b) := by
  rw [VV_gate n C hrb X hX j hj, h]
  simp [GateOp.eval]

theorem V_or (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (X : List Bool) (hX : X.length = n)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ) (h : gateAt C j = ⟨GateOp.or, [a, b]⟩) :
    VV C X (n + j) = (VV C X a || VV C X b) := by
  rw [VV_gate n C hrb X hX j hj, h]
  simp [GateOp.eval]

theorem D_and (n : ℕ) (mk : Finset ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ) (h : gateAt C j = ⟨GateOp.and, [a, b]⟩) :
    DD n mk C (n + j) = DD n mk C a + DD n mk C b := by
  rw [DD_gate n mk C hrb j hj, h]
  unfold Gate.lineDegree
  split_ifs with hc
  · simp
  · exact absurd rfl hc

theorem D_or (n : ℕ) (mk : Finset ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ) (h : gateAt C j = ⟨GateOp.or, [a, b]⟩) :
    DD n mk C (n + j) = max (DD n mk C a) (DD n mk C b) := by
  rw [DD_gate n mk C hrb j hj, h]
  simp [Gate.lineDegree]

theorem indep (n : ℕ) (mk : Finset ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack n C) (X X' : List Bool) (hX : X.length = n) (hX' : X'.length = n)
    (hag : ∀ i, i < n → i ∉ mk → X.getD i false = X'.getD i false) :
    ∀ w, DD n mk C w = 0 → VV C X w = VV C X' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd
    by_cases h1 : w < n
    · rw [DD_in n mk C w h1] at hd
      have hwm : w ∉ mk := by
        intro hc
        rw [ifp hc] at hd
        omega
      rw [VV_in C X w (by omega), VV_in C X' w (by omega)]
      exact hag w h1 hwm
    · by_cases h2 : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨a, b, hab | hab⟩ := gate_shape C hg j hj
        · have ha : a < n + j := hrb j hj a (by simp [hab])
          have hb : b < n + j := hrb j hj b (by simp [hab])
          rw [D_and n mk C hrb j hj a b hab] at hd
          rw [V_and n C hrb X hX j hj a b hab, V_and n C hrb X' hX' j hj a b hab,
            ih a ha (by omega), ih b hb (by omega)]
        · have ha : a < n + j := hrb j hj a (by simp [hab])
          have hb : b < n + j := hrb j hj b (by simp [hab])
          rw [D_or n mk C hrb j hj a b hab] at hd
          have l1 := le_max_left (DD n mk C a) (DD n mk C b)
          have l2 := le_max_right (DD n mk C a) (DD n mk C b)
          rw [V_or n C hrb X hX j hj a b hab, V_or n C hrb X' hX' j hj a b hab,
            ih a ha (by omega), ih b hb (by omega)]
      · rw [VV_out C X w (by omega), VV_out C X' w (by omega)]

abbrev E (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

abbrev dL (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

abbrev dP (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD w 0

theorem E_mono (N : ℕ) (C : Circuit) (hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin N → Bool) (y : Fin N → Bool) (w : ℕ)
    (h : E N C x (fun _ => false) w = true) : E N C x y w = true := by
  unfold E at h ⊢
  rw [wires_fd] at h ⊢
  refine mono C.gates _ _ (by simp) hm ?_ w h
  intro i
  rw [app_getD, app_getD]
  split_ifs <;> simp

theorem E_indep_y (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C) (x : Fin N → Bool) (w : ℕ) (hd : dL N C w = 0)
    (y y' : Fin N → Bool) : E N C x y w = E N C x y' w :=
  indep (N + N) (Finset.Ico N (N + N)) C hg hrb _ _ (by simp) (by simp) (fun i hi hni => by
    have hiN : i < N := by
      by_contra hc
      exact hni (Finset.mem_Ico.mpr ⟨by omega, hi⟩)
    rw [app_getD, app_getD, difp hiN, difp hiN]) w hd

theorem E_indep_x (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C) (y : Fin N → Bool) (w : ℕ) (hd : dP N C w = 0)
    (x x' : Fin N → Bool) : E N C x y w = E N C x' y w :=
  indep (N + N) (Finset.range N) C hg hrb _ _ (by simp) (by simp) (fun i _ hni => by
    have hiN : ¬ i < N := fun hc => hni (Finset.mem_range.mpr hc)
    rw [app_getD, app_getD, difn hiN, difn hiN]) w hd

theorem E_pt (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) (hw : w < N) :
    E N C x y w = x ⟨w, hw⟩ := by
  show VV C (List.ofFn (Fin.append x y)) w = _
  rw [VV_in C (List.ofFn (Fin.append x y)) w (by rw [List.length_ofFn]; omega), app_getD, difp hw]

theorem dL_in (N : ℕ) (C : Circuit) (w : ℕ) (hw : w < N + N) :
    dL N C w = if N ≤ w then 1 else 0 := by
  have := DD_in (N + N) (Finset.Ico N (N + N)) C w hw
  show DD (N + N) (Finset.Ico N (N + N)) C w = _
  rw [this]
  simp [hw]

theorem dP_in (N : ℕ) (C : Circuit) (w : ℕ) (hw : w < N + N) :
    dP N C w = if w < N then 1 else 0 := by
  have := DD_in (N + N) (Finset.range N) C w hw
  show DD (N + N) (Finset.range N) C w = _
  rw [this]
  simp

abbrev XV (N : ℕ) (G : List Gate) (x : Fin N → Bool) (i : ℕ) : Bool :=
  ((⟨G, 0⟩ : Circuit).wires (List.ofFn x)).getD i false

abbrev WFX (N : ℕ) (G : List Gate) : Prop :=
  (∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    ReadsBack N ⟨G, 0⟩

abbrev Has (N : ℕ) (G : List Gate) (f : (Fin N → Bool) → Bool) : Prop :=
  ∃ i, i < N + G.length ∧ ∀ x, XV N G x i = f x

abbrev Good (N : ℕ) (G : List Gate) (f : (Fin N → Bool) → Bool) : Prop :=
  f = (fun _ => false) ∨ f = (fun _ => true) ∨ Has N G f

theorem XV_in (N : ℕ) (G : List Gate) (x : Fin N → Bool) (w : ℕ) (hw : w < N) :
    XV N G x w = x ⟨w, hw⟩ := by
  show VV ⟨G, 0⟩ (List.ofFn x) w = _
  rw [VV_in ⟨G, 0⟩ (List.ofFn x) w (by rw [List.length_ofFn]; exact hw), ofFn_getD, difp hw]

theorem XV_snoc (N : ℕ) (G : List Gate) (g : Gate) (x : Fin N → Bool) (k : ℕ) :
    XV N (G ++ [g]) x k =
      if k = N + G.length then stpF g (fd stpF (List.ofFn x) G) else XV N G x k := by
  show (fd stpF (List.ofFn x) (G ++ [g])).getD k false =
    if k = N + G.length then stpF g (fd stpF (List.ofFn x) G)
    else (fd stpF (List.ofFn x) G).getD k false
  rw [fd_app]
  show ((fd stpF (List.ofFn x) G) ++ [stpF g (fd stpF (List.ofFn x) G)]).getD k false = _
  rw [getD_snoc, fd_len, List.length_ofFn]

theorem has_in (N : ℕ) (C : Circuit) (G : List Gate) (w : ℕ) (y0 : Fin N → Bool)
    (hw : w < N + N) (hd : dL N C w = 0) : Has N G (fun x => E N C x y0 w) := by
  have hwN : w < N := by
    rw [dL_in N C w hw] at hd
    by_contra hc
    rw [ifp (by omega)] at hd
    omega
  refine ⟨w, by omega, fun x => ?_⟩
  show XV N G x w = E N C x y0 w
  rw [XV_in N G x w hwN, E_pt N C x y0 w hwN]

theorem has_op (N : ℕ) (G : List Gate) (hW : WFX N G) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (f g : (Fin N → Bool) → Bool)
    (hf : Has N G f) (hg : Has N G g) :
    ∃ G', WFX N G' ∧ G'.length = G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Has N G' (fun x => op.eval [f x, g x]) := by
  obtain ⟨i, hi, hfi⟩ := hf
  obtain ⟨j, hj, hgj⟩ := hg
  refine ⟨G ++ [⟨op, [i, j]⟩], ⟨?_, ?_⟩, by simp, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hW.1 g' h
    · rw [List.mem_singleton] at h
      rw [h]
      exact ⟨hop, rfl⟩
  · intro j' hj' a ha
    by_cases hlt : j' < G.length
    · have e : gateAt ⟨G ++ [⟨op, [i, j]⟩], 0⟩ j' = gateAt ⟨G, 0⟩ j' := by
        show (G ++ [(⟨op, [i, j]⟩ : Gate)]).getD j' _ = G.getD j' _
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hlt]
      rw [e] at ha
      exact hW.2 j' hlt a ha
    · have hj'' : j' = G.length := by
        have : j' < G.length + 1 := by simpa using hj'
        omega
      rw [hj''] at ha ⊢
      have e : gateAt ⟨G ++ [⟨op, [i, j]⟩], 0⟩ G.length = ⟨op, [i, j]⟩ := by
        show (G ++ [(⟨op, [i, j]⟩ : Gate)]).getD G.length _ = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
        simp
      rw [e] at ha
      simp at ha
      rcases ha with h | h
      · rw [h]; omega
      · rw [h]; omega
  · rintro h ⟨k, hk, hkk⟩
    refine ⟨k, by simp; omega, fun x => ?_⟩
    rw [XV_snoc, ifn (by omega)]
    exact hkk x
  · refine ⟨N + G.length, by simp, fun x => ?_⟩
    rw [XV_snoc, ifp rfl]
    have e1 := hfi x
    have e2 := hgj x
    show op.eval [XV N G x i, XV N G x j] = op.eval [f x, g x]
    rw [e1, e2]

theorem has_and (N : ℕ) (G : List Gate) (hW : WFX N G) (f g : (Fin N → Bool) → Bool)
    (hf : Has N G f) (hg : Has N G g) :
    ∃ G', WFX N G' ∧ G'.length = G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Has N G' (fun x => f x && g x) := by
  obtain ⟨G', h1, h2, h3, h4⟩ := has_op N G hW GateOp.and (Or.inl rfl) f g hf hg
  refine ⟨G', h1, h2, h3, ?_⟩
  have e : (fun x => GateOp.and.eval [f x, g x]) = (fun x => f x && g x) := by
    funext x
    simp [GateOp.eval]
  rw [← e]
  exact h4

theorem has_or (N : ℕ) (G : List Gate) (hW : WFX N G) (f g : (Fin N → Bool) → Bool)
    (hf : Has N G f) (hg : Has N G g) :
    ∃ G', WFX N G' ∧ G'.length = G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Has N G' (fun x => f x || g x) := by
  obtain ⟨G', h1, h2, h3, h4⟩ := has_op N G hW GateOp.or (Or.inr rfl) f g hf hg
  refine ⟨G', h1, h2, h3, ?_⟩
  have e : (fun x => GateOp.or.eval [f x, g x]) = (fun x => f x || g x) := by
    funext x
    simp [GateOp.eval]
  rw [← e]
  exact h4

theorem good_lift (N : ℕ) (G G' : List Gate) (f : (Fin N → Bool) → Bool)
    (h : ∀ h, Has N G h → Has N G' h) (hf : Good N G f) : Good N G' f := by
  rcases hf with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (h f h1))

theorem good_or (N : ℕ) (G : List Gate) (hW : WFX N G) (f g : (Fin N → Bool) → Bool)
    (hf : Good N G f) (hg : Good N G g) :
    ∃ G', WFX N G' ∧ G'.length ≤ G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Good N G' (fun x => f x || g x) := by
  rcases hf with hf | hf | hf
  · have e : (fun x => f x || g x) = g := by
      funext x
      rw [hf]
      simp
    refine ⟨G, hW, by omega, fun h hh => hh, ?_⟩
    rw [e]
    exact hg
  · have e : (fun x => f x || g x) = (fun _ => true) := by
      funext x
      rw [hf]
      simp
    exact ⟨G, hW, by omega, fun h hh => hh, Or.inr (Or.inl e)⟩
  · rcases hg with hg | hg | hg
    · have e : (fun x => f x || g x) = f := by
        funext x
        rw [hg]
        simp
      refine ⟨G, hW, by omega, fun h hh => hh, ?_⟩
      rw [e]
      exact Or.inr (Or.inr hf)
    · have e : (fun x => f x || g x) = (fun _ => true) := by
        funext x
        rw [hg]
        simp
      exact ⟨G, hW, by omega, fun h hh => hh, Or.inr (Or.inl e)⟩
    · obtain ⟨G', h1, h2, h3, h4⟩ := has_or N G hW f g hf hg
      exact ⟨G', h1, by omega, h3, Or.inr (Or.inr h4)⟩

theorem good_and (N : ℕ) (G : List Gate) (hW : WFX N G) (f s : (Fin N → Bool) → Bool)
    (hf : Good N G f) (hs : Has N G s) :
    ∃ G', WFX N G' ∧ G'.length ≤ G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Good N G' (fun x => f x && s x) := by
  rcases hf with hf | hf | hf
  · have e : (fun x => f x && s x) = (fun _ => false) := by
      funext x
      rw [hf]
      simp
    exact ⟨G, hW, by omega, fun h hh => hh, Or.inl e⟩
  · have e : (fun x => f x && s x) = s := by
      funext x
      rw [hf]
      simp
    refine ⟨G, hW, by omega, fun h hh => hh, ?_⟩
    rw [e]
    exact Or.inr (Or.inr hs)
  · obtain ⟨G', h1, h2, h3, h4⟩ := has_and N G hW f s hf hs
    exact ⟨G', h1, by omega, h3, Or.inr (Or.inr h4)⟩

def cx (N : ℕ) (C : Circuit) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if dL N C (N + N + i) = 0 then 1 else 0

def cm (N : ℕ) (C : Circuit) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if 0 < dP N C (N + N + i) ∧ 0 < dL N C (N + N + i) then 1 else 0

theorem cx_succ (N : ℕ) (C : Circuit) (k : ℕ) :
    cx N C (k + 1) = cx N C k + if dL N C (N + N + k) = 0 then 1 else 0 := by
  unfold cx
  rw [Finset.sum_range_succ]

theorem cm_succ (N : ℕ) (C : Circuit) (k : ℕ) :
    cm N C (k + 1) =
      cm N C k + if 0 < dP N C (N + N + k) ∧ 0 < dL N C (N + N + k) then 1 else 0 := by
  unfold cm
  rw [Finset.sum_range_succ]

theorem ncx (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ dL N C (N + N + j) = 0} = cx N C C.gates.length := by
  have e : {j : ℕ | j < C.gates.length ∧ dL N C (N + N + j) = 0} =
      ↑((Finset.range C.gates.length).filter (fun j => dL N C (N + N + j) = 0)) := by
    ext j
    simp
  rw [e, Set.ncard_coe_finset]
  exact Finset.card_filter _ _

theorem ncm (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)} =
      cm N C C.gates.length := by
  have e : {j : ℕ | j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)} =
      ↑((Finset.range C.gates.length).filter
        (fun j => 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j))) := by
    ext j
    simp
  rw [e, Set.ncard_coe_finset]
  exact Finset.card_filter _ _

theorem base (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C) :
    ∀ k, k ≤ C.gates.length → ∃ G, WFX N G ∧ G.length ≤ cx N C k ∧
      ∀ w, w < N + N + k → dL N C w = 0 → Has N G (fun x => E N C x (fun _ => false) w) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], ⟨by simp, ?_⟩, by simp, ?_⟩
    · intro j hj
      simp at hj
    · intro w hw hd
      exact has_in N C [] w _ (by omega) hd
  | succ k ih =>
    intro hk
    obtain ⟨G, hW, hlen, hhas⟩ := ih (by omega)
    have hj : k < C.gates.length := by omega
    by_cases hd0 : dL N C (N + N + k) = 0
    · obtain ⟨a, b, hab | hab⟩ := gate_shape C hg k hj
      · have ha : a < N + N + k := hrb k hj a (by simp [hab])
        have hb : b < N + N + k := hrb k hj b (by simp [hab])
        have hdd : dL N C (N + N + k) = dL N C a + dL N C b :=
          D_and (N + N) (Finset.Ico N (N + N)) C hrb k hj a b hab
        obtain ⟨G', h1, h2, h3, h4⟩ := has_and N G hW _ _ (hhas a ha (by omega))
          (hhas b hb (by omega))
        refine ⟨G', h1, ?_, ?_⟩
        · rw [cx_succ, ifp hd0]
          omega
        · intro w hw hd
          by_cases hwk : w = N + N + k
          · have e : (fun x => E N C x (fun _ => false) w) =
                (fun x => E N C x (fun _ => false) a && E N C x (fun _ => false) b) := by
              funext x
              rw [hwk]
              exact V_and (N + N) C hrb _ (by simp) k hj a b hab
            rw [e]
            exact h4
          · exact h3 _ (hhas w (by omega) hd)
      · have ha : a < N + N + k := hrb k hj a (by simp [hab])
        have hb : b < N + N + k := hrb k hj b (by simp [hab])
        have hdd : dL N C (N + N + k) = max (dL N C a) (dL N C b) :=
          D_or (N + N) (Finset.Ico N (N + N)) C hrb k hj a b hab
        have l1 := le_max_left (dL N C a) (dL N C b)
        have l2 := le_max_right (dL N C a) (dL N C b)
        obtain ⟨G', h1, h2, h3, h4⟩ := has_or N G hW _ _ (hhas a ha (by omega))
          (hhas b hb (by omega))
        refine ⟨G', h1, ?_, ?_⟩
        · rw [cx_succ, ifp hd0]
          omega
        · intro w hw hd
          by_cases hwk : w = N + N + k
          · have e : (fun x => E N C x (fun _ => false) w) =
                (fun x => E N C x (fun _ => false) a || E N C x (fun _ => false) b) := by
              funext x
              rw [hwk]
              exact V_or (N + N) C hrb _ (by simp) k hj a b hab
            rw [e]
            exact h4
          · exact h3 _ (hhas w (by omega) hd)
    · refine ⟨G, hW, ?_, ?_⟩
      · rw [cx_succ, ifn hd0]
        omega
      · intro w hw hd
        have hwk : w ≠ N + N + k := by
          intro hc
          rw [hc] at hd
          exact hd0 hd
        exact hhas w (by omega) hd

def upd (N : ℕ) (acc : ℕ → (Fin N → Bool) → Bool) (u : ℕ) (f : (Fin N → Bool) → Bool) :
    ℕ → (Fin N → Bool) → Bool :=
  fun w => if w = u then f else acc w

theorem upd_eq (N : ℕ) (acc : ℕ → (Fin N → Bool) → Bool) (u : ℕ) (f : (Fin N → Bool) → Bool) :
    upd N acc u f u = f := by
  simp [upd]

theorem upd_ne (N : ℕ) (acc : ℕ → (Fin N → Bool) → Bool) (u : ℕ) (f : (Fin N → Bool) → Bool)
    (w : ℕ) (h : w ≠ u) : upd N acc u f w = acc w := by
  simp [upd, h]

abbrev Sound (N : ℕ) (C : Circuit) (acc : ℕ → (Fin N → Bool) → Bool) : Prop :=
  ∀ w x y, acc w x = true → E N C x y w = true → E N C x y C.output = true

abbrev Comp (N : ℕ) (C : Circuit) (k : ℕ) (acc : ℕ → (Fin N → Bool) → Bool) : Prop :=
  ∀ x y, E N C x y C.output = true → E N C x (fun _ => false) C.output = true ∨
    ∃ w, (w < N + N + k ∨ dP N C w = 0) ∧ 0 < dL N C w ∧
      (w = C.output ∨ ∃ j, j < C.gates.length ∧ w ∈ (gateAt C j).inputs ∧
        0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)) ∧
      acc w x = true ∧ E N C x y w = true

abbrev Inv (N : ℕ) (C : Circuit) (B k : ℕ) (G : List Gate)
    (acc : ℕ → (Fin N → Bool) → Bool) : Prop :=
  WFX N G ∧ G.length + 2 * cm N C k ≤ B ∧
  (∀ w, w < N + N + C.gates.length → dL N C w = 0 →
    Has N G (fun x => E N C x (fun _ => false) w)) ∧
  (∀ w, Good N G (acc w)) ∧ Sound N C acc ∧ Comp N C k acc

theorem edge1 (N : ℕ) (C : Circuit) (G : List Gate) (acc : ℕ → (Fin N → Bool) → Bool)
    (hW : WFX N G) (hgood : ∀ w, Good N G (acc w)) (hsound : Sound N C acc) (g u : ℕ)
    (himp : ∀ x y, E N C x y u = true → E N C x y g = true) :
    ∃ G' acc', WFX N G' ∧ G'.length ≤ G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      (∀ w, Good N G' (acc' w)) ∧ Sound N C acc' ∧
      (∀ w x, acc w x = true → acc' w x = true) ∧
      (∀ x, acc g x = true → acc' u x = true) := by
  obtain ⟨G1, hW1, hl1, hh1, hg1⟩ := good_or N G hW (acc u) (acc g) (hgood u) (hgood g)
  refine ⟨G1, upd N acc u (fun x => acc u x || acc g x), hW1, hl1, hh1, ?_, ?_, ?_, ?_⟩
  · intro w
    by_cases hwu : w = u
    · rw [hwu, upd_eq]
      exact hg1
    · rw [upd_ne _ _ _ _ _ hwu]
      exact good_lift N G G1 _ hh1 (hgood w)
  · intro w x y haw hEw
    by_cases hwu : w = u
    · rw [hwu, upd_eq] at haw
      rw [hwu] at hEw
      simp only [Bool.or_eq_true] at haw
      rcases haw with haw | haw
      · exact hsound u x y haw hEw
      · exact hsound g x y haw (himp x y hEw)
    · rw [upd_ne _ _ _ _ _ hwu] at haw
      exact hsound w x y haw hEw
  · intro w x haw
    by_cases hwu : w = u
    · rw [hwu, upd_eq]
      rw [hwu] at haw
      simp [haw]
    · rw [upd_ne _ _ _ _ _ hwu]
      exact haw
  · intro x hag
    rw [upd_eq]
    simp [hag]

theorem edge2 (N : ℕ) (C : Circuit) (G : List Gate) (acc : ℕ → (Fin N → Bool) → Bool)
    (hW : WFX N G) (hgood : ∀ w, Good N G (acc w)) (hsound : Sound N C acc) (g u : ℕ)
    (m : (Fin N → Bool) → Bool) (hm : Has N G m)
    (himp : ∀ x y, m x = true → E N C x y u = true → E N C x y g = true) :
    ∃ G' acc', WFX N G' ∧ G'.length ≤ G.length + 2 ∧ (∀ h, Has N G h → Has N G' h) ∧
      (∀ w, Good N G' (acc' w)) ∧ Sound N C acc' ∧
      (∀ w x, acc w x = true → acc' w x = true) ∧
      (∀ x, acc g x = true → m x = true → acc' u x = true) := by
  obtain ⟨G1, hW1, hl1, hh1, hg1⟩ := good_and N G hW (acc g) m (hgood g) hm
  obtain ⟨G2, hW2, hl2, hh2, hg2⟩ := good_or N G1 hW1 (acc u) _
    (good_lift N G G1 _ hh1 (hgood u)) hg1
  refine ⟨G2, upd N acc u (fun x => acc u x || (acc g x && m x)), hW2, by omega,
    fun h hh => hh2 h (hh1 h hh), ?_, ?_, ?_, ?_⟩
  · intro w
    by_cases hwu : w = u
    · rw [hwu, upd_eq]
      exact hg2
    · rw [upd_ne _ _ _ _ _ hwu]
      exact good_lift N G1 G2 _ hh2 (good_lift N G G1 _ hh1 (hgood w))
  · intro w x y haw hEw
    by_cases hwu : w = u
    · rw [hwu, upd_eq] at haw
      rw [hwu] at hEw
      simp only [Bool.or_eq_true, Bool.and_eq_true] at haw
      rcases haw with haw | ⟨haw, hmx⟩
      · exact hsound u x y haw hEw
      · exact hsound g x y haw (himp x y hmx hEw)
    · rw [upd_ne _ _ _ _ _ hwu] at haw
      exact hsound w x y haw hEw
  · intro w x haw
    by_cases hwu : w = u
    · rw [hwu, upd_eq]
      rw [hwu] at haw
      simp [haw]
    · rw [upd_ne _ _ _ _ _ hwu]
      exact haw
  · intro x hag hmx
    rw [upd_eq]
    simp [hag, hmx]

theorem compl (N : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hmix : 0 < dP N C (N + N + k) ∧ 0 < dL N C (N + N + k))
    (acc acc' : ℕ → (Fin N → Bool) → Bool)
    (hmono : ∀ w x, acc w x = true → acc' w x = true)
    (hexp : ∀ x y, acc (N + N + k) x = true → E N C x y (N + N + k) = true →
      E N C x (fun _ => false) C.output = true ∨
      ∃ u, u < N + N + k ∧ 0 < dL N C u ∧ u ∈ (gateAt C k).inputs ∧
        acc' u x = true ∧ E N C x y u = true)
    (hcomp : Comp N C (k + 1) acc) : Comp N C k acc' := by
  intro x y hxy
  rcases hcomp x y hxy with h0 | ⟨w, hw, hdw, hfr, haw, hEw⟩
  · exact Or.inl h0
  · by_cases hwk : w = N + N + k
    · rw [hwk] at haw hEw
      rcases hexp x y haw hEw with h0 | ⟨u, hu, hdu, hmem, hau, hEu⟩
      · exact Or.inl h0
      · exact Or.inr ⟨u, Or.inl hu, hdu, Or.inr ⟨k, hk, hmem, hmix⟩, hau, hEu⟩
    · refine Or.inr ⟨w, ?_, hdw, hfr, hmono w x haw, hEw⟩
      rcases hw with hw | hw
      · left
        omega
      · right
        exact hw

theorem step (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hkm : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      (∃ i, i ∈ (gateAt C j).inputs ∧ dL N C i = 0) ∨
      (∀ h, h ∈ (gateAt C j).inputs → dP N C h = 0))
    (B k : ℕ) (hk : k < C.gates.length) (G : List Gate) (acc : ℕ → (Fin N → Bool) → Bool)
    (h : Inv N C B (k + 1) G acc) : ∃ G' acc', Inv N C B k G' acc' := by
  obtain ⟨hW, hlen, hbase, hgood, hsound, hcomp⟩ := h
  by_cases hmix : 0 < dP N C (N + N + k) ∧ 0 < dL N C (N + N + k)
  swap
  · refine ⟨G, acc, hW, ?_, hbase, hgood, hsound, ?_⟩
    · rw [cm_succ, ifn hmix] at hlen
      omega
    · intro x y hxy
      rcases hcomp x y hxy with h0 | ⟨w, hw, hdw, hfr, haw, hEw⟩
      · exact Or.inl h0
      · refine Or.inr ⟨w, ?_, hdw, hfr, haw, hEw⟩
        by_cases hwk : w = N + N + k
        · right
          rw [hwk] at hdw ⊢
          by_contra hc
          exact hmix ⟨by omega, hdw⟩
        · rcases hw with hw | hw
          · left
            omega
          · right
            exact hw
  rw [cm_succ, ifp hmix] at hlen
  have hmP := hmix.1
  have hmL := hmix.2
  obtain ⟨a, b, hab | hab⟩ := gate_shape C hg k hk
  · have ha : a < N + N + k := hrb k hk a (by simp [hab])
    have hb : b < N + N + k := hrb k hk b (by simp [hab])
    have hDL : dL N C (N + N + k) = dL N C a + dL N C b :=
      D_and (N + N) (Finset.Ico N (N + N)) C hrb k hk a b hab
    have hDP : dP N C (N + N + k) = dP N C a + dP N C b :=
      D_and (N + N) (Finset.range N) C hrb k hk a b hab
    have hV : ∀ x y, E N C x y (N + N + k) = (E N C x y a && E N C x y b) :=
      fun x y => V_and (N + N) C hrb _ (by simp) k hk a b hab
    have hsu : ∃ s u, dL N C s = 0 ∧ 0 < dL N C u ∧ s < N + N + k ∧ u < N + N + k ∧
        u ∈ (gateAt C k).inputs ∧
        ∀ x y, E N C x y (N + N + k) = (E N C x y s && E N C x y u) := by
      rcases hkm k hk (by simp [hab]) with ⟨i, hi, hi0⟩ | hall
      · simp [hab] at hi
        rcases hi with h | h
        · rw [h] at hi0
          exact ⟨a, b, hi0, by omega, ha, hb, by simp [hab], hV⟩
        · rw [h] at hi0
          exact ⟨b, a, hi0, by omega, hb, ha, by simp [hab],
            fun x y => by rw [hV x y, Bool.and_comm]⟩
      · exfalso
        have h1 := hall a (by simp [hab])
        have h2 := hall b (by simp [hab])
        omega
    obtain ⟨s, u, hs0, hupos, hs, hu, humem, hVsu⟩ := hsu
    obtain ⟨G', acc', hW', hl', hh', hgood', hsound', hmono', hadd'⟩ :=
      edge2 N C G acc hW hgood hsound (N + N + k) u (fun x => E N C x (fun _ => false) s)
        (hbase s (by omega) hs0) (by
          intro x y hm hEu
          have e := E_indep_y N C hg hrb x s hs0 y (fun _ => false)
          have hm' : E N C x (fun _ => false) s = true := hm
          rw [hVsu x y, Bool.and_eq_true]
          exact ⟨by rw [e]; exact hm', hEu⟩)
    refine ⟨G', acc', hW', by omega, fun w hw hd => hh' _ (hbase w hw hd), hgood', hsound', ?_⟩
    apply compl N C k hk hmix acc acc' hmono' ?_ hcomp
    intro x y hag hEg
    rw [hVsu x y] at hEg
    simp only [Bool.and_eq_true] at hEg
    refine Or.inr ⟨u, hu, hupos, humem, hadd' x hag ?_, hEg.2⟩
    show E N C x (fun _ => false) s = true
    rw [← E_indep_y N C hg hrb x s hs0 y (fun _ => false)]
    exact hEg.1
  · have ha : a < N + N + k := hrb k hk a (by simp [hab])
    have hb : b < N + N + k := hrb k hk b (by simp [hab])
    have hV : ∀ x y, E N C x y (N + N + k) = (E N C x y a || E N C x y b) :=
      fun x y => V_or (N + N) C hrb _ (by simp) k hk a b hab
    obtain ⟨G1, acc1, hW1, hl1, hh1, hgood1, hsound1, hmono1, hadd1⟩ :=
      edge1 N C G acc hW hgood hsound (N + N + k) a (by
        intro x y hEa
        rw [hV x y, Bool.or_eq_true]
        exact Or.inl hEa)
    obtain ⟨G2, acc2, hW2, hl2, hh2, hgood2, hsound2, hmono2, hadd2⟩ :=
      edge1 N C G1 acc1 hW1 hgood1 hsound1 (N + N + k) b (by
        intro x y hEb
        rw [hV x y, Bool.or_eq_true]
        exact Or.inr hEb)
    refine ⟨G2, acc2, hW2, by omega, fun w hw hd => hh2 _ (hh1 _ (hbase w hw hd)),
      hgood2, hsound2, ?_⟩
    apply compl N C k hk hmix acc acc2 (fun w x h => hmono2 w x (hmono1 w x h)) ?_ hcomp
    intro x y hag hEg
    rw [hV x y] at hEg
    simp only [Bool.or_eq_true] at hEg
    rcases hEg with hE | hE
    · by_cases hd : dL N C a = 0
      · left
        apply hsound (N + N + k) x _ hag
        have e := E_indep_y N C hg hrb x a hd y (fun _ => false)
        rw [hE] at e
        rw [hV x (fun _ => false), Bool.or_eq_true]
        exact Or.inl e.symm
      · exact Or.inr ⟨a, ha, by omega, by simp [hab], hmono2 a x (hadd1 x hag), hE⟩
    · by_cases hd : dL N C b = 0
      · left
        apply hsound (N + N + k) x _ hag
        have e := E_indep_y N C hg hrb x b hd y (fun _ => false)
        rw [hE] at e
        rw [hV x (fun _ => false), Bool.or_eq_true]
        exact Or.inr e.symm
      · exact Or.inr ⟨b, hb, by omega, by simp [hab], hadd2 x (hmono1 _ x hag), hE⟩

theorem down (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hkm : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      (∃ i, i ∈ (gateAt C j).inputs ∧ dL N C i = 0) ∨
      (∀ h, h ∈ (gateAt C j).inputs → dP N C h = 0))
    (B : ℕ) (G0 : List Gate) (acc0 : ℕ → (Fin N → Bool) → Bool)
    (h0 : Inv N C B C.gates.length G0 acc0) :
    ∀ d, d ≤ C.gates.length → ∃ G acc, Inv N C B (C.gates.length - d) G acc := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨G0, acc0, h0⟩
  | succ d ih =>
    intro hd
    obtain ⟨G, acc, h⟩ := ih (by omega)
    have e : C.gates.length - d = (C.gates.length - (d + 1)) + 1 := by omega
    rw [e] at h
    exact step N C hg hrb hkm B _ (by omega) G acc h

open Classical in
noncomputable def phf (N : ℕ) (G : List Gate) (acc : ℕ → (Fin N → Bool) → Bool) (h : ℕ) : ℕ :=
  if acc h = (fun _ => false) then N + G.length
  else if hh : Has N G (acc h) then Classical.choose hh else 0

theorem phf_spec (N : ℕ) (G : List Gate) (acc : ℕ → (Fin N → Bool) → Bool) (h : ℕ)
    (x : Fin N → Bool) (hg : Good N G (acc h)) :
    (acc h = (fun _ => true) ∨ XV N G x (phf N G acc h) = true) ↔ acc h x = true := by
  unfold phf
  by_cases hf : acc h = (fun _ => false)
  · rw [ifp hf]
    have hx : XV N G x (N + G.length) = false :=
      VV_out ⟨G, 0⟩ (List.ofFn x) _ (by simp)
    rw [hx]
    constructor
    · rintro (h1 | h1)
      · rw [h1]
      · simp at h1
    · intro h1
      rw [hf] at h1
      simp at h1
  · rw [ifn hf]
    rcases hg with h1 | h1 | h1
    · exact absurd h1 hf
    · constructor
      · intro _
        rw [h1]
      · intro _
        exact Or.inl h1
    · rw [difp h1]
      have hs := (Classical.choose_spec h1).2 x
      rw [hs]
      constructor
      · rintro (h2 | h2)
        · rw [h2]
        · exact h2
      · intro h2
        exact Or.inr h2

abbrev Fr (N : ℕ) (C : Circuit) (h : ℕ) : Prop :=
  dP N C h = 0 ∧ 0 < dL N C h ∧ ∃ j, j < C.gates.length ∧ h ∈ (gateAt C j).inputs ∧
    0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)

theorem main (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hkm : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      (∃ i, i ∈ (gateAt C j).inputs ∧ dL N C i = 0) ∨
      (∀ h, h ∈ (gateAt C j).inputs → dP N C h = 0))
    (hoP : 0 < dP N C C.output) (hoL : 0 < dL N C C.output) :
    ∃ (X : Circuit) (ph : ℕ → ℕ) (H : Set ℕ),
      ((∀ g ∈ X.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        ReadsBack N X) ∧
      X.size ≤ Set.ncard {j : ℕ | j < C.gates.length ∧ dL N C (N + N + j) = 0} +
        3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧
          0 < dL N C (N + N + j)} ∧
      (∀ h ∈ H, Fr N C h) ∧
      ∀ x y : Fin N → Bool, (E N C x y C.output = true ↔
        (E N C x (fun _ => false) C.output = true ∨
          ∃ h : ℕ, Fr N C h ∧ E N C (fun _ => false) y h = true ∧
            (h ∈ H ∨ (X.wires (List.ofFn x)).getD (ph h) false = true))) := by
  have hout : C.output < N + N + C.gates.length := by
    by_contra hc
    have h' : dP N C C.output = 0 := DD_out (N + N) (Finset.range N) C C.output (by omega)
    omega
  obtain ⟨G0, hW0, hl0, hb0⟩ := base N C hg hrb C.gates.length le_rfl
  have hinv0 : Inv N C (cx N C C.gates.length + 2 * cm N C C.gates.length) C.gates.length G0
      (upd N (fun _ _ => false) C.output (fun _ => true)) := by
    refine ⟨hW0, by omega, hb0, ?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = C.output
      · rw [hw, upd_eq]
        exact Or.inr (Or.inl rfl)
      · rw [upd_ne _ _ _ _ _ hw]
        exact Or.inl rfl
    · intro w x y haw hEw
      by_cases hw : w = C.output
      · rw [hw] at hEw
        exact hEw
      · rw [upd_ne _ _ _ _ _ hw] at haw
        simp at haw
    · intro x y hxy
      exact Or.inr ⟨C.output, Or.inl hout, hoL, Or.inl rfl, by simp [upd], hxy⟩
  have hfin := down N C hg hrb hkm _ G0 _ hinv0 C.gates.length le_rfl
  rw [Nat.sub_self] at hfin
  obtain ⟨G, acc, hW, hlen, hbase, hgood, hsound, hcomp⟩ := hfin
  have key : ∀ h x, Fr N C h →
      ((h ∈ ({h | Fr N C h ∧ acc h = fun _ => true} : Set ℕ) ∨
        XV N G x (phf N G acc h) = true) ↔ acc h x = true) := by
    intro h x hfr
    have hs := phf_spec N G acc h x (hgood h)
    constructor
    · rintro (⟨_, h1⟩ | h1)
      · exact hs.mp (Or.inl h1)
      · exact hs.mp (Or.inr h1)
    · intro haw
      rcases hs.mpr haw with h1 | h1
      · exact Or.inl ⟨hfr, h1⟩
      · exact Or.inr h1
  refine ⟨⟨G, 0⟩, phf N G acc, {h | Fr N C h ∧ acc h = fun _ => true}, hW, ?_,
    fun h hh => hh.1, ?_⟩
  · have h1 := ncx N C
    have h2 := ncm N C
    show G.length ≤ _
    rw [h1, h2]
    omega
  · intro x y
    constructor
    · intro hxy
      rcases hcomp x y hxy with h0 | ⟨w, hw, hdw, hfr, haw, hEw⟩
      · exact Or.inl h0
      · have hP : dP N C w = 0 := by
          rcases hw with hw | hw
          · have h1 := dL_in N C w (by omega)
            have h2 := dP_in N C w (by omega)
            rw [h2]
            rw [h1] at hdw
            by_cases hNw : N ≤ w
            · rw [ifn (by omega)]
            · rw [ifn hNw] at hdw
              omega
          · exact hw
        have hfr' : Fr N C w := by
          refine ⟨hP, hdw, ?_⟩
          rcases hfr with h | hj
          · rw [h] at hP
            omega
          · exact hj
        refine Or.inr ⟨w, hfr', ?_, (key w x hfr').mpr haw⟩
        rw [E_indep_x N C hg hrb y w hP (fun _ => false) x]
        exact hEw
    · rintro (h0 | ⟨h, hfr, hEh, hH⟩)
      · exact E_mono N C (fun g hgm => (hg g hgm).1) x y C.output h0
      · have haw := (key h x hfr).mp hH
        apply hsound h x y haw
        rw [E_indep_x N C hg hrb y h hfr.1 x (fun _ => false)]
        exact hEh

end PEqualNP.Outside.L_meta_1714

theorem PEqualNP.Outside.L_meta_1714 : ∀ (N22 : ℕ) (C22 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g22 ∈ C22.gates, (g22.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N22 + N22) C22 → (∀ j22b < C22.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD i22 0 = 0) ∨ (∀ h22b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22b 0 = 0)) → 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD C22.output 0 → 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD C22.output 0 → ∃ (X22 : PEqualNP.CircuitLowerBounds.Circuit) (ph22 : ℕ → ℕ) (H22 : Set ℕ), ((∀ g22a ∈ X22.gates, (g22a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N22 X22) ∧ X22.size ≤ Set.ncard {j22 : ℕ | j22 < C22.gates.length ∧ (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22) 0 = 0} + 3 * Set.ncard {j22a : ℕ | j22a < C22.gates.length ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22a) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22a) 0} ∧ (∀ h22 ∈ H22, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22 0 ∧ ∃ j22c < C22.gates.length, h22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22c).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22c) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22c) 0)) ∧ ∀ x22 y22 : Fin N22 → Bool, (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 y22) = true ↔ (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 (fun u22 : Fin N22 => false)) = true ∨ ∃ h22a : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22a 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22a 0 ∧ ∃ j22d < C22.gates.length, h22a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22d).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22d) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22d) 0) ∧ (C22.wires (List.ofFn (Fin.append (fun u22a : Fin N22 => false) y22))).getD h22a false = true ∧ (h22a ∈ H22 ∨ (X22.wires (List.ofFn x22)).getD (ph22 h22a) false = true))) := by
  intro N22 C22 h1 h2 h3 h4 h5
  exact PEqualNP.Outside.L_meta_1714.main N22 C22 h1 h2 h3 h4 h5
