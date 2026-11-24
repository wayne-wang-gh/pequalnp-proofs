import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1726

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


theorem arith1 (s q k m : ℕ) (hs : s ≤ q + 1) (hmq : m ≤ q) (hmk : m ≤ k) :
    s * m ≤ q * min (s - 1) k + m := by
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · subst h0
    simp
  · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hs' : s' ≤ q := by omega
    have e : (s' + 1) * m = s' * m + m := by ring
    rw [Nat.add_sub_cancel, e]
    rcases le_total s' k with h | h
    · rw [min_eq_left h]
      have h1 : s' * m ≤ q * s' := by
        rw [Nat.mul_comm q s']
        exact Nat.mul_le_mul_left _ hmq
      omega
    · rw [min_eq_right h]
      have h1 : s' * m ≤ q * k := Nat.mul_le_mul hs' hmk
      omega

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

def RSB : Prop :=
  ∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size

def F2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (X X' : Circuit) : Prop :=
  F2 X' ∧ ReadsBack n X' ∧ X.gates.length ≤ X'.gates.length ∧
  ∀ (x : List Bool), x.length = n → ∀ w, w < n + X.gates.length → V X' x w = V X x w

theorem Ext_refl (n : ℕ) (X : Circuit) (h2 : F2 X) (hrb : ReadsBack n X) : Ext n X X :=
  ⟨h2, hrb, le_refl _, fun _ _ _ _ => rfl⟩

theorem Ext_trans (n : ℕ) (X X1 X2 : Circuit) (h1 : Ext n X X1) (h2 : Ext n X1 X2) :
    Ext n X X2 := by
  obtain ⟨_, _, hl1, hv1⟩ := h1
  obtain ⟨hF, hrb, hl2, hv2⟩ := h2
  refine ⟨hF, hrb, le_trans hl1 hl2, fun x hx w hw => ?_⟩
  rw [hv2 x hx w (by omega), hv1 x hx w hw]

theorem snoc_or (n : ℕ) (X : Circuit) (h2 : F2 X) (hrb : ReadsBack n X) (a b : ℕ)
    (ha : a < n + X.gates.length) (hb : b < n + X.gates.length) :
    ∃ X' : Circuit, Ext n X X' ∧ X'.gates.length = X.gates.length + 1 ∧
      ∀ x : List Bool, x.length = n → V X' x (n + X.gates.length) = (V X x a || V X x b) := by
  have hw : ∀ x : List Bool,
      (⟨X.gates ++ [⟨GateOp.or, [a, b]⟩], X.output⟩ : Circuit).wires x
      = X.wires x ++ [(V X x a || V X x b)] := by
    intro x
    show fd stpF x (X.gates ++ [⟨GateOp.or, [a, b]⟩]) = fd stpF x X.gates ++ [_]
    rw [fd_app]
    simp [fd, stpF, GateOp.eval, V, wires_fd]
  have hlen : ∀ x : List Bool, (X.wires x).length = x.length + X.gates.length :=
    fun x => fd_len stpF X.gates x
  refine ⟨⟨X.gates ++ [⟨GateOp.or, [a, b]⟩], X.output⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact h2 g h
    · rw [List.mem_singleton.mp h]
      exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    have hj' : j < X.gates.length + 1 := by simpa using hj
    by_cases hjl : j < X.gates.length
    · have e : gateAt ⟨X.gates ++ [⟨GateOp.or, [a, b]⟩], X.output⟩ j = gateAt X j := by
        unfold gateAt
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl]
      rw [e] at hi
      exact hrb j hjl i hi
    · have hje : j = X.gates.length := by omega
      have e : gateAt ⟨X.gates ++ [⟨GateOp.or, [a, b]⟩], X.output⟩ j = ⟨GateOp.or, [a, b]⟩ := by
        unfold gateAt
        rw [hje]
        simp [List.getD_eq_getElem?_getD]
      rw [e] at hi
      have hi' : i = a ∨ i = b := by simpa using hi
      rcases hi' with h | h <;> omega
  · simp
  · intro x hx w hw'
    unfold V
    rw [hw x, getD_snoc, ifn (by rw [hlen, hx]; omega)]
  · simp
  · intro x hx
    unfold V
    rw [hw x, getD_snoc, ifp (by rw [hlen, hx])]
    rfl

theorem or_set (n : ℕ) (s : Finset ℕ) (hs : s.Nonempty) :
    ∀ (X : Circuit), F2 X → ReadsBack n X → (∀ w ∈ s, w < n + X.gates.length) →
    ∃ (X' : Circuit) (o : ℕ), Ext n X X' ∧ o < n + X'.gates.length ∧
      X'.gates.length + 1 = X.gates.length + s.card ∧
      ∀ x : List Bool, x.length = n → (V X' x o = true ↔ ∃ w ∈ s, V X x w = true) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro X h2 hrb hw
    exact ⟨X, a, Ext_refl n X h2 hrb, hw a (Finset.mem_singleton_self a), by simp,
      fun x _ => by simp⟩
  | cons a s ha hs ih =>
    intro X h2 hrb hw
    obtain ⟨X1, o1, hE1, ho1, hl1, hv1⟩ :=
      ih X h2 hrb (fun w hw' => hw w (Finset.mem_cons.mpr (Or.inr hw')))
    have ha' : a < n + X.gates.length := hw a (Finset.mem_cons.mpr (Or.inl rfl))
    have hle := hE1.2.2.1
    obtain ⟨X2, hE2, hl2, hv2⟩ := snoc_or n X1 hE1.1 hE1.2.1 a o1 (by omega) ho1
    refine ⟨X2, n + X1.gates.length, Ext_trans n X X1 X2 hE1 hE2, by omega, ?_, ?_⟩
    · rw [Finset.card_cons]
      omega
    · intro x hx
      rw [hv2 x hx, Bool.or_eq_true, hv1 x hx, hE1.2.2.2 x hx a ha']
      simp only [Finset.mem_cons, exists_eq_or_imp]

theorem or_fam {ι : Type} [DecidableEq ι] (n : ℕ) (f : ι → Finset ℕ) (X : Circuit) (h2 : F2 X)
    (hrb : ReadsBack n X) :
    ∀ (T : Finset ι), (∀ i ∈ T, (f i).Nonempty ∧ ∀ w ∈ f i, w < n + X.gates.length) →
    ∃ (X' : Circuit) (o : ι → ℕ), Ext n X X' ∧
      X'.gates.length + T.card = X.gates.length + ∑ i ∈ T, (f i).card ∧
      (∀ i ∈ T, o i < n + X'.gates.length) ∧
      ∀ i ∈ T, ∀ x : List Bool, x.length = n →
        (V X' x (o i) = true ↔ ∃ w ∈ f i, V X x w = true) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨X, fun _ => 0, Ext_refl n X h2 hrb, by simp, by simp, by simp⟩
  | insert a T ha ih =>
    intro hT
    obtain ⟨X1, o1, hE1, hl1, ho1, hv1⟩ := ih (fun i hi => hT i (Finset.mem_insert_of_mem hi))
    obtain ⟨hne, hwa⟩ := hT a (Finset.mem_insert_self a T)
    have hle := hE1.2.2.1
    obtain ⟨X2, oa, hE2, hoa, hl2, hv2⟩ := or_set n (f a) hne X1 hE1.1 hE1.2.1
      (fun w hw => by have := hwa w hw; omega)
    have hle2 := hE2.2.2.1
    refine ⟨X2, Function.update o1 a oa, Ext_trans n X X1 X2 hE1 hE2, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
      omega
    · intro i hi
      by_cases hia : i = a
      · rw [hia, Function.update_self]
        exact hoa
      · rw [Function.update_of_ne hia]
        have := ho1 i ((Finset.mem_insert.mp hi).resolve_left hia)
        omega
    · intro i hi x hx
      by_cases hia : i = a
      · rw [hia, Function.update_self, hv2 x hx]
        constructor
        · rintro ⟨w, hw, h⟩
          exact ⟨w, hw, by rw [← hE1.2.2.2 x hx w (hwa w hw)]; exact h⟩
        · rintro ⟨w, hw, h⟩
          exact ⟨w, hw, by rw [hE1.2.2.2 x hx w (hwa w hw)]; exact h⟩
      · have hiT := (Finset.mem_insert.mp hi).resolve_left hia
        rw [Function.update_of_ne hia, hE2.2.2.2 x hx (o1 i) (ho1 i hiT)]
        exact hv1 i hiT x hx

theorem rsb_fin (H1 : RSB) {ι : Type} (T : Finset ι) (n k : ℕ) (U S : ι → Finset (Fin n))
    (C : Circuit) (o c : ι → ℕ)
    (hU : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (U i ∩ U j).card ≤ 1)
    (hS : ∀ i ∈ T, S i ⊆ U i) (h2 : ∀ i ∈ T, 2 ≤ (S i).card) (hF : F2 C) (hrb : ReadsBack n C)
    (hsing : ∀ i ∈ T, ∀ p : Fin n,
      (V C (List.ofFn (fun a : Fin n => decide (a = p))) (o i) = true ↔ p ∈ S i))
    (hzero : ∀ i ∈ T, ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun b : Fin n => x b = true)).card ≤ k →
      (∀ b ∈ U i, x b = false) → V C (List.ofFn x) (o i) = false)
    (hck : ∀ i ∈ T, c i ≤ k) (hcS : ∀ i ∈ T, c i + 1 ≤ (S i).card) :
    ∑ i ∈ T, c i ≤ C.gates.length := by
  have e := T.equivFin
  have h := H1 n T.card k (fun i => U (e.symm i).1) (fun i => S (e.symm i).1) C
    (fun i => o (e.symm i).1) (fun i => c (e.symm i).1)
    (fun i j hij => hU _ (e.symm i).2 _ (e.symm j).2
      (fun hc => hij (e.symm.injective (Subtype.ext hc))))
    (fun i => hS _ (e.symm i).2) (fun i => h2 _ (e.symm i).2) hF hrb
    (fun i p => hsing _ (e.symm i).2 p) (fun i x hx hxU => hzero _ (e.symm i).2 x hx hxU)
    (fun i => hck _ (e.symm i).2) (fun i => hcS _ (e.symm i).2)
  have e1 : ∑ i : Fin T.card, c (e.symm i).1 = ∑ t : T, c t.1 :=
    Equiv.sum_comp e.symm (fun t : T => c t.1)
  have e2 : ∑ t : T, c t.1 = ∑ i ∈ T, c i := Finset.sum_coe_sort T c
  rw [← e2, ← e1]
  exact h

theorem rsb_or (H1 : RSB) {ι : Type} [DecidableEq ι] (T : Finset ι) (n k : ℕ)
    (U S : ι → Finset (Fin n)) (C : Circuit) (f : ι → Finset ℕ) (c : ι → ℕ) (hF : F2 C)
    (hrb : ReadsBack n C)
    (hf : ∀ i ∈ T, ∀ w ∈ f i, w < n + C.gates.length)
    (hU : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (U i ∩ U j).card ≤ 1)
    (hS : ∀ i ∈ T, S i ⊆ U i) (h2 : ∀ i ∈ T, 2 ≤ (S i).card)
    (hsing : ∀ i ∈ T, ∀ p : Fin n,
      (p ∈ S i ↔ ∃ w ∈ f i, V C (List.ofFn (fun a : Fin n => decide (a = p))) w = true))
    (hzero : ∀ i ∈ T, ∀ w ∈ f i, ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun b : Fin n => x b = true)).card ≤ k →
      (∀ b ∈ U i, x b = false) → V C (List.ofFn x) w = false)
    (hck : ∀ i ∈ T, c i ≤ k) (hcS : ∀ i ∈ T, c i + 1 ≤ (S i).card) :
    ∑ i ∈ T, c i + T.card ≤ C.gates.length + ∑ i ∈ T, (f i).card := by
  obtain ⟨X', o, hE, hl, _, hv⟩ := or_fam n f C hF hrb T (fun i hi => by
    refine ⟨?_, hf i hi⟩
    have hpos : 0 < (S i).card := by have := h2 i hi; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    obtain ⟨w, hw, _⟩ := (hsing i hi p).mp hp
    exact ⟨w, hw⟩)
  have h := rsb_fin H1 T n k U S X' o c hU hS h2 hE.1 hE.2.1
    (fun i hi p => (hv i hi _ (by simp)).trans (hsing i hi p).symm)
    (fun i hi x hx hxU => by
      by_contra hne
      have hV : V X' (List.ofFn x) (o i) = true := by simpa using hne
      obtain ⟨w, hw, h'⟩ := (hv i hi _ (by simp)).mp hV
      rw [hzero i hi w hw x hx hxU] at h'
      cases h')
    hck hcS
  omega

theorem two_lines (N : ℕ) (I : Fin N → Fin N → Prop)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p p' l l' : Fin N) (h1 : I p l) (h2 : I p' l) (h3 : I p l') (h4 : I p' l') :
    p = p' ∨ l = l' := by
  by_cases h : p = p'
  · exact Or.inl h
  · exact Or.inr ((hu p p' h).unique ⟨h1, h2⟩ ⟨h3, h4⟩)

theorem line_inter (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (l l' : Fin N) (hll : l ≠ l') :
    ((Finset.univ.filter (fun p => I p l)) ∩ (Finset.univ.filter (fun p => I p l'))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp p' hp'
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  rcases two_lines N I hu p p' l l' hp.1 hp'.1 hp.2 hp'.2 with h | h
  · exact h
  · exact absurd h hll

theorem natAdd_inj' (N : ℕ) (l l' : Fin N) (h : Fin.natAdd N l = Fin.natAdd N l') : l = l' := by
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd] at this
  exact Fin.ext (by omega)

theorem dc {α β γ : Type} (A : Finset α) (B : Finset β) (G : Finset γ) (P : α → γ → Prop)
    (Q : β → γ → Prop) [∀ a g, Decidable (P a g)] [∀ b g, Decidable (Q b g)]
    (h : ∀ g ∈ G, (A.filter (fun a => P a g)).card + (B.filter (fun b => Q b g)).card ≤ 1) :
    ∑ a ∈ A, (G.filter (fun g => P a g)).card + ∑ b ∈ B, (G.filter (fun g => Q b g)).card
      ≤ G.card := by
  have e1 : ∑ a ∈ A, (G.filter (fun g => P a g)).card
      = ∑ g ∈ G, (A.filter (fun a => P a g)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have e2 : ∑ b ∈ B, (G.filter (fun g => Q b g)).card
      = ∑ g ∈ G, (B.filter (fun b => Q b g)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [e1, e2, ← Finset.sum_add_distrib]
  calc ∑ g ∈ G, ((A.filter (fun a => P a g)).card + (B.filter (fun b => Q b g)).card)
      ≤ ∑ g ∈ G, 1 := Finset.sum_le_sum h
    _ = G.card := by simp

theorem part3 (n : ℕ) (P1 P2 P3 : ℕ → Prop) [DecidablePred P1] [DecidablePred P2]
    [DecidablePred P3] (h12 : ∀ j, P1 j → ¬ P2 j) (h13 : ∀ j, P1 j → ¬ P3 j)
    (h23 : ∀ j, P2 j → ¬ P3 j) :
    ((Finset.range n).filter P1).card + ((Finset.range n).filter P2).card
      + ((Finset.range n).filter P3).card ≤ n := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc ∑ j ∈ Finset.range n, ((if P1 j then 1 else 0) + (if P2 j then 1 else 0)
        + (if P3 j then 1 else 0))
      ≤ ∑ j ∈ Finset.range n, 1 := Finset.sum_le_sum (fun j _ => by
        by_cases h1 : P1 j
        · rw [ifp h1, ifn (h12 j h1), ifn (h13 j h1)]
        · by_cases h2 : P2 j
          · rw [ifn h1, ifp h2, ifn (h23 j h2)]
          · rw [ifn h1, ifn h2]
            split_ifs <;> omega)
    _ = n := by simp

theorem ncard_eq (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Set.ncard {j : ℕ | j < n ∧ P j} = ((Finset.range n).filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp

def ep {N : ℕ} (p : Fin N) : Fin N → Bool := fun a => decide (a = p)

def ind {N : ℕ} (T : Finset (Fin N)) : Fin N → Bool := fun a => decide (a ∈ T)

def z0 (N : ℕ) : Fin N → Bool := fun _ => false

def Wv (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  V C (List.ofFn (Fin.append x y)) w

def DL (N : ℕ) (C : Circuit) (w : ℕ) : ℕ := D (N + N) (Finset.Ico N (N + N)) C w

def DP (N : ℕ) (C : Circuit) (w : ℕ) : ℕ := D (N + N) (Finset.range N) C w

def cf (N : ℕ) (C : Circuit) (x y : Fin N → Bool) : Bool := Wv N C x y C.output

def Fr (N : ℕ) (C : Circuit) (h : ℕ) : Prop :=
  DP N C h = 0 ∧ 0 < DL N C h ∧ ∃ j < C.gates.length, h ∈ (gateAt C j).inputs ∧
    0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j)

def LT (N : ℕ) (C : Circuit) (W : Finset (Fin N)) (h : ℕ) (l : Fin N) : Prop :=
  Wv N C (z0 N) (ep l) h = true ∧ ∀ l' ∈ W, Wv N C (z0 N) (ep l') h = true → l' = l

def MT (N : ℕ) (C : Circuit) (W : Finset (Fin N)) (h : ℕ) : Prop :=
  ∃ l ∈ W, ∃ l' ∈ W, l ≠ l' ∧ Wv N C (z0 N) (ep l) h = true ∧ Wv N C (z0 N) (ep l') h = true

theorem LT_or_MT (N : ℕ) (C : Circuit) (W : Finset (Fin N)) (h : ℕ) (l : Fin N) (hl : l ∈ W)
    (hh : Wv N C (z0 N) (ep l) h = true) : LT N C W h l ∨ MT N C W h := by
  by_cases hc : ∀ l' ∈ W, Wv N C (z0 N) (ep l') h = true → l' = l
  · exact Or.inl ⟨hh, hc⟩
  · right
    push_neg at hc
    obtain ⟨l', hl', hh', hne⟩ := hc
    exact ⟨l', hl', l, hl, hne, hh', hh⟩

theorem LT_MT_false (N : ℕ) (C : Circuit) (W : Finset (Fin N)) (h : ℕ) (l : Fin N)
    (h1 : LT N C W h l) (h2 : MT N C W h) : False := by
  obtain ⟨l1, hl1, l2, hl2, hne, hh1, hh2⟩ := h2
  exact hne ((h1.2 l1 hl1 hh1).trans (h1.2 l2 hl2 hh2).symm)

theorem ep_card {N : ℕ} (p : Fin N) :
    (Finset.univ.filter (fun a : Fin N => ep p a = true)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have ha' : a = p := by simpa [ep] using ha
  have hb' : b = p := by simpa [ep] using hb
  rw [ha', hb']

theorem ind_empty (N : ℕ) : ind (∅ : Finset (Fin N)) = z0 N := by
  funext a
  simp [ind, z0]

theorem append_split (N : ℕ) (zf : Fin (N + N) → Bool) :
    zf = Fin.append (fun i => zf (Fin.castAdd N i)) (fun i => zf (Fin.natAdd N i)) := by
  funext a
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · rw [Fin.append_left]
  · rw [Fin.append_right]

theorem epp_nat (N : ℕ) (l : Fin N) :
    (fun a : Fin (N + N) => decide (a = Fin.natAdd N l)) = Fin.append (z0 N) (ep l) := by
  funext a
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · rw [Fin.append_left]
    show decide (Fin.castAdd N i = Fin.natAdd N l) = false
    refine decide_eq_false (fun h => ?_)
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := i.isLt
    omega
  · rw [Fin.append_right]
    show decide (Fin.natAdd N i = Fin.natAdd N l) = decide (i = l)
    by_cases h : i = l
    · subst h
      simp
    · rw [decide_eq_false h, decide_eq_false (fun hh => h (natAdd_inj' N i l hh))]

theorem Wv_line (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (h : ℕ) (h1 : N ≤ h)
    (h2 : h < N + N) : Wv N C x y h = y ⟨h - N, by omega⟩ := by
  unfold Wv
  rw [V_in _ _ _ (by simp; omega), app_getD, difn (by omega), difp (by omega)]

theorem DP_point (N : ℕ) (C : Circuit) (h : ℕ) (h1 : h < N) : DP N C h = 1 := by
  unfold DP
  rw [D_in _ _ _ _ (by omega), ifp (Finset.mem_range.mpr h1)]

theorem frR (N : ℕ) (C : Circuit) (h : ℕ) (l : Fin N) (hfr : Fr N C h)
    (hh : Wv N C (z0 N) (ep l) h = true) :
    h = N + l.val ∨ (N + N ≤ h ∧ h < N + N + C.gates.length) := by
  by_cases h1 : h < N
  · have := DP_point N C h h1
    have := hfr.1
    omega
  · by_cases h2 : h < N + N
    · left
      rw [Wv_line N C _ _ h (by omega) h2] at hh
      have e : (⟨h - N, by omega⟩ : Fin N) = l := by simpa [ep] using hh
      have := congrArg Fin.val e
      simp only at this
      omega
    · right
      refine ⟨by omega, ?_⟩
      by_contra h3
      have : Wv N C (z0 N) (ep l) h = false := V_out _ _ _ (by simp; omega)
      rw [hh] at this
      cases this

theorem mtR (N : ℕ) (C : Circuit) (W : Finset (Fin N)) (h : ℕ) (hfr : Fr N C h)
    (hmt : MT N C W h) : N + N ≤ h ∧ h < N + N + C.gates.length := by
  obtain ⟨l1, _, l2, _, hne, hh1, hh2⟩ := hmt
  have := l1.isLt
  have := l2.isLt
  rcases frR N C h l1 hfr hh1 with e | e
  · rcases frR N C h l2 hfr hh2 with e' | e'
    · exact absurd (Fin.ext (by omega)) hne
    · omega
  · exact e

theorem inc_empty (N a b : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Dc : Circuit)
    (S W : Finset (Fin N))
    (hacc : ∀ p ∈ S, ∀ l ∈ W, I p l → cf N Dc (ep p) (ep l) = true)
    (hrejP : ∀ p ∈ S, ∀ T ⊆ W, (∀ l ∈ T, ¬ I p l) → T.card ≤ a →
      cf N Dc (ep p) (ind T) = false)
    (hrejL : ∀ l ∈ W, ∀ X ⊆ S, (∀ p ∈ X, ¬ I p l) → X.card ≤ b →
      cf N Dc (ind X) (ep l) = false)
    (hor : (∀ x y y' : Fin N → Bool, cf N Dc x y = cf N Dc x y') ∨
      (∀ x x' y : Fin N → Bool, cf N Dc x y = cf N Dc x' y)) :
    ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨p, l⟩ hpl hI
  obtain ⟨hp, hl⟩ := Finset.mem_product.mp hpl
  have hacc' := hacc p hp l hl hI
  rcases hor with h | h
  · rw [h (ep p) (ep l) (ind ∅), hrejP p hp ∅ (Finset.empty_subset _) (by simp) (by simp)]
      at hacc'
    cases hacc'
  · rw [h (ep p) (ind ∅) (ep l), hrejL l hl ∅ (Finset.empty_subset _) (by simp) (by simp)]
      at hacc'
    cases hacc'

theorem core (H1 : RSB) (q N a b : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (Dc : Circuit) (S W : Finset (Fin N)) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (hF : F2 Dc) (hrb : ReadsBack (N + N) Dc) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hign : ∀ x x' y y' : Fin N → Bool, (∀ p ∈ S, x p = x' p) → (∀ l ∈ W, y l = y' l) →
      cf N Dc x y = cf N Dc x' y')
    (hacc : ∀ p ∈ S, ∀ l ∈ W, I p l → cf N Dc (ep p) (ep l) = true)
    (hrejP : ∀ p ∈ S, ∀ T ⊆ W, (∀ l ∈ T, ¬ I p l) → T.card ≤ a →
      cf N Dc (ep p) (ind T) = false)
    (hrejL : ∀ l ∈ W, ∀ X ⊆ S, (∀ p ∈ X, ¬ I p l) → X.card ≤ b →
      cf N Dc (ind X) (ep l) = false)
    (hP0 : ∀ (w : ℕ) (xa xb ya : Fin N → Bool), DP N Dc w = 0 →
      Wv N Dc xa ya w = Wv N Dc xb ya w)
    (X : Circuit) (ph : ℕ → ℕ) (Hs : Set ℕ) (hXF : F2 X) (hXrb : ReadsBack N X)
    (hXsize : X.gates.length ≤
      ((Finset.range Dc.gates.length).filter (fun j => DL N Dc (N + N + j) = 0)).card
      + 3 * ((Finset.range Dc.gates.length).filter
          (fun j => 0 < DP N Dc (N + N + j) ∧ 0 < DL N Dc (N + N + j))).card)
    (hform : ∀ x y : Fin N → Bool, (cf N Dc x y = true ↔ (cf N Dc x (z0 N) = true ∨
      ∃ h : ℕ, Fr N Dc h ∧ Wv N Dc (z0 N) y h = true ∧
        (h ∈ Hs ∨ V X (List.ofFn x) (ph h) = true)))) :
    min (min a b) q * ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card
      ≤ 5 * q * Dc.gates.length + min (min a b) q * (S.card + W.card) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = min (min a b) q := ⟨_, rfl⟩
  rw [← hm]
  have hma : m ≤ a := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hmb : m ≤ b := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hmq : m ≤ q := by rw [hm]; exact min_le_right _ _
  have ZX : ∀ l ∈ W, ∀ h, Fr N Dc h → Wv N Dc (z0 N) (ep l) h = true → ∀ x : Fin N → Bool,
      (Finset.univ.filter (fun p => x p = true)).card ≤ b → (∀ p, I p l → x p = false) →
      V X (List.ofFn x) (ph h) = false := by
    intro l hl h hfr hh x hx hxl
    by_contra hne
    have hV : V X (List.ofFn x) (ph h) = true := by simpa using hne
    have h1 : cf N Dc x (ep l) = true :=
      (hform x (ep l)).mpr (Or.inr ⟨h, hfr, hh, Or.inr hV⟩)
    rw [hign x (ind (S.filter (fun p => x p = true))) (ep l) (ep l)
      (fun p hp => by simp [ind, hp]) (fun _ _ => rfl),
      hrejL l hl _ (Finset.filter_subset _ _)
        (fun p hp hI => by
          have := hxl p hI
          rw [(Finset.mem_filter.mp hp).2] at this
          cases this)
        (le_trans (Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.subset_univ S))) hx)] at h1
    cases h1
  have ZY : ∀ p ∈ S, ∀ h, Fr N Dc h → V X (List.ofFn (ep p)) (ph h) = true →
      ∀ y : Fin N → Bool, (Finset.univ.filter (fun l => y l = true)).card ≤ a →
      (∀ l, I p l → y l = false) → Wv N Dc (z0 N) y h = false := by
    intro p hp h hfr hV y hy hyp
    by_contra hne
    have hh : Wv N Dc (z0 N) y h = true := by simpa using hne
    have h1 : cf N Dc (ep p) y = true :=
      (hform (ep p) y).mpr (Or.inr ⟨h, hfr, hh, Or.inr hV⟩)
    rw [hign (ep p) (ep p) y (ind (W.filter (fun l => y l = true))) (fun _ _ => rfl)
      (fun l hl => by simp [ind, hl]),
      hrejP p hp _ (Finset.filter_subset _ _)
        (fun l hl hI => by
          have := hyp l hI
          rw [(Finset.mem_filter.mp hl).2] at this
          cases this)
        (le_trans (Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.subset_univ W))) hy)] at h1
    cases h1
  have ZY' : ∀ p ∈ S, ∀ h, Fr N Dc h → V X (List.ofFn (ep p)) (ph h) = true →
      ∀ zf : Fin (N + N) → Bool, (Finset.univ.filter (fun z => zf z = true)).card ≤ a →
      (∀ l, I p l → zf (Fin.natAdd N l) = false) → V Dc (List.ofFn zf) h = false := by
    intro p hp h hfr hV zf hzf hzp
    have e : V Dc (List.ofFn zf) h
        = Wv N Dc (fun i => zf (Fin.castAdd N i)) (fun i => zf (Fin.natAdd N i)) h := by
      unfold Wv
      rw [← append_split N zf]
    rw [e, hP0 h _ (z0 N) _ hfr.1]
    refine ZY p hp h hfr hV _ (le_trans ?_ hzf) hzp
    exact Finset.card_le_card_of_injOn (Fin.natAdd N)
      (fun l hl => by
        have hl' := (Finset.mem_filter.mp hl).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩)
      (fun l _ l' _ hll => natAdd_inj' N l l' hll)
  have cov : ∀ p ∈ S, ∀ l ∈ W, I p l → ∃ h, Fr N Dc h ∧ Wv N Dc (z0 N) (ep l) h = true ∧
      V X (List.ofFn (ep p)) (ph h) = true := by
    intro p hp l hl hI
    rcases (hform (ep p) (ep l)).mp (hacc p hp l hl hI) with h1 | ⟨h, hfr, hh, hH | hV⟩
    · have := hrejP p hp ∅ (Finset.empty_subset _) (by simp) (by simp)
      rw [ind_empty, h1] at this
      cases this
    · have h1 : cf N Dc (z0 N) (ep l) = true :=
        (hform (z0 N) (ep l)).mpr (Or.inr ⟨h, hfr, hh, Or.inl hH⟩)
      have := hrejL l hl ∅ (Finset.empty_subset _) (by simp) (by simp)
      rw [ind_empty, h1] at this
      cases this
    · exact ⟨h, hfr, hh, hV⟩
  have incH : ∀ p ∈ S, ∀ (l : Fin N) (h : ℕ), Fr N Dc h → Wv N Dc (z0 N) (ep l) h = true →
      V X (List.ofFn (ep p)) (ph h) = true → I p l := by
    intro p hp l h hfr hh hV
    by_contra hI
    have := ZY p hp h hfr hV (ep l) (le_trans (ep_card l) ha)
      (fun l' hI' => decide_eq_false (fun hll => hI (hll ▸ hI')))
    rw [hh] at this
    cases this
  have hXin : ∀ (x : Fin N → Bool) (w : ℕ), V X (List.ofFn x) w = true →
      w < N + X.gates.length := by
    intro x w hV
    by_contra hc
    have : V X (List.ofFn x) w = false := V_out _ _ _ (by simp; omega)
    rw [hV] at this
    cases this
  obtain ⟨FG, hFG⟩ : ∃ FG : Finset ℕ, FG = (Finset.range Dc.gates.length).filter
      (fun j => DP N Dc (N + N + j) = 0 ∧ 0 < DL N Dc (N + N + j)) := ⟨_, rfl⟩
  have hFGm : ∀ j, j ∈ FG ↔ (j < Dc.gates.length ∧ DP N Dc (N + N + j) = 0 ∧
      0 < DL N Dc (N + N + j)) := by
    intro j
    rw [hFG, Finset.mem_filter, Finset.mem_range]
  obtain ⟨fX, hfX⟩ : ∃ fX : Fin N → Finset ℕ, ∀ l w, w ∈ fX l ↔
      (w < N + X.gates.length ∧ ∃ h, Fr N Dc h ∧ LT N Dc W h l ∧ ph h = w) :=
    ⟨fun l => (Finset.range (N + X.gates.length)).filter
      (fun w => ∃ h, Fr N Dc h ∧ LT N Dc W h l ∧ ph h = w),
      fun l w => by rw [Finset.mem_filter, Finset.mem_range]⟩
  obtain ⟨SX, hSX⟩ : ∃ SX : Fin N → Finset (Fin N), ∀ l p, p ∈ SX l ↔
      ∃ w ∈ fX l, V X (List.ofFn (fun a : Fin N => decide (a = p))) w = true :=
    ⟨fun l => Finset.univ.filter
      (fun p => ∃ w ∈ fX l, V X (List.ofFn (fun a : Fin N => decide (a = p))) w = true),
      fun l p => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)⟩
  obtain ⟨fY, hfY⟩ : ∃ fY : Fin N → Finset ℕ, ∀ p h, h ∈ fY p ↔
      (h < N + N + Dc.gates.length ∧ Fr N Dc h ∧ MT N Dc W h ∧
        V X (List.ofFn (ep p)) (ph h) = true) :=
    ⟨fun p => (Finset.range (N + N + Dc.gates.length)).filter
      (fun h => Fr N Dc h ∧ MT N Dc W h ∧ V X (List.ofFn (ep p)) (ph h) = true),
      fun p h => by rw [Finset.mem_filter, Finset.mem_range]⟩
  obtain ⟨SY, hSY⟩ : ∃ SY : Fin N → Finset (Fin (N + N)), ∀ p z, z ∈ SY p ↔
      ∃ h ∈ fY p, V Dc (List.ofFn (fun a : Fin (N + N) => decide (a = z))) h = true :=
    ⟨fun p => Finset.univ.filter
      (fun z => ∃ h ∈ fY p, V Dc (List.ofFn (fun a : Fin (N + N) => decide (a = z))) h = true),
      fun p z => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)⟩
  have hSXU : ∀ l ∈ W, SX l ⊆ Finset.univ.filter (fun p => I p l) := by
    intro l hl p hp
    obtain ⟨w, hw, hV⟩ := (hSX l p).mp hp
    obtain ⟨_, h, hfr, hlt, rfl⟩ := (hfX l w).mp hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hI
    have := ZX l hl h hfr hlt.1 (ep p) (le_trans (ep_card p) hb)
      (fun p' hI' => decide_eq_false (fun hpp => hI (hpp ▸ hI')))
    rw [show V X (List.ofFn (ep p)) (ph h) = true from hV] at this
    cases this
  have hSYU : ∀ p ∈ S, SY p ⊆ (Finset.univ.filter (fun l => I p l)).image (Fin.natAdd N) := by
    intro p hp z hz
    obtain ⟨h, hh, hV⟩ := (hSY p z).mp hz
    obtain ⟨_, hfr, hmt, hVX⟩ := (hfY p h).mp hh
    by_contra hzU
    have := ZY' p hp h hfr hVX (fun a => decide (a = z)) (le_trans (ep_card z) ha)
      (fun l hI => decide_eq_false (fun hlz => hzU (Finset.mem_image.mpr
        ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩, hlz⟩)))
    rw [hV] at this
    cases this
  have hUY : ∀ p p' : Fin N, p ≠ p' →
      ((Finset.univ.filter (fun l => I p l)).image (Fin.natAdd N) ∩
        (Finset.univ.filter (fun l => I p' l)).image (Fin.natAdd N)).card ≤ 1 := by
    intro p p' hpp
    rw [Finset.card_le_one]
    intro z hz z' hz'
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hz hz'
    obtain ⟨⟨l1, h1, rfl⟩, ⟨l2, h2, e2⟩⟩ := hz
    obtain ⟨⟨l3, h3, rfl⟩, ⟨l4, h4, e4⟩⟩ := hz'
    have e2' : l2 = l1 := natAdd_inj' N l2 l1 e2
    have e4' : l4 = l3 := natAdd_inj' N l4 l3 e4
    rcases two_lines N I huniq p p' l1 l3 h1 (e2' ▸ h2) h3 (e4' ▸ h4) with h | h
    · exact absurd h hpp
    · rw [h]
  have hXsum := rsb_or H1 (W.filter (fun l => 2 ≤ (SX l).card)) N m
    (fun l => Finset.univ.filter (fun p => I p l)) SX X fX
    (fun l => min ((SX l).card - 1) m) hXF hXrb
    (fun l _ w hw => ((hfX l w).mp hw).1)
    (fun l _ l' _ hll => line_inter N I huniq l l' hll)
    (fun l hl => hSXU l (Finset.mem_filter.mp hl).1)
    (fun l hl => (Finset.mem_filter.mp hl).2)
    (fun l _ p => hSX l p)
    (fun l hl w hw x hx hxU => by
      obtain ⟨_, h, hfr, hlt, rfl⟩ := (hfX l w).mp hw
      exact ZX l (Finset.mem_filter.mp hl).1 h hfr hlt.1 x (le_trans hx hmb)
        (fun p hI => hxU p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩)))
    (fun l _ => min_le_right _ _)
    (fun l hl => by
      have := (Finset.mem_filter.mp hl).2
      have := min_le_left ((SX l).card - 1) m
      omega)
  have hYsum := rsb_or H1 (S.filter (fun p => 2 ≤ (SY p).card)) (N + N) m
    (fun p => (Finset.univ.filter (fun l => I p l)).image (Fin.natAdd N)) SY Dc fY
    (fun p => min ((SY p).card - 1) m) hF hrb
    (fun p _ h hh => ((hfY p h).mp hh).1)
    (fun p _ p' _ hpp => hUY p p' hpp)
    (fun p hp => hSYU p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p _ z => hSY p z)
    (fun p hp h hh zf hzf hzU => by
      obtain ⟨_, hfr, hmt, hVX⟩ := (hfY p h).mp hh
      exact ZY' p (Finset.mem_filter.mp hp).1 h hfr hVX zf (le_trans hzf hma)
        (fun l hI => hzU _ (Finset.mem_image.mpr
          ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩, rfl⟩)))
    (fun p _ => min_le_right _ _)
    (fun p hp => by
      have := (Finset.mem_filter.mp hp).2
      have := min_le_left ((SY p).card - 1) m
      omega)
  have hfXc : ∀ l : Fin N, (fX l).card ≤ (FG.filter
      (fun j => Fr N Dc (N + N + j) ∧ LT N Dc W (N + N + j) l)).card + 1 := by
    intro l
    have sub : fX l ⊆ (insert (N + l.val) ((FG.filter
        (fun j => Fr N Dc (N + N + j) ∧ LT N Dc W (N + N + j) l)).image
          (fun j => N + N + j))).image ph := by
      intro w hw
      obtain ⟨_, h, hfr, hlt, rfl⟩ := (hfX l w).mp hw
      refine Finset.mem_image.mpr ⟨h, ?_, rfl⟩
      rcases frR N Dc h l hfr hlt.1 with e | ⟨e1, e2⟩
      · rw [e]
        exact Finset.mem_insert_self _ _
      · have e3 : N + N + (h - (N + N)) = h := by omega
        refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨h - (N + N), ?_, e3⟩)
        refine Finset.mem_filter.mpr ⟨(hFGm _).mpr ⟨by omega, ?_⟩, ?_⟩
        · rw [e3]
          exact ⟨hfr.1, hfr.2.1⟩
        · rw [e3]
          exact ⟨hfr, hlt⟩
    calc (fX l).card ≤ _ := Finset.card_le_card sub
      _ ≤ (insert (N + l.val) ((FG.filter
        (fun j => Fr N Dc (N + N + j) ∧ LT N Dc W (N + N + j) l)).image
          (fun j => N + N + j))).card := Finset.card_image_le
      _ ≤ ((FG.filter (fun j => Fr N Dc (N + N + j) ∧ LT N Dc W (N + N + j) l)).image
          (fun j => N + N + j)).card + 1 := Finset.card_insert_le _ _
      _ ≤ _ := Nat.add_le_add_right Finset.card_image_le 1
  have hfYc : ∀ p : Fin N, (fY p).card ≤ (FG.filter
      (fun j => Fr N Dc (N + N + j) ∧ MT N Dc W (N + N + j) ∧
        V X (List.ofFn (ep p)) (ph (N + N + j)) = true)).card := by
    intro p
    have sub : fY p ⊆ (FG.filter
        (fun j => Fr N Dc (N + N + j) ∧ MT N Dc W (N + N + j) ∧
          V X (List.ofFn (ep p)) (ph (N + N + j)) = true)).image (fun j => N + N + j) := by
      intro h hh
      obtain ⟨_, hfr, hmt, hVX⟩ := (hfY p h).mp hh
      obtain ⟨e1, e2⟩ := mtR N Dc W h hfr hmt
      have e3 : N + N + (h - (N + N)) = h := by omega
      refine Finset.mem_image.mpr ⟨h - (N + N), ?_, e3⟩
      refine Finset.mem_filter.mpr ⟨(hFGm _).mpr ⟨by omega, ?_⟩, ?_⟩
      · rw [e3]
        exact ⟨hfr.1, hfr.2.1⟩
      · rw [e3]
        exact ⟨hfr, hmt, hVX⟩
    exact le_trans (Finset.card_le_card sub) Finset.card_image_le
  have hdc := dc (W.filter (fun l => 2 ≤ (SX l).card)) (S.filter (fun p => 2 ≤ (SY p).card)) FG
    (fun l j => Fr N Dc (N + N + j) ∧ LT N Dc W (N + N + j) l)
    (fun p j => Fr N Dc (N + N + j) ∧ MT N Dc W (N + N + j) ∧
        V X (List.ofFn (ep p)) (ph (N + N + j)) = true)
    (fun j _ => by
      by_cases hmt : MT N Dc W (N + N + j)
      · have e : (W.filter (fun l => 2 ≤ (SX l).card)).filter
            (fun l => Fr N Dc (N + N + j) ∧ LT N Dc W (N + N + j) l) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun l _ hP => LT_MT_false N Dc W _ l hP.2 hmt)
        rw [e, Finset.card_empty, zero_add, Finset.card_le_one]
        intro p hp p' hp'
        obtain ⟨l1, hl1, l2, hl2, hne, hh1, hh2⟩ := hmt
        have hpS := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        have hQ := (Finset.mem_filter.mp hp).2
        have hpS' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp').1).1
        have hQ' := (Finset.mem_filter.mp hp').2
        rcases two_lines N I huniq p p' l1 l2 (incH p hpS l1 _ hQ.1 hh1 hQ.2.2)
          (incH p' hpS' l1 _ hQ'.1 hh1 hQ'.2.2) (incH p hpS l2 _ hQ.1 hh2 hQ.2.2)
          (incH p' hpS' l2 _ hQ'.1 hh2 hQ'.2.2) with e' | e'
        · exact e'
        · exact absurd e' hne
      · have e : (S.filter (fun p => 2 ≤ (SY p).card)).filter
            (fun p => Fr N Dc (N + N + j) ∧ MT N Dc W (N + N + j) ∧
              V X (List.ofFn (ep p)) (ph (N + N + j)) = true) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun p _ hQ => hmt hQ.2.1)
        rw [e, Finset.card_empty, add_zero, Finset.card_le_one]
        intro l hl l' hl'
        have h1 := (Finset.mem_filter.mp hl).2.2
        have h2 := (Finset.mem_filter.mp hl').2.2
        have hlW := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1
        exact h2.2 l hlW h1.1)
  have hp3 := part3 Dc.gates.length (fun j => DL N Dc (N + N + j) = 0)
    (fun j => 0 < DP N Dc (N + N + j) ∧ 0 < DL N Dc (N + N + j))
    (fun j => DP N Dc (N + N + j) = 0 ∧ 0 < DL N Dc (N + N + j))
    (fun j h1 h2 => by omega) (fun j h1 h2 => by omega) (fun j h1 h2 => by omega)
  rw [← hFG] at hp3
  have hs1 : ∑ l ∈ W.filter (fun l => 2 ≤ (SX l).card), (fX l).card
      ≤ ∑ l ∈ W.filter (fun l => 2 ≤ (SX l).card), (FG.filter
        (fun j => Fr N Dc (N + N + j) ∧ LT N Dc W (N + N + j) l)).card
        + (W.filter (fun l => 2 ≤ (SX l).card)).card := by
    have := Finset.sum_le_sum (s := W.filter (fun l => 2 ≤ (SX l).card))
      (fun l _ => hfXc l)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at this
    exact this
  have hs2 : ∑ p ∈ S.filter (fun p => 2 ≤ (SY p).card), (fY p).card
      ≤ ∑ p ∈ S.filter (fun p => 2 ≤ (SY p).card), (FG.filter
        (fun j => Fr N Dc (N + N + j) ∧ MT N Dc W (N + N + j) ∧
          V X (List.ofFn (ep p)) (ph (N + N + j)) = true)).card :=
    Finset.sum_le_sum (fun p _ => hfYc p)
  have hcX : ∑ l ∈ W.filter (fun l => 2 ≤ (SX l).card), min ((SX l).card - 1) m
      = ∑ l ∈ W, min ((SX l).card - 1) m :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun l hl hnl => by
      have h2 : ¬ 2 ≤ (SX l).card := fun h => hnl (Finset.mem_filter.mpr ⟨hl, h⟩)
      have h0 : (SX l).card - 1 = 0 := by omega
      rw [h0]
      exact Nat.zero_min _)
  have hcY : ∑ p ∈ S.filter (fun p => 2 ≤ (SY p).card), min ((SY p).card - 1) m
      = ∑ p ∈ S, min ((SY p).card - 1) m :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun p hp hnp => by
      have h2 : ¬ 2 ≤ (SY p).card := fun h => hnp (Finset.mem_filter.mpr ⟨hp, h⟩)
      have h0 : (SY p).card - 1 = 0 := by omega
      rw [h0]
      exact Nat.zero_min _)
  rw [hcX] at hXsum
  rw [hcY] at hYsum
  have htot : ∑ l ∈ W, min ((SX l).card - 1) m + ∑ p ∈ S, min ((SY p).card - 1) m
      ≤ 4 * Dc.gates.length := by
    omega
  have hAX : (∑ l ∈ W, (SX l).card) * m ≤ q * ∑ l ∈ W, min ((SX l).card - 1) m
      + W.card * m := by
    rw [Finset.sum_mul, Finset.mul_sum]
    have := Finset.sum_le_sum (s := W) (fun l hl => arith1 (SX l).card q m m
      (by rw [← hline l]; exact Finset.card_le_card (hSXU l hl)) hmq (le_refl m))
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at this
    exact this
  have hAY : (∑ p ∈ S, (SY p).card) * m ≤ q * ∑ p ∈ S, min ((SY p).card - 1) m
      + S.card * m := by
    rw [Finset.sum_mul, Finset.mul_sum]
    have := Finset.sum_le_sum (s := S) (fun p hp => arith1 (SY p).card q m m
      (by
        rw [← lines_through q N I hq hN hline huniq p]
        exact le_trans (Finset.card_le_card (hSYU p hp)) Finset.card_image_le)
      hmq (le_refl m))
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at this
    exact this
  have hsub : (S ×ˢ W).filter (fun pl => I pl.1 pl.2)
      ⊆ (S ×ˢ W).filter (fun pl => pl.1 ∈ SX pl.2)
        ∪ (S ×ˢ W).filter (fun pl => Fin.natAdd N pl.2 ∈ SY pl.1) := by
    rintro ⟨p, l⟩ hpl
    obtain ⟨hpl1, hI⟩ := Finset.mem_filter.mp hpl
    obtain ⟨hp, hl⟩ := Finset.mem_product.mp hpl1
    obtain ⟨h, hfr, hh, hV⟩ := cov p hp l hl hI
    rcases LT_or_MT N Dc W h l hl hh with hlt | hmt
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpl1, ?_⟩)
      exact (hSX l p).mpr ⟨ph h, (hfX l _).mpr ⟨hXin _ _ hV, h, hfr, hlt, rfl⟩, hV⟩
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpl1, ?_⟩)
      refine (hSY p _).mpr ⟨h, (hfY p h).mpr ⟨(mtR N Dc W h hfr hmt).2, hfr, hmt, hV⟩, ?_⟩
      show V Dc (List.ofFn (fun a : Fin (N + N) => decide (a = Fin.natAdd N l))) h = true
      rw [epp_nat N l]
      exact hh
  have hcA : ((S ×ˢ W).filter (fun pl => pl.1 ∈ SX pl.2)).card ≤ ∑ l ∈ W, (SX l).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun pl => (⟨pl.2, pl.1⟩ : (_ : Fin N) × Fin N))
      (fun pl hpl => ?_) (fun pl _ pl' _ hpp => ?_)
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hpl
      exact Finset.mem_sigma.mpr ⟨(Finset.mem_product.mp h1).2, h2⟩
    · have h1 := congrArg Sigma.fst hpp
      have h2 := eq_of_heq (Sigma.mk.inj hpp).2
      exact Prod.ext h2 h1
  have hcB : ((S ×ˢ W).filter (fun pl => Fin.natAdd N pl.2 ∈ SY pl.1)).card
      ≤ ∑ p ∈ S, (SY p).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn
      (fun pl => (⟨pl.1, Fin.natAdd N pl.2⟩ : (_ : Fin N) × Fin (N + N)))
      (fun pl hpl => ?_) (fun pl _ pl' _ hpp => ?_)
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hpl
      exact Finset.mem_sigma.mpr ⟨(Finset.mem_product.mp h1).1, h2⟩
    · have h1 := congrArg Sigma.fst hpp
      have h2 := eq_of_heq (Sigma.mk.inj hpp).2
      exact Prod.ext h1 (natAdd_inj' N _ _ h2)
  have hinc : ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card
      ≤ ∑ l ∈ W, (SX l).card + ∑ p ∈ S, (SY p).card :=
    le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add hcA hcB))
  have h1 := Nat.mul_le_mul_left m hinc
  have h2 := Nat.mul_le_mul_left q htot
  nlinarith [h1, h2, hAX, hAY]

end PEqualNP.Outside.L_meta_1726

theorem PEqualNP.Outside.L_meta_1726 : (∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size) → (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → (∀ (N22 : ℕ) (C22 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g22 ∈ C22.gates, (g22.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N22 + N22) C22 → (∀ j22b < C22.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD i22 0 = 0) ∨ (∀ h22b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22b 0 = 0)) → 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD C22.output 0 → 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD C22.output 0 → ∃ (X22 : PEqualNP.CircuitLowerBounds.Circuit) (ph22 : ℕ → ℕ) (H22 : Set ℕ), ((∀ g22a ∈ X22.gates, (g22a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N22 X22) ∧ X22.size ≤ Set.ncard {j22 : ℕ | j22 < C22.gates.length ∧ (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22) 0 = 0} + 3 * Set.ncard {j22a : ℕ | j22a < C22.gates.length ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22a) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22a) 0} ∧ (∀ h22 ∈ H22, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22 0 ∧ ∃ j22c < C22.gates.length, h22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22c).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22c) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22c) 0)) ∧ ∀ x22 y22 : Fin N22 → Bool, (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 y22) = true ↔ (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 (fun u22 : Fin N22 => false)) = true ∨ ∃ h22a : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22a 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22a 0 ∧ ∃ j22d < C22.gates.length, h22a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22d).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22d) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22d) 0) ∧ (C22.wires (List.ofFn (Fin.append (fun u22a : Fin N22 => false) y22))).getD h22a false = true ∧ (h22a ∈ H22 ∨ (X22.wires (List.ofFn x22)).getD (ph22 h22a) false = true)))) → ∀ (q122 N122 a122 b122 : ℕ) (I122 : Fin N122 → Fin N122 → Prop) [DecidableRel I122] (D122 : PEqualNP.CircuitLowerBounds.Circuit) (S122 W122 : Finset (Fin N122)), 2 ≤ q122 → N122 = q122 ^ 2 + q122 + 1 → (∀ l122d : Fin N122, (Finset.univ.filter (fun p122d => I122 p122d l122d)).card = q122 + 1) → (∀ pa122 pb122 : Fin N122, pa122 ≠ pb122 → ∃! lb122 : Fin N122, I122 pa122 lb122 ∧ I122 pb122 lb122) → (∀ g122 ∈ D122.gates, (g122.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g122.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g122.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N122 + N122) D122 → (∀ j122 < D122.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D122 j122).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i122 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D122 j122).inputs, (D122.lineDegrees (N122 + N122) (Finset.Ico N122 (N122 + N122))).getD i122 0 = 0) ∨ (∀ h122 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D122 j122).inputs, (D122.lineDegrees (N122 + N122) (Finset.range N122)).getD h122 0 = 0)) → 1 ≤ a122 → 1 ≤ b122 → (∀ x122 xa122 y122 ya122 : Fin N122 → Bool, (∀ p122 ∈ S122, x122 p122 = xa122 p122) → (∀ l122 ∈ W122, y122 l122 = ya122 l122) → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append x122 y122) = PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append xa122 ya122)) → (∀ p122a ∈ S122, ∀ l122a ∈ W122, I122 p122a l122a → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append (fun a122a => decide (a122a = p122a)) (fun a122b => decide (a122b = l122a))) = true) → (∀ p122b ∈ S122, ∀ T122 ⊆ W122, (∀ l122b ∈ T122, ¬ I122 p122b l122b) → T122.card ≤ a122 → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append (fun a122c => decide (a122c = p122b)) (fun a122d => decide (a122d ∈ T122))) = false) → (∀ l122c ∈ W122, ∀ X122 ⊆ S122, (∀ p122c ∈ X122, ¬ I122 p122c l122c) → X122.card ≤ b122 → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append (fun a122e => decide (a122e ∈ X122)) (fun a122f => decide (a122f = l122c))) = false) → min (min a122 b122) q122 * ((S122 ×ˢ W122).filter (fun pl122 => I122 pl122.1 pl122.2)).card ≤ 5 * q122 * D122.size + min (min a122 b122) q122 * (S122.card + W122.card) := by
  intro H1 H2 H3 q N a b I instI Dc S W hq hN hline huniq hF hrb hkm ha hb hign hacc hrejP hrejL
  have h2 := (H2 N Dc hF hrb hkm).1
  by_cases hmix : 0 < (Dc.lineDegrees (N + N) (Finset.range N)).getD Dc.output 0 ∧ 0 < (Dc.lineDegrees (N + N) (Finset.Ico N (N + N))).getD Dc.output 0
  · obtain ⟨X, ph, Hs, ⟨hXF, hXrb⟩, hXsize, _, hform⟩ := H3 N Dc hF hrb hkm hmix.1 hmix.2
    have e1 := PEqualNP.Outside.L_meta_1726.ncard_eq Dc.gates.length (fun j => PEqualNP.Outside.L_meta_1726.DL N Dc (N + N + j) = 0)
    have e2 := PEqualNP.Outside.L_meta_1726.ncard_eq Dc.gates.length (fun j => 0 < PEqualNP.Outside.L_meta_1726.DP N Dc (N + N + j) ∧ 0 < PEqualNP.Outside.L_meta_1726.DL N Dc (N + N + j))
    exact PEqualNP.Outside.L_meta_1726.core H1 q N a b I Dc S W hq hN hline huniq hF hrb ha hb hign hacc hrejP hrejL (fun w xa xb ya hd => (h2 w xa xb ya ya).2.1 hd) X ph Hs hXF hXrb (by rw [← e1, ← e2]; exact hXsize) hform
  · have hor : (Dc.lineDegrees (N + N) (Finset.Ico N (N + N))).getD Dc.output 0 = 0 ∨ (Dc.lineDegrees (N + N) (Finset.range N)).getD Dc.output 0 = 0 := by omega
    have hempty := PEqualNP.Outside.L_meta_1726.inc_empty N a b I Dc S W hacc hrejP hrejL (by
      rcases hor with h | h
      · exact Or.inl (fun x y y' => (h2 Dc.output x x y y').1 h)
      · exact Or.inr (fun x x' y => (h2 Dc.output x x' y y).2.1 h))
    rw [hempty]
    simp
