import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1623

def fo {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) : List α :=
  G.foldl (fun w g => w ++ [Φ g (g.inputs.map fun i => w.getD i dflt)]) x

def gv {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) (i : ℕ) : α :=
  (fo dflt Φ G x).getD i dflt

def gd : Gate := ⟨GateOp.or, []⟩

def Φb (g : Gate) (l : List Bool) : Bool := g.op.eval l

def Φd (g : Gate) (l : List ℕ) : ℕ :=
  @ite ℕ (g.op = GateOp.and) (lineDegreeGateOpDecEq g.op GateOp.and) l.sum (l.foldr max 0)

def vl (G : List Gate) (X : List Bool) (i : ℕ) : Bool := gv false Φb G X i

def d0 (n m : ℕ) : List ℕ := (List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0

def dg (n m : ℕ) (G : List Gate) (i : ℕ) : ℕ := gv 0 Φd G (d0 n m) i

def inp {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) : List Bool := List.ofFn (Fin.append x y)

theorem wires_eq (C : Circuit) (X : List Bool) : C.wires X = fo false Φb C.gates X := rfl

theorem deg_eq (C : Circuit) (n m i : ℕ) :
    (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = dg n m C.gates i := rfl

def St (n m : ℕ) (G : List Gate) : Prop :=
  (∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < G.length, ∀ i ∈ (G.getD j gd).inputs, i < n + m + j) ∧
  (∀ j < G.length, (G.getD j gd).op = GateOp.and → (G.getD j gd).inputs.length = 2 →
    ∃ i ∈ (G.getD j gd).inputs, dg n m G i = 0)

def AZ (n m : ℕ) (G : List Gate) : Prop := ∀ j < G.length, dg n m G (n + m + j) = 0

def PX (n m : ℕ) (G : List Gate) : Prop := St n m G ∧ AZ n m G

def Ex (G G' : List Gate) (c : ℕ) : Prop := (∃ E, G' = G ++ E) ∧ G'.length ≤ G.length + c

def Cm {n m : ℕ} (G : List Gate) (w : ℕ) (f : (Fin n → Bool) → (Fin m → Bool) → Bool) : Prop :=
  w < n + m + G.length ∧ ∀ x y, vl G (inp x y) w = f x y

def XC (n m : ℕ) (G : List Gate) (w : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  (w < n ∨ n + m ≤ w) ∧ Cm (n := n) (m := m) G w (fun x _ => f x)

def vC (C : Circuit) {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) : Bool :=
  vl C.gates (inp x y) w

def dC (n m : ℕ) (C : Circuit) (i : ℕ) : ℕ := dg n m C.gates i

def RB (n m : ℕ) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j gd).inputs, i < n + m + j

def M2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def cross (n m : ℕ) (C : Circuit) (u : ℕ) : Prop :=
  (C.gates.getD u gd).op = GateOp.and ∧ (C.gates.getD u gd).inputs.length = 2 ∧
    ∀ i ∈ (C.gates.getD u gd).inputs, 0 < dC n m C i

def env (C : Circuit) {n m : ℕ} (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool) : Bool :=
  vC C x (fun _ : Fin m => false) w ||
    decide (∃ j : Fin m, y j = true ∧ vC C x (fun l : Fin m => decide (l = j)) w = true)

theorem hA_fo_append {α : Type} (dflt : α) (Φ : Gate → List α → α) (G1 G2 : List Gate) (x : List α) :
    fo dflt Φ (G1 ++ G2) x = fo dflt Φ G2 (fo dflt Φ G1 x) := by
  unfold fo
  rw [List.foldl_append]

theorem hA_fo_pre {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) :
    ∀ x : List α, ∃ t, fo dflt Φ G x = x ++ t ∧ t.length = G.length := by
  induction G with
  | nil => intro x; exact ⟨[], by simp [fo], rfl⟩
  | cons g G ih =>
    intro x
    obtain ⟨t, ht, hl⟩ := ih (x ++ [Φ g (g.inputs.map fun i => x.getD i dflt)])
    refine ⟨Φ g (g.inputs.map fun i => x.getD i dflt) :: t, ?_, by simp [hl]⟩
    show fo dflt Φ G (x ++ [Φ g (g.inputs.map fun i => x.getD i dflt)]) = _
    rw [ht]
    simp

theorem hA_fo_len {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) :
    (fo dflt Φ G x).length = x.length + G.length := by
  obtain ⟨t, ht, hl⟩ := hA_fo_pre dflt Φ G x
  rw [ht, List.length_append, hl]

theorem gv_stable {α : Type} (dflt : α) (Φ : Gate → List α → α) (G1 G2 : List Gate) (x : List α) (i : ℕ)
    (h : i < x.length + G1.length) : gv dflt Φ (G1 ++ G2) x i = gv dflt Φ G1 x i := by
  have hl := hA_fo_len dflt Φ G1 x
  obtain ⟨t, ht, _⟩ := hA_fo_pre dflt Φ G2 (fo dflt Φ G1 x)
  show (fo dflt Φ (G1 ++ G2) x).getD i dflt = (fo dflt Φ G1 x).getD i dflt
  rw [hA_fo_append, ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega)]

theorem gv_input {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) (i : ℕ)
    (h : i < x.length) : gv dflt Φ G x i = x.getD i dflt := by
  obtain ⟨t, ht, _⟩ := hA_fo_pre dflt Φ G x
  show (fo dflt Φ G x).getD i dflt = x.getD i dflt
  rw [ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gv_oob {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) (i : ℕ)
    (h : x.length + G.length ≤ i) : gv dflt Φ G x i = dflt := by
  have hl := hA_fo_len dflt Φ G x
  show (fo dflt Φ G x).getD i dflt = dflt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem gv_snoc {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (g : Gate) (x : List α) :
    gv dflt Φ (G ++ [g]) x (x.length + G.length) = Φ g (g.inputs.map (gv dflt Φ G x)) := by
  have hl := hA_fo_len dflt Φ G x
  show (fo dflt Φ (G ++ [g]) x).getD (x.length + G.length) dflt =
    Φ g (g.inputs.map fun i => (fo dflt Φ G x).getD i dflt)
  rw [hA_fo_append]
  show ((fo dflt Φ G x) ++ [Φ g (g.inputs.map fun i => (fo dflt Φ G x).getD i dflt)]).getD
    (x.length + G.length) dflt = _
  rw [← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem gv_gate {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α)
    (hrb : ∀ j < G.length, ∀ i ∈ (G.getD j gd).inputs, i < x.length + j) (j : ℕ) (hj : j < G.length) :
    gv dflt Φ G x (x.length + j) = Φ (G.getD j gd) ((G.getD j gd).inputs.map (gv dflt Φ G x)) := by
  have hsplit : (G.take j ++ [G.getD j gd]) ++ G.drop (j + 1) = G := by
    have hg : G.getD j gd = G[j] := by simp [List.getD_eq_getElem?_getD, hj]
    rw [hg]
    simp
  have hlen : (G.take j).length = j := by
    rw [List.length_take]
    omega
  have h1 : gv dflt Φ ((G.take j ++ [G.getD j gd]) ++ G.drop (j + 1)) x (x.length + j) =
      gv dflt Φ (G.take j ++ [G.getD j gd]) x (x.length + j) :=
    gv_stable dflt Φ _ _ x _ (by rw [List.length_append, hlen, List.length_singleton]; omega)
  rw [hsplit] at h1
  have h2 := gv_snoc dflt Φ (G.take j) (G.getD j gd) x
  rw [hlen] at h2
  rw [h1, h2]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h3 := gv_stable dflt Φ (G.take j) (G.drop j) x i (by rw [hlen]; exact hrb j hj i hi)
  rw [List.take_append_drop] at h3
  exact h3.symm

theorem inp_len {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) : (inp x y).length = n + m := by
  simp [inp]

theorem inp_left {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ) (h : i < n) :
    (inp x y).getD i false = x ⟨i, h⟩ := by
  unfold inp
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (by omega : i < n + m)]
  exact Fin.append_left x y ⟨i, h⟩

theorem inp_right {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m) :
    (inp x y).getD (n + j.val) false = y j := by
  unfold inp
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (by omega : n + j.val < n + m)]
  exact Fin.append_right x y j

theorem d0_len (n m : ℕ) : (d0 n m).length = n + m := by
  simp [d0]

theorem d0_left (n m i : ℕ) (h : i < n) : (d0 n m).getD i 0 = 0 := by
  unfold d0
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp
  omega

theorem d0_right (n m i : ℕ) (h : n ≤ i) (h2 : i < n + m) : (d0 n m).getD i 0 = 1 := by
  unfold d0
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp
  exact ⟨h, h2⟩

theorem Ex_refl (G : List Gate) : Ex G G 0 := ⟨⟨[], by simp⟩, le_refl _⟩

theorem Ex_trans {G G' G'' : List Gate} {c c' : ℕ} (h1 : Ex G G' c) (h2 : Ex G' G'' c') :
    Ex G G'' (c + c') := by
  obtain ⟨⟨E1, rfl⟩, hl1⟩ := h1
  obtain ⟨⟨E2, rfl⟩, hl2⟩ := h2
  exact ⟨⟨E1 ++ E2, by simp⟩, by omega⟩

theorem Ex_mono {G G' : List Gate} {c c' : ℕ} (h1 : Ex G G' c) (h : c ≤ c') : Ex G G' c' :=
  ⟨h1.1, by have := h1.2; omega⟩

theorem Ex_len {G G' : List Gate} {c : ℕ} (h1 : Ex G G' c) : G.length ≤ G'.length := by
  obtain ⟨⟨E, rfl⟩, _⟩ := h1
  simp

theorem Cm_ex {n m : ℕ} {G G' : List Gate} {c w : ℕ} {f : (Fin n → Bool) → (Fin m → Bool) → Bool}
    (h : Cm G w f) (he : Ex G G' c) : Cm G' w f := by
  obtain ⟨⟨E, rfl⟩, _⟩ := he
  refine ⟨by have := h.1; rw [List.length_append]; omega, fun x y => ?_⟩
  rw [← h.2 x y]
  exact gv_stable false Φb G E (inp x y) w (by rw [inp_len]; exact h.1)

theorem XC_ex {n m : ℕ} {G G' : List Gate} {c w : ℕ} {f : (Fin n → Bool) → Bool}
    (h : XC n m G w f) (he : Ex G G' c) : XC n m G' w f :=
  ⟨h.1, Cm_ex h.2 he⟩

theorem dg_ex {n m : ℕ} {G G' : List Gate} {c i : ℕ} (he : Ex G G' c) (h : i < n + m + G.length) :
    dg n m G' i = dg n m G i := by
  obtain ⟨⟨E, rfl⟩, _⟩ := he
  exact gv_stable 0 Φd G E (d0 n m) i (by rw [d0_len]; exact h)

theorem xw_dg {n m : ℕ} {G : List Gate} {w : ℕ} (hA : AZ n m G) (h1 : w < n ∨ n + m ≤ w)
    (h2 : w < n + m + G.length) : dg n m G w = 0 := by
  rcases h1 with h1 | h1
  · show gv 0 Φd G (d0 n m) w = 0
    rw [gv_input 0 Φd G (d0 n m) w (by rw [d0_len]; omega), d0_left n m w h1]
  · have h3 := hA (w - (n + m)) (by omega)
    rwa [show n + m + (w - (n + m)) = w by omega] at h3

theorem hA_getD_lt (G : List Gate) (g : Gate) (j : ℕ) (h : j < G.length) :
    (G ++ [g]).getD j gd = G.getD j gd := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem hA_getD_eq (G : List Gate) (g : Gate) : (G ++ [g]).getD G.length gd = g := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem hA_dg_stable {n m : ℕ} {G : List Gate} (E : List Gate) {i : ℕ} (h : i < n + m + G.length) :
    dg n m (G ++ E) i = dg n m G i :=
  gv_stable 0 Φd G E (d0 n m) i (by rw [d0_len]; exact h)

theorem hA_Φd_zero (g : Gate) (l : List ℕ) (h : ∀ a ∈ l, a = 0) : Φd g l = 0 := by
  have h2 : l.foldr max 0 = 0 := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      have ha : a = 0 := h a (by simp)
      have hr := ih (fun b hb => h b (by simp [hb]))
      simp [List.foldr_cons, ha, hr]
  have h1 : l.sum = 0 := List.sum_eq_zero h
  unfold Φd
  split_ifs
  · exact h1
  · exact h2

theorem push2 {n m : ℕ} {G : List Gate} (hS : St n m G) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < n + m + G.length)
    (hand : g.op = GateOp.and → g.inputs.length = 2 → ∃ i ∈ g.inputs, dg n m G i = 0) :
    St n m (G ++ [g]) ∧
    (∀ X : List Bool, X.length = n + m →
      vl (G ++ [g]) X (n + m + G.length) = g.op.eval (g.inputs.map (vl G X))) ∧
    ((∀ i ∈ g.inputs, dg n m G i = 0) → dg n m (G ++ [g]) (n + m + G.length) = 0) := by
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with hg' | hg'
    · exact h1 g' hg'
    · rw [List.mem_singleton] at hg'
      subst hg'
      exact ⟨hop, hlen⟩
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    by_cases hj' : j < G.length
    · rw [hA_getD_lt G g j hj'] at hi
      exact h2 j hj' i hi
    · have hje : j = G.length := by omega
      subst hje
      rw [hA_getD_eq] at hi
      exact hin i hi
  · intro j hj ha hl
    rw [List.length_append, List.length_singleton] at hj
    by_cases hj' : j < G.length
    · rw [hA_getD_lt G g j hj'] at ha hl ⊢
      obtain ⟨i, hi, hd⟩ := h3 j hj' ha hl
      refine ⟨i, hi, ?_⟩
      rw [hA_dg_stable [g] (by have := h2 j hj' i hi; omega)]
      exact hd
    · have hje : j = G.length := by omega
      subst hje
      rw [hA_getD_eq] at ha hl ⊢
      obtain ⟨i, hi, hd⟩ := hand ha hl
      refine ⟨i, hi, ?_⟩
      rw [hA_dg_stable [g] (hin i hi)]
      exact hd
  · intro X hX
    have h4 := gv_snoc false Φb G g X
    rw [hX] at h4
    exact h4
  · intro hz
    have h4 := gv_snoc 0 Φd G g (d0 n m)
    rw [d0_len] at h4
    show gv 0 Φd (G ++ [g]) (d0 n m) (n + m + G.length) = 0
    rw [h4]
    apply hA_Φd_zero
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    exact hz i hi

theorem L_gate {n m : ℕ} {G : List Gate} (hP : PX n m G) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (is : List ℕ) (hlen : is.length ≤ 2) (ρ : ℕ → ℕ)
    (fs : ℕ → (Fin n → Bool) → Bool) (h : ∀ i ∈ is, XC n m G (ρ i) (fs i)) :
    ∃ G' w, Ex G G' 1 ∧ PX n m G' ∧ XC n m G' w (fun x => op.eval (is.map fun i => fs i x)) := by
  obtain ⟨hS, hA⟩ := hP
  have hz : ∀ i ∈ is.map ρ, dg n m G i = 0 := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hi
    exact xw_dg hA (h a ha).1 (h a ha).2.1
  have hin : ∀ i ∈ is.map ρ, i < n + m + G.length := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hi
    exact (h a ha).2.1
  have hlen' : (is.map ρ).length ≤ 2 := by rw [List.length_map]; exact hlen
  obtain ⟨hS', hv, hd⟩ := push2 hS ⟨op, is.map ρ⟩ hop hlen' hin (fun _ h2 => by
    obtain ⟨i, hi⟩ := List.exists_mem_of_length_pos (by rw [h2]; norm_num : 0 < (is.map ρ).length)
    exact ⟨i, hi, hz i hi⟩)
  refine ⟨G ++ [⟨op, is.map ρ⟩], n + m + G.length, ⟨⟨[⟨op, is.map ρ⟩], rfl⟩, by simp⟩, ⟨hS', ?_⟩, ?_⟩
  · intro j hj
    rw [List.length_append, List.length_singleton] at hj
    by_cases hj' : j < G.length
    · rw [hA_dg_stable _ (by omega)]
      exact hA j hj'
    · have hje : j = G.length := by omega
      subst hje
      exact hd hz
  · refine ⟨Or.inr (by omega), by rw [List.length_append, List.length_singleton]; omega, fun x y => ?_⟩
    rw [hv (inp x y) (inp_len x y)]
    show op.eval ((is.map ρ).map (vl G (inp x y))) = op.eval (is.map fun i => fs i x)
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact (h a ha).2.2 x y

theorem hB_and (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  show (l.map f).all id = true ↔ _
  simp [List.all_eq_true]

theorem hB_or (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  show (l.map f).any id = true ↔ _
  simp [List.any_eq_true]

theorem hB_mem (C : Circuit) (u : ℕ) (hu : u < C.gates.length) : C.gates.getD u gd ∈ C.gates := by
  rw [List.getD_eq_getElem _ _ hu]
  exact List.getElem_mem hu

theorem hB_sum0 (l : List ℕ) : l.sum = 0 → ∀ a ∈ l, a = 0 := by
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons b t ih =>
    intro h a ha
    rw [List.sum_cons] at h
    rcases List.mem_cons.mp ha with hab | ha
    · omega
    · exact ih (by omega) a ha

theorem hB_max0 (l : List ℕ) : l.foldr max 0 = 0 → ∀ a ∈ l, a = 0 := by
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons b t ih =>
    intro h a ha
    rw [List.foldr_cons] at h
    have h1 : b = 0 := by
      have := le_max_left b (t.foldr max 0)
      omega
    have h2 : t.foldr max 0 = 0 := by
      have := le_max_right b (t.foldr max 0)
      omega
    rcases List.mem_cons.mp ha with hab | ha
    · omega
    · exact ih h2 a ha

theorem vC_gate {n m : ℕ} {C : Circuit} (hrb : RB n m C) (u : ℕ) (hu : u < C.gates.length)
    (x : Fin n → Bool) (y : Fin m → Bool) :
    vC C x y (n + m + u) = (C.gates.getD u gd).op.eval ((C.gates.getD u gd).inputs.map (vC C x y)) := by
  have h := gv_gate false Φb C.gates (inp x y) (by rw [inp_len]; exact hrb) u hu
  rw [inp_len] at h
  exact h

theorem vC_left {n m : ℕ} (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n) :
    vC C x y w = x ⟨w, h⟩ := by
  show gv false Φb C.gates (inp x y) w = _
  rw [gv_input false Φb C.gates (inp x y) w (by rw [inp_len]; omega), inp_left x y w h]

theorem vC_right {n m : ℕ} (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m) :
    vC C x y (n + j.val) = y j := by
  have hj := j.isLt
  show gv false Φb C.gates (inp x y) (n + j.val) = _
  rw [gv_input false Φb C.gates (inp x y) (n + j.val) (by rw [inp_len]; omega), inp_right x y j]

theorem vC_oob {n m : ℕ} (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ)
    (h : n + m + C.gates.length ≤ w) : vC C x y w = false :=
  gv_oob false Φb C.gates (inp x y) w (by rw [inp_len]; exact h)

theorem hB_mid {n m : ℕ} (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ)
    (h1 : n ≤ w) (h2 : w < n + m) : vC C x y w = y ⟨w - n, by omega⟩ := by
  have e : vC C x y w = vC C x y (n + (⟨w - n, by omega⟩ : Fin m).val) :=
    congrArg (vC C x y) (show w = n + (w - n) by omega)
  rw [e, vC_right]

theorem vC_mono {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (x : Fin n → Bool)
    (y y' : Fin m → Bool) (h : ∀ j, y j = true → y' j = true) (w : ℕ) :
    vC C x y w = true → vC C x y' w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [vC_left C x y' w h1]
      rw [vC_left C x y w h1] at hw
      exact hw
    · by_cases h2 : w < n + m
      · rw [hB_mid C x y w (by omega) h2] at hw
        rw [hB_mid C x y' w (by omega) h2]
        exact h _ hw
      · by_cases h3 : w < n + m + C.gates.length
        · obtain ⟨u, rfl⟩ : ∃ u, w = n + m + u := ⟨w - (n + m), by omega⟩
          have hu : u < C.gates.length := by omega
          rw [vC_gate hrb u hu] at hw ⊢
          have hin := hrb u hu
          rcases (hM _ (hB_mem C u hu)).1 with ho | ho
          · rw [ho] at hw ⊢
            rw [hB_and] at hw ⊢
            intro i hi
            exact ih i (hin i hi) (hw i hi)
          · rw [ho] at hw ⊢
            rw [hB_or] at hw ⊢
            obtain ⟨i, hi, hv⟩ := hw
            exact ⟨i, hi, ih i (hin i hi) hv⟩
        · rw [vC_oob C x y w (by omega)] at hw
          cases hw

theorem dC_left (n m : ℕ) (C : Circuit) (w : ℕ) (h : w < n) : dC n m C w = 0 := by
  show gv 0 Φd C.gates (d0 n m) w = 0
  rw [gv_input 0 Φd C.gates (d0 n m) w (by rw [d0_len]; omega), d0_left n m w h]

theorem hB_dgate {n m : ℕ} {C : Circuit} (hrb : RB n m C) (u : ℕ) (hu : u < C.gates.length) :
    dC n m C (n + m + u) =
      Φd (C.gates.getD u gd) ((C.gates.getD u gd).inputs.map (dC n m C)) := by
  have h := gv_gate 0 Φd C.gates (d0 n m) (by rw [d0_len]; exact hrb) u hu
  rw [d0_len] at h
  exact h

theorem dC_zero {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (u : ℕ)
    (hu : u < C.gates.length) (h : dC n m C (n + m + u) = 0) :
    ∀ i ∈ (C.gates.getD u gd).inputs, dC n m C i = 0 := by
  rw [hB_dgate hrb u hu] at h
  intro i hi
  have hmem : dC n m C i ∈ (C.gates.getD u gd).inputs.map (dC n m C) :=
    List.mem_map.mpr ⟨i, hi, rfl⟩
  rcases (hM _ (hB_mem C u hu)).1 with ho | ho
  · unfold Φd at h
    rw [if_pos ho] at h
    exact hB_sum0 _ h _ hmem
  · unfold Φd at h
    rw [if_neg (by rw [ho]; intro hh; cases hh)] at h
    exact hB_max0 _ h _ hmem

theorem dC_cross {n m : ℕ} {C : Circuit} (hrb : RB n m C) (u : ℕ)
    (hu : u < C.gates.length) (h : cross n m C u) : 0 < dC n m C (n + m + u) := by
  obtain ⟨ho, hl, hp⟩ := h
  rw [hB_dgate hrb u hu]
  unfold Φd
  rw [if_pos ho]
  by_contra hne
  have hs : ((C.gates.getD u gd).inputs.map (dC n m C)).sum = 0 := by omega
  have hall := hB_sum0 _ hs
  cases hI : (C.gates.getD u gd).inputs with
  | nil => rw [hI] at hl; simp at hl
  | cons a t =>
    have ha : a ∈ (C.gates.getD u gd).inputs := by rw [hI]; simp
    have h1 := hp a ha
    have h2 := hall _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
    omega

theorem vC_dz {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (w : ℕ) (h : dC n m C w = 0)
    (x : Fin n → Bool) (y y' : Fin m → Bool) : vC C x y w = vC C x y' w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < n
    · rw [vC_left C x y w h1, vC_left C x y' w h1]
    · by_cases h2 : w < n + m
      · exfalso
        have h5 : dC n m C w = 1 := by
          show gv 0 Φd C.gates (d0 n m) w = 1
          rw [gv_input 0 Φd C.gates (d0 n m) w (by rw [d0_len]; exact h2),
            d0_right n m w (by omega) h2]
        omega
      · by_cases h3 : w < n + m + C.gates.length
        · obtain ⟨u, rfl⟩ : ∃ u, w = n + m + u := ⟨w - (n + m), by omega⟩
          have hu : u < C.gates.length := by omega
          have hz := dC_zero hM hrb u hu h
          rw [vC_gate hrb u hu, vC_gate hrb u hu]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact ih i (hrb u hu i hi) (hz i hi)
        · rw [vC_oob C x y w (by omega), vC_oob C x y' w (by omega)]

theorem hB_env_iff {n m : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool) :
    env C w x y = true ↔ (vC C x (fun _ : Fin m => false) w = true ∨
      ∃ j : Fin m, y j = true ∧ vC C x (fun l : Fin m => decide (l = j)) w = true) := by
  unfold env
  simp only [Bool.or_eq_true, decide_eq_true_eq]

theorem env_left {n m : ℕ} (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n) :
    env C w x y = x ⟨w, h⟩ := by
  rw [Bool.eq_iff_iff, hB_env_iff]
  have e0 := vC_left C x (fun _ : Fin m => false) w h
  have e1 := fun j : Fin m => vC_left C x (fun l : Fin m => decide (l = j)) w h
  constructor
  · rintro (h0 | ⟨j, _, h1⟩)
    · rw [← e0]; exact h0
    · rw [← e1 j]; exact h1
  · intro hx
    left
    rw [e0]; exact hx

theorem env_right {n m : ℕ} (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m) :
    env C (n + j.val) x y = y j := by
  rw [Bool.eq_iff_iff, hB_env_iff]
  have e0 := vC_right C x (fun _ : Fin m => false) j
  have e1 := fun j' : Fin m => vC_right C x (fun l : Fin m => decide (l = j')) j
  constructor
  · rintro (h0 | ⟨j', hj', h1⟩)
    · rw [e0] at h0; cases h0
    · rw [e1 j'] at h1
      have he : j = j' := of_decide_eq_true h1
      subst he
      exact hj'
  · intro hy
    right
    refine ⟨j, hy, ?_⟩
    rw [e1 j]
    exact decide_eq_true rfl

theorem env_oob {n m : ℕ} (C : Circuit) (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ)
    (h : n + m + C.gates.length ≤ w) : env C w x y = false := by
  rw [Bool.eq_false_iff]
  intro hc
  rw [hB_env_iff] at hc
  rcases hc with h0 | ⟨j, _, h1⟩
  · rw [vC_oob C x _ w h] at h0; cases h0
  · rw [vC_oob C x _ w h] at h1; cases h1

theorem hB_all {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (d : ℕ) (hz : dC n m C d = 0)
    (x : Fin n → Bool) (y : Fin m → Bool) (he : env C d x y = true) :
    ∀ y' : Fin m → Bool, vC C x y' d = true := by
  intro y'
  rcases (hB_env_iff C d x y).mp he with h | ⟨j, _, h⟩
  · exact (vC_dz hM hrb d hz x y' _).trans h
  · exact (vC_dz hM hrb d hz x y' _).trans h

theorem env_gate {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (u : ℕ)
    (hu : u < C.gates.length) (hnc : ¬ cross n m C u) (x : Fin n → Bool) (y : Fin m → Bool) :
    (C.gates.getD u gd).op.eval ((C.gates.getD u gd).inputs.map (fun i => env C i x y)) =
      env C (n + m + u) x y := by
  have hg := hM _ (hB_mem C u hu)
  have e0 := vC_gate hrb u hu x (fun _ : Fin m => false)
  have e1 := fun j : Fin m => vC_gate hrb u hu x (fun l : Fin m => decide (l = j))
  have hnc' : ¬ ((C.gates.getD u gd).op = GateOp.and ∧ (C.gates.getD u gd).inputs.length = 2 ∧
      ∀ i ∈ (C.gates.getD u gd).inputs, 0 < dC n m C i) := hnc
  rw [Bool.eq_iff_iff, hB_env_iff, e0]
  simp only [e1]
  clear e0 e1 hnc
  generalize C.gates.getD u gd = g at hg hnc' ⊢
  obtain ⟨op, is⟩ := g
  dsimp only at hg hnc' ⊢
  rcases hg.1 with ho | ho
  · subst ho
    simp only [hB_and]
    constructor
    · intro hall
      rcases is with _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩
      · left
        intro i hi
        cases hi
      · rcases (hB_env_iff C c x y).mp (hall c (by simp)) with h | ⟨j, hj, h⟩
        · left
          intro i hi
          rw [List.mem_singleton] at hi
          subst hi
          exact h
        · right
          refine ⟨j, hj, ?_⟩
          intro i hi
          rw [List.mem_singleton] at hi
          subst hi
          exact h
      · have hz : dC n m C c = 0 ∨ dC n m C d = 0 := by
          by_contra hcon
          push_neg at hcon
          apply hnc'
          refine ⟨rfl, rfl, ?_⟩
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with hi | hi
          · subst hi; omega
          · subst hi; omega
        have hc := hall c (by simp)
        have hd := hall d (by simp)
        rcases hz with hz | hz
        · have A := hB_all hM hrb c hz x y hc
          rcases (hB_env_iff C d x y).mp hd with h | ⟨j, hj, h⟩
          · left
            intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with hi | hi
            · subst hi; exact A _
            · subst hi; exact h
          · right
            refine ⟨j, hj, ?_⟩
            intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with hi | hi
            · subst hi; exact A _
            · subst hi; exact h
        · have A := hB_all hM hrb d hz x y hd
          rcases (hB_env_iff C c x y).mp hc with h | ⟨j, hj, h⟩
          · left
            intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with hi | hi
            · subst hi; exact h
            · subst hi; exact A _
          · right
            refine ⟨j, hj, ?_⟩
            intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with hi | hi
            · subst hi; exact h
            · subst hi; exact A _
      · exfalso
        have h2 := hg.2
        simp only [List.length_cons] at h2
        omega
    · rintro (h0 | ⟨j, hj, h1⟩) i hi
      · exact (hB_env_iff C i x y).mpr (Or.inl (h0 i hi))
      · exact (hB_env_iff C i x y).mpr (Or.inr ⟨j, hj, h1 i hi⟩)
  · subst ho
    simp only [hB_or]
    constructor
    · rintro ⟨i, hi, he⟩
      rcases (hB_env_iff C i x y).mp he with h | ⟨j, hj, h⟩
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr ⟨j, hj, i, hi, h⟩
    · rintro (⟨i, hi, h⟩ | ⟨j, hj, i, hi, h⟩)
      · exact ⟨i, hi, (hB_env_iff C i x y).mpr (Or.inl h)⟩
      · exact ⟨i, hi, (hB_env_iff C i x y).mpr (Or.inr ⟨j, hj, h⟩)⟩

theorem hC_xc {n m : ℕ} {G : List Gate} {w : ℕ} {f f' : (Fin n → Bool) → Bool}
    (h : XC n m G w f) (e : ∀ x, f x = f' x) : XC n m G w f' := by
  have hff : f = f' := funext e
  rw [← hff]
  exact h

theorem hC_or2 {n m : ℕ} {G : List Gate} (hP : PX n m G) {a b : ℕ} {f h : (Fin n → Bool) → Bool}
    (ha : XC n m G a f) (hb : XC n m G b h) :
    ∃ G' w, Ex G G' 1 ∧ PX n m G' ∧ XC n m G' w (fun x => f x || h x) := by
  obtain ⟨G', w, hE, hP', hw⟩ := L_gate hP GateOp.or (Or.inr rfl) [0, 1] (by simp)
    (fun i => if i = 0 then a else b) (fun i => if i = 0 then f else h)
    (by
      intro i hi
      simp at hi
      rcases hi with rfl | rfl
      · simpa using ha
      · simpa using hb)
  exact ⟨G', w, hE, hP', hC_xc hw (by intro x; simp [GateOp.eval])⟩

theorem hC_and2 {n m : ℕ} {G : List Gate} (hP : PX n m G) {a b : ℕ} {f h : (Fin n → Bool) → Bool}
    (ha : XC n m G a f) (hb : XC n m G b h) :
    ∃ G' w, Ex G G' 1 ∧ PX n m G' ∧ XC n m G' w (fun x => f x && h x) := by
  obtain ⟨G', w, hE, hP', hw⟩ := L_gate hP GateOp.and (Or.inl rfl) [0, 1] (by simp)
    (fun i => if i = 0 then a else b) (fun i => if i = 0 then f else h)
    (by
      intro i hi
      simp at hi
      rcases hi with rfl | rfl
      · simpa using ha
      · simpa using hb)
  exact ⟨G', w, hE, hP', hC_xc hw (by intro x; simp [GateOp.eval])⟩

theorem hC_const {n m : ℕ} {G : List Gate} (hP : PX n m G) (b : Bool) :
    ∃ G' w, Ex G G' 1 ∧ PX n m G' ∧ XC n m G' w (fun _ => b) := by
  cases b
  · obtain ⟨G', w, hE, hP', hw⟩ := L_gate hP GateOp.or (Or.inr rfl) [] (by simp)
      (fun i => i) (fun _ _ => false) (by intro i hi; simp at hi)
    exact ⟨G', w, hE, hP', hC_xc hw (by intro x; simp [GateOp.eval])⟩
  · obtain ⟨G', w, hE, hP', hw⟩ := L_gate hP GateOp.and (Or.inl rfl) [] (by simp)
      (fun i => i) (fun _ _ => false) (by intro i hi; simp at hi)
    exact ⟨G', w, hE, hP', hC_xc hw (by intro x; simp [GateOp.eval])⟩

theorem hC_acc {n m : ℕ} {C : Circuit} {t : ℕ} {G : List Gate} (hP : PX n m G)
    {R : ℕ → ℕ} {r : ℕ → (Fin n → Bool) → Bool}
    (hS1 : ∀ w, XC n m G (R w) (r w))
    (hS2 : ∀ (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool), r w x = true → vC C x y w = true → vC C x y t = true)
    (κ : ℕ) (kf : (Fin n → Bool) → Bool) (hκ : XC n m G κ kf) (c : ℕ)
    (hk : ∀ (x : Fin n → Bool) (y : Fin m → Bool), kf x = true → vC C x y c = true → vC C x y t = true) :
    ∃ (G' : List Gate) (R' : ℕ → ℕ) (r' : ℕ → (Fin n → Bool) → Bool),
      Ex G G' 1 ∧ PX n m G' ∧ (∀ w, XC n m G' (R' w) (r' w)) ∧
      (∀ (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool), r' w x = true → vC C x y w = true → vC C x y t = true) ∧
      (∀ w x, r w x = true → r' w x = true) ∧ (∀ x, kf x = true → r' c x = true) := by
  obtain ⟨G', w, hE, hP', hw⟩ := hC_or2 hP (hS1 c) hκ
  refine ⟨G', fun w' => if w' = c then w else R w',
    fun w' => if w' = c then (fun x => r c x || kf x) else r w', hE, hP', ?_, ?_, ?_, ?_⟩
  · intro w'
    by_cases h : w' = c
    · simp only [if_pos h]
      exact hw
    · simp only [if_neg h]
      exact XC_ex (hS1 w') hE
  · intro w' x y h1 h2
    by_cases h : w' = c
    · simp only [if_pos h] at h1
      rw [Bool.or_eq_true] at h1
      rw [h] at h2
      rcases h1 with h1 | h1
      · exact hS2 _ x y h1 h2
      · exact hk x y h1 h2
    · simp only [if_neg h] at h1
      exact hS2 w' x y h1 h2
  · intro w' x h1
    by_cases h : w' = c
    · simp only [if_pos h]
      rw [h] at h1
      rw [h1]
      rfl
    · simp only [if_neg h]
      exact h1
  · intro x h1
    simp only [if_true]
    rw [h1]
    simp

theorem hC_andstep {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) {t : ℕ} (G : List Gate)
    (hP : PX n m G) (c0 : ℕ → ℕ)
    (hc0 : ∀ w < n + m + C.gates.length,
      XC n m G (c0 w) (fun x => vC C x (fun _ : Fin m => false) w))
    (R : ℕ → ℕ) (r : ℕ → (Fin n → Bool) → Bool)
    (hS1 : ∀ w, XC n m G (R w) (r w))
    (hS2 : ∀ (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool), r w x = true → vC C x y w = true → vC C x y t = true)
    (u : ℕ) (hu : u < C.gates.length) (p s : ℕ) (hp : p < n + m + u) (hs : s < n + m + u)
    (hsz : dC n m C s = 0)
    (e : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      vC C x y (n + m + u) = true ↔ (vC C x y p = true ∧ vC C x y s = true)) :
    ∃ (G' : List Gate) (R' : ℕ → ℕ) (r' : ℕ → (Fin n → Bool) → Bool),
      Ex G G' 2 ∧ PX n m G' ∧ (∀ w, XC n m G' (R' w) (r' w)) ∧
      (∀ (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool), r' w x = true → vC C x y w = true → vC C x y t = true) ∧
      (∀ w x, r w x = true → r' w x = true) ∧
      (∀ (x : Fin n → Bool) (y : Fin m → Bool), r (n + m + u) x = true → vC C x y (n + m + u) = true →
        vC C x (fun _ : Fin m => false) (n + m + u) = false →
        ∃ w, w < n + m + u ∧ r' w x = true ∧ vC C x y w = true ∧
          vC C x (fun _ : Fin m => false) w = false) := by
  obtain ⟨G1, κ, hE1, hP1, hκ⟩ := hC_and2 hP (hS1 (n + m + u)) (hc0 s (by omega))
  obtain ⟨G2, R', r', hE2, hP2, hS1', hS2', hmono, hkc⟩ :=
    hC_acc (C := C) (t := t) hP1 (fun w => XC_ex (hS1 w) hE1) hS2 κ _ hκ p
      (by
        intro x y hk hvp
        rw [Bool.and_eq_true] at hk
        apply hS2 (n + m + u) x y hk.1
        rw [e]
        refine ⟨hvp, vC_mono hM hrb x _ y ?_ s hk.2⟩
        intro j hj
        simp at hj)
  refine ⟨G2, R', r', Ex_mono (Ex_trans hE1 hE2) (by omega), hP2, hS1', hS2', hmono, ?_⟩
  intro x y hr hv hv0
  rw [e] at hv
  have hs0 : vC C x (fun _ : Fin m => false) s = true := by
    rw [vC_dz hM hrb s hsz x _ y]
    exact hv.2
  have hp0 : vC C x (fun _ : Fin m => false) p = false := by
    by_contra hh
    rw [Bool.not_eq_false] at hh
    have h3 := (e x (fun _ : Fin m => false)).2 ⟨hh, hs0⟩
    rw [h3] at hv0
    simp at hv0
  refine ⟨p, hp, hkc x ?_, hv.1, hp0⟩
  show (r (n + m + u) x && vC C x (fun _ : Fin m => false) s) = true
  rw [hr, hs0]
  rfl

theorem hC_step {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) {t : ℕ} (G : List Gate)
    (hP : PX n m G) (c0 : ℕ → ℕ)
    (hc0 : ∀ w < n + m + C.gates.length,
      XC n m G (c0 w) (fun x => vC C x (fun _ : Fin m => false) w))
    (R : ℕ → ℕ) (r : ℕ → (Fin n → Bool) → Bool)
    (hS1 : ∀ w, XC n m G (R w) (r w))
    (hS2 : ∀ (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool), r w x = true → vC C x y w = true → vC C x y t = true)
    (u : ℕ) (hu : u < C.gates.length) :
    ∃ (G' : List Gate) (R' : ℕ → ℕ) (r' : ℕ → (Fin n → Bool) → Bool),
      Ex G G' 2 ∧ PX n m G' ∧ (∀ w, XC n m G' (R' w) (r' w)) ∧
      (∀ (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool), r' w x = true → vC C x y w = true → vC C x y t = true) ∧
      (∀ w x, r w x = true → r' w x = true) ∧
      (∀ (x : Fin n → Bool) (y : Fin m → Bool), r (n + m + u) x = true → vC C x y (n + m + u) = true →
        vC C x (fun _ : Fin m => false) (n + m + u) = false →
        cross n m C u ∨ ∃ w, w < n + m + u ∧ r' w x = true ∧ vC C x y w = true ∧
          vC C x (fun _ : Fin m => false) w = false) := by
  by_cases hc : cross n m C u
  · exact ⟨G, R, r, Ex_mono (Ex_refl G) (by omega), hP, hS1, hS2, fun _ _ h => h,
      fun _ _ _ _ _ => Or.inl hc⟩
  have hg : C.gates.getD u gd ∈ C.gates := by
    rw [List.getD_eq_getElem _ _ hu]
    exact List.getElem_mem hu
  have hopl : ((C.gates.getD u gd).op = GateOp.and ∨ (C.gates.getD u gd).op = GateOp.or) ∧
      (C.gates.getD u gd).inputs.length ≤ 2 := hM _ hg
  have hge : ∀ (x : Fin n → Bool) (y : Fin m → Bool), vC C x y (n + m + u) =
      (C.gates.getD u gd).op.eval ((C.gates.getD u gd).inputs.map (vC C x y)) :=
    fun x y => vC_gate hrb u hu x y
  have hin : ∀ i ∈ (C.gates.getD u gd).inputs, i < n + m + u := hrb u hu
  have hc' : ¬ ((C.gates.getD u gd).op = GateOp.and ∧ (C.gates.getD u gd).inputs.length = 2 ∧
      ∀ i ∈ (C.gates.getD u gd).inputs, 0 < dC n m C i) := hc
  clear hg
  generalize C.gates.getD u gd = g at hopl hge hin hc'
  obtain ⟨op, is⟩ := g
  obtain ⟨hop, hlen⟩ := hopl
  dsimp only at hop hlen hge hin hc'
  rcases is with _ | ⟨c, _ | ⟨d, _ | ⟨e3, rest⟩⟩⟩
  · refine ⟨G, R, r, Ex_mono (Ex_refl G) (by omega), hP, hS1, hS2, fun _ _ h => h, ?_⟩
    intro x y hr hv hv0
    rw [hge x y] at hv
    rw [hge x (fun _ : Fin m => false)] at hv0
    simp only [List.map_nil] at hv hv0
    rw [hv] at hv0
    simp at hv0
  · have e : ∀ (x : Fin n → Bool) (y : Fin m → Bool), vC C x y (n + m + u) = vC C x y c := by
      intro x y
      rw [hge]
      rcases hop with rfl | rfl <;> simp [GateOp.eval]
    obtain ⟨G', R', r', hE, hP', hS1', hS2', hmono, hkc⟩ :=
      hC_acc (C := C) (t := t) hP hS1 hS2 (R (n + m + u)) (r (n + m + u)) (hS1 _) c
        (by
          intro x y hk hv
          apply hS2 (n + m + u) x y hk
          rw [e]
          exact hv)
    refine ⟨G', R', r', Ex_mono hE (by omega), hP', hS1', hS2', hmono, ?_⟩
    intro x y hr hv hv0
    rw [e] at hv hv0
    exact Or.inr ⟨c, hin c (by simp), hkc x hr, hv, hv0⟩
  · rcases hop with rfl | rfl
    · have hz : dC n m C c = 0 ∨ dC n m C d = 0 := by
        by_contra hh
        rw [not_or] at hh
        obtain ⟨h1, h2⟩ := hh
        refine hc' ⟨rfl, rfl, ?_⟩
        intro i hi
        simp at hi
        rcases hi with rfl | rfl <;> omega
      have e : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
          vC C x y (n + m + u) = true ↔ (vC C x y c = true ∧ vC C x y d = true) := by
        intro x y
        rw [hge]
        simp [GateOp.eval]
      have hcl : c < n + m + u := hin c (by simp)
      have hdl : d < n + m + u := hin d (by simp)
      rcases hz with hz | hz
      · obtain ⟨G', R', r', h1, h2, h3, h4, h5, h6⟩ :=
          hC_andstep hM hrb G hP c0 hc0 R r hS1 hS2 u hu d c hdl hcl hz
            (fun x y => by rw [e x y]; exact And.comm)
        exact ⟨G', R', r', h1, h2, h3, h4, h5, fun x y a b c' => Or.inr (h6 x y a b c')⟩
      · obtain ⟨G', R', r', h1, h2, h3, h4, h5, h6⟩ :=
          hC_andstep hM hrb G hP c0 hc0 R r hS1 hS2 u hu c d hcl hdl hz e
        exact ⟨G', R', r', h1, h2, h3, h4, h5, fun x y a b c' => Or.inr (h6 x y a b c')⟩
    · have e : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
          vC C x y (n + m + u) = (vC C x y c || vC C x y d) := by
        intro x y
        rw [hge]
        simp [GateOp.eval]
      obtain ⟨G1, R1, r1, hE1, hP1, hS11, hS12, hm1, hk1⟩ :=
        hC_acc (C := C) (t := t) hP hS1 hS2 (R (n + m + u)) (r (n + m + u)) (hS1 _) c
          (by
            intro x y hk hv
            apply hS2 (n + m + u) x y hk
            rw [e, hv]
            rfl)
      obtain ⟨G2, R2, r2, hE2, hP2, hS21, hS22, hm2, hk2⟩ :=
        hC_acc (C := C) (t := t) hP1 hS11 hS12 (R (n + m + u)) (r (n + m + u))
          (XC_ex (hS1 _) hE1) d
          (by
            intro x y hk hv
            apply hS2 (n + m + u) x y hk
            rw [e, hv]
            simp)
      refine ⟨G2, R2, r2, Ex_mono (Ex_trans hE1 hE2) (by omega), hP2, hS21, hS22,
        fun w x h => hm2 w x (hm1 w x h), ?_⟩
      intro x y hr hv hv0
      rw [e] at hv hv0
      rw [Bool.or_eq_true] at hv
      rw [Bool.or_eq_false_iff] at hv0
      rcases hv with hv | hv
      · exact Or.inr ⟨c, hin c (by simp), hm2 _ _ (hk1 x hr), hv, hv0.1⟩
      · exact Or.inr ⟨d, hin d (by simp), hk2 x hr, hv, hv0.2⟩
  · exfalso
    simp only [List.length_cons] at hlen
    omega

theorem hC_fin {n m : ℕ} {C : Circuit} {t u : ℕ} (hu : u < C.gates.length)
    {r r' : ℕ → (Fin n → Bool) → Bool}
    (hmono : ∀ w x, r w x = true → r' w x = true)
    (htr : ∀ (x : Fin n → Bool) (y : Fin m → Bool), r (n + m + u) x = true → vC C x y (n + m + u) = true →
        vC C x (fun _ : Fin m => false) (n + m + u) = false →
        cross n m C u ∨ ∃ w, w < n + m + u ∧ r' w x = true ∧ vC C x y w = true ∧
          vC C x (fun _ : Fin m => false) w = false)
    (hCm : ∀ (x : Fin n → Bool) (y : Fin m → Bool), vC C x y t = true → vC C x (fun _ : Fin m => false) t = false →
        ∃ w, w ≤ t ∧ r w x = true ∧ vC C x y w = true ∧
          vC C x (fun _ : Fin m => false) w = false ∧
          (w < n + m + (u + 1) ∨ ∃ u' < C.gates.length, w = n + m + u' ∧ cross n m C u')) :
    ∀ (x : Fin n → Bool) (y : Fin m → Bool), vC C x y t = true → vC C x (fun _ : Fin m => false) t = false →
        ∃ w, w ≤ t ∧ r' w x = true ∧ vC C x y w = true ∧
          vC C x (fun _ : Fin m => false) w = false ∧
          (w < n + m + u ∨ ∃ u' < C.gates.length, w = n + m + u' ∧ cross n m C u') := by
  intro x y h1 h2
  obtain ⟨w, hwt, hr, hv, hv0, hw⟩ := hCm x y h1 h2
  rcases hw with hw | hw
  · by_cases hwu : w = n + m + u
    · subst hwu
      rcases htr x y hr hv hv0 with hc | ⟨w', hw', hr', hv', hv0'⟩
      · exact ⟨_, hwt, hmono _ _ hr, hv, hv0, Or.inr ⟨u, hu, rfl, hc⟩⟩
      · exact ⟨w', by omega, hr', hv', hv0', Or.inl hw'⟩
    · exact ⟨w, hwt, hmono _ _ hr, hv, hv0, Or.inl (by omega)⟩
  · exact ⟨w, hwt, hmono _ _ hr, hv, hv0, Or.inr hw⟩

theorem hC_main {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (G : List Gate)
    (hP : PX n m G) (c0 : ℕ → ℕ)
    (hc0 : ∀ w < n + m + C.gates.length,
      XC n m G (c0 w) (fun x => vC C x (fun _ : Fin m => false) w))
    (t : ℕ) : ∀ q, q ≤ C.gates.length →
    ∃ (G' : List Gate) (R : ℕ → ℕ) (r : ℕ → (Fin n → Bool) → Bool),
      Ex G G' (2 + 2 * q) ∧ PX n m G' ∧ (∀ w, XC n m G' (R w) (r w)) ∧
      (∀ (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool), r w x = true → vC C x y w = true → vC C x y t = true) ∧
      (∀ (x : Fin n → Bool) (y : Fin m → Bool), vC C x y t = true → vC C x (fun _ : Fin m => false) t = false →
        ∃ w, w ≤ t ∧ r w x = true ∧ vC C x y w = true ∧
          vC C x (fun _ : Fin m => false) w = false ∧
          (w < n + m + (C.gates.length - q) ∨
            ∃ u < C.gates.length, w = n + m + u ∧ cross n m C u)) := by
  intro q
  induction q with
  | zero =>
    intro _
    obtain ⟨G1, T, hE1, hP1, hT⟩ := hC_const hP true
    obtain ⟨G2, F, hE2, hP2, hF⟩ := hC_const hP1 false
    refine ⟨G2, fun w => if w = t then T else F, fun w _ => decide (w = t),
      Ex_mono (Ex_trans hE1 hE2) (by omega), hP2, ?_, ?_, ?_⟩
    · intro w
      show XC n m G2 (if w = t then T else F) (fun _ => decide (w = t))
      by_cases h : w = t
      · rw [if_pos h]
        exact hC_xc (XC_ex hT hE2) (fun x => by simp [h])
      · rw [if_neg h]
        exact hC_xc hF (fun x => by simp [h])
    · intro w x y h1 h2
      have hwt : w = t := by simpa using h1
      rw [hwt] at h2
      exact h2
    · intro x y h1 h2
      refine ⟨t, le_refl _, by simp, h1, h2, Or.inl ?_⟩
      by_contra hlt
      have h3 := vC_oob C x y t (by omega)
      rw [h3] at h1
      simp at h1
  | succ q ih =>
    intro hq
    obtain ⟨G1, R, r, hE, hP1, hS1, hS2, hCm⟩ := ih (by omega)
    have e1 : C.gates.length - q = (C.gates.length - (q + 1)) + 1 := by omega
    rw [e1] at hCm
    have hu : C.gates.length - (q + 1) < C.gates.length := by omega
    generalize C.gates.length - (q + 1) = u at hCm hu ⊢
    obtain ⟨G2, R', r', hE2, hP2, hS1', hS2', hmono, htr⟩ :=
      hC_step hM hrb G1 hP1 c0 (fun w hw => XC_ex (hc0 w hw) hE) R r hS1 hS2 u hu
    exact ⟨G2, R', r', Ex_mono (Ex_trans hE hE2) (by omega), hP2, hS1', hS2',
      hC_fin hu hmono htr hCm⟩

theorem L4 {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (G : List Gate) (hP : PX n m G)
    (c0 : ℕ → ℕ)
    (hc0 : ∀ w < n + m + C.gates.length,
      XC n m G (c0 w) (fun x => vC C x (fun _ : Fin m => false) w))
    (t : ℕ) :
    ∃ (G' : List Gate) (R : ℕ → ℕ) (r : ℕ → (Fin n → Bool) → Bool),
      Ex G G' (2 * C.gates.length + 2) ∧ PX n m G' ∧ (∀ w, XC n m G' (R w) (r w)) ∧
      (∀ (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool), r w x = true → vC C x y w = true → vC C x y t = true) ∧
      (∀ (x : Fin n → Bool) (y : Fin m → Bool), vC C x y t = true → vC C x (fun _ : Fin m => false) t = false →
        ∃ w, w ≤ t ∧ r w x = true ∧ vC C x y w = true ∧
          ((n ≤ w ∧ w < n + m) ∨ ∃ u < C.gates.length, w = n + m + u ∧ cross n m C u)) := by
  obtain ⟨G', R, r, hE, hP', hS1, hS2, hCm⟩ :=
    hC_main hM hrb G hP c0 hc0 t C.gates.length (le_refl _)
  refine ⟨G', R, r, Ex_mono hE (by omega), hP', hS1, hS2, ?_⟩
  intro x y h1 h2
  obtain ⟨w, hwt, hr, hv, hv0, hw⟩ := hCm x y h1 h2
  refine ⟨w, hwt, hr, hv, ?_⟩
  rcases hw with hw | hw
  · left
    refine ⟨?_, by omega⟩
    by_contra hlt
    have hlt' : w < n := by omega
    rw [vC_left C x y w hlt'] at hv
    rw [vC_left C x (fun _ : Fin m => false) w hlt'] at hv0
    rw [hv] at hv0
    simp at hv0
  · exact Or.inr hw

open Classical in
noncomputable def cc (n m : ℕ) (C : Circuit) (p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun u => cross n m C u)).card

theorem cc_succ_cross (n m : ℕ) (C : Circuit) (p : ℕ) (h : cross n m C p) :
    cc n m C (p + 1) = cc n m C p + 1 := by
  classical
  unfold cc
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem]
  simp

theorem cc_succ_not (n m : ℕ) (C : Circuit) (p : ℕ) (h : ¬ cross n m C p) :
    cc n m C (p + 1) = cc n m C p := by
  classical
  unfold cc
  rw [Finset.range_add_one, Finset.filter_insert, if_neg h]

theorem cc_mono (n m : ℕ) (C : Circuit) (p q : ℕ) (h : p ≤ q) : cc n m C p ≤ cc n m C q := by
  classical
  unfold cc
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

theorem cc_pos (n m : ℕ) (C : Circuit) (u p : ℕ) (h : u < p) (hc : cross n m C u) :
    cc n m C u + 1 ≤ cc n m C p := by
  rw [← cc_succ_cross n m C u hc]
  exact cc_mono n m C (u + 1) p h

theorem cc_ncard (n m : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ cross n m C j} = cc n m C C.gates.length := by
  classical
  unfold cc
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp

theorem cc_list (n m : ℕ) (C : Circuit) (u : ℕ) :
    ∃ L : List ℕ, L.length = cc n m C u ∧ ∀ u', u' ∈ L ↔ (u' < u ∧ cross n m C u') := by
  classical
  refine ⟨((Finset.range u).filter (fun u' => cross n m C u')).toList, ?_, ?_⟩
  · rw [Finset.length_toList]
    rfl
  · intro u'
    rw [Finset.mem_toList, Finset.mem_filter, Finset.mem_range]

theorem hE_xin {n m : ℕ} (G : List Gate) (w : ℕ) (h : w < n) :
    XC n m G w (fun x => x ⟨w, h⟩) := by
  refine ⟨Or.inl h, by omega, ?_⟩
  intro x y
  show gv false Φb G (inp x y) w = _
  rw [gv_input _ _ _ _ _ (by rw [inp_len]; omega), inp_left x y w h]

theorem hE_cm {n m : ℕ} {G : List Gate} {w : ℕ} {f f' : (Fin n → Bool) → (Fin m → Bool) → Bool}
    (h : Cm G w f) (e : ∀ x y, f x y = f' x y) : Cm G w f' := by
  have hff : f = f' := funext fun x => funext fun y => e x y
  rw [← hff]
  exact h

theorem hE_L3 {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (G : List Gate)
    (hP : PX n m G) (F : ℕ) (hF : XC n m G F (fun _ => false)) :
    ∀ p, p ≤ C.gates.length → ∃ (G' : List Gate) (c0 : ℕ → ℕ), Ex G G' p ∧ PX n m G' ∧
      ∀ w < n + m + p, XC n m G' (c0 w) (fun x => vC C x (fun _ : Fin m => false) w) := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨G, fun w => if w < n then w else F, Ex_refl G, hP, ?_⟩
    intro w hw
    by_cases h : w < n
    · have e : (if w < n then w else F) = w := if_pos h
      show XC n m G (if w < n then w else F) _
      rw [e]
      refine hC_xc (hE_xin G w h) ?_
      intro x
      exact (vC_left C x _ w h).symm
    · have e : (if w < n then w else F) = F := if_neg h
      show XC n m G (if w < n then w else F) _
      rw [e]
      refine hC_xc hF ?_
      intro x
      rw [hB_mid C x _ w (by omega) (by omega)]
  | succ p ih =>
    intro hp
    obtain ⟨G1, c0, hE1, hP1, hc⟩ := ih (by omega)
    have hp' : p < C.gates.length := by omega
    have hg := hM _ (hB_mem C p hp')
    obtain ⟨G2, w2, hE2, hP2, hw2⟩ := L_gate hP1 (C.gates.getD p gd).op hg.1
      (C.gates.getD p gd).inputs hg.2 c0 (fun i x => vC C x (fun _ : Fin m => false) i)
      (fun i hi => hc i (hrb p hp' i hi))
    refine ⟨G2, Function.update c0 (n + m + p) w2, Ex_trans hE1 hE2, hP2, ?_⟩
    intro w hw
    by_cases h : w = n + m + p
    · rw [h, Function.update_self]
      refine hC_xc hw2 ?_
      intro x
      exact (vC_gate hrb p hp' x _).symm
    · rw [Function.update_of_ne h]
      exact XC_ex (hc w (by omega)) hE2

theorem L3 {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (G : List Gate) (hP : PX n m G) :
    ∃ (G' : List Gate) (c0 : ℕ → ℕ), Ex G G' (C.gates.length + 1) ∧ PX n m G' ∧
      ∀ w < n + m + C.gates.length,
        XC n m G' (c0 w) (fun x => vC C x (fun _ : Fin m => false) w) := by
  obtain ⟨G1, F, hE1, hP1, hF⟩ := hC_const hP false
  obtain ⟨G2, c0, hE2, hP2, hc⟩ := hE_L3 hM hrb G1 hP1 F hF C.gates.length (le_refl _)
  exact ⟨G2, c0, Ex_mono (Ex_trans hE1 hE2) (by omega), hP2, hc⟩

theorem hE_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem hE_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem hE_mux {n m : ℕ} {C : Circuit} (P : List Gate) (hP : PX n m P) (u z : ℕ)
    (hz : XC n m P z (fun x => vC C x (fun _ : Fin m => false) (n + m + u)))
    (H : ℕ → ℕ)
    (hH : ∀ j : Fin m,
      XC n m P (H j.val) (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u)))
    (G0 : List Gate) (c : ℕ) (hE0 : Ex P G0 c) (hS0 : St n m G0) :
    ∀ j', j' ≤ m → ∃ (G' : List Gate) (w : ℕ), Ex G0 G' (2 * j') ∧ St n m G' ∧
      Cm (n := n) (m := m) G' w (fun x y => vC C x (fun _ : Fin m => false) (n + m + u) ||
        decide (∃ j : Fin m, j.val < j' ∧ y j = true ∧
          vC C x (fun l : Fin m => decide (l = j)) (n + m + u) = true)) := by
  intro j'
  induction j' with
  | zero =>
    intro _
    refine ⟨G0, z, Ex_refl G0, hS0, ?_⟩
    refine hE_cm (Cm_ex hz.2 hE0) ?_
    intro x y
    simp
  | succ j' ih =>
    intro hj
    obtain ⟨G1, w1, hE1, hS1, hC1⟩ := ih (by omega)
    have hlt : j' < m := by omega
    have EP1 : Ex P G1 (c + 2 * j') := Ex_trans hE0 hE1
    have hl1 := Ex_len EP1
    have hHj := hH ⟨j', hlt⟩
    have hHlt : H j' < n + m + P.length := hHj.2.1
    have h2 := push2 hS1 ⟨GateOp.and, [n + j', H j']⟩ (Or.inl rfl) (by simp)
      (by
        intro i hi
        simp at hi
        rcases hi with rfl | rfl
        · omega
        · omega)
      (fun _ _ => ⟨H j', by simp, by
        rw [dg_ex EP1 hHlt]
        exact xw_dg hP.2 hHj.1 hHlt⟩)
    obtain ⟨G2, hG2⟩ : ∃ G2, G2 = G1 ++ [(⟨GateOp.and, [n + j', H j']⟩ : Gate)] := ⟨_, rfl⟩
    rw [← hG2] at h2
    obtain ⟨hS2, hv2, -⟩ := h2
    have hlen2 : G2.length = G1.length + 1 := by rw [hG2]; simp
    have E12 : Ex G1 G2 1 := ⟨⟨_, hG2⟩, by omega⟩
    have hw1 : w1 < n + m + G1.length := hC1.1
    have h3 := push2 hS2 ⟨GateOp.or, [w1, n + m + G1.length]⟩ (Or.inr rfl) (by simp)
      (by
        intro i hi
        simp at hi
        rcases hi with rfl | rfl
        · omega
        · omega)
      (fun h => by simp at h)
    obtain ⟨G3, hG3⟩ : ∃ G3, G3 = G2 ++ [(⟨GateOp.or, [w1, n + m + G1.length]⟩ : Gate)] :=
      ⟨_, rfl⟩
    rw [← hG3] at h3
    obtain ⟨hS3, hv3, -⟩ := h3
    have hlen3 : G3.length = G2.length + 1 := by rw [hG3]; simp
    have E23 : Ex G2 G3 1 := ⟨⟨_, hG3⟩, by omega⟩
    refine ⟨G3, n + m + G2.length, Ex_mono (Ex_trans (Ex_trans hE1 E12) E23) (by omega), hS3,
      by omega, ?_⟩
    intro x y
    rw [hv3 (inp x y) (inp_len x y)]
    have e1 := (Cm_ex hC1 E12).2 x y
    have e2 : vl G2 (inp x y) (n + m + G1.length) =
        (y ⟨j', hlt⟩ && vC C x (fun l : Fin m => decide (l = ⟨j', hlt⟩)) (n + m + u)) := by
      rw [hv2 (inp x y) (inp_len x y)]
      have a1 : vl G1 (inp x y) (n + j') = y ⟨j', hlt⟩ := by
        show gv false Φb G1 (inp x y) (n + j') = _
        rw [gv_input _ _ _ _ _ (by rw [inp_len]; omega)]
        exact inp_right x y ⟨j', hlt⟩
      have a2 := (Cm_ex hHj.2 EP1).2 x y
      show GateOp.and.eval [vl G1 (inp x y) (n + j'), vl G1 (inp x y) (H j')] = _
      rw [a1, a2, hE_and2]
    show GateOp.or.eval [vl G2 (inp x y) w1, vl G2 (inp x y) (n + m + G1.length)] = _
    rw [e1, e2, hE_or2, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((h | ⟨j, hj, h⟩) | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, h⟩
      · exact Or.inr ⟨⟨j', hlt⟩, Nat.lt_succ_self j', h1, h2⟩
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inl (Or.inl h)
      · by_cases e : j.val = j'
        · have ej : j = ⟨j', hlt⟩ := Fin.ext e
          rw [ej] at h
          exact Or.inr h
        · exact Or.inl (Or.inr ⟨j, by omega, h⟩)

theorem hE_Q1 {n m : ℕ} {C : Circuit} (P : List Gate) (hP : PX n m P)
    (z0 : ℕ → ℕ)
    (hz : ∀ u < C.gates.length, cross n m C u →
      XC n m P (z0 u) (fun x => vC C x (fun _ : Fin m => false) (n + m + u)))
    (H : ℕ → ℕ → ℕ)
    (hH : ∀ u < C.gates.length, cross n m C u → ∀ j : Fin m,
      XC n m P (H u j.val) (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u))) :
    ∀ p, p ≤ C.gates.length → ∃ (G' : List Gate) (Ew : ℕ → ℕ),
      Ex P G' (cc n m C p * (2 * m)) ∧ St n m G' ∧
      ∀ u < p, cross n m C u → Cm (n := n) (m := m) G' (Ew u) (env C (n + m + u)) := by
  intro p
  induction p with
  | zero =>
    intro _
    exact ⟨P, fun _ => 0, Ex_mono (Ex_refl P) (Nat.zero_le _), hP.1,
      fun u hu => absurd hu (Nat.not_lt_zero _)⟩
  | succ p ih =>
    intro hp
    obtain ⟨G1, Ew, hE1, hS1, hC1⟩ := ih (by omega)
    by_cases hc : cross n m C p
    · obtain ⟨G2, w, hE2, hS2, hw⟩ := hE_mux P hP p (z0 p) (hz p (by omega) hc) (H p)
        (hH p (by omega) hc) G1 _ hE1 hS1 m (le_refl _)
      refine ⟨G2, Function.update Ew p w, ?_, hS2, ?_⟩
      · rw [cc_succ_cross n m C p hc]
        exact Ex_mono (Ex_trans hE1 hE2) (Nat.le_of_eq (by ring))
      · intro u hu hcu
        by_cases h : u = p
        · rw [h, Function.update_self]
          refine hE_cm hw ?_
          intro x y
          rw [Bool.eq_iff_iff, hB_env_iff]
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          constructor
          · rintro (h | ⟨j, _, h⟩)
            · exact Or.inl h
            · exact Or.inr ⟨j, h⟩
          · rintro (h | ⟨j, h⟩)
            · exact Or.inl h
            · exact Or.inr ⟨j, j.isLt, h⟩
        · rw [Function.update_of_ne h]
          exact Cm_ex (hC1 u (by omega) hcu) hE2
    · refine ⟨G1, Ew, ?_, hS1, ?_⟩
      · rw [cc_succ_not n m C p hc]
        exact hE1
      · intro u hu hcu
        have hne : u ≠ p := by
          rintro rfl
          exact hc hcu
        exact hC1 u (by omega) hcu

theorem Q1 {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (P : List Gate) (hP : PX n m P)
    (z0 : ℕ → ℕ)
    (hz : ∀ u < C.gates.length, cross n m C u →
      XC n m P (z0 u) (fun x => vC C x (fun _ : Fin m => false) (n + m + u)))
    (H : ℕ → ℕ → ℕ)
    (hH : ∀ u < C.gates.length, cross n m C u → ∀ j : Fin m,
      XC n m P (H u j.val) (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u))) :
    ∃ (G' : List Gate) (Ew : ℕ → ℕ), Ex P G' (cc n m C C.gates.length * (2 * m)) ∧ St n m G' ∧
      ∀ u < C.gates.length, cross n m C u → Cm (n := n) (m := m) G' (Ew u) (env C (n + m + u)) :=
  hE_Q1 P hP z0 hz H hH C.gates.length (le_refl _)

theorem hF_fold {n m : ℕ} {C : Circuit} (j : Fin m) (r : ℕ → (Fin n → Bool) → Bool) (L' : List ℕ) :
    ∀ (G : List Gate) (R : ℕ → ℕ) (H : ℕ → ℕ → ℕ) (w : ℕ) (f : (Fin n → Bool) → Bool),
      PX n m G → (∀ w', XC n m G (R w') (r w')) →
      (∀ u' ∈ L', XC n m G (H u' j.val)
        (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u'))) →
      XC n m G w f →
      ∃ G' w', Ex G G' (2 * L'.length) ∧ PX n m G' ∧
        XC n m G' w' (fun x => f x || L'.any (fun u' =>
          vC C x (fun l : Fin m => decide (l = j)) (n + m + u') && r (n + m + u') x)) := by
  induction L' with
  | nil =>
    intro G R H w f hP hR hH hw
    exact ⟨G, w, Ex_refl G, hP, hC_xc hw (by intro x; simp)⟩
  | cons a L' ih =>
    intro G R H w f hP hR hH hw
    obtain ⟨G1, w1, hE1, hP1, hw1⟩ := hC_and2 hP (hH a (List.mem_cons_self ..)) (hR (n + m + a))
    obtain ⟨G2, w2, hE2, hP2, hw2⟩ := hC_or2 hP1 (XC_ex hw hE1) hw1
    have hE12 := Ex_trans hE1 hE2
    obtain ⟨G3, w3, hE3, hP3, hw3⟩ := ih G2 R H w2 _ hP2 (fun w' => XC_ex (hR w') hE12)
      (fun u' hu' => XC_ex (hH u' (List.mem_cons_of_mem _ hu')) hE12) hw2
    refine ⟨G3, w3, Ex_mono (Ex_trans hE12 hE3) (by simp only [List.length_cons]; omega), hP3,
      hC_xc hw3 ?_⟩
    intro x
    simp [List.any_cons, Bool.or_assoc]

theorem hF_one {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (G : List Gate)
    (hP : PX n m G) (c0 : ℕ → ℕ)
    (hc0 : ∀ w < n + m + C.gates.length,
      XC n m G (c0 w) (fun x => vC C x (fun _ : Fin m => false) w))
    (u : ℕ) (hu : u < C.gates.length) (t : ℕ) (ht : t < n + m + u)
    (R : ℕ → ℕ) (r : ℕ → (Fin n → Bool) → Bool)
    (hR : ∀ w, XC n m G (R w) (r w))
    (hs : ∀ (w : ℕ) (x : Fin n → Bool) (y : Fin m → Bool),
      r w x = true → vC C x y w = true → vC C x y t = true)
    (hc : ∀ (x : Fin n → Bool) (y : Fin m → Bool), vC C x y t = true →
      vC C x (fun _ : Fin m => false) t = false →
        ∃ w, w ≤ t ∧ r w x = true ∧ vC C x y w = true ∧
          ((n ≤ w ∧ w < n + m) ∨ ∃ u' < C.gates.length, w = n + m + u' ∧ cross n m C u'))
    (H : ℕ → ℕ → ℕ)
    (hH : ∀ u' < u, cross n m C u' → ∀ j : Fin m,
      XC n m G (H u' j.val) (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u')))
    (j : Fin m) :
    ∃ G' w, Ex G G' (1 + 2 * cc n m C u) ∧ PX n m G' ∧
      XC n m G' w (fun x => vC C x (fun l : Fin m => decide (l = j)) t) := by
  obtain ⟨L, hLlen, hLmem⟩ := cc_list n m C u
  obtain ⟨G1, w1, hE1, hP1, hw1⟩ := hC_or2 hP (hc0 t (by omega)) (hR (n + j.val))
  obtain ⟨G2, w2, hE2, hP2, hw2⟩ := hF_fold (C := C) j r L G1 R H w1 _ hP1
    (fun w' => XC_ex (hR w') hE1)
    (fun u' hu' => XC_ex (hH u' ((hLmem u').1 hu').1 ((hLmem u').1 hu').2 j) hE1) hw1
  refine ⟨G2, w2, Ex_mono (Ex_trans hE1 hE2) (by omega), hP2, hC_xc hw2 ?_⟩
  intro x
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ((h | h) | ⟨u', hu', h1, h2⟩)
    · exact vC_mono hM hrb x _ _ (fun j' hj' => absurd hj' (by simp)) t h
    · refine hs (n + j.val) x _ h ?_
      rw [vC_right]
      simp
    · exact hs _ x _ h2 h1
  · intro h
    by_cases h0 : vC C x (fun _ : Fin m => false) t = true
    · exact Or.inl (Or.inl h0)
    · have h0' : vC C x (fun _ : Fin m => false) t = false := by simpa using h0
      obtain ⟨w, hwt, hrw, hvw, hcase⟩ := hc x _ h h0'
      rcases hcase with ⟨hn, hnm⟩ | ⟨u', hu', rfl, hcr⟩
      · rw [hB_mid C x _ w hn hnm] at hvw
        have h3 : (⟨w - n, by omega⟩ : Fin m) = j := by simpa using hvw
        have h4 : w - n = j.val := congrArg Fin.val h3
        have hwj : w = n + j.val := by omega
        rw [hwj] at hrw
        exact Or.inl (Or.inr hrw)
      · exact Or.inr ⟨u', (hLmem u').2 ⟨by omega, hcr⟩, hvw, hrw⟩

theorem hF_gate {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (G : List Gate)
    (hP : PX n m G) (c0 : ℕ → ℕ)
    (hc0 : ∀ w < n + m + C.gates.length,
      XC n m G (c0 w) (fun x => vC C x (fun _ : Fin m => false) w))
    (u : ℕ) (hu : u < C.gates.length) (hcr : cross n m C u)
    (H : ℕ → ℕ → ℕ)
    (hH : ∀ u' < u, cross n m C u' → ∀ j : Fin m,
      XC n m G (H u' j.val) (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u'))) :
    ∃ (G' : List Gate) (Hu : ℕ → ℕ),
      Ex G G' (4 * C.gates.length + 4 + m * (4 * cc n m C u + 3)) ∧ PX n m G' ∧
      ∀ j : Fin m, XC n m G' (Hu j.val)
        (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u)) := by
  obtain ⟨hop, hlen, hpos⟩ := hcr
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
  have ha : a < n + m + u := hrb u hu a (by rw [hab]; simp)
  have hb : b < n + m + u := hrb u hu b (by rw [hab]; simp)
  obtain ⟨G1, Ra, ra, hE1, hP1, hRa, hsa, hca⟩ := L4 hM hrb G hP c0 hc0 a
  obtain ⟨G2, Rb, rb, hE2, hP2, hRb, hsb, hcb⟩ :=
    L4 hM hrb G1 hP1 c0 (fun w hw => XC_ex (hc0 w hw) hE1) b
  have key : ∀ j' ≤ m, ∃ (G' : List Gate) (Hu : ℕ → ℕ),
      Ex G2 G' (j' * (4 * cc n m C u + 3)) ∧ PX n m G' ∧
      ∀ j : Fin m, j.val < j' → XC n m G' (Hu j.val)
        (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u)) := by
    intro j'
    induction j' with
    | zero =>
      intro _
      exact ⟨G2, fun _ => 0, Ex_mono (Ex_refl G2) (Nat.zero_le _), hP2,
        fun j hj => absurd hj (by omega)⟩
    | succ j' ih =>
      intro hj'
      obtain ⟨G3, Hu, hE3, hP3, hHu⟩ := ih (by omega)
      have hE13 := Ex_trans hE2 hE3
      have hE03 := Ex_trans hE1 hE13
      obtain ⟨j, hjdef⟩ : ∃ j : Fin m, j.val = j' := ⟨⟨j', by omega⟩, rfl⟩
      obtain ⟨G4, wa, hE4, hP4, hwa⟩ := hF_one hM hrb G3 hP3 c0
        (fun w hw => XC_ex (hc0 w hw) hE03) u hu a ha Ra ra (fun w => XC_ex (hRa w) hE13)
        hsa hca H (fun u' hu' hc' j => XC_ex (hH u' hu' hc' j) hE03) j
      have hE04 := Ex_trans hE03 hE4
      obtain ⟨G5, wb, hE5, hP5, hwb⟩ := hF_one hM hrb G4 hP4 c0
        (fun w hw => XC_ex (hc0 w hw) hE04) u hu b hb Rb rb
        (fun w => XC_ex (hRb w) (Ex_trans hE3 hE4))
        hsb hcb H (fun u' hu' hc' j => XC_ex (hH u' hu' hc' j) hE04) j
      obtain ⟨G6, wg, hE6, hP6, hwg⟩ := hC_and2 hP5 (XC_ex hwa hE5) hwb
      have hE36 := Ex_trans (Ex_trans hE4 hE5) hE6
      refine ⟨G6, Function.update Hu j' wg, Ex_mono (Ex_trans hE3 hE36) ?_, hP6, ?_⟩
      · rw [Nat.add_mul, Nat.one_mul]
        omega
      · intro i hi
        by_cases hij : i.val = j'
        · have hieq : i = j := Fin.ext (hij.trans hjdef.symm)
          rw [hij, Function.update_self, hieq]
          refine hC_xc hwg ?_
          intro x
          rw [vC_gate hrb u hu x _, hop, hab]
          simp [GateOp.eval]
        · rw [Function.update_of_ne hij]
          exact XC_ex (hHu i (by omega)) hE36
  obtain ⟨G', Hu, hE', hP', hHu⟩ := key m le_rfl
  refine ⟨G', Hu, Ex_mono (Ex_trans hE1 (Ex_trans hE2 hE')) ?_, hP', fun j => hHu j j.isLt⟩
  generalize m * (4 * cc n m C u + 3) = z
  omega

theorem L6 {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (G : List Gate) (hP : PX n m G)
    (c0 : ℕ → ℕ)
    (hc0 : ∀ w < n + m + C.gates.length,
      XC n m G (c0 w) (fun x => vC C x (fun _ : Fin m => false) w)) :
    ∃ (G' : List Gate) (H : ℕ → ℕ → ℕ),
      Ex G G' (cc n m C C.gates.length *
        (4 * C.gates.length + 4 + m * (4 * cc n m C C.gates.length + 3))) ∧ PX n m G' ∧
      ∀ u < C.gates.length, cross n m C u → ∀ j : Fin m,
        XC n m G' (H u j.val) (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u)) := by
  have key : ∀ p ≤ C.gates.length, ∃ (G' : List Gate) (H : ℕ → ℕ → ℕ),
      Ex G G' (cc n m C p *
        (4 * C.gates.length + 4 + m * (4 * cc n m C C.gates.length + 3))) ∧ PX n m G' ∧
      ∀ u < p, cross n m C u → ∀ j : Fin m,
        XC n m G' (H u j.val)
          (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u)) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact ⟨G, fun _ _ => 0, Ex_mono (Ex_refl G) (Nat.zero_le _), hP,
        fun u hu => absurd hu (by omega)⟩
    | succ p ih =>
      intro hp
      obtain ⟨G1, H, hE1, hP1, hH⟩ := ih (by omega)
      by_cases hcr : cross n m C p
      · obtain ⟨G2, Hu, hE2, hP2, hHu⟩ := hF_gate hM hrb G1 hP1 c0
          (fun w hw => XC_ex (hc0 w hw) hE1) p (by omega) hcr H
          (fun u' hu' hc' j => hH u' hu' hc' j)
        refine ⟨G2, Function.update H p Hu, Ex_mono (Ex_trans hE1 hE2) ?_, hP2, ?_⟩
        · rw [cc_succ_cross n m C p hcr, Nat.add_mul, Nat.one_mul]
          have h1 : cc n m C p ≤ cc n m C C.gates.length := cc_mono n m C p _ (by omega)
          have h2 : m * (4 * cc n m C p + 3) ≤ m * (4 * cc n m C C.gates.length + 3) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        · intro u hu hc j
          by_cases hup : u = p
          · rw [hup, Function.update_self]
            exact hHu j
          · rw [Function.update_of_ne hup]
            exact XC_ex (hH u (by omega) hc j) hE2
      · refine ⟨G1, H, ?_, hP1, ?_⟩
        · rw [cc_succ_not n m C p hcr]
          exact hE1
        · intro u hu hc j
          have hne : u ≠ p := by
            rintro rfl
            exact hcr hc
          exact hH u (by omega) hc j
  exact key _ le_rfl

theorem hG_base {n m : ℕ} (C : Circuit) (G : List Gate) (w : ℕ) (hw : w < n + m) :
    Cm (n := n) (m := m) G w (env C w) ∧ (dC n m C w = 0 → dg n m G w = 0) := by
  refine ⟨⟨by omega, fun x y => ?_⟩, fun h => ?_⟩
  · show gv false Φb G (inp x y) w = env C w x y
    rw [gv_input false Φb G (inp x y) w (by rw [inp_len]; exact hw)]
    by_cases h : w < n
    · rw [inp_left x y w h, env_left C x y w h]
    · obtain ⟨j, rfl⟩ : ∃ j : Fin m, w = n + j.val :=
        ⟨⟨w - n, by omega⟩, by show w = n + (w - n); omega⟩
      rw [inp_right, env_right]
  · have h1 : dC n m C w = (d0 n m).getD w 0 :=
      gv_input 0 Φd C.gates (d0 n m) w (by rw [d0_len]; exact hw)
    have h2 : dg n m G w = (d0 n m).getD w 0 :=
      gv_input 0 Φd G (d0 n m) w (by rw [d0_len]; exact hw)
    rw [h2, ← h1]
    exact h

theorem hG_main {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (G : List Gate) (hS : St n m G)
    (Ew : ℕ → ℕ)
    (hE : ∀ u < C.gates.length, cross n m C u →
      Cm (n := n) (m := m) G (Ew u) (env C (n + m + u))) :
    ∀ p, p ≤ C.gates.length → ∃ (G' : List Gate) (ρ : ℕ → ℕ), Ex G G' p ∧ St n m G' ∧
      ∀ w < n + m + p, Cm (n := n) (m := m) G' (ρ w) (env C w) ∧
        (dC n m C w = 0 → dg n m G' (ρ w) = 0) := by
  intro p
  induction p with
  | zero =>
    intro _
    exact ⟨G, id, Ex_refl G, hS, fun w hw => hG_base C G w (by omega)⟩
  | succ p ih =>
    intro hp
    have hpl : p < C.gates.length := by omega
    obtain ⟨G', ρ, hEx, hS', hw⟩ := ih (by omega)
    by_cases hc : cross n m C p
    · refine ⟨G', Function.update ρ (n + m + p) (Ew p), Ex_mono hEx (by omega), hS',
        fun w hlt => ?_⟩
      by_cases hwp : w = n + m + p
      · subst hwp
        rw [Function.update_self]
        refine ⟨Cm_ex (hE p hpl hc) hEx, fun h0 => ?_⟩
        have := dC_cross hrb p hpl hc
        omega
      · rw [Function.update_of_ne hwp]
        exact hw w (by omega)
    · obtain ⟨g, hg⟩ : ∃ g, g = C.gates.getD p gd := ⟨_, rfl⟩
      have hgm : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        rw [hg]
        exact hM _ (hB_mem C p hpl)
      have hin : ∀ i ∈ g.inputs, i < n + m + p := by
        rw [hg]
        exact hrb p hpl
      have hc' : ¬ (g.op = GateOp.and ∧ g.inputs.length = 2 ∧
          ∀ i ∈ g.inputs, 0 < dC n m C i) := by
        rw [hg]
        exact hc
      have heg : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
          g.op.eval (g.inputs.map (fun i => env C i x y)) = env C (n + m + p) x y := by
        rw [hg]
        exact env_gate hM hrb p hpl hc
      have hdz : dC n m C (n + m + p) = 0 → ∀ i ∈ g.inputs, dC n m C i = 0 := by
        rw [hg]
        exact dC_zero hM hrb p hpl
      have hpush := push2 hS' ⟨g.op, g.inputs.map ρ⟩ hgm.1 (by simpa using hgm.2)
        (by
          intro i hi
          obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
          exact (hw i0 (hin i0 hi0)).1.1)
        (by
          intro hop hl
          have hl2 : g.inputs.length = 2 := by simpa using hl
          have hex : ∃ i ∈ g.inputs, ¬ 0 < dC n m C i := by
            by_contra hcon
            apply hc'
            refine ⟨hop, hl2, fun i hi => ?_⟩
            by_contra hi0
            exact hcon ⟨i, hi, hi0⟩
          obtain ⟨i, hi, hd⟩ := hex
          exact ⟨ρ i, List.mem_map_of_mem hi, (hw i (hin i hi)).2 (by omega)⟩)
      obtain ⟨hS'', hval, hdeg⟩ := hpush
      have hEx1 : Ex G' (G' ++ [⟨g.op, g.inputs.map ρ⟩]) 1 := ⟨⟨[_], rfl⟩, by simp⟩
      refine ⟨G' ++ [⟨g.op, g.inputs.map ρ⟩],
        Function.update ρ (n + m + p) (n + m + G'.length), Ex_trans hEx hEx1, hS'',
        fun w hlt => ?_⟩
      by_cases hwp : w = n + m + p
      · subst hwp
        rw [Function.update_self]
        refine ⟨⟨by simp, fun x y => ?_⟩, fun h0 => ?_⟩
        · rw [hval (inp x y) (inp_len x y)]
          show g.op.eval ((g.inputs.map ρ).map (vl G' (inp x y))) = _
          rw [List.map_map, ← heg x y]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact (hw i (hin i hi)).1.2 x y
        · apply hdeg
          intro i hi
          obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
          exact (hw i0 (hin i0 hi0)).2 (hdz h0 i0 hi0)
      · rw [Function.update_of_ne hwp]
        have h := hw w (by omega)
        refine ⟨Cm_ex h.1 hEx1, fun h0 => ?_⟩
        rw [dg_ex hEx1 h.1.1]
        exact h.2 h0

theorem Q2 {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (G : List Gate) (hS : St n m G)
    (Ew : ℕ → ℕ)
    (hE : ∀ u < C.gates.length, cross n m C u →
      Cm (n := n) (m := m) G (Ew u) (env C (n + m + u))) :
    ∃ (G' : List Gate) (ρ : ℕ → ℕ), Ex G G' C.gates.length ∧ St n m G' ∧
      ∀ w < n + m + C.gates.length, Cm (n := n) (m := m) G' (ρ w) (env C w) := by
  obtain ⟨G', ρ, hEx, hS', hw⟩ := hG_main hM hrb G hS Ew hE C.gates.length (le_refl _)
  exact ⟨G', ρ, hEx, hS', fun w hlt => (hw w hlt).1⟩

theorem hH_tail {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) (P : List Gate) (hP : PX n m P)
    (z0 : ℕ → ℕ)
    (hz : ∀ u < C.gates.length, cross n m C u →
      XC n m P (z0 u) (fun x => vC C x (fun _ : Fin m => false) (n + m + u)))
    (H : ℕ → ℕ → ℕ)
    (hH : ∀ u < C.gates.length, cross n m C u → ∀ j : Fin m,
      XC n m P (H u j.val) (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u))) :
    ∃ (G' : List Gate) (ρ : ℕ → ℕ),
      Ex P G' (cc n m C C.gates.length * (2 * m) + C.gates.length) ∧ St n m G' ∧
      (∀ j < P.length, dg n m G' (n + m + j) = 0) ∧
      ∀ w < n + m + C.gates.length, Cm (n := n) (m := m) G' (ρ w) (env C w) := by
  obtain ⟨G1, Ew, hE1, hS1, hEw⟩ := Q1 hM hrb P hP z0 hz H hH
  obtain ⟨G2, ρ, hE2, hS2, hρ⟩ := Q2 hM hrb G1 hS1 Ew hEw
  have hE := Ex_trans hE1 hE2
  refine ⟨G2, ρ, hE, hS2, ?_, hρ⟩
  intro j hj
  rw [dg_ex hE (by omega)]
  exact hP.2 j hj

theorem hH_nil (n m : ℕ) : PX n m [] := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    simp at hg
  · intro j hj
    simp at hj
  · intro j hj
    simp at hj
  · intro j hj
    simp at hj

theorem hH_P {n m : ℕ} {C : Circuit} (hM : M2 C) (hrb : RB n m C) :
    ∃ (P : List Gate) (z0 : ℕ → ℕ) (H : ℕ → ℕ → ℕ), PX n m P ∧
      (∀ u < C.gates.length, cross n m C u →
        XC n m P (z0 u) (fun x => vC C x (fun _ : Fin m => false) (n + m + u))) ∧
      (∀ u < C.gates.length, cross n m C u → ∀ j : Fin m,
        XC n m P (H u j.val) (fun x => vC C x (fun l : Fin m => decide (l = j)) (n + m + u))) ∧
      P.length ≤ (C.gates.length + 1) + cc n m C C.gates.length *
        (4 * C.gates.length + 4 + m * (4 * cc n m C C.gates.length + 3)) ∧
      (cc n m C C.gates.length = 0 → P.length = 0) := by
  by_cases hk : cc n m C C.gates.length = 0
  · refine ⟨[], fun _ => 0, fun _ _ => 0, hH_nil n m, ?_, ?_, ?_, fun _ => rfl⟩
    · intro u hu hc
      have := cc_pos n m C u _ hu hc
      omega
    · intro u hu hc
      have := cc_pos n m C u _ hu hc
      omega
    · simp
  · obtain ⟨G1, c0, hE1, hP1, hc0⟩ := L3 hM hrb [] (hH_nil n m)
    obtain ⟨G2, H, hE2, hP2, hH⟩ := L6 hM hrb G1 hP1 c0 hc0
    refine ⟨G2, fun u => c0 (n + m + u), H, hP2, ?_, hH, ?_, fun h => absurd h hk⟩
    · intro u hu hc
      exact XC_ex (hc0 (n + m + u) (by omega)) hE2
    · have h1 := hE1.2
      have h2 := hE2.2
      simp only [List.length_nil, Nat.zero_add] at h1
      omega

theorem main_thm : ∀ (n m s k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + k * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true)) := by
  intro n m s k C hMono hRB hs hk
  have hM : M2 C := by
    intro g hg
    have h := hMono g hg
    refine ⟨?_, h.2⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  have hrb : RB n m C := fun j hj i hi => hRB j hj i hi
  have hk0 : cc n m C C.gates.length ≤ k := by
    rw [← cc_ncard]
    exact hk
  obtain ⟨P, z0, H, hP, hz, hH, hPlen, hP0⟩ := hH_P (n := n) (m := m) hM hrb
  obtain ⟨G', ρ, hE, hS, hdz, hρ⟩ := hH_tail hM hrb P hP z0 hz H hH
  have hs0 : C.gates.length ≤ s := hs
  have hlen1 : P.length ≤ G'.length := Ex_len hE
  have hlen2 : G'.length ≤ P.length + (cc n m C C.gates.length * (2 * m) + C.gates.length) := hE.2
  refine ⟨⟨G', if C.output < n + m + C.gates.length then ρ C.output else n + m + G'.length⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have h := hS.1 g hg
    refine ⟨?_, h.2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact h.1
  · exact fun j hj i hi => hS.2.1 j hj i hi
  · exact fun j hj h1 h2 => hS.2.2 j hj h1 h2
  · show G'.length ≤ _
    revert hlen2 hPlen hP0 hk0 hs0
    generalize cc n m C C.gates.length = k0
    generalize C.gates.length = s0
    generalize G'.length = g
    generalize P.length = p
    intro hlen2 hPlen hP0 hk0 hs0
    by_cases hz0 : k0 = 0
    · have hp := hP0 hz0
      subst hz0
      have h3 : s ≤ (6 * k + 3) * s := Nat.le_mul_of_pos_left s (by omega)
      omega
    · have h1k : 1 ≤ k0 := Nat.one_le_iff_ne_zero.mpr hz0
      have hsq : k0 ≤ k0 ^ 2 := by nlinarith
      have hA : g ≤ (6 * k0 + 3) * s0 + 12 * k0 ^ 2 * m + 7 * k0 * m + 6 * k0 ^ 2 + 2 * k0 := by
        nlinarith [Nat.zero_le (k0 * s0), Nat.zero_le (k0 ^ 2 * m), Nat.zero_le (k0 * m)]
      have hB : (6 * k0 + 3) * s0 + 12 * k0 ^ 2 * m + 7 * k0 * m + 6 * k0 ^ 2 + 2 * k0 ≤
          (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k := by
        gcongr
      exact le_trans hA hB
  · have hsub : {j : ℕ | j < G'.length ∧ 0 < dg n m G' (n + m + j)} ⊆
        ↑(Finset.Ico P.length G'.length) := by
      intro j hj0
      have hj : j < G'.length ∧ 0 < dg n m G' (n + m + j) := hj0
      rw [Finset.mem_coe, Finset.mem_Ico]
      refine ⟨?_, hj.1⟩
      by_contra hlt
      have := hdz j (by omega)
      omega
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Nat.card_Ico] at h1
    have h2 : cc n m C C.gates.length * (2 * m) ≤ k * (2 * m + 1) := Nat.mul_le_mul hk0 (by omega)
    show Set.ncard {j : ℕ | j < G'.length ∧ 0 < dg n m G' (n + m + j)} ≤ _
    omega
  · intro x Y
    by_cases ho : C.output < n + m + C.gates.length
    · have hc := (hρ C.output ho).2 x (fun l => decide (l ∈ Y))
      have e1 : PEqualNP.MetaComplexity.circuitFun (n + m)
          ⟨G', if C.output < n + m + C.gates.length then ρ C.output else n + m + G'.length⟩
          (Fin.append x (fun l => decide (l ∈ Y))) =
          vl G' (inp x (fun l => decide (l ∈ Y))) (ρ C.output) := by
        rw [if_pos ho]
        rfl
      rw [e1, hc]
      show env C C.output x _ = (vC C x (fun _ : Fin m => false) C.output ||
        decide (∃ j ∈ Y, vC C x (fun l : Fin m => decide (l = j)) C.output = true))
      unfold env
      congr 1
      simp
    · have e1 : PEqualNP.MetaComplexity.circuitFun (n + m)
          ⟨G', if C.output < n + m + C.gates.length then ρ C.output else n + m + G'.length⟩
          (Fin.append x (fun l => decide (l ∈ Y))) = false := by
        rw [if_neg ho]
        show gv false Φb G' (inp x _) (n + m + G'.length) = false
        exact gv_oob _ _ _ _ _ (le_of_eq (by rw [inp_len]))
      have hv : ∀ y : Fin m → Bool,
          PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x y) = false :=
        fun y => vC_oob C x y C.output (by omega)
      rw [e1]
      simp [hv]

end PEqualNP.Outside.L_meta_1623

theorem PEqualNP.Outside.L_meta_1623 : ∀ (n m s k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + k * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true)) := by
  exact PEqualNP.Outside.L_meta_1623.main_thm
