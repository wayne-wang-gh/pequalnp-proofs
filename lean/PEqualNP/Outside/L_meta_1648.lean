import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1648

lemma ifp {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

lemma ifn {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ifp hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ifn hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def gA (gs : List Gate) (j : ℕ) : Gate := gs.getD j ⟨GateOp.or, []⟩

lemma gA_eq {gs : List Gate} {j : ℕ} (hj : j < gs.length) : gA gs j = gs[j] := by
  simp [gA, List.getD_eq_getElem?_getD, hj]

lemma gA_mem {gs : List Gate} {j : ℕ} (hj : j < gs.length) : gA gs j ∈ gs := by
  rw [gA_eq hj]; exact List.getElem_mem hj

def V {N : ℕ} (gs : List Gate) (z : Fin N → Bool) (u : ℕ) : Bool :=
  (gs.foldl stepWire (List.ofFn z)).getD u false

lemma V_input {N : ℕ} (gs : List Gate) (z : Fin N → Bool) {u : ℕ} (hu : u < N) :
    V gs z u = z ⟨u, hu⟩ := by
  unfold V
  rw [foldl_getD_lt _ _ _ (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma V_ge {N : ℕ} (gs : List Gate) (z : Fin N → Bool) {u : ℕ} (hu : N + gs.length ≤ u) :
    V gs z u = false := by
  unfold V
  apply getD_ge
  rw [foldl_length]
  simpa using hu

lemma V_gate {N : ℕ} (gs : List Gate) (z : Fin N → Bool) {j : ℕ} (hj : j < gs.length) :
    V gs z (N + j) = (gA gs j).op.eval ((gA gs j).inputs.map fun i =>
      if i < N + j then V gs z i else false) := by
  rw [gA_eq hj]
  have key := foldl_getD_gate gs (List.ofFn z) j hj
  rw [List.length_ofFn] at key
  exact key

lemma and_eval {α : Type} (l : List α) (f : α → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

lemma or_eval {α : Type} (l : List α) (f : α → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

lemma monoB {N : ℕ} (gs : List Gate) (P : (Fin N → Bool) → Prop) (B : ℕ)
    (hop : ∀ k < gs.length, (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or ∨
      (gA gs k).op = GateOp.not)
    (hn : ∀ k < gs.length, N + k < B → (gA gs k).op = GateOp.not →
      ∀ x : Fin N → Bool, P x → V gs x (N + k) = true) :
    ∀ i, i < B → ∀ x x' : Fin N → Bool, P x → P x' → (∀ v, x v = true → x' v = true) →
      V gs x i = true → V gs x' i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiB x x' hx hx' hle hv
    by_cases h1 : i < N
    · rw [V_input gs x h1] at hv
      rw [V_input gs x' h1]
      exact hle _ hv
    · by_cases h2 : N + gs.length ≤ i
      · rw [V_ge gs x h2] at hv
        exact absurd hv (by decide)
      · obtain ⟨k, rfl⟩ : ∃ k, i = N + k := ⟨i - N, by omega⟩
        have hk : k < gs.length := by omega
        rcases hop k hk with ho | ho | ho
        · rw [V_gate gs x hk, ho, and_eval] at hv
          rw [V_gate gs x' hk, ho, and_eval]
          intro a ha
          have hva := hv a ha
          by_cases hlt : a < N + k
          · rw [ifp hlt] at hva ⊢
            exact ih a hlt (by omega) x x' hx hx' hle hva
          · rw [ifn hlt] at hva
            exact absurd hva (by decide)
        · rw [V_gate gs x hk, ho, or_eval] at hv
          rw [V_gate gs x' hk, ho, or_eval]
          obtain ⟨a, ha, hav⟩ := hv
          refine ⟨a, ha, ?_⟩
          by_cases hlt : a < N + k
          · rw [ifp hlt] at hav ⊢
            exact ih a hlt (by omega) x x' hx hx' hle hav
          · rw [ifn hlt] at hav
            exact absurd hav (by decide)
        · exact hn k hk hiB ho x' hx'

lemma not_val {N : ℕ} (gs : List Gate) (j h : ℕ) (hj : j < gs.length) (hhj : h < j)
    (hop : (gA gs j).op = GateOp.not) (r : List ℕ) (hin : (gA gs j).inputs = (N + h) :: r)
    (x : Fin N → Bool) : V gs x (N + j) = !V gs x (N + h) := by
  rw [V_gate gs x hj, hop, hin]
  simp only [List.map_cons, GateOp.eval, List.headD_cons]
  rw [ifp (by omega : N + h < N + j)]

lemma main {N : ℕ} (M : Finset (Fin N)) (p0 p1 : Fin N) (gs : List Gate) (j h : ℕ)
    (hj : j < gs.length) (hhj : h < j)
    (hop : ∀ k < gs.length, (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or ∨
      (gA gs k).op = GateOp.not)
    (hjn : (gA gs j).op = GateOp.not)
    (huniq : ∀ k < gs.length, (gA gs k).op = GateOp.not → k = j)
    (r : List ℕ) (hin : (gA gs j).inputs = (N + h) :: r)
    (h0 : V gs (fun v => decide (v = p0)) (N + h) = true)
    (h1 : V gs (fun v => decide (v = p1)) (N + h) = true)
    (hp : ∀ p : Fin N, p ≠ p0 → p ≠ p1 → V gs (fun v => decide (v = p)) (N + h) = false)
    (hW : V gs (fun v => decide (v ∉ M)) (N + h) = false) :
    (∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ M) →
      V gs x (N + h) = false ∧ V gs x (N + j) = true) ∧
    (∀ w ∈ M, w ≠ p0 → w ≠ p1 → V gs (fun v => decide (v = w)) (N + h) = false ∧
      V gs (fun v => decide (v = w)) (N + j) = true) ∧
    V gs (fun v => decide (v = p0)) (N + j) = false ∧
    V gs (fun v => decide (v = p1)) (N + j) = false ∧
    ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ M) →
      (∀ v : Fin N, y v = true → v ∉ M) → (∀ v : Fin N, x v = true → y v = true) →
      V gs x w = true → V gs y w = true := by
  have nv := not_val gs j h hj hhj hjn r hin
  have A : ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ M) →
      V gs x (N + h) = false ∧ V gs x (N + j) = true := by
    intro x hx
    have hf : V gs x (N + h) = false := by
      by_contra hc
      have ht : V gs x (N + h) = true := by simpa using hc
      have h3 := monoB gs (fun _ => True) (N + j) hop
        (fun k hk hlt ho => absurd (huniq k hk ho) (by omega)) (N + h) (by omega) x
        (fun v => decide (v ∉ M)) trivial trivial (fun v hv => by simpa using hx v hv) ht
      rw [hW] at h3
      exact absurd h3 (by decide)
    exact ⟨hf, by simp [nv, hf]⟩
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro w _ hw0 hw1
    have hf := hp w hw0 hw1
    exact ⟨hf, by simp [nv, hf]⟩
  · simp [nv, h0]
  · simp [nv, h1]
  · intro w x y hx hy hle hv
    exact monoB gs (fun z => ∀ v : Fin N, z v = true → v ∉ M) (w + 1) hop
      (fun k hk _ ho x' hx' => by rw [huniq k hk ho]; exact (A x' hx').2)
      w (by omega) x y hx hy hle hv

lemma cover {α : Type} [DecidableEq α] (n : ℕ) (R : ℕ → Prop) (Vv : ℕ → Finset α) (K : Finset ℕ)
    (hstep : ∀ w < n, R w → ∃ S : Finset (Finset α),
        (∀ A ∈ S, A.card ≤ 1 ∨ ∃ w' < w, R w' ∧ A ⊆ Vv w') ∧ Vv w ⊆ S.biUnion id ∧
        (S.card ≤ 1 ∨ (S.card ≤ 2 ∧ w ∈ K))) :
    ∀ m ≤ n, ∀ C : Finset (Finset α), (∀ A ∈ C, A.card ≤ 1 ∨ ∃ w' < m, R w' ∧ A ⊆ Vv w') →
      (C.biUnion id).card ≤ C.card + (K.filter (fun w => w < m)).card := by
  classical
  intro m
  induction m with
  | zero =>
    intro _ C hC
    have h1 : ∀ A ∈ C, A.card ≤ 1 := by
      intro A hA
      rcases hC A hA with h | ⟨w', hw', _⟩
      · exact h
      · exact absurd hw' (Nat.not_lt_zero _)
    have h2 : (C.biUnion id).card ≤ ∑ A ∈ C, (id A).card := Finset.card_biUnion_le
    have h3 : ∑ A ∈ C, (id A).card ≤ ∑ _A ∈ C, 1 := Finset.sum_le_sum (fun A hA => h1 A hA)
    have h4 : ∑ _A ∈ C, 1 = C.card := by simp
    omega
  | succ m ih =>
    intro hm C hC
    have hK : (K.filter (fun w => w < m)).card ≤ (K.filter (fun w => w < m + 1)).card :=
      Finset.card_le_card (fun w hw => by
        rw [Finset.mem_filter] at hw ⊢
        exact ⟨hw.1, by omega⟩)
    by_cases hall : ∀ A ∈ C, A.card ≤ 1 ∨ ∃ w' < m, R w' ∧ A ⊆ Vv w'
    · have := ih (by omega) C hall
      omega
    · obtain ⟨A0, hA0, hnot⟩ : ∃ A0 ∈ C, ¬ (A0.card ≤ 1 ∨ ∃ w' < m, R w' ∧ A0 ⊆ Vv w') := by
        by_contra hc
        exact hall (fun A hA => by
          by_contra hh
          exact hc ⟨A, hA, hh⟩)
      have hRm : R m := by
        rcases hC A0 hA0 with h | ⟨w', hw', hR, hsub⟩
        · exact absurd (Or.inl h) hnot
        · by_cases e : w' = m
          · subst e
            exact hR
          · exact absurd (Or.inr ⟨w', by omega, hR, hsub⟩) hnot
      obtain ⟨S, hSg, hScov, hScard⟩ := hstep m (by omega) hRm
      obtain ⟨C1, hC1⟩ : ∃ C1 : Finset (Finset α),
          C1 = C.filter (fun A => A.card ≤ 1 ∨ ∃ w' < m, R w' ∧ A ⊆ Vv w') := ⟨_, rfl⟩
      have hC1lt : C1.card < C.card := by
        rw [hC1]
        exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨A0, hA0, hnot⟩)
      have hgood : ∀ A ∈ C1 ∪ S, A.card ≤ 1 ∨ ∃ w' < m, R w' ∧ A ⊆ Vv w' := by
        intro A hA
        rcases Finset.mem_union.mp hA with h | h
        · rw [hC1] at h
          exact (Finset.mem_filter.mp h).2
        · exact hSg A h
      have hsub : C.biUnion id ⊆ (C1 ∪ S).biUnion id := by
        intro p hp
        rw [Finset.mem_biUnion] at hp ⊢
        obtain ⟨A, hA, hpA⟩ := hp
        by_cases hgA : A.card ≤ 1 ∨ ∃ w' < m, R w' ∧ A ⊆ Vv w'
        · refine ⟨A, Finset.mem_union_left _ ?_, hpA⟩
          rw [hC1]
          exact Finset.mem_filter.mpr ⟨hA, hgA⟩
        · have hAm : A ⊆ Vv m := by
            rcases hC A hA with h | ⟨w', hw', hR, hs⟩
            · exact absurd (Or.inl h) hgA
            · by_cases e : w' = m
              · subst e
                exact hs
              · exact absurd (Or.inr ⟨w', by omega, hR, hs⟩) hgA
          have hpm : p ∈ S.biUnion id := hScov (hAm hpA)
          rw [Finset.mem_biUnion] at hpm
          obtain ⟨B, hB, hpB⟩ := hpm
          exact ⟨B, Finset.mem_union_right _ hB, hpB⟩
      have h1 := ih (by omega) (C1 ∪ S) hgood
      have h2 := Finset.card_le_card hsub
      have h3 : (C1 ∪ S).card ≤ C1.card + S.card := Finset.card_union_le _ _
      have hK2 : S.card ≤ 1 ∨ ((K.filter (fun w => w < m)).card + 1 ≤
          (K.filter (fun w => w < m + 1)).card ∧ S.card ≤ 2) := by
        rcases hScard with h | ⟨h, hmK⟩
        · left
          exact h
        · right
          refine ⟨?_, h⟩
          have hnm : m ∉ K.filter (fun w => w < m) := by
            intro hmem
            rw [Finset.mem_filter] at hmem
            omega
          have hss : insert m (K.filter (fun w => w < m)) ⊆ K.filter (fun w => w < m + 1) := by
            intro w hw
            rw [Finset.mem_insert] at hw
            rw [Finset.mem_filter]
            rcases hw with hw | hw
            · rw [hw]
              exact ⟨hmK, by omega⟩
            · rw [Finset.mem_filter] at hw
              exact ⟨hw.1, by omega⟩
          have hle := Finset.card_le_card hss
          rw [Finset.card_insert_of_notMem hnm] at hle
          exact hle
      omega

def ep {N : ℕ} (p : Fin N) : Fin N → Bool := fun v => decide (v = p)

def Ft {N : ℕ} (M T : Finset (Fin N)) : Fin N → Bool := fun v => decide (v ∉ M ∧ v ∉ T)

def Semi {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (w : ℕ) : Prop :=
  V gs (Ft M T) w = false

def Cond {N : ℕ} (T : Finset (Fin N)) (p0 p1 m : Fin N) : Prop :=
  (m ≠ p0 ∧ m ≠ p1) ∨ p0 ∈ T ∨ p1 ∈ T

def Dst {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (p0 p1 : Fin N) (w : ℕ) : Prop :=
  Semi gs M T w ∧ ∀ m ∈ M, m ∉ T → Cond T p0 p1 m → V gs (ep m) w = false

noncomputable def Vt {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (p0 p1 : Fin N) (w : ℕ) :
    Finset (Fin N) :=
  @Finset.filter _ (fun p => V gs (ep p) w = true ∧ (Dst gs M T p0 p1 w ∨ p ∉ M))
    (Classical.decPred _) T

lemma mem_Vt {N : ℕ} {gs : List Gate} {M T : Finset (Fin N)} {p0 p1 : Fin N} {w : ℕ} {p : Fin N} :
    p ∈ Vt gs M T p0 p1 w ↔ p ∈ T ∧ V gs (ep p) w = true ∧ (Dst gs M T p0 p1 w ∨ p ∉ M) := by
  unfold Vt
  exact @Finset.mem_filter _ _ (Classical.decPred _) _ _

def ChO {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (p0 p1 : Fin N) (k : ℕ) : Prop :=
  (gA gs k).op = GateOp.or ∧ Semi gs M T (N + k) ∧ (Vt gs M T p0 p1 (N + k)).Nonempty ∧
    ∀ e ∈ (gA gs k).inputs, ¬ Vt gs M T p0 p1 (N + k) ⊆ Vt gs M T p0 p1 e

def ChA {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (p0 p1 : Fin N) (j k : ℕ) : Prop :=
  (gA gs k).op = GateOp.and ∧ Dst gs M T p0 p1 (N + k) ∧ N + j ∉ (gA gs k).inputs ∧
    (∃ p ∈ T, p ∈ M ∧ V gs (ep p) (N + k) = true) ∧ (∃ p ∈ T, p ∉ M ∧ V gs (ep p) (N + k) = true)

def Ch {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (p0 p1 : Fin N) (j k : ℕ) : Prop :=
  ChO gs M T p0 p1 k ∨ ChA gs M T p0 p1 j k

lemma orv {N : ℕ} (gs : List Gate) (x : Fin N → Bool) {k : ℕ} (hk : k < gs.length)
    (ho : (gA gs k).op = GateOp.or) (hin : ∀ w ∈ (gA gs k).inputs, w < N + k) :
    V gs x (N + k) = true ↔ ∃ e ∈ (gA gs k).inputs, V gs x e = true := by
  rw [V_gate gs x hk, ho, or_eval]
  constructor
  · intro hv
    obtain ⟨e, he, hev⟩ := hv
    rw [ifp (hin e he)] at hev
    exact ⟨e, he, hev⟩
  · intro hv
    obtain ⟨e, he, hev⟩ := hv
    refine ⟨e, he, ?_⟩
    rw [ifp (hin e he)]
    exact hev

lemma andv {N : ℕ} (gs : List Gate) (x : Fin N → Bool) {k : ℕ} (hk : k < gs.length)
    (ho : (gA gs k).op = GateOp.and) (hin : ∀ w ∈ (gA gs k).inputs, w < N + k) :
    V gs x (N + k) = true ↔ ∀ e ∈ (gA gs k).inputs, V gs x e = true := by
  rw [V_gate gs x hk, ho, and_eval]
  constructor
  · intro hv e he
    have hev := hv e he
    rw [ifp (hin e he)] at hev
    exact hev
  · intro hv e he
    rw [ifp (hin e he)]
    exact hv e he

lemma orF {N : ℕ} (gs : List Gate) (x : Fin N → Bool) {k : ℕ} (hk : k < gs.length)
    (ho : (gA gs k).op = GateOp.or) (hin : ∀ w ∈ (gA gs k).inputs, w < N + k)
    (hf : V gs x (N + k) = false) : ∀ e ∈ (gA gs k).inputs, V gs x e = false := by
  intro e he
  by_contra hc
  have ht : V gs x e = true := by simpa using hc
  have h2 := (orv gs x hk ho hin).mpr ⟨e, he, ht⟩
  rw [hf] at h2
  exact absurd h2 (by decide)

lemma two (l : List ℕ) (hl : l.length ≤ 2) {a z : ℕ} (ha : a ∈ l) (hz : z ∈ l) (hne : a ≠ z) :
    ∀ e ∈ l, e = a ∨ e = z := by
  intro e he
  rcases l with _ | ⟨u, _ | ⟨v, _ | ⟨x, r⟩⟩⟩
  · simp at ha
  · simp at ha hz
    omega
  · simp at ha hz he
    omega
  · have hh : (u :: v :: x :: r).length = r.length + 3 := rfl
    omega

lemma ML {N : ℕ} (gs : List Gate) (M : Finset (Fin N))
    (hmW : ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ M) →
      (∀ v : Fin N, y v = true → v ∉ M) → (∀ v : Fin N, x v = true → y v = true) →
      V gs x w = true → V gs y w = true)
    {T' : Finset (Fin N)} {w : ℕ} (hs : Semi gs M T' w) {p : Fin N} (hpM : p ∉ M) (hpT : p ∉ T') :
    V gs (ep p) w = false := by
  by_contra hc
  have ht : V gs (ep p) w = true := by simpa using hc
  have h3 := hmW w (ep p) (Ft M T')
    (fun v hv => by
      have e : v = p := of_decide_eq_true hv
      rw [e]
      exact hpM)
    (fun v hv => (of_decide_eq_true hv : v ∉ M ∧ v ∉ T').1)
    (fun v hv => by
      have e : v = p := of_decide_eq_true hv
      rw [e]
      exact decide_eq_true ⟨hpM, hpT⟩) ht
  have hs' : V gs (Ft M T') w = false := hs
  rw [hs'] at h3
  exact absurd h3 (by decide)

lemma orcov {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (p0 p1 : Fin N) {k : ℕ}
    (hin : ∀ w ∈ (gA gs k).inputs, w < N + k) (hk : k < gs.length)
    (ho : (gA gs k).op = GateOp.or) {p : Fin N} (hp : p ∈ Vt gs M T p0 p1 (N + k)) :
    ∃ e ∈ (gA gs k).inputs, p ∈ Vt gs M T p0 p1 e := by
  rw [mem_Vt] at hp
  obtain ⟨hpT, hv, hd⟩ := hp
  obtain ⟨e, he, hev⟩ := (orv gs (ep p) hk ho hin).mp hv
  refine ⟨e, he, ?_⟩
  rw [mem_Vt]
  refine ⟨hpT, hev, ?_⟩
  rcases hd with hd | hd
  · left
    exact ⟨orF gs (Ft M T) hk ho hin hd.1 e he,
      fun m hmM hmT hc => orF gs (ep m) hk ho hin (hd.2 m hmM hmT hc) e he⟩
  · right
    exact hd

lemma key {N : ℕ} (gs : List Gate) (M T T' : Finset (Fin N)) (p0 p1 : Fin N) (w : ℕ)
    (hD : Dst gs M T p0 p1 w) (hD' : Dst gs M T' p0 p1 w)
    {u u2 : Fin N} (huT' : u ∉ T') (huM : u ∈ M) (huv : V gs (ep u) w = true)
    (hu2T : u2 ∉ T) (hu2T' : u2 ∈ T') (hu2M : u2 ∈ M) (hu2v : V gs (ep u2) w = true) : False := by
  have c1 : ¬ Cond T p0 p1 u2 := fun hc => by
    have h := hD.2 u2 hu2M hu2T hc
    rw [hu2v] at h
    exact absurd h (by decide)
  have c2 : ¬ Cond T' p0 p1 u := fun hc => by
    have h := hD'.2 u huM huT' hc
    rw [huv] at h
    exact absurd h (by decide)
  have h0 : p0 ∉ T' := fun h => c2 (Or.inr (Or.inl h))
  have h1 : p1 ∉ T' := fun h => c2 (Or.inr (Or.inr h))
  by_cases e0 : u2 = p0
  · rw [e0] at hu2T'
    exact h0 hu2T'
  · by_cases e1 : u2 = p1
    · rw [e1] at hu2T'
      exact h1 hu2T'
    · exact c1 (Or.inl ⟨e0, e1⟩)

lemma osplit {N : ℕ} (gs : List Gate) (M T T' : Finset (Fin N)) (p0 p1 : Fin N)
    (hin : ∀ k < gs.length, ∀ w ∈ (gA gs k).inputs, w < N + k)
    (hTT : ∀ a ∈ T, a ∈ T' → ∀ b ∈ T, b ∈ T' → a = b)
    {k : ℕ} (hk : k < gs.length) (h : ChO gs M T p0 p1 k) :
    ∃ u ∈ Vt gs M T p0 p1 (N + k), u ∉ T' := by
  obtain ⟨ho, _, ⟨u, hu⟩, hstrict⟩ := h
  obtain ⟨e, he, hue⟩ := orcov gs M T p0 p1 (hin k hk) hk ho hu
  have hns := hstrict e he
  rw [Finset.not_subset] at hns
  obtain ⟨u', hu', hu'e⟩ := hns
  by_cases c : u ∈ T'
  · by_cases c' : u' ∈ T'
    · exfalso
      have hT : u ∈ T := (mem_Vt.mp hu).1
      have hT' : u' ∈ T := (mem_Vt.mp hu').1
      have e2 := hTT u hT c u' hT' c'
      rw [e2] at hue
      exact hu'e hue
    · exact ⟨u', hu', c'⟩
  · exact ⟨u, hu, c⟩

lemma disj {N : ℕ} (gs : List Gate) (M T T' : Finset (Fin N)) (p0 p1 : Fin N) (j : ℕ)
    (hin : ∀ k < gs.length, ∀ w ∈ (gA gs k).inputs, w < N + k)
    (hmW : ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ M) →
      (∀ v : Fin N, y v = true → v ∉ M) → (∀ v : Fin N, x v = true → y v = true) →
      V gs x w = true → V gs y w = true)
    (hTT : ∀ a ∈ T, a ∈ T' → ∀ b ∈ T, b ∈ T' → a = b)
    {k : ℕ} (hk : k < gs.length) (h : Ch gs M T p0 p1 j k) (h' : Ch gs M T' p0 p1 j k) : False := by
  rcases h with h | h <;> rcases h' with h' | h'
  · obtain ⟨u, huV, huT'⟩ := osplit gs M T T' p0 p1 hin hTT hk h
    obtain ⟨u2, hu2V, hu2T⟩ := osplit gs M T' T p0 p1 hin
      (fun a ha ha' b hb hb' => hTT a ha' ha b hb' hb) hk h'
    rw [mem_Vt] at huV hu2V
    have huM : u ∈ M := by
      by_contra hn
      have h3 := ML gs M hmW h'.2.1 hn huT'
      rw [huV.2.1] at h3
      exact absurd h3 (by decide)
    have hu2M : u2 ∈ M := by
      by_contra hn
      have h3 := ML gs M hmW h.2.1 hn hu2T
      rw [hu2V.2.1] at h3
      exact absurd h3 (by decide)
    have hD : Dst gs M T p0 p1 (N + k) := by
      rcases huV.2.2 with hd | hd
      · exact hd
      · exact absurd huM hd
    have hD' : Dst gs M T' p0 p1 (N + k) := by
      rcases hu2V.2.2 with hd | hd
      · exact hd
      · exact absurd hu2M hd
    exact key gs M T T' p0 p1 (N + k) hD hD' huT' huM huV.2.1 hu2T hu2V.1 hu2M hu2V.2.1
  · have e1 := h.1
    have e2 := h'.1
    rw [e1] at e2
    cases e2
  · have e1 := h.1
    have e2 := h'.1
    rw [e1] at e2
    cases e2
  · obtain ⟨_, hD, _, ⟨a, haT, haM, hav⟩, ⟨w, hwT, hwM, hwv⟩⟩ := h
    obtain ⟨_, hD', _, ⟨a', haT', haM', hav'⟩, ⟨w', hwT', hwM', hwv'⟩⟩ := h'
    have hwT2 : w ∈ T' := by
      by_contra hn
      have h3 := ML gs M hmW hD'.1 hwM hn
      rw [hwv] at h3
      exact absurd h3 (by decide)
    have hw'T2 : w' ∈ T := by
      by_contra hn
      have h3 := ML gs M hmW hD.1 hwM' hn
      rw [hwv'] at h3
      exact absurd h3 (by decide)
    have haT2 : a ∉ T' := by
      intro hc
      have e2 := hTT a haT hc w hwT hwT2
      rw [e2] at haM
      exact hwM haM
    have ha'T2 : a' ∉ T := by
      intro hc
      have e2 := hTT a' hc haT' w' hw'T2 hwT'
      rw [e2] at haM'
      exact hwM' haM'
    exact key gs M T T' p0 p1 (N + k) hD hD' haT2 haM hav ha'T2 haT' haM' hav'

lemma step {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (p0 p1 : Fin N) (j : ℕ)
    (hop : ∀ k < gs.length, (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or ∨
      (gA gs k).op = GateOp.not)
    (hlen : ∀ k < gs.length, (gA gs k).inputs.length ≤ 2)
    (hin : ∀ k < gs.length, ∀ w ∈ (gA gs k).inputs, w < N + k)
    (huniq : ∀ k < gs.length, (gA gs k).op = GateOp.not → k = j)
    (hzW : ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ M) → V gs x (N + j) = true)
    (hzM : ∀ m ∈ M, m ≠ p0 → m ≠ p1 → V gs (ep m) (N + j) = true)
    (hz0 : V gs (ep p0) (N + j) = false) (hz1 : V gs (ep p1) (N + j) = false)
    (hp0 : p0 ∈ M) (hp1 : p1 ∈ M)
    (hTM : T ≠ M → ∀ a ∈ T, a ∈ M → ∀ b ∈ T, b ∈ M → a = b) :
    ∀ w < N + gs.length, Semi gs M T w → ∃ S : Finset (Finset (Fin N)),
      (∀ A ∈ S, A.card ≤ 1 ∨ ∃ w' < w, Semi gs M T w' ∧ A ⊆ Vt gs M T p0 p1 w') ∧
      Vt gs M T p0 p1 w ⊆ S.biUnion id ∧
      (S.card ≤ 1 ∨ (S.card ≤ 2 ∧ N ≤ w ∧ Ch gs M T p0 p1 j (w - N))) := by
  classical
  intro w hw hs
  have single : ((Vt gs M T p0 p1 w).card ≤ 1 ∨
      ∃ w' < w, Semi gs M T w' ∧ Vt gs M T p0 p1 w ⊆ Vt gs M T p0 p1 w') →
      ∃ S : Finset (Finset (Fin N)),
      (∀ A ∈ S, A.card ≤ 1 ∨ ∃ w' < w, Semi gs M T w' ∧ A ⊆ Vt gs M T p0 p1 w') ∧
      Vt gs M T p0 p1 w ⊆ S.biUnion id ∧
      (S.card ≤ 1 ∨ (S.card ≤ 2 ∧ N ≤ w ∧ Ch gs M T p0 p1 j (w - N))) := by
    intro hgood
    refine ⟨{Vt gs M T p0 p1 w}, ?_, ?_, ?_⟩
    · intro A hA
      rw [Finset.mem_singleton] at hA
      rw [hA]
      exact hgood
    · intro p hp
      rw [Finset.mem_biUnion]
      exact ⟨_, Finset.mem_singleton_self _, hp⟩
    · left
      rw [Finset.card_singleton]
  have hzF : V gs (Ft M T) (N + j) = true :=
    hzW (Ft M T) (fun v hv => (of_decide_eq_true hv : v ∉ M ∧ v ∉ T).1)
  by_cases h1 : w < N
  · apply single
    left
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [mem_Vt] at ha hb
    have ea : V gs (ep a) w = true := ha.2.1
    have eb : V gs (ep b) w = true := hb.2.1
    rw [V_input gs _ h1] at ea eb
    have e1 : (⟨w, h1⟩ : Fin N) = a := of_decide_eq_true ea
    have e2 : (⟨w, h1⟩ : Fin N) = b := of_decide_eq_true eb
    exact e1.symm.trans e2
  · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
    have hk : k < gs.length := by omega
    have hsF : V gs (Ft M T) (N + k) = false := hs
    rcases hop k hk with ho | ho | ho
    · obtain ⟨a, ha, haS⟩ : ∃ a ∈ (gA gs k).inputs, V gs (Ft M T) a = false := by
        by_contra hc
        have hall : ∀ e ∈ (gA gs k).inputs, V gs (Ft M T) e = true := by
          intro e he
          by_contra hh
          exact hc ⟨e, he, by simpa using hh⟩
        have h2 := (andv gs (Ft M T) hk ho (hin k hk)).mpr hall
        rw [hsF] at h2
        exact absurd h2 (by decide)
      have halt : a < N + k := hin k hk a ha
      have hPa : ∀ p : Fin N, V gs (ep p) (N + k) = true → V gs (ep p) a = true :=
        fun p hp => (andv gs (ep p) hk ho (hin k hk)).mp hp a ha
      have hcardTM : T ≠ M → (T ∩ M).card ≤ 1 := by
        intro hne
        rw [Finset.card_le_one]
        intro x hx y hy
        rw [Finset.mem_inter] at hx hy
        exact hTM hne x hx.1 hx.2 y hy.1 hy.2
      by_cases hc : ChA gs M T p0 p1 j k
      · have hc' := hc
        obtain ⟨_, _, _, _, ⟨pw, hpwT, hpwM, _⟩⟩ := hc
        have hne : T ≠ M := by
          intro e
          rw [e] at hpwT
          exact hpwM hpwT
        refine ⟨{Vt gs M T p0 p1 a, T ∩ M}, ?_, ?_,
          Or.inr ⟨Finset.card_le_two, Nat.le_add_right N k, ?_⟩⟩
        · intro A hA
          rw [Finset.mem_insert, Finset.mem_singleton] at hA
          rcases hA with hA | hA
          · right
            rw [hA]
            exact ⟨a, halt, haS, Finset.Subset.refl _⟩
          · left
            rw [hA]
            exact hcardTM hne
        · intro p hp
          rw [mem_Vt] at hp
          rw [Finset.mem_biUnion]
          by_cases hpM : p ∈ M
          · exact ⟨T ∩ M, by simp, Finset.mem_inter.mpr ⟨hp.1, hpM⟩⟩
          · refine ⟨Vt gs M T p0 p1 a, by simp, ?_⟩
            show p ∈ Vt gs M T p0 p1 a
            rw [mem_Vt]
            exact ⟨hp.1, hPa p hp.2.1, Or.inr hpM⟩
        · rw [Nat.add_sub_cancel_left]
          exact Or.inr hc'
      · apply single
        by_cases hDa : Dst gs M T p0 p1 a
        · right
          refine ⟨a, halt, haS, fun p hp => ?_⟩
          rw [mem_Vt] at hp ⊢
          exact ⟨hp.1, hPa p hp.2.1, Or.inl hDa⟩
        · by_cases hDg : Dst gs M T p0 p1 (N + k)
          · by_cases hm1 : ∃ p ∈ T, p ∈ M ∧ V gs (ep p) (N + k) = true
            · by_cases hm2 : ∃ p ∈ T, p ∉ M ∧ V gs (ep p) (N + k) = true
              · exfalso
                have hzin : N + j ∈ (gA gs k).inputs := by
                  by_contra hni
                  exact hc ⟨ho, hDg, hni, hm1, hm2⟩
                obtain ⟨pm, hpmT, hpmM, hpmv⟩ := hm1
                obtain ⟨pw, hpwT, hpwM, _⟩ := hm2
                have hne : T ≠ M := by
                  intro e
                  rw [e] at hpwT
                  exact hpwM hpwT
                have hzpm : V gs (ep pm) (N + j) = true :=
                  (andv gs (ep pm) hk ho (hin k hk)).mp hpmv _ hzin
                have hpm0 : pm ≠ p0 := by
                  intro e
                  rw [e, hz0] at hzpm
                  exact absurd hzpm (by decide)
                have hpm1 : pm ≠ p1 := by
                  intro e
                  rw [e, hz1] at hzpm
                  exact absurd hzpm (by decide)
                have hane : a ≠ N + j := by
                  intro e
                  rw [e, hzF] at haS
                  exact absurd haS (by decide)
                have htwo : ∀ e ∈ (gA gs k).inputs, e = a ∨ e = N + j :=
                  two _ (hlen k hk) ha hzin hane
                apply hDa
                refine ⟨haS, fun m hmM hmT hcond => ?_⟩
                by_contra hh
                have hat : V gs (ep m) a = true := by simpa using hh
                have hzm : V gs (ep m) (N + j) = true := by
                  by_cases hm0 : m = p0 ∨ m = p1
                  · exfalso
                    have hin2 : p0 ∈ T ∨ p1 ∈ T := by
                      rcases hcond with ⟨c0, c1⟩ | c
                      · rcases hm0 with e | e
                        · exact absurd e c0
                        · exact absurd e c1
                      · exact c
                    rcases hin2 with c | c
                    · exact hpm0 (hTM hne pm hpmT hpmM p0 c hp0)
                    · exact hpm1 (hTM hne pm hpmT hpmM p1 c hp1)
                  · exact hzM m hmM (fun e => hm0 (Or.inl e)) (fun e => hm0 (Or.inr e))
                have hgt : V gs (ep m) (N + k) = true :=
                  (andv gs (ep m) hk ho (hin k hk)).mpr (fun e he => by
                    rcases htwo e he with e1 | e1
                    · rw [e1]
                      exact hat
                    · rw [e1]
                      exact hzm)
                rw [hDg.2 m hmM hmT hcond] at hgt
                exact absurd hgt (by decide)
              · left
                have hne : T ≠ M := by
                  intro e
                  apply hDa
                  refine ⟨haS, fun m hmM hmT _ => ?_⟩
                  rw [e] at hmT
                  exact absurd hmM hmT
                refine le_trans (Finset.card_le_card (t := T ∩ M) ?_) (hcardTM hne)
                intro p hp
                rw [mem_Vt] at hp
                rw [Finset.mem_inter]
                refine ⟨hp.1, ?_⟩
                by_contra hpM
                exact hm2 ⟨p, hp.1, hpM, hp.2.1⟩
            · right
              refine ⟨a, halt, haS, fun p hp => ?_⟩
              rw [mem_Vt] at hp ⊢
              have hpM : p ∉ M := fun hpM => hm1 ⟨p, hp.1, hpM, hp.2.1⟩
              exact ⟨hp.1, hPa p hp.2.1, Or.inr hpM⟩
          · right
            refine ⟨a, halt, haS, fun p hp => ?_⟩
            rw [mem_Vt] at hp ⊢
            rcases hp.2.2 with hd | hpM
            · exact absurd hd hDg
            · exact ⟨hp.1, hPa p hp.2.1, Or.inr hpM⟩
    · have hinS : ∀ e ∈ (gA gs k).inputs, Semi gs M T e :=
        orF gs (Ft M T) hk ho (hin k hk) hsF
      by_cases hc : ChO gs M T p0 p1 k
      · refine ⟨(gA gs k).inputs.toFinset.image (Vt gs M T p0 p1), ?_, ?_,
          Or.inr ⟨?_, Nat.le_add_right N k, ?_⟩⟩
        · intro A hA
          rw [Finset.mem_image] at hA
          obtain ⟨e, he, hAe⟩ := hA
          rw [List.mem_toFinset] at he
          right
          rw [← hAe]
          exact ⟨e, hin k hk e he, hinS e he, Finset.Subset.refl _⟩
        · intro p hp
          obtain ⟨e, he, hpe⟩ := orcov gs M T p0 p1 (hin k hk) hk ho hp
          rw [Finset.mem_biUnion]
          exact ⟨Vt gs M T p0 p1 e, Finset.mem_image_of_mem _ (List.mem_toFinset.mpr he), hpe⟩
        · exact le_trans Finset.card_image_le (le_trans (List.toFinset_card_le _) (hlen k hk))
        · rw [Nat.add_sub_cancel_left]
          exact Or.inl hc
      · apply single
        by_cases hne : (Vt gs M T p0 p1 (N + k)).Nonempty
        · right
          by_contra hno
          apply hc
          exact ⟨ho, hs, hne, fun e he hsub => hno ⟨e, hin k hk e he, hinS e he, hsub⟩⟩
        · left
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          rw [hne]
          simp
    · exfalso
      have e := huniq k hk ho
      rw [e, hzF] at hsF
      exact absurd hsF (by decide)

lemma fin {N q : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hcard : ∀ i : Fin N, (L i).card = q + 1)
    (hint : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (gates : List Gate) (o : Fin N → ℕ) (j h : Fin gates.length)
    (hg : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or ∨ gt.op = GateOp.not) ∧
      gt.inputs.length ≤ 2)
    (hin0 : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (hjn : (gates.get j).op = GateOp.not)
    (huniq0 : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hhj : h < j) (hjin : ∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r)
    (hout : ∀ (t : Fin N) (x : Fin N → Bool),
      V gates x (o t) = decide (∃ v ∈ L t, x v = true))
    (h0 : V gates (fun v : Fin N => decide (v = p0)) (N + (h : ℕ)) = true)
    (h1 : V gates (fun v : Fin N => decide (v = p1)) (N + (h : ℕ)) = true)
    (hp : ∀ p : Fin N, p ≠ p0 → p ≠ p1 →
      V gates (fun v : Fin N => decide (v = p)) (N + (h : ℕ)) = false)
    (hW : V gates (fun v : Fin N => decide (v ∉ L i0)) (N + (h : ℕ)) = false) :
    N * q + (Finset.univ.filter (fun i : Fin gates.length =>
      (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length := by
  classical
  obtain ⟨r, hr⟩ := hjin
  have hop : ∀ k < gates.length, (gA gates k).op = GateOp.and ∨
      (gA gates k).op = GateOp.or ∨ (gA gates k).op = GateOp.not :=
    fun k hk => (hg _ (gA_mem hk)).1
  have hlen : ∀ k < gates.length, (gA gates k).inputs.length ≤ 2 :=
    fun k hk => (hg _ (gA_mem hk)).2
  have hin : ∀ k < gates.length, ∀ w ∈ (gA gates k).inputs, w < N + k := by
    intro k hk w hw
    rw [gA_eq hk] at hw
    exact hin0 ⟨k, hk⟩ w hw
  have hjn' : (gA gates j).op = GateOp.not := by
    rw [gA_eq j.isLt]
    exact hjn
  have huniq : ∀ k < gates.length, (gA gates k).op = GateOp.not → k = j := by
    intro k hk ho
    rw [gA_eq hk] at ho
    exact congrArg Fin.val (huniq0 ⟨k, hk⟩ ho)
  have hr' : (gA gates j).inputs = (N + (h : ℕ)) :: r := by
    rw [gA_eq j.isLt]
    exact hr
  obtain ⟨hzW0, hzM0, hz0, hz1, hmW⟩ :=
    main (L i0) p0 p1 gates j h j.isLt hhj hop hjn' huniq r hr' h0 h1 hp hW
  have hzW : ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) →
      V gates x (N + (j : ℕ)) = true := fun x hx => (hzW0 x hx).2
  have hzM : ∀ m ∈ L i0, m ≠ p0 → m ≠ p1 → V gates (ep m) (N + (j : ℕ)) = true :=
    fun m hm a b => (hzM0 m hm a b).2
  have hsingle : ∀ t t' : Fin N, t ≠ t' →
      ∀ a ∈ L t, a ∈ L t' → ∀ b ∈ L t, b ∈ L t' → a = b := by
    intro t t' hne a ha ha' b hb hb'
    have hc := hint t t' hne
    rw [Finset.card_eq_one] at hc
    obtain ⟨c, hc⟩ := hc
    have ea : a ∈ L t ∩ L t' := Finset.mem_inter.mpr ⟨ha, ha'⟩
    have eb : b ∈ L t ∩ L t' := Finset.mem_inter.mpr ⟨hb, hb'⟩
    rw [hc, Finset.mem_singleton] at ea eb
    rw [ea, eb]
  obtain ⟨A, hA⟩ : ∃ A : Fin N → Finset (Fin gates.length), ∀ t, A t =
      Finset.univ.filter (fun i : Fin gates.length => Ch gates (L i0) (L t) p0 p1 j i) :=
    ⟨_, fun _ => rfl⟩
  have hAq : ∀ t, q ≤ (A t).card := by
    intro t
    have hTM : L t ≠ L i0 → ∀ a ∈ L t, a ∈ L i0 → ∀ b ∈ L t, b ∈ L i0 → a = b := by
      intro hne
      exact hsingle t i0 (fun e => hne (by rw [e]))
    have hot : o t < N + gates.length := by
      by_contra hge
      obtain ⟨u, hu⟩ : (L t).Nonempty := Finset.card_pos.mp (by
        rw [hcard]
        omega)
      have h1 := hout t (ep u)
      rw [V_ge gates _ (by omega)] at h1
      have h2 : decide (∃ v ∈ L t, ep u v = true) = true :=
        decide_eq_true ⟨u, hu, decide_eq_true rfl⟩
      rw [h2] at h1
      exact absurd h1 (by decide)
    have hSemi : Semi gates (L i0) (L t) (o t) := by
      show V gates (Ft (L i0) (L t)) (o t) = false
      rw [hout]
      refine decide_eq_false ?_
      rintro ⟨v, hv, hF⟩
      exact (of_decide_eq_true hF : v ∉ L i0 ∧ v ∉ L t).2 hv
    have hfull : L t ⊆ Vt gates (L i0) (L t) p0 p1 (o t) := by
      intro p hp
      rw [mem_Vt]
      refine ⟨hp, ?_, Or.inl ⟨hSemi, fun m _ hmT _ => ?_⟩⟩
      · rw [hout]
        exact decide_eq_true ⟨p, hp, decide_eq_true rfl⟩
      · rw [hout]
        refine decide_eq_false ?_
        rintro ⟨v, hv, hF⟩
        have e : v = m := of_decide_eq_true hF
        rw [e] at hv
        exact hmT hv
    obtain ⟨K, hK⟩ : ∃ K : Finset ℕ, K = (Finset.range (N + gates.length)).filter
        (fun w => N ≤ w ∧ Ch gates (L i0) (L t) p0 p1 j (w - N)) := ⟨_, rfl⟩
    have hcov := cover (N + gates.length) (Semi gates (L i0) (L t))
      (Vt gates (L i0) (L t) p0 p1) K
      (fun w hw hR => by
        obtain ⟨S, s1, s2, s3⟩ := step gates (L i0) (L t) p0 p1 j hop hlen hin huniq hzW hzM
          hz0 hz1 hp0 hp1 hTM w hw hR
        refine ⟨S, s1, s2, s3.imp id (fun hh => ⟨hh.1, ?_⟩)⟩
        rw [hK, Finset.mem_filter, Finset.mem_range]
        exact ⟨hw, hh.2⟩)
      (N + gates.length) le_rfl {Vt gates (L i0) (L t) p0 p1 (o t)}
      (fun B hB => by
        rw [Finset.mem_singleton] at hB
        rw [hB]
        exact Or.inr ⟨o t, hot, hSemi, Finset.Subset.refl _⟩)
    rw [Finset.singleton_biUnion, Finset.card_singleton] at hcov
    have hcov2 : (Vt gates (L i0) (L t) p0 p1 (o t)).card ≤
        1 + (K.filter (fun w => w < N + gates.length)).card := hcov
    have hKf : (K.filter (fun w => w < N + gates.length)).card ≤ K.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hKle : K.card ≤ (A t).card := by
      refine le_trans (Finset.card_le_card
        (t := (A t).image (fun i : Fin gates.length => N + (i : ℕ))) ?_) Finset.card_image_le
      intro w hw
      rw [hK, Finset.mem_filter, Finset.mem_range] at hw
      rw [Finset.mem_image]
      have hNw := hw.2.1
      refine ⟨⟨w - N, by omega⟩, ?_, ?_⟩
      · rw [hA]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.2.2⟩
      · show N + (w - N) = w
        omega
    have hLt := Finset.card_le_card hfull
    rw [hcard] at hLt
    omega
  have hdisj : ∀ t t' : Fin N, t ≠ t' → Disjoint (A t) (A t') := by
    intro t t' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [hA, Finset.mem_filter] at hi hi'
    exact disj gates (L i0) (L t) (L t') p0 p1 j hin hmW (hsingle t t' hne) i.isLt hi.2 hi'.2
  have hbig : N * q ≤ (Finset.univ.biUnion A).card := by
    rw [Finset.card_biUnion (fun t _ t' _ hne => hdisj t t' hne)]
    have e1 : ∑ _t : Fin N, q = N * q := by simp
    have e2 : ∑ _t : Fin N, q ≤ ∑ t : Fin N, (A t).card :=
      Finset.sum_le_sum (fun t _ => hAq t)
    omega
  have hRd : Disjoint (Finset.univ.biUnion A) (Finset.univ.filter
      (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_biUnion] at hi
    obtain ⟨t, _, hit⟩ := hi
    rw [hA, Finset.mem_filter] at hit
    rw [Finset.mem_filter] at hi'
    have hmem : N + (j : ℕ) ∈ (gA gates i).inputs := by
      rw [gA_eq i.isLt]
      exact hi'.2
    rcases hit.2 with hc | hc
    · have hz : V gates (Ft (L i0) (L t)) (N + (j : ℕ)) = true :=
        hzW _ (fun v hv => (of_decide_eq_true hv : v ∉ L i0 ∧ v ∉ L t).1)
      have h3 := (orv gates (Ft (L i0) (L t)) i.isLt hc.1 (hin i i.isLt)).mpr ⟨_, hmem, hz⟩
      have hs : V gates (Ft (L i0) (L t)) (N + (i : ℕ)) = false := hc.2.1
      rw [hs] at h3
      exact absurd h3 (by decide)
    · exact hc.2.2.1 hmem
  have hj1 : j ∉ Finset.univ.biUnion A ∪ Finset.univ.filter
      (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs) := by
    intro hmem
    rw [Finset.mem_union] at hmem
    rcases hmem with hi | hi
    · rw [Finset.mem_biUnion] at hi
      obtain ⟨t, _, hit⟩ := hi
      rw [hA, Finset.mem_filter] at hit
      rcases hit.2 with hc | hc
      · have e := hc.1
        rw [hjn'] at e
        cases e
      · have e := hc.1
        rw [hjn'] at e
        cases e
    · rw [Finset.mem_filter] at hi
      have h3 := hin0 j _ hi.2
      omega
  have htot := Finset.card_le_univ (insert j (Finset.univ.biUnion A ∪ Finset.univ.filter
      (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)))
  rw [Fintype.card_fin, Finset.card_insert_of_notMem hj1,
    Finset.card_union_of_disjoint hRd] at htot
  omega

end PEqualNP.Outside.L_meta_1648

theorem PEqualNP.Outside.L_meta_1648 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p0))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p1))) = true →
    (∀ p : Fin N, p ≠ p0 → p ≠ p1 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = false) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length := by
  intro q N L i0 p0 p1 _ _ hcard hint _ _ hp0 hp1 gates o j h hg hin hjn huniq hhj hjin hout h0 h1 hp hW
  exact PEqualNP.Outside.L_meta_1648.fin L i0 p0 p1 hcard hint hp0 hp1 gates o j h hg hin hjn huniq
    hhj hjin hout h0 h1 hp hW
