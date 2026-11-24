import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1645

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

end PEqualNP.Outside.L_meta_1645

open PEqualNP.Outside.L_meta_1645 in
theorem PEqualNP.Outside.L_meta_1645 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    (∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true) ∧
    (∀ w ∈ L i0, w ≠ p0 → w ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = w)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = w)) = true) ∧
    ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = false ∧
    ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ L i0) → (∀ v : Fin N, y v = true → v ∉ L i0) → (∀ v : Fin N, x v = true → y v = true) → ev w x = true → ev w y = true := by
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ gates o j h hg _ hjn huniq hhj hin _ ev hev h0 h1 hp hW
  have hE : ev = fun w x => V gates x w := funext fun w => funext fun x => hev w x
  subst hE
  obtain ⟨r, hr⟩ := hin
  have hop : ∀ k < gates.length, (gA gates k).op = GateOp.and ∨
      (gA gates k).op = GateOp.or ∨ (gA gates k).op = GateOp.not :=
    fun k hk => (hg _ (gA_mem hk)).1
  have hjn' : (gA gates j).op = GateOp.not := by
    rw [gA_eq j.isLt]; exact hjn
  have huniq' : ∀ k < gates.length, (gA gates k).op = GateOp.not → k = j := by
    intro k hk ho
    rw [gA_eq hk] at ho
    exact congrArg Fin.val (huniq ⟨k, hk⟩ ho)
  have hr' : (gA gates j).inputs = (N + (h : ℕ)) :: r := by
    rw [gA_eq j.isLt]; exact hr
  exact main (L i0) p0 p1 gates j h j.isLt hhj hop hjn' huniq' r hr' h0 h1 hp hW
