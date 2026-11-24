import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1651

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

lemma gA_set_ne (gs : List Gate) (j k : ℕ) (g : Gate) (hkj : k ≠ j) :
    gA (gs.set j g) k = gA gs k := by
  simp [gA, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hkj)]

lemma gA_set_self (gs : List Gate) (j : ℕ) (g : Gate) (hj : j < gs.length) :
    gA (gs.set j g) j = g := by
  simp [gA, List.getD_eq_getElem?_getD, hj]

lemma Vz {N : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) (x : Fin N → Bool) :
    V (gs.set j ⟨GateOp.or, []⟩) x (N + j) = false := by
  rw [V_gate _ x (by simpa using hj), gA_set_self gs j _ hj]
  rfl

lemma leS {N : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hop : ∀ k < gs.length, (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or ∨
      (gA gs k).op = GateOp.not)
    (huniq : ∀ k < gs.length, (gA gs k).op = GateOp.not → k = j) (x : Fin N → Bool) :
    ∀ w, V (gs.set j ⟨GateOp.or, []⟩) x w = true → V gs x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases h1 : w < N
    · rw [V_input _ x h1] at hv
      rw [V_input gs x h1]
      exact hv
    · by_cases h2 : N + gs.length ≤ w
      · rw [V_ge _ x (by simpa using h2)] at hv
        exact absurd hv (by decide)
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < gs.length := by omega
        have hkS : k < (gs.set j ⟨GateOp.or, []⟩).length := by simpa using hk
        by_cases hkj : k = j
        · subst hkj
          rw [Vz gs k hk x] at hv
          exact absurd hv (by decide)
        · rw [V_gate _ x hkS, gA_set_ne gs j k _ hkj] at hv
          rw [V_gate gs x hk]
          rcases hop k hk with ho | ho | ho
          · rw [ho, and_eval] at hv ⊢
            intro a ha
            have hva := hv a ha
            by_cases hlt : a < N + k
            · rw [ifp hlt] at hva ⊢
              exact ih a hlt hva
            · rw [ifn hlt] at hva
              exact absurd hva (by decide)
          · rw [ho, or_eval] at hv ⊢
            obtain ⟨a, ha, hav⟩ := hv
            refine ⟨a, ha, ?_⟩
            by_cases hlt : a < N + k
            · rw [ifp hlt] at hav ⊢
              exact ih a hlt hav
            · rw [ifn hlt] at hav
              exact absurd hav (by decide)
          · exact absurd (huniq k hk ho) hkj

lemma agree {N : ℕ} (gs : List Gate) (j : ℕ) (x : Fin N → Bool)
    (hr : ∀ k < gs.length, (N + j) ∈ (gA gs k).inputs → k ≠ j →
      V (gs.set j ⟨GateOp.or, []⟩) x (N + k) = V gs x (N + k)) :
    ∀ w, w ≠ N + j → V (gs.set j ⟨GateOp.or, []⟩) x w = V gs x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · rw [V_input _ x h1, V_input gs x h1]
    · by_cases h2 : N + gs.length ≤ w
      · rw [V_ge _ x (by simpa using h2), V_ge gs x h2]
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < gs.length := by omega
        have hkS : k < (gs.set j ⟨GateOp.or, []⟩).length := by simpa using hk
        have hkj : k ≠ j := fun e => hw (by rw [e])
        by_cases hm : (N + j) ∈ (gA gs k).inputs
        · exact hr k hk hm hkj
        · rw [V_gate _ x hkS, gA_set_ne gs j k _ hkj, V_gate gs x hk]
          congr 1
          apply List.map_congr_left
          intro a ha
          by_cases hlt : a < N + k
          · rw [ifp hlt, ifp hlt]
            exact ih a hlt (fun e => hm (by rw [← e]; exact ha))
          · rw [ifn hlt, ifn hlt]

lemma rd {N : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) (x : Fin N → Bool) (k : ℕ)
    (hk : k < gs.length) (hjk : j < k) (hm : (N + j) ∈ (gA gs k).inputs)
    (ho : (gA gs k).op = GateOp.and) :
    V (gs.set j ⟨GateOp.or, []⟩) x (N + k) = false := by
  by_contra hc
  have ht : V (gs.set j ⟨GateOp.or, []⟩) x (N + k) = true := by simpa using hc
  rw [V_gate _ x (by simpa using hk), gA_set_ne gs j k _ (by omega), ho, and_eval] at ht
  have h3 := ht _ hm
  rw [ifp (by omega : N + j < N + k), Vz gs j hj x] at h3
  exact absurd h3 (by decide)

lemma rd0 {N : ℕ} (gs : List Gate) (j : ℕ) (x : Fin N → Bool) (k : ℕ)
    (hk : k < gs.length) (hjk : j < k) (hm : (N + j) ∈ (gA gs k).inputs)
    (ho : (gA gs k).op = GateOp.and) (hz : V gs x (N + j) = false) :
    V gs x (N + k) = false := by
  by_contra hc
  have ht : V gs x (N + k) = true := by simpa using hc
  rw [V_gate gs x hk, ho, and_eval] at ht
  have h3 := ht _ hm
  rw [ifp (by omega : N + j < N + k), hz] at h3
  exact absurd h3 (by decide)

lemma main {q N : ℕ} (L : Fin N → Finset (Fin N)) (va vb vc : Fin N) (hq : 3 ≤ q)
    (hN : N = q ^ 2 + q + 1) (hc : ∀ i : Fin N, (L i).card = q + 1)
    (gs : List Gate) (o : Fin N → ℕ) (j h : ℕ) (hj : j < gs.length) (hhj : h < j)
    (hop : ∀ k < gs.length, (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or ∨
      (gA gs k).op = GateOp.not)
    (hin : ∀ k < gs.length, ∀ a ∈ (gA gs k).inputs, a < N + k)
    (hjn : (gA gs j).op = GateOp.not)
    (huniq : ∀ k < gs.length, (gA gs k).op = GateOp.not → k = j)
    (r : List ℕ) (hr : (gA gs j).inputs = (N + h) :: r)
    (hout : ∀ (t : Fin N) (x : Fin N → Bool), V gs x (o t) = decide (∃ v ∈ L t, x v = true))
    (hand : ∀ k < gs.length, (N + j) ∈ (gA gs k).inputs → (gA gs k).op = GateOp.and)
    (hh : ∀ p : Fin N, V gs (fun v => decide (v = p)) (N + h) = true ↔
      (p = va ∨ p = vb ∨ p = vc)) :
    (∀ (w : ℕ) (x : Fin N → Bool), V (gs.set j ⟨GateOp.or, []⟩) x w = true → V gs x w = true) ∧
    (∀ (w : ℕ) (x : Fin N → Bool), V gs x (N + h) = true →
      V (gs.set j ⟨GateOp.or, []⟩) x w = V gs x w) ∧
    (∀ k < gs.length, ∀ x : Fin N → Bool, (N + j) ∈ (gA gs k).inputs →
      V (gs.set j ⟨GateOp.or, []⟩) x (N + k) = false) ∧
    (∀ t P : Fin N, P ∈ L t →
      V (gs.set j ⟨GateOp.or, []⟩) (fun v => decide (v = P)) (o t) = false →
      ∃ k, ∃ _ : k < gs.length, (N + j) ∈ (gA gs k).inputs ∧
        V gs (fun v => decide (v = P)) (N + k) = true) ∧
    (∀ (t : Fin N) (x : Fin N → Bool),
      (∃ p : Fin N, (p = va ∨ p = vb ∨ p = vc) ∧ x p = true ∧ p ∈ L t) →
      V (gs.set j ⟨GateOp.or, []⟩) x (o t) = true) := by
  have nv := not_val gs j h hj hhj hjn r hr
  have rdr : ∀ k < gs.length, (N + j) ∈ (gA gs k).inputs → j < k := by
    intro k hk hm
    have := hin k hk _ hm
    omega
  have C3 : ∀ k < gs.length, ∀ x : Fin N → Bool, (N + j) ∈ (gA gs k).inputs →
      V (gs.set j ⟨GateOp.or, []⟩) x (N + k) = false :=
    fun k hk x hm => rd gs j hj x k hk (rdr k hk hm) hm (hand k hk hm)
  have C2 : ∀ (w : ℕ) (x : Fin N → Bool), V gs x (N + h) = true →
      V (gs.set j ⟨GateOp.or, []⟩) x w = V gs x w := by
    intro w x hx
    have hz : V gs x (N + j) = false := by rw [nv, hx]; rfl
    by_cases hw : w = N + j
    · rw [hw, hz, Vz gs j hj x]
    · exact agree gs j x (fun k hk hm _ => by
        rw [C3 k hk x hm, rd0 gs j x k hk (rdr k hk hm) hm (hand k hk hm) hz]) w hw
  refine ⟨fun w x => leS gs j hj hop huniq x w, C2, C3, ?_, ?_⟩
  · intro t P hP hf
    by_contra hne
    have hneF : ∀ k < gs.length, (N + j) ∈ (gA gs k).inputs →
        V gs (fun v => decide (v = P)) (N + k) = false := by
      intro k hk hm
      by_contra hcc
      exact hne ⟨k, hk, hm, by simpa using hcc⟩
    have hag := agree gs j (fun v => decide (v = P))
      (fun k hk hm _ => by rw [C3 k hk _ hm, hneF k hk hm])
    have htrue : V gs (fun v => decide (v = P)) (o t) = true := by
      rw [hout]
      exact decide_eq_true ⟨P, hP, by simp⟩
    by_cases hw : o t = N + j
    · have hsub : (Finset.univ : Finset (Fin N)) ⊆ L t ∪ {va, vb, vc} := by
        intro p _
        by_cases hp : p = va ∨ p = vb ∨ p = vc
        · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          exact Or.inr hp
        · have h1 : V gs (fun v => decide (v = p)) (N + h) = false := by
            by_contra hcc
            exact hp ((hh p).1 (by simpa using hcc))
          have h2 : V gs (fun v => decide (v = p)) (o t) = true := by
            rw [hw, nv, h1]; rfl
          rw [hout] at h2
          obtain ⟨v, hv, hvp⟩ := of_decide_eq_true h2
          have hvq : v = p := of_decide_eq_true hvp
          rw [hvq] at hv
          exact Finset.mem_union_left _ hv
      have hcard := Finset.card_le_card hsub
      have h3 : ({va, vb, vc} : Finset (Fin N)).card ≤ 3 := Finset.card_le_three
      have hu := Finset.card_union_le (L t) {va, vb, vc}
      rw [Finset.card_univ, Fintype.card_fin] at hcard
      rw [hc t] at hu
      nlinarith [Nat.mul_le_mul hq hq]
    · rw [hag (o t) hw, htrue] at hf
      exact absurd hf (by decide)
  · rintro t x ⟨p, hp, hxp, hpt⟩
    have h1 : V gs (fun v => decide (v = p)) (N + h) = true := (hh p).2 hp
    have h2 : V gs x (N + h) = true := monoB gs (fun _ => True) (N + j) hop
      (fun k hk hlt ho => absurd (huniq k hk ho) (by omega)) (N + h) (by omega)
      (fun v => decide (v = p)) x trivial trivial
      (fun v hv => by
        have hvp : v = p := of_decide_eq_true hv
        rw [hvp]; exact hxp) h1
    rw [C2 (o t) x h2, hout]
    exact decide_eq_true ⟨p, hpt, hxp⟩

lemma c50 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    ∀ ev ev' : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w⟩ (List.ofFn x)) →
    (∀ p : Fin N, ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = true → ev w x = true) ∧ (∀ (w : ℕ) (x : Fin N → Bool), ev (N + (h : ℕ)) x = true → ev' w x = ev w x) ∧
    (∀ (i : Fin gates.length) (x : Fin N → Bool), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev' (N + (i : ℕ)) x = false) ∧
    (∀ (t P : Fin N), P ∈ L t → ev' (o t) (fun v : Fin N => decide (v = P)) = false → ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true) ∧
    ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t → ev' (o t) (fun v : Fin N => decide (v = v)) = true := by
  intro q N L va vb vc sa sb sc hq hN hc _ _ _ _ _ _ _ _ _ gates o j h hg hin hjn huniq hhj hr hout hand ev evS hev hevS hh _
  have hE : ev = fun w x => V gates x w := funext fun w => funext fun x => hev w x
  have hES : evS = fun w x => V (gates.set j ⟨GateOp.or, []⟩) x w :=
    funext fun w => funext fun x => hevS w x
  subst hE
  subst hES
  obtain ⟨r, hr⟩ := hr
  have hop : ∀ k < gates.length, (gA gates k).op = GateOp.and ∨
      (gA gates k).op = GateOp.or ∨ (gA gates k).op = GateOp.not :=
    fun k hk => (hg _ (gA_mem hk)).1
  have hinN : ∀ k < gates.length, ∀ a ∈ (gA gates k).inputs, a < N + k := by
    intro k hk a ha
    rw [gA_eq hk] at ha
    exact hin ⟨k, hk⟩ a ha
  have hjnN : (gA gates j).op = GateOp.not := by
    rw [gA_eq j.isLt]; exact hjn
  have huniqN : ∀ k < gates.length, (gA gates k).op = GateOp.not → k = j := by
    intro k hk ho
    rw [gA_eq hk] at ho
    exact congrArg Fin.val (huniq ⟨k, hk⟩ ho)
  have hrN : (gA gates j).inputs = (N + (h : ℕ)) :: r := by
    rw [gA_eq j.isLt]; exact hr
  have handN : ∀ k < gates.length, (N + (j : ℕ)) ∈ (gA gates k).inputs →
      (gA gates k).op = GateOp.and := by
    intro k hk hm
    rw [gA_eq hk] at hm ⊢
    exact hand ⟨k, hk⟩ hm
  obtain ⟨c1, c2, c3, c4, c5⟩ := main L va vb vc hq hN hc gates o j h j.isLt hhj hop hinN
    hjnN huniqN r hrN (fun t x => hout t x) handN hh
  refine ⟨c1, c2, fun i x hm => c3 i i.isLt x (by rw [gA_eq i.isLt]; exact hm), ?_, ?_⟩
  · intro t P hP hf
    obtain ⟨k, hk, hm, hv⟩ := c4 t P hP hf
    exact ⟨⟨k, hk⟩, by rw [gA_eq hk] at hm; exact hm, hv⟩
  · intro t v hv hvt
    refine c5 t _ ⟨v, ?_, by simp, hvt⟩
    simpa using hv

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

def vl {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) : Bool :=
  value (⟨gates, 0⟩ : Circuit) x w

lemma vl_input {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h : w < N) :
    vl gates x w = x ⟨w, h⟩ :=
  input_value (⟨gates, 0⟩ : Circuit) x ⟨w, h⟩

lemma vl_missing {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : N + gates.length ≤ w) : vl gates x w = false :=
  missing_value (⟨gates, 0⟩ : Circuit) x w hw

lemma vl_and {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h13 : N ≤ w)
    (hw : w < N + gates.length) (hop : (gates[w - N]'(by omega)).op = GateOp.and) :
    vl gates x w = true ↔
      ∀ r ∈ (gates[w - N]'(by omega)).inputs, r < w ∧ vl gates x r = true := by
  have h := gate_value (⟨gates, 0⟩ : Circuit) x w h13 hw
  simp only at h
  unfold vl
  rw [h, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
  constructor
  · intro hall r hr
    have := hall _ ⟨r, hr, rfl⟩
    by_cases hrw : r < w
    · simpa [hrw] using this
    · simp [hrw] at this
  · rintro hall b ⟨r, hr, rfl⟩
    have := hall r hr
    simp [this.1, this.2]

lemma vl_or {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h13 : N ≤ w)
    (hw : w < N + gates.length) (hop : (gates[w - N]'(by omega)).op = GateOp.or) :
    vl gates x w = true ↔
      ∃ r ∈ (gates[w - N]'(by omega)).inputs, r < w ∧ vl gates x r = true := by
  have h := gate_value (⟨gates, 0⟩ : Circuit) x w h13 hw
  simp only at h
  unfold vl
  rw [h, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
  constructor
  · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    by_cases hrw : r < w
    · exact ⟨r, hr, hrw, by simpa [hrw] using hb⟩
    · simp [hrw] at hb
  · rintro ⟨r, hr, hrw, hv⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by simp [hrw, hv]⟩

lemma vl_mono {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, vl gates x w = true → vl gates y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases h13 : w < N
    · rw [vl_input gates x w h13] at hx
      rw [vl_input gates y w h13]
      exact hxy _ hx
    · by_cases hw : w < N + gates.length
      · have hk : w - N < gates.length := by omega
        rcases hg (gates[w - N]) (List.getElem_mem hk) with hop | hop
        · rw [vl_and gates x w (by omega) hw hop] at hx
          rw [vl_and gates y w (by omega) hw hop]
          intro r hr
          exact ⟨(hx r hr).1, ih r (hx r hr).1 (hx r hr).2⟩
        · rw [vl_or gates x w (by omega) hw hop] at hx
          rw [vl_or gates y w (by omega) hw hop]
          obtain ⟨r, hr, hlt, hv⟩ := hx
          exact ⟨r, hr, hlt, ih r hlt hv⟩
      · rw [vl_missing gates x w (by omega)] at hx
        exact Bool.noConfusion hx

lemma core {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (U : Finset ℕ)
    (h : ∀ w, (S w).card ≤ 1 ∨ (∃ r, r < w ∧ S w ⊆ S r) ∨
      (w ∈ U ∧ ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ r ∈ R, r < w) ∧ S w ⊆ R.biUnion S)) :
    ∀ (m : ℕ) (T : Finset ℕ), (∀ w ∈ T, w < m) →
      (T.biUnion S).card ≤ T.card + (U.filter (fun u => u < m)).card := by
  intro m
  induction m with
  | zero =>
    intro T hT
    have hTe : T = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun w hw => absurd (hT w hw) (by omega))
    subst hTe
    simp
  | succ m ih =>
    intro T hT
    have hmono : (U.filter (fun u => u < m)).card ≤ (U.filter (fun u => u < m + 1)).card := by
      apply Finset.card_le_card
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨hu'.1, by omega⟩
    by_cases hm : m ∈ T
    · have hT0 : ∀ w ∈ T.erase m, w < m := by
        intro w hw
        have h1 := hT w (Finset.mem_of_mem_erase hw)
        have h2 := Finset.ne_of_mem_erase hw
        omega
      have hTc : (T.erase m).card + 1 = T.card := Finset.card_erase_add_one hm
      have hTu : T.biUnion S = S m ∪ (T.erase m).biUnion S := by
        conv_lhs => rw [← Finset.insert_erase hm]
        rw [Finset.biUnion_insert]
      rcases h m with h1 | ⟨r, hr, hsub⟩ | ⟨hmU, R, hRc, hRlt, hsub⟩
      · have h2 := ih (T.erase m) hT0
        have h3 := Finset.card_union_le (S m) ((T.erase m).biUnion S)
        rw [hTu]
        omega
      · have h2 := ih (insert r (T.erase m)) (by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hr
          · exact hT0 w hw)
        have h3 : T.biUnion S ⊆ (insert r (T.erase m)).biUnion S := by
          rw [hTu]
          intro a ha
          rcases Finset.mem_union.mp ha with ha | ha
          · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_insert_self _ _, hsub ha⟩
          · obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
            exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_insert_of_mem hc, hac⟩
        have h4 := Finset.card_le_card h3
        have h5 := Finset.card_insert_le r (T.erase m)
        omega
      · have h2 := ih (R ∪ T.erase m) (by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hRlt w hw
          · exact hT0 w hw)
        have h3 : T.biUnion S ⊆ (R ∪ T.erase m).biUnion S := by
          rw [hTu]
          intro a ha
          rcases Finset.mem_union.mp ha with ha | ha
          · obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp (hsub ha)
            exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_union_left _ hc, hac⟩
          · obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
            exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_union_right _ hc, hac⟩
        have h4 := Finset.card_le_card h3
        have h5 := Finset.card_union_le R (T.erase m)
        have h6 : (U.filter (fun u => u < m)).card + 1 ≤
            (U.filter (fun u => u < m + 1)).card := by
          have hins : insert m (U.filter (fun u => u < m)) ⊆ U.filter (fun u => u < m + 1) := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact Finset.mem_filter.mpr ⟨hmU, by omega⟩
            · have hu' := Finset.mem_filter.mp hu
              exact Finset.mem_filter.mpr ⟨hu'.1, by omega⟩
          have h7 := Finset.card_le_card hins
          rw [Finset.card_insert_of_notMem (by simp)] at h7
          exact h7
        omega
    · have h2 := ih T (fun w hw => by
        have h1 := hT w hw
        have h3 : w ≠ m := fun e => hm (e ▸ hw)
        omega)
      omega

def S {N : ℕ} (gates : List Gate) (z : Fin N → Bool) (ws : Fin N → Fin N → Bool)
    (M : Finset (Fin N)) (w : ℕ) : Finset (Fin N) :=
  M.filter (fun p => vl gates z w = false ∧ vl gates (ws p) w = true)

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

lemma isOr_iff (op : GateOp) : isOr op = true ↔ op = GateOp.or := by
  cases op <;> simp [isOr]

def U {N : ℕ} (gates : List Gate) (z : Fin N → Bool) (ws : Fin N → Fin N → Bool)
    (M : Finset (Fin N)) : Finset ℕ :=
  (Finset.Ico N (N + gates.length)).filter (fun w =>
    isOr (gates.getD (w - N) ⟨GateOp.and, []⟩).op = true ∧ 2 ≤ (S gates z ws M w).card)

lemma mem_U {N : ℕ} (gates : List Gate) (z : Fin N → Bool) (ws : Fin N → Fin N → Bool)
    (M : Finset (Fin N)) (w : ℕ) :
    w ∈ U gates z ws M ↔ (N ≤ w ∧ w < N + gates.length) ∧
      (gates.getD (w - N) ⟨GateOp.and, []⟩).op = GateOp.or ∧ 2 ≤ (S gates z ws M w).card := by
  unfold U
  rw [Finset.mem_filter, Finset.mem_Ico, isOr_iff]

lemma local_prop {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : Fin N → Bool) (ws : Fin N → Fin N → Bool) (M : Finset (Fin N))
    (hin : ∀ v p, z v = false → p ∈ M → ws p v = true → p = v) (w : ℕ) :
    (S gates z ws M w).card ≤ 1 ∨ (∃ r, r < w ∧ S gates z ws M w ⊆ S gates z ws M r) ∨
      (w ∈ U gates z ws M ∧ ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ r ∈ R, r < w) ∧
        S gates z ws M w ⊆ R.biUnion (S gates z ws M)) := by
  by_cases hz : vl gates z w = true
  · left
    have he : S gates z ws M w = ∅ := by
      unfold S
      apply Finset.filter_eq_empty_iff.mpr
      intro p _ hp
      rw [hz] at hp
      exact Bool.noConfusion hp.1
    rw [he]
    simp
  · have hz' : vl gates z w = false := by simpa using hz
    by_cases h13 : w < N
    · left
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have hzv : z ⟨w, h13⟩ = false := by
        rw [← vl_input gates z w h13]
        exact hz'
      have e1 := hin ⟨w, h13⟩ a hzv ha'.1 (by
        rw [← vl_input gates (ws a) w h13]
        exact ha'.2.2)
      have e2 := hin ⟨w, h13⟩ b hzv hb'.1 (by
        rw [← vl_input gates (ws b) w h13]
        exact hb'.2.2)
      exact e1.trans e2.symm
    · by_cases hw : w < N + gates.length
      · have hk : w - N < gates.length := by omega
        have hmem : gates[w - N] ∈ gates := List.getElem_mem hk
        rcases (hg _ hmem).1 with hop | hop
        · have hnot : ¬ (∀ r ∈ (gates[w - N]).inputs, r < w ∧ vl gates z r = true) := by
            rw [← vl_and gates z w (by omega) hw hop]
            simp [hz']
          push Not at hnot
          obtain ⟨r, hr, hrn⟩ := hnot
          by_cases hrw : r < w
          · right
            left
            refine ⟨r, hrw, ?_⟩
            intro p hp
            have hp' := Finset.mem_filter.mp hp
            refine Finset.mem_filter.mpr ⟨hp'.1, ?_, ?_⟩
            · have h1 := hrn hrw
              simpa using h1
            · exact ((vl_and gates (ws p) w (by omega) hw hop).mp hp'.2.2 r hr).2
          · left
            have he : S gates z ws M w = ∅ := by
              unfold S
              apply Finset.filter_eq_empty_iff.mpr
              intro p _ hp
              exact hrw ((vl_and gates (ws p) w (by omega) hw hop).mp hp.2 r hr).1
            rw [he]
            simp
        · by_cases hc : (S gates z ws M w).card ≤ 1
          · left
            exact hc
          · right
            right
            refine ⟨?_, ((gates[w - N]).inputs.filter (fun r => r < w)).toFinset, ?_, ?_, ?_⟩
            · rw [mem_U]
              refine ⟨⟨by omega, hw⟩, ?_, by omega⟩
              rw [List.getD_eq_getElem _ _ hk]
              exact hop
            · exact le_trans (List.toFinset_card_le _)
                (le_trans (List.length_filter_le _ _) (hg _ hmem).2)
            · intro r hr
              have h1 := (List.mem_filter.mp (List.mem_toFinset.mp hr)).2
              simpa using h1
            · intro p hp
              have hp' := Finset.mem_filter.mp hp
              obtain ⟨r, hr, hrw, hv⟩ := (vl_or gates (ws p) w (by omega) hw hop).mp hp'.2.2
              refine Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr
                (List.mem_filter.mpr ⟨hr, by simpa using hrw⟩),
                Finset.mem_filter.mpr ⟨hp'.1, ?_, hv⟩⟩
              by_contra hne
              have ht : vl gates z r = true := by simpa using hne
              have h1 := (vl_or gates z w (by omega) hw hop).mpr ⟨r, hr, hrw, ht⟩
              rw [hz'] at h1
              exact Bool.noConfusion h1
      · left
        have he : S gates z ws M w = ∅ := by
          unfold S
          apply Finset.filter_eq_empty_iff.mpr
          intro p _ hp
          rw [vl_missing gates (ws p) w (by omega)] at hp
          exact Bool.noConfusion hp.2
        rw [he]
        simp

lemma three_le {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : Fin N → Bool) (ws : Fin N → Fin N → Bool) (M : Finset (Fin N))
    (hin : ∀ v p, z v = false → p ∈ M → ws p v = true → p = v)
    (q : ℕ) (hM : M.card = q + 1) (o : ℕ) (hz : vl gates z o = false)
    (ho : ∀ p ∈ M, vl gates (ws p) o = true) : q ≤ (U gates z ws M).card := by
  have h := core (S gates z ws M) (U gates z ws M) (local_prop gates hg z ws M hin)
    (o + 1) {o} (by simp)
  have hS : S gates z ws M o = M := Finset.filter_true_of_mem (fun p hp => ⟨hz, ho p hp⟩)
  have h2 : ((U gates z ws M).filter (fun u => u < o + 1)).card ≤ (U gates z ws M).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Finset.singleton_biUnion, hS, hM, Finset.card_singleton] at h
  omega

lemma disj_one {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (z : Fin N → Bool) (ws : Fin N → Fin N → Bool) (M M' : Finset (Fin N))
    (z' : Fin N → Bool) (hc : (M ∩ M').card ≤ 1)
    (h : ∀ p ∈ M, p ∉ M' → ∀ v, ws p v = true → z' v = true) (w : ℕ)
    (h2 : 2 ≤ (S gates z ws M w).card) : vl gates z' w = true := by
  have hex : ∃ p ∈ S gates z ws M w, p ∉ M' := by
    by_contra hcon
    push Not at hcon
    have hsub : S gates z ws M w ⊆ M ∩ M' := fun p hp =>
      Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, hcon p hp⟩
    have h3 := Finset.card_le_card hsub
    omega
  obtain ⟨p, hp, hpM'⟩ := hex
  have hp' := Finset.mem_filter.mp hp
  exact vl_mono gates hg (ws p) z' (h p hp'.1 hpM') w hp'.2.2

def zf {N : ℕ} (M : Finset (Fin N)) : Fin N → Bool := fun v => decide (v ∉ M)

def wf {N : ℕ} (Bp : Fin N → Finset (Fin N)) : Fin N → Fin N → Bool :=
  fun p v => decide (v = p ∨ v ∈ Bp p)

theorem rot_exists (k : ℕ) :
    ∃ r : Fin (k + 3) → Fin (k + 3), Function.Injective r ∧ ∀ a, r a ≠ a ∧ r (r a) ≠ a := by
  have h1 : ((1 : Fin (k + 3)) : ℕ) = 1 := Fin.val_one (k + 1)
  refine ⟨fun a => a + 1, add_left_injective 1, ?_⟩
  intro a
  constructor
  · intro h
    have h2 : a + 1 = a + 0 := h.trans (add_zero a).symm
    have h3 : (1 : Fin (k + 3)) = 0 := add_left_cancel h2
    have h4 := congrArg Fin.val h3
    rw [h1] at h4
    simp at h4
  · intro h
    have h2 : a + (1 + 1) = a + 0 := by
      rw [← add_assoc, add_zero]
      exact h
    have h3 : (1 + 1 : Fin (k + 3)) = 0 := add_left_cancel h2
    have h4 := congrArg Fin.val h3
    rw [Fin.val_add, h1, Nat.mod_eq_of_lt (by omega)] at h4
    simp at h4

theorem sigma_exists {N : ℕ} (T0 : Finset (Fin N)) (k : ℕ) (hc : T0.card = k + 3) :
    ∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧
      (∀ x ∈ T0, sigma x ≠ x ∧ sigma (sigma x) ≠ x) := by
  obtain ⟨r, hri, hr⟩ := rot_exists k
  have e : T0 ≃ Fin (k + 3) := T0.equivFinOfCardEq hc
  have hex : ∃ sigma : Fin N → Fin N, ∀ x (h : x ∈ T0), sigma x = (e.symm (r (e ⟨x, h⟩))).1 :=
    ⟨fun x => if h : x ∈ T0 then (e.symm (r (e ⟨x, h⟩))).1 else x, fun x h => dif_pos h⟩
  obtain ⟨sigma, hs⟩ := hex
  refine ⟨sigma, ?_, ?_, ?_⟩
  · intro x hx
    rw [hs x hx]
    exact (e.symm _).2
  · intro x hx y hy hxy
    have hx' : x ∈ T0 := Finset.mem_coe.mp hx
    have hy' : y ∈ T0 := Finset.mem_coe.mp hy
    rw [hs x hx', hs y hy'] at hxy
    have h1 := hri (e.symm.injective (Subtype.ext hxy))
    have h2 := e.injective h1
    exact congrArg Subtype.val h2
  · intro x hx
    have hsx : sigma x ∈ T0 := by
      rw [hs x hx]
      exact (e.symm _).2
    have e1 : e ⟨sigma x, hsx⟩ = r (e ⟨x, hx⟩) := by
      have h0 : (⟨sigma x, hsx⟩ : T0) = e.symm (r (e ⟨x, hx⟩)) := Subtype.ext (hs x hx)
      rw [h0, Equiv.apply_symm_apply]
    constructor
    · intro h
      have h0 : (⟨sigma x, hsx⟩ : T0) = ⟨x, hx⟩ := Subtype.ext h
      rw [h0] at e1
      exact (hr _).1 e1.symm
    · intro h
      have e2 : sigma (sigma x) = (e.symm (r (e ⟨sigma x, hsx⟩))).1 := hs _ hsx
      rw [e1] at e2
      have h0 : e.symm (r (r (e ⟨x, hx⟩))) = ⟨x, hx⟩ := Subtype.ext (e2.symm.trans h)
      have h1 := congrArg e h0
      rw [Equiv.apply_symm_apply] at h1
      exact (hr _).2 h1

lemma main2 (q N : ℕ) (L : Fin N → Finset (Fin N))
    (hL4 : ∀ t : Fin N, (L t).card = q + 1)
    (hL1 : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (D : (Fin N → Bool) → Prop)
    (hzD : ∀ t : Fin N, D (zf (L t)))
    (gates : List Gate) (o : Fin N → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hev : ∀ (t : Fin N) (x : Fin N → Bool), D x →
      vl gates x (o t) = decide (∃ v ∈ L t, x v = true))
    (Lam : Finset (Fin N)) (B : Fin N → Fin N → Finset (Fin N))
    (hB : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (wf (B t) p))
    (hcross : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty)))
    (J : Finset ℕ) (hJ1 : J ⊆ Finset.Ico N (N + gates.length))
    (hJ2 : ∀ w ∈ J, ∀ t ∈ Lam, w ∉ U gates (zf (L t)) (wf (B t)) (L t)) :
    q * Lam.card + J.card ≤ gates.length := by
  classical
  have hgm : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  have hLi : ∀ t t', t ≠ t' → (L t ∩ L t').card ≤ 1 := fun t t' h => le_of_eq (hL1 t t' h)
  have hz0 : ∀ t, vl gates (zf (L t)) (o t) = false := by
    intro t
    rw [hev t _ (hzD t)]
    simp [zf]
  have hw1 : ∀ t ∈ Lam, ∀ p ∈ L t, vl gates (wf (B t) p) (o t) = true := by
    intro t ht p hp
    rw [hev t _ (hB t ht p hp).2]
    simp only [decide_eq_true_eq]
    exact ⟨p, hp, by simp [wf]⟩
  have hin : ∀ t ∈ Lam, ∀ v p, zf (L t) v = false → p ∈ L t → wf (B t) p v = true → p = v := by
    intro t ht v p hzv hp hwv
    have hv : v ∈ L t := by simpa [zf] using hzv
    have hwv' : v = p ∨ v ∈ B t p := by simpa [wf] using hwv
    rcases hwv' with h | h
    · exact h.symm
    · exfalso
      have he := (hB t ht p hp).1
      have hmem : v ∈ B t p ∩ L t := Finset.mem_inter.mpr ⟨h, hv⟩
      rw [he] at hmem
      exact absurd hmem (Finset.notMem_empty v)
  have h3 : ∀ t ∈ Lam, q ≤ (U gates (zf (L t)) (wf (B t)) (L t)).card := fun t ht =>
    three_le gates hg _ _ _ (hin t ht) q (hL4 t) (o t) (hz0 t) (hw1 t ht)
  have hone : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → (∀ p ∈ L t \ L t', B t p ∩ L t' = ∅) →
      Disjoint (U gates (zf (L t)) (wf (B t)) (L t))
        (U gates (zf (L t')) (wf (B t')) (L t')) := by
    intro t ht t' ht' hne hb
    rw [Finset.disjoint_left]
    intro w hw hw'
    have h2 := ((mem_U _ _ _ _ _).mp hw).2.2
    have h2' := ((mem_U _ _ _ _ _).mp hw').2.2
    have htrue : vl gates (zf (L t')) w = true := by
      refine disj_one gates hgm (zf (L t)) (wf (B t)) (L t) (L t') (zf (L t'))
        (hLi t t' hne) ?_ w h2
      intro p hp hp' v hv
      have hv' : v = p ∨ v ∈ B t p := by simpa [wf] using hv
      have hvn : v ∉ L t' := by
        rcases hv' with rfl | h
        · exact hp'
        · intro hvl
          have he := hb p (Finset.mem_sdiff.mpr ⟨hp, hp'⟩)
          have hmem : v ∈ B t p ∩ L t' := Finset.mem_inter.mpr ⟨h, hvl⟩
          rw [he] at hmem
          exact absurd hmem (Finset.notMem_empty v)
      simp [zf, hvn]
    obtain ⟨pp, hpp⟩ := Finset.card_pos.mp
      (by omega : 0 < (S gates (zf (L t')) (wf (B t')) (L t') w).card)
    have hf := (Finset.mem_filter.mp hpp).2.1
    rw [htrue] at hf
    exact Bool.noConfusion hf
  have hdisj : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' →
      Disjoint (U gates (zf (L t)) (wf (B t)) (L t))
        (U gates (zf (L t')) (wf (B t')) (L t')) := by
    intro t ht t' ht' hne
    by_cases h1 : ∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty
    · have h2 : ¬ ∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty :=
        fun h2 => hcross t ht t' ht' hne ⟨h1, h2⟩
      exact (hone t' ht' t ht hne.symm (fun p hp =>
        Finset.not_nonempty_iff_eq_empty.mp (fun hne' => h2 ⟨p, hp, hne'⟩))).symm
    · exact hone t ht t' ht' hne (fun p hp =>
        Finset.not_nonempty_iff_eq_empty.mp (fun hne' => h1 ⟨p, hp, hne'⟩))
  have hAcard : q * Lam.card ≤
      (Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t))).card := by
    rw [Finset.card_biUnion (fun t ht t' ht' hne => hdisj t ht t' ht' hne)]
    have h4 := Finset.card_nsmul_le_sum Lam
      (fun t => (U gates (zf (L t)) (wf (B t)) (L t)).card) q h3
    rw [smul_eq_mul] at h4
    exact le_of_eq_of_le (Nat.mul_comm _ _) h4
  have hAsub : Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t)) ⊆
      Finset.Ico N (N + gates.length) := by
    intro w hw
    obtain ⟨t, _, hwt⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_Ico.mpr ((mem_U _ _ _ _ _).mp hwt).1
  have hd : Disjoint (Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t))) J := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp hw
    exact hJ2 w hw' t ht hwt
  have hsub : Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t)) ∪ J ⊆
      Finset.Ico N (N + gates.length) := Finset.union_subset hAsub hJ1
  have h5 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Nat.card_Ico] at h5
  omega

lemma two_cover (l : List ℕ) (hl : l.length ≤ 2) (hne : l ≠ []) :
    ∃ r1 r2, r1 ∈ l ∧ r2 ∈ l ∧ ∀ r ∈ l, r = r1 ∨ r = r2 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact absurd rfl hne
  · exact ⟨a, a, by simp, by simp, by simp⟩
  · exact ⟨a, b, by simp, by simp, by simp⟩
  · simp only [List.length_cons] at hl
    omega

lemma core2 {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (G : Finset ℕ) (cap : Finset α → ℕ)
    (c0 : cap ∅ = 0)
    (cU : ∀ A B : Finset α, cap (A ∪ B) ≤ cap A + cap B)
    (cS : ∀ (w : ℕ) (A1 A2 : Finset α), A1 ⊆ S w → A2 ⊆ S w → Disjoint A1 A2 →
      cap A1 + cap A2 ≤ cap (A1 ∪ A2) + 1)
    (h : ∀ w, (∀ A : Finset α, A ⊆ S w → A.card ≤ cap A) ∨
      (w ∈ G ∧ ∃ r1 r2, r1 < w ∧ r2 < w ∧ S w ⊆ S r1 ∪ S r2)) :
    ∀ (m : ℕ) (T : ℕ → Finset α), (∀ w, T w ⊆ S w) →
      ((Finset.range m).biUnion T).card ≤
        (∑ w ∈ Finset.range m, cap (T w)) + (G.filter (fun u => u < m)).card := by
  intro m
  induction m with
  | zero =>
    intro T _
    simp
  | succ m ih =>
    intro T hT
    have hmono : (G.filter (fun u => u < m)).card ≤ (G.filter (fun u => u < m + 1)).card := by
      apply Finset.card_le_card
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨hu'.1, by omega⟩
    have hTu : (Finset.range (m + 1)).biUnion T = T m ∪ (Finset.range m).biUnion T := by
      rw [Finset.range_add_one, Finset.biUnion_insert]
    rw [Finset.sum_range_succ]
    rcases h m with hleaf | ⟨hmG, r1, r2, hr1, hr2, hsub⟩
    · have h2 := ih T hT
      have h3 := Finset.card_union_le (T m) ((Finset.range m).biUnion T)
      have h4 := hleaf (T m) (hT m)
      rw [hTu]
      omega
    · have key : ∀ A1 A2 : Finset α, A1 ⊆ S r1 → A2 ⊆ S r2 → A1 ∪ A2 = T m → Disjoint A1 A2 →
          ((Finset.range (m + 1)).biUnion T).card ≤
            (∑ w ∈ Finset.range m, cap (T w)) + cap (T m) +
              (G.filter (fun u => u < m + 1)).card := by
        intro A1 A2 hA1s hA2s hAu hAd
        have hcs := cS m A1 A2 (fun a ha => hT m (hAu ▸ Finset.mem_union_left _ ha))
          (fun a ha => hT m (hAu ▸ Finset.mem_union_right _ ha)) hAd
        rw [hAu] at hcs
        obtain ⟨T', hT'def⟩ : ∃ T' : ℕ → Finset α, ∀ w, T' w =
            T w ∪ ((if w = r1 then A1 else ∅) ∪ (if w = r2 then A2 else ∅)) := ⟨_, fun _ => rfl⟩
        have hT' : ∀ w, T' w ⊆ S w := by
          intro w a ha
          rw [hT'def] at ha
          rcases Finset.mem_union.mp ha with ha | ha
          · exact hT w ha
          · rcases Finset.mem_union.mp ha with ha | ha
            · by_cases e : w = r1
              · rw [ifp e] at ha
                rw [e]
                exact hA1s ha
              · rw [ifn e] at ha
                exact absurd ha (Finset.notMem_empty a)
            · by_cases e : w = r2
              · rw [ifp e] at ha
                rw [e]
                exact hA2s ha
              · rw [ifn e] at ha
                exact absurd ha (Finset.notMem_empty a)
        have h2 := ih T' hT'
        have h3 : (Finset.range (m + 1)).biUnion T ⊆ (Finset.range m).biUnion T' := by
          rw [hTu]
          intro a ha
          rcases Finset.mem_union.mp ha with ha | ha
          · rw [← hAu] at ha
            rcases Finset.mem_union.mp ha with ha | ha
            · refine Finset.mem_biUnion.mpr ⟨r1, Finset.mem_range.mpr hr1, ?_⟩
              rw [hT'def]
              refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
              rw [ifp rfl]
              exact ha
            · refine Finset.mem_biUnion.mpr ⟨r2, Finset.mem_range.mpr hr2, ?_⟩
              rw [hT'def]
              refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
              rw [ifp rfl]
              exact ha
          · obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
            refine Finset.mem_biUnion.mpr ⟨c, hc, ?_⟩
            rw [hT'def]
            exact Finset.mem_union_left _ hac
        have h4 := Finset.card_le_card h3
        have s1 : ∑ w ∈ Finset.range m, (if w = r1 then cap A1 else 0) = cap A1 := by
          rw [Finset.sum_ite_eq' (Finset.range m) r1 (fun _ => cap A1),
            ifp (Finset.mem_range.mpr hr1)]
        have s2 : ∑ w ∈ Finset.range m, (if w = r2 then cap A2 else 0) = cap A2 := by
          rw [Finset.sum_ite_eq' (Finset.range m) r2 (fun _ => cap A2),
            ifp (Finset.mem_range.mpr hr2)]
        have h5 : ∑ w ∈ Finset.range m, cap (T' w) ≤
            (∑ w ∈ Finset.range m, cap (T w)) + cap A1 + cap A2 := by
          have hpt : ∀ w ∈ Finset.range m, cap (T' w) ≤
              cap (T w) + ((if w = r1 then cap A1 else 0) + (if w = r2 then cap A2 else 0)) := by
            intro w _
            have e1 : cap (if w = r1 then A1 else ∅) = if w = r1 then cap A1 else 0 := by
              by_cases e : w = r1
              · rw [ifp e, ifp e]
              · rw [ifn e, ifn e]
                exact c0
            have e2 : cap (if w = r2 then A2 else ∅) = if w = r2 then cap A2 else 0 := by
              by_cases e : w = r2
              · rw [ifp e, ifp e]
              · rw [ifn e, ifn e]
                exact c0
            have i1 := cU (T w) ((if w = r1 then A1 else ∅) ∪ (if w = r2 then A2 else ∅))
            have i2 := cU (if w = r1 then A1 else ∅) (if w = r2 then A2 else ∅)
            rw [e1, e2] at i2
            rw [hT'def]
            exact le_trans i1 (Nat.add_le_add_left i2 _)
          have hs := Finset.sum_le_sum hpt
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, s1, s2] at hs
          omega
        have h6 : (G.filter (fun u => u < m)).card + 1 ≤
            (G.filter (fun u => u < m + 1)).card := by
          have hins : insert m (G.filter (fun u => u < m)) ⊆ G.filter (fun u => u < m + 1) := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact Finset.mem_filter.mpr ⟨hmG, by omega⟩
            · have hu' := Finset.mem_filter.mp hu
              exact Finset.mem_filter.mpr ⟨hu'.1, by omega⟩
          have h7 := Finset.card_le_card hins
          rw [Finset.card_insert_of_notMem (by simp)] at h7
          exact h7
        omega
      refine key ((T m).filter (fun a => a ∈ S r1)) ((T m).filter (fun a => ¬ a ∈ S r1))
        (fun a ha => (Finset.mem_filter.mp ha).2) ?_
        (Finset.filter_union_filter_not_eq _ _) (Finset.disjoint_filter_filter_not _ _ _)
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      rcases Finset.mem_union.mp (hsub (hT m ha'.1)) with h1 | h1
      · exact absurd h1 ha'.2
      · exact h1

def SS {N : ℕ} (gates : List Gate) (Z : Fin 3 → Fin N → Bool) (W : Fin 3 → Fin N → Fin N → Bool)
    (M : Fin 3 → Finset (Fin N)) (w : ℕ) : Finset ((_ : Fin 3) × Fin N) :=
  Finset.univ.sigma (fun x => S gates (Z x) (W x) (M x) w)

lemma mem_SS {N : ℕ} (gates : List Gate) (Z : Fin 3 → Fin N → Bool)
    (W : Fin 3 → Fin N → Fin N → Bool) (M : Fin 3 → Finset (Fin N)) (w : ℕ)
    (y : (_ : Fin 3) × Fin N) :
    y ∈ SS gates Z W M w ↔
      y.2 ∈ M y.1 ∧ vl gates (Z y.1) w = false ∧ vl gates (W y.1 y.2) w = true := by
  unfold SS S
  rw [Finset.mem_sigma, Finset.mem_filter]
  simp

def pr {N : ℕ} (A : Finset ((_ : Fin 3) × Fin N)) : Prop :=
  ∃ y ∈ A, ∃ y' ∈ A, y.1 ≠ y'.1 ∧ y.2 = y'.2

open Classical in
noncomputable def cap {N : ℕ} (A : Finset ((_ : Fin 3) × Fin N)) : ℕ :=
  if A = ∅ then 0 else if pr A then 2 else 1

lemma cap_empty {N : ℕ} : cap (∅ : Finset ((_ : Fin 3) × Fin N)) = 0 := by
  unfold cap
  rw [ifp rfl]

lemma cap_pr {N : ℕ} (A : Finset ((_ : Fin 3) × Fin N)) (hA : A ≠ ∅) (h : pr A) : cap A = 2 := by
  unfold cap
  simp [hA, h]

lemma cap_npr {N : ℕ} (A : Finset ((_ : Fin 3) × Fin N)) (hA : A ≠ ∅) (h : ¬ pr A) :
    cap A = 1 := by
  unfold cap
  simp [hA, h]

lemma cap_le {N : ℕ} (A : Finset ((_ : Fin 3) × Fin N)) : cap A ≤ 2 := by
  unfold cap
  split_ifs <;> omega

lemma cap_pos {N : ℕ} (A : Finset ((_ : Fin 3) × Fin N)) (hA : A ≠ ∅) : 1 ≤ cap A := by
  unfold cap
  rw [ifn hA]
  split_ifs <;> omega

lemma cap_union {N : ℕ} (A B : Finset ((_ : Fin 3) × Fin N)) : cap (A ∪ B) ≤ cap A + cap B := by
  by_cases hA : A = ∅
  · rw [hA, Finset.empty_union]
    omega
  · by_cases hB : B = ∅
    · rw [hB, Finset.union_empty]
      omega
    · have h1 := cap_pos A hA
      have h2 := cap_pos B hB
      have h3 := cap_le (A ∪ B)
      omega

lemma pr_mono {N : ℕ} {A B : Finset ((_ : Fin 3) × Fin N)} (h : A ⊆ B) (hp : pr A) : pr B := by
  obtain ⟨y, hy, y', hy', h1, h2⟩ := hp
  exact ⟨y, h hy, y', h hy', h1, h2⟩

lemma cap_split {N : ℕ} (A1 A2 : Finset ((_ : Fin 3) × Fin N))
    (hone : pr A1 → pr A2 → False) : cap A1 + cap A2 ≤ cap (A1 ∪ A2) + 1 := by
  by_cases hA1 : A1 = ∅
  · rw [hA1, Finset.empty_union, cap_empty]
    omega
  by_cases hA2 : A2 = ∅
  · rw [hA2, Finset.union_empty, cap_empty]
    omega
  have hU : A1 ∪ A2 ≠ ∅ := by
    intro h
    exact hA1 (Finset.union_eq_empty.mp h).1
  by_cases h1 : pr A1
  · have h2 : ¬ pr A2 := fun h2 => hone h1 h2
    have e1 := cap_pr A1 hA1 h1
    have e2 := cap_npr A2 hA2 h2
    have e3 := cap_pr _ hU (pr_mono Finset.subset_union_left h1)
    omega
  · by_cases h2 : pr A2
    · have e1 := cap_npr A1 hA1 h1
      have e2 := cap_pr A2 hA2 h2
      have e3 := cap_pr _ hU (pr_mono Finset.subset_union_right h2)
      omega
    · have e1 := cap_npr A1 hA1 h1
      have e2 := cap_npr A2 hA2 h2
      have e3 := cap_pos _ hU
      omega

lemma fin3_cases : ∀ a b c d : Fin 3, a ≠ b → c ≠ d →
    (c ≠ a ∧ c ≠ b) ∨ (d ≠ a ∧ d ≠ b) ∨ (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  decide

lemma SS_hone {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (Z : Fin 3 → Fin N → Bool) (W : Fin 3 → Fin N → Fin N → Bool) (M : Fin 3 → Finset (Fin N))
    (hI : ∀ x x', x ≠ x' → (M x ∩ M x').card ≤ 1)
    (hG : ∀ x x' z v, x ≠ x' → z ≠ x → z ≠ x' → v ∈ M x → v ∈ M x' →
      ∀ u, W x v u = true → Z z u = true)
    (w : ℕ) (A1 A2 : Finset ((_ : Fin 3) × Fin N)) (h1 : A1 ⊆ SS gates Z W M w)
    (h2 : A2 ⊆ SS gates Z W M w) (hd : Disjoint A1 A2) (p1 : pr A1) (p2 : pr A2) : False := by
  obtain ⟨y, hy, y', hy', hne, he⟩ := p1
  obtain ⟨u, hu, u', hu', hne2, he2⟩ := p2
  have ty := (mem_SS gates Z W M w y).mp (h1 hy)
  have ty' := (mem_SS gates Z W M w y').mp (h1 hy')
  have tu := (mem_SS gates Z W M w u).mp (h2 hu)
  have tu' := (mem_SS gates Z W M w u').mp (h2 hu')
  have hv' : y.2 ∈ M y'.1 := by
    rw [he]
    exact ty'.1
  have third : ∀ z, z ≠ y.1 → z ≠ y'.1 → vl gates (Z z) w = true := by
    intro z hz hz'
    exact vl_mono gates hg (W y.1 y.2) (Z z) (hG y.1 y'.1 z y.2 hne hz hz' ty.1 hv') w ty.2.2
  have m2 : y.2 ∈ M y.1 ∩ M y'.1 := Finset.mem_inter.mpr ⟨ty.1, hv'⟩
  have hu2' : u.2 ∈ M u'.1 := by
    rw [he2]
    exact tu'.1
  rcases fin3_cases y.1 y'.1 u.1 u'.1 hne hne2 with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · have h3 := third u.1 a b
    rw [tu.2.1] at h3
    exact Bool.noConfusion h3
  · have h3 := third u'.1 a b
    rw [tu'.2.1] at h3
    exact Bool.noConfusion h3
  · have m1 : u.2 ∈ M y.1 ∩ M y'.1 :=
      Finset.mem_inter.mpr ⟨by rw [← a]; exact tu.1, by rw [← b]; exact hu2'⟩
    have e := Finset.card_le_one.mp (hI y.1 y'.1 hne) u.2 m1 y.2 m2
    have e3 : u = y := Sigma.ext a (heq_of_eq e)
    rw [e3] at hu
    exact Finset.disjoint_left.mp hd hy hu
  · have m1 : u.2 ∈ M y.1 ∩ M y'.1 :=
      Finset.mem_inter.mpr ⟨by rw [← b]; exact hu2', by rw [← a]; exact tu.1⟩
    have e := Finset.card_le_one.mp (hI y.1 y'.1 hne) u.2 m1 y.2 m2
    have e3 : u = y' := Sigma.ext a (heq_of_eq (e.trans he))
    rw [e3] at hu
    exact Finset.disjoint_left.mp hd hy' hu

lemma SS_local {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Z : Fin 3 → Fin N → Bool) (W : Fin 3 → Fin N → Fin N → Bool) (M : Fin 3 → Finset (Fin N))
    (hin : ∀ x v p, Z x v = false → p ∈ M x → W x p v = true → p = v)
    (hG : ∀ x x' z v, x ≠ x' → z ≠ x → z ≠ x' → v ∈ M x → v ∈ M x' →
      ∀ u, W x v u = true → Z z u = true) (w : ℕ) :
    (∀ A : Finset ((_ : Fin 3) × Fin N), A ⊆ SS gates Z W M w → A.card ≤ cap A) ∨
      (w ∈ (Finset.Ico N (N + gates.length)).filter (fun w => 2 ≤ (SS gates Z W M w).card) ∧
        ∃ r1 r2, r1 < w ∧ r2 < w ∧
          SS gates Z W M w ⊆ SS gates Z W M r1 ∪ SS gates Z W M r2) := by
  have small : ∀ A : Finset ((_ : Fin 3) × Fin N), A.card ≤ 1 → A.card ≤ cap A := by
    intro A hA
    by_cases hAe : A = ∅
    · rw [hAe]
      simp
    · have h1 := cap_pos A hAe
      omega
  by_cases h13 : w < N
  · left
    intro A hA
    by_cases hc : A.card ≤ 1
    · exact small A hc
    · obtain ⟨y, hy, y', hy', hyy⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
      have pt : ∀ u ∈ A, u.2 = ⟨w, h13⟩ ∧ Z u.1 ⟨w, h13⟩ = false ∧
          W u.1 u.2 ⟨w, h13⟩ = true := by
        intro u hu
        have tu := (mem_SS gates Z W M w u).mp (hA hu)
        have z1 : Z u.1 ⟨w, h13⟩ = false := by
          rw [← vl_input gates (Z u.1) w h13]
          exact tu.2.1
        have z2 : W u.1 u.2 ⟨w, h13⟩ = true := by
          rw [← vl_input gates (W u.1 u.2) w h13]
          exact tu.2.2
        exact ⟨hin u.1 _ u.2 z1 tu.1 z2, z1, z2⟩
      have e12 : y.2 = y'.2 := (pt y hy).1.trans (pt y' hy').1.symm
      have hne : y.1 ≠ y'.1 := by
        intro e
        exact hyy (Sigma.ext e (heq_of_eq e12))
      have hpr : pr A := ⟨y, hy, y', hy', hne, e12⟩
      have hAne : A ≠ ∅ := by
        intro e
        rw [e] at hy
        exact absurd hy (Finset.notMem_empty y)
      rw [cap_pr A hAne hpr]
      have ty := (mem_SS gates Z W M w y).mp (hA hy)
      have ty' := (mem_SS gates Z W M w y').mp (hA hy')
      have hv' : y.2 ∈ M y'.1 := by
        rw [e12]
        exact ty'.1
      have hsub : A ⊆ {y, y'} := by
        intro u hu
        by_cases e1 : u.1 = y.1
        · exact Finset.mem_insert.mpr (Or.inl
            (Sigma.ext e1 (heq_of_eq ((pt u hu).1.trans (pt y hy).1.symm))))
        · by_cases e2 : u.1 = y'.1
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
              (Sigma.ext e2 (heq_of_eq ((pt u hu).1.trans (pt y' hy').1.symm)))))
          · exfalso
            have h3 := hG y.1 y'.1 u.1 y.2 hne e1 e2 ty.1 hv' ⟨w, h13⟩ (pt y hy).2.2
            rw [(pt u hu).2.1] at h3
            exact Bool.noConfusion h3
      exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
  · by_cases hc : (SS gates Z W M w).card ≤ 1
    · left
      intro A hA
      exact small A (le_trans (Finset.card_le_card hA) hc)
    · right
      have hw : w < N + gates.length := by
        by_contra hw
        obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (SS gates Z W M w).card)
        have ty := (mem_SS gates Z W M w y).mp hy
        have h1 := ty.2.2
        rw [vl_missing gates _ w (by omega)] at h1
        exact Bool.noConfusion h1
      have hk : w - N < gates.length := by omega
      have hmem : gates[w - N] ∈ gates := List.getElem_mem hk
      have hcov : ∀ y ∈ SS gates Z W M w,
          ∃ r ∈ (gates[w - N]).inputs.filter (fun r => decide (r < w)),
            y ∈ SS gates Z W M r := by
        intro y hy
        have ty := (mem_SS gates Z W M w y).mp hy
        rcases (hg _ hmem).1 with hop | hop
        · have hnot : ¬ (∀ r ∈ (gates[w - N]).inputs, r < w ∧ vl gates (Z y.1) r = true) := by
            rw [← vl_and gates (Z y.1) w (by omega) hw hop]
            simp [ty.2.1]
          push Not at hnot
          obtain ⟨r, hr, hrn⟩ := hnot
          have h4 := (vl_and gates (W y.1 y.2) w (by omega) hw hop).mp ty.2.2 r hr
          refine ⟨r, List.mem_filter.mpr ⟨hr, by simpa using h4.1⟩,
            (mem_SS gates Z W M r y).mpr ⟨ty.1, ?_, h4.2⟩⟩
          have h5 := hrn h4.1
          simpa using h5
        · obtain ⟨r, hr, hrw, hv⟩ := (vl_or gates (W y.1 y.2) w (by omega) hw hop).mp ty.2.2
          refine ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hrw⟩,
            (mem_SS gates Z W M r y).mpr ⟨ty.1, ?_, hv⟩⟩
          by_contra hne
          have ht : vl gates (Z y.1) r = true := by simpa using hne
          have h1 := (vl_or gates (Z y.1) w (by omega) hw hop).mpr ⟨r, hr, hrw, ht⟩
          rw [ty.2.1] at h1
          exact Bool.noConfusion h1
      have hll : ((gates[w - N]).inputs.filter (fun r => decide (r < w))).length ≤ 2 :=
        le_trans (List.length_filter_le _ _) (hg _ hmem).2
      have hlne : (gates[w - N]).inputs.filter (fun r => decide (r < w)) ≠ [] := by
        intro e
        obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (SS gates Z W M w).card)
        obtain ⟨r, hr, _⟩ := hcov y hy
        rw [e] at hr
        simp at hr
      obtain ⟨r1, r2, m1, m2, hall⟩ := two_cover _ hll hlne
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hw⟩, by omega⟩,
        r1, r2, ?_, ?_, ?_⟩
      · simpa using (List.mem_filter.mp m1).2
      · simpa using (List.mem_filter.mp m2).2
      · intro y hy
        obtain ⟨r, hr, hyr⟩ := hcov y hy
        rcases hall r hr with e | e
        · rw [e] at hyr
          exact Finset.mem_union_left _ hyr
        · rw [e] at hyr
          exact Finset.mem_union_right _ hyr

lemma sides {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Z : Fin 3 → Fin N → Bool) (W : Fin 3 → Fin N → Fin N → Bool) (M : Fin 3 → Finset (Fin N))
    (hin : ∀ x v p, Z x v = false → p ∈ M x → W x p v = true → p = v)
    (hI : ∀ x x', x ≠ x' → (M x ∩ M x').card ≤ 1)
    (hG : ∀ x x' z v, x ≠ x' → z ≠ x → z ≠ x' → v ∈ M x → v ∈ M x' →
      ∀ u, W x v u = true → Z z u = true)
    (q : ℕ) (hM : ∀ x, (M x).card = q + 1) (o : Fin 3 → ℕ)
    (hz : ∀ x, vl gates (Z x) (o x) = false)
    (ho : ∀ x, ∀ p ∈ M x, vl gates (W x p) (o x) = true)
    (hoz : ∀ x x', x ≠ x' → vl gates (Z x) (o x') = true) :
    3 * q ≤ ((Finset.Ico N (N + gates.length)).filter
      (fun w => 2 ≤ (SS gates Z W M w).card)).card := by
  have hgm : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → Finset ((_ : Fin 3) × Fin N),
      ∀ w, T w = Finset.univ.sigma (fun x => if o x = w then M x else ∅) := ⟨_, fun _ => rfl⟩
  have memT : ∀ w y, y ∈ T w ↔ o y.1 = w ∧ y.2 ∈ M y.1 := by
    intro w y
    rw [hTdef, Finset.mem_sigma]
    by_cases e : o y.1 = w
    · simp [e]
    · simp [e]
  have hT : ∀ w, T w ⊆ SS gates Z W M w := by
    intro w y hy
    obtain ⟨e, hp⟩ := (memT w y).mp hy
    refine (mem_SS gates Z W M w y).mpr ⟨hp, ?_, ?_⟩
    · rw [← e]
      exact hz y.1
    · rw [← e]
      exact ho y.1 y.2 hp
  have hmain := core2 (SS gates Z W M)
    ((Finset.Ico N (N + gates.length)).filter (fun w => 2 ≤ (SS gates Z W M w).card))
    cap cap_empty cap_union
    (fun w A1 A2 h1 h2 hd => cap_split A1 A2 (SS_hone gates hgm Z W M hI hG w A1 A2 h1 h2 hd))
    (SS_local gates hg Z W M hin hG) (N + gates.length) T hT
  have hcov : Finset.univ.sigma M ⊆ (Finset.range (N + gates.length)).biUnion T := by
    intro y hy
    have hp : y.2 ∈ M y.1 := (Finset.mem_sigma.mp hy).2
    have hlt : o y.1 < N + gates.length := by
      by_contra hge
      have h1 := ho y.1 y.2 hp
      rw [vl_missing gates _ _ (by omega)] at h1
      exact Bool.noConfusion h1
    exact Finset.mem_biUnion.mpr ⟨o y.1, Finset.mem_range.mpr hlt, (memT _ y).mpr ⟨rfl, hp⟩⟩
  have hcard : (Finset.univ.sigma M).card = 3 * (q + 1) := by
    rw [Finset.card_sigma]
    simp [hM]
  have hcap : ∀ w, cap (T w) ≤ ∑ x : Fin 3, (if o x = w then (1 : ℕ) else 0) := by
    intro w
    by_cases he : T w = ∅
    · rw [he, cap_empty]
      exact Nat.zero_le _
    · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr he
      have hnp : ¬ pr (T w) := by
        rintro ⟨u, hu, u', hu', hne, _⟩
        have e1 := ((memT w u).mp hu).1
        have e2 := ((memT w u').mp hu').1
        have h1 := hoz u.1 u'.1 hne
        rw [e2, ← e1, hz u.1] at h1
        exact Bool.noConfusion h1
      rw [cap_npr _ he hnp]
      have e := ((memT w y).mp hy).1
      have h1 : (if o y.1 = w then (1 : ℕ) else 0) ≤
          ∑ x : Fin 3, (if o x = w then (1 : ℕ) else 0) :=
        Finset.single_le_sum (f := fun x : Fin 3 => if o x = w then (1 : ℕ) else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ y.1)
      rw [ifp e] at h1
      exact h1
  have hone1 : ∀ x : Fin 3,
      ∑ w ∈ Finset.range (N + gates.length), (if o x = w then (1 : ℕ) else 0) ≤ 1 := by
    intro x
    rw [Finset.sum_ite_eq (Finset.range (N + gates.length)) (o x) (fun _ => (1 : ℕ))]
    split_ifs <;> simp
  have hsum : ∑ w ∈ Finset.range (N + gates.length), cap (T w) ≤ 3 := by
    refine le_trans (Finset.sum_le_sum (fun w _ => hcap w)) ?_
    rw [Finset.sum_comm]
    refine le_trans (Finset.sum_le_sum (fun x _ => hone1 x)) ?_
    simp
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_le_card (Finset.filter_subset (fun u => u < N + gates.length)
    ((Finset.Ico N (N + gates.length)).filter (fun w => 2 ≤ (SS gates Z W M w).card)))
  rw [hcard] at h1
  omega

lemma fin3c : ∀ x x' x0 : Fin 3, x ≠ x' → x ≠ x0 → x ≠ x0 + 1 → x' ≠ x0 → x' ≠ x0 + 1 → False := by
  decide

lemma fin3d : ∀ x x' : Fin 3, x ≠ x' → x' = x + 1 ∨ x = x' + 1 := by
  decide

lemma fin3b : ∀ x y : Fin 3, y = x + 1 → x = y + 1 → False := by
  decide

lemma m51 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    (∀ p : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (i : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = P))) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  intro q N L va vb vc sa sb sc hq hN hcard hint hjoin hnc hbsa hcsa hcsb hasb hasc hbsc
    gates o j h hg hwf hjop hone hhj hjin hout hand hh hrd
  generalize hk : (Finset.univ.filter (fun i : Fin gates.length =>
    (N + (j : ℕ)) ∈ (gates.get i).inputs)) = Rd
  have memRd : ∀ i, i ∈ Rd ↔ (N + (j : ℕ)) ∈ (gates.get i).inputs := by
    intro i
    rw [← hk]
    simp
  obtain ⟨c1, c2, c3, c4, _⟩ := c50 q N L va vb vc sa sb sc hq hN hcard hint hjoin hnc hbsa hcsa
    hcsb hasb hasc hbsc gates o j h hg hwf hjop hone hhj hjin hout hand
    (fun w x => Circuit.eval ⟨gates, w⟩ (List.ofFn x))
    (fun w x => Circuit.eval ⟨gates.set j ⟨GateOp.or, []⟩, w⟩ (List.ofFn x))
    (fun _ _ => rfl) (fun _ _ => rfl) hh hrd
  obtain ⟨gs, hgs⟩ : ∃ gs : List Gate, gs = gates.set j ⟨GateOp.or, []⟩ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : (Fin N → Bool) → Prop,
      ∀ x, D x ↔ ∀ t, vl gs x (o t) = decide (∃ v ∈ L t, x v = true) :=
    ⟨fun x => ∀ t, vl gs x (o t) = decide (∃ v ∈ L t, x v = true), fun _ => Iff.rfl⟩
  have hlen : gs.length = gates.length := by
    rw [hgs, List.length_set]
  have d1 : ∀ (w : ℕ) (x : Fin N → Bool), vl gs x w = true → vl gates x w = true := by
    intro w x hx
    rw [hgs] at hx
    exact c1 w x hx
  have d2 : ∀ (w : ℕ) (x : Fin N → Bool), vl gates x (N + (h : ℕ)) = true → vl gs x w = vl gates x w := by
    intro w x hx
    rw [hgs]
    exact c2 w x hx
  have d3 : ∀ (i : Fin gates.length) (x : Fin N → Bool), (N + (j : ℕ)) ∈ (gates.get i).inputs →
      vl gs x (N + (i : ℕ)) = false := by
    intro i x hm
    rw [hgs]
    exact c3 i x hm
  have d4 : ∀ (t P : Fin N), P ∈ L t → vl gs (fun v : Fin N => decide (v = P)) (o t) = false →
      ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧
        vl gates (fun v : Fin N => decide (v = P)) (N + (i : ℕ)) = true := by
    intro t P hP hf
    rw [hgs] at hf
    exact c4 t P hP hf
  have dout : ∀ (t : Fin N) (x : Fin N → Bool), vl gates x (o t) = decide (∃ v ∈ L t, x v = true) := fun t x => hout t x
  have dh : ∀ p : Fin N, vl gates (fun v : Fin N => decide (v = p)) (N + (h : ℕ)) = true ↔
      (p = va ∨ p = vb ∨ p = vc) := fun p => hh p
  have drd : ∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs →
      vl gates (fun v : Fin N => decide (v = P)) (N + (i : ℕ)) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc := fun i P hm hv => hrd i P hm hv
  have hg' : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hgm
    have hi' : i < gates.length := by
      rw [← hlen]
      exact hi
    subst hgs
    rw [List.getElem_set] at e
    by_cases hij : (j : ℕ) = i
    · rw [ifp hij] at e
      rw [← e]
      exact ⟨Or.inr rfl, by simp⟩
    · rw [ifn hij] at e
      rw [← e]
      have h0 := hg gates[i] (List.getElem_mem hi')
      refine ⟨?_, h0.2⟩
      rcases h0.1 with a | a | a
      · exact Or.inl a
      · exact Or.inr a
      · exact absurd (congrArg Fin.val (hone ⟨i, hi'⟩ a)).symm hij
  have hgm' : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hgm => (hg' g hgm).1
  have mono' : ∀ (x y : Fin N → Bool), (∀ v, x v = true → y v = true) →
      ∀ w, vl gs x w = true → vl gs y w = true := vl_mono gs hgm'
  have hle : ∀ (t : Fin N) (x : Fin N → Bool), vl gs x (o t) = true → ∃ v ∈ L t, x v = true := by
    intro t x hx
    have h1 := d1 _ _ hx
    rw [dout t x] at h1
    exact of_decide_eq_true h1
  have hjf : ∀ x : Fin N → Bool, vl gs x (N + (j : ℕ)) = false := by
    intro x
    by_contra hf
    have hf' : vl gs x (N + (j : ℕ)) = true := by simpa using hf
    have hjl : N + (j : ℕ) < N + gs.length := by
      rw [hlen]
      have := j.isLt
      omega
    have hget : gs[N + (j : ℕ) - N]'(by omega) = ⟨GateOp.or, []⟩ := by
      subst hgs
      simp
    have hop : (gs[N + (j : ℕ) - N]'(by omega)).op = GateOp.or := by
      rw [hget]
    obtain ⟨r, hr, _⟩ := (vl_or gs x (N + (j : ℕ)) (by omega) hjl hop).mp hf'
    rw [hget] at hr
    simp at hr
  obtain ⟨s, hs0, hs1, hs2⟩ : ∃ s : Fin 3 → Fin N, s 0 = sa ∧ s 1 = sb ∧ s 2 = sc :=
    ⟨![sa, sb, sc], rfl, rfl, rfl⟩
  obtain ⟨vo, hv0, hv1, hv2⟩ : ∃ vo : Fin 3 → Fin N, vo 0 = va ∧ vo 1 = vb ∧ vo 2 = vc :=
    ⟨![va, vb, vc], rfl, rfl, rfl⟩
  have k3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have V1 : ∀ x z : Fin 3, x ≠ z → vo z ∈ L (s x) := by
    intro x z hxz
    rcases k3 x with rfl | rfl | rfl <;> rcases k3 z with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxz
        | (simp only [hs0, hs1, hs2, hv0, hv1, hv2]; assumption)
  have V2 : ∀ x : Fin 3, vo x ∉ L (s x) := by
    intro x hx
    rcases k3 x with rfl | rfl | rfl
    · rw [hs0, hv0] at hx
      exact hnc sa ⟨hx, hbsa, hcsa⟩
    · rw [hs1, hv1] at hx
      exact hnc sb ⟨hasb, hx, hcsb⟩
    · rw [hs2, hv2] at hx
      exact hnc sc ⟨hasc, hbsc, hx⟩
  have isV : ∀ p, (p = va ∨ p = vb ∨ p = vc) ↔ ∃ z, p = vo z := by
    intro p
    constructor
    · rintro (e | e | e)
      · exact ⟨0, e.trans hv0.symm⟩
      · exact ⟨1, e.trans hv1.symm⟩
      · exact ⟨2, e.trans hv2.symm⟩
    · rintro ⟨z, e⟩
      rcases k3 z with rfl | rfl | rfl
      · exact Or.inl (e.trans hv0)
      · exact Or.inr (Or.inl (e.trans hv1))
      · exact Or.inr (Or.inr (e.trans hv2))
  have onS : ∀ p, (p ∈ L sa ∨ p ∈ L sb ∨ p ∈ L sc) → ∃ x, p ∈ L (s x) := by
    rintro p (e | e | e)
    · exact ⟨0, by rw [hs0]; exact e⟩
    · exact ⟨1, by rw [hs1]; exact e⟩
    · exact ⟨2, by rw [hs2]; exact e⟩
  have two : ∀ (t t' a b : Fin N), a ≠ b → a ∈ L t → b ∈ L t → a ∈ L t' → b ∈ L t' →
      t = t' := by
    intro t t' a b hab h1 h2 h3 h4
    by_contra hne
    exact hab (Finset.card_le_one.mp (le_of_eq (hint t t' hne)) a
      (Finset.mem_inter.mpr ⟨h1, h3⟩) b (Finset.mem_inter.mpr ⟨h2, h4⟩))
  have F1 : ∀ x x' : Fin 3, x ≠ x' → s x ≠ s x' := by
    intro x x' hne e
    have h1 := V1 x x' hne
    rw [e] at h1
    exact V2 x' h1
  have F2 : ∀ x x' : Fin 3, x ≠ x' → (L (s x) ∩ L (s x')).card ≤ 1 :=
    fun x x' hne => le_of_eq (hint _ _ (F1 x x' hne))
  have F4 : ∀ (x x' z : Fin 3) (p : Fin N), x ≠ x' → z ≠ x → z ≠ x' → p ∈ L (s x) →
      p ∈ L (s x') → p = vo z :=
    fun x x' z p hne hz hz' h1 h2 => Finset.card_le_one.mp (F2 x x' hne) p
      (Finset.mem_inter.mpr ⟨h1, h2⟩) (vo z)
      (Finset.mem_inter.mpr ⟨V1 x z (Ne.symm hz), V1 x' z (Ne.symm hz')⟩)
  have third3 : ∀ x x' : Fin 3, x ≠ x' → ∃ z, z ≠ x ∧ z ≠ x' := by decide
  have onesd : ∀ (p : Fin N) (x x0 : Fin 3), (∀ z, p ≠ vo z) → p ∈ L (s x) → p ∈ L (s x0) →
      x = x0 := by
    intro p x x0 hnv h1 h2
    by_contra hne
    obtain ⟨z, hz, hz'⟩ := third3 x x0 hne
    exact hnv z (F4 x x0 z p hne hz hz' h1 h2)
  have ne1 : ∀ x : Fin 3, x ≠ x + 1 := by decide
  have hhv : ∀ (x : Fin N → Bool) (z : Fin 3), x (vo z) = true →
      vl gs x (N + (h : ℕ)) = true := by
    intro x z hx
    have h1 : vl gates (fun v : Fin N => decide (v = vo z)) (N + (h : ℕ)) = true :=
      (dh (vo z)).mpr ((isV (vo z)).mpr ⟨z, rfl⟩)
    have h2 : vl gs (fun v : Fin N => decide (v = vo z)) (N + (h : ℕ)) = true :=
      (d2 _ _ h1).trans h1
    refine mono' _ x (fun v hv => ?_) _ h2
    rw [of_decide_eq_true hv]
    exact hx
  have Dvert : ∀ (x : Fin N → Bool) (z : Fin 3), x (vo z) = true → D x := by
    intro x z hx
    rw [hD]
    intro t
    exact (d2 (o t) x (d1 _ _ (hhv x z hx))).trans (dout t x)
  have Dgood : ∀ p : Fin N, ¬ ((∃ x, p ∈ L (s x)) ∧ ∀ z, p ≠ vo z) →
      D (fun v : Fin N => decide (v = p)) := by
    intro p hp
    by_cases hv : ∃ z, p = vo z
    · obtain ⟨z, e⟩ := hv
      exact Dvert _ z (by simp [e])
    · rw [hD]
      intro t
      by_cases hpt : p ∈ L t
      · have hvl : vl gs (fun v : Fin N => decide (v = p)) (o t) = true := by
          by_contra hf
          have hf' : vl gs (fun v : Fin N => decide (v = p)) (o t) = false := by simpa using hf
          obtain ⟨i, hm, hv2⟩ := d4 t p hpt hf'
          have h3 := drd i p hm hv2
          exact hp ⟨onS p h3.1, fun z e => hv ⟨z, e⟩⟩
        rw [hvl]
        exact (decide_eq_true ⟨p, hpt, by simp⟩).symm
      · have hvl : vl gs (fun v : Fin N => decide (v = p)) (o t) = false := by
          by_contra hf
          have hf' : vl gs (fun v : Fin N => decide (v = p)) (o t) = true := by simpa using hf
          obtain ⟨v, hvt, hvp⟩ := hle t _ hf'
          have e : v = p := by simpa using hvp
          rw [e] at hvt
          exact hpt hvt
        rw [hvl]
        refine (decide_eq_false ?_).symm
        rintro ⟨v, hvt, hvp⟩
        have e : v = p := by simpa using hvp
        rw [e] at hvt
        exact hpt hvt
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin 3 → Fin N → Bool, ∀ x u, Z x u = decide (u ∉ L (s x)) :=
    ⟨fun x u => decide (u ∉ L (s x)), fun _ _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Fin 3 → Fin N → Fin N → Bool,
      ∀ x p u, W x p u = decide (u = p ∨ ((∀ z, p ≠ vo z) ∧ u = vo x)) :=
    ⟨fun x p u => decide (u = p ∨ ((∀ z, p ≠ vo z) ∧ u = vo x)), fun _ _ _ => rfl⟩
  have DZ : ∀ x, D (Z x) := fun x => Dvert (Z x) x (by
    rw [hZ]
    exact decide_eq_true (V2 x))
  have DW : ∀ x p, D (W x p) := by
    intro x p
    by_cases hv : ∃ z, p = vo z
    · obtain ⟨z, e⟩ := hv
      refine Dvert (W x p) z ?_
      rw [hW]
      exact decide_eq_true (Or.inl e.symm)
    · refine Dvert (W x p) x ?_
      rw [hW]
      exact decide_eq_true (Or.inr ⟨fun z e => hv ⟨z, e⟩, rfl⟩)
  have hsides := sides gs hg' Z W (fun x => L (s x))
    (by
      intro x v p hz hp hw
      rw [hZ] at hz
      have hv : v ∈ L (s x) := by simpa using hz
      rw [hW] at hw
      rcases of_decide_eq_true hw with e | ⟨_, e⟩
      · exact e.symm
      · rw [e] at hv
        exact absurd hv (V2 x))
    F2
    (by
      intro x x' z v hne hz hz' h1 h2 u hu
      have ev := F4 x x' z v hne hz hz' h1 h2
      rw [hW] at hu
      rw [hZ]
      rcases of_decide_eq_true hu with e | ⟨hnv, _⟩
      · rw [e, ev]
        exact decide_eq_true (V2 z)
      · exact absurd ev (hnv z))
    q (fun x => hcard (s x)) (fun x => o (s x))
    (by
      intro x
      have h1 := (hD (Z x)).mp (DZ x) (s x)
      rw [h1]
      refine decide_eq_false ?_
      rintro ⟨v, hv, hzv⟩
      rw [hZ] at hzv
      exact (of_decide_eq_true hzv) hv)
    (by
      intro x p hp
      have h1 := (hD (W x p)).mp (DW x p) (s x)
      rw [h1]
      refine decide_eq_true ⟨p, hp, ?_⟩
      rw [hW]
      exact decide_eq_true (Or.inl rfl))
    (by
      intro x x' hne
      have h1 := (hD (Z x)).mp (DZ x) (s x')
      rw [h1]
      refine decide_eq_true ⟨vo x, V1 x' x (Ne.symm hne), ?_⟩
      rw [hZ]
      exact decide_eq_true (V2 x))
  obtain ⟨Gm, hGm⟩ : ∃ Gm : Finset ℕ, Gm = (Finset.Ico N (N + gs.length)).filter
      (fun w => 2 ≤ (SS gs Z W (fun x => L (s x)) w).card) := ⟨_, rfl⟩
  rw [← hGm] at hsides
  have sinj : Function.Injective s := by
    intro x x' e
    by_contra hne
    exact F1 x x' hne e
  obtain ⟨Lam, hLamdef⟩ : ∃ Lam : Finset (Fin N), Lam = (Finset.univ.image s)ᶜ := ⟨_, rfl⟩
  have memLam : ∀ t, t ∈ Lam ↔ ∀ x, s x ≠ t := by
    intro t
    rw [hLamdef]
    simp
  have cLam : Lam.card = N - 3 := by
    rw [hLamdef, Finset.card_compl, Finset.card_image_of_injective _ sinj]
    simp
  obtain ⟨B, hBdef⟩ : ∃ B : Fin N → Fin N → Finset (Fin N), ∀ t p v, v ∈ B t p ↔
      ((∀ z, p ≠ vo z) ∧ ∃ x, p ∈ L (s x) ∧ v = vo (x + 1)) :=
    ⟨fun _ p => Finset.univ.filter
      (fun v => (∀ z, p ≠ vo z) ∧ ∃ x, p ∈ L (s x) ∧ v = vo (x + 1)),
      fun t p v => by simp⟩
  have hoff : ∀ t : Fin N, ∃ z, vo z ∉ L t := by
    intro t
    by_contra hcon
    have hall : ∀ z, vo z ∈ L t := fun z => by
      by_contra hz
      exact hcon ⟨z, hz⟩
    have h0 := hall 0
    have h1 := hall 1
    have h2 := hall 2
    rw [hv0] at h0
    rw [hv1] at h1
    rw [hv2] at h2
    exact hnc t ⟨h0, h1, h2⟩
  have hzD : ∀ t : Fin N, D (zf (L t)) := by
    intro t
    obtain ⟨z, hz⟩ := hoff t
    exact Dvert _ z (decide_eq_true hz)
  have hB : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (wf (B t) p) := by
    intro t ht p hp
    constructor
    · apply Finset.eq_empty_of_forall_notMem
      intro v hv
      obtain ⟨hvB, hvt⟩ := Finset.mem_inter.mp hv
      obtain ⟨hnv, x, hpx, ev⟩ := (hBdef t p v).mp hvB
      have h1 := two (s x) t p v (by rw [ev]; exact hnv (x + 1)) hpx
        (by rw [ev]; exact V1 x (x + 1) (ne1 x)) hp hvt
      exact (memLam t).mp ht x h1
    · by_cases hbad : (∃ x, p ∈ L (s x)) ∧ ∀ z, p ≠ vo z
      · obtain ⟨⟨x, hpx⟩, hnv⟩ := hbad
        refine Dvert _ (x + 1) ?_
        exact decide_eq_true (Or.inr ((hBdef t p _).mpr ⟨hnv, x, hpx, rfl⟩))
      · have e : wf (B t) p = fun v : Fin N => decide (v = p) := by
          funext v
          have hn : v ∉ B t p := by
            intro hv
            obtain ⟨hnv, x, hpx, _⟩ := (hBdef t p v).mp hv
            exact hbad ⟨⟨x, hpx⟩, hnv⟩
          simp [wf, hn]
        rw [e]
        exact Dgood p hbad
  have hcross : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' →
      ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
        (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty)) := by
    rintro t ht t' ht' _ ⟨⟨p, hp, v, hv⟩, ⟨p', hp', v', hv'⟩⟩
    obtain ⟨hvB, hvt'⟩ := Finset.mem_inter.mp hv
    obtain ⟨hnv, x, hpx, ev⟩ := (hBdef t p v).mp hvB
    obtain ⟨hvB', hvt⟩ := Finset.mem_inter.mp hv'
    obtain ⟨hnv', y, hpy, ev'⟩ := (hBdef t' p' v').mp hvB'
    have hpm := Finset.mem_sdiff.mp hp
    have hpm' := Finset.mem_sdiff.mp hp'
    rw [ev] at hvt'
    rw [ev'] at hvt
    have e1 : y = x + 1 := by
      by_contra hy
      exact (memLam t').mp ht' y (two (s y) t' p' (vo (x + 1)) (hnv' (x + 1)) hpy
        (V1 y (x + 1) hy) hpm'.1 hvt')
    have e2 : x = y + 1 := by
      by_contra hx
      exact (memLam t).mp ht x (two (s x) t p (vo (y + 1)) (hnv (y + 1)) hpx
        (V1 x (y + 1) hx) hpm.1 hvt)
    exact fin3b x y e1 e2
  obtain ⟨J0, hJ0def⟩ : ∃ J0 : Finset ℕ, J0 = insert (N + (h : ℕ)) (insert (N + (j : ℕ))
      (Rd.image (fun i : Fin gates.length => N + (i : ℕ)))) := ⟨_, rfl⟩
  have rdlt : ∀ i ∈ Rd, (j : ℕ) < (i : ℕ) := by
    intro i hi
    have h1 := hwf i _ ((memRd i).mp hi)
    omega
  have hhjn : (h : ℕ) < (j : ℕ) := hhj
  have cJ0 : J0.card = Rd.card + 2 := by
    have n1 : N + (j : ℕ) ∉ Rd.image (fun i : Fin gates.length => N + (i : ℕ)) := by
      intro hm
      obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hm
      have h1 := rdlt i hi
      omega
    have n2 : N + (h : ℕ) ∉ insert (N + (j : ℕ))
        (Rd.image (fun i : Fin gates.length => N + (i : ℕ))) := by
      intro hm
      rcases Finset.mem_insert.mp hm with e | hm
      · omega
      · obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hm
        have h1 := rdlt i hi
        omega
    have c1' : (Rd.image (fun i : Fin gates.length => N + (i : ℕ))).card = Rd.card :=
      Finset.card_image_of_injective _ (fun a b e => Fin.ext (by
        have e' : N + (a : ℕ) = N + (b : ℕ) := e
        omega))
    have c2' := Finset.card_insert_of_notMem n1
    have c3' := Finset.card_insert_of_notMem n2
    rw [hJ0def]
    omega
  have PJ : ∀ w ∈ J0, (∀ x : Fin N → Bool, vl gs x w = false) ∨
      (∀ t : Fin N, vl gs (zf (L t)) w = true) := by
    intro w hw
    rw [hJ0def] at hw
    rcases Finset.mem_insert.mp hw with e | hw
    · right
      intro t
      obtain ⟨z, hz⟩ := hoff t
      rw [e]
      exact hhv _ z (decide_eq_true hz)
    · rcases Finset.mem_insert.mp hw with e | hw
      · left
        intro x
        rw [e]
        exact hjf x
      · left
        intro x
        obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hw
        rw [← e]
        exact d3 i x ((memRd i).mp hi)
  have key : ∀ t ∈ Lam, ∀ w, 2 ≤ (S gs (zf (L t)) (wf (B t)) (L t) w).card →
      (SS gs Z W (fun x => L (s x)) w).card ≤ 1 := by
    intro t ht w h2
    by_contra hcon
    obtain ⟨y, hy, y', hy', hyy⟩ := Finset.one_lt_card.mp
      (by omega : 1 < (SS gs Z W (fun x => L (s x)) w).card)
    obtain ⟨p1, hp1, p2, hp2, hpp⟩ := Finset.one_lt_card.mp
      (by omega : 1 < (S gs (zf (L t)) (wf (B t)) (L t) w).card)
    have tp1 := Finset.mem_filter.mp hp1
    have tp2 := Finset.mem_filter.mp hp2
    have ty := (mem_SS gs Z W _ w y).mp hy
    have ty' := (mem_SS gs Z W _ w y').mp hy'
    have hzt := tp1.2.1
    have Pt : ∀ p, vl gs (wf (B t) p) w = true → ∀ x, vl gs (Z x) w = false →
        p ∈ L (s x) ∨ ((∀ z, p ≠ vo z) ∧ ∃ x0, p ∈ L (s x0) ∧ x ≠ x0 ∧ x ≠ x0 + 1) := by
      intro p hw x hzx
      by_contra hc
      have hall : ∀ u, wf (B t) p u = true → Z x u = true := by
        intro u hu
        rw [hZ]
        apply decide_eq_true
        intro hux
        apply hc
        have hu' : u = p ∨ u ∈ B t p := by simpa [wf] using hu
        rcases hu' with e | hB'
        · left
          rw [← e]
          exact hux
        · obtain ⟨hnv, x0, hpx0, e⟩ := (hBdef t p u).mp hB'
          by_cases hx0 : x = x0
          · left
            rw [hx0]
            exact hpx0
          · right
            refine ⟨hnv, x0, hpx0, hx0, ?_⟩
            intro e2
            rw [e, ← e2] at hux
            exact V2 x hux
      have h3 := mono' (wf (B t) p) (Z x) hall w hw
      rw [hzx] at h3
      exact Bool.noConfusion h3
    have Tg : ∀ u : (_ : Fin 3) × Fin N, vl gs (W u.1 u.2) w = true →
        u.2 ∈ L t ∨ ((∀ z, u.2 ≠ vo z) ∧ vo u.1 ∈ L t) := by
      intro u hw
      by_contra hc
      have hall : ∀ a, W u.1 u.2 a = true → zf (L t) a = true := by
        intro a ha
        show decide (a ∉ L t) = true
        apply decide_eq_true
        intro hat
        apply hc
        rw [hW] at ha
        rcases of_decide_eq_true ha with e | ⟨hnv, e⟩
        · left
          rw [← e]
          exact hat
        · right
          exact ⟨hnv, by rw [← e]; exact hat⟩
      have h3 := mono' _ _ hall w hw
      rw [hzt] at h3
      exact Bool.noConfusion h3
    by_cases hx : y.1 = y'.1
    · have h22 : y.2 ≠ y'.2 := fun e => hyy (Sigma.ext hx (heq_of_eq e))
      have hvt : vo y.1 ∈ L t := by
        rcases Tg y ty.2.2 with a | a
        · rcases Tg y' ty'.2.2 with b | b
          · exfalso
            have hy2 : y'.2 ∈ L (s y.1) := by
              rw [hx]
              exact ty'.1
            exact (memLam t).mp ht y.1 (two (s y.1) t y.2 y'.2 h22 ty.1 hy2 a b)
          · rw [hx]
            exact b.2
        · exact a.2
      have inx : ∀ p, p ∈ L t → vl gs (wf (B t) p) w = true → p ∈ L (s y.1) := by
        intro p hpt hw
        rcases Pt p hw y.1 ty.2.1 with a | ⟨hnv, x0, hpx0, hne0, _⟩
        · exact a
        · exfalso
          exact (memLam t).mp ht x0 (two (s x0) t p (vo y.1) (hnv y.1) hpx0
            (V1 x0 y.1 (Ne.symm hne0)) hpt hvt)
      exact (memLam t).mp ht y.1 (two (s y.1) t p1 p2 hpp (inx p1 tp1.1 tp1.2.2)
        (inx p2 tp2.1 tp2.2.2) tp1.1 tp2.1)
    · have Q : ∀ p, vl gs (wf (B t) p) w = true →
          (y'.1 = y.1 + 1 → p ∈ L (s y'.1)) ∧ (y.1 = y'.1 + 1 → p ∈ L (s y.1)) := by
        intro p hw
        have a := Pt p hw y.1 ty.2.1
        have b := Pt p hw y'.1 ty'.2.1
        constructor
        · intro e
          rcases b with b | ⟨hnv, x0, hpx0, n1, n2⟩
          · exact b
          · exfalso
            rcases a with a | ⟨_, x1, hpx1, m1, m2⟩
            · have e0 := onesd p y.1 x0 hnv a hpx0
              rw [← e0] at n2
              exact n2 e
            · have e0 := onesd p x1 x0 hnv hpx1 hpx0
              rw [e0] at m1 m2
              exact fin3c y.1 y'.1 x0 hx m1 m2 n1 n2
        · intro e
          rcases a with a | ⟨hnv, x0, hpx0, n1, n2⟩
          · exact a
          · exfalso
            rcases b with b | ⟨_, x1, hpx1, m1, m2⟩
            · have e0 := onesd p y'.1 x0 hnv b hpx0
              rw [← e0] at n2
              exact n2 e
            · have e0 := onesd p x1 x0 hnv hpx1 hpx0
              rw [e0] at m1 m2
              exact fin3c y.1 y'.1 x0 hx n1 n2 m1 m2
      rcases fin3d y.1 y'.1 hx with e | e
      · exact (memLam t).mp ht y'.1 (two (s y'.1) t p1 p2 hpp ((Q p1 tp1.2.2).1 e)
          ((Q p2 tp2.2.2).1 e) tp1.1 tp2.1)
      · exact (memLam t).mp ht y.1 (two (s y.1) t p1 p2 hpp ((Q p1 tp1.2.2).2 e)
          ((Q p2 tp2.2.2).2 e) tp1.1 tp2.1)
  have hJ1 : Gm ∪ J0 ⊆ Finset.Ico N (N + gs.length) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · rw [hGm] at hw
      exact (Finset.mem_filter.mp hw).1
    · rw [hJ0def] at hw
      rw [Finset.mem_Ico, hlen]
      rcases Finset.mem_insert.mp hw with e | hw
      · have h1 := h.isLt
        omega
      · rcases Finset.mem_insert.mp hw with e | hw
        · have h1 := j.isLt
          omega
        · obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hw
          have h1 := i.isLt
          omega
  have hJ2 : ∀ w ∈ Gm ∪ J0, ∀ t ∈ Lam, w ∉ U gs (zf (L t)) (wf (B t)) (L t) := by
    intro w hw t ht hU
    have h2 := ((mem_U _ _ _ _ _).mp hU).2.2
    rcases Finset.mem_union.mp hw with hw | hw
    · rw [hGm] at hw
      have h3 := (Finset.mem_filter.mp hw).2
      have h4 := key t ht w h2
      omega
    · obtain ⟨p, hp⟩ := Finset.card_pos.mp
        (by omega : 0 < (S gs (zf (L t)) (wf (B t)) (L t) w).card)
      have tp := Finset.mem_filter.mp hp
      rcases PJ w hw with a | a
      · have h5 := tp.2.2
        rw [a] at h5
        exact Bool.noConfusion h5
      · have h5 := tp.2.1
        rw [a t] at h5
        exact Bool.noConfusion h5
  have hdisj : Disjoint Gm J0 := by
    rw [Finset.disjoint_left]
    intro w hw hw0
    rw [hGm] at hw
    have h3 := (Finset.mem_filter.mp hw).2
    obtain ⟨y, hy⟩ := Finset.card_pos.mp
      (by omega : 0 < (SS gs Z W (fun x => L (s x)) w).card)
    have ty := (mem_SS gs Z W _ w y).mp hy
    rcases PJ w hw0 with a | a
    · have h5 := ty.2.2
      rw [a] at h5
      exact Bool.noConfusion h5
    · have h5 := ty.2.1
      have e : Z y.1 = zf (L (s y.1)) := by
        funext u
        rw [hZ]
        rfl
      rw [e, a (s y.1)] at h5
      exact Bool.noConfusion h5
  have hm := main2 q N L hcard hint D hzD gs o hg' (fun t x hx => (hD x).mp hx t) Lam B hB
    hcross (Gm ∪ J0) hJ1 hJ2
  rw [Finset.card_union_of_disjoint hdisj, cLam, cJ0, hlen] at hm
  have h3N : 3 ≤ N := by
    have h1 : q ≤ q ^ 2 + q := Nat.le_add_left _ _
    omega
  have e : q * (N - 3) + 3 * q = N * q := by
    rw [Nat.mul_comm 3 q, ← Nat.mul_add, Nat.sub_add_cancel h3N, Nat.mul_comm]
  omega

end PEqualNP.Outside.L_meta_1651

theorem PEqualNP.Outside.L_meta_1651 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    (∀ p : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (i : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = P))) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1651.m51
