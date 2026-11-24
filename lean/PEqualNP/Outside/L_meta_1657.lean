import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1657

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

end PEqualNP.Outside.L_meta_1657

open PEqualNP.Outside.L_meta_1657 in
theorem PEqualNP.Outside.L_meta_1657 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
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
    ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t → ev' (o t) (fun uu : Fin N => decide (uu = v)) = true := by
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
