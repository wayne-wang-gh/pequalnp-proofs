import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1655

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

private lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

private def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

private lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

private lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

private lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

private lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma W_prefix {n : ℕ} (gs rest : List Gate) (x : Fin n → Bool) (t : ℕ)
    (ht : t < n + gs.length) :
    (W (gs ++ rest) x).getD t false = (W gs x).getD t false := by
  induction rest using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton rest g ih =>
    have hne : ¬ t = n + (gs ++ rest).length := by
      rw [List.length_append]
      omega
    rw [← List.append_assoc, W_val, if_neg hne]
    exact ih

private lemma gate_eq {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < gs.length)
    (hord : ∀ w ∈ (gs[i]'hi).inputs, w < n + i) :
    (W gs x).getD (n + i) false =
      (gs[i]'hi).op.eval ((gs[i]'hi).inputs.map fun k => (W gs x).getD k false) := by
  have h1 := W_prefix (gs.take (i + 1)) (gs.drop (i + 1)) x (n + i)
    (by rw [List.length_take]; omega)
  rw [List.take_append_drop] at h1
  have hlen : n + i = n + (gs.take i).length := by
    rw [List.length_take]
    omega
  rw [h1, List.take_succ_eq_append_getElem hi, W_val, if_pos hlen]
  congr 1
  apply List.map_congr_left
  intro k hk
  have h2 := W_prefix (gs.take i) (gs.drop i) x k
    (by rw [List.length_take]; have := hord k hk; omega)
  rw [List.take_append_drop] at h2
  exact h2.symm

private lemma mono_gen {N : ℕ} (gates : List Gate) (ev : ℕ → (Fin N → Bool) → Bool)
    (F_in : ∀ (k : ℕ) (hk : k < N) (x : Fin N → Bool), ev k x = x ⟨k, hk⟩)
    (F_gate : ∀ (i : Fin gates.length) (x : Fin N → Bool),
      ev (N + (i : ℕ)) x = (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev k x))
    (F_out : ∀ (k : ℕ), N + gates.length ≤ k → ∀ x : Fin N → Bool, ev k x = false)
    (hord : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) (B : ℕ)
    (good : ∀ i : Fin gates.length, N + (i : ℕ) < B →
      (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or ∨ ev (N + (i : ℕ)) y = true) :
    ∀ w : ℕ, w < B → ev w x = true → ev w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwB hx
    by_cases h1 : w < N
    · rw [F_in w h1 x] at hx
      rw [F_in w h1 y]
      exact hxy _ hx
    · by_cases h2 : w < N + gates.length
      · obtain ⟨i, hi⟩ : ∃ i : Fin gates.length, w = N + (i : ℕ) :=
          ⟨⟨w - N, by omega⟩, by show w = N + (w - N); omega⟩
        subst hi
        rcases good i hwB with hand | hor | ht
        · rw [F_gate i x, hand] at hx
          rw [F_gate i y, hand]
          exact (all_true _ _).mpr (fun k hk =>
            ih k (hord i k hk) (lt_trans (hord i k hk) hwB) ((all_true _ _).mp hx k hk))
        · rw [F_gate i x, hor] at hx
          rw [F_gate i y, hor]
          obtain ⟨k, hk, hkt⟩ := (any_true _ _).mp hx
          exact (any_true _ _).mpr
            ⟨k, hk, ih k (hord i k hk) (lt_trans (hord i k hk) hwB) hkt⟩
        · exact ht
      · rw [F_out w (by omega) x] at hx
        exact Bool.noConfusion hx

private theorem base : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
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
  intro q N L i0 p0 p1 hq hN hcard hint hjoin hne hm0 hm1 gates o j h hg hord hjnot hjuniq hhj
    hjin hout ev hev hh0 hh1 hhp hhW
  have E : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = (W gates x).getD w false :=
    fun w x => hev w x
  have F_in : ∀ (k : ℕ) (hk : k < N) (x : Fin N → Bool), ev k x = x ⟨k, hk⟩ := by
    intro k hk x
    have e := W_prefix [] gates x k (by simpa using hk)
    rw [List.nil_append] at e
    rw [E, e]
    exact ofFn_getD_val x ⟨k, hk⟩
  have F_out : ∀ (k : ℕ), N + gates.length ≤ k → ∀ x : Fin N → Bool, ev k x = false := by
    intro k hk x
    rw [E]
    exact List.getD_eq_default _ _ (by rw [W_len]; omega)
  have F_gate : ∀ (i : Fin gates.length) (x : Fin N → Bool),
      ev (N + (i : ℕ)) x =
        (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev k x) := by
    intro i x
    have e := gate_eq gates x i.val i.isLt (hord i)
    have hfun : (fun k => (W gates x).getD k false) = fun k => ev k x :=
      funext (fun k => (E k x).symm)
    rw [hfun, ← E] at e
    exact e
  have hop : ∀ i : Fin gates.length, i ≠ j →
      (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or := by
    intro i hij
    rcases (hg (gates.get i) (List.get_mem gates i)).1 with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact absurd (hjuniq i a) hij
  have hz : ∀ x : Fin N → Bool, ev (N + (j : ℕ)) x = Bool.not (ev (N + (h : ℕ)) x) := by
    intro x
    obtain ⟨r, hr⟩ := hjin
    have e1 := F_gate j x
    rw [hjnot, hr] at e1
    exact e1
  have hzt : ∀ x : Fin N → Bool, ev (N + (h : ℕ)) x = false → ev (N + (j : ℕ)) x = true :=
    fun x hf => (hz x).trans (congrArg Bool.not hf)
  have hzf : ∀ x : Fin N → Bool, ev (N + (h : ℕ)) x = true → ev (N + (j : ℕ)) x = false :=
    fun x hf => (hz x).trans (congrArg Bool.not hf)
  have hlt : (h : ℕ) < (j : ℕ) := hhj
  have hmonoh : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) →
      ev (N + (h : ℕ)) x = true → ev (N + (h : ℕ)) y = true := by
    intro x y hxy
    refine mono_gen gates ev F_in F_gate F_out hord x y hxy (N + (j : ℕ)) ?_ (N + (h : ℕ))
      (by omega)
    intro i hi
    have hij : i ≠ j := by
      intro e
      rw [e] at hi
      exact lt_irrefl _ hi
    rcases hop i hij with a | a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
  have P1 : ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) →
      ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true := by
    intro x hx
    have hf : ev (N + (h : ℕ)) x = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have h3 := hmonoh x (fun v : Fin N => decide (v ∉ L i0))
        (fun v hv => decide_eq_true (hx v hv)) ht
      exact Bool.noConfusion (h3.symm.trans hhW)
    exact ⟨hf, hzt x hf⟩
  refine ⟨P1, ?_, hzf _ hh0, hzf _ hh1, ?_⟩
  · intro w hw hw0 hw1
    have hf := hhp w hw0 hw1
    exact ⟨hf, hzt _ hf⟩
  · intro w x y hx hy hxy hw
    refine mono_gen gates ev F_in F_gate F_out hord x y hxy (w + 1) ?_ w (Nat.lt_succ_self w) hw
    intro i hi
    by_cases hij : i = j
    · refine Or.inr (Or.inr ?_)
      rw [hij]
      exact (P1 y hy).2
    · rcases hop i hij with a | a
      · exact Or.inl a
      · exact Or.inr (Or.inl a)

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
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
    ∀ Sm Dm : Fin N → ℕ → Prop,
    (∀ (t : Fin N) (w : ℕ), Sm t w ↔ ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true → ∃ v ∈ L t, x v = true) →
    (∀ (t : Fin N) (w : ℕ), Dm t w ↔ (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t)) →
    ∀ Vs : Fin N → ℕ → Fin N → Prop,
    (∀ (t : Fin N) (w : ℕ) (v : Fin N), Vs t w v ↔ ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨ (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true))) →
    ∀ t : Fin N,
    (∀ (w : ℕ) (v : Fin N), Dm t w → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or → (Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e) ∧ (Dm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Dm t e)) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and → Sm t (N + (g : ℕ)) → ∃ e ∈ (gates.get g).inputs, Sm t e) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → Vs t w v → v ∈ L t) := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin hne hm0 hm1 gates o j h hg hord hjnot hjuniq hhj
    hjin hout ev hev hh0 hh1 hhp hhW Sm Dm hSm hDm Vs hVs t
  have hmono := (base q N L i0 p0 p1 hq hN hcard hint hjoin hne hm0 hm1 gates o j h hg hord hjnot
    hjuniq hhj hjin hout ev hev hh0 hh1 hhp hhW).2.2.2.2
  have E : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = (W gates x).getD w false :=
    fun w x => hev w x
  have F_gate : ∀ (i : Fin gates.length) (x : Fin N → Bool),
      ev (N + (i : ℕ)) x =
        (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev k x) := by
    intro i x
    have e := gate_eq gates x i.val i.isLt (hord i)
    have hfun : (fun k => (W gates x).getD k false) = fun k => ev k x :=
      funext (fun k => (E k x).symm)
    rw [hfun, ← E] at e
    exact e
  have C2 : ∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 →
      ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t := by
    intro w v hS hv he
    have hsup : ∀ u : Fin N, (fun uu : Fin N => decide (uu = v)) u = true → u ∉ L i0 := by
      intro u hu
      have hu1 : decide (u = v) = true := hu
      have hu2 : u = v := of_decide_eq_true hu1
      rw [hu2]
      exact hv
    obtain ⟨u, hu, hux⟩ := (hSm t w).mp hS (fun uu : Fin N => decide (uu = v)) hsup he
    have hu1 : decide (u = v) = true := hux
    have hu2 : u = v := of_decide_eq_true hu1
    rw [← hu2]
    exact hu
  have C1 : ∀ (w : ℕ) (v : Fin N), Dm t w →
      ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t := by
    intro w v hD he
    obtain ⟨hS, hD2⟩ := (hDm t w).mp hD
    by_cases hv : v ∈ L i0
    · exact hD2 v hv he
    · exact C2 w v hS hv he
  refine ⟨C1, C2, ?_, ?_, ?_⟩
  · intro g hor
    have hup : ∀ e ∈ (gates.get g).inputs, ∀ x : Fin N → Bool, ev e x = true →
        ev (N + (g : ℕ)) x = true := by
      intro e he x hx
      rw [F_gate g x, hor]
      exact (any_true _ _).mpr ⟨e, he, hx⟩
    have hsm : Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e := by
      intro hS e he
      refine (hSm t e).mpr ?_
      intro x hx hex
      exact (hSm t (N + (g : ℕ))).mp hS x hx (hup e he x hex)
    refine ⟨hsm, ?_⟩
    intro hD e he
    obtain ⟨hS, hD2⟩ := (hDm t (N + (g : ℕ))).mp hD
    exact (hDm t e).mpr ⟨hsm hS e he, fun p hp hep => hD2 p hp (hup e he _ hep)⟩
  · intro g hand hS
    by_contra hno
    have hwit : ∀ e : ℕ, ∃ x : Fin N → Bool, e ∈ (gates.get g).inputs →
        ((∀ v : Fin N, x v = true → v ∉ L i0) ∧ ev e x = true ∧
          ∀ v : Fin N, v ∈ L t → x v = true → False) := by
      intro e
      by_cases he : e ∈ (gates.get g).inputs
      · by_contra hc
        apply hno
        refine ⟨e, he, (hSm t e).mpr ?_⟩
        intro x hx hex
        by_contra hc2
        exact hc ⟨x, fun _ => ⟨hx, hex, fun v hv hxv => hc2 ⟨v, hv, hxv⟩⟩⟩
      · exact ⟨fun _ => false, fun hin => absurd hin he⟩
    choose xf hxf using hwit
    obtain ⟨y, hydef⟩ : ∃ y : Fin N → Bool,
        ∀ v : Fin N, y v = (gates.get g).inputs.any (fun e => xf e v) := ⟨_, fun _ => rfl⟩
    have hy : ∀ v : Fin N, y v = true → ∃ e ∈ (gates.get g).inputs, xf e v = true := by
      intro v hv
      rw [hydef v] at hv
      exact List.any_eq_true.mp hv
    have hyW : ∀ v : Fin N, y v = true → v ∉ L i0 := by
      intro v hv
      obtain ⟨e, he, hxe⟩ := hy v hv
      exact (hxf e he).1 v hxe
    have hall : ev (N + (g : ℕ)) y = true := by
      rw [F_gate g y, hand]
      refine (all_true _ _).mpr (fun e he => ?_)
      refine hmono e (xf e) y (hxf e he).1 hyW ?_ (hxf e he).2.1
      intro v hv
      rw [hydef v]
      exact List.any_eq_true.mpr ⟨e, he, hv⟩
    obtain ⟨v, hv, hyv⟩ := (hSm t (N + (g : ℕ))).mp hS y hyW hall
    obtain ⟨e, he, hxe⟩ := hy v hyv
    exact (hxf e he).2.2 v hv hxe
  · intro w v hS hV
    rcases (hVs t w v).mp hV with ⟨hD, he⟩ | ⟨_, hv, he⟩
    · exact C1 w v hD he
    · exact C2 w v hS hv he

end PEqualNP.Outside.L_meta_1655

theorem PEqualNP.Outside.L_meta_1655 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
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
    ∀ Sm Dm : Fin N → ℕ → Prop,
    (∀ (t : Fin N) (w : ℕ), Sm t w ↔ ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true → ∃ v ∈ L t, x v = true) →
    (∀ (t : Fin N) (w : ℕ), Dm t w ↔ (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t)) →
    ∀ Vs : Fin N → ℕ → Fin N → Prop,
    (∀ (t : Fin N) (w : ℕ) (v : Fin N), Vs t w v ↔ ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨ (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true))) →
    ∀ t : Fin N,
    (∀ (w : ℕ) (v : Fin N), Dm t w → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or → (Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e) ∧ (Dm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Dm t e)) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and → Sm t (N + (g : ℕ)) → ∃ e ∈ (gates.get g).inputs, Sm t e) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → Vs t w v → v ∈ L t) :=
  PEqualNP.Outside.L_meta_1655.main_aux
