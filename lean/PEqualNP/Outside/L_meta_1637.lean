import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1637

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

def vl {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  value (⟨gates, 0⟩ : Circuit) x w

lemma vl_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    vl gates x w = x ⟨w, h⟩ :=
  input_value (⟨gates, 0⟩ : Circuit) x ⟨w, h⟩

lemma vl_missing {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : vl gates x w = false :=
  missing_value (⟨gates, 0⟩ : Circuit) x w hw

lemma vl_gate {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) :
    vl gates x (n + k) =
      g.op.eval (g.inputs.map fun r => if r < n + k then vl gates x r else false) := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hk
  have h := gate_value (⟨gates, 0⟩ : Circuit) x (n + k) (by omega)
    (by show n + k < n + gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

lemma vl_and {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) (hop : g.op = GateOp.and) :
    vl gates x (n + k) = true ↔ ∀ r ∈ g.inputs, r < n + k ∧ vl gates x r = true := by
  rw [vl_gate gates x k g hk, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
  constructor
  · intro hall r hr
    have := hall _ ⟨r, hr, rfl⟩
    by_cases hrw : r < n + k
    · simpa [hrw] using this
    · simp [hrw] at this
  · rintro hall b ⟨r, hr, rfl⟩
    have := hall r hr
    simp [this.1, this.2]

lemma vl_or {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) (hop : g.op = GateOp.or) :
    vl gates x (n + k) = true ↔ ∃ r ∈ g.inputs, r < n + k ∧ vl gates x r = true := by
  rw [vl_gate gates x k g hk, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
  constructor
  · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    by_cases hrw : r < n + k
    · exact ⟨r, hr, hrw, by simpa [hrw] using hb⟩
    · simp [hrw] at hb
  · rintro ⟨r, hr, hrw, hv⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by simp [hrw, hv]⟩

theorem main (N : ℕ) (L : Fin N → Finset (Fin N)) (p0 p1 : Fin N)
    (T : Fin N → Fin N → Fin N → Bool)
    (hT : ∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t)))
    (gates : List Gate)
    (hg : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (ev : ℕ → (Fin N → Bool) → Bool) (hev : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = vl gates x w)
    (TS : Fin N → Fin N → ℕ → Prop)
    (hTS : ∀ (l m : Fin N) (w : ℕ), TS l m w ↔ (ev w (fun v : Fin N => decide (v ∉ L l)) = false ∧ ev w (fun v : Fin N => decide (v ∉ L m)) = false ∧ (∃ p ∈ L l, ev w (T l p) = true) ∧ ∃ p ∈ L m, ev w (T m p) = true))
    (Hg : Fin N → Fin N → Fin gates.length → Prop)
    (hHg : ∀ (l m : Fin N) (g : Fin gates.length), Hg l m g ↔ (TS l m (N + (g : ℕ)) ∧ ((gates.get g).op = GateOp.and ∨ ((gates.get g).op = GateOp.or ∧ ∀ e ∈ (gates.get g).inputs, ¬ TS l m e))))
    (l m : Fin N) (hl : p0 ∈ L l ∧ p1 ∉ L l) (hm : p1 ∈ L m ∧ p0 ∉ L m) :
      (∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m)) ∧
      (∀ p : Fin N, p ∈ L l → p ∈ L m → (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧ (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p)) ∧
      ∀ w : ℕ, TS l m w → ∃ ν : ℕ, (∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → ν ∈ Zs) ∧
        ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨ ∃ h : Fin gates.length, ν = (N + (h : ℕ)) ∧ Hg l m h) ∧
        (∀ s ∈ L l, ev ν (T l s) = true → ev w (T l s) = true) ∧ (∀ s ∈ L m, ev ν (T m s) = true → ev w (T m s) = true) ∧
        (∃ s ∈ L l, ev ν (T l s) = true) ∧ ∃ s ∈ L m, ev ν (T m s) = true := by
  have ev_in : ∀ (p : Fin N) (x : Fin N → Bool), ev (p : ℕ) x = x p := by
    intro p x
    rw [hev, vl_input gates x p p.2]
  have ev_miss : ∀ (w : ℕ) (x : Fin N → Bool), N + gates.length ≤ w → ev w x = false := by
    intro w x hw
    rw [hev]
    exact vl_missing gates x w hw
  have ev_or : ∀ (k : Fin gates.length) (x : Fin N → Bool), (gates.get k).op = GateOp.or →
      ∀ r ∈ (gates.get k).inputs, ev r x = true → ev (N + (k : ℕ)) x = true := by
    intro k x hop r hr hv
    rw [hev] at hv
    rw [hev]
    exact (vl_or gates x k _ (List.getElem?_eq_getElem k.2) hop).mpr ⟨r, hr, hwf k r hr, hv⟩
  have hA : ∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m) := by
    intro p
    rw [hTS]
    simp only [ev_in]
    constructor
    · rintro ⟨h1, h2, -, -⟩
      exact ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using h1, by simpa using h2, ⟨p, h1, (hT l p p).mpr (Or.inl rfl)⟩,
        ⟨p, h2, (hT m p p).mpr (Or.inl rfl)⟩⟩
  have hB : ∀ p : Fin N, p ∈ L l → p ∈ L m → (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧
      (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p) := by
    intro p hpl hpm
    constructor
    · intro s hs
      rw [ev_in, hT]
      constructor
      · rintro (h | ⟨h, -⟩ | ⟨-, -, -, h⟩ | ⟨-, h, -⟩)
        · exact h.symm
        · exact absurd hl.1 h
        · rw [h] at hpl
          exact absurd hpl hl.2
        · exact absurd h hl.2
      · intro h
        exact Or.inl h.symm
    · intro s hs
      rw [ev_in, hT]
      constructor
      · rintro (h | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · exact h.symm
        · rw [h] at hpm
          exact absurd hpm hm.2
        · exact absurd h hm.2
        · exact absurd h hm.2
      · intro h
        exact Or.inl h.symm
  refine ⟨hA, hB, ?_⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    have hw' := (hTS l m w).mp hw
    by_cases hn : w < N
    · refine ⟨w, fun Zs h _ => h, Or.inl ⟨⟨w, hn⟩, ?_, ?_, rfl⟩, fun s _ h => h, fun s _ h => h,
        hw'.2.2.1, hw'.2.2.2⟩
      · exact ((hA ⟨w, hn⟩).mp hw).1
      · exact ((hA ⟨w, hn⟩).mp hw).2
    · by_cases hlt : w < N + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < gates.length := by omega
        by_cases hH : Hg l m ⟨k, hk⟩
        · exact ⟨N + k, fun Zs h _ => h, Or.inr ⟨⟨k, hk⟩, rfl, hH⟩, fun s _ h => h, fun s _ h => h,
            hw'.2.2.1, hw'.2.2.2⟩
        · rw [hHg] at hH
          have hop : (gates.get ⟨k, hk⟩).op = GateOp.or := by
            rcases (hg _ (List.get_mem gates ⟨k, hk⟩)).1 with h | h
            · exact absurd ⟨hw, Or.inl h⟩ hH
            · exact h
          have hex : ∃ e ∈ (gates.get ⟨k, hk⟩).inputs, TS l m e := by
            by_contra hne
            exact hH ⟨hw, Or.inr ⟨hop, fun e he hte => hne ⟨e, he, hte⟩⟩⟩
          obtain ⟨e, he, hte⟩ := hex
          obtain ⟨ν, h1, h2, h3, h4, h5, h6⟩ := ih e (hwf ⟨k, hk⟩ e he) hte
          refine ⟨ν, fun Zs h hcl => h1 Zs (hcl ⟨k, hk⟩ h e he) hcl, h2, ?_, ?_, h5, h6⟩
          · intro s hs hv
            exact ev_or ⟨k, hk⟩ _ hop e he (h3 s hs hv)
          · intro s hs hv
            exact ev_or ⟨k, hk⟩ _ hop e he (h4 s hs hv)
      · exfalso
        obtain ⟨p, -, hp⟩ := hw'.2.2.1
        rw [ev_miss w _ (by omega)] at hp
        exact Bool.noConfusion hp

end PEqualNP.Outside.L_meta_1637

theorem PEqualNP.Outside.L_meta_1637 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ TS : Fin N → Fin N → ℕ → Prop,
    (∀ (l m : Fin N) (w : ℕ), TS l m w ↔ (ev w (fun v : Fin N => decide (v ∉ L l)) = false ∧ ev w (fun v : Fin N => decide (v ∉ L m)) = false ∧ (∃ p ∈ L l, ev w (T l p) = true) ∧ ∃ p ∈ L m, ev w (T m p) = true)) →
    ∀ Hg : Fin N → Fin N → Fin gates.length → Prop,
    (∀ (l m : Fin N) (g : Fin gates.length), Hg l m g ↔ (TS l m (N + (g : ℕ)) ∧ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ e ∈ (gates.get g).inputs, ¬ TS l m e)))) →
    ∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      (∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m)) ∧
      (∀ p : Fin N, p ∈ L l → p ∈ L m → (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧ (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p)) ∧
      ∀ w : ℕ, TS l m w → ∃ ν : ℕ, (∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → ν ∈ Zs) ∧
        ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨ ∃ h : Fin gates.length, ν = (N + (h : ℕ)) ∧ Hg l m h) ∧
        (∀ s ∈ L l, ev ν (T l s) = true → ev w (T l s) = true) ∧ (∀ s ∈ L m, ev ν (T m s) = true → ev w (T m s) = true) ∧
        (∃ s ∈ L l, ev ν (T l s) = true) ∧ ∃ s ∈ L m, ev ν (T m s) = true := by
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ T hT gates hg _ hwf ev hev TS hTS Hg hHg l m hl hm
  exact PEqualNP.Outside.L_meta_1637.main N L p0 p1 T hT gates hg hwf ev (fun w x => hev w x)
    TS hTS Hg hHg l m hl hm
