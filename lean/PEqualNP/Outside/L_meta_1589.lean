import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1589_aux
open PEqualNP.CircuitLowerBounds

def Good {P : Type*} [DecidableEq P] (R D : Finset P) (sens pure : P → Prop) (core : Prop) : Prop :=
  (∀ r ∈ R, r ∉ D → sens r → pure r ∧ ¬ core) ∧
  (∀ r ∈ R, r ∉ D → sens r → ∀ s ∈ R, s ∉ D → sens s → r = s)

lemma Good.mono {P : Type*} [DecidableEq P] {R D E : Finset P} {s p : P → Prop} {c : Prop}
    (h : Good R D s p c) (hDE : D ⊆ E) : Good R E s p c :=
  ⟨fun r hr hd hs => h.1 r hr (fun h => hd (hDE h)) hs,
   fun r hr hd hs t ht he hs' => h.2 r hr (fun h => hd (hDE h)) hs t ht (fun h => he (hDE h)) hs'⟩

abbrev V {N : ℕ} (gs : List Gate) (w : ℕ) (x : Fin N → Bool) : Bool := Circuit.eval ⟨gs,w⟩ (List.ofFn x)
abbrev base {N : ℕ} (M : Finset (Fin N)) : Fin N → Bool := fun v => decide (v ∉ M)
abbrev single {N : ℕ} (r : Fin N) : Fin N → Bool := fun v => decide (v = r)
abbrev rimInput {N : ℕ} (M : Finset (Fin N)) (r : Fin N) : Fin N → Bool := fun v => decide (v ∉ M ∨ v = r)
abbrev S {N : ℕ} (gs : List Gate) (M : Finset (Fin N)) (w : ℕ) (r : Fin N) : Prop := V gs w (rimInput M r) = true
abbrev U {N : ℕ} (gs : List Gate) (w : ℕ) (r : Fin N) : Prop := V gs w (single r) = true
abbrev C {N : ℕ} (gs : List Gate) (T : Finset (Fin N)) (w : ℕ) : Prop := ∃ x ∈ T, U gs w x

namespace CoWire

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

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

end CoWire

lemma twoPoints {N : ℕ} (L : Fin N → Finset (Fin N)) {i t r s : Fin N}
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (ht : t ≠ i) (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s) :
    r ∉ L t ∨ s ∉ L t := by
  by_contra! h
  have hsub : ({r,s} : Finset (Fin N)) ⊆ L i ∩ L t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hr, h.1⟩
    · exact Finset.mem_inter.mpr ⟨hs, h.2⟩
  have hle := Finset.card_le_card hsub
  simp [hrs, hinter i t ht.symm] at hle

lemma offOther {N : ℕ} (gates : List Gate) (w : ℕ) (L : Fin N → Finset (Fin N))
    {i r s : Fin N} (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s)
    (h1 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = r)) = true)
    (h2 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = s)) = true)
    (t : Fin N) (ht : t ≠ i) :
    Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
  have lift (p : Fin N) (hp : p ∉ L t)
      (hv : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = p)) = true) :
      Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
    apply CoWire.mono ⟨gates,w⟩ hC (fun v : Fin N => decide (v = p)) (fun v => decide (v ∉ L t)) _ w hv
    intro v h
    simp only [decide_eq_true_eq] at h ⊢
    simpa only [h] using hp
  rcases twoPoints L hinter ht hr hs hrs with h | h
  · exact lift r h h1
  · exact lift s h h2

theorem orUpdate {P : Type*} [DecidableEq P] (R D : Finset P) (s₁ s₂ p₁ p₂ : P → Prop)
    (c₁ c₂ Q : Prop) [Decidable Q] (g₁ : Good R D s₁ p₁ c₁) (g₂ : Good R D s₂ p₂ c₂)
    (charge : ((∃ r ∈ R, r ∉ D ∧ s₁ r ∧ c₂) ∨ (∃ r ∈ R, r ∉ D ∧ s₂ r ∧ c₁) ∨
        (∃ r ∈ R, ∃ t ∈ R, r ∉ D ∧ t ∉ D ∧ s₁ r ∧ s₂ t ∧ r ≠ t)) → Q) :
    ∃ E : Finset P, D ⊆ E ∧ E.card ≤ D.card + (if Q then 1 else 0) ∧
      Good R E (fun r => s₁ r ∨ s₂ r) (fun r => p₁ r ∨ p₂ r) (c₁ ∨ c₂) := by
  classical
  let Bad := (∃ r ∈ R, r ∉ D ∧ s₁ r ∧ c₂) ∨ (∃ r ∈ R, r ∉ D ∧ s₂ r ∧ c₁) ∨
             (∃ r ∈ R, ∃ t ∈ R, r ∉ D ∧ t ∉ D ∧ s₁ r ∧ s₂ t ∧ r ≠ t)
  have drop {s p : P → Prop} {c : Prop} (g : Good R D s p c) {a : P}
      (ha : a ∈ R) (hd : a ∉ D) (hs : s a) :
      ∀ z ∈ R, z ∉ insert a D → ¬ s z := by
    intro z hz he hsz
    have eq := g.2 z hz (fun h => he (Finset.mem_insert_of_mem h)) hsz a ha hd hs
    exact he (Finset.mem_insert.mpr (Or.inl eq))
  have vac (E : Finset P) (h : ∀ z ∈ R, z ∉ E → ¬ (s₁ z ∨ s₂ z)) :
      Good R E (fun z => s₁ z ∨ s₂ z) (fun z => p₁ z ∨ p₂ z) (c₁ ∨ c₂) := by
    exact ⟨fun r hr he hs => (h r hr he hs).elim, fun r hr he hs => (h r hr he hs).elim⟩
  by_cases bad : Bad
  · have q : Q := charge bad
    have budget (a : P) : (insert a D).card ≤ D.card + (if Q then 1 else 0) := by
      rw [ite_eq_left q]
      exact Finset.card_insert_le a D
    rcases bad with ⟨a,ha,hd,hs,hc⟩ | ⟨a,ha,hd,hs,hc⟩ | ⟨a,ha,b,hb,hd,_,hs,_,_⟩
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, vac _ ?_⟩
      intro z hz he h
      rcases h with l | r
      · exact drop g₁ ha hd hs z hz he l
      · exact (g₂.1 z hz (fun h => he (Finset.mem_insert_of_mem h)) r).2 hc
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, vac _ ?_⟩
      intro z hz he h
      rcases h with l | r
      · exact (g₁.1 z hz (fun h => he (Finset.mem_insert_of_mem h)) l).2 hc
      · exact drop g₂ ha hd hs z hz he r
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, ?_⟩
      have right : ∀ z ∈ R, z ∉ insert a D → s₁ z ∨ s₂ z → s₂ z :=
        fun z hz he h => h.resolve_left (drop g₁ ha hd hs z hz he)
      have g₂' := g₂.mono (Finset.subset_insert a D)
      constructor
      · intro z hz he h
        have v := g₂'.1 z hz he (right z hz he h)
        exact ⟨Or.inr v.1, fun hC => hC.elim (g₁.1 a ha hd hs).2 v.2⟩
      · intro z hz he h t ht hte hts
        exact g₂'.2 z hz he (right z hz he h) t ht hte (right t ht hte hts)
  · refine ⟨D, Finset.Subset.rfl, Nat.le_add_right _ _, ?_⟩
    have cross {a b : P} (ha : a ∈ R) (hb : b ∈ R) (da : a ∉ D) (db : b ∉ D)
        (sa : s₁ a) (sb : s₂ b) : a = b := by
      by_contra hn
      exact bad (Or.inr (Or.inr ⟨a,ha,b,hb,da,db,sa,sb,hn⟩))
    constructor
    · intro r hr hd hs
      rcases hs with l | r'
      · have v := g₁.1 r hr hd l
        exact ⟨Or.inl v.1, fun c => c.elim v.2 (fun rc => bad (Or.inl ⟨r,hr,hd,l,rc⟩))⟩
      · have v := g₂.1 r hr hd r'
        exact ⟨Or.inr v.1, fun c => c.elim (fun lc => bad (Or.inr (Or.inl ⟨r,hr,hd,r',lc⟩))) v.2⟩
    · intro a ha da hsa b hb db hsb
      rcases hsa with l | r <;> rcases hsb with l' | r'
      · exact g₁.2 a ha da l b hb db l'
      · exact cross ha hb da db l r'
      · exact (cross hb ha db da l' r).symm
      · exact g₂.2 a ha da r b hb db r'

theorem strand_of_rim_only_input {N : ℕ} {L : Fin N → Finset (Fin N)}
    {i0 : Fin N} {T0 : Finset (Fin N)} {gates : List Gate} {Xs : Finset (Fin gates.length)}
    (hXs : ∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ¬ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ T0, ∃ r' ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin N => decide (v = r))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin N => decide (v = r'))) = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (i : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ T0, ∀ y' ∈ T0,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true) → (y ∈ X ↔ y' ∈ X))) ∧ ∀ t : Fin N, t ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = true) → g ∈ Xs)
    {g : Fin gates.length} {a b : ℕ}
    (hop : (gates.get g).op = GateOp.or)
    (hcold : Circuit.eval ⟨gates, N + (g : ℕ)⟩
      (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false)
    (hinputs : (gates.get g).inputs = [a,b] ∨ (gates.get g).inputs = [b,a])
    (hempty : ¬ ∃ x ∈ T0, Circuit.eval ⟨gates, a⟩
      (List.ofFn (fun v : Fin N => decide (v = x))) = true)
    (hother : ∀ t : Fin N, t ≠ i0 → Circuit.eval ⟨gates, N + (g : ℕ)⟩
      (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = true) : g ∈ Xs := by
  apply hXs g
  refine ⟨hop, hcold, ?_, hother⟩
  rintro ⟨_, _, w₁, w₂, hw, x, hx, y, hy, hx₁, hy₂, _⟩
  rcases hinputs with hab | hba
  · rw [hab] at hw
    simp only [List.cons.injEq, and_true] at hw
    exact hempty ⟨x, hx, hw.1 ▸ hx₁⟩
  · rw [hba] at hw
    simp only [List.cons.injEq, and_true] at hw
    exact hempty ⟨y, hy, hw.2 ▸ hy₂⟩

theorem realOrUpdate {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 : Fin N}
    {T : Finset (Fin N)} {gs : List Gate} {Xs : Finset (Fin gs.length)} {D : Finset (Fin N)}
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1) (hTsub : T ⊆ L i0)
    (hXs : ∀ g : Fin gs.length, ((gs.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ¬ ((gs.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧
        ∃ w1 w2 : ℕ, (gs.get g).inputs = [w1, w2] ∧ ∃ r ∈ T, ∃ r' ∈ T, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, w1⟩ (List.ofFn (fun v : Fin N => decide (v = r))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, w2⟩ (List.ofFn (fun v : Fin N => decide (v = r'))) = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gs.length, i < g → (gs.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, N + (i : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
          ∀ a b : ℕ, (gs.get i).inputs = [a, b] → ∀ y ∈ T, ∀ y' ∈ T,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, a⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, b⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, a⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, b⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true) → (y ∈ X ↔ y' ∈ X))) ∧ ∀ t : Fin N, t ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = true) → g ∈ Xs)
    (i : Fin gs.length) (a b : ℕ) (hop : (gs.get i).op = GateOp.or)
    (hinputs : (gs.get i).inputs = [a,b]) (hcold : V gs (N + i.val) (base (L i0)) = false)
    (hor : ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x || V gs b x))
    (ga : Good (L i0 \ T) D (S gs (L i0) a) (U gs a) (C gs T a))
    (gb : Good (L i0 \ T) D (S gs (L i0) b) (U gs b) (C gs T b)) :
    ∃ E : Finset (Fin N), D ⊆ E ∧ E.card ≤ D.card + (if i ∈ Xs then 1 else 0) ∧
      Good (L i0 \ T) E (S gs (L i0) (N + i.val)) (U gs (N + i.val)) (C gs T (N + i.val)) := by
  classical
  have us (r : Fin N) : U gs (N + i.val) r ↔ U gs a r ∨ U gs b r := by
    change V gs (N + i.val) (single r) = true ↔ _
    rw [hor]
    simp only [Bool.or_eq_true, U]
  have ss (r : Fin N) : S gs (L i0) (N + i.val) r ↔ S gs (L i0) a r ∨ S gs (L i0) b r := by
    change V gs (N + i.val) (rimInput (L i0) r) = true ↔ _
    rw [hor]
    simp only [Bool.or_eq_true, S]
  have cs : C gs T (N + i.val) ↔ C gs T a ∨ C gs T b := by
    constructor
    · rintro ⟨x,hx,ux⟩
      rcases (us x).1 ux with ua | ub
      · exact Or.inl ⟨x,hx,ua⟩
      · exact Or.inr ⟨x,hx,ub⟩
    · rintro (⟨x,hx,ua⟩ | ⟨x,hx,ub⟩)
      · exact ⟨x,hx,(us x).2 (Or.inl ua)⟩
      · exact ⟨x,hx,(us x).2 (Or.inr ub)⟩
  have pay {r t : Fin N} (hr : r ∈ L i0) (ht : t ∈ L i0) (hrt : r ≠ t)
      (u₁ : U gs a r) (u₂ : U gs b t) (empty : ¬ C gs T a ∨ ¬ C gs T b) : i ∈ Xs := by
    have every := offOther gs (N + i.val) L hG hinter hr ht hrt
      ((us r).2 (Or.inl u₁)) ((us t).2 (Or.inr u₂))
    rcases empty with ha | hb
    · exact strand_of_rim_only_input hXs hop hcold (Or.inl hinputs) ha every
    · exact strand_of_rim_only_input hXs hop hcold (Or.inr hinputs) hb every
  obtain ⟨E,hDE,hcard,hGood⟩ := orUpdate (L i0 \ T) D _ _ _ _ _ _ (i ∈ Xs) ga gb (by
    rintro (⟨r,hr,hd,sa,t,ht,ub⟩ | ⟨t,ht,hd,sb,r,hr,ua⟩ | ⟨r,hr,t,ht,dr,dt,sa,sb,hrt⟩)
    · obtain ⟨ua,ha⟩ := ga.1 r hr hd sa
      have h := Finset.mem_sdiff.mp hr
      exact pay h.1 (hTsub ht) (fun e => h.2 (e ▸ ht)) ua ub (Or.inl ha)
    · obtain ⟨ub,hb⟩ := gb.1 t ht hd sb
      have h := Finset.mem_sdiff.mp ht
      exact pay (hTsub hr) h.1 (fun e => h.2 (e ▸ hr)) ua ub (Or.inr hb)
    · obtain ⟨ua,ha⟩ := ga.1 r hr dr sa
      obtain ⟨ub,_⟩ := gb.1 t ht dt sb
      exact pay (Finset.mem_sdiff.mp hr).1 (Finset.mem_sdiff.mp ht).1 hrt ua ub (Or.inl ha))
  refine ⟨E,hDE,hcard,?_,?_⟩
  · intro r hr hd sr
    obtain ⟨u,c⟩ := hGood.1 r hr hd ((ss r).1 sr)
    exact ⟨(us r).2 u, fun h => c (cs.1 h)⟩
  · intro r hr hd sr t ht hdt st
    exact hGood.2 r hr hd ((ss r).1 sr) t ht hdt ((ss t).1 st)

lemma andUpdate {P : Type*} [DecidableEq P] (R D : Finset P)
    (sChild pChild sGate pGate : P → Prop) (cChild cGate Q : Prop) [Decidable Q]
    (h : Good R D sChild pChild cChild) (sub : ∀ r, sGate r → sChild r)
    (qual : (∃ r ∈ R, sGate r) → Q) :
    ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if Q then 1 else 0) ∧ Good R E sGate pGate cGate := by
  suffices step : ∃ E : Finset P, D ⊆ E ∧ E.card ≤ D.card + (if Q then 1 else 0) ∧
      ∀ r ∈ R, r ∉ E → ¬ sGate r by
    obtain ⟨E, hDE, hcard, no⟩ := step
    exact ⟨E, hDE, hcard, fun r hr he hs => (no r hr he hs).elim,
      fun r hr he hs => (no r hr he hs).elim⟩
  by_cases unpaid : ∃ r ∈ R, r ∉ D ∧ sGate r
  · obtain ⟨r, hr, hd, hs⟩ := unpaid
    have hQ := qual ⟨r, hr, hs⟩
    refine ⟨insert r D, Finset.subset_insert _ _, ?_, ?_⟩
    · simp [hd, hQ]
    · intro t ht he hts
      have htd : t ∉ D := fun hmem => he (Finset.mem_insert_of_mem hmem)
      have heq := h.2 t ht htd (sub t hts) r hr hd (sub r hs)
      exact he (Finset.mem_insert.mpr (Or.inl heq))
  · refine ⟨D, Finset.Subset.rfl, Nat.le_add_right _ _, ?_⟩
    exact fun r hr hd hs => unpaid ⟨r, hr, hd, hs⟩

theorem prefixBudget {P : Type*} [DecidableEq P] (N k : ℕ)
    (A Xs : Finset (Fin k)) (G : ℕ → Finset P → Prop)
    (mono : ∀ w D E, D ⊆ E → G w D → G w E)
    (init : ∀ w < N, G w ∅)
    (step : ∀ (i : Fin k) (D : Finset P), (∀ w < N + i.val, G w D) →
      ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if i ∈ A then 1 else 0) +
        (if i ∈ Xs then 1 else 0) ∧ G (N + i.val) E) :
    ∃ D, D.card ≤ A.card + Xs.card ∧ ∀ w < N + k, G w D := by
  let count (S : Finset (Fin k)) (j : ℕ) := (S.filter fun v => v.val < j).card
  have next (S : Finset (Fin k)) (i : Fin k) :
      count S (i.val + 1) = count S i.val + (if i ∈ S then 1 else 0) := by
    have hlt (v : Fin k) : v.val < i.val + 1 ↔ v = i ∨ v.val < i.val := by
      rw [Fin.ext_iff]
      omega
    by_cases hi : i ∈ S
    · have heq : S.filter (fun v => v.val < i.val + 1) =
          insert i (S.filter fun v => v.val < i.val) := by
        ext v
        by_cases hv : v = i
        · subst v
          simp [hi]
        · simp [hlt, hv]
      have hnot : i ∉ S.filter (fun v => v.val < i.val) := by simp
      simp only [count, heq, Finset.card_insert_of_notMem hnot, ite_eq_left hi]
    · have heq : S.filter (fun v => v.val < i.val + 1) =
          S.filter (fun v => v.val < i.val) := by
        ext v
        by_cases hv : v = i
        · subst v
          simp [hi]
        · simp [hlt, hv]
      simp only [count, heq, ite_eq_right hi, Nat.add_zero]
  have prefixBound (j : ℕ) (hj : j ≤ k) :
      ∃ D, D.card ≤ count A j + count Xs j ∧ ∀ w < N + j, G w D := by
    induction j with
    | zero =>
      exact ⟨∅, by simp [count], by simpa using init⟩
    | succ j ih =>
      let i : Fin k := ⟨j, by omega⟩
      obtain ⟨D, hD, hG⟩ := ih (by omega)
      obtain ⟨E, hDE, hE, hGE⟩ := step i D hG
      refine ⟨E, ?_, ?_⟩
      · change E.card ≤ count A (i.val + 1) + count Xs (i.val + 1)
        rw [next A i, next Xs i]
        change D.card ≤ count A i.val + count Xs i.val at hD
        omega
      · intro w hw
        by_cases hprev : w < N + j
        · exact mono w D E hDE (hG w hprev)
        · have hw' : w = N + i.val := by change w = N + j; omega
          exact hw' ▸ hGE
  have last (S : Finset (Fin k)) : count S k = S.card := by
    have heq : S.filter (fun v => v.val < k) = S := by
      ext v
      simp
    simp only [count, heq]
  simpa only [last] using prefixBound k (le_refl k)

lemma primaryGood {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (w : ℕ) (hw : w < N)
    (hc : V gs w (base M) = false) : Good (M \ T) ∅ (S gs M w) (U gs w) (C gs T w) := by
  let p : Fin N := ⟨w, hw⟩
  have eval (x : Fin N → Bool) : V gs w x = x p := CoWire.input_value ⟨gs,w⟩ x p
  rw [eval] at hc
  have hp : p ∈ M := by simpa [base] using hc
  have sens (r : Fin N) : S gs M w r ↔ p = r := by
    change V gs w (rimInput M r) = true ↔ _
    rw [eval]
    simp [rimInput, hp]
  have purePt (r : Fin N) : U gs w r ↔ p = r := by
    change V gs w (single r) = true ↔ _
    rw [eval]
    simp [single]
  constructor
  · intro r hr _ hs
    refine ⟨(purePt r).mpr ((sens r).mp hs), ?_⟩
    rintro ⟨x, hx, hux⟩
    have heq : r = x := ((sens r).mp hs).symm.trans ((purePt x).mp hux)
    exact (Finset.mem_sdiff.mp hr).2 (heq ▸ hx)
  · intro r _ _ hr s _ _ hs
    exact ((sens r).mp hr).symm.trans ((sens s).mp hs)

lemma missingV {N : ℕ} (gs : List Gate) (w : ℕ) (hw : N + gs.length ≤ w)
    (x : Fin N → Bool) : V gs w x = false :=
  CoWire.missing_value ⟨gs,w⟩ x w hw

lemma gateCases {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length) :
    (∃ a < N + i.val, ∀ x : Fin N → Bool, V gs (N + i.val) x = V gs a x) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.and ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x && V gs b x)) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.or ∧
      (gs.get i).inputs = [a, b] ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x || V gs b x)) := by
  obtain ⟨hop, hlen⟩ := hG (gs.get i) (List.get_mem gs i)
  obtain ⟨hnon, earlier⟩ := htop i
  have val (x : Fin N → Bool) :
      V gs (N + i.val) x = (gs.get i).op.eval
        ((gs.get i).inputs.map fun r => if r < N + i.val then V gs r x else false) := by
    let D : Circuit := ⟨gs,0⟩
    have hw : N + i.val < N + D.size := Nat.add_lt_add_left i.isLt N
    have h := CoWire.gate_value D x (N + i.val) (by omega) hw
    simpa [D, CoWire.value, V, Circuit.eval, Circuit.wires] using h
  generalize eqg : gs.get i = g at hop hlen hnon earlier val ⊢
  cases ins : g.inputs with
  | nil => simp [ins] at hnon
  | cons a rest =>
    have ha : a < N + i.val := earlier a (by simp [ins])
    cases rest with
    | nil =>
      refine Or.inl ⟨a, ha, ?_⟩
      intro x
      rcases hop with hop | hop <;> simpa [ins, hop, GateOp.eval, ha] using val x
    | cons b rest =>
      cases rest with
      | nil =>
        have hb : b < N + i.val := earlier b (by simp [ins])
        rcases hop with hop | hop
        · refine Or.inr (Or.inl ⟨a, ha, b, hb, hop, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
        · refine Or.inr (Or.inr ⟨a, ha, b, hb, hop, rfl, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
      | cons c rest => simp [ins] at hlen

end PEqualNP.Outside.L_meta_1589_aux

set_option maxHeartbeats 1200000 in
open PEqualNP.Outside.L_meta_1589_aux in
theorem PEqualNP.Outside.L_meta_1589 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ x ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v = x))) = true) → (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) →
    ∀ A Xs : Finset (Fin gates.length), (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) → a ∈ A) →
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ¬ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ T0, ∃ r' ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin N => decide (v = r))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin N => decide (v = r'))) = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (i : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ T0, ∀ y' ∈ T0,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true) → (y ∈ X ↔ y' ∈ X))) ∧ ∀ t : Fin N, t ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = true) → g ∈ Xs) →
      q + 1 - m ≤ A.card + Xs.card := by
  classical
  intro q m N L i0 T _hq hm _hN hsize hinter _hpair hTsub hTm gs o hG htop hbase hsingle hrim A Xs hA hXs
  let M := L i0
  let R := M \ T
  let Inv (w : ℕ) (D : Finset (Fin N)) :=
    V gs w (base M) = false → Good R D (S gs M w) (U gs w) (C gs T w)
  have grow : ∀ w D E, D ⊆ E → Inv w D → Inv w E := by
    intro w D E hDE hw hc
    exact (hw hc).mono hDE
  have init : ∀ w < N, Inv w ∅ := by
    intro w hw hc
    exact primaryGood gs M T w hw hc
  have step (i : Fin gs.length) (D : Finset (Fin N))
      (prev : ∀ w < N + i.val, Inv w D) :
      ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if i ∈ A then 1 else 0) + (if i ∈ Xs then 1 else 0) ∧ Inv (N + i.val) E := by
    by_cases hc : V gs (N+i.val) (base M) = false
    · rcases gateCases gs hG htop i with
        ⟨a, hlt, heq⟩ | ⟨a, ha, b, hb, hop, heq⟩ | ⟨a, ha, b, hb, hop, hin, heq⟩
      · refine ⟨D, fun _ h => h, by omega, ?_⟩
        intro _
        have ca : V gs a (base M) = false := (heq _).symm.trans hc
        have hs : S gs M (N+i.val) = S gs M a := funext fun r =>
          congrArg (fun b : Bool => b = true) (heq (rimInput M r))
        have hu : U gs (N+i.val) = U gs a := funext fun r =>
          congrArg (fun b : Bool => b = true) (heq (single r))
        have hcore : C gs T (N+i.val) = C gs T a := congrArg (fun f : Fin N → Prop => ∃ x ∈ T, f x) hu
        rw [hs, hu, hcore]
        exact prev a hlt ca
      · have forced : ∀ r, S gs M (N+i.val) r → S gs M a r ∧ S gs M b r := by
          intro r hr
          exact Bool.and_eq_true_iff.mp ((heq _).symm.trans hr)
        have coldChoice : ∃ w, w < N+i.val ∧ V gs w (base M) = false ∧
            ∀ r, S gs M (N+i.val) r → S gs M w r := by
          by_cases ca : V gs a (base M) = false
          · exact ⟨a, ha, ca, fun r h => (forced r h).1⟩
          · have cb : V gs b (base M) = false := by
              have h := (heq (base M)).symm.trans hc
              cases h₁ : V gs a (base M) with
              | false => exact (ca h₁).elim
              | true => simpa only [h₁, Bool.true_and] using h
            exact ⟨b, hb, cb, fun r h => (forced r h).2⟩
        obtain ⟨w, hw, cw, sub⟩ := coldChoice
        have qual : (∃ r ∈ R, S gs M (N+i.val) r) → i ∈ A := fun h => hA i ⟨hop, hc, h⟩
        obtain ⟨E, hDE, hcard, hg⟩ := andUpdate R D (S gs M w) (U gs w)
          (S gs M (N+i.val)) (U gs (N+i.val)) (C gs T w) (C gs T (N+i.val))
          (i ∈ A) (prev w hw cw) sub qual
        exact ⟨E, hDE, by omega, fun _ => hg⟩
      · have ab : V gs a (base M) = false ∧ V gs b (base M) = false := by
          simpa only [Bool.or_eq_false_iff] using (heq (base M)).symm.trans hc
        obtain ⟨E, hDE, hcard, hg⟩ := realOrUpdate hG hinter hTsub hXs i a b hop hin hc heq
          (prev a ha ab.1) (prev b hb ab.2)
        exact ⟨E, hDE, by omega, fun _ => hg⟩
    · exact ⟨D, fun _ h => h, by omega, fun h => (hc h).elim⟩
  obtain ⟨D, hd, hgood⟩ := prefixBudget N gs.length A Xs Inv grow init step
  have tne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := tne
  have bounded : o < N + gs.length := by
    by_contra! he
    have h := missingV gs o he (single x)
    have p : V gs o (single x) = true := hsingle x hx
    simp [h] at p
  have core : C gs T o := ⟨x, hx, hsingle x hx⟩
  have covered : R ⊆ D := by
    intro r hr
    by_contra hd'
    exact ((hgood o bounded hbase).1 r hr hd' (hrim r hr)).2 core
  have count := (Finset.card_le_card covered).trans hd
  simpa only [R, M, Finset.card_sdiff_of_subset hTsub, hsize, hTm] using count

