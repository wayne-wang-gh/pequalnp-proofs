import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1610

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_append (A B : List Gate) (x : List Bool) : run (A ++ B) x = run B (run A x) := by
  simp [run, List.foldl_append]

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

lemma gate_value' {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    value ⟨gs, 0⟩ x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then value ⟨gs, 0⟩ x r else false) := by
  have h := gate_value ⟨gs, 0⟩ x (n + k) (by omega) (by change n + k < n + gs.length; omega)
  simpa only [Nat.add_sub_cancel_left] using h

def V {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool := value ⟨gs, 0⟩ x w

lemma V_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    V gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then V gs x r else false) :=
  gate_value' gs x k hk

lemma V_missing {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : V gs x w = false :=
  missing_value ⟨gs, 0⟩ x w hw

lemma V_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    V gs x w = x ⟨w, hw⟩ := by
  change (run gs (List.ofFn x)).getD w false = x ⟨w, hw⟩
  have hp : w < (List.ofFn x).length := by simpa using hw
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma three_distinct (l : List ℕ) (a b c : ℕ) (hl : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l)
    (hc : c ∈ l) : a = b ∨ b = c ∨ a = c := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at ha
  · simp at ha hb hc; omega
  · simp at ha hb hc; omega
  · simp at hl

lemma mono {n : ℕ} (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ w, V gs x w = true → V gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [V_input gs x w hn, V_input gs y w hn]
      exact hxy _
    by_cases hw : n + gs.length ≤ w
    · rw [V_missing gs x w hw]
      intro hh
      exact Bool.noConfusion hh
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < gs.length := by omega
    rw [V_gate gs x k hk, V_gate gs y k hk]
    have hr (r : ℕ) : (if r < n + k then V gs x r else false) = true →
        (if r < n + k then V gs y r else false) = true := by
      by_cases h' : r < n + k
      · simpa [h'] using ih r h'
      · simp [h']
    rcases hops gs[k] (List.getElem_mem hk) with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
      intro hx b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
      intro hx
      obtain ⟨b, hb, hv⟩ := hx
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hv⟩

lemma forest {ι α : Type} [LinearOrder ι] [DecidableEq α] (a b : ι → α) (X : ι → Finset α) :
    ∀ (k : ℕ) (I : Finset ι) (S : Finset α), I.card = k → S.Nonempty →
      (∀ g ∈ I, a g ∈ S ∧ b g ∈ S ∧ a g ∈ X g ∧ b g ∉ X g ∧
        ∀ i ∈ I, i < g → (a i ∈ X g ↔ b i ∈ X g)) → I.card + 1 ≤ S.card := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro I S hk hS h
    by_cases hI : I.Nonempty
    · let g := I.max' hI
      have hg : g ∈ I := Finset.max'_mem I hI
      obtain ⟨hga, hgb, hgaX, hgbX, hgcl⟩ := h g hg
      have hlt : ∀ i ∈ I.erase g, i < g := fun i hi =>
        lt_of_le_of_ne (Finset.le_max' I i (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi)
      have hc' : (I.erase g).card + 1 = I.card := Finset.card_erase_add_one hg
      have hsplitI := Finset.card_filter_add_card_filter_not (s := I.erase g)
        (fun i => a i ∈ X g)
      have hsplitS := Finset.card_filter_add_card_filter_not (s := S)
        (fun v => v ∈ X g)
      have e1 := ih ((I.erase g).filter (fun i => a i ∈ X g)).card (by
          have := Finset.card_filter_le (I.erase g) (fun i => a i ∈ X g); omega)
        ((I.erase g).filter (fun i => a i ∈ X g)) (S.filter (fun v => v ∈ X g)) rfl
        ⟨a g, Finset.mem_filter.mpr ⟨hga, hgaX⟩⟩ (by
          intro i hi
          obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
          have hiI := Finset.mem_of_mem_erase hi1
          obtain ⟨p1, p2, p3, p4, p5⟩ := h i hiI
          refine ⟨Finset.mem_filter.mpr ⟨p1, hi2⟩,
            Finset.mem_filter.mpr ⟨p2, (hgcl i hiI (hlt i hi1)).mp hi2⟩, p3, p4, ?_⟩
          intro j hj hji
          exact p5 j (Finset.mem_of_mem_erase (Finset.mem_filter.mp hj).1) hji)
      have e2 := ih ((I.erase g).filter (fun i => ¬ a i ∈ X g)).card (by
          have := Finset.card_filter_le (I.erase g) (fun i => ¬ a i ∈ X g); omega)
        ((I.erase g).filter (fun i => ¬ a i ∈ X g)) (S.filter (fun v => ¬ v ∈ X g)) rfl
        ⟨b g, Finset.mem_filter.mpr ⟨hgb, hgbX⟩⟩ (by
          intro i hi
          obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
          have hiI := Finset.mem_of_mem_erase hi1
          obtain ⟨p1, p2, p3, p4, p5⟩ := h i hiI
          refine ⟨Finset.mem_filter.mpr ⟨p1, hi2⟩,
            Finset.mem_filter.mpr ⟨p2, fun hb => hi2 ((hgcl i hiI (hlt i hi1)).mpr hb)⟩, p3, p4, ?_⟩
          intro j hj hji
          exact p5 j (Finset.mem_of_mem_erase (Finset.mem_filter.mp hj).1) hji)
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hI
      have := Finset.card_pos.mpr hS
      rw [hI]; simpa using this

lemma or_true {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) (w : ℕ) (hw : w ∈ gs[k].inputs) (hlt : w < n + k)
    (hv : V gs x w = true) : V gs x (n + k) = true := by
  rw [V_gate gs x k hk, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  exact ⟨_, ⟨w, hw, rfl⟩, by simp [hlt, hv]⟩

lemma core (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (hLM : L ∩ M = {m})
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hidx : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ))
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I, ((gates.get g).op = GateOp.or ∧
        V gates (fun v : Fin n => decide (v ∉ L)) (n + (g : ℕ)) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L, ∃ r' ∈ L,
          V gates (t r) w1 = true ∧ V gates (t r') w2 = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g →
            (gates.get i).op = GateOp.or →
            V gates (fun v : Fin n => decide (v ∉ L)) (n + (i : ℕ)) = false →
            ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ L, ∀ y' ∈ L, (V gates (t y) a = true ∨ V gates (t y) b = true) →
              (V gates (t y') a = true ∨ V gates (t y') b = true) → (y ∈ X ↔ y' ∈ X)) ∧
        V gates (fun v : Fin n => decide (v ∉ M)) (n + (g : ℕ)) = false) :
    I.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card := by
  classical
  have hops' : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hops g h).1
  have point : ∀ r ∈ L, ∀ k : ℕ, V gates (t r) (n + k) = true →
      V gates (fun v : Fin n => decide (v ∉ M)) (n + k) = false →
      r ∈ insert m ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)) := by
    intro r hr k h1 h2
    by_contra hcon
    rw [Finset.mem_insert, not_or] at hcon
    obtain ⟨hrm, hrD⟩ := hcon
    have hrM : r ∉ M := by
      intro hM
      have : r ∈ L ∩ M := Finset.mem_inter.mpr ⟨hr, hM⟩
      rw [hLM] at this
      exact hrm (Finset.mem_singleton.mp this)
    have hno : ∀ v ∈ M, ¬ t r v = true := by
      intro v hv htv
      exact hrD (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hr, hrM⟩, v, hv, htv⟩)
    have hm := mono gates hops' (t r) (fun v : Fin n => decide (v ∉ M)) (by
      intro p hp
      have : p ∉ M := fun hpM => hno p hpM hp
      simp [this]) (n + k) h1
    rw [h2] at hm
    exact Bool.noConfusion hm
  have h1 : ∀ g : Fin gates.length, ∃ (a b : Fin n) (X : Finset (Fin n)), g ∈ I →
      (a ∈ L ∧ b ∈ L ∧ a ∈ X ∧ b ∉ X ∧
        (∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ V gates (t a) w1 = true ∧
          V gates (t b) w2 = true) ∧
        ∀ i : Fin gates.length, i < g →
            (gates.get i).op = GateOp.or →
            V gates (fun v : Fin n => decide (v ∉ L)) (n + (i : ℕ)) = false →
            ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ L, ∀ y' ∈ L, (V gates (t y) a = true ∨ V gates (t y) b = true) →
              (V gates (t y') a = true ∨ V gates (t y') b = true) → (y ∈ X ↔ y' ∈ X)) := by
    intro g
    by_cases hg : g ∈ I
    · obtain ⟨⟨_, _, w1, w2, hin, r, hr, r', hr', hv1, hv2, X, hX1, hX2, hcl⟩, _⟩ := hI g hg
      exact ⟨r, r', X, fun _ => ⟨hr, hr', hX1, hX2, ⟨w1, w2, hin, hv1, hv2⟩, hcl⟩⟩
    · exact ⟨m, m, ∅, fun h => absurd h hg⟩
  choose a b X hab using h1
  have hS : ∀ g ∈ I, a g ∈ insert m ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)) ∧
      b g ∈ insert m ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)) := by
    intro g hg
    obtain ⟨ha, hb, _, _, ⟨w1, w2, hin, hv1, hv2⟩, _⟩ := hab g hg
    obtain ⟨⟨hop, _, _⟩, hfM⟩ := hI g hg
    have hin' : gates[g.val].inputs = [w1, w2] := hin
    have hop' : gates[g.val].op = GateOp.or := hop
    have m1 : w1 ∈ gates[g.val].inputs := by rw [hin']; simp
    have m2 : w2 ∈ gates[g.val].inputs := by rw [hin']; simp
    have l1 : w1 < n + g.val := hidx g w1 m1
    have l2 : w2 < n + g.val := hidx g w2 m2
    exact ⟨point (a g) ha g.val (or_true gates _ g.val g.isLt hop' w1 m1 l1 hv1) hfM,
      point (b g) hb g.val (or_true gates _ g.val g.isLt hop' w2 m2 l2 hv2) hfM⟩
  have hf := forest a b X I.card I
    (insert m ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true))) rfl
    ⟨m, Finset.mem_insert_self _ _⟩ (by
      intro g hg
      obtain ⟨ha, hb, hX1, hX2, _, hcl⟩ := hab g hg
      refine ⟨(hS g hg).1, (hS g hg).2, hX1, hX2, ?_⟩
      intro i hi hig
      obtain ⟨hai, hbi, _, _, ⟨w1, w2, hin, hv1, hv2⟩, _⟩ := hab i hi
      obtain ⟨⟨hop, hfL, _⟩, _⟩ := hI i hi
      exact hcl i hig hop hfL w1 w2 hin (a i) hai (b i) hbi (Or.inl hv1) (Or.inr hv2))
  have hc := Finset.card_insert_le m ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true))
  omega

end PEqualNP.Outside.L_meta_1610

theorem PEqualNP.Outside.L_meta_1610 : ∀ (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (t u : Fin n → Fin n → Bool)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (oL oM : ℕ),
    L ∩ M = {m} →
    (∀ r ∈ L, ∀ v ∈ L, t r v = true ↔ v = r) → (∀ r ∈ M, ∀ v ∈ M, u r v = true ↔ v = r) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oL⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false → (∀ r ∈ L, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oL⟩ (List.ofFn (t r)) = true) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oM⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false → (∀ r ∈ M, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oM⟩ (List.ofFn (u r)) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L, ∃ r' ∈ L,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (t r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (t r')) = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false → ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ L, ∀ y' ∈ L, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (t y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (t y)) = true) →
              (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (t y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (t y')) = true) → (y ∈ X ↔ y' ∈ X)) ∧
        ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (u r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (u r')) = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false → ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ M, ∀ y' ∈ M, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (u y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (u y)) = true) →
              (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (u y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (u y')) = true) → (y ∈ X ↔ y' ∈ X))) →
      I.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card ∧
      I.card ≤ ((M \ L).filter (fun r => ∃ v ∈ L, u r v = true)).card := by
  intro n L M m t u gates oL oM hLM _ _ hops hidx _ _ _ _ I hI
  refine ⟨PEqualNP.Outside.L_meta_1610.core n L M m t gates hLM hops hidx I
      (fun g hg => ⟨(hI g hg).1, (hI g hg).2.2.1⟩),
    PEqualNP.Outside.L_meta_1610.core n M L m u gates (by rw [Finset.inter_comm]; exact hLM)
      hops hidx I (fun g hg => ⟨(hI g hg).2, (hI g hg).1.2.1⟩)⟩
