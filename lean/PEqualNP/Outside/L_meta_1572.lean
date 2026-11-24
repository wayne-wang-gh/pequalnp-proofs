import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1572_aux

-- The wire evaluation lemmas follow L-meta-1353.

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

abbrev AO (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma wires_mono {n : ℕ} (C : Circuit) (hAO : AO C) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let p : Fin n := ⟨w, hw⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases h : w < n + C.size
    · let k := w - n
      have hk : k < C.gates.length := by dsimp [k]; unfold Circuit.size at h; omega
      have hwk : w = n + k := by dsimp [k]; omega
      rw [hwk]
      refine gate_mono C k hk (hAO _ (List.getElem_mem hk)).1 x y ?_
      intro r _ hr
      exact ih r (by omega)
    · rw [missing_value C x w (by omega)]
      simp

lemma or_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hor : C.gates[k].op = GateOp.or) :
    value C x (n + k) = true ↔
      ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hv := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hv
  rw [hv, hor]
  simp only [GateOp.eval, List.any_eq_true, id_eq]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨r, hr, hv⟩ := List.mem_map.mp hb
    by_cases hlt : r < n + k
    · exact ⟨r, hr, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨r, hr, hl, hval⟩
    refine ⟨true, List.mem_map.mpr ⟨r, hr, ?_⟩, rfl⟩
    simp [hl, hval]

def OrPath (C : Circuit) (n w target : ℕ) : Prop :=
  ∀ S : Set ℕ, w ∈ S →
    (∀ i : Fin C.gates.length, n + (i : ℕ) ∈ S → (C.gates.get i).op = GateOp.or →
      ∀ a ∈ (C.gates.get i).inputs, a ∈ S) → target ∈ S

lemma find_atom {n : ℕ} (C : Circuit) (hAO : AO C) (x y z : Fin n → Bool)
    (hraw : ∀ p, x p = true → y p = true ∨ z p = true) (w : ℕ)
    (hx : value C x w = true) (hy : value C y w = false) (hz : value C z w = false) :
    ∃ target : ℕ, OrPath C n w target ∧
      (∃ i : Fin C.gates.length, target = n + (i : ℕ) ∧ (C.gates.get i).op = GateOp.and) ∧
      value C x target = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hinput : w < n
    · let p : Fin n := ⟨w, hinput⟩
      change value C x p = true at hx
      change value C y p = false at hy
      change value C z p = false at hz
      rw [input_value] at hx hy hz
      have h := hraw p hx
      rw [hy, hz] at h
      simp at h
    by_cases hvalid : w < n + C.size
    · let k := w-n
      have hk : k < C.gates.length := by dsimp [k]; unfold Circuit.size at hvalid; omega
      have hwk : n+k = w := by dsimp [k]; omega
      have hop := (hAO _ (List.getElem_mem hk)).1
      rcases hop with hand | hor
      · exact ⟨w, fun _ hw _ => hw, ⟨⟨k,hk⟩, hwk.symm, hand⟩, hx⟩
      · obtain ⟨r, hr, hrlt, hrx⟩ := (or_value C x k hk hor).mp (hwk.symm ▸ hx)
        have false_child (u : Fin n → Bool) (hu : value C u w = false) : value C u r = false := by
          cases hv : value C u r with
          | false => rfl
          | true =>
            have ht := (or_value C u k hk hor).mpr ⟨r, hr, hrlt, hv⟩
            rw [hwk, hu] at ht
            exact Bool.noConfusion ht
        obtain ⟨target, hreach, hand, hval⟩ :=
          ih r (hwk ▸ hrlt) hrx (false_child y hy) (false_child z hz)
        refine ⟨target, ?_, hand, hval⟩
        intro S hw hclosed
        apply hreach S _ hclosed
        exact hclosed ⟨k,hk⟩ (hwk.symm ▸ hw) hor r hr
    · rw [missing_value C x w (by omega)] at hx
      exact Bool.noConfusion hx

def rowTest (single base point : Fin 13) (v : Fin 13) : Bool :=
  decide (v = point ∨ (point ≠ single ∧ v = base))

def outside (A : Finset (Fin 13)) (v : Fin 13) : Bool := decide (v ∉ A)

lemma atom_for_row (C : Circuit) (hAO : AO C) (A B : Finset (Fin 13)) (c single base : Fin 13)
    (hinter : A ∩ B = {c}) (hs : single ∉ B) (hb : base ∉ A) (g : ℕ)
    (hA : value C (outside A) g = false) (hB : value C (outside B) g = false)
    (hcount : 2 ≤ (A.filter fun p => value C (rowTest single base p) g = true).card) :
    ∃ Y : ℕ, OrPath C 13 g Y ∧
      (∃ i : Fin C.gates.length, Y = 13 + (i : ℕ) ∧ (C.gates.get i).op = GateOp.and) ∧
      ∃ p ∈ A, p ≠ single ∧ p ≠ c ∧ value C (rowTest single base p) Y = true := by
  classical
  let T := A.filter fun p => value C (rowTest single base p) g = true
  have hex : ∃ p ∈ T, p ≠ c := by
    by_contra! h
    have hsub : T ⊆ {c} := fun p hp => Finset.mem_singleton.mpr (h p hp)
    have hle := Finset.card_le_card hsub
    change 2 ≤ T.card at hcount
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨p, hp, hpc⟩ := hex
  have hpA := (Finset.mem_filter.mp hp).1
  have hpG := (Finset.mem_filter.mp hp).2
  have hps : p ≠ single := by
    intro eq
    subst p
    have hle : ∀ v, rowTest single base single v = true → outside B v = true := by
      intro v hv
      have hv' : v = single := by simpa [rowTest] using hv
      simp [outside, hv', hs]
    have ht := wires_mono C hAO _ _ hle g hpG
    rw [hB] at ht
    exact Bool.noConfusion ht
  have hpB : p ∉ B := by
    intro h
    have hi : p ∈ A ∩ B := Finset.mem_inter.mpr ⟨hpA, h⟩
    rw [hinter, Finset.mem_singleton] at hi
    exact hpc hi
  have hraw : ∀ v, rowTest single base p v = true → outside A v = true ∨ outside B v = true := by
    intro v hv
    simp only [rowTest, decide_eq_true_eq] at hv
    rcases hv with rfl | ⟨_, rfl⟩
    · exact Or.inr (by simp [outside, hpB])
    · exact Or.inl (by simp [outside, hb])
  obtain ⟨Y, hpath, hgate, htrue⟩ := find_atom C hAO _ _ _ hraw g hpG hA hB
  exact ⟨Y, hpath, hgate, p, hpA, hps, hpc, htrue⟩

lemma left_avoids_one : ∀ t ∈ ({4, 10, 12} : Finset (Fin 13)),
    (1 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by decide

lemma right_avoids_zero : ∀ t ∈ ({1, 5, 11} : Finset (Fin 13)),
    (0 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by decide

end PEqualNP.Outside.L_meta_1572_aux

open PEqualNP.Outside.L_meta_1572_aux

theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates g l m c hAO _ hl hm hmeet hfalseL hfalseM
  let C : Circuit := ⟨gates, g⟩
  have hlA : (1 : Fin 13) ∉ L l := by
    rw [hL l]
    exact left_avoids_one l hl
  have hmA : (0 : Fin 13) ∉ L m := by
    rw [hL m]
    exact right_avoids_zero m hm
  have hmeet' : L m ∩ L l = {c} := (Finset.inter_comm _ _).trans hmeet
  constructor
  · exact atom_for_row C hAO (L l) (L m) c 0 1 hmeet hmA hlA g hfalseL hfalseM
  · exact atom_for_row C hAO (L m) (L l) c 1 0 hmeet' hlA hmA g hfalseM hfalseL
