import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1579

open PEqualNP.CircuitLowerBounds

def stepW (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def run (gs : List Gate) (W : List Bool) : List Bool := gs.foldl stepW W

theorem run_append (gs gs' : List Gate) (W : List Bool) :
    run (gs ++ gs') W = run gs' (run gs W) := by
  simp [run, List.foldl_append]

theorem run_prefix (gs : List Gate) : ∀ W : List Bool,
    ∃ t : List Bool, run gs W = W ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro W; exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    intro W
    obtain ⟨t, ht, hl⟩ := ih (stepW W g)
    refine ⟨g.op.eval (g.inputs.map fun i => W.getD i false) :: t, ?_, by simp [hl]⟩
    have e : run (g :: gs) W = run gs (stepW W g) := rfl
    rw [e, ht]; simp [stepW]

theorem run_length (gs : List Gate) (W : List Bool) :
    (run gs W).length = W.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs W
  rw [ht]; simp [hl]

theorem run_getD_lt (gs : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (run gs W).getD i false = W.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs W
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem run_getD_ge (gs : List Gate) (W : List Bool) (i : ℕ) (h : W.length + gs.length ≤ i) :
    (run gs W).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [run_length]; exact h

theorem run_snoc (gs : List Gate) (g : Gate) (W : List Bool) :
    run (gs ++ [g]) W = stepW (run gs W) g := by
  rw [run_append]; rfl

def gateAt (gates : List Gate) (i : ℕ) : Gate := gates.getD i ⟨GateOp.and, []⟩

theorem old_gate (gates : List Gate) (x' : List Bool) (i : ℕ) (hi : i < gates.length) :
    (run gates x').getD (x'.length + i) false =
      (gateAt gates i).op.eval ((gateAt gates i).inputs.map fun q => (run (gates.take i) x').getD q false) := by
  have e1 : gates = gates.take (i + 1) ++ gates.drop (i + 1) := (List.take_append_drop _ _).symm
  have e2 : gates.take (i + 1) = gates.take i ++ [gateAt gates i] := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hi, List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  have hlen : (run (gates.take i) x').length = x'.length + i := by
    rw [run_length, List.length_take]; congr 1; omega
  conv => lhs; rw [e1, run_append]
  rw [run_getD_lt _ _ _ (by rw [run_length, List.length_take]; omega), e2, run_snoc]
  unfold stepW
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  simp

theorem old_take (gates : List Gate) (x' : List Bool) (i q : ℕ) (hi : i ≤ gates.length) :
    (run (gates.take i) x').getD q false = if q < x'.length + i then (run gates x').getD q false else false := by
  have hlen : (run (gates.take i) x').length = x'.length + i := by
    rw [run_length, List.length_take]; congr 1; omega
  split_ifs with hq
  · rw [show run gates x' = run (gates.drop i) (run (gates.take i) x') by
      rw [← run_append, List.take_append_drop]]
    rw [run_getD_lt (gates.drop i) _ q (by omega)]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem gateAt_get (gates : List Gate) (i : Fin gates.length) : gateAt gates i.val = gates.get i := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ i.isLt]; rfl

abbrev E (gates : List Gate) (w : ℕ) (f : Fin 13 → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn f)

theorem E_eq (gates : List Gate) (w : ℕ) (f : Fin 13 → Bool) :
    E gates w f = (run gates (List.ofFn f)).getD w false := rfl

theorem E_gate (gates : List Gate) (hlt : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (i : Fin gates.length) (f : Fin 13 → Bool) :
    E gates (13 + (i : ℕ)) f = (gates.get i).op.eval ((gates.get i).inputs.map fun a => E gates a f) := by
  have h := old_gate gates (List.ofFn f) i.val i.isLt
  rw [List.length_ofFn, gateAt_get] at h
  rw [E_eq, h]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [old_take _ _ _ _ (le_of_lt i.isLt), List.length_ofFn]
  simp only [hlt i a ha, ↓reduceIte]
  rfl

theorem E_input (gates : List Gate) (w : ℕ) (hw : w < 13) (f : Fin 13 → Bool) :
    E gates w f = f ⟨w, hw⟩ := by
  rw [E_eq, run_getD_lt _ _ _ (by simpa using hw), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hw]

theorem E_big (gates : List Gate) (w : ℕ) (hw : 13 + gates.length ≤ w) (f : Fin 13 → Bool) :
    E gates w f = false := by
  rw [E_eq, run_getD_ge _ _ _ (by simpa using hw)]

def Reach (gates : List Gate) (u Y : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S

theorem descend (gates : List Gate)
    (hop : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlt : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (u B : ℕ) (x xl xm : Fin 13 → Bool) : ∀ w : ℕ, Reach gates u w → w < B →
    E gates w x = true → E gates w xl = false → E gates w xm = false →
    (∃ w' : Fin 13, x w' = true ∧ xl w' = false ∧ xm w' = false) ∨
    ∃ Y : ℕ, Reach gates u Y ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧ Y < B ∧
      E gates Y xl = false ∧ E gates Y xm = false ∧ E gates Y x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hR hB hx hl hm
    by_cases h13 : w < 13
    · left
      refine ⟨⟨w, h13⟩, ?_, ?_, ?_⟩
      · rw [E_input gates w h13 x] at hx; exact hx
      · rw [E_input gates w h13 xl] at hl; exact hl
      · rw [E_input gates w h13 xm] at hm; exact hm
    · by_cases hbig : 13 + gates.length ≤ w
      · rw [E_big gates w hbig] at hx; exact absurd hx (by simp)
      · let i : Fin gates.length := ⟨w - 13, by omega⟩
        have hw : w = 13 + (i : ℕ) := by simp [i]; omega
        rcases (hop (gates.get i) (List.get_mem _ _)).1 with ha | ho
        · right
          exact ⟨w, hR, ⟨i, hw, ha⟩, hB, hl, hm, hx⟩
        · rw [hw, E_gate gates hlt i, ho] at hx hl hm
          simp only [GateOp.eval, List.any_eq_true, List.any_eq_false, List.mem_map, id] at hx hl hm
          obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hx
          have hal : a < w := by have := hlt i a ha; omega
          have hR' : Reach gates u a := by
            intro S hu hS
            exact hS i (hw ▸ hR S hu hS) ho a ha
          have hla : E gates a xl = false := by
            cases h : E gates a xl
            · rfl
            · exact absurd (hl _ ⟨a, ha, h⟩) (by simp)
          have hma : E gates a xm = false := by
            cases h : E gates a xm
            · rfl
            · exact absurd (hm _ ⟨a, ha, h⟩) (by simp)
          exact ih a hal hR' (by omega) hb hla hma

theorem one_notin : ∀ l : Fin 13, l ∈ ({4, 10, 12} : Finset (Fin 13)) →
    (1 : Fin 13) ∉ ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)) := by decide

theorem zero_notin : ∀ m : Fin 13, m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (0 : Fin 13) ∉ ({m, m + 1, m + 3, m + 9} : Finset (Fin 13)) := by decide

theorem main : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (∀ p ∈ L l, p ≠ 0 → p ≠ c → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Y < 13 + (zs : ℕ) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (∀ p ∈ L m, p ≠ 1 → p ≠ c → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Y < 13 + (zs : ℕ) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates zs u v l m c hop hlt hl hm hc hz hin hul hum
  have h1l : (1 : Fin 13) ∉ L l := by rw [hL]; exact one_notin l hl
  have h0m : (0 : Fin 13) ∉ L m := by rw [hL]; exact zero_notin m hm
  have hu_lt : u < 13 + (zs : ℕ) := hlt zs u (by rw [hin]; simp)
  have hR : Reach gates u u := fun S hu _ => hu
  have key : ∀ x : Fin 13 → Bool, E gates (13 + (zs : ℕ)) x = true → E gates u x = true := by
    intro x h
    rw [E_gate gates hlt zs, hz, hin] at h
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
      Bool.and_true, Bool.and_eq_true] at h
    exact h.1
  constructor
  · intro p hp hp0 hpc hzx
    rcases descend gates hop hlt u (13 + (zs : ℕ)) _ _ _ u hR hu_lt (key _ hzx) hul hum with
      ⟨w', hx, hxl, hxm⟩ | hY
    · exfalso
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_not] at hx hxl hxm
      have hmem : w' ∈ L l ∩ L m := Finset.mem_inter.2 ⟨hxl, hxm⟩
      rw [hc, Finset.mem_singleton] at hmem
      rcases hx with hx | ⟨_, hx⟩
      · exact hpc (hx ▸ hmem)
      · exact h1l (hx ▸ hxl)
    · exact hY
  · intro p hp hp1 hpc hzx
    rcases descend gates hop hlt u (13 + (zs : ℕ)) _ _ _ u hR hu_lt (key _ hzx) hul hum with
      ⟨w', hx, hxl, hxm⟩ | hY
    · exfalso
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_not] at hx hxl hxm
      have hmem : w' ∈ L l ∩ L m := Finset.mem_inter.2 ⟨hxl, hxm⟩
      rw [hc, Finset.mem_singleton] at hmem
      rcases hx with hx | ⟨_, hx⟩
      · exact hpc (hx ▸ hmem)
      · exact h0m (hx ▸ hxm)
    · exact hY

end PEqualNP.Outside.L_meta_1579

theorem PEqualNP.Outside.L_meta_1579 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (∀ p ∈ L l, p ≠ 0 → p ≠ c → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Y < 13 + (zs : ℕ) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (∀ p ∈ L m, p ≠ 1 → p ≠ c → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Y < 13 + (zs : ℕ) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) :=
  PEqualNP.Outside.L_meta_1579.main
