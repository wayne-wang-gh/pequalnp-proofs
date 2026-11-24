import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1333

open PEqualNP.CircuitLowerBounds

-- the value a gate computes from the wires present so far
def gv (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

-- all wires after running a list of gates
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl (fun w g => w ++ [gv g w]) w

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = run gs w ++ [gv g (run gs w)] := by
  simp [run, List.foldl_append]

theorem length_run (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [gv g w])).length = _
    rw [ih]
    simp
    omega

theorem run_take_succ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    run (gs.take (j + 1)) w = run (gs.take j) w ++ [gv gs[j] (run (gs.take j) w)] := by
  rw [List.take_succ_eq_append_getElem hj, run_snoc]

theorem length_run_take (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j ≤ gs.length) :
    (run (gs.take j) w).length = w.length + j := by
  rw [length_run, List.length_take, Nat.min_eq_left hj]

theorem read_lt (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j ≤ gs.length) (i : ℕ)
    (hi : i < w.length) : (run (gs.take j) w).getD i false = w.getD i false := by
  induction j with
  | zero => simp [run]
  | succ j ih =>
    rw [run_take_succ gs w j (by omega),
      List.getD_append _ _ _ _ (by rw [length_run_take gs w j (by omega)]; omega)]
    exact ih (by omega)

theorem read_ge (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j ≤ gs.length) (i : ℕ)
    (hi : w.length + j ≤ i) : (run (gs.take j) w).getD i false = false := by
  apply List.getD_eq_default
  rw [length_run_take gs w j hj]
  exact hi

theorem read_gate (gs : List Gate) (w : List Bool) (a j : ℕ) (ha : a < j) (hj : j ≤ gs.length) :
    (run (gs.take j) w).getD (w.length + a) false =
      gv (gs[a]'(by omega)) (run (gs.take a) w) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [run_take_succ gs w j (by omega)]
    by_cases h : a = j
    · subst h
      rw [List.getD_append_right _ _ _ _ (by rw [length_run_take gs w a (by omega)])]
      have h0 : w.length + a - (run (gs.take a) w).length = 0 := by
        rw [length_run_take gs w a (by omega)]
        omega
      rw [h0]
      rfl
    · rw [List.getD_append _ _ _ _ (by rw [length_run_take gs w j (by omega)]; omega)]
      exact ih (by omega) (by omega)

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem gv_congr (g : Gate) (u u0 : List Bool)
    (h : ∀ i ∈ g.inputs, u.getD i false = u0.getD i false) : gv g u = gv g u0 := by
  unfold gv
  congr 1
  exact List.map_congr_left h

-- two runs that agree away from wire p keep agreeing, if every gate does
theorem sim (gates gl : List Gate) (hlen : gl.length = gates.length) (p : ℕ) (w w0 : List Bool)
    (hw : w.length = w0.length)
    (hag : ∀ i, i ≠ p → w.getD i false = w0.getD i false)
    (hstep : ∀ j (hj : j < gates.length) (u : List Bool),
      u.length = (run (gates.take j) w0).length →
      (∀ i, i ≠ p → u.getD i false = (run (gates.take j) w0).getD i false) →
      gv (gl[j]'(by omega)) u = gv gates[j] (run (gates.take j) w0)) :
    ∀ j, j ≤ gates.length → (run (gl.take j) w).length = (run (gates.take j) w0).length ∧
      ∀ i, i ≠ p → (run (gl.take j) w).getD i false = (run (gates.take j) w0).getD i false := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨by simpa [run] using hw, by simpa [run] using hag⟩
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hj' : j < gates.length := by omega
    have hs := hstep j hj' _ h1 h2
    rw [run_take_succ gl w j (by omega), run_take_succ gates w0 j hj']
    refine ⟨by simp [h1], ?_⟩
    intro i hi
    by_cases hlt : i < (run (gl.take j) w).length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (h1 ▸ hlt)]
      exact h2 i hi
    · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), h1, hs]

-- a gate whose value differs between two inputs either is constant on the good inputs,
-- or is a two-wire AND/OR gate reading a wire that is constant on the good inputs
theorem gate_cases {X : Type} (P : X → Prop) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hl : g.inputs.length ≤ 2) (rd1 rd0 : ℕ → Bool) (rd : X → ℕ → Bool)
    (hin : ∀ i ∈ g.inputs, rd1 i = rd0 i ∨ ∃ c, ∀ x, P x → rd x i = c)
    (hdiff : g.op.eval (g.inputs.map rd1) ≠ g.op.eval (g.inputs.map rd0)) :
    (∃ c, ∀ x, P x → g.op.eval (g.inputs.map (rd x)) = c) ∨
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ i1 i2, g.inputs = [i1, i2] ∧ ∃ e other,
      ((e = i1 ∧ other = i2) ∨ (e = i2 ∧ other = i1)) ∧ ∃ c, ∀ x, P x → rd x e = c) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hl hin hdiff ⊢
  rcases ins with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, l⟩⟩⟩
  · exact absurd rfl hdiff
  · have h1 := hin i1 (by simp)
    rcases h1 with h1 | ⟨c, hc⟩
    · exfalso
      apply hdiff
      simp [h1]
    · left
      rcases hop with rfl | rfl | rfl
      · exact ⟨c, fun x hx => by simp [GateOp.eval, hc x hx]⟩
      · exact ⟨c, fun x hx => by simp [GateOp.eval, hc x hx]⟩
      · exact ⟨!c, fun x hx => by simp [GateOp.eval, hc x hx]⟩
  · have h1 := hin i1 (by simp)
    have h2 := hin i2 (by simp)
    rcases hop with rfl | rfl | rfl
    · right
      refine ⟨Or.inl rfl, i1, i2, rfl, ?_⟩
      rcases h1 with h1 | ⟨c, hc⟩
      · rcases h2 with h2 | ⟨c, hc⟩
        · exfalso
          apply hdiff
          simp [h1, h2]
        · exact ⟨i2, i1, Or.inr ⟨rfl, rfl⟩, c, hc⟩
      · exact ⟨i1, i2, Or.inl ⟨rfl, rfl⟩, c, hc⟩
    · right
      refine ⟨Or.inr rfl, i1, i2, rfl, ?_⟩
      rcases h1 with h1 | ⟨c, hc⟩
      · rcases h2 with h2 | ⟨c, hc⟩
        · exfalso
          apply hdiff
          simp [h1, h2]
        · exact ⟨i2, i1, Or.inr ⟨rfl, rfl⟩, c, hc⟩
      · exact ⟨i1, i2, Or.inl ⟨rfl, rfl⟩, c, hc⟩
    · rcases h1 with h1 | ⟨c, hc⟩
      · exfalso
        apply hdiff
        simp [GateOp.eval, h1]
      · left
        exact ⟨!c, fun x hx => by simp [GateOp.eval, hc x hx]⟩
  · simp at hl

-- a two-wire AND gate listing a false wire is false
theorem and_false (g : Gate) (hop : g.op = GateOp.and) (hl : g.inputs.length = 2) (pv : ℕ)
    (hp : pv ∈ g.inputs) (u : List Bool) (hu : u.getD pv false = false) : gv g u = false := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hl hp
  subst hop
  rcases ins with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, l⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [List.getD_eq_getElem?_getD] at hu
    rcases hp with rfl | rfl <;> simp [gv, GateOp.eval, hu]
  · simp at hl

-- the gate put in place of a two-wire gate reading a constant wire
def repl (op : GateOp) (c : Bool) (other : ℕ) : Gate :=
  match op, c with
  | GateOp.and, true => ⟨GateOp.and, [other]⟩
  | GateOp.and, false => ⟨GateOp.or, []⟩
  | _, true => ⟨GateOp.and, []⟩
  | _, false => ⟨GateOp.or, [other]⟩

theorem repl_op (op : GateOp) (c : Bool) (o : ℕ) :
    (repl op c o).op = GateOp.and ∨ (repl op c o).op = GateOp.or := by
  cases op <;> cases c <;> simp [repl]

theorem repl_len (op : GateOp) (c : Bool) (o : ℕ) : (repl op c o).inputs.length ≤ 1 := by
  cases op <;> cases c <;> simp [repl]

theorem repl_val (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (i1 i2 e other : ℕ)
    (heo : (e = i1 ∧ other = i2) ∨ (e = i2 ∧ other = i1)) (c : Bool) (u u0 : List Bool)
    (hc : u0.getD e false = c) (hag : u.getD other false = u0.getD other false) :
    gv (repl op c other) u = gv ⟨op, [i1, i2]⟩ u0 := by
  simp only [List.getD_eq_getElem?_getD] at hc hag
  rcases hop with rfl | rfl <;> rcases heo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases c <;>
    simp [repl, gv, GateOp.eval, hc, hag]

theorem getElem_idx {α : Type} (l : List α) (i j : ℕ) (h : i = j) (hi : i < l.length)
    (hj : j < l.length) : l[i] = l[j] := by
  subst h
  rfl

-- what a gate reads either agrees at the two test inputs or is constant once p is false
theorem read_cases (n : ℕ) (gates : List Gate) (p : Fin n) (j : ℕ) (hj : j ≤ gates.length)
    (IH : ∀ a (ha : a < j),
      gv (gates[a]'(by omega))
          (run (gates.take a) (List.ofFn (fun q : Fin n => decide (q = p)))) ≠
        gv (gates[a]'(by omega)) (run (gates.take a) (List.ofFn (fun _ : Fin n => false))) →
      ∃ c, ∀ x : Fin n → Bool, x p = false →
        gv (gates[a]'(by omega)) (run (gates.take a) (List.ofFn x)) = c)
    (i : ℕ) (hi : i ≠ p.val) :
    (run (gates.take j) (List.ofFn (fun q : Fin n => decide (q = p)))).getD i false =
      (run (gates.take j) (List.ofFn (fun _ : Fin n => false))).getD i false ∨
    ∃ c, ∀ x : Fin n → Bool, x p = false →
      (run (gates.take j) (List.ofFn x)).getD i false = c := by
  by_cases hin : i < n
  · left
    rw [read_lt gates _ j hj i (by simpa using hin), read_lt gates _ j hj i (by simpa using hin),
      getD_ofFn _ i hin, getD_ofFn _ i hin]
    apply decide_eq_false
    intro h
    exact hi (congrArg Fin.val h)
  · by_cases ha : i - n < j
    · have hrd : ∀ x : Fin n → Bool, (run (gates.take j) (List.ofFn x)).getD i false =
          gv (gates[i - n]'(by omega)) (run (gates.take (i - n)) (List.ofFn x)) := by
        intro x
        have h := read_gate gates (List.ofFn x) (i - n) j ha hj
        simp only [List.length_ofFn] at h
        rw [show n + (i - n) = i by omega] at h
        exact h
      by_cases hd : gv (gates[i - n]'(by omega))
          (run (gates.take (i - n)) (List.ofFn (fun q : Fin n => decide (q = p)))) =
          gv (gates[i - n]'(by omega))
            (run (gates.take (i - n)) (List.ofFn (fun _ : Fin n => false)))
      · left
        rw [hrd, hrd]
        exact hd
      · right
        obtain ⟨c, hc⟩ := IH (i - n) ha hd
        exact ⟨c, fun x hx => by rw [hrd]; exact hc x hx⟩
    · left
      rw [read_ge gates _ j hj i (by simp only [List.length_ofFn]; omega),
        read_ge gates _ j hj i (by simp only [List.length_ofFn]; omega)]

-- some two-wire AND/OR gate other than k reads a wire that is constant once p is false
theorem second_gate (n : ℕ) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (p : Fin n) (k : ℕ) (hk : k < gates.length)
    (hkop : gates[k].op = GateOp.and) (hklen : gates[k].inputs.length = 2)
    (hkp : p.val ∈ gates[k].inputs)
    (honly : ∀ j (hj : j < gates.length), p.val ∈ gates[j].inputs → j = k)
    (w : ℕ) (v0 : Fin n) (hv0 : v0 ≠ p)
    (h1 : (run gates (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)
    (h0 : (run gates (List.ofFn (fun _ : Fin n => false))).getD w false = false)
    (hv : (run gates (List.ofFn (fun q : Fin n => decide (q = v0)))).getD w false = true) :
    ∃ r, ∃ hr : r < gates.length, r ≠ k ∧
      (gates[r].op = GateOp.and ∨ gates[r].op = GateOp.or) ∧
      ∃ i1 i2, gates[r].inputs = [i1, i2] ∧ ∃ e other,
        ((e = i1 ∧ other = i2) ∨ (e = i2 ∧ other = i1)) ∧
        ∃ c, ∀ x : Fin n → Bool, x p = false →
          (run (gates.take r) (List.ofFn x)).getD e false = c := by
  by_contra H
  have key : ∀ j (hj : j < gates.length),
      gv gates[j] (run (gates.take j) (List.ofFn (fun q : Fin n => decide (q = p)))) ≠
        gv gates[j] (run (gates.take j) (List.ofFn (fun _ : Fin n => false))) →
      ∃ c, ∀ x : Fin n → Bool, x p = false →
        gv gates[j] (run (gates.take j) (List.ofFn x)) = c := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hdiff
      by_cases hjk : j = k
      · subst hjk
        refine ⟨false, fun x hx => and_false _ hkop hklen p.val hkp _ ?_⟩
        rw [read_lt gates _ j (by omega) p.val (by simp), getD_ofFn x p.val p.isLt]
        exact hx
      · obtain ⟨hop, hl⟩ := hg gates[j] (List.getElem_mem hj)
        have hin : ∀ i ∈ gates[j].inputs,
            (run (gates.take j) (List.ofFn (fun q : Fin n => decide (q = p)))).getD i false =
              (run (gates.take j) (List.ofFn (fun _ : Fin n => false))).getD i false ∨
            ∃ c, ∀ x : Fin n → Bool, x p = false →
              (run (gates.take j) (List.ofFn x)).getD i false = c :=
          fun i hi => read_cases n gates p j (by omega) (fun a ha => ih a ha (by omega)) i
            (fun hip => hjk (honly j hj (hip ▸ hi)))
        rcases gate_cases (fun x : Fin n → Bool => x p = false) gates[j] hop hl _ _
            (fun x i => (run (gates.take j) (List.ofFn x)).getD i false) hin hdiff with
          hc | ⟨hop2, i1, i2, hins, e, other, heo, c, hc⟩
        · exact hc
        · exact absurd ⟨j, hj, hjk, hop2, i1, i2, hins, e, other, heo, c, hc⟩ H
  have hwp : w ≠ p.val := by
    intro hwp
    have h := read_lt gates (List.ofFn (fun q : Fin n => decide (q = v0))) gates.length le_rfl
      p.val (by simp)
    rw [List.take_length, getD_ofFn _ p.val p.isLt] at h
    rw [hwp, h] at hv
    exact hv0 (of_decide_eq_true hv).symm
  rcases read_cases n gates p gates.length le_rfl (fun a ha => key a ha) w hwp with
    heq | ⟨c, hc⟩
  · rw [List.take_length] at heq
    rw [h1, h0] at heq
    exact Bool.noConfusion heq
  · have e0 := hc (fun _ => false) rfl
    have e1 := hc (fun q => decide (q = v0)) (decide_eq_false (fun h => hv0 h.symm))
    rw [List.take_length] at e0 e1
    rw [h0] at e0
    rw [hv] at e1
    rw [← e0] at e1
    exact Bool.noConfusion e1

theorem main (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hC : ∀ (o : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gates, out o⟩ (List.ofFn x) =
      decide (∃ v ∈ S o, x v = true))
    (p : Fin n) (i0 : Fin m) (hpi0 : p ∈ S i0) (v0 : Fin n) (hv0S : v0 ∈ S i0) (hv0p : v0 ≠ p)
    (k : Fin gates.length) (hkop : (gates.get k).op = GateOp.and)
    (hklen : (gates.get k).inputs.length = 2) (hkp : p.val ∈ (gates.get k).inputs)
    (honly : ∀ j : Fin gates.length, p.val ∈ (gates.get j).inputs → j = k)
    (t : ℕ) (ι : Fin t → Fin gates.length)
    (hι : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → ∃ r : Fin t, ι r = q)
    (I : Finset (Fin gates.length))
    (hI : ∀ q2 : Fin gates.length, ((gates.get q2).op = GateOp.and ∨
      (gates.get q2).op = GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) :
    ∃ (gl : List Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)),
      (∀ h ∈ gl, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
        h.inputs.length ≤ 2) ∧
      (∀ q3 : Fin gl.length, (gl.get q3).op = GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧
      (∀ q4 : Fin gl.length, ((gl.get q4).op = GateOp.and ∨ (gl.get q4).op = GateOp.or) ∧
        (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧
      J.card + 2 ≤ I.card ∧
      ∀ (o2 : Fin m) (x2 : Fin n → Bool), Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) =
        decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  have hC' : ∀ (o : Fin m) (x : Fin n → Bool), (run gates (List.ofFn x)).getD (out o) false =
      decide (∃ v ∈ S o, x v = true) := hC
  simp only [List.get_eq_getElem] at hkop hklen hkp honly hι hI
  have hk := k.isLt
  obtain ⟨r, hr, hrk, hrop, i1, i2, hrin, e, other, heo, c, hc⟩ :=
    second_gate n gates hg p k.val hk hkop hklen hkp
      (fun j hj h => congrArg Fin.val (honly ⟨j, hj⟩ h)) (out i0) v0 hv0p
      (by rw [hC']; exact decide_eq_true ⟨p, hpi0, by simp⟩)
      (by rw [hC']; exact decide_eq_false (by rintro ⟨_, _, h⟩; exact Bool.noConfusion h))
      (by rw [hC']; exact decide_eq_true ⟨v0, hv0S, by simp⟩)
  have hother : other ≠ p.val := by
    intro h
    apply hrk
    refine congrArg Fin.val (honly ⟨r, hr⟩ ?_)
    show p.val ∈ gates[r].inputs
    rw [hrin, ← h]
    rcases heo with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  obtain ⟨gl, hgl⟩ : ∃ gl : List Gate,
      gl = (gates.set k.val ⟨GateOp.or, []⟩).set r (repl gates[r].op c other) := ⟨_, rfl⟩
  have hlen : gl.length = gates.length := by simp [hgl]
  have glk : gl[k.val]'(by omega) = ⟨GateOp.or, []⟩ := by
    subst hgl
    rw [List.getElem_set_ne hrk, List.getElem_set_self]
  have glr : gl[r]'(by omega) = repl gates[r].op c other := by
    subst hgl
    rw [List.getElem_set_self]
  have glo : ∀ j (hj : j < gates.length), j ≠ k.val → j ≠ r → gl[j]'(by omega) = gates[j] := by
    intro j hj h1 h2
    subst hgl
    rw [List.getElem_set_ne (Ne.symm h2), List.getElem_set_ne (Ne.symm h1)]
  have simres : ∀ (x2 : Fin n → Bool) (i : ℕ), i ≠ p.val →
      (run gl (List.ofFn x2)).getD i false =
        (run gates (List.ofFn (fun q : Fin n => if q = p then false else x2 q))).getD i false := by
    intro x2
    have hx0p : (fun q : Fin n => if q = p then false else x2 q) p = false := by simp
    have h := sim gates gl hlen p.val (List.ofFn x2)
      (List.ofFn (fun q : Fin n => if q = p then false else x2 q)) (by simp) ?_ ?_
      gates.length le_rfl
    · have h2 := h.2
      rw [List.take_of_length_le (by omega), List.take_length] at h2
      exact h2
    · intro i hi
      by_cases hin : i < n
      · rw [getD_ofFn _ i hin, getD_ofFn _ i hin]
        have hne : (⟨i, hin⟩ : Fin n) ≠ p := fun h => hi (congrArg Fin.val h)
        simp [hne]
      · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
    · intro j hj u hu hagree
      by_cases hjk : j = k.val
      · subst hjk
        rw [glk, and_false gates[k.val] hkop hklen p.val hkp _
          (by rw [read_lt gates _ _ (by omega) p.val (by simp), getD_ofFn _ p.val p.isLt]
              exact hx0p)]
        simp [gv, GateOp.eval]
      · by_cases hjr : j = r
        · subst hjr
          rw [glr]
          have e1 : gv gates[j] (run (gates.take j)
              (List.ofFn (fun q : Fin n => if q = p then false else x2 q))) =
              gv ⟨gates[j].op, [i1, i2]⟩ (run (gates.take j)
                (List.ofFn (fun q : Fin n => if q = p then false else x2 q))) := by
            unfold gv
            simp only [hrin]
          rw [e1]
          exact repl_val _ hrop i1 i2 e other heo c u _ (hc _ hx0p) (hagree other hother)
        · rw [glo j hj hjk hjr]
          apply gv_congr
          intro i hi
          apply hagree
          intro hip
          exact hjk (congrArg Fin.val (honly ⟨j, hj⟩ (hip ▸ hi)))
  refine ⟨gl, fun o => if out o = p.val then n + gates.length else out o,
    fun r2 => ⟨(ι r2).val, by omega⟩,
    ((I.erase k).erase ⟨r, hr⟩).map (finCongr hlen.symm).toEmbedding, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    rw [hgl] at hh
    rcases List.mem_or_eq_of_mem_set hh with hh | rfl
    · rcases List.mem_or_eq_of_mem_set hh with hh | rfl
      · exact hg h hh
      · exact ⟨Or.inr (Or.inl rfl), by simp⟩
    · refine ⟨?_, le_trans (repl_len _ _ _) (by norm_num)⟩
      rcases repl_op gates[r].op c other with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · intro q3 hq3
    simp only [List.get_eq_getElem] at hq3
    have h1 : q3.val ≠ k.val := by
      intro h
      rw [getElem_idx gl q3.val k.val h q3.isLt (by omega), glk] at hq3
      exact GateOp.noConfusion hq3
    have h2 : q3.val ≠ r := by
      intro h
      rw [getElem_idx gl q3.val r h q3.isLt (by omega), glr] at hq3
      rcases repl_op gates[r].op c other with h' | h' <;> rw [h'] at hq3 <;>
        exact GateOp.noConfusion hq3
    rw [glo q3.val (by omega) h1 h2] at hq3
    obtain ⟨r2, hr2⟩ := hι ⟨q3.val, by omega⟩ hq3
    exact ⟨r2, Fin.ext (show (ι r2).val = q3.val from congrArg Fin.val hr2)⟩
  · rintro q4 ⟨hop4, hl4⟩
    simp only [List.get_eq_getElem] at hop4 hl4
    have h1 : q4.val ≠ k.val := by
      intro h
      rw [getElem_idx gl q4.val k.val h q4.isLt (by omega), glk] at hl4
      simp at hl4
    have h2 : q4.val ≠ r := by
      intro h
      rw [getElem_idx gl q4.val r h q4.isLt (by omega), glr] at hl4
      have := repl_len gates[r].op c other
      omega
    rw [glo q4.val (by omega) h1 h2] at hop4 hl4
    rw [Finset.mem_map]
    refine ⟨⟨q4.val, by omega⟩, ?_, Fin.ext rfl⟩
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun h => h2 (congrArg Fin.val h), fun h => h1 (congrArg Fin.val h), hI _ ⟨hop4, hl4⟩⟩
  · rw [Finset.card_map]
    have hkI : k ∈ I := hI k ⟨Or.inl hkop, hklen⟩
    have hrI : (⟨r, hr⟩ : Fin gates.length) ∈ I.erase k :=
      Finset.mem_erase.mpr ⟨fun h => hrk (congrArg Fin.val h),
        hI _ ⟨hrop, by show gates[r].inputs.length = 2; rw [hrin]; rfl⟩⟩
    have e1 := Finset.card_erase_add_one hrI
    have e2 := Finset.card_erase_add_one hkI
    omega
  · intro o2 x2
    show (run gl (List.ofFn x2)).getD (if out o2 = p.val then n + gates.length else out o2)
      false = _
    by_cases ho : out o2 = p.val
    · simp only [ho, ↓reduceIte]
      rw [List.getD_eq_default _ _ (by rw [length_run, List.length_ofFn]; omega)]
      symm
      apply decide_eq_false
      rintro ⟨v2, hv2S, hv2p, -⟩
      have h := hC' o2 (fun q => decide (q = v2))
      have hfull := read_lt gates (List.ofFn (fun q : Fin n => decide (q = v2))) gates.length
        le_rfl p.val (by simp)
      rw [List.take_length, getD_ofFn _ p.val p.isLt] at hfull
      rw [ho, hfull, decide_eq_false (fun h => hv2p h.symm),
        decide_eq_true (⟨v2, hv2S, by simp⟩ : ∃ v ∈ S o2, decide (v = v2) = true)] at h
      exact Bool.noConfusion h
    · simp only [ho, ↓reduceIte]
      rw [simres x2 _ ho, hC']
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨v, hvS, hv⟩
        by_cases hvp : v = p
        · simp [hvp] at hv
        · exact ⟨v, hvS, hvp, by simpa [hvp] using hv⟩
      · rintro ⟨v, hvS, hvp, hv⟩
        exact ⟨v, hvS, by simp [hvp, hv]⟩

end PEqualNP.Outside.L_meta_1333

theorem PEqualNP.Outside.L_meta_1333 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) → ∀ k : Fin gates.length, (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get k).inputs.length = 2 → p.val ∈ (gates.get k).inputs → (∀ j : Fin gates.length, p.val ∈ (gates.get j).inputs → j = k) → (∀ o1 : Fin m, out o1 ≠ n + k.val) → ∀ (t : ℕ) (ι : Fin t → Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin t, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  intro n m S _ gates out hg hC p hp k hkop hklen hkp honly _ t ι hι I hI
  obtain ⟨i0, hpi0, v0, hv0S, hv0p⟩ := hp
  exact PEqualNP.Outside.L_meta_1333.main n m S gates out hg hC p i0 hpi0 v0 hv0S hv0p k hkop
    hklen hkp honly t ι hι I hI
