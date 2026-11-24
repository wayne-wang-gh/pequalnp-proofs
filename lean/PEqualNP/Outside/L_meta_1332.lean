import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1332_aux
open PEqualNP.CircuitLowerBounds

def valid (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
def binary (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def cut (p : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if g.inputs.any (· == p) then ⟨.or, []⟩ else g
  | .or => ⟨.or, g.inputs.filter (· != p)⟩
  | .not => if g.inputs.head? = some p then ⟨.and, []⟩ else g
  | _ => g

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem small (xs : List ℕ) (h : xs.length ≤ 2) :
    xs = [] ∨ (∃ a, xs = [a]) ∨ ∃ a b, xs = [a,b] := by
  cases xs with
  | nil => exact Or.inl rfl
  | cons a xs =>
    cases xs with
    | nil => exact Or.inr (Or.inl ⟨a,rfl⟩)
    | cons b xs =>
      cases xs with
      | nil => exact Or.inr (Or.inr ⟨a,b,rfl⟩)
      | cons c xs => simp at h

theorem cut_valid (p : ℕ) (g : Gate) (hg : valid g) : valid (cut p g) := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨ho, hl⟩
  rcases ho with rfl | rfl | rfl
  · simp only [cut]; split <;> simp_all [valid]
  · exact ⟨Or.inr (Or.inl rfl), (List.length_filter_le _ _).trans hl⟩
  · simp only [cut]; split <;> simp_all [valid]

theorem cut_not (p : ℕ) (g : Gate) (h : (cut p g).op = GateOp.not) :
    g.op = GateOp.not := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [cut]
  split at h <;> simp_all

theorem cut_binary (p : ℕ) (g : Gate) (hg : valid g) (h : binary (cut p g)) :
    binary g ∧ p ∉ g.inputs := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨ho, hl⟩
  rcases small ins hl with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
  · rcases ho with rfl | rfl | rfl <;> simp_all [cut, binary]
  · by_cases ha : a = p <;> rcases ho with rfl | rfl | rfl <;>
      simp_all [cut, binary] <;> aesop
  · by_cases ha : a = p <;> by_cases hb : b = p <;>
      rcases ho with rfl | rfl | rfl <;> simp_all [cut, binary] <;> aesop

theorem cut_eval (p : ℕ) (g : Gate) (hg : valid g)
    (v w : List Bool) (hp : w.getD p false = false)
    (h : ∀ i, i ≠ p → v.getD i false = w.getD i false) :
    (cut p g).op.eval ((cut p g).inputs.map fun i => v.getD i false) =
    g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨ho, hl⟩
  rcases small ins hl with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
  · rcases ho with rfl | rfl | rfl <;> simp [cut, GateOp.eval]
  · by_cases ha : a = p <;> rcases ho with rfl | rfl | rfl <;>
      simp_all [cut, GateOp.eval]
  · by_cases ha : a = p <;> by_cases hb : b = p <;>
      rcases ho with rfl | rfl | rfl <;>
      simp_all [cut, GateOp.eval]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    simpa [run, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])

theorem run_cut (p : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, valid g)
    (v w : List Bool) (hlen : v.length = w.length) (hp : p < w.length)
    (hz : w.getD p false = false)
    (h : ∀ i, i ≠ p → v.getD i false = w.getD i false) :
    ∀ i, i ≠ p → (run (gs.map (cut p)) v).getD i false = (run gs w).getD i false := by
  induction gs generalizing v w with
  | nil => exact h
  | cons g gs ih =>
    have he := cut_eval p g (hg g (by simp)) v w hz h
    simp only [List.map_cons, run, List.foldl_cons]
    apply ih (fun g hmem => hg g (by simp [hmem]))
    · simp [hlen]
    · simp; omega
    · rw [List.getD_append _ _ _ _ hp]; exact hz
    · intro i hi
      by_cases hil : i < w.length
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hil]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), hlen, he]

theorem run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

end PEqualNP.Outside.L_meta_1332_aux

theorem PEqualNP.Outside.L_meta_1332 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) → ∀ a b : Fin gates.length, a ≠ b → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get b).inputs.length = 2 → p.val ∈ (gates.get b).inputs → ∀ (t : ℕ) (ι : Fin t → Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin t, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  classical
  intro n m S hS gates out hg hc p hp a b hab ha ha2 hap hb hb2 hbp t ι hι I hI
  let gl := gates.map (PEqualNP.Outside.L_meta_1332_aux.cut p.val)
  have hlen : gl.length = gates.length := List.length_map _
  let e : Fin gates.length ≃ Fin gl.length := finCongr hlen.symm
  have hget (i : Fin gates.length) : gl.get (e i) =
      PEqualNP.Outside.L_meta_1332_aux.cut p.val (gates.get i) := by
    simp [gl, e, List.get_eq_getElem]
  let J := ((I.erase a).erase b).map e.toEmbedding
  let ol : Fin m → ℕ := fun o => if out o = p.val then n + gl.length else out o
  refine ⟨gl, ol, fun r => e (ι r), J, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hmem
    change g ∈ gates.map (PEqualNP.Outside.L_meta_1332_aux.cut p.val) at hmem
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hmem
    exact PEqualNP.Outside.L_meta_1332_aux.cut_valid p.val g0 (hg g0 hg0)
  · intro q hq
    obtain ⟨i, rfl⟩ := e.surjective q
    rw [hget] at hq
    obtain ⟨r, hr⟩ := hι i (PEqualNP.Outside.L_meta_1332_aux.cut_not p.val _ hq)
    exact ⟨r, congrArg e hr⟩
  · intro q hq
    obtain ⟨i, rfl⟩ := e.surjective q
    rw [hget] at hq
    obtain ⟨hi, hip⟩ := PEqualNP.Outside.L_meta_1332_aux.cut_binary p.val _
      (hg _ (List.get_mem _ _)) hq
    have hia : i ≠ a := by rintro rfl; exact hip hap
    have hib : i ≠ b := by rintro rfl; exact hip hbp
    apply Finset.mem_map.mpr
    exact ⟨i, by simp [hia, hib, hI i hi], rfl⟩
  · have hai : a ∈ I := hI a ⟨ha, ha2⟩
    have hbi : b ∈ I.erase a := by simp [hab.symm, hI b ⟨hb, hb2⟩]
    have h1 := Finset.card_erase_add_one hai
    have h2 := Finset.card_erase_add_one hbi
    simp only [J, Finset.card_map]
    omega
  · intro o x
    let x0 : Fin n → Bool := Function.update x p false
    have hz : (List.ofFn x0).getD p.val false = false := by
      rw [List.getD_eq_getElem _ _ (by simpa using p.isLt)]
      simp [x0]
    have hr := PEqualNP.Outside.L_meta_1332_aux.run_cut p.val gates hg
      (List.ofFn x) (List.ofFn x0) (by simp) (by simpa using p.isLt) hz
      (by
        intro i hi
        by_cases hin : i < n
        · rw [List.getD_eq_getElem _ _ (by simpa using hin),
            List.getD_eq_getElem _ _ (by simpa using hin)]
          simp [x0, Function.update_apply, Fin.ext_iff, hi]
        · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hin),
            List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hin)])
    have he : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o⟩ (List.ofFn x) =
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x0) := by
      by_cases ho : out o = p.val
      · change (PEqualNP.Outside.L_meta_1332_aux.run gl (List.ofFn x)).getD (ol o) false =
          (PEqualNP.Outside.L_meta_1332_aux.run gates (List.ofFn x0)).getD (out o) false
        rw [show ol o = n + gl.length by simp [ol, ho],
          List.getD_eq_default _ _ (by simp [PEqualNP.Outside.L_meta_1332_aux.run_length])]
        rw [ho, PEqualNP.Outside.L_meta_1332_aux.run_input _ _ _ (by simpa using p.isLt), hz]
      · simpa [PEqualNP.CircuitLowerBounds.Circuit.eval,
          PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.Outside.L_meta_1332_aux.run,
          gl, ol, ho] using hr (out o) ho
    rw [he, hc]
    congr 1
    apply propext
    simp [x0, Function.update_apply, and_assoc]
