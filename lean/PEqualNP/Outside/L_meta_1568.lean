import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1568
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

/-- The line number `s` of Z13. -/
def Lf (s : Fin 13) : Finset (Fin 13) := {s, s + 1, s + 3, s + 9}

theorem meet_one : ∀ t u p q : Fin 13, t ≠ u → p ∈ Lf t → p ∈ Lf u → q ∈ Lf t → q ∈ Lf u →
    p = q := by decide

theorem half (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List Gate) (g : ℕ) (t u : Fin 13)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htu : t ≠ u)
    (hu : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lf u))) = false)
    (h2 : 2 ≤ ((Lf t).filter (fun p => Circuit.eval ⟨gates, g⟩ (List.ofFn (T t p)) = true)).card) :
    ∃ p ∈ Lf t \ Lf u, ∃ v ∈ Lf u, (T t p) v = true := by
  obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.1 h2
  rw [Finset.mem_filter] at hp1 hp2
  have key : ∀ p, p ∈ Lf t → p ∉ Lf u →
      Circuit.eval ⟨gates, g⟩ (List.ofFn (T t p)) = true →
      ∃ p ∈ Lf t \ Lf u, ∃ v ∈ Lf u, (T t p) v = true := by
    intro p hp hpu htrue
    refine ⟨p, Finset.mem_sdiff.2 ⟨hp, hpu⟩, ?_⟩
    by_contra hcon
    push_neg at hcon
    rw [eval_eq] at htrue hu
    have := mono2 gates hleg (List.ofFn (T t p)) (List.ofFn (fun v : Fin 13 => decide (v ∉ Lf u)))
      (by simp) (by
        apply ofFn_mono
        intro v hv
        have : v ∉ Lf u := fun hin => by
          have := hcon v hin
          rw [hv] at this
          exact absurd this (by simp)
        simp [this]) g htrue
    rw [this] at hu
    exact absurd hu (by simp)
  by_cases h1 : p1 ∈ Lf u
  · by_cases h2' : p2 ∈ Lf u
    · exact absurd (meet_one t u p1 p2 htu hp1.1 h1 hp2.1 h2') hne
    · exact key p2 hp2.1 h2' hp2.2
  · exact key p1 hp1.1 h1 hp1.2

end PEqualNP.Outside.L_meta_1568

open PEqualNP.Outside.L_meta_1568 in
theorem PEqualNP.Outside.L_meta_1568 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t u : Fin 13),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → t ≠ u →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L u))) = false →
    2 ≤ ((L t).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (T t p)) = true)).card →
    2 ≤ ((L u).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (T u p)) = true)).card →
    (∃ p ∈ L t \ L u, ∃ v ∈ L u, (T t p) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (T u p) v = true) := by
  intro L hL T gates g t u _ hleg htu ht hu h2t h2u
  have hLf : L = Lf := by funext s; rw [hL s]; rfl
  subst hLf
  exact ⟨half T gates g t u hleg htu hu h2t, half T gates g u t hleg (Ne.symm htu) ht h2u⟩
