import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1573
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

theorem factL : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ l' ∈ ({4, 10, 12} : Finset (Fin 13)),
    l' ≠ l → ∀ p ∈ Lf l, p ≠ 0 → (1 : Fin 13) ∉ Lf l' ∧ p ∉ Lf l' := by decide

theorem factM : ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ m' ∈ ({1, 5, 11} : Finset (Fin 13)),
    m' ≠ m → ∀ p ∈ Lf m, p ≠ 1 → (0 : Fin 13) ∉ Lf m' ∧ p ∉ Lf m' := by decide

theorem zeroM : ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (0 : Fin 13) ∉ Lf m := by decide

theorem oneL : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (1 : Fin 13) ∉ Lf l := by decide

/-- A wire true at `x` is true at every input above `x`. -/
theorem up (gates : List Gate) (g : ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin 13 → Bool) (hxy : ∀ v, x v = true → y v = true)
    (h : Circuit.eval ⟨gates, g⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, g⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  exact mono2 gates hleg _ _ (by simp) (ofFn_mono 13 x y hxy) g h

end PEqualNP.Outside.L_meta_1573

open PEqualNP.Outside.L_meta_1573 in
theorem PEqualNP.Outside.L_meta_1573 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false → (∃ p ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) →
      ∀ l' ∈ ({4, 10, 12} : Finset (Fin 13)), l' ≠ l → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l'))) = true) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → (∃ p ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) →
      ∀ m' ∈ ({1, 5, 11} : Finset (Fin 13)), m' ≠ m → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m'))) = true) := by
  intro L hL gates g hleg
  have hLf : L = Lf := by funext s; rw [hL s]; rfl
  subst hLf
  constructor
  · rintro m hm l hl hfalse ⟨p, hp, htrue⟩ l' hl' hne
    by_cases hp0 : p = 0
    · exfalso
      subst hp0
      have := up gates g hleg _ (fun v : Fin 13 => decide (v ∉ Lf m)) (fun v hv => by
        have hv' : v = 0 := by simpa using hv
        subst hv'
        simpa using zeroM m hm) htrue
      rw [this] at hfalse
      exact absurd hfalse (by simp)
    · obtain ⟨h1, h2⟩ := factL l hl l' hl' hne p hp hp0
      refine up gates g hleg _ _ (fun v hv => ?_) htrue
      have hv' : v = p ∨ v = 1 := by
        have := of_decide_eq_true hv
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr h.2
      rcases hv' with rfl | rfl
      · simpa using h2
      · simpa using h1
  · rintro l hl m hm hfalse ⟨p, hp, htrue⟩ m' hm' hne
    by_cases hp1 : p = 1
    · exfalso
      subst hp1
      have := up gates g hleg _ (fun v : Fin 13 => decide (v ∉ Lf l)) (fun v hv => by
        have hv' : v = 1 := by simpa using hv
        subst hv'
        simpa using oneL l hl) htrue
      rw [this] at hfalse
      exact absurd hfalse (by simp)
    · obtain ⟨h1, h2⟩ := factM m hm m' hm' hne p hp hp1
      refine up gates g hleg _ _ (fun v hv => ?_) htrue
      have hv' : v = p ∨ v = 0 := by
        have := of_decide_eq_true hv
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr h.2
      rcases hv' with rfl | rfl
      · simpa using h2
      · simpa using h1
