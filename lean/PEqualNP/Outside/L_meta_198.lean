import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_198

open PEqualNP.CircuitLowerBounds

-- One gate appended to the wire list.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- Running a list of gates.
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (step w g) := rfl

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_pre (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step; exact List.getD_append _ _ _ _ h

theorem step_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

theorem run_len (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run_nil]
  | cons g gs ih => intro w; rw [run_cons, ih, step_len]; simp; omega

theorem run_pre (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [run_cons, ih _ _ (by rw [step_len]; omega), step_pre _ _ _ h]

theorem any_congr (l : List ℕ) (f g : ℕ → Bool) (h : ∀ k ∈ l, f k = g k) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun k hk => h k (by simp [hk]))]

-- An OR chain starting from wire prev over the wires ks.
def chainG : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | p, prev, k :: ks => ⟨GateOp.or, [prev, k]⟩ :: chainG (p + 1) p ks

def res : ℕ → ℕ → List ℕ → ℕ
  | _, prev, [] => prev
  | p, _, _ :: ks => res (p + 1) p ks

theorem chainG_len : ∀ (ks : List ℕ) (p prev : ℕ), (chainG p prev ks).length = ks.length := by
  intro ks
  induction ks with
  | nil => intro p prev; rfl
  | cons k ks ih => intro p prev; simp [chainG, ih]

theorem chainG_fan : ∀ (ks : List ℕ) (p prev : ℕ), ∀ g ∈ chainG p prev ks,
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  intro ks
  induction ks with
  | nil => intro p prev g hg; simp [chainG] at hg
  | cons k ks ih =>
    intro p prev g hg
    simp only [chainG, List.mem_cons] at hg
    rcases hg with hg | hg
    · subst hg; simp
    · exact ih _ _ g hg

theorem chain_val (v : ℕ → Bool) : ∀ (ks : List ℕ) (p prev : ℕ) (w : List Bool) (b : Bool),
    w.length = p → prev < p → (∀ k ∈ ks, k < p ∧ w.getD k false = v k) →
    w.getD prev false = b →
    (run (chainG p prev ks) w).getD (res p prev ks) false = (b || ks.any v) := by
  intro ks
  induction ks with
  | nil => intro p prev w b _ _ _ hb; simp only [chainG, res, run_nil]; rw [hb]; simp
  | cons k ks ih =>
    intro p prev w b hl hp hk hb
    simp only [chainG, res, run_cons]
    have hk0 := hk k (by simp)
    rw [ih (p + 1) p _ (b || v k) (by rw [step_len]; omega) (by omega)]
    · simp [Bool.or_assoc]
    · intro k' hk'
      have := hk k' (by simp [hk'])
      refine ⟨by omega, ?_⟩
      rw [step_pre _ _ _ (by omega)]; exact this.2
    · rw [← hl, step_last]
      simp only [GateOp.eval, List.map_cons, List.map_nil]
      rw [hb, hk0.2]; simp

-- One block per star: an OR chain over its leaves, then an AND with its centre.
def stars : ℕ → List (ℕ × List ℕ) → List Gate
  | _, [] => []
  | p, (_, []) :: S => stars p S
  | p, (t, j :: js) :: S =>
      chainG p j js ++ [⟨GateOp.and, [res p j js, t]⟩] ++ stars (p + js.length + 1) S

def outs : ℕ → List (ℕ × List ℕ) → List ℕ
  | _, [] => []
  | p, (_, []) :: S => outs p S
  | p, (_, _ :: js) :: S => (p + js.length) :: outs (p + js.length + 1) S

theorem stars_len : ∀ (S : List (ℕ × List ℕ)) (p : ℕ),
    (stars p S).length = (S.map fun e => e.2.length).sum := by
  intro S
  induction S with
  | nil => intro p; rfl
  | cons e S ih =>
    intro p
    obtain ⟨t, L⟩ := e
    cases L with
    | nil => simp [stars, ih]
    | cons j js => simp [stars, ih, chainG_len]; omega

theorem outs_len : ∀ (S : List (ℕ × List ℕ)) (p : ℕ), (outs p S).length ≤ S.length := by
  intro S
  induction S with
  | nil => intro p; simp [outs]
  | cons e S ih =>
    intro p
    obtain ⟨t, L⟩ := e
    cases L with
    | nil => have := ih p; simp [outs]; omega
    | cons j js => have := ih (p + js.length + 1); simp [outs]; omega

theorem outs_lt : ∀ (S : List (ℕ × List ℕ)) (p : ℕ), ∀ o ∈ outs p S, o < p + (stars p S).length := by
  intro S
  induction S with
  | nil => intro p o ho; simp [outs] at ho
  | cons e S ih =>
    intro p o ho
    obtain ⟨t, L⟩ := e
    cases L with
    | nil => simp only [outs] at ho; simp only [stars]; exact ih p o ho
    | cons j js =>
      simp only [outs, List.mem_cons] at ho
      simp only [stars, List.length_append, chainG_len]
      rcases ho with ho | ho
      · simp; omega
      · have := ih _ o ho; simp at this ⊢; omega

theorem stars_fan : ∀ (S : List (ℕ × List ℕ)) (p : ℕ), ∀ g ∈ stars p S,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro S
  induction S with
  | nil => intro p g hg; simp [stars] at hg
  | cons e S ih =>
    intro p g hg
    obtain ⟨t, L⟩ := e
    cases L with
    | nil => simp only [stars] at hg; exact ih p g hg
    | cons j js =>
      simp only [stars, List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | hg
      · have := chainG_fan js p j g hg; exact ⟨Or.inr this.1, by omega⟩
      · subst hg; simp
      · exact ih _ g hg

theorem stars_val (v : ℕ → Bool) (m : ℕ) : ∀ (S : List (ℕ × List ℕ)) (p : ℕ) (w : List Bool),
    w.length = p → m ≤ p → (∀ i < m, w.getD i false = v i) →
    (∀ e ∈ S, e.1 < m ∧ ∀ j ∈ e.2, j < m) →
    (outs p S).any (fun o => (run (stars p S) w).getD o false) =
      S.any (fun e => v e.1 && e.2.any v) := by
  intro S
  induction S with
  | nil => intro p w _ _ _ _; simp [outs]
  | cons e S ih =>
    intro p w hl hm hv hS
    obtain ⟨t, L⟩ := e
    have hS' : ∀ e ∈ S, e.1 < m ∧ ∀ j ∈ e.2, j < m := fun e he => hS e (by simp [he])
    have he := hS (t, L) (by simp)
    cases L with
    | nil =>
      simp only [outs, stars]
      rw [ih p w hl hm hv hS']
      simp
    | cons j js =>
      simp only [outs, stars, List.any_cons]
      set w1 := run (chainG p j js ++ [⟨GateOp.and, [res p j js, t]⟩]) w with hw1
      have hl1 : w1.length = p + js.length + 1 := by
        rw [hw1, run_len]; simp [chainG_len]; omega
      have hv1 : ∀ i < m, w1.getD i false = v i := by
        intro i hi; rw [hw1, run_pre _ _ _ (by omega)]; exact hv i hi
      rw [run_append, ← hw1, ih _ w1 hl1 (by omega) hv1 hS',
        run_pre _ _ _ (by omega)]
      congr 1
      rw [hw1, run_append]
      have hc := chain_val v js p j w (v j) hl (by have := he.2 j (by simp); omega)
        (fun k hk => ⟨by have := he.2 k (by simp [hk]); omega, hv k (he.2 k (by simp [hk]))⟩)
        (hv j (he.2 j (by simp)))
      have hlc : (run (chainG p j js) w).length = p + js.length := by
        rw [run_len, chainG_len, hl]
      rw [run_cons, run_nil, ← hlc, step_last]
      simp only [GateOp.eval, List.map_cons, List.map_nil]
      rw [hc, run_pre _ _ _ (by rw [hl]; have := he.1; omega), hv t he.1]
      simp [Bool.and_comm]

-- The leaves assigned to a cover vertex t: neighbours j, with t below j when j is in T too.
def leaves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (t : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => G.Adj t j ∧ (j ∈ T → t < j))

theorem leaves_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) :
    ∑ t ∈ T, (leaves G T t).card ≤ G.edgeFinset.card := by
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun e => s(e.1, e.2))
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_sigma, leaves, Finset.mem_filter] at he
    simp [SimpleGraph.mem_edgeFinset, he.2.2.1]
  · intro e he e' he' h
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, leaves,
      Finset.mem_filter] at he he'
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Sigma.ext h1 (heq_of_eq h2)
    · exfalso
      have a := he.2.2.2 (by rw [h2]; exact he'.1)
      have b := he'.2.2.2 (by rw [← h1]; exact he.1)
      rw [h1, h2] at a
      exact lt_asymm a b

end PEqualNP.Outside.L_meta_198

open PEqualNP.Outside.L_meta_198 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_198 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n)) (s : ℕ), (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → s + 1 = A.card + G.edgeFinset.card + T.card → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s := by
  intro n G _ A T s _ hcov hs
  set S : List (ℕ × List ℕ) :=
    T.toList.map (fun t : Fin n => ((t : ℕ), (leaves G T t).toList.map Fin.val)) with hSdef
  set I : List ℕ := A.toList.map Fin.val ++ outs n S with hIdef
  set P : ℕ := n + (stars n S).length with hP
  refine ⟨⟨stars n S ++ chainG P (I.headD 0) I.tail,
    if I = [] then P else res P (I.headD 0) I.tail⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · have := stars_fan S n g hg
      refine ⟨?_, this.2⟩
      rcases this.1 with h | h <;> rw [h] <;> simp
    · have := chainG_fan _ _ _ g hg
      refine ⟨by rw [this.1]; simp, by omega⟩
  · have heq : (stars n S).length = ∑ t ∈ T, (leaves G T t).card := by
      rw [stars_len, hSdef, List.map_map, ← Finset.sum_map_toList]
      simp [Function.comp_def]
    have hsum : (stars n S).length ≤ G.edgeFinset.card := heq ▸ leaves_card G T
    have hT0 : T.card = 0 → (stars n S).length = 0 := by
      intro h
      rw [Finset.card_eq_zero] at h
      rw [heq, h, Finset.sum_empty]
    have hI : I.length ≤ A.card + T.card := by
      have := outs_len S n
      have hSl : S.length = T.card := by rw [hSdef, List.length_map, Finset.length_toList]
      rw [hIdef, List.length_append, List.length_map, Finset.length_toList]
      omega
    show (stars n S ++ chainG P (I.headD 0) I.tail).length ≤ s
    rw [List.length_append, chainG_len, List.length_tail]
    omega
  · intro x
    set v : ℕ → Bool := fun i => (List.ofFn x).getD i false with hv
    have hvx : ∀ i : Fin n, v i = x i := by
      intro i; simp [hv]
    set W := run (stars n S) (List.ofFn x) with hW
    have hWl : W.length = P := by rw [hW, run_len]; simp [hP]
    have hWv : ∀ i < n, W.getD i false = v i := by
      intro i hi; rw [hW, run_pre _ _ _ (by simpa using hi)]
    have hIlt : ∀ i ∈ I, i < P := by
      intro i hi
      simp only [hIdef, List.mem_append, List.mem_map] at hi
      rcases hi with ⟨a, _, rfl⟩ | hi
      · omega
      · exact outs_lt S n i hi
    have heval : Circuit.eval ⟨stars n S ++ chainG P (I.headD 0) I.tail,
        if I = [] then P else res P (I.headD 0) I.tail⟩ (List.ofFn x) =
        I.any (fun o => W.getD o false) := by
      show (run _ _).getD _ false = _
      rw [run_append, ← hW]
      rcases hI : I with _ | ⟨i0, is⟩
      · simp only [List.headD_nil, List.tail_nil, chainG, run_nil, ↓reduceIte, List.any_nil]
        rw [List.getD_eq_default _ _ (by omega)]
      · simp only [List.headD_cons, List.tail_cons, reduceCtorEq, ↓reduceIte]
        have h0 := hIlt i0 (by rw [hI]; simp)
        rw [chain_val (fun o => W.getD o false) is P i0 W _ hWl h0
          (fun k hk => ⟨hIlt k (by rw [hI]; simp [hk]), rfl⟩) rfl]
        simp
    rw [heval, hIdef, List.any_append]
    have hA : (A.toList.map Fin.val).any (fun o => W.getD o false) =
        (A.toList.map Fin.val).any v := by
      apply any_congr
      intro k hk
      simp only [List.mem_map] at hk
      obtain ⟨a, _, rfl⟩ := hk
      exact hWv a a.isLt
    rw [hA, hW, stars_val v n S n (List.ofFn x) (by simp) le_rfl (fun i hi => rfl)
      (by
        intro e he
        simp only [hSdef, List.mem_map] at he
        obtain ⟨t, _, rfl⟩ := he
        refine ⟨t.isLt, ?_⟩
        intro j hj
        simp only [List.mem_map] at hj
        obtain ⟨j, _, rfl⟩ := hj
        exact j.isLt)]
    rw [Bool.eq_iff_iff]
    simp only [hSdef, Bool.or_eq_true, List.any_eq_true, List.mem_map, Finset.mem_toList,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨_, ⟨a, ha, rfl⟩, h⟩ | ⟨_, ⟨t, ht, rfl⟩, h1, k, hk, h2⟩)
      · exact Or.inl ⟨a, ha, by rw [← hvx]; exact h⟩
      · simp only [List.mem_map, Finset.mem_toList] at hk
        obtain ⟨j, hj, rfl⟩ := hk
        exact Or.inr ⟨t, j, (Finset.mem_filter.mp hj).2.1, by rw [← hvx]; exact h1, by rw [← hvx]; exact h2⟩
    · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
      · exact Or.inl ⟨a, ⟨a, ha, rfl⟩, by rw [hvx]; exact h⟩
      · right
        have key : ∀ i j : Fin n, G.Adj i j → x i = true → x j = true → i ∈ T →
            (j ∈ T → i < j) → ∃ e, (∃ t, t ∈ T ∧ ((t : ℕ), (leaves G T t).toList.map Fin.val) = e)
              ∧ v e.1 = true ∧ ∃ k ∈ e.2, v k = true := by
          intro i j hij hi hj hiT hlt
          refine ⟨_, ⟨i, hiT, rfl⟩, by rw [hvx]; exact hi, j, ?_, by rw [hvx]; exact hj⟩
          simp only [List.mem_map, Finset.mem_toList, leaves, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨j, ⟨hij, hlt⟩, rfl⟩
        have hne : i ≠ j := G.ne_of_adj hij
        by_cases hiT : i ∈ T
        · by_cases hjT : j ∈ T
          · rcases lt_or_gt_of_ne hne with h | h
            · exact key i j hij hi hj hiT (fun _ => h)
            · exact key j i hij.symm hj hi hjT (fun _ => h)
          · exact key i j hij hi hj hiT (fun h => absurd h hjT)
        · have hjT : j ∈ T := (hcov i j hij).resolve_left hiT
          exact key j i hij.symm hj hi hjT (fun h => absurd h hiT)
