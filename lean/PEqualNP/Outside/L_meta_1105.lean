import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1105

open PEqualNP.CircuitLowerBounds

-- one gate appended to the list of wire values
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem foldl_length (gs : List Gate) : ∀ W : List Bool,
    (gs.foldl stp W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    rw [List.foldl_cons, ih]
    simp [stp]
    omega

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem getD_big (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem prefix_keep (gs : List Gate) : ∀ (W : List Bool) (i : ℕ), i < W.length →
    (gs.foldl stp W).getD i false = W.getD i false := by
  induction gs with
  | nil => intro W i _; rfl
  | cons g gs ih =>
    intro W i h
    rw [List.foldl_cons, ih (stp W g) i (by simp [stp]; omega)]
    simp only [stp, getD_snoc]
    rw [if_neg (by omega)]

def rel (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

theorem sim (ρ : ℕ → ℕ) (gs : List Gate) : ∀ (W W' : List Bool),
    (∀ t i, i = W.length + t ↔ ρ i = W'.length + t) →
    (∀ i, W.getD i false = W'.getD (ρ i) false) →
    ∀ i, (gs.foldl stp W).getD i false = ((gs.map (rel ρ)).foldl stp W').getD (ρ i) false := by
  induction gs with
  | nil => intro W W' _ H; simpa using H
  | cons g gs ih =>
    intro W W' hρ H
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    apply ih
    · intro t i
      have := hρ (t + 1) i
      simp only [stp, List.length_append, List.length_singleton]
      constructor
      · intro e; have := this.1 (by omega); omega
      · intro e; have := this.2 (by omega); omega
    · intro i
      simp only [stp, getD_snoc]
      have h0 := hρ 0 i
      simp only [add_zero] at h0
      by_cases hi : i = W.length
      · rw [if_pos hi, if_pos (h0.1 hi)]
        simp only [rel, List.map_map]
        congr 1
        apply List.map_congr_left
        intro k _
        exact H k
      · rw [if_neg hi, if_neg (fun e => hi (h0.2 e))]
        exact H i

def r1 (n i : ℕ) : ℕ := if i < n then i else i + 1

def r2 (n m i : ℕ) : ℕ := if i < n then i else if i < n + m then i + 1 else if i = n + m then n else i

theorem mono_pre (l : List Gate) (j : ℕ) (P : Gate → Prop)
    (h : ∀ i g, l[i]? = some g → i ≠ j → P g) : ∀ g ∈ l.take j, P g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
  rw [List.getElem?_take] at hi
  by_cases h2 : i < j
  · rw [if_pos h2] at hi
    exact h i g hi (by omega)
  · rw [if_neg h2] at hi
    simp at hi

theorem mono_post (l : List Gate) (j : ℕ) (P : Gate → Prop)
    (h : ∀ i g, l[i]? = some g → i ≠ j → P g) : ∀ g ∈ l.drop (j + 1), P g := by
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
  rw [List.getElem?_drop] at hi
  exact h _ g hi (by omega)

end PEqualNP.Outside.L_meta_1105

open PEqualNP.Outside.L_meta_1105 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1105 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), (∀ i (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[i]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (i = j ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not))) → ∃ (D H : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D ∧ PEqualNP.CircuitLowerBounds.IsMonotoneCircuit H ∧ D.size ≤ C.size ∧ H.size ≤ C.size ∧ ∀ x : List Bool, x.length = n → C.eval x = D.eval (x ++ [!(H.eval x)]) := by
  intro n C j hC
  have hP : ∀ i g, C.gates[i]? = some g → i ≠ j → (g.op = GateOp.and ∨ g.op = GateOp.or) := by
    intro i g hg hne
    rcases hC i g hg with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h.1 hne
  by_cases hj : ∃ g, C.gates[j]? = some g ∧ g.op = GateOp.not
  · obtain ⟨g, hg, hgn⟩ := hj
    have hjl : j < C.gates.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hg
      simp at hg
    have hgj : C.gates[j] = g := by
      rw [List.getElem?_eq_getElem hjl] at hg
      exact Option.some.inj hg
    let pre := C.gates.take j
    let post := C.gates.drop (j + 1)
    have hsplit : C.gates = pre ++ g :: post := by
      rw [← hgj, ← List.drop_eq_getElem_cons hjl]
      exact (List.take_append_drop j C.gates).symm
    have hpl : pre.length = j := by simp [pre]; omega
    have hpre := mono_pre C.gates j _ hP
    have hpost := mono_post C.gates j _ hP
    refine ⟨⟨pre.map (rel (r1 n)) ++ post.map (rel (r2 n pre.length)), r2 n pre.length C.output⟩,
      ⟨pre, g.inputs.headD (n + pre.length)⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro g' hg'
      simp only [List.mem_append, List.mem_map] at hg'
      rcases hg' with ⟨g0, hg0, rfl⟩ | ⟨g0, hg0, rfl⟩
      · exact hpre g0 hg0
      · exact hpost g0 hg0
    · exact hpre
    · simp only [Circuit.size, List.length_append, List.length_map]
      rw [hsplit]
      simp
    · simp only [Circuit.size]
      rw [hsplit]
      simp
    · intro x hx
      set b := !(Circuit.eval ⟨pre, g.inputs.headD (n + pre.length)⟩ x) with hb
      let Wp := pre.foldl stp x
      let Wq := (pre.map (rel (r1 n))).foldl stp (x ++ [b])
      have hLp : Wp.length = n + pre.length := by simp only [Wp]; rw [foldl_length, hx]
      have hLq : Wq.length = n + 1 + pre.length := by
        simp only [Wq]; rw [foldl_length]; simp [hx]
      have s1 := sim (r1 n) pre x (x ++ [b])
        (by intro t i; simp only [r1, List.length_append, List.length_singleton, hx]; split_ifs <;> omega)
        (by
          intro i
          simp only [r1]
          split_ifs with h
          · rw [getD_snoc, if_neg (by omega)]
          · rw [getD_big x i (by omega), getD_big _ _ (by simp; omega)])
      have hqn : Wq.getD n false = b := by
        simp only [Wq]
        rw [prefix_keep _ _ n (by simp [hx]), getD_snoc, if_pos hx.symm]
      have hv : g.op.eval (g.inputs.map fun i => Wp.getD i false) = b := by
        rw [hgn, hb, eval_eq]
        simp only [GateOp.eval]
        congr 1
        cases hi : g.inputs with
        | nil => simp only [List.map_nil, List.headD_nil]; rw [getD_big _ _ (le_of_eq hLp)]
        | cons a t => rfl
      have hL1 : (stp Wp g).length = n + pre.length + 1 := by
        simp only [stp, List.length_append, List.length_singleton]; rw [hLp]
      have s2 := sim (r2 n pre.length) post (stp Wp g) Wq
        (by intro t i; rw [hL1, hLq]; simp only [r2]; split_ifs <;> omega)
        (by
          intro i
          have e1 : (stp Wp g).getD i false = if i = Wp.length then b else Wp.getD i false := by
            simp only [stp]; rw [getD_snoc, hv]
          rw [e1, hLp]
          have s1i := s1 i
          by_cases c1 : i < n
          · have ha : r2 n pre.length i = i := by simp only [r2]; rw [if_pos c1]
            have hb2 : r1 n i = i := by simp only [r1]; rw [if_pos c1]
            rw [if_neg (by omega), ha]
            rw [hb2] at s1i
            exact s1i
          · by_cases c2 : i < n + pre.length
            · have ha : r2 n pre.length i = i + 1 := by simp only [r2]; rw [if_neg c1, if_pos c2]
              have hb2 : r1 n i = i + 1 := by simp only [r1]; rw [if_neg c1]
              rw [if_neg (by omega), ha]
              rw [hb2] at s1i
              exact s1i
            · by_cases c3 : i = n + pre.length
              · have : r2 n pre.length i = n := by simp only [r2]; rw [if_neg c1, if_neg c2, if_pos c3]
                rw [if_pos c3, this, hqn]
              · have : r2 n pre.length i = i := by simp only [r2]; rw [if_neg c1, if_neg c2, if_neg c3]
                rw [if_neg c3, this, getD_big _ _ (by omega), getD_big _ _ (by omega)])
      rw [eval_eq, eval_eq, hsplit, List.foldl_append, List.foldl_cons, List.foldl_append]
      exact s2 C.output
  · have hall : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
      rcases hC i g hi with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd ⟨g, h.1 ▸ hi, h.2⟩ hj
    refine ⟨⟨C.gates.map (rel (r1 n)), r1 n C.output⟩, ⟨[], 0⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro g' hg'
      simp only [List.mem_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := hg'
      exact hall g0 hg0
    · intro g' hg'
      simp at hg'
    · simp [Circuit.size]
    · simp [Circuit.size]
    · intro x hx
      rw [eval_eq, eval_eq]
      exact sim (r1 n) C.gates x (x ++ [_])
        (by intro t i; simp only [r1, List.length_append, List.length_singleton, hx]; split_ifs <;> omega)
        (by
          intro i
          simp only [r1]
          split_ifs with h
          · rw [getD_snoc, if_neg (by omega)]
          · rw [getD_big x i (by omega), getD_big _ _ (by simp; omega)]) C.output
