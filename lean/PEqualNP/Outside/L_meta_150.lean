import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_150

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

theorem getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_big (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

-- AND and OR gates are monotone: a wire true on the smaller run is true on the larger
theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

-- the three runs: a is the run on the single point r, b on the single point w, c on both
def Agree (Wa Wb Wc : List Bool) : Prop :=
  ∀ i, Wa.getD i false = false → Wc.getD i false = Wb.getD i false

-- either some AND gate reads a wire that is already true on the single point r,
-- or every wire false at r takes the same value with and without r
theorem find : ∀ (gs : List Gate) (Wa Wb Wc : List Bool), Wb.length = Wa.length →
    Wc.length = Wa.length → (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    Agree Wa Wb Wc →
    (∃ (pre : List Gate) (g : Gate) (post : List Gate), gs = pre ++ g :: post ∧
        g.op = GateOp.and ∧ ∃ p ∈ g.inputs, (pre.foldl stp Wa).getD p false = true) ∨
      Agree (gs.foldl stp Wa) (gs.foldl stp Wb) (gs.foldl stp Wc) := by
  intro gs
  induction gs with
  | nil => intro Wa Wb Wc _ _ _ H; right; simpa using H
  | cons g gs ih =>
    intro Wa Wb Wc hb hc hop H
    by_cases hg : g.op = GateOp.and ∧ ∃ p ∈ g.inputs, Wa.getD p false = true
    · left
      exact ⟨[], g, gs, rfl, hg.1, by simpa using hg.2⟩
    · have hnew : Agree (stp Wa g) (stp Wb g) (stp Wc g) := by
        intro i
        simp only [stp, getD_snoc, hb, hc]
        split_ifs
        · intro hva
          have hall : ∀ k ∈ g.inputs, Wa.getD k false = false := by
            intro k hk
            by_contra hne
            have hkt : Wa.getD k false = true := by
              cases hh : Wa.getD k false
              · exact absurd hh hne
              · rfl
            rcases hop g List.mem_cons_self with ha | ho
            · exact hg ⟨ha, k, hk, hkt⟩
            · have : g.op.eval (g.inputs.map fun i => Wa.getD i false) = true :=
                (ev_or g _ ho).2 ⟨k, hk, hkt⟩
              rw [this] at hva
              exact Bool.noConfusion hva
          have e : (g.inputs.map fun i => Wc.getD i false) = (g.inputs.map fun i => Wb.getD i false) := by
            apply List.map_congr_left
            intro k hk
            exact H k (hall k hk)
          rw [e]
        · exact H i
      rcases ih (stp Wa g) (stp Wb g) (stp Wc g) (by simp [stp, hb]) (by simp [stp, hc])
        (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) hnew with ⟨pre, g1, post, e, ha, p, hp, hv⟩ | h
      · left
        exact ⟨g :: pre, g1, post, by rw [e]; rfl, ha, p, hp, by simpa using hv⟩
      · right
        simpa using h

-- the sandwich: the middle run reads its wires through the renaming
def Inv (ρ : ℕ → ℕ) (W1 W' W2 : List Bool) : Prop :=
  ∀ i, (W1.getD i false = true → W'.getD (ρ i) false = true) ∧
    (W'.getD (ρ i) false = true → W2.getD i false = true)

theorem inv_snoc (ρ : ℕ → ℕ) (n BIG : ℕ) (hρ : ∀ i, ρ i = i ∨ (i < n ∧ ρ i = BIG))
    (W1 W' W2 : List Bool) (l1 : W1.length = W'.length) (l2 : W2.length = W'.length)
    (hn : n ≤ W'.length) (hB : W'.length < BIG) (v1 v' v2 : Bool)
    (h1 : v1 = true → v' = true) (h2 : v' = true → v2 = true) (H : Inv ρ W1 W' W2) :
    Inv ρ (W1 ++ [v1]) (W' ++ [v']) (W2 ++ [v2]) := by
  intro i
  simp only [getD_snoc, l1, l2]
  rcases hρ i with e | ⟨hi, e⟩
  · rw [e]
    split_ifs
    · exact ⟨h1, h2⟩
    · have := H i
      rwa [e] at this
  · rw [e, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have := H i
    rwa [e] at this

def rel (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

theorem rel_val (ρ : ℕ → ℕ) (g : Gate) (W : List Bool) :
    (rel ρ g).op.eval ((rel ρ g).inputs.map fun i => W.getD i false) =
      g.op.eval (g.inputs.map fun i => W.getD (ρ i) false) := by
  simp [rel, List.map_map, Function.comp_def]

theorem sim (ρ : ℕ → ℕ) (n BIG : ℕ) (hρ : ∀ i, ρ i = i ∨ (i < n ∧ ρ i = BIG)) :
    ∀ (gs : List Gate) (W1 W' W2 : List Bool), W1.length = W'.length → W2.length = W'.length →
    n ≤ W'.length → W'.length + gs.length ≤ BIG →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Inv ρ W1 W' W2 →
    Inv ρ (gs.foldl stp W1) ((gs.map (rel ρ)).foldl stp W') (gs.foldl stp W2) := by
  intro gs
  induction gs with
  | nil => intro W1 W' W2 _ _ _ _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W' W2 l1 l2 hn hB hop H
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons]
    have hlen : W'.length + 1 + gs.length ≤ BIG := by
      simp only [List.length_cons] at hB
      omega
    apply ih (stp W1 g) (stp W' (rel ρ g)) (stp W2 g) (by simp [stp, l1]) (by simp [stp, l2])
      (by simp [stp]; omega) (by simp [stp]; omega)
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    unfold stp
    rw [rel_val]
    apply inv_snoc ρ n BIG hρ W1 W' W2 l1 l2 hn (by omega) _ _ _ _ _ H
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact (H k).1 (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, (H k).1 h⟩
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact (H k).2 (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, (H k).2 h⟩

theorem ev_one (W : List Bool) (k : ℕ) :
    (⟨GateOp.or, [k]⟩ : Gate).op.eval ((⟨GateOp.or, [k]⟩ : Gate).inputs.map fun i => W.getD i false) =
      W.getD k false := by
  simp [GateOp.eval]

theorem two (l : List ℕ) (h : l.length ≤ 2) (p q : ℕ) (hp : p ∈ l) (hq : q ∈ l) (hne : p ≠ q) :
    ∀ i ∈ l, i = p ∨ i = q := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hp
  · simp at hp hq
    omega
  · intro i hi
    simp at hp hq hi
    omega
  · simp at h

-- which gate sits at each place of the rebuilt list
theorem at_place (ρ : ℕ → ℕ) (pre post : List Gate) (g G' : Gate) (k : ℕ) (g' : Gate)
    (h : (pre.map (rel ρ) ++ G' :: post.map (rel ρ))[k]? = some g') :
    (k = pre.length ∧ g' = G') ∨
      (k ≠ pre.length ∧ ∃ g0, (pre ++ g :: post)[k]? = some g0 ∧ g'.op = g0.op) := by
  rcases lt_trichotomy k pre.length with hk | hk | hk
  · right
    rw [List.getElem?_append_left (by simpa using hk)] at h
    rw [List.getElem?_map] at h
    rw [List.getElem?_append_left hk]
    cases hh : pre[k]? with
    | none => rw [hh] at h; simp at h
    | some g0 =>
      rw [hh] at h
      simp at h
      exact ⟨by omega, g0, rfl, by rw [← h]; rfl⟩
  · left
    subst hk
    have : (pre.map (rel ρ) ++ G' :: post.map (rel ρ))[pre.length]? = some G' := by
      rw [List.getElem?_append_right (by simp)]
      simp
    rw [this] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · right
    obtain ⟨d, rfl⟩ : ∃ d, k = pre.length + 1 + d := ⟨k - pre.length - 1, by omega⟩
    rw [List.getElem?_append_right (by simp; omega)] at h
    have e1 : pre.length + 1 + d - (pre.map (rel ρ)).length = d + 1 := by simp; omega
    rw [e1, List.getElem?_cons_succ, List.getElem?_map] at h
    rw [List.getElem?_append_right (by omega)]
    have e2 : pre.length + 1 + d - pre.length = d + 1 := by omega
    rw [e2, List.getElem?_cons_succ]
    cases hh : post[d]? with
    | none => rw [hh] at h; simp at h
    | some g0 =>
      rw [hh] at h
      simp at h
      exact ⟨by omega, g0, rfl, by rw [← h]; rfl⟩

end PEqualNP.Outside.L_meta_150

open PEqualNP.Outside.L_meta_150 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_150 : ∀ (n a : ℕ) (G : SimpleGraph (Fin n)) (r : Fin n), (∃ w : Fin n, G.Adj r w) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ a + 1 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ a ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ u ≠ r ∧ v ≠ r ∧ ¬ G.Adj r u ∧ ¬ G.Adj r v ∧ x u = true ∧ x v = true) := by
  classical
  rintro n a G r ⟨w, hrw⟩ ⟨C, hM, ⟨A, hA, hAnd⟩, hC⟩
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hM g hg).1
  have hwr : w ≠ r := fun e => G.loopless.irrefl r (by rw [e] at hrw; exact hrw)
  -- an AND gate reading a wire that is true on the single point r
  have hsplit : ∃ (pre : List Gate) (g : Gate) (post : List Gate), C.gates = pre ++ g :: post ∧
      g.op = GateOp.and ∧ ∃ p ∈ g.inputs,
        (pre.foldl stp (List.ofFn (fun i : Fin n => decide (i = r)))).getD p false = true := by
    rcases find C.gates (List.ofFn (fun i : Fin n => decide (i = r)))
      (List.ofFn (fun i : Fin n => decide (i = w)))
      (List.ofFn (fun i : Fin n => decide (i = r) || decide (i = w))) (by simp) (by simp) hop
      (by
        intro i hi
        by_cases hin : i < n
        · rw [getD_ofFn _ i hin] at hi
          rw [getD_ofFn _ i hin, getD_ofFn _ i hin]
          simp at hi
          simp [hi]
        · rw [getD_big _ i (by simp; omega), getD_big _ i (by simp; omega)]) with h | h
    · exact h
    · exfalso
      have hr0 : C.eval (List.ofFn (fun i : Fin n => decide (i = r))) = false := by
        by_contra hne
        have ht : C.eval (List.ofFn (fun i : Fin n => decide (i = r))) = true := by simpa using hne
        obtain ⟨u, v, huv, hu, hv⟩ := (hC _).1 ht
        simp at hu hv
        rw [hu, hv] at huv
        exact G.loopless.irrefl r huv
      have hw0 : C.eval (List.ofFn (fun i : Fin n => decide (i = w))) = false := by
        by_contra hne
        have ht : C.eval (List.ofFn (fun i : Fin n => decide (i = w))) = true := by simpa using hne
        obtain ⟨u, v, huv, hu, hv⟩ := (hC _).1 ht
        simp at hu hv
        rw [hu, hv] at huv
        exact G.loopless.irrefl w huv
      have hrw1 : C.eval (List.ofFn (fun i : Fin n => decide (i = r) || decide (i = w))) = true :=
        (hC _).2 ⟨r, w, hrw, by simp, by simp⟩
      rw [eval_eq] at hr0 hw0 hrw1
      have := h C.output hr0
      rw [hrw1, hw0] at this
      exact Bool.noConfusion this
  obtain ⟨pre, g, post, hgs, hga, p, hp, hpv⟩ := hsplit
  have hglen : g.inputs.length ≤ 2 := (hM g (by rw [hgs]; simp)).2
  -- the renaming: the inputs at r and at its neighbours are read as a missing wire
  let BIG : ℕ := n + C.gates.length
  let ρ : ℕ → ℕ := fun i => if h : i < n then
    (if (⟨i, h⟩ : Fin n) = r ∨ G.Adj r ⟨i, h⟩ then BIG else i) else i
  have hρ : ∀ i, ρ i = i ∨ (i < n ∧ ρ i = BIG) := by
    intro i
    by_cases h : i < n
    · by_cases h2 : (⟨i, h⟩ : Fin n) = r ∨ G.Adj r ⟨i, h⟩
      · right
        exact ⟨h, by simp [ρ, h, h2]⟩
      · left
        simp [ρ, h, h2]
    · left
      simp [ρ, h]
  let Wa : List Bool := pre.foldl stp (List.ofFn (fun i : Fin n => decide (i = r)))
  -- the wire the replaced gate keeps
  let c : ℕ := if h : ∃ q ∈ g.inputs, Wa.getD q false = false then h.choose else p
  let G' : Gate := ⟨GateOp.or, [ρ c]⟩
  refine ⟨⟨pre.map (rel ρ) ++ G' :: post.map (rel ρ), ρ C.output⟩, ?_, ⟨A.erase pre.length, ?_, ?_⟩, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hg'
    rcases hg' with ⟨g0, hg0, rfl⟩ | rfl | ⟨g0, hg0, rfl⟩
    · have := hM g0 (by rw [hgs]; simp [hg0])
      exact ⟨this.1, by simpa [rel] using this.2⟩
    · exact ⟨by simp [G'], by simp [G']⟩
    · have := hM g0 (by rw [hgs]; simp [hg0])
      exact ⟨this.1, by simpa [rel] using this.2⟩
  · have hin : pre.length ∈ A := hAnd pre.length g (by rw [hgs]; simp) hga
    rw [Finset.card_erase_of_mem hin]
    omega
  · intro j g' hj hand
    rcases at_place ρ pre post g G' j g' hj with ⟨_, e⟩ | ⟨hne, g0, hg0, hopeq⟩
    · rw [e] at hand
      simp [G'] at hand
    · rw [Finset.mem_erase]
      exact ⟨hne, hAnd j g0 (by rw [hgs]; exact hg0) (by rw [← hopeq]; exact hand)⟩
  · intro x
    -- y: x with r and its neighbours false; z: y with r true
    let y : Fin n → Bool := fun i => if i = r ∨ G.Adj r i then false else x i
    let z : Fin n → Bool := fun i => if i = r then true else y i
    have hpre : ∀ g0 ∈ pre, g0.op = GateOp.and ∨ g0.op = GateOp.or :=
      fun g0 h0 => hop g0 (by rw [hgs]; simp [h0])
    have hpost : ∀ g0 ∈ post, g0.op = GateOp.and ∨ g0.op = GateOp.or :=
      fun g0 h0 => hop g0 (by rw [hgs]; simp [h0])
    have hlenC : C.gates.length = pre.length + post.length + 1 := by rw [hgs]; simp; omega
    have h0 : Inv ρ (List.ofFn y) (List.ofFn x) (List.ofFn z) := by
      intro i
      by_cases h : i < n
      · by_cases h2 : (⟨i, h⟩ : Fin n) = r ∨ G.Adj r ⟨i, h⟩
        · have e : ρ i = BIG := by simp [ρ, h, h2]
          have hy0 : y ⟨i, h⟩ = false := if_pos h2
          rw [e, getD_big (List.ofFn x) BIG (by simp [BIG]), getD_ofFn _ i h, hy0]
          simp
        · have e : ρ i = i := by simp [ρ, h, h2]
          have h3 : (⟨i, h⟩ : Fin n) ≠ r := fun e => h2 (Or.inl e)
          have hy1 : y ⟨i, h⟩ = x ⟨i, h⟩ := if_neg h2
          have hz1 : z ⟨i, h⟩ = y ⟨i, h⟩ := if_neg h3
          rw [e, getD_ofFn _ i h, getD_ofFn _ i h, getD_ofFn _ i h, hz1, hy1]
          exact ⟨id, id⟩
      · have e : ρ i = i := by simp [ρ, h]
        rw [e, getD_big _ i (by simp; omega), getD_big _ i (by simp; omega),
          getD_big _ i (by simp; omega)]
        simp
    have h1 := sim ρ n BIG hρ pre (List.ofFn y) (List.ofFn x) (List.ofFn z) (by simp) (by simp)
      (by simp) (by simp [BIG]; omega) hpre h0
    -- wires true on the single point r are true on z
    have hgood : ∀ i, Wa.getD i false = true → (pre.foldl stp (List.ofFn z)).getD i false = true := by
      apply mono pre _ _ (by simp) hpre
      intro i
      by_cases h : i < n
      · rw [getD_ofFn _ i h, getD_ofFn _ i h]
        intro hi
        simp at hi
        simp [z, hi]
      · rw [getD_big _ i (by simp; omega)]
        simp
    have hL1 : (pre.foldl stp (List.ofFn y)).length = n + pre.length := by rw [foldl_length]; simp
    have hL' : ((pre.map (rel ρ)).foldl stp (List.ofFn x)).length = n + pre.length := by
      rw [foldl_length]; simp
    have hL2 : (pre.foldl stp (List.ofFn z)).length = n + pre.length := by rw [foldl_length]; simp
    have h2 : Inv ρ (stp (pre.foldl stp (List.ofFn y)) g)
        (stp ((pre.map (rel ρ)).foldl stp (List.ofFn x)) G')
        (stp (pre.foldl stp (List.ofFn z)) g) := by
      unfold stp
      apply inv_snoc ρ n BIG hρ _ _ _ (by rw [hL1, hL']) (by rw [hL2, hL']) (by rw [hL']; omega)
        (by rw [hL']; simp only [BIG]; omega) _ _ _ _ _ h1
      · rw [ev_and g _ hga]
        intro hall
        have hc : c ∈ g.inputs := by
          by_cases hq : ∃ q ∈ g.inputs, Wa.getD q false = false
          · simp only [c, dif_pos hq]
            exact hq.choose_spec.1
          · simp only [c, dif_neg hq]
            exact hp
        exact (ev_one _ (ρ c)).trans ((h1 c).1 (hall c hc))
      · rw [ev_and g _ hga]
        intro hv
        have hv' : ((pre.map (rel ρ)).foldl stp (List.ofFn x)).getD (ρ c) false = true :=
          (ev_one _ (ρ c)).symm.trans hv
        have hcz := (h1 c).2 hv'
        by_cases hq : ∃ q ∈ g.inputs, Wa.getD q false = false
        · have hce : c = hq.choose := by simp only [c, dif_pos hq]
          have hcq := hq.choose_spec
          rw [← hce] at hcq
          have hpc : p ≠ c := by
            intro e
            rw [e] at hpv
            rw [hcq.2] at hpv
            exact Bool.noConfusion hpv
          intro k hk
          rcases two g.inputs hglen p c hp hcq.1 hpc k hk with e | e
          · rw [e]
            exact hgood p hpv
          · rw [e]
            exact hcz
        · intro k hk
          apply hgood
          by_contra hne
          exact hq ⟨k, hk, by simpa using hne⟩
    have h3 := sim ρ n BIG hρ post _ _ _ (by simp [stp, hL1, hL']) (by simp [stp, hL2, hL'])
      (by simp [stp, hL']; omega) (by simp [stp, hL']; simp only [BIG]; omega) hpost h2
    have hy : C.eval (List.ofFn y) = (post.foldl stp (stp (pre.foldl stp (List.ofFn y)) g)).getD C.output false := by
      rw [eval_eq, hgs, List.foldl_append, List.foldl_cons]
    have hz : C.eval (List.ofFn z) = (post.foldl stp (stp (pre.foldl stp (List.ofFn z)) g)).getD C.output false := by
      rw [eval_eq, hgs, List.foldl_append, List.foldl_cons]
    have hx : Circuit.eval ⟨pre.map (rel ρ) ++ G' :: post.map (rel ρ), ρ C.output⟩ (List.ofFn x) =
        ((post.map (rel ρ)).foldl stp (stp ((pre.map (rel ρ)).foldl stp (List.ofFn x)) G')).getD (ρ C.output) false := by
      rw [eval_eq, List.foldl_append, List.foldl_cons]
    rw [hx]
    constructor
    · intro ht
      have := (h3 C.output).2 ht
      rw [← hz] at this
      obtain ⟨u, v, huv, hu, hv⟩ := (hC z).1 this
      have key : ∀ t : Fin n, z t = true → t ≠ r → (¬ G.Adj r t ∧ x t = true) := by
        intro t ht hne
        simp only [z, if_neg hne, y] at ht
        by_cases hb : t = r ∨ G.Adj r t
        · rw [if_pos hb] at ht
          exact Bool.noConfusion ht
        · rw [if_neg hb] at ht
          exact ⟨fun h => hb (Or.inr h), ht⟩
      have hur : u ≠ r := by
        intro e
        rw [e] at huv
        have hvr : v ≠ r := fun e2 => G.loopless.irrefl r (by rw [e2] at huv; exact huv)
        exact (key v hv hvr).1 huv
      have hvr : v ≠ r := by
        intro e
        rw [e] at huv
        exact (key u hu hur).1 huv.symm
      exact ⟨u, v, huv, hur, hvr, (key u hu hur).1, (key v hv hvr).1, (key u hu hur).2, (key v hv hvr).2⟩
    · rintro ⟨u, v, huv, hur, hvr, hnu, hnv, hu, hv⟩
      apply (h3 C.output).1
      rw [← hy]
      apply (hC y).2
      refine ⟨u, v, huv, ?_, ?_⟩
      · simp [y, hur, hnu, hu]
      · simp [y, hvr, hnv, hv]
