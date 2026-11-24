import Mathlib
import PEqualNP.Defs

-- For a line through the point z, an OR gate that is false at the complement of another line
-- missing z has no input true at the single point z (monotonicity), so its two witnesses lie
-- among the other three points of the line. Each gate of I joins two classes not yet joined by
-- the earlier gates of I; three such joins on three points are impossible.

namespace PEqualNP.Outside.L_meta_1612

open PEqualNP.CircuitLowerBounds

-- The wires of the first t gates on input x.
def W {n : ℕ} (gates : List Gate) (t : ℕ) (x : Fin n → Bool) : List Bool :=
  Circuit.wires ⟨gates.take t, 0⟩ (List.ofFn x)

theorem W_zero {n : ℕ} (gates : List Gate) (x : Fin n → Bool) : W gates 0 x = List.ofFn x := by
  simp [W, Circuit.wires]

theorem W_succ {n : ℕ} (gates : List Gate) (t : ℕ) (ht : t < gates.length)
    (x : Fin n → Bool) :
    W gates (t + 1) x = W gates t x ++
      [gates[t].op.eval (gates[t].inputs.map fun k => (W gates t x).getD k false)] := by
  unfold W Circuit.wires
  rw [List.take_add_one, List.getElem?_eq_getElem ht]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem W_length {n : ℕ} (gates : List Gate) (x : Fin n → Bool) :
    ∀ t : ℕ, t ≤ gates.length → (W gates t x).length = n + t := by
  intro t
  induction t with
  | zero => intro _; simp [W_zero]
  | succ t ih =>
    intro ht
    rw [W_succ gates t (by omega), List.length_append, ih (by omega)]
    simp
    omega

theorem W_prefix {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (t : ℕ) :
    ∀ u : ℕ, t + u ≤ gates.length → W gates t x <+: W gates (t + u) x := by
  intro u
  induction u with
  | zero => intro _; exact List.prefix_refl _
  | succ u ih =>
    intro h
    rw [← Nat.add_assoc, W_succ gates (t + u) (by omega)]
    exact (ih (by omega)).trans (List.prefix_append _ _)

theorem getD_of_prefix {l1 l2 : List Bool} (h : l1 <+: l2) (i : ℕ) (hi : i < l1.length) :
    l1.getD i false = l2.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc (l : List Bool) (b : Bool) (k : ℕ) :
    (l ++ [b]).getD k false =
      if k < l.length then l.getD k false else if k = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    (List.ofFn x).getD k false = if h : k < n then x ⟨k, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

theorem all_mono (ks : List ℕ) (f g : ℕ → Bool) (hfg : ∀ k, f k = true → g k = true) :
    (ks.map f).all id = true → (ks.map g).all id = true := by
  simp only [List.all_eq_true, List.mem_map, id]
  rintro h b ⟨k, hk, rfl⟩
  exact hfg k (h (f k) ⟨k, hk, rfl⟩)

theorem any_mono (ks : List ℕ) (f g : ℕ → Bool) (hfg : ∀ k, f k = true → g k = true) :
    (ks.map f).any id = true → (ks.map g).any id = true := by
  simp only [List.any_eq_true, List.mem_map, id]
  rintro ⟨b, ⟨k, hk, rfl⟩, hb⟩
  exact ⟨g k, ⟨k, hk, rfl⟩, hfg k hb⟩

theorem W_mono {n : ℕ} (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ t : ℕ, t ≤ gates.length →
      ∀ k, (W gates t x).getD k false = true → (W gates t y).getD k false = true := by
  intro t
  induction t with
  | zero =>
    intro _ k hk
    rw [W_zero, ofFn_getD] at hk ⊢
    split_ifs at hk ⊢ with h
    exact hxy _ hk
  | succ t ih =>
    intro ht k hk
    have htl : t < gates.length := by omega
    have ih' := ih (by omega)
    rw [W_succ gates t htl, getD_snoc] at hk ⊢
    rw [W_length gates x t (by omega)] at hk
    rw [W_length gates y t (by omega)]
    split_ifs at hk ⊢ with h1 h2
    · exact ih' k hk
    · rcases hops _ (List.getElem_mem htl) with hop | hop
      · rw [hop] at hk ⊢
        exact all_mono _ _ _ ih' hk
      · rw [hop] at hk ⊢
        exact any_mono _ _ _ ih' hk

theorem eval_eq {n : ℕ} (gates : List Gate) (w : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = (W gates gates.length x).getD w false := by
  simp [Circuit.eval, W, Circuit.wires]

theorem eval_mono {n : ℕ} (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true → Circuit.eval ⟨gates, w⟩ (List.ofFn y) = true := by
  rw [eval_eq, eval_eq]
  exact W_mono gates hops x y hxy gates.length le_rfl w

-- The value of an OR gate reading two earlier wires.
theorem eval_or {n : ℕ} (gates : List Gate) (g : Fin gates.length)
    (hop : (gates.get g).op = GateOp.or) (a b : ℕ) (hin : (gates.get g).inputs = [a, b])
    (ha : a < n + g) (hb : b < n + g) (x : Fin n → Bool) :
    Circuit.eval ⟨gates, n + g⟩ (List.ofFn x) =
      (Circuit.eval ⟨gates, a⟩ (List.ofFn x) || Circuit.eval ⟨gates, b⟩ (List.ofFn x)) := by
  rw [eval_eq, eval_eq, eval_eq]
  have hg := g.isLt
  have hpre1 := W_prefix gates x (g.val + 1) (gates.length - (g.val + 1)) (by omega)
  rw [show g.val + 1 + (gates.length - (g.val + 1)) = gates.length by omega] at hpre1
  have hpre0 := W_prefix gates x g.val (gates.length - g.val) (by omega)
  rw [show g.val + (gates.length - g.val) = gates.length by omega] at hpre0
  have hlen0 := W_length gates x g.val (by omega)
  have hlen1 := W_length gates x (g.val + 1) (by omega)
  rw [← getD_of_prefix hpre1 (n + g) (by omega), ← getD_of_prefix hpre0 a (by omega),
    ← getD_of_prefix hpre0 b (by omega), W_succ gates g.val hg, getD_snoc, hlen0]
  simp only [lt_irrefl, ite_false, ite_true]
  have h1 : gates[g.val] = gates.get g := by simp
  rw [h1, hop, hin]
  simp [GateOp.eval]

-- Three joins on three points: impossible.
theorem core : ∀ (i1 i1' i2 i2' i3 i3' : Fin 3) (f2 f3 : Fin 3 → Bool), i1 ≠ i1' →
    f2 i2 = true → f2 i2' = false → f2 i1 = f2 i1' →
    f3 i3 = true → f3 i3' = false → f3 i1 = f3 i1' → f3 i2 = f3 i2' → False := by
  decide

-- The condition on a gate of I, for the line Lx and the inputs Tx.
def Cond (gates : List Gate) (Lx : Finset (Fin 13)) (Tx : Fin 13 → Fin 13 → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧
    Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lx))) = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ Lx, ∃ r' ∈ Lx,
      Circuit.eval ⟨gates, w1⟩ (List.ofFn (Tx r)) = true ∧
      Circuit.eval ⟨gates, w2⟩ (List.ofFn (Tx r')) = true ∧
      ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g →
        (gates.get i).op = GateOp.or →
        Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Lx))) =
          false →
        ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ Lx, ∀ y' ∈ Lx,
        (Circuit.eval ⟨gates, a⟩ (List.ofFn (Tx y)) = true ∨
          Circuit.eval ⟨gates, b⟩ (List.ofFn (Tx y)) = true) →
        (Circuit.eval ⟨gates, a⟩ (List.ofFn (Tx y')) = true ∨
          Circuit.eval ⟨gates, b⟩ (List.ofFn (Tx y')) = true) → (y ∈ X ↔ y' ∈ X))

-- A witness of a gate of I is not the point z.
theorem witness_ne (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (Tx : Fin 13 → Fin 13 → Bool) (z : Fin 13) (hz : Tx z = fun v : Fin 13 => decide (v = z))
    (g : Fin gates.length) (hop : (gates.get g).op = GateOp.or) (w1 w2 : ℕ)
    (hin : (gates.get g).inputs = [w1, w2]) (Ly : Finset (Fin 13)) (hzy : z ∉ Ly)
    (hdead : Circuit.eval ⟨gates, 13 + (g : ℕ)⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ Ly))) = false)
    (w : ℕ) (hw : w = w1 ∨ w = w2) (r : Fin 13)
    (hr : Circuit.eval ⟨gates, w⟩ (List.ofFn (Tx r)) = true) : r ≠ z := by
  rintro rfl
  have h1 := hwf g w1 (by rw [hin]; simp)
  have h2 := hwf g w2 (by rw [hin]; simp)
  have hle : ∀ p, Tx r p = true → (decide (p ∉ Ly)) = true := by
    intro p hp
    rw [hz] at hp
    have : p = r := by simpa using hp
    subst this
    simpa using hzy
  have hm := eval_mono gates hops (Tx r) (fun v : Fin 13 => decide (v ∉ Ly)) hle w hr
  rw [eval_or gates g hop w1 w2 hin h1 h2] at hdead
  rcases hw with rfl | rfl
  · rw [hm] at hdead
    simp at hdead
  · rw [hm] at hdead
    simp at hdead

theorem tri (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (Lx : Finset (Fin 13)) (Tx : Fin 13 → Fin 13 → Bool) (z : Fin 13)
    (hz : Tx z = fun v : Fin 13 => decide (v = z))
    (pa pb pc : Fin 13) (hab : pa ≠ pb) (hac : pa ≠ pc) (hbc : pb ≠ pc)
    (hQ : ∀ r ∈ Lx, r ≠ z → r = pa ∨ r = pb ∨ r = pc)
    (g1 g2 g3 : Fin gates.length)
    (d1 : ∃ Ly : Finset (Fin 13), z ∉ Ly ∧ Circuit.eval ⟨gates, 13 + (g1 : ℕ)⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ Ly))) = false)
    (d2 : ∃ Ly : Finset (Fin 13), z ∉ Ly ∧ Circuit.eval ⟨gates, 13 + (g2 : ℕ)⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ Ly))) = false)
    (d3 : ∃ Ly : Finset (Fin 13), z ∉ Ly ∧ Circuit.eval ⟨gates, 13 + (g3 : ℕ)⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ Ly))) = false)
    (c1 : Cond gates Lx Tx g1) (c2 : Cond gates Lx Tx g2)
    (c3 : Cond gates Lx Tx g3) (h12 : g1 < g2) (h23 : g2 < g3) : False := by
  obtain ⟨Ly1, hz1, hd1⟩ := d1
  obtain ⟨Ly2, hz2, hd2⟩ := d2
  obtain ⟨Ly3, hz3, hd3⟩ := d3
  obtain ⟨hop1, hdx1, a1, b1, hin1, r1, hr1, s1, hs1, e1, f1, X1, hX1, hY1, _⟩ := c1
  obtain ⟨hop2, hdx2, a2, b2, hin2, r2, hr2, s2, hs2, e2, f2, X2, hX2, hY2, hcl2⟩ := c2
  obtain ⟨hop3, hdx3, a3, b3, hin3, r3, hr3, s3, hs3, e3, f3, X3, hX3, hY3, hcl3⟩ := c3
  have q1 := hQ r1 hr1 (witness_ne gates hops hwf Tx z hz g1 hop1 a1 b1 hin1 Ly1 hz1 hd1 a1
    (Or.inl rfl) r1 e1)
  have q1' := hQ s1 hs1 (witness_ne gates hops hwf Tx z hz g1 hop1 a1 b1 hin1 Ly1 hz1 hd1 b1
    (Or.inr rfl) s1 f1)
  have q2 := hQ r2 hr2 (witness_ne gates hops hwf Tx z hz g2 hop2 a2 b2 hin2 Ly2 hz2 hd2 a2
    (Or.inl rfl) r2 e2)
  have q2' := hQ s2 hs2 (witness_ne gates hops hwf Tx z hz g2 hop2 a2 b2 hin2 Ly2 hz2 hd2 b2
    (Or.inr rfl) s2 f2)
  have q3 := hQ r3 hr3 (witness_ne gates hops hwf Tx z hz g3 hop3 a3 b3 hin3 Ly3 hz3 hd3 a3
    (Or.inl rfl) r3 e3)
  have q3' := hQ s3 hs3 (witness_ne gates hops hwf Tx z hz g3 hop3 a3 b3 hin3 Ly3 hz3 hd3 b3
    (Or.inr rfl) s3 f3)
  have hne1 : r1 ≠ s1 := fun h => hY1 (h ▸ hX1)
  have k21 := hcl2 g1 h12 hop1 hdx1 a1 b1 hin1 r1 hr1 s1 hs1 (Or.inl e1) (Or.inr f1)
  have k31 := hcl3 g1 (lt_trans h12 h23) hop1 hdx1 a1 b1 hin1 r1 hr1 s1 hs1 (Or.inl e1)
    (Or.inr f1)
  have k32 := hcl3 g2 h23 hop2 hdx2 a2 b2 hin2 r2 hr2 s2 hs2 (Or.inl e2) (Or.inr f2)
  let pt : Fin 3 → Fin 13 := ![pa, pb, pc]
  let idx : Fin 13 → Fin 3 := fun r => if r = pa then 0 else if r = pb then 1 else 2
  have hpt : ∀ r, (r = pa ∨ r = pb ∨ r = pc) → pt (idx r) = r := by
    intro r hr
    rcases hr with rfl | rfl | rfl
    · simp [pt, idx]
    · simp [pt, idx, Ne.symm hab]
    · simp [pt, idx, Ne.symm hac, Ne.symm hbc]
  let F2 : Fin 3 → Bool := fun i => decide (pt i ∈ X2)
  let F3 : Fin 3 → Bool := fun i => decide (pt i ∈ X3)
  have hF2 : ∀ r, (r = pa ∨ r = pb ∨ r = pc) → F2 (idx r) = decide (r ∈ X2) := by
    intro r hr
    simp only [F2, hpt r hr]
  have hF3 : ∀ r, (r = pa ∨ r = pb ∨ r = pc) → F3 (idx r) = decide (r ∈ X3) := by
    intro r hr
    simp only [F3, hpt r hr]
  apply core (idx r1) (idx s1) (idx r2) (idx s2) (idx r3) (idx s3) F2 F3
  · intro h
    apply hne1
    rw [← hpt r1 q1, ← hpt s1 q1', h]
  · rw [hF2 r2 q2]; simpa using hX2
  · rw [hF2 s2 q2']; simpa using hY2
  · rw [hF2 r1 q1, hF2 s1 q1']; simp [k21]
  · rw [hF3 r3 q3]; simpa using hX3
  · rw [hF3 s3 q3']; simpa using hY3
  · rw [hF3 r1 q1, hF3 s1 q1']; simp [k31]
  · rw [hF3 r2 q2, hF3 s2 q2']; simp [k32]

theorem gen (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (Lx : Finset (Fin 13)) (Tx : Fin 13 → Fin 13 → Bool) (z : Fin 13)
    (hz : Tx z = fun v : Fin 13 => decide (v = z))
    (pa pb pc : Fin 13) (hab : pa ≠ pb) (hac : pa ≠ pc) (hbc : pb ≠ pc)
    (hQ : ∀ r ∈ Lx, r ≠ z → r = pa ∨ r = pb ∨ r = pc)
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I, Cond gates Lx Tx g ∧ ∃ Ly : Finset (Fin 13), z ∉ Ly ∧
      Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ Ly))) = false) :
    I.card ≤ 2 := by
  by_contra hc
  have h3 : 2 < I.card := by omega
  obtain ⟨a, b, c, ha, hb, hc', hab', hac', hbc'⟩ := Finset.two_lt_card_iff.1 h3
  have hT : ∀ g1 ∈ I, ∀ g2 ∈ I, ∀ g3 ∈ I, g1 < g2 → g2 < g3 → False := by
    intro g1 h1 g2 h2 g3 h3 l12 l23
    exact tri gates hops hwf Lx Tx z hz pa pb pc hab hac hbc hQ g1 g2 g3 (hI _ h1).2 (hI _ h2).2
      (hI _ h3).2 (hI _ h1).1 (hI _ h2).1 (hI _ h3).1 l12 l23
  rcases lt_trichotomy a b with h | h | h <;> rcases lt_trichotomy b c with h' | h' | h' <;>
    rcases lt_trichotomy a c with h'' | h'' | h''
  all_goals first
    | exact hab' (by assumption)
    | exact hac' (by assumption)
    | exact hbc' (by assumption)
    | exact hT _ ha _ hb _ hc' h h'
    | exact hT _ ha _ hc' _ hb h'' (by assumption)
    | exact hT _ hb _ ha _ hc' h h''
    | exact hT _ hb _ hc' _ ha h' h''
    | exact hT _ hc' _ ha _ hb h'' h
    | exact hT _ hc' _ hb _ ha h' h

end PEqualNP.Outside.L_meta_1612

open PEqualNP.Outside.L_meta_1612

theorem PEqualNP.Outside.L_meta_1612 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), T l 0 = (fun v : Fin 13 => decide (v = 0))) → (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), T m 1 = (fun v : Fin 13 => decide (v = 1))) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ)) →
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (∀ X : Finset (Fin 13), (∀ i : Fin gates.length, True → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X)) → ∀ y ∈ L l, ∀ y' ∈ L l, (y ∈ X ↔ y' ∈ X)) →
      ∀ I : Finset (Fin gates.length), (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X))) ∧
        ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false) → I.card ≤ 2) ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (∀ X : Finset (Fin 13), (∀ i : Fin gates.length, True → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X)) → ∀ y ∈ L m, ∀ y' ∈ L m, (y ∈ X ↔ y' ∈ X)) →
      ∀ I : Finset (Fin gates.length), (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T m r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T m r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X))) ∧
        ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false) → I.card ≤ 2) := by
  intro L hL T gates _ hT0 hT1 hops0 hwf
  have hops : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g h => (hops0 g h).1
  constructor
  · intro l hl _ I hI
    have hz : T l 0 = fun v : Fin 13 => decide (v = 0) := hT0 l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · have hQ : ∀ r ∈ L 4, r ≠ 0 → r = 4 ∨ r = 5 ∨ r = 7 := by
        intro r hr hrz
        rw [hL] at hr
        have key : ∀ r : Fin 13, r ∈ ({4, 4 + 1, 4 + 3, 4 + 9} : Finset (Fin 13)) → r ≠ 0 →
            r = 4 ∨ r = 5 ∨ r = 7 := by decide
        exact key r hr hrz
      apply gen gates hops hwf (L 4) (T 4) 0 hz 4 5 7 (by decide) (by decide) (by decide) hQ I
      intro g hg
      obtain ⟨hc, m, hm, hdm⟩ := hI g hg
      refine ⟨hc, L m, ?_, hdm⟩
      rw [hL]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> decide
    · have hQ : ∀ r ∈ L 10, r ≠ 0 → r = 10 ∨ r = 11 ∨ r = 6 := by
        intro r hr hrz
        rw [hL] at hr
        have key : ∀ r : Fin 13, r ∈ ({10, 10 + 1, 10 + 3, 10 + 9} : Finset (Fin 13)) → r ≠ 0 →
            r = 10 ∨ r = 11 ∨ r = 6 := by decide
        exact key r hr hrz
      apply gen gates hops hwf (L 10) (T 10) 0 hz 10 11 6 (by decide) (by decide) (by decide) hQ I
      intro g hg
      obtain ⟨hc, m, hm, hdm⟩ := hI g hg
      refine ⟨hc, L m, ?_, hdm⟩
      rw [hL]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> decide
    · have hQ : ∀ r ∈ L 12, r ≠ 0 → r = 12 ∨ r = 2 ∨ r = 8 := by
        intro r hr hrz
        rw [hL] at hr
        have key : ∀ r : Fin 13, r ∈ ({12, 12 + 1, 12 + 3, 12 + 9} : Finset (Fin 13)) → r ≠ 0 →
            r = 12 ∨ r = 2 ∨ r = 8 := by decide
        exact key r hr hrz
      apply gen gates hops hwf (L 12) (T 12) 0 hz 12 2 8 (by decide) (by decide) (by decide) hQ I
      intro g hg
      obtain ⟨hc, m, hm, hdm⟩ := hI g hg
      refine ⟨hc, L m, ?_, hdm⟩
      rw [hL]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> decide
  · intro m hm _ I hI
    have hz : T m 1 = fun v : Fin 13 => decide (v = 1) := hT1 m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · have hQ : ∀ r ∈ L 1, r ≠ 1 → r = 2 ∨ r = 4 ∨ r = 10 := by
        intro r hr hrz
        rw [hL] at hr
        have key : ∀ r : Fin 13, r ∈ ({1, 1 + 1, 1 + 3, 1 + 9} : Finset (Fin 13)) → r ≠ 1 →
            r = 2 ∨ r = 4 ∨ r = 10 := by decide
        exact key r hr hrz
      apply gen gates hops hwf (L 1) (T 1) 1 hz 2 4 10 (by decide) (by decide) (by decide) hQ I
      intro g hg
      obtain ⟨hc, m, hm, hdm⟩ := hI g hg
      refine ⟨hc, L m, ?_, hdm⟩
      rw [hL]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> decide
    · have hQ : ∀ r ∈ L 5, r ≠ 1 → r = 5 ∨ r = 6 ∨ r = 8 := by
        intro r hr hrz
        rw [hL] at hr
        have key : ∀ r : Fin 13, r ∈ ({5, 5 + 1, 5 + 3, 5 + 9} : Finset (Fin 13)) → r ≠ 1 →
            r = 5 ∨ r = 6 ∨ r = 8 := by decide
        exact key r hr hrz
      apply gen gates hops hwf (L 5) (T 5) 1 hz 5 6 8 (by decide) (by decide) (by decide) hQ I
      intro g hg
      obtain ⟨hc, m, hm, hdm⟩ := hI g hg
      refine ⟨hc, L m, ?_, hdm⟩
      rw [hL]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> decide
    · have hQ : ∀ r ∈ L 11, r ≠ 1 → r = 11 ∨ r = 12 ∨ r = 7 := by
        intro r hr hrz
        rw [hL] at hr
        have key : ∀ r : Fin 13, r ∈ ({11, 11 + 1, 11 + 3, 11 + 9} : Finset (Fin 13)) → r ≠ 1 →
            r = 11 ∨ r = 12 ∨ r = 7 := by decide
        exact key r hr hrz
      apply gen gates hops hwf (L 11) (T 11) 1 hz 11 12 7 (by decide) (by decide) (by decide) hQ I
      intro g hg
      obtain ⟨hc, m, hm, hdm⟩ := hI g hg
      refine ⟨hc, L m, ?_, hdm⟩
      rw [hL]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl <;> decide
