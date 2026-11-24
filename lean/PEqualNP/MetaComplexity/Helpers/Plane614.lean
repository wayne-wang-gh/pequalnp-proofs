import PEqualNP.MetaComplexity.Helpers.LineDeg3Below

namespace PEqualNP.MetaComplexity.Plane614

/-- The point-line relation of a cyclic difference set `D` modulo `N`, on `Fin (2 N)`. -/
def rel (N : ℕ) (D : Finset ℕ) (a b : Fin (2 * N)) : Prop :=
  a.val < N ∧ N ≤ b.val ∧ (a.val + (b.val - N)) % N ∈ D

instance (N : ℕ) (D : Finset ℕ) : DecidableRel (rel N D) := fun a b => by
  unfold rel; infer_instance

/-- Boolean adjacency. -/
def adjB (N : ℕ) (D : Finset ℕ) (a b : Fin (2 * N)) : Bool :=
  decide (a ≠ b ∧ (rel N D a b ∨ rel N D b a))

theorem adj_iff (N : ℕ) (D : Finset ℕ) (a b : Fin (2 * N)) :
    (SimpleGraph.fromRel (rel N D)).Adj a b ↔ adjB N D a b = true := by
  simp [adjB, SimpleGraph.fromRel_adj]

theorem ncard_eq (N : ℕ) (D : Finset ℕ) (v : Fin (2 * N)) :
    ((SimpleGraph.fromRel (rel N D)).neighborSet v).ncard
      = (Finset.univ.filter (fun w => adjB N D v w = true)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborSet, adjB, SimpleGraph.fromRel_adj]


/-- Generic assembly: facts decided at a concrete size give the conclusion of L-meta-614's
hypotheses-to-bound statement. -/
theorem assemble (N : ℕ) (D : Finset ℕ) (hN : 0 < N)
    (hdeg : ∀ v : Fin (2 * N), 2 ≤ (Finset.univ.filter (fun w => adjB N D v w = true)).card)
    (hH1 : ∀ v w : Fin (2 * N), v ≠ w → adjB N D v w = false → ∃ u, adjB N D v u ≠ adjB N D w u)
    (hH2 : ∀ v w : Fin (2 * N), adjB N D v w = true → ∃ a b : Fin (2 * N), adjB N D v a = true ∧ a ≠ w ∧
      adjB N D w b = true ∧ b ≠ v ∧ (a = b ∨ adjB N D a b = false))
    (hcov : ∀ u v : Fin (2 * N), adjB N D u v = true → u.val < N ∨ v.val < N)
    (hM : ∀ (p : Fin N) (q : Fin (2 * N)), q.val = N + (N - p.val) % N →
      adjB N D (Fin.castLE (by omega) p) q = true)
    (hMinj : ∀ p q : Fin N, (N - p.val) % N = (N - q.val) % N → p = q)
    (h614 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) →
      (∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) →
      (∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ a b : Fin n, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b)) →
      (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧ S.card = t) →
      (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) → t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      n + t ≤ C.size + 1)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hM2 : PEqualNP.MetaComplexity.Monotone2 C)
    (hC : ∀ x : Fin (2 * N) → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin (2 * N),
      (SimpleGraph.fromRel (rel N D)).Adj u v ∧ x u = true ∧ x v = true) :
    2 * N + N ≤ C.size + 1 := by
  have hd : ∀ v : Fin (2 * N), 2 ≤ ((SimpleGraph.fromRel (rel N D)).neighborSet v).ncard :=
    fun v => by rw [ncard_eq]; exact hdeg v
  refine h614 (2 * N) N _ C ?_ ?_ ?_ ?_ ?_ hM2 hC
  · intro v
    have := hdeg v
    have h0 : 0 < (Finset.univ.filter (fun w => adjB N D v w = true)).card := by omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp h0
    exact ⟨w, (adj_iff _ _ _ _).2 (by simpa using hw)⟩
  · intro v w hvw hn _ _
    obtain ⟨u, hu⟩ := hH1 v w hvw (by rw [adj_iff] at hn; simpa using hn)
    exact ⟨u, fun h => hu (Bool.eq_iff_iff.2 (by rw [adj_iff, adj_iff] at h; exact h))⟩
  · intro v w hadj _ _
    obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := hH2 v w ((adj_iff _ _ _ _).1 hadj)
    exact ⟨a, b, (adj_iff _ _ _ _).2 h1, h2, (adj_iff _ _ _ _).2 h3, h4, by
      rcases h5 with h5 | h5
      · exact Or.inl h5
      · exact Or.inr (by rw [adj_iff]; simp [h5])⟩
  · refine ⟨Finset.univ.filter (fun v : Fin (2 * N) => v.val < N), ?_, ?_⟩
    · intro u v h _ _
      simpa using hcov u v ((adj_iff _ _ _ _).1 h)
    · have : (Finset.univ.filter (fun v : Fin (2 * N) => v.val < N)).card = N := by
        have e : (Finset.univ.filter (fun v : Fin (2 * N) => v.val < N)) =
            (Finset.univ : Finset (Fin N)).map (Fin.castLEEmb (by omega)) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Fin.castLEEmb_apply]
          constructor
          · intro h; exact ⟨⟨v.val, h⟩, Fin.ext rfl⟩
          · rintro ⟨p, rfl⟩; exact p.2
        rw [e, Finset.card_map]; simp
      exact this
  · intro S hS
    let g : Fin N → Fin (2 * N) := fun p =>
      if Fin.castLE (by omega) p ∈ S then Fin.castLE (by omega) p
      else ⟨N + (N - p.val) % N, by have := Nat.mod_lt (N - p.val) hN; omega⟩
    have hgS : ∀ p, g p ∈ S := by
      intro p
      by_cases h : Fin.castLE (by omega) p ∈ S
      · simp only [g, if_pos h]; exact h
      · simp only [g, if_neg h]
        have := hM p ⟨N + (N - p.val) % N, by have := Nat.mod_lt (N - p.val) hN; omega⟩ rfl
        rcases hS _ _ ((adj_iff _ _ _ _).2 this) (hd _) (hd _) with h' | h'
        · exact absurd h' h
        · exact h'
    have hinj : Function.Injective g := by
      intro p q hpq
      have hp := Nat.mod_lt (N - p.val) hN
      have hq := Nat.mod_lt (N - q.val) hN
      have pl := p.2
      have ql := q.2
      simp only [g] at hpq
      split_ifs at hpq with h1 h2 h2
      · exact Fin.castLE_injective _ hpq
      · have := congrArg Fin.val hpq; simp at this; omega
      · have := congrArg Fin.val hpq; simp at this; omega
      · have := congrArg Fin.val hpq; simp at this
        exact hMinj p q (by omega)
    have := Finset.card_le_card_of_injOn g (s := (Finset.univ : Finset (Fin N))) (t := S)
      (fun p _ => hgS p) hinj.injOn
    simpa using this


/-- Heawood graph facts, decided. -/
theorem facts14 :
    (∀ v : Fin (2 * 7), 2 ≤ (Finset.univ.filter (fun w => adjB 7 {0, 1, 3} v w = true)).card) ∧
    (∀ v w : Fin (2 * 7), v ≠ w → adjB 7 {0, 1, 3} v w = false → ∃ u, adjB 7 {0, 1, 3} v u ≠ adjB 7 {0, 1, 3} w u) ∧
    (∀ v w : Fin (2 * 7), adjB 7 {0, 1, 3} v w = true → ∃ a b : Fin (2 * 7), adjB 7 {0, 1, 3} v a = true ∧ a ≠ w ∧
      adjB 7 {0, 1, 3} w b = true ∧ b ≠ v ∧ (a = b ∨ adjB 7 {0, 1, 3} a b = false)) ∧
    (∀ u v : Fin (2 * 7), adjB 7 {0, 1, 3} u v = true → u.val < 7 ∨ v.val < 7) ∧
    (∀ (p : Fin 7) (q : Fin (2 * 7)), q.val = 7 + (7 - p.val) % 7 →
      adjB 7 {0, 1, 3} (Fin.castLE (by omega) p) q = true) ∧
    (∀ p q : Fin 7, (7 - p.val) % 7 = (7 - q.val) % 7 → p = q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Plane of order 3 facts, decided. -/
theorem facts26 :
    (∀ v : Fin (2 * 13), 2 ≤ (Finset.univ.filter (fun w => adjB 13 {0, 1, 3, 9} v w = true)).card) ∧
    (∀ v w : Fin (2 * 13), v ≠ w → adjB 13 {0, 1, 3, 9} v w = false → ∃ u, adjB 13 {0, 1, 3, 9} v u ≠ adjB 13 {0, 1, 3, 9} w u) ∧
    (∀ v w : Fin (2 * 13), adjB 13 {0, 1, 3, 9} v w = true → ∃ a b : Fin (2 * 13), adjB 13 {0, 1, 3, 9} v a = true ∧ a ≠ w ∧
      adjB 13 {0, 1, 3, 9} w b = true ∧ b ≠ v ∧ (a = b ∨ adjB 13 {0, 1, 3, 9} a b = false)) ∧
    (∀ u v : Fin (2 * 13), adjB 13 {0, 1, 3, 9} u v = true → u.val < 13 ∨ v.val < 13) ∧
    (∀ (p : Fin 13) (q : Fin (2 * 13)), q.val = 13 + (13 - p.val) % 13 →
      adjB 13 {0, 1, 3, 9} (Fin.castLE (by omega) p) q = true) ∧
    (∀ p q : Fin 13, (13 - p.val) % 13 = (13 - q.val) % 13 → p = q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end PEqualNP.MetaComplexity.Plane614
