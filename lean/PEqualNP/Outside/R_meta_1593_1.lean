import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Minimize the whole circuit once. The cut child treats a variable with
-- four effective readers, or three readers including an absorbing gate.
-- The other child retains just the corresponding sparse-reader case.
-- Of the allowed operations, only NOT returns true on the input [false].
theorem PEqualNP.Outside.R_meta_1593_1 :
    (∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (z : Fin n),
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∃ x y, f (Function.update x z false) ≠ f (Function.update y z false)) →
      (let rs := C.gates.filter fun g =>
        List.contains (g.inputs.take (bif g.op.eval [false] then 1 else 2)) z.val
       4 ≤ rs.length ∨ rs.length = 3 ∧ ∃ g ∈ rs, g.op ≠ .or) →
      ∃ t, t + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x z false)) t) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool) (C : Circuit),
      (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ z : Fin n, z ∉ A →
        let rs := C.gates.filter fun g =>
          List.contains (g.inputs.take (bif g.op.eval [false] then 1 else 2)) z.val
        rs.length ≤ 3 ∧ (rs.length = 3 → ∀ g ∈ rs, g.op = .or)) →
      ∃ z : Fin n, z ∉ A ∧ ∃ t, t + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => f (Function.update x z false)) t) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
      (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i1 j1 : Fin n, G.Adj i1 j1) →
      ∃ z : Fin n, z ∉ A ∧ ∀ s : ℕ,
        PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
          @decide ((∃ a ∈ A, x a = true) ∨
            ∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true)
            (Classical.propDecidable _)) s →
        ∃ t : ℕ, t + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n
          (fun x' : Fin n → Bool => @decide ((∃ a' ∈ A, x' a' = true) ∨
            ∃ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i3 j3 ∧
              x' i3 = true ∧ x' j3 = true) (Classical.propDecidable _)) t := by
  classical
  intro cut sparse n G A hdeg hgirth hmarked hedge
  let f := fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨
    ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)
  have hf (x : Fin n → Bool) : f x = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by
    simp [f]
  have survives (z : Fin n) : ∃ i j, G.Adj i j ∧ i ≠ z ∧ j ≠ z := by
    obtain ⟨i, j, hij⟩ := hedge
    have hchoose : ∃ u, u ≠ z ∧ u ∉ A := by
      by_cases hiz : i = z
      · exact ⟨j, fun hjz => hij.ne (hiz.trans hjz.symm), hmarked j i hij.symm⟩
      · exact ⟨i, hiz, hmarked i j hij⟩
    obtain ⟨u, huz, huA⟩ := hchoose
    by_contra hno
    have hsub : G.neighborSet u ⊆ ({z} : Set (Fin n)) := by
      intro w hw
      by_contra hwz
      exact hno ⟨u, w, hw, huz, fun eq => hwz (by simp [eq])⟩
    have hle := Set.ncard_le_ncard hsub
    simp [hdeg u huA] at hle
  have nonconstant (z : Fin n) : ∃ x y,
      f (Function.update x z false) ≠ f (Function.update y z false) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    have hzero : f (Function.update (fun _ => false) z false) ≠ true := by
      intro h
      rcases (hf _).1 h with ⟨a, _, ha⟩ | ⟨i, _, _, hi, _⟩
      · simp [Function.update] at ha
      · simp [Function.update] at hi
    obtain ⟨i, j, hij, hiz, hjz⟩ := survives z
    have hone : f (Function.update (fun _ => true) z false) = true := (hf _).2
      (Or.inr ⟨i, j, hij, by simp [Function.update_of_ne hiz],
        by simp [Function.update_of_ne hjz]⟩)
    rw [hone]
    exact hzero
  have adj_delete (z i j : Fin n) : (G.deleteEdges (G.incidenceSet z)).Adj i j ↔
      G.Adj i j ∧ i ≠ z ∧ j ≠ z := by
    exact SimpleGraph.deleteIncidenceSet_adj
  have cofactor (z : Fin n) (hz : z ∉ A) (x : Fin n → Bool) :
      f (Function.update x z false) =
        @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j,
          (G.deleteEdges (G.incidenceSet z)).Adj i j ∧ x i = true ∧ x j = true)
          (Classical.propDecidable _) := by
    apply Bool.eq_iff_iff.mpr
    rw [hf, @decide_eq_true_eq _ (Classical.propDecidable _)]
    constructor
    · rintro (⟨a, haA, ha⟩ | ⟨i, j, hij, hi, hj⟩)
      · have haz : a ≠ z := fun e => hz (e ▸ haA)
        exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne haz] using ha⟩
      · have hiz : i ≠ z := by intro e; simp [e] at hi
        have hjz : j ≠ z := by intro e; simp [e] at hj
        exact Or.inr ⟨i, j, (adj_delete z i j).2 ⟨hij, hiz, hjz⟩,
          by simpa [Function.update_of_ne hiz] using hi,
          by simpa [Function.update_of_ne hjz] using hj⟩
    · rintro (⟨a, haA, ha⟩ | ⟨i, j, hij, hi, hj⟩)
      · have haz : a ≠ z := fun e => hz (e ▸ haA)
        exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne haz] using ha⟩
      · obtain ⟨hij, hiz, hjz⟩ := (adj_delete z i j).1 hij
        exact Or.inr ⟨i, j, hij, by simpa [Function.update_of_ne hiz] using hi,
          by simpa [Function.update_of_ne hjz] using hj⟩
  by_cases hfinit : ∃ s, HasCircuitSize n f s
  · obtain ⟨C, hC, hsize, hcorrect⟩ := Nat.find_spec hfinit
    have heval : circuitFun n C = f := funext hcorrect
    have minimal (s : ℕ) (h : HasCircuitSize n f s) : C.size ≤ s :=
      hsize.trans (Nat.find_min' hfinit h)
    let readers := fun z : Fin n => C.gates.filter fun g =>
      List.contains (g.inputs.take (bif g.op.eval [false] then 1 else 2)) z.val
    have exists_cut : ∃ z : Fin n, z ∉ A ∧ ∃ t, t + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => f (Function.update x z false)) t := by
      by_cases hlarge : ∃ z : Fin n, z ∉ A ∧
          (4 ≤ (readers z).length ∨ (readers z).length = 3 ∧
            ∃ g ∈ readers z, g.op ≠ .or)
      · obtain ⟨z, hz, hread⟩ := hlarge
        exact ⟨z, hz, cut n f C z hC heval minimal (nonconstant z) hread⟩
      · apply sparse n G A f C hdeg hgirth hmarked hedge hf hC heval minimal
        intro z hz
        change (readers z).length ≤ 3 ∧
          ((readers z).length = 3 → ∀ g ∈ readers z, g.op = .or)
        refine ⟨?_, ?_⟩
        · by_contra hn
          exact hlarge ⟨z, hz, Or.inl (by omega)⟩
        · intro hthree g hg
          by_contra hn
          exact hlarge ⟨z, hz, Or.inr ⟨hthree, g, hg, hn⟩⟩
    obtain ⟨z, hz, t, ht, D, hD, hDsize, hDeval⟩ := exists_cut
    refine ⟨z, hz, fun s hs => ⟨t, ht.trans (minimal s hs), D, hD, hDsize, ?_⟩⟩
    intro x
    exact (hDeval x).trans (cofactor z hz x)
  · obtain ⟨i, j, hij⟩ := hedge
    exact ⟨i, hmarked i j hij, fun s hs => (hfinit ⟨s, hs⟩).elim⟩
