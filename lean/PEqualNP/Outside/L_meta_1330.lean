import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1330 : (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (np mp : ℕ) (Sp : Fin mp → Finset (Fin np)), (∀ ic : Fin mp, 2 ≤ (Sp ic).card) → (∀ ia ja : Fin mp, ia ≠ ja → (Sp ia ∩ Sp ja).card ≤ 1) → ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin mp → ℕ), (∀ gg ∈ gl, (gg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gg.inputs.length ≤ 2) → (∀ (oa : Fin mp) (xa : Fin np → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ Sp oa, xa va = true)) → ∀ ι : Fin 1 → Fin gl.length, (∀ qa : Fin gl.length, (gl.get qa).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ ka : Fin 1, ι ka = qa) → ∀ c : PEqualNP.CircuitLowerBounds.GateOp, (c = PEqualNP.CircuitLowerBounds.GateOp.and ∨ c = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (ob : Fin mp) (xb : Fin np → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl.set (ι 0).val ⟨c, []⟩, ol ob⟩ (List.ofFn xb) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol ob⟩ (List.ofFn xb)) → (∑ sa : Fin mp, (Sp sa).card) ≤ gl.length + mp := by
  intro H np mp Sp h2 hint gl ol hgl hev ι hι c hc hset
  have hfree : ∀ g ∈ gl.set (ι 0).val ⟨c, []⟩, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_set]
    split_ifs with hiq
    · exact ⟨hc, by simp⟩
    · have hq' : q < gl.length := by simpa using hq
      obtain ⟨hop, hlen⟩ := hgl gl[q] (List.getElem_mem hq')
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        obtain ⟨k, hk⟩ := hι ⟨q, hq'⟩ (by simpa using h)
        have hk0 : k = 0 := Subsingleton.elim k 0
        subst hk0
        exact hiq (by rw [hk])
  have hb := H np mp Sp hint (gl.set (ι 0).val ⟨c, []⟩) ol hfree
    (fun w x => (hset w x).trans (hev w x))
  rw [List.length_set] at hb
  have hsum : (∑ sa : Fin mp, (Sp sa).card) = (∑ sa : Fin mp, ((Sp sa).card - 1)) + mp := by
    have e : ∀ sa : Fin mp, (Sp sa).card = ((Sp sa).card - 1) + 1 := by
      intro sa
      have := h2 sa
      omega
    conv_lhs => rw [Finset.sum_congr rfl (fun sa _ => e sa)]
    rw [Finset.sum_add_distrib]
    simp
  omega
