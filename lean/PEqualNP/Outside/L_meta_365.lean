import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_365 :
    ∀ (n : ℕ) (E : PEqualNP.MetaComplexity.SingleLevel.Edges n), PEqualNP.MetaComplexity.SingleLevel.WF E → ∀ τ : Fin n × Fin n → Finset (Fin n) → Fin n, (∀ e ∈ E, ∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin n × Fin n → ℚ, (∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin n, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → (∀ w : Fin n, (∀ a b : Fin n, ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) → ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0) ∧ (∀ e ∈ E, ((∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) ∨ (∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2)) → c e = 0) := by
  intro n E hWF τ hτ c hc
  constructor
  · intro w hN
    let I : Finset (Fin n) := Finset.univ.filter (fun u => (w, u) ∈ E ∨ (u, w) ∈ E)
    have hI : ∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I) := by
      intro f hf hmem
      have h1 : (w, f.1) ∈ E ∨ (f.1, w) ∈ E := by
        simpa [I] using hmem.1
      have h2 : (w, f.2) ∈ E ∨ (f.2, w) ∈ E := by
        simpa [I] using hmem.2
      exact hN f.1 f.2 h1 h2 (Or.inl hf)
    have hzero := hc I hI w
    have hfilt : E.filter (fun e => τ e I = w) = E.filter (fun e => e.1 = w ∨ e.2 = w) := by
      apply List.filter_congr
      intro e he
      simp only [decide_eq_decide]
      have ⟨hor, hnot⟩ := hτ e he I hI
      constructor
      · intro htw
        rw [← htw]
        exact hor.imp Eq.symm Eq.symm
      · intro hew
        rcases hew with h1 | h2
        · have he2 : e.2 ∈ I := by
            simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
            left
            rw [← h1]
            exact he
          rcases hor with hτ1 | hτ2
          · exact hτ1.trans h1
          · exact False.elim (hnot (hτ2 ▸ he2))
        · have he1 : e.1 ∈ I := by
            simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
            right
            rw [← h2]
            exact he
          rcases hor with hτ1 | hτ2
          · exact False.elim (hnot (hτ1 ▸ he1))
          · exact hτ2.trans h2
    rw [← hfilt]
    exact hzero
  · intro e he hpendant
    have hnodup : E.Nodup := by
      apply hWF.2.imp
      intro a b hab heq
      subst heq
      exact hab (Or.inl ⟨rfl, rfl⟩)
    have hfilter_eq : ∀ {L : List (Fin n × Fin n)} {x : Fin n × Fin n},
        L.Nodup → x ∈ L → L.filter (fun f => f = x) = [x] := by
      intro L x hnd hx
      induction L with
      | nil => cases hx
      | cons hd tl ih =>
        rw [List.nodup_cons] at hnd
        rcases List.mem_cons.mp hx with rfl | hxtl
        · simp only [List.filter_cons, decide_true, ↓reduceIte]
          congr 1
          rw [List.filter_eq_nil_iff]
          intro f hf
          simp only [decide_eq_true_eq]
          intro hfx
          subst hfx
          exact hnd.1 hf
        · have hne : hd ≠ x := fun h => hnd.1 (h ▸ hxtl)
          simp only [List.filter_cons, decide_eq_false hne, Bool.false_eq_true, ↓reduceIte]
          exact ih hnd.2 hxtl
    have hsingle : ∀ (u v : Fin n),
        (u = e.1 ∧ v = e.2 ∨ u = e.2 ∧ v = e.1) →
        (∀ f ∈ E, f ≠ e → f.1 ≠ u ∧ f.2 ≠ u) → c e = 0 := by
      intro u v huv hdeg
      let I : Finset (Fin n) := {v}
      have hI : ∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I) := by
        intro f hf hmem
        have h1 : f.1 = v := Finset.mem_singleton.mp hmem.1
        have h2 : f.2 = v := Finset.mem_singleton.mp hmem.2
        exact hWF.1 f hf (h1.trans h2.symm)
      have hzero := hc I hI u
      have hfilt : E.filter (fun f => τ f I = u) = E.filter (fun f => f = e) := by
        apply List.filter_congr
        intro f hf
        simp only [decide_eq_decide]
        have ⟨hor, hnot⟩ := hτ f hf I hI
        constructor
        · intro htu
          by_contra hne
          have ⟨h1, h2⟩ := hdeg f hf hne
          rcases hor with hτ1 | hτ2
          · exact h1 (hτ1.symm.trans htu)
          · exact h2 (hτ2.symm.trans htu)
        · intro hfe
          subst hfe
          have hv : v ∈ I := Finset.mem_singleton_self v
          rcases huv with ⟨hu, hv'⟩ | ⟨hu, hv'⟩
          · rcases hor with hτ1 | hτ2
            · exact hτ1.trans hu.symm
            · exact False.elim (hnot ((hτ2.trans hv'.symm) ▸ hv))
          · rcases hor with hτ1 | hτ2
            · exact False.elim (hnot ((hτ1.trans hv'.symm) ▸ hv))
            · exact hτ2.trans hu.symm
      rw [hfilt, hfilter_eq hnodup he] at hzero
      simpa using hzero
    rcases hpendant with h1 | h2
    · exact hsingle e.1 e.2 (Or.inl ⟨rfl, rfl⟩) h1
    · exact hsingle e.2 e.1 (Or.inr ⟨rfl, rfl⟩) h2
