import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_351

-- If the first input of gate g is already true at I, adding the vertex u (which is read only by
-- g, on its first input, and by H, already true at I) changes no gate value.
theorem stable (n b : ℕ) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b))
    (val : Finset (Fin n) → Fin b → Prop)
    (hP : ∀ i : Fin b, ∀ j ∈ PG i, j < i) (hR : ∀ i : Fin b, ∀ j ∈ RG i, j < i)
    (hval : ∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔
      (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j)))
    (g H : Fin b) (u : Fin n) (huR : u ∉ RV g)
    (honly : ∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H)
    (I : Finset (Fin n)) (hH : val I H)
    (hside : (∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j) :
    ∀ (k : ℕ) (i : Fin b), i.val < k → (val (insert u I) i → val I i) := by
  intro k
  induction k with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hi hv
    by_cases hiH : i = H
    · rw [hiH]; exact hH
    have hlt : ∀ j : Fin b, j < i → j.val < k := by
      intro j hj
      have : j.val < i.val := hj
      omega
    rw [hval] at hv
    rw [hval]
    obtain ⟨h1, h2⟩ := hv
    by_cases hig : i = g
    · subst hig
      refine ⟨hside, ?_⟩
      rcases h2 with ⟨v, hv1, hv2⟩ | ⟨j, hj1, hj2⟩
      · left
        refine ⟨v, hv1, ?_⟩
        rcases Finset.mem_insert.mp hv2 with h | h
        · exact absurd (h ▸ hv1) huR
        · exact h
      · right
        exact ⟨j, hj1, ih j (hlt j (hR i j hj1)) hj2⟩
    · have hu1 : u ∉ PV i := fun h => by
        rcases honly i (Or.inl h) with h' | h'
        · exact hig h'
        · exact hiH h'
      have hu2 : u ∉ RV i := fun h => by
        rcases honly i (Or.inr h) with h' | h'
        · exact hig h'
        · exact hiH h'
      constructor
      · rcases h1 with ⟨v, hv1, hv2⟩ | ⟨j, hj1, hj2⟩
        · left
          refine ⟨v, hv1, ?_⟩
          rcases Finset.mem_insert.mp hv2 with h | h
          · exact absurd (h ▸ hv1) hu1
          · exact h
        · right
          exact ⟨j, hj1, ih j (hlt j (hP i j hj1)) hj2⟩
      · rcases h2 with ⟨v, hv1, hv2⟩ | ⟨j, hj1, hj2⟩
        · left
          refine ⟨v, hv1, ?_⟩
          rcases Finset.mem_insert.mp hv2 with h | h
          · exact absurd (h ▸ hv1) hu2
          · exact h
        · right
          exact ⟨j, hj1, ih j (hlt j (hR i j hj1)) hj2⟩

-- The first input of a locked gate is false at I.
theorem side_false (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n))
    (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b))
    (val : Finset (Fin n) → Fin b → Prop)
    (hP : ∀ i : Fin b, ∀ j ∈ PG i, j < i) (hR : ∀ i : Fin b, ∀ j ∈ RG i, j < i)
    (hval : ∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔
      (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j)))
    (hout : ∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔
      ∃ a ∈ X, ∃ c ∈ X, G.Adj a c)
    (g H : Fin b) (u : Fin n) (huR : u ∉ RV g)
    (honly : ∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H)
    (I : Finset (Fin n)) (hI : ∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c)
    (hw : ∃ w ∈ I, G.Adj u w) (hH : val I H) :
    ¬ ((∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j) := by
  intro hside
  have hst := PEqualNP.Outside.L_meta_351.stable n b PV RV PG RG val hP hR hval g H u huR honly I hH
    hside
  have huOV : u ∉ OV := by
    intro h
    have h1 := (hout {u}).mp (Or.inl ⟨u, h, Finset.mem_singleton_self u⟩)
    obtain ⟨a, ha, c, hc, hac⟩ := h1
    rw [Finset.mem_singleton] at ha hc
    rw [ha, hc] at hac
    exact G.irrefl hac
  obtain ⟨w, hwI, huw⟩ := hw
  have h1 := (hout (insert u I)).mpr
    ⟨u, Finset.mem_insert_self u I, w, Finset.mem_insert_of_mem hwI, huw⟩
  have h2 : (∃ v ∈ OV, v ∈ I) ∨ ∃ j ∈ OG, val I j := by
    rcases h1 with ⟨v, hv1, hv2⟩ | ⟨j, hj1, hj2⟩
    · left
      refine ⟨v, hv1, ?_⟩
      rcases Finset.mem_insert.mp hv2 with h | h
      · exact absurd (h ▸ hv1) huOV
      · exact h
    · right
      exact ⟨j, hj1, hst (j.val + 1) j (Nat.lt_succ_self _) hj2⟩
  obtain ⟨a, ha, c, hc, hac⟩ := (hout I).mp h2
  exact hI a ha c hc hac


-- A locked gate does not read H on its first input.
theorem notP (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n))
    (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b))
    (val : Finset (Fin n) → Fin b → Prop)
    (hP : ∀ i : Fin b, ∀ j ∈ PG i, j < i) (hR : ∀ i : Fin b, ∀ j ∈ RG i, j < i)
    (hval : ∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔
      (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j)))
    (hout : ∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔
      ∃ a ∈ X, ∃ c ∈ X, G.Adj a c)
    (g H : Fin b)
    (hl : ∃ (u : Fin n) (I : Finset (Fin n)), u ∈ PV g ∧ u ∉ RV g ∧ (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧ (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H) :
    H ∉ PG g := by
  obtain ⟨u, I, _, huR, honly, hI, _, hw, hH⟩ := hl
  intro hHg
  exact PEqualNP.Outside.L_meta_351.side_false n b G PV RV PG RG OV OG val hP hR hval hout g H u
    huR honly I hI hw hH (Or.inr ⟨H, hHg, hH⟩)

end PEqualNP.Outside.L_meta_351

theorem PEqualNP.Outside.L_meta_351 : ∀ (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop), (∀ i : Fin b, ∀ j ∈ PG i, j < i) → (∀ i : Fin b, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) → ∀ H : Fin b, (∃ g : Fin b, g ≠ H) → (∀ g : Fin b, g ≠ H → (∃ (u : Fin n) (I : Finset (Fin n)), u ∈ PV g ∧ u ∉ RV g ∧ (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧ (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H) ∧ (∃ (u : Fin n) (I : Finset (Fin n)), u ∈ RV g ∧ u ∉ PV g ∧ (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧ (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H)) → ∀ a c : Fin n, G.Adj a c → ¬ ∀ i : Fin b, i ≠ H → ((a ∉ PV i ∧ c ∉ PV i) ∨ (a ∉ RV i ∧ c ∉ RV i)) := by
  intro n b G PV RV PG RG OV OG val hP hR hval hout H hex hlock a c hac hb
  have hval' : ∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔
      (((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j) ∧ ((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j)) :=
    fun X i => (hval X i).trans and_comm
  have hnP : ∀ g : Fin b, g ≠ H → H ∉ PG g := fun g hg =>
    PEqualNP.Outside.L_meta_351.notP n b G PV RV PG RG OV OG val hP hR hval hout g H (hlock g hg).1
  have hnR : ∀ g : Fin b, g ≠ H → H ∉ RG g := by
    intro g hg
    obtain ⟨u, I, h1, h2, h3, h4, h5, h6, h7⟩ := (hlock g hg).2
    exact PEqualNP.Outside.L_meta_351.notP n b G RV PV RG PG OV OG val hR hP hval' hout g H
      ⟨u, I, h1, h2, fun i hi => h3 i hi.symm, h4, h5, h6, h7⟩
  have hnOV : ∀ v ∈ OV, False := by
    intro v h
    have h1 := (hout {v}).mp (Or.inl ⟨v, h, Finset.mem_singleton_self v⟩)
    obtain ⟨a', ha, c', hc, hac'⟩ := h1
    rw [Finset.mem_singleton] at ha hc
    rw [ha, hc] at hac'
    exact G.irrefl hac'
  have hnOG : H ∉ OG := by
    intro hH
    obtain ⟨g, hg⟩ := hex
    obtain ⟨u, I, _, _, _, hI, _, _, hv⟩ := (hlock g hg).1
    obtain ⟨a', ha, c', hc, hac'⟩ := (hout I).mp (Or.inr ⟨H, hH, hv⟩)
    exact hI a' ha c' hc hac'
  have key : ∀ (k : ℕ) (i : Fin b), i.val < k → i ≠ H → ¬ val {a, c} i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi hiH hv
      have hlt : ∀ j : Fin b, j < i → j.val < k := by
        intro j hj
        have : j.val < i.val := hj
        omega
      rw [hval] at hv
      obtain ⟨h1, h2⟩ := hv
      have e1 : ∃ v ∈ PV i, v ∈ ({a, c} : Finset (Fin n)) := by
        rcases h1 with h | ⟨j, hj1, hj2⟩
        · exact h
        · exact absurd hj2 (ih j (hlt j (hP i j hj1)) (fun h => hnP i hiH (h ▸ hj1)))
      have e2 : ∃ v ∈ RV i, v ∈ ({a, c} : Finset (Fin n)) := by
        rcases h2 with h | ⟨j, hj1, hj2⟩
        · exact h
        · exact absurd hj2 (ih j (hlt j (hR i j hj1)) (fun h => hnR i hiH (h ▸ hj1)))
      obtain ⟨v, hv1, hv2⟩ := e1
      obtain ⟨w, hw1, hw2⟩ := e2
      rw [Finset.mem_insert, Finset.mem_singleton] at hv2 hw2
      rcases hb i hiH with ⟨p1, p2⟩ | ⟨p1, p2⟩
      · rcases hv2 with h | h
        · exact p1 (h ▸ hv1)
        · exact p2 (h ▸ hv1)
      · rcases hw2 with h | h
        · exact p1 (h ▸ hw1)
        · exact p2 (h ▸ hw1)
  have h1 := (hout {a, c}).mpr ⟨a, by simp, c, by simp, hac⟩
  rcases h1 with ⟨v, hv1, _⟩ | ⟨j, hj1, hj2⟩
  · exact hnOV v hv1
  · exact key (j.val + 1) j (Nat.lt_succ_self _) (fun h => hnOG (h ▸ hj1)) hj2
