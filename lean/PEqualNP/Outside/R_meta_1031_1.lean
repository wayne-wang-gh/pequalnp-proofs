import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1031_1
    (hUsed : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v, G.Adj u v ∧ Owns n C j u v)
    (hExchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G →
      let useful (C : Circuit) : Prop :=
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v, G.Adj u v ∧ Owns n C j u v
      let cost (C : Circuit) : ℕ :=
        {j : ℕ | ∃ u v p q : Fin n, G.Adj u v ∧ G.Adj p q ∧
          Owns n C j u v ∧ Owns n C j p q ∧ u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q}.ncard
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        useful C → 0 < cost C →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
          D.size ≤ C.size ∧ useful D ∧ cost D < cost C) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  classical
  intro n G _ htri hcycle
  have hfour : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hap, hbp⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨haq, hbq⟩ := (Finset.mem_filter.mp hq).2
    exact (hcycle a p b q hap hbp.symm hbq haq.symm).resolve_left hab
  let useful (D : Circuit) : Prop :=
    ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∃ u v, G.Adj u v ∧ Owns n D j u v
  let bad (D : Circuit) : Set ℕ :=
    {j | ∃ u v p q : Fin n, G.Adj u v ∧ G.Adj p q ∧
      Owns n D j u v ∧ Owns n D j p q ∧ u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q}
  let admissible (k : ℕ) : Prop :=
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
      useful D ∧ (bad D).ncard = k
  obtain ⟨C₀, h₀min, h₀fun, h₀use⟩ := hUsed n G htri hfour
  have hex : ∃ k, admissible k := ⟨(bad C₀).ncard, C₀, h₀min, h₀fun, h₀use, rfl⟩
  obtain ⟨C, hmin, hfun, huse, hcost⟩ := Nat.find_spec hex
  have hgood (j : ℕ) : j ∉ bad C := by
    intro hj
    have hfinite : (bad C).Finite :=
      (Set.finite_lt_nat C.gates.length).subset (by
        intro a ha
        obtain ⟨u, v, p, q, _, _, hown, _, _, _, _, _⟩ := ha
        exact hown.1)
    have hpositive : 0 < (bad C).ncard := (Set.ncard_pos hfinite).mpr ⟨j, hj⟩
    obtain ⟨D, hDm, hDf, hsize, hDu, hdrop⟩ :=
      hExchange n G htri hfour C hmin hfun huse hpositive
    have hDmin : IsMinimalMonoCircuit n D := ⟨hDm, fun E hEm hEf =>
      hsize.trans (hmin.2 E hEm (hEf.trans (hDf.trans hfun.symm)))⟩
    have hleast := Nat.find_min' hex
      (show admissible (bad D).ncard from ⟨D, hDmin, hDf, hDu, rfl⟩)
    change (bad D).ncard < (bad C).ncard at hdrop
    omega
  have common (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
      ∃ c : Fin n, ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = c ∨ v = c := by
    have hmeet (u v p q : Fin n) (huv : G.Adj u v) (hpq : G.Adj p q)
        (h1 : Owns n C j u v) (h2 : Owns n C j p q) : u = p ∨ u = q ∨ v = p ∨ v = q := by
      by_contra hn
      push Not at hn
      exact hgood j ⟨u, v, p, q, huv, hpq, h1, h2, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩
    obtain ⟨a, b, hab, hoab⟩ := huse j hj hop
    by_cases ha : ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = a ∨ v = a
    · exact ⟨a, ha⟩
    · push Not at ha
      obtain ⟨p, q, hpq, hopq, hpa, hqa⟩ := ha
      have hbpq : p = b ∨ q = b := by
        have h := hmeet p q a b hpq hab hopq hoab
        tauto
      have hext : ∃ w : Fin n, w ≠ a ∧ G.Adj b w ∧
          ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
        rcases hbpq with rfl | rfl
        · refine ⟨q, hqa, hpq, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
        · refine ⟨p, hpa, hpq.symm, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
      obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
      refine ⟨b, ?_⟩
      intro u v huv hov
      by_contra hn
      push Not at hn
      have huva : u = a ∨ v = a := by
        have h := hmeet u v a b huv hab hov hoab
        tauto
      have huvw : u = w ∨ v = w := by
        have h := hmeetw u v huv hov
        tauto
      have hwaAdj : G.Adj w a := by
        rcases huva with h | h
        · subst u
          have hvw : v = w := huvw.resolve_left (Ne.symm hwa)
          simpa [hvw] using huv.symm
        · subst v
          have huw : u = w := huvw.resolve_right (Ne.symm hwa)
          simpa [huw] using huv
      exact htri a b w hab hbw hwaAdj
  have coneUnfold (cs : List (List ℕ)) (g : Gate) :
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
  have coneLength (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [coneUnfold]
      omega
  have coneCharacter (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
          n ≤ w ∧ w < n + j ∧ (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by simp [coneLength]
      have old (k : ℕ) (hk : k < gs.length) :
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        simp only [coneUnfold, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have hold : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [old j h, ih i j, hold]
        constructor
        · rintro ⟨_, w, hw, h1, h2, hi⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rwa [old (w - n) (by omega)]
        · rintro ⟨_, w, hw, h1, h2, hi⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rwa [old (w - n) (by omega)] at hi
      · subst h
        have hgate : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have hnew : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          simp only [coneUnfold, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [hnew, hgate]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, hi⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rwa [old (w - n) (by omega)]
        · rintro ⟨_, w, hw, h1, h2, hi⟩
          rw [old (w - n) (by omega)] at hi
          exact ⟨w, ⟨hw, h1, h2⟩, hi⟩
      · have hnone : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          simp only [coneUnfold, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [hnone]
        constructor
        · intro hfalse; simp at hfalse
        · rintro ⟨hout, _⟩
          simp at hout
          omega
  have coneRec (i j : ℕ) : InCone n C i j ↔ j < C.gates.length ∧
      ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ InCone n C i k) := by
    delta InCone cones gateAt
    rw [coneCharacter]
    constructor
    · rintro ⟨hj, w, hw, hn, hwj, hi⟩
      refine ⟨hj, w - n, by omega, ?_, hi⟩
      rwa [show n + (w - n) = w by omega]
    · rintro ⟨hj, k, hk, hw, hi⟩
      refine ⟨hj, n + k, hw, by omega, by omega, ?_⟩
      rwa [show n + k - n = k by omega]
  have someBound (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) : j < C.gates.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hg
    contradiction
  have gateEq (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) : gateAt C j = g := by
    delta gateAt
    simp [List.getD_eq_getElem?_getD, hg]
  have gateSome (j : ℕ) (hj : j < C.gates.length) : C.gates[j]? = some (gateAt C j) := by
    delta gateAt
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  let step (a b : ℕ) : Prop :=
    a < b ∧ ∃ (k : ℕ) (g : Gate), b = n + k ∧ C.gates[k]? = some g ∧ a ∈ g.inputs
  have increasing {a b : ℕ} (hpath : Relation.TransGen step a b) : a < b := by
    induction hpath with
    | single h => exact h.1
    | tail _ h ih => exact ih.trans h.1
  have conePath (j : ℕ) : ∀ i, InCone n C i j → Relation.TransGen step (n + i) (n + j) := by
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i hi
      obtain ⟨hj, k, hkj, hmem, hk⟩ := (coneRec i j).1 hi
      have hstep : step (n + k) (n + j) := ⟨by omega, j, gateAt C j, rfl, gateSome j hj, hmem⟩
      rcases hk with h | h
      · subst i
        exact Relation.TransGen.single hstep
      · exact Relation.TransGen.tail (ih k hkj i h) hstep
  have pathHasCone {b : ℕ} {i : ℕ} (hpath : Relation.TransGen step (n + i) b) :
      ∃ j, b = n + j ∧ InCone n C i j := by
    induction hpath with
    | single hs =>
      obtain ⟨hlt, j, g, hindex, hg, hmem⟩ := hs
      rw [hindex] at hlt
      refine ⟨j, hindex, (coneRec i j).2 ⟨someBound j g hg, i, by omega, ?_, Or.inl rfl⟩⟩
      simpa only [gateEq j g hg] using hmem
    | tail _ hs ih =>
      obtain ⟨k, hbefore, hc⟩ := ih
      obtain ⟨hlt, j, g, hindex, hg, hmem⟩ := hs
      rw [hbefore, hindex] at hlt
      refine ⟨j, hindex, (coneRec i j).2 ⟨someBound j g hg, k, by omega, ?_, Or.inr hc⟩⟩
      rwa [gateEq j g hg, ← hbefore]
  have pathCone {i j : ℕ} (hpath : Relation.TransGen step (n + i) (n + j)) :
      InCone n C i j := by
    obtain ⟨k, hk, hc⟩ := pathHasCone hpath
    have : k = j := by omega
    rwa [this] at hc
  have ownExact (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
      (u v : Fin n) : Owns n C j u v ↔
      (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + j) false = true ∧
        ∀ (i : ℕ) (g' : Gate), C.gates[i]? = some g' → g'.op = GateOp.and →
          Relation.TransGen step (n + i) (n + j) →
            (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + i) false = false := by
    have hj := someBound j g hg
    constructor
    · rintro ⟨_, _, hval, hprev⟩
      refine ⟨hval, ?_⟩
      intro i g' hi ho hpath
      have hlt := increasing hpath
      exact hprev i (by omega) (pathCone hpath) (by rwa [gateEq i g' hi])
    · rintro ⟨hval, hprev⟩
      refine ⟨hj, by rwa [gateEq j g hg], hval, ?_⟩
      intro i hi hc hgate
      exact hprev i (gateAt C i) (gateSome i (hi.trans hj)) hgate (conePath j i hc)
  have model (D : Circuit) : Monotone2 D ↔
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) := by
    delta Monotone2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have computes (D : Circuit) : circuitFun n D = graphFun G ∅ ↔
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) := by
    rw [funext_iff]
    delta circuitFun graphFun
    simp
  refine ⟨C, (model C).1 hmin.1, (computes C).1 hfun, ?_, ?_⟩
  · intro D hD hDf
    exact hmin.2 D ((model D).2 hD) (((computes D).2 hDf).trans hfun.symm)
  · intro j g hj hop
    have hgate : (gateAt C j).op = GateOp.and := by rwa [gateEq j g hj]
    have hbound := someBound j g hj
    obtain ⟨u, v, huv, hown⟩ := huse j hbound hgate
    obtain ⟨c, hc⟩ := common j hbound hgate
    refine ⟨c, ⟨u, v, huv, (ownExact j g hj hop u v).1 hown⟩, ?_⟩
    intro p q hpq h
    exact hc p q hpq ((ownExact j g hj hop p q).2 h)
