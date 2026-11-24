import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1350_aux

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem prefixValue (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD i false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem firstValue {n : ℕ} (g : Gate) (gs : List Gate) (x : Fin n → Bool) :
    Circuit.eval ⟨g :: gs, n⟩ (List.ofFn x) =
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
  change (gs.foldl step (step (List.ofFn x) g)).getD n false = _
  rw [prefixValue _ _ _ (by simp [step])]
  unfold step
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem inputValue {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    Circuit.eval ⟨gs, p.val⟩ (List.ofFn x) = x p := by
  change (gs.foldl step (List.ofFn x)).getD p.val false = _
  rw [prefixValue _ _ _ (by simp)]
  simp

-- Compare wire values away from the raw input positions changed by a test.
private def Off (skip : ℕ → Prop) (r : Bool → Bool → Prop)
    (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, ¬ skip i → r (w.getD i false) (w'.getD i false)

private theorem offSnoc {skip r w w' a b} (h : Off skip r w w') (hab : r a b) :
    Off skip r (w ++ [a]) (w' ++ [b]) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  by_cases il : i < w.length
  · rw [List.getD_append _ _ _ _ il, List.getD_append _ _ _ _ (by rw [← h.1]; exact il)]
    exact h.2 i hi
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by rw [← h.1]; omega), ← h.1]
    cases d : i - w.length with
    | zero => simpa using hab
    | succ j =>
      have h0 := h.2 i hi
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by rw [← h.1]; omega)] at h0
      simpa using h0

private theorem offFold {skip r} (gs : List Gate)
    (preserve : ∀ g ∈ gs, ∀ w w', Off skip r w w' →
      r (g.op.eval (g.inputs.map fun i => w.getD i false))
         (g.op.eval (g.inputs.map fun i => w'.getD i false))) :
    ∀ w w', Off skip r w w' → Off skip r (gs.foldl step w) (gs.foldl step w') := by
  induction gs with
  | nil => exact fun _ _ h => h
  | cons g gs ih =>
    intro w w' h
    change Off skip r (gs.foldl step (step w g)) (gs.foldl step (step w' g))
    exact ih (fun g' hm => preserve g' (List.mem_cons_of_mem _ hm)) _ _
      (offSnoc h (preserve g List.mem_cons_self w w' h))

private theorem offInput {n : ℕ} {skip r} {x y : Fin n → Bool}
    (h : ∀ i : Fin n, ¬ skip i.val → r (x i) (y i)) (r00 : r false false) :
    Off skip r (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, fun j hj => ?_⟩
  by_cases jl : j < n
  · simpa [jl] using h ⟨j, jl⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact r00

private def Binary (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

private def BinaryReads (g : Gate) (i : ℕ) : Prop := Binary g ∧ i ∈ g.inputs

private def NegReads (g : Gate) (i : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some i

private theorem binaryMono {skip w w'} (g : Gate) (hg : Binary g)
    (safe : ∀ j ∈ g.inputs, ¬ skip j) (h : Off skip (fun a b => a = true → b = true) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hl b hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact h.2 j (safe j hj) (hl _ ⟨j, hj, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
    exact ⟨_, ⟨j, hj, rfl⟩, h.2 j (safe j hj) hb⟩

private theorem inputBits {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases hi : i < n
  · simp [hi]
  · rw [dite_eq_right hi, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]

private theorem uniqueNeg {gs : List Gate} (pick : Fin 1 → Fin gs.length)
    (hpick : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → ∃ r : Fin 1, pick r = i)
    {i j : Fin gs.length} (hi : (gs.get i).op = GateOp.not) (hj : (gs.get j).op = GateOp.not) :
    i = j := by
  obtain ⟨a, ha⟩ := hpick i hi
  obtain ⟨b, hb⟩ := hpick j hj
  rw [← ha, ← hb, Subsingleton.elim a b]

private theorem pairSeparated {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hcover : ∀ u : Fin n, ∃ i j : Fin m, i ≠ j ∧ u ∈ S i ∧ u ∈ S j)
    (p q : Fin n) (pq : p ≠ q) : ∃ i, p ∈ S i ∧ q ∉ S i := by
  obtain ⟨i, j, hij, hip, hjp⟩ := hcover p
  by_cases hiq : q ∈ S i
  · by_cases hjq : q ∈ S j
    · have hs : ({p,q} : Finset (Fin n)) ⊆ S i ∩ S j := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> simp [hip, hjp, hiq, hjq]
      have hh := (Finset.card_le_card hs).trans (hmeet i j hij)
      rw [Finset.card_pair pq] at hh
      omega
    · exact ⟨j, hjp, hjq⟩
  · exact ⟨i, hip, hiq⟩

private theorem outputNotInput {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ o : Fin m, 2 ≤ (S o).card) (gs : List Gate) (out : Fin m → ℕ)
    (correct : ∀ (o : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gs, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) :
    ∀ o : Fin m, n ≤ out o := by
  intro o
  by_contra! h
  let p : Fin n := ⟨out o,h⟩
  have hex : ∃ q ∈ S o, q ≠ p := by
    by_contra! hall
    have le : S o ⊆ {p} := by intro q hq; simpa using hall q hq
    have := Finset.card_le_card le
    simp at this
    have := hcard o
    omega
  obtain ⟨q, hq, qp⟩ := hex
  let x : Fin n → Bool := fun i => decide (i = q)
  have l : Circuit.eval ⟨gs,out o⟩ (List.ofFn x) = false := by
    change Circuit.eval ⟨gs,p.val⟩ (List.ofFn x) = false
    rw [inputValue]
    simp [x, qp.symm]
  rw [correct] at l
  exact (of_decide_eq_false l) ⟨q, hq, by simp [x]⟩

private theorem tailIndex (g : Gate) (gs : List Gate) {k : Gate} (hk : k ∈ gs) :
    ∃ i : Fin (g :: gs).length, i.val ≠ 0 ∧ (g :: gs).get i = k := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hk
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hj
  exact ⟨⟨j+1, by simpa using Nat.succ_lt_succ hlt⟩, by simp, heq⟩

end PEqualNP.Outside.L_meta_1350_aux
theorem PEqualNP.Outside.L_meta_1350 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ ic : Fin m, 2 ≤ (S ic).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ u : Fin n, ∃ i1 j1 : Fin m, i1 ≠ j1 ∧ u ∈ S i1 ∧ u ∈ S j1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → (∀ jr : Fin gates.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gates.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gates.length, (∃ oq : Fin m, out oq = n + jr3.val) ∨ ∃ kr : Fin gates.length, ((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gates.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gates.get kr).inputs)) ∧ (∀ jr4 : Fin gates.length, ((gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gates.get jr4).inputs = [ar, br]) → ∃ p : Fin n, (∃ a b : Fin gates.length, a ≠ b ∧ ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get a).inputs ∧ ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get b).inputs) ∨ (∃ a2 : Fin gates.length, (gates.get a2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ p.val ∈ (gates.get a2).inputs) ∨ (∃ k a3 : Fin gates.length, (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gates.get k).inputs.head? = some p.val ∧ ((gates.get a3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a3).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get a3).inputs) := by
  classical
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1350_aux in
  intro n m S hcard hmeet hcover gates out ops correct pick atMostOne reduced
  obtain ⟨nonconstant, aliases, _live, distinctArgs⟩ := reduced
  have outGE := outputNotInput S hcard gates out correct
  cases gates with
  | nil =>
    exact Fin.elim0 (pick 0)
  | cons g gs =>
    let first : Fin (g :: gs).length := ⟨0, by simp⟩
    have headEq : (g :: gs).get first = g := rfl
    by_contra noPay
    have noAnd (p : Fin n) (i : Fin (g :: gs).length)
        (hop : ((g :: gs).get i).op = GateOp.and) (hread : p.val ∈ ((g :: gs).get i).inputs) : False :=
      noPay ⟨p, Or.inr (Or.inl ⟨i,hop,hread⟩)⟩
    have atMostOneBinary (p : Fin n) (i j : Fin (g :: gs).length)
        (hi : BinaryReads ((g :: gs).get i) p.val) (hj : BinaryReads ((g :: gs).get j) p.val) :
        i = j := by
      by_contra hne
      exact noPay ⟨p, Or.inl ⟨i,j,hne,hi.1,hi.2,hj.1,hj.2⟩⟩
    have noMixed (p : Fin n) (i j : Fin (g :: gs).length)
        (hi : NegReads ((g :: gs).get i) p.val) (hj : BinaryReads ((g :: gs).get j) p.val) : False :=
      noPay ⟨p, Or.inr (Or.inr ⟨i,j,hi.1,hi.2,hj.1,hj.2⟩)⟩
    have noHeadConst (v : Bool) (hc : ∀ x : Fin n → Bool,
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = v) : False := by
      obtain ⟨x,y,hxy⟩ := nonconstant first
      change Circuit.eval ⟨g :: gs,n⟩ (List.ofFn x) ≠ Circuit.eval ⟨g :: gs,n⟩ (List.ofFn y) at hxy
      rw [firstValue, firstValue, hc x, hc y] at hxy
      exact hxy rfl
    have noHeadAlias (p : Fin n) (hc : ∀ x : Fin n → Bool,
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = x p) : False := by
      obtain ⟨x,hx⟩ := aliases first p.val (by simp [first])
      change Circuit.eval ⟨g :: gs,n⟩ (List.ofFn x) ≠ Circuit.eval ⟨g :: gs,p.val⟩ (List.ofFn x) at hx
      rw [firstValue, hc, inputValue] at hx
      exact hx rfl
    have headArgs (h : Binary g) : ∃ a b, a ≠ b ∧ g.inputs = [a,b] :=
      distinctArgs first (by rw [headEq]; exact h)
    rcases (ops g List.mem_cons_self).1 with hop | hop | hop
    · obtain ⟨a,b,ane,args⟩ := headArgs (Or.inl hop)
      have hA : ¬ a < n := by
        intro ha
        exact noAnd ⟨a,ha⟩ first (by rw [headEq,hop]) (by rw [headEq,args]; simp)
      have hB : ¬ b < n := by
        intro hb
        exact noAnd ⟨b,hb⟩ first (by rw [headEq,hop]) (by rw [headEq,args]; simp)
      exact noHeadConst false (fun x => by simp [hop,args,GateOp.eval,hA,hB])
    -- A first OR merges two inputs that some output must distinguish.
    · obtain ⟨a,b,ab,args⟩ := headArgs (Or.inr hop)
      have abRaw : a < n ∧ b < n := by
        by_cases ha : a < n <;> by_cases hb : b < n
        · exact ⟨ha,hb⟩
        · exact (noHeadAlias ⟨a,ha⟩ (fun x => by simp [hop,args,GateOp.eval,ha,hb])).elim
        · exact (noHeadAlias ⟨b,hb⟩ (fun x => by simp [hop,args,GateOp.eval,ha,hb])).elim
        · exact (noHeadConst false (fun x => by simp [hop,args,GateOp.eval,ha,hb])).elim
      let p : Fin n := ⟨a,abRaw.1⟩
      let q : Fin n := ⟨b,abRaw.2⟩
      have pq : p ≠ q := fun e => ab (congrArg Fin.val e)
      obtain ⟨o, hp, hq⟩ := pairSeparated S hmeet hcover p q pq
      let x : Fin n → Bool := fun i => decide (i = p)
      let y : Fin n → Bool := fun i => decide (i = q)
      have xp : x p = true := by simp [x]
      have xq : x q = false := by simp [x,pq.symm]
      have yp : y p = false := by simp [y,pq]
      have yq : y q = true := by simp [y]
      have brP : BinaryReads ((g :: gs).get first) p.val := by
        rw [headEq]
        exact ⟨Or.inr hop, by simp [p,args]⟩
      have brQ : BinaryReads ((g :: gs).get first) q.val := by
        rw [headEq]
        exact ⟨Or.inr hop, by simp [q,args]⟩
      let skip : ℕ → Prop := fun j => j = a ∨ j = b
      have keep : ∀ k ∈ gs, ∀ w w', Off skip Eq w w' →
          k.op.eval (k.inputs.map fun j => w.getD j false) =
          k.op.eval (k.inputs.map fun j => w'.getD j false) := by
        intro k hk w w' hw
        obtain ⟨i, i0, hki⟩ := tailIndex g gs hk
        have safe (hbin : Binary k) (j : ℕ) (hj : j ∈ k.inputs) : ¬ skip j := by
          intro hbad
          have hr : BinaryReads ((g :: gs).get i) j := by rw [hki]; exact ⟨hbin,hj⟩
          rcases hbad with ha | hb
          · have he := atMostOneBinary p i first (by rwa [ha] at hr) brP
            exact i0 (congrArg Fin.val he)
          · have he := atMostOneBinary q i first (by rwa [hb] at hr) brQ
            exact i0 (congrArg Fin.val he)
        have gateEq (hbin : Binary k) :
            k.op.eval (k.inputs.map fun j => w.getD j false) =
              k.op.eval (k.inputs.map fun j => w'.getD j false) :=
          congrArg k.op.eval (List.map_congr_left fun j hj => hw.2 j (safe hbin j hj))
        rcases (ops k (List.mem_cons_of_mem _ hk)).1 with ho | ho | ho
        · exact gateEq (Or.inl ho)
        · exact gateEq (Or.inr ho)
        · cases hargs : k.inputs with
          | nil => simp [ho,GateOp.eval]
          | cons j js =>
            have hj : ¬ skip j := by
              intro hbad
              have hr : NegReads ((g :: gs).get i) j := by rw [hki]; exact ⟨ho,by simp [hargs]⟩
              rcases hbad with ha | hb
              · exact noMixed p i first (by rwa [ha] at hr) brP
              · exact noMixed q i first (by rwa [hb] at hr) brQ
            simp [ho,GateOp.eval]
            exact hw.2 j hj
      have initial : Off skip Eq (List.ofFn x) (List.ofFn y) := by
        apply offInput _ rfl
        intro i hi
        have ip : i ≠ p := fun e => hi (Or.inl (congrArg Fin.val e))
        have iq : i ≠ q := fun e => hi (Or.inr (congrArg Fin.val e))
        simp [x,y,ip,iq]
      have equalFirst :
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) =
          g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false) := by
        have ap : (List.ofFn x).getD a false = true := by simpa [inputBits,abRaw.1,p] using xp
        have bp : (List.ofFn x).getD b false = false := by simpa [inputBits,abRaw.2,q] using xq
        have aq : (List.ofFn y).getD a false = false := by simpa [inputBits,abRaw.1,p] using yp
        have bq : (List.ofFn y).getD b false = true := by simpa [inputBits,abRaw.2,q] using yq
        simp only [hop,args,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
          id,ap,bp,aq,bq]
        rfl
      have same := offFold gs keep _ _ (offSnoc initial equalFirst)
      have ho : ¬ skip (out o) := by
        intro hbad
        have := outGE o
        rcases hbad with ha | hb <;> omega
      have sameOut : Circuit.eval ⟨g :: gs,out o⟩ (List.ofFn x) =
          Circuit.eval ⟨g :: gs,out o⟩ (List.ofFn y) := same.2 (out o) ho
      rw [correct, correct] at sameOut
      have lhs : (∃ v ∈ S o, x v = true) := ⟨p,hp,xp⟩
      have rhs : ¬ (∃ v ∈ S o, y v = true) := by
        rintro ⟨v,hv,hy⟩
        have e : v = q := of_decide_eq_true hy
        exact hq (e ▸ hv)
      simp [lhs,rhs] at sameOut
    · cases hargs : g.inputs with
      | nil => exact noHeadConst true (fun x => by simp [hop,hargs,GateOp.eval])
      | cons a as =>
        by_cases ha : a < n
        · let p : Fin n := ⟨a,ha⟩
          let x : Fin n → Bool := fun i => decide (i = p)
          let y : Fin n → Bool := fun _ => false
          obtain ⟨o,_,_,hp,_⟩ := hcover p
          have np : NegReads ((g :: gs).get first) p.val := by
            rw [headEq]
            exact ⟨hop,by simp [hargs,p]⟩
          let skip : ℕ → Prop := fun j => j = a
          let rel : Bool → Bool → Prop := fun l r => l = true → r = true
          -- The first NOT reverses the singleton comparison. The tail preserves that order.
          have keep : ∀ k ∈ gs, ∀ w w', Off skip rel w w' →
              rel (k.op.eval (k.inputs.map fun i => w.getD i false))
                  (k.op.eval (k.inputs.map fun i => w'.getD i false)) := by
            intro k hk w w' hw
            obtain ⟨i,h0,he⟩ := tailIndex g gs hk
            have hb : Binary k := by
              rcases (ops k (List.mem_cons_of_mem _ hk)).1 with ho | ho | ho
              · exact Or.inl ho
              · exact Or.inr ho
              · exfalso
                have ei := uniqueNeg pick atMostOne (show ((g :: gs).get i).op = GateOp.not by rw [he,ho])
                  (show ((g :: gs).get first).op = GateOp.not by rw [headEq,hop])
                exact h0 (congrArg Fin.val ei)
            apply binaryMono k hb _ hw
            intro j hj heq
            have hr : BinaryReads ((g :: gs).get i) p.val := by
              rw [he]
              exact ⟨hb,by change j = p.val at heq; rwa [← heq]⟩
            exact noMixed p first i np hr
          have initial : Off skip rel (List.ofFn x) (List.ofFn y) := by
            apply offInput _ (by simp [rel])
            intro i hi
            have ip : i ≠ p := fun e => hi (congrArg Fin.val e)
            simp [rel,x,y,ip]
          have hd : rel
              (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))
              (g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false)) := by
            simp [rel,hop,hargs,GateOp.eval,ha,x,y,p]
          have result := offFold gs keep _ _ (offSnoc initial hd)
          have ho : ¬ skip (out o) := by
            intro hbad
            have := outGE o
            change out o = a at hbad
            omega
          have comparison : rel (Circuit.eval ⟨g :: gs,out o⟩ (List.ofFn x))
              (Circuit.eval ⟨g :: gs,out o⟩ (List.ofFn y)) := result.2 (out o) ho
          rw [correct, correct] at comparison
          have hx : (∃ v ∈ S o, x v = true) := ⟨p,hp,by simp [x]⟩
          simp [rel,hx,y] at comparison
        · exact noHeadConst true (fun x => by simp [hop,hargs,GateOp.eval,ha])
