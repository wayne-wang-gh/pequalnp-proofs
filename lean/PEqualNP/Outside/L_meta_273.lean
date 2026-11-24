import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_273

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

def Wv (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem Wv_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    Wv C n x i = x i := by
  unfold Wv
  rw [wires_eq, foldl_step_getD _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem Wv_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (t : ℕ) (ht : t < C.gates.length) :
    Wv C n x (n + t) = (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
      if i < n + t then Wv C n x i else false) := by
  have := gate_value C.gates (List.ofFn x) t ht
  rw [List.length_ofFn] at this
  exact this

theorem Wv_big (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : Wv C n x i = false := by
  unfold Wv
  rw [wires_eq]
  apply getD_of_length_le
  rw [foldl_step_length, List.length_ofFn]
  exact hi

def Rd (C : Circuit) (n : ℕ) (x : Fin n → Bool) (t i : ℕ) : Bool :=
  if i < n + t then Wv C n x i else false

def pt (n : ℕ) (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def ind (n : ℕ) (A : Finset (Fin n)) : Fin n → Bool := fun q => decide (q ∈ A)

def Ls (C : Circuit) (n : ℕ) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => Wv C n (pt n p) j = true)

theorem mem_Ls (C : Circuit) (n : ℕ) (j : ℕ) (p : Fin n) :
    p ∈ Ls C n j ↔ Wv C n (pt n p) j = true := by
  simp [Ls]

theorem eval_and (u v : Bool) : GateOp.and.eval [u, v] = (u && v) := by
  simp [GateOp.eval]

theorem eval_or (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
  simp [GateOp.eval]

theorem Wv_two (C : Circuit) (n : ℕ) (x : Fin n → Bool) (t : ℕ) (ht : t < C.gates.length)
    (a b : ℕ) (hab : (C.gates[t]).inputs = [a, b]) :
    Wv C n x (n + t) = (C.gates[t]).op.eval [Rd C n x t a, Rd C n x t b] := by
  rw [Wv_gate C n x t ht, hab]
  rfl

theorem gate_lift (C : Circuit) (n : ℕ) (x y : Fin n → Bool) (t : ℕ) (ht : t < C.gates.length)
    (hop : (C.gates[t]).op = GateOp.and ∨ (C.gates[t]).op = GateOp.or)
    (a b : ℕ) (hab : (C.gates[t]).inputs = [a, b])
    (ha : Rd C n x t a = true → Rd C n y t a = true)
    (hb : Rd C n x t b = true → Rd C n y t b = true) :
    Wv C n x (n + t) = true → Wv C n y (n + t) = true := by
  rw [Wv_two C n x t ht a b hab, Wv_two C n y t ht a b hab]
  rcases hop with h | h
  · rw [h, eval_and, eval_and]
    intro hh
    rw [Bool.and_eq_true] at hh ⊢
    exact ⟨ha hh.1, hb hh.2⟩
  · rw [h, eval_or, eval_or]
    intro hh
    rw [Bool.or_eq_true] at hh ⊢
    exact hh.imp ha hb

theorem Wv_mono (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ j, Wv C n x j = true → Wv C n y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  by_cases hin : j < n
  · have h1 := Wv_input C n x ⟨j, hin⟩
    have h2 := Wv_input C n y ⟨j, hin⟩
    simp only at h1 h2
    rw [h1, h2]
    exact hxy _
  · by_cases hbig : n + C.gates.length ≤ j
    · rw [Wv_big C n x j hbig]
      intro h
      exact absurd h (by simp)
    · obtain ⟨t, rfl⟩ : ∃ t, j = n + t := ⟨j - n, by omega⟩
      have ht : t < C.gates.length := by omega
      obtain ⟨hop, hlen⟩ := hg (C.gates[t]) (List.getElem_mem ht)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
      apply gate_lift C n x y t ht hop a b hab
      · unfold Rd
        split_ifs with hlt
        · exact ih a hlt
        · exact id
      · unfold Rd
        split_ifs with hlt
        · exact ih b hlt
        · exact id

theorem priv_range (C : Circuit) (n : ℕ) (j : ℕ) (h2 : 2 ≤ (Ls C n j).card) :
    n ≤ j ∧ j < n + C.gates.length := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have hsub : Ls C n j ⊆ {⟨j, hlt⟩} := by
      intro p hp
      rw [mem_Ls] at hp
      have h1 := Wv_input C n (pt n p) ⟨j, hlt⟩
      simp only at h1
      rw [h1] at hp
      simp only [pt, decide_eq_true_eq] at hp
      rw [Finset.mem_singleton]
      exact hp.symm
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  · by_contra hge
    push_neg at hge
    have hemp : Ls C n j = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      rw [mem_Ls, Wv_big C n _ j hge] at hp
      exact Bool.false_ne_true hp
    rw [hemp] at h2
    simp at h2

theorem inv (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) :
    ∀ N : ℕ, ∀ J : Finset ℕ, (∀ j ∈ J, j < N) →
      ∃ (D : Finset ℕ) (A B : Finset (Fin n)),
        (∀ t ∈ D, n + t < N ∧ t < C.gates.length ∧ Ls C n (n + t) ⊆ S ∧
          2 ≤ (Ls C n (n + t)).card) ∧
        (∀ q ∈ A, q ∉ S) ∧
        A.card + B.card ≤ D.card + J.card ∧
        ∀ j ∈ J, ∀ p ∈ S, p ∉ B → Wv C n (pt n p) j = true → Wv C n (ind n A) j = true := by
  intro N
  induction N with
  | zero =>
    intro J hJ
    have hJe : J = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      have := hJ j hj
      omega
    subst hJe
    exact ⟨∅, ∅, ∅, by simp, by simp, by simp, by simp⟩
  | succ N ih =>
    intro J hJ
    by_cases hN : N ∈ J
    · have hJ0 : ∀ j ∈ J.erase N, j < N := by
        intro j hj
        rw [Finset.mem_erase] at hj
        have := hJ j hj.2
        omega
      have hcard : (J.erase N).card + 1 = J.card := Finset.card_erase_add_one hN
      by_cases hsub : Ls C n N ⊆ S
      · by_cases hpriv : 2 ≤ (Ls C n N).card
        · obtain ⟨hnN, hNlt⟩ := priv_range C n N hpriv
          obtain ⟨t, rfl⟩ : ∃ t, N = n + t := ⟨N - n, by omega⟩
          have ht : t < C.gates.length := by omega
          obtain ⟨hop, hlen⟩ := hg (C.gates[t]) (List.getElem_mem ht)
          obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
          have hJ' : ∀ j ∈ J.erase (n + t) ∪ (({a, b} : Finset ℕ).filter (fun i => i < n + t)),
              j < n + t := by
            intro j hj
            rw [Finset.mem_union] at hj
            rcases hj with hj | hj
            · exact hJ0 j hj
            · exact (Finset.mem_filter.mp hj).2
          obtain ⟨D, A, B, hD, hA, hc, hp⟩ := ih _ hJ'
          have htD : t ∉ D := by
            intro h
            have := (hD t h).1
            omega
          have hJc : (J.erase (n + t) ∪ (({a, b} : Finset ℕ).filter (fun i => i < n + t))).card ≤
              (J.erase (n + t)).card + 2 := by
            have h1 := Finset.card_union_le (J.erase (n + t))
              (({a, b} : Finset ℕ).filter (fun i => i < n + t))
            have h2 := Finset.card_filter_le ({a, b} : Finset ℕ) (fun i => i < n + t)
            have h3 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
            omega
          refine ⟨insert t D, A, B, ?_, hA, ?_, ?_⟩
          · intro t' ht'
            rw [Finset.mem_insert] at ht'
            rcases ht' with rfl | ht'
            · exact ⟨by omega, ht, hsub, hpriv⟩
            · exact ⟨by have := (hD t' ht').1; omega, (hD t' ht').2⟩
          · rw [Finset.card_insert_of_notMem htD]
            omega
          · intro j hj p hpS hpB
            by_cases hjN : j = n + t
            · subst hjN
              apply gate_lift C n (pt n p) (ind n A) t ht hop a b hab
              · unfold Rd
                split_ifs with hlt
                · intro hw
                  refine hp a ?_ p hpS hpB hw
                  rw [Finset.mem_union]
                  right
                  rw [Finset.mem_filter]
                  exact ⟨by simp, hlt⟩
                · exact id
              · unfold Rd
                split_ifs with hlt
                · intro hw
                  refine hp b ?_ p hpS hpB hw
                  rw [Finset.mem_union]
                  right
                  rw [Finset.mem_filter]
                  exact ⟨by simp, hlt⟩
                · exact id
            · refine hp j ?_ p hpS hpB
              rw [Finset.mem_union]
              left
              rw [Finset.mem_erase]
              exact ⟨hjN, hj⟩
        · obtain ⟨D, A, B, hD, hA, hc, hp⟩ := ih _ hJ0
          have hL1 : (Ls C n N).card ≤ 1 := by omega
          refine ⟨D, A, B ∪ Ls C n N, ?_, hA, ?_, ?_⟩
          · intro t' ht'
            exact ⟨by have := (hD t' ht').1; omega, (hD t' ht').2⟩
          · have := Finset.card_union_le B (Ls C n N)
            omega
          · intro j hj p hpS hpB
            rw [Finset.mem_union, not_or] at hpB
            by_cases hjN : j = N
            · subst hjN
              intro hw
              exact absurd ((mem_Ls C n j p).2 hw) hpB.2
            · refine hp j ?_ p hpS hpB.1
              rw [Finset.mem_erase]
              exact ⟨hjN, hj⟩
      · obtain ⟨q, hqL, hqS⟩ := Finset.not_subset.mp hsub
        obtain ⟨D, A, B, hD, hA, hc, hp⟩ := ih _ hJ0
        have hmono : ∀ j, Wv C n (ind n A) j = true → Wv C n (ind n (insert q A)) j = true := by
          apply Wv_mono C n hg
          intro r hr
          simp only [ind, decide_eq_true_eq] at hr ⊢
          exact Finset.mem_insert_of_mem hr
        refine ⟨D, insert q A, B, ?_, ?_, ?_, ?_⟩
        · intro t' ht'
          exact ⟨by have := (hD t' ht').1; omega, (hD t' ht').2⟩
        · intro r hr
          rw [Finset.mem_insert] at hr
          rcases hr with rfl | hr
          · exact hqS
          · exact hA r hr
        · have := Finset.card_insert_le q A
          omega
        · intro j hj p hpS hpB
          by_cases hjN : j = N
          · subst hjN
            intro _
            apply Wv_mono C n hg (pt n q) (ind n (insert q A)) ?_ j ((mem_Ls C n j q).1 hqL)
            intro r hr
            simp only [pt, ind, decide_eq_true_eq] at hr ⊢
            rw [hr]
            exact Finset.mem_insert_self q A
          · intro hw
            apply hmono
            refine hp j ?_ p hpS hpB hw
            rw [Finset.mem_erase]
            exact ⟨hjN, hj⟩
    · obtain ⟨D, A, B, hD, hA, hc, hp⟩ := ih J (by
        intro j hj
        have := hJ j hj
        have hne : j ≠ N := fun h => hN (h ▸ hj)
        omega)
      refine ⟨D, A, B, ?_, hA, hc, hp⟩
      intro t' ht'
      exact ⟨by have := (hD t' ht').1; omega, (hD t' ht').2⟩

theorem main : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS h2 hg hL hK hck hcS
  classical
  have key : ∀ i : Fin m, c i ≤ ((Finset.range C.gates.length).filter (fun t =>
      PEqualNP.Outside.L_meta_273.Ls C n (n + t) ⊆ S i ∧
        2 ≤ (PEqualNP.Outside.L_meta_273.Ls C n (n + t)).card)).card := by
    intro i
    obtain ⟨D, A, B, hD, hA, hc, hp⟩ :=
      PEqualNP.Outside.L_meta_273.inv C n hg (S i) (o i + 1) {o i} (by simp)
    have hDP : D ⊆ (Finset.range C.gates.length).filter (fun t =>
        PEqualNP.Outside.L_meta_273.Ls C n (n + t) ⊆ S i ∧
          2 ≤ (PEqualNP.Outside.L_meta_273.Ls C n (n + t)).card) := by
      intro t ht
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨(hD t ht).2.1, (hD t ht).2.2⟩
    have hDc : c i ≤ D.card := by
      rw [Finset.card_singleton] at hc
      by_cases hAk : A.card ≤ k
      · have hfilt : Finset.univ.filter (fun q : Fin n =>
            PEqualNP.Outside.L_meta_273.ind n A q = true) = A := by
          ext q
          simp [PEqualNP.Outside.L_meta_273.ind]
        have hfalse : PEqualNP.Outside.L_meta_273.Wv C n (PEqualNP.Outside.L_meta_273.ind n A) (o i) = false := by
          apply hK i (PEqualNP.Outside.L_meta_273.ind n A)
          · rw [hfilt]
            exact hAk
          · intro q hq
            simp only [PEqualNP.Outside.L_meta_273.ind, decide_eq_false_iff_not]
            exact fun h => hA q h hq
        have hSB : S i ⊆ B := by
          intro p hpS
          by_contra hpB
          have h1 := hp (o i) (Finset.mem_singleton_self _) p hpS hpB ((hL i p).2 hpS)
          rw [hfalse] at h1
          exact Bool.false_ne_true h1
        have h3 := Finset.card_le_card hSB
        have h4 := hcS i
        omega
      · have h4 := hck i
        omega
    exact le_trans hDc (Finset.card_le_card hDP)
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)), i ≠ j →
      Disjoint ((Finset.range C.gates.length).filter (fun t =>
        PEqualNP.Outside.L_meta_273.Ls C n (n + t) ⊆ S i ∧
          2 ≤ (PEqualNP.Outside.L_meta_273.Ls C n (n + t)).card))
        ((Finset.range C.gates.length).filter (fun t =>
        PEqualNP.Outside.L_meta_273.Ls C n (n + t) ⊆ S j ∧
          2 ≤ (PEqualNP.Outside.L_meta_273.Ls C n (n + t)).card)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro t hti htj
    rw [Finset.mem_filter] at hti htj
    have hsub : PEqualNP.Outside.L_meta_273.Ls C n (n + t) ⊆ S i ∩ S j :=
      Finset.subset_inter hti.2.1 htj.2.1
    have h5 := Finset.card_le_card hsub
    have h6 := hS i j hij
    have h7 := hti.2.2
    omega
  calc ∑ i : Fin m, c i
      ≤ ∑ i : Fin m, ((Finset.range C.gates.length).filter (fun t =>
          PEqualNP.Outside.L_meta_273.Ls C n (n + t) ⊆ S i ∧
            2 ≤ (PEqualNP.Outside.L_meta_273.Ls C n (n + t)).card)).card :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = ((Finset.univ : Finset (Fin m)).biUnion (fun i => (Finset.range C.gates.length).filter (fun t =>
          PEqualNP.Outside.L_meta_273.Ls C n (n + t) ⊆ S i ∧
            2 ≤ (PEqualNP.Outside.L_meta_273.Ls C n (n + t)).card))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.range C.gates.length).card := by
        apply Finset.card_le_card
        intro t ht
        rw [Finset.mem_biUnion] at ht
        obtain ⟨i, _, hi⟩ := ht
        exact (Finset.mem_filter.mp hi).1
    _ = C.size := by
        rw [Finset.card_range]
        rfl

end PEqualNP.Outside.L_meta_273

theorem PEqualNP.Outside.L_meta_273 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 3 → ℕ), C.size ≤ 5 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 3, (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i) ∧ ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C, o, hsz, hg, h⟩
  have key := PEqualNP.Outside.L_meta_273.main 6 3 2
    (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) C o (fun _ => 2)
    (by decide) (by decide) hg (fun i p => (h i).1 p) (fun i x hx hq => (h i).2 x hx hq)
    (by intro i; exact le_refl 2) (by decide)
  have h6 : ∑ i : Fin 3, (fun _ : Fin 3 => 2) i = 6 := by
    simp
  rw [h6] at key
  omega
