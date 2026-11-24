import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1373

open PEqualNP.CircuitLowerBounds

abbrev CountHyp := (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size)

abbrev ReduceHyp := (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)))

theorem linesHit {n m q : ℕ} (F : Fin m → Finset (Fin n))
    (reg : ∀ p : Fin n,(Finset.univ.filter (fun i : Fin m => p ∈ F i)).card = q+1)
    (pair : ∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ F i ∧ v ∈ F i)
    (Y : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin m => ¬ Disjoint Y (F i))).card ≤ q*Y.card+1 := by
  classical
  let lines (p : Fin n) := Finset.univ.filter (fun i : Fin m => p ∈ F i)
  have aux (A : Finset (Fin n)) : (A.biUnion lines).card ≤ q*A.card+1 := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert p A hp ih =>
      rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hp,Nat.mul_add,Nat.mul_one]
      cases A.eq_empty_or_nonempty with
      | inl h => subst A; simpa [lines] using (reg p).le
      | inr h =>
        obtain ⟨r,hr⟩ := h
        have hpr : p ≠ r := fun eq => hp (eq ▸ hr)
        obtain ⟨i,hpi,hri⟩ := pair p r hpr
        have hi : i ∈ lines p ∩ A.biUnion lines := Finset.mem_inter.mpr
          ⟨by simpa [lines] using hpi,Finset.mem_biUnion.mpr ⟨r,hr,by simpa [lines] using hri⟩⟩
        have hpos : 0 < (lines p ∩ A.biUnion lines).card := Finset.card_pos.mpr ⟨i,hi⟩
        have hu := Finset.card_union_add_card_inter (lines p) (A.biUnion lines)
        have hcnt : (lines p).card = q+1 := reg p
        omega
  apply le_trans _ (aux Y)
  apply Finset.card_le_card
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨p,hp,hpi⟩ := h
  exact Finset.mem_biUnion.mpr ⟨p,hp,by simpa [lines] using hpi⟩

theorem pair_of_count {n q : ℕ} (hn : n = q*q+q+1) (S : Fin n → Finset (Fin n))
    (hs : ∀ i, (S i).card = q+1)
    (hd : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (reg : ∀ p : Fin n, (Finset.univ.filter (fun i : Fin n => p ∈ S i)).card = q+1) :
    ∀ u v : Fin n, u ≠ v → ∃ i : Fin n, u ∈ S i ∧ v ∈ S i := by
  classical
  intro u v huv
  let Lu := Finset.univ.filter (fun i : Fin n => u ∈ S i)
  let A (i : Fin n) := (S i).erase u
  have hdisj : ∀ i ∈ Lu, ∀ i' ∈ Lu, i ≠ i' → Disjoint (A i) (A i') := by
    intro i hi i' hi' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hui : u ∈ S i := (Finset.mem_filter.mp hi).2
    have hui' : u ∈ S i' := (Finset.mem_filter.mp hi').2
    have hxi := Finset.mem_erase.mp hx
    have hxi' := Finset.mem_erase.mp hx'
    have hsub : ({u, x} : Finset (Fin n)) ⊆ S i ∩ S i' := by
      intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · rw [hz]; exact Finset.mem_inter.mpr ⟨hui, hui'⟩
      · rw [Finset.mem_singleton.mp hz]; exact Finset.mem_inter.mpr ⟨hxi.2, hxi'.2⟩
    have h2 : ({u, x} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hxi.1)
    have h3 := Finset.card_le_card hsub
    have h4 := hd i i' hne
    omega
  have hcard : (Lu.biUnion A).card = (q+1)*q := by
    rw [Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (fun i hi => show (A i).card = q from by
      have hui : u ∈ S i := (Finset.mem_filter.mp hi).2
      simp only [A]; rw [Finset.card_erase_of_mem hui, hs]; rfl)]
    simp [reg u, Lu]
  have hu : u ∉ Lu.biUnion A := by simp [A]
  have huniv : insert u (Lu.biUnion A) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem hu, hcard, Fintype.card_fin, hn]; ring
  have hv : v ∈ insert u (Lu.biUnion A) := by rw [huniv]; exact Finset.mem_univ v
  rcases Finset.mem_insert.mp hv with h | h
  · exact (huv h.symm).elim
  · obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp h
    exact ⟨i, (Finset.mem_filter.mp hi).2, (Finset.mem_erase.mp hvi).2⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (L : List Gate) (W : List Bool) : List Bool := L.foldl step W

def ren (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map σ⟩

theorem run_cons (g : Gate) (L : List Gate) (W : List Bool) : run (g :: L) W = run L (step W g) := rfl

theorem run_append (A B : List Gate) (W : List Bool) : run (A ++ B) W = run B (run A W) := by
  simp [run, List.foldl_append]

theorem step_length (W : List Bool) (g : Gate) : (step W g).length = W.length + 1 := by
  simp [step]

theorem run_length : ∀ (L : List Gate) (W : List Bool), (run L W).length = W.length + L.length
  | [], W => by simp [run]
  | g :: L, W => by
    rw [run_cons, run_length L, step_length, List.length_cons]; omega

theorem getD_snoc_lt (W : List Bool) (v : Bool) (i : ℕ) (h : i < W.length) :
    (W ++ [v]).getD i false = W.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (W : List Bool) (v : Bool) : (W ++ [v]).getD W.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem run_getD_lt : ∀ (L : List Gate) (W : List Bool) (i : ℕ), i < W.length →
    (run L W).getD i false = W.getD i false
  | [], _, _, _ => rfl
  | g :: L, W, i, h => by
    rw [run_cons, run_getD_lt L _ i (by rw [step_length]; omega)]
    exact getD_snoc_lt _ _ _ h

theorem sim (σ : ℕ → ℕ) (d : ℕ) : ∀ (L : List Gate) (W W' : List Bool),
    W'.length = W.length + d →
    (∀ i, W.length ≤ i → σ i = i + d) →
    (∀ i, i < W.length → σ i < W.length + d) →
    (∀ i, W'.getD (σ i) false = W.getD i false) →
    ∀ i, (run (L.map (ren σ)) W').getD (σ i) false = (run L W).getD i false
  | [], _, _, _, _, _, h => h
  | g :: L, W, W', hl, hge, hlt, h => by
    rw [List.map_cons, run_cons, run_cons]
    have hv : (ren σ g).op.eval ((ren σ g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [ren, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    apply sim σ d L
    · rw [step_length, step_length]; omega
    · intro i hi; rw [step_length] at hi; exact hge i (by omega)
    · intro i hi; rw [step_length] at hi ⊢
      rcases Nat.lt_or_ge i W.length with h1 | h1
      · have := hlt i h1; omega
      · have := hge i h1; omega
    · intro i
      unfold step
      rw [hv]
      rcases Nat.lt_trichotomy i W.length with h1 | h1 | h1
      · have h2 := hlt i h1
        rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ h1]; exact h i
      · have h2 := hge i h1.ge
        rw [h2, h1, ← hl, getD_snoc_eq, getD_snoc_eq]
      · have h2 := hge i h1.le
        rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]

theorem mono_run : ∀ (L : List Gate) (W W' : List Bool),
    (∀ g ∈ L, g.op = GateOp.and ∨ g.op = GateOp.or) → W'.length = W.length →
    (∀ i, W.getD i false = true → W'.getD i false = true) →
    ∀ i, (run L W).getD i false = true → (run L W').getD i false = true
  | [], _, _, _, _, h => h
  | g :: L, W, W', ha, hl, h => by
    rw [run_cons, run_cons]
    apply mono_run L _ _ (fun g' hg' => ha g' (List.mem_cons_of_mem _ hg'))
    · rw [step_length, step_length, hl]
    · intro i
      have hv : g.op.eval (g.inputs.map fun i => W.getD i false) = true →
          g.op.eval (g.inputs.map fun i => W'.getD i false) = true := by
        rcases ha g List.mem_cons_self with ho | ho
        · rw [ho]
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
          intro hh x hx; exact h _ (hh x hx)
        · rw [ho]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
          rintro ⟨x, hx, hh⟩; exact ⟨x, hx, h _ hh⟩
      unfold step
      rcases Nat.lt_trichotomy i W.length with h1 | h1 | h1
      · rw [getD_snoc_lt _ _ _ h1, getD_snoc_lt _ _ _ (hl ▸ h1)]; exact h i
      · rw [h1, getD_snoc_eq, ← hl, getD_snoc_eq]; exact hv
      · rw [getD_ge _ _ (by simp; omega)]; simp

def s1 (n : ℕ) (i : ℕ) : ℕ := if i < n then i else i + 1

def s2 (n j : ℕ) (i : ℕ) : ℕ :=
  if i < n then i else if i < n + j then i + 1 else if i = n + j then n else i

def cut (n : ℕ) (P Q : List Gate) : List Gate :=
  P.map (ren (s1 n)) ++ Q.map (ren (s2 n P.length))

theorem cut_correct (P Q : List Gate) (g : Gate) (hg : g.op = GateOp.not) (X : List Bool) (b : Bool)
    (hb : (!((g.inputs.map fun i => (run P X).getD i false).headD false)) = b) :
    ∀ i, (run (cut X.length P Q) (X ++ [b])).getD (s2 X.length P.length i) false
      = (run (P ++ g :: Q) X).getD i false := by
  intro i
  have h1 : ∀ i, (run (P.map (ren (s1 X.length))) (X ++ [b])).getD (s1 X.length i) false
      = (run P X).getD i false := by
    apply sim (s1 X.length) 1 P X (X ++ [b])
    · simp
    · intro i hi; unfold s1; split_ifs <;> omega
    · intro i hi; unfold s1; split_ifs; omega
    · intro i; unfold s1; split_ifs with h
      · exact getD_snoc_lt _ _ _ h
      · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by omega)]
  have hlen : (run P X).length = X.length + P.length := run_length P X
  have hlen' : (run (P.map (ren (s1 X.length))) (X ++ [b])).length = X.length + P.length + 1 := by
    rw [run_length]; simp; omega
  rw [cut, run_append, run_append, run_cons]
  have hstep : step (run P X) g = run P X ++ [b] := by
    unfold step; rw [hg]; simp only [GateOp.eval]; rw [hb]
  rw [hstep]
  apply sim (s2 X.length P.length) 0 Q (run P X ++ [b]) (run (P.map (ren (s1 X.length))) (X ++ [b]))
  · rw [hlen']; simp [hlen]
  · intro i hi; simp [hlen] at hi; unfold s2; split_ifs <;> omega
  · intro i hi; simp [hlen] at hi ⊢; unfold s2; split_ifs <;> omega
  · intro i
    unfold s2; split_ifs with a b' c
    · rw [getD_snoc_lt _ _ _ (by omega)]
      have := h1 i; simp [s1, a] at this; exact this
    · rw [getD_snoc_lt _ _ _ (by omega)]
      have := h1 i; simp [s1, a] at this; exact this
    · rw [c, ← hlen, getD_snoc_eq, run_getD_lt _ _ _ (by simp)]; exact getD_snoc_eq X b
    · rw [getD_ge _ _ (by omega), getD_ge _ _ (by simp [hlen]; omega)]

def supp {n : ℕ} (x : Fin n → Bool) := Finset.univ.filter (fun p => x p = true)

theorem core (hc : CountHyp) (hr : ReduceHyp) {n m q k : ℕ}
    (hk : 1 ≤ k) (hq : 1 ≤ q) (F : Fin m → Finset (Fin n)) (Y Z : Finset (Fin n))
    (hs : ∀ i, (F i).card=q+1) (hd : ∀ i j, i≠j → (F i ∩ F j).card ≤ 1)
    (L : List Gate) (out : Fin m → ℕ)
    (ha : ∀ g ∈ L, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length ≤ 2)
    (win : ∀ i (x : Fin n → Bool), (supp x).card ≤ k →
      Circuit.eval ⟨L,out i⟩ (List.ofFn (fun p => if p ∈ Y then true else if p ∈ Z then false else x p)) =
      decide (∃ p ∈ F i, x p = true)) :
    m * min k q ≤ L.length := by
  classical
  obtain ⟨D,r,hD,hsize,respond⟩ := hr n L Y Z ha
  have emptyS : supp (fun _ : Fin n => false) = ∅ := by ext; simp [supp]
  have singS (p : Fin n) : supp (fun a => decide (a=p)) = {p} := by ext; simp [supp]
  have live (i : Fin m) : ∃ x y : Fin n → Bool,
      Circuit.eval ⟨L,out i⟩ (List.ofFn (fun p => if p ∈ Y then true else if p ∈ Z then false else x p)) ≠
      Circuit.eval ⟨L,out i⟩ (List.ofFn (fun p => if p ∈ Y then true else if p ∈ Z then false else y p)) := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (F i).card by rw [hs]; omega)
    refine ⟨fun _ => false,fun a => decide (a=p),?_⟩
    rw [win i _ (by simp [emptyS]), win i _ (by simpa [singS] using hk)]
    simp [hp]
  have result (i : Fin m) (x : Fin n → Bool) (hx : (supp x).card ≤ k) :
      Circuit.eval ⟨D,r (out i)⟩ (List.ofFn x) = decide (∃ p ∈ F i, x p = true) := by
    rw [show Circuit.eval ⟨D,r (out i)⟩ (List.ofFn x) = _ from respond _ (live i) x, win i x hx]
  have bound := hc n m k F ⟨D,0⟩ (fun i => r (out i)) (fun _ => min k q) hd
    (fun i => by rw [hs]; omega) hD
    (fun i p => by
      change Circuit.eval ⟨D,r (out i)⟩ _ = true ↔ _
      rw [result i _ (by simpa [singS] using hk)]
      simp)
    (fun i x hx hnone => by
      change Circuit.eval ⟨D,r (out i)⟩ _ = false
      rw [result i x hx]
      simpa using hnone)
    (fun _ => min_le_left _ _) (fun i => by rw [hs]; omega)
  simpa [Circuit.size] using le_trans bound hsize

theorem side (hc : CountHyp) (hr : ReduceHyp) {n m q k : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q)
    (F : Fin m → Finset (Fin n)) (T0 : Finset (Fin n)) (b : Bool)
    (hs : ∀ i, (F i).card = q+1) (hd : ∀ i j, i ≠ j → (F i ∩ F j).card ≤ 1)
    (hdis : ∀ i, Disjoint T0 (F i))
    (P Q : List Gate) (g : Gate) (hg : g.op = GateOp.not)
    (hP : ∀ g ∈ P, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length ≤ 2)
    (hQ : ∀ g ∈ Q, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ)
    (hnv : ∀ x : Fin n → Bool, (supp x).card ≤ k →
      (!((g.inputs.map fun i => (run P (List.ofFn (fun p => decide (p ∈ T0) || x p))).getD i false).headD false)) = b)
    (hout : ∀ i (y : Fin n → Bool), Circuit.eval ⟨P ++ g :: Q, out i⟩ (List.ofFn y) =
      decide (∃ v ∈ F i, y v = true)) :
    m * min k q ≤ P.length + Q.length := by
  classical
  let F' (i : Fin m) : Finset (Fin (n+1)) := (F i).map Fin.castSuccEmb
  let Y : Finset (Fin (n+1)) := T0.map Fin.castSuccEmb ∪ (if b = true then {Fin.last n} else ∅)
  let Z : Finset (Fin (n+1)) := {Fin.last n}
  have hcut : (cut n P Q).length = P.length + Q.length := by simp [cut]
  rw [← hcut]
  apply core hc hr hk hq F' Y Z (fun i => by simp [F', hs]) (fun i j hij => by
      have : F' i ∩ F' j = (F i ∩ F j).map Fin.castSuccEmb := by simp [F', Finset.map_inter]
      rw [this, Finset.card_map]; exact hd i j hij) (cut n P Q) (fun i => s2 n P.length (out i))
  · intro g' hg'
    simp only [cut, List.mem_append, List.mem_map] at hg'
    rcases hg' with ⟨g0, h0, rfl⟩ | ⟨g0, h0, rfl⟩
    · simpa [ren] using hP g0 h0
    · simpa [ren] using hQ g0 h0
  · intro i x' hx'
    let x : Fin n → Bool := fun p => x' p.castSucc
    let y : Fin n → Bool := fun p => decide (p ∈ T0) || x p
    have hxk : (supp x).card ≤ k := by
      refine le_trans ?_ hx'
      rw [← Finset.card_map Fin.castSuccEmb]
      apply Finset.card_le_card
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
      simpa [supp, x] using hp
    have hA : List.ofFn (fun p' : Fin (n+1) => if p' ∈ Y then true else if p' ∈ Z then false else x' p')
        = List.ofFn y ++ [b] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      congr 1
      · congr 1; funext p
        by_cases hp : p ∈ T0 <;> cases b <;>
          simp [Y, Z, y, x, hp, (Fin.castSucc_lt_last p).ne]
      · cases b <;> simp [Y, Z]
    rw [hA]
    have hcc := cut_correct P Q g hg (List.ofFn y) b (hnv x hxk) (out i)
    rw [List.length_ofFn] at hcc
    change (run (cut n P Q) (List.ofFn y ++ [b])).getD (s2 n P.length (out i)) false = _
    rw [hcc]
    have hthis := hout i y
    change (run (P ++ g :: Q) (List.ofFn y)).getD (out i) false = _ at hthis
    rw [hthis]
    congr 1
    apply propext
    constructor
    · rintro ⟨v, hv, hyv⟩
      have hvT : v ∉ T0 := fun h => Finset.disjoint_left.mp (hdis i) h hv
      refine ⟨v.castSucc, Finset.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
      simpa [y, x, hvT] using hyv
    · rintro ⟨p', hp', hx⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hp'
      exact ⟨v, hv, by simp only [y, x, Bool.or_eq_true]; right; exact hx⟩

theorem main (hc : CountHyp) (hr : ReduceHyp) (q n : ℕ) (hn : n = q*q+q+1)
    (S : Fin n → Finset (Fin n)) (gates : List Gate) (out : Fin n → ℕ)
    (hq : 2 ≤ q) (hs : ∀ i, (S i).card = q + 1) (hd : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (reg : ∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (hout : ∀ (w : Fin n) (x : Fin n → Bool), Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
      decide (∃ v ∈ S w, x v = true)) :
    ∃ w : ℕ, 1 ≤ w ∧ 1 + max (n * min (w - 1) q) (q * (n - (w * q + 1))) ≤ gates.length := by
  classical
  by_cases hex : ∃ j : Fin gates.length, (gates.get j).op = GateOp.not
  · obtain ⟨j, hj⟩ := hex
    obtain ⟨g, P, Q, hsplit, hgop⟩ : ∃ g P Q, gates = P ++ g :: Q ∧ g.op = GateOp.not :=
      ⟨gates.get j, gates.take j, gates.drop (j+1), by simp, hj⟩
    subst hsplit
    have hP : ∀ g' ∈ P, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
      intro g' hg'
      obtain ⟨hop, hlen⟩ := hgates g' (by simp [hg'])
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg'
        have h1 := huniq ⟨t, by simp; omega⟩ ⟨P.length, by simp⟩
          (by simpa [List.getElem_append_left ht] using h) (by simpa using hgop)
        simp [Fin.ext_iff] at h1; omega
    have hQ : ∀ g' ∈ Q, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
      intro g' hg'
      obtain ⟨hop, hlen⟩ := hgates g' (by simp [hg'])
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg'
        have h1 := huniq ⟨P.length + (t + 1), by simp; omega⟩ ⟨P.length, by simp⟩
          (by simpa using h) (by simpa using hgop)
        simp [Fin.ext_iff] at h1
    have hlen : (P ++ g :: Q).length = P.length + Q.length + 1 := by simp; omega
    rw [hlen]
    let nvf (y : Fin n → Bool) : Bool :=
      !((g.inputs.map fun i => (run P (List.ofFn y)).getD i false).headD false)
    have e0 : ∀ x : Fin n → Bool, (fun p => decide (p ∈ (∅ : Finset (Fin n))) || x p) = x := by
      intro x; funext p; simp
    have sideA : ∀ k, 1 ≤ k → (∀ x : Fin n → Bool, (supp x).card ≤ k → nvf x = true) →
        n * min k q ≤ P.length + Q.length := by
      intro k hk hx
      exact side hc hr hk (by omega) S ∅ true hs hd (fun i => Finset.disjoint_empty_left _)
        P Q g hgop hP hQ out
        (fun x hxk => by rw [e0]; exact hx x hxk) (fun i y => hout i y)
    by_cases hB : ∃ y, nvf y = false
    · have hw : ∃ w, ∃ y, (supp y).card = w ∧ nvf y = false := by
        obtain ⟨y, hy⟩ := hB; exact ⟨_, y, rfl, hy⟩
      obtain ⟨y0, hy0c, hy0⟩ := Nat.find_spec hw
      have hmin : ∀ y, (supp y).card < Nat.find hw → nvf y = true := by
        intro y hy
        have hnot := Nat.find_min hw hy
        cases h : nvf y
        · exact (hnot ⟨y, rfl, h⟩).elim
        · rfl
      generalize Nat.find hw = w0 at hy0c hmin
      have hfalse : ∀ x : Fin n → Bool, nvf (fun p => decide (p ∈ supp y0) || x p) = false := by
        intro x
        have hm := mono_run P (List.ofFn y0) (List.ofFn (fun p => decide (p ∈ supp y0) || x p))
          (fun g' hg' => (hP g' hg').1) (by simp)
          (by
            intro i hi
            by_cases hin : i < n
            · simp [List.getD_eq_getElem?_getD, hin] at hi ⊢
              left; simp [supp, hi]
            · simp [List.getD_eq_getElem?_getD, hin] at hi)
        simp only [nvf] at hy0 ⊢
        cases hin : g.inputs with
        | nil => rw [hin] at hy0; simp at hy0
        | cons a l =>
          rw [hin] at hy0
          simp at hy0 ⊢
          exact hm a hy0
      have hBb : (Finset.univ.filter (fun i : Fin n => Disjoint (supp y0) (S i))).card * min q q
          ≤ P.length + Q.length := by
        let I := Finset.univ.filter (fun i : Fin n => Disjoint (supp y0) (S i))
        let e : Fin I.card ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
        exact side hc hr (by omega) (by omega) (fun i => S (e i).val) (supp y0) false (fun i => hs _)
          (fun i j hij => hd _ _ (fun eq => hij (e.injective (Subtype.ext eq))))
          (fun i => (Finset.mem_filter.mp (e i).property).2) P Q g hgop hP hQ
          (fun i => out (e i).val)
          (fun x _ => hfalse x) (fun i y => hout _ y)
      have hhit := linesHit S reg (pair_of_count hn S hs hd reg) (supp y0)
      have hsum := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => Disjoint (supp y0) (S i))
      rw [hy0c] at hhit
      rw [min_self] at hBb
      simp only [Finset.card_univ, Fintype.card_fin] at hsum
      generalize (Finset.univ.filter (fun i : Fin n => Disjoint (supp y0) (S i))).card = cI at hBb hsum
      generalize (Finset.univ.filter (fun i : Fin n => ¬ Disjoint (supp y0) (S i))).card = cH at hhit hsum
      refine ⟨max w0 1, le_max_right _ _, ?_⟩
      have hA : n * min (max w0 1 - 1) q ≤ P.length + Q.length := by
        by_cases h1 : w0 ≤ 1
        · have h0 : max w0 1 - 1 = 0 := by omega
          rw [h0]; simp
        · have h0 : max w0 1 - 1 = w0 - 1 := by omega
          rw [h0]
          exact sideA (w0 - 1) (by omega) (fun x hx => hmin x (by omega))
      have hB2 : q * (n - (max w0 1 * q + 1)) ≤ P.length + Q.length := by
        have h4 : q * w0 ≤ max w0 1 * q := by
          rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (le_max_left _ _)
        have h3 : n - (max w0 1 * q + 1) ≤ cI := by omega
        calc q * (n - (max w0 1 * q + 1)) ≤ q * cI := Nat.mul_le_mul_left _ h3
          _ = cI * q := Nat.mul_comm _ _
          _ ≤ _ := hBb
      have hmx := max_le hA hB2
      omega
    · have hall : ∀ y, nvf y = true := by
        intro y
        cases h : nvf y
        · exact (hB ⟨y, h⟩).elim
        · rfl
      have hA := sideA q (by omega) (fun x _ => hall x)
      refine ⟨q + 1, by omega, ?_⟩
      have h1 : q + 1 - 1 = q := by omega
      have h2 : n - ((q+1)*q+1) = 0 := by
        have h5 : (q+1)*q = q*q+q := by ring
        rw [hn, h5]; omega
      rw [min_self] at hA
      rw [h1, h2, min_self, Nat.mul_zero, max_eq_left (Nat.zero_le _)]
      omega
  · have hall : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hgates g hg
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
        exact (hex ⟨⟨t, ht⟩, by simpa using h⟩).elim
    have hb := core hc hr (k := q) (q := q) (by omega) (by omega) S ∅ ∅ hs hd gates out hall
      (fun i x _ => by simpa using hout i x)
    refine ⟨1, le_refl _, ?_⟩
    rw [min_self] at hb
    have h2 : n - (1*q+1) = q*q := by rw [hn]; omega
    have h3 : n * q = q*(q*q) + q*q + q := by rw [hn]; ring
    have h6 : 1 ≤ q*q := Nat.mul_pos (by omega) (by omega)
    rw [h2, Nat.sub_self, Nat.zero_min, Nat.mul_zero, max_eq_right (Nat.zero_le _)]
    omega

end PEqualNP.Outside.L_meta_1373

open PEqualNP.Outside.L_meta_1373 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1373 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1))) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q^2+q+1) → ℕ), 2 ≤ q → (∀ i, (S i).card = q + 1) → (∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ (w : Fin (q^2+q+1)) (x : Fin (q^2+q+1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → ∃ w : ℕ, 1 ≤ w ∧ 1 + max ((q^2+q+1) * min (w - 1) q) (q * ((q^2+q+1) - (w * q + 1))) ≤ gates.length := by
  intro hc hr q S gates out hq hs hd reg hgates huniq hout
  exact PEqualNP.Outside.L_meta_1373.main hc hr q _ (by ring) S gates out hq hs hd reg hgates huniq hout
