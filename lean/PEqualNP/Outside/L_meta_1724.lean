import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1724

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstp (d : List ℕ) (g : Gate) : List ℕ :=
  d ++ [g.lineDegree d]

def sw (D : Circuit) (j c : ℕ) : Circuit :=
  ⟨D.gates.set j ⟨GateOp.or, [c, c]⟩, D.output⟩

def KM (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  (∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
    (∀ h ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0)

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem ld_eq (C : Circuit) (n : ℕ) (M : Finset ℕ) :
    C.lineDegrees n M
      = C.gates.foldl dstp ((List.range n).map fun i => if i ∈ M then 1 else 0) := rfl

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g2 hg2 => hop g2 (List.mem_cons_of_mem _ hg2))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem sum_mono (f1 f2 : ℕ → ℕ) (H : ∀ i, f1 i ≤ f2 i) :
    ∀ l : List ℕ, (l.map f1).sum ≤ (l.map f2).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (H a) (sum_mono f1 f2 H l)

theorem max_mono (f1 f2 : ℕ → ℕ) (H : ∀ i, f1 i ≤ f2 i) :
    ∀ l : List ℕ, (l.map f1).foldr max 0 ≤ (l.map f2).foldr max 0
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (H a) (max_mono f1 f2 H l)

theorem ldeg_mono (g : Gate) (d1 d2 : List ℕ) (H : ∀ i, d1.getD i 0 ≤ d2.getD i 0) :
    g.lineDegree d1 ≤ g.lineDegree d2 := by
  unfold Gate.lineDegree
  split_ifs
  · exact sum_mono _ _ H g.inputs
  · exact max_mono _ _ H g.inputs

theorem ld_or (ins : List ℕ) (d : List ℕ) :
    (⟨GateOp.or, ins⟩ : Gate).lineDegree d = (ins.map fun i => d.getD i 0).foldr max 0 := by
  unfold Gate.lineDegree
  rw [if_neg (by simp)]

theorem ld_and (ins : List ℕ) (d : List ℕ) :
    (⟨GateOp.and, ins⟩ : Gate).lineDegree d = (ins.map fun i => d.getD i 0).sum := by
  unfold Gate.lineDegree
  rw [if_pos rfl]

theorem dmono : ∀ (gs : List Gate) (d1 d2 : List ℕ), d1.length = d2.length →
    (∀ i, d1.getD i 0 ≤ d2.getD i 0) →
    ∀ i, (gs.foldl dstp d1).getD i 0 ≤ (gs.foldl dstp d2).getD i 0 := by
  intro gs
  induction gs with
  | nil => intro d1 d2 _ H; simpa using H
  | cons g gs ih =>
    intro d1 d2 hl H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (dstp d1 g) (dstp d2 g) (by simp [dstp, hl])
    intro i
    simp only [dstp, getD_snoc, hl]
    split_ifs
    · exact ldeg_mono g d1 d2 H
    · exact H i

theorem set_split {α : Type} (g a : α) (S : List α) :
    ∀ P : List α, (P ++ g :: S).set P.length a = P ++ a :: S
  | [] => rfl
  | p :: P => by simp [set_split g a S P]

theorem bool_fin (u v : Bool) (h : u = true → v = true) : (u && v) = u ∧ (v && u) = u := by
  cases u <;> cases v <;> simp at h ⊢

theorem and_split (P S : List Gate) (a b : ℕ) (x : List Bool) (o : ℕ)
    (hS : ∀ g ∈ S, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (((P ++ (⟨GateOp.or, [a, a]⟩ : Gate) :: S).foldl stp x).getD o false
      && ((P ++ (⟨GateOp.or, [b, b]⟩ : Gate) :: S).foldl stp x).getD o false)
      = ((P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S).foldl stp x).getD o false := by
  simp only [List.foldl_append, List.foldl_cons]
  generalize P.foldl stp x = w
  have e1 : stp w ⟨GateOp.or, [a, a]⟩ = w ++ [w.getD a false] := by simp [stp, GateOp.eval]
  have e2 : stp w ⟨GateOp.or, [b, b]⟩ = w ++ [w.getD b false] := by simp [stp, GateOp.eval]
  have e3 : stp w ⟨GateOp.and, [a, b]⟩ = w ++ [w.getD a false && w.getD b false] := by
    simp [stp, GateOp.eval]
  rw [e1, e2, e3]
  have key : ∀ i, (S.foldl stp (w ++ [false])).getD i false = true →
      (S.foldl stp (w ++ [true])).getD i false = true := by
    apply mono S _ _ (by simp) hS
    intro i
    simp only [getD_snoc]
    split_ifs
    · exact fun _ => rfl
    · exact id
  cases hA : w.getD a false <;> cases hB : w.getD b false
  · simp only [Bool.and_self]
  · simp only [Bool.false_and]
    exact (bool_fin _ _ (key o)).1
  · simp only [Bool.and_false]
    exact (bool_fin _ _ (key o)).2
  · simp only [Bool.and_self]

theorem deg_split (P S : List Gate) (a b c : ℕ) (hc : c = a ∨ c = b) (d0 : List ℕ) (i : ℕ) :
    ((P ++ (⟨GateOp.or, [c, c]⟩ : Gate) :: S).foldl dstp d0).getD i 0
      ≤ ((P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S).foldl dstp d0).getD i 0 := by
  simp only [List.foldl_append, List.foldl_cons]
  generalize P.foldl dstp d0 = d
  apply dmono S _ _ (by simp [dstp])
  intro k
  simp only [dstp, getD_snoc]
  split_ifs
  · rw [ld_or, ld_and]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.sum_cons,
      List.sum_nil]
    rcases hc with rfl | rfl <;> omega
  · exact le_rfl

theorem surg (n : ℕ) (P S : List Gate) (a b o : ℕ)
    (hS : ∀ g ∈ S, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (∀ x : List Bool,
      ((sw ⟨P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S, o⟩ P.length a).eval x
        && (sw ⟨P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S, o⟩ P.length b).eval x)
        = Circuit.eval ⟨P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S, o⟩ x) ∧
    (∀ c, (c = a ∨ c = b) → ∀ (M : Finset ℕ) (i : ℕ),
      ((sw ⟨P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S, o⟩ P.length c).lineDegrees n M).getD i 0
        ≤ (Circuit.lineDegrees ⟨P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S, o⟩ n M).getD i 0) := by
  have hsw : ∀ c, sw ⟨P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S, o⟩ P.length c
      = ⟨P ++ (⟨GateOp.or, [c, c]⟩ : Gate) :: S, o⟩ :=
    fun c => congrArg (fun l => Circuit.mk l o) (set_split _ _ S P)
  refine ⟨fun x => ?_, fun c hc M i => ?_⟩
  · rw [hsw, hsw, eval_eq, eval_eq, eval_eq]
    exact and_split P S a b x o hS
  · rw [hsw, ld_eq, ld_eq]
    exact deg_split P S a b c hc _ i

theorem gate_ext (g : Gate) (a b : ℕ) (h1 : g.op = GateOp.and) (h2 : g.inputs = [a, b]) :
    g = ⟨GateOp.and, [a, b]⟩ := by
  obtain ⟨op, ins⟩ := g
  have h3 : op = GateOp.and := h1
  have h4 : ins = [a, b] := h2
  subst h3
  subst h4
  rfl

theorem surg2 (n : ℕ) (D : Circuit) (j0 : ℕ) (hj0 : j0 < D.gates.length)
    (hop0 : (PEqualNP.MetaComplexity.NestedCover.gateAt D j0).op = GateOp.and)
    (hDg : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∃ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt D j0).inputs = [a, b] ∧
      ((∀ x : List Bool, ((sw D j0 a).eval x && (sw D j0 b).eval x) = D.eval x) ∧
      (∀ c, (c = a ∨ c = b) → ∀ (M : Finset ℕ) (i : ℕ),
        ((sw D j0 c).lineDegrees n M).getD i 0 ≤ (D.lineDegrees n M).getD i 0)) := by
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt D j0 = D.gates[j0] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj0]
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (hDg _ (List.getElem_mem hj0)).2
  have hg0 : D.gates[j0] = ⟨GateOp.and, [a, b]⟩ :=
    gate_ext _ a b (by rw [← hga]; exact hop0) hab
  have hsplit : ∃ P S, D.gates = P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S ∧ P.length = j0 := by
    refine ⟨D.gates.take j0, D.gates.drop (j0 + 1), ?_, ?_⟩
    · rw [← hg0, ← List.drop_eq_getElem_cons hj0, List.take_append_drop]
    · rw [List.length_take]
      omega
  obtain ⟨P, S, hs, hP⟩ := hsplit
  refine ⟨a, b, by rw [hga, hab], ?_⟩
  have hSg : ∀ g ∈ S, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hDg g (by rw [hs]; simp [hg])).1
  clear hga hab hg0 hop0 hDg hj0
  obtain ⟨gates, o⟩ := D
  have hs2 : gates = P ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: S := hs
  subst hs2
  subst hP
  exact surg n P S a b o hSg

theorem gateAt_sw (D : Circuit) (j0 c j : ℕ) (hne : j ≠ j0) :
    PEqualNP.MetaComplexity.NestedCover.gateAt (sw D j0 c) j
      = PEqualNP.MetaComplexity.NestedCover.gateAt D j := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, sw, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm hne)]

theorem gateAt_sw_self (D : Circuit) (j0 c : ℕ) (hj : j0 < D.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt (sw D j0 c) j0 = ⟨GateOp.or, [c, c]⟩ := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, sw, List.getD_eq_getElem?_getD, hj]

theorem sw_len (D : Circuit) (j0 c : ℕ) : (sw D j0 c).gates.length = D.gates.length := by
  simp [sw]

theorem sw_gates (D : Circuit) (j0 c : ℕ)
    (hDg : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ g ∈ (sw D j0 c).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  rcases List.mem_or_eq_of_mem_set hg with h | rfl
  · exact hDg g h
  · exact ⟨Or.inr rfl, rfl⟩

theorem sw_rb (n : ℕ) (D : Circuit) (j0 c : ℕ)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n D) (hj0 : j0 < D.gates.length)
    (hc : c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j0).inputs) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n (sw D j0 c) := by
  intro j hj i hi
  have hj2 : j < D.gates.length := by rw [sw_len] at hj; exact hj
  by_cases h : j = j0
  · subst h
    rw [gateAt_sw_self D j c hj2] at hi
    have hic : i = c := by simpa using hi
    rw [hic]
    exact hrb j hj2 c hc
  · rw [gateAt_sw D j0 c j h] at hi
    exact hrb j hj2 i hi

theorem sw_km (N : ℕ) (D : Circuit) (j0 c : ℕ)
    (hdeg : ∀ (M : Finset ℕ) (i : ℕ),
      ((sw D j0 c).lineDegrees (N + N) M).getD i 0 ≤ (D.lineDegrees (N + N) M).getD i 0)
    (j : ℕ) (hne : j ≠ j0) (hk : KM N D j) : KM N (sw D j0 c) j := by
  unfold KM at *
  rw [gateAt_sw D j0 c j hne]
  rcases hk with ⟨i, hi, h0⟩ | h
  · refine Or.inl ⟨i, hi, ?_⟩
    have h1 := hdeg (Finset.Ico N (N + N)) i
    omega
  · refine Or.inr fun k hh => ?_
    have h1 := hdeg (Finset.range N) k
    have h2 := h k hh
    omega

end PEqualNP.Outside.L_meta_1724

theorem PEqualNP.Outside.L_meta_1724 : (∀ (q9 N9 k9 : ℕ) (I9 : Fin N9 → Fin N9 → Prop) [DecidableRel I9] (Ca9 Cb9 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q9 → N9 = q9 ^ 2 + q9 + 1 → (∀ l9a : Fin N9, (Finset.univ.filter (fun p9a => I9 p9a l9a)).card = q9 + 1) → (∀ pa9 pb9 : Fin N9, pa9 ≠ pb9 → ∃! lb9 : Fin N9, I9 pa9 lb9 ∧ I9 pb9 lb9) → 8 ≤ q9 → 2 ≤ k9 → (∀ g9 ∈ Ca9.gates, (g9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g9.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g9.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N9 + N9) Ca9 → (∀ g9a ∈ Cb9.gates, (g9a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g9a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g9a.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N9 + N9) Cb9 → (∀ j9 < Ca9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt Ca9 j9).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i9b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Ca9 j9).inputs, (Ca9.lineDegrees (N9 + N9) (Finset.Ico N9 (N9 + N9))).getD i9b 0 = 0) ∨ (∀ h9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Ca9 j9).inputs, (Ca9.lineDegrees (N9 + N9) (Finset.range N9)).getD h9 0 = 0)) → (∀ j9a < Cb9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt Cb9 j9a).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i9c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Cb9 j9a).inputs, (Cb9.lineDegrees (N9 + N9) (Finset.Ico N9 (N9 + N9))).getD i9c 0 = 0) ∨ (∀ h9a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Cb9 j9a).inputs, (Cb9.lineDegrees (N9 + N9) (Finset.range N9)).getD h9a 0 = 0)) → (∀ p9 l9 : Fin N9, I9 p9 l9 → (PEqualNP.MetaComplexity.circuitFun (N9 + N9) Ca9 (fun i9 => decide (i9 = Fin.castAdd N9 p9 ∨ i9 = Fin.natAdd N9 l9)) && PEqualNP.MetaComplexity.circuitFun (N9 + N9) Cb9 (fun i9a => decide (i9a = Fin.castAdd N9 p9 ∨ i9a = Fin.natAdd N9 l9))) = true) → (∀ z9 : Fin (N9 + N9) → Bool, (Finset.univ.filter (fun l9b : Fin N9 => z9 (Fin.natAdd N9 l9b) = true)).card ≤ k9 → (¬ ∃ p9b l9c : Fin N9, I9 p9b l9c ∧ z9 (Fin.castAdd N9 p9b) = true ∧ z9 (Fin.natAdd N9 l9c) = true) → (PEqualNP.MetaComplexity.circuitFun (N9 + N9) Ca9 z9 && PEqualNP.MetaComplexity.circuitFun (N9 + N9) Cb9 z9) = false) → N9 * min (k9 / 2) (q9 / 4) ≤ 10 * max Ca9.size Cb9.size) → (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1) → (∀ (N102 : ℕ) (C102 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C102 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N102 + N102) C102 → Set.ncard {j102 : ℕ | j102 < C102.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C102 j102).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i102 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C102 j102).inputs, (C102.lineDegrees (N102 + N102) (Finset.Ico N102 (N102 + N102))).getD i102 0 = 0) ∨ (∀ h102 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C102 j102).inputs, (C102.lineDegrees (N102 + N102) (Finset.range N102)).getD h102 0 = 0))} ≤ 1 → (∃ z102 z102a : Fin (N102 + N102) → Bool, PEqualNP.MetaComplexity.circuitFun (N102 + N102) C102 z102 ≠ PEqualNP.MetaComplexity.circuitFun (N102 + N102) C102 z102a) → ∃ D102 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g102 ∈ D102.gates, (g102.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g102.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g102.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N102 + N102) D102) ∧ Set.ncard {j102a : ℕ | j102a < D102.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D102 j102a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i102a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D102 j102a).inputs, (D102.lineDegrees (N102 + N102) (Finset.Ico N102 (N102 + N102))).getD i102a 0 = 0) ∨ (∀ h102a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D102 j102a).inputs, (D102.lineDegrees (N102 + N102) (Finset.range N102)).getD h102a 0 = 0))} ≤ 1 ∧ D102.size ≤ C102.size ∧ PEqualNP.MetaComplexity.circuitFun (N102 + N102) D102 = PEqualNP.MetaComplexity.circuitFun (N102 + N102) C102) → ∀ (q10 N10 : ℕ) (I10 : Fin N10 → Fin N10 → Prop) [DecidableRel I10] (C10 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q10 → N10 = q10 ^ 2 + q10 + 1 → (∀ l10 : Fin N10, (Finset.univ.filter (fun p10 => I10 p10 l10)).card = q10 + 1) → (∀ p10 pp10 : Fin N10, p10 ≠ pp10 → ∃! l10 : Fin N10, I10 p10 l10 ∧ I10 pp10 l10) → PEqualNP.MetaComplexity.Monotone2 C10 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N10 + N10) C10 → Set.ncard {j10 : ℕ | j10 < C10.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C10 j10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C10 j10).inputs, (C10.lineDegrees (N10 + N10) (Finset.Ico N10 (N10 + N10))).getD i10 0 = 0) ∨ (∀ h10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C10 j10).inputs, (C10.lineDegrees (N10 + N10) (Finset.range N10)).getD h10 0 = 0))} ≤ 1 → (∀ p10 l10 : Fin N10, I10 p10 l10 → PEqualNP.MetaComplexity.circuitFun (N10 + N10) C10 (fun k10 => decide (k10 = Fin.castAdd N10 p10 ∨ k10 = Fin.natAdd N10 l10)) = true) → (∀ z10 : Fin (N10 + N10) → Bool, (Finset.univ.filter (fun l10 : Fin N10 => z10 (Fin.natAdd N10 l10) = true)).card ≤ q10 → (¬ ∃ p10 l10 : Fin N10, I10 p10 l10 ∧ z10 (Fin.castAdd N10 p10) = true ∧ z10 (Fin.natAdd N10 l10) = true) → PEqualNP.MetaComplexity.circuitFun (N10 + N10) C10 z10 = false) → N10 * q10 ≤ 100 * C10.size := by
  intro H1 H2 H3 q N I hdec C hq hN hcard huniq hmono hrb hone hacc hrej
  have hq2 : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  by_cases hq8 : 8 ≤ q
  swap
  · have h2 := H2 q N I C hq hN hcard huniq hmono hrb hacc hrej
    have h7 : N * q ≤ N * 7 := Nat.mul_le_mul_left _ (by omega)
    omega
  have hN0 : 0 < N := by omega
  obtain ⟨p, hp⟩ : ∃ p, I p ⟨0, hN0⟩ := by
    have hc := hcard ⟨0, hN0⟩
    have hne : (Finset.univ.filter (fun p0 => I p0 ⟨0, hN0⟩)).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, (Finset.mem_filter.1 hp).2⟩
  have hfalse : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun _ => false) = false :=
    hrej (fun _ => false) (by simp) (by simp)
  obtain ⟨D, ⟨hDg, hDrb⟩, hDone, hDsize, hDfun⟩ := H3 N C hmono hrb hone
    ⟨fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N ⟨0, hN0⟩), fun _ => false,
      fun h => absurd ((hacc p ⟨0, hN0⟩ hp).symm.trans (h.trans hfalse)) (by decide)⟩
  have hDone2 : Set.ncard {j : ℕ | j < D.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op
        = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ¬ PEqualNP.Outside.L_meta_1724.KM N D j} ≤ 1 := hDone
  have hfin : N * min (q / 2) (q / 4) ≤ 10 * D.size := by
    by_cases hS : ∃ j, j < D.gates.length ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op
          = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ¬ PEqualNP.Outside.L_meta_1724.KM N D j
    · obtain ⟨j0, hj0, hop0, hnk0⟩ := hS
      have huS : ∀ j, j < D.gates.length →
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op
            = PEqualNP.CircuitLowerBounds.GateOp.and →
          ¬ PEqualNP.Outside.L_meta_1724.KM N D j → j = j0 := by
        intro j h1 h2 h3
        have hfS : {j : ℕ | j < D.gates.length ∧
            (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op
              = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            ¬ PEqualNP.Outside.L_meta_1724.KM N D j}.Finite :=
          Set.Finite.subset (Set.finite_lt_nat D.gates.length) (fun j hj => hj.1)
        exact (Set.ncard_le_one hfS).1 hDone2 j ⟨h1, h2, h3⟩ j0 ⟨hj0, hop0, hnk0⟩
      obtain ⟨a, b, hab, hev, hdeg⟩ :=
        PEqualNP.Outside.L_meta_1724.surg2 (N + N) D j0 hj0 hop0 hDg
      have hka : ∀ c, (c = a ∨ c = b) →
          ∀ j < (PEqualNP.Outside.L_meta_1724.sw D j0 c).gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt
            (PEqualNP.Outside.L_meta_1724.sw D j0 c) j).op
            = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.Outside.L_meta_1724.KM N (PEqualNP.Outside.L_meta_1724.sw D j0 c) j := by
        intro c hc j hj hop
        have hj2 : j < D.gates.length := by
          rw [PEqualNP.Outside.L_meta_1724.sw_len] at hj
          exact hj
        by_cases h : j = j0
        · subst h
          rw [PEqualNP.Outside.L_meta_1724.gateAt_sw_self D j c hj2] at hop
          exact absurd hop (by simp)
        · rw [PEqualNP.Outside.L_meta_1724.gateAt_sw D j0 c j h] at hop
          apply PEqualNP.Outside.L_meta_1724.sw_km N D j0 c (hdeg c hc) j h
          by_contra hn
          exact h (huS j hj2 hop hn)
      have h1 := H1 q N q I (PEqualNP.Outside.L_meta_1724.sw D j0 a)
        (PEqualNP.Outside.L_meta_1724.sw D j0 b) hq hN hcard huniq hq8 (by omega)
        (PEqualNP.Outside.L_meta_1724.sw_gates D j0 a hDg)
        (PEqualNP.Outside.L_meta_1724.sw_rb (N + N) D j0 a hDrb hj0 (by rw [hab]; simp))
        (PEqualNP.Outside.L_meta_1724.sw_gates D j0 b hDg)
        (PEqualNP.Outside.L_meta_1724.sw_rb (N + N) D j0 b hDrb hj0 (by rw [hab]; simp))
        (hka a (Or.inl rfl)) (hka b (Or.inr rfl))
        (by
          intro p1 l1 h
          have e := hev (List.ofFn
            (fun i9 => decide (i9 = Fin.castAdd N p1 ∨ i9 = Fin.natAdd N l1)))
          have e2 := hacc p1 l1 h
          rw [← hDfun] at e2
          exact e.trans e2)
        (by
          intro z hz hno
          have e := hev (List.ofFn z)
          have e2 := hrej z hz hno
          rw [← hDfun] at e2
          exact e.trans e2)
      have e1 : (PEqualNP.Outside.L_meta_1724.sw D j0 a).size = D.size :=
        PEqualNP.Outside.L_meta_1724.sw_len D j0 a
      have e2 : (PEqualNP.Outside.L_meta_1724.sw D j0 b).size = D.size :=
        PEqualNP.Outside.L_meta_1724.sw_len D j0 b
      rw [e1, e2, max_self] at h1
      exact h1
    · have h1 := H1 q N q I D D hq hN hcard huniq hq8 (by omega) hDg hDrb hDg hDrb
        (fun j hj hop => by
          by_contra hn
          exact hS ⟨j, hj, hop, hn⟩)
        (fun j hj hop => by
          by_contra hn
          exact hS ⟨j, hj, hop, hn⟩)
        (by
          intro p1 l1 h
          have e2 := hacc p1 l1 h
          rw [← hDfun] at e2
          rw [e2]
          rfl)
        (by
          intro z hz hno
          have e2 := hrej z hz hno
          rw [← hDfun] at e2
          rw [e2]
          rfl)
      rw [max_self] at h1
      exact h1
  have hm : min (q / 2) (q / 4) = q / 4 := by omega
  rw [hm] at hfin
  have h10 : q ≤ 10 * (q / 4) := by omega
  calc N * q ≤ N * (10 * (q / 4)) := Nat.mul_le_mul_left _ h10
    _ = 10 * (N * (q / 4)) := by ring
    _ ≤ 10 * (10 * D.size) := Nat.mul_le_mul_left _ hfin
    _ ≤ 100 * C.size := by omega
