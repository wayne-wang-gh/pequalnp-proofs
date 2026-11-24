import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_216

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def evalS {n : ℕ} (s : Option (Finset (Fin n))) (x : Fin n → Bool) : Bool :=
  match s with
  | none => true
  | some S => decide (∃ i ∈ S, x i = true)

def joinS {n : ℕ} :
    Option (Finset (Fin n)) → Option (Finset (Fin n)) → Option (Finset (Fin n))
  | some S, some T => some (S ∪ T)
  | _, _ => none

def R (a b : Bool) : Prop := a = true → b = true

lemma evalS_join {n : ℕ} (a b : Option (Finset (Fin n))) (x : Fin n → Bool) :
    evalS (joinS a b) x = (evalS a x || evalS b x) := by
  cases a with
  | none => cases b <;> simp [evalS, joinS]
  | some S =>
    cases b with
    | none => simp [evalS, joinS]
    | some T =>
      simp only [evalS, joinS]
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.or_eq_true, Finset.mem_union]
      constructor
      · rintro ⟨i, hi | hi, hx⟩
        · exact Or.inl ⟨i, hi, hx⟩
        · exact Or.inr ⟨i, hi, hx⟩
      · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
        · exact ⟨i, Or.inl hi, hx⟩
        · exact ⟨i, Or.inr hi, hx⟩

lemma getD_map_evalS {n : ℕ} (W : List (Option (Finset (Fin n)))) (x : Fin n → Bool) (i : ℕ) :
    (W.map (fun s => evalS s x)).getD i false = evalS (W.getD i (some ∅)) x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> simp [evalS]

lemma any_simple {n : ℕ} (W : List (Option (Finset (Fin n)))) (l : List ℕ) :
    ∃ s : Option (Finset (Fin n)), ∀ x : Fin n → Bool,
      (l.map fun i => (W.map (fun s => evalS s x)).getD i false).any id = evalS s x := by
  induction l with
  | nil => exact ⟨some ∅, fun x => by simp [evalS]⟩
  | cons a l ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨joinS (W.getD a (some ∅)) s, fun x => ?_⟩
    rw [evalS_join, ← hs x, ← getD_map_evalS]
    simp

lemma all_simple {n : ℕ} (W : List (Option (Finset (Fin n)))) (l : List ℕ) (hl : l.length ≤ 2) :
    ∃ sa sb : Option (Finset (Fin n)), ∀ x : Fin n → Bool,
      (l.map fun i => (W.map (fun s => evalS s x)).getD i false).all id
        = (evalS sa x && evalS sb x) := by
  match l, hl with
  | [], _ => exact ⟨none, none, fun x => by simp [evalS]⟩
  | [a], _ =>
    exact ⟨W.getD a (some ∅), W.getD a (some ∅), fun x => by
      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true,
        getD_map_evalS, Bool.and_self]⟩
  | [a, b], _ =>
    exact ⟨W.getD a (some ∅), W.getD b (some ∅), fun x => by
      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true,
        getD_map_evalS]⟩
  | _ :: _ :: _ :: _, h => simp at h

lemma R_refl (w : List Bool) : List.Forall₂ R w w := by
  induction w with
  | nil => exact List.Forall₂.nil
  | cons a w ih => exact List.Forall₂.cons (fun h => h) ih

lemma getD_le {w w' : List Bool} (h : List.Forall₂ R w w') :
    ∀ i : ℕ, w.getD i false = true → w'.getD i false = true := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => intro hi; exact hab (by simpa using hi)
    | succ i => simpa using ih i

lemma step_mono {w w' : List Bool} (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : List.Forall₂ R w w') : List.Forall₂ R (step w g) (step w' g) := by
  unfold step
  refine List.rel_append h (List.Forall₂.cons ?_ List.Forall₂.nil)
  intro hv
  rcases hg with hg | hg
  · rw [hg] at hv ⊢
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv ⊢
    intro i hi
    exact getD_le h i (hv i hi)
  · rw [hg] at hv ⊢
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv ⊢
    obtain ⟨i, hi, hv⟩ := hv
    exact ⟨i, hi, getD_le h i hv⟩

lemma Mono_tail {g : Gate} {gs : List Gate} (hm : Mono (g :: gs)) : Mono gs :=
  fun g' hg' => hm g' (List.mem_cons_of_mem g hg')

lemma run_mono : ∀ (gs : List Gate) (w w' : List Bool), Mono gs → List.Forall₂ R w w' →
    List.Forall₂ R (run gs w) (run gs w') := by
  intro gs
  induction gs with
  | nil => intro w w' _ h; exact h
  | cons g gs ih =>
    intro w w' hm h
    exact ih (step w g) (step w' g) (Mono_tail hm)
      (step_mono g (hm g List.mem_cons_self).1 h)

lemma branch (gs : List Gate) (hm : Mono gs) (w : List Bool) (a b : Bool) (o : ℕ) :
    (run gs (w ++ [a && b])).getD o false = false ↔
      ((run gs (w ++ [a])).getD o false = false ∨ (run gs (w ++ [b])).getD o false = false) := by
  constructor
  · intro h
    have hab : (a && b) = a ∨ (a && b) = b := by cases a <;> cases b <;> simp
    rcases hab with hab | hab
    · rw [hab] at h; exact Or.inl h
    · rw [hab] at h; exact Or.inr h
  · intro h
    have ha : List.Forall₂ R (w ++ [a && b]) (w ++ [a]) :=
      List.rel_append (R_refl w)
        (List.Forall₂.cons (by intro h'; cases a <;> cases b <;> simp_all) List.Forall₂.nil)
    have hb : List.Forall₂ R (w ++ [a && b]) (w ++ [b]) :=
      List.rel_append (R_refl w)
        (List.Forall₂.cons (by intro h'; cases a <;> cases b <;> simp_all) List.Forall₂.nil)
    have hA := getD_le (run_mono gs _ _ hm ha) o
    have hB := getD_le (run_mono gs _ _ hm hb) o
    cases hv : (run gs (w ++ [a && b])).getD o false with
    | false => rfl
    | true =>
      rcases h with h | h
      · rw [hA hv] at h; exact absurd h (by simp)
      · rw [hB hv] at h; exact absurd h (by simp)

lemma main {n : ℕ} : ∀ (gs : List Gate) (W : List (Option (Finset (Fin n)))) (k o : ℕ),
    Mono gs → gs.countP (fun g => isAnd g.op) ≤ k →
    ∃ T : Finset (Option (Finset (Fin n))), T.card ≤ 2 ^ k ∧ ∀ x : Fin n → Bool,
      ((run gs (W.map (fun s => evalS s x))).getD o false = false ↔
        ∃ s ∈ T, evalS s x = false) := by
  intro gs
  induction gs with
  | nil =>
    intro W k o _ _
    refine ⟨{W.getD o (some ∅)}, ?_, fun x => ?_⟩
    · rw [Finset.card_singleton]; exact Nat.one_le_two_pow
    · show (W.map (fun s => evalS s x)).getD o false = false ↔ _
      rw [getD_map_evalS]
      simp
  | cons g gs ih =>
    intro W k o hm hk
    have hg := hm g List.mem_cons_self
    have hm' := Mono_tail hm
    rcases hg.1 with hop | hop
    · have hcount : gs.countP (fun g => isAnd g.op) + 1 ≤ k := by
        have : List.countP (fun g => isAnd g.op) (g :: gs)
            = gs.countP (fun g => isAnd g.op) + 1 := by
          rw [List.countP_cons]; simp [hop, isAnd]
        omega
      obtain ⟨sa, sb, hs⟩ := all_simple W g.inputs hg.2
      obtain ⟨Ta, hTa, hTax⟩ := ih (W ++ [sa]) (k - 1) o hm' (by omega)
      obtain ⟨Tb, hTb, hTbx⟩ := ih (W ++ [sb]) (k - 1) o hm' (by omega)
      refine ⟨Ta ∪ Tb, ?_, fun x => ?_⟩
      · have h2 : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
          have : k = (k - 1) + 1 := by omega
          rw [this, pow_succ]; simp; omega
        calc (Ta ∪ Tb).card ≤ Ta.card + Tb.card := Finset.card_union_le _ _
          _ ≤ 2 ^ k := by omega
      · have hstep : run (g :: gs) (W.map (fun s => evalS s x))
            = run gs (W.map (fun s => evalS s x) ++ [evalS sa x && evalS sb x]) := by
          show run gs (step _ g) = _
          unfold step
          rw [hop]
          show run gs (_ ++ [List.all _ id]) = _
          rw [hs x]
        rw [hstep, branch gs hm']
        have h1 := hTax x
        have h2 := hTbx x
        rw [List.map_append, List.map_singleton] at h1 h2
        rw [h1, h2]
        constructor
        · rintro (⟨s, hs, hx⟩ | ⟨s, hs, hx⟩)
          · exact ⟨s, Finset.mem_union_left _ hs, hx⟩
          · exact ⟨s, Finset.mem_union_right _ hs, hx⟩
        · rintro ⟨s, hs, hx⟩
          rcases Finset.mem_union.mp hs with hs | hs
          · exact Or.inl ⟨s, hs, hx⟩
          · exact Or.inr ⟨s, hs, hx⟩
    · have hcount : gs.countP (fun g => isAnd g.op) ≤ k := by
        have : List.countP (fun g => isAnd g.op) (g :: gs)
            = gs.countP (fun g => isAnd g.op) := by
          rw [List.countP_cons]; simp [hop, isAnd]
        omega
      obtain ⟨s, hs⟩ := any_simple W g.inputs
      obtain ⟨T, hT, hTx⟩ := ih (W ++ [s]) k o hm' hcount
      refine ⟨T, hT, fun x => ?_⟩
      have hstep : run (g :: gs) (W.map (fun s => evalS s x))
          = run gs (W.map (fun s => evalS s x) ++ [evalS s x]) := by
        show run gs (step _ g) = _
        unfold step
        rw [hop]
        show run gs (_ ++ [List.any _ id]) = _
        rw [hs x]
      have h1 := hTx x
      rw [List.map_append, List.map_singleton] at h1
      rw [hstep, h1]

lemma count_le : ∀ (gs : List Gate) (A : Finset ℕ),
    (∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → j ∈ A) →
    gs.countP (fun g => isAnd g.op) ≤ A.card := by
  intro gs
  induction gs with
  | nil => intro A _; simp
  | cons g gs ih =>
    intro A hA
    have hsub : gs.countP (fun g => isAnd g.op) ≤ ((A.erase 0).image Nat.pred).card := by
      apply ih
      intro j g' hj hop
      have hmem : j + 1 ∈ A := hA (j + 1) g' (by simpa using hj) hop
      exact Finset.mem_image.mpr ⟨j + 1, Finset.mem_erase.mpr ⟨by omega, hmem⟩, rfl⟩
    have himg : ((A.erase 0).image Nat.pred).card ≤ (A.erase 0).card := Finset.card_image_le
    rw [List.countP_cons]
    by_cases hop : g.op = GateOp.and
    · have h0 : 0 ∈ A := hA 0 g (by simp) hop
      have hcard : (A.erase 0).card = A.card - 1 := Finset.card_erase_of_mem h0
      have hpos : 0 < A.card := Finset.card_pos.mpr ⟨0, h0⟩
      have hyes : isAnd g.op = true := by rw [hop]; rfl
      simp only [hyes]
      simp
      omega
    · have hle : (A.erase 0).card ≤ A.card := Finset.card_erase_le
      have hno : isAnd g.op = false := by
        cases hg : g.op <;> simp_all [isAnd]
      simp only [hno]
      simp
      omega

def top {n : ℕ} (s : Option (Finset (Fin n))) : Fin n → Bool :=
  match s with
  | none => fun _ => true
  | some S => fun i => decide (i ∉ S)

end PEqualNP.Outside.L_meta_216

theorem PEqualNP.Outside.L_meta_216 : ∀ (n k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∃ A : Finset ℕ, A.card ≤ k ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → {x : Fin n → Bool | C.eval (List.ofFn x) = false ∧ ∀ y : Fin n → Bool, (∀ i : Fin n, x i = true → y i = true) → C.eval (List.ofFn y) = false → y = x}.ncard ≤ 2 ^ k := by
  classical
  intro n k C hmono hA
  obtain ⟨A, hAk, hAnd⟩ := hA
  have hm : PEqualNP.Outside.L_meta_216.Mono C.gates := by
    intro g hg
    have h := hmono g hg
    refine ⟨?_, h.2⟩
    rcases h.1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hcount := PEqualNP.Outside.L_meta_216.count_le C.gates A hAnd
  obtain ⟨T, hT, hTx⟩ := PEqualNP.Outside.L_meta_216.main (n := n) C.gates
    (List.ofFn (fun i : Fin n => some ({i} : Finset (Fin n)))) k C.output hm (by omega)
  have hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = false ↔
      ∃ s ∈ T, PEqualNP.Outside.L_meta_216.evalS s x = false := by
    intro x
    have h := hTx x
    have hmap : (List.ofFn (fun i : Fin n => some ({i} : Finset (Fin n)))).map
        (fun s => PEqualNP.Outside.L_meta_216.evalS s x) = List.ofFn x := by
      rw [List.map_ofFn]
      congr 1
      funext i
      simp [PEqualNP.Outside.L_meta_216.evalS]
    rw [hmap] at h
    exact h
  have hsub : {x : Fin n → Bool | C.eval (List.ofFn x) = false ∧ ∀ y : Fin n → Bool,
      (∀ i : Fin n, x i = true → y i = true) → C.eval (List.ofFn y) = false → y = x}
      ⊆ ((T.image PEqualNP.Outside.L_meta_216.top : Finset (Fin n → Bool)) : Set (Fin n → Bool)) := by
    intro x hx
    obtain ⟨hx0, hxmax⟩ := hx
    obtain ⟨s, hsT, hsx⟩ := (hF x).mp hx0
    cases s with
    | none => simp [PEqualNP.Outside.L_meta_216.evalS] at hsx
    | some S =>
      have hxS : ∀ i ∈ S, x i = false := by
        intro i hi
        simp only [PEqualNP.Outside.L_meta_216.evalS, decide_eq_false_iff_not] at hsx
        cases hxi : x i with
        | false => rfl
        | true => exact absurd ⟨i, hi, hxi⟩ hsx
      have hy : PEqualNP.Outside.L_meta_216.top (some S) = x := by
        apply hxmax
        · intro i hi
          simp only [PEqualNP.Outside.L_meta_216.top, decide_eq_true_eq]
          intro hiS
          rw [hxS i hiS] at hi
          exact absurd hi (by simp)
        · rw [hF]
          refine ⟨some S, hsT, ?_⟩
          simp [PEqualNP.Outside.L_meta_216.evalS, PEqualNP.Outside.L_meta_216.top]
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨some S, hsT, hy⟩
  calc _ ≤ ((T.image PEqualNP.Outside.L_meta_216.top : Finset (Fin n → Bool)) :
        Set (Fin n → Bool)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (T.image PEqualNP.Outside.L_meta_216.top).card := Set.ncard_coe_finset _
    _ ≤ T.card := Finset.card_image_le
    _ ≤ 2 ^ k := hT
