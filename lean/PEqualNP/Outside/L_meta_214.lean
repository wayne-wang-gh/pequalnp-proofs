import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_214

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [Circuit.wires, List.foldl_append]

lemma run_extends (gs : List Gate) (w : List Bool) :
    ∃ tail : List Bool, run gs w = w ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [Circuit.wires], rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨tail, heq, hlen⟩ := ih (w ++ [b])
    refine ⟨b :: tail, ?_, by simp [hlen]⟩
    change run gs (w ++ [b]) = w ++ b :: tail
    simpa [List.append_assoc] using heq

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨tail, heq, hlen⟩ := run_extends gs w
  simp [heq, hlen]

lemma run_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨tail, heq, _⟩ := run_extends gs w
  rw [heq, List.getD_append _ _ _ _ hi]

def TracksAnd (gs : List Gate) (A : Finset ℕ) : Prop :=
  ∀ j g, gs[j]? = some g → g.op = GateOp.and → j ∈ A

lemma TracksAnd.append {gs hs : List Gate} {A B : Finset ℕ}
    (hA : TracksAnd gs A) (hB : TracksAnd hs B) :
    TracksAnd (gs ++ hs) (A ∪ B.image (gs.length + ·)) := by
  intro j g hg hand
  by_cases hj : j < gs.length
  · rw [List.getElem?_append_left hj] at hg
    exact Finset.mem_union_left _ (hA j g hg hand)
  · have hle := Nat.le_of_not_gt hj
    rw [List.getElem?_append_right hle] at hg
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨j - gs.length, hB _ g hg hand, Nat.add_sub_of_le hle⟩)

def Builds (n : ℕ) (F : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (o : ℕ) (A : Finset ℕ),
    Monotone2 ⟨gs, o⟩ ∧ TracksAnd gs A ∧ A.card ≤ k ∧ o < m + gs.length ∧
    ∀ w : List Bool, w.length = m → (run gs w).getD o false = F (fun i => w.getD i false)

lemma Builds.input {n : ℕ} (i : Fin n) : Builds n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, ∅, by simp [Monotone2], by simp [TracksAnd], by simp, ?_, ?_⟩
  · simpa using i.isLt.trans_le hm
  · intro w _
    rfl

lemma Builds.zero (n : ℕ) : Builds n (fun _ => false) 0 := by
  intro m _
  refine ⟨[⟨.or, []⟩], m, ∅, by simp [Monotone2], ?_, by simp, by simp, ?_⟩
  · intro j g hg hand
    have heq := List.getElem?_eq_some_iff.mp hg
    have hj : j = 0 := by simpa using heq.1
    subst j
    simp at hg
    subst g
    cases hand
  · intro w hw
    change (w ++ [false]).getD m false = false
    rw [← hw]
    simp

def binaryOp (conj : Bool) : GateOp :=
  if conj then .and else .or

lemma Builds.binary {n k l : ℕ} {F H : (Fin n → Bool) → Bool}
    (hF : Builds n F k) (hH : Builds n H l) (conj : Bool) :
    Builds n (fun x => if conj then F x && H x else F x || H x)
      (k + l + if conj then 1 else 0) := by
  intro m hm
  obtain ⟨gs, p, A, hmA, hrA, hcA, hp, heA⟩ := hF m hm
  obtain ⟨hs, q, B, hmB, hrB, hcB, hq, heB⟩ := hH (m + gs.length) (by omega)
  let gate : Gate := ⟨binaryOp conj, [p, q]⟩
  let D : Finset ℕ := if conj then {0} else ∅
  have hcD : D.card = if conj then 1 else 0 := by cases conj <;> simp [D]
  have hrD : TracksAnd [gate] D := by
    intro j g hg hand
    have heq := List.getElem?_eq_some_iff.mp hg
    have hj : j = 0 := by simpa using heq.1
    subst j
    have he : g = gate := by simpa using heq.2.symm
    subst g
    cases conj <;> simp_all [gate, binaryOp, D]
  refine ⟨gs ++ hs ++ [gate], m + gs.length + hs.length,
    (A ∪ B.image (gs.length + ·)) ∪ D.image ((gs ++ hs).length + ·),
    ?_, (hrA.append hrB).append hrD, ?_, by simp; omega, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact hmA g hg
    · exact hmB g hg
    · cases conj <;> simp [gate, binaryOp]
  · have h₁ := Finset.card_union_le (A ∪ B.image (gs.length + ·))
      (D.image ((gs ++ hs).length + ·))
    have h₂ := Finset.card_union_le A (B.image (gs.length + ·))
    have h₃ := Finset.card_image_le (f := (gs.length + ·)) (s := B)
    have h₄ := Finset.card_image_le (f := ((gs ++ hs).length + ·)) (s := D)
    omega
  · intro w hw
    rw [run_append, run_append]
    let u := run gs w
    let v := run hs u
    have hu : u.length = m + gs.length := by simp [u, run_length, hw]
    have hv : v.length = m + gs.length + hs.length := by simp [v, run_length, hu]
    have hFv : v.getD p false = F (fun i => w.getD i false) := by
      rw [show v = run hs u from rfl, run_getD _ _ _ (by omega), heA w hw]
    have hHv : v.getD q false = H (fun i => w.getD i false) := by
      rw [show v = run hs u from rfl, heB u hu]
      congr 1
      funext i
      exact run_getD _ _ _ (i.isLt.trans_le (hw ▸ hm))
    change (v ++ [gate.op.eval (gate.inputs.map fun i => v.getD i false)]).getD
      (m + gs.length + hs.length) false = _
    rw [← hv]
    have hlast (b : Bool) : (v ++ [b]).getD v.length false = b := by simp
    rw [hlast]
    simp only [List.getD_eq_getElem?_getD] at hFv hHv
    cases conj <;> simp [gate, binaryOp, GateOp.eval, hFv, hHv]

lemma builds_any {n : ℕ} (vs : List (Fin n)) :
    Builds n (fun x => vs.any fun i => x i) 0 := by
  induction vs with
  | nil => exact Builds.zero n
  | cons i vs ih =>
    simpa using (Builds.input i).binary ih false

lemma builds_stars {n : ℕ} (neighbors : Fin n → List (Fin n)) (cover : List (Fin n)) :
    Builds n (fun x => cover.any fun u => x u && (neighbors u).any (fun v => x v))
      cover.length := by
  induction cover with
  | nil => exact Builds.zero n
  | cons u cover ih =>
    have star := (Builds.input u).binary (builds_any (neighbors u)) true
    simpa [Nat.add_comm] using star.binary ih false

lemma upper_bound {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (hT : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    ∃ C : Circuit, Monotone2 C ∧
      (∃ A : Finset ℕ, A.card ≤ T.card ∧ TracksAnd C.gates A) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  let neighbors (u : Fin n) := (Finset.univ.filter (G.Adj u)).toList
  obtain ⟨gs, o, A, hmono, htracks, hcard, _, heval⟩ :=
    builds_stars neighbors T.toList n le_rfl
  refine ⟨⟨gs, o⟩, hmono, ⟨A, by simpa using hcard, htracks⟩, ?_⟩
  intro x
  have hx (i : Fin n) : (List.ofFn x).getD i false = x i := by simp
  change (run gs (List.ofFn x)).getD o false = true ↔ _
  rw [heval _ (by simp)]
  simp only [hx, List.any_eq_true, Bool.and_eq_true, Finset.mem_toList, neighbors,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, _, hu, v, huv, hv⟩
    exact ⟨u, v, huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases hT u v huv with h | h
    · exact ⟨u, h, hu, v, huv, hv⟩
    · exact ⟨v, h, hv, u, huv.symm, hu⟩

end PEqualNP.Outside.L_meta_214

theorem PEqualNP.Outside.L_meta_214 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ T.card ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :=
  fun _ G T hT => PEqualNP.Outside.L_meta_214.upper_bound G T hT
