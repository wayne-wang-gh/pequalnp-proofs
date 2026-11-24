import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1632

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma fold_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (step w g) i (by rw [step_len]; omega), step_lt w g i hi]

lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ l l' : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p0 ∈ L l' ∧ p1 ∉ L l') → l ≠ l' → ∀ p ∈ L l, p ≠ p0 → p1 ∉ L l' ∧ p ∉ L l') ∧
    (∀ m m' : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p1 ∈ L m' ∧ p0 ∉ L m') → m ≠ m' → ∀ p ∈ L m, p ≠ p1 → p0 ∉ L m' ∧ p ∉ L m') ∧
    (∀ m : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → p0 ∉ L m) ∧ (∀ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → p1 ∉ L l) ∧
    (∀ M m : Fin N, (p0 ∉ L M ∧ p1 ∉ L M) → (p1 ∈ L m ∧ p0 ∉ L m) → ∀ p ∈ L M, p ∉ L m → p0 ∉ L m ∧ p ∉ L m) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ∃ c : Fin N, L l ∩ L m = {c}) ∧
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      ∀ p t : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false ↔ p ∈ L t) := by
  intro q N L i0 p0 p1 _ _ _ hint _ _ _ _
  have key : ∀ a b : Fin N, a ≠ b → ∀ x y : Fin N, x ∈ L a → x ∈ L b → y ∈ L a → y ∈ L b →
      x = y := by
    intro a b hab x y hxa hxb hya hyb
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hint a b hab)
    have hx : x ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨hxa, hxb⟩
    have hy : y ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨hya, hyb⟩
    rw [hc] at hx hy
    rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l2 hl hl2 hne p hp hpne
    exact ⟨hl2.2, fun hp2 => hpne (key l l2 hne p p0 hp hp2 hl.1 hl2.1)⟩
  · intro m m2 hm hm2 hne p hp hpne
    exact ⟨hm2.2, fun hp2 => hpne (key m m2 hne p p1 hp hp2 hm.1 hm2.1)⟩
  · intro m hm
    exact hm.2
  · intro l hl
    exact hl.2
  · intro M m _ hm p _ hpm
    exact ⟨hm.2, hpm⟩
  · intro l m hl hm
    have hne : l ≠ m := by
      intro h
      rw [h] at hl
      exact hm.2 hl.1
    exact Finset.card_eq_one.mp (hint l m hne)
  · intro gates _ _ _ p t
    have hv : Circuit.eval ⟨gates, (p : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t)))
        = decide (p ∉ L t) := by
      have h1 : (gates.foldl step (List.ofFn (fun v : Fin N => decide (v ∉ L t)))).getD
          (p : ℕ) false = (List.ofFn (fun v : Fin N => decide (v ∉ L t))).getD (p : ℕ) false :=
        fold_lt gates _ _ (by simp)
      rw [ofFn_getD_val] at h1
      exact h1
    rw [hv]
    simp

end PEqualNP.Outside.L_meta_1632

theorem PEqualNP.Outside.L_meta_1632 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ l l' : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p0 ∈ L l' ∧ p1 ∉ L l') → l ≠ l' → ∀ p ∈ L l, p ≠ p0 → p1 ∉ L l' ∧ p ∉ L l') ∧
    (∀ m m' : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p1 ∈ L m' ∧ p0 ∉ L m') → m ≠ m' → ∀ p ∈ L m, p ≠ p1 → p0 ∉ L m' ∧ p ∉ L m') ∧
    (∀ m : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → p0 ∉ L m) ∧ (∀ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → p1 ∉ L l) ∧
    (∀ M m : Fin N, (p0 ∉ L M ∧ p1 ∉ L M) → (p1 ∈ L m ∧ p0 ∉ L m) → ∀ p ∈ L M, p ∉ L m → p0 ∉ L m ∧ p ∉ L m) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ∃ c : Fin N, L l ∩ L m = {c}) ∧
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      ∀ p t : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (p : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false ↔ p ∈ L t) :=
  PEqualNP.Outside.L_meta_1632.main_aux
