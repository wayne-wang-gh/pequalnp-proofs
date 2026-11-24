import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1019

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma two_inputs (ins : List ℕ) (h : ins.length ≤ 2) :
    ∃ a b : ℕ, ∀ j ∈ ins, j = a ∨ j = b := by
  match ins, h with
  | [], _ => exact ⟨0, 0, by simp⟩
  | [a], _ => exact ⟨a, a, by simp⟩
  | [a, b], _ => exact ⟨a, b, by simp⟩
  | _ :: _ :: _ :: _, h => simp at h

def Depends {n : ℕ} (gs : List Gate) (i : ℕ) (t : Fin n) : Prop :=
  ∃ x y : Fin n → Bool, (∀ j, j ≠ t → x j = y j) ∧ val gs x i ≠ val gs y i

lemma components {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (label : Fin n → ℕ) (wire : ℕ → ℕ),
      S.card ≤ (S.image label).card + gs.length ∧
      ∀ i t, Depends gs i t → label t = wire i := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.val, id, ?_, ?_⟩
    · simp [Finset.card_image_of_injective _ Fin.val_injective]
    · rintro i t ⟨x, y, hxy, hne⟩
      rw [val_nil, val_nil] at hne
      by_cases hi : i < n
      · simp only [hi, dite_true] at hne
        have he : (⟨i, hi⟩ : Fin n) = t := by
          by_contra h
          exact hne (hxy _ h)
        exact congrArg Fin.val he.symm
      · simp [hi] at hne
  | append_singleton gs g ih =>
    obtain ⟨label, wire, hcount, hdep⟩ := ih (fun g' h => hg g' (by simp [h]))
    obtain ⟨a, b, hinputs⟩ := two_inputs g.inputs (hg g (by simp))
    let merge (k : ℕ) := if k = wire b then wire a else k
    have ha : merge (wire a) = wire a := by simp [merge]
    have hb : merge (wire b) = wire a := by simp [merge]
    refine ⟨merge ∘ label, fun i => if i = n + gs.length then wire a else merge (wire i),
      ?_, ?_⟩
    · have hsub : S.image label ⊆ insert (wire b) (S.image (merge ∘ label)) := by
        intro v hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
        by_cases he : label t = wire b
        · simp [he]
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, by simp [merge, he]⟩)
      have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      simp only [List.length_append, List.length_cons, List.length_nil] at ⊢
      omega
    · rintro i t ⟨x, y, hxy, hne⟩
      rw [val_snoc, val_snoc] at hne
      by_cases hi : i = n + gs.length
      · simp only [hi, ite_true, Function.comp_apply] at hne ⊢
        have hd : val gs x a ≠ val gs y a ∨ val gs x b ≠ val gs y b := by
          by_contra! hh
          apply hne
          apply congrArg g.op.eval
          apply List.map_congr_left
          intro j hj
          rcases hinputs j hj with rfl | rfl
          · exact hh.1
          · exact hh.2
        rcases hd with hd | hd
        · rw [hdep a t ⟨x, y, hxy, hd⟩, ha]
        · rw [hdep b t ⟨x, y, hxy, hd⟩, hb]
      · simp only [hi, ite_false, Function.comp_apply] at hne ⊢
        rw [hdep i t ⟨x, y, hxy, hne⟩]

def line (k : Fin 3) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image
    (fun u => u + (if k = 0 then 0 else if k = 1 then 12 else 10))

def points : Finset (Fin 13) := Finset.univ.biUnion line

def full (k : Fin 3) (v : Fin 13) : Bool :=
  decide (v ∈ line k ∨ v ∈ ({4, 5, 7} : Finset (Fin 13)))

def cut (k : Fin 3) (t v : Fin 13) : Bool := if v = t then false else full k v

def weight (x : Fin 13 → Bool) : ℕ := (Finset.univ.filter fun i => x i = true).card

lemma full_weight : ∀ k : Fin 3, weight (full k) = 7 := by decide

lemma cut_weight : ∀ (k : Fin 3) (t : Fin 13), t ∈ line k → weight (cut k t) = 6 := by
  decide

lemma line_depends (gs : List Gate) (out : Fin 3 → ℕ)
    (spec : ∀ (k : Fin 3) (x : Fin 13 → Bool), weight x = 6 ∨ weight x = 7 →
      val gs x (out k) = decide (∀ v ∈ line k, x v = true))
    (k : Fin 3) (t : Fin 13) (ht : t ∈ line k) : Depends gs (out k) t := by
  refine ⟨full k, cut k t, ?_, ?_⟩
  · intro j hj
    simp [cut, hj]
  · rw [spec k _ (Or.inr (full_weight k)), spec k _ (Or.inl (cut_weight k t ht))]
    have hfull : ∀ v ∈ line k, full k v = true := fun v hv => by simp [full, hv]
    have hcut : ¬ ∀ v ∈ line k, cut k t v = true := by
      intro h
      simpa [cut] using h t ht
    simp [hcut]
    exact hfull

end PEqualNP.Outside.L_meta_1019

open PEqualNP.Outside.L_meta_1019

theorem PEqualNP.Outside.L_meta_1019 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 3 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin 13 → Bool, ((Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 6 ∨ (Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 7) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 0⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 0)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 1⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 12)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 2⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 10)), x v = true)) → 9 ≤ gates.length := by
  intro gs out hg hcorrect
  have spec : ∀ (k : Fin 3) (x : Fin 13 → Bool), weight x = 6 ∨ weight x = 7 →
      val gs x (out k) = decide (∀ v ∈ line k, x v = true) := by
    intro k x hw
    obtain ⟨h₀, h₁, h₂⟩ := hcorrect x hw
    fin_cases k
    · exact h₀
    · exact h₁
    · exact h₂
  obtain ⟨label, wire, hcount, hdep⟩ := components points gs (fun g h => (hg g h).2)
  have hzero : ∀ k : Fin 3, 0 ∈ line k := by decide
  have same : ∀ t ∈ points, label t = label 0 := by
    intro t ht
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp ht
    exact (hdep _ _ (line_depends gs out spec k t hk)).trans
      (hdep _ _ (line_depends gs out spec k 0 (hzero k))).symm
  have hsub : points.image label ⊆ {label 0} := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_singleton.mpr (same t ht)
  have hc := Finset.card_le_card hsub
  have hs : points.card = 10 := by decide
  rw [Finset.card_singleton] at hc
  omega
