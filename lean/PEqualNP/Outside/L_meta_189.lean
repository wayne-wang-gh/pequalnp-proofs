import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_189

private abbrev Input (n : ℕ) := Fin n → Bool

private def gate (g : Bool) (a b : Bool) : Bool :=
  if g then a || b else a && b

private def join {n : ℕ} (g : Bool) (a b : DMFormula n) : DMFormula n :=
  if g then .or a b else .and a b

private theorem join_eval {n : ℕ} (g : Bool) (a b : DMFormula n) (x : Input n) :
    (join g a b).eval x = gate g (a.eval x) (b.eval x) := by
  cases g <;> rfl

private theorem join_leaves {n : ℕ} (g : Bool) (a b : DMFormula n) :
    (join g a b).leaves = a.leaves + b.leaves := by
  cases g <;> rfl

private theorem join_induct {n : ℕ} {P : DMFormula n → Prop}
    (lit : ∀ i b, P (.lit i b))
    (bin : ∀ g a b, P a → P b → P (join g a b)) (φ : DMFormula n) : P φ := by
  induction φ with
  | lit i b => exact lit i b
  | and a b ha hb => exact bin false a b ha hb
  | or a b ha hb => exact bin true a b ha hb

private def count {n : ℕ} (D : Finset (Fin n)) : DMFormula n → ℕ
  | .lit v _ => if v ∈ D then 1 else 0
  | .and a b | .or a b => count D a + count D b

private theorem count_join {n : ℕ} (D : Finset (Fin n)) (g : Bool) (a b : DMFormula n) :
    count D (join g a b) = count D a + count D b := by
  cases g <;> rfl

private abbrev outside {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) := count Dᶜ φ

private theorem outside_join {n : ℕ} (D : Finset (Fin n)) (g : Bool) (a b : DMFormula n) :
    outside D (join g a b) = outside D a + outside D b :=
  count_join Dᶜ g a b

private theorem count_add_outside {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) :
    count D φ + outside D φ = φ.leaves := by
  induction φ using join_induct with
  | lit i b => by_cases h : i ∈ D <;> simp [count, DMFormula.leaves, h]
  | bin g a b ha hb => rw [join_leaves, count_join, outside_join]; omega

private def splice {n : ℕ} (D : Finset (Fin n)) (x y : Input n) : Input n :=
  fun v => if v ∈ D then x v else y v

private theorem eval_agree {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n)
    (h : ∀ v ∈ D, x v = y v) (hφ : outside D φ = 0) : φ.eval x = φ.eval y := by
  induction φ using join_induct with
  | lit i b =>
    have hi : i ∈ D := by by_contra hi; simp [count, hi] at hφ
    simp [DMFormula.eval, h i hi]
  | bin g a b ha hb =>
    rw [outside_join] at hφ
    rw [join_eval, join_eval, ha (by omega), hb (by omega)]

private theorem essential {n : ℕ} {φ : DMFormula n} {v : Fin n}
    {x y : Input n} (ha : ∀ w, w ≠ v → x w = y w)
    (hne : φ.eval x ≠ φ.eval y) : 0 < count {v} φ := by
  by_contra! hz
  apply hne
  refine eval_agree ({v}ᶜ) φ x y (by simpa using ha) ?_
  change count ({v}ᶜ)ᶜ φ = 0
  rw [compl_compl]
  omega

private theorem count_sum {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) :
    count D φ = ∑ v ∈ D, count {v} φ := by
  induction φ using join_induct with
  | lit i b => simp [count]
  | bin g a b ha hb => simp only [count_join, Finset.sum_add_distrib, ha, hb]

-- Restrictions simplify constant branches. The weight of a constant is zero.
private abbrev Reduced (n : ℕ) := Bool ⊕ DMFormula n

private def weight {n : ℕ} : Reduced n → ℕ
  | .inl _ => 0
  | .inr φ => φ.leaves

private def value {n : ℕ} (x : Input n) : Reduced n → Bool
  | .inl c => c
  | .inr φ => φ.eval x

private def combine {n : ℕ} (g : Bool) : Reduced n → Reduced n → Reduced n
  | .inl c, b => if c = g then .inl g else b
  | a, .inl c => if c = g then .inl g else a
  | .inr a, .inr b => .inr (join g a b)

private theorem combine_eval {n : ℕ} (g : Bool) (a b : Reduced n) (x : Input n) :
    value x (combine g a b) = gate g (value x a) (value x b) := by
  cases a with
  | inl c => cases g <;> cases c <;> cases b <;> simp [combine, value, gate]
  | inr a =>
    cases b with
    | inl c => cases g <;> cases c <;> simp [combine, value, gate]
    | inr b => exact join_eval _ _ _ _

private theorem combine_le {n : ℕ} (g : Bool) (a b : Reduced n) :
    weight (combine g a b) ≤ weight a + weight b := by
  cases a with
  | inl c => cases c <;> cases g <;> cases b <;> simp [combine, weight]
  | inr a =>
    cases b with
    | inl c => cases c <;> cases g <;> simp [combine, weight]
    | inr b => simp [combine, weight, join_leaves]

private def reduce {n : ℕ} (D : Finset (Fin n)) (x : Input n) : DMFormula n → Reduced n
  | .lit v b => if v ∈ D then .inl ((DMFormula.lit v b).eval x) else .inr (.lit v b)
  | .and a b => combine false (reduce D x a) (reduce D x b)
  | .or a b => combine true (reduce D x a) (reduce D x b)

private theorem reduce_join {n : ℕ} (D : Finset (Fin n)) (x : Input n)
    (g : Bool) (a b : DMFormula n) :
    reduce D x (join g a b) = combine g (reduce D x a) (reduce D x b) := by
  cases g <;> rfl

private theorem reduce_eval {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n) :
    value y (reduce D x φ) = φ.eval (splice D x y) := by
  induction φ using join_induct with
  | lit v b => by_cases h : v ∈ D <;> simp [reduce, splice, DMFormula.eval, h, value]
  | bin g a b ha hb => rw [reduce_join, combine_eval, ha, hb, join_eval]

private theorem reduce_le {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x : Input n) :
    weight (reduce D x φ) ≤ outside D φ := by
  induction φ using join_induct with
  | lit v b => by_cases h : v ∈ D <;> simp [reduce, count, h, weight, DMFormula.leaves]
  | bin g a b ha hb =>
    rw [reduce_join, outside_join]
    exact (combine_le _ _ _).trans (Nat.add_le_add ha hb)

private theorem reduce_pure {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x : Input n)
    (h : outside D φ = 0) : reduce D x φ = .inl (φ.eval x) := by
  induction φ using join_induct with
  | lit v b =>
    have hv : v ∈ D := by by_contra hv; simp [count, hv] at h
    simp [reduce, hv]
  | bin g a b ha hb =>
    rw [outside_join] at h
    rw [reduce_join, ha (by omega), hb (by omega), join_eval]
    cases g <;> cases a.eval x <;> cases b.eval x <;> rfl

-- A maximal subtree using only vertices in D can be pruned with its sibling
-- whenever its value absorbs their parent gate.
private def chunks {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) : List (DMFormula n) :=
  if outside D φ = 0 then [φ] else
    match φ with
    | .lit _ _ => []
    | .and a b | .or a b => chunks D a ++ chunks D b

private theorem chunks_join {n : ℕ} (D : Finset (Fin n)) (g : Bool) (a b : DMFormula n) :
    chunks D (join g a b) =
      if outside D a + outside D b = 0 then [join g a b] else chunks D a ++ chunks D b := by
  cases g <;> rw [chunks.eq_def, outside_join] <;> rfl

private theorem chunks_pure {n : ℕ} (D : Finset (Fin n)) (φ ψ : DMFormula n)
    (h : ψ ∈ chunks D φ) : outside D ψ = 0 := by
  induction φ using join_induct with
  | lit v b =>
    rw [chunks] at h
    split at h <;> simp_all
  | bin g a b ha hb =>
    rw [chunks_join] at h
    split at h
    · obtain rfl := List.mem_singleton.mp h
      rw [outside_join]; assumption
    · exact (List.mem_append.mp h).elim ha hb

private theorem chunks_sum {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) :
    ((chunks D φ).map DMFormula.leaves).sum = count D φ := by
  induction φ using join_induct with
  | lit v b => by_cases h : v ∈ D <;> simp [chunks, count, h, DMFormula.leaves]
  | bin g a b ha hb =>
    rw [chunks_join, count_join]
    split
    · have hab := count_add_outside D (join g a b)
      rw [count_join, outside_join] at hab
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    · simp [ha, hb]

private theorem chunks_agree {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n)
    (h : ∀ v ∉ D, x v = y v) (hs : ∀ ψ ∈ chunks D φ, ψ.eval x = ψ.eval y) :
    φ.eval x = φ.eval y := by
  induction φ using join_induct with
  | lit v b =>
    by_cases hv : v ∈ D
    · exact hs _ (by simp [chunks, count, hv])
    · simp [DMFormula.eval, h v hv]
  | bin g a b ha hb =>
    rw [chunks_join] at hs
    split at hs
    · exact hs _ (by simp)
    · rw [join_eval, join_eval, ha (fun ψ hψ => hs ψ (List.mem_append_left _ hψ)),
        hb (fun ψ hψ => hs ψ (List.mem_append_right _ hψ))]

private theorem chunks_fixed {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n)
    (hφ : 0 < outside D φ)
    (hx : outside D φ ≤ weight (reduce D x φ)) (hy : outside D φ ≤ weight (reduce D y φ)) :
    ∀ ψ ∈ chunks D φ, ψ.eval x = ψ.eval y := by
  induction φ using join_induct with
  | lit v b =>
    have hv : v ∉ D := by intro hv; simp [count, hv] at hφ
    simp [chunks, count, hv]
  | bin g a b ha hb =>
    rw [outside_join] at hφ hx hy
    rw [reduce_join] at hx hy
    have hm : outside D a + outside D b ≠ 0 := by omega
    simp only [chunks_join, hm, ite_false]
    have hax := reduce_le D a x
    have hay := reduce_le D a y
    have hbx := reduce_le D b x
    have hby := reduce_le D b y
    have hx' := combine_le g (reduce D x a) (reduce D x b)
    have hy' := combine_le g (reduce D y a) (reduce D y b)
    have pure_left (z : Input n) (hz : outside D a + outside D b ≤
        weight (combine g (reduce D z a) (reduce D z b))) (h : outside D a = 0) :
        a.eval z ≠ g := by
      rw [reduce_pure D a z h] at hz
      intro he
      simp [combine, he, weight] at hz
      omega
    have pure_right (z : Input n) (hz : outside D a + outside D b ≤
        weight (combine g (reduce D z a) (reduce D z b))) (h : outside D b = 0) :
        b.eval z ≠ g := by
      rw [reduce_pure D b z h] at hz
      intro he
      cases he' : reduce D z a <;> cases g <;> cases b.eval z <;>
        simp_all [combine, weight] <;> omega
    intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · by_cases h : outside D a = 0
      · obtain rfl : ψ = a := List.mem_singleton.mp (by simpa [chunks.eq_def, h] using hψ)
        have h₁ := pure_left x hx h
        have h₂ := pure_left y hy h
        exact (Bool.eq_not_of_ne h₁).trans (Bool.eq_not_of_ne h₂).symm
      · exact ha (by omega) (by omega) (by omega) ψ hψ
    · by_cases h : outside D b = 0
      · obtain rfl : ψ = b := List.mem_singleton.mp (by simpa [chunks.eq_def, h] using hψ)
        have h₁ := pure_right x hx h
        have h₂ := pure_right y hy h
        exact (Bool.eq_not_of_ne h₁).trans (Bool.eq_not_of_ne h₂).symm
      · exact hb (by omega) (by omega) (by omega) ψ hψ

private theorem leaves_pos {n : ℕ} (φ : DMFormula n) : 0 < φ.leaves := by
  induction φ using join_induct with
  | lit i b => exact Nat.one_pos
  | bin g a b ha hb => rw [join_leaves]; omega

private theorem eval_occ_agree {n : ℕ} (φ : DMFormula n) (x y : Input n)
    (h : ∀ v, 0 < count {v} φ → x v = y v) : φ.eval x = φ.eval y := by
  induction φ using join_induct with
  | lit v b => simp [DMFormula.eval, h v (by simp [count])]
  | bin g a b ha hb =>
    simp only [count_join] at h
    rw [join_eval, join_eval, ha (fun v hv => h v (by omega)),
      hb (fun v hv => h v (by omega))]

private theorem scope_in {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n)
    (h : outside D φ = 0) (v : Fin n) (hv : 0 < count {v} φ) : v ∈ D := by
  by_contra hv'
  have hmem : v ∈ Dᶜ := by simpa
  change count Dᶜ φ = 0 at h
  rw [count_sum] at h
  have := Finset.single_le_sum (f := fun v => count {v} φ) (fun _ _ => Nat.zero_le _) hmem
  omega

private theorem read_once_range {n : ℕ} (φ : DMFormula n)
    (h : ∀ v, count {v} φ ≤ 1) (c : Bool) : ∃ x, φ.eval x = c := by
  induction φ using join_induct with
  | lit v b => exact ⟨fun _ => if b then c else !c, by cases b <;> simp [DMFormula.eval]⟩
  | bin g a b ha hb =>
    simp only [count_join] at h
    obtain ⟨x, hx⟩ := ha (fun v => by have := h v; omega)
    obtain ⟨y, hy⟩ := hb (fun v => by have := h v; omega)
    let z : Input n := fun v => if 0 < count {v} a then x v else y v
    have hz₁ : a.eval z = c :=
      (eval_occ_agree a z x (fun v hv => by simp [z, hv])).trans hx
    have hz₂ : b.eval z = c :=
      (eval_occ_agree b z y (fun v hv => by have := h v; simp [z, show ¬0 < count {v} a by omega])).trans hy
    exact ⟨z, by cases g <;> cases c <;> simp [join_eval, hz₁, hz₂, gate]⟩

private theorem chunks_subcount {n : ℕ} (D S : Finset (Fin n)) (φ : DMFormula n) :
    ((chunks D φ).map (count S)).sum ≤ count S φ := by
  induction φ using join_induct with
  | lit v b => rw [chunks.eq_def]; split <;> simp
  | bin g a b ha hb =>
    rw [chunks_join]
    split
    · simp
    · simp only [List.map_append, List.sum_append, count_join]
      omega

private theorem chunk_count_le {n : ℕ} (D S : Finset (Fin n)) (φ ψ : DMFormula n)
    (h : ψ ∈ chunks D φ) : count S ψ ≤ count S φ :=
  (List.le_sum_of_mem (List.mem_map.mpr ⟨ψ, h, rfl⟩)).trans (chunks_subcount D S φ)

private def cofactorNe {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n) : Prop :=
  ∃ z, φ.eval (splice D x z) ≠ φ.eval (splice D y z)

private theorem chunks_dist {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y : Input n)
    (h : cofactorNe D φ x y) : ∃ ψ ∈ chunks D φ, ψ.eval x ≠ ψ.eval y := by
  by_contra! h'
  obtain ⟨z, hz⟩ := h
  apply hz
  apply chunks_agree D φ _ _ (by simp +contextual [splice])
  intro ψ hψ
  have hp := chunks_pure D φ ψ hψ
  have hx : ψ.eval (splice D x z) = ψ.eval x :=
    eval_agree D ψ _ _ (fun v hv => by simp [splice, hv]) hp
  have hy : ψ.eval (splice D y z) = ψ.eval y :=
    eval_agree D ψ _ _ (fun v hv => by simp [splice, hv]) hp
  exact hx.trans ((h' ψ hψ).trans hy.symm)

private theorem three_cofactors {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (x y z : Input n)
    (hxy : cofactorNe D φ x y) (hxz : cofactorNe D φ x z) (hyz : cofactorNe D φ y z) :
    2 ≤ (chunks D φ).length := by
  obtain ⟨a, ha, hxy'⟩ := chunks_dist D φ x y hxy
  obtain ⟨b, hb, hxz'⟩ := chunks_dist D φ x z hxz
  obtain ⟨c, hc, hyz'⟩ := chunks_dist D φ y z hyz
  cases h : chunks D φ with
  | nil => simp [h] at ha
  | cons head tail =>
    cases tail with
    | nil =>
      rw [h, List.mem_singleton] at ha hb hc
      subst a b c
      cases hx' : head.eval x <;> cases hy' : head.eval y <;>
        cases hz' : head.eval z <;> simp_all
    | cons head' tail => simp

private theorem count_essential {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n)
    (h : ∀ v ∈ D, 0 < count {v} φ) : D.card ≤ count D φ := by
  rw [count_sum]
  simpa using (Finset.sum_le_sum (s := D) (fun v hv => h v hv) :
    (∑ _ ∈ D, (1 : ℕ)) ≤ ∑ v ∈ D, count {v} φ)

private theorem count_once {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n)
    (h : ∀ v ∈ D, 0 < count {v} φ) (hb : count D φ ≤ D.card) {v : Fin n} (hv : v ∈ D) :
    count {v} φ ≤ 1 := by
  have he := count_essential (D.erase v) φ (fun w hw => h w (Finset.mem_of_mem_erase hw))
  rw [count_sum] at hb he
  rw [← Finset.sum_erase_add _ _ hv] at hb
  rw [Finset.card_erase_of_mem hv] at he
  have := Finset.card_pos.mpr ⟨v, hv⟩
  omega

private theorem star_saving {n : ℕ} (D : Finset (Fin n)) (φ : DMFormula n) (v : Fin n)
    (hv : v ∈ D) (h : ∀ w ∈ D, 0 < count {w} φ) (ho : 0 < outside D φ)
    (hthree : ∃ x y z, cofactorNe D φ x y ∧ cofactorNe D φ x z ∧ cofactorNe D φ y z) :
    ∃ x : Input n, x v = false ∧ weight (reduce D x φ) + (D.card + 1) ≤ φ.leaves := by
  have hc := count_essential D φ h
  have ht := count_add_outside D φ
  by_cases hb : D.card < count D φ
  · exact ⟨fun _ => false, rfl, by have := reduce_le D φ (fun _ => false); omega⟩
  push Not at hb
  by_contra! hn
  have hfull (x : Input n) (hx : x v = false) : outside D φ ≤ weight (reduce D x φ) := by
    have := hn x hx
    omega
  have hchunk : ∀ ψ ∈ chunks D φ, 1 ≤ count {v} ψ := by
    intro ψ hp
    by_contra! hz
    have hpure := chunks_pure D φ ψ hp
    have hro (w : Fin n) : count {w} ψ ≤ 1 := by
      by_cases hw : 0 < count {w} ψ
      · exact (chunk_count_le D {w} φ ψ hp).trans (count_once D φ h hb (scope_in D ψ hpure w hw))
      · omega
    obtain ⟨x, hx⟩ := read_once_range ψ hro false
    obtain ⟨y, hy⟩ := read_once_range ψ hro true
    let x' := splice {v} (fun _ => false) x
    let y' := splice {v} (fun _ => false) y
    have hxx := eval_occ_agree ψ x' x (fun w hw => by
      have hne : w ≠ v := by rintro rfl; omega
      simp [x', splice, hne])
    have hyy := eval_occ_agree ψ y' y (fun w hw => by
      have hne : w ≠ v := by rintro rfl; omega
      simp [y', splice, hne])
    have hs := chunks_fixed D φ x' y' ho (hfull x' (by simp [x', splice]))
      (hfull y' (by simp [y', splice])) ψ hp
    rw [hxx, hyy, hx, hy] at hs
    contradiction
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := hthree
  have hlen := three_cofactors D φ x y z hxy hxz hyz
  have hsum := chunks_subcount D {v} φ
  have hv' := count_once D φ h hb hv
  have hl : (chunks D φ).length ≤ ((chunks D φ).map (count {v})).sum := by
    generalize chunks D φ = l at hchunk ⊢
    induction l with
    | nil => simp
    | cons ψ l ih =>
      have hψ := hchunk ψ (by simp)
      have hl := ih (fun a ha => hchunk a (List.mem_cons_of_mem _ ha))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  omega

private def rename {n m : ℕ} (r : Fin n → Fin m) : DMFormula n → DMFormula m
  | .lit v b => .lit (r v) b
  | .and a b => .and (rename r a) (rename r b)
  | .or a b => .or (rename r a) (rename r b)

private theorem rename_eval {n m : ℕ} (r : Fin n → Fin m) (φ : DMFormula n) (x : Input m) :
    (rename r φ).eval x = φ.eval (x ∘ r) := by
  induction φ <;> simp_all [rename, DMFormula.eval, Function.comp_def]

private theorem rename_leaves {n m : ℕ} (r : Fin n → Fin m) (φ : DMFormula n) :
    (rename r φ).leaves = φ.leaves := by
  induction φ <;> simp_all [rename, DMFormula.leaves]

private theorem reduce_scope {n : ℕ} (D : Finset (Fin n)) (x : Input n) (φ ψ : DMFormula n)
    (h : reduce D x φ = .inr ψ) : count D ψ = 0 := by
  induction φ using join_induct generalizing ψ with
  | lit v b =>
    by_cases hv : v ∈ D
    · simp [reduce, hv] at h
    · simp [reduce, hv] at h
      subst ψ
      simp [count, hv]
  | bin g a b ha hb =>
    rw [reduce_join] at h
    cases he₁ : reduce D x a with
    | inl c =>
      cases c <;> cases g <;> simp [combine, he₁] at h
      all_goals exact hb ψ h
    | inr a' =>
      cases he₂ : reduce D x b with
      | inl c =>
        cases c <;> cases g <;> simp [combine, he₁, he₂] at h
        all_goals subst ψ; exact ha _ he₁
      | inr b' =>
        simp [combine, he₁, he₂] at h
        subst ψ
        rw [count_join, ha _ he₁, hb _ he₂]

private def vals (i : ℕ) : Input 3 := fun v => i.testBit v.val

private def table : DMFormula 3 → ℕ
  | .lit v b => if b then (![170, 204, 240] : Fin 3 → ℕ) v else
      (![85, 51, 15] : Fin 3 → ℕ) v
  | .and a b => table a &&& table b
  | .or a b => table a ||| table b

private theorem table_eval (φ : DMFormula 3) (i : ℕ) (hi : i < 8) :
    (table φ).testBit i = φ.eval (vals i) := by
  induction φ with
  | lit v b =>
    have h : ∀ (v : Fin 3) (b : Bool) (i : Fin 8),
        (table (.lit v b)).testBit i.val = (DMFormula.lit v b).eval (vals i.val) := by decide
    exact h v b ⟨i, hi⟩
  | and a b ha hb => simp [table, DMFormula.eval, ha, hb]
  | or a b ha hb => simp [table, DMFormula.eval, ha, hb]

-- Bit i of each set records whether truth table i is attainable at that leaf count.
-- The checks below certify that the sets contain all literals and are closed under gates.
private def tableSet : ℕ → ℕ
  | 1 => 0x1000000001000000004000000000000000000002000000008000000008000
  | 2 => 0x9429400020009001080084010000010000800000802100108009000400029429
  | 3 => 0xfdbfd401b021f1118c09cd050000950180a90000a0b39031888f840d802bfdbf
  | 4 => 0xfdbfd415b123f5398d0bdd2d0200bd0180bd0040b4bbd0b19cafc48da82bfdbf
  | 5 => 0xfffffd7df7bbfdbfdfaffdbfab03ff3dbcffc0d5fdbff5fbfdbfddefbebfffff
  | _ => 0

private def tables (k : ℕ) : List ℕ :=
  (List.range 256).filter (tableSet k).testBit

private theorem tables_iff {k t : ℕ} : t ∈ tables k ↔ t < 256 ∧ (tableSet k).testBit t = true := by
  simp [tables]

private def goodTables (k l : ℕ) : Bool :=
  (tables k).all fun x => (tables l).all fun y =>
    ((tableSet (k + l)).testBit (x &&& y) && (tableSet (k + l)).testBit (x ||| y))

set_option maxHeartbeats 2000000 in
private theorem tables_join {k l x y : ℕ} (hk : 0 < k) (hl : 0 < l) (hs : k + l ≤ 5)
    (hx : x ∈ tables k) (hy : y ∈ tables l) (g : Bool) :
    (if g then x ||| y else x &&& y) ∈ tables (k + l) := by
  have hkl : goodTables k l = true ∨ goodTables l k = true := by
    have h11 : goodTables 1 1 = true := by decide +kernel
    have h12 : goodTables 1 2 = true := by decide +kernel
    have h13 : goodTables 1 3 = true := by decide +kernel
    have h14 : goodTables 1 4 = true := by decide +kernel
    have h22 : goodTables 2 2 = true := by decide +kernel
    have h23 : goodTables 2 3 = true := by decide +kernel
    have hk' : k ≤ 4 := by omega
    have hl' : l ≤ 4 := by omega
    interval_cases k <;> interval_cases l <;> first | omega | tauto
  have hx' := (tables_iff.mp hx).1
  have hy' := (tables_iff.mp hy).1
  apply tables_iff.mpr
  constructor
  · cases g
    · exact Nat.lt_of_le_of_lt Nat.and_le_left hx'
    · exact Nat.or_lt_two_pow (n := 8) hx' hy'
  · rcases hkl with h | h
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h x hx) y hy
      simp only [Bool.and_eq_true] at hh
      cases g
      · exact hh.1
      · exact hh.2
    · have hh := List.all_eq_true.mp (List.all_eq_true.mp h y hy) x hx
      rw [Nat.add_comm l k, Nat.and_comm y x, Nat.or_comm y x] at hh
      simp only [Bool.and_eq_true] at hh
      cases g
      · exact hh.1
      · exact hh.2

private theorem table_mem (φ : DMFormula 3) (h : φ.leaves ≤ 5) :
    table φ ∈ tables φ.leaves := by
  induction φ using join_induct with
  | lit v b => apply tables_iff.mpr; fin_cases v <;> cases b <;> decide +kernel
  | bin g a b ha hb =>
    rw [join_leaves] at h ⊢
    have h' := tables_join (leaves_pos a) (leaves_pos b) h (ha (by omega)) (hb (by omega)) g
    cases g <;> exact h'

-- The attached triangle has three kinds of cofactors. These six pairs must be separated
-- by the subtrees confined to the triangle.
private def trianglePairs : List (ℕ × ℕ) :=
  [(1, 0), (3, 0), (3, 1), (5, 0), (5, 1), (6, 0)]

private def coversPair (t : ℕ) (p : ℕ × ℕ) : Bool := t.testBit p.1 != t.testBit p.2

private def stable (t : ℕ) : Bool :=
  (t.testBit 0 == t.testBit 2) && (t.testBit 0 == t.testBit 4)

private def mask (t : ℕ) : ℕ :=
    (if coversPair t (1, 0) then 1 else 0) |||
    (if coversPair t (3, 0) then 2 else 0) |||
    (if coversPair t (3, 1) then 4 else 0) |||
    (if coversPair t (5, 0) then 8 else 0) |||
    (if coversPair t (5, 1) then 16 else 0) |||
    (if coversPair t (6, 0) then 32 else 0)

private def stableMasks : ℕ → List ℕ
  | 1 => [11]
  | 2 => [0, 6, 11, 13, 19, 24, 32]
  | 3 => [0, 6, 11, 13, 19, 21, 24, 30, 32, 38, 43, 56]
  | 4 => [0, 6, 11, 13, 19, 21, 24, 30, 32, 38, 43, 45, 51, 56]
  | 5 => [0, 6, 11, 13, 19, 21, 24, 30, 32, 38, 43, 45, 51, 53, 56, 62]
  | _ => []

set_option maxHeartbeats 1500000 in
private theorem stableMasks_mem {k t : ℕ} (hk : k ≤ 5) (ht : t ∈ tables k)
    (hs : stable t = true) : mask t ∈ stableMasks k := by
  have h : ∀ i : Fin 6, (tables i.val).all
      (fun t => !stable t || (stableMasks i.val).contains (mask t)) = true := by decide +kernel
  have hh := List.all_eq_true.mp (h ⟨k, by omega⟩) t ht
  simpa [hs] using hh

private def masksWith (k : ℕ) (ms : List ℕ) : List ℕ :=
  ((stableMasks k).flatMap fun t => ms.map fun m => t ||| m).eraseDups

private def masks0 : List ℕ := [0]
private def masks1 : List ℕ := masksWith 1 masks0
private def masks2 : List ℕ := (masksWith 1 masks1 ++ masksWith 2 masks0).eraseDups
private def masks3 : List ℕ :=
  (masksWith 1 masks2 ++ masksWith 2 masks1 ++ masksWith 3 masks0).eraseDups
private def masks4 : List ℕ :=
  (masksWith 1 masks3 ++ masksWith 2 masks2 ++ masksWith 3 masks1 ++ masksWith 4 masks0).eraseDups
private def masks5 : List ℕ :=
  (masksWith 1 masks4 ++ masksWith 2 masks3 ++ masksWith 3 masks2 ++ masksWith 4 masks1 ++
    masksWith 5 masks0).eraseDups

private def masks : ℕ → List ℕ
  | 0 => masks0
  | 1 => masks1
  | 2 => masks2
  | 3 => masks3
  | 4 => masks4
  | 5 => masks5
  | _ => []

set_option maxRecDepth 4096 in
private theorem masks_step {k l t m : ℕ} (hk : 0 < k) (hs : k + l ≤ 5)
    (ht : t ∈ tables k) (hb : stable t = true) (hm : m ∈ masks l) :
    mask t ||| m ∈ masks (k + l) := by
  have h : mask t ||| m ∈ masksWith k (masks l) := by
    simp only [masksWith, List.mem_eraseDups, List.mem_flatMap, List.mem_map]
    exact ⟨mask t, stableMasks_mem (by omega) ht hb, m, hm, rfl⟩
  have hk' : k ≤ 5 := by omega
  have hl' : l ≤ 5 := by omega
  interval_cases k <;> interval_cases l <;>
    first | omega | (simp only [masks, masks2, masks3, masks4, masks5, List.mem_eraseDups,
      List.mem_append] at h ⊢; tauto)

private def totalMask (fs : List (DMFormula 3)) : ℕ :=
  (fs.map (mask ∘ table)).foldr (· ||| ·) 0

private theorem totalMask_mem (fs : List (DMFormula 3))
    (h : (fs.map DMFormula.leaves).sum ≤ 5) (hs : ∀ φ ∈ fs, stable (table φ) = true) :
    totalMask fs ∈ masks (fs.map DMFormula.leaves).sum := by
  induction fs with
  | nil => exact List.mem_singleton.mpr rfl
  | cons a fs ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    change mask (table a) ||| totalMask fs ∈ _
    exact masks_step (leaves_pos a) h (table_mem a (by omega)) (hs a (by simp))
      (ih (by omega) (fun φ hφ => hs φ (List.mem_cons_of_mem _ hφ)))

private theorem mask_bit (t : ℕ) (i : Fin 6) :
    (mask t).testBit i.val = coversPair t (trianglePairs.get i) := by
  have ht (c : Bool) (m j : ℕ) :
      (if c then m else 0).testBit j = (c && m.testBit j) := by
    cases c <;> simp
  have hb : ∀ j : Fin 6,
      (1 : ℕ).testBit j.val = decide (j = 0) ∧ (2 : ℕ).testBit j.val = decide (j = 1) ∧
      (4 : ℕ).testBit j.val = decide (j = 2) ∧ (8 : ℕ).testBit j.val = decide (j = 3) ∧
      (16 : ℕ).testBit j.val = decide (j = 4) ∧ (32 : ℕ).testBit j.val = decide (j = 5) := by decide
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb i
  simp only [mask, Nat.testBit_or, ht, h1, h2, h3, h4, h5, h6]
  fin_cases i <;> simp (config := { decide := true }) [trianglePairs]

private theorem totalMask_bit (fs : List (DMFormula 3)) (i : Fin 6)
    (h : ∃ φ ∈ fs, coversPair (table φ) (trianglePairs.get i) = true) :
    (totalMask fs).testBit i.val = true := by
  induction fs with
  | nil => simp at h
  | cons φ fs ih =>
    obtain ⟨ψ, hψ, hbit⟩ := h
    change ((mask (table φ)) ||| totalMask fs).testBit i.val = true
    rw [Nat.testBit_or, mask_bit, Bool.or_eq_true]
    rcases List.mem_cons.mp hψ with hψ | hψ
    · exact .inl (hψ ▸ hbit)
    · exact .inr (ih ⟨ψ, hψ, hbit⟩)

set_option maxHeartbeats 3000000 in
private theorem mask_excludes_full (k : ℕ) (hk : k ≤ 5) (m : ℕ) (h : m ∈ masks k) :
    ¬ ∀ i : Fin 6, m.testBit i.val = true := by
  have hc : ∀ k : Fin 6,
      ((masks k.val).all fun m => !(List.ofFn fun i : Fin 6 => m.testBit i.val).all id) = true := by
    decide +kernel
  have ht := List.all_eq_true.mp (hc ⟨k, by omega⟩) m h
  intro hb
  simp [List.all_eq_true, hb] at ht

private theorem triangle_chunks (fs : List (DMFormula 3))
    (hs : ∀ φ ∈ fs, stable (table φ) = true)
    (hd : ∀ i : Fin 6, ∃ φ ∈ fs, coversPair (table φ) (trianglePairs.get i) = true) :
    6 ≤ (fs.map DMFormula.leaves).sum := by
  by_contra! h
  exact mask_excludes_full _ (by omega) _ (totalMask_mem fs (by omega) hs)
    (fun i => totalMask_bit fs i (hd i))

private theorem majority_leaves (φ : DMFormula 3)
    (h : ∀ i : Fin 8, φ.eval (vals i.val) = (232 : ℕ).testBit i.val) : 5 ≤ φ.leaves := by
  by_contra! hb
  have ht := tables_iff.mp (table_mem φ (by omega))
  have ht' : table φ = 232 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · exact (table_eval φ i hi).trans (h ⟨i, hi⟩)
    · have hw : 8 ≤ i := by omega
      rw [Nat.testBit_eq_false_of_lt (n := table φ) (by
        exact ht.1.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hw)),
        Nat.testBit_eq_false_of_lt (n := 232) (by
        exact (show 232 < 2 ^ 8 by decide).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hw))]
  rw [ht'] at ht
  have he : ∀ k : Fin 5, (tableSet k.val).testBit 232 = false := by decide
  have hh := he ⟨φ.leaves, hb⟩
  rw [hh] at ht
  contradiction


open SimpleGraph

private abbrev Graph (n : ℕ) := SimpleGraph (Fin n)

private def cut {n : ℕ} (G : Graph n) (D : Finset (Fin n)) : Graph n where
  Adj u v := G.Adj u v ∧ u ∉ D ∧ v ∉ D
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private def cutDec {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n)) :
    DecidableRel (cut G D).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u ∉ D ∧ v ∉ D))

private theorem cut_adj {n : ℕ} (G : Graph n) (D : Finset (Fin n)) (u v : Fin n) :
    (cut G D).Adj u v ↔ G.Adj u v ∧ u ∉ D ∧ v ∉ D := Iff.rfl

private theorem cut_le {n : ℕ} (G : Graph n) (D : Finset (Fin n)) : cut G D ≤ G :=
  fun _ _ h => h.1

private def funOf {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (x : Input n) : Bool :=
  decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

private def active {n : ℕ} (G : Graph n) (x : Input n) : Prop :=
  ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

private theorem funOf_true {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (x : Input n) :
    funOf G x = true ↔ active G x := by simp [funOf, active]

private theorem funOf_false {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (x : Input n) :
    funOf G x = false ↔ ¬active G x := by simp [funOf, active]

private def bits {n : ℕ} (S : Finset (Fin n)) : Input n := fun v => decide (v ∈ S)

private theorem bits_true {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    bits S v = true ↔ v ∈ S := by simp [bits]

private theorem splice_bits {n : ℕ} (D X Y : Finset (Fin n)) :
    splice D (bits X) (bits Y) = bits ((X ∩ D) ∪ (Y \ D)) := by
  funext v
  by_cases h : v ∈ D <;> simp [splice, bits, h]

private theorem active_pair {n : ℕ} (G : Graph n) (a b : Fin n) :
    active G (bits {a, b}) ↔ G.Adj a b := by
  simp only [active, bits_true, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨u, v, huv, rfl | rfl, rfl | rfl⟩
    · exact (huv.ne rfl).elim
    · exact huv
    · exact huv.symm
    · exact (huv.ne rfl).elim
  · intro h
    exact ⟨a, b, h, .inl rfl, .inr rfl⟩

private theorem inactive_singleton {n : ℕ} (G : Graph n) (a : Fin n) :
    ¬active G (bits {a}) := by
  rw [show ({a} : Finset (Fin n)) = {a, a} by simp, active_pair]
  exact G.irrefl

private theorem inactive_empty {n : ℕ} (G : Graph n) :
    ¬active G (bits ∅) := by simp [active, bits_true]

private theorem graph_essential {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (φ : DMFormula n)
    (hφ : ∀ x, φ.eval x = funOf G x) {v w : Fin n} (h : G.Adj v w) :
    0 < count {v} φ := by
  apply essential (x := bits {v, w}) (y := bits {w})
  · intro u hu
    simp [bits, hu]
  · rw [hφ, hφ, (funOf_true _ _).2 ((active_pair _ _ _).2 h),
      (funOf_false _ _).2 (inactive_singleton G w)]
    decide

private theorem cut_eval {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (D : Finset (Fin n)) (x : Input n) (h : ∀ u v, G.Adj u v →
      u ∈ D → x u = true → v ∈ D ∧ x v = false)
    [DecidableRel (cut G D).Adj] (y : Input n) :
    funOf G (splice D x y) = funOf (cut G D) y := by
  apply Bool.eq_iff_iff.mpr
  rw [funOf_true, funOf_true]
  constructor
  · rintro ⟨u, v, ha, hu, hv⟩
    by_cases h₁ : u ∈ D
    · obtain ⟨h₂, hx⟩ := h u v ha h₁ (by simpa [splice, h₁] using hu)
      simp [splice, h₂, hx] at hv
    by_cases h₂ : v ∈ D
    · exact (h₁ (h v u ha.symm h₂ (by simpa [splice, h₂] using hv)).1).elim
    exact ⟨u, v, ⟨ha, h₁, h₂⟩, by simpa [splice, h₁] using hu,
      by simpa [splice, h₂] using hv⟩
  · rintro ⟨u, v, ⟨ha, h₁, h₂⟩, hu, hv⟩
    exact ⟨u, v, ha, by simpa [splice, h₁] using hu, by simpa [splice, h₂] using hv⟩

private theorem card_cut {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] :
    G.edgeFinset.card = (cut G D).edgeFinset.card +
      (G.edgeFinset \ (cut G D).edgeFinset).card := by
  have hsub : (cut G D).edgeFinset ⊆ G.edgeFinset := by
    intro e
    induction e using Sym2.ind
    simp only [mem_edgeFinset, mem_edgeSet]
    exact fun h => h.1
  have h := Finset.card_sdiff_add_card_eq_card hsub
  omega

private theorem removed_iff {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] (u v : Fin n) :
    s(u, v) ∈ G.edgeFinset \ (cut G D).edgeFinset ↔ G.Adj u v ∧ (u ∈ D ∨ v ∈ D) := by
  simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, cut_adj]
  tauto

private theorem cut_lt {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] {u v : Fin n} (h : G.Adj u v) (hu : u ∈ D) :
    (cut G D).edgeFinset.card < G.edgeFinset.card := by
  have hp := Finset.card_pos.mpr ⟨_, (removed_iff G D u v).2 ⟨h, Or.inl hu⟩⟩
  rw [card_cut G D]
  omega

private abbrev Tri {n : ℕ} (G : Graph n) (a b c : Fin n) : Prop :=
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

private abbrev OnTri {n : ℕ} (G : Graph n) (a : Fin n) : Prop :=
  ∃ b c, Tri G a b c

private abbrev Good {n : ℕ} (G : Graph n) [DecidableRel G.Adj] : Prop :=
  (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → p.length = 3) ∧
  (∀ a b c, Tri G a b c → G.degree a = 2 ∨ G.degree b = 2 ∨ G.degree c = 2) ∧
  (∀ a b c, Tri G a b c → G.degree a ≤ 3)

private theorem tri_rotate {n : ℕ} {G : Graph n} {a b c : Fin n} (h : Tri G a b c) :
    Tri G b c a := ⟨h.2.1, h.2.2, h.1⟩

private theorem neighbor_container {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    {a : Fin n} {N : Finset (Fin n)} (hs : ∀ b ∈ N, G.Adj a b)
    (hc : G.degree a ≤ N.card) : ∀ b, G.Adj a b ↔ b ∈ N := by
  have hsub : N ⊆ G.neighborFinset a := by
    intro v hv
    rw [mem_neighborFinset]
    exact hs v hv
  have he := Finset.eq_of_subset_of_card_le hsub hc
  simp [he]

private theorem degree_le_of_cut {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] (u : Fin n) :
    (cut G D).degree u ≤ G.degree u := by
  apply Finset.card_le_card
  intro w
  simp only [mem_neighborFinset]
  exact fun h => h.1

private theorem good_cut {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] (h : Good G) : Good (cut G D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u p hp
    simpa using h.1 u (p.mapLe (cut_le G D)) ((Walk.isCycle_mapLe _).2 hp)
  · intro a b c ht
    have ht' : Tri G a b c := ⟨ht.1.1, ht.2.1.1, ht.2.2.1⟩
    have hdeg (u v w : Fin n) (hv : (cut G D).Adj u v) (hw : (cut G D).Adj u w)
        (hne : v ≠ w) : 2 ≤ (cut G D).degree u := by
      have hsub : ({v, w} : Finset (Fin n)) ⊆ (cut G D).neighborFinset u := by
        intro x hx
        rw [mem_neighborFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hv
        · exact hw
      calc
        2 = ({v, w} : Finset (Fin n)).card := by simp [hne]
        _ ≤ (cut G D).degree u := Finset.card_le_card hsub
    rcases h.2.1 a b c ht' with ha | hb | hc
    · have := hdeg a b c ht.1 ht.2.2.symm ht.2.1.ne
      have := degree_le_of_cut G D a
      exact .inl (by omega)
    · have := hdeg b c a ht.2.1 ht.1.symm ht.2.2.ne
      have := degree_le_of_cut G D b
      exact .inr (.inl (by omega))
    · have := hdeg c a b ht.2.2 ht.2.1.symm ht.1.ne
      have := degree_le_of_cut G D c
      exact .inr (.inr (by omega))
  · intro a b c ht
    exact (degree_le_of_cut G D a).trans (h.2.2 a b c ⟨ht.1.1, ht.2.1.1, ht.2.2.1⟩)

private def triRow {n : ℕ} (a b c : Fin n) (i : ℕ) : Input n :=
  match i with
  | 0 => bits ∅
  | 1 => bits {a}
  | 2 => bits {b}
  | 3 => bits {a, b}
  | 4 => bits {c}
  | 5 => bits {a, c}
  | 6 => bits {b, c}
  | _ => bits {a, b, c}

private def triIndex {n : ℕ} (a b : Fin n) (v : Fin n) : Fin 3 :=
  if v = a then 0 else if v = b then 1 else 2

private theorem triRow_rename {n : ℕ} {G : Graph n} {a b c : Fin n} (ht : Tri G a b c)
    (φ : DMFormula n) (hp : outside {a, b, c} φ = 0) (i : Fin 8) :
    (rename (triIndex a b) φ).eval (vals i.val) = φ.eval (triRow a b c i.val) := by
  rw [rename_eval]
  apply eval_agree {a, b, c} _ _ _ _ hp
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  have hab := ht.1.ne
  have hbc := ht.2.1.ne
  have hca := ht.2.2.ne
  rcases hv with rfl | rfl | rfl <;> fin_cases i <;>
    simp [vals, triIndex, triRow, bits, hab, hab.symm, hbc, hbc.symm, hca, hca.symm] <;> decide

private theorem tri_eval {n : ℕ} (G : Graph n) [DecidableRel G.Adj] {a b c : Fin n}
    (ht : Tri G a b c) (i : Fin 8) :
    funOf G (triRow a b c i.val) = (232 : ℕ).testBit i.val := by
  fin_cases i
  · exact (funOf_false _ _).2 (inactive_empty G)
  · exact (funOf_false _ _).2 (inactive_singleton G a)
  · exact (funOf_false _ _).2 (inactive_singleton G b)
  · exact (funOf_true _ _).2 ((active_pair _ _ _).2 ht.1)
  · exact (funOf_false _ _).2 (inactive_singleton G c)
  · exact (funOf_true _ _).2 ((active_pair _ _ _).2 ht.2.2.symm)
  · exact (funOf_true _ _).2 ((active_pair _ _ _).2 ht.2.1)
  · exact (funOf_true _ _).2 ⟨a, b, ht.1, by simp [triRow, bits], by simp [triRow, bits]⟩

private theorem restrict_triangle {n : ℕ} (G : Graph n) [DecidableRel G.Adj] {a b c : Fin n}
    (ht : Tri G a b c) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x) :
    5 ≤ count {a, b, c} φ := by
  let D : Finset (Fin n) := {a, b, c}
  have he (i : Fin 8) : value (triRow a b c i.val) (reduce Dᶜ (bits ∅) φ) =
      (232 : ℕ).testBit i.val := by
    rw [reduce_eval, hφ]
    convert tri_eval G ht i using 2
    funext v
    by_cases hv : v ∈ D
    · simp [splice, hv]
    · have ha : v ≠ a := by intro h; apply hv; simp [D, h]
      have hb : v ≠ b := by intro h; apply hv; simp [D, h]
      have hc : v ≠ c := by intro h; apply hv; simp [D, h]
      fin_cases i <;> simp [splice, hv, triRow, bits, ha, hb, hc]
  have hb := reduce_le Dᶜ φ (bits ∅)
  change weight (reduce Dᶜ (bits ∅) φ) ≤ count Dᶜᶜ φ at hb
  rw [compl_compl] at hb
  cases h : reduce Dᶜ (bits ∅) φ with
  | inl q =>
    rw [h] at he
    have h0 := he 0
    have h3 := he 3
    change q = false at h0
    change q = true at h3
    rw [h0] at h3
    contradiction
  | inr ψ =>
    have hs := reduce_scope Dᶜ (bits ∅) φ ψ h
    have hm := majority_leaves (rename (triIndex a b) ψ) (fun i => by
      rw [triRow_rename ht ψ hs]
      simpa [h, value] using he i)
    rw [rename_leaves] at hm
    rw [h] at hb
    exact hm.trans hb

private theorem triRow_splice_empty {n : ℕ} (a b c : Fin n) (i : Fin 8) :
    splice {a, b, c} (triRow a b c i.val) (bits ∅) = triRow a b c i.val := by
  funext v
  by_cases hv : v ∈ ({a, b, c} : Finset (Fin n))
  · simp [splice, hv]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    fin_cases i <;> simp [triRow, splice, bits, hv.1, hv.2.1, hv.2.2]

private theorem attached_triangle_saving {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    {a b c p : Fin n} (ht : Tri G a b c) (hp : G.Adj a p)
    (hpn : p ∉ ({a, b, c} : Finset (Fin n)))
    (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x) :
    ∃ i : Fin 8, (i = 0 ∨ i = 2 ∨ i = 4) ∧
      weight (reduce {a, b, c} (triRow a b c i.val) φ) + 6 ≤ φ.leaves := by
  let D : Finset (Fin n) := {a, b, c}
  have ho : 0 < outside D φ := by
    apply (graph_essential G φ hφ hp.symm).trans_le
    change count {p} φ ≤ count Dᶜ φ
    rw [count_sum Dᶜ]
    apply Finset.single_le_sum (f := fun w => count {w} φ) (fun _ _ => Nat.zero_le _)
    simpa
  have hd := count_add_outside D φ
  have hc : 5 ≤ count D φ := restrict_triangle G ht φ hφ
  by_cases hlarge : 6 ≤ count D φ
  · refine ⟨0, .inl rfl, ?_⟩
    change weight (reduce D (triRow a b c 0) φ) + 6 ≤ φ.leaves
    have := reduce_le D φ (triRow a b c 0)
    omega
  by_contra! h
  have hfull (i : Fin 8) (hi : i = 0 ∨ i = 2 ∨ i = 4) :
      outside D φ ≤ weight (reduce D (triRow a b c i.val) φ) := by
    have := h i hi
    change φ.leaves < weight (reduce D (triRow a b c i.val) φ) + 6 at this
    omega
  let fs := (chunks D φ).map (rename (triIndex a b))
  have hstable : ∀ ψ ∈ fs, stable (table ψ) = true := by
    intro ψ hψ
    obtain ⟨ψ', hp', rfl⟩ := List.mem_map.mp hψ
    have hpur := chunks_pure D φ ψ' hp'
    simp only [stable, Bool.and_eq_true, beq_iff_eq]
    have hbit (i : Fin 8) : (table (rename (triIndex a b) ψ')).testBit i.val =
        ψ'.eval (triRow a b c i.val) := by
      rw [table_eval _ _ i.isLt, triRow_rename ht ψ' hpur]
    constructor
    · change (table (rename (triIndex a b) ψ')).testBit (0 : Fin 8).val =
        (table (rename (triIndex a b) ψ')).testBit (2 : Fin 8).val
      rw [hbit 0, hbit 2]
      exact chunks_fixed D φ _ _ ho (hfull 0 (.inl rfl)) (hfull 2 (.inr (.inl rfl))) ψ' hp'
    · change (table (rename (triIndex a b) ψ')).testBit (0 : Fin 8).val =
        (table (rename (triIndex a b) ψ')).testBit (4 : Fin 8).val
      rw [hbit 0, hbit 4]
      exact chunks_fixed D φ _ _ ho (hfull 0 (.inl rfl)) (hfull 4 (.inr (.inr rfl))) ψ' hp'
  have hdiff (i j : Fin 8) (hj : (232 : ℕ).testBit i.val ≠ (232 : ℕ).testBit j.val) :
      cofactorNe D φ (triRow a b c i.val) (triRow a b c j.val) := by
    refine ⟨bits ∅, ?_⟩
    simpa only [D, triRow_splice_empty, hφ, tri_eval G ht] using hj
  have hspecial : cofactorNe D φ (triRow a b c 1) (triRow a b c 0) := by
    refine ⟨bits {p}, ?_⟩
    have hL : splice D (triRow a b c 1) (bits {p}) = bits {a, p} := by
      change splice D (bits {a}) (bits {p}) = _
      rw [splice_bits]
      congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton]
      have ha : a ∈ D := by simp [D]
      grind
    have hR : splice D (triRow a b c 0) (bits {p}) = bits {p} := by
      change splice D (bits ∅) (bits {p}) = _
      rw [splice_bits]
      congr 1
      ext w
      simp only [Finset.empty_inter, Finset.empty_union, Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨And.left, fun hw => ⟨hw, hw.symm ▸ hpn⟩⟩
    rw [hL, hR, hφ, hφ, (funOf_true _ _).2 ((active_pair _ _ _).2 hp),
      (funOf_false _ _).2 (inactive_singleton G p)]
    decide
  have hsep : ∀ i : Fin 6, ∃ ψ ∈ fs, coversPair (table ψ) (trianglePairs.get i) = true := by
    have hpair (i j : Fin 8) (hij : cofactorNe D φ (triRow a b c i.val) (triRow a b c j.val)) :
        ∃ ψ ∈ fs, coversPair (table ψ) (i.val, j.val) = true := by
      obtain ⟨ψ, hψ, hne⟩ := chunks_dist D φ _ _ hij
      refine ⟨rename (triIndex a b) ψ, List.mem_map.mpr ⟨ψ, hψ, rfl⟩, ?_⟩
      have hpur := chunks_pure D φ ψ hψ
      simp only [coversPair, bne_iff_ne]
      rw [table_eval _ _ i.isLt, table_eval _ _ j.isLt, triRow_rename ht ψ hpur,
        triRow_rename ht ψ hpur]
      exact hne
    intro i
    fin_cases i
    · exact hpair 1 0 hspecial
    · exact hpair 3 0 (hdiff 3 0 (by decide))
    · exact hpair 3 1 (hdiff 3 1 (by decide))
    · exact hpair 5 0 (hdiff 5 0 (by decide))
    · exact hpair 5 1 (hdiff 5 1 (by decide))
    · exact hpair 6 0 (hdiff 6 0 (by decide))
  have hm := triangle_chunks fs hstable hsep
  unfold fs at hm
  simp only [List.map_map, Function.comp_def, rename_leaves, chunks_sum] at hm
  omega

private theorem tri_flip {n : ℕ} {G : Graph n} {a b c : Fin n} (h : Tri G a b c) :
    Tri G a c b := ⟨h.2.2.symm, h.2.1.symm, h.1.symm⟩

private theorem two_neighbors {n : ℕ} (G : Graph n) [DecidableRel G.Adj] {a b c : Fin n}
    (hab : G.Adj a b) (hac : G.Adj a c) (hne : b ≠ c) : 2 ≤ G.degree a := by
  have hsub : ({b, c} : Finset (Fin n)) ⊆ G.neighborFinset a := by
    intro w hw
    simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] at *
    rcases hw with rfl | rfl <;> assumption
  calc
    2 = ({b, c} : Finset (Fin n)).card := by simp [hne]
    _ ≤ G.degree a := Finset.card_le_card hsub

private theorem degree_two_neighbors {n : ℕ} {G : Graph n} [DecidableRel G.Adj]
    {a b c : Fin n} (ht : Tri G a b c) (hd : G.degree a = 2) (w : Fin n) :
    G.Adj a w ↔ w = b ∨ w = c := by
  have hne := ht.2.1.ne
  have h₀ : ∀ u ∈ ({b, c} : Finset (Fin n)), G.Adj a u := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro u (rfl | rfl)
    · exact ht.1
    · exact ht.2.2.symm
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    neighbor_container G h₀ (by simp [hne, hd]) w

private theorem degree_three_neighbors {n : ℕ} {G : Graph n} [DecidableRel G.Adj]
    {a b c p : Fin n} (ht : Tri G a b c) (hd : G.degree a ≤ 3)
    (hp : G.Adj a p) (hpb : p ≠ b) (hpc : p ≠ c) (w : Fin n) :
    G.Adj a w ↔ w = b ∨ w = c ∨ w = p := by
  have hne := ht.2.1.ne
  have h₀ : ∀ u ∈ ({b, c, p} : Finset (Fin n)), G.Adj a u := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro u (rfl | rfl | rfl)
    · exact ht.1
    · exact ht.2.2.symm
    · exact hp
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    neighbor_container G h₀ (by simpa [hne, hpb.symm, hpc.symm]) w

private theorem triangle_unique {n : ℕ} {G : Graph n} [DecidableRel G.Adj] (h : Good G)
    {a b c d e : Fin n} (ht : Tri G a b c) (ht' : Tri G a d e) :
    d = b ∨ d = c := by
  by_contra! hd
  have hfour {u v w x : Fin n} (huv : G.Adj u v) (hvw : G.Adj v w)
      (hwx : G.Adj w x) (hxu : G.Adj x u) (huw : u ≠ w) (hvx : v ≠ x) : False := by
    let p : G.Walk u u := .cons huv (.cons hvw (.cons hwx (.cons hxu .nil)))
    have hp : p.IsCycle := by
      rw [Walk.isCycle_iff_isPath_tail_and_le_length]
      have huv' := huv.ne
      have hvw' := hvw.ne
      have hwx' := hwx.ne
      have hxu' := hxu.ne
      simp [p, Walk.isPath_def, huv', hvw', hwx', hxu', huw, hvx,
        huv'.symm, hvw'.symm, hwx'.symm, hxu'.symm, huw.symm, hvx.symm]
    have hh := h.1 u p hp
    change 4 = 3 at hh
    omega
  rcases (degree_three_neighbors ht (h.2.2 a b c ht) ht'.1 hd.1 hd.2 e).1
      ht'.2.2.symm with he | he | he
  · subst e
    exact hfour ht.2.1 ht.2.2 ht'.1 ht'.2.1 ht.1.ne.symm hd.2.symm
  · subst e
    exact hfour ht.2.1.symm ht.1.symm ht'.1 ht'.2.1 ht.2.2.ne hd.1.symm
  · exact ht'.2.1.ne he.symm

private theorem degree_two_onTri_neighbor {n : ℕ} {G : Graph n} [DecidableRel G.Adj]
    {a w : Fin n} (ha : G.Adj a w) (ht : OnTri G w) (hd : G.degree w = 2) :
    ∃ b, Tri G a w b := by
  obtain ⟨b, c, ht⟩ := ht
  rcases (degree_two_neighbors ht hd a).1 ha.symm with rfl | rfl
  · exact ⟨c, tri_rotate (tri_flip ht) |> tri_rotate⟩
  · exact ⟨b, tri_rotate (tri_rotate ht)⟩

private theorem triangle_of_three_cycle {n : ℕ} {G : Graph n} {u : Fin n} (p : G.Walk u u)
    (h : p.length = 3) : ∃ v w, Tri G u v w := by
  cases p with
  | nil => simp at h
  | cons huv p =>
    cases p with
    | nil => simp at h
    | cons hvw p =>
      cases p with
      | nil => simp at h
      | cons hwx p =>
        cases p with
        | nil => exact ⟨_, _, huv, hvw, hwx⟩
        | cons hadj p => simp at h

private theorem path_start_leaf {n : ℕ} {G : Graph n} (hG : G.IsAcyclic)
    {u v : Fin n} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (a b : Fin n) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {w : Fin n} (hw : G.Adj u w) : w = p.snd := by
  apply hG.eq_snd_of_adj_start hp hw
  by_contra hn
  have hh := hmax _ _ (p.cons hw.symm) (hp.cons hn)
  simp at hh

private theorem peripheral_star {n : ℕ} (G : Graph n) (h : G.IsAcyclic)
    (he : ∃ u v, G.Adj u v) :
    ∃ u v p, G.Adj u v ∧
      (∀ w, G.Adj u w → w = v) ∧
      (∀ w, G.Adj v w → (∀ z, G.Adj w z → z = v) ∨ w = p) := by
  obtain ⟨a, b, hab⟩ := he
  letI : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨u, t, q, hq, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hlen := hmax a b hab.toWalk hab.isPath_toWalk
  cases q with
  | nil => simp at hlen
  | cons huv q =>
    refine ⟨u, _, q.snd, huv, ?_, ?_⟩
    · intro w hw
      simpa only [Walk.snd_cons] using path_start_leaf h hq hmax hw
    · intro w hvw
      by_cases hw : w = q.snd
      · exact .inr hw
      · left
        have htail := hq.of_cons
        have hn : w ∉ q.support := fun hm => hw (h.eq_snd_of_adj_start htail hvw hm)
        have hp : (q.cons hvw.symm).IsPath := htail.cons hn
        have hm (a b : Fin n) (r : G.Walk a b) (hr : r.IsPath) :
            r.length ≤ (q.cons hvw.symm).length := by
          simpa using hmax a b r hr
        intro z hz
        simpa only [Walk.snd_cons] using path_start_leaf h hp hm hz

-- If no triangle has two degree-two vertices, isolate the unique degree-two vertex
-- of every triangle. The remaining forest exposes a pendant star.
private theorem structural {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (h : Good G)
    (he : ∃ u v, G.Adj u v) :
    (∃ a b c, Tri G a b c ∧ G.degree b = 2 ∧ G.degree c = 2) ∨
    (∃ u v b c, G.Adj u v ∧ (∀ w, G.Adj u w → w = v) ∧
      Tri G v b c ∧ G.degree c = 2) ∨
    (∃ u v p, G.Adj u v ∧ (∀ w, G.Adj u w → w = v) ∧
      (∀ w, G.Adj v w → (∀ z, G.Adj w z → z = v) ∨ w = p)) := by
  classical
  by_cases hend : ∃ a b c, Tri G a b c ∧ G.degree b = 2 ∧ G.degree c = 2
  · exact .inl hend
  right
  let D := Finset.univ.filter fun w => OnTri G w ∧ G.degree w = 2
  have hD (w : Fin n) : w ∈ D ↔ OnTri G w ∧ G.degree w = 2 := by simp [D]
  have hnocut {a w : Fin n} (ha : ¬OnTri G a) (hw : G.Adj a w) : w ∉ D := by
    intro h
    obtain ⟨ht, hd⟩ := (hD w).1 h
    obtain ⟨b, hb⟩ := degree_two_onTri_neighbor hw ht hd
    exact ha ⟨w, b, hb⟩
  have hone {a b c : Fin n} (ht : Tri G a b c) (hc : c ∈ D) :
      a ∉ D ∧ b ∉ D := by
    have hc' := ((hD c).1 hc).2
    constructor
    · exact fun ha => hend ⟨b, c, a, tri_rotate ht, hc', ((hD a).1 ha).2⟩
    · exact fun hb => hend ⟨a, b, c, ht, ((hD b).1 hb).2, hc'⟩
  let H := cut G D
  letI : DecidableRel H.Adj := cutDec G D
  have hacy : H.IsAcyclic := by
    intro a q hq
    have hq' := h.1 a (q.mapLe (cut_le G D)) ((Walk.isCycle_mapLe _).2 hq)
    have hl : q.length = 3 := by simpa using hq'
    obtain ⟨b, c, ht⟩ := triangle_of_three_cycle q hl
    have ht' : Tri G a b c := ⟨ht.1.1, ht.2.1.1, ht.2.2.1⟩
    rcases h.2.1 a b c ht' with ha | hb | hc
    · exact ht.1.2.1 ((hD a).2 ⟨⟨b, c, ht'⟩, ha⟩)
    · exact ht.2.1.2.1 ((hD b).2 ⟨⟨c, a, tri_rotate ht'⟩, hb⟩)
    · exact ht.2.2.2.1 ((hD c).2 ⟨⟨a, b, tri_rotate (tri_rotate ht')⟩, hc⟩)
  have hremaining : ∃ u v, H.Adj u v := by
    obtain ⟨u, v, huv⟩ := he
    have hkeep (w : Fin n) (hw : w ∈ D) : ∃ a b, H.Adj a b := by
      obtain ⟨⟨a, b, ht⟩, _⟩ := (hD w).1 hw
      have hk := hone (tri_rotate ht) hw
      exact ⟨a, b, ht.2.1, hk.1, hk.2⟩
    by_cases hu : u ∈ D
    · exact hkeep u hu
    by_cases hv : v ∈ D
    · exact hkeep v hv
    exact ⟨u, v, huv, hu, hv⟩
  have hleaf {a b : Fin n} (hab : H.Adj a b) (hl : ∀ w, H.Adj a w → w = b) :
      ¬ OnTri G a := by
    rintro ⟨c, d, ht⟩
    have hno {c d : Fin n} (ht : Tri G a c d) (hd : G.degree d = 2) : False := by
      have hd' : d ∈ D := (hD d).2 ⟨⟨a, c, tri_rotate (tri_rotate ht)⟩, hd⟩
      have hc' := (hone ht hd').2
      have hcb := hl c ⟨ht.1, hab.2.1, hc'⟩
      have hda : G.degree a = 3 := by
        have ha := two_neighbors G ht.1 ht.2.2.symm ht.2.1.ne
        have hle := h.2.2 a c d ht
        have hne : G.degree a ≠ 2 := fun heq => hab.2.1 ((hD a).2 ⟨⟨c, d, ht⟩, heq⟩)
        omega
      have hbig : ∃ p, G.Adj a p ∧ p ≠ c ∧ p ≠ d := by
        by_contra! h'
        have hl' : G.neighborFinset a ⊆ ({c, d} : Finset (Fin n)) := by
          intro w hw
          rw [mem_neighborFinset] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases hwc : w = c
          · exact .inl hwc
          · exact .inr (h' w hw hwc)
        have hcard := Finset.card_le_card hl'
        change G.degree a ≤ _ at hcard
        simp [ht.2.1.ne, hda] at hcard
      obtain ⟨p, hp, hpc, hpd⟩ := hbig
      have hp' : p ∉ D := by
        intro hpD
        obtain ⟨hpT, hp2⟩ := (hD p).1 hpD
        obtain ⟨e, he'⟩ := degree_two_onTri_neighbor hp hpT hp2
        exact (triangle_unique h ht he').elim hpc hpd
      exact hpc ((hl p ⟨hp, hab.2.1, hp'⟩).trans hcb.symm)
    rcases h.2.1 a c d ht with ha | hc | hd
    · exact hab.2.1 ((hD a).2 ⟨⟨c, d, ht⟩, ha⟩)
    · exact hno (tri_flip ht) hc
    · exact hno ht hd
  obtain ⟨u, v, p, huv, hu, hv⟩ := peripheral_star H hacy hremaining
  have hut := hleaf huv hu
  have hu' (w : Fin n) (hw : G.Adj u w) : w = v := hu w ⟨hw, huv.2.1, hnocut hut hw⟩
  by_cases hvt : OnTri G v
  · left
    obtain ⟨b, c, ht⟩ := hvt
    rcases h.2.1 v b c ht with hv2 | hb2 | hc2
    · exact (huv.2.2 ((hD v).2 ⟨⟨b, c, ht⟩, hv2⟩)).elim
    · exact ⟨u, v, c, b, huv.1, hu', tri_flip ht, hb2⟩
    · exact ⟨u, v, b, c, huv.1, hu', ht, hc2⟩
  · right
    refine ⟨u, v, p, huv.1, hu', fun w hw => ?_⟩
    have hvw : H.Adj v w := ⟨hw, huv.2.2, hnocut hvt hw⟩
    rcases hv w hvw with hw' | hwp
    · left
      have hwt := hleaf hvw.symm hw'
      exact fun z hz => hw' z ⟨hz, hvw.2.2, hnocut hwt hz⟩
    · exact .inr hwp

private abbrev Budget {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ G.edgeFinset.card + S.card ≤ k

private abbrev Smaller {n : ℕ} (G : Graph n) [DecidableRel G.Adj] : Prop :=
  ∀ (H : Graph n) [DecidableRel H.Adj], H.edgeFinset.card < G.edgeFinset.card →
    Good H → ∀ r : Reduced n, (∀ y, value y r = funOf H y) → Budget H (weight r)

-- Charge the removed edges and the cover extension against leaves saved by a restriction.
private theorem use_cut {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (hg : Good G) (ih : Smaller G)
    (D : Finset (Fin n)) [DecidableRel (cut G D).Adj] (φ : DMFormula n)
    (hφ : ∀ x, φ.eval x = funOf G x) (x : Input n)
    (hx : ∀ u v, G.Adj u v → u ∈ D → x u = true → v ∈ D ∧ x v = false)
    (he : ∃ u ∈ D, ∃ v, G.Adj u v) (e k : ℕ)
    (hm : (G.edgeFinset \ (cut G D).edgeFinset).card ≤ e)
    (hs : ∀ S, CoverPromise.IsVertexCover (cut G D) S → ∃ T, CoverPromise.IsVertexCover G T ∧ T.card ≤ S.card + k)
    (hb : weight (reduce D x φ) + e + k ≤ φ.leaves) : Budget G φ.leaves := by
  obtain ⟨u, hu, v, huv⟩ := he
  obtain ⟨S, hS, hcard⟩ := ih (cut G D) (cut_lt G D huv hu) (good_cut G D hg) (reduce D x φ)
    (fun y => by rw [reduce_eval, hφ, cut_eval G D x hx y])
  obtain ⟨T, hT, hcard'⟩ := hs S hS
  refine ⟨T, hT, ?_⟩
  have := card_cut G D
  omega

private theorem removed_sub {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (D : Finset (Fin n))
    [DecidableRel (cut G D).Adj] (E : Finset (Sym2 (Fin n)))
    (he : ∀ u v, G.Adj u v → u ∈ D → s(u, v) ∈ E) :
    (G.edgeFinset \ (cut G D).edgeFinset).card ≤ E.card := by
  apply Finset.card_le_card
  intro e
  induction e using Sym2.ind with
  | h u v =>
    rw [removed_iff]
    rintro ⟨h, hu | hv⟩
    · exact he u v h hu
    · rw [Sym2.eq_swap]
      exact he v u h.symm hv

private theorem peel_triangle_pendant {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (hg : Good G) (ih : Smaller G) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x)
    {u v b c : Fin n} (huv : G.Adj u v) (hu : ∀ w, G.Adj u w → w = v)
    (ht : Tri G v b c) (hc : G.degree c = 2) : Budget G φ.leaves := by
  let D : Finset (Fin n) := {u}
  letI : DecidableRel (cut G D).Adj := cutDec G D
  have hub : u ≠ b := by
    rintro rfl
    exact ht.2.2.ne (hu c ht.2.1)
  have huc : u ≠ c := by
    rintro rfl
    exact ht.1.ne.symm (hu b ht.2.1.symm)
  refine use_cut G hg ih D φ hφ (fun _ => false) (by simp) ⟨u, by simp [D], v, huv⟩ 1 0 ?_ ?_ ?_
  · refine (removed_sub G D {s(u, v)} (fun a w haw ha => ?_)).trans (by simp)
    have ha' : a = u := by simpa [D] using ha
    subst a
    rw [hu w haw]
    simp
  · intro S hS
    by_cases hv : v ∈ S
    · refine ⟨S, ?_, by simp⟩
      intro a w haw
      by_cases ha : a = u
      · subst a; exact .inr (hu w haw ▸ hv)
      by_cases hw : w = u
      · subst w; exact .inl (hu a haw.symm ▸ hv)
      exact hS a w ⟨haw, by simpa [D], by simpa [D]⟩
    have hcv : (cut G D).Adj c v := ⟨ht.2.2, by simpa [D] using huc.symm,
      by simpa [D] using huv.ne.symm⟩
    have hbc : (cut G D).Adj v b := ⟨ht.1, by simpa [D] using huv.ne.symm,
      by simpa [D] using hub.symm⟩
    have hc' : c ∈ S := (hS c v hcv).resolve_right hv
    have hb : b ∈ S := (hS v b hbc).resolve_left hv
    refine ⟨insert v (S.erase c), ?_, ?_⟩
    · intro a w haw
      have hhit (a w : Fin n) (haw : G.Adj a w) (ha : a = u ∨ a = c) :
          w ∈ insert v (S.erase c) := by
        rcases ha with rfl | rfl
        · simp [hu w haw]
        · rcases (degree_two_neighbors (tri_rotate (tri_rotate ht)) hc w).1 haw with rfl | rfl
          · simp
          · simp [hb, ht.2.1.ne]
      by_cases ha : a = u ∨ a = c
      · exact .inr (hhit a w haw ha)
      by_cases hw : w = u ∨ w = c
      · exact .inl (hhit w a haw.symm hw)
      have ha' : a ≠ u ∧ a ≠ c := not_or.mp ha
      have hw' : w ≠ u ∧ w ≠ c := not_or.mp hw
      rcases hS a w ⟨haw, by simpa [D] using ha'.1, by simpa [D] using hw'.1⟩ with h | h
      · exact .inl (by simp [h, ha'.2])
      · exact .inr (by simp [h, hw'.2])
    · have hne : v ∉ S.erase c := fun h => hv (Finset.mem_of_mem_erase h)
      rw [Finset.card_insert_of_notMem hne, Finset.card_erase_of_mem hc']
      have := Finset.card_pos.mpr ⟨c, hc'⟩
      omega
  · have he := graph_essential G φ hφ huv
    have hr := reduce_le D φ (fun _ => false)
    have ht := count_add_outside D φ
    change 0 < count D φ at he
    omega

private theorem empty_splice {n : ℕ} (D X : Finset (Fin n)) (hX : X ⊆ D) :
    splice D (bits X) (bits ∅) = bits X := by
  rw [splice_bits]
  simp [Finset.inter_eq_left.mpr hX]

private theorem peel_star {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (hg : Good G) (ih : Smaller G) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x)
    {u v p : Fin n} (huv : G.Adj u v) (hu : ∀ w, G.Adj u w → w = v)
    (hv : ∀ w, G.Adj v w → (∀ z, G.Adj w z → z = v) ∨ w = p) : Budget G φ.leaves := by
  classical
  let L := (G.neighborFinset v).filter fun w => ∀ z, G.Adj w z → z = v
  let D := insert v L
  letI : DecidableRel (cut G D).Adj := cutDec G D
  have hL (w : Fin n) : w ∈ L ↔ G.Adj v w ∧ ∀ z, G.Adj w z → z = v := by simp [L]
  have hvL : v ∉ L := fun h => ((hL v).1 h).1.ne rfl
  have hvD : v ∈ D := by simp [D]
  have huD : u ∈ D := Finset.mem_insert_of_mem ((hL u).2 ⟨huv.symm, hu⟩)
  have hcard : D.card = L.card + 1 := Finset.card_insert_of_notMem hvL
  have hD (w : Fin n) : w ∈ D ↔ w = v ∨ w ∈ L := by simp [D]
  have he (w : Fin n) (hw : w ∈ D) : 0 < count {w} φ := by
    rcases (hD w).1 hw with rfl | hw
    · exact graph_essential G φ hφ huv.symm
    · exact graph_essential G φ hφ ((hL w).1 hw).1.symm
  have hcut (x : Input n) (hx : x v = false) (a b : Fin n) (hab : G.Adj a b)
      (ha : a ∈ D) (hax : x a = true) : b ∈ D ∧ x b = false := by
    rcases (hD a).1 ha with rfl | ha
    · rw [hx] at hax; contradiction
    · rw [((hL a).1 ha).2 b hab]
      exact ⟨hvD, hx⟩
  have hcover (S : Finset (Fin n)) (hS : CoverPromise.IsVertexCover (cut G D) S) :
      ∃ T, CoverPromise.IsVertexCover G T ∧ T.card ≤ S.card + 1 := by
    refine ⟨insert v S, ?_, Finset.card_insert_le _ _⟩
    intro a b hab
    have hcent (a b : Fin n) (ha : a ∈ D) (hab : G.Adj a b) : a = v ∨ b = v := by
      exact ((hD a).1 ha).imp_right (fun ha => ((hL a).1 ha).2 b hab)
    by_cases ha : a ∈ D
    · rcases hcent a b ha hab with rfl | rfl <;> simp
    by_cases hb : b ∈ D
    · rcases hcent b a hb hab.symm with rfl | rfl <;> simp
    exact (hS a b ⟨hab, ha, hb⟩).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
  let E := L.image fun w => s(v, w)
  have hE (a b : Fin n) (hab : G.Adj a b) (ha : a ∈ D)
      (hh : ∀ w, G.Adj v w → w ∈ L ∨ s(v, w) ∈ ({s(v, p)} : Finset _)) :
      s(a, b) ∈ insert s(v, p) E := by
    rcases (hD a).1 ha with rfl | ha
    · rcases hh b hab with hl | hp
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hl)
      · rw [Finset.mem_singleton.mp hp]
        exact Finset.mem_insert_self _ _
    · rw [((hL a).1 ha).2 b hab, Sym2.eq_swap (a := a) (b := v)]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)
  by_cases hp : G.Adj v p ∧ p ∉ D
  · have hthree : ∃ x y z, cofactorNe D φ x y ∧ cofactorNe D φ x z ∧ cofactorNe D φ y z := by
      refine ⟨bits ∅, bits {v}, bits {u, v}, ?_, ?_, ?_⟩
      · refine ⟨bits {p}, ?_⟩
        have h0 : splice D (bits ∅) (bits {p}) = bits {p} := by
          rw [splice_bits]
          congr 1
          ext w
          simp +contextual [hp.2]
        have h1 : splice D (bits {v}) (bits {p}) = bits {v, p} := by
          rw [splice_bits]
          congr 1
          ext w
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
            Finset.mem_insert, Finset.mem_singleton]
          grind [hp.2]
        rw [h0, h1, hφ, hφ, (funOf_false _ _).2 (inactive_singleton G p),
          (funOf_true _ _).2 ((active_pair _ _ _).2 hp.1)]
        decide
      · refine ⟨bits ∅, ?_⟩
        rw [empty_splice D ∅ (by simp), empty_splice D {u, v} (Finset.insert_subset_iff.mpr ⟨huD, Finset.singleton_subset_iff.mpr hvD⟩), hφ, hφ,
          (funOf_false _ _).2 (inactive_empty G), (funOf_true _ _).2 ((active_pair _ _ _).2 huv)]
        decide
      · refine ⟨bits ∅, ?_⟩
        rw [empty_splice D {v} (Finset.singleton_subset_iff.mpr hvD), empty_splice D {u, v} (Finset.insert_subset_iff.mpr ⟨huD, Finset.singleton_subset_iff.mpr hvD⟩), hφ, hφ,
          (funOf_false _ _).2 (inactive_singleton G v), (funOf_true _ _).2 ((active_pair _ _ _).2 huv)]
        decide
    have ho : 0 < outside D φ := by
      apply (graph_essential G φ hφ hp.1.symm).trans_le
      change count {p} φ ≤ count Dᶜ φ
      rw [count_sum Dᶜ]
      exact Finset.single_le_sum (f := fun w => count {w} φ) (fun _ _ => Nat.zero_le _) (by simpa using hp.2)
    obtain ⟨x, hx, hb⟩ := star_saving D φ v hvD he ho hthree
    refine use_cut G hg ih D φ hφ x (hcut x hx) ⟨u, huD, v, huv⟩
      (L.card + 1) 1 ?_ hcover (by omega)
    refine (removed_sub G D (insert s(v, p) E) (fun a b hab ha => hE a b hab ha ?_)).trans ?_
    · intro w hw
      rcases hv w hw with hl | rfl
      · exact .inl ((hL w).2 ⟨hw, hl⟩)
      · exact .inr (by simp)
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le _)
  · refine use_cut G hg ih D φ hφ (fun _ => false) (hcut _ rfl) ⟨u, huD, v, huv⟩
      L.card 1 ?_ hcover ?_
    · refine (removed_sub G D E (fun a b hab ha => ?_)).trans Finset.card_image_le
      rcases (hD a).1 ha with rfl | ha
      · apply Finset.mem_image_of_mem
        rcases hv b hab with hl | rfl
        · exact (hL b).2 ⟨hab, hl⟩
        · exact ((hD b).1 (by by_contra hn; exact hp ⟨hab, hn⟩)).resolve_left hab.ne.symm
      · rw [((hL a).1 ha).2 b hab, Sym2.eq_swap (a := a) (b := v)]
        exact Finset.mem_image_of_mem _ ha
    · have hr := reduce_le D φ (fun _ => false)
      have hc := count_essential D φ he
      have ht := count_add_outside D φ
      omega

private theorem peel_triangle {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (hg : Good G) (ih : Smaller G) (φ : DMFormula n) (hφ : ∀ x, φ.eval x = funOf G x)
    {a b c : Fin n} (ht : Tri G a b c) (hb : G.degree b = 2) (hc : G.degree c = 2) :
    Budget G φ.leaves := by
  let D : Finset (Fin n) := {a, b, c}
  letI : DecidableRel (cut G D).Adj := cutDec G D
  have haD : a ∈ D := by simp [D]
  have hbD : b ∈ D := by simp [D]
  have hcD : c ∈ D := by simp [D]
  have hbn := degree_two_neighbors (tri_rotate ht) hb
  have hcn := degree_two_neighbors (tri_rotate (tri_rotate ht)) hc
  have hab := ht.1.ne
  have hbc := ht.2.1.ne
  have hca := ht.2.2.ne
  have hcover (S : Finset (Fin n)) (hS : CoverPromise.IsVertexCover (cut G D) S) :
      ∃ T, CoverPromise.IsVertexCover G T ∧ T.card ≤ S.card + 2 := by
    refine ⟨insert a (insert b S), ?_, ?_⟩
    · have hhit (u v : Fin n) (hu : u ∈ D) (h : G.Adj u v) :
          u ∈ insert a (insert b S) ∨ v ∈ insert a (insert b S) := by
        simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · simp
        · simp
        · rcases (hcn v).1 h with rfl | rfl <;> simp
      intro u v huv
      by_cases hu : u ∈ D
      · exact hhit u v hu huv
      by_cases hv : v ∈ D
      · exact (hhit v u hv huv.symm).symm
      exact (hS u v ⟨huv, hu, hv⟩).imp (fun h => by simp [h]) (fun h => by simp [h])
    · have h₁ := Finset.card_insert_le a (insert b S)
      have h₂ := Finset.card_insert_le b S
      omega
  have hcut (i : Fin 8) (hi : i = 0 ∨ i = 2 ∨ i = 4) (u v : Fin n) (huv : G.Adj u v)
      (_ : u ∈ D) (hu : triRow a b c i.val u = true) :
      v ∈ D ∧ triRow a b c i.val v = false := by
    rcases hi with rfl | rfl | rfl
    · change bits ∅ u = true at hu
      simp [bits] at hu
    · change bits {b} u = true at hu
      have hub : u = b := by simpa [bits] using hu
      subst u
      change v ∈ D ∧ bits {b} v = false
      rcases (hbn v).1 huv with rfl | rfl <;> simp [bits, D, hbc.symm, hab]
    · change bits {c} u = true at hu
      have huc : u = c := by simpa [bits] using hu
      subst u
      change v ∈ D ∧ bits {c} v = false
      rcases (hcn v).1 huv with rfl | rfl <;> simp [bits, D, hbc, hca.symm]
  let E : Finset (Sym2 (Fin n)) := {s(a, b), s(b, c), s(c, a)}
  have hE : E.card ≤ 3 := by
    have h₁ := Finset.card_insert_le s(a,b) ({s(b,c), s(c,a)} : Finset _)
    have h₂ := Finset.card_insert_le s(b,c) ({s(c,a)} : Finset _)
    simp only [Finset.card_singleton] at h₂
    change E.card ≤ 3
    unfold E
    omega
  have hin (u v : Fin n) (huv : G.Adj u v) (hu : u ∈ D) (hv : v ∈ D) :
      s(u, v) ∈ E := by
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first | exact (huv.ne rfl).elim | simp [E] | rw [Sym2.eq_swap]; simp [E]
  by_cases hp : ∃ p, G.Adj a p ∧ p ∉ D
  · obtain ⟨p, hp, hpD⟩ := hp
    obtain ⟨i, hi, hr⟩ := attached_triangle_saving G ht hp hpD φ hφ
    have hp' : p ≠ b ∧ p ≠ c := ⟨fun e => hpD (e ▸ hbD), fun e => hpD (e ▸ hcD)⟩
    have han := degree_three_neighbors ht (hg.2.2 a b c ht) hp hp'.1 hp'.2
    refine use_cut G hg ih D φ hφ (triRow a b c i.val) (hcut i hi)
      ⟨a, haD, b, ht.1⟩ 4 2 ?_ hcover (by omega)
    refine (removed_sub G D (insert s(a, p) E) (fun u v huv hu => ?_)).trans ?_
    · by_cases hv : v ∈ D
      · exact Finset.mem_insert_of_mem (hin u v huv hu hv)
      simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · rcases (han v).1 huv with rfl | rfl | rfl
        · exact (hv hbD).elim
        · exact (hv hcD).elim
        · simp
      · rcases (hbn v).1 huv with rfl | rfl
        · exact (hv hcD).elim
        · exact (hv haD).elim
      · rcases (hcn v).1 huv with rfl | rfl
        · exact (hv haD).elim
        · exact (hv hbD).elim
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hE 1)
  · refine use_cut G hg ih D φ hφ (triRow a b c 0) (hcut 0 (.inl rfl))
      ⟨a, haD, b, ht.1⟩ 3 2 ?_ hcover ?_
    · refine (removed_sub G D E (fun u v huv hu => hin u v huv hu ?_)).trans hE
      simp only [D, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · by_contra hn
        exact hp ⟨v, huv, hn⟩
      · rcases (hbn v).1 huv with rfl | rfl
        · exact hcD
        · exact haD
      · rcases (hcn v).1 huv with rfl | rfl
        · exact haD
        · exact hbD
    · have hr := reduce_le D φ (triRow a b c 0)
      have ht' := count_add_outside D φ
      have hc' : 5 ≤ count D φ := restrict_triangle G ht φ hφ
      omega

private theorem no_edges_budget {n : ℕ} (G : Graph n) [DecidableRel G.Adj]
    (h : ¬ ∃ u v, G.Adj u v) (k : ℕ) : Budget G k := by
  have he : G.edgeFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e
    induction e using Sym2.ind with
    | h u v =>
      simp only [mem_edgeFinset, mem_edgeSet]
      exact fun huv => h ⟨u, v, huv⟩
  exact ⟨∅, fun u v huv => (h ⟨u, v, huv⟩).elim, by simp [he]⟩

private theorem lower_bound {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (hg : Good G)
    (r : Reduced n) (hr : ∀ y, value y r = funOf G y) : Budget G (weight r) := by
  generalize hk : G.edgeFinset.card = k
  induction k using Nat.strong_induction_on generalizing G r with
  | ind k ih =>
    by_cases he : ∃ u v, G.Adj u v
    · cases r with
      | inl d =>
        obtain ⟨u, v, huv⟩ := he
        have h₀ := (hr (bits ∅)).trans ((funOf_false _ _).2 (inactive_empty G))
        have h₁ := (hr (bits {u, v})).trans ((funOf_true _ _).2 ((active_pair _ _ _).2 huv))
        exact (Bool.false_ne_true (h₀.symm.trans h₁)).elim
      | inr φ =>
        have hi : Smaller G := by
          intro H _ hlt hh p hp
          exact ih H.edgeFinset.card (hk ▸ hlt) H hh p hp rfl
        rcases structural G hg he with ⟨a, b, c, ht, hb, hc⟩ |
            ⟨u, v, b, c, huv, hu, ht, hc⟩ | ⟨u, v, p, huv, hu, hv⟩
        · exact peel_triangle G hg hi φ hr ht hb hc
        · exact peel_triangle_pendant G hg hi φ hr huv hu ht hc
        · exact peel_star G hg hi φ hr huv hu hv
    · exact no_edges_budget G he _

private theorem or_vars {n : ℕ} (S : Finset (Fin n)) :
    ∃ r : Reduced n, weight r ≤ S.card ∧
      ∀ x, value x r = true ↔ ∃ v ∈ S, x v = true := by
  induction S using Finset.induction_on with
  | empty => exact ⟨.inl false, by simp [weight, value]⟩
  | @insert v S hv ih =>
    obtain ⟨r, hr, he⟩ := ih
    refine ⟨combine true (.inr (.lit v true)) r, ?_, ?_⟩
    · have h := combine_le true (.inr (.lit v true)) r
      rw [Finset.card_insert_of_notMem hv]
      change weight (combine true (.inr (.lit v true)) r) ≤ 1 + weight r at h
      omega
    · intro x
      rw [combine_eval]
      change (x v || value x r) = true ↔ ∃ w ∈ insert v S, x w = true
      rw [Bool.or_eq_true, he x]
      simp only [Finset.mem_insert]
      constructor
      · rintro (hx | ⟨w, hw, hx⟩)
        · exact ⟨v, .inl rfl, hx⟩
        · exact ⟨w, .inr hw, hx⟩
      · rintro ⟨w, rfl | hw, hx⟩
        · exact .inl hx
        · exact .inr ⟨w, hw, hx⟩

private theorem upper_bound {n : ℕ} (S : Finset (Fin n))
    (G : Graph n) [DecidableRel G.Adj] (hS : CoverPromise.IsVertexCover G S) :
    ∃ r : Reduced n, weight r ≤ G.edgeFinset.card + S.card ∧ ∀ x, value x r = funOf G x := by
  induction S using Finset.induction_on generalizing G with
  | empty =>
    have h : ∀ u v, ¬G.Adj u v := by
      intro u v hu
      simpa using hS u v hu
    exact ⟨.inl false, Nat.zero_le _, fun x => ((funOf_false _ _).2
      (fun ⟨u, v, huv, _⟩ => h u v huv)).symm⟩
  | @insert v S hv ih =>
    let H := G.deleteIncidenceSet v
    have hH : CoverPromise.IsVertexCover H S := by
      intro a b hab
      obtain ⟨hab, ha, hb⟩ := deleteIncidenceSet_adj.mp hab
      simpa [Finset.mem_insert, ha, hb] using hS a b hab
    obtain ⟨r, hr, he⟩ := ih H hH
    obtain ⟨o, ho, hoe⟩ := or_vars (G.neighborFinset v)
    let a := combine false (.inr (.lit v true)) o
    refine ⟨combine true a r, ?_, ?_⟩
    · have h₁ := combine_le true a r
      have h₂ := combine_le false (.inr (.lit v true)) o
      change weight a ≤ 1 + weight o at h₂
      have h₃ := card_edgeFinset_deleteIncidenceSet G v
      have h₄ : G.degree v ≤ G.edgeFinset.card := by
        rw [← card_incidenceFinset_eq_degree]
        exact Finset.card_le_card (G.incidenceFinset_subset _)
      change H.edgeFinset.card = _ at h₃
      change weight o ≤ G.degree v at ho
      rw [Finset.card_insert_of_notMem hv]
      omega
    · intro x
      have ha : value x a = (x v && value x o) := by
        unfold a
        rw [combine_eval]
        rfl
      have hl : value x (combine true a r) = ((x v && value x o) || funOf H x) := by
        rw [combine_eval, ha, he]
        rfl
      rw [hl]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, hoe x, mem_neighborFinset, funOf_true]
      constructor
      · rintro (⟨hv, w, hw, hx⟩ | ⟨u, w, huw, hu, hw⟩)
        · exact ⟨v, w, hw, hv, hx⟩
        · exact ⟨u, w, (deleteIncidenceSet_adj.mp huw).1, hu, hw⟩
      · rintro ⟨u, w, huw, hu, hw⟩
        by_cases heq : u = v
        · subst u
          exact .inl ⟨hu, w, huw, hw⟩
        by_cases hweq : w = v
        · subst w
          exact .inl ⟨hw, u, huw.symm, hu⟩
        exact .inr ⟨u, w, deleteIncidenceSet_adj.mpr ⟨huw, heq, hweq⟩, hu, hw⟩

private theorem main {n : ℕ} (G : Graph n) [DecidableRel G.Adj] (t s : ℕ)
    (he : ∃ u v, G.Adj u v) (hg : Good G)
    (ht : ∃ S, CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hmin : ∀ S, CoverPromise.IsVertexCover G S → t ≤ S.card) :
    HasLeafSize n (funOf G) s ↔ G.edgeFinset.card + t ≤ s := by
  constructor
  · rintro ⟨φ, hs, hp⟩
    obtain ⟨S, hS, hb⟩ := lower_bound G hg (.inr φ) hp
    exact (Nat.add_le_add_left (hmin S hS) _).trans (hb.trans hs)
  · intro hs
    obtain ⟨S, hS, rfl⟩ := ht
    obtain ⟨r, hb, hr⟩ := upper_bound S G hS
    cases r with
    | inr φ => exact ⟨φ, hb.trans hs, hr⟩
    | inl d =>
      obtain ⟨u, v, huv⟩ := he
      have h₀ := (hr (bits ∅)).trans ((funOf_false _ _).2 (inactive_empty G))
      have h₁ := (hr (bits {u, v})).trans ((funOf_true _ _).2 ((active_pair _ _ _).2 huv))
      exact (Bool.false_ne_true (h₀.symm.trans h₁)).elim

end PEqualNP.Outside.L_meta_189

theorem PEqualNP.Outside.L_meta_189 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t s : ℕ), (∃ u v : Fin n, G.Adj u v) → (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → p.length = 3) → (∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj c a → ((Finset.univ.filter fun w => G.Adj a w).card = 2 ∨ (Finset.univ.filter fun w => G.Adj b w).card = 2 ∨ (Finset.univ.filter fun w => G.Adj c w).card = 2)) → (∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj c a → (Finset.univ.filter fun w => G.Adj a w).card ≤ 3) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (PEqualNP.MetaComplexity.HasLeafSize n (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) s ↔ G.edgeFinset.card + t ≤ s) := by
  intro n G _ t s he hcyc htwo hthree ht hmin
  apply PEqualNP.Outside.L_meta_189.main G t s he ?_ ht hmin
  refine ⟨hcyc, ?_, ?_⟩
  · intro a b c h
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using htwo a b c h.1 h.2.1 h.2.2
  · intro a b c h
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using hthree a b c h.1 h.2.1 h.2.2
