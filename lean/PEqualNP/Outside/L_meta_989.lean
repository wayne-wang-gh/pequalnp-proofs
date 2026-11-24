import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_989
open Matrix MvPolynomial

private theorem fourOrth {F : Type} [Field F] {p q a b : Fin 3 → F}
    (hp : p ≠ 0) (hq : q ≠ 0) (ha : a ≠ 0)
    (hpq : ∀ c : F, q ≠ c • p) (hab : ∀ c : F, b ≠ c • a)
    (pa : dotProduct p a = 0) (pb : dotProduct p b = 0)
    (qa : dotProduct q a = 0) (qb : dotProduct q b = 0) : False := by
  have nc : crossProduct a b ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr
    ((LinearIndependent.pair_iff' ha).mpr (by simpa [eq_comm] using hab))
  have cx (v : Fin 3 → F) (v0 : v ≠ 0) (va : dotProduct v a = 0) (vb : dotProduct v b = 0) :
      Projectivization.mk F v v0 = Projectivization.mk F (crossProduct a b) nc := by
    apply (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero v0 nc).mpr
    rw [cross_cross_eq_smul_sub_smul', dotProduct_comm a v, va, vb, zero_smul, zero_smul, sub_self]
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' F q p hq hp).mp
    ((cx q hq qa qb).trans (cx p hp pa pb).symm)
  exact hpq c hc.symm

private noncomputable def form {F : Type} [Field F] (v : Fin 3 → F) : MvPolynomial (Fin 3) F :=
  ∑ t, C (v t) * X t

private theorem separated {F : Type} [Field F] {k b : ℕ} (P : Fin k → MvPolynomial (Fin 3) F)
    (l : Fin k → Fin 3 → F) (hd : ∀ i, (P i).IsHomogeneous b)
    (diag : ∀ i, eval (l i) (P i) ≠ 0)
    (off : ∀ i j, i ≠ j → eval (l j) (P i) = 0) :
    2 * k ≤ (b + 1) * (b + 2) := by
  classical
  let A := (Finset.univ : Finset (Fin 3)).finsuppAntidiag b
  let W (i : Fin k) (d : ↥A) : F := (P i).coeff d.val
  have ind : LinearIndependent F W := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hp : ∑ i, c i • P i = 0 := by
      ext d
      by_cases h : d ∈ A
      · have e := congrFun hc (⟨d,h⟩ : ↥A)
        simpa [W, Finset.sum_apply, coeff_sum] using e
      · have van (i : Fin k) : (P i).coeff d = 0 := by
          by_contra ne
          apply h
          simpa [A, Finset.mem_finsuppAntidiag, Finsupp.weight_apply, Finsupp.sum_fintype] using hd i ne
        simp [van]
    have v := congrArg (eval (l j)) hp
    simp only [map_sum, smul_eq_C_mul, map_mul, eval_C, map_zero] at v
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [off i j hij]) (by simp)] at v
    exact (mul_eq_zero.mp v).resolve_right (diag j)
  have hh := ind.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_pi, Fintype.card_coe] at hh
  rw [show A.card = (b+2).choose b by
    simpa [A, Nat.add_comm, Nat.add_assoc] using
      Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin 3))) b] at hh
  rw [← Nat.choose_symm (show b ≤ b+2 by omega), show b+2-b=2 by omega,
    Nat.choose_two_right] at hh
  have htwo := Nat.div_mul_le_self ((b+2)*(b+2-1)) 2
  have h := Nat.mul_le_mul_right 2 hh
  have he : b+2-1 = b+1 := by omega
  rw [he] at htwo h
  nlinarith

private theorem upper : ∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2) := by
  classical
  intro F _ n k b pt l y g hp hpp hl hll hy havoid safe two
  have hit (i j : Fin k) (hij : i ≠ j) : ∃ v ∈ y i, dotProduct (pt v) (l j) = 0 := by
    obtain ⟨p,q,hpq,pa,qa,gp,gq⟩ := two i
    by_contra! miss
    have on (v : Fin n) (gv : g (fun w => decide (w ∈ y i ∨ w = v)) = true) :
        dotProduct (pt v) (l j) = 0 := by
      obtain ⟨w,hw,hj⟩ := safe j _ gv
      rcases of_decide_eq_true hw with hy | rfl
      · exact False.elim (miss w hy hj)
      · exact hj
    exact fourOrth (hp p) (hp q) (hl i) (hpp p q hpq) (hll i j hij) pa (on p gp) qa (on q gq)
  have coord (i : Fin k) : ∃ t, l i t ≠ 0 := by
    by_contra! hn
    exact hl i (funext hn)
  choose t ht using coord
  let Q (i : Fin k) : MvPolynomial (Fin 3) F := ∏ p ∈ y i, form (pt p)
  let P (i : Fin k) := Q i * (X (t i)) ^ (b - (y i).card)
  have evform (v z : Fin 3 → F) : eval z (form v) = dotProduct v z := by
    simp [form, dotProduct]
  apply separated P l
  · intro i
    have hform (v : Fin 3 → F) : (form v).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ (fun t _ => isHomogeneous_C_mul_X _ _)
    have hQ : (Q i).IsHomogeneous (y i).card := by
      simpa [Q] using IsHomogeneous.prod (y i) (fun p => form (pt p)) (fun _ => 1) (fun p _ => hform (pt p))
    simpa [P, Nat.add_sub_of_le (hy i)] using hQ.mul (isHomogeneous_X_pow (t i) (b - (y i).card))
  · intro i
    simp only [P, Q, map_mul, map_prod, map_pow, eval_X, evform]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (havoid i)) (pow_ne_zero _ (ht i))
  · intro i j hij
    obtain ⟨v,hv,hd⟩ := hit i j hij
    simp only [P, Q, map_mul, map_prod, evform]
    rw [Finset.prod_eq_zero hv hd, zero_mul]


private def arc {F : Type} [Field F] : Option F → Fin 3 → F
  | none => ![0,0,1]
  | some t => ![1,t,t^2]

private def secant {F : Type} [Field F] : Option F → Option F → Fin 3 → F
  | some a, some b => ![a*b, -(a+b), 1]
  | some a, none => ![-a,1,0]
  | none, some a => ![-a,1,0]
  | none, none => ![0,1,0]

private theorem arc_ne {F : Type} [Field F] (a : Option F) : arc a ≠ 0 := by
  cases a with
  | none => intro h; simpa [arc] using congrFun h 2
  | some a => intro h; simpa [arc] using congrFun h 0

private theorem secant_ne {F : Type} [Field F] (a b : Option F) : secant a b ≠ 0 := by
  cases a <;> cases b <;> intro h <;>
    first | simpa [secant] using congrFun h 1 | simpa [secant] using congrFun h 2

private theorem arc_eq {F : Type} [Field F] {a b : Option F} {c : F}
    (h : c • arc a = arc b) : a = b := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  cases a <;> cases b <;> simp_all [arc]

private theorem secant_inc {F : Type} [Field F] (z a b : Option F) (h : a ≠ b) :
    dotProduct (arc z) (secant a b) = 0 ↔ z = a ∨ z = b := by
  cases a with
  | none =>
    cases b with
    | none => exact (h rfl).elim
    | some b =>
      cases z <;> simp [arc,secant,neg_add_eq_zero,eq_comm]
  | some a =>
    cases b with
    | none => cases z <;> simp [arc,secant,neg_add_eq_zero,eq_comm]
    | some b =>
      cases z with
      | none => simp [arc,secant]
      | some z =>
        simp only [arc,secant,vec3_dotProduct,cons_val, one_mul, mul_one, Option.some.injEq]
        rw [show a*b + z* (-(a+b)) + z^2 = (z-a)*(z-b) by ring, mul_eq_zero, sub_eq_zero, sub_eq_zero]

private theorem lower : ∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2) := by
  classical
  intro F _ _ b bound
  let V := Option (Fin (b+1))
  let P := Projectivization F (Fin 3 → F)
  let _ : Fintype P := Fintype.ofFinite P
  let E := Fintype.equivFin P
  let pt (i : Fin (Fintype.card P)) : Fin 3 → F := (E.symm i).rep
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (b+1)) (β := F) (by simpa using bound)
  let f (v : V) := Option.map emb v
  have fi : Function.Injective f := by
    intro x y h
    cases x <;> cases y <;> simp_all [f, emb.injective.eq_iff]
  let ix (v : V) := E (Projectivization.mk F (arc (f v)) (arc_ne _))
  have ixinj : Function.Injective ix := by
    intro x y eq
    have h := E.injective eq
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp h
    exact fi (arc_eq hc).symm
  let D := (Finset.univ : Finset V).powersetCard 2
  let L := Fintype.equivFin ↥D
  let S (i : Fin (Fintype.card ↥D)) : Finset V := (L.symm i).val
  have size (i) : (S i).card = 2 := (Finset.mem_powersetCard.mp (L.symm i).property).2
  choose a d ad pair using fun i => Finset.card_eq_two.mp (size i)
  let line (i : Fin (Fintype.card ↥D)) := secant (f (a i)) (f (d i))
  have inc (i) (v : V) : dotProduct (pt (ix v)) (line i) = 0 ↔ v ∈ S i := by
    have he : pt (ix v) = (Projectivization.mk F (arc (f v)) (arc_ne _)).rep := by simp [pt,ix]
    obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep F (arc (f v)) (arc_ne _)
    rw [he, ← hc]
    change dotProduct ((c : F) • arc (f v)) (line i) = 0 ↔ _
    rw [smul_dotProduct, smul_eq_mul, mul_eq_zero]
    simp only [Units.ne_zero, false_or, line, secant_inc _ _ _ (fun h => ad i (fi h)),
      fi.eq_iff, pair, Finset.mem_insert, Finset.mem_singleton]
  let y (i : Fin (Fintype.card ↥D)) := (Finset.univ \ S i).image ix
  let g (x : Fin (Fintype.card P) → Bool) := decide (∀ u v : V, u ≠ v → x (ix u) = true ∨ x (ix v) = true)
  have fire (i) (u v : V) (ne : u ≠ v) (su : S i = {u,v}) :
      g (fun t => decide (t ∈ y i ∨ t = ix u)) = true := by
    apply decide_eq_true
    intro r s rs
    have single (w : V) (hw : w ≠ v) : ix w ∈ y i ∨ ix w = ix u := by
      by_cases eq : w = u
      · exact Or.inr (congrArg ix eq)
      · exact Or.inl (Finset.mem_image.mpr ⟨w, by simp [su, eq, hw], rfl⟩)
    by_cases hr : r = v
    · exact Or.inr (decide_eq_true (single s (fun hs => rs (hr.trans hs.symm))))
    · exact Or.inl (decide_eq_true (single r hr))
  have cardV : Fintype.card V = b + 2 := by simp [V]
  refine ⟨_,_,pt,line,y,g,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p
    exact (E.symm p).rep_ne_zero
  · intro p q hpq c h
    apply hpq
    apply E.symm.injective
    rw [← Projectivization.mk_rep (E.symm p), ← Projectivization.mk_rep (E.symm q)]
    exact ((Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨c,h.symm⟩).symm
  · intro v hv
    refine ⟨E (Projectivization.mk F v hv),?_⟩
    have eq : Projectivization.mk F v hv = Projectivization.mk F (pt (E (Projectivization.mk F v hv))) (E.symm _).rep_ne_zero := by simp [pt]
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp eq
    exact ⟨c,hc.symm⟩
  · intro i
    exact secant_ne _ _
  · intro i j hij c eq
    apply hij
    apply L.symm.injective
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le _ (by change (S j).card ≤ (S i).card; rw [size, size])
    intro v hv
    apply (inc j v).mp
    rw [eq, dotProduct_smul, (inc i v).mpr hv, smul_zero]
  · intro i
    have h := Finset.card_image_le (f := ix) (s := Finset.univ \ S i)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,cardV,size] at h
    exact h.trans (by omega)
  · intro i p hp hinc
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_sdiff.mp hv).2 ((inc i v).mp hinc)
  · intro x x' h hx
    apply decide_eq_true
    intro u v ne
    exact ((of_decide_eq_true hx) u v ne).imp (h _) (h _)
  · intro i x hx
    rcases (of_decide_eq_true hx) (a i) (d i) (ad i) with h | h
    · exact ⟨ix (a i), h, (inc i _).mpr (by simp [pair])⟩
    · exact ⟨ix (d i), h, (inc i _).mpr (by simp [pair])⟩
  · intro i
    refine ⟨ix (a i), ix (d i), fun h => ad i (ixinj h),
      (inc i _).mpr (by simp [pair]), (inc i _).mpr (by simp [pair]),
      fire i _ _ (ad i) (pair i), fire i _ _ (ad i).symm ?_⟩
    rw [pair, Finset.pair_comm]
  · rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, cardV]
    have h := Nat.add_one_mul_choose_eq (b+1) 1
    simp only [Nat.choose_one_right] at h
    nlinarith

end PEqualNP.Outside.L_meta_989

open PEqualNP.Outside.L_meta_989 in
theorem PEqualNP.Outside.L_meta_989 : (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) := by
  exact ⟨upper, lower⟩
