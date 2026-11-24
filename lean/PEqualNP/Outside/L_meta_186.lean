import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_186_aux

open PEqualNP.MetaComplexity

abbrev Vec := Fin 6 → ℕ

def occ : DMFormula 6 → Fin 6 → ℕ
  | .lit i _ => fun k => if k = i then 1 else 0
  | .and a b => fun k => occ a k + occ b k
  | .or a b => fun k => occ a k + occ b k

def zv (o : Vec) (i : Fin 6) : Vec := fun k => if k = i then 0 else o k

def dv (o : Vec) (j : Fin 6) : Vec := fun k => if k = j then o j - 1 else o k

def upd (x : Fin 6 → Bool) (i : Fin 6) (c : Bool) : Fin 6 → Bool :=
  fun k => if k = i then c else x k

def litv (s v : Bool) : Bool := if s then v else !v

def bop (g a b : Bool) : Bool := if g then (a || b) else (a && b)

def mk (g : Bool) (a b : DMFormula 6) : DMFormula 6 := if g then .or a b else .and a b

theorem eval_mk (g : Bool) (a b : DMFormula 6) (x : Fin 6 → Bool) :
    (mk g a b).eval x = bop g (a.eval x) (b.eval x) := by
  cases g <;> rfl

theorem occ_mk (g : Bool) (a b : DMFormula 6) (k : Fin 6) :
    occ (mk g a b) k = occ a k + occ b k := by
  cases g <;> rfl

theorem eval_lit (i : Fin 6) (s : Bool) (x : Fin 6 → Bool) :
    (DMFormula.lit i s).eval x = litv s (x i) := by
  cases s <;> rfl

theorem leaves_eq (φ : DMFormula 6) : φ.leaves = ∑ k, occ φ k := by
  induction φ with
  | lit i b => simp [DMFormula.leaves, occ]
  | and a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]
  | or a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]

theorem eval_congr (φ : DMFormula 6) (x y : Fin 6 → Bool)
    (h : ∀ k, 1 ≤ occ φ k → x k = y k) : φ.eval x = φ.eval y := by
  induction φ with
  | lit i b =>
    simp only [eval_lit]
    rw [h i (by simp [occ])]
  | and a b iha ihb =>
    simp only [DMFormula.eval]
    rw [iha (fun k hk => h k (by simp [occ]; omega)), ihb (fun k hk => h k (by simp [occ]; omega))]
  | or a b iha ihb =>
    simp only [DMFormula.eval]
    rw [iha (fun k hk => h k (by simp [occ]; omega)), ihb (fun k hk => h k (by simp [occ]; omega))]

theorem eval_upd_of_zero (φ : DMFormula 6) (i : Fin 6) (h : occ φ i = 0) (x : Fin 6 → Bool)
    (c : Bool) : φ.eval (upd x i c) = φ.eval x := by
  apply eval_congr
  intro k hk
  have : k ≠ i := by rintro rfl; omega
  simp [upd, this]

theorem exists_occ (φ : DMFormula 6) : ∃ j, 1 ≤ occ φ j := by
  induction φ with
  | lit i b => exact ⟨i, by simp [occ]⟩
  | and a b iha ihb => obtain ⟨j, hj⟩ := iha; exact ⟨j, by simp [occ]; omega⟩
  | or a b iha ihb => obtain ⟨j, hj⟩ := iha; exact ⟨j, by simp [occ]; omega⟩

def Ach (o : Vec) (h : (Fin 6 → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x, h x = c) ∨ ∃ φ : DMFormula 6, (∀ x, φ.eval x = h x) ∧ ∀ k, occ φ k ≤ o k

theorem Ach.mono {o o' : Vec} {h : (Fin 6 → Bool) → Bool} (hle : ∀ k, o k ≤ o' k)
    (a : Ach o h) : Ach o' h := by
  rcases a with hc | ⟨φ, he, ho⟩
  · exact .inl hc
  · exact .inr ⟨φ, he, fun k => (ho k).trans (hle k)⟩

theorem Ach.congr {o : Vec} {h h' : (Fin 6 → Bool) → Bool} (e : ∀ x, h x = h' x)
    (a : Ach o h) : Ach o h' := by
  rcases a with ⟨c, hc⟩ | ⟨φ, he, ho⟩
  · exact .inl ⟨c, fun x => by rw [← e, hc]⟩
  · exact .inr ⟨φ, fun x => by rw [he, e], ho⟩

theorem Ach.form (φ : DMFormula 6) : Ach (occ φ) φ.eval := .inr ⟨φ, fun _ => rfl, fun _ => le_rfl⟩

theorem Ach.const (o : Vec) (c : Bool) : Ach o (fun _ => c) := .inl ⟨c, fun _ => rfl⟩

theorem Ach.bop {o1 o2 : Vec} {h1 h2 : (Fin 6 → Bool) → Bool} (g : Bool) (a1 : Ach o1 h1)
    (a2 : Ach o2 h2) : Ach (fun k => o1 k + o2 k) (fun x => bop g (h1 x) (h2 x)) := by
  rcases a1 with ⟨c1, hc1⟩ | ⟨φ1, e1, b1⟩
  · by_cases hg : c1 = g
    · exact .inl ⟨g, fun x => by beta_reduce; rw [hc1, hg]; cases g <;> simp [PEqualNP.Outside.L_meta_186_aux.bop]⟩
    · refine (a2.mono (fun k => Nat.le_add_left _ _)).congr (fun x => ?_)
      rw [hc1]; cases g <;> cases c1 <;> simp_all [PEqualNP.Outside.L_meta_186_aux.bop]
  · rcases a2 with ⟨c2, hc2⟩ | ⟨φ2, e2, b2⟩
    · by_cases hg : c2 = g
      · exact .inl ⟨g, fun x => by beta_reduce; rw [hc2, hg]; cases g <;> simp [PEqualNP.Outside.L_meta_186_aux.bop]⟩
      · refine (Ach.mono (o := o1) (fun k => Nat.le_add_right _ _) (.inr ⟨φ1, e1, b1⟩)).congr
          (fun x => ?_)
        rw [hc2]; cases g <;> cases c2 <;> simp_all [PEqualNP.Outside.L_meta_186_aux.bop]
    · exact .inr ⟨mk g φ1 φ2, fun x => by rw [eval_mk, e1, e2],
        fun k => by rw [occ_mk]; exact Nat.add_le_add (b1 k) (b2 k)⟩

theorem restrict (φ : DMFormula 6) (i : Fin 6) (c : Bool) :
    Ach (zv (occ φ) i) (fun x => φ.eval (upd x i c)) := by
  induction φ with
  | lit j b =>
    by_cases hj : j = i
    · subst hj
      exact .inl ⟨litv b c, fun x => by simp [eval_lit, upd]⟩
    · refine .inr ⟨.lit j b, fun x => by simp [eval_lit, upd, hj], fun k => ?_⟩
      simp only [occ, zv]
      split_ifs <;> simp_all
  | and a b iha ihb =>
    refine ((iha.bop false ihb).mono (fun k => ?_)).congr (fun x => ?_)
    · simp only [zv, occ]; split_ifs <;> simp
    · rfl
  | or a b iha ihb =>
    refine ((iha.bop true ihb).mono (fun k => ?_)).congr (fun x => ?_)
    · simp only [zv, occ]; split_ifs <;> simp
    · rfl

theorem Ach.restrict {o : Vec} {h : (Fin 6 → Bool) → Bool} (a : Ach o h) (i : Fin 6) (c : Bool) :
    Ach (zv o i) (fun x => h (upd x i c)) := by
  rcases a with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · exact .inl ⟨c0, fun x => hc _⟩
  · refine ((L_meta_186_aux.restrict φ i c).mono (fun k => ?_)).congr (fun x => by rw [he])
    simp only [zv]; split_ifs <;> simp [ho k]

theorem Ach.upd_inv {o : Vec} {h : (Fin 6 → Bool) → Bool} (a : Ach o h) (i : Fin 6)
    (hi : o i = 0) (x : Fin 6 → Bool) (c : Bool) : h (upd x i c) = h x := by
  rcases a with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · rw [hc, hc]
  · rw [← he, ← he, eval_upd_of_zero φ i (by have := ho i; omega)]


def KM (i : Fin 6) (o : Vec) (h : (Fin 6 → Bool) → Bool) : Prop :=
  Ach (dv o i) h ∨ ∃ c j, j ≠ i ∧ 1 ≤ o j ∧ Ach (dv (zv o i) j) (fun x => h (upd x i c))

theorem KM.congr {i : Fin 6} {o o' : Vec} {h h' : (Fin 6 → Bool) → Bool} (eo : ∀ k, o k = o' k)
    (eh : ∀ x, h x = h' x) (a : KM i o h) : KM i o' h' := by
  obtain rfl : o = o' := funext eo
  obtain rfl : h = h' := funext eh
  exact a

theorem km_step (i : Fin 6) (g : Bool) (A B : DMFormula 6) (hA : 1 ≤ occ A i)
    (ihA : (∃ s, A = .lit i s) ∨ KM i (occ A) A.eval) :
    KM i (fun k => occ A k + occ B k) (fun x => bop g (A.eval x) (B.eval x)) := by
  rcases ihA with ⟨s, rfl⟩ | hk
  · by_cases hB : ∃ j, j ≠ i ∧ 1 ≤ occ B j
    · obtain ⟨j, hji, hj⟩ := hB
      refine .inr ⟨litv s g, j, hji, by simp only; omega, .inl ⟨g, fun x => ?_⟩⟩
      simp only [eval_lit, upd, ite_true]
      cases s <;> cases g <;> simp [litv, bop]
    · push Not at hB
      left
      have hBi : 1 ≤ occ B i := by
        obtain ⟨j, hj⟩ := exists_occ B
        by_cases hji : j = i
        · exact hji ▸ hj
        · have := hB j hji; omega
      have key : ∀ x, B.eval x = B.eval (fun _ => x i) := fun x =>
        eval_congr B _ _ (fun k hk => by
          by_cases hk' : k = i
          · subst hk'; rfl
          · have := hB k hk'; omega)
      have hH : ∀ x, bop g ((DMFormula.lit i s).eval x) (B.eval x)
          = bop g (litv s (x i)) (B.eval (fun _ => x i)) := by
        intro x; rw [eval_lit, key x]
      refine Ach.congr (fun x => (hH x).symm) ?_
      have hocc : ∀ (b : Bool) k, occ (DMFormula.lit i b) k ≤
          dv (fun k => occ (DMFormula.lit i s) k + occ B k) i k := by
        intro b k
        simp only [occ, dv]
        split_ifs <;> subst_vars <;> omega
      cases hf : bop g (litv s false) (B.eval (fun _ => false)) <;>
        cases ht : bop g (litv s true) (B.eval (fun _ => true))
      · refine .inl ⟨false, fun x => ?_⟩
        show bop g (litv s (x i)) (B.eval (fun _ => x i)) = false
        cases x i
        · exact hf
        · exact ht
      · refine .inr ⟨.lit i true, fun x => ?_, hocc true⟩
        show (DMFormula.lit i true).eval x = bop g (litv s (x i)) (B.eval (fun _ => x i))
        rw [eval_lit]
        cases x i
        · rw [hf]; rfl
        · rw [ht]; rfl
      · refine .inr ⟨.lit i false, fun x => ?_, hocc false⟩
        show (DMFormula.lit i false).eval x = bop g (litv s (x i)) (B.eval (fun _ => x i))
        rw [eval_lit]
        cases x i
        · rw [hf]; rfl
        · rw [ht]; rfl
      · refine .inl ⟨true, fun x => ?_⟩
        show bop g (litv s (x i)) (B.eval (fun _ => x i)) = true
        cases x i
        · exact hf
        · exact ht
  · rcases hk with hl | ⟨c, j, hji, hj, ha⟩
    · left
      refine (hl.bop g (Ach.form B)).mono (fun k => ?_)
      simp only [dv]
      split_ifs with hk
      · subst hk; omega
      · omega
    · right
      refine ⟨c, j, hji, by simp only; omega, ?_⟩
      refine (ha.bop g ((Ach.form B).restrict i c)).mono (fun k => ?_)
      simp only [dv, zv]
      split_ifs <;> subst_vars <;> omega

theorem kill_multi (i : Fin 6) (φ : DMFormula 6) :
    1 ≤ occ φ i → (∀ s, φ ≠ .lit i s) → KM i (occ φ) φ.eval := by
  induction φ with
  | lit j b =>
    intro h1 hne
    by_cases hj : j = i
    · subst hj; exact absurd rfl (hne b)
    · simp [occ, Ne.symm hj] at h1
  | and a b iha ihb =>
    intro h1 _
    have hsum : 1 ≤ occ a i + occ b i := h1
    by_cases ha : 1 ≤ occ a i
    · have ih : (∃ s, a = .lit i s) ∨ KM i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact km_step i false a b ha ih
    · have hb : 1 ≤ occ b i := by omega
      have ih : (∃ s, b = .lit i s) ∨ KM i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (km_step i false b a hb ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.and_comm])
  | or a b iha ihb =>
    intro h1 _
    have hsum : 1 ≤ occ a i + occ b i := h1
    by_cases ha : 1 ≤ occ a i
    · have ih : (∃ s, a = .lit i s) ∨ KM i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact km_step i true a b ha ih
    · have hb : 1 ≤ occ b i := by omega
      have ih : (∃ s, b = .lit i s) ∨ KM i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (km_step i true b a hb ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.or_comm])

def KS (i : Fin 6) (o : Vec) (h : (Fin 6 → Bool) → Bool) : Prop :=
  (∃ j, j ≠ i ∧ 1 ≤ o j ∧ ∃ g si sj : Bool, ∃ ψ : DMFormula 6, (∀ k, occ ψ k ≤ dv o j k) ∧
      ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i)) (litv sj (x j))))) ∨
  (∃ c j k, j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ 1 ≤ o j ∧ 1 ≤ o k ∧ (j ≠ k ∨ 2 ≤ o j) ∧
      Ach (dv (dv (zv o i) j) k) (fun x => h (upd x i c)))

theorem KS.congr {i : Fin 6} {o o' : Vec} {h h' : (Fin 6 → Bool) → Bool} (eo : ∀ k, o k = o' k)
    (eh : ∀ x, h x = h' x) (a : KS i o h) : KS i o' h' := by
  obtain rfl : o = o' := funext eo
  obtain rfl : h = h' := funext eh
  exact a

theorem two_leaves (i : Fin 6) (C D : DMFormula 6) (hC : occ C i = 0) (hD : occ D i = 0) :
    ∃ j k, j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ 1 ≤ occ C j + occ D j ∧ 1 ≤ occ C k + occ D k ∧
      (j ≠ k ∨ 2 ≤ occ C j + occ D j) := by
  obtain ⟨j, hj⟩ := exists_occ C
  obtain ⟨k, hk⟩ := exists_occ D
  have hji : j ≠ i := by rintro rfl; omega
  have hki : k ≠ i := by rintro rfl; omega
  rcases le_total j k with hjk | hjk
  · refine ⟨j, k, hji, hki, hjk, by omega, by omega, ?_⟩
    by_cases e : j = k
    · subst e; right; omega
    · left; exact e
  · refine ⟨k, j, hki, hji, hjk, by omega, by omega, ?_⟩
    by_cases e : k = j
    · subst e; right; omega
    · left; exact e

theorem ks_step (i : Fin 6) (g : Bool) (A B : DMFormula 6) (hA : occ A i = 1) (hB0 : occ B i = 0)
    (ihA : (∃ s, A = .lit i s) ∨ KS i (occ A) A.eval) :
    KS i (fun k => occ A k + occ B k) (fun x => bop g (A.eval x) (B.eval x)) := by
  rcases ihA with ⟨si, rfl⟩ | hk
  · have kill2 : ∀ C D : DMFormula 6, occ C i = 0 → occ D i = 0 →
        (∀ k, occ B k = occ C k + occ D k) →
        KS i (fun k => occ (DMFormula.lit i si) k + occ B k)
          (fun x => bop g ((DMFormula.lit i si).eval x) (B.eval x)) := by
      intro C D hC hD hBCD
      obtain ⟨j, k, hji, hki, hjk, hj, hk, hjk2⟩ := two_leaves i C D hC hD
      refine .inr ⟨litv si g, j, k, hji, hki, hjk, ?_, ?_, ?_, .inl ⟨g, fun x => ?_⟩⟩
      · simp only [hBCD]; omega
      · simp only [hBCD]; omega
      · rcases hjk2 with e | e
        · exact .inl e
        · right; simp only [hBCD]; omega
      · simp only [eval_lit, upd, ite_true]
        cases si <;> cases g <;> simp [litv, bop]
    cases B with
    | lit j sj =>
      have hji : j ≠ i := by
        rintro rfl; simp [occ] at hB0
      refine .inl ⟨j, hji, by simp [occ], g, si, sj, .lit i true, fun k => ?_, fun x => ?_⟩
      · simp only [occ, dv]
        split_ifs <;> simp_all
      · simp [eval_lit, upd, litv]
    | and C D =>
      have hB0' : occ C i + occ D i = 0 := hB0
      exact kill2 C D (by omega) (by omega) (fun k => rfl)
    | or C D =>
      have hB0' : occ C i + occ D i = 0 := hB0
      exact kill2 C D (by omega) (by omega) (fun k => rfl)
  · rcases hk with ⟨j, hji, hj, g', si, sj, ψ, hψo, hψe⟩ |
      ⟨c, j, k, hji, hki, hjk, hj, hk1, hjk2, ha⟩
    · refine .inl ⟨j, hji, by simp only; omega, g', si, sj, mk g ψ B, fun k => ?_, fun x => ?_⟩
      · rw [occ_mk]
        have := hψo k
        simp only [dv] at this ⊢
        split_ifs at this ⊢ with e
        · subst e; omega
        · omega
      · rw [eval_mk, ← hψe x, eval_upd_of_zero B i hB0]
    · refine .inr ⟨c, j, k, hji, hki, hjk, by simp only; omega, by simp only; omega, ?_, ?_⟩
      · rcases hjk2 with e | e
        · exact .inl e
        · right; simp only; omega
      · refine (ha.bop g ((Ach.form B).restrict i c)).mono (fun m => ?_)
        simp only [dv, zv]
        split_ifs <;> subst_vars <;> omega

theorem kill_single (i : Fin 6) (φ : DMFormula 6) :
    occ φ i = 1 → (∀ s, φ ≠ .lit i s) → KS i (occ φ) φ.eval := by
  induction φ with
  | lit j b =>
    intro h1 hne
    by_cases hj : j = i
    · subst hj; exact absurd rfl (hne b)
    · simp [occ, Ne.symm hj] at h1
  | and a b iha ihb =>
    intro h1 _
    have hsum : occ a i + occ b i = 1 := h1
    by_cases ha : occ a i = 1
    · have ih : (∃ s, a = .lit i s) ∨ KS i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact ks_step i false a b ha (by omega) ih
    · have hb : occ b i = 1 := by omega
      have ih : (∃ s, b = .lit i s) ∨ KS i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (ks_step i false b a hb (by omega) ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.and_comm])
  | or a b iha ihb =>
    intro h1 _
    have hsum : occ a i + occ b i = 1 := h1
    by_cases ha : occ a i = 1
    · have ih : (∃ s, a = .lit i s) ∨ KS i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact ks_step i true a b ha (by omega) ih
    · have hb : occ b i = 1 := by omega
      have ih : (∃ s, b = .lit i s) ∨ KS i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (ks_step i true b a hb (by omega) ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.or_comm])

theorem zv_le {o o' : Vec} (i : Fin 6) (h : ∀ m, o m ≤ o' m) (m : Fin 6) :
    zv o i m ≤ zv o' i m := by
  simp only [zv]
  split_ifs
  · exact le_rfl
  · exact h m

theorem dv_le {o o' : Vec} (j : Fin 6) (h : ∀ m, o m ≤ o' m) (m : Fin 6) :
    dv o j m ≤ dv o' j m := by
  simp only [dv]
  split_ifs
  · exact Nat.sub_le_sub_right (h j) 1
  · exact h m

theorem dv_add {o p : Vec} (j : Fin 6) (h : 1 ≤ o j) (m : Fin 6) :
    dv o j m + p m ≤ dv (fun n => o n + p n) j m := by
  simp only [dv]
  split_ifs with e
  · subst e; omega
  · exact le_rfl

theorem zv_add (o p : Vec) (i m : Fin 6) :
    zv o i m + zv p i m ≤ zv (fun n => o n + p n) i m := by
  simp only [zv]
  split_ifs <;> simp

theorem dv_same (o : Vec) (j : Fin 6) : dv o j j = o j - 1 := by simp [dv]

theorem dv_ne (o : Vec) {j m : Fin 6} (h : m ≠ j) : dv o j m = o m := by simp [dv, h]

theorem dv_comm (o : Vec) (a b : Fin 6) : dv (dv o a) b = dv (dv o b) a := by
  funext m
  by_cases e : a = b
  · subst e; rfl
  · by_cases h1 : m = a
    · subst h1
      rw [dv_ne _ e, dv_same, dv_same, dv_ne _ e]
    · by_cases h2 : m = b
      · subst h2
        rw [dv_same, dv_ne _ h1, dv_ne _ h1, dv_same]
      · rw [dv_ne _ h2, dv_ne _ h1, dv_ne _ h1, dv_ne _ h2]

theorem fit2_swap {o : Vec} {b c : Fin 6} (h1 : 1 ≤ o b) (h2 : 1 ≤ dv o b c) :
    1 ≤ o c ∧ 1 ≤ dv o c b := by
  by_cases e : c = b
  · subst e
    exact ⟨h1, h2⟩
  · rw [dv_ne _ e] at h2
    rw [dv_ne _ (Ne.symm e)]
    exact ⟨h2, h1⟩

abbrev Fit3 (o : Vec) (j k l : Fin 6) : Prop := 1 ≤ o j ∧ 1 ≤ dv o j k ∧ 1 ≤ dv (dv o j) k l

theorem Fit3.swap23 {o : Vec} {a b c : Fin 6} (h : Fit3 o a b c) : Fit3 o a c b := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h4, h5⟩ := fit2_swap h2 h3
  exact ⟨h1, h4, h5⟩

theorem Fit3.swap12 {o : Vec} {a b c : Fin 6} (h : Fit3 o a b c) : Fit3 o b a c := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h4, h5⟩ := fit2_swap h1 h2
  refine ⟨h4, h5, ?_⟩
  rw [dv_comm]
  exact h3

theorem sort3 {o : Vec} {i a b c : Fin 6} (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i)
    (h : Fit3 o a b c) :
    ∃ j k l, j ≠ i ∧ k ≠ i ∧ l ≠ i ∧ j ≤ k ∧ k ≤ l ∧ Fit3 o j k l := by
  rcases le_total a b with hab | hab
  · rcases le_total b c with hbc | hbc
    · exact ⟨a, b, c, ha, hb, hc, hab, hbc, h⟩
    · rcases le_total a c with hac | hac
      · exact ⟨a, c, b, ha, hc, hb, hac, hbc, h.swap23⟩
      · exact ⟨c, a, b, hc, ha, hb, hac, hab, h.swap23.swap12⟩
  · rcases le_total a c with hac | hac
    · exact ⟨b, a, c, hb, ha, hc, hab, hac, h.swap12⟩
    · rcases le_total b c with hbc | hbc
      · exact ⟨b, c, a, hb, hc, ha, hbc, hac, h.swap12.swap23⟩
      · exact ⟨c, b, a, hc, hb, ha, hbc, hab, h.swap12.swap23.swap12⟩

theorem fit_of_three {o p q r : Vec} {a b c : Fin 6} (ho : ∀ m, p m + q m + r m ≤ o m)
    (ha : 1 ≤ p a) (hb : 1 ≤ q b) (hc : 1 ≤ r c) : Fit3 o a b c := by
  have ha' := ho a
  have hb' := ho b
  have hc' := ho c
  refine ⟨by omega, ?_, ?_⟩
  · simp only [dv]
    split_ifs <;> subst_vars <;> omega
  · simp only [dv]
    split_ifs <;> subst_vars <;> omega

theorem one_le_dv {o : Vec} {j k : Fin 6} (hk : 1 ≤ o k) (hjk : j ≠ k ∨ 2 ≤ o j) :
    1 ≤ dv o j k := by
  by_cases e : k = j
  · subst e
    rw [dv_same]
    rcases hjk with e' | e'
    · exact absurd rfl e'
    · omega
  · rw [dv_ne _ e]
    exact hk

theorem dv2_add {o p : Vec} {j k : Fin 6} (f1 : 1 ≤ o j) (f2 : 1 ≤ dv o j k) (m : Fin 6) :
    dv (dv o j) k m + p m ≤ dv (dv (fun n => o n + p n) j) k m := by
  have s1 : ∀ n, dv o j n + p n ≤ dv (fun n => o n + p n) j n := fun n => dv_add j f1 n
  exact le_trans (dv_add k f2 m) (dv_le k s1 m)

theorem dv3_add {o p : Vec} {i j k l : Fin 6} (f1 : 1 ≤ zv o i j) (f2 : 1 ≤ dv (zv o i) j k)
    (f3 : 1 ≤ dv (dv (zv o i) j) k l) (m : Fin 6) :
    dv (dv (dv (zv o i) j) k) l m + zv p i m ≤
      dv (dv (dv (zv (fun n => o n + p n) i) j) k) l m := by
  have s1 : ∀ n, zv o i n + zv p i n ≤ zv (fun n => o n + p n) i n := fun n => zv_add o p i n
  have s2 : ∀ n, dv (dv (zv o i) j) k n + zv p i n ≤
      dv (dv (zv (fun n => o n + p n) i) j) k n :=
    fun n => le_trans (dv2_add f1 f2 n) (dv_le k (dv_le j s1) n)
  exact le_trans (dv_add l f3 m) (dv_le l s2 m)

def KS4 (i : Fin 6) (o : Vec) (h : (Fin 6 → Bool) → Bool) : Prop :=
  (∃ j, j ≠ i ∧ 1 ≤ o j ∧ ∃ g si sj : Bool, ∃ ψ : DMFormula 6, (∀ k, occ ψ k ≤ dv o j k) ∧
      ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i)) (litv sj (x j))))) ∨
  (∃ j k, j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ 1 ≤ o j ∧ 1 ≤ o k ∧ (j ≠ k ∨ 2 ≤ o j) ∧
      ∃ g si g2 sj sk : Bool, ∃ ψ : DMFormula 6, (∀ m, occ ψ m ≤ dv (dv o j) k m) ∧
        ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i))
          (bop g2 (litv sj (x j)) (litv sk (x k)))))) ∨
  (∃ c j k l, j ≠ i ∧ k ≠ i ∧ l ≠ i ∧ j ≤ k ∧ k ≤ l ∧ Fit3 (zv o i) j k l ∧
      Ach (dv (dv (dv (zv o i) j) k) l) (fun x => h (upd x i c)))

theorem KS4.congr {i : Fin 6} {o o' : Vec} {h h' : (Fin 6 → Bool) → Bool} (eo : ∀ k, o k = o' k)
    (eh : ∀ x, h x = h' x) (a : KS4 i o h) : KS4 i o' h' := by
  obtain rfl : o = o' := funext eo
  obtain rfl : h = h' := funext eh
  exact a

theorem form_cases (B : DMFormula 6) :
    (∃ j s, B = .lit j s) ∨ ∃ g2 C D, B = mk g2 C D := by
  cases B with
  | lit j s => exact .inl ⟨j, s, rfl⟩
  | and C D => exact .inr ⟨false, C, D, rfl⟩
  | or C D => exact .inr ⟨true, C, D, rfl⟩

theorem occ_lit_self (j : Fin 6) (s : Bool) : occ (DMFormula.lit j s) j = 1 := by simp [occ]

theorem occ_lit_ne (j : Fin 6) (s : Bool) {m : Fin 6} (h : m ≠ j) :
    occ (DMFormula.lit j s) m = 0 := by simp [occ, h]

theorem bop_comm (g a b : Bool) : bop g a b = bop g b a := by
  cases g <;> cases a <;> cases b <;> rfl

theorem ks4_abs2 (i : Fin 6) (g si g2 : Bool) (j k : Fin 6) (sj sk : Bool) (hji : j ≠ i)
    (hki : k ≠ i) (hjk : j ≤ k) :
    KS4 i (fun m => occ (DMFormula.lit i si) m +
        (occ (DMFormula.lit j sj) m + occ (DMFormula.lit k sk) m))
      (fun x => bop g (litv si (x i)) (bop g2 (litv sj (x j)) (litv sk (x k)))) := by
  have hj1 := occ_lit_self j sj
  have hk1 := occ_lit_self k sk
  refine .inr (.inl ⟨j, k, hji, hki, hjk, by simp only; omega, by simp only; omega, ?_,
    g, si, g2, sj, sk, .lit i true, fun m => ?_, fun x => ?_⟩)
  · by_cases e : j = k
    · right
      have hk2 : occ (DMFormula.lit k sk) j = 1 := by rw [e]; exact hk1
      simp only; omega
    · left; exact e
  · by_cases hm : m = i
    · rw [hm, dv_ne _ (Ne.symm hki), dv_ne _ (Ne.symm hji)]
      have h1 := occ_lit_self i true
      have h2 := occ_lit_self i si
      omega
    · rw [occ_lit_ne i true hm]
      exact Nat.zero_le _
  · simp [eval_lit, upd, litv]

theorem ks4_kill3 (i : Fin 6) (g si : Bool) (o : Vec) (hB : (Fin 6 → Bool) → Bool)
    (X Y Z : DMFormula 6) (hX : occ X i = 0) (hY : occ Y i = 0) (hZ : occ Z i = 0)
    (ho : ∀ m, occ X m + occ Y m + occ Z m ≤ o m) :
    KS4 i o (fun x => bop g ((DMFormula.lit i si).eval x) (hB x)) := by
  obtain ⟨a, ha⟩ := exists_occ X
  obtain ⟨b, hb⟩ := exists_occ Y
  obtain ⟨c, hc⟩ := exists_occ Z
  have hai : a ≠ i := by rintro rfl; omega
  have hbi : b ≠ i := by rintro rfl; omega
  have hci : c ≠ i := by rintro rfl; omega
  have hz : ∀ m, occ X m + occ Y m + occ Z m ≤ zv o i m := by
    intro m
    simp only [zv]
    split_ifs with e
    · subst e; omega
    · exact ho m
  obtain ⟨j, k, l, hji, hki, hli, hjk, hkl, hf⟩ := sort3 hai hbi hci (fit_of_three hz ha hb hc)
  refine .inr (.inr ⟨litv si g, j, k, l, hji, hki, hli, hjk, hkl, hf, .inl ⟨g, fun x => ?_⟩⟩)
  show bop g ((DMFormula.lit i si).eval (upd x i (litv si g))) (hB (upd x i (litv si g))) = g
  rw [eval_lit]
  have e : upd x i (litv si g) i = litv si g := by simp [upd]
  rw [e]
  cases si <;> cases g <;> simp [litv, bop]

theorem ks_step4 (i : Fin 6) (g : Bool) (A B : DMFormula 6) (hA : occ A i = 1) (hB0 : occ B i = 0)
    (ihA : (∃ s, A = .lit i s) ∨ KS4 i (occ A) A.eval) :
    KS4 i (fun k => occ A k + occ B k) (fun x => bop g (A.eval x) (B.eval x)) := by
  rcases ihA with ⟨si, rfl⟩ | hk
  · rcases form_cases B with ⟨j, sj, rfl⟩ | ⟨g2, C, D, rfl⟩
    · have hji : j ≠ i := by
        rintro rfl; simp [occ] at hB0
      refine .inl ⟨j, hji, by simp [occ], g, si, sj, .lit i true, fun k => ?_, fun x => ?_⟩
      · simp only [occ, dv]
        split_ifs <;> simp_all
      · simp [eval_lit, upd, litv]
    · have hB0' := hB0
      rw [occ_mk] at hB0'
      have hC : occ C i = 0 := by omega
      have hD : occ D i = 0 := by omega
      rcases form_cases C with ⟨j, sj, rfl⟩ | ⟨g3, C1, C2, rfl⟩
      · rcases form_cases D with ⟨k, sk, rfl⟩ | ⟨g4, D1, D2, rfl⟩
        · have hji : j ≠ i := by
            rintro rfl; simp [occ] at hC
          have hki : k ≠ i := by
            rintro rfl; simp [occ] at hD
          rcases le_total j k with hjk | hjk
          · exact (ks4_abs2 i g si g2 j k sj sk hji hki hjk).congr
              (fun m => by simp only [occ_mk])
              (fun x => by simp only [eval_lit, eval_mk])
          · exact (ks4_abs2 i g si g2 k j sk sj hki hji hjk).congr
              (fun m => by simp only [occ_mk]; omega)
              (fun x => by simp only [eval_lit, eval_mk]; rw [bop_comm g2])
        · rw [occ_mk] at hD
          exact ks4_kill3 i g si _ _ (.lit j sj) D1 D2 hC (by omega) (by omega)
            (fun m => by simp only [occ_mk]; omega)
      · rw [occ_mk] at hC
        exact ks4_kill3 i g si _ _ C1 C2 D (by omega) (by omega) hD
          (fun m => by simp only [occ_mk]; omega)
  · have hle : ∀ m, occ A m ≤ (fun k => occ A k + occ B k) m := fun m => Nat.le_add_right _ _
    rcases hk with ⟨j, hji, hj, g', si, sj, ψ, hψo, hψe⟩ |
      ⟨j, k, hji, hki, hjk, hj, hk1, hjk2, g', si, g2, sj, sk, ψ, hψo, hψe⟩ |
      ⟨c, j, k, l, hji, hki, hli, hjk, hkl, ⟨f1, f2, f3⟩, ha⟩
    · refine .inl ⟨j, hji, by simp only; omega, g', si, sj, mk g ψ B, fun k => ?_, fun x => ?_⟩
      · rw [occ_mk]
        have := hψo k
        simp only [dv] at this ⊢
        split_ifs at this ⊢ with e
        · subst e; omega
        · omega
      · rw [eval_mk, ← hψe x, eval_upd_of_zero B i hB0]
    · refine .inr (.inl ⟨j, k, hji, hki, hjk, by simp only; omega, by simp only; omega, ?_,
        g', si, g2, sj, sk, mk g ψ B, fun m => ?_, fun x => ?_⟩)
      · rcases hjk2 with e | e
        · exact .inl e
        · right; simp only; omega
      · rw [occ_mk]
        exact le_trans (Nat.add_le_add_right (hψo m) _) (dv2_add hj (one_le_dv hk1 hjk2) m)
      · rw [eval_mk, ← hψe x, eval_upd_of_zero B i hB0]
    · refine .inr (.inr ⟨c, j, k, l, hji, hki, hli, hjk, hkl, ⟨?_, ?_, ?_⟩, ?_⟩)
      · exact le_trans f1 (zv_le i hle j)
      · exact le_trans f2 (dv_le j (zv_le i hle) k)
      · exact le_trans f3 (dv_le k (dv_le j (zv_le i hle)) l)
      · refine (ha.bop g ((Ach.form B).restrict i c)).mono (fun m => ?_)
        exact dv3_add f1 f2 f3 m

theorem kill_single4 (i : Fin 6) (φ : DMFormula 6) :
    occ φ i = 1 → (∀ s, φ ≠ .lit i s) → KS4 i (occ φ) φ.eval := by
  induction φ with
  | lit j b =>
    intro h1 hne
    by_cases hj : j = i
    · subst hj; exact absurd rfl (hne b)
    · simp [occ, Ne.symm hj] at h1
  | and a b iha ihb =>
    intro h1 _
    have hsum : occ a i + occ b i = 1 := h1
    by_cases ha : occ a i = 1
    · have ih : (∃ s, a = .lit i s) ∨ KS4 i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact ks_step4 i false a b ha (by omega) ih
    · have hb : occ b i = 1 := by omega
      have ih : (∃ s, b = .lit i s) ∨ KS4 i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (ks_step4 i false b a hb (by omega) ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.and_comm])
  | or a b iha ihb =>
    intro h1 _
    have hsum : occ a i + occ b i = 1 := h1
    by_cases ha : occ a i = 1
    · have ih : (∃ s, a = .lit i s) ∨ KS4 i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact ks_step4 i true a b ha (by omega) ih
    · have hb : occ b i = 1 := by omega
      have ih : (∃ s, b = .lit i s) ∨ KS4 i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (ks_step4 i true b a hb (by omega) ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.or_comm])

def code (x : Fin 6 → Bool) : ℕ :=
  Nat.bit (x 0) (Nat.bit (x 1) (Nat.bit (x 2) (Nat.bit (x 3) (Nat.bit (x 4) (Nat.bit (x 5) 0)))))

def ev (T : ℕ) (x : Fin 6 → Bool) : Bool := T.testBit (code x)

def M : ℕ := 0xffffffffffffffff

def vt : Fin 6 → ℕ := ![0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem allx {P : (Fin 6 → Bool) → Prop}
    (h : ∀ b0 b1 b2 b3 b4 b5 : Bool, P ![b0, b1, b2, b3, b4, b5]) (x : Fin 6 → Bool) : P x := by
  have e : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext k; fin_cases k <;> rfl
  rw [e]; exact h _ _ _ _ _ _

theorem code_lt : ∀ x, code x < 64 := allx (by decide +kernel)

def setIdx (a : ℕ) (i : Fin 6) (c : Bool) : ℕ :=
  if c then (if a.testBit i then a else 2 ^ (i : ℕ) + a)
  else (if a.testBit i then a - 2 ^ (i : ℕ) else a)

theorem code_upd (i : Fin 6) (c : Bool) : ∀ x, code (upd x i c) = setIdx (code x) i c := by
  fin_cases i <;> cases c <;> exact allx (by decide +kernel)

def rst (g : ℕ) (i : Fin 6) (c : Bool) : ℕ :=
  if c then (g &&& vt i) ||| ((g &&& vt i) >>> 2 ^ (i : ℕ))
  else (g &&& (M ^^^ vt i)) ||| ((g &&& (M ^^^ vt i)) <<< 2 ^ (i : ℕ))

theorem facts_t : ∀ i : Fin 6, ∀ a < 64,
    ((vt i).testBit a = true → setIdx a i true = a ∧ (vt i).testBit (2 ^ (i : ℕ) + a) = false) ∧
    ((vt i).testBit a = false →
      setIdx a i true = 2 ^ (i : ℕ) + a ∧ (vt i).testBit (2 ^ (i : ℕ) + a) = true) := by
  decide +kernel

theorem facts_f : ∀ i : Fin 6, ∀ a < 64,
    ((vt i).testBit a = true → setIdx a i false = a - 2 ^ (i : ℕ) ∧ 2 ^ (i : ℕ) ≤ a ∧
      (M ^^^ vt i).testBit a = false ∧ (M ^^^ vt i).testBit (a - 2 ^ (i : ℕ)) = true) ∧
    ((vt i).testBit a = false → setIdx a i false = a ∧ (M ^^^ vt i).testBit a = true ∧
      (decide (a ≥ 2 ^ (i : ℕ)) && (M ^^^ vt i).testBit (a - 2 ^ (i : ℕ))) = false) := by
  decide +kernel

theorem rst_bit (g : ℕ) (i : Fin 6) (c : Bool) (a : ℕ) (ha : a < 64) :
    (rst g i c).testBit a = g.testBit (setIdx a i c) := by
  cases c
  · have F := facts_f i a ha
    simp only [rst, Bool.false_eq_true, if_false, Nat.testBit_or, Nat.testBit_and,
      Nat.testBit_shiftLeft]
    cases hL : (vt i).testBit a
    · obtain ⟨h1, h2, h3⟩ := F.2 hL
      rw [h1, h2]
      cases hd : decide (a ≥ 2 ^ (i : ℕ)) <;> cases hm : (M ^^^ vt i).testBit (a - 2 ^ (i : ℕ)) <;>
        simp_all
    · obtain ⟨h1, h2, h3, h4⟩ := F.1 hL
      rw [h1, h3, h4]
      simp [h2]
  · have F := facts_t i a ha
    simp only [rst, if_true, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight]
    cases hL : (vt i).testBit a
    · obtain ⟨h1, h2⟩ := F.2 hL
      rw [h1, h2]; simp
    · obtain ⟨h1, h2⟩ := F.1 hL
      rw [h1, h2]; simp

theorem ev_rst (g : ℕ) (i : Fin 6) (c : Bool) (x : Fin 6 → Bool) :
    ev (rst g i c) x = ev g (upd x i c) := by
  unfold ev
  rw [rst_bit _ _ _ _ (code_lt x), code_upd]

theorem ev_and (A B : ℕ) (x : Fin 6 → Bool) : ev (A &&& B) x = (ev A x && ev B x) :=
  Nat.testBit_and _ _ _

theorem ev_or (A B : ℕ) (x : Fin 6 → Bool) : ev (A ||| B) x = (ev A x || ev B x) :=
  Nat.testBit_or _ _ _

theorem ev_xor (A B : ℕ) (x : Fin 6 → Bool) : ev (A ^^^ B) x = (ev A x ^^ ev B x) :=
  Nat.testBit_xor _ _ _

theorem ev_zero (x : Fin 6 → Bool) : ev 0 x = false := Nat.zero_testBit _

theorem ev_M : ∀ x, ev M x = true := allx (by decide +kernel)

theorem ev_vt (i : Fin 6) : ∀ x, ev (vt i) x = x i := by
  fin_cases i <;> exact allx (by decide +kernel)

def cT (b : Bool) : ℕ := if b then M else 0

def litT (j : Fin 6) (s : Bool) : ℕ := if s then vt j else M ^^^ vt j

def opT (g : Bool) (a b : ℕ) : ℕ := if g then a ||| b else a &&& b

theorem ev_cT (b : Bool) (x : Fin 6 → Bool) : ev (cT b) x = b := by
  cases b
  · exact ev_zero x
  · exact ev_M x

theorem ev_litT (j : Fin 6) (s : Bool) (x : Fin 6 → Bool) : ev (litT j s) x = litv s (x j) := by
  cases s <;> simp [litT, litv, ev_xor, ev_M, ev_vt]

theorem ev_opT (g : Bool) (A B : ℕ) (x : Fin 6 → Bool) :
    ev (opT g A B) x = bop g (ev A x) (ev B x) := by
  cases g <;> simp [opT, bop, ev_and, ev_or]

def cnd (i j : Fin 6) (g si sj b : Bool) : ℕ := M ^^^ (opT g (cT (litv si b)) (litT j sj) ^^^ vt i)

theorem ev_cnd (i j : Fin 6) (g si sj b : Bool) (z : Fin 6 → Bool) :
    ev (cnd i j g si sj b) z = !(bop g (litv si b) (litv sj (z j)) ^^ z i) := by
  simp only [cnd, ev_xor, ev_M, ev_opT, ev_cT, ev_litT, ev_vt, Bool.true_xor]

def absLo (lo : ℕ) (i j : Fin 6) (g si sj : Bool) : ℕ :=
  (cnd i j g si sj false &&& rst lo i false) ||| (cnd i j g si sj true &&& rst lo i true)

def absHi (hi : ℕ) (i j : Fin 6) (g si sj : Bool) : ℕ :=
  M ^^^ ((cnd i j g si sj false &&& (M ^^^ rst hi i false)) |||
    (cnd i j g si sj true &&& (M ^^^ rst hi i true)))

def InIv (lo hi : ℕ) (h : (Fin 6 → Bool) → Bool) : Prop :=
  ∀ x, (ev lo x = true → h x = true) ∧ (h x = true → ev hi x = true)

def Bad (lo hi : ℕ) (o : Vec) : Prop := ∀ h, InIv lo hi h → ¬ Ach o h

theorem code_dec : ∀ a < 64, code (fun k : Fin 6 => a.testBit k) = a := by decide +kernel

theorem exists_x (T : ℕ) (hT : T &&& M ≠ 0) : ∃ x, ev T x = true := by
  obtain ⟨a, ha⟩ := Nat.exists_testBit_of_ne_zero hT
  rw [Nat.testBit_and, Bool.and_eq_true] at ha
  have ha64 : a < 64 := by
    by_contra hc
    push Not at hc
    have hM : M < 2 ^ a :=
      lt_of_lt_of_le (by decide : M < 2 ^ 64) (Nat.pow_le_pow_right (by norm_num) hc)
    rw [Nat.testBit_lt_two_pow hM] at ha
    exact absurd ha.2 (by simp)
  exact ⟨fun k => a.testBit k, by unfold ev; rw [code_dec a ha64]; exact ha.1⟩

theorem InIv.rst' {lo hi : ℕ} {h : (Fin 6 → Bool) → Bool} (hI : InIv lo hi h) (i : Fin 6)
    (c : Bool) : InIv (rst lo i c) (rst hi i c) (fun x => h (upd x i c)) := fun x => by
  rw [ev_rst, ev_rst]; exact hI _

theorem InIv.abs {lo hi : ℕ} {h : (Fin 6 → Bool) → Bool} (hI : InIv lo hi h) {i j : Fin 6}
    (hji : j ≠ i) {g si sj : Bool} {ψ : DMFormula 6}
    (hψ : ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i)) (litv sj (x j))))) :
    InIv (absLo lo i j g si sj) (absHi hi i j g si sj) ψ.eval := by
  have key : ∀ z b, bop g (litv si b) (litv sj (z j)) = z i → h (upd z i b) = ψ.eval z := by
    intro z b hb
    rw [hψ]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp [upd, hji, hb]
    · simp [upd, hk]
  intro z
  have hf : ∀ b, bop g (litv si b) (litv sj (z j)) = z i → ψ.eval z = true →
      ev hi (upd z i b) = true := fun b hb hz => (hI _).2 (by rw [key z b hb]; exact hz)
  have hl : ∀ b, bop g (litv si b) (litv sj (z j)) = z i → ev lo (upd z i b) = true →
      ψ.eval z = true := fun b hb hz => by rw [← key z b hb]; exact (hI _).1 hz
  clear key hψ
  have f0 := hf false
  have f1 := hf true
  have g0 := hl false
  have g1 := hl true
  clear hf hl
  simp only [absLo, absHi, ev_or, ev_and, ev_xor, ev_M, ev_cnd, ev_rst]
  generalize ψ.eval z = v at f0 f1 g0 g1 ⊢
  generalize ev lo (upd z i false) = l0 at f0 f1 g0 g1 ⊢
  generalize ev lo (upd z i true) = l1 at f0 f1 g0 g1 ⊢
  generalize ev hi (upd z i false) = u0 at f0 f1 g0 g1 ⊢
  generalize ev hi (upd z i true) = u1 at f0 f1 g0 g1 ⊢
  generalize bop g (litv si false) (litv sj (z j)) = p0 at f0 f1 g0 g1 ⊢
  generalize bop g (litv si true) (litv sj (z j)) = p1 at f0 f1 g0 g1 ⊢
  generalize z i = w at f0 f1 g0 g1 ⊢
  revert f0 f1 g0 g1
  cases v <;> cases l0 <;> cases l1 <;> cases u0 <;> cases u1 <;> cases p0 <;> cases p1 <;>
    cases w <;> simp

def cndT (i : Fin 6) (t : ℕ) (g si b : Bool) : ℕ := M ^^^ (opT g (cT (litv si b)) t ^^^ vt i)

theorem ev_cndT (i : Fin 6) (t : ℕ) (g si b : Bool) (z : Fin 6 → Bool) :
    ev (cndT i t g si b) z = !(bop g (litv si b) (ev t z) ^^ z i) := by
  simp only [cndT, ev_xor, ev_M, ev_opT, ev_cT, ev_vt, Bool.true_xor]

def absLoT (lo : ℕ) (i : Fin 6) (t : ℕ) (g si : Bool) : ℕ :=
  (cndT i t g si false &&& rst lo i false) ||| (cndT i t g si true &&& rst lo i true)

def absHiT (hi : ℕ) (i : Fin 6) (t : ℕ) (g si : Bool) : ℕ :=
  M ^^^ ((cndT i t g si false &&& (M ^^^ rst hi i false)) |||
    (cndT i t g si true &&& (M ^^^ rst hi i true)))

theorem InIv.absT {lo hi : ℕ} {h : (Fin 6 → Bool) → Bool} (hI : InIv lo hi h) {i : Fin 6}
    {t : ℕ} (ht : ∀ z b, ev t (upd z i b) = ev t z) {g si : Bool} {ψ : DMFormula 6}
    (hψ : ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i)) (ev t x)))) :
    InIv (absLoT lo i t g si) (absHiT hi i t g si) ψ.eval := by
  have key : ∀ z b, bop g (litv si b) (ev t z) = z i → h (upd z i b) = ψ.eval z := by
    intro z b hb
    rw [hψ, ht]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp [upd, hb]
    · simp [upd, hk]
  intro z
  have hf : ∀ b, bop g (litv si b) (ev t z) = z i → ψ.eval z = true →
      ev hi (upd z i b) = true := fun b hb hz => (hI _).2 (by rw [key z b hb]; exact hz)
  have hl : ∀ b, bop g (litv si b) (ev t z) = z i → ev lo (upd z i b) = true →
      ψ.eval z = true := fun b hb hz => by rw [← key z b hb]; exact (hI _).1 hz
  clear key hψ ht
  have f0 := hf false
  have f1 := hf true
  have g0 := hl false
  have g1 := hl true
  clear hf hl
  simp only [absLoT, absHiT, ev_or, ev_and, ev_xor, ev_M, ev_cndT, ev_rst]
  generalize ψ.eval z = v at f0 f1 g0 g1 ⊢
  generalize ev lo (upd z i false) = l0 at f0 f1 g0 g1 ⊢
  generalize ev lo (upd z i true) = l1 at f0 f1 g0 g1 ⊢
  generalize ev hi (upd z i false) = u0 at f0 f1 g0 g1 ⊢
  generalize ev hi (upd z i true) = u1 at f0 f1 g0 g1 ⊢
  generalize bop g (litv si false) (ev t z) = p0 at f0 f1 g0 g1 ⊢
  generalize bop g (litv si true) (ev t z) = p1 at f0 f1 g0 g1 ⊢
  generalize z i = w at f0 f1 g0 g1 ⊢
  revert f0 f1 g0 g1
  cases v <;> cases l0 <;> cases l1 <;> cases u0 <;> cases u1 <;> cases p0 <;> cases p1 <;>
    cases w <;> simp

def F6 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

def BB : List Bool := [false, true]

theorem mem_F6 (j : Fin 6) : j ∈ F6 := by fin_cases j <;> simp [F6]

theorem mem_BB (b : Bool) : b ∈ BB := by cases b <;> simp [BB]

def nstep (o : Vec) (p : ℕ × ℕ) (i : Fin 6) : ℕ × ℕ :=
  if o i = 0 then (rst p.1 i false ||| rst p.1 i true, rst p.2 i false &&& rst p.2 i true) else p

def nrm (lo hi : ℕ) (o : Vec) : ℕ × ℕ := F6.foldl (nstep o) (lo, hi)

theorem nstep_ok {o : Vec} {h : (Fin 6 → Bool) → Bool} (hA : Ach o h) (p : ℕ × ℕ) (i : Fin 6)
    (hI : InIv p.1 p.2 h) : InIv (nstep o p i).1 (nstep o p i).2 h := by
  unfold nstep
  split_ifs with h0
  · intro x
    have e0 := hA.upd_inv i h0 x false
    have e1 := hA.upd_inv i h0 x true
    simp only [ev_or, ev_and, ev_rst, Bool.or_eq_true, Bool.and_eq_true]
    refine ⟨fun hl => ?_, fun hx => ⟨?_, ?_⟩⟩
    · rcases hl with hl | hl
      · rw [← e0]; exact (hI _).1 hl
      · rw [← e1]; exact (hI _).1 hl
    · exact (hI _).2 (by rw [e0]; exact hx)
    · exact (hI _).2 (by rw [e1]; exact hx)
  · exact hI

theorem nrm_ok {o : Vec} {h : (Fin 6 → Bool) → Bool} {lo hi : ℕ} (hA : Ach o h)
    (hI : InIv lo hi h) : InIv (nrm lo hi o).1 (nrm lo hi o).2 h := by
  unfold nrm
  suffices ∀ (l : List (Fin 6)) (p : ℕ × ℕ), InIv p.1 p.2 h →
      InIv (l.foldl (nstep o) p).1 (l.foldl (nstep o) p).2 h from this _ _ hI
  intro l
  induction l with
  | nil => intro p hp; exact hp
  | cons i l ih => intro p hp; exact ih _ (nstep_ok hA p i hp)

theorem bad_nrm {lo hi : ℕ} {o : Vec} (hb : Bad (nrm lo hi o).1 (nrm lo hi o).2 o) :
    Bad lo hi o := fun h hI hA => hb h (nrm_ok hA hI) hA

theorem bad0 {lo hi : ℕ} {o : Vec} (hz : lo &&& (M ^^^ hi) &&& M ≠ 0) : Bad lo hi o := by
  intro h hI _
  obtain ⟨x, hx⟩ := exists_x _ hz
  simp only [ev_and, ev_xor, ev_M, Bool.and_eq_true] at hx
  have h2 := (hI x).2 ((hI x).1 hx.1)
  rw [h2] at hx
  simp at hx

theorem bad1 {lo hi : ℕ} {o : Vec} (i : Fin 6) (c : Bool)
    (hb : Bad (rst lo i c) (rst hi i c) (zv o i)) : Bad lo hi o :=
  fun h hI hA => hb _ (hI.rst' i c) (hA.restrict i c)

def kids2 (lo hi : ℕ) (o : Vec) (i : Fin 6) : List (ℕ × ℕ × Vec) :=
  (lo, hi, dv o i) :: BB.flatMap (fun c => (F6.filter (fun j => decide (j ≠ i ∧ 1 ≤ o j))).map
    (fun j => (rst lo i c, rst hi i c, dv (zv o i) j)))

theorem mem_kids2 {lo hi : ℕ} {o : Vec} {i j : Fin 6} (c : Bool) (hji : j ≠ i) (hj : 1 ≤ o j) :
    (rst lo i c, rst hi i c, dv (zv o i) j) ∈ kids2 lo hi o i := by
  simp only [kids2, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact .inr ⟨c, mem_BB c, j, ⟨mem_F6 j, decide_eq_true ⟨hji, hj⟩⟩, rfl⟩

theorem bad2 {lo hi : ℕ} {o : Vec} {i : Fin 6} (h2 : 2 ≤ o i)
    (hk : ∀ k ∈ kids2 lo hi o i, Bad k.1 k.2.1 k.2.2) : Bad lo hi o := by
  intro h hI hA
  have c1 : Bad lo hi (dv o i) := hk (lo, hi, dv o i) (by simp [kids2])
  rcases hA with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · exact c1 h hI (.inl ⟨c0, hc⟩)
  · by_cases hφ : occ φ i = 0 ∨ ∃ s, φ = .lit i s
    · refine c1 h hI (.inr ⟨φ, he, fun k => ?_⟩)
      have := ho k
      have := ho i
      rcases hφ with h0 | ⟨s, rfl⟩
      · simp only [dv]; split_ifs <;> subst_vars <;> omega
      · simp only [dv, occ] at *; split_ifs at * <;> subst_vars <;> omega
    · push Not at hφ
      obtain ⟨h0, hl⟩ := hφ
      rcases kill_multi i φ (by omega) hl with ha | ⟨c, j, hji, hj, ha⟩
      · refine c1 h hI ((ha.mono (fun k => ?_)).congr he)
        have := ho k; have := ho i
        simp only [dv]; split_ifs <;> subst_vars <;> omega
      · have hk' := hk _ (mem_kids2 (lo := lo) (hi := hi) c hji (le_trans hj (ho j)))
        refine hk' _ (hI.rst' i c) ((ha.mono (fun k => ?_)).congr (fun x => he _))
        have := ho k; have := ho i; have := ho j
        simp only [dv, zv]; split_ifs <;> subst_vars <;> omega

def litin (lo hi t : ℕ) : Bool := (lo &&& (M ^^^ t) &&& M == 0) && (t &&& (M ^^^ hi) &&& M == 0)

def litok (lo hi : ℕ) (i : Fin 6) : Bool := !litin lo hi (litT i true) && !litin lo hi (litT i false)

theorem litin_of {lo hi t : ℕ} {h : (Fin 6 → Bool) → Bool} (hI : InIv lo hi h)
    (he : ∀ x, h x = ev t x) : litin lo hi t = true := by
  unfold litin
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · by_contra hne
    obtain ⟨x, hx⟩ := exists_x _ hne
    simp only [ev_and, ev_xor, ev_M, Bool.and_eq_true] at hx
    have := (hI x).1 hx.1
    rw [he] at this
    rw [this] at hx
    simp at hx
  · by_contra hne
    obtain ⟨x, hx⟩ := exists_x _ hne
    simp only [ev_and, ev_xor, ev_M, Bool.and_eq_true] at hx
    have := (hI x).2 (by rw [he]; exact hx.1)
    rw [this] at hx
    simp at hx

def kids3 (lo hi : ℕ) (o : Vec) (i : Fin 6) : List (ℕ × ℕ × Vec) :=
  (lo, hi, zv o i) ::
  ((F6.filter (fun j => decide (j ≠ i ∧ 1 ≤ o j))).flatMap (fun j => BB.flatMap (fun g =>
    BB.flatMap (fun si => BB.map (fun sj =>
      (absLo lo i j g si sj, absHi hi i j g si sj, dv o j))))) ++
  BB.flatMap (fun c => F6.flatMap (fun j => (F6.filter (fun k =>
    decide (j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ 1 ≤ o j ∧ 1 ≤ o k ∧ (j ≠ k ∨ 2 ≤ o j)))).map
      (fun k => (rst lo i c, rst hi i c, dv (dv (zv o i) j) k)))))

theorem mem_kids3_abs {lo hi : ℕ} {o : Vec} {i j : Fin 6} (g si sj : Bool) (hji : j ≠ i)
    (hj : 1 ≤ o j) : (absLo lo i j g si sj, absHi hi i j g si sj, dv o j) ∈ kids3 lo hi o i := by
  simp only [kids3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inl ⟨j, ⟨mem_F6 j, decide_eq_true ⟨hji, hj⟩⟩, g, mem_BB g, si, mem_BB si, sj,
    mem_BB sj, rfl⟩)

theorem mem_kids3_kill {lo hi : ℕ} {o : Vec} {i j k : Fin 6} (c : Bool) (hji : j ≠ i)
    (hki : k ≠ i) (hjk : j ≤ k) (hj : 1 ≤ o j) (hk : 1 ≤ o k) (hjk2 : j ≠ k ∨ 2 ≤ o j) :
    (rst lo i c, rst hi i c, dv (dv (zv o i) j) k) ∈ kids3 lo hi o i := by
  simp only [kids3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inr ⟨c, mem_BB c, j, mem_F6 j, k,
    ⟨mem_F6 k, decide_eq_true ⟨hji, hki, hjk, hj, hk, hjk2⟩⟩, rfl⟩)

theorem bad3 {lo hi : ℕ} {o : Vec} {i : Fin 6} (h1 : o i = 1) (hlit : litok lo hi i = true)
    (hk : ∀ k ∈ kids3 lo hi o i, Bad k.1 k.2.1 k.2.2) : Bad lo hi o := by
  intro h hI hA
  have c1 : Bad lo hi (zv o i) := hk (lo, hi, zv o i) (by simp [kids3])
  rcases hA with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · exact c1 h hI (.inl ⟨c0, hc⟩)
  · by_cases h0 : occ φ i = 0
    · refine c1 h hI (.inr ⟨φ, he, fun k => ?_⟩)
      have := ho k
      simp only [zv]; split_ifs <;> subst_vars <;> omega
    · have hi1 : occ φ i = 1 := by have := ho i; omega
      by_cases hl : ∃ s, φ = .lit i s
      · obtain ⟨s, rfl⟩ := hl
        have := litin_of hI (t := litT i s) (fun x => by rw [← he, eval_lit, ev_litT])
        unfold litok at hlit
        cases s <;> simp_all
      · push Not at hl
        rcases kill_single i φ hi1 hl with ⟨j, hji, hj, g, si, sj, ψ, hψo, hψe⟩ |
          ⟨c, j, k, hji, hki, hjk, hj, hk1, hjk2, ha⟩
        · have hk' := hk _ (mem_kids3_abs (lo := lo) (hi := hi) g si sj hji (le_trans hj (ho j)))
          refine hk' _ (hI.abs hji (fun x => by rw [← he]; exact hψe x))
            (.inr ⟨ψ, fun _ => rfl, fun m => ?_⟩)
          have h3 := hψo m
          have := ho m; have := ho j
          simp only [dv] at h3 ⊢
          split_ifs at h3 ⊢ <;> subst_vars <;> omega
        · have hk' := hk _ (mem_kids3_kill (lo := lo) (hi := hi) c hji hki hjk
            (le_trans hj (ho j)) (le_trans hk1 (ho k)) (hjk2.imp id (fun e => le_trans e (ho j))))
          refine hk' _ (hI.rst' i c) ((ha.mono (fun m => ?_)).congr (fun x => he _))
          have := ho m; have := ho i; have := ho j; have := ho k
          simp only [dv, zv]; split_ifs <;> subst_vars <;> omega

def kids4 (lo hi : ℕ) (o : Vec) (i : Fin 6) : List (ℕ × ℕ × Vec) :=
  (lo, hi, zv o i) ::
  ((F6.filter (fun j => decide (j ≠ i ∧ 1 ≤ o j))).flatMap (fun j => BB.flatMap (fun g =>
    BB.flatMap (fun si => BB.map (fun sj =>
      (absLo lo i j g si sj, absHi hi i j g si sj, dv o j))))) ++
  (F6.flatMap (fun j => (F6.filter (fun k =>
    decide (j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ 1 ≤ o j ∧ 1 ≤ o k ∧ (j ≠ k ∨ 2 ≤ o j)))).flatMap
      (fun k => BB.flatMap (fun g => BB.flatMap (fun si => BB.flatMap (fun g2 =>
        BB.flatMap (fun sj => BB.map (fun sk =>
          (absLoT lo i (opT g2 (litT j sj) (litT k sk)) g si,
            absHiT hi i (opT g2 (litT j sj) (litT k sk)) g si, dv (dv o j) k)))))))) ++
  BB.flatMap (fun c => F6.flatMap (fun j => F6.flatMap (fun k => (F6.filter (fun l =>
    decide (j ≠ i ∧ k ≠ i ∧ l ≠ i ∧ j ≤ k ∧ k ≤ l ∧ Fit3 (zv o i) j k l))).map
      (fun l => (rst lo i c, rst hi i c, dv (dv (dv (zv o i) j) k) l)))))))

theorem mem_kids4_abs {lo hi : ℕ} {o : Vec} {i j : Fin 6} (g si sj : Bool) (hji : j ≠ i)
    (hj : 1 ≤ o j) : (absLo lo i j g si sj, absHi hi i j g si sj, dv o j) ∈ kids4 lo hi o i := by
  simp only [kids4, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inl ⟨j, ⟨mem_F6 j, decide_eq_true ⟨hji, hj⟩⟩, g, mem_BB g, si, mem_BB si, sj,
    mem_BB sj, rfl⟩)

theorem mem_kids4_abs2 {lo hi : ℕ} {o : Vec} {i j k : Fin 6} (g si g2 sj sk : Bool)
    (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≤ k) (hj : 1 ≤ o j) (hk : 1 ≤ o k)
    (hjk2 : j ≠ k ∨ 2 ≤ o j) :
    (absLoT lo i (opT g2 (litT j sj) (litT k sk)) g si,
      absHiT hi i (opT g2 (litT j sj) (litT k sk)) g si, dv (dv o j) k) ∈ kids4 lo hi o i := by
  simp only [kids4, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inr (.inl ⟨j, mem_F6 j, k,
    ⟨mem_F6 k, decide_eq_true ⟨hji, hki, hjk, hj, hk, hjk2⟩⟩, g, mem_BB g, si, mem_BB si,
    g2, mem_BB g2, sj, mem_BB sj, sk, mem_BB sk, rfl⟩))

theorem mem_kids4_kill {lo hi : ℕ} {o : Vec} {i j k l : Fin 6} (c : Bool) (hji : j ≠ i)
    (hki : k ≠ i) (hli : l ≠ i) (hjk : j ≤ k) (hkl : k ≤ l) (hf : Fit3 (zv o i) j k l) :
    (rst lo i c, rst hi i c, dv (dv (dv (zv o i) j) k) l) ∈ kids4 lo hi o i := by
  simp only [kids4, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inr (.inr ⟨c, mem_BB c, j, mem_F6 j, k, mem_F6 k, l,
    ⟨mem_F6 l, decide_eq_true ⟨hji, hki, hli, hjk, hkl, hf⟩⟩, rfl⟩))

theorem bad4 {lo hi : ℕ} {o : Vec} {i : Fin 6} (h1 : o i = 1) (hlit : litok lo hi i = true)
    (hk : ∀ k ∈ kids4 lo hi o i, Bad k.1 k.2.1 k.2.2) : Bad lo hi o := by
  intro h hI hA
  have c1 : Bad lo hi (zv o i) := hk (lo, hi, zv o i) (by simp [kids4])
  rcases hA with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · exact c1 h hI (.inl ⟨c0, hc⟩)
  · by_cases h0 : occ φ i = 0
    · refine c1 h hI (.inr ⟨φ, he, fun k => ?_⟩)
      have := ho k
      simp only [zv]; split_ifs <;> subst_vars <;> omega
    · have hi1 : occ φ i = 1 := by have := ho i; omega
      by_cases hl : ∃ s, φ = .lit i s
      · obtain ⟨s, rfl⟩ := hl
        have := litin_of hI (t := litT i s) (fun x => by rw [← he, eval_lit, ev_litT])
        unfold litok at hlit
        cases s <;> simp_all
      · push Not at hl
        rcases kill_single4 i φ hi1 hl with ⟨j, hji, hj, g, si, sj, ψ, hψo, hψe⟩ |
          ⟨j, k, hji, hki, hjk, hj, hk1, hjk2, g, si, g2, sj, sk, ψ, hψo, hψe⟩ |
          ⟨c, j, k, l, hji, hki, hli, hjk, hkl, ⟨f1, f2, f3⟩, ha⟩
        · have hk' := hk _ (mem_kids4_abs (lo := lo) (hi := hi) g si sj hji (le_trans hj (ho j)))
          refine hk' _ (hI.abs hji (fun x => by rw [← he]; exact hψe x))
            (.inr ⟨ψ, fun _ => rfl, fun m => ?_⟩)
          have h3 := hψo m
          have := ho m; have := ho j
          simp only [dv] at h3 ⊢
          split_ifs at h3 ⊢ <;> subst_vars <;> omega
        · have hk' := hk _ (mem_kids4_abs2 (lo := lo) (hi := hi) g si g2 sj sk hji hki hjk
            (le_trans hj (ho j)) (le_trans hk1 (ho k)) (hjk2.imp id (fun e => le_trans e (ho j))))
          have ht : ∀ z b, ev (opT g2 (litT j sj) (litT k sk)) (upd z i b) =
              ev (opT g2 (litT j sj) (litT k sk)) z := by
            intro z b
            simp [ev_opT, ev_litT, upd, hji, hki]
          refine hk' _ (hI.absT ht (fun x => ?_))
            (.inr ⟨ψ, fun _ => rfl, fun m => le_trans (hψo m) (dv_le k (dv_le j ho) m)⟩)
          rw [← he, ev_opT, ev_litT, ev_litT]
          exact hψe x
        · have hk' := hk _ (mem_kids4_kill (lo := lo) (hi := hi) c hji hki hli hjk hkl
            ⟨le_trans f1 (zv_le i ho j), le_trans f2 (dv_le j (zv_le i ho) k),
              le_trans f3 (dv_le k (dv_le j (zv_le i ho)) l)⟩)
          exact hk' _ (hI.rst' i c) ((ha.mono (dv_le l (dv_le k (dv_le j (zv_le i ho))))).congr
            (fun x => he _))

def chkAll (f : ℕ → ℕ → Vec → ℕ → Option ℕ) : List (ℕ × ℕ × Vec) → ℕ → Option ℕ
  | [], r => some r
  | k :: ks, r => (f k.1 k.2.1 k.2.2 r).bind (chkAll f ks)

theorem chkAll_ok (f : ℕ → ℕ → Vec → ℕ → Option ℕ) : ∀ (ks : List (ℕ × ℕ × Vec)) (r r' : ℕ),
    chkAll f ks r = some r' → ∀ k ∈ ks, ∃ r1 r2, f k.1 k.2.1 k.2.2 r1 = some r2
  | [], _, _, _ => by simp
  | k :: ks, r, r', h => by
    simp only [chkAll, Option.bind_eq_some_iff] at h
    obtain ⟨r1, h1, h2⟩ := h
    intro k' hk'
    rcases List.mem_cons.1 hk' with rfl | hk'
    · exact ⟨r, r1, h1⟩
    · exact chkAll_ok f ks r1 r' h2 k' hk'

def chk : ℕ → ℕ → ℕ → Vec → ℕ → Option ℕ
  | 0, _, _, _, _ => none
  | n + 1, lo0, hi0, o, cert =>
    if cert % 8 = 0 then
      (if (nrm lo0 hi0 o).1 &&& (M ^^^ (nrm lo0 hi0 o).2) &&& M ≠ 0 then some (cert / 8) else none)
    else if hi6 : cert / 8 % 8 < 6 then
      (if cert % 8 = 1 then
        chk n (rst (nrm lo0 hi0 o).1 ⟨cert / 8 % 8, hi6⟩ (cert / 8 / 8 % 8 == 1))
          (rst (nrm lo0 hi0 o).2 ⟨cert / 8 % 8, hi6⟩ (cert / 8 / 8 % 8 == 1))
          (zv o ⟨cert / 8 % 8, hi6⟩) (cert / 8 / 8 / 8)
      else if cert % 8 = 2 then
        (if 2 ≤ o ⟨cert / 8 % 8, hi6⟩ then
          chkAll (chk n) (kids2 (nrm lo0 hi0 o).1 (nrm lo0 hi0 o).2 o ⟨cert / 8 % 8, hi6⟩)
            (cert / 8 / 8)
        else none)
      else if cert % 8 = 3 then
        (if o ⟨cert / 8 % 8, hi6⟩ = 1 ∧
            litok (nrm lo0 hi0 o).1 (nrm lo0 hi0 o).2 ⟨cert / 8 % 8, hi6⟩ = true then
          chkAll (chk n) (kids3 (nrm lo0 hi0 o).1 (nrm lo0 hi0 o).2 o ⟨cert / 8 % 8, hi6⟩)
            (cert / 8 / 8)
        else none)
      else if cert % 8 = 4 then
        (if o ⟨cert / 8 % 8, hi6⟩ = 1 ∧
            litok (nrm lo0 hi0 o).1 (nrm lo0 hi0 o).2 ⟨cert / 8 % 8, hi6⟩ = true then
          chkAll (chk n) (kids4 (nrm lo0 hi0 o).1 (nrm lo0 hi0 o).2 o ⟨cert / 8 % 8, hi6⟩)
            (cert / 8 / 8)
        else none)
      else none)
    else none

theorem chk_ok : ∀ (n lo hi : ℕ) (o : Vec) (cert r : ℕ), chk n lo hi o cert = some r → Bad lo hi o
  | 0, _, _, _, _, _, h => by simp [chk] at h
  | n + 1, lo, hi, o, cert, r, h => by
    apply bad_nrm
    have IH : ∀ ks : List (ℕ × ℕ × Vec), ∀ r1 r2, chkAll (chk n) ks r1 = some r2 →
        ∀ k ∈ ks, Bad k.1 k.2.1 k.2.2 := fun ks r1 r2 e k hk => by
      obtain ⟨_, _, e'⟩ := chkAll_ok _ ks r1 r2 e k hk
      exact chk_ok n _ _ _ _ _ e'
    simp only [chk] at h
    split_ifs at h with t0 z hi6 t1 t2 h2 t3 h3 t4 h4
    · exact bad0 z
    · exact bad1 _ _ (chk_ok n _ _ _ _ _ h)
    · exact bad2 h2 (IH _ _ _ h)
    · exact bad3 h3.1 h3.2 (IH _ _ _ h)
    · exact bad4 h4.1 h4.2 (IH _ _ _ h)

def fT : ℕ := 18446743974923794664

-- certificates for chk, one per vector of topsL: base 8 digits, lowest digit first
def certL : List ℕ :=
  [413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 237569839617, 28196487705, 236496097793, 28196487705, 28196487705, 304141832705, 3628339713, 3628339713, 4702081537, 3628339713, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 413418009, 237569839617, 402669806202526098416018131275109456603977812897088495543923664161123582212348183301493314560725253281666778501664171545669495759237216747967713228281219478292396586723225899871135603971118394016614885306835413503612336234018359520395451230202663141195110042342144726049, 236496097793, 182862907334718948622024255910217562730822196327660463253015220940300085995784953626527238657840037533750648912870046998086939903054067066845315651201441076152006058488150996157078738805402847316248032239053956550021415739666422820648357076744067084939627015538880022251732716501475290092696134820919124994521127338685442241659364873293866515887465931305316409092786069001190750799939881103303927284580219429345702610622336202753397013528297393801068287829437962912161069252105677445338170486979112113811528345610483591816555224442791313174494779014107405646084721068107659165192481085677791672459135808041147990994594274902737593753697573056358842008874078177571115753930958943556110405564866276905403586121050492624360623909614301190396669738765432537472487853508306671486114688567492120146904545260163998558382106520020080564434384817553834990463944179601413311259834608735097968028192890675651257402170232278160951556344507676104695475118646024360661430100124277210011636164981000653849644575861608397919593477004558431662427495757080750475487589876536989972463902850452685467547508900465878189906633057485255014631558566597554099252200994825784071890398424073652182273187977517315764204787409298431288381906479801675251196959917702283921479918669691716780442099851629599294492464681213564297261368670887355337596570822963743244635767913001631201843524500118630276343064541391287716052587197696744297802048331125993625488804898829803412033292532872353016889288526059847922866709559352189994183637245402041872232681802190924096616786872699749874081514651652, 22857863416839868577753031988777195341352774540957557906626902617537510749473119203318478692161794203402793261827436325599805606294495129736744070568321021354426911580733539752057500769278572542692996548563743083571028525460590563266407463863187628482261573856687366679344986084625617433034994228231580525439494131957466183654847724455979009312498302215940641419532131165433395705439269244562054925809470441779892950996676496426474331234258778741667906820119108651557976030329336793406581587972077817877380523591801024681144939771222912465478481109238472193154548488893852815106813064349409454624734727455804721893116236576700235183233402058453864620930198488979926727885036956896804483369765446803556656984430756655168506777816222908443818982414340333319424560309999907673906617330351483246081152039334528340452765383145589433898176370394623976760548540515377659369170687879424796609394461826944643302574898180283302059663180181101957106713060027414703928288818230979879613701596212190949405611457236895298747333027109859516520610984128163762378380772428158807170903530056507474647929212977175987672481713356417864946762312331116548964541164471378131060186001784289253538899335641417090594814197370368113808053240500646168960426743118142751680389266738882771436033844238295271125584420588695154391345310024438400418779876414845563152661041832088536220540189164370722061326171599715788166283815731405754451023831174033556289447555563322709545861371677961079004595453152662978485938554048473832855002204946311260249006589122519403817059703652747346600668430340, 304141832705, 3628339713, 3628339713, 4702081537, 3628339713, 237569839617, 27122745881, 236496097793, 27122745881, 27122745881, 304141832705, 3628339713, 3628339713, 4702081537, 3628339713, 3628339713, 3628339713, 4702081537, 3628339713, 3628339713, 1487159833, 1487159833, 1487159833, 1487159833, 1487159833, 1487159833, 1487159833, 1487159833, 1487159833, 1487159833, 237569839617, 1459258868473856591120696535325843340390990019040864001314259217721889122957428345520005658039871427760184558991259579329077422355897463833171089927743255447408271526032361843858596758220128980462011738739684660395440521095379675407645385817273364744737496895106678379553, 236496097793, 182862700902430933852801468258697845204676467708598853705122511288219136637943641227921265996880974036038547776733030254030277301390171757171444402160888502511700682721815374934244334784827653612900105024464155792891270876361465544621385663404313796294687063994010675845667897093822983087652749328470544911624979613325904012468155923474251579610150979802632499631267454576349258808340214739438126265134851947347115362540427614716289775138451759958079954791724014259580339799020433270533668862091087886998834409672017559400389669411483125876212712606815317563347823708513682902229527476105817054335503394394829584509488286164987339426202570280853419564416787034394487947657151659273448914324521973255163515318695846694460361314513926890121563752540503837580874515490387082552050163006009448267878650241940223334165939375959568467362697690472607237418112826789605767843270592618216930736795361506624780562953127316343317411731682531718179184552433732060606469156725769942459399002551637844013123727148404698382444831569702034506544432897262138004847892763180737705991283608036244000222137850498676642925549252218618790592551441994360879491687956619336572965648818170149023780614327534233443882260866963165606893881864637165664763277022167221650954699553779261692652486646559970440518690082561798873639076315869110944449880510011126863264689666268934113106558303826301904758847789615637959406300278046326879685074165110448644700261100119953717698110025442356972759429777726743618110361055813870242492443425886411961645731998591391969704926543943512088308927692812, 22857837612803866731600183532337230650584558463574856713140313911027392079742955153492732106636303986434199619455247370150685094541866108775532658065745109610406061819949719669765327387837473719731125852119134231541963567292678229771416432408792526258077097877257574243206440618744554517410098150677551986570769966898019471687426826480217902416466074795112585112555010705446686540239925449573557555311786360435535358962027552884132114942766250218056077878899659226779025427447326363403170302352444879763797651728307941921143488603881667368345329495385756518543614055493389882919504518593596239051413911812028998693990737582741407348659206487541419869687733294946143740776591153110848570683089439775657089327571381055243197864786179656657715584096635425242761645535885873931017451993701851579465699710015119179075429693714410416256086004188088933667782328402180960800657064180912768076250601748824185715818602763802657235391788383061185943659894812526590474085305485054856175371965821711067915978398088138827981228322565384513813016400923532531377407923056803498649637543036782989421823649496155586639152658236290210145233616548597628603648127951349027114675331908103235141923531156553011447358771348800127214354391729173745507692429291390085778715987490527434788694312126477792862273837258483350162098866651066361403431149116649995626760844298045734787123020296116950494277108881582422898850789764845773621105038139258048694065795715471811561559657075412991032010934715135354000833035273378212190124182042326605378483812945824628107240646145303618924008439820, 304141832705, 3628339713, 3628339713, 4702081537, 3628339713, 237569839617, 1065162437039640599174132809534071209367014753715310595772514594268462661369581346779224757734973772597720052113904641, 236496097793, 37015699238204795014929381821372708869949019992800689863818161980773114979830045973198439012236246845141143572997442642423096596076332402670931249894084897288027148823454569763481565712639098400764320638431817952091567929481014511898162715838525316848685439255726967329793, 4626962404775599376866183064374218343630684343493693394745337319023832561789223464123741123239893396079275664956427585306541053849650414916156572031402329749203684462014607729676406619487619020422847000343415755833119647511942987062707819589308468501355612199061310247937, 304141832705, 3628339713, 3628339713, 4702081537, 3628339713, 3628339713, 3628339713, 4702081537, 3628339713, 3628339713, 237569839617, 94768480793, 236496097793, 94768480793, 94768480793, 304141832705, 3628339713, 3628339713, 4702081537, 3628339713, 3628339713, 3628339713, 4702081537, 3628339713, 3628339713, 3628339713, 3628339713, 4702081537, 3628339713, 3628339713, 3628339713]

def topsL : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 5], [1, 1, 1, 1, 2, 4], [1, 1, 1, 1, 3, 3], [1, 1, 1, 1, 4, 2], [1, 1, 1, 1, 5, 1], [1, 1, 1, 2, 1, 4], [1, 1, 1, 2, 2, 3], [1, 1, 1, 2, 3, 2], [1, 1, 1, 2, 4, 1], [1, 1, 1, 3, 1, 3], [1, 1, 1, 3, 2, 2], [1, 1, 1, 3, 3, 1], [1, 1, 1, 4, 1, 2], [1, 1, 1, 4, 2, 1], [1, 1, 1, 5, 1, 1], [1, 1, 2, 1, 1, 4], [1, 1, 2, 1, 2, 3], [1, 1, 2, 1, 3, 2], [1, 1, 2, 1, 4, 1], [1, 1, 2, 2, 1, 3], [1, 1, 2, 2, 2, 2], [1, 1, 2, 2, 3, 1], [1, 1, 2, 3, 1, 2], [1, 1, 2, 3, 2, 1], [1, 1, 2, 4, 1, 1], [1, 1, 3, 1, 1, 3], [1, 1, 3, 1, 2, 2], [1, 1, 3, 1, 3, 1], [1, 1, 3, 2, 1, 2], [1, 1, 3, 2, 2, 1], [1, 1, 3, 3, 1, 1], [1, 1, 4, 1, 1, 2], [1, 1, 4, 1, 2, 1], [1, 1, 4, 2, 1, 1], [1, 1, 5, 1, 1, 1], [1, 2, 1, 1, 1, 4], [1, 2, 1, 1, 2, 3], [1, 2, 1, 1, 3, 2], [1, 2, 1, 1, 4, 1], [1, 2, 1, 2, 1, 3], [1, 2, 1, 2, 2, 2], [1, 2, 1, 2, 3, 1], [1, 2, 1, 3, 1, 2], [1, 2, 1, 3, 2, 1], [1, 2, 1, 4, 1, 1], [1, 2, 2, 1, 1, 3], [1, 2, 2, 1, 2, 2], [1, 2, 2, 1, 3, 1], [1, 2, 2, 2, 1, 2], [1, 2, 2, 2, 2, 1], [1, 2, 2, 3, 1, 1], [1, 2, 3, 1, 1, 2], [1, 2, 3, 1, 2, 1], [1, 2, 3, 2, 1, 1], [1, 2, 4, 1, 1, 1], [1, 3, 1, 1, 1, 3], [1, 3, 1, 1, 2, 2], [1, 3, 1, 1, 3, 1], [1, 3, 1, 2, 1, 2], [1, 3, 1, 2, 2, 1], [1, 3, 1, 3, 1, 1], [1, 3, 2, 1, 1, 2], [1, 3, 2, 1, 2, 1], [1, 3, 2, 2, 1, 1], [1, 3, 3, 1, 1, 1], [1, 4, 1, 1, 1, 2], [1, 4, 1, 1, 2, 1], [1, 4, 1, 2, 1, 1], [1, 4, 2, 1, 1, 1], [1, 5, 1, 1, 1, 1], [2, 1, 1, 1, 1, 4], [2, 1, 1, 1, 2, 3], [2, 1, 1, 1, 3, 2], [2, 1, 1, 1, 4, 1], [2, 1, 1, 2, 1, 3], [2, 1, 1, 2, 2, 2], [2, 1, 1, 2, 3, 1], [2, 1, 1, 3, 1, 2], [2, 1, 1, 3, 2, 1], [2, 1, 1, 4, 1, 1], [2, 1, 2, 1, 1, 3], [2, 1, 2, 1, 2, 2], [2, 1, 2, 1, 3, 1], [2, 1, 2, 2, 1, 2], [2, 1, 2, 2, 2, 1], [2, 1, 2, 3, 1, 1], [2, 1, 3, 1, 1, 2], [2, 1, 3, 1, 2, 1], [2, 1, 3, 2, 1, 1], [2, 1, 4, 1, 1, 1], [2, 2, 1, 1, 1, 3], [2, 2, 1, 1, 2, 2], [2, 2, 1, 1, 3, 1], [2, 2, 1, 2, 1, 2], [2, 2, 1, 2, 2, 1], [2, 2, 1, 3, 1, 1], [2, 2, 2, 1, 1, 2], [2, 2, 2, 1, 2, 1], [2, 2, 2, 2, 1, 1], [2, 2, 3, 1, 1, 1], [2, 3, 1, 1, 1, 2], [2, 3, 1, 1, 2, 1], [2, 3, 1, 2, 1, 1], [2, 3, 2, 1, 1, 1], [2, 4, 1, 1, 1, 1], [3, 1, 1, 1, 1, 3], [3, 1, 1, 1, 2, 2], [3, 1, 1, 1, 3, 1], [3, 1, 1, 2, 1, 2], [3, 1, 1, 2, 2, 1], [3, 1, 1, 3, 1, 1], [3, 1, 2, 1, 1, 2], [3, 1, 2, 1, 2, 1], [3, 1, 2, 2, 1, 1], [3, 1, 3, 1, 1, 1], [3, 2, 1, 1, 1, 2], [3, 2, 1, 1, 2, 1], [3, 2, 1, 2, 1, 1], [3, 2, 2, 1, 1, 1], [3, 3, 1, 1, 1, 1], [4, 1, 1, 1, 1, 2], [4, 1, 1, 1, 2, 1], [4, 1, 1, 2, 1, 1], [4, 1, 2, 1, 1, 1], [4, 2, 1, 1, 1, 1], [5, 1, 1, 1, 1, 1]]

def vecOf (l : List ℕ) : Vec := fun k => l.getD (k : ℕ) 0

def runL : List (List ℕ) → List ℕ → Prop
  | [], _ => True
  | _ :: _, [] => False
  | l :: ls, c :: cs => chk 30 fT fT (vecOf l) c = some 0 ∧ runL ls cs

theorem runL_nil (cs : List ℕ) : runL [] cs := trivial

theorem runL_cons {l : List ℕ} {ls : List (List ℕ)} {c : ℕ} {cs : List ℕ}
    (h1 : chk 30 fT fT (vecOf l) c = some 0) (h2 : runL ls cs) : runL (l :: ls) (c :: cs) :=
  And.intro h1 h2

theorem runL_ok : ∀ (ls : List (List ℕ)) (cs : List ℕ), runL ls cs →
    ∀ l ∈ ls, Bad fT fT (vecOf l)
  | [], _, _ => by simp
  | _ :: _, [], h => False.elim h
  | l :: ls, c :: cs, h => by
    have h2 : chk 30 fT fT (vecOf l) c = some 0 ∧ runL ls cs := h
    intro l1 hl1
    rcases List.mem_cons.1 hl1 with rfl | hl1
    · exact chk_ok _ _ _ _ _ _ h2.1
    · exact runL_ok ls cs h2.2 l1 hl1

theorem tops_run : runL topsL certL := by
  unfold topsL certL
  repeat' first | exact runL_nil _ | apply runL_cons
  all_goals decide +kernel

theorem tops_bad : ∀ l ∈ topsL, Bad fT fT (vecOf l) := runL_ok topsL certL tops_run

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tops_cover : ∀ a < 6, ∀ b < 6, ∀ c < 6, ∀ d < 6, ∀ e < 6, ∀ f < 6,
    ¬ (1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 1 ≤ d ∧ 1 ≤ e ∧ 1 ≤ f ∧ a + b + c + d + e + f = 10) ∨
    [a, b, c, d, e, f] ∈ topsL := by
  decide +kernel

def fn (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 3 && x 5) ||
    (x 4 && x 5)

theorem ev_fT : ∀ x, ev fT x = fn x := allx (by decide +kernel)

def up : DMFormula 6 :=
  .or (.or (.or (.and (.lit 2 true) (.or (.or (.lit 0 true) (.lit 1 true)) (.lit 3 true)))
    (.and (.lit 0 true) (.lit 1 true))) (.and (.lit 3 true) (.or (.lit 4 true) (.lit 5 true))))
    (.and (.lit 4 true) (.lit 5 true))

theorem up_leaves : up.leaves ≤ 11 := by decide

theorem up_eval : ∀ x, up.eval x = fn x := allx (by decide +kernel)

theorem dep (k : Fin 6) : ∃ x c, fn (upd x k c) ≠ fn x := by
  fin_cases k
  · exact ⟨![false, true, false, false, false, false], true, by decide⟩
  · exact ⟨![true, false, false, false, false, false], true, by decide⟩
  · exact ⟨![true, false, false, false, false, false], true, by decide⟩
  · exact ⟨![false, false, false, false, true, false], true, by decide⟩
  · exact ⟨![false, false, false, true, false, false], true, by decide⟩
  · exact ⟨![false, false, false, true, false, false], true, by decide⟩

theorem lower (φ : DMFormula 6) (hl : φ.leaves ≤ 10) (he : ∀ x, φ.eval x = fn x) : False := by
  have hpos : ∀ k, 1 ≤ occ φ k := by
    intro k
    by_contra hk
    obtain ⟨x, c, hx⟩ := dep k
    apply hx
    rw [← he, ← he, eval_upd_of_zero φ k (by omega)]
  rw [leaves_eq, Fin.sum_univ_six] at hl
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  have h3 := hpos 3
  have h4 := hpos 4
  have h5 := hpos 5
  have mem := tops_cover (10 - (occ φ 1 + occ φ 2 + occ φ 3 + occ φ 4 + occ φ 5)) (by omega)
    (occ φ 1) (by omega) (occ φ 2) (by omega) (occ φ 3) (by omega) (occ φ 4) (by omega)
    (occ φ 5) (by omega) |>.resolve_left (not_not.2 ⟨by omega, h1, h2, h3, h4, h5, by omega⟩)
  refine tops_bad _ mem fn (fun x => by rw [ev_fT]; exact ⟨id, id⟩) (.inr ⟨φ, he, fun k => ?_⟩)
  fin_cases k
  · show occ φ 0 ≤ 10 - (occ φ 1 + occ φ 2 + occ φ 3 + occ φ 4 + occ φ 5); omega
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

end PEqualNP.Outside.L_meta_186_aux

theorem PEqualNP.Outside.L_meta_186 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) s ↔ 11 ≤ s := by
  intro s
  unfold PEqualNP.MetaComplexity.HasLeafSize
  constructor
  · rintro ⟨φ, hl, he⟩
    by_contra hs
    exact PEqualNP.Outside.L_meta_186_aux.lower φ (by omega) he
  · intro hs
    exact ⟨PEqualNP.Outside.L_meta_186_aux.up, le_trans PEqualNP.Outside.L_meta_186_aux.up_leaves hs,
      PEqualNP.Outside.L_meta_186_aux.up_eval⟩
