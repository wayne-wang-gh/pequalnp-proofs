import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_185_aux

-- Restriction lemmas and certificate checker adapted from the checked L-meta-316.
open PEqualNP.MetaComplexity

abbrev Vec := Fin 5 → ℕ

def occ : DMFormula 5 → Fin 5 → ℕ
  | .lit i _ => fun k => if k = i then 1 else 0
  | .and a b => fun k => occ a k + occ b k
  | .or a b => fun k => occ a k + occ b k

def zv (o : Vec) (i : Fin 5) : Vec := fun k => if k = i then 0 else o k

def dv (o : Vec) (j : Fin 5) : Vec := fun k => if k = j then o j - 1 else o k

def upd (x : Fin 5 → Bool) (i : Fin 5) (c : Bool) : Fin 5 → Bool :=
  fun k => if k = i then c else x k

def litv (s v : Bool) : Bool := if s then v else !v

def bop (g a b : Bool) : Bool := if g then (a || b) else (a && b)

def mk (g : Bool) (a b : DMFormula 5) : DMFormula 5 := if g then .or a b else .and a b

theorem eval_mk (g : Bool) (a b : DMFormula 5) (x : Fin 5 → Bool) :
    (mk g a b).eval x = bop g (a.eval x) (b.eval x) := by
  cases g <;> rfl

theorem occ_mk (g : Bool) (a b : DMFormula 5) (k : Fin 5) :
    occ (mk g a b) k = occ a k + occ b k := by
  cases g <;> rfl

theorem eval_lit (i : Fin 5) (s : Bool) (x : Fin 5 → Bool) :
    (DMFormula.lit i s).eval x = litv s (x i) := by
  cases s <;> rfl

theorem leaves_eq (φ : DMFormula 5) : φ.leaves = ∑ k, occ φ k := by
  induction φ with
  | lit i b => simp [DMFormula.leaves, occ]
  | and a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]
  | or a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]

theorem eval_congr (φ : DMFormula 5) (x y : Fin 5 → Bool)
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

theorem eval_upd_of_zero (φ : DMFormula 5) (i : Fin 5) (h : occ φ i = 0) (x : Fin 5 → Bool)
    (c : Bool) : φ.eval (upd x i c) = φ.eval x := by
  apply eval_congr
  intro k hk
  have : k ≠ i := by rintro rfl; omega
  simp [upd, this]

theorem exists_occ (φ : DMFormula 5) : ∃ j, 1 ≤ occ φ j := by
  induction φ with
  | lit i b => exact ⟨i, by simp [occ]⟩
  | and a b iha ihb => obtain ⟨j, hj⟩ := iha; exact ⟨j, by simp [occ]; omega⟩
  | or a b iha ihb => obtain ⟨j, hj⟩ := iha; exact ⟨j, by simp [occ]; omega⟩

def Ach (o : Vec) (h : (Fin 5 → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x, h x = c) ∨ ∃ φ : DMFormula 5, (∀ x, φ.eval x = h x) ∧ ∀ k, occ φ k ≤ o k

theorem Ach.mono {o o' : Vec} {h : (Fin 5 → Bool) → Bool} (hle : ∀ k, o k ≤ o' k)
    (a : Ach o h) : Ach o' h := by
  rcases a with hc | ⟨φ, he, ho⟩
  · exact .inl hc
  · exact .inr ⟨φ, he, fun k => (ho k).trans (hle k)⟩

theorem Ach.congr {o : Vec} {h h' : (Fin 5 → Bool) → Bool} (e : ∀ x, h x = h' x)
    (a : Ach o h) : Ach o h' := by
  rcases a with ⟨c, hc⟩ | ⟨φ, he, ho⟩
  · exact .inl ⟨c, fun x => by rw [← e, hc]⟩
  · exact .inr ⟨φ, fun x => by rw [he, e], ho⟩

theorem Ach.form (φ : DMFormula 5) : Ach (occ φ) φ.eval := .inr ⟨φ, fun _ => rfl, fun _ => le_rfl⟩

theorem Ach.const (o : Vec) (c : Bool) : Ach o (fun _ => c) := .inl ⟨c, fun _ => rfl⟩

theorem Ach.bop {o1 o2 : Vec} {h1 h2 : (Fin 5 → Bool) → Bool} (g : Bool) (a1 : Ach o1 h1)
    (a2 : Ach o2 h2) : Ach (fun k => o1 k + o2 k) (fun x => bop g (h1 x) (h2 x)) := by
  rcases a1 with ⟨c1, hc1⟩ | ⟨φ1, e1, b1⟩
  · by_cases hg : c1 = g
    · exact .inl ⟨g, fun x => by beta_reduce; rw [hc1, hg]; cases g <;> simp [PEqualNP.Outside.L_meta_185_aux.bop]⟩
    · refine (a2.mono (fun k => Nat.le_add_left _ _)).congr (fun x => ?_)
      rw [hc1]; cases g <;> cases c1 <;> simp_all [PEqualNP.Outside.L_meta_185_aux.bop]
  · rcases a2 with ⟨c2, hc2⟩ | ⟨φ2, e2, b2⟩
    · by_cases hg : c2 = g
      · exact .inl ⟨g, fun x => by beta_reduce; rw [hc2, hg]; cases g <;> simp [PEqualNP.Outside.L_meta_185_aux.bop]⟩
      · refine (Ach.mono (o := o1) (fun k => Nat.le_add_right _ _) (.inr ⟨φ1, e1, b1⟩)).congr
          (fun x => ?_)
        rw [hc2]; cases g <;> cases c2 <;> simp_all [PEqualNP.Outside.L_meta_185_aux.bop]
    · exact .inr ⟨mk g φ1 φ2, fun x => by rw [eval_mk, e1, e2],
        fun k => by rw [occ_mk]; exact Nat.add_le_add (b1 k) (b2 k)⟩

theorem restrict (φ : DMFormula 5) (i : Fin 5) (c : Bool) :
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

theorem Ach.restrict {o : Vec} {h : (Fin 5 → Bool) → Bool} (a : Ach o h) (i : Fin 5) (c : Bool) :
    Ach (zv o i) (fun x => h (upd x i c)) := by
  rcases a with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · exact .inl ⟨c0, fun x => hc _⟩
  · refine ((L_meta_185_aux.restrict φ i c).mono (fun k => ?_)).congr (fun x => by rw [he])
    simp only [zv]; split_ifs <;> simp [ho k]

theorem Ach.upd_inv {o : Vec} {h : (Fin 5 → Bool) → Bool} (a : Ach o h) (i : Fin 5)
    (hi : o i = 0) (x : Fin 5 → Bool) (c : Bool) : h (upd x i c) = h x := by
  rcases a with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · rw [hc, hc]
  · rw [← he, ← he, eval_upd_of_zero φ i (by have := ho i; omega)]


def KM (i : Fin 5) (o : Vec) (h : (Fin 5 → Bool) → Bool) : Prop :=
  Ach (dv o i) h ∨ ∃ c j, j ≠ i ∧ 1 ≤ o j ∧ Ach (dv (zv o i) j) (fun x => h (upd x i c))

theorem KM.congr {i : Fin 5} {o o' : Vec} {h h' : (Fin 5 → Bool) → Bool} (eo : ∀ k, o k = o' k)
    (eh : ∀ x, h x = h' x) (a : KM i o h) : KM i o' h' := by
  obtain rfl : o = o' := funext eo
  obtain rfl : h = h' := funext eh
  exact a

theorem km_step (i : Fin 5) (g : Bool) (A B : DMFormula 5) (hA : 1 ≤ occ A i)
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

theorem kill_multi (i : Fin 5) (φ : DMFormula 5) :
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

def KS (i : Fin 5) (o : Vec) (h : (Fin 5 → Bool) → Bool) : Prop :=
  (∃ j, j ≠ i ∧ 1 ≤ o j ∧ ∃ g si sj : Bool, ∃ ψ : DMFormula 5, (∀ k, occ ψ k ≤ dv o j k) ∧
      ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i)) (litv sj (x j))))) ∨
  (∃ c j k, j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ 1 ≤ o j ∧ 1 ≤ o k ∧ (j ≠ k ∨ 2 ≤ o j) ∧
      Ach (dv (dv (zv o i) j) k) (fun x => h (upd x i c)))

theorem KS.congr {i : Fin 5} {o o' : Vec} {h h' : (Fin 5 → Bool) → Bool} (eo : ∀ k, o k = o' k)
    (eh : ∀ x, h x = h' x) (a : KS i o h) : KS i o' h' := by
  obtain rfl : o = o' := funext eo
  obtain rfl : h = h' := funext eh
  exact a

theorem two_leaves (i : Fin 5) (C D : DMFormula 5) (hC : occ C i = 0) (hD : occ D i = 0) :
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

theorem ks_step (i : Fin 5) (g : Bool) (A B : DMFormula 5) (hA : occ A i = 1) (hB0 : occ B i = 0)
    (ihA : (∃ s, A = .lit i s) ∨ KS i (occ A) A.eval) :
    KS i (fun k => occ A k + occ B k) (fun x => bop g (A.eval x) (B.eval x)) := by
  rcases ihA with ⟨si, rfl⟩ | hk
  · have kill2 : ∀ C D : DMFormula 5, occ C i = 0 → occ D i = 0 →
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

theorem kill_single (i : Fin 5) (φ : DMFormula 5) :
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

def code (x : Fin 5 → Bool) : ℕ :=
  Nat.bit (x 0) (Nat.bit (x 1) (Nat.bit (x 2) (Nat.bit (x 3) (Nat.bit (x 4) (0)))))

def ev (T : ℕ) (x : Fin 5 → Bool) : Bool := T.testBit (code x)

def M : ℕ := 4294967295

def vt : Fin 5 → ℕ := ![2863311530, 3435973836, 4042322160, 4278255360, 4294901760]

theorem allx {P : (Fin 5 → Bool) → Prop}
    (h : ∀ b0 b1 b2 b3 b4 : Bool, P ![b0, b1, b2, b3, b4]) (x : Fin 5 → Bool) : P x := by
  have e : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext k; fin_cases k <;> rfl
  rw [e]; exact h _ _ _ _ _

theorem code_lt : ∀ x, code x < 32 := allx (by decide +kernel)

def setIdx (a : ℕ) (i : Fin 5) (c : Bool) : ℕ :=
  if c then (if a.testBit i then a else 2 ^ (i : ℕ) + a)
  else (if a.testBit i then a - 2 ^ (i : ℕ) else a)

theorem code_upd (i : Fin 5) (c : Bool) : ∀ x, code (upd x i c) = setIdx (code x) i c := by
  fin_cases i <;> cases c <;> exact allx (by decide +kernel)

def rst (g : ℕ) (i : Fin 5) (c : Bool) : ℕ :=
  if c then (g &&& vt i) ||| ((g &&& vt i) >>> 2 ^ (i : ℕ))
  else (g &&& (M ^^^ vt i)) ||| ((g &&& (M ^^^ vt i)) <<< 2 ^ (i : ℕ))

theorem facts_t : ∀ i : Fin 5, ∀ a < 32,
    ((vt i).testBit a = true → setIdx a i true = a ∧ (vt i).testBit (2 ^ (i : ℕ) + a) = false) ∧
    ((vt i).testBit a = false →
      setIdx a i true = 2 ^ (i : ℕ) + a ∧ (vt i).testBit (2 ^ (i : ℕ) + a) = true) := by
  decide +kernel

theorem facts_f : ∀ i : Fin 5, ∀ a < 32,
    ((vt i).testBit a = true → setIdx a i false = a - 2 ^ (i : ℕ) ∧ 2 ^ (i : ℕ) ≤ a ∧
      (M ^^^ vt i).testBit a = false ∧ (M ^^^ vt i).testBit (a - 2 ^ (i : ℕ)) = true) ∧
    ((vt i).testBit a = false → setIdx a i false = a ∧ (M ^^^ vt i).testBit a = true ∧
      (decide (a ≥ 2 ^ (i : ℕ)) && (M ^^^ vt i).testBit (a - 2 ^ (i : ℕ))) = false) := by
  decide +kernel

theorem rst_bit (g : ℕ) (i : Fin 5) (c : Bool) (a : ℕ) (ha : a < 32) :
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

theorem ev_rst (g : ℕ) (i : Fin 5) (c : Bool) (x : Fin 5 → Bool) :
    ev (rst g i c) x = ev g (upd x i c) := by
  unfold ev
  rw [rst_bit _ _ _ _ (code_lt x), code_upd]

theorem ev_and (A B : ℕ) (x : Fin 5 → Bool) : ev (A &&& B) x = (ev A x && ev B x) :=
  Nat.testBit_and _ _ _

theorem ev_or (A B : ℕ) (x : Fin 5 → Bool) : ev (A ||| B) x = (ev A x || ev B x) :=
  Nat.testBit_or _ _ _

theorem ev_xor (A B : ℕ) (x : Fin 5 → Bool) : ev (A ^^^ B) x = (ev A x ^^ ev B x) :=
  Nat.testBit_xor _ _ _

theorem ev_zero (x : Fin 5 → Bool) : ev 0 x = false := Nat.zero_testBit _

theorem ev_M : ∀ x, ev M x = true := allx (by decide +kernel)

theorem ev_vt (i : Fin 5) : ∀ x, ev (vt i) x = x i := by
  fin_cases i <;> exact allx (by decide +kernel)

def cT (b : Bool) : ℕ := if b then M else 0

def litT (j : Fin 5) (s : Bool) : ℕ := if s then vt j else M ^^^ vt j

def opT (g : Bool) (a b : ℕ) : ℕ := if g then a ||| b else a &&& b

theorem ev_cT (b : Bool) (x : Fin 5 → Bool) : ev (cT b) x = b := by
  cases b
  · exact ev_zero x
  · exact ev_M x

theorem ev_litT (j : Fin 5) (s : Bool) (x : Fin 5 → Bool) : ev (litT j s) x = litv s (x j) := by
  cases s <;> simp [litT, litv, ev_xor, ev_M, ev_vt]

theorem ev_opT (g : Bool) (A B : ℕ) (x : Fin 5 → Bool) :
    ev (opT g A B) x = bop g (ev A x) (ev B x) := by
  cases g <;> simp [opT, bop, ev_and, ev_or]

def cnd (i j : Fin 5) (g si sj b : Bool) : ℕ := M ^^^ (opT g (cT (litv si b)) (litT j sj) ^^^ vt i)

theorem ev_cnd (i j : Fin 5) (g si sj b : Bool) (z : Fin 5 → Bool) :
    ev (cnd i j g si sj b) z = !(bop g (litv si b) (litv sj (z j)) ^^ z i) := by
  simp only [cnd, ev_xor, ev_M, ev_opT, ev_cT, ev_litT, ev_vt, Bool.true_xor]

def absLo (lo : ℕ) (i j : Fin 5) (g si sj : Bool) : ℕ :=
  (cnd i j g si sj false &&& rst lo i false) ||| (cnd i j g si sj true &&& rst lo i true)

def absHi (hi : ℕ) (i j : Fin 5) (g si sj : Bool) : ℕ :=
  M ^^^ ((cnd i j g si sj false &&& (M ^^^ rst hi i false)) |||
    (cnd i j g si sj true &&& (M ^^^ rst hi i true)))

def InIv (lo hi : ℕ) (h : (Fin 5 → Bool) → Bool) : Prop :=
  ∀ x, (ev lo x = true → h x = true) ∧ (h x = true → ev hi x = true)

def Bad (lo hi : ℕ) (o : Vec) : Prop := ∀ h, InIv lo hi h → ¬ Ach o h

theorem code_dec : ∀ a < 32, code (fun k : Fin 5 => a.testBit k) = a := by decide +kernel

theorem exists_x (T : ℕ) (hT : T &&& M ≠ 0) : ∃ x, ev T x = true := by
  obtain ⟨a, ha⟩ := Nat.exists_testBit_of_ne_zero hT
  rw [Nat.testBit_and, Bool.and_eq_true] at ha
  have ha64 : a < 32 := by
    by_contra hc
    push Not at hc
    have hM : M < 2 ^ a :=
      lt_of_lt_of_le (by decide : M < 2 ^ 32) (Nat.pow_le_pow_right (by norm_num) hc)
    rw [Nat.testBit_lt_two_pow hM] at ha
    exact absurd ha.2 (by simp)
  exact ⟨fun k => a.testBit k, by unfold ev; rw [code_dec a ha64]; exact ha.1⟩

theorem InIv.rst' {lo hi : ℕ} {h : (Fin 5 → Bool) → Bool} (hI : InIv lo hi h) (i : Fin 5)
    (c : Bool) : InIv (rst lo i c) (rst hi i c) (fun x => h (upd x i c)) := fun x => by
  rw [ev_rst, ev_rst]; exact hI _

theorem InIv.abs {lo hi : ℕ} {h : (Fin 5 → Bool) → Bool} (hI : InIv lo hi h) {i j : Fin 5}
    (hji : j ≠ i) {g si sj : Bool} {ψ : DMFormula 5}
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

def F6 : List (Fin 5) := [0, 1, 2, 3, 4]

def BB : List Bool := [false, true]

theorem mem_F6 (j : Fin 5) : j ∈ F6 := by fin_cases j <;> simp [F6]

theorem mem_BB (b : Bool) : b ∈ BB := by cases b <;> simp [BB]

def nstep (o : Vec) (p : ℕ × ℕ) (i : Fin 5) : ℕ × ℕ :=
  if o i = 0 then (rst p.1 i false ||| rst p.1 i true, rst p.2 i false &&& rst p.2 i true) else p

def nrm (lo hi : ℕ) (o : Vec) : ℕ × ℕ := F6.foldl (nstep o) (lo, hi)

theorem nstep_ok {o : Vec} {h : (Fin 5 → Bool) → Bool} (hA : Ach o h) (p : ℕ × ℕ) (i : Fin 5)
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

theorem nrm_ok {o : Vec} {h : (Fin 5 → Bool) → Bool} {lo hi : ℕ} (hA : Ach o h)
    (hI : InIv lo hi h) : InIv (nrm lo hi o).1 (nrm lo hi o).2 h := by
  unfold nrm
  suffices ∀ (l : List (Fin 5)) (p : ℕ × ℕ), InIv p.1 p.2 h →
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

theorem bad1 {lo hi : ℕ} {o : Vec} (i : Fin 5) (c : Bool)
    (hb : Bad (rst lo i c) (rst hi i c) (zv o i)) : Bad lo hi o :=
  fun h hI hA => hb _ (hI.rst' i c) (hA.restrict i c)

def kids2 (lo hi : ℕ) (o : Vec) (i : Fin 5) : List (ℕ × ℕ × Vec) :=
  (lo, hi, dv o i) :: BB.flatMap (fun c => (F6.filter (fun j => decide (j ≠ i ∧ 1 ≤ o j))).map
    (fun j => (rst lo i c, rst hi i c, dv (zv o i) j)))

theorem mem_kids2 {lo hi : ℕ} {o : Vec} {i j : Fin 5} (c : Bool) (hji : j ≠ i) (hj : 1 ≤ o j) :
    (rst lo i c, rst hi i c, dv (zv o i) j) ∈ kids2 lo hi o i := by
  simp only [kids2, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact .inr ⟨c, mem_BB c, j, ⟨mem_F6 j, decide_eq_true ⟨hji, hj⟩⟩, rfl⟩

theorem bad2 {lo hi : ℕ} {o : Vec} {i : Fin 5} (h2 : 2 ≤ o i)
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

def litok (lo hi : ℕ) (i : Fin 5) : Bool := !litin lo hi (litT i true) && !litin lo hi (litT i false)

theorem litin_of {lo hi t : ℕ} {h : (Fin 5 → Bool) → Bool} (hI : InIv lo hi h)
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

def kids3 (lo hi : ℕ) (o : Vec) (i : Fin 5) : List (ℕ × ℕ × Vec) :=
  (lo, hi, zv o i) ::
  ((F6.filter (fun j => decide (j ≠ i ∧ 1 ≤ o j))).flatMap (fun j => BB.flatMap (fun g =>
    BB.flatMap (fun si => BB.map (fun sj =>
      (absLo lo i j g si sj, absHi hi i j g si sj, dv o j))))) ++
  BB.flatMap (fun c => F6.flatMap (fun j => (F6.filter (fun k =>
    decide (j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ 1 ≤ o j ∧ 1 ≤ o k ∧ (j ≠ k ∨ 2 ≤ o j)))).map
      (fun k => (rst lo i c, rst hi i c, dv (dv (zv o i) j) k)))))

theorem mem_kids3_abs {lo hi : ℕ} {o : Vec} {i j : Fin 5} (g si sj : Bool) (hji : j ≠ i)
    (hj : 1 ≤ o j) : (absLo lo i j g si sj, absHi hi i j g si sj, dv o j) ∈ kids3 lo hi o i := by
  simp only [kids3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inl ⟨j, ⟨mem_F6 j, decide_eq_true ⟨hji, hj⟩⟩, g, mem_BB g, si, mem_BB si, sj,
    mem_BB sj, rfl⟩)

theorem mem_kids3_kill {lo hi : ℕ} {o : Vec} {i j k : Fin 5} (c : Bool) (hji : j ≠ i)
    (hki : k ≠ i) (hjk : j ≤ k) (hj : 1 ≤ o j) (hk : 1 ≤ o k) (hjk2 : j ≠ k ∨ 2 ≤ o j) :
    (rst lo i c, rst hi i c, dv (dv (zv o i) j) k) ∈ kids3 lo hi o i := by
  simp only [kids3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inr ⟨c, mem_BB c, j, mem_F6 j, k,
    ⟨mem_F6 k, decide_eq_true ⟨hji, hki, hjk, hj, hk, hjk2⟩⟩, rfl⟩)

theorem bad3 {lo hi : ℕ} {o : Vec} {i : Fin 5} (h1 : o i = 1) (hlit : litok lo hi i = true)
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
    else if hi6 : cert / 8 % 8 < 5 then
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
    split_ifs at h with t0 z hi6 t1 t2 h2 t3 h3
    · exact bad0 z
    · exact bad1 _ _ (chk_ok n _ _ _ _ _ h)
    · exact bad2 h2 (IH _ _ _ h)
    · exact bad3 h3.1 h3.2 (IH _ _ _ h)

def fT : ℕ := 4293454568

def certN : ℕ := 638001440620422643085427208515441686014682325257670128806141109863512343507474170847767770518107407034467158705227444940395590146898560385509217142646850917971901089728645923426249758611271579419334445492067735033976388341658344498113411144101820179171509724671083928419542350681208101949392440874995015100484801391664538803758463494121950493928003145639994792640378349504692872196803779824956443918814244307511615605955423580488351184445272234439874974602172599883390994821603433087447501834559256745084286777044132845534249352194703322440628773264589497409122771944856998961135144785078286263945039655399747679511977962183272666387505690607199506782953169312967478996103364232503996176594495839380506058600832118778471871767830762658225985976396940488541526041813516837947941425889699093584475215626304520246957725645091454058911853837480822030839399433

def topsL : List (List ℕ) := [[1, 1, 1, 1, 3], [1, 1, 1, 2, 2], [1, 1, 1, 3, 1], [1, 1, 2, 1, 2], [1, 1, 2, 2, 1], [1, 1, 3, 1, 1], [1, 2, 1, 1, 2], [1, 2, 1, 2, 1], [1, 2, 2, 1, 1], [1, 3, 1, 1, 1], [2, 1, 1, 1, 2], [2, 1, 1, 2, 1], [2, 1, 2, 1, 1], [2, 2, 1, 1, 1], [3, 1, 1, 1, 1]]

def vecOf (l : List ℕ) : Vec := fun k => l.getD (k : ℕ) 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tops_run :
    chkAll (chk 30) (topsL.map (fun l => (fT, fT, vecOf l))) certN = some 0 := by
  decide +kernel

theorem tops_bad : ∀ l ∈ topsL, Bad fT fT (vecOf l) := by
  intro l hl
  obtain ⟨_, _, e⟩ := chkAll_ok _ _ _ _ tops_run (fT, fT, vecOf l) (List.mem_map.2 ⟨l, hl, rfl⟩)
  exact chk_ok _ _ _ _ _ _ e

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tops_cover : ∀ a0 < 4, ∀ a1 < 4, ∀ a2 < 4, ∀ a3 < 4, ∀ a4 < 4,
    ¬ (1 ≤ a0 ∧ 1 ≤ a1 ∧ 1 ≤ a2 ∧ 1 ≤ a3 ∧ 1 ≤ a4 ∧ a0 + a1 + a2 + a3 + a4 = 7) ∨
    [a0, a1, a2, a3, a4] ∈ topsL := by
  decide +kernel

def fn (x : Fin 5 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4)

theorem ev_fT : ∀ x, ev fT x = fn x := allx (by decide +kernel)

def up : DMFormula 5 := (.or (.or (.and (.lit 0 true) (.or (.or (.lit 1 true) (.lit 2 true)) (.lit 3 true))) (.and (.lit 1 true) (.lit 2 true))) (.and (.lit 3 true) (.lit 4 true)))

theorem up_leaves : up.leaves ≤ 8 := by decide

theorem up_eval : ∀ x, up.eval x = fn x := allx (by decide +kernel)

theorem dep (k : Fin 5) : ∃ x c, fn (upd x k c) ≠ fn x := by
  fin_cases k
  · exact ⟨![false, true, false, false, false], true, by decide⟩
  · exact ⟨![true, false, false, false, false], true, by decide⟩
  · exact ⟨![true, false, false, false, false], true, by decide⟩
  · exact ⟨![true, false, false, false, false], true, by decide⟩
  · exact ⟨![false, false, false, true, false], true, by decide⟩

theorem lower (φ : DMFormula 5) (hl : φ.leaves ≤ 7) (he : ∀ x, φ.eval x = fn x) : False := by
  have hpos : ∀ k, 1 ≤ occ φ k := by
    intro k
    by_contra hk
    obtain ⟨x, c, hx⟩ := dep k
    apply hx
    rw [← he, ← he, eval_upd_of_zero φ k (by omega)]
  rw [leaves_eq, Fin.sum_univ_five] at hl
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  have h3 := hpos 3
  have h4 := hpos 4
  have mem := tops_cover (7 - (occ φ 1 + occ φ 2 + occ φ 3 + occ φ 4)) (by omega)
    (occ φ 1) (by omega) (occ φ 2) (by omega) (occ φ 3) (by omega) (occ φ 4) (by omega)
    |>.resolve_left (not_not.2 ⟨by omega, h1, h2, h3, h4, by omega⟩)
  refine tops_bad _ mem fn (fun x => by rw [ev_fT]; exact ⟨id, id⟩) (.inr ⟨φ, he, fun k => ?_⟩)
  fin_cases k
  · show occ φ 0 ≤ 7 - (occ φ 1 + occ φ 2 + occ φ 3 + occ φ 4); omega
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

end PEqualNP.Outside.L_meta_185_aux

theorem PEqualNP.Outside.L_meta_185 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4)) s ↔ 8 ≤ s := by
  intro s
  constructor
  · rintro ⟨φ, hl, he⟩
    by_contra h
    exact PEqualNP.Outside.L_meta_185_aux.lower φ (by omega) he
  · intro h
    exact ⟨PEqualNP.Outside.L_meta_185_aux.up, (le_trans PEqualNP.Outside.L_meta_185_aux.up_leaves h), PEqualNP.Outside.L_meta_185_aux.up_eval⟩
