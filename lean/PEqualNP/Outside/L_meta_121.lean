import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.DeMorganFormula

namespace PEqualNP.Outside.L_meta_121

open PEqualNP.MetaComplexity

def occ {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit j _ => if j = i then 1 else 0
  | .and a b => occ i a + occ i b
  | .or a b => occ i a + occ i b

def rs {n : ℕ} (i : Fin n) (c : Bool) : DMFormula n → Bool ⊕ DMFormula n
  | .lit j b => if j = i then Sum.inl (if b then c else !c) else Sum.inr (.lit j b)
  | .and a b =>
    match rs i c a, rs i c b with
    | .inl false, _ => .inl false
    | .inl true, r => r
    | .inr _, .inl false => .inl false
    | .inr p, .inl true => .inr p
    | .inr p, .inr q => .inr (.and p q)
  | .or a b =>
    match rs i c a, rs i c b with
    | .inl true, _ => .inl true
    | .inl false, r => r
    | .inr _, .inl true => .inl true
    | .inr p, .inl false => .inr p
    | .inr p, .inr q => .inr (.or p q)

def ev {n : ℕ} (r : Bool ⊕ DMFormula n) (x : Fin n → Bool) : Bool :=
  match r with
  | .inl v => v
  | .inr p => p.eval x

def sz {n : ℕ} (r : Bool ⊕ DMFormula n) : ℕ :=
  match r with
  | .inl _ => 0
  | .inr p => p.leaves

lemma leaves_pos {n : ℕ} (φ : DMFormula n) : 1 ≤ φ.leaves := by
  induction φ with
  | lit => simp [DMFormula.leaves]
  | and a b iha ihb => simp only [DMFormula.leaves]; omega
  | or a b iha ihb => simp only [DMFormula.leaves]; omega

lemma occ_le {n : ℕ} (i : Fin n) (φ : DMFormula n) : occ i φ ≤ φ.leaves := by
  induction φ with
  | lit j b => simp only [occ, DMFormula.leaves]; split <;> omega
  | and a b iha ihb => simp only [occ, DMFormula.leaves]; omega
  | or a b iha ihb => simp only [occ, DMFormula.leaves]; omega

lemma rs_eval {n : ℕ} (i : Fin n) (c : Bool) (φ : DMFormula n) (x : Fin n → Bool)
    (hx : x i = c) : ev (rs i c φ) x = φ.eval x := by
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · subst h; cases b <;> simp [rs, ev, DMFormula.eval, hx]
    · simp [rs, ev, DMFormula.eval, h]
  | and a b iha ihb =>
    rcases ha : rs i c a with (_ | _) | p <;> rcases hb : rs i c b with (_ | _) | q <;>
      simp_all [rs, ev, DMFormula.eval]
  | or a b iha ihb =>
    rcases ha : rs i c a with (_ | _) | p <;> rcases hb : rs i c b with (_ | _) | q <;>
      simp_all [rs, ev, DMFormula.eval]

lemma rs_sz {n : ℕ} (i : Fin n) (c : Bool) (φ : DMFormula n) :
    sz (rs i c φ) + occ i φ ≤ φ.leaves := by
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · subst h; simp [rs, sz, occ, DMFormula.leaves]
    · simp [rs, sz, occ, DMFormula.leaves, h]
  | and a b iha ihb =>
    have h1 := occ_le i a
    have h2 := occ_le i b
    rcases ha : rs i c a with (_ | _) | p <;> rcases hb : rs i c b with (_ | _) | q <;>
      simp_all [rs, sz, occ, DMFormula.leaves] <;> omega
  | or a b iha ihb =>
    have h1 := occ_le i a
    have h2 := occ_le i b
    rcases ha : rs i c a with (_ | _) | p <;> rcases hb : rs i c b with (_ | _) | q <;>
      simp_all [rs, sz, occ, DMFormula.leaves] <;> omega

lemma rs_sz_le {n : ℕ} (i : Fin n) (c : Bool) (φ : DMFormula n) :
    sz (rs i c φ) ≤ φ.leaves := by
  have := rs_sz i c φ; omega

lemma rs_and_sz {n : ℕ} (i : Fin n) (c : Bool) (a b : DMFormula n) :
    sz (rs i c (.and a b)) ≤ sz (rs i c a) + sz (rs i c b) := by
  rcases ha : rs i c a with (_ | _) | p <;> rcases hb : rs i c b with (_ | _) | q <;>
    simp_all [rs, sz, DMFormula.leaves]

lemma rs_or_sz {n : ℕ} (i : Fin n) (c : Bool) (a b : DMFormula n) :
    sz (rs i c (.or a b)) ≤ sz (rs i c a) + sz (rs i c b) := by
  rcases ha : rs i c a with (_ | _) | p <;> rcases hb : rs i c b with (_ | _) | q <;>
    simp_all [rs, sz, DMFormula.leaves]

lemma save {n : ℕ} (i : Fin n) (φ : DMFormula n) (h : occ i φ ≠ 0) (v : Bool) :
    ∃ c, rs i c φ = .inl v ∨ sz (rs i c φ) + 2 ≤ φ.leaves := by
  induction φ generalizing v with
  | lit j b =>
    by_cases hj : j = i
    · subst hj
      refine ⟨if b then v else !v, Or.inl ?_⟩
      cases b <;> cases v <;> simp [rs]
    · simp [occ, hj] at h
  | and a b iha ihb =>
    refine Or.elim (show occ i a ≠ 0 ∨ occ i b ≠ 0 by simp only [occ] at h; omega) ?_ ?_
    · intro ha0
      obtain ⟨c, hc⟩ := iha ha0 false
      refine ⟨c, Or.inr ?_⟩
      rcases hc with hc | hc
      · have : rs i c (.and a b) = .inl false := by simp [rs, hc]
        rw [this]; have := leaves_pos a; have := leaves_pos b
        simp only [sz, DMFormula.leaves]; omega
      · have := rs_and_sz i c a b; have := rs_sz_le i c b
        simp only [DMFormula.leaves]; omega
    · intro hb0
      obtain ⟨c, hc⟩ := ihb hb0 false
      refine ⟨c, Or.inr ?_⟩
      rcases hc with hc | hc
      · have : rs i c (.and a b) = .inl false := by
          rcases ha : rs i c a with (_ | _) | p <;> simp [rs, ha, hc]
        rw [this]; have := leaves_pos a; have := leaves_pos b
        simp only [sz, DMFormula.leaves]; omega
      · have := rs_and_sz i c a b; have := rs_sz_le i c a
        simp only [DMFormula.leaves]; omega
  | or a b iha ihb =>
    refine Or.elim (show occ i a ≠ 0 ∨ occ i b ≠ 0 by simp only [occ] at h; omega) ?_ ?_
    · intro ha0
      obtain ⟨c, hc⟩ := iha ha0 true
      refine ⟨c, Or.inr ?_⟩
      rcases hc with hc | hc
      · have : rs i c (.or a b) = .inl true := by simp [rs, hc]
        rw [this]; have := leaves_pos a; have := leaves_pos b
        simp only [sz, DMFormula.leaves]; omega
      · have := rs_or_sz i c a b; have := rs_sz_le i c b
        simp only [DMFormula.leaves]; omega
    · intro hb0
      obtain ⟨c, hc⟩ := ihb hb0 true
      refine ⟨c, Or.inr ?_⟩
      rcases hc with hc | hc
      · have : rs i c (.or a b) = .inl true := by
          rcases ha : rs i c a with (_ | _) | p <;> simp [rs, ha, hc]
        rw [this]; have := leaves_pos a; have := leaves_pos b
        simp only [sz, DMFormula.leaves]; omega
      · have := rs_or_sz i c a b; have := rs_sz_le i c a
        simp only [DMFormula.leaves]; omega

lemma indep {n : ℕ} (j : Fin n) (φ : DMFormula n) (h : occ j φ = 0) (x y : Fin n → Bool)
    (hxy : ∀ k, k ≠ j → x k = y k) : φ.eval x = φ.eval y := by
  induction φ with
  | lit i b =>
    have : i ≠ j := by intro e; simp [occ, e] at h
    simp [DMFormula.eval, hxy i this]
  | and a b iha ihb =>
    simp only [occ] at h
    simp only [DMFormula.eval, iha (by omega), ihb (by omega)]
  | or a b iha ihb =>
    simp only [occ] at h
    simp only [DMFormula.eval, iha (by omega), ihb (by omega)]

def Fp {n : ℕ} (m : ℕ) (x : Fin n → Bool) : Prop :=
  ∃ i j : Fin n, i.val + 1 = j.val ∧ j.val < m ∧ x i = true ∧ x j = true

def mk {n : ℕ} (m : ℕ) (z T : ℕ → Bool) : Fin n → Bool :=
  fun j => if j.val < m then T j.val else z j.val

lemma mk_tail {n m : ℕ} (z T : ℕ → Bool) : ∀ j : Fin n, m ≤ j.val → mk m z T j = z j.val := by
  intro j hj
  simp [mk, show ¬ j.val < m by omega]

lemma mk_lt {n m : ℕ} (z T : ℕ → Bool) (j : Fin n) (hj : j.val < m) : mk m z T j = T j.val := by
  simp [mk, hj]

lemma Fp_mk {n m : ℕ} (hmn : m ≤ n) (z T : ℕ → Bool) :
    Fp m (mk (n := n) m z T) ↔ ∃ k, k + 1 < m ∧ T k = true ∧ T (k + 1) = true := by
  constructor
  · rintro ⟨i, j, h1, h2, h3, h4⟩
    refine ⟨i.val, by omega, ?_, ?_⟩
    · rw [mk_lt z T i (by omega)] at h3; exact h3
    · rw [mk_lt z T j h2] at h4; rw [h1]; exact h4
  · rintro ⟨k, hk, h3, h4⟩
    refine ⟨⟨k, by omega⟩, ⟨k + 1, by omega⟩, rfl, hk, ?_, ?_⟩
    · rw [mk_lt z T _ (by simp; omega)]; exact h3
    · rw [mk_lt z T _ hk]; exact h4

lemma Fp_drop {n m : ℕ} (h2 : 2 ≤ m) (hmn : m ≤ n) (x : Fin n → Bool)
    (hb : x ⟨m - 2, by omega⟩ = false) : Fp m x ↔ Fp (m - 2) x := by
  constructor
  · rintro ⟨i, j, h1, h3, h4, h5⟩
    have hj : j.val ≠ m - 2 := by
      intro e
      have : j = ⟨m - 2, by omega⟩ := Fin.ext e
      rw [this, hb] at h5; exact Bool.false_ne_true h5
    have hi : i.val ≠ m - 2 := by
      intro e
      have : i = ⟨m - 2, by omega⟩ := Fin.ext e
      rw [this, hb] at h4; exact Bool.false_ne_true h4
    exact ⟨i, j, h1, by omega, h4, h5⟩
  · rintro ⟨i, j, h1, h3, h4, h5⟩
    exact ⟨i, j, h1, by omega, h4, h5⟩

lemma dep {n m : ℕ} (z : ℕ → Bool) (ψ : DMFormula n) (j : Fin n) (T U : ℕ → Bool)
    (hTU : ∀ k, k ≠ j.val → T k = U k)
    (hT : ψ.eval (mk m z T) = false) (hU : ψ.eval (mk m z U) = true) : occ j ψ ≠ 0 := by
  intro h0
  have := indep j ψ h0 (mk m z T) (mk m z U) (by
    intro k hk
    simp only [mk]
    split
    · exact hTU _ (fun e => hk (Fin.ext e))
    · rfl)
  rw [this, hU] at hT
  exact Bool.noConfusion hT

lemma lower (n : ℕ) : ∀ m, ∀ (φ : DMFormula n) (z : ℕ → Bool), 2 ≤ m → m ≤ n →
    (∀ x : Fin n → Bool, (∀ j : Fin n, m ≤ j.val → x j = z j.val) →
      (φ.eval x = true ↔ Fp m x)) → m + m / 2 ≤ φ.leaves + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro φ z h2 hmn hφ
  have hev : ∀ T, φ.eval (mk m z T) = true ↔ ∃ k, k + 1 < m ∧ T k = true ∧ T (k + 1) = true := by
    intro T
    rw [hφ _ (mk_tail z T), Fp_mk hmn]
  have evF : ∀ T, (¬ ∃ k, k + 1 < m ∧ T k = true ∧ T (k + 1) = true) →
      φ.eval (mk m z T) = false := by
    intro T hT
    cases h : φ.eval (mk m z T)
    · rfl
    · exact absurd ((hev T).1 h) hT
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
  · have o0 : occ ⟨0, by omega⟩ φ ≠ 0 :=
      dep z φ _ (fun k => decide (k = 1)) (fun k => decide (k = 0 ∨ k = 1))
        (by intro k hk; simp at hk ⊢; omega)
        (evF _ (by rintro ⟨k, hk, h1, h4⟩; simp at h1 h4; omega))
        ((hev _).2 ⟨0, by omega, by simp, by simp⟩)
    have o1 : occ ⟨1, by omega⟩ φ ≠ 0 :=
      dep z φ _ (fun k => decide (k = 0)) (fun k => decide (k = 0 ∨ k = 1))
        (by intro k hk; simp at hk ⊢; omega)
        (evF _ (by rintro ⟨k, hk, h1, h4⟩; simp at h1 h4 <;> omega))
        ((hev _).2 ⟨0, by omega, by simp, by simp⟩)
    cases φ with
    | lit i b =>
      simp only [occ] at o0 o1
      split at o0 <;> split at o1 <;> simp_all [Fin.ext_iff]
    | and a b =>
      have := leaves_pos a; have := leaves_pos b; simp only [DMFormula.leaves]; omega
    | or a b =>
      have := leaves_pos a; have := leaves_pos b; simp only [DMFormula.leaves]; omega
  · let a : Fin n := ⟨m - 1, by omega⟩
    let b : Fin n := ⟨m - 2, by omega⟩
    have oa : occ a φ ≠ 0 :=
      dep z φ a (fun k => decide (k = m - 2)) (fun k => decide (k = m - 2 ∨ k = m - 1))
        (by intro k hk; simp [a] at hk ⊢; omega)
        (evF _ (by rintro ⟨k, hk, h1, h4⟩; simp at h1 h4; omega))
        ((hev _).2 ⟨m - 2, by omega, by simp, by simp; omega⟩)
    obtain ⟨c, hc⟩ := save a φ oa false
    let X2 : ℕ → Bool := fun k => decide (k = m - 1) && c
    let Y2 : ℕ → Bool := fun k => decide (k = m - 3 ∨ k = m - 2) || (decide (k = m - 1) && c)
    let X3 : ℕ → Bool := fun k => decide (k = m - 3) || (decide (k = m - 1) && c)
    have hX2 : φ.eval (mk m z X2) = false :=
      evF _ (by rintro ⟨k, hk, h1, h4⟩; cases c <;> simp [X2] at h1 h4 <;> omega)
    have hY2 : φ.eval (mk m z Y2) = true :=
      (hev _).2 ⟨m - 3, by omega, by simp [Y2], by simp [Y2]; omega⟩
    have hX3 : φ.eval (mk m z X3) = false :=
      evF _ (by rintro ⟨k, hk, h1, h4⟩; cases c <;> simp [X3] at h1 h4 <;> omega)
    have aX2 : mk m z X2 a = c := by rw [mk_lt z X2 a (by simp [a]; omega)]; simp [X2, a]
    have aY2 : mk m z Y2 a = c := by
      rw [mk_lt z Y2 a (by simp [a]; omega)]; cases c <;> simp [Y2, a] <;> omega
    have aX3 : mk m z X3 a = c := by
      rw [mk_lt z X3 a (by simp [a]; omega)]; cases c <;> simp [X3, a] <;> omega
    have key : ∃ ψ1, rs a c φ = .inr ψ1 := by
      rcases h : rs a c φ with w | ψ1
      · exfalso
        have e1 := rs_eval a c φ _ aX2
        have e2 := rs_eval a c φ _ aY2
        rw [h] at e1 e2
        simp only [ev] at e1 e2
        rw [hX2] at e1; rw [hY2] at e2
        rw [e1] at e2; exact Bool.noConfusion e2
      · exact ⟨ψ1, rfl⟩
    obtain ⟨ψ1, h1⟩ := key
    have hs1 : ψ1.leaves + 2 ≤ φ.leaves := by
      rcases hc with hc | hc
      · rw [h1] at hc; simp at hc
      · rw [h1] at hc; simpa [sz] using hc
    have hψ1 : ∀ x, x a = c → ψ1.eval x = φ.eval x := by
      intro x hx
      have := rs_eval a c φ x hx
      rw [h1] at this; exact this
    have ob : occ b ψ1 ≠ 0 :=
      dep z ψ1 b X3 Y2
        (by
          intro k hk
          have hk' : k ≠ m - 2 := hk
          cases c <;> simp only [X3, Y2] <;> by_cases h : k = m - 3 <;> simp [h, hk'])
        (by rw [hψ1 _ aX3]; exact hX3)
        (by rw [hψ1 _ aY2]; exact hY2)
    have hs2 := rs_sz b false ψ1
    rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | h4
    · have := occ_le b ψ1
      omega
    · rcases h2r : rs b false ψ1 with w | ψ2
      · exfalso
        let Y4 : ℕ → Bool := fun k => decide (k = 0 ∨ k = 1) || (decide (k = m - 1) && c)
        have hY4 : φ.eval (mk m z Y4) = true :=
          (hev _).2 ⟨0, by omega, by simp [Y4], by simp [Y4]⟩
        have aY4 : mk m z Y4 a = c := by
          rw [mk_lt z Y4 a (by simp [a]; omega)]; cases c <;> simp [Y4, a] <;> omega
        have bX2 : mk m z X2 b = false := by
          rw [mk_lt z X2 b (by simp [b]; omega)]; cases c <;> simp [X2, b] <;> omega
        have bY4 : mk m z Y4 b = false := by
          rw [mk_lt z Y4 b (by simp [b]; omega)]; cases c <;> simp [Y4, b] <;> omega
        have e1 := rs_eval b false ψ1 _ bX2
        have e2 := rs_eval b false ψ1 _ bY4
        rw [h2r] at e1 e2
        simp only [ev] at e1 e2
        rw [hψ1 _ aX2, hX2] at e1
        rw [hψ1 _ aY4, hY4] at e2
        rw [e1] at e2; exact Bool.noConfusion e2
      · let z' : ℕ → Bool := fun k => if k = m - 1 then c else if k = m - 2 then false else z k
        have hih := ih (m - 2) (by omega) ψ2 z' (by omega) (by omega) (by
          intro x hx
          have xb : x b = false := by
            rw [hx b (by simp [b])]; simp [z', b]; omega
          have xa : x a = c := by
            rw [hx a (by simp [a]; omega)]; simp [z', a]
          have xt : ∀ j : Fin n, m ≤ j.val → x j = z j.val := by
            intro j hj
            rw [hx j (by omega)]
            simp [z', show j.val ≠ m - 1 by omega, show j.val ≠ m - 2 by omega]
          have e := rs_eval b false ψ1 x xb
          rw [h2r] at e
          simp only [ev] at e
          rw [e, hψ1 x xa, hφ x xt]
          exact Fp_drop (by omega) hmn x xb)
        rw [h2r] at hs2
        simp only [sz] at hs2
        omega

def v {n : ℕ} (hn : 0 < n) (k : ℕ) : DMFormula n := .lit ⟨k % n, Nat.mod_lt _ hn⟩ true

def G {n : ℕ} (hn : 0 < n) : ℕ → DMFormula n
  | 0 => v hn 0
  | 1 => v hn 0
  | 2 => .and (v hn 0) (v hn 1)
  | 3 => .and (v hn 1) (.or (v hn 0) (v hn 2))
  | m + 4 => .or (G hn (m + 2)) (.and (v hn (m + 2)) (.or (v hn (m + 1)) (v hn (m + 3))))

lemma G_leaves {n : ℕ} (hn : 0 < n) : ∀ m, 2 ≤ m → (G hn m).leaves + 1 = m + m / 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro h2
  match m, h2 with
  | 2, _ => simp [G, v, DMFormula.leaves]
  | 3, _ => simp [G, v, DMFormula.leaves]
  | m + 4, _ =>
    have := ih (m + 2) (by omega) (by omega)
    simp only [G, v, DMFormula.leaves] at this ⊢
    omega

lemma Fp_v {n m : ℕ} (hn : 0 < n) (hmn : m ≤ n) (x : Fin n → Bool) :
    Fp m x ↔ ∃ k, k + 1 < m ∧ (v hn k).eval x = true ∧ (v hn (k + 1)).eval x = true := by
  simp only [v, DMFormula.eval, ite_true]
  constructor
  · rintro ⟨i, j, h1, h3, h4, h5⟩
    refine ⟨i.val, by omega, ?_, ?_⟩
    · have : (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      rw [this]; exact h4
    · have : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = j :=
        Fin.ext (by simp only; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      rw [this]; exact h5
  · rintro ⟨k, hk, h4, h5⟩
    refine ⟨⟨k % n, Nat.mod_lt _ hn⟩, ⟨(k + 1) % n, Nat.mod_lt _ hn⟩, ?_, ?_, h4, h5⟩
    · simp only; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    · simp only; rw [Nat.mod_eq_of_lt (by omega)]; exact hk

lemma G_eval {n : ℕ} (hn : 0 < n) : ∀ m, 2 ≤ m → m ≤ n → ∀ x : Fin n → Bool,
    ((G hn m).eval x = true ↔ Fp m x) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro h2 hmn x
  rw [Fp_v hn hmn x]
  match m, h2 with
  | 2, _ =>
    simp only [G, DMFormula.eval, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h3⟩; exact ⟨0, by omega, h1, h3⟩
    · rintro ⟨k, hk, h1, h3⟩
      obtain rfl : k = 0 := by omega
      exact ⟨h1, h3⟩
  | 3, _ =>
    simp only [G, DMFormula.eval, Bool.and_eq_true, Bool.or_eq_true]
    constructor
    · rintro ⟨h1, h3 | h3⟩
      · exact ⟨0, by omega, h3, h1⟩
      · exact ⟨1, by omega, h1, h3⟩
    · rintro ⟨k, hk, h1, h3⟩
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact ⟨h3, Or.inl h1⟩
      · exact ⟨h1, Or.inr h3⟩
  | m + 4, _ =>
    have hi := ih (m + 2) (by omega) (by omega) (by omega) x
    rw [Fp_v hn (by omega) x] at hi
    simp only [G, DMFormula.eval, Bool.and_eq_true, Bool.or_eq_true, hi]
    constructor
    · rintro (⟨k, hk, h1, h3⟩ | ⟨h1, h3 | h3⟩)
      · exact ⟨k, by omega, h1, h3⟩
      · exact ⟨m + 1, by omega, h3, h1⟩
      · exact ⟨m + 2, by omega, h1, h3⟩
    · rintro ⟨k, hk, h1, h3⟩
      rcases (show k + 1 < m + 2 ∨ k = m + 1 ∨ k = m + 2 by omega) with hk' | rfl | rfl
      · exact Or.inl ⟨k, hk', h1, h3⟩
      · exact Or.inr ⟨h3, Or.inl h1⟩
      · exact Or.inr ⟨h1, Or.inr h3⟩

end PEqualNP.Outside.L_meta_121

theorem PEqualNP.Outside.L_meta_121 : ∀ n s : ℕ, 2 ≤ n → (PEqualNP.MetaComplexity.HasLeafSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) s ↔ n + n / 2 ≤ s + 1) := by
  intro n s hn
  have conv : ∀ x : Fin n → Bool, (decide (∃ i j : Fin n, i.val + 1 = j.val ∧ x i = true ∧ x j = true) = true ↔ PEqualNP.Outside.L_meta_121.Fp n x) := by
    intro x
    simp only [decide_eq_true_eq, PEqualNP.Outside.L_meta_121.Fp]
    constructor
    · rintro ⟨i, j, h1, h2, h3⟩; exact ⟨i, j, h1, j.isLt, h2, h3⟩
    · rintro ⟨i, j, h1, _, h2, h3⟩; exact ⟨i, j, h1, h2, h3⟩
  constructor
  · rintro ⟨φ, hl, he⟩
    have := PEqualNP.Outside.L_meta_121.lower n n φ (fun _ => false) hn le_rfl
      (fun x _ => by rw [he x]; exact conv x)
    omega
  · intro h
    have hpos : 0 < n := by omega
    refine ⟨PEqualNP.Outside.L_meta_121.G hpos n, ?_, fun x => ?_⟩
    · have := PEqualNP.Outside.L_meta_121.G_leaves hpos n hn; omega
    · have := PEqualNP.Outside.L_meta_121.G_eval hpos n hn le_rfl x
      apply Bool.eq_iff_iff.mpr
      rw [this, conv x]
