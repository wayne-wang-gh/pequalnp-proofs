import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_383

open Turing PEqualNP.Library

lemma iterate_none {α : Type} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

lemma iter_trans {α : Type} (f : α → Option α) {n₁ n₂ : ℕ} {a b c : α}
    (h₁ : (flip bind f)^[n₁] (some a) = some b)
    (h₂ : (flip bind f)^[n₂] (some b) = some c) :
    (flip bind f)^[n₁ + n₂] (some a) = some c := by
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

lemma simulate {α β : Type} (f : α → Option α) (g : β → Option β) (emb : α → β)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : α), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (emb a)) = some (emb b) := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa : f a with
    | none =>
      have e : flip bind f (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab

def pushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

lemma stepAux_length {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_cons]; omega
    · rw [Function.update_of_ne h]; omega
  | peek _ _ _ ih => exact ih _ _
  | pop k' _ _ ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne h]
  | load _ _ ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · exact (ih₂ v S).trans (by have := le_max_right (pushes q₁) (pushes q₂); omega)
    · exact (ih₁ v S).trans (by have := le_max_left (pushes q₁) (pushes q₂); omega)
  | goto _ => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)

lemma step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : TM2.step tm.m c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have : pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f := fun l => pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this

lemma run_length (tm : FinTM2) (k : tm.K) :
    ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a) = some b →
      (b.stk k).length ≤ (a.stk k).length + maxPush tm * n := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; simp
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa : TM2.step tm.m a with
    | none =>
      have e : flip bind (TM2.step tm.m) (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step tm.m) (some a) = some c := hfa
      rw [e] at hab
      have h1 := ih c b hab
      have h2 := step_length tm a c hfa k
      rw [Nat.mul_succ]; omega

lemma initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

lemma haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

lemma out_len_le (tm : FinTM2) (l0 : List (tm.Γ tm.k₀)) (l1 : List (tm.Γ tm.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step tm.m))^[s] (some (initList tm l0)) = some (haltList tm l1)) :
    l1.length ≤ l0.length + maxPush tm * s := by
  have hlen := run_length tm tm.k₁ s _ _ h
  have h1 : (haltList tm l1).stk tm.k₁ = l1 := by rw [haltList_eq]; simp
  have h0 : ((initList tm l0).stk tm.k₁).length ≤ l0.length := by
    rw [initList_eq]
    by_cases hk : tm.k₁ = tm.k₀
    · rw [hk]; simp
    · simp [hk]
  rw [h1] at hlen
  omega

lemma eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

def cntFrom (P : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i, r + 1 => (if P i then 1 else 0) + cntFrom P (i + 1) r

lemma cntFrom_eq_range' (P : ℕ → Bool) :
    ∀ (r i : ℕ), cntFrom P i r = (List.range' i r).countP P := by
  intro r
  induction r with
  | zero =>
    intro i
    simp [cntFrom]
  | succ r ih =>
    intro i
    rw [List.range'_succ, List.countP_cons]
    simp only [cntFrom]
    rw [ih (i + 1)]
    omega

lemma cntFrom_zero (P : ℕ → Bool) (N : ℕ) :
    cntFrom P 0 N = (List.range N).countP P := by
  rw [List.range_eq_range', cntFrom_eq_range']

abbrev CK (Mc Ma Mp : FinTM2) : Type := Mc.K ⊕ Ma.K ⊕ Mp.K ⊕ Fin 6

abbrev CΓ (Mc Ma Mp : FinTM2) : CK Mc Ma Mp → Type
  | Sum.inl k => Mc.Γ k
  | Sum.inr (Sum.inl k) => Ma.Γ k
  | Sum.inr (Sum.inr (Sum.inl k)) => Mp.Γ k
  | Sum.inr (Sum.inr (Sum.inr _)) => Bool

abbrev CΛ (Mc Ma Mp : FinTM2) : Type := Mc.Λ ⊕ Ma.Λ ⊕ Mp.Λ ⊕ Fin 16

abbrev Cσ (Mc Ma Mp : FinTM2) : Type := Mc.σ × Ma.σ × Mp.σ × Option Bool

abbrev CCfg (Mc Ma Mp : FinTM2) : Type :=
  TM2.Cfg (CΓ Mc Ma Mp) (CΛ Mc Ma Mp) (Cσ Mc Ma Mp)

abbrev kI (Mc Ma Mp : FinTM2) : CK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr 0))
abbrev kO (Mc Ma Mp : FinTM2) : CK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr 1))
abbrev kRem (Mc Ma Mp : FinTM2) : CK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr 2))
abbrev kIdx (Mc Ma Mp : FinTM2) : CK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr 3))
abbrev kArg (Mc Ma Mp : FinTM2) : CK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr 4))
abbrev kTmp (Mc Ma Mp : FinTM2) : CK Mc Ma Mp := Sum.inr (Sum.inr (Sum.inr 5))

abbrev lbl (Mc Ma Mp : FinTM2) (j : Fin 16) : CΛ Mc Ma Mp :=
  Sum.inr (Sum.inr (Sum.inr j))

def trC {Mc Ma Mp : FinTM2} :
    TM2.Stmt Mc.Γ Mc.Λ Mc.σ → TM2.Stmt (CΓ Mc Ma Mp) (CΛ Mc Ma Mp) (Cσ Mc Ma Mp)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trC q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trC q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trC q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trC q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trC q₁) (trC q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => lbl Mc Ma Mp 2)

def trA {Mc Ma Mp : FinTM2} :
    TM2.Stmt Ma.Γ Ma.Λ Ma.σ → TM2.Stmt (CΓ Mc Ma Mp) (CΛ Mc Ma Mp) (Cσ Mc Ma Mp)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun s => f s.2.1) (trA q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (trA q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (trA q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (trA q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (trA q₁) (trA q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .goto (fun _ => lbl Mc Ma Mp 4)

def trP {Mc Ma Mp : FinTM2} :
    TM2.Stmt Mp.Γ Mp.Λ Mp.σ → TM2.Stmt (CΓ Mc Ma Mp) (CΛ Mc Ma Mp) (Cσ Mc Ma Mp)
  | .push k f q => .push (Sum.inr (Sum.inr (Sum.inl k))) (fun s => f s.2.2.1) (trP q)
  | .peek k f q =>
      .peek (Sum.inr (Sum.inr (Sum.inl k))) (fun s o => (s.1, s.2.1, f s.2.2.1 o, s.2.2.2)) (trP q)
  | .pop k f q =>
      .pop (Sum.inr (Sum.inr (Sum.inl k))) (fun s o => (s.1, s.2.1, f s.2.2.1 o, s.2.2.2)) (trP q)
  | .load a q => .load (fun s => (s.1, s.2.1, a s.2.2.1, s.2.2.2)) (trP q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.2.1) (trP q₁) (trP q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inr (Sum.inl (f s.2.2.1))))
  | .halt => .goto (fun _ => lbl Mc Ma Mp 11)

def ctrlProg (Mc Ma Mp : FinTM2)
    (ec₀ : Bool → Mc.Γ Mc.k₀)
    (ea₀ : Bool → Ma.Γ Ma.k₀) (ea₁ : Ma.Γ Ma.k₁ → Bool)
    (ep₀ : Bool → Mp.Γ Mp.k₀) :
    Fin 16 → TM2.Stmt (CΓ Mc Ma Mp) (CΛ Mc Ma Mp) (Cσ Mc Ma Mp)
  | ⟨0, _⟩ =>
      .pop (kI Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.push (kTmp Mc Ma Mp) (fun s => s.2.2.2.getD false)
            (.push (kArg Mc Ma Mp) (fun s => s.2.2.2.getD false)
              (.goto fun _ => lbl Mc Ma Mp 0)))
          (.goto fun _ => lbl Mc Ma Mp 1))
  | ⟨1, _⟩ =>
      .pop (kTmp Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.push (Sum.inl Mc.k₀) (fun s => ec₀ (s.2.2.2.getD false))
            (.goto fun _ => lbl Mc Ma Mp 1))
          (.goto fun _ => Sum.inl Mc.main))
  | ⟨2, _⟩ =>
      .pop (Sum.inl Mc.k₁) (fun s o => (s.1, s.2.1, s.2.2.1, o.map fun _ => true))
        (.branch (fun s => s.2.2.2.isSome)
          (.push (kRem Mc Ma Mp) (fun _ => true)
            (.goto fun _ => lbl Mc Ma Mp 2))
          (.goto fun _ => lbl Mc Ma Mp 3))
  | ⟨3, _⟩ =>
      .pop (kArg Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.push (Sum.inr (Sum.inl Ma.k₀)) (fun s => ea₀ (s.2.2.2.getD false))
            (.goto fun _ => lbl Mc Ma Mp 3))
          (.goto fun _ => Sum.inr (Sum.inl Ma.main)))
  | ⟨4, _⟩ =>
      .pop (Sum.inr (Sum.inl Ma.k₁)) (fun s o => (s.1, s.2.1, s.2.2.1, o.map ea₁))
        (.branch (fun s => s.2.2.2.isSome)
          (.push (kArg Mc Ma Mp) (fun s => s.2.2.2.getD false)
            (.goto fun _ => lbl Mc Ma Mp 4))
          (.goto fun _ => lbl Mc Ma Mp 5))
  | ⟨5, _⟩ =>
      .pop (kRem Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.goto fun _ => lbl Mc Ma Mp 6)
          (.goto fun _ => lbl Mc Ma Mp 14))
  | ⟨6, _⟩ =>
      .pop (kArg Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.push (Sum.inr (Sum.inr (Sum.inl Mp.k₀))) (fun s => ep₀ (s.2.2.2.getD false))
            (.push (kTmp Mc Ma Mp) (fun s => s.2.2.2.getD false)
              (.goto fun _ => lbl Mc Ma Mp 6)))
          (.goto fun _ => lbl Mc Ma Mp 7))
  | ⟨7, _⟩ =>
      .pop (kTmp Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.push (kArg Mc Ma Mp) (fun s => s.2.2.2.getD false)
            (.goto fun _ => lbl Mc Ma Mp 7))
          (.goto fun _ => lbl Mc Ma Mp 8))
  | ⟨8, _⟩ =>
      .pop (kIdx Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.push (Sum.inr (Sum.inr (Sum.inl Mp.k₀))) (fun s => ep₀ (s.2.2.2.getD false))
            (.push (kTmp Mc Ma Mp) (fun s => s.2.2.2.getD false)
              (.goto fun _ => lbl Mc Ma Mp 8)))
          (.goto fun _ => lbl Mc Ma Mp 9))
  | ⟨9, _⟩ =>
      .push (Sum.inr (Sum.inr (Sum.inl Mp.k₀))) (fun _ => ep₀ false)
        (.goto fun _ => lbl Mc Ma Mp 10)
  | ⟨10, _⟩ =>
      .pop (kTmp Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.push (Sum.inr (Sum.inr (Sum.inl Mp.k₀))) (fun s => ep₀ (s.2.2.2.getD false))
            (.push (kIdx Mc Ma Mp) (fun s => s.2.2.2.getD false)
              (.goto fun _ => lbl Mc Ma Mp 10)))
          (.goto fun _ => Sum.inr (Sum.inr (Sum.inl Mp.main))))
  | ⟨11, _⟩ =>
      .pop (Sum.inr (Sum.inr (Sum.inl Mp.k₁))) (fun s o => (s.1, s.2.1, s.2.2.1, o.map fun _ => true))
        (.branch (fun s => s.2.2.2.isSome)
          (.goto fun _ => lbl Mc Ma Mp 12)
          (.push (kIdx Mc Ma Mp) (fun _ => true)
            (.goto fun _ => lbl Mc Ma Mp 5)))
  | ⟨12, _⟩ =>
      .pop (Sum.inr (Sum.inr (Sum.inl Mp.k₁))) (fun s o => (s.1, s.2.1, s.2.2.1, o.map fun _ => true))
        (.branch (fun s => s.2.2.2.isSome)
          (.goto fun _ => lbl Mc Ma Mp 12)
          (.push (kO Mc Ma Mp) (fun _ => true)
            (.push (kIdx Mc Ma Mp) (fun _ => true)
              (.goto fun _ => lbl Mc Ma Mp 5))))
  | ⟨13, _⟩ =>
      .pop (kRem Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.goto fun _ => lbl Mc Ma Mp 13)
          (.goto fun _ => lbl Mc Ma Mp 14))
  | ⟨14, _⟩ =>
      .pop (kArg Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.goto fun _ => lbl Mc Ma Mp 14)
          (.goto fun _ => lbl Mc Ma Mp 15))
  | ⟨15, _⟩ =>
      .pop (kIdx Mc Ma Mp) (fun s o => (s.1, s.2.1, s.2.2.1, o))
        (.branch (fun s => s.2.2.2.isSome)
          (.goto fun _ => lbl Mc Ma Mp 15)
          .halt)
  | ⟨_ + 16, h⟩ => absurd h (by omega)

def compProg (Mc Ma Mp : FinTM2)
    (ec₀ : Bool → Mc.Γ Mc.k₀)
    (ea₀ : Bool → Ma.Γ Ma.k₀) (ea₁ : Ma.Γ Ma.k₁ → Bool)
    (ep₀ : Bool → Mp.Γ Mp.k₀) :
    CΛ Mc Ma Mp → TM2.Stmt (CΓ Mc Ma Mp) (CΛ Mc Ma Mp) (Cσ Mc Ma Mp)
  | Sum.inl l => trC (Mc.m l)
  | Sum.inr (Sum.inl l) => trA (Ma.m l)
  | Sum.inr (Sum.inr (Sum.inl l)) => trP (Mp.m l)
  | Sum.inr (Sum.inr (Sum.inr j)) => ctrlProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀ j

def compM (Mc Ma Mp : FinTM2)
    (ec₀ : Bool → Mc.Γ Mc.k₀)
    (ea₀ : Bool → Ma.Γ Ma.k₀) (ea₁ : Ma.Γ Ma.k₁ → Bool)
    (ep₀ : Bool → Mp.Γ Mp.k₀) : FinTM2 :=
  letI := Mc.kFin
  letI := Ma.kFin
  letI := Mp.kFin
  letI := Mc.ΛFin
  letI := Ma.ΛFin
  letI := Mp.ΛFin
  letI := Mc.σFin
  letI := Ma.σFin
  letI := Mp.σFin
  { K := CK Mc Ma Mp
    k₀ := kI Mc Ma Mp
    k₁ := kO Mc Ma Mp
    Γ := CΓ Mc Ma Mp
    Λ := CΛ Mc Ma Mp
    main := lbl Mc Ma Mp 0
    σ := Cσ Mc Ma Mp
    initialState := (Mc.initialState, Ma.initialState, Mp.initialState, none)
    Γk₀Fin := Bool.fintype
    m := compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀ }

def cstk {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool) : ∀ k, List (CΓ Mc Ma Mp k)
  | Sum.inl k => Sc k
  | Sum.inr (Sum.inl k) => Sa k
  | Sum.inr (Sum.inr (Sum.inl k)) => Sp k
  | Sum.inr (Sum.inr (Sum.inr ⟨0, _⟩)) => i
  | Sum.inr (Sum.inr (Sum.inr ⟨1, _⟩)) => o
  | Sum.inr (Sum.inr (Sum.inr ⟨2, _⟩)) => rem
  | Sum.inr (Sum.inr (Sum.inr ⟨3, _⟩)) => idx
  | Sum.inr (Sum.inr (Sum.inr ⟨4, _⟩)) => arg
  | Sum.inr (Sum.inr (Sum.inr ⟨5, _⟩)) => tmp

lemma cstk_nil {Mc Ma Mp : FinTM2} :
    (cstk (Mc := Mc) (Ma := Ma) (Mp := Mp)
      (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] [] [] []) = fun _ => [] := by
  funext k
  rcases k with k | (k | (k | ⟨j, hj⟩))
  · rfl
  · rfl
  · rfl
  · match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

lemma cstk_set_C {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool) (k : Mc.K) (x : List (Mc.Γ k)) :
    Function.update (cstk Sc Sa Sp i o rem idx arg tmp) (Sum.inl k) x =
      cstk (Function.update Sc k x) Sa Sp i o rem idx arg tmp := by
  funext j
  rcases j with j | (j | (j | ⟨j, hj⟩))
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update Sc j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Sc j = Function.update Sc k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

lemma cstk_set_A {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool) (k : Ma.K) (x : List (Ma.Γ k)) :
    Function.update (cstk Sc Sa Sp i o rem idx arg tmp) (Sum.inr (Sum.inl k)) x =
      cstk Sc (Function.update Sa k x) Sp i o rem idx arg tmp := by
  funext j
  rcases j with j | (j | (j | ⟨j, hj⟩))
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update Sa j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Sa j = Function.update Sa k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

lemma cstk_set_P {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool) (k : Mp.K) (x : List (Mp.Γ k)) :
    Function.update (cstk Sc Sa Sp i o rem idx arg tmp) (Sum.inr (Sum.inr (Sum.inl k))) x =
      cstk Sc Sa (Function.update Sp k x) i o rem idx arg tmp := by
  funext j
  rcases j with j | (j | (j | ⟨j, hj⟩))
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update Sp j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Sp j = Function.update Sp k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

lemma cstk_set_I {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp i' : List Bool) :
    Function.update (cstk Sc Sa Sp i o rem idx arg tmp) (kI Mc Ma Mp) i' =
      cstk Sc Sa Sp i' o rem idx arg tmp := by
  funext j
  rcases j with j | (j | (j | j))
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> simp [cstk]

lemma cstk_set_O {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp o' : List Bool) :
    Function.update (cstk Sc Sa Sp i o rem idx arg tmp) (kO Mc Ma Mp) o' =
      cstk Sc Sa Sp i o' rem idx arg tmp := by
  funext j
  rcases j with j | (j | (j | j))
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> simp [cstk]

lemma cstk_set_Rem {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp rem' : List Bool) :
    Function.update (cstk Sc Sa Sp i o rem idx arg tmp) (kRem Mc Ma Mp) rem' =
      cstk Sc Sa Sp i o rem' idx arg tmp := by
  funext j
  rcases j with j | (j | (j | j))
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> simp [cstk]

lemma cstk_set_Idx {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp idx' : List Bool) :
    Function.update (cstk Sc Sa Sp i o rem idx arg tmp) (kIdx Mc Ma Mp) idx' =
      cstk Sc Sa Sp i o rem idx' arg tmp := by
  funext j
  rcases j with j | (j | (j | j))
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> simp [cstk]

lemma cstk_set_Arg {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp arg' : List Bool) :
    Function.update (cstk Sc Sa Sp i o rem idx arg tmp) (kArg Mc Ma Mp) arg' =
      cstk Sc Sa Sp i o rem idx arg' tmp := by
  funext j
  rcases j with j | (j | (j | j))
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> simp [cstk]

lemma cstk_set_Tmp {Mc Ma Mp : FinTM2}
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp tmp' : List Bool) :
    Function.update (cstk Sc Sa Sp i o rem idx arg tmp) (kTmp Mc Ma Mp) tmp' =
      cstk Sc Sa Sp i o rem idx arg tmp' := by
  funext j
  rcases j with j | (j | (j | j))
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> simp [cstk]

lemma cstk_nil_I {Mc Ma Mp : FinTM2} (i : List Bool) :
    cstk (Mc := Mc) (Ma := Ma) (Mp := Mp)
      (fun _ => []) (fun _ => []) (fun _ => []) i [] [] [] [] [] =
      Function.update (fun _ => [] : ∀ k, List (CΓ Mc Ma Mp k)) (kI Mc Ma Mp) i :=
  (cstk_set_I (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] [] [] [] i).symm.trans
    (by rw [cstk_nil])

lemma cstk_nil_O {Mc Ma Mp : FinTM2} (o : List Bool) :
    cstk (Mc := Mc) (Ma := Ma) (Mp := Mp)
      (fun _ => []) (fun _ => []) (fun _ => []) [] o [] [] [] [] =
      Function.update (fun _ => [] : ∀ k, List (CΓ Mc Ma Mp k)) (kO Mc Ma Mp) o :=
  (cstk_set_O (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] [] [] [] o).symm.trans
    (by rw [cstk_nil])

def embC {Mc Ma Mp : FinTM2} (va : Ma.σ) (vp : Mp.σ) (b : Option Bool)
    (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool)
    (c : TM2.Cfg Mc.Γ Mc.Λ Mc.σ) : CCfg Mc Ma Mp :=
  ⟨some (c.l.elim (lbl Mc Ma Mp 2) Sum.inl), (c.var, va, vp, b),
    cstk c.stk Sa Sp i o rem idx arg tmp⟩

lemma stepAux_trC {Mc Ma Mp : FinTM2} (va : Ma.σ) (vp : Mp.σ) (b : Option Bool)
    (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool)
    (q : TM2.Stmt Mc.Γ Mc.Λ Mc.σ) (vc : Mc.σ) (Sc : ∀ k, List (Mc.Γ k)) :
    TM2.stepAux (trC q) (vc, va, vp, b) (cstk Sc Sa Sp i o rem idx arg tmp) =
      embC va vp b Sa Sp i o rem idx arg tmp (TM2.stepAux q vc Sc) := by
  induction q generalizing vc Sc with
  | push k f q ih =>
    simp only [trC, TM2.stepAux, cstk_set_C]
    exact ih _ _
  | peek k f q ih =>
    simp only [trC, TM2.stepAux, cstk]
    exact ih _ _
  | pop k f q ih =>
    simp only [trC, TM2.stepAux, cstk, cstk_set_C]
    exact ih _ _
  | load a q ih =>
    simp only [trC, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trC, TM2.stepAux]
    cases f vc
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f =>
    simp [trC, TM2.stepAux, embC]
  | halt =>
    simp [trC, TM2.stepAux, embC]

lemma step_embC {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀)
    (ea₀ : Bool → Ma.Γ Ma.k₀) (ea₁ : Ma.Γ Ma.k₁ → Bool)
    (ep₀ : Bool → Mp.Γ Mp.k₀)
    (va : Ma.σ) (vp : Mp.σ) (b : Option Bool)
    (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool)
    (c c' : TM2.Cfg Mc.Γ Mc.Λ Mc.σ) (h : TM2.step Mc.m c = some c') :
    TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀) (embC va vp b Sa Sp i o rem idx arg tmp c) =
      some (embC va vp b Sa Sp i o rem idx arg tmp c') := by
  obtain ⟨l, vc, Sc⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [embC, Option.elim_some, TM2.step, compProg]
    exact congrArg some (stepAux_trC va vp b Sa Sp i o rem idx arg tmp (Mc.m l) vc Sc)

def embA {Mc Ma Mp : FinTM2} (vc : Mc.σ) (vp : Mp.σ) (b : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool)
    (c : TM2.Cfg Ma.Γ Ma.Λ Ma.σ) : CCfg Mc Ma Mp :=
  ⟨some (c.l.elim (lbl Mc Ma Mp 4) (fun l => Sum.inr (Sum.inl l))), (vc, c.var, vp, b),
    cstk Sc c.stk Sp i o rem idx arg tmp⟩

lemma stepAux_trA {Mc Ma Mp : FinTM2} (vc : Mc.σ) (vp : Mp.σ) (b : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool)
    (q : TM2.Stmt Ma.Γ Ma.Λ Ma.σ) (va : Ma.σ) (Sa : ∀ k, List (Ma.Γ k)) :
    TM2.stepAux (trA q) (vc, va, vp, b) (cstk Sc Sa Sp i o rem idx arg tmp) =
      embA vc vp b Sc Sp i o rem idx arg tmp (TM2.stepAux q va Sa) := by
  induction q generalizing va Sa with
  | push k f q ih =>
    simp only [trA, TM2.stepAux, cstk_set_A]
    exact ih _ _
  | peek k f q ih =>
    simp only [trA, TM2.stepAux, cstk]
    exact ih _ _
  | pop k f q ih =>
    simp only [trA, TM2.stepAux, cstk, cstk_set_A]
    exact ih _ _
  | load a q ih =>
    simp only [trA, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trA, TM2.stepAux]
    cases f va
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f =>
    simp [trA, TM2.stepAux, embA]
  | halt =>
    simp [trA, TM2.stepAux, embA]

lemma step_embA {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀)
    (ea₀ : Bool → Ma.Γ Ma.k₀) (ea₁ : Ma.Γ Ma.k₁ → Bool)
    (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (vp : Mp.σ) (b : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool)
    (c c' : TM2.Cfg Ma.Γ Ma.Λ Ma.σ) (h : TM2.step Ma.m c = some c') :
    TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀) (embA vc vp b Sc Sp i o rem idx arg tmp c) =
      some (embA vc vp b Sc Sp i o rem idx arg tmp c') := by
  obtain ⟨l, va, Sa⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [embA, Option.elim_some, TM2.step, compProg]
    exact congrArg some (stepAux_trA vc vp b Sc Sp i o rem idx arg tmp (Ma.m l) va Sa)

def embP {Mc Ma Mp : FinTM2} (vc : Mc.σ) (va : Ma.σ) (b : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (i o rem idx arg tmp : List Bool)
    (c : TM2.Cfg Mp.Γ Mp.Λ Mp.σ) : CCfg Mc Ma Mp :=
  ⟨some (c.l.elim (lbl Mc Ma Mp 11) (fun l => Sum.inr (Sum.inr (Sum.inl l)))),
    (vc, va, c.var, b), cstk Sc Sa c.stk i o rem idx arg tmp⟩

lemma stepAux_trP {Mc Ma Mp : FinTM2} (vc : Mc.σ) (va : Ma.σ) (b : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (i o rem idx arg tmp : List Bool)
    (q : TM2.Stmt Mp.Γ Mp.Λ Mp.σ) (vp : Mp.σ) (Sp : ∀ k, List (Mp.Γ k)) :
    TM2.stepAux (trP q) (vc, va, vp, b) (cstk Sc Sa Sp i o rem idx arg tmp) =
      embP vc va b Sc Sa i o rem idx arg tmp (TM2.stepAux q vp Sp) := by
  induction q generalizing vp Sp with
  | push k f q ih =>
    simp only [trP, TM2.stepAux, cstk_set_P]
    exact ih _ _
  | peek k f q ih =>
    simp only [trP, TM2.stepAux, cstk]
    exact ih _ _
  | pop k f q ih =>
    simp only [trP, TM2.stepAux, cstk, cstk_set_P]
    exact ih _ _
  | load a q ih =>
    simp only [trP, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trP, TM2.stepAux]
    cases f vp
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f =>
    simp [trP, TM2.stepAux, embP]
  | halt =>
    simp [trP, TM2.stepAux, embP]

lemma step_embP {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀)
    (ea₀ : Bool → Ma.Γ Ma.k₀) (ea₁ : Ma.Γ Ma.k₁ → Bool)
    (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (b : Option Bool)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (i o rem idx arg tmp : List Bool)
    (c c' : TM2.Cfg Mp.Γ Mp.Λ Mp.σ) (h : TM2.step Mp.m c = some c') :
    TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀) (embP vc va b Sc Sa i o rem idx arg tmp c) =
      some (embP vc va b Sc Sa i o rem idx arg tmp c') := by
  obtain ⟨l, vp, Sp⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [embP, Option.elim_some, TM2.step, compProg]
    exact congrArg some (stepAux_trP vc va b Sc Sa i o rem idx arg tmp (Mp.m l) vp Sp)

lemma loop0 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (o rem idx : List Bool) :
    ∀ (i arg tmp : List Bool) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[i.length + 1]
        (some (⟨some (lbl Mc Ma Mp 0), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (lbl Mc Ma Mp 1), (vc, va, vp, none),
        cstk Sc Sa Sp [] o rem idx (i.reverse ++ arg) (i.reverse ++ tmp)⟩ := by
  intro i
  induction i with
  | nil =>
    intro arg tmp b
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kI, cstk_set_I]
  | cons a i ih =>
    intro arg tmp b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 0), (vc, va, vp, b),
          cstk Sc Sa Sp (a :: i) o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 0), (vc, va, vp, some a),
          cstk Sc Sa Sp i o rem idx (a :: arg) (a :: tmp)⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kI, kTmp, kArg,
        cstk_set_I, cstk_set_Tmp, cstk_set_Arg]
    rw [hstep, ih]
    simp

lemma loop1 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg : List Bool) :
    ∀ (tmp : List Bool) (Sc : ∀ k, List (Mc.Γ k)) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[tmp.length + 1]
        (some (⟨some (lbl Mc Ma Mp 1), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (Sum.inl Mc.main), (vc, va, vp, none),
        cstk (Function.update Sc Mc.k₀ (tmp.reverse.map ec₀ ++ Sc Mc.k₀))
          Sa Sp i o rem idx arg []⟩ := by
  intro tmp
  induction tmp with
  | nil =>
    intro Sc b
    have hEq : Function.update Sc Mc.k₀ (([] : List Bool).reverse.map ec₀ ++ Sc Mc.k₀) = Sc := by simp
    rw [hEq]
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kTmp, cstk_set_Tmp]
  | cons a tmp ih =>
    intro Sc b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 1), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg (a :: tmp)⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 1), (vc, va, vp, some a),
          cstk (Function.update Sc Mc.k₀ (ec₀ a :: Sc Mc.k₀)) Sa Sp i o rem idx arg tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kTmp,
        cstk_set_Tmp, cstk_set_C]
    rw [hstep, ih]
    simp

lemma loop2 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o idx arg tmp : List Bool) :
    ∀ (mc : List (Mc.Γ Mc.k₁)) (rem : List Bool) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[mc.length + 1]
        (some (⟨some (lbl Mc Ma Mp 2), (vc, va, vp, b),
          cstk (Function.update Sc Mc.k₁ mc) Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (lbl Mc Ma Mp 3), (vc, va, vp, none),
        cstk (Function.update Sc Mc.k₁ []) Sa Sp i o (List.replicate mc.length true ++ rem)
          idx arg tmp⟩ := by
  intro mc
  induction mc with
  | nil =>
    intro rem b
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, cstk_set_C]
  | cons y mc ih =>
    intro rem b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 2), (vc, va, vp, b),
          cstk (Function.update Sc Mc.k₁ (y :: mc)) Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 2), (vc, va, vp, some true),
          cstk (Function.update Sc Mc.k₁ mc) Sa Sp i o (true :: rem) idx arg tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kRem,
        cstk_set_C, cstk_set_Rem]
    rw [hstep, ih]
    congr 2
    rw [List.replicate_succ', List.append_assoc]
    rfl

lemma loop3 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx tmp : List Bool) :
    ∀ (arg : List Bool) (Sa : ∀ k, List (Ma.Γ k)) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[arg.length + 1]
        (some (⟨some (lbl Mc Ma Mp 3), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (Sum.inr (Sum.inl Ma.main)), (vc, va, vp, none),
        cstk Sc (Function.update Sa Ma.k₀ (arg.reverse.map ea₀ ++ Sa Ma.k₀))
          Sp i o rem idx [] tmp⟩ := by
  intro arg
  induction arg with
  | nil =>
    intro Sa b
    have hEq : Function.update Sa Ma.k₀ (([] : List Bool).reverse.map ea₀ ++ Sa Ma.k₀) = Sa := by simp
    rw [hEq]
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kArg, cstk_set_Arg]
  | cons a arg ih =>
    intro Sa b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 3), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx (a :: arg) tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 3), (vc, va, vp, some a),
          cstk Sc (Function.update Sa Ma.k₀ (ea₀ a :: Sa Ma.k₀)) Sp i o rem idx arg tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kArg,
        cstk_set_Arg, cstk_set_A]
    rw [hstep, ih]
    simp

lemma loop4 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx tmp : List Bool) :
    ∀ (ma : List (Ma.Γ Ma.k₁)) (arg : List Bool) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[ma.length + 1]
        (some (⟨some (lbl Mc Ma Mp 4), (vc, va, vp, b),
          cstk Sc (Function.update Sa Ma.k₁ ma) Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (lbl Mc Ma Mp 5), (vc, va, vp, none),
        cstk Sc (Function.update Sa Ma.k₁ []) Sp i o rem idx (ma.reverse.map ea₁ ++ arg) tmp⟩ := by
  intro ma
  induction ma with
  | nil =>
    intro arg b
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, cstk_set_A]
  | cons y ma ih =>
    intro arg b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 4), (vc, va, vp, b),
          cstk Sc (Function.update Sa Ma.k₁ (y :: ma)) Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 4), (vc, va, vp, some (ea₁ y)),
          cstk Sc (Function.update Sa Ma.k₁ ma) Sp i o rem idx (ea₁ y :: arg) tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kArg,
        cstk_set_A, cstk_set_Arg]
    rw [hstep, ih]
    simp

lemma loop6 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (i o rem idx : List Bool) :
    ∀ (arg tmp : List Bool) (Sp : ∀ k, List (Mp.Γ k)) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[arg.length + 1]
        (some (⟨some (lbl Mc Ma Mp 6), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (lbl Mc Ma Mp 7), (vc, va, vp, none),
        cstk Sc Sa (Function.update Sp Mp.k₀ (arg.reverse.map ep₀ ++ Sp Mp.k₀))
          i o rem idx [] (arg.reverse ++ tmp)⟩ := by
  intro arg
  induction arg with
  | nil =>
    intro tmp Sp b
    have hEq : Function.update Sp Mp.k₀ (([] : List Bool).reverse.map ep₀ ++ Sp Mp.k₀) = Sp := by simp
    rw [hEq]
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kArg, cstk_set_Arg]
  | cons a arg ih =>
    intro tmp Sp b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 6), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx (a :: arg) tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 6), (vc, va, vp, some a),
          cstk Sc Sa (Function.update Sp Mp.k₀ (ep₀ a :: Sp Mp.k₀))
            i o rem idx arg (a :: tmp)⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kArg, kTmp,
        cstk_set_Arg, cstk_set_P, cstk_set_Tmp]
    rw [hstep, ih]
    simp

lemma loop7 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx : List Bool) :
    ∀ (tmp arg : List Bool) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[tmp.length + 1]
        (some (⟨some (lbl Mc Ma Mp 7), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (lbl Mc Ma Mp 8), (vc, va, vp, none),
        cstk Sc Sa Sp i o rem idx (tmp.reverse ++ arg) []⟩ := by
  intro tmp
  induction tmp with
  | nil =>
    intro arg b
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kTmp, cstk_set_Tmp]
  | cons a tmp ih =>
    intro arg b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 7), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg (a :: tmp)⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 7), (vc, va, vp, some a),
          cstk Sc Sa Sp i o rem idx (a :: arg) tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kTmp, kArg,
        cstk_set_Tmp, cstk_set_Arg]
    rw [hstep, ih]
    simp

lemma loop8 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (i o rem arg : List Bool) :
    ∀ (idx tmp : List Bool) (Sp : ∀ k, List (Mp.Γ k)) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[idx.length + 1]
        (some (⟨some (lbl Mc Ma Mp 8), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (lbl Mc Ma Mp 9), (vc, va, vp, none),
        cstk Sc Sa (Function.update Sp Mp.k₀ (idx.reverse.map ep₀ ++ Sp Mp.k₀))
          i o rem [] arg (idx.reverse ++ tmp)⟩ := by
  intro idx
  induction idx with
  | nil =>
    intro tmp Sp b
    have hEq : Function.update Sp Mp.k₀ (([] : List Bool).reverse.map ep₀ ++ Sp Mp.k₀) = Sp := by simp
    rw [hEq]
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kIdx, cstk_set_Idx]
  | cons a idx ih =>
    intro tmp Sp b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 8), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem (a :: idx) arg tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 8), (vc, va, vp, some a),
          cstk Sc Sa (Function.update Sp Mp.k₀ (ep₀ a :: Sp Mp.k₀))
            i o rem idx arg (a :: tmp)⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kIdx, kTmp,
        cstk_set_Idx, cstk_set_P, cstk_set_Tmp]
    rw [hstep, ih]
    simp

lemma loop10 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k))
    (i o rem arg : List Bool) :
    ∀ (tmp idx : List Bool) (Sp : ∀ k, List (Mp.Γ k)) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[tmp.length + 1]
        (some (⟨some (lbl Mc Ma Mp 10), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (Sum.inr (Sum.inr (Sum.inl Mp.main))), (vc, va, vp, none),
        cstk Sc Sa (Function.update Sp Mp.k₀ (tmp.reverse.map ep₀ ++ Sp Mp.k₀))
          i o rem (tmp.reverse ++ idx) arg []⟩ := by
  intro tmp
  induction tmp with
  | nil =>
    intro idx Sp b
    have hEq : Function.update Sp Mp.k₀ (([] : List Bool).reverse.map ep₀ ++ Sp Mp.k₀) = Sp := by simp
    rw [hEq]
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kTmp, cstk_set_Tmp]
  | cons a tmp ih =>
    intro idx Sp b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 10), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg (a :: tmp)⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 10), (vc, va, vp, some a),
          cstk Sc Sa (Function.update Sp Mp.k₀ (ep₀ a :: Sp Mp.k₀))
            i o rem (a :: idx) arg tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kTmp, kIdx,
        cstk_set_Tmp, cstk_set_P, cstk_set_Idx]
    rw [hstep, ih]
    simp

lemma loop12 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx arg tmp : List Bool) :
    ∀ (mp : List (Mp.Γ Mp.k₁)) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[mp.length + 1]
        (some (⟨some (lbl Mc Ma Mp 12), (vc, va, vp, b),
          cstk Sc Sa (Function.update Sp Mp.k₁ mp) i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (lbl Mc Ma Mp 5), (vc, va, vp, none),
        cstk Sc Sa (Function.update Sp Mp.k₁ []) i (true :: o) rem (true :: idx) arg tmp⟩ := by
  intro mp
  induction mp with
  | nil =>
    intro b
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, cstk_set_P, kIdx, kO,
      cstk_set_Idx, cstk_set_O]
  | cons y mp ih =>
    intro b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 12), (vc, va, vp, b),
          cstk Sc Sa (Function.update Sp Mp.k₁ (y :: mp)) i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 12), (vc, va, vp, some true),
          cstk Sc Sa (Function.update Sp Mp.k₁ mp) i o rem idx arg tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, cstk_set_P]
    rw [hstep, ih]

lemma loop13 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o idx arg tmp : List Bool) :
    ∀ (rem : List Bool) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[rem.length + 1]
        (some (⟨some (lbl Mc Ma Mp 13), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (lbl Mc Ma Mp 14), (vc, va, vp, none),
        cstk Sc Sa Sp i o [] idx arg tmp⟩ := by
  intro rem
  induction rem with
  | nil =>
    intro b
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kRem, cstk_set_Rem]
  | cons a rem ih =>
    intro b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 13), (vc, va, vp, b),
          cstk Sc Sa Sp i o (a :: rem) idx arg tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 13), (vc, va, vp, some a),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kRem, cstk_set_Rem]
    rw [hstep, ih]

lemma loop14 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i o rem idx tmp : List Bool) :
    ∀ (arg : List Bool) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[arg.length + 1]
        (some (⟨some (lbl Mc Ma Mp 14), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨some (lbl Mc Ma Mp 15), (vc, va, vp, none),
        cstk Sc Sa Sp i o rem idx [] tmp⟩ := by
  intro arg
  induction arg with
  | nil =>
    intro b
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kArg, cstk_set_Arg]
  | cons a arg ih =>
    intro b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 14), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx (a :: arg) tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 14), (vc, va, vp, some a),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kArg, cstk_set_Arg]
    rw [hstep, ih]

lemma loop15 {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀)
    (vc : Mc.σ) (va : Ma.σ) (vp : Mp.σ)
    (Sc : ∀ k, List (Mc.Γ k)) (Sa : ∀ k, List (Ma.Γ k)) (Sp : ∀ k, List (Mp.Γ k))
    (i rem arg tmp : List Bool) :
    ∀ (idx o : List Bool) (b : Option Bool),
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[idx.length + 1]
        (some (⟨some (lbl Mc Ma Mp 15), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ : CCfg Mc Ma Mp)) =
      some ⟨none, (vc, va, vp, none),
        cstk Sc Sa Sp i o rem [] arg tmp⟩ := by
  intro idx
  induction idx with
  | nil =>
    intro o b
    simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kIdx, cstk_set_Idx]
  | cons a idx ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
        (some (⟨some (lbl Mc Ma Mp 15), (vc, va, vp, b),
          cstk Sc Sa Sp i o rem (a :: idx) arg tmp⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 15), (vc, va, vp, some a),
          cstk Sc Sa Sp i o rem idx arg tmp⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kIdx,
        cstk_set_Idx]
    rw [hstep, ih]

lemma search_loop {Mc Ma Mp : FinTM2}
    (ec₀ : Bool → Mc.Γ Mc.k₀) (ea₀ : Bool → Ma.Γ Ma.k₀)
    (ea₁ : Ma.Γ Ma.k₁ → Bool) (ep₀ : Bool → Mp.Γ Mp.k₀) (ep₁ : Mp.Γ Mp.k₁ → Bool)
    (p : List Bool → List Bool) (Tp : Polynomial ℕ)
    (hp_run : ∀ z : List Bool, ∃ (s : ℕ) (m : List (Mp.Γ Mp.k₁)),
      s ≤ Tp.eval z.length ∧
      (flip bind (TM2.step Mp.m))^[s] (some (initList Mp (z.map ep₀))) = some (haltList Mp m) ∧
      m.map ep₁ = p z)
    (a : List Bool) (N Q : ℕ) (hQ : 2 * N + 1 + a.length ≤ Q) :
    ∀ (r idxLen c : ℕ) (b : Option Bool), idxLen + r ≤ N →
      ∃ n, n ≤ r * (Tp.eval Q + 2 * a.length + 2 * N + 8 +
          (Q + maxPush Mp * Tp.eval Q + 2)) + 2 * N + a.length + 6 ∧
        (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[n]
          (some (⟨some (lbl Mc Ma Mp 5),
            (Mc.initialState, Ma.initialState, Mp.initialState, b),
            cstk (fun _ => []) (fun _ => []) (fun _ => []) [] (List.replicate c true)
              (List.replicate r true) (List.replicate idxLen true) a.reverse []⟩ : CCfg Mc Ma Mp)) =
        some (haltList (compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀)
          (List.replicate (c + cntFrom (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ a))).isEmpty) idxLen r) true)) := by
  intro r
  induction r with
  | zero =>
    intro idxLen c b hle
    have q1 : (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[1]
        (some (⟨some (lbl Mc Ma Mp 5),
          (Mc.initialState, Ma.initialState, Mp.initialState, b),
          cstk (fun _ => []) (fun _ => []) (fun _ => []) [] (List.replicate c true)
            [] (List.replicate idxLen true) a.reverse []⟩ : CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 14),
          (Mc.initialState, Ma.initialState, Mp.initialState, none),
          cstk (fun _ => []) (fun _ => []) (fun _ => []) [] (List.replicate c true)
            [] (List.replicate idxLen true) a.reverse []⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kRem, cstk_set_Rem]
    have q2 := loop14 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) (fun _ => []) [] (List.replicate c true) []
      (List.replicate idxLen true) [] a.reverse none
    have q3 := loop15 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] [] (List.replicate idxLen true)
      (List.replicate c true) none
    have hhalt : (⟨none, (Mc.initialState, Ma.initialState, Mp.initialState, none),
        cstk (fun _ => []) (fun _ => []) (fun _ => []) []
          (List.replicate c true) [] [] [] []⟩ : CCfg Mc Ma Mp) =
        haltList (compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀) (List.replicate c true) := by
      rw [cstk_nil_O]
      exact (haltList_eq (compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀) (List.replicate c true)).symm
    rw [hhalt] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    simp only [List.length_reverse, List.length_replicate]
    omega
  | succ r ih =>
    intro idxLen c b hle
    let qstr := List.replicate idxLen true ++ false :: (List.replicate idxLen true ++ a)
    have hqlen : qstr.length ≤ Q := by
      simp only [qstr, List.length_append, List.length_cons, List.length_replicate]
      omega
    have q1 : (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[1]
        (some (⟨some (lbl Mc Ma Mp 5),
          (Mc.initialState, Ma.initialState, Mp.initialState, b),
          cstk (fun _ => []) (fun _ => []) (fun _ => []) [] (List.replicate c true)
            (true :: List.replicate r true) (List.replicate idxLen true) a.reverse []⟩ :
            CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 6),
          (Mc.initialState, Ma.initialState, Mp.initialState, some true),
          cstk (fun _ => []) (fun _ => []) (fun _ => []) [] (List.replicate c true)
            (List.replicate r true) (List.replicate idxLen true) a.reverse []⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, kRem, cstk_set_Rem]
    have q2 := loop6 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) [] (List.replicate c true) (List.replicate r true) (List.replicate idxLen true)
      a.reverse [] (fun _ => []) (some true)
    simp only [List.reverse_reverse, List.append_nil] at q2
    have q3 := loop7 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) (Function.update (fun _ => []) Mp.k₀ (a.map ep₀))
      [] (List.replicate c true) (List.replicate r true) (List.replicate idxLen true) a [] none
    simp only [List.append_nil] at q3
    have q4 := loop8 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) [] (List.replicate c true) (List.replicate r true) a.reverse
      (List.replicate idxLen true) [] (Function.update (fun _ => []) Mp.k₀ (a.map ep₀)) none
    simp only [List.reverse_replicate, List.append_nil, Function.update_self, Function.update_idem] at q4
    have q5 : (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[1]
        (some (⟨some (lbl Mc Ma Mp 9),
          (Mc.initialState, Ma.initialState, Mp.initialState, none),
          cstk (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) Mp.k₀ ((List.replicate idxLen true).map ep₀ ++ a.map ep₀))
            [] (List.replicate c true) (List.replicate r true) [] a.reverse (List.replicate idxLen true)⟩ :
            CCfg Mc Ma Mp)) =
        some ⟨some (lbl Mc Ma Mp 10),
          (Mc.initialState, Ma.initialState, Mp.initialState, none),
          cstk (fun _ => []) (fun _ => [])
            (Function.update (fun _ => []) Mp.k₀
              (ep₀ false :: ((List.replicate idxLen true).map ep₀ ++ a.map ep₀)))
            [] (List.replicate c true) (List.replicate r true) [] a.reverse (List.replicate idxLen true)⟩ := by
      simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, cstk_set_P]
    have q6 := loop10 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) [] (List.replicate c true) (List.replicate r true) a.reverse
      (List.replicate idxLen true) []
      (Function.update (fun _ => []) Mp.k₀
        (ep₀ false :: ((List.replicate idxLen true).map ep₀ ++ a.map ep₀))) none
    simp only [List.reverse_replicate, List.append_nil, Function.update_self, Function.update_idem] at q6
    have hqmap : (List.replicate idxLen true).map ep₀ ++
        (ep₀ false :: ((List.replicate idxLen true).map ep₀ ++ a.map ep₀)) = qstr.map ep₀ := by
      simp [qstr, List.map_append]
    rw [hqmap] at q6
    obtain ⟨sp, mp, hsp, hmp_run, hmp_val⟩ := hp_run qstr
    have q7 := simulate (TM2.step Mp.m) (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
      (embP Mc.initialState Ma.initialState none (fun _ => []) (fun _ => [])
        [] (List.replicate c true) (List.replicate r true) (List.replicate idxLen true) a.reverse [])
      (step_embP ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState none (fun _ => []) (fun _ => [])
        [] (List.replicate c true) (List.replicate r true) (List.replicate idxLen true) a.reverse [])
      sp _ _ hmp_run
    rw [initList_eq, haltList_eq] at q7
    simp only [embP, Option.elim_some, Option.elim_none] at q7
    have hspQ : sp ≤ Tp.eval Q := hsp.trans (eval_mono Tp hqlen)
    have hmp_len : mp.length ≤ Q + maxPush Mp * Tp.eval Q := by
      have h' := hmp_run
      rw [initList_eq, haltList_eq] at h'
      have hlen := run_length Mp Mp.k₁ sp _ _ h'
      simp only [Function.update_self] at hlen
      have hin : ((Function.update (fun _ => [] : ∀ k, List (Mp.Γ k)) Mp.k₀ (qstr.map ep₀))
          Mp.k₁).length ≤ qstr.length := by
        by_cases hk : Mp.k₁ = Mp.k₀
        · rw [hk, Function.update_self, List.length_map]
        · rw [Function.update_of_ne hk]; simp
      have hmul : maxPush Mp * sp ≤ maxPush Mp * Tp.eval Q := Nat.mul_le_mul_left _ hspQ
      omega
    have q1_6 := iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5) q6) q7
    cases hmp : mp with
    | nil =>
      have hp_empty : (p qstr).isEmpty = true := by
        rw [← hmp_val, hmp]; rfl
      have hfind : c + cntFrom (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ a))).isEmpty) idxLen (r + 1) =
          c + cntFrom (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ a))).isEmpty) (idxLen + 1) r := by
        simp [cntFrom, qstr] at hp_empty ⊢
        simp [hp_empty]
      rw [hmp] at q1_6
      have q8 : (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[1]
          (some (⟨some (lbl Mc Ma Mp 11),
            (Mc.initialState, Ma.initialState, Mp.initialState, none),
            cstk (fun _ => []) (fun _ => []) (Function.update (fun _ => []) Mp.k₁ [])
              [] (List.replicate c true) (List.replicate r true) (List.replicate idxLen true) a.reverse []⟩ :
              CCfg Mc Ma Mp)) =
          some ⟨some (lbl Mc Ma Mp 5),
            (Mc.initialState, Ma.initialState, Mp.initialState, none),
            cstk (fun _ => []) (fun _ => []) (fun _ => [])
              [] (List.replicate c true) (List.replicate r true) (List.replicate (idxLen + 1) true) a.reverse []⟩ := by
        have hupd : Function.update (fun _ => [] : ∀ k, List (Mp.Γ k)) Mp.k₁ [] = fun _ => [] :=
          Function.update_eq_self Mp.k₁ _
        rw [hupd, List.replicate_succ]
        simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, cstk_set_P, kIdx,
          cstk_set_Idx]
      obtain ⟨n', hn', q9⟩ := ih (idxLen + 1) c none (by omega)
      rw [hfind]
      refine ⟨_, ?_, iter_trans _ (iter_trans _ q1_6 q8) q9⟩
      simp only [List.length_reverse, List.length_replicate, Nat.succ_mul] at hn' ⊢
      omega
    | cons y mp' =>
      have hp_nonempty : (p qstr).isEmpty = false := by
        rw [← hmp_val, hmp]; rfl
      have hfind : c + cntFrom (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ a))).isEmpty) idxLen (r + 1) =
          (c + 1) + cntFrom (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ a))).isEmpty) (idxLen + 1) r := by
        simp [cntFrom, qstr] at hp_nonempty ⊢
        simp [hp_nonempty]
        omega
      rw [hmp] at q1_6 hmp_len
      have q8 : (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[1]
          (some (⟨some (lbl Mc Ma Mp 11),
            (Mc.initialState, Ma.initialState, Mp.initialState, none),
            cstk (fun _ => []) (fun _ => []) (Function.update (fun _ => []) Mp.k₁ (y :: mp'))
              [] (List.replicate c true) (List.replicate r true) (List.replicate idxLen true) a.reverse []⟩ :
              CCfg Mc Ma Mp)) =
          some ⟨some (lbl Mc Ma Mp 12),
            (Mc.initialState, Ma.initialState, Mp.initialState, some true),
            cstk (fun _ => []) (fun _ => []) (Function.update (fun _ => []) Mp.k₁ mp')
              [] (List.replicate c true) (List.replicate r true) (List.replicate idxLen true) a.reverse []⟩ := by
        simp [flip, TM2.step, compProg, ctrlProg, lbl, TM2.stepAux, cstk, cstk_set_P]
      have q9 := loop12 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
        (fun _ => []) (fun _ => []) (fun _ => []) [] (List.replicate c true) (List.replicate r true)
        (List.replicate idxLen true) a.reverse [] mp' (some true)
      have hupd : Function.update (fun _ => [] : ∀ k, List (Mp.Γ k)) Mp.k₁ [] = fun _ => [] :=
        Function.update_eq_self Mp.k₁ _
      rw [hupd, ← List.replicate_succ, ← List.replicate_succ] at q9
      obtain ⟨n', hn', q10⟩ := ih (idxLen + 1) (c + 1) none (by omega)
      rw [hfind]
      refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ q1_6 q8) q9) q10⟩
      simp only [List.length_reverse, List.length_replicate, List.length_cons, Nat.succ_mul] at hmp_len hn' ⊢
      omega

theorem main_thm : ∀ p cnt arg : List Bool → List Bool, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) p → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cnt → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) arg → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s : List Bool => List.replicate ((List.range (cnt s).length).countP (fun i : ℕ => !(p (List.replicate i true ++ false :: (List.replicate i true ++ arg s))).isEmpty)) true) := by
  rintro p cnt arg ⟨cp⟩ ⟨cc⟩ ⟨ca⟩
  let Mc := cc.tm
  let Ma := ca.tm
  let Mp := cp.tm
  let ec₀ : Bool → Mc.Γ Mc.k₀ := cc.inputAlphabet.invFun
  let ec₁ : Mc.Γ Mc.k₁ → Bool := cc.outputAlphabet
  let ea₀ : Bool → Ma.Γ Ma.k₀ := ca.inputAlphabet.invFun
  let ea₁ : Ma.Γ Ma.k₁ → Bool := ca.outputAlphabet
  let ep₀ : Bool → Mp.Γ Mp.k₀ := cp.inputAlphabet.invFun
  let ep₁ : Mp.Γ Mp.k₁ → Bool := cp.outputAlphabet
  let PC : Polynomial ℕ := Polynomial.X + Polynomial.C (maxPush Mc) * cc.time
  let PA : Polynomial ℕ := Polynomial.X + Polynomial.C (maxPush Ma) * ca.time
  let PQ : Polynomial ℕ := Polynomial.C 2 * PC + Polynomial.C 1 + PA
  let PpQ : Polynomial ℕ := cp.time.comp PQ
  let T : Polynomial ℕ :=
    Polynomial.C 3 * Polynomial.X + cc.time + ca.time +
      PC * (PpQ + Polynomial.C 2 * PA + Polynomial.C 2 * PC + Polynomial.C 8 +
        (PQ + Polynomial.C (maxPush Mp) * PpQ + Polynomial.C 2)) +
      Polynomial.C 3 * PC + Polynomial.C 2 * PA + Polynomial.C 12
  have hp_run : ∀ z : List Bool, ∃ (s : ℕ) (m : List (Mp.Γ Mp.k₁)),
      s ≤ cp.time.eval z.length ∧
      (flip bind (TM2.step Mp.m))^[s] (some (initList Mp (z.map ep₀))) = some (haltList Mp m) ∧
      m.map ep₁ = p z := by
    intro z
    refine ⟨(cp.outputsFun z).steps, (p z).map cp.outputAlphabet.invFun,
      (cp.outputsFun z).steps_le_m, (cp.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (p z)]
    exact List.map_congr_left fun b _ => cp.outputAlphabet.right_inv b
  have key : ∀ s : List Bool, ∃ n, n ≤ T.eval s.length ∧
      (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[n]
        (some (initList (compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀) s)) =
      some (haltList (compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀)
        (List.replicate ((List.range (cnt s).length).countP
          (fun i => !(p (List.replicate i true ++ false :: (List.replicate i true ++ arg s))).isEmpty)) true)) := by
    intro s
    have hinit : initList (compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀) s =
        (⟨some (lbl Mc Ma Mp 0), (Mc.initialState, Ma.initialState, Mp.initialState, none),
          cstk (fun _ => []) (fun _ => []) (fun _ => []) s [] [] [] [] []⟩ : CCfg Mc Ma Mp) := by
      rw [cstk_nil_I]
      exact initList_eq (compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀) s
    have q0 := loop0 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] s [] [] none
    simp only [List.append_nil] at q0
    rw [← hinit] at q0
    have q1 := loop1 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) [] [] [] [] s.reverse s.reverse (fun _ => []) none
    simp only [List.reverse_reverse, List.append_nil] at q1
    have hsc : (cc.outputsFun s).steps ≤ cc.time.eval s.length := (cc.outputsFun s).steps_le_m
    have hmc_run : (flip bind (TM2.step Mc.m))^[(cc.outputsFun s).steps]
        (some (initList Mc (s.map ec₀))) =
        some (haltList Mc ((cnt s).map cc.outputAlphabet.invFun)) := (cc.outputsFun s).evals_in_steps
    have q2 := simulate (TM2.step Mc.m) (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
      (embC Ma.initialState Mp.initialState none (fun _ => []) (fun _ => [])
        [] [] [] [] s.reverse [])
      (step_embC ec₀ ea₀ ea₁ ep₀ Ma.initialState Mp.initialState none (fun _ => []) (fun _ => [])
        [] [] [] [] s.reverse [])
      (cc.outputsFun s).steps _ _ hmc_run
    have hq2i : embC Ma.initialState Mp.initialState none (fun _ => []) (fun _ => [])
        [] [] [] [] s.reverse [] (initList Mc (s.map ec₀)) =
        ⟨some (Sum.inl Mc.main), (Mc.initialState, Ma.initialState, Mp.initialState, none),
          cstk (Function.update (fun _ => []) Mc.k₀ (s.map ec₀)) (fun _ => []) (fun _ => [])
            [] [] [] [] s.reverse []⟩ := by
      rw [initList_eq]; rfl
    have hq2h : embC Ma.initialState Mp.initialState none (fun _ => []) (fun _ => [])
        [] [] [] [] s.reverse [] (haltList Mc ((cnt s).map cc.outputAlphabet.invFun)) =
        ⟨some (lbl Mc Ma Mp 2), (Mc.initialState, Ma.initialState, Mp.initialState, none),
          cstk (Function.update (fun _ => []) Mc.k₁ ((cnt s).map cc.outputAlphabet.invFun))
            (fun _ => []) (fun _ => []) [] [] [] [] s.reverse []⟩ := by
      rw [haltList_eq]; rfl
    rw [hq2i, hq2h] at q2
    have q3 := loop2 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) (fun _ => []) [] [] [] s.reverse []
      ((cnt s).map cc.outputAlphabet.invFun) [] none
    have hupdC : Function.update (fun _ => [] : ∀ k, List (Mc.Γ k)) Mc.k₁ [] = fun _ => [] :=
      Function.update_eq_self Mc.k₁ _
    rw [hupdC, List.append_nil, List.length_map] at q3
    have q4 := loop3 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) [] [] (List.replicate (cnt s).length true) [] []
      s.reverse (fun _ => []) none
    simp only [List.reverse_reverse, List.append_nil] at q4
    have hsa : (ca.outputsFun s).steps ≤ ca.time.eval s.length := (ca.outputsFun s).steps_le_m
    have hma_run : (flip bind (TM2.step Ma.m))^[(ca.outputsFun s).steps]
        (some (initList Ma (s.map ea₀))) =
        some (haltList Ma ((arg s).map ca.outputAlphabet.invFun)) := (ca.outputsFun s).evals_in_steps
    have q5 := simulate (TM2.step Ma.m) (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀))
      (embA Mc.initialState Mp.initialState none (fun _ => []) (fun _ => [])
        [] [] (List.replicate (cnt s).length true) [] [] [])
      (step_embA ec₀ ea₀ ea₁ ep₀ Mc.initialState Mp.initialState none (fun _ => []) (fun _ => [])
        [] [] (List.replicate (cnt s).length true) [] [] [])
      (ca.outputsFun s).steps _ _ hma_run
    have hq5i : embA Mc.initialState Mp.initialState none (fun _ => []) (fun _ => [])
        [] [] (List.replicate (cnt s).length true) [] [] [] (initList Ma (s.map ea₀)) =
        ⟨some (Sum.inr (Sum.inl Ma.main)), (Mc.initialState, Ma.initialState, Mp.initialState, none),
          cstk (fun _ => []) (Function.update (fun _ => []) Ma.k₀ (s.map ea₀)) (fun _ => [])
            [] [] (List.replicate (cnt s).length true) [] [] []⟩ := by
      rw [initList_eq]; rfl
    have hq5h : embA Mc.initialState Mp.initialState none (fun _ => []) (fun _ => [])
        [] [] (List.replicate (cnt s).length true) [] [] []
        (haltList Ma ((arg s).map ca.outputAlphabet.invFun)) =
        ⟨some (lbl Mc Ma Mp 4), (Mc.initialState, Ma.initialState, Mp.initialState, none),
          cstk (fun _ => []) (Function.update (fun _ => []) Ma.k₁ ((arg s).map ca.outputAlphabet.invFun))
            (fun _ => []) [] [] (List.replicate (cnt s).length true) [] [] []⟩ := by
      rw [haltList_eq]; rfl
    rw [hq5i, hq5h] at q5
    have q6 := loop4 ec₀ ea₀ ea₁ ep₀ Mc.initialState Ma.initialState Mp.initialState
      (fun _ => []) (fun _ => []) (fun _ => []) [] [] (List.replicate (cnt s).length true) [] []
      ((arg s).map ca.outputAlphabet.invFun) [] none
    have hupdA : Function.update (fun _ => [] : ∀ k, List (Ma.Γ k)) Ma.k₁ [] = fun _ => [] :=
      Function.update_eq_self Ma.k₁ _
    have hma_rev : ((arg s).map ca.outputAlphabet.invFun).reverse.map ea₁ = (arg s).reverse := by
      rw [List.map_reverse, List.map_map]
      congr 1
      conv_rhs => rw [← List.map_id (arg s)]
      exact List.map_congr_left fun b _ => ca.outputAlphabet.right_inv b
    rw [hupdA, List.append_nil, hma_rev] at q6
    have hcnt_len : (cnt s).length ≤ PC.eval s.length := by
      have hlen := out_len_le Mc (s.map ec₀) ((cnt s).map cc.outputAlphabet.invFun)
        (cc.outputsFun s).steps hmc_run
      simp only [List.length_map] at hlen
      have hmul : maxPush Mc * (cc.outputsFun s).steps ≤ maxPush Mc * cc.time.eval s.length :=
        Nat.mul_le_mul_left _ hsc
      simp only [PC, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega
    have harg_len : (arg s).length ≤ PA.eval s.length := by
      have hlen := out_len_le Ma (s.map ea₀) ((arg s).map ca.outputAlphabet.invFun)
        (ca.outputsFun s).steps hma_run
      simp only [List.length_map] at hlen
      have hmul : maxPush Ma * (ca.outputsFun s).steps ≤ maxPush Ma * ca.time.eval s.length :=
        Nat.mul_le_mul_left _ hsa
      simp only [PA, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega
    have hQ_bound : 2 * (cnt s).length + 1 + (arg s).length ≤ PQ.eval s.length := by
      simp only [PQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      omega
    obtain ⟨n_loop, hn_loop, q7⟩ := search_loop ec₀ ea₀ ea₁ ep₀ ep₁ p cp.time hp_run
      (arg s) (cnt s).length (PQ.eval s.length) hQ_bound (cnt s).length 0 0 none (by omega)
    rw [Nat.zero_add, cntFrom_zero] at q7
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q0 q1) q2) q3) q4) q5) q6) q7⟩
    have hprod : (cnt s).length * (cp.time.eval (PQ.eval s.length) + 2 * (arg s).length +
          2 * (cnt s).length + 8 + (PQ.eval s.length +
            maxPush Mp * cp.time.eval (PQ.eval s.length) + 2)) ≤
        PC.eval s.length * (PpQ.eval s.length + 2 * PA.eval s.length + 2 * PC.eval s.length + 8 +
          (PQ.eval s.length + maxPush Mp * PpQ.eval s.length + 2)) := by
      have hpq : PpQ.eval s.length = cp.time.eval (PQ.eval s.length) := by
        simp [PpQ, Polynomial.eval_comp]
      rw [hpq]
      exact Nat.mul_le_mul hcnt_len (by omega)
    have hpq : PpQ.eval s.length = cp.time.eval (PQ.eval s.length) := by
      simp [PpQ, Polynomial.eval_comp]
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      List.length_reverse, List.length_map]
    rw [hpq] at hprod ⊢
    omega
  exact ⟨{
    tm := compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun s =>
      { steps := Classical.choose (key s)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (compProg Mc Ma Mp ec₀ ea₀ ea₁ ep₀)))^[
            Classical.choose (key s)] (some (initList (compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀) l)))
            (hm _ s)).trans ((Classical.choose_spec (key s)).2.trans
            (congrArg (fun l => some (haltList (compM Mc Ma Mp ec₀ ea₀ ea₁ ep₀) l))
              (hm _ _).symm))
        steps_le_m := (Classical.choose_spec (key s)).1 } }⟩

end PEqualNP.Outside.L_meta_383

theorem PEqualNP.Outside.L_meta_383 : ∀ p cnt arg : List Bool → List Bool, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) p → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cnt → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) arg → PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s : List Bool => List.replicate ((List.range (cnt s).length).countP (fun i : ℕ => !(p (List.replicate i true ++ false :: (List.replicate i true ++ arg s))).isEmpty)) true) :=
  PEqualNP.Outside.L_meta_383.main_thm
