import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1018

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

lemma wiresFrom_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wiresFrom (gs ++ [g]) w =
      wiresFrom gs w ++ [g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD i false)] := by
  simp [wiresFrom, List.foldl_append]

lemma length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    have hstep : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) := rfl
    rw [hstep, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_snoc (l : List Bool) (b : Bool) (j : ℕ) :
    (l ++ [b]).getD j false =
      if j < l.length then l.getD j false else if j = l.length then b else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def W (gs : List Gate) (j : ℕ) (x : Fin 13 → Bool) : Bool :=
  (wiresFrom gs (List.ofFn x)).getD j false

lemma W_snoc (gs : List Gate) (g : Gate) (j : ℕ) (x : Fin 13 → Bool) :
    W (gs ++ [g]) j x =
      if j < 13 + gs.length then W gs j x
      else if j = 13 + gs.length then g.op.eval (g.inputs.map fun i => W gs i x) else false := by
  simp only [W, wiresFrom_snoc, getD_snoc, length_wiresFrom, List.length_ofFn]

lemma ofFn_getD (z : Fin 13 → Bool) (j : ℕ) (hj : j < 13) :
    (List.ofFn z).getD j false = z ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]

lemma W_mono (gs : List Gate) (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (j : ℕ)
    (x y : Fin 13 → Bool) (hle : ∀ w, x w = true → y w = true) (h : W gs j x = true) :
    W gs j y = true := by
  refine wiresFrom_mono gs hmono (List.ofFn x) (List.ofFn y) (by simp) ?_ j h
  intro i hi
  by_cases hi13 : i < 13
  · rw [ofFn_getD x i hi13] at hi
    rw [ofFn_getD y i hi13]
    exact hle _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.noConfusion hi

def wt (x : Fin 13 → Bool) : ℕ := (Finset.univ.filter (fun i : Fin 13 => x i = true)).card

lemma wt_mono (a b : Fin 13 → Bool) (h : ∀ v, a v = true → b v = true) : wt a ≤ wt b := by
  refine Finset.card_le_card ?_
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact h v hv

lemma wt_or_le (a b y : Fin 13 → Bool) (h : ∀ w, y w = true → a w = true ∨ b w = true) :
    wt y ≤ wt a + wt b := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hw ⊢
  exact h w hw

lemma wt_split (c : Fin 13 → Fin 13) (α β : Fin 13) (hαβ : α ≠ β) (x : Fin 13 → Bool) :
    wt (fun w => x w && decide (c w = α)) + wt (fun w => x w && decide (c w = β)) ≤ wt x := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i : Fin 13 => x i = true)) (fun w => c w = α)
  have h1 : wt (fun w => x w && decide (c w = α)) ≤
      ((Finset.univ.filter (fun i : Fin 13 => x i = true)).filter (fun w => c w = α)).card := by
    refine Finset.card_le_card ?_
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq] at hw ⊢
    exact hw
  have h2 : wt (fun w => x w && decide (c w = β)) ≤
      ((Finset.univ.filter (fun i : Fin 13 => x i = true)).filter (fun w => ¬ c w = α)).card := by
    refine Finset.card_le_card ?_
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq] at hw ⊢
    exact ⟨hw.1, fun e => hαβ (e.symm.trans hw.2)⟩
  have h3 : wt x = (Finset.univ.filter (fun i : Fin 13 => x i = true)).card := rfl
  omega

def Dep (c : Fin 13 → Fin 13) (α : Fin 13) (f : (Fin 13 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 13 → Bool, (∀ v, c v = α → x v = y v) → f x = f y

-- f behaves like the AND of T around the point x, T holds s and t, and x leaves u out
def R (f : (Fin 13 → Bool) → Bool) (s t u : Fin 13) : Prop :=
  ∃ (T : Finset (Fin 13)) (x : Fin 13 → Bool), s ∈ T ∧ t ∈ T ∧ (∀ v ∈ T, x v = true) ∧
    x u = false ∧ f x = true ∧
    ∀ z : Fin 13 → Bool, (∃ v ∈ T, z v = false) → wt z ≤ wt x → f z = false

lemma off_wt (x : Fin 13 → Bool) (v : Fin 13) : wt (fun w => x w && decide (w ≠ v)) ≤ wt x := by
  refine wt_mono _ _ ?_
  intro w hw
  simp only [Bool.and_eq_true] at hw
  exact hw.1

lemma R_dep2 (c : Fin 13 → Fin 13) (α β : Fin 13) (p q f : (Fin 13 → Bool) → Bool)
    (hp : Dep c α p) (hq : Dep c β q)
    (hf : ∀ x y : Fin 13 → Bool, p x = p y → q x = q y → f x = f y)
    (T : Finset (Fin 13)) (x : Fin 13 → Bool) (hx : f x = true)
    (hZ : ∀ z : Fin 13 → Bool, (∃ v ∈ T, z v = false) → wt z ≤ wt x → f z = false) :
    ∀ v ∈ T, c v = α ∨ c v = β := by
  intro v hv
  by_contra h
  have hz := hZ (fun w => x w && decide (w ≠ v)) ⟨v, hv, by simp⟩ (off_wt x v)
  have e1 : p x = p (fun w => x w && decide (w ≠ v)) := hp _ _ (fun w hw => by
    have hne : w ≠ v := by
      rintro rfl
      exact h (Or.inl hw)
    simp [hne])
  have e2 : q x = q (fun w => x w && decide (w ≠ v)) := hq _ _ (fun w hw => by
    have hne : w ≠ v := by
      rintro rfl
      exact h (Or.inr hw)
    simp [hne])
  exact Bool.noConfusion (hx.symm.trans ((hf _ _ e1 e2).trans hz))

lemma R_dep (c : Fin 13 → Fin 13) (α : Fin 13) (f : (Fin 13 → Bool) → Bool) (hf : Dep c α f)
    (T : Finset (Fin 13)) (x : Fin 13 → Bool) (hx : f x = true)
    (hZ : ∀ z : Fin 13 → Bool, (∃ v ∈ T, z v = false) → wt z ≤ wt x → f z = false) :
    ∀ v ∈ T, c v = α := by
  intro v hv
  rcases R_dep2 c α α f f f hf hf (fun _ _ e _ => e) T x hx hZ v hv with h | h <;> exact h

lemma R_nonconst (f : (Fin 13 → Bool) → Bool) (s t u : Fin 13) (h : ∀ x y, f x = f y) :
    ¬ R f s t u := by
  rintro ⟨T, x, hs, -, -, -, hfx, hZ⟩
  have hz := hZ (fun _ => false) ⟨s, hs, rfl⟩ (wt_mono _ _ (fun v hv => Bool.noConfusion hv))
  exact Bool.noConfusion (hfx.symm.trans ((h _ _).trans hz))

lemma R_distinct (f : (Fin 13 → Bool) → Bool) (s t u s' t' u' : Fin 13)
    (h1 : u = s' ∨ u = t') (h2 : u' = s ∨ u' = t) : R f s t u → R f s' t' u' → False := by
  rintro ⟨T, x, hs, ht, -, hxu, hfx, hZ⟩ ⟨T', x', hs', ht', -, hxu', hfx', hZ'⟩
  rcases le_total (wt x) (wt x') with h | h
  · have hu : u ∈ T' := by
      rcases h1 with e | e
      · rw [e]; exact hs'
      · rw [e]; exact ht'
    exact Bool.noConfusion (hfx.symm.trans (hZ' x ⟨u, hu, hxu⟩ h))
  · have hu : u' ∈ T := by
      rcases h2 with e | e
      · rw [e]; exact hs
      · rw [e]; exact ht
    exact Bool.noConfusion (hfx'.symm.trans (hZ x' ⟨u', hu, hxu'⟩ h))

lemma descend1 (c : Fin 13 → Fin 13) (α β : Fin 13) (p q f : (Fin 13 → Bool) → Bool)
    (hαβ : α ≠ β) (hp : Dep c α p) (hq : Dep c β q)
    (hf : (∀ x, f x = (p x && q x)) ∨ (∀ x, f x = (p x || q x)))
    (s t u : Fin 13) (hs : c s = α) (ht : c t = α) (hR : R f s t u) : R p s t u := by
  obtain ⟨T, x, hsT, htT, hTx, hxu, hfx, hZ⟩ := hR
  rcases hf with hf | hf
  · have hpq := hfx
    rw [hf x] at hpq
    simp only [Bool.and_eq_true] at hpq
    obtain ⟨hpx, hqx⟩ := hpq
    refine ⟨T.filter (fun v => c v = α), fun v => x v && decide (c v = α),
      Finset.mem_filter.mpr ⟨hsT, hs⟩, Finset.mem_filter.mpr ⟨htT, ht⟩, ?_, ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨hvT, hvα⟩ := Finset.mem_filter.mp hv
      simp [hTx v hvT, hvα]
    · simp [hxu]
    · rw [← hpx]
      exact hp _ _ (fun v hv => by simp [hv])
    · rintro z ⟨v, hv, hzv⟩ hwt
      obtain ⟨hvT, hvα⟩ := Finset.mem_filter.mp hv
      by_contra hpz
      have hpz' : p z = true := by simpa using hpz
      have hpy : p (fun w => (z w && decide (c w = α)) || (x w && decide (c w = β))) = p z :=
        hp _ _ (fun w hw => by simp [hw, hαβ])
      have hqy : q (fun w => (z w && decide (c w = α)) || (x w && decide (c w = β))) = q x :=
        hq _ _ (fun w hw => by simp [hw, hαβ.symm])
      have hfy : f (fun w => (z w && decide (c w = α)) || (x w && decide (c w = β))) = true := by
        rw [hf, hpy, hqy, hpz', hqx]
        rfl
      have hyv : (fun w => (z w && decide (c w = α)) || (x w && decide (c w = β))) v = false := by
        simp [hzv, hvα, hαβ]
      have hw1 : wt (fun w => (z w && decide (c w = α)) || (x w && decide (c w = β))) ≤
          wt z + wt (fun w => x w && decide (c w = β)) := by
        refine wt_or_le _ _ _ ?_
        intro w hw
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw
        rcases hw with hw | hw
        · exact Or.inl hw.1
        · right
          simp only [Bool.and_eq_true]
          exact hw
      have hw2 := wt_split c α β hαβ x
      have hw3 : wt (fun w => (z w && decide (c w = α)) || (x w && decide (c w = β))) ≤ wt x := by
        omega
      have hfy0 := hZ _ ⟨v, hvT, hyv⟩ hw3
      exact Bool.noConfusion (hfy.symm.trans hfy0)
  · have hqx : q x = false := by
      by_contra h
      have h' : q x = true := by simpa using h
      have e : q (fun w => x w && decide (c w = β)) = q x := hq _ _ (fun w hw => by simp [hw])
      have hfy : f (fun w => x w && decide (c w = β)) = true := by
        rw [hf, e, h']
        simp
      have hfy0 := hZ (fun w => x w && decide (c w = β)) ⟨s, hsT, by simp [hs, hαβ]⟩
        (wt_mono _ _ (fun w hw => by
          simp only [Bool.and_eq_true] at hw
          exact hw.1))
      exact Bool.noConfusion (hfy.symm.trans hfy0)
    have hpx : p x = true := by
      have h := hfx
      rw [hf x, hqx] at h
      simpa using h
    refine ⟨T, x, hsT, htT, hTx, hxu, hpx, ?_⟩
    intro z hz hwt
    have h := hZ z hz hwt
    rw [hf z] at h
    simp only [Bool.or_eq_false_iff] at h
    exact h.1

lemma descend (c : Fin 13 → Fin 13) (α β : Fin 13) (p q f : (Fin 13 → Bool) → Bool)
    (hαβ : α ≠ β) (hp : Dep c α p) (hq : Dep c β q)
    (hf : (∀ x, f x = (p x && q x)) ∨ (∀ x, f x = (p x || q x)))
    (s t u : Fin 13) (hst : c s = c t) (hR : R f s t u) : R p s t u ∨ R q s t u := by
  have hlab : c s = α ∨ c s = β := by
    obtain ⟨T, x, hsT, -, -, -, hfx, hZ⟩ := hR
    refine R_dep2 c α β p q f hp hq ?_ T x hfx hZ s hsT
    intro x y e1 e2
    rcases hf with hf | hf <;> rw [hf x, hf y, e1, e2]
  rcases hlab with h | h
  · exact Or.inl (descend1 c α β p q f hαβ hp hq hf s t u h (hst ▸ h) hR)
  · exact Or.inr (descend1 c β α q p f hαβ.symm hq hp
      (hf.imp (fun h x => (h x).trans (Bool.and_comm _ _)) (fun h x => (h x).trans (Bool.or_comm _ _)))
      s t u h (hst ▸ h) hR)

lemma gate_form (gs : List Gate) (op : GateOp) (inputs : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : inputs.length ≤ 2) :
    (∀ x y : Fin 13 → Bool,
      op.eval (inputs.map fun i => W gs i x) = op.eval (inputs.map fun i => W gs i y)) ∨
    ∃ a b : ℕ, (∀ x : Fin 13 → Bool, op.eval (inputs.map fun i => W gs i x) = (W gs a x && W gs b x)) ∨
      (∀ x : Fin 13 → Bool, op.eval (inputs.map fun i => W gs i x) = (W gs a x || W gs b x)) := by
  match inputs, hlen with
  | [], _ =>
    left
    intro x y
    rfl
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl
    · left
      intro x
      simp [GateOp.eval]
    · right
      intro x
      simp [GateOp.eval]
  | [a, b], _ =>
    right
    refine ⟨a, b, ?_⟩
    rcases hop with rfl | rfl
    · left
      intro x
      simp [GateOp.eval]
    · right
      intro x
      simp [GateOp.eval]
  | _ :: _ :: _ :: _, h =>
    simp only [List.length_cons] at h
    omega

def InvF (c : Fin 13 → Fin 13) (gs : List Gate) : Prop := ∀ j : ℕ, ∃ α : Fin 13, Dep c α (W gs j)

def Triple (gs : List Gate) : Prop :=
  ∃ j0 j1 j2 : ℕ, R (W gs j0) 1 3 2 ∧ R (W gs j1) 1 2 3 ∧ R (W gs j2) 2 3 1

lemma inv0 : InvF id [] := by
  intro j
  by_cases hj : j < 13
  · refine ⟨⟨j, hj⟩, ?_⟩
    intro x y h
    show (List.ofFn x).getD j false = (List.ofFn y).getD j false
    rw [ofFn_getD x j hj, ofFn_getD y j hj]
    exact h _ rfl
  · refine ⟨0, ?_⟩
    intro x y _
    show (List.ofFn x).getD j false = (List.ofFn y).getD j false
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma inv_snoc (c : Fin 13 → Fin 13) (gs : List Gate) (g : Gate) (hI : InvF c gs) (α : Fin 13)
    (hα : Dep c α (fun x => g.op.eval (g.inputs.map fun i => W gs i x))) : InvF c (gs ++ [g]) := by
  intro j
  by_cases h1 : j < 13 + gs.length
  · obtain ⟨γ, hγ⟩ := hI j
    refine ⟨γ, fun x y h => ?_⟩
    rw [W_snoc, W_snoc]
    simp only [h1, ↓reduceIte]
    exact hγ x y h
  · by_cases h2 : j = 13 + gs.length
    · refine ⟨α, fun x y h => ?_⟩
      subst h2
      rw [W_snoc, W_snoc]
      simp only [lt_irrefl, ↓reduceIte]
      exact hα x y h
    · refine ⟨0, fun x y _ => ?_⟩
      rw [W_snoc, W_snoc]
      simp only [h1, h2, ↓reduceIte]

lemma dep_merge (c : Fin 13 → Fin 13) (α β γ : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (h : Dep c γ f) : Dep (fun v => if c v = β then α else c v) (if γ = β then α else γ) f := by
  intro x y hxy
  refine h x y (fun v hv => hxy v ?_)
  subst hv
  rfl

lemma dep_gate (c : Fin 13 → Fin 13) (α : Fin 13) (p q f : (Fin 13 → Bool) → Bool)
    (hp : Dep c α p) (hq : Dep c α q)
    (hf : (∀ x, f x = (p x && q x)) ∨ (∀ x, f x = (p x || q x))) : Dep c α f := by
  intro x y h
  rcases hf with hf | hf <;> rw [hf x, hf y, hp x y h, hq x y h]

lemma R_snoc (gs : List Gate) (g : Gate) (j : ℕ) (s t u : Fin 13)
    (h : R (W (gs ++ [g]) j) s t u) :
    R (W gs j) s t u ∨ R (fun x => g.op.eval (g.inputs.map fun i => W gs i x)) s t u := by
  by_cases h1 : j < 13 + gs.length
  · left
    have e : W (gs ++ [g]) j = W gs j := by
      funext x
      rw [W_snoc]
      simp only [h1, ↓reduceIte]
    rwa [e] at h
  · by_cases h2 : j = 13 + gs.length
    · right
      subst h2
      have e : W (gs ++ [g]) (13 + gs.length) =
          fun x => g.op.eval (g.inputs.map fun i => W gs i x) := by
        funext x
        rw [W_snoc]
        simp only [lt_irrefl, ↓reduceIte]
      rwa [e] at h
    · exfalso
      refine R_nonconst _ s t u (fun x y => ?_) h
      rw [W_snoc, W_snoc]
      simp only [h1, h2, ↓reduceIte]

lemma R_same (c : Fin 13 → Fin 13) (gs : List Gate) (hI : InvF c gs) (j : ℕ) (s t u : Fin 13)
    (h : R (W gs j) s t u) : c s = c t := by
  obtain ⟨γ, hγ⟩ := hI j
  obtain ⟨T, x, hs, ht, -, -, hfx, hZ⟩ := h
  exact (R_dep c γ _ hγ T x hfx hZ s hs).trans (R_dep c γ _ hγ T x hfx hZ t ht).symm

lemma triple_down (c : Fin 13 → Fin 13) (gs : List Gate) (g : Gate) (a b : ℕ) (α β : Fin 13)
    (hI : InvF c gs) (hα : Dep c α (W gs a)) (hβ : Dep c β (W gs b)) (hαβ : α ≠ β)
    (hf : (∀ x : Fin 13 → Bool, g.op.eval (g.inputs.map fun i => W gs i x) = (W gs a x && W gs b x)) ∨
      (∀ x : Fin 13 → Bool, g.op.eval (g.inputs.map fun i => W gs i x) = (W gs a x || W gs b x)))
    (hT : Triple (gs ++ [g])) : Triple gs := by
  obtain ⟨j0, j1, j2, h0, h1, h2⟩ := hT
  rcases R_snoc gs g j0 1 3 2 h0 with o0 | t0
  · rcases R_snoc gs g j1 1 2 3 h1 with o1 | t1
    · rcases R_snoc gs g j2 2 3 1 h2 with o2 | t2
      · exact ⟨j0, j1, j2, o0, o1, o2⟩
      · have e : c 2 = c 3 :=
          (R_same c gs hI j1 1 2 3 o1).symm.trans (R_same c gs hI j0 1 3 2 o0)
        rcases descend c α β _ _ _ hαβ hα hβ hf 2 3 1 e t2 with r | r
        · exact ⟨j0, j1, a, o0, o1, r⟩
        · exact ⟨j0, j1, b, o0, o1, r⟩
    · rcases R_snoc gs g j2 2 3 1 h2 with o2 | t2
      · have e : c 1 = c 2 :=
          (R_same c gs hI j0 1 3 2 o0).trans (R_same c gs hI j2 2 3 1 o2).symm
        rcases descend c α β _ _ _ hαβ hα hβ hf 1 2 3 e t1 with r | r
        · exact ⟨j0, a, j2, o0, r, o2⟩
        · exact ⟨j0, b, j2, o0, r, o2⟩
      · exact (R_distinct _ 1 2 3 2 3 1 (Or.inr rfl) (Or.inl rfl) t1 t2).elim
  · rcases R_snoc gs g j1 1 2 3 h1 with o1 | t1
    · rcases R_snoc gs g j2 2 3 1 h2 with o2 | t2
      · have e : c 1 = c 3 :=
          (R_same c gs hI j1 1 2 3 o1).trans (R_same c gs hI j2 2 3 1 o2)
        rcases descend c α β _ _ _ hαβ hα hβ hf 1 3 2 e t0 with r | r
        · exact ⟨a, j1, j2, r, o1, o2⟩
        · exact ⟨b, j1, j2, r, o1, o2⟩
      · exact (R_distinct _ 1 3 2 2 3 1 (Or.inl rfl) (Or.inl rfl) t0 t2).elim
    · exact (R_distinct _ 1 3 2 1 2 3 (Or.inr rfl) (Or.inr rfl) t0 t1).elim

lemma main : ∀ gs : List Gate,
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∃ c : Fin 13 → Fin 13, InvF c gs ∧ 13 ≤ (Finset.univ.image c).card + gs.length ∧
      (Triple gs → 14 ≤ (Finset.univ.image c).card + gs.length) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨id, inv0, by simp, ?_⟩
    rintro ⟨j0, -, -, h0, -, -⟩
    exact absurd (R_same id [] inv0 j0 1 3 2 h0) (show (1 : Fin 13) ≠ 3 by decide)
  | append_singleton gs g ih =>
    intro hall
    obtain ⟨c, hI, hA, hB⟩ := ih (fun g' h => hall g' (List.mem_append_left _ h))
    have hg := hall g (List.mem_append_right _ (List.mem_singleton_self g))
    have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
    rcases gate_form gs g.op g.inputs hg.1 hg.2 with hconst | ⟨a, b, hf⟩
    · refine ⟨c, inv_snoc c gs g hI 0 (fun x y _ => hconst x y), by omega, fun _ => by omega⟩
    · obtain ⟨α, hα⟩ := hI a
      obtain ⟨β, hβ⟩ := hI b
      by_cases hαβ : α = β
      · subst hαβ
        exact ⟨c, inv_snoc c gs g hI α (dep_gate c α _ _ _ hα hβ hf), by omega, fun _ => by omega⟩
      · have hcard : (Finset.univ.image c).card ≤
            (Finset.univ.image (fun v => if c v = β then α else c v)).card + 1 := by
          have hsub : Finset.univ.image c ⊆
              insert β (Finset.univ.image (fun v => if c v = β then α else c v)) := by
            intro t ht
            obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ht
            by_cases h : c v = β
            · exact Finset.mem_insert.mpr (Or.inl h)
            · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, ?_⟩))
              simp [h]
          exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        have hα1 := dep_merge c α β α _ hα
        have hβ1 := dep_merge c α β β _ hβ
        simp only [ite_self] at hα1
        simp only [↓reduceIte] at hβ1
        refine ⟨fun v => if c v = β then α else c v,
          inv_snoc _ gs g (fun j => ?_) α (dep_gate _ α _ _ _ hα1 hβ1 hf), by omega, ?_⟩
        · obtain ⟨γ, hγ⟩ := hI j
          exact ⟨_, dep_merge c α β γ _ hγ⟩
        · intro hT
          have h14 := hB (triple_down c gs g a b α β hI hα hβ hαβ hf hT)
          omega

lemma zero_ext (z : Fin 13 → Bool) (v : Fin 13) (hzv : z v = false) (hwt : wt z ≤ 6) :
    ∃ z' : Fin 13 → Bool, (∀ w, z w = true → z' w = true) ∧ z' v = false ∧ wt z' = 6 := by
  have hsub : Finset.univ.filter (fun i : Fin 13 => z i = true) ⊆ Finset.univ.erase v := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ w⟩
    rintro rfl
    rw [hzv] at hw
    exact Bool.noConfusion hw
  have h12 : 6 ≤ (Finset.univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    simp
  obtain ⟨U, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq hsub hwt h12
  refine ⟨fun w => decide (w ∈ U), ?_, ?_, ?_⟩
  · intro w hw
    have hm : w ∈ U := h1 (by simpa using hw)
    simpa using hm
  · have hm : v ∉ U := fun h => (Finset.mem_erase.mp (h2 h)).1 rfl
    simpa using hm
  · have e : Finset.univ.filter (fun i : Fin 13 => (fun w => decide (w ∈ U)) i = true) = U := by
      ext w
      simp
    show (Finset.univ.filter (fun i : Fin 13 => (fun w => decide (w ∈ U)) i = true)).card = 6
    rw [e]
    exact h3

lemma mkZ (gates : List Gate) (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (o : ℕ)
    (L : Finset (Fin 13)) (S : Fin 13 → Bool) (hS6 : wt S = 6)
    (h0 : ∀ z : Fin 13 → Bool, wt z = 6 → (∃ v ∈ L, z v = false) → W gates o z = false) :
    ∀ z : Fin 13 → Bool, (∃ v ∈ L, z v = false) → wt z ≤ wt S → W gates o z = false := by
  rintro z ⟨v, hv, hzv⟩ hwt
  obtain ⟨z', hle, hz'v, hw⟩ := zero_ext z v hzv (hS6 ▸ hwt)
  have h := h0 z' hw ⟨v, hv, hz'v⟩
  by_contra hne
  have ht : W gates o z = true := by simpa using hne
  exact Bool.noConfusion ((W_mono gates hmono o z z' hle ht).symm.trans h)

def S0 : Fin 13 → Bool := fun u => decide (u ∈ ({0, 1, 3, 6, 7, 9} : Finset (Fin 13)))

lemma w6_0 : wt S0 = 6 := by decide

lemma t0 : decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 0)), S0 v = true) = true := by decide

lemma img0 : ∀ v ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 0)) := by decide

lemma on0 : ∀ v ∈ ({0, 1, 3, 9} : Finset (Fin 13)), S0 v = true := by decide

def S1 : Fin 13 → Bool := fun u => decide (u ∈ ({1, 2, 4, 6, 7, 10} : Finset (Fin 13)))

lemma w6_1 : wt S1 = 6 := by decide

lemma t1 : decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 1)), S1 v = true) = true := by decide

lemma img1 : ∀ v ∈ ({1, 2, 4, 10} : Finset (Fin 13)), v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 1)) := by decide

lemma on1 : ∀ v ∈ ({1, 2, 4, 10} : Finset (Fin 13)), S1 v = true := by decide

def S2 : Fin 13 → Bool := fun u => decide (u ∈ ({2, 3, 5, 6, 7, 11} : Finset (Fin 13)))

lemma w6_2 : wt S2 = 6 := by decide

lemma t2 : decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 2)), S2 v = true) = true := by decide

lemma img2 : ∀ v ∈ ({2, 3, 5, 11} : Finset (Fin 13)), v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 2)) := by decide

lemma on2 : ∀ v ∈ ({2, 3, 5, 11} : Finset (Fin 13)), S2 v = true := by decide

lemma cover : ∀ v : Fin 13, v ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v ∈ ({1, 2, 4, 10} : Finset (Fin 13)) ∨ v ∈ ({2, 3, 5, 11} : Finset (Fin 13)) ∨ v ∈ ({6, 7, 8, 12} : Finset (Fin 13)) := by decide

end PEqualNP.Outside.L_meta_1018

theorem PEqualNP.Outside.L_meta_1018 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 3 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin 13 → Bool, ((Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 6 ∨ (Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 7) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 0⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 0)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 1⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 1)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 2⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 2)), x v = true)) → 9 ≤ gates.length := by
  intro gates out hg hc
  obtain ⟨c, hI, -, hB⟩ := PEqualNP.Outside.L_meta_1018.main gates hg
  have hmono : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g h => (hg g h).1
  obtain ⟨a0, ha0⟩ := hI (out 0)
  obtain ⟨a1, ha1⟩ := hI (out 1)
  obtain ⟨a2, ha2⟩ := hI (out 2)
  have x0 : PEqualNP.Outside.L_meta_1018.W gates (out 0) PEqualNP.Outside.L_meta_1018.S0 = true := (hc _ (Or.inl PEqualNP.Outside.L_meta_1018.w6_0)).1.trans PEqualNP.Outside.L_meta_1018.t0
  have x1 : PEqualNP.Outside.L_meta_1018.W gates (out 1) PEqualNP.Outside.L_meta_1018.S1 = true := (hc _ (Or.inl PEqualNP.Outside.L_meta_1018.w6_1)).2.1.trans PEqualNP.Outside.L_meta_1018.t1
  have x2 : PEqualNP.Outside.L_meta_1018.W gates (out 2) PEqualNP.Outside.L_meta_1018.S2 = true := (hc _ (Or.inl PEqualNP.Outside.L_meta_1018.w6_2)).2.2.trans PEqualNP.Outside.L_meta_1018.t2
  have z0 := PEqualNP.Outside.L_meta_1018.mkZ gates hmono (out 0) ({0, 1, 3, 9} : Finset (Fin 13)) PEqualNP.Outside.L_meta_1018.S0 PEqualNP.Outside.L_meta_1018.w6_0
    (fun z hz hv => (hc z (Or.inl hz)).1.trans (decide_eq_false (fun h => by
      obtain ⟨v, hv, hzv⟩ := hv
      exact Bool.noConfusion ((h v (PEqualNP.Outside.L_meta_1018.img0 v hv)).symm.trans hzv))))
  have z1 := PEqualNP.Outside.L_meta_1018.mkZ gates hmono (out 1) ({1, 2, 4, 10} : Finset (Fin 13)) PEqualNP.Outside.L_meta_1018.S1 PEqualNP.Outside.L_meta_1018.w6_1
    (fun z hz hv => (hc z (Or.inl hz)).2.1.trans (decide_eq_false (fun h => by
      obtain ⟨v, hv, hzv⟩ := hv
      exact Bool.noConfusion ((h v (PEqualNP.Outside.L_meta_1018.img1 v hv)).symm.trans hzv))))
  have z2 := PEqualNP.Outside.L_meta_1018.mkZ gates hmono (out 2) ({2, 3, 5, 11} : Finset (Fin 13)) PEqualNP.Outside.L_meta_1018.S2 PEqualNP.Outside.L_meta_1018.w6_2
    (fun z hz hv => (hc z (Or.inl hz)).2.2.trans (decide_eq_false (fun h => by
      obtain ⟨v, hv, hzv⟩ := hv
      exact Bool.noConfusion ((h v (PEqualNP.Outside.L_meta_1018.img2 v hv)).symm.trans hzv))))
  have hT : PEqualNP.Outside.L_meta_1018.Triple gates :=
    ⟨out 0, out 1, out 2,
      ⟨_, PEqualNP.Outside.L_meta_1018.S0, by decide, by decide, PEqualNP.Outside.L_meta_1018.on0, by decide, x0, z0⟩,
      ⟨_, PEqualNP.Outside.L_meta_1018.S1, by decide, by decide, PEqualNP.Outside.L_meta_1018.on1, by decide, x1, z1⟩,
      ⟨_, PEqualNP.Outside.L_meta_1018.S2, by decide, by decide, PEqualNP.Outside.L_meta_1018.on2, by decide, x2, z2⟩⟩
  have h14 := hB hT
  have hL0 := PEqualNP.Outside.L_meta_1018.R_dep c a0 _ ha0 _ PEqualNP.Outside.L_meta_1018.S0 x0 z0
  have hL1 := PEqualNP.Outside.L_meta_1018.R_dep c a1 _ ha1 _ PEqualNP.Outside.L_meta_1018.S1 x1 z1
  have hL2 := PEqualNP.Outside.L_meta_1018.R_dep c a2 _ ha2 _ PEqualNP.Outside.L_meta_1018.S2 x2 z2
  have e1 : a1 = a0 := (hL1 1 (by decide)).symm.trans (hL0 1 (by decide))
  have e2 : a2 = a0 := (hL2 3 (by decide)).symm.trans (hL0 3 (by decide))
  have hsub : Finset.univ.image c ⊆ ({a0, c 6, c 7, c 8, c 12} : Finset (Fin 13)) := by
    intro t ht
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ht
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases PEqualNP.Outside.L_meta_1018.cover v with h | h | h | h
    · exact Or.inl (hL0 v h)
    · exact Or.inl ((hL1 v h).trans e1)
    · exact Or.inl ((hL2 v h).trans e2)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have h5 : (Finset.univ.image c).card ≤ 5 := (Finset.card_le_card hsub).trans Finset.card_le_five
  omega
