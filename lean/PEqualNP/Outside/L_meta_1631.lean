import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1631

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (W gs x).getD t false = true → (W gs y).getD t false = true

lemma mono_nil {n : ℕ} : Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := ofFn_getD_true x t ht
  exact (ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

lemma mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Mono (n := n) gs) :
    Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [W_val] at ht ⊢
  by_cases htt : t = n + gs.length
  · rw [if_pos htt] at ht ⊢
    rcases hop with hand | hor
    · rw [hand] at ht ⊢
      exact (all_true _ _).mpr (fun i hi => h x y hxy i ((all_true _ _).mp ht i hi))
    · rw [hor] at ht ⊢
      obtain ⟨i, hi, hti⟩ := (any_true _ _).mp ht
      exact (any_true _ _).mpr ⟨i, hi, h x y hxy i hti⟩
  · rw [if_neg htt] at ht ⊢
    exact h x y hxy t ht

lemma mono_all {n : ℕ} (gs : List Gate) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => intro _; exact mono_nil
  | append_singleton l a ih =>
    intro h
    exact mono_step l a (h a (by simp)) (ih (fun g hg => h g (by simp [hg])))

lemma eval_mono {n : ℕ} (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hx : Circuit.eval ⟨gs, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn y) = true :=
  mono_all gs h x y hxy o hx

lemma ev_mono {N : ℕ} (gates : List Gate) (ev : ℕ → (Fin N → Bool) → Bool)
    (hev : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = Circuit.eval ⟨gates, w⟩ (List.ofFn x))
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ) (x y : Fin N → Bool)
    (hxy : ∀ i, x i = true → y i = true) (hx : ev w x = true) : ev w y = true := by
  rw [hev] at hx ⊢
  exact eval_mono gates w hg x y hxy hx

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, ((∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) ↔
    ∀ t : Fin N, ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false ∧ (p0 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p0)) = true) ∧ (p1 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, ev (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧ ev (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧ (t ≠ i0 → ev (o t) (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 → ev (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true)) := by
  intro q N L i0 p0 p1 hq hN hcard hcap hjoin h01 h0 h1 gates hg hin hwire ev hev o
  have hg' : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hgm => (hg g hgm).1
  constructor
  · intro H t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hF : ((fun v : Fin N => decide (v ∉ L t)) p0 = true ∨ (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨
          ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true) := by
        by_cases hti : t = i0
        · right
          right
          intro u hu
          rw [hti]
          exact decide_eq_true hu
        · by_cases hp0 : p0 ∈ L t
          · right
            left
            have hp1 : p1 ∉ L t := by
              intro hp1
              exact h01 (Finset.card_le_one.mp (le_of_eq (hcap t i0 hti)) p0
                (Finset.mem_inter.mpr ⟨hp0, h0⟩) p1 (Finset.mem_inter.mpr ⟨hp1, h1⟩))
            exact decide_eq_true hp1
          · left
            exact decide_eq_true hp0
      have h := H t (fun v : Fin N => decide (v ∉ L t)) hF
      refine h.trans (decide_eq_false ?_)
      rintro ⟨v, hv, hv2⟩
      have hv3 : v ∉ L t := by simpa using hv2
      exact hv3 hv
    · intro hp0
      have h := H t (fun v : Fin N => decide (v = p0)) (by left; simp)
      exact h.trans (decide_eq_true ⟨p0, hp0, by simp⟩)
    · intro hp1
      have h := H t (fun v : Fin N => decide (v = p1)) (by right; left; simp)
      exact h.trans (decide_eq_true ⟨p1, hp1, by simp⟩)
    · intro p hp
      constructor
      · have h := H t (fun v : Fin N => decide (v = p0 ∨ v = p)) (by left; simp)
        exact h.trans (decide_eq_true ⟨p, hp, by simp⟩)
      · have h := H t (fun v : Fin N => decide (v = p1 ∨ v = p)) (by right; left; simp)
        exact h.trans (decide_eq_true ⟨p, hp, by simp⟩)
    · intro hti
      have h := H t (fun v : Fin N => decide (v ∉ L i0)) (by right; right; intro u hu; simp [hu])
      obtain ⟨v, hv⟩ : ∃ v, v ∈ L t \ L i0 := by
        have hc := Finset.card_sdiff_add_card_inter (L t) (L i0)
        rw [hcap t i0 hti, hcard t] at hc
        have hpos : 0 < (L t \ L i0).card := by omega
        exact Finset.card_pos.mp hpos
      rw [Finset.mem_sdiff] at hv
      exact h.trans (decide_eq_true ⟨v, hv.1, by simp [hv.2]⟩)
    · intro w hw hw0 hw1
      rw [Finset.mem_inter] at hw
      have h := H t (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) (by right; right; intro u hu; simp [hu])
      exact h.trans (decide_eq_true ⟨w, hw.1, by simp⟩)
  · intro H t x hF
    obtain ⟨hz, he0, he1, hpair, hoff, hon⟩ := H t
    by_cases hex : ∃ v ∈ L t, x v = true
    · refine Eq.trans ?_ (decide_eq_true hex).symm
      obtain ⟨p, hp, hxp⟩ := hex
      by_cases hx0 : x p0 = true
      · refine ev_mono gates ev hev hg' (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) x ?_ (hpair p hp).1
        intro v hv
        have hv' : v = p0 ∨ v = p := by simpa using hv
        rcases hv' with h | h
        · rw [h]
          exact hx0
        · rw [h]
          exact hxp
      · by_cases hx1 : x p1 = true
        · refine ev_mono gates ev hev hg' (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) x ?_ (hpair p hp).2
          intro v hv
          have hv' : v = p1 ∨ v = p := by simpa using hv
          rcases hv' with h | h
          · rw [h]
            exact hx1
          · rw [h]
            exact hxp
        · have hall : ∀ u : Fin N, u ∉ L i0 → x u = true := by
            rcases hF with h | h | h
            · exact absurd h hx0
            · exact absurd h hx1
            · exact h
          by_cases hpi : p ∈ L i0
          · have hpn0 : p ≠ p0 := by
              intro h
              rw [h] at hxp
              exact hx0 hxp
            have hpn1 : p ≠ p1 := by
              intro h
              rw [h] at hxp
              exact hx1 hxp
            refine ev_mono gates ev hev hg' (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = p)) x ?_
              (hon p (Finset.mem_inter.mpr ⟨hp, hpi⟩) hpn0 hpn1)
            intro v hv
            have hv' : v ∉ L i0 ∨ v = p := by simpa using hv
            rcases hv' with h | h
            · exact hall v h
            · rw [h]
              exact hxp
          · have hti : t ≠ i0 := by
              intro h
              rw [h] at hp
              exact hpi hp
            refine ev_mono gates ev hev hg' (o t) (fun v : Fin N => decide (v ∉ L i0)) x ?_ (hoff hti)
            intro v hv
            have hv' : v ∉ L i0 := by simpa using hv
            exact hall v hv'
    · refine Eq.trans ?_ (decide_eq_false hex).symm
      cases hval : ev (o t) x with
      | false => rfl
      | true =>
        exfalso
        have h2 := ev_mono gates ev hev hg' (o t) x (fun v : Fin N => decide (v ∉ L t))
          (fun v hv => decide_eq_true (fun hvt => hex ⟨v, hvt, hv⟩)) hval
        exact Bool.noConfusion (h2.symm.trans hz)

end PEqualNP.Outside.L_meta_1631

theorem PEqualNP.Outside.L_meta_1631 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, ((∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) ↔
    ∀ t : Fin N, ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false ∧ (p0 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p0)) = true) ∧ (p1 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, ev (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧ ev (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧ (t ≠ i0 → ev (o t) (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 → ev (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true)) :=
  PEqualNP.Outside.L_meta_1631.main_aux
