import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1715

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def vl (gs : List Gate) (w : ℕ) (x : List Bool) : Bool := (run gs x).getD w false

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_len (gs : List Gate) : ∀ x : List Bool, (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => intro x; simp [run]
  | append_singleton gs g ih =>
    intro x
    rw [run_snoc, List.length_append, ih x]
    simp
    omega

theorem vl_snoc_lt (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ) (h : w < x.length + gs.length) :
    vl (gs ++ [g]) w x = vl gs w x := by
  unfold vl
  rw [run_snoc, List.getD_append _ _ _ _ (by rw [run_len]; exact h)]

theorem vl_snoc_eq (gs : List Gate) (g : Gate) (x : List Bool) :
    vl (gs ++ [g]) (x.length + gs.length) x = g.op.eval (g.inputs.map fun i => vl gs i x) := by
  unfold vl
  rw [run_snoc, List.getD_append_right _ _ _ _ (by rw [run_len])]
  simp [run_len]

theorem vl_ge (gs : List Gate) (w : ℕ) (x : List Bool) (h : x.length + gs.length ≤ w) :
    vl gs w x = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [run_len]; exact h)

def dg (gs : List Gate) (n : ℕ) (M : Finset ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) ((List.range n).map fun i => if i ∈ M then 1 else 0)

theorem dg_snoc (gs : List Gate) (g : Gate) (n : ℕ) (M : Finset ℕ) :
    dg (gs ++ [g]) n M = dg gs n M ++ [g.lineDegree (dg gs n M)] := by
  simp [dg, List.foldl_append]

theorem dg_len (gs : List Gate) (n : ℕ) (M : Finset ℕ) : (dg gs n M).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [dg]
  | append_singleton gs g ih =>
    rw [dg_snoc, List.length_append, ih]
    simp
    omega

def Z (gs : List Gate) (n : ℕ) (M : Finset ℕ) (w : ℕ) : Prop := (dg gs n M).getD w 0 = 0

theorem Z_snoc_lt (gs : List Gate) (g : Gate) (n : ℕ) (M : Finset ℕ) (w : ℕ) (h : w < n + gs.length) :
    Z (gs ++ [g]) n M w ↔ Z gs n M w := by
  unfold Z
  rw [dg_snoc, List.getD_append _ _ _ _ (by rw [dg_len]; exact h)]

theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) : (l.map f).sum = 0 ↔ ∀ i ∈ l, f i = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.forall_mem_cons]
    rw [← ih]
    omega

theorem max_zero (f : ℕ → ℕ) (l : List ℕ) : (l.map f).foldr max 0 = 0 ↔ ∀ i ∈ l, f i = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, List.forall_mem_cons]
    rw [← ih]
    omega

theorem ld_zero (g : Gate) (d : List ℕ) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.lineDegree d = 0 ↔ ∀ i ∈ g.inputs, d.getD i 0 = 0 := by
  unfold Gate.lineDegree
  rcases hop with h | h
  · rw [if_pos h]
    exact sum_zero _ _
  · rw [if_neg (by rw [h]; intro hh; cases hh)]
    exact max_zero _ _

theorem Z_snoc_eq (gs : List Gate) (g : Gate) (n : ℕ) (M : Finset ℕ)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    Z (gs ++ [g]) n M (n + gs.length) ↔ ∀ i ∈ g.inputs, Z gs n M i := by
  unfold Z
  rw [dg_snoc, List.getD_append_right _ _ _ _ (by rw [dg_len]), dg_len]
  simp only [Nat.sub_self, List.getD_cons_zero]
  exact ld_zero g _ hop

def Hyp (n : ℕ) (L P : Finset ℕ) (gs : List Gate) : Prop :=
  ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧ (∀ i ∈ g.inputs, i < n + k) ∧
    (g.op = GateOp.and → (∃ i ∈ g.inputs, Z gs n L i) ∨ ∀ h ∈ g.inputs, Z gs n P h)

def Good (n : ℕ) (L P : Finset ℕ) (gs : List Gate) : Prop :=
  ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ (∀ i ∈ g.inputs, i < n + k) ∧
    (g.op = GateOp.and → (∃ i ∈ g.inputs, Z gs n L i) ∨ ∀ h ∈ g.inputs, Z gs n P h)

theorem Hyp_prefix {n : ℕ} {L P : Finset ℕ} {gs : List Gate} {g : Gate} (h : Hyp n L P (gs ++ [g])) :
    Hyp n L P gs := by
  intro k g0 hk
  have hkl : k < gs.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hk
    cases hk
  obtain ⟨h1, h2, h3, h4⟩ := h k g0 (by rw [List.getElem?_append_left hkl]; exact hk)
  refine ⟨h1, h2, h3, fun hop => ?_⟩
  rcases h4 hop with ⟨i, hi, hz⟩ | hz
  · exact Or.inl ⟨i, hi, (Z_snoc_lt gs g n L i (by have := h3 i hi; omega)).1 hz⟩
  · exact Or.inr fun j hj => (Z_snoc_lt gs g n P j (by have := h3 j hj; omega)).1 (hz j hj)

theorem Hyp_last {n : ℕ} {L P : Finset ℕ} {gs : List Gate} {g : Gate} (h : Hyp n L P (gs ++ [g])) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧
    (∀ i ∈ g.inputs, i < n + gs.length) ∧
    (g.op = GateOp.and → (∃ i ∈ g.inputs, Z gs n L i) ∨ ∀ h ∈ g.inputs, Z gs n P h) := by
  obtain ⟨h1, h2, h3, h4⟩ := h gs.length g (by simp)
  refine ⟨h1, h2, h3, fun hop => ?_⟩
  rcases h4 hop with ⟨i, hi, hz⟩ | hz
  · exact Or.inl ⟨i, hi, (Z_snoc_lt gs g n L i (h3 i hi)).1 hz⟩
  · exact Or.inr fun j hj => (Z_snoc_lt gs g n P j (h3 j hj)).1 (hz j hj)

theorem Good_snoc {n : ℕ} {L P : Finset ℕ} {gs : List Gate} {g : Gate} (hG : Good n L P gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length = 2)
    (hin : ∀ i ∈ g.inputs, i < n + gs.length)
    (hkm : g.op = GateOp.and → (∃ i ∈ g.inputs, Z gs n L i) ∨ ∀ h ∈ g.inputs, Z gs n P h) :
    Good n L P (gs ++ [g]) := by
  intro k g0 hk
  rcases Nat.lt_or_ge k gs.length with hkl | hkl
  · rw [List.getElem?_append_left hkl] at hk
    obtain ⟨h1, h2, h3, h4⟩ := hG k g0 hk
    refine ⟨h1, h2, h3, fun hop0 => ?_⟩
    rcases h4 hop0 with ⟨i, hi, hz⟩ | hz
    · exact Or.inl ⟨i, hi, (Z_snoc_lt gs g n L i (by have := h3 i hi; omega)).2 hz⟩
    · exact Or.inr fun j hj => (Z_snoc_lt gs g n P j (by have := h3 j hj; omega)).2 (hz j hj)
  · have hke : k = gs.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by simp; omega)] at hk
      cases hk
    subst hke
    have hgg : g = g0 := by simpa using hk
    subst hgg
    refine ⟨hop, hl, hin, fun hop0 => ?_⟩
    rcases hkm hop0 with ⟨i, hi, hz⟩ | hz
    · exact Or.inl ⟨i, hi, (Z_snoc_lt gs g n L i (hin i hi)).2 hz⟩
    · exact Or.inr fun j hj => (Z_snoc_lt gs g n P j (hin j hj)).2 (hz j hj)

def St (n : ℕ) (gs' : List Gate) (F : List Bool → Bool) (ZF : Finset ℕ → Prop) : Prop :=
  (∀ x : List Bool, x.length = n → F x = false) ∨ (∀ x : List Bool, x.length = n → F x = true) ∨
  ∃ w', w' < n + gs'.length ∧ (∀ x : List Bool, x.length = n → F x = vl gs' w' x) ∧
    ∀ M : Finset ℕ, ZF M → Z gs' n M w'

def St4 (n : ℕ) (L P : Finset ℕ) (gs' : List Gate) (F : List Bool → Bool) (ZF : Finset ℕ → Prop) :
    Prop :=
  St n gs' F ZF ∨ ∃ g' : Gate, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 ∧
    (∀ a ∈ g'.inputs, a < n + gs'.length) ∧
    (g'.op = GateOp.and → (∃ i ∈ g'.inputs, Z gs' n L i) ∨ ∀ h ∈ g'.inputs, Z gs' n P h) ∧
    (∀ x : List Bool, x.length = n → F x = g'.op.eval (g'.inputs.map fun i => vl gs' i x)) ∧
    ∀ M : Finset ℕ, ZF M → ∀ i ∈ g'.inputs, Z gs' n M i

theorem st1_congr {n : ℕ} {gs' : List Gate} {F G : List Bool → Bool} {ZF ZG : Finset ℕ → Prop}
    (h : ∀ x : List Bool, x.length = n → F x = G x) (hz : ∀ M, ZF M → ZG M) :
    St n gs' G ZG → St n gs' F ZF := by
  rintro (h1 | h1 | ⟨w', hw', h1, h2⟩)
  · exact Or.inl fun x hx => (h x hx).trans (h1 x hx)
  · exact Or.inr (Or.inl fun x hx => (h x hx).trans (h1 x hx))
  · exact Or.inr (Or.inr ⟨w', hw', fun x hx => (h x hx).trans (h1 x hx), fun M hM => h2 M (hz M hM)⟩)

theorem st_congr {n : ℕ} {L P : Finset ℕ} {gs' : List Gate} {F G : List Bool → Bool}
    {ZF ZG : Finset ℕ → Prop}
    (h : ∀ x : List Bool, x.length = n → F x = G x) (hz : ∀ M, ZF M → ZG M) :
    St4 n L P gs' G ZG → St4 n L P gs' F ZF := by
  rintro (h1 | ⟨g', a, b, c, d, e, f⟩)
  · exact Or.inl (st1_congr h hz h1)
  · exact Or.inr ⟨g', a, b, c, d, fun x hx => (h x hx).trans (e x hx), fun M hM => f M (hz M hM)⟩

theorem st_lift {n : ℕ} {gs' : List Gate} (g' : Gate) {F : List Bool → Bool} {ZF : Finset ℕ → Prop} :
    St n gs' F ZF → St n (gs' ++ [g']) F ZF := by
  rintro (h1 | h1 | ⟨w', hw', h1, h2⟩)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr ⟨w', by simp; omega, fun x hx => ?_, fun M hM => ?_⟩)
    · rw [h1 x hx, vl_snoc_lt gs' g' x w' (by rw [hx]; exact hw')]
    · exact (Z_snoc_lt gs' g' n M w' hw').2 (h2 M hM)

theorem st_and {n : ℕ} {L P : Finset ℕ} {gs' : List Gate} {F G : List Bool → Bool}
    {ZF ZG : Finset ℕ → Prop} (hF : St n gs' F ZF) (hG : St n gs' G ZG)
    (hkm : (ZF L ∨ ZG L) ∨ (ZF P ∧ ZG P)) :
    St4 n L P gs' (fun x => F x && G x) (fun M => ZF M ∧ ZG M) := by
  rcases hF with hF | hF | ⟨w1, hw1, hF, hz1⟩
  · exact Or.inl (Or.inl fun x hx => by simp [hF x hx])
  · rcases hG with hG | hG | ⟨w2, hw2, hG, hz2⟩
    · exact Or.inl (Or.inl fun x hx => by simp [hG x hx])
    · exact Or.inl (Or.inr (Or.inl fun x hx => by simp [hF x hx, hG x hx]))
    · exact Or.inl (Or.inr (Or.inr ⟨w2, hw2, fun x hx => by simp [hF x hx, hG x hx],
        fun M hM => hz2 M hM.2⟩))
  · rcases hG with hG | hG | ⟨w2, hw2, hG, hz2⟩
    · exact Or.inl (Or.inl fun x hx => by simp [hG x hx])
    · exact Or.inl (Or.inr (Or.inr ⟨w1, hw1, fun x hx => by simp [hF x hx, hG x hx],
        fun M hM => hz1 M hM.1⟩))
    · refine Or.inr ⟨⟨GateOp.and, [w1, w2]⟩, Or.inl rfl, rfl, ?_, ?_, fun x hx => ?_, ?_⟩
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> assumption
      · intro _
        rcases hkm with (h | h) | ⟨h1, h2⟩
        · exact Or.inl ⟨w1, by simp, hz1 L h⟩
        · exact Or.inl ⟨w2, by simp, hz2 L h⟩
        · refine Or.inr fun a ha => ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · exact hz1 P h1
          · exact hz2 P h2
      · simp [GateOp.eval, hF x hx, hG x hx]
      · intro M hM a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact hz1 M hM.1
        · exact hz2 M hM.2

theorem st_or {n : ℕ} {L P : Finset ℕ} {gs' : List Gate} {F G : List Bool → Bool}
    {ZF ZG : Finset ℕ → Prop} (hF : St n gs' F ZF) (hG : St n gs' G ZG) :
    St4 n L P gs' (fun x => F x || G x) (fun M => ZF M ∧ ZG M) := by
  rcases hF with hF | hF | ⟨w1, hw1, hF, hz1⟩
  · rcases hG with hG | hG | ⟨w2, hw2, hG, hz2⟩
    · exact Or.inl (Or.inl fun x hx => by simp [hF x hx, hG x hx])
    · exact Or.inl (Or.inr (Or.inl fun x hx => by simp [hG x hx]))
    · exact Or.inl (Or.inr (Or.inr ⟨w2, hw2, fun x hx => by simp [hF x hx, hG x hx],
        fun M hM => hz2 M hM.2⟩))
  · exact Or.inl (Or.inr (Or.inl fun x hx => by simp [hF x hx]))
  · rcases hG with hG | hG | ⟨w2, hw2, hG, hz2⟩
    · exact Or.inl (Or.inr (Or.inr ⟨w1, hw1, fun x hx => by simp [hF x hx, hG x hx],
        fun M hM => hz1 M hM.1⟩))
    · exact Or.inl (Or.inr (Or.inl fun x hx => by simp [hG x hx]))
    · refine Or.inr ⟨⟨GateOp.or, [w1, w2]⟩, Or.inr rfl, rfl, ?_, ?_, fun x hx => ?_, ?_⟩
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> assumption
      · intro hh
        cases hh
      · simp [GateOp.eval, hF x hx, hG x hx]
      · intro M hM a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact hz1 M hM.1
        · exact hz2 M hM.2

theorem norm (n : ℕ) (L P : Finset ℕ) (gs : List Gate) : Hyp n L P gs →
    ∃ gs' : List Gate, Good n L P gs' ∧ gs'.length ≤ gs.length ∧
      ∀ w : ℕ, St n gs' (fun x => vl gs w x) (fun M => Z gs n M w) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], fun k g hk => by simp at hk, le_refl _, fun w => ?_⟩
    by_cases hw : w < n
    · exact Or.inr (Or.inr ⟨w, by simpa using hw, fun x hx => rfl, fun M h => h⟩)
    · exact Or.inl fun x hx => vl_ge [] w x (by rw [hx]; simp; omega)
  | append_singleton gs g ih =>
    intro hH
    obtain ⟨gs', hG, hlen, hw⟩ := ih (Hyp_prefix hH)
    obtain ⟨hop, hl2, hin, hkm⟩ := Hyp_last hH
    have key : St4 n L P gs' (fun x => vl (gs ++ [g]) (n + gs.length) x)
        (fun M => Z (gs ++ [g]) n M (n + gs.length)) := by
      have hV : ∀ x : List Bool, x.length = n →
          vl (gs ++ [g]) (n + gs.length) x = g.op.eval (g.inputs.map fun i => vl gs i x) :=
        fun x hx => by
          have := vl_snoc_eq gs g x
          rw [hx] at this
          exact this
      have hZ : ∀ M : Finset ℕ, Z (gs ++ [g]) n M (n + gs.length) → ∀ i ∈ g.inputs, Z gs n M i :=
        fun M h => (Z_snoc_eq gs g n M hop).1 h
      refine st_congr hV hZ ?_
      clear hV hZ hH
      obtain ⟨op, inputs⟩ := g
      dsimp only at hop hl2 hin hkm ⊢
      rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
      · rcases hop with hop | hop
        · exact Or.inl (Or.inr (Or.inl fun x hx => by simp [hop, GateOp.eval]))
        · exact Or.inl (Or.inl fun x hx => by simp [hop, GateOp.eval])
      · refine st_congr (G := fun x => vl gs a x) (ZG := fun M => Z gs n M a) (fun x hx => ?_)
          (fun M h => h a (by simp)) (Or.inl (hw a))
        rcases hop with hop | hop <;> simp [hop, GateOp.eval]
      · rcases hop with hop | hop
        · have hkm' : (Z gs n L a ∨ Z gs n L b) ∨ (Z gs n P a ∧ Z gs n P b) := by
            rcases hkm hop with ⟨i, hi, hz⟩ | hz
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact Or.inl (Or.inl hz)
              · exact Or.inl (Or.inr hz)
            · exact Or.inr ⟨hz a (by simp), hz b (by simp)⟩
          refine st_congr (fun x hx => ?_) (fun M h => ⟨h a (by simp), h b (by simp)⟩)
            (st_and (hw a) (hw b) hkm')
          simp [hop, GateOp.eval]
        · refine st_congr (fun x hx => ?_) (fun M h => ⟨h a (by simp), h b (by simp)⟩)
            (st_or (hw a) (hw b))
          simp [hop, GateOp.eval]
      · simp at hl2
    rcases key with key | ⟨g', hop', hl', hin', hkm', hval, hzz⟩
    · refine ⟨gs', hG, by simp; omega, fun w => ?_⟩
      rcases lt_trichotomy w (n + gs.length) with hlt | heq | hgt
      · exact st1_congr (fun x hx => vl_snoc_lt gs g x w (by rw [hx]; exact hlt))
          (fun M h => (Z_snoc_lt gs g n M w hlt).1 h) (hw w)
      · subst heq
        exact key
      · exact Or.inl fun x hx => vl_ge (gs ++ [g]) w x (by rw [hx]; simp; omega)
    · refine ⟨gs' ++ [g'], Good_snoc hG hop' hl' hin' hkm', by simp; omega, fun w => ?_⟩
      rcases lt_trichotomy w (n + gs.length) with hlt | heq | hgt
      · exact st_lift g' (st1_congr (fun x hx => vl_snoc_lt gs g x w (by rw [hx]; exact hlt))
          (fun M h => (Z_snoc_lt gs g n M w hlt).1 h) (hw w))
      · subst heq
        refine Or.inr (Or.inr ⟨n + gs'.length, by simp, fun x hx => ?_, fun M h => ?_⟩)
        · have := vl_snoc_eq gs' g' x
          rw [hx] at this
          rw [this]
          exact hval x hx
        · exact (Z_snoc_eq gs' g' n M hop').2 (hzz M h)
      · exact Or.inl fun x hx => vl_ge (gs ++ [g]) w x (by rw [hx]; simp; omega)

theorem gateAt_eq (C : Circuit) (k : ℕ) (g : Gate) (h : C.gates[k]? = some g) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, h]

theorem main (n : ℕ) (L P : Finset ℕ) (C : Circuit)
    (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hK : ∀ j < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and →
      (∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        (C.lineDegrees n L).getD i 0 = 0) ∨
      (∀ h ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        (C.lineDegrees n P).getD h 0 = 0))
    (hnc : ∃ z z' : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n C z ≠ PEqualNP.MetaComplexity.circuitFun n C z') :
    ∃ D : Circuit,
      ((∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n D) ∧
      (∀ j < D.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        (∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs,
          (D.lineDegrees n L).getD i 0 = 0) ∨
        (∀ h ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs,
          (D.lineDegrees n P).getD h 0 = 0)) ∧
      D.size ≤ C.size ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C := by
  have hH : Hyp n L P C.gates := by
    intro k g hk
    have hkl : k < C.gates.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hk
      cases hk
    have hga := gateAt_eq C k g hk
    have hm := hM g (List.mem_of_getElem? hk)
    refine ⟨by simpa using hm.1, hm.2, ?_, ?_⟩
    · have := hR k hkl
      rw [hga] at this
      exact this
    · have := hK k hkl
      rw [hga] at this
      exact this
  obtain ⟨gs', hG, hlen, hw⟩ := norm n L P C.gates hH
  have hfun : ∀ z : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n C z = vl C.gates C.output (List.ofFn z) := fun z => rfl
  rcases hw C.output with h0 | h1 | ⟨w', hw', hv, _⟩
  · exfalso
    obtain ⟨z, z', hz⟩ := hnc
    apply hz
    rw [hfun, hfun]
    exact (h0 _ (by simp)).trans (h0 _ (by simp)).symm
  · exfalso
    obtain ⟨z, z', hz⟩ := hnc
    apply hz
    rw [hfun, hfun]
    exact (h1 _ (by simp)).trans (h1 _ (by simp)).symm
  · refine ⟨⟨gs', w'⟩, ⟨?_, ?_⟩, ?_, hlen, ?_⟩
    · intro g hg
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hg
      obtain ⟨a, b, _, _⟩ := hG k g hk
      exact ⟨a, b⟩
    · intro j hj i hi
      have hk : gs'[j]? = some gs'[j] := List.getElem?_eq_getElem hj
      rw [gateAt_eq ⟨gs', w'⟩ j _ hk] at hi
      exact (hG j _ hk).2.2.1 i hi
    · intro j hj hop
      have hk : gs'[j]? = some gs'[j] := List.getElem?_eq_getElem hj
      rw [gateAt_eq ⟨gs', w'⟩ j _ hk] at hop ⊢
      exact (hG j _ hk).2.2.2 hop
    · funext z
      rw [hfun]
      exact (hv _ (by simp)).symm

end PEqualNP.Outside.L_meta_1715

theorem PEqualNP.Outside.L_meta_1715 : ∀ (N4 : ℕ) (C4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N4 + N4) C4 → (∀ j4 < C4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C4 j4).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C4 j4).inputs, (C4.lineDegrees (N4 + N4) (Finset.Ico N4 (N4 + N4))).getD i4 0 = 0) ∨ (∀ h4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C4 j4).inputs, (C4.lineDegrees (N4 + N4) (Finset.range N4)).getD h4 0 = 0)) → (∃ z4 z4a : Fin (N4 + N4) → Bool, PEqualNP.MetaComplexity.circuitFun (N4 + N4) C4 z4 ≠ PEqualNP.MetaComplexity.circuitFun (N4 + N4) C4 z4a) → ∃ D4 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g4 ∈ D4.gates, (g4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g4.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N4 + N4) D4) ∧ (∀ j4a < D4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D4 j4a).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i4a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D4 j4a).inputs, (D4.lineDegrees (N4 + N4) (Finset.Ico N4 (N4 + N4))).getD i4a 0 = 0) ∨ (∀ h4a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D4 j4a).inputs, (D4.lineDegrees (N4 + N4) (Finset.range N4)).getD h4a 0 = 0)) ∧ D4.size ≤ C4.size ∧ PEqualNP.MetaComplexity.circuitFun (N4 + N4) D4 = PEqualNP.MetaComplexity.circuitFun (N4 + N4) C4 := by
  intro N4 C4 h1 h2 h3 h4
  exact PEqualNP.Outside.L_meta_1715.main (N4 + N4) _ _ C4 h1 h2 h3 h4
