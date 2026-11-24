import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1595

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    value C x w = (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).op.eval
      ((C.gates[w - n]'(by unfold Circuit.size at hw; omega)).inputs.map
        fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hop : (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).op = GateOp.and ∨
      (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).op = GateOp.or)
    (hlen : (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).inputs.length ≤ 2) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  classical
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [g, hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact hr r hrm (hx _ (List.mem_map.mpr ⟨r, hrm, rfl⟩))
    · simp only [g, hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hbt⟩ := hx
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hrm, rfl⟩, hr r hrm hbt⟩

lemma not_head (l : List ℕ) (f f' : ℕ → Bool) (h : GateOp.not.eval (l.map f) = false)
    (hff : ∀ r ∈ l, f r = true → f' r = true) : GateOp.not.eval (l.map f') = false := by
  cases l with
  | nil => simp [GateOp.eval] at h
  | cons r rest =>
    simp [GateOp.eval] at h ⊢
    exact hff r (by simp) h

-- A NOT gate that is false on Y stays false on every input above Y,
-- as soon as the earlier wires are monotone above Y.
lemma not_false {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) (hn : n ≤ w)
    (hw : w < n + C.size)
    (hop : (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).op = GateOp.not)
    (hfalse : value C (fun v => decide (v ∈ Y)) w = false)
    (x : Fin n → Bool)
    (hmono : ∀ r, r < w → value C (fun v => decide (v ∈ Y)) r = true → value C x r = true) :
    value C x w = false := by
  have f1 := gate_value C (fun v => decide (v ∈ Y)) w hn hw
  have f2 := gate_value C x w hn hw
  rw [hop] at f1 f2
  rw [f2]
  rw [f1] at hfalse
  refine not_head _ _ _ hfalse ?_
  intro r _ hr
  by_cases h : r < w
  · simp only [h, if_true] at hr ⊢
    exact hmono r h hr
  · simp [h] at hr

lemma value_mono {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → (j : ℕ) = t)
    (hfalse : value C (fun v => decide (v ∈ Y)) (n + t) = false)
    (w : ℕ) : ∀ (x y : Fin n → Bool), (∀ p ∈ Y, x p = true) →
      (∀ p, x p = true → y p = true) → value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro x y hY hxy
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
      obtain ⟨hop, hlen⟩ := hG (C.gates[w - n]) (List.getElem_mem _)
      rcases hop with hop | hop | hop
      · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C w (by omega) hw (Or.inl hop) hlen
        exact hstep x y fun r hr => ih r (hP r hr) x y hY hxy
      · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C w (by omega) hw (Or.inr hop) hlen
        exact hstep x y fun r hr => ih r (hP r hr) x y hY hxy
      · have ht : w - n = t := hnot ⟨w - n, hj⟩ hop
        have hwt : w = n + t := by omega
        intro hx
        have hf := not_false C Y w (by omega) hw hop (by rw [hwt]; exact hfalse) x
          (fun r hr hv => ih r hr (fun v => decide (v ∈ Y)) x
            (fun p hp => decide_eq_true hp) (fun p hp => hY p (of_decide_eq_true hp)) hv)
        rw [hf] at hx
        exact absurd hx (by simp)
    · simp [missing_value C x w (by omega)]

-- Expand the selected gates once each, in reverse evaluation order.
-- Replacing one wire by at most two earlier wires increases the cut by at most one.
lemma cut {n : ℕ} (C : Circuit) (G : Finset ℕ)
    (hstep : ∀ w ∈ G, ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := hstep t hex.2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

-- Soundness for T, tested only on inputs that contain Y.
def sound {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (∀ v ∈ Y, x v = true) → value C x w = true → ∃ p ∈ T, x p = true

def supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun v => decide (v ∈ Y ∨ v = p)) w = true)

lemma mem_supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ supp C Y w ↔ value C (fun v => decide (v ∈ Y ∨ v = p)) w = true := by
  simp [supp]

noncomputable def asg {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter (fun w => sound C Y T w ∧ 2 ≤ (supp C Y w).card)

lemma mem_asg {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ) :
    w ∈ asg C Y T ↔ (n ≤ w ∧ w < n + C.size) ∧ sound C Y T w ∧ 2 ≤ (supp C Y w).card := by
  classical
  unfold asg
  rw [Finset.mem_filter, Finset.mem_Ico]

lemma supp_gate {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ) (hYT : Disjoint Y T)
    (hs : sound C Y T w) (h2 : 2 ≤ (supp C Y w).card) : n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p0 : Fin n := ⟨w, hw⟩
    have hY : p0 ∉ Y := by
      intro hp0
      have hv : value C (fun v => decide (v ∈ Y)) w = true := by
        change value C (fun v => decide (v ∈ Y)) p0 = true
        rw [input_value]
        simpa using hp0
      obtain ⟨q, hqT, hqY⟩ := hs _ (fun v hv => decide_eq_true hv) hv
      exact Finset.disjoint_left.mp hYT (by simpa using hqY) hqT
    have hsub : supp C Y w ⊆ {p0} := by
      intro q hq
      have hv := (mem_supp C Y w q).mp hq
      change value C (fun v => decide (v ∈ Y ∨ v = q)) p0 = true at hv
      rw [input_value] at hv
      simp only [decide_eq_true_eq] at hv
      rcases hv with hv | hv
      · exact absurd hv hY
      · simp [hv]
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_contra! hw
    have hs0 : supp (n := n) C Y w = ∅ := by
      ext q
      simp [mem_supp, missing_value C _ w hw]
    simp [hs0] at h2

lemma card_le {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (t : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → (j : ℕ) = t)
    (hfalse : value C (fun v => decide (v ∈ Y)) (n + t) = false)
    (o : ℕ) (hYT : Disjoint Y T) (hso : sound C Y T o)
    (hfire : ∀ p ∈ T, value C (fun v => decide (v ∈ Y ∨ v = p)) o = true) :
    T.card ≤ (asg C Y T).card + 1 := by
  classical
  let G := asg C Y T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := fun w hw => ((mem_asg C Y T w).mp hw).1
  have hstep : ∀ w ∈ G, ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
    intro w hw
    obtain ⟨⟨hn, hlt⟩, hs, h2⟩ := (mem_asg C Y T w).mp hw
    have hj : w - n < C.gates.length := by unfold Circuit.size at hlt; omega
    obtain ⟨hop, hlen⟩ := hG (C.gates[w - n]) (List.getElem_mem _)
    rcases hop with hop | hop | hop
    · exact gate_inputs C w hn hlt (Or.inl hop) hlen
    · exact gate_inputs C w hn hlt (Or.inr hop) hlen
    · exfalso
      have ht : w - n = t := hnot ⟨w - n, hj⟩ hop
      have hwt : w = n + t := by omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (supp C Y w).card)
      have hv := (mem_supp C Y w p).mp hp
      have hf := not_false C Y w hn hlt hop (by rw [hwt]; exact hfalse)
        (fun v => decide (v ∈ Y ∨ v = p))
        (fun r _ hr => value_mono C Y t hG hnot hfalse r (fun v => decide (v ∈ Y))
          (fun v => decide (v ∈ Y ∨ v = p)) (fun q hq => decide_eq_true hq)
          (fun q hq => decide_eq_true (Or.inl (of_decide_eq_true hq))) hr)
      rw [hf] at hv
      exact Bool.false_ne_true hv
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C G hstep (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ G.card + 1 := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    omega
  let clean (w : ℕ) : Finset (Fin n) := if sound C Y T w then supp C Y w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : sound C Y T w
    · simp only [clean, if_pos hs]
      by_contra! hlarge
      have hg := supp_gate C Y T w hYT hs (by omega)
      exact Finset.disjoint_left.mp hd hw ((mem_asg C Y T w).mpr ⟨hg, hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    have hG' : G.card + 1 < T.card := hsmall
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let Dn := B.filter (fun w => ¬ sound C Y T w)
  have hout (w : {w // w ∈ Dn}) :
      ∃ x : Fin n → Bool, (∀ v ∈ Y, x v = true) ∧ value C x w.val = true ∧
        ∀ q ∈ T, x q = false := by
    have hns := (Finset.mem_filter.mp w.property).2
    unfold sound at hns
    push_neg at hns
    obtain ⟨x, hxY, hx, hxT⟩ := hns
    exact ⟨x, hxY, hx, fun q hq => by simpa using hxT q hq⟩
  choose xs hxs using hout
  let z : Fin n → Bool := fun v => decide (v ∈ Y ∨ ∃ d : {w // w ∈ Dn}, xs d v = true)
  have hzY : ∀ v ∈ Y, z v = true := fun v hv => decide_eq_true (Or.inl hv)
  have hzfalse : value C z o = false := by
    by_contra hne
    have ht : value C z o = true := by simpa using hne
    obtain ⟨q, hqT, hzq⟩ := hso z hzY ht
    simp only [z, decide_eq_true_eq] at hzq
    rcases hzq with hqY | ⟨d, hd'⟩
    · exact Finset.disjoint_left.mp hYT hqY hqT
    · rw [(hxs d).2.2 q hqT] at hd'
      exact Bool.false_ne_true hd'
  have hztrue : value C z o = true := by
    apply hcut (fun v => decide (v ∈ Y ∨ v = p)) z _ o (Finset.mem_singleton_self o) (hfire p hp)
    intro w hw hx
    by_cases hs : sound C Y T w
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simp only [clean, if_pos hs]; exact (mem_supp C Y w p).mpr hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      refine value_mono C Y t hG hnot hfalse w (xs d) z (hxs d).1 ?_ (hxs d).2.1
      intro v hv
      simp only [z, decide_eq_true_eq]
      exact Or.inr ⟨d, hv⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

end PEqualNP.Outside.L_meta_1595

open PEqualNP.Outside.L_meta_1595 in
theorem PEqualNP.Outside.L_meta_1595 : (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (N M : ℕ) (A : Fin M → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin M → ℕ) (t : ℕ) (Y : Finset (Fin N)), (∀ ab1 ab2 : Fin M, ab1 ≠ ab2 → (A ab1 ∩ A ab2).card ≤ 1) → (∀ eb1 ∈ D.gates, (eb1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ eb1.inputs.length ≤ 2) → (∀ lb1 : Fin D.gates.length, (D.gates.get lb1).op = PEqualNP.CircuitLowerBounds.GateOp.not → (lb1 : ℕ) = t) → (∀ (ab3 : Fin M) (zb1 : Fin N → Bool), (D.wires (List.ofFn zb1)).getD (u ab3) false = decide (∃ sb1 ∈ A ab3, zb1 sb1 = true)) → (∀ zb2 : Fin N → Bool, (Finset.univ.filter (fun vb1 : Fin N => zb2 vb1 = true)).card < Y.card → (D.wires (List.ofFn zb2)).getD (N + t) false = true) → (D.wires (List.ofFn (fun vb2 : Fin N => decide (vb2 ∈ Y)))).getD (N + t) false = false → ∀ b4 : Fin M, Disjoint (A b4) Y → (A b4).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length => (∀ s2 : Fin N, s2 ∉ Y → (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 ∈ Y ∨ w1 = s2)))).getD (N + h1) false = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N => s3 ∉ Y ∧ (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 ∈ Y ∨ w2 = s3)))).getD (N + h1) false = true)).card)).card + 1 := by
  intro _ _ N M A D u t Y _ hG hnot hout _ hfalse b4 hdisj
  have hYT : Disjoint Y (A b4) := hdisj.symm
  have hmain := card_le D Y (A b4) t hG hnot hfalse (u b4) hYT
    (fun x _ hx => of_decide_eq_true ((hout b4 x).symm.trans hx))
    (fun p hp => (hout b4 _).trans (decide_eq_true ⟨p, hp, by simp⟩))
  refine hmain.trans (Nat.add_le_add_right ?_ 1)
  refine (Finset.card_le_card ?_).trans
    (Finset.card_image_le (f := fun h : Fin D.gates.length => N + (h : ℕ)))
  intro w hw
  obtain ⟨⟨hn, hlt⟩, hs, h2⟩ := (mem_asg D Y (A b4) w).mp hw
  obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
  have hj : j < D.gates.length := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.size at hlt; omega
  refine Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, rfl⟩
  · intro s hsY hv
    obtain ⟨p, hpT, hp⟩ := hs _ (fun v hv => decide_eq_true (Or.inl hv)) hv
    rcases of_decide_eq_true hp with hpY | rfl
    · exact absurd hpT (Finset.disjoint_left.mp hYT hpY)
    · exact hpT
  · refine h2.trans (Finset.card_le_card ?_)
    intro p hp
    have hv := (mem_supp D Y (N + j) p).mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hv⟩
    intro hpY
    obtain ⟨q, hqT, hq⟩ := hs _ (fun v hv => decide_eq_true (Or.inl hv)) hv
    rcases of_decide_eq_true hq with hqY | rfl
    · exact Finset.disjoint_left.mp hYT hqY hqT
    · exact Finset.disjoint_left.mp hYT hpY hqT
