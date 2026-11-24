import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1375

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
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
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

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hm : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, h⟩)
      · simp [h]
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

-- Expand the selected gates once each, in reverse evaluation order.
-- Replacing one wire by at most two earlier wires increases the cut by at most one.
lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
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
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
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

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun v => decide (v = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun v => decide (v = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra hw
    have hw' : w < n := not_le.mp hw
    let p : Fin n := ⟨w, hw'⟩
    have hs : support C w ⊆ {p} := by
      intro r hr
      have hv := (mem_support C w r).mp hr
      change value C (fun v => decide (v = r)) p = true at hv
      rw [input_value] at hv
      exact Finset.mem_singleton.mpr (of_decide_eq_true hv).symm
    have hb := Finset.card_le_card hs
    rw [Finset.card_singleton] at hb
    omega
  · by_contra hw
    have hs : support (n := n) C w = ∅ := by
      ext r
      simp [mem_support, missing_value C _ w (not_lt.mp hw)]
    rw [hs, Finset.card_empty] at h
    omega

-- Gates owned by the set T: false on everything off R and off T, and either two
-- support points of T off R, or two support points of T with no support in R off T.
def own {n : ℕ} (C : Circuit) (T R : Finset (Fin n)) (y : Fin n → Bool) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => value C y w = false ∧
    (2 ≤ (support C w ∩ (T \ R)).card ∨ (support C w ∩ R ⊆ T ∧ 2 ≤ (support C w ∩ T).card))

lemma mem_own {n : ℕ} (C : Circuit) (T R : Finset (Fin n)) (y : Fin n → Bool) (w : ℕ)
    (hy : value C y w = false)
    (h : 2 ≤ (support C w ∩ (T \ R)).card ∨ (support C w ∩ R ⊆ T ∧ 2 ≤ (support C w ∩ T).card)) :
    w ∈ own C T R y := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w ?_), hy, h⟩
  rcases h with h | h
  · exact h.trans (Finset.card_le_card Finset.inter_subset_left)
  · exact h.2.trans (Finset.card_le_card Finset.inter_subset_left)

lemma two_le {n : ℕ} (s : Finset (Fin n)) (p p' : Fin n) (h : p ≠ p') (hp : p ∈ s)
    (hp' : p' ∈ s) : 2 ≤ s.card := by
  have hsub : ({p, p'} : Finset (Fin n)) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]; exact hp
    · rw [Finset.mem_singleton.mp hx]; exact hp'
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair h] at this

lemma core {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T R : Finset (Fin n)) (y : Fin n → Bool) (o : ℕ)
    (hy : value C y o = false)
    (hT : ∀ p ∈ T, value C (fun v => decide (v = p)) o = true) :
    ∃ B : Finset ℕ, Disjoint B (own C T R y) ∧ B.card ≤ (own C T R y).card + 1 ∧
      (∀ x z : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C z w = true) →
        value C x o = true → value C z o = true) ∧
      ∀ p ∈ T, ∃ w ∈ B, value C (fun v => decide (v = p)) w = true ∧ value C y w = false := by
  obtain ⟨B, hd, hc, hcut⟩ := cut C hG (own C T R y)
    (fun w hw => Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1) (n + C.size) {o}
    (fun w _ hw => (Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1).2)
  refine ⟨B, hd, ?_, fun x z h => hcut x z h o (Finset.mem_singleton_self o), ?_⟩
  · have := Finset.card_filter_le (own C T R y) (fun w => w < n + C.size)
    rw [Finset.card_singleton] at hc
    omega
  · intro p hp
    by_contra hcon
    have htrue : value C y o = true :=
      hcut _ y (fun w hw hx => by
        by_contra hne
        exact hcon ⟨w, hw, hx, Bool.eq_false_iff.mpr hne⟩) o (Finset.mem_singleton_self o)
        (hT p hp)
    rw [hy] at htrue
    exact Bool.false_ne_true htrue

lemma inj_on {n : ℕ} (C : Circuit) (T R : Finset (Fin n)) (y : Fin n → Bool) (B : Finset ℕ)
    (hd : Disjoint B (own C T R y)) (f : Fin n → ℕ)
    (hf : ∀ p ∈ T, f p ∈ B ∧ value C (fun v => decide (v = p)) (f p) = true ∧
      value C y (f p) = false)
    (p p' : Fin n) (hp : p ∈ T) (hp' : p' ∈ T) (hR : (p ∉ R ∧ p' ∉ R) ∨ R ⊆ T)
    (he : f p = f p') : p = p' := by
  by_contra hne
  obtain ⟨hB, hv, hy⟩ := hf p hp
  obtain ⟨_, hv', _⟩ := hf p' hp'
  rw [← he] at hv'
  refine Finset.disjoint_left.mp hd hB (mem_own C T R y (f p) hy ?_)
  rcases hR with hR | hR
  · left
    exact two_le _ p p' hne
      (Finset.mem_inter.mpr ⟨(mem_support C _ p).mpr hv, Finset.mem_sdiff.mpr ⟨hp, hR.1⟩⟩)
      (Finset.mem_inter.mpr ⟨(mem_support C _ p').mpr hv', Finset.mem_sdiff.mpr ⟨hp', hR.2⟩⟩)
  · right
    exact ⟨fun x hx => hR (Finset.mem_inter.mp hx).2, two_le _ p p' hne
      (Finset.mem_inter.mpr ⟨(mem_support C _ p).mpr hv, hp⟩)
      (Finset.mem_inter.mpr ⟨(mem_support C _ p').mpr hv', hp'⟩)⟩

lemma count_a {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T R : Finset (Fin n)) (y : Fin n → Bool) (o : ℕ)
    (hy : value C y o = false)
    (hT : ∀ p ∈ T, value C (fun v => decide (v = p)) o = true)
    (U : Finset (Fin n)) (hU : U ⊆ T) (hR : (∀ p ∈ U, p ∉ R) ∨ R ⊆ T) :
    U.card ≤ (own C T R y).card + 1 := by
  obtain ⟨B, hd, hc, _, hstar⟩ := core C hG T R y o hy hT
  choose! f hf using hstar
  have hinj : Set.InjOn f (U : Set (Fin n)) := fun p hp p' hp' he =>
    inj_on C T R y B hd f hf p p' (hU hp) (hU hp')
      (hR.imp (fun h => ⟨h p hp, h p' hp'⟩) id) he
  have h1 : U.card ≤ B.card :=
    Finset.card_le_card_of_injOn f (fun p hp => (hf p (hU hp)).1) hinj
  omega

lemma count_b {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T R : Finset (Fin n)) (y : Fin n → Bool) (o : ℕ)
    (hy : value C y o = false)
    (hT : ∀ p ∈ T, value C (fun v => decide (v = p)) o = true)
    (a : Fin n) (haT : a ∈ T) (haR : a ∈ R)
    (hb : ∀ b ∈ R, b ∉ T → value C (fun v => decide (v = b)) o = false) :
    (T \ R).card ≤ (own C T R y).card := by
  by_contra hlt
  obtain ⟨B, hd, hc, hcut, hstar⟩ := core C hG T R y o hy hT
  choose! f hf using hstar
  have hinj : Set.InjOn f ((T \ R : Finset (Fin n)) : Set (Fin n)) := fun p hp p' hp' he =>
    inj_on C T R y B hd f hf p p' (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp').1
      (Or.inl ⟨(Finset.mem_sdiff.mp hp).2, (Finset.mem_sdiff.mp hp').2⟩) he
  have himg : (T \ R).image f ⊆ B := fun w hw => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    exact (hf p (Finset.mem_sdiff.mp hp).1).1
  have hcard : ((T \ R).image f).card = (T \ R).card := Finset.card_image_of_injOn hinj
  have heq : (T \ R).image f = B := Finset.eq_of_subset_of_card_le himg (by omega)
  obtain ⟨hfa, hva, hya⟩ := hf a haT
  rw [← heq] at hfa
  obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp hfa
  obtain ⟨hpT, hpR⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hfp, hvp, hyp⟩ := hf p hpT
  have hnot : f p ∉ own C T R y := fun h => Finset.disjoint_left.mp hd hfp h
  have hex : ∃ b ∈ R, b ∉ T ∧ value C (fun v => decide (v = b)) (f p) = true := by
    by_contra hno
    apply hnot
    refine mem_own C T R y (f p) hyp (Or.inr ⟨?_, ?_⟩)
    · intro b hbm
      by_contra hbT
      exact hno ⟨b, (Finset.mem_inter.mp hbm).2, hbT,
        (mem_support C _ b).mp (Finset.mem_inter.mp hbm).1⟩
    · have hva' : value C (fun v => decide (v = a)) (f p) = true := by rw [hpa]; exact hva
      exact two_le _ p a (fun h => hpR (h ▸ haR))
        (Finset.mem_inter.mpr ⟨(mem_support C _ p).mpr hvp, hpT⟩)
        (Finset.mem_inter.mpr ⟨(mem_support C _ a).mpr hva', haT⟩)
  obtain ⟨b, hbR, hbT, hvb⟩ := hex
  have htrue : value C (fun v => decide (v = b)) o = true := by
    refine hcut (fun v => decide (v = p)) _ ?_ (hT p hpT)
    intro w hw hx
    rw [← heq] at hw
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hw
    have hpp : p' = p := by
      by_contra hne
      obtain ⟨hpT', hpR'⟩ := Finset.mem_sdiff.mp hp'
      obtain ⟨hB', hv', hy'⟩ := hf p' hpT'
      exact Finset.disjoint_left.mp hd hB' (mem_own C T R y (f p') hy' (Or.inl
        (two_le _ p' p hne
          (Finset.mem_inter.mpr ⟨(mem_support C _ p').mpr hv', hp'⟩)
          (Finset.mem_inter.mpr ⟨(mem_support C _ p).mpr hx, hp⟩))))
    rw [hpp]
    exact hvb
  rw [hb b hbR hbT] at htrue
  exact Bool.false_ne_true htrue

lemma off {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T R : Finset (Fin n)) (w : ℕ)
    (hy : value C (fun v => decide (v ∉ R ∧ v ∉ T)) w = false) (u : Fin n)
    (hu : u ∈ support C w) (huR : u ∉ R) : u ∈ T := by
  by_contra huT
  have htrue := value_mono C hG (fun v => decide (v = u)) (fun v => decide (v ∉ R ∧ v ∉ T))
    (fun p hp => by
      have hpu : p = u := of_decide_eq_true hp
      rw [hpu]
      exact decide_eq_true ⟨huR, huT⟩) w ((mem_support C w u).mp hu)
  rw [hy] at htrue
  exact Bool.false_ne_true htrue

lemma own_disjoint {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T T' R : Finset (Fin n)) (hTT : (T ∩ T').card ≤ 1) :
    Disjoint (own C T R (fun v => decide (v ∉ R ∧ v ∉ T)))
      (own C T' R (fun v => decide (v ∉ R ∧ v ∉ T'))) := by
  refine Finset.disjoint_left.mpr fun w h1 h2 => ?_
  obtain ⟨_, hy1, ha1⟩ := Finset.mem_filter.mp h1
  obtain ⟨_, hy2, ha2⟩ := Finset.mem_filter.mp h2
  have o1 := off C hG T R w hy1
  have o2 := off C hG T' R w hy2
  have key : ∀ s : Finset (Fin n), s ⊆ T ∩ T' → ¬ 2 ≤ s.card := fun s hs h => by
    have := Finset.card_le_card hs
    omega
  rcases ha1 with ha1 | ha1
  · exact key _ (fun x hx => by
      obtain ⟨hs, hx2⟩ := Finset.mem_inter.mp hx
      obtain ⟨hxT, hxR⟩ := Finset.mem_sdiff.mp hx2
      exact Finset.mem_inter.mpr ⟨hxT, o2 x hs hxR⟩) ha1
  rcases ha2 with ha2 | ha2
  · exact key _ (fun x hx => by
      obtain ⟨hs, hx2⟩ := Finset.mem_inter.mp hx
      obtain ⟨hxT, hxR⟩ := Finset.mem_sdiff.mp hx2
      exact Finset.mem_inter.mpr ⟨o1 x hs hxR, hxT⟩) ha2
  · exact key _ (fun x hx => by
      obtain ⟨hs, hxT⟩ := Finset.mem_inter.mp hx
      refine Finset.mem_inter.mpr ⟨hxT, ?_⟩
      by_cases hxR : x ∈ R
      · exact ha2.1 (Finset.mem_inter.mpr ⟨hs, hxR⟩)
      · exact o2 x hs hxR) ha1.2

lemma per_set {q n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T R : Finset (Fin n)) (o : ℕ) (hcard : T.card = q + 1)
    (hprom : ∀ x : Fin n → Bool,
      ((∀ v ∈ R, x v = false) ∨ (∃ p ∈ R, ∀ v : Fin n, x v = decide (v = p))) →
      value C x o = decide (∃ v ∈ T, x v = true)) :
    q ≤ (own C T R (fun v => decide (v ∉ R ∧ v ∉ T))).card + ((T ∩ R).card - 1) ∧
      (R ⊆ T → q ≤ (own C T R (fun v => decide (v ∉ R ∧ v ∉ T))).card) := by
  have hy : value C (fun v => decide (v ∉ R ∧ v ∉ T)) o = false := by
    rw [hprom _ (Or.inl fun v hv => decide_eq_false (fun h => h.1 hv))]
    exact decide_eq_false (by
      rintro ⟨v, hv, h⟩
      exact (of_decide_eq_true h).2 hv)
  have hT : ∀ p ∈ T, value C (fun v => decide (v = p)) o = true := by
    intro p hp
    have hin : (∀ v ∈ R, (fun v => decide (v = p)) v = false) ∨
        (∃ p' ∈ R, ∀ v : Fin n, (fun v => decide (v = p)) v = decide (v = p')) := by
      by_cases hpR : p ∈ R
      · exact Or.inr ⟨p, hpR, fun v => rfl⟩
      · exact Or.inl fun v hv => decide_eq_false (fun h => hpR (h ▸ hv))
    rw [hprom _ hin]
    exact decide_eq_true ⟨p, hp, decide_eq_true rfl⟩
  have hb : ∀ b ∈ R, b ∉ T → value C (fun v => decide (v = b)) o = false := by
    intro b hbR hbT
    rw [hprom _ (Or.inr ⟨b, hbR, fun v => rfl⟩)]
    exact decide_eq_false (by
      rintro ⟨v, hv, h⟩
      exact hbT ((of_decide_eq_true h) ▸ hv))
  constructor
  · have hsplit := Finset.card_sdiff_add_card_inter T R
    by_cases hne : (T ∩ R).Nonempty
    · obtain ⟨a, ha⟩ := hne
      have h1 := count_b C hG T R _ o hy hT a (Finset.mem_inter.mp ha).1
        (Finset.mem_inter.mp ha).2 hb
      have h2 : 0 < (T ∩ R).card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    · have h1 := count_a C hG T R _ o hy hT T (le_refl T)
        (Or.inl fun p hp hpR => hne ⟨p, Finset.mem_inter.mpr ⟨hp, hpR⟩⟩)
      omega
  · intro hRT
    have h1 := count_a C hG T R _ o hy hT T (le_refl T) (Or.inr hRT)
    omega

lemma main : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      ((∀ v ∈ S i0, x v = false) ∨ (∃ p ∈ S i0, ∀ v : Fin n, x v = decide (v = p))) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    m * q ≤ gates.length := by
  intro q n m S i0 _ hsize hinter gates out hg heval
  let C : Circuit := ⟨gates, 0⟩
  let G (i : Fin m) := own C (S i) (S i0) (fun v => decide (v ∉ S i0 ∧ v ∉ S i))
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G :=
    fun i _ j _ hij => own_disjoint C hg (S i) (S j) (S i0) (hinter i j hij)
  have hi (i : Fin m) : q ≤ (G i).card := by
    have h := per_set C hg (S i) (S i0) (out i) (hsize i) (by
      intro x hx
      have h := heval i x hx
      exact h)
    by_cases hii : i = i0
    · subst hii
      exact h.2 (le_refl _)
    · have h1 := hinter i i0 hii
      have h2 := h.1
      change q ≤ (G i).card + _ at h2
      omega
  have hs : Finset.univ.biUnion G ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i, _, hw⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hw).1
  have hlen : (Finset.Ico n (n + C.size)).card = gates.length := by simp [C, Circuit.size]
  have hle := Finset.card_le_card hs
  calc m * q = ∑ _i : Fin m, q := by simp
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ => hi i
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ gates.length := by omega

end PEqualNP.Outside.L_meta_1375

theorem PEqualNP.Outside.L_meta_1375 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      ((∀ v ∈ S i0, x v = false) ∨ (∃ p ∈ S i0, ∀ v : Fin n, x v = decide (v = p))) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    m * q ≤ gates.length :=
  PEqualNP.Outside.L_meta_1375.main
