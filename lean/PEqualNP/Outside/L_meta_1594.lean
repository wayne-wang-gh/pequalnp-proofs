import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1594

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
  classical
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
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
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact hr r hrm (hx _ (List.mem_map.mpr ⟨r, hrm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hbt⟩ := hx
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hrm, rfl⟩, hr r hrm hbt⟩

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

def supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun v => decide (v ∈ Y ∨ v = p)) w = true)

lemma mem_supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ supp C Y w ↔ value C (fun v => decide (v ∈ Y ∨ v = p)) w = true := by
  simp [supp]

abbrev Base (n : ℕ) := Finset (Fin n)
def bits {n : ℕ} (A : Base n) (p : Fin n) : Bool := decide (p ∈ A)

def windowG {n : ℕ} (C : Circuit) (Y S : Base n) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter (fun w => supp C Y w ⊆ S ∧ 2 ≤ (supp C Y w).card)

lemma windowG_bounds {n : ℕ} (C : Circuit) (Y S : Base n) {w : ℕ} (h : w ∈ windowG C Y S) :
    n ≤ w ∧ w < n + C.size :=
  Finset.mem_Ico.mp (Finset.mem_filter.mp h).1

lemma windowG_only_wire {n : ℕ} (C : Circuit) (Y S : Base n)
    (hy : Disjoint Y S) (w : ℕ) (hc : supp C Y w ⊆ S)
    (hTwo : 2 ≤ (supp C Y w).card) : n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra hn
    have hn' : w < n := Nat.lt_of_not_ge hn
    let p : Fin n := ⟨w,hn'⟩
    have hp : p ∈ supp C Y w := by
      apply (mem_supp C Y w p).mpr
      change value C (fun v => decide (v ∈ Y ∨ v = p)) p = true
      rw [input_value]
      simp
    have hpS := hc hp
    have hpY : p ∉ Y := fun h => Finset.disjoint_left.mp hy h hpS
    have hsub : supp C Y w ⊆ {p} := by
      intro v hv
      have ha := (mem_supp C Y w v).mp hv
      change value C (fun q => decide (q ∈ Y ∨ q = v)) p = true at ha
      rw [input_value] at ha
      exact Finset.mem_singleton.mpr ((of_decide_eq_true ha).resolve_left hpY).symm
    have hz := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hz
    omega
  · by_contra hn
    have hn' : n + C.size ≤ w := Nat.le_of_not_gt hn
    have hzero : supp C Y w = ∅ := by
      ext p
      simp [mem_supp,missing_value C _ _ hn']
    simp [hzero] at hTwo

lemma window_bound {n : ℕ} (C : Circuit)
    (hMono : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (Y S : Base n) (out k : ℕ) (hY : Disjoint Y S)
    (hPos : ∀ p ∈ S, value C (fun v => decide (v ∈ Y ∨ v = p)) out = true)
    (hNeg : ∀ A : Base n, Disjoint A S → A.card < k → value C (bits (Y ∪ A)) out = false) :
    min k S.card ≤ (windowG C Y S).card + 1 := by
  classical
  by_contra hn
  let G := windowG C Y S
  have hglt (w : ℕ) (hw : w ∈ G) := (windowG_bounds C Y S hw).2
  obtain ⟨B,hB,hBn,transport⟩ := cut C hMono G (fun w => windowG_bounds C Y S)
    (n+C.size) {out} (fun w _ => hglt w)
  have hb : B.card ≤ G.card + 1 := by
    have he := Finset.card_filter_le G (fun w => w < n+C.size)
    simp only [Finset.card_singleton] at hBn
    omega
  let safe (w : ℕ) : Base n := if supp C Y w ⊆ S then supp C Y w else ∅
  have hsafe : ∀ w ∈ B, (safe w).card ≤ 1 := by
    intro w hw
    by_cases hsub : supp C Y w ⊆ S
    · rw [show safe w = supp C Y w by simp [safe,hsub]]
      by_contra hlarge
      have h2 : 2 ≤ (supp C Y w).card := by omega
      have hr := windowG_only_wire C Y S hY w hsub h2
      exact (Finset.disjoint_left.mp hB hw (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hr,hsub,h2⟩))
    · simp [safe,hsub]
  have hall : (B.biUnion safe).card < S.card := by
    have he := Finset.card_biUnion_le_card_mul B safe 1 hsafe
    simp only [mul_one] at he
    change ¬ (min k S.card ≤ G.card + 1) at hn
    omega
  obtain ⟨p,hp,hpn⟩ := Finset.exists_mem_notMem_of_card_lt_card hall
  let D := B.filter (fun w => ¬ supp C Y w ⊆ S)
  have hchoose : ∀ w : {w // w ∈ D}, ∃ q : Fin n, q ∈ supp C Y w.val ∧ q ∉ S :=
    fun w => Finset.not_subset.mp (Finset.mem_filter.mp w.property).2
  choose chosen hchosen using hchoose
  let A : Base n := D.attach.image chosen
  have hA : Disjoint A S := by
    apply Finset.disjoint_left.mpr
    intro q hq hqs
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hq
    exact (hchosen w).2 hqs
  have hsmall : A.card < k := by
    have he := (Finset.card_image_le (s := D.attach) (f := chosen)).trans
      (by simpa [D] using (Finset.card_filter_le B fun w => ¬ supp C Y w ⊆ S))
    change ¬ (min k S.card ≤ G.card + 1) at hn
    have hx : A.card ≤ B.card := he
    omega
  have hj (w : ℕ) (hw : w ∈ B)
      (hwTrue : value C (fun v => decide (v ∈ Y ∨ v = p)) w = true) :
      value C (bits (Y ∪ A)) w = true := by
    by_cases hsub : supp C Y w ⊆ S
    · exfalso
      apply hpn
      exact Finset.mem_biUnion.mpr ⟨w,hw,by simp only [safe,ite_eq_left hsub]; exact (mem_supp C Y w p).mpr hwTrue⟩
    · let ww : {w // w ∈ D} := ⟨w,Finset.mem_filter.mpr ⟨hw,hsub⟩⟩
      have hCh : chosen ww ∈ A := Finset.mem_image.mpr ⟨ww,Finset.mem_attach _ _,rfl⟩
      apply value_mono C hMono
        (fun v => decide (v ∈ Y ∨ v = chosen ww)) (bits (Y ∪ A)) ?_ w
        ((mem_supp C Y w (chosen ww)).mp (hchosen ww).1)
      intro v hv
      have hv' : v ∈ Y ∨ v = chosen ww := of_decide_eq_true hv
      apply decide_eq_true
      rcases hv' with hv' | rfl
      · exact Finset.mem_union_left _ hv'
      · exact Finset.mem_union_right _ hCh
  have he := transport _ _ hj out (Finset.mem_singleton_self out) (hPos p hp)
  rw [hNeg A hA hsmall] at he
  contradiction

def pin (C : Circuit) (t : ℕ) (b : Bool) : Circuit :=
  ⟨C.gates.set t ⟨if b then .and else .or,[]⟩,C.output⟩

lemma pin_size (C : Circuit) (t : ℕ) (b : Bool) : (pin C t b).size = C.size := by
  simp [pin,Circuit.size]

def Mono (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def Legal (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def Only (C : Circuit) (t : ℕ) : Prop :=
  ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → i.val = t

lemma pin_mono (C : Circuit) (t : ℕ) (b : Bool) (hL : Legal C) (hOnly : Only C t) :
    Mono (pin C t b) := by
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
  have hi' : i < C.gates.length := by simpa [pin] using hi
  by_cases h : t = i
  · cases b <;> simp [pin,h]
  · have he : (pin C t b).gates[i] = C.gates[i] := by simp [pin,h]
    rw [he]
    obtain ⟨ho,hl⟩ := hL (C.gates[i]) (List.getElem_mem _)
    refine ⟨?_,hl⟩
    rcases ho with ha | hb | hc
    · exact Or.inl ha
    · exact Or.inr hb
    · exact (h ((hOnly ⟨i,hi'⟩ hc).symm)).elim

lemma pin_here {n : ℕ} (C : Circuit) (t : ℕ) (b : Bool) (ht : t < C.size) (x : Fin n → Bool) :
    value (pin C t b) x (n+t) = b := by
  have hp := gate_value (pin C t b) x (n+t) (by omega)
    (by rw [pin_size]; omega)
  rw [hp]
  cases b <;> simp [pin,GateOp.eval]

lemma pin_value {n : ℕ} (C : Circuit) (t : ℕ) (b : Bool) (x : Fin n → Bool) (v : ℕ)
    (h : v < n+t ∨ value C x (n+t) = b) :
    value (pin C t b) x v = value C x v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    by_cases hn : v < n
    · let u : Fin n := ⟨v,hn⟩
      exact (input_value (pin C t b) x u).trans (input_value C x u).symm
    by_cases hlt : v < n+C.size
    · by_cases he : v = n+t
      · subst v
        exact (pin_here C t b (by omega) x).trans ((h.resolve_left (by omega)).symm)
      · have heq : (pin C t b).gates[v-n]'(by simp [pin,Circuit.size] at *; omega) =
            C.gates[v-n]'(by unfold Circuit.size at hlt; omega) := by
          simp only [pin,List.getElem_set]
          rw [ite_eq_right (by omega)]
        rw [gate_value (pin C t b) x v (by omega) (by rw [pin_size]; exact hlt),
          gate_value C x v (by omega) hlt]
        have ha : v-n < C.gates.length := by unfold Circuit.size at hlt; omega
        have hb : v-n < (pin C t b).gates.length := by simpa [pin] using ha
        change ((pin C t b).gates[v-n]'hb).op.eval _ = (C.gates[v-n]'ha).op.eval _
        rw [heq]
        congr 1
        apply List.map_congr_left
        intro r _
        by_cases hr : r < v
        · have hih := ih r hr (h.imp_left (fun hh => hr.trans hh))
          simpa only [ite_eq_left hr] using hih
        · simp [hr]
    · rw [missing_value C _ _ (by omega),missing_value (pin C t b) _ _ (by rw [pin_size]; omega)]

def Exact {n : ℕ} (C : Circuit) (S : Base n) (o : ℕ) : Prop :=
  ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ S, x p = true)

def Light {n : ℕ} (C : Circuit) (t k : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (Finset.univ.filter fun p => x p = true).card < k →
    value C x (n+t) = true

lemma true_count_bits {n : ℕ} (A : Base n) :
    (Finset.univ.filter fun p => bits A p = true).card = A.card := by
  congr 1
  ext p
  simp [bits]

lemma exact_bits_false {n : ℕ} (C : Circuit) (S A : Base n) (o : ℕ)
    (he : Exact C S o) (hd : Disjoint A S) : value C (bits A) o = false := by
  rw [he]
  simp only [decide_eq_false_iff_not, bits, decide_eq_true_eq]
  exact fun ⟨p,hpS,hpA⟩ => (Finset.disjoint_left.mp hd) hpA hpS

lemma light_count {n : ℕ} (C : Circuit) (t k : ℕ) (hL : Legal C) (hOnly : Only C t)
    (hLight : Light (n:=n) C t k) (hk : 2 ≤ k) (S : Base n) (o : ℕ) (he : Exact C S o) :
    min k S.card ≤ (windowG (pin C t true) ∅ S).card + 1 := by
  apply window_bound (pin C t true) (pin_mono C t true hL hOnly) ∅ S o k (by simp)
  · intro p hp
    let x : Fin n → Bool := fun v => decide (v ∈ (∅ : Base n) ∨ v = p)
    have hX : x = bits {p} := by funext v; simp [x,bits]
    have ht : value C x (n+t) = true := by
      apply hLight
      rw [hX,true_count_bits,Finset.card_singleton]
      omega
    change value (pin C t true) x o = true
    rw [pin_value C t true x o (Or.inr ht),he x]
    exact decide_eq_true ⟨p,hp,by simp [x]⟩
  · intro A hAd hsmall
    let x := bits ((∅ : Base n) ∪ A)
    have hx : x = bits A := by simp [x]
    have ht : value C x (n+t) = true := by
      apply hLight
      rwa [hx,true_count_bits]
    change value (pin C t true) x o = false
    rw [pin_value C t true x o (Or.inr ht),hx]
    exact exact_bits_false C S A o he hAd


lemma light_support {n : ℕ} (C : Circuit) (t k : ℕ)
    (hLight : Light (n := n) C t k) (hk : 2 ≤ k) (w : ℕ) :
    supp (pin C t true) (∅ : Base n) w = supp C (∅ : Base n) w := by
  ext p
  simp only [mem_supp]
  let x : Fin n → Bool := fun v => decide (v ∈ (∅ : Base n) ∨ v = p)
  change (value (pin C t true) x w = true ↔ value C x w = true)
  have hx : x = bits {p} := by
    funext v
    simp [x,bits]
  have ht : value C x (n+t) = true := by
    apply hLight
    rw [hx,true_count_bits,Finset.card_singleton]
    omega
  rw [pin_value C t true x w (Or.inr ht)]

def singletonGates {n : ℕ} (C : Circuit) (S : Base n) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun g => supp C ∅ (n+g) ⊆ S ∧ 2 ≤ (supp C (∅ : Base n) (n+g)).card

lemma charge_card_le {n : ℕ} (C : Circuit) (t k : ℕ)
    (hLight : Light (n := n) C t k) (hk : 2 ≤ k) (S : Base n) :
    (windowG (pin C t true) ∅ S).card ≤ (singletonGates C S).card := by
  let e : Fin C.gates.length ↪ ℕ := ⟨fun g => n+(g:ℕ),by
    intro a b h
    exact Fin.ext (Nat.add_left_cancel h)⟩
  rw [← Finset.card_map e]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hlo,hhi⟩ := windowG_bounds _ ∅ S hw
  rw [pin_size] at hhi
  let g : Fin C.gates.length := ⟨w-n,by unfold Circuit.size at hhi; omega⟩
  have hg : n+(g:ℕ) = w := by change n+(w-n) = w; omega
  apply Finset.mem_map.mpr
  refine ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ g,?_⟩,hg⟩
  rw [hg]
  have hdata := (Finset.mem_filter.mp hw).2
  rw [light_support C t k hLight hk w] at hdata
  exact hdata

end PEqualNP.Outside.L_meta_1594

open PEqualNP.Outside.L_meta_1594 in
theorem PEqualNP.Outside.L_meta_1594 : (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → ∀ (N M : ℕ) (A : Fin M → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin M → ℕ) (t : ℕ) (Y : Finset (Fin N)), (∀ ab1 ab2 : Fin M, ab1 ≠ ab2 → (A ab1 ∩ A ab2).card ≤ 1) → (∀ eb1 ∈ D.gates, (eb1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ eb1.inputs.length ≤ 2) → (∀ lb1 : Fin D.gates.length, (D.gates.get lb1).op = PEqualNP.CircuitLowerBounds.GateOp.not → (lb1 : ℕ) = t) → (∀ (ab3 : Fin M) (zb1 : Fin N → Bool), (D.wires (List.ofFn zb1)).getD (u ab3) false = decide (∃ sb1 ∈ A ab3, zb1 sb1 = true)) → (∀ zb2 : Fin N → Bool, (Finset.univ.filter (fun vb1 : Fin N => zb2 vb1 = true)).card < Y.card → (D.wires (List.ofFn zb2)).getD (N + t) false = true) → (D.wires (List.ofFn (fun vb2 : Fin N => decide (vb2 ∈ Y)))).getD (N + t) false = false → 2 ≤ Y.card → ∀ b4 : Fin M, min Y.card (A b4).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length => (∀ s2 : Fin N, (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 = s2)))).getD (N + h1) false = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N => (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 = s3)))).getD (N + h1) false = true)).card)).card + 1
    := by
  intro _ _ N M A D u t Y _ hL hOnly hE hLight _ hY i
  have h := light_count D t Y.card hL hOnly hLight hY (A i) (u i) (hE i)
  have hbound := h.trans (Nat.add_le_add_right (charge_card_le D t Y.card hLight hY (A i)) 1)
  simpa only [singletonGates,supp,Finset.subset_iff,Finset.mem_filter,Finset.mem_univ,
    true_and,Finset.notMem_empty,false_or,value] using hbound
