import Mathlib
import PEqualNP.Defs

-- The restriction recursion uses the repository FewNot helpers and checked L-meta-270 and L-meta-669.
-- The trace and incidence facts use checked L-meta-1049.

namespace PEqualNP.Outside.L_meta_1325.Sparse

open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
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

private lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := by
    cases h : g.inputs with
    | nil => simp [h] at hlen
    | cons a rest =>
      cases rest with
      | nil => simp [h] at hlen
      | cons b tail =>
        have : tail = [] := by simpa [h] using hlen
        exact ⟨a, b, by simp [this]⟩
  let P := ({a, b} : Finset ℕ).filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ?_, ?_, ?_⟩
  · by_cases h : a = b <;> simp [h, Finset.card_insert_of_notMem]
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ ({a, b} : Finset ℕ)) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨hr, h⟩)
      · simp [h]
    have ha := hr a (by simp)
    have hb := hr b (by simp)
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval
          [if a < w then value C z a else false, if b < w then value C z b else false] := by
      simpa [g, hab] using gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
        Bool.and_eq_true] at hx ⊢
      exact ⟨ha hx.1, hb hx.2⟩
    · simp only [hop, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
        Bool.or_eq_true] at hx ⊢
      exact hx.imp ha hb

private lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
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

private lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
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

private def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

private lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

private lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

private def assigned {n : ℕ} (C : Circuit) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => support C w ⊆ T ∧ 2 ≤ (support (n := n) C w).card

private lemma card_assigned {n k c : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ T)
    (hsparse : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ T, x q = false) → value C x o = false)
    (hk : c ≤ k) (hc : c + 1 ≤ T.card) : c ≤ (assigned C T).card := by
  classical
  let G := assigned C T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < c at hsmall
    omega
  let clean (w : ℕ) : Finset (Fin n) := if support C w ⊆ T then support C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : support C w ⊆ T
    · change (if support C w ⊆ T then support (n := n) C w else ∅).card ≤ 1
      rw [ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w (by omega)), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let D := B.filter (fun w => ¬ support C w ⊆ T)
  have hout (w : {w // w ∈ D}) : ∃ q : Fin n, q ∈ support C w.val ∧ q ∉ T := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hout
  let U := D.attach.image q
  let y : Fin n → Bool := fun r => decide (r ∈ U)
  have hu : U.card ≤ k := calc
    U.card ≤ D.attach.card := Finset.card_image_le
    _ = D.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ k := hb.trans hk
  have hyfalse : value C y o = false := by
    apply hsparse y
    · have hset : Finset.univ.filter (fun r => y r = true) = U := by ext r; simp [y]
      rwa [hset]
    · intro r hr
      have hnot : r ∉ U := by
        intro hmem
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
        exact (hq w).2 hr
      simp [y, hnot]
  have hytrue : value C y o = true := by
    apply hcut (fun r => decide (r = p)) y _ o (Finset.mem_singleton_self o) ((ho p).mpr hp)
    intro w hw hx
    by_cases hs : support C w ⊆ T
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_left hs, mem_support] using hx⟩))
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (fun r => decide (r = q d)) y _ w ((mem_support C w (q d)).mp (hq d).1)
      intro r hr
      have he : r = q d := of_decide_eq_true hr
      subst r
      have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp [y, hm]
  simp [hyfalse] at hytrue




theorem main :
    ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (o : Fin m → ℕ) (c : Fin m → ℕ),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ i : Fin m, 2 ≤ (S i).card) →
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      (∀ (i : Fin m) (p : Fin n),
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) →
      (∀ (i : Fin m) (x : Fin n → Bool),
        (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
        (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
      (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) →
      ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hinter _ hG ho hsparse hk hc
  let G (i : Fin m) := assigned C (S i)
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
    have hi := (Finset.mem_filter.mp hwi).2
    have hj := (Finset.mem_filter.mp hwj).2
    have hsub : support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi.1 hp, hj.1 hp⟩
    have hle := Finset.card_le_card hsub
    have hsmall := hinter i j hij
    omega
  calc
    ∑ i : Fin m, c i ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ =>
      card_assigned C (S i) (o i) hG (ho i) (hsparse i) (hk i) (hc i)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun w hw => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = C.size := by simp

end PEqualNP.Outside.L_meta_1325.Sparse
namespace PEqualNP.Outside.L_meta_1325.Restrict

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

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, le_refl _, rep_input ρ hρ⟩

lemma inv_final {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (gates : List Gate)
    (h : Inv ρ gates) :
    ∃ (gates' : List Gate) (r : ℕ → ℕ), (∀ g ∈ gates', Fan g) ∧ gates'.length ≤ gates.length ∧
      ∀ o : ℕ, (∃ x y : Fin n → Bool,
        (W gates (ρ x)).getD o false ≠ (W gates (ρ y)).getD o false) →
        ∀ x : Fin n → Bool, (W gates' x).getD (r o) false = (W gates (ρ x)).getD o false := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  have hsel : ∀ o : ℕ, ∃ j : ℕ,
      (∃ c : Bool, ∀ x : Fin n → Bool, (W gates (ρ x)).getD o false = c) ∨
      (∀ x : Fin n → Bool, (W new x).getD j false = (W gates (ρ x)).getD o false) := by
    intro o
    rcases hrep o with hc | ⟨j, _, hj⟩
    · exact ⟨0, Or.inl hc⟩
    · exact ⟨j, Or.inr hj⟩
  choose r hr using hsel
  refine ⟨new, r, hfan, hl, ?_⟩
  intro o hne x
  rcases hr o with ⟨c, hc⟩ | hj
  · obtain ⟨x1, y1, hxy⟩ := hne
    exact absurd ((hc x1).trans (hc y1).symm) hxy
  · exact hj x

theorem main_aux : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) := by
  intro n gates T Z hg
  have hρ : ∀ i : Fin n,
      (∃ c : Bool, ∀ x : Fin n → Bool,
        (if i ∈ T then true else if i ∈ Z then false else x i) = c) ∨
      (∀ x : Fin n → Bool, (if i ∈ T then true else if i ∈ Z then false else x i) = x i) := by
    intro i
    by_cases h1 : i ∈ T
    · exact Or.inl ⟨true, fun x => by rw [if_pos h1]⟩
    · by_cases h2 : i ∈ Z
      · exact Or.inl ⟨false, fun x => by rw [if_neg h1, if_pos h2]⟩
      · exact Or.inr (fun x => by rw [if_neg h1, if_neg h2])
  exact inv_final (fun (x : Fin n → Bool) (i : Fin n) =>
    if i ∈ T then true else if i ∈ Z then false else x i) gates
    (inv_all _ hρ gates hg)

end PEqualNP.Outside.L_meta_1325.Restrict
namespace PEqualNP.Outside.L_meta_1325.Trace

open PEqualNP.CircuitLowerBounds

def Allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def Positive (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def gateValue (values : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun w => values.getD w false)

def appendGate (values : List Bool) (g : Gate) : List Bool :=
  values ++ [gateValue values g]

def run (gates : List Gate) (values : List Bool) : List Bool :=
  gates.foldl appendGate values

def Below (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ w, x.getD w false = true → y.getD w false = true

theorem gateValue_pos (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (a b : List Bool) (h : Below a b) :
    gateValue a g = true → gateValue b g = true := by
  unfold gateValue
  rcases hop with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro ha w hw
    exact h.2 w (ha w hw)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨w, hw, ha⟩
    exact ⟨w, hw, h.2 w ha⟩

theorem gateValue_neg (g : Gate) (hop : g.op = .not) (a b : List Bool) (h : Below a b) :
    gateValue b g = true → gateValue a g = true := by
  unfold gateValue
  rw [hop]
  cases hi : g.inputs with
  | nil => simp [GateOp.eval]
  | cons w ws =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro hf
    cases ha : a.getD w false
    · rfl
    · exact (Bool.false_ne_true (hf.symm.trans (h.2 w ha))).elim

theorem appendGate_below {a b : List Bool} (h : Below a b) (g : Gate)
    (hg : gateValue a g = true → gateValue b g = true) :
    Below (appendGate a g) (appendGate b g) := by
  refine ⟨by simp [appendGate, h.1], ?_⟩
  intro w
  unfold appendGate
  by_cases hw : w < a.length
  · have hwb : w < b.length := h.1 ▸ hw
    rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hwb]
    exact h.2 w
  · have ha := Nat.le_of_not_gt hw
    have hb : b.length ≤ w := h.1 ▸ ha
    rw [List.getD_append_right _ _ _ _ ha, List.getD_append_right _ _ _ _ hb, h.1]
    cases he : w - b.length with
    | zero => simpa using hg
    | succ k => simp

theorem initial_below {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    Below (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro w
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hw
    simpa using h ⟨w, hw⟩
  · simp

theorem run_cons (g : Gate) (gs : List Gate) (a : List Bool) :
    run (g :: gs) a = run gs (appendGate a g) := rfl

theorem run_keeps (gs : List Gate) (a : List Bool) {w : ℕ} (h : w < a.length) :
    (run gs a).getD w false = a.getD w false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp [appendGate]; omega), appendGate, List.getD_append _ _ _ _ h]

theorem value_first (g : Gate) (gs : List Gate) (a : List Bool) :
    (run (g :: gs) a).getD a.length false = gateValue a g := by
  rw [run_cons, run_keeps _ _ (by simp [appendGate]), appendGate]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl a.length)]
  simp

theorem next_index (g : Gate) (gs : List Gate) (a : List Bool) (j : ℕ) :
    (run gs (appendGate a g)).getD ((appendGate a g).length + j) false =
      (run (g :: gs) a).getD (a.length + (j + 1)) false := by
  congr 1
  simp [appendGate]
  omega

def AgreesNot (gs : List Gate) (a b : List Bool) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .not →
    (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false

theorem AgreesNot.tail {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) :
    AgreesNot gs (appendGate a g) (appendGate b g) := by
  intro j q hj hq
  rw [next_index, next_index]
  exact h (j+1) q (by simpa using hj) hq

theorem AgreesNot.first {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) (hg : g.op = .not) :
    gateValue a g = gateValue b g := by
  have h0 := h 0 g rfl hg
  simpa only [Nat.add_zero, value_first] using h0

theorem run_below (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (hnot : AgreesNot gs a b) :
    Below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons, run_cons]
    apply ih _ _ (appendGate_below h g ?_)
      (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    rcases (hops _ (List.mem_cons_self ..)).1 with ha | ho | hn
    · exact gateValue_pos g (Or.inl ha) a b h
    · exact gateValue_pos g (Or.inr ho) a b h
    · rw [hnot.first hn]
      exact id

def booleanGate : Bool → Gate
  | true => ⟨.and, []⟩
  | false => ⟨.or, []⟩

theorem booleanGate_pos (b : Bool) : Positive (booleanGate b) := by
  cases b <;> simp [Positive, booleanGate]

theorem booleanGate_runs (b : Bool) (x : List Bool) :
    gateValue x (booleanGate b) = b := by
  cases b <;> rfl

noncomputable def freezeGate (a : List Bool) (g : Gate) : Gate := by
  classical
  exact if g.op = .not then booleanGate (gateValue a g) else g

noncomputable def freeze (a : List Bool) : List Gate → List Gate
  | [] => []
  | g :: gs => freezeGate a g :: freeze (appendGate a g) gs

theorem freeze_length (gs : List Gate) (a : List Bool) : (freeze a gs).length = gs.length := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => simp [freeze, ih]

theorem freeze_pos (gs : List Gate) (a : List Bool) (h : ∀ g ∈ gs, Allowed g) :
    ∀ g ∈ freeze a gs, Positive g := by
  induction gs generalizing a with
  | nil => simp [freeze]
  | cons g gs ih =>
    intro q hq
    rw [freeze, List.mem_cons] at hq
    rcases hq with rfl | hq
    · classical
      unfold freezeGate
      split
      · exact booleanGate_pos _
      · rename_i hn
        obtain ⟨ha | ho | hh, hf⟩ := h g (List.mem_cons_self ..)
        · exact ⟨Or.inl ha, hf⟩
        · exact ⟨Or.inr ho, hf⟩
        · exact (hn hh).elim
    · exact ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq)) _ hq

theorem freeze_run (gs : List Gate) (a b z : List Bool)
    (haz : Below a z) (hzb : Below z b) (hops : ∀ g ∈ gs, Allowed g)
    (hnot : AgreesNot gs a b) : run (freeze a gs) z = run gs z := by
  induction gs generalizing a b z with
  | nil => rfl
  | cons g gs ih =>
    rw [freeze, run_cons, run_cons]
    have hA : g ∈ g :: gs := List.mem_cons_self
    have hop := (hops g hA).1
    rcases hop with h | h | h
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inl h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inl h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inr h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inr h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have he : gateValue a g = gateValue b g := hnot.first h
      have hze : gateValue z g = gateValue a g := by
        apply Bool.eq_iff_iff.mpr
        refine ⟨gateValue_neg g h a z haz, ?_⟩
        rw [he]
        exact gateValue_neg g h z b hzb
      have hf : appendGate z (freezeGate a g) = appendGate z g := by
        classical
        unfold appendGate
        simp [freezeGate, h, booleanGate_runs, hze]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (by rw [hze]; exact id))
        (appendGate_below hzb g (by rw [hze, he]; exact id))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail

theorem note_antitone (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (i : ℕ) (g : Gate) (hi : gs[i]? = some g)
    (hg : g.op = .not)
    (hprev : ∀ (j : ℕ) (q : Gate), j < i → gs[j]? = some q → q.op = .not →
      (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false) :
    (run gs b).getD (b.length + i) false = true →
      (run gs a).getD (a.length + i) false = true := by
  induction gs generalizing a b i g with
  | nil => simp at hi
  | cons q gs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst g
      simpa only [Nat.add_zero, value_first] using gateValue_neg q hg a b h
    | succ i =>
      have hb : Below (appendGate a q) (appendGate b q) := by
        apply appendGate_below h
        rcases (hops q (List.mem_cons_self ..)).1 with ha | ho | hn
        · exact gateValue_pos q (Or.inl ha) a b h
        · exact gateValue_pos q (Or.inr ho) a b h
        · have he := hprev 0 q (Nat.zero_lt_succ i) rfl hn
          simp only [Nat.add_zero, value_first] at he
          rw [he]
          exact id
      have hpre (j : ℕ) (r : Gate) (hji : j < i) (hj : gs[j]? = some r)
          (hr : r.op = .not) :
          (run gs (appendGate a q)).getD ((appendGate a q).length + j) false =
          (run gs (appendGate b q)).getD ((appendGate b q).length + j) false := by
        rw [next_index, next_index]
        exact hprev (j+1) r (by omega) (by simpa using hj) hr
      have got := ih _ _ hb (fun r hr => hops r (List.mem_cons_of_mem _ hr))
        i g (by simpa using hi) hg hpre
      rwa [next_index, next_index] at got

noncomputable def notIndices (gs : List Gate) : Finset (Fin gs.length) := by
  classical
  exact Finset.univ.filter (fun i => (gs.get i).op = .not)

theorem mem_notIndices (gs : List Gate) (j : Fin gs.length) :
    j ∈ notIndices gs ↔ (gs.get j).op = .not := by
  classical
  simp [notIndices]

noncomputable def notEmbedding (gs : List Gate) :
    Fin (notIndices gs).card ↪o Fin gs.length :=
  (notIndices gs).orderEmbOfFin rfl

theorem notEmbedding_mem (gs : List Gate) (j : Fin (notIndices gs).card) :
    notEmbedding gs j ∈ notIndices gs :=
  (notIndices gs).orderEmbOfFin_mem rfl j

theorem exists_notEmbedding (gs : List Gate) (j : Fin gs.length)
    (hj : j ∈ notIndices gs) : ∃ i, notEmbedding gs i = j := by
  have h := (notIndices gs).range_orderEmbOfFin rfl
  change Set.range (notEmbedding gs) = _ at h
  change j ∈ Set.range (notEmbedding gs)
  rw [h]
  exact hj

theorem card_notIndices (gs : List Gate) (t : ℕ)
    (h : ∃ f : Fin t → Fin gs.length,
      ∀ i : Fin gs.length, (gs.get i).op = .not → ∃ j, f j = i) :
    (notIndices gs).card ≤ t := by
  classical
  obtain ⟨f, h⟩ := h
  have hsub : notIndices gs ⊆ Finset.univ.image f := by
    intro j hj
    obtain ⟨i, hi⟩ := h j ((mem_notIndices gs j).1 hj)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

def trace {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length) : Bool :=
  (run gs (List.ofFn x)).getD (n + i.val) false

theorem trace_after {n m : ℕ} (gs : List Gate) (x : Fin m → Fin n → Bool)
    (hx : ∀ a b : Fin m, a ≤ b → ∀ w, x a w = true → x b w = true)
    (hg : ∀ g ∈ gs, Allowed g)
    (i : Fin (notIndices gs).card) (a b : Fin m) (hab : a ≤ b)
    (hprev : ∀ j : Fin (notIndices gs).card, j < i →
      trace gs (x a) (notEmbedding gs j) = trace gs (x b) (notEmbedding gs j)) :
    trace gs (x b) (notEmbedding gs i) = true →
      trace gs (x a) (notEmbedding gs i) = true := by
  let j := notEmbedding gs i
  have hj := (mem_notIndices gs j).1 (notEmbedding_mem gs i)
  have hi : gs[j.val]? = some (gs.get j) := List.getElem?_eq_getElem j.isLt
  have got := note_antitone gs (List.ofFn (x a)) (List.ofFn (x b))
    (initial_below _ _ (hx a b hab)) hg j.val (gs.get j) hi hj
  have earlier (k : ℕ) (q : Gate) (hk : k < j.val) (hq : gs[k]? = some q)
      (hqn : q.op = .not) :
      (run gs (List.ofFn (x a))).getD ((List.ofFn (x a)).length + k) false =
      (run gs (List.ofFn (x b))).getD ((List.ofFn (x b)).length + k) false := by
    have hkl : k < gs.length := by
      apply lt_trans hk
      exact j.isLt
    let k' : Fin gs.length := ⟨k, hkl⟩
    have hget : gs.get k' = q := by simpa [k', List.getElem?_eq_getElem hkl] using hq
    obtain ⟨p, hp⟩ := exists_notEmbedding gs k'
      ((mem_notIndices gs k').2 (hget ▸ hqn))
    have hpi : p < i := by
      have hlt : notEmbedding gs p < notEmbedding gs i := by
        rw [hp]
        exact hk
      exact (notEmbedding gs).lt_iff_lt.mp hlt
    have h := hprev p hpi
    rw [hp] at h
    simpa only [trace, List.length_ofFn, k'] using h
  simpa only [trace, List.length_ofFn, j] using got earlier

theorem trace_agrees {n : ℕ} (gs : List Gate) (a b : Fin n → Bool)
    (h : ∀ i : Fin (notIndices gs).card,
      trace gs a (notEmbedding gs i) = trace gs b (notEmbedding gs i)) :
    AgreesNot gs (List.ofFn a) (List.ofFn b) := by
  intro j g hj hg
  have hlt : j < gs.length := (List.getElem?_eq_some_iff.mp hj).choose
  let i : Fin gs.length := ⟨j, hlt⟩
  have he : gs.get i = g := by simpa [i, List.getElem?_eq_getElem hlt] using hj
  obtain ⟨p, hp⟩ := exists_notEmbedding gs i
    ((mem_notIndices gs i).2 (he ▸ hg))
  have hh := h p
  rw [hp] at hh
  simpa only [trace, List.length_ofFn, i] using hh

lemma existsCuts {t m : ℕ} (p : Fin t → Fin m → Bool)
    (h : ∀ (i : Fin t) (a b : Fin m), a ≤ b →
      (∀ j : Fin t, j < i → p j a = p j b) → (p i b = true → p i a = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.range m ∧ P.card + 1 ≤ 2 ^ t ∧
      ∀ a b : Fin m, a ≤ b → (∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) →
        ∀ i : Fin t, p i a = p i b := by
  induction t with
  | zero =>
      refine ⟨∅, by simp, by simp, ?_⟩
      intro _ _ _ _ i
      exact Fin.elim0 i
  | succ t ih =>
      let p₀ (i : Fin t) := p i.castSucc
      have h₀ : ∀ (i : Fin t) (a b : Fin m), a ≤ b →
          (∀ j : Fin t, j < i → p₀ j a = p₀ j b) →
          (p₀ i b = true → p₀ i a = true) := by
        intro i a b hab hearlier htrue
        apply h i.castSucc a b hab ?_ htrue
        intro j hj
        have hjt : j.val < t := lt_of_lt_of_le hj i.isLt.le
        exact hearlier ⟨j.val, hjt⟩ (by exact hj)
      obtain ⟨P, hP, hp, stable⟩ := ih p₀ h₀
      have hlast {a b : Fin m} (hab : a ≤ b)
          (hgood : ∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) :
          p (Fin.last t) b = true → p (Fin.last t) a = true := by
        apply h (Fin.last t) a b hab
        intro j hj
        exact stable a b hab hgood ⟨j.val, hj⟩
      let value (w : ℕ) : Bool := if hw : w < m then p (Fin.last t) ⟨w, hw⟩ else false
      have value_eq (w : ℕ) (hw : w < m) : value w = p (Fin.last t) ⟨w, hw⟩ := dite_eq_left hw
      let N := (Finset.range m).filter (fun w =>
        0 < w ∧ w ∉ P ∧ value (w - 1) = true ∧ value w = false)
      have hN {w : ℕ} (hw : w ∈ N) :
          w < m ∧ 0 < w ∧ w ∉ P ∧ value (w - 1) = true ∧ value w = false := by
        have he := Finset.mem_filter.mp hw
        exact ⟨Finset.mem_range.mp he.1, he.2⟩
      let before (w : ℕ) := P.filter (fun k => k ≤ w)
      have hsep {u v : ℕ} (hu : u ∈ N) (hv : v ∈ N) (hlt : u < v) :
          (before u).card ≠ (before v).card := by
        intro he
        have hsub : before u ⊆ before v := by
          intro k hk
          obtain ⟨hkP, hku⟩ := Finset.mem_filter.mp hk
          exact Finset.mem_filter.mpr ⟨hkP, le_trans hku hlt.le⟩
        have heq : before u = before v :=
          Finset.eq_of_subset_of_card_le hsub he.ge
        have hnocut : ∀ w ∈ P, ¬ (u < w ∧ w ≤ v - 1) := by
          intro w hw hinterval
          have hwv : w ∈ before v :=
            Finset.mem_filter.mpr ⟨hw, hinterval.2.trans (Nat.sub_le ..)⟩
          rw [← heq] at hwv
          exact (not_le_of_gt hinterval.1) (Finset.mem_filter.mp hwv).2
        have huu := hN hu
        have hvv := hN hv
        have hvlt : v - 1 < m := lt_of_le_of_lt (Nat.sub_le ..) hvv.1
        have htrans := hlast
          (a := ⟨u, huu.1⟩) (b := ⟨v - 1, hvlt⟩)
          (by show u ≤ v - 1; omega) hnocut
        have htrue : value u = true := by
          rw [value_eq _ huu.1]
          apply htrans
          rw [← value_eq _ hvlt]
          exact hvv.2.2.2.1
        rw [huu.2.2.2.2] at htrue
        contradiction
      have hcount : N.card ≤ P.card + 1 := by
        simpa only [Finset.card_range] using
          (Finset.card_le_card_of_injOn
            (s := N) (t := Finset.range (P.card + 1))
            (fun w => (before w).card)
            (fun w _ => Finset.mem_range.mpr (Nat.lt_succ_of_le
              (Finset.card_filter_le _ _)))
            (by
              intro u hu v hv he
              rcases lt_trichotomy u v with hlt | heq | hgt
              · exact False.elim (hsep hu hv hlt he)
              · exact heq
              · exact False.elim (hsep hv hu hgt he.symm)))
      refine ⟨P ∪ N, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hP hw
        · exact Finset.mem_range.mpr (hN hw).1
      · have hU := Finset.card_union_le P N
        rw [Nat.pow_succ]
        omega
      · intro a b hab hgood i
        have hprev : ∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val) :=
          fun w hw => hgood w (Finset.mem_union_left _ hw)
        by_cases hi : i.val < t
        · exact stable a b hab hprev ⟨i.val, hi⟩
        · have hie : i = Fin.last t := by
            apply Fin.ext
            have hi' := i.isLt
            change i.val = t
            omega
          subst i
          have hadj (w : ℕ) (haw : a.val < w) (hwb : w ≤ b.val) :
              value (w - 1) = value w := by
            have hw : w < m := hwb.trans_lt b.isLt
            have hw' : w - 1 < m := (Nat.sub_le ..).trans_lt hw
            have hpos : 0 < w := by omega
            have hpw : w ∉ P := fun hmem => hprev w hmem ⟨haw, hwb⟩
            have hnW : w ∉ N :=
              fun hmem => hgood w (Finset.mem_union_right _ hmem) ⟨haw, hwb⟩
            have hstep := hlast
              (a := ⟨w - 1, hw'⟩) (b := ⟨w, hw⟩)
              (Nat.sub_le ..)
              (by
                rintro k hk ⟨hkw, hwk⟩
                change w - 1 < k at hkw
                change k ≤ w at hwk
                have he : k = w := by omega
                exact hpw (he ▸ hk))
            have himp : value w = true → value (w - 1) = true := by
              rw [value_eq _ hw, value_eq _ hw']
              exact hstep
            cases hr : value w <;> cases hl : value (w - 1)
            · rfl
            · exact False.elim (hnW (Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr hw, hpos, hpw, hl, hr⟩))
            · exact False.elim (Bool.false_ne_true (hl.symm.trans (himp hr)))
            · rfl
          have hdist : ∀ d : ℕ, a.val + d ≤ b.val → value (a.val + d) = value a.val := by
            intro d
            induction d with
            | zero => simp
            | succ d ih =>
                intro hd
                have hprev' := ih (by omega)
                have hs := hadj (a.val + (d + 1)) (by omega) hd
                have he : a.val + (d + 1) - 1 = a.val + d := by omega
                rw [he] at hs
                exact hs.symm.trans hprev'
          have hab' : a.val ≤ b.val := hab
          have hdist' := hdist (b.val - a.val) (by omega)
          have he : a.val + (b.val - a.val) = b.val := by omega
          rw [he, value_eq _ b.isLt, value_eq _ a.isLt] at hdist'
          exact hdist'.symm

end PEqualNP.Outside.L_meta_1325.Trace
namespace PEqualNP.Outside.L_meta_1325.Incidence

open PEqualNP.CircuitLowerBounds

def through {n : ℕ} (S : Fin n → Finset (Fin n)) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p ∈ S i)

theorem through_card {n q : ℕ} (S : Fin n → Finset (Fin n))
    (hn : n = q*q + q + 1) (hq : 0 < q)
    (hS : ∀ i, (S i).card = q+1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hjoin : ∀ p p' : Fin n, p ≠ p' → ∃ i, p ∈ S i ∧ p' ∈ S i)
    (p : Fin n) : (through S p).card = q + 1 := by
  let T := through S p
  have hdis : (T : Set (Fin n)).PairwiseDisjoint (fun i => (S i).erase p) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hpi : p ∈ S i := by simpa [T, through] using hi
    have hpj : p ∈ S j := by simpa [T, through] using hj
    have hp : p ∈ S i ∩ S j := Finset.mem_inter.mpr ⟨hpi, hpj⟩
    have ha' : a ∈ S i ∩ S j := Finset.mem_inter.mpr
      ⟨Finset.mem_of_mem_erase ha, Finset.mem_of_mem_erase hb⟩
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hcross i j hij)
    have hpv : p = v := by simpa [hv] using hp
    have hav : a = v := by simpa [hv] using ha'
    exact (Finset.mem_erase.mp ha).1 (hav.trans hpv.symm)
  have hcover : T.biUnion (fun i => (S i).erase p) =
      (Finset.univ : Finset (Fin n)).erase p := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, hmem⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hmem).1, Finset.mem_univ _⟩
    · intro ha
      have hpa : p ≠ a := Ne.symm (Finset.mem_erase.mp ha).1
      obtain ⟨i, hpi, hai⟩ := hjoin p a hpa
      exact Finset.mem_biUnion.mpr ⟨i, by simpa [T, through] using hpi,
        Finset.mem_erase.mpr ⟨Ne.symm hpa, hai⟩⟩
  have hf (i : Fin n) (hi : i ∈ T) : ((S i).erase p).card = q := by
    have hpi : p ∈ S i := by simpa [T, through] using hi
    rw [Finset.card_erase_of_mem hpi, hS]
    omega
  have hcount := Finset.card_biUnion hdis
  rw [hcover, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  calc
    (through S p).card = T.card := rfl
    _ = q + 1 := by
      have hsum : (∑ i ∈ T, ((S i).erase p).card) = T.card * q := by
        rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul]
        rfl
      rw [hsum] at hcount
      have hmul : q * T.card = q * (q+1) := by
        rw [Nat.mul_comm q T.card, ← hcount, hn]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      exact Nat.eq_of_mul_eq_mul_left hq hmul

end PEqualNP.Outside.L_meta_1325.Incidence
namespace PEqualNP.Outside.L_meta_1325.OneNot

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]



theorem on1_wires_output (gs : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = Circuit.wires ⟨gs, o'⟩ x := rfl

theorem on1_wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = wiresFrom gs x := rfl

theorem on1_length_wires (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  length_wiresFrom C.gates x

theorem on1_getD_wires_of_ge (C : Circuit) (x : List Bool) (i : ℕ)
    (h : x.length + C.gates.length ≤ i) : (C.wires x).getD i false = false := by
  rw [List.getD_eq_default]; rw [on1_length_wires]; exact h

theorem on1_getD_wiresFrom_of_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (wiresFrom gs w).getD i false = false := by
  rw [List.getD_eq_default]; rw [length_wiresFrom]; exact h

theorem on1_wires_append (l1 l2 : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨l1 ++ l2, o⟩ x = wiresFrom l2 (Circuit.wires ⟨l1, o'⟩ x) :=
  wiresFrom_append l1 l2 x

theorem on1_wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem on1_wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem on1_getD_wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  show (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [getD_wiresFrom _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem on1_getD_append_left (w t : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := List.getD_append _ _ _ _ h

lemma on1_getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i,h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]


theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp





def on1_Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

theorem on1_above_snoc {v v' : List Bool} {a a' : Bool} (h : on1_Above v v')
    (ha : a = true → a' = true) : on1_Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst hiv
    rw [getD_snoc_eq] at hi
    rw [h.1, getD_snoc_eq]; exact ha hi
  · rw [getD_snoc_ne _ _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

theorem on1_above_wiresFrom (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v v' : List Bool, on1_Above v v' → on1_Above (wiresFrom gs v) (wiresFrom gs v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
    intro v v' h
    rw [on1_wiresFrom_cons, on1_wiresFrom_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    apply on1_above_snoc h
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

theorem on1_piece_h : ∀ (n : ℕ) (pre : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
    (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn y)).getD i false).headD false) = true := by
  intro n pre ins hpre x y hxy
  have hab : on1_Above (wiresFrom pre (List.ofFn x)) (wiresFrom pre (List.ofFn y)) := by
    apply on1_above_wiresFrom pre (fun g hg => (hpre g hg).1)
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hin : i < n
    · rw [on1_getD_ofFn _ _ hin] at hi ⊢; exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)
  cases ins with
  | nil => simp
  | cons j _ =>
    simp only [List.map_cons, List.headD_cons]
    exact hab.2 j

theorem on1_wires_slot (pre post : List Gate) (g g' : Gate) (o o' : ℕ) (x : List Bool)
    (h : g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)
      = g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)) :
    Circuit.wires ⟨pre ++ g :: post, o⟩ x = Circuit.wires ⟨pre ++ g' :: post, o'⟩ x := by
  rw [on1_wires_append _ _ o 0, on1_wires_append _ _ o' 0, on1_wiresFrom_cons,
    on1_wiresFrom_cons, h]

theorem on1_piece_d : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.all_nil]
  rw [h]; rfl

theorem on1_piece_u_cheap : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.any_nil]
  rw [h]; rfl

end PEqualNP.Outside.L_meta_1325.OneNot
namespace PEqualNP.Outside.L_meta_1325.FewNot

def fewNotBound (m q s b K : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun b' K' : ℕ => (if b' = 0 then m else m - (b' * q + 1)) * min K' q)
    (fun _ (g : ℕ → ℕ → ℕ) (b' K' : ℕ) =>
      (List.range (min K' (q + 1) + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (g (b' + j) (K' - j)) (g b' j))) 0)
    s b K

theorem fn_G_zero (m q b K : ℕ) :
    fewNotBound m q 0 b K = (if b = 0 then m else m - (b * q + 1)) * min K q := rfl

theorem fn_G_succ (m q s b K : ℕ) :
    fewNotBound m q (s + 1) b K =
      (List.range (min K (q + 1) + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (fewNotBound m q s (b + j) (K - j))
          (fewNotBound m q s b j))) 0 := rfl

theorem fn_le_foldr_max {f : ℕ → ℕ} {r j : ℕ} (hj : j ∈ List.range r) :
    f j ≤ (List.range r).foldr (fun (j acc : ℕ) => max acc (f j)) 0 := by
  suffices H : ∀ l : List ℕ, j ∈ l → f j ≤ l.foldr (fun (j acc : ℕ) => max acc (f j)) 0 from
    H _ hj
  intro l hl
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hl with h | h
    · subst h; exact le_max_right _ _
    · exact le_trans (ih h) (le_max_left _ _)

theorem fn_foldr_max_le {f : ℕ → ℕ} {r c : ℕ} (h : ∀ j ∈ List.range r, f j ≤ c) :
    (List.range r).foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤ c := by
  suffices H : ∀ l : List ℕ, (∀ j ∈ l, f j ≤ c) →
      l.foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤ c from H _ h
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (ih fun j hj => hl j (List.mem_cons_of_mem a hj)) (hl a List.mem_cons_self)



open PEqualNP.CircuitLowerBounds

def H270 : Prop :=
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

def H669 : Prop :=
  ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))

def PSub : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∃ (m' : ℕ) (e : Fin m' → Fin m), m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧ Function.Injective e ∧ (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧ (∀ i : Fin m', (S (e i)).card = q + 1) ∧ (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1)

def PSplit : Prop :=
  ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨ ∃ (s' : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ), s = s' + 1 ∧ gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } : PEqualNP.CircuitLowerBounds.Gate) :: post ∧ ins.length ≤ 2 ∧ (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ ∀ g' : PEqualNP.CircuitLowerBounds.Gate, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) → g'.inputs.length ≤ 2 → (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ ∃ ι' : Fin s' → Fin (pre ++ g' :: post).length, ∀ i : Fin (pre ++ g' :: post).length, ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s', ι' j = i

def H713 : Prop :=
  ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r

def Fam (n m q : ℕ) (S : Fin m → Finset (Fin n)) : Prop :=
  (∀ i : Fin m, (S i).card = q + 1) ∧
  (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧
  (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin m, p ∈ S i ∧ p' ∈ S i) ∧
  (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ q + 1)

def OpsOK (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2

def AndOr2 (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def NotAtMost (s : ℕ) (gates : List Gate) : Prop :=
  ∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
    (gates.get i).op = GateOp.not → ∃ j : Fin s, ι j = i

def Win {n : ℕ} (y : Finset (Fin n)) (K : ℕ) (x : Fin n → Bool) : Prop :=
  (∀ p ∈ y, x p = true) ∧ (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K

def Right {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (K : ℕ)
    (gates : List Gate) (out : Fin m → ℕ) : Prop :=
  ∀ (w : Fin m) (x : Fin n → Bool), Disjoint (S w) y → (∀ p ∈ y, x p = true) →
    (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K →
    Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)

theorem fnp_right_iff_win {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (K : ℕ) (gates : List Gate) (out : Fin m → ℕ) :
    Right S y K gates out ↔ ∀ (w : Fin m) (x : Fin n → Bool), Disjoint (S w) y → Win y K x →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true) :=
  ⟨fun h w x hd hw => h w x hd hw.1 hw.2, fun h w x hd h1 h2 => h w x hd ⟨h1, h2⟩⟩

def Claim (n m q : ℕ) (S : Fin m → Finset (Fin n)) (s : ℕ) : Prop :=
  ∀ (b K : ℕ) (y : Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ), y.card ≤ b →
    OpsOK gates → NotAtMost s gates → Right S y K gates out →
    fewNotBound m q s b K ≤ gates.length

def BoundPlane : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin m, p ∈ S i ∧ p' ∈ S i) →
    (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ q + 1) →
    ∀ s : ℕ, Claim n m q S s

def TargetPlane : Prop := H270 → H669 → BoundPlane

def PCount : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)), Fam n m q S → ∀ (b : ℕ) (y : Finset (Fin n)),
    y.card ≤ b → (if b = 0 then m else m - (b * q + 1)) ≤
      (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card

def fewNotGenG (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun b' K' : ℕ => (m - kappa b') * min K' (d - 1))
    (fun _ (g : ℕ → ℕ → ℕ) (b' K' : ℕ) =>
      (List.range (K' + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (g (b' + j) (K' - j)) (g b' j))) 0)
    s b K

theorem fnp_genG_zero (m d : ℕ) (kappa : ℕ → ℕ) (b K : ℕ) :
    fewNotGenG m d kappa 0 b K = (m - kappa b) * min K (d - 1) := rfl

theorem fnp_genG_succ (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ) :
    fewNotGenG m d kappa (s + 1) b K = (List.range (K + 1)).foldr
      (fun (j acc : ℕ) => max acc (min (fewNotGenG m d kappa s (b + j) (K - j))
        (fewNotGenG m d kappa s b j))) 0 := rfl

def FamG (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) : Prop :=
  (∀ i : Fin m, (S i).card = d) ∧
  (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧
  (∀ (b : ℕ) (y : Finset (Fin n)), y.card ≤ b →
    (Finset.univ.filter (fun w : Fin m => ¬ Disjoint (S w) y)).card ≤ kappa b)

def ClaimG (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ (b K : ℕ) (y : Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ), y.card ≤ b →
    OpsOK gates → NotAtMost s gates → Right S y K gates out →
    fewNotGenG m d kappa s b K ≤ gates.length

def BoundG : Prop :=
  ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ), FamG n m d S kappa →
    ∀ s : ℕ, ClaimG n m d S kappa s

def PSplitS : Prop :=
  ∀ (gates : List Gate) (s : ℕ), OpsOK gates → NotAtMost (s + 1) gates →
    NotAtMost s gates ∨
    ∃ (pre post : List Gate) (ins : List ℕ),
      gates = pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post ∧ AndOr2 pre ∧
      OpsOK (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) ∧
      OpsOK (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post) ∧
      NotAtMost s (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) ∧
      NotAtMost s (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post)

theorem fnp_splitS (h : PSplit) : PSplitS := by
  intro gates s hops hnot
  rcases h (s + 1) gates hops hnot with hno | ⟨s', pre, post, ins, hs, heq, _, hpre, hvar⟩
  · left
    obtain ⟨ι, _⟩ := hnot
    refine ⟨fun _ => ι 0, fun i hi => ?_⟩
    rcases (hno _ (List.get_mem gates i)).1 with h' | h' <;> rw [h'] at hi <;> cases hi
  · obtain rfl : s' = s := by omega
    right
    have ha := hvar { op := GateOp.and, inputs := [] } (Or.inl rfl) (by simp)
    have ho := hvar { op := GateOp.or, inputs := [] } (Or.inr rfl) (by simp)
    exact ⟨pre, post, ins, heq, hpre, ha.1, ho.1, ha.2, ho.2⟩

def H669at : Prop :=
  ∀ (n : ℕ) (gates : List Gate) (y : Finset (Fin n)), AndOr2 gates →
    ∃ (gates' : List Gate) (r : ℕ → ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      gates'.length ≤ gates.length ∧ ∀ o : ℕ,
      (∃ x x' : Fin n → Bool,
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x i)) ≠
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x' i))) →
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates', r o⟩ (List.ofFn x) =
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x i))

theorem fnp_669_at (h : H669) : H669at := fun n gates y hg => h n gates y ∅ hg

def PBaseG : Prop :=
  H270 → H669at → PSub → ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ),
    FamG n m d S kappa → ClaimG n m d S kappa 0

def PStepG : Prop :=
  PSplitS → ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ),
    FamG n m d S kappa → ∀ s : ℕ, ClaimG n m d S kappa s → ClaimG n m d S kappa (s + 1)

def PMono : Prop :=
  ∀ (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ),
    fewNotGenG m d kappa s b K ≤ fewNotGenG m d kappa s b (K + 1) ∧
    fewNotGenG m d kappa (s + 1) b K ≤ fewNotGenG m d kappa s b K ∧
    ((∀ b', kappa b' ≤ kappa (b' + 1)) → fewNotGenG m d kappa s (b + 1) K ≤ fewNotGenG m d kappa s b K)

theorem fnp_assemblyG (hS : PSub) (hSp : PSplit) (hB : PBaseG) (hSt : PStepG) :
    H270 → H669 → BoundG := by
  intro h270 h669 n m d S kappa hF s
  induction s with
  | zero => exact hB h270 (fnp_669_at h669) hS n m d S kappa hF
  | succ s ih => exact hSt (fnp_splitS hSp) n m d S kappa hF s ih

example (n : ℕ) (pre : List Gate) (ins : List ℕ) (hpre : AndOr2 pre) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hx : ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false)
      = true) :
    ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn y)).getD i false).headD false)
      = true :=
  OneNot.on1_piece_h n pre ins hpre x y hxy hx

theorem fnp_variant_length (pre post : List Gate) (g g' : Gate) :
    (pre ++ g :: post).length = (pre ++ g' :: post).length := by simp

def kappaPlane (q : ℕ) : ℕ → ℕ := fun b => if b = 0 then 0 else b * q + 1

theorem fnp_foldr_max_mono {f g : ℕ → ℕ} {r r' : ℕ} (hr : r ≤ r')
    (hfg : ∀ j ∈ List.range r, f j ≤ g j) :
    (List.range r).foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤
      (List.range r').foldr (fun (j acc : ℕ) => max acc (g j)) 0 :=
  fn_foldr_max_le fun j hj => le_trans (hfg j hj)
    (fn_le_foldr_max (List.mem_range.mpr (lt_of_lt_of_le (List.mem_range.mp hj) hr)))

theorem fnp_plane_le_genG (m q : ℕ) :
    ∀ s b K : ℕ, fewNotBound m q s b K ≤ fewNotGenG m (q + 1) (kappaPlane q) s b K
  | 0, b, K => by
    rw [fnp_genG_zero, fn_G_zero, kappaPlane]
    simp only [Nat.add_sub_cancel]
    split_ifs <;> simp
  | s + 1, b, K => by
    rw [fnp_genG_succ, fn_G_succ]
    exact fnp_foldr_max_mono (Nat.add_le_add_right (min_le_left _ _) 1) fun j _ =>
      min_le_min (fnp_plane_le_genG m q s _ _) (fnp_plane_le_genG m q s _ _)

theorem fnp_famG_of_fam (hC : PCount) (n m q : ℕ) (S : Fin m → Finset (Fin n))
    (hF : Fam n m q S) : FamG n m (q + 1) S (kappaPlane q) := by
  refine ⟨hF.1, hF.2.1, fun b y hy => ?_⟩
  have hc := hC n m q S hF b y hy
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun w : Fin m => Disjoint (S w) y)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  unfold kappaPlane
  split_ifs at hc ⊢ <;> omega

theorem fnp_claim_of_claimG (n m q : ℕ) (S : Fin m → Finset (Fin n)) (s : ℕ)
    (h : ClaimG n m (q + 1) S (kappaPlane q) s) : Claim n m q S s := by
  intro b K y gates out hy hops hnot hr
  exact le_trans (fnp_plane_le_genG m q s b K) (h b K y gates out hy hops hnot hr)



theorem fn_family_reindex (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∃ (m' : ℕ) (e : Fin m' → Fin m),
      m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧
      Function.Injective e ∧
      (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧
      (∀ i : Fin m', (S (e i)).card = q + 1) ∧
      (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1) := by
  classical
  set F := Finset.univ.filter (fun w : Fin m => Disjoint (S w) y) with hF
  let f := F.orderEmbOfFin (rfl : F.card = F.card)
  refine ⟨F.card, fun i => f i, rfl, f.injective, ?_, fun i => hcard _, ?_⟩
  · intro w
    have hr : Set.range f = (F : Set (Fin m)) := Finset.range_orderEmbOfFin F rfl
    constructor
    · intro hw
      have : w ∈ (F : Set (Fin m)) := by simp [hF, hw]
      rw [← hr] at this
      exact this
    · rintro ⟨i, rfl⟩
      have : f i ∈ (F : Set (Fin m)) := hr ▸ Set.mem_range_self i
      simpa [hF] using this
  · intro i j hij
    exact hmeet _ _ (fun h => hij (f.injective h))

open PEqualNP.CircuitLowerBounds

theorem fn_split_getElem?_ne (pre post : List Gate) (a b : Gate) (i : ℕ)
    (hi : i ≠ pre.length) : (pre ++ b :: post)[i]? = (pre ++ a :: post)[i]? := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - pre.length = k + 1 := ⟨i - pre.length - 1, by omega⟩
    rw [hk, List.getElem?_cons_succ, List.getElem?_cons_succ]

theorem fn_split_count (t : ℕ) (pre post : List Gate) (a b : Gate)
    (hb : b.op ≠ GateOp.not)
    (ι : Fin (t + 1) → Fin (pre ++ a :: post).length)
    (hι : ∀ i : Fin (pre ++ a :: post).length, ((pre ++ a :: post).get i).op = GateOp.not →
      ∃ j : Fin (t + 1), ι j = i)
    (j0 : Fin (t + 1)) (hj0 : (ι j0).val = pre.length) :
    ∃ ι' : Fin t → Fin (pre ++ b :: post).length,
      ∀ i : Fin (pre ++ b :: post).length, ((pre ++ b :: post).get i).op = GateOp.not →
        ∃ j : Fin t, ι' j = i := by
  have hlen : (pre ++ b :: post).length = (pre ++ a :: post).length := by simp
  refine ⟨fun j => ⟨(ι (j0.succAbove j)).val, by have := (ι (j0.succAbove j)).isLt; omega⟩, ?_⟩
  intro i hi
  have hne : i.val ≠ pre.length := by
    intro h
    apply hb
    have : (pre ++ b :: post).get i = b := by
      simp only [List.get_eq_getElem, h, List.getElem_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem_cons_zero]
    rw [← this]; exact hi
  have hget : (pre ++ a :: post).get ⟨i.val, by have := i.isLt; omega⟩ = (pre ++ b :: post).get i := by
    have := fn_split_getElem?_ne pre post a b i.val hne
    simp only [List.get_eq_getElem]
    rw [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem (by have := i.isLt; omega)] at this
    exact (Option.some.inj this).symm
  obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
  have hjne : j ≠ j0 := by
    rintro rfl
    apply hne
    rw [← hj0, hj]
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjne
  refine ⟨j', ?_⟩
  apply Fin.ext
  simp only [hj]

theorem fn_split_first : ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
        (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      1 ≤ s ∧
      ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
        (g' = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ∨
          g' = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }) →
        (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        ∃ ι' : Fin (s - 1) → Fin (pre ++ g' :: post).length,
          ∀ i : Fin (pre ++ g' :: post).length,
            ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
            ∃ j : Fin (s - 1), ι' j = i := by
  intro s gates hops hcnt
  by_cases hex : ∃ k, ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not
  · right
    classical
    let k := Nat.find hex
    obtain ⟨hk, hkop⟩ : ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not :=
      Nat.find_spec hex
    have hmin : ∀ i < k, ∀ hi : i < gates.length, (gates[i]'hi).op ≠ GateOp.not :=
      fun i hi hi' hop => Nat.find_min hex hi ⟨hi', hop⟩
    set pre := gates.take k with hpre
    set post := gates.drop (k + 1) with hpost
    have hprelen : pre.length = k := by simp [hpre]; omega
    have hsplit : gates = pre ++ gates[k] :: post := by
      rw [hpre, hpost, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have hgk : gates[k] = ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate) := by
      cases h : gates[k] with
      | mk op ins => rw [h] at hkop; simp only at hkop; subst hkop; rfl
    have hsplit' : gates = pre ++ ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate)
        :: post := by
      rw [← hgk]; exact hsplit
    obtain ⟨ι, hι⟩ := hcnt
    obtain ⟨j0, hj0⟩ := hι ⟨k, hk⟩ (by simpa using hkop)
    have hs : 1 ≤ s := by
      rcases s with _ | t
      · exact j0.elim0
      · omega
    refine ⟨pre, post, (gates[k]).inputs, hsplit', ?_, hs, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have hik : i < k := by omega
      have hig : i < gates.length := by omega
      have heq : pre[i] = gates[i] := by simp [hpre]
      rw [heq]
      obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] (List.getElem_mem hig)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 (hmin i hik hig)
    · intro g' hg'
      have hg'op : g'.op ≠ GateOp.not := by
        rcases hg' with rfl | rfl <;> simp
      refine ⟨?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with h | h
        · exact hops g (by rw [hsplit]; simp [h])
        · rcases List.mem_cons.mp h with h | h
          · subst h; rcases hg' with rfl | rfl <;> simp
          · exact hops g (by rw [hsplit]; simp [h])
      · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
        have hgl : gates.length = (pre ++ gates[k] :: post).length := by rw [← hsplit]
        let ι2 : Fin (t + 1) → Fin (pre ++ gates[k] :: post).length :=
          fun j => ⟨(ι j).val, by have := (ι j).isLt; omega⟩
        have hι2 : ∀ i : Fin (pre ++ gates[k] :: post).length,
            ((pre ++ gates[k] :: post).get i).op = GateOp.not → ∃ j, ι2 j = i := by
          intro i hi
          have hget : gates.get ⟨i.val, by have := i.isLt; omega⟩ = (pre ++ gates[k] :: post).get i := by
            simp only [List.get_eq_getElem]
            congr 1
          obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
          exact ⟨j, Fin.ext (by simp [ι2, hj])⟩
        exact fn_split_count t pre post gates[k] g' hg'op ι2 hι2 j0
          (by simp [ι2, hj0, hprelen])
  · left
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨i, hi, h1⟩ hex

theorem fn_split_general : ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
        (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (s' : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      s = s' + 1 ∧
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      ins.length ≤ 2 ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
        (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        g'.inputs.length ≤ 2 →
        (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        ∃ ι' : Fin s' → Fin (pre ++ g' :: post).length,
          ∀ i : Fin (pre ++ g' :: post).length,
            ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
            ∃ j : Fin s', ι' j = i := by
  intro s gates hops hcnt
  by_cases hex : ∃ k, ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not
  · right
    classical
    let k := Nat.find hex
    obtain ⟨hk, hkop⟩ : ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not :=
      Nat.find_spec hex
    have hmin : ∀ i < k, ∀ hi : i < gates.length, (gates[i]'hi).op ≠ GateOp.not :=
      fun i hi hi' hop => Nat.find_min hex hi ⟨hi', hop⟩
    set pre := gates.take k with hpre
    set post := gates.drop (k + 1) with hpost
    have hprelen : pre.length = k := by simp [hpre]; omega
    have hsplit : gates = pre ++ gates[k] :: post := by
      rw [hpre, hpost, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have hgk : gates[k] = ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate) := by
      cases h : gates[k] with
      | mk op ins => rw [h] at hkop; simp only at hkop; subst hkop; rfl
    have hsplit' : gates = pre ++ ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate)
        :: post := by
      rw [← hgk]; exact hsplit
    obtain ⟨ι, hι⟩ := hcnt
    obtain ⟨j0, hj0⟩ := hι ⟨k, hk⟩ (by simpa using hkop)
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := by
      rcases s with _ | t
      · exact j0.elim0
      · exact ⟨t, rfl⟩
    refine ⟨t, pre, post, (gates[k]).inputs, rfl, hsplit',
      (hops gates[k] (List.getElem_mem hk)).2, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have hik : i < k := by omega
      have hig : i < gates.length := by omega
      have heq : pre[i] = gates[i] := by simp [hpre]
      rw [heq]
      obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] (List.getElem_mem hig)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 (hmin i hik hig)
    · intro g' hg' hg'len
      have hg'op : g'.op ≠ GateOp.not := by
        rcases hg' with h | h <;> rw [h] <;> simp
      refine ⟨?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with h | h
        · exact hops g (by rw [hsplit]; simp [h])
        · rcases List.mem_cons.mp h with h | h
          · subst h
            rcases hg' with h | h
            · exact ⟨Or.inl h, hg'len⟩
            · exact ⟨Or.inr (Or.inl h), hg'len⟩
          · exact hops g (by rw [hsplit]; simp [h])
      · have hgl : gates.length = (pre ++ gates[k] :: post).length := by rw [← hsplit]
        let ι2 : Fin (t + 1) → Fin (pre ++ gates[k] :: post).length :=
          fun j => ⟨(ι j).val, by have := (ι j).isLt; omega⟩
        have hι2 : ∀ i : Fin (pre ++ gates[k] :: post).length,
            ((pre ++ gates[k] :: post).get i).op = GateOp.not → ∃ j, ι2 j = i := by
          intro i hi
          have hget : gates.get ⟨i.val, by have := i.isLt; omega⟩ =
              (pre ++ gates[k] :: post).get i := by
            simp only [List.get_eq_getElem]
            congr 1
          obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
          exact ⟨j, Fin.ext (by simp [ι2, hj])⟩
        exact fn_split_count t pre post gates[k] g' hg'op ι2 hι2 j0
          (by simp [ι2, hj0, hprelen])
  · left
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨i, hi, h1⟩ hex

open PEqualNP.CircuitLowerBounds

theorem fnb_andOr2_of_not0 (gates : List Gate) (hops : OpsOK gates)
    (hn : NotAtMost 0 gates) : AndOr2 gates := by
  intro g hg
  obtain ⟨ι, hι⟩ := hn
  refine ⟨?_, (hops g hg).2⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
  rcases (hops _ hg).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨j, _⟩ := hι i h
    exact j.elim0

theorem fnb_card_disj {n m d : ℕ} (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ)
    (hF : FamG n m d S kappa) (b : ℕ) (y : Finset (Fin n)) (hy : y.card ≤ b) :
    m - kappa b ≤ (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card := by
  have hk := hF.2.2 b y hy
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun w : Fin m => Disjoint (S w) y)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  omega

def fnb_force {n : ℕ} (y : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ y then true else if i ∈ (∅ : Finset (Fin n)) then false else x i

theorem fnb_right_force {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (K : ℕ)
    (gates : List Gate) (out : Fin m → ℕ) (hr : Right S y K gates out) (w : Fin m)
    (hw : Disjoint (S w) y) (x : Fin n → Bool)
    (hx : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ K) :
    Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x)) =
      decide (∃ v ∈ S w, x v = true) := by
  have hv : ∀ v ∈ S w, fnb_force y x v = x v := fun v hv => by
    have : v ∉ y := Finset.disjoint_left.mp hw hv
    simp [fnb_force, this]
  rw [hr w (fnb_force y x) hw (fun p hp => by simp [fnb_force, hp]) ?_]
  · simp only [decide_eq_decide]
    exact ⟨fun ⟨v, h1, h2⟩ => ⟨v, h1, by rw [← hv v h1]; exact h2⟩,
      fun ⟨v, h1, h2⟩ => ⟨v, h1, by rw [hv v h1]; exact h2⟩⟩
  · refine le_trans (Finset.card_le_card ?_) hx
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    simpa [fnb_force, h2] using h1

theorem fnb_card_single {n : ℕ} (p : Fin n) :
    (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hc
  rw [ha, hc]

theorem fnb_main : PBaseG := by
  intro h270 h669 hsub n m d S kappa hF b K y gates out hy hops hnot hright
  rw [fnp_genG_zero]
  rcases Nat.eq_zero_or_pos (min K (d - 1)) with h0 | hpos
  · rw [h0, Nat.mul_zero]
    exact Nat.zero_le _
  obtain ⟨hK, hd⟩ := Nat.lt_min.mp hpos
  obtain ⟨gates', r, hg', hlen, hcomp⟩ := h669 n gates y (fnb_andOr2_of_not0 gates hops hnot)
  obtain ⟨m', e, hm', _, hiff, hcard', hpair'⟩ :=
    hsub n m (d - 1) S y (fun i => by rw [hF.1 i]; omega) hF.2.1
  have hc : ∀ w : Fin m, Disjoint (S w) y → ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ K →
      Circuit.eval ⟨gates', r (out w)⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true) := by
    intro w hw x hx
    have hne : ∃ x x' : Fin n → Bool,
        Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x)) ≠
          Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x')) := by
      obtain ⟨p, hp⟩ : (S w).Nonempty := by
        rw [← Finset.card_pos, hF.1 w]
        omega
      refine ⟨fun _ => false, fun q => decide (q = p), ?_⟩
      rw [fnb_right_force S y K gates out hright w hw _ (by simp),
        fnb_right_force S y K gates out hright w hw _ ((fnb_card_single p).trans hK)]
      have h2 : ∃ v ∈ S w, decide (v = p) = true := ⟨p, hp, by simp⟩
      rw [decide_eq_true h2]
      simp
    have h1 := hcomp (out w) hne x
    exact h1.trans (fnb_right_force S y K gates out hright w hw x hx)
  have hdisj : ∀ i : Fin m', Disjoint (S (e i)) y := fun i => (hiff (e i)).mpr ⟨i, rfl⟩
  have key := h270 n m' K (fun i => S (e i)) ⟨gates', 0⟩ (fun i => r (out (e i)))
    (fun _ => min K (d - 1)) hpair' (fun i => by rw [hcard' i]; omega) hg'
    (fun i p => by
      change Circuit.eval ⟨gates', r (out (e i))⟩ _ = true ↔ _
      rw [hc (e i) (hdisj i) _ ((fnb_card_single p).trans hK)]
      simp)
    (fun i x hx hz => by
      change Circuit.eval ⟨gates', r (out (e i))⟩ _ = false
      rw [hc (e i) (hdisj i) x hx]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro v hv
      simp [hz v hv])
    (fun _ => min_le_left _ _) (fun i => by rw [hcard' i]; omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Circuit.size] at key
  have hm : m - kappa b ≤ m' := hm' ▸ fnb_card_disj S kappa hF b y hy
  calc (m - kappa b) * min K (d - 1) ≤ m' * min K (d - 1) := Nat.mul_le_mul_right _ hm
    _ ≤ gates'.length := key
    _ ≤ gates.length := hlen

open PEqualNP.CircuitLowerBounds

def fns_hv {n : ℕ} (pre : List Gate) (ins : List ℕ) (x : Fin n → Bool) : Bool :=
  (ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false

theorem fns_right_mono {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    {j K : ℕ} (hj : j ≤ K) (gates : List Gate) (out : Fin m → ℕ)
    (h : Right S y K gates out) : Right S y j gates out :=
  fun w x hd h1 h2 => h w x hd h1 (le_trans h2 hj)

theorem fns_right_congr {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (K : ℕ) (gates gates' : List Gate) (out : Fin m → ℕ)
    (hag : ∀ x : Fin n → Bool, Win y K x → ∀ o : ℕ,
      Circuit.eval ⟨gates', o⟩ (List.ofFn x) = Circuit.eval ⟨gates, o⟩ (List.ofFn x))
    (h : Right S y K gates out) : Right S y K gates' out := by
  intro w x hd h1 h2
  rw [hag x ⟨h1, h2⟩ (out w)]
  exact h w x hd h1 h2

theorem fns_card_true {n : ℕ} (y : Finset (Fin n)) (b j : ℕ) (hy : y.card ≤ b)
    (x : Fin n → Bool) (hx : Win y j x) :
    (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ b + j := by
  have hsub : Finset.univ.filter (fun p : Fin n => x p = true) ⊆
      y ∪ Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hpy : p ∈ y
    · exact Finset.mem_union_left _ hpy
    · exact Finset.mem_union_right _ (by simp [hp, hpy])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ b + j := Nat.add_le_add hy hx.2

theorem fns_win_above {n : ℕ} (y : Finset (Fin n)) {j K : ℕ} (hj : j ≤ K)
    (x0 : Fin n → Bool) (hx0 : Win y j x0) (x : Fin n → Bool)
    (hx : Win (Finset.univ.filter (fun p : Fin n => x0 p = true)) (K - j) x) :
    Win y K x := by
  refine ⟨fun p hp => hx.1 p (by simp [hx0.1 p hp]), ?_⟩
  have hsub : Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y) ⊆
      Finset.univ.filter (fun p : Fin n => x0 p = true ∧ p ∉ y) ∪
      Finset.univ.filter (fun p : Fin n => x p = true ∧
        p ∉ Finset.univ.filter (fun p : Fin n => x0 p = true)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h0 : x0 p = true
    · exact Finset.mem_union_left _ (by simp [h0, hp.2])
    · exact Finset.mem_union_right _ (by simp [h0, hp.1])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ j + (K - j) := Nat.add_le_add hx0.2 hx.2
    _ = K := by omega

theorem fns_right_base {n m : ℕ} (S : Fin m → Finset (Fin n)) (y y' : Finset (Fin n))
    (hyy : y ⊆ y') (K K' : ℕ) (gates : List Gate) (out : Fin m → ℕ)
    (hwin : ∀ x : Fin n → Bool, Win y' K' x → Win y K x)
    (h : Right S y K gates out) : Right S y' K' gates out := by
  intro w x hd h1 h2
  have hw := hwin x ⟨h1, h2⟩
  exact h w x (Finset.disjoint_of_subset_right hyy hd) hw.1 hw.2

theorem fns_term_split {n m d : ℕ} (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) (s : ℕ)
    (ih : ClaimG n m d S kappa s) (b K : ℕ) (y : Finset (Fin n)) (out : Fin m → ℕ)
    (hy : y.card ≤ b) (pre post : List Gate) (ins : List ℕ)
    (hpre : AndOr2 pre)
    (hopsA : OpsOK (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post))
    (hopsO : OpsOK (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post))
    (hnA : NotAtMost s (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post))
    (hnO : NotAtMost s (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post))
    (hR : Right S y K (pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post) out)
    (j : ℕ) (hj : j ≤ K) :
    min (fewNotGenG m d kappa s (b + j) (K - j)) (fewNotGenG m d kappa s b j) ≤
      (pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post).length := by
  classical
  by_cases hex : ∃ x0 : Fin n → Bool, Win y j x0 ∧ fns_hv pre ins x0 = true
  · obtain ⟨x0, hx0, hv⟩ := hex
    set y' := Finset.univ.filter (fun p : Fin n => x0 p = true) with hy'
    have hyy : y ⊆ y' := fun p hp => by simp [hy', hx0.1 p hp]
    have hRy := fns_right_base S y y' hyy K (K - j) _ out
      (fun x hx => fns_win_above y hj x0 hx0 x hx) hR
    have hRO : Right S y' (K - j)
        (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post) out := by
      refine fns_right_congr S y' (K - j) _ _ out ?_ hRy
      intro x hx o
      apply OneNot.on1_piece_u_cheap
      exact OneNot.on1_piece_h n pre ins hpre x0 x
        (fun i hi => hx.1 i (by simp [hy', hi])) hv
    have := ih (b + j) (K - j) y' _ out (fns_card_true y b j hy x0 hx0) hopsO hnO hRO
    rw [fnp_variant_length pre post _ ({ op := GateOp.or, inputs := [] } : Gate)]
    exact le_trans (min_le_left _ _) this
  · have hRA : Right S y j
        (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) out := by
      refine fns_right_congr S y j _ _ out ?_ (fns_right_mono S y hj _ out hR)
      intro x hx o
      apply OneNot.on1_piece_d
      have hf : ¬ fns_hv pre ins x = true := fun ht => hex ⟨x, hx, ht⟩
      simpa [fns_hv] using hf
    have := ih b j y _ out hy hopsA hnA hRA
    rw [fnp_variant_length pre post _ ({ op := GateOp.and, inputs := [] } : Gate)]
    exact le_trans (min_le_right _ _) this

theorem fns_main : PStepG := by
  intro hsplit n m d S kappa _hF s ih b K y gates out hy hops hnot hR
  rw [fnp_genG_succ]
  apply fn_foldr_max_le
  intro j hjr
  have hj : j ≤ K := by
    have := List.mem_range.mp hjr
    omega
  rcases hsplit gates s hops hnot with hle | ⟨pre, post, ins, heq, hpre, hopsA, hopsO, hnA, hnO⟩
  · exact le_trans (min_le_right _ _) (ih b j y gates out hy hops hle (fns_right_mono S y hj _ out hR))
  · subst heq
    exact fns_term_split S kappa s ih b K y out hy pre post ins hpre hopsA hopsO hnA hnO hR j hj

end PEqualNP.Outside.L_meta_1325.FewNot
namespace PEqualNP.Outside.L_meta_1325.DualSparse

open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
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

private lemma gate_inputs {n : ℕ} (C : Circuit)
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

private lemma value_mono {n : ℕ} (C : Circuit)
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

private lemma cut {n : ℕ} (C : Circuit)
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

end PEqualNP.Outside.L_meta_1325.DualSparse

namespace PEqualNP.Outside.L_meta_1325

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1325.FewNot

lemma kill_bound {n q : ℕ} (S : Fin n → Finset (Fin n))
    (hreg : ∀ p, (Incidence.through S p).card = q + 1)
    (hjoin : ∀ p p', p ≠ p' → ∃ i, p ∈ S i ∧ p' ∈ S i)
    (b : ℕ) (y : Finset (Fin n)) (hy : y.card ≤ b) :
    (Finset.univ.filter (fun i : Fin n => ¬ Disjoint (S i) y)).card ≤ kappaPlane q b := by
  classical
  induction y using Finset.induction_on generalizing b with
  | empty => simp [kappaPlane]
  | @insert p y hp ih =>
    have hy' := Finset.card_insert_of_notMem hp
    have hb : b ≠ 0 := by omega
    simp only [kappaPlane, if_neg hb]
    let D := y.biUnion (Incidence.through S)
    have hhit : Finset.univ.filter (fun i : Fin n => ¬ Disjoint (S i) (insert p y))
        = (insert p y).biUnion (Incidence.through S) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_disjoint_iff,
        Finset.mem_biUnion, Incidence.through]
      exact exists_congr fun x => and_comm
    rw [hhit, Finset.biUnion_insert]
    by_cases hy0 : y = ∅
    · subst y
      simp only [Finset.biUnion_empty, Finset.union_empty, hreg]
      have hb1 : 1 * q ≤ b * q := Nat.mul_le_mul_right q (by omega)
      omega
    · have hypos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hy0)
      obtain ⟨p', hp'⟩ := Finset.nonempty_iff_ne_empty.mpr hy0
      have hne : p ≠ p' := fun h => hp (h ▸ hp')
      have hone : 1 ≤ ((Incidence.through S p) ∩ D).card := by
        obtain ⟨i, hip, hip'⟩ := hjoin p p' hne
        have hm : i ∈ Incidence.through S p ∩ D := by
          refine Finset.mem_inter.mpr ⟨by simp [Incidence.through, hip], ?_⟩
          exact Finset.mem_biUnion.mpr ⟨p', hp', by simp [Incidence.through, hip']⟩
        exact Finset.card_pos.mpr ⟨i, hm⟩
      have hD : D.card ≤ y.card * q + 1 := by
        specialize ih y.card le_rfl
        have hsame : D = Finset.univ.filter (fun i : Fin n => ¬ Disjoint (S i) y) := by
          ext i
          simp [D, Incidence.through, Finset.not_disjoint_iff, and_comm]
        rw [hsame]
        simpa [kappaPlane, hypos.ne'] using ih
      have hdis := Finset.card_union_add_card_inter (Incidence.through S p) D
      have hmul : y.card * q + q ≤ b * q := by
        rw [← Nat.add_one_mul]
        exact Nat.mul_le_mul_right q (by omega)
      change ((Incidence.through S p) ∪ D).card ≤ b * q + 1
      rw [hreg] at hdis
      omega

theorem recursive_bound {q n : ℕ} (hn : n = q*q + q + 1) (hq : 2 ≤ q)
    (L : Fin n → Finset (Fin n))
    (hS : ∀ i, (L i).card = q + 1) (hcross : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hjoin : ∀ p p', p ≠ p' → ∃ i, p ∈ L i ∧ p' ∈ L i)
    (s : ℕ) (gates : List Gate) (out : Fin n → ℕ)
    (hg : OpsOK gates) (hnot : NotAtMost s gates)
    (hout : ∀ (w : Fin n) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ L w, x v = true))
    (G : ℕ → ℕ → ℕ → ℕ)
    (hzero : ∀ b K, G 0 b K = (n - (if b = 0 then 0 else min n (b*q+1))) * min K q)
    (hsucc : ∀ t b K, G (t+1) b K = (List.range (K+1)).foldr
      (fun j acc => max acc (min (G t (b+j) (K-j)) (G t b j))) 0) :
    G s 0 n ≤ gates.length := by
  have hle : ∀ i j, i ≠ j → (L i ∩ L j).card ≤ 1 := fun i j h => (hcross i j h).le
  have hreg : ∀ p, (Incidence.through L p).card = q + 1 :=
    Incidence.through_card L hn (by omega) hS hcross hjoin
  have hfam : FamG n n (q+1) L (kappaPlane q) :=
    ⟨hS, hle, kill_bound L hreg hjoin⟩
  have hbound := fnp_assemblyG fn_family_reindex fn_split_general fnb_main fns_main
    Sparse.main Restrict.main_aux n n (q+1) L (kappaPlane q) hfam s 0 n ∅ gates out
    (by simp) hg hnot (fun w x _ _ _ => hout w x)
  suffices hEq : ∀ t b K, G t b K = fewNotGenG n (q+1) (kappaPlane q) t b K by
    rw [hEq]; exact hbound
  intro t
  induction t with
  | zero =>
    intro b K
    rw [hzero, fnp_genG_zero, kappaPlane]
    by_cases hb : b = 0
    · simp [hb]
    · simp only [if_neg hb, Nat.add_sub_cancel]
      by_cases h : n ≤ b*q+1
      · rw [min_eq_left h, Nat.sub_self, Nat.sub_eq_zero_of_le h]
      · rw [min_eq_right (by omega : b*q+1 ≤ n)]
  | succ t ih =>
    intro b K
    rw [hsucc, fnp_genG_succ]
    simp only [ih]


-- The same gate-cut proof applies to complementary values, by reversing the two inputs.
private def dval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  !(DualSparse.value C (fun i => !(x i)) w)

private lemma contra_bool (a b : Bool) (h : a = true → b = true) :
    !b = true → !a = true := by
  cases a <;> cases b <;> simp_all

private lemma dval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    dval C x p = x p := by
  simp [dval, DualSparse.input_value]

private lemma dval_missing {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (h : n + C.size ≤ w) : dval C x w = true := by
  simp [dval, DualSparse.missing_value C _ _ h]

private lemma dval_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    dval C x w = true → dval C y w = true :=
  contra_bool _ _ (DualSparse.value_mono C hG (fun i => !(y i)) (fun i => !(x i))
    (fun i => contra_bool _ _ (hxy i)) w)

private lemma dcut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, dval C x w = true → dval C y w = true) →
        ∀ w ∈ F, dval C x w = true → dval C y w = true := by
  obtain ⟨B, hd, hb, hcut⟩ := DualSparse.cut C hG G hGates t F hF
  refine ⟨B, hd, hb, fun x y hxy w hw => contra_bool _ _ (hcut
    (fun i => !(y i)) (fun i => !(x i)) ?_ w hw)⟩
  intro v hv
  simpa [dval] using contra_bool _ _ (hxy v hv)


private def onSet {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ T)

private lemma weight {n : ℕ} (T : Finset (Fin n)) :
    (Finset.univ.filter (fun p => onSet T p = true)).card = T.card := by
  congr 1
  ext p
  simp [onSet]

private lemma room {n : ℕ} (T y : Finset (Fin n)) : (T \ y).card + y.card ≤ n := by
  classical
  have hd : Disjoint (T \ y) y := Finset.disjoint_left.mpr (fun _ h hy =>
    (Finset.mem_sdiff.mp h).2 hy)
  rw [← Finset.card_union_of_disjoint hd]
  simpa using Finset.card_le_card (Finset.subset_univ ((T \ y) ∪ y))

private lemma union_bound {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hsize : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (y : Finset (Fin n)) (B : Finset ℕ) (A : ℕ → Finset (Fin n))
    (hA : ∀ w ∈ B, (A w).card ≤ q ∨ ∃ i, A w = S i \ y) :
    (B.biUnion A).card ≤ B.card * q + 1 := by
  classical
  by_cases hbig : ∃ w ∈ B, ∃ i, A w = S i \ y
  · obtain ⟨w,hw,i,hi⟩ := hbig
    let R := B.erase w
    have hdiff : ∀ v ∈ R, (A v \ S i).card ≤ q := by
      intro v hv
      rcases hA v (Finset.mem_erase.mp hv).2 with hs | ⟨j,hj⟩
      · exact (Finset.card_le_card Finset.sdiff_subset).trans hs
      · rw [hj]
        by_cases h : j = i
        · simp [h]
        · have he := Finset.card_sdiff_add_card_inter (S j) (S i)
          rw [hinter j i h, hsize] at he
          have hs : (S j \ y) \ S i ⊆ S j \ S i := fun _ hp =>
            Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1,
              (Finset.mem_sdiff.mp hp).2⟩
          have hc := Finset.card_le_card hs
          omega
    have hsub : B.biUnion A ⊆ S i ∪ R.biUnion (fun v => A v \ S i) := by
      intro p hp
      obtain ⟨v,hv,hp⟩ := Finset.mem_biUnion.mp hp
      by_cases h : p ∈ S i
      · exact Finset.mem_union_left _ h
      · have hne : v ≠ w := by rintro rfl; exact h ((Finset.mem_sdiff.mp (hi ▸ hp)).1)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨v,Finset.mem_erase.mpr ⟨hne,hv⟩,Finset.mem_sdiff.mpr ⟨hp,h⟩⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (S i) (R.biUnion (fun v => A v \ S i))
    have h3 := Finset.card_biUnion_le_card_mul R (fun v => A v \ S i) q hdiff
    have he : R.card + 1 = B.card := Finset.card_erase_add_one hw
    rw [← he, Nat.add_mul, Nat.one_mul]
    rw [hsize] at h2
    omega
  · have hsmall (v) (hv : v ∈ B) : (A v).card ≤ q :=
      (hA v hv).resolve_right (fun h => hbig ⟨v,hv,h⟩)
    exact (Finset.card_biUnion_le_card_mul B A q hsmall).trans (by omega)

private def specific {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (i : Fin m) :
    Finset ℕ := (Finset.Ico n (n+C.size)).filter fun w =>
      dval C (onSet (y ∪ S i)) w = true ∧ ∀ j, j ≠ i → dval C (onSet (y ∪ S j)) w = false

private lemma private_count {q n m K : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (C : Circuit) (i : Fin m) (o c : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ T : Finset (Fin n), (T \ y).card ≤ K →
      (dval C (onSet (y ∪ T)) o = true ↔ S i \ y ⊆ T))
    (hc : c ≤ q) (hcsize : c + 1 ≤ (S i \ y).card)
    (hK : c * q < K ∨ n ≤ y.card + K) : c ≤ (specific C S y i).card := by
  classical
  by_contra! hsmall
  let G := specific C S y i
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBC, hcut⟩ := dcut C hg G hgate (n+C.size) {o} (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hf := Finset.card_filter_le G (fun w => w < n+C.size)
    simp only [Finset.card_singleton] at hBC
    change G.card < c at hsmall
    omega
  have hpositive : 1 ≤ c := by omega
  have hsK : (S i \ y).card ≤ K := by
    rcases hK with hK | hK
    · have hp := Nat.mul_le_mul_right q hpositive
      rw [Nat.one_mul] at hp
      have hs := Finset.card_le_card (Finset.sdiff_subset : S i \ y ⊆ S i)
      rw [hsize] at hs
      omega
    · have hr := room (S i) y
      omega
  have witness (w : ℕ) (hw : w ∈ B) : ∃ T : Finset (Fin n),
      (T.card ≤ q ∨ ∃ j, T = S j \ y) ∧ (T ∩ (S i \ y)).card ≤ 1 ∧
      (dval C (onSet (y ∪ S i)) w = true → dval C (onSet (y ∪ T)) w = true) := by
    by_cases hv : dval C (onSet (y ∪ S i)) w = true
    · by_cases hin : w < n
      · let p : Fin n := ⟨w,hin⟩
        refine ⟨{p},Or.inl (by simp; omega),?_,?_⟩
        · exact (Finset.card_le_card (Finset.inter_subset_left : {p} ∩ (S i \ y) ⊆ {p})).trans (by simp)
        · intro _
          change dval C (onSet (y ∪ {p})) p = true
          simp [dval_input,onSet]
      · by_cases bound : w < n+C.size
        · have hn : w ∉ specific C S y i := Finset.disjoint_left.mp hd hw
          have hex : ∃ j, j ≠ i ∧ dval C (onSet (y ∪ S j)) w = true := by
            by_contra! neg
            apply hn
            refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,bound⟩,hv,?_⟩
            intro j hj
            simpa using neg j hj
          obtain ⟨j,hji,hj⟩ := hex
          refine ⟨S j \ y, Or.inr ⟨j, rfl⟩, ?_, ?_⟩
          · have hs : (S j \ y) ∩ (S i \ y) ⊆ S j ∩ S i := fun _ hp =>
              Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
                (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1⟩
            exact (Finset.card_le_card hs).trans (hinter j i hji).le
          · intro _
            apply dval_mono C hg (onSet (y ∪ S j)) _ _ w hj
            intro p hp
            have hm : p ∈ y ∪ S j := of_decide_eq_true hp
            apply decide_eq_true
            rcases Finset.mem_union.mp hm with hy | hj'
            · exact Finset.mem_union_left _ hy
            · by_cases hy : p ∈ y
              · exact Finset.mem_union_left _ hy
              · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hj', hy⟩)
        · exact ⟨∅, Or.inl (by simp), by simp, fun _ => dval_missing C _ w (by omega)⟩
    · exact ⟨∅,Or.inl (by simp),by simp,fun ht => False.elim (hv ht)⟩
  let A (w : ℕ) : Finset (Fin n) := if h : w ∈ B then (witness w h).choose else ∅
  have ha (w : ℕ) (hw : w ∈ B) :
      ((A w).card ≤ q ∨ ∃ j, A w = S j \ y) ∧ (A w ∩ (S i \ y)).card ≤ 1 ∧
      (dval C (onSet (y ∪ S i)) w = true → dval C (onSet (y ∪ A w)) w = true) := by
    simpa [A,hw] using (witness w hw).choose_spec
  let U := B.biUnion A
  have hu : (U \ y).card ≤ K := by
    rcases hK with hK | hK
    · have h := union_bound S hsize hinter y B A (fun w hw => (ha w hw).1)
      have h' := Nat.mul_le_mul_right q hb
      have hs := Finset.card_le_card (Finset.sdiff_subset : U \ y ⊆ U)
      change U.card ≤ B.card * q + 1 at h
      omega
    · have hr := room U y
      omega
  have hot : dval C (onSet (y ∪ U)) o = true := by
    apply hcut (onSet (y ∪ S i)) (onSet (y ∪ U)) _ o (Finset.mem_singleton_self o)
      ((heval (S i) hsK).mpr Finset.sdiff_subset)
    intro w hw hp
    apply dval_mono C hg (onSet (y ∪ A w)) (onSet (y ∪ U)) _ w ((ha w hw).2.2 hp)
    intro p hp
    apply decide_eq_true
    rcases Finset.mem_union.mp (of_decide_eq_true hp : p ∈ y ∪ A w) with hy | hA
    · exact Finset.mem_union_left _ hy
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw, hA⟩)
  have hSub := (heval U hu).mp hot
  have hcover : S i \ y ⊆ B.biUnion (fun w => A w ∩ (S i \ y)) := by
    intro p hp
    obtain ⟨w,hw,hm⟩ := Finset.mem_biUnion.mp (hSub hp)
    exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_inter.mpr ⟨hm,hp⟩⟩
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le_card_mul B (fun w => A w ∩ (S i \ y)) 1 (fun w hw => (ha w hw).2.1)
  simp only [Nat.mul_one] at h2
  omega




theorem dual_cost : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (∀ v ∈ y, x v = true) → ((Finset.univ.filter (fun i : Fin n => x i = true)) \ y).card ≤ K → dval ⟨gates, 0⟩ x (out w) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → (c * q < K ∨ n ≤ y.card + K) → ∑ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card), min c ((S i \ y).card - 1) ≤ gates.length := by
  classical
  intro q n m K S y hq hsize hinter gates out hg heval c hc hK
  let C : Circuit := ⟨gates, 0⟩
  let G (i : Fin m) := specific C S y i
  let I := Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card)
  have hd : (↑I : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hi hj => ?_
    have hfalse := (Finset.mem_filter.mp hi).2.2 j (Ne.symm hij)
    have htrue := (Finset.mem_filter.mp hj).2.1
    simp [htrue] at hfalse
  have hi (i : Fin m) (hi : i ∈ I) : min (c + 1) (S i \ y).card ≤ (G i).card + 1 := by
    let d := min (c + 1) (S i \ y).card - 1
    have hpos : 1 ≤ min (c + 1) (S i \ y).card :=
      le_min (by omega) ((by simpa [I] using hi : 2 ≤ (S i \ y).card).trans' (by decide))
    have hd1 : d + 1 = min (c + 1) (S i \ y).card := by dsimp [d]; omega
    have hdc : d ≤ c := by have := min_le_left (c + 1) (S i \ y).card; omega
    have hds : d + 1 ≤ (S i \ y).card := hd1 ▸ min_le_right _ _
    have hdK : d * q < K ∨ n ≤ y.card + K :=
      hK.imp (fun h => lt_of_le_of_lt (Nat.mul_le_mul_right q hdc) h) id
    suffices h : d ≤ (G i).card by omega
    apply private_count S y hq hsize hinter C i (out i) d hg _ (hdc.trans hc) hds hdK
    intro T hT
    have hon : ∀ v ∈ y, onSet (y ∪ T) v = true := fun v hv =>
      decide_eq_true (Finset.mem_union_left _ hv)
    have heq : (Finset.univ.filter (fun v => onSet (y ∪ T) v = true)) \ y = T \ y := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, onSet,
        decide_eq_true_eq, Finset.mem_union]
      tauto
    have h := heval i (onSet (y ∪ T)) hon (heq.symm ▸ hT)
    change dval C (onSet (y ∪ T)) (out i) = _ at h
    rw [h]
    simp only [decide_eq_true_eq, onSet, Finset.mem_union, Finset.subset_iff,
      Finset.mem_sdiff]
    constructor
    · intro hh v hv
      exact (hh v hv.1).resolve_left hv.2
    · intro hh v hv
      by_cases hy : v ∈ y
      · exact Or.inl hy
      · exact Or.inr (hh ⟨hv, hy⟩)
  have hs : I.biUnion G ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hi).1
  have hcharge (i : Fin m) (h : i ∈ I) :
      min c ((S i \ y).card - 1) ≤ (G i).card := by
    have h' := hi i h
    omega
  change ∑ i ∈ I, min c ((S i \ y).card - 1) ≤ gates.length
  calc
    _ ≤ ∑ i ∈ I, (G i).card := Finset.sum_le_sum hcharge
    _ = (I.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card hs
    _ = gates.length := by simp [C, Circuit.size]


private def zeros {n : ℕ} (z : Finset (Fin n)) : Fin n → Bool := fun p => decide (p ∉ z)

private lemma zeros_antitone {n : ℕ} {z y : Finset (Fin n)} (h : z ⊆ y) :
    ∀ p, zeros y p = true → zeros z p = true := by
  intro p hp
  simp only [zeros, decide_eq_true_eq] at hp ⊢
  exact fun hz => hp (h hz)

private lemma freeze_eq (gates : List Gate) (a b : List Bool)
    (h : Trace.AgreesNot gates a b) : Trace.freeze a gates = Trace.freeze b gates := by
  induction gates generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    rw [Trace.freeze, Trace.freeze, ih _ _ h.tail]
    by_cases hg : g.op = .not
    · simp [Trace.freezeGate, hg, h.first hg]
    · simp [Trace.freezeGate, hg]

-- A decreasing chain changes its NOT trace at most 2^s - 1 times.
private lemma stable_window {n : ℕ} (gates : List Gate) (s F d : ℕ)
    (hops : OpsOK gates) (hnot : NotAtMost s gates) (hF : F + 1 = 2 ^ s) :
    ∃ (i : ℕ) (z : Finset (Fin n)), i ≤ F ∧ z.card ≤ i * d ∧
      ∀ Y : Finset (Fin n), z ⊆ Y → (i < F → (Y \ z).card ≤ d) →
        ∀ t : Fin (Trace.notIndices gates).card,
          Trace.trace gates (zeros z) (Trace.notEmbedding gates t) =
            Trace.trace gates (zeros Y) (Trace.notEmbedding gates t) := by
  classical
  by_contra hbad
  let Bad (i : ℕ) (z Y : Finset (Fin n)) : Prop :=
    z ⊆ Y ∧ (i < F → (Y \ z).card ≤ d) ∧
    ¬ ∀ t : Fin (Trace.notIndices gates).card,
      Trace.trace gates (zeros z) (Trace.notEmbedding gates t) =
        Trace.trace gates (zeros Y) (Trace.notEmbedding gates t)
  have step (i : ℕ) (z : Finset (Fin n)) (hi : i ≤ F) (hz : z.card ≤ i * d) :
      ∃ Y, Bad i z Y := by
    by_contra hh
    exact hbad ⟨i, z, hi, hz, fun Y hzy hcard => by
      by_contra ha
      exact hh ⟨Y, hzy, hcard, ha⟩⟩
  let next (i : ℕ) (z : Finset (Fin n)) : Finset (Fin n) :=
    if h : i ≤ F ∧ z.card ≤ i*d then (step i z h.1 h.2).choose else z
  have next_bad (i : ℕ) (z : Finset (Fin n)) (hi : i ≤ F) (hz : z.card ≤ i*d) :
      Bad i z (next i z) := by
    simp only [next, dif_pos (show i ≤ F ∧ z.card ≤ i*d from ⟨hi, hz⟩)]
    exact (step i z hi hz).choose_spec
  let seq : ℕ → Finset (Fin n) := Nat.rec ∅ (fun i z => next i z)
  have hsize (i : ℕ) (hi : i ≤ F) : (seq i).card ≤ i*d := by
    induction i with
    | zero => simp [seq]
    | succ i ih =>
      have hlt : i < F := by omega
      have hprev := ih (by omega)
      have hb := next_bad i (seq i) (by omega) hprev
      have hu := Finset.card_sdiff_add_card_eq_card hb.1
      have hlocal := hb.2.1 hlt
      change (next i (seq i)).card ≤ (i+1)*d
      rw [Nat.add_one_mul]
      omega
  have hseq : Monotone seq := monotone_nat_of_le_succ (fun i => by
    change seq i ⊆ next i (seq i)
    by_cases h : i ≤ F ∧ (seq i).card ≤ i*d
    · exact (next_bad i (seq i) h.1 h.2).1
    · simp [next, h])
  have hbadstep (i : ℕ) (hi : i ≤ F) : Bad i (seq i) (seq (i+1)) :=
    next_bad i (seq i) hi (hsize i hi)
  let u (a : Fin (F+2)) : Fin n → Bool := zeros (seq (F + 1 - a.val))
  have hu (a b : Fin (F+2)) (hab : a ≤ b) (w : Fin n) (hw : u a w = true) :
      u b w = true :=
    zeros_antitone (hseq (Nat.sub_le_sub_left hab _)) w hw
  obtain ⟨P, _, hcount, hagree⟩ := Trace.existsCuts
    (fun t a => Trace.trace gates (u a) (Trace.notEmbedding gates t))
    (fun t a b hab hp => Trace.trace_after gates u hu hops t a b hab hp)
  have hin : Finset.Icc 1 (F+1) ⊆ P := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    by_contra hkp
    let a : Fin (F+2) := ⟨k-1, by omega⟩
    let b : Fin (F+2) := ⟨k, by omega⟩
    have hab : a ≤ b := Nat.sub_le k 1
    have hc := hagree a b hab (by
      rintro w hw ⟨haw, hwb⟩
      change k-1 < w at haw
      change w ≤ k at hwb
      have he : w = k := by omega
      exact hkp (he ▸ hw))
    let i := F+1-k
    have hp := (hbadstep i (by dsimp [i]; omega)).2.2
    apply hp
    intro t
    have he : F + 1 - (k - 1) = i + 1 := by dsimp [i]; omega
    simpa [u, a, b, he, i] using (hc t).symm
  have hh := Finset.card_le_card hin
  have hz := Nat.pow_le_pow_right (by decide : 0 < 2) (Trace.card_notIndices gates s hnot)
  simp only [Nat.card_Icc] at hh
  omega

private lemma window_price {n q : ℕ} (S : Fin n → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (gates : List Gate) (out : Fin n → ℕ) (hops : OpsOK gates)
    (hout : ∀ (w : Fin n) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true))
    (z : Finset (Fin n)) (c K : ℕ) (hc : c ≤ q) (hK : c*q < K ∨ n ≤ z.card + K)
    (hstable : ∀ Y : Finset (Fin n), z ⊆ Y → (Y \ z).card ≤ K →
      ∀ t : Fin (Trace.notIndices gates).card,
        Trace.trace gates (zeros z) (Trace.notEmbedding gates t) =
          Trace.trace gates (zeros Y) (Trace.notEmbedding gates t)) :
    ∑ l ∈ Finset.univ.filter (fun l : Fin n => (S l ∩ z).card + 1 ≤ q),
      min c (q - (S l ∩ z).card) ≤ gates.length := by
  classical
  let gs := Trace.freeze (List.ofFn (zeros z)) gates
  have hm (w : Fin n) (x : Fin n → Bool) (hz : ∀ v ∈ z, x v = true)
      (hW : ((Finset.univ.filter (fun i : Fin n => x i = true)) \ z).card ≤ K) :
      dval ⟨gs, 0⟩ x (out w) = decide (∀ v ∈ S w, x v = true) := by
    let Y := Finset.univ.filter (fun i : Fin n => x i = true)
    have hzy : z ⊆ Y := fun p hp => by simp [Y, hz p hp]
    have he : zeros Y = fun p => !(x p) := by
      funext p
      cases h : x p <;> simp [zeros, Y, h]
    have hmono := Trace.initial_below (zeros Y) (zeros z) (zeros_antitone hzy)
    have hang := Trace.trace_agrees gates (zeros Y) (zeros z)
      (fun t => (hstable Y hzy hW t).symm)
    have hr := Trace.freeze_run gates (List.ofFn (zeros Y)) (List.ofFn (zeros z))
      (List.ofFn (zeros Y)) ⟨rfl, fun _ => id⟩ hmono hops hang
    rw [freeze_eq gates _ _ hang, he] at hr
    change (!((Trace.run gs (List.ofFn (fun p => !(x p)))).getD (out w) false)) = _
    rw [hr]
    change (!(Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun p => !(x p))))) = _
    rw [hout]
    apply Bool.eq_iff_iff.mpr
    simp
  have hot := dual_cost q n n K S z hq hsize hcross gs out (Trace.freeze_pos gates _ hops) hm c hc hK
  rw [Trace.freeze_length] at hot
  have hre (l : Fin n) : (S l \ z).card + (S l ∩ z).card = q+1 := by
    rw [Finset.card_sdiff_add_card_inter, hsize]
  have hfilter : (Finset.univ.filter (fun l => 2 ≤ (S l \ z).card)) =
      Finset.univ.filter (fun l : Fin n => (S l ∩ z).card + 1 ≤ q) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := hre l
    omega
  rw [hfilter] at hot
  refine le_trans ?_ hot
  apply Finset.sum_le_sum
  intro l hl
  have := hre l
  omega

private lemma min_form {n q : ℕ} (S : Fin n → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (gates : List Gate) (out : Fin n → ℕ) (hops : OpsOK gates)
    (s : ℕ) (hnot : NotAtMost s gates)
    (hout : ∀ (w : Fin n) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true))
    (j F T : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ q) (hF : F + 1 = 2 ^ s)
    (hT : ∀ i : ℕ, i + 1 ≤ F → ∀ z : Finset (Fin n), z.card ≤ i * (j*q+1) →
        T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin n => (S l ∩ z).card + 1 ≤ q), min j (q-(S l ∩ z).card))
    (hFull : ∀ z : Finset (Fin n), z.card ≤ F*(j*q+1) →
        T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin n => (S l ∩ z).card + 1 ≤ q), (q-(S l ∩ z).card)) :
    T ≤ gates.length := by
  obtain ⟨i, z, hi, hz, hstable⟩ := stable_window (n := n) gates s F (j*q+1) hops hnot hF
  by_cases h : i < F
  · exact (hT i (by omega) z hz).trans
      (window_price S hq hsize hcross gates out hops hout z j (j*q+1) hj
        (Or.inl (by omega)) (fun Y hsub hW => hstable Y hsub (fun _ => hW)))
  · have hze : z.card ≤ F*(j*q+1) := by rwa [show i = F by omega] at hz
    apply (hFull z hze).trans
    have hprice := window_price S hq hsize hcross gates out hops hout z q n le_rfl
      (Or.inr (by omega)) (fun Y hsub _ => hstable Y hsub (fun h' => (h h').elim))
    simpa only [min_eq_right (Nat.sub_le q _)] using hprice


end PEqualNP.Outside.L_meta_1325

open PEqualNP.Outside.L_meta_1325 in
theorem PEqualNP.Outside.L_meta_1325 : ∀ (q s : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1))), 2 ≤ q → (∀ i : Fin (q ^ 2 + q + 1), (L i).card = q + 1) → (∀ i j : Fin (q ^ 2 + q + 1), i ≠ j → (L i ∩ L j).card = 1) → (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i : Fin (q ^ 2 + q + 1), p ∈ L i ∧ p' ∈ L i) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q ^ 2 + q + 1) → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ (w : Fin (q ^ 2 + q + 1)) (x : Fin (q ^ 2 + q + 1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ L w, x v = true)) → (∀ G : ℕ → ℕ → ℕ → ℕ, (∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q) → (∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) → G s 0 (q ^ 2 + q + 1) ≤ gates.length) ∧ (∀ j F T : ℕ, 1 ≤ j → j ≤ q → F + 1 = 2 ^ s → (∀ i : ℕ, i + 1 ≤ F → ∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ i * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), min j (q - (L l ∩ z).card)) → (∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ F * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), (q - (L l ∩ z).card)) → T ≤ gates.length) := by
  intro q s L hq hS hc hj gates out hg hnot hout
  refine ⟨?_, ?_⟩
  · intro G hG hR
    apply recursive_bound (n := q^2+q+1) (q := q) (by rw [pow_two]) hq L hS hc hj s gates out hg hnot hout G
    · simpa only [pow_two] using hG
    · exact hR
  · exact min_form L hq hS hc gates out hg s hnot hout
