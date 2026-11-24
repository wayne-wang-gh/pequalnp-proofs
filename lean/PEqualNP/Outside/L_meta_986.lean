import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_986
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
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

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
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
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

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def owned {n} (C : Circuit) (z : ℕ) (P S : Finset (Fin n)) : Finset ℕ :=
  ((Finset.Ico n (n+C.size)).erase z).filter fun w => support C w ∩ P ⊆ S ∧ 2 ≤ (support C w ∩ P).card

def bit {n} (A : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ A)

theorem countOne {n} (C : Circuit) (z o : ℕ) (P S : Finset (Fin n)) (hg : good C)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hpos : ∀ p ∈ S ∩ P, value C (fun v => decide (v = p)) o = true)
    (hneg : value C (bit (P \ S)) o = false) :
    (S ∩ P).card - 1 ≤ (owned C z P S).card := by
  classical
  let G := owned C z P S
  have hgate (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size :=
    Finset.mem_Ico.mp (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
  obtain ⟨B, hd, hc, hcut⟩ := cut C hg G hgate (n+C.size) {o} (fun w _ hw => (hgate w hw).2)
  let y := bit (P \ S)
  let F := B.filter fun w => value C y w = false
  have small (w) (hw : w ∈ F) : (support C w ∩ P).card ≤ 1 := by
    have hb := (Finset.mem_filter.mp hw).1
    have hv := (Finset.mem_filter.mp hw).2
    have hs : support C w ∩ P ⊆ S := by
      intro p hp
      by_contra h
      have hpt := (mem_support C w p).mp (Finset.mem_inter.mp hp).1
      have hmono := value_mono C hg (fun q => decide (q = p)) y (by
        intro q he
        have eq : q = p := of_decide_eq_true he
        subst q
        simp [y,bit,(Finset.mem_inter.mp hp).2,h]) w hpt
      simp [hv] at hmono
    by_contra! hlarge
    have hlt := Finset.card_le_card (Finset.inter_subset_left (s₂ := P) (s₁ := support C w))
    have hne : w ≠ z := by rintro rfl; simp [hz y] at hv
    exact Finset.disjoint_left.mp hd hb (Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hne,Finset.mem_Ico.mpr (support_gate C w (by omega))⟩,hs,by omega⟩)
  have covered : S ∩ P ⊆ F.biUnion (fun w => support C w ∩ P) := by
    intro p hp
    by_contra hn
    have hbad : value C y o = true := by
      apply hcut _ y _ o (Finset.mem_singleton_self _) (hpos p hp)
      intro w hw hv
      by_contra! he
      exact hn (Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw,Bool.eq_false_iff.mpr he⟩,
        Finset.mem_inter.mpr ⟨(mem_support C w p).mpr hv,(Finset.mem_inter.mp hp).2⟩⟩)
    rw [hneg] at hbad
    contradiction
  have h1 := Finset.card_le_card covered
  have h2 := Finset.card_biUnion_le_card_mul F (fun w => support C w ∩ P) 1 small
  have h3 := Finset.card_filter_le B (fun w => value C y w = false)
  change F.card ≤ B.card at h3
  have h4 := Finset.card_filter_le G (fun w => w < n+C.size)
  simp only [Finset.card_singleton] at hc
  change _ ≤ G.card
  omega



lemma sum_card_disjoint_le {ι : Type*} [DecidableEq ι] (R : Finset ι) (A : ι → Finset ℕ)
    (c : ι → ℕ) (B : Finset ℕ)
    (hd : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → Disjoint (A i) (A j))
    (hsub : ∀ i ∈ R, A i ⊆ B)
    (hc : ∀ i ∈ R, c i ≤ (A i).card) :
    ∑ i ∈ R, c i ≤ B.card := by
  have hpd : (R : Set ι).PairwiseDisjoint A := fun i hi j hj hij => hd i hi j hj hij
  calc
    ∑ i ∈ R, c i ≤ ∑ i ∈ R, (A i).card := Finset.sum_le_sum hc
    _ = (R.biUnion A).card := (Finset.card_biUnion hpd).symm
    _ ≤ B.card := Finset.card_le_card fun w hw => by
      obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp hw
      exact hsub i hi hwi

lemma one_add_sum_le_of_wires {m : ℕ} (n L w0 : ℕ) (A : Fin m → Finset ℕ) (c : Fin m → ℕ)
    (hw0 : n ≤ w0 ∧ w0 < n + L)
    (hd : ∀ i j : Fin m, i ≠ j → Disjoint (A i) (A j))
    (hsub : ∀ (i : Fin m), ∀ w ∈ A i, n ≤ w ∧ w < n + L ∧ w ≠ w0)
    (hc : ∀ i : Fin m, c i ≤ (A i).card) :
    1 + ∑ i : Fin m, c i ≤ L := by
  have h := sum_card_disjoint_le Finset.univ A c ((Finset.Ico n (n + L)).erase w0)
    (fun i _ j _ hij => hd i j hij)
    (fun i _ w hw => by
      have := hsub i w hw
      exact Finset.mem_erase.mpr ⟨this.2.2, Finset.mem_Ico.mpr ⟨this.1, this.2.1⟩⟩)
    (fun i _ => hc i)
  have hmem : w0 ∈ Finset.Ico n (n + L) := Finset.mem_Ico.mpr hw0
  rw [Finset.card_erase_of_mem hmem] at h
  simp only [Nat.card_Ico] at h
  omega

lemma one_add_sum_le_of_fin {m L : ℕ} (i0 : Fin L) (A : Fin m → Finset (Fin L)) (c : Fin m → ℕ)
    (hd : ∀ i j : Fin m, i ≠ j → Disjoint (A i) (A j))
    (hi0 : ∀ i : Fin m, i0 ∉ A i)
    (hc : ∀ i : Fin m, c i ≤ (A i).card) :
    1 + ∑ i : Fin m, c i ≤ L := by
  have hpd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint A :=
    fun i _ j _ hij => hd i j hij
  have h : ∑ i : Fin m, c i ≤ ((Finset.univ : Finset (Fin L)).erase i0).card := calc
    ∑ i : Fin m, c i ≤ ∑ i : Fin m, (A i).card := Finset.sum_le_sum fun i _ => hc i
    _ = (Finset.univ.biUnion A).card := (Finset.card_biUnion hpd).symm
    _ ≤ ((Finset.univ : Finset (Fin L)).erase i0).card := Finset.card_le_card fun w hw => by
      obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
      exact Finset.mem_erase.mpr ⟨fun e => hi0 i (e ▸ hwi), Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have := i0.isLt
  omega

lemma sum_card_inter_eq {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin n)) :
    ∑ s : Fin m, (S s ∩ U).card
      = ∑ u ∈ U, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  have h1 : ∀ s : Fin m, (S s ∩ U).card = ∑ u ∈ U, if u ∈ S s then 1 else 0 := by
    intro s
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  have h2 : ∀ u : Fin n, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card
      = ∑ s : Fin m, if u ∈ S s then 1 else 0 := by
    intro u
    rw [Finset.card_filter]
  simp only [h1, h2]
  exact Finset.sum_comm

lemma sum_pred_le_sdiff {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin n)) :
    ∑ s : Fin m, ((S s).card - 1)
      ≤ ∑ s : Fin m, ((S s \ U).card - 1)
        + ∑ u ∈ U, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  rw [← sum_card_inter_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have h := Finset.card_sdiff_add_card_inter (S s) U
  omega

lemma final_of_wires {n m : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n)) (t0 : Fin n)
    (L w0 : ℕ) (A : Fin m → Finset ℕ)
    (hw0 : n ≤ w0 ∧ w0 < n + L)
    (hd : ∀ i j : Fin m, i ≠ j → Disjoint (A i) (A j))
    (hsub : ∀ (i : Fin m), ∀ w ∈ A i, n ≤ w ∧ w < n + L ∧ w ≠ w0)
    (hc : ∀ i : Fin m, (S i \ T.erase t0).card - 1 ≤ (A i).card) :
    1 + ∑ s : Fin m, ((S s).card - 1)
      ≤ L + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  have h1 := one_add_sum_le_of_wires n L w0 A (fun i => (S i \ T.erase t0).card - 1) hw0 hd hsub hc
  have h2 := sum_pred_le_sdiff S (T.erase t0)
  omega

lemma final_of_fin {n m L : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n)) (t0 : Fin n)
    (i0 : Fin L) (A : Fin m → Finset (Fin L))
    (hd : ∀ i j : Fin m, i ≠ j → Disjoint (A i) (A j))
    (hi0 : ∀ i : Fin m, i0 ∉ A i)
    (hc : ∀ i : Fin m, (S i \ T.erase t0).card - 1 ≤ (A i).card) :
    1 + ∑ s : Fin m, ((S s).card - 1)
      ≤ L + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  have h1 := one_add_sum_le_of_fin i0 A (fun i => (S i \ T.erase t0).card - 1) hd hi0 hc
  have h2 := sum_pred_le_sdiff S (T.erase t0)
  omega

lemma sdiff_erase_of_notMem {n : ℕ} (X T : Finset (Fin n)) (t0 : Fin n) (h : t0 ∉ X) :
    X \ T.erase t0 = X \ T := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨ha, hn⟩
    exact ⟨ha, fun hT => hn ⟨fun e => h (e ▸ ha), hT⟩⟩
  · rintro ⟨ha, hn⟩
    exact ⟨ha, fun hT => hn hT.2⟩

def keep {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) : Finset (Fin n) :=
  if t0 ∈ S then Finset.univ \ (T.erase t0) else Finset.univ \ T

lemma inter_keep {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) :
    S ∩ keep S T t0 = S \ T.erase t0 := by
  unfold keep
  split_ifs with h
  · ext a
    simp
  · rw [sdiff_erase_of_notMem S T t0 h]
    ext a
    simp

theorem finishSum {n m N z : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n)) (t0 : Fin n) (G : Fin m → Finset ℕ) (hz : z ∈ Finset.Ico n (n+N)) (hG : ∀ i, G i ⊆ (Finset.Ico n (n+N)).erase z) (hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G) (h : ∀ i, (S i ∩ keep (S i) T t0).card - 1 ≤ (G i).card) : 1 + ∑ i, ((S i).card-1) ≤ N + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun i : Fin m => u ∈ S i)).card := by
  refine final_of_wires S T t0 N z G (Finset.mem_Ico.mp hz)
    (fun i j hij => hd (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij)
    (fun i w hw => ?_) (fun i => ?_)
  · have h1 := Finset.mem_erase.mp (hG i hw)
    have h2 := Finset.mem_Ico.mp h1.2
    exact ⟨h2.1, h2.2, h1.1⟩
  · rw [← inter_keep]
    exact h i


lemma repl_eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ r ∈ g.inputs, f r = true → f' r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx r hr => h r hr (hx r hr)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact fun ⟨r, hr, hx⟩ => ⟨r, hr, h r hr hx⟩

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

def replC (gates : List Gate) (i0 : ℕ) : Circuit :=
  ⟨gates.set i0 ⟨GateOp.and, []⟩, 0⟩

lemma replC_size (gates : List Gate) (i0 : ℕ) : (replC gates i0).size = gates.length := by
  simp [replC, Circuit.size]

lemma replC_gates (gates : List Gate) (i0 : Fin gates.length)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0) :
    ∀ g ∈ (replC gates i0.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [replC] using hk
  by_cases hki : i0.val = k
  · simp [replC, hki]
  · have e : (replC gates i0.val).gates[k] = gates[k] := by
      simp [replC, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hgate gates[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

lemma replC_true {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (x : Fin n → Bool) :
    value (replC gates i0.val) x (n + i0.val) = true := by
  have h := gate_value (replC gates i0.val) x (n + i0.val) (by omega)
    (by rw [replC_size]; omega)
  simp only at h
  rw [h]
  simp [replC, GateOp.eval]

lemma replC_other {n : ℕ} (gates : List Gate) (i0 : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + i0) :
    value (replC gates i0) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (replC gates i0) x r else false) := by
  have h := gate_value (replC gates i0) x w hn (by rw [replC_size]; exact hw)
  simp only at h
  rw [h]
  have e : (replC gates i0).gates[w - n]'(by simp [replC]; omega) = gates[w - n]'(by omega) := by
    simp only [replC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma orig_value {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma replC_ge {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (x : Fin n → Bool) (w : ℕ) :
    value ⟨gates, o⟩ x w = true → value (replC gates i0.val) x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact id
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · intro _
        rw [hne]
        exact replC_true gates i0 x
      · rw [orig_value gates o x w (by omega) hw, replC_other gates i0.val x w (by omega) hw hne]
        have hop : (gates[w - n]'(by omega)).op = GateOp.and ∨
            (gates[w - n]'(by omega)).op = GateOp.or := by
          rcases (hgate (gates[w - n]'(by omega)) (List.getElem_mem _)).1 with hop | hop | hop
          · exact Or.inl hop
          · exact Or.inr hop
          · have := congrArg Fin.val (hnot ⟨w - n, by omega⟩ hop)
            simp only at this
            omega
        apply repl_eval_mono _ hop
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · intro h
      rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega)] at h
      exact absurd h (by simp)

lemma replC_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (h0 : value ⟨gates, o⟩ x (n + i0.val) = true) (w : ℕ) :
    value (replC gates i0.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · rw [hne, h0]
        exact replC_true gates i0 x
      · rw [orig_value gates o x w (by omega) hw, replC_other gates i0.val x w (by omega) hw hne]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (replC gates i0.val) x w (by rw [replC_size]; omega)]

lemma orig_not_true {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o hw : ℕ)
    (hop : (gates.get i0).op = GateOp.not) (hhead : (gates.get i0).inputs.head? = some hw)
    (hlt : hw < n + i0.val) (x : Fin n → Bool)
    (hx : Circuit.eval ⟨gates, hw⟩ (List.ofFn x) = false) :
    value ⟨gates, o⟩ x (n + i0.val) = true := by
  rw [orig_value gates o x (n + i0.val) (by omega) (by omega)]
  have e : gates[n + i0.val - n]'(by omega) = gates.get i0 := by
    simp
  rw [e, hop]
  obtain ⟨rest, hin⟩ : ∃ rest, (gates.get i0).inputs = hw :: rest := by
    cases h : (gates.get i0).inputs with
    | nil => rw [h] at hhead; simp at hhead
    | cons a rest => rw [h] at hhead; exact ⟨rest, by simpa using hhead⟩
  rw [hin]
  have hv : value ⟨gates, o⟩ x hw = false := hx
  simp [GateOp.eval, hlt, hv]

theorem replacement {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
    (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (hop : (gates.get i0).op = GateOp.not)
    (hhead : (gates.get i0).inputs.head? = some hw)
    (hlt : hw < n + i0.val)
    (hout : ∀ (o : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true))
    (hT : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) →
      Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) :
    ∃ C : Circuit, C.size = gates.length ∧
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, value C x (n + i0.val) = true) ∧
      (∀ i x, (∀ u ∈ T.erase t0, x u = false) → (t0 ∈ S i ∨ x t0 = false) →
        value C x (out i) = decide (∃ v ∈ S i, x v = true)) := by
  refine ⟨replC gates i0.val, replC_size gates i0.val, replC_gates gates i0 hgate hnot,
    replC_true gates i0, ?_⟩
  intro i x hx hcase
  have hval : value ⟨gates, out i⟩ x (out i) = decide (∃ v ∈ S i, x v = true) := hout i x
  by_cases h0 : x t0 = false
  · have hz : ∀ t ∈ T, x t = false := by
      intro t ht
      by_cases htt : t = t0
      · rw [htt]; exact h0
      · exact hx t (Finset.mem_erase.mpr ⟨htt, ht⟩)
    rw [replC_eq gates i0 (out i) x
      (orig_not_true gates i0 (out i) hw hop hhead hlt x (hT x hz)) (out i), hval]
  · have ht0 : t0 ∈ S i := hcase.resolve_right h0
    have htrue : decide (∃ v ∈ S i, x v = true) = true :=
      decide_eq_true ⟨t0, ht0, by simpa using h0⟩
    rw [htrue]
    exact replC_ge gates i0 (out i) hgate hnot x (out i) (hval.trans htrue)


end PEqualNP.Outside.L_meta_986
open PEqualNP.Outside.L_meta_986 in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  intro n m S gates out i0 hw T t0 _ hl hG hu hop hh hlt he hc ht _
  classical
  obtain ⟨C,hlen,hgood,hz,hok⟩ := replacement S gates out i0 hw T t0 hG hu hop hh hlt he hc
  let z := n+i0.val
  let P := fun i => keep (S i) T t0
  let G := fun i => owned C z (P i) (S i)
  have allG (i) : G i ⊆ (Finset.Ico n (n+C.size)).erase z := Finset.filter_subset _ _
  have smallP (i) : (Finset.univ \ T) ⊆ P i := by
    intro p hp
    have hnt := (Finset.mem_sdiff.mp hp).2
    simp [P,keep]
    split <;> simp_all
  have comp (i j) : P i ⊆ P j ∨ P j ⊆ P i := by
    by_cases hi : t0 ∈ S i
    · by_cases hj : t0 ∈ S j
      · exact Or.inl (by simp [P,keep,hi,hj])
      · exact Or.inr (by simpa [P,keep,hj] using smallP i)
    · exact Or.inl (by simpa [P,keep,hi] using smallP j)
  have noCommon (i j) (hij : i ≠ j) (hp : P i ⊆ P j) (w) (hi : w ∈ G i) (hj : w ∈ G j) : False := by
    have ai := (Finset.mem_filter.mp hi).2
    have aj := (Finset.mem_filter.mp hj).2
    have inc : support C w ∩ P i ⊆ S i ∩ S j := by
      intro p hp'
      exact Finset.mem_inter.mpr ⟨ai.1 hp',aj.1 (Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hp').1, hp (Finset.mem_inter.mp hp').2⟩)⟩
    exact (by omega : ¬ 2 ≤ 1) (ai.2.trans ((Finset.card_le_card inc).trans (hl i j hij)))
  have dis : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    rcases comp i j with h|h
    · exact noCommon i j hij h w hi hj
    · exact noCommon j i hij.symm h w hj hi
  have hmask (i : Fin m) (x : Fin n → Bool) (h : ∀ v, x v = true → v ∈ P i) :
      value C x (out i) = decide (∃ v ∈ S i, x v = true) := by
    apply hok i x
    · intro u hdel
      apply Bool.eq_false_iff.mpr
      intro hv
      have hin := h u hv
      by_cases hi : t0 ∈ S i
      · have hf : u ∈ (Finset.univ : Finset (Fin n)) \ T.erase t0 := by
          simpa only [P,keep,if_pos hi] using hin
        exact (Finset.mem_sdiff.mp hf).2 hdel
      · have hf : u ∈ (Finset.univ : Finset (Fin n)) \ T := by
          simpa only [P,keep,if_neg hi] using hin
        exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_erase.mp hdel).2
    · by_cases hi : t0 ∈ S i
      · exact Or.inl hi
      · refine Or.inr (Bool.eq_false_iff.mpr ?_)
        intro hv
        have hin := h t0 hv
        have hf : t0 ∈ (Finset.univ : Finset (Fin n)) \ T := by
          simpa only [P,keep,if_neg hi] using hin
        exact (Finset.mem_sdiff.mp hf).2 ht
  rw [← hlen]
  apply finishSum S T t0 G (by have := i0.isLt; simp [z]; omega) allG dis
  intro i
  apply countOne C z (out i) (P i) (S i) hgood hz
  · intro p hp
    rw [hmask i _ (fun v hv => (of_decide_eq_true hv : v = p) ▸ (Finset.mem_inter.mp hp).2)]
    exact decide_eq_true ⟨p,(Finset.mem_inter.mp hp).1,by simp⟩
  · have supp (v : Fin n) (hv : bit (P i \ S i) v = true) : v ∈ P i :=
      (Finset.mem_sdiff.mp (show v ∈ P i \ S i from of_decide_eq_true hv)).1
    rw [hmask i (bit (P i \ S i)) supp]
    apply decide_eq_false
    rintro ⟨p,hp,hb⟩
    exact (Finset.mem_sdiff.mp (show p ∈ P i \ S i from of_decide_eq_true hb)).2 hp
