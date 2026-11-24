import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

-- The wire and reverse-cut helpers come from the checked L-meta-1460 proof, following L-meta-925 and L-meta-270.


open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1591

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

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
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

private def input {n : ℕ} (A : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ A)

private def probes {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  S.filter fun p => value C (input (R p)) w = true

private lemma mem_probes {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ probes C S R w ↔ p ∈ S ∧ value C (input (R p)) w = true := by
  simp [probes]

private def outside {n : ℕ} (S : Finset (Fin n)) (p : Fin n) : Bool :=
  decide (p ∉ S)

private def charged {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, w = n + j.val ∧
    (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
    value C (outside S) w = false ∧ 2 ≤ (probes C S R w).card ∧
    ∀ r ∈ (C.gates.get j).inputs, (probes C S R r).Nonempty

-- A gate rejecting the outside assignment can be replaced by earlier rejecting wires.
-- Only a binary OR with two productive reads can enlarge this frontier.
private lemma expand {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n))
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hR : ∀ p ∈ S, R p ∩ S = {p}) (w : ℕ)
    (hF : value C (outside S) w = false) (hLarge : 1 < (probes C S R w).card) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (1 < P.card → charged C S R w) ∧
      (∀ r ∈ P, r < w ∧ value C (outside S) r = false) ∧
      probes C S R w ⊆ P.biUnion (probes C S R) := by
  classical
  have hw₀ : n ≤ w := by
    by_contra! hn
    let p : Fin n := ⟨w, hn⟩
    have hp : p ∈ S := by
      change value C (outside S) p = false at hF
      simpa [input_value, outside] using hF
    have hsmall : probes C S R w ⊆ {p} := by
      intro s hs
      obtain ⟨hsS, hv⟩ := (mem_probes C S R w s).1 hs
      change value C (input (R s)) p = true at hv
      have hr : p ∈ R s := by simpa [input_value, input] using hv
      have he : p ∈ ({s} : Finset (Fin n)) := hR s hsS ▸ Finset.mem_inter.mpr ⟨hr, hp⟩
      simp [Finset.mem_singleton.mp he]
    have hb := Finset.card_le_card hsmall
    simp at hb
    omega
  have hw₁ : w < n + C.size := by
    by_contra! hn
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (probes C S R w).card)
    have hv := (mem_probes C S R w p).1 hp
    rw [missing_value C _ w hn] at hv
    simp_all
  let g := C.gates[w - n]'(by unfold Circuit.size at hw₁; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let read (x : Fin n → Bool) (r : ℕ) := if r < w then value C x r else false
  have hgate (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x w hw₀ hw₁
  have hAnd (h : g.op = GateOp.and) (x : Fin n → Bool) :
      value C x w = true ↔ ∀ r ∈ g.inputs, read x r = true := by
    rw [hgate, h, GateOp.eval, List.all_eq_true]
    simp
  have hOr (h : g.op = GateOp.or) (x : Fin n → Bool) :
      value C x w = true ↔ ∃ r ∈ g.inputs, read x r = true := by
    rw [hgate, h, GateOp.eval, List.any_eq_true]
    simp
  rcases hop with h | h
  · have hbad : ¬ ∀ r ∈ g.inputs, read (outside S) r = true := by
      rw [← hAnd h, hF]; decide
    push Not at hbad
    obtain ⟨r, hr, hrF⟩ := hbad
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (probes C S R w).card)
    have hread := (hAnd h _).1 ((mem_probes C S R w p).1 hp).2 r hr
    have hrlt : r < w := (by simpa [read] using hread : r < w ∧ value C (input (R p)) r = true).1
    refine ⟨{r}, by simp, by simp, ?_, ?_⟩
    · intro s hs
      have he : s = r := Finset.mem_singleton.mp hs
      subst s
      exact ⟨hrlt, by simpa [read, hrlt] using hrF⟩
    · intro p hp
      obtain ⟨hps, hpv⟩ := (mem_probes C S R w p).1 hp
      exact Finset.mem_biUnion.mpr ⟨r, by simp, (mem_probes C S R r p).2
        ⟨hps, by simpa [read, hrlt] using (hAnd h _).1 hpv r hr⟩⟩
  · let P := g.inputs.toFinset.filter fun r => r < w ∧ (probes C S R r).Nonempty
    have hcard : P.card ≤ g.inputs.toFinset.card := Finset.card_filter_le _ _
    have hcard' := List.toFinset_card_le g.inputs
    refine ⟨P, by omega, ?_, ?_, ?_⟩
    · intro hlarge
      have hj : w - n < C.gates.length := by unfold Circuit.size at hw₁; omega
      have hlen' : g.inputs.length = 2 := by omega
      have hP : P = g.inputs.toFinset :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      refine ⟨⟨w - n, hj⟩, by simp; omega, h, hlen', hF, hLarge, ?_⟩
      intro r hr
      change r ∈ g.inputs at hr
      exact (Finset.mem_filter.mp (by rw [hP]; exact List.mem_toFinset.mpr hr : r ∈ P)).2.2
    · intro r hr
      obtain ⟨hri, hrlt, _⟩ := Finset.mem_filter.mp hr
      refine ⟨hrlt, ?_⟩
      have hn : read (outside S) r ≠ true := by
        intro ht
        have := (hOr h _).2 ⟨r, List.mem_toFinset.mp hri, ht⟩
        rw [hF] at this
        simp_all
      simpa [read, hrlt] using hn
    · intro p hp
      obtain ⟨hps, hpv⟩ := (mem_probes C S R w p).1 hp
      obtain ⟨r, hr, hrv⟩ := (hOr h _).1 hpv
      have hrlt : r < w := (by simpa [read] using hrv : r < w ∧ value C (input (R p)) r = true).1
      have hpr := (mem_probes C S R r p).2 ⟨hps, by simpa [read, hrlt] using hrv⟩
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr hr, hrlt, p, hpr⟩, hpr⟩


private lemma card_prefix (G : Finset ℕ) (t : ℕ) :
    (G.filter (· < t + 1)).card = (G.filter (· < t)).card + if t ∈ G then 1 else 0 := by
  classical
  by_cases ht : t ∈ G
  · have h : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw, hlt⟩
        by_cases he : w = t
        · exact Or.inl he
        · exact Or.inr ⟨hw, by omega⟩
      · rintro (rfl | ⟨hw, hlt⟩)
        · exact ⟨ht, by omega⟩
        · exact ⟨hw, by omega⟩
    rw [h, Finset.card_insert_of_notMem (by simp), ite_eq_left ht]
  · have h : G.filter (· < t + 1) = G.filter (· < t) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, hlt⟩
        have hne : w ≠ t := fun e => ht (e ▸ hw)
        exact ⟨hw, by omega⟩
      · rintro ⟨hw, hlt⟩
        exact ⟨hw, by omega⟩
    rw [h, ite_eq_right ht, Nat.add_zero]

-- Count each expanding wire at most once by processing the frontier in reverse order.
private lemma cut_card {α : Type*} [DecidableEq α]
    (P : ℕ → Finset α) (ok : ℕ → Prop) (G : Finset ℕ)
    (expandWire : ∀ w, ok w → 1 < (P w).card →
      ∃ B : Finset ℕ, B.card ≤ 2 ∧ (1 < B.card → w ∈ G) ∧
        (∀ r ∈ B, r < w ∧ ok r) ∧ P w ⊆ B.biUnion P)
    (t : ℕ) (F : Finset ℕ)
    (hF : ∀ w ∈ F, ok w ∧ (1 < (P w).card → w < t)) :
    (F.biUnion P).card ≤ F.card + (G.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    apply (Finset.card_biUnion_le_card_mul F P 1 ?_).trans
    · simp
    · intro r hr
      have h := (hF r hr).2
      omega
  | succ t ih =>
    by_cases ht : t ∈ F ∧ 1 < (P t).card
    · obtain ⟨B, hBcard, hcharge, hB, hcover⟩ := expandWire t (hF t ht.1).1 ht.2
      let F' := F.erase t ∪ B
      have hF' : ∀ w ∈ F', ok w ∧ (1 < (P w).card → w < t) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
          have ⟨hok, hlt⟩ := hF w hmem
          exact ⟨hok, fun h => by have := hlt h; omega⟩
        · exact ⟨(hB w hw).2, fun _ => (hB w hw).1⟩
      have hU : F.biUnion P ⊆ F'.biUnion P := by
        intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        by_cases h : w = t
        · subst w
          obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp (hcover hpw)
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hpw⟩
      have hsize := Finset.card_union_le (F.erase t) B
      change F'.card ≤ _ at hsize
      have he := Finset.card_erase_add_one ht.1
      have hh := (Finset.card_le_card hU).trans (ih F' hF')
      rw [card_prefix]
      by_cases hg : t ∈ G
      · simp only [ite_eq_left hg]
        omega
      · simp only [ite_eq_right hg]
        have : B.card ≤ 1 := by by_contra! hl; exact hg (hcharge hl)
        omega
    · have hFt : ∀ w ∈ F, ok w ∧ (1 < (P w).card → w < t) := by
        intro w hw
        refine ⟨(hF w hw).1, fun h => ?_⟩
        have hne : w ≠ t := fun e => ht ⟨e ▸ hw, e ▸ h⟩
        have := (hF w hw).2 h
        omega
      have hh := ih F hFt
      rw [card_prefix]
      omega

private noncomputable def charges {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) : Finset ℕ :=
  open Classical in
  (Finset.Ico n (n + C.size)).filter (charged C S R)

private lemma mem_charges {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) :
    w ∈ charges C S R ↔ charged C S R w := by
  classical
  rw [charges, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨j, rfl, _⟩ := h
  have hj := j.isLt
  unfold Circuit.size
  omega

private lemma charge_card {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hR : ∀ p ∈ S, R p ∩ S = {p})
    (hFalse : value C (outside S) w = false)
    (hTrue : ∀ p ∈ S, value C (input (R p)) w = true) :
    S.card ≤ 1 + (charges C S R).card := by
  classical
  let G := charges C S R
  have hstep (r : ℕ) (hf : value C (outside S) r = false) (hcard : 1 < (probes C S R r).card) :
      ∃ B : Finset ℕ, B.card ≤ 2 ∧ (1 < B.card → r ∈ G) ∧
        (∀ s ∈ B, s < r ∧ value C (outside S) s = false) ∧
        probes C S R r ⊆ B.biUnion (probes C S R) := by
    obtain ⟨B, hB, hcharge, hread, hcover⟩ := expand C S R hG hR r hf hcard
    exact ⟨B, hB, fun h => (mem_charges C S R r).2 (hcharge h), hread, hcover⟩
  have hh := cut_card (probes C S R) (fun r => value C (outside S) r = false) G
    hstep (w + 1) {w} (by
      intro r hr
      have he : r = w := Finset.mem_singleton.mp hr
      subst r
      exact ⟨hFalse, fun _ => by omega⟩)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hh
  have hFull : probes C S R w = S := by
    ext p
    simp only [mem_probes]
    exact ⟨And.left, fun hp => ⟨hp, hTrue p hp⟩⟩
  rw [hFull] at hh
  have hbound := Finset.card_filter_le G (· < w + 1)
  change S.card ≤ 1 + G.card
  omega

private lemma cross_hit {n : ℕ} (C : Circuit)
    (S T : Finset (Fin n)) (R : Fin n → Finset (Fin n)) (w : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hSize : (S ∩ T).card ≤ 1)
    (hCard : 2 ≤ (probes C S R w).card)
    (hFalse : value C (outside T) w = false) :
    ∃ p ∈ S \ T, (R p ∩ T).Nonempty := by
  classical
  have hex : ∃ p ∈ probes C S R w, p ∉ T := by
    by_contra! h
    have hsub : probes C S R w ⊆ S ∩ T := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨((mem_probes C S R w p).1 hp).1, h p hp⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨p, hp, hpt⟩ := hex
  obtain ⟨hps, hpw⟩ := (mem_probes C S R w p).1 hp
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hps, hpt⟩, ?_⟩
  by_contra hn
  have hxy (v : Fin n) (hv : input (R p) v = true) : outside T v = true := by
    simp only [input, decide_eq_true_eq] at hv
    simp only [outside, decide_eq_true_eq]
    exact fun ht => hn ⟨v, Finset.mem_inter.mpr ⟨hv, ht⟩⟩
  have := value_mono C hG _ _ hxy w hpw
  rw [hFalse] at this
  contradiction

-- A cyclic permutation of a finite set, adapted from the checked L-meta-1541 direction-cycle construction.
private theorem cycle_fin (N : ℕ) (hN : 3 ≤ N) :
    ∃ e : Equiv.Perm (Fin N), ∀ a, e a ≠ a ∧ e (e a) ≠ a := by
  have : NeZero N := ⟨by omega⟩
  let e : Equiv.Perm (Fin N) := Equiv.addRight (1 : Fin N)
  have h₁ : (1 : Fin N) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < N)] at hv
  have h₂ : (1 : Fin N) + 1 ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < N),
      Nat.mod_eq_of_lt (by omega : 1 + 1 < N)] at hv
  refine ⟨e, fun a => ⟨?_, ?_⟩⟩
  · intro h
    apply h₁
    apply add_left_cancel (a := a)
    simpa [e] using h
  · intro h
    apply h₂
    apply add_left_cancel (a := a)
    simpa [e, add_assoc] using h

private theorem cycle_finset {α : Type} (s : Finset α) (hs : 3 ≤ s.card) :
    ∃ e : Equiv.Perm {x // x ∈ s}, ∀ a, e a ≠ a ∧ e (e a) ≠ a := by
  classical
  obtain ⟨e, he⟩ := cycle_fin s.card hs
  let f : {x // x ∈ s} ≃ Fin s.card := s.equivFin
  let e' : Equiv.Perm {x // x ∈ s} := (f.trans e).trans f.symm
  refine ⟨e', fun a => ⟨?_, ?_⟩⟩
  · intro h
    apply (he (f a)).1
    simpa [e'] using congrArg f h
  · intro h
    apply (he (f a)).2
    simpa [e'] using congrArg f h

private theorem rotor_bases {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N)
    (T : Finset (Fin N)) (hT : T ⊆ L i0)
    (hMeet : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (f : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N))
    (closed : ∀ x ∈ T, f x ∈ T)
    (cycle : ∀ x ∈ T, f x ≠ x ∧ f (f x) ≠ x) (hx0 : x0 ∈ T)
    (baseT : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T, x ∈ L s →
      B s p = if p = x then ∅ else {f x})
    (baseW : ∀ s : Fin N, s ≠ i0 → ∀ e ∈ L i0 \ T, e ∈ L s → ∀ p ∈ L s, B s p = {x0}) :
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧
      ∃ v ∈ T, v = p ∨ v ∈ B s p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' →
      ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧
        (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  classical
  have into (x : Fin N) (hx : x ∈ T) : x ∈ L i0 := hT hx
  have only_one (s : Fin N) (hs : s ≠ i0) {a b : Fin N}
      (ha : a ∈ L s) (ha0 : a ∈ L i0) (hb : b ∈ L s) (hb0 : b ∈ L i0) : a = b :=
    Finset.card_le_one.mp (hMeet s i0 hs).le a (Finset.mem_inter.mpr ⟨ha,ha0⟩)
      b (Finset.mem_inter.mpr ⟨hb,hb0⟩)
  have bases (s : Fin N) (hs : s ≠ i0) (p : Fin N) (hp : p ∈ L s) :
      B s p ⊆ T ∧ B s p ∩ L s = ∅ ∧ ∃ v ∈ T, v = p ∨ v ∈ B s p := by
    obtain ⟨e,he⟩ := Finset.card_pos.mp (by rw [hMeet s i0 hs]; decide)
    obtain ⟨hes,he0⟩ := Finset.mem_inter.mp he
    by_cases het : e ∈ T
    · rw [baseT s hs p hp e het hes]
      by_cases hep : p = e
      · subst p
        simp [het]
      · rw [ite_eq_right hep]
        have hnot : f e ∉ L s := fun h =>
          (cycle e het).1 (only_one s hs h (into _ (closed e het)) hes he0)
        exact ⟨by simp [closed e het],by simp [hnot],⟨f e,closed e het,Or.inr (by simp)⟩⟩
    · have hnot : x0 ∉ L s := by
        intro hx
        have heq := only_one s hs hx (into _ hx0) hes he0
        exact het (heq ▸ hx0)
      rw [baseW s hs e (Finset.mem_sdiff.mpr ⟨he0,het⟩) hes p hp]
      exact ⟨by simp [hx0],by simp [hnot],⟨x0,hx0,Or.inr (by simp)⟩⟩
  refine ⟨fun s hs p hp => (bases s hs p hp).2,?_⟩
  intro s s' hs hs' _ h
  obtain ⟨⟨p,hp,r,hr⟩,⟨p',hp',r',hr'⟩⟩ := h
  obtain ⟨hp,_⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hp',_⟩ := Finset.mem_sdiff.mp hp'
  obtain ⟨hrB,hrs'⟩ := Finset.mem_inter.mp hr
  obtain ⟨hr'B,hr's⟩ := Finset.mem_inter.mp hr'
  have hrT := (bases s hs p hp).1 hrB
  have hr'T := (bases s' hs' p' hp').1 hr'B
  rw [baseT s hs p hp r' hr'T hr's] at hrB
  rw [baseT s' hs' p' hp' r hrT hrs'] at hr'B
  have e : r = f r' := by
    split at hrB
    · simp at hrB
    · exact Finset.mem_singleton.mp hrB
  have e' : r' = f r := by
    split at hr'B
    · simp at hr'B
    · exact Finset.mem_singleton.mp hr'B
  exact (cycle r' hr'T).2 ((congrArg f e.symm).trans e'.symm)



private def onePoint {n : ℕ} (p : Fin n) : Fin n → Bool := fun v => decide (v = p)

private noncomputable def singletons {n : ℕ} (C : Circuit) (r : ℕ) : Finset (Fin n) :=
  open Classical in Finset.univ.filter (fun p => value C (onePoint p) r = true)

private lemma mem_singletons {n : ℕ} (C : Circuit) (r : ℕ) (p : Fin n) :
    p ∈ singletons (n := n) C r ↔ value C (onePoint p) r = true := by
  classical
  simp [singletons]


private lemma wide_is_gate {n : ℕ} (C : Circuit) (w : ℕ)
    (hwide : 1 < (singletons (n := n) C w).card) : n ≤ w ∧ w < n+C.gates.length := by
  classical
  constructor
  · by_contra! h
    let p : Fin n := ⟨w,h⟩
    have hs : singletons C w ⊆ ({p} : Finset (Fin n)) := by
      intro u hu
      have hv : value C (onePoint u) p = true := (mem_singletons C w u).mp hu
      rw [input_value] at hv
      have he : p = u := of_decide_eq_true hv
      exact Finset.mem_singleton.mpr he.symm
    have := Finset.card_le_card hs
    rw [Finset.card_singleton] at this
    omega
  · by_contra! h
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (singletons (n := n) C w).card)
    have hv := (mem_singletons C w p).mp hp
    rw [missing_value C (onePoint p) w (by simpa only [Circuit.size] using h)] at hv
    cases hv



private lemma wire_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : Fin C.gates.length)
    (hop : (C.gates.get j).op = .and) :
    value C x (n + j.val) = true ↔
      ∀ r ∈ (C.gates.get j).inputs, r < n + j.val ∧ value C x r = true := by
  rw [gate_value C x _ (by omega) (by simp [Circuit.size, j.isLt])]
  simp [← List.get_eq_getElem, hop, GateOp.eval, List.all_eq_true]

private lemma wire_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : Fin C.gates.length)
    (hop : (C.gates.get j).op = .or) :
    value C x (n + j.val) = true ↔
      ∃ r ∈ (C.gates.get j).inputs, r < n + j.val ∧ value C x r = true := by
  rw [gate_value C x _ (by omega) (by simp [Circuit.size, j.isLt])]
  simp [← List.get_eq_getElem, hop, GateOp.eval, List.any_eq_true]

private lemma false_and_read {n : ℕ} (C : Circuit) (y x : Fin n → Bool) (j : Fin C.gates.length)
    (hop : (C.gates.get j).op = .and)
    (hf : value C y (n+j.val) = false) (ht : value C x (n+j.val) = true) :
    ∃ r ∈ (C.gates.get j).inputs, r < n+j.val ∧ value C y r = false := by
  have hn : ¬ ∀ r ∈ (C.gates.get j).inputs, r < n+j.val ∧ value C y r = true := by
    intro hall
    have h := (wire_and C y j hop).mpr hall
    rw [hf] at h
    contradiction
  push Not at hn
  obtain ⟨r, hr, h⟩ := hn
  have he := ((wire_and C x j hop).mp ht r hr).1
  exact ⟨r,hr,he,Bool.eq_false_iff.mpr (h he)⟩

private def rimInput {n : ℕ} (M : Finset (Fin n)) (p v : Fin n) : Bool :=
  decide (v ∉ M ∨ v = p)

private noncomputable def rimAND {n : ℕ} (C : Circuit) (M T : Finset (Fin n)) : Finset ℕ :=
  open Classical in
  (Finset.Ico n (n + C.gates.length)).filter (fun w =>
    (∃ j : Fin C.gates.length, w = n+j.val ∧ (C.gates.get j).op = .and) ∧
    value C (outside M) w = false ∧ ∃ p ∈ M \ T, value C (rimInput M p) w = true)

private noncomputable def wideOR {n : ℕ} (C : Circuit) (M : Finset (Fin n)) : Finset ℕ :=
  open Classical in
  (Finset.Ico n (n + C.gates.length)).filter (fun w =>
    (∃ j : Fin C.gates.length, w = n+j.val ∧ (C.gates.get j).op = .or ∧
      ∀ r ∈ (C.gates.get j).inputs, ∃ p : Fin n, value C (onePoint p) r = true) ∧
    value C (outside M) w = false ∧ 1 < (singletons (n := n) C w).card)

private lemma rim_children {n : ℕ} (C : Circuit) (M T : Finset (Fin n)) :
    ∃ ch : ℕ → ℕ, ∀ w ∈ rimAND C M T,
      ch w < w ∧ value C (outside M) (ch w) = false ∧
      ∀ x : Fin n → Bool, value C x w = true → value C x (ch w) = true := by
  classical
  have hex (w : ℕ) (hw : w ∈ rimAND C M T) :
      ∃ r, r < w ∧ value C (outside M) r = false ∧
        ∀ x : Fin n → Bool, value C x w = true → value C x r = true := by
    obtain ⟨_,⟨j,rfl,hop⟩,hf,p,_,ht⟩ := Finset.mem_filter.mp hw
    obtain ⟨r,hr,he,hfr⟩ := false_and_read C (outside M) (rimInput M p) j hop hf ht
    exact ⟨r,he,hfr,fun x hx => ((wire_and C x j hop).mp hx r hr).2⟩
  let ch (w : ℕ) := if hw : w ∈ rimAND C M T then (hex w hw).choose else 0
  refine ⟨ch,fun w hw => ?_⟩
  simpa only [ch, dite_eq_left hw] using (hex w hw).choose_spec

private lemma rim_trace {n : ℕ} (C : Circuit) (M T : Finset (Fin n))
    (hG : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (ch : ℕ → ℕ) (hch : ∀ w ∈ rimAND C M T,
      ch w < w ∧ value C (outside M) (ch w) = false ∧
      ∀ x : Fin n → Bool, value C x w = true → value C x (ch w) = true)
    (p : Fin n) (hp : p ∈ M \ T) (w : ℕ)
    (hf : value C (outside M) w = false) (ht : value C (rimInput M p) w = true) :
    value C (onePoint p) w = true ∨
      ∃ a ∈ rimAND C M T, value C (onePoint p) (ch a) = true := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let v : Fin n := ⟨w,hn⟩
      change value C (outside M) v = false at hf
      change value C (rimInput M p) v = true at ht
      rw [input_value] at hf ht
      have hv : v ∈ M := by simpa [outside] using hf
      have he : v = p := by simpa [rimInput,hv] using ht
      left
      change value C (onePoint p) v = true
      simp [input_value, onePoint, he]
    by_cases hw : w < n+C.gates.length
    · let j : Fin C.gates.length := ⟨w-n,by omega⟩
      have hEq : w = n+j.val := by dsimp [j]; omega
      have hmem : C.gates.get j ∈ C.gates := List.get_mem _ _
      rcases (hG _ hmem).1 with hand | hor
      · have ha : w ∈ rimAND C M T := Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega,hw⟩,⟨j,hEq,hand⟩,hf,p,hp,ht⟩
        obtain ⟨he,hfr,htr⟩ := hch w ha
        rcases ih (ch w) he hfr (htr _ ht) with hh | hh
        · exact Or.inr ⟨w,ha,hh⟩
        · exact Or.inr hh
      · have ht' : value C (rimInput M p) (n+j.val) = true := hEq ▸ ht
        obtain ⟨r,hr,he,htr⟩ := (wire_or C _ j hor).mp ht'
        have hfr : value C (outside M) r = false := by
          apply Bool.eq_false_iff.mpr
          intro hh
          have htw := (wire_or C (outside M) j hor).mpr ⟨r,hr,he,hh⟩
          rw [← hEq, hf] at htw
          contradiction
        rcases ih r (hEq.symm ▸ he) hfr htr with hh | hh
        · exact Or.inl (hEq.symm ▸ (wire_or C _ j hor).mpr ⟨r,hr,he,hh⟩)
        · exact Or.inr hh
    · rw [missing_value C (rimInput M p) w (by simpa only [Circuit.size] using (Nat.le_of_not_gt hw))] at ht
      contradiction

private lemma expand_singletons {n : ℕ} (C : Circuit) (M : Finset (Fin n))
    (hG : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hf : value C (outside M) w = false) (hwide : 1 < (singletons (n := n) C w).card) :
    ∃ B : Finset ℕ, B.card ≤ 2 ∧ (1 < B.card → w ∈ wideOR C M) ∧
      (∀ r ∈ B, r < w ∧ value C (outside M) r = false) ∧
      singletons (n := n) C w ⊆ B.biUnion (singletons (n := n) C) := by
  classical
  obtain ⟨hn,hw⟩ := wide_is_gate C w hwide
  let j : Fin C.gates.length := ⟨w-n,by omega⟩
  have hEq : w = n+j.val := by dsimp [j]; omega
  have hmem : C.gates.get j ∈ C.gates := List.get_mem _ _
  obtain ⟨hop,hlen⟩ := hG _ hmem
  rcases hop with hand | hor
  · obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (singletons (n := n) C w).card)
    have hp' := (mem_singletons C w p).mp hp
    obtain ⟨r,hr,he,hfr⟩ := false_and_read C (outside M) (onePoint p) j hand (hEq ▸ hf) (hEq ▸ hp')
    refine ⟨{r},by simp,by simp,?_,?_⟩
    · intro s hs
      obtain rfl := Finset.mem_singleton.mp hs
      exact ⟨hEq.symm ▸ he,hfr⟩
    · intro u hu
      have hu' := (mem_singletons C w u).mp hu
      exact Finset.mem_biUnion.mpr ⟨r,by simp,
        (mem_singletons C r u).mpr (((wire_and C (onePoint u) j hand).mp (hEq ▸ hu') r hr).2)⟩
  · let B := (C.gates.get j).inputs.toFinset.filter
      (fun r => r < n+j.val ∧ 0 < (singletons (n := n) C r).card)
    refine ⟨B,(Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen),?_,?_,?_⟩

    · intro hB
      have hSub : B ⊆ (C.gates.get j).inputs.toFinset := Finset.filter_subset _ _
      have hCard : (C.gates.get j).inputs.toFinset.card ≤ B.card := by
        have := List.toFinset_card_le (C.gates.get j).inputs
        omega
      have hEqB := Finset.eq_of_subset_of_card_le hSub hCard
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn,hw⟩,⟨j,hEq,hor,?_⟩,hf,hwide⟩
      intro r hr
      have hrB : r ∈ B := hEqB.symm ▸ List.mem_toFinset.mpr hr
      obtain ⟨_,_,hs⟩ := Finset.mem_filter.mp hrB
      obtain ⟨p,hp⟩ := Finset.card_pos.mp hs
      exact ⟨p,(mem_singletons C r p).mp hp⟩
    · intro r hr
      obtain ⟨hr,he,_⟩ := Finset.mem_filter.mp hr
      refine ⟨hEq.symm ▸ he,Bool.eq_false_iff.mpr ?_⟩
      intro ht
      have htw := (wire_or C (outside M) j hor).mpr ⟨r,List.mem_toFinset.mp hr,he,ht⟩
      rw [← hEq,hf] at htw
      contradiction
    · intro p hp
      have hp' := (mem_singletons C w p).mp hp
      obtain ⟨r,hr,he,ht⟩ := (wire_or C (onePoint p) j hor).mp (hEq ▸ hp')
      exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,he,
        Finset.card_pos.mpr ⟨p,(mem_singletons C r p).mpr ht⟩⟩,
        (mem_singletons C r p).mpr ht⟩

private lemma core_card {n : ℕ} (C : Circuit) (M T : Finset (Fin n)) (out : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hf : value C (outside M) out = false)
    (hCore : ∀ p ∈ T, value C (onePoint p) out = true)
    (hRim : ∀ p ∈ M \ T, value C (rimInput M p) out = true) :
    M.card ≤ 1 + (rimAND C M T).card + (wideOR C M).card := by
  classical
  obtain ⟨ch,hch⟩ := rim_children C M T
  let A := rimAND C M T
  let F := insert out (A.image ch)
  have hF : ∀ w ∈ F, value C (outside M) w = false := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · exact h.symm ▸ hf
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (hch a ha).2.1
  have hCover : M ⊆ F.biUnion (singletons (n := n) C) := by
    intro p hp
    by_cases hpt : p ∈ T
    · exact Finset.mem_biUnion.mpr ⟨out,Finset.mem_insert_self _ _,(mem_singletons C out p).mpr (hCore p hpt)⟩
    · have hr := Finset.mem_sdiff.mpr ⟨hp,hpt⟩
      rcases rim_trace C M T hG ch hch p hr out hf (hRim p hr) with ht | ⟨a,ha,ht⟩
      · exact Finset.mem_biUnion.mpr ⟨out,Finset.mem_insert_self _ _,(mem_singletons C out p).mpr ht⟩
      · exact Finset.mem_biUnion.mpr ⟨ch a,Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha),
          (mem_singletons C (ch a) p).mpr ht⟩
  have hCut := cut_card (singletons (n := n) C) (fun w => value C (outside M) w = false)
    (wideOR C M) (expand_singletons C M hG) (n+C.gates.length) F
    (fun w hw => ⟨hF w hw,fun hh => (wide_is_gate C w hh).2⟩)
  have hFcard : F.card ≤ A.card + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le _)
  have hM := Finset.card_le_card hCover
  have hX := Finset.card_filter_le (wideOR C M) (· < n+C.gates.length)
  change F.card ≤ (rimAND C M T).card + 1 at hFcard
  omega


-- Gate reservation count adapted from upstream L-meta-1461.
theorem paid_card {n : ℕ} (gates : List Gate) (j h : Fin gates.length) (earlier : h < j)
    (paid : Finset (Fin gates.length)) (hj : j ∉ paid) (hh : h ∉ paid)
    (noReader : ∀ i ∈ paid, j < i → n+j.val ∉ (gates.get i).inputs) :
    paid.card + (Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ n+j.val ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  classical
  let rs := Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n+j.val∈(gates.get i).inputs)
  have dis : Disjoint paid rs := Finset.disjoint_left.mpr fun i hi hr =>
    noReader i hi (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hr).2.2
  have outJ : j ∉ paid∪rs := by
    simp [rs,hj]
  have outH : h ∉ insert j (paid∪rs) := by
    simp [rs,hh,earlier.ne,not_lt_of_gt earlier]
  have cap := Finset.card_le_univ (insert h (insert j (paid∪rs)))
  rw [Finset.card_insert_of_notMem outH,Finset.card_insert_of_notMem outJ,
    Finset.card_union_of_disjoint dis,Fintype.card_fin] at cap
  change paid.card+rs.card+2 ≤ gates.length
  omega

-- The evaluation replacement argument adapts L-meta-1457.

def patchC (gates : List Gate) (j : ℕ) : Circuit :=
  ⟨gates.set j ⟨GateOp.or, []⟩, 0⟩

lemma patchC_size (gates : List Gate) (j : ℕ) : (patchC gates j).size = gates.length := by
  simp [patchC, Circuit.size]

lemma patchC_good (gates : List Gate) (j : Fin gates.length)
    (valid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j) :
    ∀ g ∈ (patchC gates j.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [patchC] using hk
  by_cases hkj : j.val = k
  · simp [patchC, hkj]
  · have same : (patchC gates j.val).gates[k] = gates[k] := by simp [patchC, hkj]
    rw [same]
    obtain ⟨hop, hfan⟩ := valid gates[k] (List.getElem_mem _)
    refine ⟨?_, hfan⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (unique ⟨k, hk'⟩ hop)).symm hkj

lemma patchC_false {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool) :
    value (patchC gates j.val) x (n + j.val) = false := by
  have h := gate_value (patchC gates j.val) x (n + j.val) (by omega)
    (by rw [patchC_size]; omega)
  simp only at h
  rw [h]
  simp [patchC, GateOp.eval]

lemma patchC_other {n : ℕ} (gates : List Gate) (j : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + j) :
    value (patchC gates j) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (patchC gates j) x r else false) := by
  have h := gate_value (patchC gates j) x w hn (by rw [patchC_size]; exact hw)
  simp only at h
  rw [h]
  have same : (patchC gates j).gates[w - n]'(by simp [patchC]; omega) =
      gates[w - n]'(by omega) := by
    simp only [patchC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [same]

lemma originalGateValue {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma patchEvalCongr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

lemma patchC_eq {n : ℕ} (gates : List Gate) (j : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (hjFalse : value ⟨gates, o⟩ x (n + j.val) = false) (w : ℕ) :
    value (patchC gates j.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h₁ := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h₂ := input_value (patchC gates j.val) x ⟨w, hn⟩
      simp only at h₁ h₂
      rw [h₁, h₂]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + j.val
      · rw [hne, hjFalse]
        exact patchC_false gates j x
      · rw [originalGateValue gates o x w (by omega) hw,
          patchC_other gates j.val x w (by omega) hw hne]
        apply patchEvalCongr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (patchC gates j.val) x w (by rw [patchC_size]; omega)]

lemma not_false_of_input_true {n : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (o : ℕ) (x : Fin n → Bool)
    (hop : (gates.get j).op = GateOp.not) (hlt : h < j)
    (hread : ∃ r : List ℕ, (gates.get j).inputs = (n + h.val) :: r)
    (hhTrue : value ⟨gates, o⟩ x (n + h.val) = true) :
    value ⟨gates, o⟩ x (n + j.val) = false := by
  obtain ⟨r, hr⟩ := hread
  have hj : n + j.val < n + gates.length := by omega
  have hw : n + h.val < n + j.val := by exact Nat.add_lt_add_left hlt n
  have he := originalGateValue gates o x (n + j.val) (by omega) hj
  simp only [Nat.add_sub_cancel_left] at he
  rw [he]
  change (gates.get j).op.eval ((gates.get j).inputs.map fun w =>
    if w < n + j.val then value ⟨gates, o⟩ x w else false) = false
  rw [hop, hr]
  simp [hw, hhTrue, GateOp.eval]


private lemma patchC_eq_below {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n+j.val) :
    value (patchC gates j.val) x w = value ⟨gates,0⟩ x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let v : Fin n := ⟨w,hn⟩
      change value (patchC gates j.val) x v = value ⟨gates,0⟩ x v
      rw [input_value,input_value]
    have hj := j.isLt
    have hw' : w < n+gates.length := by omega
    rw [patchC_other gates j.val x w (by omega) hw' (by omega),
      originalGateValue gates 0 x w (by omega) hw']
    apply patchEvalCongr
    intro r _
    by_cases hr : r < w
    · simpa [hr] using ih r hr (by omega)
    · simp [hr]


end PEqualNP.Outside.L_meta_1591

open PEqualNP.Outside.L_meta_1591 in
theorem PEqualNP.Outside.L_meta_1591 :
  ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = 3 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = true →
    (∀ a ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = a))) = true) →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ N + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  classical
  intro q N L i0 T hq _ hSize hMeet _ hT hTcard gates o j h hGood hJ hUnique hEarlier hRead hOrig hOutside hCoreH
  let C := patchC gates j.val
  have hG := patchC_good gates j hGood hUnique
  have hLen : C.gates.length = gates.length := by simp [C,patchC]
  let M := L i0
  have cm : 3 ≤ T.card := by omega
  have hBefore : N+h.val < N+j.val := by have : h.val < j.val := hEarlier; omega
  have hDomHigh (x : Fin N → Bool)
      (hx : (∃ v ∈ T, x v = true) ∨ ∀ v : Fin N, v ∉ M → x v = true) :
      value C x (N+h.val) = true := by
    rcases hx with ⟨p,hp,hpx⟩ | hx
    · have ht := hCoreH p hp
      change value ⟨gates,0⟩ (onePoint p) (N+h.val) = true at ht
      have hf := patchC_eq_below gates j (onePoint p) (N+h.val) hBefore
      have hLe (v : Fin N) (hv : onePoint p v = true) : x v = true := by
        have he : v = p := of_decide_eq_true hv
        exact he.symm ▸ hpx
      exact value_mono C hG _ _ hLe _ (hf.trans ht)
    · have ht := hOutside
      change value ⟨gates,0⟩ (outside M) (N+h.val) = true at ht
      have hf := patchC_eq_below gates j (outside M) (N+h.val) hBefore
      have hLe (v : Fin N) (hv : outside M v = true) : x v = true := hx v (of_decide_eq_true hv)
      exact value_mono C hG _ _ hLe _ (hf.trans ht)
  have hEval (t : Fin N) (x : Fin N → Bool)
      (hx : (∃ v ∈ T, x v = true) ∨ ∀ v : Fin N, v ∉ M → x v = true) :
      value C x (o t) = decide (∃ v ∈ L t, x v = true) := by
    have hHx : value ⟨gates,0⟩ x (N+h.val) = true :=
      (patchC_eq_below gates j x _ hBefore).symm.trans (hDomHigh x hx)
    have hFalse := not_false_of_input_true gates j h 0 x hJ hEarlier hRead hHx
    exact (patchC_eq gates j 0 x hFalse (o t)).trans (hOrig t x)

  obtain ⟨x0,hx0⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  obtain ⟨e,he⟩ := cycle_finset T cm
  let f (x : Fin N) := if hx : x ∈ T then (e ⟨x,hx⟩).val else x
  have fval (x : Fin N) (hx : x ∈ T) : f x = (e ⟨x,hx⟩).val := by simp [f,hx]
  have fclosed (x : Fin N) (hx : x ∈ T) : f x ∈ T := by
    rw [fval x hx]
    exact (e ⟨x,hx⟩).property
  have fcycle (x : Fin N) (hx : x ∈ T) : f x ≠ x ∧ f (f x) ≠ x := by
    have hsub : (⟨f x,fclosed x hx⟩ : {a // a ∈ T}) = e ⟨x,hx⟩ := Subtype.ext (fval x hx)
    constructor
    · intro h
      exact (he ⟨x,hx⟩).1 (Subtype.ext ((fval x hx).symm.trans h))
    · intro h
      apply (he ⟨x,hx⟩).2
      apply Subtype.ext
      rw [← hsub, ← fval (f x) (fclosed x hx), h]
  have existsPoint (i : Fin N) : ∃ v, v ∈ L i ∧ v ∈ M := by
    by_cases hi : i = i0
    · exact ⟨x0,hi.symm ▸ hT hx0,hT hx0⟩
    · obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [hMeet i i0 hi]; decide)
      exact ⟨v,Finset.mem_inter.mp hv⟩
  choose point pointLine pointM using existsPoint
  have point_unique (i : Fin N) (hi : i ≠ i0) (v : Fin N) (hv : v ∈ L i) (hvM : v ∈ M) :
      point i = v :=
    Finset.card_le_one.mp (hMeet i i0 hi).le (point i) (Finset.mem_inter.mpr ⟨pointLine i,pointM i⟩)
      v (Finset.mem_inter.mpr ⟨hv,hvM⟩)
  let B (i : Fin N) (p : Fin N) := if point i ∈ T then
    if p = point i then (∅ : Finset (Fin N)) else {f (point i)}
    else {x0}
  have baseT (i : Fin N) (hi : i ≠ i0) (p : Fin N) (_ : p ∈ L i)
      (x : Fin N) (hx : x ∈ T) (hxi : x ∈ L i) :
      B i p = if p = x then ∅ else {f x} := by
    simp [B,point_unique i hi x hxi (hT hx),hx]
  have baseW (i : Fin N) (hi : i ≠ i0) (x : Fin N) (hx : x ∈ M \ T) (hxi : x ∈ L i)
      (p : Fin N) (_ : p ∈ L i) : B i p = {x0} := by
    obtain ⟨hxM,hxT⟩ := Finset.mem_sdiff.mp hx
    simp [B,point_unique i hi x hxi hxM,hxT]
  obtain ⟨hBase,hConflict⟩ := rotor_bases L i0 T hT hMeet f x0 B fclosed fcycle hx0 baseT baseW
  let R (i : Fin N) (p : Fin N) := insert p (B i p)
  have hR (i : Fin N) (hi : i ≠ i0) (p : Fin N) (hp : p ∈ L i) : R i p ∩ L i = {p} := by
    ext v
    constructor
    · intro hv
      obtain ⟨hv,hi'⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp
      · have h := Finset.mem_inter.mpr ⟨hv,hi'⟩
        rw [(hBase i hi p hp).1] at h
        exact (Finset.notMem_empty _ h).elim
    · intro hv
      obtain rfl := Finset.mem_singleton.mp hv
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,hp⟩
  have offDom (i : Fin N) : (∃ v ∈ T, outside (L i) v = true) ∨
        ∀ v, v ∉ M → outside (L i) v = true := by
    by_cases hi : i = i0
    · exact Or.inr (fun v hv => by simpa [outside,hi] using hv)
    · left
      by_contra! hn
      have hsub : T ⊆ L i ∩ M := by
        intro v hv
        exact Finset.mem_inter.mpr ⟨by simpa [outside] using hn v hv,hT hv⟩
      have hcard := Finset.card_le_card hsub
      change T.card ≤ (L i ∩ L i0).card at hcard
      rw [hMeet i i0 hi] at hcard
      omega
  have hFalse (i : Fin N) : value C (outside (L i)) (o i) = false := by
    have h := hEval i (outside (L i)) (offDom i)
    change value C (outside (L i)) (o i) = _ at h
    simpa [outside] using h
  have hTrue (i : Fin N) (hi : i ≠ i0) (p : Fin N) (hp : p ∈ L i) :
      value C (input (R i p)) (o i) = true := by
    obtain ⟨v,hv,hvp⟩ := (hBase i hi p hp).2
    have hDom : (∃ v ∈ T, input (R i p) v = true) ∨
        ∀ v, v ∉ M → input (R i p) v = true :=
      Or.inl ⟨v,hv,by simpa [input,R] using hvp⟩
    have h := hEval i (input (R i p)) hDom
    change value C (input (R i p)) (o i) = _ at h
    have hx : ∃ v ∈ L i, input (R i p) v = true := ⟨p,hp,by simp [input,R]⟩
    simpa [hx] using h
  have hCore (p : Fin N) (hp : p ∈ T) : value C (onePoint p) (o i0) = true := by
    have h := hEval i0 (onePoint p) (Or.inl ⟨p,hp,by simp [onePoint]⟩)
    change value C (onePoint p) (o i0) = _ at h
    have hx : ∃ v ∈ M, onePoint p v = true := ⟨p,hT hp,by simp [onePoint]⟩
    simpa [M] using (h.trans (show decide (∃ v ∈ M, onePoint p v = true) = true by simp [hx]))
  have hRim (p : Fin N) (hp : p ∈ M \ T) : value C (rimInput M p) (o i0) = true := by
    have h := hEval i0 (rimInput M p) (Or.inr (fun v hv => by simp [rimInput, show v ∉ M from hv]))
    change value C (rimInput M p) (o i0) = _ at h
    have hx : ∃ v ∈ M, rimInput M p v = true :=
      ⟨p,(Finset.mem_sdiff.mp hp).1,by simp [rimInput]⟩
    exact h.trans (show decide (∃ v ∈ M, rimInput M p v = true) = true by simp [hx])
  let others : Finset (Fin N) := Finset.univ.erase i0
  let G (i : Fin N) := charges C (L i) (R i)
  let U := others.biUnion G
  let A := rimAND C M T
  let X := wideOR C M
  have hcard (i : Fin N) (hi : i ≠ i0) : q ≤ (G i).card := by
    have h := charge_card C (L i) (R i) (o i) hG (hR i hi) (hFalse i) (hTrue i hi)
    change (L i).card ≤ 1 + (G i).card at h
    rw [hSize i] at h
    omega
  have hDis : (↑others : Set (Fin N)).PairwiseDisjoint G := by
    intro i hi j hj hij
    have hi0 := (Finset.mem_erase.mp (show i ∈ others from hi)).1
    have hj0 := (Finset.mem_erase.mp (show j ∈ others from hj)).1
    change Disjoint (G i) (G j)
    rw [Finset.disjoint_left]
    intro w hiw hjw
    obtain ⟨_,_,_,_,hfi,hci,_⟩ := (mem_charges C (L i) (R i) w).1 hiw
    obtain ⟨_,_,_,_,hfj,hcj,_⟩ := (mem_charges C (L j) (R j) w).1 hjw
    have strip {i j : Fin N} {p : Fin N} (hp : p ∈ L i \ L j)
        (h : (R i p ∩ L j).Nonempty) : (B i p ∩ L j).Nonempty := by
      obtain ⟨v,hv⟩ := h
      obtain ⟨hvr,hvj⟩ := Finset.mem_inter.mp hv
      refine ⟨v,Finset.mem_inter.mpr ⟨?_,hvj⟩⟩
      rcases Finset.mem_insert.mp hvr with rfl | h
      · exact ((Finset.mem_sdiff.mp hp).2 hvj).elim
      · exact h
    obtain ⟨p,hp,hp'⟩ := cross_hit C (L i) (L j) (R i) w hG (hMeet i j hij).le hci hfj
    obtain ⟨s,hs,hs'⟩ := cross_hit C (L j) (L i) (R j) w hG (hMeet j i hij.symm).le hcj hfi
    exact hConflict i j hi0 hj0 hij ⟨⟨p,hp,strip hp hp'⟩,⟨s,hs,strip hs hs'⟩⟩
  have hUcard : q * (N-1) ≤ U.card := by
    calc
      q * (N-1) = ∑ i ∈ others, q := by simp [others,Nat.mul_comm]
      _ ≤ ∑ i ∈ others, (G i).card := Finset.sum_le_sum (fun i hi => hcard i (Finset.mem_erase.mp hi).1)
      _ = U.card := (Finset.card_biUnion hDis).symm
  have hCoreCard : q ≤ A.card + X.card := by
    have h := core_card C M T (o i0) hG (hFalse i0) hCore hRim
    change (L i0).card ≤ 1 + A.card + X.card at h
    rw [hSize i0] at h
    omega
  have liveOr (w : ℕ) (hw : w ∈ U) :
      ∃ i ∈ others, (∃ j : Fin C.gates.length, w = N+j.val ∧ (C.gates.get j).op = .or) ∧
        value C (outside (L i)) w = false := by
    obtain ⟨i,hi,hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨j,hw,hop,_,hf,_,_⟩ := (mem_charges C (L i) (R i) w).mp hw
    exact ⟨i,hi,⟨j,hw,hop⟩,hf⟩
  have noBoth {w : ℕ}
      (ha : ∃ j : Fin C.gates.length, w = N+j.val ∧ (C.gates.get j).op = .and)
      (ho : ∃ j : Fin C.gates.length, w = N+j.val ∧ (C.gates.get j).op = .or) : False := by
    obtain ⟨j,hj,hja⟩ := ha
    obtain ⟨k,hk,hko⟩ := ho
    have he : j = k := Fin.ext (by omega)
    subst k
    rw [hja] at hko
    contradiction
  have hUA : Disjoint U A := Finset.disjoint_left.mpr (fun w hu ha => by
    obtain ⟨_,_,ho,_⟩ := liveOr w hu
    exact noBoth (Finset.mem_filter.mp ha).2.1 ho)
  have hAX : Disjoint A X := Finset.disjoint_left.mpr (fun _ ha hx =>
    by
      obtain ⟨_,⟨a,he,hop,_⟩,_⟩ := Finset.mem_filter.mp hx
      exact noBoth (Finset.mem_filter.mp ha).2.1 ⟨a,he,hop⟩)
  have hUX : Disjoint U X := Finset.disjoint_left.mpr (fun w hu hx => by
    obtain ⟨i,hi,_,hfi⟩ := liveOr w hu
    obtain ⟨_,_,hfM,hwide⟩ := Finset.mem_filter.mp hx
    have hsub : singletons (n := N) C w ⊆ L i ∩ M := by
      intro p hp
      have ht := (mem_singletons C w p).mp hp
      have restrict (S : Finset (Fin N)) (hf : value C (outside S) w = false) : p ∈ S := by
        by_contra h
        have hle (v : Fin N) (hv : onePoint p v = true) : outside S v = true := by
          have he : v = p := of_decide_eq_true hv
          simp [he,outside,h]
        have h' := value_mono C hG _ _ hle w ht
        rw [hf] at h'
        contradiction
      exact Finset.mem_inter.mpr ⟨restrict _ hfi,restrict _ hfM⟩
    have hh := Finset.card_le_card hsub
    change (singletons (n := N) C w).card ≤ (L i ∩ L i0).card at hh
    rw [hMeet i i0 (Finset.mem_erase.mp hi).1] at hh
    omega)

  let UAX := U ∪ (A ∪ X)
  have hUAXcard : N*q ≤ UAX.card := by
    have hc : UAX.card = U.card + (A.card + X.card) := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hUA,hUX⟩),
        Finset.card_union_of_disjoint hAX]
    rw [hc]
    have hN : N-1+1 = N := by have := i0.isLt; omega
    have hSplit : N*q = q*(N-1)+q := by
      calc
        N*q = (N-1+1)*q := by rw [hN]
        _ = q*(N-1)+q := by rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (N-1)]
    omega
  -- Every charge is false at a co-line and every input of its gate has a true probe.
  have chargeInfo (w : ℕ) (hw : w ∈ UAX) :
      ∃ a : Fin C.gates.length, w = N+a.val ∧
        (∃ x : Fin N → Bool, value C x w = true) ∧
        (∃ i : Fin N, value C (outside (L i)) w = false) ∧
        ∀ r ∈ (C.gates.get a).inputs, ∃ x : Fin N → Bool, value C x r = true := by
    rcases Finset.mem_union.mp hw with hu | hax
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨a,ha,_,_,hf,hcard,hread⟩ := (mem_charges C (L i) (R i) w).mp hi
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (probes C (L i) (R i) w).card)
      refine ⟨a,ha,⟨input (R i p),((mem_probes C (L i) (R i) w p).mp hp).2⟩,⟨i,hf⟩,?_⟩
      intro r hr
      obtain ⟨v,hv⟩ := hread r hr
      exact ⟨input (R i v),((mem_probes C (L i) (R i) r v).mp hv).2⟩
    rcases Finset.mem_union.mp hax with ha | hx
    · obtain ⟨_,⟨a,hw,hop⟩,hf,p,_,ht⟩ := Finset.mem_filter.mp ha
      refine ⟨a,hw,⟨rimInput M p,ht⟩,⟨i0,hf⟩,?_⟩
      have ht' : value C (rimInput M p) (N+a.val) = true := hw ▸ ht
      exact fun r hr => ⟨_,((wire_and C _ a hop).mp ht' r hr).2⟩
    · obtain ⟨_,⟨a,hw,_,hr⟩,hf,hwide⟩ := Finset.mem_filter.mp hx
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (singletons (n := N) C w).card)
      exact ⟨a,hw,⟨onePoint p,(mem_singletons C w p).mp hp⟩,⟨i0,hf⟩,
        fun r h => let ⟨v,hv⟩ := hr r h; ⟨onePoint v,hv⟩⟩
  let paid : Finset (Fin gates.length) := Finset.univ.filter (fun a : Fin gates.length => N+a.val ∈ UAX)
  have hPaid (w : ℕ) (hw : w ∈ UAX) : w ∈ paid.image (fun a => N+a.val) := by
    obtain ⟨a,ha,_,_,_⟩ := chargeInfo w hw
    let b : Fin gates.length := ⟨a.val,hLen ▸ a.isLt⟩
    have hb : N+b.val = w := ha.symm
    exact Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb.symm ▸ hw⟩,hb⟩
  have hPayCard : N*q ≤ paid.card :=
    hUAXcard.trans ((Finset.card_le_card hPaid).trans Finset.card_image_le)
  have hnotJ : j ∉ paid := by
    intro hj
    obtain ⟨_,_,⟨x,hx⟩,_,_⟩ := chargeInfo (N+j.val) (Finset.mem_filter.mp hj).2
    rw [patchC_false gates j x] at hx
    contradiction
  have hnotH : h ∉ paid := by
    intro hh
    obtain ⟨_,_,_,⟨i,hf⟩,_⟩ := chargeInfo (N+h.val) (Finset.mem_filter.mp hh).2
    rw [hDomHigh _ (offDom i)] at hf
    contradiction
  have hReadNone (a : Fin gates.length) (ha : a ∈ paid) (hja : j < a) :
      N+j.val ∉ (gates.get a).inputs := by
    intro hReader
    obtain ⟨b,hb,_,_,hInputs⟩ := chargeInfo (N+a.val) (Finset.mem_filter.mp ha).2
    have hv : b.val = a.val := by omega
    have hn : j.val ≠ a.val := Nat.ne_of_lt hja
    have hg : C.gates.get b = gates.get a := by
      change (gates.set j.val ⟨GateOp.or,[]⟩)[b.val] = gates[a.val]
      simp [hv,hn]
    rw [hg] at hInputs
    obtain ⟨x,hx⟩ := hInputs (N+j.val) hReader
    rw [patchC_false gates j x] at hx
    contradiction
  have hh := paid_card (n := N) gates j h hEarlier paid hnotJ hnotH hReadNone
  omega
