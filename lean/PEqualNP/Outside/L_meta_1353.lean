import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1353

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

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

def Step {n : ℕ} (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ) : Prop :=
  ∀ w, n ≤ w → w < n + C.size → ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∈ R → P.card ≤ 1) ∧
    (∀ r ∈ P, r < w) ∧
    ∀ (x y : Fin n → Bool), X x → X y → (∀ r ∈ P, value C x r = true → value C y r = true) →
      value C x w = true → value C y w = true

lemma value_mono {n : ℕ} (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ)
    (hS : Step C X R)
    (x y : Fin n → Bool) (hx : X x) (hy : X y) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, _, hP, hstep⟩ := hS w (by omega) hw
      exact hstep x y hx hy fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma cut {n : ℕ} (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ)
    (hS : Step C X R)
    (G : Finset ℕ) (hGates : ∀ w ∈ G ∪ R, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G ∪ R → w < t) :
    ∃ B : Finset ℕ, Disjoint B (G ∪ R) ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, X x → X y → (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ _ _ h => h⟩
  | succ t ih =>
    have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ t ∈ G ∪ R
    · obtain ⟨P, hPcard, hPR, hP, hp⟩ := hS t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G ∪ R → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hu := Finset.card_union_le (F.erase t) P
      have he := Finset.card_erase_add_one hex.1
      change F'.card ≤ _ at hu
      refine ⟨B, hd, ?_, ?_⟩
      · by_cases htG : t ∈ G
        · have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hg, hlt⟩
              by_cases h : w = t
              · exact Or.inl h
              · exact Or.inr ⟨hg, by omega⟩
            · rintro (rfl | ⟨hg, hlt⟩)
              · exact ⟨htG, by omega⟩
              · exact ⟨hg, by omega⟩
          rw [hfilter, Finset.card_insert_of_notMem (by simp)]
          omega
        · have htR : t ∈ R := (Finset.mem_union.mp hex.2).resolve_left htG
          have := hPR htR
          omega
      · intro x y hx hy hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y hx hy fun r hr => hi x y hx hy hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hx hy hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G ∪ R → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      exact ⟨B, hd, by omega, hi⟩

def offSet {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∉ T)

lemma weight {n : ℕ} (T : Finset (Fin n)) :
    (Finset.univ.filter (fun p => offSet T p = true)).card = n - T.card := by
  have h : Finset.univ.filter (fun p => offSet T p = true) = Tᶜ := by
    ext p
    simp [offSet]
  rw [h, Finset.card_compl, Fintype.card_fin]

lemma union_bound {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hsize : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (B : Finset ℕ) (A : ℕ → Finset (Fin n))
    (hA : ∀ w ∈ B, (A w).card ≤ q ∨ ∃ i, A w = S i) :
    (B.biUnion A).card ≤ B.card * q + 1 := by
  classical
  by_cases hbig : ∃ w ∈ B, ∃ i, A w = S i
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
          omega
    have hsub : B.biUnion A ⊆ S i ∪ R.biUnion (fun v => A v \ S i) := by
      intro p hp
      obtain ⟨v,hv,hp⟩ := Finset.mem_biUnion.mp hp
      by_cases h : p ∈ S i
      · exact Finset.mem_union_left _ h
      · have hne : v ≠ w := by rintro rfl; exact h (hi ▸ hp)
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

def specific {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (R : Finset ℕ) (i : Fin m) :
    Finset ℕ := (Finset.Ico n (n+C.size)).filter fun w => w ∉ R ∧
      value C (offSet (S i)) w = false ∧ ∀ j, j ≠ i → value C (offSet (S j)) w = true

lemma own_count {q n m K : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ)
    (hS : Step C X R) (hR : ∀ w ∈ R, n ≤ w ∧ w < n + C.size)
    (hX : ∀ T : Finset (Fin n), T.card ≤ K → X (offSet T))
    (i : Fin m) (o c : ℕ)
    (heval : ∀ T : Finset (Fin n), T.card ≤ K →
      (value C (offSet T) o = false ↔ S i ⊆ T))
    (hc : c ≤ q) (hK : c*q < K) : c ≤ (specific C S R i).card := by
  classical
  by_contra! hsmall
  let G := specific C S R i
  have hgate : ∀ w ∈ G ∪ R, n ≤ w ∧ w < n + C.size := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
    · exact hR w hw
  obtain ⟨B, hd, hBC, hcut⟩ := cut C X R hS G hgate (n+C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hf := Finset.card_filter_le G (fun w => w < n+C.size)
    simp only [Finset.card_singleton] at hBC
    change G.card < c at hsmall
    omega
  have hpositive : 1 ≤ c := by omega
  have hqK : q + 1 ≤ K := by
    have hp := Nat.mul_le_mul_right q hpositive
    rw [Nat.one_mul] at hp
    omega
  have hsK : ∀ j, (S j).card ≤ K := fun j => by rw [hsize]; exact hqK
  have witness (w : ℕ) (hw : w ∈ B) : ∃ T : Finset (Fin n),
      (T.card ≤ q ∨ ∃ j, T = S j) ∧ (T ∩ S i).card ≤ 1 ∧
      (value C (offSet T) w = true → value C (offSet (S i)) w = true) := by
    by_cases hv : value C (offSet (S i)) w = true
    · exact ⟨∅,Or.inl (by simp),by simp,fun _ => hv⟩
    · by_cases hin : w < n
      · let p : Fin n := ⟨w,hin⟩
        refine ⟨{p},Or.inl (by simp; omega),?_,?_⟩
        · exact (Finset.card_le_card (Finset.inter_subset_left : {p} ∩ S i ⊆ {p})).trans (by simp)
        · intro h
          change value C (offSet {p}) p = true at h
          simp [input_value,offSet] at h
      · by_cases bound : w < n+C.size
        · have hnGR := Finset.disjoint_left.mp hd hw
          have hn : w ∉ specific C S R i := fun h => hnGR (Finset.mem_union_left _ h)
          have hnR : w ∉ R := fun h => hnGR (Finset.mem_union_right _ h)
          have hex : ∃ j, j ≠ i ∧ ¬ value C (offSet (S j)) w = true := by
            by_contra! neg
            apply hn
            refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,bound⟩,hnR,?_,neg⟩
            simpa using hv
          obtain ⟨j,hji,hj⟩ := hex
          exact ⟨S j,Or.inr ⟨j,rfl⟩,(hinter j i hji).le,fun h => absurd h hj⟩
        · refine ⟨∅,Or.inl (by simp),by simp,fun h => ?_⟩
          have hm := missing_value C (offSet (∅ : Finset (Fin n))) w (by omega)
          rw [hm] at h
          exact Bool.noConfusion h
  let A (w : ℕ) : Finset (Fin n) := if h : w ∈ B then (witness w h).choose else ∅
  have ha (w : ℕ) (hw : w ∈ B) :
      ((A w).card ≤ q ∨ ∃ j, A w = S j) ∧ (A w ∩ S i).card ≤ 1 ∧
      (value C (offSet (A w)) w = true → value C (offSet (S i)) w = true) := by
    simpa [A,hw] using (witness w hw).choose_spec
  let U := B.biUnion A
  have hu : U.card ≤ K := by
    have h := union_bound S hsize hinter B A (fun w hw => (ha w hw).1)
    have h' := Nat.mul_le_mul_right q hb
    change (B.biUnion A).card ≤ K
    omega
  have hSi : value C (offSet (S i)) o = false := (heval (S i) (hsK i)).mpr (by rfl)
  have hot : value C (offSet U) o = false := by
    by_contra hne
    have ht : value C (offSet U) o = true := by simpa using hne
    have h2 := hcut (offSet U) (offSet (S i)) (hX U hu) (hX _ (hsK i)) (fun w hw hp => by
      apply (ha w hw).2.2
      have hAU : A w ⊆ U := Finset.subset_biUnion_of_mem A hw
      apply value_mono C X R hS (offSet U) (offSet (A w)) (hX U hu)
        (hX _ ((Finset.card_le_card hAU).trans hu)) _ w hp
      intro p hp
      simp only [offSet, decide_eq_true_eq] at hp ⊢
      exact fun hm => hp (hAU hm)) o (Finset.mem_singleton_self o) ht
    rw [hSi] at h2
    exact Bool.noConfusion h2
  have hSub := (heval U hu).mp hot
  have hcover : S i ⊆ B.biUnion (fun w => A w ∩ S i) := by
    intro p hp
    obtain ⟨w,hw,hm⟩ := Finset.mem_biUnion.mp (hSub hp)
    exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_inter.mpr ⟨hm,hp⟩⟩
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le_card_mul B (fun w => A w ∩ S i) 1 (fun w hw => (ha w hw).2.1)
  rw [hsize] at h1
  simp only [Nat.mul_one] at h2
  omega

lemma main : ∀ (q n m s : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, s + 1 ≤ (Finset.univ.filter (fun v : Fin n => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * min q ((n - (s + 1) + q - 1) / q - 1) +
        (Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length := by
  classical
  intro q n m s S hq hsize hinter gates out j hg hj huniq heval hfalse
  let C : Circuit := ⟨gates, 0⟩
  let K := n - (s + 1)
  let c := min q ((K + q - 1) / q - 1)
  let Rd := Finset.univ.filter (fun i : Fin gates.length =>
    j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)
  let R : Finset ℕ := insert (n + (j : ℕ)) (Rd.image (fun i : Fin gates.length => n + (i : ℕ)))
  let X : (Fin n → Bool) → Prop := fun x =>
    s + 1 ≤ (Finset.univ.filter (fun v : Fin n => x v = true)).card
  have hjv : ∀ x, X x → value C x (n + (j : ℕ)) = false := fun x hx => hfalse x hx
  have hnotR : n + (j : ℕ) ∉ Rd.image (fun i : Fin gates.length => n + (i : ℕ)) := by
    intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    have := (Finset.mem_filter.mp hi).2.1
    have : (j : ℕ) < (i : ℕ) := this
    omega
  have hRcard : R.card = Rd.card + 1 := by
    rw [Finset.card_insert_of_notMem hnotR, Finset.card_image_of_injective]
    intro a b hab
    exact Fin.ext (by simpa using hab)
  have hR : ∀ w ∈ R, n ≤ w ∧ w < n + C.size := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · rw [h]
      exact ⟨by omega, by change _ < n + gates.length; omega⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨by omega, by change _ < n + gates.length; omega⟩
  have hS : Step C X R := by
    intro w hn hw
    have hk : w - n < gates.length := by change w < n + gates.length at hw; omega
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    simp only [Nat.add_sub_cancel_left] at hk
    by_cases hkj : k = (j : ℕ)
    · refine ⟨∅, by simp, by simp, by simp, fun x y hx hy _ h => ?_⟩
      rw [hkj, hjv x hx] at h
      exact Bool.noConfusion h
    · have hop : gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or := by
        rcases (hg gates[k] (List.getElem_mem _)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (congrArg Fin.val (huniq ⟨k, hk⟩ h)) hkj
      have hlen := (hg gates[k] (List.getElem_mem _)).2
      let P0 := gates[k].inputs.toFinset.filter (· < n + k)
      have hP0 : P0.card ≤ 2 :=
        (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
      by_cases hR' : n + k ∈ R
      · have hrd : (j : ℕ) < k ∧ n + (j : ℕ) ∈ gates[k].inputs := by
          rcases Finset.mem_insert.mp hR' with h | h
          · omega
          · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
            have hik : (i : ℕ) = k := by omega
            have hi2 := (Finset.mem_filter.mp hi).2
            have e : i = ⟨k, hk⟩ := Fin.ext hik
            rw [e] at hi2
            exact ⟨hi2.1, hi2.2⟩
        have hmem : n + (j : ℕ) ∈ P0 :=
          Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hrd.2, by omega⟩
        refine ⟨P0.erase (n + (j : ℕ)), (Finset.card_erase_le).trans hP0, fun _ => ?_,
          fun r hr => (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).2, ?_⟩
        · have := Finset.card_erase_add_one hmem
          omega
        · intro x y hx hy hxy
          refine gate_mono C k hk hop x y fun r hm hlt hv => ?_
          by_cases hrj : r = n + (j : ℕ)
          · rw [hrj, hjv x hx] at hv
            exact Bool.noConfusion hv
          · exact hxy r (Finset.mem_erase.mpr ⟨hrj,
              Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, hlt⟩⟩) hv
      · refine ⟨P0, hP0, fun h => absurd h hR', fun r hr => (Finset.mem_filter.mp hr).2, ?_⟩
        intro x y _ _ hxy
        exact gate_mono C k hk hop x y fun r hm hlt hv =>
          hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, hlt⟩) hv
  let G (i : Fin m) := specific C S R i
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ i' _ hij
    refine Finset.disjoint_left.mpr fun w hi hj => ?_
    have htrue := (Finset.mem_filter.mp hi).2.2.2 i' (Ne.symm hij)
    have hfalse := (Finset.mem_filter.mp hj).2.2.1
    simp [htrue] at hfalse
  have hi (i : Fin m) : c ≤ (G i).card := by
    by_cases hc0 : c = 0
    · omega
    have hd2 : 2 ≤ (K + q - 1) / q := by
      have : c ≤ (K + q - 1) / q - 1 := min_le_right _ _
      omega
    have hmul := Nat.div_mul_le_self (K + q - 1) q
    have hcq : c * q ≤ ((K + q - 1) / q - 1) * q := Nat.mul_le_mul_right q (min_le_right _ _)
    have hsub : ((K + q - 1) / q - 1) * q = (K + q - 1) / q * q - q := by
      rw [Nat.sub_mul, Nat.one_mul]
    have h2q : 2 * q ≤ (K + q - 1) / q * q := Nat.mul_le_mul_right q hd2
    have hK : c * q < K := by omega
    apply own_count S hq hsize hinter C X R hS hR (K := K) _ i (out i) c _ (min_le_left _ _) hK
    · intro T hT
      change s + 1 ≤ _
      rw [weight T]
      have : K = n - (s + 1) := rfl
      omega
    · intro T hT
      have h := heval i (offSet T)
      change value C (offSet T) (out i) = _ at h
      rw [h]
      simp [offSet,Finset.subset_iff]
  have hs : Finset.univ.biUnion G ∪ R ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    · exact Finset.mem_Ico.mpr (hR w hw)
  have hdis : Disjoint (Finset.univ.biUnion G) R := by
    refine Finset.disjoint_left.mpr fun w hw hr => ?_
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hi).2.1 hr
  have h1 : m * c ≤ (Finset.univ.biUnion G).card := by
    calc
      m*c = ∑ _i : Fin m, c := by simp
      _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum (fun i _ => hi i)
      _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
  have h2 := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hdis, hRcard] at h2
  have h3 : (Finset.Ico n (n+C.size)).card = gates.length := by simp [C,Circuit.size]
  change m * c + Rd.card + 1 ≤ gates.length
  omega

end PEqualNP.Outside.L_meta_1353

theorem PEqualNP.Outside.L_meta_1353 : ∀ (q n m s : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, s + 1 ≤ (Finset.univ.filter (fun v : Fin n => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * min q ((n - (s + 1) + q - 1) / q - 1) +
        (Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1353.main
