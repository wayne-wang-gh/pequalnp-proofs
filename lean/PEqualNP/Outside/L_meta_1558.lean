import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1558

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

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

def Sv {n : ℕ} {ι : Type*} (C : Circuit) (l : ι → Fin n → Bool) (y : Fin n → Bool)
    (p : ι) (w : ℕ) : Prop :=
  value C (l p) w = true ∧ value C y w = false

def Multi {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Sv C l y p w ∧ Sv C l y p' w

lemma list_cases (L : List ℕ) (hL : L.length ≤ 2) (Q : ℕ → Prop) :
    (L.length = 2 ∧ ∀ r ∈ L, Q r) ∨ ∃ c, ∀ r ∈ L, Q r → r = c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · exact Or.inr ⟨0, fun r hr => absurd hr (by simp)⟩
  · exact Or.inr ⟨a, fun r hr _ => by simpa using hr⟩
  · by_cases ha : Q a
    · by_cases hb : Q b
      · refine Or.inl ⟨rfl, fun r hr => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · exact ha
        · exact hb
      · refine Or.inr ⟨a, fun r hr hq => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · rfl
        · exact absurd hq hb
    · refine Or.inr ⟨b, fun r hr hq => ?_⟩
      rcases List.mem_pair.mp hr with rfl | rfl
      · exact absurd hq ha
      · rfl
  · simp at hL

lemma step_cases {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < C.gates.length) (hm : Multi C T l y (n + k)) :
    (∃ r ∈ C.gates[k].inputs, r < n + k ∧ ∀ p ∈ T, Sv C l y p (n + k) → Sv C l y p r) ∨
    (C.gates[k].op = GateOp.or ∧ C.gates[k].inputs.length = 2 ∧
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) ∧
      ∀ p ∈ T, Sv C l y p (n + k) → ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Sv C l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
  · left
    have hy := hs0.2
    by_contra hcon
    have hall : ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C y r = true := by
      intro r hr
      by_contra hr2
      apply hcon
      have hlt := ((and_value C k hk hop (l p0)).mp hs0.1 r hr).1
      refine ⟨r, hr, hlt, fun p _ hsp => ⟨((and_value C k hk hop (l p)).mp hsp.1 r hr).2, ?_⟩⟩
      by_contra hne
      exact hr2 ⟨hlt, by simpa using hne⟩
    rw [(and_value C k hk hop y).mpr hall] at hy
    exact Bool.noConfusion hy
  · have hyall : ∀ r ∈ C.gates[k].inputs, r < n + k → value C y r = false := by
      intro r hr hlt
      by_contra h
      have h2 : value C y (n + k) = true :=
        (or_value C k hk hop y).mpr ⟨r, hr, hlt, by simpa using h⟩
      rw [hs0.2] at h2
      exact Bool.noConfusion h2
    have hsv : ∀ p ∈ T, Sv C l y p (n + k) →
        ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C (l p) r = true ∧ Sv C l y p r := by
      intro p _ hsp
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C k hk hop (l p)).mp hsp.1
      exact ⟨r, hr, hlt, hv, hv, hyall r hr hlt⟩
    rcases list_cases C.gates[k].inputs (hC _ (List.getElem_mem hk)).2
      (fun r => ∃ p ∈ T, r < n + k ∧ value C (l p) r = true) with ⟨hlen, hQ⟩ | ⟨c, hc⟩
    · right
      refine ⟨hop, hlen, fun r hr => ?_, fun p hp hsp => ?_⟩
      · obtain ⟨p, hp, _, hv⟩ := hQ r hr
        exact ⟨p, hp, hv⟩
      · obtain ⟨r, hr, hlt, _, hs⟩ := hsv p hp hsp
        exact ⟨r, hr, hlt, hs⟩
    · left
      obtain ⟨r, hr, hlt, hv, _⟩ := hsv p0 hp0 hs0
      have hrc := hc r hr ⟨p0, hp0, hlt, hv⟩
      refine ⟨r, hr, hlt, fun p hp hsp => ?_⟩
      obtain ⟨r', hr', hlt', hv', hs'⟩ := hsv p hp hsp
      have hrc' := hc r' hr' ⟨p, hp, hlt', hv'⟩
      rw [hrc, ← hrc']
      exact hs'

lemma frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < C.gates.length, Multi C T l y (n + k) →
      C.gates[k].op = GateOp.or → C.gates[k].inputs.length = 2 →
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) → n + k ∈ W)
    (hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, Multi C T l y w → w < t)
    (T' : Finset ι) (hT' : T' ⊆ T) (hs : ∀ p ∈ T', ∃ w ∈ F, Sv C l y p w) :
    T'.card ≤ F.card + (W.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T' := by
      intro p hp p' hp' e
      by_contra hne
      have hc : Multi C T l y (f p) :=
        ⟨p, hT' hp, p', hT' hp', hne, hfs p hp, by rw [e]; exact hfs p' hp'⟩
      have := hF (f p) (hfF p hp) hc
      omega
    have := Finset.card_le_card_of_injOn f (fun p hp => hfF p hp) hinj
    omega
  | succ t ih =>
    have hle : (W.filter (· < t)).card ≤ (W.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ Multi C T l y t
    · obtain ⟨h1, h2⟩ := hlen t hex.2
      have hk : t - n < C.gates.length := by omega
      have htk : t = n + (t - n) := by omega
      have hm : Multi C T l y (n + (t - n)) := by rw [← htk]; exact hex.2
      have he := Finset.card_erase_add_one hex.1
      rcases step_cases C T l y hC (t - n) hk hm with ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
      · rw [← htk] at hlt hall
        let F' := insert r (F.erase t)
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with hw | hw
          · rw [hw]; exact hlt
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsv⟩ := hs p hp
          by_cases h : w = t
          · subst h
            exact ⟨r, Finset.mem_insert_self _ _, hall p (hT' hp) hsv⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_insert_le r (F.erase t)
        change F'.card ≤ _ at hu
        omega
      · rw [← htk] at hsv
        have htW : t ∈ W := by
          have := hW (t - n) hk hm hop hlen2 hQ
          rwa [← htk] at this
        let P : Finset ℕ := (C.gates[t - n].inputs.filter (· < t)).toFinset
        have hPcard : P.card ≤ 2 := by
          have h1 := List.toFinset_card_le (C.gates[t - n].inputs.filter (· < t))
          have h2 := List.length_filter_le (fun r => decide (r < t)) C.gates[t - n].inputs
          change P.card ≤ _ at h1
          omega
        let F' := F.erase t ∪ P
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsvp⟩ := hs p hp
          by_cases h : w = t
          · subst h
            obtain ⟨r, hr, hlt, hsr⟩ := hsv p (hT' hp) hsvp
            exact ⟨r, Finset.mem_union_right _ (List.mem_toFinset.mpr
              (List.mem_filter.mpr ⟨hr, by simpa using hlt⟩)), hsr⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hsvp⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_union_le (F.erase t) P
        change F'.card ≤ _ at hu
        have hfilter : W.filter (· < t + 1) = insert t (W.filter (· < t)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hlt⟩
            by_cases h : w = t
            · exact Or.inl h
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, hlt⟩)
            · exact ⟨htW, by omega⟩
            · exact ⟨hg, by omega⟩
        rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
    · have hF' : ∀ w ∈ F, Multi C T l y w → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      have := ih F hF' hs
      omega

lemma family {n : ℕ} {ι : Type*} (gates : List Gate)
    (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset ι) (l : ι → Fin n → Bool) (y : Fin n → Bool) (o : ℕ)
    (ho : ∀ p ∈ T, Sv ⟨gates, 0⟩ l y p o)
    (hin : ∀ w, w < n → ¬ Multi ⟨gates, 0⟩ T l y w)
    (K : Finset (Fin gates.length))
    (hK : ∀ g : Fin gates.length, Multi ⟨gates, 0⟩ T l y (n + (g : ℕ)) →
      gates[(g : ℕ)].op = GateOp.or → gates[(g : ℕ)].inputs.length = 2 →
      (∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ T, value ⟨gates, 0⟩ (l p) r = true) → g ∈ K) :
    T.card ≤ K.card + 1 := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let W : Finset ℕ := Finset.image (fun g : Fin gates.length => n + (g : ℕ)) K
  have hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length := by
    intro w hc
    refine ⟨Nat.le_of_not_lt fun h => hin w h hc, ?_⟩
    by_contra hge
    obtain ⟨p, _, _, _, _, hsv, _⟩ := hc
    have hm := missing_value C (l p) w (by unfold Circuit.size; omega)
    have h1 := hsv.1
    rw [hm] at h1
    exact Bool.noConfusion h1
  have h := frontier C T l y hC W
    (fun k hk hm hop hl hQ => Finset.mem_image.mpr ⟨(⟨k, hk⟩ : Fin gates.length), hK ⟨k, hk⟩ hm hop hl hQ, rfl⟩)
    hlen (n + C.gates.length) {o}
    (fun w _ hc => (hlen w hc).2) T (Finset.Subset.refl T)
    (fun p hp => ⟨o, Finset.mem_singleton_self o, ho p hp⟩)
  have h1 := Finset.card_filter_le W (· < n + C.gates.length)
  have h2 : W.card ≤ K.card := Finset.card_image_le
  rw [Finset.card_singleton] at h
  omega

def rowL {n m : ℕ} (R : Fin m → Fin n → Finset (Fin n)) (i : Fin m) (p : Fin n) :
    Fin n → Bool :=
  fun v => decide (v ∈ R i p)

def coY {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) : Fin n → Bool :=
  fun v => decide (v ∉ S i)

lemma kill {n m : ℕ} (gates : List Gate)
    (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Fin m → Finset (Fin n)) (R : Fin m → Fin n → Finset (Fin n)) (i j : Fin m)
    (hint : (S i ∩ S j).card ≤ 1)
    (hnA : ¬ ∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) (w : ℕ)
    (hi : Multi ⟨gates, 0⟩ (S i) (rowL R i) (coY S i) w)
    (hj : value ⟨gates, 0⟩ (coY S j) w = false) : False := by
  obtain ⟨p, hp, p', hp', hne, hs, hs'⟩ := hi
  have key : ∀ a ∈ S i, a ∉ S j → value ⟨gates, 0⟩ (rowL R i a) w = true → False := by
    intro a ha haj hv
    have := mono ⟨gates, 0⟩ hC (rowL R i a) (coY S j) (fun v hv => ?_) w hv
    · rw [hj] at this
      exact Bool.noConfusion this
    · simp only [rowL, coY, decide_eq_true_eq] at hv ⊢
      intro hvj
      exact hnA ⟨a, Finset.mem_sdiff.mpr ⟨ha, haj⟩, ⟨v, Finset.mem_inter.mpr ⟨hv, hvj⟩⟩⟩
  by_cases hpj : p ∈ S j
  · by_cases hpj' : p' ∈ S j
    · exact hne (Finset.card_le_one.mp hint p (Finset.mem_inter.mpr ⟨hp, hpj⟩) p'
        (Finset.mem_inter.mpr ⟨hp', hpj'⟩))
    · exact key p' hp' hpj' hs'.1
  · exact key p hp hpj hs.1

def InK {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)) (i : Fin m) (g : Fin gates.length) : Prop :=
  Multi ⟨gates, 0⟩ (S i) (rowL R i) (coY S i) (n + (g : ℕ)) ∧
    gates[(g : ℕ)].op = GateOp.or ∧ gates[(g : ℕ)].inputs.length = 2 ∧
    ∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ S i, value ⟨gates, 0⟩ (rowL R i p) r = true


lemma lines_card : ∀ t : Fin 13, ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)).card = 4 := by
  decide

lemma lines_inter : ∀ i j : Fin 13, i ≠ j →
    (({i, i + 1, i + 3, i + 9} : Finset (Fin 13)) ∩ {j, j + 1, j + 3, j + 9}).card ≤ 1 := by
  decide

lemma and_down {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (y l : Fin n → Bool)
    (hy : value C y (n + k) = false) (hl : value C l (n + k) = true) :
    ∃ r, r < n + k ∧ value C y r = false ∧ r ∈ C.gates[k].inputs := by
  have h1 := (and_value C k hk hop l).mp hl
  have h2 : ¬ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C y r = true := fun h => by
    have h3 := (and_value C k hk hop y).mpr h
    rw [hy] at h3
    exact Bool.noConfusion h3
  by_contra hc
  apply h2
  intro r hr
  refine ⟨(h1 r hr).1, ?_⟩
  by_contra hv
  exact hc ⟨r, (h1 r hr).1, Bool.eq_false_iff.mpr hv, hr⟩

lemma three_in (l : List ℕ) (hl : l.length ≤ 2) (a b c : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hc : c ∈ l) : a = b ∨ a = c ∨ b = c := by
  rcases l with _ | ⟨x, _ | ⟨z, _ | ⟨u, t⟩⟩⟩
  · simp at ha
  · simp at ha hb hc
    omega
  · simp at ha hb hc
    omega
  · simp only [List.length_cons] at hl
    omega

lemma first_and {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Q : ℕ → Prop) (hin : ∀ w, w < n → ¬ Q w) (hmiss : ∀ w, n + C.gates.length ≤ w → ¬ Q w)
    (hor : ∀ k (hk : k < C.gates.length), C.gates[k].op = GateOp.or → Q (n + k) →
      ∃ r, r < n + k ∧ Q r) (o : ℕ) (ho : Q o) :
    ∃ k, ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.and ∧ Q (n + k) ∧
      ∀ r, r < n + k → ¬ Q r := by
  classical
  have hex : ∃ w, Q w := ⟨o, ho⟩
  obtain ⟨w, hw, hmin⟩ : ∃ w, Q w ∧ ∀ r, r < w → ¬ Q r :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => Nat.find_min hex hr⟩
  have h1 : n ≤ w := by
    by_contra h
    exact hin w (by omega) hw
  have h2 : w < n + C.gates.length := by
    by_contra h
    exact hmiss w (by omega) hw
  have hk : w - n < C.gates.length := by omega
  have hwk : n + (w - n) = w := by omega
  refine ⟨w - n, hk, ?_, by rw [hwk]; exact hw, fun r hr => hmin r (by omega)⟩
  rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
  · exact hop
  · exfalso
    obtain ⟨r, hr, hq⟩ := hor (w - n) hk hop (by rw [hwk]; exact hw)
    exact hmin r (by omega) hq

def QQ {n : ℕ} (C : Circuit) (y1 y2 t : Fin n → Bool) (w : ℕ) : Prop :=
  value C y1 w = false ∧ value C y2 w = false ∧ value C t w = true

lemma qq_and {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (y1 y2 t : Fin n → Bool)
    (hno : ∀ v : Fin n, ¬ (t v = true ∧ y1 v = false ∧ y2 v = false))
    (o : ℕ) (ho : QQ C y1 y2 t o) :
    ∃ k, ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.and ∧ QQ C y1 y2 t (n + k) ∧
      ∀ r, r < n + k → ¬ QQ C y1 y2 t r := by
  refine first_and C hC (QQ C y1 y2 t) ?_ ?_ ?_ o ho
  · rintro w hw ⟨h1, h2, h3⟩
    exact hno ⟨w, hw⟩ ⟨(input_value C t ⟨w, hw⟩).symm.trans h3,
      (input_value C y1 ⟨w, hw⟩).symm.trans h1, (input_value C y2 ⟨w, hw⟩).symm.trans h2⟩
  · rintro w hw ⟨_, _, h3⟩
    rw [missing_value C _ w (by unfold Circuit.size; omega)] at h3
    exact Bool.noConfusion h3
  · rintro k hk hop ⟨h1, h2, h3⟩
    obtain ⟨r, hr, hlt, hv⟩ := (or_value C k hk hop t).mp h3
    refine ⟨r, hlt, ?_, ?_, hv⟩
    · by_contra hv'
      have h4 := (or_value C k hk hop y1).mpr ⟨r, hr, hlt, by simpa using hv'⟩
      rw [h1] at h4
      exact Bool.noConfusion h4
    · by_contra hv'
      have h4 := (or_value C k hk hop y2).mpr ⟨r, hr, hlt, by simpa using hv'⟩
      rw [h2] at h4
      exact Bool.noConfusion h4

def MK {n : ℕ} (gates : List Gate) (T : Finset (Fin n)) (l : Fin n → Fin n → Bool)
    (y : Fin n → Bool) (g : Fin gates.length) : Prop :=
  Multi ⟨gates, 0⟩ T l y (n + (g : ℕ)) ∧ gates[(g : ℕ)].op = GateOp.or

lemma mk_card {n : ℕ} (gates : List Gate)
    (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset (Fin n)) (l : Fin n → Fin n → Bool) (y : Fin n → Bool) (o : ℕ)
    (ho : ∀ p ∈ T, Sv ⟨gates, 0⟩ l y p o)
    (hin : ∀ p ∈ T, ∀ v : Fin n, l p v = true → y v = false → v = p) :
    ∃ K : Finset (Fin gates.length), T.card ≤ K.card + 1 ∧ ∀ g, g ∈ K ↔ MK gates T l y g := by
  classical
  refine ⟨Finset.univ.filter fun g => MK gates T l y g, ?_, fun g => by simp⟩
  refine family gates hC T l y o ho (fun w hw hc => ?_) _
    (fun g hm hop _ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hm, hop⟩)
  obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
  have e : ∀ a ∈ T, Sv ⟨gates, 0⟩ l y a w → (⟨w, hw⟩ : Fin n) = a := fun a ha hsa =>
    hin a ha ⟨w, hw⟩ ((input_value _ _ ⟨w, hw⟩).symm.trans hsa.1)
      ((input_value _ _ ⟨w, hw⟩).symm.trans hsa.2)
  exact hne ((e p hp hs1).symm.trans (e p' hp' hs2))

def ln (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def Bt (t p : Fin 13) : Finset (Fin 13) :=
  if t = 0 then (if p = 0 then {4, 8} else {8})
  else if t = 1 then (if p = 4 then {8} else {5})
  else if t = 2 then (if p = 2 then {9} else {8})
  else if t = 3 then (if p = 6 then {2} else {11})
  else if t = 4 then (if p = 0 then {3, 12} else {12})
  else if t = 5 then (if p = 5 then {12} else {7})
  else if t = 6 then (if p = 7 then {3} else {4})
  else if t = 7 then (if p = 8 then {6} else {12})
  else if t = 8 then (if p = 11 then {5} else {10})
  else if t = 9 then (if p = 10 then {1} else {6})
  else if t = 10 then (if p = 0 then {1, 2} else {1})
  else if t = 11 then (if p = 12 then {9} else {2})
  else (if p = 0 then {6, 9} else {6})

def Rt (t p : Fin 13) : Finset (Fin 13) := insert p (Bt t p)

lemma factZ : ∀ t : Fin 13, ∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧
    ¬ ∃ s ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ ln s ∧ b ∈ ln s) ∧ a ∉ ln t ∧ b ∉ ln t := by
  decide +kernel

lemma factT : ∀ t : Fin 13, ∀ p ∈ ln t, ∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧
    ¬ ∃ s ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ ln s ∧ b ∈ ln s) ∧ a ∈ Rt t p ∧ b ∈ Rt t p := by
  decide +kernel

lemma factR : ∀ t : Fin 13, ∀ p ∈ ln t, Rt t p ∩ ln t = {p} := by
  decide +kernel

lemma factCa : ∀ s s' : Fin 13, s ≠ s' → (s = 12 → s' ≠ 3 ∧ s' ≠ 5) → (s' = 12 → s ≠ 3 ∧ s ≠ 5) →
    ¬ ((∃ p ∈ ln s \ ln s', Rt s p ∩ ln s' ≠ ∅) ∧
      (∃ p ∈ ln s' \ ln s, Rt s' p ∩ ln s ≠ ∅)) := by
  decide +kernel

lemma factC : ∀ s s' : Fin 13, s ≠ s' → (s = 12 → s' ≠ 3 ∧ s' ≠ 5) → (s' = 12 → s ≠ 3 ∧ s ≠ 5) →
    ¬ ((∃ p ∈ ln s \ ln s', (Rt s p ∩ ln s').Nonempty) ∧
      (∃ p ∈ ln s' \ ln s, (Rt s' p ∩ ln s).Nonempty)) := by
  simp only [Finset.nonempty_iff_ne_empty]
  exact factCa

lemma factS3 : ∀ a ∈ ln 3, a ≠ 6 → a ≠ 12 → ∀ v ∈ Rt 3 a, v ∉ ln 12 := by
  decide +kernel

lemma factS5 : ∀ a ∈ ln 5, a ≠ 5 → a ≠ 8 → ∀ v ∈ Rt 5 a, v ∉ ln 12 := by
  decide +kernel

lemma factT3 : ∀ p ∈ ({3, 4, 12} : Finset (Fin 13)), p ∈ ln 3 ∧ p ≠ 6 := by
  decide +kernel

lemma factT5 : ∀ p ∈ ({1, 6, 8} : Finset (Fin 13)), p ∈ ln 5 ∧ p ≠ 5 := by
  decide +kernel

lemma factQ3 : ∀ v : Fin 13, ¬ (rowL Rt 3 6 v = true ∧ coY ln 3 v = false ∧ coY ln 12 v = false) := by
  decide +kernel

lemma factQ5 : ∀ v : Fin 13, ¬ (rowL Rt 5 5 v = true ∧ coY ln 5 v = false ∧ coY ln 12 v = false) := by
  decide +kernel

lemma factQ35 : ∀ v : Fin 13, ¬ (rowL Rt 5 5 v = true ∧ coY ln 3 v = false ∧ coY ln 5 v = false) := by
  decide +kernel

lemma hinR (i p : Fin 13) (hp : p ∈ ln i) (v : Fin 13) (h1 : rowL Rt i p v = true)
    (h2 : coY ln i v = false) : v = p := by
  simp only [rowL, coY, decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h1 h2
  have h3 : v ∈ Rt i p ∩ ln i := Finset.mem_inter.mpr ⟨h1, h2⟩
  rw [factR i p hp] at h3
  exact Finset.mem_singleton.mp h3

lemma disj (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i j : Fin 13) (hij : i ≠ j)
    (hc : ¬ ((∃ p ∈ ln i \ ln j, (Rt i p ∩ ln j).Nonempty) ∧
      (∃ p ∈ ln j \ ln i, (Rt j p ∩ ln i).Nonempty)))
    (g : Fin gates.length) (hi : MK gates (ln i) (rowL Rt i) (coY ln i) g)
    (hj : MK gates (ln j) (rowL Rt j) (coY ln j) g) : False := by
  have hmi := hi.1
  have hmj := hj.1
  have hyi : value ⟨gates, 0⟩ (coY ln i) (13 + (g : ℕ)) = false := by
    obtain ⟨p, _, _, _, _, hs, _⟩ := hmi
    exact hs.2
  have hyj : value ⟨gates, 0⟩ (coY ln j) (13 + (g : ℕ)) = false := by
    obtain ⟨p, _, _, _, _, hs, _⟩ := hmj
    exact hs.2
  by_cases hA : ∃ p ∈ ln i \ ln j, (Rt i p ∩ ln j).Nonempty
  · have hB : ¬ ∃ s ∈ ln j \ ln i, (Rt j s ∩ ln i).Nonempty := fun hB => hc ⟨hA, hB⟩
    exact kill gates hg ln Rt j i (lines_inter j i (Ne.symm hij)) hB _ hmj hyi
  · exact kill gates hg ln Rt i j (lines_inter i j hij) hA _ hmi hyj

lemma off12 (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (s c d : Fin 13) (hS : ∀ a ∈ ln s, a ≠ c → a ≠ d → ∀ v ∈ Rt s a, v ∉ ln 12)
    (a : Fin 13) (ha : a ∈ ln s) (w : ℕ)
    (hv : value ⟨gates, 0⟩ (rowL Rt s a) w = true)
    (hz : value ⟨gates, 0⟩ (coY ln 12) w = false) : a = c ∨ a = d := by
  by_contra hne
  rw [not_or] at hne
  have h := mono ⟨gates, 0⟩ hg (rowL Rt s a) (coY ln 12) (fun v hv => by
    simp only [rowL, coY, decide_eq_true_eq] at hv ⊢
    exact hS a ha hne.1 hne.2 v hv) w hv
  rw [hz] at h
  exact Bool.noConfusion h

lemma sub_off (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (s c d : Fin 13) (hS : ∀ a ∈ ln s, a ≠ c → a ≠ d → ∀ v ∈ Rt s a, v ∉ ln 12)
    (T : Finset (Fin 13)) (hT : ∀ p ∈ T, p ∈ ln s ∧ p ≠ c)
    (g : Fin gates.length) (hm : MK gates T (rowL Rt s) (coY ln s) g)
    (hz : value ⟨gates, 0⟩ (coY ln 12) (13 + (g : ℕ)) = false) : False := by
  obtain ⟨⟨p, hp, p', hp', hne, hs, hs'⟩, _⟩ := hm
  have e1 : p = d := (off12 gates hg s c d hS p (hT p hp).1 _ hs.1 hz).resolve_left (hT p hp).2
  have e2 : p' = d := (off12 gates hg s c d hS p' (hT p' hp').1 _ hs'.1 hz).resolve_left (hT p' hp').2
  exact hne (e1.trans e2.symm)

lemma shared_c (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (s c d : Fin 13) (hS : ∀ a ∈ ln s, a ≠ c → a ≠ d → ∀ v ∈ Rt s a, v ∉ ln 12)
    (g : Fin gates.length) (hm : MK gates (ln s) (rowL Rt s) (coY ln s) g)
    (hz : value ⟨gates, 0⟩ (coY ln 12) (13 + (g : ℕ)) = false) :
    QQ ⟨gates, 0⟩ (coY ln s) (coY ln 12) (rowL Rt s c) (13 + (g : ℕ)) := by
  obtain ⟨⟨p, hp, p', hp', hne, hs, hs'⟩, _⟩ := hm
  rcases off12 gates hg s c d hS p hp _ hs.1 hz with h | h
  · rw [← h]
    exact ⟨hs.2, hz, hs.1⟩
  · rcases off12 gates hg s c d hS p' hp' _ hs'.1 hz with h' | h'
    · rw [← h']
      exact ⟨hs'.2, hz, hs'.1⟩
    · exact absurd (h.trans h'.symm) hne

lemma two_ands (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k3 : ℕ) (hk3 : k3 < C.gates.length) (hop3 : C.gates[k3].op = GateOp.and)
    (hQ3 : QQ C (coY ln 3) (coY ln 12) (rowL Rt 3 6) (13 + k3))
    (hmin3 : ∀ r, r < 13 + k3 → ¬ QQ C (coY ln 3) (coY ln 12) (rowL Rt 3 6) r)
    (k5 : ℕ) (hk5 : k5 < C.gates.length) (hop5 : C.gates[k5].op = GateOp.and)
    (hQ5 : QQ C (coY ln 5) (coY ln 12) (rowL Rt 5 5) (13 + k5))
    (hmin5 : ∀ r, r < 13 + k5 → ¬ QQ C (coY ln 5) (coY ln 12) (rowL Rt 5 5) r) :
    ∃ k k' : ℕ, ∃ hk : k < C.gates.length, ∃ hk' : k' < C.gates.length, k ≠ k' ∧
      C.gates[k].op = GateOp.and ∧ C.gates[k'].op = GateOp.and := by
  by_cases hkk : k3 = k5
  · subst hkk
    have hin3 := (and_value C k3 hk3 hop3 (rowL Rt 3 6)).mp hQ3.2.2
    have hin5 := (and_value C k3 hk3 hop3 (rowL Rt 5 5)).mp hQ5.2.2
    obtain ⟨u, hu, hyu, hmu⟩ := and_down C k3 hk3 hop3 (coY ln 3) (rowL Rt 3 6) hQ3.1 hQ3.2.2
    obtain ⟨v, hv, hyv, hmv⟩ := and_down C k3 hk3 hop3 (coY ln 12) (rowL Rt 3 6) hQ3.2.1 hQ3.2.2
    obtain ⟨w, hw, hyw, hmw⟩ := and_down C k3 hk3 hop3 (coY ln 5) (rowL Rt 5 5) hQ5.1 hQ5.2.2
    have hv3 : ¬ value C (coY ln 3) v = false := fun h => hmin3 v hv ⟨h, hyv, (hin3 v hmv).2⟩
    have hv5 : ¬ value C (coY ln 5) v = false := fun h => hmin5 v hv ⟨h, hyv, (hin5 v hmv).2⟩
    rcases three_in _ (hC _ (List.getElem_mem hk3)).2 u v w hmu hmv hmw with h | h | h
    · rw [h] at hyu
      exact absurd hyu hv3
    · rw [← h] at hyw
      obtain ⟨k', hk', hop', hQ', hmin'⟩ := qq_and C hC (coY ln 3) (coY ln 5) (rowL Rt 5 5) factQ35 u
        ⟨hyu, hyw, (hin5 u hmu).2⟩
      refine ⟨k3, k', hk3, hk', ?_, hop3, hop'⟩
      intro e
      rw [← e] at hmin'
      exact hmin' u hu ⟨hyu, hyw, (hin5 u hmu).2⟩
    · rw [← h] at hyw
      exact absurd hyw hv5
  · exact ⟨k3, k5, hk3, hk5, hkk, hop3, hop5⟩

lemma assemble (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (K : Fin 13 → Finset (Fin gates.length))
    (hKm : ∀ i g, g ∈ K i ↔ MK gates (ln i) (rowL Rt i) (coY ln i) g)
    (hKc : ∀ i, 3 ≤ (K i).card)
    (X3 X5 : Finset (Fin gates.length)) (q3 q5 : ℕ)
    (h3s : X3 ⊆ K 3) (h3d : Disjoint X3 (K 12)) (h3c : q3 ≤ X3.card)
    (h5s : X5 ⊆ K 5) (h5d : Disjoint X5 (K 12)) (h5c : q5 ≤ X5.card) :
    ∃ U : Finset (Fin gates.length), 33 + q3 + q5 ≤ U.card ∧
      ∀ g ∈ U, gates[(g : ℕ)].op = GateOp.or := by
  classical
  let s : Finset (Fin 13) := (Finset.univ.erase 3).erase 5
  have hs : s.card = 11 := by decide
  have hs3 : ∀ i ∈ s, i ≠ 3 ∧ i ≠ 5 := fun i hi =>
    ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1, (Finset.mem_erase.mp hi).1⟩
  have hdK : ∀ i j : Fin 13, i ≠ j → (i = 12 → j ≠ 3 ∧ j ≠ 5) → (j = 12 → i ≠ 3 ∧ i ≠ 5) →
      Disjoint (K i) (K j) := fun i j hij h1 h2 =>
    Finset.disjoint_left.mpr fun g hgi hgj =>
      disj gates hg i j hij (factC i j hij h1 h2) g ((hKm i g).mp hgi) ((hKm j g).mp hgj)
  have hB : (s.biUnion K).card = ∑ i ∈ s, (K i).card :=
    Finset.card_biUnion (fun i hi j hj hij => hdK i j hij (fun _ => hs3 j hj) (fun _ => hs3 i hi))
  have hB2 : 11 * 3 ≤ (s.biUnion K).card := by
    rw [hB]
    have h2 : ∑ _i ∈ s, 3 ≤ ∑ i ∈ s, (K i).card := Finset.sum_le_sum fun i _ => hKc i
    rw [Finset.sum_const, hs, smul_eq_mul] at h2
    exact h2
  have hd3 : Disjoint (s.biUnion K) X3 := by
    rw [Finset.disjoint_biUnion_left]
    intro i hi
    by_cases h12 : i = 12
    · rw [h12]
      exact h3d.symm
    · exact (hdK i 3 (hs3 i hi).1 (fun h => absurd h h12) (fun h => absurd h (by decide))).mono_right h3s
  have hd5 : Disjoint (s.biUnion K ∪ X3) X5 := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_biUnion_left]
      intro i hi
      by_cases h12 : i = 12
      · rw [h12]
        exact h5d.symm
      · exact (hdK i 5 (hs3 i hi).2 (fun h => absurd h h12) (fun h => absurd h (by decide))).mono_right h5s
    · exact (hdK 3 5 (by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))).mono h3s h5s
  refine ⟨s.biUnion K ∪ X3 ∪ X5, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hd5, Finset.card_union_of_disjoint hd3]
    omega
  · intro g hgU
    rcases Finset.mem_union.mp hgU with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
        exact ((hKm i g).mp hi).2
      · exact ((hKm 3 g).mp (h3s h)).2
    · exact ((hKm 5 g).mp (h5s h)).2

lemma or_and_count (gates : List Gate) (U : Finset (Fin gates.length))
    (hU : ∀ g ∈ U, gates[(g : ℕ)].op = GateOp.or) (A : Finset (Fin gates.length))
    (hA : ∀ g ∈ A, gates[(g : ℕ)].op = GateOp.and) : U.card + A.card ≤ gates.length := by
  classical
  have hd : Disjoint U A := Finset.disjoint_left.mpr fun g h1 h2 => by
    cases (hU g h1).symm.trans (hA g h2)
  have h := Finset.card_le_univ (U ∪ A)
  rw [Finset.card_union_of_disjoint hd, Fintype.card_fin] at h
  exact h

theorem core (gates : List Gate) (o : Fin 13 → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hev : ∀ (t : Fin 13) (x : Fin 13 → Bool), (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧
      ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ ln t ∧ b ∈ ln t) ∧ x a = true ∧ x b = true) →
      value ⟨gates, 0⟩ x (o t) = decide (∃ v ∈ ln t, x v = true)) :
    39 ≤ gates.length := by
  classical
  have hfalse : ∀ t : Fin 13, value ⟨gates, 0⟩ (coY ln t) (o t) = false := by
    intro t
    obtain ⟨a, b, hc, ha, hb⟩ := factZ t
    have h := hev t (coY ln t) ⟨a, b, hc, decide_eq_true ha, decide_eq_true hb⟩
    have h2 : decide (∃ v ∈ ln t, coY ln t v = true) = false := by
      refine decide_eq_false ?_
      rintro ⟨v, hv, hh⟩
      exact (of_decide_eq_true hh) hv
    rw [h2] at h
    exact h
  have htrue : ∀ t : Fin 13, ∀ p ∈ ln t, value ⟨gates, 0⟩ (rowL Rt t p) (o t) = true := by
    intro t p hp
    obtain ⟨a, b, hc, ha, hb⟩ := factT t p hp
    have h := hev t (rowL Rt t p) ⟨a, b, hc, decide_eq_true ha, decide_eq_true hb⟩
    have h2 : decide (∃ v ∈ ln t, rowL Rt t p v = true) = true :=
      decide_eq_true ⟨p, hp, decide_eq_true (Finset.mem_insert_self p (Bt t p))⟩
    rw [h2] at h
    exact h
  have hK : ∀ i : Fin 13, ∃ K : Finset (Fin gates.length), (ln i).card ≤ K.card + 1 ∧
      ∀ g, g ∈ K ↔ MK gates (ln i) (rowL Rt i) (coY ln i) g := fun i =>
    mk_card gates hg (ln i) (rowL Rt i) (coY ln i) (o i)
      (fun p hp => ⟨htrue i p hp, hfalse i⟩) (fun p hp v h1 h2 => hinR i p hp v h1 h2)
  choose K hKc0 hKm using hK
  have hKc : ∀ i, 3 ≤ (K i).card := by
    intro i
    have h1 := hKc0 i
    have h2 : (ln i).card = 4 := lines_card i
    omega
  have hz12 : ∀ g ∈ K 12, value ⟨gates, 0⟩ (coY ln 12) (13 + (g : ℕ)) = false := by
    intro g hgK
    obtain ⟨⟨p, _, _, _, _, hs, _⟩, _⟩ := (hKm 12 g).mp hgK
    exact hs.2
  obtain ⟨Y3, hY3c, hY3m⟩ := mk_card gates hg ({3, 4, 12} : Finset (Fin 13)) (rowL Rt 3) (coY ln 3) (o 3)
    (fun p hp => ⟨htrue 3 p (factT3 p hp).1, hfalse 3⟩)
    (fun p hp v h1 h2 => hinR 3 p (factT3 p hp).1 v h1 h2)
  obtain ⟨Y5, hY5c, hY5m⟩ := mk_card gates hg ({1, 6, 8} : Finset (Fin 13)) (rowL Rt 5) (coY ln 5) (o 5)
    (fun p hp => ⟨htrue 5 p (factT5 p hp).1, hfalse 5⟩)
    (fun p hp v h1 h2 => hinR 5 p (factT5 p hp).1 v h1 h2)
  have c3 : ({3, 4, 12} : Finset (Fin 13)).card = 3 := by decide
  have c5 : ({1, 6, 8} : Finset (Fin 13)).card = 3 := by decide
  have hY3s : Y3 ⊆ K 3 := by
    intro g hgY
    obtain ⟨⟨p, hp, p', hp', hne, hs, hs'⟩, hop⟩ := (hY3m g).mp hgY
    exact (hKm 3 g).mpr ⟨⟨p, (factT3 p hp).1, p', (factT3 p' hp').1, hne, hs, hs'⟩, hop⟩
  have hY5s : Y5 ⊆ K 5 := by
    intro g hgY
    obtain ⟨⟨p, hp, p', hp', hne, hs, hs'⟩, hop⟩ := (hY5m g).mp hgY
    exact (hKm 5 g).mpr ⟨⟨p, (factT5 p hp).1, p', (factT5 p' hp').1, hne, hs, hs'⟩, hop⟩
  have hY3d : Disjoint Y3 (K 12) := Finset.disjoint_left.mpr fun g h1 h2 =>
    sub_off gates hg 3 6 12 factS3 _ factT3 g ((hY3m g).mp h1) (hz12 g h2)
  have hY5d : Disjoint Y5 (K 12) := Finset.disjoint_left.mpr fun g h1 h2 =>
    sub_off gates hg 5 5 8 factS5 _ factT5 g ((hY5m g).mp h1) (hz12 g h2)
  have hY3q : 2 ≤ Y3.card := by omega
  have hY5q : 2 ≤ Y5.card := by omega
  have hand3 : ¬ Disjoint (K 3) (K 12) → ∃ k, ∃ hk : k < gates.length,
      gates[k].op = GateOp.and ∧ QQ ⟨gates, 0⟩ (coY ln 3) (coY ln 12) (rowL Rt 3 6) (13 + k) ∧
      ∀ r, r < 13 + k → ¬ QQ ⟨gates, 0⟩ (coY ln 3) (coY ln 12) (rowL Rt 3 6) r := by
    intro hnd
    obtain ⟨g, h1, h2⟩ := Finset.not_disjoint_iff.mp hnd
    exact qq_and ⟨gates, 0⟩ hg _ _ _ factQ3 _
      (shared_c gates hg 3 6 12 factS3 g ((hKm 3 g).mp h1) (hz12 g h2))
  have hand5 : ¬ Disjoint (K 5) (K 12) → ∃ k, ∃ hk : k < gates.length,
      gates[k].op = GateOp.and ∧ QQ ⟨gates, 0⟩ (coY ln 5) (coY ln 12) (rowL Rt 5 5) (13 + k) ∧
      ∀ r, r < 13 + k → ¬ QQ ⟨gates, 0⟩ (coY ln 5) (coY ln 12) (rowL Rt 5 5) r := by
    intro hnd
    obtain ⟨g, h1, h2⟩ := Finset.not_disjoint_iff.mp hnd
    exact qq_and ⟨gates, 0⟩ hg _ _ _ factQ5 _
      (shared_c gates hg 5 5 8 factS5 g ((hKm 5 g).mp h1) (hz12 g h2))
  by_cases h3 : Disjoint (K 3) (K 12)
  · by_cases h5 : Disjoint (K 5) (K 12)
    · obtain ⟨U, hUc, hUo⟩ := assemble gates hg K hKm hKc (K 3) (K 5) 3 3
        (Finset.Subset.refl _) h3 (hKc 3) (Finset.Subset.refl _) h5 (hKc 5)
      have h := or_and_count gates U hUo ∅ (fun g hgA => absurd hgA (Finset.notMem_empty g))
      omega
    · obtain ⟨k, hk, hop, _, _⟩ := hand5 h5
      obtain ⟨U, hUc, hUo⟩ := assemble gates hg K hKm hKc (K 3) Y5 3 2
        (Finset.Subset.refl _) h3 (hKc 3) hY5s hY5d hY5q
      have h := or_and_count gates U hUo {(⟨k, hk⟩ : Fin gates.length)} (fun g hgA => by
        rw [Finset.mem_singleton.mp hgA]
        exact hop)
      rw [Finset.card_singleton] at h
      omega
  · by_cases h5 : Disjoint (K 5) (K 12)
    · obtain ⟨k, hk, hop, _, _⟩ := hand3 h3
      obtain ⟨U, hUc, hUo⟩ := assemble gates hg K hKm hKc Y3 (K 5) 2 3
        hY3s hY3d hY3q (Finset.Subset.refl _) h5 (hKc 5)
      have h := or_and_count gates U hUo {(⟨k, hk⟩ : Fin gates.length)} (fun g hgA => by
        rw [Finset.mem_singleton.mp hgA]
        exact hop)
      rw [Finset.card_singleton] at h
      omega
    · obtain ⟨k3, hk3, hop3, hQ3, hmin3⟩ := hand3 h3
      obtain ⟨k5, hk5, hop5, hQ5, hmin5⟩ := hand5 h5
      obtain ⟨k, k', hk, hk', hne, hop, hop'⟩ := two_ands ⟨gates, 0⟩ hg k3 hk3 hop3 hQ3 hmin3
        k5 hk5 hop5 hQ5 hmin5
      obtain ⟨U, hUc, hUo⟩ := assemble gates hg K hKm hKc Y3 Y5 2 2
        hY3s hY3d hY3q hY5s hY5d hY5q
      have h := or_and_count gates U hUo {(⟨k, hk⟩ : Fin gates.length), ⟨k', hk'⟩} (fun g hgA => by
        rcases Finset.mem_insert.mp hgA with e | e
        · rw [e]
          exact hop
        · rw [Finset.mem_singleton.mp e]
          exact hop')
      rw [Finset.card_pair (fun e => hne (Fin.mk.inj e))] at h
      omega

lemma m58 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    39 ≤ gates.length := by
  intro L hL gates o hg hev
  have hLf : L = ln := funext hL
  subst hLf
  exact core gates o hg hev

end PEqualNP.Outside.L_meta_1558

theorem PEqualNP.Outside.L_meta_1558 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    39 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1558.m58
