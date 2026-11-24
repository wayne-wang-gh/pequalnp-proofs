import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1553

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


lemma or_decomp {n : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.or)
    (x : Fin n → Bool) (w : ℕ) :
    value C x w = true → ∃ q : Fin n, x q = true ∧ value C (fun v => decide (v = q)) w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · intro h
      refine ⟨⟨w, hn⟩, ?_, ?_⟩
      · have h2 := input_value C x ⟨w, hn⟩
        rw [← h2]
        exact h
      · have h2 := input_value C (fun v => decide (v = (⟨w, hn⟩ : Fin n))) ⟨w, hn⟩
        simp only [decide_true] at h2
        exact h2
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      intro h
      rw [hwk] at h
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C (w - n) hk (hC _ (List.getElem_mem hk)) x).mp h
      obtain ⟨q, hq, hq2⟩ := ih r (by omega) hv
      refine ⟨q, hq, ?_⟩
      rw [hwk]
      exact (or_value C (w - n) hk (hC _ (List.getElem_mem hk)) _).mpr ⟨r, hr, hlt, hq2⟩
    · intro h
      rw [missing_value C x w (by unfold Circuit.size; omega)] at h
      exact Bool.noConfusion h

theorem main : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)),
    1 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i → R i p ∩ S i = {p}) →
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2) →
    (∀ w : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S w))) = false) →
    (∀ (w : Fin m) (p : Fin n), p ∈ S w →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R w p))) = true) →
    ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (gates.get g).inputs.length = 2 ∧
      (∃ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false) ∧
      ∀ w ∈ (gates.get g).inputs, ∃ (i : Fin m) (p : Fin n), p ∈ S i ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R i p))) = true) → g ∈ I) → m * q ≤ I.card := by
  intro q n m S R hq hcard hint hR hno gates out hg hfalse htrue I hI
  classical
  let K : Fin m → Finset (Fin gates.length) := fun i => Finset.univ.filter fun g =>
    PEqualNP.Outside.L_meta_1553.InK gates S R i g
  have hKq : ∀ i, q ≤ (K i).card := by
    intro i
    have h := PEqualNP.Outside.L_meta_1553.family (n := n) gates hg (S i)
      (PEqualNP.Outside.L_meta_1553.rowL R i) (PEqualNP.Outside.L_meta_1553.coY S i) (out i)
      (fun p hp => ⟨htrue i p hp, hfalse i⟩)
      (fun w hw hc => by
        obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
        have e : ∀ a ∈ S i, PEqualNP.Outside.L_meta_1553.Sv ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1553.rowL R i) (PEqualNP.Outside.L_meta_1553.coY S i) a w →
            (⟨w, hw⟩ : Fin n) = a := by
          intro a ha hsa
          have h1 : PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1553.rowL R i a) ((⟨w, hw⟩ : Fin n) : ℕ) = true := hsa.1
          have h2 : PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1553.coY S i) ((⟨w, hw⟩ : Fin n) : ℕ) = false := hsa.2
          rw [PEqualNP.Outside.L_meta_1553.input_value] at h1 h2
          simp only [PEqualNP.Outside.L_meta_1553.rowL, PEqualNP.Outside.L_meta_1553.coY,
            decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h1 h2
          have h3 : (⟨w, hw⟩ : Fin n) ∈ R i a ∩ S i := Finset.mem_inter.mpr ⟨h1, h2⟩
          rw [hR i a ha] at h3
          exact Finset.mem_singleton.mp h3
        exact hne ((e p hp hs1).symm.trans (e p' hp' hs2)))
      (K i)
      (fun g hm hop hl hQ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hm, hop, hl, hQ⟩)
    have := hcard i
    omega
  have hKI : ∀ i, K i ⊆ I := by
    intro i g hgK
    obtain ⟨hm, hop, hl, hQ⟩ := (Finset.mem_filter.mp hgK).2
    refine hI g ⟨hop, hl, ⟨i, ?_⟩, fun w hw => ?_⟩
    · obtain ⟨p, _, _, _, _, hs, _⟩ := hm
      exact hs.2
    · obtain ⟨p, hp, hv⟩ := hQ w hw
      exact ⟨i, p, hp, hv⟩
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (K i) (K j) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
    have hmi := (Finset.mem_filter.mp hgi).2.1
    have hmj := (Finset.mem_filter.mp hgj).2.1
    have hyi : PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
        (PEqualNP.Outside.L_meta_1553.coY S i) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmi
      exact hs.2
    have hyj : PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
        (PEqualNP.Outside.L_meta_1553.coY S j) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmj
      exact hs.2
    by_cases hA : ∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty
    · have hB : ¬ ∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty := fun hB => hno i j hij ⟨hA, hB⟩
      exact PEqualNP.Outside.L_meta_1553.kill gates hg S R j i
        (by rw [Finset.inter_comm]; exact hint i j hij) hB _ hmj hyi
    · exact PEqualNP.Outside.L_meta_1553.kill gates hg S R i j (hint i j hij) hA _ hmi hyj
  have hsub : Finset.univ.biUnion K ⊆ I := fun g hgm => by
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hgm
    exact hKI i hgi
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at h1
  have h2 : ∑ i : Fin m, q ≤ ∑ i : Fin m, (K i).card := Finset.sum_le_sum fun i _ => hKq i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

theorem orcase : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    3 ≤ q → T0 ⊆ L i0 → T0.card = q →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
    (∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin N) (x : Fin N → Bool), ((∃ v ∈ T0, x v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    N * q ≤ gates.length := by
  intro q N L i0 T0 _ _ hcard hinter _ _ _ _ gates o hg hev
  classical
  have hg' : ∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g h => ⟨Or.inr (hg g h).1, (hg g h).2⟩
  have hfalse : ∀ t : Fin N, PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
      (fun v : Fin N => decide (v ∉ L t)) (o t) = false := by
    intro t
    have h := hev t (fun v : Fin N => decide (v ∉ L t))
      (Or.inr ⟨t, fun v hv => by simpa using hv⟩)
    have h2 : decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false := by
      simp
    rw [h2] at h
    exact h
  have htrue : ∀ (t p : Fin N), p ∈ L t → PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
      (fun v : Fin N => decide (v ∈ ({p} : Finset (Fin N)))) (o t) = true := by
    intro t p hp
    have h := hev t (fun v : Fin N => decide (v ∉ L t ∨ v = p))
      (Or.inr ⟨t, fun v hv => by
        by_contra hc
        simp [hc] at hv⟩)
    have h2 : decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, Or.inr rfl⟩
    rw [h2] at h
    obtain ⟨q, hq, hq2⟩ := PEqualNP.Outside.L_meta_1553.or_decomp ⟨gates, 0⟩
      (fun g hgm => (hg g hgm).1) (fun v : Fin N => decide (v ∉ L t ∨ v = p)) (o t) h
    simp only [decide_eq_true_eq] at hq
    rcases hq with hq | hq
    · have h3 := PEqualNP.Outside.L_meta_1553.mono ⟨gates, 0⟩ hg'
        (fun v : Fin N => decide (v = q)) (fun v : Fin N => decide (v ∉ L t))
        (fun v hv => by
          simp only [decide_eq_true_eq] at hv ⊢
          rw [hv]
          exact hq) (o t) hq2
      rw [hfalse t] at h3
      exact Bool.noConfusion h3
    · subst hq
      simpa using hq2
  have hmain := PEqualNP.Outside.L_meta_1553.main q N N L (fun _ p => {p}) (by omega)
    hcard
    (fun i j hij => (hinter i j hij).le)
    (fun i p hp => Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hp))
    (fun i j _ hc => by
      obtain ⟨⟨p, hp, v, hv⟩, _⟩ := hc
      have h1 := Finset.mem_inter.mp hv
      have h2 := Finset.mem_singleton.mp h1.1
      rw [h2] at h1
      exact (Finset.mem_sdiff.mp hp).2 h1.2)
    gates o hg' hfalse htrue Finset.univ (fun g _ => Finset.mem_univ g)
  simpa using hmain

theorem main2 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)),
    1 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i → R i p ∩ S i = {p}) →
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2) →
    (∀ w : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S w))) = false) →
    (∀ (w : Fin m) (p : Fin n), p ∈ S w →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R w p))) = true) →
    ∃ K : Fin m → Finset (Fin gates.length), (∀ i, q ≤ (K i).card) ∧
      (∀ i j, i ≠ j → Disjoint (K i) (K j)) ∧
      ∀ i, ∀ g ∈ K i, gates[(g : ℕ)].op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1553.coY S i) (n + (g : ℕ)) = false := by
  intro q n m S R hq hcard hint hR hno gates out hg hfalse htrue
  classical
  let K : Fin m → Finset (Fin gates.length) := fun i => Finset.univ.filter fun g =>
    PEqualNP.Outside.L_meta_1553.InK gates S R i g
  have hKq : ∀ i, q ≤ (K i).card := by
    intro i
    have h := PEqualNP.Outside.L_meta_1553.family (n := n) gates hg (S i)
      (PEqualNP.Outside.L_meta_1553.rowL R i) (PEqualNP.Outside.L_meta_1553.coY S i) (out i)
      (fun p hp => ⟨htrue i p hp, hfalse i⟩)
      (fun w hw hc => by
        obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
        have e : ∀ a ∈ S i, PEqualNP.Outside.L_meta_1553.Sv ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1553.rowL R i) (PEqualNP.Outside.L_meta_1553.coY S i) a w →
            (⟨w, hw⟩ : Fin n) = a := by
          intro a ha hsa
          have h1 : PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1553.rowL R i a) ((⟨w, hw⟩ : Fin n) : ℕ) = true := hsa.1
          have h2 : PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1553.coY S i) ((⟨w, hw⟩ : Fin n) : ℕ) = false := hsa.2
          rw [PEqualNP.Outside.L_meta_1553.input_value] at h1 h2
          simp only [PEqualNP.Outside.L_meta_1553.rowL, PEqualNP.Outside.L_meta_1553.coY,
            decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h1 h2
          have h3 : (⟨w, hw⟩ : Fin n) ∈ R i a ∩ S i := Finset.mem_inter.mpr ⟨h1, h2⟩
          rw [hR i a ha] at h3
          exact Finset.mem_singleton.mp h3
        exact hne ((e p hp hs1).symm.trans (e p' hp' hs2)))
      (K i)
      (fun g hm hop hl hQ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hm, hop, hl, hQ⟩)
    have := hcard i
    omega
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (K i) (K j) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
    have hmi := (Finset.mem_filter.mp hgi).2.1
    have hmj := (Finset.mem_filter.mp hgj).2.1
    have hyi : PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
        (PEqualNP.Outside.L_meta_1553.coY S i) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmi
      exact hs.2
    have hyj : PEqualNP.Outside.L_meta_1553.value ⟨gates, 0⟩
        (PEqualNP.Outside.L_meta_1553.coY S j) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmj
      exact hs.2
    by_cases hA : ∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty
    · have hB : ¬ ∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty := fun hB => hno i j hij ⟨hA, hB⟩
      exact PEqualNP.Outside.L_meta_1553.kill gates hg S R j i
        (by rw [Finset.inter_comm]; exact hint i j hij) hB _ hmj hyi
    · exact PEqualNP.Outside.L_meta_1553.kill gates hg S R i j (hint i j hij) hA _ hmi hyj
  refine ⟨K, hKq, fun i j hij => hdisj i (Finset.mem_univ i) j (Finset.mem_univ j) hij, fun i g hgK => ?_⟩
  obtain ⟨hm, hop, _, _⟩ := (Finset.mem_filter.mp hgK).2
  obtain ⟨p, _, _, _, _, hs, _⟩ := hm
  exact ⟨hop, hs.2⟩

lemma count {N m q : ℕ} (K : Fin m → Finset (Fin N)) (hq : ∀ i, q ≤ (K i).card)
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)) : m * q ≤ (Finset.univ.biUnion K).card := by
  rw [Finset.card_biUnion (fun i _ j _ hij => hd i j hij)]
  have h2 : ∑ _i : Fin m, q ≤ ∑ i : Fin m, (K i).card := Finset.sum_le_sum fun i _ => hq i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  exact h2

lemma shift {N : ℕ} (T : Finset (Fin N)) (hT : 3 ≤ T.card) :
    ∃ F : {x // x ∈ T} → {x // x ∈ T}, (∀ x, F x ≠ x) ∧ ∀ x, F (F x) ≠ x := by
  classical
  let e := T.equivFin
  have hpos : ∀ i : ℕ, i % T.card < T.card := fun i => Nat.mod_lt _ (by omega)
  let g : Fin T.card → Fin T.card := fun i => ⟨((i : ℕ) + 1) % T.card, hpos _⟩
  have hg1 : ∀ i, g i ≠ i := by
    intro i h
    have h1 : ((i : ℕ) + 1) % T.card = i := congrArg Fin.val h
    have hi := i.isLt
    rcases Nat.lt_or_ge ((i : ℕ) + 1) T.card with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h1
      omega
    · have h3 : (i : ℕ) + 1 = T.card := by omega
      rw [h3, Nat.mod_self] at h1
      omega
  have hg2 : ∀ i, g (g i) ≠ i := by
    intro i h
    have h1 : ((((i : ℕ) + 1) % T.card) + 1) % T.card = i := congrArg Fin.val h
    have hi := i.isLt
    rcases Nat.lt_or_ge ((i : ℕ) + 1) T.card with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h1
      rcases Nat.lt_or_ge ((i : ℕ) + 1 + 1) T.card with h4 | h4
      · rw [Nat.mod_eq_of_lt h4] at h1
        omega
      · have h3 : (i : ℕ) + 1 + 1 = T.card := by omega
        rw [h3, Nat.mod_self] at h1
        omega
    · have h3 : (i : ℕ) + 1 = T.card := by omega
      have h5 : (0 + 1) % T.card = 0 + 1 := Nat.mod_eq_of_lt (by omega)
      rw [h3, Nat.mod_self, h5] at h1
      omega
  refine ⟨fun x => e.symm (g (e x)), fun x h => ?_, fun x h => ?_⟩
  · have h2 : e (e.symm (g (e x))) = e x := congrArg e h
    rw [e.apply_symm_apply] at h2
    exact hg1 (e x) h2
  · have h2 : e (e.symm (g (e (e.symm (g (e x)))))) = e x := congrArg e h
    rw [e.apply_symm_apply, e.apply_symm_apply] at h2
    exact hg2 (e x) h2

lemma cex {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (hT : T0 ⊆ L i0) (h3 : 3 ≤ T0.card) :
    ∃ c : Fin N → Fin N, (∀ s, s ≠ i0 → c s ∈ T0 ∧ c s ∉ L s) ∧
      ∀ s s', s ≠ i0 → s' ≠ i0 → c s ∈ L s' → c s' ∈ L s → False := by
  classical
  obtain ⟨F, hF1, hF2⟩ := shift T0 h3
  have hne : T0.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a0, ha0⟩ := hne
  have uniq : ∀ s, s ≠ i0 → ∀ a b, a ∈ T0 → b ∈ T0 → a ∈ L s → b ∈ L s → a = b := by
    intro s hs a b ha hb has hbs
    exact Finset.card_le_one.mp (hinter s i0 hs).le a (Finset.mem_inter.mpr ⟨has, hT ha⟩) b
      (Finset.mem_inter.mpr ⟨hbs, hT hb⟩)
  let c : Fin N → Fin N := fun s =>
    if h : ∃ x : {x // x ∈ T0}, x.1 ∈ L s then (F (Classical.choose h)).1 else a0
  have key : ∀ s, s ≠ i0 → ∀ x : {x // x ∈ T0}, x.1 ∈ L s → c s = (F x).1 := by
    intro s hs x hx
    have h : ∃ x : {x // x ∈ T0}, x.1 ∈ L s := ⟨x, hx⟩
    have e1 : c s = (F (Classical.choose h)).1 := dite_eq_left h
    have e2 : Classical.choose h = x :=
      Subtype.ext (uniq s hs _ _ (Classical.choose h).2 x.2 (Classical.choose_spec h) hx)
    rw [e1, e2]
  have hcT : ∀ s, c s ∈ T0 := by
    intro s
    by_cases h : ∃ x : {x // x ∈ T0}, x.1 ∈ L s
    · have e1 : c s = (F (Classical.choose h)).1 := dite_eq_left h
      rw [e1]
      exact (F (Classical.choose h)).2
    · have e1 : c s = a0 := dite_eq_right h
      rw [e1]
      exact ha0
  refine ⟨c, fun s hs => ⟨hcT s, fun hin => ?_⟩, fun s s' hs hs' h1 h2 => ?_⟩
  · have e1 := key s hs ⟨c s, hcT s⟩ hin
    exact hF1 ⟨c s, hcT s⟩ (Subtype.ext e1.symm)
  · have e1 : c s' = (F ⟨c s, hcT s⟩).1 := key s' hs' ⟨c s, hcT s⟩ h1
    have h2' : (F ⟨c s, hcT s⟩).1 ∈ L s := by
      rw [← e1]
      exact h2
    have e2 := key s hs (F ⟨c s, hcT s⟩) h2'
    exact hF2 ⟨c s, hcT s⟩ (Subtype.ext e2.symm)

theorem andcase (q n : ℕ) (L : Fin (n + 1) → Finset (Fin (n + 1))) (i0 : Fin (n + 1))
    (T0 : Finset (Fin (n + 1)))
    (hcard : ∀ i, (L i).card = q + 1) (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hq : 3 ≤ q) (hT : T0 ⊆ L i0) (hTc : T0.card = q)
    (gates : List Gate) (o : Fin (n + 1) → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hev : ∀ (t : Fin (n + 1)) (x : Fin (n + 1) → Bool), ((∃ v ∈ T0, x v = true) ∨
      ∃ s : Fin (n + 1), ∀ v : Fin (n + 1), x v = false → v ∈ L s) →
      value ⟨gates, 0⟩ x (o t) = decide (∃ v ∈ L t, x v = true))
    (m : Fin gates.length) (hm : gates[(m : ℕ)].op = GateOp.and) :
    (n + 1) * q ≤ gates.length := by
  classical
  obtain ⟨c, hc1, hc2⟩ := cex L i0 T0 hinter hT (by omega)
  have hfalse : ∀ t : Fin (n + 1), value ⟨gates, 0⟩ (fun v : Fin (n + 1) => decide (v ∉ L t)) (o t) = false := by
    intro t
    have h := hev t (fun v : Fin (n + 1) => decide (v ∉ L t))
      (Or.inr ⟨t, fun v hv => by simpa using hv⟩)
    have h2 : decide (∃ v ∈ L t, (fun v : Fin (n + 1) => decide (v ∉ L t)) v = true) = false := by
      simp
    rw [h2] at h
    exact h
  let R : Fin n → Fin (n + 1) → Finset (Fin (n + 1)) := fun i p =>
    if p ∈ T0 then {p} else {p, c (i0.succAbove i)}
  have hsne : ∀ i : Fin n, i0.succAbove i ≠ i0 := fun i => Fin.succAbove_ne i0 i
  have hRmem : ∀ i p v, v ∈ R i p → v = p ∨ (p ∉ T0 ∧ v = c (i0.succAbove i)) := by
    intro i p v hv
    by_cases hp : p ∈ T0
    · have e : R i p = {p} := ite_eq_left hp
      rw [e] at hv
      exact Or.inl (Finset.mem_singleton.mp hv)
    · have e : R i p = {p, c (i0.succAbove i)} := ite_eq_right hp
      rw [e] at hv
      rcases Finset.mem_insert.mp hv with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hp, Finset.mem_singleton.mp h⟩
  have hRp : ∀ i p, p ∈ R i p := by
    intro i p
    by_cases hp : p ∈ T0
    · have e : R i p = {p} := ite_eq_left hp
      rw [e]
      exact Finset.mem_singleton_self p
    · have e : R i p = {p, c (i0.succAbove i)} := ite_eq_right hp
      rw [e]
      exact Finset.mem_insert_self _ _
  have hRT : ∀ i p, ∃ v ∈ T0, v ∈ R i p := by
    intro i p
    by_cases hp : p ∈ T0
    · exact ⟨p, hp, hRp i p⟩
    · have e : R i p = {p, c (i0.succAbove i)} := ite_eq_right hp
      refine ⟨c (i0.succAbove i), (hc1 _ (hsne i)).1, ?_⟩
      rw [e]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hpoint : ∀ i j : Fin n, (∃ p ∈ L (i0.succAbove i) \ L (i0.succAbove j),
      (R i p ∩ L (i0.succAbove j)).Nonempty) → c (i0.succAbove i) ∈ L (i0.succAbove j) := by
    rintro i j ⟨p, hp, v, hv⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
    rcases hRmem i p v h1 with h | ⟨_, h⟩
    · rw [h] at h2
      exact absurd h2 (Finset.mem_sdiff.mp hp).2
    · rw [h] at h2
      exact h2
  obtain ⟨K, hKq, hKd, hKp⟩ := main2 q (n + 1) n (fun i => L (i0.succAbove i)) R (by omega)
    (fun i => hcard _)
    (fun i j hij => (hinter _ _ (fun h => hij (Fin.succAbove_right_injective h))).le)
    (fun i p hp => by
      ext v
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        rcases hRmem i p v h1 with h | ⟨_, h⟩
        · exact h
        · rw [h] at h2
          exact absurd h2 (hc1 _ (hsne i)).2
      · rintro rfl
        exact ⟨hRp i v, hp⟩)
    (fun i j _ hc => hc2 _ _ (hsne i) (hsne j) (hpoint i j hc.1) (hpoint j i hc.2))
    gates (fun i => o (i0.succAbove i)) hg (fun i => hfalse _)
    (fun i p hp => by
      obtain ⟨v, hv, hvR⟩ := hRT i p
      have h := hev (i0.succAbove i) (fun v => decide (v ∈ R i p))
        (Or.inl ⟨v, hv, decide_eq_true hvR⟩)
      have h2 : decide (∃ v ∈ L (i0.succAbove i), (fun v => decide (v ∈ R i p)) v = true) = true :=
        decide_eq_true ⟨p, hp, decide_eq_true (hRp i p)⟩
      rw [h2] at h
      exact h)
  let y : Fin (n + 1) → Bool := fun v => decide (v ∉ L i0)
  let l : Fin (n + 1) → Fin (n + 1) → Bool := fun a v => decide (v = a)
  let K0 : Finset (Fin gates.length) := Finset.univ.filter fun g =>
    Multi ⟨gates, 0⟩ T0 l y (n + 1 + (g : ℕ)) ∧ gates[(g : ℕ)].op = GateOp.or
  have h0 := family (n := n + 1) gates hg T0 l y (o i0)
    (fun a ha => ⟨by
        have h := hev i0 (l a) (Or.inl ⟨a, ha, decide_eq_true rfl⟩)
        have h2 : decide (∃ v ∈ L i0, l a v = true) = true :=
          decide_eq_true ⟨a, hT ha, decide_eq_true rfl⟩
        rw [h2] at h
        exact h, hfalse i0⟩)
    (fun w hw hc => by
      obtain ⟨p, _, p', _, hne, hs1, hs2⟩ := hc
      have e1 : l p ⟨w, hw⟩ = true := (input_value ⟨gates, 0⟩ (l p) ⟨w, hw⟩).symm.trans hs1.1
      have e2 : l p' ⟨w, hw⟩ = true := (input_value ⟨gates, 0⟩ (l p') ⟨w, hw⟩).symm.trans hs2.1
      exact hne ((of_decide_eq_true e1).symm.trans (of_decide_eq_true e2)))
    K0 (fun g hmu hop _ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hmu, hop⟩)
  let U : Finset (Fin gates.length) := Finset.univ.biUnion K
  have hU : n * q ≤ U.card := count K hKq hKd
  have hd0 : Disjoint K0 U := by
    refine Finset.disjoint_left.mpr fun g hg0 hgU => ?_
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hgU
    have h1 := (hKp i g hi).2
    obtain ⟨⟨a, ha, b, hb, hab, hsa, hsb⟩, _⟩ := (Finset.mem_filter.mp hg0).2
    have hnot : a ∉ L (i0.succAbove i) ∨ b ∉ L (i0.succAbove i) := by
      by_contra hcon
      have hca : a ∈ L (i0.succAbove i) := by
        by_contra h
        exact hcon (Or.inl h)
      have hcb : b ∈ L (i0.succAbove i) := by
        by_contra h
        exact hcon (Or.inr h)
      exact hab (Finset.card_le_one.mp (hinter _ i0 (hsne i)).le a
        (Finset.mem_inter.mpr ⟨hca, hT ha⟩) b (Finset.mem_inter.mpr ⟨hcb, hT hb⟩))
    have h2 : value ⟨gates, 0⟩ (coY (fun i => L (i0.succAbove i)) i) (n + 1 + (g : ℕ)) = true := by
      rcases hnot with hn | hn
      · exact mono ⟨gates, 0⟩ hg (l a) _ (fun v hv => by
          have hva : v = a := of_decide_eq_true hv
          rw [hva]
          exact decide_eq_true hn) _ hsa.1
      · exact mono ⟨gates, 0⟩ hg (l b) _ (fun v hv => by
          have hvb : v = b := of_decide_eq_true hv
          rw [hvb]
          exact decide_eq_true hn) _ hsb.1
    exact Bool.noConfusion (h1.symm.trans h2)
  have hmU : m ∉ U := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hmem
    have h1 := (hKp i _ hi).1
    cases h1.symm.trans hm
  have hm0 : m ∉ K0 := by
    intro hmem
    have h1 := (Finset.mem_filter.mp hmem).2.2
    cases h1.symm.trans hm
  have c1 : (K0 ∪ U).card = K0.card + U.card := Finset.card_union_of_disjoint hd0
  have c2 : (insert m (K0 ∪ U)).card = (K0 ∪ U).card + 1 :=
    Finset.card_insert_of_notMem (fun h => (Finset.mem_union.mp h).elim hm0 hmU)
  have hle := Finset.card_le_univ (insert m (K0 ∪ U))
  rw [Fintype.card_fin] at hle
  have e : (n + 1) * q = n * q + q := by ring
  omega

lemma core : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    3 ≤ q → T0 ⊆ L i0 → T0.card = q →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin N) (x : Fin N → Bool), ((∃ v ∈ T0, x v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    N * q ≤ gates.length := by
  intro q N L i0 T0 h2 hN hcard hinter hpts hq hT hTc gates o hg hev
  classical
  by_cases hA : ∃ m : Fin gates.length, gates[(m : ℕ)].op = PEqualNP.CircuitLowerBounds.GateOp.and
  · obtain ⟨m, hm⟩ := hA
    rcases N with _ | n
    · exact i0.elim0
    · exact PEqualNP.Outside.L_meta_1553.andcase q n L i0 T0 hcard hinter hq hT hTc gates o hg hev m hm
  · refine PEqualNP.Outside.L_meta_1553.orcase q N L i0 T0 h2 hN hcard hinter hpts hq hT hTc gates o
      (fun g hgm => ⟨?_, (hg g hgm).2⟩) hev
    rcases (hg g hgm).1 with h | h
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hgm
      exact absurd ⟨⟨i, hi⟩, h⟩ hA
    · exact h

def brun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma bruncons (g : Gate) (gs : List Gate) (x : List Bool) :
    brun (g :: gs) x = brun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma brunlength (gs : List Gate) (x : List Bool) :
    (brun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [brun]
  | cons g gs ih => rw [bruncons, ih]; simp; omega

lemma brungetD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (brun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [bruncons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma brunsplit (gs : List Gate) (x : List Bool) (j : ℕ) :
    brun gs x = brun (gs.drop j) (brun (gs.take j) x) := by
  simpa only [brun, List.foldl_append] using
    congrArg (fun l : List Gate => brun l x) (List.take_append_drop j gs).symm

def bvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma binputvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    bvalue C x p = x p := by
  change (brun C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [brungetD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma bmissingvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : bvalue C x w = false := by
  change (brun C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [brunlength, Circuit.size] using hw)

lemma bgatevalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    bvalue C x w = g.op.eval (g.inputs.map fun r => if r < w then bvalue C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := brun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, brunlength, Nat.min_eq_left hj.le, j]; omega
  have split : brun C.gates (List.ofFn x) = brun (g :: C.gates.drop (j + 1)) earlier := by
    rw [brunsplit C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then bvalue C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (brun C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (brungetD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (brun C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then bvalue C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [bruncons]
  rw [brungetD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma bgatemono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → bvalue C x r = true → bvalue C y r = true) :
    bvalue C x (n + k) = true → bvalue C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := bgatevalue C x (n + k) (by omega) hw
  have hy := bgatevalue C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then bvalue C x r else false) = true →
      (if r < n + k then bvalue C y r else false) = true := by
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

lemma borvalue {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    bvalue C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ bvalue C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := bgatevalue C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma bandvalue {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    bvalue C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ bvalue C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := bgatevalue C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma bmono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    bvalue C x w = true → bvalue C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change bvalue C x p = true → bvalue C y p = true
      simpa only [binputvalue] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact bgatemono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [bmissingvalue C x w (by unfold Circuit.size; omega)]

lemma hmono (N : ℕ) (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) (hw : w < N + (j : ℕ)) :
    bvalue ⟨gates, 0⟩ x w = true → bvalue ⟨gates, 0⟩ y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < N
    · let p : Fin N := ⟨w, hn⟩
      change bvalue ⟨gates, 0⟩ x p = true → bvalue ⟨gates, 0⟩ y p = true
      simpa only [binputvalue] using hxy p
    · have hk : w - N < gates.length := by
        have := j.isLt
        omega
      have hwk : w = N + (w - N) := by omega
      rw [hwk]
      have hop : gates[w - N].op = GateOp.and ∨ gates[w - N].op = GateOp.or := by
        rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have h1 := hone ⟨w - N, hk⟩ h
          have h2 : w - N = (j : ℕ) := congrArg Fin.val h1
          omega
      exact bgatemono (n := N) ⟨gates, 0⟩ (w - N) hk hop x y fun r _ hlt => ih r (by omega) (by omega)

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma druncons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma drunappend (A B : List Gate) (x : List Bool) : drun (A ++ B) x = drun B (drun A x) := by
  simp [drun, List.foldl_append]

lemma drunlength (gs : List Gate) (x : List Bool) :
    (drun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [drun]
  | cons g gs ih => rw [druncons, ih]; simp; omega

lemma drungetD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (drun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [druncons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma drunsplit (gs : List Gate) (x : List Bool) (j : ℕ) :
    drun gs x = drun (gs.drop j) (drun (gs.take j) x) := by
  simpa only [drun, List.foldl_append] using
    congrArg (fun l : List Gate => drun l x) (List.take_append_drop j gs).symm

def dvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma dmissingvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : dvalue C x w = false := by
  change (drun C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [drunlength, Circuit.size] using hw)

lemma dgatevalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    dvalue C x w = g.op.eval (g.inputs.map fun r => if r < w then dvalue C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := drun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, drunlength, Nat.min_eq_left hj.le, j]; omega
  have split : drun C.gates (List.ofFn x) = drun (g :: C.gates.drop (j + 1)) earlier := by
    rw [drunsplit C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then dvalue C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (drun C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (drungetD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (drun C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then dvalue C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [druncons]
  rw [drungetD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma dgatevalueP {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    dvalue ⟨gs, 0⟩ x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then dvalue ⟨gs, 0⟩ x r else false) := by
  have h := dgatevalue ⟨gs, 0⟩ x (n + k) (by omega) (by change n + k < n + gs.length; omega)
  simpa only [Nat.add_sub_cancel_left] using h

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma eval_ao (op : GateOp) (l : List Bool) (h : op = GateOp.and ∨ op = GateOp.or) :
    op.eval l = if isOr op ∈ l then isOr op else !isOr op := by
  rcases h with rfl | rfl
  · simp only [GateOp.eval, isOr]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all
  · simp only [GateOp.eval, isOr]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all

def fin3 (a : Bool) (op : GateOp) (N : ℕ) : List ℕ → (Bool ⊕ ℕ) × List Gate
  | [] => (Sum.inl (!a), [])
  | [w] => (Sum.inr w, [])
  | w :: w2 :: t => (Sum.inr N, [⟨op, w :: w2 :: t⟩])

def gen (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (Bool ⊕ ℕ) × List Gate :=
  if Sum.inl (isOr g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) then
    (Sum.inl (isOr g.op), [])
  else fin3 (isOr g.op) g.op N
    ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?)

def stp (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  if k < h then (s.1 ++ [Sum.inr (n + s.2.length)], s.2 ++ [g])
  else if k = h then (s.1 ++ [Sum.inl true], s.2)
  else if isNot g.op = true then (s.1 ++ [Sum.inl false], s.2)
  else (s.1 ++ [(gen s.1 (n + s.2.length) g).1], s.2 ++ (gen s.1 (n + s.2.length) g).2)

def S (n h : ℕ) (gs : List Gate) : ℕ → List (Bool ⊕ ℕ) × List Gate
  | 0 => ((List.range n).map Sum.inr, [])
  | k + 1 => match gs[k]? with
    | none => S n h gs k
    | some g => stp n h k g (S n h gs k)

lemma S_succ (n h : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    S n h gs (k + 1) = stp n h k gs[k] (S n h gs k) := by
  rw [S]
  simp [hk]

lemma fin3_len (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) : (fin3 a op N l).2.length ≤ 1 := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩ <;> simp [fin3]

lemma fin3_mem (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) :
    ∀ g' ∈ (fin3 a op N l).2, g'.op = op ∧ g'.inputs = l := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩ <;> simp [fin3]

lemma fin3_short (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) (h : l.length ≤ 1) :
    (fin3 a op N l).2 = [] := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
  · rfl
  · rfl
  · simp at h

lemma gen_len (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (gen ρ N g).2.length ≤ 1 := by
  unfold gen
  split_ifs
  · simp
  · exact fin3_len _ _ _ _

lemma gen_mem (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) :
    ∀ g' ∈ (gen ρ N g).2, g'.op = g.op ∧ g'.inputs.length ≤ g.inputs.length := by
  unfold gen
  split_ifs
  · simp
  · intro g' hg'
    obtain ⟨h1, h2⟩ := fin3_mem _ _ _ _ g' hg'
    refine ⟨h1, ?_⟩
    rw [h2]
    exact (List.length_filterMap_le _ _).trans (by simp)

lemma filterMap_lt (l : List (Bool ⊕ ℕ)) (b : Bool) (h : Sum.inl b ∈ l) :
    (l.filterMap Sum.getRight?).length + 1 ≤ l.length := by
  induction l with
  | nil => simp at h
  | cons c t ih =>
    rcases List.mem_cons.mp h with h | h
    · subst h
      have := List.length_filterMap_le Sum.getRight? t
      change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
      omega
    · have := ih h
      rcases c with c | c
      · change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
        omega
      · change (t.filterMap Sum.getRight?).length + 1 + 1 ≤ t.length + 1
        omega

lemma gen_reader (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2)
    (r : ℕ) (hr : r ∈ g.inputs) (hρ : ρ.getD r (Sum.inl false) = Sum.inl false) :
    (gen ρ N g).2 = [] := by
  unfold gen
  split_ifs
  · rfl
  · apply fin3_short
    have hm : Sum.inl false ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) :=
      List.mem_map.mpr ⟨r, hr, hρ⟩
    have := filterMap_lt _ false hm
    simp only [List.length_map] at this
    omega

lemma stp_fst (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    ∃ d, (stp n h k g s).1 = s.1 ++ [d] := by
  unfold stp
  split_ifs <;> exact ⟨_, rfl⟩

lemma stp_snd (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    ∃ e, (stp n h k g s).2 = s.2 ++ e ∧ e.length ≤ 1 := by
  unfold stp
  split_ifs
  · exact ⟨[g], rfl, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨_, rfl, gen_len _ _ _⟩

lemma S_len (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → (S n h gs k).1.length = n + k := by
  intro k
  induction k with
  | zero => intro _; simp [S]
  | succ k ih =>
    intro hk
    rw [S_succ n h gs k (by omega)]
    obtain ⟨d, hd⟩ := stp_fst n h k gs[k] (S n h gs k)
    rw [hd, List.length_append, ih (by omega)]
    simp
    omega

lemma S_low (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → k ≤ h →
    (S n h gs k).2 = gs.take k ∧ (S n h gs k).1 = (List.range (n + k)).map Sum.inr := by
  intro k
  induction k with
  | zero => intro _ _; simp [S]
  | succ k ih =>
    intro hk hkh
    obtain ⟨h1, h2⟩ := ih (by omega) (by omega)
    rw [S_succ n h gs k (by omega)]
    have hlt : k < h := by omega
    unfold stp
    simp only [hlt, ↓reduceIte]
    rw [h1, h2]
    refine ⟨(List.take_succ_eq_append_getElem (by omega)).symm, ?_⟩
    have : (List.take k gs).length = k := by simp; omega
    rw [this, ← Nat.add_assoc, List.range_succ, List.map_append]
    rfl

lemma S_prefix (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → h ≤ k →
    gs.take h <+: (S n h gs k).2 := by
  intro k
  induction k with
  | zero =>
    intro _ hh
    have : h = 0 := by omega
    subst this
    simp
  | succ k ih =>
    intro hk hh
    by_cases he : h = k + 1
    · rw [he, (S_low n (k + 1) gs (k + 1) hk le_rfl).1]
    · rw [S_succ n h gs k (by omega)]
      obtain ⟨e, he2, _⟩ := stp_snd n h k gs[k] (S n h gs k)
      rw [he2]
      exact (ih (by omega) (by omega)).trans (List.prefix_append _ _)

lemma S_ops (n h j : ℕ) (gs : List Gate) (hhj : h < j)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j) :
    ∀ k, k ≤ gs.length → ∀ g' ∈ (S n h gs k).2,
      (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro _ g' hg'; simp [S] at hg'
  | succ k ih =>
    intro hk g' hg'
    have hkl : k < gs.length := by omega
    rw [S_succ n h gs k hkl] at hg'
    have hg := hops gs[k] (List.getElem_mem hkl)
    unfold stp at hg'
    split_ifs at hg' with h1 h2 h3
    · rcases List.mem_append.mp hg' with hm | hm
      · exact ih (by omega) g' hm
      · rw [List.mem_singleton.mp hm]
        refine ⟨?_, hg.2⟩
        rcases hg.1 with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · have := huniq k hkl ho
          omega
    · exact ih (by omega) g' hg'
    · exact ih (by omega) g' hg'
    · rcases List.mem_append.mp hg' with hm | hm
      · exact ih (by omega) g' hm
      · obtain ⟨e1, e2⟩ := gen_mem _ _ _ g' hm
        refine ⟨?_, e2.trans hg.2⟩
        rw [e1]
        rcases hg.1 with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · rw [ho] at h3
          exact absurd rfl h3

lemma S_j (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) :
    ∀ k, k ≤ gs.length → j < k → (S n h gs k).1.getD (n + j) (Sum.inl false) = Sum.inl false := by
  intro k
  induction k with
  | zero => intro _ h0; omega
  | succ k ih =>
    intro hk hjk
    have hkl : k < gs.length := by omega
    have hl := S_len n h gs k (by omega)
    by_cases he : k = j
    · subst he
      rw [S_succ n h gs k hkl]
      unfold stp
      have h1 : ¬ k < h := by omega
      have h2 : ¬ k = h := by omega
      have h3 : isNot gs[k].op = true := by rw [hjn]; rfl
      simp only [h1, h2, h3, ↓reduceIte]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hl]
    · rw [S_succ n h gs k hkl]
      obtain ⟨d, hd⟩ := stp_fst n h k gs[k] (S n h gs k)
      rw [hd, List.getD_append _ _ _ _ (by omega)]
      exact ih (by omega) (by omega)

def bad (n h j : ℕ) (gs : List Gate) (i : ℕ) : Bool :=
  decide (i = h ∨ i = j ∨ (j < i ∧ n + j ∈ (gs.getD i ⟨GateOp.and, []⟩).inputs))

lemma S_bad (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gs.length) (hb : bad n h j gs k = true) :
    (S n h gs (k + 1)).2 = (S n h gs k).2 := by
  rw [S_succ n h gs k hk]
  unfold bad at hb
  simp only [decide_eq_true_eq] at hb
  unfold stp
  rcases hb with hb | hb | ⟨hb1, hb2⟩
  · subst hb
    simp only [lt_irrefl, ↓reduceIte]
  · have h1 : ¬ k < h := by omega
    have h2 : ¬ k = h := by omega
    have h3 : isNot gs[k].op = true := by subst hb; rw [hjn]; rfl
    simp only [h1, h2, h3, ↓reduceIte]
  · have h1 : ¬ k < h := by omega
    have h2 : ¬ k = h := by omega
    simp only [h1, h2, ↓reduceIte]
    split_ifs
    · rfl
    · rw [List.getD_eq_getElem _ _ hk] at hb2
      rw [gen_reader _ _ gs[k] (hlen _ (List.getElem_mem hk)) (n + j) hb2
        (S_j n h j gs hhj hj hjn k (by omega) hb1)]
      simp

lemma S_count (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ k, k ≤ gs.length →
      (S n h gs k).2.length + ((Finset.range k).filter (fun i => bad n h j gs i = true)).card ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp [S]
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hb : bad n h j gs k = true
    · rw [S_bad n h j gs hhj hj hjn hlen k hkl hb]
      simp only [hb, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · simp only [hb]
      rw [S_succ n h gs k hkl]
      obtain ⟨e, he, hel⟩ := stp_snd n h k gs[k] (S n h gs k)
      rw [he, List.length_append]
      have : (false = true) = False := by simp
      simp only [this, ↓reduceIte]
      omega

def Rp (W' : List Bool) (v : Bool) : Bool ⊕ ℕ → Prop
  | Sum.inl b => v = b
  | Sum.inr w => w < W'.length ∧ W'.getD w false = v

lemma Rp_mono (W' : List Bool) (e : List Gate) (v : Bool) (r : Bool ⊕ ℕ) (hr : Rp W' v r) :
    Rp (drun e W') v r := by
  rcases r with b | w
  · exact hr
  · exact ⟨by rw [drunlength]; exact Nat.lt_add_right _ hr.1, by rw [drungetD _ _ _ hr.1]; exact hr.2⟩

lemma ext (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (e : List Gate) (d : Bool ⊕ ℕ) (V : ℕ → Bool)
    (N : ℕ) (hlen : ρ.length = N)
    (ih : ∀ i, Rp W' (if i < N then V i else false) (ρ.getD i (Sum.inl false)))
    (hd : Rp (drun e W') (V N) d) (i : ℕ) :
    Rp (drun e W') (if i < N + 1 then V i else false) ((ρ ++ [d]).getD i (Sum.inl false)) := by
  rcases lt_trichotomy i N with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by omega)]
    have := Rp_mono W' e _ _ (ih i)
    have h1 : i < N + 1 := by omega
    simpa only [hi, h1, ↓reduceIte] using this
  · subst hi
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simpa [hlen] using hd
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    have h1 : ¬ i < N + 1 := by omega
    simp only [h1, ↓reduceIte]
    exact rfl

lemma gen_sem (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (vals : ℕ → Bool)
    (hr : ∀ r ∈ g.inputs, Rp W' (vals r) (ρ.getD r (Sum.inl false))) :
    Rp (drun (gen ρ W'.length g).2 W') (g.op.eval (g.inputs.map vals)) (gen ρ W'.length g).1 := by
  rw [eval_ao g.op _ hop]
  unfold gen
  by_cases hin : Sum.inl (isOr g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false))
  · simp only [hin, ↓reduceIte]
    obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hin
    have h1 := hr r hrm
    rw [hre] at h1
    have h2 : vals r = isOr g.op := h1
    have hmem : isOr g.op ∈ g.inputs.map vals := List.mem_map.mpr ⟨r, hrm, h2⟩
    simp only [hmem, ↓reduceIte]
    exact rfl
  · simp only [hin, ↓reduceIte]
    have key1 : ∀ w ∈ (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?,
        w < W'.length ∧ ∃ r ∈ g.inputs, W'.getD w false = vals r := by
      intro w hw
      obtain ⟨c, hc, hcw⟩ := List.mem_filterMap.mp hw
      obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hc
      have hc' : c = Sum.inr w := Sum.getRight?_eq_some_iff.mp hcw
      have h1 := hr r hrm
      rw [hre, hc'] at h1
      exact ⟨h1.1, r, hrm, h1.2⟩
    have key2 : isOr g.op ∈ g.inputs.map vals ↔ isOr g.op ∈
        ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?).map
          (fun w => W'.getD w false) := by
      constructor
      · intro hm
        obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hm
        have h1 := hr r hrm
        rcases hc : ρ.getD r (Sum.inl false) with b | w
        · rw [hc] at h1
          have h2 : vals r = b := h1
          exact absurd (List.mem_map.mpr ⟨r, hrm, by rw [hc, ← h2, hre]⟩) hin
        · rw [hc] at h1
          refine List.mem_map.mpr ⟨w, List.mem_filterMap.mpr ⟨Sum.inr w, List.mem_map.mpr ⟨r, hrm, hc⟩, rfl⟩, ?_⟩
          rw [h1.2, hre]
      · intro hm
        obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
        obtain ⟨_, r, hrm, hre⟩ := key1 w hw
        exact List.mem_map.mpr ⟨r, hrm, by rw [← hre, hwe]⟩
    simp only [key2]
    generalize (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight? = l at key1
    rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
    · simp [fin3, Rp]
    · have hw := (key1 w (by simp)).1
      refine ⟨hw, ?_⟩
      change W'.getD w false = _
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      generalize W'.getD w false = c
      cases isOr g.op <;> cases c <;> simp
    · refine ⟨by simp [fin3, drun], ?_⟩
      simp only [fin3, drun, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact eval_ao g.op _ hop

lemma sem (n h j : ℕ) (gs : List Gate) (x : Fin n → Bool)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j)
    (hh : dvalue ⟨gs, 0⟩ x (n + h) = true) (hjv : dvalue ⟨gs, 0⟩ x (n + j) = false) :
    ∀ k, k ≤ gs.length → ∀ i, Rp (drun (S n h gs k).2 (List.ofFn x))
      (if i < n + k then dvalue ⟨gs, 0⟩ x i else false)
      ((S n h gs k).1.getD i (Sum.inl false)) := by
  intro k
  induction k with
  | zero =>
    intro _ i
    change Rp (List.ofFn x) (if i < n + 0 then dvalue ⟨gs, 0⟩ x i else false)
      (((List.range n).map Sum.inr).getD i (Sum.inl false))
    by_cases hi : i < n
    · have e1 : ((List.range n).map (Sum.inr : ℕ → Bool ⊕ ℕ)).getD i (Sum.inl false) = Sum.inr i := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi)]
        simp
      rw [e1]
      simp only [Nat.add_zero, hi, ↓reduceIte]
      refine ⟨by simpa using hi, ?_⟩
      exact (drungetD gs _ i (by simpa using hi)).symm
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [Nat.add_zero, hi, ↓reduceIte]
      exact rfl
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    have hl := S_len n h gs k (by omega)
    have hWl : (drun (S n h gs k).2 (List.ofFn x)).length = n + (S n h gs k).2.length := by
      rw [drunlength]; simp
    have hgv := dgatevalueP gs x k hkl
    rw [S_succ n h gs k hkl]
    unfold stp
    split_ifs with h1 h2 h3
    · simp only [drunappend, ← Nat.add_assoc]
      apply ext _ _ _ _ (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
      obtain ⟨l1, l2⟩ := S_low n h gs k (by omega) (by omega)
      have hk2 : (S n h gs k).2.length = k := by rw [l1]; simp; omega
      refine ⟨by rw [drunlength, hWl]; simp, ?_⟩
      change ((drun (S n h gs k).2 (List.ofFn x)) ++ [_]).getD _ false = _
      rw [List.getD_append_right _ _ _ _ (by omega), hWl, Nat.sub_self, List.getD_cons_zero, hgv]
      congr 1
      apply List.map_congr_left
      intro r _
      by_cases hr : r < n + k
      · have h4 := ih' r
        have e1 : (S n h gs k).1.getD r (Sum.inl false) = Sum.inr r := by
          rw [l2, List.getD_eq_getElem _ _ (by simpa using hr)]
          simp
        rw [e1] at h4
        simp only [hr, ↓reduceIte] at h4 ⊢
        exact h4.2
      · simp only [hr, ↓reduceIte]
        exact List.getD_eq_default _ _ (by omega)
    · simp only [← Nat.add_assoc]
      have := ext _ _ [] (Sum.inl true) (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
        (by subst h2; exact hh)
      exact this
    · simp only [← Nat.add_assoc]
      have hkj : k = j := by
        apply huniq k hkl
        rcases hops gs[k] (List.getElem_mem hkl) with ho | ho | ho
        · rw [ho] at h3; exact absurd h3 (by simp [isNot])
        · rw [ho] at h3; exact absurd h3 (by simp [isNot])
        · exact ho
      have := ext _ _ [] (Sum.inl false) (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
        (by subst hkj; exact hjv)
      exact this
    · simp only [drunappend, ← Nat.add_assoc]
      apply ext _ _ _ _ (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
      have hop : gs[k].op = GateOp.and ∨ gs[k].op = GateOp.or := by
        rcases hops gs[k] (List.getElem_mem hkl) with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · rw [ho] at h3; exact absurd rfl h3
      change Rp _ (dvalue ⟨gs, 0⟩ x (n + k)) _
      rw [hgv, ← hWl]
      exact gen_sem _ _ gs[k] hop _ (fun r _ => ih' r)

lemma dmain : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) := by
  intro n m gates out j h hops hj huniq hhj hin hsep
  have hjl : (j : ℕ) < gates.length := j.2
  have hhj' : (h : ℕ) < (j : ℕ) := hhj
  have hjn : gates[(j : ℕ)].op = GateOp.not := hj
  have huniq' : ∀ i (hi : i < gates.length), gates[i].op = GateOp.not → i = (j : ℕ) :=
    fun i hi ho => congrArg Fin.val (huniq ⟨i, hi⟩ ho)
  have hops1 : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hops g hg).1
  have hlen : ∀ g ∈ gates, g.inputs.length ≤ 2 := fun g hg => (hops g hg).2
  have hjv : ∀ x : Fin n → Bool, dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true →
      dvalue ⟨gates, 0⟩ x (n + (j : ℕ)) = false := by
    intro x hx
    obtain ⟨r, hr⟩ := hin
    have hr' : gates[(j : ℕ)].inputs = (n + (h : ℕ)) :: r := hr
    rw [dgatevalueP gates x j hjl, hjn, hr']
    have : n + (h : ℕ) < n + (j : ℕ) := by omega
    simp [GateOp.eval, this, hx]
  have hsem := fun (x : Fin n → Bool) (hx : dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true) =>
    sem n h j gates x hops1 huniq' hx (hjv x hx) gates.length le_rfl
  have hSl := S_len n h gates gates.length le_rfl
  refine ⟨(S n h gates gates.length).2,
    fun w => ((S n h gates gates.length).1.getD (out w) (Sum.inl false)).elim (fun _ => 0) id,
    S_ops n h j gates hhj' hops huniq' gates.length le_rfl,
    S_prefix n h gates gates.length le_rfl (by omega), ?_, ?_⟩
  · have hc := S_count n h j gates hhj' hjl hjn hlen gates.length le_rfl
    have hsub : insert (h : ℕ) (insert (j : ℕ)
        ((Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).image (fun i : Fin gates.length => (i : ℕ)))) ⊆
        (Finset.range gates.length).filter (fun i => bad n h j gates i = true) := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range]
      unfold bad
      simp only [decide_eq_true_eq]
      rcases Finset.mem_insert.mp hi with hi | hi
      · exact ⟨by omega, Or.inl hi⟩
      rcases Finset.mem_insert.mp hi with hi | hi
      · exact ⟨by omega, Or.inr (Or.inl hi)⟩
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨_, a, b⟩ := Finset.mem_filter.mp hi'
      refine ⟨i'.2, Or.inr (Or.inr ⟨a, ?_⟩)⟩
      rw [List.getD_eq_getElem _ _ i'.2]
      exact b
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_image_of_injective _ Fin.val_injective] at hcard
    · omega
    · intro hm
      obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hm
      have := (Finset.mem_filter.mp hi').2.1
      have : (j : ℕ) < (i' : ℕ) := this
      omega
    · intro hm
      rcases Finset.mem_insert.mp hm with hm | hm
      · omega
      · obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hm
        have := (Finset.mem_filter.mp hi').2.1
        have : (j : ℕ) < (i' : ℕ) := this
        omega
  · intro w x hx
    have hx' : dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true := hx
    obtain ⟨x0, y0, hx0, hy0, ox, oy⟩ := hsep w
    have ox' : dvalue ⟨gates, 0⟩ x0 (out w) = true := ox
    have oy' : dvalue ⟨gates, 0⟩ y0 (out w) = false := oy
    have a1 := hsem x0 hx0 (out w)
    have a2 := hsem y0 hy0 (out w)
    have a3 := hsem x hx' (out w)
    change (drun (S n h gates gates.length).2 (List.ofFn x)).getD (Sum.elim (fun _ => 0) id ((S n h gates gates.length).1.getD (out w) (Sum.inl false))) false = dvalue ⟨gates, 0⟩ x (out w)
    rcases hc : (S n h gates gates.length).1.getD (out w) (Sum.inl false) with b | w'
    · rw [hc] at a1 a2
      exfalso
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a1 a2
        have e1 : dvalue ⟨gates, 0⟩ x0 (out w) = b := a1
        have e2 : dvalue ⟨gates, 0⟩ y0 (out w) = b := a2
        rw [ox'] at e1
        rw [oy'] at e2
        rw [← e1] at e2
        exact Bool.noConfusion e2
      · rw [dmissingvalue _ x0 (out w) (by change n + gates.length ≤ _; omega)] at ox'
        exact Bool.noConfusion ox'
    · rw [hc] at a3
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a3
        exact a3.2
      · simp only [hlt, ↓reduceIte] at a3
        rw [dmissingvalue _ x (out w) (by change n + gates.length ≤ _; omega)]
        exact a3.2

lemma m53 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    3 ≤ q → T0 ⊆ L i0 → T0.card = q →
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
  intro q N L i0 T0 hq2 hN hcard hint hjoin hq3 hT0 hT0c gates o j h hg hjop hone hhj hjin hout hco hpts
  classical
  have hoff : ∀ t : Fin N, t ≠ i0 → ∃ a ∈ T0, a ∉ L t := by
    intro t ht
    by_contra hc
    have hsub : T0 ⊆ L t ∩ L i0 := fun a ha =>
      Finset.mem_inter.mpr ⟨by_contra (fun hn => hc ⟨a, ha, hn⟩), hT0 ha⟩
    have hle := Finset.card_le_card hsub
    rw [hint t i0 ht, hT0c] at hle
    omega
  have hlt : N + (h : ℕ) < N + (j : ℕ) := by
    have : (h : ℕ) < (j : ℕ) := hhj
    omega
  obtain ⟨a0, ha0⟩ : T0.Nonempty := Finset.card_pos.mp (by omega)
  have htrue : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun _ : Fin N => true)) = true :=
    hmono N gates j hg hone (fun v : Fin N => decide (v = a0)) (fun _ : Fin N => true) (fun v _ => rfl) _ hlt (hpts a0 ha0)
  have hy : ∀ t : Fin N, ∃ y : Fin N → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn y) = true ∧ ∀ v ∈ L t, y v = false := by
    intro t
    by_cases ht : t = i0
    · refine ⟨fun v : Fin N => decide (v ∉ L i0), hco, fun v hv => decide_eq_false (not_not.mpr ?_)⟩
      rw [← ht]
      exact hv
    · obtain ⟨a, ha, hat⟩ := hoff t ht
      refine ⟨fun v : Fin N => decide (v = a), hpts a ha, fun v hv => decide_eq_false (fun e => hat ?_)⟩
      rw [← e]
      exact hv
  obtain ⟨gates', out', hg', hpre, hlen, hagree⟩ := dmain N N gates o j h hg hjop hone hhj hjin (by
    intro w
    obtain ⟨y, hy1, hy2⟩ := hy w
    refine ⟨fun _ : Fin N => true, y, htrue, hy1, ?_, ?_⟩
    · rw [hout]
      obtain ⟨u, hu⟩ : (L w).Nonempty := Finset.card_pos.mp (by
        rw [hcard]
        omega)
      exact decide_eq_true ⟨u, hu, rfl⟩
    · rw [hout]
      refine decide_eq_false ?_
      rintro ⟨v, hv, hh⟩
      rw [hy2 v hv] at hh
      exact Bool.false_ne_true hh)
  have key := core q N L i0 T0 hq2 hN hcard hint hjoin hq3 hT0 hT0c gates' out' hg' (fun t x hx => (hagree t x (by
    rcases hx with ⟨a, ha, hxa⟩ | ⟨s, hs⟩
    · refine hmono N gates j hg hone (fun v : Fin N => decide (v = a)) x (fun v hv => ?_) _ hlt (hpts a ha)
      rw [of_decide_eq_true hv]
      exact hxa
    · by_cases hs0 : s = i0
      · refine hmono N gates j hg hone (fun v : Fin N => decide (v ∉ L i0)) x (fun v hv => ?_) _ hlt hco
        by_contra hf
        have hvs := hs v ((Bool.not_eq_true _).mp hf)
        rw [hs0] at hvs
        exact (of_decide_eq_true hv) hvs
      · obtain ⟨a, ha, hat⟩ := hoff s hs0
        have hxa : x a = true := by
          by_contra hf
          exact hat (hs a ((Bool.not_eq_true _).mp hf))
        refine hmono N gates j hg hone (fun v : Fin N => decide (v = a)) x (fun v hv => ?_) _ hlt (hpts a ha)
        rw [of_decide_eq_true hv]
        exact hxa)).trans (hout t x))
  omega

end PEqualNP.Outside.L_meta_1553

theorem PEqualNP.Outside.L_meta_1553 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    3 ≤ q → T0 ⊆ L i0 → T0.card = q →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = true →
    (∀ a ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = a))) = true) →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ N + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1553.m53
