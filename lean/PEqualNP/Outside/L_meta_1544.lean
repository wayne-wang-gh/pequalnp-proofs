import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1544

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

lemma main : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    ∀ D : (Fin N → Bool) → Prop,
    (∀ x y : Fin N → Bool, D x → (∀ v : Fin N, x v = true → y v = true) → D y) →
    (∀ t : Fin N, D (fun v : Fin N => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin N) (x : Fin N → Bool), D x → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin N)) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v : Fin N => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧ (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      q * Lam.card + max (N - Lam.card) I.card ≤ gates.length := by
  intro q N L hq hN hcard hint1 hjoin D hup hco gates o hg hout Lam B hB hno I hI
  classical
  let R : Fin N → Fin N → Finset (Fin N) := fun t p => insert p (B t p)
  have hNq : q + 1 < N := by
    rw [hN]
    nlinarith
  have hint : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card ≤ 1 := fun i j hij => le_of_eq (hint1 i j hij)
  have hgeo1 : ∀ t t' : Fin N, t ≠ t' → ∃ u ∈ L t, u ∉ L t' := by
    intro t t' htt
    by_contra hc
    have hsub : L t ⊆ L t' := fun u hu => by_contra fun hu' => hc ⟨u, hu, hu'⟩
    have h1 := hint1 t t' htt
    rw [Finset.inter_eq_left.mpr hsub, hcard t] at h1
    omega
  have hgeo2 : ∀ t v : Fin N, v ∈ L t → ∃ t' : Fin N, t' ≠ t ∧ v ∈ L t' := by
    intro t v hv
    have hex : ∃ p' : Fin N, p' ∉ L t := by
      by_contra hc
      have hsub : (Finset.univ : Finset (Fin N)) ⊆ L t := fun p _ => by_contra fun hp => hc ⟨p, hp⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin, hcard t] at h1
      omega
    obtain ⟨p', hp'⟩ := hex
    obtain ⟨i, hi1, hi2⟩ := hjoin v p' (fun e => hp' (e ▸ hv))
    exact ⟨i, fun e => hp' (e ▸ hi2), hi1⟩
  have hsucc : ∀ t : Fin N, ∃ t' : Fin N, t ≠ t' := by
    intro t
    have hpos : 0 < (L t).card := by
      rw [hcard t]
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    obtain ⟨t', hne, _⟩ := hgeo2 t v hv
    exact ⟨t', Ne.symm hne⟩
  have hval : ∀ (t : Fin N) (x : Fin N → Bool), D x →
      value ⟨gates, 0⟩ x (o t) = decide (∃ v ∈ L t, x v = true) := fun t x hx => hout t x hx
  have hDco : ∀ t : Fin N, D (coY L t) := hco
  have hfalse : ∀ t : Fin N, value ⟨gates, 0⟩ (coY L t) (o t) = false := by
    intro t
    rw [hval t _ (hDco t)]
    refine decide_eq_false ?_
    rintro ⟨v, hv, h⟩
    exact (of_decide_eq_true h) hv
  have hA : ∀ t t' : Fin N, t ≠ t' → value ⟨gates, 0⟩ (coY L t') (o t) = true := by
    intro t t' htt
    rw [hval t _ (hDco t')]
    obtain ⟨u, hu, hu'⟩ := hgeo1 t t' htt
    exact decide_eq_true ⟨u, hu, decide_eq_true hu'⟩
  have hrow : ∀ t ∈ Lam, ∀ p ∈ L t, rowL R t p = fun v => decide (v = p ∨ v ∈ B t p) := by
    intro t _ p _
    funext v
    simp only [rowL, R, Finset.mem_insert]
  have htrue : ∀ t ∈ Lam, ∀ p ∈ L t, value ⟨gates, 0⟩ (rowL R t p) (o t) = true := by
    intro t ht p hp
    have hd : D (rowL R t p) := by
      rw [hrow t ht p hp]
      exact (hB t ht p hp).2
    rw [hval t _ hd]
    exact decide_eq_true ⟨p, hp, decide_eq_true (Finset.mem_insert_self p _)⟩
  let K : Fin N → Finset (Fin gates.length) := fun i => Finset.univ.filter fun g =>
    InK gates L R i g
  have hK3 : ∀ t ∈ Lam, q ≤ (K t).card := by
    intro i hiL
    have h := family (n := N) gates hg (L i) (rowL R i) (coY L i) (o i)
      (fun p hp => ⟨htrue i hiL p hp, hfalse i⟩)
      (fun w hw hc => by
        obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
        have e : ∀ a ∈ L i, Sv ⟨gates, 0⟩ (rowL R i) (coY L i) a w →
            (⟨w, hw⟩ : Fin N) = a := by
          intro a ha hsa
          have h1 : value ⟨gates, 0⟩ (rowL R i a) ((⟨w, hw⟩ : Fin N) : ℕ) = true := hsa.1
          have h2 : value ⟨gates, 0⟩ (coY L i) ((⟨w, hw⟩ : Fin N) : ℕ) = false := hsa.2
          rw [input_value] at h1 h2
          simp only [rowL, coY, R, decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h1 h2
          rcases Finset.mem_insert.mp h1 with h3 | h3
          · exact h3
          · have h4 : (⟨w, hw⟩ : Fin N) ∈ B i a ∩ L i := Finset.mem_inter.mpr ⟨h3, h2⟩
            rw [(hB i hiL a ha).1] at h4
            exact absurd h4 (Finset.notMem_empty _)
        exact hne ((e p hp hs1).symm.trans (e p' hp' hs2)))
      (K i)
      (fun g hm hop hl hQ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hm, hop, hl, hQ⟩)
    have := hcard i
    omega
  have hKy : ∀ (i : Fin N) (g : Fin gates.length), g ∈ K i →
      value ⟨gates, 0⟩ (coY L i) (N + (g : ℕ)) = false := by
    intro i g hgi
    obtain ⟨p, _, _, _, _, hs, _⟩ := (Finset.mem_filter.mp hgi).2.1
    exact hs.2
  have hconv : ∀ i j : Fin N, (¬ ∃ p ∈ L i \ L j, (B i p ∩ L j).Nonempty) →
      ¬ ∃ p ∈ L i \ L j, (R i p ∩ L j).Nonempty := by
    rintro i j hn ⟨p, hp, v, hv⟩
    refine hn ⟨p, hp, v, ?_⟩
    obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_insert.mp hv1 with h3 | h3
    · rw [h3] at hv2
      exact absurd hv2 (Finset.mem_sdiff.mp hp).2
    · exact Finset.mem_inter.mpr ⟨h3, hv2⟩
  have hdisj : ∀ i ∈ Lam, ∀ j ∈ Lam, i ≠ j → Disjoint (K i) (K j) := by
    intro i hi j hj hij
    refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
    have hmi := (Finset.mem_filter.mp hgi).2.1
    have hmj := (Finset.mem_filter.mp hgj).2.1
    have hyi := hKy i g hgi
    have hyj := hKy j g hgj
    by_cases hA' : ∃ p ∈ L i \ L j, (B i p ∩ L j).Nonempty
    · have hB' : ¬ ∃ s ∈ L j \ L i, (B j s ∩ L i).Nonempty := fun hB' => hno i hi j hj hij ⟨hA', hB'⟩
      exact kill gates hg L R j i
        (by rw [Finset.inter_comm]; exact hint i j hij) (hconv j i hB') _ hmj hyi
    · exact kill gates hg L R i j (hint i j hij) (hconv i j hA') _ hmi hyj
  let U : Finset (Fin gates.length) := Lam.biUnion K
  have hU : q * Lam.card ≤ U.card := by
    have h1 : U.card = ∑ i ∈ Lam, (K i).card := Finset.card_biUnion hdisj
    have h2 : ∑ _i ∈ Lam, q ≤ ∑ i ∈ Lam, (K i).card := Finset.sum_le_sum fun i hi => hK3 i hi
    rw [Finset.sum_const, smul_eq_mul, mul_comm] at h2
    omega
  have hUor : ∀ g ∈ U, gates[(g : ℕ)].op = GateOp.or := by
    intro g hgU
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hgU
    exact (Finset.mem_filter.mp hgi).2.2.1
  have hUI : Disjoint U I := by
    refine Finset.disjoint_left.mpr fun g hgU hgI => ?_
    have h1 := hUor g hgU
    have h2 : gates[(g : ℕ)].op = GateOp.and := hI g hgI
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hpart2 : q * Lam.card + I.card ≤ gates.length := by
    have h1 := Finset.card_union_of_disjoint hUI
    have h2 := Finset.card_le_univ (U ∪ I)
    rw [Fintype.card_fin] at h2
    omega
  have hrange : ∀ t : Fin N, N ≤ o t ∧ o t < N + gates.length := by
    intro t
    constructor
    · by_contra hlt
      have hlt' : o t < N := by omega
      have hin : ∀ x : Fin N → Bool, value ⟨gates, 0⟩ x (o t) = x ⟨o t, hlt'⟩ := fun x =>
        input_value ⟨gates, 0⟩ x ⟨o t, hlt'⟩
      have h1 := hfalse t
      rw [hin] at h1
      have hv : (⟨o t, hlt'⟩ : Fin N) ∈ L t := by
        simpa only [coY, decide_eq_false_iff_not, not_not] using h1
      obtain ⟨t', hne, hv'⟩ := hgeo2 t _ hv
      have h2 := hA t t' (Ne.symm hne)
      rw [hin] at h2
      simp only [coY, decide_eq_true_eq] at h2
      exact h2 hv'
    · by_contra hge
      obtain ⟨t1, ht1⟩ := hsucc t
      have h2 := hA t t1 ht1
      rw [missing_value ⟨gates, 0⟩ _ (o t) (by change N + gates.length ≤ o t; omega)] at h2
      exact Bool.noConfusion h2
  let Un : Finset ℕ := U.image (fun g : Fin gates.length => N + (g : ℕ))
  let On : Finset ℕ := (Finset.univ \ Lam).image o
  have hUn : Un.card = U.card := Finset.card_image_of_injective _ (by
    intro a b hab
    exact Fin.ext (by simpa using hab))
  have hOn : On.card = N - Lam.card := by
    have h1 : On.card = (Finset.univ \ Lam).card := Finset.card_image_of_injOn (by
      intro a _ b _ hab
      by_contra hne
      have h1 := hA a b hne
      have h2 := hfalse b
      rw [show o a = o b from hab] at h1
      rw [h1] at h2
      exact Bool.noConfusion h2)
    rw [h1, Finset.card_sdiff_of_subset (Finset.subset_univ Lam), Finset.card_univ, Fintype.card_fin]
  have hdis : Disjoint Un On := by
    refine Finset.disjoint_left.mpr fun w hwU hwO => ?_
    obtain ⟨g, hgU, rfl⟩ := Finset.mem_image.mp hwU
    obtain ⟨t, htL, hto⟩ := Finset.mem_image.mp hwO
    obtain ⟨i, hiL, hgi⟩ := Finset.mem_biUnion.mp hgU
    have hne : t ≠ i := fun e => (Finset.mem_sdiff.mp htL).2 (e ▸ hiL)
    have h1 := hA t i hne
    have h2 := hKy i g hgi
    rw [hto, h2] at h1
    exact Bool.noConfusion h1
  have hsub : Un ∪ On ⊆ Finset.Ico N (N + gates.length) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_Ico.mpr ⟨by omega, by have := g.isLt; omega⟩
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_Ico.mpr (hrange t)
  have hpart1 : q * Lam.card + (N - Lam.card) ≤ gates.length := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, Nat.card_Ico] at h1
    omega
  rcases le_total (N - Lam.card) I.card with h | h
  · rw [max_eq_right h]
    exact hpart2
  · rw [max_eq_left h]
    exact hpart1
end PEqualNP.Outside.L_meta_1544

theorem PEqualNP.Outside.L_meta_1544 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    ∀ D : (Fin N → Bool) → Prop,
    (∀ x y : Fin N → Bool, D x → (∀ v : Fin N, x v = true → y v = true) → D y) →
    (∀ t : Fin N, D (fun v : Fin N => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin N) (x : Fin N → Bool), D x → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin N)) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v : Fin N => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧ (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      q * Lam.card + max (N - Lam.card) I.card ≤ gates.length :=
  PEqualNP.Outside.L_meta_1544.main
