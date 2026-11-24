import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1590

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
        PEqualNP.Outside.L_meta_1590.value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1590.coY S i) (n + (g : ℕ)) = false := by
  intro q n m S R hq hcard hint hR hno gates out hg hfalse htrue
  classical
  let K : Fin m → Finset (Fin gates.length) := fun i => Finset.univ.filter fun g =>
    PEqualNP.Outside.L_meta_1590.InK gates S R i g
  have hKq : ∀ i, q ≤ (K i).card := by
    intro i
    have h := PEqualNP.Outside.L_meta_1590.family (n := n) gates hg (S i)
      (PEqualNP.Outside.L_meta_1590.rowL R i) (PEqualNP.Outside.L_meta_1590.coY S i) (out i)
      (fun p hp => ⟨htrue i p hp, hfalse i⟩)
      (fun w hw hc => by
        obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
        have e : ∀ a ∈ S i, PEqualNP.Outside.L_meta_1590.Sv ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1590.rowL R i) (PEqualNP.Outside.L_meta_1590.coY S i) a w →
            (⟨w, hw⟩ : Fin n) = a := by
          intro a ha hsa
          have h1 : PEqualNP.Outside.L_meta_1590.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1590.rowL R i a) ((⟨w, hw⟩ : Fin n) : ℕ) = true := hsa.1
          have h2 : PEqualNP.Outside.L_meta_1590.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1590.coY S i) ((⟨w, hw⟩ : Fin n) : ℕ) = false := hsa.2
          rw [PEqualNP.Outside.L_meta_1590.input_value] at h1 h2
          simp only [PEqualNP.Outside.L_meta_1590.rowL, PEqualNP.Outside.L_meta_1590.coY,
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
    have hyi : PEqualNP.Outside.L_meta_1590.value ⟨gates, 0⟩
        (PEqualNP.Outside.L_meta_1590.coY S i) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmi
      exact hs.2
    have hyj : PEqualNP.Outside.L_meta_1590.value ⟨gates, 0⟩
        (PEqualNP.Outside.L_meta_1590.coY S j) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmj
      exact hs.2
    by_cases hA : ∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty
    · have hB : ¬ ∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty := fun hB => hno i j hij ⟨hA, hB⟩
      exact PEqualNP.Outside.L_meta_1590.kill gates hg S R j i
        (by rw [Finset.inter_comm]; exact hint i j hij) hB _ hmj hyi
    · exact PEqualNP.Outside.L_meta_1590.kill gates hg S R i j (hint i j hij) hA _ hmi hyj
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

theorem core (q n : ℕ) (L : Fin (n + 1) → Finset (Fin (n + 1))) (i0 : Fin (n + 1))
    (T0 : Finset (Fin (n + 1)))
    (hcard : ∀ i, (L i).card = q + 1) (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hq : 3 ≤ q) (hT : T0 ⊆ L i0) (hTc : 3 ≤ T0.card)
    (gates : List Gate) (o : Fin (n + 1) → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hev : ∀ (t : Fin (n + 1)) (x : Fin (n + 1) → Bool), ((∃ v ∈ T0, x v = true) ∨
      ∀ v : Fin (n + 1), v ∉ L i0 → x v = true) →
      value ⟨gates, 0⟩ x (o t) = decide (∃ v ∈ L t, x v = true)) :
    (n + 1) * q ≤ gates.length := by
  classical
  obtain ⟨c, hc1, hc2⟩ := cex L i0 T0 hinter hT hTc
  have hfalse : ∀ t : Fin (n + 1), value ⟨gates, 0⟩ (fun v : Fin (n + 1) => decide (v ∉ L t)) (o t) = false := by
    intro t
    have hdom : (∃ v ∈ T0, (fun v : Fin (n + 1) => decide (v ∉ L t)) v = true) ∨
        ∀ v : Fin (n + 1), v ∉ L i0 → (fun v : Fin (n + 1) => decide (v ∉ L t)) v = true := by
      by_cases ht : t = i0
      · rw [ht]
        exact Or.inr fun v hv => decide_eq_true hv
      · exact Or.inl ⟨c t, (hc1 t ht).1, decide_eq_true (hc1 t ht).2⟩
    have h := hev t (fun v : Fin (n + 1) => decide (v ∉ L t)) hdom
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
  let yp : Fin (n + 1) → Fin (n + 1) → Bool := fun a v => decide (v ∉ L i0 ∨ v = a)
  let A : Finset (Fin gates.length) := Finset.univ.filter fun g => gates[(g : ℕ)].op = GateOp.and
  let ch : Fin gates.length → ℕ := fun g =>
    if h : ∃ r ∈ gates[(g : ℕ)].inputs, r < n + 1 + (g : ℕ) ∧ value ⟨gates, 0⟩ y r = false
    then Classical.choose h else o i0
  let F : Finset ℕ := insert (o i0) (A.image ch)
  have hFy : ∀ w ∈ F, value ⟨gates, 0⟩ y w = false := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · rw [h]
      exact hfalse i0
    · obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp h
      by_cases hx : ∃ r ∈ gates[(g : ℕ)].inputs, r < n + 1 + (g : ℕ) ∧ value ⟨gates, 0⟩ y r = false
      · have e : ch g = Classical.choose hx := dite_eq_left hx
        rw [e]
        exact (Classical.choose_spec hx).2.2
      · have e : ch g = o i0 := dite_eq_right hx
        rw [e]
        exact hfalse i0
  have hFcard : F.card ≤ A.card + 1 := by
    have h1 := Finset.card_insert_le (o i0) (A.image ch)
    have h2 : (A.image ch).card ≤ A.card := Finset.card_image_le
    change F.card ≤ _ at h1
    omega
  have key : ∀ p : Fin (n + 1), ∀ w : ℕ, value ⟨gates, 0⟩ (yp p) w = true →
      value ⟨gates, 0⟩ y w = false →
      value ⟨gates, 0⟩ (l p) w = true ∨ ∃ d ∈ F, value ⟨gates, 0⟩ (l p) d = true := by
    intro p w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h1 h2
      by_cases hn : w < n + 1
      · left
        have e1 : yp p ⟨w, hn⟩ = true := (input_value ⟨gates, 0⟩ (yp p) ⟨w, hn⟩).symm.trans h1
        have e2 : y ⟨w, hn⟩ = false := (input_value ⟨gates, 0⟩ y ⟨w, hn⟩).symm.trans h2
        have e3 : (⟨w, hn⟩ : Fin (n + 1)) ∉ L i0 ∨ (⟨w, hn⟩ : Fin (n + 1)) = p := of_decide_eq_true e1
        have e4 : ¬ ((⟨w, hn⟩ : Fin (n + 1)) ∉ L i0) := of_decide_eq_false e2
        have e5 : (⟨w, hn⟩ : Fin (n + 1)) = p := e3.resolve_left e4
        have e6 : value ⟨gates, 0⟩ (l p) ((⟨w, hn⟩ : Fin (n + 1)) : ℕ) = l p ⟨w, hn⟩ :=
          input_value ⟨gates, 0⟩ (l p) ⟨w, hn⟩
        exact e6.trans (decide_eq_true e5)
      by_cases hw : w < n + 1 + gates.length
      · have hk : w - (n + 1) < gates.length := by omega
        have hwk : w = n + 1 + (w - (n + 1)) := by omega
        rw [hwk] at h1 h2
        rcases (hg _ (List.getElem_mem hk)).1 with hop | hop
        · have hx : ∃ r ∈ gates[w - (n + 1)].inputs, r < n + 1 + (w - (n + 1)) ∧
              value ⟨gates, 0⟩ y r = false := by
            by_contra hcon
            have hall : ∀ r ∈ gates[w - (n + 1)].inputs, r < n + 1 + (w - (n + 1)) ∧
                value ⟨gates, 0⟩ y r = true := by
              intro r hr
              have hlt := ((and_value (n := n + 1) ⟨gates, 0⟩ (w - (n + 1)) hk hop (yp p)).mp h1 r hr).1
              refine ⟨hlt, ?_⟩
              by_contra hne
              exact hcon ⟨r, hr, hlt, by simpa using hne⟩
            have h3 := (and_value (n := n + 1) ⟨gates, 0⟩ (w - (n + 1)) hk hop y).mpr hall
            exact Bool.noConfusion (h2.symm.trans h3)
          have e : ch ⟨w - (n + 1), hk⟩ = Classical.choose hx := dite_eq_left hx
          obtain ⟨hr, hlt, hry⟩ := Classical.choose_spec hx
          have hmem : Classical.choose hx ∈ F := by
            rw [← e]
            exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨⟨w - (n + 1), hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hop⟩, rfl⟩)
          have hv := ((and_value (n := n + 1) ⟨gates, 0⟩ (w - (n + 1)) hk hop (yp p)).mp h1 _ hr).2
          rcases ih _ (by omega) hv hry with h | h
          · exact Or.inr ⟨_, hmem, h⟩
          · exact Or.inr h
        · obtain ⟨r, hr, hlt, hv⟩ := (or_value (n := n + 1) ⟨gates, 0⟩ (w - (n + 1)) hk hop (yp p)).mp h1
          have hry : value ⟨gates, 0⟩ y r = false := by
            by_contra hne
            have h3 := (or_value (n := n + 1) ⟨gates, 0⟩ (w - (n + 1)) hk hop y).mpr
              ⟨r, hr, hlt, by simpa using hne⟩
            exact Bool.noConfusion (h2.symm.trans h3)
          rcases ih r (by omega) hv hry with h | h
          · left
            rw [hwk]
            exact (or_value (n := n + 1) ⟨gates, 0⟩ (w - (n + 1)) hk hop (l p)).mpr ⟨r, hr, hlt, h⟩
          · exact Or.inr h
      · have h3 := missing_value (n := n + 1) ⟨gates, 0⟩ (yp p) w (by
          change n + 1 + gates.length ≤ w
          omega)
        exact Bool.noConfusion (h3.symm.trans h1)
  have hcover : ∀ p ∈ L i0, ∃ w ∈ F, Sv ⟨gates, 0⟩ l y p w := by
    intro p hp
    by_cases hpT : p ∈ T0
    · refine ⟨o i0, Finset.mem_insert_self _ _, ?_, hfalse i0⟩
      have h := hev i0 (l p) (Or.inl ⟨p, hpT, decide_eq_true rfl⟩)
      have h2 : decide (∃ v ∈ L i0, l p v = true) = true :=
        decide_eq_true ⟨p, hp, decide_eq_true rfl⟩
      rw [h2] at h
      exact h
    · have h := hev i0 (yp p) (Or.inr fun v hv => decide_eq_true (Or.inl hv))
      have h2 : decide (∃ v ∈ L i0, yp p v = true) = true :=
        decide_eq_true ⟨p, hp, decide_eq_true (Or.inr rfl)⟩
      rw [h2] at h
      rcases key p (o i0) h (hfalse i0) with h3 | ⟨d, hd, h3⟩
      · exact ⟨o i0, Finset.mem_insert_self _ _, h3, hfalse i0⟩
      · exact ⟨d, hd, h3, hFy d hd⟩
  let K0 : Finset (Fin gates.length) := Finset.univ.filter fun g =>
    Multi ⟨gates, 0⟩ (L i0) l y (n + 1 + (g : ℕ)) ∧ gates[(g : ℕ)].op = GateOp.or
  let W : Finset ℕ := Finset.image (fun g : Fin gates.length => n + 1 + (g : ℕ)) K0
  have hlen : ∀ w, Multi ⟨gates, 0⟩ (L i0) l y w → n + 1 ≤ w ∧ w < n + 1 + gates.length := by
    intro w hc
    refine ⟨Nat.le_of_not_lt fun hw => ?_, ?_⟩
    · obtain ⟨p, _, p', _, hne, hs1, hs2⟩ := hc
      have e1 : l p ⟨w, hw⟩ = true := (input_value ⟨gates, 0⟩ (l p) ⟨w, hw⟩).symm.trans hs1.1
      have e2 : l p' ⟨w, hw⟩ = true := (input_value ⟨gates, 0⟩ (l p') ⟨w, hw⟩).symm.trans hs2.1
      exact hne ((of_decide_eq_true e1).symm.trans (of_decide_eq_true e2))
    · by_contra hge
      obtain ⟨p, _, _, _, _, hsv, _⟩ := hc
      have hm := missing_value (n := n + 1) ⟨gates, 0⟩ (l p) w (by
        change n + 1 + gates.length ≤ w
        omega)
      exact Bool.noConfusion (hm.symm.trans hsv.1)
  have h0 : (L i0).card ≤ F.card + (W.filter (· < n + 1 + gates.length)).card :=
    frontier (n := n + 1) ⟨gates, 0⟩ (L i0) l y hg W
      (fun k hk hm hop _ _ => Finset.mem_image.mpr ⟨(⟨k, hk⟩ : Fin gates.length),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, hop⟩, rfl⟩)
      hlen (n + 1 + gates.length) F
      (fun w _ hc => (hlen w hc).2) (L i0) (Finset.Subset.refl _) hcover
  have hW1 := Finset.card_filter_le W (· < n + 1 + gates.length)
  have hW2 : W.card ≤ K0.card := Finset.card_image_le
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
        (Finset.mem_inter.mpr ⟨hca, ha⟩) b (Finset.mem_inter.mpr ⟨hcb, hb⟩))
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
  have hdA : Disjoint A (K0 ∪ U) := by
    refine Finset.disjoint_left.mpr fun g hgA hgKU => ?_
    have hand : gates[(g : ℕ)].op = GateOp.and := (Finset.mem_filter.mp hgA).2
    rcases Finset.mem_union.mp hgKU with h | h
    · have h1 := (Finset.mem_filter.mp h).2.2
      cases h1.symm.trans hand
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
      have h1 := (hKp i _ hi).1
      cases h1.symm.trans hand
  have c1 : (K0 ∪ U).card = K0.card + U.card := Finset.card_union_of_disjoint hd0
  have c2 : (A ∪ (K0 ∪ U)).card = A.card + (K0 ∪ U).card := Finset.card_union_of_disjoint hdA
  have hle := Finset.card_le_univ (A ∪ (K0 ∪ U))
  rw [Fintype.card_fin] at hle
  have e : (n + 1) * q = n * q + q := by ring
  have hc0 := hcard i0
  omega

end PEqualNP.Outside.L_meta_1590

theorem PEqualNP.Outside.L_meta_1590 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin N) (x : Fin N → Bool), ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    N * q ≤ gates.length := by
  intro q m N L i0 T0 hq hm _ _ hcard hinter _ hT hTc gates o hg hev
  rcases N with _ | n
  · exact i0.elim0
  · exact PEqualNP.Outside.L_meta_1590.core q n L i0 T0 hcard hinter hq hT (by omega) gates o hg hev
