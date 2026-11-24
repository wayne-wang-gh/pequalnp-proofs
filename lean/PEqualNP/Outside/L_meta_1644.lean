import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1644

namespace B1643


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

lemma run_append (a b : List Gate) (x : List Bool) : run (a ++ b) x = run b (run a x) := by
  unfold run
  rw [List.foldl_append]

lemma any_congr' (l : List ℕ) (f g : ℕ → Bool) (h : ∀ p ∈ l, f p = g p) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun p hp => h p (by simp [hp]))]

lemma ofFn_getD {N : ℕ} (x : Fin N → Bool) (v : Fin N) : (List.ofFn x).getD (v : ℕ) false = x v := by
  have hp : (v : ℕ) < (List.ofFn x).length := by simp
  rw [List.getD_eq_getElem _ _ hp]
  simp

def chainFrom : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | acc, base, p :: ps => ⟨GateOp.or, [acc, p]⟩ :: chainFrom base (base + 1) ps

lemma chain_nil (acc base : ℕ) : chainFrom acc base [] = [] := rfl

lemma chain_cons (acc base p : ℕ) (ps : List ℕ) :
    chainFrom acc base (p :: ps) = ⟨GateOp.or, [acc, p]⟩ :: chainFrom base (base + 1) ps := rfl

lemma chain_length (ps : List ℕ) : ∀ acc base : ℕ, (chainFrom acc base ps).length = ps.length := by
  induction ps with
  | nil => intro acc base; rfl
  | cons p ps ih => intro acc base; rw [chain_cons, List.length_cons, List.length_cons, ih]

lemma chain_op (ps : List ℕ) : ∀ acc base : ℕ, ∀ g ∈ chainFrom acc base ps,
    g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  induction ps with
  | nil => intro acc base g hg; rw [chain_nil] at hg; simp at hg
  | cons p ps ih =>
    intro acc base g hg
    rw [chain_cons] at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨rfl, by simp⟩
    · exact ih _ _ g hg

lemma chain_wf (ps : List ℕ) : ∀ acc base : ℕ, acc < base → (∀ p ∈ ps, p < base) →
    ∀ (j : ℕ) (h : j < (chainFrom acc base ps).length),
      ∀ w ∈ ((chainFrom acc base ps)[j]).inputs, w < base + j := by
  induction ps with
  | nil => intro acc base _ _ j h; rw [chain_nil] at h; simp at h
  | cons p ps ih =>
    intro acc base hacc hps j h w hw
    have hp : p < base := hps p (by simp)
    cases j with
    | zero =>
      simp only [chain_cons, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    | succ j =>
      simp only [chain_cons, List.getElem_cons_succ] at hw
      have h' : j < (chainFrom base (base + 1) ps).length := by
        rw [chain_cons, List.length_cons] at h
        omega
      have h2 := ih base (base + 1) (by omega)
        (fun p' hp' => by have := hps p' (by simp [hp']); omega) j h' w hw
      omega

lemma chain_run (ps : List ℕ) : ∀ (acc base : ℕ) (W : List Bool), W.length = base →
    (∀ p ∈ ps, p < base) →
    (run (chainFrom acc base ps) W).getD (if ps = [] then acc else base + ps.length - 1) false =
      (W.getD acc false || ps.any (fun p => W.getD p false)) := by
  induction ps with
  | nil => intro acc base W _ _; simp [chain_nil, run]
  | cons p ps ih =>
    intro acc base W hW hps
    have hp : p < base := hps p (by simp)
    have hps' : ∀ p' ∈ ps, p' < base + 1 := fun p' hp' => by
      have := hps p' (by simp [hp'])
      omega
    have h := ih base (base + 1) (W ++ [GateOp.or.eval ([acc, p].map fun i => W.getD i false)])
      (by simp [hW]) hps'
    have hidx : (if ps = [] then base else base + 1 + ps.length - 1) =
        base + (p :: ps).length - 1 := by
      split_ifs with he
      · subst he; simp
      · simp only [List.length_cons]; omega
    rw [hidx] at h
    rw [if_neg (List.cons_ne_nil _ _), chain_cons, run_cons]
    refine h.trans ?_
    have hb : (W ++ [GateOp.or.eval ([acc, p].map fun i => W.getD i false)]).getD base false =
        (W.getD acc false || W.getD p false) := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hW, GateOp.eval]
    have hany : ps.any (fun p' =>
        (W ++ [GateOp.or.eval ([acc, p].map fun i => W.getD i false)]).getD p' false) =
        ps.any (fun p' => W.getD p' false) := by
      apply any_congr'
      intro p' hp'
      have := hps p' (by simp [hp'])
      exact List.getD_append _ _ _ _ (by omega)
    rw [hb, hany, List.any_cons, Bool.or_assoc]

def build (q N : ℕ) (pts : ℕ → List ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => build q N pts k ++ chainFrom ((pts k).headD 0) (N + k * q) (pts k).tail

lemma build_succ (q N : ℕ) (pts : ℕ → List ℕ) (k : ℕ) :
    build q N pts (k + 1) =
      build q N pts k ++ chainFrom ((pts k).headD 0) (N + k * q) (pts k).tail := rfl

lemma build_length (q N : ℕ) (pts : ℕ → List ℕ) (hlen : ∀ k, k < N → (pts k).length = q + 1) :
    ∀ k, k ≤ N → (build q N pts k).length = k * q := by
  intro k
  induction k with
  | zero => intro _; simp [build]
  | succ k ih =>
    intro hk
    rw [build_succ, List.length_append, ih (by omega), chain_length, List.length_tail,
      hlen k (by omega), Nat.succ_mul]
    omega

lemma build_op (q N : ℕ) (pts : ℕ → List ℕ) :
    ∀ k, ∀ g ∈ build q N pts k, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro g hg; simp [build] at hg
  | succ k ih =>
    intro g hg
    rw [build_succ] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact ih g hg
    · exact chain_op _ _ _ g hg

lemma wf_append (off : ℕ) (a b : List Gate)
    (ha : ∀ (j : ℕ) (h : j < a.length), ∀ w ∈ (a[j]).inputs, w < off + j)
    (hb : ∀ (j : ℕ) (h : j < b.length), ∀ w ∈ (b[j]).inputs, w < off + a.length + j) :
    ∀ (j : ℕ) (h : j < (a ++ b).length), ∀ w ∈ ((a ++ b)[j]).inputs, w < off + j := by
  intro j h w hw
  by_cases hj : j < a.length
  · rw [List.getElem_append_left hj] at hw
    exact ha j hj w hw
  · rw [List.getElem_append_right (by omega)] at hw
    have h2 := hb (j - a.length) (by rw [List.length_append] at h; omega) w hw
    omega

lemma build_wf (q N : ℕ) (pts : ℕ → List ℕ) (hlen : ∀ k, k < N → (pts k).length = q + 1)
    (hlt : ∀ k, k < N → ∀ p ∈ pts k, p < N) :
    ∀ k, k ≤ N → ∀ (j : ℕ) (h : j < (build q N pts k).length),
      ∀ w ∈ ((build q N pts k)[j]).inputs, w < N + j := by
  intro k
  induction k with
  | zero => intro _ j h; simp [build] at h
  | succ k ih =>
    intro hk
    have hkN : k < N := by omega
    have hl := build_length q N pts hlen k (by omega)
    obtain ⟨a, l, hpt⟩ : ∃ a l, pts k = a :: l := by
      have := hlen k hkN
      cases hc : pts k with
      | nil => rw [hc] at this; simp at this
      | cons a l => exact ⟨a, l, rfl⟩
    have ha : a < N := hlt k hkN a (by rw [hpt]; simp)
    refine wf_append N _ _ (ih (by omega)) ?_
    rw [hl]
    refine chain_wf _ _ _ ?_ ?_
    · rw [hpt]
      simp only [List.headD_cons]
      omega
    · intro p hp
      have := hlt k hkN p (List.mem_of_mem_tail hp)
      omega

lemma build_run (q N : ℕ) (hq : 1 ≤ q) (pts : ℕ → List ℕ)
    (hlen : ∀ k, k < N → (pts k).length = q + 1)
    (hlt : ∀ k, k < N → ∀ p ∈ pts k, p < N) (X : List Bool) (hX : X.length = N) :
    ∀ k, k ≤ N → ∀ t, t < k →
      (run (build q N pts k) X).getD (N + t * q + q - 1) false =
        (pts t).any (fun p => X.getD p false) := by
  intro k
  induction k with
  | zero => intro _ t ht; omega
  | succ k ih =>
    intro hk t ht
    have hkN : k < N := by omega
    have hl := build_length q N pts hlen k (by omega)
    have hWlen : (run (build q N pts k) X).length = N + k * q := by
      rw [run_length, hl, hX]
    rw [build_succ, run_append]
    by_cases htk : t < k
    · have h1 : (t + 1) * q ≤ k * q := Nat.mul_le_mul_right q (by omega)
      rw [Nat.succ_mul] at h1
      rw [run_getD _ _ _ (by rw [hWlen]; omega)]
      exact ih (by omega) t htk
    · have htk' : t = k := by omega
      subst htk'
      obtain ⟨a, l, hpt⟩ : ∃ a l, pts t = a :: l := by
        have := hlen t hkN
        cases hc : pts t with
        | nil => rw [hc] at this; simp at this
        | cons a l => exact ⟨a, l, rfl⟩
      have hll : l.length = q := by
        have := hlen t hkN
        rw [hpt, List.length_cons] at this
        omega
      have hne : l ≠ [] := by
        intro he
        rw [he] at hll
        simp at hll
        omega
      have hWX : ∀ p, p < N → (run (build q N pts t) X).getD p false = X.getD p false :=
        fun p hp => run_getD _ _ _ (by omega)
      have hmem : ∀ p ∈ a :: l, p < N := fun p hp => hlt t hkN p (by rw [hpt]; exact hp)
      have hc := chain_run l a (N + t * q) (run (build q N pts t) X) hWlen
        (fun p hp => by have := hmem p (by simp [hp]); omega)
      rw [if_neg hne, hll] at hc
      rw [hpt]
      simp only [List.headD_cons, List.tail_cons]
      rw [hc, List.any_cons, hWX a (hmem a (by simp))]
      congr 1
      apply any_congr'
      intro p hp
      exact hWX p (hmem p (by simp [hp]))

lemma upper (q N : ℕ) (L : Fin N → Finset (Fin N)) (hq : 1 ≤ q)
    (hL : ∀ i : Fin N, (L i).card = q + 1) :
    ∃ (gates : List Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) ∧
      (∀ (t : Fin N) (x : Fin N → Bool),
        Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) ∧
      gates.length = N * q := by
  obtain ⟨pts, hpts⟩ : ∃ pts : ℕ → List ℕ, ∀ (k : ℕ) (h : k < N),
      pts k = List.map Fin.val (L ⟨k, h⟩).toList :=
    ⟨fun k => if h : k < N then List.map Fin.val (L ⟨k, h⟩).toList else [],
      fun k h => dif_pos h⟩
  have hlen : ∀ k, k < N → (pts k).length = q + 1 := by
    intro k h
    rw [hpts k h, List.length_map, Finset.length_toList, hL]
  have hlt : ∀ k, k < N → ∀ p ∈ pts k, p < N := by
    intro k h p hp
    rw [hpts k h] at hp
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
    exact v.2
  refine ⟨build q N pts N, fun t => N + (t : ℕ) * q + q - 1, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have h := build_op q N pts N g hg
    exact ⟨Or.inr h.1, h.2⟩
  · intro i w hw
    exact build_wf q N pts hlen hlt N le_rfl i.1 i.2 w hw
  · intro t x
    have hT : pts (t : ℕ) = List.map Fin.val (L t).toList := hpts t t.2
    change (run (build q N pts N) (List.ofFn x)).getD (N + (t : ℕ) * q + q - 1) false = _
    rw [build_run q N hq pts hlen hlt (List.ofFn x) (by simp) N le_rfl t t.2, hT,
      Bool.eq_iff_iff]
    simp only [List.any_eq_true, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨p, ⟨v, hv, rfl⟩, h⟩
      rw [ofFn_getD] at h
      exact ⟨v, Finset.mem_toList.mp hv, h⟩
    · rintro ⟨v, hv, h⟩
      exact ⟨v, ⟨v, Finset.mem_toList.mpr hv, rfl⟩, by rw [ofFn_getD]; exact h⟩
  · exact build_length q N pts hlen N le_rfl

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

def vl {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) : Bool :=
  value (⟨gates, 0⟩ : Circuit) x w

lemma vl_input {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h : w < N) :
    vl gates x w = x ⟨w, h⟩ :=
  input_value (⟨gates, 0⟩ : Circuit) x ⟨w, h⟩

lemma vl_missing {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : N + gates.length ≤ w) : vl gates x w = false :=
  missing_value (⟨gates, 0⟩ : Circuit) x w hw

lemma vl_and {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h13 : N ≤ w)
    (hw : w < N + gates.length) (hop : (gates[w - N]'(by omega)).op = GateOp.and) :
    vl gates x w = true ↔
      ∀ r ∈ (gates[w - N]'(by omega)).inputs, r < w ∧ vl gates x r = true := by
  have h := gate_value (⟨gates, 0⟩ : Circuit) x w h13 hw
  simp only at h
  unfold vl
  rw [h, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
  constructor
  · intro hall r hr
    have := hall _ ⟨r, hr, rfl⟩
    by_cases hrw : r < w
    · simpa [hrw] using this
    · simp [hrw] at this
  · rintro hall b ⟨r, hr, rfl⟩
    have := hall r hr
    simp [this.1, this.2]

lemma vl_or {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h13 : N ≤ w)
    (hw : w < N + gates.length) (hop : (gates[w - N]'(by omega)).op = GateOp.or) :
    vl gates x w = true ↔
      ∃ r ∈ (gates[w - N]'(by omega)).inputs, r < w ∧ vl gates x r = true := by
  have h := gate_value (⟨gates, 0⟩ : Circuit) x w h13 hw
  simp only at h
  unfold vl
  rw [h, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
  constructor
  · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    by_cases hrw : r < w
    · exact ⟨r, hr, hrw, by simpa [hrw] using hb⟩
    · simp [hrw] at hb
  · rintro ⟨r, hr, hrw, hv⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by simp [hrw, hv]⟩

lemma vl_mono {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, vl gates x w = true → vl gates y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases h13 : w < N
    · rw [vl_input gates x w h13] at hx
      rw [vl_input gates y w h13]
      exact hxy _ hx
    · by_cases hw : w < N + gates.length
      · have hk : w - N < gates.length := by omega
        rcases hg (gates[w - N]) (List.getElem_mem hk) with hop | hop
        · rw [vl_and gates x w (by omega) hw hop] at hx
          rw [vl_and gates y w (by omega) hw hop]
          intro r hr
          exact ⟨(hx r hr).1, ih r (hx r hr).1 (hx r hr).2⟩
        · rw [vl_or gates x w (by omega) hw hop] at hx
          rw [vl_or gates y w (by omega) hw hop]
          obtain ⟨r, hr, hlt, hv⟩ := hx
          exact ⟨r, hr, hlt, ih r hlt hv⟩
      · rw [vl_missing gates x w (by omega)] at hx
        exact Bool.noConfusion hx

namespace B1635

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M c τ i X

def Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X

theorem single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    ∀ w, w < n + k → val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at hwc h1 h2
      have hm := hc _ hwc
      have e1 := (hτ y hy _ hm).1 h1
      have e2 := (hτ y' hy' _ hm).1 h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : 1 ≤ gates[w - n].inputs.length ∧ ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j c = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) c = true := by
            apply (val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp.2 j hj, ?_⟩
            cases hv : val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp.2 j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j c = false := by
          intro j hj
          cases hv : val gates j c with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) c = true :=
              (val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp.2 j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp.2 a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    Con gates M c τ (k + 1) X ↔ Con gates M c τ k X ∧ Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : Con gates M c τ k X) :
    Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : Con gates M c τ k X)
    (hY : Con gates M c τ k Y) : Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M c τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

theorem symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => Con gates M c τ k X)

open Classical in
theorem symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ P gates M c τ k)
    (hY : Y ⊆ M) (hYc : Con gates M c τ k Y) : symmDiff X Y ∈ P gates M c τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M c τ ((g : ℕ) + 1)).card * (if Mrg gates M c τ g then 2 else 1)
      = (P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : P gates M c τ ((g : ℕ) + 1) = P gates M c τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    rw [hP, if_neg hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := (hin g).2 a hma
    have hb : b < n + (g : ℕ) := (hin g).2 b hmb
    have hac : val gates a c = false := by
      cases hv : val gates a c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : val gates b c = false := by
      cases hv : val gates b c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hc hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hc hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X
    · have hmrg : Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [if_pos hmrg]
      have hP : P gates M c τ ((g : ℕ) + 1)
          = (P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [if_neg hnm, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M c τ g X h⟩

open Classical in
theorem count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M c τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M c τ (k + 1)).card * (if Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M c τ k).card := step gates M c τ hc hτ legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
          + (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring


open Classical in
theorem mcount {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = M.card - 1 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M c τ hc hτ legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := count gates M c τ hc hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

open Classical in
theorem final {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true)
    (K : Finset (Fin gates.length)) (hK : ∀ g : Fin gates.length, g ∈ K ↔ Mrg gates M c τ g) :
    K.card = M.card - 1 := by
  have hKe : K = Finset.univ.filter (fun g => Mrg gates M c τ g) := by
    ext g
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact hK g
  rw [hKe, Finset.card_filter]
  exact mcount gates M c τ hc hτ legal hin hM o hoc hot

theorem line_eq {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (h2 : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hne : p0 ≠ p1) (h0 : p0 ∈ L i0) (h1 : p1 ∈ L i0)
    (t : Fin N) (a0 : p0 ∈ L t) (a1 : p1 ∈ L t) : t = i0 := by
  by_contra hti
  have hc := h2 t i0 hti
  have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_inter.mpr ⟨a0, h0⟩
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_inter.mpr ⟨a1, h1⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hne, hc] at hle
  omega


theorem top : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) →
    ∀ Mg : Fin N → Fin gates.length → Prop,
    (∀ (t : Fin N) (g : Fin gates.length), Mg t g ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L t, ∃ r' ∈ L t, ev w1 (T t r) = true ∧ ev w2 (T t r') = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
          ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
          (ev c1 (T t s) = true ∨ ev c2 (T t s) = true) → (ev c1 (T t s') = true ∨ ev c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X)))) →
    ∀ t : Fin N,
      (∀ g : Fin gates.length, ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false → ∀ a ∈ L t, ∀ b ∈ L t, ev (N + (g : ℕ)) (T t a) = true → ev (N + (g : ℕ)) (T t b) = true →
        ∀ X : Finset (Fin N), (∀ i : Fin gates.length, i ≤ g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
          ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
          (ev c1 (T t s) = true ∨ ev c2 (T t s) = true) → (ev c1 (T t s') = true ∨ ev c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X)) → (a ∈ X ↔ b ∈ X)) ∧
      ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ I ↔ Mg t g) → I.card = q := by
  intro q N L i0 p0 p1 _ _ hcard hI _ hne h0 h1 T hT gates legal hlen hin ev hev o ho Mg hMg t
  have hevf : ev = fun w x => val gates w x := funext fun w => funext fun x => hev w x
  subst hevf
  have key := line_eq L i0 p0 p1 hI hne h0 h1
  have hc : ∀ v, (fun v : Fin N => decide (v ∉ L t)) v = false → v ∈ L t :=
    fun v hv => by simpa using hv
  have hτ : ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p := by
    intro p hp v hv
    rw [hT t p v]
    constructor
    · rintro (h | ⟨h, _, e⟩ | ⟨_, h, _, e⟩ | ⟨_, _, _, _, h⟩)
      · exact h
      · exact absurd (e ▸ hv) h
      · exact absurd (e ▸ hv) h
      · exact absurd hv h
    · exact fun h => Or.inl h
  have hin' : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ) := fun i => ⟨hlen i, hin i⟩
  constructor
  · intro g hgc a ha b hb h1' h2' X hX
    exact single gates (L t) _ (T t) hc hτ legal hin' ((g : ℕ) + 1) (Nat.succ_le_of_lt g.2) X
      (fun i hi => hX i (Fin.le_def.mpr (Nat.lt_succ_iff.mp hi))) (N + (g : ℕ)) (by omega) hgc
      a ha b hb h1' h2'
  · intro I hI'
    have hzF : (fun v : Fin N => decide (v ∉ L t)) p0 = true ∨
        (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨
        ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true := by
      by_cases a0 : p0 ∈ L t
      · by_cases a1 : p1 ∈ L t
        · have ht := key t a0 a1
          refine Or.inr (Or.inr ?_)
          intro u hu
          rw [ht]
          exact decide_eq_true hu
        · exact Or.inr (Or.inl (decide_eq_true a1))
      · exact Or.inl (decide_eq_true a0)
    have hTF : ∀ p ∈ L t, T t p p0 = true ∨ T t p p1 = true ∨
        ∀ u : Fin N, u ∉ L i0 → T t p u = true := by
      intro p _
      by_cases e0 : p = p0
      · exact Or.inl ((hT t p p0).mpr (Or.inl e0.symm))
      by_cases e1 : p = p1
      · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inl e1.symm)))
      by_cases a0 : p0 ∈ L t
      · by_cases a1 : p1 ∈ L t
        · have ht := key t a0 a1
          refine Or.inr (Or.inr ?_)
          intro u hu
          refine (hT t p u).mpr (Or.inr (Or.inr (Or.inr ⟨a0, a1, e0, e1, ?_⟩)))
          rw [ht]
          exact hu
        · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨a0, a1, e0, rfl⟩)))))
      · exact Or.inl ((hT t p p0).mpr (Or.inr (Or.inl ⟨a0, e1, rfl⟩)))
    have hoc : val gates (o t) (fun v : Fin N => decide (v ∉ L t)) = false :=
      (ho t _ hzF).trans (by simp)
    have hot : ∀ p ∈ L t, val gates (o t) (T t p) = true := fun p hp =>
      (ho t _ (hTF p hp)).trans (decide_eq_true ⟨p, hp, (hτ p hp p hp).2 rfl⟩)
    have h := final gates (L t) (fun v : Fin N => decide (v ∉ L t)) (T t) hc hτ legal hin'
      (by rw [hcard t]; omega) (o t) hoc hot I (fun g => (hI' g).trans (hMg t g))
    rw [h, hcard t]
    rfl

end B1635

namespace B1637


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

def vl {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  value (⟨gates, 0⟩ : Circuit) x w

lemma vl_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    vl gates x w = x ⟨w, h⟩ :=
  input_value (⟨gates, 0⟩ : Circuit) x ⟨w, h⟩

lemma vl_missing {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : vl gates x w = false :=
  missing_value (⟨gates, 0⟩ : Circuit) x w hw

lemma vl_gate {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) :
    vl gates x (n + k) =
      g.op.eval (g.inputs.map fun r => if r < n + k then vl gates x r else false) := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hk
  have h := gate_value (⟨gates, 0⟩ : Circuit) x (n + k) (by omega)
    (by show n + k < n + gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

lemma vl_and {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) (hop : g.op = GateOp.and) :
    vl gates x (n + k) = true ↔ ∀ r ∈ g.inputs, r < n + k ∧ vl gates x r = true := by
  rw [vl_gate gates x k g hk, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
  constructor
  · intro hall r hr
    have := hall _ ⟨r, hr, rfl⟩
    by_cases hrw : r < n + k
    · simpa [hrw] using this
    · simp [hrw] at this
  · rintro hall b ⟨r, hr, rfl⟩
    have := hall r hr
    simp [this.1, this.2]

lemma vl_or {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) (hop : g.op = GateOp.or) :
    vl gates x (n + k) = true ↔ ∃ r ∈ g.inputs, r < n + k ∧ vl gates x r = true := by
  rw [vl_gate gates x k g hk, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
  constructor
  · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    by_cases hrw : r < n + k
    · exact ⟨r, hr, hrw, by simpa [hrw] using hb⟩
    · simp [hrw] at hb
  · rintro ⟨r, hr, hrw, hv⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by simp [hrw, hv]⟩

theorem main (N : ℕ) (L : Fin N → Finset (Fin N)) (p0 p1 : Fin N)
    (T : Fin N → Fin N → Fin N → Bool)
    (hT : ∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t)))
    (gates : List Gate)
    (hg : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (ev : ℕ → (Fin N → Bool) → Bool) (hev : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = vl gates x w)
    (TS : Fin N → Fin N → ℕ → Prop)
    (hTS : ∀ (l m : Fin N) (w : ℕ), TS l m w ↔ (ev w (fun v : Fin N => decide (v ∉ L l)) = false ∧ ev w (fun v : Fin N => decide (v ∉ L m)) = false ∧ (∃ p ∈ L l, ev w (T l p) = true) ∧ ∃ p ∈ L m, ev w (T m p) = true))
    (Hg : Fin N → Fin N → Fin gates.length → Prop)
    (hHg : ∀ (l m : Fin N) (g : Fin gates.length), Hg l m g ↔ (TS l m (N + (g : ℕ)) ∧ ((gates.get g).op = GateOp.and ∨ ((gates.get g).op = GateOp.or ∧ ∀ e ∈ (gates.get g).inputs, ¬ TS l m e))))
    (l m : Fin N) (hl : p0 ∈ L l ∧ p1 ∉ L l) (hm : p1 ∈ L m ∧ p0 ∉ L m) :
      (∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m)) ∧
      (∀ p : Fin N, p ∈ L l → p ∈ L m → (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧ (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p)) ∧
      ∀ w : ℕ, TS l m w → ∃ ν : ℕ, (∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → ν ∈ Zs) ∧
        ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨ ∃ h : Fin gates.length, ν = (N + (h : ℕ)) ∧ Hg l m h) ∧
        (∀ s ∈ L l, ev ν (T l s) = true → ev w (T l s) = true) ∧ (∀ s ∈ L m, ev ν (T m s) = true → ev w (T m s) = true) ∧
        (∃ s ∈ L l, ev ν (T l s) = true) ∧ ∃ s ∈ L m, ev ν (T m s) = true := by
  have ev_in : ∀ (p : Fin N) (x : Fin N → Bool), ev (p : ℕ) x = x p := by
    intro p x
    rw [hev, vl_input gates x p p.2]
  have ev_miss : ∀ (w : ℕ) (x : Fin N → Bool), N + gates.length ≤ w → ev w x = false := by
    intro w x hw
    rw [hev]
    exact vl_missing gates x w hw
  have ev_or : ∀ (k : Fin gates.length) (x : Fin N → Bool), (gates.get k).op = GateOp.or →
      ∀ r ∈ (gates.get k).inputs, ev r x = true → ev (N + (k : ℕ)) x = true := by
    intro k x hop r hr hv
    rw [hev] at hv
    rw [hev]
    exact (vl_or gates x k _ (List.getElem?_eq_getElem k.2) hop).mpr ⟨r, hr, hwf k r hr, hv⟩
  have hA : ∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m) := by
    intro p
    rw [hTS]
    simp only [ev_in]
    constructor
    · rintro ⟨h1, h2, -, -⟩
      exact ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using h1, by simpa using h2, ⟨p, h1, (hT l p p).mpr (Or.inl rfl)⟩,
        ⟨p, h2, (hT m p p).mpr (Or.inl rfl)⟩⟩
  have hB : ∀ p : Fin N, p ∈ L l → p ∈ L m → (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧
      (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p) := by
    intro p hpl hpm
    constructor
    · intro s hs
      rw [ev_in, hT]
      constructor
      · rintro (h | ⟨h, -⟩ | ⟨-, -, -, h⟩ | ⟨-, h, -⟩)
        · exact h.symm
        · exact absurd hl.1 h
        · rw [h] at hpl
          exact absurd hpl hl.2
        · exact absurd h hl.2
      · intro h
        exact Or.inl h.symm
    · intro s hs
      rw [ev_in, hT]
      constructor
      · rintro (h | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · exact h.symm
        · rw [h] at hpm
          exact absurd hpm hm.2
        · exact absurd h hm.2
        · exact absurd h hm.2
      · intro h
        exact Or.inl h.symm
  refine ⟨hA, hB, ?_⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    have hw' := (hTS l m w).mp hw
    by_cases hn : w < N
    · refine ⟨w, fun Zs h _ => h, Or.inl ⟨⟨w, hn⟩, ?_, ?_, rfl⟩, fun s _ h => h, fun s _ h => h,
        hw'.2.2.1, hw'.2.2.2⟩
      · exact ((hA ⟨w, hn⟩).mp hw).1
      · exact ((hA ⟨w, hn⟩).mp hw).2
    · by_cases hlt : w < N + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < gates.length := by omega
        by_cases hH : Hg l m ⟨k, hk⟩
        · exact ⟨N + k, fun Zs h _ => h, Or.inr ⟨⟨k, hk⟩, rfl, hH⟩, fun s _ h => h, fun s _ h => h,
            hw'.2.2.1, hw'.2.2.2⟩
        · rw [hHg] at hH
          have hop : (gates.get ⟨k, hk⟩).op = GateOp.or := by
            rcases (hg _ (List.get_mem gates ⟨k, hk⟩)).1 with h | h
            · exact absurd ⟨hw, Or.inl h⟩ hH
            · exact h
          have hex : ∃ e ∈ (gates.get ⟨k, hk⟩).inputs, TS l m e := by
            by_contra hne
            exact hH ⟨hw, Or.inr ⟨hop, fun e he hte => hne ⟨e, he, hte⟩⟩⟩
          obtain ⟨e, he, hte⟩ := hex
          obtain ⟨ν, h1, h2, h3, h4, h5, h6⟩ := ih e (hwf ⟨k, hk⟩ e he) hte
          refine ⟨ν, fun Zs h hcl => h1 Zs (hcl ⟨k, hk⟩ h e he) hcl, h2, ?_, ?_, h5, h6⟩
          · intro s hs hv
            exact ev_or ⟨k, hk⟩ _ hop e he (h3 s hs hv)
          · intro s hs hv
            exact ev_or ⟨k, hk⟩ _ hop e he (h4 s hs hv)
      · exfalso
        obtain ⟨p, -, hp⟩ := hw'.2.2.1
        rw [ev_miss w _ (by omega)] at hp
        exact Bool.noConfusion hp


theorem top : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ TS : Fin N → Fin N → ℕ → Prop,
    (∀ (l m : Fin N) (w : ℕ), TS l m w ↔ (ev w (fun v : Fin N => decide (v ∉ L l)) = false ∧ ev w (fun v : Fin N => decide (v ∉ L m)) = false ∧ (∃ p ∈ L l, ev w (T l p) = true) ∧ ∃ p ∈ L m, ev w (T m p) = true)) →
    ∀ Hg : Fin N → Fin N → Fin gates.length → Prop,
    (∀ (l m : Fin N) (g : Fin gates.length), Hg l m g ↔ (TS l m (N + (g : ℕ)) ∧ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ e ∈ (gates.get g).inputs, ¬ TS l m e)))) →
    ∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      (∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m)) ∧
      (∀ p : Fin N, p ∈ L l → p ∈ L m → (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧ (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p)) ∧
      ∀ w : ℕ, TS l m w → ∃ ν : ℕ, (∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → ν ∈ Zs) ∧
        ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨ ∃ h : Fin gates.length, ν = (N + (h : ℕ)) ∧ Hg l m h) ∧
        (∀ s ∈ L l, ev ν (T l s) = true → ev w (T l s) = true) ∧ (∀ s ∈ L m, ev ν (T m s) = true → ev w (T m s) = true) ∧
        (∃ s ∈ L l, ev ν (T l s) = true) ∧ ∃ s ∈ L m, ev ν (T m s) = true := by
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ T hT gates hg _ hwf ev hev TS hTS Hg hHg l m hl hm
  exact PEqualNP.Outside.L_meta_1644.B1643.B1637.main N L p0 p1 T hT gates hg hwf ev (fun w x => hev w x)
    TS hTS Hg hHg l m hl hm

end B1637

namespace B1642

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

def St (gates : List Gate) (N : ℕ) (w p : ℕ) : Prop :=
  ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs →
    (gates.get k).op = GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → p ∈ Zs

theorem st_refl (gates : List Gate) (N w : ℕ) : St gates N w w := fun _ h _ => h

theorem st_down (gates : List Gate) (N w : ℕ) (k : Fin gates.length)
    (hop : (gates.get k).op = GateOp.or) (e : ℕ) (he : e ∈ (gates.get k).inputs)
    (h : St gates N w (N + (k : ℕ))) : St gates N w e :=
  fun Zs h1 h2 => h2 k (h Zs h1 h2) hop e he

theorem st_up (gates : List Gate) (N : ℕ) (k : Fin gates.length)
    (hop : (gates.get k).op = GateOp.or) (e : ℕ) (he : e ∈ (gates.get k).inputs) (p : ℕ)
    (h : St gates N e p) : St gates N (N + (k : ℕ)) p :=
  fun Zs h1 h2 => h Zs (h2 k h1 hop e he) h2

theorem st_atom (gates : List Gate) (N w p : ℕ)
    (hno : ∀ k : Fin gates.length, w = N + (k : ℕ) → (gates.get k).op ≠ GateOp.or)
    (h : St gates N w p) : p = w := by
  have h1 : p ∈ ({w} : Set ℕ) := h {w} (Set.mem_singleton w)
    (fun k hk hop => absurd hop (hno k (Set.mem_singleton_iff.1 hk).symm))
  exact Set.mem_singleton_iff.1 h1

theorem st_or (gates : List Gate) (N : ℕ) (k : Fin gates.length) (p : ℕ)
    (h : St gates N (N + (k : ℕ)) p) :
    p = N + (k : ℕ) ∨ ∃ e ∈ (gates.get k).inputs, St gates N e p := by
  have h1 : p ∈ {u : ℕ | u = N + (k : ℕ) ∨ ∃ e ∈ (gates.get k).inputs, St gates N e u} := by
    refine h _ ?_ ?_
    · show N + (k : ℕ) = N + (k : ℕ) ∨ _
      exact Or.inl rfl
    · intro k' hk' hop e' he'
      have hk'' : N + (k' : ℕ) = N + (k : ℕ) ∨
          ∃ e ∈ (gates.get k).inputs, St gates N e (N + (k' : ℕ)) := hk'
      show e' = N + (k : ℕ) ∨ ∃ e ∈ (gates.get k).inputs, St gates N e e'
      rcases hk'' with hk'' | ⟨e, he, hs⟩
      · have hkk : k' = k := Fin.ext (by omega)
        subst hkk
        exact Or.inr ⟨e', he', st_refl gates N e'⟩
      · exact Or.inr ⟨e, he, st_down gates N e k' hop e' he' hs⟩
  exact h1

theorem st_false (gates : List Gate) (N : ℕ)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (x : Fin N → Bool) (w p : ℕ) (hw : val gates w x = false) (h : St gates N w p) :
    val gates p x = false := by
  have h1 : p ∈ {u : ℕ | val gates u x = false} := by
    refine h _ hw ?_
    intro k hk hop e he
    show val gates e x = false
    have hk' : val gates (N + (k : ℕ)) x = false := hk
    cases hv : val gates e x with
    | false => rfl
    | true =>
      have ht := (val_or gates x (k : ℕ) k.2 hop).2 ⟨e, he, hin k e he, hv⟩
      rw [ht] at hk'
      exact Bool.noConfusion hk'
  exact h1

def E (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N) (w : ℕ) (v : Fin N) :
    Prop :=
  (v ∈ M ∧ v ≠ p0 ∧ v ≠ p1 ∧ St gates N w (v : ℕ)) ∨
  (v = p0 ∧ (val gates w (fun u : Fin N => decide (u = p0)) = true ∨
    val gates w (fun u : Fin N => decide (u = p1)) = true))

def Inv (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N) (z : Fin N → Bool)
    (k : ℕ) (f : Fin N → Fin N) : Prop :=
  ∀ g : Fin gates.length, (g : ℕ) < k → (gates.get g).op = GateOp.or →
    val gates (N + (g : ℕ)) z = false → ∀ v v' : Fin N,
    E gates N M p0 p1 (N + (g : ℕ)) v → E gates N M p0 p1 (N + (g : ℕ)) v' → f v = f v'

theorem anchor_input (gates : List Gate) {N : ℕ} (u p : Fin N)
    (h : val gates (u : ℕ) (fun t : Fin N => decide (t = p)) = true) : u = p := by
  rw [val_input gates _ (u : ℕ) u.2] at h
  exact of_decide_eq_true h

theorem E_same (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N)
    (z : Fin N → Bool) (k : ℕ) (f : Fin N → Fin N) (hI : Inv gates N M p0 p1 z k f)
    (w : ℕ) (hw : w < N + k) (hz : val gates w z = false) (v v' : Fin N)
    (hv : E gates N M p0 p1 w v) (hv' : E gates N M p0 p1 w v') : f v = f v' := by
  by_cases hor : ∃ g : Fin gates.length, w = N + (g : ℕ) ∧ (gates.get g).op = GateOp.or
  · obtain ⟨g, hg, hop⟩ := hor
    subst hg
    exact hI g (by omega) hop hz v v' hv hv'
  · have hno : ∀ g : Fin gates.length, w = N + (g : ℕ) → (gates.get g).op ≠ GateOp.or :=
      fun g hg hop => hor ⟨g, hg, hop⟩
    rcases hv with ⟨_, h0, h1, hs⟩ | ⟨e0, ha⟩
    · have e1 : (v : ℕ) = w := st_atom gates N w _ hno hs
      rcases hv' with ⟨_, h0', h1', hs'⟩ | ⟨e0', ha'⟩
      · have e2 : (v' : ℕ) = w := st_atom gates N w _ hno hs'
        have : v = v' := Fin.ext (e1.trans e2.symm)
        rw [this]
      · exfalso
        rw [← e1] at ha'
        rcases ha' with h | h
        · exact h0 (anchor_input gates v _ h)
        · exact h1 (anchor_input gates v _ h)
    · rcases hv' with ⟨_, h0', h1', hs'⟩ | ⟨e0', ha'⟩
      · exfalso
        have e2 : (v' : ℕ) = w := st_atom gates N w _ hno hs'
        rw [← e2] at ha
        rcases ha with h | h
        · exact h0' (anchor_input gates v' _ h)
        · exact h1' (anchor_input gates v' _ h)
      · rw [e0, e0']

theorem E_down (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N)
    (k : Fin gates.length) (hop : (gates.get k).op = GateOp.or) (v : Fin N)
    (h : E gates N M p0 p1 (N + (k : ℕ)) v) :
    ∃ e ∈ (gates.get k).inputs, E gates N M p0 p1 e v := by
  rcases h with ⟨hM, h0, h1, hs⟩ | ⟨hv, ha⟩
  · rcases st_or gates N k _ hs with h | ⟨e, he, hse⟩
    · exact absurd h (by have := v.2; omega)
    · exact ⟨e, he, Or.inl ⟨hM, h0, h1, hse⟩⟩
  · rcases ha with h | h
    · obtain ⟨e, he, _, hv'⟩ := (val_or gates _ (k : ℕ) k.2 hop).1 h
      exact ⟨e, he, Or.inr ⟨hv, Or.inl hv'⟩⟩
    · obtain ⟨e, he, _, hv'⟩ := (val_or gates _ (k : ℕ) k.2 hop).1 h
      exact ⟨e, he, Or.inr ⟨hv, Or.inr hv'⟩⟩

theorem E_wit (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (hp0 : p0 ∈ M) (hp1 : p1 ∈ M) (w : ℕ) (v : Fin N)
    (h : E gates N M p0 p1 w v) :
    ∃ x : Fin N, x ∈ M ∧ ((x = v ∧ v ≠ p0 ∧ v ≠ p1) ∨ (v = p0 ∧ (x = p0 ∨ x = p1))) ∧
      ∀ X : Fin N → Bool, X x = true → val gates w X = true := by
  rcases h with ⟨hM, h0, h1, hs⟩ | ⟨hv, ha⟩
  · refine ⟨v, hM, Or.inl ⟨rfl, h0, h1⟩, ?_⟩
    intro X hX
    cases hw : val gates w X with
    | true => rfl
    | false =>
      have h2 := st_false gates N hin X w _ hw hs
      rw [val_input gates X (v : ℕ) v.2] at h2
      exact Bool.noConfusion (hX.symm.trans h2)
  · rcases ha with h | h
    · refine ⟨p0, hp0, Or.inr ⟨hv, Or.inl rfl⟩, ?_⟩
      intro X hX
      exact val_mono gates legal _ X
        (fun u hu => by have h3 := of_decide_eq_true hu; rw [h3]; exact hX) w h
    · refine ⟨p1, hp1, Or.inr ⟨hv, Or.inr rfl⟩, ?_⟩
      intro X hX
      exact val_mono gates legal _ X
        (fun u hu => by have h3 := of_decide_eq_true hu; rw [h3]; exact hX) w h

theorem two_cases (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ e ∈ l, e = a ∨ e = b := by
  match l, hl, ha, hb with
  | [], _, ha, _ => exact absurd ha (by simp)
  | [x], _, ha, hb =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | [x, y], _, ha, hb =>
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb he
    omega
  | _ :: _ :: _ :: _, hl, _, _ =>
    simp only [List.length_cons] at hl
    omega

theorem cover (gates : List Gate) (N : ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z xr : Fin N → Bool) (r : Fin N)
    (hzr : ∀ v, z v = false → xr v = true → v = r)
    (ch : Fin gates.length → ℕ)
    (hch : ∀ a : Fin gates.length, (gates.get a).op = GateOp.and →
      val gates (N + (a : ℕ)) z = false → val gates (N + (a : ℕ)) xr = true →
      ch a ∈ (gates.get a).inputs ∧ val gates (ch a) z = false) :
    ∀ w, val gates w z = false → val gates w xr = true →
      St gates N w (r : ℕ) ∨ ∃ a : Fin gates.length, (gates.get a).op = GateOp.and ∧
        val gates (N + (a : ℕ)) z = false ∧ val gates (N + (a : ℕ)) xr = true ∧
        St gates N (ch a) (r : ℕ) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h0 hr
    by_cases hwn : w < N
    · left
      rw [val_input gates _ w hwn] at h0 hr
      have h1 := hzr _ h0 hr
      rw [← h1]
      exact st_refl gates N w
    · by_cases hbig : N + gates.length ≤ w
      · rw [val_big gates xr w hbig] at hr
        exact Bool.noConfusion hr
      · have hi : w - N < gates.length := by omega
        have he : N + (w - N) = w := by omega
        rw [← he] at h0 hr ⊢
        rcases (legal gates[w - N] (List.getElem_mem hi)).1 with ha | ho
        · obtain ⟨hcm, hc0⟩ := hch ⟨w - N, hi⟩ ha h0 hr
          obtain ⟨hclt, hcr⟩ := (val_and gates xr (w - N) hi ha).1 hr _ hcm
          rcases ih (ch ⟨w - N, hi⟩) (by omega) hc0 hcr with h | h
          · exact Or.inr ⟨⟨w - N, hi⟩, ha, h0, hr, h⟩
          · exact Or.inr h
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates xr (w - N) hi ho).1 hr
          have hj0 : val gates j z = false := by
            cases hv0 : val gates j z with
            | false => rfl
            | true =>
              have ht := (val_or gates z (w - N) hi ho).2 ⟨j, hj, hjlt, hv0⟩
              rw [ht] at h0
              exact Bool.noConfusion h0
          rcases ih j (by omega) hj0 hv with h | h
          · exact Or.inl (st_up gates N ⟨w - N, hi⟩ ho j hj _ h)
          · exact Or.inr h

theorem step (N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hint : ∀ t : Fin N, t ≠ i0 → (L i0 ∩ L t).card = 1)
    (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (Xs : Finset (Fin gates.length))
    (hXs : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
      val gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      (∀ t : Fin N, t ≠ i0 → val gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
      ¬ ∀ e ∈ (gates.get g).inputs, (val gates e (fun v : Fin N => decide (v = p0)) = true ∨
        val gates e (fun v : Fin N => decide (v = p1)) = true)) → g ∈ Xs)
    (V : Finset (Fin N)) :
    ∀ k : ℕ, k ≤ gates.length → ∃ f : Fin N → Fin N,
      Inv gates N (L i0) p0 p1 (fun v : Fin N => decide (v ∉ L i0)) k f ∧
      V.card ≤ (V.image f).card + (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k)).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, fun g hg => absurd hg (Nat.not_lt_zero _), ?_⟩
    rw [Finset.image_id]
    exact Nat.le_add_right _ _
  | succ k ih =>
    intro hk
    obtain ⟨f, hI, hc⟩ := ih (by omega)
    have hmono : (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k)).card
        ≤ (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k + 1)).card := by
      apply Finset.card_le_card
      intro g hg
      rw [Finset.mem_filter] at hg ⊢
      exact ⟨hg.1, by omega⟩
    have hklt : k < gates.length := by omega
    by_cases hor : (gates.get ⟨k, hklt⟩).op = GateOp.or ∧
        val gates (N + k) (fun v : Fin N => decide (v ∉ L i0)) = false
    swap
    · refine ⟨f, ?_, by omega⟩
      intro g hg hop hz v v' hv hv'
      by_cases hgk : (g : ℕ) < k
      · exact hI g hgk hop hz v v' hv hv'
      · have hgeq : g = ⟨k, hklt⟩ := Fin.ext (show (g : ℕ) = k by omega)
        subst hgeq
        exact absurd ⟨hop, hz⟩ hor
    obtain ⟨hop, hz⟩ := hor
    by_cases hgood : ∀ v v' : Fin N, E gates N (L i0) p0 p1 (N + k) v →
        E gates N (L i0) p0 p1 (N + k) v' → f v = f v'
    · refine ⟨f, ?_, by omega⟩
      intro g hg hop' hz' v v' hv hv'
      by_cases hgk : (g : ℕ) < k
      · exact hI g hgk hop' hz' v v' hv hv'
      · have hgeq : g = ⟨k, hklt⟩ := Fin.ext (show (g : ℕ) = k by omega)
        subst hgeq
        exact hgood v v' hv hv'
    · push_neg at hgood
      obtain ⟨v, v', hv, hv', hne⟩ := hgood
      have hinz : ∀ e ∈ (gates.get ⟨k, hklt⟩).inputs,
          val gates e (fun v : Fin N => decide (v ∉ L i0)) = false := by
        intro e he
        cases hv0 : val gates e (fun v : Fin N => decide (v ∉ L i0)) with
        | false => rfl
        | true =>
          have ht := (val_or gates (fun v : Fin N => decide (v ∉ L i0)) k hklt hop).2
            ⟨e, he, hin ⟨k, hklt⟩ e he, hv0⟩
          rw [ht] at hz
          exact Bool.noConfusion hz
      have hsame : ∀ e ∈ (gates.get ⟨k, hklt⟩).inputs, ∀ a b : Fin N,
          E gates N (L i0) p0 p1 e a → E gates N (L i0) p0 p1 e b → f a = f b :=
        fun e he a b ha hb => E_same gates N (L i0) p0 p1 _ k f hI e (hin ⟨k, hklt⟩ e he)
          (hinz e he) a b ha hb
      obtain ⟨ea, hea, hEa⟩ := E_down gates N (L i0) p0 p1 ⟨k, hklt⟩ hop v hv
      obtain ⟨eb, heb, hEb⟩ := E_down gates N (L i0) p0 p1 ⟨k, hklt⟩ hop v' hv'
      have hab : ea ≠ eb := by
        intro h
        rw [← h] at hEb
        exact hne (hsame ea hea v v' hEa hEb)
      have hall := two_cases _ (legal _ (List.get_mem gates ⟨k, hklt⟩)).2 ea eb hea heb hab
      have hcl : ∀ u : Fin N, E gates N (L i0) p0 p1 (N + k) u → f u = f v ∨ f u = f v' := by
        intro u hu
        obtain ⟨eu, heu, hEu⟩ := E_down gates N (L i0) p0 p1 ⟨k, hklt⟩ hop u hu
        rcases hall eu heu with h | h
        · rw [h] at hEu
          exact Or.inl (hsame ea hea u v hEu hEa)
        · rw [h] at hEu
          exact Or.inr (hsame eb heb u v' hEu hEb)
      have hmem : (⟨k, hklt⟩ : Fin gates.length) ∈ Xs := by
        apply hXs
        refine ⟨hop, hz, ?_, ?_⟩
        · intro t ht
          obtain ⟨x, hxM, hxc, hxv⟩ :=
            E_wit gates N (L i0) p0 p1 legal hin hp0 hp1 (N + k) v hv
          obtain ⟨x', hxM', hxc', hxv'⟩ :=
            E_wit gates N (L i0) p0 p1 legal hin hp0 hp1 (N + k) v' hv'
          have hvv : v ≠ v' := fun h => hne (by rw [h])
          have hxx : x ≠ x' := by
            intro h
            rcases hxc with ⟨e1, a0, a1⟩ | ⟨e1, a⟩
            · rcases hxc' with ⟨e2, b0, b1⟩ | ⟨e2, b⟩
              · exact hvv (e1.symm.trans (h.trans e2))
              · rcases b with b | b
                · exact a0 (e1.symm.trans (h.trans b))
                · exact a1 (e1.symm.trans (h.trans b))
            · rcases hxc' with ⟨e2, b0, b1⟩ | ⟨e2, b⟩
              · rcases a with a | a
                · exact b0 (e2.symm.trans (h.symm.trans a))
                · exact b1 (e2.symm.trans (h.symm.trans a))
              · exact hvv (e1.trans e2.symm)
          have hoff : x ∉ L t ∨ x' ∉ L t := by
            by_contra hcon
            push_neg at hcon
            have h1 := hint t ht
            exact hxx (Finset.card_le_one.1 (le_of_eq h1) x (Finset.mem_inter.2 ⟨hxM, hcon.1⟩)
              x' (Finset.mem_inter.2 ⟨hxM', hcon.2⟩))
          rcases hoff with h | h
          · exact hxv _ (decide_eq_true h)
          · exact hxv' _ (decide_eq_true h)
        · intro hanch
          have h1 : f v = f p0 := hsame ea hea v p0 hEa (Or.inr ⟨rfl, hanch ea hea⟩)
          have h2 : f v' = f p0 := hsame eb heb v' p0 hEb (Or.inr ⟨rfl, hanch eb heb⟩)
          exact hne (h1.trans h2.symm)
      have hf' : ∃ f' : Fin N → Fin N, ∀ x, f' x = if f x = f v' then f v else f x :=
        ⟨_, fun _ => rfl⟩
      obtain ⟨f', hf'⟩ := hf'
      have hnew : ∀ u : Fin N, E gates N (L i0) p0 p1 (N + k) u → f' u = f v := by
        intro u hu
        rw [hf']
        rcases hcl u hu with h | h
        · rw [h]
          exact ite_self _
        · rw [if_pos h]
      refine ⟨f', ?_, ?_⟩
      · intro g hg hop' hz' a b ha hb
        by_cases hgk : (g : ℕ) < k
        · have h3 := hI g hgk hop' hz' a b ha hb
          rw [hf', hf', h3]
        · have hgeq : g = ⟨k, hklt⟩ := Fin.ext (show (g : ℕ) = k by omega)
          subst hgeq
          rw [hnew a ha, hnew b hb]
      · have hA : (V.image f).card ≤ (V.image f').card + 1 := by
          refine (Finset.card_le_card ?_).trans (Finset.card_insert_le (f v') _)
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
          by_cases h : f x = f v'
          · rw [h]
            exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨x, hx, ?_⟩)
            rw [hf', if_neg h]
        have hB : (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k)).card + 1
            ≤ (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k + 1)).card := by
          have hnot : (⟨k, hklt⟩ : Fin gates.length) ∉
              Xs.filter (fun g : Fin gates.length => (g : ℕ) < k) := by
            intro h
            exact Nat.lt_irrefl k (Finset.mem_filter.1 h).2
          rw [← Finset.card_insert_of_notMem hnot]
          apply Finset.card_le_card
          intro g hg
          rcases Finset.mem_insert.1 hg with h | h
          · rw [h]
            exact Finset.mem_filter.2 ⟨hmem, Nat.lt_succ_self k⟩
          · rw [Finset.mem_filter] at h ⊢
            exact ⟨h.1, by omega⟩
        omega

theorem main (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hcard : (L i0).card = q + 1)
    (hint : ∀ t : Fin N, t ≠ i0 → (L i0 ∩ L t).card = 1)
    (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (o0 : ℕ)
    (hoz : val gates o0 (fun v : Fin N => decide (v ∉ L i0)) = false)
    (ho0 : val gates o0 (fun v : Fin N => decide (v = p0)) = true)
    (hor : ∀ r ∈ L i0, r ≠ p0 → r ≠ p1 →
      val gates o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true)
    (ch : Fin gates.length → ℕ)
    (hch : ∀ a : Fin gates.length, ((gates.get a).op = GateOp.and ∧
      val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
        val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
      ch a ∈ (gates.get a).inputs ∧ val gates (ch a) (fun v : Fin N => decide (v ∉ L i0)) = false)
    (Au Xs : Finset (Fin gates.length))
    (hAu : ∀ a : Fin gates.length, (((gates.get a).op = GateOp.and ∧
      val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
        val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) ∧
      ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
        val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true ∧
        St gates N (ch a) (r : ℕ)) → a ∈ Au)
    (hXs : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
      val gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      (∀ t : Fin N, t ≠ i0 → val gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
      ¬ ∀ e ∈ (gates.get g).inputs, (val gates e (fun v : Fin N => decide (v = p0)) = true ∨
        val gates e (fun v : Fin N => decide (v = p1)) = true)) → g ∈ Xs) :
    q - 1 ≤ Au.card + Xs.card := by
  classical
  obtain ⟨f, hI, hc⟩ := step N L i0 p0 p1 hint hp0 hp1 gates legal hin Xs hXs
    ((L i0).erase p1) gates.length le_rfl
  have hVc := Finset.card_erase_of_mem hp1
  have hfil : (Xs.filter (fun g : Fin gates.length => (g : ℕ) < gates.length)).card ≤ Xs.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hex : ∃ ρ : Fin gates.length → Fin N, ∀ a : Fin gates.length, ∀ r : Fin N,
      r ∈ L i0 → r ≠ p0 → r ≠ p1 → St gates N (ch a) (r : ℕ) →
      (ρ a ∈ L i0 ∧ ρ a ≠ p0 ∧ ρ a ≠ p1 ∧ St gates N (ch a) (ρ a : ℕ)) := by
    refine ⟨fun a => if h : ∃ r : Fin N, r ∈ L i0 ∧ r ≠ p0 ∧ r ≠ p1 ∧
      St gates N (ch a) (r : ℕ) then h.choose else p0, ?_⟩
    intro a r h1 h2 h3 h4
    have h : ∃ r : Fin N, r ∈ L i0 ∧ r ≠ p0 ∧ r ≠ p1 ∧ St gates N (ch a) (r : ℕ) :=
      ⟨r, h1, h2, h3, h4⟩
    simp only [dif_pos h]
    exact h.choose_spec
  obtain ⟨ρ, hρ⟩ := hex
  have himg : ((L i0).erase p1).image f ⊆ insert (f p0) (Au.image (fun a => f (ρ a))) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hx1, hxM⟩ := Finset.mem_erase.1 hx
    by_cases hx0 : x = p0
    · rw [hx0]
      exact Finset.mem_insert_self _ _
    · have hzr : ∀ v : Fin N, (fun v : Fin N => decide (v ∉ L i0)) v = false →
          (fun v : Fin N => decide (v ∉ L i0 ∨ v = x)) v = true → v = x := by
        intro v h1 h2
        have a1 : ¬ (v ∉ L i0) := of_decide_eq_false h1
        have a2 : v ∉ L i0 ∨ v = x := of_decide_eq_true h2
        exact a2.resolve_left a1
      rcases cover gates N legal _ _ x hzr ch
        (fun a ha h0 hr => hch a ⟨ha, h0, x, hxM, hx0, hx1, hr⟩) o0 hoz (hor x hxM hx0 hx1)
        with hs | ⟨a, ha, h0, hr, hs⟩
      · have ho_lt : o0 < N + gates.length := by
          by_contra hcon
          rw [val_big gates _ o0 (by omega)] at ho0
          exact Bool.noConfusion ho0
        have h5 := E_same gates N (L i0) p0 p1 _ gates.length f hI o0 ho_lt hoz x p0
          (Or.inl ⟨hxM, hx0, hx1, hs⟩) (Or.inr ⟨rfl, Or.inl ho0⟩)
        rw [h5]
        exact Finset.mem_insert_self _ _
      · have hrim : (gates.get a).op = GateOp.and ∧
            val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
            ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
              val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true :=
          ⟨ha, h0, x, hxM, hx0, hx1, hr⟩
        have haA : a ∈ Au := hAu a ⟨hrim, x, hxM, hx0, hx1, hr, hs⟩
        obtain ⟨hcm, hc0⟩ := hch a hrim
        obtain ⟨r1, r2, r3, r4⟩ := hρ a x hxM hx0 hx1 hs
        have hlt : ch a < N + gates.length := by
          have h6 := hin a _ hcm
          have h7 := a.2
          omega
        have h5 := E_same gates N (L i0) p0 p1 _ gates.length f hI (ch a) hlt hc0 x (ρ a)
          (Or.inl ⟨hxM, hx0, hx1, hs⟩) (Or.inl ⟨r1, r2, r3, r4⟩)
        rw [h5]
        exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨a, haA, rfl⟩)
  have h1 := (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
  have h2 : (Au.image (fun a => f (ρ a))).card ≤ Au.card := Finset.card_image_le
  omega


theorem top : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ ch : Fin gates.length → ℕ, (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) → ch a ∈ (gates.get a).inputs ∧ ev (ch a) (fun v : Fin N => decide (v ∉ L i0)) = false) →
    ∀ Au Xs : Finset (Fin gates.length), (∀ a : Fin gates.length, (((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true ∧ St (ch a) r) → a ∈ Au) →
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true)) → g ∈ Xs) → q - 1 ≤ Au.card + Xs.card := by
  intro q N L i0 p0 p1 _ _ hcard hint _ _ hp0 hp1 gates legal _ hin ev he o0 hoz ho0 _ hor St hSt ch hch Au Xs hAu hXs
  have hev : ev = fun w x => PEqualNP.Outside.L_meta_1644.B1643.B1642.val gates w x := by
    funext w x
    rw [he]
    exact PEqualNP.Outside.L_meta_1644.B1643.B1642.eval_eq gates w _
  subst hev
  exact PEqualNP.Outside.L_meta_1644.B1643.B1642.main q N L i0 p0 p1 (hcard i0)
    (fun t ht => hint i0 t (Ne.symm ht)) hp0 hp1 gates legal hin o0 hoz ho0 hor ch hch Au Xs
    (fun a h => hAu a ⟨h.1, by
      obtain ⟨r, h1, h2, h3, h4, h5⟩ := h.2
      exact ⟨r, h1, h2, h3, h4, (hSt _ _).2 h5⟩⟩) hXs

end B1642

lemma vg_and {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (i : Fin gates.length)
    (hop : (gates.get i).op = GateOp.and) :
    vl gates x (N + (i : ℕ)) = true ↔
      ∀ r ∈ (gates.get i).inputs, r < N + (i : ℕ) ∧ vl gates x r = true := by
  have e : N + (i : ℕ) - N = i := by omega
  have h := vl_and gates x (N + (i : ℕ)) (Nat.le_add_right _ _) (by have := i.2; omega)
    (by simp only [e]; exact hop)
  simp only [e] at h
  exact h

lemma vg_or {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (i : Fin gates.length)
    (hop : (gates.get i).op = GateOp.or) :
    vl gates x (N + (i : ℕ)) = true ↔
      ∃ r ∈ (gates.get i).inputs, r < N + (i : ℕ) ∧ vl gates x r = true := by
  have e : N + (i : ℕ) - N = i := by omega
  have h := vl_or gates x (N + (i : ℕ)) (Nat.le_add_right _ _) (by have := i.2; omega)
    (by simp only [e]; exact hop)
  simp only [e] at h
  exact h

lemma two_mem (l : List ℕ) (hl : l.length ≤ 2) (a e e' : ℕ) (ha : a ∈ l) (he : e ∈ l)
    (he' : e' ∈ l) (h1 : e ≠ a) (h2 : e' ≠ a) : e = e' := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha he he'
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha he he'
    omega
  · simp only [List.length_cons] at hl
    omega

lemma two_cover (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ e ∈ l, e = a ∨ e = b := by
  intro e he
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb he
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb he
    omega
  · simp only [List.length_cons] at hl
    omega

def CT (N : ℕ) (gates : List Gate) (w : ℕ) : Prop := ∀ x : Fin N → Bool, vl gates x w = true

def CF (N : ℕ) (gates : List Gate) (w : ℕ) : Prop := ∀ x : Fin N → Bool, vl gates x w = false

lemma normalize {N : ℕ} (hNpos : 0 < N) (gates : List Gate)
    (hg : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) :
    ∃ gates' : List Gate,
      gates'.length = gates.length ∧
      (∀ gt ∈ gates', (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
      (∀ i : Fin gates'.length, 1 ≤ (gates'.get i).inputs.length) ∧
      (∀ (i : Fin gates'.length), ∀ w ∈ (gates'.get i).inputs, w < N + (i : ℕ)) ∧
      ∀ w : ℕ, ¬ CT N gates w → ¬ CF N gates w →
        ∀ x : Fin N → Bool, vl gates' x w = vl gates x w := by
  classical
  have opi : ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or :=
    fun i => (hg _ (List.getElem_mem i.2)).1
  have hFex : ∀ i : Fin gates.length, ∃ G : Gate,
      ((CT N gates (N + (i : ℕ)) ∨ CF N gates (N + (i : ℕ))) → G = ⟨GateOp.or, [0]⟩) ∧
      (¬ (CT N gates (N + (i : ℕ)) ∨ CF N gates (N + (i : ℕ))) → (gates.get i).op = GateOp.and →
        G = ⟨GateOp.and, (gates.get i).inputs.filter (fun r => decide (¬ CT N gates r))⟩) ∧
      (¬ (CT N gates (N + (i : ℕ)) ∨ CF N gates (N + (i : ℕ))) → (gates.get i).op = GateOp.or →
        G = ⟨GateOp.or, (gates.get i).inputs.filter (fun r => decide (¬ CF N gates r))⟩) := by
    intro i
    by_cases hcst : CT N gates (N + (i : ℕ)) ∨ CF N gates (N + (i : ℕ))
    · exact ⟨⟨GateOp.or, [0]⟩, fun _ => rfl, fun h => absurd hcst h, fun h => absurd hcst h⟩
    · rcases opi i with hop | hop
      · refine ⟨⟨GateOp.and, (gates.get i).inputs.filter (fun r => decide (¬ CT N gates r))⟩,
          fun h => absurd h hcst, fun _ _ => rfl, fun _ h => ?_⟩
        rw [hop] at h
        cases h
      · refine ⟨⟨GateOp.or, (gates.get i).inputs.filter (fun r => decide (¬ CF N gates r))⟩,
          fun h => absurd h hcst, fun _ h => ?_, fun _ _ => rfl⟩
        rw [hop] at h
        cases h
  choose F hF1 hF2 hF3 using hFex
  obtain ⟨gates', hlen, hget⟩ : ∃ gates' : List Gate, ∃ hlen : gates'.length = gates.length,
      ∀ (i : ℕ) (hi : i < gates.length), gates'[i]'(by rw [hlen]; exact hi) = F ⟨i, hi⟩ :=
    ⟨List.ofFn F, by simp, by intro i hi; simp⟩
  have spec : ∀ (i : ℕ) (hi : i < gates.length),
      ((gates'[i]'(by rw [hlen]; exact hi)).op = GateOp.and ∨
        (gates'[i]'(by rw [hlen]; exact hi)).op = GateOp.or) ∧
      (gates'[i]'(by rw [hlen]; exact hi)).inputs.length ≤ 2 ∧
      1 ≤ (gates'[i]'(by rw [hlen]; exact hi)).inputs.length ∧
      ∀ w ∈ (gates'[i]'(by rw [hlen]; exact hi)).inputs, w < N + i := by
    intro i hi
    by_cases hcst : CT N gates (N + i) ∨ CF N gates (N + i)
    · rw [hget i hi, hF1 ⟨i, hi⟩ hcst]
      refine ⟨Or.inr rfl, by simp, by simp, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      omega
    · rcases opi ⟨i, hi⟩ with hop | hop
      · rw [hget i hi, hF2 ⟨i, hi⟩ hcst hop]
        refine ⟨Or.inl rfl, le_trans (List.length_filter_le _ _) (hg _ (List.getElem_mem hi)).2, ?_,
          fun w hw => hwf ⟨i, hi⟩ w (List.mem_filter.mp hw).1⟩
        by_contra hcon
        have hnil := List.eq_nil_of_length_eq_zero
          (show ((gates.get ⟨i, hi⟩).inputs.filter (fun r => decide (¬ CT N gates r))).length = 0 by
            simp only [] at hcon; omega)
        apply hcst
        left
        intro x
        rw [vg_and gates x ⟨i, hi⟩ hop]
        intro r hr
        refine ⟨hwf ⟨i, hi⟩ r hr, ?_⟩
        have h3 := List.filter_eq_nil_iff.mp hnil r hr
        simp only [decide_eq_true_eq, not_not] at h3
        exact h3 x
      · rw [hget i hi, hF3 ⟨i, hi⟩ hcst hop]
        refine ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) (hg _ (List.getElem_mem hi)).2, ?_,
          fun w hw => hwf ⟨i, hi⟩ w (List.mem_filter.mp hw).1⟩
        by_contra hcon
        have hnil := List.eq_nil_of_length_eq_zero
          (show ((gates.get ⟨i, hi⟩).inputs.filter (fun r => decide (¬ CF N gates r))).length = 0 by
            simp only [] at hcon; omega)
        apply hcst
        right
        intro x
        by_contra hx
        have hx' : vl gates x (N + i) = true := by simpa using hx
        obtain ⟨r, hr, _, hrv⟩ := (vg_or gates x ⟨i, hi⟩ hop).mp hx'
        have h3 := List.filter_eq_nil_iff.mp hnil r hr
        simp only [decide_eq_true_eq, not_not] at h3
        rw [h3 x] at hrv
        exact Bool.noConfusion hrv
  refine ⟨gates', hlen, ?_, ?_, ?_, ?_⟩
  · intro gt hgt
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgt
    have h := spec j (by rw [← hlen]; exact hj)
    exact ⟨h.1, h.2.1⟩
  · intro i
    exact (spec i.1 (by rw [← hlen]; exact i.2)).2.2.1
  · intro i w hw
    exact (spec i.1 (by rw [← hlen]; exact i.2)).2.2.2 w hw
  · intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hnt hnf x
      by_cases hin : w < N
      · rw [vl_input gates' x w hin, vl_input gates x w hin]
      · by_cases hlt : w < N + gates.length
        · obtain ⟨I, hI⟩ : ∃ I : Fin gates.length, (I : ℕ) = w - N := ⟨⟨w - N, by omega⟩, rfl⟩
          have hw : N + (I : ℕ) = w := by omega
          have hI'lt : (I : ℕ) < gates'.length := by rw [hlen]; exact I.2
          have hcst : ¬ (CT N gates (N + (I : ℕ)) ∨ CF N gates (N + (I : ℕ))) := by
            rw [hw]
            tauto
          have hG' : gates'.get ⟨(I : ℕ), hI'lt⟩ = F I := hget (I : ℕ) I.2
          rcases opi I with hop | hop
          · have hGa := hF2 I hcst hop
            have hop' : (gates'.get ⟨(I : ℕ), hI'lt⟩).op = GateOp.and := by rw [hG', hGa]
            have h1 := vg_and gates' x ⟨(I : ℕ), hI'lt⟩ hop'
            rw [hG', hGa] at h1
            have h1' : vl gates' x w = true ↔
                ∀ r ∈ (gates.get I).inputs.filter (fun r => decide (¬ CT N gates r)),
                  r < w ∧ vl gates' x r = true := by
              rw [← hw]
              exact h1
            have gand : ∀ x' : Fin N → Bool, vl gates x' w = true ↔
                ∀ r ∈ (gates.get I).inputs, r < w ∧ vl gates x' r = true := by
              intro x'
              rw [← hw]
              exact vg_and gates x' I hop
            have hnfin : ∀ r ∈ (gates.get I).inputs, ¬ CF N gates r := by
              intro r hr hcf
              apply hnf
              intro x'
              by_contra hx'
              have ht : vl gates x' w = true := by simpa using hx'
              have h5 := ((gand x').mp ht r hr).2
              rw [hcf x'] at h5
              exact Bool.noConfusion h5
            rw [Bool.eq_iff_iff, h1', gand x]
            constructor
            · intro H r hr
              have hrw := hwf I r hr
              refine ⟨by omega, ?_⟩
              by_cases hct : CT N gates r
              · exact hct x
              · have hmem : r ∈ (gates.get I).inputs.filter (fun r => decide (¬ CT N gates r)) :=
                  List.mem_filter.mpr ⟨hr, by simpa using hct⟩
                rw [← ih r (by omega) hct (hnfin r hr) x]
                exact (H r hmem).2
            · intro H r hr
              have hr' := List.mem_filter.mp hr
              have hct : ¬ CT N gates r := by simpa using hr'.2
              have h6 := H r hr'.1
              refine ⟨h6.1, ?_⟩
              rw [ih r (by omega) hct (hnfin r hr'.1) x]
              exact h6.2
          · have hGa := hF3 I hcst hop
            have hop' : (gates'.get ⟨(I : ℕ), hI'lt⟩).op = GateOp.or := by rw [hG', hGa]
            have h1 := vg_or gates' x ⟨(I : ℕ), hI'lt⟩ hop'
            rw [hG', hGa] at h1
            have h1' : vl gates' x w = true ↔
                ∃ r ∈ (gates.get I).inputs.filter (fun r => decide (¬ CF N gates r)),
                  r < w ∧ vl gates' x r = true := by
              rw [← hw]
              exact h1
            have gor : ∀ x' : Fin N → Bool, vl gates x' w = true ↔
                ∃ r ∈ (gates.get I).inputs, r < w ∧ vl gates x' r = true := by
              intro x'
              rw [← hw]
              exact vg_or gates x' I hop
            have hntin : ∀ r ∈ (gates.get I).inputs, ¬ CT N gates r := by
              intro r hr hct
              apply hnt
              intro x'
              have hrw := hwf I r hr
              exact (gor x').mpr ⟨r, hr, by omega, hct x'⟩
            rw [Bool.eq_iff_iff, h1', gor x]
            constructor
            · rintro ⟨r, hr, hrw, hv⟩
              have hr' := List.mem_filter.mp hr
              have hcf : ¬ CF N gates r := by simpa using hr'.2
              refine ⟨r, hr'.1, hrw, ?_⟩
              rw [← ih r hrw (hntin r hr'.1) hcf x]
              exact hv
            · rintro ⟨r, hr, hrw, hv⟩
              have hcf : ¬ CF N gates r := by
                intro hcf
                rw [hcf x] at hv
                exact Bool.noConfusion hv
              refine ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hcf⟩, hrw, ?_⟩
              rw [ih r hrw (hntin r hr) hcf x]
              exact hv
        · rw [vl_missing gates' x w (by rw [hlen]; omega), vl_missing gates x w (by omega)]

lemma count_abs {G ι : Type*} [Fintype G] [DecidableEq G] [DecidableEq ι] (A : Finset ι)
    (I : ι → Finset G) (P Q : ι → Prop) (K : Finset G) (hPQ : ∀ t, ¬ (P t ∧ Q t))
    (hpair : ∀ g, ∀ t ∈ A, ∀ s ∈ A, t ≠ s → g ∈ I t → g ∈ I s →
      g ∈ K ∧ ((P t ∧ Q s) ∨ (Q t ∧ P s))) :
    ∑ t ∈ A, (I t).card ≤ (A.biUnion I).card + K.card := by
  classical
  have key : ∀ g : G, (∑ t ∈ A, if g ∈ I t then 1 else 0) ≤
      (if g ∈ A.biUnion I then 1 else 0) + (if g ∈ K then 1 else 0) := by
    intro g
    rw [← Finset.card_filter]
    have hB : g ∉ A.biUnion I → (A.filter (fun t => g ∈ I t)).card = 0 := by
      intro h
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t ht hgt
      exact h (Finset.mem_biUnion.mpr ⟨t, ht, hgt⟩)
    have hK2 : (A.filter (fun t => g ∈ I t)).card ≤ 2 := by
      by_contra hcon
      have h3 : 2 < (A.filter (fun t => g ∈ I t)).card := by omega
      obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
      rw [Finset.mem_filter] at ha hb hc
      have e1 := (hpair g a ha.1 b hb.1 hab ha.2 hb.2).2
      have e2 := (hpair g a ha.1 c hc.1 hac ha.2 hc.2).2
      have e3 := (hpair g b hb.1 c hc.1 hbc hb.2 hc.2).2
      have f1 := hPQ a
      have f2 := hPQ b
      have f3 := hPQ c
      tauto
    have hK1 : g ∉ K → (A.filter (fun t => g ∈ I t)).card ≤ 1 := by
      intro h
      apply Finset.card_le_one.mpr
      intro a ha b hb
      by_contra hab
      rw [Finset.mem_filter] at ha hb
      exact h (hpair g a ha.1 b hb.1 hab ha.2 hb.2).1
    by_cases hgB : g ∈ A.biUnion I
    · by_cases hgK : g ∈ K
      · rw [if_pos hgB, if_pos hgK]
        omega
      · rw [if_pos hgB, if_neg hgK]
        have := hK1 hgK
        omega
    · have := hB hgB
      omega
  calc ∑ t ∈ A, (I t).card = ∑ t ∈ A, ∑ g : G, (if g ∈ I t then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.card_eq_sum_ones]
    _ = ∑ g : G, ∑ t ∈ A, (if g ∈ I t then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ g : G, ((if g ∈ A.biUnion I then 1 else 0) + (if g ∈ K then 1 else 0)) :=
        Finset.sum_le_sum (fun g _ => key g)
    _ = (A.biUnion I).card + K.card := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.univ_inter, ← Finset.card_eq_sum_ones, ← Finset.card_eq_sum_ones]

lemma five {G : Type*} [Fintype G] [DecidableEq G] (B Gh Au Xs : Finset G) (gs : G)
    (d1 : Disjoint B Gh) (d2 : Disjoint B Au) (d3 : Disjoint B Xs) (d4 : gs ∉ B)
    (d5 : Disjoint Gh Au) (d6 : Disjoint Gh Xs) (d7 : gs ∉ Gh) (d8 : Disjoint Au Xs)
    (d9 : gs ∉ Au) (d10 : gs ∉ Xs) :
    B.card + Gh.card + Au.card + Xs.card + 1 ≤ Fintype.card G := by
  have h := Finset.card_le_univ (insert gs (B ∪ Gh ∪ Au ∪ Xs))
  rw [Finset.card_insert_of_notMem (by simp [d4, d7, d9, d10]),
    Finset.card_union_of_disjoint (by simp [Finset.disjoint_union_left, d3, d6, d8]),
    Finset.card_union_of_disjoint (by simp [Finset.disjoint_union_left, d2, d5]),
    Finset.card_union_of_disjoint d1] at h
  exact h

def zt {N : ℕ} (L : Fin N → Finset (Fin N)) (t : Fin N) : Fin N → Bool :=
  fun v => decide (v ∉ L t)

def sgp {N : ℕ} (p : Fin N) : Fin N → Bool := fun v => decide (v = p)

def zrr {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 r : Fin N) : Fin N → Bool :=
  fun v => decide (v ∉ L i0 ∨ v = r)

def Tt {N : ℕ} (L : Fin N → Finset (Fin N)) (p0 p1 t p : Fin N) : Fin N → Bool := fun v =>
  decide (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
    (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))

def ClP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (p0 p1 t : Fin N) (j : ℕ)
    (X : Finset (Fin N)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = GateOp.or →
    vl gates (zt L t) (N + (i : ℕ)) = false →
    ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
      (vl gates (Tt L p0 p1 t s) c1 = true ∨ vl gates (Tt L p0 p1 t s) c2 = true) →
      (vl gates (Tt L p0 p1 t s') c1 = true ∨ vl gates (Tt L p0 p1 t s') c2 = true) →
      (s ∈ X ↔ s' ∈ X)

def MgP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (p0 p1 t : Fin N)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ vl gates (zt L t) (N + (g : ℕ)) = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L t, ∃ r' ∈ L t,
      vl gates (Tt L p0 p1 t r) w1 = true ∧ vl gates (Tt L p0 p1 t r') w2 = true ∧
      ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ ClP gates L p0 p1 t (g : ℕ) X

def EqvP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (p0 p1 t : Fin N) (j : ℕ)
    (s r : Fin N) : Prop :=
  ∀ X : Finset (Fin N), ClP gates L p0 p1 t j X → (s ∈ X ↔ r ∈ X)

lemma eqv_symm {N : ℕ} {gates : List Gate} {L : Fin N → Finset (Fin N)} {p0 p1 t : Fin N} {j : ℕ}
    {s r : Fin N} (h : EqvP gates L p0 p1 t j s r) : EqvP gates L p0 p1 t j r s :=
  fun X hX => (h X hX).symm

lemma eqv_trans {N : ℕ} {gates : List Gate} {L : Fin N → Finset (Fin N)} {p0 p1 t : Fin N} {j : ℕ}
    {s r u : Fin N} (h : EqvP gates L p0 p1 t j s r) (h' : EqvP gates L p0 p1 t j r u) :
    EqvP gates L p0 p1 t j s u :=
  fun X hX => (h X hX).trans (h' X hX)

lemma eqv_mono {N : ℕ} {gates : List Gate} {L : Fin N → Finset (Fin N)} {p0 p1 t : Fin N}
    {j j' : ℕ} {s r : Fin N} (hjj : j ≤ j') (h : EqvP gates L p0 p1 t j s r) :
    EqvP gates L p0 p1 t j' s r := by
  intro X hX
  apply h X
  intro i hi
  exact hX i (lt_of_lt_of_le hi hjj)

def TSP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (p0 p1 l m : Fin N)
    (w : ℕ) : Prop :=
  vl gates (zt L l) w = false ∧ vl gates (zt L m) w = false ∧
    (∃ p ∈ L l, vl gates (Tt L p0 p1 l p) w = true) ∧ ∃ p ∈ L m, vl gates (Tt L p0 p1 m p) w = true

def HgP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (p0 p1 l m : Fin N)
    (g : Fin gates.length) : Prop :=
  TSP gates L p0 p1 l m (N + (g : ℕ)) ∧ ((gates.get g).op = GateOp.and ∨
    ((gates.get g).op = GateOp.or ∧ ∀ e ∈ (gates.get g).inputs, ¬ TSP gates L p0 p1 l m e))

def StP {N : ℕ} (gates : List Gate) (w : ℕ) (p : Fin N) : Prop :=
  ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs →
    (gates.get k).op = GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs

def K0P {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (a : Fin gates.length) : Prop :=
  (gates.get a).op = GateOp.and ∧ vl gates (zt L i0) (N + (a : ℕ)) = false ∧
    ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ vl gates (zrr L i0 r) (N + (a : ℕ)) = true

def AuP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (ch : Fin gates.length → ℕ) (a : Fin gates.length) : Prop :=
  K0P gates L i0 p0 p1 a ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
    vl gates (zrr L i0 r) (N + (a : ℕ)) = true ∧ StP gates (ch a) r

def XsP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ vl gates (zt L i0) (N + (g : ℕ)) = false ∧
    (∀ t : Fin N, t ≠ i0 → vl gates (zt L t) (N + (g : ℕ)) = true) ∧
    ¬ ∀ e ∈ (gates.get g).inputs, (vl gates (sgp p0) e = true ∨ vl gates (sgp p1) e = true)

def LeafP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (p0 p1 : Fin N)
    (Au : Finset (Fin gates.length)) (l m : Fin N) (ν : ℕ) : Prop :=
  (∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨
    ∃ h : Fin gates.length, ν = N + (h : ℕ) ∧ HgP gates L p0 p1 l m h ∧ h ∉ Au

def TouchP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (p0 p1 l : Fin N)
    (j ν : ℕ) (r : Fin N) : Prop :=
  ∃ s ∈ L l, vl gates (Tt L p0 p1 l s) ν = true ∧ EqvP gates L p0 p1 l j s r

def QP {N : ℕ} (gates : List Gate) (L : Fin N → Finset (Fin N)) (p0 p1 : Fin N)
    (Au : Finset (Fin gates.length)) (l m : Fin N) (g h : Fin gates.length) : Prop :=
  vl gates (zt L l) (N + (h : ℕ)) = false ∧ ∃ ra ∈ L l, ∃ rb ∈ L l, ∃ μ : ℕ,
    LeafP gates L p0 p1 Au l m μ ∧ μ < N + (h : ℕ) ∧ (h : ℕ) < (g : ℕ) ∧
    TouchP gates L p0 p1 l (g : ℕ) (N + (h : ℕ)) ra ∧ TouchP gates L p0 p1 l (g : ℕ) μ rb ∧
    (∀ j : ℕ, (g : ℕ) < j → EqvP gates L p0 p1 l j ra rb) ∧
    ∀ ν' : ℕ, LeafP gates L p0 p1 Au l m ν' → ν' < N + (g : ℕ) →
      TouchP gates L p0 p1 l (g : ℕ) ν' ra → N + (h : ℕ) ≤ ν'

lemma St_true {N : ℕ} (gates : List Gate)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (w : ℕ) (p : Fin N) (h : StP gates w p) (x : Fin N → Bool) (hx : x p = true) :
    vl gates x w = true := by
  by_contra hcon
  have hf : vl gates x w = false := by simpa using hcon
  have h2 : vl gates x (p : ℕ) = false := h {k | vl gates x k = false} hf (by
    intro k hk hop e he
    show vl gates x e = false
    by_contra hc2
    have ht : vl gates x e = true := by simpa using hc2
    have h3 := (vg_or gates x k hop).mpr ⟨e, he, hwf k e he, ht⟩
    have hk' : vl gates x (N + (k : ℕ)) = false := hk
    rw [h3] at hk'
    exact Bool.noConfusion hk')
  rw [vl_input gates x p p.2] at h2
  have h3 : x p = false := h2
  rw [hx] at h3
  exact Bool.noConfusion h3

lemma lower_nc (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hq : 3 ≤ q) (hN : N = q ^ 2 + q + 1) (hL : ∀ i : Fin N, (L i).card = q + 1)
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hP : ∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i)
    (hne : p0 ≠ p1) (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (gates : List Gate) (o : Fin N → ℕ)
    (hg : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hc : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (hev : ∀ (t : Fin N) (x : Fin N → Bool),
      (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        vl gates x (o t) = decide (∃ v ∈ L t, x v = true)) :
    N * q ≤ gates.length := by
  classical
  have hg1 : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  have mono : ∀ (x y : Fin N → Bool), (∀ v, x v = true → y v = true) →
      ∀ w, vl gates x w = true → vl gates y w = true := fun x y h => vl_mono gates hg1 x y h
  have iu : ∀ i j : Fin N, i ≠ j → ∀ a b, a ∈ L i → a ∈ L j → b ∈ L i → b ∈ L j → a = b := by
    intro i j hij a b ha ha' hb hb'
    exact Finset.card_le_one.mp (hI i j hij).le a (Finset.mem_inter.mpr ⟨ha, ha'⟩) b
      (Finset.mem_inter.mpr ⟨hb, hb'⟩)
  have two_off : ∀ t : Fin N, t ≠ i0 → ¬ (p0 ∈ L t ∧ p1 ∈ L t) := by
    intro t ht h
    exact hne (iu t i0 ht p0 p1 h.1 hp0 h.2 hp1)
  have lne : ∀ l : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → l ≠ i0 := by
    intro l hl h
    rw [h] at hl
    exact hl.2 hp1
  have mne : ∀ m : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → m ≠ i0 := by
    intro m hm h
    rw [h] at hm
    exact hm.2 hp0
  have opi : ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or :=
    fun i => hg1 _ (List.getElem_mem i.2)
  have orT : ∀ (i : Fin gates.length), (gates.get i).op = GateOp.or → ∀ (x : Fin N → Bool) (e : ℕ),
      e ∈ (gates.get i).inputs → vl gates x e = true → vl gates x (N + (i : ℕ)) = true :=
    fun i hop x e he hv => (vg_or gates x i hop).mpr ⟨e, he, hwf i e he, hv⟩
  have orF : ∀ (i : Fin gates.length), (gates.get i).op = GateOp.or → ∀ (x : Fin N → Bool),
      vl gates x (N + (i : ℕ)) = false → ∀ e ∈ (gates.get i).inputs, vl gates x e = false := by
    intro i hop x hx e he
    by_contra hcon
    have h3 : vl gates x e = true := by simpa using hcon
    rw [orT i hop x e he h3] at hx
    exact Bool.noConfusion hx
  have orE : ∀ (i : Fin gates.length), (gates.get i).op = GateOp.or → ∀ (x : Fin N → Bool),
      vl gates x (N + (i : ℕ)) = true → ∃ e ∈ (gates.get i).inputs, vl gates x e = true := by
    intro i hop x hx
    obtain ⟨e, he, _, hv⟩ := (vg_or gates x i hop).mp hx
    exact ⟨e, he, hv⟩
  have andT : ∀ (i : Fin gates.length), (gates.get i).op = GateOp.and → ∀ (x : Fin N → Bool),
      vl gates x (N + (i : ℕ)) = true → ∀ e ∈ (gates.get i).inputs, vl gates x e = true :=
    fun i hop x hx e he => ((vg_and gates x i hop).mp hx e he).2
  have andF : ∀ (i : Fin gates.length), (gates.get i).op = GateOp.and → ∀ (x : Fin N → Bool),
      vl gates x (N + (i : ℕ)) = false → ∃ e ∈ (gates.get i).inputs, vl gates x e = false := by
    intro i hop x hx
    by_contra hcon
    push Not at hcon
    have h3 : vl gates x (N + (i : ℕ)) = true :=
      (vg_and gates x i hop).mpr (fun e he => ⟨hwf i e he, by simpa using hcon e he⟩)
    rw [h3] at hx
    exact Bool.noConfusion hx
  have Tiff : ∀ t p v : Fin N, Tt L p0 p1 t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨
      (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t)) := fun t p v => by
    unfold Tt
    exact decide_eq_true_iff
  have ztT : ∀ t v : Fin N, zt L t v = true ↔ v ∉ L t := fun t v => by
    unfold zt
    exact decide_eq_true_iff
  have tz : ∀ (t s p : Fin N) (w : ℕ), vl gates (Tt L p0 p1 t p) w = true →
      vl gates (zt L s) w = false → ∃ v, Tt L p0 p1 t p v = true ∧ v ∈ L s := by
    intro t s p w ha hb
    by_contra hcon
    push Not at hcon
    have h3 := mono (Tt L p0 p1 t p) (zt L s) (fun v hv => (ztT s v).mpr (hcon v hv)) w ha
    rw [h3] at hb
    exact Bool.noConfusion hb
  have f36a : ∀ (l m l' : Fin N), (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      (p0 ∈ L l' ∧ p1 ∉ L l') → l' ≠ l → ∀ (w : ℕ) (p : Fin N), p ∈ L l →
      vl gates (zt L m) w = false → vl gates (Tt L p0 p1 l p) w = true →
      vl gates (zt L l') w = true := by
    intro l m l' hl hm hl' hll w p hp hzm hT
    by_cases hpp : p = p0
    · exfalso
      obtain ⟨v, hv, hvm⟩ := tz l m p w hT hzm
      rw [Tiff] at hv
      rcases hv with hv | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩
      · rw [hv, hpp] at hvm
        exact hm.2 hvm
      · exact h hl.1
      · exact h hpp
      · exact hl.2 h
    · apply mono (Tt L p0 p1 l p) (zt L l') _ w hT
      intro v hv
      rw [ztT]
      rw [Tiff] at hv
      rcases hv with hv | ⟨h, _⟩ | ⟨_, _, _, hv⟩ | ⟨_, h, _⟩
      · intro hvl'
        rw [hv] at hvl'
        exact hpp (iu l l' (Ne.symm hll) p p0 hp hvl' hl.1 hl'.1)
      · exact absurd hl.1 h
      · rw [hv]
        exact hl'.2
      · exact absurd h hl.2
  have f36b : ∀ (l m m' : Fin N), (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      (p1 ∈ L m' ∧ p0 ∉ L m') → m' ≠ m → ∀ (w : ℕ) (p : Fin N), p ∈ L m →
      vl gates (zt L l) w = false → vl gates (Tt L p0 p1 m p) w = true →
      vl gates (zt L m') w = true := by
    intro l m m' hl hm hm' hmm w p hp hzl hT
    by_cases hpp : p = p1
    · exfalso
      obtain ⟨v, hv, hvl⟩ := tz m l p w hT hzl
      rw [Tiff] at hv
      rcases hv with hv | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · rw [hv, hpp] at hvl
        exact hl.2 hvl
      · exact h hpp
      · exact hm.2 h
      · exact hm.2 h
    · apply mono (Tt L p0 p1 m p) (zt L m') _ w hT
      intro v hv
      rw [ztT]
      rw [Tiff] at hv
      rcases hv with hv | ⟨_, _, hv⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · intro hvm'
        rw [hv] at hvm'
        exact hpp (iu m m' (Ne.symm hmm) p p1 hp hvm' hm.1 hm'.1)
      · rw [hv]
        exact hm'.2
      · exact absurd h hm.2
      · exact absurd h hm.2
  have f36c : ∀ (t m : Fin N), p0 ∉ L t → (p1 ∈ L m ∧ p0 ∉ L m) → t ≠ m → ∀ (w : ℕ)
      (p p' : Fin N), p ∈ L t → p' ∈ L t → p ≠ p' → vl gates (zt L m) w = false →
      vl gates (Tt L p0 p1 t p) w = true → vl gates (Tt L p0 p1 t p') w = true → False := by
    have one : ∀ (t m : Fin N), p0 ∉ L t → (p1 ∈ L m ∧ p0 ∉ L m) → ∀ (w : ℕ) (p : Fin N),
        p ∉ L m → vl gates (zt L m) w = false → vl gates (Tt L p0 p1 t p) w = true → False := by
      intro t m ht hm w p hpm hzm hT
      obtain ⟨v, hv, hvm⟩ := tz t m p w hT hzm
      rw [Tiff] at hv
      rcases hv with hv | ⟨_, _, hv⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · rw [hv] at hvm
        exact hpm hvm
      · rw [hv] at hvm
        exact hm.2 hvm
      · exact ht h
      · exact ht h
    intro t m ht hm htm w p p' hp hp' hpp hzm hT hT'
    by_cases hpm : p ∈ L m
    · by_cases hpm' : p' ∈ L m
      · exact hpp (iu t m htm p p' hp hpm hp' hpm')
      · exact one t m ht hm w p' hpm' hzm hT'
    · exact one t m ht hm w p hpm hzm hT
  have pairuniq : ∀ (l m l' m' : Fin N), (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      (p0 ∈ L l' ∧ p1 ∉ L l') → (p1 ∈ L m' ∧ p0 ∉ L m') → ∀ w : ℕ,
      TSP gates L p0 p1 l m w → TSP gates L p0 p1 l' m' w → l = l' ∧ m = m' := by
    intro l m l' m' hl hm hl' hm' w h h'
    constructor
    · by_contra hll
      obtain ⟨p, hp, hpT⟩ := h.2.2.1
      have h3 := f36a l m l' hl hm hl' (fun e => hll e.symm) w p hp h.2.1 hpT
      rw [h'.1] at h3
      exact Bool.noConfusion h3
    · by_contra hmm
      obtain ⟨p, hp, hpT⟩ := h.2.2.2
      have h3 := f36b l m m' hl hm hm' (fun e => hmm e.symm) w p hp h.1 hpT
      rw [h'.2.1] at h3
      exact Bool.noConfusion h3
  have pt : ∀ (t s : Fin N) (w : ℕ) (r r' : Fin N), t ≠ s → t ≠ i0 → r ∈ L t → r' ∈ L t →
      r ≠ r' → vl gates (Tt L p0 p1 t r) w = true → vl gates (Tt L p0 p1 t r') w = true →
      vl gates (zt L s) w = false →
      (p0 ∉ L t ∧ p0 ∈ L s) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p1 ∈ L s) := by
    have one : ∀ (t s : Fin N) (w : ℕ) (r : Fin N), t ≠ i0 → r ∉ L s →
        vl gates (Tt L p0 p1 t r) w = true → vl gates (zt L s) w = false →
        (p0 ∉ L t ∧ p0 ∈ L s) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p1 ∈ L s) := by
      intro t s w r ht hrs hT hz
      obtain ⟨v, hv, hvs⟩ := tz t s r w hT hz
      rw [Tiff] at hv
      rcases hv with hv | ⟨h, _, hv⟩ | ⟨h, h', _, hv⟩ | ⟨h, h', _⟩
      · rw [hv] at hvs
        exact absurd hvs hrs
      · rw [hv] at hvs
        exact Or.inl ⟨h, hvs⟩
      · rw [hv] at hvs
        exact Or.inr ⟨h, h', hvs⟩
      · exact absurd ⟨h, h'⟩ (two_off t ht)
    intro t s w r r' hts ht hr hr' hrr hT hT' hz
    by_cases hrs : r ∈ L s
    · by_cases hrs' : r' ∈ L s
      · exact absurd (iu t s hts r r' hr hrs hr' hrs') hrr
      · exact one t s w r' ht hrs' hT' hz
    · exact one t s w r ht hrs hT hz
  have mgD : ∀ (t : Fin N) (g : Fin gates.length), MgP gates L p0 p1 t g →
      vl gates (zt L t) (N + (g : ℕ)) = false ∧ ∃ r ∈ L t, ∃ r' ∈ L t, r ≠ r' ∧
        vl gates (Tt L p0 p1 t r) (N + (g : ℕ)) = true ∧
        vl gates (Tt L p0 p1 t r') (N + (g : ℕ)) = true := by
    rintro t g ⟨hop, hz, w1, w2, hin, r, hr, r', hr', hT, hT', X, hX, hX', _⟩
    refine ⟨hz, r, hr, r', hr', ?_, orT g hop _ w1 (by rw [hin]; simp) hT,
      orT g hop _ w2 (by rw [hin]; simp) hT'⟩
    intro e
    rw [e] at hX
    exact hX' hX
  have share : ∀ (t s : Fin N) (g : Fin gates.length), t ≠ s → t ≠ i0 → s ≠ i0 →
      MgP gates L p0 p1 t g → MgP gates L p0 p1 s g →
      ((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L s ∧ p0 ∉ L s)) ∨
        ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L s ∧ p1 ∉ L s)) := by
    intro t s g hts ht hs hMt hMs
    obtain ⟨hzt, r, hr, r', hr', hrr, hT, hT'⟩ := mgD t g hMt
    obtain ⟨hzs, u, hu, u', hu', huu, hU, hU'⟩ := mgD s g hMs
    have a1 := pt t s _ r r' hts ht hr hr' hrr hT hT' hzs
    have a2 := pt s t _ u u' (Ne.symm hts) hs hu hu' huu hU hU' hzt
    have b1 := two_off t ht
    have b2 := two_off s hs
    tauto
  have ho1 : vl gates (zt L i0) (o i0) = false := by
    rw [hev i0 (zt L i0) (Or.inr (Or.inr (fun u hu => (ztT i0 u).mpr hu)))]
    apply decide_eq_false
    rintro ⟨v, hv, hz⟩
    exact (ztT i0 v).mp hz hv
  have ho2 : vl gates (sgp p0) (o i0) = true := by
    rw [hev i0 (sgp p0) (Or.inl (by simp [sgp]))]
    exact decide_eq_true ⟨p0, hp0, by simp [sgp]⟩
  have ho3 : vl gates (sgp p1) (o i0) = true := by
    rw [hev i0 (sgp p1) (Or.inr (Or.inl (by simp [sgp])))]
    exact decide_eq_true ⟨p1, hp1, by simp [sgp]⟩
  have ho4 : ∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → vl gates (zrr L i0 r) (o i0) = true := by
    intro r hr _ _
    rw [hev i0 (zrr L i0 r) (Or.inr (Or.inr (fun u hu => by simp [zrr, hu])))]
    exact decide_eq_true ⟨r, hr, by simp [zrr]⟩
  have hchex : ∀ a : Fin gates.length, ∃ c : ℕ, K0P gates L i0 p0 p1 a →
      c ∈ (gates.get a).inputs ∧ vl gates (zt L i0) c = false := by
    intro a
    by_cases hK : K0P gates L i0 p0 p1 a
    · obtain ⟨e, he, hef⟩ := andF a hK.1 _ hK.2.1
      exact ⟨e, fun _ => ⟨he, hef⟩⟩
    · exact ⟨0, fun h => absurd h hK⟩
  choose ch hch using hchex
  obtain ⟨Au, hAu⟩ : ∃ Au : Finset (Fin gates.length), ∀ a, a ∈ Au ↔ AuP gates L i0 p0 p1 ch a :=
    ⟨Finset.univ.filter (fun a => AuP gates L i0 p0 p1 ch a), fun a => by simp⟩
  obtain ⟨Xs, hXs⟩ : ∃ Xs : Finset (Fin gates.length), ∀ a, a ∈ Xs ↔ XsP gates L i0 p0 p1 a :=
    ⟨Finset.univ.filter (fun a => XsP gates L i0 p0 p1 a), fun a => by simp⟩
  have h42 : q - 1 ≤ Au.card + Xs.card :=
    B1642.top q N L i0 p0 p1 hq hN hL hI hP hne hp0 hp1 gates hg hc hwf
      (fun w x => vl gates x w) (fun _ _ => rfl) (o i0) ho1 ho2 ho3 ho4 (StP gates)
      (fun _ _ => Iff.rfl) ch hch Au Xs (fun a ha => (hAu a).mpr ha) (fun a ha => (hXs a).mpr ha)
  have h35 := fun t : Fin N => B1635.top q N L i0 p0 p1 hq hN hL hI hP hne hp0 hp1 (Tt L p0 p1)
    Tiff gates hg hc hwf (fun w x => vl gates x w) (fun _ _ => rfl) o hev (MgP gates L p0 p1)
    (fun _ _ => Iff.rfl) t
  have h37 := fun (l m : Fin N) (hl : p0 ∈ L l ∧ p1 ∉ L l) (hm : p1 ∈ L m ∧ p0 ∉ L m) =>
    B1637.top q N L i0 p0 p1 hq hN hL hI hP hne hp0 hp1 (Tt L p0 p1) Tiff gates hg hc hwf
      (fun w x => vl gates x w) (fun _ _ => rfl) (TSP gates L p0 p1) (fun _ _ _ => Iff.rfl)
      (HgP gates L p0 p1) (fun _ _ _ => Iff.rfl) l m hl hm
  have onec : ∀ (l : Fin N), (p0 ∈ L l ∧ p1 ∉ L l) → ∀ (ν j : ℕ), ν < N + j →
      vl gates (zt L l) ν = false → ∀ a ∈ L l, ∀ b ∈ L l,
      vl gates (Tt L p0 p1 l a) ν = true → vl gates (Tt L p0 p1 l b) ν = true →
      EqvP gates L p0 p1 l j a b := by
    intro l hl ν j hνj hz a ha b hb hTa hTb
    by_cases hin : ν < N
    · have hz' : zt L l ⟨ν, hin⟩ = false := by
        rw [← vl_input gates (zt L l) ν hin]
        exact hz
      have hνl : (⟨ν, hin⟩ : Fin N) ∈ L l := by
        by_contra hc'
        rw [(ztT l _).mpr hc'] at hz'
        exact Bool.noConfusion hz'
      have key : ∀ c ∈ L l, vl gates (Tt L p0 p1 l c) ν = true → (⟨ν, hin⟩ : Fin N) = c := by
        intro c _ hT
        rw [vl_input gates _ ν hin, Tiff] at hT
        rcases hT with h | ⟨h, _⟩ | ⟨_, _, _, h⟩ | ⟨_, h, _⟩
        · exact h
        · exact absurd hl.1 h
        · rw [h] at hνl
          exact absurd hνl hl.2
        · exact absurd h hl.2
      have hab : a = b := (key a ha hTa).symm.trans (key b hb hTb)
      rw [hab]
      intro X _
      exact Iff.rfl
    · by_cases hlt : ν < N + gates.length
      · have hk : ν - N < gates.length := by omega
        have e : N + ((⟨ν - N, hk⟩ : Fin gates.length) : ℕ) = ν := by
          show N + (ν - N) = ν
          omega
        intro X hX
        exact (h35 l).1 ⟨ν - N, hk⟩ (by rw [e]; exact hz) a ha b hb (by rw [e]; exact hTa)
          (by rw [e]; exact hTb) X (fun i hi => hX i (by
            have h5 : (i : ℕ) ≤ ν - N := hi
            omega))
      · rw [vl_missing gates _ ν (by omega)] at hTa
        exact Bool.noConfusion hTa
  have auIn : ∀ (l m : Fin N), (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      ∀ h : Fin gates.length, h ∈ Au → TSP gates L p0 p1 l m (N + (h : ℕ)) →
      ∃ v : ℕ, v < N + (h : ℕ) ∧ TSP gates L p0 p1 l m v ∧
        ∀ x : Fin N → Bool, vl gates x (N + (h : ℕ)) = true → vl gates x v = true := by
    intro l m hl hm h hA hTS
    obtain ⟨hK, r, hr, hr0, hr1, _, hSt⟩ := (hAu h).mp hA
    have hop := hK.1
    have hchin := (hch h hK).1
    have hrl : r ∉ L l := fun hrl => hr0 (iu l i0 (lne l hl) r p0 hrl hr hl.1 hp0)
    have hrm : r ∉ L m := fun hrm => hr1 (iu m i0 (mne m hm) r p1 hrm hr hm.1 hp1)
    have hchl : vl gates (zt L l) (ch h) = true :=
      St_true gates hwf (ch h) r hSt (zt L l) ((ztT l r).mpr hrl)
    have hchm : vl gates (zt L m) (ch h) = true :=
      St_true gates hwf (ch h) r hSt (zt L m) ((ztT m r).mpr hrm)
    obtain ⟨e, he, hel⟩ := andF h hop (zt L l) hTS.1
    obtain ⟨e', he', hem⟩ := andF h hop (zt L m) hTS.2.1
    have hne1 : e ≠ ch h := by
      intro hh
      rw [hh, hchl] at hel
      exact Bool.noConfusion hel
    have hne2 : e' ≠ ch h := by
      intro hh
      rw [hh, hchm] at hem
      exact Bool.noConfusion hem
    have hee : e = e' :=
      two_mem _ (hg _ (List.getElem_mem h.2)).2 (ch h) e e' hchin he he' hne1 hne2
    rw [← hee] at hem
    obtain ⟨_, _, ⟨p, hp, hpT⟩, ⟨p', hp', hpT'⟩⟩ := hTS
    exact ⟨e, hwf h e he, ⟨hel, hem, ⟨p, hp, andT h hop _ hpT e he⟩,
      ⟨p', hp', andT h hop _ hpT' e he⟩⟩, fun x hx => andT h hop x hx e he⟩
  have leafOf : ∀ (l m : Fin N), (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ∀ w : ℕ,
      TSP gates L p0 p1 l m w → ∃ ν : ℕ, ν ≤ w ∧ LeafP gates L p0 p1 Au l m ν ∧
        ∀ j : ℕ, w < N + j → ∀ r ∈ L l, vl gates (Tt L p0 p1 l r) w = true →
          TouchP gates L p0 p1 l j ν r := by
    intro l m hl hm w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hTS
      obtain ⟨ν0, hcone, hkind, hsubl, _, ⟨s0, hs0, hs0T⟩, _⟩ := (h37 l m hl hm).2.2 w hTS
      have hν0w : ν0 ≤ w := hcone {k | k ≤ w} (le_refl w) (by
        intro k hk e he
        have h5 := hwf k e he
        have h6 : N + (k : ℕ) ≤ w := hk
        show e ≤ w
        omega)
      have htouch0 : ∀ j : ℕ, w < N + j → ∀ r ∈ L l, vl gates (Tt L p0 p1 l r) w = true →
          TouchP gates L p0 p1 l j ν0 r := fun j hj r hr hrT =>
        ⟨s0, hs0, hs0T, onec l hl w j hj hTS.1 s0 hs0 r hr (hsubl s0 hs0 hs0T) hrT⟩
      rcases hkind with ⟨c, hcl, hcm, hνc⟩ | ⟨h, hνh, hH⟩
      · exact ⟨ν0, hν0w, Or.inl ⟨c, hcl, hcm, hνc⟩, htouch0⟩
      · by_cases hA : h ∈ Au
        · obtain ⟨v, hvlt, hvTS, hvsub⟩ := auIn l m hl hm h hA hH.1
          obtain ⟨ν, hνv, hleaf, htouch⟩ := ih v (by omega) hvTS
          refine ⟨ν, by omega, hleaf, ?_⟩
          intro j hj r hr hrT
          have hs0w := hsubl s0 hs0 hs0T
          have hs0v : vl gates (Tt L p0 p1 l s0) v = true := hvsub _ (by rw [← hνh]; exact hs0T)
          obtain ⟨s, hs, hsT, hse⟩ := htouch j (by omega) s0 hs0 hs0v
          exact ⟨s, hs, hsT, eqv_trans hse (onec l hl w j hj hTS.1 s0 hs0 r hr hs0w hrT)⟩
        · exact ⟨ν0, hν0w, Or.inr ⟨h, hνh, hH, hA⟩, htouch0⟩
  have leaf_zl : ∀ (l m : Fin N) (ν : ℕ), LeafP gates L p0 p1 Au l m ν →
      vl gates (zt L l) ν = false := by
    intro l m ν hlf
    rcases hlf with ⟨c, hcl, _, hνc⟩ | ⟨h, hνh, hH, _⟩
    · rw [hνc, vl_input gates _ c c.2]
      show zt L l c = false
      unfold zt
      exact decide_eq_false (fun h => h hcl)
    · rw [hνh]
      exact hH.1.1
  have kimg : ∀ (l m : Fin N), (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      ∀ g : Fin gates.length, MgP gates L p0 p1 l g → MgP gates L p0 p1 m g →
      ∃ h : Fin gates.length, (HgP gates L p0 p1 l m h ∧ h ∉ Au) ∧ QP gates L p0 p1 Au l m g h := by
    intro l m hl hm g hMl hMm
    obtain ⟨hop, hzl, w1, w2, hin, r1, hr1, r2, hr2, hT1, hT2, X, hX1, hX2, hXc⟩ := hMl
    obtain ⟨_, hzm, w1', w2', hin', u1, hu1, u2, hu2, hS1, hS2, _⟩ := hMm
    have hww : w1 = w1' ∧ w2 = w2' := by
      rw [hin] at hin'
      simpa using hin'
    rw [← hww.1] at hS1
    rw [← hww.2] at hS2
    have hw1in : w1 ∈ (gates.get g).inputs := by rw [hin]; simp
    have hw2in : w2 ∈ (gates.get g).inputs := by rw [hin]; simp
    have ts1 : TSP gates L p0 p1 l m w1 :=
      ⟨orF g hop _ hzl w1 hw1in, orF g hop _ hzm w1 hw1in, ⟨r1, hr1, hT1⟩, ⟨u1, hu1, hS1⟩⟩
    have ts2 : TSP gates L p0 p1 l m w2 :=
      ⟨orF g hop _ hzl w2 hw2in, orF g hop _ hzm w2 hw2in, ⟨r2, hr2, hT2⟩, ⟨u2, hu2, hS2⟩⟩
    obtain ⟨ν1, hν1, hlf1, htc1⟩ := leafOf l m hl hm w1 ts1
    obtain ⟨ν2, hν2, hlf2, htc2⟩ := leafOf l m hl hm w2 ts2
    have hw1g := hwf g w1 hw1in
    have hw2g := hwf g w2 hw2in
    have ex1 : ∃ ν : ℕ, LeafP gates L p0 p1 Au l m ν ∧ ν < N + (g : ℕ) ∧
        TouchP gates L p0 p1 l (g : ℕ) ν r1 := ⟨ν1, hlf1, by omega, htc1 g hw1g r1 hr1 hT1⟩
    have ex2 : ∃ ν : ℕ, LeafP gates L p0 p1 Au l m ν ∧ ν < N + (g : ℕ) ∧
        TouchP gates L p0 p1 l (g : ℕ) ν r2 := ⟨ν2, hlf2, by omega, htc2 g hw2g r2 hr2 hT2⟩
    obtain ⟨d1, ⟨hd1a, hd1b, hd1c⟩, hmin1⟩ : ∃ ν : ℕ, (LeafP gates L p0 p1 Au l m ν ∧
        ν < N + (g : ℕ) ∧ TouchP gates L p0 p1 l (g : ℕ) ν r1) ∧
        ∀ ν' : ℕ, (LeafP gates L p0 p1 Au l m ν' ∧ ν' < N + (g : ℕ) ∧
          TouchP gates L p0 p1 l (g : ℕ) ν' r1) → ν ≤ ν' :=
      ⟨Nat.find ex1, Nat.find_spec ex1, fun ν' h' => Nat.find_min' ex1 h'⟩
    obtain ⟨d2, ⟨hd2a, hd2b, hd2c⟩, hmin2⟩ : ∃ ν : ℕ, (LeafP gates L p0 p1 Au l m ν ∧
        ν < N + (g : ℕ) ∧ TouchP gates L p0 p1 l (g : ℕ) ν r2) ∧
        ∀ ν' : ℕ, (LeafP gates L p0 p1 Au l m ν' ∧ ν' < N + (g : ℕ) ∧
          TouchP gates L p0 p1 l (g : ℕ) ν' r2) → ν ≤ ν' :=
      ⟨Nat.find ex2, Nat.find_spec ex2, fun ν' h' => Nat.find_min' ex2 h'⟩
    have hne12 : d1 ≠ d2 := by
      intro he
      rw [← he] at hd2c
      obtain ⟨s, hs, hsT, hse⟩ := hd1c
      obtain ⟨s', hs', hsT', hse'⟩ := hd2c
      have hsame := onec l hl d1 g hd1b (leaf_zl l m d1 hd1a) s hs s' hs' hsT hsT'
      have h12 : EqvP gates L p0 p1 l (g : ℕ) r1 r2 :=
        eqv_trans (eqv_symm hse) (eqv_trans hsame hse')
      exact hX2 ((h12 X hXc).mp hX1)
    have joined : ∀ j : ℕ, (g : ℕ) < j → EqvP gates L p0 p1 l j r1 r2 := fun j hj X' hX' =>
      hX' g hj hop hzl w1 w2 hin r1 hr1 r2 hr2 (Or.inl hT1) (Or.inr hT2)
    have hlm : l ≠ m := by
      intro e
      rw [e] at hl
      exact hm.2 hl.1
    have big : ∀ (ν μ : ℕ) (ra rb : Fin N), ra ∈ L l → rb ∈ L l →
        LeafP gates L p0 p1 Au l m ν → LeafP gates L p0 p1 Au l m μ → μ < ν → ν < N + (g : ℕ) →
        TouchP gates L p0 p1 l (g : ℕ) ν ra → TouchP gates L p0 p1 l (g : ℕ) μ rb →
        (∀ j : ℕ, (g : ℕ) < j → EqvP gates L p0 p1 l j ra rb) →
        (∀ ν' : ℕ, LeafP gates L p0 p1 Au l m ν' → ν' < N + (g : ℕ) →
          TouchP gates L p0 p1 l (g : ℕ) ν' ra → ν ≤ ν') →
        ∃ h : Fin gates.length, (HgP gates L p0 p1 l m h ∧ h ∉ Au) ∧
          QP gates L p0 p1 Au l m g h := by
      intro ν μ ra rb hra hrb hlν hlμ hμν hνg htν htμ hj hmin
      have hzν := leaf_zl l m ν hlν
      rcases hlν with ⟨c, hcl, hcm, hνc⟩ | ⟨h, hνh, hH, hA⟩
      · exfalso
        rcases hlμ with ⟨c', hcl', hcm', hμc⟩ | ⟨h', hμh, _⟩
        · have hcc : c' = c := iu l m hlm c' c hcl' hcm' hcl hcm
          rw [hμc, hνc, hcc] at hμν
          exact lt_irrefl _ hμν
        · have := c.2
          omega
      · rw [hνh] at hμν hνg htν hmin hzν
        exact ⟨h, ⟨hH, hA⟩, hzν, ra, hra, rb, hrb, μ, hlμ, hμν, by omega, htν, htμ, hj, hmin⟩
    rcases lt_or_gt_of_ne hne12 with hlt | hgt
    · exact big d2 d1 r2 r1 hr2 hr1 hd2a hd1a hlt hd2b hd2c hd1c
        (fun j hj => eqv_symm (joined j hj)) (fun ν' a b c => hmin2 ν' ⟨a, b, c⟩)
    · exact big d1 d2 r1 r2 hr1 hr2 hd1a hd2a hgt hd1b hd1c hd2c joined
        (fun ν' a b c => hmin1 ν' ⟨a, b, c⟩)
  have kinj : ∀ (l m : Fin N), (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      ∀ (g g' h : Fin gates.length), (g : ℕ) < (g' : ℕ) → QP gates L p0 p1 Au l m g h →
      QP gates L p0 p1 Au l m g' h → False := by
    rintro l m hl hm g g' h hgg ⟨hzν, ra, hra, rb, hrb, μ, hlμ, hμν, hνg, htν, htμ, hj, _⟩
      ⟨_, ra', hra', _, _, _, _, _, hνg', htν', _, _, hmin'⟩
    obtain ⟨s, hs, hsT, hse⟩ := htν'
    obtain ⟨s0, hs0, hs0T, hs0e⟩ := htν
    obtain ⟨t, ht, htT, hte⟩ := htμ
    have e1 : EqvP gates L p0 p1 l (g' : ℕ) s s0 :=
      onec l hl (N + (h : ℕ)) g' (by omega) hzν s hs s0 hs0 hsT hs0T
    have hle : (g : ℕ) ≤ (g' : ℕ) := le_of_lt hgg
    have chain : EqvP gates L p0 p1 l (g' : ℕ) t ra' :=
      eqv_trans (eqv_mono hle hte) (eqv_trans (eqv_symm (hj g' hgg))
        (eqv_trans (eqv_symm (eqv_mono hle hs0e)) (eqv_trans (eqv_symm e1) hse)))
    have h7 := hmin' μ hlμ (by omega) ⟨t, ht, htT, chain⟩
    omega
  obtain ⟨Kk, hKk⟩ : ∃ Kk : Finset (Fin gates.length), ∀ g, g ∈ Kk ↔
      ∃ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) ∧ (p1 ∈ L m ∧ p0 ∉ L m) ∧
        MgP gates L p0 p1 l g ∧ MgP gates L p0 p1 m g :=
    ⟨Finset.univ.filter (fun g => ∃ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) ∧ (p1 ∈ L m ∧ p0 ∉ L m) ∧
        MgP gates L p0 p1 l g ∧ MgP gates L p0 p1 m g), fun g => by simp⟩
  obtain ⟨Gh, hGL⟩ : ∃ Gh : Finset (Fin gates.length), ∀ h, h ∈ Gh ↔
      ∃ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) ∧ (p1 ∈ L m ∧ p0 ∉ L m) ∧
        HgP gates L p0 p1 l m h ∧ h ∉ Au :=
    ⟨Finset.univ.filter (fun h => ∃ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) ∧ (p1 ∈ L m ∧ p0 ∉ L m) ∧
        HgP gates L p0 p1 l m h ∧ h ∉ Au), fun g => by simp⟩
  have hKGL : Kk.card ≤ Gh.card := by
    have ex : ∀ g : Fin gates.length, ∃ h : Fin gates.length, g ∈ Kk →
        ∃ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) ∧ (p1 ∈ L m ∧ p0 ∉ L m) ∧
          (HgP gates L p0 p1 l m h ∧ h ∉ Au) ∧ QP gates L p0 p1 Au l m g h := by
      intro g
      by_cases hgK : g ∈ Kk
      · obtain ⟨l, m, hl, hm, hMl, hMm⟩ := (hKk g).mp hgK
        obtain ⟨h, hh, hQ⟩ := kimg l m hl hm g hMl hMm
        exact ⟨h, fun _ => ⟨l, m, hl, hm, hh, hQ⟩⟩
      · exact ⟨g, fun h => absurd h hgK⟩
    choose Φ hΦ using ex
    apply Finset.card_le_card_of_injOn Φ
    · intro g hgK
      have hgK' : g ∈ Kk := by simpa using hgK
      obtain ⟨l, m, hl, hm, hh, _⟩ := hΦ g hgK'
      show Φ g ∈ Gh
      exact (hGL _).mpr ⟨l, m, hl, hm, hh.1, hh.2⟩
    · intro g hgK g' hgK' hΦeq
      have hgK1 : g ∈ Kk := by simpa using hgK
      have hgK2 : g' ∈ Kk := by simpa using hgK'
      obtain ⟨l, m, hl, hm, hh, hQ⟩ := hΦ g hgK1
      obtain ⟨l', m', hl', hm', hh', hQ'⟩ := hΦ g' hgK2
      rw [← hΦeq] at hh' hQ'
      obtain ⟨ell, emm⟩ := pairuniq l m l' m' hl hm hl' hm' (N + (Φ g : ℕ)) hh.1.1 hh'.1.1
      rw [← ell, ← emm] at hQ'
      by_contra hne'
      rcases lt_or_gt_of_ne (fun h => hne' (Fin.ext h)) with hlt | hgt
      · exact kinj l m hl hm g g' (Φ g) hlt hQ hQ'
      · exact kinj l m hl hm g' g (Φ g) hgt hQ' hQ
  obtain ⟨I, hImem⟩ : ∃ I : Fin N → Finset (Fin gates.length), ∀ t g, g ∈ I t ↔
      MgP gates L p0 p1 t g :=
    ⟨fun t => Finset.univ.filter (fun g => MgP gates L p0 p1 t g), fun t g => by simp⟩
  have hIq : ∀ t : Fin N, (I t).card = q := fun t => (h35 t).2 (I t) (fun g => hImem t g)
  have hsum : ∑ t ∈ Finset.univ.erase i0, (I t).card = (N - 1) * q := by
    rw [Finset.sum_congr rfl (fun t _ => hIq t), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  have hcnt := count_abs (Finset.univ.erase i0) I (fun t => p0 ∈ L t ∧ p1 ∉ L t)
    (fun t => p1 ∈ L t ∧ p0 ∉ L t) Kk (fun t h => h.1.2 h.2.1) (by
      intro g t ht s hs hts hgt hgs
      have ht' := Finset.ne_of_mem_erase ht
      have hs' := Finset.ne_of_mem_erase hs
      have hMt := (hImem t g).mp hgt
      have hMs := (hImem s g).mp hgs
      have hsh := share t s g hts ht' hs' hMt hMs
      refine ⟨?_, hsh⟩
      rcases hsh with ⟨a, b⟩ | ⟨a, b⟩
      · exact (hKk g).mpr ⟨t, s, a, b, hMt, hMs⟩
      · exact (hKk g).mpr ⟨s, t, b, a, hMs, hMt⟩)
  have hgs : ∃ gs : Fin gates.length, (gates.get gs).op = GateOp.or ∧
      vl gates (sgp p0) (N + (gs : ℕ)) = true ∧ vl gates (sgp p1) (N + (gs : ℕ)) = true ∧
      ∀ e ∈ (gates.get gs).inputs, (vl gates (sgp p0) e = true ∨ vl gates (sgp p1) e = true) := by
    have exw : ∃ w : ℕ, vl gates (zt L i0) w = false ∧ vl gates (sgp p0) w = true ∧
        vl gates (sgp p1) w = true := ⟨o i0, ho1, ho2, ho3⟩
    obtain ⟨w, ⟨hw1, hw2, hw3⟩, hmin⟩ : ∃ w : ℕ, (vl gates (zt L i0) w = false ∧
        vl gates (sgp p0) w = true ∧ vl gates (sgp p1) w = true) ∧
        ∀ w' : ℕ, w' < w → ¬ (vl gates (zt L i0) w' = false ∧ vl gates (sgp p0) w' = true ∧
          vl gates (sgp p1) w' = true) :=
      ⟨Nat.find exw, Nat.find_spec exw, fun w' h' => Nat.find_min exw h'⟩
    have hwN : N ≤ w := by
      by_contra hcon
      have hin : w < N := by omega
      rw [vl_input gates _ w hin] at hw2 hw3
      have e2 : (⟨w, hin⟩ : Fin N) = p0 := by simpa [sgp] using hw2
      have e3 : (⟨w, hin⟩ : Fin N) = p1 := by simpa [sgp] using hw3
      exact hne (e2.symm.trans e3)
    have hwlt : w < N + gates.length := by
      by_contra hcon
      rw [vl_missing gates _ w (by omega)] at hw2
      exact Bool.noConfusion hw2
    obtain ⟨gs, hgsw⟩ : ∃ gs : Fin gates.length, N + (gs : ℕ) = w :=
      ⟨⟨w - N, by omega⟩, by show N + (w - N) = w; omega⟩
    rw [← hgsw] at hw1 hw2 hw3 hmin
    rcases opi gs with hop | hop
    · exfalso
      obtain ⟨e, he, hef⟩ := andF gs hop _ hw1
      exact hmin e (hwf gs e he) ⟨hef, andT gs hop _ hw2 e he, andT gs hop _ hw3 e he⟩
    · refine ⟨gs, hop, hw2, hw3, ?_⟩
      obtain ⟨e0, he0, hv0⟩ := orE gs hop _ hw2
      obtain ⟨e1, he1, hv1⟩ := orE gs hop _ hw3
      have hne01 : e0 ≠ e1 := by
        intro e
        rw [← e] at hv1
        exact hmin e0 (hwf gs e0 he0) ⟨orF gs hop _ hw1 e0 he0, hv0, hv1⟩
      intro e he
      rcases two_cover _ (hg _ (List.getElem_mem gs.2)).2 e0 e1 he0 he1 hne01 e he with h | h
      · rw [h]
        exact Or.inl hv0
      · rw [h]
        exact Or.inr hv1
  obtain ⟨gs, hgsop, hgs0, hgs1, hgsin⟩ := hgs
  have gsz : ∀ t : Fin N, t ≠ i0 → vl gates (zt L t) (N + (gs : ℕ)) = true := by
    intro t ht
    by_cases h : p0 ∈ L t
    · have h' : p1 ∉ L t := fun h' => two_off t ht ⟨h, h'⟩
      apply mono (sgp p1) (zt L t) _ _ hgs1
      intro v hv
      have e : v = p1 := by simpa [sgp] using hv
      rw [ztT, e]
      exact h'
    · apply mono (sgp p0) (zt L t) _ _ hgs0
      intro v hv
      have e : v = p0 := by simpa [sgp] using hv
      rw [ztT, e]
      exact h
  have hnh : ∀ (l m : Fin N), (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      ∀ (h : Fin gates.length) (t : Fin N), HgP gates L p0 p1 l m h → t ≠ i0 →
      MgP gates L p0 p1 t h → False := by
    intro l m hl hm h t hH ht hM
    obtain ⟨hzt, r, hr, r', hr', hrr, hT, hT'⟩ := mgD t h hM
    obtain ⟨hTS, hkind⟩ := hH
    rcases hkind with hand | ⟨hor, hnots⟩
    · rw [hM.1] at hand
      cases hand
    · by_cases htl : t = l
      · obtain ⟨_, _, w1, w2, hin, a, ha, b, hb, hTa, hTb, _⟩ := hM
        rw [htl] at ha hb hTa hTb
        have hw1in : w1 ∈ (gates.get h).inputs := by rw [hin]; simp
        have hw2in : w2 ∈ (gates.get h).inputs := by rw [hin]; simp
        obtain ⟨u, hu, huT⟩ := hTS.2.2.2
        obtain ⟨e, he, hev'⟩ := orE h hor _ huT
        rw [hin] at he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with he | he
        · rw [he] at hev'
          exact hnots w1 hw1in ⟨orF h hor _ hTS.1 w1 hw1in, orF h hor _ hTS.2.1 w1 hw1in,
            ⟨a, ha, hTa⟩, ⟨u, hu, hev'⟩⟩
        · rw [he] at hev'
          exact hnots w2 hw2in ⟨orF h hor _ hTS.1 w2 hw2in, orF h hor _ hTS.2.1 w2 hw2in,
            ⟨b, hb, hTb⟩, ⟨u, hu, hev'⟩⟩
      · by_cases htm : t = m
        · obtain ⟨_, _, w1, w2, hin, a, ha, b, hb, hTa, hTb, _⟩ := hM
          rw [htm] at ha hb hTa hTb
          have hw1in : w1 ∈ (gates.get h).inputs := by rw [hin]; simp
          have hw2in : w2 ∈ (gates.get h).inputs := by rw [hin]; simp
          obtain ⟨u, hu, huT⟩ := hTS.2.2.1
          obtain ⟨e, he, hev'⟩ := orE h hor _ huT
          rw [hin] at he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with he | he
          · rw [he] at hev'
            exact hnots w1 hw1in ⟨orF h hor _ hTS.1 w1 hw1in, orF h hor _ hTS.2.1 w1 hw1in,
              ⟨u, hu, hev'⟩, ⟨a, ha, hTa⟩⟩
          · rw [he] at hev'
            exact hnots w2 hw2in ⟨orF h hor _ hTS.1 w2 hw2in, orF h hor _ hTS.2.1 w2 hw2in,
              ⟨u, hu, hev'⟩, ⟨b, hb, hTb⟩⟩
        · by_cases htp : p0 ∈ L t
          · have htl' : p0 ∈ L t ∧ p1 ∉ L t := ⟨htp, fun h' => two_off t ht ⟨htp, h'⟩⟩
            obtain ⟨u, hu, huT⟩ := hTS.2.2.1
            have h3 := f36a l m t hl hm htl' htl _ u hu hTS.2.1 huT
            rw [hzt] at h3
            exact Bool.noConfusion h3
          · exact f36c t m htp hm htm _ r r' hr hr' hrr hTS.2.1 hT hT'
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin gates.length), B = (Finset.univ.erase i0).biUnion I :=
    ⟨_, rfl⟩
  have hBmem : ∀ g, g ∈ B → ∃ t : Fin N, t ≠ i0 ∧ MgP gates L p0 p1 t g := by
    intro g hgB
    rw [hB] at hgB
    obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.mp hgB
    exact ⟨t, Finset.ne_of_mem_erase ht, (hImem t g).mp hgt⟩
  have h5 := five B Gh Au Xs gs
    (Finset.disjoint_left.mpr (fun g hgB hgG => by
      obtain ⟨t, ht, hM⟩ := hBmem g hgB
      obtain ⟨l, m, hl, hm, hH, _⟩ := (hGL g).mp hgG
      exact hnh l m hl hm g t hH ht hM))
    (Finset.disjoint_left.mpr (fun g hgB hgA => by
      obtain ⟨t, ht, hM⟩ := hBmem g hgB
      have h7 := ((hAu g).mp hgA).1.1
      rw [hM.1] at h7
      cases h7))
    (Finset.disjoint_left.mpr (fun g hgB hgX => by
      obtain ⟨t, ht, hM⟩ := hBmem g hgB
      have h7 := ((hXs g).mp hgX).2.2.1 t ht
      rw [hM.2.1] at h7
      exact Bool.noConfusion h7))
    (fun hgB => by
      obtain ⟨t, ht, hM⟩ := hBmem gs hgB
      have h7 := gsz t ht
      rw [hM.2.1] at h7
      exact Bool.noConfusion h7)
    (Finset.disjoint_left.mpr (fun g hgG hgA => by
      obtain ⟨l, m, hl, hm, hH, hnA⟩ := (hGL g).mp hgG
      exact hnA hgA))
    (Finset.disjoint_left.mpr (fun g hgG hgX => by
      obtain ⟨l, m, hl, hm, hH, _⟩ := (hGL g).mp hgG
      have h7 := ((hXs g).mp hgX).2.2.1 l (lne l hl)
      rw [hH.1.1] at h7
      exact Bool.noConfusion h7))
    (fun hgG => by
      obtain ⟨l, m, hl, hm, hH, _⟩ := (hGL gs).mp hgG
      have h7 := gsz l (lne l hl)
      rw [hH.1.1] at h7
      exact Bool.noConfusion h7)
    (Finset.disjoint_left.mpr (fun g hgA hgX => by
      have h7 := ((hAu g).mp hgA).1.1
      rw [((hXs g).mp hgX).1] at h7
      cases h7))
    (fun hgA => by
      have h7 := ((hAu gs).mp hgA).1.1
      rw [hgsop] at h7
      cases h7)
    (fun hgX => ((hXs gs).mp hgX).2.2.2 hgsin)
  rw [Fintype.card_fin] at h5
  rw [← hB, hsum] at hcnt
  have hNpos : 0 < N := Fin.pos i0
  have hNq : N * q = (N - 1) * q + q := by
    have e : N = (N - 1) + 1 := by omega
    conv_lhs => rw [e]
    rw [Nat.add_mul, Nat.one_mul]
  omega

lemma lower (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hq : 3 ≤ q) (hN : N = q ^ 2 + q + 1) (hL : ∀ i : Fin N, (L i).card = q + 1)
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hP : ∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i)
    (hne : p0 ≠ p1) (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (gates : List Gate) (o : Fin N → ℕ)
    (hg : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (hev : ∀ (t : Fin N) (x : Fin N → Bool),
      (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) :
    N * q ≤ gates.length := by
  have hNpos : 0 < N := Fin.pos i0
  have hev' : ∀ (t : Fin N) (x : Fin N → Bool),
      (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        vl gates x (o t) = decide (∃ v ∈ L t, x v = true) := fun t x hx => hev t x hx
  obtain ⟨gates', hlen, hg', hc', hwf', hval⟩ := normalize hNpos gates hg hwf
  rw [← hlen]
  apply lower_nc q N L i0 p0 p1 hq hN hL hI hP hne hp0 hp1 gates' o hg' hc' hwf'
  intro t x hx
  have hnt : ¬ CT N gates (o t) := by
    intro hct
    have hF : (zt L t p0 = true ∨ zt L t p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → zt L t u = true) := by
      by_cases ht : t = i0
      · right
        right
        intro u hu
        rw [ht]
        simp [zt, hu]
      · by_cases h : p0 ∈ L t
        · right
          left
          have h' : p1 ∉ L t := by
            intro h'
            apply hne
            exact Finset.card_le_one.mp (hI t i0 ht).le p0 (Finset.mem_inter.mpr ⟨h, hp0⟩) p1
              (Finset.mem_inter.mpr ⟨h', hp1⟩)
          simp [zt, h']
        · left
          simp [zt, h]
    have e := (hct (zt L t)).symm.trans (hev' t (zt L t) hF)
    obtain ⟨v, hv, hz⟩ := of_decide_eq_true e.symm
    simp [zt, hv] at hz
  have hnf : ¬ CF N gates (o t) := by
    intro hcf
    have e := (hcf (fun _ => true)).symm.trans (hev' t (fun _ => true) (Or.inl rfl))
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [hL t]; omega)
    have h3 : decide (∃ v ∈ L t, (fun _ : Fin N => true) v = true) = true :=
      decide_eq_true ⟨v, hv, rfl⟩
    rw [h3] at e
    exact Bool.noConfusion e
  rw [hval (o t) hnt hnf x]
  exact hev' t x hx

lemma thm43 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
      N * q ≤ gates.length) ∧
    ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) ∧
      (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) ∧
      gates.length = N * q := by
  intro q N L i0 p0 p1 hq hN hL hI hP hne h0 h1
  exact ⟨fun gates o hg hwf hev =>
      PEqualNP.Outside.L_meta_1644.B1643.lower q N L i0 p0 p1 hq hN hL hI hP hne h0 h1 gates o hg hwf hev,
    PEqualNP.Outside.L_meta_1644.B1643.upper q N L (by omega) hL⟩

end B1643

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

def isOrD : GateOp → Bool
  | GateOp.or => true
  | _ => false

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma eval_ao (op : GateOp) (l : List Bool) (h : op = GateOp.and ∨ op = GateOp.or) :
    op.eval l = if isOrD op ∈ l then isOrD op else !isOrD op := by
  rcases h with rfl | rfl
  · simp only [GateOp.eval, isOrD]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all
  · simp only [GateOp.eval, isOrD]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all

def fin3 (a : Bool) (op : GateOp) (N : ℕ) : List ℕ → (Bool ⊕ ℕ) × List Gate
  | [] => (Sum.inl (!a), [])
  | [w] => (Sum.inr w, [])
  | w :: w2 :: t => (Sum.inr N, [⟨op, w :: w2 :: t⟩])

def gen (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (Bool ⊕ ℕ) × List Gate :=
  if Sum.inl (isOrD g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) then
    (Sum.inl (isOrD g.op), [])
  else fin3 (isOrD g.op) g.op N
    ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?)

def stp (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  if k < h then (s.1 ++ [Sum.inr (n + s.2.length)], s.2 ++ [g])
  else if k = h then (s.1 ++ [Sum.inl true], s.2)
  else if isNot g.op = true then (s.1 ++ [Sum.inl false], s.2)
  else (s.1 ++ [(gen s.1 (n + s.2.length) g).1], s.2 ++ (gen s.1 (n + s.2.length) g).2)

def SD (n h : ℕ) (gs : List Gate) : ℕ → List (Bool ⊕ ℕ) × List Gate
  | 0 => ((List.range n).map Sum.inr, [])
  | k + 1 => match gs[k]? with
    | none => SD n h gs k
    | some g => stp n h k g (SD n h gs k)

lemma SD_succ (n h : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    SD n h gs (k + 1) = stp n h k gs[k] (SD n h gs k) := by
  rw [SD]
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

lemma SD_len (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → (SD n h gs k).1.length = n + k := by
  intro k
  induction k with
  | zero => intro _; simp [SD]
  | succ k ih =>
    intro hk
    rw [SD_succ n h gs k (by omega)]
    obtain ⟨d, hd⟩ := stp_fst n h k gs[k] (SD n h gs k)
    rw [hd, List.length_append, ih (by omega)]
    simp
    omega

lemma SD_low (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → k ≤ h →
    (SD n h gs k).2 = gs.take k ∧ (SD n h gs k).1 = (List.range (n + k)).map Sum.inr := by
  intro k
  induction k with
  | zero => intro _ _; simp [SD]
  | succ k ih =>
    intro hk hkh
    obtain ⟨h1, h2⟩ := ih (by omega) (by omega)
    rw [SD_succ n h gs k (by omega)]
    have hlt : k < h := by omega
    unfold stp
    simp only [hlt, ↓reduceIte]
    rw [h1, h2]
    refine ⟨(List.take_succ_eq_append_getElem (by omega)).symm, ?_⟩
    have : (List.take k gs).length = k := by simp; omega
    rw [this, ← Nat.add_assoc, List.range_succ, List.map_append]
    rfl

lemma SD_prefix (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → h ≤ k →
    gs.take h <+: (SD n h gs k).2 := by
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
    · rw [he, (SD_low n (k + 1) gs (k + 1) hk le_rfl).1]
    · rw [SD_succ n h gs k (by omega)]
      obtain ⟨e, he2, _⟩ := stp_snd n h k gs[k] (SD n h gs k)
      rw [he2]
      exact (ih (by omega) (by omega)).trans (List.prefix_append _ _)

lemma SD_ops (n h j : ℕ) (gs : List Gate) (hhj : h < j)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j) :
    ∀ k, k ≤ gs.length → ∀ g' ∈ (SD n h gs k).2,
      (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro _ g' hg'; simp [SD] at hg'
  | succ k ih =>
    intro hk g' hg'
    have hkl : k < gs.length := by omega
    rw [SD_succ n h gs k hkl] at hg'
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

lemma SD_j (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) :
    ∀ k, k ≤ gs.length → j < k → (SD n h gs k).1.getD (n + j) (Sum.inl false) = Sum.inl false := by
  intro k
  induction k with
  | zero => intro _ h0; omega
  | succ k ih =>
    intro hk hjk
    have hkl : k < gs.length := by omega
    have hl := SD_len n h gs k (by omega)
    by_cases he : k = j
    · subst he
      rw [SD_succ n h gs k hkl]
      unfold stp
      have h1 : ¬ k < h := by omega
      have h2 : ¬ k = h := by omega
      have h3 : isNot gs[k].op = true := by rw [hjn]; rfl
      simp only [h1, h2, h3, ↓reduceIte]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hl]
    · rw [SD_succ n h gs k hkl]
      obtain ⟨d, hd⟩ := stp_fst n h k gs[k] (SD n h gs k)
      rw [hd, List.getD_append _ _ _ _ (by omega)]
      exact ih (by omega) (by omega)

def bad (n h j : ℕ) (gs : List Gate) (i : ℕ) : Bool :=
  decide (i = h ∨ i = j ∨ (j < i ∧ n + j ∈ (gs.getD i ⟨GateOp.and, []⟩).inputs))

lemma SD_bad (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gs.length) (hb : bad n h j gs k = true) :
    (SD n h gs (k + 1)).2 = (SD n h gs k).2 := by
  rw [SD_succ n h gs k hk]
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
        (SD_j n h j gs hhj hj hjn k (by omega) hb1)]
      simp

lemma SD_count (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ k, k ≤ gs.length →
      (SD n h gs k).2.length + ((Finset.range k).filter (fun i => bad n h j gs i = true)).card ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp [SD]
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hb : bad n h j gs k = true
    · rw [SD_bad n h j gs hhj hj hjn hlen k hkl hb]
      simp only [hb, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · simp only [hb]
      rw [SD_succ n h gs k hkl]
      obtain ⟨e, he, hel⟩ := stp_snd n h k gs[k] (SD n h gs k)
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
  by_cases hin : Sum.inl (isOrD g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false))
  · simp only [hin, ↓reduceIte]
    obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hin
    have h1 := hr r hrm
    rw [hre] at h1
    have h2 : vals r = isOrD g.op := h1
    have hmem : isOrD g.op ∈ g.inputs.map vals := List.mem_map.mpr ⟨r, hrm, h2⟩
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
    have key2 : isOrD g.op ∈ g.inputs.map vals ↔ isOrD g.op ∈
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
      cases isOrD g.op <;> cases c <;> simp
    · refine ⟨by simp [fin3, drun], ?_⟩
      simp only [fin3, drun, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact eval_ao g.op _ hop

lemma sem (n h j : ℕ) (gs : List Gate) (x : Fin n → Bool)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j)
    (hh : dvalue ⟨gs, 0⟩ x (n + h) = true) (hjv : dvalue ⟨gs, 0⟩ x (n + j) = false) :
    ∀ k, k ≤ gs.length → ∀ i, Rp (drun (SD n h gs k).2 (List.ofFn x))
      (if i < n + k then dvalue ⟨gs, 0⟩ x i else false)
      ((SD n h gs k).1.getD i (Sum.inl false)) := by
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
    have hl := SD_len n h gs k (by omega)
    have hWl : (drun (SD n h gs k).2 (List.ofFn x)).length = n + (SD n h gs k).2.length := by
      rw [drunlength]; simp
    have hgv := dgatevalueP gs x k hkl
    rw [SD_succ n h gs k hkl]
    unfold stp
    split_ifs with h1 h2 h3
    · simp only [drunappend, ← Nat.add_assoc]
      apply ext _ _ _ _ (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
      obtain ⟨l1, l2⟩ := SD_low n h gs k (by omega) (by omega)
      have hk2 : (SD n h gs k).2.length = k := by rw [l1]; simp; omega
      refine ⟨by rw [drunlength, hWl]; simp, ?_⟩
      change ((drun (SD n h gs k).2 (List.ofFn x)) ++ [_]).getD _ false = _
      rw [List.getD_append_right _ _ _ _ (by omega), hWl, Nat.sub_self, List.getD_cons_zero, hgv]
      congr 1
      apply List.map_congr_left
      intro r _
      by_cases hr : r < n + k
      · have h4 := ih' r
        have e1 : (SD n h gs k).1.getD r (Sum.inl false) = Sum.inr r := by
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

lemma fin3_wf (a : Bool) (op : GateOp) (M : ℕ) (l : List ℕ) (B : ℕ) (hl : ∀ w ∈ l, w < B) :
    (∀ w, (fin3 a op M l).1 = Sum.inr w → w < B ∨ (w = M ∧ (fin3 a op M l).2.length = 1)) ∧
      ∀ g' ∈ (fin3 a op M l).2, ∀ w ∈ g'.inputs, w < B := by
  rcases l with _ | ⟨w1, _ | ⟨w2, t⟩⟩
  · refine ⟨fun w hw => ?_, fun g' hg' => ?_⟩
    · simp [fin3] at hw
    · simp [fin3] at hg'
  · refine ⟨fun w hw => ?_, fun g' hg' => ?_⟩
    · left
      have e : w1 = w := by simpa [fin3] using hw
      rw [← e]
      exact hl w1 (by simp)
    · simp [fin3] at hg'
  · refine ⟨fun w hw => ?_, fun g' hg' => ?_⟩
    · right
      have e : M = w := by simpa [fin3] using hw
      exact ⟨e.symm, by simp [fin3]⟩
    · have e : g' = ⟨op, w1 :: w2 :: t⟩ := by simpa [fin3] using hg'
      rw [e]
      exact hl

lemma gen_wf (ρ : List (Bool ⊕ ℕ)) (M : ℕ) (g : Gate) (B : ℕ)
    (hρ : ∀ w, Sum.inr w ∈ ρ → w < B) :
    (∀ w, (gen ρ M g).1 = Sum.inr w → w < B ∨ (w = M ∧ (gen ρ M g).2.length = 1)) ∧
      ∀ g' ∈ (gen ρ M g).2, ∀ w ∈ g'.inputs, w < B := by
  unfold gen
  split_ifs with hc
  · refine ⟨fun w hw => ?_, fun g' hg' => ?_⟩
    · simp at hw
    · simp at hg'
  · apply fin3_wf
    intro w hw
    obtain ⟨d, hd, hdw⟩ := List.mem_filterMap.mp hw
    obtain ⟨r, _, hr⟩ := List.mem_map.mp hd
    have hd2 : d = Sum.inr w := by
      rcases d with b | v
      · simp at hdw
      · simp at hdw
        rw [hdw]
    apply hρ
    rw [← hd2, ← hr]
    by_cases hlt : r < ρ.length
    · rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    · rw [List.getD_eq_default _ _ (by omega)] at hr
      rw [hd2] at hr
      simp at hr

lemma SD_wf (n h : ℕ) (gs : List Gate)
    (hwf : ∀ i (hi : i < gs.length), ∀ w ∈ gs[i].inputs, w < n + i) :
    ∀ k, k ≤ gs.length →
      (∀ w, Sum.inr w ∈ (SD n h gs k).1 → w < n + (SD n h gs k).2.length) ∧
      (∀ i (hi : i < (SD n h gs k).2.length), ∀ w ∈ ((SD n h gs k).2)[i].inputs, w < n + i) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun w hw => ?_, fun i hi => ?_⟩
    · simp [SD] at hw
      omega
    · simp [SD] at hi
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    obtain ⟨ia, ib⟩ := ih (by omega)
    rw [SD_succ n h gs k hkl]
    unfold stp
    split_ifs with h1 h2 h3
    · have hlow := (SD_low n h gs k (by omega) (by omega)).1
      have hlen : (SD n h gs k).2.length = k := by
        rw [hlow, List.length_take]
        omega
      refine ⟨fun w hw => ?_, fun i hi w hw => ?_⟩
      · rw [List.length_append, List.length_singleton]
        rcases List.mem_append.mp hw with hm | hm
        · have := ia w hm
          omega
        · have e : w = n + (SD n h gs k).2.length := by simpa using hm
          omega
      · rw [List.length_append, List.length_singleton] at hi
        by_cases hi2 : i < (SD n h gs k).2.length
        · rw [List.getElem_append_left hi2] at hw
          exact ib i hi2 w hw
        · have e : i = (SD n h gs k).2.length := by omega
          subst e
          rw [List.getElem_append_right (le_refl _)] at hw
          simp only [Nat.sub_self, List.getElem_cons_zero] at hw
          have := hwf k hkl w hw
          omega
    · exact ⟨fun w hw => by
        rcases List.mem_append.mp hw with hm | hm
        · exact ia w hm
        · simp at hm, ib⟩
    · exact ⟨fun w hw => by
        rcases List.mem_append.mp hw with hm | hm
        · exact ia w hm
        · simp at hm, ib⟩
    · obtain ⟨ga, gb⟩ := gen_wf (SD n h gs k).1 (n + (SD n h gs k).2.length) gs[k]
        (n + (SD n h gs k).2.length) ia
      have glen := gen_len (SD n h gs k).1 (n + (SD n h gs k).2.length) gs[k]
      refine ⟨fun w hw => ?_, fun i hi w hw => ?_⟩
      · rw [List.length_append]
        rcases List.mem_append.mp hw with hm | hm
        · have := ia w hm
          omega
        · have e : (gen (SD n h gs k).1 (n + (SD n h gs k).2.length) gs[k]).1 = Sum.inr w := by
            exact (List.mem_singleton.mp hm).symm
          rcases ga w e with hlt | ⟨he, hl1⟩
          · omega
          · omega
      · rw [List.length_append] at hi
        by_cases hi2 : i < (SD n h gs k).2.length
        · rw [List.getElem_append_left hi2] at hw
          exact ib i hi2 w hw
        · have e : i = (SD n h gs k).2.length := by omega
          subst e
          rw [List.getElem_append_right (le_refl _)] at hw
          exact gb _ (List.getElem_mem _) w hw

lemma dmain : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ)) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ (i : Fin gates'.length), ∀ w ∈ (gates'.get i).inputs, w < n + (i : ℕ)) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) := by
  intro n m gates out j h hops hj huniq hwf0 hhj hin hsep
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
  have hSl := SD_len n h gates gates.length le_rfl
  refine ⟨(SD n h gates gates.length).2,
    fun w => ((SD n h gates gates.length).1.getD (out w) (Sum.inl false)).elim (fun _ => 0) id,
    SD_ops n h j gates hhj' hops huniq' gates.length le_rfl,
    fun i w hw => (SD_wf n h gates (fun i hi w hw => hwf0 ⟨i, hi⟩ w hw) gates.length le_rfl).2 i i.2 w hw,
    SD_prefix n h gates gates.length le_rfl (by omega), ?_, ?_⟩
  · have hc := SD_count n h j gates hhj' hjl hjn hlen gates.length le_rfl
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
    change (drun (SD n h gates gates.length).2 (List.ofFn x)).getD (Sum.elim (fun _ => 0) id ((SD n h gates gates.length).1.getD (out w) (Sum.inl false))) false = dvalue ⟨gates, 0⟩ x (out w)
    rcases hc : (SD n h gates gates.length).1.getD (out w) (Sum.inl false) with b | w'
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


lemma mono43 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
      N * q ≤ gates.length := by
  intro q N L i0 p0 p1 h3 hN hc hi hj hne h0 h1 gates o hg hwf hev
  exact (B1643.thm43 q N L i0 p0 p1 h3 hN hc hi hj hne h0 h1).1 gates o hg hwf hev

lemma m44 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = p0))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = p1))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = true →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ N + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  intro q N L i0 p0 p1 hq3 hN hcard hint hjoin hne h0 h1 gates o j h hg hwf hjop hone hhj hjin hout hp0 hp1 hco
  classical
  have hoff : ∀ t : Fin N, t ≠ i0 → ∃ a : Fin N, (a = p0 ∨ a = p1) ∧ a ∉ L t := by
    intro t ht
    by_contra hc
    have m0 : p0 ∈ L t := by_contra (fun hn => hc ⟨p0, Or.inl rfl, hn⟩)
    have m1 : p1 ∈ L t := by_contra (fun hn => hc ⟨p1, Or.inr rfl, hn⟩)
    exact hne (Finset.card_le_one.mp (hint t i0 ht).le p0 (Finset.mem_inter.mpr ⟨m0, h0⟩) p1
      (Finset.mem_inter.mpr ⟨m1, h1⟩))
  have hpts : ∀ a : Fin N, (a = p0 ∨ a = p1) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = a))) = true := by
    intro a ha
    rcases ha with rfl | rfl
    · exact hp0
    · exact hp1
  have hlt : N + (h : ℕ) < N + (j : ℕ) := by
    have : (h : ℕ) < (j : ℕ) := hhj
    omega
  have htrue : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun _ : Fin N => true)) = true :=
    hmono N gates j hg hone (fun v : Fin N => decide (v = p0)) (fun _ : Fin N => true) (fun v _ => rfl) _ hlt hp0
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
  obtain ⟨gates', out', hg', hwf', hpre, hlen, hagree⟩ := dmain N N gates o j h hg hjop hone hwf hhj hjin (by
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
  have key := mono43 q N L i0 p0 p1 hq3 hN hcard hint hjoin hne h0 h1 gates' out' hg' hwf' (fun t x hx => (hagree t x (by
    rcases hx with hxa | hxa | hs
    · refine hmono N gates j hg hone (fun v : Fin N => decide (v = p0)) x (fun v hv => ?_) _ hlt hp0
      rw [of_decide_eq_true hv]
      exact hxa
    · refine hmono N gates j hg hone (fun v : Fin N => decide (v = p1)) x (fun v hv => ?_) _ hlt hp1
      rw [of_decide_eq_true hv]
      exact hxa
    · exact hmono N gates j hg hone (fun v : Fin N => decide (v ∉ L i0)) x
        (fun v hv => hs v (of_decide_eq_true hv)) _ hlt hco)).trans (hout t x))
  omega

end PEqualNP.Outside.L_meta_1644

theorem PEqualNP.Outside.L_meta_1644 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = p0))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = p1))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = true →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ N + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1644.m44
