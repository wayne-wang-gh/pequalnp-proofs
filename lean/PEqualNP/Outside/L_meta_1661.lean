import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1661

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

lemma getD_inr_mem (ρ : List (Bool ⊕ ℕ)) (r w : ℕ) (h : ρ.getD r (Sum.inl false) = Sum.inr w) :
    Sum.inr w ∈ ρ := by
  by_cases hr : r < ρ.length
  · rw [List.getD_eq_getElem _ _ hr] at h
    rw [← h]
    exact List.getElem_mem hr
  · rw [List.getD_eq_default _ _ (by omega)] at h
    exact absurd h (by simp)

lemma fin3_wf (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) (hl : ∀ w ∈ l, w < N) :
    (∀ w, (fin3 a op N l).1 = Sum.inr w → w < N + (fin3 a op N l).2.length) ∧
    ∀ g' ∈ (fin3 a op N l).2, ∀ w ∈ g'.inputs, w < N := by
  refine ⟨?_, ?_⟩
  · rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
    · intro w hw
      simp [fin3] at hw
    · intro w' hw'
      simp only [fin3, Sum.inr.injEq] at hw'
      have := hl w (by simp)
      omega
    · intro w' hw'
      simp only [fin3, Sum.inr.injEq] at hw'
      simp only [fin3, List.length_singleton]
      omega
  · intro g' hg' w hw
    obtain ⟨_, h2⟩ := fin3_mem a op N l g' hg'
    rw [h2] at hw
    exact hl w hw

lemma gen_wf (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) (hρ : ∀ w, Sum.inr w ∈ ρ → w < N) :
    (∀ w, (gen ρ N g).1 = Sum.inr w → w < N + (gen ρ N g).2.length) ∧
    ∀ g' ∈ (gen ρ N g).2, ∀ w ∈ g'.inputs, w < N := by
  unfold gen
  split_ifs
  · exact ⟨fun w hw => absurd hw (by simp), fun g' hg' => absurd hg' (by simp)⟩
  · apply fin3_wf
    intro w hw
    obtain ⟨c, hc, hcw⟩ := List.mem_filterMap.mp hw
    obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hc
    have hc' : c = Sum.inr w := Sum.getRight?_eq_some_iff.mp hcw
    rw [hc'] at hre
    exact hρ w (getD_inr_mem ρ r w hre)

lemma wf_append (n : ℕ) (A e : List Gate)
    (hA : ∀ i (hi : i < A.length), ∀ w ∈ A[i].inputs, w < n + i)
    (he : e.length ≤ 1) (he2 : ∀ g' ∈ e, ∀ w ∈ g'.inputs, w < n + A.length) :
    ∀ i (hi : i < (A ++ e).length), ∀ w ∈ (A ++ e)[i].inputs, w < n + i := by
  intro i hi w hw
  by_cases h1 : i < A.length
  · rw [List.getElem_append_left h1] at hw
    exact hA i h1 w hw
  · rw [List.length_append] at hi
    rw [List.getElem_append_right (by omega)] at hw
    have := he2 _ (List.getElem_mem _) w hw
    omega

lemma SD_wf (n h : ℕ) (gs : List Gate)
    (hearly : ∀ i (hi : i < gs.length), ∀ w ∈ gs[i].inputs, w < n + i) :
    ∀ k, k ≤ gs.length →
      (∀ w, Sum.inr w ∈ (SD n h gs k).1 → w < n + (SD n h gs k).2.length) ∧
      ∀ i (hi : i < (SD n h gs k).2.length), ∀ w ∈ ((SD n h gs k).2[i]).inputs, w < n + i := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · intro w hw
      have : w < n := by simpa [SD] using hw
      exact Nat.lt_add_right _ this
    · intro i hi
      simp [SD] at hi
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [SD_succ n h gs k hkl]
    unfold stp
    split_ifs with h1 h2 h3
    · have hk2 : (SD n h gs k).2.length = k := by
        rw [(SD_low n h gs k (by omega) (by omega)).1]
        simp
        omega
      refine ⟨?_, ?_⟩
      · intro w hw
        simp only [List.length_append, List.length_singleton]
        rcases List.mem_append.mp hw with hm | hm
        · have := ih1 w hm
          omega
        · have e : w = n + (SD n h gs k).2.length := by simpa using hm
          omega
      · exact wf_append n _ _ ih2 (by simp) (fun g' hg' w hw => by
          rw [List.mem_singleton.mp hg'] at hw
          have := hearly k hkl w hw
          omega)
    · refine ⟨fun w hw => ?_, ih2⟩
      rcases List.mem_append.mp hw with hm | hm
      · exact ih1 w hm
      · simp at hm
    · refine ⟨fun w hw => ?_, ih2⟩
      rcases List.mem_append.mp hw with hm | hm
      · exact ih1 w hm
      · simp at hm
    · obtain ⟨g1, g2⟩ := gen_wf (SD n h gs k).1 (n + (SD n h gs k).2.length) gs[k] ih1
      refine ⟨?_, wf_append n _ _ ih2 (gen_len _ _ _) g2⟩
      intro w hw
      rw [List.length_append]
      rcases List.mem_append.mp hw with hm | hm
      · have := ih1 w hm
        omega
      · have := g1 w (List.mem_singleton.mp hm).symm
        omega

lemma SD_stable (n h : ℕ) (gs : List Gate) (k0 : ℕ) (i : ℕ) (hi : i < n + k0) :
    ∀ k, k ≤ gs.length → k0 ≤ k →
      (SD n h gs k).1.getD i (Sum.inl false) = (SD n h gs k0).1.getD i (Sum.inl false) := by
  intro k
  induction k with
  | zero =>
    intro _ h0
    have : k0 = 0 := by omega
    subst this
    rfl
  | succ k ih =>
    intro hk hk0
    by_cases he : k0 = k + 1
    · subst he
      rfl
    · have hl := SD_len n h gs k (by omega)
      rw [SD_succ n h gs k (by omega)]
      obtain ⟨d, hd⟩ := stp_fst n h k gs[k] (SD n h gs k)
      rw [hd, List.getD_append _ _ _ _ (by omega)]
      exact ih (by omega) (by omega)

lemma gen_and (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) (hop : g.op = GateOp.and)
    (r : ℕ) (hr : r ∈ g.inputs) (hρ : ρ.getD r (Sum.inl false) = Sum.inl false) :
    (gen ρ N g).1 = Sum.inl false := by
  have hm : Sum.inl (isOrD g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) := by
    rw [hop]
    exact List.mem_map.mpr ⟨r, hr, hρ⟩
  unfold gen
  rw [if_pos hm, hop]
  rfl

lemma SD_and (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (a : ℕ) (ha : a < gs.length) (hja : j < a)
    (hop : gs[a].op = GateOp.and) (hr : n + j ∈ gs[a].inputs) :
    (SD n h gs (a + 1)).1.getD (n + a) (Sum.inl false) = Sum.inl false := by
  have hl := SD_len n h gs a (by omega)
  rw [SD_succ n h gs a ha]
  unfold stp
  have h1 : ¬ a < h := by omega
  have h2 : ¬ a = h := by omega
  have h3 : ¬ isNot gs[a].op = true := by rw [hop]; simp [isNot]
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hl, Nat.sub_self, List.getD_cons_zero]
  exact gen_and _ _ _ hop (n + j) hr (SD_j n h j gs hhj hj hjn a (by omega) hja)

lemma SD_false (n h : ℕ) (gs : List Gate) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gs.length) (hhk : h < k) (r : ℕ) (hr : r ∈ gs[k].inputs)
    (hρ : (SD n h gs k).1.getD r (Sum.inl false) = Sum.inl false) :
    (SD n h gs (k + 1)).2 = (SD n h gs k).2 := by
  rw [SD_succ n h gs k hk]
  unfold stp
  have h1 : ¬ k < h := by omega
  have h2 : ¬ k = h := by omega
  simp only [h1, h2, ↓reduceIte]
  split_ifs
  · rfl
  · rw [gen_reader _ _ gs[k] (hlen _ (List.getElem_mem hk)) r hr hρ]
    simp

lemma SD_count2 (n h : ℕ) (gs : List Gate) (B : Finset ℕ)
    (hB : ∀ k ∈ B, ∀ hk : k < gs.length, (SD n h gs (k + 1)).2 = (SD n h gs k).2) :
    ∀ k, k ≤ gs.length →
      (SD n h gs k).2.length + (B.filter (fun i => i < k)).card ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp [SD]
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    by_cases hb : k ∈ B
    · rw [hB k hb hkl]
      have hsub : B.filter (fun i => i < k + 1) ⊆ insert k (B.filter (fun i => i < k)) := by
        intro i hi
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
        by_cases he : i = k
        · exact Finset.mem_insert.mpr (Or.inl he)
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h1, by omega⟩)
      have c1 := Finset.card_le_card hsub
      have c2 := Finset.card_insert_le k (B.filter (fun i => i < k))
      omega
    · have hsub : B.filter (fun i => i < k + 1) ⊆ B.filter (fun i => i < k) := by
        intro i hi
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
        have he : i ≠ k := fun e => hb (e ▸ h1)
        exact Finset.mem_filter.mpr ⟨h1, by omega⟩
      have c1 := Finset.card_le_card hsub
      rw [SD_succ n h gs k hkl]
      obtain ⟨e, he, hel⟩ := stp_snd n h k gs[k] (SD n h gs k)
      rw [he, List.length_append]
      omega

lemma cardB {L : ℕ} (R W : Finset (Fin L)) (h j : ℕ) (hhj : h < j)
    (hR : ∀ i ∈ R, j < i.1) (hW : ∀ i ∈ W, i ∉ R ∧ i.1 ≠ h ∧ j < i.1) :
    R.card + W.card + 2 ≤ (insert h (insert j (R.image Fin.val ∪ W.image Fin.val))).card := by
  have hRi : (R.image Fin.val).card = R.card := Finset.card_image_of_injective _ Fin.val_injective
  have hWi : (W.image Fin.val).card = W.card := Finset.card_image_of_injective _ Fin.val_injective
  have hdis : Disjoint (R.image Fin.val) (W.image Fin.val) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    obtain ⟨i1, hi1, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨i2, hi2, he⟩ := Finset.mem_image.mp h2
    have e : i2 = i1 := Fin.ext he
    subst e
    exact (hW i2 hi2).1 hi1
  have hU := Finset.card_union_of_disjoint hdis
  have hgt : ∀ k ∈ R.image Fin.val ∪ W.image Fin.val, j < k := by
    intro k hk
    rcases Finset.mem_union.mp hk with hm | hm
    · obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hm
      exact hR i' hi'
    · obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hm
      exact (hW i' hi').2.2
  have hjU : j ∉ R.image Fin.val ∪ W.image Fin.val := fun hm => by
    have := hgt j hm
    omega
  have hhU : h ∉ insert j (R.image Fin.val ∪ W.image Fin.val) := by
    intro hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · omega
    · have := hgt h hm
      omega
  have c1 := Finset.card_insert_of_notMem hhU
  have c2 := Finset.card_insert_of_notMem hjU
  omega

end PEqualNP.Outside.L_meta_1661

theorem PEqualNP.Outside.L_meta_1661 : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∀ W : Finset (Fin gates.length), (∀ i : Fin gates.length, i ∈ W ↔ (i ≠ h ∧ ¬ (j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs) ∧
      ∃ a : Fin gates.length, j < a ∧ n + (j : ℕ) ∈ (gates.get a).inputs ∧ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ n + (a : ℕ) ∈ (gates.get i).inputs)) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ (i : Fin gates'.length), ∀ w ∈ (gates'.get i).inputs, w < n + (i : ℕ)) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + W.card
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) := by
  intro n m gates out j h hops hearly hj huniq hhj hin hsep W hW
  have hjl : (j : ℕ) < gates.length := j.2
  have hhj' : (h : ℕ) < (j : ℕ) := hhj
  have hjn : gates[(j : ℕ)].op = GateOp.not := hj
  have huniq' : ∀ i (hi : i < gates.length), gates[i].op = GateOp.not → i = (j : ℕ) :=
    fun i hi ho => congrArg Fin.val (huniq ⟨i, hi⟩ ho)
  have hops1 : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hops g hg).1
  have hlen : ∀ g ∈ gates, g.inputs.length ≤ 2 := fun g hg => (hops g hg).2
  have hearly' : ∀ i (hi : i < gates.length), ∀ w ∈ gates[i].inputs, w < n + i :=
    fun i hi w hw => hearly ⟨i, hi⟩ w hw
  have hjv : ∀ x : Fin n → Bool, PEqualNP.Outside.L_meta_1661.dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true →
      PEqualNP.Outside.L_meta_1661.dvalue ⟨gates, 0⟩ x (n + (j : ℕ)) = false := by
    intro x hx
    obtain ⟨r, hr⟩ := hin
    have hr' : gates[(j : ℕ)].inputs = (n + (h : ℕ)) :: r := hr
    rw [PEqualNP.Outside.L_meta_1661.dgatevalueP gates x j hjl, hjn, hr']
    have : n + (h : ℕ) < n + (j : ℕ) := by omega
    simp [GateOp.eval, this, hx]
  have hsem := fun (x : Fin n → Bool) (hx : PEqualNP.Outside.L_meta_1661.dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true) =>
    PEqualNP.Outside.L_meta_1661.sem n h j gates x hops1 huniq' hx (hjv x hx) gates.length le_rfl
  have hSl := PEqualNP.Outside.L_meta_1661.SD_len n h gates gates.length le_rfl
  have hwf := PEqualNP.Outside.L_meta_1661.SD_wf n h gates hearly' gates.length le_rfl
  refine ⟨(PEqualNP.Outside.L_meta_1661.SD n h gates gates.length).2,
    fun w => ((PEqualNP.Outside.L_meta_1661.SD n h gates gates.length).1.getD (out w) (Sum.inl false)).elim (fun _ => 0) id,
    PEqualNP.Outside.L_meta_1661.SD_ops n h j gates hhj' hops huniq' gates.length le_rfl,
    fun i w hw => hwf.2 i.1 i.2 w hw,
    PEqualNP.Outside.L_meta_1661.SD_prefix n h gates gates.length le_rfl (by omega), ?_, ?_⟩
  · obtain ⟨R, hRe⟩ : ∃ R : Finset (Fin gates.length), R = Finset.univ.filter
        (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs) := ⟨_, rfl⟩
    rw [← hRe]
    have hRm : ∀ i ∈ R, j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs := by
      intro i hi
      rw [hRe] at hi
      exact (Finset.mem_filter.mp hi).2
    have hWm : ∀ i ∈ W, i ∉ R ∧ (i : ℕ) ≠ (h : ℕ) ∧ (j : ℕ) < (i : ℕ) := by
      intro i hi
      obtain ⟨h1, h2, a, hja, hra, hopa, hai⟩ := (hW i).mp hi
      refine ⟨fun hiR => h2 (hRm i hiR), fun e => h1 (Fin.ext e), ?_⟩
      have hlt := hearly i _ hai
      have hja' : (j : ℕ) < (a : ℕ) := hja
      omega
    have hcB := PEqualNP.Outside.L_meta_1661.cardB R W (h : ℕ) (j : ℕ) hhj' (fun i hi => (hRm i hi).1) hWm
    obtain ⟨B, hBe⟩ : ∃ B : Finset ℕ, B = insert (h : ℕ) (insert (j : ℕ) (R.image Fin.val ∪ W.image Fin.val)) := ⟨_, rfl⟩
    rw [← hBe] at hcB
    have hBstep : ∀ k ∈ B, ∀ hk : k < gates.length,
        (PEqualNP.Outside.L_meta_1661.SD n h gates (k + 1)).2 = (PEqualNP.Outside.L_meta_1661.SD n h gates k).2 := by
      intro k hkB hk
      rw [hBe] at hkB
      rcases Finset.mem_insert.mp hkB with hi | hi
      · exact PEqualNP.Outside.L_meta_1661.SD_bad n h j gates hhj' hjl hjn hlen k hk (by
          unfold PEqualNP.Outside.L_meta_1661.bad
          simp only [decide_eq_true_eq]
          exact Or.inl hi)
      rcases Finset.mem_insert.mp hi with hi | hi
      · exact PEqualNP.Outside.L_meta_1661.SD_bad n h j gates hhj' hjl hjn hlen k hk (by
          unfold PEqualNP.Outside.L_meta_1661.bad
          simp only [decide_eq_true_eq]
          exact Or.inr (Or.inl hi))
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨a, b⟩ := hRm i' hi'
        have a' : (j : ℕ) < (i' : ℕ) := a
        exact PEqualNP.Outside.L_meta_1661.SD_false n h gates hlen i' hk (by omega) (n + (j : ℕ)) b
          (PEqualNP.Outside.L_meta_1661.SD_j n h j gates hhj' hjl hjn i' (by omega) a')
      · obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨_, _, a, hja, hra, hopa, hai⟩ := (hW i').mp hi'
        have hlt := hearly i' _ hai
        have hja' : (j : ℕ) < (a : ℕ) := hja
        have e1 := PEqualNP.Outside.L_meta_1661.SD_and n h j gates hhj' hjl hjn a a.2 hja' hopa hra
        have e2 := PEqualNP.Outside.L_meta_1661.SD_stable n h gates ((a : ℕ) + 1) (n + (a : ℕ)) (by omega)
          i' (by omega) (by omega)
        exact PEqualNP.Outside.L_meta_1661.SD_false n h gates hlen i' hk (by omega) (n + (a : ℕ)) hai
          (e2.trans e1)
    have hBlt : ∀ k ∈ B, k < gates.length := by
      intro k hkB
      rw [hBe] at hkB
      rcases Finset.mem_insert.mp hkB with hi | hi
      · omega
      rcases Finset.mem_insert.mp hi with hi | hi
      · omega
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hi
        exact i'.2
      · obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hi
        exact i'.2
    have hc := PEqualNP.Outside.L_meta_1661.SD_count2 n h gates B hBstep gates.length le_rfl
    have hsub : B ⊆ B.filter (fun i => i < gates.length) :=
      fun k hk => Finset.mem_filter.mpr ⟨hk, hBlt k hk⟩
    have hcard := Finset.card_le_card hsub
    omega
  · intro w x hx
    have hx' : PEqualNP.Outside.L_meta_1661.dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true := hx
    obtain ⟨x0, y0, hx0, hy0, ox, oy⟩ := hsep w
    have ox' : PEqualNP.Outside.L_meta_1661.dvalue ⟨gates, 0⟩ x0 (out w) = true := ox
    have oy' : PEqualNP.Outside.L_meta_1661.dvalue ⟨gates, 0⟩ y0 (out w) = false := oy
    have a1 := hsem x0 hx0 (out w)
    have a2 := hsem y0 hy0 (out w)
    have a3 := hsem x hx' (out w)
    change (PEqualNP.Outside.L_meta_1661.drun (PEqualNP.Outside.L_meta_1661.SD n h gates gates.length).2 (List.ofFn x)).getD (Sum.elim (fun _ => 0) id ((PEqualNP.Outside.L_meta_1661.SD n h gates gates.length).1.getD (out w) (Sum.inl false))) false = PEqualNP.Outside.L_meta_1661.dvalue ⟨gates, 0⟩ x (out w)
    rcases hc : (PEqualNP.Outside.L_meta_1661.SD n h gates gates.length).1.getD (out w) (Sum.inl false) with b | w'
    · rw [hc] at a1 a2
      exfalso
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a1 a2
        have e1 : PEqualNP.Outside.L_meta_1661.dvalue ⟨gates, 0⟩ x0 (out w) = b := a1
        have e2 : PEqualNP.Outside.L_meta_1661.dvalue ⟨gates, 0⟩ y0 (out w) = b := a2
        rw [ox'] at e1
        rw [oy'] at e2
        rw [← e1] at e2
        exact Bool.noConfusion e2
      · rw [PEqualNP.Outside.L_meta_1661.dmissingvalue _ x0 (out w) (by change n + gates.length ≤ _; omega)] at ox'
        exact Bool.noConfusion ox'
    · rw [hc] at a3
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a3
        exact a3.2
      · simp only [hlt, ↓reduceIte] at a3
        rw [PEqualNP.Outside.L_meta_1661.dmissingvalue _ x (out w) (by change n + gates.length ≤ _; omega)]
        exact a3.2
