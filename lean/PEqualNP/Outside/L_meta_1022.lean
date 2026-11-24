import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1022_aux

open PEqualNP.CircuitLowerBounds

-- Rows are ordered pairs of distinct true points. Every other input bit is false.
abbrev Row := {p : Fin 7 × Fin 7 // p.1 ≠ p.2}
abbrev Mask := Finset Row
def input (r : Row) (p : Fin 7) := decide (p = r.val.1 ∨ p = r.val.2)
def points (w : Fin 7) := ({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)
def hit (w : Fin 7) (r : Row) := decide (∃ p ∈ points w, input r p = true)
def line (w : Fin 7) : Mask := Finset.univ.filter (fun r => hit w r = true)
def pointMask (p : Fin 7) : Mask := Finset.univ.filter (fun r => input r p = true)

lemma band : ∀ r : Row, (Finset.univ.filter (fun p => input r p = false)).card = 5 := by decide

-- Two rows separate a line output from the union and intersection of any two other outputs.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma separating_rows : ∀ w a b : Fin 7, a ≠ w → b ≠ w →
    (∃ r : Row, hit w r = true ∧ hit a r = false ∧ hit b r = false) ∧
    (∃ r : Row, hit w r = false ∧ hit a r = true ∧ hit b r = true) := by decide +kernel

lemma incomparable {a w : Fin 7} (h : a ≠ w) : ¬ line w ⊆ line a := by
  obtain ⟨r, hw, ha, _⟩ := (separating_rows w a a h h).1
  intro hs
  have := hs (show r ∈ line w by simp [line, hw])
  simp [line, ha] at this

-- A mask belongs to a line when it lies below only that line or above only that line.
abbrev Own (s : Mask) (w : Fin 7) : Prop :=
  (s ⊆ line w ∧ ∀ a, a ≠ w → ¬ s ⊆ line a) ∨
  (line w ⊆ s ∧ ∀ a, a ≠ w → ¬ line a ⊆ s)

def credit (s : Mask) (w : Fin 7) : ℕ := if Own s w then 1 else 0

lemma credit_of_own {s : Mask} {w : Fin 7} (hw : Own s w) : credit s w = 1 := ite_eq_left hw

lemma own_unique {s : Mask} {u v : Fin 7} (hu : Own s u) (hv : Own s v) : u = v := by
  by_contra h
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact h2 v (Ne.symm h) h3
  · exact incomparable h (h3.trans h1)
  · exact incomparable (Ne.symm h) (h1.trans h3)
  · exact h2 v (Ne.symm h) h3

lemma line_credit (w : Fin 7) : credit (line w) w = 1 := by
  have h : Own (line w) w := Or.inl ⟨Finset.Subset.refl _, fun a ha => incomparable ha⟩
  exact ite_eq_left h

lemma capacity (s : Mask) : ∑ w, credit s w ≤ 1 := by
  classical
  by_cases h : ∃ w, Own s w
  · obtain ⟨w, hw⟩ := h
    rw [Finset.sum_eq_single w]
    · exact (show credit s w = 1 from ite_eq_left hw).le
    · intro v _ hv
      exact ite_eq_right (fun ho => hv (own_unique ho hw))
    · simp
  · have hn : ∀ w, credit s w = 0 := fun w => ite_eq_right (fun ho => h ⟨w, ho⟩)
    simp [hn]

def amount (S : Finset Mask) (w : Fin 7) := ∑ s ∈ S, credit s w
def budget (S : Finset Mask) := ∑ w, amount S w

lemma cost {S : Finset Mask} {s : Mask} (w : Fin 7) (hs : s ∈ S) :
    credit s w ≤ amount S w := Finset.single_le_sum (f := fun s => credit s w) (fun _ _ => Nat.zero_le _) hs

lemma union_cost {S : Finset Mask} {s t : Mask} {w} (hs : s ∈ S) (ht : t ∈ S)
    (_ : line w ∉ S) (h : s ∪ t = line w) : 1 ≤ amount S w := by
  classical
  have h1 : s ⊆ line w := h ▸ Finset.subset_union_left
  have h2 : t ⊆ line w := h ▸ Finset.subset_union_right
  by_cases hpriv : ∀ a, a ≠ w → ¬ s ⊆ line a
  · have hw : Own s w := Or.inl ⟨h1, hpriv⟩
    simpa only [credit_of_own hw] using cost w hs
  push Not at hpriv
  obtain ⟨a, ha, hsa⟩ := hpriv
  have hw : Own t w := by
    refine Or.inl ⟨h2, ?_⟩
    intro b hb htb
    obtain ⟨r, rw', ra, rb⟩ := (separating_rows w a b ha hb).1
    have hr : r ∈ s ∪ t := h ▸ (by simp [line, rw'])
    rcases Finset.mem_union.mp hr with hr | hr
    · simpa [line, ra] using hsa hr
    · simpa [line, rb] using htb hr
  simpa only [credit_of_own hw] using cost w ht

lemma inter_cost {S : Finset Mask} {s t : Mask} {w} (hs : s ∈ S) (ht : t ∈ S)
    (_ : line w ∉ S) (h : s ∩ t = line w) : 1 ≤ amount S w := by
  classical
  have h1 : line w ⊆ s := h ▸ Finset.inter_subset_left
  have h2 : line w ⊆ t := h ▸ Finset.inter_subset_right
  by_cases hpriv : ∀ a, a ≠ w → ¬ line a ⊆ s
  · have hw : Own s w := Or.inr ⟨h1, hpriv⟩
    simpa only [credit_of_own hw] using cost w hs
  push Not at hpriv
  obtain ⟨a, ha, has⟩ := hpriv
  have hw : Own t w := by
    refine Or.inr ⟨h2, ?_⟩
    intro b hb hbt
    obtain ⟨r, rw', ra, rb⟩ := (separating_rows w a b ha hb).2
    have hr : r ∈ s ∩ t := Finset.mem_inter.mpr
      ⟨has (by simp [line, ra]), hbt (by simp [line, rb])⟩
    rw [h] at hr
    simp [line, rw'] at hr
  simpa only [credit_of_own hw] using cost w ht


def pool (xs : List Mask) : Finset Mask := insert ∅ (insert Finset.univ xs.toFinset)
def val (xs : List Mask) (i : ℕ) : Mask := xs.getD i ∅
def gateMask (xs : List Mask) (g : Gate) : Mask :=
  Finset.univ.filter (fun v => g.op.eval (g.inputs.map (fun i => decide (v ∈ val xs i))))

lemma available (xs : List Mask) (i : ℕ) : val xs i ∈ pool xs := by
  by_cases h : i < xs.length
  · unfold val
    rw [List.getD_eq_getElem _ _ h]
    simp [pool,List.getElem_mem]
  · unfold val
    rw [List.getD_eq_default _ _ (by omega : xs.length ≤ i)]
    simp [pool]

lemma gate_cost (xs : List Mask) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 7) (hn : line w ∉ pool xs) (he : gateMask xs g = line w) :
    1 ≤ amount (pool xs) w := by
  obtain ⟨op,ins⟩ := g
  rcases hg with ⟨ha,hl⟩
  change op = GateOp.and ∨ op = GateOp.or at ha
  change ins.length ≤ 2 at hl
  have non (s : Mask) (hm : s ∈ pool xs) (eq : s = line w) : False := hn (eq ▸ hm)
  cases ins with
  | nil =>
    rcases ha with rfl|rfl <;> simp [gateMask,GateOp.eval] at he <;>
      exact (non _ (by simp [pool]) he).elim
  | cons i l =>
    cases l with
    | nil =>
      rcases ha with rfl|rfl <;> simp [gateMask,GateOp.eval] at he <;>
        exact (non _ (available xs i) he).elim
    | cons j l =>
      cases l with
      | cons k l => simp at hl
      | nil =>
        rcases ha with rfl|rfl
        · apply inter_cost (available xs i) (available xs j) hn
          rw [← he]
          ext v
          simp [gateMask,GateOp.eval]
        · apply union_cost (available xs i) (available xs j) hn
          rw [← he]
          ext v
          simp [gateMask,GateOp.eval]

def rich (xs : List Mask) := ∀ w, line w ∈ pool xs → 2 ≤ amount (pool xs) w
def next (xs : List Mask) (g : Gate) := xs ++ [gateMask xs g]

lemma pool_next (xs : List Mask) (g : Gate) : pool (next xs g) = insert (gateMask xs g) (pool xs) := by
  ext s
  simp [pool, next] <;> tauto

lemma push (xs : List Mask) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) (h : rich xs) :
    rich (next xs g) ∧ budget (pool (next xs g)) ≤ budget (pool xs) + 1 := by
  by_cases hm : gateMask xs g ∈ pool xs
  · simpa [rich,pool_next,Finset.insert_eq_of_mem hm] using h
  have add (w : Fin 7) : amount (pool (next xs g)) w =
      credit (gateMask xs g) w + amount (pool xs) w := by simp [amount,pool_next,hm]
  constructor
  · intro w hw
    rw [pool_next,Finset.mem_insert] at hw
    rw [add]
    rcases hw with eq|old
    · have hh := gate_cost xs g hg w (fun e => hm (eq ▸ e)) eq.symm
      rw [← eq]
      rw [line_credit]
      omega
    · exact (h w old).trans (Nat.le_add_left _ _)
  · simp only [budget,add,Finset.sum_add_distrib]
    have := capacity (gateMask xs g)
    omega

def initial : List Mask := List.ofFn pointMask
lemma init_rich : rich initial := by unfold rich; decide +kernel
lemma init_budget : budget (pool initial) = 0 := by decide +kernel

lemma accumulate (gs : List Gate) (xs : List Mask) (hr : rich xs)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    rich (gs.foldl next xs) ∧ budget (pool (gs.foldl next xs)) ≤ budget (pool xs) + gs.length := by
  induction gs generalizing xs with
  | nil => simp [hr]
  | cons g gs ih =>
    obtain ⟨h1,h2⟩ := push xs g (hg g (by simp)) hr
    obtain ⟨h3,h4⟩ := ih (next xs g) h1 (fun z hz => hg z (by simp [hz]))
    exact ⟨h3,by simp only [List.foldl_cons,List.length_cons]; omega⟩

def bit (v : Row) (s : Mask) : Bool := decide (v ∈ s)
def boolGate (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

lemma read_bit (v : Row) (xs : List Mask) (i : ℕ) :
    (xs.map (bit v)).getD i false = bit v (val xs i) := by
  have e : bit v ∅ = false := by simp [bit]
  rw [← e]
  exact List.getD_map xs ∅ (bit v)

lemma map_next (v : Row) (xs : List Mask) (g : Gate) :
    (next xs g).map (bit v) = boolGate (xs.map (bit v)) g := by
  simp only [next,boolGate,List.map_append,List.map_cons,List.map_nil,read_bit]
  congr 2
  simp [bit,gateMask]

lemma map_run (v : Row) (gs : List Gate) (xs : List Mask) :
    (gs.foldl next xs).map (bit v) = gs.foldl boolGate (xs.map (bit v)) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih => rw [List.foldl_cons,List.foldl_cons,ih,map_next]

lemma eval_bit (v : Row) (gs : List Gate) (o : ℕ) :
    (Circuit.mk gs o).eval (List.ofFn (input v)) =
      bit v (val (gs.foldl next initial) o) := by
  have hi : initial.map (bit v) = List.ofFn (input v) := by
    simp [initial, bit, pointMask]
  change (gs.foldl boolGate _).getD o false = _
  rw [← hi,← map_run,read_bit]

end PEqualNP.Outside.L_meta_1022_aux

open PEqualNP.Outside.L_meta_1022_aux

theorem PEqualNP.Outside.L_meta_1022 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 7) (x : Fin 7 → Bool), ((Finset.univ.filter (fun p : Fin 7 => x p = false)).card = 4 ∨ (Finset.univ.filter (fun p : Fin 7 => x p = false)).card = 5) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) → 14 ≤ gates.length := by
  intro gs out hg ho
  let xs := gs.foldl next initial
  have all_lines (w : Fin 7) : line w ∈ pool xs := by
    have he : val xs (out w) = line w := by
      ext r
      have h := ho w (input r) (Or.inr (band r))
      rw [eval_bit] at h
      simpa [xs, bit, line, hit, points] using (Bool.eq_iff_iff.mp h)
    exact he ▸ available xs (out w)
  obtain ⟨hr, hb⟩ := accumulate gs initial init_rich hg
  have lower : (∑ _w : Fin 7, (2 : ℕ)) ≤ budget (pool xs) :=
    Finset.sum_le_sum (fun w _ => hr w (all_lines w))
  change budget (pool xs) ≤ _ at hb
  rw [init_budget] at hb
  simp at lower
  omega
