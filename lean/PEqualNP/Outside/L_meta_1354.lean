import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354

open PEqualNP.CircuitLowerBounds

def remap (n sentinel i : Nat) : Nat :=
  if i < n then i else if i = n then sentinel else i - 1

def mapGate (n sentinel : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap n sentinel)⟩

def mapAll (n sentinel : Nat) (gs : List Gate) : List Gate :=
  gs.map (mapGate n sentinel)

theorem mapAll_op (n sentinel : Nat) (gs : List Gate) :
    (mapAll n sentinel gs).map Gate.op = gs.map Gate.op := by
  induction gs with
  | nil => rfl
  | cons g gs _ =>
    simp [mapAll, mapGate]

theorem mapAll_len (n sentinel : Nat) (gs : List Gate) :
    (mapAll n sentinel gs).map (fun g => g.inputs.length) =
      gs.map (fun g => g.inputs.length) := by
  induction gs with
  | nil => rfl
  | cons g gs _ =>
    simp [mapAll, mapGate, List.length_map]

def W (gs : List Gate) (x : List Bool) : List Bool :=
  Circuit.wires ⟨gs, 0⟩ x

theorem W_nil (x : List Bool) : W [] x = x := by
  simp [W, Circuit.wires]

theorem W_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    W (g :: gs) x =
      W gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := by
  simp [W, Circuit.wires, List.foldl_cons]

theorem eval_eq_getD (gs : List Gate) (idx : Nat) (x : List Bool) :
    Circuit.eval ⟨gs, idx⟩ x = (W gs x).getD idx false := by
  unfold Circuit.eval W
  have : Circuit.wires ⟨gs, idx⟩ x = Circuit.wires ⟨gs, 0⟩ x := by
    simp [Circuit.wires]
  simp [this]

theorem getD_ge (l : List Bool) (i : Nat) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD]
  have : l[i]? = none := List.getElem?_eq_none (by omega)
  simp [this]

theorem getD_append_lt (l : List Bool) (b : Bool) (i : Nat) (hi : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
    List.getElem_append_left hi]

theorem getD_append_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp

theorem read_ok (n sentinel : Nat) (w' w : List Bool)
    (hshift : ∀ i, w'.getD i false = w.getD (if i < n then i else i + 1) false)
    (hfalse : w.getD n false = false)
    (hsent : w'.length ≤ sentinel) (i : Nat) :
    w'.getD (remap n sentinel i) false = w.getD i false := by
  by_cases h1 : i < n
  · have hr : remap n sentinel i = i := by simp [remap, h1]
    rw [hr, hshift]
    simp [h1]
  · by_cases h2 : i = n
    · have hr : remap n sentinel i = sentinel := by simp [remap, h2]
      rw [hr, getD_ge w' sentinel hsent]
      simpa [h2] using hfalse.symm
    · have hr : remap n sentinel i = i - 1 := by simp [remap, h1, h2]
      rw [hr, hshift (i - 1)]
      have hlt : ¬ i - 1 < n := by omega
      have he : (i - 1) + 1 = i := by omega
      simp [hlt, he]

theorem reads_eq (n sentinel : Nat) (g : Gate) (w' w : List Bool)
    (hshift : ∀ i, w'.getD i false = w.getD (if i < n then i else i + 1) false)
    (hfalse : w.getD n false = false)
    (hsent : w'.length ≤ sentinel) :
    g.inputs.map (fun i => w.getD i false) =
      (mapGate n sentinel g).inputs.map (fun i => w'.getD i false) := by
  simp only [mapGate]
  induction g.inputs with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih⟩
    symm
    exact read_ok n sentinel w' w hshift hfalse hsent a

theorem shift_append (n : Nat) (w' w : List Bool) (b : Bool)
    (hge : n ≤ w'.length)
    (hlen : w'.length + 1 = w.length)
    (hshift : ∀ i, w'.getD i false = w.getD (if i < n then i else i + 1) false) (i : Nat) :
    (w' ++ [b]).getD i false =
      (w ++ [b]).getD (if i < n then i else i + 1) false := by
  by_cases hi : i < w'.length
  · rw [getD_append_lt w' b i hi]
    have hidx : (if i < n then i else i + 1) < w.length := by
      by_cases hn : i < n
      · simp [hn]
        omega
      · simp [hn]
        omega
    rw [getD_append_lt w b _ hidx, hshift]
  · by_cases he : i = w'.length
    · subst he
      rw [getD_append_eq]
      have hn : ¬ w'.length < n := by omega
      simp [hn]
      have hlen' : w'.length + 1 = w.length := hlen
      simp [hlen']
    · have hgt' : (w' ++ [b]).length ≤ i := by simp; omega
      rw [getD_ge (w' ++ [b]) i hgt']
      have hn : ¬ i < n := by omega
      simp [hn]
      have hgt2 : (w ++ [b]).length ≤ i + 1 := by simp; omega
      exact getD_ge (w ++ [b]) (i + 1) hgt2

theorem false_append (n : Nat) (w : List Bool) (b : Bool)
    (hn : n < w.length) (hfalse : w.getD n false = false) :
    (w ++ [b]).getD n false = false := by
  rw [getD_append_lt w b n hn, hfalse]

theorem inv (n sentinel : Nat) (gs : List Gate) (w' w : List Bool)
    (hlen : w'.length + 1 = w.length)
    (hge : n ≤ w'.length)
    (hshift : ∀ i, w'.getD i false = w.getD (if i < n then i else i + 1) false)
    (hfalse : w.getD n false = false)
    (hsent : w'.length + gs.length ≤ sentinel) :
    ∀ i, (W (mapAll n sentinel gs) w').getD i false =
      (W gs w).getD (if i < n then i else i + 1) false := by
  induction gs generalizing w' w with
  | nil =>
    simp [mapAll, W_nil]
    exact hshift
  | cons g gs ih =>
    have hsent' : w'.length ≤ sentinel := by
      have : gs.length + 1 = (g :: gs).length := rfl
      omega
    have hreads := reads_eq n sentinel g w' w hshift hfalse hsent'
    set b : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hb :
        (mapGate n sentinel g).op.eval
            ((mapGate n sentinel g).inputs.map fun i => w'.getD i false) = b := by
      unfold mapGate at hreads ⊢
      simp only [b]
      rw [← hreads]
    have hlen1 : (w' ++ [b]).length + 1 = (w ++ [b]).length := by simp [hlen]
    have hge1 : n ≤ (w' ++ [b]).length := by simp; omega
    have hfalse1 : (w ++ [b]).getD n false = false :=
      false_append n w b (by omega) hfalse
    have hshift1 :
        ∀ i, (w' ++ [b]).getD i false =
          (w ++ [b]).getD (if i < n then i else i + 1) false :=
      fun i => shift_append n w' w b hge hlen hshift i
    have hsent1 : (w' ++ [b]).length + gs.length ≤ sentinel := by
      have h1 : (w' ++ [b]).length = w'.length + 1 := by simp
      have h2 : (g :: gs).length = gs.length + 1 := rfl
      omega
    have htail := ih (w' ++ [b]) (w ++ [b]) hlen1 hge1 hshift1 hfalse1 hsent1
    intro i
    simp only [mapAll, List.map_cons, W_cons, hb]
    exact htail i

theorem base_false (n : Nat) (x : Fin n → Bool) :
    (List.ofFn x ++ [false]).getD n false = false := by
  simp [List.length_ofFn]

theorem base_shift (n : Nat) (x : Fin n → Bool) :
    ∀ i, (List.ofFn x).getD i false =
      (List.ofFn x ++ [false]).getD (if i < n then i else i + 1) false := by
  intro i
  by_cases hi : i < n
  · have hif : (if i < n then i else i + 1) = i := by simp [hi]
    rw [hif]
    exact (getD_append_lt (List.ofFn x) false i (by simpa using hi)).symm
  · have hx : (List.ofFn x).length ≤ i := by simpa using hi
    rw [getD_ge (List.ofFn x) i hx]
    have hn : ¬ i < n := hi
    simp [hn]

end PEqualNP.Outside.L_meta_1354

theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  refine ⟨PEqualNP.Outside.L_meta_1354.mapAll n (n + gates.length) gates, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_1354.mapAll_op n (n + gates.length) gates
  · exact PEqualNP.Outside.L_meta_1354.mapAll_len n (n + gates.length) gates
  · intro j x hj
    have hshift :=
      PEqualNP.Outside.L_meta_1354.inv n (n + gates.length) gates (List.ofFn x)
        (List.ofFn x ++ [false]) (by simp) (by simp) 
        (PEqualNP.Outside.L_meta_1354.base_shift n x)
        (PEqualNP.Outside.L_meta_1354.base_false n x) (by simp)
    rw [PEqualNP.Outside.L_meta_1354.eval_eq_getD, PEqualNP.Outside.L_meta_1354.eval_eq_getD]
    have hnj : ¬ n + j < n := by omega
    rw [hshift (n + j)]
    simp [hnj]
    have : n + j + 1 = n + 1 + j := by omega
    simp [this]
