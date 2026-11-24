import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1323

open PEqualNP.CircuitLowerBounds

def nin (gates : List Gate) (t : Fin gates.length) {n : ℕ} (x : Fin n → Bool) : Bool :=
  ((gates.get t).inputs.map (fun k : ℕ => (Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn x)).getD k false)).headD false

lemma wires_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ w = Circuit.wires ⟨gs, 0⟩ w ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ w).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma wires_length (gs : List Gate) : ∀ w : List Bool,
    (Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => intro w; simp [Circuit.wires]
  | append_singleton gs g ih =>
    intro w
    rw [wires_snoc]
    simp [ih]
    omega

lemma take_succ_eq (gates : List Gate) (m : ℕ) (hm : m < gates.length) :
    gates.take (m + 1) = gates.take m ++ [gates[m]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hm]
  simp

lemma getD_snoc (L : List Bool) (v : Bool) (k : ℕ) :
    (L ++ [v]).getD k false = if k < L.length then L.getD k false else if k = L.length then v else false := by
  rcases lt_trichotomy k L.length with h | h | h
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

lemma all_mono (ins : List ℕ) (f h : ℕ → Bool) (hfh : ∀ k, f k = true → h k = true) :
    (ins.map f).all id = true → (ins.map h).all id = true := by
  induction ins with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true]
    exact fun H => ⟨hfh a H.1, ih H.2⟩

lemma any_mono (ins : List ℕ) (f h : ℕ → Bool) (hfh : ∀ k, f k = true → h k = true) :
    (ins.map f).any id = true → (ins.map h).any id = true := by
  induction ins with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id_eq, Bool.or_eq_true]
    rintro (H | H)
    · exact Or.inl (hfh a H)
    · exact Or.inr (ih H)

lemma sandwich (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    {n : ℕ} (x z y : Fin n → Bool)
    (hxz : ∀ p, x p = true → z p = true) (hzy : ∀ p, z p = true → y p = true)
    (hnot : ∀ t : Fin gates.length, (gates.get t).op = GateOp.not → nin gates t x = nin gates t y) :
    ∀ m, m ≤ gates.length → ∀ k,
      ((Circuit.wires ⟨gates.take m, 0⟩ (List.ofFn x)).getD k false = true →
        (Circuit.wires ⟨gates.take m, 0⟩ (List.ofFn z)).getD k false = true) ∧
      ((Circuit.wires ⟨gates.take m, 0⟩ (List.ofFn z)).getD k false = true →
        (Circuit.wires ⟨gates.take m, 0⟩ (List.ofFn y)).getD k false = true) := by
  intro m
  induction m with
  | zero =>
    intro _ k
    have e : ∀ v : Fin n → Bool, Circuit.wires ⟨gates.take 0, 0⟩ (List.ofFn v) = List.ofFn v := by
      intro v; simp [Circuit.wires]
    rw [e, e, e]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases hk : k < n
    · simp only [hk, dite_true, Option.getD_some]
      exact ⟨hxz _, hzy _⟩
    · simp [hk]
  | succ m ih =>
    intro hm k
    have hm' : m < gates.length := by omega
    have ih' := ih (by omega)
    set Lx := Circuit.wires ⟨gates.take m, 0⟩ (List.ofFn x) with hLx
    set Lz := Circuit.wires ⟨gates.take m, 0⟩ (List.ofFn z) with hLz
    set Ly := Circuit.wires ⟨gates.take m, 0⟩ (List.ofFn y) with hLy
    have lx : Lx.length = n + m := by
      rw [hLx, wires_length]; simp; omega
    have lz : Lz.length = n + m := by
      rw [hLz, wires_length]; simp; omega
    have ly : Ly.length = n + m := by
      rw [hLy, wires_length]; simp; omega
    rw [take_succ_eq gates m hm', wires_snoc, wires_snoc, wires_snoc, ← hLx, ← hLz, ← hLy,
      getD_snoc, getD_snoc, getD_snoc, lx, lz, ly]
    by_cases hk : k < n + m
    · simp only [hk, if_true]
      exact ih' k
    · by_cases hk2 : k = n + m
      · subst hk2
        simp only [lt_self_iff_false, if_false, if_true]
        have hg := hops (gates[m]) (List.getElem_mem hm')
        rcases hg with hop | hop | hop
        · rw [hop]
          exact ⟨all_mono _ _ _ (fun i => (ih' i).1), all_mono _ _ _ (fun i => (ih' i).2)⟩
        · rw [hop]
          exact ⟨any_mono _ _ _ (fun i => (ih' i).1), any_mono _ _ _ (fun i => (ih' i).2)⟩
        · have hn := hnot ⟨m, hm'⟩ (by simpa using hop)
          simp only [nin, List.get_eq_getElem] at hn
          rw [← hLx, ← hLy] at hn
          rw [hop]
          simp only [GateOp.eval]
          cases hins : (gates[m]).inputs with
          | nil => simp
          | cons a l =>
            rw [hins] at hn
            simp only [List.map_cons, List.headD_cons] at hn ⊢
            have h1 := (ih' a).1
            have h2 := (ih' a).2
            cases ha : Lx.getD a false <;> cases hb : Lz.getD a false <;> cases hc : Ly.getD a false <;>
              simp_all
      · simp [hk, hk2]

lemma nin_eq (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    {n : ℕ} (x z y : Fin n → Bool)
    (hxz : ∀ p, x p = true → z p = true) (hzy : ∀ p, z p = true → y p = true)
    (hnot : ∀ t : Fin gates.length, (gates.get t).op = GateOp.not → nin gates t x = nin gates t y)
    (t : Fin gates.length) (ht : (gates.get t).op = GateOp.not) : nin gates t z = nin gates t x := by
  have hs := sandwich gates hops x z y hxz hzy hnot t.val (le_of_lt t.isLt)
  have hn := hnot t ht
  simp only [nin] at hn ⊢
  cases hins : (gates.get t).inputs with
  | nil => simp
  | cons a l =>
    rw [hins] at hn
    simp only [List.map_cons, List.headD_cons] at hn ⊢
    have h1 := (hs a).1
    have h2 := (hs a).2
    revert h1 h2 hn
    cases (Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn x)).getD a false <;>
      cases (Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn z)).getD a false <;>
      cases (Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn y)).getD a false <;> simp

lemma chain {n : ℕ} (r : ℕ) (x : ℕ → Fin n → Bool)
    (hc : ∀ i : ℕ, i < r → ∀ p : Fin n, x i p = true → x (i + 1) p = true) :
    ∀ i j, i ≤ j → j ≤ r → ∀ p, x i p = true → x j p = true := by
  intro i j hij hjr
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact fun p h => h
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h; exact fun p h => h
    · intro p hp
      exact hc j (by omega) p (ih (by omega) (by omega) p hp)

end PEqualNP.Outside.L_meta_1323

theorem PEqualNP.Outside.L_meta_1323 : ∀ (n s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → ∀ (r : ℕ) (x : ℕ → Fin n → Bool), (∀ i : ℕ, i < r → ∀ p : Fin n, x i p = true → x (i + 1) p = true) → (∀ i : ℕ, i < r → ∃ t : Fin gates.length, (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x i))).getD k false)).headD false ≠ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x (i + 1)))).getD k false)).headD false) → r + 1 ≤ 2 ^ s := by
  classical
  intro n s gates hG hι r x hchain hstep
  have hops : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not :=
    fun g hg => (hG g hg).1
  set NOTs := (Finset.univ : Finset (Fin gates.length)).filter
    (fun t => (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not) with hNOTs
  have hcard : NOTs.card ≤ s := by
    obtain ⟨ι, hιc⟩ := hι
    calc NOTs.card ≤ ((Finset.univ : Finset (Fin s)).image ι).card := by
          apply Finset.card_le_card
          intro t ht
          rw [hNOTs, Finset.mem_filter] at ht
          obtain ⟨j, hj⟩ := hιc t ht.2
          exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
      _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
      _ = s := by simp
  let A : ℕ → Finset (Fin gates.length) := fun i =>
    NOTs.filter (fun t => PEqualNP.Outside.L_meta_1323.nin gates t (x i) = true)
  have key : ∀ i j, i < j → j ≤ r → A i ≠ A j := by
    intro i j hij hjr hA
    obtain ⟨t, ht, hne⟩ := hstep i (by omega)
    have hnot : ∀ u : Fin gates.length, (gates.get u).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        PEqualNP.Outside.L_meta_1323.nin gates u (x i) = PEqualNP.Outside.L_meta_1323.nin gates u (x j) := by
      intro u hu
      have h1 : u ∈ A i ↔ u ∈ A j := by rw [hA]
      simp only [A, Finset.mem_filter, hNOTs, Finset.mem_univ, true_and] at h1
      cases h3 : PEqualNP.Outside.L_meta_1323.nin gates u (x i) <;>
        cases h4 : PEqualNP.Outside.L_meta_1323.nin gates u (x j) <;> simp_all
    have he := PEqualNP.Outside.L_meta_1323.nin_eq gates hops (x i) (x (i + 1)) (x j)
      (PEqualNP.Outside.L_meta_1323.chain r x hchain i (i + 1) (by omega) (by omega))
      (PEqualNP.Outside.L_meta_1323.chain r x hchain (i + 1) j (by omega) hjr) hnot t ht
    exact hne (by simpa [PEqualNP.Outside.L_meta_1323.nin] using he.symm)
  have hinj : Set.InjOn A (Finset.range (r + 1) : Set ℕ) := by
    intro i hi j hj hA
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hA (key i j h (by omega))
    · exact h
    · exact absurd hA.symm (key j i h (by omega))
  have hle := Finset.card_le_card_of_injOn A
    (by intro i _; exact Finset.mem_powerset.2 (Finset.filter_subset _ _)) hinj
  rw [Finset.card_range, Finset.card_powerset] at hle
  calc r + 1 ≤ 2 ^ NOTs.card := hle
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hcard
