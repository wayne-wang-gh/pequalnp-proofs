import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1044_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

theorem foldl_stepW_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_take_getD (gs : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((gs.take t).foldl stepW w).length) :
    (gs.foldl stepW w).getD i false = ((gs.take t).foldl stepW w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t gs, List.foldl_append]
  exact foldl_stepW_getD _ _ _ hi

theorem gate_val (C : Circuit) (x : Fin 18 → Bool) (t : ℕ) (ht : t < C.gates.length) :
    (C.wires (List.ofFn x)).getD (18 + t) false =
      (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
        if i < 18 + t then (C.wires (List.ofFn x)).getD i false else false) := by
  have hsplit : C.gates = C.gates.take t ++ C.gates[t] :: C.gates.drop (t + 1) := by
    simp [List.take_append_drop]
  have hlen : ((C.gates.take t).foldl stepW (List.ofFn x)).length = 18 + t := by
    rw [foldl_stepW_length, List.length_ofFn, List.length_take, Nat.min_eq_left ht.le]
  have hlhs : (C.wires (List.ofFn x)).getD (18 + t) false =
      (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
        ((C.gates.take t).foldl stepW (List.ofFn x)).getD i false) := by
    change (C.gates.foldl stepW (List.ofFn x)).getD (18 + t) false = _
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [foldl_stepW_getD _ _ _ (by simp only [stepW, List.length_append, List.length_singleton, hlen]; omega)]
    simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ((C.gates.take t).foldl stepW (List.ofFn x)).length ≤ 18 + t), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hlhs]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hi
  · exact (foldl_take_getD C.gates (List.ofFn x) t i (by omega)).symm
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem input_val (C : Circuit) (x : Fin 18 → Bool) (i : Fin 18) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (C.gates.foldl stepW (List.ofFn x)).getD i.val false = x i
  rw [foldl_stepW_getD _ _ _ (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

def netAdj6 (a b : ℕ) : Bool :=
  (a == 0 && b == 1) || (a == 1 && b == 0) ||
  (a == 1 && b == 2) || (a == 2 && b == 1) ||
  (a == 0 && b == 2) || (a == 2 && b == 0) ||
  (a == 0 && b == 3) || (a == 3 && b == 0) ||
  (a == 1 && b == 4) || (a == 4 && b == 1) ||
  (a == 2 && b == 5) || (a == 5 && b == 2)

def adj18 (u v : Fin 18) : Bool :=
  (u.val / 6 == v.val / 6) && netAdj6 (u.val % 6) (v.val % 6)

def G : SimpleGraph (Fin 18) where
  Adj u v := adj18 u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

theorem netAdj6_c4free : ∀ a b c e : Fin 6,
    netAdj6 a.val b.val = true → netAdj6 b.val c.val = true →
    netAdj6 c.val e.val = true → netAdj6 e.val a.val = true →
    a = c ∨ b = e := by
  decide

theorem G_c4free : ∀ a b c e : Fin 18,
    G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e := by
  intro a b c e hab hbc hce hea
  simp only [G, adj18, Bool.and_eq_true, beq_iff_eq] at hab hbc hce hea
  have h6 := netAdj6_c4free ⟨a.val % 6, Nat.mod_lt _ (by omega)⟩
    ⟨b.val % 6, Nat.mod_lt _ (by omega)⟩
    ⟨c.val % 6, Nat.mod_lt _ (by omega)⟩
    ⟨e.val % 6, Nat.mod_lt _ (by omega)⟩ hab.2 hbc.2 hce.2 hea.2
  rcases h6 with h | h
  · left; apply Fin.ext; simp only [Fin.mk.injEq] at h; omega
  · right; apply Fin.ext; simp only [Fin.mk.injEq] at h; omega

def pairIdx (i : Fin 18) : Fin 9 :=
  ⟨3 * (i.val / 6) + (i.val % 3), by omega⟩

theorem pair_edge (p : Fin 9) :
    ∃ u v : Fin 18, adj18 u v = true ∧ pairIdx u = p ∧ pairIdx v = p := by
  revert p; decide

theorem G_vc : ∀ T : Finset (Fin 18), (∀ i j : Fin 18, G.Adj i j → i ∈ T ∨ j ∈ T) → 9 ≤ T.card := by
  intro T hT
  have hsub : (Finset.univ : Finset (Fin 9)) ⊆ T.image pairIdx := by
    intro p _
    obtain ⟨u, v, huv, hu, hv⟩ := pair_edge p
    rcases hT u v huv with huT | hvT
    · exact Finset.mem_image.mpr ⟨u, huT, hu⟩
    · exact Finset.mem_image.mpr ⟨v, hvT, hv⟩
  have h1 : 9 ≤ (T.image pairIdx).card := by
    have := Finset.card_le_card hsub
    simpa using this
  exact h1.trans Finset.card_image_le

def edgeFin : Finset (Sym2 (Fin 18)) :=
  {s(0, 1), s(1, 2), s(0, 2), s(0, 3), s(1, 4), s(2, 5),
    s(6, 7), s(7, 8), s(6, 8), s(6, 9), s(7, 10), s(8, 11),
    s(12, 13), s(13, 14), s(12, 14), s(12, 15), s(13, 16), s(14, 17)}

theorem G_edgeSet_eq : G.edgeSet = (edgeFin : Set (Sym2 (Fin 18))) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    change adj18 u v = true ↔ s(u, v) ∈ edgeFin
    revert u v
    decide

theorem G_edges_card : G.edgeSet.ncard = 18 := by
  rw [G_edgeSet_eq, Set.ncard_coe_finset]
  decide

def C : Circuit where
  gates := [
    ⟨.and, [8, 11]⟩,
    ⟨.or,  [6, 7]⟩,
    ⟨.or,  [19, 18]⟩,
    ⟨.or,  [6, 8]⟩,
    ⟨.or,  [21, 10]⟩,
    ⟨.or,  [7, 8]⟩,
    ⟨.or,  [23, 9]⟩,
    ⟨.and, [22, 24]⟩,
    ⟨.and, [20, 25]⟩,
    ⟨.and, [14, 17]⟩,
    ⟨.or,  [12, 13]⟩,
    ⟨.or,  [28, 27]⟩,
    ⟨.or,  [12, 14]⟩,
    ⟨.or,  [30, 16]⟩,
    ⟨.or,  [13, 14]⟩,
    ⟨.or,  [32, 15]⟩,
    ⟨.and, [31, 33]⟩,
    ⟨.and, [29, 34]⟩,
    ⟨.or,  [26, 35]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.or,  [0, 1]⟩,
    ⟨.or,  [38, 37]⟩,
    ⟨.or,  [0, 2]⟩,
    ⟨.or,  [40, 4]⟩,
    ⟨.or,  [1, 2]⟩,
    ⟨.or,  [42, 3]⟩,
    ⟨.or,  [39, 36]⟩,
    ⟨.or,  [41, 36]⟩,
    ⟨.or,  [43, 36]⟩,
    ⟨.and, [45, 46]⟩,
    ⟨.and, [44, 47]⟩
  ]
  output := 48

theorem C_mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

def V (x : Fin 18 → Bool) (w : ℕ) : Bool := (C.wires (List.ofFn x)).getD w false

theorem V_in (x : Fin 18 → Bool) (i : Fin 18) : V x i.val = x i := input_val C x i

theorem V_and (x : Fin 18 → Bool) (t a b : ℕ) (ht : t < C.gates.length)
    (hg : C.gates[t] = ⟨.and, [a, b]⟩) (ha : a < 18 + t) (hb : b < 18 + t) :
    V x (18 + t) = (V x a && V x b) := by
  unfold V
  rw [gate_val C x t ht, hg]
  simp [GateOp.eval, ha, hb]

theorem V_or (x : Fin 18 → Bool) (t a b : ℕ) (ht : t < C.gates.length)
    (hg : C.gates[t] = ⟨.or, [a, b]⟩) (ha : a < 18 + t) (hb : b < 18 + t) :
    V x (18 + t) = (V x a || V x b) := by
  unfold V
  rw [gate_val C x t ht, hg]
  simp [GateOp.eval, ha, hb]

theorem v18 (x) : V x 18 = (x 8 && x 11) := by rw [V_and x 0 8 11 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· && ·) (V_in x 8) (V_in x 11)
theorem v19 (x) : V x 19 = (x 6 || x 7) := by rw [V_or x 1 6 7 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) (V_in x 6) (V_in x 7)
theorem v20 (x) : V x 20 = (V x 19 || V x 18) := V_or x 2 19 18 (by decide) rfl (by omega) (by omega)
theorem v21 (x) : V x 21 = (x 6 || x 8) := by rw [V_or x 3 6 8 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) (V_in x 6) (V_in x 8)
theorem v22 (x) : V x 22 = (V x 21 || x 10) := by rw [V_or x 4 21 10 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) rfl (V_in x 10)
theorem v23 (x) : V x 23 = (x 7 || x 8) := by rw [V_or x 5 7 8 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) (V_in x 7) (V_in x 8)
theorem v24 (x) : V x 24 = (V x 23 || x 9) := by rw [V_or x 6 23 9 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) rfl (V_in x 9)
theorem v25 (x) : V x 25 = (V x 22 && V x 24) := V_and x 7 22 24 (by decide) rfl (by omega) (by omega)
theorem v26 (x) : V x 26 = (V x 20 && V x 25) := V_and x 8 20 25 (by decide) rfl (by omega) (by omega)

theorem v27 (x) : V x 27 = (x 14 && x 17) := by rw [V_and x 9 14 17 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· && ·) (V_in x 14) (V_in x 17)
theorem v28 (x) : V x 28 = (x 12 || x 13) := by rw [V_or x 10 12 13 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) (V_in x 12) (V_in x 13)
theorem v29 (x) : V x 29 = (V x 28 || V x 27) := V_or x 11 28 27 (by decide) rfl (by omega) (by omega)
theorem v30 (x) : V x 30 = (x 12 || x 14) := by rw [V_or x 12 12 14 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) (V_in x 12) (V_in x 14)
theorem v31 (x) : V x 31 = (V x 30 || x 16) := by rw [V_or x 13 30 16 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) rfl (V_in x 16)
theorem v32 (x) : V x 32 = (x 13 || x 14) := by rw [V_or x 14 13 14 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) (V_in x 13) (V_in x 14)
theorem v33 (x) : V x 33 = (V x 32 || x 15) := by rw [V_or x 15 32 15 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) rfl (V_in x 15)
theorem v34 (x) : V x 34 = (V x 31 && V x 33) := V_and x 16 31 33 (by decide) rfl (by omega) (by omega)
theorem v35 (x) : V x 35 = (V x 29 && V x 34) := V_and x 17 29 34 (by decide) rfl (by omega) (by omega)

theorem v36 (x) : V x 36 = (V x 26 || V x 35) := V_or x 18 26 35 (by decide) rfl (by omega) (by omega)

theorem v37 (x) : V x 37 = (x 2 && x 5) := by rw [V_and x 19 2 5 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· && ·) (V_in x 2) (V_in x 5)
theorem v38 (x) : V x 38 = (x 0 || x 1) := by rw [V_or x 20 0 1 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) (V_in x 0) (V_in x 1)
theorem v39 (x) : V x 39 = (V x 38 || V x 37) := V_or x 21 38 37 (by decide) rfl (by omega) (by omega)
theorem v40 (x) : V x 40 = (x 0 || x 2) := by rw [V_or x 22 0 2 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) (V_in x 0) (V_in x 2)
theorem v41 (x) : V x 41 = (V x 40 || x 4) := by rw [V_or x 23 40 4 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) rfl (V_in x 4)
theorem v42 (x) : V x 42 = (x 1 || x 2) := by rw [V_or x 24 1 2 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) (V_in x 1) (V_in x 2)
theorem v43 (x) : V x 43 = (V x 42 || x 3) := by rw [V_or x 25 42 3 (by decide) rfl (by omega) (by omega)]; exact congrArg₂ (· || ·) rfl (V_in x 3)
theorem v44 (x) : V x 44 = (V x 39 || V x 36) := V_or x 26 39 36 (by decide) rfl (by omega) (by omega)
theorem v45 (x) : V x 45 = (V x 41 || V x 36) := V_or x 27 41 36 (by decide) rfl (by omega) (by omega)
theorem v46 (x) : V x 46 = (V x 43 || V x 36) := V_or x 28 43 36 (by decide) rfl (by omega) (by omega)
theorem v47 (x) : V x 47 = (V x 45 && V x 46) := V_and x 29 45 46 (by decide) rfl (by omega) (by omega)
theorem v48 (x) : V x 48 = (V x 44 && V x 47) := V_and x 30 44 47 (by decide) rfl (by omega) (by omega)

def netF (x0 x1 x2 x3 x4 x5 : Bool) : Bool :=
  ((x0 || x1) || (x2 && x5)) && (((x0 || x2) || x4) && ((x1 || x2) || x3))

def netE (x0 x1 x2 x3 x4 x5 : Bool) : Bool :=
  (x0 && x1) || (x1 && x2) || (x0 && x2) || (x0 && x3) || (x1 && x4) || (x2 && x5)

theorem netF_eq_netE : ∀ a b c d e f : Bool, netF a b c d e f = netE a b c d e f := by
  decide

theorem dist3 : ∀ a b c X : Bool,
    ((a || X) && ((b || X) && (c || X))) = ((a && (b && c)) || X) := by
  decide

theorem v26_eq (x) : V x 26 = netE (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) := by
  rw [v26, v20, v19, v18, v25, v22, v21, v24, v23]
  exact netF_eq_netE _ _ _ _ _ _

theorem v35_eq (x) : V x 35 = netE (x 12) (x 13) (x 14) (x 15) (x 16) (x 17) := by
  rw [v35, v29, v28, v27, v34, v31, v30, v33, v32]
  exact netF_eq_netE _ _ _ _ _ _

theorem C_eval_formula (x : Fin 18 → Bool) :
    C.eval (List.ofFn x) =
      (netE (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) ||
       (netE (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) ||
        netE (x 12) (x 13) (x 14) (x 15) (x 16) (x 17))) := by
  change V x 48 = _
  rw [v48, v47, v44, v45, v46, dist3, v39, v38, v37, v41, v40, v43, v42, v36, v26_eq, v35_eq]
  exact congrArg₂ (· || ·) (netF_eq_netE _ _ _ _ _ _) rfl

theorem C_eval_spec (x : Fin 18 → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 18, G.Adj u v ∧ x u = true ∧ x v = true := by
  rw [C_eval_formula]
  constructor
  · intro h
    simp only [netE, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) |
      ((((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) |
       (((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩))
    · exact ⟨0, 1, by change adj18 0 1 = true; decide, h1, h2⟩
    · exact ⟨1, 2, by change adj18 1 2 = true; decide, h1, h2⟩
    · exact ⟨0, 2, by change adj18 0 2 = true; decide, h1, h2⟩
    · exact ⟨0, 3, by change adj18 0 3 = true; decide, h1, h2⟩
    · exact ⟨1, 4, by change adj18 1 4 = true; decide, h1, h2⟩
    · exact ⟨2, 5, by change adj18 2 5 = true; decide, h1, h2⟩
    · exact ⟨6, 7, by change adj18 6 7 = true; decide, h1, h2⟩
    · exact ⟨7, 8, by change adj18 7 8 = true; decide, h1, h2⟩
    · exact ⟨6, 8, by change adj18 6 8 = true; decide, h1, h2⟩
    · exact ⟨6, 9, by change adj18 6 9 = true; decide, h1, h2⟩
    · exact ⟨7, 10, by change adj18 7 10 = true; decide, h1, h2⟩
    · exact ⟨8, 11, by change adj18 8 11 = true; decide, h1, h2⟩
    · exact ⟨12, 13, by change adj18 12 13 = true; decide, h1, h2⟩
    · exact ⟨13, 14, by change adj18 13 14 = true; decide, h1, h2⟩
    · exact ⟨12, 14, by change adj18 12 14 = true; decide, h1, h2⟩
    · exact ⟨12, 15, by change adj18 12 15 = true; decide, h1, h2⟩
    · exact ⟨13, 16, by change adj18 13 16 = true; decide, h1, h2⟩
    · exact ⟨14, 17, by change adj18 14 17 = true; decide, h1, h2⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    change adj18 u v = true at huv
    fin_cases u <;> fin_cases v
    all_goals first
      | (exfalso; revert huv; decide)
      | (simp only [netE, Bool.or_eq_true, Bool.and_eq_true]; simp_all)

def A : Finset ℕ := {0, 7, 8, 9, 16, 17, 19, 29, 30}
def B : Finset ℕ := {1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 14, 15, 20, 21, 22, 23, 24, 25, 26, 27, 28}
def D : Finset ℕ := {18}
def Fz : Finset ℕ := {29}

def des (j : ℕ) : ℕ :=
  if j = 0 then 8
  else if j = 8 then 25
  else if j = 9 then 14
  else if j = 17 then 34
  else if j = 19 then 2
  else if j = 30 then 47
  else 0

def e1 (u : Fin 18) : Fin 18 → Bool := fun i => decide (i = u)

def wide (w : ℕ) : Prop :=
  ∃ u v : Fin 18, u ≠ v ∧ V (e1 u) w = true ∧ V (e1 v) w = true

theorem e1_v26 (u : Fin 18) : V (e1 u) 26 = false := by
  rw [v26_eq]; revert u; decide

theorem e1_v35 (u : Fin 18) : V (e1 u) 35 = false := by
  rw [v35_eq]; revert u; decide

theorem e1_v36 (u : Fin 18) : V (e1 u) 36 = false := by
  rw [v36, e1_v26, e1_v35]; rfl

theorem thin_in (a : Fin 18) : ¬ wide a.val := by
  rintro ⟨u, v, huv, hu, hv⟩
  rw [V_in] at hu hv
  simp only [e1, decide_eq_true_eq] at hu hv
  exact huv (hu.symm.trans hv)

theorem thin_25 : ¬ wide 25 := by
  rintro ⟨u, v, huv, hu, hv⟩
  rw [v25, v22, v21, v24, v23] at hu hv
  have hu' : u = 8 := by clear huv hv; revert u hu; decide
  have hv' : v = 8 := by clear huv hu hu'; revert v hv; decide
  exact huv (hu'.trans hv'.symm)

theorem thin_34 : ¬ wide 34 := by
  rintro ⟨u, v, huv, hu, hv⟩
  rw [v34, v31, v30, v33, v32] at hu hv
  have hu' : u = 14 := by clear huv hv; revert u hu; decide
  have hv' : v = 14 := by clear huv hu hu'; revert v hv; decide
  exact huv (hu'.trans hv'.symm)

theorem thin_36 : ¬ wide 36 := by
  rintro ⟨u, _, _, hu, _⟩
  rw [e1_v36] at hu; cases hu

theorem thin_47 : ¬ wide 47 := by
  rintro ⟨u, v, huv, hu, hv⟩
  rw [v47, v45, v46, e1_v36, v41, v40, v43, v42] at hu hv
  have hu' : u = 2 := by clear huv hv; revert u hu; decide
  have hv' : v = 2 := by clear huv hu hu'; revert v hv; decide
  exact huv (hu'.trans hv'.symm)

theorem wide_19 : wide 19 := ⟨6, 7, by decide, by rw [v19]; decide, by rw [v19]; decide⟩
theorem wide_20 : wide 20 := ⟨6, 7, by decide, by rw [v20, v19, v18]; decide, by rw [v20, v19, v18]; decide⟩
theorem wide_21 : wide 21 := ⟨6, 8, by decide, by rw [v21]; decide, by rw [v21]; decide⟩
theorem wide_22 : wide 22 := ⟨6, 8, by decide, by rw [v22, v21]; decide, by rw [v22, v21]; decide⟩
theorem wide_23 : wide 23 := ⟨7, 8, by decide, by rw [v23]; decide, by rw [v23]; decide⟩
theorem wide_24 : wide 24 := ⟨7, 8, by decide, by rw [v24, v23]; decide, by rw [v24, v23]; decide⟩
theorem wide_28 : wide 28 := ⟨12, 13, by decide, by rw [v28]; decide, by rw [v28]; decide⟩
theorem wide_29 : wide 29 := ⟨12, 13, by decide, by rw [v29, v28, v27]; decide, by rw [v29, v28, v27]; decide⟩
theorem wide_30 : wide 30 := ⟨12, 14, by decide, by rw [v30]; decide, by rw [v30]; decide⟩
theorem wide_31 : wide 31 := ⟨12, 14, by decide, by rw [v31, v30]; decide, by rw [v31, v30]; decide⟩
theorem wide_32 : wide 32 := ⟨13, 14, by decide, by rw [v32]; decide, by rw [v32]; decide⟩
theorem wide_33 : wide 33 := ⟨13, 14, by decide, by rw [v33, v32]; decide, by rw [v33, v32]; decide⟩
theorem wide_38 : wide 38 := ⟨0, 1, by decide, by rw [v38]; decide, by rw [v38]; decide⟩
theorem wide_39 : wide 39 := ⟨0, 1, by decide, by rw [v39, v38, v37]; decide, by rw [v39, v38, v37]; decide⟩
theorem wide_40 : wide 40 := ⟨0, 2, by decide, by rw [v40]; decide, by rw [v40]; decide⟩
theorem wide_41 : wide 41 := ⟨0, 2, by decide, by rw [v41, v40]; decide, by rw [v41, v40]; decide⟩
theorem wide_42 : wide 42 := ⟨1, 2, by decide, by rw [v42]; decide, by rw [v42]; decide⟩
theorem wide_43 : wide 43 := ⟨1, 2, by decide, by rw [v43, v42]; decide, by rw [v43, v42]; decide⟩
theorem wide_44 : wide 44 := ⟨0, 1, by decide, by rw [v44, v39, v38, v37, e1_v36]; decide, by rw [v44, v39, v38, v37, e1_v36]; decide⟩
theorem wide_45 : wide 45 := ⟨0, 2, by decide, by rw [v45, v41, v40, e1_v36]; decide, by rw [v45, v41, v40, e1_v36]; decide⟩
theorem wide_46 : wide 46 := ⟨1, 2, by decide, by rw [v46, v43, v42, e1_v36]; decide, by rw [v46, v43, v42, e1_v36]; decide⟩

theorem hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → j ∈ A := by
  intro j g hg hop
  have hj : j < 31 := (List.getElem?_eq_some_iff.mp hg).1
  interval_cases j <;> simp [C] at hg <;> subst hg <;> cases hop <;> decide

theorem hB : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → wide (18 + j) → j ∈ B := by
  intro j g hg hop hw
  have hj : j < 31 := (List.getElem?_eq_some_iff.mp hg).1
  interval_cases j <;> simp [C] at hg <;> subst hg <;> cases hop <;> first | decide | exact False.elim (thin_36 hw)

theorem hD : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → ¬ wide (18 + j) → j ∈ D := by
  intro j g hg hop hnw
  have hj : j < 31 := (List.getElem?_eq_some_iff.mp hg).1
  interval_cases j <;> simp [C] at hg <;> subst hg <;> cases hop
  · exact False.elim (hnw wide_19)
  · exact False.elim (hnw wide_20)
  · exact False.elim (hnw wide_21)
  · exact False.elim (hnw wide_22)
  · exact False.elim (hnw wide_23)
  · exact False.elim (hnw wide_24)
  · exact False.elim (hnw wide_28)
  · exact False.elim (hnw wide_29)
  · exact False.elim (hnw wide_30)
  · exact False.elim (hnw wide_31)
  · exact False.elim (hnw wide_32)
  · exact False.elim (hnw wide_33)
  · decide
  · exact False.elim (hnw wide_38)
  · exact False.elim (hnw wide_39)
  · exact False.elim (hnw wide_40)
  · exact False.elim (hnw wide_41)
  · exact False.elim (hnw wide_42)
  · exact False.elim (hnw wide_43)
  · exact False.elim (hnw wide_44)
  · exact False.elim (hnw wide_45)
  · exact False.elim (hnw wide_46)

theorem hDes : ∀ (j1 : ℕ) (g1 : Gate), C.gates[j1]? = some g1 → g1.op = GateOp.and →
    ¬ (∀ w1 ∈ g1.inputs, wide w1) → des j1 ∈ g1.inputs ∧ ¬ wide (des j1) := by
  intro j1 g1 hg hop hnf
  have hj : j1 < 31 := (List.getElem?_eq_some_iff.mp hg).1
  interval_cases j1 <;> simp [C] at hg <;> subst hg <;> cases hop
  · exact ⟨by decide, thin_in 8⟩
  · exfalso; apply hnf; intro w hw; simp at hw; rcases hw with rfl | rfl; exact wide_22; exact wide_24
  · exact ⟨by decide, thin_25⟩
  · exact ⟨by decide, thin_in 14⟩
  · exfalso; apply hnf; intro w hw; simp at hw; rcases hw with rfl | rfl; exact wide_31; exact wide_33
  · exact ⟨by decide, thin_34⟩
  · exact ⟨by decide, thin_in 2⟩
  · exfalso; apply hnf; intro w hw; simp at hw; rcases hw with rfl | rfl; exact wide_45; exact wide_46
  · exact ⟨by decide, thin_47⟩

def Step (r3 t3 : ℕ) : Prop :=
  ∃ (j3 : ℕ) (g3 : Gate), r3 = 18 + j3 ∧ C.gates[j3]? = some g3 ∧
    ((g3.op = GateOp.or ∧ ¬ wide r3 ∧ t3 ∈ g3.inputs) ∨
     (g3.op = GateOp.and ∧ ¬ (∀ w5 ∈ g3.inputs, wide w5) ∧ t3 = des j3))

theorem step_48 : ∀ t, Step 48 t → t = 47 := by
  rintro t ⟨j3, g3, hr, hg, h⟩
  have hj : j3 = 30 := by omega
  subst hj
  simp [C] at hg
  subst hg
  rcases h with ⟨hop, _, _⟩ | ⟨_, _, rfl⟩
  · cases hop
  · rfl

theorem step_47 : ∀ t, ¬ Step 47 t := by
  rintro t ⟨j3, g3, hr, hg, h⟩
  have hj : j3 = 29 := by omega
  subst hj
  simp [C] at hg
  subst hg
  rcases h with ⟨hop, _, _⟩ | ⟨_, hnf, _⟩
  · cases hop
  · apply hnf; intro w hw; simp at hw; rcases hw with rfl | rfl; exact wide_45; exact wide_46

theorem reach_from_48 : ∀ w, Relation.ReflTransGen Step 48 w → w = 48 ∨ w = 47 := by
  intro w hw
  induction hw with
  | refl => left; rfl
  | tail _ hstep ih =>
    rcases ih with rfl | rfl
    · right; exact step_48 _ hstep
    · exact False.elim (step_47 _ hstep)

theorem hFz : ∀ (j6 : ℕ) (g6 : Gate), C.gates[j6]? = some g6 → g6.op = GateOp.and →
    (∀ w7 ∈ g6.inputs, wide w7) → Relation.ReflTransGen Step C.output (18 + j6) →
    (∀ c8 : Fin 18, ∃ u8 v8 : Fin 18, G.Adj u8 v8 ∧
      (C.wires (List.ofFn (fun i8 : Fin 18 => decide (i8 = u8 ∨ i8 = v8)))).getD (18 + j6) false = true ∧
      c8 ≠ u8 ∧ c8 ≠ v8) → j6 ∈ Fz := by
  intro j6 g6 hg hop hfat hreach _
  have hr := reach_from_48 (18 + j6) hreach
  rcases hr with h48 | h47
  · have hj : j6 = 30 := by omega
    subst hj
    simp [C] at hg
    subst hg
    exact False.elim (thin_47 (hfat 47 (by simp)))
  · have hj : j6 = 29 := by omega
    subst hj
    decide

theorem main : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D Fz : Finset ℕ) (des : ℕ → ℕ), (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ D) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C.gates[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ (∀ w1 ∈ g1.inputs, (∃ a1 b1 : Fin n, a1 ≠ b1 ∧ (C.wires (List.ofFn (fun i1 : Fin n => decide (i1 = a1)))).getD w1 false = true ∧ (C.wires (List.ofFn (fun k1 : Fin n => decide (k1 = b1)))).getD w1 false = true)) → des j1 ∈ g1.inputs ∧ ¬ (∃ a2 b2 : Fin n, a2 ≠ b2 ∧ (C.wires (List.ofFn (fun i2 : Fin n => decide (i2 = a2)))).getD (des j1) false = true ∧ (C.wires (List.ofFn (fun k2 : Fin n => decide (k2 = b2)))).getD (des j1) false = true)) → (∀ (j6 : ℕ) (g6 : PEqualNP.CircuitLowerBounds.Gate), C.gates[j6]? = some g6 → g6.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ w7 ∈ g6.inputs, (∃ a7 b7 : Fin n, a7 ≠ b7 ∧ (C.wires (List.ofFn (fun i7 : Fin n => decide (i7 = a7)))).getD w7 false = true ∧ (C.wires (List.ofFn (fun k7 : Fin n => decide (k7 = b7)))).getD w7 false = true)) → Relation.ReflTransGen (fun r3 t3 : ℕ => ∃ (j3 : ℕ) (g3 : PEqualNP.CircuitLowerBounds.Gate), r3 = n + j3 ∧ C.gates[j3]? = some g3 ∧ ((g3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ¬ (∃ a4 b4 : Fin n, a4 ≠ b4 ∧ (C.wires (List.ofFn (fun i4 : Fin n => decide (i4 = a4)))).getD r3 false = true ∧ (C.wires (List.ofFn (fun k4 : Fin n => decide (k4 = b4)))).getD r3 false = true) ∧ t3 ∈ g3.inputs) ∨ (g3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ (∀ w5 ∈ g3.inputs, (∃ a5 b5 : Fin n, a5 ≠ b5 ∧ (C.wires (List.ofFn (fun i5 : Fin n => decide (i5 = a5)))).getD w5 false = true ∧ (C.wires (List.ofFn (fun k5 : Fin n => decide (k5 = b5)))).getD w5 false = true)) ∧ t3 = des j3))) C.output (n + j6) → (∀ c8 : Fin n, ∃ u8 v8 : Fin n, G.Adj u8 v8 ∧ (C.wires (List.ofFn (fun i8 : Fin n => decide (i8 = u8 ∨ i8 = v8)))).getD (n + j6) false = true ∧ c8 ≠ u8 ∧ c8 ≠ v8) → j6 ∈ Fz) → G.edgeSet.ncard + 2 * k ≤ A.card + B.card + 2 * D.card + Fz.card + 2) := by
  intro h
  have hle := h 18 9 G C A B D Fz des G_c4free G_vc C_mono C_eval_spec hA hB hD hDes hFz
  rw [G_edges_card] at hle
  have hAcard : A.card = 9 := by decide
  have hBcard : B.card = 21 := by decide
  have hDcard : D.card = 1 := by decide
  have hFzcard : Fz.card = 1 := by decide
  rw [hAcard, hBcard, hDcard, hFzcard] at hle
  omega

end PEqualNP.Outside.L_meta_1044_aux

theorem PEqualNP.Outside.L_meta_1044 : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D Fz : Finset ℕ) (des : ℕ → ℕ), (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ D) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C.gates[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ (∀ w1 ∈ g1.inputs, (∃ a1 b1 : Fin n, a1 ≠ b1 ∧ (C.wires (List.ofFn (fun i1 : Fin n => decide (i1 = a1)))).getD w1 false = true ∧ (C.wires (List.ofFn (fun k1 : Fin n => decide (k1 = b1)))).getD w1 false = true)) → des j1 ∈ g1.inputs ∧ ¬ (∃ a2 b2 : Fin n, a2 ≠ b2 ∧ (C.wires (List.ofFn (fun i2 : Fin n => decide (i2 = a2)))).getD (des j1) false = true ∧ (C.wires (List.ofFn (fun k2 : Fin n => decide (k2 = b2)))).getD (des j1) false = true)) → (∀ (j6 : ℕ) (g6 : PEqualNP.CircuitLowerBounds.Gate), C.gates[j6]? = some g6 → g6.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ w7 ∈ g6.inputs, (∃ a7 b7 : Fin n, a7 ≠ b7 ∧ (C.wires (List.ofFn (fun i7 : Fin n => decide (i7 = a7)))).getD w7 false = true ∧ (C.wires (List.ofFn (fun k7 : Fin n => decide (k7 = b7)))).getD w7 false = true)) → Relation.ReflTransGen (fun r3 t3 : ℕ => ∃ (j3 : ℕ) (g3 : PEqualNP.CircuitLowerBounds.Gate), r3 = n + j3 ∧ C.gates[j3]? = some g3 ∧ ((g3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ¬ (∃ a4 b4 : Fin n, a4 ≠ b4 ∧ (C.wires (List.ofFn (fun i4 : Fin n => decide (i4 = a4)))).getD r3 false = true ∧ (C.wires (List.ofFn (fun k4 : Fin n => decide (k4 = b4)))).getD r3 false = true) ∧ t3 ∈ g3.inputs) ∨ (g3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ (∀ w5 ∈ g3.inputs, (∃ a5 b5 : Fin n, a5 ≠ b5 ∧ (C.wires (List.ofFn (fun i5 : Fin n => decide (i5 = a5)))).getD w5 false = true ∧ (C.wires (List.ofFn (fun k5 : Fin n => decide (k5 = b5)))).getD w5 false = true)) ∧ t3 = des j3))) C.output (n + j6) → (∀ c8 : Fin n, ∃ u8 v8 : Fin n, G.Adj u8 v8 ∧ (C.wires (List.ofFn (fun i8 : Fin n => decide (i8 = u8 ∨ i8 = v8)))).getD (n + j6) false = true ∧ c8 ≠ u8 ∧ c8 ≠ v8) → j6 ∈ Fz) → G.edgeSet.ncard + 2 * k ≤ A.card + B.card + 2 * D.card + Fz.card + 2) :=
  PEqualNP.Outside.L_meta_1044_aux.main
