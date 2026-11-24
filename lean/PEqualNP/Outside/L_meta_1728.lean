import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1728

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem eval_mono_fn {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (o : ℕ)
    (h : Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  refine mono gates _ _ (by simp) hg ?_ o h
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · exact hxy _
  · exact id

theorem acc_mono {N : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (p l : Fin N) (B : Finset (Fin N))
    (h : PEqualNP.MetaComplexity.circuitFun (N + N) C
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) :
    PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun a => decide (a ∈ ({p} : Finset (Fin N))))
        (fun b => decide (b ∈ insert l B))) = true := by
  refine eval_mono_fn C.gates (fun g' hg' => (hg g' hg').1) _ _ (fun v => ?_) C.output h
  refine Fin.addCases (fun i => ?_) (fun i => ?_) v
  · rw [Fin.append_left]
    intro hv
    have hv' : Fin.castAdd N i = Fin.castAdd N p ∨ Fin.castAdd N i = Fin.natAdd N l := by
      simpa using hv
    rcases hv' with h1 | h1
    · have h2 := congrArg Fin.val h1
      simp only [Fin.coe_castAdd] at h2
      have h3 : i = p := Fin.ext h2
      simp [h3]
    · have h2 := congrArg Fin.val h1
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h2
      have := i.isLt
      omega
  · rw [Fin.append_right]
    intro hv
    have hv' : Fin.natAdd N i = Fin.castAdd N p ∨ Fin.natAdd N i = Fin.natAdd N l := by
      simpa using hv
    rcases hv' with h1 | h1
    · have h2 := congrArg Fin.val h1
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h2
      have := p.isLt
      omega
    · have h2 := congrArg Fin.val h1
      simp only [Fin.coe_natAdd] at h2
      have h3 : i = l := Fin.ext (by omega)
      simp [h3]

theorem inP {N : ℕ} (S : Finset (Fin N)) (p : Fin N) (hp : p ∈ S) :
    (fun u : Fin N => decide (u ∈ S) && decide (u = p)) =
      (fun a => decide (a ∈ ({p} : Finset (Fin N)))) := by
  funext u
  by_cases h : u = p
  · subst h
    simp [hp]
  · simp [h]

theorem inX {N : ℕ} (S X : Finset (Fin N)) (hX : X ⊆ S) :
    (fun u : Fin N => decide (u ∈ S) && decide (u ∈ X)) = (fun a => decide (a ∈ X)) := by
  funext u
  by_cases h : u ∈ X
  · simp [h, hX h]
  · simp [h]

theorem lnT {N : ℕ} (W B T : Finset (Fin N)) (hT : T ⊆ W) (hWB : Disjoint W B) :
    (fun t : Fin N => if t ∈ W then decide (t ∈ T) else decide (t ∈ B)) =
      (fun b => decide (b ∈ T ∪ B)) := by
  funext t
  by_cases h : t ∈ W
  · have h1 : t ∉ B := Finset.disjoint_left.mp hWB h
    simp [h, h1]
  · have h1 : t ∉ T := fun h' => h (hT h')
    simp [h, h1]

theorem lnL {N : ℕ} (W B : Finset (Fin N)) (l : Fin N) (hl : l ∈ W) (hWB : Disjoint W B) :
    (fun t : Fin N => if t ∈ W then decide (t = l) else decide (t ∈ B)) =
      (fun b => decide (b ∈ insert l B)) := by
  funext t
  by_cases h : t ∈ W
  · have h1 : t ∉ B := Finset.disjoint_left.mp hWB h
    simp [h, h1]
  · have h1 : t ≠ l := fun h' => h (h' ▸ hl)
    simp [h, h1]

theorem inc_ge {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (S W : Finset (Fin N)) (c : ℕ)
    (h : ∀ l ∈ W, c ≤ (S.filter (fun u => I u l)).card) :
    W.card * c ≤ ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card := by
  have h1 : ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card =
      ∑ l ∈ W, (S.filter (fun u => I u l)).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.card_filter]
  rw [h1]
  calc W.card * c = ∑ _l ∈ W, c := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum h

theorem arith (q N K0 t w s inc d j sz : ℕ) (hN : N = q ^ 2 + q + 1) (hq : 8 ≤ q)
    (hd : 4 * d ≤ q) (hj : 8 * j ≤ q) (hw : N ≤ w + (j + d * (q + 1))) (hs : s ≤ N)
    (hinc : w * (q + 1 - d) ≤ inc) (hsz : sz ≤ t)
    (h3 : K0 * inc ≤ 5 * q * sz + K0 * (s + w)) : N * K0 ≤ 20 * t := by
  obtain ⟨e, he⟩ : ∃ e, q = d + e := ⟨q - d, by omega⟩
  have he1 : q + 1 - d = e + 1 := by omega
  rw [he1] at hinc
  have a1 : 8 * q ^ 2 ≤ q ^ 3 := by nlinarith [Nat.mul_le_mul_right (q ^ 2) hq]
  have a2 : 8 * q ≤ q ^ 2 := by nlinarith [Nat.mul_le_mul_right q hq]
  have h1 : 4 * (d * (q + 1)) ≤ q * (q + 1) := by nlinarith [Nat.mul_le_mul_right (q + 1) hd]
  have h2 : 6 * q ^ 2 + 5 * q + 8 ≤ 8 * w := by nlinarith
  have h4 : 3 * q ≤ 4 * e := by omega
  have h5 : 3 * (q * w) ≤ 4 * (w * e) := by nlinarith [Nat.mul_le_mul_left w h4]
  have h6 : q * (6 * q ^ 2 + 5 * q + 8) ≤ 8 * (q * w) := by nlinarith [Nat.mul_le_mul_left q h2]
  have h7 : (q + 4) * N ≤ 4 * (w * e) := by
    rw [hN]
    nlinarith [a1, a2, h5, h6]
  have h8 : K0 * (w * (e + 1)) ≤ K0 * inc := Nat.mul_le_mul_left K0 hinc
  have h9 : 5 * q * sz ≤ 5 * q * t := Nat.mul_le_mul_left _ hsz
  have h10 : K0 * (s + w) ≤ K0 * (N + w) := Nat.mul_le_mul_left K0 (by omega)
  have h11 : K0 * ((q + 4) * N) ≤ K0 * (4 * (w * e)) := Nat.mul_le_mul_left K0 h7
  have h12 : q * (N * K0) ≤ q * (20 * t) := by nlinarith [h3, h8, h9, h10, h11]
  exact Nat.le_of_mul_le_mul_left h12 (by omega)

end PEqualNP.Outside.L_meta_1728

theorem PEqualNP.Outside.L_meta_1728 : (∀ (N82 K82 v82 : ℕ) (I82 : Fin N82 → Fin N82 → Prop) [DecidableRel I82] (Cs82 : Fin v82 → PEqualNP.CircuitLowerBounds.Circuit) (A82 : Finset (Fin v82)) (iz82 : Fin v82) (S82 W82 B82 : Finset (Fin N82)), (∀ i82 : Fin v82, (∀ g82 ∈ (Cs82 i82).gates, (g82.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g82.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g82.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N82 + N82) (Cs82 i82)) → iz82 ∈ A82 → Disjoint W82 B82 → (∀ p82 ∈ S82, ∀ l82 ∈ B82, ¬ I82 p82 l82) → (∀ X82 Y82 : Finset (Fin N82), X82 ⊆ S82 → Y82 ⊆ W82 → Y82.card ≤ K82 → (∀ p82a ∈ X82, ∀ l82a ∈ Y82, ¬ I82 p82a l82a) → ∃ i82a ∈ A82, PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 i82a) (Fin.append (fun a82 => decide (a82 ∈ X82)) (fun b82 => decide (b82 ∈ (Y82 ∪ B82)))) = false) → (∀ pz82 ∈ S82, ∀ T82 ⊆ W82, (∀ l82b ∈ T82, ¬ I82 pz82 l82b) → T82.card ≤ K82 → PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 iz82) (Fin.append (fun a82a => decide (a82a ∈ ({pz82} : Finset (Fin N82)))) (fun b82a => decide (b82a ∈ (T82 ∪ B82)))) = true → ∀ X82a Y82a : Finset (Fin N82), X82a ⊆ S82.filter (fun u82 => u82 ≠ pz82 ∧ ∀ l82c ∈ T82, ¬ I82 u82 l82c) → Y82a ⊆ W82.filter (fun l82d => ¬ I82 pz82 l82d ∧ l82d ∉ T82) → Y82a.card + T82.card ≤ K82 → (∀ p82b ∈ X82a, ∀ l82e ∈ Y82a, ¬ I82 p82b l82e) → ∃ i82b ∈ A82.erase iz82, PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 i82b) (Fin.append (fun a82b => decide (a82b ∈ X82a)) (fun b82b => decide (b82b ∈ (Y82a ∪ (T82 ∪ B82))))) = false) ∧ (∀ wz82 ∈ W82, ∀ Q82 ⊆ S82, (∀ p82c ∈ Q82, ¬ I82 p82c wz82) → PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 iz82) (Fin.append (fun a82c => decide (a82c ∈ Q82)) (fun b82c => decide (b82c ∈ (insert wz82 B82)))) = true → ∀ X82b Y82b : Finset (Fin N82), X82b ⊆ S82.filter (fun u82a => ¬ I82 u82a wz82 ∧ u82a ∉ Q82) → Y82b ⊆ W82.filter (fun l82f => l82f ≠ wz82 ∧ ∀ p82d ∈ Q82, ¬ I82 p82d l82f) → Y82b.card + 1 ≤ K82 → (∀ p82e ∈ X82b, ∀ l82g ∈ Y82b, ¬ I82 p82e l82g) → ∃ i82c ∈ A82.erase iz82, PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 i82c) (Fin.append (fun a82d => decide (a82d ∈ X82b)) (fun b82d => decide (b82d ∈ (Y82b ∪ insert wz82 B82)))) = false)) → (∀ (q131 N131 r131 : ℕ) (I131 : Fin N131 → Fin N131 → Prop) [DecidableRel I131] (S131 W131 : Finset (Fin N131)), 2 ≤ q131 → N131 = q131 ^ 2 + q131 + 1 → (∀ l131f : Fin N131, (Finset.univ.filter (fun p131b => I131 p131b l131f)).card = q131 + 1) → (∀ pa131 pb131 : Fin N131, pa131 ≠ pb131 → ∃! lb131 : Fin N131, I131 pa131 lb131 ∧ I131 pb131 lb131) → (∀ (pz131 : Fin N131) (T131 : Finset (Fin N131)), T131.card ≤ r131 → (W131 \ W131.filter (fun l131 => ¬ I131 pz131 l131 ∧ l131 ∉ T131)).card ≤ q131 + 1 + r131 ∧ ∀ l131b ∈ W131.filter (fun l131a => ¬ I131 pz131 l131a ∧ l131a ∉ T131), (S131.filter (fun u131 => I131 u131 l131b)).card ≤ ((S131.filter (fun u131a => u131a ≠ pz131 ∧ ∀ m131 ∈ T131, ¬ I131 u131a m131)).filter (fun u131b => I131 u131b l131b)).card + r131) ∧ (∀ (wz131 : Fin N131) (Q131 : Finset (Fin N131)), Q131.card ≤ r131 → (W131 \ W131.filter (fun l131c => l131c ≠ wz131 ∧ ∀ p131 ∈ Q131, ¬ I131 p131 l131c)).card ≤ 1 + r131 * (q131 + 1) ∧ ∀ l131e ∈ W131.filter (fun l131d => l131d ≠ wz131 ∧ ∀ p131a ∈ Q131, ¬ I131 p131a l131d), (S131.filter (fun u131c => I131 u131c l131e)).card ≤ ((S131.filter (fun u131d => ¬ I131 u131d wz131 ∧ u131d ∉ Q131)).filter (fun u131e => I131 u131e l131e)).card + 1)) → (∀ (q90 N90 a90 b90 : ℕ) (I90 : Fin N90 → Fin N90 → Prop) [DecidableRel I90] (D90 : PEqualNP.CircuitLowerBounds.Circuit) (S90 W90 : Finset (Fin N90)) (nu90 : Fin N90 → Bool), 2 ≤ q90 → N90 = q90 ^ 2 + q90 + 1 → (∀ l90c : Fin N90, (Finset.univ.filter (fun p90c => I90 p90c l90c)).card = q90 + 1) → (∀ pa90 pb90 : Fin N90, pa90 ≠ pb90 → ∃! lb90 : Fin N90, I90 pa90 lb90 ∧ I90 pb90 lb90) → (∀ g90 ∈ D90.gates, (g90.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g90.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g90.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N90 + N90) D90 → (∀ j90 < D90.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i90 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).inputs, (D90.lineDegrees (N90 + N90) (Finset.Ico N90 (N90 + N90))).getD i90 0 = 0) ∨ (∀ h90 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D90 j90).inputs, (D90.lineDegrees (N90 + N90) (Finset.range N90)).getD h90 0 = 0)) → 1 ≤ a90 → 1 ≤ b90 → (∀ p90 ∈ S90, ∀ l90 ∈ W90, I90 p90 l90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90 => decide (u90 ∈ S90) && decide (u90 = p90)) (fun t90 => if t90 ∈ W90 then decide (t90 = l90) else nu90 t90)) = true) → (∀ p90a ∈ S90, ∀ T90 ⊆ W90, (∀ l90a ∈ T90, ¬ I90 p90a l90a) → T90.card ≤ a90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90a => decide (u90a ∈ S90) && decide (u90a = p90a)) (fun t90a => if t90a ∈ W90 then decide (t90a ∈ T90) else nu90 t90a)) = false) → (∀ l90b ∈ W90, ∀ X90 ⊆ S90, (∀ p90b ∈ X90, ¬ I90 p90b l90b) → X90.card ≤ b90 → PEqualNP.MetaComplexity.circuitFun (N90 + N90) D90 (Fin.append (fun u90b => decide (u90b ∈ S90) && decide (u90b ∈ X90)) (fun t90b => if t90b ∈ W90 then decide (t90b = l90b) else nu90 t90b)) = false) → min (min a90 b90) q90 * ((S90 ×ˢ W90).filter (fun pl90 => I90 pl90.1 pl90.2)).card ≤ 5 * q90 * D90.size + min (min a90 b90) q90 * (S90.card + W90.card)) → ∀ (q111 N111 k111 v111 t111 : ℕ) (I111 : Fin N111 → Fin N111 → Prop) [DecidableRel I111] (Cs111 : Fin v111 → PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q111 → N111 = q111 ^ 2 + q111 + 1 → (∀ l111a : Fin N111, (Finset.univ.filter (fun p111a => I111 p111a l111a)).card = q111 + 1) → (∀ pa111 pb111 : Fin N111, pa111 ≠ pb111 → ∃! lb111 : Fin N111, I111 pa111 lb111 ∧ I111 pb111 lb111) → 8 ≤ q111 → 1 ≤ v111 → v111 ≤ k111 → 8 * v111 ≤ q111 → (∀ i111 : Fin v111, ((∀ g111 ∈ (Cs111 i111).gates, (g111.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g111.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g111.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N111 + N111) (Cs111 i111)) ∧ (∀ j111 < (Cs111 i111).gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i111c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).inputs, ((Cs111 i111).lineDegrees (N111 + N111) (Finset.Ico N111 (N111 + N111))).getD i111c 0 = 0) ∨ (∀ h111 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).inputs, ((Cs111 i111).lineDegrees (N111 + N111) (Finset.range N111)).getD h111 0 = 0)) ∧ (Cs111 i111).size ≤ t111) → (∀ p111 l111 : Fin N111, I111 p111 l111 → ∀ i111a : Fin v111, PEqualNP.MetaComplexity.circuitFun (N111 + N111) (Cs111 i111a) (fun i111d => decide (i111d = Fin.castAdd N111 p111 ∨ i111d = Fin.natAdd N111 l111)) = true) → (∀ z111 : Fin (N111 + N111) → Bool, (Finset.univ.filter (fun l111b : Fin N111 => z111 (Fin.natAdd N111 l111b) = true)).card ≤ k111 → (¬ ∃ p111b l111c : Fin N111, I111 p111b l111c ∧ z111 (Fin.castAdd N111 p111b) = true ∧ z111 (Fin.natAdd N111 l111c) = true) → ∃ i111b : Fin v111, PEqualNP.MetaComplexity.circuitFun (N111 + N111) (Cs111 i111b) z111 = false) → N111 * (min k111 (q111 / 4) / v111) ≤ 20 * t111 := by
  intro H1 H2 H3 q N k v t I _ Cs hq2 hN hline huniq hq8 hv1 hvk h8v hC hacc hrej
  rcases Nat.eq_zero_or_pos (min k (q / 4) / v) with h0 | hK0
  · rw [h0]
    simp
  obtain ⟨K0, hK0def⟩ : ∃ K0, K0 = min k (q / 4) / v := ⟨_, rfl⟩
  rw [← hK0def] at hK0 ⊢
  have hvK0 : v * K0 ≤ q / 4 := by
    rw [hK0def]
    exact (Nat.mul_div_le _ _).trans (min_le_right _ _)
  have hvK0k : v * K0 ≤ k := by
    rw [hK0def]
    exact (Nat.mul_div_le _ _).trans (min_le_left _ _)
  have hK0v : K0 ≤ v * K0 := Nat.le_mul_of_pos_left K0 hv1
  obtain ⟨c, hc⟩ : ∃ c, c = 1 + K0 * (q + 1) := ⟨_, rfl⟩
  have hc1 : q + 1 + K0 ≤ c := by
    have h1 : q ≤ K0 * q := Nat.le_mul_of_pos_left q hK0
    have h2 : K0 * (q + 1) = K0 * q + K0 := Nat.mul_succ K0 q
    omega
  have key : ∀ n : ℕ, ∀ (A : Finset (Fin v)) (S W B : Finset (Fin N)) (K j : ℕ), A.card = n →
      n + j = v → Disjoint W B → (∀ p ∈ S, ∀ l ∈ B, ¬ I p l) →
      (∀ X Y : Finset (Fin N), X ⊆ S → Y ⊆ W → Y.card ≤ K → (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
        ∃ i ∈ A, PEqualNP.MetaComplexity.circuitFun (N + N) (Cs i)
          (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ (Y ∪ B)))) = false) →
      n * K0 ≤ K → N ≤ W.card + j * c →
      (∀ l ∈ W, q + 1 ≤ (S.filter (fun u => I u l)).card + j * K0) → N * K0 ≤ 20 * t := by
    intro n
    induction n with
    | zero =>
      intro A S W B K j hA _ _ _ hR _ _ _
      obtain ⟨i, hi, _⟩ := hR ∅ ∅ (Finset.empty_subset _) (Finset.empty_subset _) (by simp) (by simp)
      rw [Finset.card_eq_zero.mp hA] at hi
      simp at hi
    | succ n ih =>
      intro A S W B K j hA hnj hWB hSB hR hK hWc hSc
      obtain ⟨iz, hiz⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
      have hH1 := H1 N K v I Cs A iz S W B (fun i => (hC i).1) hiz hWB hSB hR
      have hH2 := H2 q N K0 I S W hq2 hN hline huniq
      have hsm : (n + 1) * K0 = n * K0 + K0 := Nat.succ_mul n K0
      have hjK : (j + 1) * K0 = j * K0 + K0 := Nat.succ_mul j K0
      have hjc : (j + 1) * c = j * c + c := Nat.succ_mul j c
      have hAe : (A.erase iz).card = n := by
        rw [Finset.card_erase_of_mem hiz, hA]
        rfl
      by_cases hP : ∃ pz ∈ S, ∃ T ⊆ W, (∀ l ∈ T, ¬ I pz l) ∧ T.card ≤ K0 ∧
          PEqualNP.MetaComplexity.circuitFun (N + N) (Cs iz)
            (Fin.append (fun a => decide (a ∈ ({pz} : Finset (Fin N))))
              (fun b => decide (b ∈ (T ∪ B)))) = true
      · obtain ⟨pz, hpz, T, hT, hTI, hTc, hb⟩ := hP
        have hTK : T.card ≤ K := by omega
        obtain ⟨hcW, hcS⟩ := hH2.1 pz T hTc
        have hsub := Finset.card_sdiff_add_card_eq_card
          (Finset.filter_subset (fun l => ¬ I pz l ∧ l ∉ T) W)
        refine ih (A.erase iz) _ _ (T ∪ B) (K - T.card) (j + 1) hAe (by omega) ?_ ?_
          (fun X Y hX hY hYc hXY => hH1.1 pz hpz T hT hTI hTK hb X Y hX hY (by omega) hXY)
          (by omega) (by omega) ?_
        · rw [Finset.disjoint_left]
          intro l hl hl2
          rcases Finset.mem_union.mp hl2 with h1 | h1
          · exact (Finset.mem_filter.mp hl).2.2 h1
          · exact Finset.disjoint_left.mp hWB (Finset.mem_filter.mp hl).1 h1
        · intro p hp l hl
          rcases Finset.mem_union.mp hl with h1 | h1
          · exact (Finset.mem_filter.mp hp).2.2 l h1
          · exact hSB p (Finset.mem_filter.mp hp).1 l h1
        · intro l hl
          have h1 := hcS l hl
          have h2 := hSc l (Finset.mem_filter.mp hl).1
          omega
      · by_cases hL : ∃ wz ∈ W, ∃ Q ⊆ S, (∀ p ∈ Q, ¬ I p wz) ∧ Q.card ≤ K0 ∧
            PEqualNP.MetaComplexity.circuitFun (N + N) (Cs iz)
              (Fin.append (fun a => decide (a ∈ Q))
                (fun b => decide (b ∈ (insert wz B)))) = true
        · obtain ⟨wz, hwz, Q, hQ, hQI, hQc, hb⟩ := hL
          obtain ⟨hcW, hcS⟩ := hH2.2 wz Q hQc
          have hsub := Finset.card_sdiff_add_card_eq_card
            (Finset.filter_subset (fun l => l ≠ wz ∧ ∀ p ∈ Q, ¬ I p l) W)
          refine ih (A.erase iz) _ _ (insert wz B) (K - 1) (j + 1) hAe (by omega) ?_ ?_
            (fun X Y hX hY hYc hXY => hH1.2 wz hwz Q hQ hQI hb X Y hX hY (by omega) hXY)
            (by omega) (by omega) ?_
          · rw [Finset.disjoint_left]
            intro l hl hl2
            rcases Finset.mem_insert.mp hl2 with h1 | h1
            · exact (Finset.mem_filter.mp hl).2.1 h1
            · exact Finset.disjoint_left.mp hWB (Finset.mem_filter.mp hl).1 h1
          · intro p hp l hl
            rcases Finset.mem_insert.mp hl with h1 | h1
            · rw [h1]
              exact (Finset.mem_filter.mp hp).2.1
            · exact hSB p (Finset.mem_filter.mp hp).1 l h1
          · intro l hl
            have h1 := hcS l hl
            have h2 := hSc l (Finset.mem_filter.mp hl).1
            omega
        · have h3 := H3 q N K0 K0 I (Cs iz) S W (fun b => decide (b ∈ B)) hq2 hN hline huniq
            (hC iz).1.1 (hC iz).1.2 (hC iz).2.1 hK0 hK0
            (by
              intro p hp l hl hI
              rw [PEqualNP.Outside.L_meta_1728.inP S p hp,
                PEqualNP.Outside.L_meta_1728.lnL W B l hl hWB]
              exact PEqualNP.Outside.L_meta_1728.acc_mono (Cs iz) (hC iz).1.1 p l B (hacc p l hI iz))
            (by
              intro p hp T hT hTI hTc
              rw [PEqualNP.Outside.L_meta_1728.inP S p hp,
                PEqualNP.Outside.L_meta_1728.lnT W B T hT hWB]
              by_contra hne
              exact hP ⟨p, hp, T, hT, hTI, hTc, Bool.eq_true_of_not_eq_false hne⟩)
            (by
              intro l hl X hX hXI hXc
              rw [PEqualNP.Outside.L_meta_1728.inX S X hX,
                PEqualNP.Outside.L_meta_1728.lnL W B l hl hWB]
              by_contra hne
              exact hL ⟨l, hl, X, hX, hXI, hXc, Bool.eq_true_of_not_eq_false hne⟩)
          have hmin : min (min K0 K0) q = K0 := by
            rw [min_self]
            exact min_eq_left (by omega)
          rw [hmin] at h3
          have hjv : j * K0 ≤ v * K0 := Nat.mul_le_mul_right K0 (by omega)
          have hwN : N ≤ W.card + (j + j * K0 * (q + 1)) := by
            have h1 : j * c = j + j * K0 * (q + 1) := by
              rw [hc]
              ring
            omega
          have hs : S.card ≤ N := by simpa using Finset.card_le_univ S
          have hinc := PEqualNP.Outside.L_meta_1728.inc_ge I S W (q + 1 - j * K0)
            (fun l hl => by
              have h2 := hSc l hl
              omega)
          exact PEqualNP.Outside.L_meta_1728.arith q N K0 t W.card S.card _ (j * K0) j (Cs iz).size
            hN hq8 (by omega) (by omega) hwN hs hinc (hC iz).2.2 h3
  refine key v Finset.univ Finset.univ Finset.univ ∅ (v * K0) 0 (by simp) (by omega)
    (Finset.disjoint_empty_right _) (by simp) ?_ le_rfl (by simp) ?_
  · intro X Y _ _ hYc hXY
    have hz := hrej (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ (Y ∪ ∅))))
      (by
        have h1 : (Finset.univ.filter (fun l : Fin N =>
            Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ (Y ∪ ∅)))
              (Fin.natAdd N l) = true)) = Y := by
          ext l
          rw [Finset.mem_filter, Fin.append_right]
          simp
        rw [h1]
        omega)
      (by
        rintro ⟨p, l, hI, hp, hl⟩
        rw [Fin.append_left] at hp
        rw [Fin.append_right] at hl
        exact hXY p (by simpa using hp) l (by simpa using hl) hI)
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, Finset.mem_univ _, hi⟩
  · intro l _
    rw [hline l]
    omega
