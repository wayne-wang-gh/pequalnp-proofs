import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1603

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CarriedProduct PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]


def F (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) : List ℕ :=
  ((List.range m).reverse).foldl (liveStep n C vals) L

lemma F_zero (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) :
    F n C vals 0 L = L := by
  simp [F]

lemma F_succ (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) :
    F n C vals (m + 1) L = F n C vals m (liveStep n C vals L m) := by
  simp [F, List.range_succ]

lemma step_sub (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ) (hw : w ∈ L) :
    w ∈ liveStep n C vals L j := by
  unfold liveStep
  split_ifs
  · exact List.mem_append_left _ hw
  · exact hw

lemma step_mem (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ)
    (h : w ∈ liveStep n C vals L j) :
    w ∈ L ∨ (n + j ∈ L ∧ w ∈ (gateAt C j).inputs ∧ w < n + j ∧ vals.getD w false = true) := by
  unfold liveStep at h
  split_ifs at h with hj
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Or.inr ⟨hj, h.1, h.2.1, h.2.2⟩
  · exact Or.inl h

lemma F_sub (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ L → w ∈ F n C vals m L := by
  intro m
  induction m with
  | zero => intro L w hw; rw [F_zero]; exact hw
  | succ m ih => intro L w hw; rw [F_succ]; exact ih _ w (step_sub n C vals L m w hw)

lemma F_mem (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ F n C vals m L → w ∈ L ∨ w < n + m := by
  intro m
  induction m with
  | zero => intro L w hw; rw [F_zero] at hw; exact Or.inl hw
  | succ m ih =>
    intro L w hw
    rw [F_succ] at hw
    rcases ih _ w hw with h | h
    · rcases step_mem n C vals L m w h with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · exact Or.inr (by omega)

lemma F_true (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ), (∀ w ∈ L, vals.getD w false = true) →
      ∀ w ∈ F n C vals m L, vals.getD w false = true := by
  intro m
  induction m with
  | zero => intro L hL w hw; rw [F_zero] at hw; exact hL w hw
  | succ m ih =>
    intro L hL w hw
    rw [F_succ] at hw
    refine ih _ ?_ w hw
    intro w2 hw2
    rcases step_mem n C vals L m w2 hw2 with h | h
    · exact hL w2 h
    · exact h.2.2.2

lemma F_back (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (j : ℕ), j < m → n + j ∈ F n C vals m L →
      ∀ a ∈ (gateAt C j).inputs, a < n + j → vals.getD a false = true →
        a ∈ F n C vals m L := by
  intro m
  induction m with
  | zero => intro L j hj; omega
  | succ m ih =>
    intro L j hj hmem a ha hlt hv
    rw [F_succ] at hmem ⊢
    by_cases hjm : j < m
    · exact ih _ j hjm hmem a ha hlt hv
    · have hjeq : j = m := by omega
      subst hjeq
      have h1 : n + j ∈ liveStep n C vals L j := by
        rcases F_mem n C vals j _ _ hmem with h | h
        · exact h
        · omega
      have h2 : n + j ∈ L := by
        rcases step_mem n C vals L j _ h1 with h | h
        · exact h
        · exact h.1
      apply F_sub
      unfold liveStep
      rw [if_pos h2]
      refine List.mem_append_right _ ?_
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ha, hlt, hv⟩

lemma liveWires_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    liveWires n C x = F n C (C.wires (List.ofFn x)) C.gates.length
      (if (C.wires (List.ofFn x)).getD C.output false then [C.output] else []) := rfl

lemma live_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : IsLive n C x w) :
    W n C x w = true := by
  unfold IsLive at h
  rw [liveWires_eq] at h
  refine F_true n C _ _ _ ?_ w h
  intro w2 hw2
  split_ifs at hw2 with hc
  · simp only [List.mem_singleton] at hw2
    rw [hw2]; exact hc
  · simp at hw2

lemma live_back (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (h : IsLive n C x (n + j)) (a : ℕ) (ha : a ∈ (gateAt C j).inputs) (hlt : a < n + j)
    (hv : W n C x a = true) : IsLive n C x a := by
  unfold IsLive at h ⊢
  rw [liveWires_eq] at h ⊢
  exact F_back n C _ _ _ j hj h a ha hlt hv

lemma live_out (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : W n C x C.output = true) :
    IsLive n C x C.output := by
  unfold IsLive
  rw [liveWires_eq]
  apply F_sub
  unfold W at h
  rw [if_pos h]
  simp

theorem closure (n : ℕ) (C : Circuit) (hM : Monotone2 C) (u v : Fin n) (B : ℕ)
    (hno : ∀ i, n + i < B → (gateAt C i).op = GateOp.and →
      ¬ IsLive n C (pairInput u v) (n + i)) :
    ∀ w, w < B → IsLive n C (pairInput u v) w →
      W n C (pairInput u u) w = true ∨ W n C (pairInput v v) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwB hlive
    have hw := live_true n C _ w hlive
    by_cases hwn : w < n
    · rw [W_input n C _ w hwn] at hw
      simp only [pairInput, decide_eq_true_eq] at hw
      rcases hw with h | h
      · left; rw [W_input n C _ w hwn]; simp [pairInput, h]
      · right; rw [W_input n C _ w hwn]; simp [pairInput, h]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k < C.gates.length
      · have hmem : gateAt C k ∈ C.gates := by
          rw [gateAt_eq C k hk]
          exact List.getElem_mem hk
        have hops := (hM _ hmem).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hops
        rcases hops with hop | hop
        · exact absurd hlive (hno k hwB hop)
        · rw [W_gate n C _ k hk, hop] at hw
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hw
          obtain ⟨i, hi, hv⟩ := hw
          have hlt : i < n + k := by
            by_contra hc
            simp [hc] at hv
          simp only [hlt, ite_true] at hv
          have hli := live_back n C _ k hk hlive i hi hlt hv
          have key : ∀ y : Fin n → Bool, W n C y i = true → W n C y (n + k) = true := by
            intro y hy
            rw [W_gate n C _ k hk, hop]
            simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
            exact ⟨i, hi, by simp only [hlt, ite_true]; exact hy⟩
          rcases ih i hlt (by omega) hli with h | h
          · exact Or.inl (key _ h)
          · exact Or.inr (key _ h)
      · exfalso
        have : W n C (pairInput u v) (n + k) = false := by
          simp only [W]
          exact getD_ge_length _ _ (by rw [wires_length]; omega)
        rw [this] at hw
        exact Bool.false_ne_true hw

lemma exists_min (P : ℕ → Prop) (h : ∃ t, P t) : ∃ t, P t ∧ ∀ i < t, ¬ P i := by
  by_contra hno
  have hall : ∀ t, ¬ P t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro hp
      exact hno ⟨t, hp, ih⟩
  obtain ⟨t, ht⟩ := h
  exact hall t ht

lemma card_pair (n : ℕ) (u v : Fin n) :
    (Finset.univ.filter (fun k : Fin n => pairInput u v k = true)).card ≤ 2 := by
  have hsub : Finset.univ.filter (fun k : Fin n => pairInput u v k = true) ⊆ {u, v} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairInput, decide_eq_true_eq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hk
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

lemma graph_single (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (pairInput i i) = false := by
  rw [Bool.eq_false_iff]
  intro h
  unfold graphFun at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩
  · simp at ha
  · simp only [pairInput, or_self, decide_eq_true_eq] at ha hb
    rw [ha, hb] at hab
    exact G.irrefl hab

lemma graph_pair (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  unfold graphFun
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  right
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (Finset.univ.filter (fun k : Fin n => x k = true)).card ≤ 2 → PEqualNP.MetaComplexity.circuitFun n C x = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) → (∀ j : ℕ, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ i : Fin n, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput i i) = false) → ∀ u v : Fin n, G.Adj u v → (∃ t : ℕ, PEqualNP.CarriedProduct.IsCarrier n C u v t) ∧ ∀ s : ℕ, PEqualNP.CarriedProduct.IsCarrier n C u v s → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C s).inputs = [a, b] ∧ ((PEqualNP.CleanedNonEdge.wireVal n C a (PEqualNP.EdgeOwnership.pairInput u u) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.EdgeOwnership.pairInput v v) = true) ∨ (PEqualNP.CleanedNonEdge.wireVal n C a (PEqualNP.EdgeOwnership.pairInput v v) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.EdgeOwnership.pairInput u u) = true)) := by
  intro n G hdec C hM hcorr hand u v huv
  have hW : ∀ y, circuitFun n C y = W n C y C.output := fun y => rfl
  have hsingle : ∀ i : Fin n, W n C (pairInput i i) C.output = false := by
    intro i
    rw [← hW, hcorr _ (card_pair n i i)]
    exact graph_single n G i
  have hout : IsLive n C (pairInput u v) C.output := by
    apply live_out
    rw [← hW, hcorr _ (card_pair n u v)]
    exact graph_pair n G u v huv
  have hex : ∃ t, (gateAt C t).op = GateOp.and ∧ IsLive n C (pairInput u v) (n + t) := by
    by_contra hno
    have hno2 : ∀ i, n + i < C.output + 1 → (gateAt C i).op = GateOp.and →
        ¬ IsLive n C (pairInput u v) (n + i) := fun i _ hop hl => hno ⟨i, hop, hl⟩
    rcases closure n C hM u v (C.output + 1) hno2 C.output (by omega) hout with h | h
    · rw [hsingle u] at h; exact Bool.false_ne_true h
    · rw [hsingle v] at h; exact Bool.false_ne_true h
  have hlen : ∀ t, (gateAt C t).op = GateOp.and → t < C.gates.length := by
    intro t hop
    by_contra hc
    have hd : gateAt C t = ⟨GateOp.or, []⟩ := by
      simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hc)]
    rw [hd] at hop
    cases hop
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ⟨hop, hl⟩, hmin⟩ := exists_min _ hex
    exact ⟨t, hlen t hop, hop, hl, fun i hi hopi hli => hmin i hi ⟨hopi, hli⟩⟩
  · intro s hs
    obtain ⟨hslen, hop, hl, hmin⟩ := hs
    have hno : ∀ i, n + i < n + s → (gateAt C i).op = GateOp.and →
        ¬ IsLive n C (pairInput u v) (n + i) := fun i hi hopi => hmin i (by omega) hopi
    have hval := live_true n C _ _ hl
    rw [W_gate n C _ s hslen, hop] at hval
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at hval
    have hin : ∀ a ∈ (gateAt C s).inputs, a < n + s ∧
        (W n C (pairInput u u) a = true ∨ W n C (pairInput v v) a = true) := by
      intro a ha
      have hv := hval a ha
      have hlt : a < n + s := by
        by_contra hc
        simp [hc] at hv
      simp only [hlt, ite_true] at hv
      exact ⟨hlt, closure n C hM u v (n + s) hno a hlt (live_back n C _ s hslen hl a ha hlt hv)⟩
    have hfalse : ∀ i : Fin n, W n C (pairInput i i) (n + s) = false :=
      fun i => hand s hslen hop i
    have hgate : ∀ y : Fin n → Bool, W n C y (n + s) =
        ((gateAt C s).inputs.map fun i => if i < n + s then W n C y i else false).all id := by
      intro y
      rw [W_gate n C y s hslen, hop]
      rfl
    have hmemg : gateAt C s ∈ C.gates := by
      rw [gateAt_eq C s hslen]
      exact List.getElem_mem hslen
    have hlen2 := (hM _ hmemg).2
    rcases hinp : (gateAt C s).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exfalso
      have hf := hfalse u
      rw [hgate, hinp] at hf
      simp at hf
    · exfalso
      have ha := hin a (by rw [hinp]; simp)
      rcases ha.2 with h | h
      · have hf := hfalse u
        rw [hgate, hinp] at hf
        simp [ha.1, h] at hf
      · have hf := hfalse v
        rw [hgate, hinp] at hf
        simp [ha.1, h] at hf
    · have ha := hin a (by rw [hinp]; simp)
      have hb := hin b (by rw [hinp]; simp)
      refine ⟨a, b, by first | rfl | exact hinp, ?_⟩
      rcases ha.2 with h1 | h1 <;> rcases hb.2 with h2 | h2
      · exfalso
        have hf := hfalse u
        rw [hgate, hinp] at hf
        simp [ha.1, hb.1, h1, h2] at hf
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exfalso
        have hf := hfalse v
        rw [hgate, hinp] at hf
        simp [ha.1, hb.1, h1, h2] at hf
    · exfalso
      rw [hinp] at hlen2
      simp at hlen2

end PEqualNP.Outside.L_meta_1603

theorem PEqualNP.Outside.L_meta_1603 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (Finset.univ.filter (fun k : Fin n => x k = true)).card ≤ 2 → PEqualNP.MetaComplexity.circuitFun n C x = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) → (∀ j : ℕ, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ i : Fin n, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput i i) = false) → ∀ u v : Fin n, G.Adj u v → (∃ t : ℕ, PEqualNP.CarriedProduct.IsCarrier n C u v t) ∧ ∀ s : ℕ, PEqualNP.CarriedProduct.IsCarrier n C u v s → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C s).inputs = [a, b] ∧ ((PEqualNP.CleanedNonEdge.wireVal n C a (PEqualNP.EdgeOwnership.pairInput u u) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.EdgeOwnership.pairInput v v) = true) ∨ (PEqualNP.CleanedNonEdge.wireVal n C a (PEqualNP.EdgeOwnership.pairInput v v) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.EdgeOwnership.pairInput u u) = true)) :=
  PEqualNP.Outside.L_meta_1603.main_aux
