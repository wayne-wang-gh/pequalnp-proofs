import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_931

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeAny {n : ℕ} (es : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  es.any (fun e => x e.1 && x e.2)

def edgeFold {n : ℕ} (x : Fin n → Bool) : List (Fin n × Fin n) → Bool
  | [] => false
  | e :: rest => rest.foldl (fun acc p => acc || (x p.1 && x p.2)) (x e.1 && x e.2)

theorem foldl_or_edgeAny {n : ℕ} (x : Fin n → Bool) (es : List (Fin n × Fin n)) :
    ∀ b : Bool, es.foldl (fun acc p => acc || (x p.1 && x p.2)) b = (b || edgeAny es x) := by
  induction es with
  | nil => intro b; simp [edgeAny]
  | cons e rest ih =>
    intro b
    simp only [List.foldl_cons, ih, edgeAny, List.any_cons, Bool.or_assoc]

theorem edgeFold_eq_edgeAny {n : ℕ} (x : Fin n → Bool) (es : List (Fin n × Fin n)) :
    edgeFold x es = edgeAny es x := by
  cases es with
  | nil => rfl
  | cons e rest =>
    simp only [edgeFold, foldl_or_edgeAny, edgeAny, List.any_cons]

def loopless {n : ℕ} (es : List (Fin n × Fin n)) : Bool :=
  es.all (fun e => e.1 != e.2)

def hasEdge {n : ℕ} (es : List (Fin n × Fin n)) (u v : Fin n) : Bool :=
  es.any (fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u))

def onlyNeighbor {n : ℕ} (es : List (Fin n × Fin n)) (v u : Fin n) : Bool :=
  es.all (fun e => (!(e.1 == v) || e.2 == u) && (!(e.2 == v) || e.1 == u))

def delV {n : ℕ} (v : Fin n) (es : List (Fin n × Fin n)) : List (Fin n × Fin n) :=
  es.filter (fun e => e.1 != v && e.2 != v)

def delVV {n : ℕ} (u v : Fin n) (es : List (Fin n × Fin n)) : List (Fin n × Fin n) :=
  es.filter (fun e => e.1 != u && e.2 != u && e.1 != v && e.2 != v)

theorem edgeAny_allFalse {n : ℕ} (es : List (Fin n × Fin n)) :
    edgeAny es (fun _ => false) = false := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp [edgeAny, ih]

theorem edgeAny_singleton {n : ℕ} {es : List (Fin n × Fin n)} (hl : loopless es = true)
    (v : Fin n) : edgeAny es (fun i => decide (i = v)) = false := by
  simp only [loopless, List.all_eq_true, bne_iff_ne] at hl
  rw [Bool.eq_false_iff]
  intro h
  simp only [edgeAny, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨e, he, h1, h2⟩ := h
  exact hl e he (h1.trans h2.symm)

theorem edgeAny_pair_true {n : ℕ} {es : List (Fin n × Fin n)} {u v : Fin n}
    (he : hasEdge es u v = true) :
    edgeAny es (fun i => decide (i = u ∨ i = v)) = true := by
  simp only [hasEdge, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨e, hmem, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := he
  · simp only [edgeAny, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨e, hmem, Or.inl h1, Or.inr h2⟩
  · simp only [edgeAny, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨e, hmem, Or.inr h1, Or.inl h2⟩

theorem edgeAny_pair_false {n : ℕ} {es : List (Fin n × Fin n)} (hl : loopless es = true)
    {u v : Fin n} (hne : hasEdge es u v = false) :
    edgeAny es (fun i => decide (i = u ∨ i = v)) = false := by
  simp only [loopless, List.all_eq_true, bne_iff_ne] at hl
  rw [Bool.eq_false_iff]
  intro h
  simp only [edgeAny, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨e, hmem, h1, h2⟩ := h
  have hneq := hl e hmem
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hneq (h1.trans h2.symm)
  · have ht : hasEdge es u v = true := by
      simp only [hasEdge, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact ⟨e, hmem, Or.inl ⟨h1, h2⟩⟩
    exact Bool.noConfusion (hne.symm.trans ht)
  · have ht : hasEdge es u v = true := by
      simp only [hasEdge, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact ⟨e, hmem, Or.inr ⟨h1, h2⟩⟩
    exact Bool.noConfusion (hne.symm.trans ht)
  · exact hneq (h1.trans h2.symm)

theorem edgeAny_nonempty_true {n : ℕ} {es : List (Fin n × Fin n)} (hne : es ≠ []) :
    ∃ x : Fin n → Bool, edgeAny es x = true := by
  cases es with
  | nil => exact absurd rfl hne
  | cons e rest => exact ⟨fun _ => true, by simp [edgeAny]⟩

def applyAssign {n : ℕ} (ρ : Fin n → Option Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => (ρ i).getD (x i)

theorem edgeAny_delV {n : ℕ} (es : List (Fin n × Fin n)) (v : Fin n) (x : Fin n → Bool) :
    edgeAny es (applyAssign (fun i => if i = v then some false else none) x) =
      edgeAny (delV v es) x := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    have hL : edgeAny (e :: rest) (applyAssign (fun i => if i = v then some false else none) x) =
        ((applyAssign (fun i => if i = v then some false else none) x e.1 &&
          applyAssign (fun i => if i = v then some false else none) x e.2) ||
          edgeAny rest (applyAssign (fun i => if i = v then some false else none) x)) := rfl
    have hR : delV v (e :: rest) =
        if (e.1 != v && e.2 != v) = true then e :: delV v rest else delV v rest :=
      List.filter_cons
    rw [hL, hR, ih]
    by_cases h1 : e.1 = v
    · simp [applyAssign, h1]
    · by_cases h2 : e.2 = v
      · simp [applyAssign, h1, h2]
      · simp [applyAssign, h1, h2, edgeAny]

theorem edgeAny_delVV_ff {n : ℕ} (es : List (Fin n × Fin n)) (u v : Fin n) (x : Fin n → Bool) :
    edgeAny es (applyAssign (fun i => if i = u then some false else if i = v then some false else none) x) =
      edgeAny (delVV u v es) x := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    have hL : edgeAny (e :: rest) (applyAssign (fun i => if i = u then some false else if i = v then some false else none) x) =
        ((applyAssign (fun i => if i = u then some false else if i = v then some false else none) x e.1 &&
          applyAssign (fun i => if i = u then some false else if i = v then some false else none) x e.2) ||
          edgeAny rest (applyAssign (fun i => if i = u then some false else if i = v then some false else none) x)) := rfl
    have hR : delVV u v (e :: rest) =
        if (e.1 != u && e.2 != u && e.1 != v && e.2 != v) = true then e :: delVV u v rest else delVV u v rest :=
      List.filter_cons
    rw [hL, hR, ih]
    by_cases h1u : e.1 = u
    · simp [applyAssign, h1u]
    · by_cases h2u : e.2 = u
      · simp [applyAssign, h1u, h2u]
      · by_cases h1v : e.1 = v
        · simp [applyAssign, h2u, h1v]
        · by_cases h2v : e.2 = v
          · simp [applyAssign, h1u, h1v, h2v]
          · simp [applyAssign, h1u, h2u, h1v, h2v, edgeAny]

theorem edgeAny_delVV_ft {n : ℕ} {es : List (Fin n × Fin n)} {u v : Fin n}
    (hleaf : onlyNeighbor es v u = true) (x : Fin n → Bool) :
    edgeAny es (applyAssign (fun i => if i = u then some false else if i = v then some true else none) x) =
      edgeAny (delVV u v es) x := by
  simp only [onlyNeighbor, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, beq_eq_false_iff_ne] at hleaf
  induction es with
  | nil => rfl
  | cons e rest ih =>
    have he := hleaf e List.mem_cons_self
    have hrest : ∀ a ∈ rest, (a.1 ≠ v ∨ a.2 = u) ∧ (a.2 ≠ v ∨ a.1 = u) :=
      fun a ha => hleaf a (List.mem_cons_of_mem _ ha)
    have ih' := ih hrest
    have hL : edgeAny (e :: rest) (applyAssign (fun i => if i = u then some false else if i = v then some true else none) x) =
        ((applyAssign (fun i => if i = u then some false else if i = v then some true else none) x e.1 &&
          applyAssign (fun i => if i = u then some false else if i = v then some true else none) x e.2) ||
          edgeAny rest (applyAssign (fun i => if i = u then some false else if i = v then some true else none) x)) := rfl
    have hR : delVV u v (e :: rest) =
        if (e.1 != u && e.2 != u && e.1 != v && e.2 != v) = true then e :: delVV u v rest else delVV u v rest :=
      List.filter_cons
    rw [hL, hR, ih']
    by_cases h1u : e.1 = u
    · simp [applyAssign, h1u]
    · by_cases h2u : e.2 = u
      · simp [applyAssign, h1u, h2u]
      · have h1v : e.1 ≠ v := fun h => he.1.elim (fun hn => hn h) h2u
        have h2v : e.2 ≠ v := fun h => he.2.elim (fun hn => hn h) h1u
        simp [applyAssign, h1u, h2u, h1v, h2v, edgeAny]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem wiresFrom_indep (v : ℕ) (gs : List Gate) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ j, j ≠ v → w1.getD j false = w2.getD j false) →
      (∀ g ∈ gs, v ∉ g.inputs) →
      ∀ j, j ≠ v → (wiresFrom gs w1).getD j false = (wiresFrom gs w2).getD j false := by
  induction gs with
  | nil => intro w1 w2 _ heq _ j hj; exact heq j hj
  | cons g gs ih =>
    intro w1 w2 hlen heq hnv j hj
    have hgnv : v ∉ g.inputs := hnv g List.mem_cons_self
    have hgsnv : ∀ g' ∈ gs, v ∉ g'.inputs := fun g' hg' => hnv g' (List.mem_cons_of_mem _ hg')
    have hmap : g.inputs.map (fun i => w1.getD i false) = g.inputs.map (fun i => w2.getD i false) :=
      List.map_congr_left fun i hi => heq i (fun h => hgnv (h ▸ hi))
    let b := g.op.eval (g.inputs.map fun i => w1.getD i false)
    have hstep : g.op.eval (g.inputs.map fun i => w2.getD i false) = b := by rw [← hmap]
    change (wiresFrom gs (w1 ++ [b])).getD j false =
      (wiresFrom gs (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])).getD j false
    rw [hstep]
    apply ih (w1 ++ [b]) (w2 ++ [b]) (by simp [hlen]) _ hgsnv j hj
    intro k hk
    by_cases hlt : k < w1.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]
      exact heq k hk
    · simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (Nat.le_of_not_gt hlt),
          List.getElem?_append_right (Nat.le_of_not_gt (hlen ▸ hlt)), hlen]

theorem wiresFrom_swap_uv (u v : ℕ) (gs : List Gate) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length → u < w1.length → v < w1.length →
      w1.getD u false = w2.getD v false →
      w1.getD v false = w2.getD u false →
      (∀ j, j ≠ u → j ≠ v → w1.getD j false = w2.getD j false) →
      (∀ g ∈ gs, (u ∉ g.inputs ∧ v ∉ g.inputs) ∨
        (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (g.inputs = [u, v] ∨ g.inputs = [v, u]))) →
      ∀ j, j ≠ u → j ≠ v → (wiresFrom gs w1).getD j false = (wiresFrom gs w2).getD j false := by
  induction gs with
  | nil => intro w1 w2 _ _ _ _ _ heq _ j hju hjv; exact heq j hju hjv
  | cons g gs ih =>
    intro w1 w2 hlen hu hv h12 h21 heq hok j hju hjv
    have hg := hok g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, (u ∉ g'.inputs ∧ v ∉ g'.inputs) ∨
        (g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (g'.inputs = [u, v] ∨ g'.inputs = [v, u])) :=
      fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    have hgeval : g.op.eval (g.inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      rcases hg with ⟨hnu, hnv⟩ | ⟨hop, hins | hins⟩
      · congr 1
        exact List.map_congr_left fun i hi => heq i (fun h => hnu (h ▸ hi)) (fun h => hnv (h ▸ hi))
      · change g.op = GateOp.and ∨ g.op = GateOp.or at hop
        rw [hins, List.map_cons, List.map_cons, List.map_nil, List.map_cons, List.map_cons, List.map_nil, h12, h21]
        rcases hop with hop | hop <;> rw [hop] <;>
          simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
      · change g.op = GateOp.and ∨ g.op = GateOp.or at hop
        rw [hins, List.map_cons, List.map_cons, List.map_nil, List.map_cons, List.map_cons, List.map_nil, h12, h21]
        rcases hop with hop | hop <;> rw [hop] <;>
          simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
    let b := g.op.eval (g.inputs.map fun i => w1.getD i false)
    change (wiresFrom gs (w1 ++ [b])).getD j false =
      (wiresFrom gs (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])).getD j false
    rw [← hgeval]
    apply ih (w1 ++ [b]) (w2 ++ [b]) (by simp [hlen]) (by simp; omega) (by simp; omega)
      (by rw [List.getD_append _ _ _ _ hu, List.getD_append _ _ _ _ (hlen ▸ hv)]; exact h12)
      (by rw [List.getD_append _ _ _ _ hv, List.getD_append _ _ _ _ (hlen ▸ hu)]; exact h21)
      _ hgs j hju hjv
    intro k hku hkv
    by_cases hlt : k < w1.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]
      exact heq k hku hkv
    · simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (Nat.le_of_not_gt hlt),
          List.getElem?_append_right (Nat.le_of_not_gt (hlen ▸ hlt)), hlen]

def shiftIdx (k i : ℕ) : ℕ := if i < k then i else i - 1

def shiftGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftIdx k)⟩

def deleteGate (n : ℕ) (C : Circuit) (p : ℕ) : Circuit :=
  ⟨C.gates.take p ++ (C.gates.drop (p + 1)).map (shiftGate (n + p)), shiftIdx (n + p) C.output⟩

theorem getD_del_eq (u v : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ u.length) :
    (u ++ b :: v).getD i false = (u ++ v).getD (shiftIdx u.length i) false := by
  simp only [shiftIdx]
  by_cases hlt : i < u.length
  · rw [ite_eq_left hlt]
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
  · rw [ite_eq_right hlt]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    have hsub : i - u.length = (i - 1 - u.length) + 1 := by omega
    rw [hsub, List.getElem?_cons_succ]

theorem wiresFrom_delete_aux (u : List Bool) (b : Bool) (rest : List Gate) :
    ∀ v : List Bool, (∀ g ∈ rest, ∀ i ∈ g.inputs, i ≠ u.length) →
      ∃ v' : List Bool,
        wiresFrom rest (u ++ b :: v) = u ++ b :: v' ∧
        wiresFrom (rest.map (shiftGate u.length)) (u ++ v) = u ++ v' := by
  induction rest with
  | nil =>
    intro v _
    exact ⟨v, rfl, rfl⟩
  | cons g gs ih =>
    intro v hall
    have hg := hall g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, ∀ i ∈ g'.inputs, i ≠ u.length :=
      fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')
    have hmap : g.inputs.map (fun i => (u ++ b :: v).getD i false) =
        (g.inputs.map (shiftIdx u.length)).map (fun i => (u ++ v).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact getD_del_eq u v b i (hg i hi)
    have hev : g.op.eval (g.inputs.map fun i => (u ++ b :: v).getD i false) =
        (shiftGate u.length g).op.eval ((shiftGate u.length g).inputs.map fun i => (u ++ v).getD i false) := by
      simp only [shiftGate, hmap]
    let c := g.op.eval (g.inputs.map fun i => (u ++ b :: v).getD i false)
    obtain ⟨v', h1, h2⟩ := ih (v ++ [c]) hgs
    refine ⟨v', ?_, ?_⟩
    · change wiresFrom gs ((u ++ b :: v) ++ [c]) = u ++ b :: v'
      simpa [List.append_assoc] using h1
    · change wiresFrom (gs.map (shiftGate u.length))
        ((u ++ v) ++ [(shiftGate u.length g).op.eval ((shiftGate u.length g).inputs.map fun i => (u ++ v).getD i false)]) = u ++ v'
      rw [← hev]
      simpa [c, List.append_assoc] using h2

theorem deleteGate_spec {n : ℕ} (C : Circuit) (hM : Monotone2 C) (p : ℕ) (hp : p < C.gates.length)
    (hout : C.output ≠ n + p)
    (hunused : ∀ g ∈ C.gates.drop (p + 1), ∀ i ∈ g.inputs, i ≠ n + p) :
    Monotone2 (deleteGate n C p) ∧
    (deleteGate n C p).size + 1 = C.size ∧
    ∀ x : Fin n → Bool, (deleteGate n C p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [deleteGate, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hM g (List.mem_of_mem_take h1)
    · obtain ⟨hop, hlen⟩ := hM g0 (List.mem_of_mem_drop hg0)
      exact ⟨hop, by simpa [shiftGate] using hlen⟩
  · simp only [Circuit.size, deleteGate, List.length_append, List.length_take, List.length_map,
      List.length_drop]
    omega
  · intro x
    have hsplit : C.gates = (C.gates.take p ++ [C.gates[p]]) ++ C.gates.drop (p + 1) := by
      conv_lhs => rw [← List.take_append_drop (p + 1) C.gates]
      rw [List.take_succ_eq_append_getElem hp]
    let u := wiresFrom (C.gates.take p) (List.ofFn x)
    have hu : u.length = n + p := by
      simp [u, length_wiresFrom, List.length_take, Nat.min_eq_left hp.le]
    let b := C.gates[p].op.eval (C.gates[p].inputs.map fun i => u.getD i false)
    have h1 : C.wires (List.ofFn x) = wiresFrom (C.gates.drop (p + 1)) (u ++ b :: []) := by
      change wiresFrom C.gates (List.ofFn x) = _
      conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append]
      rfl
    have h2 : (deleteGate n C p).wires (List.ofFn x) =
        wiresFrom ((C.gates.drop (p + 1)).map (shiftGate u.length)) (u ++ []) := by
      change wiresFrom (C.gates.take p ++ (C.gates.drop (p + 1)).map (shiftGate (n + p))) (List.ofFn x) = _
      rw [wiresFrom_append, ← hu]
      simp [u]
    obtain ⟨v', hv1, hv2⟩ := wiresFrom_delete_aux u b (C.gates.drop (p + 1)) [] (by simpa [hu] using hunused)
    rw [Circuit.eval, Circuit.eval, h1, h2, hv1, hv2]
    change (u ++ v').getD (shiftIdx (n + p) C.output) false = (u ++ b :: v').getD C.output false
    rw [← hu, getD_del_eq u v' b C.output (by omega)]

def evalVal (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def lookup (env : List (Sum Bool ℕ)) (i : ℕ) : Sum Bool ℕ :=
  env.getD i (Sum.inl false)

def simGate (n : ℕ) (g : Gate) (env : List (Sum Bool ℕ)) (outLen : ℕ) : Option Gate × Sum Bool ℕ :=
  let rs := g.inputs.map (lookup env)
  match g.op, rs with
  | GateOp.and, [] => (none, Sum.inl true)
  | GateOp.and, [r] => (none, r)
  | GateOp.and, [Sum.inl false, _] => (none, Sum.inl false)
  | GateOp.and, [_, Sum.inl false] => (none, Sum.inl false)
  | GateOp.and, [Sum.inl true, r] => (none, r)
  | GateOp.and, [r, Sum.inl true] => (none, r)
  | GateOp.and, [Sum.inr a, Sum.inr b] =>
    if a = b then (none, Sum.inr a) else (some ⟨GateOp.and, [a, b]⟩, Sum.inr (n + outLen))
  | GateOp.or, [] => (none, Sum.inl false)
  | GateOp.or, [r] => (none, r)
  | GateOp.or, [Sum.inl true, _] => (none, Sum.inl true)
  | GateOp.or, [_, Sum.inl true] => (none, Sum.inl true)
  | GateOp.or, [Sum.inl false, r] => (none, r)
  | GateOp.or, [r, Sum.inl false] => (none, r)
  | GateOp.or, [Sum.inr a, Sum.inr b] =>
    if a = b then (none, Sum.inr a) else (some ⟨GateOp.or, [a, b]⟩, Sum.inr (n + outLen))
  | _, _ => (none, Sum.inl false)

def simRun (n : ℕ) : List Gate → List Gate → List (Sum Bool ℕ) → List Bool →
    List Gate × List (Sum Bool ℕ) × List Bool
  | [], outGs, env, elims => (outGs, env, elims)
  | g :: gs, outGs, env, elims =>
    let r := simGate n g env outGs.length
    match r.1 with
    | none => simRun n gs outGs (env ++ [r.2]) (elims ++ [true])
    | some ng => simRun n gs (outGs ++ [ng]) (env ++ [r.2]) (elims ++ [false])

theorem simRun_append (n : ℕ) (gs₁ gs₂ : List Gate) :
    ∀ (outGs : List Gate) (env : List (Sum Bool ℕ)) (elims : List Bool),
      simRun n (gs₁ ++ gs₂) outGs env elims =
        let res := simRun n gs₁ outGs env elims
        simRun n gs₂ res.1 res.2.1 res.2.2 := by
  induction gs₁ with
  | nil => intro outGs env elims; rfl
  | cons g gs ih =>
    intro outGs env elims
    simp only [List.cons_append, simRun]
    cases (simGate n g env outGs.length).1 <;> exact ih _ _ _

theorem simGate_wf {n : ℕ} (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (env : List (Sum Bool ℕ)) (outLen : ℕ)
    (hbnd : ∀ v ∈ env, ∀ k, v = Sum.inr k → k < n + outLen) :
    let r := simGate n g env outLen
    (∀ ng, r.1 = some ng → ng.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ ng.inputs.length ≤ 2) ∧
    (∀ k, r.2 = Sum.inr k → k < n + (if r.1.isSome then outLen + 1 else outLen)) := by
  obtain ⟨hop, hlen⟩ := hg
  change g.op = GateOp.and ∨ g.op = GateOp.or at hop
  have hmem_bnd : ∀ i k, lookup env i = Sum.inr k → k < n + outLen := by
    intro i k hk
    by_cases hi : i < env.length
    · rw [lookup, List.getD_eq_getElem _ _ hi] at hk
      exact hbnd (env[i]) (List.getElem_mem hi) k hk
    · rw [lookup, List.getD_eq_default _ _ (Nat.le_of_not_gt hi)] at hk
      cases hk
  cases g with
  | mk op ins =>
    simp only at hop hlen
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
    · rcases hop with rfl | rfl <;> simp [simGate]
    · rcases hop with rfl | rfl <;>
        exact ⟨by simp [simGate], fun k hk => by
          simp only [simGate, List.map_cons, List.map_nil, Option.isSome_none, Bool.false_eq_true, ite_false] at hk ⊢
          exact hmem_bnd i k hk⟩
    · rcases hop with rfl | rfl
      · cases hli : lookup env i with
        | inl bi =>
          cases bi with
          | false => simp [simGate, hli]
          | true =>
            cases hlj : lookup env j with
            | inl bj => cases bj <;> simp [simGate, hli, hlj]
            | inr b =>
              refine ⟨by simp [simGate, hli, hlj], fun k hk => ?_⟩
              simp [simGate, hli, hlj] at hk ⊢; subst hk; exact hmem_bnd j b hlj
        | inr a =>
          cases hlj : lookup env j with
          | inl bj =>
            cases bj with
            | false => simp [simGate, hli, hlj]
            | true =>
              refine ⟨by simp [simGate, hli, hlj], fun k hk => ?_⟩
              simp [simGate, hli, hlj] at hk ⊢; subst hk; exact hmem_bnd i a hli
          | inr b =>
            by_cases hab : a = b
            · subst hab
              refine ⟨by simp [simGate, hli, hlj], fun k hk => ?_⟩
              simp [simGate, hli, hlj] at hk ⊢; subst hk; exact hmem_bnd i a hli
            · refine ⟨fun ng hng => ?_, fun k hk => ?_⟩
              · simp [simGate, hli, hlj, hab] at hng; subst hng; simp
              · simp [simGate, hli, hlj, hab] at hk ⊢; subst hk; omega
      · cases hli : lookup env i with
        | inl bi =>
          cases bi with
          | true => simp [simGate, hli]
          | false =>
            cases hlj : lookup env j with
            | inl bj => cases bj <;> simp [simGate, hli, hlj]
            | inr b =>
              refine ⟨by simp [simGate, hli, hlj], fun k hk => ?_⟩
              simp [simGate, hli, hlj] at hk ⊢; subst hk; exact hmem_bnd j b hlj
        | inr a =>
          cases hlj : lookup env j with
          | inl bj =>
            cases bj with
            | true => simp [simGate, hli, hlj]
            | false =>
              refine ⟨by simp [simGate, hli, hlj], fun k hk => ?_⟩
              simp [simGate, hli, hlj] at hk ⊢; subst hk; exact hmem_bnd i a hli
          | inr b =>
            by_cases hab : a = b
            · subst hab
              refine ⟨by simp [simGate, hli, hlj], fun k hk => ?_⟩
              simp [simGate, hli, hlj] at hk ⊢; subst hk; exact hmem_bnd i a hli
            · refine ⟨fun ng hng => ?_, fun k hk => ?_⟩
              · simp [simGate, hli, hlj, hab] at hng; subst hng; simp
              · simp [simGate, hli, hlj, hab] at hk ⊢; subst hk; omega
    · simp at hlen

theorem simGate_eval {n : ℕ} (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (env : List (Sum Bool ℕ)) (outGs : List Gate)
    (x : Fin n → Bool) (w : List Bool)
    (heval : ∀ i, evalVal (wiresFrom outGs (List.ofFn x)) (lookup env i) = w.getD i false) :
    let r := simGate n g env outGs.length
    let outGs' := match r.1 with | none => outGs | some ng => outGs ++ [ng]
    evalVal (wiresFrom outGs' (List.ofFn x)) r.2 =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨hop, hlen⟩ := hg
  change g.op = GateOp.and ∨ g.op = GateOp.or at hop
  have hw'len : (wiresFrom outGs (List.ofFn x)).length = n + outGs.length := by
    simp [length_wiresFrom]
  cases g with
  | mk op ins =>
    simp only at hop hlen
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
    · rcases hop with rfl | rfl <;> simp [simGate, GateOp.eval, evalVal]
    · rcases hop with rfl | rfl <;> simpa [simGate, GateOp.eval] using heval i
    · have hi := heval i
      have hj := heval j
      rcases hop with rfl | rfl
      · cases hli : lookup env i with
        | inl bi =>
          rw [hli] at hi
          cases bi with
          | false =>
            simp only [simGate, List.map_cons, List.map_nil, hli, evalVal, GateOp.eval, List.all_cons,
              List.all_nil, id_eq, Bool.and_true] at hi ⊢
            rw [← hi]; rfl
          | true =>
            cases hlj : lookup env j with
            | inl bj =>
              rw [hlj] at hj
              cases bj <;>
                (simp only [simGate, List.map_cons, List.map_nil, hli, hlj, evalVal, GateOp.eval,
                  List.all_cons, List.all_nil, id_eq, Bool.and_true] at hi hj ⊢; rw [← hi, ← hj]; rfl)
            | inr b =>
              rw [hlj] at hj
              simp only [simGate, List.map_cons, List.map_nil, hli, hlj, evalVal, GateOp.eval,
                List.all_cons, List.all_nil, id_eq, Bool.and_true] at hi hj ⊢
              rw [← hi, ← hj]; rfl
        | inr a =>
          rw [hli] at hi
          cases hlj : lookup env j with
          | inl bj =>
            rw [hlj] at hj
            cases bj <;>
              (simp only [simGate, List.map_cons, List.map_nil, hli, hlj, evalVal, GateOp.eval,
                List.all_cons, List.all_nil, id_eq, Bool.and_true] at hi hj ⊢; rw [← hi, ← hj]; simp)
          | inr b =>
            rw [hlj] at hj
            by_cases hab : a = b
            · subst hab
              simp only [simGate, List.map_cons, List.map_nil, hli, hlj, ite_true, evalVal, GateOp.eval,
                List.all_cons, List.all_nil, id_eq, Bool.and_true] at hi hj ⊢
              rw [← hi, ← hj]; simp
            · simp only [simGate, List.map_cons, List.map_nil, hli, hlj, hab, ite_false]
              rw [wiresFrom_append]
              change (wiresFrom outGs (List.ofFn x) ++
                [GateOp.and.eval ([a, b].map fun idx => (wiresFrom outGs (List.ofFn x)).getD idx false)]).getD
                (n + outGs.length) false = _
              rw [← hw'len, List.getD_eq_getElem _ _ (by simp)]
              simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero,
                List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [← hi, ← hj]; rfl
      · cases hli : lookup env i with
        | inl bi =>
          rw [hli] at hi
          cases bi with
          | true =>
            simp only [simGate, List.map_cons, List.map_nil, hli, evalVal, GateOp.eval, List.any_cons,
              List.any_nil, id_eq, Bool.or_false] at hi ⊢
            rw [← hi]; rfl
          | false =>
            cases hlj : lookup env j with
            | inl bj =>
              rw [hlj] at hj
              cases bj <;>
                (simp only [simGate, List.map_cons, List.map_nil, hli, hlj, evalVal, GateOp.eval,
                  List.any_cons, List.any_nil, id_eq, Bool.or_false] at hi hj ⊢; rw [← hi, ← hj]; rfl)
            | inr b =>
              rw [hlj] at hj
              simp only [simGate, List.map_cons, List.map_nil, hli, hlj, evalVal, GateOp.eval,
                List.any_cons, List.any_nil, id_eq, Bool.or_false] at hi hj ⊢
              rw [← hi, ← hj]; rfl
        | inr a =>
          rw [hli] at hi
          cases hlj : lookup env j with
          | inl bj =>
            rw [hlj] at hj
            cases bj <;>
              (simp only [simGate, List.map_cons, List.map_nil, hli, hlj, evalVal, GateOp.eval,
                List.any_cons, List.any_nil, id_eq, Bool.or_false] at hi hj ⊢; rw [← hi, ← hj]; simp)
          | inr b =>
            rw [hlj] at hj
            by_cases hab : a = b
            · subst hab
              simp only [simGate, List.map_cons, List.map_nil, hli, hlj, ite_true, evalVal, GateOp.eval,
                List.any_cons, List.any_nil, id_eq, Bool.or_false] at hi hj ⊢
              rw [← hi, ← hj]; simp
            · simp only [simGate, List.map_cons, List.map_nil, hli, hlj, hab, ite_false]
              rw [wiresFrom_append]
              change (wiresFrom outGs (List.ofFn x) ++
                [GateOp.or.eval ([a, b].map fun idx => (wiresFrom outGs (List.ofFn x)).getD idx false)]).getD
                (n + outGs.length) false = _
              rw [← hw'len, List.getD_eq_getElem _ _ (by simp)]
              simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero,
                List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [← hi, ← hj]; rfl
    · simp at hlen

theorem simRun_prefix (n : ℕ) (gs : List Gate) :
    ∀ (outGs : List Gate) (env : List (Sum Bool ℕ)) (elims : List Bool),
      let res := simRun n gs outGs env elims
      (∃ t, res.2.1 = env ++ t ∧ t.length = gs.length) ∧
      (∃ t, res.2.2 = elims ++ t ∧ t.length = gs.length) ∧
      res.1.length + res.2.2.count true = outGs.length + elims.count true + gs.length := by
  induction gs with
  | nil =>
    intro outGs env elims
    exact ⟨⟨[], by simp [simRun], rfl⟩, ⟨[], by simp [simRun], rfl⟩, by simp [simRun]⟩
  | cons g gs ih =>
    intro outGs env elims
    simp only [simRun]
    cases (simGate n g env outGs.length).1 with
    | none =>
      obtain ⟨⟨te, hte, hle⟩, ⟨tb, htb, hlb⟩, hcnt⟩ :=
        ih outGs (env ++ [(simGate n g env outGs.length).2]) (elims ++ [true])
      refine ⟨⟨(simGate n g env outGs.length).2 :: te, by simpa [List.append_assoc] using hte, by simp [hle]⟩,
              ⟨true :: tb, by simpa [List.append_assoc] using htb, by simp [hlb]⟩, ?_⟩
      simp only [List.count_append, List.count_cons_self, List.count_nil, List.length_cons] at hcnt ⊢
      omega
    | some ng =>
      obtain ⟨⟨te, hte, hle⟩, ⟨tb, htb, hlb⟩, hcnt⟩ :=
        ih (outGs ++ [ng]) (env ++ [(simGate n g env outGs.length).2]) (elims ++ [false])
      refine ⟨⟨(simGate n g env outGs.length).2 :: te, by simpa [List.append_assoc] using hte, by simp [hle]⟩,
              ⟨false :: tb, by simpa [List.append_assoc] using htb, by simp [hlb]⟩, ?_⟩
      simp only [List.count_append, List.count_cons, beq_iff_eq, Bool.false_eq_true, ite_false,
        List.count_nil, List.length_append, List.length_cons, List.length_nil] at hcnt ⊢
      omega

theorem simRun_eval (n : ℕ) (gs : List Gate) :
    ∀ (outGs : List Gate) (env : List (Sum Bool ℕ)) (elims : List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ g ∈ outGs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ v ∈ env, ∀ k, v = Sum.inr k → k < n + outGs.length) →
      let res := simRun n gs outGs env elims
      (∀ g ∈ res.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ v ∈ res.2.1, ∀ k, v = Sum.inr k → k < n + res.1.length) ∧
      ∀ (x : Fin n → Bool) (w : List Bool), w.length = env.length →
        (∀ i, evalVal (wiresFrom outGs (List.ofFn x)) (lookup env i) = w.getD i false) →
        ∀ i, evalVal (wiresFrom res.1 (List.ofFn x)) (lookup res.2.1 i) = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil =>
    intro outGs env elims _ hout hbnd
    exact ⟨hout, hbnd, fun x w _ he i => he i⟩
  | cons g gs ih =>
    intro outGs env elims hgs hout hbnd
    have hg := hgs g List.mem_cons_self
    have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    have hwf := simGate_wf g hg env outGs.length hbnd
    simp only [simRun]
    cases hng : (simGate n g env outGs.length).1 with
    | none =>
      have hbnd' : ∀ v ∈ env ++ [(simGate n g env outGs.length).2], ∀ k, v = Sum.inr k → k < n + outGs.length := by
        intro v hv k hk
        rcases List.mem_append.mp hv with hv | hv
        · exact hbnd v hv k hk
        · have hv' : v = (simGate n g env outGs.length).2 := List.mem_singleton.mp hv
          have h2 := hwf.2 k (hv' ▸ hk)
          simpa [hng] using h2
      obtain ⟨hout', hbnd'', hev'⟩ :=
        ih outGs (env ++ [(simGate n g env outGs.length).2]) (elims ++ [true]) hgs' hout hbnd'
      refine ⟨hout', hbnd'', fun x w hwlen he i => ?_⟩
      have hge := simGate_eval g hg env outGs x w he
      simp only [hng] at hge
      apply hev' x (w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]) (by simp [hwlen]) _ i
      intro j
      by_cases hj : j < env.length
      · rw [lookup, List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (hwlen.symm ▸ hj)]
        exact he j
      · by_cases hjeq : j = env.length
        · subst hjeq
          have hl1 : lookup (env ++ [(simGate n g env outGs.length).2]) env.length =
              (simGate n g env outGs.length).2 := by
            rw [lookup, List.getD_eq_getElem _ _ (by simp)]
            simp
          have hl2 : (w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]).getD env.length false =
              g.op.eval (g.inputs.map fun idx => w.getD idx false) := by
            rw [← hwlen, List.getD_eq_getElem _ _ (by simp)]
            simp
          rw [hl1, hl2]; exact hge
        · rw [lookup, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          rfl
    | some ng =>
      have hng_ok := hwf.1 ng hng
      have hout_step : ∀ g' ∈ outGs ++ [ng], g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
        intro g' hg'
        rcases List.mem_append.mp hg' with hg' | hg'
        · exact hout g' hg'
        · exact (List.mem_singleton.mp hg') ▸ hng_ok
      have hbnd' : ∀ v ∈ env ++ [(simGate n g env outGs.length).2], ∀ k, v = Sum.inr k → k < n + (outGs ++ [ng]).length := by
        intro v hv k hk
        rcases List.mem_append.mp hv with hv | hv
        · have := hbnd v hv k hk; simp; omega
        · have hv' : v = (simGate n g env outGs.length).2 := List.mem_singleton.mp hv
          have h2 := hwf.2 k (hv' ▸ hk)
          simp [hng] at h2 ⊢; omega
      obtain ⟨hout', hbnd'', hev'⟩ :=
        ih (outGs ++ [ng]) (env ++ [(simGate n g env outGs.length).2]) (elims ++ [false]) hgs' hout_step hbnd'
      refine ⟨hout', hbnd'', fun x w hwlen he i => ?_⟩
      have hge := simGate_eval g hg env outGs x w he
      simp only [hng] at hge
      apply hev' x (w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]) (by simp [hwlen]) _ i
      intro j
      by_cases hj : j < env.length
      · rw [lookup, List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (hwlen.symm ▸ hj)]
        have hprev := he j
        rw [lookup] at hprev
        cases hval : env.getD j (Sum.inl false) with
        | inl b =>
          rw [hval] at hprev
          exact hprev
        | inr k =>
          have hk : k < n + outGs.length := by
            apply hbnd (env[j]) (List.getElem_mem hj) k
            rw [← List.getD_eq_getElem _ _ hj]; exact hval
          rw [hval] at hprev
          rw [wiresFrom_append]
          change (wiresFrom [ng] (wiresFrom outGs (List.ofFn x))).getD k false = w.getD j false
          rw [getD_wiresFrom [ng] (wiresFrom outGs (List.ofFn x)) k (by simp [length_wiresFrom, hk])]
          exact hprev
      · by_cases hjeq : j = env.length
        · subst hjeq
          have hl1 : lookup (env ++ [(simGate n g env outGs.length).2]) env.length =
              (simGate n g env outGs.length).2 := by
            rw [lookup, List.getD_eq_getElem _ _ (by simp)]
            simp
          have hl2 : (w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]).getD env.length false =
              g.op.eval (g.inputs.map fun idx => w.getD idx false) := by
            rw [← hwlen, List.getD_eq_getElem _ _ (by simp)]
            simp
          rw [hl1, hl2]; exact hge
        · rw [lookup, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          rfl

def initEnv (n : ℕ) (ρ : Fin n → Option Bool) : List (Sum Bool ℕ) :=
  List.ofFn (fun i : Fin n => match ρ i with | some b => Sum.inl b | none => Sum.inr i.val)

def simplify (n : ℕ) (ρ : Fin n → Option Bool) (C : Circuit) :
    Circuit × List (Sum Bool ℕ) × List Bool :=
  let res := simRun n C.gates [] (initEnv n ρ) []
  let out := match lookup res.2.1 C.output with
    | Sum.inr k => k
    | Sum.inl _ => n + res.1.length
  (⟨res.1, out⟩, res.2.1, res.2.2)

theorem simplify_spec {n : ℕ} (ρ : Fin n → Option Bool) (C : Circuit) (hM : Monotone2 C)
    (hx0 : ∃ x0 : Fin n → Bool, C.eval (List.ofFn (applyAssign ρ x0)) = false) :
    let res := simplify n ρ C
    Monotone2 res.1 ∧
    res.1.size + res.2.2.count true = C.size ∧
    res.2.1.length = n + C.gates.length ∧
    res.2.2.length = C.gates.length ∧
    (∀ x : Fin n → Bool, res.1.eval (List.ofFn x) = C.eval (List.ofFn (applyAssign ρ x))) ∧
    (∀ i (hi : i < n), lookup res.2.1 i = match ρ ⟨i, hi⟩ with | some b => Sum.inl b | none => Sum.inr i) ∧
    (∀ (x1 : Fin n → Bool), C.eval (List.ofFn (applyAssign ρ x1)) = true →
      ∀ b : Bool, lookup res.2.1 C.output ≠ Sum.inl b) := by
  have hbnd0 : ∀ v ∈ initEnv n ρ, ∀ k, v = Sum.inr k → k < n + ([] : List Gate).length := by
    intro v hv k hk
    simp only [initEnv, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    cases h : ρ i with
    | some b => simp [h] at hk
    | none => simp [h] at hk; subst hk; simp
  obtain ⟨hout, hbnd, hev⟩ := simRun_eval n C.gates [] (initEnv n ρ) [] hM (by simp) hbnd0
  obtain ⟨⟨te, hte, hle⟩, ⟨tb, htb, hlb⟩, hcnt⟩ := simRun_prefix n C.gates [] (initEnv n ρ) []
  have hinit_eval (x : Fin n → Bool) (i : ℕ) :
      evalVal (wiresFrom [] (List.ofFn x)) (lookup (initEnv n ρ) i) =
        (List.ofFn (applyAssign ρ x)).getD i false := by
    by_cases hi : i < n
    · rw [lookup, List.getD_eq_getElem _ _ (by simp [initEnv, hi]),
          List.getD_eq_getElem _ _ (by simp [hi])]
      simp only [initEnv, List.getElem_ofFn, applyAssign, wiresFrom, List.foldl_nil]
      cases h : ρ ⟨i, hi⟩ with
      | some b => rfl
      | none =>
        change (List.ofFn x).getD i false = x ⟨i, hi⟩
        rw [List.getD_eq_getElem _ _ (by simp [hi])]
        simp
    · rw [lookup, List.getD_eq_default _ _ (by simp [initEnv]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      rfl
  have hev_all (x : Fin n → Bool) (i : ℕ) :
      evalVal (wiresFrom (simRun n C.gates [] (initEnv n ρ) []).1 (List.ofFn x))
        (lookup (simRun n C.gates [] (initEnv n ρ) []).2.1 i) =
        (C.wires (List.ofFn (applyAssign ρ x))).getD i false :=
    hev x (List.ofFn (applyAssign ρ x)) (by simp [initEnv]) (hinit_eval x) i
  have hnot_true : lookup (simRun n C.gates [] (initEnv n ρ) []).2.1 C.output ≠ Sum.inl true := by
    intro h
    obtain ⟨x0, hx0⟩ := hx0
    have h1 := hev_all x0 C.output
    rw [h] at h1
    change true = C.eval (List.ofFn (applyAssign ρ x0)) at h1
    rw [hx0] at h1
    exact Bool.noConfusion h1
  refine ⟨hout, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [simplify, Circuit.size] using hcnt
  · change (simRun n C.gates [] (initEnv n ρ) []).2.1.length = n + C.gates.length
    rw [hte, List.length_append, hle]; simp [initEnv]
  · simp [simplify, htb, hlb]
  · intro x
    have h1 := hev_all x C.output
    simp only [simplify, Circuit.eval]
    cases h : lookup (simRun n C.gates [] (initEnv n ρ) []).2.1 C.output with
    | inl b =>
      cases b with
      | true => exact absurd h hnot_true
      | false =>
        rw [h] at h1
        change (wiresFrom (simRun n C.gates [] (initEnv n ρ) []).1 (List.ofFn x)).getD
          (n + (simRun n C.gates [] (initEnv n ρ) []).1.length) false = _
        rw [List.getD_eq_default _ _ (by simp [length_wiresFrom])]
        exact h1
    | inr k =>
      rw [h] at h1
      exact h1
  · intro i hi
    change lookup (simRun n C.gates [] (initEnv n ρ) []).2.1 i = _
    rw [lookup, hte, List.getD_append _ _ _ _ (by simp [initEnv, hi]),
        List.getD_eq_getElem _ _ (by simp [initEnv, hi])]
    simp [initEnv]
  · intro x1 hx1 b hb
    change lookup (simRun n C.gates [] (initEnv n ρ) []).2.1 C.output = Sum.inl b at hb
    cases b with
    | true => exact hnot_true hb
    | false =>
      have h1 := hev_all x1 C.output
      rw [hb] at h1
      change false = C.eval (List.ofFn (applyAssign ρ x1)) at h1
      rw [hx1] at h1
      exact Bool.noConfusion h1

theorem simplify_at_gate {n : ℕ} (ρ : Fin n → Option Bool) (C : Circuit)
    (p : ℕ) (hp : p < C.gates.length) :
    let res := simplify n ρ C
    let pre := simRun n (C.gates.take p) [] (initEnv n ρ) []
    let r := simGate n C.gates[p] pre.2.1 pre.1.length
    lookup res.2.1 (n + p) = r.2 ∧
    res.2.2.getD p false = r.1.isNone ∧
    (∀ j < n + p, lookup pre.2.1 j = lookup res.2.1 j) ∧
    pre.2.1.length = n + p := by
  have hsplit : C.gates = C.gates.take p ++ C.gates[p] :: C.gates.drop (p + 1) := by
    conv_lhs => rw [← List.take_append_drop p C.gates]
    rw [List.drop_eq_getElem_cons hp]
  obtain ⟨⟨te1, hte1, hle1⟩, ⟨tb1, htb1, hlb1⟩, _⟩ :=
    simRun_prefix n (C.gates.take p) [] (initEnv n ρ) []
  set pre := simRun n (C.gates.take p) [] (initEnv n ρ) [] with hpre
  have hpre_env_len : pre.2.1.length = n + p := by
    rw [hte1, List.length_append, hle1, List.length_take, Nat.min_eq_left hp.le]
    simp [initEnv]
  have hpre_elims_len : pre.2.2.length = p := by
    rw [htb1, List.length_append, hlb1, List.length_take, Nat.min_eq_left hp.le]
    simp
  have hrun : simRun n C.gates [] (initEnv n ρ) [] =
      simRun n (C.gates[p] :: C.gates.drop (p + 1)) pre.1 pre.2.1 pre.2.2 := by
    conv_lhs => rw [hsplit]
    rw [simRun_append]
  set r := simGate n C.gates[p] pre.2.1 pre.1.length with hr
  cases hr1 : r.1 with
  | none =>
    have hrun' : simRun n C.gates [] (initEnv n ρ) [] =
        simRun n (C.gates.drop (p + 1)) pre.1 (pre.2.1 ++ [r.2]) (pre.2.2 ++ [true]) := by
      rw [hrun]; simp only [simRun, ← hr, hr1]
    obtain ⟨⟨te2, hte2, _⟩, ⟨tb2, htb2, _⟩, _⟩ :=
      simRun_prefix n (C.gates.drop (p + 1)) pre.1 (pre.2.1 ++ [r.2]) (pre.2.2 ++ [true])
    refine ⟨?_, ?_, ?_, hpre_env_len⟩
    · simp only [simplify, lookup, hrun', hte2, List.append_assoc]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hpre_env_len, hr]
    · simp only [simplify, hrun', htb2, List.append_assoc]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hpre_elims_len, ← hr, hr1]
    · intro j hj
      simp only [simplify, lookup, hrun', hte2, List.append_assoc]
      rw [List.getD_append _ _ _ _ (by omega)]
  | some ng =>
    have hrun' : simRun n C.gates [] (initEnv n ρ) [] =
        simRun n (C.gates.drop (p + 1)) (pre.1 ++ [ng]) (pre.2.1 ++ [r.2]) (pre.2.2 ++ [false]) := by
      rw [hrun]; simp only [simRun, ← hr, hr1]
    obtain ⟨⟨te2, hte2, _⟩, ⟨tb2, htb2, _⟩, _⟩ :=
      simRun_prefix n (C.gates.drop (p + 1)) (pre.1 ++ [ng]) (pre.2.1 ++ [r.2]) (pre.2.2 ++ [false])
    refine ⟨?_, ?_, ?_, hpre_env_len⟩
    · simp only [simplify, lookup, hrun', hte2, List.append_assoc]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hpre_env_len, hr]
    · simp only [simplify, hrun', htb2, List.append_assoc]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hpre_elims_len, ← hr, hr1]
    · intro j hj
      simp only [simplify, lookup, hrun', hte2, List.append_assoc]
      rw [List.getD_append _ _ _ _ (by omega)]

theorem simGate_elim_of_ne_two {n : ℕ} (g : Gate) (env : List (Sum Bool ℕ)) (k : ℕ)
    (h : g.inputs.length ≠ 2) : (simGate n g env k).1.isNone = true := by
  cases g with
  | mk op ins =>
    cases ins with
    | nil => cases op <;> simp [simGate]
    | cons a t =>
      cases t with
      | nil => cases op <;> simp [simGate]
      | cons b t2 =>
        cases t2 with
        | nil => simp at h
        | cons c t3 => cases op <;> simp [simGate]

theorem simGate_elim_of_left {n : ℕ} (g : Gate) (a b : ℕ) (hins : g.inputs = [a, b])
    (env : List (Sum Bool ℕ)) (k : ℕ)
    (hl : (lookup env a).isLeft ∨ (lookup env b).isLeft) :
    (simGate n g env k).1.isNone = true := by
  cases g with
  | mk op ins =>
    simp only at hins; subst hins
    cases op <;> cases h1 : lookup env a with
    | inl ba => cases ba <;> cases h2 : lookup env b with
      | inl bb => cases bb <;> simp [simGate, h1, h2]
      | inr kb => simp [simGate, h1, h2]
    | inr ka => cases h2 : lookup env b with
      | inl bb => cases bb <;> simp [simGate, h1, h2]
      | inr kb => simp [h1, h2] at hl

theorem simGate_elim_of_eq {n : ℕ} (g : Gate) (a b : ℕ) (hins : g.inputs = [a, b])
    (env : List (Sum Bool ℕ)) (k : ℕ)
    (heq : lookup env a = lookup env b) :
    (simGate n g env k).1.isNone = true := by
  cases g with
  | mk op ins =>
    simp only at hins; subst hins
    cases h1 : lookup env a with
    | inl ba =>
      exact simGate_elim_of_left ⟨op, [a, b]⟩ a b rfl env k (Or.inl (by simp [h1]))
    | inr ka =>
      have h2 : lookup env b = Sum.inr ka := heq.symm.trans h1
      cases op <;> simp [simGate, h1, h2]

theorem simGate_out_left_both {n : ℕ} (g : Gate) (a b : ℕ) (hins : g.inputs = [a, b])
    (env : List (Sum Bool ℕ)) (k : ℕ)
    (ha : (lookup env a).isLeft) (hb : (lookup env b).isLeft) :
    ((simGate n g env k).2).isLeft = true := by
  cases g with
  | mk op ins =>
    simp only at hins; subst hins
    cases h1 : lookup env a with
    | inr _ => simp [h1] at ha
    | inl ba =>
      cases h2 : lookup env b with
      | inr _ => simp [h2] at hb
      | inl bb =>
        cases op <;> cases ba <;> cases bb <;> simp [simGate, h1, h2]

theorem simGate_and_false {n : ℕ} (g : Gate) (a b : ℕ) (hop : g.op = GateOp.and)
    (hins : g.inputs = [a, b]) (env : List (Sum Bool ℕ)) (k : ℕ)
    (hf : lookup env a = Sum.inl false ∨ lookup env b = Sum.inl false) :
    (simGate n g env k).2 = Sum.inl false := by
  cases g with
  | mk op ins =>
    simp only at hop hins; subst hop; subst hins
    rcases hf with h1 | h2
    · simp [simGate, h1]
    · cases h1 : lookup env a with
      | inl ba => cases ba <;> simp [simGate, h1, h2]
      | inr ka => simp [simGate, h1, h2]

theorem simGate_or_true {n : ℕ} (g : Gate) (a b : ℕ) (hop : g.op = GateOp.or)
    (hins : g.inputs = [a, b]) (env : List (Sum Bool ℕ)) (k : ℕ)
    (ht : lookup env a = Sum.inl true ∨ lookup env b = Sum.inl true) :
    (simGate n g env k).2 = Sum.inl true := by
  cases g with
  | mk op ins =>
    simp only at hop hins; subst hop; subst hins
    rcases ht with h1 | h2
    · simp [simGate, h1]
    · cases h1 : lookup env a with
      | inl ba => cases ba <;> simp [simGate, h1, h2]
      | inr ka => simp [simGate, h1, h2]

theorem count_true_eq_filter_range (l : List Bool) :
    ((Finset.range l.length).filter (fun p => l.getD p false = true)).card = l.count true := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    have hsplit : (Finset.range (bs.length + 1)).filter (fun p => (b :: bs).getD p false = true) =
        (if b = true then {0} else ∅) ∪
          ((Finset.range bs.length).filter (fun p => bs.getD p false = true)).image (· + 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
      cases x with
      | zero =>
        cases b <;> simp
      | succ k =>
        cases b <;> simp [Nat.succ_lt_succ_iff]
    rw [List.length_cons, hsplit, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.succ.inj h), ih]
      cases b <;> simp [List.count_cons] <;> omega
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_image] at hx2
      obtain ⟨k, _, rfl⟩ := hx2
      cases b <;> simp at hx1

theorem finset_le_count_true (l : List Bool) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p < l.length ∧ l.getD p false = true) : S.card ≤ l.count true := by
  rw [← count_true_eq_filter_range]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨h1, h2⟩ := hS p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, h2⟩

theorem exists_min_circuit {n : ℕ} (f : (Fin n → Bool) → Bool)
    (C : Circuit) (hM : Monotone2 C) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ C0 : Circuit, Monotone2 C0 ∧ C0.size ≤ C.size ∧
      (∀ x : Fin n → Bool, C0.eval (List.ofFn x) = f x) ∧
      (∀ D : Circuit, Monotone2 D → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) → C0.size ≤ D.size) := by
  classical
  have hex : ∃ s, ∃ D : Circuit, Monotone2 D ∧ D.size = s ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x :=
    ⟨C.size, C, hM, rfl, he⟩
  obtain ⟨C0, hM0, hs0, he0⟩ := Nat.find_spec hex
  refine ⟨C0, hM0, ?_, he0, ?_⟩
  · rw [hs0]; exact Nat.find_min' hex ⟨C, hM, rfl, he⟩
  · intro D hMD hDe
    rw [hs0]; exact Nat.find_min' hex ⟨D, hMD, rfl, hDe⟩

theorem min_circuit_props {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hx0 : ∃ x0 : Fin n → Bool, f x0 = false)
    (C0 : Circuit) (hM : Monotone2 C0)
    (he : ∀ x : Fin n → Bool, C0.eval (List.ofFn x) = f x)
    (hmin : ∀ D : Circuit, Monotone2 D → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) → C0.size ≤ D.size) :
    (∀ p (hp : p < C0.gates.length), ∃ a b, C0.gates[p].inputs = [a, b] ∧ a < n + p ∧ b < n + p ∧ a ≠ b) ∧
    (∀ p (hp : p < C0.gates.length), n + p ≠ C0.output →
      ∃ q, ∃ (_ : q < C0.gates.length), p < q ∧ (n + p) ∈ C0.gates[q].inputs) := by
  let ρ0 : Fin n → Option Bool := fun _ => none
  have happly (x : Fin n → Bool) : applyAssign ρ0 x = x := rfl
  obtain ⟨hM', hcnt, _, hlenE, hev', hinit, _⟩ :=
    simplify_spec ρ0 C0 hM (by obtain ⟨x0, hx0⟩ := hx0; exact ⟨x0, by rw [happly, he, hx0]⟩)
  have hle : C0.size ≤ (simplify n ρ0 C0).1.size :=
    hmin _ hM' (fun x => (hev' x).trans (by rw [happly, he]))
  have hzero : (simplify n ρ0 C0).2.2.count true = 0 := by omega
  have hno_elim (p : ℕ) (hp : p < C0.gates.length) : (simplify n ρ0 C0).2.2.getD p false = false := by
    by_contra h
    have ht : (simplify n ρ0 C0).2.2.getD p false = true := by
      cases hval : (simplify n ρ0 C0).2.2.getD p false <;> simp_all
    have hc := finset_le_count_true (simplify n ρ0 C0).2.2 {p} (by
      intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact ⟨by omega, ht⟩)
    simp [hzero] at hc
  have h1 : ∀ p (hp : p < C0.gates.length), ∃ a b, C0.gates[p].inputs = [a, b] ∧ a < n + p ∧ b < n + p ∧ a ≠ b := by
    intro p hp
    obtain ⟨_, helim, hpre, hplen⟩ := simplify_at_gate ρ0 C0 p hp
    set pre := simRun n (C0.gates.take p) [] (initEnv n ρ0) []
    have hnone : (simGate n C0.gates[p] pre.2.1 pre.1.length).1.isNone = false := by
      rw [← helim, hno_elim p hp]
    have hlen2 : C0.gates[p].inputs.length = 2 := by
      by_contra hne2
      exact Bool.noConfusion (hnone.symm.trans (simGate_elim_of_ne_two C0.gates[p] pre.2.1 pre.1.length hne2))
    obtain ⟨a, b, hab⟩ : ∃ a b, C0.gates[p].inputs = [a, b] := by
      rcases h : C0.gates[p].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp [h] at hlen2
      exact ⟨a, b, rfl⟩
    have ha_lt : a < n + p := by
      by_contra hge
      have hla : lookup pre.2.1 a = Sum.inl false := by
        rw [lookup, List.getD_eq_default _ _ (by rw [hplen]; omega)]
      exact Bool.noConfusion (hnone.symm.trans (simGate_elim_of_left C0.gates[p] a b hab pre.2.1 pre.1.length (Or.inl (by simp [hla]))))
    have hb_lt : b < n + p := by
      by_contra hge
      have hlb : lookup pre.2.1 b = Sum.inl false := by
        rw [lookup, List.getD_eq_default _ _ (by rw [hplen]; omega)]
      exact Bool.noConfusion (hnone.symm.trans (simGate_elim_of_left C0.gates[p] a b hab pre.2.1 pre.1.length (Or.inr (by simp [hlb]))))
    have hne : a ≠ b := by
      intro h; subst h
      exact Bool.noConfusion (hnone.symm.trans (simGate_elim_of_eq C0.gates[p] a a hab pre.2.1 pre.1.length rfl))
    exact ⟨a, b, hab, ha_lt, hb_lt, hne⟩
  refine ⟨h1, ?_⟩
  intro p hp hout
  by_contra hno
  push Not at hno
  have hunused : ∀ g ∈ C0.gates.drop (p + 1), ∀ i ∈ g.inputs, i ≠ n + p := by
    intro g hg i hi heq
    rw [List.mem_iff_getElem] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    rw [List.length_drop] at hk
    have hq : p + 1 + k < C0.gates.length := by omega
    rw [List.getElem_drop] at hi
    exact hno (p + 1 + k) hq (by omega) (heq ▸ hi)
  obtain ⟨hMd, hsd, hed⟩ := deleteGate_spec C0 hM p hp hout.symm hunused
  have hle' := hmin (deleteGate n C0 p) hMd (fun x => (hed x).trans (he x))
  omega

theorem wire_read_of_depends {n : ℕ} {es : List (Fin n × Fin n)} (hl : loopless es = true)
    (C0 : Circuit) (he : ∀ x : Fin n → Bool, C0.eval (List.ofFn x) = edgeAny es x)
    {u v : Fin n} (huv : hasEdge es u v = true) :
    C0.output ≠ v.val ∧ ∃ p, ∃ (_ : p < C0.gates.length), v.val ∈ C0.gates[p].inputs := by
  have hout : C0.output ≠ v.val := by
    intro h
    have hv := he (fun i => decide (i = v))
    have h1 : C0.eval (List.ofFn (fun i : Fin n => decide (i = v))) = true := by
      rw [Circuit.eval, h]
      change (wiresFrom C0.gates (List.ofFn (fun i : Fin n => decide (i = v)))).getD v.val false = true
      rw [getD_wiresFrom _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp
    rw [h1, edgeAny_singleton hl v] at hv
    exact Bool.noConfusion hv
  refine ⟨hout, ?_⟩
  by_contra hno
  push Not at hno
  have hnv : ∀ g ∈ C0.gates, v.val ∉ g.inputs := by
    intro g hg
    rw [List.mem_iff_getElem] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    exact hno p hp
  let x1 : Fin n → Bool := fun i => decide (i = u)
  let x2 : Fin n → Bool := fun i => decide (i = u ∨ i = v)
  have heq : C0.eval (List.ofFn x1) = C0.eval (List.ofFn x2) := by
    apply wiresFrom_indep v.val C0.gates (List.ofFn x1) (List.ofFn x2) (by simp) _ hnv C0.output hout
    intro j hj
    by_cases hjn : j < n
    · rw [List.getD_eq_getElem _ _ (by simp [hjn]), List.getD_eq_getElem _ _ (by simp [hjn])]
      simp only [List.getElem_ofFn, x1, x2]
      have hne : (⟨j, hjn⟩ : Fin n) ≠ v := fun h => hj (congrArg Fin.val h)
      simp [hne]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  rw [he x1, he x2, edgeAny_singleton hl u, edgeAny_pair_true huv] at heq
  exact Bool.noConfusion heq

theorem elim_one_edge {n : ℕ} {es : List (Fin n × Fin n)} (hl : loopless es = true)
    {u v : Fin n} (huv : hasEdge es u v = true)
    (C : Circuit) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) :
    1 ≤ C.size := by
  obtain ⟨_, p, hp, _⟩ := wire_read_of_depends hl C he huv
  change 1 ≤ C.gates.length
  omega

theorem elim_leaf {n : ℕ} {es : List (Fin n × Fin n)} (hl : loopless es = true)
    {u v : Fin n} (huv : hasEdge es u v = true)
    (C : Circuit) (hM : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = edgeAny (delV v es) x := by
  obtain ⟨C0, hM0, hle0, he0, hmin0⟩ := exists_min_circuit (edgeAny es) C hM he
  obtain ⟨hred, _⟩ := min_circuit_props ⟨fun _ => false, edgeAny_allFalse es⟩ C0 hM0 he0 hmin0
  obtain ⟨_, p, hp, hvmem⟩ := wire_read_of_depends hl C0 he0 huv
  let ρ : Fin n → Option Bool := fun i => if i = v then some false else none
  have hx0 : ∃ x0 : Fin n → Bool, C0.eval (List.ofFn (applyAssign ρ x0)) = false :=
    ⟨fun _ => false, by rw [he0, edgeAny_delV, edgeAny_allFalse]⟩
  obtain ⟨hM', hcnt, _, hlenE, hev', hinit, _⟩ := simplify_spec ρ C0 hM0 hx0
  obtain ⟨a, b, hab, ha_lt, hb_lt, _⟩ := hred p hp
  obtain ⟨_, helim, hpre, _⟩ := simplify_at_gate ρ C0 p hp
  have hv_init : lookup (simplify n ρ C0).2.1 v.val = Sum.inl false := by
    simpa [ρ] using hinit v.val v.isLt
  have hpelim : (simplify n ρ C0).2.2.getD p false = true := by
    rw [helim]
    apply simGate_elim_of_left C0.gates[p] a b hab _ _
    rw [hab] at hvmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvmem
    rcases hvmem with h1 | h2
    · left; rw [← h1, hpre v.val (by omega), hv_init]; rfl
    · right; rw [← h2, hpre v.val (by omega), hv_init]; rfl
  have hc := finset_le_count_true (simplify n ρ C0).2.2 {p} (by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact ⟨by omega, hpelim⟩)
  simp only [Finset.card_singleton] at hc
  refine ⟨(simplify n ρ C0).1, hM', by omega, fun x => (hev' x).trans (by rw [he0, edgeAny_delV])⟩

theorem elim_edge_two {n : ℕ} {es : List (Fin n × Fin n)} (hl : loopless es = true)
    {u v : Fin n} (huv : hasEdge es u v = true) (hne : delVV u v es ≠ [])
    (C : Circuit) (hM : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size + 2 ≤ C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = edgeAny (delVV u v es) x := by
  obtain ⟨C0, hM0, hle0, he0, hmin0⟩ := exists_min_circuit (edgeAny es) C hM he
  obtain ⟨hred, hlive⟩ := min_circuit_props ⟨fun _ => false, edgeAny_allFalse es⟩ C0 hM0 he0 hmin0
  have hvu : hasEdge es v u = true := by
    simpa [hasEdge, Bool.or_comm] using huv
  obtain ⟨_, pv, hpv, hvmem⟩ := wire_read_of_depends hl C0 he0 huv
  obtain ⟨_, pu, hpu, humem⟩ := wire_read_of_depends hl C0 he0 hvu
  let ρ : Fin n → Option Bool := fun i => if i = u then some false else if i = v then some false else none
  have hx0 : ∃ x0 : Fin n → Bool, C0.eval (List.ofFn (applyAssign ρ x0)) = false :=
    ⟨fun _ => false, by rw [he0, edgeAny_delVV_ff, edgeAny_allFalse]⟩
  obtain ⟨x1, hx1⟩ := edgeAny_nonempty_true hne
  obtain ⟨hM', hcnt, _, hlenE, hev', hinit, hnoConstOut⟩ := simplify_spec ρ C0 hM0 hx0
  have hnoOut : ∀ b, lookup (simplify n ρ C0).2.1 C0.output ≠ Sum.inl b :=
    hnoConstOut x1 (by rw [he0, edgeAny_delVV_ff, hx1])
  have hu_init : lookup (simplify n ρ C0).2.1 u.val = Sum.inl false := by
    simpa [ρ] using hinit u.val u.isLt
  have hv_init : lookup (simplify n ρ C0).2.1 v.val = Sum.inl false := by
    have h := hinit v.val v.isLt
    by_cases hvu' : v = u
    · simpa [ρ, hvu'] using h
    · simpa [ρ, hvu'] using h
  have helim_of_in (p : ℕ) (hp : p < C0.gates.length) (w : ℕ) (hw : w ∈ C0.gates[p].inputs)
      (hleft : (lookup (simplify n ρ C0).2.1 w).isLeft = true) :
      (simplify n ρ C0).2.2.getD p false = true := by
    obtain ⟨a, b, hab, ha_lt, hb_lt, _⟩ := hred p hp
    obtain ⟨_, helim, hpre, _⟩ := simplify_at_gate ρ C0 p hp
    rw [helim]
    apply simGate_elim_of_left C0.gates[p] a b hab _ _
    rw [hab] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · left; rw [hpre _ ha_lt]; exact hleft
    · right; rw [hpre _ hb_lt]; exact hleft
  have hpv_e : (simplify n ρ C0).2.2.getD pv false = true :=
    helim_of_in pv hpv v.val hvmem (by simp [hv_init])
  have hpu_e : (simplify n ρ C0).2.2.getD pu false = true :=
    helim_of_in pu hpu u.val humem (by simp [hu_init])
  have hcount2 : 2 ≤ (simplify n ρ C0).2.2.count true := by
    by_cases hpeq : pv = pu
    · subst hpeq
      obtain ⟨a, b, hab, ha_lt, hb_lt, _⟩ := hred pv hpv
      obtain ⟨hval, _, hpre, _⟩ := simplify_at_gate ρ C0 pv hpv
      have huv_ne : u.val ≠ v.val := by
        intro h
        have h' : u = v := Fin.ext h
        subst h'
        have ht := edgeAny_pair_true huv
        have hf := edgeAny_singleton hl u
        have heq_f : (fun i : Fin n => decide (i = u ∨ i = u)) = (fun i : Fin n => decide (i = u)) := by
          funext i; simp
        rw [heq_f, hf] at ht
        exact Bool.noConfusion ht
      rw [hab] at hvmem humem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvmem humem
      have ha_left : (lookup (simRun n (C0.gates.take pv) [] (initEnv n ρ) []).2.1 a).isLeft = true := by
        rw [hpre a ha_lt]
        rcases hvmem with h1 | h1 <;> rcases humem with h2 | h2
        · exact absurd (h2.trans h1.symm) huv_ne
        · rw [← h1, hv_init]; rfl
        · rw [← h2, hu_init]; rfl
        · exact absurd (h2.trans h1.symm) huv_ne
      have hb_left : (lookup (simRun n (C0.gates.take pv) [] (initEnv n ρ) []).2.1 b).isLeft = true := by
        rw [hpre b hb_lt]
        rcases hvmem with h1 | h1 <;> rcases humem with h2 | h2
        · exact absurd (h2.trans h1.symm) huv_ne
        · rw [← h2, hu_init]; rfl
        · rw [← h1, hv_init]; rfl
        · exact absurd (h2.trans h1.symm) huv_ne
      have hout_left : (lookup (simplify n ρ C0).2.1 (n + pv)).isLeft = true := by
        rw [hval]
        exact simGate_out_left_both C0.gates[pv] a b hab _ _ ha_left hb_left
      have hne_out : n + pv ≠ C0.output := by
        intro h
        rw [h] at hout_left
        cases hco : lookup (simplify n ρ C0).2.1 C0.output with
        | inl b => exact hnoOut b hco
        | inr _ => simp [hco] at hout_left
      obtain ⟨q, hq, hpq, hqmem⟩ := hlive pv hpv hne_out
      have hq_e := helim_of_in q hq (n + pv) hqmem hout_left
      have hc := finset_le_count_true (simplify n ρ C0).2.2 {pv, q} (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ⟨by omega, hpv_e⟩
        · exact ⟨by omega, hq_e⟩)
      rw [Finset.card_pair (by omega)] at hc
      exact hc
    · have hc := finset_le_count_true (simplify n ρ C0).2.2 {pv, pu} (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ⟨by omega, hpv_e⟩
        · exact ⟨by omega, hpu_e⟩)
      rw [Finset.card_pair hpeq] at hc
      exact hc
  refine ⟨(simplify n ρ C0).1, hM', by omega, fun x => (hev' x).trans (by rw [he0, edgeAny_delVV_ff])⟩

theorem elim_leaf_deg2 {n : ℕ} {es : List (Fin n × Fin n)} (hl : loopless es = true)
    {u v w : Fin n} (hwv : w ≠ v) (huv : hasEdge es u v = true) (huw : hasEdge es u w = true)
    (hvw : hasEdge es v w = false) (hleaf : onlyNeighbor es v u = true)
    (hne : delVV u v es ≠ [])
    (C : Circuit) (hM : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size + 3 ≤ C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = edgeAny (delVV u v es) x := by
  obtain ⟨C0, hM0, hle0, he0, hmin0⟩ := exists_min_circuit (edgeAny es) C hM he
  obtain ⟨hred, hlive⟩ := min_circuit_props ⟨fun _ => false, edgeAny_allFalse es⟩ C0 hM0 he0 hmin0
  have hvu : hasEdge es v u = true := by simpa [hasEdge, Bool.or_comm] using huv
  obtain ⟨hout_v, pv0, hpv0, hvmem0⟩ := wire_read_of_depends hl C0 he0 huv
  obtain ⟨hout_u, pu0, hpu0, humem0⟩ := wire_read_of_depends hl C0 he0 hvu
  have huv_ne : u ≠ v := by
    intro h; subst h
    have ht := edgeAny_pair_true huv
    have hf := edgeAny_singleton hl u
    have heq_f : (fun i : Fin n => decide (i = u ∨ i = u)) = (fun i : Fin n => decide (i = u)) := by
      funext i; simp
    rw [heq_f, hf] at ht; exact Bool.noConfusion ht
  have huw_ne : u ≠ w := by
    intro h; subst h
    have ht := edgeAny_pair_true huw
    have hf := edgeAny_singleton hl u
    have heq_f : (fun i : Fin n => decide (i = u ∨ i = u)) = (fun i : Fin n => decide (i = u)) := by
      funext i; simp
    rw [heq_f, hf] at ht; exact Bool.noConfusion ht
  have huv_val_ne : u.val ≠ v.val := fun h => huv_ne (Fin.ext h)
  have hcard3 (l : List Bool) (a b c : ℕ) (ha : a < l.length) (hb : b < l.length) (hc : c < l.length)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ea : l.getD a false = true) (eb : l.getD b false = true) (ec : l.getD c false = true) :
      3 ≤ l.count true := by
    have h := finset_le_count_true l {a, b, c} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨ha, ea⟩
      · exact ⟨hb, eb⟩
      · exact ⟨hc, ec⟩)
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at h
    exact h
  have hstep_from_rho (ρ : Fin n → Option Bool)
      (hρeq : ∀ x, edgeAny es (applyAssign ρ x) = edgeAny (delVV u v es) x) :
      let res := simplify n ρ C0
      Monotone2 res.1 ∧
      res.1.size + res.2.2.count true = C0.size ∧
      res.2.2.length = C0.gates.length ∧
      (∀ x, res.1.eval (List.ofFn x) = edgeAny (delVV u v es) x) ∧
      (∀ p (hp : p < C0.gates.length) (k : ℕ), k ∈ C0.gates[p].inputs →
        (lookup res.2.1 k).isLeft = true → res.2.2.getD p false = true) ∧
      (∀ p (hp : p < C0.gates.length), (lookup res.2.1 (n + p)).isLeft = true →
        ∃ q, ∃ (_ : q < C0.gates.length), p < q ∧ (n + p) ∈ C0.gates[q].inputs ∧ res.2.2.getD q false = true) := by
    have hx0 : ∃ x0, C0.eval (List.ofFn (applyAssign ρ x0)) = false :=
      ⟨fun _ => false, by rw [he0, hρeq, edgeAny_allFalse]⟩
    obtain ⟨x1, hx1⟩ := edgeAny_nonempty_true hne
    obtain ⟨hM', hcnt, _, hlenE, hev', _, hnoConstOut⟩ := simplify_spec ρ C0 hM0 hx0
    have hnoOut : ∀ b, lookup (simplify n ρ C0).2.1 C0.output ≠ Sum.inl b :=
      hnoConstOut x1 (by rw [he0, hρeq, hx1])
    have helim_of_in : ∀ p (hp : p < C0.gates.length) (k : ℕ), k ∈ C0.gates[p].inputs →
        (lookup (simplify n ρ C0).2.1 k).isLeft = true → (simplify n ρ C0).2.2.getD p false = true := by
      intro p hp k hk hleft
      obtain ⟨a, b, hab, ha_lt, hb_lt, _⟩ := hred p hp
      obtain ⟨_, helim, hpre, _⟩ := simplify_at_gate ρ C0 p hp
      rw [helim]
      apply simGate_elim_of_left C0.gates[p] a b hab _ _
      rw [hab] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · left; rw [hpre _ ha_lt]; exact hleft
      · right; rw [hpre _ hb_lt]; exact hleft
    refine ⟨hM', hcnt, hlenE, fun x => (hev' x).trans (by rw [he0, hρeq]), helim_of_in, ?_⟩
    intro p hp hleft
    have hne_out : n + p ≠ C0.output := by
      intro h; rw [h] at hleft
      cases hco : lookup (simplify n ρ C0).2.1 C0.output with
      | inl b => exact hnoOut b hco
      | inr _ => simp [hco] at hleft
    obtain ⟨q, hq, hpq, hqmem⟩ := hlive p hp hne_out
    exact ⟨q, hq, hpq, hqmem, helim_of_in q hq (n + p) hqmem hleft⟩
  by_cases hboth : ∃ p, ∃ (_ : p < C0.gates.length), u.val ∈ C0.gates[p].inputs ∧ v.val ∈ C0.gates[p].inputs
  · obtain ⟨p, hp, hum, hvm⟩ := hboth
    let ρ : Fin n → Option Bool := fun i => if i = u then some false else if i = v then some false else none
    obtain ⟨hM', hcnt, hlenE, hev', helim_in, hnext⟩ :=
      hstep_from_rho ρ (edgeAny_delVV_ff es u v)
    obtain ⟨_, _, _, _, _, hinit, _⟩ :=
      simplify_spec ρ C0 hM0 ⟨fun _ => false, by rw [he0, edgeAny_delVV_ff, edgeAny_allFalse]⟩
    have hu_l : (lookup (simplify n ρ C0).2.1 u.val).isLeft = true := by
      have h := hinit u.val u.isLt; simp [ρ] at h; rw [h]; rfl
    have hv_l : (lookup (simplify n ρ C0).2.1 v.val).isLeft = true := by
      have h := hinit v.val v.isLt; simp [ρ, huv_ne.symm] at h; rw [h]; rfl
    obtain ⟨a, b, hab, ha_lt, hb_lt, _⟩ := hred p hp
    obtain ⟨hval, _, hpre, _⟩ := simplify_at_gate ρ C0 p hp
    have hab_uv : (a = u.val ∧ b = v.val) ∨ (a = v.val ∧ b = u.val) := by
      rw [hab] at hum hvm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hum hvm
      rcases hum with h1 | h1 <;> rcases hvm with h2 | h2
      · exact absurd (h1.trans h2.symm) huv_val_ne
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
      · exact absurd (h1.trans h2.symm) huv_val_ne
    have hp_left : (lookup (simplify n ρ C0).2.1 (n + p)).isLeft = true := by
      rw [hval]
      apply simGate_out_left_both C0.gates[p] a b hab _ _
      · rw [hpre a ha_lt]; rcases hab_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      · rw [hpre b hb_lt]; rcases hab_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hp_e := helim_in p hp u.val hum hu_l
    obtain ⟨q, hq, hpq, hqmem, hq_e⟩ := hnext p hp hp_left
    have hcnt3 : 3 ≤ (simplify n ρ C0).2.2.count true := by
      by_cases hother : ∃ r, ∃ (_ : r < C0.gates.length), r ≠ p ∧ r ≠ q ∧
          (simplify n ρ C0).2.2.getD r false = true
      · obtain ⟨r, hr, hrp, hrq, hr_e⟩ := hother
        exact hcard3 _ p q r (by omega) (by omega) (by omega) (by omega) hrp.symm hrq.symm hp_e hq_e hr_e
      · push Not at hother
        have hq_no_uv : u.val ∉ C0.gates[q].inputs ∧ v.val ∉ C0.gates[q].inputs := by
          constructor <;> intro hmem
          · obtain ⟨qa, qb, qab, qa_lt, qb_lt, _⟩ := hred q hq
            obtain ⟨qval, _, qpre, _⟩ := simplify_at_gate ρ C0 q hq
            have hne_uq : u.val ≠ n + p := by omega
            rw [qab] at hqmem hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hqmem hmem
            have hqa_l : (lookup (simRun n (C0.gates.take q) [] (initEnv n ρ) []).2.1 qa).isLeft = true := by
              rw [qpre qa qa_lt]
              rcases hmem with h1 | h1 <;> rcases hqmem with h2 | h2
              · exact absurd (h1.trans h2.symm) hne_uq
              · rw [← h1]; exact hu_l
              · rw [← h2]; exact hp_left
              · exact absurd (h1.trans h2.symm) hne_uq
            have hqb_l : (lookup (simRun n (C0.gates.take q) [] (initEnv n ρ) []).2.1 qb).isLeft = true := by
              rw [qpre qb qb_lt]
              rcases hmem with h1 | h1 <;> rcases hqmem with h2 | h2
              · exact absurd (h1.trans h2.symm) hne_uq
              · rw [← h2]; exact hp_left
              · rw [← h1]; exact hu_l
              · exact absurd (h1.trans h2.symm) hne_uq
            have hq_left : (lookup (simplify n ρ C0).2.1 (n + q)).isLeft = true := by
              rw [qval]; exact simGate_out_left_both C0.gates[q] qa qb qab _ _ hqa_l hqb_l
            obtain ⟨r, hr, hqr, _, hr_e⟩ := hnext q hq hq_left
            exact hother r hr (by omega) (by omega) hr_e
          · obtain ⟨qa, qb, qab, qa_lt, qb_lt, _⟩ := hred q hq
            obtain ⟨qval, _, qpre, _⟩ := simplify_at_gate ρ C0 q hq
            have hne_vq : v.val ≠ n + p := by omega
            rw [qab] at hqmem hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hqmem hmem
            have hqa_l : (lookup (simRun n (C0.gates.take q) [] (initEnv n ρ) []).2.1 qa).isLeft = true := by
              rw [qpre qa qa_lt]
              rcases hmem with h1 | h1 <;> rcases hqmem with h2 | h2
              · exact absurd (h1.trans h2.symm) hne_vq
              · rw [← h1]; exact hv_l
              · rw [← h2]; exact hp_left
              · exact absurd (h1.trans h2.symm) hne_vq
            have hqb_l : (lookup (simRun n (C0.gates.take q) [] (initEnv n ρ) []).2.1 qb).isLeft = true := by
              rw [qpre qb qb_lt]
              rcases hmem with h1 | h1 <;> rcases hqmem with h2 | h2
              · exact absurd (h1.trans h2.symm) hne_vq
              · rw [← h2]; exact hp_left
              · rw [← h1]; exact hv_l
              · exact absurd (h1.trans h2.symm) hne_vq
            have hq_left : (lookup (simplify n ρ C0).2.1 (n + q)).isLeft = true := by
              rw [qval]; exact simGate_out_left_both C0.gates[q] qa qb qab _ _ hqa_l hqb_l
            obtain ⟨r, hr, hqr, _, hr_e⟩ := hnext q hq hq_left
            exact hother r hr (by omega) (by omega) hr_e
        have hall_gates : ∀ g ∈ C0.gates, (u.val ∉ g.inputs ∧ v.val ∉ g.inputs) ∨
            (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val])) := by
          intro g hg
          rw [List.mem_iff_getElem] at hg
          obtain ⟨r, hr, rfl⟩ := hg
          by_cases hrp : r = p
          · subst hrp
            right
            refine ⟨(hM0 _ (List.getElem_mem hr)).1, ?_⟩
            rcases hab_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl hab
            · exact Or.inr hab
          · by_cases hrq : r = q
            · subst hrq; exact Or.inl hq_no_uv
            · left
              exact ⟨fun hm => hother r hr hrp hrq (helim_in r hr u.val hm hu_l),
                     fun hm => hother r hr hrp hrq (helim_in r hr v.val hm hv_l)⟩
        let x1 : Fin n → Bool := fun i => decide (i = u ∨ i = w)
        let x2 : Fin n → Bool := fun i => decide (i = v ∨ i = w)
        have hswap : C0.eval (List.ofFn x1) = C0.eval (List.ofFn x2) := by
          apply wiresFrom_swap_uv u.val v.val C0.gates (List.ofFn x1) (List.ofFn x2)
            (by simp) (by simp) (by simp)
            (by rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]; simp [x1, x2])
            (by rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]; simp [x1, x2, huv_ne, huv_ne.symm, huw_ne, hwv.symm])
            _ hall_gates C0.output hout_u hout_v
          intro j hju hjv
          by_cases hjn : j < n
          · rw [List.getD_eq_getElem _ _ (by simp [hjn]), List.getD_eq_getElem _ _ (by simp [hjn])]
            simp only [List.getElem_ofFn, x1, x2]
            have h1 : (⟨j, hjn⟩ : Fin n) ≠ u := fun h => hju (congrArg Fin.val h)
            have h2 : (⟨j, hjn⟩ : Fin n) ≠ v := fun h => hjv (congrArg Fin.val h)
            simp [h1, h2]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        rw [he0 x1, he0 x2, edgeAny_pair_true huw, edgeAny_pair_false hl hvw] at hswap
        exact Bool.noConfusion hswap
    refine ⟨(simplify n ρ C0).1, hM', by omega, hev'⟩
  · push Not at hboth
    have hpu_ne_pv : pv0 ≠ pu0 := fun h => hboth pu0 hpu0 humem0 (h ▸ hvmem0)
    have finish_branch (ρ : Fin n → Option Bool) (hρu : ρ u = some false) (bv : Bool)
        (hρv : ρ v = some bv) (hρeq : ∀ x, edgeAny es (applyAssign ρ x) = edgeAny (delVV u v es) x)
        (hpv_left : (lookup (simplify n ρ C0).2.1 (n + pv0)).isLeft = true) :
        ∃ C' : Circuit, Monotone2 C' ∧ C'.size + 3 ≤ C.size ∧
          ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = edgeAny (delVV u v es) x := by
      obtain ⟨hM', hcnt, hlenE, hev', helim_in, hnext⟩ :=
        hstep_from_rho ρ hρeq
      obtain ⟨_, _, _, _, _, hinit, _⟩ :=
        simplify_spec ρ C0 hM0 ⟨fun _ => false, by rw [he0, hρeq, edgeAny_allFalse]⟩
      have hu_l : (lookup (simplify n ρ C0).2.1 u.val).isLeft = true := by
        have h := hinit u.val u.isLt; simp [hρu] at h; rw [h]; rfl
      have hv_l : (lookup (simplify n ρ C0).2.1 v.val).isLeft = true := by
        have h := hinit v.val v.isLt; simp [hρv] at h; rw [h]; rfl
      have hpv_e := helim_in pv0 hpv0 v.val hvmem0 hv_l
      have hpu_e := helim_in pu0 hpu0 u.val humem0 hu_l
      obtain ⟨q, hq, hpq, hqmem, hq_e⟩ := hnext pv0 hpv0 hpv_left
      have hcnt3 : 3 ≤ (simplify n ρ C0).2.2.count true := by
        by_cases hqu : q = pu0
        · subst hqu
          obtain ⟨a, b, hab, ha_lt, hb_lt, _⟩ := hred q hq
          obtain ⟨hval, _, hpre, _⟩ := simplify_at_gate ρ C0 q hq
          have hne_uq : u.val ≠ n + pv0 := by omega
          rw [hab] at humem0 hqmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at humem0 hqmem
          have ha_l : (lookup (simRun n (C0.gates.take q) [] (initEnv n ρ) []).2.1 a).isLeft = true := by
            rw [hpre a ha_lt]
            rcases humem0 with h1 | h1 <;> rcases hqmem with h2 | h2
            · exact absurd (h1.trans h2.symm) hne_uq
            · rw [← h1]; exact hu_l
            · rw [← h2]; exact hpv_left
            · exact absurd (h1.trans h2.symm) hne_uq
          have hb_l : (lookup (simRun n (C0.gates.take q) [] (initEnv n ρ) []).2.1 b).isLeft = true := by
            rw [hpre b hb_lt]
            rcases humem0 with h1 | h1 <;> rcases hqmem with h2 | h2
            · exact absurd (h1.trans h2.symm) hne_uq
            · rw [← h2]; exact hpv_left
            · rw [← h1]; exact hu_l
            · exact absurd (h1.trans h2.symm) hne_uq
          have hq_left : (lookup (simplify n ρ C0).2.1 (n + q)).isLeft = true := by
            rw [hval]; exact simGate_out_left_both C0.gates[q] a b hab _ _ ha_l hb_l
          obtain ⟨r, hr, hqr, _, hr_e⟩ := hnext q hq hq_left
          exact hcard3 _ pv0 q r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hpv_e hq_e hr_e
        · exact hcard3 _ pv0 pu0 q (by omega) (by omega) (by omega) hpu_ne_pv (by omega) (Ne.symm hqu) hpv_e hpu_e hq_e
      exact ⟨(simplify n ρ C0).1, hM', by omega, hev'⟩
    obtain ⟨hop, _⟩ := hM0 C0.gates[pv0] (List.getElem_mem hpv0)
    change C0.gates[pv0].op = GateOp.and ∨ C0.gates[pv0].op = GateOp.or at hop
    obtain ⟨a, b, hab, ha_lt, hb_lt, _⟩ := hred pv0 hpv0
    rcases hop with hop | hop
    · let ρ : Fin n → Option Bool := fun i => if i = u then some false else if i = v then some false else none
      obtain ⟨hval, _, hpre, _⟩ := simplify_at_gate ρ C0 pv0 hpv0
      obtain ⟨_, _, _, _, _, hinit, _⟩ :=
        simplify_spec ρ C0 hM0 ⟨fun _ => false, by rw [he0, edgeAny_delVV_ff, edgeAny_allFalse]⟩
      have hv_val : lookup (simplify n ρ C0).2.1 v.val = Sum.inl false := by
        simpa [ρ, huv_ne.symm] using hinit v.val v.isLt
      have hpv_left : (lookup (simplify n ρ C0).2.1 (n + pv0)).isLeft = true := by
        rw [hval]
        have hf : lookup (simRun n (C0.gates.take pv0) [] (initEnv n ρ) []).2.1 a = Sum.inl false ∨
            lookup (simRun n (C0.gates.take pv0) [] (initEnv n ρ) []).2.1 b = Sum.inl false := by
          rw [hab] at hvmem0
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hvmem0
          rcases hvmem0 with h1 | h1
          · left; rw [hpre a ha_lt, ← h1, hv_val]
          · right; rw [hpre b hb_lt, ← h1, hv_val]
        rw [simGate_and_false C0.gates[pv0] a b hop hab _ _ hf]; rfl
      exact finish_branch ρ (by simp [ρ]) false (by simp [ρ, huv_ne.symm]) (edgeAny_delVV_ff es u v) hpv_left
    · let ρ : Fin n → Option Bool := fun i => if i = u then some false else if i = v then some true else none
      obtain ⟨hval, _, hpre, _⟩ := simplify_at_gate ρ C0 pv0 hpv0
      obtain ⟨_, _, _, _, _, hinit, _⟩ :=
        simplify_spec ρ C0 hM0 ⟨fun _ => false, by rw [he0, edgeAny_delVV_ft hleaf, edgeAny_allFalse]⟩
      have hv_val : lookup (simplify n ρ C0).2.1 v.val = Sum.inl true := by
        simpa [ρ, huv_ne.symm] using hinit v.val v.isLt
      have hpv_left : (lookup (simplify n ρ C0).2.1 (n + pv0)).isLeft = true := by
        rw [hval]
        have ht : lookup (simRun n (C0.gates.take pv0) [] (initEnv n ρ) []).2.1 a = Sum.inl true ∨
            lookup (simRun n (C0.gates.take pv0) [] (initEnv n ρ) []).2.1 b = Sum.inl true := by
          rw [hab] at hvmem0
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hvmem0
          rcases hvmem0 with h1 | h1
          · left; rw [hpre a ha_lt, ← h1, hv_val]
          · right; rw [hpre b hb_lt, ← h1, hv_val]
        rw [simGate_or_true C0.gates[pv0] a b hop hab _ _ ht]; rfl
      exact finish_branch ρ (by simp [ρ]) true (by simp [ρ, huv_ne.symm]) (edgeAny_delVV_ft hleaf) hpv_left

-- Live-wire search engine parameterized by pair count p

def build {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {available : Finset α} (h : build ops goal k available) :
    ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {s : Finset α} (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    (D : α → Prop) (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : ℕ} {s : Finset α} (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

abbrev W (p : ℕ) := BitVec (p + p)

def bvOps (p : ℕ) (x y : W p) : List (W p) := [x &&& y, x ||| y]

def sep (p : ℕ) (x : W p) : BitVec p := ((x >>> p) &&& ~~~x).setWidth p

def cuts (p : ℕ) (ws : List (W p)) : BitVec p := ws.foldr (fun w v => sep p w ||| v) 0

def goal (p : ℕ) : W p := BitVec.allOnes p ++ (0 : BitVec p)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (p : ℕ) (a b : W p) : Finset (W p) := (bvOps p a b).toFinset

def differs (p : ℕ) (i : Fin p) (w : W p) : Prop :=
  w.getLsbD (p + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (p : ℕ) (i : Fin p) (a b z : W p) (hz : z ∈ basicOps p a b)
    (hd : differs p i z) : differs p i a ∨ differs p i b := by
  simp only [basicOps, bvOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (p + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (p + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs (p : ℕ) (i : Fin p) : differs p i (goal p) := by
  unfold differs goal
  constructor
  · rw [BitVec.getLsbD_append]
    have h1 : ¬ (p + i.val < p) := by omega
    simp [h1, i.isLt]
  · rw [BitVec.getLsbD_append]
    simp [i.isLt]

theorem goal_ne_zero {p : ℕ} (hp : 0 < p) : goal p ≠ 0 := by
  intro h
  have hd := (goal_differs p ⟨0, hp⟩).1
  rw [h] at hd
  simp at hd

theorem goal_ne_allOnes {p : ℕ} (hp : 0 < p) : goal p ≠ BitVec.allOnes (p + p) := by
  intro h
  have hd := (goal_differs p ⟨0, hp⟩).2
  rw [h, BitVec.getLsbD_allOnes] at hd
  have hlt : 0 < p + p := by omega
  simp [hlt] at hd

theorem cuts_spec (p : ℕ) (ws : List (W p)) (i : Fin p) :
    (cuts p ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs p i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep p a ||| cuts p rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < p + p := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {p k : ℕ} {ws : List (W p)} (h : live (basicOps p) (goal p) k ws.toFinset) :
    cuts p ws = BitVec.allOnes p := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs p ⟨j, hj⟩) (goal_differs p ⟨j, hj⟩) (ops_differs p ⟨j, hj⟩) h
  have hbit := (cuts_spec p ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (p : ℕ) (a b : W p) : basicOps p a b = basicOps p b a := by
  ext z
  simp [basicOps, bvOps, BitVec.and_comm, BitVec.or_comm]

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) :=
  [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {α : Type} [DecidableEq α] {g : α} {ws : List α}
    (hn : ws.Nodup) (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def possible (p : ℕ) (w : List (W p)) (z : W p) : Bool :=
  z == 0 || z == BitVec.allOnes (p + p) || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

def bvBit (p : ℕ) (k : Fin (p + p)) (z : W p) : Bool := z[k.val]

theorem read_bit (p : ℕ) (w : List (W p)) (i : ℕ) (k : Fin (p + p)) :
    (w.map (bvBit p k)).getD i false = bvBit p k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bvBit]

theorem read_wire (p : ℕ) (w : List (W p)) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem bvAtom {p : ℕ} {ws : List (W p)} {x : W p} (hx : x = 0 ∨ x ∈ ws) : possible p ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

theorem bvPair {p : ℕ} {ws : List (W p)} {x y : W p}
    (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible p ws (x &&& y) ∧ possible p ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using bvAtom hy
  rcases hy with rfl | hy
  · simpa [possible] using bvAtom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

def bvStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def bvLegal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem gate_table (p : ℕ) (w ws : List (W p)) (hw : w ⊆ ws) (g : Gate) (hg : bvLegal g) :
    ∃ z, possible p ws z ∧ ∀ k, bvStep (w.map (bvBit p k)) g = (w ++ [z]).map (bvBit p k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire p w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes (p + p), by simp [possible],
        by intro k; simp [bvStep, GateOp.eval, bvBit]⟩
    · exact ⟨0, by simp [possible], by intro k; simp [bvStep, GateOp.eval, bvBit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, bvAtom (mem i),
          by intro k; simp only [bvStep, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, bvAtom (mem i),
          by intro k; simp only [bvStep, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (bvPair (mem i) (mem j)).1,
            by intro k; simp only [bvStep, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bvBit]⟩
        · exact ⟨_, (bvPair (mem i) (mem j)).2,
            by intro k; simp only [bvStep, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bvBit]⟩

def represents (p : ℕ) (available : Finset (W p)) (w : List (W p)) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes (p + p) ∨ u ∈ available

theorem classify {p : ℕ} {available : Finset (W p)} {ws : List (W p)} (hw : represents p available ws)
    {z : W p} (hz : possible p ws z) :
    z = 0 ∨ z = BitVec.allOnes (p + p) ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps p a b := by
  have lift {t : W p} (h : t = 0 ∨ t = BitVec.allOnes (p + p) ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes (p + p) ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps p a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, bvOps]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W p) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W p) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, bvOps]⟩))

theorem compile {p : ℕ} (hp : 0 < p) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, bvLegal g)
    (w : List (W p)) (av : Finset (W p)) (hw : represents p av w)
    (he : ∀ k, (gs.foldl bvStep (w.map (bvBit p k))).getD out false = bvBit p k (goal p)) :
    build (basicOps p) (goal p) gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal p := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bvBit] using he ⟨i, hi⟩
    have hr := read_wire p w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim (goal_ne_zero hp hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim (goal_ne_zero hp h)
      · exact False.elim (goal_ne_allOnes hp h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table p w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl bvStep ((w ++ [z]).map (bvBit p k))).getD out false = bvBit p k (goal p) := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes (p + p) ∨ z ∈ av) : represents p av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · exact (List.mem_singleton.mp fresh) ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

theorem extend_live {p m n : ℕ} {s : Finset (W p)} (le : m ≤ n)
    (h : live (basicOps p) (goal p) m s) : live (basicOps p) (goal p) n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

def dispatch (p : ℕ) (extra : ℕ) (next : ℕ → List (W p) → Bool) (a b : W p) (r : List (W p)) : Bool :=
  let base := cuts p r
  let full := BitVec.allOnes p
  (bvOps p a b).any fun w =>
    !(w == a || w == b || r.contains w) &&
    (let v := sep p w ||| base
     ((v == full) && next extra (w :: r)) ||
     ((extra != 0) && (((v ||| sep p a == full) && next (extra - 1) (w :: a :: r)) ||
                        ((v ||| sep p b == full) && next (extra - 1) (w :: b :: r)))) ||
     ((extra ≥ 2) && (v ||| sep p a ||| sep p b == full) && next (extra - 2) (w :: a :: b :: r)))

def optimized (p : ℕ) : ℕ → ℕ → List (W p) → Bool
  | 0, _, ws => ws == [goal p]
  | k + 1, extra, ws => ws == [goal p] ||
    (pairs ws).any (fun (a, b, r) => dispatch p extra (optimized p k) a b r)

theorem dispatch_complete {p k extra : ℕ} {a b z : W p} {r kept : List (W p)}
    (next : ℕ → List (W p) → Bool)
    (hz : z ∈ basicOps p a b) (hz_ne_a : z ≠ a) (hz_ne_b : z ≠ b) (hz_nr : z ∉ r)
    (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts p (z :: kept) = BitVec.allOnes p) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch p extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨by simp [hz_ne_a, hz_ne_b, hz_nr], ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega,
      .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega,
      .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (p n : ℕ) (ws : List (W p)) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live (basicOps p) (goal p) n ws.toFinset) :
    optimized p n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W p} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps p a b) :
          dispatch p extra (optimized p k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hz_not_perm : z ∉ a :: b :: r := fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm))
        simp only [List.mem_cons, not_or] at hz_not_perm
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live (basicOps p) (goal p) k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (p := p) (k := k) (extra := extra) (optimized p k)
          hop hz_not_perm.1 hz_not_perm.2.1 hz_not_perm.2.2 hk
          (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap p a b ▸ hz)⟩

def embedOK {n m : ℕ} (inv : Fin n → Option (Fin m))
    (es : List (Fin n × Fin n)) (coreEs : List (Fin m × Fin m)) : Bool :=
  es.all (fun e => match inv e.1, inv e.2 with
    | some i, some j => hasEdge coreEs i j
    | _, _ => false) &&
  coreEs.all (fun c => es.any (fun e => match inv e.1, inv e.2 with
    | some i, some j => (i == c.1 && j == c.2) || (i == c.2 && j == c.1)
    | _, _ => false))

def liftAssign {n m : ℕ} (inv : Fin n → Option (Fin m)) (y : Fin m → Bool) : Fin n → Bool :=
  fun j => match inv j with | some i => y i | none => false

theorem edgeAny_embed {n m : ℕ} {inv : Fin n → Option (Fin m)}
    {es : List (Fin n × Fin n)} {coreEs : List (Fin m × Fin m)}
    (hok : embedOK inv es coreEs = true) (y : Fin m → Bool) :
    edgeAny es (liftAssign inv y) = edgeAny coreEs y := by
  simp only [embedOK, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨h1, h2⟩ := hok
  apply Bool.eq_iff_iff.mpr
  simp only [edgeAny, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨e, he, h1e, h2e⟩
    have hm := h1 e he
    simp only [liftAssign] at h1e h2e
    cases hi : inv e.1 with
    | none => simp [hi] at h1e
    | some i =>
      cases hj : inv e.2 with
      | none => simp [hj] at h2e
      | some j =>
        simp [hi] at h1e; simp [hj] at h2e; simp [hi, hj] at hm
        simp only [hasEdge, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
        obtain ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hm
        · exact ⟨c, hc, h1e, h2e⟩
        · exact ⟨c, hc, h2e, h1e⟩
  · rintro ⟨c, hc, hc1, hc2⟩
    have hm := h2 c hc
    simp only [List.any_eq_true] at hm
    obtain ⟨e, he, hme⟩ := hm
    cases hi : inv e.1 with
    | none => simp [hi] at hme
    | some i =>
      cases hj : inv e.2 with
      | none => simp [hi, hj] at hme
      | some j =>
        simp only [hi, hj, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hme
        refine ⟨e, he, ?_⟩
        rcases hme with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [liftAssign, hi, hj, hc1, hc2]
        · simp [liftAssign, hi, hj, hc1, hc2]

theorem core_lower {n m p : ℕ} (hp : 0 < p) (k extra : ℕ)
    (coreInputs : List (W p)) (coreEs : List (Fin m × Fin m)) (sites : List (Fin p))
    (hnd : coreInputs.Nodup)
    (hroom : extra + coreInputs.length = k + 1)
    (hnec : coreInputs.all (fun a => sites.any (fun i => coreInputs.all (fun b =>
      !(b.getLsbD (p + i.val) && !b.getLsbD i.val) || b == a))) = true)
    (hrows : ∀ r : Fin (p + p),
      edgeAny coreEs (fun i : Fin m => bvBit p r (coreInputs.getD i.val 0)) = bvBit p r (goal p))
    (hsearch : optimized p k extra coreInputs = false)
    (inv : Fin n → Option (Fin m)) (es : List (Fin n × Fin n))
    (hembed : embedOK inv es coreEs = true)
    (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) :
    k + 1 ≤ C.size := by
  by_contra hlt
  have hs : C.gates.length ≤ k := by change ¬ (k + 1 ≤ C.gates.length) at hlt; omega
  let w0 : List (W p) := List.ofFn (fun j : Fin n =>
    match inv j with | some i => coreInputs.getD i.val 0 | none => 0)
  have hrep : represents p coreInputs.toFinset w0 := by
    intro u hu
    simp only [w0, List.mem_ofFn] at hu
    obtain ⟨j, rfl⟩ := hu
    cases inv j with
    | none => exact Or.inl rfl
    | some i =>
      rcases read_wire p coreInputs i.val with h0 | hmem
      · exact Or.inl h0
      · exact Or.inr (Or.inr (List.mem_toFinset.mpr hmem))
  have hmap (r : Fin (p + p)) :
      w0.map (bvBit p r) = List.ofFn (liftAssign inv (fun i : Fin m => bvBit p r (coreInputs.getD i.val 0))) := by
    simp only [w0, List.map_ofFn]
    congr 1; funext j
    dsimp only [Function.comp, liftAssign]
    cases inv j with
    | none => simp [bvBit]
    | some i => rfl
  have heval (r : Fin (p + p)) :
      (C.gates.foldl bvStep (w0.map (bvBit p r))).getD C.output false = bvBit p r (goal p) := by
    rw [hmap r]
    change C.eval (List.ofFn (liftAssign inv (fun i : Fin m => bvBit p r (coreInputs.getD i.val 0)))) = _
    rw [he, edgeAny_embed hembed, hrows r]
  have hb : build (basicOps p) (goal p) C.gates.length coreInputs.toFinset :=
    compile hp C.gates C.output hm w0 coreInputs.toFinset hrep heval
  obtain ⟨S, hsub, hLive⟩ := compress hb
  have hfull : S = coreInputs.toFinset := by
    apply Finset.Subset.antisymm hsub
    intro a ha
    obtain ⟨i, _, hAll⟩ :=
      List.any_eq_true.mp (List.all_eq_true.mp hnec a (List.mem_toFinset.mp ha))
    have hi (b : W p) (hb' : b ∈ coreInputs) (hd : differs p i b) : b = a := by
      have hrow := List.all_eq_true.mp hAll b hb'
      obtain ⟨h1, h2⟩ := hd
      rw [h1, h2] at hrow
      simpa using hrow
    obtain ⟨b, hb', hd⟩ := live_separates (differs p i) (goal_differs p i) (ops_differs p i) hLive
    exact hi b (List.mem_toFinset.mp (hsub hb')) hd ▸ hb'
  have hLiveFull : live (basicOps p) (goal p) k coreInputs.toFinset :=
    extend_live hs (hfull ▸ hLive)
  have hfound := optimized_complete p k coreInputs extra hnd hroom hLiveFull
  exact Bool.noConfusion (hsearch.symm.trans hfound)

-- The 7 irreducible cores

def edgesK3 : List (Fin 3 × Fin 3) := [(0, 1), (0, 2), (1, 2)]
def inputsK3 : List (W 9) := [0x7f24, 0x38e92, 0x3f049]
def sitesK3 : List (Fin 9) := [1, 2, 5]

theorem frontK3 : optimized 9 3 1 inputsK3 = false := by decide +kernel

theorem coreK3 {n : ℕ} (inv : Fin n → Option (Fin 3)) (es : List (Fin n × Fin n))
    (hembed : embedOK inv es edgesK3 = true)
    (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) : 4 ≤ C.size :=
  core_lower (by decide) 3 1 inputsK3 edgesK3 sitesK3 (by decide) (by decide) (by decide)
    (by decide +kernel) frontK3 inv es hembed C hm he

def edgesC5 : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]
def inputsC5 : List (W 25) :=
  [0x7ff8c6318, 0xf83e6318c6, 0x1f07c05294a5, 0x3e0f80118c631, 0x3ff0000a5294a]
def sitesC5 : List (Fin 25) := [1, 3, 8, 11, 15]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem frontC5 : optimized 25 6 2 inputsC5 = false := by decide +kernel

theorem coreC5 {n : ℕ} (inv : Fin n → Option (Fin 5)) (es : List (Fin n × Fin n))
    (hembed : embedOK inv es edgesC5 = true)
    (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) : 7 ≤ C.size :=
  core_lower (by decide) 6 2 inputsC5 edgesC5 sitesC5 (by decide) (by decide) (by decide)
    (by decide +kernel) frontC5 inv es hembed C hm he

def edgesBowtie : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]
def inputsBowtie : List (W 30) :=
  [0x3ffffe1084210, 0x7c0007d8c6318c, 0x7c00f806318c63, 0xf801f0014a5294a, 0xf83e0000a5294a5]
def sitesBowtie : List (Fin 30) := [2, 4, 9, 14, 19]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontBowtie : optimized 30 7 3 inputsBowtie = false := by decide +kernel

theorem coreBowtie {n : ℕ} (inv : Fin n → Option (Fin 5)) (es : List (Fin n × Fin n))
    (hembed : embedOK inv es edgesBowtie = true)
    (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) : 8 ≤ C.size :=
  core_lower (by decide) 7 3 inputsBowtie edgesBowtie sitesBowtie (by decide) (by decide) (by decide)
    (by decide +kernel) frontBowtie inv es hembed C hm he

def edgesNet : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)]
def inputsNet : List (W 24) :=
  [0xfff888888, 0xff00f444444, 0xf0f0f0222222, 0xf00777777, 0xf0000bbbbbb, 0xf00000dddddd]
def sitesNet : List (Fin 24) := [2, 3, 7, 11, 18, 21]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontNet : optimized 24 7 2 inputsNet = false := by decide +kernel

theorem coreNet {n : ℕ} (inv : Fin n → Option (Fin 6)) (es : List (Fin n × Fin n))
    (hembed : embedOK inv es edgesNet = true)
    (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) : 8 ≤ C.size :=
  core_lower (by decide) 7 2 inputsNet edgesNet sitesNet (by decide) (by decide) (by decide)
    (by decide +kernel) frontNet inv es hembed C hm he

def edgesC6 : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 5)]
def inputsC6 : List (W 30) :=
  [0xfff18c6318, 0x1f07cc6318c6, 0x3e0f80a5294a5, 0x7c1f002318c631, 0xf83e00025294a52, 0xffc000018c6318c]
def sitesC6 : List (Fin 30) := [1, 3, 8, 11, 15, 20]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem frontC6 : optimized 30 7 2 inputsC6 = false := by decide +kernel

theorem coreC6 {n : ℕ} (inv : Fin n → Option (Fin 6)) (es : List (Fin n × Fin n))
    (hembed : embedOK inv es edgesC6 = true)
    (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) : 8 ≤ C.size :=
  core_lower (by decide) 7 2 inputsC6 edgesC6 sitesC6 (by decide) (by decide) (by decide)
    (by decide +kernel) frontC6 inv es hembed C hm he

def edgesCoreC : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]
def inputsCoreC : List (W 42) :=
  [0xfffff0c30c30c30, 0xfff000fcc30c30c30c, 0x3f03f0030c30c30c3, 0x3f000fc000a28a28a28a, 0xfc0fc00000228a28a28a2, 0xfff000000015555555555]
def sitesCoreC : List (Fin 42) := [2, 4, 10, 16, 26, 31]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontCoreC : optimized 42 8 3 inputsCoreC = false := by decide +kernel

theorem coreCoreC {n : ℕ} (inv : Fin n → Option (Fin 6)) (es : List (Fin n × Fin n))
    (hembed : embedOK inv es edgesCoreC = true)
    (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) : 9 ≤ C.size :=
  core_lower (by decide) 8 3 inputsCoreC edgesCoreC sitesCoreC (by decide) (by decide) (by decide)
    (by decide +kernel) frontCoreC inv es hembed C hm he

def edges2K3 : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]
def inputs2K3 : List (W 54) :=
  [0xfffff81c0e070381c0, 0x1ff007fc70381c0e07038, 0x1ffff8000e070381c0e07, 0x7fffe00000024924924924924, 0xff803fe00000012492492492492, 0xffffc0000000009249249249249]
def sites2K3 : List (Fin 54) := [3, 6, 15, 28, 29, 38]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem front2K3 : optimized 54 8 3 inputs2K3 = false := by decide +kernel

theorem core2K3 {n : ℕ} (inv : Fin n → Option (Fin 6)) (es : List (Fin n × Fin n))
    (hembed : embedOK inv es edges2K3 = true)
    (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeAny es x) : 9 ≤ C.size :=
  core_lower (by decide) 8 3 inputs2K3 edges2K3 sites2K3 (by decide) (by decide) (by decide)
    (by decide +kernel) front2K3 inv es hembed C hm he


theorem g1 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = (fun x : Fin 2 → Bool => (x 0 && x 1)) x) → 1 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 2 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1)] : List (Fin 2 × Fin 2)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1)] : List (Fin 2 × Fin 2)))
  have hbase := elim_one_edge (u := 0) (v := 1) (by decide) (by decide) C0 h0
  omega

theorem g2 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) x) → 2 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 3 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2)] : List (Fin 3 × Fin 3)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2)] : List (Fin 3 × Fin 3)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  have hbase := elim_one_edge (u := 0) (v := 2) (by decide) (by decide) C1 h1
  omega

theorem g3 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) x) → 4 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 3 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)))
  have hbase := coreK3 (fun j : Fin 3 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩) _ (by decide) C0 hM0 h0
  omega

theorem g4 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) x) → 3 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 4 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (2, 3)] : List (Fin 4 × Fin 4)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (2, 3)] : List (Fin 4 × Fin 4)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_edge_two (u := 0) (v := 1) (by decide) (by decide) (by decide) C0 hM0 h0
  have hbase := elim_one_edge (u := 2) (v := 3) (by decide) (by decide) C1 h1
  omega

theorem g5 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) x) → 3 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 4 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3)] : List (Fin 4 × Fin 4)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3)] : List (Fin 4 × Fin 4)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C1 hM1 h1
  have hbase := elim_one_edge (u := 0) (v := 3) (by decide) (by decide) C2 h2
  omega

theorem g6 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) x) → 4 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 4 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3)] : List (Fin 4 × Fin 4)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3)] : List (Fin 4 × Fin 4)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf_deg2 (u := 0) (v := 2) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C0 hM0 h0
  have hbase := elim_one_edge (u := 1) (v := 3) (by decide) (by decide) C1 h1
  omega

theorem g7 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) x) → 5 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 4 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2)] : List (Fin 4 × Fin 4)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2)] : List (Fin 4 × Fin 4)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  have hbase := coreK3 (fun j : Fin 4 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C1 hM1 h1
  omega

theorem g8 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) x) → 4 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (3, 4)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (3, 4)] : List (Fin 5 × Fin 5)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 0) (v := 2) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := elim_one_edge (u := 3) (v := 4) (by decide) (by decide) C2 h2
  omega

theorem g9 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) x) → 4 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4)] : List (Fin 5 × Fin 5)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 0) (v := 4) (by decide) (by decide) C3 h3
  omega

theorem g10 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) x) → 5 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4)] : List (Fin 5 × Fin 5)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 0) (v := 3) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := elim_one_edge (u := 1) (v := 4) (by decide) (by decide) C2 h2
  omega

theorem g11 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 2), (3, 4)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 2), (3, 4)] : List (Fin 5 × Fin 5)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_edge_two (u := 3) (v := 4) (by decide) (by decide) (by decide) C0 hM0 h0
  have hbase := coreK3 (fun j : Fin 5 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C1 hM1 h1
  omega

theorem g12 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) x) → 5 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3), (2, 4)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3), (2, 4)] : List (Fin 5 × Fin 5)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 1) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 0) (v := 1) (w := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := elim_one_edge (u := 2) (v := 4) (by decide) (by decide) C2 h2
  omega

theorem g13 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)] : List (Fin 5 × Fin 5)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 5 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g14 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4)] : List (Fin 5 × Fin 5)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 1) (v := 4) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 5 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g15 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)] : List (Fin 5 × Fin 5)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf_deg2 (u := 3) (v := 4) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C0 hM0 h0
  have hbase := coreK3 (fun j : Fin 5 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C1 hM1 h1
  omega

theorem g16 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)] : List (Fin 5 × Fin 5)))
  have hbase := coreC5 (fun j : Fin 5 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨3, _⟩ => some ⟨3, by decide⟩ | ⟨4, _⟩ => some ⟨4, by decide⟩) _ (by decide) C0 hM0 h0
  omega

theorem g17 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 5 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)] : List (Fin 5 × Fin 5)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)] : List (Fin 5 × Fin 5)))
  have hbase := coreBowtie (fun j : Fin 5 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨3, _⟩ => some ⟨3, by decide⟩ | ⟨4, _⟩ => some ⟨4, by decide⟩) _ (by decide) C0 hM0 h0
  omega

theorem g18 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) x) → 5 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (2, 3), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (2, 3), (4, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_edge_two (u := 0) (v := 1) (by decide) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 2) (v := 3) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := elim_one_edge (u := 4) (v := 5) (by decide) (by decide) C2 h2
  omega

theorem g19 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) x) → 5 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (4, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_edge_two (u := 0) (v := 3) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 4) (v := 5) (by decide) (by decide) C3 h3
  omega

theorem g20 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3), (4, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_edge_two (u := 4) (v := 5) (by decide) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 0) (v := 2) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := elim_one_edge (u := 1) (v := 3) (by decide) (by decide) C2 h2
  omega

theorem g21 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 5 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (3, 4), (3, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (3, 4), (3, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 3) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_edge_two (u := 0) (v := 2) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 3) (v := 5) (by decide) (by decide) C3 h3
  omega

theorem g22 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) x) → 5 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C3 hM3 h3
  have hbase := elim_one_edge (u := 0) (v := 5) (by decide) (by decide) C4 h4
  omega

theorem g23 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 0) (v := 4) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 1) (v := 5) (by decide) (by decide) C3 h3
  omega

theorem g24 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (4, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 4) (v := 5) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g25 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 1) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 0) (v := 3) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 1) (v := 5) (by decide) (by decide) C3 h3
  omega

theorem g26 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf_deg2 (u := 1) (v := 4) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 0) (v := 3) (w := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := elim_one_edge (u := 2) (v := 5) (by decide) (by decide) C2 h2
  omega

theorem g27 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (4, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 1) (v := 0) (w := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 4) (v := 5) (by decide) (by decide) C3 h3
  omega

theorem g28 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 3) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 3) (v := 5) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g29 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf_deg2 (u := 2) (v := 4) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 1) (v := 0) (w := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := elim_one_edge (u := 3) (v := 5) (by decide) (by decide) C2 h2
  omega

theorem g30 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 0) (v := 5) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g31 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 1) (v := 5) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g32 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 3) (v := 5) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g33 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)))
  have hbase := coreNet (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨3, _⟩ => some ⟨3, by decide⟩ | ⟨4, _⟩ => some ⟨4, by decide⟩ | ⟨5, _⟩ => some ⟨5, by decide⟩) _ (by decide) C0 hM0 h0
  omega

theorem g34 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 1) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 3) (v := 5) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g35 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 3) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 3) (v := 5) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g36 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 4) (v := 5) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 3) (v := 4) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g37 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  have hbase := coreC5 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨4, _⟩ => some ⟨3, by decide⟩ | ⟨5, _⟩ => some ⟨4, by decide⟩ | _ => none) _ (by decide) C1 hM1 h1
  omega

theorem g38 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] : List (Fin 6 × Fin 6)))
  have hbase := core2K3 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨3, _⟩ => some ⟨3, by decide⟩ | ⟨4, _⟩ => some ⟨4, by decide⟩ | ⟨5, _⟩ => some ⟨5, by decide⟩) _ (by decide) C0 hM0 h0
  omega

theorem g39 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 5)] : List (Fin 6 × Fin 6)))
  have hbase := coreC6 (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨3, _⟩ => some ⟨3, by decide⟩ | ⟨4, _⟩ => some ⟨4, by decide⟩ | ⟨5, _⟩ => some ⟨5, by decide⟩) _ (by decide) C0 hM0 h0
  omega

theorem g40 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 5) (by decide) (by decide) C0 hM0 h0
  have hbase := coreBowtie (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨3, _⟩ => some ⟨3, by decide⟩ | ⟨4, _⟩ => some ⟨4, by decide⟩ | _ => none) _ (by decide) C1 hM1 h1
  omega

theorem g41 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)] : List (Fin 6 × Fin 6)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 1) (v := 5) (by decide) (by decide) C0 hM0 h0
  have hbase := coreBowtie (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨3, _⟩ => some ⟨3, by decide⟩ | ⟨4, _⟩ => some ⟨4, by decide⟩ | _ => none) _ (by decide) C1 hM1 h1
  omega

theorem g42 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 6 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)] : List (Fin 6 × Fin 6)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)] : List (Fin 6 × Fin 6)))
  have hbase := coreCoreC (fun j : Fin 6 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨3, _⟩ => some ⟨3, by decide⟩ | ⟨4, _⟩ => some ⟨4, by decide⟩ | ⟨5, _⟩ => some ⟨5, by decide⟩) _ (by decide) C0 hM0 h0
  omega

theorem g43 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (3, 4), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (3, 4), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 0) (v := 2) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_edge_two (u := 3) (v := 4) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 5) (v := 6) (by decide) (by decide) C3 h3
  omega

theorem g44 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_edge_two (u := 0) (v := 4) (by decide) (by decide) (by decide) C3 hM3 h3
  have hbase := elim_one_edge (u := 5) (v := 6) (by decide) (by decide) C4 h4
  omega

theorem g45 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 5) (v := 6) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 0) (v := 3) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 1) (v := 4) (by decide) (by decide) C3 h3
  omega

theorem g46 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 4) (v := 5) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_edge_two (u := 0) (v := 3) (by decide) (by decide) (by decide) C3 hM3 h3
  have hbase := elim_one_edge (u := 4) (v := 6) (by decide) (by decide) C4 h4
  omega

theorem g47 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 2), (3, 4), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 2), (3, 4), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_edge_two (u := 3) (v := 4) (by decide) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 5) (v := 6) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g48 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3), (2, 4), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3), (2, 4), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 1) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 5) (v := 6) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 0) (v := 1) (w := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 2) (v := 4) (by decide) (by decide) C3 h3
  omega

theorem g49 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 4) (v := 5) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 4) (v := 6) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 0) (v := 2) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 1) (v := 3) (by decide) (by decide) C3 h3
  omega

theorem g50 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) x) → 6 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C3 hM3 h3
  obtain ⟨C5, hM5, hs5, h5⟩ := elim_leaf (u := 0) (v := 5) (by decide) (by decide) C4 hM4 h4
  have hbase := elim_one_edge (u := 0) (v := 6) (by decide) (by decide) C5 h5
  omega

theorem g51 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_leaf_deg2 (u := 0) (v := 5) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C3 hM3 h3
  have hbase := elim_one_edge (u := 1) (v := 6) (by decide) (by decide) C4 h4
  omega

theorem g52 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_edge_two (u := 5) (v := 6) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g53 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 1) (v := 5) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_leaf_deg2 (u := 0) (v := 4) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C3 hM3 h3
  have hbase := elim_one_edge (u := 1) (v := 6) (by decide) (by decide) C4 h4
  omega

theorem g54 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 1) (v := 5) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 0) (v := 4) (w := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 2) (v := 6) (by decide) (by decide) C3 h3
  omega

theorem g55 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_leaf_deg2 (u := 1) (v := 0) (w := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C3 hM3 h3
  have hbase := elim_one_edge (u := 5) (v := 6) (by decide) (by decide) C4 h4
  omega

theorem g56 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 1) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_edge_two (u := 5) (v := 6) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g57 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_edge_two (u := 5) (v := 6) (by decide) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 3) (v := 4) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g58 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 4) (v := 5) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_edge_two (u := 4) (v := 6) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g59 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 1) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 1) (v := 5) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 0) (v := 3) (w := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 2) (v := 6) (by decide) (by decide) C3 h3
  omega

theorem g60 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 1) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 2) (v := 5) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 0) (v := 1) (w := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 3) (v := 6) (by decide) (by decide) C3 h3
  omega

theorem g61 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 2) (v := 5) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 1) (v := 0) (w := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 4) (v := 6) (by decide) (by decide) C3 h3
  omega

theorem g62 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) → 7 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 4) (v := 5) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_leaf_deg2 (u := 1) (v := 0) (w := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C3 hM3 h3
  have hbase := elim_one_edge (u := 4) (v := 6) (by decide) (by decide) C4 h4
  omega

theorem g63 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (4, 5), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (4, 5), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 0) (v := 3) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 4) (v := 1) (w := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 5) (v := 6) (by decide) (by decide) C3 h3
  omega

theorem g64 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (4, 5), (4, 6), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (4, 5), (4, 6), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 1) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_edge_two (u := 0) (v := 3) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨4, _⟩ => some ⟨0, by decide⟩ | ⟨5, _⟩ => some ⟨1, by decide⟩ | ⟨6, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g65 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf_deg2 (u := 3) (v := 5) (w := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_edge_two (u := 4) (v := 6) (by decide) (by decide) (by decide) C1 hM1 h1
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g66 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 4), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 4), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_edge_two (u := 5) (v := 6) (by decide) (by decide) (by decide) C0 hM0 h0
  have hbase := coreC5 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨3, _⟩ => some ⟨3, by decide⟩ | ⟨4, _⟩ => some ⟨4, by decide⟩ | _ => none) _ (by decide) C1 hM1 h1
  omega

theorem g67 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 3) (v := 5) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf_deg2 (u := 1) (v := 3) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 2) (v := 0) (w := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := elim_one_edge (u := 4) (v := 6) (by decide) (by decide) C3 h3
  omega

theorem g68 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 0) (v := 5) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_leaf (u := 0) (v := 6) (by decide) (by decide) C3 hM3 h3
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C4 hM4 h4
  omega

theorem g69 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 0) (v := 5) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_leaf (u := 1) (v := 6) (by decide) (by decide) C3 hM3 h3
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C4 hM4 h4
  omega

theorem g70 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 5) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 3) (v := 6) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g71 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) x) → 8 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf (u := 1) (v := 5) (by decide) (by decide) C2 hM2 h2
  obtain ⟨C4, hM4, hs4, h4⟩ := elim_leaf (u := 1) (v := 6) (by decide) (by decide) C3 hM3 h3
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C4 hM4 h4
  omega

theorem g72 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  have hbase := coreNet (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨4, _⟩ => some ⟨3, by decide⟩ | ⟨5, _⟩ => some ⟨4, by decide⟩ | ⟨6, _⟩ => some ⟨5, by decide⟩ | _ => none) _ (by decide) C1 hM1 h1
  omega

theorem g73 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 1) (v := 5) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 3) (v := 6) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g74 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 5) (v := 6) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g75 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 3) (v := 5) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 3) (v := 6) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g76 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 5) (v := 6) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 3) (v := 5) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g77 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 2) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 0) (v := 4) (w := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨1, _⟩ => some ⟨0, by decide⟩ | ⟨5, _⟩ => some ⟨1, by decide⟩ | ⟨6, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g78 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 0) (v := 4) (by decide) (by decide) C1 hM1 h1
  have hbase := coreC5 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨5, _⟩ => some ⟨3, by decide⟩ | ⟨6, _⟩ => some ⟨4, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g79 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 1) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 2) (v := 5) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 3) (v := 6) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g80 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 1) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 3) (v := 5) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 3) (v := 6) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g81 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 1) (v := 4) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 5) (v := 6) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 3) (v := 5) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g82 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 4) (v := 5) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 4) (v := 6) (by decide) (by decide) C1 hM1 h1
  obtain ⟨C3, hM3, hs3, h3⟩ := elim_leaf_deg2 (u := 3) (v := 4) (w := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C2 hM2 h2
  have hbase := coreK3 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | _ => none) _ (by decide) C3 hM3 h3
  omega

theorem g83 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 1) (v := 5) (by decide) (by decide) C1 hM1 h1
  have hbase := coreC5 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨4, _⟩ => some ⟨3, by decide⟩ | ⟨6, _⟩ => some ⟨4, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g84 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5), (4, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  obtain ⟨C2, hM2, hs2, h2⟩ := elim_leaf (u := 4) (v := 6) (by decide) (by decide) C1 hM1 h1
  have hbase := coreC5 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨4, _⟩ => some ⟨3, by decide⟩ | ⟨5, _⟩ => some ⟨4, by decide⟩ | _ => none) _ (by decide) C2 hM2 h2
  omega

theorem g85 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size) := by
  intro C0 hM0 he0
  have h0 : ∀ x : Fin 7 → Bool, C0.eval (List.ofFn x) = edgeAny ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6), (5, 6)] : List (Fin 7 × Fin 7)) x :=
    fun x => (he0 x).trans (edgeFold_eq_edgeAny x ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6), (5, 6)] : List (Fin 7 × Fin 7)))
  obtain ⟨C1, hM1, hs1, h1⟩ := elim_leaf (u := 0) (v := 3) (by decide) (by decide) C0 hM0 h0
  have hbase := coreC6 (fun j : Fin 7 => match j with | ⟨0, _⟩ => some ⟨0, by decide⟩ | ⟨1, _⟩ => some ⟨1, by decide⟩ | ⟨2, _⟩ => some ⟨2, by decide⟩ | ⟨4, _⟩ => some ⟨3, by decide⟩ | ⟨5, _⟩ => some ⟨4, by decide⟩ | ⟨6, _⟩ => some ⟨5, by decide⟩ | _ => none) _ (by decide) C1 hM1 h1
  omega

end PEqualNP.Outside.L_meta_931

open PEqualNP.Outside.L_meta_931 in
theorem PEqualNP.Outside.L_meta_931 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = (fun x : Fin 2 → Bool => (x 0 && x 1)) x) → 1 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) x) → 2 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) x) → 4 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) x) → 3 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) x) → 3 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) x) → 4 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) x) → 4 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) x) → 4 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size) :=
  ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, g81, g82, g83, g84, g85⟩
