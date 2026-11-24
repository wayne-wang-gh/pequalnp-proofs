import Mathlib
import PEqualNP.Defs

-- Adapted from the merged proof of L-meta-1589 (core T0 = {p0, p1}; the purity component also records OR-reachability).
namespace PEqualNP.Outside.L_meta_1642
open PEqualNP.CircuitLowerBounds

def Good {P : Type*} [DecidableEq P] (R D : Finset P) (sens pure : P → Prop) (core : Prop) : Prop :=
  (∀ r ∈ R, r ∉ D → sens r → pure r ∧ ¬ core) ∧
  (∀ r ∈ R, r ∉ D → sens r → ∀ s ∈ R, s ∉ D → sens s → r = s)

lemma Good.mono {P : Type*} [DecidableEq P] {R D E : Finset P} {s p : P → Prop} {c : Prop}
    (h : Good R D s p c) (hDE : D ⊆ E) : Good R E s p c :=
  ⟨fun r hr hd hs => h.1 r hr (fun h => hd (hDE h)) hs,
   fun r hr hd hs t ht he hs' => h.2 r hr (fun h => hd (hDE h)) hs t ht (fun h => he (hDE h)) hs'⟩

abbrev V {N : ℕ} (gs : List Gate) (w : ℕ) (x : Fin N → Bool) : Bool := Circuit.eval ⟨gs,w⟩ (List.ofFn x)
abbrev base {N : ℕ} (M : Finset (Fin N)) : Fin N → Bool := fun v => decide (v ∉ M)
abbrev single {N : ℕ} (r : Fin N) : Fin N → Bool := fun v => decide (v = r)
abbrev rimInput {N : ℕ} (M : Finset (Fin N)) (r : Fin N) : Fin N → Bool := fun v => decide (v ∉ M ∨ v = r)
abbrev S {N : ℕ} (gs : List Gate) (M : Finset (Fin N)) (w : ℕ) (r : Fin N) : Prop := V gs w (rimInput M r) = true
abbrev U {N : ℕ} (gs : List Gate) (w : ℕ) (r : Fin N) : Prop := V gs w (single r) = true
abbrev C {N : ℕ} (gs : List Gate) (T : Finset (Fin N)) (w : ℕ) : Prop := ∃ x ∈ T, U gs w x

namespace CoWire

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

end CoWire

lemma twoPoints {N : ℕ} (L : Fin N → Finset (Fin N)) {i t r s : Fin N}
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (ht : t ≠ i) (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s) :
    r ∉ L t ∨ s ∉ L t := by
  by_contra! h
  have hsub : ({r,s} : Finset (Fin N)) ⊆ L i ∩ L t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hr, h.1⟩
    · exact Finset.mem_inter.mpr ⟨hs, h.2⟩
  have hle := Finset.card_le_card hsub
  simp [hrs, hinter i t ht.symm] at hle

lemma offOther {N : ℕ} (gates : List Gate) (w : ℕ) (L : Fin N → Finset (Fin N))
    {i r s : Fin N} (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s)
    (h1 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = r)) = true)
    (h2 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = s)) = true)
    (t : Fin N) (ht : t ≠ i) :
    Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
  have lift (p : Fin N) (hp : p ∉ L t)
      (hv : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = p)) = true) :
      Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
    apply CoWire.mono ⟨gates,w⟩ hC (fun v : Fin N => decide (v = p)) (fun v => decide (v ∉ L t)) _ w hv
    intro v h
    simp only [decide_eq_true_eq] at h ⊢
    simpa only [h] using hp
  rcases twoPoints L hinter ht hr hs hrs with h | h
  · exact lift r h h1
  · exact lift s h h2

theorem orUpdate {P : Type*} [DecidableEq P] (R D : Finset P) (s₁ s₂ p₁ p₂ : P → Prop)
    (c₁ c₂ Q : Prop) [Decidable Q] (g₁ : Good R D s₁ p₁ c₁) (g₂ : Good R D s₂ p₂ c₂)
    (charge : ((∃ r ∈ R, r ∉ D ∧ s₁ r ∧ c₂) ∨ (∃ r ∈ R, r ∉ D ∧ s₂ r ∧ c₁) ∨
        (∃ r ∈ R, ∃ t ∈ R, r ∉ D ∧ t ∉ D ∧ s₁ r ∧ s₂ t ∧ r ≠ t)) → Q) :
    ∃ E : Finset P, D ⊆ E ∧ E.card ≤ D.card + (if Q then 1 else 0) ∧
      Good R E (fun r => s₁ r ∨ s₂ r) (fun r => p₁ r ∨ p₂ r) (c₁ ∨ c₂) := by
  classical
  let Bad := (∃ r ∈ R, r ∉ D ∧ s₁ r ∧ c₂) ∨ (∃ r ∈ R, r ∉ D ∧ s₂ r ∧ c₁) ∨
             (∃ r ∈ R, ∃ t ∈ R, r ∉ D ∧ t ∉ D ∧ s₁ r ∧ s₂ t ∧ r ≠ t)
  have drop {s p : P → Prop} {c : Prop} (g : Good R D s p c) {a : P}
      (ha : a ∈ R) (hd : a ∉ D) (hs : s a) :
      ∀ z ∈ R, z ∉ insert a D → ¬ s z := by
    intro z hz he hsz
    have eq := g.2 z hz (fun h => he (Finset.mem_insert_of_mem h)) hsz a ha hd hs
    exact he (Finset.mem_insert.mpr (Or.inl eq))
  have vac (E : Finset P) (h : ∀ z ∈ R, z ∉ E → ¬ (s₁ z ∨ s₂ z)) :
      Good R E (fun z => s₁ z ∨ s₂ z) (fun z => p₁ z ∨ p₂ z) (c₁ ∨ c₂) := by
    exact ⟨fun r hr he hs => (h r hr he hs).elim, fun r hr he hs => (h r hr he hs).elim⟩
  by_cases bad : Bad
  · have q : Q := charge bad
    have budget (a : P) : (insert a D).card ≤ D.card + (if Q then 1 else 0) := by
      rw [ite_eq_left q]
      exact Finset.card_insert_le a D
    rcases bad with ⟨a,ha,hd,hs,hc⟩ | ⟨a,ha,hd,hs,hc⟩ | ⟨a,ha,b,hb,hd,_,hs,_,_⟩
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, vac _ ?_⟩
      intro z hz he h
      rcases h with l | r
      · exact drop g₁ ha hd hs z hz he l
      · exact (g₂.1 z hz (fun h => he (Finset.mem_insert_of_mem h)) r).2 hc
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, vac _ ?_⟩
      intro z hz he h
      rcases h with l | r
      · exact (g₁.1 z hz (fun h => he (Finset.mem_insert_of_mem h)) l).2 hc
      · exact drop g₂ ha hd hs z hz he r
    · refine ⟨insert a D, Finset.subset_insert _ _, budget a, ?_⟩
      have right : ∀ z ∈ R, z ∉ insert a D → s₁ z ∨ s₂ z → s₂ z :=
        fun z hz he h => h.resolve_left (drop g₁ ha hd hs z hz he)
      have g₂' := g₂.mono (Finset.subset_insert a D)
      constructor
      · intro z hz he h
        have v := g₂'.1 z hz he (right z hz he h)
        exact ⟨Or.inr v.1, fun hC => hC.elim (g₁.1 a ha hd hs).2 v.2⟩
      · intro z hz he h t ht hte hts
        exact g₂'.2 z hz he (right z hz he h) t ht hte (right t ht hte hts)
  · refine ⟨D, Finset.Subset.rfl, Nat.le_add_right _ _, ?_⟩
    have cross {a b : P} (ha : a ∈ R) (hb : b ∈ R) (da : a ∉ D) (db : b ∉ D)
        (sa : s₁ a) (sb : s₂ b) : a = b := by
      by_contra hn
      exact bad (Or.inr (Or.inr ⟨a,ha,b,hb,da,db,sa,sb,hn⟩))
    constructor
    · intro r hr hd hs
      rcases hs with l | r'
      · have v := g₁.1 r hr hd l
        exact ⟨Or.inl v.1, fun c => c.elim v.2 (fun rc => bad (Or.inl ⟨r,hr,hd,l,rc⟩))⟩
      · have v := g₂.1 r hr hd r'
        exact ⟨Or.inr v.1, fun c => c.elim (fun lc => bad (Or.inr (Or.inl ⟨r,hr,hd,r',lc⟩))) v.2⟩
    · intro a ha da hsa b hb db hsb
      rcases hsa with l | r <;> rcases hsb with l' | r'
      · exact g₁.2 a ha da l b hb db l'
      · exact cross ha hb da db l r'
      · exact (cross hb ha db da l' r).symm
      · exact g₂.2 a ha da r b hb db r'

lemma Good.imp {P : Type*} [DecidableEq P] {R D : Finset P} {s p s' p' : P → Prop} {c c' : Prop}
    (h : Good R D s p c) (hs : ∀ r, s' r → s r) (hp : ∀ r, p r → p' r) (hc : c' → c) :
    Good R D s' p' c' :=
  ⟨fun r hr hd h' => ⟨hp r (h.1 r hr hd (hs r h')).1, fun k => (h.1 r hr hd (hs r h')).2 (hc k)⟩,
   fun r hr hd h' t ht hd' h'' => h.2 r hr hd (hs r h') t ht hd' (hs t h'')⟩

lemma Good.vac {P : Type*} [DecidableEq P] {R D : Finset P} {s p : P → Prop} {c : Prop}
    (h : ∀ r ∈ R, r ∉ D → ¬ s r) : Good R D s p c :=
  ⟨fun r hr hd hs => (h r hr hd hs).elim, fun r hr hd hs => (h r hr hd hs).elim⟩

theorem realOrUpdate {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 : Fin N}
    {T : Finset (Fin N)} {gs : List Gate} {Xs : Finset (Fin gs.length)} {D : Finset (Fin N)}
    (St : ℕ → Fin N → Prop)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1) (hTsub : T ⊆ L i0)
    (hXs : ∀ g : Fin gs.length, ((gs.get g).op = GateOp.or ∧ V gs (N + g.val) (base (L i0)) = false ∧
      (∀ t : Fin N, t ≠ i0 → V gs (N + g.val) (base (L t)) = true) ∧
      ¬ ∀ e ∈ (gs.get g).inputs, C gs T e) → g ∈ Xs)
    (i : Fin gs.length) (a b : ℕ) (hop : (gs.get i).op = GateOp.or)
    (hinputs : (gs.get i).inputs = [a,b]) (hcold : V gs (N + i.val) (base (L i0)) = false)
    (hor : ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x || V gs b x))
    (stA : ∀ r, St a r → St (N + i.val) r) (stB : ∀ r, St b r → St (N + i.val) r)
    (ga : Good (L i0 \ T) D (S gs (L i0) a) (fun r => U gs a r ∧ St a r) (C gs T a))
    (gb : Good (L i0 \ T) D (S gs (L i0) b) (fun r => U gs b r ∧ St b r) (C gs T b)) :
    ∃ E : Finset (Fin N), D ⊆ E ∧ E.card ≤ D.card + (if i ∈ Xs then 1 else 0) ∧
      Good (L i0 \ T) E (S gs (L i0) (N + i.val))
        (fun r => U gs (N + i.val) r ∧ St (N + i.val) r) (C gs T (N + i.val)) := by
  classical
  have us (r : Fin N) : U gs (N + i.val) r ↔ U gs a r ∨ U gs b r := by
    change V gs (N + i.val) (single r) = true ↔ _
    rw [hor]
    simp only [Bool.or_eq_true, U]
  have ss (r : Fin N) : S gs (L i0) (N + i.val) r ↔ S gs (L i0) a r ∨ S gs (L i0) b r := by
    change V gs (N + i.val) (rimInput (L i0) r) = true ↔ _
    rw [hor]
    simp only [Bool.or_eq_true, S]
  have cs : C gs T (N + i.val) ↔ C gs T a ∨ C gs T b := by
    constructor
    · rintro ⟨x,hx,ux⟩
      rcases (us x).1 ux with ua | ub
      · exact Or.inl ⟨x,hx,ua⟩
      · exact Or.inr ⟨x,hx,ub⟩
    · rintro (⟨x,hx,ua⟩ | ⟨x,hx,ub⟩)
      · exact ⟨x,hx,(us x).2 (Or.inl ua)⟩
      · exact ⟨x,hx,(us x).2 (Or.inr ub)⟩
  have pay {r t : Fin N} (hr : r ∈ L i0) (ht : t ∈ L i0) (hrt : r ≠ t)
      (u₁ : U gs a r) (u₂ : U gs b t) (empty : ¬ C gs T a ∨ ¬ C gs T b) : i ∈ Xs := by
    have every := offOther gs (N + i.val) L hG hinter hr ht hrt
      ((us r).2 (Or.inl u₁)) ((us t).2 (Or.inr u₂))
    refine hXs i ⟨hop, hcold, every, fun hall => ?_⟩
    rcases empty with ha | hb
    · exact ha (hall a (by rw [hinputs]; simp))
    · exact hb (hall b (by rw [hinputs]; simp))
  obtain ⟨E,hDE,hcard,hGood⟩ := orUpdate (L i0 \ T) D _ _ _ _ _ _ (i ∈ Xs) ga gb (by
    rintro (⟨r,hr,hd,sa,t,ht,ub⟩ | ⟨t,ht,hd,sb,r,hr,ua⟩ | ⟨r,hr,t,ht,dr,dt,sa,sb,hrt⟩)
    · obtain ⟨ua,ha⟩ := ga.1 r hr hd sa
      have h := Finset.mem_sdiff.mp hr
      exact pay h.1 (hTsub ht) (fun e => h.2 (e ▸ ht)) ua.1 ub (Or.inl ha)
    · obtain ⟨ub,hb⟩ := gb.1 t ht hd sb
      have h := Finset.mem_sdiff.mp ht
      exact pay (hTsub hr) h.1 (fun e => h.2 (e ▸ hr)) ua ub.1 (Or.inr hb)
    · obtain ⟨ua,ha⟩ := ga.1 r hr dr sa
      obtain ⟨ub,_⟩ := gb.1 t ht dt sb
      exact pay (Finset.mem_sdiff.mp hr).1 (Finset.mem_sdiff.mp ht).1 hrt ua.1 ub.1 (Or.inl ha))
  refine ⟨E,hDE,hcard,?_,?_⟩
  · intro r hr hd sr
    obtain ⟨u,c⟩ := hGood.1 r hr hd ((ss r).1 sr)
    refine ⟨?_, fun h => c (cs.1 h)⟩
    rcases u with u | u
    · exact ⟨(us r).2 (Or.inl u.1), stA r u.2⟩
    · exact ⟨(us r).2 (Or.inr u.1), stB r u.2⟩
  · intro r hr hd sr t ht hdt st
    exact hGood.2 r hr hd ((ss r).1 sr) t ht hdt ((ss t).1 st)

theorem prefixBudget {P : Type*} [DecidableEq P] (N k : ℕ)
    (A Xs : Finset (Fin k)) (G : ℕ → Finset P → Prop)
    (mono : ∀ w D E, D ⊆ E → G w D → G w E)
    (init : ∀ w < N, G w ∅)
    (step : ∀ (i : Fin k) (D : Finset P), (∀ w < N + i.val, G w D) →
      ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if i ∈ A then 1 else 0) +
        (if i ∈ Xs then 1 else 0) ∧ G (N + i.val) E) :
    ∃ D, D.card ≤ A.card + Xs.card ∧ ∀ w < N + k, G w D := by
  let count (S : Finset (Fin k)) (j : ℕ) := (S.filter fun v => v.val < j).card
  have next (S : Finset (Fin k)) (i : Fin k) :
      count S (i.val + 1) = count S i.val + (if i ∈ S then 1 else 0) := by
    have hlt (v : Fin k) : v.val < i.val + 1 ↔ v = i ∨ v.val < i.val := by
      rw [Fin.ext_iff]
      omega
    by_cases hi : i ∈ S
    · have heq : S.filter (fun v => v.val < i.val + 1) =
          insert i (S.filter fun v => v.val < i.val) := by
        ext v
        by_cases hv : v = i
        · subst v
          simp [hi]
        · simp [hlt, hv]
      have hnot : i ∉ S.filter (fun v => v.val < i.val) := by simp
      simp only [count, heq, Finset.card_insert_of_notMem hnot, ite_eq_left hi]
    · have heq : S.filter (fun v => v.val < i.val + 1) =
          S.filter (fun v => v.val < i.val) := by
        ext v
        by_cases hv : v = i
        · subst v
          simp [hi]
        · simp [hlt, hv]
      simp only [count, heq, ite_eq_right hi, Nat.add_zero]
  have prefixBound (j : ℕ) (hj : j ≤ k) :
      ∃ D, D.card ≤ count A j + count Xs j ∧ ∀ w < N + j, G w D := by
    induction j with
    | zero =>
      exact ⟨∅, by simp [count], by simpa using init⟩
    | succ j ih =>
      let i : Fin k := ⟨j, by omega⟩
      obtain ⟨D, hD, hG⟩ := ih (by omega)
      obtain ⟨E, hDE, hE, hGE⟩ := step i D hG
      refine ⟨E, ?_, ?_⟩
      · change E.card ≤ count A (i.val + 1) + count Xs (i.val + 1)
        rw [next A i, next Xs i]
        change D.card ≤ count A i.val + count Xs i.val at hD
        omega
      · intro w hw
        by_cases hprev : w < N + j
        · exact mono w D E hDE (hG w hprev)
        · have hw' : w = N + i.val := by change w = N + j; omega
          exact hw' ▸ hGE
  have last (S : Finset (Fin k)) : count S k = S.card := by
    have heq : S.filter (fun v => v.val < k) = S := by
      ext v
      simp
    simp only [count, heq]
  simpa only [last] using prefixBound k (le_refl k)

lemma primaryGood {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (w : ℕ) (hw : w < N)
    (hc : V gs w (base M) = false) : Good (M \ T) ∅ (S gs M w) (U gs w) (C gs T w) := by
  let p : Fin N := ⟨w, hw⟩
  have eval (x : Fin N → Bool) : V gs w x = x p := CoWire.input_value ⟨gs,w⟩ x p
  rw [eval] at hc
  have hp : p ∈ M := by simpa [base] using hc
  have sens (r : Fin N) : S gs M w r ↔ p = r := by
    change V gs w (rimInput M r) = true ↔ _
    rw [eval]
    simp [rimInput, hp]
  have purePt (r : Fin N) : U gs w r ↔ p = r := by
    change V gs w (single r) = true ↔ _
    rw [eval]
    simp [single]
  constructor
  · intro r hr _ hs
    refine ⟨(purePt r).mpr ((sens r).mp hs), ?_⟩
    rintro ⟨x, hx, hux⟩
    have heq : r = x := ((sens r).mp hs).symm.trans ((purePt x).mp hux)
    exact (Finset.mem_sdiff.mp hr).2 (heq ▸ hx)
  · intro r _ _ hr s _ _ hs
    exact ((sens r).mp hr).symm.trans ((sens s).mp hs)

lemma missingV {N : ℕ} (gs : List Gate) (w : ℕ) (hw : N + gs.length ≤ w)
    (x : Fin N → Bool) : V gs w x = false :=
  CoWire.missing_value ⟨gs,w⟩ x w hw

lemma primaryGood2 {N : ℕ} (gs : List Gate) (M T : Finset (Fin N)) (St : ℕ → Fin N → Prop)
    (stIn : ∀ r : Fin N, St r.val r) (w : ℕ) (hw : w < N)
    (hc : V gs w (base M) = false) :
    Good (M \ T) ∅ (S gs M w) (fun r => U gs w r ∧ St w r) (C gs T w) := by
  refine (primaryGood gs M T w hw hc).imp (fun _ h => h) ?_ (fun h => h)
  intro r hu
  refine ⟨hu, ?_⟩
  have eval : V gs w (single r) = single r ⟨w, hw⟩ :=
    CoWire.input_value ⟨gs,w⟩ (single r) ⟨w, hw⟩
  have hu' : V gs w (single r) = true := hu
  rw [eval] at hu'
  have heq : (⟨w, hw⟩ : Fin N) = r := by simpa [single] using hu'
  subst heq
  exact stIn ⟨w, hw⟩

lemma gateCases {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length) :
    (∃ a < N + i.val, (gs.get i).inputs = [a] ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = V gs a x) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.and ∧
      (gs.get i).inputs = [a, b] ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x && V gs b x)) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.or ∧
      (gs.get i).inputs = [a, b] ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x || V gs b x)) := by
  obtain ⟨hop, hlen⟩ := hG (gs.get i) (List.get_mem gs i)
  obtain ⟨hnon, earlier⟩ := htop i
  have val (x : Fin N → Bool) :
      V gs (N + i.val) x = (gs.get i).op.eval
        ((gs.get i).inputs.map fun r => if r < N + i.val then V gs r x else false) := by
    let D : Circuit := ⟨gs,0⟩
    have hw : N + i.val < N + D.size := Nat.add_lt_add_left i.isLt N
    have h := CoWire.gate_value D x (N + i.val) (by omega) hw
    simpa [D, CoWire.value, V, Circuit.eval, Circuit.wires] using h
  generalize eqg : gs.get i = g at hop hlen hnon earlier val ⊢
  cases ins : g.inputs with
  | nil => simp [ins] at hnon
  | cons a rest =>
    have ha : a < N + i.val := earlier a (by simp [ins])
    cases rest with
    | nil =>
      refine Or.inl ⟨a, ha, rfl, ?_⟩
      intro x
      rcases hop with hop | hop <;> simpa [ins, hop, GateOp.eval, ha] using val x
    | cons b rest =>
      cases rest with
      | nil =>
        have hb : b < N + i.val := earlier b (by simp [ins])
        rcases hop with hop | hop
        · refine Or.inr (Or.inl ⟨a, ha, b, hb, hop, rfl, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
        · refine Or.inr (Or.inr ⟨a, ha, b, hb, hop, rfl, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
      | cons c rest => simp [ins] at hlen

lemma andInputs {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length)
    (hand : (gs.get i).op = GateOp.and) (e : ℕ) (he : e ∈ (gs.get i).inputs)
    (x : Fin N → Bool) (hx : V gs (N + i.val) x = true) : V gs e x = true := by
  rcases gateCases gs hG htop i with
    ⟨a, _, hin, heq⟩ | ⟨a, _, b, _, _, hin, heq⟩ | ⟨a, _, b, _, hop, _, _⟩
  · rw [hin] at he
    have hea : e = a := by simpa using he
    subst hea
    exact (heq x).symm.trans hx
  · rw [hin] at he
    have hab := Bool.and_eq_true_iff.mp ((heq x).symm.trans hx)
    have hea : e = a ∨ e = b := by simpa using he
    rcases hea with h | h
    · rw [h]; exact hab.1
    · rw [h]; exact hab.2
  · rw [hand] at hop
    cases hop

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
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
  classical
  intro q N L i0 p0 p1 _hq _hN hsize hinter _hpair hne hp0 hp1 gs hG hlen hlt ev hev o0 hbase
    h0 _h1 hrim St hSt ch hch Au Xs hAu hXs
  have htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val := fun i => ⟨hlen i, hlt i⟩
  have m0 : p0 ∈ ({p0, p1} : Finset (Fin N)) := Finset.mem_insert_self _ _
  have m1 : p1 ∈ ({p0, p1} : Finset (Fin N)) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hTsub : ({p0, p1} : Finset (Fin N)) ⊆ L i0 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hp0
    · rw [Finset.mem_singleton.mp h]; exact hp1
  have offT : ∀ r ∈ L i0 \ ({p0, p1} : Finset (Fin N)), r ∈ L i0 ∧ r ≠ p0 ∧ r ≠ p1 := by
    intro r hr
    have h := Finset.mem_sdiff.mp hr
    exact ⟨h.1, fun e => h.2 (by rw [e]; exact m0), fun e => h.2 (by rw [e]; exact m1)⟩
  have stIn : ∀ r : Fin N, St r.val r := by
    intro r
    rw [hSt]
    intro Zs hz _
    exact hz
  have stOr : ∀ (i : Fin gs.length), (gs.get i).op = GateOp.or →
      ∀ e ∈ (gs.get i).inputs, ∀ r, St e r → St (N + i.val) r := by
    intro i hor e he r h
    rw [hSt] at h ⊢
    intro Zs hz hcl
    exact h Zs (hcl i hz hor e he) hcl
  have hXs' : ∀ g : Fin gs.length, ((gs.get g).op = GateOp.or ∧
      V gs (N + g.val) (base (L i0)) = false ∧
      (∀ t : Fin N, t ≠ i0 → V gs (N + g.val) (base (L t)) = true) ∧
      ¬ ∀ e ∈ (gs.get g).inputs, C gs ({p0, p1} : Finset (Fin N)) e) → g ∈ Xs := by
    rintro g ⟨k1, k2, k3, k4⟩
    refine hXs g ⟨k1, (hev _ _).trans k2, fun t ht => (hev _ _).trans (k3 t ht),
      fun hall => k4 fun e he => ?_⟩
    rcases hall e he with h | h
    · exact ⟨p0, m0, (hev _ _).symm.trans h⟩
    · exact ⟨p1, m1, (hev _ _).symm.trans h⟩
  let Inv (w : ℕ) (D : Finset (Fin N)) : Prop :=
    V gs w (base (L i0)) = false →
      Good (L i0 \ {p0, p1}) D (S gs (L i0) w) (fun r => U gs w r ∧ St w r) (C gs {p0, p1} w)
  have grow : ∀ w D E, D ⊆ E → Inv w D → Inv w E := by
    intro w D E hDE hw hc
    exact (hw hc).mono hDE
  have init : ∀ w < N, Inv w ∅ := by
    intro w hw hc
    exact primaryGood2 gs (L i0) {p0, p1} St stIn w hw hc
  have step (i : Fin gs.length) (D : Finset (Fin N))
      (prev : ∀ w < N + i.val, Inv w D) :
      ∃ E, D ⊆ E ∧ E.card ≤ D.card + (if i ∈ Au then 1 else 0) + (if i ∈ Xs then 1 else 0) ∧
        Inv (N + i.val) E := by
    by_cases hc : V gs (N + i.val) (base (L i0)) = false
    · rcases (hG (gs.get i) (List.get_mem gs i)).1 with hand | hor
      · by_cases unpaid : ∃ r ∈ L i0 \ ({p0, p1} : Finset (Fin N)),
            r ∉ D ∧ S gs (L i0) (N + i.val) r
        · obtain ⟨r, hr, hd, hs⟩ := unpaid
          obtain ⟨hrM, ne0, ne1⟩ := offT r hr
          have hs' : ev (N + i.val) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true :=
            (hev _ _).trans hs
          have carry : (gs.get i).op = GateOp.and ∧
              ev (N + i.val) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
              ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
                ev (N + i.val) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true :=
            ⟨hand, (hev _ _).trans hc, r, hrM, ne0, ne1, hs'⟩
          obtain ⟨hmem, hcold⟩ := hch i carry
          have hcold' : V gs (ch i) (base (L i0)) = false := (hev _ _).symm.trans hcold
          have sub : ∀ x : Fin N → Bool, V gs (N + i.val) x = true → V gs (ch i) x = true :=
            fun x hx => andInputs gs hG htop i hand (ch i) hmem x hx
          have gch : Good (L i0 \ {p0, p1}) D (S gs (L i0) (ch i))
              (fun r => U gs (ch i) r ∧ St (ch i) r) (C gs {p0, p1} (ch i)) :=
            prev (ch i) (hlt i _ hmem) hcold'
          have hst : St (ch i) r := (gch.1 r hr hd (sub _ hs)).1.2
          have hin : i ∈ Au := hAu i ⟨carry, r, hrM, ne0, ne1, hs', hst⟩
          have no : ∀ t ∈ L i0 \ ({p0, p1} : Finset (Fin N)), t ∉ insert r D →
              ¬ S gs (L i0) (N + i.val) t := by
            intro t ht he hts
            have htd : t ∉ D := fun hm => he (Finset.mem_insert_of_mem hm)
            exact he (Finset.mem_insert.mpr
              (Or.inl (gch.2 t ht htd (sub _ hts) r hr hd (sub _ hs))))
          refine ⟨insert r D, Finset.subset_insert _ _, ?_, fun _ => Good.vac no⟩
          rw [Finset.card_insert_of_notMem hd, ite_eq_left hin]
          omega
        · exact ⟨D, Finset.Subset.rfl, by omega,
            fun _ => Good.vac (fun r hr hd hs => unpaid ⟨r, hr, hd, hs⟩)⟩
      · rcases gateCases gs hG htop i with
          ⟨a, ha, hin, heq⟩ | ⟨a, _, b, _, hop, _, _⟩ | ⟨a, ha, b, hb, hop, hin, heq⟩
        · refine ⟨D, Finset.Subset.rfl, by omega, fun _ => ?_⟩
          have ca : V gs a (base (L i0)) = false := (heq _).symm.trans hc
          have hmem : a ∈ (gs.get i).inputs := by rw [hin]; simp
          have ga : Good (L i0 \ {p0, p1}) D (S gs (L i0) a)
              (fun r => U gs a r ∧ St a r) (C gs {p0, p1} a) := prev a ha ca
          show Good (L i0 \ {p0, p1}) D (S gs (L i0) (N + i.val))
            (fun r => U gs (N + i.val) r ∧ St (N + i.val) r) (C gs {p0, p1} (N + i.val))
          refine ga.imp (fun r h => (heq _).symm.trans h)
            (fun r h => ⟨(heq _).trans h.1, stOr i hor a hmem r h.2⟩) ?_
          rintro ⟨x, hx, ux⟩
          exact ⟨x, hx, (heq _).symm.trans ux⟩
        · rw [hor] at hop
          cases hop
        · have ab : V gs a (base (L i0)) = false ∧ V gs b (base (L i0)) = false := by
            simpa only [Bool.or_eq_false_iff] using (heq (base (L i0))).symm.trans hc
          obtain ⟨E, hDE, hcard, hg⟩ := realOrUpdate St hG hinter hTsub hXs' i a b hop hin hc heq
            (stOr i hor a (by rw [hin]; simp)) (stOr i hor b (by rw [hin]; simp))
            (prev a ha ab.1) (prev b hb ab.2)
          exact ⟨E, hDE, by omega, fun _ => hg⟩
    · exact ⟨D, fun _ h => h, by omega, fun h => (hc h).elim⟩
  obtain ⟨D, hd, hgood⟩ := prefixBudget N gs.length Au Xs Inv grow init step
  have s0 : V gs o0 (single p0) = true := (hev _ _).symm.trans h0
  have bounded : o0 < N + gs.length := by
    by_contra! he
    exact Bool.false_ne_true ((missingV gs o0 he (single p0)).symm.trans s0)
  have core : C gs ({p0, p1} : Finset (Fin N)) o0 := ⟨p0, m0, s0⟩
  have cold : V gs o0 (base (L i0)) = false := (hev _ _).symm.trans hbase
  have gout : Good (L i0 \ {p0, p1}) D (S gs (L i0) o0)
      (fun r => U gs o0 r ∧ St o0 r) (C gs {p0, p1} o0) := hgood o0 bounded cold
  have covered : L i0 \ ({p0, p1} : Finset (Fin N)) ⊆ D := by
    intro r hr
    by_contra hd'
    obtain ⟨hrM, ne0, ne1⟩ := offT r hr
    have sens : S gs (L i0) o0 r := (hev _ _).symm.trans (hrim r hrM ne0 ne1)
    exact (gout.1 r hr hd' sens).2 core
  have count := (Finset.card_le_card covered).trans hd
  rw [Finset.card_sdiff_of_subset hTsub, hsize, Finset.card_pair hne] at count
  omega

end PEqualNP.Outside.L_meta_1642

theorem PEqualNP.Outside.L_meta_1642 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
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
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true)) → g ∈ Xs) → q - 1 ≤ Au.card + Xs.card :=
  PEqualNP.Outside.L_meta_1642.main_aux
