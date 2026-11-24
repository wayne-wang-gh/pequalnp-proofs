import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_191

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W := BitVec 494

abbrev ones : W := BitVec.allOnes 494

def x0 : W := 0x3ffe000fff8003ffe000fff8003ffe000ffffffc001fff0007fffffe000fffc94a4a5252929494a4a5252929494a4a5252929494a4a5252929494a4a5252
def x1 : W := 0x3ffffff0000003ffffff0000003fffffffffffffffe0000007ffffffffffff92109084842421210908484242121090848424212109084842421210908484
def x2 : W := 0x3ffffffffffffc0000000000003ffffff0007ffffffffffff8003ffffff0006063031818c0c6063031818c0c6063031818c0c6063031818c0c6063031818
def x3 : W := 0x3fffffffffffffffffffffffffc0000000007fffffffffffffffc00000000003801c00e007003801c00e007003801c00e007003801c00e007003801c00e0
def x4 : W := 0x3fffffffffffffffffffffffffffffffffff800000000000000000000000007c03e01f00f807c03e01f00f807c03e01f00f807c03e01f00f807c03e01f00

def t0 : W := x0 ||| x2
def t1 : W := x2 ||| x4
def t2 : W := x1 &&& t0
def t3 : W := x3 &&& t1
def goal : W := t2 ||| t3
def inputs : List W := [x0, x1, x2, x3, x4]
def five : List W := [t0, t1, t2, t3, goal]

def triv (A : Finset W) (z : W) : Prop := z = 0 ∨ z = ones ∨ z ∈ A

def gen (A : Finset W) (z : W) : Prop :=
  (∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ (z = a &&& b ∨ z = a ||| b)) ∨ ∃ a ∈ A, z = ~~~a

def run : List W → Finset W → Prop
  | [], A => goal ∈ A
  | z :: zs, A => (triv A z ∧ run zs A) ∨ (¬ triv A z ∧ gen A z ∧ run zs (insert z A))

def liveT : List W → Finset W → Prop
  | [], s => s = {goal}
  | z :: zs, s => z ∉ s ∧ z ≠ 0 ∧ z ≠ ones ∧ ∃ rest : Finset W,
      ((∃ a b, a ≠ b ∧ s = insert a (insert b rest) ∧ (z = a &&& b ∨ z = a ||| b)) ∨
        ∃ a, s = insert a rest ∧ z = ~~~a) ∧ liveT zs (insert z rest)

theorem compress {vs : List W} {A : Finset W} (h : run vs A) :
    ∃ zs s, zs.Sublist vs ∧ s ⊆ A ∧ liveT zs s := by
  induction vs generalizing A with
  | nil => exact ⟨[], {goal}, .refl _, Finset.singleton_subset_iff.mpr h, rfl⟩
  | cons z vs ih =>
    rcases h with ⟨_, tail⟩ | ⟨hnt, hg, tail⟩
    · obtain ⟨zs, s, hsub, hs, hl⟩ := ih tail
      exact ⟨zs, s, hsub.cons z, hs, hl⟩
    · obtain ⟨zs, t, hsub, ht, hl⟩ := ih tail
      by_cases sub : t ⊆ A
      · exact ⟨zs, t, hsub.cons z, sub, hl⟩
      · have hzt : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact absurd hu hn
          · exact ok
        have hzA : z ∉ A := fun h => hnt (Or.inr (Or.inr h))
        have hz0 : z ≠ 0 := fun h => hnt (Or.inl h)
        have hz1 : z ≠ ones := fun h => hnt (Or.inr (Or.inl h))
        have hrest : t.erase z ⊆ A := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        have hins : insert z (t.erase z) = t := Finset.insert_erase hzt
        rcases hg with ⟨a, ha, b, hb, hab, hop⟩ | ⟨a, ha, hop⟩
        · have hsA : insert a (insert b (t.erase z)) ⊆ A :=
            Finset.insert_subset ha (Finset.insert_subset hb hrest)
          refine ⟨z :: zs, _, hsub.cons_cons z, hsA, fun h => hzA (hsA h), hz0, hz1, t.erase z,
            .inl ⟨a, b, hab, rfl, hop⟩, ?_⟩
          rw [hins]; exact hl
        · have hsA : insert a (t.erase z) ⊆ A := Finset.insert_subset ha hrest
          refine ⟨z :: zs, _, hsub.cons_cons z, hsA, fun h => hzA (hsA h), hz0, hz1, t.erase z,
            .inr ⟨a, rfl, hop⟩, ?_⟩
          rw [hins]; exact hl

theorem liveT_card {zs : List W} {s : Finset W} (h : liveT zs s) : s.card ≤ zs.length + 1 := by
  induction zs generalizing s with
  | nil => change s = {goal} at h; simp [h]
  | cons z zs ih =>
    obtain ⟨hz, _, _, rest, hstep, tail⟩ := h
    have htail := ih tail
    rcases hstep with ⟨a, b, _, rfl, _⟩ | ⟨a, rfl, _⟩
    · have hzr : z ∉ rest := fun hm => hz (by simp [hm])
      rw [Finset.card_insert_of_notMem hzr] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      simp only [List.length_cons]
      omega
    · have hzr : z ∉ rest := fun hm => hz (by simp [hm])
      rw [Finset.card_insert_of_notMem hzr] at htail
      have h₁ := Finset.card_insert_le a rest
      simp only [List.length_cons]
      omega

def sep (x : W) : BitVec 247 := ((x >>> 247) ^^^ x).setWidth 247

def cuts (ws : List W) : BitVec 247 := ws.foldr (fun w v => sep w ||| v) 0

abbrev full : BitVec 247 := BitVec.allOnes 247

def dif (i : Fin 247) (w : W) : Prop := w.getLsbD (247 + i.val) ≠ w.getLsbD i.val

theorem sep_bit (a : W) (i : Fin 247) : (sep a).getLsbD i.val = true ↔ dif i a := by
  have hi := i.isLt
  simp only [sep, dif, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
  cases a.getLsbD (247 + i.val) <;> cases a.getLsbD i.val <;> simp [hi]

theorem cuts_spec (ws : List W) (i : Fin 247) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, dif i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih, sep_bit]
    simp

theorem dif_and (i : Fin 247) (a b : W) (h : dif i (a &&& b)) : dif i a ∨ dif i b := by
  unfold dif at *
  revert h
  simp only [BitVec.getLsbD_and]
  cases a.getLsbD (247 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (247 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem dif_or (i : Fin 247) (a b : W) (h : dif i (a ||| b)) : dif i a ∨ dif i b := by
  unfold dif at *
  revert h
  simp only [BitVec.getLsbD_or]
  cases a.getLsbD (247 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (247 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem dif_not (i : Fin 247) (a : W) (h : dif i (~~~a)) : dif i a := by
  have hi := i.isLt
  unfold dif at *
  have h1 : 247 + i.val < 494 := by omega
  have h2 : i.val < 494 := by omega
  revert h
  simp only [BitVec.getLsbD_not, h1, h2, decide_true, Bool.true_and]
  cases a.getLsbD (247 + i.val) <;> cases a.getLsbD i.val <;> simp

theorem goal_dif : ∀ i : Fin 247, dif i goal := by
  unfold dif
  decide +kernel

theorem live_sep (i : Fin 247) {zs : List W} {s : Finset W} (h : liveT zs s) :
    ∃ w ∈ s, dif i w := by
  induction zs generalizing s with
  | nil => change s = {goal} at h; exact ⟨goal, by simp [h], goal_dif i⟩
  | cons z zs ih =>
    obtain ⟨_, _, _, rest, hstep, tail⟩ := h
    obtain ⟨w, hw, hd⟩ := ih tail
    rcases hstep with ⟨a, b, _, rfl, hop⟩ | ⟨a, rfl, hop⟩
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · have hab : dif i a ∨ dif i b := by
          rcases hop with e | e
          · exact dif_and i a b (e ▸ hd)
          · exact dif_or i a b (e ▸ hd)
        rcases hab with h | h
        · exact ⟨a, by simp, h⟩
        · exact ⟨b, by simp, h⟩
      · exact ⟨w, by simp [hw], hd⟩
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨a, by simp, dif_not i a (hop ▸ hd)⟩
      · exact ⟨w, by simp [hw], hd⟩

theorem cuts_full {zs ws : List W} (h : liveT zs ws.toFinset) : cuts ws = full := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  obtain ⟨w, hw, hd⟩ := live_sep ⟨j, hj⟩ h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr ⟨w, List.mem_toFinset.mp hw, hd⟩
  change (cuts ws)[j] = (BitVec.allOnes 247)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

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

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
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

theorem recover_kept1 {ws r : List W} {a : W} {needed : Finset W}
    (hp : ws.Perm (a :: r)) (hn : ws.Nodup) (hs : ws.toFinset = insert a needed) :
    ∃ kept ∈ [r, a :: r], kept.Nodup ∧ kept.toFinset = needed := by
  have har := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a r.toFinset := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a := by
    intro v
    have he : (v ∈ insert a r.toFinset) ↔ v ∈ insert a needed := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons] at har
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: r, by simp, har, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp, (List.nodup_cons.mp har).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def viable (k : ℕ) (ws : List W) (z : W) (kept : List W) : Bool :=
  (cuts (z :: kept) == full) && (z != 0) && (z != ones) && !(ws.contains z) &&
    decide (kept.length ≤ k)

def good (t : List W) : Bool :=
  (t.length == 5) && t.all (fun v => five.contains v) && five.all (fun v => t.contains v)

def chk : ℕ → List W → List W → Bool
  | 0, acc, ws => (ws != [goal]) || good acc
  | k+1, acc, ws => ((ws != [goal]) || good acc) &&
      (pairs ws).all (fun p => [p.1 &&& p.2.1, p.1 ||| p.2.1].all fun z =>
        (keepChoices p.1 p.2.1 p.2.2).all fun kept =>
          !viable k ws z kept || chk k (z :: acc) (z :: kept)) &&
      (singles ws).all (fun p => [p.2, p.1 :: p.2].all fun kept =>
        !viable k ws (~~~p.1) kept || chk k (~~~p.1 :: acc) (~~~p.1 :: kept))

theorem chk_sound (zs : List W) : ∀ (k : ℕ) (acc ws : List W), ws.Nodup → zs.length ≤ k →
    liveT zs ws.toFinset → chk k acc ws = true → good (zs.reverse ++ acc) = true := by
  induction zs with
  | nil =>
    intro k acc ws hn _ hl hc
    have hw : ws = [goal] := singleton_list hn hl
    cases k with
    | zero => simpa [chk, hw] using hc
    | succ k =>
      simp only [chk, Bool.and_eq_true] at hc
      have h := hc.1.1
      simpa [hw] using h
  | cons z zs ih =>
    intro k acc ws hn hlen hl hc
    cases k with
    | zero => simp at hlen
    | succ k =>
      have hl0 := hl
      obtain ⟨hzs, hz0, hz1, rest, hstep, tail⟩ := hl
      have hzlen : zs.length ≤ k := by simpa using hlen
      have hzw : z ∉ ws := fun h => hzs (List.mem_toFinset.mpr h)
      have child : ∀ kept : List W, kept.Nodup → kept.toFinset = rest →
          (!viable k ws z kept || chk k (z :: acc) (z :: kept)) = true →
          good ((z :: zs).reverse ++ acc) = true := by
        intro kept hkn hkf hv
        have hkrest : ∀ u ∈ kept, u ∈ rest := fun u hu => hkf ▸ List.mem_toFinset.mpr hu
        have hzrest : z ∉ rest := by
          intro hm
          apply hzs
          rcases hstep with ⟨a, b, _, hs, _⟩ | ⟨a, hs, _⟩
          · rw [hs]; simp [hm]
          · rw [hs]; simp [hm]
        have hzk : z ∉ kept := fun h => hzrest (hkrest z h)
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hzk, hkn⟩
        have hfin : (z :: kept).toFinset = insert z rest := by simp [hkf]
        have htail : liveT zs (z :: kept).toFinset := by rw [hfin]; exact tail
        have hcard := liveT_card htail
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hcard
        have hviable : viable k ws z kept = true := by
          simp only [viable, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
            Bool.not_eq_true', decide_eq_true_eq]
          refine ⟨⟨⟨⟨cuts_full htail, hz0⟩, hz1⟩, ?_⟩, by omega⟩
          simpa using hzw
        rw [hviable] at hv
        have hnext : chk k (z :: acc) (z :: kept) = true := by simpa using hv
        have := ih k (z :: acc) (z :: kept) hnd hzlen htail hnext
        simpa [List.reverse_cons, List.append_assoc] using this
      simp only [chk, Bool.and_eq_true, List.all_eq_true] at hc
      obtain ⟨⟨_, hpairs⟩, hsingles⟩ := hc
      rcases hstep with ⟨a, b, hab, hs, hz⟩ | ⟨a, hs, hz⟩
      · have ha : a ∈ ws := List.mem_toFinset.mp (by rw [hs]; simp)
        have hb : b ∈ ws := List.mem_toFinset.mp (by rw [hs]; simp)
        obtain ⟨r, hm, hp⟩ := pick_two ha hb hab
        rcases hm with hm | hm
        · obtain ⟨kept, hk, hkn, hkf⟩ := recover_kept hp hn hs
          refine child kept hkn hkf (hpairs (a, b, r) hm z ?_ kept hk)
          simpa using hz
        · have hs' : ws.toFinset = insert b (insert a rest) := by
            rw [hs, Finset.insert_comm]
          obtain ⟨kept, hk, hkn, hkf⟩ := recover_kept (hp.trans (.swap _ _ _)) hn hs'
          refine child kept hkn hkf (hpairs (b, a, r) hm z ?_ kept hk)
          simpa [BitVec.and_comm, BitVec.or_comm] using hz
      · have ha : a ∈ ws := List.mem_toFinset.mp (by rw [hs]; simp)
        obtain ⟨r, hm, hp⟩ := pick_one ha
        obtain ⟨kept, hk, hkn, hkf⟩ := recover_kept1 hp hn hs
        subst hz
        exact child kept hkn hkf (hsingles (a, r) hm kept hk)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem search_ok : chk 5 [] inputs = true := by decide +kernel

def bit (k : Fin 494) (z : W) : Bool := z.getLsbD k.val

theorem ext_bit {a b : W} (h : ∀ k : Fin 494, bit k a = bit k b) : a = b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have := h ⟨i, hi⟩
  simpa only [bit, BitVec.getLsbD_eq_getElem hi] using this

def rd (w : List W) (i : ℕ) : W := w.getD i 0

def tval (w : List W) (g : Gate) : W :=
  match g.op, g.inputs with
  | .and, [] => ones
  | .and, [i] => rd w i
  | .and, i :: j :: _ => rd w i &&& rd w j
  | .or, [] => 0
  | .or, [i] => rd w i
  | .or, i :: j :: _ => rd w i ||| rd w j
  | .not, [] => ones
  | .not, i :: _ => ~~~ rd w i
  | _, _ => 0

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def vals : List Gate → List W → List W
  | [], _ => []
  | g :: gs, w => tval w g :: vals gs (w ++ [tval w g])

theorem vals_length (gs : List Gate) (w : List W) : (vals gs w).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [vals, ih]

theorem read_bit (w : List W) (i : ℕ) (k : Fin 494) :
    (w.map (bit k)).getD i false = bit k (rd w i) := by
  by_cases h : i < w.length
  · simp [rd, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [rd, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

theorem read_wire (w : List W) (i : ℕ) : rd w i = 0 ∨ rd w i ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem bit_and (k : Fin 494) (a b : W) : bit k (a &&& b) = (bit k a && bit k b) := by
  simp [bit]

theorem bit_or (k : Fin 494) (a b : W) : bit k (a ||| b) = (bit k a || bit k b) := by
  simp [bit]

theorem bit_not (k : Fin 494) (a : W) : bit k (~~~a) = !bit k a := by
  simp [bit, k.isLt]

theorem bit_ones (k : Fin 494) : bit k ones = true := by
  simp [bit, k.isLt]

theorem bit_zero (k : Fin 494) : bit k (0#494) = false := by
  simp [bit]

theorem tval_bit (w : List W) (g : Gate) (hg : legal g) (k : Fin 494) :
    g.op.eval (g.inputs.map fun i => (w.map (bit k)).getD i false) = bit k (tval w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨l, tl⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;>
      simp [tval, GateOp.eval, bit_ones, bit_zero]
  · rcases hop with rfl | rfl | rfl <;>
      simp only [List.map_cons, List.map_nil, read_bit] <;>
      simp [tval, GateOp.eval, bit_not]
  · rcases hop with rfl | rfl | rfl <;>
      simp only [List.map_cons, List.map_nil, read_bit] <;>
      simp [tval, GateOp.eval, bit_and, bit_or, bit_not]
  · simp at hlen

theorem fold_rows (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List W) (k : Fin 494) :
    gs.foldl step (w.map (bit k)) = (w ++ vals gs w).map (bit k) := by
  induction gs generalizing w with
  | nil => simp [vals]
  | cons g gs ih =>
    have hstep : step (w.map (bit k)) g = (w ++ [tval w g]).map (bit k) := by
      rw [List.map_append, List.map_singleton, ← tval_bit w g (hg g (by simp)) k]
      rfl
    rw [List.foldl_cons, hstep, ih (fun g' h => hg g' (by simp [h]))]
    simp [vals, List.append_assoc]

def reps (A : Finset W) (w : List W) : Prop := ∀ u ∈ w, u = 0 ∨ u = ones ∨ u ∈ A

theorem rd_rep {A : Finset W} {w : List W} (hr : reps A w) (i : ℕ) :
    rd w i = 0 ∨ rd w i = ones ∨ rd w i ∈ A := by
  rcases read_wire w i with h | h
  · exact .inl h
  · exact hr _ h

theorem and_class {A : Finset W} {x y : W} (hx : x = 0 ∨ x = ones ∨ x ∈ A)
    (hy : y = 0 ∨ y = ones ∨ y ∈ A) : triv A (x &&& y) ∨ gen A (x &&& y) := by
  rcases hx with rfl | rfl | hx
  · exact .inl (.inl (by simp))
  · rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | hy
  · exact .inl (.inl (by simp))
  · rw [BitVec.and_allOnes]; exact .inl (.inr (.inr hx))
  by_cases h : x = y
  · subst h; rw [BitVec.and_self]; exact .inl (.inr (.inr hx))
  · exact .inr (.inl ⟨x, hx, y, hy, h, .inl rfl⟩)

theorem or_class {A : Finset W} {x y : W} (hx : x = 0 ∨ x = ones ∨ x ∈ A)
    (hy : y = 0 ∨ y = ones ∨ y ∈ A) : triv A (x ||| y) ∨ gen A (x ||| y) := by
  rcases hx with rfl | rfl | hx
  · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact .inl hy
  · exact .inl (.inr (.inl BitVec.allOnes_or))
  rcases hy with rfl | rfl | hy
  · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inl (.inr (.inr hx))
  · exact .inl (.inr (.inl BitVec.or_allOnes))
  by_cases h : x = y
  · subst h; rw [BitVec.or_self]; exact .inl (.inr (.inr hx))
  · exact .inr (.inl ⟨x, hx, y, hy, h, .inr rfl⟩)

theorem not_class {A : Finset W} {x : W} (hx : x = 0 ∨ x = ones ∨ x ∈ A) :
    triv A (~~~x) ∨ gen A (~~~x) := by
  rcases hx with rfl | rfl | hx
  · exact .inl (.inr (.inl BitVec.not_zero))
  · exact .inl (.inl BitVec.not_allOnes)
  · exact .inr (.inr ⟨x, hx, rfl⟩)

theorem tval_class {A : Finset W} {w : List W} (hr : reps A w) (g : Gate) (hg : legal g) :
    triv A (tval w g) ∨ gen A (tval w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨l, tl⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact .inl (.inr (.inl rfl))
    · exact .inl (.inl rfl)
    · exact .inl (.inr (.inl rfl))
  · rcases hop with rfl | rfl | rfl
    · exact .inl (rd_rep hr i)
    · exact .inl (rd_rep hr i)
    · exact not_class (rd_rep hr i)
  · rcases hop with rfl | rfl | rfl
    · exact and_class (rd_rep hr i) (rd_rep hr j)
    · exact or_class (rd_rep hr i) (rd_rep hr j)
    · exact not_class (rd_rep hr i)
  · simp at hlen

theorem goal_ne_zero : goal ≠ 0 := by decide +kernel

theorem goal_ne_ones : goal ≠ ones := by decide +kernel

theorem compile (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List W) (A : Finset W)
    (hr : reps A w) (hgoal : goal ∈ w ++ vals gs w) : run (vals gs w) A := by
  induction gs generalizing w A with
  | nil =>
    have hm : goal ∈ w := by simpa [vals] using hgoal
    rcases hr _ hm with h | h | h
    · exact absurd h goal_ne_zero
    · exact absurd h goal_ne_ones
    · exact h
  | cons g gs ih =>
    have hg' : ∀ g' ∈ gs, legal g' := fun g' h => hg g' (by simp [h])
    have hgoal' : goal ∈ (w ++ [tval w g]) ++ vals gs (w ++ [tval w g]) := by
      simpa [vals, List.append_assoc] using hgoal
    by_cases ht : triv A (tval w g)
    · refine Or.inl ⟨ht, ih hg' _ A ?_ hgoal'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hr u hu
      · rw [List.mem_singleton.mp hu]; exact ht
    · have hgen := (tval_class hr g (hg g (by simp))).resolve_left ht
      refine Or.inr ⟨ht, hgen, ih hg' _ _ ?_ hgoal'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hr u hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · rw [List.mem_singleton.mp hu]; simp

def assignment (k : Fin 494) (i : Fin 5) : Bool := bit k (inputs.getD i.val 0)

theorem input_rows (k : Fin 494) : List.ofFn (assignment k) = inputs.map (bit k) := rfl

set_option maxRecDepth 100000 in
theorem rows_cover : ∀ b0 b1 b2 b3 b4 : Bool, ∃ k : Fin 494,
    bit k x0 = b0 ∧ bit k x1 = b1 ∧ bit k x2 = b2 ∧ bit k x3 = b3 ∧ bit k x4 = b4 := by
  decide +kernel

theorem row_of (x : Fin 5 → Bool) : ∃ k, assignment k = x := by
  obtain ⟨k, h0, h1, h2, h3, h4⟩ := rows_cover (x 0) (x 1) (x 2) (x 3) (x 4)
  refine ⟨k, funext fun i => ?_⟩
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem bit_t0 (k : Fin 494) : bit k t0 = (assignment k 0 || assignment k 2) := by
  simp only [t0, bit_or]; rfl

theorem bit_t1 (k : Fin 494) : bit k t1 = (assignment k 2 || assignment k 4) := by
  simp only [t1, bit_or]; rfl

theorem bit_t2 (k : Fin 494) :
    bit k t2 = (assignment k 1 && (assignment k 0 || assignment k 2)) := by
  simp only [t2, bit_and, bit_t0]; rfl

theorem bit_t3 (k : Fin 494) :
    bit k t3 = (assignment k 3 && (assignment k 2 || assignment k 4)) := by
  simp only [t3, bit_and, bit_t1]; rfl

theorem bit_goal (k : Fin 494) : bit k goal =
    ((assignment k 1 && (assignment k 0 || assignment k 2)) ||
      (assignment k 3 && (assignment k 2 || assignment k 4))) := by
  simp only [goal, bit_or, bit_t2, bit_t3]

theorem path_eq (x : Fin 5 → Bool) :
    decide (∃ i j : Fin 5, i.val + 1 = j.val ∧ x i = true ∧ x j = true) =
      ((x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))) := by
  have e : (∃ i j : Fin 5, i.val + 1 = j.val ∧ x i = true ∧ x j = true) ↔
      (x 0 = true ∧ x 1 = true) ∨ (x 1 = true ∧ x 2 = true) ∨
        (x 2 = true ∧ x 3 = true) ∨ (x 3 = true ∧ x 4 = true) := by
    constructor
    · rintro ⟨i, j, h, hi, hj⟩
      fin_cases i <;> fin_cases j <;> simp_all
    · rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩)
      · exact ⟨0, 1, rfl, a, b⟩
      · exact ⟨1, 2, rfl, a, b⟩
      · exact ⟨2, 3, rfl, a, b⟩
      · exact ⟨3, 4, rfl, a, b⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff, e]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> simp

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [7, 8]⟩], 9⟩

theorem witness_fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_table : ∀ b0 b1 b2 b3 b4 : Bool,
    witness.eval [b0, b1, b2, b3, b4] = ((b1 && (b0 || b2)) || (b3 && (b2 || b4))) := by
  decide

theorem witness_eval (x : Fin 5 → Bool) : witness.eval (List.ofFn x) =
    decide (∃ i j : Fin 5, i.val + 1 = j.val ∧ x i = true ∧ x j = true) := by
  rw [path_eq]
  exact witness_table (x 0) (x 1) (x 2) (x 3) (x 4)

theorem nodup_inputs : inputs.Nodup := by decide +kernel

set_option maxRecDepth 100000 in
theorem needed_inputs : inputs.all (fun a => ([2, 1, 15, 55, 148] : List (Fin 247)).any
    (fun i => inputs.all (fun b =>
      !(b.getLsbD (247 + i.val) != b.getLsbD i.val) || b == a))) = true := by
  decide +kernel

theorem full_inputs {s : Finset W} {zs : List W} (hs : s ⊆ inputs.toFinset)
    (hr : liveT zs s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  obtain ⟨i, _, hAll⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp needed_inputs a (List.mem_toFinset.mp ha))
  obtain ⟨b, hb, hd⟩ := live_sep i hr
  have hrow := List.all_eq_true.mp hAll b (List.mem_toFinset.mp (hs hb))
  have hne : (b.getLsbD (247 + i.val) != b.getLsbD i.val) = true := by
    simpa [dif] using hd
  rw [hne] at hrow
  have hba : b = a := by simpa using hrow
  exact hba ▸ hb

theorem main_vals (C : Circuit) (hm : IsMinimalCircuit 5 C)
    (hf : circuitFun 5 C = fun x : Fin 5 → Bool =>
      decide (∃ i j : Fin 5, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) :
    (vals C.gates inputs).length = 5 ∧ (∀ v ∈ vals C.gates inputs, v ∈ five) ∧
      ∀ v ∈ five, v ∈ vals C.gates inputs := by
  have hsize : C.gates.length ≤ 5 := by
    have h := hm.2 witness witness_fan (by
      funext x
      rw [hf]
      exact witness_eval x)
    simpa [Circuit.size, witness] using h
  have hlegal : ∀ g ∈ C.gates, legal g := hm.1
  have hval : rd (inputs ++ vals C.gates inputs) C.output = goal := by
    apply ext_bit
    intro k
    have h := congrFun hf (assignment k)
    change (C.gates.foldl step (List.ofFn (assignment k))).getD C.output false = _ at h
    rw [input_rows k, fold_rows C.gates hlegal inputs k, read_bit, path_eq] at h
    rw [h, bit_goal]
  have hgoal : goal ∈ inputs ++ vals C.gates inputs := by
    rcases read_wire (inputs ++ vals C.gates inputs) C.output with h | h
    · exact absurd (hval.symm.trans h) goal_ne_zero
    · rwa [hval] at h
  have hrun : run (vals C.gates inputs) inputs.toFinset :=
    compile C.gates hlegal inputs _
      (fun u hu => .inr (.inr (List.mem_toFinset.mpr hu))) hgoal
  obtain ⟨zs, s, hsub, hs, hl⟩ := compress hrun
  have hsf := full_inputs hs hl
  rw [hsf] at hl
  have hzlen : zs.length ≤ 5 := by
    have h1 := hsub.length_le
    rw [vals_length] at h1
    omega
  have hgood := chk_sound zs 5 [] inputs nodup_inputs hzlen hl search_ok
  simp only [List.append_nil, good, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem, List.mem_reverse, List.length_reverse] at hgood
  obtain ⟨⟨hlen, hin⟩, hout⟩ := hgood
  have hvlen : (vals C.gates inputs).length ≤ zs.length := by
    rw [vals_length, hlen]; exact hsize
  have heq : zs = vals C.gates inputs := hsub.eq_of_length_le hvlen
  rw [← heq]
  exact ⟨hlen, hin, hout⟩

theorem no_not (gs : List Gate) (w : List W) (hg : ∀ g ∈ gs, legal g)
    (hU : ∀ u ∈ w, u ∈ inputs ++ five) (hv : ∀ v ∈ vals gs w, v ∈ five)
    (hnot : ∀ u ∈ (0 : W) :: (inputs ++ five), ~~~u ∉ five) (hones : ones ∉ five) :
    ∀ g ∈ gs, g.op ≠ GateOp.not := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    have hz : tval w g ∈ five := hv _ (by simp [vals])
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · intro hop
      obtain ⟨op, args⟩ := g'
      change op = GateOp.not at hop
      subst hop
      cases args with
      | nil => exact hones hz
      | cons i tl =>
        have hzn : ~~~ (rd w i) ∈ five := by
          cases tl with
          | nil => exact hz
          | cons j tl => exact hz
        rcases read_wire w i with h | h
        · exact hnot 0 (by simp) (h ▸ hzn)
        · exact hnot _ (List.mem_cons_of_mem _ (hU _ h)) hzn
    · refine ih (w ++ [tval w g]) (fun g'' h => hg g'' (by simp [h])) ?_ ?_ g' hg'
      · intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hU u hu
        · rw [List.mem_singleton.mp hu]
          exact List.mem_append_right _ hz
      · intro v hv'
        exact hv v (by simp [vals, hv'])

theorem not_check : ((0 : W) :: (inputs ++ five)).all (fun u => !five.contains (~~~u)) = true := by
  decide +kernel

theorem not_table : ∀ u ∈ (0 : W) :: (inputs ++ five), ~~~u ∉ five := by
  intro u hu hm
  have h := List.all_eq_true.mp not_check u hu
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  exact h hm

theorem ones_check : five.contains ones = false := by decide +kernel

theorem ones_table : ones ∉ five := by
  intro hm
  have h := ones_check
  simp only [List.contains_eq_mem, decide_eq_false_iff_not] at h
  exact h hm

theorem rd_shift (vs : List W) (j : ℕ) : rd (inputs ++ vs) (5 + j) = vs.getD j 0 := by
  have h : inputs.length = 5 := rfl
  simp only [rd, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), h, Nat.add_sub_cancel_left]

theorem wire_read (C : Circuit) (hg : ∀ g ∈ C.gates, legal g) (k : Fin 494) (j : ℕ) :
    (C.wires (List.ofFn (assignment k))).getD (5 + j) false =
      bit k ((vals C.gates inputs).getD j 0) := by
  change (C.gates.foldl step (List.ofFn (assignment k))).getD (5 + j) false = _
  rw [input_rows k, fold_rows C.gates hg inputs k, read_bit, rd_shift]

theorem wire_fn (C : Circuit) (hg : ∀ g ∈ C.gates, legal g) {t : W}
    {f : (Fin 5 → Bool) → Bool} (hbit : ∀ k, bit k t = f (assignment k)) {j : ℕ}
    (he : (vals C.gates inputs).getD j 0 = t) (x : Fin 5 → Bool) :
    (C.wires (List.ofFn x)).getD (5 + j) false = f x := by
  obtain ⟨k, rfl⟩ := row_of x
  rw [wire_read C hg, he, hbit]

theorem mem_idx {vs : List W} {v : W} (h : v ∈ vs) (hl : vs.length = 5) :
    ∃ j, j < 5 ∧ vs.getD j 0 = v := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨j, hl ▸ hj, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]⟩

theorem main (C : Circuit) (hm : IsMinimalCircuit 5 C)
    (hf : circuitFun 5 C = fun x : Fin 5 → Bool =>
      decide (∃ i j : Fin 5, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) :
    (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧
    (∀ j : ℕ, j < 5 → ∃ f ∈ ([fun x => x 0 || x 2, fun x => x 2 || x 4,
        fun x => x 1 && (x 0 || x 2), fun x => x 3 && (x 2 || x 4),
        fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))] :
          List ((Fin 5 → Bool) → Bool)),
      ∀ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD (5 + j) false = f x) ∧
    (∀ f ∈ ([fun x => x 0 || x 2, fun x => x 2 || x 4,
        fun x => x 1 && (x 0 || x 2), fun x => x 3 && (x 2 || x 4),
        fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))] :
          List ((Fin 5 → Bool) → Bool)),
      ∃ j : ℕ, j < 5 ∧ ∀ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD (5 + j) false = f x) := by
  obtain ⟨hlen, hin, hout⟩ := main_vals C hm hf
  have hg : ∀ g ∈ C.gates, legal g := hm.1
  refine ⟨no_not C.gates inputs hg (fun u hu => List.mem_append_left _ hu) hin
    not_table ones_table, ?_, ?_⟩
  · intro j hj
    have hmem : (vals C.gates inputs).getD j 0 ∈ five := by
      apply hin
      have hj' : j < (vals C.gates inputs).length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    simp only [five, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with e | e | e | e | e
    · exact ⟨fun x => x 0 || x 2, List.mem_cons_self ..,
        wire_fn C hg (f := fun x => x 0 || x 2) bit_t0 e⟩
    · exact ⟨fun x => x 2 || x 4, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        wire_fn C hg (f := fun x => x 2 || x 4) bit_t1 e⟩
    · exact ⟨fun x => x 1 && (x 0 || x 2),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        wire_fn C hg (f := fun x => x 1 && (x 0 || x 2)) bit_t2 e⟩
    · exact ⟨fun x => x 3 && (x 2 || x 4), List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
        wire_fn C hg (f := fun x => x 3 && (x 2 || x 4)) bit_t3 e⟩
    · exact ⟨fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4)),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))),
        wire_fn C hg (f := fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))) bit_goal e⟩
  · intro f hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j, hj, e⟩ := mem_idx (hout t0 (by simp [five])) hlen
      exact ⟨j, hj, wire_fn C hg (f := fun x => x 0 || x 2) bit_t0 e⟩
    · obtain ⟨j, hj, e⟩ := mem_idx (hout t1 (by simp [five])) hlen
      exact ⟨j, hj, wire_fn C hg (f := fun x => x 2 || x 4) bit_t1 e⟩
    · obtain ⟨j, hj, e⟩ := mem_idx (hout t2 (by simp [five])) hlen
      exact ⟨j, hj, wire_fn C hg (f := fun x => x 1 && (x 0 || x 2)) bit_t2 e⟩
    · obtain ⟨j, hj, e⟩ := mem_idx (hout t3 (by simp [five])) hlen
      exact ⟨j, hj, wire_fn C hg (f := fun x => x 3 && (x 2 || x 4)) bit_t3 e⟩
    · obtain ⟨j, hj, e⟩ := mem_idx (hout goal (by simp [five])) hlen
      exact ⟨j, hj, wire_fn C hg (f := fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))) bit_goal e⟩

end PEqualNP.Outside.L_meta_191

theorem PEqualNP.Outside.L_meta_191 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 5 C → PEqualNP.MetaComplexity.circuitFun 5 C = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∀ j : ℕ, j < 5 → ∃ f ∈ ([fun x => x 0 || x 2, fun x => x 2 || x 4, fun x => x 1 && (x 0 || x 2), fun x => x 3 && (x 2 || x 4), fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))] : List ((Fin 5 → Bool) → Bool)), ∀ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD (5 + j) false = f x) ∧ (∀ f ∈ ([fun x => x 0 || x 2, fun x => x 2 || x 4, fun x => x 1 && (x 0 || x 2), fun x => x 3 && (x 2 || x 4), fun x => (x 1 && (x 0 || x 2)) || (x 3 && (x 2 || x 4))] : List ((Fin 5 → Bool) → Bool)), ∃ j : ℕ, j < 5 ∧ ∀ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD (5 + j) false = f x) := by
  intro C hm hf
  exact PEqualNP.Outside.L_meta_191.main C hm hf
