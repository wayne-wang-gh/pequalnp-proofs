import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_239_aux

open PEqualNP.MetaComplexity

def bstep (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

theorem wires_eq (C : BinaryCircuit) (x : List Bool) : C.wires x = C.gates.foldl bstep x := rfl

theorem bstep_len (w : List Bool) (g : BinaryGate) : (bstep w g).length = w.length + 1 := by
  simp [bstep]

theorem getD_ge (w : List Bool) (v : ℕ) (hv : w.length ≤ v) : w.getD v false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hv]

theorem bstep_getD_lt (w : List Bool) (g : BinaryGate) (v : ℕ) (hv : v < w.length) :
    (bstep w g).getD v false = w.getD v false := by
  simp [bstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hv]

theorem bstep_getD_self (w : List Bool) (g : BinaryGate) :
    (bstep w g).getD w.length false = g.op (w.getD g.left false) (w.getD g.right false) := by
  simp [bstep, List.getD_eq_getElem?_getD]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

def pull : List BinaryGate → ℕ → Finset ℕ → Finset ℕ
  | [], _, F => F
  | g :: G, base, F =>
      if base ∈ pull G (base + 1) F then
        insert g.left (insert g.right ((pull G (base + 1) F).erase base))
      else pull G (base + 1) F

theorem pull_card : ∀ (G : List BinaryGate) (base : ℕ) (F : Finset ℕ),
    (pull G base F).card ≤ F.card + G.length := by
  intro G
  induction G with
  | nil =>
    intro base F
    simp [pull]
  | cons g G ih =>
    intro base F
    have h := ih (base + 1) F
    rw [pull, List.length_cons]
    split_ifs with hb
    · have h1 : ((pull G (base + 1) F).erase base).card + 1 = (pull G (base + 1) F).card :=
        Finset.card_erase_add_one hb
      have h2 := Finset.card_insert_le g.left (insert g.right ((pull G (base + 1) F).erase base))
      have h3 := Finset.card_insert_le g.right ((pull G (base + 1) F).erase base)
      omega
    · omega

theorem pull_sound : ∀ (G : List BinaryGate) (F : Finset ℕ) (w1 w2 : List Bool),
    w1.length = w2.length →
    (∀ v ∈ pull G w1.length F, v < w1.length → w1.getD v false = w2.getD v false) →
    ∀ v ∈ F, (G.foldl bstep w1).getD v false = (G.foldl bstep w2).getD v false := by
  intro G
  induction G with
  | nil =>
    intro F w1 w2 hlen h v hv
    rw [List.foldl_nil, List.foldl_nil]
    by_cases hlt : v < w1.length
    · exact h v hv hlt
    · rw [getD_ge w1 v (Nat.le_of_not_lt hlt),
        getD_ge w2 v (by rw [← hlen]; exact Nat.le_of_not_lt hlt)]
  | cons g G ih =>
    intro F w1 w2 hlen h v hv
    rw [List.foldl_cons, List.foldl_cons]
    refine ih F (bstep w1 g) (bstep w2 g) (by rw [bstep_len, bstep_len, hlen]) ?_ v hv
    intro u hu hult
    rw [bstep_len] at hu hult
    by_cases hub : u = w1.length
    · subst hub
      have hpl : pull (g :: G) w1.length F =
          insert g.left (insert g.right ((pull G (w1.length + 1) F).erase w1.length)) := by
        rw [pull, if_pos hu]
      have hL : w1.getD g.left false = w2.getD g.left false := by
        by_cases hll : g.left < w1.length
        · exact h g.left (by rw [hpl]; exact Finset.mem_insert_self _ _) hll
        · rw [getD_ge w1 _ (Nat.le_of_not_lt hll),
            getD_ge w2 _ (by rw [← hlen]; exact Nat.le_of_not_lt hll)]
      have hR : w1.getD g.right false = w2.getD g.right false := by
        by_cases hrr : g.right < w1.length
        · exact h g.right
            (by rw [hpl]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hrr
        · rw [getD_ge w1 _ (Nat.le_of_not_lt hrr),
            getD_ge w2 _ (by rw [← hlen]; exact Nat.le_of_not_lt hrr)]
      rw [bstep_getD_self w1 g, hlen, bstep_getD_self w2 g, hL, hR]
    · have hlt : u < w1.length := by omega
      have hmem : u ∈ pull (g :: G) w1.length F := by
        rw [pull]
        split_ifs with hb
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hub, hu⟩))
        · exact hu
      rw [bstep_getD_lt w1 g u hlt, bstep_getD_lt w2 g u (by rw [← hlen]; exact hlt)]
      exact h u hmem hlt

theorem main : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), (∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n f s → n ≤ s + 1 := by
  intro n f hdep s hs
  obtain ⟨C, hsize, hC⟩ := hs
  have hcard := pull_card C.gates n {C.output}
  have hall : ∀ i : Fin n, i.val ∈ pull C.gates n {C.output} := by
    intro i
    by_contra hni
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    rw [← hC, ← hC]
    unfold BinaryCircuit.eval
    rw [wires_eq, wires_eq]
    refine pull_sound C.gates {C.output} (List.ofFn (Function.update x i (!x i))) (List.ofFn x)
      (by simp) ?_ C.output (Finset.mem_singleton_self _)
    intro v hv hvn
    rw [List.length_ofFn] at hv hvn
    have hfin : (⟨v, hvn⟩ : Fin n) ≠ i := by
      intro heq
      apply hni
      rw [← heq]
      exact hv
    rw [ofFn_getD _ v hvn, ofFn_getD _ v hvn]
    exact Function.update_of_ne hfin _ _
  have himg : (Finset.univ.image (fun i : Fin n => i.val)) ⊆ pull C.gates n {C.output} := by
    intro v hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    rw [← hi]
    exact hall i
  have hn : (Finset.univ.image (fun i : Fin n => i.val)).card = n := by
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_univ, Fintype.card_fin]
  have hle := Finset.card_le_card himg
  have hsz : C.gates.length ≤ s := hsize
  rw [Finset.card_singleton] at hcard
  omega

end PEqualNP.Outside.L_meta_239_aux

theorem PEqualNP.Outside.L_meta_239 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), (∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n f s → n ≤ s + 1 :=
  PEqualNP.Outside.L_meta_239_aux.main
