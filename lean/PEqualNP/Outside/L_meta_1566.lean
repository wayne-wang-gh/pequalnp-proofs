import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1566_aux

def Ln (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def R (t u : Fin 13) : Prop := t ≠ u ∧ (∃ p ∈ Ln t \ Ln u, ∃ v ∈ Ln u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ Ln t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ Ln 0 else ∅))) v = true) ∧ (∃ p ∈ Ln u \ Ln t, ∃ v ∈ Ln t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ Ln u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ Ln 0 else ∅))) v = true)

instance : DecidableRel R := fun t u => by unfold R Ln; infer_instance

def G (t u : Fin 13) : Prop := (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13)))

instance : DecidableRel G := fun t u => by unfold G; infer_instance

theorem hR : ∀ t u : Fin 13, R t u ↔ G t u := by decide

theorem quad : ∀ a b c d : Fin 13, a ≠ b → a ≠ c → b ≠ c → d ≠ a → d ≠ b → d ≠ c → G a b → G a c → G b c → G d a → G d b → G d c → False := by decide +kernel

theorem tri : ∀ a b c : Fin 13, a ≠ b → a ≠ c → b ≠ c → G a b → G a c → G b c → ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ x : Fin 13, (x = a ∨ x = b ∨ x = c) ↔ (x = 0 ∨ x = l ∨ x = m) := by decide +kernel

theorem back : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ t ∈ ({0, l, m} : Finset (Fin 13)), ∀ u ∈ ({0, l, m} : Finset (Fin 13)), t ≠ u → G t u := by decide

theorem p2 (K : Finset (Fin 13)) (hK : 3 ≤ K.card) : (∀ t ∈ K, ∀ u ∈ K, t ≠ u → G t u) ↔ ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m} := by
  constructor
  · intro hc
    obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hK
    have hKe : K = {a, b, c} := by
      apply Finset.Subset.antisymm
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hne
        push Not at hne
        exact quad a b c d hab hac hbc hne.1 hne.2.1 hne.2.2 (hc a ha b hb hab) (hc a ha c hc' hac) (hc b hb c hc' hbc) (hc d hd a ha hne.1) (hc d hd b hb hne.2.1) (hc d hd c hc' hne.2.2)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    obtain ⟨l, hl, m, hm, h⟩ := tri a b c hab hac hbc (hc a ha b hb hab) (hc a ha c hc' hac) (hc b hb c hc' hbc)
    refine ⟨l, hl, m, hm, ?_⟩
    rw [hKe]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact h x
  · rintro ⟨l, hl, m, hm, rfl⟩
    exact back l hl m hm

def Q (K : Finset (Fin 13)) : Prop := K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) + (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)

instance : DecidablePred Q := fun K => by unfold Q; infer_instance

theorem one : ∀ a : Fin 13, Q {a} := by decide

theorem two : ∀ a b : Fin 13, a ≠ b → G a b → Q {a, b} := by decide

theorem three : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), Q {0, l, m} := by decide

theorem p3 (K : Finset (Fin 13)) (h1 : 1 ≤ K.card) (hc : ∀ t ∈ K, ∀ u ∈ K, t ≠ u → G t u) : Q K := by
  rcases (show K.card = 1 ∨ K.card = 2 ∨ 3 ≤ K.card by omega) with h | h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    exact one a
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h
    exact two a b hab (hc a (by simp) b (by simp) hab)
  · obtain ⟨l, hl, m, hm, rfl⟩ := (p2 K h).1 hc
    exact three l hl m hm

theorem main : (∀ t u : Fin 13, R t u ↔ G t u) ∧ (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → R t u) ↔ ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧ (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → R t u) → Q K) := by
  refine ⟨hR, fun K hK => ?_, fun K hK hc => ?_⟩
  · simp only [hR]
    exact p2 K hK
  · simp only [hR] at hc
    exact p3 K hK hc

end PEqualNP.Outside.L_meta_1566_aux
theorem PEqualNP.Outside.L_meta_1566 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ t u : Fin 13, (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true)) ↔
      (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13)))) ∧
    (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) ↔
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧
    (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) →
      K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
        (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)) := by
  intro L hL
  obtain rfl : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  exact PEqualNP.Outside.L_meta_1566_aux.main
