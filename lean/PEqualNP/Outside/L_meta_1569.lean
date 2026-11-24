import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1569

set_option maxRecDepth 100000 in
theorem per_set : ∀ F : Finset (Fin 13),
    (∀ t ∈ F, ∀ u ∈ F, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) →
    F.card - 1 = (if (0 : Fin 13) ∈ F ∧ 2 ≤ F.card then 1 else 0) +
      (if ∃ l ∈ F, ∃ m ∈ F, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1569

theorem PEqualNP.Outside.L_meta_1569 : ∀ (k : ℕ) (K : Fin k → Finset (Fin 13)),
    (∀ i : Fin k, ∀ t ∈ K i, ∀ u ∈ K i, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) →
    ∑ i : Fin k, ((K i).card - 1) =
      (Finset.univ.filter (fun i : Fin k => (0 : Fin 13) ∈ K i ∧ 2 ≤ (K i).card)).card +
      (Finset.univ.filter (fun i : Fin k => ∃ l ∈ K i, ∃ m ∈ K i, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))).card := by
  classical
  intro k K hK
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact PEqualNP.Outside.L_meta_1569.per_set (K i) (hK i)
