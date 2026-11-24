import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_238

lemma eval_nil_gates (C : BinaryCircuit) (h : C.gates = []) (x : List Bool) :
    C.eval x = x.getD C.output false := by
  simp [BinaryCircuit.eval, BinaryCircuit.wires, h]

lemma ofFn_two_eq (a b : Bool) :
    List.ofFn (fun i : Fin 2 => if (i : ℕ) = 0 then a else b) = [a, b] := by
  revert a b
  decide

end PEqualNP.Outside.L_meta_238

theorem PEqualNP.Outside.L_meta_238 :
    ∀ s : ℕ,
      PEqualNP.MetaComplexity.HasBinarySize 2 (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔
        1 ≤ s := by
  intro s
  constructor
  · rintro ⟨C, hsize, hval⟩
    by_contra h1
    have hs : s = 0 := by omega
    have hsz : C.size = 0 := by omega
    have hlen : C.gates = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [BinaryCircuit.size] using hsz)
    have hev := PEqualNP.Outside.L_meta_238.eval_nil_gates C hlen
    have hA : ([false, true] : List Bool).getD C.output false = true := by
      have h := hval (fun i : Fin 2 => if (i : ℕ) = 0 then false else true)
      rw [hev, PEqualNP.Outside.L_meta_238.ofFn_two_eq] at h
      simpa using h
    have hB : ([true, false] : List Bool).getD C.output false = true := by
      have h := hval (fun i : Fin 2 => if (i : ℕ) = 0 then true else false)
      rw [hev, PEqualNP.Outside.L_meta_238.ofFn_two_eq] at h
      simpa using h
    by_cases h0 : C.output = 0
    · rw [h0] at hA
      exact Bool.noConfusion hA
    by_cases h1' : C.output = 1
    · rw [h1'] at hB
      exact Bool.noConfusion hB
    · have h2 : 2 ≤ C.output := by omega
      rw [List.getD_eq_default] at hA
      · exact Bool.noConfusion hA
      · simpa using h2
  · intro h1
    refine ⟨⟨[⟨xor, 0, 1⟩], 2⟩, ?_, ?_⟩
    · simpa [BinaryCircuit.size] using h1
    · intro x
      rw [BinaryCircuit.eval, BinaryCircuit.wires]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      · show ((List.ofFn x).getD 0 false ^^ (List.ofFn x).getD 1 false) = (x 0 ^^ x 1)
        simp
      · simp
