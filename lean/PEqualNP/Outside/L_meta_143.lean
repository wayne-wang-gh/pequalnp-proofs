import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_143_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Inputs := Fin 3 → Bool
abbrev Wire := Inputs → Bool

def Fits (k : ℕ) (f : Wire) : Prop :=
  ∃ S : Finset (Fin 3), S.card ≤ k ∧
    ∀ x y : Inputs, (∀ i ∈ S, x i = y i) → f x = f y

lemma fits_mono {k l : ℕ} {f : Wire} (hk : k ≤ l) (hf : Fits k f) : Fits l f := by
  obtain ⟨S, hS, hagree⟩ := hf
  exact ⟨S, hS.trans hk, hagree⟩

lemma fits_const (k : ℕ) (b : Bool) : Fits k (fun _ => b) :=
  ⟨∅, by simp, fun _ _ _ => rfl⟩

lemma fits_input (i : Fin 3) : Fits 1 (fun x => x i) :=
  ⟨{i}, by simp, fun _ _ h => h i (by simp)⟩

lemma fits_unary {k : ℕ} {f : Wire} (hf : Fits k f) (op : Bool → Bool) :
    Fits k (fun x => op (f x)) := by
  obtain ⟨S, hS, hagree⟩ := hf
  exact ⟨S, hS, fun x y h => congrArg op (hagree x y h)⟩

lemma fits_binary {k : ℕ} {f g : Wire} (hf : Fits k f) (hg : Fits k g)
    (op : Bool → Bool → Bool) : Fits (k + k) (fun x => op (f x) (g x)) := by
  obtain ⟨S, hS, hfs⟩ := hf
  obtain ⟨T, hT, hgt⟩ := hg
  refine ⟨S ∪ T, (Finset.card_union_le S T).trans (Nat.add_le_add hS hT), ?_⟩
  intro x y h
  change op (f x) (g x) = op (f y) (g y)
  rw [hfs x y (fun i hi => h i (Finset.mem_union_left T hi)),
      hgt x y (fun i hi => h i (Finset.mem_union_right S hi))]

def AllFit (k : ℕ) (ws : List Wire) : Prop := ∀ w ∈ ws, Fits k w

def read (ws : List Wire) (i : ℕ) : Wire := ws.getD i (fun _ => false)

lemma read_fits {k : ℕ} {ws : List Wire} (h : AllFit k ws) (i : ℕ) :
    Fits k (read ws i) := by
  induction ws generalizing i with
  | nil => exact fits_const k false
  | cons w rest ih =>
    cases i with
    | zero => exact h w List.mem_cons_self
    | succ i => exact ih (fun v hv => h v (List.mem_cons_of_mem w hv)) i

def initial : List Wire := [fun x => x 0, fun x => x 1, fun x => x 2]

lemma initial_fits : AllFit 1 initial := by
  intro w hw
  simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  all_goals exact fits_input _

def gateValue (ws : List Wire) (g : Gate) : Wire :=
  fun x => g.op.eval (g.inputs.map fun i => read ws i x)

def step (ws : List Wire) (g : Gate) : List Wire := ws ++ [gateValue ws g]

lemma gateValue_fits {k : ℕ} {ws : List Wire} (h : AllFit k ws) (g : Gate)
    (hlen : g.inputs.length ≤ 2) : Fits (k + k) (gateValue ws g) := by
  rcases g with ⟨op, inputs⟩
  cases inputs with
  | nil => exact fits_const (k + k) (op.eval [])
  | cons i rest =>
    cases rest with
    | nil =>
      exact fits_mono (Nat.le_add_right k k)
        (fits_unary (read_fits h i) (fun a => op.eval [a]))
    | cons j rest =>
      have hrest : rest = [] := List.length_eq_zero_iff.mp (by simp at hlen ⊢; omega)
      subst rest
      exact fits_binary (read_fits h i) (read_fits h j) (fun a b => op.eval [a, b])

lemma notValue_fits {k : ℕ} {ws : List Wire} (h : AllFit k ws) (g : Gate)
    (hop : g.op = .not) : Fits k (gateValue ws g) := by
  rcases g with ⟨op, inputs⟩
  change op = .not at hop
  subst op
  cases inputs with
  | nil => exact fits_const _ _
  | cons i rest => exact fits_unary (read_fits h i) Bool.not

lemma step_fits {k l : ℕ} {ws : List Wire} {g : Gate} (h : AllFit k ws)
    (hkl : k ≤ l) (hg : Fits l (gateValue ws g)) : AllFit l (step ws g) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact fits_mono hkl (h w hw)
  · rwa [List.mem_singleton.mp hw]

lemma step_map (x : Inputs) (ws : List Wire) (g : Gate) :
    (step ws g).map (fun f => f x) =
      (ws.map fun f => f x) ++ [g.op.eval (g.inputs.map fun i =>
        (ws.map fun f => f x).getD i false)] := by
  have h : (g.inputs.map fun i => read ws i x) =
      (g.inputs.map fun i => (ws.map fun f => f x).getD i false) := by
    apply List.map_congr_left
    intro i _
    exact (List.getD_map ws (fun _ => false) (fun f => f x)).symm
  simp [step, gateValue, h]

lemma fold_map (gs : List Gate) (ws : List Wire) (x : Inputs) :
    (gs.foldl step ws).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws.map fun f => f x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g rest ih => simp only [List.foldl_cons, ih, step_map]

lemma run_eq (C : Circuit) : read (C.gates.foldl step initial) C.output = circuitFun 3 C := by
  funext x
  have h := List.getD_map (C.gates.foldl step initial) (fun _ => false)
    (n := C.output) (fun f => f x)
  rw [fold_map] at h
  exact h.symm

lemma circuit_fits {k : ℕ} (C : Circuit) (h : AllFit k (C.gates.foldl step initial)) :
    Fits k (circuitFun 3 C) := by
  rw [← run_eq]
  exact read_fits h C.output

def path (x : Inputs) : Bool := (x 0 && x 1) || (x 1 && x 2)

lemma path_not_fits : ¬ Fits 2 path := by
  intro h
  obtain ⟨S, hS, hagree⟩ := h
  have hmiss : ¬ ∀ i : Fin 3, i ∈ S := by
    intro hall
    have hcard : S.card = 3 := by simp [Finset.eq_univ_of_forall hall]
    omega
  obtain ⟨k, hk⟩ := not_forall.mp hmiss
  let x : Inputs := fun i => decide (i = (if k = 1 then 0 else 1))
  let y : Inputs := fun i => x i || decide (i = k)
  have heq := hagree x y (by
    intro i hi
    have hik : i ≠ k := fun e => hk (e ▸ hi)
    simp [y, hik])
  have hx : path x = false := by
    fin_cases k <;> decide
  have hy : path y = true := by
    fin_cases k <;> decide
  rw [hx, hy] at heq
  exact Bool.noConfusion heq

def pathCircuit : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 3]⟩], 4⟩

lemma pathCircuit_fanin : FanInTwo pathCircuit := by
  intro g hg
  simp only [pathCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  all_goals simp

lemma pathCircuit_computes : circuitFun 3 pathCircuit = path := by
  funext x
  have bits : List.ofFn x = [x 0, x 1, x 2] := rfl
  unfold circuitFun Circuit.eval Circuit.wires pathCircuit path
  rw [bits]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> simp [GateOp.eval]

lemma minimal_path (C : Circuit) (hmin : IsMinimalCircuit 3 C) (hpath : circuitFun 3 C = path) :
    C.size = 2 ∧ ∀ g ∈ C.gates, g.op ≠ .not := by
  have hsize : C.size ≤ 2 := hmin.2 pathCircuit pathCircuit_fanin (pathCircuit_computes.trans hpath.symm)
  have bad : ¬ Fits 2 (circuitFun 3 C) := hpath.symm ▸ path_not_fits
  rcases C with ⟨gates, output⟩
  cases gates with
  | nil =>
    exact (bad (circuit_fits _ (fun w hw => fits_mono (by decide : 1 ≤ 2) (initial_fits w hw)))).elim
  | cons g tail =>
    have h1 := (hmin.1 g (by simp)).2
    have hg : AllFit 2 (step initial g) :=
      step_fits initial_fits (by decide) (gateValue_fits initial_fits g h1)
    cases tail with
    | nil => exact (bad (circuit_fits _ hg)).elim
    | cons h tail =>
      have htail : tail = [] := List.length_eq_zero_iff.mp (by
        change tail.length + 1 + 1 ≤ 2 at hsize
        omega)
      subst tail
      refine ⟨rfl, ?_⟩
      intro w hw hnot
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hw | hw
      · subst w
        have first : AllFit 1 (step initial g) :=
          step_fits initial_fits (Nat.le_refl _) (notValue_fits initial_fits g hnot)
        have h2 := (hmin.1 h (by simp)).2
        have second : AllFit 2 (step (step initial g) h) :=
          step_fits first (by decide : 1 ≤ 2) (gateValue_fits first h h2)
        exact bad (circuit_fits _ second)
      · subst w
        exact bad (circuit_fits _ (step_fits hg (Nat.le_refl _) (notValue_fits hg h hnot)))

end PEqualNP.Outside.L_meta_143_aux

theorem PEqualNP.Outside.L_meta_143 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 3 C → PEqualNP.MetaComplexity.circuitFun 3 C = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2)) → C.size = 2 ∧ ∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not :=
  PEqualNP.Outside.L_meta_143_aux.minimal_path
