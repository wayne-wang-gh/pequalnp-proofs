import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_904_aux

namespace GraphFacts

open Finset

abbrev SquareFree904 {n : ℕ} (G : SimpleGraph (Fin n)) :=
  ∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a

private abbrev weight {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) : ℕ :=
  if G.Adj i j then 1 else 0

private def arcs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S T : Finset (Fin n)) : ℕ :=
  ∑ i ∈ S, ∑ j ∈ T, weight G i j

private theorem arc_symm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S T : Finset (Fin n)) :
    arcs G S T = arcs G T S := by
  unfold arcs
  rw [Finset.sum_comm]
  exact sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => by simp only [weight,G.adj_comm b a]))

private theorem arc_add {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {A B : Finset (Fin n)}
    (hd : Disjoint A B) (T : Finset (Fin n)) : arcs G (A ∪ B) T = arcs G A T + arcs G B T :=
  sum_union hd

private theorem arc_add_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    {A B : Finset (Fin n)} (hd : Disjoint A B) : arcs G T (A ∪ B) = arcs G T A + arcs G T B := by
  rw [arc_symm G T _,arc_add G hd,arc_symm G A T,arc_symm G B T]

private theorem edges_arcs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card = arcs G univ univ := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  apply sum_congr rfl
  intro i _
  rw [← G.card_neighborFinset_eq_degree,G.neighborFinset_eq_filter]
  simp [weight,Finset.sum_boole]

noncomputable def induced904 {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Fin S.card) := G.comap (fun i => (S.equivFin.symm i).val)

private theorem induced_square {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (h4 : SquareFree904 G) :
    SquareFree904 (induced904 G S) := by
  intro a b c d hac hbd hab hbc hcd hda
  let f := fun i : Fin S.card => (S.equivFin.symm i).val
  have inj : Function.Injective f := Subtype.val_injective.comp S.equivFin.symm.injective
  exact h4 (f a) (f b) (f c) (f d) (fun e => hac (inj e)) (fun e => hbd (inj e)) hab hbc hcd hda

private theorem induced_arcs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) [DecidableRel (induced904 G S).Adj] :
    2 * (induced904 G S).edgeFinset.card = arcs G S S := by
  classical
  rw [edges_arcs,arcs,arcs]
  have conv (f : Fin n → ℕ) : (∑ i : Fin S.card, f (S.equivFin.symm i).val) = ∑ i ∈ S, f i := by
    rw [← Finset.sum_attach S f]
    exact Fintype.sum_equiv S.equivFin.symm _ _ (fun _ => rfl)
  have eq (a b : Fin S.card) : weight (induced904 G S) a b = weight G (S.equivFin.symm a).val (S.equivFin.symm b).val := by
    simp only [weight,induced904,SimpleGraph.comap_adj]
  simp_rw [eq, conv]
  exact conv (fun i => ∑ j ∈ S, weight G i j)

section

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)

private theorem neigh_disj : Disjoint ({v} : Finset (Fin n)) (G.neighborFinset v) := by simp

private theorem outside_disj : Disjoint (insert v (G.neighborFinset v)) ((insert v (G.neighborFinset v))ᶜ) := disjoint_compl_right

private theorem outside_card : (((insert v (G.neighborFinset v))ᶜ)).card + ((G.neighborFinset v)).card + 1 = n := by
  have h := card_compl_add_card (insert v (G.neighborFinset v))
  simp only [Finset.card_insert_of_notMem (show v ∉ (G.neighborFinset v) from by simp), Fintype.card_fin] at h
  omega

omit [DecidableRel G.Adj] in
private theorem common_neigh_unique (h4 : SquareFree904 G) {x y u w : Fin n} (hxy : x ≠ y)
    (hxu : G.Adj x u) (hyu : G.Adj y u) (hxw : G.Adj x w) (hyw : G.Adj y w) : u = w := by
  by_contra hne
  exact h4 x u y w hxy hne hxu hyu.symm hyw hxw.symm

private theorem local_arc_bound (h4 : SquareFree904 G) (T : Finset (Fin n)) (hT : v ∉ T) :
    arcs G T (G.neighborFinset v) ≤ T.card := by
  calc
    arcs G T (G.neighborFinset v) ≤ ∑ _ ∈ T, 1 := by
      apply sum_le_sum
      intro u hu
      have cap : (((G.neighborFinset v)).filter (G.Adj u)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro x hx y hy
        obtain ⟨hx1,hx2⟩ := mem_filter.mp hx
        obtain ⟨hy1,hy2⟩ := mem_filter.mp hy
        exact common_neigh_unique G h4 (fun e : u = v => hT (e ▸ hu)) hx2 ((G.mem_neighborFinset _ _).mp hx1)
          hy2 ((G.mem_neighborFinset _ _).mp hy1)
      simpa [weight, Finset.sum_boole] using cap
    _ = _ := by simp


theorem split_at_vertex (h4 : SquareFree904 G) [DecidableRel (induced904 G ((insert v (G.neighborFinset v))ᶜ)).Adj] :
    2 * G.edgeFinset.card ≤ 2 * (n-1) + ((G.neighborFinset v)).card + 2 * (induced904 G ((insert v (G.neighborFinset v))ᶜ)).edgeFinset.card := by
  classical
  have hV : (univ : Finset (Fin n)) = (insert v (G.neighborFinset v)) ∪ ((insert v (G.neighborFinset v))ᶜ) := (Finset.union_compl _).symm
  have hi : insert v (G.neighborFinset v) = ({v} : Finset (Fin n)) ∪ (G.neighborFinset v) := by simp
  have z1 : arcs G {v} {v} = 0 := by simp [arcs,weight]
  have z2 : arcs G {v} ((insert v (G.neighborFinset v))ᶜ) = 0 := by
    simp only [arcs,sum_singleton]
    apply sum_eq_zero
    intro a ha
    have hna : a ∉ (G.neighborFinset v) := fun h => (mem_compl.mp ha) (mem_insert_of_mem h)
    exact ite_eq_right (fun h => hna ((G.mem_neighborFinset _ _).mpr h))
  have dv : arcs G {v} (G.neighborFinset v) = ((G.neighborFinset v)).card := by
    unfold arcs
    simp only [sum_singleton]
    rw [Finset.sum_congr rfl (g:=fun _ => (1 : ℕ)) (fun x hx => ite_eq_left ((G.mem_neighborFinset _ _).mp hx))]
    simp
  have NN := local_arc_bound G v h4 (G.neighborFinset v) (by simp)
  have RR := local_arc_bound G v h4 ((insert v (G.neighborFinset v))ᶜ) (by simp)
  have rev : arcs G (G.neighborFinset v) {v} = arcs G {v} (G.neighborFinset v) := arc_symm ..
  have rN : arcs G (G.neighborFinset v) ((insert v (G.neighborFinset v))ᶜ) = arcs G ((insert v (G.neighborFinset v))ᶜ) (G.neighborFinset v) := arc_symm ..
  have rV : arcs G ((insert v (G.neighborFinset v))ᶜ) {v} = arcs G {v} ((insert v (G.neighborFinset v))ᶜ) := arc_symm ..
  have add (T) : arcs G (insert v (G.neighborFinset v)) T = arcs G {v} T + arcs G (G.neighborFinset v) T := by
    rw [hi,arc_add G (neigh_disj G v)]
  have add' (T) : arcs G T (insert v (G.neighborFinset v)) = arcs G T {v} + arcs G T (G.neighborFinset v) := by
    rw [hi,arc_add_right G T (neigh_disj G v)]
  have eq := edges_arcs G
  rw [hV,arc_add G (outside_disj G v),arc_add_right G _ (outside_disj G v),
    arc_add_right G _ (outside_disj G v),add,add,add',add',add',z1,z2,dv,rev,dv,rN,rV,z2] at eq
  have rCard := outside_card G v
  have rem := induced_arcs G ((insert v (G.neighborFinset v))ᶜ)
  omega

end

end GraphFacts

namespace GraphFacts

open Finset

def Ebound : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 6
  | 6 => 7
  | 7 => 9
  | 8 => 11
  | 9 => 13
  | _ => 0

private def code4 (a b c d e f : Bool) (i j : Fin 4) : Bool :=
  match i.val, j.val with
  | 0,1 | 1,0 => a
  | 0,2 | 2,0 => b
  | 0,3 | 3,0 => c
  | 1,2 | 2,1 => d
  | 1,3 | 3,1 => e
  | 2,3 | 3,2 => f
  | _,_ => false

private theorem four_low : ∀ (a b c d e f : Bool),
    ¬(a && d && f && c) = true → ¬(a && e && f && b) = true → ¬(b && d && e && c) = true →
    ∃ i : Fin 4, ∀ j k : Fin 4,
      code4 a b c d e f i j = true → code4 a b c d e f i k = true → j=k := by decide

private theorem four_low_in {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : SquareFree904 G) (g : Fin 4 ↪ Fin n) :
    ∃ i : Fin 4, ∀ j k : Fin 4, G.Adj (g i) (g j) → G.Adj (g i) (g k) → j=k := by
  let b (i j : Fin 4) := decide (G.Adj (g i) (g j))
  have rel (i j : Fin 4) :
      code4 (b 0 1) (b 0 2) (b 0 3) (b 1 2) (b 1 3) (b 2 3) i j = true ↔ G.Adj (g i) (g j) := by
    fin_cases i <;> fin_cases j <;> simp [code4,b,SimpleGraph.adj_comm] <;> exact SimpleGraph.adj_comm _ _ _
  have no (i j k l : Fin 4) (hik : i≠k) (hjl : j≠l) :
      ¬ (G.Adj (g i) (g j) ∧ G.Adj (g j) (g k) ∧ G.Adj (g k) (g l) ∧ G.Adj (g l) (g i)) := by
    rintro ⟨h1,h2,h3,h4'⟩
    exact h4 _ _ _ _ (fun h => hik (g.injective h)) (fun h => hjl (g.injective h)) h1 h2 h3 h4'
  obtain ⟨i,h⟩ := four_low (b 0 1) (b 0 2) (b 0 3) (b 1 2) (b 1 3) (b 2 3)
    (by simpa [b, and_assoc, SimpleGraph.adj_comm] using no 0 1 2 3 (by decide) (by decide))
    (by simpa [b, and_assoc, SimpleGraph.adj_comm] using no 0 1 3 2 (by decide) (by decide))
    (by simpa [b, and_assoc, SimpleGraph.adj_comm] using no 0 2 1 3 (by decide) (by decide))
  exact ⟨i, fun j k hj hk => h j k ((rel i j).2 hj) ((rel i k).2 hk)⟩

private theorem outside_four_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : SquareFree904 G) (hm : ∀ w, 3 ≤ G.degree w) (v : Fin n) :
    n ≠ G.degree v + 5 := by
  classical
  intro hn
  let N := G.neighborFinset v
  let R := (insert v N)ᶜ
  have hc := outside_card G v
  change R.card + G.degree v + 1 = n at hc
  have hR : R.card = 4 := by omega
  let e : Fin 4 ≃ R := (finCongr hR.symm).trans R.equivFin.symm
  let g : Fin 4 ↪ Fin n := e.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨i,hi⟩ := four_low_in G h4 g
  let x := g i
  have hxR : x ∈ R := (e i).property
  obtain ⟨hxv,hxN⟩ := (show x ≠ v ∧ x ∉ N by simpa [R] using hxR)
  let U := G.neighborFinset x
  have h1 : (U ∩ N).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu z hz
    obtain ⟨hu,hu'⟩ := Finset.mem_inter.mp hu
    obtain ⟨hz,hz'⟩ := Finset.mem_inter.mp hz
    exact common_neigh_unique G h4 hxv (G.mem_neighborFinset x u|>.mp hu)
      (G.mem_neighborFinset v u|>.mp hu') (G.mem_neighborFinset x z|>.mp hz) (G.mem_neighborFinset v z|>.mp hz')
  have h2 : (U ∩ R).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu z hz
    obtain ⟨hu,hu'⟩ := Finset.mem_inter.mp hu
    obtain ⟨hz,hz'⟩ := Finset.mem_inter.mp hz
    let j := e.symm ⟨u,hu'⟩
    let k := e.symm ⟨z,hz'⟩
    have hj : g j = u := congrArg Subtype.val (e.apply_symm_apply ⟨u,hu'⟩)
    have hk : g k = z := congrArg Subtype.val (e.apply_symm_apply ⟨z,hz'⟩)
    have eq := hi j k (hj ▸ (G.mem_neighborFinset x u|>.mp hu)) (hk ▸ (G.mem_neighborFinset x z|>.mp hz))
    exact hj.symm.trans ((congrArg g eq).trans hk)
  have sub : U ⊆ (U ∩ N) ∪ (U ∩ R) := by
    intro u hu
    by_cases h : u ∈ N
    · exact mem_union_left _ (mem_inter.mpr ⟨hu,h⟩)
    · have huv : u ≠ v := by
        intro huv
        subst u
        exact hxN ((G.mem_neighborFinset v x).mpr ((G.mem_neighborFinset x v).mp hu).symm)
      exact mem_union_right _ (mem_inter.mpr ⟨hu,by simpa [R] using And.intro huv h⟩)
  have h := (card_le_card sub).trans (card_union_le _ _)
  change G.degree x ≤ _ at h
  have := hm x
  omega

private theorem erase_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
    [DecidableRel (induced904 G (univ.erase v)).Adj] :
    G.edgeFinset.card = (induced904 G (univ.erase v)).edgeFinset.card + G.degree v := by
  classical
  let S := (univ : Finset (Fin n)).erase v
  have hU : (univ : Finset (Fin n)) = {v} ∪ S := by ext a; by_cases h : a = v <;> simp [S,h]
  have hd : Disjoint ({v} : Finset (Fin n)) S := by simp [S]
  have hz : arcs G {v} {v} = 0 := by simp [arcs,weight]
  have he : arcs G {v} univ = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree,G.neighborFinset_eq_filter]
    simp [arcs,weight]
  have hs : arcs G {v} S = G.degree v := by
    rw [hU, arc_add_right G _ hd,hz,zero_add] at he; exact he
  have hr := arc_symm G S {v}
  have h := edges_arcs G
  rw [hU, arc_add G hd,arc_add_right G _ hd,arc_add_right G _ hd,hz,hr,hs] at h
  have hm := induced_arcs G S
  change 2 * (induced904 G (univ.erase v)).edgeFinset.card = _ at hm
  omega

private theorem num_small_ext : ∀ N D : Fin 10, ∀ M : Fin 46,
    let n := N.val
    let d := D.val
    let m := M.val
    d < n → 2*m ≤ n*d → 2*m ≤ 2*(n-1)+d+2*Ebound (n-1-d) →
    (m ≤ Ebound (n-1)+2 ∨ (3*(n-1)+d ≤ 2*m ∧ n≠d+5)) →
    m ≤ Ebound n := by decide

theorem small_ext_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : n ≤ 9)
    (h4 : SquareFree904 G) : G.edgeFinset.card ≤ Ebound n := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases nz : n=0
    · subst n
      exact G.card_edgeFinset_le_card_choose_two.trans (by decide)
    obtain ⟨v,hv,maxv⟩ := Finset.exists_max_image (univ : Finset (Fin n)) (fun i => G.degree i)
      ⟨⟨0,by omega⟩,mem_univ _⟩
    let d := G.degree v
    let m := G.edgeFinset.card
    have hdn : d<n := by simpa [d] using G.degree_lt_card_verts v
    have hupper : 2*m ≤ n*d := by
      change 2*G.edgeFinset.card ≤ _
      rw [← G.sum_degrees_eq_twice_card_edges]
      have := sum_le_sum (s:=univ) (g:=fun _ => d) (fun x hx => maxv x hx)
      simpa [Nat.mul_comm] using this
    let R := (insert v (G.neighborFinset v))ᶜ
    have hR := outside_card G v
    have hRc : R.card = n-1-d := by change R.card + d + 1 = n at hR; omega
    have hRlt : R.card<n := by omega
    have hRI := ih R.card hRlt (induced904 G R) (by omega) (induced_square G R h4)
    have hs := split_at_vertex G v h4
    change 2*m ≤ 2*(n-1)+d+2*(induced904 G R).edgeFinset.card at hs
    have hroot : 2*m ≤ 2*(n-1)+d+2*Ebound (n-1-d) := by rw [← hRc]; omega
    have hcases : m ≤ Ebound (n-1)+2 ∨ (3*(n-1)+d ≤ 2*m ∧ n≠d+5) := by
      by_cases hlow : ∃ u, G.degree u ≤ 2
      · obtain ⟨u,hu⟩ := hlow
        let S := (univ : Finset (Fin n)).erase u
        have hS : S.card = n-1 := by simp [S]
        have hSl : S.card < n := by omega
        have hSI := ih S.card hSl (induced904 G S) (by omega) (induced_square G S h4)
        have hE := erase_edge_bound G u
        change m = (induced904 G S).edgeFinset.card + G.degree u at hE
        left; rw [← hS]; omega
      · push Not at hlow
        refine Or.inr ⟨?_,outside_four_impossible G h4 (fun w => by have := hlow w; omega) v⟩
        have hsum : (∑ _u ∈ (univ.erase v), (3 : ℕ)) ≤ ∑ u ∈ (univ.erase v), G.degree u :=
          sum_le_sum (fun u _ => by have := hlow u; omega)
        have rem := Finset.sum_erase_add (s:=univ) (fun i => G.degree i) (mem_univ v)
        have full := G.sum_degrees_eq_twice_card_edges
        have hval : (∑ _u ∈ (univ.erase v), (3 : ℕ)) = 3*(n-1) := by simp [Nat.mul_comm]
        omega
    have hprod : n*d ≤ 9*9 := Nat.mul_le_mul hn (by omega)
    exact num_small_ext ⟨n,by omega⟩ ⟨d,by omega⟩ ⟨m,by omega⟩ hdn hupper hroot hcases

end GraphFacts

namespace Regular904

open Finset

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private def NoSquare : Prop :=
  ∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a

private def second (v u : Fin n) : Finset (Fin n) := (G.neighborFinset u).erase v

private theorem second_disjoint (h4 : NoSquare G) (v : Fin n) :
    ((G.neighborFinset v : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (second G v) := by
  intro u hu w hw hne
  refine Finset.disjoint_left.mpr ?_
  intro z hz hz'
  obtain ⟨hzv, huz⟩ := Finset.mem_erase.mp hz
  obtain ⟨_, hwz⟩ := Finset.mem_erase.mp hz'
  exact h4 v u z w hzv.symm hne (G.mem_neighborFinset _ _ |>.mp hu)
    (G.mem_neighborFinset _ _ |>.mp huz) (G.mem_neighborFinset _ _ |>.mp hwz).symm
    (G.mem_neighborFinset _ _ |>.mp hw).symm

private theorem second_card (h4 : NoSquare G) (v : Fin n) :
    ((G.neighborFinset v).biUnion (second G v)).card =
      ∑ u ∈ G.neighborFinset v, ((G.neighborFinset u).card - 1) := by
  rw [Finset.card_biUnion (second_disjoint G h4 v)]
  apply Finset.sum_congr rfl
  intro u hu
  exact Finset.card_erase_of_mem (G.mem_neighborFinset _ _ |>.mpr (G.mem_neighborFinset _ _ |>.mp hu).symm)

private theorem second_subset (v : Fin n) :
    (G.neighborFinset v).biUnion (second G v) ⊆ Finset.univ.erase v := by
  intro z hz
  obtain ⟨u, _, hzu⟩ := mem_biUnion.mp hz
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hzu).1, Finset.mem_univ _⟩


theorem four_regular (h4 : NoSquare G) (hn : n ≤ 15)
    (hmin : ∀ v, 4 ≤ (G.neighborFinset v).card) :
    ∀ v, (G.neighborFinset v).card = 4 ∧ 13 ≤ n := by
  intro v
  have hcap := Finset.card_le_card (second_subset G v)
  rw [second_card G h4 v, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin] at hcap
  have hsum : (G.neighborFinset v).card * 3 ≤ ∑ u ∈ G.neighborFinset v,
      ((G.neighborFinset u).card - 1) := by
    calc
      _ = ∑ _ ∈ G.neighborFinset v, 3 := by simp
      _ ≤ _ := Finset.sum_le_sum fun u _ => by have := hmin u; omega
  have := hmin v
  omega


theorem neighbors_in_triangle (h4 : NoSquare G) (hn : n ≤ 14)
    (hdeg : ∀ v, (G.neighborFinset v).card = 4) (v : Fin n) :
    3 ≤ ((G.neighborFinset v) ∩ (G.neighborFinset v).biUnion (second G v)).card := by
  let N := G.neighborFinset v
  let P := N.biUnion (second G v)
  have hN : N.card = 4 := hdeg v
  have hP : P.card = 12 := by
    change ((G.neighborFinset v).biUnion (second G v)).card = 12
    rw [second_card G h4 v]
    simp [hdeg]
  have hcap : (N ∪ P).card ≤ n - 1 := by
    have hsub : N ∪ P ⊆ Finset.univ.erase v := Finset.union_subset (by
      intro z hz
      exact Finset.mem_erase.mpr ⟨(G.mem_neighborFinset _ _ |>.mp hz).ne.symm, mem_univ _⟩)
      (second_subset G v)
    simpa [Finset.card_erase_of_mem (Finset.mem_univ v)] using Finset.card_le_card hsub
  have eq := Finset.card_union_add_card_inter N P
  change 3 ≤ (N ∩ P).card
  omega


omit [DecidableRel G.Adj] in
private theorem common_unique (h4 : NoSquare G) {a b u v : Fin n} (hab : a ≠ b)
    (hau : G.Adj a u) (hbu : G.Adj b u) (hav : G.Adj a v) (hbv : G.Adj b v) : u = v := by
  by_contra hne
  exact h4 a u b v hab hne hau hbu.symm hbv hav.symm

private theorem degree_square_sum (h4 : NoSquare G) :
    (∑ v : Fin n, G.degree v ^ 2) ≤ n * n - n + ∑ v : Fin n, G.degree v := by
  classical
  let F : Finset (Σ _ : Fin n, Fin n × Fin n) := univ.sigma fun v => (G.neighborFinset v).offDiag
  have bound : F.card ≤ (univ : Finset (Fin n)).offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun p => p.2)
    · intro p hp
      have d := (Finset.mem_offDiag.mp (Finset.mem_sigma.mp hp).2).2.2
      exact Finset.mem_offDiag.mpr ⟨mem_univ _, mem_univ _, d⟩
    · intro ⟨u,a,b⟩ hu ⟨v,c,d⟩ hv heq
      change (a,b) = (c,d) at heq
      cases heq
      obtain ⟨aU,bU,ab⟩ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hu).2
      obtain ⟨aV,bV,_⟩ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hv).2
      have h := common_unique G h4 ab ((G.mem_neighborFinset _ _).mp aU).symm
        ((G.mem_neighborFinset _ _).mp bU).symm ((G.mem_neighborFinset _ _).mp aV).symm
        ((G.mem_neighborFinset _ _).mp bV).symm
      cases h
      rfl
  have decomp : (∑ v : Fin n, G.degree v ^ 2) = F.card + ∑ v : Fin n, G.degree v := by
    simp only [F, Finset.card_sigma, Finset.offDiag_card, G.card_neighborFinset_eq_degree, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [Nat.sub_add_cancel (Nat.le_mul_self _), pow_two]
  rw [decomp]
  apply Nat.add_le_add_right
  simpa using bound.trans_eq (by rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin])

private theorem edge_in_triangle_if_regular13 (h4 : NoSquare G) (hn : n = 13)
    (hdeg : ∀ v, (G.neighborFinset v).card = 4) {a b : Fin n} (hab : G.Adj a b) :
    ∃ c, G.Adj a c ∧ G.Adj b c := by
  let P := (G.neighborFinset a).biUnion (second G a)
  have hh : P.card = 12 := by
    change ((G.neighborFinset a).biUnion (second G a)).card = 12
    rw [second_card G h4 a]
    simp [hdeg]
  have eq : P = (univ : Finset (Fin n)).erase a := by
    apply Finset.eq_of_subset_of_card_le (second_subset G a)
    rw [hh, Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, Fintype.card_fin, hn]
  have hb : b ∈ P := by
    rw [eq]
    exact Finset.mem_erase.mpr ⟨hab.ne.symm,mem_univ _⟩
  obtain ⟨c,hca,hbc⟩ := Finset.mem_biUnion.mp hb
  exact ⟨c,(G.mem_neighborFinset _ _).mp hca,((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hbc).2).symm⟩

private theorem directed_edge_count_3dvd (h4 : NoSquare G)
    (htri : ∀ {a b : Fin n}, G.Adj a b → ∃ c, G.Adj a c ∧ G.Adj b c) :
    3 ∣ 2 * G.edgeFinset.card := by
  classical
  let T := G.cliqueFinset 3
  have hinj : (T : Set (Finset (Fin n))).PairwiseDisjoint Finset.offDiag := by
    intro S hS U hU hne
    apply Finset.disjoint_left.mpr
    intro ⟨a,b⟩ habS habU
    apply hne
    obtain ⟨haS,hbS,ab⟩ := Finset.mem_offDiag.mp habS
    obtain ⟨haU,hbU,_⟩ := Finset.mem_offDiag.mp habU
    have cs := (SimpleGraph.mem_cliqueFinset_iff.mp hS : G.IsNClique 3 S)
    have cu := (SimpleGraph.mem_cliqueFinset_iff.mp hU : G.IsNClique 3 U)
    have hUextra : ∃ d ∈ U, d ≠ a ∧ d ≠ b := by
      by_contra! ht
      have hsub : U ⊆ ({a,b} : Finset (Fin n)) := by
        intro c hc
        rcases eq_or_ne c a with rfl | h
        · simp
        · have e := ht c hc h
          subst c
          simp
      have hc := card_le_card hsub
      rw [cu.card_eq] at hc
      simp [ab] at hc
    obtain ⟨d,hd,ha,hb⟩ := hUextra
    apply Finset.eq_of_subset_of_card_le ?_ (by rw [cs.card_eq, cu.card_eq])
    intro c hc
    by_cases ca : c = a
    · rwa [ca]
    by_cases cb : c = b
    · rwa [cb]
    have eq := common_unique G h4 ab (cs.isClique haS hc (Ne.symm ca)) (cs.isClique hbS hc (Ne.symm cb))
      (cu.isClique haU hd ha.symm) (cu.isClique hbU hd hb.symm)
    rwa [eq]
  have hcover : T.biUnion Finset.offDiag = univ.filter (fun ab : Fin n × Fin n => G.Adj ab.1 ab.2) := by
    ext p
    obtain ⟨a,b⟩ := p
    constructor
    · intro h
      obtain ⟨S,hS,hab⟩ := Finset.mem_biUnion.mp h
      obtain ⟨ha,hb,ab⟩ := Finset.mem_offDiag.mp hab
      exact mem_filter.mpr ⟨mem_univ _, (SimpleGraph.mem_cliqueFinset_iff.mp hS).isClique ha hb ab⟩
    · intro h
      have hab : G.Adj a b := (mem_filter.mp h).2
      obtain ⟨c,hac,hbc⟩ := htri hab
      refine Finset.mem_biUnion.mpr ⟨{a,b,c}, SimpleGraph.mem_cliqueFinset_iff.mpr ?_, ?_⟩
      · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩
      · exact Finset.mem_offDiag.mpr ⟨by simp,by simp,hab.ne⟩
  rw [G.two_mul_card_edgeFinset, ← hcover, Finset.card_biUnion hinj]
  have hsum : (∑ t ∈ T, t.offDiag.card) = T.card * 6 := by
    calc
      _ = ∑ _ ∈ T, 6 := Finset.sum_congr rfl fun t ht => by
        rw [Finset.offDiag_card, (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq]
      _ = _ := by simp
  rw [hsum]
  omega


theorem sparse_thirteen (h4 : NoSquare G) (hn0 : 0 < n) (hn13 : n ≤ 13) :
    G.edgeFinset.card < 2*n := by
  by_contra! hm
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hnsub : n ≤ n*n := by nlinarith [hn0]
  have hs := degree_square_sum G h4
  have hs' : (∑ v : Fin n, (G.degree v : ℤ)^2) ≤ (n:ℤ)*(n:ℤ) - n + ∑ v : Fin n, (G.degree v:ℤ) := by
    have hz := (show (n:ℤ) ≤ n*n by exact_mod_cast hnsub)
    exact_mod_cast hs
  have hsum' : (∑ v : Fin n, (G.degree v : ℤ)) = 2*(G.edgeFinset.card : ℤ) := by exact_mod_cast hsum
  have nonneg : 0 ≤ ∑ v : Fin n, ((G.degree v : ℤ)-4)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have form : (∑ v : Fin n, ((G.degree v : ℤ) - 4)^2) =
      (∑ v : Fin n, (G.degree v : ℤ)^2) - 8*(∑ v : Fin n, (G.degree v : ℤ)) + 16*n := by
    calc
      _ = ∑ v : Fin n, ((G.degree v : ℤ)^2 - 8*(G.degree v : ℤ) + 16) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]
  have hm' : 2 * (n:ℤ) ≤ G.edgeFinset.card := by exact_mod_cast hm
  have ub : (∑ v : Fin n, ((G.degree v : ℤ)-4)^2) ≤ (n:ℤ)*((n:ℤ)-13) := by linarith only [hs',hsum',form,hm']
  have heq : n = 13 := by
    by_contra ne
    have hneg : (n:ℤ) * ((n:ℤ)-13) < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hn0) (by omega)
    omega
  have hnz : (n:ℤ)*((n:ℤ)-13) = 0 := by rw [heq]; norm_num
  rw [hnz] at ub
  have zeros : (∑ v : Fin n, ((G.degree v : ℤ)-4)^2) = 0 := le_antisymm ub nonneg
  have degree4 (v : Fin n) : (G.neighborFinset v).card = 4 := by
    have hv := (Finset.sum_eq_zero_iff_of_nonneg (fun (j : Fin n) _ => sq_nonneg ((G.degree j : ℤ)-4))).mp zeros v (mem_univ _)
    rw [sq, mul_eq_zero] at hv
    have hz : (G.degree v:ℤ) - 4 = 0 := hv.elim id id
    rw [G.card_neighborFinset_eq_degree]
    omega
  have good := directed_edge_count_3dvd G h4 (edge_in_triangle_if_regular13 G h4 heq degree4)
  have hnumber : 2 * G.edgeFinset.card = 52 := by
    rw [← hsum]
    simp [← G.card_neighborFinset_eq_degree, degree4, heq]
  rw [hnumber] at good
  omega

end Regular904

namespace Regular904
open Finset
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private theorem matched_neighborhood_even (h4 : NoSquare G) (v : Fin n) :
    Even ((G.neighborFinset v) ∩ (G.neighborFinset v).biUnion (second G v)).card := by
  classical
  let A := (G.neighborFinset v) ∩ (G.neighborFinset v).biUnion (second G v)
  have characterization (u : Fin n) : u ∈ A ↔ G.Adj v u ∧ ∃ w, G.Adj v w ∧ G.Adj u w := by
    simp only [A,mem_inter,mem_biUnion,second,mem_erase,G.mem_neighborFinset]
    constructor
    · rintro ⟨h,w,hw,_,hwu⟩
      exact ⟨h,w,hw,hwu.symm⟩
    · rintro ⟨h,w,hw,huw⟩
      exact ⟨h,w,hw,h.ne.symm,huw.symm⟩
  let H := G.induce (A : Set (Fin n))
  have one (u : A) : H.degree u = 1 := by
    rw [← H.card_neighborFinset_eq_degree]
    have vu := ((characterization u).mp u.property).1
    obtain ⟨w,vw,uw⟩ := ((characterization u).mp u.property).2
    let w' : A := ⟨w, (characterization w).mpr ⟨vw,u,vu,uw.symm⟩⟩
    have eq : H.neighborFinset u = {w'} := by
      ext y
      rw [H.mem_neighborFinset,mem_singleton]
      constructor
      · intro h
        exact Subtype.ext (common_unique G h4 vu.ne
          ((characterization y).mp y.property).1 h vw uw)
      · rintro rfl
        exact uw
    simp [eq]
  have hs := H.sum_degrees_eq_twice_card_edges
  simp only [one,Finset.sum_const,Finset.card_univ, nsmul_eq_mul,mul_one] at hs
  have hs' : A.card = 2 * H.edgeFinset.card := by simpa using hs
  exact ⟨H.edgeFinset.card,by change A.card = _; omega⟩

theorem no_regular_fourteen (h4 : NoSquare G) (hn : n=14)
    (degrees : ∀ v, (G.neighborFinset v).card = 4) : False := by
  have triangles {a b : Fin n} (ab : G.Adj a b) : ∃ c, G.Adj a c ∧ G.Adj b c := by
    let N := G.neighborFinset a
    let T := N ∩ N.biUnion (second G a)
    have he := matched_neighborhood_even G h4 a
    have hl := neighbors_in_triangle G h4 (by omega) degrees a
    have hu : T.card ≤ N.card := card_le_card inter_subset_left
    have hn4 : N.card = 4 := degrees a
    change Even T.card at he
    change 3 ≤ T.card at hl
    obtain ⟨j,hj⟩ := he
    have eq : T = N := Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
    have hb : b ∈ T := eq ▸ (G.mem_neighborFinset _ _).mpr ab
    obtain ⟨c,hc,hbc⟩ := mem_biUnion.mp (mem_inter.mp hb).2
    exact ⟨c,(G.mem_neighborFinset _ _).mp hc,((G.mem_neighborFinset _ _).mp (mem_erase.mp hbc).2).symm⟩
  have dvd := directed_edge_count_3dvd G h4 triangles
  have ec := G.sum_degrees_eq_twice_card_edges
  simp only [← G.card_neighborFinset_eq_degree,degrees,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,hn] at ec
  omega

end Regular904

namespace GraphFacts

def HasWitness {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop) : Prop :=
  ∃ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧
    ∀ a c : Fin n, a ∉ I → c ∉ I → G.Adj a c →
      (∃ i ∈ I, G.Adj a i ∧ D a i) ∨ (∃ i ∈ I, G.Adj c i ∧ D c i)

private abbrev stable {V : Type*} (G : SimpleGraph V) (S : Set V) :=
  ∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b

private abbrev hit {V : Type*} (G : SimpleGraph V) (D : V → V → Prop) (K : Set V) (v : V) :=
  ∃ u ∈ K, G.Adj v u ∧ D v u

private theorem hit_mono {V : Type*} {G : SimpleGraph V} {D : V → V → Prop}
    {K K' : Set V} {v : V} (h : K ⊆ K') (hv : hit G D K v) : hit G D K' v := by
  obtain ⟨u,hu,he⟩ := hv
  exact ⟨u,h hu,he⟩

private theorem bip_kernel {V : Type*} (G : SimpleGraph V) (D : V → V → Prop)
    (hor : ∀ a b, G.Adj a b → (D a b ↔ ¬D b a))
    (A B : Set V) (hA : stable G A) (hB : stable G B) :
    ∃ K : Set V, K ⊆ A ∪ B ∧ stable G K ∧ ∀ v ∈ A ∪ B, v ∉ K → hit G D K v := by
  classical
  let side (U T : Set V) : Set V := {v | v ∈ U ∧ ¬hit G D T v}
  have flip (U : Set V) {S T : Set V} (h : S ⊆ T) : side U T ⊆ side U S :=
    fun _ hv => ⟨hv.1, fun hs => hv.2 (hit_mono h hs)⟩
  let f : Set V →o Set V := ⟨fun X => side A (side B X), fun _ _ h => flip A (flip B h)⟩
  let X := f.lfp
  let Y := side B X
  have hx (v : V) : v ∈ X ↔ v ∈ A ∧ ¬hit G D Y v := by
    change v ∈ X ↔ v ∈ f X
    rw [f.map_lfp]
  have hy (v : V) : v ∈ Y ↔ v ∈ B ∧ ¬hit G D X v := Iff.rfl
  refine ⟨X ∪ Y, ?_, ?_, ?_⟩
  · rintro v (h|h)
    · exact Or.inl ((hx _).mp h).1
    · exact Or.inr ((hy _).mp h).1
  · have cross {u v : V} (hu : u ∈ X) (hv : v ∈ Y) (he : G.Adj u v) : False := by
      by_cases huv : D u v
      · exact ((hx _).mp hu).2 ⟨v,hv,he,huv⟩
      · exact ((hy _).mp hv).2 ⟨u,hu,he.symm,(hor v u he.symm).mpr huv⟩
    rintro u (hu|hu) v (hv|hv) he
    · exact hA u ((hx _).mp hu).1 v ((hx _).mp hv).1 he
    · exact cross hu hv he
    · exact cross hv hu he.symm
    · exact hB u ((hy _).mp hu).1 v ((hy _).mp hv).1 he
  · rintro v (hv|hv) hk
    · by_contra hn
      exact hk (Or.inl ((hx _).mpr ⟨hv,fun h => hn (hit_mono Set.subset_union_right h)⟩))
    · by_contra hn
      exact hk (Or.inr ((hy _).mpr ⟨hv,fun h => hn (hit_mono Set.subset_union_left h)⟩))

private theorem witness_of_except {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (K W : Set (Fin n)) (hk : stable G K) (hw : stable G W)
    (absorb : ∀ x, x ∉ W → x ∉ K → hit G D K x) : HasWitness G D := by
  classical
  refine ⟨K.toFinset, by simpa using hk, ?_⟩
  intro u v hu hv he
  have hu' : u ∉ K := by simpa using hu
  have hv' : v ∉ K := by simpa using hv
  by_cases huw : u ∈ W
  · have hn : v ∉ W := fun h => hw _ huw _ h he
    obtain ⟨a,ha,hae⟩ := absorb v hn hv'
    exact Or.inr ⟨a,by simpa using ha,hae⟩
  · obtain ⟨a,ha,hae⟩ := absorb u huw hu'
    exact Or.inl ⟨a,by simpa using ha,hae⟩

private theorem rest_bip {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (hor : ∀ a b, G.Adj a b → (D a b ↔ ¬D b a)) (c : Fin n → Fin 3) (k : Fin 3)
    (U : Set (Fin n)) (hu : ∀ x ∈ U, c x ≠ k)
    (hc : ∀ a ∈ U, ∀ b ∈ U, G.Adj a b → c a ≠ c b) :
    ∃ K : Set (Fin n), K ⊆ U ∧ stable G K ∧ ∀ x ∈ U, x ∉ K → hit G D K x := by
  obtain ⟨i,j,hij⟩ := (by decide : ∀ k : Fin 3, ∃ i j : Fin 3,
    ∀ d : Fin 3, d ≠ k → d = i ∨ d = j) k
  let part (z : Fin 3) := {x : Fin n | x ∈ U ∧ c x = z}
  have hs (z : Fin 3) : stable G (part z) :=
    fun a ha b hb he => hc a ha.1 b hb.1 he (ha.2.trans hb.2.symm)
  have split : part i ∪ part j = U := by
    ext x
    constructor
    · rintro (h|h) <;> exact h.1
    · intro hx
      exact (hij _ (hu x hx)).imp (fun h => ⟨hx,h⟩) (fun h => ⟨hx,h⟩)
  simpa [split] using bip_kernel G D hor (part i) (part j) (hs i) (hs j)

theorem of_three_colorable {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (hor : ∀ a b, G.Adj a b → (D a b ↔ ¬D b a)) (hc : G.Colorable 3) : HasWitness G D := by
  obtain ⟨c⟩ := hc
  obtain ⟨K,_,hk,h⟩ := rest_bip G D hor c 0 {x | c x ≠ 0} (fun _ hx => hx)
    (fun _ _ _ _ he => c.valid he)
  exact witness_of_except G D K {x | c x = 0} hk
    (fun _ ha _ hb he => c.valid he (ha.trans hb.symm)) (fun x hx => h x hx)

private theorem mono_color {V : Type*} (S : Finset V) (c : V → Fin 3) (h : S.card ≤ 1) :
    ∃ k : Fin 3, ∀ x ∈ S, c x = k := by
  by_cases hn : S.Nonempty
  · obtain ⟨a,ha⟩ := hn
    exact ⟨c a,fun x hx => congrArg c (Finset.card_le_one.mp h x hx a ha)⟩
  · exact ⟨0,fun x hx => (hn ⟨x,hx⟩).elim⟩

private theorem mono_orientation {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (hor : ∀ a b, G.Adj a b → (D a b ↔ ¬D b a)) (v : Fin n)
    (degree : (G.neighborSet v).ncard ≤ 3) (c : Fin n → Fin 3) :
    ∃ k : Fin 3, (∀ u, G.Adj v u → c u ≠ k → D u v) ∨
      (∀ u, G.Adj v u → c u ≠ k → D v u) := by
  classical
  let N := (G.neighborSet v).toFinset
  let O := N.filter (D v)
  have size : N.card ≤ 3 := by rwa [Set.ncard_eq_toFinset_card'] at degree
  by_cases small : O.card ≤ 1
  · obtain ⟨k,hk⟩ := mono_color O c small
    exact ⟨k,Or.inl (fun u he hn => (hor u v he.symm).mpr
      (fun h => hn (hk u (Finset.mem_filter.mpr ⟨by simpa [N] using he,h⟩))))⟩
  · have hcount := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (D v) N)
    have few : (N \ O).card ≤ 1 := by change (N \ O).card + O.card = N.card at hcount; omega
    obtain ⟨k,hk⟩ := mono_color (N \ O) c few
    refine ⟨k,Or.inr (fun u he hn => ?_)⟩
    by_contra hd
    exact hn (hk u (Finset.mem_sdiff.mpr ⟨by simpa [N] using he,fun h => hd (Finset.mem_filter.mp h).2⟩))

theorem of_oriented_coloring {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (hor : ∀ a b, G.Adj a b → (D a b ↔ ¬D b a)) (v : Fin n)
    (c : Fin n → Fin 3)
    (hc : ∀ a b, a ≠ v → b ≠ v → G.Adj a b → c a ≠ c b)
    (k : Fin 3) (side : (∀ u, G.Adj v u → c u ≠ k → D u v) ∨
      (∀ u, G.Adj v u → c u ≠ k → D v u)) : HasWitness G D := by
  classical
  let W := {x : Fin n | x ≠ v ∧ c x = k}
  have hw : stable G W := fun a ha b hb he => hc a b ha.1 hb.1 he (ha.2.trans hb.2.symm)
  rcases side with toward | away
  · let U := {x : Fin n | (x ≠ v ∧ c x ≠ k) ∧ ¬G.Adj v x}
    obtain ⟨K,hK,indep,absorb⟩ := rest_bip G D hor c k U (fun _ hx => hx.1.2)
      (fun _ ha _ hb he => hc _ _ ha.1.1 hb.1.1 he)
    have hkv : ∀ u ∈ K, ¬G.Adj v u := fun _ hu => (hK hu).2
    refine witness_of_except G D (insert v K) W ?_ hw ?_
    · rintro a (rfl|ha) b (rfl|hb) he
      · exact G.irrefl he
      · exact hkv b hb he
      · exact hkv a ha he.symm
      · exact indep a ha b hb he
    · intro x hxW hxK
      have hne : x ≠ v := fun e => hxK (Or.inl e)
      have hcol : c x ≠ k := fun e => hxW ⟨hne,e⟩
      by_cases he : G.Adj v x
      · exact ⟨v,Set.mem_insert _ _,he.symm,toward x he hcol⟩
      · exact hit_mono (Set.subset_insert v K) (absorb x ⟨⟨hne,hcol⟩,he⟩ (fun hx => hxK (Or.inr hx)))
  · let U := {x : Fin n | x ≠ v ∧ c x ≠ k}
    obtain ⟨K,hK,indep,absorb⟩ := rest_bip G D hor c k U (fun _ hx => hx.2)
      (fun _ ha _ hb he => hc _ _ ha.1 hb.1 he)
    by_cases adj : ∃ u ∈ K, G.Adj v u
    · obtain ⟨u,hu,he⟩ := adj
      apply witness_of_except G D K W indep hw
      intro x hxW hxK
      by_cases hv : x = v
      · subst x
        exact ⟨u,hu,he,away u he (hK hu).2⟩
      · exact absorb x ⟨hv,fun hh => hxW ⟨hv,hh⟩⟩ hxK
    · refine witness_of_except G D (insert v K) W ?_ hw ?_
      · rintro a (rfl|ha) b (rfl|hb) he
        · exact G.irrefl he
        · exact adj ⟨b,hb,he⟩
        · exact adj ⟨a,ha,he.symm⟩
        · exact indep a ha b hb he
      · intro x hxW hxK
        have hne : x ≠ v := fun e => hxK (Or.inl e)
        exact hit_mono (Set.subset_insert v K)
          (absorb x ⟨hne,fun hh => hxW ⟨hne,hh⟩⟩ (fun hx => hxK (Or.inr hx)))

theorem of_coloring_off {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (hor : ∀ a b, G.Adj a b → (D a b ↔ ¬D b a)) (v : Fin n)
    (degree : (G.neighborSet v).ncard ≤ 3) (c : Fin n → Fin 3)
    (hc : ∀ a b, a ≠ v → b ≠ v → G.Adj a b → c a ≠ c b) : HasWitness G D := by
  classical
  obtain ⟨k,side⟩ := mono_orientation G D hor v degree c
  exact of_oriented_coloring G D hor v c hc k side

end GraphFacts

namespace Reduction904

open Finset

variable {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)

private def WitnessOn (U I : Finset (Fin n)) : Prop :=
  I ⊆ U ∧ (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) ∧
  ∀ a ∈ U, ∀ b ∈ U, a ∉ I → b ∉ I → G.Adj a b →
    (∃ i ∈ I, G.Adj a i ∧ D a i) ∨ (∃ i ∈ I, G.Adj b i ∧ D b i)

private def Good (U : Finset (Fin n)) : Prop := ∃ I, WitnessOn G D U I

private theorem good_empty : Good G D ∅ := by
  refine ⟨∅, ?_⟩
  simp [WitnessOn]


theorem source_step (U : Finset (Fin n)) (v : Fin n) (hmem : v ∈ U)
    (hsource : ∀ a ∈ U, G.Adj v a → D v a)
    (h : Good G D (U.erase v)) : Good G D U := by
  classical
  obtain ⟨I, hsub, hind, hgood⟩ := h
  have hI : I ⊆ U := hsub.trans (Finset.erase_subset _ _)
  have hvI : v ∉ I := fun hv => (Finset.mem_erase.mp (hsub hv)).1 rfl
  by_cases touched : ∃ i ∈ I, G.Adj v i
  · obtain ⟨i, hi, hei⟩ := touched
    have habs : ∃ i ∈ I, G.Adj v i ∧ D v i := ⟨i, hi, hei, hsource i (hI hi) hei⟩
    refine ⟨I, hI, hind, ?_⟩
    intro a ha b hb haI hbI hab
    by_cases hav : a = v
    · subst a
      exact Or.inl habs
    by_cases hbv : b = v
    · subst b
      exact Or.inr habs
    exact hgood a (Finset.mem_erase.mpr ⟨hav, ha⟩) b (Finset.mem_erase.mpr ⟨hbv, hb⟩) haI hbI hab
  · refine ⟨insert v I, Finset.insert_subset hmem hI, ?_, ?_⟩
    · rintro a ha b hb he
      rcases Finset.mem_insert.mp ha with hav | ha <;> rcases Finset.mem_insert.mp hb with hbv | hb
      · subst a; subst b; exact he.ne rfl
      · subst a; exact touched ⟨b, hb, he⟩
      · subst b; exact touched ⟨a, ha, he.symm⟩
      · exact hind a ha b hb he
    · intro a ha b hb haI hbI hab
      have hane : a ≠ v := fun e => haI (e.symm ▸ Finset.mem_insert_self v I)
      have hbne : b ≠ v := fun e => hbI (e.symm ▸ Finset.mem_insert_self v I)
      have ha' : a ∈ U.erase v := Finset.mem_erase.mpr ⟨hane, ha⟩
      have hb' : b ∈ U.erase v := Finset.mem_erase.mpr ⟨hbne, hb⟩
      rcases hgood a ha' b hb' (fun hi => haI (Finset.mem_insert_of_mem hi))
        (fun hi => hbI (Finset.mem_insert_of_mem hi)) hab with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
      · exact .inl ⟨i, Finset.mem_insert_of_mem hi, h⟩
      · exact .inr ⟨i, Finset.mem_insert_of_mem hi, h⟩


theorem sink_step (U : Finset (Fin n)) (v : Fin n) (hmem : v ∈ U)
    (hsink : ∀ a ∈ U, G.Adj a v → D a v)
    [DecidableRel G.Adj]
    (h : Good G D (U.filter (fun a => a ≠ v ∧ ¬ G.Adj a v))) : Good G D U := by
  classical
  obtain ⟨I, hsub, hind, hgood⟩ := h
  have hI : I ⊆ U := hsub.trans (Finset.filter_subset _ _)
  have hsep : ∀ i ∈ I, i ≠ v ∧ ¬ G.Adj i v := fun i hi => (Finset.mem_filter.mp (hsub hi)).2
  refine ⟨insert v I, Finset.insert_subset hmem hI, ?_, ?_⟩
  · rintro a ha b hb he
    rcases Finset.mem_insert.mp ha with hav | ha <;> rcases Finset.mem_insert.mp hb with hbv | hb
    · subst a; subst b; exact he.ne rfl
    · subst a; exact (hsep b hb).2 he.symm
    · subst b; exact (hsep a ha).2 he
    · exact hind a ha b hb he
  · intro a ha b hb haI hbI hab
    by_cases hav : G.Adj a v
    · exact Or.inl ⟨v, Finset.mem_insert_self .., hav, hsink a ha hav⟩
    by_cases hbv : G.Adj b v
    · exact Or.inr ⟨v, Finset.mem_insert_self .., hbv, hsink b hb hbv⟩
    have hane : a ≠ v := fun e => haI (e.symm ▸ Finset.mem_insert_self v I)
    have hbne : b ≠ v := fun e => hbI (e.symm ▸ Finset.mem_insert_self v I)
    have ha' : a ∈ U.filter (fun x => x ≠ v ∧ ¬ G.Adj x v) := Finset.mem_filter.mpr ⟨ha, hane, hav⟩
    have hb' : b ∈ U.filter (fun x => x ≠ v ∧ ¬ G.Adj x v) := Finset.mem_filter.mpr ⟨hb, hbne, hbv⟩
    rcases hgood a ha' b hb' (fun hi => haI (Finset.mem_insert_of_mem hi))
        (fun hi => hbI (Finset.mem_insert_of_mem hi)) hab with ⟨i, hi, h⟩ | ⟨i, hi, h⟩
    · exact .inl ⟨i, Finset.mem_insert_of_mem hi, h⟩
    · exact .inr ⟨i, Finset.mem_insert_of_mem hi, h⟩



theorem unique_out_step (U : Finset (Fin n)) (v w : Fin n) (hmem : v ∈ U)
    (orient : ∀ a b, G.Adj a b → (D a b ↔ ¬ D b a))
    (only : ∀ a ∈ U, G.Adj v a → D v a → a = w)
    [DecidableRel G.Adj] [DecidableRel D]
    (h : ∃ I, WitnessOn G D (U.filter (fun a => a ≠ v ∧ ¬ (G.Adj a v ∧ D a v))) I ∧ w ∉ I) :
    Good G D U := by
  classical
  obtain ⟨I, ⟨hsub, hind, hgood⟩, hwi⟩ := h
  have hI : I ⊆ U := hsub.trans (Finset.filter_subset _ _)
  have hsep : ∀ i ∈ I, ¬ G.Adj v i := by
    intro i hi hv
    have notIn := (Finset.mem_filter.mp (hsub hi)).2.2
    have hdir : D v i := (orient v i hv).mpr fun h => notIn ⟨hv.symm, h⟩
    exact hwi ((only i (hI hi) hv hdir) ▸ hi)
  refine ⟨insert v I, Finset.insert_subset hmem hI, ?_, ?_⟩
  · intro a ha b hb he
    rcases Finset.mem_insert.mp ha with hav | ha <;> rcases Finset.mem_insert.mp hb with hbv | hb
    · subst a; subst b; exact he.ne rfl
    · subst a; exact hsep _ hb he
    · subst b; exact hsep _ ha he.symm
    · exact hind a ha b hb he
  · intro a ha b hb haI hbI hab
    by_cases hav : G.Adj a v ∧ D a v
    · exact Or.inl ⟨v, Finset.mem_insert_self .., hav⟩
    by_cases hbv : G.Adj b v ∧ D b v
    · exact Or.inr ⟨v, Finset.mem_insert_self .., hbv⟩
    have ha' : a ∈ U.filter (fun x => x ≠ v ∧ ¬ (G.Adj x v ∧ D x v)) := by
      exact Finset.mem_filter.mpr ⟨ha, fun e => haI (e.symm ▸ Finset.mem_insert_self v I), hav⟩
    have hb' : b ∈ U.filter (fun x => x ≠ v ∧ ¬ (G.Adj x v ∧ D x v)) := by
      exact Finset.mem_filter.mpr ⟨hb, fun e => hbI (e.symm ▸ Finset.mem_insert_self v I), hbv⟩
    rcases hgood a ha' b hb' (fun hi => haI (Finset.mem_insert_of_mem hi))
      (fun hi => hbI (Finset.mem_insert_of_mem hi)) hab with ⟨i, hi, hh⟩ | ⟨i, hi, hh⟩
    · exact Or.inl ⟨i, Finset.mem_insert_of_mem hi, hh⟩
    · exact Or.inr ⟨i, Finset.mem_insert_of_mem hi, hh⟩



theorem two_neighbor_witness [DecidableRel G.Adj] [DecidableRel D] (I : Finset (Fin n))
    (hind : ∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c)
    (orient : ∀ a c, G.Adj a c → (D a c ↔ ¬ D c a))
    (hin : ∀ c : Fin n, (univ.filter fun a => G.Adj a c ∧ D a c).card ≤ 2)
    (hdom : ∀ c : Fin n, c ∉ I → (I.filter fun a => G.Adj a c).card ≥ 2) :
    WitnessOn G D univ I := by
  classical
  refine ⟨subset_univ _, hind, ?_⟩
  intro a _ c _ ha hc he
  by_contra! h
  obtain ⟨haBlocked, hcBlocked⟩ := h
  have impossible (u v : Fin n) (hu : u ∉ I) (hv : v ∉ I)
      (hedge : G.Adj u v) (harc : D u v)
      (none : ∀ i ∈ I, G.Adj v i → ¬ D v i) : False := by
    let S := I.filter fun a => G.Adj a v
    have huS : u ∉ S := fun h => hu (Finset.mem_filter.mp h).1
    have hsub : insert u S ⊆ univ.filter fun a => G.Adj a v ∧ D a v := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hedge, harc⟩
      · obtain ⟨hxI, hxv⟩ := Finset.mem_filter.mp hx
        exact ⟨hxv, (orient x v hxv).mpr (none x hxI hxv.symm)⟩
    have cap := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem huS] at cap
    have low : 2 ≤ S.card := hdom v hv
    have up := hin v
    omega
  by_cases haDir : D a c
  · exact impossible a c ha hc he haDir hcBlocked
  · exact impossible c a hc ha he.symm ((orient c a he.symm).mpr haDir) haBlocked

end Reduction904

namespace Reduction904

open Finset

private abbrev SquareFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a

private abbrev Orientation {V : Type*} (G : SimpleGraph V) (D : V → V → Prop) : Prop :=
  ∀ a b, G.Adj a b → (D a b ↔ ¬ D b a)

private def outDegree {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    [DecidableRel G.Adj] [DecidableRel D] (v : Fin n) : ℕ :=
  (univ.filter fun w => G.Adj v w ∧ D v w).card

private theorem sum_outDegree {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    [DecidableRel G.Adj] [DecidableRel D] (oriented : Orientation G D) :
    ∑ v, outDegree G D v = G.edgeFinset.card := by
  classical
  let arcs := (univ : Finset (Fin n × Fin n)).filter (fun p => G.Adj p.1 p.2 ∧ D p.1 p.2)
  have hcount : arcs.card = ∑ v, outDegree G D v := by
    let X := (univ : Finset (Fin n)).sigma fun v => univ.filter (fun w => G.Adj v w ∧ D v w)
    have heq : X.card = arcs.card := by
      apply Finset.card_nbij (fun (p : Σ _ : Fin n, Fin n) => (p.1, p.2))
      · rintro ⟨v,w⟩ h
        simpa [X, arcs] using h
      · rintro ⟨a,b⟩ _ ⟨v,w⟩ _ h
        rcases Prod.mk.inj h with ⟨rfl,rfl⟩
        rfl
      · rintro ⟨v,w⟩ h
        exact ⟨⟨v,w⟩, by simpa [X, arcs] using h, rfl⟩
    rw [← heq]
    exact Finset.card_sigma _ _
  let edges := (univ : Finset (Fin n × Fin n)).filter (fun p => G.Adj p.1 p.2)
  have hsplit : arcs.card + (edges.filter (fun p => ¬ D p.1 p.2)).card = edges.card := by
    have eq : edges.filter (fun p => D p.1 p.2) = arcs := by
      ext p
      simp [edges, arcs]
    simpa only [eq] using
      (Finset.card_filter_add_card_filter_not (s := edges) (fun p => D p.1 p.2))
  have hswap : (edges.filter (fun p => ¬ D p.1 p.2)).card = arcs.card := by
    apply Finset.card_nbij Prod.swap
    · rintro ⟨a,b⟩ h
      simp [edges] at h
      simp [arcs, h.1.symm, (oriented b a h.1.symm).mpr h.2]
    · rintro ⟨a,b⟩ _ ⟨v,w⟩ _ h
      rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      rfl
    · rintro ⟨a,b⟩ h
      simp [arcs] at h
      exact ⟨(b,a), by simp [edges, h.1.symm, (oriented a b h.1).mp h.2], rfl⟩
  have twice := G.two_mul_card_edgeFinset
  change 2 * G.edgeFinset.card = edges.card at twice
  omega

private noncomputable def included {n : ℕ} (U : Finset (Fin n)) : Fin U.card ↪ Fin n :=
  U.equivFin.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩

private theorem included_mem {n : ℕ} (U : Finset (Fin n)) (i : Fin U.card) :
    included U i ∈ U := (U.equivFin.symm i).property

private theorem included_surj {n : ℕ} {U : Finset (Fin n)} {x : Fin n} (hx : x ∈ U) :
    ∃ i, included U i = x :=
  ⟨U.equivFin ⟨x,hx⟩, congrArg Subtype.val (U.equivFin.symm_apply_apply ⟨x,hx⟩)⟩

private theorem witness_map {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    {U : Finset (Fin n)} {J : Finset (Fin U.card)}
    (hJ : WitnessOn (G.comap (included U)) (fun a b => D (included U a) (included U b)) univ J) :
    WitnessOn G D U (J.map (included U)) := by
  obtain ⟨_, hind, h⟩ := hJ
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact included_mem U i
  · intro a ha b hb
    obtain ⟨a',ha',rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_map.mp hb
    exact hind a' ha' b' hb'
  · intro a ha b hb hau hbu hab
    obtain ⟨a',rfl⟩ := included_surj ha
    obtain ⟨b',rfl⟩ := included_surj hb
    rcases h a' (mem_univ _) b' (mem_univ _)
      (fun hx => hau (mem_map.mpr ⟨_,hx,rfl⟩))
      (fun hx => hbu (mem_map.mpr ⟨_,hx,rfl⟩)) hab with ⟨i,hi,he⟩ | ⟨i,hi,he⟩
    · exact Or.inl ⟨included U i, mem_map.mpr ⟨_,hi,rfl⟩, he⟩
    · exact Or.inr ⟨included U i, mem_map.mpr ⟨_,hi,rfl⟩, he⟩

private def AvoidAll : Prop := ∀ {n : ℕ}, n ≤ 13 → ∀ G : SimpleGraph (Fin n),
  SquareFree G → ∀ D, Orientation G D → ∀ w : Fin n,
    ∃ I, WitnessOn G D univ I ∧ w ∉ I

private def DenseAll : Prop := ∀ {n : ℕ}, n ≤ 15 → ∀ G : SimpleGraph (Fin n),
  SquareFree G → ∀ D, Orientation G D →
    ∀ [DecidableRel G.Adj] [DecidableRel D],
    (∀ v, 2 ≤ outDegree G D v) → Good G D univ

private theorem dense_and_avoid_suffice (avoid : AvoidAll) (dense : DenseAll)
    {n : ℕ} (hn : n ≤ 15) (G : SimpleGraph (Fin n)) (noSquare : SquareFree G)
    (D : Fin n → Fin n → Prop) (oriented : Orientation G D) : Good G D univ := by
  classical
  have h (U : Finset (Fin n)) : Good G D U := by
    induction U using Finset.strongInductionOn with
    | _ U ih =>
      by_cases hEmpty : U = ∅
      · subst U
        exact good_empty G D
      let O : Fin n → Finset (Fin n) := fun v => U.filter (fun w => G.Adj v w ∧ D v w)
      let e (V : Finset (Fin n)) := included V
      let H (V : Finset (Fin n)) := G.comap (e V)
      let R (V : Finset (Fin n)) := fun a b => D (e V a) (e V b)
      have hH (V : Finset (Fin n)) : SquareFree (H V) :=
        fun _ _ _ _ h1 h2 => noSquare _ _ _ _
          (fun h => h1 ((e V).injective h)) (fun h => h2 ((e V).injective h))
      have hR (V : Finset (Fin n)) : Orientation (H V) (R V) :=
        fun _ _ h => oriented _ _ h
      have bounded : U.card ≤ n := by
        simpa using (Finset.card_le_card (subset_univ U))
      by_cases hLow : ∃ v ∈ U, (O v).card ≤ 1
      · obtain ⟨v,hv,hc⟩ := hLow
        by_cases hSource : ∀ a ∈ U, G.Adj v a → D v a
        · apply source_step G D U v hv hSource
          apply ih
          exact Finset.erase_ssubset hv
        by_cases hSink : ∀ a ∈ U, G.Adj a v → D a v
        · apply sink_step G D U v hv hSink
          apply ih
          exact (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
            ⟨v,hv,by simp⟩
        push Not at hSource hSink
        obtain ⟨u,hu,hvu,hnvu⟩ := hSource
        obtain ⟨w,hw,hwv,hnwv⟩ := hSink
        have hvw : D v w := (oriented v w hwv.symm).mpr hnwv
        have wO : w ∈ O v := mem_filter.mpr ⟨hw,hwv.symm,hvw⟩
        have huv : D u v := (oriented u v hvu.symm).mpr hnvu
        let V := U.filter (fun a => a ≠ v ∧ ¬ (G.Adj a v ∧ D a v))
        have hVsub : V ⊆ (U.erase v).erase u := by
          intro a ha
          obtain ⟨ha,hav,hn⟩ := Finset.mem_filter.mp ha
          exact mem_erase.mpr ⟨fun h => hn (h ▸ ⟨hvu.symm,huv⟩), mem_erase.mpr ⟨hav,ha⟩⟩
        have hVsize : V.card ≤ 13 := by
          have hu' : u ∈ U.erase v := mem_erase.mpr ⟨hvu.ne.symm,hu⟩
          have hcap := Finset.card_le_card hVsub
          rw [Finset.card_erase_of_mem hu', Finset.card_erase_of_mem hv] at hcap
          omega
        have hw' : w ∈ V := by
          refine mem_filter.mpr ⟨hw,hwv.ne,?_⟩
          exact fun h => hnwv h.2
        obtain ⟨j,hj⟩ := included_surj hw'
        obtain ⟨J,hJ,havoid⟩ := avoid hVsize (H V) (hH V) (R V) (hR V) j
        refine unique_out_step G D U v w hv oriented ?_ ⟨_, witness_map G D hJ, ?_⟩
        · intro a ha he hd
          exact (Finset.card_le_one.mp hc) a (mem_filter.mpr ⟨ha,he,hd⟩) w wO
        · intro hm
          obtain ⟨i,hi,heq⟩ := mem_map.mp hm
          exact havoid (((e V).injective (heq.trans hj.symm)) ▸ hi)
      · push Not at hLow
        let _ : DecidableRel (H U).Adj := Classical.decRel _
        let _ : DecidableRel (R U) := Classical.decRel _
        have out (i : Fin U.card) : 2 ≤ outDegree (H U) (R U) i := by
          have hlow := hLow (e U i) (included_mem U i)
          let X := (univ : Finset (Fin U.card)).filter (fun w => (H U).Adj i w ∧ R U i w)
          have heq : (X.map (e U)).card = (O (e U i)).card := by
            congr 1
            ext a
            constructor
            · intro ha
              obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp ha
              exact mem_filter.mpr ⟨included_mem U w, (mem_filter.mp hw).2⟩
            · intro ha
              obtain ⟨ha,hedge⟩ := Finset.mem_filter.mp ha
              obtain ⟨w,rfl⟩ := included_surj ha
              exact mem_map.mpr ⟨w, mem_filter.mpr ⟨mem_univ _,hedge⟩,rfl⟩
          rw [Finset.card_map] at heq
          change 2 ≤ X.card
          omega
        obtain ⟨J,hJ⟩ := dense (bounded.trans hn) (H U) (hH U) (R U) (hR U) out
        exact ⟨_, witness_map G D hJ⟩
  exact h univ

end Reduction904

namespace GraphFacts
open Finset

private theorem independent_five (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj]
    (h4 : SquareFree904 G) (reg : ∀ u, G.degree u = 4)
    (color10 : ∀ H : SimpleGraph (Fin 10), SquareFree904 H → H.Colorable 3) :
    ∃ I : Finset (Fin 15), I.card = 5 ∧ ∀ a ∈ I, ∀ b ∈ I, ¬G.Adj a b := by
  classical
  let v : Fin 15 := 0
  let R := (insert v (G.neighborFinset v))ᶜ
  have hcard : R.card = 10 := by
    have := outside_card G v
    change R.card + _ + 1 = 15 at this
    rw [G.card_neighborFinset_eq_degree, reg] at this
    omega
  have colors (k : ℕ) (hk : k=10) (H : SimpleGraph (Fin k)) (h : SquareFree904 H) : H.Colorable 3 := by
    subst k
    exact color10 H h
  obtain ⟨f⟩ := colors R.card hcard (induced904 G R) (induced_square G R h4)
  obtain ⟨c,hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f : Fin R.card → Fin 3)
    (n:=3) (by simp [hcard])
  obtain ⟨Y,hY,hYcard⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ (univ.filter (fun i => f i = c)).card)
  let emb : Fin R.card ↪ Fin 15 := R.equivFin.symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  let J := Y.map emb
  have dis {x : Fin 15} (hx : x ∈ J) : x ≠ v ∧ ¬G.Adj v x := by
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hx
    have hz : emb z ∈ R := (R.equivFin.symm z).property
    simpa only [R, mem_compl,mem_insert, G.mem_neighborFinset,not_or] using hz
  refine ⟨insert v J,?_,?_⟩
  · rw [card_insert_of_notMem (fun hv => (dis hv).1 rfl)]
    simp [J,hYcard]
  · intro a ha b hb he
    rcases mem_insert.mp ha with rfl|ha <;> rcases mem_insert.mp hb with rfl|hb
    · exact he.ne rfl
    · exact (dis hb).2 he
    · exact (dis ha).2 he.symm
    · obtain ⟨x,hx,rfl⟩ := mem_map.mp ha
      obtain ⟨y,hy,rfl⟩ := mem_map.mp hb
      exact f.valid (show (induced904 G R).Adj x y from he)
        (((mem_filter.mp (hY hx)).2).trans ((mem_filter.mp (hY hy)).2).symm)

private theorem five_dominates (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj]
    (h4 : SquareFree904 G) (reg : ∀ u, G.degree u = 4)
    (I : Finset (Fin 15)) (hs : I.card = 5) (hi : ∀ a ∈ I, ∀ b ∈ I, ¬G.Adj a b) :
    ∀ c ∉ I, 2 ≤ (I.filter fun a => G.Adj a c).card := by
  classical
  let J := Iᶜ
  have hJ : J.card = 10 := by
    have h := Finset.card_compl_add_card I
    change J.card + I.card = 15 at h
    omega
  let nei (v : Fin 15) := I.filter fun i => G.Adj i v
  let f (v : Fin 15) := (nei v).card
  have sumf : ∑ v ∈ J, f v = 20 := by
    have counting : ∑ v ∈ J, f v = arcs G I J := by
      rw [arcs, sum_comm]
      apply sum_congr rfl
      intro b _
      simp [f,nei,weight,Finset.sum_boole]
    have adj (u : Fin 15) (hu : u ∈ I) : J.filter (G.Adj u) = G.neighborFinset u := by
      ext w
      simp only [mem_filter, J,mem_compl,G.mem_neighborFinset]
      exact ⟨And.right,fun h => ⟨fun hw => hi _ hu _ hw h,h⟩⟩
    rw [counting,arcs]
    have each (u : Fin 15) (hu : u ∈ I) : ∑ v ∈ J, weight G u v = 4 := by
      simpa [weight,sum_boole,adj u hu] using reg u
    rw [sum_congr rfl each]
    simp [hs]
  let pairs := J.sigma (fun j => (nei j).offDiag)
  have hbound : pairs.card ≤ I.offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun p => p.2)
    · rintro ⟨u,a,b⟩ hu
      obtain ⟨ha,hb,ab⟩ := mem_offDiag.mp (mem_sigma.mp hu).2
      exact mem_offDiag.mpr ⟨(mem_filter.mp ha).1,(mem_filter.mp hb).1,ab⟩
    · rintro ⟨u,a,b⟩ hu ⟨v,c,d⟩ hv ht
      change (a,b)=(c,d) at ht
      cases ht
      obtain ⟨ha,hb,ab⟩ := mem_offDiag.mp (mem_sigma.mp hu).2
      obtain ⟨hc,hd,_⟩ := mem_offDiag.mp (mem_sigma.mp hv).2
      have eq := common_neigh_unique G h4 ab (mem_filter.mp ha).2 (mem_filter.mp hb).2
        (mem_filter.mp hc).2 (mem_filter.mp hd).2
      change u = v at eq
      subst v
      rfl
  have square_sum : (∑ j ∈ J, f j ^ 2) ≤ 40 := by
    have split : (∑ j ∈ J, f j ^ 2) = pairs.card + ∑ j ∈ J, f j := by
      simp only [pairs,card_sigma,offDiag_card,←sum_add_distrib]
      apply sum_congr rfl
      intro i _
      rw [show (nei i).card = f i from rfl,Nat.sub_add_cancel (Nat.le_mul_self _),pow_two]
    rw [split,sumf]
    rw [offDiag_card,hs] at hbound
    omega
  have fZ : (∑ j ∈ J, (f j : ℤ)) = 20 := by exact_mod_cast sumf
  have sqZ : (∑ j ∈ J, (f j : ℤ)^2) ≤ 40 := by exact_mod_cast square_sum
  have variance : (∑ j ∈ J, ((f j : ℤ)-2)^2) ≤ 0 := by
    calc
      _ = ∑ j ∈ J, ((f j : ℤ)^2 - 4*f j + 4) := sum_congr rfl (fun _ _ => by ring)
      _ = (∑ j ∈ J, (f j : ℤ)^2) - 4* (∑ j ∈ J, (f j:ℤ)) + 4*J.card := by
        simp [sum_add_distrib,sum_sub_distrib,mul_sum,mul_comm]
      _ ≤ 0 := by rw [fZ,hJ]; norm_num; omega
  intro v hv
  have term := single_le_sum (s:=J) (f:=fun j => ((f j : ℤ)-2)^2)
    (fun i _ => sq_nonneg _) (show v ∈ J from mem_compl.mpr hv)
  have z : ((f v : ℤ)-2)^2 = 0 := le_antisymm (term.trans variance) (sq_nonneg _)
  have z' : (f v:ℤ)=2 := by nlinarith
  change 2 ≤ f v
  exact_mod_cast (le_of_eq z'.symm)

theorem reg15_set (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj] (h4 : SquareFree904 G)
    (reg : ∀ u, G.degree u = 4)
    (color10 : ∀ H : SimpleGraph (Fin 10), SquareFree904 H → H.Colorable 3) :
    ∃ I : Finset (Fin 15), (∀ a ∈ I, ∀ b ∈ I, ¬G.Adj a b) ∧
      ∀ c ∉ I, 2 ≤ (I.filter fun a => G.Adj a c).card := by
  obtain ⟨I,hcard,hi⟩ := independent_five G h4 reg color10
  exact ⟨I,hi,five_dominates G h4 reg I hcard hi⟩

end GraphFacts

namespace GraphFacts

open Finset

private theorem numeric_dense (d r : Fin 16) (n : Fin 16) (hn : 14 ≤ n.val)
    (parts : r.val + d.val + 1 = n.val) (high : 5 ≤ d.val) :
    2*(n.val-1) + d.val + 2*Ebound r.val < 4*n.val := by
  exact (by decide : ∀ (d r n : Fin 16), 14 ≤ n.val → r.val+d.val+1=n.val → 5 ≤ d.val →
    2*(n.val-1)+d.val+2*Ebound r.val < 4*n.val) d r n hn parts high

theorem dense_regular {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : n ≤ 15) (hpos : 0 < n) (h4 : SquareFree904 G) (dense : 2*n ≤ G.edgeFinset.card) :
    n = 15 ∧ ∀ v, G.degree v = 4 := by
  classical
  have hn14 : 14 ≤ n := by
    by_contra! h
    have h' := Regular904.sparse_thirteen G h4 hpos (by omega)
    omega
  have cap (v : Fin n) : G.degree v ≤ 4 := by
    by_contra! hv
    let d := (G.neighborFinset v).card
    let R := (insert v (G.neighborFinset v))ᶜ
    have hpart := outside_card G v
    change R.card + d + 1 = n at hpart
    have h5 : 5 ≤ d := by change 5 ≤ (G.neighborFinset v).card; rw [G.card_neighborFinset_eq_degree]; omega
    have sub := small_ext_bound (induced904 G R) (by omega) (induced_square G R h4)
    have split := split_at_vertex G v h4
    change 2*G.edgeFinset.card ≤ 2*(n-1)+d+2*(induced904 G R).edgeFinset.card at split
    have low := numeric_dense ⟨d,by omega⟩ ⟨R.card,by omega⟩ ⟨n,by omega⟩ hn14 hpart h5
    change 2*(n-1) + d + 2*Ebound R.card < 4*n at low
    omega
  have reg (v : Fin n) : G.degree v = 4 := by
    by_contra h
    have hv := cap v
    have less : ∑ u : Fin n, G.degree u < ∑ _u : Fin n, 4 := Finset.sum_lt_sum
      (fun i _ => cap i) ⟨v, mem_univ _, by omega⟩
    rw [G.sum_degrees_eq_twice_card_edges] at less
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at less
    change 2*G.edgeFinset.card < n*4 at less
    omega
  refine ⟨?_,reg⟩
  by_contra ne
  exact Regular904.no_regular_fourteen G h4 (by omega) (fun v => (G.card_neighborFinset_eq_degree v).trans (reg v))

end GraphFacts

namespace Reduction904

open Finset GraphFacts

private theorem dense_of_small (color10 : ∀ H : SimpleGraph (Fin 10), SquareFree H → H.Colorable 3) :
    DenseAll := by
  intro n hn G h4 D orient _ _ hout
  classical
  by_cases h0 : n=0
  · subst n
    exact ⟨∅, empty_subset _, by simp, fun v => Fin.elim0 v⟩
  have lm := Finset.sum_le_sum (s:=univ) (fun (v : Fin n) _ => hout v)
  rw [sum_outDegree G D orient] at lm
  simp only [Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at lm
  change n*2 ≤ G.edgeFinset.card at lm
  obtain ⟨e,hd⟩ := dense_regular G hn (by omega) h4 (by omega)
  subst n
  obtain ⟨I,hi,dom⟩ := reg15_set G h4 hd color10
  refine ⟨I,two_neighbor_witness G D I hi orient (fun v => ?_) dom⟩
  let N := G.neighborFinset v
  let ins := univ.filter (fun a => G.Adj a v ∧ D a v)
  let outs := univ.filter (fun a => G.Adj v a ∧ D v a)
  have oeq : N.filter (D v) = outs := by ext x; simp [N,outs]
  have ieq : N.filter (fun a => ¬D v a) = ins := by
    ext a
    simp only [mem_filter,N,ins,mem_univ,true_and,G.mem_neighborFinset]
    exact ⟨fun ⟨h,e⟩ => ⟨h.symm,(orient a v h.symm).mpr e⟩,
      fun ⟨h,e⟩ => ⟨h.symm,(orient a v h).mp e⟩⟩
  have split := Finset.card_filter_add_card_filter_not (s:=N) (p:=D v)
  rw [oeq,ieq] at split
  have cap : N.card = 4 := (G.card_neighborFinset_eq_degree v).trans (hd v)
  have h := hout v
  change 2 ≤ outs.card at h
  change ins.card ≤ 2
  omega

end Reduction904

namespace GraphFacts

open Finset

theorem color_extend_low {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (hdeg : G.degree v ≤ 2) (hcol : (induced904 G (univ.erase v)).Colorable 3) :
    G.Colorable 3 := by
  classical
  let U := (univ : Finset (Fin n)).erase v
  obtain ⟨c⟩ := hcol
  let col (a : Fin n) : Fin 3 := if h : a ∈ U then c (U.equivFin ⟨a,h⟩) else 0
  let used := (G.neighborFinset v).image col
  have hused : used.card < (univ : Finset (Fin 3)).card := by
    have h : used.card ≤ G.degree v := Finset.card_image_le
    simp
    omega
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
  let allcol (a : Fin n) : Fin 3 := if a = v then k else col a
  refine ⟨SimpleGraph.Coloring.mk allcol ?_⟩
  intro a b hab
  by_cases hav : a = v
  · subst a
    intro eq
    have hb := (G.mem_neighborFinset v b).mpr hab
    have hne := hab.ne.symm
    have eq' : k = col b := by simpa [allcol,hne] using eq
    exact hk (eq' ▸ Finset.mem_image_of_mem col hb)
  by_cases hbv : b = v
  · subst b
    intro eq
    have ha := (G.mem_neighborFinset v a).mpr hab.symm
    have eq' : col a = k := by simpa [allcol,hav] using eq
    exact hk (eq' ▸ Finset.mem_image_of_mem col ha)
  have ha : a ∈ U := by simp [U,hav]
  have hb : b ∈ U := by simp [U,hbv]
  have edge : (induced904 G U).Adj (U.equivFin ⟨a,ha⟩) (U.equivFin ⟨b,hb⟩) := by
    simpa [induced904,SimpleGraph.comap_adj] using hab
  simpa [allcol,hav,hbv,col,ha,hb] using c.valid edge

abbrev CoreCensus904 : Prop :=
  ∀ {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj], k ≤ 11 → SquareFree904 H →
    (∀ i, 3 ≤ H.degree i) → H.Colorable 3

theorem small_colorable_of_census (coreCensus : CoreCensus904) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hn : n ≤ 11) (h4 : SquareFree904 G) : G.Colorable 3 := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases low : ∃ v, G.degree v ≤ 2
    · obtain ⟨v,hv⟩ := low
      let U := (univ : Finset (Fin n)).erase v
      have hvn := v.isLt
      have hU : U.card = n-1 := by simp [U]
      exact color_extend_low G v hv (ih U.card (by omega) (induced904 G U) (by omega)
        (induced_square G U h4))
    · exact coreCensus G hn h4 (fun i => by by_contra! h; exact low ⟨i,by omega⟩)

private theorem min_three_on_twelve (coreCensus : CoreCensus904) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hn : n = 12) (h4 : SquareFree904 G) (fail : ¬G.Colorable 3) :
    ∀ i, 3 ≤ G.degree i := by
  classical
  intro i
  by_contra! hlow
  let U := (univ : Finset (Fin n)).erase i
  have hU : U.card = n-1 := by simp [U]
  exact fail (color_extend_low G i (by omega) (small_colorable_of_census coreCensus (induced904 G U)
    (by omega) (induced_square G U h4)))

theorem low_degree_core_reduce (coreCensus : CoreCensus904) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hn : n ≤ 13) (h4 : SquareFree904 G) (fail : ¬ G.Colorable 3) :
    ((n=12 ∨ n=13) ∧ ∀ i, 3 ≤ G.degree i) ∨
    (n=13 ∧ ∃ v : Fin n, G.degree v ≤ 2 ∧
      let U := (univ : Finset (Fin n)).erase v
      U.card=12 ∧ SquareFree904 (induced904 G U) ∧ ¬(induced904 G U).Colorable 3 ∧
      ∀ j, 3 ≤ ((induced904 G U).neighborSet j).ncard) := by
  classical
  have big : 11<n := by
    by_contra! h
    exact fail (small_colorable_of_census coreCensus G h h4)
  by_cases low : ∃ v, G.degree v ≤ 2
  · obtain ⟨v,hv⟩ := low
    have n13 : n=13 := by
      by_contra ne
      have := min_three_on_twelve coreCensus G (by omega) h4 fail v
      omega
    let U := (univ : Finset (Fin n)).erase v
    have hU : U.card = 12 := by simp [U,n13]
    have square := induced_square G U h4
    have hbad : ¬(induced904 G U).Colorable 3 := fun h => fail (color_extend_low G v hv h)
    have hmin := min_three_on_twelve coreCensus (induced904 G U) hU square hbad
    exact Or.inr ⟨n13,v,hv,hU,square,hbad,fun j => by simpa using hmin j⟩
  · left
    exact ⟨by omega,fun i => by by_contra! h; exact low ⟨i,by omega⟩⟩

end GraphFacts

namespace Census904

def palettes (n : Nat) : List (Nat × Nat × Nat) :=
  match n with
  | 10 => [(564, 322, 137), (560, 387, 76), (550, 448, 25), (532, 321, 170), (768, 150, 105), (548, 338, 137), (549, 448, 26), (553, 448, 22), (768, 165, 90)]
  | 11 => [(1072, 646, 329), (1061, 720, 266), (1296, 579, 172), (1296, 549, 202), (1072, 645, 330), (1080, 646, 321), (1288, 581, 178), (1061, 770, 216), (1065, 644, 338), (1076, 642, 329), (1072, 643, 332)]
  | 12 => [(2185, 1542, 368), (2074, 1348, 673), (3078, 657, 360), (2196, 1546, 353), (2152, 1542, 401), (2132, 1283, 680), (2136, 1286, 673), (2200, 1541, 354), (2097, 1348, 650), (2256, 1795, 44), (2124, 1539, 432), (2129, 1286, 680), (3075, 840, 180), (3078, 833, 184), (2569, 1124, 402), (2242, 1292, 561), (3077, 712, 306), (2258, 1292, 545), (3074, 612, 409), (2132, 1289, 674), (3074, 620, 401), (2088, 1364, 643), (2118, 1424, 553), (2272, 1550, 273), (2097, 1728, 270), (2132, 1282, 681), (2098, 1665, 332), (2117, 1424, 554), (2569, 1346, 180), (2322, 1569, 204), (2577, 1124, 394), (2182, 1793, 120), (2098, 1728, 269), (2076, 1569, 450), (3074, 668, 353), (2314, 1540, 241), (3073, 612, 410), (2570, 1093, 432), (2130, 1668, 297), (2217, 1794, 84), (2307, 1108, 680), (2260, 1794, 41), (2570, 1124, 401), (2256, 1286, 553), (3076, 849, 170), (3076, 721, 298), (2314, 1541, 240), (2204, 1794, 97), (2224, 1550, 321), (3074, 661, 360), (3074, 660, 361), (2324, 1538, 233), (2115, 1668, 312), (2115, 1424, 556), (3073, 624, 398), (2328, 1538, 229), (2076, 1601, 418), (2136, 1285, 674), (2122, 1297, 676), (2256, 1285, 554), (2272, 1549, 274), (2321, 1540, 234), (2084, 1240, 771), (2313, 1542, 240), (2569, 1094, 432), (3075, 716, 304), (3074, 600, 421), (2194, 1793, 108), (2248, 1795, 52)]
  | 13 => [(4308, 2818, 1065), (5154, 2196, 841), (6150, 1360, 681), (4248, 3587, 356), (4230, 2864, 1097), (5154, 2200, 837), (6150, 1736, 305), (6150, 1672, 369), (6151, 1616, 424), (4139, 2628, 1424), (5154, 2313, 724), (4140, 3329, 722), (4261, 2578, 1352), (4188, 2594, 1409), (4200, 3078, 913), (4156, 3264, 771), (7169, 842, 180), (4872, 3075, 244), (4613, 3330, 248), (4198, 2577, 1416), (4304, 2819, 1068), (5144, 2498, 549), (4201, 2578, 1412), (4148, 2689, 1354), (5154, 2316, 721), (4865, 3078, 248), (4618, 3077, 496), (5153, 2324, 714), (6151, 1360, 680), (4392, 3078, 721), (4233, 3078, 880), (6150, 1665, 376), (6149, 1248, 794), (6147, 1688, 356), (5129, 2848, 214), (4336, 2566, 1289), (4244, 2882, 1065), (5152, 2201, 838), (4628, 2187, 1376), (5152, 2325, 714), (4166, 3329, 696), (4872, 3106, 213), (4628, 2376, 1187), (5153, 2194, 844), (4628, 2121, 1442), (4385, 3078, 728), (6150, 1361, 680), (7169, 652, 370), (4244, 3075, 872), (5152, 2326, 713), (4186, 2565, 1440), (5129, 2594, 468), (4290, 2588, 1313), (4872, 3078, 241), (4242, 2881, 1068), (4626, 3077, 488), (6147, 1680, 364), (4304, 2595, 1292), (7169, 844, 178), (6150, 1224, 817), (5153, 2314, 724), (4868, 3075, 248), (4614, 3329, 248), (4248, 3078, 865), (4613, 2314, 1264), (4620, 3329, 242), (4248, 3077, 866), (4618, 3332, 241), (4880, 2188, 1123), (4628, 3082, 481), (4248, 2881, 1062), (4144, 2693, 1354), (4123, 2628, 1440), (4336, 2563, 1292), (4235, 3584, 372), (4244, 2634, 1313), (4144, 2630, 1417), (4376, 3585, 230), (5123, 2596, 472), (4181, 2570, 1440), (5128, 2374, 689), (7168, 653, 370), (4320, 2582, 1289), (5129, 2596, 466), (4177, 2692, 1322), (4400, 3075, 716), (4154, 3077, 960), (5154, 2324, 713), (5154, 2692, 345), (7169, 906, 116), (4618, 3329, 244), (5123, 2880, 188), (6146, 1673, 372), (5185, 2322, 684), (5123, 2200, 868), (4868, 2187, 1136), (4613, 2322, 1256), (4484, 2152, 1555), (4204, 3074, 913), (5137, 2244, 810), (4244, 2881, 1066), (5185, 2194, 812), (5632, 2273, 286), (6150, 1352, 689), (4245, 2848, 1098), (4146, 2692, 1353), (4304, 2566, 1321), (4145, 2692, 1354), (4392, 2577, 1222), (4248, 2882, 1061), (4388, 3075, 728), (5156, 2307, 728), (4320, 2585, 1286), (4262, 2832, 1097), (4252, 3075, 864), (4617, 3330, 244), (4864, 2137, 1190), (4392, 2198, 1601), (4150, 2376, 1665), (4184, 2565, 1442), (4488, 2071, 1632), (6147, 1808, 236), (4656, 2126, 1409), (4424, 2196, 1571), (4257, 2648, 1286), (5632, 2183, 376), (4392, 2629, 1170), (6146, 1293, 752), (5384, 2593, 214), (4312, 2818, 1061), (4204, 2578, 1409), (4111, 2656, 1424), (4880, 3105, 206), (4385, 2126, 1680), (4260, 2882, 1049), (6146, 1301, 744), (5123, 2324, 744), (4154, 3264, 773), (5154, 2204, 833), (7168, 675, 348), (6656, 1125, 410), (4619, 3328, 244), (4629, 2440, 1122), (6147, 1248, 796), (5154, 2329, 708), (6146, 1648, 397), (5123, 2372, 696), (5129, 2626, 436), (6146, 1840, 205), (5632, 2218, 341), (6147, 1360, 684), (4249, 3078, 864), (5130, 2565, 496), (5130, 2372, 689), (7168, 597, 426), (6146, 1240, 805), (5126, 2200, 865), (5125, 2186, 880), (4865, 3138, 188), (5130, 2848, 213), (6150, 1760, 281), (4268, 3585, 338), (4308, 2819, 1064), (5168, 2697, 326), (4274, 2636, 1281), (4632, 3329, 230), (6147, 1356, 688), (4324, 2818, 1049), (5154, 2700, 337), (4292, 2360, 1539), (4392, 2578, 1221), (5156, 2433, 602), (4245, 2632, 1314), (4674, 2433, 1084), (4304, 2565, 1322), (4388, 3082, 721), (5154, 2821, 216), (5185, 2448, 558), (4866, 3201, 124), (5137, 2626, 428), (4676, 3201, 314), (6150, 1368, 673), (4152, 2692, 1347), (4361, 2214, 1616), (5152, 2202, 837), (4272, 2881, 1038), (5130, 2720, 341), (7168, 779, 244), (5216, 2326, 649), (5125, 2626, 440), (4420, 2579, 1192), (4246, 2569, 1376), (4245, 2626, 1320), (4241, 2632, 1318), (4177, 3332, 682), (4146, 2693, 1352), (6145, 1236, 810), (4484, 2625, 1082), (4152, 2693, 1346), (6145, 1240, 806), (4246, 3328, 617), (4259, 2832, 1100), (4676, 2323, 1192), (6149, 1352, 690), (7168, 787, 236), (4236, 3075, 880), (4363, 3140, 688), (5125, 2594, 472), (4388, 2136, 1667), (4186, 2593, 1412), (4390, 3081, 720), (4673, 2434, 1084), (4260, 2577, 1354), (4481, 3138, 572), (4182, 2568, 1441), (4400, 2563, 1228), (6150, 1232, 809), (5123, 2340, 728), (6145, 1204, 842), (4292, 2339, 1560), (7168, 590, 433), (6146, 1633, 412), (4296, 2102, 1793), (5154, 2321, 716), (4619, 3140, 432), (4178, 2692, 1321), (4196, 3075, 920), (4365, 2690, 1136), (6150, 1808, 233), (4680, 2099, 1412), (5130, 2245, 816), (6149, 1808, 234), (6147, 1416, 628), (4865, 3084, 242), (5168, 2693, 330), (4244, 3082, 865), (4388, 3585, 218), (6145, 1302, 744), (4737, 3138, 316), (4392, 3075, 724), (4484, 2571, 1136), (4306, 2572, 1313), (4260, 3081, 850), (4243, 2628, 1320), (7169, 738, 284), (6145, 1364, 682), (4676, 3202, 313), (4676, 2075, 1440), (5156, 2314, 721), (6147, 1672, 372), (6656, 1140, 395), (5250, 2625, 316), (5129, 2340, 722), (5137, 2370, 684), (5123, 2824, 244), (5156, 2329, 706), (5186, 2452, 553), (5185, 2436, 570), (4644, 3330, 217), (4208, 2563, 1420), (5250, 2817, 124), (5185, 2824, 182), (4304, 3587, 300), (4680, 2195, 1316), (5153, 2332, 706), (6150, 1377, 664), (5392, 2150, 649), (4153, 2626, 1412), (4388, 2584, 1219), (4674, 3201, 316), (4613, 2162, 1416), (7168, 613, 410), (5632, 2214, 345), (5130, 2369, 692), (4296, 3587, 308), (5186, 2436, 569), (5384, 2149, 658), (4208, 2692, 1291), (4230, 2648, 1313), (4296, 2819, 1076), (4260, 2585, 1346), (4172, 2563, 1456), (4180, 3329, 682), (4252, 2882, 1057), (6146, 1636, 409), (4272, 2566, 1353), (4617, 2436, 1138), (4626, 3168, 397), (4740, 2384, 1067), (4865, 3202, 124), (5154, 2449, 588), (5129, 2720, 342), (6149, 1360, 682), (4182, 2593, 1416), (4740, 3138, 313), (5132, 2848, 211), (5377, 2628, 186), (5153, 2326, 712), (4632, 2372, 1187), (6148, 1306, 737), (6146, 1617, 428), (4630, 3081, 480), (7169, 714, 308), (4626, 2148, 1417), (4244, 2632, 1315), (5153, 2330, 708), (4237, 2626, 1328), (4304, 2569, 1318), (4872, 3168, 151), (4626, 3081, 484), (5248, 2087, 856), (5129, 2434, 628), (4216, 2818, 1157), (5126, 2625, 440), (4865, 3082, 244), (7169, 852, 170), (5378, 2640, 173), (5632, 2119, 440), (6149, 1632, 410), (4481, 3152, 558), (4625, 2434, 1132), (7168, 598, 425), (6147, 1824, 220), (4208, 2566, 1417), (5128, 2597, 466), (4864, 2189, 1138), (6146, 1612, 433), (4676, 2099, 1416), (4392, 3077, 722), (5130, 2593, 468), (4135, 2632, 1424), (5188, 2433, 570), (4484, 2091, 1616), (4648, 3075, 468), (4291, 3840, 60), (4204, 2818, 1169), (4628, 2369, 1194), (4418, 3201, 572), (6656, 1361, 174), (4388, 2577, 1226), (4305, 3840, 46), (7169, 744, 278), (5632, 2401, 158), (6145, 1234, 812), (4182, 2569, 1440), (6146, 1221, 824), (4420, 2105, 1666), (5186, 2696, 309), (4358, 2696, 1137), (5632, 2243, 316), (4289, 3340, 562), (5392, 2119, 680), (5186, 2817, 188), (4625, 2252, 1314), (5129, 2244, 818), (6145, 1294, 752), (4392, 2182, 1617), (4864, 3079, 248), (7168, 713, 310), (4248, 2598, 1345), (4488, 3137, 566), (4264, 3077, 850), (4864, 2131, 1196), (5123, 2656, 412), (4119, 2632, 1440), (5632, 2274, 285), (4611, 3332, 248), (4386, 3585, 220), (4424, 3202, 565), (5137, 2656, 398), (4632, 2118, 1441), (6146, 1624, 421), (4262, 3585, 344), (4629, 2376, 1186), (4290, 3340, 561), (5156, 2330, 705), (5137, 2596, 458), (4613, 2210, 1368), (5632, 2091, 468), (5129, 2148, 914), (5126, 2656, 409), (7169, 876, 146), (4420, 2211, 1560), (5632, 2246, 313), (4613, 3082, 496), (4628, 2442, 1121), (4644, 2441, 1106), (4172, 3329, 690)]
  | _ => []

def exceptions (n : Nat) : List (List Nat) :=
  match n with
  | 12 => [[1584, 2344, 2196, 1098, 581, 387, 3073, 2562, 1284, 648, 336, 224]]
  | 13 => [[3840, 5168, 6156, 4544, 4611, 616, 660, 2178, 2113, 1153, 1090, 292, 280], [3840, 5312, 6192, 4364, 4611, 2122, 2181, 1033, 1030, 672, 592, 400, 352], [3592, 5380, 6147, 4296, 2100, 610, 645, 402, 297, 4624, 2368, 1184, 1104], [3840, 5132, 6147, 4544, 4656, 586, 645, 281, 294, 2208, 2128, 1168, 1120], [3840, 5312, 6192, 4364, 4611, 2122, 2181, 1049, 1062, 672, 592, 400, 352]]
  | _ => []

end Census904

namespace Census904

def bit (n i : Nat) : Nat := 2^(n-1-i)

def small (x : Nat) : Bool := (x &&& (x-1)) == 0

def pack : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 2^bs.length else 0) + pack bs

def incoming (n j : Nat) (p : List Nat) : Nat :=
  pack (p.map (fun s => s &&& bit n j != 0)) <<< (n-p.length)

abbrev Key := Nat × Nat

def generate : List Key → List Key → Nat → List Nat
  | [], _, need => if need == 0 then [0] else []
  | k::ks, blocked, need =>
    if ks.length+1 < need then [] else
      generate ks (k::blocked) need ++
      (if 0 < need ∧ k ∉ blocked then
        (generate ks blocked (need-1)).map (2^ks.length + ·)
       else [])

def vertices (n i : Nat) : List Nat := (List.range n).drop (i+1)

def hits (n : Nat) (r : Nat) (j : Nat) : Bool := r &&& bit n j != 0

def key (n : Nat) (d p : List Nat) (j : Nat) : Key :=
  (d[j]?.getD 0, incoming n j p)

def degreeOptions (n : Nat) : Nat → Nat → Nat → List (List Nat)
  | 0, _, _ => [[]]
  | todo+1, cap, budget =>
    ((List.range (cap+1)).filter (3 ≤ ·)).flatMap (fun d =>
      let w := d*(d-1)
      if w+6*todo ≤ budget then
        (degreeOptions n todo d (budget-w)).map (d::·)
      else [])

def nextRows (n : Nat) (d p : List Nat) : List Nat :=
  let i := p.length
  let lower := incoming n i p
  let deg := d[i]?.getD 0
  let used := (p.map (fun s => hits n s i)).count true
  let vs := vertices n i
  if used > deg || deg-used > vs.length then [] else
    (generate (vs.map (key n d p)) [] (deg-used)).map (lower ||| ·)

def rowOK (n : Nat) (d p : List Nat) (r : Nat) : Bool :=
  let i := p.length
  let full := 2^n-1
  p.zipIdx.all fun (s,j) =>
    small (s &&& r) &&
     (d[j]? != d[i]? ||
       let cmp := full ^^^ (bit n i ||| bit n j)
       (s &&& cmp) >= (r &&& cmp))

def paletteOK (n : Nat) (p : List Nat) (t : Nat × Nat × Nat) : Bool :=
  p.zipIdx.all fun (r,i) =>
    let b := bit n i
    let chosen := if b &&& t.1 != 0 then t.1 else if b &&& t.2.1 != 0 then t.2.1 else t.2.2
    (b &&& chosen != 0) && (r &&& chosen == 0)

def leaf (n : Nat) (p : List Nat) : Bool :=
  (exceptions n).contains p || (palettes n).any (paletteOK n p)

def visit (n : Nat) (degrees : List Nat) : Nat → List Nat → Bool
  | 0, p => leaf n p
  | t+1, p => (nextRows n degrees p).all fun r =>
      !(rowOK n degrees p r) || visit n degrees t (p++[r])

def check (n : Nat) : Bool :=
  (degreeOptions n n (n-1) (n*(n-1))).all fun d =>
    d.sum % 2 != 0 || visit n d n []

end Census904

namespace Census904

lemma deg_mem {n cap budget : Nat} (d : List Nat)
    (ordered : d.Pairwise (· ≥ ·)) (lo : ∀ a ∈ d, 3 ≤ a)
    (hi : ∀ a ∈ d, a ≤ cap)
    (cost : (d.map (fun a => a*(a-1))).sum ≤ budget) :
    d ∈ degreeOptions n d.length cap budget := by
  induction d generalizing cap budget with
  | nil => simp [degreeOptions]
  | cons a ds ih =>
    have al := lo a (by simp)
    have ah := hi a (by simp)
    have los : ∀ x ∈ ds, 3 ≤ x := fun x hx => lo x (by simp [hx])
    have hmin : 6*ds.length ≤ (ds.map (fun x => x*(x-1))).sum := by
      clear ih ordered lo hi cost
      induction ds with
      | nil => simp
      | cons x xs h =>
        have hx := los x (by simp)
        have th := h (fun v hv => los v (by simp [hv]))
        have h1 : 3*2 ≤ x*(x-1) := Nat.mul_le_mul hx (by omega)
        simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_add, Nat.mul_one]
        omega
    have or' := List.pairwise_cons.mp ordered
    simp only [List.map_cons, List.sum_cons] at cost
    simp only [List.length_cons, degreeOptions, List.mem_flatMap]
    refine ⟨a, ?_, ?_⟩
    · simp [List.mem_range, al, Nat.lt_succ_iff.mpr ah]
    · rw [if_pos (by omega)]
      exact List.mem_map.mpr ⟨ds, ih or'.2 los or'.1 (by omega), rfl⟩

lemma generate_mem (xs : List (Key × Bool)) (blocked : List Key)
    (hc : xs.Pairwise (fun a b => a.1 = b.1 → a.2 = false → b.2 = false))
    (hb : ∀ a ∈ xs, a.2 = true → a.1 ∉ blocked) :
    pack (xs.map Prod.snd) ∈ generate (xs.map Prod.fst) blocked ((xs.map Prod.snd).count true) := by
  induction xs generalizing blocked with
  | nil => simp [pack, generate]
  | cons z xs ih =>
    rcases z with ⟨k, b⟩
    have cp := List.pairwise_cons.mp hc
    have cnt : (xs.map Prod.snd).count true ≤ xs.length := by
      simpa using (List.count_le_length (l := xs.map Prod.snd) (a := true))
    cases b with
    | false =>
      have stop : ∀ a ∈ xs, a.2=true → a.1 ∉ k::blocked := by
        intro a ha htrue hmem
        rcases List.mem_cons.mp hmem with hx|hx
        · have := cp.1 a ha hx.symm rfl
          simp_all
        · exact (hb a (by simp [ha]) htrue) hx
      simp [pack, generate, Nat.not_lt.mpr (Nat.le_succ_of_le cnt)]
      exact Or.inl (ih (blocked:=k::blocked) cp.2 stop)
    | true =>
      have hk := hb (k,true) (by simp) rfl
      have stop : ∀ a ∈ xs, a.2=true → a.1 ∉ blocked :=
        fun a ha ht => hb a (by simp [ha]) ht
      have hm := ih (blocked := blocked) cp.2 stop
      simp only [List.map_cons, List.count_cons_self, pack, generate, List.length_map]
      rw [if_neg (by omega), if_pos (by exact ⟨by omega, hk⟩)]
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨_, by simpa using hm, by simp⟩

lemma nextRows_mem {n : Nat} (d p : List Nat) (r : Nat)
    (letBits : r = incoming n p.length p |||
      pack ((vertices n p.length).map (hits n r)))
    (deg : d[p.length]?.getD 0 =
        (p.map (fun s => hits n s p.length)).count true +
          ((vertices n p.length).map (hits n r)).count true)
    (lex : (vertices n p.length).Pairwise (fun u v =>
      key n d p u = key n d p v → hits n r u = false → hits n r v = false)) :
    r ∈ nextRows n d p := by
  let z := (vertices n p.length).map (fun v => (key n d p v, hits n r v))
  have hz : z.Pairwise (fun a b => a.1=b.1 → a.2=false → b.2=false) := by
    simpa [z, List.pairwise_map] using lex
  have hy := generate_mem z [] hz (by simp)
  simp only [z, List.map_map, Function.comp_def] at hy
  have cnt : ((vertices n p.length).map (hits n r)).count true ≤ (vertices n p.length).length := by
    simpa using List.count_le_length (l := (vertices n p.length).map (hits n r)) (a := true)
  unfold nextRows
  simp only [deg, Nat.lt_irrefl, Nat.not_lt_of_ge (Nat.le_add_right ..), decide_false,
    Bool.false_or, Nat.add_sub_cancel_left, Nat.not_lt.mpr cnt, Bool.false_eq_true, if_false]
  exact List.mem_map.mpr ⟨_, hy, letBits.symm⟩

lemma visit_sound {n : Nat} (d p rest : List Nat)
    (head : ∀ i : Nat, (h : i < rest.length) →
      let q := p ++ rest.take i
      rest[i] ∈ nextRows n d q ∧ rowOK n d q rest[i] = true)
    (good : visit n d rest.length p = true) : leaf n (p++rest) = true := by
  induction rest generalizing p with
  | nil => simpa [visit] using good
  | cons r rs ih =>
    have ht := head 0 (by simp)
    simp only [List.take_zero, List.append_nil, List.getElem_cons_zero] at ht
    simp only [List.length_cons, visit, List.all_eq_true] at good
    have hg := good r ht.1
    simp only [ht.2, Bool.not_true, Bool.false_or] at hg
    have hh : ∀ i : Nat, (h : i < rs.length) →
        let q := (p ++ [r]) ++ rs.take i
        rs[i] ∈ nextRows n d q ∧ rowOK n d q rs[i] = true := by
      intro i h
      have hh' : i+1 < (r::rs).length := by simpa using h
      have hx := head (i+1) hh'
      dsimp only at hx
      have hget : (r::rs)[i+1]'hh' = rs[i] := rfl
      rw [hget] at hx
      simpa [List.take_succ_cons, List.append_assoc] using hx
    simpa [List.append_assoc] using ih (p++[r]) hh hg


theorem catalogue_of_checks {n : Nat} (passed : check n = true) (d rows : List Nat)
    (dh : d.length = n) (rh : rows.length = n)
    (ordered : d.Pairwise (· ≥ ·))
    (lo : ∀ j ∈ d, 3 ≤ j) (hi : ∀ j ∈ d, j ≤ n-1)
    (cost : (d.map (fun a => a*(a-1))).sum ≤ n*(n-1)) (even : d.sum % 2 = 0)
    (valid : ∀ (i : Nat) (h : i < rows.length),
      let p := rows.take i
      let r := rows[i]
      (r = incoming n p.length p ||| pack ((vertices n p.length).map (hits n r))) ∧
      (d[p.length]?.getD 0 = (p.map (fun s => hits n s p.length)).count true +
            ((vertices n p.length).map (hits n r)).count true) ∧
      (vertices n p.length).Pairwise (fun u v =>
        key n d p u = key n d p v → hits n r u = false → hits n r v = false) ∧
      rowOK n d p r = true) : leaf n rows = true := by
  have hd := deg_mem (n:=n) d ordered lo hi cost
  rw [dh] at hd
  have hh := List.all_eq_true.mp passed d hd
  have hh' : visit n d n [] = true := by simpa [even] using hh
  have h := visit_sound (n:=n) d [] rows (by
    intro i hi
    obtain ⟨h1,h2,h3,h4⟩ := valid i hi
    simp only [List.nil_append]
    exact ⟨nextRows_mem d (rows.take i) rows[i] h1 h2 h3,h4⟩) (rh ▸ hh')
  simpa using h

end Census904

namespace Census904

def hintWords (n : Nat) : Array Nat :=
  match n with
  | 10 => #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3077, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
  | 11 => #[0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4098, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 10, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 12 => #[0, 14347, 0, 0, 0, 5, 10, 0, 0, 0, 0, 0, 0, 7, 7, 0, 5, 41, 4, 0, 35335, 0, 0, 0, 0, 0, 0, 0, 15367, 0, 0, 0, 0, 31, 0, 4, 0, 14, 0, 0, 44, 1, 0, 63, 42, 0, 1025, 19971, 0, 0, 0, 11, 10, 0, 0, 7684, 3, 30, 23066, 13, 8, 0, 27138, 0, 0, 0, 17, 0, 0, 6580602370, 0, 10249, 0, 9, 58, 0, 0, 8200, 0, 17922, 0, 1, 0, 0, 0, 25612, 56, 0, 0, 23, 0, 0, 0, 0, 32, 0, 0, 1, 14, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 20, 0, 0, 3149313, 0, 0, 0, 25, 57, 16, 0, 0, 17858589, 0, 8, 14347, 62, 0, 0, 0, 0, 29, 3, 0, 0, 1, 0, 0, 19, 37, 0, 7, 0, 0, 0, 1, 36, 0, 2561, 1, 67, 0, 1, 31, 0, 5637, 2, 65, 33801, 0, 11778, 6, 0, 55, 4, 0, 5, 0, 8, 0, 0, 0, 22, 0, 5637, 0, 2049, 46, 0, 0, 3, 0, 6, 0, 33, 18, 0, 0, 0, 52, 0, 11270, 0, 0, 0, 12305, 24, 9, 0, 25, 38, 6150, 2362372, 26, 5, 2, 6664, 0, 61, 0, 5122, 33, 0, 0, 43, 1, 18, 19, 0, 0, 32, 14, 27, 15, 17424, 24582, 0, 0, 59, 10, 2, 21, 3, 0, 10, 0, 6662, 60, 47, 9, 0, 13827, 27652, 20484, 0, 4099, 34, 26133, 0, 0]
  | 13 => #[2956990465, 19957811261973, 6747416466439, 5037074034472985, 11443313164687364, 48231167077, 1120391519658597061756417, 17474020401, 87579, 2466158778407739203073, 16381649415, 3407265084978004514307, 7043067366087689, 2069373639388295348245, 343575520632145385231345279533, 2743795704249071444491, 11793580502813187, 11768910090258, 41510, 711505945365181578340998149, 354460049697482662002683030025, 4703837669171135489, 8382890203680770, 13965993475, 8203033614, 7226034231811, 900396519322074695377623049, 16930388088324, 27692696087, 1649694866876591072359426, 1333657049513618484233730, 40115208, 9965024618233863, 5696705400726884355, 14301986299911, 6275068587987704326, 1479295731611210242, 35727363589, 118926161476046676697770043059215364, 35416624, 3296335625757165116967, 230324129276193362075511556146690, 92848169, 19873893452290, 10325593172225537, 13276620647074327, 818427614743648174353412, 1343600028802974725709318, 29740, 37627180098, 28868657, 5336138367196475920, 9979922775563, 3039973744360754006548, 191009525569300414370679697717788, 12377167505926, 61667852, 3481040556057430019, 3363147395170604943363, 20010798683651, 3065928721112581, 77345810, 25089058280455, 3464996617000590856, 238093530607440883528716316050946, 42040878604, 43370707486, 5515267, 3027178935470098224132, 4904181334821570562, 751493748199933842040838, 1986449908303613923847, 36383499781, 42802189, 3031634218068482, 10795139994114, 15281785701429, 1073361960678765209064451, 860792131170755283526667, 9698724822037, 6311204242858457602, 96278639, 21674875212804, 25251824134, 4837165494180517895, 17198497796, 6204104942671374850, 12079136, 6801528749060626, 23175935045133, 15857625107, 14783290032671, 4260199135185923, 2813273125006346755, 255451684243892286936881577473, 244, 1219668445323701786116, 60914184, 4823975878211604, 21816712111626, 23822062858258, 1208727223190694401, 9127955352261640, 960548209680844591106, 248033748129332788774115484162, 9136517140, 3139533367128027040258, 40192296971, 1857360558931283808769, 17349551625801, 48066205194, 13033552385, 19495141915, 14644162562, 5574768417426396702, 37, 43228601349, 28773997058, 94923275, 1371736968426953219, 1395019650027330487810, 21244988950, 53751300, 2946567359717081914395, 15475182941186, 23597941595153, 6401808197438685193, 6927429389114412035, 9787862854406657, 20439932451, 345947233329572212408320265217, 7823177995545096, 6865564326245706242, 5540078730113190402, 3862233338021426692, 23083528, 18660724737, 10038625329491971, 32110583819, 7293340743375361, 11268144404893189, 8213151481864205, 3289109490671223576583, 8738856415800326, 16099029832225, 6496700458104014337, 714463296473508779399169, 6166387085999614467, 3076578539847532198919, 32535069, 8466614991382, 81539088, 11484481518845445, 16110712785923, 70159, 24836210973224, 26365359306241, 87712815, 5448413956730259969, 6830699911233152005, 690675266286176665612802, 97035310, 3790384584899442183, 11196134591577602, 10933384515073, 388, 6687712418104612354, 1819645025989394151245825, 2032441688942492522502, 10667675899924484, 7715559257424908, 3529418641056397537296, 5968299686255664129, 3469792285322396830209, 65554433, 10564454678274569, 789559073428199197641729, 109757197999869664419609035147266, 44082242, 93816, 11063379843643958, 2319357928176736541190, 2545981068296, 24321734153, 18099421584898, 6817967987625567237, 80030280, 15051816992, 652656075332768469878785, 1246868989154430027777, 63236097, 36264500746, 96488480, 38577718, 4052811692153369, 3241641742708238, 66626057, 29265505281, 2356052448357603345922, 2723310949406086657, 3066328276720832487434, 8906189148266499, 10806018453519, 34, 15330887337474, 42017319, 1172309745179036162, 3130834809236611924993, 8873145802755, 14588969252865, 5266935794142293005, 40403979, 5376923722793122330, 12428751669038593, 15001803317785, 6253496987238008834, 162559265302687105449141438787585, 2550288519402256864778, 10844841167320631, 194577, 29913214391216085499606377281246981002754, 3208783401512341510, 6554200896705031, 30882142723, 4194371525415943, 6468634419725, 23730396639748, 6047672326, 17419, 6414227668207105, 6727714021617193993, 2975406424995401735, 22019054601, 6961198474044911630, 532357789050656475704461825, 10108347360258, 661251259412826331218970625, 1663982482828250484841482, 6904252280085000, 936474846046084017138960898, 2819381005826, 31581818886, 15344071384606, 6742385144829847556, 2200540520402916353, 3207282537269764, 709260306613081890099207, 1678546410087916550, 694614059318405108895059462, 16133692493, 49313837]
  | _ => #[]

end Census904

namespace Census904

def searchHints (n : Nat) (p : List Nat) : Nat → Nat → Bool
  | 0, _ => false
  | t+1, code => if code == 0 then false else
    (match (palettes n)[code % 512 - 1]? with
     | some palette => paletteOK n p palette
     | none => false) || searchHints n p t (code / 512)

def fastLeaf (n : Nat) (p : List Nat) : Bool :=
  (exceptions n).contains p ||
    searchHints n p 32 ((hintWords n)[p.foldl (fun h r => (37*h+r)%251) 0]?.getD 0)

lemma searchHints_sound (n : Nat) (p : List Nat) (t code : Nat)
    (h : searchHints n p t code = true) : (palettes n).any (paletteOK n p) = true := by
  induction t generalizing code with
  | zero => simp [searchHints] at h
  | succ t ih =>
    simp only [searchHints] at h
    split at h
    · contradiction
    rcases Bool.or_eq_true_iff.mp h with hp | hp
    · split at hp
      next g eq =>
        exact List.any_eq_true.mpr ⟨g, List.mem_of_getElem? eq, hp⟩
      next => contradiction
    · exact ih _ hp

def fastVisit (n : Nat) (d : List Nat) : Nat → List Nat → Bool
  | 0, p => fastLeaf n p
  | t+1, p => (nextRows n d p).all fun r =>
    !(rowOK n d p r) || fastVisit n d t (p++[r])

lemma fastVisit_sound (n : Nat) (d : List Nat) (t : Nat) (p : List Nat)
    (h : fastVisit n d t p = true) : visit n d t p = true := by
  induction t generalizing p with
  | zero =>
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inl h)
    · exact Bool.or_eq_true_iff.mpr (Or.inr (searchHints_sound _ _ _ _ h))
  | succ t ih =>
    apply List.all_eq_true.mpr
    intro r hr
    rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp h r hr) with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inl h)
    · exact Bool.or_eq_true_iff.mpr (Or.inr (ih _ h))

end Census904

namespace Census904

def layer (n : Nat) (d : List Nat) : Nat → List Nat → List (List Nat)
  | 0,p => [p]
  | t+1,p => ((nextRows n d p).filter (rowOK n d p)).flatMap
      (fun r => layer n d t (p++[r]))

lemma accept_layer (n : Nat) (d : List Nat) (s t : Nat) (p : List Nat)
    (verified : ∀ v ∈ layer n d s p, fastVisit n d t v = true) :
    fastVisit n d (s+t) p = true := by
  induction s generalizing p with
  | zero => simpa using verified p (by simp [layer])
  | succ s ih =>
    rw [Nat.succ_add, fastVisit, List.all_eq_true]
    intro r hr
    by_cases ok : rowOK n d p r = true
    · apply Bool.or_eq_true_iff.mpr; right
      apply ih
      intro v hv
      apply verified v
      exact List.mem_flatMap.mpr ⟨r,List.mem_filter.mpr ⟨hr,ok⟩,hv⟩
    · simp [Bool.eq_false_of_not_eq_true ok]

def piece (n : Nat) (d : List Nat) (s t bucket i : Nat) :=
  (layer n d s []).all (fun p =>
    (p.foldl (fun h r => h*37+r) 0 % bucket != i) || fastVisit n d t p)

lemma accept_pieces {n bucket s t : Nat} (d : List Nat) (hb : 0<bucket) (st : n=s+t)
    (parts : ∀ i < bucket, piece n d s t bucket i = true) : visit n d n [] = true := by
  apply fastVisit_sound

  subst n
  apply accept_layer
  intro v hv
  let z := v.foldl (fun (h r : Nat) => h*37+r) 0 % bucket
  have h := List.all_eq_true.mp (parts z (Nat.mod_lt _ hb)) v hv
  simpa [z] using h

end Census904

namespace Census904

abbrev Column := Nat × Nat × Nat × Nat

def colCache (n : Nat) (d p : List Nat) : List Column :=
  ((List.range n).drop p.length).map fun j =>
    (d[j]?.getD 0,incoming n j p,(p.map (fun s => hits n s j)).count true,bit n j)

def advanceCol (place r : Nat) (k : Column) : Column :=
  if r &&& k.2.2.2 == 0 then k else (k.1,k.2.1+place,k.2.2.1+1,k.2.2.2)

def localGenerate : List Column → Nat → Nat → Option Key → Nat → List Nat
  | [], _, _, _, need => if need == 0 then [0] else []
  | k::ks, len, pow, block, need =>
    if len < need then [] else
      let tag := (k.1,k.2.1)
      localGenerate ks (len-1) (pow/2) (some tag) need ++
      (if 0 < need ∧ some tag != block then
        (localGenerate ks (len-1) (pow/2) none (need-1)).map (pow + ·)
       else [])

def rowTests (n : Nat) (d p : List Nat) : List (Nat × Nat) :=
  p.zipIdx.map fun (s,j) =>
    (s, if d[j]? == d[p.length]? then (2^n-1) ^^^ (bit n p.length ||| bit n j) else 0)

def testsOK (tests : List (Nat × Nat)) (r : Nat) : Bool :=
  tests.all fun (s,k) => small (s &&& r) && (s &&& k >= r &&& k)

private theorem pack_snoc (bs : List Bool) (b : Bool) :
    pack (bs++[b]) = 2*pack bs + (if b then 1 else 0) := by
  induction bs with
  | nil => cases b <;> rfl
  | cons a bs ih =>
    cases a <;> simp [pack,ih,Nat.pow_succ]; omega

private theorem incoming_snoc (n j r : Nat) (p : List Nat) (h : p.length < n) :
    incoming n j (p++[r]) = incoming n j p + if hits n r j then bit n p.length else 0 := by
  have height : n-p.length = n-1-p.length+1 := by omega
  have hsmall : n-(p.length+1) = n-1-p.length := by omega
  simp only [incoming, List.map_append,List.map_cons,List.map_nil,pack_snoc,
    List.length_append,List.length_singleton, Nat.shiftLeft_eq_mul_pow,hsmall]
  change (2*pack (p.map (fun s => hits n s j)) + (if hits n r j then 1 else 0)) * _ = _
  rw [height,Nat.pow_succ]
  cases eq : hits n r j <;> simp [bit,hits] <;> ring

private def colAt (n : Nat) (d p : List Nat) (j : Nat) : Column :=
    (d[j]?.getD 0,incoming n j p,(p.map (fun s => hits n s j)).count true,bit n j)

private theorem update_at (n : Nat) (d p : List Nat) (j r : Nat) (h : p.length < n) :
    advanceCol (bit n p.length) r (colAt n d p j) = colAt n d (p++[r]) j := by
  have hs := incoming_snoc n j r p h
  cases hit : hits n r j
  · have hz : r &&& bit n j = 0 := by simpa [hits] using hit
    simp [advanceCol,colAt,hz,hs,hit]
  · have hz : ¬r &&& bit n j = 0 := by simpa [hits] using hit
    simp [advanceCol,colAt,hz,hs,hit]

private theorem cache_cons (n : Nat) (d p : List Nat) (h : p.length < n) :
    colCache n d p = colAt n d p p.length :: (vertices n p.length).map (colAt n d p) := by
  have le : p.length < (List.range n).length := by simpa
  unfold colCache
  rw [List.drop_eq_getElem_cons le]
  simp only [List.map_cons, List.getElem_range]
  rfl

private theorem cache_next (n : Nat) (d p : List Nat) (r : Nat) (h : p.length < n) :
    ((vertices n p.length).map (colAt n d p)).map (advanceCol (bit n p.length) r)
      = colCache n d (p++[r]) := by
  simp only [List.map_map,colCache,List.length_append,List.length_singleton]
  apply List.map_congr_left
  intro j _
  exact update_at n d p j r h

private theorem rowTests_agree (n : Nat) (d p : List Nat) (r : Nat) :
    testsOK (rowTests n d p) r = rowOK n d p r := by
  unfold testsOK rowTests rowOK
  rw [List.all_map]
  apply List.all_congr rfl
  intro j
  obtain ⟨s,i⟩ := j
  by_cases eq : d[i]? = d[p.length]?
  · simp [eq]
  · simp [eq]

private abbrev tag (k : Column) : Key := (k.1,k.2.1)

private theorem local_complete (cols : List Column) (bs : List Key) (blocked : Option Key)
    (hb : ∀ x, blocked = some x → x ∈ bs) (need : Nat) :
    generate (cols.map tag) bs need ⊆ localGenerate cols cols.length (2^cols.length/2) blocked need := by
  induction cols generalizing need bs blocked with
  | nil => simp [generate,localGenerate]
  | cons k ks ih =>
    intro a ha
    simp only [List.map_cons,generate,List.length_map,List.length_cons,localGenerate,
      Nat.pow_succ,Nat.mul_div_cancel _ (by decide : 0 < 2),Nat.add_sub_cancel] at ha ⊢
    by_cases room : ks.length + 1 < need
    · simp [room] at ha
    · simp only [room,ite_false,List.mem_append] at ha ⊢
      rcases ha with h | h
      · exact Or.inl (ih _ _ (fun x eq => by cases eq; simp) _ h)
      · by_cases sub : 0 < need ∧ tag k ∉ bs
        · have diff : some (tag k) != blocked := by
            apply bne_iff_ne.mpr
            intro eq
            exact sub.2 (hb (tag k) eq.symm)
          rw [ite_eq_left sub,List.mem_map] at h
          rw [ite_eq_left (show 0 < need ∧ some (tag k) != blocked from ⟨sub.1,diff⟩)]
          obtain ⟨m,hm,rfl⟩ := h
          exact Or.inr (List.mem_map.mpr ⟨m,ih _ _ (by simp) _ hm,rfl⟩)
        · rw [ite_eq_right sub] at h
          contradiction

private theorem layer_length (n : Nat) (d : List Nat) (s : Nat) (p v : List Nat)
    (hv : v ∈ layer n d s p) : v.length = p.length+s := by
  induction s generalizing p with
  | zero => simpa [layer] using congrArg List.length (show v=p by simpa [layer] using hv)
  | succ s ih =>
    obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hv
    have hl := ih _ hr
    simp only [List.length_append,List.length_singleton] at hl
    omega

def occGenerate : List Column → Nat → Nat → Option Key → Nat → Nat → List Nat
  | [], _, _, _, need, _ => if need == 0 then [0] else []
  | k::ks, len, pow, block, need, occupied =>
    if len < need then [] else
      let tag := (k.1,k.2.1)
      occGenerate ks (len-1) (pow/2) (some tag) need occupied ++
      (if 0 < need ∧ some tag != block ∧ k.2.1 &&& occupied == 0 then
        (occGenerate ks (len-1) (pow/2) none (need-1) (occupied ||| k.2.1)).map (pow + ·)
       else [])

def startOccupied (n : Nat) (p : List Nat) (low : Nat) : Nat :=
  pack (p.map (fun r => r &&& low != 0)) <<< (n-p.length)

def occVisit (n : Nat) (d : List Nat) : Nat → List Nat → List Column → Bool
  | 0,p,_ => fastLeaf n p
  | _+1,_,[] => true
  | t+1,p,k::ks =>
    if k.2.2.1 > k.1 || k.1-k.2.2.1 > t then true else
    let tests := rowTests n d p
    let place := k.2.2.2
    (occGenerate ks t (place / 2) none (k.1-k.2.2.1) (startOccupied n p k.2.1)).all fun tail =>
      let r := tail ||| k.2.1
      !(testsOK tests r) || occVisit n d t (p++[r]) (ks.map (advanceCol place r))

def occState (n : Nat) (d : List Nat) (t : Nat) (p : List Nat) : Bool :=
  occVisit n d t p (colCache n d p)

private theorem pack_bound (xs : List Bool) : pack xs < 2 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    rw [pack, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

private theorem pack_bit (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (pack xs).testBit (xs.length - 1 - i) = xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b xs ih =>
    cases i with
    | zero =>
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
      cases b
      · simpa [pack] using (Nat.testBit_lt_two_pow (pack_bound xs))
      · apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
        · simp [pack]
        · simp only [pack, ite_true, Nat.pow_succ]
          have := pack_bound xs
          omega
    | succ k =>
      have hk : k < xs.length := by simpa using hi
      have idx : (b :: xs).length - 1 - (k+1) = xs.length - 1 - k := by simp; omega
      have smallIdx : xs.length - 1 - k < xs.length := by omega
      rw [idx, List.getElem_cons_succ, ← ih k hk]
      cases b
      · simp [pack]
      · exact Nat.testBit_two_pow_add_gt smallIdx _

private theorem small_of_unique (r : ℕ)
    (uniq : ∀ u v, r.testBit u = true → r.testBit v = true → u = v) :
    small r = true := by
  by_cases hr : r = 0
  · simp [small,hr]
  obtain ⟨u,hu,_⟩ := Nat.exists_most_significant_bit hr
  have hpow : r = 2^u := by
    apply Nat.eq_of_testBit_eq
    intro v
    rw [Nat.testBit_two_pow]
    by_cases h : u = v
    · simpa [h] using hu
    · have hv : r.testBit v = false := Bool.eq_false_of_not_eq_true (fun h' => h (uniq u v hu h'))
      simp [h,hv]
  subst r
  simp [small]

theorem occ_bit_small (h : small x = true) :
    ∀ a b : Nat, x.testBit a = true → x.testBit b = true → a = b := by
  by_cases zero : x = 0
  · simp [zero]
  have hz : x &&& (x-1)=0 := beq_iff_eq.mp h
  obtain ⟨i, hi⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo zero).mp hz
  intro a b ha hb
  simpa [hi,Nat.testBit_two_pow] using Eq.trans (of_decide_eq_true (by simpa [hi,Nat.testBit_two_pow] using ha : decide (i=a)=true)).symm (of_decide_eq_true (by simpa [hi,Nat.testBit_two_pow] using hb : decide (i=b)=true))

private lemma bitList (n : Nat) (p : List Nat) (f : Nat → Bool) (u : Nat) (hn : p.length ≤ n) :
    ((pack (p.map f)) <<< (n-p.length)).testBit u =
       if hu : n-p.length ≤ u ∧ u<n then f (p[n-1-u]'(by omega)) else false := by
  rw [Nat.testBit_shiftLeft]
  by_cases hu : n-p.length ≤ u
  · rw [decide_eq_true hu, Bool.true_and]
    by_cases hlt : u < n
    · have he : u - (n-p.length) = (p.map f).length-1-(n-1-u) := by simp; omega
      rw [he, pack_bit (p.map f) (n-1-u) (by simp; omega)]
      simp [hu,hlt]
    · have lt : pack (p.map f) < 2^(u-(n-p.length)) :=
        (pack_bound _).trans_le (Nat.pow_le_pow_right (by decide) (by simp; omega))
      simp [hu,hlt,Nat.testBit_lt_two_pow lt]
  · simp [hu]

theorem occ_or (n : Nat) (p : List Nat) (a b : Nat) (hn : p.length ≤ n) :
    startOccupied n p (a ||| b) = startOccupied n p a ||| startOccupied n p b := by
  apply Nat.eq_of_testBit_eq
  intro u
  unfold startOccupied
  rw [Nat.testBit_or, bitList _ _ _ _ hn, bitList _ _ _ _ hn, bitList _ _ _ _ hn]
  split
  · simp only [Nat.and_or_distrib_left]
    apply Bool.eq_iff_iff.mpr
    simp [Nat.or_eq_zero_iff]; tauto
  · rfl

theorem occ_new (n : Nat) (p : List Nat) (j : Nat) :
    startOccupied n p (bit n j) = incoming n j p := rfl

theorem occ_separate (n : Nat) (p : List Nat) (a b : Nat) (hn : p.length ≤ n)
    (ab : a &&& b = 0)
    (ok : ∀ s ∈ p, small (s &&& (a ||| b)) = true) :
    startOccupied n p a &&& startOccupied n p b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro u
  unfold startOccupied
  rw [Nat.testBit_and, bitList _ _ _ _ hn, bitList _ _ _ _ hn, Nat.zero_testBit]
  split
  next h =>
    simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq]
    let s := p[n-1-u]'(by omega)
    change s &&& a = 0 ∨ s &&& b = 0
    by_contra! h'
    let i := (s &&& a).log2
    let k := (s &&& b).log2
    obtain ⟨hi₁,hi₂⟩ := Bool.and_eq_true_iff.mp (Nat.testBit_and .. ▸ Nat.testBit_log2 h'.1)
    obtain ⟨hk₁,hk₂⟩ := Bool.and_eq_true_iff.mp (Nat.testBit_and .. ▸ Nat.testBit_log2 h'.2)
    have eq : i=k := occ_bit_small (ok s (List.getElem_mem _)) i k
      (by simp [Nat.testBit_and,Nat.testBit_or,hi₁,hi₂,i])
      (by simp [Nat.testBit_and,Nat.testBit_or,hk₁,hk₂,k])
    have both : (a &&& b).testBit i = true := by rw [Nat.testBit_and]; exact Bool.and_eq_true_iff.mpr ⟨hi₂,eq.symm ▸ hk₂⟩
    simp [ab] at both
  next => simp

theorem occ_small_drop (s a b : Nat) (h : small (s &&& (a ||| b)) = true) : small (s &&& a) = true := by
  apply small_of_unique
  intro u v hu hv
  have hup := Bool.and_eq_true_iff.mp (Nat.testBit_and .. ▸ hu)
  have hvp := Bool.and_eq_true_iff.mp (Nat.testBit_and .. ▸ hv)
  exact occ_bit_small h _ _ (by simp [Nat.testBit_and,Nat.testBit_or,hup]) (by simp [Nat.testBit_and,Nat.testBit_or,hvp])

def occAligned (n : Nat) (p : List Nat) : List Column → Prop
  | [] => True
  | k::ks => k.2.1 = startOccupied n p (2^ks.length) ∧ occAligned n p ks

private theorem bound_local (cols : List Column) (block : Option Key) (k q : Nat)
    (hq : q ∈ localGenerate cols cols.length (2^cols.length/2) block k) :
    q < 2^cols.length := by
  induction cols generalizing block k q with
  | nil => by_cases h : k=0 <;> simp_all [localGenerate]
  | cons c cs ih =>
    simp only [List.length_cons, localGenerate, Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0<2),
      Nat.add_sub_cancel] at hq ⊢
    split at hq
    · contradiction
    rcases List.mem_append.mp hq with h|h
    · have := ih _ _ _ h
      omega
    · split at h
      · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
        have := ih _ _ _ hr
        omega
      · contradiction

theorem keep_occ (n : Nat) (p : List Nat) (cols : List Column) (hn : p.length ≤ n)
    (aligned : occAligned n p cols) (k : Nat) (block : Option Key) (x part : Nat)
    (hx : x ∈ localGenerate cols cols.length (2^cols.length/2) block k)
    (partHigh : ∀ j < cols.length, part.testBit j = false)
    (valid : ∀ a ∈ p, small (a &&& (part ||| x)) = true) :
    x ∈ occGenerate cols cols.length (2^cols.length/2) block k (startOccupied n p part) := by
  induction cols generalizing block k x part with
  | nil => exact hx
  | cons c cs ih =>
    obtain ⟨hc,ha⟩ := aligned
    simp only [List.length_cons, localGenerate, occGenerate, Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide : 0<2), Nat.add_sub_cancel] at hx ⊢
    by_cases room : cs.length + 1 < k
    · simp [room] at hx
    · simp only [room,ite_false,List.mem_append] at hx ⊢
      rcases hx with hx|hx
      · exact Or.inl (ih ha _ _ _ _ hx (fun j hj => partHigh j (by simp; omega)) valid)
      · split at hx
        next cond =>
          obtain ⟨tail,ht,hval⟩ := List.mem_map.mp hx
          subst x
          have hlt := bound_local cs _ _ _ ht
          let u := 2^cs.length
          have sum : 2^cs.length + tail = u ||| tail := by
            simpa [u] using Nat.two_pow_add_eq_or_of_lt hlt 1
          have valid' : ∀ a ∈ p, small (a &&& ((part ||| u) ||| tail)) = true := by
            intro a h
            simpa only [sum,Nat.or_assoc] using valid a h
          have pu : part &&& u = 0 := by
            simp [u,Nat.and_two_pow,partHigh cs.length (by simp)]
          have no : c.2.1 &&& startOccupied n p part = 0 := by
            rw [hc,Nat.and_comm]
            exact occ_separate n p part u hn pu fun a h => occ_small_drop a _ tail (valid' a h)
          rw [ite_eq_left (show 0<k ∧ some (c.1,c.2.1) != block ∧ c.2.1 &&& startOccupied n p part == 0
                          from ⟨cond.1,cond.2,beq_iff_eq.mpr no⟩)]
          apply Or.inr
          apply List.mem_map.mpr
          refine ⟨tail,?_,rfl⟩
          rw [hc,← occ_or _ _ _ _ hn]
          apply ih ha _ _ _ (part ||| u) ht _ valid'
          intro j hj
          simp [Nat.testBit_or,partHigh j (by simp; omega),u,Nat.testBit_two_pow,Nat.ne_of_gt hj]
        next => contradiction

private theorem occAlignFrom (n : Nat) (d p : List Nat) (left off : Nat) (sum : off+left=n) :
    occAligned n p (((List.range n).drop off).map (colAt n d p)) := by
  induction left generalizing off with
  | zero =>
    have hd : (List.range n).drop off = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [hd]
    trivial
  | succ left ih =>
    have lt : off < (List.range n).length := by simp; omega
    rw [List.drop_eq_getElem_cons lt, List.map_cons]
    constructor
    · have L : (((List.range n).drop (off+1)).map (colAt n d p)).length = n-1-off := by
        simp
        omega
      simp only [L, List.getElem_range,colAt]
      exact (occ_new n p off).symm
    · exact ih (off+1) (by omega)

theorem occState_sound {n : Nat} {d p : List Nat} {t : Nat} (ht : p.length+t=n)
    (h : occState n d t p = true) : fastVisit n d t p = true := by
  induction t generalizing p with
  | zero => exact h
  | succ t ih =>
    have hl : p.length < n := by omega
    let k := colAt n d p p.length
    let ks := (vertices n p.length).map (colAt n d p)
    have len : (vertices n p.length).length = t := by simp [vertices]; omega
    have len' : ks.length = t := by simp [ks,len]
    have pow : bit n p.length = 2 ^ t := by unfold bit; congr 1; omega
    have cache := cache_cons n d p hl
    change colCache n d p = k::ks at cache
    unfold occState at h
    rw [cache,occVisit] at h
    rw [fastVisit,List.all_eq_true]
    intro r hr
    unfold nextRows at hr
    simp only [len] at hr
    change r ∈ (if (decide (k.2.2.1 > k.1) || decide (k.1-k.2.2.1 > t)) then [] else _) at hr
    by_cases no : k.2.2.1 > k.1 || k.1 - k.2.2.1 > t
    · rw [ite_eq_left no] at hr
      contradiction
    · rw [ite_eq_right no,List.all_eq_true] at h
      rw [ite_eq_right no,List.mem_map] at hr
      obtain ⟨mask,hm,rfl⟩ := hr
      have hg := local_complete ks [] none (by simp) (k.1-k.2.2.1)
      have tags : ks.map tag = (vertices n p.length).map (key n d p) := by simp [ks,tag,colAt,key]
      rw [tags] at hg
      have hm' := hg hm
      change (! rowOK n d p (k.2.1 ||| mask) || fastVisit n d t (p++[k.2.1 ||| mask])) = true
      cases good : rowOK n d p (k.2.1 ||| mask)
      · simp
      · simp only [good,Bool.not_true,Bool.false_or]
        have square : ∀ v ∈ p, small (v &&& (k.2.1 ||| mask)) = true := by
          intro v hv
          obtain ⟨i,hi,he⟩ := List.getElem_of_mem hv
          have hz : (v,i) ∈ p.zipIdx := by
            apply List.mem_iff_getElem.mpr
            refine ⟨i,by simp [hi],?_⟩
            simpa [he]
          exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp good _ hz)).1
        have hhigh : ∀ j < ks.length, k.2.1.testBit j = false := by
          intro j hj
          change (incoming n p.length p).testBit j = false
          rw [incoming,Nat.testBit_shiftLeft]
          have less : ¬ n-p.length ≤ j := by omega
          simp [less]
        have aligned : occAligned n p ks := occAlignFrom n d p t (p.length+1) (by omega)
        have legal := keep_occ n p ks (by omega) aligned (k.1-k.2.2.1) none mask k.2.1 hm' hhigh square
        rw [len',← pow] at legal
        have H := h mask legal
        dsimp only at H
        rw [Nat.or_comm mask k.2.1, rowTests_agree,good] at H
        simp only [Bool.not_true,Bool.false_or] at H
        apply ih (p:=p++[k.2.1 ||| mask]) (by simp; omega)
        unfold occState
        rwa [← cache_next n d p _ hl]

-- Test each completed row immediately. Once all requested neighbors have been
-- chosen, the remaining columns have only one possible choice.
def allLegalTails : List Column → Nat → Nat → Option Key → Nat → Nat → Nat → (Nat → Bool) → Bool
  | [], _, _, _, need, row, _, accept => need != 0 || accept row
  | col :: cols, len, place, blocked, need, row, occupied, accept =>
    if need == 0 then accept row else
    if len < need then true else
      let tag := (col.1, col.2.1)
      allLegalTails cols (len-1) (place/2) (some tag) need row occupied accept &&
        (some tag == blocked || col.2.1 &&& occupied != 0 ||
          allLegalTails cols (len-1) (place/2) none (need-1) (place+row) (occupied ||| col.2.1) accept)

private theorem occ_no_more (cols : List Column) (len place : Nat) (blocked : Option Key) (occupied : Nat) :
    occGenerate cols len place blocked 0 occupied = [0] := by
  induction cols generalizing len place blocked with
  | nil => rfl
  | cons col cols ih => simp [occGenerate,ih]

private theorem allLegalTails_eq (cols : List Column) (len place : Nat) (blocked : Option Key)
    (need row occupied : Nat) (accept : Nat → Bool) :
    allLegalTails cols len place blocked need row occupied accept =
      (occGenerate cols len place blocked need occupied).all (fun tail => accept (tail + row)) := by
  induction cols generalizing len place blocked need row occupied with
  | nil => by_cases z : need = 0 <;> simp [allLegalTails,occGenerate,z]
  | cons col cols ih =>
    by_cases z : need = 0
    · subst need
      simp [allLegalTails,occ_no_more]
    have pos := Nat.pos_of_ne_zero z
    have nz : (need == 0) = false := beq_eq_false_iff_ne.mpr z
    by_cases full : len < need
    · simp [allLegalTails,occGenerate,full,nz]
    by_cases blockedHere : some (col.1,col.2.1) = blocked
    · simp [allLegalTails,occGenerate,full,nz,blockedHere,ih]
    have unlocked : (some (col.1,col.2.1) == blocked) = false := beq_eq_false_iff_ne.mpr blockedHere
    by_cases free : col.2.1 &&& occupied = 0
    · simp [allLegalTails,occGenerate,full,nz,unlocked,free,blockedHere,pos,ih,List.all_map,
        Function.comp_def,Nat.add_left_comm,Nat.add_comm]
    · simp [allLegalTails,occGenerate,full,nz,free,ih]

def prunedVisit (n : Nat) (d : List Nat) : Nat → List Nat → List Column → Bool
  | 0,p,_ => fastLeaf n p
  | _+1,_,[] => true
  | t+1,p,k::ks =>
    if k.2.2.1 > k.1 || k.1-k.2.2.1 > t then true else
      let tests := rowTests n d p
      let place := k.2.2.2
      allLegalTails ks t (place/2) none (k.1-k.2.2.1) 0 (startOccupied n p k.2.1) fun tail =>
        let row := tail ||| k.2.1
        !(testsOK tests row) || prunedVisit n d t (p++[row]) (ks.map (advanceCol place row))

private theorem prunedVisit_eq (n : Nat) (d : List Nat) (t : Nat) (p : List Nat) (cols : List Column) :
    prunedVisit n d t p cols = occVisit n d t p cols := by
  induction t generalizing p cols with
  | zero => rfl
  | succ t ih =>
    cases cols with
    | nil => rfl
    | cons k ks => simp [prunedVisit,occVisit,allLegalTails_eq,ih]

def prunedState (n : Nat) (d : List Nat) (t : Nat) (p : List Nat) : Bool :=
  prunedVisit n d t p (colCache n d p)

theorem prunedState_sound {n : Nat} {d p : List Nat} {t : Nat} (ht : p.length+t=n)
    (h : prunedState n d t p = true) : fastVisit n d t p = true := by
  apply occState_sound ht
  simpa only [prunedState,prunedVisit_eq,occState] using h

def prunedPiece (n : Nat) (d : List Nat) (s t bucket i : Nat) : Bool :=
  (layer n d s []).all (fun p =>
    (p.foldl (fun h r => h*37+r) 0 % bucket != i) || prunedState n d t p)

theorem prunedPiece_sound {n s t bucket i : Nat} {d : List Nat} (ht : s+t=n)
    (h : prunedPiece n d s t bucket i = true) : piece n d s t bucket i = true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain hskip | need := Bool.or_eq_true_iff.mp (List.all_eq_true.mp h p hp)
  · exact Bool.or_eq_true_iff.mpr (Or.inl hskip)
  · have len := layer_length n d s [] _ hp
    simp only [List.length_nil, Nat.zero_add] at len
    exact Bool.or_eq_true_iff.mpr (Or.inr (prunedState_sound (by omega) need))

private theorem smallFromPruned (n : Nat) (d : List Nat) (h : prunedState n d n [] = true) :
    visit n d n [] = true := by
  exact fastVisit_sound n d n [] (prunedState_sound (by simp) h)


theorem check1 : check 1 = true := by
  have h : (degreeOptions 1 1 0 0).filter (fun d => d.sum % 2 == 0) = [] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp at hm
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

theorem check2 : check 2 = true := by
  have h : (degreeOptions 2 2 1 2).filter (fun d => d.sum % 2 == 0) = [] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp at hm
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

theorem check3 : check 3 = true := by
  have h : (degreeOptions 3 3 2 6).filter (fun d => d.sum % 2 == 0) = [] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp at hm
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

theorem check4 : check 4 = true := by
  have h : (degreeOptions 4 4 3 12).filter (fun d => d.sum % 2 == 0) = [] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp at hm
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

theorem check5 : check 5 = true := by
  have h : (degreeOptions 5 5 4 20).filter (fun d => d.sum % 2 == 0) = [] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp at hm
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

theorem check6 : check 6 = true := by
  have h : (degreeOptions 6 6 5 30).filter (fun d => d.sum % 2 == 0) = [] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp at hm
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

theorem check7 : check 7 = true := by
  have h : (degreeOptions 7 7 6 42).filter (fun d => d.sum % 2 == 0) = [] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp at hm
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run8_0 : visit 8 [3,3,3,3,3,3,3,3] 8 [] = true := smallFromPruned _ _ (by decide +kernel)
theorem check8 : check 8 = true := by
  have h : (degreeOptions 8 8 7 56).filter (fun d => d.sum % 2 == 0) = [[3,3,3,3,3,3,3,3]] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl
    · simp only [run8_0, Bool.or_true]
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run9_0 : visit 9 [4,3,3,3,3,3,3,3,3] 9 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run9_1 : visit 9 [4,4,4,3,3,3,3,3,3] 9 [] = true := smallFromPruned _ _ (by decide +kernel)
theorem check9 : check 9 = true := by
  have h : (degreeOptions 9 9 8 72).filter (fun d => d.sum % 2 == 0) = [[4,3,3,3,3,3,3,3,3], [4,4,4,3,3,3,3,3,3]] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · simp only [run9_0, Bool.or_true]
    · simp only [run9_1, Bool.or_true]
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run10_0 : visit 10 [3,3,3,3,3,3,3,3,3,3] 10 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run10_1 : visit 10 [4,4,3,3,3,3,3,3,3,3] 10 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run10_2 : visit 10 [4,4,4,4,3,3,3,3,3,3] 10 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run10_3 : visit 10 [5,3,3,3,3,3,3,3,3,3] 10 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run10_4 : visit 10 [5,4,4,3,3,3,3,3,3,3] 10 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run10_5 : visit 10 [5,5,3,3,3,3,3,3,3,3] 10 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run10_6 : visit 10 [6,4,3,3,3,3,3,3,3,3] 10 [] = true := smallFromPruned _ _ (by decide +kernel)
theorem check10 : check 10 = true := by
  have h : (degreeOptions 10 10 9 90).filter (fun d => d.sum % 2 == 0) = [[3,3,3,3,3,3,3,3,3,3], [4,4,3,3,3,3,3,3,3,3], [4,4,4,4,3,3,3,3,3,3], [5,3,3,3,3,3,3,3,3,3], [5,4,4,3,3,3,3,3,3,3], [5,5,3,3,3,3,3,3,3,3], [6,4,3,3,3,3,3,3,3,3]] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [run10_0, Bool.or_true]
    · simp only [run10_1, Bool.or_true]
    · simp only [run10_2, Bool.or_true]
    · simp only [run10_3, Bool.or_true]
    · simp only [run10_4, Bool.or_true]
    · simp only [run10_5, Bool.or_true]
    · simp only [run10_6, Bool.or_true]
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_0 : visit 11 [4,3,3,3,3,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_1 : visit 11 [4,4,4,3,3,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_2 : visit 11 [4,4,4,4,4,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_3 : visit 11 [4,4,4,4,4,4,4,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_4 : visit 11 [5,4,3,3,3,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_5 : visit 11 [5,4,4,4,3,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_6 : visit 11 [5,4,4,4,4,4,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_7 : visit 11 [5,5,4,3,3,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_8 : visit 11 [6,3,3,3,3,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_9 : visit 11 [6,4,4,3,3,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_10 : visit 11 [6,5,3,3,3,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run11_11 : visit 11 [7,4,3,3,3,3,3,3,3,3,3] 11 [] = true := smallFromPruned _ _ (by decide +kernel)
theorem check11 : check 11 = true := by
  have h : (degreeOptions 11 11 10 110).filter (fun d => d.sum % 2 == 0) = [[4,3,3,3,3,3,3,3,3,3,3], [4,4,4,3,3,3,3,3,3,3,3], [4,4,4,4,4,3,3,3,3,3,3], [4,4,4,4,4,4,4,3,3,3,3], [5,4,3,3,3,3,3,3,3,3,3], [5,4,4,4,3,3,3,3,3,3,3], [5,4,4,4,4,4,3,3,3,3,3], [5,5,4,3,3,3,3,3,3,3,3], [6,3,3,3,3,3,3,3,3,3,3], [6,4,4,3,3,3,3,3,3,3,3], [6,5,3,3,3,3,3,3,3,3,3], [7,4,3,3,3,3,3,3,3,3,3]] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [run11_0, Bool.or_true]
    · simp only [run11_1, Bool.or_true]
    · simp only [run11_2, Bool.or_true]
    · simp only [run11_3, Bool.or_true]
    · simp only [run11_4, Bool.or_true]
    · simp only [run11_5, Bool.or_true]
    · simp only [run11_6, Bool.or_true]
    · simp only [run11_7, Bool.or_true]
    · simp only [run11_8, Bool.or_true]
    · simp only [run11_9, Bool.or_true]
    · simp only [run11_10, Bool.or_true]
    · simp only [run11_11, Bool.or_true]
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_0 : visit 12 [3,3,3,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_1 : visit 12 [4,4,3,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_2 : visit 12 [4,4,4,4,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_3 : visit 12 [4,4,4,4,4,4,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_4 : visit 12 [4,4,4,4,4,4,4,4,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_5 : visit 12 [4,4,4,4,4,4,4,4,4,4,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_6 : visit 12 [5,3,3,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_7 : visit 12 [5,4,4,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_8 : visit 12 [5,4,4,4,4,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_9 : visit 12 [5,4,4,4,4,4,4,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_10 : visit 12 [5,5,3,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_11 : visit 12 [5,5,4,4,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_12 : visit 12 [5,5,4,4,4,4,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_13 : visit 12 [5,5,5,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_14 : visit 12 [5,5,5,4,4,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_15 : visit 12 [5,5,5,5,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_16 : visit 12 [6,4,3,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_17 : visit 12 [6,4,4,4,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_18 : visit 12 [6,4,4,4,4,4,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_19 : visit 12 [6,5,4,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_20 : visit 12 [6,5,4,4,4,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_21 : visit 12 [6,5,5,4,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_22 : visit 12 [6,6,3,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_23 : visit 12 [6,6,4,4,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_24 : visit 12 [7,3,3,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_25 : visit 12 [7,4,4,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_26 : visit 12 [7,4,4,4,4,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_27 : visit 12 [7,5,3,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run12_28 : visit 12 [8,4,3,3,3,3,3,3,3,3,3,3] 12 [] = true := smallFromPruned _ _ (by decide +kernel)
theorem check12 : check 12 = true := by
  have h : (degreeOptions 12 12 11 132).filter (fun d => d.sum % 2 == 0) = [[3,3,3,3,3,3,3,3,3,3,3,3], [4,4,3,3,3,3,3,3,3,3,3,3], [4,4,4,4,3,3,3,3,3,3,3,3], [4,4,4,4,4,4,3,3,3,3,3,3], [4,4,4,4,4,4,4,4,3,3,3,3], [4,4,4,4,4,4,4,4,4,4,3,3], [5,3,3,3,3,3,3,3,3,3,3,3], [5,4,4,3,3,3,3,3,3,3,3,3], [5,4,4,4,4,3,3,3,3,3,3,3], [5,4,4,4,4,4,4,3,3,3,3,3], [5,5,3,3,3,3,3,3,3,3,3,3], [5,5,4,4,3,3,3,3,3,3,3,3], [5,5,4,4,4,4,3,3,3,3,3,3], [5,5,5,3,3,3,3,3,3,3,3,3], [5,5,5,4,4,3,3,3,3,3,3,3], [5,5,5,5,3,3,3,3,3,3,3,3], [6,4,3,3,3,3,3,3,3,3,3,3], [6,4,4,4,3,3,3,3,3,3,3,3], [6,4,4,4,4,4,3,3,3,3,3,3], [6,5,4,3,3,3,3,3,3,3,3,3], [6,5,4,4,4,3,3,3,3,3,3,3], [6,5,5,4,3,3,3,3,3,3,3,3], [6,6,3,3,3,3,3,3,3,3,3,3], [6,6,4,4,3,3,3,3,3,3,3,3], [7,3,3,3,3,3,3,3,3,3,3,3], [7,4,4,3,3,3,3,3,3,3,3,3], [7,4,4,4,4,3,3,3,3,3,3,3], [7,5,3,3,3,3,3,3,3,3,3,3], [8,4,3,3,3,3,3,3,3,3,3,3]] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [run12_0, Bool.or_true]
    · simp only [run12_1, Bool.or_true]
    · simp only [run12_2, Bool.or_true]
    · simp only [run12_3, Bool.or_true]
    · simp only [run12_4, Bool.or_true]
    · simp only [run12_5, Bool.or_true]
    · simp only [run12_6, Bool.or_true]
    · simp only [run12_7, Bool.or_true]
    · simp only [run12_8, Bool.or_true]
    · simp only [run12_9, Bool.or_true]
    · simp only [run12_10, Bool.or_true]
    · simp only [run12_11, Bool.or_true]
    · simp only [run12_12, Bool.or_true]
    · simp only [run12_13, Bool.or_true]
    · simp only [run12_14, Bool.or_true]
    · simp only [run12_15, Bool.or_true]
    · simp only [run12_16, Bool.or_true]
    · simp only [run12_17, Bool.or_true]
    · simp only [run12_18, Bool.or_true]
    · simp only [run12_19, Bool.or_true]
    · simp only [run12_20, Bool.or_true]
    · simp only [run12_21, Bool.or_true]
    · simp only [run12_22, Bool.or_true]
    · simp only [run12_23, Bool.or_true]
    · simp only [run12_24, Bool.or_true]
    · simp only [run12_25, Bool.or_true]
    · simp only [run12_26, Bool.or_true]
    · simp only [run12_27, Bool.or_true]
    · simp only [run12_28, Bool.or_true]
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)
end Census904

namespace Census904
private def decodeFour (x : Nat) : List Nat := [x >>> 39, (x >>> 26) % 8192, (x >>> 13) % 8192, x % 8192]
private def fr13_0 : List (List Nat) :=
  [2111350122090508, 2111414563508272, 2111414563508512].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_0 : layer 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 [] = fr13_0 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_0 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_1 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_2 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_3 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_4 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_5 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_6 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_7 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 7 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_8 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 8 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_9 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 9 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_10 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 10 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_11 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 11 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_12 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 12 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_13 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 13 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_14 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 14 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_15 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 15 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_0_16 : piece 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 4 9 17 16 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_0]
  decide +kernel

private lemma run13_0 : visit 13 [4,3,3,3,3,3,3,3,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [4,3,3,3,3,3,3,3,3,3,3,3,3] (bucket:=17) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_0_0
  · exact pc13_0_1
  · exact pc13_0_2
  · exact pc13_0_3
  · exact pc13_0_4
  · exact pc13_0_5
  · exact pc13_0_6
  · exact pc13_0_7
  · exact pc13_0_8
  · exact pc13_0_9
  · exact pc13_0_10
  · exact pc13_0_11
  · exact pc13_0_12
  · exact pc13_0_13
  · exact pc13_0_14
  · exact pc13_0_15
  · exact pc13_0_16
private def fr13_1 : List (List Nat) :=
  [527803699492868, 527803699492880, 527803699492896, 527803699493120, 527803701327876, 527803701327904, 527803701328000, 527803701328128, 527803701581825, 527803701581828, 527803701581840, 527803701581856, 527803701581952, 527803701582080, 527803703426048, 1618763510313224, 1618763510829065, 1618763510829313, 1618763510829320, 1618763514500097, 1618763514500104, 1618763514500352, 1618763515008002, 1618763515008008, 1618763515008256, 1618796796434433, 1618796796434448, 1618796796942338, 1618796796942352, 1618796798515202, 1618796798515216, 1618796799006724, 1618796799006736, 1618796800613376, 2111352269410307, 2111352269410562, 2111384481896452, 2111384483928072, 2111418858344460, 2111418858344712].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_1 : layer 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 [] = fr13_1 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_0 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_1 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_2 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_3 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_4 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_5 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_6 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_7 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 7 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_8 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 8 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_9 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 9 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_10 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 10 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_11 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 11 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_12 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 12 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_13 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 13 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_14 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 14 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_15 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 15 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_16 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 16 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_17 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 17 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_18 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 18 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_19 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 19 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_20 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 20 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_21 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 21 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_22 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 22 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_23 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 23 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_24 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 24 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_25 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 25 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_26 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 26 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_27 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 27 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_28 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 28 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_29 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 29 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_30 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 30 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_31 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 31 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_32 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 32 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_33 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 33 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_34 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 34 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_35 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 35 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_1_36 : piece 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 4 9 37 36 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_1]
  decide +kernel

private lemma run13_1 : visit 13 [4,4,4,3,3,3,3,3,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [4,4,4,3,3,3,3,3,3,3,3,3,3] (bucket:=37) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_1_0
  · exact pc13_1_1
  · exact pc13_1_2
  · exact pc13_1_3
  · exact pc13_1_4
  · exact pc13_1_5
  · exact pc13_1_6
  · exact pc13_1_7
  · exact pc13_1_8
  · exact pc13_1_9
  · exact pc13_1_10
  · exact pc13_1_11
  · exact pc13_1_12
  · exact pc13_1_13
  · exact pc13_1_14
  · exact pc13_1_15
  · exact pc13_1_16
  · exact pc13_1_17
  · exact pc13_1_18
  · exact pc13_1_19
  · exact pc13_1_20
  · exact pc13_1_21
  · exact pc13_1_22
  · exact pc13_1_23
  · exact pc13_1_24
  · exact pc13_1_25
  · exact pc13_1_26
  · exact pc13_1_27
  · exact pc13_1_28
  · exact pc13_1_29
  · exact pc13_1_30
  · exact pc13_1_31
  · exact pc13_1_32
  · exact pc13_1_33
  · exact pc13_1_34
  · exact pc13_1_35
  · exact pc13_1_36
private def fr13_2 : List (List Nat) :=
  [1249321971377234, 1249321971500043, 1249321971500099, 1249321971500105, 1249321971500106, 1249321971500113, 1249321971500169, 1249321972425874, 1249321972548619, 1249321972548739, 1249321972548745, 1249321972548746, 1249321972548753, 1249321972548873, 1249321973466131, 1249321973466179, 1249321973466193, 1249321973466194, 1249321973466257, 1249321973466385, 1249321973466433, 1249321973466448, 1249321973580811, 1249321973580819, 1249321973580867, 1249321973580874, 1249321973580882, 1249321973580931, 1249321973580938, 1249321973581059, 1249321973581066, 1249321973581122, 1249321973581128, 1249330288312365, 1249330291983373, 1249330292376597, 1249330292376613, 1249330292376625, 1249330292376628, 1249330292491271, 1249330292491275, 1249330292491278, 1249330292491283, 1249330292491299, 1249330292491302, 1249330292491306, 1249330292491308, 1249330292491314, 1249330292491331, 1249330292491338, 1249330292900885, 1249330292900933, 1249330292900945, 1249330292900948, 1249330293949461, 1249330293949509, 1249330293949521, 1249330293949524, 1249330293949573, 1249330294064135, 1249330294064139, 1249330294064142, 1249330294064147, 1249330294064195, 1249330294064198, 1249330294064202, 1249330294064204, 1249330294064210, 1249330294064259, 1249330294064262, 1249330294064387, 1249330294064394, 1249330294457351, 1249330294457363, 1249330294457366, 1249330294457379, 1249330294457382, 1249330294457394, 1249330294457396, 1249330294457411, 1249330294457426, 1249330294457475, 1249330294457478, 1249330294457603, 1249330294457618, 1249330294457634, 1249330294457648, 1249330294555655, 1249330294555662, 1249330294555670, 1249330294555686, 1249330294555692, 1249330294555700, 1249330294555718, 1249330294555724, 1249330294555782, 1249330294555910, 1249330294555916, 1249330294555940, 1249330294555944, 1249330294981639, 1249330294981651, 1249330294981654, 1249330294981699, 1249330294981702, 1249330294981714, 1249330294981716, 1249330294981763, 1249330294981891, 1249330294981906, 1249330294981954, 1249330294981968, 1794681646145956, 1794689699266665, 1794689699266857, 1794689699266889, 1794689699266913, 1794689699266920, 1794689699266953, 1794689699774507, 1794689699774563, 1794689699774603, 1794689699774731, 1794689699774755, 1794689699774762, 1794689699774787, 1794689699774818, 1794689699774851, 1794689699774858, 1794715469072425, 1794715469072649, 1794715469072673, 1794715469072680, 1794715470104587, 1794715470104611, 1794715470104618, 1794715470104835, 1794715470104842, 1794715470104866, 1794715470104872, 1794715471153163, 1794715471153187, 1794715471153194, 1794715471153411, 1794715471153442, 1794715472168967, 1794715472168974, 1794715472168998, 1794715472169004, 1794715472169222, 1794715472169252, 1794722985379859, 1794722985379875, 1794722985379890, 1794722985380099, 1794722985380114, 1794722985380130, 1794722985380144, 1794722985871367, 1794722985871382, 1794722985871398, 1794722985871412, 1794722985871622, 1794722985871636, 1794722985871652, 1794722985871664, 1794722987444231, 1794722987444246, 1794722987444262, 1794722987444276, 1794722987444486, 1794722987444516, 1794722987902990, 1794722987903004, 1794722987903020, 1794722987903032, 1794722987903244, 1794722987903272, 1794731575314451, 1794731575314467, 1794731575314482, 1794731575314691, 1794731575314706, 1794731576330247, 1794731576330262, 1794731576330278, 1794731576330292, 1794731576330502, 1794731576330516, 1794738017994759, 1794738017994790, 1794738017995014, 1794738017995044, 1794738018453518, 1794738018453548, 1794738018453772, 1794738018453800, 1794749845569579, 1794749845569675, 1794749845569699, 1794749845569706, 1794749845569803, 1794749845569827, 1794749845569834, 1794749845569923, 1794749845569930, 1794749845569954, 1794749845569960, 2040992116183047, 2040998557847559, 2041043671519239, 2041043671519366, 2041043671519494, 2041043671519620, 2041058704101390, 2041058704101516, 2111418858344462, 2111418858344716].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_2 : layer 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 [] = fr13_2 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_0 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_1 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_2 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_3 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_4 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_5 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_6 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_7 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 7 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_8 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 8 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_9 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 9 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_10 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 10 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_11 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 11 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_12 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 12 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_13 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 13 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_14 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 14 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_15 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 15 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_16 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 16 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_17 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 17 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_18 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 18 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_19 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 19 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_20 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 20 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_21 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 21 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_22 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 22 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_23 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 23 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_24 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 24 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_25 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 25 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_26 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 26 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_27 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 27 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_28 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 28 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_29 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 29 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_30 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 30 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_31 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 31 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_32 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 32 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_33 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 33 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_34 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 34 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_35 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 35 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_2_36 : piece 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 4 9 37 36 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_2]
  decide +kernel

private lemma run13_2 : visit 13 [4,4,4,4,4,3,3,3,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [4,4,4,4,4,3,3,3,3,3,3,3,3] (bucket:=37) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_2_0
  · exact pc13_2_1
  · exact pc13_2_2
  · exact pc13_2_3
  · exact pc13_2_4
  · exact pc13_2_5
  · exact pc13_2_6
  · exact pc13_2_7
  · exact pc13_2_8
  · exact pc13_2_9
  · exact pc13_2_10
  · exact pc13_2_11
  · exact pc13_2_12
  · exact pc13_2_13
  · exact pc13_2_14
  · exact pc13_2_15
  · exact pc13_2_16
  · exact pc13_2_17
  · exact pc13_2_18
  · exact pc13_2_19
  · exact pc13_2_20
  · exact pc13_2_21
  · exact pc13_2_22
  · exact pc13_2_23
  · exact pc13_2_24
  · exact pc13_2_25
  · exact pc13_2_26
  · exact pc13_2_27
  · exact pc13_2_28
  · exact pc13_2_29
  · exact pc13_2_30
  · exact pc13_2_31
  · exact pc13_2_32
  · exact pc13_2_33
  · exact pc13_2_34
  · exact pc13_2_35
  · exact pc13_2_36
private def fr13_3 : List (List Nat) :=
  [1156961586676882, 1156961586676884, 1156961586676898, 1156961586676930, 1156961586676932, 1156961586676944, 1156961586676960, 1156961586677010, 1156961587463266, 1156961587463268, 1156961587463458, 1156961587463490, 1156961587463520, 1156961587692628, 1156961587692644, 1156961587692820, 1156961587692868, 1156961587692880, 1156961587954980, 1156963664831499, 1156963666797587, 1156963666797699, 1156963666797713, 1156963666797714, 1156963666797716, 1156963666797729, 1156963666797761, 1156963666797762, 1156963666797764, 1156963666797776, 1156963666797792, 1156963666895885, 1156963666896005, 1156963666896009, 1156963666896012, 1156963666896020, 1156963666896033, 1156963666896065, 1156963666896068, 1156963666896072, 1156963666896080, 1156963666896096, 1156963666896140, 1156963666920459, 1156963666920461, 1156963666920467, 1156963666920579, 1156963666920581, 1156963666920585, 1156963666920586, 1156963666920588, 1156963666920593, 1156963666920594, 1156963666920609, 1156963666920641, 1156963666920642, 1156963666920644, 1156963666920648, 1156963666920656, 1156963666920672, 1156963666920707, 1156963666920713, 1156963666920714, 1156963667026965, 1156963667027077, 1156963667027089, 1156963667027092, 1156963667027137, 1156963667027140, 1156963667027152, 1156963667027168, 1156963667027220, 1156963667813397, 1156963667813445, 1156963667813457, 1156963667813460, 1156963667813473, 1156963667813652, 1156963667813700, 1156963667813712, 1156963667813728, 1156963667837971, 1156963667837973, 1156963667838019, 1156963667838021, 1156963667838033, 1156963667838034, 1156963667838036, 1156963667838049, 1156963667838211, 1156963667838225, 1156963667838226, 1156963667838241, 1156963667838273, 1156963667838274, 1156963667838288, 1156963667838304, 1156963667936269, 1156963667936277, 1156963667936325, 1156963667936329, 1156963667936332, 1156963667936337, 1156963667936340, 1156963667936353, 1156963667936517, 1156963667936521, 1156963667936524, 1156963667936545, 1156963667936577, 1156963667936580, 1156963667936584, 1156963667936608, 1156963668067349, 1156963668067397, 1156963668067409, 1156963668067412, 1156963668067425, 1156963668067589, 1156963668067601, 1156963668067604, 1156963668067649, 1156963668067652, 1156963668067664, 1156963668329493, 1156963668329733, 1156963668329745, 1156963668329748, 1156963668329761, 1715516003737994, 1715516003738008, 1715516003738018, 1715516003738050, 1715516003738056, 1715516003738064, 1715516003738080, 1715548216125706, 1715548216125826, 1715548216125832, 1715548216125888, 1715548217960586, 1715548217960642, 1715548217960648, 1715548217960840, 1715548217960896, 1715548218214411, 1715548218214531, 1715548218214537, 1715548218214538, 1715548218214593, 1715548218214594, 1715548218214600, 1715548218214665, 1715548218214785, 1715548218214792, 1715548218214848, 1715548219000843, 1715548219000899, 1715548219000905, 1715548219000906, 1715548219001097, 1715548219001153, 1715548219001160, 1715548219246603, 1715548219246659, 1715548219246666, 1715548219246851, 1715548219246858, 1715548219246914, 1715548219246920, 1715548219508747, 1715548219508995, 1715548219509002, 1715550094944524, 1715550094944644, 1715550094944648, 1715550094944704, 1715550095067149, 1715550095067397, 1715550095067401, 1715550095067404, 1715550095067521, 1715550095067524, 1715550095067528, 1715550095067584, 1715550097033229, 1715550097033349, 1715550097033353, 1715550097033356, 1715550097033409, 1715550097033412, 1715550097033416, 1715550097033481, 1715550097033601, 1715550097033608, 1715550097033664, 1715550097147911, 1715550097147915, 1715550097147918, 1715550097148035, 1715550097148038, 1715550097148042, 1715550097148044, 1715550097148098, 1715550097148100, 1715550097148104, 1715550097148163, 1715550097148170, 1715550097148290, 1715550097148296, 1715550097148352, 1715550098065415, 1715550098065419, 1715550098065422, 1715550098065475, 1715550098065478, 1715550098065482, 1715550098065484, 1715550098065667, 1715550098065674, 1715550098065730, 1715550098065736, 1715550098163719, 1715550098163726, 1715550098163782, 1715550098163788, 1715550098163974, 1715550098163980, 1715550098164036, 1715550098164040, 1715550098556935, 1715550098556942, 1715550098557190, 1715550098557196, 1715565127329932, 1715565127329988, 1715565127329992, 1715565127330180, 1715565127330240, 1715565127583757, 1715565127583877, 1715565127583881, 1715565127583884, 1715565127583937, 1715565127583940, 1715565127583944, 1715565127584005, 1715565127584129, 1715565127584132, 1715565127584192, 1715565128370189, 1715565128370245, 1715565128370249, 1715565128370252, 1715565128370313, 1715565128370369, 1715565128370376, 1715565128370437, 1715565128370497, 1715565128370500, 1715565128370561, 1715565128370624, 1715565128615943, 1715565128615947, 1715565128615950, 1715565128616003, 1715565128616006, 1715565128616010, 1715565128616012, 1715565128616067, 1715565128616074, 1715565128616130, 1715565128616136, 1715565128616195, 1715565128616198, 1715565128616258, 1715565128616260, 1715565128616322, 1715565128616384, 1715565128878087, 1715565128878091, 1715565128878094, 1715565128878211, 1715565128878218, 1715565128878339, 1715565128878342, 1715565128878466, 1715565129107463, 1715565129107470, 1715565129107590, 1715565129107596, 1715565129107718, 1715565129107844, 1715566738000009, 1715566738000065, 1715566738000072, 1715566738000137, 1715566738000257, 1715566738000264, 1715566738000320, 1715566738114571, 1715566738114691, 1715566738114698, 1715566738114754, 1715566738114760, 1715566738114819, 1715566738114826, 1715566738114946, 1715566738114952, 1715566738115008, 1715566739032075, 1715566739032131, 1715566739032138, 1715566739032195, 1715566739032258, 1715566739032323, 1715566739032330, 1715566739032386, 1715566739032392, 1715566739032450, 1715566739032512, 1715566739130375, 1715566739130382, 1715566739130438, 1715566739130444, 1715566739130502, 1715566739130564, 1715566739130630, 1715566739130636, 1715566739130692, 1715566739130696, 1715566739130756, 1715566739130816, 1715566739523591, 1715566739523598, 1715566739523718, 1715566739523846, 1715566739523852, 1715566739523972, 1715566739589134, 1715566739589260, 1715566739589388, 1715566739589512, 1715573180450889, 1715573180451081, 1715573180451137, 1715573180451144, 1715573180696587, 1715573180696643, 1715573180696650, 1715573180696835, 1715573180696842, 1715573180696898, 1715573180696904, 1715573180958731, 1715573180958787, 1715573180958979, 1715573180958986, 1715573180959042, 1715573181188103, 1715573181188110, 1715573181188166, 1715573181188358, 1715573181188364, 1715573181188420, 1715582592377130, 1715582592377226, 1715582592377250, 1715582592377256, 1715582592377282, 1715582592377288, 1715582592377312, 1988210726064225, 1988210726309955, 1988210726572067, 1988210726801415, 1988212336726083, 1988212337217543, 1988218778652707, 1988218778882055, 1988219852492807, 1988221999714311, 1988262281400609, 1988262281400705, 1988262281400736, 1988262281400768, 1988278924447779, 1988278924447875, 1988278924447906, 1988278924447938, 1988278924447968, 1988278925463559, 1988278925463590, 1988278925463622, 1988278925463652, 1988278925922318, 1988278925922348, 1988286440738823, 1988286440738854, 1988286440738886, 1988286440738916, 1988286441197582, 1988286441197612, 2111409194373251, 2111409194373314, 2111409194373379, 2111409194373506, 2111409194373568, 2111416710664199, 2111416710664262, 2111416710664454, 2111416710664516, 2111416711122958, 2111416711123212, 2111418858344462, 2111418858344716].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_3 : layer 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 [] = fr13_3 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_0 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_1 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_2 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_3 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_4 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_5 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_6 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_7 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 7 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_8 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 8 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_9 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 9 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_10 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 10 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_11 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 11 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_12 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 12 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_13 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 13 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_14 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 14 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_15 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 15 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_16 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 16 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_17 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 17 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_18 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 18 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_19 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 19 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_20 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 20 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_21 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 21 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_22 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 22 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_23 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 23 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_24 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 24 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_25 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 25 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_26 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 26 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_27 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 27 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_28 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 28 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_29 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 29 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_30 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 30 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_31 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 31 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_32 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 32 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_33 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 33 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_34 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 34 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_35 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 35 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_3_36 : piece 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 4 9 37 36 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_3]
  decide +kernel

private lemma run13_3 : visit 13 [4,4,4,4,4,4,4,3,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [4,4,4,4,4,4,4,3,3,3,3,3,3] (bucket:=37) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_3_0
  · exact pc13_3_1
  · exact pc13_3_2
  · exact pc13_3_3
  · exact pc13_3_4
  · exact pc13_3_5
  · exact pc13_3_6
  · exact pc13_3_7
  · exact pc13_3_8
  · exact pc13_3_9
  · exact pc13_3_10
  · exact pc13_3_11
  · exact pc13_3_12
  · exact pc13_3_13
  · exact pc13_3_14
  · exact pc13_3_15
  · exact pc13_3_16
  · exact pc13_3_17
  · exact pc13_3_18
  · exact pc13_3_19
  · exact pc13_3_20
  · exact pc13_3_21
  · exact pc13_3_22
  · exact pc13_3_23
  · exact pc13_3_24
  · exact pc13_3_25
  · exact pc13_3_26
  · exact pc13_3_27
  · exact pc13_3_28
  · exact pc13_3_29
  · exact pc13_3_30
  · exact pc13_3_31
  · exact pc13_3_32
  · exact pc13_3_33
  · exact pc13_3_34
  · exact pc13_3_35
  · exact pc13_3_36
private def fr13_4 : List (List Nat) :=
  [1695756405770338, 1695756405770352, 1695756405770562, 1695756405770592, 1695756406229042, 1695756406229282, 1695756406229296, 1695756874459267, 1695756874459329, 1695756874459330, 1695756874459360, 1695756874459522, 1695756874459584, 1695756875475011, 1695756875475041, 1695756875475042, 1695756875475056, 1695756875475266, 1695756875475296, 1695756875499587, 1695756875499617, 1695756875499618, 1695756875499632, 1695756875499779, 1695756875499841, 1695756875499842, 1695756875499872, 1695756875991075, 1695756875991089, 1695756875991090, 1695756875991299, 1695756875991329, 1695756875991330, 1695756875991344, 1695773516441667, 1695773516441697, 1695773516441698, 1695773516441712, 1695773516441794, 1695773516441824, 1695773516441921, 1695773516441952, 1695773516442048, 1695773516900387, 1695773516900401, 1695773516900402, 1695773516900514, 1695773516900528, 1695773516900641, 1695773516900656, 1695773516900768, 1695773516957731, 1695773516957745, 1695773516957746, 1695773516957827, 1695773516957857, 1695773516957858, 1695773516957872, 1695773516957985, 1695773516958000, 1695773516958081, 1695773516958112, 1695773517154323, 1695773517154435, 1695773517154449, 1695773517154450, 1695773517154577, 1695773517154689, 1695773517154704, 1695773918030018, 1695773918030048, 1695773918030210, 1695773918030272, 1695773919045730, 1695773919045744, 1695773919045856, 1695773919045954, 1695773919045984, 1695773919046080, 1695773919070275, 1695773919070305, 1695773919070306, 1695773919070320, 1695773919070401, 1695773919070432, 1695773919070467, 1695773919070529, 1695773919070530, 1695773919070560, 1695773919070593, 1695773919070656, 1695773919561763, 1695773919561777, 1695773919561778, 1695773919561889, 1695773919561904, 1695773919561987, 1695773919562017, 1695773919562018, 1695773919562032, 1695773919562113, 1695773919562144, 1695773919578147, 1695773919578162, 1695773919578243, 1695773919578274, 1695773919578288, 1695773919578371, 1695773919578402, 1695773919578416, 1695773919578498, 1695773919578528, 1695773919807507, 1695773919807619, 1695773919807634, 1695773919807747, 1695773919807762, 1695773919807874, 1695773919807888, 1695781971126370, 1695781971126384, 1695781971126594, 1695781971126624, 1695781971585074, 1695781971585136, 1695781971585314, 1695781971585328, 1695781971585376, 1695781971642403, 1695781971642417, 1695781971642418, 1695781971642465, 1695781971642480, 1695781971642627, 1695781971642657, 1695781971642658, 1695781971642672, 1695781971642689, 1695781971642720, 1695781971838995, 1695781971839057, 1695781971839235, 1695781971839249, 1695781971839250, 1695781971839297, 1695781971839312, 1695781971888147, 1695781971888195, 1695781971888210, 1695781971888387, 1695781971888402, 1695781971888450, 1695781971888464, 1695781971953731, 1695781971953923, 1695781971953986, 1975015378595952, 1975015379054648, 1975015379111985, 1975015379308569, 1975015781199984, 1975015781716017, 1975015781961747, 1975023833739320, 1975023833796657, 1975023833993241, 1975023834042387, 1975023834107915, 1975024102199345, 1975024102445075, 1975024102543367, 1975027860033561, 1975027860082707, 1975027860148235, 1975027860180999, 1975083979534536, 1975083979534560, 1975083980574793, 1975083980574817, 1975083980574824, 1975083980574832, 1975083981082635, 1975083981082659, 1975083981082666, 1975083981082674, 1975083981082680, 1975092301058121, 1975092301058145, 1975092301058152, 1975092301058160, 1975092301565963, 1975092301565987, 1975092301565994, 1975092301566002, 1975092301566008, 1975092301795335, 1975092301795342, 1975092301795350, 1975092301795356, 2111406778380512, 2111406778380736, 2111415099904097, 2111415099904112, 2111415099904321, 2111415099904352, 2111415100411939, 2111415100411954, 2111415100412163, 2111415100412194, 2111415100412208, 2111415100641287, 2111415100641302, 2111415100641542, 2111415100641556, 2111418858049571, 2111418858049586, 2111418858049795, 2111418858049826, 2111418858049840, 2111418858278919, 2111418858278934, 2111418858279174, 2111418858279188, 2111418858344462, 2111418858344716].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_4 : layer 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 [] = fr13_4 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_0 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_1 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_2 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_3 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_4 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_5 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_6 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_7 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 7 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_8 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 8 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_9 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 9 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_10 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 10 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_11 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 11 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_12 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 12 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_13 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 13 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_14 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 14 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_15 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 15 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_4_16 : piece 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 4 9 17 16 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_4]
  decide +kernel

private lemma run13_4 : visit 13 [4,4,4,4,4,4,4,4,4,3,3,3,3] 13 [] = true := by
  apply accept_pieces [4,4,4,4,4,4,4,4,4,3,3,3,3] (bucket:=17) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_4_0
  · exact pc13_4_1
  · exact pc13_4_2
  · exact pc13_4_3
  · exact pc13_4_4
  · exact pc13_4_5
  · exact pc13_4_6
  · exact pc13_4_7
  · exact pc13_4_8
  · exact pc13_4_9
  · exact pc13_4_10
  · exact pc13_4_11
  · exact pc13_4_12
  · exact pc13_4_13
  · exact pc13_4_14
  · exact pc13_4_15
  · exact pc13_4_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_5 : visit 13 [4,4,4,4,4,4,4,4,4,4,4,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_6 : visit 13 [4,4,4,4,4,4,4,4,4,4,4,4,4] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
private def fr13_7 : List (List Nat) :=
  [1090719595122705, 1090719599055873, 1090719599301634, 1090719599301648, 1090788062695427, 1090788062695458, 1090788062695682, 1090788062695712, 1090788062924806, 1090788062924820, 1090788062925060, 1090788062925072, 1090788066857988, 2181713497264131, 2181713501426692, 2181781159809036, 2181781159809288].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_7 : layer 13 [5,4,3,3,3,3,3,3,3,3,3,3,3] 4 [] = fr13_7 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_7_0 : piece 13 [5,4,3,3,3,3,3,3,3,3,3,3,3] 4 9 7 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_7]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_7_1 : piece 13 [5,4,3,3,3,3,3,3,3,3,3,3,3] 4 9 7 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_7]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_7_2 : piece 13 [5,4,3,3,3,3,3,3,3,3,3,3,3] 4 9 7 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_7]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_7_3 : piece 13 [5,4,3,3,3,3,3,3,3,3,3,3,3] 4 9 7 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_7]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_7_4 : piece 13 [5,4,3,3,3,3,3,3,3,3,3,3,3] 4 9 7 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_7]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_7_5 : piece 13 [5,4,3,3,3,3,3,3,3,3,3,3,3] 4 9 7 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_7]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_7_6 : piece 13 [5,4,3,3,3,3,3,3,3,3,3,3,3] 4 9 7 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_7]
  decide +kernel

private lemma run13_7 : visit 13 [5,4,3,3,3,3,3,3,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [5,4,3,3,3,3,3,3,3,3,3,3,3] (bucket:=7) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_7_0
  · exact pc13_7_1
  · exact pc13_7_2
  · exact pc13_7_3
  · exact pc13_7_4
  · exact pc13_7_5
  · exact pc13_7_6
private def fr13_8 : List (List Nat) :=
  [272765606248519, 272782787168389, 272799697520713, 272799697569859, 272799698569353, 272799701699587, 272799701699650, 1390059460781202, 1390059460903947, 1390059460904067, 1390059460904073, 1390059460904074, 1390059460904081, 1390059460904201, 1390076367126605, 1390076370273293, 1390076371190805, 1390076371190853, 1390076371190865, 1390076371190868, 1390076371305479, 1390076371305483, 1390076371305486, 1390076371305491, 1390076371305539, 1390076371305542, 1390076371305546, 1390076371305548, 1390076371305554, 1390076371305603, 1390076371305610, 1390076372239381, 1390076372239493, 1390076372239505, 1390076372239508, 1390127922462989, 1390127926527237, 1390127926641671, 1390127926641923, 1390127926641926, 1390144565395609, 1390144565510283, 1390144565510291, 1390144565510411, 1390144569574411, 1390144569574531, 1390144569574538, 1390144569672711, 1390144569672718, 1390144569672838, 1390144569672844, 1390161749445635, 1390177855671302, 1935435777556649, 1935435778588715, 1935435778588747, 1935435778588771, 1935435778588778, 1935435778588835, 1935435778588939, 1935452957427753, 1935452959508491, 1935452959508515, 1935452959508522, 1935469063669779, 1935469063669795, 1935469063669810, 1935469064685575, 1935469064685590, 1935469064685606, 1935469064685620, 1935487333924907, 1935487333925131, 1935487333925155, 1935487333925162, 1935520620021767, 1935520620021798, 2181729604538375, 2181781159874567, 2181781159874822].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_8 : layer 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 [] = fr13_8 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_0 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_1 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_2 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_3 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_4 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_5 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_6 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_7 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 7 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_8 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 8 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_9 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 9 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_10 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 10 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_11 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 11 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_12 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 12 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_13 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 13 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_14 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 14 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_15 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 15 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_8_16 : piece 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 4 9 17 16 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_8]
  decide +kernel

private lemma run13_8 : visit 13 [5,4,4,4,3,3,3,3,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [5,4,4,4,3,3,3,3,3,3,3,3,3] (bucket:=17) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_8_0
  · exact pc13_8_1
  · exact pc13_8_2
  · exact pc13_8_3
  · exact pc13_8_4
  · exact pc13_8_5
  · exact pc13_8_6
  · exact pc13_8_7
  · exact pc13_8_8
  · exact pc13_8_9
  · exact pc13_8_10
  · exact pc13_8_11
  · exact pc13_8_12
  · exact pc13_8_13
  · exact pc13_8_14
  · exact pc13_8_15
  · exact pc13_8_16
private def fr13_9 : List (List Nat) :=
  [68273020881057, 68277248469138, 68277248477329, 68277248477377, 68277248731298, 68277249509395, 68277249771555, 68290136771617, 68294296226833, 68294297013281, 68294297259011, 68294297259026, 68298591456289, 1192145959027874, 1192145959027876, 1192145959027906, 1192145959028002, 1192145959552322, 1192145960043812, 1192150184535059, 1192150186370083, 1192150186370179, 1192150186370209, 1192150186370210, 1192150186370212, 1192150186370241, 1192150186599445, 1192150186599557, 1192150186599569, 1192150186599572, 1192150186599588, 1192150186599617, 1192150186599700, 1192150186624019, 1192150186624021, 1192150186624035, 1192150186624131, 1192150186624133, 1192150186624145, 1192150186624146, 1192150186624148, 1192150186624161, 1192150186624162, 1192150186624193, 1192150186624259, 1192150186624273, 1192150186624274, 1192150186861605, 1192150186861701, 1192150186861729, 1192150186861732, 1192150186861860, 1192150187385893, 1192150187386148, 1192150187410467, 1192150187410469, 1192150187410691, 1192150187410721, 1192150187410722, 1192150187410753, 1192150187639829, 1192150187639845, 1192150187640069, 1192150187640081, 1192150187640084, 1192150187640129, 1192150187901989, 1192150187902213, 1192150187902241, 1192150187902244, 1192214625559873, 1192214625559937, 1192214625560000, 1192214627624129, 1192214627624384, 1192214627648705, 1192214627648833, 1192214627648897, 1192214627648960, 1192214628664641, 1192218782130594, 1192218782130596, 1192218782130626, 1192218786293026, 1192218786293122, 1192218786293152, 1192218786317347, 1192218786317571, 1192218786317601, 1192218786317602, 1192218786317697, 1192218786317698, 1192218786317728, 1192218788381731, 1192218788381827, 1192218788381857, 1192218788381858, 1192218788381985, 1192218788382081, 1192218788382112, 1192218788398115, 1192218788398211, 1192218788398242, 1192218788398339, 1192218788398370, 1192218788398466, 1192218788398496, 1192218789413923, 1192218789414147, 1192218789414178, 1192248853154945, 1192248854187011, 1192252879703043, 1192252879703170, 1192252880718854, 1192265763556355, 1750702523441434, 1750702523441546, 1750702523441554, 1750702523441560, 1750702523441576, 1750702523441602, 1750732588476682, 1750732588476802, 1750732588476808, 1750732590049418, 1750732590049672, 1750732590565387, 1750732590565507, 1750732590565513, 1750732590565514, 1750732590565641, 1750732590565761, 1750732590565768, 1750732591089675, 1750732591089929, 1750732591597579, 1750732591597827, 1750732591597834, 1750736614517004, 1750736614517124, 1750736614517128, 1750736614770701, 1750736614770949, 1750736614770953, 1750736614770956, 1750736614771073, 1750736614771076, 1750736614771080, 1750736616605709, 1750736616605829, 1750736616605833, 1750736616605836, 1750736616605961, 1750736616606081, 1750736616606088, 1750736616851463, 1750736616851467, 1750736616851470, 1750736616851587, 1750736616851590, 1750736616851594, 1750736616851596, 1750736616851715, 1750736616851722, 1750736616851842, 1750736616851848, 1750736617637895, 1750736617637899, 1750736617637902, 1750736617638147, 1750736617638154, 1750736617867271, 1750736617867278, 1750736617867526, 1750736617867532, 1750749499418764, 1750749499419012, 1750749499934733, 1750749499934853, 1750749499934857, 1750749499934860, 1750749499934981, 1750749499935105, 1750749499935108, 1750749500459021, 1750749500459145, 1750749500459269, 1750749500459393, 1750749500966919, 1750749500966923, 1750749500966926, 1750749500967043, 1750749500967050, 1750749500967171, 1750749500967174, 1750749500967298, 1750753257572489, 1750753257572617, 1750753257572737, 1750753257572744, 1750753257818123, 1750753257818243, 1750753257818250, 1750753257818371, 1750753257818378, 1750753257818498, 1750753257818504, 1750753258604555, 1750753258604675, 1750753258604803, 1750753258604810, 1750753258604930, 1750753258833927, 1750753258833934, 1750753258834054, 1750753258834182, 1750753258834188, 1750753258834308, 1750757552539913, 1750757553047563, 1750757553047811, 1750757553047818, 1750766964465994, 1750766964466058, 1750766964466114, 1750766964466120, 1750801055795465, 1750801055795585, 1750801055795592, 1750801057875979, 1750801057876099, 1750801057876106, 1750801058891783, 1750801058891790, 1750817698842755, 1750817698842883, 1750817698843010, 1750817699858439, 1750817699858694, 2023395098660899, 2023398856298531, 2023398856527879, 2023403150741539, 2023406371803143, 2023446653489473, 2023446653489537, 2023446653489600, 2023463296536643, 2023463296536707, 2023463296536770, 2023463297552391, 2023463297552454, 2023470812827655, 2023470812827718, 2146593566462019, 2146593566462083, 2146593566462146, 2146593566462211, 2146593566462338, 2146601082753031, 2146601082753094, 2146601082753286, 2181781159874567, 2181781159874822].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_9 : layer 13 [5,4,4,4,4,4,3,3,3,3,3,3,3] 4 [] = fr13_9 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_9_0 : piece 13 [5,4,4,4,4,4,3,3,3,3,3,3,3] 4 9 7 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_9]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_9_1 : piece 13 [5,4,4,4,4,4,3,3,3,3,3,3,3] 4 9 7 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_9]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_9_2 : piece 13 [5,4,4,4,4,4,3,3,3,3,3,3,3] 4 9 7 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_9]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_9_3 : piece 13 [5,4,4,4,4,4,3,3,3,3,3,3,3] 4 9 7 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_9]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_9_4 : piece 13 [5,4,4,4,4,4,3,3,3,3,3,3,3] 4 9 7 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_9]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_9_5 : piece 13 [5,4,4,4,4,4,3,3,3,3,3,3,3] 4 9 7 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_9]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_9_6 : piece 13 [5,4,4,4,4,4,3,3,3,3,3,3,3] 4 9 7 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_9]
  decide +kernel

private lemma run13_9 : visit 13 [5,4,4,4,4,4,3,3,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [5,4,4,4,4,4,3,3,3,3,3,3,3] (bucket:=7) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_9_0
  · exact pc13_9_1
  · exact pc13_9_2
  · exact pc13_9_3
  · exact pc13_9_4
  · exact pc13_9_5
  · exact pc13_9_6
private def fr13_10 : List (List Nat) :=
  [17163785145412, 17163785145440, 17163785604136, 17171300879400, 1142737342571720, 1142737342571744, 1142737342571912, 1142737342571968, 1142737343612008, 1142737343612232, 1142737343612256, 1142770629610592, 1142771635203264, 1142771636243521, 1142771636243552, 1142787740281952, 1142787740797985, 1704552498858082, 1704552498858306, 1704552498858336, 1704552499251490, 1704553504385155, 1704553504385217, 1704553504385218, 1704553504385248, 1704553504385410, 1704553504385472, 1704553505368131, 1704553505368161, 1704553505368162, 1704553505368386, 1704553505368416, 1704553505425475, 1704553505425505, 1704553505425506, 1704553505425667, 1704553505425729, 1704553505425730, 1704553505425760, 1704553505884195, 1704553505884419, 1704553505884449, 1704553505884450, 1704569609529411, 1704569609529441, 1704569609529442, 1704569609529538, 1704569609529568, 1704569609529665, 1704569609529696, 1704569609529792, 1704569609922595, 1704569609922722, 1704569609922849, 1704569609922976, 1704569610045475, 1704569610045571, 1704569610045601, 1704569610045602, 1704569610045729, 1704569610045825, 1704569610045856, 1704569610176643, 1704569610176897, 1704570547955906, 1704570547955936, 1704570547956098, 1704570547956160, 1704570548938850, 1704570548938976, 1704570548939074, 1704570548939104, 1704570548939200, 1704570548996163, 1704570548996193, 1704570548996194, 1704570548996289, 1704570548996320, 1704570548996355, 1704570548996417, 1704570548996418, 1704570548996448, 1704570548996481, 1704570548996544, 1704570549454883, 1704570549455009, 1704570549455107, 1704570549455137, 1704570549455138, 1704570549455233, 1704570549455264, 1704570549504035, 1704570549504131, 1704570549504162, 1704570549504259, 1704570549504290, 1704570549504386, 1704570549504416, 1704570549700739, 1704570549700867, 1704570549700994, 1704578064214114, 1704578064214338, 1704578064214368, 1704578064607522, 1704578064607584, 1704578064730147, 1704578064730209, 1704578064730371, 1704578064730401, 1704578064730402, 1704578064730433, 1704578064730464, 1704578064861443, 1704578064861505, 1704578064975939, 1704578064976131, 1704578064976194, 1704621166831810, 1704621166831840, 1704621167872067, 1704621167872097, 1704621167872098, 1704638210402528, 1704638210402752, 1704638211442785, 1704638211443009, 1704638211443040, 1704638211950627, 1704638211950851, 1704638211950882, 1983811471683688, 1983811472199721, 1983812411093096, 1983812411150433, 1983812411609129, 1983812411658275, 1983812411854859, 1983819926884393, 1983819927130123, 1983820732092457, 1983820732141603, 1983820732338187, 1983820732370951, 1983823953170443, 1983880072556752, 1983880072556768, 1983880073597009, 1983880073597025, 1983880073597040, 1983880074104851, 1983880074104867, 1983880074104882, 1983888394080337, 1983888394080353, 1983888394080368, 1983888394588179, 1983888394588195, 1983888394588210, 1983888394817543, 1983888394817558, 2120202871402704, 2120202871402720, 2120202871402944, 2120211192926289, 2120211192926305, 2120211192926320, 2120211192926529, 2120211192926560, 2120211193434131, 2120211193434147, 2120211193434162, 2120211193434371, 2120211193434402, 2120211193663495, 2120211193663510, 2120211193663750, 2120214951071763, 2120214951071779, 2120214951071794, 2120214951072003, 2120214951072034, 2120214951301127, 2120214951301142, 2120214951301382, 2181776327888993, 2181776327889217, 2181776327889248, 2181780086034467, 2181780086034691, 2181780086034722, 2181780086263815, 2181780086264070, 2181781159874567, 2181781159874822].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_10 : layer 13 [5,4,4,4,4,4,4,4,3,3,3,3,3] 4 [] = fr13_10 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_10_0 : piece 13 [5,4,4,4,4,4,4,4,3,3,3,3,3] 4 9 7 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_10]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_10_1 : piece 13 [5,4,4,4,4,4,4,4,3,3,3,3,3] 4 9 7 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_10]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_10_2 : piece 13 [5,4,4,4,4,4,4,4,3,3,3,3,3] 4 9 7 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_10]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_10_3 : piece 13 [5,4,4,4,4,4,4,4,3,3,3,3,3] 4 9 7 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_10]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_10_4 : piece 13 [5,4,4,4,4,4,4,4,3,3,3,3,3] 4 9 7 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_10]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_10_5 : piece 13 [5,4,4,4,4,4,4,4,3,3,3,3,3] 4 9 7 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_10]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_10_6 : piece 13 [5,4,4,4,4,4,4,4,3,3,3,3,3] 4 9 7 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_10]
  decide +kernel

private lemma run13_10 : visit 13 [5,4,4,4,4,4,4,4,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [5,4,4,4,4,4,4,4,3,3,3,3,3] (bucket:=7) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_10_0
  · exact pc13_10_1
  · exact pc13_10_2
  · exact pc13_10_3
  · exact pc13_10_4
  · exact pc13_10_5
  · exact pc13_10_6
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_11 : visit 13 [5,4,4,4,4,4,4,4,4,4,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_12 : visit 13 [5,5,4,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
private def fr13_13 : List (List Nat) :=
  [694926751893828, 694926756023560, 694935272106021, 694935272106245, 694935272106273, 694935272106276, 694935272106280, 694935272106308, 694935272106369, 694935273678917, 694935273679172, 694935274137641, 694935274137896, 694935274194981, 694935274194985, 694935274195013, 694935274195205, 694935274195233, 694935274195236, 694935274195329, 694935274661961, 694935274662216, 694935276235785, 694935276236033, 694935276236040, 694935277808649, 694935277808904, 694935278324745, 694935278324993, 694935278325000, 694943862564933, 694943862565185, 694943866694665, 694943866694913, 694952317249606, 694952317249858, 694952317708330, 694952317708578, 694952317765639, 694952317765667, 694952317765669, 694952317765670, 694952317765673, 694952317765701, 694952317765763, 694952317765891, 694952317765921, 694952317765922, 694952317765953, 694952318232650, 694952318232898, 694952321379338, 694952321379586, 694952321895427, 694952321895433, 694952321895434, 694952321895681, 694952321895682, 967580871954473, 967580875625481, 967597915525161, 967597917491249, 967597919196169, 967597921162257, 967641015660936, 967641016578384, 967641016701001, 967641016701193, 967641016701249, 967641016701256, 967641017749641, 967641018667089, 967641019847937, 967658061320329, 967658061320577, 967658062237777, 967658062238017, 967658062352395, 967658062352451, 967658062352458, 967658062352643, 967658062352706, 967658063286417, 967658064318483, 967658064318531, 967658064318546, 967658065499139, 967658067465219, 1090728189252625, 1090788331376785, 1090788331376913, 1090788332163169, 1090788332163361, 1090788332408851, 1090788332408899, 1090788332408914, 1090788332409091, 1090788332409106, 1090788335555587, 1258117194122564, 1258125714334757, 1258125715907653, 1258125716366377, 1258125716366632, 1258125716423717, 1258125716423721, 1258125716423749, 1258125716423941, 1258125716423969, 1258125716423972, 1258125716890697, 1258125716890952, 1812272092554513, 1812272094643473, 1812280543568178, 1812280547239186, 1812280547755027, 1812280547755267, 1812280547755281, 1812280547755282, 1812280549327891, 1812280549328145, 1812280549835795, 1812280549836035, 1812280549836050, 1812306313898258, 1812306315986963, 1812306315987217, 1812314634381588, 1812314634897429, 1812314634897669, 1812314634897681, 1812314634897684, 1812314636470293, 1812314636470545, 1812314636978183, 1812314636978195, 1812314636978198, 1812314636978435, 1812314636978450, 1812323225356309, 1812323225356549, 1812331277436953, 1812331277437193, 1812331277944843, 1812331277944851, 1812331277944858, 1812331277945091, 1812331277945098, 1812340689363346, 1812340693550339, 1812340695631107, 2076165219062787, 2076181860029443, 2076225359106433, 2076225361186947, 2076242002153603, 2181722091394051, 2181782233518211, 2181782233518339].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_13 : layer 13 [5,5,4,4,4,3,3,3,3,3,3,3,3] 4 [] = fr13_13 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_13_0 : piece 13 [5,5,4,4,4,3,3,3,3,3,3,3,3] 4 9 7 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_13]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_13_1 : piece 13 [5,5,4,4,4,3,3,3,3,3,3,3,3] 4 9 7 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_13]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_13_2 : piece 13 [5,5,4,4,4,3,3,3,3,3,3,3,3] 4 9 7 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_13]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_13_3 : piece 13 [5,5,4,4,4,3,3,3,3,3,3,3,3] 4 9 7 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_13]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_13_4 : piece 13 [5,5,4,4,4,3,3,3,3,3,3,3,3] 4 9 7 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_13]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_13_5 : piece 13 [5,5,4,4,4,3,3,3,3,3,3,3,3] 4 9 7 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_13]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_13_6 : piece 13 [5,5,4,4,4,3,3,3,3,3,3,3,3] 4 9 7 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_13]
  decide +kernel

private lemma run13_13 : visit 13 [5,5,4,4,4,3,3,3,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [5,5,4,4,4,3,3,3,3,3,3,3,3] (bucket:=7) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_13_0
  · exact pc13_13_1
  · exact pc13_13_2
  · exact pc13_13_3
  · exact pc13_13_4
  · exact pc13_13_5
  · exact pc13_13_6
private def fr13_14 : List (List Nat) :=
  [595989225424969, 595989225424970, 595989225424977, 595989225425033, 595989225425089, 595989225425096, 595989225425120, 595989225425224, 595989225425232, 595989225425288, 595989225425344, 595989225818257, 595989225818512, 595989225932938, 595989225933192, 595989226064018, 595989226064272, 595989229603906, 595989229603970, 595989229604032, 595989229604160, 595989229604224, 595989229997186, 595989229997440, 595995667482705, 595995667482960, 595995671661634, 595995671661888, 595997747210313, 595997747210314, 595997747210337, 595997747210505, 595997747210561, 595997747210568, 595997747210576, 595997747603729, 595997747603792, 595997747718155, 595997747718218, 595997747718409, 595997747718472, 595997747726347, 595997747726409, 595997747726433, 595997747726601, 595997747726609, 595997747726657, 595997747726664, 595997747849235, 595997747849298, 595997747849489, 595997747849552, 595997751389187, 595997751389249, 595997751389250, 595997751389441, 595997751389504, 595997751782403, 595997751782466, 595997751782657, 595997751782720, 595997751905283, 595997751905345, 595997751905346, 595997751905537, 595997751905600, 595999894825233, 595999899003907, 595999899004161, 596001907960074, 596001908091154, 596001912024322, 596001912146947, 596001912147201, 596001912147202, 875231087595594, 875231089659980, 875231091659842, 875231093724228, 875239609896971, 875239611445324, 875239611445448, 875239611961357, 875239611961481, 875239613961219, 875239615509572, 875239615509696, 875239616025605, 875239616025729, 875243772203021, 875243772203145, 875243776267269, 875243776267393, 875297675448466, 875297675448514, 875297675448528, 875297675448720, 875297675448768, 875297676234850, 875297676235104, 875297676464212, 875297676464464, 875297677512852, 875297677512900, 875297677512912, 875297678299236, 875297679381696, 875297681446080, 875306198020194, 875306198020448, 875306198249556, 875306198249808, 875306198274067, 875306198274115, 875306198274129, 875306198274130, 875306198274321, 875306198274369, 875306198274384, 875306198536227, 875306198536481, 875306198765589, 875306198765841, 875306200084580, 875306200084704, 875306200338453, 875306200338501, 875306200338513, 875306200338516, 875306200338577, 875306200338625, 875306200338640, 875306200600613, 875306200600737, 875306202207297, 875306204271681, 875310358778145, 875310359007253, 875310359007505, 875310359023635, 875310359023875, 875310359023890, 875310360842277, 875310360842401, 875310361088007, 875310361088019, 875310361088022, 875310361088131, 875310361088146, 875310362956803, 875310365021187, 1011553890538564, 1011562412839941, 1011562413306952, 1011562413822985, 1011566573081605, 1011566574064649, 1011566574064705, 1011620474327188, 1011620474327236, 1011620474327248, 1011620474327428, 1011620474327488, 1011620475113572, 1011620475113796, 1011620475310168, 1011620475310408, 1011620478260416, 1011628996898916, 1011628996899040, 1011628996899140, 1011628996899264, 1011628997095512, 1011628997095632, 1011628997095752, 1011628997095872, 1011628997152789, 1011628997152837, 1011628997152849, 1011628997152852, 1011628997152913, 1011628997152961, 1011628997152976, 1011628997153029, 1011628997153089, 1011628997153092, 1011628997153153, 1011628997153216, 1011628997414949, 1011628997415073, 1011628997415173, 1011628997415297, 1011628997611545, 1011628997611665, 1011628997611785, 1011628997611905, 1011628997881960, 1011628997882184, 1011628998135833, 1011628998135881, 1011628998135889, 1011628998135896, 1011628998136073, 1011628998136129, 1011628998136136, 1011628998397993, 1011628998398217, 1011629001086017, 1011629002069057, 1011633157656613, 1011633157656737, 1011633157656837, 1011633157656961, 1011633157853209, 1011633157853329, 1011633157853449, 1011633157853569, 1011633157902343, 1011633157902355, 1011633157902358, 1011633157902467, 1011633157902482, 1011633157902595, 1011633157902598, 1011633157902722, 1011633158639657, 1011633158639713, 1011633158639881, 1011633158639937, 1011633158885387, 1011633158885395, 1011633158885402, 1011633158885443, 1011633158885458, 1011633158885635, 1011633158885642, 1011633158885698, 1011633161835523, 1011633162818563, 1073127547868169, 1073131708109833, 1073131708503057, 1073194131927144, 1073194131927368, 1073194132058448, 1073194132181065, 1073194132181257, 1073194132181313, 1073194132181320, 1073194132443177, 1073194132443401, 1073194132574481, 1073194136114241, 1073198292684841, 1073198292684897, 1073198292685065, 1073198292685121, 1073198292816145, 1073198292816193, 1073198292930571, 1073198292930627, 1073198292930819, 1073198292930826, 1073198292930882, 1073198293078065, 1073198293078289, 1073198293323795, 1073198293324035, 1073198293324050, 1073198296863747, 1073198297256963, 1090788331376913, 1090788335555587, 1719913720972484, 1719913720972676, 1719913720972736, 1719913721890116, 1719945930213700, 1719948009416837, 1719948009416897, 1719948009416900, 1719948009417092, 1719948009417152, 1719948010334277, 1719948010334532, 1719948010457157, 1719948010457349, 1719948010457409, 1719948010457412, 1719948010850565, 1719963040884805, 1719963040884932, 1719963040885057, 1719963040885184, 1719963041400965, 1719963041401217, 1719965052987526, 1719965052987586, 1719965052987588, 1719965052987778, 1719965052987840, 1719965053904966, 1719965053905092, 1719965053905218, 1719965053905344, 1719965054027783, 1719965054027843, 1719965054027845, 1719965054027846, 1719965054027909, 1719965054027969, 1719965054027972, 1719965054028035, 1719965054028097, 1719965054028098, 1719965054028161, 1719965054028224, 1719965054420999, 1719965054421125, 1719965054421251, 1719965054421377, 1719965054535687, 1719965054535811, 1719965054535814, 1719965054535939, 1719965054536066, 1719971495569478, 1719971495569730, 1719971496085511, 1719971496085573, 1719971496085763, 1719971496085825, 1719973374388548, 1719973374511173, 1719973374511365, 1719973374511425, 1719973374511428, 1719973374904581, 1719973374904641, 1719973375019015, 1719973375019075, 1719973375019267, 1719973375019270, 1719973375019330, 1719975522126085, 1719980309611968, 1996991120815296, 1996991121855553, 1997008165426241, 1997008165934083, 1997016486417411, 1997020244055043, 1997057705390304, 1997057706430561, 1997074748960992, 1997074750001249, 1997074750509091, 1997083070484577, 1997083070992419, 1997086828630051, 2128933454632001, 2128933455139843, 2128941775623171, 2128945533260803, 2129000038166752, 2129000038166976, 2129000039207009, 2129000039207233, 2129000039714851, 2129000039715075, 2129008359690337, 2129008359690561, 2129008360198179, 2129008360198403, 2129012117835811, 2129012117836035, 2181778475372865, 2181778475880707, 2181782233518339].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_14 : layer 13 [5,5,4,4,4,4,4,3,3,3,3,3,3] 4 [] = fr13_14 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_14_0 : piece 13 [5,5,4,4,4,4,4,3,3,3,3,3,3] 4 9 7 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_14]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_14_1 : piece 13 [5,5,4,4,4,4,4,3,3,3,3,3,3] 4 9 7 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_14]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_14_2 : piece 13 [5,5,4,4,4,4,4,3,3,3,3,3,3] 4 9 7 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_14]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_14_3 : piece 13 [5,5,4,4,4,4,4,3,3,3,3,3,3] 4 9 7 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_14]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_14_4 : piece 13 [5,5,4,4,4,4,4,3,3,3,3,3,3] 4 9 7 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_14]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_14_5 : piece 13 [5,5,4,4,4,4,4,3,3,3,3,3,3] 4 9 7 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_14]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_14_6 : piece 13 [5,5,4,4,4,4,4,3,3,3,3,3,3] 4 9 7 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_14]
  decide +kernel

private lemma run13_14 : visit 13 [5,5,4,4,4,4,4,3,3,3,3,3,3] 13 [] = true := by
  apply accept_pieces [5,5,4,4,4,4,4,3,3,3,3,3,3] (bucket:=7) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_14_0
  · exact pc13_14_1
  · exact pc13_14_2
  · exact pc13_14_3
  · exact pc13_14_4
  · exact pc13_14_5
  · exact pc13_14_6
private def fr13_15 : List (List Nat) :=
  [571261285992738, 571261286025508, 571261290056752, 571261290056976, 571261290056992, 571261290155296, 571262900571408, 852152216227859, 852152216227986, 852152220390417, 852152220390544, 852154296348818, 852154296471683, 852154300511376, 852154300634241, 852220413292596, 852220413292836, 852220413292848, 852220413489432, 852220413546517, 852220413546772, 852220415381541, 852220415381553, 852220415381556, 852220415381668, 852220415381680, 852220415578137, 852220415578264, 852220417422384, 852220419511344, 852222493667604, 852222493790469, 852222495699096, 852222495756309, 852222495756421, 852222495756433, 852222495756436, 852222495821961, 852222499886097, 991773149385745, 991773150417938, 991773150418000, 991775230538770, 991775230538832, 991775230661635, 991775230661697, 991776170071105, 991841344376869, 991841344376881, 991841344376884, 991841344376996, 991841344377008, 991841344377121, 991841344377136, 991841344377248, 991841344573465, 991841344573592, 991841344573713, 991841344573840, 991841344622614, 991841344622740, 991841344622866, 991841344622992, 991841345409062, 991841345409074, 991841345409076, 991841345409124, 991841345409136, 991841345409314, 991841345409328, 991841345409376, 991841345605658, 991841345605720, 991841345605906, 991841345605968, 991841348506672, 991841349538864, 991843424694424, 991843424694672, 991843424743446, 991843424743572, 991843424743698, 991843424743824, 991843424751637, 991843424751749, 991843424751761, 991843424751764, 991843424751889, 991843424752001, 991843424752016, 991843424817289, 991843424817537, 991843424866311, 991843424866437, 991843424866563, 991843424866689, 991843425726490, 991843425726552, 991843425726738, 991843425726800, 991843425783815, 991843425783827, 991843425783829, 991843425783830, 991843425783877, 991843425783889, 991843425783892, 991843425784067, 991843425784081, 991843425784082, 991843425784129, 991843425784144, 991843425849355, 991843425849417, 991843425849603, 991843425849665, 991843428881425, 991843429913617, 991844364275845, 991844364276097, 991844365258825, 991844365259073, 991844365307911, 991844365307971, 991844365307974, 991844365308163, 991844365308226, 991844369437699, 1059934548825106, 1059934549316628, 1059936629068803, 1059936629437460, 1059936629437488, 1059936629560325, 1059936629560353, 1059937568969733, 1059937568969761, 1060002743816242, 1060002743816304, 1060002743816482, 1060002743816496, 1060002743816544, 1060002744012826, 1060002744012888, 1060002744013074, 1060002744013136, 1060002744045844, 1060002744045904, 1060002744307764, 1060002744308004, 1060002744308016, 1060002744504348, 1060002744504596, 1060002747946032, 1060002748437552, 1060004824133658, 1060004824133720, 1060004824133906, 1060004824133968, 1060004824166676, 1060004824166736, 1060004824190995, 1060004824191057, 1060004824191235, 1060004824191249, 1060004824191250, 1060004824191297, 1060004824191312, 1060004824256523, 1060004824256585, 1060004824256771, 1060004824256833, 1060004824289541, 1060004824289601, 1060004824625180, 1060004824625208, 1060004824625428, 1060004824625456, 1060004824682517, 1060004824682545, 1060004824682757, 1060004824682769, 1060004824682772, 1060004824682785, 1060004824682800, 1060004824748045, 1060004824748073, 1060004824748293, 1060004824748321, 1060004828320785, 1060004828812305, 1060005763665993, 1060005763666241, 1060005763698949, 1060005763699009, 1060005763715139, 1060005763715331, 1060005763715394, 1060005764157453, 1060005764157481, 1060005764157701, 1060005764157729, 1060005764206599, 1060005764206627, 1060005764206851, 1060005764206854, 1060005764206882, 1060005767844867, 1060005768336387, 1090785311527188, 1090785315460144, 1090787391648020, 1090787391648048, 1090787391770885, 1090787391770913, 1090787391844632, 1090787391967497, 1090787395834897, 1090787396031505, 1090788331180293, 1090788331180321, 1090788331376905, 1090788331376913, 1090788335358979, 1090788335555587, 1696873498314801, 1696873498314913, 1696873498314928, 1696873498315056, 1696873498315168, 1696873498544273, 1696873498544528, 1696881550624849, 1696881550625104, 1696882020100145, 1696882020100208, 1696882020100385, 1696882020100400, 1696882020100448, 1696882020329745, 1696882020329808, 1696882020354129, 1696882020354321, 1696882020354369, 1696882020354384, 1696882020452673, 1696885777967377, 1696885777967408, 1696885778090273, 1977214742041648, 1977223263826992, 1977223264080913, 1977227424322577, 1977227424437251, 1977282937229368, 1977291459014712, 1977291459268633, 1977295619256376, 1977295619510297, 1977295619624971, 2115736295707696, 2115744817493040, 2115744817746961, 2115748977988625, 2115748978103299, 2115750856922115, 2115804490895416, 2115804490895664, 2115813012680760, 2115813012681008, 2115813012934681, 2115813012934929, 2115817172922424, 2115817172922672, 2115817173176345, 2115817173176593, 2115817173291019, 2115817173291267, 2115819051995161, 2115819051995409, 2115819052109835, 2115819052110083, 2181775657283888, 2181775657537809, 2181779817525552, 2181779817779473, 2181779817894147, 2181781696598289, 2181781696712963, 2181782233518339].map decodeFour
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma frEq13_15 : layer 13 [5,5,4,4,4,4,4,4,4,3,3,3,3] 4 [] = fr13_15 := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_15_0 : piece 13 [5,5,4,4,4,4,4,4,4,3,3,3,3] 4 9 7 0 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_15]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_15_1 : piece 13 [5,5,4,4,4,4,4,4,4,3,3,3,3] 4 9 7 1 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_15]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_15_2 : piece 13 [5,5,4,4,4,4,4,4,4,3,3,3,3] 4 9 7 2 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_15]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_15_3 : piece 13 [5,5,4,4,4,4,4,4,4,3,3,3,3] 4 9 7 3 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_15]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_15_4 : piece 13 [5,5,4,4,4,4,4,4,4,3,3,3,3] 4 9 7 4 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_15]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_15_5 : piece 13 [5,5,4,4,4,4,4,4,4,3,3,3,3] 4 9 7 5 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_15]
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma pc13_15_6 : piece 13 [5,5,4,4,4,4,4,4,4,3,3,3,3] 4 9 7 6 = true := by
  apply prunedPiece_sound (by decide)
  unfold prunedPiece
  rw [frEq13_15]
  decide +kernel

private lemma run13_15 : visit 13 [5,5,4,4,4,4,4,4,4,3,3,3,3] 13 [] = true := by
  apply accept_pieces [5,5,4,4,4,4,4,4,4,3,3,3,3] (bucket:=7) (s:=4) (t:=9) (by decide) (by decide)
  intro j hj
  interval_cases j
  · exact pc13_15_0
  · exact pc13_15_1
  · exact pc13_15_2
  · exact pc13_15_3
  · exact pc13_15_4
  · exact pc13_15_5
  · exact pc13_15_6
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_16 : visit 13 [5,5,5,4,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_17 : visit 13 [5,5,5,4,4,4,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_18 : visit 13 [5,5,5,4,4,4,4,4,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_19 : visit 13 [5,5,5,5,4,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_20 : visit 13 [5,5,5,5,4,4,4,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_21 : visit 13 [5,5,5,5,5,4,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_22 : visit 13 [6,3,3,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_23 : visit 13 [6,4,4,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_24 : visit 13 [6,4,4,4,4,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_25 : visit 13 [6,4,4,4,4,4,4,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_26 : visit 13 [6,4,4,4,4,4,4,4,4,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_27 : visit 13 [6,5,3,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_28 : visit 13 [6,5,4,4,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_29 : visit 13 [6,5,4,4,4,4,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_30 : visit 13 [6,5,4,4,4,4,4,4,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_31 : visit 13 [6,5,5,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_32 : visit 13 [6,5,5,4,4,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_33 : visit 13 [6,5,5,4,4,4,4,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_34 : visit 13 [6,5,5,5,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_35 : visit 13 [6,5,5,5,4,4,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_36 : visit 13 [6,6,4,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_37 : visit 13 [6,6,4,4,4,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_38 : visit 13 [6,6,4,4,4,4,4,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_39 : visit 13 [6,6,5,4,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_40 : visit 13 [6,6,6,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_41 : visit 13 [7,4,3,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_42 : visit 13 [7,4,4,4,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_43 : visit 13 [7,4,4,4,4,4,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_44 : visit 13 [7,4,4,4,4,4,4,4,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_45 : visit 13 [7,5,4,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_46 : visit 13 [7,5,4,4,4,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_47 : visit 13 [7,5,5,4,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_48 : visit 13 [7,6,3,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_49 : visit 13 [7,6,4,4,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_50 : visit 13 [7,6,5,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_51 : visit 13 [7,7,4,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_52 : visit 13 [8,3,3,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_53 : visit 13 [8,4,4,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_54 : visit 13 [8,4,4,4,4,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_55 : visit 13 [8,5,3,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_56 : visit 13 [8,5,4,4,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_57 : visit 13 [8,5,5,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private lemma run13_58 : visit 13 [9,4,3,3,3,3,3,3,3,3,3,3,3] 13 [] = true := fastVisit_sound _ _ _ _ (prunedState_sound rfl (by decide +kernel))
theorem check13 : check 13 = true := by
  have h : (degreeOptions 13 13 12 156).filter (fun d => d.sum % 2 == 0) = [[4,3,3,3,3,3,3,3,3,3,3,3,3], [4,4,4,3,3,3,3,3,3,3,3,3,3], [4,4,4,4,4,3,3,3,3,3,3,3,3], [4,4,4,4,4,4,4,3,3,3,3,3,3], [4,4,4,4,4,4,4,4,4,3,3,3,3], [4,4,4,4,4,4,4,4,4,4,4,3,3], [4,4,4,4,4,4,4,4,4,4,4,4,4], [5,4,3,3,3,3,3,3,3,3,3,3,3], [5,4,4,4,3,3,3,3,3,3,3,3,3], [5,4,4,4,4,4,3,3,3,3,3,3,3], [5,4,4,4,4,4,4,4,3,3,3,3,3], [5,4,4,4,4,4,4,4,4,4,3,3,3], [5,5,4,3,3,3,3,3,3,3,3,3,3], [5,5,4,4,4,3,3,3,3,3,3,3,3], [5,5,4,4,4,4,4,3,3,3,3,3,3], [5,5,4,4,4,4,4,4,4,3,3,3,3], [5,5,5,4,3,3,3,3,3,3,3,3,3], [5,5,5,4,4,4,3,3,3,3,3,3,3], [5,5,5,4,4,4,4,4,3,3,3,3,3], [5,5,5,5,4,3,3,3,3,3,3,3,3], [5,5,5,5,4,4,4,3,3,3,3,3,3], [5,5,5,5,5,4,3,3,3,3,3,3,3], [6,3,3,3,3,3,3,3,3,3,3,3,3], [6,4,4,3,3,3,3,3,3,3,3,3,3], [6,4,4,4,4,3,3,3,3,3,3,3,3], [6,4,4,4,4,4,4,3,3,3,3,3,3], [6,4,4,4,4,4,4,4,4,3,3,3,3], [6,5,3,3,3,3,3,3,3,3,3,3,3], [6,5,4,4,3,3,3,3,3,3,3,3,3], [6,5,4,4,4,4,3,3,3,3,3,3,3], [6,5,4,4,4,4,4,4,3,3,3,3,3], [6,5,5,3,3,3,3,3,3,3,3,3,3], [6,5,5,4,4,3,3,3,3,3,3,3,3], [6,5,5,4,4,4,4,3,3,3,3,3,3], [6,5,5,5,3,3,3,3,3,3,3,3,3], [6,5,5,5,4,4,3,3,3,3,3,3,3], [6,6,4,3,3,3,3,3,3,3,3,3,3], [6,6,4,4,4,3,3,3,3,3,3,3,3], [6,6,4,4,4,4,4,3,3,3,3,3,3], [6,6,5,4,3,3,3,3,3,3,3,3,3], [6,6,6,3,3,3,3,3,3,3,3,3,3], [7,4,3,3,3,3,3,3,3,3,3,3,3], [7,4,4,4,3,3,3,3,3,3,3,3,3], [7,4,4,4,4,4,3,3,3,3,3,3,3], [7,4,4,4,4,4,4,4,3,3,3,3,3], [7,5,4,3,3,3,3,3,3,3,3,3,3], [7,5,4,4,4,3,3,3,3,3,3,3,3], [7,5,5,4,3,3,3,3,3,3,3,3,3], [7,6,3,3,3,3,3,3,3,3,3,3,3], [7,6,4,4,3,3,3,3,3,3,3,3,3], [7,6,5,3,3,3,3,3,3,3,3,3,3], [7,7,4,3,3,3,3,3,3,3,3,3,3], [8,3,3,3,3,3,3,3,3,3,3,3,3], [8,4,4,3,3,3,3,3,3,3,3,3,3], [8,4,4,4,4,3,3,3,3,3,3,3,3], [8,5,3,3,3,3,3,3,3,3,3,3,3], [8,5,4,4,3,3,3,3,3,3,3,3,3], [8,5,5,3,3,3,3,3,3,3,3,3,3], [9,4,3,3,3,3,3,3,3,3,3,3,3]] := by decide +kernel
  unfold check
  rw [List.all_eq_true]
  intro d hd
  by_cases he : d.sum % 2 = 0
  · have hm : d ∈ (degreeOptions _ _ _ _).filter (fun d => d.sum % 2 == 0) := List.mem_filter.mpr ⟨hd, by simp [he]⟩
    rw [h] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [run13_0, Bool.or_true]
    · simp only [run13_1, Bool.or_true]
    · simp only [run13_2, Bool.or_true]
    · simp only [run13_3, Bool.or_true]
    · simp only [run13_4, Bool.or_true]
    · simp only [run13_5, Bool.or_true]
    · simp only [run13_6, Bool.or_true]
    · simp only [run13_7, Bool.or_true]
    · simp only [run13_8, Bool.or_true]
    · simp only [run13_9, Bool.or_true]
    · simp only [run13_10, Bool.or_true]
    · simp only [run13_11, Bool.or_true]
    · simp only [run13_12, Bool.or_true]
    · simp only [run13_13, Bool.or_true]
    · simp only [run13_14, Bool.or_true]
    · simp only [run13_15, Bool.or_true]
    · simp only [run13_16, Bool.or_true]
    · simp only [run13_17, Bool.or_true]
    · simp only [run13_18, Bool.or_true]
    · simp only [run13_19, Bool.or_true]
    · simp only [run13_20, Bool.or_true]
    · simp only [run13_21, Bool.or_true]
    · simp only [run13_22, Bool.or_true]
    · simp only [run13_23, Bool.or_true]
    · simp only [run13_24, Bool.or_true]
    · simp only [run13_25, Bool.or_true]
    · simp only [run13_26, Bool.or_true]
    · simp only [run13_27, Bool.or_true]
    · simp only [run13_28, Bool.or_true]
    · simp only [run13_29, Bool.or_true]
    · simp only [run13_30, Bool.or_true]
    · simp only [run13_31, Bool.or_true]
    · simp only [run13_32, Bool.or_true]
    · simp only [run13_33, Bool.or_true]
    · simp only [run13_34, Bool.or_true]
    · simp only [run13_35, Bool.or_true]
    · simp only [run13_36, Bool.or_true]
    · simp only [run13_37, Bool.or_true]
    · simp only [run13_38, Bool.or_true]
    · simp only [run13_39, Bool.or_true]
    · simp only [run13_40, Bool.or_true]
    · simp only [run13_41, Bool.or_true]
    · simp only [run13_42, Bool.or_true]
    · simp only [run13_43, Bool.or_true]
    · simp only [run13_44, Bool.or_true]
    · simp only [run13_45, Bool.or_true]
    · simp only [run13_46, Bool.or_true]
    · simp only [run13_47, Bool.or_true]
    · simp only [run13_48, Bool.or_true]
    · simp only [run13_49, Bool.or_true]
    · simp only [run13_50, Bool.or_true]
    · simp only [run13_51, Bool.or_true]
    · simp only [run13_52, Bool.or_true]
    · simp only [run13_53, Bool.or_true]
    · simp only [run13_54, Bool.or_true]
    · simp only [run13_55, Bool.or_true]
    · simp only [run13_56, Bool.or_true]
    · simp only [run13_57, Bool.or_true]
    · simp only [run13_58, Bool.or_true]
  · apply Bool.or_eq_true_iff.mpr
    exact Or.inl (bne_iff_ne.mpr he)
end Census904

namespace Census904

theorem check_at_most_thirteen {n : Nat} (hn : 0 < n) (high : n ≤ 13) : check n = true := by
  interval_cases n
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13

end Census904

namespace Canonical904

private def key {n : ℕ} (A : Fin n → Fin n → Bool) : Lex (Fin n → Lex (Fin n → Bool)) :=
  toLex (fun i => toLex (A i))

private theorem swap_increases {n : ℕ} (A : Fin n → Fin n → Bool)
    (sym : ∀ a b, A a b = A b a) (diag : ∀ a, A a a = false)
    {i j k : Fin n} (ij : i < j) (ki : k ≠ i) (kj : k ≠ j)
    (before : ∀ z < k, z ≠ i → z ≠ j → A i z = A j z)
    (low : A i k = false) (high : A j k = true) :
    key A < key (fun a b => A (Equiv.swap i j a) (Equiv.swap i j b)) := by
  let σ := Equiv.swap i j
  let B := fun a b => A (σ a) (σ b)
  have si : σ i = j := Equiv.swap_apply_left _ _
  have sj : σ j = i := Equiv.swap_apply_right _ _
  have sf (a : Fin n) (ai : a ≠ i) (aj : a ≠ j) : σ a = a :=
    Equiv.swap_apply_of_ne_of_ne ai aj
  have row_eq (a : Fin n) (ai : a ≠ i) (aj : a ≠ j) (h : A i a = A j a) :
      A a = B a := by
    funext b
    change A a b = A (σ a) (σ b)
    rw [sf a ai aj]
    by_cases bi : b = i
    · subst b
      simpa only [si, sym a] using h
    by_cases bj : b = j
    · subst b
      simpa only [sj, sym a] using h.symm
    rw [sf b bi bj]
  change Pi.Lex (· < ·) (· < ·) (fun a => toLex (A a)) (fun a => toLex (B a))
  rcases lt_or_gt_of_ne ki with hki | hik
  · refine ⟨k, ?_, ?_⟩
    · intro a hak
      exact congrArg toLex (row_eq a (ne_of_lt (hak.trans hki)) (ne_of_lt ((hak.trans hki).trans ij))
        (before a hak (ne_of_lt (hak.trans hki)) (ne_of_lt ((hak.trans hki).trans ij))))
    · change Pi.Lex (· < ·) (· < ·) (A k) (B k)
      refine ⟨i, ?_, ?_⟩
      · intro b hb
        change A k b = A (σ k) (σ b)
        rw [sf k ki kj, sf b (ne_of_lt hb) (ne_of_lt (hb.trans ij))]
      · change A k i < A (σ k) (σ i)
        rw [sf k ki kj, si, sym k i, sym k j, low, high]
        decide
  · refine ⟨i, ?_, ?_⟩
    · intro a hai
      exact congrArg toLex (row_eq a (ne_of_lt hai) (ne_of_lt (hai.trans ij))
        (before a (hai.trans hik) (ne_of_lt hai) (ne_of_lt (hai.trans ij))))
    · change Pi.Lex (· < ·) (· < ·) (A i) (B i)
      refine ⟨k, ?_, ?_⟩
      · intro b hb
        change A i b = A (σ i) (σ b)
        rw [si]
        by_cases bi : b = i
        · subst b
          rw [si, diag i, diag j]
        by_cases bj : b = j
        · subst b
          rw [sj, sym i j]
        rw [sf b bi bj]
        exact before b hb bi bj
      · change A i k < A (σ i) (σ k)
        rw [si, sf k ki kj, low, high]
        decide

theorem relabel {n : ℕ} (A : Fin n → Fin n → Bool) (d : Fin n → ℕ)
    (sym : ∀ a b, A a b = A b a) (diag : ∀ a, A a a = false) :
    ∃ p : Equiv.Perm (Fin n), Antitone (fun i => d (p i)) ∧
      ∀ i j k, i < j → d (p i) = d (p j) → k ≠ i → k ≠ j →
        (∀ z < k, z ≠ i → z ≠ j → A (p i) (p z) = A (p j) (p z)) →
        A (p i) (p k) ≠ A (p j) (p k) → A (p i) (p k) = true := by
  classical
  let S := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun p => Antitone (fun i => d (p i)))
  have nonempty : S.Nonempty := ⟨Tuple.sortDesc d, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Tuple.antitone_sortDesc d⟩⟩
  obtain ⟨p,hp,maximal⟩ := S.exists_max_image (fun p => key (fun a b => A (p a) (p b))) nonempty
  have hp' := (Finset.mem_filter.mp hp).2
  refine ⟨p,hp',?_⟩
  intro i j k hij same ki kj before different
  by_contra h
  have low : A (p i) (p k) = false := Bool.eq_false_of_not_eq_true h
  have high : A (p j) (p k) = true := by
    cases ht : A (p j) (p k)
    · exact (different (low.trans ht.symm)).elim
    · rfl
  let σ := Equiv.swap i j
  have preserv (a : Fin n) : d (p (σ a)) = d (p a) := by
    by_cases ha : a = i
    · subst a
      exact (congrArg (d ∘ p) (Equiv.swap_apply_left i j)).trans same.symm
    by_cases hb : a = j
    · subst a
      exact (congrArg (d ∘ p) (Equiv.swap_apply_right i j)).trans same
    exact congrArg (d ∘ p) (Equiv.swap_apply_of_ne_of_ne ha hb)
  have hσ : σ.trans p ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro a b hab
    change d (p (σ b)) ≤ d (p (σ a))
    rw [preserv, preserv]
    exact hp' hab
  have inc := swap_increases (fun a b => A (p a) (p b))
    (fun a b => sym (p a) (p b)) (fun a => diag (p a)) hij ki kj before low high
  exact (not_lt_of_ge (maximal _ hσ)) inc

end Canonical904

namespace Census904

private theorem hits_eq_bit (n r j : ℕ) : hits n r j = r.testBit (n-1-j) := by
  unfold hits bit
  rw [Nat.and_two_pow]
  cases r.testBit (n-1-j) <;> simp

private def row {n : ℕ} (A : Fin n → Fin n → Bool) (i : Fin n) : ℕ :=
  pack (List.ofFn (A i))

private def matrix {n : ℕ} (A : Fin n → Fin n → Bool) : List Nat :=
  List.ofFn (row A)

private theorem row_hits {n : ℕ} (A : Fin n → Fin n → Bool) (i j : Fin n) :
    hits n (row A i) j = A i j := by
  rw [hits_eq_bit]
  simpa [row] using pack_bit (List.ofFn (A i)) (j : ℕ) (by simp)

private theorem row_high_false {n : ℕ} (A : Fin n → Fin n → Bool) (i : Fin n)
    (b : ℕ) (hb : n ≤ b) : (row A i).testBit b = false := by
  apply Nat.testBit_lt_two_pow
  have h : row A i < 2^n := by simpa [row] using pack_bound (List.ofFn (A i))
  exact h.trans_le (Nat.pow_le_pow_right (by decide) hb)

private theorem mask_bit {n : ℕ} (i j k : Fin n) :
    ((2^n-1) ^^^ (bit n i ||| bit n j)).testBit (n-1-k) =
      (!decide (k = i) && !decide (k = j)) := by
  have hk : n-1-(k:ℕ) < n := by omega
  have h (a : Fin n) : (n-1-(a:ℕ) = n-1-(k:ℕ)) ↔ k = a := by
    rw [Fin.ext_iff]
    omega
  simp only [Nat.testBit_xor, Nat.testBit_or, bit, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one, hk, decide_true, h]
  cases e₁ : decide (k = i) <;> cases e₂ : decide (k = j) <;> decide

private theorem masked_ge {n : ℕ} (A : Fin n → Fin n → Bool) {i j : Fin n}
    (canonical : ∀ k, k ≠ i → k ≠ j →
      (∀ z < k, z ≠ i → z ≠ j → A i z = A j z) → A i k ≠ A j k → A i k = true) :
    (row A j &&& ((2^n-1) ^^^ (bit n i ||| bit n j))) ≤
      (row A i &&& ((2^n-1) ^^^ (bit n i ||| bit n j))) := by
  classical
  let m := (2^n-1) ^^^ (bit n i ||| bit n j)
  have maskAt (a k : Fin n) : (row A a &&& m).testBit (n-1-k) =
      if k = i ∨ k = j then false else A a k := by
    rw [Nat.testBit_and, ← hits_eq_bit, row_hits, mask_bit]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki,hkj]
  let S : Finset (Fin n) := Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧ A i k ≠ A j k)
  by_cases hs : S.Nonempty
  · let k := S.min' hs
    obtain ⟨ki,kj,diff⟩ := (Finset.mem_filter.mp (S.min'_mem hs)).2
    have eq (z : Fin n) (hzk : z < k) (zi : z ≠ i) (zj : z ≠ j) : A i z = A j z := by
      by_contra h
      have hzS : z ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,zi,zj,h⟩
      exact (not_lt_of_ge (S.min'_le z hzS)) hzk
    have yes := canonical k ki kj eq diff
    have no : A j k = false := by
      cases h : A j k
      · rfl
      · exact (diff (yes.trans h.symm)).elim
    apply le_of_lt
    apply Nat.lt_of_testBit (n-1-k)
    · change (row A j &&& m).testBit (n-1-k) = false
      rw [maskAt j k]
      rw [if_neg (show ¬ (k = i ∨ k = j) from not_or_intro ki kj)]
      exact no
    · change (row A i &&& m).testBit (n-1-k) = true
      rw [maskAt i k]
      rw [if_neg (show ¬ (k = i ∨ k = j) from not_or_intro ki kj)]
      exact yes
    · intro b hb
      by_cases hbn : b < n
      · let z : Fin n := ⟨n-1-b,by omega⟩
        have idx : n-1-(z:ℕ) = b := by dsimp [z]; omega
        have hzk : z < k := by change z.val < k.val; dsimp [z]; omega
        rw [← idx, maskAt j z, maskAt i z]
        by_cases zi : z = i <;> by_cases zj : z = j <;> simp [zi,zj, eq z hzk]
      · rw [Nat.testBit_and, Nat.testBit_and, row_high_false A i _ (by omega), row_high_false A j _ (by omega)]
  · apply le_of_eq
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hbn : b < n
    · let z : Fin n := ⟨n-1-b,by omega⟩
      have idx : n-1-(z:ℕ) = b := by dsimp [z]; omega
      rw [← idx, maskAt j z, maskAt i z]
      by_cases zi : z = i <;> by_cases zj : z = j <;> simp [zi,zj]
      by_contra hnz
      exact hs ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,zi,zj,Ne.symm hnz⟩⟩
    · rw [Nat.testBit_and, Nat.testBit_and, row_high_false A i _ (by omega), row_high_false A j _ (by omega)]


end Census904

namespace Census904

open Finset

private def past {n : ℕ} (A : Fin n → Fin n → Bool) (i : Fin n) : List Nat :=
  (matrix A).take i

private theorem past_len {n : ℕ} (A : Fin n → Fin n → Bool) (i : Fin n) :
    (past A i).length = i.val := by simp [past,matrix]

private theorem past_map {n : ℕ} (A : Fin n → Fin n → Bool) (i j : Fin n) :
    (past A i).map (fun r => hits n r j) = (List.ofFn fun k => A k j).take i := by
  apply List.ext_getElem?
  intro k
  by_cases hki : k < i.val
  · have hk : k < n := hki.trans i.isLt
    simp only [past,matrix,List.getElem?_map,List.getElem?_take,List.getElem?_ofFn,hki,hk,
      dite_true,if_true, Option.map_some, row_hits]
  · simp [past,hki]

private theorem future_map {n : ℕ} (A : Fin n → Fin n → Bool) (i : Fin n) :
    (vertices n i).map (hits n (row A i)) = (List.ofFn (A i)).drop (i.val+1) := by
  apply List.ext_getElem?
  intro k
  simp only [vertices,List.getElem?_map,List.getElem?_drop,List.getElem?_ofFn]
  by_cases h : i.val+1+k < n
  · rw [List.getElem?_range h, dif_pos h]
    exact congrArg some (row_hits A i ⟨_,h⟩)
  · simp [h]

private theorem prefix_bit {n : ℕ} (A : Fin n → Fin n → Bool) (i j k : Fin n) :
    (incoming n j (past A i)).testBit (n-1-k) = if k < i then A k j else false := by
  unfold incoming
  change (pack ((past A i).map (fun r => hits n r j)) <<< (n - (past A i).length)).testBit _ = _
  rw [past_map, past_len, Nat.testBit_shiftLeft]
  by_cases h : k < i
  · have kk : k.val < i.val := h
    have later : n-i.val ≤ n-1-k.val := by omega
    have len : ((List.ofFn fun a => A a j).take i).length = i.val := by
      simp
    have ht : (n-1-k.val)-(n-i.val) = i.val-1-k.val := by omega
    have idx : (n-1-k.val)-(n-i.val) = ((List.ofFn fun a => A a j).take i).length-1-k.val := by
      rw [len,ht]
    rw [idx]
    have b : k.val < ((List.ofFn fun a => A a j).take i).length := by omega
    rw [pack_bit _ k.val b]
    simp [later,h, List.getElem_take]
  · have hh : ¬ n-i.val ≤ n-1-k.val := by
      change ¬ k.val < i.val at h
      omega
    simp [hh,h]

private theorem suffix_bit {n : ℕ} (A : Fin n → Fin n → Bool) (i k : Fin n) :
    (pack ((vertices n i).map (hits n (row A i)))).testBit (n-1-k) =
      if i < k then A i k else false := by
  rw [future_map]
  have len : ((List.ofFn (A i)).drop (i.val+1)).length = n-(i.val+1) := by simp
  by_cases h : i < k
  · have kk : i.val < k.val := h
    have b : k.val-(i.val+1) < ((List.ofFn (A i)).drop (i.val+1)).length := by
      have kn := k.isLt
      omega
    have idx : n-1-k.val = ((List.ofFn (A i)).drop (i.val+1)).length - 1 - (k.val-(i.val+1)) := by
      have kn := k.isLt
      omega
    rw [idx, pack_bit _ _ b, if_pos h, List.getElem_drop, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    dsimp
    omega
  · rw [if_neg h]
    apply Nat.testBit_lt_two_pow
    apply (pack_bound _).trans_le
    apply Nat.pow_le_pow_right (by decide)
    rw [len]
    change ¬ i.val < k.val at h
    omega

private theorem row_append {n : ℕ} (A : Fin n → Fin n → Bool)
    (sym : ∀ a b, A a b = A b a) (diag : ∀ a, A a a = false) (i : Fin n) :
    row A i = incoming n i (past A i) ||| pack ((vertices n i).map (hits n (row A i))) := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hkn : k < n
  · let v : Fin n := ⟨n-1-k,by omega⟩
    have idx : n-1-v.val = k := by dsimp [v]; omega
    rw [← idx, Nat.testBit_or, prefix_bit, suffix_bit, ← hits_eq_bit, row_hits]
    rcases lt_trichotomy v i with h | rfl | h
    · simpa [h, not_lt_of_gt h] using sym i v
    · simp [diag]
    · simp [h, not_lt_of_gt h]
  · rw [Nat.testBit_or, row_high_false A i _ (by omega)]
    have suf : (pack ((vertices n i).map (hits n (row A i)))).testBit k = false := by
      apply Nat.testBit_lt_two_pow
      apply (pack_bound _).trans_le
      apply Nat.pow_le_pow_right (by decide)
      rw [future_map]
      simp
      omega
    have pre : (incoming n i (past A i)).testBit k = false := by
      unfold incoming
      rw [Nat.testBit_shiftLeft]
      have l : ((past A i).map (fun r => r &&& bit n i != 0)).length = i.val := by simp [past_len]
      have hh : i.val ≤ k - (n-(past A i).length) := by rw [past_len]; omega
      rw [Nat.testBit_lt_two_pow ((pack_bound _).trans_le
        (Nat.pow_le_pow_right (by decide) (show _ ≤ _ by rw [l]; exact hh)))]
      simp
    rw [pre,suf]
    rfl

private theorem count_parts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    let A := fun a b => decide (G.Adj a b)
    G.degree i = ((past A i).map (fun r => hits n r i)).count true +
      ((vertices n i).map (hits n (row A i))).count true := by
  dsimp only
  rw [past_map, future_map]
  have sy (a : Fin n) : decide (G.Adj a i) = decide (G.Adj i a) := by
    rw [decide_eq_decide]
    exact ⟨SimpleGraph.Adj.symm,SimpleGraph.Adj.symm⟩
  simp_rw [sy]
  let q := List.ofFn (fun a => decide (G.Adj i a))
  have whole : q.count true = G.degree i := by
    rw [List.count_ofFn, ← G.card_neighborFinset_eq_degree]
    congr 1
    ext a
    simp [G.mem_neighborFinset]
  have piece : q.drop i.val = false :: q.drop (i.val+1) := by
    rw [List.drop_eq_getElem_cons (show i.val < q.length by simp [q])]
    simp [q]
  change G.degree i = (q.take i.val).count true + (q.drop (i.val+1)).count true
  rw [← whole]
  conv_lhs => rw [← List.take_append_drop i.val q]
  rw [List.count_append, piece]
  simp

private theorem incoming_agrees {n : ℕ} (A : Fin n → Fin n → Bool)
    {i u v : Fin n} (e : incoming n u (past A i) = incoming n v (past A i)) :
    ∀ z < i, A z u = A z v := by
  intro z hz
  have eq := congrArg (fun r : Nat => r.testBit (n-1-z.val)) e
  simpa only [prefix_bit,if_pos hz] using eq

private theorem common_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (no4 : Reduction904.SquareFree G) {i j : Fin n} (ij : i ≠ j) :
    let A := fun a b => decide (G.Adj a b)
    small (row A i &&& row A j) = true := by
  dsimp only
  apply small_of_unique
  intro u v hu hv
  have ub : u < n := by
    by_contra! h
    rw [Nat.testBit_and, row_high_false _ i _ h] at hu
    contradiction
  have vb : v < n := by
    by_contra! h
    rw [Nat.testBit_and, row_high_false _ i _ h] at hv
    contradiction
  let a : Fin n := ⟨n-1-u,by omega⟩
  let b : Fin n := ⟨n-1-v,by omega⟩
  have au : n-1-a.val = u := by dsimp [a]; omega
  have bv : n-1-b.val = v := by dsimp [b]; omega
  have get (x : Fin n) (h : (row (fun a b => decide (G.Adj a b)) i &&&
      row (fun a b => decide (G.Adj a b)) j).testBit (n-1-x.val) = true) :
      G.Adj i x ∧ G.Adj j x := by
    rw [Nat.testBit_and] at h
    have hp := Bool.and_eq_true_iff.mp h
    obtain ⟨hi,hj⟩ := hp
    rw [← hits_eq_bit, row_hits] at hi hj
    exact ⟨of_decide_eq_true hi, of_decide_eq_true hj⟩
  obtain ⟨hia,hja⟩ := get a (au.symm ▸ hu)
  obtain ⟨hib,hjb⟩ := get b (bv.symm ▸ hv)
  have eq : a = b := by
    by_contra h
    exact no4 i a j b ij h hia hja.symm hjb hib.symm
  omega

end Census904

namespace Census904

open Finset

private theorem hits_matrix {n : ℕ} (A : Fin n → Fin n → Bool) (i j : Fin n) :
    hits n ((matrix A)[i.val]?.getD 0) j.val = A i j := by
  simpa [matrix,i.isLt] using row_hits A i j

private theorem color_of_palette {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (t : ℕ × ℕ × ℕ) (h : paletteOK n (matrix (fun a b => decide (G.Adj a b))) t = true) :
    G.Colorable 3 := by
  let A := fun a b => decide (G.Adj a b)
  let c : Fin n → Fin 3 := fun i =>
    if bit n i &&& t.1 != 0 then 0 else if bit n i &&& t.2.1 != 0 then 1 else 2
  let M (k : Fin 3) := if k = 0 then t.1 else if k = 1 then t.2.1 else t.2.2
  have mask (i : Fin n) : M (c i) =
      if bit n i &&& t.1 != 0 then t.1 else if bit n i &&& t.2.1 != 0 then t.2.1 else t.2.2 := by
    dsimp [M,c]
    split <;> rename_i h
    · rfl
    split <;> rfl
  have localOK (i : Fin n) : bit n i &&& M (c i) ≠ 0 ∧ row A i &&& M (c i) = 0 := by
    have hm : (row A i, i.val) ∈ (matrix A).zipIdx := by
      exact List.mem_zipIdx_iff_getElem?.mpr (by simp [matrix,i.isLt])
    have hk := List.all_eq_true.mp h _ hm
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hk
    simpa only [mask, bne_iff_ne] using hk
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro u v hEdge hc
  obtain ⟨hb, _⟩ := localOK v
  have yes : (M (c v)).testBit (n-1-v.val) = true := by
    rw [← hits_eq_bit]
    simpa [hits, Nat.land_comm] using hb
  have huv : (row A u).testBit (n-1-v.val) = true := by
    rw [← hits_eq_bit, row_hits]
    simpa [A] using hEdge
  have hzero := (localOK u).2
  have zz := congrArg (fun q : ℕ => q.testBit (n-1-v.val)) hzero
  simp [Nat.testBit_and, hc, huv, yes] at zz

private theorem wedge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : Reduction904.SquareFree G) : (∑ i, G.degree i * (G.degree i-1)) ≤ n*(n-1) := by
  have hs := Regular904.degree_square_sum G h4
  have heq : (∑ i, G.degree i ^ 2) = (∑ i, G.degree i * (G.degree i-1)) +
      ∑ i, G.degree i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hc : G.degree i * (G.degree i-1) = G.degree i * G.degree i - G.degree i := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [hc, Nat.sub_add_cancel (Nat.le_mul_self _), pow_two]
  rw [heq] at hs
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  omega

private theorem row_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : Reduction904.SquareFree G)
    (canon : ∀ i j k : Fin n, i < j → G.degree i = G.degree j → k ≠ i → k ≠ j →
      (∀ z < k, z ≠ i → z ≠ j → decide (G.Adj i z) = decide (G.Adj j z)) →
      decide (G.Adj i k) ≠ decide (G.Adj j k) → decide (G.Adj i k) = true)
    (i : Fin n) :
    let A := fun a b => decide (G.Adj a b)
    let d := List.ofFn (fun v => G.degree v)
    let p := past A i
    let r := row A i
    (r = incoming n p.length p ||| pack ((vertices n p.length).map (hits n r))) ∧
    (d[p.length]?.getD 0 = (p.map (fun s => hits n s p.length)).count true +
          ((vertices n p.length).map (hits n r)).count true) ∧
    (vertices n p.length).Pairwise (fun u v =>
      key n d p u = key n d p v → hits n r u = false → hits n r v = false) ∧
    rowOK n d p r = true := by
  dsimp only
  let A := fun a b => decide (G.Adj a b)
  let d := List.ofFn (fun v => G.degree v)
  let p := past A i
  let r := row A i
  have plen : p.length = i.val := past_len A i
  have sym (u v : Fin n) : A u v = A v u := by
    rw [decide_eq_decide]
    exact ⟨SimpleGraph.Adj.symm,SimpleGraph.Adj.symm⟩
  have diag (u : Fin n) : A u u = false := by simp [A]
  have dv (v : Fin n) : d[v.val]? = some (G.degree v) := by simp [d,v.isLt]
  refine ⟨?_,?_,?_,?_⟩
  · rw [past_len]
    exact row_append A sym diag i
  · rw [past_len, dv]
    exact count_parts G i
  · rw [past_len, List.pairwise_iff_getElem]
    intro j k hj hk hjk
    let u : Fin n := ⟨i.val+1+j, by simp [vertices] at hj; omega⟩
    let v : Fin n := ⟨i.val+1+k, by simp [vertices] at hk; omega⟩
    have eu : (vertices n i)[j] = u.val := by simp [u,vertices,List.getElem_drop]
    have ev : (vertices n i)[k] = v.val := by simp [v,vertices,List.getElem_drop]
    have iu : i < u := by change i.val < i.val+1+j; omega
    have iv : i < v := by change i.val < i.val+1+k; omega
    have uv : u < v := by change i.val+1+j < i.val+1+k; omega
    rw [eu,ev]
    change key n d p u.val = key n d p v.val → hits n r u.val = false → hits n r v.val = false
    intro hex hn
    rw [row_hits] at hn ⊢
    have keyDeg : G.degree u = G.degree v := by
      have heq := congrArg Prod.fst hex
      simpa only [key,dv,Option.getD_some] using heq
    have near : ∀ z < i, A u z = A v z := by
      intro z hz
      rw [sym u z, sym v z]
      exact incoming_agrees A (congrArg Prod.snd hex) z hz
    by_contra! h
    have hl : A u i = false := (sym u i).trans hn
    have hr : A v i = true := (sym v i).trans (Bool.eq_true_of_not_eq_false h)
    have hf := canon u v i uv keyDeg (ne_of_lt iu) (ne_of_lt iv)
      (fun z hz _ _ => near z hz) (fun h => Bool.false_ne_true (hl.symm.trans (h.trans hr)))
    exact Bool.false_ne_true (hl.symm.trans hf)
  · change rowOK n d p r = true
    unfold rowOK
    rw [plen, List.all_eq_true]
    rintro ⟨s,k⟩ hk
    have ks := List.mem_zipIdx_iff_getElem?.mp hk
    have kl : k < i.val := by
      have := List.getElem?_eq_some_iff.mp ks
      simpa [plen] using this.choose
    let j : Fin n := ⟨k,kl.trans i.isLt⟩
    have seq : row A j = s := by
      simpa [p,past,matrix,kl,j.isLt,j] using ks
    subst s
    apply Bool.and_eq_true_iff.mpr
    refine ⟨common_small G h4 (ne_of_lt (show j < i from kl)),?_⟩
    rw [Bool.or_eq_true, dv j, dv i]
    by_cases hsame : G.degree j = G.degree i
    · apply Or.inr
      apply decide_eq_true
      have cmp := masked_ge A (canon j i · (show j < i from kl) hsame)
      simpa only [Nat.lor_comm (bit n j) (bit n i)] using cmp
    · exact Or.inl (by simpa using hsame)

private theorem classify_checked {n : ℕ} (checked : check n = true)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : Reduction904.SquareFree G)
    (low : ∀ v, 3 ≤ G.degree v) :
    G.Colorable 3 ∨ ∃ p : Equiv.Perm (Fin n),
      matrix (fun i j => decide ((G.comap p).Adj i j)) ∈ exceptions n := by
  obtain ⟨p,ord,can⟩ := Canonical904.relabel (fun a b => decide (G.Adj a b)) (fun v => G.degree v)
    (fun a b => by rw [decide_eq_decide]; exact ⟨SimpleGraph.Adj.symm,SimpleGraph.Adj.symm⟩)
    (fun a => by simp)
  let H := G.comap p
  let iso : H ≃g G := SimpleGraph.Iso.comap p G
  have dEq (v : Fin n) : H.degree v = G.degree (p v) := (iso.degree_eq v).symm
  have hH : Reduction904.SquareFree H :=
    fun a b c d hac hbd => h4 _ _ _ _ (p.injective.ne hac) (p.injective.ne hbd)
  let A := fun a b => decide (H.Adj a b)
  let d := List.ofFn (fun v => H.degree v)
  have dh : d.length = n := List.length_ofFn
  have rh : (matrix A).length = n := List.length_ofFn
  have dd (j : ℕ) (hj : j < d.length) : d[j] = H.degree ⟨j,dh ▸ hj⟩ := List.getElem_ofFn hj
  have ordered : d.Pairwise (· ≥ ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [dd i hi, dd j hj, dEq,dEq]
    exact ord (Nat.le_of_lt hij)
  have dlo (j : ℕ) (hj : j ∈ d) : 3 ≤ j := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
    rw [dEq]
    exact low (p i)
  have dhi (j : ℕ) (hj : j ∈ d) : j ≤ n-1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
    have h := H.degree_lt_card_verts i
    simp at h
    omega
  have cost : (d.map (fun a => a*(a-1))).sum ≤ n*(n-1) := by
    simpa [d, List.map_ofFn, List.sum_ofFn, Function.comp_def] using wedge_bound H hH
  have even : d.sum % 2 = 0 := by
    rw [List.sum_ofFn, H.sum_degrees_eq_twice_card_edges]
    omega
  have leafOK := catalogue_of_checks checked d (matrix A) dh rh ordered dlo dhi cost even (by
    intro i hi
    let j : Fin n := ⟨i,rh ▸ hi⟩
    have hr : (matrix A)[i] = row A j := List.getElem_ofFn hi
    rw [hr]
    exact row_valid H hH (fun a b c ab hs => can a b c ab (by simpa only [← dEq] using hs)) j)
  rcases Bool.or_eq_true_iff.mp leafOK with h | h
  · exact .inr ⟨p, List.contains_iff_mem.mp h⟩
  · obtain ⟨t,_,ht⟩ := List.any_eq_true.mp h
    obtain ⟨c⟩ := color_of_palette H t ht
    apply Or.inl
    refine ⟨SimpleGraph.Coloring.mk (fun u => c (p.symm u)) ?_⟩
    intro u v he
    apply c.valid
    change G.Adj (p (p.symm u)) (p (p.symm v))
    simpa only [Equiv.apply_symm_apply] using he

end Census904

namespace Census904

private theorem classify {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bound : n ≤ 13) (sq : Reduction904.SquareFree G)
    (minDeg : ∀ v, 3 ≤ G.degree v) :
    G.Colorable 3 ∨ ∃ p : Equiv.Perm (Fin n),
      matrix (fun i j => decide ((G.comap p).Adj i j)) ∈ exceptions n := by
  by_cases h : n = 0
  · subst n
    exact Or.inl ⟨SimpleGraph.Coloring.mk (fun v => v.elim0) (fun {u} => u.elim0)⟩
  · exact classify_checked (check_at_most_thirteen (Nat.pos_of_ne_zero h) bound) G sq minDeg

end Census904

namespace OrientationCert904

open Finset

private def edgeListGraph {n : ℕ} (E : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => (a,b) ∈ E

private def selected (M : ℕ) {n : ℕ} (v : Fin n) : Bool := M.testBit v.val

private def hits {n : ℕ} (A : List (Fin n × Fin n)) (M : ℕ) (v : Fin n) : Bool :=
  A.any fun p => decide (p.1 = v) && selected M p.2

private def leafOK {n : ℕ} (E A : List (Fin n × Fin n)) (w : Fin n) (M : ℕ) : Bool :=
  !selected M w && E.all fun (a,b) =>
    !(selected M a && selected M b) &&
      (selected M a || selected M b || hits A M a || hits A M b)

private def check {n : ℕ} (E : List (Fin n × Fin n)) (w : Fin n) :
    ℕ → List Nat → List (Fin n × Fin n) → Option (List Nat)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, t :: ts, A =>
    if 128 ≤ t then
      if leafOK E A w (t - 128) then some ts else none
    else do
      let (a,b) ← E[t]?
      if a = b then none
      else
        let rest ← check E w fuel ts ((b,a) :: A)
        check E w fuel rest ((a,b) :: A)

private theorem leaf_sound {n : ℕ} (E A : List (Fin n × Fin n)) (w : Fin n) (M : ℕ)
    (D : Fin n → Fin n → Prop)
    (arcs : ∀ p ∈ A, (edgeListGraph E).Adj p.1 p.2 ∧ D p.1 p.2)
    (ok : leafOK E A w M = true) :
    ∃ I, Reduction904.WitnessOn (edgeListGraph E) D univ I ∧ w ∉ I := by
  let I := (univ : Finset (Fin n)).filter (fun v => selected M v = true)
  have hI (v : Fin n) : v ∈ I ↔ selected M v = true := by simp [I]
  have hw : ¬ selected M w = true := by
    simp only [leafOK, Bool.and_eq_true, Bool.not_eq_true'] at ok
    simp [ok.1]
  have hpair {a b : Fin n} (h : (a,b) ∈ E) :
      ¬ (selected M a = true ∧ selected M b = true) ∧
        (selected M a = true ∨ selected M b = true ∨ hits A M a = true ∨ hits A M b = true) := by
    have hh := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 (a,b) h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at hh
    simpa [or_assoc] using hh
  have hhits {v : Fin n} (h : hits A M v = true) : ∃ i ∈ I, (edgeListGraph E).Adj v i ∧ D v i := by
    obtain ⟨⟨a,b⟩,hm,hp⟩ := List.any_eq_true.mp h
    obtain ⟨heq,hs⟩ := Bool.and_eq_true_iff.mp hp
    have h : a = v := of_decide_eq_true heq
    subst a
    exact ⟨b,(hI b).mpr hs,arcs _ hm⟩
  refine ⟨I, ⟨subset_univ _, ?_, ?_⟩, fun h => hw ((hI w).mp h)⟩
  · intro a ha b hb h
    rcases h.2 with h | h
    · exact (hpair h).1 ⟨(hI a).mp ha,(hI b).mp hb⟩
    · exact (hpair h).1 ⟨(hI b).mp hb,(hI a).mp ha⟩
  · intro a _ b _ ha hb h
    have ha' : ¬ selected M a = true := fun e => ha ((hI a).mpr e)
    have hb' : ¬ selected M b = true := fun e => hb ((hI b).mpr e)
    rcases h.2 with h | h
    · rcases ((hpair h).2.resolve_left ha').resolve_left hb' with hh | hh
      · exact .inl (hhits hh)
      · exact .inr (hhits hh)
    · rcases ((hpair h).2.resolve_left hb').resolve_left ha' with hh | hh
      · exact .inr (hhits hh)
      · exact .inl (hhits hh)

private theorem check_sound {n : ℕ} (E : List (Fin n × Fin n)) (w : Fin n) (fuel : ℕ)
    (code : List Nat) (A : List (Fin n × Fin n)) (rest : List Nat)
    (ok : check E w fuel code A = some rest) (D : Fin n → Fin n → Prop)
    (oriented : Reduction904.Orientation (edgeListGraph E) D)
    (arcs : ∀ p ∈ A, (edgeListGraph E).Adj p.1 p.2 ∧ D p.1 p.2) :
    ∃ I, Reduction904.WitnessOn (edgeListGraph E) D univ I ∧ w ∉ I := by
  classical
  induction fuel generalizing code A rest with
  | zero => simp [check] at ok
  | succ k ih =>
    cases code with
    | nil => simp [check] at ok
    | cons t ts =>
      by_cases leaf : 128 ≤ t
      · have h : leafOK E A w (t - 128) = true := by
          by_contra h
          simp [check, leaf, h] at ok
        exact leaf_sound E A w (t - 128) D arcs h
      · cases hget : E[t]? with
        | none => simp [check, leaf, hget] at ok
        | some pair =>
          obtain ⟨a,b⟩ := pair
          by_cases hab : a = b
          · simp [check, leaf, hget, hab] at ok
          have edge : (edgeListGraph E).Adj a b :=
            ⟨hab,Or.inl (List.mem_of_getElem? hget)⟩
          cases hcheck : check E w k ts ((b,a) :: A) with
          | none => simp [check, leaf, hget, hab, hcheck] at ok
          | some next =>
            have hcheck' : check E w k next ((a,b) :: A) = some rest := by
              simpa [check, leaf, hget, hab, hcheck] using ok
            by_cases dir : D a b
            · apply ih next ((a,b) :: A) rest hcheck'
              intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ⟨edge,dir⟩
              · exact arcs p hp
            · apply ih ts ((b,a) :: A) next hcheck
              intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ⟨edge.symm,(oriented b a edge.symm).mpr dir⟩
              · exact arcs p hp

private theorem certified {n : ℕ} (E : List (Fin n × Fin n)) (w : Fin n) (code : List Nat)
    (ok : check E w (E.length + 1) code [] = some []) (D : Fin n → Fin n → Prop)
    (oriented : Reduction904.Orientation (edgeListGraph E) D) :
    ∃ I, Reduction904.WitnessOn (edgeListGraph E) D univ I ∧ w ∉ I :=
  check_sound E w (E.length + 1) code [] [] ok D oriented (by simp)

end OrientationCert904

namespace Reduction904

open Finset

private def Avoidable {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n) : Prop :=
  ∀ D, Orientation G D → ∃ I, WitnessOn G D univ I ∧ w ∉ I

private theorem avoid_of_coloring {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n)
    (colorable : G.Colorable 3) : Avoidable G w := by
  classical
  intro D hor
  obtain ⟨c⟩ := colorable
  obtain ⟨K, hK, hind, h⟩ := GraphFacts.rest_bip G D hor c (c w)
    {x | c x ≠ c w} (fun _ hx => hx) (fun _ _ _ _ he => c.valid he)
  refine ⟨K.toFinset, ⟨subset_univ _, by simpa using hind, ?_⟩, ?_⟩
  · intro a _ b _ ha hb he
    have cover : c a ≠ c w ∨ c b ≠ c w := by
      by_cases e : c a = c w
      · exact Or.inr (fun e' => c.valid he (e.trans e'.symm))
      · exact Or.inl e
    rcases cover with ha' | hb'
    · obtain ⟨i,hi,hedge⟩ := h a ha' (by simpa using ha)
      exact .inl ⟨i, by simpa using hi, hedge⟩
    · obtain ⟨i,hi,hedge⟩ := h b hb' (by simpa using hb)
      exact .inr ⟨i, by simpa using hi, hedge⟩
  · intro hmem
    exact hK (Set.mem_toFinset.mp hmem) rfl

private theorem avoid_map {m n : ℕ} (G : SimpleGraph (Fin m)) (f : Fin m ↪ Fin n) (w : Fin m)
    (h : Avoidable (G.map f) (f w)) : Avoidable G w := by
  classical
  intro D oriented
  let D' : Fin n → Fin n → Prop := fun a b => ∃ x y, f x = a ∧ f y = b ∧ D x y
  have hd (x y : Fin m) : D' (f x) (f y) ↔ D x y := by
    constructor
    · rintro ⟨u,v,hu,hv,e⟩
      rwa [f.injective hu, f.injective hv] at e
    · exact fun e => ⟨x,y,rfl,rfl,e⟩
  have hor : Orientation (G.map f) D' := by
    intro a b e
    obtain ⟨x,y,hexy, rfl, rfl⟩ := (SimpleGraph.map_adj f G _ _).mp e
    simpa only [hd] using oriented x y hexy
  obtain ⟨J,⟨_,hind,hwit⟩,havoid⟩ := h D' hor
  let I := univ.filter (fun x => f x ∈ J)
  have hi (x : Fin m) : x ∈ I ↔ f x ∈ J := by simp [I]
  refine ⟨I, ⟨subset_univ _, ?_, ?_⟩, fun h => havoid ((hi w).mp h)⟩
  · intro a ha b hb he
    exact hind (f a) ((hi a).mp ha) (f b) ((hi b).mp hb) (SimpleGraph.map_adj_apply.mpr he)
  · intro a _ b _ ha hb he
    have back {x : Fin m} (hit : ∃ j ∈ J, (G.map f).Adj (f x) j ∧ D' (f x) j) :
        ∃ i ∈ I, G.Adj x i ∧ D x i := by
      obtain ⟨j,hj,edge,arc⟩ := hit
      obtain ⟨u,v,heuv,hu,rfl⟩ := (SimpleGraph.map_adj f G _ _).mp edge
      exact ⟨v, (hi v).mpr hj, (f.injective hu) ▸ heuv, (hd x v).mp arc⟩
    apply Or.imp back back
    exact hwit (f a) (mem_univ _) (f b) (mem_univ _) (mt (hi a).mpr ha) (mt (hi b).mpr hb)
      (SimpleGraph.map_adj_apply.mpr he)

private theorem avoid_relabel {n : ℕ} (G H : SimpleGraph (Fin n)) (f : Fin n → Fin n)
    (inj : Function.Injective f) (edge : ∀ a b, G.Adj a b ↔ H.Adj (f a) (f b)) (w : Fin n)
    (h : Avoidable H (f w)) : Avoidable G w := by
  let e : Fin n ↪ Fin n := ⟨f,inj⟩
  have surj : Function.Surjective f := Finite.injective_iff_surjective.mp inj
  have eq : G.map e = H := by
    ext a b
    obtain ⟨a,rfl⟩ := surj a
    obtain ⟨b,rfl⟩ := surj b
    simpa only [show f a = e a from rfl, show f b = e b from rfl, SimpleGraph.map_adj_apply] using edge a b
  exact avoid_map G e w (by rw [eq]; exact h)

end Reduction904

namespace OrientationCert904

private def arcBit (u v : Fin 13) : ℕ := 2 ^ (13*u.val+v.val)

private def markArc (n : ℕ) (a b : Fin 13) := n ||| arcBit a b

private def packedArcs (A : List (Fin 13 × Fin 13)) : ℕ :=
  A.foldr (fun e n => markArc n e.1 e.2) 0

private theorem packedBit (A : List (Fin 13 × Fin 13)) (a b : Fin 13) :
    (packedArcs A).testBit (13*a.val+b.val) = true ↔ (a,b) ∈ A := by
  induction A with
  | nil => simp [packedArcs]
  | cons e es ih =>
    obtain ⟨v,w⟩ := e
    change ((packedArcs es) ||| arcBit v w).testBit _ = true ↔ _
    simp only [Nat.testBit_or,arcBit,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,
      ih,List.mem_cons,Prod.mk.injEq]
    have h : 13 * ↑v + ↑w = 13 * ↑a + (↑b : ℕ) ↔ a = v ∧ b = w := by
      constructor
      · intro eq
        exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩
      · rintro ⟨rfl,rfl⟩; rfl
    rw [h,or_comm]

private def rowHit (n M : ℕ) (a : Fin 13) : Bool :=
  ((n >>> (13*a.val)) &&& M &&& (2^13-1)) != 0

private theorem rowHit_agrees (A : List (Fin 13 × Fin 13)) (M : ℕ) (a : Fin 13) :
    rowHit (packedArcs A) M a = hits A M a := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowHit,bne_iff_ne,hits,selected,List.any_eq_true,Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨j,hj⟩ := Nat.exists_testBit_of_ne_zero h
    simp only [Nat.testBit_and,Nat.testBit_two_pow_sub_one,Nat.testBit_shiftRight,
      Bool.and_eq_true,decide_eq_true_eq] at hj
    let b : Fin 13 := ⟨j,hj.2⟩
    exact ⟨(a,b),(packedBit A a b).mp hj.1.1,rfl,hj.1.2⟩
  · rintro ⟨⟨u,v⟩,h,eq,hv⟩ hz
    change u = a at eq
    subst u
    have bit := congrArg (fun z : ℕ => z.testBit v.val) hz
    have hm : (8191 : ℕ).testBit v.val = true := (by decide : ∀ i : Fin 13, (8191 : ℕ).testBit i.val = true) v
    simp [hm,Nat.testBit_and,Nat.testBit_shiftRight,hv,
      (packedBit A a v).mpr h] at bit

private def bLeaf (E : List (Fin 13 × Fin 13)) (n : ℕ) (w : Fin 13) (M : ℕ) : Bool :=
  !selected M w && E.all fun (a,b) =>
    !(selected M a && selected M b) &&
      (selected M a || selected M b || rowHit n M a || rowHit n M b)

private theorem bLeaf_agrees (E A : List (Fin 13 × Fin 13)) (w : Fin 13) (M : ℕ) :
    bLeaf E (packedArcs A) w M = leafOK E A w M := by
  simp only [bLeaf,leafOK,rowHit_agrees]

private def checkWords (E : List (Fin 13 × Fin 13)) (w : Fin 13) :
    ℕ → List Nat → ℕ → Option (List Nat)
  | 0, _, _ => none
  | _+1, [], _ => none
  | fuel+1, t::ts, n =>
    if 128 ≤ t then if bLeaf E n w (t-128) then some ts else none
    else do
      let (a,b) ← E[t]?
      if a=b then none else
        let rest ← checkWords E w fuel ts (markArc n b a)
        checkWords E w fuel rest (markArc n a b)

private theorem words_agree (E : List (Fin 13 × Fin 13)) (w : Fin 13) (fuel : ℕ) :
    ∀ code A, checkWords E w fuel code (packedArcs A) = check E w fuel code A := by
  induction fuel with
  | zero => intros; rfl
  | succ k ih =>
    intro code A
    cases code with
    | nil => rfl
    | cons t ts =>
      by_cases h : 128 ≤ t
      · simp [checkWords,check,h,bLeaf_agrees]
      · cases he : E[t]? with
        | none => simp [checkWords,check,h,he]
        | some xy =>
          obtain ⟨a,b⟩ := xy
          simp only [checkWords,check,h,ite_false,he]
          change (if a=b then none else _) = (if a=b then none else _)
          by_cases eq : a = b
          · simp [eq]
          · simp only [eq,ite_false]
            have pc (p q : Fin 13) : markArc (packedArcs A) p q = packedArcs ((p,q)::A) := rfl
            simp only [pc,ih]

end OrientationCert904

namespace OrientationCert904

private def bothArcs (A : List (Fin 13 × Fin 13)) := packedArcs (A ++ A.map Prod.swap)

private theorem both_spec (A : List (Fin 13 × Fin 13)) (x y : Fin 13) :
    (bothArcs A).testBit (13*x.val+y.val) = true ↔
      (x,y) ∈ A ∨ (y,x) ∈ A := by
  rw [bothArcs,packedBit,List.mem_append]
  exact or_congr Iff.rfl (List.mem_map_of_injective (a:=(y,x)) (l:=A) (f:=@Prod.swap (Fin 13) (Fin 13)) Prod.swap_injective)

private theorem packed_iso (A B : List (Fin 13 × Fin 13)) (f : Fin 13 → Fin 13)
    (hf : Function.Injective f) (h : bothArcs (A.map (Prod.map f f)) = bothArcs B) :
    ∀ x y, (edgeListGraph A).Adj x y ↔ (edgeListGraph B).Adj (f x) (f y) := by
  intro x y
  let F := Prod.map f f
  have inj : Function.Injective F := hf.prodMap hf
  have fxy : ((f x,f y) ∈ A.map F) ↔ (x,y) ∈ A := List.mem_map_of_injective (a:=(x,y)) (l:=A) inj
  have fyx : ((f y,f x) ∈ A.map F) ↔ (y,x) ∈ A := List.mem_map_of_injective (a:=(y,x)) (l:=A) inj
  have e := both_spec (A.map F) (f x) (f y)
  rw [h,both_spec,fxy,fyx] at e
  exact and_congr (not_congr hf.eq_iff.symm) e.symm

end OrientationCert904

namespace OrientationCert904

open Reduction904

private abbrev RepIndex := Fin 49
private abbrev CaseIndex := Fin 30

private def edgeDigits : ℕ → ℕ → List (Fin 13 × Fin 13)
  | 0, _ => []
  | l+1, n => (Fin.ofNat 13 (n % 16), Fin.ofNat 13 ((n >>> 4) % 16)) ::
      edgeDigits l (n >>> 8)

private def digits14 : ℕ → ℕ → List ℕ
  | 0, _ => []
  | l+1, n => n % 16384 :: digits14 l (n / 16384)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private def representative (i : RepIndex) : List (Fin 13 × Fin 13) × Fin 13 × List Nat :=
  #[(edgeDigits 23 0xc9c6c5c0bab5b4b1a5a3a2969493848280737170626150, 5, digits14 139 0x190462300055248012524801013449c823240061344012134401000384d10001492232588c000949200494920041492003c00e000401562308c96230002005509e036509e000909e0004015004109e1e08683001909e0024016003c00d6230b042a14003005909e0a1d09e002909e0024016003d09e13440d9003401542780024278001004000c13448c9641088d001488d000c0021344012134401000384d10000493232488d000849300484930040493003c00e124c00000048c92234002232409f000809f000400f036409f000809f00040100034a852a1409f004000a223409f00400090a1c09f002809f002400f0030013), (edgeDigits 23 0xc9c6c5c0bab5b4b1a5a3a2969493848280737170626150, 6, digits14 169 0x198862300075248012524800f1a0c3240a980040038683000149252480be2a1588c524801200254920041492003c000005000e00280166230a851e086830018012005988c002588c000909e4278a851a0c012005909e002909e002509e00080154278001004109e1e08683001909e0024016003c00d6230b042a14003005909e0a1d09e002909e0024016003d09e0a982870000016427800a42780094278001004000c2a1598822340072234006002551020000161a0c0041a0c00300486831a0c09f0034009003c4932a1488d002449300484930040493003c0be00080be000400e124c0002a15510124c004124c003004888d002409f004009f003c0be00080be000409f000000d0028a852a1409f004000a223409f00400090a1c09f002809f002400f0030013), (edgeDigits 23 0xc9c6c5c0bab5b4b1a5a3a2969493848280737170626150, 0, digits14 399 0x149252488001e080041080324001c3a20a98007001000e0058015524800a524800142780f84278640098000e07a0005154017000380f80014008005909e002909e00240004278002005509e000400d42782a64278800108000e0c900071e083a200382a6001c004005509e000909e00040004278009427800a005800c5800800108032410802600980b040980b04623109e003c009000c0050c900110018000002c00a001c00e005951020004200c90007003951000280160021a00300042000440164450324445000a0058007580109e002109e001c3240c90800108000e0c90007000c0004450800108000e42780084278007000c00a005800500315825248008560909e002109e001c00c1e08782524909e003000a00207821e09492002000a0a9909e002800c001c3a20e89492427800c00280080a983a207a026007a15820980015427800d0018003000000b0e880015248008427800c0028007003801600100136801904001d98862300070014a40272000500540f800440f800400f800380f8003588c6800a400055904001d98827200156230007001401302f801102f801002f800f02f800e02f800d02f800c00094925800640005558200115101540015524800400200be004401302f801002f800f02f800c02f800d02f800e00056005441a00680032410800f802f800200140030044006580001200300082000016108000e5801510002080000583240030324003800758006400054260003951004d000c04d000e002055058008000059510002000304d1600200001602f800702f8008000c00c10800be00200be001c00e001400a56095820a980be002800c001d492680198800143a200443a2003c0be00242a6001c0be00080be00040be002800c00207821e0949202f800c00280081e08782524800800282a602f800a003000700583a20a980070e880be001c0be002000a00380040000014), (edgeDigits 23 0xc9c6c5c0bab5b4b1a5a3a2969493848280737170626150, 1, digits14 387 0xb0420003240c900f802f00020024005001001120000122a143240c900f802f00020024005004468100480032c10a85000c324004400c2901a0005c00f80014b040008016290001500446400048a40680017003e00052a140020058a40005401123244d1641188c00148c900544d100408c9004c001004400619004d10018012000c00b2c10b042c1151015409c8003401520000160048b0400300090014a852a1551013449c80c90c0023240d9004088d000800700100012324006272000500340151a040161a040130048a850030009000c3240044a402324005232400305c00100c90a402c10b0422340bc00400090014b0400300122a1488d290088d001c88d00180bc0014010002400300100020980011002c00e1540550641198803e00110014a402324005005455000485500040004000455015419042c100161540012154001000100012c101340044134004000c00084d1641188c00148c9004c8c900544d100484d100400012a1413402f000500444d100404d10048a8504d001104d00100030002000c0f805c0b042c10b042324009001401229008c9001400b2a148c900248c9002c00300101700044170004000104d0b042c1088d00240052a1488d002400304d001104d00100010002003800a2c104200c900070044a85000ca4005c001123240052324003002c8c92c10a40002c4200c9000705c000b0044001232400523240030025510445000c05c0015544109c003509c00300d900540d9004c0052a140d900280d900240d9002c0030040c0029009c82c10b0402740100028006001400b2c100070c90134154055010801e823245500048006002c324001c09d004000400041340038134003000500280112a14a85027401000280032234b040c90134002801122340032234005003d11404d00140274005027400300400090008000), (edgeDigits 23 0xc9c6c5c0bab5b4b1a5a3a2969493848280737170626150, 7, digits14 131 0xa850e882a6001c00f232400b23240092a142a6003c0f8002c0f800280f800240100e882a6001c0f8002c0f800240112a142a6003c2a600444d102f800d02f800c02f800e002888d02f800f02f801002f801100240021e0868300182a6003849302f800d02f800c02f800e0028683124c00a02f800e02f800d02f800c00240011a0c28723240d900400090a1c0040a1c00300304d1002c4d1002988c4278010427800f036401503640130034a850a1c00f134409f003409f003000a223409f003c09f004000900086830a1c00c1a0c09f003009f0034009124c09f003409f003000a0004000), (edgeDigits 24 0xc7c4c1b8b6b3b1a7a5a3a096949290848373726261515040, 0, digits14 437 0x1e801e080142c80b2010807820008014004800f3250b2022d0005003c58610811a4001400f161800232504203250b201e080f800300061e08003000000222d0005003c008005000a1e08b204aa00121e08002003c5861618b201080014098026003e0007001800c003c00d161800212584962c8042000508b4001400f1258002000000800280112c80b2032508b4003c005002842010804200980c9422d000f002000c0028005100826005c00f803e04021008c9403e000f0028005000400000180080030402000c0020050b202c80586125800822d000f00280051080420108026012588b4003c008003000a001401410084021618496002000a0014002004401024c09307a01e804aa10ac00280120038c9432500bc004800e00589300040930003c00100009303250782161800a0050c94002000024c000f24c0010125811212580050040782161800a1258008044801002780050038011000817005c0c941e08014570000c32500081e085860028496002001105c001005c000f000400005c01701e08c941e080141e08011001c00100015c000304d00020170003c17000407821e0893024c040232507820050930003c00900040001e080110278005003800710080101258c9424c000f1258011027800500381120040008000c002004c93024c0c941e085860028496002001124c000f24c0010000400022d08b432504967a00c94005893000400f8001c0f8004c00e00448b4003c001000000502f00bc3250930108001424c0008004049624c04200050930002001000440bc003cc94125801102f000f00140bc0038000000401232509300040c94001493022d0005003c496100811200200101258005027800e004409e03e078224c04020050c9400144020044010570000c027800e7a015c07a0040200440100031c840028c94005809e003800413409300448496001401105c0013004009e003800803e000f00040000048782100893032508b4003c00510080141008011001c01012589300448011125800500400081e08402004009e002009e001c00e000c002001800b), (edgeDigits 24 0xc7c4c1b8b6b3b1a7a5a3a096949290848373726261515040, 1, digits14 295 0x1e805e015c05700c947a01e804aa00f802f108d000400400080120038c940028000005800800300147a0178057011c14781aa043a0012001c0034704001003400c0050b20108026009040010030014005c0106a812a843a00f802f00bc42340010000004005800c0048b20108026009042412c810c9004800700180010030014005c00f7a01e807a01780570000c00500120038c945e015c0003001432500080059e807a012a843a000c004800e24c0420098000c24c0008005001724c093032500f8003801200180160041aa0629000a22d001624c09304aa10e80030930005c930005801100080bc03e12a843a000c03e0016000c0020018012003c00b1080b206a812a80048b20005c011000817005c1aa04aa001205c001705c0016000c002002d1e043a000705c001700310c9621508d004800405c017022d00bc004800500100162c80170002c17000302410024017432588542340120010241090588542340120014004005c00000050e87a010e80031c8400298a400158a4003d0ac004800403e0c947a000f800300f8002cc94002800022d000f02f001200100164325c846a810c900318a4002800f43240096214005621400d423401200100f832508b4003c0bc004800400590c962142414aa0b203250b205e00420003c01400442410040241003400b00090c900310c90024007005d885001508d004800400000010018013), (edgeDigits 24 0xc7c4c1b8b6b3b1a7a5a3a096949290848373726261515040, 2, digits14 1079 0x78257004d00020782000c00c2c80420005078200095c02c80b2003e001200184d00904000004c00d1e08782080c170002020303e000703e0008001800d00247820008003003000f2c8042010080020050b20108040200080142c80b202c810e803e001647050c9001c241005c00100480060050260090440210090e84324001001c0061008014000c00205c0170100840243a10c9000400700184020050002000c008004c00c002801032404d01e084920020003004c93024c0930108040200095c00980017003001424c000800480067a01e8005c0b202c802410024001108001405c0008001801757002600904001005c00c002817003e00f810092a84aa028a0054002001c17000210c900310c9002400100000060058013004093024c00f803e009a1e08930100801400409300020000000c002004800605c017024c1aa04aa001243a000c05c00170014170005800300080f803e1aa024c0782100809a2c80402005008b0024000001c01005c000800140174aa001243a000c03e0016000c0020018013003c00b7a01e802c80010005daa04aa10e82c81aa047811c143240070004014000801600300122c80017003c9300449e801e084020040260003000f24c0017001417000209300058112000c002002c17005c0782108000f1e080021080402000801005c000c05c000b001400405c01701e084200040420003c170002c170003000500107821008010044800b0008003004de802c800102c8000f24c000b4aa12a81e0842000410c9001c00900052a8003c0f800300f8002c01203e07822c80420005001010812a8001c00f03e000b03e000c00100131e08260090400103e000803e00070030782000c40209040f800200f8001c00c10080030041e806a8000f24c001724c001603e001303e001203e000803e00070268003002c00200197805e017801008b202404241004c0010904014080c0030024010005c00a57015c0570024109040f84324001001c00610082030024003005c010001000c1e08782100824109052a810080f8002c0024324001001c006080c0030024010570024109040f84324001001c006004078210082030024010000c00c002801509050c9001c2414e804201008002005c782100801000542410030241002400509052a84aa0402000801510804020008017090400c090400900152a84aa028a0008015432400c4324009001800700102031e08402004020300257801e0849205c00f8001800f002000c1e08015100893005c00130020010080c009002c782124800b1008402044800b0020010080c0090008005000c00d00000117a00b20003de807a015c005c00f80018016004c00c2c80b202c810e805c00f8001801609802410004017004c00c00140102c80b202c810e805c10e8001801705c00f80018016004c00c001400f002893024c017003e0006004c93005c0402080c009044800800080f81008203002409a002000243a000c026800703e00160018013000c005002d2a84aa0b202c80241080c003002400124c0170004c00b00280174aa000643a10e82c802412c8020300240030004930002c170004d0e80018017001000c03e1e801e080142c8000f2c800104aa000624c0170004c0f8001800b2c80b207a0024105c00081e080030050b200040b20003c0090004930002c170004c0f8001800c001001600487821e082600904001098024100040f8001c0061e08003003000a1e095c04324260090400103e000600100070030782000c24109050c90018007080c00300340091e08420003c78200081700030170002c0f81e08420003d2a8001c0040a2800203e000c03e000b00187821e0878247050c9001c203005c203005400d002400f1e08002124800b000c0081008402100824105c000809040f8001c0f8002000600280050030402000c402100824109040f8001c006001400c100800305c00f80018112000c008002d3a0100824105c00f80018008002c002478000c4704001090401743242414324006005c007080c11210811e0470400100310c9001c203005c0051008002080c015044800b00200030024010004426005c00080904001108042005c1e805e0001405c001005c000f000400b002040210081707a0178000501700040170003c001002000b00087821081e801e080141e0801100080072c807820044170002c0080904010090400d0904001002426005c00080904001003000410804020008420100800203e0008002d7801e080150904010090400d0904001002426003e00080904001003028a03e000b432400903e000c001c0061e087825e015c0470426047042033240241004c492004400505c000f00100f800180011008002005c00d0030782005400b002040210082034e811e047040010030402005c0051008015002c00800407821e0817003e0006080c0021248011002c008080c001080c010080c00d00250c94aa04201008002005d0c90980b20090401409040130004402000801700300047a01e8005c10c909040170004402000801300307820050782004440200400154aa0420005c26005c0008003020300402030034203000820300040090a280f80268002002c08b0024006001c003000000e), (edgeDigits 24 0xc7c4c1b8b6b3b1a7a5a3a096949290848373726261515040, 12, digits14 377 0xe801e080142c804201e08002005000f32507820050c9400209301080782000801424c000822d04201e0800200508b40020005003c00b1e08b2010800141e08002003c782108042003e0007001800f1e08002125893022d0005003c4960008008002c0112c80b201008002004493024c040204484960014008004400205c00f803e093010800c9023c004023c003001c00503e000e05c00080004000001893032508b4003c005100801105c01120278203061c005023c0070000006000c0080008013002c402100817003e00f80904241061c08f001c00500100010000006002c40224c093004480110008170044809e080c187023c00700140000018002004c00b000c402005400810080170904420100800205c00f8001800b09040170020241000020304480f802f0004027800200184960014112027800602780050038203005c2030054008080c000000c00900500102c80b20098017000207821008010000cb20005c011000893024c049604480101258005044826005c0008080c003000009e001400e24c001724c00160044002002c17005c0402080c112027800500202030000009000c1701008112080c187023c007001400000202030448008080c0000024003002c170005800205c0017004c24105c00080904000080c1871e08260004009e00380bc001008f00000070014260003c4020008170080c187023c00700140001008112080c187023c0070014000002c002002020305c011202780050008008080c00000240030004260090400103e000803e00070980203061c00500040f800200f8001c203061c00502780080278007000800309800f8002024100040f80324001001c26003e0008080c001080c00209800f800201870008187000400503e008f000408f0008007000c000001800c), (edgeDigits 24 0x87c9c6c5c0bab5b4b1a5a3a2969493848280737170626150, 0, digits14 361 0x1582462800d5440008544001715401700c90134002800200395821e080161540017154000807a1582462800d0004170005c170002000e000c01556091140021114001d114005c3240c907820e8800e0c900170c90007000c00044511141e083a20039114005d1140021114001c013000c00a005800c66209c807a00110055510427800d15400f8427800100340f80c903240e889c803e001103e00100019988002509e003c0030000170002d09e003509e003017000280010038015002188c427800f2c1188c427800f0024324623109e003c0090044016001c0055609492427800c00215825248008427800c001c7821e09492427800c00280081e08782524800800282a6427800a00300070e883a2524909e003000a00202a60e881e807a0b042c1188c00240050a9801142780100a9800f427800d0018000002c3a20005492002109e003000a001c00e00580041c003240030550002c550002958207a01aa000400d5440017544000827201e80044550005c5500020015000c1e806a800105c000805c00170038b04641198827200156410017004d904001c00304d013466209c80054134005c1340020134001c003000001007a01340020134001c134005c0110009988272001507a00115609510005d98800349c862300be004000200541e802f800200441e802f8001003800754400f802f8001003455003e00be000400d00540f802f80010038008001558256082a602f800a003000752482a66621904005c3a200443a2003c0be00242a6001c0be00080be000400002f800a00300081e0878252480be003000a00207821e09492002000a0a980be002800c001c0160e882a602f800a001c17003e000502f8001002000e0010014), (edgeDigits 24 0x87c9c6c5c0bab5b4b1a5a3a2969493848280737170626150, 6, digits14 675 0xb0454415100c9001400399044450010003000b2c100022a1598846283a2005000f641198846283a2005000f0014017641188c42782a6005000f0014007002ca8500080032c10a850e8800f2c100072a14002000c0160c915825440008544001756091140021114005d114001c00c0c900160c90014002c3240008011560949200206830059582427800842780070a980160a9801400302a65609492002158242780084278007003000b0a980160a980140a980020a9800100380045441510124c3a22a1449300484930040493003c00b0e8800154400080038013000d1144450a85027c010027c00f44500084450007004c00300315105440493004c00304d000e04d000c005151054404930e88a85124c012124c010124c00f002d51000200be000400e004c003445109e2a1409f004009f003c01342780084278007000c0be000400c5441510124c013000c0be00380be00300140015492124d9042c100162a14003124c012124c010124c00f02f8001003801342799885608b042a140030058015027c01042780082a14006027c00f427800702f8001004c00c5248493004c0be00380be0030014001000a662198822340130019988662088d1a0c012223400d223400c004c006662000506a8014004588c223401362319040c903241a0c49300282a6003800b0010016623000502f8002223400d223400c02f8001004c0be0050011001d18a4628683027c00d027c00c004c0064628005462800406a801442799042c103240044016427800502f8002027c00c427800402f8001004c0be0050007003c0091e095105440683004c00356094920020004002c78200043a2662188c2a14013001d582662188c2a14013001c00d0049582462909e0a1c013001c00d003c00b0e8800100387820c906830010683000c3a2000400e005868364115100041510004998862300075248012524800f00106830058683004c00b1a0c001001990444500100c90016641109e004109e003c2870058287004c0040a1d9044450010641109e004109e003c004002c2870058287004c28700082870004003003151054401340e88134005c1340020134001c003005000e52494920e880be00200be001c0140038004544151004d001400384930010493000c013544151004d03a204d001704d000804d0007027c001000c014003949266219042c10a85000c0160055492004909e004109e003c00e027c00100115105440134005000e027c004027c003004c00d4450134560878200583a20038134005c1340020134001c09f0004003005109e560878200583a200380be00200be001c09f0004014001111404d0014027c004027c003004c00c002998866201aa0050011623188c0c900be00140be0010014004588c003588c003088d004c00746281aa005109e6410b04005832400440be001409f000909e00300be001009f0004014027c013001c00f66215821a0cb042c111144278004004000a2a14003027c00100300160049988003588c623032402f800502f80040044014001c88d004c88d000918a56086830c901340028287000c00c005918a00341aa00141aa001001442795821a0c016427800d427800c02f80040050007027c002027c001027c013003c0060024000), (edgeDigits 24 0x87c9c6c5c0bab5b4b1a5a3a2969493848280737170626150, 1, digits14 879 0xb802c100072c100172e00a852a155101540015004000a005ca85001c00327205c000489c82501904544001025000152720005000c00115404d12721510154001527200050004a85001c002000c012005c00b0e80324001c324005c17003e00050c9013402f00050028002002c01127209c82721904544001025001700040015005c9c8001400f00049c827209c86410b0400580172720005003c0012c1088d000c88d0014007000832405c000a05c000b03e00050c9013400280bc001400200440092c10b04154013402f000500080100028a85000c8c92324b042c10170002801023240052324003000400f2c10b0404d000a004088d001488d000c00200243a00c900170c9000707a0324005c324001c0f802f00020014009004455013441e800345500020002250017003e0005004455000419042c100161541114427009d004c00500300100008001154158066201e8004400d170001515400080008550005c01223244d1641188c00144d100408c900548c9004c00100444d10048003002c0060c90b042a149c827208c92a1551005c00151a040130048010003ca850030001232400600240030c900112c109c823240060024a8527208c90018009000c32400440052c10a8522349c82720a8544501340050681004c012003ca850030001223400722340060040009000c324004588c2234013427198827200154270008027400c4270007004c0bc00500100c900110014002001017005c0b042a148c9002400305c0011662188c001c8c900540f8004400505c0010000400404d0b042c1088d00240052a1488d002400304d001104d0010001000200281e803e0008662198856015805440170250017000408c900140042c1000200304d1000c0130018012662000d001c9c827209c817005502c1000c13440030018007000801200541e8004417025008c900148c9000c1700045904623088d004c00505c001100081700040004005c17066219046230005001c9c815404d1000c012005417000449402324005232400305c0011641188c223401300141700044002005c17000400040020001002c00e2e019880e80324001c9c800240152e000160044b040c9032466209c800540090014011005c7801c0001700489c807a01e86410b040058007000801115405502501904662000525000151540010004400400040171700550005c012002ca852a140d90274002004000a1e015101a04a85003055000280151c00016005c01223240d90040a8522340092a1409d002809d0024010000800b000cb042c109c8272088d001c00200140090c9001105c01702c10b04232400900141700044170004000100101342c10b042234009001413400441340040004000800a2a146810048a850030a8513440122a1400c036409d0008010002800327209c8272158054404d1000c0081700015272000d001c00200489c805c01e81344008000c00225008c90364010000c9c800159042c100162720b042a140032234009001c0050008001005c1e805c01e8641111400401e8001417000541700050001000c017004400b0038a852c1032405c0550154188c232401523240131540012001000105c000e0c90007001400a0044a85000cb0405c00d9001400a0c90170036400500280112a140030040b040c901341540550623088d004c5500048004000413400381340030324001c00500280112a140034450134005109c2c1009d00281e800440bc002109c00300bc001c01402740130014a85000c010000800f23248c92c1032405c000a00448c9000d51005c001503640030040b042c1017000280100c901700028011232400300308c90014001003c88d2c1032404d000a004511404d0014004088d001400f2234003000800913440d900348c92500170004417000408c9000d904445013400500102324003000800f23240055601580662151005c094005c001023240050010b04000800c001c1e800440140039510005d510002055017009c81540b04003000707a001100385500020002154001700544d1000c012232494005c001105c00102324003641111404d001400408c9000c0025441904445001000309c807a0011154001700544d1000c012003c8c9001400d000400b0018000), (edgeDigits 21 0xb8b6b3b1a7a5a3a096949290848373726261515040, 0, digits14 161 0x1e806c8000f5e080147a0178200517820045e8072517825258008004400b5e097827251496004400b00200146c8193045c10f80018013002d420508142064c1170004c00b0020001005000f00340096c8193045c10f843e14d0725000443e000f43e000e00040000018013002d4205009420508193045c0013002c008002400100500106c81b207a015c00051b200041b20003c0090005c94570001464c001064c000f002d5c045c001045c000f004dc946c81e805e08014725000a00040006c800106c8000f72519300041930003c00b53411700041170003c0130021e80725000a6c8000f72518b4003c00b7a01c940029c94002d0f8003d0f8003801243e10f8534126045c000800410f8003d0f800380010000013001800c), (edgeDigits 21 0xb8b6b3b1a7a5a3a096949290848373726261515040, 1, digits14 177 0x193045c10f872518b4003c004001801362d117043e0006004d8b400100056c81b20640524100500090005930002d170004d0f80019c9442f000f42f000e00100127251c946c810f86c810c9001800100498b443e0012002c011003d4d043e12414324006000400f004dc9462d1b206c81b2045c10c90018013003000262d000b62d000a00050bc6405241004d08d001908d0014001004800f001193062d000543e001343e0012640588500150c9004d0c9004800172518b46c81b206c811704324006004c00c00098b4002d8b40028001003d0bc42340010048004003993062d000562140016c81930002d0f800190c9000593042f000542f00064234001001001245c10f800190c900051704905b2043e000c43e000b000c00662d0005621400145c10bc00190bc001508d000401200100130034000), (edgeDigits 21 0xb8b6b3b1a7a5a3a096949290848373726261515040, 12, digits14 77 0xe802c8000f2c800103a00b200040b20003c17003e000609040f803240000018001004c00c1e08586061c782090400c023c003001c00d00284020980241000400c00400141e082410040241003426000302410004782161800a061c00d000ce80325000b1e080113250496004400a032408f001008f000c00e032408f001008f000c00d001c009), (edgeDigits 22 0xc0b8b6b3b1a7a5a3a096949290848373726261515040, 0, digits14 171 0x1e806c8000f5e080147a01b20003d7820051e805e080145e080117a01c945e094960020011002d7825e09c945258011002c0080051b2064c117043e0006004c00b5081420508193045c0013002c0080004014003c00d00540096c8193045c10f843e1b205341c9400110f8003d0f8003800900040000018013002d420508142064c1170004c00b002000100500106c81b207a015c00051b200041b20003c0090005c94570001464c001064c000f002d5c045c001045c000f004dc946c81b207a017820051c94002800900040006c800106c8000f72519300041930003c00b53411700041170003c0130021e80725000a6c8000f72518b4003c00b7a01c940029c94002d0f8003d0f8003801243e10f843e14d04981170002001043e000f43e000e00540010000013001800c), (edgeDigits 22 0xc0b8b6b3b1a7a5a3a096949290848373726261515040, 9, digits14 145 0x1c9453415865258008000c013725000472510f843e00c90004000004dc9400110f8427800443e00c9000408f0010000004800e57014960011496000d5c043e00074278003427800457000c9001c08f001008f000c00000394d05258004525800343e109e000d09e00110f809040c9001c001023c003023c004000000e0020011090517043e00060020241000024145c000843e00060324000001c187525909e00381870000008061c00a7251496004509e003808f0000007001024109040c9001c0060030241032408f00100070024187525909e0038008061c000725117043e0006004dc94002c08f0025c940011496004509e003808f0000007000c00d), (edgeDigits 22 0xc0b8b6b3b1a7a5a3a096949290848373726261515040, 3, digits14 129 0x1e806c8000f6c800107a01b200041b20003d17049815c053400084980010498000f001c0060904241570126045c0008003c241004024100340070018001004c00c5e095865e082415e08003003000d00294024980241000400c00400147a01782005178200455c07251b2064c000b003c007570001457000130031b2024040010904014090401300402410904901080c187001401109040140904013001c0060035e80725000a5e080145e08011080c2032405b20725000b725000a0014203005020300440070018010080c1872404885001420300502030044007001800d000c009), (edgeDigits 22 0xc0b8b6b3b1a7a5a3a096949290848373726261515040, 11, digits14 107 0x17825e0942050080024a28006003800757015c0032509e023c0000010007003824109040c9001c00600357825e0909e023c0000038007000c00c50094024aa128a0008007001824109050f80324001001c006500940243e10f8023c001000128a0008007001800300300105e082410040241003526000302410005782561800a061c00d000d78257015865258008001000c5e0800357014d000215860011586000c00a032408f001008f000c00e032408f001008f000c00d001c009), (edgeDigits 22 0xc0b8b6b3b1a7a5a3a096949290848373726261515040, 4, digits14 165 0x1e805e080145e080117a0178200517820044241032408f0010007061c08f001c003002400d721158600508850905b205081402000824100300062214005090400900201870010187000c08f001c08f0000012061c2415e0940200400c900300c9002418700140080324000023c004023c003023c012001c0140035586061c08f001c00d004400a5e097825008241002401000295c0003024150814020008241003024100242410000008003542050080024a28006032400c03240090324000001d78250080105e09586002818700340094a2808f002808f0024007000d7824980241000400c5e08003561800a5e082410031782000c18700001870028187002400d4a2926009040010324006003128a000c08f002808f002408f0000007001000e), (edgeDigits 22 0xc0b8b6b3b1a7a5a3a096949290848373726261515040, 2, digits14 185 0x142049802415e094020040003000400c500926009040010031402000c0025e082410040241003526000302410005782080c010080c00d000c0095e097826c8140200502416c8024100500c90004006002400a00415c009050f80324001001801000317825e094024aa10f843e1b2003240130004000003128a000940200500060041782080d2a843e000c022c002022c0010018010002400a000d4205008002090400c09040094aa128a00080c900300c900240065e094026c81b2043e10f86c800c9004c001000128a000800c0015402005140200440060040203022c0060024003003542050080024a280066c81420005024100040c90019420080c002080c001022c006000c009498024100040c9001926043e1b20090401409040135e080115008010001000150080024a2800649802030008203000408b0018009000c00c0038007), (edgeDigits 22 0xc0b8b6b3b1a7a5a3a096949290848373726261515040, 1, digits14 181 0x193045c10f872518b4003c004001801362d117043e0006004d8b400100056c81b20240424100500090005930002d170004d0f80019c9442f000f42f000e00100127251c946c810f86c800c9001800100498b443e0012002c011003d4d043e02410324006000400f004dc9462d1b206c8090109040c900180130030885001400262d000b62d000a00050bc2404241004c08d001808d0014001004800f001193062d000543e001343e0012240488500140c9004c0c9004800172518b46c81b2024042410324006004c00c221400500098b4002d8b40028001003d0bc02340010048004003993062d000522140016c81930002d0f800180c9000593042f000542f00060234001001001245c10f800180c900051700905b2043e000c43e000b000c00662d0005221400145c10bc00190bc001408d000401200100130034000), (edgeDigits 22 0xc0b8b6b3b1a7a5a3a096949290848373726261515040, 12, digits14 153 0xb202c8093022d0005240400000240012c80b200904241032400700180090004170090400103e00f803240000004006003001324c0c9424c0885032401300048850024885001000d000049612582410324007023c004023c003000000d02787820a28007023c00a023c009000000e00448b4325088522d00c900040132214004003400022d08b422142410324006004c08f001008f000c001000009e1e08402004008f002808f002408f001008f000c0000008011001400b2c80b200904203000c0090004930002c170004c0f80018b2024c000b05c001303e00060904203023c005000c0c90018001000058632500bc003c08f000000d1258496023c00d0000008027808f000000e0010012), (edgeDigits 23 0xcbc0b8b6b3b1a7a5a3a096949290848373726261515040, 3, digits14 131 0xe802c8000f5e080143a0178200517820044901080c187001401109040140904013240488500142030050203004400300340092c80b202404241004c00900054025080241000400900500102c80c943a00c942404203061c005004400d00240002c800102c8000f001926049815c00905782080c009000c00d4980010498000f001c006005117049815c053400084980010498000f001c006004ce802c8000f2c800102404c943251782561800a004400f0018901004090100340095701782000c241004024100340140904241570126045c0008003c241004024100340070018013000400c), (edgeDigits 23 0xcbc0b8b6b3b1a7a5a3a096949290848373726261515040, 0, digits14 269 0xe802c8000f5e080145e0978243e109e000d09e001000e001ce805e080145e080115e097825258008002ce8032517825258008004400b00597825e0949632500165258011002c0080050b2050810f842f0004002cb2024c117043e0006004c00b00580015081420508117024c001645c0013002c0080004014003c00d00540092c80b20508142045c0008002cb2024c117043e14d0325000443e000f43e000e0000006004c00b005800900054205009420508117024c001645c0013002c0080024001005001049815c03a00c94002c016570001457000134980010498000f000526057015c043e109e2c8128a3a000164a28012002528a004509e002d09e0028000001000e001c001498000f49800105e0978242794024a2909e002d09e0028009000000e001d40200400030008b2024c000b45c00135340c943a017820050c940028000325000b00594d0004d17045c1402444800b0008003004117045c140250091702c80930002c0160055170004c009000c002003c00100210f843e10f8534126045c000800410f8003d0f8003801500040003a00c940028b20003cc9422d000f002ce80325000a325000b43e000f43e000e004801643e10f843e14d04981170002001043e000f43e000e00540010000013001800c), (edgeDigits 23 0xcbc0b8b6b3b1a7a5a3a096949290848373726261515040, 2, digits14 115 0xe802c8000f5e080143a0178200457820050b202c812a843e000b00480062404001090401409040132404b2043e0b204aa001243e000b2c8000f00100060904001004c2030050203004400300340092c80b202404241004c00900054025080241000400900500102c80930002d170004cb202404009090401409040130004b202c810f83a00b200040b20003c0162404000002400124c09302c815c0090400d5e08003090401000509010024001000000b43e10f80324000000401243e10f803240000004013001800c), (edgeDigits 23 0xcbc0b8b6b3b1a7a5a3a096949290848373726261515040, 1, digits14 199 0x93045c10f832508b4003c004001801322d117043e0006004c8b4001000532510f8003d0f80039170004d0f80018c9442f000f42f000e001001232510f850810f800310f8002c0013250b2043e0b200324006000401222d10f8004800b0044016003d4d043e02410324006000400f004cc9432508b424042410904b20032400c43e000b0324009001c006004c8850014001003cc9442f12a84aa10bc2404241004c08d0018015003000242f000b42f000a0234005000400f00480110010c9422d09012214005000400f43e00c9000401343e00c9000401232508b424042410904b20032400c43e000b0324009001c006004c8850014001003d0bc02340010048004003893022d000522140012c80930002d0f800180c9000493042f000542f00060234001001001245c10f800180c900051700904b2043e000c43e000b000c00622d0005221400145c10bc00190bc001408d000401200100130034000), (edgeDigits 23 0xcbc0b8b6b3b1a7a5a3a096949290848373726261515040, 12, digits14 95 0xb2024c000b05c00132c8090100241700904000004c4200904009090400c0904000005000124c08b400140f8004c0f80048e80325000b325000a22140f80324001004c00d1e08782023c00d0024586023c00d002801124c08b40014901221400500040f80324001004c01003e00c90004012000000632504960044c941258011221408f004408f004800d0000c9422d000f02780123250885003408f004808f00440000038004), (edgeDigits 22 0xc1b8b6b3b1a7a5a3a096949290848373726261515040, 6, digits14 163 0x1e80725000b725000a7a01c94002dc9400292a80a28002027800b027800a027800402780030a290bc0278002002c08f002808f002408f001008f000c000004800e1e084021e08782023c00700380090040496027808f000000e00280117a01b20004078200447820051c946c800106c8000f6214005061c014061c011061c004061c00300299016214005061c014061c011061c004061c0030025e806c8000f725000a725000b1e0828a003808f002808f00240117a01c94002c782004428a003808f002808f00240126c81c9462d000f002d88500298850025e801e080140a2800e023c00a023c00900487820a2800e023c00a023c00900440007250496004409e003808f00000041e0808f002808f002409e003808f0000003001c00d), (edgeDigits 22 0xc1b8b6b3b1a7a5a3a096949290848373726261515040, 3, digits14 129 0x1e806c8000f6c800107a01b200041b20003d17049815c053400084980010498000f001c0064905241570126045c0008003d241004124100340070018001004c00c1e085861e092411e08003003000d00284024981241000400c00400147a00782005078200455c07251b2064c000b003c007570001457000130031b2064040014904014490401300412414905901080c187001401149040144904013001c0060035e80725000a1e080141e08011080c2036405b20725000b725000a0014203005020300440070018010080c1876405885001420300502030044007001800d000c009), (edgeDigits 22 0xc1b8b6b3b1a7a5a3a096949290848373726261515040, 0, digits14 161 0x1e806c8000f1e080147a0078200507820045e8072507821258008004400b1e087827250496004400b00200146c8193045c10f80018013002d420508142064c1170004c00b0020001005000f00340096c8193045c10f843e14d0725000443e000f43e000e00040000018013002d4201009420508193045c0013002c008002400100500106c81b207a015c00051b200041b20003c0090005c94570001464c001064c000f002d5c045c001045c000f004dc946c81e801e08014725000a00040006c800106c8000f72519300041930003c00b53411700041170003c0130021e80725000a6c8000f72518b4003c00b7a01c940029c94002d0f8003d0f8003801243e10f8534126045c000800410f8003d0f800380010000013001800c), (edgeDigits 22 0xc1b8b6b3b1a7a5a3a096949290848373726261515040, 1, digits14 81 0x1e80725000a725000b7a01c940029c94002d0f843e10c9000400042f10bc4234001000000400380126c8142049812416c810f80048006000400c00518b443e10bc0010012002c00f6c81170002d17000310f86c810f8002d0f800310bc00480040019e806c8000f6c800105e01420003d420004001449052414324007001800949050f84324000001800c0004013), (edgeDigits 22 0xc1b8b6b3b1a7a5a3a096949290848373726261515040, 2, digits14 185 0x142049812411e084020040003000400c100926049040010030402000c0021e092410041241003526000312410004782080c010080c00d000c0091e087826c8040200512416c8124100510c90004006002400a00415c049050f84324001001801000307821e084024aa10f843e1b2043240130004000003028a000840200500060040782080d2a843e000c022c002022c0010018010002400a000d4201008002490400c49040094aa028a00090c900310c900240061e084026c81b2043e10f86c810c9004c001000028a000800c0014402005040200440060040203022c0060024003003542010080020a280066c81420005124100050c90019420080c002080c001022c006000c009498124100050c9001926043e1b201e0801449040131e080111008010001000110080020a2800649802030008203000408b0018009000c00c0038007), (edgeDigits 22 0xc1b8b6b3b1a7a5a3a096949290848373726261515040, 4, digits14 181 0x142049812416c812410051241004c003000400c100926049040010030402000c0026c81420005126000312410005420498000c080c002080c001000c0096c81b2050812a80a287824904010432400d023c004023c0030024002001c0146c8126043a10e80a2808f00240030008007005000c002db206c80782100801049050c91e084020040003001c00c002c0146405241432408f000c00700500090005b2050812a80a29b201e0924100410c9003400b023c004023c0030024002001c01449810e8001c00c50804020009241003124100252a80a28002432400c4324009001c001004d42010080024aa000749812601008002000d0e8001d2411e0840200400034324007000400c50807824904010490400d023c000080c00300092a8001d2604980203000c00243a00070031241080c003023c00700040090048006), (edgeDigits 22 0xc1b8b6b3b1a7a5a3a096949290848373726261515040, 5, digits14 181 0x1c9472507821e08203061c00500340091e080025340008125800a1258003570124100350d800210d8001c09e000c00e004400f7251c9472507821e090c9001c08f000c00e125808f003800a0054011003d88549050c9001c08f000c011003400072507821e08203061c00500340091e080025340008125800a125800300450d8027800300395c05340008432400e432400d1618496002008f003808f0034003000001253405861258008000d0d8161809e002009e001c0034324782161800a023c007000c00000394d0061c782023c00a023c009001d24100044960020003436018702780080278007000c00e4324187023c007000c000003401316181877250496004408f000000700344961258187023c00700340000021c94027801102780121e095c049040100030782000c5860028187003408f001c0000038004), (edgeDigits 22 0xc1b8b6b3b1a7a5a3a096949290848373726261515040, 12, digits14 103 0xe802c80b202404b20325000b001400100240101e0840209042411e0808f00380070018203000c00900400111e084020904203000c00900400143250b20240400932500050040496027808f000000e0044586100820300240101618005005000a090417003e000600202410000782061c00a061c009000c187125809e0038008061c000001024105c000803e000603240001e0808f002808f002409e003808f00000033250496004409e003808f0000004001c00d), (edgeDigits 23 0xc4c1b8b6b3b1a7a5a3a096949290848373726261515040, 6, digits14 317 0x1e806c8000f6c800107a01b200041b20003de803251b2022d0005003c00a7a01c84125809e003808f000000d00287821618187023c007003400a00540116c81b203251885003400a0015b206c81c84621400d002800510084021618187003400a0014402000c0150044010004c00c5e0158450811851618c9412580110021420003d08d00100070019185001400d002878216181873251885000008f004808f004408f001008f000c007003400a005542050814205611185003400a00144021008586061c00d00280051008003005400c00400145081b206c81e80721000a64040106c8000f640400d004800650800147a01b20004188500354200051c84621400d4690014002800500319016405e80721000a6404010640400d004800648040146215e804aa009e002c00e721000a621400d4614004023c0000049185005000500047827a0190100407820050782004400c1e08003325190100405860050586004400a64041870050187004400d7a01b200040c94002cc940010782000c78200507820044c94161801416180110029885061c014061c01100340050055e805e000143250496004400a7a017805081201508142022d009e004400b002009e000d885000000500040100050c94027808f0000011002908d001108d004800e62152014614005005108d004800d7a00c94002cc940028782125800a0045e80325000b325000a023c012023c0110039885080c1870014014023c012023c011023c004023c0030034015001c009), (edgeDigits 23 0xc4c1b8b6b3b1a7a5a3a096949290848373726261515040, 0, digits14 295 0x1e8032507821258008004400b6c81b206c81b2024c017003e0006004c016002c009000400f6c81b2024c017003e00f81340c9400100f8003c0f800380010000006004c016002c0101e087823250496004400b00214205081420508142024c0170004c016002c0080024001003d4205081420508142024c0170004c016002c008002400100400146c812600051260004de8057001706c807823250496004400a00240000020782000c0146c800106c8000f6c81e8057000146c800106c8000f0024c945700c94002001424c001024c000f005800b57012600041260003c17057004d000201700040170003c0000058013000526049812601009b2043a00f80058012498001449800130024015000c0027a01b200041b20003de80721000a6c8000f32508b4003c016002de80721000a43a000f43a000e7a00c940028c94002c0f8003c0f8003801600495c0498001043a000f03e04d04980170002001003e000f03e000e0000016004c0017a01c840029b20003d0e87a01c8400290e8003d0e8003800100490e8570126000410e8003d0e80038001004c0f87a00c94002cc9400284d07a007820044c94002cc940028004004c0f8003c0f8003800003e00f857004d00021e801e08011325000b325000a001000100000f8003c0f8003809e1e085861258008002828a0038782161800a1258008027800e002c000000c0020058007001800c), (edgeDigits 23 0xc4c1b8b6b3b1a7a5a3a096949290848373726261515040, 3, digits14 153 0x1e8032507821258008004400b6c81b206c81b2024c0170325078200441700020006490400d004c016002c009000400f6c81b206405241004c00100240101e087823250496004400b002142050817801e08015490400d0024001003d4205081241000400900400146c81e807a00c94005800b6c800106c8000f001926049815c049047821e08c941258011002c008000c00d4980010498000f001c006005126049815c057004d000580084980010498000f001c006004de806c8000f6c8001064059017a01b206c80930005800b003d90100419010034012001800957015c01e08015000d2410041241003401457015c04905260498017000580080018003003d24100412410034013000400c), (edgeDigits 23 0xc4c1b8b6b3b1a7a5a3a096949290848373726261515040, 2, digits14 155 0x1e807a01e8032407827a0017003e0006490400100340071340008004c009005800b6c81b206c81b2024c017003e0006004c016002c009000400f6c81b206405241004c00100240101e087825e00c901340013005800b002142050817801e08015490400d0024001003d4205081241000400900400146c812600051260004d260498126010082030024015000c00203e00f843a028a022c00900540030008007001924149047821e080f86c807820051241004c7820044004100800200380071008010080c009005400349052411e0840200402030024015000d0c943240f81e087826c80930002d0c9004d0c9004840200440f8003c01000280f800380000a28002022c0090054003001c006000400c), (edgeDigits 23 0xc4c1b8b6b3b1a7a5a3a096949290848373726261515040, 1, digits14 193 0x1e807a00c9413400f80038c940010013005800b6c81b206405241004c00900040106c81b2024c017003e0006004c016002c00f50814204aa1b2003e17805e0178032510c95e0093003e00130058015004400d00240085080010508000f000c00b00092a800480070019780508000f508001049052414325780508142003e0c9450808b400590c9004d0c90048011000800b002000f4904010490400d000c007001800900040146c812600051260004d26049812606c810e803e001600492600051260004c015000c00203e00f843a1b2024c08b4001401643a001343a0012005400300080070019b2064040094904014490401349052417a01b20003db20004190143240f800590c9000001200252410051241004c015000d0c94325b206c81b2032508b4003c016490400d002c014640590124c08b4001401664040000050009432401343240120054003001c006000400c), (edgeDigits 23 0xc4c1b8b6b3b1a7a5a3a096949290848373726261515040, 5, digits14 285 0x1e8032507821258008004400b7a01e801e080150045e807a0078200540116405901080c1870014015004590100052414904187023c00700540034904001004c00d002400f6c019011e08782432409e023c000000c28a000800e001cc94002cc940010c94002988500340050025b0010080156405241004d24149042031e08496002808f003408f0038005023c002023c001001c0064904013080c003005400900440107a00c947a00782161800a0054011003de807a0124149050c9001c0061e0800300540116405901080c1870014015004590100040090035b006c0040249052411008496023c00d00290c900050c9003800700180051008003005401164059014905241080d5c01258004023c00d023c00e001408f00080070018203000c0150045901000400900415c05701e80325000a1e08011005400349052411e081870024782027808f000000e023c009001c015000d241000400d49052416c004021009b00325008f003400a001c006001440200440034904203080c5861258008023c00e023c00d023c0020018007000c00900552410004010004c00c5e015845e01241003000d002878216181871e09241003008f000c007003400a0055400100801549052411008015000c00c00417801e080155610586005400a4905241080c015000c0104905241080c003005400d0024014), (edgeDigits 23 0xc4c1b8b6b3b1a7a5a3a096949290848373726261515040, 7, digits14 421 0x1e8032507821258008004400b1e08c9412580110029e80325009e023c000004400a4aa009e023c00000280120038c9432500bc0278002004800e125809e1e0808f00280f800200f8001c09e000808f001008f000c0000038011002c0106a808b422d0496027800e004400200292a802f0c94325008f00340001258011027800e000800a00488b422d0496027800e000801102f0c9432500f8023c004023c00300340001258011027800e0008012002c00f1e087823250496004400b00207823250496004400a7a00c94027808f000001100292a8027808f000000a004800e3250c9402f009e000801200384960278782023c00a03e000803e00070278002023c004023c003000000e004400b0041aa022d08b4125809e0038011000800a4aa00bc1618c94325008f00340001258011002009e003800200292a8001801222d08b4125809e003801100080bc3250c9403e008f000c08f001000d0000496004409e0038002004800b003c0145700586125809e02f15c0325008f004808f0044010027800b027800a03e0006061c0050008000003800800111c1061c496027800e061c00000200040034586125809e1e08c94002cc94002808f004808f00440000038008061c496027800e0020187000000d000d5c0161849600200044324c941258011023c000001000d03e009e023c000001000e325078243a000f1258008325000a004cc940010496004409e00385861258008023c00d023c00e000000303e00f8027808f00000030008006001d5c016184960278c94023c012023c011061c005000000e00200044704187125809e0038008061c000001000d16184960278782325000b325000a023c012023c011000000e0020187125809e0038008061c00000340035700586125800800110c93250496004408f000000400340f8027808f00000040038c9416190c900344960020c94002801332500041258011027800e1618496002008f003408f0038000000d0c903e009e000808f00000030018007000400c), (edgeDigits 23 0xc4c1b8b6b3b1a7a5a3a096949290848373726261515040, 12, digits14 387 0x420108017005c0c94125801105c001005c000f0004000002c008100840205c01700904496027800e00100010000496027800e000c00b002000210802600980187027808f000000700142410034004080c003000842005c0b201e080111008010001000205c000b1080170002c1120278005080c0000008003002024105c0496027800e00100080904000080c496027800e0020203000000300040092c80b20098017000207821008010000c011000893024c0496027800e004400224c0016002c17005c0402080c112027800500202030000009000c17010082030024496027800e0020003002c1700058002004c2412c80930002c4020008203002400305c0496027800e000c00824c08b432500f8003c0f800380bc0010012001401605c01701008203002411202780050020170005800300080130904203061c08f001c005000c000000400c24c09301e0809e023c0000028402004001124c0496027800e004400b24c001600088b422d07820a2800e027808f000000a00448b4125809e0038011002c8b4005800200140f803e0203061c005027800802780070278011080c187001408f001c000000c0022c800f8002c8b40014c9402780110980b20023c01103e000b0020203000c187001408f001c0000008c942c80b20023c01100080f8002cc94002800022d000f0058004004cb2032508b4003c00b1e08782125849603e000f1258002000000b0020402100893005c0013044849600140021008015002c008004001132508b4003c496027800e023c000004400a09040f802f009e000800400202410000203125809e0038008080c000000c0f802f009e0008004032400003e00bc001009e000808f0000003001c00900040f802f000403e009e001009e000c00203e00f8023c00300080bc023c00200100c9023c004023c00300040000048006), (edgeDigits 23 0xc5c1b8b6b3b1a7a5a3a096949290848373726261515040, 3, digits14 263 0x1e80725000b725000a7a01c94002dc940029e802c809307250005002c0105e01400490400900407821009241080c003002401000540147250b2064040090041c9400155845001241002401056100051618586100820300240101618005001c015005000a004800e7a01e806c0190149040130024010003978050012410024010005078210092411e099012c80016640400149040144904013001c006080c00300240100055c947251c946c01901002401072500055611400490400900415840014014004800e1618402080c0090040586001401500280117a01e802c80016003db002c8001600417801e080151080402000801000512414905e807a00b20005800f6c00b200058010001c0064904014490401300319012c81e80725000b2c800102c8000f00180166404001490401349040140025e80725190149040136214005000000a5e0124100300146c01b0062140050029400490400c00500106405885001524100500091e087827a01c942c8000f00287820050782004400e001cb20100801410080110041901080c014080c01100247821e09e80621400a1e080141e08011003800710084022c8188500284020050402004400700180106214187005018700440090014015000c00d), (edgeDigits 23 0xc5c1b8b6b3b1a7a5a3a096949290848373726261515040, 0, digits14 279 0x1e80725000b725000a7a01c940029c94002d0d84a200bc027800200290d800310d8002c00003e00f87a007820050b2000402a800180f800300f8002c00100000160aa00bc002c0bc002828a027800b027800a0008004004800e7a01e807a01780436109c2c8028a027800a00090d80018000001000c00500120039b005001b006c010d803e00f810080030008000004800600300140040b201080b202c800f8001801200300140059c9422d001602f1c9403e00bc0010016027800e0008012002c00f53407827250496004400a00014d0002d4d000310d87a007820051b00500001400410d800310d8002c00003e1e801e080142c80420005001003e000c03e000b00040160039e801e08011725000b725000a7a01c941e08b20004028a00080000045c94002dc9400282a802f000b02f000a0a2809e002c09e0028002004800e00114d05341e807a01b005000014004000a534000c534000b00340004361e806c00010108028a027800a00092880018012436000c436000b000000e7251e802c80b201e0828a0038011000800c725000b725000a0001c947251e800aa1e801e08011000800c725000b725000a003400042702a80a28002427000b427000a000000e00480042c8017003e0006002c42000502600030b20108001405c000c05c000b0020016003c013), (edgeDigits 23 0xc5c1b8b6b3b1a7a5a3a096949290848373726261515040, 2, digits14 201 0x1e80724000b6c00b20005991024c0016002c0101e08782724000b00215c057012410034782000dc90002c0080030420100800249042600059241000400c4905241080c015000c00900400147a017805701241003400c0051b00500124100300140040b2010802602c80b2003e0012001800100300140059c90724191024c10c96404402098000c1008003640400972400080014004000800043600060038012644191043600f803e10c9644040200519100020004000c0020000006004801024c093003e00060048016002c00f10804024904b2005c000b0058009000924105c001600310d87a01b00004128849050c9001c00900490d800310d8002c004432442010080020aa028a0008007432400c4324009001000003e0b200aa001203e000c03e000b00100160019e807a00b20005800f5e0078200540146c00b2000584201008002005001049052414324007001800949052414324007001800c0004013), (edgeDigits 23 0xc5c1b8b6b3b1a7a5a3a096949290848373726261515040, 1, digits14 165 0x1e80725000a725000b7a01c940029c94002d0d803e001643240f800590c9000400042700bc005908d02f00164234001000000400380127a01e807a0178049050d8001800c00500120039b00500124100300140040b2010802602c80b2003e0012001800100300140059c9422d001602f19106405c94432400e4234004001400024c001672510d800380f800580060008012002c00f1081b0049040092c8001645412414905885423401200140040000170005800b000924105c001600310d8725109c00480044325c94621400d4234012001000003e0b2003e000b03e000c02f001200100160019e807a00b20005800f6c00b2000580105e017801080016003d4001080016004001449052414324007001800949052414324007001800c0004013), (edgeDigits 23 0xc5c1b8b6b3b1a7a5a3a096949290848373726261515040, 12, digits14 251 0x93024c0402100828a023c00a001c006080c203023c007001800924c0016004400222d08b41e0828a003809e002c09e002809e001009e000c011000800505c01701008203002400300080f803e0402080c0090278007000c0020018c9412581701e0858600280bc00200bc001c00622d00050278002003801122d08b4125809e0038011000800f001001324c026009041872c800bc002c08f0024007000c00105c00080014170004c0f80018c94125801102f000f02f000e0010260090400105c000803e00061e085860028496002009e00380030980241000409e0018782000c586002809e0014496002009e0038004000801210802600904203061c08f001c005000c00100304020980241000400c100800300084200980260061c08f001c005001017005c0187023c007001400405c000b0020002098000c09040011080260003020300042030008003002426003e00080904203061c005000c00109800f800202410004203061c005000c00203e00f8023c00300080c9023c00300040072c80930002c8b400140bc00485861e080f80030782000c5860028008061c00d023c0070008241080c003061c005023c00700040040018000)][i.val]!

set_option maxRecDepth 30000 in
private def caseEdges (i : CaseIndex) : List (Fin 13 × Fin 13) :=
  #[edgeDigits 23 0xc9c8c4bab7b4a6a2959286817571656353434030212010, edgeDigits 23 0xc7c6c4b8b5b4a8a6a39795938272656151434030212010, edgeDigits 24 0xc8c6c2b7b5b2a6a4a1989390878475746563534130212010, edgeDigits 24 0xc7c6c2b8b5b2a8a6a1979591878474656353434030212010, edgeDigits 24 0xc7c6c4b8b5b4a8a6a3979593878272656151434030212010, edgeDigits 21 0xb6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc0b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc1b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc2b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc3b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xc3c2b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc4b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xc4c1b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc5b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xc5c0b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc6b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc7b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc8b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xc8c7b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xc9b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xc9c6b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xc9c8b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xcab6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xcac6b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xcac7b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xcac9b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 22 0xcbb6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xcbc6b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xcbc7b6b5b4a7a5a3989492838172706160545342312010, edgeDigits 23 0xcbc8b6b5b4a7a5a3989492838172706160545342312010][i.val]!

private def planFields (i : CaseIndex) : ℕ :=
  #[0xc85af142a1e51e104ca5832e9443126cb508a974873241960cab510c8572d825e2921c508da432e9433216bc50a8794784132960cba50cc496f181e6a11e08c51a432ad433126cb508a974873241960cab50cc8572d825e2921c508da432e9413216bc50a8794784132960cba504c8572d825e2921c508da432e9420652bc13a9784784312ba0596c0019472c8e1e6921c490ee815a7010652bc13a9784784312ba0596c04c85af142a1e51e104ca5832e940, 0x50d61d82e6b08508e1da6e8314314367850ca9b241327896ba0c50c4d15e1826f2888c51e1a6ac314313468750acb9232418796ab0c50c50d9e1432a6c904c9e25ae8314413468750acb9232418796ab0c51050d61d82e6b08508e1da6e8314114367850ca9b241327896ba0c504194e1d06a6f08490e1ee9a4170106547831cb9a2431278ba9605c0450d61d82e6b08508e1da6e8314206547831cb9a2431278ba9605c0050d9e1432a6c904c9e25ae83140, 0x305cea02d924971609e900e46d88c317925a80b64c25849160b7a31f1cc6d92496a0320946dcda92407c173a80b64925c5827a40391b61f1cc6d92496a0320946dcda92406c054961b83a27c528407a9316b170c5e496a02d93096124582de8c6c173a80b64925c5827a40391b6170c5e496a02d93096124582de8c5c405a27961b83c2851649b073a1705cea02d924971609e900e46d86c540b83a27961c852731ba6409171cc6d92496a0320946dcda92405, 0x1196049ceae7004d0a5aeb15e00b456712839cab0312469abc57802d195c860f26e81084da6eb161c0b45682173bac90243196abc58702d195c860f26e81084da6eb161c0a45682173bac90243196abc587028e1d48592e7280904ee9a5721c0a37862154cab904231ab965c87028c8561d82e6b10508e1da432e94942176580c9ab341236987c0ba52421c59492a72cc850eea1d41a70a07826514cba934321ab875096c29195c860f26e81084da6eb161c09, 0x9960d1c6ae7004d0a5ae9e3140b256734819cab0312469ab78c502c995d0e0726e81084da6ea1f140b25684371bac90243196ab87c502c995d0e0726e81084da6ea1f140a25684371bac90243196ab87c502861d50d8ae7280904ee9a61d700a17864352cab904231ab96875c02821cd950aa72c4850eea1da5430a07846532cba914321ab879650c2850d61d82e6b08508e1da6e8314924376580c9ab141236987bac0524995d0e0726e81084da6ea1f1409, 0x31486e4dd92283205c952cdaa40ec512a846739b0c182745b639a0371486e4dd92283205c952cdaa40dc2157648a0b93c241587960ba33704959ce6c2a1310945e241aaccdc2519b0a84673c758412a30b9637054a282e4dd9315d208680e6d8dc034682ab1975c45271809a63b3304959ce6c2a1310945e241aacccc2157648a0b93c241587960ba3330d02ac65d5a0b1e14508eac1a4cc430ba2865791c8715243ba609331486e4dd92283205c952cdaa40c, 0x31486e4dd92283205c952cdaa416c512a846739b0c182745b639a0571486e4dd92283205c952cdaa415c512a846739b0c182745b639a0531486e4dd92283205c952cdaa414c512a846739b0c182745b639a04f1486e4dd92283205c952cdaa413c521b937648a0c817254b36a904b1486e4dd92283205c952cdaa411c512a846739b0c182745b639a047144aa119ce6c30609d16d8e6810c521b937648a0c817254b36a90431486e4dd92283205c952cdaa40f, 0x310c2e8a195e4721c5490ee98256c403975682ab1c1284756b930a57100e5d5a0aac704a11d5ae4c294c430ba2865791c8715243ba60957100e5d5a0aac704a11d5ae4c293c430ba2865791c8715243ba6095310c2e8a195e4721c5490ee98253c430ba2865791c8715243ba6094710c2e8a195e4721c5490ee98252c403975682ab1c1284756b930a43100e5d5a0aac704a11d5ae4c291c430ba2865791c8715243ba6093f10c2e8a195e4721c5490ee98250, 0x30d02ac65d5a0b1e14508eac1a56c304865791ba2c21485769b03a530c12195e46e8b085215da6c0e95c304865791ba2c21485769b03a4f0d02ac65d5a0b1e14508eac1a55c340ab1975682c7851423ab0694f0d02ac65d5a0b1e14508eac1a54c340ab1975682c7851423ab069470c12195e46e8b085215da6c0e90c340ab1975682c7851423ab0694b0d02ac65d5a0b1e14508eac1a4fc304865791ba2c21485769b03a470d02ac65d5a0b1e14508eac1a50, 0x30855d92282e4f090561e582e8d6c2157648a0b93c241587960ba3530855d92282e4f090561e582e8d3c2157648a0b93c241587960ba35709466c2a119cf1d6104a8c2e593c2519b0a84673c758412a30b965709466c2a119cf1d6104a8c2e594c2157648a0b93c241587960ba34309466c2a119cf1d6104a8c2e591c2157648a0b93c241587960ba33f0855d92282e4f090561e582e8d2c2519b0a84673c758412a30b96430855d92282e4f090561e582e8d1, 0x30d02ac65d5a0b1e14508eac1a5bc2157648a0b93c241587960ba3670c12195e46e8b085215da6c0e9ac2157648a0b93c241587960ba36b0d02ac65d5a0b1e14508eac1a5ac2519b0a84673c758412a30b966b09466c2a119cf1d6104a8c2e599c340ab1975682c7851423ab0695f09466c2a119cf1d6104a8c2e597c2157648a0b93c241587960ba3630d02ac65d5a0b1e14508eac1a58c304865791ba2c21485769b03a5f0855d92282e4f090561e582e8d7, 0x304959ce6c2a1310945e241aacd6c1256739b0a84c425178906ab34f04959ce6c2a1310945e241aacd4c1528a0b93764c574821a039b64f04959ce6c2a1310945e241aacd5c1528a0b93764c574821a039b653054a282e4dd9315d208680e6d95c1256739b0a84c425178906ab34304959ce6c2a1310945e241aaccfc1528a0b93764c574821a039b647054a282e4dd9315d208680e6d90c1256739b0a84c425178906ab34b04959ce6c2a1310945e241aacd1, 0x310c2e8a195e4721c5490ee9825bc403975682ab1c1284756b930a6b04959ce6c2a1310945e241aacd9c430ba2865791c8715243ba6096b04959ce6c2a1310945e241aacdac1528a0b93764c574821a039b667054a282e4dd9315d208680e6d9ac430ba2865791c8715243ba6095f04959ce6c2a1310945e241aacd8c1528a0b93764c574821a039b65f100e5d5a0aac704a11d5ae4c297c430ba2865791c8715243ba6096304959ce6c2a1310945e241aacd7, 0x300d1a0aac65d71149c602698ed6c034682ab1975c45271809a63b4f010de46e8a197151ca042a4dad3c034682ab1975c45271809a63b53010de46e8a197151ca042a4dad4c034682ab1975c45271809a63b57010de46e8a197151ca042a4dad5c034682ab1975c45271809a63b3f00d1a0aac65d71149c602698ed0c043791ba2865c5472810a936b43010de46e8a197151ca042a4dad1c034682ab1975c45271809a63b4700d1a0aac65d71149c602698ed2, 0x31486e4dd92283205c952cdaa41bc512a846739b0c182745b639a06b1486e4dd92283205c952cdaa41ac512a846739b0c182745b639a0671486e4dd92283205c952cdaa419c034682ab1975c45271809a63b6b010de46e8a197151ca042a4dadac034682ab1975c45271809a63b631486e4dd92283205c952cdaa417c512a846739b0c182745b639a05f010de46e8a197151ca042a4dad7c034682ab1975c45271809a63b5f1486e4dd92283205c952cdaa418, 0x3054a282e4dd9315d208680e6da3c1528a0b93764c574821a039b68b010de46e8a197151ca042a4dae1c1528a0b93764c574821a039b687010de46e8a197151ca042a4dae0c1528a0b93764c574821a039b683054a282e4dd9315d208680e6d9fc043791ba2865c5472810a936b7b054a282e4dd9315d208680e6d9ec1528a0b93764c574821a039b677010de46e8a197151ca042a4daddc043791ba2865c5472810a936b73054a282e4dd9315d208680e6d9c, 0x309466c2a119cf1d6104a8c2e5a3c034682ab1975c45271809a63b8709466c2a119cf1d6104a8c2e5a2c034682ab1975c45271809a63b8309466c2a119cf1d6104a8c2e5a1c2519b0a84673c758412a30b967f09466c2a119cf1d6104a8c2e5a0c034682ab1975c45271809a63b7b09466c2a119cf1d6104a8c2e59dc2519b0a84673c758412a30b967b00d1a0aac65d71149c602698edcc034682ab1975c45271809a63b7709466c2a119cf1d6104a8c2e59c, 0x304959ce6c2a1310945e241aace3c1256739b0a84c425178906ab38704959ce6c2a1310945e241aace0c1256739b0a84c425178906ab38b04959ce6c2a1310945e241aacdfc340ab1975682c7851423ab069870d02ac65d5a0b1e14508eac1a60c340ab1975682c7851423ab0697704959ce6c2a1310945e241aacdec1256739b0a84c425178906ab3730d02ac65d5a0b1e14508eac1a5ec340ab1975682c7851423ab0697304959ce6c2a1310945e241aacdd, 0x309466c2a119cf1d6104a8c2e5abc2519b0a84673c758412a30b96ab09466c2a119cf1d6104a8c2e5a9c340ab1975682c7851423ab069a70d02ac65d5a0b1e14508eac1a68c2519b0a84673c758412a30b96a309466c2a119cf1d6104a8c2e5a7c340ab1975682c7851423ab0699b09466c2a119cf1d6104a8c2e5a6c2519b0a84673c758412a30b96970d02ac65d5a0b1e14508eac1a65c340ab1975682c7851423ab0699309466c2a119cf1d6104a8c2e5a4, 0x30855d92282e4f090561e582e8e3c2157648a0b93c241587960ba3830855d92282e4f090561e582e8e1c2157648a0b93c241587960ba37f0855d92282e4f090561e582e8e2c430ba2865791c8715243ba6098310c2e8a195e4721c5490ee98261c430ba2865791c8715243ba609770855d92282e4f090561e582e8dcc2157648a0b93c241587960ba37b10c2e8a195e4721c5490ee9825cc430ba2865791c8715243ba6097b0855d92282e4f090561e582e8dd, 0x3054a282e4dd9315d208680e6dabc1528a0b93764c574821a039b6a7054a282e4dd9315d208680e6daac430ba2865791c8715243ba609a310c2e8a195e4721c5490ee98269c1528a0b93764c574821a039b69f054a282e4dd9315d208680e6da8c430ba2865791c8715243ba6099b054a282e4dd9315d208680e6da5c1528a0b93764c574821a039b69b10c2e8a195e4721c5490ee98264c430ba2865791c8715243ba60997054a282e4dd9315d208680e6da4, 0x304959ce6c2a1310945e241aacf0c2157648a0b93c241587960ba3bb04959ce6c2a1310945e241aaceec2157648a0b93c241587960ba3bf04959ce6c2a1310945e241aacefc430ba2865791c8715243ba609bb0d02ac65d5a0b1e14508eac1a6ec430ba2865791c8715243ba609b304959ce6c2a1310945e241aacedc2157648a0b93c241587960ba3b70d02ac65d5a0b1e14508eac1a6dc430ba2865791c8715243ba609b70855d92282e4f090561e582e8ec, 0x31486e4dd92283205c952cdaa423c304865791ba2c21485769b03a831486e4dd92283205c952cdaa41fc304865791ba2c21485769b03a871486e4dd92283205c952cdaa420c521b937648a0c817254b36a908b1486e4dd92283205c952cdaa421c304865791ba2c21485769b03a731486e4dd92283205c952cdaa41dc521b937648a0c817254b36a90730c12195e46e8b085215da6c0e9ec304865791ba2c21485769b03a771486e4dd92283205c952cdaa41e, 0x31486e4dd92283205c952cdaa42bc043791ba2865c5472810a936ba71486e4dd92283205c952cdaa428c521b937648a0c817254b36a90ab1486e4dd92283205c952cdaa427c521b937648a0c817254b36a90a7010de46e8a197151ca042a4dae8c043791ba2865c5472810a936b971486e4dd92283205c952cdaa426c521b937648a0c817254b36a9093010de46e8a197151ca042a4dae6c043791ba2865c5472810a936b931486e4dd92283205c952cdaa425, 0x300d1a0aac65d71149c602698ef0c304865791ba2c21485769b03abb1486e4dd92283205c952cdaa42fc034682ab1975c45271809a63bbb1486e4dd92283205c952cdaa42ec2519b0a84673c758412a30b96bf09466c2a119cf1d6104a8c2e5aec034682ab1975c45271809a63bb71486e4dd92283205c952cdaa42cc2519b0a84673c758412a30b96b70c12195e46e8b085215da6c0eadc304865791ba2c21485769b03ab31486e4dd92283205c952cdaa42d, 0x30855d92282e4f090561e582e8ebc2157648a0b93c241587960ba39f0c12195e46e8b085215da6c0ea8c2157648a0b93c241587960ba3a30855d92282e4f090561e582e8e9c304865791ba2c21485769b03aa70855d92282e4f090561e582e8eac304865791ba2c21485769b03a930855d92282e4f090561e582e8e4c2157648a0b93c241587960ba3970c12195e46e8b085215da6c0ea5c304865791ba2c21485769b03a9b0855d92282e4f090561e582e8e6, 0x3144aa119ce6c30609d16d8e6823c512a846739b0c182745b639a07f100e5d5a0aac704a11d5ae4c2a0c512a846739b0c182745b639a083100e5d5a0aac704a11d5ae4c2a1c512a846739b0c182745b639a087144aa119ce6c30609d16d8e6822c403975682ab1c1284756b930a73144aa119ce6c30609d16d8e681cc512a846739b0c182745b639a077100e5d5a0aac704a11d5ae4c29dc403975682ab1c1284756b930a7b144aa119ce6c30609d16d8e681e, 0x3010de46e8a197151ca042a4daf0c512a846739b0c182745b639a0bf100e5d5a0aac704a11d5ae4c2aec512a846739b0c182745b639a0bb010de46e8a197151ca042a4daeec1528a0b93764c574821a039b6bb054a282e4dd9315d208680e6dafc043791ba2865c5472810a936bb7054a282e4dd9315d208680e6dadc512a846739b0c182745b639a0b3100e5d5a0aac704a11d5ae4c2acc403975682ab1c1284756b930ab7144aa119ce6c30609d16d8e682d, 0x3144aa119ce6c30609d16d8e682bc512a846739b0c182745b639a0a300d1a0aac65d71149c602698ee9c512a846739b0c182745b639a09f144aa119ce6c30609d16d8e682ac034682ab1975c45271809a63ba3144aa119ce6c30609d16d8e6829c034682ab1975c45271809a63b97144aa119ce6c30609d16d8e6824c512a846739b0c182745b639a09b00d1a0aac65d71149c602698ee4c034682ab1975c45271809a63b9b144aa119ce6c30609d16d8e6825, 0x304959ce6c2a1310945e241aacebc403975682ab1c1284756b930aa304959ce6c2a1310945e241aace7c1256739b0a84c425178906ab3a704959ce6c2a1310945e241aace8c1256739b0a84c425178906ab3ab100e5d5a0aac704a11d5ae4c2a9c403975682ab1c1284756b930a9304959ce6c2a1310945e241aace5c1256739b0a84c425178906ab393100e5d5a0aac704a11d5ae4c2a6c403975682ab1c1284756b930a9704959ce6c2a1310945e241aace6][i.val]!

private def plan (i : CaseIndex) (w : Fin 13) : RepIndex × ℕ :=
  let v := planFields i >>> (110*w.val)
  (Fin.ofNat 49 (v % 64), (v >>> 6) % (2^104))

private def trans (i : CaseIndex) (w u : Fin 13) : Fin 13 := Fin.ofNat 13 (((plan i w).2 >>> (4 * u.val)) % 16)

private def invPlan (i : CaseIndex) (w u : Fin 13) : Fin 13 :=
  Fin.ofNat 13 (((plan i w).2 >>> (52+4*u.val)) % 16)

private def verifyPlan (i : CaseIndex) (w : Fin 13) : Bool :=
  let f := trans i w
  let E := (representative (plan i w).1).1
  (f w == (representative (plan i w).1).2.1) &&
    ((List.finRange 13).all fun a => invPlan i w (f a) == a) &&
    (bothArcs ((caseEdges i).map (Prod.map f f)) == bothArcs E)

private def repOK (i : RepIndex) : Bool :=
  let E := (representative i).1
  checkWords E (representative i).2.1 (E.length+1) (representative i).2.2 0 == some []

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc0 : repOK 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc1 : repOK 1 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc2 : repOK 2 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc3 : repOK 3 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc4 : repOK 4 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc5 : repOK 5 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc6 : repOK 6 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc7 : repOK 7 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc8 : repOK 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc9 : repOK 9 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc10 : repOK 10 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc11 : repOK 11 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc12 : repOK 12 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc13 : repOK 13 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc14 : repOK 14 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc15 : repOK 15 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc16 : repOK 16 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc17 : repOK 17 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc18 : repOK 18 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc19 : repOK 19 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc20 : repOK 20 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc21 : repOK 21 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc22 : repOK 22 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc23 : repOK 23 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc24 : repOK 24 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc25 : repOK 25 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc26 : repOK 26 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc27 : repOK 27 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc28 : repOK 28 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc29 : repOK 29 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc30 : repOK 30 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc31 : repOK 31 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc32 : repOK 32 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc33 : repOK 33 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc34 : repOK 34 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc35 : repOK 35 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc36 : repOK 36 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc37 : repOK 37 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc38 : repOK 38 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc39 : repOK 39 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc40 : repOK 40 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc41 : repOK 41 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc42 : repOK 42 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc43 : repOK 43 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc44 : repOK 44 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc45 : repOK 45 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc46 : repOK 46 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc47 : repOK 47 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem rc48 : repOK 48 = true := by decide +kernel
private theorem representativesChecked (i : RepIndex) : repOK i = true := by
  fin_cases i
  · exact rc0
  · exact rc1
  · exact rc2
  · exact rc3
  · exact rc4
  · exact rc5
  · exact rc6
  · exact rc7
  · exact rc8
  · exact rc9
  · exact rc10
  · exact rc11
  · exact rc12
  · exact rc13
  · exact rc14
  · exact rc15
  · exact rc16
  · exact rc17
  · exact rc18
  · exact rc19
  · exact rc20
  · exact rc21
  · exact rc22
  · exact rc23
  · exact rc24
  · exact rc25
  · exact rc26
  · exact rc27
  · exact rc28
  · exact rc29
  · exact rc30
  · exact rc31
  · exact rc32
  · exact rc33
  · exact rc34
  · exact rc35
  · exact rc36
  · exact rc37
  · exact rc38
  · exact rc39
  · exact rc40
  · exact rc41
  · exact rc42
  · exact rc43
  · exact rc44
  · exact rc45
  · exact rc46
  · exact rc47
  · exact rc48

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc0 : ∀ w : Fin 13, verifyPlan 0 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc1 : ∀ w : Fin 13, verifyPlan 1 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc2 : ∀ w : Fin 13, verifyPlan 2 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc3 : ∀ w : Fin 13, verifyPlan 3 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc4 : ∀ w : Fin 13, verifyPlan 4 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc5 : ∀ w : Fin 13, verifyPlan 5 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc6 : ∀ w : Fin 13, verifyPlan 6 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc7 : ∀ w : Fin 13, verifyPlan 7 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc8 : ∀ w : Fin 13, verifyPlan 8 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc9 : ∀ w : Fin 13, verifyPlan 9 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc10 : ∀ w : Fin 13, verifyPlan 10 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc11 : ∀ w : Fin 13, verifyPlan 11 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc12 : ∀ w : Fin 13, verifyPlan 12 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc13 : ∀ w : Fin 13, verifyPlan 13 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc14 : ∀ w : Fin 13, verifyPlan 14 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc15 : ∀ w : Fin 13, verifyPlan 15 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc16 : ∀ w : Fin 13, verifyPlan 16 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc17 : ∀ w : Fin 13, verifyPlan 17 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc18 : ∀ w : Fin 13, verifyPlan 18 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc19 : ∀ w : Fin 13, verifyPlan 19 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc20 : ∀ w : Fin 13, verifyPlan 20 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc21 : ∀ w : Fin 13, verifyPlan 21 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc22 : ∀ w : Fin 13, verifyPlan 22 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc23 : ∀ w : Fin 13, verifyPlan 23 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc24 : ∀ w : Fin 13, verifyPlan 24 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc25 : ∀ w : Fin 13, verifyPlan 25 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc26 : ∀ w : Fin 13, verifyPlan 26 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc27 : ∀ w : Fin 13, verifyPlan 27 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc28 : ∀ w : Fin 13, verifyPlan 28 w = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 60000000 in
private theorem pc29 : ∀ w : Fin 13, verifyPlan 29 w = true := by decide +kernel
private theorem planBits (i : CaseIndex) : ∀ w : Fin 13, verifyPlan i w = true := by
  fin_cases i
  · exact pc0
  · exact pc1
  · exact pc2
  · exact pc3
  · exact pc4
  · exact pc5
  · exact pc6
  · exact pc7
  · exact pc8
  · exact pc9
  · exact pc10
  · exact pc11
  · exact pc12
  · exact pc13
  · exact pc14
  · exact pc15
  · exact pc16
  · exact pc17
  · exact pc18
  · exact pc19
  · exact pc20
  · exact pc21
  · exact pc22
  · exact pc23
  · exact pc24
  · exact pc25
  · exact pc26
  · exact pc27
  · exact pc28
  · exact pc29


private theorem plansChecked (i : CaseIndex) (w : Fin 13) :
    (∀ a b, trans i w a = trans i w b → a = b) ∧
    trans i w w = (representative (plan i w).1).2.1 ∧
    ∀ a b, (edgeListGraph (caseEdges i)).Adj a b ↔
      (edgeListGraph (representative (plan i w).1).1).Adj (trans i w a) (trans i w b) := by
  have h := planBits i w
  simp only [verifyPlan,Bool.and_eq_true,List.all_eq_true,beq_iff_eq,List.mem_finRange,
    true_implies] at h
  have inj : Function.Injective (trans i w) := by
    intro a b he
    exact ((h.1.2 a).symm.trans ((congrArg (invPlan i w) he).trans (h.1.2 b)))
  exact ⟨inj,h.1.1,packed_iso _ _ _ inj h.2⟩

private theorem avoid_case (i : CaseIndex) (w : Fin 13) :
    Avoidable (edgeListGraph (caseEdges i)) w := by
  obtain ⟨hinj,hw,he⟩ := plansChecked i w
  refine avoid_relabel _ _ (trans i w) (fun {a b} => hinj a b) he w ?_
  rw [hw]
  apply certified
  have h := eq_of_beq (representativesChecked (plan i w).1)
  change checkWords _ _ _ _ (packedArcs []) = some [] at h
  rwa [words_agree] at h

end OrientationCert904

namespace OrientationCert904

open Finset

def coreEdges12 : List (Fin 12 × Fin 12) := [(0,1), (0,2), (1,3), (2,4), (3,5), (4,5), (0,6), (1,6), (0,7), (2,7), (1,8), (3,8), (2,9), (4,9), (8,9), (3,10), (5,10), (7,10), (4,11), (5,11), (6,11)]

private def tailCase (j : Fin 25) : CaseIndex := ⟨j.val+5,by omega⟩

private def tailSet (j : Fin 25) : Finset (Fin 12) :=
  #[∅, {0}, {1}, {2}, {3}, {2,3}, {4}, {1,4}, {5}, {0,5}, {6}, {7}, {8}, {7,8}, {9}, {6,9}, {8,9}, {10}, {6,10}, {7,10}, {9,10}, {11}, {6,11}, {7,11}, {8,11}][j.val]!

private def coverBit {n : ℕ} (E : List (Fin n × Fin n)) (a b : Fin n) : Bool :=
  decide (a ≠ b) && (E.contains (a,b) || E.contains (b,a))

private theorem coverBit_iff {n : ℕ} (E : List (Fin n × Fin n)) (a b : Fin n) :
    coverBit E a b = true ↔ (edgeListGraph E).Adj a b := by
  simp [coverBit,edgeListGraph,SimpleGraph.fromRel_adj]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem oldCheck : ∀ j : Fin 25, ∀ a b : Fin 12,
    coverBit (caseEdges (tailCase j)) a.castSucc b.castSucc = coverBit coreEdges12 a b := by decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem lastCheck : ∀ j : Fin 25, ∀ a : Fin 12,
    coverBit (caseEdges (tailCase j)) a.castSucc (Fin.last 12) = decide (a ∈ tailSet j) := by decide

private theorem tableShape (j : Fin 25) :
    (∀ a b : Fin 12, (edgeListGraph (caseEdges (tailCase j))).Adj a.castSucc b.castSucc ↔
       (edgeListGraph coreEdges12).Adj a b) ∧
    (∀ a : Fin 12, (edgeListGraph (caseEdges (tailCase j))).Adj a.castSucc (Fin.last 12) ↔ a ∈ tailSet j) := by
  constructor
  · intro a b; rw [← coverBit_iff,← coverBit_iff,oldCheck]
  · intro a; rw [← coverBit_iff,lastCheck,decide_eq_true_eq]

private theorem emptyTail : ∃ j : Fin 25, tailSet j = ∅ := by decide
private theorem singleTail : ∀ a : Fin 12, ∃ j : Fin 25, tailSet j = {a} := by decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem pairCheck : ∀ a b : Fin 12, a ≠ b →
    (∀ z : Fin 12, (coverBit coreEdges12 a z && coverBit coreEdges12 b z) = false) →
    ∃ j : Fin 25, tailSet j = {a,b} := by decide

private theorem pairTail (a b : Fin 12) (hab : a ≠ b)
    (no : ∀ z, ¬ ((edgeListGraph coreEdges12).Adj a z ∧ (edgeListGraph coreEdges12).Adj b z)) :
    ∃ j : Fin 25, tailSet j = {a,b} := by
  apply pairCheck a b hab
  intro z
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
  exact no z ⟨(coverBit_iff _ _ _).mp ha,(coverBit_iff _ _ _).mp hb⟩

private theorem extend_core12 (H : SimpleGraph (Fin 13)) [DecidableRel H.Adj]
    (h0 : ∀ a b : Fin 12, H.Adj a.castSucc b.castSucc ↔ (edgeListGraph coreEdges12).Adj a b)
    (h4 : Reduction904.SquareFree H) (hd : H.degree (Fin.last 12) ≤ 2) :
    ∃ i : CaseIndex, H = edgeListGraph (caseEdges i) := by
  classical
  let N := univ.filter (fun a : Fin 12 => H.Adj a.castSucc (Fin.last 12))
  have hm (a : Fin 12) : a ∈ N ↔ H.Adj a.castSucc (Fin.last 12) := by simp [N]
  have hc : N.card ≤ 2 := by
    have sub : N.map (Fin.castSuccEmb : Fin 12 ↪ Fin 13) ⊆ H.neighborFinset (Fin.last 12) := by
      intro y hy
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hy
      exact (H.mem_neighborFinset _ _).mpr ((hm a).mp ha).symm
    have h := card_le_card sub
    rw [card_map,H.card_neighborFinset_eq_degree] at h
    omega
  have existsCase : ∃ j : Fin 25, tailSet j = N := by
    by_cases hZ : N.card = 0
    · simpa only [card_eq_zero.mp hZ] using emptyTail
    by_cases hO : N.card = 1
    · obtain ⟨a,ha⟩ := card_eq_one.mp hO
      rw [ha]
      exact singleTail a
    obtain ⟨a,b,hab,hN⟩ := card_eq_two.mp (show N.card=2 by omega)
    have edgeA := (hm a).mp (show a ∈ N by rw [hN]; simp)
    have edgeB := (hm b).mp (show b ∈ N by rw [hN]; simp)
    rw [hN]
    apply pairTail a b hab
    intro z h
    exact h4 a.castSucc z.castSucc b.castSucc (Fin.last 12)
      (fun e => hab (Fin.castSucc_inj.mp e)) (Fin.castSucc_ne_last z)
      ((h0 _ _).mpr h.1) ((h0 _ _).mpr h.2).symm edgeB edgeA.symm
  obtain ⟨j,hj⟩ := existsCase
  obtain ⟨old,last⟩ := tableShape j
  refine ⟨tailCase j, ?_⟩
  ext a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · simp
  · rename_i b
    rw [H.adj_comm, (edgeListGraph (caseEdges (tailCase j))).adj_comm, last, hj,hm]
  · rename_i a
    rw [last,hj,hm]
  · rename_i a b
    exact (h0 a b).trans (old a b).symm

private abbrev rowsAdj (n : ℕ) (rows : List ℕ) (a b : Fin n) :=
  (rows[a.val]?.getD 0).testBit (n-1-b.val) = true

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
private theorem rows12Check : ∀ rows ∈ Census904.exceptions 12, ∀ a b : Fin 12,
    rowsAdj 12 rows a b ↔ (edgeListGraph coreEdges12).Adj a b := by
  unfold Census904.exceptions
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq]
  unfold edgeListGraph
  simp only [SimpleGraph.fromRel_adj]
  decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
private theorem rows13Check : ∀ rows ∈ Census904.exceptions 13, ∃ i : Fin 5, ∀ a b : Fin 13,
    rowsAdj 13 rows a b ↔ (edgeListGraph (caseEdges ⟨i.val, by omega⟩)).Adj a b := by
  intro rows h
  unfold Census904.exceptions at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl <;>
    unfold edgeListGraph <;> simp only [SimpleGraph.fromRel_adj] <;> decide

private theorem from13Rows (H : SimpleGraph (Fin 13)) (rows : List ℕ)
    (he : rows ∈ Census904.exceptions 13)
    (ha : ∀ a b, H.Adj a b ↔ (rows[a.val]?.getD 0).testBit (13-1-b.val) = true) :
    ∃ i : CaseIndex, H = edgeListGraph (caseEdges i) := by
  obtain ⟨i,h⟩ := rows13Check rows he
  exact ⟨⟨i.val,by omega⟩, by ext a b; exact (ha a b).trans (h a b)⟩

private theorem from12Rows (H : SimpleGraph (Fin 12)) (rows : List ℕ)
    (he : rows ∈ Census904.exceptions 12)
    (ha : ∀ a b, H.Adj a b ↔ (rows[a.val]?.getD 0).testBit (12-1-b.val) = true) :
    H = edgeListGraph coreEdges12 :=
  by ext a b; exact (ha a b).trans (rows12Check rows he a b)

end OrientationCert904

namespace OrientationCert904

open Reduction904
open GraphFacts Finset

private theorem matrix_iff {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (a b : Fin n) :
    H.Adj a b ↔
      ((Census904.matrix (fun x y => decide (H.Adj x y)))[a.val]?.getD 0).testBit (n-1-b.val)=true := by
  let A := fun x y : Fin n => decide (H.Adj x y)
  have hh := Census904.row_hits A a b
  rw [Census904.hits_eq_bit] at hh
  have he : (Census904.matrix A)[a.val]? = some (Census904.row A a) := by simp [Census904.matrix]
  change H.Adj a b ↔ ((Census904.matrix A)[a.val]?.getD 0).testBit _ = true
  rw [he]
  change _ ↔ (Census904.row A a).testBit _ = true
  rw [hh]
  exact decide_eq_true_iff.symm

private theorem from_comap {n : ℕ} (G : SimpleGraph (Fin n)) (p : Equiv.Perm (Fin n)) (w : Fin n)
    (h : Avoidable (G.comap p) (p.symm w)) : Avoidable G w := by
  apply avoid_relabel G (G.comap p) p.symm p.symm.injective _ w h
  intro a b
  simp [SimpleGraph.comap_adj]

private theorem pad_eq : (edgeListGraph coreEdges12).map (Fin.castSuccEmb : Fin 12 ↪ Fin 13) =
    edgeListGraph (caseEdges (tailCase 0)) := by
  let K := edgeListGraph coreEdges12
  let f := (Fin.castSuccEmb : Fin 12 ↪ Fin 13)
  have miss (a : Fin 13) : ¬ (K.map f).Adj (Fin.last 12) a := by
    intro h
    obtain ⟨u,v,_,eq,_⟩ := (SimpleGraph.map_adj f K _ _).mp h
    exact Fin.castSucc_ne_last u eq
  obtain ⟨old,last⟩ := tableShape 0
  have ht : tailSet 0 = ∅ := by decide
  ext a b
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · simp
  · rename_i b
    change (K.map f).Adj _ _ ↔ _
    rw [iff_false_left (miss _), (edgeListGraph (caseEdges (tailCase 0))).adj_comm, last, ht]
    simp
  · rename_i a
    change (K.map f).Adj _ _ ↔ _
    rw [(K.map f).adj_comm, iff_false_left (miss _), last, ht]
    simp
  · rename_i a b
    change (K.map f).Adj (f a) (f b) ↔ _
    rw [SimpleGraph.map_adj_apply,old]

private theorem avoid12_for_exception (H : SimpleGraph (Fin 12)) [DecidableRel H.Adj]
    (p : Equiv.Perm (Fin 12)) (w : Fin 12)
    (hp : Census904.matrix (fun i j => decide ((H.comap p).Adj i j)) ∈ Census904.exceptions 12) :
    Avoidable H w := by
  have hg := from12Rows (H.comap p) _ hp (matrix_iff _)
  apply from_comap H p w
  rw [hg]
  apply avoid_map _ Fin.castSuccEmb
  rw [pad_eq]
  exact avoid_case _ _

private abbrev Classifies : Prop := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  n ≤ 13 → SquareFree G → (∀ v, 3 ≤ G.degree v) → G.Colorable 3 ∨ ∃ p : Equiv.Perm (Fin n),
  Census904.matrix (fun i j => decide ((G.comap p).Adj i j)) ∈ Census904.exceptions n

private theorem core_census_of_classify (classify : Classifies) : CoreCensus904 := by
  intro n G _ hn h4 hmin
  rcases classify G (by omega) h4 hmin with hc | ⟨p,hp⟩
  · exact hc
  · have hemp : ∀ k : Fin 12, Census904.exceptions k.val = [] := by decide
    rw [hemp ⟨n,by omega⟩] at hp
    exact (List.not_mem_nil hp).elim

private theorem extend_exception (classify : Classifies) (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (h4 : SquareFree G) (v w : Fin 13) (hv : G.degree v ≤ 2)
    (hsub : let U := (univ : Finset (Fin 13)).erase v
      U.card=12 ∧ SquareFree (induced904 G U) ∧ ¬(induced904 G U).Colorable 3 ∧
      ∀ i, 3 ≤ ((induced904 G U).neighborSet i).ncard) : Avoidable G w := by
  classical
  let U := (univ : Finset (Fin 13)).erase v
  let K := induced904 G U
  obtain ⟨hu,hs,hnc,hmin⟩ := hsub
  change U.card=12 at hu
  obtain ⟨p,hp⟩ : ∃ p : Equiv.Perm (Fin U.card),
      Census904.matrix (fun i j => decide ((K.comap p).Adj i j)) ∈ Census904.exceptions U.card := by
    rcases classify K (by omega) hs (fun j => by simpa [K] using hmin j) with hc | h
    · exact (hnc hc).elim
    · exact h
  let rows := Census904.matrix (fun i j => decide ((K.comap p).Adj i j))
  change rows ∈ _ at hp
  have h12 := rows12Check rows (show rows ∈ Census904.exceptions 12 from hu ▸ hp)
  let f : Fin 12 ≃ U := ((finCongr hu.symm).trans p).trans U.equivFin.symm
  let name := (Fin.lastCases v (fun i => (f i).val) : Fin 13 → Fin 13)
  have fl (a : Fin 12) : (f a).val ≠ v := (mem_erase.mp (f a).property).1
  have hinj : Function.Injective name := by
    intro a b
    induction a using Fin.lastCases <;> induction b using Fin.lastCases
    · exact fun _ => rfl
    · rename_i b
      intro eq
      exact False.elim ((fl b) (show v = (f b).val from by simpa only [name,Fin.lastCases_last,Fin.lastCases_castSucc] using eq).symm)
    · rename_i a
      intro eq
      exact False.elim ((fl a) (by simpa only [name,Fin.lastCases_last,Fin.lastCases_castSucc] using eq))
    · rename_i a b
      intro eq
      exact congrArg Fin.castSucc (f.injective (Subtype.ext (by simpa only [name,Fin.lastCases_last,Fin.lastCases_castSucc] using eq)))
  let e : Equiv.Perm (Fin 13) := Equiv.ofBijective name ⟨hinj,Finite.injective_iff_surjective.mp hinj⟩
  have elast : e (Fin.last 12) = v := by
    change name (Fin.last 12) = v
    exact Fin.lastCases_last
  have ein (a : Fin 12) : e a.castSucc = (f a).val := by
    change name a.castSucc = (f a).val
    exact Fin.lastCases_castSucc _
  have old (a b : Fin 12) : (G.comap e).Adj a.castSucc b.castSucc ↔ (edgeListGraph coreEdges12).Adj a b := by
    rw [SimpleGraph.comap_adj,ein,ein]
    have hh := matrix_iff (K.comap p) (Fin.cast hu.symm a) (Fin.cast hu.symm b)
    change G.Adj (f a).val (f b).val ↔ (rows[a.val]?.getD 0).testBit (U.card-1-b.val) = true at hh
    rw [hh]
    simpa only [rowsAdj,hu] using h12 a b
  have square : SquareFree (G.comap e) :=
    fun a b c d hac hbd hab hbc hcd hda =>
      h4 (e a) (e b) (e c) (e d) (fun he => hac (e.injective he)) (fun he => hbd (e.injective he)) hab hbc hcd hda
  have low : (G.comap e).degree (Fin.last 12) ≤ 2 := by
    rw [← (SimpleGraph.Iso.comap e G).degree_eq (Fin.last 12)]
    change G.degree (e (Fin.last 12)) ≤ 2
    rw [elast]
    exact hv
  obtain ⟨i,hi⟩ := extend_core12 (G.comap e) old square low
  apply from_comap G e w
  rw [hi]
  exact avoid_case _ _

theorem all_avoid_of_classify (classify : Classifies) : Reduction904.AvoidAll := by
  intro n hn G h4
  classical
  have allW : ∀ w, Avoidable G w := by
    intro w
    by_cases hc : G.Colorable 3
    · exact avoid_of_coloring G w hc
    rcases low_degree_core_reduce (core_census_of_classify classify) G hn h4 hc with
      ⟨hord,hmin⟩ | ⟨h13,v,hv,hsub⟩
    · rcases hord with rfl|rfl
      · rcases classify G (by decide) h4 hmin with h|⟨p,hp⟩
        · exact (hc h).elim
        · exact avoid12_for_exception G p w hp
      · rcases classify G (by decide) h4 hmin with h|⟨p,hp⟩
        · exact (hc h).elim
        · obtain ⟨i,hi⟩ := from13Rows (G.comap p) _ hp (matrix_iff _)
          apply from_comap G p w
          rw [hi]
          exact avoid_case _ _
    · subst n
      exact extend_exception classify G h4 v w hv hsub
  exact fun D ho w => allW w D ho

end OrientationCert904

theorem full_statement (n : ℕ) (hn : n ≤ 15) (G : SimpleGraph (Fin n))
    (h4 : Reduction904.SquareFree G) (D : Fin n → Fin n → Prop)
    (hor : Reduction904.Orientation G D) : GraphFacts.HasWitness G D := by
  have color10 (H : SimpleGraph (Fin 10)) (sq : Reduction904.SquareFree H) : H.Colorable 3 := by
    classical
    exact GraphFacts.small_colorable_of_census
      (OrientationCert904.core_census_of_classify Census904.classify) H (by decide) sq
  obtain ⟨I,_,hi,hw⟩ := Reduction904.dense_and_avoid_suffice
    (OrientationCert904.all_avoid_of_classify Census904.classify)
    (Reduction904.dense_of_small color10) hn G h4 D hor
  exact ⟨I,hi,fun a c => hw a (Finset.mem_univ _) c (Finset.mem_univ _)⟩

end PEqualNP.Outside.L_meta_904_aux

theorem PEqualNP.Outside.L_meta_904 : ∀ n : ℕ, n ≤ 15 → ∀ G : SimpleGraph (Fin n),
  (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
  ∀ D : Fin n → Fin n → Prop, (∀ a c : Fin n, G.Adj a c → (D a c ↔ ¬ D c a)) →
  ∃ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧
    ∀ a c : Fin n, a ∉ I → c ∉ I → G.Adj a c →
      (∃ i ∈ I, G.Adj a i ∧ D a i) ∨ (∃ i ∈ I, G.Adj c i ∧ D c i) := by
  exact PEqualNP.Outside.L_meta_904_aux.full_statement
