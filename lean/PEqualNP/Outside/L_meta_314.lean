import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_314_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open Function (update)
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
 gs.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x=wiresFrom C.gates x:=rfl
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) : wiresFrom (gs ++ gs') w=wiresFrom gs' (wiresFrom gs w):=by simp [wiresFrom,List.foldl_append]
theorem p9 (gs : List Gate) : ∀ w : List Bool,∃ t : List Bool,wiresFrom gs w=w ++ t ∧ t.length=gs.length:=by{
induction gs with
| nil=>intro w;exact ⟨[],by simp [wiresFrom],rfl⟩
| cons g gs ih =>{
intro w;obtain ⟨t,ht,hl⟩:=ih (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)])
refine ⟨g.op.eval (g.inputs.map fun i=>w.getD i false) :: t,?_,by simp [hl]⟩
have : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
rw [this,ht];simp
}
}
theorem length_wiresFrom (gs : List Gate) (w : List Bool) : (wiresFrom gs w).length=w.length + gs.length:=by{
obtain ⟨t,ht,hl⟩:=p9 gs w;rw [ht];simp [hl]
}
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) : (wiresFrom gs w).getD i false=w.getD i false:=by{
obtain ⟨t,ht,_⟩:=p9 gs w;rw [ht,List.getD_append _ _ _ _ h]
}
def Ok (g : Gate) : Prop :=
 g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) : (L ++ [S]).getD j d=L.getD j d:=by
 by_cases hj : j < L.length
 · exact List.getD_append _ _ _ _ hj
 · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d=S:=by simp
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
 (g.inputs.map fun a=>L.getD a ∅).foldr (· ∪ ·) ∅
theorem pd (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) : i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l,i ∈ F a:=by{
induction l with
| nil=>simp
| cons b l ih=>simp [ih]
}
theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) : i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs,i ∈ L.getD a ∅ :=
 pd _ _ _
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
 gs.foldl (fun L g=>L ++ [gateSupp L g]) L
def inputSupps (n : ℕ) : List (Finset (Fin n)):=List.ofFn fun i : Fin n=>{i}
def p3f (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
 L.length=w.length ∧ w.length=w'.length ∧
  ∀ j : ℕ,(∀ i ∈ L.getD j ∅,x i=y i) → w.getD j false=w'.getD j false
theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) : ∀ (L : List (Finset (Fin n))) (w w' : List Bool),p3f x y L w w' → p3f x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w'):=by
 induction gs with
 | nil=>intro L w w' h;exact h
 | cons g gs ih =>
  intro L w w' h;obtain ⟨h1,h2,h3⟩:=h;apply ih (L ++ [gateSupp L g])
   (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)])
   (w' ++ [g.op.eval (g.inputs.map fun i=>w'.getD i false)])
  refine ⟨by simp [h1],by simp [h2],?_⟩
  intro j hj
  by_cases hjl : j=L.length
  · subst hjl;rw [getD_snoc_eq] at hj;rw [h1,getD_snoc_eq,h2,getD_snoc_eq];congr 1;apply List.map_congr_left;intro a ha;exact h3 a (fun i hi=>hj i ((mem_gateSupp L g i).2 ⟨a,ha,hi⟩))
  · rw [getD_snoc_ne _ _ _ _ hjl] at hj
    rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)]
    exact h3 j hj
theorem agree_inputs (x y : Fin n → Bool) : p3f x y (inputSupps n) (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp [inputSupps],by simp,?_⟩
 intro j hj
 by_cases hjn : j < n
 · have hx : x ⟨j,hjn⟩=y ⟨j,hjn⟩:=hj _ (by simp [inputSupps,hjn])
   simp [hjn,hx]
 · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
 ∀ W : Finset ℕ,(W.biUnion fun j=>L.getD j ∅).card ≤ t + W.card
theorem cnt_inputs : Cnt 0 (inputSupps n):=by
 intro W;refine le_trans Finset.card_biUnion_le ?_
 rw [zero_add,Finset.card_eq_sum_ones];apply Finset.sum_le_sum;intro j _
 by_cases hjn : j < n
 · simp [inputSupps,hjn]
 · rw [List.getD_eq_default _ _ (by simp [inputSupps];omega)];simp
theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2) (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]):=by{
intro W
by_cases hW : L.length ∈ W
{
have hsub : (W.biUnion fun j=>(L ++ [gateSupp L g]).getD j ∅) ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j=>L.getD j ∅):=by{
intro i hi;rw [Finset.mem_biUnion] at hi ⊢;obtain ⟨j,hjW,hij⟩:=hi
by_cases hjl : j=L.length
{subst hjl;rw [getD_snoc_eq] at hij;obtain ⟨a,ha,hia⟩:=(mem_gateSupp L g i).1 hij;exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩}
{rw [getD_snoc_ne _ _ _ _ hjl] at hij;exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩}
}
have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2:=by{
refine le_trans (Finset.card_union_le _ _) ?_
rw [Finset.card_erase_of_mem hW];exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
}
have hWpos : 1 ≤ W.card:=Finset.card_pos.2 ⟨_,hW⟩;have:=h (W.erase L.length ∪ g.inputs.toFinset);have:=Finset.card_le_card hsub;omega
}
{
have heq : (W.biUnion fun j=>(L ++ [gateSupp L g]).getD j ∅) = (W.biUnion fun j=>L.getD j ∅):=by{
apply Finset.biUnion_congr rfl;intro j hj;exact getD_snoc_ne _ _ _ _ (fun e=>hW (e ▸ hj))
}
rw [heq];have:=h W;omega
}
}
theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),(∀ g ∈ gs,Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L):=by
 induction gs with
 | nil=>intro t L _ h;exact h
 | cons g gs ih =>
  intro t L hok h;have:=ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg'=>hok g' (List.mem_cons_of_mem _ hg'))
   (cnt_step t L g (hok g List.mem_cons_self).2 h)
  rw [List.length_cons,show t + (gs.length + 1)=t + 1 + gs.length by omega]
  exact this
theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool) (hdep : ∀ i : Fin n,∃ x : Fin n → Bool,f (update x i (!x i)) ≠ f x) (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1:=by
 obtain ⟨C,ok,hsz,hev⟩:=h;have hsz' : C.gates.length ≤ s:=hsz
 set S:=(suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
 have hall : ∀ i : Fin n,i ∈ S:=by
  intro i
  by_contra hi
  obtain ⟨x,hx⟩:=hdep i;apply hx
  have hag:=(agree_wiresFrom (update x i (!x i)) x C.gates _ _ _ (agree_inputs _ _)).2.2 C.output (by
   intro k hk;have : k ≠ i:=fun e=>hi (e ▸ hk)
   simp [Function.update_of_ne this])
  rw [← hev,← hev];exact hag
 have hcard : S.card=n:=by rw [Finset.eq_univ_of_forall hall];simp
 have hc:=cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output};simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at hc;rw [← hS,hcard] at hc;omega
open PEqualNP.CircuitLowerBounds
def normGate (g : Gate) : Gate :=
 match g.op with
 | GateOp.not=>⟨GateOp.not,g.inputs.take 1⟩
 | _=>g
theorem p17 (g : Gate) (F : ℕ → Bool) : (normGate g).op.eval ((normGate g).inputs.map F)=g.op.eval (g.inputs.map F):=by{
obtain ⟨op,inputs⟩:=g
cases op <;> simp only [normGate]
cases inputs <;> simp [GateOp.eval]
}
def NOk (g : Gate) : Prop:=Ok g ∧ (g.op=GateOp.not → g.inputs.length ≤ 1)
theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g):=by{
obtain ⟨op,inputs⟩:=g;obtain ⟨hop,hlen⟩:=h
rcases hop with h | h | h
{
have : op=GateOp.and:=h
subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [normGate]⟩
}
{
have : op=GateOp.or:=h
subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [normGate]⟩
}
{
have : op=GateOp.not:=h;subst this;refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _=>?_⟩
{cases inputs <;> simp [normGate]}
{cases inputs <;> simp [normGate]}
}
}
theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,wiresFrom (gs.map normGate) w=wiresFrom gs w:=by
 induction gs with
 | nil=>intro w;rfl
 | cons g gs ih =>
  intro w;have s1 : wiresFrom ((g :: gs).map normGate) w=wiresFrom (gs.map normGate)
   (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i=>w.getD i false)]):=rfl
  have s2 : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
  rw [s1,s2,p17,ih]
abbrev Stat : Type:=Bool ⊕ ℕ
def Stat.val (w : List Bool) : Stat → Bool
 | Sum.inl c=>c
 | Sum.inr j=>w.getD j false
def Stat.Valid (m : ℕ) : Stat → Prop
 | Sum.inl _=>True
 | Sum.inr j=>j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
 | []=>(none,Sum.inl true)
 | Sum.inl c :: _=>(none,Sum.inl (!c))
 | Sum.inr j :: _=>(some ⟨GateOp.not,[j]⟩,Sum.inr m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
 | []=>(none,Sum.inl true)
 | [Sum.inl c]=>(none,Sum.inl c)
 | [Sum.inr j]=>(none,Sum.inr j)
 | [Sum.inl c,Sum.inl d]=>(none,Sum.inl (c && d))
 | [Sum.inl c,Sum.inr j]=>(none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inl c]=>(none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inr k]=>(some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
 | _=>(none,Sum.inl false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
 | []=>(none,Sum.inl false)
 | [Sum.inl c]=>(none,Sum.inl c)
 | [Sum.inr j]=>(none,Sum.inr j)
 | [Sum.inl c,Sum.inl d]=>(none,Sum.inl (c || d))
 | [Sum.inl c,Sum.inr j]=>(none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inl c]=>(none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inr k]=>(some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
 | _=>(none,Sum.inl false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
 match op with
 | GateOp.and=>simpAnd m ins
 | GateOp.or=>simpOr m ins
 | GateOp.not=>simpNot m ins
 | _=>(none,Sum.inl false)
theorem p24 (op : GateOp) (m : ℕ) (ins : List Stat) : ∀ g ∈ (simplify op m ins).1,Ok g:=by
 intro g hg
 cases op <;> simp only [simplify] at hg
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp [simpAnd] at hg ;(subst hg;simp [Ok])
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp [simpOr] at hg ;(subst hg;simp [Ok])
 · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
    simp [simpNot] at hg ;(subst hg;simp [Ok])
 · simp at hg
 · simp at hg
theorem p10 (op : GateOp) (m : ℕ) (ins : List Stat) (hop : op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not) (hlen : ins.length ≤ 2) (hnot : op=GateOp.not → ins.length ≤ 1) (hc : ∃ c,Sum.inl c ∈ ins) : (simplify op m ins).1=none:=by
 obtain ⟨c,hc⟩:=hc
 rcases hop with rfl | rfl | rfl
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simplify,simpAnd]
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simplify,simpOr]
 · have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [simplify,simpNot]
theorem p14 (op : GateOp) (hop : op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not) (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2) (hv : ∀ s ∈ ins,s.Valid w.length) : ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧ ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)=op.eval (ins.map (Stat.val w)):=by{
rcases hop with rfl | rfl | rfl
{
rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
{simp [simplify,simpAnd,Stat.Valid,Stat.val,GateOp.eval]}
{cases a <;> simp_all [simplify,simpAnd,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]}
{
cases a with
| inl c =>{
cases b with
| inl e=>simp_all [simplify,simpAnd,Stat.Valid,Stat.val,GateOp.eval]
| inr k=>cases c <;> simp_all [simplify,simpAnd,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
}
| inr j =>{
cases b with
| inl e=>cases e <;> simp_all [simplify,simpAnd,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
| inr k=>simp_all [simplify,simpAnd,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
}
}
{simp at hlen}
}
{
rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
{simp [simplify,simpOr,Stat.Valid,Stat.val,GateOp.eval]}
{cases a <;> simp_all [simplify,simpOr,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]}
{
cases a with
| inl c =>{
cases b with
| inl e=>simp_all [simplify,simpOr,Stat.Valid,Stat.val,GateOp.eval]
| inr k=>cases c <;> simp_all [simplify,simpOr,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
}
| inr j =>{
cases b with
| inl e=>cases e <;> simp_all [simplify,simpOr,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
| inr k=>simp_all [simplify,simpOr,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
}
}
{simp at hlen}
}
{
rcases ins with _ | ⟨a,l⟩
{simp [simplify,simpNot,Stat.Valid,Stat.val,GateOp.eval]}
{cases a <;> simp_all [simplify,simpNot,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]}
}
}
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
 (acc.1 ++ [(simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).2],acc.2 ++ (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
 gs.foldl (elimStep n) acc
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length=k) : (L ++ [S]).getD k d=S:=by subst h;simp
theorem p2b (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,k < acc.1.length → (elim n gs acc).1.getD k d=acc.1.getD k d:=by
 induction gs with
 | nil=>intro acc _;rfl
 | cons g gs ih =>
  intro acc hk;have h3 : elim n (g :: gs) acc=elim n gs (elimStep n acc g):=rfl
  rw [h3,ih (elimStep n acc g) (by simp [elimStep];omega)]
  exact getD_snoc_ne _ _ _ _ (by omega)
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1:=by cases o <;> simp
theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,(∀ g ∈ acc.2,Ok g) → ∀ g ∈ (elim n gs acc).2,Ok g:=by
 induction gs with
 | nil=>intro acc h;exact h
 | cons g gs ih =>
  intro acc h;apply ih (elimStep n acc g);intro g' hg'
  rcases List.mem_append.1 hg' with h1 | h1
  · exact h g' h1
  · exact p24 _ _ _ g' (by simpa using h1)
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,(elim n gs acc).2.length ≤ acc.2.length + gs.length:=by{
induction gs with
| nil=>intro acc;simp [elim]
| cons g gs ih =>{
intro acc;have h1:=ih (elimStep n acc g)
have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1:=by{
simp only [elimStep,List.length_append];have:=toList_length_le (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1;omega
}
have h3 : elim n (g :: gs) acc=elim n gs (elimStep n acc g):=rfl;rw [h3,List.length_cons];omega
}
}
theorem p23 (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,(∀ g ∈ gs,NOk g) → k < acc.1.length → (∃ c,acc.1.getD k (Sum.inl false)=Sum.inl c) → (∃ g ∈ gs,k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length:=by
 induction gs with
 | nil=>intro acc _ _ _ h;obtain ⟨g,hg,_⟩:=h;simp at hg
 | cons g gs ih =>
  intro acc hok hk hc hex;have h3 : elim n (g :: gs) acc=elim n gs (elimStep n acc g):=rfl;rw [h3,List.length_cons]
  by_cases hkg : k ∈ g.inputs
  · obtain ⟨c,hc⟩:=hc;have hnok:=hok g List.mem_cons_self
    have hnone : (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1=none:=by
     apply p10
     · exact hnok.1.1
     · simpa using hnok.1.2
     · intro h;simpa using hnok.2 h
     · exact ⟨c,List.mem_map.2 ⟨k,hkg,hc⟩⟩
    have h2 : (elimStep n acc g).2.length=acc.2.length:=by
     show (acc.2 ++ (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1.toList).length=_;rw [hnone];simp
    have:=elim_len n gs (elimStep n acc g);omega
  · have hex' : ∃ g' ∈ gs,k ∈ g'.inputs:=by
     obtain ⟨g',hg',hk'⟩:=hex
     rcases List.mem_cons.1 hg' with rfl | h
     · exact absurd hk' hkg
     · exact ⟨g',h,hk'⟩
    have h1:=ih (elimStep n acc g) (fun g' hg'=>hok g' (List.mem_cons_of_mem _ hg'))
     (by simp [elimStep];omega)
     (by
      obtain ⟨c,hc⟩:=hc;refine ⟨c,?_⟩
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)];exact hc)
     hex'
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1:=by
     simp only [elimStep,List.length_append];have:=toList_length_le (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1;omega
    omega
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat,s.Valid m → s.Valid m'
 | Sum.inl _,_=>trivial
 | Sum.inr _,hj=>lt_of_lt_of_le hj h
theorem Stat.val_append (w t : List Bool) : ∀ s : Stat,s.Valid w.length → s.val (w ++ t)=s.val w
 | Sum.inl _,_=>rfl
 | Sum.inr _,hj=>List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
 acc.1.length=w.length ∧ ∀ i : ℕ,
  (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
  (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y)=w.getD i false
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length=n) (gs : List Gate) : ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) → Inv n y w acc → Inv n y (wiresFrom gs w) (elim n gs acc):=by
 induction gs with
 | nil=>intro w acc _ h;exact h
 | cons g gs ih =>
  intro w acc hok h;apply ih (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]) (elimStep n acc g)
   (fun g' hg'=>hok g' (List.mem_cons_of_mem _ hg'))
  obtain ⟨hl,hi⟩:=h
  set w':=wiresFrom acc.2 y with hw'
  have lw' : w'.length=n + acc.2.length:=by rw [hw',length_wiresFrom,hy]
  set ins:=g.inputs.map fun i=>acc.1.getD i (Sum.inl false) with hins
  have hgok:=hok g List.mem_cons_self
  have hs:=p14 g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
   (by
    intro s hs;obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
    rw [lw'];exact (hi a).1)
  rw [lw'] at hs
  set r:=simplify g.op (n + acc.2.length) ins with hr
  have hvals : ins.map (Stat.val w')=g.inputs.map fun i=>w.getD i false:=by
   rw [hins,List.map_map];apply List.map_congr_left;intro a _;exact (hi a).2
  have hnew : wiresFrom (acc.2 ++ r.1.toList) y=wiresFrom r.1.toList w':=by rw [wiresFrom_append]
  obtain ⟨t,ht,htl⟩:=p9 r.1.toList w'
  refine ⟨by simp [elimStep,hl],?_⟩
  intro i;show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
   ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y)=_
  rw [hnew,List.length_append,← Nat.add_assoc]
  by_cases hil : i=acc.1.length
  · subst hil;rw [getD_snoc_eq,hl,getD_snoc_eq]
    exact ⟨hs.1,by rw [hs.2,hvals]⟩
  · rw [getD_snoc_ne _ _ _ _ hil,getD_snoc_ne _ _ _ _ (by omega)]
    refine ⟨Stat.valid_mono (by omega) _ (hi i).1,?_⟩
    rw [ht,Stat.val_append _ _ _ (by rw [lw'];exact (hi i).1)]
    exact (hi i).2
def p2a (n : ℕ) (b : Bool) : List Stat :=
 List.ofFn (fun i : Fin n=>(Sum.inr (i : ℕ) : Stat)) ++ [(Sum.inl b : Stat)]
theorem p33 (n : ℕ) (b : Bool) (y : Fin n → Bool) : Inv n (List.ofFn y) (List.ofFn y ++ [b]) (p2a n b,[]):=by
 refine ⟨by simp [p2a],?_⟩
 intro i
 have l1 : (List.ofFn (fun i : Fin n=>(Sum.inr (i : ℕ) : Stat))).length=n:=by simp
 have l2 : (List.ofFn y).length=n:=by simp
 by_cases hin : i=n
 · subst hin
   simp only [p2a];rw [getD_snoc_len _ _ _ _ l1,getD_snoc_len _ _ _ _ l2];exact ⟨trivial,rfl⟩
 · simp only [p2a]
   rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)]
   by_cases hlt : i < n
   · simp [hlt,Stat.Valid,Stat.val,wiresFrom]
   · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
     exact ⟨trivial,rfl⟩
theorem p2f (n : ℕ) (y : Fin n → Bool) (b : Bool) : List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)=List.ofFn y ++ [b]:=by{
rw [List.ofFn_succ']
simp
}
theorem p25 (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),(∀ g ∈ gs,n ∉ g.inputs) → (∀ j : ℕ,j ≠ n → Fin.last n ∉ L.getD j ∅) → ∀ j : ℕ,j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅:=by{
induction gs with
| nil=>intro L _ h;exact h
| cons g gs ih =>{
intro L hno h;apply ih (L ++ [gateSupp L g]) (fun g' hg'=>hno g' (List.mem_cons_of_mem _ hg'));intro j hj
by_cases hjl : j=L.length
{subst hjl;rw [getD_snoc_eq];intro hmem;obtain ⟨a,ha,hia⟩:=(mem_gateSupp L g _).1 hmem;exact h a (fun e=>hno g List.mem_cons_self (e ▸ ha)) hia}
{rw [getD_snoc_ne _ _ _ _ hjl];exact h j hj}
}
}
theorem pc (m j : ℕ) (h : j < m) : (inputSupps m).getD j ∅={⟨j,h⟩}:=by simp [inputSupps,h]
theorem p7 (n : ℕ) : ∀ j : ℕ,j ≠ n → Fin.last n ∉ (inputSupps (n + 1)).getD j ∅:=by
 intro j hj
 by_cases hlt : j < n + 1
 · have e : (inputSupps (n + 1)).getD j ∅={⟨j,hlt⟩}:=pc (n + 1) j hlt;rw [e,Finset.mem_singleton];intro e'
   exact hj (by have:=congrArg Fin.val e';simpa using this.symm)
 · rw [List.getD_eq_default _ _ (by simp [inputSupps];omega)];simp
open PEqualNP.CircuitLowerBounds
theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) : elim n (g :: gs) acc=elim n gs (elimStep n acc g):=rfl
theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) : elim n (pre ++ post) acc=elim n post (elim n pre acc):=by simp [elim,List.foldl_append]
theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,(elim n gs acc).1.length=acc.1.length + gs.length:=by{
induction gs with
| nil=>intro acc;rfl
| cons g gs ih =>{
intro acc;rw [elim_cons,ih];simp only [elimStep,List.length_append,List.length_cons,List.length_nil];omega
}
}
theorem p15 (n : ℕ) (b : Bool) : (p2a n b).getD n (Sum.inl false)=Sum.inl b :=
 getD_snoc_len _ _ _ _ (by simp)
theorem pf (op : GateOp) (m : ℕ) (ins : List Stat) (hop : op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not) (hlen : ins.length ≤ 2) (hnot : op=GateOp.not → ins.length ≤ 1) (b : Bool) (hand : op=GateOp.and → b=false) (hor : op=GateOp.or → b=true) (hc : Sum.inl b ∈ ins) : ∃ c,(simplify op m ins).2=Sum.inl c:=by
 rcases hop with rfl | rfl | rfl
 · have:=hand rfl;subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
    simp_all [simplify,simpAnd]
 · have:=hor rfl;subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
    simp_all [simplify,simpOr]
 · have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨d,l⟩⟩ <;> (try cases a) <;> simp_all [simplify,simpNot]
theorem p19 (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ) (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false)=Sum.inl c) : (elimStep n acc g).2.length=acc.2.length:=by{
have hnone : (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1=none:=by{
apply p10
{exact hg.1.1}
{simpa using hg.1.2}
{intro h;simpa using hg.2 h}
{exact ⟨c,List.mem_map.2 ⟨k,hk,hc⟩⟩}
}
show (acc.2 ++ (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1.toList).length=_;rw [hnone];simp
}
def fixBit (g : Gate) : Bool :=
 match g.op with
 | GateOp.or=>true
 | _=>false
theorem p13 (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ) (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false)=Sum.inl (fixBit g)) : ∃ c,(elimStep n acc g).1.getD acc.1.length (Sum.inl false)=Sum.inl c:=by
 have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).2:=getD_snoc_eq _ _ _
 rw [e]
 apply pf _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h=>by simpa using hg.2 h)
  (fixBit g)
 · intro h;simp [fixBit,h]
 · intro h;simp [fixBit,h]
 · exact List.mem_map.2 ⟨k,hk,hc⟩
theorem pa {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) : suppsFrom (pre ++ post) L=suppsFrom post (suppsFrom pre L):=by simp [suppsFrom,List.foldl_append]
theorem pb {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),(suppsFrom gs L).length=L.length + gs.length:=by{
induction gs with
| nil=>intro L;rfl
| cons g gs ih =>{
intro L;have h : suppsFrom (g :: gs) L=suppsFrom gs (L ++ [gateSupp L g]):=rfl;rw [h,ih];simp only [List.length_append,List.length_cons,List.length_nil];omega
}
}
theorem p1e (n : ℕ) (D : ℕ → Prop) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),(∀ g ∈ gs,∀ a ∈ g.inputs,¬ D a) → (∀ j : ℕ,¬ D j → Fin.last n ∉ L.getD j ∅) → ∀ j : ℕ,¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅:=by{
induction gs with
| nil=>intro L _ h;exact h
| cons g gs ih =>{
intro L hno h;apply ih (L ++ [gateSupp L g]) (fun g' hg'=>hno g' (List.mem_cons_of_mem _ hg'));intro j hj
by_cases hjl : j=L.length
{subst hjl;rw [getD_snoc_eq];intro hmem;obtain ⟨a,ha,hia⟩:=(mem_gateSupp L g _).1 hmem;exact h a (hno g List.mem_cons_self a ha) hia}
{rw [getD_snoc_ne _ _ _ _ hjl];exact h j hj}
}
}
theorem p2d (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs,NOk g) (o : ℕ) (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅) (hout : ∀ b c,(elim n gs (p2a n b,[])).1.getD o (Sum.inl false) ≠ Sum.inl c) : ∃ b,(elim n gs (p2a n b,[])).2.length + 2 ≤ gs.length:=by
 have hon : o ≠ n:=by
  intro e;apply hout false false
  rw [e,p2b n n _ gs _ (by simp [p2a])]
  exact p15 n false
 by_cases hread : ∃ g ∈ gs,n ∈ g.inputs
 swap
 · exfalso;push Not at hread;exact p25 n gs (inputSupps (n + 1)) hread (p7 n) o hon hdep
 obtain ⟨g,hg,hng⟩:=hread;obtain ⟨pre,post,rfl⟩:=List.append_of_mem hg;have hgn : NOk g:=hnok g hg;have hpren : ∀ g' ∈ pre,NOk g':=fun g' h=>hnok g' (List.mem_append_left _ h)
 have hpostn : ∀ g' ∈ post,NOk g' :=
  fun g' h=>hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have hsplit : ∀ b,elim n (pre ++ g :: post) (p2a n b,[]) = elim n post (elimStep n (elim n pre (p2a n b,[])) g) :=
  fun b=>by rw [elim_append,elim_cons]
 have hAn : ∀ b,(elim n pre (p2a n b,[])).1.getD n (Sum.inl false)=Sum.inl b:=by
  intro b
  rw [p2b n n _ pre _ (by simp [p2a])]
  exact p15 n b
 have hAl : ∀ b,(elim n pre (p2a n b,[])).1.length=n + 1 + pre.length:=by
  intro b;rw [elim_fst_len];simp [p2a]
 have hA2 : ∀ b,(elim n pre (p2a n b,[])).2.length ≤ 0 + pre.length :=
  fun b=>elim_len n pre (p2a n b,[])
 have hB2:=fun b=>p19 n (elim n pre (p2a n b,[])) g hgn n hng b (hAn b);have hBl : ∀ b,(elimStep n (elim n pre (p2a n b,[])) g).1.length
  = n + 1 + pre.length + 1:=by
  intro b;simp [elimStep,hAl b]
 have hBn : ∀ b,(elimStep n (elim n pre (p2a n b,[])) g).1.getD n (Sum.inl false) = Sum.inl b:=by
  intro b;show ((elim n pre (p2a n b,[])).1 ++ [_]).getD n _=_
  rw [getD_snoc_ne _ _ _ _ (by rw [hAl b];omega)]
  exact hAn b
 have hF:=fun b=>elim_len n post (elimStep n (elim n pre (p2a n b,[])) g)
 have hlen : (pre ++ g :: post).length=pre.length + post.length + 1:=by simp only [List.length_append,List.length_cons];omega
 by_cases h1 : ∃ g' ∈ pre,n ∈ g'.inputs
 · refine ⟨false,?_⟩
   have a1 : (elim n pre (p2a n false,[])).2.length + 1 ≤ 0 + pre.length :=
    p23 n n pre (p2a n false,[]) hpren (by simp [p2a])
     ⟨false,p15 n false⟩ h1
   have:=hF false;have:=hB2 false;rw [hsplit,hlen];omega
 by_cases h2 : ∃ g' ∈ post,n ∈ g'.inputs
 · refine ⟨false,?_⟩
   have a1:=p23 n n post (elimStep n (elim n pre (p2a n false,[])) g) hpostn
    (by rw [hBl];omega) ⟨false,hBn false⟩ h2
   have:=hA2 false;have:=hB2 false;rw [hsplit,hlen];omega
 obtain ⟨c,hc⟩:=p13 n (elim n pre (p2a n (fixBit g),[])) g hgn n hng
  (hAn (fixBit g))
 rw [hAl (fixBit g)] at hc;refine ⟨fixBit g,?_⟩
 by_cases h3 : ∃ g' ∈ post,(n + 1 + pre.length) ∈ g'.inputs
 · have a1:=p23 n (n + 1 + pre.length) post
    (elimStep n (elim n pre (p2a n (fixBit g),[])) g) hpostn
    (by rw [hBl];omega) ⟨c,hc⟩ h3
   have:=hA2 (fixBit g);have:=hB2 (fixBit g);rw [hsplit,hlen];omega
 · exfalso
   have hom : o ≠ n + 1 + pre.length:=by
    intro e;apply hout (fixBit g) c
    rw [hsplit,e,p2b n _ _ post _ (by rw [hBl];omega)]
    exact hc
   push Not at h1 h2 h3;have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
    = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
     ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]):=by
    rw [pa];rfl
   rw [hs] at hdep;have hL:=p25 n pre (inputSupps (n + 1)) h1 (p7 n)
   have hLl : (suppsFrom pre (inputSupps (n + 1))).length=n + 1 + pre.length:=by
    rw [pb];simp [inputSupps]
   refine p1e n (fun j=>j=n ∨ j=n + 1 + pre.length) post _ ?_ ?_ o
    (by simp [hon,hom]) hdep
   · intro g' hg' a ha hD
     rcases hD with rfl | rfl
     · exact h2 g' hg' ha
     · exact h3 g' hg' ha
   · intro j hj
     have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length:=by
      constructor
      · exact fun e=>hj (Or.inl e)
      · exact fun e=>hj (Or.inr e)
     rw [getD_snoc_ne _ _ _ _ (by rw [hLl];exact hj'.2)]
     exact hL j hj'.1
theorem p1b (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ x : Fin (n + 1) → Bool,f (update x (Fin.last n) (!x (Fin.last n))) ≠ f x) (hnc : ∀ b : Bool,∃ y y' : Fin n → Bool,f (Fin.snoc y b) ≠ f (Fin.snoc y' b)) (h : HasCircuitSize (n + 1) f s) : ∃ (b : Bool) (s' : ℕ),s' + 2 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool=>f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h;have hsz' : C.gates.length ≤ s:=hsz
 set gs:=C.gates.map normGate with hgs
 have hl : gs.length=C.gates.length:=by simp [hgs]
 have hnok : ∀ g ∈ gs,NOk g:=by
  intro g hg;obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg;exact normGate_nok g0 (ok g0 hg0)
 have hevg : ∀ x : Fin (n + 1) → Bool,(wiresFrom gs (List.ofFn x)).getD C.output false=f x:=by
  intro x;rw [hgs,wiresFrom_norm,← hev x];rfl
 have hinv : ∀ (b : Bool) (y : Fin n → Bool), Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) (elim n gs (p2a n b,[])):=by
  intro b y;rw [p2f]
  exact inv_elim n _ (by simp) gs _ _ (fun g hg=>(hnok g hg).1) (p33 n b y)
 have hval : ∀ (b : Bool) (y : Fin n → Bool), ((elim n gs (p2a n b,[])).1.getD C.output (Sum.inl false)).val (wiresFrom (elim n gs (p2a n b,[])).2 (List.ofFn y))=f (Fin.snoc y b):=by
  intro b y;rw [((hinv b y).2 C.output).2,hevg]
 have hout : ∀ b c, (elim n gs (p2a n b,[])).1.getD C.output (Sum.inl false) ≠ Sum.inl c:=by
  intro b c hst;obtain ⟨y,y',hne⟩:=hnc b;apply hne;rw [← hval b y,← hval b y',hst];rfl
 have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅:=by
  by_contra hns
  obtain ⟨x,hx⟩:=hdep;apply hx
  have hag:=(agree_wiresFrom (update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _ (agree_inputs _ _)).2.2 C.output (by
   intro k hk;have : k ≠ Fin.last n:=fun e=>hns (e ▸ hk)
   simp [Function.update_of_ne this])
  rw [← hevg,← hevg];exact hag
 obtain ⟨b,hb⟩:=p2d n gs hnok C.output hsupp hout
 cases hst : (elim n gs (p2a n b,[])).1.getD C.output (Sum.inl false) with
 | inl c=>exact absurd hst (hout b c)
 | inr j =>
  refine ⟨b,(elim n gs (p2a n b,[])).2.length,by omega,
   ⟨(elim n gs (p2a n b,[])).2,j⟩,elim_ok n gs _ (by simp),le_refl _,?_⟩
  intro y;have:=hval b y;rw [hst] at this;exact this
open PEqualNP.CircuitLowerBounds
def CleanGate (m : ℕ) (g : Gate) : Prop :=
 (g.op=GateOp.not ∧ ∃ j,j < m ∧ g.inputs=[j]) ∨
 ((g.op=GateOp.and ∨ g.op=GateOp.or) ∧ ∃ j k,j < m ∧ k < m ∧ g.inputs=[j,k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
 ∀ (p : ℕ) (g : Gate),gs[p]?=some g → CleanGate (m + p) g
theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g:=by{
rcases h with ⟨h1,j,_,h2⟩ | ⟨h1 | h1,j,k,_,_,h2⟩
{
refine ⟨⟨?_,?_⟩,?_⟩
{rw [h1];exact Or.inr (Or.inr rfl)}
{rw [h2];simp}
{intro _;rw [h2];simp}
}
{
refine ⟨⟨?_,?_⟩,?_⟩
{rw [h1];exact Or.inl rfl}
{rw [h2];simp}
{intro h;rw [h1] at h;cases h}
}
{
refine ⟨⟨?_,?_⟩,?_⟩
{rw [h1];exact Or.inr (Or.inl rfl)}
{rw [h2];simp}
{intro h;rw [h1] at h;cases h}
}
}
theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs,a < m:=by{
intro a ha
rcases h with ⟨_,j,hj,h2⟩ | ⟨_,j,k,hj,hk,h2⟩
{
rw [h2] at ha
simp at ha
subst ha;exact hj
}
{
rw [h2] at ha
simp at ha
rcases ha with rfl | rfl
{exact hj}
{exact hk}
}
}
theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs,NOk g:=by{
intro g hg;obtain ⟨p,hp⟩:=List.mem_iff_getElem?.1 hg;exact (h p g hp).nok
}
theorem p12 (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins,s.Valid m) : ∀ g ∈ (simplify op m ins).1,CleanGate m g:=by
 intro g hg
 cases op <;> simp only [simplify] at hg
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp [simpAnd] at hg
   subst hg;refine Or.inr ⟨Or.inl rfl,_,_,?_,?_,rfl⟩
   · exact hv _ List.mem_cons_self
   · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
 · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp [simpOr] at hg
   subst hg;refine Or.inr ⟨Or.inr rfl,_,_,?_,?_,rfl⟩
   · exact hv _ List.mem_cons_self
   · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
 · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [simpNot] at hg
   subst hg;refine Or.inl ⟨rfl,_,?_,rfl⟩
   exact hv _ List.mem_cons_self
 · simp at hg
 · simp at hg
theorem p11? {α : Type} (o : Option α) (k : ℕ) (a : α) (h : o.toList[k]?=some a) : k=0 ∧ a ∈ o:=by{
cases o with
| none=>simp at h
| some b =>{
cases k with
| zero=>simp at h;simp [h]
| succ k=>simp at h
}
}
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length=n) (gs : List Gate) : ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) → Inv n y w acc → CleanL n acc.2 → CleanL n (elim n gs acc).2:=by
 induction gs with
 | nil=>intro w acc _ _ h;exact h
 | cons g gs ih =>
  intro w acc hok hinv hcl
  have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
   inv_elim n y hy [g] w acc (fun g' hg'=>hok g' (by simp at hg';simp [hg'])) hinv
  refine ih _ (elimStep n acc g) (fun g' hg'=>hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
  intro p g' hp;have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1.toList)[p]?=some g':=hp
  by_cases hlt : p < acc.2.length
  · rw [List.getElem?_append_left hlt] at hp'
    exact hcl p g' hp'
  · rw [List.getElem?_append_right (by omega)] at hp'
    obtain ⟨h0,hmem⟩:=p11? _ _ _ hp'
    have hpl : p=acc.2.length:=by omega
    rw [hpl]
    exact p12 _ _ _ (fun s hs=>by
     obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
     exact (hinv.2 a).1) g' hmem
def p34 (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
 ∃ (gs : List Gate) (o : ℕ),CleanL n gs ∧ gs.length ≤ s ∧
  ∀ x : Fin n → Bool,(wiresFrom gs (List.ofFn x)).getD o false=f x
def idStats (n : ℕ) : List Stat:=List.ofFn (fun i : Fin n=>(Sum.inr (i : ℕ) : Stat))
theorem inv_id (n : ℕ) (y : Fin n → Bool) : Inv n (List.ofFn y) (List.ofFn y) (idStats n,[]):=by
 refine ⟨by simp [idStats],?_⟩
 intro i
 by_cases hlt : i < n
 · simp [idStats,hlt,Stat.Valid,Stat.val,wiresFrom]
 · rw [List.getD_eq_default _ _ (by simp [idStats];omega),List.getD_eq_default _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
theorem p35 (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) (hnc : ∃ y y' : Fin n → Bool,f y ≠ f y') (h : HasCircuitSize n f s) : p34 n f s:=by
 obtain ⟨C,ok,hsz,hev⟩:=h;have hsz' : C.gates.length ≤ s:=hsz;have hok : ∀ g ∈ C.gates,Ok g:=ok
 set acc:=elim n C.gates (idStats n,[]) with hacc
 have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
  fun y=>inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
 have hval : ∀ y : Fin n → Bool, (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))=f y:=by
  intro y;rw [((hinv y).2 C.output).2,← hev y];rfl
 cases hst : acc.1.getD C.output (Sum.inl false) with
 | inl c =>
  exfalso;obtain ⟨y,y',hne⟩:=hnc;apply hne;rw [← hval y,← hval y',hst];rfl
 | inr j =>
  refine ⟨acc.2,j,?_,?_,?_⟩
  · exact clean_elim n (List.ofFn fun _ : Fin n=>false) (by simp) C.gates _ _ hok
     (inv_id n _) (by intro p g hp;simp at hp)
  · have:=elim_len n C.gates (idStats n,[]);rw [← hacc] at this;simp only [List.length_nil,zero_add] at this;omega
  · intro y;have:=hval y;rw [hst] at this;exact this
theorem p2e {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) : (List.ofFn F).getD j d=F j:=by simp
def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
 List.ofFn (Fin.insertNth i (Sum.inl b) (fun k : Fin n=>Sum.inr k) : Fin (n + 1) → Stat)
theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length=n + 1:=by simp [statAt]
theorem p31 (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).getD i (Sum.inl false)=Sum.inl b:=by rw [statAt,p2e,Fin.insertNth_apply_same]
theorem p1c (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) : (statAt n i b).getD (i.succAbove k) (Sum.inl false)=Sum.inr (k : ℕ):=by rw [statAt,p2e,Fin.insertNth_apply_succAbove]
theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)) (statAt n i b,[]):=by
 refine ⟨by simp [statAt],?_⟩
 have key : ∀ j : Fin (n + 1), ((statAt n i b).getD j (Sum.inl false)).Valid (n + 0) ∧ ((statAt n i b).getD j (Sum.inl false)).val (List.ofFn y) = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false:=by
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k,rfl⟩
  · rw [p31,p2e,Fin.insertNth_apply_same];exact ⟨trivial,rfl⟩
  · rw [p1c,p2e,Fin.insertNth_apply_succAbove];refine ⟨?_,?_⟩
    · show (k : ℕ) < n + 0;have:=k.isLt;omega
    · show (List.ofFn y).getD k false=y k;exact p2e n y false k
 intro j
 by_cases hlt : j < n + 1
 · exact key ⟨j,hlt⟩
 · show ((statAt n i b).getD j (Sum.inl false)).Valid (n + 0) ∧
    ((statAt n i b).getD j (Sum.inl false)).val (List.ofFn y)
     = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
   rw [List.getD_eq_default _ _ (by rw [statAt_length];omega),List.getD_eq_default _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
 (elim n gs (statAt n i b,[])).1.getD a (Sum.inl false)
theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : stF n gs i b i=Sum.inl b:=by
 show (elim n gs (statAt n i b,[])).1.getD i (Sum.inl false)=_
 rw [p2b n i _ gs _ (by
  show (i : ℕ) < (statAt n i b).length
  rw [statAt_length];exact i.isLt)]
 exact p31 n i b
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α),l[p]?=some g → ∃ pre post,l=pre ++ g :: post ∧ pre.length=p:=by{
intro l
induction l with
| nil=>intro p g h;simp at h
| cons x l ih =>{
intro p g h
cases p with
| zero =>{
simp at h
subst h;exact ⟨[],l,rfl,rfl⟩
}
| succ p =>{
simp at h
obtain ⟨pre,post,rfl,rfl⟩:=ih p g h;exact ⟨x :: pre,post,rfl,rfl⟩
}
}
}
theorem pe (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) : (elim n (pre ++ g :: post) acc).1.getD a d=(elimStep n (elim n pre acc) g).1.getD a d:=by
 rw [elim_append,elim_cons,p2b n a d post _ (by
  show a < ((elim n pre acc).1 ++ [_]).length
  rw [List.length_append,elim_fst_len,List.length_singleton];omega)]
theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) : (elim n (pre ++ g :: post) acc).1.getD a d=(elim n pre acc).1.getD a d:=by
 rw [pe n pre g post acc a d (le_of_lt h)];show ((elim n pre acc).1 ++ [_]).getD a d=_
 exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len];omega)
theorem p18 (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate) (hp : gs[p]?=some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs) (hlt : a < acc.1.length + p) (hc : (elim n gs acc).1.getD a (Sum.inl false)=Sum.inl (fixBit g)) : ∃ c,(elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false)=Sum.inl c:=by{
obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp;rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc;obtain ⟨c,hc'⟩:=p13 n (elim n pre acc) g hg a ha hc;refine ⟨c,?_⟩
rw [pe n pre g post acc _ _ (le_refl _)];rw [elim_fst_len] at hc';exact hc'
}
theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,(∀ g ∈ gs,NOk g) → ∀ S : Finset ℕ,(∀ p ∈ S,∃ g,gs[p]?=some g ∧ ∃ a ∈ g.inputs,a < acc.1.length + p ∧ ∃ c,(elim n gs acc).1.getD a (Sum.inl false)=Sum.inl c) → (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length:=by
 intro gs
 induction gs using List.reverseRecOn with
 | nil =>
  intro _ S hS
  have hE : S=∅:=by
   apply Finset.eq_empty_of_forall_notMem;intro p hp;obtain ⟨g,hg,_⟩:=hS p hp
   simp at hg
  subst hE;simp [elim]
 | append_singleton gs g ih =>
  intro hok S hS
  have hstep : elim n (gs ++ [g]) acc=elimStep n (elim n gs acc) g:=by rw [elim_append];rfl
  have hpre : ∀ (a : ℕ) (d : Stat),a < acc.1.length + gs.length → (elim n (gs ++ [g]) acc).1.getD a d=(elim n gs acc).1.getD a d :=
   fun a d h=>elim_split_getD_lt n gs g [] acc a d h
  have hok' : ∀ g' ∈ gs,NOk g':=fun g' h=>hok g' (List.mem_append_left _ h)
  have ih':=ih hok' (S.erase gs.length) (by
   intro p hp;obtain ⟨hne,hpS⟩:=Finset.mem_erase.1 hp;obtain ⟨g',hg',a,ha,hlt,c,hc⟩:=hS p hpS
   have hpl : p < gs.length:=by
    obtain ⟨h1,_⟩:=List.getElem?_eq_some_iff.1 hg'
    rw [List.length_append,List.length_singleton] at h1;omega
   rw [List.getElem?_append_left hpl] at hg'
   rw [hpre a _ (by omega)] at hc
   exact ⟨g',hg',a,ha,hlt,c,hc⟩)
  rw [hstep,List.length_append,List.length_singleton]
  by_cases hin : gs.length ∈ S
  · obtain ⟨g',hg',a,ha,hlt,c,hc⟩:=hS _ hin
    have hgg : g'=g:=by
     rw [List.getElem?_concat_length] at hg'
     exact (Option.some.inj hg').symm
    subst hgg;rw [hpre a _ hlt] at hc
    have h2:=p19 n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
    have hcard:=Finset.card_erase_of_mem hin
    have hpos : 1 ≤ S.card:=Finset.card_pos.2 ⟨_,hin⟩;omega
  · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1:=by
     simp only [elimStep,List.length_append];have:=toList_length_le (simplify g.op (n + (elim n gs acc).2.length) (g.inputs.map fun i=>(elim n gs acc).1.getD i (Sum.inl false))).1;omega
    rw [Finset.erase_eq_of_notMem hin] at ih';omega
theorem p20 (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,(∀ g ∈ gs,k ∉ g.inputs) → w.length=w'.length → (∀ j,j ≠ k → w.getD j false=w'.getD j false) → ∀ j,j ≠ k → (wiresFrom gs w).getD j false=(wiresFrom gs w').getD j false:=by
 induction gs with
 | nil=>intro w w' _ _ h;exact h
 | cons g gs ih =>
  intro w w' hno hl h;have hno':=hno g List.mem_cons_self
  have e : (g.inputs.map fun i=>w.getD i false)=g.inputs.map fun i=>w'.getD i false :=
   List.map_congr_left (fun a ha=>h a (fun e=>hno' (e ▸ ha)))
  apply ih (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)])
   (w' ++ [g.op.eval (g.inputs.map fun i=>w'.getD i false)])
   (fun g' hg'=>hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
  intro j hj
  by_cases hjl : j=w.length
  · rw [hjl,getD_snoc_eq,hl,getD_snoc_eq,e]
  · rw [getD_snoc_ne _ _ _ _ hjl,getD_snoc_ne _ _ _ _ (by omega)]
    exact h j hj
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
 ∃ g,gs[p]?=some g ∧ ∃ a ∈ g.inputs,∃ c,stF n gs i b a=Sum.inl c
open PEqualNP.CircuitLowerBounds
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
 (wiresFrom gs (List.ofFn u)).getD j false
theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) : vl gs u j=u ⟨j,h⟩:=by
 unfold vl
 rw [getD_wiresFrom gs _ j (by simpa using h)]
 exact p2e k u false ⟨j,h⟩
theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate) (hp : gs[p]?=some g) : vl gs u (k + p)=g.op.eval (g.inputs.map (vl gs u)):=by
 have hlt:=(hcl p g hp).lt;obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp
 have hwl : (wiresFrom pre (List.ofFn u)).length=k + pre.length:=by rw [length_wiresFrom];simp
 have e : wiresFrom (pre ++ g :: post) (List.ofFn u) = wiresFrom post (wiresFrom pre (List.ofFn u) ++ [g.op.eval (g.inputs.map fun i=>(wiresFrom pre (List.ofFn u)).getD i false)]):=by
  rw [wiresFrom_append];rfl
 have full : ∀ j,j < k + pre.length → (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false = (wiresFrom pre (List.ofFn u)).getD j false:=by
  intro j hj
  rw [e,getD_wiresFrom _ _ j (by simp [hwl];omega),getD_snoc_ne _ _ _ _ (by omega)]
 have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false = g.op.eval (g.inputs.map fun i=>(wiresFrom pre (List.ofFn u)).getD i false):=by
  rw [e,getD_wiresFrom _ _ _ (by simp [hwl]),getD_snoc_len _ _ _ _ hwl]
 show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
  = g.op.eval (g.inputs.map fun j=>(wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
 rw [top];congr 1;apply List.map_congr_left;intro a ha;exact (full a (hlt a ha)).symm
theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ) (g : Gate) (hp : gs[p]?=some g) (h : ∀ a ∈ g.inputs,vl gs u a=vl gs u' a) : vl gs u (k + p)=vl gs u' (k + p):=by{
rw [vl_gate gs hcl u p g hp,vl_gate gs hcl u' p g hp];congr 1;exact List.map_congr_left h
}
theorem p37 {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (B : ℕ → Prop) (L : ℕ) (hin : ∀ j,j < k → ¬ B j → vl gs u j=vl gs u' j) (hstep : ∀ p g,gs[p]?=some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs,B a) → (∀ j,j < k + p → ¬ B j → vl gs u j=vl gs u' j) → vl gs u (k + p)=vl gs u' (k + p)) : ∀ j,j < L → ¬ B j → vl gs u j=vl gs u' j:=by
 intro j
 induction j using Nat.strong_induction_on with
 | _ j ih =>
  intro hjL hB
  by_cases hjk : j < k
  · exact hin j hjk hB
  · obtain ⟨p,rfl⟩ : ∃ p,j=k + p:=⟨j - k,by omega⟩
    cases hp : gs[p]? with
    | none =>
     have hlen : gs.length ≤ p:=List.getElem?_eq_none_iff.1 hp
     have h1 : ∀ v : Fin k → Bool,vl gs v (k + p)=false:=by
      intro v;unfold vl
      exact List.getD_eq_default _ _ (by rw [length_wiresFrom];simp;omega)
     rw [h1,h1]
    | some g =>
     by_cases hr : ∃ a ∈ g.inputs,B a
     · exact hstep p g hp hjL hB hr (fun j' hj' hB'=>ih j' hj' (by omega) hB')
     · exact vl_congr gs hcl u u' p g hp (fun a ha =>
        ih a ((hcl p g hp).lt a ha) (by have:=(hcl p g hp).lt a ha;omega)
         (fun hBa=>hr ⟨a,ha,hBa⟩))
theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]?=some g) (h' : gs[q]?=some g') (e : p=q) : g=g':=by{
subst e;rw [h] at h';exact Option.some.inj h'
}
theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs) (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w=a ∨ w=b:=by
 rcases hg with ⟨_,j,_,hin⟩ | ⟨_,j,k,_,_,hin⟩ <;> rw [hin] at ha hb hw <;>
  simp at ha hb hw <;> omega
theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat) (hS : ∀ y : Fin k → Bool,S.Valid (k + (elim k pre (idStats k,[])).2.length) ∧ S.val (wiresFrom (elim k pre (idStats k,[])).2 (List.ofFn y))=vl (pre ++ g :: post) y (k + pre.length)) (hnc : ∃ y y' : Fin k → Bool,vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) : ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧ ∀ y : Fin k → Bool,vl gs' y o'=vl (pre ++ g :: post) y o:=by
 have hok : ∀ g' ∈ pre ++ g :: post,Ok g':=fun g' hg'=>(clean_nok _ _ hcl g' hg').1;have hokpre : ∀ g' ∈ pre,Ok g':=fun g' h=>hok g' (List.mem_append_left _ h)
 have hokpost : ∀ g' ∈ post,Ok g' :=
  fun g' h=>hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have inv1 : ∀ y : Fin k → Bool,Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y)) (elim k pre (idStats k,[])) :=
  fun y=>inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
 have hwl : ∀ y : Fin k → Bool,(wiresFrom pre (List.ofFn y)).length=k + pre.length:=by intro y;rw [length_wiresFrom];simp
 have hfull : ∀ y : Fin k → Bool,wiresFrom (pre ++ g :: post) (List.ofFn y) = wiresFrom post (wiresFrom pre (List.ofFn y) ++ [g.op.eval (g.inputs.map fun a=>(wiresFrom pre (List.ofFn y)).getD a false)]):=by
  intro y;rw [wiresFrom_append];rfl
 have hgv : ∀ y : Fin k → Bool,vl (pre ++ g :: post) y (k + pre.length) = g.op.eval (g.inputs.map fun a=>(wiresFrom pre (List.ofFn y)).getD a false):=by
  intro y;show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false=_
  rw [hfull,getD_wiresFrom _ _ _ (by simp [hwl y]),getD_snoc_len _ _ _ _ (hwl y)]
 have inv2 : ∀ y : Fin k → Bool,Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y) ++ [g.op.eval (g.inputs.map fun a=>(wiresFrom pre (List.ofFn y)).getD a false)]) ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2):=by
  intro y;obtain ⟨hl,hi⟩:=inv1 y
  refine ⟨by simp [hl],?_⟩
  intro a;show (((elim k pre (idStats k,[])).1 ++ [S]).getD a (Sum.inl false)).Valid
   (k + (elim k pre (idStats k,[])).2.length) ∧
   (((elim k pre (idStats k,[])).1 ++ [S]).getD a (Sum.inl false)).val
    (wiresFrom (elim k pre (idStats k,[])).2 (List.ofFn y))=_
  by_cases hal : a=(elim k pre (idStats k,[])).1.length
  · rw [hal,getD_snoc_eq,hl,getD_snoc_eq]
    exact ⟨(hS y).1,by rw [(hS y).2,hgv]⟩
  · rw [getD_snoc_ne _ _ _ _ hal,getD_snoc_ne _ _ _ _ (by omega)]
    exact hi a
 have inv3 : ∀ y : Fin k → Bool,Inv k (List.ofFn y) (wiresFrom (pre ++ g :: post) (List.ofFn y)) (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)):=by
  intro y;rw [hfull]
  exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
 have hc1 : CleanL k (elim k pre (idStats k,[])).2 :=
  clean_elim k (List.ofFn fun _ : Fin k=>false) (by simp) pre _ _ hokpre (inv_id k _)
   (by intro p g' hp;simp at hp)
 have hc3 : CleanL k (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)).2 :=
  clean_elim k (List.ofFn fun _ : Fin k=>false) (by simp) post _ _ hokpost (inv2 _) hc1
 have hlen : (elim k post ((elim k pre (idStats k,[])).1 ++ [S], (elim k pre (idStats k,[])).2)).2.length + 1 ≤ (pre ++ g :: post).length:=by
  have h1 : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)).2.length ≤ (elim k pre (idStats k,[])).2.length + post.length:=elim_len k post _
  have h2 : (elim k pre (idStats k,[])).2.length ≤ 0 + pre.length :=
   elim_len k pre (idStats k,[])
  simp only [List.length_append,List.length_cons];omega
 have hval : ∀ y : Fin k → Bool, ((elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)).1.getD o (Sum.inl false)).val (wiresFrom (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)).2 (List.ofFn y)) = vl (pre ++ g :: post) y o:=fun y=>((inv3 y).2 o).2
 cases hst : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)).1.getD o (Sum.inl false) with
 | inl c =>
  exfalso;obtain ⟨y,y',hne⟩:=hnc;apply hne;rw [← hval y,← hval y',hst];rfl
 | inr j =>
  refine ⟨_,j,hc3,hlen,?_⟩
  intro y;have h:=hval y;rw [hst] at h;exact h
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length) (hj : j < k + p) (heq : ∀ y : Fin k → Bool,vl gs y (k + p)=vl gs y j) (hnc : ∃ y y' : Fin k → Bool,vl gs y o ≠ vl gs y' o) : ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ ∀ y : Fin k → Bool,vl gs' y o'=vl gs y o:=by
 obtain ⟨g,hg⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
 obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg;apply drop_core k pre g post hcl o ((elim k pre (idStats k,[])).1.getD j (Sum.inl false))
  ?_ hnc
 intro y
 have hokpre : ∀ g' ∈ pre,Ok g' :=
  fun g' h=>(clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
 have inv1:=inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
 refine ⟨(inv1.2 j).1,?_⟩
 rw [(inv1.2 j).2,heq y];show (wiresFrom pre (List.ofFn y)).getD j false
  = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
 rw [wiresFrom_append,getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j (by rw [length_wiresFrom];simp;omega)]
theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool) (hp : p < gs.length) (heq : ∀ y : Fin k → Bool,vl gs y (k + p)=c) (hnc : ∃ y y' : Fin k → Bool,vl gs y o ≠ vl gs y' o) : ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ ∀ y : Fin k → Bool,vl gs' y o'=vl gs y o:=by{
obtain ⟨g,hg⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg;exact drop_core k pre g post hcl o (Sum.inl c) (fun y=>⟨trivial,(heq y).symm⟩) hnc
}
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
 Fin.insertNth i b y
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
 (elim n gs (statAt n i b,[])).2
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
 ∃ c,stF n gs i b a=Sum.inl c
theorem p39 (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b,[])) :=
 inv_elim n _ (by simp) gs _ _ (fun g hg=>(clean_nok _ gs hcl g hg).1) (inv_at n i b y)
theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j=Sum.inl c) (y : Fin n → Bool) : vl gs (ins i b y) j=c:=by{
have h1:=((p39 n gs hcl i b y).2 j).2;rw [show (elim n gs (statAt n i b,[])).1.getD j (Sum.inl false)=Sum.inl c from h] at h1;exact h1.symm
}
theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool) (j q : ℕ) (h : stF n gs i b j=Sum.inr q) (y : Fin n → Bool) : vl gs (ins i b y) j=vl (passG n gs i b) y q:=by{
have h1:=((p39 n gs hcl i b y).2 j).2;rw [show (elim n gs (statAt n i b,[])).1.getD j (Sum.inl false)=Sum.inr q from h] at h1;exact h1.symm
}
theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]?=some g) : ∃ t,stF n gs i b (n + 1 + p)=(simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2:=by
 have hlt:=(hcl p g hp).lt;obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp;have hL : (statAt n i b,([] : List Gate)).1.length=n + 1:=statAt_length n i b;refine ⟨(elim n pre (statAt n i b,[])).2.length,?_⟩
 have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length) = (elimStep n (elim n pre (statAt n i b,[])) g).1.getD (n + 1 + pre.length) (Sum.inl false) :=
  pe n pre g post _ _ _ (by rw [hL])
 have e2 : (elimStep n (elim n pre (statAt n i b,[])) g).1.getD (n + 1 + pre.length) (Sum.inl false) = (simplify g.op (n + (elim n pre (statAt n i b,[])).2.length) (g.inputs.map fun a=>(elim n pre (statAt n i b,[])).1.getD a (Sum.inl false))).2 :=
  getD_snoc_len _ _ _ _ (by rw [elim_fst_len,hL])
 have e3 : (g.inputs.map fun a=>(elim n pre (statAt n i b,[])).1.getD a (Sum.inl false)) = g.inputs.map (stF n (pre ++ g :: post) i b) :=
  List.map_congr_left (fun a ha =>
   (elim_split_getD_lt n pre g post _ a _ (by rw [hL];exact hlt a ha)).symm)
 rw [e1,e2,e3]
theorem p16 (op : GateOp) (t : ℕ) (ins : List Stat) (hop : op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not) (hlen : ins.length ≤ 2) (h : ∀ s ∈ ins,∃ c,s=Sum.inl c) : ∃ c,(simplify op t ins).2=Sum.inl c:=by
 rcases hop with rfl | rfl | rfl
 · rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩
   · exact ⟨_,rfl⟩
   · obtain ⟨c,rfl⟩:=h a (by simp)
     exact ⟨_,rfl⟩
   · obtain ⟨c,rfl⟩:=h a (by simp)
     obtain ⟨c',rfl⟩:=h d (by simp)
     exact ⟨_,rfl⟩
   · simp at hlen
 · rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩
   · exact ⟨_,rfl⟩
   · obtain ⟨c,rfl⟩:=h a (by simp)
     exact ⟨_,rfl⟩
   · obtain ⟨c,rfl⟩:=h a (by simp)
     obtain ⟨c',rfl⟩:=h d (by simp)
     exact ⟨_,rfl⟩
   · simp at hlen
 · rcases ins with _ | ⟨a,l⟩
   · exact ⟨_,rfl⟩
   · obtain ⟨c,rfl⟩:=h a (by simp)
     exact ⟨_,rfl⟩
theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]?=some g) (h : ∀ a ∈ g.inputs,IsC n gs i b a) : IsC n gs i b (n + 1 + p):=by
 obtain ⟨t,ht⟩:=st_gate n gs hcl i b p g hp;have hn:=(hcl p g hp).nok;obtain ⟨c,hc⟩:=p16 g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
  (by simpa using hn.1.2) (by
   intro s hs;obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hs
   exact h a ha)
 exact ⟨c,by rw [ht];exact hc⟩
theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]?=some g) (a : ℕ) (ha : a ∈ g.inputs) (hc : stF n gs i b a=Sum.inl (fixBit g)) : IsC n gs i b (n + 1 + p):=by
 have hL : (statAt n i b,([] : List Gate)).1.length=n + 1:=statAt_length n i b;have h:=p18 n gs (statAt n i b,[]) p g hp ((hcl p g hp).nok) a ha
  (by rw [hL];exact (hcl p g hp).lt a ha) hc
 rw [hL] at h;exact h
namespace PermInputs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
 if h : w < n then (π ⟨w,h⟩ : ℕ) else w - n + m
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
 ⟨g.op,g.inputs.map (wmap n m π)⟩
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
 ⟨C.gates.map (relGate n m π),wmap n m π C.output⟩
def step (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
 n ≤ W.length ∧ W'.length + n=W.length + m ∧
  ∀ w : ℕ,W'.getD (wmap n m π w) false=W.getD w false
theorem p36 (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate) (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)):=by
 obtain ⟨h1,h2,h3⟩:=h;have hv : (relGate n m π g).op.eval
  ((relGate n m π g).inputs.map fun i=>W'.getD i false)
  = g.op.eval (g.inputs.map fun i=>W.getD i false):=by
  simp only [relGate,List.map_map];congr 1;apply List.map_congr_left;intro a _;exact h3 a
 refine ⟨by simp [step];omega,by simp [step];omega,?_⟩
 intro w;simp only [step,hv]
 rcases Nat.lt_trichotomy w W.length with hw | hw | hw
 · have hlt : wmap n m π w < W'.length:=by
    unfold wmap
    split
    · have:=(π ⟨w,by assumption⟩).2;omega
    · omega
   rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hw];exact h3 w
 · have he : wmap n m π w=W'.length:=by
    unfold wmap
    split
    · omega
    · omega
   rw [he,hw,getD_snoc_eq,getD_snoc_eq]
 · have hge : W'.length + 1 ≤ wmap n m π w:=by
    unfold wmap
    split
    · omega
    · omega
   rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) : ∀ W W' : List Bool,Rel n m π W W' → Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W'):=by{
induction gs with
| nil=>intro W W' h;exact h
| cons g gs ih =>{
intro W W' h;exact ih _ _ (p36 n m π W W' g h)
}
}
theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) : Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x):=by
 refine ⟨by simp,by simp;omega,?_⟩
 intro w;unfold wmap
 split
 · rename_i hw
   rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)]
   simp
 · rename_i hw
   rw [List.getD_eq_default _ _ (by simp),List.getD_eq_default _ _ (by simp;omega)]
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ) (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x=>h (x ∘ π)) s:=by{
obtain ⟨C,ok,hsz,hev⟩:=hc;refine ⟨relabel n m π C,?_,?_,?_⟩
{
intro g hg;obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
exact ⟨(ok g0 hg0).1,by simpa [relGate] using (ok g0 hg0).2⟩
}
{simpa [relabel,Circuit.size] using hsz}
{intro x;show _=h (x ∘ π);rw [← hev (x ∘ π)];have:=(rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output;exact this}
}
theorem p2c (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) : (Fin.snoc (fun j : Fin n=>x (Equiv.swap p (Fin.last n) j.castSucc)) b : Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))=update x p b:=by{
funext j;simp only [Function.comp_apply]
by_cases hj : j=p
{subst hj;rw [Equiv.swap_apply_left,Fin.snoc_last,Function.update_self]}
{
have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n:=by{
intro e;apply hj;have:=congrArg (Equiv.swap p (Fin.last n)) e;rwa [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
}
obtain ⟨t,ht⟩:=Fin.exists_castSucc_eq.2 hl;rw [← ht,Fin.snoc_castSucc,ht,Equiv.swap_apply_self,Function.update_of_ne hj]
}
}
theorem p1d (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ) (hdep : ∃ x : Fin (n + 1) → Bool,f (update x p (!x p)) ≠ f x) (hnc : ∀ b : Bool,∃ x y : Fin (n + 1) → Bool,f (update x p b) ≠ f (update y p b)) (h : HasCircuitSize (n + 1) f s) : ∃ (b : Bool) (s' : ℕ),s' + 2 ≤ s ∧ HasCircuitSize (n + 1) (fun x=>f (update x p b)) s':=by{
set σ : Equiv.Perm (Fin (n + 1)):=Equiv.swap p (Fin.last n) with hσ
have hg : HasCircuitSize (n + 1) (fun x=>f (x ∘ σ)) s:=relabel_size (⇑σ) f s h
have hss : ∀ x : Fin (n + 1) → Bool,(x ∘ σ) ∘ σ=x:=by intro x;funext j;simp [hσ,Equiv.swap_apply_self]
have hsl : σ.symm (Fin.last n)=p:=by rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
have hdep' : ∃ x : Fin (n + 1) → Bool, (fun x=>f (x ∘ σ)) (update x (Fin.last n) (!x (Fin.last n))) ≠ (fun x=>f (x ∘ σ)) x:=by{
obtain ⟨x0,hx0⟩:=hdep;refine ⟨x0 ∘ σ,?_⟩
simp only
rw [Function.update_comp_equiv,hsl,hss]
have : (x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
rw [this];exact hx0
}
have hnc' : ∀ b : Bool,∃ y y' : Fin n → Bool, (fun x=>f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x=>f (x ∘ σ)) (Fin.snoc y' b):=by{
intro b;obtain ⟨x,y,hxy⟩:=hnc b;refine ⟨fun j=>x (σ j.castSucc),fun j=>y (σ j.castSucc),?_⟩
simp only
rw [p2c,p2c];exact hxy
}
obtain ⟨b,s',hs,h'⟩:=p1b n _ s hdep' hnc' hg;refine ⟨b,s',hs,?_⟩
have h'':=relabel_size (fun j : Fin n=>σ j.castSucc) _ s' h'
have e : (fun x : Fin (n + 1) → Bool => (fun y : Fin n → Bool=>(fun x=>f (x ∘ σ)) (Fin.snoc y b)) (x ∘ fun j : Fin n=>σ j.castSucc)) = fun x=>f (update x p b):=by{
funext x
simp only
exact congrArg f (p2c n p x b)
}
rw [e] at h'';exact h''
}
end PermInputs
namespace Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
open PEqualNP.Outside.L_meta_314_aux.PermInputs
def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
 ∃ x : Fin m → Bool,f (update x p (!x p)) ≠ f x
abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) : Fin m → Bool :=
 update (update x p a) q b
def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
 ∃ a b : Bool,∀ x : Fin m → Bool,
  f (set2 x p (!a) q b)=f (set2 x p a q (!b)) ∧
  f (set2 x p a q (!b))=f (set2 x p (!a) q (!b))
def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
 ∃ s' : ℕ,s' + k ≤ s ∧ HasCircuitSize m (fun x=>f (update x y b)) s'
def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
 (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
  (Drop f y false 2 s ∧ Drop f y true 4 s)
def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
 ∀ p : Fin m,Dep f p → ∀ b : Bool,∃ x y : Fin m → Bool,
  f (update x p b) ≠ f (update y p b)
def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
 ∀ p q : Fin m,p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q
def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
 CleanL m gs ∧ (∀ x : Fin m → Bool,vl gs x o=f x) ∧
  (∀ (gs' : List Gate) (o' : ℕ),CleanL m gs' → (∀ x : Fin m → Bool,vl gs' x o'=f x) → gs.length ≤ gs'.length)
theorem Least.hcl {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ} (L : Least m f gs o) : CleanL m gs:=L.1
theorem Least.hev {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ} (L : Least m f gs o) : ∀ x : Fin m → Bool,vl gs x o=f x:=L.2.1
theorem Least.hmin {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ} (L : Least m f gs o) : ∀ (gs' : List Gate) (o' : ℕ),CleanL m gs' → (∀ x : Fin m → Bool,vl gs' x o'=f x) → gs.length ≤ gs'.length:=L.2.2
def Reads (gs : List Gate) (p w : ℕ) : Prop:=∃ g,gs[p]?=some g ∧ w ∈ g.inputs
theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) : ∃ x y : Fin m → Bool,f x ≠ f y:=by{
obtain ⟨x,hx⟩:=h;exact ⟨_,_,hx⟩
}
theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ} (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s':=by{
obtain ⟨t,ht,hc⟩:=h
exact ⟨t,by omega,hc⟩
}
theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) : HasCircuitSize k (fun y=>vl gs y o) gs.length:=by{
refine ⟨⟨gs,o⟩,?_,le_refl _,fun y=>rfl⟩
intro g hg;exact (clean_nok k gs hcl g hg).1
}
theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) : w < k + q:=by{
obtain ⟨g,hg,hw⟩:=h;exact (hcl q g hg).lt w hw
}
theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length:=by{
obtain ⟨g,hg,_⟩:=h;exact (List.getElem?_eq_some_iff.1 hg).1
}
theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) : vl gs u w=false:=by
 unfold vl
 exact List.getD_eq_default _ _ (by rw [length_wiresFrom];simp;omega)
theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate) (hq : gs[q]?=some g) (j : ℕ) (hop : g.op=GateOp.not) (hin : g.inputs=[j]) : vl gs u (k + q)=!vl gs u j:=by{
rw [vl_gate gs hcl u q g hq,hop,hin];rfl
}
theorem p21 (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (h : HasCircuitSize m f s) : ∃ (gs : List Gate) (o : ℕ),Least m f gs o ∧ gs.length ≤ s:=by{
classical
have hc:=p35 m f s hnc h;have hex : ∃ t,p34 m f t:=⟨s,hc⟩;obtain ⟨gs,o,hcl,hsz,hev⟩:=Nat.find_spec hex;have hfs : Nat.find hex ≤ s:=Nat.find_min' hex hc
refine ⟨gs,o,⟨hcl,hev,?_⟩,by omega⟩
intro gs' o' hc' he';have:=Nat.find_min' hex ⟨gs',o',hc',le_refl _,he'⟩;omega
}
theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length) (ho : o ≠ k + p) (hno : ∀ q,¬ Reads gs q (k + p)) (hnc : ∃ y y' : Fin k → Bool,vl gs y o ≠ vl gs y' o) : ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ ∀ y : Fin k → Bool,vl gs' y o'=vl gs y o:=by
 obtain ⟨g,hg⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
 have hpos : 0 < k + p:=by rcases hcl p g hg with ⟨_,j,hj,_⟩ | ⟨_,j,_,hj,_,_⟩ <;> omega
 let g0 : Gate:=⟨GateOp.and,[0,0]⟩;let gs':=gs.set p g0
 have hlen : gs'.length=gs.length:=by simp [gs']
 have hget_p : gs'[p]?=some g0:=by simp [gs',hp]
 have hget_ne : ∀ r,r ≠ p → gs'[r]?=gs[r]?:=by
  intro r hr;simp [gs',Ne.symm hr]
 have hcl' : CleanL k gs':=by
  intro r g' hr'
  by_cases hrp : r=p
  · subst hrp;rw [hget_p] at hr';cases hr';exact Or.inr ⟨Or.inl rfl,0,0,hpos,hpos,rfl⟩
  · rw [hget_ne r hrp] at hr';exact hcl r g' hr'
 have hagree : ∀ y : Fin k → Bool,∀ w,w ≠ k + p → vl gs' y w=vl gs y w:=by
  intro y w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
   intro hw
   by_cases hwk : w < k
   · rw [vl_input gs' y w hwk,vl_input gs y w hwk]
   · obtain ⟨r,rfl⟩ : ∃ r,w=k + r:=⟨w - k,by omega⟩
     have hrp : r ≠ p:=fun e=>hw (by rw [e])
     cases hr : gs[r]? with
     | none =>
      have hl : gs.length ≤ r:=List.getElem?_eq_none_iff.1 hr
      rw [vl_beyond gs' y _ (by omega),vl_beyond gs y _ (by omega)]
     | some g' =>
      have hr' : gs'[r]?=some g':=by rw [hget_ne r hrp];exact hr
      rw [vl_gate gs' hcl' y r g' hr',vl_gate gs hcl y r g' hr];congr 1;apply List.map_congr_left;intro a ha;have hlt:=(hcl r g' hr).lt a ha;exact ih a hlt (fun e=>hno r ⟨g',hr,e ▸ ha⟩)
 have halias : ∀ y : Fin k → Bool,vl gs' y (k + p)=vl gs' y 0:=by
  intro y;rw [vl_gate gs' hcl' y p g0 hget_p];simp [g0,GateOp.eval]
 have hnc' : ∃ y y' : Fin k → Bool,vl gs' y o ≠ vl gs' y' o:=by
  obtain ⟨y,y',h⟩:=hnc
  exact ⟨y,y',by rw [hagree y o ho,hagree y' o ho];exact h⟩
 obtain ⟨gs'',o'',hc'',hl'',he''⟩ :=
  drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
 exact ⟨gs'',o'',hc'',by omega,fun y=>by rw [he'' y,hagree y o ho]⟩
section
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) : ∃ y y' : Fin m → Bool,vl gs y o ≠ vl gs y' o:=by{
obtain ⟨x,y,h⟩:=hnc
exact ⟨x,y,by rw [L.hev,L.hev];exact h⟩
}
theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (s : ℕ) (h : HasCircuitSize m f s) : gs.length ≤ s:=by{
obtain ⟨gs',o',hc',hl',he'⟩:=p35 m f s hnc h;have:=L.hmin gs' o' hc' he';omega
}
theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (p : ℕ) (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool,vl gs u (m + p)=c:=by{
intro hall;obtain ⟨gs',o',hc',hl',he'⟩:=drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
have:=L.hmin gs' o' hc' (fun x=>by rw [he' x];exact L.hev x)
omega
}
theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (p : ℕ) (hp : p < gs.length) (j : ℕ) (hj : j < m + p) : ¬ ∀ u : Fin m → Bool,vl gs u (m + p)=vl gs u j:=by{
intro hall;obtain ⟨gs',o',hc',hl',he'⟩:=drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
have:=L.hmin gs' o' hc' (fun x=>by rw [he' x];exact L.hev x)
omega
}
theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (p : ℕ) (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q,p < q ∧ Reads gs q (m + p):=by{
by_contra hno
have hno' : ∀ q,¬ Reads gs q (m + p):=by{
intro q hq
by_cases hpq : p < q
{exact hno ⟨q,hpq,hq⟩}
{have:=reads_lt L.hcl hq;omega}
}
obtain ⟨gs',o',hc',hl',he'⟩:=drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
have:=L.hmin gs' o' hc' (fun x=>by rw [he' x];exact L.hev x)
omega
}
theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i) (hnc : ∀ b : Bool,∃ x y : Fin m → Bool,f (update x i b) ≠ f (update y i b)) : ∃ q,Reads gs q i:=by
 by_contra hno
 have hno' : ∀ g ∈ gs,(i : ℕ) ∉ g.inputs:=by
  intro g hg hi;obtain ⟨q,hq⟩:=List.mem_iff_getElem?.1 hg;exact hno ⟨q,g,hq,hi⟩
 have hoi : o ≠ i:=by
  intro e;obtain ⟨x,y,hxy⟩:=hnc false;apply hxy;rw [← L.hev,← L.hev,e,vl_input gs _ i i.isLt,vl_input gs _ i i.isLt]
  simp
 obtain ⟨x,hx⟩:=hd;apply hx;rw [← L.hev,← L.hev]
 refine p20 i gs _ _ hno' (by simp) ?_ o hoi
 intro j hj
 by_cases hjm : j < m
 · rw [show (List.ofFn (update x i (!x i))).getD j false=update x i (!x i) ⟨j,hjm⟩ from p2e m _ false ⟨j,hjm⟩,show (List.ofFn x).getD j false=x ⟨j,hjm⟩ from p2e m x false ⟨j,hjm⟩];exact Function.update_of_ne (fun e=>hj (congrArg Fin.val e)) _ _
 · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
end
theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) : update x i b=ins i b (Fin.removeNth i x) :=
 (Fin.insertNth_removeNth i b x).symm
theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ} (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool,vl gs x o=f x) (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o=Sum.inl c) (x : Fin (n + 1) → Bool) : f (update x i b)=c:=by{
rw [upd_ins,← hev];exact st_val_const n gs hcl i b o c h _
}
theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ) (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool,vl gs x o=f x) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (S : Finset ℕ) (hS : ∀ p ∈ S,RC n gs i b p) : Drop f i b S.card gs.length:=by
 have hL : (statAt n i b,([] : List Gate)).1.length=n + 1:=statAt_length n i b
 have hcount:=elim_count n (statAt n i b,[]) gs (clean_nok _ gs hcl) S (by
  intro p hp;obtain ⟨g,hg,a,ha,c,hc⟩:=hS p hp;refine ⟨g,hg,a,ha,?_,c,hc⟩
  rw [hL]
  exact (hcl p g hg).lt a ha)
 simp only [List.length_nil,zero_add] at hcount
 cases hst : stF n gs i b o with
 | inl c =>
  exfalso;obtain ⟨x,y,hxy⟩:=hnc;exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
 | inr j =>
  have hc : CleanL n (passG n gs i b) :=
   clean_elim n (List.ofFn fun _ : Fin n=>false) (by simp) gs _ _
    (fun g hg=>(clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp;simp at hp)
  have h2:=relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc);have e : (fun x : Fin (n + 1) → Bool=>f (update x i b))
   = fun x=>vl (passG n gs i b) (x ∘ Fin.succAbove i) j:=by
   funext x;rw [upd_ins,← hev,st_val_wire n gs hcl i b o j hst];rfl
  refine ⟨(passG n gs i b).length,hcount,?_⟩
  rw [e];exact h2
section
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (S : Finset ℕ) (hS : ∀ p ∈ S,RC n gs i b p) : Drop f i b S.card gs.length :=
 PEqualNP.Outside.L_meta_314_aux.Readers.save n f gs o L.hcl L.hev i b hnc S hS
theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) : Drop f i b 2 gs.length:=by
 have:=L.save i b hnc {p1,p2} (by
  intro p hp;simp only [Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> assumption)
 rwa [Finset.card_pair h12] at this
theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) : Drop f i b 3 gs.length:=by
 have:=L.save i b hnc {p1,p2,p3} (by
  intro p hp;simp only [Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> assumption)
 rwa [Finset.card_eq_three.2 ⟨p1,p2,p3,h12,h13,h23,rfl⟩] at this
theorem Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) : Drop f i b 4 gs.length:=by
 have:=L.save i b hnc {p1,p2,p3,p4} (by
  intro p hp;simp only [Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> assumption)
 have hcard : ({p1,p2,p3,p4} : Finset ℕ).card=4:=by rw [Finset.card_insert_of_notMem (by simp [h12,h13,h14]),Finset.card_eq_three.2 ⟨p2,p3,p4,h23,h24,h34,rfl⟩]
 rwa [hcard] at this
theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) : RC n gs i b q:=by{
obtain ⟨g,hg,hin⟩:=h;exact ⟨g,hg,i,hin,b,stF_self n gs i b⟩
}
theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w) (hc : IsC n gs i b w) : RC n gs i b q:=by{
obtain ⟨g,hg,hin⟩:=h;obtain ⟨c,hc⟩:=hc;exact ⟨g,hg,w,hin,c,hc⟩
}
theorem Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool,f x ≠ f y) (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i:=by
 by_contra hnd
 have hnd' : ∀ x : Fin (n + 1) → Bool,f (update x i (!x i))=f x:=by
  intro x
  by_contra h
  exact hnd ⟨x,h⟩
 have hfix : ∀ x : Fin (n + 1) → Bool,f (update x i false)=f x:=by
  intro x
  by_cases hx : x i=false
  · have e : update x i false=x:=by
     rw [← hx];exact Function.update_eq_self i x
    rw [e]
  · have e : (!x i)=false:=by simpa using hx
    have:=hnd' x;rwa [e] at this
 have hnc' : ∃ x y : Fin (n + 1) → Bool, f (update x i false) ≠ f (update y i false):=by
  obtain ⟨x,y,h⟩:=hnc
  exact ⟨x,y,by rw [hfix,hfix];exact h⟩
 obtain ⟨s',hs',hc⟩:=L.save i false hnc' {q} (by
  intro p hp;rw [Finset.mem_singleton] at hp;subst hp
  exact rc_input false hq)
 rw [Finset.card_singleton] at hs';have e : (fun x : Fin (n + 1) → Bool=>f (update x i false))=f:=funext hfix;rw [e] at hc;have:=L.lower hnc s' hc;omega
theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) : ∃ q,p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q:=by{
have hfnc : ∃ x y : Fin (n + 1) → Bool,f x ≠ f y:=by{
obtain ⟨x,y,h⟩:=hnc;exact ⟨_,_,h⟩
}
have ho : o ≠ n + 1 + p:=by{
intro e;obtain ⟨c,hc'⟩:=hc;obtain ⟨x,y,hxy⟩:=hnc;rw [← e] at hc';exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
}
obtain ⟨q,hpq,hr⟩:=L.live hfnc p hp ho;exact ⟨q,hpq,hr,rc_of_reads hr hc⟩
}
end
end Readers
namespace Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate) (hq : gs[q]?=some g) (a : ℕ) (ha : a ∈ g.inputs) : (g.op=GateOp.not ∧ g.inputs=[a] ∧ ∀ u : Fin k → Bool,vl gs u (k + q)=!vl gs u a) ∨ ∃ w,(g.inputs=[a,w] ∨ g.inputs=[w,a]) ∧ ((g.op=GateOp.and ∧ ∀ u : Fin k → Bool,vl gs u (k + q)=(vl gs u a && vl gs u w)) ∨ (g.op=GateOp.or ∧ ∀ u : Fin k → Bool,vl gs u (k + q)=(vl gs u a || vl gs u w))):=by{
rcases hcl q g hq with ⟨hop,j,_,hin⟩ | ⟨hop,j,j',_,_,hin⟩
{
left
have e : a=j:=by rw [hin] at ha;simpa using ha
subst e;exact ⟨hop,hin,fun u=>vl_not gs hcl u q g hq a hop hin⟩
}
{
right
have e : a=j ∨ a=j':=by rw [hin] at ha;simpa using ha
rcases e with e | e
{
subst e;refine ⟨j',Or.inl hin,?_⟩
rcases hop with hop | hop
{exact Or.inl ⟨hop,fun u=>by rw [vl_gate gs hcl u q g hq,hop,hin];simp [GateOp.eval]⟩}
{exact Or.inr ⟨hop,fun u=>by rw [vl_gate gs hcl u q g hq,hop,hin];simp [GateOp.eval]⟩}
}
{
subst e;refine ⟨j,Or.inr hin,?_⟩
rcases hop with hop | hop
{
refine Or.inl ⟨hop,fun u=>?_⟩
rw [vl_gate gs hcl u q g hq,hop,hin];simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id,Bool.and_true];exact Bool.and_comm _ _
}
{
refine Or.inr ⟨hop,fun u=>?_⟩
rw [vl_gate gs hcl u q g hq,hop,hin];simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id,Bool.or_false];exact Bool.or_comm _ _
}
}
}
}
section
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (p q a : ℕ) (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False:=by
 obtain ⟨gp,hgp,hap⟩:=hpa;obtain ⟨gq,hgq,haq⟩:=hqa;obtain ⟨gq',hgq',hpq⟩:=hqp
 have e : gq'=gq:=by rw [hgq] at hgq';exact (Option.some.inj hgq').symm
 subst e;have hlt_a : a < m + p:=(L.hcl p gp hgp).lt a hap;have hlt_p : m + p < m + q:=(L.hcl q gq' hgq).lt _ hpq;have hqlen : q < gs.length:=(List.getElem?_eq_some_iff.1 hgq).1
 rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_,hin,_⟩ | ⟨w,hin,hq⟩
 · rw [hin] at hpq
   simp at hpq
   omega
 · have hw : w=m + p:=by
    rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
   subst hw
   rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_,_,hp⟩ | ⟨w',_,hp⟩
   · rcases hq with ⟨_,hq⟩ | ⟨_,hq⟩
     · exact L.no_const hnc q hqlen false (fun u=>by
        rw [hq u,hp u];cases vl gs u a <;> rfl)
     · exact L.no_const hnc q hqlen true (fun u=>by
        rw [hq u,hp u];cases vl gs u a <;> rfl)
   · rcases hq with ⟨_,hq⟩ | ⟨_,hq⟩ <;> rcases hp with ⟨_,hp⟩ | ⟨_,hp⟩
     · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u=>by
        rw [hq u,hp u];cases vl gs u a <;> cases vl gs u w' <;> rfl)
     · exact L.no_alias hnc q hqlen a (by omega) (fun u=>by
        rw [hq u,hp u];cases vl gs u a <;> cases vl gs u w' <;> rfl)
     · exact L.no_alias hnc q hqlen a (by omega) (fun u=>by
        rw [hq u,hp u];cases vl gs u a <;> cases vl gs u w' <;> rfl)
     · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u=>by
        rw [hq u,hp u];cases vl gs u a <;> cases vl gs u w' <;> rfl)
end
section
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate) (hgp : gs[p]?=some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool) (h : gp.op=GateOp.not ∨ b=fixBit gp) : IsC n gs i b (n + 1 + p):=by{
rcases h with h | rfl
{
apply st_allconst n gs hcl i b p gp hgp;intro a ha
rcases hcl p gp hgp with ⟨_,j,_,hin⟩ | ⟨hop,_⟩
{
rw [hin] at ha hip
simp at ha hip
rw [ha,← hip];exact ⟨b,stF_self n gs i b⟩
}
{rcases hop with hop | hop <;> rw [hop] at h <;> cases h}
}
{exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)}
}
theorem Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length:=by
 have hfnc : ∃ x y : Fin (n + 1) → Bool,f x ≠ f y:=by
  obtain ⟨x,y,h⟩:=hnc;exact ⟨_,_,h⟩
 obtain ⟨J,hJp,hJr,hJrc⟩:=L.next i b hnc p (reads_len hp) hc
 have hJq : J ≠ q:=by
  rintro rfl;exact L.no_tri hfnc p J i hp hq hJr
 exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc
theorem Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) : Drop f i b 4 gs.length:=by
 have hfnc : ∃ x y : Fin (n + 1) → Bool,f x ≠ f y:=by
  obtain ⟨x,y,h⟩:=hnc;exact ⟨_,_,h⟩
 obtain ⟨J1,h1p,h1r,h1rc⟩:=L.next i b hnc p (reads_len hp) hcp;obtain ⟨J2,h2q,h2r,h2rc⟩:=L.next i b hnc q (reads_len hq) hcq
 have h1q : J1 ≠ q:=by
  rintro rfl;exact L.no_tri hfnc p J1 i hp hq h1r
 have h2p : J2 ≠ p:=by
  rintro rfl;exact L.no_tri hfnc q J2 i hq hp h2r
 by_cases h12 : J1=J2
 · have h2r' : Reads gs J1 (n + 1 + q):=by rw [h12];exact h2r
   have h2q' : q < J1:=by rw [h12];exact h2q
   obtain ⟨gJ,hgJ,hinp⟩:=h1r;obtain ⟨gJ',hgJ',hinq⟩:=h2r';have e : gJ'=gJ:=gate_eq hgJ' hgJ rfl;subst e
   have hcJ : IsC n gs i b (n + 1 + J1):=st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha=>by
    rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
     with e | e
    · rw [e];exact hcp
    · rw [e];exact hcq)
   obtain ⟨K,hKJ,_,hKrc⟩:=L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
   exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
    (rc_input b hp) (rc_input b hq) h1rc hKrc
 · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
    (rc_input b hp) (rc_input b hq) h1rc h2rc
theorem Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (hnc : ∀ b : Bool,∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length:=by
 obtain ⟨gp,hgp,hip⟩:=hp;obtain ⟨gq,hgq,hiq⟩:=hq;have hp : Reads gs p i:=⟨gp,hgp,hip⟩;have hq : Reads gs q i:=⟨gq,hgq,hiq⟩;have cp:=isC_reader L.hcl i p gp hgp hip;have cq:=isC_reader L.hcl i q gq hgq hiq
 by_cases hnp : gp.op=GateOp.not
 · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
 by_cases hnq : gq.op=GateOp.not
 · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
 by_cases hfb : fixBit gp=fixBit gq
 · cases hc : fixBit gp
   · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb,hc]))),L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
   · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp) (rc_input false hq),L.fourth i true (hnc true) p q hpq hp hq (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb,hc])))⟩)
 · have key : ∀ b,Drop f i b 3 gs.length:=by
    intro b
    by_cases hb : b=fixBit gp
    · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
    · have hb' : b=fixBit gq:=by
       revert hb hfb
       cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
      exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
   exact Or.inl ⟨key false,key true⟩
theorem Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (hnc : ∀ b : Bool,∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (r : ℕ) (g : Gate) (hr : gs[r]?=some g) (hop : g.op=GateOp.not) (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r)) (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length:=by
 have key : ∀ b,Drop f i b 3 gs.length:=by
  intro b;have hc:=isC_reader L.hcl i r g hr hin b (Or.inl hop);have hpr:=reads_lt L.hcl hp;have hqr:=reads_lt L.hcl hq
  exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g,hr,hin⟩)
   (rc_of_reads hp hc) (rc_of_reads hq hc)
 exact ⟨key false,key true⟩
end
end Readers
namespace Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
theorem p27 {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool) (h : ∀ u,f u=xor (u v) c) : False:=by{
have hd : Dep f v:=⟨fun _=>false,by rw [h,h];cases c <;> simp⟩
obtain ⟨x,y,hxy⟩:=hnc v hd false;apply hxy;rw [h,h]
simp
}
theorem p3d {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) : set2 x p a q b p=a:=by simp [set2,Function.update_of_ne h]
theorem p3c {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) : set2 x p a q b q=b:=by simp [set2]
theorem p3e {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p) (hq : i ≠ q) : set2 x p a q b i=x i:=by simp [set2,Function.update_of_ne hp,Function.update_of_ne hq]
section
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool,f x ≠ f y) (t : ℕ) (ht : ∀ r < t,∀ g,gs[r]?=some g → g.op=GateOp.not) (r : ℕ) (hr : r < t) (g : Gate) (hg : gs[r]?=some g) : ∃ v : Fin (n + 1),g.inputs=[(v : ℕ)]:=by
 rcases L.hcl r g hg with ⟨hop,j,hj,hin⟩ | ⟨hop,_⟩
 · by_cases hjn : j < n + 1
   · exact ⟨⟨j,hjn⟩,hin⟩
   · exfalso
     obtain ⟨r',rfl⟩ : ∃ r',j=n + 1 + r':=⟨j - (n + 1),by omega⟩
     have hrl : r < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
     obtain ⟨g',hg'⟩ : ∃ g',gs[r']?=some g' :=
      ⟨gs[r'],List.getElem?_eq_getElem (by omega)⟩
     have hop':=ht r' (by omega) g' hg'
     rcases L.hcl r' g' hg' with ⟨_,j',hj',hin'⟩ | ⟨hop2,_⟩
     · exact L.no_alias hfnc r hrl j' (by omega) (fun u=>by
        rw [vl_not gs L.hcl u r g hg _ hop hin,vl_not gs L.hcl u r' g' hg' _ hop' hin']
        simp)
     · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
 · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h
theorem Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool,f x ≠ f y) (t : ℕ) (ht : ∀ r < t,∀ g,gs[r]?=some g → g.op=GateOp.not) (w : ℕ) (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) : ∃ (v : Fin (n + 1)) (c : Bool),(∀ u,vl gs u w=xor (u v) c) ∧ (w=v ∨ ∃ r g,r < t ∧ w=n + 1 + r ∧ gs[r]?=some g ∧ g.op=GateOp.not ∧ g.inputs=[(v : ℕ)]):=by
 by_cases hwn : w < n + 1
 · exact ⟨⟨w,hwn⟩,false,fun u=>by rw [vl_input gs u w hwn];simp,Or.inl rfl⟩
 · obtain ⟨r,rfl⟩ : ∃ r,w=n + 1 + r:=⟨w - (n + 1),by omega⟩
   obtain ⟨g,hg⟩ : ∃ g,gs[r]?=some g:=⟨gs[r],List.getElem?_eq_getElem (by omega)⟩
   have hop:=ht r (by omega) g hg
   obtain ⟨v,hin⟩:=L.not_input hfnc t ht r (by omega) g hg
   exact ⟨v,true,fun u=>by
    rw [vl_not gs L.hcl u r g hg _ hop hin,vl_input gs u v v.isLt];simp,
    Or.inr ⟨r,g,by omega,rfl,hg,hop,hin⟩⟩
theorem Least.funnel (L : Least (n + 1) f gs o) (hdep : ∃ p,Dep f p) (hnc : RestrNC f) (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ),Reads gs p i → Reads gs q i → p=q) (h2 : ∀ (i : Fin (n + 1)) (r : ℕ) (g : Gate),gs[r]?=some g → g.op=GateOp.not → (i : ℕ) ∈ g.inputs → ∀ p q : ℕ,Reads gs p (n + 1 + r) → Reads gs q (n + 1 + r) → p=q) : ∃ p q : Fin (n + 1),p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q:=by
 classical
 have hfnc : ∃ x y : Fin (n + 1) → Bool,f x ≠ f y:=by
  obtain ⟨p,hp⟩:=hdep;exact dep_nc hp
 by_cases hex : ∃ (t : ℕ) (g : Gate),gs[t]?=some g ∧ g.op ≠ GateOp.not
 swap
 · exfalso;push Not at hex
   have ht : ∀ r < gs.length,∀ g,gs[r]?=some g → g.op=GateOp.not :=
    fun r _ g hg=>hex r g hg
   by_cases hol : o < n + 1 + gs.length
   · obtain ⟨v,c,hv,_⟩:=L.lit_wire hfnc gs.length ht o hol hol
     exact p27 hnc v c (fun u=>by rw [← L.hev,hv])
   · obtain ⟨x,y,hxy⟩:=hfnc;apply hxy
     rw [← L.hev,← L.hev,vl_beyond gs x o (by omega),vl_beyond gs y o (by omega)]
 obtain ⟨g,hg,hgop⟩:=Nat.find_spec hex
 set t:=Nat.find hex with htdef
 have ht : ∀ r < t,∀ g',gs[r]?=some g' → g'.op=GateOp.not:=by
  intro r hr g' hg'
  by_contra hne
  exact Nat.find_min hex hr ⟨g',hg',hne⟩
 have htl : t < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 rcases L.hcl t g hg with ⟨hop,_⟩ | ⟨hop,j,k,hj,hk,hin⟩
 · exact absurd hop hgop
 obtain ⟨vj,cj,hvj,hsj⟩:=L.lit_wire hfnc t ht j hj (by omega)
 obtain ⟨vk,ck,hvk,hsk⟩:=L.lit_wire hfnc t ht k hk (by omega)
 have hRj : Reads gs t j:=⟨g,hg,by rw [hin];simp⟩
 have hRk : Reads gs t k:=⟨g,hg,by rw [hin];simp⟩
 have hRv : ∀ (w : ℕ) (v : Fin (n + 1)),Reads gs t w → (w=v ∨ ∃ r g',r < t ∧ w=n + 1 + r ∧ gs[r]?=some g' ∧ g'.op=GateOp.not ∧ g'.inputs=[(v : ℕ)]) → ∃ r,Reads gs r v:=by
  intro w v hw hs
  rcases hs with e | ⟨r,g',_,_,hg',_,hin'⟩
  · exact ⟨t,by rw [← e];exact hw⟩
  · exact ⟨r,g',hg',by rw [hin'];simp⟩
 have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)),Reads gs t w → (w=v ∨ ∃ r g',r < t ∧ w=n + 1 + r ∧ gs[r]?=some g' ∧ g'.op=GateOp.not ∧ g'.inputs=[(v : ℕ)]) → ∀ p' a,(a=(v : ℕ) ∨ a=w) → Reads gs p' a → n + 1 + p' ≠ w → p'=t:=by
  intro w v hw hs p' a ha hr hne
  rcases hs with e | ⟨r,g',_,er,hg',hop',hin'⟩
  · have ha' : a=v:=by
     rcases ha with ha | ha
     · exact ha
     · rw [ha,e]
    rw [ha'] at hr
    exact h1 v p' t hr (by rw [← e];exact hw)
  · have hrv : Reads gs r v:=⟨g',hg',by rw [hin'];simp⟩
    rcases ha with ha | ha
    · rw [ha] at hr;have:=h1 v p' r hr hrv
      exact (hne (by rw [this,er])).elim
    · rw [ha,er] at hr;rw [er] at hw
      exact h2 v r g' hg' hop' (by rw [hin'];simp) p' t hr hw
 have hvjk : vj ≠ vk:=by
  intro e
  have hjk : j ≠ k:=by
   intro e';subst e'
   exact L.no_alias hfnc t htl j hj (fun u=>by
    rw [vl_gate gs L.hcl u t g hg,hin]
    rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
  rcases hsj with ej | ⟨r1,g1,hr1,ej,hg1,hop1,hin1⟩ <;>
   rcases hsk with ek | ⟨r2,g2,hr2,ek,hg2,hop2,hin2⟩
  · exact hjk (by rw [ej,ek,e])
  · have:=h1 vj t r2 (by rw [← ej];exact hRj) ⟨g2,hg2,by rw [hin2,← e];simp⟩
    omega
  · have:=h1 vk t r1 (by rw [← ek];exact hRk) ⟨g1,hg1,by rw [hin1,e];simp⟩
    omega
  · have:=h1 vj r1 r2 ⟨g1,hg1,by rw [hin1];simp⟩ ⟨g2,hg2,by rw [hin2,← e];simp⟩
    exact hjk (by rw [ej,ek,this])
 obtain ⟨rj,hrj⟩:=hRv j vj hRj hsj;obtain ⟨rk,hrk⟩:=hRv k vk hRk hsk;have hdj:=L.read_dep hfnc vj rj hrj;have hdk:=L.read_dep hfnc vk rk hrk;have KC : ∀ u u' : Fin (n + 1) → Bool,(∀ i,i ≠ vj → i ≠ vk → u i=u' i) →
  vl gs u (n + 1 + t)=vl gs u' (n + 1 + t) → f u=f u':=by
  intro u u' hagr hgv;rw [← L.hev,← L.hev];refine p37 gs L.hcl u u' (fun a=>a=(vj : ℕ) ∨ a=(vk : ℕ) ∨ a=j ∨ a=k) (o + 1)
   ?_ ?_ o (by omega) ?_
  · intro a ha hBa;have hBa' : ¬ (a=(vj : ℕ) ∨ a=(vk : ℕ) ∨ a=j ∨ a=k):=hBa;rw [vl_input gs u a ha,vl_input gs u' a ha];apply hagr
    · intro e;exact hBa' (Or.inl (congrArg Fin.val e))
    · intro e;exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
  · intro p' g' hp' _ hB' hr _;have hB'' : ¬ (n + 1 + p'=(vj : ℕ) ∨ n + 1 + p'=(vk : ℕ) ∨ n + 1 + p'=j ∨ n + 1 + p'=k):=hB';obtain ⟨a,ha,hBa⟩:=hr;have hBa' : a=(vj : ℕ) ∨ a=(vk : ℕ) ∨ a=j ∨ a=k:=hBa;have hR : Reads gs p' a:=⟨g',hp',ha⟩
    have hpt : p'=t:=by
     rcases hBa' with e | e | e | e
     · exact hopnd j vj hRj hsj p' a (Or.inl e) hR
        (fun e'=>hB'' (Or.inr (Or.inr (Or.inl e'))))
     · exact hopnd k vk hRk hsk p' a (Or.inl e) hR
        (fun e'=>hB'' (Or.inr (Or.inr (Or.inr e'))))
     · exact hopnd j vj hRj hsj p' a (Or.inr e) hR
        (fun e'=>hB'' (Or.inr (Or.inr (Or.inl e'))))
     · exact hopnd k vk hRk hsk p' a (Or.inr e) hR
        (fun e'=>hB'' (Or.inr (Or.inr (Or.inr e'))))
    rw [hpt];exact hgv
  · intro hB;have hB' : o=(vj : ℕ) ∨ o=(vk : ℕ) ∨ o=j ∨ o=k:=hB
    rcases hB' with e | e | e | e
    · exact p27 hnc vj false (fun x=>by
       rw [← L.hev,e,vl_input gs x vj vj.isLt];simp)
    · exact p27 hnc vk false (fun x=>by
       rw [← L.hev,e,vl_input gs x vk vk.isLt];simp)
    · exact p27 hnc vj cj (fun x=>by rw [← L.hev,e,hvj])
    · exact p27 hnc vk ck (fun x=>by rw [← L.hev,e,hvk])
 have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool),∀ i,i ≠ vj → i ≠ vk → set2 x vj a vk b i=set2 x vj a' vk b' i:=by
  intro x a b a' b' i e1 e2;rw [p3e x vj vk a b i e1 e2,p3e x vj vk a' b' i e1 e2]
 have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool), vl gs (set2 x vj a vk b) (n + 1 + t)=g.op.eval [xor a cj,xor b ck]:=by
  intro x a b;rw [vl_gate gs L.hcl _ t g hg,hin];simp only [List.map_cons,List.map_nil];rw [hvj,hvk,p3d x hvjk,p3c x]
 refine ⟨vj,vk,hvjk,hdj,hdk,?_⟩
 rcases hop with hop | hop
 · refine ⟨!cj,!ck,fun x=>⟨KC _ _ (hag x _ _ _ _) ?_,KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
    rw [hval,hval,hop] <;> cases cj <;> cases ck <;> rfl
 · refine ⟨cj,ck,fun x=>⟨KC _ _ (hag x _ _ _ _) ?_,KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
    rw [hval,hval,hop] <;> cases cj <;> cases ck <;> rfl
end
end Readers
namespace Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
theorem fanout_step (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p,Dep f p) (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) : ∃ y : Fin (n + 1),Dep f y ∧ Pays f y s:=by
 classical
 have hfnc : ∃ x y : Fin (n + 1) → Bool,f x ≠ f y:=by
  obtain ⟨p,hp⟩:=hdep;exact dep_nc hp
 obtain ⟨gs,o,L,hls⟩:=p21 (n + 1) f s hfnc h
 have mono : ∀ y,Pays f y gs.length → Pays f y s:=by
  intro y hp
  rcases hp with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
  · exact Or.inl ⟨a.mono le_rfl hls,b.mono le_rfl hls⟩
  · exact Or.inr (Or.inl ⟨a.mono le_rfl hls,b.mono le_rfl hls⟩)
  · exact Or.inr (Or.inr ⟨a.mono le_rfl hls,b.mono le_rfl hls⟩)
 by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ),p ≠ q ∧ Reads gs p i ∧ Reads gs q i
 · obtain ⟨i,p,q,hpq,hp,hq⟩:=hA;have hd:=L.read_dep hfnc i p hp;exact ⟨i,hd,mono i (L.two_readers i (hnc i hd) p q hpq hp hq)⟩
 by_cases hB : ∃ (i : Fin (n + 1)) (r : ℕ) (g : Gate),gs[r]?=some g ∧ g.op=GateOp.not ∧
  (i : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ,p ≠ q ∧ Reads gs p (n + 1 + r) ∧ Reads gs q (n + 1 + r)
 · obtain ⟨i,r,g,hr,hop,hin,p,q,hpq,hp,hq⟩:=hB;have hd:=L.read_dep hfnc i r ⟨g,hr,hin⟩;obtain ⟨d1,d2⟩:=L.not_two_readers i (hnc i hd) r g hr hop hin p q hpq hp hq;exact ⟨i,hd,mono i (Or.inl ⟨d1,d2⟩)⟩
 exfalso;obtain ⟨p,q,hpq,hdp,hdq,hf⟩:=L.funnel hdep hnc
  (fun i p q hp hq=>by
   by_contra hne
   exact hA ⟨i,p,q,hne,hp,hq⟩)
  (fun i r g hr hop hin p q hp hq=>by
   by_contra hne
   exact hB ⟨i,r,g,hr,hop,hin,p,q,hne,hp,hq⟩)
 exact hnf p q hpq hdp hdq hf
theorem fanout_step_3_4 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p,Dep f p) (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) : (∃ (y : Fin (n + 1)) (s' : ℕ),s' + 3 ≤ s ∧ HasCircuitSize (n + 1) (fun x=>f (update x y false)) s') ∨ (∃ (y : Fin (n + 1)) (s' : ℕ),s' + 4 ≤ s ∧ HasCircuitSize (n + 1) (fun x=>f (update x y true)) s'):=by{
obtain ⟨y,_,hp⟩:=fanout_step n f s hdep hnc hnf h
rcases hp with ⟨⟨s',h1,h2⟩,_⟩ | ⟨⟨s',h1,h2⟩,_⟩ | ⟨_,⟨s',h1,h2⟩⟩
{exact Or.inl ⟨y,s',h1,h2⟩}
{exact Or.inl ⟨y,s',by omega,h2⟩}
{exact Or.inr ⟨y,s',h1,h2⟩}
}
end Readers
theorem readerTheorem : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ),(∃ p : Fin (n + 1),∃ x : Fin (n + 1) → Bool,f (update x p (!x p)) ≠ f x) → (∀ p : Fin (n + 1),(∃ x : Fin (n + 1) → Bool,f (update x p (!x p)) ≠ f x) → ∀ b : Bool,∃ x y : Fin (n + 1) → Bool,f (update x p b) ≠ f (update y p b)) → (∀ p q : Fin (n + 1),p ≠ q → (∃ x : Fin (n + 1) → Bool,f (update x p (!x p)) ≠ f x) → (∃ x : Fin (n + 1) → Bool,f (update x q (!x q)) ≠ f x) → ¬ ∃ a b : Bool,∀ x : Fin (n + 1) → Bool,f (update (update x p (!a)) q b)=f (update (update x p a) q (!b)) ∧ f (update (update x p a) q (!b))=f (update (update x p (!a)) q (!b))) → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s → (∃ (y : Fin (n + 1)) (s' : ℕ),s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x=>f (update x y false)) s') ∨ (∃ (y : Fin (n + 1)) (s' : ℕ),s' + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x=>f (update x y true)) s') :=
 PEqualNP.Outside.L_meta_314_aux.Readers.fanout_step_3_4
namespace PathSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
open PEqualNP.Outside.L_meta_314_aux.PermInputs
def G (N k : ℕ) (x : Fin N → Bool) : Bool :=
 decide ((∃ i : Fin N,i.val < k ∧ x i=true) ∨ (∃ i j : Fin N,k ≤ i.val ∧ i.val + 1=j.val ∧ x i=true ∧ x j=true))
def ext {N : ℕ} (x : Fin N → Bool) (j : ℕ) : Bool:=if h : j < N then x ⟨j,h⟩ else false
theorem ext_fin {N : ℕ} (x : Fin N → Bool) (i : Fin N) : ext x i.val=x i:=by simp [ext]
theorem ext_lt {N : ℕ} {x : Fin N → Bool} {j : ℕ} (h : ext x j=true) : j < N:=by{
unfold ext at h
split at h
{assumption}
{simp at h}
}
theorem ext_fn {N : ℕ} (Q : ℕ → Bool) (j : ℕ) : ext (fun i : Fin N=>Q i.val) j=(decide (j < N) && Q j):=by{
unfold ext
by_cases hj : j < N <;> simp [hj]
}
theorem ext_update {N : ℕ} (x : Fin N → Bool) (p : Fin N) (b : Bool) (j : ℕ) : ext (update x p b) j=if j=p.val then b else ext x j:=by{
unfold ext
by_cases hj : j < N
{simp [hj,Function.update_apply,Fin.ext_iff]}
{
have : j ≠ p.val:=by have:=p.2;omega
simp [hj,this]
}
}
theorem G_iff (N k : ℕ) (x : Fin N → Bool) : G N k x=true ↔ ((∃ i,i < k ∧ ext x i=true) ∨ (∃ i,k ≤ i ∧ ext x i=true ∧ ext x (i + 1)=true)):=by{
unfold G;rw [decide_eq_true_iff];constructor
{
rintro (⟨i,hi,hx⟩ | ⟨i,j,hi,hij,hx,hy⟩)
{exact Or.inl ⟨i,hi,by rw [ext_fin];exact hx⟩}
{
refine Or.inr ⟨i,hi,by rw [ext_fin];exact hx,?_⟩
rw [hij,ext_fin];exact hy
}
}
{
rintro (⟨i,hi,hx⟩ | ⟨i,hi,hx,hy⟩)
{
have hl:=ext_lt hx;refine Or.inl ⟨⟨i,hl⟩,hi,?_⟩
rw [← ext_fin x ⟨i,hl⟩];exact hx
}
{
have hl:=ext_lt hy
refine Or.inr ⟨⟨i,by omega⟩,⟨i + 1,hl⟩,hi,rfl,?_,?_⟩
{rw [← ext_fin x ⟨i,by omega⟩];exact hx}
{rw [← ext_fin x ⟨i + 1,hl⟩];exact hy}
}
}
}
def del (n k : ℕ) (hk : k < n) : Fin (n + 1) → Fin n :=
 fun i=>⟨if i.val ≤ k then i.val else i.val - 1,by have:=i.2;split <;> omega⟩
theorem ext_del (n k : ℕ) (hk : k < n) (y : Fin n → Bool) (b : Bool) (j : ℕ) : ext (update (y ∘ del n k hk) ⟨k,by omega⟩ b) j=if j=k then b else if j < k then ext y j else ext y (j - 1):=by
 rw [ext_update]
 by_cases hjk : j=k
 · simp [hjk]
 · rw [ite_eq_right hjk,ite_eq_right hjk];unfold ext
   by_cases hj : j < n + 1
   · rw [dite_eq_left hj]
     by_cases hjk' : j < k
     · rw [ite_eq_left hjk',dite_eq_left (by omega)]
       simp [del,show j ≤ k by omega]
     · rw [ite_eq_right hjk',dite_eq_left (by omega)]
       simp [del,show ¬ j ≤ k by omega]
   · rw [dite_eq_right hj,ite_eq_right (by omega),dite_eq_right (by omega)]
theorem G_del_false (n k : ℕ) (hk : k < n) (y : Fin n → Bool) : G (n + 1) k (update (y ∘ del n k hk) ⟨k,by omega⟩ false)=G n k y:=by
 rw [Bool.eq_iff_iff,G_iff,G_iff];simp only [ext_del];constructor
 · rintro (⟨i,hi,hx⟩ | ⟨i,hi,hx,hy⟩)
   · rw [ite_eq_right (by omega),ite_eq_left hi] at hx
     exact Or.inl ⟨i,hi,hx⟩
   · by_cases hik : i=k
     · rw [ite_eq_left hik] at hx;exact absurd hx (by simp)
     · rw [ite_eq_right hik,ite_eq_right (by omega)] at hx
       rw [ite_eq_right (by omega),ite_eq_right (by omega)] at hy
       refine Or.inr ⟨i - 1,by omega,hx,?_⟩
       rwa [show i - 1 + 1=i + 1 - 1 by omega]
 · rintro (⟨i,hi,hx⟩ | ⟨i,hi,hx,hy⟩)
   · refine Or.inl ⟨i,hi,?_⟩
     rw [ite_eq_right (by omega),ite_eq_left hi];exact hx
   · refine Or.inr ⟨i + 1,by omega,?_,?_⟩
     · rw [ite_eq_right (by omega),ite_eq_right (by omega)];simpa using hx
     · rw [ite_eq_right (by omega),ite_eq_right (by omega)];simpa using hy
theorem G_del_true (n k : ℕ) (hk : k < n) (y : Fin n → Bool) : G (n + 1) k (update (y ∘ del n k hk) ⟨k,by omega⟩ true)=G n (k + 1) y:=by
 rw [Bool.eq_iff_iff,G_iff,G_iff];simp only [ext_del];constructor
 · rintro (⟨i,hi,hx⟩ | ⟨i,hi,hx,hy⟩)
   · rw [ite_eq_right (by omega),ite_eq_left hi] at hx
     exact Or.inl ⟨i,by omega,hx⟩
   · by_cases hik : i=k
     · rw [ite_eq_right (by omega),ite_eq_right (by omega)] at hy
       refine Or.inl ⟨k,by omega,?_⟩
       rwa [show k=i + 1 - 1 by omega]
     · by_cases hik1 : i=k + 1
       · rw [ite_eq_right (by omega),ite_eq_right (by omega)] at hx
         refine Or.inl ⟨k,by omega,?_⟩
         rwa [show k=i - 1 by omega]
       · rw [ite_eq_right hik,ite_eq_right (by omega)] at hx
         rw [ite_eq_right (by omega),ite_eq_right (by omega)] at hy
         refine Or.inr ⟨i - 1,by omega,hx,?_⟩
         rwa [show i - 1 + 1=i + 1 - 1 by omega]
 · rintro (⟨i,hi,hx⟩ | ⟨i,hi,hx,hy⟩)
   · by_cases hik : i < k
     · refine Or.inl ⟨i,hik,?_⟩
       rw [ite_eq_right (by omega),ite_eq_left hik];exact hx
     · have e : i=k:=by omega
       subst e
       refine Or.inr ⟨i,le_rfl,by simp,?_⟩
       rw [ite_eq_right (by omega),ite_eq_right (by omega)];simpa using hx
   · refine Or.inr ⟨i + 1,by omega,?_,?_⟩
     · rw [ite_eq_right (by omega),ite_eq_right (by omega)];simpa using hx
     · rw [ite_eq_right (by omega),ite_eq_right (by omega)];simpa using hy
theorem G_dep (N k : ℕ) (hd : k + 2 ≤ N) (p : Fin N) : ∃ x : Fin N → Bool,G N k (update x p (!x p)) ≠ G N k x:=by
 by_cases hp : p.val < k
 · refine ⟨fun _=>false,?_⟩
   have h1 : G N k (update (fun _=>false) p (!false))=true:=by
    rw [G_iff];refine Or.inl ⟨p.val,hp,?_⟩
    rw [ext_update];simp
   have h0 : G N k (fun _=>false)=false:=by
    rw [← Bool.not_eq_true,G_iff]
    rintro (⟨i,_,hx⟩ | ⟨i,_,hx,_⟩) <;> simp [ext] at hx
   rw [h1,h0];simp
 · set q : ℕ:=if p.val + 1 < N then p.val + 1 else p.val - 1 with hq
   have hqN : q < N:=by rw [hq];split <;> omega
   have hqk : k ≤ q:=by have:=p.2;rw [hq];split <;> omega
   have hpq : p.val ≠ q:=by rw [hq];split <;> omega
   refine ⟨fun i : Fin N=>decide (i.val=q),?_⟩
   have hxp : (fun i : Fin N=>decide (i.val=q)) p=false:=by simp [hpq]
   rw [hxp]
   have h1 : G N k (update (fun i : Fin N=>decide (i.val=q)) p (!false))=true:=by
    rw [G_iff];right
    by_cases hc : p.val + 1 < N
    · have hqv : q=p.val + 1:=by rw [hq,ite_eq_left hc]
      refine ⟨p.val,by omega,?_,?_⟩
      · rw [ext_update];simp
      · rw [ext_update,ite_eq_right (by omega),ext_fn (fun j=>decide (j=q))];simp [hqv,hc]
    · have hqv : q=p.val - 1:=by rw [hq,ite_eq_right hc]
      refine ⟨q,hqk,?_,?_⟩
      · rw [ext_update,ite_eq_right (by omega),ext_fn (fun j=>decide (j=q))];simp [hqN]
      · rw [ext_update,ite_eq_left (by omega)];rfl
   have h0 : G N k (fun i : Fin N=>decide (i.val=q))=false:=by
    rw [← Bool.not_eq_true,G_iff];rintro (⟨i,hi,hx⟩ | ⟨i,_,hx,hy⟩)
    · rw [ext_fn (fun j=>decide (j=q))] at hx
      simp at hx;omega
    · rw [ext_fn (fun j=>decide (j=q))] at hx hy
      simp at hx hy;omega
   rw [h1,h0];simp
theorem G_lower : ∀ d : ℕ,2 ≤ d → ∀ k N s : ℕ,N=k + d → HasCircuitSize N (G N k) s → N + d / 2 ≤ s + 2:=by
 intro d
 induction d using Nat.strong_induction_on with
 | _ d ih =>
  intro hd k N s hN h
  by_cases hd4 : d < 4
  · have:=dep_lower N (G N k) (G_dep N k (by omega)) s h
    have : d / 2 ≤ 1:=by omega
    omega
  · obtain ⟨n,rfl⟩ : ∃ n,N=n + 1:=⟨N - 1,by omega⟩
    have hk : k < n:=by omega
    set p : Fin (n + 1):=⟨k,by omega⟩ with hp
    have hdep:=G_dep (n + 1) k (by omega) p
    have hnc : ∀ b : Bool,∃ x y : Fin (n + 1) → Bool, G (n + 1) k (update x p b) ≠ G (n + 1) k (update y p b):=by
     intro b;refine ⟨fun _=>false,fun i : Fin (n + 1)=>decide (i.val=k + 2 ∨ i.val=k + 3),?_⟩
     have h0 : G (n + 1) k (update (fun _=>false) p b)=false:=by
      rw [← Bool.not_eq_true,G_iff];rintro (⟨i,hi,hx⟩ | ⟨i,_,hx,hy⟩)
      · rw [ext_update,ite_eq_right (by simp [hp];omega)] at hx
        simp [ext] at hx
      · rw [ext_update] at hx hy
        rw [ite_eq_right (by simp [hp];omega)] at hy
        simp [ext] at hy
     have h1 : G (n + 1) k (update (fun i : Fin (n + 1)=>decide (i.val=k + 2 ∨ i.val=k + 3)) p b)=true:=by
      rw [G_iff]
      refine Or.inr ⟨k + 2,by omega,?_,?_⟩
      · rw [ext_update,ite_eq_right (by simp [hp]),ext_fn (fun j=>decide (j=k + 2 ∨ j=k + 3))]
        simp;omega
      · rw [ext_update,ite_eq_right (by simp [hp];omega),ext_fn (fun j=>decide (j=k + 2 ∨ j=k + 3))]
        simp;omega
     rw [h0,h1];simp
    obtain ⟨b,s',hs,h'⟩:=p1d n (G (n + 1) k) p s hdep hnc h;have h'':=relabel_size (del n k hk) _ s' h'
    cases b with
    | false =>
     have e : (fun y : Fin n → Bool => (fun x=>G (n + 1) k (update x p false)) (y ∘ del n k hk))=G n k:=by
      funext y;exact G_del_false n k hk y
     rw [e] at h''
     have:=ih (d - 1) (by omega) (by omega) k n s' (by omega) h''
     omega
    | true =>
     have e : (fun y : Fin n → Bool => (fun x=>G (n + 1) k (update x p true)) (y ∘ del n k hk))=G n (k + 1):=by
      funext y;exact G_del_true n k hk y
     rw [e] at h''
     have:=ih (d - 2) (by omega) (by omega) (k + 1) n s' (by omega) h''
     omega
def path (n : ℕ) (x : Fin n → Bool) : Bool :=
 decide (∃ i j : Fin n,i.val + 1=j.val ∧ x i=true ∧ x j=true)
theorem path_eq_G (n : ℕ) : path n=G n 0:=by{
funext x;simp [path,G]
}
theorem path_lower (n s : ℕ) (h : HasCircuitSize n (path n) s) : n + n / 2 ≤ s + 2:=by
 by_cases hn : n ≤ 1
 · have : n / 2=0:=by omega
   omega
 · rw [path_eq_G] at h
   exact G_lower n (by omega) 0 n s (by omega) h
end PathSize
namespace CycleSize.PG
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
open PEqualNP.Outside.L_meta_314_aux.PermInputs PEqualNP.Outside.L_meta_314_aux.PathSize
def pathB (w : List Bool) : ℕ → Bool
 | 0=>false
 | 1=>false
 | k + 2=>pathB w (k + 1) || (w.getD k false && w.getD (k + 1) false)
theorem pathB_iff (w : List Bool) : ∀ n : ℕ,pathB w n=true ↔ ∃ i,i + 1 < n ∧ w.getD i false=true ∧ w.getD (i + 1) false=true
 | 0=>by simp [pathB]
 | 1=>by simp [pathB]
 | k + 2=>by
  rw [pathB,Bool.or_eq_true,pathB_iff w (k + 1),Bool.and_eq_true];constructor
  · rintro (⟨i,hi,h1,h2⟩ | ⟨h1,h2⟩)
    · exact ⟨i,by omega,h1,h2⟩
    · exact ⟨k,by omega,h1,h2⟩
  · rintro ⟨i,hi,h1,h2⟩
    by_cases hik : i=k
    · subst hik;exact Or.inr ⟨h1,h2⟩
    · exact Or.inl ⟨i,by omega,h1,h2⟩
theorem pathB_step (w : List Bool) (n : ℕ) (hn : 1 ≤ n) : pathB w (n + 2)=(pathB w n || (w.getD n false && (w.getD (n - 1) false || w.getD (n + 1) false))):=by{
obtain ⟨n,rfl⟩ : ∃ k,n=k + 1:=⟨n - 1,by omega⟩
simp only [pathB,Nat.add_sub_cancel]
generalize pathB w (n + 1)=P
generalize w.getD n false=a
generalize w.getD (n + 1) false=b
generalize w.getD (n + 1 + 1) false=c
cases P <;> cases a <;> cases b <;> cases c <;> rfl
}
theorem three_gates (v : List Bool) (a b c o : ℕ) (_ha : a < v.length) (hb : b < v.length) (_hc : c < v.length) (ho : o < v.length) : (wiresFrom [⟨GateOp.or,[a,c]⟩,⟨GateOp.and,[b,v.length]⟩,⟨GateOp.or,[o,v.length + 1]⟩] v).getD (v.length + 2) false=(v.getD o false || (v.getD b false && (v.getD a false || v.getD c false))):=by{
have A : ∀ (t : List Bool) (i : ℕ),i < v.length → (v ++ t)[i]?.getD false=v[i]?.getD false:=by{
intro t i h;rw [List.getElem?_append_left h]
}
simp [wiresFrom,GateOp.eval,A _ _ hb,A _ _ ho]
}
theorem pathGates : ∀ n : ℕ,2 ≤ n → ∀ m : ℕ,n ≤ m → ∃ (gs : List Gate) (out : ℕ),(∀ g ∈ gs,Ok g) ∧ gs.length + 2=n + n / 2 ∧ out < m + gs.length ∧ ∀ w : List Bool,w.length=m → (wiresFrom gs w).getD out false=pathB w n:=by
 intro n
 induction n using Nat.strong_induction_on with
 | _ n ih =>
  intro hn m hm
  match n,hn,hm,ih with
  | 2,_,hm,_ =>
   refine ⟨[⟨GateOp.and,[0,1]⟩],m,?_,rfl,by simp,?_⟩
   · intro g hg;simp only [List.mem_singleton] at hg;subst hg;simp [Ok]
   · intro w hw;have A : ∀ (t : List Bool) (i : ℕ),i < w.length →
      (w ++ t)[i]?.getD false=w[i]?.getD false:=by
      intro t i h;rw [List.getElem?_append_left h]
     subst hw;simp [wiresFrom,GateOp.eval,pathB]
  | 3,_,hm,_ =>
   refine ⟨[⟨GateOp.or,[0,2]⟩,⟨GateOp.and,[1,m]⟩],m + 1,?_,rfl,by simp,?_⟩
   · intro g hg;simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
     rcases hg with rfl | rfl <;> simp [Ok]
   · intro w hw;have A : ∀ (t : List Bool) (i : ℕ),i < w.length →
      (w ++ t)[i]?.getD false=w[i]?.getD false:=by
      intro t i h;rw [List.getElem?_append_left h]
     subst hw
     simp [wiresFrom,GateOp.eval,pathB,A _ 1 (by omega)]
     generalize w[0]?.getD false=a
     generalize w[1]?.getD false=b
     generalize w[2]?.getD false=c
     cases a <;> cases b <;> cases c <;> simp
  | n + 4,_,hm,ih =>
   obtain ⟨gs,out,ok,len,hout,ev⟩:=ih (n + 2) (by omega) (by omega) m (by omega)
   refine ⟨gs ++ [⟨GateOp.or,[n + 1,n + 3]⟩,⟨GateOp.and,[n + 2,m + gs.length]⟩,
    ⟨GateOp.or,[out,m + gs.length + 1]⟩],m + gs.length + 2,?_,?_,by simp;omega,?_⟩
   · intro g hg
     rcases List.mem_append.1 hg with hg | hg
     · exact ok g hg
     · simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
       rcases hg with rfl | rfl | rfl <;> simp [Ok]
   · simp only [List.length_append,List.length_cons,List.length_nil]
     have : (n + 4) / 2=(n + 2) / 2 + 1:=by omega
     omega
   · intro w hw;rw [wiresFrom_append]
     set v:=wiresFrom gs w with hv
     have lv : v.length=m + gs.length:=by rw [hv,length_wiresFrom,hw]
     have e : ∀ i,i < m → v.getD i false=w.getD i false:=by intro i hi;rw [hv,getD_wiresFrom _ _ _ (by omega)]
     rw [← lv,three_gates v _ _ _ _ (by omega) (by omega) (by omega) (by omega),e (n + 1) (by omega),e (n + 2) (by omega),e (n + 3) (by omega),hv,ev w hw,pathB_step w (n + 2) (by omega)]
     rfl
theorem p1a {n : ℕ} (x : Fin n → Bool) (i : ℕ) : (List.ofFn x).getD i false=ext x i:=by
 unfold ext
 by_cases hi : i < n
 · rw [dite_eq_left hi];simp [hi]
 · rw [dite_eq_right hi,List.getD_eq_default _ _ (by simp;omega)]
end CycleSize.PG
namespace CycleSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
open PEqualNP.Outside.L_meta_314_aux.PermInputs PEqualNP.Outside.L_meta_314_aux.PathSize
open PEqualNP.Outside.L_meta_314_aux.CycleSize.PG
def cyc (n : ℕ) : (Fin n → Bool) → Bool :=
 fun x : Fin n → Bool=>decide (∃ i j : Fin n,(i.val + 1) % n=j.val ∧ x i=true ∧ x j=true)
theorem succ_mod_eq {i n : ℕ} (h : i < n) : (i + 1) % n=if i + 1=n then 0 else i + 1:=by
 split_ifs with h1
 · rw [h1,Nat.mod_self]
 · exact Nat.mod_eq_of_lt (by omega)
theorem cyc_iff_ext (n : ℕ) (x : Fin n → Bool) : cyc n x=true ↔ ∃ i,i < n ∧ ext x i=true ∧ ext x (if i + 1=n then 0 else i + 1)=true:=by{
unfold cyc;rw [decide_eq_true_iff];constructor
{
rintro ⟨i,j,hij,hi,hj⟩
refine ⟨i.val,i.2,by rw [ext_fin];exact hi,?_⟩
rw [← succ_mod_eq i.2,hij,ext_fin];exact hj
}
{
rintro ⟨i,hi,h1,h2⟩;have hl:=ext_lt h2;refine ⟨⟨i,hi⟩,⟨_,hl⟩,succ_mod_eq hi,?_,?_⟩
{rw [← ext_fin x ⟨i,hi⟩];exact h1}
{rw [← ext_fin x ⟨_,hl⟩];exact h2}
}
}
def rot (n c : ℕ) (i : Fin n) : Fin n:=⟨(i.val + c) % n,Nat.mod_lt _ (by have:=i.2;omega)⟩
theorem cyc_rot_imp (n c : ℕ) (x : Fin n → Bool) (h : cyc n (x ∘ rot n c)=true) : cyc n x=true:=by{
unfold cyc at h ⊢;rw [decide_eq_true_iff] at h ⊢;obtain ⟨i,j,hij,hi,hj⟩:=h;refine ⟨rot n c i,rot n c j,?_,hi,hj⟩
simp only [rot];rw [Nat.mod_add_mod,← hij,Nat.mod_add_mod];congr 1;omega
}
theorem rot_inv (n c : ℕ) (hc : c ≤ n) (i : Fin n) : rot n c (rot n (n - c) i)=i:=by
 apply Fin.ext;simp only [rot]
 rw [Nat.mod_add_mod,show i.val + (n - c) + c=i.val + n by omega,Nat.add_mod_right,
  Nat.mod_eq_of_lt i.2]
theorem cyc_rot (n c : ℕ) (hc : c ≤ n) (x : Fin n → Bool) : cyc n (x ∘ rot n c)=cyc n x:=by{
rw [Bool.eq_iff_iff];refine ⟨cyc_rot_imp n c x,fun h=>cyc_rot_imp n (n - c) (x ∘ rot n c) ?_⟩
have e : (x ∘ rot n c) ∘ rot n (n - c)=x:=by funext i;simp only [Function.comp_apply,rot_inv n c hc]
rw [e];exact h
}
theorem cyc_eq_path_or (m : ℕ) (hm : 2 ≤ m) (x : Fin (m + 1) → Bool) : cyc (m + 1) x=(pathB (List.ofFn x) m || (ext x m && (ext x (m - 1) || ext x 0))):=by
 rw [Bool.eq_iff_iff,cyc_iff_ext,Bool.or_eq_true,pathB_iff,Bool.and_eq_true,Bool.or_eq_true];simp only [p1a];constructor
 · rintro ⟨i,hi,h1,h2⟩
   by_cases h3 : i + 1 < m
   · rw [ite_eq_right (by omega)] at h2
     exact Or.inl ⟨i,h3,h1,h2⟩
   · by_cases h4 : i=m
     · subst h4;rw [ite_eq_left rfl] at h2;exact Or.inr ⟨h1,Or.inr h2⟩
     · rw [ite_eq_right (by omega),show i + 1=m by omega] at h2
       rw [show i=m - 1 by omega] at h1
       exact Or.inr ⟨h2,Or.inl h1⟩
 · rintro (⟨i,hi,h1,h2⟩ | ⟨h1,h2 | h2⟩)
   · exact ⟨i,by omega,h1,by rw [ite_eq_right (by omega)];exact h2⟩
   · exact ⟨m - 1,by omega,h2,by rw [ite_eq_right (by omega),show m - 1 + 1=m by omega];exact h1⟩
   · exact ⟨m,by omega,h1,by rw [ite_eq_left rfl];exact h2⟩
theorem cyc_upper (n s : ℕ) (hn : 3 ≤ n) (h : n + (n + 1) / 2 ≤ s + 1) : HasCircuitSize n (cyc n) s:=by
 obtain ⟨m,rfl⟩ : ∃ m,n=m + 1:=⟨n - 1,by omega⟩
 obtain ⟨gs,out,ok,len,hout,ev⟩:=pathGates m (by omega) (m + 1) (by omega)
 refine ⟨⟨gs ++ [⟨GateOp.or,[m - 1,0]⟩,⟨GateOp.and,[m,m + 1 + gs.length]⟩,⟨GateOp.or,[out,m + 1 + gs.length + 1]⟩],m + 1 + gs.length + 2⟩,?_,?_,?_⟩
 · intro g hg
   rcases List.mem_append.1 hg with hg | hg
   · exact ok g hg
   · simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
     rcases hg with rfl | rfl | rfl <;> simp
 · simp only [Circuit.size,List.length_append,List.length_cons,List.length_nil];omega
 · intro x;simp only [Circuit.eval,wires_eq];rw [wiresFrom_append]
   set w:=List.ofFn x with hw
   have hwl : w.length=m + 1:=by simp [hw]
   set v:=wiresFrom gs w with hv
   have lv : v.length=m + 1 + gs.length:=by rw [hv,length_wiresFrom,hwl]
   have e : ∀ i,i < m + 1 → v.getD i false=w.getD i false:=by intro i hi;rw [hv,getD_wiresFrom _ _ _ (by omega)]
   rw [← lv,three_gates v _ _ _ _ (by omega) (by omega) (by omega) (by omega),e (m - 1) (by omega),e m (by omega),e 0 (by omega),hv,ev w hwl,cyc_eq_path_or m (by omega) x,hw]
   simp only [p1a]
theorem ext_snoc (m : ℕ) (y : Fin m → Bool) (b : Bool) (j : ℕ) : ext (Fin.snoc y b : Fin (m + 1) → Bool) j=if j < m then ext y j else if j=m then b else false:=by
 unfold ext
 by_cases h1 : j < m
 · rw [dite_eq_left (by omega),ite_eq_left h1,dite_eq_left h1]
   simp [Fin.snoc,h1]
 · rw [ite_eq_right h1]
   by_cases h2 : j=m
   · subst h2;rw [dite_eq_left (by omega),ite_eq_left rfl]
     simp [Fin.snoc]
   · rw [dite_eq_right (by omega),ite_eq_right h2]
theorem cyc_snoc_false (m : ℕ) (y : Fin m → Bool) : cyc (m + 1) (Fin.snoc y false)=path m y:=by{
rw [Bool.eq_iff_iff,cyc_iff_ext,path_eq_G,G_iff];simp only [ext_snoc];constructor
{
rintro ⟨i,hi,h1,h2⟩
by_cases a : i + 1 < m
{
simp (disch:=omega) only [ite_eq_left,ite_eq_right] at h1 h2
exact Or.inr ⟨i,Nat.zero_le _,h1,h2⟩
}
{
by_cases b : i=m
{subst b;simp at h1}
{
simp (disch:=omega) only [ite_eq_left,ite_eq_right] at h2
simp at h2
}
}
}
{
rintro (⟨i,hi,_⟩ | ⟨i,_,h1,h2⟩)
{omega}
{
have:=ext_lt h2
refine ⟨i,by omega,?_,?_⟩ <;> simp (disch:=omega) only [ite_eq_left,ite_eq_right] <;> assumption
}
}
}
def tauN (m j : ℕ) : ℕ:=if j=0 then 0 else if j + 1=m then 1 else j + 1
def tau (m : ℕ) (j : Fin m) : Fin m:=⟨tauN m j.val % m,Nat.mod_lt _ (by have:=j.2;omega)⟩
theorem ext_tau (m : ℕ) (hm : 2 ≤ m) (z : Fin m → Bool) (j : ℕ) : ext (z ∘ tau m) j=if j < m then ext z (tauN m j) else false:=by{
unfold ext
by_cases h1 : j < m
{
have ht : tauN m j < m:=by unfold tauN;split_ifs <;> omega
rw [dite_eq_left h1,ite_eq_left h1,dite_eq_left ht];simp only [Function.comp_apply,tau,Nat.mod_eq_of_lt ht]
}
{rw [dite_eq_right h1,ite_eq_right h1]}
}
theorem cyc_snoc_true (m : ℕ) (hm : 3 ≤ m) (z : Fin m → Bool) : cyc (m + 1) (Fin.snoc (z ∘ tau m) true)=G m 2 z:=by
 rw [Bool.eq_iff_iff,cyc_iff_ext,G_iff]
 simp only [ext_snoc,ext_tau m (by omega)]
 constructor
 · rintro ⟨i,hi,h1,h2⟩
   by_cases h3 : i=m
   · subst h3
     simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right,ite_true] at h2
     exact Or.inl ⟨0,by omega,h2⟩
   · by_cases h4 : i + 1=m
     · simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right] at h1
       exact Or.inl ⟨1,by omega,h1⟩
     · by_cases h5 : i=0
       · subst h5
         simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right,ite_true] at h1
         exact Or.inl ⟨0,by omega,h1⟩
       · by_cases h6 : i + 2=m
         · simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right] at h2
           exact Or.inl ⟨1,by omega,h2⟩
         · simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right] at h1 h2
           exact Or.inr ⟨i + 1,by omega,h1,h2⟩
 · rintro (⟨i,hi,h⟩ | ⟨i,hi,h1,h2⟩)
   · by_cases h0 : i=0
     · subst h0
       refine ⟨m,by omega,?_,?_⟩
       · simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right,ite_true]
       · simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right,ite_true];exact h
     · have h1 : i=1:=by omega
       subst h1
       refine ⟨m - 1,by omega,?_,?_⟩
       · simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right];exact h
       · simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right,ite_true,show m - 1 + 1=m by omega]
   · have hl:=ext_lt h2
     refine ⟨i - 1,by omega,?_,?_⟩
     · simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right,show i - 1 + 1=i by omega]
       exact h1
     · simp (disch:=omega) only [tauN,ite_eq_left,ite_eq_right,show i - 1 + 1=i by omega]
       exact h2
theorem cyc_false_lower (m s : ℕ) (h : HasCircuitSize m (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y false)) s) : m + m / 2 ≤ s + 2:=by
 have e : (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y false))=path m :=
  funext (cyc_snoc_false m)
 rw [e] at h;exact path_lower m s h
theorem cyc_true_lower (m s : ℕ) (hm : 4 ≤ m) (h : HasCircuitSize m (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y true)) s) : m + (m - 2) / 2 ≤ s + 2:=by
 have h':=relabel_size (tau m) _ s h
 have e : (fun x : Fin m → Bool => (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y true)) (x ∘ tau m))=G m 2 :=
  funext fun z=>cyc_snoc_true m (by omega) z
 rw [e] at h'
 exact G_lower (m - 2) (by omega) 2 m s (by omega) h'
def piv (m : ℕ) (hm : 0 < m) (v : Fin (m + 1)) (i : Fin (m + 1)) : Fin m :=
 ⟨((i.val + (m - v.val)) % (m + 1)) % m,Nat.mod_lt _ hm⟩
theorem restrict_last (m : ℕ) (hm : 0 < m) (v : Fin (m + 1)) (b : Bool) (s : ℕ) (h : HasCircuitSize (m + 1) (fun x=>cyc (m + 1) (update x v b)) s) : HasCircuitSize m (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y b)) s:=by
 have h':=relabel_size (piv m hm v) _ s h
 have e : (fun y : Fin m → Bool => (fun x=>cyc (m + 1) (update x v b)) (y ∘ piv m hm v)) = fun y=>cyc (m + 1) (Fin.snoc y b):=by
  funext y
  simp only
  rw [← cyc_rot (m + 1) (v.val + 1) (by omega) (update (y ∘ piv m hm v) v b)]
  congr 1;funext i
  induction i using Fin.lastCases with
  | last =>
   have hl : rot (m + 1) (v.val + 1) (Fin.last m)=v:=by
    apply Fin.ext;simp only [rot,Fin.val_last]
    rw [show m + (v.val + 1)=v.val + (m + 1) by omega,Nat.add_mod_right,
     Nat.mod_eq_of_lt v.2]
   simp only [Function.comp_apply,hl,Function.update_self,Fin.snoc_last]
  | cast j =>
   have hj:=j.2;have hv:=v.2
   have hne : rot (m + 1) (v.val + 1) j.castSucc ≠ v:=by
    intro hc;have h0:=congrArg Fin.val hc;simp only [rot,Fin.val_castSucc] at h0
    rcases lt_or_ge (j.val + (v.val + 1)) (m + 1) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at h0;omega
    · rw [Nat.mod_eq_sub_mod h1,Nat.mod_eq_of_lt (by omega)] at h0;omega
   have hp : piv m hm v (rot (m + 1) (v.val + 1) j.castSucc)=j:=by
    apply Fin.ext;simp only [piv,rot,Fin.val_castSucc]
    rw [Nat.mod_add_mod,show j.val + (v.val + 1) + (m - v.val)=j.val + (m + 1) by omega,
     Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : j.val < m + 1),Nat.mod_eq_of_lt hj]
   simp only [Function.comp_apply,Function.update_of_ne hne,hp,Fin.snoc_castSucc]
 rw [e] at h';exact h'
theorem p22 (n s : ℕ) (hn : 5 ≤ n) (hs : s + 1 < n + (n + 1) / 2) (h3 : 3 ≤ s) : ¬ ((n - 1) + (n - 1) / 2 ≤ (s - 3) + 2):=by omega
theorem p29 (n s : ℕ) (hn : 5 ≤ n) (hs : s + 1 < n + (n + 1) / 2) (h4 : 4 ≤ s) : ¬ ((n - 1) + (n - 3) / 2 ≤ (s - 4) + 2):=by omega
def p26 : Prop :=
 ∀ n s : ℕ,5 ≤ n → s + 1 < n + (n + 1) / 2 → HasCircuitSize n (cyc n) s →
  ∃ v : Fin n,
   (3 ≤ s ∧ HasCircuitSize n (fun x=>cyc n (update x v false)) (s - 3)) ∨
   (4 ≤ s ∧ HasCircuitSize n (fun x=>cyc n (update x v true)) (s - 4))
theorem p8 (hcore : p26) : ∀ n s : ℕ,5 ≤ n → (PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool=>decide (∃ i j : Fin n,(i.val + 1) % n=j.val ∧ x i=true ∧ x j=true)) s ↔ n + (n + 1) / 2 ≤ s + 1):=by
 intro n s hn;constructor
 · intro h
   by_contra hlt
   have hs : s + 1 < n + (n + 1) / 2:=by omega
   obtain ⟨m,rfl⟩ : ∃ m,n=m + 1:=⟨n - 1,by omega⟩
   obtain ⟨v,⟨h3,hc⟩ | ⟨h4,hc⟩⟩:=hcore (m + 1) s hn hs h
   · have:=cyc_false_lower m (s - 3) (restrict_last m (by omega) v false (s - 3) hc)
     exact p22 (m + 1) s hn hs h3 (by simpa using this)
   · have:=cyc_true_lower m (s - 4) (by omega) (restrict_last m (by omega) v true (s - 4) hc)
     exact p29 (m + 1) s hn hs h4 (by omega)
 · exact cyc_upper n s (by omega)
end CycleSize
namespace CycleSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
open PEqualNP.Outside.L_meta_314_aux.PathSize
def p38 : Prop :=
 ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ),(∃ p : Fin (n + 1),∃ x : Fin (n + 1) → Bool,f (update x p (!x p)) ≠ f x) → (∀ p : Fin (n + 1),(∃ x : Fin (n + 1) → Bool,f (update x p (!x p)) ≠ f x) → ∀ b : Bool,∃ x y : Fin (n + 1) → Bool,f (update x p b) ≠ f (update y p b)) → (∀ p q : Fin (n + 1),p ≠ q → (∃ x : Fin (n + 1) → Bool,f (update x p (!x p)) ≠ f x) → (∃ x : Fin (n + 1) → Bool,f (update x q (!x q)) ≠ f x) → ¬ ∃ a b : Bool,∀ x : Fin (n + 1) → Bool,f (update (update x p (!a)) q b)=f (update (update x p a) q (!b)) ∧ f (update (update x p a) q (!b))=f (update (update x p (!a)) q (!b))) → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s → (∃ (y : Fin (n + 1)) (s' : ℕ),s' + 3 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x=>f (update x y false)) s') ∨ (∃ (y : Fin (n + 1)) (s' : ℕ),s' + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x=>f (update x y true)) s')
def sc (N i : ℕ) : ℕ:=if i + 1=N then 0 else i + 1
def pt (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : Fin N → Bool:=fun i=>decide (P i.val)
theorem p3a (N : ℕ) (P : ℕ → Prop) [DecidablePred P] : cyc N (pt N P)=true ↔ ∃ i,i < N ∧ P i ∧ P (sc N i):=by{
rw [cyc_iff_ext]
have e : ∀ j,j < N → ext (pt N P) j=decide (P j):=by intro j hj;simp [ext,pt,hj]
constructor
{
rintro ⟨i,hi,h1,h2⟩
have hs : sc N i < N:=by unfold sc;split_ifs <;> omega
refine ⟨i,hi,?_,?_⟩
{rw [e i hi] at h1;simpa using h1}
{unfold sc at hs ⊢;rw [e _ hs] at h2;simpa using h2}
}
{
rintro ⟨i,hi,h1,h2⟩
have hs : sc N i < N:=by unfold sc;split_ifs <;> omega
refine ⟨i,hi,?_,?_⟩
{rw [e i hi];simpa using h1}
{unfold sc at hs h2;rw [e _ hs];simpa using h2}
}
}
theorem p1f (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (h : ∀ i,i < N → P i → P (sc N i) → False) : cyc N (pt N P)=false:=by{
rw [← Bool.not_eq_true,p3a];rintro ⟨i,hi,h1,h2⟩;exact h i hi h1 h2
}
theorem p3b (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (p : Fin N) (v : Bool) : update (pt N P) p v=pt N (fun j=>(j=p.val ∧ v=true) ∨ (j ≠ p.val ∧ P j)):=by{
funext i
by_cases h : i=p
{subst h;simp [pt]}
{have h' : i.val ≠ p.val:=fun e=>h (Fin.ext e);rw [Function.update_of_ne h];simp [pt,h']}
}
theorem cyc_dep (N : ℕ) (hN : 3 ≤ N) (p : Fin N) : ∃ x : Fin N → Bool,cyc N (update x p (!x p)) ≠ cyc N x:=by
 have hp:=p.2;refine ⟨pt N (fun j=>j=sc N p.val),?_⟩
 have hx : pt N (fun j=>j=sc N p.val) p=false:=by simp only [pt,decide_eq_false_iff_not];unfold sc;split_ifs <;> omega
 have h1 : cyc N (pt N (fun j=>j=sc N p.val))=false :=
  p1f N _ (by intro i hi h1 h2;unfold sc at h1 h2;split_ifs at h1 h2 <;> omega)
 have h2 : cyc N (pt N (fun j=>(j=p.val ∧ true=true) ∨ (j ≠ p.val ∧ j=sc N p.val)))=true:=by
  rw [p3a]
  exact ⟨p.val,hp,Or.inl ⟨rfl,rfl⟩,Or.inr ⟨by unfold sc;split_ifs <;> omega,rfl⟩⟩
 rw [hx,p3b,Bool.not_false,h1,h2];decide
theorem cyc_nonconst (N : ℕ) (hN : 3 ≤ N) (p : Fin N) (b : Bool) : ∃ x y : Fin N → Bool,cyc N (update x p b) ≠ cyc N (update y p b):=by
 have hp:=p.2;refine ⟨pt N (fun _=>False),pt N (fun j=>j=sc N p.val ∨ j=sc N (sc N p.val)),?_⟩
 have h1 : cyc N (pt N (fun j=>(j=p.val ∧ b=true) ∨ (j ≠ p.val ∧ False)))=false :=
  p1f N _ (by
   intro i hi h1 h2;simp only [and_false,or_false] at h1 h2;have a1:=h1.1;have a2:=h2.1
   unfold sc at a2;split_ifs at a2 <;> omega)
 have h2 : cyc N (pt N (fun j=>(j=p.val ∧ b=true) ∨ (j ≠ p.val ∧ (j=sc N p.val ∨ j=sc N (sc N p.val)))))=true:=by
  rw [p3a]
  refine ⟨sc N p.val,by unfold sc;split_ifs <;> omega,?_,?_⟩
  · right;exact ⟨by unfold sc;split_ifs <;> omega,Or.inl rfl⟩
  · right;exact ⟨by unfold sc;split_ifs <;> omega,Or.inr rfl⟩
 rw [p3b,p3b,h1,h2];decide
theorem p28 (N : ℕ) (hN : 5 ≤ N) (p q : ℕ) (hp : p < N) (hq : q < N) (hpq : p ≠ q) : ∃ r,r < N ∧ r ≠ p ∧ r ≠ q ∧ (sc N p=r ∨ sc N r=p) ∧ sc N q ≠ r ∧ sc N r ≠ q:=by{
by_cases h : q=sc N p ∨ q=sc N (sc N p)
{
refine ⟨if p=0 then N - 1 else p - 1,?_⟩
unfold sc at h ⊢
split_ifs at h ⊢ <;> omega
}
{
refine ⟨sc N p,?_⟩
unfold sc at h ⊢
split_ifs at h ⊢ <;> omega
}
}
theorem p32 (N : ℕ) (hN : 5 ≤ N) (p q : Fin N) (hpq : p ≠ q) (c : Bool) : ∃ x : Fin N → Bool,cyc N (update (update x p true) q c)=true ∧ cyc N (update (update x p false) q c)=false:=by
 have hpq' : p.val ≠ q.val:=fun e=>hpq (Fin.ext e);obtain ⟨r,hr,hrp,hrq,hadj,hn1,hn2⟩:=p28 N hN p.val q.val p.2 q.2 hpq';refine ⟨pt N (fun j=>j=r),?_,?_⟩
 · rw [p3b,p3b,p3a]
   rcases hadj with h | h
   · refine ⟨p.val,p.2,Or.inr ⟨hpq',Or.inl ⟨rfl,rfl⟩⟩,Or.inr ⟨?_,Or.inr ⟨?_,?_⟩⟩⟩ <;>
      rw [h] <;> assumption
   · refine ⟨r,hr,Or.inr ⟨hrq,Or.inr ⟨hrp,rfl⟩⟩,Or.inr ⟨?_,Or.inl ⟨h,rfl⟩⟩⟩
     rw [h];exact hpq'
 · rw [p3b,p3b];apply p1f;intro i hi h1 h2;unfold sc at h2 hn1 hn2
   cases c <;> simp only [Bool.false_eq_true,and_false,false_or,and_true] at h1 h2 <;>
    split_ifs at h2 hn1 hn2 <;> omega
theorem cyc_no_funnel (N : ℕ) (hN : 5 ≤ N) (p q : Fin N) (hpq : p ≠ q) : ¬ ∃ a b : Bool,∀ x : Fin N → Bool,cyc N (update (update x p (!a)) q b)=cyc N (update (update x p a) q (!b)) ∧ cyc N (update (update x p a) q (!b))=cyc N (update (update x p (!a)) q (!b)):=by
 rintro ⟨a,b,h⟩;obtain ⟨x,h1,h2⟩:=p32 N hN p q hpq (!b);have e:=(h x).2;cases a
 · rw [Bool.not_false,h1,h2] at e;exact absurd e (by decide)
 · rw [Bool.not_true,h1,h2] at e;exact absurd e (by decide)
theorem p30 {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (h : HasCircuitSize n f s) (hst : s ≤ t) : HasCircuitSize n f t:=by{
obtain ⟨C,h1,h2,h3⟩:=h;exact ⟨C,h1,le_trans h2 hst,h3⟩
}
theorem p6 (h107 : p38) : p26:=by
 intro N s hN hs hc
 obtain ⟨n,rfl⟩ : ∃ n,N=n + 1:=⟨N - 1,by omega⟩
 rcases h107 n (cyc (n + 1)) s ⟨⟨0,by omega⟩,cyc_dep (n + 1) (by omega) _⟩
  (fun p _ b=>cyc_nonconst (n + 1) (by omega) p b)
  (fun p q hpq _ _=>cyc_no_funnel (n + 1) hN p q hpq) hc with
  ⟨y,s',hle,hC⟩ | ⟨y,s',hle,hC⟩
 · exact ⟨y,Or.inl ⟨by omega,p30 hC (by omega)⟩⟩
 · exact ⟨y,Or.inr ⟨by omega,p30 hC (by omega)⟩⟩
theorem cyc_exact_of_readers (h107 : p38) : ∀ n s : ℕ,5 ≤ n → (PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool=>decide (∃ i j : Fin n,(i.val + 1) % n=j.val ∧ x i=true ∧ x j=true)) s ↔ n + (n + 1) / 2 ≤ s + 1) :=
 p8 (p6 h107)
end CycleSize
theorem cycleTheorem : ∀ n s : ℕ,5 ≤ n → (PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool=>decide (∃ i j : Fin n,(i.val + 1) % n=j.val ∧ x i=true ∧ x j=true)) s ↔ n + (n + 1) / 2 ≤ s + 1) :=
 PEqualNP.Outside.L_meta_314_aux.CycleSize.cyc_exact_of_readers PEqualNP.Outside.L_meta_314_aux.readerTheorem
namespace Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def cycFun (n : ℕ) (x : Fin n → Bool) : Bool :=
 decide (∃ i j : Fin n,(i.val + 1) % n=j.val ∧ x i=true ∧ x j=true)
theorem cycFun_eq_cyc (n : ℕ) : cycFun n=CycleSize.cyc n:=rfl
theorem hasCircuitSize_of_fanInTwo {n : ℕ} {C : Circuit} (hf : FanInTwo C) : HasCircuitSize n (circuitFun n C) C.size:=by{
refine ⟨C,?_,le_rfl,fun _=>rfl⟩
intro g hg;exact hf g hg
}
theorem cyc_size_lower {n : ℕ} (hn : 5 ≤ n) {D : Circuit} (hf : FanInTwo D) (he : circuitFun n D=cycFun n) : n + (n + 1) / 2 - 1 ≤ D.size:=by{
have h1 : HasCircuitSize n (cycFun n) D.size:=by{
rw [← he];exact hasCircuitSize_of_fanInTwo hf
}
have h2:=(cycleTheorem n D.size hn).mp h1;omega
}
theorem minimal_cyc_size_eq {n : ℕ} (hn : 5 ≤ n) {C : Circuit} (hmin : IsMinimalCircuit n C) (he : circuitFun n C=cycFun n) : C.size=n + (n + 1) / 2 - 1:=by
 have hlo:=cyc_size_lower hn hmin.1 he
 have hup:=CycleSize.cyc_upper n (n + (n + 1) / 2 - 1) (by omega) (by omega)
 obtain ⟨D,hDok,hDsz,hDev⟩:=hup;have hDf : FanInTwo D:=fun g hg=>hDok g hg;have hDe : circuitFun n D=cycFun n:=funext hDev;have hminD:=hmin.2 D hDf (hDe.trans he.symm);omega
theorem cyc_false_size_lower {n : ℕ} (hn : 5 ≤ n) (p : Fin n) {D : Circuit} (hf : FanInTwo D) (he : circuitFun n D=fun x=>cycFun n (update x p false)) : n + (n + 1) / 2 - 4 ≤ D.size:=by
 obtain ⟨m,rfl⟩ : ∃ m,n=m + 1:=⟨n - 1,by omega⟩
 have h1 : HasCircuitSize (m + 1) (fun x=>CycleSize.cyc (m + 1) (update x p false)) D.size:=by
  rw [← cycFun_eq_cyc,← he];exact hasCircuitSize_of_fanInTwo hf
 have h2:=CycleSize.cyc_false_lower m D.size (CycleSize.restrict_last m (by omega) p false D.size h1)
 omega
theorem cyc_true_size_lower {n : ℕ} (hn : 5 ≤ n) (p : Fin n) {D : Circuit} (hf : FanInTwo D) (he : circuitFun n D=fun x=>cycFun n (update x p true)) : n + (n + 1) / 2 - 5 ≤ D.size:=by
 obtain ⟨m,rfl⟩ : ∃ m,n=m + 1:=⟨n - 1,by omega⟩
 have h1 : HasCircuitSize (m + 1) (fun x=>CycleSize.cyc (m + 1) (update x p true)) D.size:=by
  rw [← cycFun_eq_cyc,← he];exact hasCircuitSize_of_fanInTwo hf
 have h2:=CycleSize.cyc_true_lower m D.size (by omega) (CycleSize.restrict_last m (by omega) p true D.size h1)
 omega
end Bridge
end PEqualNP.Outside.L_meta_314_aux

namespace PEqualNP.Outside.L_meta_314_aux.NoNot
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
open Function (update)
open PEqualNP.Outside.L_meta_314_aux.PermInputs PEqualNP.Outside.L_meta_314_aux.Readers
open PEqualNP.Outside.L_meta_314_aux.PathSize PEqualNP.Outside.L_meta_314_aux.CycleSize
def HasNotCircuitSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
 ∃ C : Circuit,FanInTwo C ∧ C.size ≤ s ∧ (∃ g ∈ C.gates,g.op=GateOp.not) ∧
  ∀ x : Fin n → Bool,C.eval (List.ofFn x)=f x
theorem hasNot_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t) (h : HasNotCircuitSize n f s) : HasNotCircuitSize n f t:=by{
obtain ⟨C,ok,hsz,hnot,hev⟩:=h;exact ⟨C,ok,le_trans hsz hst,hnot,hev⟩
}
theorem relabel_hasNot {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ) (hc : HasNotCircuitSize n h s) : HasNotCircuitSize m (fun x=>h (x ∘ π)) s:=by{
obtain ⟨C,ok,hsz,⟨g0,hg0,hop0⟩,hev⟩:=hc;refine ⟨relabel n m π C,?_,?_,?_,?_⟩
{
intro g hg;obtain ⟨g1,hg1,rfl⟩:=List.mem_map.1 hg
exact ⟨(ok g1 hg1).1,by simpa [relGate] using (ok g1 hg1).2⟩
}
{simpa [relabel,Circuit.size] using hsz}
{exact ⟨relGate n m π g0,List.mem_map.2 ⟨g0,hg0,rfl⟩,hop0⟩}
{intro x;show _=h (x ∘ π);rw [← hev (x ∘ π)];exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output}
}
theorem n8 {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 1) (h : Cnt t L) : Cnt t (L ++ [gateSupp L g]):=by{
intro W
by_cases hW : L.length ∈ W
{
have hsub : (W.biUnion fun j=>(L ++ [gateSupp L g]).getD j ∅) ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j=>L.getD j ∅):=by{
intro i hi;rw [Finset.mem_biUnion] at hi ⊢;obtain ⟨j,hjW,hij⟩:=hi
by_cases hjl : j=L.length
{subst hjl;rw [getD_snoc_eq] at hij;obtain ⟨a,ha,hia⟩:=(mem_gateSupp L g i).1 hij;exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩}
{rw [getD_snoc_ne _ _ _ _ hjl] at hij;exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩}
}
have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 1:=by{
refine le_trans (Finset.card_union_le _ _) ?_
rw [Finset.card_erase_of_mem hW];exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
}
have hWpos : 1 ≤ W.card:=Finset.card_pos.2 ⟨_,hW⟩;have h1:=h (W.erase L.length ∪ g.inputs.toFinset);have h2:=Finset.card_le_card hsub;omega
}
{
have heq : (W.biUnion fun j=>(L ++ [gateSupp L g]).getD j ∅) = (W.biUnion fun j=>L.getD j ∅):=by{
apply Finset.biUnion_congr rfl;intro j hj;exact getD_snoc_ne _ _ _ _ (fun e=>hW (e ▸ hj))
}
rw [heq];exact h W
}
}
theorem n6 {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),(∀ g ∈ gs,NOk g) → (∃ g ∈ gs,g.op=GateOp.not) → Cnt t L → Cnt (t + (gs.length - 1)) (suppsFrom gs L):=by{
induction gs with
| nil =>{
intro _ _ _ ⟨g,hg,_⟩ _
simp at hg
}
| cons g gs ih =>{
intro t L hnok hnot hcnt;have hnok_tl : ∀ g' ∈ gs,NOk g':=fun g' hg'=>hnok g' (List.mem_cons_of_mem _ hg');have hok_tl : ∀ g' ∈ gs,Ok g':=fun g' hg'=>(hnok_tl g' hg').1
by_cases hgn : g.op=GateOp.not
{have hstep:=n8 t L g ((hnok g List.mem_cons_self).2 hgn) hcnt;have hrest:=cnt_suppsFrom gs t (L ++ [gateSupp L g]) hok_tl hstep;simpa only [suppsFrom,List.foldl_cons,List.length_cons,Nat.add_sub_cancel] using hrest}
{
obtain ⟨g',hg',hop'⟩:=hnot
have hg'_tl : g' ∈ gs:=by{
rcases List.mem_cons.1 hg' with rfl | hmem
{exact absurd hop' hgn}
{exact hmem}
}
have hpos : 1 ≤ gs.length:=List.length_pos_of_mem hg'_tl;have hstep:=cnt_step t L g (hnok g List.mem_cons_self).1.2 hcnt;have hrest:=ih (t + 1) (L ++ [gateSupp L g]) hnok_tl ⟨g',hg'_tl,hop'⟩ hstep
have heq : t + 1 + (gs.length - 1)=t + ((g :: gs).length - 1):=by simp only [List.length_cons];omega
rw [heq] at hrest;exact hrest
}
}
}
theorem dep_lower_with_not (n : ℕ) (f : (Fin n → Bool) → Bool) (hdep : ∀ i : Fin n,∃ x : Fin n → Bool,f (update x i (!x i)) ≠ f x) (s : ℕ) (h : HasNotCircuitSize n f s) : n ≤ s:=by
 obtain ⟨C,ok,hsz,⟨g0,hg0,hop0⟩,hev⟩:=h;have hsz' : C.gates.length ≤ s:=hsz;let gs:=C.gates.map normGate
 have hnok : ∀ g ∈ gs,NOk g:=by
  intro g hg;obtain ⟨g1,hg1,rfl⟩:=List.mem_map.1 hg;exact normGate_nok g1 (ok g1 hg1)
 have hnot : ∃ g ∈ gs,g.op=GateOp.not :=
  ⟨normGate g0,List.mem_map.2 ⟨g0,hg0,rfl⟩,by simp [normGate,hop0]⟩
 have hlen : gs.length=C.gates.length:=List.length_map _;have hpos : 1 ≤ gs.length:=List.length_pos_of_mem hnot.choose_spec.1
 set S:=(suppsFrom gs (inputSupps n)).getD C.output ∅ with hS
 have hall : ∀ i : Fin n,i ∈ S:=by
  intro i
  by_contra hi
  obtain ⟨x,hx⟩:=hdep i;apply hx
  have hag:=(agree_wiresFrom (update x i (!x i)) x gs _ _ _ (agree_inputs _ _)).2.2 C.output (by
   intro k hk;have : k ≠ i:=fun e=>hi (e ▸ hk)
   simp [Function.update_of_ne this])
  have he1 : wiresFrom gs (List.ofFn (update x i (!x i))) = wiresFrom C.gates (List.ofFn (update x i (!x i))) :=
   wiresFrom_norm C.gates _
  have he2 : wiresFrom gs (List.ofFn x)=wiresFrom C.gates (List.ofFn x) :=
   wiresFrom_norm C.gates _
  rw [he1,he2] at hag;rw [← hev,← hev];exact hag
 have hcard : S.card=n:=by rw [Finset.eq_univ_of_forall hall];simp
 have hc:=n6 gs 0 (inputSupps n) hnok hnot cnt_inputs {C.output};simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at hc;rw [← hS,hcard] at hc;omega
theorem n7 {m : ℕ} {g : Gate} (hg : CleanGate m g) (hnot : g.op=GateOp.not) : ∃ a,a < m ∧ g.inputs=[a]:=by{
rcases hg with ⟨_,a,ha,hin⟩ | ⟨hbin,_⟩
{exact ⟨a,ha,hin⟩}
{rcases hbin with h1 | h1 <;> rw [hnot] at h1 <;> cases h1}
}
theorem nc (n : ℕ) (gs : List Gate) : ∀ (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) → acc.1.length=n + acc.2.length → (∀ w < acc.1.length,acc.1.getD w (Sum.inl false)=Sum.inr w) → (elim n gs acc).2.length=acc.2.length + gs.length → (elim n gs acc).2=acc.2 ++ gs.map normGate ∧ (∀ w < (elim n gs acc).1.length,(elim n gs acc).1.getD w (Sum.inl false)=Sum.inr w):=by
 induction gs with
 | nil =>
  intro acc _ _ hid _
  exact ⟨by simp [elim],hid⟩
 | cons g gs ih =>
  intro acc hok hlen hid hfull
  have hstep_le : (elimStep n acc g).2.length ≤ acc.2.length + 1:=by
   simp only [elimStep,List.length_append];have:=toList_length_le (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1;omega
  have hrest_le : (elim n gs (elimStep n acc g)).2.length ≤ (elimStep n acc g).2.length + gs.length :=
   elim_len n gs (elimStep n acc g)
  have heq_step : (elimStep n acc g).2.length=acc.2.length + 1:=by
   change (elim n gs (elimStep n acc g)).2.length=acc.2.length + (gs.length + 1) at hfull;omega
  have heq_rest : (elim n gs (elimStep n acc g)).2.length=(elimStep n acc g).2.length + gs.length:=by
   change (elim n gs (elimStep n acc g)).2.length=acc.2.length + (gs.length + 1) at hfull;omega
  have hsimp_some : ∃ g', (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1=some g':=by
   cases ho : (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1 with
   | none =>
    simp only [elimStep,ho,Option.toList_none,List.append_nil] at heq_step;omega
   | some g'=>exact ⟨g',rfl⟩
  obtain ⟨g',hg'⟩:=hsimp_some;have hokg : Ok g:=hok g List.mem_cons_self;have hgate_res : g'=normGate g ∧
   (simplify g.op (n + acc.2.length) (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).2 =
    Sum.inr (n + acc.2.length):=by
   have hget : ∀ a,acc.1.getD a (Sum.inl false) = if a < acc.1.length then Sum.inr a else Sum.inl false:=by
    intro a
    by_cases ha : a < acc.1.length
    · rw [ite_eq_left_iff.2 (fun h=>(h ha).elim),hid a ha]
    · rw [ite_eq_right_iff.2 (fun h=>(ha h).elim),List.getD_eq_default _ _ (by omega)]
   have hop_cases : g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not:=by simpa using hokg.1
   rcases hop_cases with hop | hop | hop
   · rcases hin : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
     · simp [simplify,simpAnd,hop,hin] at hg'
     · rw [hop,hin] at hg';simp only [List.map_cons,List.map_nil,simplify,simpAnd,hget] at hg'
       by_cases ha : a < acc.1.length <;> simp [ha] at hg'
     · rw [hop] at hg' ⊢;simp only [hin,List.map_cons,List.map_nil,simplify,simpAnd,hget] at hg' ⊢
       by_cases ha : a < acc.1.length <;> by_cases hb : b < acc.1.length
       · simp only [ha,hb,↓reduceIte,Option.some.injEq] at hg' ⊢;refine ⟨?_,trivial⟩
         subst hg';cases g;simp_all [normGate]
       · simp [ha,hb] at hg'
       · simp [ha,hb] at hg'
       · simp [ha,hb] at hg'
     · have:=hokg.2;rw [hin] at this;simp at this
   · rcases hin : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
     · simp [simplify,simpOr,hop,hin] at hg'
     · rw [hop,hin] at hg';simp only [List.map_cons,List.map_nil,simplify,simpOr,hget] at hg'
       by_cases ha : a < acc.1.length <;> simp [ha] at hg'
     · rw [hop] at hg' ⊢;simp only [hin,List.map_cons,List.map_nil,simplify,simpOr,hget] at hg' ⊢
       by_cases ha : a < acc.1.length <;> by_cases hb : b < acc.1.length
       · simp only [ha,hb,↓reduceIte,Option.some.injEq] at hg' ⊢;refine ⟨?_,trivial⟩
         subst hg';cases g;simp_all [normGate]
       · simp [ha,hb] at hg'
       · simp [ha,hb] at hg'
       · simp [ha,hb] at hg'
     · have:=hokg.2;rw [hin] at this;simp at this
   · rcases hin : g.inputs with _ | ⟨a,rest⟩
     · simp [simplify,simpNot,hop,hin] at hg'
     · rw [hop] at hg' ⊢;simp only [hin,List.map_cons,simplify,simpNot,hget] at hg' ⊢
       by_cases ha : a < acc.1.length
       · simp only [ha,↓reduceIte,Option.some.injEq] at hg' ⊢;refine ⟨?_,trivial⟩
         subst hg';cases g;simp_all [normGate]
       · simp [ha] at hg'
  have hstep_fst : (elimStep n acc g).1=acc.1 ++ [Sum.inr (n + acc.2.length)]:=by simp only [elimStep,hgate_res.2]
  have hstep_snd : (elimStep n acc g).2=acc.2 ++ [normGate g]:=by simp only [elimStep,hg',hgate_res.1,Option.toList_some]
  have hlen' : (elimStep n acc g).1.length=n + (elimStep n acc g).2.length:=by rw [hstep_fst,hstep_snd];simp;omega
  have hid' : ∀ w < (elimStep n acc g).1.length, (elimStep n acc g).1.getD w (Sum.inl false)=Sum.inr w:=by
   intro w hw;rw [hstep_fst] at hw ⊢
   by_cases hwl : w < acc.1.length
   · rw [getD_snoc_ne _ _ _ _ (by omega)];exact hid w hwl
   · have hwe : w=acc.1.length:=by simp at hw;omega
     subst hwe;rw [getD_snoc_eq,hlen]
  obtain ⟨ih1,ih2⟩:=ih (elimStep n acc g) (fun g1 hg1=>hok g1 (List.mem_cons_of_mem _ hg1))
   hlen' hid' heq_rest
  refine ⟨?_,ih2⟩
  change (elim n gs (elimStep n acc g)).2=_;rw [ih1,hstep_snd,List.append_assoc,List.map_cons];rfl
theorem least_of_minimal (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (hnc : ∃ x y : Fin n → Bool,f x ≠ f y) (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=f) : CleanL n (C.gates.map normGate) ∧ Least n f (C.gates.map normGate) C.output ∧ C.output < n + C.gates.length ∧ (∀ x : Fin n → Bool,∀ w : ℕ,vl (C.gates.map normGate) x w=(C.wires (List.ofFn x)).getD w false):=by
 have hok : ∀ g ∈ C.gates,Ok g:=hmin.1;have hev : ∀ x : Fin n → Bool,C.eval (List.ofFn x)=f x:=fun x=>congrFun hfun x
 set acc:=elim n C.gates (idStats n,[]) with hacc
 have hinv : ∀ y : Fin n → Bool,Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
  fun y=>inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
 have hval : ∀ y : Fin n → Bool, (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))=f y:=by
  intro y;rw [((hinv y).2 C.output).2,← hev y];rfl
 have hcl : CleanL n acc.2 :=
  clean_elim n (List.ofFn fun _ : Fin n=>false) (by simp) C.gates _ _ hok
   (inv_id n _) (by intro p g hp;simp at hp)
 cases hst : acc.1.getD C.output (Sum.inl false) with
 | inl c =>
  exfalso;obtain ⟨y,y',hne⟩:=hnc;apply hne;rw [← hval y,← hval y',hst];rfl
 | inr j =>
  have hle : acc.2.length ≤ C.gates.length:=by
   have:=elim_len n C.gates (idStats n,[]);rw [← hacc] at this;simp only [List.length_nil,zero_add] at this;exact this
  have hge : C.gates.length ≤ acc.2.length:=by
   have hD:=has_of_clean n acc.2 j hcl;obtain ⟨D,hDok,hDsz,hDev⟩:=hD
   have hDfun : circuitFun n D=circuitFun n C:=by
    funext x;rw [hfun];show D.eval (List.ofFn x)=f x;rw [hDev x];have:=hval x;rw [hst] at this;exact this
   have:=hmin.2 D hDok hDfun;exact le_trans this hDsz
  have heq_len : acc.2.length=C.gates.length:=le_antisymm hle hge
  have hid0 : ∀ w < (idStats n,([] : List Gate)).1.length, (idStats n,([] : List Gate)).1.getD w (Sum.inl false)=Sum.inr w:=by
   intro w hw;simp only [idStats,List.length_ofFn] at hw;simp [idStats,hw]
  obtain ⟨hmap,hid1⟩:=nc n C.gates (idStats n,[]) hok (by simp [idStats]) hid0
   (by simpa [hacc] using heq_len)
  rw [List.nil_append] at hmap
  have hacc_len : acc.1.length=n + C.gates.length:=by rw [hacc,elim_fst_len];simp [idStats]
  have hout_lt : C.output < n + C.gates.length:=by
   by_contra hge'
   have hdef : acc.1.getD C.output (Sum.inl false)=Sum.inl false :=
    List.getD_eq_default _ _ (by omega)
   rw [hdef] at hst;cases hst
  have hj_eq : j=C.output:=by
   have h1:=hid1 C.output (by rw [← hacc,hacc_len];exact hout_lt)
   rw [← hacc,hst] at h1;exact Sum.inr.inj h1
  subst hj_eq
  have hcl_map : CleanL n (C.gates.map normGate):=by rw [← hmap];exact hcl
  have hvl_eq : ∀ (x : Fin n → Bool) (w : ℕ), vl (C.gates.map normGate) x w=(C.wires (List.ofFn x)).getD w false:=by
   intro x w;unfold vl;rw [wiresFrom_norm C.gates (List.ofFn x),wires_eq]
  have hleast : Least n f (C.gates.map normGate) C.output:=by
   refine ⟨hcl_map,fun x=>by rw [hvl_eq x C.output];exact hev x,?_⟩
   intro gs' o' hc' he';obtain ⟨D,hDok,hDsz,hDev⟩:=has_of_clean n gs' o' hc'
   have hDfun : circuitFun n D=circuitFun n C:=by
    funext x;rw [hfun];show D.eval (List.ofFn x)=f x;rw [hDev x];exact he' x
   have h1:=hmin.2 D hDok hDfun;have h2 : C.gates.length ≤ gs'.length:=le_trans h1 hDsz;simpa only [List.length_map] using h2
  exact ⟨hcl_map,hleast,hout_lt,hvl_eq⟩
theorem n1 (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (h : ∃ g' ∈ acc.2,g'.op=GateOp.not) : ∃ g' ∈ (elimStep n acc g).2,g'.op=GateOp.not:=by{
obtain ⟨g',hg',hop⟩:=h;exact ⟨g',List.mem_append_left _ hg',hop⟩
}
theorem n4 (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,(∃ g' ∈ acc.2,g'.op=GateOp.not) → ∃ g' ∈ (elim n gs acc).2,g'.op=GateOp.not:=by{
induction gs with
| nil=>intro acc h;exact h
| cons g gs ih =>{
intro acc h;exact ih (elimStep n acc g) (n1 n acc g h)
}
}
theorem n0 (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool) (u : ℕ) (gu : Gate) (hgu : gs[u]?=some gu) (hop : gu.op=GateOp.not) (hnrc : ¬ RC n gs i b u) : ∃ g' ∈ passG n gs i b,g'.op=GateOp.not:=by{
have hu : u < gs.length:=(List.getElem?_eq_some_iff.1 hgu).1
let pre:=gs.take u;let post:=gs.drop (u + 1)
have hgs : gs=pre ++ gu :: post:=by{
have h1:=List.getElem?_eq_some_iff.1 hgu
dsimp [pre,post];rw [← h1.2,List.cons_getElem_drop_succ,List.take_append_drop]
}
have hpre_len : pre.length=u:=by simp [pre];omega
obtain ⟨a,halt,hin⟩:=n7 (hcl u gu hgu) hop;unfold passG;rw [hgs,elim_append];change ∃ g' ∈ (elim n post (elimStep n (elim n pre (statAt n i b,[])) gu)).2,g'.op=GateOp.not;apply n4 n post
have hst_a : (elim n pre (statAt n i b,[])).1.getD a (Sum.inl false)=stF n gs i b a:=by{
unfold stF;rw [hgs]
have hlt : a < (statAt n i b,([] : List Gate)).1.length + pre.length:=by rw [statAt_length,hpre_len];omega
exact (elim_split_getD_lt n pre gu post (statAt n i b,[]) a (Sum.inl false) hlt).symm
}
cases hfa : stF n gs i b a with
| inl c =>{
exfalso
exact hnrc ⟨gu,hgu,a,by rw [hin];simp,c,hfa⟩
}
| inr w =>{
refine ⟨⟨GateOp.not,[w]⟩,?_,rfl⟩
unfold elimStep;rw [hop,hin];simp only [List.map_cons,List.map_nil,hst_a,hfa,simplify,simpNot,Option.toList_some,List.mem_append,List.mem_singleton];exact Or.inr trivial
}
}
theorem nf {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ} (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (S : Finset ℕ) (hS : ∀ p ∈ S,RC n gs i b p) (u : ℕ) (gu : Gate) (hgu : gs[u]?=some gu) (hop : gu.op=GateOp.not) (hnrc : ¬ RC n gs i b u) : ∃ s' : ℕ,s' + S.card ≤ gs.length ∧ HasNotCircuitSize (n + 1) (fun x=>f (update x i b)) s':=by
 have hL : (statAt n i b,([] : List Gate)).1.length=n + 1:=statAt_length n i b
 have hcount:=elim_count n (statAt n i b,[]) gs (clean_nok _ gs L.hcl) S (by
  intro p hp;obtain ⟨g,hg,a,ha,c,hc⟩:=hS p hp;refine ⟨g,hg,a,ha,?_,c,hc⟩
  rw [hL]
  exact (L.hcl p g hg).lt a ha)
 simp only [List.length_nil,zero_add] at hcount
 cases hst : stF n gs i b o with
 | inl c =>
  exfalso;obtain ⟨x,y,hxy⟩:=hnc;exact hxy ((restr_const L.hcl L.hev i b c hst x).trans (restr_const L.hcl L.hev i b c hst y).symm)
 | inr j =>
  have hc : CleanL n (passG n gs i b) :=
   clean_elim n (List.ofFn fun _ : Fin n=>false) (by simp) gs _ _
    (fun g hg=>(clean_nok _ gs L.hcl g hg).1) (inv_at n i b _) (by intro p g hp;simp at hp)
  have hnot : ∃ g' ∈ passG n gs i b,g'.op=GateOp.not :=
   n0 n gs L.hcl i b u gu hgu hop hnrc
  have hhas : HasNotCircuitSize n (fun y=>vl (passG n gs i b) y j) (passG n gs i b).length:=by refine ⟨⟨passG n gs i b,j⟩,fun g hg=>(clean_nok n _ hc g hg).1,le_refl _,hnot,fun _=>rfl⟩
  have h2:=relabel_hasNot (Fin.succAbove i) _ _ hhas;have e : (fun x : Fin (n + 1) → Bool=>f (update x i b))
   = fun x=>vl (passG n gs i b) (x ∘ Fin.succAbove i) j:=by
   funext x;rw [upd_ins,← L.hev,st_val_wire n gs L.hcl i b o j hst];rfl
  refine ⟨(passG n gs i b).length,hcount,?_⟩
  rw [e];exact h2
theorem nb {n : ℕ} {gs : List Gate} (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool) (u : ℕ) (gu : Gate) (hgu : gs[u]?=some gu) (hop : gu.op=GateOp.not) (hrc : RC n gs i b u) : IsC n gs i b (n + 1 + u):=by{
obtain ⟨g',hg',a,ha,c,hc⟩:=hrc;have e : g'=gu:=gate_eq hg' hgu rfl;subst e;apply st_allconst n gs hcl i b u g' hgu;intro w hw;obtain ⟨j,_,hin⟩:=n7 (hcl u g' hgu) hop;rw [hin] at ha hw
simp at ha hw
rw [hw,← ha];exact ⟨c,hc⟩
}
theorem ne {n : ℕ} {gs : List Gate} (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool) (p : ℕ) (gp : Gate) (hgp : gs[p]?=some gp) (hop : gp.op=GateOp.not) (a : ℕ) (ha : a ∈ gp.inputs) (c : Bool) (hc : stF n gs i b a=Sum.inl c) : stF n gs i b (n + 1 + p)=Sum.inl (!c):=by{
obtain ⟨t,ht⟩:=st_gate n gs hcl i b p gp hgp;obtain ⟨j,_,hin⟩:=n7 (hcl p gp hgp) hop;rw [hin] at ha
simp at ha
subst ha;rw [ht,hop,hin];simp [simplify,simpNot,hc]
}
theorem n10 {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ} (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool) (hnc : ∃ x y : Fin (n + 1) → Bool,f (update x i b) ≠ f (update y i b)) (p1 p2 p3 p4 p5 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h15 : p1 ≠ p5) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h25 : p2 ≠ p5) (h34 : p3 ≠ p4) (h35 : p3 ≠ p5) (h45 : p4 ≠ p5) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) (h5 : RC n gs i b p5) : Drop f i b 5 gs.length:=by
 have:=L.save i b hnc {p1,p2,p3,p4,p5} (by
  intro p hp;simp only [Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption)
 have hcard : ({p1,p2,p3,p4,p5} : Finset ℕ).card=5:=by rw [Finset.card_insert_of_notMem (by simp [h12,h13,h14,h15]),Finset.card_insert_of_notMem (by simp [h23,h24,h25]),Finset.card_eq_three.2 ⟨p3,p4,p5,h34,h35,h45,rfl⟩]
 rwa [hcard] at this
theorem G_lower_with_not : ∀ d : ℕ,2 ≤ d → ∀ k N s : ℕ,N=k + d → HasNotCircuitSize N (G N k) s → N + d / 2 ≤ s + 1:=by
 intro d
 induction d using Nat.strong_induction_on with
 | _ d ih =>
  intro hd k N s hN hnotC
  by_cases hd4 : d < 4
  · have h1:=dep_lower_with_not N (G N k) (G_dep N k (by omega)) s hnotC
    have : d / 2 ≤ 1:=by omega
    omega
  · by_cases hsm : HasCircuitSize N (G N k) (s - 1)
    · have h1:=G_lower d hd k N (s - 1) hN hsm
      have hpos : 1 ≤ s:=by
       obtain ⟨C,_,hsz,⟨g,hg,_⟩,_⟩:=hnotC;have:=List.length_pos_of_mem hg;change C.gates.length ≤ s at hsz;omega
      omega
    · obtain ⟨C,okC,hszC,⟨g0,hg0,hop0⟩,hevC⟩:=hnotC
      have hsz_eq : C.size=s:=by
       by_contra hne
       have hlt : C.size ≤ s - 1:=by omega
       exact hsm ⟨C,okC,hlt,hevC⟩
      have hminC : IsMinimalCircuit N C:=by
       refine ⟨okC,fun D hDok hDfun=>?_⟩
       by_contra hlt
       push Not at hlt
       have hDsz : D.size ≤ s - 1:=by omega
       exact hsm ⟨D,hDok,hDsz,fun x=>(congrFun hDfun x).trans (hevC x)⟩
      obtain ⟨n,rfl⟩ : ∃ n,N=n + 1:=⟨N - 1,by omega⟩
      have hk : k < n:=by omega
      set p : Fin (n + 1):=⟨k,by omega⟩ with hp_def
      have hdep:=G_dep (n + 1) k (by omega) p
      have hnc : ∀ b : Bool,∃ x y : Fin (n + 1) → Bool, G (n + 1) k (update x p b) ≠ G (n + 1) k (update y p b):=by
       intro b;refine ⟨fun _=>false,fun i : Fin (n + 1)=>decide (i.val=k + 2 ∨ i.val=k + 3),?_⟩
       have h0 : G (n + 1) k (update (fun _=>false) p b)=false:=by
        rw [← Bool.not_eq_true,G_iff];rintro (⟨i,hi,hx⟩ | ⟨i,_,hx,hy⟩)
        · rw [ext_update,ite_eq_right_iff.2 (fun h=>by simp [hp_def] at h;omega)] at hx
          simp [ext] at hx
        · rw [ext_update] at hx hy
          rw [ite_eq_right_iff.2 (fun h=>by simp [hp_def] at h;omega)] at hy
          simp [ext] at hy
       have h1 : G (n + 1) k (update (fun i : Fin (n + 1)=>decide (i.val=k + 2 ∨ i.val=k + 3)) p b)=true:=by
        rw [G_iff]
        refine Or.inr ⟨k + 2,by omega,?_,?_⟩
        · rw [ext_update,ite_eq_right_iff.2 (fun h=>by simp [hp_def] at h),
           ext_fn (fun j=>decide (j=k + 2 ∨ j=k + 3))]
          simp;omega
        · rw [ext_update,ite_eq_right_iff.2 (fun h=>by simp [hp_def] at h;omega),
           ext_fn (fun j=>decide (j=k + 2 ∨ j=k + 3))]
          simp;omega
       rw [h0,h1];simp
      have hfnc : ∃ x y : Fin (n + 1) → Bool,G (n + 1) k x ≠ G (n + 1) k y:=dep_nc hdep;obtain ⟨hcl,L,_,_⟩:=least_of_minimal (n + 1) (G (n + 1) k) C hfnc hminC (funext hevC)
      set gs:=C.gates.map normGate with hgs_def
      have hgs_len : gs.length=s:=by rw [hgs_def,List.length_map];exact hsz_eq
      obtain ⟨u,hgu⟩ : ∃ u,gs[u]?=some (normGate g0) :=
       List.mem_iff_getElem?.1 (List.mem_map.2 ⟨g0,hg0,rfl⟩)
      have hu_op : (normGate g0).op=GateOp.not:=by simp [normGate,hop0]
      have hclose_drop3 : ∀ b : Bool,Drop (G (n + 1) k) p b 3 gs.length → n + 1 + d / 2 ≤ s + 1:=by
       intro b ⟨s',hs',hC'⟩;have h'':=relabel_size (del n k hk) _ s' hC'
       cases b with
       | false =>
        have e : (fun y : Fin n → Bool => (fun x=>G (n + 1) k (update x p false)) (y ∘ del n k hk))=G n k :=
         funext (G_del_false n k hk)
        rw [e] at h''
        have:=G_lower (d - 1) (by omega) k n s' (by omega) h''
        omega
       | true =>
        have e : (fun y : Fin n → Bool => (fun x=>G (n + 1) k (update x p true)) (y ∘ del n k hk))=G n (k + 1) :=
         funext (G_del_true n k hk)
        rw [e] at h''
        have:=G_lower (d - 2) (by omega) (k + 1) n s' (by omega) h''
        omega
      have hclose_not2 : ∀ b : Bool, (∃ s',s' + 2 ≤ gs.length ∧ HasNotCircuitSize (n + 1) (fun x=>G (n + 1) k (update x p b)) s') → n + 1 + d / 2 ≤ s + 1:=by
       intro b ⟨s',hs',hC'⟩;have h'':=relabel_hasNot (del n k hk) _ s' hC'
       cases b with
       | false =>
        have e : (fun y : Fin n → Bool => (fun x=>G (n + 1) k (update x p false)) (y ∘ del n k hk))=G n k :=
         funext (G_del_false n k hk)
        rw [e] at h''
        have:=ih (d - 1) (by omega) (by omega) k n s' (by omega) h''
        omega
       | true =>
        have e : (fun y : Fin n → Bool => (fun x=>G (n + 1) k (update x p true)) (y ∘ del n k hk))=G n (k + 1) :=
         funext (G_del_true n k hk)
        rw [e] at h''
        have:=ih (d - 2) (by omega) (by omega) (k + 1) n s' (by omega) h''
        omega
      obtain ⟨r,hr⟩:=L.dep_read p hdep hnc;obtain ⟨gr,hgr,hir⟩:=hr;have hr_reads : Reads gs r p:=⟨gr,hgr,hir⟩
      by_cases hrn : gr.op=GateOp.not
      · have ho_ne : C.output ≠ n + 1 + r:=by
         intro e;obtain ⟨x,y,hxy⟩:=hnc false;apply hxy;have hcr : IsC n gs p false (n + 1 + r):=isC_reader hcl p r gr hgr hir false (Or.inl hrn);obtain ⟨c,hc⟩:=hcr;rw [← e] at hc;exact (restr_const hcl L.hev p false c hc x).trans (restr_const hcl L.hev p false c hc y).symm
        obtain ⟨J,hrJ,hJr⟩:=L.live hfnc r (List.getElem?_eq_some_iff.1 hgr).1 ho_ne
        obtain ⟨gJ,hgJ,hr_in_J⟩:=hJr
        have hJn : gJ.op ≠ GateOp.not:=by
         intro hJnot;obtain ⟨a,_,hinr⟩:=n7 (hcl r gr hgr) hrn;obtain ⟨a',_,hinJ⟩:=n7 (hcl J gJ hgJ) hJnot;rw [hinr] at hir;simp at hir;subst hir;rw [hinJ] at hr_in_J;simp at hr_in_J;subst hr_in_J
         exact L.no_alias hfnc J (List.getElem?_eq_some_iff.1 hgJ).1 p.val (by have:=p.2;omega)
          (fun x=>by rw [vl_not gs hcl x J gJ hgJ _ hJnot hinJ,vl_not gs hcl x r gr hgr _ hrn hinr,Bool.not_not])
        let b:=!(fixBit gJ)
        have hst_r : stF n gs p b (n + 1 + r)=Sum.inl (fixBit gJ):=by
         have h1:=ne hcl p b r gr hgr hrn p.val hir b (stF_self n gs p b);simpa [b] using h1
        have hIsCJ : IsC n gs p b (n + 1 + J):=const_read n gs hcl p b J gJ hgJ (n + 1 + r) hr_in_J hst_r;obtain ⟨K,hJK,_,hKrc⟩:=L.next p b (hnc b) J (List.getElem?_eq_some_iff.1 hgJ).1 hIsCJ
        have hJrc : RC n gs p b J:=⟨gJ,hgJ,n + 1 + r,hr_in_J,fixBit gJ,hst_r⟩
        exact hclose_drop3 b (L.save3 p b (hnc b) r J K (by omega) (by omega) (by omega) (rc_input b hr_reads) hJrc hKrc)
      · let b:=fixBit gr;have hIsCr : IsC n gs p b (n + 1 + r):=isC_reader hcl p r gr hgr hir b (Or.inr rfl);obtain ⟨J,hrJ,_,hJrc⟩:=L.next p b (hnc b) r (List.getElem?_eq_some_iff.1 hgr).1 hIsCr
        by_cases hurc : RC n gs p b u
        · by_cases huJ : u=J
          · subst huJ;have hIsCu : IsC n gs p b (n + 1 + u):=nb hcl p b u _ hgu hu_op hurc;obtain ⟨K,huK,_,hKrc⟩:=L.next p b (hnc b) u (List.getElem?_eq_some_iff.1 hgu).1 hIsCu
            exact hclose_drop3 b (L.save3 p b (hnc b) r u K (by omega) (by omega) (by omega) (rc_input b hr_reads) hurc hKrc)
          · have hur : r ≠ u:=by
             rintro rfl;have e:=gate_eq hgr hgu rfl
             exact hrn (by rw [e];exact hu_op)
            exact hclose_drop3 b (L.save3 p b (hnc b) r J u (by omega) hur (Ne.symm huJ) (rc_input b hr_reads) hJrc hurc)
        · have hnot2:=nf L p b (hnc b) {r,J} (by
           intro x hx;simp only [Finset.mem_insert,Finset.mem_singleton] at hx
           rcases hx with rfl | rfl
           · exact rc_input b hr_reads
           · exact hJrc) u _ hgu hu_op hurc
          rw [Finset.card_pair (by omega : r ≠ J)] at hnot2
          exact hclose_not2 b hnot2
theorem n2 (m : ℕ) (hm : 0 < m) (v : Fin (m + 1)) (b : Bool) (s : ℕ) (h : HasNotCircuitSize (m + 1) (fun x=>cyc (m + 1) (update x v b)) s) : HasNotCircuitSize m (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y b)) s:=by
 have h':=relabel_hasNot (piv m hm v) _ s h
 have e : (fun y : Fin m → Bool => (fun x=>cyc (m + 1) (update x v b)) (y ∘ piv m hm v)) = fun y=>cyc (m + 1) (Fin.snoc y b):=by
  funext y
  simp only
  rw [← cyc_rot (m + 1) (v.val + 1) (by omega) (update (y ∘ piv m hm v) v b)]
  congr 1;funext i
  induction i using Fin.lastCases with
  | last =>
   have hl : rot (m + 1) (v.val + 1) (Fin.last m)=v:=by
    apply Fin.ext;simp only [rot,Fin.val_last]
    rw [show m + (v.val + 1)=v.val + (m + 1) by omega,Nat.add_mod_right,
     Nat.mod_eq_of_lt v.2]
   simp only [Function.comp_apply,hl,Function.update_self,Fin.snoc_last]
  | cast j =>
   have hj:=j.2;have hv:=v.2
   have hne : rot (m + 1) (v.val + 1) j.castSucc ≠ v:=by
    intro hc;have h0:=congrArg Fin.val hc;simp only [rot,Fin.val_castSucc] at h0
    rcases lt_or_ge (j.val + (v.val + 1)) (m + 1) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at h0;omega
    · rw [Nat.mod_eq_sub_mod h1,Nat.mod_eq_of_lt (by omega)] at h0;omega
   have hp : piv m hm v (rot (m + 1) (v.val + 1) j.castSucc)=j:=by
    apply Fin.ext;simp only [piv,rot,Fin.val_castSucc]
    rw [Nat.mod_add_mod,show j.val + (v.val + 1) + (m - v.val)=j.val + (m + 1) by omega,
     Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : j.val < m + 1),Nat.mod_eq_of_lt hj]
   simp only [Function.comp_apply,Function.update_of_ne hne,hp,Fin.snoc_castSucc]
 rw [e] at h';exact h'
theorem cyc_false_lower_with_not (m s : ℕ) (hm : 2 ≤ m) (h : HasNotCircuitSize m (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y false)) s) : m + m / 2 ≤ s + 1:=by
 have e : (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y false))=G m 0:=by
  rw [← path_eq_G];exact funext (cyc_snoc_false m)
 rw [e] at h
 exact G_lower_with_not m hm 0 m s (by omega) h
theorem cyc_true_lower_with_not (m s : ℕ) (hm : 4 ≤ m) (h : HasNotCircuitSize m (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y true)) s) : m + (m - 2) / 2 ≤ s + 1:=by
 have h':=relabel_hasNot (tau m) _ s h
 have e : (fun x : Fin m → Bool => (fun y : Fin m → Bool=>cyc (m + 1) (Fin.snoc y true)) (x ∘ tau m))=G m 2 :=
  funext fun z=>cyc_snoc_true m (by omega) z
 rw [e] at h'
 exact G_lower_with_not (m - 2) (by omega) 2 m s (by omega) h'
theorem n5 {m : ℕ} (gs : List Gate) (hcl : CleanL m gs) (t : ℕ) (ht : t < gs.length) (gnew : Gate) (hcl' : CleanL m (gs.set t gnew)) (x : Fin m → Bool) (hagree : gnew.op.eval (gnew.inputs.map fun a=>vl gs x a)=vl gs x (m + t)) : ∀ k,vl (gs.set t gnew) x k=vl gs x k:=by
 intro k
 induction k using Nat.strong_induction_on with
 | _ k ih =>
  by_cases hkm : k < m
  · rw [vl_input _ x k hkm,vl_input _ x k hkm]
  · by_cases hkl : m + gs.length ≤ k
    · rw [vl_beyond _ x k (by simp;omega),vl_beyond _ x k hkl]
    · let r:=k - m
      have hr : r < gs.length:=by omega
      have hk_eq : k=m + r:=by omega
      rw [hk_eq]
      by_cases hrt : r=t
      · subst hrt
        have hget : (gs.set r gnew)[r]?=some gnew:=by simp [hr]
        rw [vl_gate (gs.set r gnew) hcl' x r gnew hget];have hmap : (gnew.inputs.map fun a=>vl (gs.set r gnew) x a) =
         gnew.inputs.map fun a=>vl gs x a :=
         List.map_congr_left fun a ha=>ih a (by have:=(hcl' r gnew hget).lt a ha;omega)
        rw [hmap];exact hagree
      · obtain ⟨gr,hgr⟩ : ∃ gr,gs[r]?=some gr:=⟨gs[r],List.getElem?_eq_getElem hr⟩
        have hget : (gs.set t gnew)[r]?=some gr:=by rw [List.getElem?_set_ne (Ne.symm hrt)];exact hgr
        rw [vl_gate (gs.set t gnew) hcl' x r gr hget,vl_gate gs hcl x r gr hgr];congr 1
        exact List.map_congr_left fun a ha=>ih a (by have:=(hcl r gr hgr).lt a ha;omega)
theorem n9 {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ} (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (i : Fin m) (p q J : ℕ) (hpq : p ≠ q) (gp gq gJ : Gate) (hgp : gs[p]?=some gp) (hgq : gs[q]?=some gq) (hgJ : gs[J]?=some gJ) (hp_not : gp.op=GateOp.not) (hp_in : gp.inputs=[i.val]) (hq_or : gq.op=GateOp.or) (w : ℕ) (hw_lt : w < m + q) (hq_in : gq.inputs=[i.val,w] ∨ gq.inputs=[w,i.val]) (hJ_and : gJ.op=GateOp.and) (hJ_in : gJ.inputs=[m + p,m + q] ∨ gJ.inputs=[m + q,m + p]) (ho_ne : o ≠ m + q) (honly : ∀ k,Reads gs k (m + q) → k=J) : False:=by
 have hJlen : J < gs.length:=(List.getElem?_eq_some_iff.1 hgJ).1
 have hqlen : q < gs.length:=(List.getElem?_eq_some_iff.1 hgq).1
 have hpJ : m + p < m + J:=(L.hcl J gJ hgJ).lt (m + p) (by rcases hJ_in with h | h <;> rw [h] <;> simp)
 have hqJ : m + q < m + J:=(L.hcl J gJ hgJ).lt (m + q) (by rcases hJ_in with h | h <;> rw [h] <;> simp)
 let gnew : Gate:=⟨GateOp.and,[m + p,w]⟩;let gs1:=gs.set J gnew
 have hcl1 : CleanL m gs1:=by
  intro r gr hgr
  by_cases hrJ : r=J
  · subst hrJ
    have : gs1[r]?=some gnew:=by simp [gs1,hJlen]
    have e:=gate_eq hgr this rfl;subst e
    exact Or.inr ⟨Or.inl rfl,m + p,w,hpJ,by omega,rfl⟩
  · rw [List.getElem?_set_ne (Ne.symm hrJ)] at hgr
    exact L.hcl r gr hgr
 have hvl1 : ∀ (x : Fin m → Bool) (k : ℕ),vl gs1 x k=vl gs x k:=by
  intro x;apply n5 gs L.hcl J hJlen gnew hcl1 x
  have hv_p : vl gs x (m + p)=!vl gs x i.val:=vl_not gs L.hcl x p gp hgp i.val hp_not hp_in
  have hv_q : vl gs x (m + q)=(vl gs x i.val || vl gs x w):=by
   rw [vl_gate gs L.hcl x q gq hgq,hq_or]
   rcases hq_in with h | h <;> rw [h] <;> simp [GateOp.eval,Bool.or_comm]
  have hv_J : vl gs x (m + J)=(vl gs x (m + p) && vl gs x (m + q)):=by
   rw [vl_gate gs L.hcl x J gJ hgJ,hJ_and]
   rcases hJ_in with h | h <;> rw [h] <;> simp [GateOp.eval,Bool.and_comm]
  rw [hv_J,hv_q,hv_p];simp only [gnew,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,Bool.and_true,hv_p]
  cases vl gs x i.val <;> cases vl gs x w <;> rfl
 have hno1 : ∀ k,¬ Reads gs1 k (m + q):=by
  rintro k ⟨gk,hgk,hin⟩
  by_cases hkJ : k=J
  · subst hkJ
    have : gs1[k]?=some gnew:=by simp [gs1,hJlen]
    have e:=gate_eq hgk this rfl;subst e
    simp [gnew] at hin
    omega
  · rw [List.getElem?_set_ne (Ne.symm hkJ)] at hgk
    exact hkJ (honly k ⟨gk,hgk,hin⟩)
 have hnc1 : ∃ y y' : Fin m → Bool,vl gs1 y o ≠ vl gs1 y' o:=by
  obtain ⟨x,y,hxy⟩:=L.ncv hnc
  exact ⟨x,y,by rw [hvl1 x o,hvl1 y o];exact hxy⟩
 obtain ⟨gs',o',hc',hl',he'⟩:=drop_dead m gs1 hcl1 o q (by simp [gs1];exact hqlen) ho_ne hno1 hnc1
 have hmin:=L.hmin gs' o' hc' (fun x=>by rw [he' x,hvl1 x o];exact L.hev x)
 simp only [gs1,List.length_set] at hl';omega
theorem na {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ} (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (i : Fin m) (p J q : ℕ) (gp gJ gq : Gate) (hgp : gs[p]?=some gp) (hgJ : gs[J]?=some gJ) (hgq : gs[q]?=some gq) (hp_not : gp.op=GateOp.not) (hp_in : gp.inputs=[i.val]) (hJ_and : gJ.op=GateOp.and) (w : ℕ) (hw_lt : w < m + J) (hJ_in : gJ.inputs=[m + p,w] ∨ gJ.inputs=[w,m + p]) (hq_or : gq.op=GateOp.or) (hq_in : gq.inputs=[i.val,m + J] ∨ gq.inputs=[m + J,i.val]) (ho_ne : o ≠ m + J) (honly : ∀ k,Reads gs k (m + J) → k=q) : False:=by
 have hJlen : J < gs.length:=(List.getElem?_eq_some_iff.1 hgJ).1
 have hqlen : q < gs.length:=(List.getElem?_eq_some_iff.1 hgq).1
 have hJq : m + J < m + q:=(L.hcl q gq hgq).lt (m + J) (by rcases hq_in with h | h <;> rw [h] <;> simp)
 let gnew : Gate:=⟨GateOp.or,[i.val,w]⟩;let gs1:=gs.set q gnew
 have hcl1 : CleanL m gs1:=by
  intro r gr hgr
  by_cases hrq : r=q
  · subst hrq
    have : gs1[r]?=some gnew:=by simp [gs1,hqlen]
    have e:=gate_eq hgr this rfl;subst e
    exact Or.inr ⟨Or.inr rfl,i.val,w,by have:=i.2;omega,by omega,rfl⟩
  · rw [List.getElem?_set_ne (Ne.symm hrq)] at hgr
    exact L.hcl r gr hgr
 have hvl1 : ∀ (x : Fin m → Bool) (k : ℕ),vl gs1 x k=vl gs x k:=by
  intro x;apply n5 gs L.hcl q hqlen gnew hcl1 x
  have hv_p : vl gs x (m + p)=!vl gs x i.val:=vl_not gs L.hcl x p gp hgp i.val hp_not hp_in
  have hv_J : vl gs x (m + J)=(vl gs x (m + p) && vl gs x w):=by
   rw [vl_gate gs L.hcl x J gJ hgJ,hJ_and]
   rcases hJ_in with h | h <;> rw [h] <;> simp [GateOp.eval,Bool.and_comm]
  have hv_q : vl gs x (m + q)=(vl gs x i.val || vl gs x (m + J)):=by
   rw [vl_gate gs L.hcl x q gq hgq,hq_or]
   rcases hq_in with h | h <;> rw [h] <;> simp [GateOp.eval,Bool.or_comm]
  rw [hv_q,hv_J,hv_p];simp only [gnew,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,Bool.or_false]
  cases vl gs x i.val <;> cases vl gs x w <;> rfl
 have hno1 : ∀ k,¬ Reads gs1 k (m + J):=by
  rintro k ⟨gk,hgk,hin⟩
  by_cases hkq : k=q
  · subst hkq
    have : gs1[k]?=some gnew:=by simp [gs1,hqlen]
    have e:=gate_eq hgk this rfl;subst e
    simp [gnew] at hin
    have:=i.2;omega
  · rw [List.getElem?_set_ne (Ne.symm hkq)] at hgk
    exact hkq (honly k ⟨gk,hgk,hin⟩)
 have hnc1 : ∃ y y' : Fin m → Bool,vl gs1 y o ≠ vl gs1 y' o:=by
  obtain ⟨x,y,hxy⟩:=L.ncv hnc
  exact ⟨x,y,by rw [hvl1 x o,hvl1 y o];exact hxy⟩
 obtain ⟨gs',o',hc',hl',he'⟩:=drop_dead m gs1 hcl1 o J (by simp [gs1];exact hJlen) ho_ne hno1 hnc1
 have hmin:=L.hmin gs' o' hc' (fun x=>by rw [he' x,hvl1 x o];exact L.hev x)
 simp only [gs1,List.length_set] at hl';omega
theorem nd {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ} (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (i : Fin m) (p u q : ℕ) (gp gu gq : Gate) (hgp : gs[p]?=some gp) (hgu : gs[u]?=some gu) (hgq : gs[q]?=some gq) (hp_or : gp.op=GateOp.or) (w : ℕ) (hw_lt : w < m + p) (hp_in : gp.inputs=[i.val,w] ∨ gp.inputs=[w,i.val]) (hu_not : gu.op=GateOp.not) (hu_in : gu.inputs=[m + p]) (hq_or : gq.op=GateOp.or) (hq_in : gq.inputs=[i.val,m + u] ∨ gq.inputs=[m + u,i.val]) (ho_p : o ≠ m + p) (honly_p : ∀ k,Reads gs k (m + p) → k=u) (ho_u : o ≠ m + u) (honly_u : ∀ k,Reads gs k (m + u) → k=q) : False:=by
 have hplen : p < gs.length:=(List.getElem?_eq_some_iff.1 hgp).1
 have hulen : u < gs.length:=(List.getElem?_eq_some_iff.1 hgu).1
 have hpu : m + p < m + u:=(L.hcl u gu hgu).lt (m + p) (by rw [hu_in];simp)
 have huq : m + u < m + q:=(L.hcl q gq hgq).lt (m + u) (by rcases hq_in with h | h <;> rw [h] <;> simp)
 let gnew : Gate:=⟨GateOp.not,[w]⟩;let gs1:=gs.set u gnew
 have hcl1 : CleanL m gs1:=by
  intro r gr hgr
  by_cases hru : r=u
  · subst hru
    have : gs1[r]?=some gnew:=by simp [gs1,hulen]
    have e:=gate_eq hgr this rfl;subst e
    exact Or.inl ⟨rfl,w,by omega,rfl⟩
  · rw [List.getElem?_set_ne (Ne.symm hru)] at hgr
    exact L.hcl r gr hgr
 have hvl1 : ∀ (x : Fin m → Bool) (k : ℕ),k ≠ m + u → vl gs1 x k=vl gs x k:=by
  intro x k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
   intro hku
   by_cases hkm : k < m
   · rw [vl_input _ x k hkm,vl_input _ x k hkm]
   · by_cases hkl : m + gs.length ≤ k
     · rw [vl_beyond _ x k (by simp [gs1];omega),vl_beyond _ x k hkl]
     · let r:=k - m
       have hr : r < gs.length:=by omega
       have hk_eq : k=m + r:=by omega
       have hru : r ≠ u:=by omega
       rw [hk_eq]
       by_cases hrq : r=q
       · subst hrq
         have hget : gs1[r]?=some gq:=by rw [List.getElem?_set_ne (Ne.symm hru)];exact hgq
         rw [vl_gate gs1 hcl1 x r gq hget,vl_gate gs L.hcl x r gq hgq,hq_or]
         have hget_u : gs1[u]?=some gnew:=by simp [gs1,hulen]
         have hvu1 : vl gs1 x (m + u)=!vl gs x w:=by
          rw [vl_not gs1 hcl1 x u gnew hget_u w rfl rfl]
          rw [ih w (by omega) (by omega)]
         have hvi1 : vl gs1 x i.val=vl gs x i.val:=by rw [vl_input _ x i.val i.2,vl_input _ x i.val i.2]
         have hvp : vl gs x (m + p)=(vl gs x i.val || vl gs x w):=by
          rw [vl_gate gs L.hcl x p gp hgp,hp_or]
          rcases hp_in with h | h <;> rw [h] <;> simp [GateOp.eval,Bool.or_comm]
         have hvu : vl gs x (m + u)=!vl gs x (m + p):=vl_not gs L.hcl x u gu hgu (m + p) hu_not hu_in
         rcases hq_in with h | h <;> rw [h] <;>
          simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,Bool.or_false,hvu1,hvi1,hvu,hvp] <;>
          cases vl gs x i.val <;> cases vl gs x w <;> rfl
       · obtain ⟨gr,hgr⟩ : ∃ gr,gs[r]?=some gr:=⟨gs[r],List.getElem?_eq_getElem hr⟩
         have hget : gs1[r]?=some gr:=by rw [List.getElem?_set_ne (Ne.symm hru)];exact hgr
         rw [vl_gate gs1 hcl1 x r gr hget,vl_gate gs L.hcl x r gr hgr];congr 1
         refine List.map_congr_left fun a ha=>ih a (by have:=(L.hcl r gr hgr).lt a ha;omega) ?_
         intro heq;exact hrq (honly_u r ⟨gr,hgr,heq ▸ ha⟩)
 have hno1 : ∀ k,¬ Reads gs1 k (m + p):=by
  rintro k ⟨gk,hgk,hin⟩
  by_cases hku : k=u
  · subst hku
    have : gs1[k]?=some gnew:=by simp [gs1,hulen]
    have e:=gate_eq hgk this rfl;subst e
    simp [gnew] at hin
    omega
  · rw [List.getElem?_set_ne (Ne.symm hku)] at hgk
    exact hku (honly_p k ⟨gk,hgk,hin⟩)
 have hnc1 : ∃ y y' : Fin m → Bool,vl gs1 y o ≠ vl gs1 y' o:=by
  obtain ⟨x,y,hxy⟩:=L.ncv hnc
  exact ⟨x,y,by rw [hvl1 x o ho_u,hvl1 y o ho_u];exact hxy⟩
 obtain ⟨gs',o',hc',hl',he'⟩:=drop_dead m gs1 hcl1 o p (by simp [gs1];exact hplen) ho_p hno1 hnc1
 have hmin:=L.hmin gs' o' hc' (fun x=>by rw [he' x,hvl1 x o ho_u];exact L.hev x)
 simp only [gs1,List.length_set] at hl';omega
theorem n3 (n : ℕ) (C : Circuit) (hn : 5 ≤ n) (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=cyc n) : C.size=n + (n + 1) / 2 - 1:=by
 have hup:=(cycleTheorem n (n + (n + 1) / 2 - 1) hn).2 (by omega)
 obtain ⟨D,hDok,hDsz,hDev⟩:=hup
 have hDfun : circuitFun n D=circuitFun n C:=by funext x;rw [hfun];exact hDev x
 have hle : C.size ≤ n + (n + 1) / 2 - 1:=le_trans (hmin.2 D hDok hDfun) hDsz;have hge:=(cycleTheorem n C.size hn).1 ⟨C,hmin.1,le_refl _,fun x=>congrFun hfun x⟩;omega
theorem no_not_of_minimal_cyc (n : ℕ) (C : Circuit) (hn : 5 ≤ n) (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=cyc n) : ∀ g ∈ C.gates,g.op ≠ GateOp.not:=by
 by_contra hhas
 push Not at hhas;obtain ⟨g0,hg0,hop0⟩:=hhas;have hsz_eq : C.size=n + (n + 1) / 2 - 1:=n3 n C hn hmin hfun
 obtain ⟨m,rfl⟩ : ∃ m,n=m + 1:=⟨n - 1,by omega⟩
 have hm4 : 4 ≤ m:=by omega
 have hdep_all : ∀ p : Fin (m + 1),Dep (cyc (m + 1)) p:=fun p=>cyc_dep (m + 1) (by omega) p
 have hnc_all : RestrNC (cyc (m + 1)):=fun p _ b=>cyc_nonconst (m + 1) (by omega) p b
 have hnf_all : NoFunnel (cyc (m + 1)):=fun p q hpq _ _=>cyc_no_funnel (m + 1) hn p q hpq
 have hfnc : ∃ x y : Fin (m + 1) → Bool,cyc (m + 1) x ≠ cyc (m + 1) y :=
  dep_nc (hdep_all ⟨0,by omega⟩)
 obtain ⟨hcl,L,_,_⟩:=least_of_minimal (m + 1) (cyc (m + 1)) C hfnc hmin hfun
 set gs:=C.gates.map normGate with hgs_def
 have hgs_len : gs.length=m + 1 + (m + 2) / 2 - 1:=by
  rw [hgs_def,List.length_map];exact hsz_eq
 obtain ⟨u,hgu⟩ : ∃ u,gs[u]?=some (normGate g0) :=
  List.mem_iff_getElem?.1 (List.mem_map.2 ⟨g0,hg0,rfl⟩)
 have hu_op : (normGate g0).op=GateOp.not:=by simp [normGate,hop0]
 have contra_f4 : ∀ y : Fin (m + 1),Drop (cyc (m + 1)) y false 4 gs.length → False:=by
  intro y ⟨s',hs',hC'⟩
  have hlow:=cyc_false_lower m s' (restrict_last m (by omega) y false s' hC')
  omega
 have contra_f3n : ∀ y : Fin (m + 1), (∃ s',s' + 3 ≤ gs.length ∧ HasNotCircuitSize (m + 1) (fun x=>cyc (m + 1) (update x y false)) s') → False:=by
  intro y ⟨s',hs',hC'⟩
  have hlow:=cyc_false_lower_with_not m s' (by omega) (n2 m (by omega) y false s' hC')
  omega
 have contra_t5 : ∀ y : Fin (m + 1),Drop (cyc (m + 1)) y true 5 gs.length → False:=by
  intro y ⟨s',hs',hC'⟩
  have hlow:=cyc_true_lower m s' hm4 (restrict_last m (by omega) y true s' hC')
  omega
 have contra_t4n : ∀ y : Fin (m + 1), (∃ s',s' + 4 ≤ gs.length ∧ HasNotCircuitSize (m + 1) (fun x=>cyc (m + 1) (update x y true)) s') → False:=by
  intro y ⟨s',hs',hC'⟩
  have hlow:=cyc_true_lower_with_not m s' hm4 (n2 m (by omega) y true s' hC')
  omega
 by_cases hA : ∃ (y : Fin (m + 1)) (p q : ℕ),p ≠ q ∧ Reads gs p y ∧ Reads gs q y
 · obtain ⟨y,p,q,hpq,hp,hq⟩:=hA
   have hncy : ∀ b,∃ x x' : Fin (m + 1) → Bool, cyc (m + 1) (update x y b) ≠ cyc (m + 1) (update x' y b) :=
    fun b=>hnc_all y (hdep_all y) b
   obtain ⟨gp,hgp,hip⟩:=hp;obtain ⟨gq,hgq,hiq⟩:=hq;have hpR : Reads gs p y:=⟨gp,hgp,hip⟩;have hqR : Reads gs q y:=⟨gq,hgq,hiq⟩;have not_and_case : ∀ (p0 q0 : ℕ) (gp0 gq0 : Gate),p0 ≠ q0 →
    gs[p0]?=some gp0 → gs[q0]?=some gq0 →
    (y : ℕ) ∈ gp0.inputs → (y : ℕ) ∈ gq0.inputs →
    gp0.op=GateOp.not → False:=by
    intro p0 q0 gp0 gq0 hne0 hgp0 hgq0 hip0 hiq0 hnot0;have hp0R : Reads gs p0 y:=⟨gp0,hgp0,hip0⟩;have hq0R : Reads gs q0 y:=⟨gq0,hgq0,hiq0⟩;obtain ⟨ap0,_,hpin0⟩:=n7 (hcl p0 gp0 hgp0) hnot0;rw [hpin0] at hip0;simp at hip0;subst hip0
    have hip0' : y.val ∈ gp0.inputs:=by rw [hpin0];simp
    by_cases hqnot : gq0.op=GateOp.not
    · have hcp:=isC_reader hcl y p0 gp0 hgp0 hip0' false (Or.inl hnot0);have hcq:=isC_reader hcl y q0 gq0 hgq0 hiq0 false (Or.inl hqnot);exact contra_f4 y (L.fourth y false (hncy false) p0 q0 hne0 hp0R hq0R hcp hcq)
    · rcases hcl q0 gq0 hgq0 with ⟨hqn,_⟩ | ⟨hqand | hqor,w1,w2,hw1,hw2,hqin⟩
      · exact hqnot hqn
      · have hcp:=isC_reader hcl y p0 gp0 hgp0 hip0' false (Or.inl hnot0)
        have hcq : IsC m gs y false (m + 1 + q0) :=
         isC_reader hcl y q0 gq0 hgq0 hiq0 false (Or.inr (by simp [fixBit,hqand]))
        exact contra_f4 y (L.fourth y false (hncy false) p0 q0 hne0 hp0R hq0R hcp hcq)
      · have hst_p0_f : stF m gs y false (m + 1 + p0)=Sum.inl true :=
         ne hcl y false p0 gp0 hgp0 hnot0 y.val hip0' false (stF_self m gs y false)
        have hcp_f : IsC m gs y false (m + 1 + p0):=⟨true,hst_p0_f⟩;obtain ⟨J,hp0J,hJr,hJrc_f⟩:=L.next y false (hncy false) p0 (List.getElem?_eq_some_iff.1 hgp0).1 hcp_f
        have hJq0 : J ≠ q0:=by
         rintro rfl;exact L.no_tri hfnc p0 J y hp0R hq0R hJr
        obtain ⟨gJ,hgJ,hp0_in_J⟩:=hJr
        rcases hcl J gJ hgJ with ⟨hJn,aJ,_,hJin⟩ | ⟨hJand | hJor,aJ,bJ,haJ,hbJ,hJin⟩
        · rw [hJin] at hp0_in_J;simp at hp0_in_J;subst hp0_in_J
          exact L.no_alias hfnc J (List.getElem?_eq_some_iff.1 hgJ).1 y.val (by have:=y.2;omega)
           (fun x=>by rw [vl_not gs hcl x J gJ hgJ _ hJn hJin,vl_not gs hcl x p0 gp0 hgp0 _ hnot0 hpin0,Bool.not_not])
        · have hst_p0_t : stF m gs y true (m + 1 + p0)=Sum.inl false :=
           ne hcl y true p0 gp0 hgp0 hnot0 y.val hip0' true (stF_self m gs y true)
          have hIsCJ_t : IsC m gs y true (m + 1 + J) :=
           const_read m gs hcl y true J gJ hgJ (m + 1 + p0) hp0_in_J (by simpa [fixBit,hJand] using hst_p0_t)
          have hJrc_t : RC m gs y true J:=⟨gJ,hgJ,m + 1 + p0,hp0_in_J,false,hst_p0_t⟩
          have hIsCq_t : IsC m gs y true (m + 1 + q0) :=
           isC_reader hcl y q0 gq0 hgq0 hiq0 true (Or.inr (by simp [fixBit,hqor]))
          by_cases hexJ2 : ∃ J',J' ≠ q0 ∧ Reads gs J' (m + 1 + J)
          · obtain ⟨J',hJ'q0,hJ'r⟩:=hexJ2
            have hJJ' : J < J':=by have:=reads_lt hcl hJ'r;omega
            have hJ'rc_t : RC m gs y true J':=rc_of_reads hJ'r hIsCJ_t
            by_cases hex2 : ∃ q2,q2 ≠ J ∧ Reads gs q2 (m + 1 + q0)
            · obtain ⟨q2,hq2J,hq2r⟩:=hex2
              have hq2_gt : q0 < q2:=by have:=reads_lt hcl hq2r;omega
              have hq2p0 : q2 ≠ p0:=by
               rintro rfl;obtain ⟨g2,hg2,hin2⟩:=hq2r;have e:=gate_eq hg2 hgp0 rfl;subst g2;rw [hpin0] at hin2;simp at hin2;omega
              have hq2rc_t : RC m gs y true q2:=rc_of_reads hq2r hIsCq_t
              by_cases hq2J' : q2=J'
              · subst hq2J';obtain ⟨g2,hg2,hin_q0⟩:=hq2r;obtain ⟨g2',hg2',hin_J⟩:=hJ'r;have e:=gate_eq hg2' hg2 rfl;subst g2'
                have hIsC2 : IsC m gs y true (m + 1 + q2):=st_allconst m gs hcl y true q2 g2 hg2 (fun a ha=>by
                 rcases two_inputs (hcl q2 g2 hg2) (m + 1 + q0) (m + 1 + J) a hin_q0 hin_J (by omega) ha with rfl | rfl
                 · exact hIsCq_t
                 · exact hIsCJ_t)
                obtain ⟨K,hq2K,_,hKrc_t⟩:=L.next y true (hncy true) q2 (List.getElem?_eq_some_iff.1 hg2).1 hIsC2
                exact contra_t5 y (n10 L y true (hncy true) p0 q0 J q2 K hne0 (by omega) (by omega) (by omega) (Ne.symm hJq0) (by omega) (by omega) (by omega) (by omega) (by omega) (rc_input true hp0R) (rc_input true hq0R) hJrc_t hq2rc_t hKrc_t)
              · exact contra_t5 y (n10 L y true (hncy true) p0 q0 J J' q2 hne0 (by omega) (by omega) (Ne.symm hq2p0) (Ne.symm hJq0) (Ne.symm hJ'q0) (by omega) (by omega) (Ne.symm hq2J) (Ne.symm hq2J') (rc_input true hp0R) (rc_input true hq0R) hJrc_t hJ'rc_t hq2rc_t)
            · push Not at hex2
              have honly_q0 : ∀ k,Reads gs k (m + 1 + q0) → k=J:=fun k hk=>by
               by_contra hne;exact hex2 k hne hk
              have ho_q0 : C.output ≠ m + 1 + q0:=by
               intro e;obtain ⟨c,hc⟩:=hIsCq_t;rw [← e] at hc;obtain ⟨x,x',hxx'⟩:=hncy true;exact hxx' ((restr_const hcl L.hev y true c hc x).trans (restr_const hcl L.hev y true c hc x').symm)
              obtain ⟨q1,_,hq1r⟩:=L.live hfnc q0 (List.getElem?_eq_some_iff.1 hgq0).1 ho_q0
              have hq1J : q1=J:=honly_q0 q1 hq1r;subst q1;obtain ⟨gJ',hgJ',hq0_in_J⟩:=hq1r;have e:=gate_eq hgJ' hgJ rfl;subst gJ'
              have hJ_in' : gJ.inputs=[m + 1 + p0,m + 1 + q0] ∨ gJ.inputs=[m + 1 + q0,m + 1 + p0]:=by
               rw [hJin] at hp0_in_J hq0_in_J ⊢
               simp at hp0_in_J hq0_in_J
               rcases hp0_in_J with rfl | rfl <;> rcases hq0_in_J with h | h
               · omega
               · subst h;exact Or.inl rfl
               · subst h;exact Or.inr rfl
               · omega
              rw [hqin] at hiq0;simp at hiq0
              rcases hiq0 with rfl | rfl
              · exact n9 L hfnc y p0 q0 J hne0 gp0 gq0 gJ hgp0 hgq0 hgJ
                 hnot0 hpin0 hqor w2 hw2 (Or.inl hqin) hJand hJ_in' ho_q0 honly_q0
              · exact n9 L hfnc y p0 q0 J hne0 gp0 gq0 gJ hgp0 hgq0 hgJ
                 hnot0 hpin0 hqor w1 hw1 (Or.inr hqin) hJand hJ_in' ho_q0 honly_q0
          · push Not at hexJ2
            have honly_J : ∀ k,Reads gs k (m + 1 + J) → k=q0:=fun k hk=>by
             by_contra hne;exact hexJ2 k hne hk
            have ho_J : C.output ≠ m + 1 + J:=by
             intro e;obtain ⟨c,hc⟩:=hIsCJ_t;rw [← e] at hc;obtain ⟨x,x',hxx'⟩:=hncy true;exact hxx' ((restr_const hcl L.hev y true c hc x).trans (restr_const hcl L.hev y true c hc x').symm)
            obtain ⟨J1,_,hJ1r⟩:=L.live hfnc J (List.getElem?_eq_some_iff.1 hgJ).1 ho_J
            have hJ1q0 : J1=q0:=honly_J J1 hJ1r;subst J1;obtain ⟨gq',hgq',hJ_in_q0⟩:=hJ1r;have e:=gate_eq hgq' hgq0 rfl;subst gq'
            have hq_in' : gq0.inputs=[y.val,m + 1 + J] ∨ gq0.inputs=[m + 1 + J,y.val]:=by
             rw [hqin] at hiq0 hJ_in_q0 ⊢
             simp at hiq0 hJ_in_q0
             rcases hiq0 with rfl | rfl <;> rcases hJ_in_q0 with h | h
             · have:=y.2;omega
             · subst h;exact Or.inl rfl
             · subst h;exact Or.inr rfl
             · have:=y.2;omega
            rw [hJin] at hp0_in_J;simp at hp0_in_J
            rcases hp0_in_J with rfl | rfl
            · exact na L hfnc y p0 J q0 gp0 gJ gq0 hgp0 hgJ hgq0
               hnot0 hpin0 hJand bJ hbJ (Or.inl hJin) hqor hq_in' ho_J honly_J
            · exact na L hfnc y p0 J q0 gp0 gJ gq0 hgp0 hgJ hgq0
               hnot0 hpin0 hJand aJ haJ (Or.inr hJin) hqor hq_in' ho_J honly_J
        · have hIsCJ_f : IsC m gs y false (m + 1 + J) :=
           const_read m gs hcl y false J gJ hgJ (m + 1 + p0) hp0_in_J (by simpa [fixBit,hJor] using hst_p0_f)
          obtain ⟨K,hJK,hKr,hKrc_f⟩:=L.next y false (hncy false) J (List.getElem?_eq_some_iff.1 hgJ).1 hIsCJ_f
          by_cases hKq0 : K=q0
          · subst hKq0;obtain ⟨gK,hgK,hJ_in_q0⟩:=hKr;have e:=gate_eq hgK hgq0 rfl;subst gK
            have hIsCq_f : IsC m gs y false (m + 1 + K):=st_allconst m gs hcl y false K gq0 hgq0 (fun a ha=>by
             rcases two_inputs (hcl K gq0 hgq0) y.val (m + 1 + J) a hiq0 hJ_in_q0 (by have:=y.2;omega) ha with rfl | rfl
             · exact ⟨false,stF_self m gs y false⟩
             · exact hIsCJ_f)
            obtain ⟨K2,hKK2,_,hK2rc_f⟩:=L.next y false (hncy false) K (List.getElem?_eq_some_iff.1 hgq0).1 hIsCq_f
            exact contra_f4 y (L.save4 y false (hncy false) p0 K J K2 hne0 (by omega) (by omega) (Ne.symm hJq0) (by omega) (by omega) (rc_input false hp0R) (rc_input false hq0R) hJrc_f hK2rc_f)
          · exact contra_f4 y (L.save4 y false (hncy false) p0 q0 J K hne0 (by omega) (by omega) (Ne.symm hJq0) (Ne.symm hKq0) (by omega) (rc_input false hp0R) (rc_input false hq0R) hJrc_f hKrc_f)
   by_cases hpn : gp.op=GateOp.not
   · exact not_and_case p q gp gq hpq hgp hgq hip hiq hpn
   by_cases hqn : gq.op=GateOp.not
   · exact not_and_case q p gq gp (Ne.symm hpq) hgq hgp hiq hip hqn
   rcases hcl p gp hgp with ⟨h1,_⟩ | ⟨hpand | hpor,wp1,wp2,hwp1,hwp2,hpin⟩
   · exact hpn h1
   · rcases hcl q gq hgq with ⟨h2,_⟩ | ⟨hqand | hqor,wq1,wq2,hwq1,hwq2,hqin⟩
     · exact hqn h2
     · have hcp : IsC m gs y false (m + 1 + p):=isC_reader hcl y p gp hgp hip false (Or.inr (by simp [fixBit,hpand]))
       have hcq : IsC m gs y false (m + 1 + q):=isC_reader hcl y q gq hgq hiq false (Or.inr (by simp [fixBit,hqand]))
       exact contra_f4 y (L.fourth y false (hncy false) p q hpq hpR hqR hcp hcq)
     · have hcp : IsC m gs y false (m + 1 + p):=isC_reader hcl y p gp hgp hip false (Or.inr (by simp [fixBit,hpand]))
       obtain ⟨J,hpJ,hJr,hJrc⟩:=L.next y false (hncy false) p (List.getElem?_eq_some_iff.1 hgp).1 hcp
       have hJq : J ≠ q:=by
        rintro rfl;exact L.no_tri hfnc p J y hpR hqR hJr
       by_cases hurc : RC m gs y false u
       · have hup : u ≠ p:=by rintro rfl;exact hpn (by rw [gate_eq hgp hgu rfl];exact hu_op)
         have huq : u ≠ q:=by rintro rfl;exact hqn (by rw [gate_eq hgq hgu rfl];exact hu_op)
         by_cases huJ : u=J
         · subst huJ;have hIsCu : IsC m gs y false (m + 1 + u):=nb hcl y false u _ hgu hu_op hurc;obtain ⟨K,huK,hKr,hKrc⟩:=L.next y false (hncy false) u (List.getElem?_eq_some_iff.1 hgu).1 hIsCu
           by_cases hKq : K=q
           · subst hKq;obtain ⟨gK,hgK,hu_in_q⟩:=hKr;have e:=gate_eq hgK hgq rfl;subst gK
             have hIsCq : IsC m gs y false (m + 1 + K):=st_allconst m gs hcl y false K gq hgq (fun a ha=>by
              rcases two_inputs (hcl K gq hgq) y.val (m + 1 + u) a hiq hu_in_q (by have:=y.2;omega) ha with rfl | rfl
              · exact ⟨false,stF_self m gs y false⟩
              · exact hIsCu)
             obtain ⟨K2,hKK2,_,hK2rc⟩:=L.next y false (hncy false) K (List.getElem?_eq_some_iff.1 hgq).1 hIsCq
             exact contra_f4 y (L.save4 y false (hncy false) p K u K2 hpq (by omega) (by omega) (Ne.symm hJq) (by omega) (by omega) (rc_input false hpR) (rc_input false hqR) hurc hK2rc)
           · exact contra_f4 y (L.save4 y false (hncy false) p q u K hpq (by omega) (by omega) (Ne.symm hJq) (Ne.symm hKq) (by omega) (rc_input false hpR) (rc_input false hqR) hurc hKrc)
         · exact contra_f4 y (L.save4 y false (hncy false) p q J u hpq (by omega) (Ne.symm hup) (Ne.symm hJq) (Ne.symm huq) (Ne.symm huJ) (rc_input false hpR) (rc_input false hqR) hJrc hurc)
       · have hnot3:=nf L y false (hncy false) {p,q,J} (by
          intro x hx;simp only [Finset.mem_insert,Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact rc_input false hpR
          · exact rc_input false hqR
          · exact hJrc) u _ hgu hu_op hurc
         rw [Finset.card_eq_three.2 ⟨p,q,J,hpq,by omega,Ne.symm hJq,rfl⟩] at hnot3
         exact contra_f3n y hnot3
   · rcases hcl q gq hgq with ⟨h2,_⟩ | ⟨hqand | hqor,wq1,wq2,hwq1,hwq2,hqin⟩
     · exact hqn h2
     · have hcq : IsC m gs y false (m + 1 + q):=isC_reader hcl y q gq hgq hiq false (Or.inr (by simp [fixBit,hqand]))
       obtain ⟨J,hqJ,hJr,hJrc⟩:=L.next y false (hncy false) q (List.getElem?_eq_some_iff.1 hgq).1 hcq
       have hJp : J ≠ p:=by
        rintro rfl;exact L.no_tri hfnc q J y hqR hpR hJr
       by_cases hurc : RC m gs y false u
       · have hup : u ≠ p:=by rintro rfl;exact hpn (by rw [gate_eq hgp hgu rfl];exact hu_op)
         have huq : u ≠ q:=by rintro rfl;exact hqn (by rw [gate_eq hgq hgu rfl];exact hu_op)
         by_cases huJ : u=J
         · subst huJ;have hIsCu : IsC m gs y false (m + 1 + u):=nb hcl y false u _ hgu hu_op hurc;obtain ⟨K,huK,hKr,hKrc⟩:=L.next y false (hncy false) u (List.getElem?_eq_some_iff.1 hgu).1 hIsCu
           by_cases hKp : K=p
           · subst hKp;obtain ⟨gK,hgK,hu_in_p⟩:=hKr;have e:=gate_eq hgK hgp rfl;subst gK
             have hIsCp : IsC m gs y false (m + 1 + K):=st_allconst m gs hcl y false K gp hgp (fun a ha=>by
              rcases two_inputs (hcl K gp hgp) y.val (m + 1 + u) a hip hu_in_p (by have:=y.2;omega) ha with rfl | rfl
              · exact ⟨false,stF_self m gs y false⟩
              · exact hIsCu)
             obtain ⟨K2,hKK2,_,hK2rc⟩:=L.next y false (hncy false) K (List.getElem?_eq_some_iff.1 hgp).1 hIsCp
             exact contra_f4 y (L.save4 y false (hncy false) q K u K2 (Ne.symm hpq) (by omega) (by omega) (Ne.symm hJp) (by omega) (by omega) (rc_input false hqR) (rc_input false hpR) hurc hK2rc)
           · exact contra_f4 y (L.save4 y false (hncy false) q p u K (Ne.symm hpq) (by omega) (by omega) (Ne.symm hJp) (Ne.symm hKp) (by omega) (rc_input false hqR) (rc_input false hpR) hurc hKrc)
         · exact contra_f4 y (L.save4 y false (hncy false) q p J u (Ne.symm hpq) (by omega) (Ne.symm huq) (Ne.symm hJp) (Ne.symm hup) (Ne.symm huJ) (rc_input false hqR) (rc_input false hpR) hJrc hurc)
       · have hnot3:=nf L y false (hncy false) {q,p,J} (by
          intro x hx;simp only [Finset.mem_insert,Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact rc_input false hqR
          · exact rc_input false hpR
          · exact hJrc) u _ hgu hu_op hurc
         rw [Finset.card_eq_three.2 ⟨q,p,J,Ne.symm hpq,by omega,Ne.symm hJp,rfl⟩] at hnot3
         exact contra_f3n y hnot3
     · have hcp : IsC m gs y true (m + 1 + p):=isC_reader hcl y p gp hgp hip true (Or.inr (by simp [fixBit,hpor]))
       have hcq : IsC m gs y true (m + 1 + q):=isC_reader hcl y q gq hgq hiq true (Or.inr (by simp [fixBit,hqor]))
       obtain ⟨J1,h1p,h1r,h1rc⟩:=L.next y true (hncy true) p (List.getElem?_eq_some_iff.1 hgp).1 hcp
       obtain ⟨J2,h2q,h2r,h2rc⟩:=L.next y true (hncy true) q (List.getElem?_eq_some_iff.1 hgq).1 hcq
       have h1q : J1 ≠ q:=by rintro rfl;exact L.no_tri hfnc p J1 y hpR hqR h1r
       have h2p : J2 ≠ p:=by rintro rfl;exact L.no_tri hfnc q J2 y hqR hpR h2r
       have hup : u ≠ p:=by rintro rfl;exact hpn (by rw [gate_eq hgp hgu rfl];exact hu_op)
       have huq : u ≠ q:=by rintro rfl;exact hqn (by rw [gate_eq hgq hgu rfl];exact hu_op)
       by_cases h12 : J1=J2
       · have h2r' : Reads gs J1 (m + 1 + q):=by rw [h12];exact h2r
         have h2q' : q < J1:=by rw [h12];exact h2q
         obtain ⟨gJ,hgJ,hinp⟩:=h1r;obtain ⟨gJ',hgJ',hinq⟩:=h2r';have e:=gate_eq hgJ' hgJ rfl;subst gJ'
         have hcJ : IsC m gs y true (m + 1 + J1):=st_allconst m gs hcl y true J1 gJ hgJ (fun a ha=>by
          rcases two_inputs (hcl J1 gJ hgJ) (m + 1 + p) (m + 1 + q) a hinp hinq (by omega) ha with rfl | rfl
          · exact hcp
          · exact hcq)
         obtain ⟨K,hKJ,_,hKrc⟩:=L.next y true (hncy true) J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
         have huJ1 : u ≠ J1:=by
          rintro rfl
          rcases hcl u gJ hgJ with ⟨_,a,_,hin⟩ | ⟨hbin,_⟩
          · rw [hin] at hinp hinq;simp at hinp hinq;omega
          · have e2:=gate_eq hgJ hgu rfl
            rcases hbin with h1 | h1 <;> rw [e2,hu_op] at h1 <;> cases h1
         by_cases hurc : RC m gs y true u
         · by_cases huK : u=K
           · subst huK;have hIsCu : IsC m gs y true (m + 1 + u):=nb hcl y true u _ hgu hu_op hurc;obtain ⟨K2,huK2,_,hK2rc⟩:=L.next y true (hncy true) u (List.getElem?_eq_some_iff.1 hgu).1 hIsCu
             exact contra_t5 y (n10 L y true (hncy true) p q J1 u K2 hpq (by omega) (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega) (by omega) (by omega) (by omega) (rc_input true hpR) (rc_input true hqR) h1rc hurc hK2rc)
           · exact contra_t5 y (n10 L y true (hncy true) p q J1 K u hpq (by omega) (by omega) (Ne.symm hup) (Ne.symm h1q) (by omega) (Ne.symm huq) (by omega) (Ne.symm huJ1) (Ne.symm huK) (rc_input true hpR) (rc_input true hqR) h1rc hKrc hurc)
         · have hnot4:=nf L y true (hncy true) {p,q,J1,K} (by
            intro x hx;simp only [Finset.mem_insert,Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact rc_input true hpR
            · exact rc_input true hqR
            · exact h1rc
            · exact hKrc) u _ hgu hu_op hurc
           have hcard4 : ({p,q,J1,K} : Finset ℕ).card=4:=by
            rw [Finset.card_insert_of_notMem (by simp [hpq,show p ≠ J1 by omega,show p ≠ K by omega]),
             Finset.card_eq_three.2 ⟨q,J1,K,Ne.symm h1q,by omega,by omega,rfl⟩]
           rw [hcard4] at hnot4;exact contra_t4n y hnot4
       · by_cases hurc : RC m gs y true u
         · have or_not_case : ∀ (p0 q0 J0 K0 : ℕ) (gp0 gq0 : Gate), p0 ≠ q0 → J0 ≠ K0 → p0 < J0 → q0 < K0 → J0 ≠ q0 → K0 ≠ p0 → gs[p0]?=some gp0 → gs[q0]?=some gq0 → (y : ℕ) ∈ gp0.inputs → (y : ℕ) ∈ gq0.inputs → gp0.op=GateOp.or → gq0.op=GateOp.or → IsC m gs y true (m + 1 + p0) → IsC m gs y true (m + 1 + q0) → Reads gs J0 (m + 1 + p0) → Reads gs K0 (m + 1 + q0) → RC m gs y true J0 → RC m gs y true K0 → J0=u → False:=by
            intro p0 q0 J0 K0 gp0 gq0 hne0 hJK0 hpJ0 hqK0 hJq0 hKp0 hgp0 hgq0 hip0 hiq0 hpor0 hqor0 hcp0 hcq0 hJr0 hKr0 hJrc0 hKrc0 hJ0u;subst J0;have hp0R : Reads gs p0 y:=⟨gp0,hgp0,hip0⟩;have hq0R : Reads gs q0 y:=⟨gq0,hgq0,hiq0⟩;have hIsCu : IsC m gs y true (m + 1 + u):=nb hcl y true u _ hgu hu_op hurc
            by_cases hex_u2 : ∃ u2,u2 ≠ q0 ∧ Reads gs u2 (m + 1 + u)
            · obtain ⟨u2,hu2q0,hu2r⟩:=hex_u2
              have hu2_gt : u < u2:=by have:=reads_lt hcl hu2r;omega
              have hu2rc : RC m gs y true u2:=rc_of_reads hu2r hIsCu
              by_cases hu2K0 : u2=K0
              · subst hu2K0;obtain ⟨g2,hg2,h_in_u⟩:=hu2r;obtain ⟨g2',hg2',h_in_q⟩:=hKr0;have e:=gate_eq hg2' hg2 rfl;subst g2'
                have hIsC2 : IsC m gs y true (m + 1 + u2):=st_allconst m gs hcl y true u2 g2 hg2 (fun a ha=>by
                 rcases two_inputs (hcl u2 g2 hg2) (m + 1 + u) (m + 1 + q0) a h_in_u h_in_q (by omega) ha with rfl | rfl
                 · exact hIsCu
                 · exact hcq0)
                obtain ⟨M,hu2M,_,hMrc⟩:=L.next y true (hncy true) u2 (List.getElem?_eq_some_iff.1 hg2).1 hIsC2
                exact contra_t5 y (n10 L y true (hncy true) p0 q0 u u2 M hne0 (by omega) (by omega) (by omega) (Ne.symm hJq0) (by omega) (by omega) (by omega) (by omega) (by omega) (rc_input true hp0R) (rc_input true hq0R) hurc hu2rc hMrc)
              · exact contra_t5 y (n10 L y true (hncy true) p0 q0 u K0 u2 hne0 (by omega) (Ne.symm hKp0) (by omega) (Ne.symm hJq0) (by omega) (Ne.symm hu2q0) hJK0 (by omega) (Ne.symm hu2K0) (rc_input true hp0R) (rc_input true hq0R) hurc hKrc0 hu2rc)
            · push Not at hex_u2
              have honly_u : ∀ k,Reads gs k (m + 1 + u) → k=q0:=fun k hk=>by
               by_contra hne;exact hex_u2 k hne hk
              have ho_u : C.output ≠ m + 1 + u:=by
               intro e;obtain ⟨c,hc⟩:=hIsCu;rw [← e] at hc;obtain ⟨x,x',hxx'⟩:=hncy true;exact hxx' ((restr_const hcl L.hev y true c hc x).trans (restr_const hcl L.hev y true c hc x').symm)
              obtain ⟨u1,_,hu1r⟩:=L.live hfnc u (List.getElem?_eq_some_iff.1 hgu).1 ho_u
              have hu1q0 : u1=q0:=honly_u u1 hu1r;have huq0r : Reads gs q0 (m + 1 + u):=hu1q0 ▸ hu1r
              by_cases hex_p2 : ∃ p2,p2 ≠ u ∧ Reads gs p2 (m + 1 + p0)
              · obtain ⟨p2,hp2u,hp2r⟩:=hex_p2
                have hp2_gt : p0 < p2:=by have:=reads_lt hcl hp2r;omega
                have hp2q0 : p2 ≠ q0:=by rintro rfl;exact L.no_tri hfnc p0 p2 y hp0R hq0R hp2r
                have hp2rc : RC m gs y true p2:=rc_of_reads hp2r hcp0
                by_cases hp2K0 : p2=K0
                · subst hp2K0;obtain ⟨g2,hg2,h_in_p⟩:=hp2r;obtain ⟨g2',hg2',h_in_q⟩:=hKr0;have e:=gate_eq hg2' hg2 rfl;subst g2'
                  have hIsC2 : IsC m gs y true (m + 1 + p2):=st_allconst m gs hcl y true p2 g2 hg2 (fun a ha=>by
                   rcases two_inputs (hcl p2 g2 hg2) (m + 1 + p0) (m + 1 + q0) a h_in_p h_in_q (by omega) ha with rfl | rfl
                   · exact hcp0
                   · exact hcq0)
                  obtain ⟨M,hp2M,_,hMrc⟩:=L.next y true (hncy true) p2 (List.getElem?_eq_some_iff.1 hg2).1 hIsC2
                  exact contra_t5 y (n10 L y true (hncy true) p0 q0 u p2 M hne0 (by omega) (by omega) (by omega) (Ne.symm hJq0) (by omega) (by omega) (Ne.symm hp2u) (by omega) (by omega) (rc_input true hp0R) (rc_input true hq0R) hurc hp2rc hMrc)
                · exact contra_t5 y (n10 L y true (hncy true) p0 q0 u K0 p2 hne0 (by omega) (Ne.symm hKp0) (by omega) (Ne.symm hJq0) (by omega) (Ne.symm hp2q0) hJK0 (Ne.symm hp2u) (Ne.symm hp2K0) (rc_input true hp0R) (rc_input true hq0R) hurc hKrc0 hp2rc)
              · push Not at hex_p2
                have honly_p : ∀ k,Reads gs k (m + 1 + p0) → k=u:=fun k hk=>by
                 by_contra hne;exact hex_p2 k hne hk
                have ho_p0 : C.output ≠ m + 1 + p0:=by
                 intro e;obtain ⟨c,hc⟩:=hcp0;rw [← e] at hc;obtain ⟨x,x',hxx'⟩:=hncy true;exact hxx' ((restr_const hcl L.hev y true c hc x).trans (restr_const hcl L.hev y true c hc x').symm)
                rcases hcl p0 gp0 hgp0 with ⟨h1,_⟩ | ⟨_,wp01,wp02,hwp01,hwp02,hpin0⟩
                · rw [hpor0] at h1;cases h1
                obtain ⟨au,_,huin⟩:=n7 (hcl u _ hgu) hu_op;obtain ⟨gu',hgu',hp0_in_u⟩:=hJr0;have eu:=gate_eq hgu' hgu rfl;subst gu';rw [huin] at hp0_in_u;simp at hp0_in_u;subst hp0_in_u;obtain ⟨gq',hgq',hu_in_q⟩:=huq0r;have eq':=gate_eq hgq' hgq0 rfl;subst gq'
                rcases hcl q0 gq0 hgq0 with ⟨h1,_⟩ | ⟨_,wq01,wq02,_,_,hqin0⟩
                · rw [hqor0] at h1;cases h1
                have hqin' : gq0.inputs=[y.val,m + 1 + u] ∨ gq0.inputs=[m + 1 + u,y.val]:=by
                 rw [hqin0] at hiq0 hu_in_q ⊢
                 simp at hiq0 hu_in_q
                 rcases hiq0 with rfl | rfl <;> rcases hu_in_q with h | h
                 · have:=y.2;omega
                 · subst h;exact Or.inl rfl
                 · subst h;exact Or.inr rfl
                 · have:=y.2;omega
                rw [hpin0] at hip0;simp at hip0
                rcases hip0 with rfl | rfl
                · exact nd L hfnc y p0 u q0 gp0 _ gq0 hgp0 hgu hgq0 hpor0 wp02 hwp02
                   (Or.inl hpin0) hu_op huin hqor0 hqin' ho_p0 honly_p ho_u honly_u
                · exact nd L hfnc y p0 u q0 gp0 _ gq0 hgp0 hgu hgq0 hpor0 wp01 hwp01
                   (Or.inr hpin0) hu_op huin hqor0 hqin' ho_p0 honly_p ho_u honly_u
           by_cases huJ1 : u=J1
           · exact or_not_case p q J1 J2 gp gq hpq h12 h1p h2q h1q h2p hgp hgq hip hiq hpor hqor hcp hcq h1r h2r h1rc h2rc huJ1.symm
           by_cases huJ2 : u=J2
           · exact or_not_case q p J2 J1 gq gp (Ne.symm hpq) (Ne.symm h12) h2q h1p h2p h1q hgq hgp hiq hip hqor hpor hcq hcp h2r h1r h2rc h1rc huJ2.symm
           exact contra_t5 y (n10 L y true (hncy true) p q J1 J2 u hpq (by omega) (Ne.symm h2p) (Ne.symm hup) (Ne.symm h1q) (by omega) (Ne.symm huq) h12 (Ne.symm huJ1) (Ne.symm huJ2) (rc_input true hpR) (rc_input true hqR) h1rc h2rc hurc)
         · have hnot4:=nf L y true (hncy true) {p,q,J1,J2} (by
            intro x hx;simp only [Finset.mem_insert,Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact rc_input true hpR
            · exact rc_input true hqR
            · exact h1rc
            · exact h2rc) u _ hgu hu_op hurc
           have hcard4 : ({p,q,J1,J2} : Finset ℕ).card=4:=by
            rw [Finset.card_insert_of_notMem (by simp [hpq,show p ≠ J1 by omega,Ne.symm h2p]),
             Finset.card_eq_three.2 ⟨q,J1,J2,Ne.symm h1q,by omega,h12,rfl⟩]
           rw [hcard4] at hnot4;exact contra_t4n y hnot4
 · by_cases hB : ∃ (y : Fin (m + 1)) (r : ℕ) (g : Gate),gs[r]?=some g ∧ g.op=GateOp.not ∧
    (y : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ,p ≠ q ∧ Reads gs p (m + 1 + r) ∧ Reads gs q (m + 1 + r)
   · obtain ⟨y,r,gr,hgr,hrn,hir,p,q,hpq,hpR0,hqR0⟩:=hB
     have hncy : ∀ b,∃ x x' : Fin (m + 1) → Bool, cyc (m + 1) (update x y b) ≠ cyc (m + 1) (update x' y b) :=
      fun b=>hnc_all y (hdep_all y) b
     have hrR : Reads gs r y:=⟨gr,hgr,hir⟩;obtain ⟨gp,hgp,hrp⟩:=hpR0;obtain ⟨gq,hgq,hrq⟩:=hqR0;have hpR : Reads gs p (m + 1 + r):=⟨gp,hgp,hrp⟩;have hqR : Reads gs q (m + 1 + r):=⟨gq,hgq,hrq⟩
     have hp_gt : r < p:=by have:=reads_lt hcl hpR;omega
     have hq_gt : r < q:=by have:=reads_lt hcl hqR;omega
     have hst_r_f : stF m gs y false (m + 1 + r)=Sum.inl true :=
      ne hcl y false r gr hgr hrn y.val hir false (stF_self m gs y false)
     have hst_r_t : stF m gs y true (m + 1 + r)=Sum.inl false :=
      ne hcl y true r gr hgr hrn y.val hir true (stF_self m gs y true)
     have hnot_not : ∀ (p0 : ℕ) (gp0 : Gate),gs[p0]?=some gp0 → (m + 1 + r) ∈ gp0.inputs → gp0.op ≠ GateOp.not:=by
      intro p0 gp0 hgp0 hrp0 hpn0;obtain ⟨ar,_,hrin⟩:=n7 (hcl r gr hgr) hrn;obtain ⟨ap0,_,hpin0⟩:=n7 (hcl p0 gp0 hgp0) hpn0;rw [hrin] at hir;simp at hir;subst hir;rw [hpin0] at hrp0;simp at hrp0;subst hrp0
      exact L.no_alias hfnc p0 (List.getElem?_eq_some_iff.1 hgp0).1 y.val (by have:=y.2;omega)
       (fun x=>by rw [vl_not gs hcl x p0 gp0 hgp0 _ hpn0 hpin0,vl_not gs hcl x r gr hgr _ hrn hrin,Bool.not_not])
     have hor_case : ∀ (p0 q0 : ℕ) (gp0 gq0 : Gate),p0 ≠ q0 → r < p0 → r < q0 → gs[p0]?=some gp0 → gs[q0]?=some gq0 → (m + 1 + r) ∈ gp0.inputs → (m + 1 + r) ∈ gq0.inputs → gp0.op=GateOp.or → False:=by
      intro p0 q0 gp0 gq0 hne0 hrp0 hrq0 hgp0 hgq0 hrp_in hrq_in hpor0;have hp0R : Reads gs p0 (m + 1 + r):=⟨gp0,hgp0,hrp_in⟩;have hq0R : Reads gs q0 (m + 1 + r):=⟨gq0,hgq0,hrq_in⟩
      have hcp0 : IsC m gs y false (m + 1 + p0) :=
       const_read m gs hcl y false p0 gp0 hgp0 (m + 1 + r) hrp_in (by simpa [fixBit,hpor0] using hst_r_f)
      obtain ⟨J,hp0J,hJr,hJrc⟩:=L.next y false (hncy false) p0 (List.getElem?_eq_some_iff.1 hgp0).1 hcp0
      have hJq0 : J ≠ q0:=by rintro rfl;exact L.no_tri hfnc p0 J (m + 1 + r) hp0R hq0R hJr
      exact contra_f4 y (L.save4 y false (hncy false) r p0 q0 J (by omega) (by omega) (by omega) hne0 (by omega) (Ne.symm hJq0) (rc_input false hrR) (rc_of_reads hp0R ⟨true,hst_r_f⟩) (rc_of_reads hq0R ⟨true,hst_r_f⟩) hJrc)
     rcases hcl p gp hgp with ⟨h1,_⟩ | ⟨hpand | hpor,_⟩
     · exact hnot_not p gp hgp hrp h1
     · rcases hcl q gq hgq with ⟨h2,_⟩ | ⟨hqand | hqor,_⟩
       · exact hnot_not q gq hgq hrq h2
       · have hcp : IsC m gs y true (m + 1 + p) :=
          const_read m gs hcl y true p gp hgp (m + 1 + r) hrp (by simpa [fixBit,hpand] using hst_r_t)
         have hcq : IsC m gs y true (m + 1 + q) :=
          const_read m gs hcl y true q gq hgq (m + 1 + r) hrq (by simpa [fixBit,hqand] using hst_r_t)
         obtain ⟨J1,h1p,h1r,h1rc⟩:=L.next y true (hncy true) p (List.getElem?_eq_some_iff.1 hgp).1 hcp
         obtain ⟨J2,h2q,h2r,h2rc⟩:=L.next y true (hncy true) q (List.getElem?_eq_some_iff.1 hgq).1 hcq
         have h1q : J1 ≠ q:=by rintro rfl;exact L.no_tri hfnc p J1 (m + 1 + r) hpR hqR h1r
         have h2p : J2 ≠ p:=by rintro rfl;exact L.no_tri hfnc q J2 (m + 1 + r) hqR hpR h2r
         by_cases h12 : J1=J2
         · have h2r' : Reads gs J1 (m + 1 + q):=by rw [h12];exact h2r
           have h2q' : q < J1:=by rw [h12];exact h2q
           obtain ⟨gJ,hgJ,hinp⟩:=h1r;obtain ⟨gJ',hgJ',hinq⟩:=h2r';have e:=gate_eq hgJ' hgJ rfl;subst gJ'
           have hcJ : IsC m gs y true (m + 1 + J1):=st_allconst m gs hcl y true J1 gJ hgJ (fun a ha=>by
            rcases two_inputs (hcl J1 gJ hgJ) (m + 1 + p) (m + 1 + q) a hinp hinq (by omega) ha with rfl | rfl
            · exact hcp
            · exact hcq)
           obtain ⟨K,hKJ,_,hKrc⟩:=L.next y true (hncy true) J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
           exact contra_t5 y (n10 L y true (hncy true) r p q J1 K (by omega) (by omega) (by omega) (by omega) hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega) (rc_input true hrR) (rc_of_reads hpR ⟨false,hst_r_t⟩) (rc_of_reads hqR ⟨false,hst_r_t⟩) h1rc hKrc)
         · exact contra_t5 y (n10 L y true (hncy true) r p q J1 J2 (by omega) (by omega) (by omega) (by omega) hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12 (rc_input true hrR) (rc_of_reads hpR ⟨false,hst_r_t⟩) (rc_of_reads hqR ⟨false,hst_r_t⟩) h1rc h2rc)
       · exact hor_case q p gq gp (Ne.symm hpq) hq_gt hp_gt hgq hgp hrq hrp hqor
     · exact hor_case p q gp gq hpq hp_gt hq_gt hgp hgq hrp hrq hpor
   · obtain ⟨p,q,hpq,hdp,hdq,hfun_pq⟩:=L.funnel ⟨⟨0,by omega⟩,hdep_all ⟨0,by omega⟩⟩ hnc_all
      (fun i p q hp hq=>by by_contra hne;exact hA ⟨i,p,q,hne,hp,hq⟩)
      (fun i r g hr hop hin p q hp hq=>by by_contra hne;exact hB ⟨i,r,g,hr,hop,hin,p,q,hne,hp,hq⟩)
     exact hnf_all p q hpq hdp hdq hfun_pq
theorem minimal_clean_cyc (n : ℕ) (C : Circuit) (hn : 5 ≤ n) (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=cyc n) : (∀ g ∈ C.gates,g.op ≠ GateOp.not) ∧ CleanL n C.gates ∧ Least n (cyc n) C.gates C.output ∧ C.size=n + (n + 1) / 2 - 1 ∧ n ≤ C.output ∧ C.output < n + C.size ∧ (∀ t < C.size,∀ g,C.gates[t]?=some g → (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ ∃ a b,a < n + t ∧ b < n + t ∧ a ≠ b ∧ g.inputs=[a,b]):=by
 have hnonot:=no_not_of_minimal_cyc n C hn hmin hfun;have hsz:=n3 n C hn hmin hfun
 have hmap_id : C.gates.map normGate=C.gates:=by
  have h1 : ∀ gs : List Gate,(∀ g ∈ gs,g.op ≠ GateOp.not) → gs.map normGate=gs:=by
   intro gs hgs
   induction gs with
   | nil=>rfl
   | cons g gs ih =>
    rw [List.map_cons,ih (fun g' hg'=>hgs g' (List.mem_cons_of_mem _ hg'))];have hne:=hgs g List.mem_cons_self
    have hg : normGate g=g:=by
     unfold normGate
     cases hop : g.op <;> simp_all
    rw [hg]
  exact h1 C.gates hnonot
 have hfnc : ∃ x y : Fin n → Bool,cyc n x ≠ cyc n y:=dep_nc (cyc_dep n (by omega) ⟨0,by omega⟩)
 obtain ⟨hcl,L,hout_lt,_⟩:=least_of_minimal n (cyc n) C hfnc hmin hfun;rw [hmap_id] at hcl L
 have hout_ge : n ≤ C.output:=by
  by_contra hlt
  push Not at hlt;let v : Fin n:=⟨C.output,hlt⟩
  obtain ⟨x,y,hxy⟩:=cyc_nonconst n (by omega) v false
  apply hxy;have hx:=L.hev (update x v false);have hy:=L.hev (update y v false);rw [← hx,← hy,vl_input C.gates _ C.output hlt,vl_input C.gates _ C.output hlt];simp [v]
 refine ⟨hnonot,hcl,L,hsz,hout_ge,hout_lt,?_⟩
 intro t ht g hg
 rcases hcl t g hg with ⟨hnot,_⟩ | ⟨hop,a,b,ha,hb,hin⟩
 · exact absurd hnot (hnonot g (List.mem_of_getElem? hg))
 · refine ⟨hop,a,b,ha,hb,?_,hin⟩
   intro hab;subst hab;apply L.no_alias hfnc t ht a ha;intro x;rw [vl_gate C.gates hcl x t g hg,hin]
   rcases hop with h1 | h1 <;> rw [h1] <;> simp [GateOp.eval]
end PEqualNP.Outside.L_meta_314_aux.NoNot


namespace PEqualNP.Outside.L_meta_314_aux.WrapOut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_314_aux PEqualNP.Outside.L_meta_314_aux.NoNot

theorem vl_agree_prefix {n : ℕ} (gs gs' : List Gate) (hcl : CleanL n gs) (hcl' : CleanL n gs')
    (k : ℕ) (hpre : ∀ r, r < k → gs'[r]? = gs[r]?) :
    ∀ w, w < n + k → ∀ x : Fin n → Bool, vl gs' x w = vl gs x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw x
    by_cases hwn : w < n
    · rw [vl_input gs' x w hwn, vl_input gs x w hwn]
    · obtain ⟨r, rfl⟩ : ∃ r, w = n + r := ⟨w - n, by omega⟩
      have hrk : r < k := by omega
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        have hr' : gs'[r]? = none := by rw [hpre r hrk, hr]
        have hl' : gs'.length ≤ r := List.getElem?_eq_none_iff.1 hr'
        rw [Readers.vl_beyond gs' x _ (Nat.add_le_add_left hl' n), Readers.vl_beyond gs x _ (Nat.add_le_add_left hl n)]
      | some g =>
        have hr' : gs'[r]? = some g := by rw [hpre r hrk, hr]
        rw [vl_gate gs' hcl' x r g hr', vl_gate gs hcl x r g hr]
        congr 1
        apply List.map_congr_left
        intro a ha
        exact ih a ((hcl r g hr).lt a ha) (lt_trans ((hcl r g hr).lt a ha) hw) x

theorem output_eq_top {n : ℕ} (hn : 5 ≤ n) (C : Circuit)
    (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C = Bridge.cycFun n) :
    C.output = n + C.size - 1 := by
  obtain ⟨_, hcl, _, _, _, hout_lt, _⟩ := minimal_clean_cyc n C hn hmin hfun
  by_contra hne
  have hlt : C.output < n + (C.size - 1) := by omega
  let k := C.size - 1
  have hk_le : k ≤ C.gates.length := by change k ≤ C.size; omega
  let gs' := C.gates.take k
  have hpre : ∀ r, r < k → gs'[r]? = C.gates[r]? := fun r hr => List.getElem?_take_of_lt hr
  have hcl' : CleanL n gs' := by
    intro r g hr
    by_cases hrk : r < k
    · rw [hpre r hrk] at hr; exact hcl r g hr
    · have hlen : gs'.length ≤ r := by simp [gs']; omega
      rw [List.getElem?_eq_none hlen] at hr; cases hr
  let D : Circuit := ⟨gs', C.output⟩
  have hDf : FanInTwo D := fun g hg => hmin.1 g (List.mem_of_mem_take hg)
  have hDe : circuitFun n D = circuitFun n C := by
    funext x; show vl gs' x C.output = vl C.gates x C.output
    exact vl_agree_prefix C.gates gs' hcl hcl' k hpre C.output hlt x
  have hDsz : C.size ≤ D.size := hmin.2 D hDf hDe
  have hlen' : gs'.length = k := List.length_take_of_le hk_le
  have hDsz' : C.size ≤ k := by simpa [D, Circuit.size, hlen'] using hDsz
  have hcpos : 1 ≤ C.size := by omega
  omega

end PEqualNP.Outside.L_meta_314_aux.WrapOut

namespace PEqualNP.Outside.L_meta_314_aux
namespace WireClass
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev wgE:=@List.getElem?_eq_some_iff
abbrev wmF:=@Finset.mem_filter
abbrev wmI:=@Finset.mem_insert
abbrev wm1:=@Finset.mem_singleton
abbrev wmU:=@Finset.mem_univ
abbrev wmN:=@Finset.notMem_empty
def stepW (w:List Bool) (g:Gate):List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma wa37 (gs:List Gate) (w:List Bool):(gs.foldl stepW w).length=w.length + gs.length:=by{
induction gs generalizing w with
| nil=>simp
| cons g gs ih =>{
simp only [List.foldl_cons,List.length_cons];rw [ih (stepW w g)];simp [stepW];omega
}
}
lemma wa28 (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i < w.length):(gs.foldl stepW w).getD i false=w.getD i false:=by{
induction gs generalizing w with
| nil=>rfl
| cons g gs ih =>{
simp only [List.foldl_cons]
have hi':i < (stepW w g).length:=by simp [stepW];omega
rw [ih (stepW w g) hi'];simp only [stepW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
}
}
lemma wa31 (gs:List Gate) (w:List Bool) (j:ℕ) (hj:j < gs.length):(gs.foldl stepW w).getD (w.length + j) false=(gs[j]).op.eval ((gs[j]).inputs.map fun i=>if i < w.length + j then (gs.foldl stepW w).getD i false else false):=by
 induction gs generalizing w j with
 | nil=>simp at hj
 | cons g gs ih =>
  cases j with
  | zero =>
   simp only [Nat.add_zero,List.foldl_cons,List.getElem_cons_zero]
   have hlen:w.length < (stepW w g).length:=by simp [stepW]
   rw [wa28 gs (stepW w g) w.length hlen];have hval:(stepW w g).getD w.length false =
    g.op.eval (g.inputs.map fun i=>w.getD i false):=by
    simp [stepW,List.getD_eq_getElem?_getD]
   rw [hval];congr 1;apply List.map_congr_left;intro i _
   by_cases hi:i < w.length
   · simp only [hi,↓reduceIte]
     have hi':i < (stepW w g).length:=by simp [stepW];omega
     rw [wa28 gs (stepW w g) i hi'];simp only [stepW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
   · simp only [hi,↓reduceIte];simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_lt hi),Option.getD_none]
  | succ j' =>
   have hj':j' < gs.length:=Nat.lt_of_succ_lt_succ hj;simp only [List.foldl_cons,List.getElem_cons_succ]
   have heq:w.length + (j' + 1)=(stepW w g).length + j':=by simp [stepW];omega
   rw [heq];exact ih (stepW w g) j' hj'
def wireVal {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (w:ℕ):Bool :=
 (C.wires (List.ofFn x)).getD w false
lemma wa45 {n:ℕ} (C:Circuit) (x:Fin n→ Bool):C.wires (List.ofFn x)=C.gates.foldl stepW (List.ofFn x):=rfl
lemma wa68 {n:ℕ} (C:Circuit) (x:Fin n→ Bool):(C.wires (List.ofFn x)).length=n + C.size:=by rw [wa45,wa37,List.length_ofFn];rfl
lemma wa52 {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (i:Fin n):wireVal C x i.val=x i:=by{
unfold wireVal;rw [wa45]
have hi:i.val < (List.ofFn x).length:=by simp
rw [wa28 C.gates (List.ofFn x) i.val hi];simp [List.getD_eq_getElem?_getD]
}
lemma wa5c {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (j:ℕ) (hj:j < C.gates.length):wireVal C x (n + j)=(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i=>if i < n + j then wireVal C x i else false):=by{
unfold wireVal;rw [wa45];have hlen:(List.ofFn x).length=n:=List.length_ofFn;have h:=wa31 C.gates (List.ofFn x) j hj;simpa [hlen] using h
}
lemma wa6f {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (w:ℕ) (hw:n + C.gates.length ≤ w):wireVal C x w=false:=by{
unfold wireVal
have hlen:(C.wires (List.ofFn x)).length ≤ w:=by rw [wa68];exact hw
simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hlen]
}
lemma wa14 {n:ℕ} (C:Circuit) (x:Fin n→ Bool):circuitFun n C x=wireVal C x C.output:=rfl
lemma wa2f (op:GateOp) (hop:op=GateOp.and∨ op=GateOp.or) (l₁ l₂ : List Bool) (hlen:l₁.length=l₂.length) (hle:∀ i (h1:i < l₁.length) (h2:i < l₂.length),l₁[i]=true→ l₂[i]=true):op.eval l₁=true→ op.eval l₂=true:=by{
rcases hop with rfl | rfl
{simp only [GateOp.eval,List.all_eq_true,id_eq];intro h y hy;obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem hy;have hi1:i < l₁.length:=hlen ▸ hi;exact hle i hi1 hi (h l₁[i] (List.getElem_mem hi1))}
{simp only [GateOp.eval,List.any_eq_true,id_eq];rintro ⟨y,hy,rfl⟩;obtain ⟨i,hi,hy_eq⟩:=List.getElem_of_mem hy;have hi2:i < l₂.length:=hlen ▸ hi;refine ⟨l₂[i],List.getElem_mem hi2,hle i hi hi2 hy_eq⟩}
}
lemma wa5b {n:ℕ} (C:Circuit) (hnn:∀ g ∈ C.gates,g.op=GateOp.and∨ g.op=GateOp.or) (x y:Fin n→ Bool) (hle:∀ i:Fin n,x i=true→ y i=true):∀ w:ℕ,wireVal C x w=true→ wireVal C y w=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hw
  by_cases hwn:w < n
  · have hx:=wa52 C x ⟨w,hwn⟩;have hy:=wa52 C y ⟨w,hwn⟩
    exact hy ▸ hle ⟨w,hwn⟩ (by simpa [hx] using hw)
  · by_cases hwl:w < n + C.gates.length
    · have hj:w - n < C.gates.length:=by omega
      have heq:n + (w - n)=w:=by omega
      rw [← heq,wa5c C x (w - n) hj] at hw;rw [← heq,wa5c C y (w - n) hj]
      refine wa2f C.gates[w - n].op (hnn _ (List.getElem_mem hj)) _ _ (by simp) ?_ hw
      intro i h1 h2;simp only [List.getElem_map]
      split_ifs with hi
      · exact ih _ (by omega)
      · intro hc;exact absurd hc (by decide)
    · rw [wa6f C x w (by omega)] at hw
      exact absurd hw (by decide)
def wa70 (n q repl w:ℕ):ℕ :=
 if w < n + q then w else if w=n + q then repl else w - 1
def wa7a (n q w:ℕ):ℕ :=
 if w < n + q then w else w - 1
def wa74 (f:ℕ→ ℕ) (g:Gate):Gate :=
 ⟨g.op,g.inputs.map f⟩
def wa82 (n:ℕ) (C:Circuit) (q repl:ℕ):Circuit :=
 ⟨C.gates.take q ++ (C.gates.drop (q + 1)).map (wa74 (wa70 n q repl)),wa70 n q repl C.output⟩
lemma wa63 {n:ℕ} (C:Circuit) (q repl:ℕ) (hq:q < C.gates.length):(wa82 n C q repl).size=C.size - 1:=by{
simp only [wa82,Circuit.size,List.length_append,List.length_take,List.length_map,List.length_drop];omega
}
lemma wa3f {n:ℕ} (C:Circuit) (q repl:ℕ) (hf:FanInTwo C):FanInTwo (wa82 n C q repl):=by{
intro g hg;simp only [wa82,List.mem_append,List.mem_map] at hg
rcases hg with hg | ⟨g',hg',rfl⟩
{exact hf g (List.mem_of_mem_take hg)}
{have h:=hf g' (List.mem_of_mem_drop hg');simpa [wa74] using h}
}
lemma wa54 {n:ℕ} (C:Circuit) (q repl:ℕ) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not):∀ g ∈ (wa82 n C q repl).gates,g.op ≠ GateOp.not:=by{
intro g hg;simp only [wa82,List.mem_append,List.mem_map] at hg
rcases hg with hg | ⟨g',hg',rfl⟩
{exact hnn g (List.mem_of_mem_take hg)}
{exact hnn g' (List.mem_of_mem_drop hg')}
}
lemma wa46 {n:ℕ} (C:Circuit) (q repl:ℕ) (hq:q < C.gates.length) (hrepl:repl < n + q) (x:Fin n→ Bool) (heq:wireVal C x (n + q)=wireVal C x repl):∀ w:ℕ,w ≠ n + q→ wireVal (wa82 n C q repl) x (wa7a n q w)=wireVal C x w:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hne
  by_cases hw_lt_n:w < n
  · have hso:wa7a n q w=w:=by simp [wa7a];omega
    rw [hso];let i:Fin n:=⟨w,hw_lt_n⟩;exact (wa52 (wa82 n C q repl) x i).trans (wa52 C x i).symm
  · have hw_ge_n:n ≤ w:=Nat.le_of_not_lt hw_lt_n
    by_cases hw_lt_len:w < n + C.gates.length
    · let k:=w - n
      have hk_eq:n + k=w:=by omega
      have hk_lt:k < C.gates.length:=by omega
      by_cases hkq:k < q
      · have hso:wa7a n q w=w:=by simp [wa7a];omega
        rw [hso,← hk_eq]
        have htake:(C.gates.take q).length=q:=by rw [List.length_take];omega
        have hk':k < (wa82 n C q repl).gates.length:=by simp only [wa82,List.length_append,htake,List.length_map,List.length_drop];omega
        rw [wa5c (wa82 n C q repl) x k hk',wa5c C x k hk_lt]
        have hgk:(wa82 n C q repl).gates[k]=C.gates[k]:=by
         simp only [wa82]
         rw [List.getElem_append_left (by rw [htake];exact hkq),List.getElem_take]
        rw [hgk];congr 1;apply List.map_congr_left;intro i _
        by_cases hi:i < n + k
        · simp only [hi,↓reduceIte]
          have hne':i ≠ n + q:=by omega
          have hi_so:wa7a n q i=i:=by simp [wa7a];omega
          have h1:=ih i (by omega) hne'
          rw [hi_so] at h1;exact h1
        · simp only [hi,↓reduceIte]
      · have hq_lt_k:q < k:=by omega
        have hso:wa7a n q w=n + (k - 1):=by simp only [wa7a];split_ifs <;> omega
        rw [hso,← hk_eq]
        have htake:(C.gates.take q).length=q:=by rw [List.length_take];omega
        have hk':k - 1 < (wa82 n C q repl).gates.length:=by simp only [wa82,List.length_append,htake,List.length_map,List.length_drop];omega
        rw [wa5c (wa82 n C q repl) x (k - 1) hk',wa5c C x k hk_lt]
        have hidx:(q + 1) + (k - 1 - q)=k:=by omega
        have hgk:(wa82 n C q repl).gates[k - 1] = wa74 (wa70 n q repl) C.gates[k]:=by
         simp only [wa82]
         rw [List.getElem_append_right (by rw [htake];omega)]
         simp only [htake];rw [List.getElem_map,List.getElem_drop];simp only [hidx]
        rw [hgk,wa74,List.map_map];congr 1;apply List.map_congr_left;intro i _;simp only [Function.comp_apply]
        by_cases hi:i < n + k
        · have hsi:wa70 n q repl i < n + (k - 1):=by
           simp only [wa70]
           split_ifs <;> omega
          simp only [hi,hsi,↓reduceIte]
          by_cases hiq:i=n + q
          · subst hiq
            have hsw:wa70 n q repl (n + q)=repl:=by simp [wa70]
            have hso_r:wa7a n q repl=repl:=by simp [wa7a,hrepl]
            have h1:=ih repl (by omega) (by omega)
            rw [hso_r] at h1;rw [hsw];exact h1.trans heq.symm
          · have hsw:wa70 n q repl i=wa7a n q i:=by
             simp only [wa70,wa7a,hiq,↓reduceIte]
            rw [hsw]
            exact ih i (by omega) hiq
        · have hsi:¬ wa70 n q repl i < n + (k - 1):=by
           simp only [wa70]
           split_ifs <;> omega
          simp only [hi,hsi,↓reduceIte]
    · have hw_ge:n + C.gates.length ≤ w:=Nat.le_of_not_lt hw_lt_len
      have hso_ge:n + (wa82 n C q repl).gates.length ≤ wa7a n q w:=by
       have hsz:(wa82 n C q repl).gates.length=C.gates.length - 1:=by simpa [Circuit.size] using wa63 C q repl hq
       simp only [wa7a,hsz]
       split_ifs <;> omega
      rw [wa6f (wa82 n C q repl) x _ hso_ge,wa6f C x w hw_ge]
lemma wa20 {n:ℕ} (C:Circuit) (q repl:ℕ) (hq:q < C.gates.length) (hrepl:repl < n + q) (x:Fin n→ Bool) (heq:wireVal C x (n + q)=wireVal C x repl):circuitFun n (wa82 n C q repl) x=circuitFun n C x:=by
 simp only [wa14];change wireVal (wa82 n C q repl) x (wa70 n q repl C.output)=wireVal C x C.output
 by_cases hout:C.output=n + q
 · have hsw:wa70 n q repl C.output=repl:=by simp [wa70,hout]
   have hso:wa7a n q repl=repl:=by simp [wa7a,hrepl]
   have h1:=wa46 C q repl hq hrepl x heq repl (by omega)
   rw [hso] at h1;rw [hsw,hout,heq];exact h1
 · have hsw:wa70 n q repl C.output=wa7a n q C.output:=by
    simp only [wa70,wa7a,hout,↓reduceIte]
   rw [hsw];exact wa46 C q repl hq hrepl x heq C.output hout
lemma wa1c {n:ℕ} (C:Circuit) (q repl:ℕ) (hq:q < C.gates.length) (hunused:∀ (k:ℕ) (hk:k < C.gates.length),q < k→ n + q ∉ (C.gates[k]).inputs) (x:Fin n→ Bool):∀ w:ℕ,w ≠ n + q→ wireVal (wa82 n C q repl) x (wa7a n q w)=wireVal C x w:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hne
  by_cases hw_lt_n:w < n
  · have hso:wa7a n q w=w:=by simp [wa7a];omega
    rw [hso];exact (wa52 (wa82 n C q repl) x ⟨w,hw_lt_n⟩).trans
     (wa52 C x ⟨w,hw_lt_n⟩).symm
  · have hw_ge_n:n ≤ w:=Nat.le_of_not_lt hw_lt_n
    by_cases hw_lt_len:w < n + C.gates.length
    · let k:=w - n
      have hk_eq:n + k=w:=by omega
      have hk_lt:k < C.gates.length:=by omega
      by_cases hkq:k < q
      · have hso:wa7a n q w=w:=by simp [wa7a];omega
        rw [hso,← hk_eq]
        have htake:(C.gates.take q).length=q:=by rw [List.length_take];omega
        have hk':k < (wa82 n C q repl).gates.length:=by simp only [wa82,List.length_append,htake,List.length_map,List.length_drop];omega
        rw [wa5c (wa82 n C q repl) x k hk',wa5c C x k hk_lt]
        have hgk:(wa82 n C q repl).gates[k]=C.gates[k]:=by
         simp only [wa82]
         rw [List.getElem_append_left (by rw [htake];exact hkq),List.getElem_take]
        rw [hgk];congr 1;apply List.map_congr_left;intro i _
        by_cases hi:i < n + k
        · simp only [hi,↓reduceIte]
          have hi_so:wa7a n q i=i:=by simp [wa7a];omega
          have h1:=ih i (by omega) (by omega)
          rw [hi_so] at h1;exact h1
        · simp only [hi,↓reduceIte]
      · have hq_lt_k:q < k:=by omega
        have hso:wa7a n q w=n + (k - 1):=by simp only [wa7a];split_ifs <;> omega
        rw [hso,← hk_eq]
        have htake:(C.gates.take q).length=q:=by rw [List.length_take];omega
        have hk':k - 1 < (wa82 n C q repl).gates.length:=by simp only [wa82,List.length_append,htake,List.length_map,List.length_drop];omega
        rw [wa5c (wa82 n C q repl) x (k - 1) hk',wa5c C x k hk_lt]
        have hidx:(q + 1) + (k - 1 - q)=k:=by omega
        have hgk:(wa82 n C q repl).gates[k - 1] = wa74 (wa70 n q repl) C.gates[k]:=by
         simp only [wa82]
         rw [List.getElem_append_right (by rw [htake];omega)]
         simp only [htake];rw [List.getElem_map,List.getElem_drop];simp only [hidx]
        rw [hgk,wa74,List.map_map];congr 1;apply List.map_congr_left;intro i hi_mem;have hi_neq:i ≠ n + q:=fun h=>hunused k hk_lt hq_lt_k (h ▸ hi_mem);simp only [Function.comp_apply]
        by_cases hi:i < n + k
        · have hsi:wa70 n q repl i < n + (k - 1):=by
           simp only [wa70,hi_neq,↓reduceIte]
           split_ifs <;> omega
          have hsw:wa70 n q repl i=wa7a n q i:=by simp only [wa70,wa7a,hi_neq,↓reduceIte]
          simp only [hi,hsi,↓reduceIte];rw [hsw]
          exact ih i (by omega) hi_neq
        · have hsi:¬ wa70 n q repl i < n + (k - 1):=by
           simp only [wa70,hi_neq,↓reduceIte]
           split_ifs <;> omega
          simp only [hi,hsi,↓reduceIte]
    · have hw_ge:n + C.gates.length ≤ w:=Nat.le_of_not_lt hw_lt_len
      have hso_ge:n + (wa82 n C q repl).gates.length ≤ wa7a n q w:=by
       have hsz:(wa82 n C q repl).gates.length=C.gates.length - 1:=by simpa [Circuit.size] using wa63 C q repl hq
       simp only [wa7a,hsz]
       split_ifs <;> omega
      rw [wa6f (wa82 n C q repl) x _ hso_ge,wa6f C x w hw_ge]
lemma wa34 {n:ℕ} (C:Circuit) (q repl:ℕ) (hq:q < C.gates.length) (hout:C.output ≠ n + q) (hunused:∀ (k:ℕ) (hk:k < C.gates.length),q < k→ n + q ∉ (C.gates[k]).inputs) (x:Fin n→ Bool):circuitFun n (wa82 n C q repl) x=circuitFun n C x:=by{
simp only [wa14];change wireVal (wa82 n C q repl) x (wa70 n q repl C.output)=wireVal C x C.output
have hsw:wa70 n q repl C.output=wa7a n q C.output:=by simp only [wa70,wa7a,hout,↓reduceIte]
rw [hsw];exact wa1c C q repl hq hunused x C.output hout
}
def wa77 (op:GateOp) (a b:Sum Bool ℕ) (nextW:ℕ):Sum Bool ℕ × Option Gate :=
 match op with
 | GateOp.and =>
  match a,b with
  | Sum.inl false,_=>(Sum.inl false,none)
  | _,Sum.inl false=>(Sum.inl false,none)
  | Sum.inl true,r=>(r,none)
  | r,Sum.inl true=>(r,none)
  | Sum.inr u,Sum.inr v=>(Sum.inr nextW,some ⟨GateOp.and,[u,v]⟩)
 | GateOp.or =>
  match a,b with
  | Sum.inl true,_=>(Sum.inl true,none)
  | _,Sum.inl true=>(Sum.inl true,none)
  | Sum.inl false,r=>(r,none)
  | r,Sum.inl false=>(r,none)
  | Sum.inr u,Sum.inr v=>(Sum.inr nextW,some ⟨GateOp.or,[u,v]⟩)
 | _=>(Sum.inl false,none)
def wa7f (n:ℕ) (st:List (Sum Bool ℕ) × List Gate) (g:Gate):Sum Bool ℕ × Option Gate :=
 let m:=st.1.length;let lookup:=fun w:ℕ=>if w < m then st.1.getD w (Sum.inl false) else Sum.inl false
 match g.op,g.inputs with
 | GateOp.and,[]=>(Sum.inl true,none)
 | GateOp.and,[a]=>(lookup a,none)
 | GateOp.and,[a,b]=>wa77 GateOp.and (lookup a) (lookup b) (n + st.2.length)
 | GateOp.or,[]=>(Sum.inl false,none)
 | GateOp.or,[a]=>(lookup a,none)
 | GateOp.or,[a,b]=>wa77 GateOp.or (lookup a) (lookup b) (n + st.2.length)
 | GateOp.not,[a] =>
  match lookup a with
  | Sum.inl c=>(Sum.inl (!c),none)
  | Sum.inr u=>(Sum.inr (n + st.2.length),some ⟨GateOp.not,[u]⟩)
 | GateOp.not,[a,_] =>
  match lookup a with
  | Sum.inl c=>(Sum.inl (!c),none)
  | Sum.inr u=>(Sum.inr (n + st.2.length),some ⟨GateOp.not,[u]⟩)
 | GateOp.not,[]=>(Sum.inl true,none)
 | _,_=>(Sum.inl false,none)
def wa7b {n:ℕ} (gs:List Gate) (x:Fin n→ Bool):Sum Bool ℕ→ Bool
 | Sum.inl c=>c
 | Sum.inr w=>wireVal ⟨gs,0⟩ x w
lemma wa11 {n:ℕ} (gs gs':List Gate) (x:Fin n→ Bool) (w:ℕ) (hw:w < n + gs.length):wireVal ⟨gs ++ gs',0⟩ x w=wireVal ⟨gs,0⟩ x w:=by
 simp only [wireVal,wa45,List.foldl_append]
 have hlen:(gs.foldl stepW (List.ofFn x)).length=n + gs.length:=by rw [wa37,List.length_ofFn]
 exact wa28 gs' (gs.foldl stepW (List.ofFn x)) w (by omega)
lemma wa59 (n:ℕ) (st:List (Sum Bool ℕ) × List Gate) (g:Gate) (hg:(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not)∧ g.inputs.length ≤ 2) (x:Fin n→ Bool) (hbound:∀ s ∈ st.1,match s with | Sum.inl _=>True | Sum.inr u=>u < n + st.2.length) :
 let res:=wa7f n st g
 let gs':=match res.2 with | none=>st.2 | some g'=>st.2 ++ [g']
 (match res.1 with | Sum.inl _=>True | Sum.inr u=>u < n + gs'.length) ∧
 (∀ g' ∈ gs',(g' ∈ st.2∨ (g'.op=g.op∧ g'.inputs.length ≤ 2))) ∧
 wa7b gs' x res.1=g.op.eval (g.inputs.map fun w =>
  if w < st.1.length then wa7b st.2 x (st.1.getD w (Sum.inl false)) else false):=by
 have hb_all:∀ w,match (if w < st.1.length then st.1.getD w (Sum.inl false) else Sum.inl false) with
  | Sum.inl _=>True | Sum.inr u=>u < n + st.2.length:=by
  intro w
  split_ifs with hw
  · simp only [List.getD_eq_getElem?_getD,wgE.2 ⟨hw,rfl⟩,Option.getD_some]
    exact hbound _ (List.getElem_mem hw)
  · trivial
 have heval_if:∀ w, (if w < st.1.length then wa7b st.2 x (st.1.getD w (Sum.inl false)) else false) = wa7b st.2 x (if w < st.1.length then st.1.getD w (Sum.inl false) else Sum.inl false) :=
  fun w=>by split_ifs <;> rfl
 rcases hg with ⟨hop,hlen⟩
 rcases hop with hop | hop | hop
 · rcases h_in:g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩
   · simp only [wa7f,hop,h_in,List.map_nil,GateOp.eval,List.all_nil,wa7b];exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
   · have ha:=hb_all a;simp only [wa7f,hop,h_in,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,heval_if]
     cases h:(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false) with
     | inl c=>exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
     | inr u =>
      rw [h] at ha;exact ⟨ha,fun _ hg'=>Or.inl hg',trivial⟩
   · have ha:=hb_all a;have hb:=hb_all b;simp only [wa7f,hop,h_in,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,heval_if]
     cases ha_v:(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false) with
     | inl ca =>
      cases ca
      · simp only [wa77,wa7b,Bool.false_and];exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
      · cases hb_v:(if b < st.1.length then st.1.getD b (Sum.inl false) else Sum.inl false) with
        | inl cb =>
         cases cb <;> simp only [wa77,wa7b,Bool.true_and] <;>
          exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
        | inr v =>
         rw [hb_v] at hb;simp only [wa77,wa7b,Bool.true_and];exact ⟨hb,fun _ hg'=>Or.inl hg',trivial⟩
     | inr u =>
      rw [ha_v] at ha
      cases hb_v:(if b < st.1.length then st.1.getD b (Sum.inl false) else Sum.inl false) with
      | inl cb =>
       cases cb <;> simp only [wa77,wa7b,Bool.and_false,Bool.and_true]
       · exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
       · exact ⟨ha,fun _ hg'=>Or.inl hg',trivial⟩
      | inr v =>
       rw [hb_v] at hb;simp only [wa77,List.mem_append,List.mem_singleton]
       refine ⟨by simp,fun g' hg'=>?_,?_⟩
       · rcases hg' with h | rfl
         · exact Or.inl h
         · exact Or.inr ⟨rfl,by simp⟩
       · simp only [wa7b];let C':Circuit:=⟨st.2 ++ [⟨GateOp.and,[u,v]⟩],0⟩
         have hlt:st.2.length < C'.gates.length:=by simp [C']
         rw [wa5c C' x st.2.length hlt];simp only [C',List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,ha,hb,↓reduceIte];rw [wa11 st.2 _ x u ha,wa11 st.2 _ x v hb]
   · simp [h_in] at hlen
 · rcases h_in:g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩
   · simp only [wa7f,hop,h_in,List.map_nil,GateOp.eval,List.any_nil,wa7b];exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
   · have ha:=hb_all a;simp only [wa7f,hop,h_in,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,heval_if]
     cases h:(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false) with
     | inl c=>exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
     | inr u =>
      rw [h] at ha;exact ⟨ha,fun _ hg'=>Or.inl hg',trivial⟩
   · have ha:=hb_all a;have hb:=hb_all b;simp only [wa7f,hop,h_in,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,heval_if]
     cases ha_v:(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false) with
     | inl ca =>
      cases ca
      · cases hb_v:(if b < st.1.length then st.1.getD b (Sum.inl false) else Sum.inl false) with
        | inl cb =>
         cases cb <;> simp only [wa77,wa7b,Bool.false_or] <;>
          exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
        | inr v =>
         rw [hb_v] at hb;simp only [wa77,wa7b,Bool.false_or];exact ⟨hb,fun _ hg'=>Or.inl hg',trivial⟩
      · simp only [wa77,wa7b,Bool.true_or];exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
     | inr u =>
      rw [ha_v] at ha
      cases hb_v:(if b < st.1.length then st.1.getD b (Sum.inl false) else Sum.inl false) with
      | inl cb =>
       cases cb <;> simp only [wa77,wa7b,Bool.or_false,Bool.or_true]
       · exact ⟨ha,fun _ hg'=>Or.inl hg',trivial⟩
       · exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
      | inr v =>
       rw [hb_v] at hb;simp only [wa77,List.mem_append,List.mem_singleton]
       refine ⟨by simp,fun g' hg'=>?_,?_⟩
       · rcases hg' with h | rfl
         · exact Or.inl h
         · exact Or.inr ⟨rfl,by simp⟩
       · simp only [wa7b];let C':Circuit:=⟨st.2 ++ [⟨GateOp.or,[u,v]⟩],0⟩
         have hlt:st.2.length < C'.gates.length:=by simp [C']
         rw [wa5c C' x st.2.length hlt];simp only [C',List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,ha,hb,↓reduceIte];rw [wa11 st.2 _ x u ha,wa11 st.2 _ x v hb]
   · simp [h_in] at hlen
 · rcases h_in:g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩
   · simp only [wa7f,hop,h_in,List.map_nil,GateOp.eval,List.headD_nil,Bool.not_false,wa7b];exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
   · have ha:=hb_all a;simp only [wa7f,hop,h_in,List.map_cons,List.map_nil,GateOp.eval,List.headD_cons,heval_if]
     cases h:(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false) with
     | inl c=>simp only [wa7b];exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
     | inr u =>
      rw [h] at ha
      refine ⟨by simp,fun g' hg'=>?_,?_⟩
      · simp only [List.mem_append,List.mem_singleton] at hg'
        rcases hg' with h' | rfl
        · exact Or.inl h'
        · exact Or.inr ⟨rfl,by simp⟩
      · simp only [wa7b];let C':Circuit:=⟨st.2 ++ [⟨GateOp.not,[u]⟩],0⟩
        have hlt:st.2.length < C'.gates.length:=by simp [C']
        rw [wa5c C' x st.2.length hlt];simp only [C',List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero,List.map_cons,List.map_nil,GateOp.eval,List.headD_cons,ha,↓reduceIte];rw [wa11 st.2 _ x u ha]
   · have ha:=hb_all a;simp only [wa7f,hop,h_in,List.map_cons,List.map_nil,GateOp.eval,List.headD_cons,heval_if]
     cases h:(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false) with
     | inl c=>simp only [wa7b];exact ⟨trivial,fun _ hg'=>Or.inl hg',trivial⟩
     | inr u =>
      rw [h] at ha
      refine ⟨by simp,fun g' hg'=>?_,?_⟩
      · simp only [List.mem_append,List.mem_singleton] at hg'
        rcases hg' with h' | rfl
        · exact Or.inl h'
        · exact Or.inr ⟨rfl,by simp⟩
      · simp only [wa7b];let C':Circuit:=⟨st.2 ++ [⟨GateOp.not,[u]⟩],0⟩
        have hlt:st.2.length < C'.gates.length:=by simp [C']
        rw [wa5c C' x st.2.length hlt];simp only [C',List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero,List.map_cons,List.map_nil,GateOp.eval,List.headD_cons,ha,↓reduceIte];rw [wa11 st.2 _ x u ha]
   · simp [h_in] at hlen
lemma wa4e (op:GateOp) (a b:Sum Bool ℕ) (w u:ℕ) (h1:(wa77 op a b w).1=Sum.inr u):(wa77 op a b w).2=none→ a=Sum.inr u∨ b=Sum.inr u:=by{
intro h2
rcases op with _ | _ | _ | _ | _
{
cases a with
| inl ca =>{
cases ca
{simp [wa77] at h1}
{
cases b with
| inl cb=>cases cb <;> simp [wa77] at h1
| inr vb=>simp [wa77] at h1;exact Or.inr (congrArg Sum.inr h1)
}
}
| inr va =>{
cases b with
| inl cb =>{
cases cb
{simp [wa77] at h1}
{simp [wa77] at h1;exact Or.inl (congrArg Sum.inr h1)}
}
| inr vb=>simp [wa77] at h2
}
}
{
cases a with
| inl ca =>{
cases ca
{
cases b with
| inl cb=>cases cb <;> simp [wa77] at h1
| inr vb=>simp [wa77] at h1;exact Or.inr (congrArg Sum.inr h1)
}
{simp [wa77] at h1}
}
| inr va =>{
cases b with
| inl cb =>{
cases cb
{simp [wa77] at h1;exact Or.inl (congrArg Sum.inr h1)}
{simp [wa77] at h1}
}
| inr vb=>simp [wa77] at h2
}
}
{simp [wa77] at h1}
{simp [wa77] at h1}
{simp [wa77] at h1}
}
lemma wa4b (op:GateOp) (a b:Sum Bool ℕ) (w:ℕ) (g':Gate) (h:(wa77 op a b w).2=some g'):(op=GateOp.and∨ op=GateOp.or)∧ ∃ u v:ℕ,a=Sum.inr u∧ b=Sum.inr v∧ g'=⟨op,[u,v]⟩∧ (wa77 op a b w).1=Sum.inr w:=by{
rcases op with _ | _ | _ | _ | _
{
cases a with
| inl ca =>{
cases ca
{simp [wa77] at h}
{
cases b with
| inl cb=>cases cb <;> simp [wa77] at h
| inr vb=>simp [wa77] at h
}
}
| inr va =>{
cases b with
| inl cb=>cases cb <;> simp [wa77] at h
| inr vb =>{
simp only [wa77,Option.some.injEq] at h;exact ⟨Or.inl rfl,va,vb,rfl,rfl,h.symm,rfl⟩
}
}
}
{
cases a with
| inl ca =>{
cases ca
{
cases b with
| inl cb=>cases cb <;> simp [wa77] at h
| inr vb=>simp [wa77] at h
}
{simp [wa77] at h}
}
| inr va =>{
cases b with
| inl cb=>cases cb <;> simp [wa77] at h
| inr vb =>{
simp only [wa77,Option.some.injEq] at h;exact ⟨Or.inr rfl,va,vb,rfl,rfl,h.symm,rfl⟩
}
}
}
{simp [wa77] at h}
{simp [wa77] at h}
{simp [wa77] at h}
}
def wa6c (n:ℕ) (fix:ℕ→ Option Bool) (q:ℕ) (st:List (Sum Bool ℕ) × List Gate) (g:Gate):Sum Bool ℕ × Option Gate :=
 match fix (n + q) with
 | some b=>(Sum.inl b,none)
 | none=>wa7f n st g
def wa72 (n:ℕ) (fix:ℕ→ Option Bool) (k:ℕ):List Gate→ List (Sum Bool ℕ) × List Gate × List ℕ→ List (Sum Bool ℕ) × List Gate × List ℕ
 | [],st=>st
 | g :: gs,st =>
  let res:=wa6c n fix k (st.1,st.2.1) g
  let st':=match res.2 with
   | none=>(st.1 ++ [res.1],st.2.1,st.2.2)
   | some g'=>(st.1 ++ [res.1],st.2.1 ++ [g'],st.2.2 ++ [k])
  wa72 n fix (k + 1) gs st'
def wa79 (n:ℕ) (fix:ℕ→ Option Bool):List (Sum Bool ℕ) :=
 List.ofFn fun i:Fin n =>
  match fix i.val with
  | some b=>Sum.inl b
  | none=>Sum.inr i.val
lemma wa58 (n:ℕ) (fix:ℕ→ Option Bool):(wa79 n fix).length=n:=by simp [wa79]
lemma wa4a (n:ℕ) (fix:ℕ→ Option Bool):∀ s ∈ wa79 n fix,match s with | Sum.inl _=>True | Sum.inr u=>u < n + 0:=by{
intro s hs;simp only [wa79,List.mem_ofFn] at hs;obtain ⟨i,rfl⟩:=hs
cases fix i.val with
| some b=>trivial
| none=>exact Nat.lt_of_lt_of_le i.isLt (Nat.le_refl _)
}
lemma wa30 (n:ℕ) (fix:ℕ→ Option Bool) (q:ℕ) (st:List (Sum Bool ℕ) × List Gate) (g:Gate) (hg:(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not)∧ g.inputs.length ≤ 2) (hbound:∀ s ∈ st.1,match s with | Sum.inl _=>True | Sum.inr u=>u < n + st.2.length) :
 let res:=wa6c n fix q st g
 let gs':=match res.2 with | none=>st.2 | some g'=>st.2 ++ [g']
 (match res.1 with | Sum.inl _=>True | Sum.inr u=>u < n + gs'.length) ∧
 (∀ g' ∈ gs',g' ∈ st.2∨ (g'.op=g.op∧ g'.inputs.length ≤ 2)):=by
 cases hfx:fix (n + q) with
 | some b =>
  simp only [wa6c,hfx];exact ⟨trivial,fun _ h=>Or.inl h⟩
 | none =>
  have hsp:=wa59 n st g hg (fun _=>false) hbound;simpa [wa6c,hfx] using ⟨hsp.1,hsp.2.1⟩
lemma wa15 (n:ℕ) (fix:ℕ→ Option Bool) (q:ℕ) (st:List (Sum Bool ℕ) × List Gate) (g g':Gate) (hg:(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not)∧ g.inputs.length ≤ 2) (hsome:(wa6c n fix q st g).2=some g'):g'.op=g.op∧ g'.inputs.length ≤ 2∧ (wa6c n fix q st g).1=Sum.inr (n + st.2.length)∧ (∀ u ∈ g'.inputs,∃ a ∈ g.inputs,a < st.1.length∧ st.1.getD a (Sum.inl false)=Sum.inr u):=by
 cases hfx:fix (n + q) with
 | some b=>simp [wa6c,hfx] at hsome
 | none =>
  simp only [wa6c,hfx] at hsome ⊢
  rcases hg with ⟨hop,hlen⟩
  rcases hop with hop | hop | hop <;>
   rcases h_in:g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩
  all_goals try (simp [wa7f,hop,h_in] at hsome;done)
  all_goals try (simp [h_in] at hlen;done)
  · simp only [wa7f,hop,h_in] at hsome ⊢
    obtain ⟨_,_,_,h1,h2,h3,h4⟩ :=
     wa4b GateOp.and _ _ (n + st.2.length) g' hsome
    subst h3
    refine ⟨rfl,by simp,h4,fun u hu=>?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl
    · by_cases ha:a < st.1.length
      · simp only [ha,↓reduceIte] at h1;exact ⟨a,by simp,ha,h1⟩
      · simp only [ha,↓reduceIte] at h1;cases h1
    · by_cases hb:b < st.1.length
      · simp only [hb,↓reduceIte] at h2;exact ⟨b,by simp,hb,h2⟩
      · simp only [hb,↓reduceIte] at h2;cases h2
  · simp only [wa7f,hop,h_in] at hsome ⊢
    obtain ⟨_,_,_,h1,h2,h3,h4⟩ :=
     wa4b GateOp.or _ _ (n + st.2.length) g' hsome
    subst h3
    refine ⟨rfl,by simp,h4,fun u hu=>?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl
    · by_cases ha:a < st.1.length
      · simp only [ha,↓reduceIte] at h1;exact ⟨a,by simp,ha,h1⟩
      · simp only [ha,↓reduceIte] at h1;cases h1
    · by_cases hb:b < st.1.length
      · simp only [hb,↓reduceIte] at h2;exact ⟨b,by simp,hb,h2⟩
      · simp only [hb,↓reduceIte] at h2;cases h2
  · simp only [wa7f,hop,h_in] at hsome ⊢
    cases ha_v:(if a < st.1.length then st.1[a]?.getD (Sum.inl false) else Sum.inl false) with
    | inl ca =>
     have ha_v':(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false)=Sum.inl ca:=by simpa [List.getD_eq_getElem?_getD] using ha_v
     rw [ha_v'] at hsome
     simp only at hsome
     cases hsome
    | inr v =>
     have ha_v':(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false)=Sum.inr v:=by simpa [List.getD_eq_getElem?_getD] using ha_v
     rw [ha_v'] at hsome;simp only [Option.some.injEq] at hsome;subst hsome
     refine ⟨rfl,by simp,by simp [ha_v],fun u hu=>?_⟩
     simp only [List.mem_singleton] at hu;subst hu
     by_cases ha:a < st.1.length
     · simp only [ha,↓reduceIte] at ha_v';exact ⟨a,by simp,ha,ha_v'⟩
     · simp only [ha,↓reduceIte] at ha_v';cases ha_v'
  · simp only [wa7f,hop,h_in] at hsome ⊢
    cases ha_v:(if a < st.1.length then st.1[a]?.getD (Sum.inl false) else Sum.inl false) with
    | inl ca =>
     have ha_v':(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false)=Sum.inl ca:=by simpa [List.getD_eq_getElem?_getD] using ha_v
     rw [ha_v'] at hsome
     simp only at hsome
     cases hsome
    | inr v =>
     have ha_v':(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false)=Sum.inr v:=by simpa [List.getD_eq_getElem?_getD] using ha_v
     rw [ha_v'] at hsome;simp only [Option.some.injEq] at hsome;subst hsome
     refine ⟨rfl,by simp,by simp [ha_v],fun u hu=>?_⟩
     simp only [List.mem_singleton] at hu;subst hu
     by_cases ha:a < st.1.length
     · simp only [ha,↓reduceIte] at ha_v';exact ⟨a,by simp,ha,ha_v'⟩
     · simp only [ha,↓reduceIte] at ha_v';cases ha_v'
lemma wa3c (n:ℕ) (fix:ℕ→ Option Bool) (q:ℕ) (st:List (Sum Bool ℕ) × List Gate) (g:Gate) (hg:(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not)∧ g.inputs.length ≤ 2) (x:Fin n→ Bool) (hfixq:∀ b,fix (n + q)=some b→ g.op.eval (g.inputs.map fun w=>if w < st.1.length then wa7b st.2 x (st.1.getD w (Sum.inl false)) else false)=b) (hbound:∀ s ∈ st.1,match s with | Sum.inl _=>True | Sum.inr u=>u < n + st.2.length) :
 let res:=wa6c n fix q st g
 let gs':=match res.2 with | none=>st.2 | some g'=>st.2 ++ [g']
 (match res.1 with | Sum.inl _=>True | Sum.inr u=>u < n + gs'.length) ∧
 (∀ g' ∈ gs',g' ∈ st.2∨ (g'.op=g.op∧ g'.inputs.length ≤ 2)) ∧
 wa7b gs' x res.1=g.op.eval (g.inputs.map fun w =>
  if w < st.1.length then wa7b st.2 x (st.1.getD w (Sum.inl false)) else false):=by
 cases hfx:fix (n + q) with
 | some b =>
  simp only [wa6c,hfx];refine ⟨trivial,fun _ h=>Or.inl h,?_⟩
  simp only [wa7b];exact (hfixq b hfx).symm
 | none=>simpa [wa6c,hfx] using wa59 n st g hg x hbound
lemma wa32 (n:ℕ) (fix:ℕ→ Option Bool) (k:ℕ) (gs₁ gs₂ : List Gate) (st:List (Sum Bool ℕ) × List Gate × List ℕ) :
 wa72 n fix k (gs₁ ++ gs₂) st =
  wa72 n fix (k + gs₁.length) gs₂ (wa72 n fix k gs₁ st):=by
 induction gs₁ generalizing k st with
 | nil=>simp [wa72]
 | cons g gs₁ ih =>
  simp only [List.cons_append,wa72,List.length_cons];rw [ih (k + 1)];simp only [Nat.add_assoc,Nat.add_comm 1 gs₁.length]
lemma wa33 (n:ℕ) (fix:ℕ→ Option Bool):∀ (k:ℕ) (gs:List Gate) (st:List (Sum Bool ℕ) × List Gate × List ℕ),st.1.length=n + k→ st.2.2.length=st.2.1.length→ (∀ s ∈ st.1,match s with | Sum.inl _=>True | Sum.inr u=>u < n + st.2.1.length)→ (∀ q ∈ st.2.2,q < k)→ (∀ j₁ j₂ (h₁ : j₁ < st.2.2.length) (h₂ : j₂ < st.2.2.length),j₁ < j₂→ st.2.2[j₁] < st.2.2[j₂])→ (∀ j (hj:j < st.2.2.length),st.1.getD (n + st.2.2[j]) (Sum.inl false)=Sum.inr (n + j))→ (∀ g ∈ gs,(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not)∧ g.inputs.length ≤ 2)→ (∀ g' ∈ st.2.1,(g'.op=GateOp.and∨ g'.op=GateOp.or∨ g'.op=GateOp.not)∧ g'.inputs.length ≤ 2) →
 let res:=wa72 n fix k gs st
 res.1.length=n + (k + gs.length) ∧
 res.2.2.length=res.2.1.length ∧
 (∀ s ∈ res.1,match s with | Sum.inl _=>True | Sum.inr u=>u < n + res.2.1.length) ∧
 (∀ q ∈ res.2.2,q < k + gs.length) ∧
 (∀ j₁ j₂ (h₁ : j₁ < res.2.2.length) (h₂ : j₂ < res.2.2.length),j₁ < j₂→ res.2.2[j₁] < res.2.2[j₂]) ∧
 (∀ j (hj:j < res.2.2.length),res.1.getD (n + res.2.2[j]) (Sum.inl false)=Sum.inr (n + j)) ∧
 (∀ g' ∈ res.2.1,(g'.op=GateOp.and∨ g'.op=GateOp.or∨ g'.op=GateOp.not) ∧
  g'.inputs.length ≤ 2):=by
 intro k gs
 induction gs generalizing k with
 | nil =>
  intro st hlen hslen hb hq hmono hsrc hgs hst1;exact ⟨hlen,hslen,hb,hq,hmono,hsrc,hst1⟩
 | cons g gs ih =>
  intro st hlen hslen hb hq hmono hsrc hgs hst1
  have hg:(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not)∧ g.inputs.length ≤ 2 :=
   hgs g List.mem_cons_self
  have hgs':∀ g' ∈ gs,(g'.op=GateOp.and∨ g'.op=GateOp.or∨ g'.op=GateOp.not)∧ g'.inputs.length ≤ 2:=fun g' hg'=>hgs g' (List.mem_cons_of_mem g hg')
  have hspec:=wa30 n fix k (st.1,st.2.1) g hg hb
  rcases hres2:(wa6c n fix k (st.1,st.2.1) g).2 with _ | g' <;>
   simp only [wa72,hres2,List.length_cons]
  · have hspec':=hspec;simp only [hres2] at hspec'
    have hlen':(st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1]).length=n + (k + 1):=by simp [hlen];omega
    have hb':∀ s ∈ st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1], match s with | Sum.inl _=>True | Sum.inr u=>u < n + st.2.1.length:=by
     intro s hs;simp only [List.mem_append,List.mem_singleton] at hs
     rcases hs with hs | rfl
     · exact hb s hs
     · exact hspec'.1
    have hq':∀ q ∈ st.2.2,q < k + 1:=fun q hqm=>Nat.lt_succ_of_lt (hq q hqm)
    have hsrc':∀ j (hj:j < st.2.2.length), (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1]).getD (n + st.2.2[j]) (Sum.inl false) = Sum.inr (n + j):=by
     intro j hj
     have hlt:n + st.2.2[j] < st.1.length:=by have:=hq _ (List.getElem_mem hj);omega
     rw [List.getD_eq_getElem?_getD,List.getElem?_append_left hlt,← List.getD_eq_getElem?_getD]
     exact hsrc j hj
    have hres:=ih (k + 1) (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],st.2.1,st.2.2)
     hlen' hslen hb' hq' hmono hsrc' hgs' hst1
    have hkeq:k + 1 + gs.length=k + (gs.length + 1):=by omega
    rw [hkeq] at hres;exact hres
  · have hspec':=hspec;simp only [hres2] at hspec';have hinfo:=wa15 n fix k (st.1,st.2.1) g g' hg hres2
    have hlen':(st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1]).length=n + (k + 1):=by simp [hlen];omega
    have hslen':(st.2.2 ++ [k]).length=(st.2.1 ++ [g']).length:=by simp [hslen]
    have hb':∀ s ∈ st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1], match s with | Sum.inl _=>True | Sum.inr u=>u < n + (st.2.1 ++ [g']).length:=by
     intro s hs;simp only [List.mem_append,List.mem_singleton] at hs
     rcases hs with hs | rfl
     · have hs0:=hb s hs
       cases s with
       | inl _=>trivial
       | inr u=>simp only [List.length_append,List.length_singleton];omega
     · exact hspec'.1
    have hq':∀ q ∈ st.2.2 ++ [k],q < k + 1:=by
     intro q hqm;simp only [List.mem_append,List.mem_singleton] at hqm
     rcases hqm with hqm | rfl
     · exact Nat.lt_succ_of_lt (hq q hqm)
     · omega
    have hmono':∀ j₁ j₂ (h₁ : j₁ < (st.2.2 ++ [k]).length) (h₂ : j₂ < (st.2.2 ++ [k]).length), j₁ < j₂→ (st.2.2 ++ [k])[j₁] < (st.2.2 ++ [k])[j₂]:=by
     intro j₁ j₂ h₁ h₂ hij;simp only [List.length_append,List.length_singleton] at h₁ h₂
     by_cases hj₂ : j₂ < st.2.2.length
     · have hj₁ : j₁ < st.2.2.length:=by omega
       rw [List.getElem_append_left hj₁,List.getElem_append_left hj₂];exact hmono j₁ j₂ hj₁ hj₂ hij
     · have hj₂eq:j₂=st.2.2.length:=by omega
       have hj₁ : j₁ < st.2.2.length:=by omega
       subst hj₂eq;rw [List.getElem_append_left hj₁];simp only [List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero];exact hq _ (List.getElem_mem hj₁)
    have hsrc':∀ j (hj:j < (st.2.2 ++ [k]).length), (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1]).getD (n + (st.2.2 ++ [k])[j]) (Sum.inl false)=Sum.inr (n + j):=by
     intro j hj;simp only [List.length_append,List.length_singleton] at hj
     by_cases hj0:j < st.2.2.length
     · rw [List.getElem_append_left hj0]
       have hlt:n + st.2.2[j] < st.1.length:=by have:=hq _ (List.getElem_mem hj0);omega
       rw [List.getD_eq_getElem?_getD,List.getElem?_append_left hlt,← List.getD_eq_getElem?_getD]
       exact hsrc j hj0
     · have hjeq:j=st.2.2.length:=by omega
       subst hjeq;simp only [List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero]
       rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [hlen]),hlen]
       simp only [Nat.sub_self,List.getElem?_cons_zero,Option.getD_some,hinfo.2.2.1,hslen]
    have hst1':∀ g'' ∈ st.2.1 ++ [g'], (g''.op=GateOp.and∨ g''.op=GateOp.or∨ g''.op=GateOp.not)∧ g''.inputs.length ≤ 2:=by
     intro g'' hg''
     rcases hspec'.2 g'' hg'' with h1 | h2
     · exact hst1 g'' h1
     · exact ⟨h2.1.symm ▸ hg.1,h2.2⟩
    have hres:=ih (k + 1) (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],st.2.1 ++ [g'],st.2.2 ++ [k]) hlen' hslen' hb' hq' hmono' hsrc' hgs' hst1'
    have hkeq:k + 1 + gs.length=k + (gs.length + 1):=by omega
    rw [hkeq] at hres;exact hres
lemma waf (n:ℕ) (fix:ℕ→ Option Bool):∀ (k:ℕ) (gs:List Gate) (st:List (Sum Bool ℕ) × List Gate × List ℕ) (w:ℕ),w < st.1.length→ (wa72 n fix k gs st).1.getD w (Sum.inl false)=st.1.getD w (Sum.inl false):=by
 intro k gs
 induction gs generalizing k with
 | nil=>intro st w _hw;rfl
 | cons g gs ih =>
  intro st w hw
  rcases h2:(wa6c n fix k (st.1,st.2.1) g).2 with _ | g' <;>
   simp only [wa72,h2]
  · have hw':w < (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1]).length:=by simp;omega
    rw [ih (k + 1) _ w hw'];simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hw]
  · have hw':w < (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1]).length:=by simp;omega
    rw [ih (k + 1) _ w hw'];simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hw]
lemma wa18 (n:ℕ) (fix:ℕ→ Option Bool):∀ (k:ℕ) (gs:List Gate) (st:List (Sum Bool ℕ) × List Gate × List ℕ),(∀ j,j < st.2.1.length→ (wa72 n fix k gs st).2.1[j]?=st.2.1[j]?)∧ (∀ j,j < st.2.2.length→ (wa72 n fix k gs st).2.2[j]?=st.2.2[j]?):=by
 intro k gs
 induction gs generalizing k with
 | nil=>intro st;exact ⟨fun _ _=>rfl,fun _ _=>rfl⟩
 | cons g gs ih =>
  intro st
  rcases h2:(wa6c n fix k (st.1,st.2.1) g).2 with _ | g' <;>
   simp only [wa72,h2]
  · simpa using ih (k + 1) (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],st.2.1,st.2.2)
  · have hrec:=ih (k + 1) (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],st.2.1 ++ [g'],st.2.2 ++ [k]);constructor
    · intro j hj
      have hj':j < (st.2.1 ++ [g']).length:=by simp;omega
      rw [hrec.1 j hj',List.getElem?_append_left hj]
    · intro j hj
      have hj':j < (st.2.2 ++ [k]).length:=by simp;omega
      rw [hrec.2 j hj',List.getElem?_append_left hj]
lemma wa23 (n:ℕ) (fix:ℕ→ Option Bool):∀ (k:ℕ) (gs:List Gate) (st:List (Sum Bool ℕ) × List Gate × List ℕ),st.2.1.length ≤ (wa72 n fix k gs st).2.1.length∧ st.2.2.length ≤ (wa72 n fix k gs st).2.2.length:=by
 intro k gs
 induction gs generalizing k with
 | nil=>intro st;exact ⟨le_refl _,le_refl _⟩
 | cons g gs ih =>
  intro st
  rcases h2:(wa6c n fix k (st.1,st.2.1) g).2 with _ | g' <;>
   simp only [wa72,h2]
  · simpa using ih (k + 1) (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],st.2.1,st.2.2)
  · have hrec:=ih (k + 1) (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],st.2.1 ++ [g'],st.2.2 ++ [k]);simp only [List.length_append,List.length_singleton] at hrec;omega
lemma wa35 (n:ℕ) (fix:ℕ→ Option Bool):∀ (k:ℕ) (gs:List Gate) (st:List (Sum Bool ℕ) × List Gate × List ℕ),(∀ g ∈ gs,(g.op=GateOp.and∨ g.op=GateOp.or)∧ g.inputs.length ≤ 2)→ (∀ g' ∈ st.2.1,g'.op ≠ GateOp.not)→ ∀ g' ∈ (wa72 n fix k gs st).2.1,g'.op ≠ GateOp.not:=by
 intro k gs
 induction gs generalizing k with
 | nil=>intro st _ hst;exact hst
 | cons g gs ih =>
  intro st hgs hst;have hg:=hgs g List.mem_cons_self
  have hg_nn:g.op ≠ GateOp.not:=by rcases hg.1 with h | h <;> simp [h]
  have hgs':=fun g' hg'=>hgs g' (List.mem_cons_of_mem g hg');dsimp only [wa72]
  cases h2:(wa6c n fix k (st.1,st.2.1) g).2 with
  | none=>exact ih (k + 1) _ hgs' hst
  | some g' =>
   dsimp only;refine ih (k + 1) _ hgs' ?_
   have hinfo:=wa15 n fix k (st.1,st.2.1) g g'
    ⟨Or.imp_right Or.inl hg.1,hg.2⟩ h2
   intro g'' hg'';simp only [List.mem_append,List.mem_singleton] at hg''
   rcases hg'' with h1 | rfl
   · exact hst g'' h1
   · rw [hinfo.1];exact hg_nn
lemma wa44 (n:ℕ) (C:Circuit) (fix:ℕ→ Option Bool) (hft:FanInTwo C) (x:Fin n→ Bool) (hfix_gate:∀ q,q < C.gates.length→ ∀ b,fix (n + q)=some b→ wireVal C x (n + q)=b):∀ (k:ℕ) (suf:List Gate) (st:List (Sum Bool ℕ) × List Gate × List ℕ),k + suf.length=C.gates.length→ (∀ j,j < suf.length→ suf[j]?=C.gates[k + j]?)→ st.1.length=n + k→ (∀ s ∈ st.1,match s with | Sum.inl _=>True | Sum.inr u=>u < n + st.2.1.length)→ (∀ w,w < n + k→ wa7b st.2.1 x (st.1.getD w (Sum.inl false))=wireVal C x w)→ ∀ w,w < n + C.gates.length→ wa7b (wa72 n fix k suf st).2.1 x ((wa72 n fix k suf st).1.getD w (Sum.inl false))=wireVal C x w:=by
 intro k suf
 induction suf generalizing k with
 | nil =>
  intro st hk _ hlen _ heval w hw;simp only [List.length_nil,Nat.add_zero] at hk;subst hk;exact heval w hw
 | cons g suf ih =>
  intro st hk hsuf hlen hb heval w hw
  have hk_lt:k < C.gates.length:=by simp only [List.length_cons] at hk;omega
  have hg_eq:C.gates[k]?=some g:=by
   have h0:=hsuf 0 (by simp)
   simpa using h0.symm
  have hg_mem:g ∈ C.gates:=List.mem_of_getElem? hg_eq;have hg_ft:=hft g hg_mem;have hg_spec_in:(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not) ∧
   g.inputs.length ≤ 2:=by
   rcases hg_ft with ⟨hop,hlen'⟩
   refine ⟨?_,hlen'⟩
   simpa using hop
  have hfixq:∀ b,fix (n + k)=some b→ g.op.eval (g.inputs.map fun w => if w < st.1.length then wa7b st.2.1 x (st.1.getD w (Sum.inl false)) else false)=b:=by
   intro b hfb;have hwval:=hfix_gate k hk_lt b hfb;rw [wa5c C x k hk_lt] at hwval;have hg_idx:C.gates[k]=g:=(wgE.1 hg_eq).2;rw [hg_idx] at hwval;rw [← hwval];congr 1;apply List.map_congr_left;intro u _
   by_cases hu:u < n + k
   · simp only [hlen,hu,↓reduceIte];exact heval u hu
   · simp only [hlen,hu,↓reduceIte]
  have hsp:=wa3c n fix k (st.1,st.2.1) g hg_spec_in x hfixq hb
  rcases h2:(wa6c n fix k (st.1,st.2.1) g).2 with _ | g' <;>
   simp only [wa72,h2]
  · have hsp':=hsp;simp only [h2] at hsp'
    refine ih (k + 1) _ (by simp only [List.length_cons] at hk;omega) ?_ ?_ ?_ ?_ w hw
    · intro j hj
      have hj':=hsuf (j + 1) (by simp only [List.length_cons];omega)
      simp only [List.getElem?_cons_succ] at hj'
      simpa [Nat.add_assoc,Nat.add_comm 1 j] using hj'
    · simp [hlen];omega
    · intro s hs;simp only [List.mem_append,List.mem_singleton] at hs
      rcases hs with hs | rfl
      · exact hb s hs
      · exact hsp'.1
    · intro u hu
      by_cases huk:u < n + k
      · rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega),← List.getD_eq_getElem?_getD]
        exact heval u huk
      · have hueq:u=n + k:=by omega
        subst hueq;dsimp only
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [hlen]),hlen]
        simp only [Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
        rw [hsp'.2.2,wa5c C x k hk_lt];have hg_idx:C.gates[k]=g:=(wgE.1 hg_eq).2;rw [hg_idx];congr 1;apply List.map_congr_left;intro v _
        by_cases hv:v < n + k
        · simp only [hlen,hv,↓reduceIte];exact heval v hv
        · simp only [hlen,hv,↓reduceIte]
  · have hsp':=hsp;simp only [h2] at hsp'
    refine ih (k + 1) _ (by simp only [List.length_cons] at hk;omega) ?_ ?_ ?_ ?_ w hw
    · intro j hj
      have hj':=hsuf (j + 1) (by simp only [List.length_cons];omega)
      simp only [List.getElem?_cons_succ] at hj'
      simpa [Nat.add_assoc,Nat.add_comm 1 j] using hj'
    · simp [hlen];omega
    · intro s hs;simp only [List.mem_append,List.mem_singleton] at hs
      rcases hs with hs | rfl
      · have hs0:=hb s hs
        cases s with
        | inl _=>trivial
        | inr u=>simp only [List.length_append,List.length_singleton];omega
      · exact hsp'.1
    · intro u hu
      by_cases huk:u < n + k
      · rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega),← List.getD_eq_getElem?_getD]
        have hpre:wa7b (st.2.1 ++ [g']) x (st.1.getD u (Sum.inl false)) = wa7b st.2.1 x (st.1.getD u (Sum.inl false)):=by
         have hmem:st.1.getD u (Sum.inl false) ∈ st.1:=by
          rw [List.getD_eq_getElem?_getD,wgE.2 ⟨by omega,rfl⟩,Option.getD_some]
          exact List.getElem_mem (by omega)
         have hbu:=hb _ hmem
         cases hgv:st.1.getD u (Sum.inl false) with
         | inl c=>rfl
         | inr v =>
          rw [hgv] at hbu;simp only [wa7b];exact wa11 st.2.1 [g'] x v hbu
        rw [hpre];exact heval u huk
      · have hueq:u=n + k:=by omega
        subst hueq;dsimp only
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [hlen]),hlen]
        simp only [Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
        rw [hsp'.2.2,wa5c C x k hk_lt];have hg_idx:C.gates[k]=g:=(wgE.1 hg_eq).2;rw [hg_idx];congr 1;apply List.map_congr_left;intro v _
        by_cases hv:v < n + k
        · simp only [hlen,hv,↓reduceIte];exact heval v hv
        · simp only [hlen,hv,↓reduceIte]
lemma wa2c (n:ℕ) (C:Circuit) (fix:ℕ→ Option Bool) (hft:FanInTwo C) (x:Fin n→ Bool) (hfix_in:∀ i:Fin n,∀ b,fix i.val=some b→ x i=b) (hfix_gate:∀ q,q < C.gates.length→ ∀ b,fix (n + q)=some b→ wireVal C x (n + q)=b) :
 let res:=wa72 n fix 0 C.gates (wa79 n fix,[],[])
 ∀ w,w < n + C.gates.length→ wa7b res.2.1 x (res.1.getD w (Sum.inl false))=wireVal C x w:=by
 apply wa44 n C fix hft x hfix_gate 0 C.gates (wa79 n fix,[],[])
 · simp
 · intro _ _;simp
 · exact wa58 n fix
 · exact wa4a n fix
 · intro w hw;simp only [Nat.add_zero] at hw
   have hw_len:w < (wa79 n fix).length:=by rw [wa58];exact hw
   rw [List.getD_eq_getElem?_getD,wgE.2 ⟨hw_len,rfl⟩,Option.getD_some]
   simp only [wa79,List.getElem_ofFn]
   cases hfx:fix w with
   | some b =>
    simp only [wa7b];have hx:=hfix_in ⟨w,hw⟩ b hfx;rw [← wa52 C x ⟨w,hw⟩] at hx;exact hx.symm
   | none =>
    simp only [wa7b];rw [wa52 ⟨[],0⟩ x ⟨w,hw⟩,wa52 C x ⟨w,hw⟩]
lemma wa1f (n:ℕ) (fix:ℕ→ Option Bool) (q:ℕ) (st:List (Sum Bool ℕ) × List Gate) (g:Gate) (hg:(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not)∧ g.inputs.length ≤ 2) (hnone:(wa6c n fix q st g).2=none) (u:ℕ) (hinr:(wa6c n fix q st g).1=Sum.inr u):∃ a ∈ g.inputs,a < st.1.length∧ st.1.getD a (Sum.inl false)=Sum.inr u:=by
 cases hfx:fix (n + q) with
 | some b=>simp [wa6c,hfx] at hinr
 | none =>
  simp only [wa6c,hfx] at hnone hinr
  rcases hg with ⟨hop,hlen⟩
  rcases hop with hop | hop | hop <;>
   rcases h_in:g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩
  all_goals try (simp [wa7f,hop,h_in] at hinr;done)
  all_goals try (simp [h_in] at hlen;done)
  · simp only [wa7f,hop,h_in] at hinr
    by_cases ha:a < st.1.length
    · simp only [ha,↓reduceIte] at hinr;exact ⟨a,by simp,ha,hinr⟩
    · simp only [ha,↓reduceIte] at hinr;cases hinr
  · simp only [wa7f,hop,h_in] at hnone hinr
    rcases wa4e GateOp.and _ _ (n + st.2.length) u hinr hnone with h | h
    · by_cases ha:a < st.1.length
      · simp only [ha,↓reduceIte] at h;exact ⟨a,by simp,ha,h⟩
      · simp only [ha,↓reduceIte] at h;cases h
    · by_cases hb:b < st.1.length
      · simp only [hb,↓reduceIte] at h;exact ⟨b,by simp,hb,h⟩
      · simp only [hb,↓reduceIte] at h;cases h
  · simp only [wa7f,hop,h_in] at hinr
    by_cases ha:a < st.1.length
    · simp only [ha,↓reduceIte] at hinr;exact ⟨a,by simp,ha,hinr⟩
    · simp only [ha,↓reduceIte] at hinr;cases hinr
  · simp only [wa7f,hop,h_in] at hnone hinr
    rcases wa4e GateOp.or _ _ (n + st.2.length) u hinr hnone with h | h
    · by_cases ha:a < st.1.length
      · simp only [ha,↓reduceIte] at h;exact ⟨a,by simp,ha,h⟩
      · simp only [ha,↓reduceIte] at h;cases h
    · by_cases hb:b < st.1.length
      · simp only [hb,↓reduceIte] at h;exact ⟨b,by simp,hb,h⟩
      · simp only [hb,↓reduceIte] at h;cases h
  · simp only [wa7f,hop,h_in] at hnone hinr
    cases h:(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false) with
    | inl ca=>rw [h] at hinr;cases hinr
    | inr v=>rw [h] at hnone;cases hnone
  · simp only [wa7f,hop,h_in] at hnone hinr
    cases h:(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false) with
    | inl ca=>rw [h] at hinr;cases hinr
    | inr v=>rw [h] at hnone;cases hnone
lemma waa (n:ℕ) (fix:ℕ→ Option Bool) (q:ℕ) (st:List (Sum Bool ℕ) × List Gate) (g g':Gate) (hg:(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not)∧ g.inputs.length ≤ 2) (hsome:(wa6c n fix q st g).2=some g') (u:ℕ) (hu:u ∈ g'.inputs):∃ a ∈ g.inputs,a < st.1.length∧ st.1.getD a (Sum.inl false)=Sum.inr u :=
 (wa15 n fix q st g g' hg hsome).2.2.2 u hu
lemma wa2e (n:ℕ) (C:Circuit) (fix:ℕ→ Option Bool) (hft:FanInTwo C) (q:ℕ) (hq:q < C.gates.length) :
 let st_q:=wa72 n fix 0 (C.gates.take q) (wa79 n fix,[],[]);let g_q:=C.gates[q];let res_q:=wa6c n fix q (st_q.1,st_q.2.1) g_q;let full:=wa72 n fix 0 C.gates (wa79 n fix,[],[])
 st_q.1.length=n + q ∧
 full.1.getD (n + q) (Sum.inl false)=res_q.1 ∧
 (∀ w,w < n + q→ full.1.getD w (Sum.inl false)=st_q.1.getD w (Sum.inl false)) ∧
 (res_q.2=none→ q ∉ full.2.2) ∧
 (∀ g',res_q.2=some g'→ st_q.2.2.length < full.2.2.length∧ full.2.2[st_q.2.2.length]?=some q ∧
  full.2.1[st_q.2.1.length]?=some g'):=by
 have htake_len:(C.gates.take q).length=q:=by rw [List.length_take];exact Nat.min_eq_left (Nat.le_of_lt hq)
 have hsplit:C.gates=C.gates.take q ++ C.gates[q] :: C.gates.drop (q + 1):=by
  conv_lhs=>rw [← List.take_append_drop q C.gates]
  congr 1;exact List.drop_eq_getElem_cons hq
 have hprops_q:=wa33 n fix 0 (C.gates.take q) (wa79 n fix,[],[])
  (wa58 n fix) rfl (wa4a n fix) (fun _ h=>by cases h)
  (fun j₁ _ h₁ _=>by simp at h₁) (fun j hj=>by simp at hj)
  (fun g hg=>by have:=hft g (List.mem_of_mem_take hg);simpa using this)
  (fun _ h=>by cases h)
 have hstq_len:(wa72 n fix 0 (C.gates.take q) (wa79 n fix,[],[])).1.length=n + q:=by rw [hprops_q.1,Nat.zero_add,htake_len]
 have hfull_eq:wa72 n fix 0 C.gates (wa79 n fix,[],[]) = wa72 n fix q (C.gates[q] :: C.gates.drop (q + 1)) (wa72 n fix 0 (C.gates.take q) (wa79 n fix,[],[])):=by
  conv_lhs=>rw [hsplit,wa32,Nat.zero_add,htake_len]
 refine ⟨hstq_len,?_,?_,?_,?_⟩
 · rw [hfull_eq];simp only [wa72]
   rcases h2:(wa6c n fix q _ C.gates[q]).2 with _ | g'
   · rw [waf n fix (q + 1) _ _ (n + q) (by simp [hstq_len])]
     rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
     simp [hstq_len]
   · rw [waf n fix (q + 1) _ _ (n + q) (by simp [hstq_len])]
     rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
     simp [hstq_len]
 · intro w hw;rw [hfull_eq];simp only [wa72]
   rcases (wa6c n fix q _ C.gates[q]).2 with _ | g'
   · rw [waf n fix (q + 1) _ _ w (by simp [hstq_len];omega)]
     rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega),← List.getD_eq_getElem?_getD]
   · rw [waf n fix (q + 1) _ _ w (by simp [hstq_len];omega)]
     rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega),← List.getD_eq_getElem?_getD]
 · intro hnone hmem;have hfull_props:=wa33 n fix 0 C.gates (wa79 n fix,[],[])
    (wa58 n fix) rfl (wa4a n fix) (fun _ h=>by cases h)
    (fun j₁ _ h₁ _=>by simp at h₁) (fun j hj=>by simp at hj)
    (fun g hg=>by have:=hft g hg;simpa using this) (fun _ h=>by cases h)
   rw [hfull_eq] at hmem;dsimp only [wa72] at hmem;rw [hnone] at hmem;dsimp only at hmem;obtain ⟨j,hj,hjeq⟩:=List.getElem_of_mem hmem;set st_q:=wa72 n fix 0 (C.gates.take q) (wa79 n fix,[],[]);have hlt_src:j < st_q.2.2.length∨ st_q.2.2.length ≤ j:=Nat.lt_or_ge j st_q.2.2.length
   rcases hlt_src with hj_lt | hj_ge
   · have hpre:=(wa18 n fix (q + 1) (C.gates.drop (q + 1)) (st_q.1 ++ [(wa6c n fix q (st_q.1,st_q.2.1) C.gates[q]).1],st_q.2.1,st_q.2.2)).2 j hj_lt;rw [wgE.2 ⟨hj,hjeq⟩] at hpre;have hj_mem:st_q.2.2[j] ∈ st_q.2.2:=List.getElem_mem hj_lt;have hq_lt:=hprops_q.2.2.2.1 _ hj_mem;have hq_eq:st_q.2.2[j]=q:=(wgE.1 hpre.symm).2;omega
   · have hsrc_w:=hfull_props.2.2.2.2.2.1 j (by rw [hfull_eq];dsimp only [wa72];rw [hnone];exact hj)
     have hq_eq:(wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2[j]'(by rw [hfull_eq];dsimp only [wa72];rw [hnone];exact hj)=q:=by
      simpa [hfull_eq,wa72,hnone] using hjeq
     have hn_eq:(wa72 n fix 0 C.gates (wa79 n fix,[],[])).1.getD (n + q) (Sum.inl false) = Sum.inr (n + j):=by
      simpa [hq_eq] using hsrc_w
     have h_at_q:(wa72 n fix 0 C.gates (wa79 n fix,[],[])).1.getD (n + q) (Sum.inl false) = (wa6c n fix q (st_q.1,st_q.2.1) C.gates[q]).1:=by
      rw [hfull_eq];dsimp only [wa72];rw [hnone];dsimp only
      rw [waf n fix (q + 1) _ _ (n + q) (by simp [hstq_len])]
      rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
      simp [hstq_len]
     rw [h_at_q] at hn_eq;have hgq_spec:(C.gates[q].op=GateOp.and∨ C.gates[q].op=GateOp.or∨ C.gates[q].op=GateOp.not) ∧
      C.gates[q].inputs.length ≤ 2:=by simpa using hft C.gates[q] (List.getElem_mem hq)
     obtain ⟨a,_,ha_lt,ha_eq⟩:=wa1f n fix q (st_q.1,st_q.2.1) C.gates[q]
      hgq_spec hnone (n + j) hn_eq
     have ha_mem:st_q.1.getD a (Sum.inl false) ∈ st_q.1:=by
      rw [List.getD_eq_getElem?_getD,wgE.2 ⟨ha_lt,rfl⟩,Option.getD_some]
      exact List.getElem_mem ha_lt
     have ha_bd:=hprops_q.2.2.1 _ ha_mem;rw [ha_eq] at ha_bd;have hsl:=hprops_q.2.1;omega
 · intro g' hsome;rw [hfull_eq];dsimp only [wa72];rw [hsome];dsimp only;set st_q:=wa72 n fix 0 (C.gates.take q) (wa79 n fix,[],[]);have hlen_m:=wa23 n fix (q + 1) (C.gates.drop (q + 1))
    (st_q.1 ++ [(wa6c n fix q (st_q.1,st_q.2.1) C.gates[q]).1],st_q.2.1 ++ [g'],st_q.2.2 ++ [q])
   have hpre:=wa18 n fix (q + 1) (C.gates.drop (q + 1))
    (st_q.1 ++ [(wa6c n fix q (st_q.1,st_q.2.1) C.gates[q]).1],st_q.2.1 ++ [g'],st_q.2.2 ++ [q])
   refine ⟨by simp only [List.length_append,List.length_singleton] at hlen_m;omega,?_,?_⟩
   · have h1:=hpre.2 st_q.2.2.length (by simp)
     simpa using h1
   · have h1:=hpre.1 st_q.2.1.length (by simp)
     simpa using h1
lemma wa26 (n:ℕ) (C:Circuit) (fix:ℕ→ Option Bool) (hft:FanInTwo C) (j0 q0:ℕ) (hj0:j0 < (wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2.length) (hq0_eq:(wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2[j0]=q0) :
 let full:=wa72 n fix 0 C.gates (wa79 n fix,[],[])
 (∀ w,w < n + q0→ full.1.getD w (Sum.inl false) ≠ Sum.inr (n + j0)) ∧
 (∀ (j:ℕ) (hj:j < full.2.1.length),∀ u ∈ (full.2.1[j]'hj).inputs,∃ q a,full.2.2[j]?=some q∧ ∃ (hq:q < C.gates.length),a ∈ (C.gates[q]'hq).inputs∧ a < n + q∧ full.1.getD a (Sum.inl false)=Sum.inr u) ∧
 (∀ q,q0 < q→ ∀ (hq:q < C.gates.length),full.1.getD (n + q) (Sum.inl false)=Sum.inr (n + j0) →
  ∃ a ∈ (C.gates[q]'hq).inputs,a < n + q∧ full.1.getD a (Sum.inl false)=Sum.inr (n + j0)):=by
 have hfull_props:=wa33 n fix 0 C.gates (wa79 n fix,[],[])
  (wa58 n fix) rfl (wa4a n fix) (fun _ h=>by cases h)
  (fun j₁ _ h₁ _=>by simp at h₁) (fun j hj=>by simp at hj)
  (fun g hg=>by have:=hft g hg;simpa using this) (fun _ h=>by cases h)
 have hq0_lt:q0 < C.gates.length:=by have:=hfull_props.2.2.2.1 q0 (hq0_eq ▸ List.getElem_mem hj0);simpa using this
 have h_at_q0:=wa2e n C fix hft q0 hq0_lt;set full:=wa72 n fix 0 C.gates (wa79 n fix,[],[]);set st_q0:=wa72 n fix 0 (C.gates.take q0) (wa79 n fix,[],[])
 have hj0_eq_st:st_q0.2.2.length=j0:=by
  cases hres0:(wa6c n fix q0 (st_q0.1,st_q0.2.1) C.gates[q0]).2 with
  | none=>exact absurd (hq0_eq ▸ List.getElem_mem hj0) (h_at_q0.2.2.2.1 hres0)
  | some g' =>
   have hg':=h_at_q0.2.2.2.2 g' hres0;have h1:full.2.2[st_q0.2.2.length]?=some q0:=hg'.2.1;have h2:full.2.2[j0]?=some q0:=wgE.2 ⟨hj0,hq0_eq⟩;have h1v:=(wgE.1 h1).2;have h2v:=(wgE.1 h2).2
   by_contra hne
   rcases lt_or_gt_of_ne hne with hlt | hlt
   · have hm:=hfull_props.2.2.2.2.1 st_q0.2.2.length j0 hg'.1 hj0 hlt;omega
   · have hm:=hfull_props.2.2.2.2.1 j0 st_q0.2.2.length hj0 hg'.1 hlt;omega
 have hstq0_props:=wa33 n fix 0 (C.gates.take q0) (wa79 n fix,[],[])
  (wa58 n fix) rfl (wa4a n fix) (fun _ h=>by cases h)
  (fun j₁ _ h₁ _=>by simp at h₁) (fun j hj=>by simp at hj)
  (fun g hg=>by have:=hft g (List.mem_of_mem_take hg);simpa using this)
  (fun _ h=>by cases h)
 refine ⟨?_,?_,?_⟩
 · intro w hw heqw;rw [h_at_q0.2.2.1 w hw] at heqw
   have hmem:st_q0.1.getD w (Sum.inl false) ∈ st_q0.1:=by
    rw [List.getD_eq_getElem?_getD,wgE.2 ⟨by rw [h_at_q0.1];exact hw,rfl⟩,Option.getD_some]
    exact List.getElem_mem (by rw [h_at_q0.1];exact hw)
   have hbd:=hstq0_props.2.2.1 _ hmem;rw [heqw,← hstq0_props.2.1,hj0_eq_st] at hbd;omega
 · intro j hj u hu
   have hj_src:j < full.2.2.length:=by rw [hfull_props.2.1];exact hj
   obtain ⟨q,hq_eq_j⟩:∃ q,full.2.2[j]?=some q:=⟨full.2.2[j],wgE.2 ⟨hj_src,rfl⟩⟩
   have hq_lt:q < C.gates.length:=by have:=hfull_props.2.2.2.1 q (List.mem_of_getElem? hq_eq_j);omega
   have h_at_q:=wa2e n C fix hft q hq_lt;set st_q:=wa72 n fix 0 (C.gates.take q) (wa79 n fix,[],[]);have hstq_props:=wa33 n fix 0 (C.gates.take q) (wa79 n fix,[],[])
    (wa58 n fix) rfl (wa4a n fix) (fun _ h=>by cases h)
    (fun j₁ _ h₁ _=>by simp at h₁) (fun j hj=>by simp at hj)
    (fun g hg=>by have:=hft g (List.mem_of_mem_take hg);simpa using this)
    (fun _ h=>by cases h)
   cases hresq:(wa6c n fix q (st_q.1,st_q.2.1) C.gates[q]).2 with
   | none=>exact absurd (List.mem_of_getElem? hq_eq_j) (h_at_q.2.2.2.1 hresq)
   | some g' =>
    have hg':=h_at_q.2.2.2.2 g' hresq;have h1v:=(wgE.1 hg'.2.1).2;have h2v:=(wgE.1 hq_eq_j).2
    have hj_eq:st_q.2.2.length=j:=by
     by_contra hne
     rcases lt_or_gt_of_ne hne with hlt | hlt
     · have hm:=hfull_props.2.2.2.2.1 st_q.2.2.length j hg'.1 hj_src hlt;rw [h1v,h2v] at hm;omega
     · have hm:=hfull_props.2.2.2.2.1 j st_q.2.2.length hj_src hg'.1 hlt;rw [h1v,h2v] at hm;omega
    have hg'_eq:full.2.1[j]=g':=by
     have h3:=hg'.2.2;rw [← hstq_props.2.1,hj_eq] at h3;exact (wgE.1 h3).2
    rw [hg'_eq] at hu;have hgq_spec:(C.gates[q].op=GateOp.and∨ C.gates[q].op=GateOp.or∨ C.gates[q].op=GateOp.not) ∧
     C.gates[q].inputs.length ≤ 2:=by simpa using hft C.gates[q] (List.getElem_mem hq_lt)
    obtain ⟨a,ha_mem,ha_lt,ha_eq⟩:=waa n fix q (st_q.1,st_q.2.1)
     C.gates[q] g' hgq_spec hresq u hu
    rw [h_at_q.1] at ha_lt;refine ⟨q,a,hq_eq_j,hq_lt,ha_mem,ha_lt,?_⟩
    rw [h_at_q.2.2.1 a ha_lt];exact ha_eq
 · intro q hq0q hq_lt hinr;have h_at_q:=wa2e n C fix hft q hq_lt;set st_q:=wa72 n fix 0 (C.gates.take q) (wa79 n fix,[],[])
   cases hresq:(wa6c n fix q (st_q.1,st_q.2.1) C.gates[q]).2 with
   | none =>
    rw [h_at_q.2.1] at hinr;have hgq_spec:(C.gates[q].op=GateOp.and∨ C.gates[q].op=GateOp.or∨ C.gates[q].op=GateOp.not) ∧
     C.gates[q].inputs.length ≤ 2:=by simpa using hft C.gates[q] (List.getElem_mem hq_lt)
    obtain ⟨a,ha_mem,ha_lt,ha_eq⟩:=wa1f n fix q (st_q.1,st_q.2.1)
     C.gates[q] hgq_spec hresq (n + j0) hinr
    rw [h_at_q.1] at ha_lt;refine ⟨a,ha_mem,ha_lt,?_⟩
    rw [h_at_q.2.2.1 a ha_lt];exact ha_eq
   | some g' =>
    have hg':=h_at_q.2.2.2.2 g' hresq;have hsr:=hfull_props.2.2.2.2.2.1 st_q.2.2.length hg'.1;have hq_mem_eq:full.2.2[st_q.2.2.length]'hg'.1=q:=(wgE.1 hg'.2.1).2;rw [hq_mem_eq] at hsr;rw [hsr] at hinr
    have hnj:st_q.2.2.length=j0:=by have:=Sum.inr.inj hinr;omega
    have hq_opt:full.2.2[st_q.2.2.length]?=some q:=hg'.2.1;rw [hnj,wgE.2 ⟨hj0,hq0_eq⟩] at hq_opt
    simp at hq_opt
    omega
def wa73 (n:ℕ) (gs:List Gate) (out:ℕ):ℕ→ Finset ℕ
 | 0=>{out}
 | d + 1 =>
  let N:=wa73 n gs out d;let k:=gs.length - (d + 1)
  match gs[k]? with
  | none=>N
  | some g=>if n + k ∈ N then N ∪ g.inputs.toFinset else N
def wa65 (n:ℕ) (gs:List Gate) (out k:ℕ):Finset ℕ :=
 wa73 n gs out (gs.length - k)
lemma wa47 (n:ℕ) (gs:List Gate) (out k:ℕ) (hk:gs.length ≤ k):wa65 n gs out k={out}:=by{
have hsub:gs.length - k=0:=Nat.sub_eq_zero_of_le hk;simp [wa65,hsub,wa73]
}
lemma wa48 (n:ℕ) (gs:List Gate) (out k:ℕ) (hk:k < gs.length):wa65 n gs out k=if n + k ∈ wa65 n gs out (k + 1) then wa65 n gs out (k + 1) ∪ (gs[k]).inputs.toFinset else wa65 n gs out (k + 1):=by{
unfold wa65
have hd:gs.length - k=(gs.length - (k + 1)) + 1:=by omega
rw [hd,wa73]
have hk_eq:gs.length - (gs.length - (k + 1) + 1)=k:=by omega
rw [hk_eq,wgE.2 ⟨hk,rfl⟩]
}
def wa7e (n:ℕ) (gs:List Gate) (out:ℕ):ℕ→ Circuit→ Circuit
 | 0,C_cur=>C_cur
 | k + 1,C_cur =>
  let C_next :=
   if n + k ∈ wa65 n gs out (k + 1) then C_cur
   else wa82 n C_cur k 0
  wa7e n gs out k C_next
lemma wa53 (n:ℕ) (gs:List Gate) (out:ℕ) (_hf:FanInTwo ⟨gs,out⟩) (_hnn:∀ g ∈ gs,g.op ≠ GateOp.not):∀ (k:ℕ) (C_cur:Circuit),k ≤ gs.length→ k ≤ C_cur.gates.length→ C_cur.gates.take k=gs.take k→ FanInTwo C_cur→ (∀ g ∈ C_cur.gates,g.op ≠ GateOp.not)→ (∀ x,circuitFun n C_cur x=circuitFun n ⟨gs,out⟩ x)→ (∀ w,w < n + k→ (w ∈ wa65 n gs out k↔ (C_cur.output=w∨ ∃ j,∃ (_hj1:k ≤ j) (hj2:j < C_cur.gates.length),w ∈ C_cur.gates[j].inputs)))→ C_cur.gates.length - k=(Finset.univ.filter (fun j:Fin gs.length=>k ≤ j.val∧ n + j.val ∈ wa65 n gs out (j.val + 1))).card →
 let C_fin:=wa7e n gs out k C_cur
 FanInTwo C_fin ∧
 (∀ g ∈ C_fin.gates,g.op ≠ GateOp.not) ∧
 (∀ x,circuitFun n C_fin x=circuitFun n ⟨gs,out⟩ x) ∧
 C_fin.size=(Finset.univ.filter (fun j:Fin gs.length =>
  n + j.val ∈ wa65 n gs out (j.val + 1))).card:=by
 intro k
 induction k with
 | zero =>
  intro C_cur _ _ _ hf_c hnn_c hev _ hcnt;refine ⟨hf_c,hnn_c,hev,?_⟩
  simp only [Circuit.size];simp only [Nat.sub_zero,Nat.zero_le,true_and] at hcnt;exact hcnt
 | succ k ih =>
  intro C_cur hk hclen htake hf_c hnn_c hev hneed hcnt
  have hk_lt:k < gs.length:=by omega
  have hck_lt:k < C_cur.gates.length:=by omega
  have hgk_eq:C_cur.gates[k]=gs[k]:=by
   have h1:(C_cur.gates.take (k + 1))[k]?=(gs.take (k + 1))[k]?:=by rw [htake]
   rw [List.getElem?_take_of_lt (by omega),List.getElem?_take_of_lt (by omega)] at h1
   rw [wgE.2 ⟨hck_lt,rfl⟩,wgE.2 ⟨hk_lt,rfl⟩] at h1;exact Option.some.inj h1
  simp only [wa7e]
  by_cases hmem:n + k ∈ wa65 n gs out (k + 1)
  · simp only [hmem,↓reduceIte]
    refine ih C_cur (by omega) (by omega) ?_ hf_c hnn_c hev ?_ ?_
    · have htk1:List.take k (List.take (k + 1) C_cur.gates)=List.take k (List.take (k + 1) gs):=by
       rw [htake]
      simpa [List.take_take,Nat.min_eq_left (by omega:k ≤ k + 1)] using htk1
    · intro w hw;rw [wa48 n gs out k hk_lt];simp only [hmem,↓reduceIte,Finset.mem_union,List.mem_toFinset]
      rw [hneed w (by omega),← hgk_eq]
      constructor
      · rintro (⟨h1 | ⟨j,hj1,hj2,hj3⟩⟩ | hw_k)
        · exact Or.inl h1
        · exact Or.inr ⟨j,by omega,hj2,hj3⟩
        · exact Or.inr ⟨k,le_refl _,hck_lt,hw_k⟩
      · rintro (h1 | ⟨j,hj1,hj2,hj3⟩)
        · exact Or.inl (Or.inl h1)
        · by_cases hjk:j=k
          · subst hjk;exact Or.inr hj3
          · exact Or.inl (Or.inr ⟨j,by omega,hj2,hj3⟩)
    · have hfilt:Finset.univ.filter (fun j:Fin gs.length=>k ≤ j.val∧ n + j.val ∈ wa65 n gs out (j.val + 1)) = insert ⟨k,hk_lt⟩ (Finset.univ.filter (fun j:Fin gs.length=>k + 1 ≤ j.val∧ n + j.val ∈ wa65 n gs out (j.val + 1))):=by
       ext j;simp only [wmF,wmU,true_and,wmI,Fin.ext_iff];constructor
       · rintro ⟨hj1,hj2⟩
         by_cases hjk:j.val=k
         · exact Or.inl hjk
         · exact Or.inr ⟨by omega,hj2⟩
       · rintro (hjk | ⟨hj1,hj2⟩)
         · subst hjk;exact ⟨le_refl _,hmem⟩
         · exact ⟨by omega,hj2⟩
      have hnot_mem:⟨k,hk_lt⟩ ∉ Finset.univ.filter (fun j:Fin gs.length=>k + 1 ≤ j.val∧ n + j.val ∈ wa65 n gs out (j.val + 1)):=by simp
      rw [hfilt,Finset.card_insert_of_notMem hnot_mem,← hcnt];omega
  · simp only [hmem,↓reduceIte]
    have hnk_spec:=hneed (n + k) (by omega)
    have hnk_out:C_cur.output ≠ n + k:=fun h=>hmem (hnk_spec.mpr (Or.inl h))
    have hnk_in:∀ j (hj:j < C_cur.gates.length),k < j→ n + k ∉ C_cur.gates[j].inputs :=
     fun j hj hkj hm=>hmem (hnk_spec.mpr (Or.inr ⟨j,hkj,hj,hm⟩))
    have hdel_sz:(wa82 n C_cur k 0).gates.length=C_cur.gates.length - 1:=by simpa [Circuit.size] using wa63 C_cur k 0 hck_lt
    refine ih (wa82 n C_cur k 0) (by omega) (by omega) ?_
     (wa3f C_cur k 0 hf_c) (wa54 C_cur k 0 hnn_c)
     (fun x=>(wa34 C_cur k 0 hck_lt hnk_out hnk_in x).trans (hev x)) ?_ ?_
    · have htk:(C_cur.gates.take k).length=k:=by rw [List.length_take];omega
      simp only [wa82]
      rw [List.take_append_of_le_length (by rw [htk])]
      have htk1:List.take k (List.take (k + 1) C_cur.gates)=List.take k (List.take (k + 1) gs):=by rw [htake]
      simpa [List.take_take,Nat.min_eq_left (by omega:k ≤ k + 1)] using htk1
    · intro w hw;rw [wa48 n gs out k hk_lt];simp only [hmem,↓reduceIte]
      rw [hneed w (by omega)]
      have hsw_iff:∀ u,u ≠ n + k→ (wa70 n k 0 u=w↔ u=w):=by
       intro u hun;simp only [wa70]
       split_ifs <;> omega
      have htake_k:(C_cur.gates.take k).length=k:=by rw [List.length_take];omega
      constructor
      · rintro (hout_w | ⟨j,hj1,hj2,hj3⟩)
        · left;change wa70 n k 0 C_cur.output=w;exact (hsw_iff C_cur.output hnk_out).mpr hout_w
        · right
          refine ⟨j - 1,by omega,by omega,?_⟩
          have hg_j:(wa82 n C_cur k 0).gates[j - 1] = wa74 (wa70 n k 0) C_cur.gates[j]:=by
           simp only [wa82]
           rw [List.getElem_append_right (by rw [htake_k];omega)]
           simp only [htake_k];rw [List.getElem_map,List.getElem_drop]
           have hidx:k + 1 + (j - 1 - k)=j:=by omega
           simp only [hidx]
          rw [hg_j,wa74,List.mem_map]
          exact ⟨w,hj3,(hsw_iff w (by omega)).mpr rfl⟩
      · rintro (hout_w | ⟨j,hj1,hj2,hj3⟩)
        · left;change wa70 n k 0 C_cur.output=w at hout_w;exact (hsw_iff C_cur.output hnk_out).mp hout_w
        · right
          refine ⟨j + 1,by omega,by omega,?_⟩
          have hg_j:(wa82 n C_cur k 0).gates[j] = wa74 (wa70 n k 0) C_cur.gates[j + 1]:=by
           simp only [wa82]
           rw [List.getElem_append_right (by rw [htake_k];omega)]
           simp only [htake_k];rw [List.getElem_map,List.getElem_drop]
           have hidx:k + 1 + (j - k)=j + 1:=by omega
           simp only [hidx]
          rw [hg_j,wa74,List.mem_map] at hj3
          rcases hj3 with ⟨u,hu_mem,hu_eq⟩
          have hune:u ≠ n + k:=fun h=>hnk_in (j + 1) (by omega) (by omega) (h ▸ hu_mem)
          have hueq:u=w:=(hsw_iff u hune).mp hu_eq;exact hueq ▸ hu_mem
    · have hfilt:Finset.univ.filter (fun j:Fin gs.length=>k ≤ j.val∧ n + j.val ∈ wa65 n gs out (j.val + 1)) = Finset.univ.filter (fun j:Fin gs.length=>k + 1 ≤ j.val∧ n + j.val ∈ wa65 n gs out (j.val + 1)):=by
       ext j;simp only [wmF,wmU,true_and];constructor
       · rintro ⟨hj1,hj2⟩
         by_cases hjk:j.val=k
         · subst hjk;exact absurd hj2 hmem
         · exact ⟨by omega,hj2⟩
       · rintro ⟨hj1,hj2⟩;exact ⟨by omega,hj2⟩
      rw [hfilt,← hcnt,hdel_sz];omega
lemma wa55 (n:ℕ) (gs:List Gate) (out:ℕ) (hf:FanInTwo ⟨gs,out⟩) (hnn:∀ g ∈ gs,g.op ≠ GateOp.not) :
 let C_fin:=wa7e n gs out gs.length ⟨gs,out⟩
 FanInTwo C_fin ∧
 (∀ g ∈ C_fin.gates,g.op ≠ GateOp.not) ∧
 (∀ x,circuitFun n C_fin x=circuitFun n ⟨gs,out⟩ x) ∧
 C_fin.size=(Finset.univ.filter (fun j:Fin gs.length =>
  n + j.val ∈ wa65 n gs out (j.val + 1))).card:=by
 apply wa53 n gs out hf hnn gs.length ⟨gs,out⟩ (le_refl _) (le_refl _) rfl hf hnn
  (fun _=>rfl)
 · intro w _;rw [wa47 n gs out gs.length (le_refl _)];simp only [wm1];constructor
   · intro h;exact Or.inl h.symm
   · rintro (h | ⟨j,hj1,hj2,_⟩)
     · exact h.symm
     · omega
 · have hempty:Finset.univ.filter (fun j:Fin gs.length => gs.length ≤ j.val∧ n + j.val ∈ wa65 n gs out (j.val + 1))=∅ :=
    Finset.filter_eq_empty_iff.mpr fun j _ h=>absurd h.1 (Nat.not_le_of_lt j.isLt)
   rw [hempty,Finset.card_empty,Nat.sub_self]
lemma wa0 (n:ℕ) (C:Circuit) (fix:ℕ→ Option Bool) (hft:FanInTwo C) (out':ℕ) (hout_eq:(wa72 n fix 0 C.gates (wa79 n fix,[],[])).1.getD C.output (Sum.inl false)=Sum.inr out') (S_van:Finset ℕ) (hS_out:∀ q ∈ S_van,n + q ≠ C.output) (hS_step:∀ q ∈ S_van,∀ (q':ℕ) (hq':q' < C.gates.length),n + q ∈ (C.gates[q']'hq').inputs→ (∃ b,(wa72 n fix 0 C.gates (wa79 n fix,[],[])).1.getD (n + q') (Sum.inl false)=Sum.inl b)∨ q' ∈ S_van):∀ j q:ℕ,(hj:j < (wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2.length)→ (wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2[j]=q→ q ∈ S_van→ n + j ∉ wa65 n (wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.1 out' (j + 1):=by
 set full:=wa72 n fix 0 C.gates (wa79 n fix,[],[]);have hfull_props:=wa33 n fix 0 C.gates (wa79 n fix,[],[])
  (wa58 n fix) rfl (wa4a n fix) (fun _ h=>by cases h)
  (fun j₁ _ h₁ _=>by simp at h₁) (fun j hj=>by simp at hj)
  (fun g hg=>by have:=hft g hg;simpa using this) (fun _ h=>by cases h)
 have hvan_of_inr:∀ j0 q0,(hj0:j0 < full.2.2.length)→ full.2.2[j0]=q0→ q0 ∈ S_van→ ∀ q,q < C.gates.length→ full.1.getD (n + q) (Sum.inl false)=Sum.inr (n + j0)→ q ∈ S_van:=by
  intro j0 q0 hj0 hq0_eq hq0_mem q;have hinr_step:=wa26 n C fix hft j0 q0 hj0 hq0_eq
  induction q using Nat.strong_induction_on with
  | ind q ih =>
   intro hq_lt hq_inr
   rcases lt_trichotomy q q0 with hlt | rfl | hgt
   · exact absurd hq_inr (hinr_step.1 (n + q) (by omega))
   · exact hq0_mem
   · obtain ⟨a,ha_mem,ha_lt,ha_eq⟩:=hinr_step.2.2 q hgt hq_lt hq_inr
     by_cases ha_ge:a < n + q0
     · exact absurd ha_eq (hinr_step.1 a ha_ge)
     · have hq'_lt:a - n < C.gates.length:=by omega
       have heq_a:n + (a - n)=a:=by omega
       have hprev:=ih (a - n) (by omega) hq'_lt (by simpa [heq_a] using ha_eq)
       rcases hS_step (a - n) hprev q hq_lt (by simpa [heq_a] using ha_mem) with
        ⟨b,hbot⟩ | hq_in
       · rw [hbot] at hq_inr;cases hq_inr
       · exact hq_in
 have hd_ind:∀ d,∀ j0 q0,(hj0:j0 < full.2.2.length)→ full.2.2[j0]=q0→ q0 ∈ S_van→ n + j0 ∉ wa73 n full.2.1 out' d:=by
  intro d
  induction d with
  | zero =>
   intro j0 q0 hj0 hq0_eq hq0_mem hmem;have hinr_step:=wa26 n C fix hft j0 q0 hj0 hq0_eq;simp only [wa73,wm1] at hmem;have hout_eq':full.1.getD C.output (Sum.inl false)=Sum.inr (n + j0):=hout_eq.trans (congrArg Sum.inr hmem.symm)
   by_cases hout_lt:C.output < n + C.gates.length
   · have hout_ge:n + q0 ≤ C.output:=by
      by_contra hlt;exact hinr_step.1 C.output (by omega) hout_eq'
     have hq_out:C.output - n < C.gates.length:=by omega
     have heq_o:n + (C.output - n)=C.output:=by omega
     have hvin:=hvan_of_inr j0 q0 hj0 hq0_eq hq0_mem (C.output - n) hq_out (by simpa [heq_o] using hout_eq')
     exact hS_out (C.output - n) hvin heq_o
   · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by rw [hfull_props.1];omega)] at hout_eq'
     simp at hout_eq'
  | succ d ihd =>
   intro j0 q0 hj0 hq0_eq hq0_mem hmem;have hinr_step:=wa26 n C fix hft j0 q0 hj0 hq0_eq;simp only [wa73] at hmem;set k':=full.2.1.length - (d + 1)
   cases hk'_c:(full.2.1[k']? : Option Gate) with
   | none =>
    rw [hk'_c] at hmem;exact ihd j0 q0 hj0 hq0_eq hq0_mem hmem
   | some gk' =>
    rw [hk'_c] at hmem;have hk'_lt:k' < full.2.1.length:=(wgE.1 hk'_c).1
    by_cases hn_k':n + k' ∈ wa73 n full.2.1 out' d
    · simp only [hn_k',↓reduceIte,Finset.mem_union,List.mem_toFinset] at hmem
      rcases hmem with hm | hm_in
      · exact ihd j0 q0 hj0 hq0_eq hq0_mem hm
      · have hgk'_eq:full.2.1[k']=gk':=(wgE.1 hk'_c).2
        rw [← hgk'_eq] at hm_in
        obtain ⟨q',a,hq'_eq,hq'_lt,ha_mem,ha_lt,ha_eq⟩:=hinr_step.2.1 k' hk'_lt (n + j0) hm_in
        have hk'_src:k' < full.2.2.length:=by rw [hfull_props.2.1];exact hk'_lt
        have hq'_src:q'=full.2.2[k']:=(wgE.1 hq'_eq).2.symm
        have ha_ge:n + q0 ≤ a:=by by_contra hlt;exact hinr_step.1 a (by omega) ha_eq
        have hqa_lt:a - n < C.gates.length:=by omega
        have heqa:n + (a - n)=a:=by omega
        have hvan_a:=hvan_of_inr j0 q0 hj0 hq0_eq hq0_mem (a - n) hqa_lt (by simpa [heqa] using ha_eq)
        rcases hS_step (a - n) hvan_a q' hq'_lt (by simpa [heqa] using ha_mem) with
         ⟨b,hbot⟩ | hq'_van
        · have hj_w:=hfull_props.2.2.2.2.2.1 k' hk'_src;rw [← hq'_src,hbot] at hj_w;cases hj_w
        · exact ihd k' q' hk'_src hq'_src.symm hq'_van hn_k'
    · simp only [hn_k',↓reduceIte] at hmem;exact ihd j0 q0 hj0 hq0_eq hq0_mem hmem
 intro j q hj hq hmem;exact hd_ind (full.2.1.length - (j + 1)) j q hj hq hmem
def wa50 (n:ℕ) (C:Circuit) (fix:ℕ→ Option Bool):Circuit :=
 let full:=wa72 n fix 0 C.gates (wa79 n fix,[],[])
 match full.1.getD C.output (Sum.inl false) with
 | Sum.inl true=>⟨[⟨GateOp.and,[]⟩],n⟩
 | Sum.inl false=>⟨[⟨GateOp.or,[]⟩],n⟩
 | Sum.inr out'=>wa7e n full.2.1 out' full.2.1.length ⟨full.2.1,out'⟩
lemma wa25 (n:ℕ) (C:Circuit) (fix:ℕ→ Option Bool) (hf:FanInTwo C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output < n + C.gates.length) :
 let D:=wa50 n C fix
 FanInTwo D ∧
 (∀ g ∈ D.gates,g.op ≠ GateOp.not) ∧
 (∀ x:Fin n→ Bool,(∀ i:Fin n,∀ b,fix i.val=some b→ x i=b)→ (∀ q,q < C.gates.length→ ∀ b,fix (n + q)=some b→ wireVal C x (n + q)=b)→ circuitFun n D x=circuitFun n C x) ∧
 (∀ out',(wa72 n fix 0 C.gates (wa79 n fix,[],[])).1.getD C.output (Sum.inl false)=Sum.inr out'→ ∀ killed:Finset (Fin C.gates.length),(∀ q ∈ killed,q.val ∉ (wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2∨ ∃ j:Fin (wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2.length,(wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2[j]=q.val∧ n + j.val ∉ wa65 n (wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.1 out' (j.val + 1)) →
  D.size + killed.card ≤ C.size):=by
 dsimp only [wa50];set full:=wa72 n fix 0 C.gates (wa79 n fix,[],[]);have hfull_props:=wa33 n fix 0 C.gates (wa79 n fix,[],[])
  (wa58 n fix) rfl (wa4a n fix) (fun _ h=>by cases h)
  (fun j₁ _ h₁ _=>by simp at h₁) (fun j hj=>by simp at hj)
  (fun g hg=>by have:=hf g hg;simpa using this) (fun _ h=>by cases h)
 have hgs_bin:∀ g ∈ C.gates,(g.op=GateOp.and∨ g.op=GateOp.or)∧ g.inputs.length ≤ 2:=by
  intro g hg
  rcases hf g hg with ⟨hop,hlen⟩
  have hn':=hnn g hg;refine ⟨?_,hlen⟩
  rcases (by simpa using hop:g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hn'
 have hfull_nn:∀ g ∈ full.2.1,g.op ≠ GateOp.not :=
  wa35 n fix 0 C.gates (wa79 n fix,[],[]) hgs_bin (fun _ h=>by cases h)
 have hfull_ft:∀ out0,FanInTwo ⟨full.2.1,out0⟩:=by
  intro out0 g hg;have hg0:=hfull_props.2.2.2.2.2.2 g hg;refine ⟨?_,hg0.2⟩
  simpa using hg0.1
 cases hres_out:full.1.getD C.output (Sum.inl false) with
 | inl b =>
  cases b
  · refine ⟨?_,?_,?_,?_⟩
    · intro g hg;simp only [List.mem_singleton] at hg;subst hg;exact ⟨Or.inr (Or.inl rfl),by simp⟩
    · intro g hg;simp only [List.mem_singleton] at hg;subst hg;simp
    · intro x hfi hfg;have hev:=wa2c n C fix hf x hfi hfg C.output hout;change wa7b full.2.1 x (full.1.getD C.output (Sum.inl false))=wireVal C x C.output at hev;rw [hres_out] at hev;simp only [wa7b] at hev;rw [← wa14] at hev;rw [← hev,wa14];show wireVal ⟨[⟨GateOp.or,[]⟩],n⟩ x (n + 0)=false
      rw [wa5c ⟨[⟨GateOp.or,[]⟩],n⟩ x 0 (by simp)]
      simp [GateOp.eval]
    · intro out' hbot;cases hbot
  · refine ⟨?_,?_,?_,?_⟩
    · intro g hg;simp only [List.mem_singleton] at hg;subst hg;exact ⟨Or.inl rfl,by simp⟩
    · intro g hg;simp only [List.mem_singleton] at hg;subst hg;simp
    · intro x hfi hfg;have hev:=wa2c n C fix hf x hfi hfg C.output hout;change wa7b full.2.1 x (full.1.getD C.output (Sum.inl false))=wireVal C x C.output at hev;rw [hres_out] at hev;simp only [wa7b] at hev;rw [← wa14] at hev;rw [← hev,wa14];show wireVal ⟨[⟨GateOp.and,[]⟩],n⟩ x (n + 0)=true
      rw [wa5c ⟨[⟨GateOp.and,[]⟩],n⟩ x 0 (by simp)]
      simp [GateOp.eval]
    · intro out' hbot;cases hbot
 | inr out' =>
  have hpr:=wa55 n full.2.1 out' (hfull_ft out') hfull_nn;refine ⟨hpr.1,hpr.2.1,?_,?_⟩
  · intro x hfi hfg;rw [hpr.2.2.1 x];have hev:=wa2c n C fix hf x hfi hfg C.output hout;change wa7b full.2.1 x (full.1.getD C.output (Sum.inl false))=wireVal C x C.output at hev;rw [hres_out] at hev;exact hev
  · intro out'' hout'' killed hkilled
    rcases Sum.inr.inj hout'' with rfl
    rw [hpr.2.2.2]
    let f:Fin full.2.1.length→ Fin C.gates.length:=fun j =>
     ⟨full.2.2[j.val]'(by rw [hfull_props.2.1];exact j.isLt),by
      have hlt:=hfull_props.2.2.2.1 _ (List.getElem_mem (by rw [hfull_props.2.1];exact j.isLt))
      simpa using hlt⟩
    have hf_inj:Function.Injective f:=by
     intro j₁ j₂ hj
     by_contra hne
     rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
     · have hm:=hfull_props.2.2.2.2.1 j₁.val j₂.val (by rw [hfull_props.2.1];exact j₁.isLt)
        (by rw [hfull_props.2.1];exact j₂.isLt) hlt
       have hv:f j₁=f j₂:=hj;have hv':(f j₁).val=(f j₂).val:=congrArg Fin.val hv;dsimp only [f,full] at hv';omega
     · have hm:=hfull_props.2.2.2.2.1 j₂.val j₁.val (by rw [hfull_props.2.1];exact j₂.isLt)
        (by rw [hfull_props.2.1];exact j₁.isLt) hlt
       have hv:f j₁=f j₂:=hj;have hv':(f j₁).val=(f j₂).val:=congrArg Fin.val hv;dsimp only [f,full] at hv';omega
    let aliveIdx:=Finset.univ.filter (fun j:Fin full.2.1.length =>
     n + j.val ∈ wa65 n full.2.1 out' (j.val + 1))
    let kept:=aliveIdx.image f;have hcard:aliveIdx.card=kept.card:=(Finset.card_image_of_injective aliveIdx hf_inj).symm
    have hdisj:Disjoint kept killed:=by
     rw [Finset.disjoint_left];intro q hq_k hq_kill;simp only [kept,Finset.mem_image,aliveIdx,wmF,wmU,true_and] at hq_k
     rcases hq_k with ⟨j,hj_need,hj_eq⟩
     rcases hkilled q hq_kill with hnot | ⟨j',hj'_eq,hj'_not⟩
     · apply hnot;have hv':=congrArg Fin.val hj_eq;dsimp only [f,full] at hv'
       change (wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2[j.val]'(by rw [hfull_props.2.1];exact j.isLt)=q.val at hv'
       rw [← hv']
       exact List.getElem_mem (by rw [hfull_props.2.1];exact j.isLt)
     · have hv':=congrArg Fin.val hj_eq;dsimp only [f,full] at hv'
       have hq1:(wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2[j.val]'(by rw [hfull_props.2.1];exact j.isLt)=q.val:=hv'
       have hq2:(wa72 n fix 0 C.gates (wa79 n fix,[],[])).2.2[j'.val]'j'.isLt=q.val:=hj'_eq
       have hj_eq':j.val=j'.val:=by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have hm:=hfull_props.2.2.2.2.1 j.val j'.val (by rw [hfull_props.2.1];exact j.isLt)
           j'.isLt hlt
          rw [hq1,hq2] at hm;exact Nat.lt_irrefl q.val hm
        · have hm:=hfull_props.2.2.2.2.1 j'.val j.val j'.isLt
           (by rw [hfull_props.2.1];exact j.isLt) hlt
          rw [hq1,hq2] at hm;exact Nat.lt_irrefl q.val hm
       rw [hj_eq'] at hj_need;exact hj'_not hj_need
    have hunion:(kept ∪ killed).card ≤ Fintype.card (Fin C.gates.length) :=
     Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj,Fintype.card_fin] at hunion;show aliveIdx.card + killed.card ≤ C.size;rw [hcard];exact hunion
abbrev wa83 {n:ℕ} (u v:Fin n):Prop :=
 (u.val + 1) % n=v.val∨ (v.val + 1) % n=u.val
def oneHot {n:ℕ} (u:Fin n):Fin n→ Bool:=fun i=>decide (i=u)
def wa85 {n:ℕ} (u v:Fin n):Fin n→ Bool:=fun i=>decide (i=u∨ i=v)
def cycF (n:ℕ) (x:Fin n→ Bool):Bool :=
 decide (∃ i j:Fin n,(i.val + 1) % n=j.val∧ x i=true∧ x j=true)
def S1 (n:ℕ) (C:Circuit) (w:ℕ):Finset (Fin n) :=
 Finset.univ.filter fun u:Fin n=>wireVal C (oneHot u) w=true
def wDeg (C:Circuit) (w:ℕ):ℕ :=
 (C.gates.filter fun g=>decide (w ∈ g.inputs)).length
def D2 (n:ℕ) (C:Circuit):Finset (Fin n) :=
 Finset.univ.filter fun v:Fin n=>wDeg C v.val=2
def wa80 {n:ℕ} (hn:0 < n) (v:Fin n):Fin n :=
 ⟨(v.val + 1) % n,Nat.mod_lt _ hn⟩
def wa7d {n:ℕ} (hn:0 < n) (v:Fin n):Fin n :=
 ⟨(v.val + n - 1) % n,Nat.mod_lt _ hn⟩
lemma wa66 {n:ℕ} (hn:0 < n) (v:Fin n):(wa80 hn v).val=if v.val + 1=n then 0 else v.val + 1:=by
 simp only [wa80];have hv:=v.2
 split_ifs with h
 · rw [h,Nat.mod_self]
 · exact Nat.mod_eq_of_lt (by omega)
lemma wa5d {n:ℕ} (hn:0 < n) (v:Fin n):(wa7d hn v).val=if v.val=0 then n - 1 else v.val - 1:=by
 simp only [wa7d];have hv:=v.2
 split_ifs with h
 · rw [h,zero_add]
   exact Nat.mod_eq_of_lt (by omega)
 · have hlt:v.val - 1 < n:=by omega
   rw [show v.val + n - 1=(v.val - 1) + n by omega,Nat.add_mod_right,
    Nat.mod_eq_of_lt hlt]
lemma wa39 {n:ℕ} (hn:0 < n) (v:Fin n):wa80 hn (wa7d hn v)=v:=by{
apply Fin.ext;have hv:=v.2;simp only [wa66,wa5d]
by_cases h:v.val=0
{simp [h];omega}
{simp [h];split_ifs <;> omega}
}
lemma wa41 {n:ℕ} (hn:0 < n) (v:Fin n):wa7d hn (wa80 hn v)=v:=by{
apply Fin.ext;have hv:=v.2;simp only [wa5d,wa66]
by_cases h:v.val + 1=n
{simp [h];omega}
{simp [h]}
}
lemma wa5e {n:ℕ} (hn:0 < n) (v:Fin n):wa83 v (wa80 hn v) :=
 Or.inl rfl
lemma wa5f {n:ℕ} (hn:0 < n) (v:Fin n):wa83 v (wa7d hn v) :=
 Or.inr (congrArg Fin.val (wa39 hn v))
lemma wa29 {n:ℕ} (hn:5 ≤ n) (v:Fin n):wa80 (by omega) v ≠ wa7d (by omega) v:=by{
intro h;have h1:=congrArg Fin.val h;have hv:=v.2;rw [wa66,wa5d] at h1
split_ifs at h1 <;> omega
}
lemma wa16 {n:ℕ} (hn:5 ≤ n) (v u:Fin n):wa83 v u↔ u=wa80 (by omega) v∨ u=wa7d (by omega) v:=by
 constructor
 · rintro (h | h)
   · exact Or.inl (Fin.ext h.symm)
   · have hu:wa80 (by omega) u=v:=Fin.ext h
     have:=congrArg Fin.val (wa41 (by omega) u)
     rw [hu] at this;exact Or.inr (Fin.ext this.symm)
 · rintro (rfl | rfl)
   · exact wa5e (by omega) v
   · exact wa5f (by omega) v
lemma wa4f {n:ℕ} (hn:5 ≤ n) (v:Fin n):¬ wa83 v v:=by{
rintro (h | h) <;> have hv:=v.2
{
by_cases hlt:v.val + 1 < n
{rw [Nat.mod_eq_of_lt hlt] at h;omega}
{
have:v.val + 1=n:=by omega
rw [this,Nat.mod_self] at h;omega
}
}
{
by_cases hlt:v.val + 1 < n
{rw [Nat.mod_eq_of_lt hlt] at h;omega}
{
have:v.val + 1=n:=by omega
rw [this,Nat.mod_self] at h;omega
}
}
}
lemma wa12 {n:ℕ} (hn:5 ≤ n) {c c':Fin n} (h1:wa83 c' (wa80 (by omega) c)) (h2:wa83 c' (wa7d (by omega) c)):c'=c:=by
 rw [wa16 hn] at h1 h2;have hc:=c.2;have hc':=c'.2
 rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
  apply Fin.ext <;> have e1:=congrArg Fin.val h1 <;> have e2:=congrArg Fin.val h2 <;>
  simp only [wa66,wa5d] at e1 e2
 · split_ifs at e1 e2 <;> omega
 · have:c'.val=c.val:=by split_ifs at e1 e2 <;> omega
   exact this
 · split_ifs at e1 e2 <;> omega
 · split_ifs at e1 e2 <;> omega
lemma wa2a {n:ℕ} (hn:5 ≤ n) (u:Fin n):cycF n (oneHot u)=false:=by{
rw [cycF,decide_eq_false_iff_not];simp only [oneHot,not_exists,not_and,decide_eq_true_eq];intro i j hij hi hj;subst hi hj;exact wa4f hn _ (Or.inl hij)
}
lemma wa40 {n:ℕ} (hn:5 ≤ n) (u v:Fin n):cycF n (wa85 u v)=true↔ wa83 u v:=by{
simp only [cycF,wa85,decide_eq_true_eq];constructor
{
rintro ⟨i,j,hij,hi,hj⟩
rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
{exact absurd (Or.inl hij) (wa4f hn _)}
{exact Or.inl hij}
{exact Or.inr hij}
{exact absurd (Or.inl hij) (wa4f hn _)}
}
{
rintro (h | h)
{exact ⟨u,v,h,Or.inl rfl,Or.inr rfl⟩}
{exact ⟨v,u,h,Or.inr rfl,Or.inl rfl⟩}
}
}
lemma wa6 {n:ℕ} (hn:5 ≤ n) (K:Finset (Fin n)) (hcov:∀ u v:Fin n,wa83 u v→ u ∈ K∨ v ∈ K):(n + 1) / 2 ≤ K.card:=by
 have h1:∀ i:Fin n,1 ≤ (if i ∈ K then 1 else 0) + (if wa80 (by omega) i ∈ K then 1 else 0):=by
  intro i
  rcases hcov i (wa80 (by omega) i) (wa5e (by omega) i) with hi | hn'
  · simp [hi]
  · simp [hn']
 have hsum:=Finset.sum_le_sum (fun i (_:i ∈ Finset.univ)=>h1 i);rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hsum;rw [Finset.sum_add_distrib] at hsum
 have ha : ∑ i:Fin n,(if i ∈ K then 1 else 0)=K.card:=by simp [Finset.sum_ite_mem]
 have hb : ∑ i:Fin n,(if wa80 (by omega) i ∈ K then 1 else 0)=K.card:=by
  have hbij:(∑ i:Fin n,if wa80 (by omega) i ∈ K then 1 else 0) = ∑ i:Fin n,if i ∈ K then 1 else 0 :=
   Finset.sum_nbij' (wa80 (by omega)) (wa7d (by omega))
    (fun _ _=>wmU _) (fun _ _=>wmU _)
    (fun a _=>wa41 (by omega) a) (fun b _=>wa39 (by omega) b)
    (fun _ _=>rfl)
  rw [hbij];exact ha
 rw [ha,hb] at hsum;omega
lemma wa60 {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (q a b:ℕ) (hq:q < C.gates.length) (hg:C.gates[q]?=some ⟨GateOp.and,[a,b]⟩) (ha:a < n + q) (hb:b < n + q):wireVal C x (n + q)=(wireVal C x a && wireVal C x b):=by{
have hidx:C.gates[q]=⟨GateOp.and,[a,b]⟩:=(wgE.1 hg).2;rw [wa5c C x q hq,hidx];simp [GateOp.eval,ha,hb]
}
lemma wa6e {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (q a b:ℕ) (hq:q < C.gates.length) (hg:C.gates[q]?=some ⟨GateOp.or,[a,b]⟩) (ha:a < n + q) (hb:b < n + q):wireVal C x (n + q)=(wireVal C x a || wireVal C x b):=by{
have hidx:C.gates[q]=⟨GateOp.or,[a,b]⟩:=(wgE.1 hg).2;rw [wa5c C x q hq,hidx];simp [GateOp.eval,ha,hb]
}
lemma wa21 {n:ℕ} (C:Circuit) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q):∀ w:ℕ,@wireVal n C (fun _=>false) w=false:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  by_cases hwn:w < n
  · rw [wa52 C _ ⟨w,hwn⟩]
  · by_cases hwl:w < n + C.gates.length
    · have hq:w - n < C.size:=by simp [Circuit.size];omega
      obtain ⟨g,op,a,b,hg,rfl,hop,hin,_,ha,hb⟩:=hbin (w - n) hq
      have heq:n + (w - n)=w:=by omega
      have hg':C.gates[w - n]?=some ⟨g.op,[a,b]⟩:=by cases g;simp only at hin;subst hin;exact hg
      rw [← heq]
      rcases hop with hop | hop
      · rw [hop] at hg'
        rw [wa60 C _ (w - n) a b hq hg' ha hb,ih a (by omega),ih b (by omega)];rfl
      · rw [hop] at hg'
        rw [wa6e C _ (w - n) a b hq hg' ha hb,ih a (by omega),ih b (by omega)];rfl
    · exact wa6f C _ w (Nat.le_of_not_lt hwl)
lemma wa76 {n:ℕ} (C:Circuit) (v:Fin n):S1 n C v.val={v}:=by{
ext u;simp only [S1,wmF,wmU,true_and,wm1,wa52,oneHot,decide_eq_true_eq];exact eq_comm
}
lemma S1_or {n:ℕ} (C:Circuit) (q a b:ℕ) (hq:q < C.gates.length) (hg:C.gates[q]?=some ⟨GateOp.or,[a,b]⟩) (ha:a < n + q) (hb:b < n + q):S1 n C (n + q)=S1 n C a ∪ S1 n C b:=by{
ext u;simp only [S1,wmF,wmU,true_and,Finset.mem_union];rw [wa6e C (oneHot u) q a b hq hg ha hb,Bool.or_eq_true]
}
lemma wa17 (C:Circuit) (w:ℕ):wDeg C w=(Finset.univ.filter fun q:Fin C.size=>w ∈ (C.gates[q.val]).inputs).card:=by
 unfold wDeg;have h1:∀ l:List Gate,(l.filter fun g=>decide (w ∈ g.inputs)).length =
  (Finset.univ.filter fun q:Fin l.length=>w ∈ (l[q.val]).inputs).card:=by
  intro l
  induction l with
  | nil=>simp
  | cons g gs ih =>
   simp only [List.filter_cons,List.length_cons];rw [Finset.card_filter,Fin.sum_univ_succ];simp only [Fin.val_zero,List.getElem_cons_zero,Fin.val_succ,List.getElem_cons_succ];rw [← Finset.card_filter,← ih]
   by_cases hw:w ∈ g.inputs
   · simp [hw];omega
   · simp [hw]
 exact h1 C.gates
lemma wa2 (C:Circuit) (w:ℕ) (hpos:1 ≤ wDeg C w):∃ (q:ℕ) (_:q < C.size) (g:Gate),C.gates[q]?=some g∧ w ∈ g.inputs:=by{
rw [wa17] at hpos;obtain ⟨q,hq⟩:=Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hpos);rw [wmF] at hq;exact ⟨q.val,q.isLt,C.gates[q.val],wgE.2 ⟨q.isLt,rfl⟩,hq.2⟩
}
lemma wa3 (C:Circuit) (w q₁ q₂ : ℕ) (hdeg:wDeg C w=1) (g₁ g₂ : Gate) (hg₁ : C.gates[q₁]?=some g₁) (hw₁ : w ∈ g₁.inputs) (hg₂ : C.gates[q₂]?=some g₂) (hw₂ : w ∈ g₂.inputs):q₁=q₂:=by
 rw [wa17] at hdeg;obtain ⟨hq1,h1eq⟩:=wgE.1 hg₁;obtain ⟨hq2,h2eq⟩:=wgE.1 hg₂
 have hm1:⟨q₁,hq1⟩ ∈ Finset.univ.filter fun q:Fin C.size=>w ∈ (C.gates[q.val]).inputs :=
  wmF.2 ⟨wmU _,h1eq ▸ hw₁⟩
 have hm2:⟨q₂,hq2⟩ ∈ Finset.univ.filter fun q:Fin C.size=>w ∈ (C.gates[q.val]).inputs :=
  wmF.2 ⟨wmU _,h2eq ▸ hw₂⟩
 exact congrArg Fin.val (Finset.card_le_one.mp (le_of_eq hdeg) _ hm1 _ hm2)
lemma wa64 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (hsz:C.size=n + (n + 1) / 2 - 1):(∑ v:Fin n,wDeg C v.val) + (∑ q ∈ Finset.range (C.size - 1),wDeg C (n + q))=2 * C.size:=by
 have hlen_pos:0 < C.size:=by omega
 have hcount_gate:∀ (q:Fin C.size), (Finset.univ.filter fun w:Fin (n + C.size)=>w.val ∈ (C.gates[q.val]).inputs).card=2:=by
  intro q;obtain ⟨g,op,a,b,hg,_,_,hin,hne,ha,hb⟩:=hbin q.val q.isLt;have hidx:C.gates[q.val]=g:=(wgE.1 hg).2;have hset:(Finset.univ.filter fun w:Fin (n + C.size)=>w.val ∈ (C.gates[q.val]).inputs) =
   {⟨a,by omega⟩,⟨b,by omega⟩}:=by
   ext w;simp only [wmF,wmU,true_and,hidx,hin,List.mem_cons,List.not_mem_nil,or_false,wmI,wm1,Fin.ext_iff]
  rw [hset,Finset.card_pair (by intro h;exact hne (congrArg Fin.val h))]
 have hsum_all : ∑ w:Fin (n + C.size),wDeg C w.val=2 * C.size:=by
  have hrew:∀ w:Fin (n + C.size),wDeg C w.val = ∑ q:Fin C.size,if w.val ∈ (C.gates[q.val]).inputs then 1 else 0:=by
   intro w;rw [wa17,Finset.card_filter]
  simp_rw [hrew]
  rw [Finset.sum_comm]
  have hgate:∀ q:Fin C.size, (∑ w:Fin (n + C.size),if w.val ∈ (C.gates[q.val]).inputs then 1 else 0)=2:=by
   intro q;rw [← Finset.card_filter];exact hcount_gate q
  simp_rw [hgate,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_two]
  omega
 have hlast_zero:wDeg C (n + (C.size - 1))=0:=by
  by_contra hne
  obtain ⟨q,hq,g,hg,hin⟩:=wa2 C (n + (C.size - 1)) (Nat.pos_of_ne_zero hne);obtain ⟨g',_,a,b,hg',_,_,hin',_,ha,hb⟩:=hbin q hq;rw [hg] at hg';cases hg'
  rw [hin'] at hin
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
  rcases hin with h | h <;> omega
 have hsplit:(∑ w:Fin (n + C.size),wDeg C w.val) = (∑ v:Fin n,wDeg C v.val) + (∑ q ∈ Finset.range C.size,wDeg C (n + q)):=by
  rw [Fin.sum_univ_add];congr 1;simp only [Fin.val_natAdd];exact Fin.sum_univ_eq_sum_range (fun q=>wDeg C (n + q)) C.size
 have hrange : ∑ q ∈ Finset.range C.size,wDeg C (n + q) = (∑ q ∈ Finset.range (C.size - 1),wDeg C (n + q)) + wDeg C (n + (C.size - 1)):=by
  conv_lhs=>rw [show C.size=(C.size - 1) + 1 by omega,Finset.sum_range_succ]
 rw [hsum_all,hrange,hlast_zero,Nat.add_zero] at hsplit;exact hsplit.symm
lemma wa19 {n:ℕ} (C:Circuit) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (S_ch:Finset ℕ) (wstar:ℕ) (hleak:∀ (q:ℕ) (hq:q < C.size),n + q ∉ S_ch→ ∀ a ∈ (C.gates[q]'hq).inputs,a ∈ S_ch→ a=wstar) (x y:Fin n→ Bool) (hin_le:∀ i:Fin n,i.val ∉ S_ch→ x i=true→ y i=true) (hwstar:wireVal C x wstar=true→ wireVal C y wstar=true):∀ w,w ∉ S_ch→ wireVal C x w=true→ wireVal C y w=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hwS hwx
  by_cases hwn:w < n
  · rw [wa52 C x ⟨w,hwn⟩] at hwx;rw [wa52 C y ⟨w,hwn⟩];exact hin_le ⟨w,hwn⟩ hwS hwx
  · by_cases hwl:w < n + C.gates.length
    · have hq:w - n < C.size:=by simp [Circuit.size];omega
      have heq:n + (w - n)=w:=by omega
      have hwSn:n + (w - n) ∉ S_ch:=by rwa [heq]
      obtain ⟨g,op,a,b,hg,rfl,hop,hin,_,ha,hb⟩:=hbin (w - n) hq;have hidx:C.gates[w - n]=g:=(wgE.1 hg).2;have step_wire:∀ u,u < n + (w - n)→ u ∈ g.inputs →
       wireVal C x u=true→ wireVal C y u=true:=by
       intro u hu huin hux
       by_cases huS:u ∈ S_ch
       · have hwe:=hleak (w - n) hq hwSn u (hidx ▸ huin) huS;subst hwe;exact hwstar hux
       · exact ih u (by omega) huS hux
      have hg':C.gates[w - n]?=some ⟨g.op,[a,b]⟩:=by cases g;simp only at hin;subst hin;exact hg
      rw [← heq] at hwx ⊢
      rcases hop with hop | hop
      · rw [hop] at hg';rw [wa60 C x (w - n) a b hq hg' ha hb,Bool.and_eq_true] at hwx;rw [wa60 C y (w - n) a b hq hg' ha hb,Bool.and_eq_true]
        exact ⟨step_wire a ha (by rw [hin];simp) hwx.1,step_wire b hb (by rw [hin];simp) hwx.2⟩
      · rw [hop] at hg';rw [wa6e C x (w - n) a b hq hg' ha hb,Bool.or_eq_true] at hwx;rw [wa6e C y (w - n) a b hq hg' ha hb,Bool.or_eq_true]
        rcases hwx with h1 | h2
        · exact Or.inl (step_wire a ha (by rw [hin];simp) h1)
        · exact Or.inr (step_wire b hb (by rw [hin];simp) h2)
    · rw [wa6f C x w (Nat.le_of_not_lt hwl)] at hwx;cases hwx
lemma wa75 {n:ℕ} (C:Circuit) (hmin:IsMinimalCircuit n C) (w₁ w₂ : ℕ) (hlt:w₁ < w₂) (hbd:w₂ < n + C.size):∃ x:Fin n→ Bool,wireVal C x w₁ ≠ wireVal C x w₂:=by
 by_cases hw2n:w₂ < n
 · let i₁ : Fin n:=⟨w₁,by omega⟩
   let i₂ : Fin n:=⟨w₂,hw2n⟩;refine ⟨oneHot i₁,?_⟩
   rw [wa52 C _ i₁,wa52 C _ i₂];intro h
   have h1:decide (i₁=i₁)=decide (i₂=i₁):=by simpa [oneHot] using h
   have h2:i₂=i₁:=of_decide_eq_true (by simpa using h1.symm)
   have:=congrArg Fin.val h2;simp only [i₁,i₂] at this;omega
 · obtain ⟨q,rfl⟩:∃ q,w₂=n + q:=⟨w₂ - n,by omega⟩
   have hq:q < C.gates.length:=by simp [Circuit.size] at hbd;omega
   by_contra hall
   push Not at hall
   have heq:∀ x:Fin n→ Bool,wireVal C x (n + q)=wireVal C x w₁ :=
    fun x=>(hall x).symm
   have hce:circuitFun n (wa82 n C q w₁)=circuitFun n C :=
    funext fun x=>wa20 C q w₁ hq (by omega) x (heq x)
   have hsz:=hmin.2 (wa82 n C q w₁) (wa3f C q w₁ hmin.1) hce;rw [wa63 C q w₁ hq] at hsz;omega
lemma wa1e {n:ℕ} (C:Circuit) (hmin:IsMinimalCircuit n C) (hout:C.output=n + C.size - 1) (q:ℕ) (hq:q + 1 < C.size):1 ≤ wDeg C (n + q):=by
 by_contra h0
 have hz:wDeg C (n + q)=0:=by omega
 have hneq:C.output ≠ n + q:=by omega
 have hq_len:q < C.gates.length:=by simp [Circuit.size] at hq ⊢;omega
 have hunused:∀ (k:ℕ) (hk:k < C.gates.length),q < k→ n + q ∉ (C.gates[k]).inputs:=by
  intro k hk _ hmem
  have hpos:1 ≤ wDeg C (n + q):=by
   rw [wa17];exact Finset.card_pos.mpr ⟨⟨k,hk⟩,wmF.2 ⟨wmU _,hmem⟩⟩
  omega
 have hce:circuitFun n (wa82 n C q 0)=circuitFun n C :=
  funext fun x=>wa34 C q 0 hq_len hneq hunused x
 have hsz:=hmin.2 (wa82 n C q 0) (wa3f C q 0 hmin.1) hce;rw [wa63 C q 0 hq_len] at hsz;simp only [Circuit.size] at hq hsz;omega
lemma wa3d {n:ℕ} (hn:5 ≤ n) (v:Fin n):wa80 (by omega) (wa80 (by omega) v) ≠ v:=by{
intro h;have h1:=congrArg Fin.val h;have hv:=v.2;simp only [wa66] at h1
split_ifs at h1 <;> omega
}
lemma wa7c {n:ℕ} (hn:5 ≤ n) (C:Circuit) (hfun:circuitFun n C=cycF n) (hout:C.output=n + C.size - 1) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (hsz:C.size=n + (n + 1) / 2 - 1) (v:Fin n):1 ≤ wDeg C v.val:=by
 by_contra h0
 have hz:wDeg C v.val=0:=by omega
 have hno_read:∀ (q:ℕ) (hq:q < C.size),v.val ∉ (C.gates[q]'hq).inputs:=by
  intro q hq hvq
  have hpos:1 ≤ wDeg C v.val:=by
   rw [wa17];exact Finset.card_pos.mpr ⟨⟨q,hq⟩,wmF.2 ⟨wmU _,hvq⟩⟩
  omega
 let u:=wa80 (by omega) v
 have huv:wa83 v u:=wa5e (by omega) v
 have hleak:∀ (q:ℕ) (hq:q < C.size),n + q ∉ ({v.val} : Finset ℕ)→ ∀ a ∈ (C.gates[q]'hq).inputs,a ∈ ({v.val} : Finset ℕ)→ a=n + C.size:=by
  intro q hq _ a ha hs;rw [wm1] at hs;exact absurd (hs ▸ ha) (hno_read q hq)
 have hout_not:C.output ∉ ({v.val} : Finset ℕ):=by rw [wm1,hout];have:=v.2;omega
 have hmono:=wa19 C hbin {v.val} (n + C.size) hleak (wa85 v u) (oneHot u)
  (fun i hi hpi=>by
   rw [wm1] at hi;simp only [wa85,oneHot,decide_eq_true_eq] at hpi ⊢
   rcases hpi with rfl | rfl
   · exact absurd rfl hi
   · rfl)
  (fun hge=>by rw [wa6f C _ _ (by simp [Circuit.size])] at hge;cases hge)
  C.output hout_not
 have ht:wireVal C (wa85 v u) C.output=true:=by rw [← wa14,hfun,wa40 hn];exact huv
 have hf:=hmono ht;rw [← wa14,hfun,wa2a hn] at hf;cases hf
lemma wa13 {n:ℕ} (C:Circuit) (hmin:IsMinimalCircuit n C) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (q₁ q₂ w:ℕ) (hq1:q₁ < C.size) (hq2:q₂ < C.size) (hw1:w ∈ (C.gates[q₁]'hq1).inputs) (hw2:w ∈ (C.gates[q₂]'hq2).inputs) (hq12:n + q₁ ∈ (C.gates[q₂]'hq2).inputs):False:=by
 obtain ⟨g₁,op₁,a₁,b₁,hg₁,rfl,hop1,hin1,_,ha1,hb1⟩:=hbin q₁ hq1;obtain ⟨g₂,op₂,a₂,b₂,hg₂,rfl,hop2,hin2,_,ha2,hb2⟩:=hbin q₂ hq2;have hidx1:C.gates[q₁]=g₁:=(wgE.1 hg₁).2;have hidx2:C.gates[q₂]=g₂:=(wgE.1 hg₂).2
 have hg₁':C.gates[q₁]?=some ⟨g₁.op,[a₁,b₁]⟩:=by cases g₁;simp only at hin1;subst hin1;exact hg₁
 have hg₂':C.gates[q₂]?=some ⟨g₂.op,[a₂,b₂]⟩:=by cases g₂;simp only at hin2;subst hin2;exact hg₂
 rw [hidx1,hin1,List.mem_cons,List.mem_singleton] at hw1;rw [hidx2,hin2,List.mem_cons,List.mem_singleton] at hw2 hq12
 have hq1_lt_q2:q₁ < q₂:=by rcases hq12 with h | h <;> omega
 have hw_lt1:w < n + q₁:=by rcases hw1 with rfl | rfl <;> assumption
 have hother:∃ y,∀ x:Fin n→ Bool, wireVal C x (n + q₁)=g₁.op.eval [wireVal C x w,wireVal C x y]∧ wireVal C x (n + q₂)=g₂.op.eval [wireVal C x w,wireVal C x (n + q₁)]:=by
  have hcase1:∀ x:Fin n→ Bool,wireVal C x (n + q₁)=g₁.op.eval [wireVal C x w, wireVal C x (if a₁=w then b₁ else a₁)]:=by
   intro x
   rcases hop1 with h | h <;> rw [h] at hg₁' ⊢
   · rw [wa60 C x q₁ a₁ b₁ hq1 hg₁' ha1 hb1]
     rcases hw1 with rfl | rfl
     · simp [GateOp.eval]
     · simp [GateOp.eval,Bool.and_comm,‹a₁ ≠ w›]
   · rw [wa6e C x q₁ a₁ b₁ hq1 hg₁' ha1 hb1]
     rcases hw1 with rfl | rfl
     · simp [GateOp.eval]
     · simp [GateOp.eval,Bool.or_comm,‹a₁ ≠ w›]
  refine ⟨if a₁=w then b₁ else a₁,fun x=>⟨hcase1 x,?_⟩⟩
  rcases hop2 with h | h <;> rw [h] at hg₂' ⊢
  · rw [wa60 C x q₂ a₂ b₂ hq2 hg₂' ha2 hb2]
    rcases hw2 with rfl | rfl <;> rcases hq12 with hq | hq
    · exact absurd hq (by omega)
    · rw [hq];simp [GateOp.eval]
    · rw [hq];simp [GateOp.eval,Bool.and_comm]
    · exact absurd hq (by omega)
  · rw [wa6e C x q₂ a₂ b₂ hq2 hg₂' ha2 hb2]
    rcases hw2 with rfl | rfl <;> rcases hq12 with hq | hq
    · exact absurd hq (by omega)
    · rw [hq];simp [GateOp.eval]
    · rw [hq];simp [GateOp.eval,Bool.or_comm]
    · exact absurd hq (by omega)
 obtain ⟨y,hy⟩:=hother
 rcases hop1 with h1 | h1 <;> rcases hop2 with h2 | h2
 · obtain ⟨x,hx⟩:=wa75 C hmin (n + q₁) (n + q₂) (by omega) (by omega)
   apply hx;have h1x:=(hy x).1;have h2x:=(hy x).2;rw [h1] at h1x;rw [h2] at h2x;simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true] at h1x h2x;rw [h2x,h1x,← Bool.and_assoc,Bool.and_self]
 · obtain ⟨x,hx⟩:=wa75 C hmin w (n + q₂) (by omega) (by omega)
   apply hx;have h1x:=(hy x).1;have h2x:=(hy x).2;rw [h1] at h1x;rw [h2] at h2x;simp only [GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] at h1x h2x;rw [h2x,h1x]
   cases wireVal C x w <;> cases wireVal C x y <;> rfl
 · obtain ⟨x,hx⟩:=wa75 C hmin w (n + q₂) (by omega) (by omega)
   apply hx;have h1x:=(hy x).1;have h2x:=(hy x).2;rw [h1] at h1x;rw [h2] at h2x;simp only [GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] at h1x h2x;rw [h2x,h1x]
   cases wireVal C x w <;> cases wireVal C x y <;> rfl
 · obtain ⟨x,hx⟩:=wa75 C hmin (n + q₁) (n + q₂) (by omega) (by omega)
   apply hx;have h1x:=(hy x).1;have h2x:=(hy x).2;rw [h1] at h1x;rw [h2] at h2x;simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false] at h1x h2x;rw [h2x,h1x,← Bool.or_assoc,Bool.or_self]
def wa84 (v:ℕ) (bv:Bool):ℕ→ Option Bool :=
 fun w=>if w=v then some bv else none
lemma wa22 (op:GateOp) (a b:Sum Bool ℕ) (w u:ℕ) (h:(wa77 op a b w).1=Sum.inr u):a=Sum.inr u∨ b=Sum.inr u∨ u=w:=by{
rcases op with _ | _ | _ | _ | _ <;> cases a <;> cases b <;> simp only [wa77] at h
{cases ‹Bool› <;> cases ‹Bool› <;> simp at h}
{
cases ‹Bool›
{simp at h}
{simp at h;exact Or.inr (Or.inl (congrArg Sum.inr h))}
}
{
cases ‹Bool›
{simp at h}
{simp at h;exact Or.inl (congrArg Sum.inr h)}
}
{simp at h;exact Or.inr (Or.inr h.symm)}
{cases ‹Bool› <;> cases ‹Bool› <;> simp at h}
{
cases ‹Bool›
{simp at h;exact Or.inr (Or.inl (congrArg Sum.inr h))}
{simp at h}
}
{
cases ‹Bool›
{simp at h;exact Or.inl (congrArg Sum.inr h)}
{simp at h}
}
{simp at h;exact Or.inr (Or.inr h.symm)}
{cases h}
{cases h}
{cases h}
{cases h}
{cases h}
{cases h}
{cases h}
{cases h}
{cases h}
{cases h}
{cases h}
{cases h}
}
lemma wa3a (op:GateOp) (a b:Sum Bool ℕ) (w v:ℕ) (ha:a ≠ Sum.inr v) (hb:b ≠ Sum.inr v) (hv:v < w):(wa77 op a b w).1 ≠ Sum.inr v:=by{
intro h
rcases wa22 op a b w v h with h1 | h1 | h1
{exact ha h1}
{exact hb h1}
{omega}
}
lemma wa2b (n:ℕ) (st:List (Sum Bool ℕ) × List Gate) (g:Gate) (v:ℕ) (hv:v < n) (hst:∀ s ∈ st.1,s ≠ Sum.inr v):(wa7f n st g).1 ≠ Sum.inr v:=by
 have hlk:∀ a,(if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false) ≠ Sum.inr v:=by
  intro a
  split_ifs with ha
  · apply hst;rw [List.getD_eq_getElem?_getD,wgE.2 ⟨ha,rfl⟩,Option.getD_some]
    exact List.getElem_mem ha
  · simp
 rcases g with ⟨op,ins⟩
 rcases op with _ | _ | _ | _ | _ <;> rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩ <;>
  simp only [wa7f]
 all_goals try exact hlk a
 all_goals try exact wa3a _ _ _ _ _ (hlk a) (hlk b) (by omega)
 all_goals try (simp;done)
 · cases (if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false)
   · simp
   · simp;omega
 · cases (if a < st.1.length then st.1.getD a (Sum.inl false) else Sum.inl false)
   · simp
   · simp;omega
lemma wa1b (n:ℕ) (fix:ℕ→ Option Bool) (v:Fin n):∀ (k:ℕ) (gs:List Gate) (st:List (Sum Bool ℕ) × List Gate × List ℕ),(∀ s ∈ st.1,s ≠ Sum.inr v.val)→ ∀ s ∈ (wa72 n fix k gs st).1,s ≠ Sum.inr v.val:=by{
intro k gs
induction gs generalizing k with
| nil=>intro st hst;exact hst
| cons g gs ih =>{
intro st hst
have hstep:(wa6c n fix k (st.1,st.2.1) g).1 ≠ Sum.inr v.val:=by{
cases hfx:fix (n + k) with
| some c=>simp [wa6c,hfx]
| none =>{
simp only [wa6c,hfx];exact wa2b n (st.1,st.2.1) g v.val v.isLt hst
}
}
have hst':∀ s ∈ st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],s ≠ Sum.inr v.val:=by{
intro s hs;simp only [List.mem_append,List.mem_singleton] at hs
rcases hs with h | rfl
{exact hst s h}
{exact hstep}
}
cases h2:(wa6c n fix k (st.1,st.2.1) g).2 <;> simp only [wa72,h2]
{exact ih (k + 1) _ hst'}
{exact ih (k + 1) _ hst'}
}
}
lemma wa5 (n:ℕ) (fix:ℕ→ Option Bool) (v:Fin n):∀ (k:ℕ) (gs:List Gate) (st:List (Sum Bool ℕ) × List Gate × List ℕ),(∀ s ∈ st.1,s ≠ Sum.inr v.val)→ (∀ s ∈ st.1,match s with | Sum.inl _=>True | Sum.inr u=>u < n + st.2.1.length)→ (∀ g ∈ gs,(g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not)∧ g.inputs.length ≤ 2)→ (∀ (j:ℕ) (hj:j < st.2.1.length),∀ u ∈ st.2.1[j].inputs,u ≠ v.val∧ u < n + j)→ ∀ (j:ℕ) (hj:j < (wa72 n fix k gs st).2.1.length),∀ u ∈ (wa72 n fix k gs st).2.1[j].inputs,u ≠ v.val∧ u < n + j:=by
 intro k gs
 induction gs generalizing k with
 | nil=>intro st _ _ _ hg;exact hg
 | cons g gs ih =>
  intro st hst_nv hst_bd hgs hg_inv j hj u hu;have hg0:=hgs g List.mem_cons_self;have hgs':=fun g' hg'=>hgs g' (List.mem_cons_of_mem g hg')
  have hstep:(wa6c n fix k (st.1,st.2.1) g).1 ≠ Sum.inr v.val:=by
   cases hfx:fix (n + k) with
   | some c=>simp [wa6c,hfx]
   | none=>simp only [wa6c,hfx];exact wa2b n (st.1,st.2.1) g v.val v.isLt hst_nv
  have hst_nv':∀ s ∈ st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],s ≠ Sum.inr v.val:=by
   intro s hs;simp only [List.mem_append,List.mem_singleton] at hs
   rcases hs with h | rfl <;> [exact hst_nv s h;exact hstep]
  have hbd_step:=wa30 n fix k (st.1,st.2.1) g hg0 hst_bd
  cases h2:(wa6c n fix k (st.1,st.2.1) g).2 with
  | none =>
   simp only [wa72,h2] at hj hu ⊢
   have hst_bd':∀ s ∈ st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1], match s with | Sum.inl _=>True | Sum.inr w=>w < n + st.2.1.length:=by
    intro s hs;simp only [List.mem_append,List.mem_singleton] at hs
    rcases hs with h | rfl
    · exact hst_bd s h
    · simpa [h2] using hbd_step.1
   exact ih (k + 1) (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],st.2.1,st.2.2)
    hst_nv' hst_bd' hgs' hg_inv j hj u hu
  | some g' =>
   simp only [wa72,h2] at hj hu ⊢
   have hst_bd':∀ s ∈ st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1], match s with | Sum.inl _=>True | Sum.inr w=>w < n + (st.2.1 ++ [g']).length:=by
    intro s hs;simp only [List.mem_append,List.mem_singleton] at hs
    rcases hs with h | rfl
    · have h0:=hst_bd s h
      cases s with
      | inl _=>trivial
      | inr _=>simp only [List.length_append,List.length_singleton];omega
    · simpa [h2] using hbd_step.1
   have hg_inv':∀ (j0:ℕ) (hj0:j0 < (st.2.1 ++ [g']).length), ∀ w ∈ (st.2.1 ++ [g'])[j0].inputs,w ≠ v.val∧ w < n + j0:=by
    intro j0 hj0 w hw;simp only [List.length_append,List.length_singleton] at hj0
    by_cases hjlt:j0 < st.2.1.length
    · rw [List.getElem_append_left hjlt] at hw;exact hg_inv j0 hjlt w hw
    · have hjeq:j0=st.2.1.length:=by omega
      subst hjeq;simp only [List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero] at hw;obtain ⟨a,_,ha_lt,ha_eq⟩:=waa n fix k (st.1,st.2.1) g g' hg0 h2 w hw
      have hmem:st.1.getD a (Sum.inl false) ∈ st.1:=by
       rw [List.getD_eq_getElem?_getD,wgE.2 ⟨ha_lt,rfl⟩,Option.getD_some]
       exact List.getElem_mem ha_lt
      have h1:=hst_nv _ hmem;rw [ha_eq] at h1;have h2':=hst_bd _ hmem;rw [ha_eq] at h2';exact ⟨fun heq=>h1 (congrArg Sum.inr heq),h2'⟩
   exact ih (k + 1) (st.1 ++ [(wa6c n fix k (st.1,st.2.1) g).1],st.2.1 ++ [g'],st.2.2 ++ [k])
    hst_nv' hst_bd' hgs' hg_inv' j hj u hu
lemma wa56 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (bv:Bool) (hf:FanInTwo C) (_hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output < n + C.gates.length) (hfun:circuitFun n C=cycF n):∃ out':ℕ,(wa72 n (wa84 v.val bv) 0 C.gates (wa79 n (wa84 v.val bv),[],[])).1.getD C.output (Sum.inl false)=Sum.inr out':=by
 set fix:=wa84 v.val bv;set full:=wa72 n fix 0 C.gates (wa79 n fix,[],[])
 cases hres:full.1.getD C.output (Sum.inl false) with
 | inr out'=>exact ⟨out',rfl⟩
 | inl c =>
  exfalso
  have hev:∀ x:Fin n→ Bool,x v=bv→ cycF n x=c:=by
   intro x hxv;have h1:=wa2c n C fix hf x
    (fun i _ h=>by simp only [fix,wa84] at h;split_ifs at h with hi;have hvi:=Fin.ext hi;cases h;rw [hvi,hxv])
    (fun q _ _ h=>by simp only [fix,wa84] at h;split_ifs at h with hq;omega)
    C.output hout
   change wa7b full.2.1 x (full.1.getD C.output (Sum.inl false))=_ at h1;rw [hres,wa7b,← wa14,hfun] at h1;exact h1.symm
  cases c
  · let u₁:=wa80 (by omega) v
    let u₂:=wa80 (by omega) u₁
    have hu1_ne:u₁ ≠ v:=fun h=>by
     have h':=wa5e (by omega) v
     change wa83 v u₁ at h';rw [h] at h';exact wa4f hn v h'
    have hu2_ne:u₂ ≠ v:=wa3d hn v;let x:=Function.update (wa85 u₁ u₂) v bv
    have hx:=hev x (by simp [x])
    have hpx:cycF n x=true:=by
     simp only [cycF,decide_eq_true_eq];refine ⟨u₁,u₂,rfl,?_,?_⟩
     · simp [x,Function.update_of_ne hu1_ne,wa85]
     · simp [x,Function.update_of_ne hu2_ne,wa85]
    rw [hpx] at hx;cases hx
  · let x:=Function.update (fun _:Fin n=>false) v bv
    have hx:=hev x (by simp [x])
    have hno:cycF n x=false:=by
     simp only [cycF,decide_eq_false_iff_not,not_exists,not_and];intro i j hij hi hj
     have:i=v∧ j=v:=by
      constructor <;> by_contra hne <;>
       simp [x,Function.update_of_ne hne] at hi hj
     exact wa4f hn v (by rcases this with ⟨rfl,rfl⟩;exact Or.inl hij)
    rw [hno] at hx;cases hx
lemma wa69 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (bv:Bool) (hf:FanInTwo C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output < n + C.gates.length) (hfun:circuitFun n C=cycF n):circuitFun n (wa50 n C (wa84 v.val bv))=fun x=>cycF n (Function.update x v bv):=by
 set fix:=wa84 v.val bv;set full:=wa72 n fix 0 C.gates (wa79 n fix,[],[]);obtain ⟨out',hout'⟩:=wa56 hn C v bv hf hnn hout hfun
 have hinit_nv:∀ s ∈ wa79 n fix,s ≠ Sum.inr v.val:=by
  intro s hs;simp only [wa79,List.mem_ofFn] at hs;obtain ⟨i,rfl⟩:=hs
  by_cases hi:i=v
  · subst hi;simp [fix,wa84]
  · have:i.val ≠ v.val:=fun h=>hi (Fin.ext h);simp only [fix,wa84]
    split_ifs <;> simp [this]
 have hfull_nv:=wa1b n fix v 0 C.gates (wa79 n fix,[],[]) hinit_nv
 have hfull_gnv:∀ (j:ℕ) (hj:j < full.2.1.length),∀ u ∈ full.2.1[j].inputs, u ≠ v.val∧ u < n + j :=
  wa5 n fix v 0 C.gates (wa79 n fix,[],[]) hinit_nv
   (wa4a n fix) (fun g hg=>by have:=hf g hg;simpa using this) (fun j hj=>by simp at hj)
 have hout_nv:out' ≠ v.val:=by
  have hmem:full.1.getD C.output (Sum.inl false) ∈ full.1:=by
   by_cases ho:C.output < full.1.length
   · rw [List.getD_eq_getElem?_getD,wgE.2 ⟨ho,rfl⟩,Option.getD_some]
     exact List.getElem_mem ho
   · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_lt ho)] at hout'
     simp at hout'
  rw [hout'] at hmem;intro heq;exact hfull_nv _ hmem (congrArg Sum.inr heq)
 have hindep:∀ x:Fin n→ Bool,∀ w,w ≠ v.val→ wireVal ⟨full.2.1,out'⟩ x w=wireVal ⟨full.2.1,out'⟩ (Function.update x v bv) w:=by
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
   intro hwv
   by_cases hwn:w < n
   · rw [wa52 ⟨full.2.1,out'⟩ x ⟨w,hwn⟩,wa52 ⟨full.2.1,out'⟩ (Function.update x v bv) ⟨w,hwn⟩];exact (Function.update_of_ne (fun (h:(⟨w,hwn⟩:Fin n)=v)=>hwv (congrArg Fin.val h)) bv x).symm
   · by_cases hwl:w < n + full.2.1.length
     · have hj:w - n < full.2.1.length:=by omega
       have heq:n + (w - n)=w:=by omega
       rw [← heq,wa5c ⟨full.2.1,out'⟩ x (w - n) hj,wa5c ⟨full.2.1,out'⟩ (Function.update x v bv) (w - n) hj];congr 1;apply List.map_congr_left;intro u hu;obtain ⟨hunv,hult⟩:=hfull_gnv (w - n) hj u hu;simp only [hult,↓reduceIte]
       exact ih u (by omega) hunv
     · rw [wa6f ⟨full.2.1,out'⟩ x w (by simp;omega),wa6f ⟨full.2.1,out'⟩ (Function.update x v bv) w (by simp;omega)]
 have hfull_props:=wa33 n fix 0 C.gates (wa79 n fix,[],[])
  (wa58 n fix) rfl (wa4a n fix) (fun _ h=>by cases h)
  (fun j₁ _ h₁ _=>by simp at h₁) (fun j hj=>by simp at hj)
  (fun g hg=>by have:=hf g hg;simpa using this) (fun _ h=>by cases h)
 have hgs_bin:∀ g ∈ C.gates,(g.op=GateOp.and∨ g.op=GateOp.or)∧ g.inputs.length ≤ 2:=by
  intro g hg;rcases hf g hg with ⟨hop,hlen⟩;have hn':=hnn g hg
  refine ⟨?_,hlen⟩
  rcases (by simpa using hop:g.op=GateOp.and∨ g.op=GateOp.or∨ g.op=GateOp.not) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hn'
 have hfull_nn:∀ g ∈ full.2.1,g.op ≠ GateOp.not :=
  wa35 n fix 0 C.gates (wa79 n fix,[],[]) hgs_bin (fun _ h=>by cases h)
 have hfull_ft:FanInTwo ⟨full.2.1,out'⟩:=by intro g hg;have hg0:=hfull_props.2.2.2.2.2.2 g hg;exact ⟨by simpa using hg0.1,hg0.2⟩
 have hpr:=wa55 n full.2.1 out' hfull_ft hfull_nn;funext x
 have hD_eq:wa50 n C fix=wa7e n full.2.1 out' full.2.1.length ⟨full.2.1,out'⟩:=by simp only [wa50];change match full.1.getD C.output (Sum.inl false) with | _=>_=_;rw [hout']
 change circuitFun n (wa50 n C fix) x=_;rw [hD_eq,hpr.2.2.1 x,wa14,hindep x out' hout_nv,← wa14];have hev:=wa2c n C fix hf (Function.update x v bv)
  (fun i _ h=>by
   simp only [fix,wa84] at h
   split_ifs at h with hi
   · have hvi:i=v:=Fin.ext hi;cases h
     rw [hvi,Function.update_self])
  (fun q _ _ h=>by simp only [fix,wa84] at h;split_ifs at h with hq;omega)
  C.output hout
 change wa7b full.2.1 _ (full.1.getD C.output (Sum.inl false))=_ at hev;rw [hout',wa7b,← wa14,hfun] at hev;exact hev
lemma wab {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hf:FanInTwo C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (h_false_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p false))→ n + (n + 1) / 2 - 4 ≤ D.size):∀ out',(wa72 n (wa84 v.val false) 0 C.gates (wa79 n (wa84 v.val false),[],[])).1.getD C.output (Sum.inl false)=Sum.inr out'→ ∀ killed:Finset (Fin C.gates.length),(∀ q ∈ killed,q.val ∉ (wa72 n (wa84 v.val false) 0 C.gates (wa79 n (wa84 v.val false),[],[])).2.2∨ ∃ j:Fin (wa72 n (wa84 v.val false) 0 C.gates (wa79 n (wa84 v.val false),[],[])).2.2.length,(wa72 n (wa84 v.val false) 0 C.gates (wa79 n (wa84 v.val false),[],[])).2.2[j]=q.val∧ n + j.val ∉ wa65 n (wa72 n (wa84 v.val false) 0 C.gates (wa79 n (wa84 v.val false),[],[])).2.1 out' (j.val + 1))→ killed.card ≤ 3:=by
 have hlen_pos:0 < C.gates.length:=by simp [Circuit.size] at hsz;omega
 have hsp:=wa25 n C (wa84 v.val false) hf hnn (by simp [Circuit.size] at hout ⊢;omega)
 have hfeq:=wa69 hn C v false hf hnn (by simp [Circuit.size] at hout ⊢;omega) hfun
 have hlo:=h_false_lo v (wa50 n C (wa84 v.val false)) hsp.1 hfeq;intro out' hout' killed hkilled;have hbd:=hsp.2.2.2 out' hout' killed hkilled;omega
lemma wa10 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hf:FanInTwo C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (h_true_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p true))→ n + (n + 1) / 2 - 5 ≤ D.size):∀ out',(wa72 n (wa84 v.val true) 0 C.gates (wa79 n (wa84 v.val true),[],[])).1.getD C.output (Sum.inl false)=Sum.inr out'→ ∀ killed:Finset (Fin C.gates.length),(∀ q ∈ killed,q.val ∉ (wa72 n (wa84 v.val true) 0 C.gates (wa79 n (wa84 v.val true),[],[])).2.2∨ ∃ j:Fin (wa72 n (wa84 v.val true) 0 C.gates (wa79 n (wa84 v.val true),[],[])).2.2.length,(wa72 n (wa84 v.val true) 0 C.gates (wa79 n (wa84 v.val true),[],[])).2.2[j]=q.val∧ n + j.val ∉ wa65 n (wa72 n (wa84 v.val true) 0 C.gates (wa79 n (wa84 v.val true),[],[])).2.1 out' (j.val + 1))→ killed.card ≤ 4:=by
 have hlen_pos:0 < C.gates.length:=by simp [Circuit.size] at hsz;omega
 have hsp:=wa25 n C (wa84 v.val true) hf hnn (by simp [Circuit.size] at hout ⊢;omega)
 have hfeq:=wa69 hn C v true hf hnn (by simp [Circuit.size] at hout ⊢;omega) hfun
 have hlo:=h_true_lo v (wa50 n C (wa84 v.val true)) hsp.1 hfeq;intro out' hout' killed hkilled;have hbd:=hsp.2.2.2 out' hout' killed hkilled;omega
def wa81 (n:ℕ) (C:Circuit) (v:Fin n) (bv:Bool):List (Sum Bool ℕ) × List Gate × List ℕ :=
 wa72 n (wa84 v.val bv) 0 C.gates (wa79 n (wa84 v.val bv),[],[])
def wa86 (n:ℕ) (C:Circuit) (v:Fin n) (bv:Bool):Finset (Fin C.gates.length) :=
 Finset.univ.filter fun q:Fin C.gates.length =>
  (wa81 n C v bv).1.getD (n + q.val) (Sum.inl false)=Sum.inl bv
lemma wa38 (n:ℕ) (C:Circuit) (v:Fin n) (bv:Bool):(wa81 n C v bv).1.getD v.val (Sum.inl false)=Sum.inl bv:=by{
unfold wa81
have hlt:v.val < (wa79 n (wa84 v.val bv)).length:=by rw [wa58];exact v.2
rw [waf n (wa84 v.val bv) 0 C.gates _ v.val hlt];rw [List.getD_eq_getElem?_getD,wgE.2 ⟨hlt,rfl⟩,Option.getD_some]
simp [wa79,wa84]
}
lemma wa4d {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (bv:Bool) (hf:FanInTwo C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (q:Fin C.gates.length) (hq:q ∈ wa86 n C v bv):q.val ∉ (wa81 n C v bv).2.2∧ q.val + 1 < C.size:=by
 have hfull_props:=wa33 n (wa84 v.val bv) 0 C.gates (wa79 n (wa84 v.val bv),[],[])
  (wa58 n _) rfl (wa4a n _) (fun _ h=>by cases h)
  (fun j₁ _ h₁ _=>by simp at h₁) (fun j hj=>by simp at hj)
  (fun g hg=>by have:=hf g hg;simpa using this) (fun _ h=>by cases h)
 have hmem:(wa81 n C v bv).1.getD (n + q.val) (Sum.inl false)=Sum.inl bv :=
  (wmF.1 hq).2
 constructor
 · intro hq_in
   obtain ⟨j,hj,hjeq⟩:=List.getElem_of_mem hq_in
   have hs:=hfull_props.2.2.2.2.2.1 j hj;change (wa81 n C v bv).1.getD (n + (wa81 n C v bv).2.2[j]) (Sum.inl false)=Sum.inr (n + j) at hs;rw [hjeq,hmem] at hs;cases hs
 · have hbd_out:C.output < n + C.gates.length:=by simp [Circuit.size] at hout hsz ⊢;omega
   obtain ⟨out',hout'⟩:=wa56 hn C v bv hf hnn hbd_out hfun;change (wa81 n C v bv).1.getD C.output (Sum.inl false)=Sum.inr out' at hout'
   have hneq:n + q.val ≠ C.output:=fun heq=>by rw [heq,hout'] at hmem;cases hmem
   have hq_lt:=q.isLt;simp only [Circuit.size] at hout ⊢;omega
lemma wa27 {n:ℕ} (C:Circuit) (v:Fin n) (bv:Bool) (hf:FanInTwo C) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (e:Fin C.gates.length) (a:ℕ) (ha_in:a ∈ (C.gates[e.val]).inputs) (ha_bv:(wa81 n C v bv).1.getD a (Sum.inl false)=Sum.inl bv):e.val ∉ (wa81 n C v bv).2.2∧ (∀ b ∈ (C.gates[e.val]).inputs,b ≠ a→ ((C.gates[e.val]).op=GateOp.and∧ bv=false)∨ ((C.gates[e.val]).op=GateOp.or∧ bv=true)∨ (wa81 n C v bv).1.getD b (Sum.inl false)=Sum.inl bv→ e ∈ wa86 n C v bv)∧ (e ∉ wa86 n C v bv→ ∀ b ∈ (C.gates[e.val]).inputs,b ≠ a→ (wa81 n C v bv).1.getD b (Sum.inl false) ≠ Sum.inl bv):=by
 obtain ⟨g,op,x₁,x₂,hg,rfl,hop,hin,hne,hx1,hx2⟩:=hbin e.val e.isLt;have hidx:C.gates[e.val]=g:=(wgE.1 hg).2;have hat:=wa2e n C (wa84 v.val bv) hf e.val e.isLt;set st_e:=wa72 n (wa84 v.val bv) 0 (C.gates.take e.val) (wa79 n (wa84 v.val bv),[],[]);have hst_len:st_e.1.length=n + e.val:=hat.1
 have ha_lt:a < n + e.val:=by
  simp only [hidx,hin,List.mem_cons,List.mem_nil_iff,or_false] at ha_in
  rcases ha_in with rfl | rfl <;> assumption
 have hx1_eq:(wa81 n C v bv).1.getD x₁ (Sum.inl false)=st_e.1.getD x₁ (Sum.inl false) :=
  hat.2.2.1 x₁ hx1
 have hx2_eq:(wa81 n C v bv).1.getD x₂ (Sum.inl false)=st_e.1.getD x₂ (Sum.inl false) :=
  hat.2.2.1 x₂ hx2
 have hfx_e:wa84 v.val bv (n + e.val)=none:=by simp [wa84];omega
 have hres_e:(wa81 n C v bv).1.getD (n + e.val) (Sum.inl false) = (wa7f n (st_e.1,st_e.2.1) (C.gates[e.val])).1:=by
  unfold wa81;rw [hat.2.1];simp [wa6c,hfx_e]
 have hlk1:(if x₁ < st_e.1.length then st_e.1.getD x₁ (Sum.inl false) else Sum.inl false) = (wa81 n C v bv).1.getD x₁ (Sum.inl false):=by
  simp only [hst_len,hx1,↓reduceIte,hx1_eq]
 have hlk2:(if x₂ < st_e.1.length then st_e.1.getD x₂ (Sum.inl false) else Sum.inl false) = (wa81 n C v bv).1.getD x₂ (Sum.inl false):=by
  simp only [hst_len,hx2,↓reduceIte,hx2_eq]
 have hpair_none:(wa6c n (wa84 v.val bv) e.val (st_e.1,st_e.2.1) (C.gates[e.val])).2=none:=by
  simp only [wa6c,hfx_e,wa7f,hidx,hin]
  simp only [hidx,hin,List.mem_cons,List.mem_nil_iff,or_false] at ha_in
  rcases ha_in with rfl | rfl
  · rcases hop with h | h <;> simp only [h,hlk1,hlk2,ha_bv] <;>
     cases bv <;> cases (wa81 n C v _).1.getD x₂ (Sum.inl false) with
     | inl c=>cases c <;> simp [wa77]
     | inr _=>simp [wa77]
  · rcases hop with h | h <;> simp only [h,hlk1,hlk2,ha_bv] <;>
     cases bv <;> cases (wa81 n C v _).1.getD x₁ (Sum.inl false) with
     | inl c=>cases c <;> simp [wa77]
     | inr _=>simp [wa77]
 have he_not_in:e.val ∉ (wa81 n C v bv).2.2:=hat.2.2.2.1 hpair_none;refine ⟨he_not_in,?_,?_⟩
 · intro b hb hba hcond;dsimp only [wa86];rw [wmF];refine ⟨wmU _,?_⟩
   rw [hres_e];simp only [wa7f,hidx,hin];simp only [hidx,hin,List.mem_cons,List.mem_nil_iff,or_false] at ha_in hb
   rcases ha_in with rfl | rfl <;> rcases hb with rfl | rfl
   · exact absurd rfl hba
   · rcases hcond with ⟨hop',hbv⟩ | ⟨hop',hbv⟩ | hbv_eq
     · rw [hidx] at hop';subst hbv;simp only [hop',hlk1,hlk2,ha_bv,wa77]
     · rw [hidx] at hop';subst hbv;simp only [hop',hlk1,hlk2,ha_bv,wa77]
     · rcases hop with h | h <;> simp only [h,hlk1,hlk2,ha_bv,hbv_eq] <;> cases bv <;> simp [wa77]
   · rcases hcond with ⟨hop',hbv⟩ | ⟨hop',hbv⟩ | hbv_eq
     · rw [hidx] at hop';subst hbv
       cases hvb:(wa81 n C v false).1.getD b (Sum.inl false) with
       | inl c=>cases c <;> simp only [hop',hlk1,hlk2,ha_bv,hvb,wa77]
       | inr _=>simp only [hop',hlk1,hlk2,ha_bv,hvb,wa77]
     · rw [hidx] at hop';subst hbv
       cases hvb:(wa81 n C v true).1.getD b (Sum.inl false) with
       | inl c=>cases c <;> simp only [hop',hlk1,hlk2,ha_bv,hvb,wa77]
       | inr _=>simp only [hop',hlk1,hlk2,ha_bv,hvb,wa77]
     · rcases hop with h | h <;> simp only [h,hlk1,hlk2,ha_bv,hbv_eq] <;> cases bv <;> simp [wa77]
   · exact absurd rfl hba
 · intro hnot b hb hba hbe;apply hnot;dsimp only [wa86];rw [wmF];refine ⟨wmU _,?_⟩
   rw [hres_e];simp only [wa7f,hidx,hin];simp only [hidx,hin,List.mem_cons,List.mem_nil_iff,or_false] at ha_in hb
   rcases ha_in with rfl | rfl <;> rcases hb with rfl | rfl
   · exact absurd rfl hba
   · rcases hop with h | h <;> simp only [h,hlk1,hlk2,ha_bv,hbe] <;> cases bv <;> simp [wa77]
   · rcases hop with h | h <;> simp only [h,hlk1,hlk2,ha_bv,hbe] <;> cases bv <;> simp [wa77]
   · exact absurd rfl hba
lemma wa42 {n:ℕ} (C:Circuit) (v:Fin n) (hf:FanInTwo C) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (q:Fin C.gates.length) (hqv:v.val ∈ (C.gates[q.val]).inputs):q.val ∉ (wa81 n C v false).2.2∧ ((C.gates[q.val]).op=GateOp.and→ q ∈ wa86 n C v false):=by
 have hc:=wa27 C v false hf hbin q v.val hqv (wa38 n C v false);refine ⟨hc.1,fun hop=>?_⟩
 obtain ⟨g,op,a,b,hg,rfl,_,hin,hne,_,_⟩:=hbin q.val q.isLt;have hidx:C.gates[q.val]=g:=(wgE.1 hg).2;rw [hidx,hin,List.mem_cons,List.mem_singleton] at hqv
 rcases hqv with rfl | rfl
 · exact hc.2.1 b (by rw [hidx,hin];simp) hne.symm (Or.inl ⟨hop,rfl⟩)
 · exact hc.2.1 a (by rw [hidx,hin];simp) hne (Or.inl ⟨hop,rfl⟩)
lemma wa3e {n:ℕ} (C:Circuit) (v:Fin n) (hf:FanInTwo C) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (q:Fin C.gates.length) (hqv:v.val ∈ (C.gates[q.val]).inputs):q.val ∉ (wa81 n C v true).2.2∧ ((C.gates[q.val]).op=GateOp.or→ q ∈ wa86 n C v true):=by
 have hc:=wa27 C v true hf hbin q v.val hqv (wa38 n C v true);refine ⟨hc.1,fun hop=>?_⟩
 obtain ⟨g,op,a,b,hg,rfl,_,hin,hne,_,_⟩:=hbin q.val q.isLt;have hidx:C.gates[q.val]=g:=(wgE.1 hg).2;rw [hidx,hin,List.mem_cons,List.mem_singleton] at hqv
 rcases hqv with rfl | rfl
 · exact hc.2.1 b (by rw [hidx,hin];simp) hne.symm (Or.inr (Or.inl ⟨hop,rfl⟩))
 · exact hc.2.1 a (by rw [hidx,hin];simp) hne (Or.inr (Or.inl ⟨hop,rfl⟩))
lemma wa8 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hf:FanInTwo C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (h_false_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p false))→ n + (n + 1) / 2 - 4 ≤ D.size) (S:Finset (Fin C.gates.length)) (hS:∀ q ∈ S,q.val ∉ (wa81 n C v false).2.2):S.card ≤ 3:=by
 have hbd_out:C.output < n + C.gates.length:=by simp [Circuit.size] at hout hsz ⊢;omega
 obtain ⟨out',hout'⟩:=wa56 hn C v false hf hnn hbd_out hfun;exact wab hn C v hf hnn hout hsz hfun h_false_lo out' hout' S
  (fun q hq=>Or.inl (hS q hq))
lemma wac {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hf:FanInTwo C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (h_true_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p true))→ n + (n + 1) / 2 - 5 ≤ D.size) (S:Finset (Fin C.gates.length)) (hS:∀ q ∈ S,q.val ∉ (wa81 n C v true).2.2):S.card ≤ 4:=by
 have hbd_out:C.output < n + C.gates.length:=by simp [Circuit.size] at hout hsz ⊢;omega
 obtain ⟨out',hout'⟩:=wa56 hn C v true hf hnn hbd_out hfun;exact wa10 hn C v hf hnn hout hsz hfun h_true_lo out' hout' S
  (fun q hq=>Or.inl (hS q hq))
lemma wa3b {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (bv:Bool) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (q:Fin C.gates.length) (hq:q ∈ wa86 n C v bv):∃ e:Fin C.gates.length,q.val < e.val∧ n + q.val ∈ (C.gates[e.val]).inputs∧ e.val ∉ (wa81 n C v bv).2.2:=by
 have hvan:=wa4d hn C v bv hmin.1 hnn hout hsz hfun q hq;have hdeg:=wa1e C hmin hout q.val hvan.2;obtain ⟨e,he,g,hg,hin⟩:=wa2 C (n + q.val) hdeg;obtain ⟨g',_,a,b,hg',_,_,hin',_,ha,hb⟩:=hbin e he;rw [hg] at hg';cases hg';have hidx:C.gates[e]=g:=(wgE.1 hg).2
 have hlt:q.val < e:=by
  rw [hin'] at hin
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
  rcases hin with h | h <;> omega
 have hmem_bv:(wa81 n C v bv).1.getD (n + q.val) (Sum.inl false)=Sum.inl bv :=
  (wmF.1 hq).2
 have hc:=wa27 C v bv hmin.1 hbin ⟨e,he⟩ (n + q.val) (hidx ▸ hin) hmem_bv;exact ⟨⟨e,he⟩,hlt,hidx ▸ hin,hc.1⟩
lemma wa7 {n:ℕ} (C:Circuit) (v:Fin n) (bv:Bool) (hf:FanInTwo C) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (q₁ q₂ e:Fin C.gates.length) (hne:q₁ ≠ q₂) (hq1:q₁ ∈ wa86 n C v bv) (hq2:q₂ ∈ wa86 n C v bv) (he1:n + q₁.val ∈ (C.gates[e.val]).inputs) (he2:n + q₂.val ∈ (C.gates[e.val]).inputs):e ∈ wa86 n C v bv:=by
 have hbv1:(wa81 n C v bv).1.getD (n + q₁.val) (Sum.inl false)=Sum.inl bv :=
  (wmF.1 hq1).2
 have hbv2:(wa81 n C v bv).1.getD (n + q₂.val) (Sum.inl false)=Sum.inl bv :=
  (wmF.1 hq2).2
 have hc:=wa27 C v bv hf hbin e (n + q₁.val) he1 hbv1
 have hnq_ne:n + q₂.val ≠ n + q₁.val:=fun h=>hne (Fin.ext (by omega))
 exact hc.2.1 (n + q₂.val) he2 hnq_ne (Or.inr (Or.inr hbv2))
lemma wa4 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (h_true_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p true))→ n + (n + 1) / 2 - 5 ≤ D.size):(wa86 n C v true).card ≤ 3:=by
 by_contra hgt
 have h4:4 ≤ (wa86 n C v true).card:=by omega
 have hne:(wa86 n C v true).Nonempty:=Finset.card_pos.mp (by omega)
 let q_max:=(wa86 n C v true).max' hne;have hqm_mem:q_max ∈ wa86 n C v true:=Finset.max'_mem _ hne;obtain ⟨e,hlt,_,he_nv⟩:=wa3b hn C v true hmin hnn hout hsz hfun hbin q_max hqm_mem
 have he_not:e ∉ wa86 n C v true:=fun h=>by
  have hle:=Finset.le_max' (wa86 n C v true) e h;change e.val ≤ q_max.val at hle;omega
 have hcard:(insert e (wa86 n C v true)).card=(wa86 n C v true).card + 1 :=
  Finset.card_insert_of_notMem he_not
 have hle4:=wac hn C v hmin.1 hnn hout hsz hfun h_true_lo
  (insert e (wa86 n C v true)) (fun q hq=>by
   rcases wmI.1 hq with rfl | hq
   · exact he_nv
   · exact (wa4d hn C v true hmin.1 hnn hout hsz hfun q hq).1)
 omega
def wa78 (op:GateOp) (g:Gate):Bool :=
 match op,g.op with
 | GateOp.and,GateOp.and=>true
 | GateOp.or,GateOp.or=>true
 | GateOp.not,GateOp.not=>true
 | _,_=>false
lemma wa5a (g:Gate):wa78 GateOp.and g=true↔ g.op=GateOp.and:=by{
rcases g with ⟨op,ins⟩
cases op <;> simp [wa78]
}
lemma wa61 (g:Gate):wa78 GateOp.or g=true↔ g.op=GateOp.or:=by{
rcases g with ⟨op,ins⟩
cases op <;> simp [wa78]
}
lemma wa6d {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (h_false_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p false))→ n + (n + 1) / 2 - 4 ≤ D.size):(Finset.univ.filter fun q:Fin C.gates.length=>v.val ∈ (C.gates[q.val]).inputs∧ wa78 GateOp.and (C.gates[q.val])=true).card ≤ 1:=by
 rw [Finset.card_le_one];intro q₁ hq1 q₂ hq2
 by_contra hne
 have h1:=wmF.1 hq1;have h2:=wmF.1 hq2;have hT1:=(wa42 C v hmin.1 hbin q₁ h1.2.1).2 ((wa5a _).mp h1.2.2);have hT2:=(wa42 C v hmin.1 hbin q₂ h2.2.1).2 ((wa5a _).mp h2.2.2);obtain ⟨e₁,hlt1,hein1,he1_nv⟩:=wa3b hn C v false hmin hnn hout hsz hfun hbin q₁ hT1;obtain ⟨e₂,hlt2,hein2,he2_nv⟩:=wa3b hn C v false hmin hnn hout hsz hfun hbin q₂ hT2
 have he1_neq_q2:e₁ ≠ q₂:=fun h=>by
  subst h;exact wa13 C hmin hbin q₁.val e₁.val v.val q₁.isLt e₁.isLt h1.2.1 h2.2.1 hein1
 have he2_neq_q1:e₂ ≠ q₁:=fun h=>by
  subst h;exact wa13 C hmin hbin q₂.val e₂.val v.val q₂.isLt e₂.isLt h2.2.1 h1.2.1 hein2
 by_cases hT_in:e₁ ∈ wa86 n C v false∨ e₂ ∈ wa86 n C v false
 · let T':=wa86 n C v false
   have h3:3 ≤ T'.card:=by
    rcases hT_in with he1T | he2T
    · have hsub : {q₁,q₂,e₁} ⊆ T':=by
       intro x hx;simp only [wmI,wm1] at hx
       rcases hx with rfl | rfl | rfl <;> assumption
      have hc3:({q₁,q₂,e₁} : Finset (Fin C.gates.length)).card=3:=by
       rw [Finset.card_insert_of_notMem,Finset.card_pair he1_neq_q2.symm];simp only [wmI,wm1]
       rintro (h | h);exact hne h;exact absurd h (by intro hh;subst hh;omega)
      exact hc3 ▸ Finset.card_le_card hsub
    · have hsub : {q₁,q₂,e₂} ⊆ T':=by
       intro x hx;simp only [wmI,wm1] at hx
       rcases hx with rfl | rfl | rfl <;> assumption
      have hc3:({q₁,q₂,e₂} : Finset (Fin C.gates.length)).card=3:=by
       rw [Finset.card_insert_of_notMem,Finset.card_pair (fun h=>by subst h;omega)]
       simp only [wmI,wm1];rintro (h | h);exact hne h;exact he2_neq_q1 h.symm
      exact hc3 ▸ Finset.card_le_card hsub
   have hneT:T'.Nonempty:=Finset.card_pos.mp (by omega)
   let q_max:=T'.max' hneT;obtain ⟨es,hlte,_,hes_nv⟩:=wa3b hn C v false hmin hnn hout hsz hfun hbin q_max
    (Finset.max'_mem _ hneT)
   have hes_not:es ∉ T':=fun h=>by
    have hle:=Finset.le_max' T' es h;change es.val ≤ q_max.val at hle;omega
   have h4:=wa8 hn C v hmin.1 hnn hout hsz hfun h_false_lo (insert es T')
    (fun q hq=>by
     rcases wmI.1 hq with rfl | hq
     · exact hes_nv
     · exact (wa4d hn C v false hmin.1 hnn hout hsz hfun q hq).1)
   rw [Finset.card_insert_of_notMem hes_not] at h4;omega
 · push Not at hT_in
   have he_ne:e₁ ≠ e₂:=fun heq=>by
    subst heq;exact hT_in.1 (wa7 C v false hmin.1 hbin q₁ q₂ e₁ hne hT1 hT2 hein1 hein2)
   have h4set:({q₁,q₂,e₁,e₂} : Finset (Fin C.gates.length)).card=4:=by
    have hm1:q₁ ∉ ({q₂,e₁,e₂} : Finset _):=by
     simp only [wmI,wm1]
     rintro (h | h | h);exact hne h;exact absurd h (by intro hh;subst hh;omega);exact he2_neq_q1 h.symm
    have hm2:q₂ ∉ ({e₁,e₂} : Finset _):=by
     simp only [wmI,wm1]
     rintro (h | h);exact he1_neq_q2 h.symm;exact absurd h (by intro hh;subst hh;omega)
    rw [Finset.card_insert_of_notMem hm1,Finset.card_insert_of_notMem hm2,Finset.card_pair he_ne]
   have hle:=wa8 hn C v hmin.1 hnn hout hsz hfun h_false_lo {q₁,q₂,e₁,e₂}
    (fun q hq=>by
     simp only [wmI,wm1] at hq
     rcases hq with rfl | rfl | rfl | rfl
     · exact (wa4d hn C v false hmin.1 hnn hout hsz hfun q hT1).1
     · exact (wa4d hn C v false hmin.1 hnn hout hsz hfun q hT2).1
     · exact he1_nv
     · exact he2_nv)
   omega
lemma wa2d {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (h_false_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p false))→ n + (n + 1) / 2 - 4 ≤ D.size) (q₀ q₁ q₂ : Fin C.gates.length) (hq0:v.val ∈ (C.gates[q₀.val]).inputs∧ (C.gates[q₀.val]).op=GateOp.and) (hq1:v.val ∈ (C.gates[q₁.val]).inputs∧ (C.gates[q₁.val]).op=GateOp.or) (hq2:v.val ∈ (C.gates[q₂.val]).inputs∧ (C.gates[q₂.val]).op=GateOp.or) (hq12:q₁ ≠ q₂):False:=by
 have hT0:=(wa42 C v hmin.1 hbin q₀ hq0.1).2 hq0.2;have hv1:=(wa42 C v hmin.1 hbin q₁ hq1.1).1;have hv2:=(wa42 C v hmin.1 hbin q₂ hq2.1).1;obtain ⟨e₀,hlt0,hein0,he0_nv⟩:=wa3b hn C v false hmin hnn hout hsz hfun hbin q₀ hT0
 have h01:q₀ ≠ q₁:=fun h=>by rw [h,hq1.2] at hq0;cases hq0.2
 have h02:q₀ ≠ q₂:=fun h=>by rw [h,hq2.2] at hq0;cases hq0.2
 have he01:e₀ ≠ q₁:=fun h=>by
  subst h;exact wa13 C hmin hbin q₀.val e₀.val v.val q₀.isLt e₀.isLt hq0.1 hq1.1 hein0
 have he02:e₀ ≠ q₂:=fun h=>by
  subst h;exact wa13 C hmin hbin q₀.val e₀.val v.val q₀.isLt e₀.isLt hq0.1 hq2.1 hein0
 have hm0:q₀ ∉ ({q₁,q₂,e₀} : Finset _):=by
  simp only [wmI,wm1]
  rintro (h | h | h);exact h01 h;exact h02 h;exact absurd h (by intro hh;subst hh;omega)
 have hm1:q₁ ∉ ({q₂,e₀} : Finset _):=by
  simp only [wmI,wm1];rintro (h | h);exact hq12 h;exact he01 h.symm
 have h4:=wa8 hn C v hmin.1 hnn hout hsz hfun h_false_lo {q₀,q₁,q₂,e₀}
  (fun q hq=>by
   simp only [wmI,wm1] at hq
   rcases hq with rfl | rfl | rfl | rfl
   · exact (wa4d hn C v false hmin.1 hnn hout hsz hfun q hT0).1
   · exact hv1
   · exact hv2
   · exact he0_nv)
 rw [Finset.card_insert_of_notMem hm0,Finset.card_insert_of_notMem hm1,Finset.card_pair he02.symm] at h4;omega
lemma wa67 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (h_true_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p true))→ n + (n + 1) / 2 - 5 ≤ D.size):(Finset.univ.filter fun q:Fin C.gates.length=>v.val ∈ (C.gates[q.val]).inputs∧ wa78 GateOp.or (C.gates[q.val])=true).card ≤ 2:=by
 by_contra hgt
 have h3:3 ≤ (Finset.univ.filter fun q:Fin C.gates.length => v.val ∈ (C.gates[q.val]).inputs∧ wa78 GateOp.or (C.gates[q.val])=true).card:=by omega
 obtain ⟨S3,hS3_sub,hS3_card⟩:=Finset.exists_subset_card_eq h3
 have hS3_T:S3 ⊆ wa86 n C v true:=by
  intro q hq;have hf:=wmF.1 (hS3_sub hq);exact (wa3e C v hmin.1 hbin q hf.2.1).2 ((wa61 _).mp hf.2.2)
 have hT_card:=wa4 hn C v hmin hnn hout hsz hfun hbin h_true_lo
 have hS3_eq:S3=wa86 n C v true:=Finset.eq_of_subset_of_card_le hS3_T (by omega)
 have hcons_not:∀ q ∈ S3,∃ e:Fin C.gates.length,q.val < e.val∧ n + q.val ∈ (C.gates[e.val]).inputs∧ e.val ∉ (wa81 n C v true).2.2∧ e ∉ S3:=by
  intro q hq;obtain ⟨e,hlt,hein,he_nv⟩:=wa3b hn C v true hmin hnn hout hsz hfun hbin q (hS3_T hq)
  have he_not:e ∉ S3:=by
   intro heS;have hf1:=wmF.1 (hS3_sub hq);have hf2:=wmF.1 (hS3_sub heS)
   exact wa13 C hmin hbin q.val e.val v.val q.isLt e.isLt hf1.2.1 hf2.2.1 hein
  exact ⟨e,hlt,hein,he_nv,he_not⟩
 choose f_e hf_lt hf_in hf_nv hf_not using hcons_not
 let E:Finset (Fin C.gates.length):=S3.attach.image fun q=>f_e q.1 q.2
 have hE_inj:Function.Injective (fun q : {x // x ∈ S3}=>f_e q.1 q.2):=by
  intro a b hab
  by_contra hne
  have hane:a.1 ≠ b.1:=fun h=>hne (Subtype.ext h);have he_eq:f_e a.1 a.2=f_e b.1 b.2:=hab;have hfa:=hf_in a.1 a.2;rw [he_eq] at hfa;have hTe:=wa7 C v true hmin.1 hbin a.1 b.1 (f_e b.1 b.2) hane
   (hS3_T a.2) (hS3_T b.2) hfa (hf_in b.1 b.2)
  exact hf_not b.1 b.2 (hS3_eq ▸ hTe)
 have hE_card:E.card=3:=by rw [Finset.card_image_of_injective _ hE_inj,Finset.card_attach,hS3_card]
 have hdisj:Disjoint S3 E:=by
  rw [Finset.disjoint_left];intro x hxS hxE;simp only [E,Finset.mem_image,Finset.mem_attach,true_and,Subtype.exists] at hxE;obtain ⟨q,hq,rfl⟩:=hxE;exact hf_not q hq hxS
 have hle4:=wac hn C v hmin.1 hnn hout hsz hfun h_true_lo (S3 ∪ E) (fun x hx=>by
  rcases Finset.mem_union.mp hx with hxS | hxE
  · exact (wa4d hn C v true hmin.1 hnn hout hsz hfun x (hS3_T hxS)).1
  · simp only [E,Finset.mem_image,Finset.mem_attach,true_and,Subtype.exists] at hxE;obtain ⟨q,hq,rfl⟩:=hxE
    exact hf_nv q hq)
 rw [Finset.card_union_of_disjoint hdisj,hS3_card,hE_card] at hle4;omega
lemma wa1d {n:ℕ} (hn:5 ≤ n) (C:Circuit) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (h_false_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p false))→ n + (n + 1) / 2 - 4 ≤ D.size) (h_true_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p true))→ n + (n + 1) / 2 - 5 ≤ D.size):∀ v:Fin n,1 ≤ wDeg C v.val∧ wDeg C v.val ≤ 2:=by
 intro v;refine ⟨wa7c hn C hfun hout hbin hsz v,?_⟩
 let RA:=Finset.univ.filter fun q:Fin C.gates.length =>
  v.val ∈ (C.gates[q.val]).inputs∧ wa78 GateOp.and (C.gates[q.val])=true
 let RO:=Finset.univ.filter fun q:Fin C.gates.length =>
  v.val ∈ (C.gates[q.val]).inputs∧ wa78 GateOp.or (C.gates[q.val])=true
 let R:=Finset.univ.filter fun q:Fin C.gates.length=>v.val ∈ (C.gates[q.val]).inputs
 have hR_eq:R=RA ∪ RO:=by
  ext q;simp only [R,RA,RO,Finset.mem_union,wmF,wmU,true_and];constructor
  · intro h;obtain ⟨g,op,_,_,hg,rfl,hop,_,_,_,_⟩:=hbin q.val q.isLt;have hidx:C.gates[q.val]=g:=(wgE.1 hg).2;rw [hidx] at h ⊢
    rcases hop with hop | hop
    · exact Or.inl ⟨h,(wa5a g).mpr hop⟩
    · exact Or.inr ⟨h,(wa61 g).mpr hop⟩
  · rintro (⟨h,_⟩ | ⟨h,_⟩) <;> exact h
 have hdisj:Disjoint RA RO:=by
  rw [Finset.disjoint_left];intro q ha ho;have h1:=(wa5a _).mp (wmF.1 ha).2.2;have h2:=(wa61 _).mp (wmF.1 ho).2.2;rw [h1] at h2;cases h2
 have hR_card:wDeg C v.val=R.card:=wa17 C v.val
 have hdeg_sum:wDeg C v.val=RA.card + RO.card:=by rw [hR_card,hR_eq,Finset.card_union_of_disjoint hdisj]
 have hA1:RA.card ≤ 1:=wa6d hn C v hmin hnn hout hsz hfun hbin h_false_lo;have hO2:RO.card ≤ 2:=wa67 hn C v hmin hnn hout hsz hfun hbin h_true_lo
 rcases Nat.eq_zero_or_pos RA.card with hA0 | hApos
 · omega
 · have hAeq:RA.card=1:=by omega
   obtain ⟨q₀,hq₀⟩:=Finset.card_pos.mp hApos
   have hO1:RO.card ≤ 1:=by
    by_contra hgt
    have h2:2 ≤ RO.card:=by omega
    obtain ⟨q₁,hq1,q₂,hq2,hq12⟩:=Finset.one_lt_card.mp (by omega:1 < RO.card)
    exact wa2d hn C v hmin hnn hout hsz hfun hbin h_false_lo q₀ q₁ q₂
     ⟨(wmF.1 hq₀).2.1,(wa5a _).mp (wmF.1 hq₀).2.2⟩
     ⟨(wmF.1 hq1).2.1,(wa61 _).mp (wmF.1 hq1).2.2⟩
     ⟨(wmF.1 hq2).2.1,(wa61 _).mp (wmF.1 hq2).2.2⟩ hq12
   omega
def wa71 (C:Circuit) (w:ℕ):Finset (Fin C.gates.length) :=
 Finset.univ.filter fun q:Fin C.gates.length=>w ∈ (C.gates[q.val]).inputs
lemma wa43 (C:Circuit) (w:ℕ):(wa71 C w).card=wDeg C w :=
 (wa17 C w).symm
lemma wa4c (C:Circuit) (w:ℕ) (q:Fin C.gates.length):q ∈ wa71 C w↔ w ∈ (C.gates[q.val]).inputs:=by simp [wa71]
def wa6b (n:ℕ) (C:Circuit):ℕ→ ℕ→ Finset ℕ→ ℕ × Finset ℕ
 | 0,w,S=>(w,insert w S)
 | fuel + 1,w,S =>
  let R:=wa71 C w
  if h:R.card=1 then
   let q:=R.min' (Finset.card_pos.mp (by omega))
   if wa78 GateOp.or (C.gates[q.val])=true then
    wa6b n C fuel (n + q.val) (insert w S)
   else (w,insert w S)
  else (w,insert w S)
def orChain (n:ℕ) (C:Circuit) (v:Fin n):ℕ × Finset ℕ :=
 wa6b n C (C.gates.length + 1) v.val ∅
lemma wa36 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (fuel:ℕ) (w:ℕ) (S:Finset ℕ) (hS_lt:∀ x ∈ S,x < w) (hv_mem:v.val ∈ insert w S) (hv_S1:v ∈ S1 n C w) (hT_w:w=v.val∨ ∃ qw:Fin C.gates.length,w=n + qw.val∧ qw ∈ wa86 n C v true) (hS_info:∀ x ∈ S,wDeg C x=1∧ ∃ q:Fin C.gates.length,x ∈ (C.gates[q.val]).inputs∧ (C.gates[q.val]).op=GateOp.or∧ (x=v.val∨ ∃ qx:Fin C.gates.length,x=n + qx.val∧ qx ∈ wa86 n C v true)∧ n + q.val ∈ insert w S) (hfirst:S=∅∨ ∃ r₀ : Fin C.gates.length,v.val ∈ (C.gates[r₀.val]).inputs∧ (C.gates[r₀.val]).op=GateOp.or∧ r₀ ∈ wa86 n C v true∧ n + r₀.val ∈ insert w S∧ ∀ x ∈ S,x=v.val∨ n + r₀.val ≤ x) (hfuel:(w < n∧ C.gates.length + 1 ≤ fuel)∨ ∃ qw:Fin C.gates.length,w=n + qw.val∧ C.gates.length - qw.val ≤ fuel) :
 let wstar:=(wa6b n C fuel w S).1;let Sch:=(wa6b n C fuel w S).2
 wstar ∈ Sch ∧
 v.val ∈ Sch ∧
 v ∈ S1 n C wstar ∧
 1 ≤ wDeg C wstar ∧
 wstar < C.output ∧
 (wstar=v.val∨ ∃ qstar:Fin C.gates.length,wstar=n + qstar.val∧ qstar ∈ wa86 n C v true) ∧
 (∀ x ∈ Sch,x ≤ wstar∧ (x=v.val∨ ∃ qx:Fin C.gates.length,x=n + qx.val∧ qx ∈ wa86 n C v true)) ∧
 (∀ x ∈ Sch,x ≠ wstar→ x < wstar∧ wDeg C x=1∧ ∃ q:Fin C.gates.length,x ∈ (C.gates[q.val]).inputs∧ (C.gates[q.val]).op=GateOp.or∧ n + q.val ∈ Sch) ∧
 (wDeg C wstar=1→ ∃ qz:Fin C.gates.length,wstar ∈ (C.gates[qz.val]).inputs∧ (C.gates[qz.val]).op=GateOp.and) ∧
 (wstar ≠ v.val→ ∃ r₀ : Fin C.gates.length,v.val ∈ (C.gates[r₀.val]).inputs∧ (C.gates[r₀.val]).op=GateOp.or∧ r₀ ∈ wa86 n C v true ∧
  n + r₀.val ∈ Sch∧ ∀ x ∈ Sch,x=v.val∨ n + r₀.val ≤ x):=by
 induction fuel generalizing w S with
 | zero =>
  exfalso
  rcases hfuel with ⟨_,h1⟩ | ⟨qw,_,h2⟩
  · omega
  · have hlt:=qw.isLt;omega
 | succ fuel ih =>
  have hpos_w:1 ≤ wDeg C w:=by
   rcases hT_w with rfl | ⟨qw,rfl,hqT⟩
   · exact wa7c hn C hfun hout hbin hsz v
   · have hvan:=(wa4d hn C v true hmin.1 hnn hout hsz hfun qw hqT).2;exact wa1e C hmin hout qw.val hvan
  have hlt_out_w:w < C.output:=by
   rcases hT_w with rfl | ⟨qw,rfl,hqT⟩
   · simp only [Circuit.size] at hout hsz ⊢;omega
   · have hvan:=(wa4d hn C v true hmin.1 hnn hout hsz hfun qw hqT).2;simp only [Circuit.size] at hout hvan ⊢;omega
  have hw_bv:(wa81 n C v true).1.getD w (Sum.inl false)=Sum.inl true:=by
   rcases hT_w with rfl | ⟨qw,rfl,hqT⟩
   · exact wa38 n C v true
   · exact (wmF.1 hqT).2
  dsimp only [wa6b]
  split_ifs with hcard h_or
  · let R:=wa71 C w
    let q:Fin C.gates.length:=R.min' (Finset.card_pos.mp (by dsimp [R];rw [wa43];omega))
    have hq_mem:q ∈ R:=Finset.min'_mem R _;have hqw:w ∈ (C.gates[q.val]).inputs:=(wa4c C w q).mp hq_mem
    have hdeg_w:wDeg C w=1:=by rw [← wa43 C w];exact hcard
    have hop_or:(C.gates[q.val]).op=GateOp.or:=(wa61 _).mp h_or;obtain ⟨g,_,a,b,hg,rfl,_,hin,hne,ha,hb⟩:=hbin q.val q.isLt;have hidx:C.gates[q.val]=g:=(wgE.1 hg).2
    have hqw_cases:w=a∨ w=b:=by
     have h':=hqw;simp only [hidx,hin,List.mem_cons,List.mem_nil_iff,or_false] at h';exact h'
    have hq_T:q ∈ wa86 n C v true:=by
     have hc:=(wa27 C v true hmin.1 hbin q w hqw hw_bv).2.1
     rcases hqw_cases with rfl | rfl
     · exact hc b (by rw [hidx,hin];simp) hne.symm (Or.inr (Or.inl ⟨hop_or,rfl⟩))
     · exact hc a (by rw [hidx,hin];simp) hne (Or.inr (Or.inl ⟨hop_or,rfl⟩))
    have hlt_w_nq:w < n + q.val:=by rcases hqw_cases with rfl | rfl <;> assumption
    have hv_nq:v ∈ S1 n C (n + q.val):=by
     have hop_g:g.op=GateOp.or:=by rw [← hidx];exact hop_or
     have hg':C.gates[q.val]?=some ⟨GateOp.or,[a,b]⟩:=by
      rw [hg];congr 1
      rcases g with ⟨op',ins'⟩
      exact congrArg₂ Gate.mk hop_g hin
     rw [S1_or C q.val a b q.isLt hg' ha hb]
     rcases hqw_cases with rfl | rfl
     · exact Finset.mem_union_left _ hv_S1
     · exact Finset.mem_union_right _ hv_S1
    have hfuel':(n + q.val < n∧ C.gates.length + 1 ≤ fuel)∨ ∃ qw:Fin C.gates.length,n + q.val=n + qw.val∧ C.gates.length - qw.val ≤ fuel:=by
     refine Or.inr ⟨q,rfl,?_⟩
     have hq_lt:=q.isLt
     rcases hfuel with ⟨hw_n,hfl⟩ | ⟨qw,hweq,hfl⟩
     · omega
     · have hqw_lt:=qw.isLt;omega
    have hS_lt':∀ x ∈ insert w S,x < n + q.val:=by
     intro x hx
     rcases wmI.1 hx with rfl | hxS
     · exact hlt_w_nq
     · exact lt_trans (hS_lt x hxS) hlt_w_nq
    have hS_info':∀ x ∈ insert w S,wDeg C x=1∧ ∃ qq:Fin C.gates.length, x ∈ (C.gates[qq.val]).inputs∧ (C.gates[qq.val]).op=GateOp.or∧ (x=v.val∨ ∃ qx:Fin C.gates.length,x=n + qx.val∧ qx ∈ wa86 n C v true)∧ n + qq.val ∈ insert (n + q.val) (insert w S):=by
     intro x hx
     rcases wmI.1 hx with rfl | hxS
     · exact ⟨hdeg_w,q,hqw,hop_or,hT_w,Finset.mem_insert_self _ _⟩
     · obtain ⟨hd,qq,hqin,hqop,hqT,hmem⟩:=hS_info x hxS;exact ⟨hd,qq,hqin,hqop,hqT,Finset.mem_insert_of_mem hmem⟩
    have hfirst':insert w S=∅∨ ∃ r₀ : Fin C.gates.length,v.val ∈ (C.gates[r₀.val]).inputs∧ (C.gates[r₀.val]).op=GateOp.or∧ r₀ ∈ wa86 n C v true∧ n + r₀.val ∈ insert (n + q.val) (insert w S)∧ ∀ x ∈ insert w S,x=v.val∨ n + r₀.val ≤ x:=by
     refine Or.inr ?_
     rcases hfirst with rfl | ⟨r₀,hr0_in,hr0_op,hr0_T,hr0_mem,hr0_le⟩
     · have hwv:w=v.val:=by
        rcases wmI.1 hv_mem with hv | hne
        · exact hv.symm
        · exact absurd hne (wmN _)
       refine ⟨q,hwv ▸ hqw,hop_or,hq_T,Finset.mem_insert_self _ _,fun x hx=>?_⟩
       rcases wmI.1 hx with rfl | hx
       · exact Or.inl hwv
       · exact absurd hx (wmN _)
     · refine ⟨r₀,hr0_in,hr0_op,hr0_T,Finset.mem_insert_of_mem hr0_mem,fun x hx=>?_⟩
       rcases wmI.1 hx with rfl | hxS
       · rcases wmI.1 hr0_mem with hnw | hnrS
         · exact Or.inr (by omega)
         · exact Or.inr (le_of_lt (hS_lt _ hnrS))
       · exact hr0_le x hxS
    exact ih (n + q.val) (insert w S) hS_lt' (Finset.mem_insert_of_mem hv_mem) hv_nq
     (Or.inr ⟨q,rfl,hq_T⟩) hS_info' hfirst' hfuel'
  · refine ⟨Finset.mem_insert_self _ _,hv_mem,hv_S1,hpos_w,hlt_out_w,hT_w,?_,?_,?_,?_⟩
    · intro x hx
      rcases wmI.1 hx with rfl | hxS
      · exact ⟨le_refl _,hT_w⟩
      · obtain ⟨_,_,_,_,hqT,_⟩:=hS_info x hxS;exact ⟨le_of_lt (hS_lt x hxS),hqT⟩
    · intro x hx hne
      rcases wmI.1 hx with rfl | hxS
      · exact absurd rfl hne
      · obtain ⟨hd,qq,hqin,hqop,_,hmem⟩:=hS_info x hxS;exact ⟨hS_lt x hxS,hd,qq,hqin,hqop,hmem⟩
    · intro hdeg1
      have hcard1:(wa71 C w).card=1:=by rw [wa43];exact hdeg1
      let R:=wa71 C w
      let qz:Fin C.gates.length:=R.min' (Finset.card_pos.mp (by rw [hcard1];exact Nat.zero_lt_one))
      have hqz_mem:qz ∈ R:=Finset.min'_mem R _;have hqz_in:w ∈ (C.gates[qz.val]).inputs:=(wa4c C w qz).mp hqz_mem
      have hnot_or:¬(wa78 GateOp.or (C.gates[qz.val])=true):=fun hor=>h_or (by
       change wa78 GateOp.or (C.gates[((wa71 C w).min' _).val])=true
       exact hor)
      obtain ⟨g,op,_,_,hg,rfl,hop,_,_,_,_⟩:=hbin qz.val qz.isLt;have hidx:C.gates[qz.val]=g:=(wgE.1 hg).2;rw [hidx] at hnot_or
      rcases hop with hop | hop
      · exact ⟨qz,hqz_in,by rw [hidx];exact hop⟩
      · exact absurd ((wa61 g).mpr hop) hnot_or
    · intro hne_v
      rcases hfirst with rfl | ⟨r₀,hr0_in,hr0_op,hr0_T,hr0_mem,hr0_le⟩
      · rcases wmI.1 hv_mem with hv | hv
        · exact absurd hv.symm hne_v
        · exact absurd hv (wmN _)
      · exact ⟨r₀,hr0_in,hr0_op,hr0_T,hr0_mem,fun x hx=>by
         rcases wmI.1 hx with rfl | hxS
         · rcases wmI.1 hr0_mem with hnw | hnrS
           · exact Or.inr (by omega)
           · exact Or.inr (le_of_lt (hS_lt _ hnrS))
         · exact hr0_le x hxS⟩
  · refine ⟨Finset.mem_insert_self _ _,hv_mem,hv_S1,hpos_w,hlt_out_w,hT_w,?_,?_,?_,?_⟩
    · intro x hx
      rcases wmI.1 hx with rfl | hxS
      · exact ⟨le_refl _,hT_w⟩
      · obtain ⟨_,_,_,_,hqT,_⟩:=hS_info x hxS;exact ⟨le_of_lt (hS_lt x hxS),hqT⟩
    · intro x hx hne
      rcases wmI.1 hx with rfl | hxS
      · exact absurd rfl hne
      · obtain ⟨hd,qq,hqin,hqop,_,hmem⟩:=hS_info x hxS;exact ⟨hS_lt x hxS,hd,qq,hqin,hqop,hmem⟩
    · intro hdeg1;exfalso;apply hcard;rw [wa43];exact hdeg1
    · intro hne_v
      rcases hfirst with rfl | ⟨r₀,hr0_in,hr0_op,hr0_T,hr0_mem,hr0_le⟩
      · rcases wmI.1 hv_mem with hv | hv
        · exact absurd hv.symm hne_v
        · exact absurd hv (wmN _)
      · exact ⟨r₀,hr0_in,hr0_op,hr0_T,hr0_mem,fun x hx=>by
         rcases wmI.1 hx with rfl | hxS
         · rcases wmI.1 hr0_mem with hnw | hnrS
           · exact Or.inr (by omega)
           · exact Or.inr (le_of_lt (hS_lt _ hnrS))
         · exact hr0_le x hxS⟩
lemma wa57 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) :
 let wstar:=(orChain n C v).1;let Sch:=(orChain n C v).2
 wstar ∈ Sch ∧
 v.val ∈ Sch ∧
 v ∈ S1 n C wstar ∧
 1 ≤ wDeg C wstar ∧
 wstar < C.output ∧
 (wstar=v.val∨ ∃ qstar:Fin C.gates.length,wstar=n + qstar.val∧ qstar ∈ wa86 n C v true) ∧
 (∀ x ∈ Sch,x ≤ wstar∧ (x=v.val∨ ∃ qx:Fin C.gates.length,x=n + qx.val∧ qx ∈ wa86 n C v true)) ∧
 (∀ x ∈ Sch,x ≠ wstar→ x < wstar∧ wDeg C x=1∧ ∃ q:Fin C.gates.length,x ∈ (C.gates[q.val]).inputs∧ (C.gates[q.val]).op=GateOp.or∧ n + q.val ∈ Sch) ∧
 (wDeg C wstar=1→ ∃ qz:Fin C.gates.length,wstar ∈ (C.gates[qz.val]).inputs∧ (C.gates[qz.val]).op=GateOp.and) ∧
 (wstar ≠ v.val→ ∃ r₀ : Fin C.gates.length,v.val ∈ (C.gates[r₀.val]).inputs∧ (C.gates[r₀.val]).op=GateOp.or∧ r₀ ∈ wa86 n C v true ∧
  n + r₀.val ∈ Sch∧ ∀ x ∈ Sch,x=v.val∨ n + r₀.val ≤ x):=by
 exact wa36 hn C v hmin hnn hout hsz hfun hbin (C.gates.length + 1) v.val ∅
  (fun x hx=>absurd hx (wmN _))
  (Finset.mem_insert_self _ _)
  (by rw [wa76];exact Finset.mem_singleton_self _)
  (Or.inl rfl)
  (fun x hx=>absurd hx (wmN _))
  (Or.inl rfl)
  (Or.inl ⟨v.isLt,le_refl _⟩)
lemma wae {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (_hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (_hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (wstar:ℕ) (Sch:Finset ℕ) (hwstar_out:wstar < C.output) (hv_Sch:v.val ∈ Sch) (hv_S1:v ∈ S1 n C wstar) (hSch_le:∀ x ∈ Sch,x ≤ wstar) (hSch_in:∀ x ∈ Sch,x ≠ wstar→ wDeg C x=1∧ ∃ q:Fin C.gates.length,x ∈ (C.gates[q.val]).inputs∧ n + q.val ∈ Sch):S1 n C wstar={v}:=by
 rw [Finset.eq_singleton_iff_unique_mem];refine ⟨hv_S1,fun u hu=>?_⟩
 have hleak:∀ (q:ℕ) (hq:q < C.size),n + q ∉ Sch→ ∀ a ∈ (C.gates[q]).inputs,a ∈ Sch→ a=wstar:=by
  intro q hq hq_not a ha_in ha_S
  by_contra hne
  obtain ⟨hdeg,qq,hqin,hmem⟩:=hSch_in a ha_S hne;have hidx_q:C.gates[q]?=some C.gates[q]:=wgE.2 ⟨hq,rfl⟩;have hidx_qq:C.gates[qq.val]?=some C.gates[qq.val]:=wgE.2 ⟨qq.isLt,rfl⟩
  have heq:=wa3 C a q qq.val hdeg _ _ hidx_q ha_in hidx_qq hqin
  rw [heq] at hq_not;exact hq_not hmem
 have hout_not:C.output ∉ Sch:=fun h=>by have:=hSch_le C.output h;omega
 have hstep:∀ w:Fin n,wa83 v w→ wa83 u w:=by
  intro w hadj
  have hx_out:wireVal C (wa85 v w) C.output=true:=by
   have hf:=congrArg (fun f=>f (wa85 v w)) hfun;rw [wa14] at hf;rw [hf];exact (wa40 hn v w).mpr hadj
  have hy_w:wireVal C (wa85 u w) wstar=true:=by
   have hu_w:wireVal C (oneHot u) wstar=true:=(wmF.1 hu).2
   have hbi:∀ g ∈ C.gates,g.op=GateOp.and∨ g.op=GateOp.or:=fun g hg=>by
    obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp hg;obtain ⟨g',_,_,_,hgi,rfl,hop,_,_,_,_⟩:=hbin i hi;have heq:C.gates[i]=g':=(wgE.1 hgi).2;rw [heq];exact hop
   exact wa5b C hbi (oneHot u) (wa85 u w) (fun i hi=>by
    simp only [oneHot,wa85,decide_eq_true_eq] at hi ⊢;exact Or.inl hi) wstar hu_w
  have hy_out:wireVal C (wa85 u w) C.output=true :=
   wa19 C hbin Sch wstar hleak (wa85 v w) (wa85 u w)
    (fun i hi hxi=>by
     simp only [wa85,decide_eq_true_eq] at hxi ⊢
     rcases hxi with rfl | rfl
     · exact absurd hv_Sch hi
     · exact Or.inr rfl)
    (fun _=>hy_w) C.output hout_not hx_out
  have hf:=congrArg (fun f=>f (wa85 u w)) hfun;rw [wa14] at hf;rw [hf] at hy_out;exact (wa40 hn u w).mp hy_out
 exact wa12 hn (hstep (wa80 (by omega) v) (wa5e (by omega) v))
  (hstep (wa7d (by omega) v) (wa5f (by omega) v))
lemma wa9 {n:ℕ} (C:Circuit) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (Sch:Finset ℕ) (w_end:ℕ) (q_end:Fin C.gates.length) (hw_end_in:w_end ∈ (C.gates[q_end.val]).inputs) (hw_end_deg:wDeg C w_end=1) (hSch_in:∀ x ∈ Sch,x ≠ w_end→ wDeg C x=1∧ ∃ q:Fin C.gates.length,x ∈ (C.gates[q.val]).inputs∧ n + q.val ∈ Sch) (x y:Fin n→ Bool) (hxy:∀ i:Fin n,i.val ∉ Sch→ x i=y i) (w:ℕ) (hw_lt:w < n + q_end.val) (hw_not:w ∉ Sch):wireVal C x w=wireVal C y w:=by
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  by_cases hwn:w < n
  · have hx:=wa52 C x ⟨w,hwn⟩;have hy:=wa52 C y ⟨w,hwn⟩;dsimp only at hx hy;rw [hx,hy,hxy ⟨w,hwn⟩ hw_not]
  · have hqn:w - n < C.size:=by
     have hq_sz:=q_end.isLt;simp only [Circuit.size] at hq_sz ⊢;omega
    obtain ⟨g,op,a,b,hg,rfl,hop,hin,_,ha,hb⟩:=hbin (w - n) hqn
    have hweq:n + (w - n)=w:=by omega
    have hq_ne_end:w - n ≠ q_end.val:=by omega
    have hno_Sch:∀ c ∈ [a,b],c ∉ Sch:=by
     intro c hc hc_S;have hidx:C.gates[w - n]=g:=(wgE.1 hg).2
     have hc_in:c ∈ (C.gates[w - n]).inputs:=by rw [hidx,hin];exact hc
     have hc_g:c ∈ g.inputs:=hidx ▸ hc_in
     by_cases hce:c=w_end
     · have hc_g2:w_end ∈ g.inputs:=hce ▸ hc_g;have h1:C.gates[w - n]?=some g:=hg
       have h2:C.gates[q_end.val]?=some C.gates[q_end.val] :=
        wgE.2 ⟨q_end.isLt,rfl⟩
       exact hq_ne_end (wa3 C w_end (w - n) q_end.val hw_end_deg _ _ h1 hc_g2 h2 hw_end_in)
     · obtain ⟨hdeg,qq,hqin,hmem⟩:=hSch_in c hc_S hce;have h1:C.gates[w - n]?=some g:=hg
       have h2:C.gates[qq.val]?=some C.gates[qq.val] :=
        wgE.2 ⟨qq.isLt,rfl⟩
       have heq:=wa3 C c (w - n) qq.val hdeg _ _ h1 hc_g h2 hqin
       rw [← heq,hweq] at hmem;exact hw_not hmem
    have ha_eq:=ih a (by omega) (by omega) (hno_Sch a (by simp))
    have hb_eq:=ih b (by omega) (by omega) (hno_Sch b (by simp))
    rcases hop with hop | hop
    · have hg':C.gates[w - n]?=some ⟨GateOp.and,[a,b]⟩:=by
       rw [hg];congr 1;rcases g with ⟨op',ins'⟩;exact congrArg₂ Gate.mk hop hin
      rw [← hweq,wa60 C x (w - n) a b hqn hg' ha hb,wa60 C y (w - n) a b hqn hg' ha hb,ha_eq,hb_eq]
    · have hg':C.gates[w - n]?=some ⟨GateOp.or,[a,b]⟩:=by
       rw [hg];congr 1;rcases g with ⟨op',ins'⟩;exact congrArg₂ Gate.mk hop hin
      rw [← hweq,wa6e C x (w - n) a b hqn hg' ha hb,wa6e C y (w - n) a b hqn hg' ha hb,ha_eq,hb_eq]
lemma wa1 {n:ℕ} (C:Circuit) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (v:Fin n) (Sch:Finset ℕ) (w_end:ℕ) (q_end:Fin C.gates.length) (hv_S:v.val ∈ Sch) (hw_end_in:w_end ∈ (C.gates[q_end.val]).inputs) (hw_end_deg:wDeg C w_end=1) (hSch_in:∀ x ∈ Sch,x ≠ w_end→ wDeg C x=1∧ ∃ q:Fin C.gates.length,x ∈ (C.gates[q.val]).inputs∧ n + q.val ∈ Sch) (w:ℕ) (hw_lt:w < n + q_end.val) (hw_not:w ∉ Sch):wireVal C (oneHot v) w=false:=by
 have heq:=wa9 C hbin Sch w_end q_end hw_end_in hw_end_deg hSch_in
  (oneHot v) (fun _=>false) (fun i hi=>by
   simp only [oneHot,decide_eq_false_iff_not]
   intro h;subst h;exact hi hv_S) w hw_lt hw_not
 rw [heq];exact wa21 C hbin w
def D1' (n:ℕ) (C:Circuit):Finset (Fin n) :=
 Finset.univ.filter fun v:Fin n=>wDeg C v.val=1∧ 2 ≤ wDeg C (orChain n C v).1
def gSplit (n:ℕ) (C:Circuit) (v:Fin n):ℕ:=(orChain n C v).1
lemma wa6a {n:ℕ} (hn:5 ≤ n) (C:Circuit) (c:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (hdeg1:wDeg C c.val=1) (hc_not:c ∉ D1' n C) :
 let w_c:=(orChain n C c).1
 ∃ qz y_c:ℕ,qz < C.size ∧
  (C.gates[qz]?=some ⟨GateOp.and,[w_c,y_c]⟩∨ C.gates[qz]?=some ⟨GateOp.and,[y_c,w_c]⟩) ∧
  S1 n C w_c={c} ∧
  (∀ u:Fin n,wa83 c u→ u ∈ S1 n C y_c) ∧
  c ∉ S1 n C y_c:=by
 have hsp:=wa57 hn C c hmin hnn hout hsz hfun hbin
 set w_c:=(orChain n C c).1;set S_c:=(orChain n C c).2
 have hwc_deg:wDeg C w_c=1:=by
  have hge1:=hsp.2.2.2.1
  have hnot2:¬(2 ≤ wDeg C w_c):=fun h2 =>
   hc_not (wmF.2 ⟨wmU _,hdeg1,h2⟩)
  omega
 obtain ⟨qz,hqz_in,hqz_op⟩:=hsp.2.2.2.2.2.2.2.2.1 hwc_deg
 have hqz_in0:w_c ∈ (C.gates[qz.val]).inputs:=hqz_in
 obtain ⟨g,op,a,b,hg,rfl,_,hin,hne,ha,hb⟩:=hbin qz.val qz.isLt;have hidx:C.gates[qz.val]=g:=(wgE.1 hg).2
 have hg_and:g.op=GateOp.and:=by rw [← hidx];exact hqz_op
 simp only [hidx,hin,List.mem_cons,List.mem_nil_iff,or_false] at hqz_in
 have hS1_wc:S1 n C w_c={c} :=
  wae hn C c hnn hout hsz hfun hbin w_c S_c
   hsp.2.2.2.2.1 hsp.2.1 hsp.2.2.1
   (fun x hx=>(hsp.2.2.2.2.2.2.1 x hx).1)
   (fun x hx hne'=>by
    obtain ⟨_,hdx,qq,hqin,_,hmem⟩:=hsp.2.2.2.2.2.2.2.1 x hx hne'
    exact ⟨hdx,qq,hqin,hmem⟩)
 have h_not_S:∀ y:ℕ,y ∈ [a,b]→ y ≠ w_c→ y ∉ S_c:=by
  intro y hy hy_ne hy_S
  have hy_in:y ∈ (C.gates[qz.val]).inputs:=by rw [hidx,hin];exact hy
  obtain ⟨_,hdy,qq,hqin,hqop,hmem⟩:=hsp.2.2.2.2.2.2.2.1 y hy_S hy_ne;have h1:C.gates[qz.val]?=some g:=hg
  have h2:C.gates[qq.val]?=some C.gates[qq.val] :=
   wgE.2 ⟨qq.isLt,rfl⟩
  have heq:=wa3 C y qz.val qq.val hdy _ _ h1 (hidx ▸ hy_in) h2 hqin
  have hop_eq:(C.gates[qz.val]?).map Gate.op=(C.gates[qq.val]?).map Gate.op:=by rw [heq]
  rw [wgE.2 ⟨qz.isLt,rfl⟩,wgE.2 ⟨qq.isLt,rfl⟩] at hop_eq;simp only [Option.map_some,Option.some.injEq,hqz_op,hqop] at hop_eq;cases hop_eq
 have hcent_y:∀ y:ℕ,w_c < n + qz.val→ y < n + qz.val→ y ∉ S_c→ (C.gates[qz.val]?=some ⟨GateOp.and,[w_c,y]⟩∨ C.gates[qz.val]?=some ⟨GateOp.and,[y,w_c]⟩)→ (∀ u:Fin n,wa83 c u→ u ∈ S1 n C y)∧ c ∉ S1 n C y:=by
  intro y hwc_lt hy_lt hy_nS hgate
  have hSch_sub:∀ x ∈ S_c,x ≠ w_c→ wDeg C x=1∧ ∃ qq:Fin C.gates.length, x ∈ (C.gates[qq.val]).inputs∧ n + qq.val ∈ S_c:=fun x hx hne'=>by
   obtain ⟨_,hdx,qq,hqin,_,hmem⟩:=hsp.2.2.2.2.2.2.2.1 x hx hne';exact ⟨hdx,qq,hqin,hmem⟩
  have hc_not_y:c ∉ S1 n C y:=by
   intro hcy;have htr:wireVal C (oneHot c) y=true:=(wmF.1 hcy).2;have hfl:=wa1 C hbin c S_c w_c qz
    hsp.2.1 hqz_in0 hwc_deg hSch_sub y hy_lt hy_nS
   exact Bool.false_ne_true (hfl.symm.trans htr)
  refine ⟨fun u hadj=>?_,hc_not_y⟩
  by_contra hu_nS1
  have hu_val:wireVal C (oneHot u) y=false:=by
   have hnmem:¬(u ∈ S1 n C y):=hu_nS1;simp only [S1,wmF,wmU,true_and] at hnmem;exact Bool.eq_false_iff.mpr hnmem
  have hpair_y:wireVal C (wa85 c u) y=false:=by
   have heq:=wa9 C hbin S_c w_c qz hqz_in0 hwc_deg hSch_sub
    (wa85 c u) (oneHot u) (fun i hi=>by
     simp only [wa85,oneHot];have hic:i ≠ c:=fun h=>hi (h ▸ hsp.2.1)
     simp [hic]) y hy_lt hy_nS
   rw [heq];exact hu_val
  have hpair_qz:wireVal C (wa85 c u) (n + qz.val)=false:=by
   rcases hgate with hgate | hgate
   · rw [wa60 C (wa85 c u) qz.val w_c y qz.isLt hgate hwc_lt hy_lt,hpair_y,Bool.and_false]
   · rw [wa60 C (wa85 c u) qz.val y w_c qz.isLt hgate hy_lt hwc_lt,hpair_y,Bool.false_and]
  have hpair_out:wireVal C (wa85 c u) C.output=true:=by
   have hf:=congrArg (fun f=>f (wa85 c u)) hfun;rw [wa14] at hf;rw [hf];exact (wa40 hn c u).mpr hadj
  by_cases hqz_out:n + qz.val=C.output
  · rw [hqz_out] at hpair_qz;exact Bool.false_ne_true (hpair_qz.symm.trans hpair_out)
  · have hS_not_out:C.output ∉ insert (n + qz.val) S_c:=by
     intro hmem
     rcases wmI.1 hmem with h1 | h2
     · exact hqz_out h1.symm
     · have:=(hsp.2.2.2.2.2.2.1 C.output h2).1;have:=hsp.2.2.2.2.1;omega
    have hleak':∀ (q:ℕ) (hq:q < C.size),n + q ∉ insert (n + qz.val) S_c→ ∀ d ∈ (C.gates[q]).inputs,d ∈ insert (n + qz.val) S_c→ d=n + qz.val:=by
     intro q hq hq_not d hd_in hd_mem
     rcases wmI.1 hd_mem with rfl | hd_S
     · rfl
     · exfalso
       by_cases hd_w:d=w_c
       · subst hd_w;have h1:C.gates[q]?=some C.gates[q]:=wgE.2 ⟨hq,rfl⟩
         have h2:C.gates[qz.val]?=some C.gates[qz.val] :=
          wgE.2 ⟨qz.isLt,rfl⟩
         have heq:=wa3 C w_c q qz.val hwc_deg _ _ h1 hd_in h2 hqz_in0;rw [heq] at hq_not;exact hq_not (Finset.mem_insert_self _ _)
       · obtain ⟨hdegd,qq,hqin,hmem⟩:=hSch_sub d hd_S hd_w;have h1:C.gates[q]?=some C.gates[q]:=wgE.2 ⟨hq,rfl⟩
         have h2:C.gates[qq.val]?=some C.gates[qq.val] :=
          wgE.2 ⟨qq.isLt,rfl⟩
         have heq:=wa3 C d q qq.val hdegd _ _ h1 hd_in h2 hqin
         exact hq_not (Finset.mem_insert_of_mem (heq ▸ hmem))
    have hu_out:wireVal C (oneHot u) C.output=true :=
     wa19 C hbin (insert (n + qz.val) S_c) (n + qz.val) hleak'
      (wa85 c u) (oneHot u)
      (fun i hi hxi=>by
       simp only [wa85,oneHot,decide_eq_true_eq] at hxi ⊢
       rcases hxi with rfl | rfl
       · exact absurd (Finset.mem_insert_of_mem hsp.2.1) hi
       · rfl)
      (fun h=>absurd h (by rw [hpair_qz];exact Bool.false_ne_true))
      C.output hS_not_out hpair_out
    have hf:=congrArg (fun f=>f (oneHot u)) hfun;rw [wa14] at hf;rw [hf,wa2a hn u] at hu_out;exact Bool.false_ne_true hu_out
 rcases hqz_in with rfl | rfl
 · have hgate:C.gates[qz.val]?=some ⟨GateOp.and,[w_c,b]⟩:=by
    rw [hg];congr 1;rcases g with ⟨op',ins'⟩;exact congrArg₂ Gate.mk hg_and hin
   have hcb:=hcent_y b ha hb (h_not_S b (by simp) hne.symm) (Or.inl hgate)
   exact ⟨qz.val,b,qz.isLt,Or.inl hgate,hS1_wc,hcb.1,hcb.2⟩
 · have hgate:C.gates[qz.val]?=some ⟨GateOp.and,[a,w_c]⟩:=by
    rw [hg];congr 1;rcases g with ⟨op',ins'⟩;exact congrArg₂ Gate.mk hg_and hin
   have hca:=hcent_y a hb ha (h_not_S a (by simp) hne) (Or.inr hgate)
   exact ⟨qz.val,a,qz.isLt,Or.inr hgate,hS1_wc,hca.1,hca.2⟩
lemma wa49 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (u v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (hdeg_u:wDeg C u.val=1) (hu_not:u ∉ D1' n C) (_hdeg_v:wDeg C v.val=1) (_hv_not:v ∉ D1' n C) (hadj:wa83 u v) (qzu y_u qzv y_v:ℕ) (hqzu:qzu < C.size) (hgu:C.gates[qzu]?=some ⟨GateOp.and,[(orChain n C u).1,y_u]⟩∨ C.gates[qzu]?=some ⟨GateOp.and,[y_u,(orChain n C u).1]⟩) (_hS1_u:S1 n C (orChain n C u).1={u}) (hnbr_u:∀ w:Fin n,wa83 u w→ w ∈ S1 n C y_u) (hqzv:qzv < C.size) (hgv:C.gates[qzv]?=some ⟨GateOp.and,[(orChain n C v).1,y_v]⟩∨ C.gates[qzv]?=some ⟨GateOp.and,[y_v,(orChain n C v).1]⟩) (hS1_v:S1 n C (orChain n C v).1={v}) (hnbr_v:∀ w:Fin n,wa83 v w→ w ∈ S1 n C y_v):qzu < qzv:=by
 have hsp_u:=wa57 hn C u hmin hnn hout hsz hfun hbin
 set w_u:=(orChain n C u).1;set S_u:=(orChain n C u).2;set w_v:=(orChain n C v).1
 have hwu_deg:wDeg C w_u=1:=by
  have hge1:=hsp_u.2.2.2.1
  have hnot2:¬(2 ≤ wDeg C w_u):=fun h2 =>
   hu_not (wmF.2 ⟨wmU _,hdeg_u,h2⟩)
  omega
 have hgu_in:w_u ∈ (C.gates[qzu]).inputs∧ y_u ≠ w_u:=by
  obtain ⟨g,_,a,b,hg,rfl,_,hin,hne,_,_⟩:=hbin qzu hqzu;have hidx:C.gates[qzu]=g:=(wgE.1 hg).2
  rcases hgu with hgu | hgu <;> rw [hgu] at hg <;> cases hg <;> rw [hidx] <;>
   simp only [List.cons.injEq,and_true] at hin
  · exact ⟨by simp,fun h=>hne (hin.1.symm.trans (h.symm.trans hin.2))⟩
  · exact ⟨by simp,fun h=>hne (hin.1.symm.trans (h.trans hin.2))⟩
 have hyv_lt:y_v < n + qzv:=by
  obtain ⟨g,_,a,b,hg,rfl,_,hin,_,ha,hb⟩:=hbin qzv hqzv
  rcases hgv with hgv | hgv <;> rw [hgv] at hg <;> cases hg <;> simp only [List.cons.injEq,and_true] at hin
  · rcases hin with ⟨_,rfl⟩;exact hb
  · rcases hin with ⟨rfl,_⟩;exact ha
 have hyv_in:y_v ∈ (C.gates[qzv]).inputs:=by
  rcases hgv with hgv | hgv
  · have h':C.gates[qzv]=⟨GateOp.and,[w_v,y_v]⟩:=by convert (wgE.1 hgv).2
    rw [h'];simp
  · have h':C.gates[qzv]=⟨GateOp.and,[y_v,w_v]⟩:=by convert (wgE.1 hgv).2
    rw [h'];simp
 have hqv_op:(C.gates[qzv]?).map Gate.op=some GateOp.and:=by rcases hgv with hgv | hgv <;> rw [hgv] <;> rfl
 have hu_in_yv:u ∈ S1 n C y_v:=hnbr_v u (Or.elim hadj Or.inr Or.inl)
 by_cases hyv_S:y_v ∈ S_u
 · by_cases hyv_w:y_v=w_u
   · have h1:C.gates[qzu]?=some C.gates[qzu]:=wgE.2 ⟨hqzu,rfl⟩;have h2:C.gates[qzv]?=some C.gates[qzv]:=wgE.2 ⟨hqzv,rfl⟩;have heq_qz:qzu=qzv:=wa3 C w_u qzu qzv hwu_deg _ _ h1 hgu_in.1 h2 (hyv_w ▸ hyv_in)
     have hyu_wv:y_u=w_v:=by
      rw [← heq_qz] at hgv
      rcases hgu with hgu | hgu <;> rcases hgv with hgv | hgv <;> rw [hgu] at hgv <;>
       simp only [Option.some.injEq,Gate.mk.injEq,List.cons.injEq,and_true,true_and] at hgv
      · exact absurd (hgv.2.trans hyv_w) hgu_in.2
      · exact hgv.2
      · exact hgv.1
      · exact absurd (hgv.1.trans hyv_w) hgu_in.2
     have hS1_yu:S1 n C y_u={v}:=hyu_wv ▸ hS1_v
     have hn1:wa80 (by omega) u ∈ S1 n C y_u:=hnbr_u _ (wa5e (by omega) u)
     have hn2:wa7d (by omega) u ∈ S1 n C y_u:=hnbr_u _ (wa5f (by omega) u)
     rw [hS1_yu,wm1] at hn1 hn2;exact absurd (hn1.trans hn2.symm) (wa29 hn u)
   · exfalso;obtain ⟨_,hdy,qq,hqin,hqop,_⟩:=hsp_u.2.2.2.2.2.2.2.1 y_v hyv_S hyv_w;have h1:C.gates[qzv]?=some C.gates[qzv]:=wgE.2 ⟨hqzv,rfl⟩;have h2:C.gates[qq.val]?=some C.gates[qq.val]:=wgE.2 ⟨qq.isLt,rfl⟩
     have heq:=wa3 C y_v qzv qq.val hdy _ _ h1 hyv_in h2 hqin
     have hop_eq:(C.gates[qzv]?).map Gate.op=(C.gates[qq.val]?).map Gate.op:=by rw [heq]
     rw [hqv_op,wgE.2 ⟨qq.isLt,rfl⟩] at hop_eq;simp only [Option.map_some,Option.some.injEq,hqop] at hop_eq;cases hop_eq
 · have htr:wireVal C (oneHot u) y_v=true:=(wmF.1 hu_in_yv).2
   by_contra hle
   have hlt_u:y_v < n + qzu:=by omega
   have hSch_sub:∀ x ∈ S_u,x ≠ w_u→ wDeg C x=1∧ ∃ qq:Fin C.gates.length, x ∈ (C.gates[qq.val]).inputs∧ n + qq.val ∈ S_u:=fun x hx hne'=>by
    obtain ⟨_,hdx,qq,hqin,_,hmem⟩:=hsp_u.2.2.2.2.2.2.2.1 x hx hne';exact ⟨hdx,qq,hqin,hmem⟩
   have hfl:=wa1 C hbin u S_u w_u ⟨qzu,hqzu⟩
    hsp_u.2.1 hgu_in.1 hwu_deg hSch_sub y_v hlt_u hyv_S
   exact Bool.false_ne_true (hfl.symm.trans htr)
lemma wa62 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (hD_bounds:∀ v:Fin n,1 ≤ wDeg C v.val∧ wDeg C v.val ≤ 2):∀ u v:Fin n,wa83 u v→ u ∈ D2 n C ∪ D1' n C∨ v ∈ D2 n C ∪ D1' n C:=by
 intro u v hadj
 by_contra hnot
 rw [not_or,Finset.mem_union,Finset.mem_union,not_or,not_or] at hnot
 rcases hnot with ⟨⟨hu2,hu1'⟩,⟨hv2,hv1'⟩⟩
 have hu_deg1:wDeg C u.val=1:=by
  have hb:=hD_bounds u;have hne2:wDeg C u.val ≠ 2:=fun h=>hu2 (wmF.2 ⟨wmU _,h⟩);omega
 have hv_deg1:wDeg C v.val=1:=by
  have hb:=hD_bounds v;have hne2:wDeg C v.val ≠ 2:=fun h=>hv2 (wmF.2 ⟨wmU _,h⟩);omega
 obtain ⟨qzu,y_u,hqzu,hgu,hS1_u,hnbr_u,_⟩:=wa6a hn C u hmin hnn hout hsz hfun hbin hu_deg1 hu1';obtain ⟨qzv,y_v,hqzv,hgv,hS1_v,hnbr_v,_⟩:=wa6a hn C v hmin hnn hout hsz hfun hbin hv_deg1 hv1';have h1:=wa49 hn C u v hmin hnn hout hsz hfun hbin hu_deg1 hu1' hv_deg1 hv1' hadj
  qzu y_u qzv y_v hqzu hgu hS1_u hnbr_u hqzv hgv hS1_v hnbr_v
 have h2:=wa49 hn C v u hmin hnn hout hsz hfun hbin hv_deg1 hv1' hu_deg1 hu1' (Or.elim hadj Or.inr Or.inl)
  qzv y_v qzu y_u hqzv hgv hS1_v hnbr_v hqzu hgu hS1_u hnbr_u
 omega
lemma wad {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q):S1 n C (gSplit n C v)={v}:=by
 have hsp:=wa57 hn C v hmin hnn hout hsz hfun hbin
 exact wae hn C v hnn hout hsz hfun hbin (orChain n C v).1 (orChain n C v).2
  hsp.2.2.2.2.1 hsp.2.1 hsp.2.2.1
  (fun x hx=>(hsp.2.2.2.2.2.2.1 x hx).1)
  (fun x hx hne'=>by
   obtain ⟨_,hdx,qq,hqin,_,hmem⟩:=hsp.2.2.2.2.2.2.2.1 x hx hne'
   exact ⟨hdx,qq,hqin,hmem⟩)
lemma wa51 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (hv:v ∈ D1' n C):n ≤ gSplit n C v∧ gSplit n C v < C.output∧ ∃ qstar:Fin C.gates.length,gSplit n C v=n + qstar.val∧ qstar ∈ wa86 n C v true:=by
 have hsp:=wa57 hn C v hmin hnn hout hsz hfun hbin
 have hmem:=wmF.1 hv
 have hne_v:gSplit n C v ≠ v.val:=fun heq=>by
  have h1:=hmem.2.1;have h2:=hmem.2.2;change 2 ≤ wDeg C (gSplit n C v) at h2;rw [heq,h1] at h2;omega
 rcases hsp.2.2.2.2.2.1 with hv_eq | ⟨qstar,hqs_eq,hqs_T⟩
 · exact absurd hv_eq hne_v
 · exact ⟨by change gSplit n C v=n + qstar.val at hqs_eq;omega,hsp.2.2.2.2.1,qstar,hqs_eq,hqs_T⟩
lemma wa24 {n:ℕ} (hn:5 ≤ n) (C:Circuit) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (hD_bounds:∀ v:Fin n,1 ≤ wDeg C v.val∧ wDeg C v.val ≤ 2):(D2 n C).card + (D1' n C).card=(n + 1) / 2∧ (∀ v ∈ D1' n C,wDeg C (gSplit n C v)=2)∧ (∀ q,q + 1 < C.size→ (∀ v ∈ D1' n C,n + q ≠ gSplit n C v)→ wDeg C (n + q)=1):=by
 have hcov:=wa62 hn C hmin hnn hout hsz hfun hbin hD_bounds;have hcv:=wa6 hn (D2 n C ∪ D1' n C) hcov
 have hle_cv:(n + 1) / 2 ≤ (D2 n C).card + (D1' n C).card :=
  le_trans hcv (Finset.card_union_le (D2 n C) (D1' n C))
 let Q2:=(Finset.range (C.size - 1)).filter fun q=>2 ≤ wDeg C (n + q);let Q3:=(Finset.range (C.size - 1)).filter fun q=>3 ≤ wDeg C (n + q);let f:Fin n→ ℕ:=fun v=>gSplit n C v - n
 have hf_mem:∀ v ∈ D1' n C,f v ∈ Q2:=by
  intro v hv;obtain ⟨hn_le,hlt_out,_⟩:=wa51 hn C v hmin hnn hout hsz hfun hbin hv;have h2:2 ≤ wDeg C (gSplit n C v):=(wmF.1 hv).2.2;rw [wmF,Finset.mem_range]
  refine ⟨by dsimp [f];simp only [Circuit.size] at hout hlt_out ⊢;omega,?_⟩
  have heq:n + f v=gSplit n C v:=by dsimp [f];omega
  rw [heq];exact h2
 have hf_inj:Set.InjOn f (D1' n C:Set (Fin n)):=by
  intro v₁ hv₁ v₂ hv₂ heq;have hb1:=wa51 hn C v₁ hmin hnn hout hsz hfun hbin hv₁;have hb2:=wa51 hn C v₂ hmin hnn hout hsz hfun hbin hv₂
  have hgs:gSplit n C v₁=gSplit n C v₂:=by dsimp [f] at heq;omega
  have hs1:=wad hn C v₁ hmin hnn hout hsz hfun hbin
  have hs2:=wad hn C v₂ hmin hnn hout hsz hfun hbin
  rw [hgs,hs2] at hs1;exact Finset.singleton_injective hs1.symm
 have hD1'_le:(D1' n C).card ≤ Q2.card:=Finset.card_le_card_of_injOn f hf_mem hf_inj
 have hsum_in : ∑ v:Fin n,wDeg C v.val=n + (D2 n C).card:=by
  have heq:∀ v:Fin n,wDeg C v.val=1 + if v ∈ D2 n C then 1 else 0:=by
   intro v;have hb:=hD_bounds v;simp only [D2,wmF,wmU,true_and]
   split_ifs with h <;> omega
  simp_rw [heq,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,Finset.sum_boole,Nat.cast_id]
  congr 1;simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
 have hsum_gate:(C.size - 1) + Q2.card + Q3.card ≤ ∑ q ∈ Finset.range (C.size - 1),wDeg C (n + q):=by
  have hle_pt:∀ q ∈ Finset.range (C.size - 1), 1 + (if q ∈ Q2 then 1 else 0) + (if q ∈ Q3 then 1 else 0) ≤ wDeg C (n + q):=by
   intro q hq;rw [Finset.mem_range] at hq
   have h1:=wa1e C hmin hout q (by omega)
   simp only [Q2,Q3,wmF,Finset.mem_range]
   split_ifs <;> omega
  have hs:=Finset.sum_le_sum hle_pt;simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,Finset.sum_boole,Nat.cast_id] at hs
  have hi2:((Finset.range (C.size - 1)).filter fun x=>x ∈ Q2).card=Q2.card:=by rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
  have hi3:((Finset.range (C.size - 1)).filter fun x=>x ∈ Q3).card=Q3.card:=by rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
  rw [hi2,hi3] at hs;exact hs
 have hsum_tot:=wa64 hn C hbin hsz
 have hup:(D2 n C).card + Q2.card + Q3.card ≤ (n + 1) / 2:=by omega
 have hcard_eq:(D2 n C).card + (D1' n C).card=(n + 1) / 2:=by omega
 have hQ2_eq:(D1' n C).card=Q2.card:=by omega
 have hQ3_eq:Q3.card=0:=by omega
 have hQ3_empty:Q3=∅:=Finset.card_eq_zero.mp hQ3_eq
 have hdeg2:∀ v ∈ D1' n C,wDeg C (gSplit n C v)=2:=by
  intro v hv;have hf_m:=hf_mem v hv;have hn_le:=(wa51 hn C v hmin hnn hout hsz hfun hbin hv).1
  have hnot3:f v ∉ Q3:=fun h=>by rw [hQ3_empty] at h;exact wmN _ h
  simp only [Q2,Q3,wmF,Finset.mem_range] at hf_m hnot3
  have hlt3:wDeg C (n + f v) < 3:=by
   by_contra hc;exact hnot3 ⟨hf_m.1,by omega⟩
  have heq:n + f v=gSplit n C v:=by dsimp [f];omega
  rw [← heq];exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt3) hf_m.2
 have himg_eq:(D1' n C).image f=Q2:=by
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨v,hv,rfl⟩
    exact hf_mem v hv
  · rw [Finset.card_image_of_injOn hf_inj,hQ2_eq]
 have hdeg1_other:∀ q,q + 1 < C.size→ (∀ v ∈ D1' n C,n + q ≠ gSplit n C v)→ wDeg C (n + q)=1:=by
  intro q hq hnev;have h1:=wa1e C hmin hout q hq
  have hnot2:q ∉ Q2:=by
   intro hq2;rw [← himg_eq,Finset.mem_image] at hq2
   rcases hq2 with ⟨v,hv,hfv⟩
   have hn_le:=(wa51 hn C v hmin hnn hout hsz hfun hbin hv).1
   exact hnev v hv (by dsimp [f] at hfv;omega)
  simp only [Q2,wmF,Finset.mem_range] at hnot2;omega
 exact ⟨hcard_eq,hdeg2,hdeg1_other⟩
lemma wa1a {n:ℕ} (hn:5 ≤ n) (C:Circuit) (v:Fin n) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (h_true_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p true))→ n + (n + 1) / 2 - 5 ≤ D.size) (hv_D1':v ∈ D1' n C) (hdeg2:wDeg C (gSplit n C v)=2) (hdeg1_other:∀ q,q + 1 < C.size→ (∀ u ∈ D1' n C,n + q ≠ gSplit n C u)→ wDeg C (n + q)=1) (q:ℕ) (hq:q < C.size) (g:Gate) (hg:C.gates[q]?=some g) (hin:gSplit n C v ∈ g.inputs):g.op=GateOp.and:=by
 by_contra hnot_and
 have hsp:=wa57 hn C v hmin hnn hout hsz hfun hbin
 obtain ⟨hn_gs,hlt_out,qstar,hqs_eq,hqs_T⟩:=wa51 hn C v hmin hnn hout hsz hfun hbin hv_D1'
 have hne_v:(orChain n C v).1 ≠ v.val:=fun heq=>by
  change gSplit n C v=v.val at heq;omega
 obtain ⟨r₀,hr0_in,hr0_op,hr0_T,hr0_mem,hr0_le⟩:=hsp.2.2.2.2.2.2.2.2.2 hne_v;have hidx_q:C.gates[q]=g:=(wgE.1 hg).2
 have hc1_or:(C.gates[q]).op=GateOp.or:=by
  obtain ⟨g',_,_,_,hg',rfl,hop',_,_,_,_⟩:=hbin q hq;rw [hg'] at hg;cases hg
  rcases hop' with hop' | hop'
  · exact absurd hop' hnot_and
  · rw [hidx_q];exact hop'
 let c₁ : Fin C.gates.length:=⟨q,hq⟩
 have hc1_in:n + qstar.val ∈ (C.gates[c₁.val]).inputs:=by rw [← hqs_eq,hidx_q];exact hin
 have hqs_bv:(wa81 n C v true).1.getD (n + qstar.val) (Sum.inl false)=Sum.inl true :=
  (wmF.1 hqs_T).2
 have hc1_T:c₁ ∈ wa86 n C v true:=by
  have hc:=(wa27 C v true hmin.1 hbin c₁ (n + qstar.val) hc1_in hqs_bv).2.1;obtain ⟨g',_,a,b,hg',rfl,_,hin',hne',_,_⟩:=hbin c₁.val c₁.isLt;have hidx':C.gates[c₁.val]=g':=(wgE.1 hg').2
  have hg'_mem:∀ {w:ℕ},w ∈ g'.inputs→ w ∈ (C.gates[c₁.val]).inputs:=by
   intro w hw;exact Eq.mp (congrArg (fun gt:Gate=>w ∈ gt.inputs) ((wgE.1 hg').2).symm) hw
  have hin_ab:n + qstar.val=a∨ n + qstar.val=b:=by have h':=hc1_in;simp only [hidx',hin',List.mem_cons,List.mem_nil_iff,or_false] at h';exact h'
  rcases hin_ab with rfl | rfl
  · exact hc b (hg'_mem (by rw [hin'];simp)) hne'.symm (Or.inr (Or.inl ⟨hc1_or,rfl⟩))
  · exact hc a (hg'_mem (by rw [hin'];simp)) hne' (Or.inr (Or.inl ⟨hc1_or,rfl⟩))
 have hc1_nv:c₁.val ∉ (wa81 n C v true).2.2 :=
  (wa4d hn C v true hmin.1 hnn hout hsz hfun c₁ hc1_T).1
 have hqs_lt_c1:qstar.val < c₁.val:=by
  obtain ⟨g',_,a,b,hg',rfl,_,hin',_,ha,hb⟩:=hbin c₁.val c₁.isLt;have hidx':C.gates[c₁.val]=g':=(wgE.1 hg').2
  simp only [hidx',hin',List.mem_cons,List.mem_nil_iff,or_false] at hc1_in
  rcases hc1_in with h1 | h2 <;> omega
 have hR2:(wa71 C (n + qstar.val)).card=2:=by rw [wa43,← hqs_eq];exact hdeg2
 obtain ⟨e₂,he2_mem,he2_ne⟩:=Finset.exists_mem_ne (by omega:1 < (wa71 C (n + qstar.val)).card) c₁
 have he2_in:n + qstar.val ∈ (C.gates[e₂.val]).inputs:=(wa4c C _ e₂).mp he2_mem
 have he2_nv:e₂.val ∉ (wa81 n C v true).2.2 :=
  (wa27 C v true hmin.1 hbin e₂ (n + qstar.val) he2_in hqs_bv).1
 have hqs_lt_e2:qstar.val < e₂.val:=by
  obtain ⟨g',_,a,b,hg',rfl,_,hin',_,ha,hb⟩:=hbin e₂.val e₂.isLt;have hidx':C.gates[e₂.val]=g':=(wgE.1 hg').2
  simp only [hidx',hin',List.mem_cons,List.mem_nil_iff,or_false] at he2_in
  rcases he2_in with h1 | h2 <;> omega
 by_cases hqr:qstar=r₀
 · subst hqr;obtain ⟨g',_,a,b,hg',rfl,_,hin',hne',ha,hb⟩:=hbin qstar.val qstar.isLt;have hidx':C.gates[qstar.val]=g':=(wgE.1 hg').2
   have hhop:g'.op=GateOp.or:=by rw [← hidx'];exact hr0_op
   have hr0_ab:v.val=a∨ v.val=b:=by have h':=hr0_in;simp only [hidx',hin',List.mem_cons,List.mem_nil_iff,or_false] at h';exact h'
   have hy0_prop:∃ y₀ : ℕ,(C.gates[qstar.val]?=some ⟨GateOp.or,[v.val,y₀]⟩∨ C.gates[qstar.val]?=some ⟨GateOp.or,[y₀,v.val]⟩)∧ y₀ < n + qstar.val∧ y₀ ≠ v.val:=by
    rcases hr0_ab with rfl | rfl
    · refine ⟨b,Or.inl ?_,hb,hne'.symm⟩
      rw [hg'];congr 1;rcases g' with ⟨op',ins'⟩;exact congrArg₂ Gate.mk hhop hin'
    · refine ⟨a,Or.inr ?_,ha,hne'⟩
      rw [hg'];congr 1;rcases g' with ⟨op',ins'⟩;exact congrArg₂ Gate.mk hhop hin'
   obtain ⟨y₀,hgy0,hy0_lt,hy0_ne⟩:=hy0_prop
   have hS1_qs:S1 n C (n + qstar.val)={v}:=by rw [← hqs_eq];exact wad hn C v hmin hnn hout hsz hfun hbin
   have hS1_sub:S1 n C y₀ ⊆ {v}:=by
    rw [← hS1_qs]
    rcases hgy0 with hgy0 | hgy0
    · rw [S1_or C qstar.val v.val y₀ qstar.isLt hgy0 (by omega) hy0_lt]
      exact Finset.subset_union_right
    · rw [S1_or C qstar.val y₀ v.val qstar.isLt hgy0 hy0_lt (by omega)]
      exact Finset.subset_union_left
   have hy0_ge_n:n ≤ y₀:=by
    by_contra hlt_n
    have hy0_lt_n:y₀ < n:=by omega
    have hmem:(⟨y₀,hy0_lt_n⟩:Fin n) ∈ S1 n C y₀:=by
     change (⟨y₀,hy0_lt_n⟩:Fin n) ∈ S1 n C (⟨y₀,hy0_lt_n⟩:Fin n).val;rw [wa76];exact Finset.mem_singleton_self _
    have heqv:=wm1.1 (hS1_sub hmem);exact hy0_ne (congrArg Fin.val heqv)
   have hy0_not_gs:∀ u ∈ D1' n C,y₀ ≠ gSplit n C u:=by
    intro u hu hyu
    have hs:=wad hn C u hmin hnn hout hsz hfun hbin
    have hmem:u ∈ S1 n C y₀:=by rw [hyu,hs];exact Finset.mem_singleton_self _
    have heqv:=wm1.1 (hS1_sub hmem);rw [heqv,hqs_eq] at hyu;omega
   have hqy_lt:y₀ - n < C.gates.length:=by have:=qstar.isLt;omega
   let q_y:Fin C.gates.length:=⟨y₀ - n,hqy_lt⟩
   have hqy_lt_qs:q_y.val < qstar.val:=by dsimp [q_y];omega
   have hy0_deg1:wDeg C (n + q_y.val)=1:=by
    have hn_qy:n + q_y.val=y₀:=by dsimp [q_y];omega
    have hn_sub:n + (y₀ - n)=y₀:=by omega
    have hqy_sub:n + q_y.val=n + (y₀ - n):=rfl;rw [hqy_sub]
    exact hdeg1_other (y₀ - n) (by simp only [Circuit.size] at *;have:=qstar.isLt;omega)
     (fun u hu=>by rw [hn_sub];exact hy0_not_gs u hu)
   have hne_T:(wa86 n C v true).Nonempty:=⟨c₁,hc1_T⟩;let q_max:=(wa86 n C v true).max' hne_T;have hqm_mem:q_max ∈ wa86 n C v true:=Finset.max'_mem _ hne_T;have hc1_le_qm:c₁.val ≤ q_max.val:=Finset.le_max' _ c₁ hc1_T
   obtain ⟨e_max,hqm_lt_em,hem_in,hem_nv⟩ :=
    wa3b hn C v true hmin hnn hout hsz hfun hbin q_max hqm_mem
   have hem_not_T:e_max ∉ wa86 n C v true:=fun h=>by
    have hle:=Finset.le_max' (wa86 n C v true) e_max h;change e_max.val ≤ q_max.val at hle;omega
   have hem_ne_e2:e_max ≠ e₂:=fun heq=>by
    rw [heq] at hem_in
    exact hem_not_T (heq ▸ wa7 C v true hmin.1 hbin qstar q_max e₂ (Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hqs_lt_c1 hc1_le_qm))) hr0_T hqm_mem he2_in hem_in)
   have hbd_out:C.output < n + C.gates.length:=by
    change C.output < n + C.size
    have hpos:0 < C.size:=by rw [hsz];exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide:1 < 5) (Nat.le_trans hn (Nat.le_add_right n ((n + 1) / 2))))
    rw [hout];exact Nat.sub_lt (Nat.add_pos_right n hpos) Nat.zero_lt_one
   obtain ⟨out',hout'⟩:=wa56 hn C v true hmin.1 hnn hbd_out hfun;let full:=wa72 n (wa84 v.val true) 0 C.gates (wa79 n (wa84 v.val true),[],[]);change full.1.getD C.output (Sum.inl false)=Sum.inr out' at hout';have hqy_kill:q_y.val ∉ full.2.2 ∨
    ∃ j:Fin full.2.2.length,full.2.2[j.val]=q_y.val ∧
     n + j.val ∉ wa65 n full.2.1 out' (j.val + 1):=by
    by_cases hmem_full:q_y.val ∈ full.2.2
    · refine Or.inr ?_
      obtain ⟨j,hj,hj_eq⟩:=List.mem_iff_getElem.mp hmem_full;have hnot_need:=wa0 n C (wa84 v.val true) hmin.1 out' hout'
       {q_y.val}
       (fun qq hqq=>by rw [wm1.1 hqq];simp only [Circuit.size] at hout;omega)
       (fun qq hqq q' hq' hq_in=>by
        rw [wm1.1 hqq] at hq_in
        have h1:C.gates[q']?=some C.gates[q']:=wgE.2 ⟨hq',rfl⟩;have h2:C.gates[qstar.val]?=some (C.gates[qstar.val]):=wgE.2 ⟨qstar.isLt,rfl⟩
        have hqy_in_qs:n + q_y.val ∈ (C.gates[qstar.val]).inputs:=by
         have hqy_eq:n + q_y.val=y₀:=by dsimp [q_y];omega
         rw [hqy_eq]
         rcases hgy0 with hgy0 | hgy0
         · have he:(C.gates[qstar.val]?).map Gate.inputs=some [v.val,y₀]:=by rw [hgy0];rfl
           rw [wgE.2 ⟨qstar.isLt,rfl⟩] at he;simp only [Option.map_some,Option.some.injEq] at he;rw [he];simp
         · have he:(C.gates[qstar.val]?).map Gate.inputs=some [y₀,v.val]:=by rw [hgy0];rfl
           rw [wgE.2 ⟨qstar.isLt,rfl⟩] at he;simp only [Option.map_some,Option.some.injEq] at he;rw [he];simp
        have heq:=wa3 C (n + q_y.val) q' qstar.val hy0_deg1 _ _ h1 hq_in h2 hqy_in_qs
        exact Or.inl ⟨true,by rw [heq];exact hqs_bv⟩)
       j q_y.val hj hj_eq (Finset.mem_singleton_self _)
      exact ⟨⟨j,hj⟩,hj_eq,hnot_need⟩
    · exact Or.inl hmem_full
   have h5set:({q_y,qstar,c₁,e_max,e₂} : Finset (Fin C.gates.length)).card=5:=by
    have hm1:q_y ∉ ({qstar,c₁,e_max,e₂} : Finset _):=by simp only [wmI,wm1];rintro (h | h | h | h) <;> omega
    have hm2:qstar ∉ ({c₁,e_max,e₂} : Finset _):=by simp only [wmI,wm1];rintro (h | h | h) <;> omega
    have hm3:c₁ ∉ ({e_max,e₂} : Finset _):=by
     simp only [wmI,wm1];rintro (h | h);omega;exact he2_ne h.symm
    rw [Finset.card_insert_of_notMem hm1,Finset.card_insert_of_notMem hm2,Finset.card_insert_of_notMem hm3,Finset.card_pair hem_ne_e2]
   have hle4:=wa10 hn C v hmin.1 hnn hout hsz hfun h_true_lo out' hout'
    {q_y,qstar,c₁,e_max,e₂} (fun qq hqq=>by
     simp only [wmI,wm1] at hqq
     rcases hqq with rfl | rfl | rfl | rfl | rfl
     · rcases hqy_kill with h1 | ⟨j,hj1,hj2⟩
       · exact Or.inl h1
       · exact Or.inr ⟨j,hj1,hj2⟩
     · exact Or.inl (wa4d hn C v true hmin.1 hnn hout hsz hfun qq hr0_T).1
     · exact Or.inl hc1_nv
     · exact Or.inl hem_nv
     · exact Or.inl he2_nv)
   omega
 · have hr0_in_S:n + r₀.val ∈ (orChain n C v).2:=hr0_mem
   have hr0_lt_qs:r₀.val < qstar.val:=by
    have h1:=(hsp.2.2.2.2.2.2.1 (n + r₀.val) hr0_in_S).1;change n + r₀.val ≤ gSplit n C v at h1;rw [hqs_eq] at h1;have hne_fin:r₀.val ≠ qstar.val:=fun h=>hqr (Fin.ext h).symm;omega
   have hsub3 : {r₀,qstar,c₁} ⊆ wa86 n C v true:=by
    intro x hx;simp only [wmI,wm1] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
   have hm1:r₀ ∉ ({qstar,c₁} : Finset _):=by simp only [wmI,wm1];rintro (h | h) <;> omega
   have hpr:({qstar,c₁} : Finset (Fin C.gates.length)).card=2 :=
    Finset.card_pair (Fin.ne_of_val_ne (Nat.ne_of_lt hqs_lt_c1))
   have hc3:({r₀,qstar,c₁} : Finset (Fin C.gates.length)).card=3:=by rw [Finset.card_insert_of_notMem hm1,hpr]
   have h3:3 ≤ (wa86 n C v true).card:=hc3 ▸ Finset.card_le_card hsub3;have hT_le3:=wa4 hn C v hmin hnn hout hsz hfun hbin h_true_lo
   have hT_eq3:wa86 n C v true={r₀,qstar,c₁} :=
    (Finset.eq_of_subset_of_card_le hsub3 (hc3 ▸ hT_le3)).symm
   obtain ⟨e₁,hc1_lt_e1,he1_in,he1_nv⟩ :=
    wa3b hn C v true hmin hnn hout hsz hfun hbin c₁ hc1_T
   have he1_not_T:e₁ ∉ wa86 n C v true:=by
    rw [hT_eq3]
    simp only [wmI,wm1];rintro (h | h | h) <;> omega
   have he2_not_T:e₂ ∉ wa86 n C v true:=by
    rw [hT_eq3];simp only [wmI,wm1];rintro (h | h | h)
    · omega
    · omega
    · exact he2_ne h
   have he1_ne_e2:e₁ ≠ e₂:=fun heq=>by
    rw [heq] at he1_in
    exact he2_not_T (wa7 C v true hmin.1 hbin qstar c₁ e₂ (Fin.ne_of_val_ne (Nat.ne_of_lt hqs_lt_c1)) hqs_T hc1_T he2_in he1_in)
   have h5set:({r₀,qstar,c₁,e₁,e₂} : Finset (Fin C.gates.length)).card=5:=by
    have hm1:r₀ ∉ ({qstar,c₁,e₁,e₂} : Finset _):=by simp only [wmI,wm1];rintro (h | h | h | h) <;> omega
    have hm2:qstar ∉ ({c₁,e₁,e₂} : Finset _):=by simp only [wmI,wm1];rintro (h | h | h) <;> omega
    have hm3:c₁ ∉ ({e₁,e₂} : Finset _):=by
     simp only [wmI,wm1];rintro (h | h);omega;exact he2_ne h.symm
    rw [Finset.card_insert_of_notMem hm1,Finset.card_insert_of_notMem hm2,Finset.card_insert_of_notMem hm3,Finset.card_pair he1_ne_e2]
   have hle4:=wac hn C v hmin.1 hnn hout hsz hfun h_true_lo
    {r₀,qstar,c₁,e₁,e₂} (fun qq hqq=>by
     simp only [wmI,wm1] at hqq
     rcases hqq with rfl | rfl | rfl | rfl | rfl
     · exact (wa4d hn C v true hmin.1 hnn hout hsz hfun qq hr0_T).1
     · exact (wa4d hn C v true hmin.1 hnn hout hsz hfun qq hqs_T).1
     · exact hc1_nv
     · exact he1_nv
     · exact he2_nv)
   omega
theorem wire_class_stageA {n:ℕ} (hn:5 ≤ n) (C:Circuit) (hmin:IsMinimalCircuit n C) (hnn:∀ g ∈ C.gates,g.op ≠ GateOp.not) (hout:C.output=n + C.size - 1) (hsz:C.size=n + (n + 1) / 2 - 1) (hfun:circuitFun n C=cycF n) (hbin:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧ g.op=op∧ (op=GateOp.and∨ op=GateOp.or)∧ g.inputs=[a,b]∧ a ≠ b∧ a < n + q∧ b < n + q) (h_false_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p false))→ n + (n + 1) / 2 - 4 ≤ D.size) (h_true_lo:∀ p:Fin n,∀ D:Circuit,FanInTwo D→ circuitFun n D=(fun x=>cycF n (Function.update x p true))→ n + (n + 1) / 2 - 5 ≤ D.size):(∀ v:Fin n,1 ≤ wDeg C v.val∧ wDeg C v.val ≤ 2)∧ (∃ (D₁':Finset (Fin n)) (gSplit_fn:Fin n→ ℕ),(∀ v ∈ D₁',wDeg C v.val=1∧ n ≤ gSplit_fn v∧ gSplit_fn v < C.output∧ wDeg C (gSplit_fn v)=2∧ S1 n C (gSplit_fn v)={v}∧ ∀ q < C.size,∀ g,C.gates[q]?=some g→ gSplit_fn v ∈ g.inputs→ g.op=GateOp.and)∧ (∀ q,q + 1 < C.size→ (∀ v ∈ D₁',n + q ≠ gSplit_fn v)→ wDeg C (n + q)=1)∧ (D2 n C).card + D₁'.card=(n + 1) / 2∧ (∀ u v:Fin n,((u.val + 1) % n=v.val∨ (v.val + 1) % n=u.val)→ u ∈ D2 n C ∪ D₁'∨ v ∈ D2 n C ∪ D₁')∧ (∀ c:Fin n,wDeg C c.val=1→ c ∉ D₁'→ ∃ qz w_c y_c:ℕ,qz < C.size∧ (C.gates[qz]?=some ⟨GateOp.and,[w_c,y_c]⟩∨ C.gates[qz]?=some ⟨GateOp.and,[y_c,w_c]⟩)∧ S1 n C w_c={c}∧ (∀ u:Fin n,((c.val + 1) % n=u.val∨ (u.val + 1) % n=c.val)→ u ∈ S1 n C y_c)∧ c ∉ S1 n C y_c)):=by
 have hDb:=wa1d hn C hmin hnn hout hsz hfun hbin h_false_lo h_true_lo;obtain ⟨hcard_eq,hdeg2,hdeg1_other⟩:=wa24 hn C hmin hnn hout hsz hfun hbin hDb;refine ⟨hDb,D1' n C,gSplit n C,?_,hdeg1_other,hcard_eq,?_,?_⟩
 · intro v hv;have hb:=wa51 hn C v hmin hnn hout hsz hfun hbin hv;exact ⟨(wmF.1 hv).2.1,hb.1,hb.2.1,hdeg2 v hv,wad hn C v hmin hnn hout hsz hfun hbin,fun q hq g hg hin=>wa1a hn C v hmin hnn hout hsz hfun hbin h_true_lo hv (hdeg2 v hv) hdeg1_other q hq g hg hin⟩
 · exact wa62 hn C hmin hnn hout hsz hfun hbin hDb
 · intro c hc_deg hc_not
   obtain ⟨qz,y_c,hqz,hg_c,hS1_wc,hnbr_c,hc_ny⟩ :=
    wa6a hn C c hmin hnn hout hsz hfun hbin hc_deg hc_not
   exact ⟨qz,(orChain n C c).1,y_c,hqz,hg_c,hS1_wc,hnbr_c,hc_ny⟩
end WireClass
end PEqualNP.Outside.L_meta_314_aux
namespace PEqualNP.Outside.L_meta_314_aux.WirePart2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset Relation
abbrev mF:=@Finset.mem_filter
abbrev mS:=@Finset.mem_sdiff
abbrev m1:=@Finset.mem_singleton
abbrev mI:=@Finset.mem_insert
abbrev mU:=@Finset.mem_univ
abbrev mG:=@Finset.mem_image
abbrev mR:=@Finset.mem_range
abbrev mE:=@Finset.mem_erase
abbrev mN:=@Finset.notMem_empty
abbrev oI:=@Option.some.inj
abbrev zL:=@Nat.zero_le
abbrev cP0:=@Finset.card_pair
abbrev sC:=@Finset.sum_congr
abbrev s1s:=@Finset.single_le_sum
abbrev aSe:=@Finset.add_sum_erase
abbrev bAt:=@Bool.and_eq_true
abbrev bOt:=@Bool.or_eq_true
abbrev IsBin (n:ℕ) (C:Circuit):Prop :=
 ∀ q<C.size,∃ g op a b,C.gates[q]?=some g∧g.op=op ∧
  (op=.and∨op=.or)∧g.inputs=[a,b]∧a≠b∧a<n+q∧b<n+q
def sW (w:List Bool) (g:Gate):List Bool :=
 w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma fsL (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i<w.length) :
  (gs.foldl sW w).getD i false=w.getD i false:= by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih => rw [List.foldl_cons,ih (sW w g) (by simp [sW];omega)];simp [sW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma fsG (gs:List Gate) (w:List Bool) (j:ℕ) (hj:j<gs.length) :
  (gs.foldl sW w).getD (w.length+j) false =
   (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
    if i<w.length+j then (gs.foldl sW w).getD i false else false):= by
 induction gs generalizing w j with
 | nil=>simp at hj
 | cons g gs ih =>
  rw [List.foldl_cons];cases j with
  | zero =>
   rw [Nat.add_zero,fsL gs (sW w g) w.length (by simp [sW])];simp only [List.getElem_cons_zero];have h2:(sW w g).getD w.length false =
     g.op.eval (g.inputs.map fun i=>w.getD i false):= by
    simp [sW,List.getD_eq_getElem?_getD]
   rw [h2]
   congr 1
   apply List.map_congr_left;intro i _;by_cases hi:i<w.length;{rw [ite_eq_left_iff.2 (fun h=>(h hi).elim),fsL gs (sW w g) i (by simp [sW];omega)];simp [sW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]};{rw [ite_eq_right_iff.2 (fun h=>(hi h).elim)];simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_lt hi)]}
  | succ j =>
   have hj':j<gs.length:= by {simpa using hj};have key:=ih (sW w g) j hj';have hl:(sW w g).length=w.length+1:= by {simp [sW]};rw [hl] at key;have e:w.length+(j+1)=w.length+1+j:= by omega
   simp only [List.getElem_cons_succ];rw [e];exact key
def wv {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (w:ℕ):Bool :=
 (C.wires (List.ofFn x)).getD w false
lemma wvI {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (i:Fin n) :
  wv C x i.val=x i:= by
 unfold wv;change (C.gates.foldl sW (List.ofFn x)).getD i.val false=x i;rw [fsL C.gates (List.ofFn x) i.val (by simp)];simp [List.getD_eq_getElem?_getD]
lemma wvG {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (q:ℕ) (hq:q<C.gates.length) :
  wv C x (n+q)=(C.gates[q]).op.eval ((C.gates[q]).inputs.map fun i =>
   if i<n+q then wv C x i else false):= by
 unfold wv;change (C.gates.foldl sW (List.ofFn x)).getD (n+q) false =
  (C.gates[q]).op.eval ((C.gates[q]).inputs.map fun i =>
   if i<n+q then (C.gates.foldl sW (List.ofFn x)).getD i false else false)
 have h:=fsG C.gates (List.ofFn x) q hq;simpa only [List.length_ofFn] using h
lemma wvA {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (q a b:ℕ) (hq:q<C.gates.length)
  (hg:C.gates[q]?=some ⟨.and,[a,b]⟩) (ha:a<n+q) (hb:b<n+q) :
  wv C x (n+q)=(wv C x a&&wv C x b):= by
 rw [wvG C x q hq];have hget:C.gates[q]=⟨.and,[a,b]⟩:= by rw [List.getElem?_eq_getElem hq] at hg;exact oI hg
 rw [hget];simp [GateOp.eval,ha,hb]
lemma wvR {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (q a b:ℕ) (hq:q<C.gates.length)
  (hg:C.gates[q]?=some ⟨.or,[a,b]⟩) (ha:a<n+q) (hb:b<n+q) :
  wv C x (n+q)=(wv C x a||wv C x b):= by
 rw [wvG C x q hq];have hget:C.gates[q]=⟨.or,[a,b]⟩:= by rw [List.getElem?_eq_getElem hq] at hg;exact oI hg
 rw [hget];simp [GateOp.eval,ha,hb]
lemma wvM {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (x y:Fin n→ Bool) (hxy:∀ i:Fin n,x i=true→ y i=true) :
  ∀ w<n+C.size,wv C x w=true→ wv C y w=true:= by
 intro w;induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hw hx;by_cases hwn:w<n;{let i:Fin n:=⟨w,hwn⟩;have h1:wv C x i.val=x i:=wvI C x i;have h2:wv C y i.val=y i:=wvI C y i;exact h2.trans (hxy i (h1.symm.trans hx))};{
   let q:=w - n;have hq:q<C.size:= by {omega};have hw_eq:w=n+q:= by {omega};rw [hw_eq] at hx ⊢;obtain ⟨g,op,a,b,hg,rfl,hop,hin,_,ha,hb⟩:=hb q hq;have hg':C.gates[q]?=some ⟨g.op,[a,b]⟩:= by cases g;simp only at hin;subst hin;exact hg
   rcases hop with hop | hop;{rw [hop] at hg';rw [wvA C x q a b hq hg' ha hb,bAt] at hx;rw [wvA C y q a b hq hg' ha hb,bAt];exact ⟨ih a (by omega) (by omega) hx.1,ih b (by omega) (by omega) hx.2⟩};{
    rw [hop] at hg';rw [wvR C x q a b hq hg' ha hb,bOt] at hx;rw [wvR C y q a b hq hg' ha hb,bOt];rcases hx with h1 | h2;{exact Or.inl (ih a (by omega) (by omega) h1)};{exact Or.inr (ih b (by omega) (by omega) h2)}
   }
  }
abbrev cA {n:ℕ} (u v:Fin n):Prop :=
 (u.val+1)%n=v.val∨(v.val+1)%n=u.val
def oH {n:ℕ} (u:Fin n):Fin n→ Bool:=fun i=>decide (i=u)
def pI {n:ℕ} (u v:Fin n):Fin n→ Bool:=fun i=>decide (i=u∨i=v)
def cF (n:ℕ) (x:Fin n→ Bool):Bool :=
 decide (∃ i j:Fin n,(i.val+1)%n=j.val∧x i=true∧x j=true)
def S1 (n:ℕ) (C:Circuit) (w:ℕ):Finset (Fin n) :=
 univ.filter fun u:Fin n=>wv C (oH u) w=true
def wD (C:Circuit) (w:ℕ):ℕ :=
 (C.gates.filter fun g=>decide (w∈g.inputs)).length
def D2 (n:ℕ) (C:Circuit):Finset (Fin n) :=
 univ.filter fun v:Fin n=>wD C v.val=2
abbrev IS (n:ℕ) (C:Circuit):Finset (Fin n):=univ \ D2 n C
def cN {n:ℕ} (hn:0<n) (v:Fin n):Fin n :=
 ⟨(v.val+1)%n,Nat.mod_lt _ hn⟩
def cP {n:ℕ} (hn:0<n) (v:Fin n):Fin n :=
 ⟨(v.val+n - 1)%n,Nat.mod_lt _ hn⟩
lemma cnV {n:ℕ} (hn:0<n) (v:Fin n) :
  (cN hn v).val=if v.val+1=n then 0 else v.val+1:= by
 simp only [cN];have hv:=v.2
 split_ifs with h
 {rw [h,Nat.mod_self]};{exact Nat.mod_eq_of_lt (by omega)}
lemma cpV {n:ℕ} (hn:0<n) (v:Fin n) :
  (cP hn v).val=if v.val=0 then n - 1 else v.val - 1:= by
 simp only [cP];have hv:=v.2
 split_ifs with h
 {rw [h,zero_add,Nat.mod_eq_of_lt (by omega)]};{
  rw [show v.val+n - 1=(v.val - 1)+n by omega,Nat.add_mod_right,
   Nat.mod_eq_of_lt (by omega)]
 }
lemma cnP {n:ℕ} (hn:0<n) (v:Fin n) :
  cN hn (cP hn v)=v:= by
 apply Fin.ext;have hv:=v.2;rw [cnV,cpV]
 split_ifs <;> omega
lemma cpN {n:ℕ} (hn:0<n) (v:Fin n) :
  cP hn (cN hn v)=v:= by
 apply Fin.ext;have hv:=v.2;rw [cpV,cnV];by_cases h:v.val+1=n;{simp only [h,↓reduceIte];omega};{simp only [h,↓reduceIte,Nat.add_eq_zero_iff,one_ne_zero,and_false];omega}
lemma cnA {n:ℕ} (hn:0<n) (v:Fin n):cA v (cN hn v) :=
 Or.inl rfl
lemma cpA {n:ℕ} (hn:0<n) (v:Fin n):cA v (cP hn v) :=
 Or.inr (congrArg Fin.val (cnP hn v))
lemma cnNP {n:ℕ} (hn:5≤n) (v:Fin n) :
  cN (by omega) v≠cP (by omega) v:= by
 intro h;have h1:=congrArg Fin.val h;have hv:=v.2;rw [cnV,cpV] at h1
 split_ifs at h1 <;> omega
lemma caI {n:ℕ} (hn:5≤n) (v u:Fin n) :
  cA v u↔u=cN (by omega) v∨u=cP (by omega) v:= by
 constructor;{
  rintro (h | h);{left;exact Fin.ext h.symm};{right;have hv:cN (by omega) u=v:=Fin.ext h;rw [← hv,cpN (by omega) u]}
 }
 {rintro (rfl | rfl);{exact cnA (by omega) v};{exact cpA (by omega) v}}
lemma caR {n:ℕ} (hn:5≤n) (v:Fin n):¬ cA v v:= by
 rintro (h | h) <;>
 {
  have h':(cN (by omega) v).val=v.val:=h;have hv:=v.2;rw [cnV] at h'
  split_ifs at h' <;> omega
 }
lemma cnJ {n:ℕ} (hn:0<n):Function.Injective (cN hn):= by
 intro a b h;have h1:=congrArg (cP hn) h;rwa [cpN hn a,cpN hn b] at h1
lemma cpJ {n:ℕ} (hn:0<n):Function.Injective (cP hn):= by
 intro a b h;have h1:=congrArg (cN hn) h;rwa [cnP hn a,cnP hn b] at h1
lemma caC {n:ℕ} (hn:5≤n) {c c':Fin n}
  (h1:cA c' (cN (by omega) c)) (h2:cA c' (cP (by omega) c)) :
  c'=c:= by
 have h1':=(caI hn (cN (by omega) c) c').1 (Or.symm h1);have h2':=(caI hn (cP (by omega) c) c').1 (Or.symm h2);rw [cpN (by omega) c] at h1';rw [cnP (by omega) c] at h2';rcases h1' with rfl | rfl;{
  rcases h2' with h | h;{exact h};{
   exfalso;have hv:=congrArg Fin.val h;have hc:=c.2;simp only [cnV,cpV] at hv
   split_ifs at hv <;> omega
  }
 }
 {rfl}
lemma cnPP {n:ℕ} (hn:5≤n) (c:Fin n) :
  cN (by omega) c≠cP (by omega) (cP (by omega) c):= by
 intro h;have hv:=congrArg Fin.val h;have hc:=c.2;simp only [cnV,cpV] at hv
 split_ifs at hv <;> omega
lemma cpNA {n:ℕ} (hn:5≤n) {u v:Fin n}
  (huv:(u.val+1)%n=v.val) :
  cP (by omega) u≠cN (by omega) v:= by
 intro h;have hv_eq:v=cN (by omega) u:=Fin.ext huv.symm;rw [hv_eq] at h;have hv:=congrArg Fin.val h;have hu:=u.2;simp only [cpV,cnV] at hv
 split_ifs at hv <;> omega
lemma cf1 {n:ℕ} (hn:5≤n) (u:Fin n):cF n (oH u)=false:= by
 rw [Bool.eq_false_iff];intro h;simp only [cF,decide_eq_true_eq,oH] at h;obtain ⟨i,j,hij,hi,hj⟩:=h;rw [hi,hj] at hij;exact caR hn u (Or.inl hij)
lemma cf2 {n:ℕ} (hn:5≤n) (u v:Fin n) :
  cF n (pI u v)=true↔cA u v:= by
 simp only [cF,decide_eq_true_eq,pI];constructor;{
  rintro ⟨i,j,hij,hi,hj⟩;rcases hi with hi | hi <;> rcases hj with hj | hj;{rw [hi,hj] at hij;exact (caR hn u (Or.inl hij)).elim};{rw [hi,hj] at hij;exact Or.inl hij};{rw [hi,hj] at hij;exact Or.inr hij};{rw [hi,hj] at hij;exact (caR hn v (Or.inl hij)).elim}
 }
 {rintro (h | h);{exact ⟨u,v,h,Or.inl rfl,Or.inr rfl⟩};{exact ⟨v,u,h,Or.inr rfl,Or.inl rfl⟩}}
lemma s1I {n:ℕ} (C:Circuit) (v:Fin n):S1 n C v.val={v}:= by
 ext u
 simp [S1,wvI,oH,eq_comm]
lemma s1A (n:ℕ) (C:Circuit) (q a b:ℕ) (hq:q<C.gates.length)
  (hg:C.gates[q]?=some ⟨.and,[a,b]⟩) (ha:a<n+q) (hb:b<n+q) :
  S1 n C (n+q)=S1 n C a∩S1 n C b:= by
 ext u
 simp [S1,wvA C (oH u) q a b hq hg ha hb]
lemma s1O (n:ℕ) (C:Circuit) (q a b:ℕ) (hq:q<C.gates.length)
  (hg:C.gates[q]?=some ⟨.or,[a,b]⟩) (ha:a<n+q) (hb:b<n+q) :
  S1 n C (n+q)=S1 n C a∪S1 n C b:= by
 ext u
 simp [S1,wvR C (oH u) q a b hq hg ha hb]
lemma wdR (C:Circuit) (w:ℕ) :
  wD C w=((range C.size).filter fun q =>
   ∃ g,C.gates[q]?=some g∧w∈g.inputs).card:= by
 unfold wD Circuit.size;suffices h:∀ gs:List Gate,(gs.filter fun g=>decide (w∈g.inputs)).length =
   ((range gs.length).filter fun q=>∃ g,gs[q]?=some g∧w∈g.inputs).card from h C.gates
 intro gs;induction gs using List.reverseRecOn with
 | nil=>simp
 | append_singleton gs g ih =>
  rw [List.filter_append,List.length_append,List.length_append,List.length_singleton,
   range_add_one,filter_insert]
  have hpr:(range gs.length).filter (fun q=>∃ g',(gs++[g])[q]?=some g'∧w∈g'.inputs) =
    (range gs.length).filter (fun q=>∃ g',gs[q]?=some g'∧w∈g'.inputs):= by
   apply filter_congr;intro q hq;rw [List.getElem?_append_left (mR.1 hq)]
  rw [hpr];have hls:(∃ g',(gs++[g])[gs.length]?=some g'∧w∈g'.inputs)↔w∈g.inputs:= by simp
  by_cases hw:w∈g.inputs;{
   have hMm:gs.length∉(range gs.length).filter (fun q=>∃ g',gs[q]?=some g'∧w∈g'.inputs):= by {simp};have hcd:(∃ g',(gs++[g])[gs.length]?=some g'∧w∈g'.inputs):=hls.2 hw;simp only [hcd,↓reduceIte,card_insert_of_notMem hMm,← ih,List.filter_cons,hw,
    decide_true,List.length_cons,List.filter_nil,List.length_nil,zero_add]
  }
  {
   have hcd:¬ (∃ g',(gs++[g])[gs.length]?=some g'∧w∈g'.inputs):=fun h=>hw (hls.1 h);simp only [hcd,↓reduceIte,← ih,List.filter_cons,hw,decide_false,Bool.false_eq_true,
    List.filter_nil,List.length_nil,add_zero]
  }
lemma uR1 (C:Circuit) (w q1 q2:ℕ) (hdeg:wD C w=1)
  (g1 g2:Gate) (hg1:C.gates[q1]?=some g1) (hw1:w∈g1.inputs)
  (hg2:C.gates[q2]?=some g2) (hw2:w∈g2.inputs):q1=q2:= by
 rw [wdR] at hdeg;have h1:q1∈(range C.size).filter (fun q=>∃ g,C.gates[q]?=some g∧w∈g.inputs) :=
  mF.2 ⟨mR.2 (List.getElem?_eq_some_iff.1 hg1).1,g1,hg1,hw1⟩
 have h2:q2∈(range C.size).filter (fun q=>∃ g,C.gates[q]?=some g∧w∈g.inputs) :=
  mF.2 ⟨mR.2 (List.getElem?_eq_some_iff.1 hg2).1,g2,hg2,hw2⟩
 exact card_le_one.1 (le_of_eq hdeg) q1 h1 q2 h2
lemma eR1 (C:Circuit) (w:ℕ) (hp:1≤wD C w) :
  ∃ q<C.size,∃ g,C.gates[q]?=some g∧w∈g.inputs:= by
 rw [wdR] at hp;obtain ⟨q,hq⟩:=card_pos.1 (Nat.lt_of_lt_of_le Nat.zero_lt_one hp);obtain ⟨ql,g,hg,hw⟩:=mF.1 hq;exact ⟨q,mR.1 ql,g,hg,hw⟩
def eO {n:ℕ} (S:Finset ℕ) (x:Fin n→ Bool):Bool :=
 decide (∃ i j:Fin n,i.val∈S∧(i.val+1)%n=j.val∧x i=true∧x j=true)
def wC (n:ℕ) (C:Circuit) (w:ℕ):Prop :=
 (∃ S:Finset ℕ,S.Nonempty∧(∀ i∈S,i<n)∧∀ x:Fin n→ Bool,wv C x w=eO S x) ∨
 (∃ a c b:Fin n,(a.val+1)%n=c.val∧(c.val+1)%n=b.val ∧
  ∀ x:Fin n→ Bool,wv C x w=(x a||x b)) ∨
 (∃ i j k:Fin n,(i.val+1)%n=j.val∧((j.val+1)%n=k.val∨(k.val+1)%n=i.val) ∧
  ∀ x:Fin n→ Bool,wv C x w=((x i&&x j)||x k))
def iS (n:ℕ) (C:Circuit) (w r:ℕ):Prop :=
 ReflTransGen (fun u v=>∃ q<C.size,∃ g,C.gates[q]?=some g∧v=n+q∧u∈g.inputs) w r
lemma isL {n:ℕ} (C:Circuit) (hb:IsBin n C)
  {w r:ℕ} (h:iS n C w r):w≤r:= by
 induction h with
 | refl=>exact le_rfl
 | tail _ hSt0 ih =>
  obtain ⟨q,hq,g,hg,rfl,hin⟩:=hSt0;obtain ⟨g',op,a,b,hg',_,_,hin',_,ha,hb⟩:=hb q hq;rw [hg] at hg';obtain rfl:=oI hg';rw [hin'] at hin;simp at hin;rcases hin with rfl | rfl <;> omega
lemma isSt {n:ℕ} (C:Circuit) (q:ℕ) (hq:q<C.size) (g:Gate)
  (hg:C.gates[q]?=some g) (u:ℕ) (hu:u∈g.inputs) :
  iS n C u (n+q) :=
 ReflTransGen.single ⟨q,hq,g,hg,rfl,hu⟩
lemma isO {n:ℕ} (C:Circuit) (ho:C.output=n+C.size - 1) (hb:IsBin n C)
  (hd1:∀ q,q+1<C.size→ wD C (n+q)=1) (hp:0<C.size) :
  ∀ q<C.size,iS n C (n+q) C.output:= by
 suffices h:∀ d q,q<C.size→ C.size - 1 - q≤d→ iS n C (n+q) C.output by
  intro q hq;exact h (C.size - 1 - q) q hq le_rfl
 intro d;induction d with
 | zero => intro q hq hd;rw [show n+q=C.output by omega];exact ReflTransGen.refl
 | succ d ih =>
  intro q hq hd;by_cases hls:q+1=C.size;{rw [show n+q=C.output by omega];exact ReflTransGen.refl};{
   have h1:=hd1 q (by omega);obtain ⟨r,rl,gr,hgr,hqin⟩:=eR1 C (n+q) (by omega);have hqr:q<r:= by
    obtain ⟨g',_,a,b,hg',_,_,hin',_,ha,hb⟩:=hb r rl;rw [hgr] at hg';obtain rfl:=oI hg';rw [hin'] at hqin;simp at hqin;rcases hqin with h | h <;> omega
   exact ReflTransGen.head ⟨r,rl,gr,hgr,rfl,hqin⟩ (ih r rl (by omega))
  }
def gL (C:Circuit) (q:ℕ):ℕ :=
 match C.gates[q]? with
 | some g=>g.inputs.getD 0 0
 | none=>0
def gR (C:Circuit) (q:ℕ):ℕ :=
 match C.gates[q]? with
 | some g=>g.inputs.getD 1 0
 | none=>0
lemma hbG {n:ℕ} (C:Circuit) (hb:IsBin n C) (q:ℕ) (hq:q<C.size) :
  ∃ op,C.gates[q]?=some ⟨op,[gL C q,gR C q]⟩ ∧
   (op=.and∨op=.or) ∧
   gL C q≠gR C q∧gL C q<n+q∧gR C q<n+q:= by
 obtain ⟨g,op,a,b,hg,rfl,hop,hin,hab,ha,hb⟩:=hb q hq;have hl:gL C q=a:= by simp [gL,hg,hin]
 have hr:gR C q=b:= by {simp [gR,hg,hin]};rw [hl,hr];have hg':C.gates[q]?=some ⟨g.op,[a,b]⟩:= by cases g;simp only at hin;subst hin;exact hg
 exact ⟨g.op,hg',hop,hab,ha,hb⟩
lemma isS {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (v:Fin n):∀ w<n+C.size,v∈S1 n C w→ iS n C v.val w:= by
 intro w;induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro wl hvw;by_cases hwn:w<n;{have hS:=s1I C ⟨w,hwn⟩;rw [hS,m1] at hvw;rw [congrArg Fin.val hvw];exact ReflTransGen.refl};{
   let q:=w - n;have hq:q<C.size:= by {omega};have we:w=n+q:= by {omega};rw [we] at hvw ⊢;obtain ⟨op,hg,hop,_,hl,hr⟩:=hbG C hb q hq;have hSL:iS n C (gL C q) (n+q) :=
    isSt C q hq ⟨op,[gL C q,gR C q]⟩ hg (gL C q) (by simp)
   have hSR:iS n C (gR C q) (n+q) :=
    isSt C q hq ⟨op,[gL C q,gR C q]⟩ hg (gR C q) (by simp)
   rcases hop with rfl | rfl;{rw [s1A n C q (gL C q) (gR C q) hq hg hl hr,mem_inter] at hvw;exact ReflTransGen.trans (ih (gL C q) (by omega) (by omega) hvw.1) hSL};{
    rw [s1O n C q (gL C q) (gR C q) hq hg hl hr,mem_union] at hvw;rcases hvw with h1 | h2;{exact ReflTransGen.trans (ih (gL C q) (by omega) (by omega) h1) hSL};{exact ReflTransGen.trans (ih (gR C q) (by omega) (by omega) h2) hSR}
   }
  }
lemma s1D {n:ℕ} (C:Circuit) (hn:5≤n)
  (hf:circuitFun n C=cF n) (ho:C.output=n+C.size - 1) (hb:IsBin n C)
  (D₁':Finset (Fin n)) (gS:Fin n→ ℕ)
  (hS1:∀ v∈D₁',wD C v.val=1∧n≤gS v∧gS v<C.output ∧
   wD C (gS v)=2∧S1 n C (gS v)={v} ∧
   ∀ q<C.size,∀ g,C.gates[q]?=some g→ gS v∈g.inputs→ g.op=.and)
  (hD1o:∀ q,q+1<C.size→ (∀ v∈D₁',n+q≠gS v)→ wD C (n+q)=1)
  (v:Fin n) (hv:v∈D₁') :
  ∀ w<n+C.size,v∈S1 n C w→ S1 n C w={v}:= by
 obtain ⟨hdv,hgG,hgL,_,hSgs,hcons⟩:=hS1 v hv;have hVO:v∉S1 n C C.output:= by simp only [S1,mF,mU,true_and];have hf:=congrFun hf (oH v);change wv C (oH v) C.output=cF n (oH v) at hf;rw [hf,cf1 hn v];decide
 have hW1:∀ w<n+C.size,v∈S1 n C w→ w≠gS v→ wD C w=1:= by
  intro w wl hvw hne;by_cases hwn:w<n;{have hS:=s1I C ⟨w,hwn⟩;rw [hS,m1] at hvw;have heq:w=v.val:=(congrArg Fin.val hvw).symm;rw [heq];exact hdv};{
   let q:=w - n;have hq:q<C.size:= by {omega};have we:w=n+q:= by {omega};rw [we] at hvw hne ⊢;have hQL:q+1<C.size:= by
    by_contra hge;rw [show n+q=C.output by omega] at hvw
    exact hVO hvw
   apply hD1o q hQL;intro v' hv' heq;have hSv':=(hS1 v' hv').2.2.2.2.1;rw [heq,hSv',m1] at hvw;subst hvw;exact hne heq
  }
 have hIg:∀ w<n+C.size,v∈S1 n C w→ iS n C w (gS v):= by
  intro w;induction w using Nat.strong_induction_on with
  | _ w ih =>
   intro wl hvw;by_cases hwn:w<n;{have hS:=s1I C ⟨w,hwn⟩;rw [hS,m1] at hvw;have heq:w=v.val:=(congrArg Fin.val hvw).symm;rw [heq];exact isS C hb v (gS v) (by omega) (by rw [hSgs];exact mem_singleton_self v)};{
    let r:=w - n;have hr:r<C.size:= by {omega};have we:w=n+r:= by {omega};rw [we] at hvw ⊢;obtain ⟨op,hg,hop,hne_ab,hl,hr_lt⟩:=hbG C hb r hr;have hSF:∀ u<n+r,v∈S1 n C u→ u≠gS v→ u∈[gL C r,gR C r] →
      iS n C (n+r) (gS v):= by
     intro u hult hvu hune humem;have hsb:=ih u (by omega) (by omega) hvu;cases hsb using ReflTransGen.head_induction_on with
     | refl=>exact absurd rfl hune
     | head hfirst hRe =>
      obtain ⟨q',hq',g',hg',rfl,huin'⟩:=hfirst;have hdu:=hW1 u (by omega) hvu hune;have hrq:r=q':=uR1 C u r q' hdu
       ⟨op,[gL C r,gR C r]⟩ g' hg humem hg' huin'
      rw [hrq];exact hRe
    rcases hop with rfl | rfl;{
     rw [s1A n C r (gL C r) (gR C r) hr hg hl hr_lt,mem_inter] at hvw;by_cases hL:gL C r=gS v;{exact hSF (gR C r) hr_lt hvw.2 (fun h=>hne_ab (hL.trans h.symm)) (by simp)};{exact hSF (gL C r) hl hvw.1 hL (by simp)}
    }
    {
     rw [s1O n C r (gL C r) (gR C r) hr hg hl hr_lt,mem_union] at hvw;rcases hvw with h1 | h2;{
      by_cases hL:gL C r=gS v;{have hand:=hcons r hr ⟨.or,[gL C r,gR C r]⟩ hg (by rw [hL];simp);cases hand};{exact hSF (gL C r) hl h1 hL (by simp)}
     }
     {by_cases hR:gR C r=gS v;{have hand:=hcons r hr ⟨.or,[gL C r,gR C r]⟩ hg (by rw [hR];simp);cases hand};{exact hSF (gR C r) hr_lt h2 hR (by simp)}}
    }
   }
 have hCn:∀ k≤gS v,∀ x y,x<y→ y≤k→ v∈S1 n C x→ v∈S1 n C y →
   iS n C x y:= by
  intro k;induction k with
  | zero=>intro _ x y hxy hy0 _ _;omega
  | succ k ih =>
   intro hk x y hxy hyk hvx hvy;by_cases hy_le:y≤k;{exact ih (by omega) x y hxy hy_le hvx hvy};{
    have hy_eq:y=k+1:= by {omega};have hxv:v.val≤x:=isL C hb (isS C hb v x (by omega) hvx);have hyn:¬ y<n:= by {intro hlt;have hS:=s1I C ⟨y,hlt⟩;rw [hS,m1] at hvy;have hyv:y=v.val:=(congrArg Fin.val hvy).symm;omega};let r:=y - n;have hr:r<C.size:= by {omega};have ye:y=n+r:= by {omega};rw [ye] at hvy hxy hy_eq ⊢;obtain ⟨op,hg,hop,_,hl,hr_lt⟩:=hbG C hb r hr;have hCh:∃ c,c∈[gL C r,gR C r]∧c<n+r∧v∈S1 n C c:= by
     rcases hop with rfl | rfl;{rw [s1A n C r (gL C r) (gR C r) hr hg hl hr_lt,mem_inter] at hvy;exact ⟨gL C r,by simp,hl,hvy.1⟩};{
      rw [s1O n C r (gL C r) (gR C r) hr hg hl hr_lt,mem_union] at hvy;rcases hvy with h1 | h2;{exact ⟨gL C r,by simp,hl,h1⟩};{exact ⟨gR C r,by simp,hr_lt,h2⟩}
     }
    obtain ⟨c,hcin,hclt,hvc⟩:=hCh;have hstepc:iS n C c (n+r) :=
     isSt C r hr ⟨op,[gL C r,gR C r]⟩ hg c hcin
    by_cases hxc:x=c;{subst hxc;exact hstepc};{
     by_cases hxltc:x<c;{exact ReflTransGen.trans (ih (by omega) x c hxltc (by omega) hvx hvc) hstepc};{
      exfalso;have hcltx:c<x:= by omega
      have hcx:=ih (by omega) c x hcltx (by omega) hvc hvx;cases hcx using ReflTransGen.head_induction_on with
      | refl=>omega
      | head hs1 hr1 =>
       obtain ⟨q1,hq1,g1,hg1,rfl,hc1⟩:=hs1;have hle1:=isL C hb hr1;have hdc:=hW1 c (by omega) hvc (by omega);have heq1:=uR1 C c q1 r hdc g1
        ⟨op,[gL C r,gR C r]⟩ hg1 hc1 hg hcin
       omega
     }
    }
   }
 have hSs0:∀ z≤gS v,v∈S1 n C z→ ∀ w≤z,v∈S1 n C w→ S1 n C w⊆S1 n C z:= by
  intro z;induction z using Nat.strong_induction_on with
  | _ z ih =>
   intro hzle hvz w hwz hvw;by_cases hw_eq:w=z;{rw [hw_eq]};{
    have hwv:v.val≤w:=isL C hb (isS C hb v w (by omega) hvw);have hzn:¬ z<n:= by {intro hlt;have hS:=s1I C ⟨z,hlt⟩;rw [hS,m1] at hvz;have hzv:z=v.val:=(congrArg Fin.val hvz).symm;omega};let r:=z - n;have hr:r<C.size:= by {omega};have ze:z=n+r:= by {omega};rw [ze] at hvz hwz hw_eq hzle ⊢;obtain ⟨op,hg,hop,hne_ab,hl,hr_lt⟩:=hbG C hb r hr;have hop_or:op=.or:= by
     rcases hop with rfl | rfl;{
      exfalso;rw [s1A n C r (gL C r) (gR C r) hr hg hl hr_lt,mem_inter] at hvz;by_cases hLR:gL C r<gR C r;{
       have hsb:=hCn (gS v) le_rfl (gL C r) (gR C r) hLR (by omega) hvz.1 hvz.2;rcases ReflTransGen.cases_head hsb with hEq | ⟨w',hs1,hr1⟩;{omega};{
        obtain ⟨q1,_,g1,hg1,rfl,hL1⟩:=hs1;have hle1:=isL C hb hr1;have hdL:=hW1 (gL C r) (by omega) hvz.1 (by omega);have heq1:=uR1 C (gL C r) q1 r hdL g1
         ⟨.and,[gL C r,gR C r]⟩ hg1 hL1 hg (by simp)
        omega
       }
      }
      {
       have hRL:gR C r<gL C r:= by {omega};have hsb:=hCn (gS v) le_rfl (gR C r) (gL C r) hRL (by omega) hvz.2 hvz.1;rcases ReflTransGen.cases_head hsb with hEq | ⟨w',hs1,hr1⟩;{omega};{
        obtain ⟨q1,_,g1,hg1,rfl,hR1⟩:=hs1;have hle1:=isL C hb hr1;have hdR:=hW1 (gR C r) (by omega) hvz.2 (by omega);have heq1:=uR1 C (gR C r) q1 r hdR g1
         ⟨.and,[gL C r,gR C r]⟩ hg1 hR1 hg (by simp)
        omega
       }
      }
     }
     {rfl}
    subst hop_or;rw [s1O n C r (gL C r) (gR C r) hr hg hl hr_lt] at hvz ⊢;have hSC:∀ c,c∈[gL C r,gR C r]→ c<n+r→ v∈S1 n C c →
      S1 n C c⊆S1 n C (gL C r)∪S1 n C (gR C r) →
      S1 n C w⊆S1 n C (gL C r)∪S1 n C (gR C r):= by
     intro c hcin hclt hvc hcsub;by_cases hwc:w≤c;{exact Subset.trans (ih c (by omega) (by omega) hvc w hwc hvw) hcsub};{
      exfalso;have hcw:c<w:= by omega
      have hsb:=hCn (gS v) le_rfl c w hcw (by omega) hvc hvw;cases hsb using ReflTransGen.head_induction_on with
      | refl=>omega
      | head hs1 hr1 =>
       obtain ⟨q1,_,g1,hg1,rfl,hc1⟩:=hs1;have hle1:=isL C hb hr1;have hdc:=hW1 c (by omega) hvc (by omega);have heq1:=uR1 C c q1 r hdc g1
        ⟨.or,[gL C r,gR C r]⟩ hg1 hc1 hg hcin
       omega
     }
    rcases mem_union.1 hvz with h1 | h2;{exact hSC (gL C r) (by simp) hl h1 subset_union_left};{exact hSC (gR C r) (by simp) hr_lt h2 subset_union_right}
   }
 intro w wl hvw;have hw_le:w≤gS v:=isL C hb (hIg w wl hvw);have hsb:=hSs0 (gS v) le_rfl (by rw [hSgs];exact mem_singleton_self v) w hw_le hvw;rw [hSgs] at hsb;apply Subset.antisymm hsb;rw [singleton_subset_iff];exact hvw
lemma d1E {n:ℕ} (C:Circuit) (hn:5≤n)
  (hf:circuitFun n C=cF n) (ho:C.output=n+C.size - 1) (hb:IsBin n C)
  (hDb:∀ v:Fin n,1≤wD C v.val∧wD C v.val≤2)
  (D₁':Finset (Fin n)) (gS:Fin n→ ℕ)
  (hS1:∀ v∈D₁',wD C v.val=1∧n≤gS v∧gS v<C.output ∧
   wD C (gS v)=2∧S1 n C (gS v)={v} ∧
   ∀ q<C.size,∀ g,C.gates[q]?=some g→ gS v∈g.inputs→ g.op=.and)
  (hD1o:∀ q,q+1<C.size→ (∀ v∈D₁',n+q≠gS v)→ wD C (n+q)=1)
  (hCc:(D2 n C).card+D₁'.card=(n+1)/2)
  (hCv:∀ u v:Fin n,cA u v→ u∈D2 n C∪D₁'∨v∈D2 n C∪D₁')
  (hCe0:∀ c:Fin n,wD C c.val=1→ c∉D₁' →
   ∃ qz w_c y_c:ℕ,qz<C.size ∧
    (C.gates[qz]?=some ⟨.and,[w_c,y_c]⟩∨C.gates[qz]?=some ⟨.and,[y_c,w_c]⟩) ∧
    S1 n C w_c={c}∧(∀ u:Fin n,cA c u→ u∈S1 n C y_c)∧c∉S1 n C y_c) :
  D₁'=∅:= by
 have hDj:Disjoint (D2 n C) D₁':= by {rw [disjoint_left];intro v hv2 hv1;have h2:wD C v.val=2:=(mF.1 hv2).2;have h1:wD C v.val=1:=(hS1 v hv1).1;omega};let I:Finset (Fin n):=univ \ (D2 n C∪D₁');have hIc:I.card=n/2:= by {have hc:=card_sdiff_add_card_eq_card (subset_univ (D2 n C∪D₁'));rw [card_univ,Fintype.card_fin,card_union_of_disjoint hDj,hCc] at hc;change I.card+(n+1)/2=n at hc;omega};have hIN:∀ c∈I,∀ u:Fin n,cA c u→ u∈D2 n C:= by
  intro c hcI u hAd;have hNt0:c∉D2 n C∪D₁':=(mS.1 hcI).2;have hnot2:c∉D2 n C:=fun h=>hNt0 (mem_union_left _ h);have hnot1:c∉D₁':=fun h=>hNt0 (mem_union_right _ h);have hdegc:wD C c.val=1:= by have hb:=hDb c;have hne2:wD C c.val≠2:=fun h=>hnot2 (mF.2 ⟨mU c,h⟩);omega
  have hu_cov:u∈D2 n C∪D₁':=(hCv c u hAd).resolve_left hNt0;rcases mem_union.1 hu_cov with hu2 | hu1;{exact hu2};{
   exfalso;obtain ⟨qz,w_c,y_c,hqz,hgqz,_,hy_adj,_⟩:=hCe0 c hdegc hnot1;have hy_lt:y_c<n+C.size:= by
    obtain ⟨op,hg,_,_,hl,hr⟩:=hbG C hb qz hqz;rcases hgqz with h1 | h1;{
     rw [h1] at hg;have:[w_c,y_c]=[gL C qz,gR C qz]:=congrArg Gate.inputs (oI hg);have:y_c=gR C qz:= by injection this with _ h2;injection h2
     omega
    }
    {
     rw [h1] at hg;have:[y_c,w_c]=[gL C qz,gR C qz]:=congrArg Gate.inputs (oI hg);have:y_c=gL C qz:= by injection this
     omega
    }
   have hSy_eq:S1 n C y_c={u} :=
    s1D C hn hf ho hb D₁' gS hS1 hD1o u hu1 y_c hy_lt (hy_adj u hAd)
   have h1:cN (by omega) c∈S1 n C y_c:=hy_adj _ (cnA (by omega) c);have h2:cP (by omega) c∈S1 n C y_c:=hy_adj _ (cpA (by omega) c);rw [hSy_eq,m1] at h1 h2;exact cnNP hn c (h1.trans h2.symm)
  }
 have hID:I.card≤(D2 n C).card:= by
  have hsb:I.image (cN (by omega))⊆D2 n C:= by {intro u hu;obtain ⟨c,hc,rfl⟩:=mG.1 hu;exact hIN c hc _ (cnA (by omega) c)}
  calc I.card=(I.image (cN (by omega))).card :=
     (card_image_of_injective I (cnJ (by omega))).symm
   _≤(D2 n C).card:=card_le_card hsb
 by_contra hne;obtain ⟨v,hv⟩:=nonempty_iff_ne_empty.2 hne;have h1p:1≤D₁'.card:=one_le_card.2 ⟨v,hv⟩;have h2e:(D2 n C).card=n/2:= by omega
 have h1e:D₁'.card=1:= by {omega};have hIm:I.image (cN (by omega))=D2 n C:= by {apply Finset.eq_of_subset_of_card_le;{intro u hu;obtain ⟨c,hc,rfl⟩:=mG.1 hu;exact hIN c hc _ (cnA (by omega) c)};{rw [card_image_of_injective I (cnJ (by omega)),hIc,h2e]}};let w:=cN (by omega) v;have hvw:cA v w:=cnA (by omega) v;have hNI:w∉I:= by {intro hwI;exact disjoint_left.1 hDj (hIN w hwI v (Or.inr rfl)) hv};have hN2:w∉D2 n C:= by {intro hw2;rw [← hIm] at hw2;obtain ⟨c,hcI,hcw⟩:=mG.1 hw2;have hcv:c=v:=cnJ (by omega) hcw;subst hcv;exact (mS.1 hcI).2 (mem_union_right _ hv)};have hw_D1:w∈D₁':= by
  have:w∈D2 n C∪D₁':= by by_contra hno;exact hNI (mS.2 ⟨mU w,hno⟩)
  exact (mem_union.1 this).resolve_left hN2
 have hEv:w=v:=card_le_one.1 (le_of_eq h1e) w hw_D1 v hv;exact caR hn v (hEv▸hvw)
lemma scW {n:ℕ} (C:Circuit) (hb:IsBin n C) (f:ℕ→ ℕ) :
  ∑ q∈range C.size,(f (gL C q)+f (gR C q)) =
   ∑ w∈range (n+C.size),wD C w*f w:= by
 have h1:∀ w,wD C w*f w=∑ q∈range C.size,
   if ∃ g,C.gates[q]?=some g∧w∈g.inputs then f w else 0:= by
  intro w;rw [wdR,card_filter,sum_mul];apply sC rfl;intro q _
  split_ifs <;> simp
 simp_rw [h1];rw [sum_comm];apply sC rfl;intro q hq;have ql:q<C.size:=mR.1 hq;obtain ⟨op,hg,_,hne,hl,hr⟩:=hbG C hb q ql;have hMm:∀ w,(∃ g,C.gates[q]?=some g∧w∈g.inputs)↔w=gL C q∨w=gR C q:= by
  intro w;constructor;{rintro ⟨g,hg',hw⟩;rw [hg] at hg';obtain rfl:=oI hg';simpa using hw};{
   rintro (rfl | rfl);{exact ⟨_,hg,by simp⟩};{exact ⟨_,hg,by simp⟩}
  }
 have heq:(∑ w∈range (n+C.size),
   if ∃ g,C.gates[q]?=some g∧w∈g.inputs then f w else 0) =
   ∑ w∈(range (n+C.size)).filter (fun w=>w=gL C q∨w=gR C q),f w:= by
  rw [sum_filter];apply sC rfl;intro w _;simp only [hMm w]
 rw [heq];have hPr:(range (n+C.size)).filter (fun w=>w=gL C q∨w=gR C q) =
   {gL C q,gR C q}:= by
  ext w
  simp only [mF,mR,mI,m1];constructor;{exact fun h=>h.2};{
   rintro (rfl | rfl);{exact ⟨by omega,Or.inl rfl⟩};{exact ⟨by omega,Or.inr rfl⟩}
  }
 rw [hPr,sum_pair hne]
lemma wdO {n:ℕ} (C:Circuit) (ho:C.output=n+C.size - 1)
  (hb:IsBin n C) (hp:0<C.size):wD C C.output=0:= by
 rw [wdR,card_eq_zero,filter_eq_empty_iff];intro q hq;have ql:q<C.size:=mR.1 hq;rintro ⟨g,hg,hMm⟩;obtain ⟨op,hg',_,_,hl,hr⟩:=hbG C hb q ql;rw [hg] at hg';obtain rfl:=oI hg';simp only [List.mem_cons,List.not_mem_nil,or_false] at hMm;rcases hMm with h | h <;> omega
lemma tT {n:ℕ} (C:Circuit) (ho:C.output=n+C.size - 1) (hb:IsBin n C)
  (hd1:∀ q,q+1<C.size→ wD C (n+q)=1) (hp:0<C.size)
  (f k:ℕ→ ℕ)
  (hSt0:∀ q<C.size,f (gL C q)+f (gR C q)=f (n+q)+k q) :
  (∑ w∈range n,wD C w*f w) =
   f C.output+∑ q∈range C.size,k q:= by
 have h1:=scW C hb f;have h2:∑ q∈range C.size,(f (gL C q)+f (gR C q)) =
   (∑ q∈range C.size,f (n+q))+∑ q∈range C.size,k q:= by
  rw [← sum_add_distrib];exact sC rfl (fun q hq=>hSt0 q (mR.1 hq))
 rw [sum_range_add] at h1;have hsz:C.size=(C.size - 1)+1:= by omega
 have hGs:∑ q∈range C.size,wD C (n+q)*f (n+q) =
   ∑ q∈range (C.size - 1),f (n+q):= by
  conv_lhs=>rw [hsz,sum_range_succ];rw [show n+(C.size - 1)=C.output by omega,wdO C ho hb hp,zero_mul,add_zero]
  apply sC rfl;intro q hq;rw [hd1 q (by have:=mR.1 hq;omega),one_mul]
 have hFs:∑ q∈range C.size,f (n+q) =
   (∑ q∈range (C.size - 1),f (n+q))+f C.output:= by
  conv_lhs=>rw [hsz,sum_range_succ];rw [show n+(C.size - 1)=C.output by omega]
 rw [hGs] at h1;rw [hFs] at h2;omega
def lM (n:ℕ) (C:Circuit) (v:Fin n) (r:ℕ):ℕ :=
 if r<n then (if r=v.val then 1 else 0)
 else if _h:gL C (r - n)<r∧gR C (r - n)<r then
  lM n C v (gL C (r - n))+lM n C v (gR C (r - n))
 else 0
termination_by r
decreasing_by all_goals (first | exact _h.1 | exact _h.2)
lemma lmL (n:ℕ) (C:Circuit) (v:Fin n) (r:ℕ) (hr:r<n) :
  lM n C v r=if r=v.val then 1 else 0:= by
 rw [lM];simp [hr]
lemma lmG {n:ℕ} (C:Circuit) (hb:IsBin n C) (v:Fin n) (q:ℕ) (hq:q<C.size) :
  lM n C v (n+q)=lM n C v (gL C q)+lM n C v (gR C q):= by
 obtain ⟨_,_,_,_,hl,hr⟩:=hbG C hb q hq;rw [lM];have hnl:¬ n+q<n:= by omega
 have hsb:n+q - n=q:=Nat.add_sub_cancel_left n q;simp only [hnl,↓reduceIte,hsb,hl,hr,and_self,↓reduceDIte]
lemma lmO {n:ℕ} (C:Circuit) (ho:C.output=n+C.size - 1)
  (hb:IsBin n C) (hd1:∀ q,q+1<C.size→ wD C (n+q)=1)
  (hp:0<C.size) (v:Fin n) :
  lM n C v C.output=wD C v.val:= by
 have ht:=tT C ho hb hd1 hp (lM n C v) (fun _=>0)
  (fun q hq=> by rw [lmG C hb v q hq,add_zero])
 have hSm:∑ w∈range n,wD C w*lM n C v w=wD C v.val:= by
  have hrw:∀ w∈range n,
    wD C w*lM n C v w=if w=v.val then wD C w else 0:= by
   intro w hw;rw [lmL n C v w (mR.1 hw)]
   split_ifs <;> simp
  rw [sC rfl hrw,sum_ite_eq' (range n) v.val (fun w=>wD C w)];simp [mR.2 v.2]
 rw [hSm,sum_const_zero,add_zero] at ht;exact ht.symm
lemma lmM {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (v:Fin n) {w r:ℕ} (h:iS n C w r) :
  lM n C v w≤lM n C v r:= by
 induction h with
 | refl=>exact le_rfl
 | tail _ hSt0 ih =>
  obtain ⟨q,hq,g,hg,rfl,hMm⟩:=hSt0;obtain ⟨op,hg',_,_,_,_⟩:=hbG C hb q hq;rw [hg] at hg';obtain rfl:=oI hg';rw [lmG C hb v q hq];simp only [List.mem_cons,List.not_mem_nil,or_false] at hMm;rcases hMm with rfl | rfl <;> omega
def sL (n:ℕ) (C:Circuit) (v:Fin n) (r:ℕ):ℕ :=
 if v∉S1 n C r then 0
 else if r<n then 1
 else if _h:gL C (r - n)<r∧gR C (r - n)<r then
  sL n C v (gL C (r - n))+sL n C v (gR C (r - n))
 else 0
termination_by r
decreasing_by all_goals (first | exact _h.1 | exact _h.2)
lemma slN (n:ℕ) (C:Circuit) (v:Fin n) (r:ℕ) (hv:v∉S1 n C r) :
  sL n C v r=0:= by
 rw [sL];simp [hv]
lemma slL (n:ℕ) (C:Circuit) (v:Fin n) (r:ℕ) (hr:r<n) :
  sL n C v r=if r=v.val then 1 else 0:= by
 by_cases heq:r=v.val;{
  have hMm:v∈S1 n C r:= by {rw [s1I C ⟨r,hr⟩,m1];exact Fin.ext heq.symm};rw [sL,ite_eq_right_iff.2 (fun h=>(h hMm).elim),ite_eq_left_iff.2 (fun h=>(h hr).elim),
   ite_eq_left_iff.2 (fun h=>(h heq).elim)]
 }
 {have hNt0:v∉S1 n C r:= by {rw [s1I C ⟨r,hr⟩,m1];intro h;exact heq (congrArg Fin.val h).symm};rw [slN n C v r hNt0,ite_eq_right_iff.2 (fun h=>(heq h).elim)]}
lemma slG {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (v:Fin n) (q:ℕ) (hq:q<C.size) (hv:v∈S1 n C (n+q)) :
  sL n C v (n+q)=sL n C v (gL C q)+sL n C v (gR C q):= by
 obtain ⟨_,_,_,_,hl,hr⟩:=hbG C hb q hq;rw [sL];have hnl:¬ n+q<n:= by omega
 have hsb:n+q - n=q:=Nat.add_sub_cancel_left n q;simp only [hv,not_true_eq_false,↓reduceIte,hnl,hsb,hl,hr,and_self,↓reduceDIte]
lemma sl1 {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (v:Fin n):∀ r<n+C.size,v∈S1 n C r→ 1≤sL n C v r:= by
 intro r;induction r using Nat.strong_induction_on with
 | _ r ih =>
  intro rl hvr;by_cases hrn:r<n;{rw [slL n C v r hrn];have hS:=s1I C ⟨r,hrn⟩;rw [hS,m1] at hvr;have:r=v.val:=(congrArg Fin.val hvr).symm;simp [this]};{
   let q:=r - n;have hq:q<C.size:= by {omega};have re:r=n+q:= by {omega};rw [re] at hvr ⊢;rw [slG C hb v q hq hvr];obtain ⟨op,hg,hop,_,hl,hr⟩:=hbG C hb q hq;rcases hop with rfl | rfl;{rw [s1A n C q (gL C q) (gR C q) hq hg hl hr,mem_inter] at hvr;have:=ih (gL C q) (by omega) (by omega) hvr.1;omega};{
    rw [s1O n C q (gL C q) (gR C q) hq hg hl hr,mem_union] at hvr;rcases hvr with h1 | h2;{have:=ih (gL C q) (by omega) (by omega) h1;omega};{have:=ih (gR C q) (by omega) (by omega) h2;omega}
   }
  }
lemma slM {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (v:Fin n):∀ r<n+C.size,sL n C v r≤lM n C v r:= by
 intro r;induction r using Nat.strong_induction_on with
 | _ r ih =>
  intro rl;by_cases hrn:r<n;{rw [slL n C v r hrn,lmL n C v r hrn]};{
   let q:=r - n;have hq:q<C.size:= by {omega};have re:r=n+q:= by {omega};rw [re];by_cases hvr:v∈S1 n C (n+q);{rw [slG C hb v q hq hvr,lmG C hb v q hq];obtain ⟨_,_,_,_,hl,hr⟩:=hbG C hb q hq;have h1:=ih (gL C q) (by omega) (by omega);have h2:=ih (gR C q) (by omega) (by omega);omega};{rw [slN n C v (n+q) hvr];exact zL _}
  }
def kS (n:ℕ) (C:Circuit) (v:Fin n) (q:ℕ):ℕ :=
 if v∉S1 n C (n+q) then sL n C v (gL C q)+sL n C v (gR C q) else 0
lemma kSS {n:ℕ} (C:Circuit) (hn:5≤n)
  (hf:circuitFun n C=cF n) (ho:C.output=n+C.size - 1) (hb:IsBin n C)
  (hd1:∀ q,q+1<C.size→ wD C (n+q)=1) (hp:0<C.size) (v:Fin n) :
  ∑ q∈range C.size,kS n C v q=wD C v.val:= by
 have ht:=tT C ho hb hd1 hp (sL n C v) (kS n C v) (fun q hq=> by
  unfold kS;by_cases hv:v∈S1 n C (n+q);{rw [slG C hb v q hq hv];simp [hv]};{rw [slN n C v (n+q) hv];simp [hv]})
 have hSm:∑ w∈range n,wD C w*sL n C v w=wD C v.val:= by
  have hrw:∀ w∈range n,
    wD C w*sL n C v w=if w=v.val then wD C w else 0:= by
   intro w hw;rw [slL n C v w (mR.1 hw)]
   split_ifs <;> simp
  rw [sC rfl hrw,sum_ite_eq' (range n) v.val (fun w=>wD C w)];simp [mR.2 v.2]
 have hout_not:v∉S1 n C C.output:= by {simp only [S1,mF,mU,true_and];have hf:=congrFun hf (oH v);change wv C (oH v) C.output=cF n (oH v) at hf;rw [hf,cf1 hn v];decide};rw [hSm,slN n C v C.output hout_not,zero_add] at ht;exact ht.symm
def lmC (n:ℕ) (C:Circuit) (T:Finset ℕ) (v:Fin n) (r:ℕ):ℕ :=
 if r<n then (if r=v.val then 1 else 0)
 else if r - n∈T then 0
 else if _h:gL C (r - n)<r∧gR C (r - n)<r then
  lmC n C T v (gL C (r - n))+lmC n C T v (gR C (r - n))
 else 0
termination_by r
decreasing_by all_goals (first | exact _h.1 | exact _h.2)
lemma lmcL (n:ℕ) (C:Circuit) (T:Finset ℕ) (v:Fin n) (r:ℕ) (hr:r<n) :
  lmC n C T v r=if r=v.val then 1 else 0:= by
 rw [lmC];simp [hr]
lemma lmcE (n:ℕ) (C:Circuit) (T:Finset ℕ) (v:Fin n) (q:ℕ) (hq:q∈T) :
  lmC n C T v (n+q)=0:= by
 rw [lmC];have hnl:¬ n+q<n:= by omega
 have hsb:n+q - n=q:=Nat.add_sub_cancel_left n q;simp only [hnl,↓reduceIte,hsb,hq]
lemma lmcG {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (T:Finset ℕ) (v:Fin n) (q:ℕ) (hq:q<C.size) (hNt0:q∉T) :
  lmC n C T v (n+q) =
   lmC n C T v (gL C q)+lmC n C T v (gR C q):= by
 obtain ⟨_,_,_,_,hl,hr⟩:=hbG C hb q hq;rw [lmC];have hnl:¬ n+q<n:= by omega
 have hsb:n+q - n=q:=Nat.add_sub_cancel_left n q;simp only [hnl,↓reduceIte,hsb,hNt0,hl,hr,and_self,↓reduceDIte]
lemma lmcD {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (T:Finset ℕ) (v:Fin n) :
  ∀ r<n+C.size,(∀ t∈T,¬ iS n C (n+t) r) →
   lmC n C T v r=lM n C v r:= by
 intro r;induction r using Nat.strong_induction_on with
 | _ r ih =>
  intro rl hDj;by_cases hrn:r<n;{rw [lmcL n C T v r hrn,lmL n C v r hrn]};{
   let q:=r - n;have hq:q<C.size:= by {omega};have re:r=n+q:= by {omega};rw [re] at hDj ⊢;have hqnot:q∉T:=fun hqT=>hDj q hqT ReflTransGen.refl;rw [lmcG C hb T v q hq hqnot,lmG C hb v q hq];obtain ⟨op,hg,_,_,hl,hr⟩:=hbG C hb q hq;have hSL:iS n C (gL C q) (n+q) :=
    isSt C q hq ⟨op,[gL C q,gR C q]⟩ hg (gL C q) (by simp)
   have hSR:iS n C (gR C q) (n+q) :=
    isSt C q hq ⟨op,[gL C q,gR C q]⟩ hg (gR C q) (by simp)
   rw [ih (gL C q) (by omega) (by omega) (fun t ht h=>hDj t ht (ReflTransGen.trans h hSL)),
    ih (gR C q) (by omega) (by omega) (fun t ht h=>hDj t ht (ReflTransGen.trans h hSR))]
  }
lemma lmcO {n:ℕ} (C:Circuit) (ho:C.output=n+C.size - 1)
  (hb:IsBin n C) (hd1:∀ q,q+1<C.size→ wD C (n+q)=1) (hp:0<C.size)
  (T:Finset ℕ) (hTs:∀ t∈T,t<C.size)
  (hAn:∀ t1∈T,∀ t2∈T,iS n C (n+t1) (n+t2)→ t1=t2) (v:Fin n) :
  lmC n C T v C.output+∑ t∈T,lM n C v (n+t)=wD C v.val:= by
 have ht:=tT C ho hb hd1 hp (lmC n C T v)
  (fun q=>if q∈T then lM n C v (n+q) else 0) (fun q hq=> by
   by_cases hqT:q∈T;{
    rw [lmcE n C T v q hqT,zero_add];simp only [hqT,↓reduceIte];obtain ⟨op,hg,_,_,hl,hr⟩:=hbG C hb q hq;have hSL:iS n C (gL C q) (n+q) :=
     isSt C q hq ⟨op,[gL C q,gR C q]⟩ hg (gL C q) (by simp)
    have hSR:iS n C (gR C q) (n+q) :=
     isSt C q hq ⟨op,[gL C q,gR C q]⟩ hg (gR C q) (by simp)
    have hDL:∀ t∈T,¬ iS n C (n+t) (gL C q):= by {intro t ht hsb;have heq:=hAn t ht q hqT (ReflTransGen.trans hsb hSL);subst heq;have:=isL C hb hsb;omega};have hDR:∀ t∈T,¬ iS n C (n+t) (gR C q):= by {intro t ht hsb;have heq:=hAn t ht q hqT (ReflTransGen.trans hsb hSR);subst heq;have:=isL C hb hsb;omega};rw [lmcD C hb T v (gL C q) (by omega) hDL,
     lmcD C hb T v (gR C q) (by omega) hDR,
     lmG C hb v q hq]
   }
   {rw [lmcG C hb T v q hq hqT];simp [hqT]})
 have hSm:∑ w∈range n,wD C w*lmC n C T v w=wD C v.val:= by
  have hrw:∀ w∈range n,
    wD C w*lmC n C T v w=if w=v.val then wD C w else 0:= by
   intro w hw;rw [lmcL n C T v w (mR.1 hw)]
   split_ifs <;> simp
  rw [sC rfl hrw,sum_ite_eq' (range n) v.val (fun w=>wD C w)];simp [mR.2 v.2]
 have hTsum:(∑ q∈range C.size,if q∈T then lM n C v (n+q) else 0) =
   ∑ t∈T,lM n C v (n+t):= by
  rw [← sum_filter];have hfl:(range C.size).filter (fun q=>q∈T)=T:= by ext q;simp only [mF,mR,and_iff_right_iff_imp];exact hTs q
  rw [hfl]
 rw [hSm,hTsum] at ht;exact ht.symm
lemma lmcM {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (T:Finset ℕ) (v:Fin n) {w r:ℕ} (h:iS n C w r)
  (hno:∀ q<C.size,iS n C w (n+q)→ iS n C (n+q) r→ q∉T) :
  lmC n C T v w≤lmC n C T v r:= by
 induction h with
 | refl=>exact le_rfl
 | tail hPv hSt0 ih =>
  obtain ⟨q,hq,g,hg,rfl,hMm⟩:=hSt0;obtain ⟨op,hg',_,_,_,_⟩:=hbG C hb q hq;rw [hg] at hg';obtain rfl:=oI hg';have sbq:iS n C w (n+q) :=
   ReflTransGen.tail hPv ⟨q,hq,⟨op,[gL C q,gR C q]⟩,hg,rfl,hMm⟩
  have hqnot:q∉T:=hno q hq sbq ReflTransGen.refl;have ih':=ih (fun q' hq' h1 h2 =>
   hno q' hq' h1 (ReflTransGen.tail h2 ⟨q,hq,⟨op,[gL C q,gR C q]⟩,hg,rfl,hMm⟩))
  rw [lmcG C hb T v q hq hqnot];simp only [List.mem_cons,List.not_mem_nil,or_false] at hMm;rcases hMm with rfl | rfl <;> omega
lemma wvcZ {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (T:Finset ℕ) (x y:Fin n→ Bool)
  (hTa:∀ t∈T,wv C x (n+t)=wv C y (n+t)) :
  ∀ r<n+C.size,(∀ i:Fin n,0<lmC n C T i r→ x i=y i) →
   wv C x r=wv C y r:= by
 intro r;induction r using Nat.strong_induction_on with
 | _ r ih =>
  intro rl hAg;by_cases hrn:r<n;{let i:Fin n:=⟨r,hrn⟩;rw [wvI C x i,wvI C y i];apply hAg i;rw [lmcL n C T i r hrn];simp [i]};{
   let q:=r - n;have hq:q<C.size:= by {omega};have re:r=n+q:= by {omega};rw [re] at hAg ⊢;by_cases hqT:q∈T;{exact hTa q hqT};{
    obtain ⟨op,hg,hop,_,hl,hr⟩:=hbG C hb q hq;have hga:wv C x (gL C q)=wv C y (gL C q) :=
     ih (gL C q) (by omega) (by omega) (fun i hi=>hAg i (by rw [lmcG C hb T i q hq hqT];omega))
    have hgb:wv C x (gR C q)=wv C y (gR C q) :=
     ih (gR C q) (by omega) (by omega) (fun i hi=>hAg i (by rw [lmcG C hb T i q hq hqT];omega))
    rcases hop with rfl | rfl;{
     rw [wvA C x q (gL C q) (gR C q) hq hg hl hr,
      wvA C y q (gL C q) (gR C q) hq hg hl hr,hga,hgb]
    }
    {
     rw [wvR C x q (gL C q) (gR C q) hq hg hl hr,
      wvR C y q (gL C q) (gR C q) hq hg hl hr,hga,hgb]
    }
   }
  }
lemma wvZ {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (x y:Fin n→ Bool) (r:ℕ) (rl:r<n+C.size)
  (hAg:∀ i:Fin n,0<lM n C i r→ x i=y i) :
  wv C x r=wv C y r:= by
 apply wvcZ C hb ∅ x y (by simp) r rl;intro i hi;rw [lmcD C hb ∅ i r rl (by simp)] at hi;exact hAg i hi
lemma wvO {n:ℕ} (C:Circuit)
  (hf:circuitFun n C=cF n) (ho:C.output=n+C.size - 1) (hb:IsBin n C)
  (hd1:∀ q,q+1<C.size→ wD C (n+q)=1) (hp:0<C.size)
  (q:ℕ) (hq:q<C.size)
  (hor:∀ r<C.size,iS n C (n+q) (n+r)→ r≠q →
   ∀ g,C.gates[r]?=some g→ g.op=.or) :
  ∀ x:Fin n→ Bool,wv C x (n+q)=true→ cF n x=true:= by
 intro x hxq;have hup:∀ u,iS n C (n+q) u→ wv C x u=true:= by
  intro u hu;induction hu with
  | refl=>exact hxq
  | @tail w' _ hPv hSt0 ih =>
   obtain ⟨r,hr,g,hgr,rfl,hwin⟩:=hSt0;obtain ⟨op,hgr',_,_,hl,hr_lt⟩:=hbG C hb r hr;rw [hgr] at hgr';obtain rfl:=oI hgr';have hw_lt:w'<n+r:= by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hwin;rcases hwin with rfl | rfl <;> omega
   have hle_prev:=isL C hb hPv;have sbr:iS n C (n+q) (n+r) :=
    ReflTransGen.tail hPv ⟨r,hr,⟨op,[gL C r,gR C r]⟩,hgr,rfl,hwin⟩
   have hop:op=.or:=hor r hr sbr (by omega) ⟨op,[gL C r,gR C r]⟩ hgr;subst hop;rw [wvR C x r (gL C r) (gR C r) hr hgr hl hr_lt,bOt];simp only [List.mem_cons,List.not_mem_nil,or_false] at hwin;rcases hwin with rfl | rfl;{exact Or.inl ih};{exact Or.inr ih}
 have hout_true:=hup C.output (isO C ho hb hd1 hp q hq);have hf:=congrFun hf x;change wv C x C.output=cF n x at hf;exact hf.symm.trans hout_true
lemma lm1 {n:ℕ} (C:Circuit) (hb:IsBin n C) :
  ∀ r<n+C.size,1≤∑ v:Fin n,lM n C v r:= by
 intro r;induction r using Nat.strong_induction_on with
 | _ r ih =>
  intro rl;by_cases hrn:r<n;{
   let u:Fin n:=⟨r,hrn⟩;have h1:lM n C u r=1:= by {rw [lmL n C u r hrn];simp [u]};have hle:lM n C u r≤∑ v:Fin n,lM n C v r :=
    s1s (f:=fun v:Fin n=>lM n C v r) (fun _ _=>zL _) (mU u)
   omega
  }
  {
   let q:=r - n;have hq:q<C.size:= by {omega};have re:r=n+q:= by {omega};rw [re];obtain ⟨_,_,_,_,hl,hr⟩:=hbG C hb q hq;have hSm:∑ v:Fin n,lM n C v (n+q) =
     (∑ v:Fin n,lM n C v (gL C q))+∑ v:Fin n,lM n C v (gR C q):= by
    rw [← sum_add_distrib];exact sC rfl (fun v _=>lmG C hb v q hq)
   have h1:=ih (gL C q) (by omega) (by omega);have h2:=ih (gR C q) (by omega) (by omega);omega
  }
lemma lm2 {n:ℕ} (C:Circuit) (hb:IsBin n C) (q:ℕ) (hq:q<C.size) :
  2≤∑ v:Fin n,lM n C v (n+q):= by
 obtain ⟨_,_,_,_,hl,hr⟩:=hbG C hb q hq;have hSm:∑ v:Fin n,lM n C v (n+q) =
   (∑ v:Fin n,lM n C v (gL C q))+∑ v:Fin n,lM n C v (gR C q):= by
  rw [← sum_add_distrib];exact sC rfl (fun v _=>lmG C hb v q hq)
 have h1:=lm1 C hb (gL C q) (by omega);have h2:=lm1 C hb (gR C q) (by omega);omega
lemma lmI {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (r:ℕ) (hr:r<n+C.size) (u:Fin n)
  (hlm:∀ v:Fin n,lM n C v r=if v=u then 1 else 0) :
  r=u.val:= by
 have hSm:∑ v:Fin n,lM n C v r=1:= by {simp [hlm]};have hrn:r<n:= by
  by_contra hge;let q:=r - n;have hq:q<C.size:= by omega
  rw [show r=n+q by omega] at hSm
  have h2:=lm2 C hb q hq;omega
 have hu:=hlm u;rw [lmL n C u r hrn] at hu;simp only [↓reduceIte] at hu;by_contra hne;rw [ite_eq_right_iff.2 (fun h=>(hne h).elim)] at hu;omega
lemma lmP {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (r:ℕ) (hr:r<n+C.size) (u v:Fin n) (huv:u≠v)
  (hlm:∀ z:Fin n,lM n C z r=if z=u∨z=v then 1 else 0) :
  ∃ q<C.size,∃ op,r=n+q∧(op=.and∨op=.or) ∧
   (C.gates[q]?=some ⟨op,[u.val,v.val]⟩∨C.gates[q]?=some ⟨op,[v.val,u.val]⟩):= by
 have hSm:∑ z:Fin n,lM n C z r=2:= by
  have hrw:(∑ z:Fin n,lM n C z r) =
    ∑ z∈(univ:Finset (Fin n)).filter (fun z=>z=u∨z=v),1:= by
   rw [sum_filter];exact sC rfl (fun z _=>hlm z)
  have hfl:(univ:Finset (Fin n)).filter (fun z=>z=u∨z=v)={u,v}:= by {ext z;simp};rw [hrw,hfl,sum_const,cP0 huv,smul_eq_mul,mul_one]
 have hrge:n≤r:= by
  by_contra hlt;have h1:∑ z:Fin n,lM n C z r=1:= by
   have:∀ z:Fin n,lM n C z r=if z=⟨r,by omega⟩ then 1 else 0:= by
    intro z;rw [lmL n C z r (by omega)];by_cases hz:z=⟨r,by omega⟩
    {subst hz;simp};{have hne:r≠z.val:=fun h=>hz (Fin.ext h.symm);simp [hz,hne]}
   simp [this]
  omega
 let q:=r - n;have hq:q<C.size:= by {omega};have re:r=n+q:= by {omega};obtain ⟨op,hg,hop,hne_lr,hl,hr_lt⟩:=hbG C hb q hq;have hSl:(∑ z:Fin n,lM n C z (gL C q)) +
   (∑ z:Fin n,lM n C z (gR C q))=2:= by
  rw [← sum_add_distrib];have h1:∑ z:Fin n,(lM n C z (gL C q)+lM n C z (gR C q)) =
    ∑ z:Fin n,lM n C z r :=
   sC rfl (fun z _=> by rw [re,lmG C hb z q hq])
  omega
 have h1L:=lm1 C hb (gL C q) (by omega);have h1R:=lm1 C hb (gR C q) (by omega);have hL_lt:gL C q<n:= by by_contra hge;have h2:=lm2 C hb (gL C q - n) (by omega);rw [show n+(gL C q - n)=gL C q by omega] at h2;omega
 have hR_lt:gR C q<n:= by by_contra hge;have h2:=lm2 C hb (gR C q - n) (by omega);rw [show n+(gR C q - n)=gR C q by omega] at h2;omega
 let a:Fin n:=⟨gL C q,hL_lt⟩;let b:Fin n:=⟨gR C q,hR_lt⟩;have hab:a≠b:=fun h=>hne_lr (congrArg Fin.val h);have ha_mem:a=u∨a=v:= by {have h1:=hlm a;rw [re,lmG C hb a q hq,lmL n C a (gL C q) hL_lt] at h1;simp only [a,↓reduceIte] at h1;by_contra hno;rw [ite_eq_right_iff.2 (fun h=>(hno h).elim)] at h1;omega};have hb_mem:b=u∨b=v:= by {have h1:=hlm b;rw [re,lmG C hb b q hq,lmL n C b (gR C q) hR_lt] at h1;simp only [b,↓reduceIte] at h1;by_contra hno;rw [ite_eq_right_iff.2 (fun h=>(hno h).elim)] at h1;omega};refine ⟨q,hq,op,re,hop,?_⟩;rcases ha_mem with ha | ha <;> rcases hb_mem with hb | hb;{exact (hab (ha.trans hb.symm)).elim};{left;have hL_eq:gL C q=u.val:=congrArg Fin.val ha;have hR_eq:gR C q=v.val:=congrArg Fin.val hb;rw [hL_eq,hR_eq] at hg;exact hg};{right;have hL_eq:gL C q=v.val:=congrArg Fin.val ha;have hR_eq:gR C q=u.val:=congrArg Fin.val hb;rw [hL_eq,hR_eq] at hg;exact hg};{exact (hab (ha.trans hb.symm)).elim}
lemma lmT {n:ℕ} (C:Circuit) (hb:IsBin n C)
  (r:ℕ) (hr:r<n+C.size) (c u v:Fin n) (hcu:c≠u) (hcv:c≠v) (huv:u≠v)
  (hSr:S1 n C r={c})
  (hlm:∀ z:Fin n,lM n C z r=if z=c∨z=u∨z=v then 1 else 0) :
  ∃ qw qb:ℕ,qw<C.size∧qb<C.size∧r=n+qw ∧
   (C.gates[qw]?=some ⟨.or,[c.val,n+qb]⟩ ∨
    C.gates[qw]?=some ⟨.or,[n+qb,c.val]⟩) ∧
   (C.gates[qb]?=some ⟨.and,[u.val,v.val]⟩ ∨
    C.gates[qb]?=some ⟨.and,[v.val,u.val]⟩):= by
 have hSm:∑ z:Fin n,lM n C z r=3:= by
  have hrw:(∑ z:Fin n,lM n C z r) =
    ∑ z∈(univ:Finset (Fin n)).filter (fun z=>z=c∨z=u∨z=v),1:= by
   rw [sum_filter];exact sC rfl (fun z _=>hlm z)
  have hfl:(univ:Finset (Fin n)).filter (fun z=>z=c∨z=u∨z=v)={c,u,v}:= by {ext z;simp};have hcnot:c∉({u,v}:Finset (Fin n)):= by {simp [hcu,hcv]};rw [hrw,hfl,sum_const,card_insert_of_notMem hcnot,cP0 huv,
   smul_eq_mul,mul_one]
 have hrge:n≤r:= by
  by_contra hlt;have h1:∑ z:Fin n,lM n C z r=1:= by
   have:∀ z:Fin n,lM n C z r=if z=⟨r,by omega⟩ then 1 else 0:= by
    intro z;rw [lmL n C z r (by omega)];by_cases hz:z=⟨r,by omega⟩
    {subst hz;simp};{have hne:r≠z.val:=fun h=>hz (Fin.ext h.symm);simp [hz,hne]}
   simp [this]
  omega
 let qw:=r - n;have hqw:qw<C.size:= by {omega};have re:r=n+qw:= by {omega};obtain ⟨op,hg,hop,_,hl,hr_lt⟩:=hbG C hb qw hqw;have hop_or:op=.or:= by
  rcases hop with rfl | rfl;{
   exfalso;have hc_in:c∈S1 n C (n+qw):= by rw [← re,hSr];exact mem_singleton_self c
   rw [s1A n C qw (gL C qw) (gR C qw) hqw hg hl hr_lt,mem_inter] at hc_in;have h1:=le_trans (sl1 C hb c (gL C qw) (by omega) hc_in.1)
    (slM C hb c (gL C qw) (by omega))
   have h2:=le_trans (sl1 C hb c (gR C qw) (by omega) hc_in.2)
    (slM C hb c (gR C qw) (by omega))
   have h3:=hlm c;rw [re,lmG C hb c qw hqw] at h3;simp only [true_or,↓reduceIte] at h3;omega
  }
  {rfl}
 subst hop_or;have hSl:(∑ z:Fin n,lM n C z (gL C qw)) +
   (∑ z:Fin n,lM n C z (gR C qw))=3:= by
  rw [← sum_add_distrib];have h1:∑ z:Fin n,(lM n C z (gL C qw)+lM n C z (gR C qw)) =
    ∑ z:Fin n,lM n C z r :=
   sC rfl (fun z _=> by rw [re,lmG C hb z qw hqw])
  omega
 have h1L:=lm1 C hb (gL C qw) (by omega);have h1R:=lm1 C hb (gR C qw) (by omega);have hSu:S1 n C (gL C qw)∪S1 n C (gR C qw)={c}:= by {rw [← s1O n C qw (gL C qw) (gR C qw) hqw hg hl hr_lt,← re,hSr]};have hHd:∀ x y:ℕ,(x=gL C qw∧y=gR C qw∨x=gR C qw∧y=gL C qw) →
   ∑ z:Fin n,lM n C z x=1 →
   x=c.val∧∃ qb<C.size,y=n+qb ∧
    (C.gates[qb]?=some ⟨.and,[u.val,v.val]⟩ ∨
     C.gates[qb]?=some ⟨.and,[v.val,u.val]⟩):= by
  intro x y hxy hsumx;have hx_lt:x<n:= by
   by_contra hge;have h2:=lm2 C hb (x - n) (by rcases hxy with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> omega);rw [show n+(x - n)=x by omega] at h2;omega
  have hx_sub:S1 n C x⊆{c}:= by
   rw [← hSu];rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩;{exact subset_union_left};{exact subset_union_right}
  have hx_eq_c:x=c.val:= by {have hMm:(⟨x,hx_lt⟩:Fin n)∈S1 n C x:= by {rw [s1I C ⟨x,hx_lt⟩];exact mem_singleton_self _};exact congrArg Fin.val (m1.1 (hx_sub hMm))};have hy_lm:∀ z:Fin n,lM n C z y=if z=u∨z=v then 1 else 0:= by
   intro z;have hTt:=hlm z;rw [re,lmG C hb z qw hqw] at hTt;have hxy_add:lM n C z x+lM n C z y=lM n C z (gL C qw)+lM n C z (gR C qw):= by
    rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩;{rfl};{exact Nat.add_comm _ _}
   rw [lmL n C z x hx_lt,hx_eq_c] at hxy_add;by_cases hzc:z=c;{
    subst hzc;have hnot_uv:¬ (z=u∨z=v):= by rintro (rfl | rfl);exact hcu rfl;exact hcv rfl
    simp only [true_or,↓reduceIte,hnot_uv] at hTt hxy_add ⊢;omega
   }
   {have hne_val:c.val≠z.val:=fun h=>hzc (Fin.ext h.symm);simp only [hzc,false_or,hne_val,↓reduceIte,zero_add] at hTt hxy_add;omega}
  have hy_lt:y<n+C.size:= by rcases hxy with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
  obtain ⟨qb,hqb,opb,hy_eq,hopb,hgb⟩:=lmP C hb y hy_lt u v huv hy_lm;have hopb_and:opb=.and:= by
   rcases hopb with rfl | rfl;{rfl};{
    exfalso;have hy_sub:S1 n C y⊆{c}:= by
     rw [← hSu];rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩;{exact subset_union_right};{exact subset_union_left}
    have hu_in_y:u∈S1 n C y:= by
     rw [hy_eq];rcases hgb with hgb1 | hgb2;{rw [s1O n C qb u.val v.val hqb hgb1 (by omega) (by omega),s1I,s1I,mem_union];exact Or.inl (mem_singleton_self u)};{rw [s1O n C qb v.val u.val hqb hgb2 (by omega) (by omega),s1I,s1I,mem_union];exact Or.inr (mem_singleton_self u)}
    exact hcu (m1.1 (hy_sub hu_in_y)).symm
   }
  subst hopb_and;exact ⟨hx_eq_c,qb,hqb,hy_eq,hgb⟩
 by_cases hL1:∑ z:Fin n,lM n C z (gL C qw)=1;{obtain ⟨hL_eq,qb,hqb,hR_eq,hgb⟩:=hHd (gL C qw) (gR C qw) (Or.inl ⟨rfl,rfl⟩) hL1;rw [hL_eq,hR_eq] at hg;exact ⟨qw,qb,hqw,hqb,re,Or.inl hg,hgb⟩};{
  have hR1:∑ z:Fin n,lM n C z (gR C qw)=1:= by {omega};obtain ⟨hR_eq,qb,hqb,hL_eq,hgb⟩:=hHd (gR C qw) (gL C qw) (Or.inr ⟨rfl,rfl⟩) hR1;rw [hL_eq,hR_eq] at hg;exact ⟨qw,qb,hqw,hqb,re,Or.inr hg,hgb⟩
 }
lemma eoU {n:ℕ} (S1 S2:Finset ℕ) (x:Fin n→ Bool) :
  eO (S1∪S2) x=(eO S1 x||eO S2 x):= by
 apply Bool.eq_iff_iff.2;simp only [eO,bOt,decide_eq_true_eq,mem_union];constructor;{
  rintro ⟨i,j,h1 | h2,hij,hxi,hxj⟩;{exact Or.inl ⟨i,j,h1,hij,hxi,hxj⟩};{exact Or.inr ⟨i,j,h2,hij,hxi,hxj⟩}
 }
 {rintro (⟨i,j,h1,hij,hxi,hxj⟩ | ⟨i,j,h2,hij,hxi,hxj⟩);{exact ⟨i,j,Or.inl h1,hij,hxi,hxj⟩};{exact ⟨i,j,Or.inr h2,hij,hxi,hxj⟩}}
lemma eoS {n:ℕ} {u v:Fin n} (huv:(u.val+1)%n=v.val) (x:Fin n→ Bool) :
  (x u&&x v)=eO {u.val} x:= by
 apply Bool.eq_iff_iff.2;simp only [eO,bAt,decide_eq_true_eq,m1];constructor;{rintro ⟨hu,hv⟩;exact ⟨u,v,rfl,huv,hu,hv⟩};{rintro ⟨i,j,hi,hij,hxi,hxj⟩;have hiu:i=u:=Fin.ext hi;rw [hiu] at hij hxi;have hjv:j=v:=Fin.ext (hij.symm.trans huv);rw [hjv] at hxj;exact ⟨hxi,hxj⟩}
lemma eoSt {n:ℕ} (hn:5≤n) (c:Fin n) (x:Fin n→ Bool) :
  (x c&&(x (cP (by omega) c)||x (cN (by omega) c))) =
   eO {(cP (by omega) c).val,c.val} x:= by
 apply Bool.eq_iff_iff.2;simp only [eO,bAt,bOt,decide_eq_true_eq,
  mI,m1]
 have hpc:((cP (by omega) c).val+1)%n=c.val :=
  congrArg Fin.val (cnP (by omega) c)
 have hcn:(c.val+1)%n=(cN (by omega) c).val:=rfl;constructor;{
  rintro ⟨hxc,hxp | hxn⟩;{exact ⟨cP (by omega) c,c,Or.inl rfl,hpc,hxp,hxc⟩};{exact ⟨c,cN (by omega) c,Or.inr rfl,hcn,hxc,hxn⟩}
 }
 {rintro ⟨i,j,hi | hi,hij,hxi,hxj⟩;{have hi':i=cP (by omega) c:=Fin.ext hi;rw [hi'] at hij hxi;have hj':j=c:=Fin.ext (hij.symm.trans hpc);rw [hj'] at hxj;exact ⟨hxj,Or.inl hxi⟩};{have hi':i=c:=Fin.ext hi;rw [hi'] at hij hxi;have hj':j=cN (by omega) c:=Fin.ext (hij.symm.trans hcn);rw [hj'] at hxj;exact ⟨hxi,Or.inr hxj⟩}}
lemma eoTP {n:ℕ} (hn:5≤n) {u0 v0 c:Fin n}
  (huv:(u0.val+1)%n=v0.val) (hc:c=cP (by omega) u0) (x:Fin n→ Bool) :
  (((x u0&&x v0)||x c)&&(x (cP (by omega) c)||x (cN (by omega) c))) =
   eO {(cP (by omega) c).val,c.val,u0.val} x:= by
 have hnext:cN (by omega) c=u0:= by {rw [hc,cnP]};rw [hnext];apply Bool.eq_iff_iff.2;simp only [eO,bAt,bOt,decide_eq_true_eq,
  mI,m1]
 have hpc:((cP (by omega) c).val+1)%n=c.val :=
  congrArg Fin.val (cnP (by omega) c)
 have hcu:(c.val+1)%n=u0.val:=congrArg Fin.val hnext;constructor;{
  rintro ⟨⟨hu,hv⟩ | hxc,hxp | hxu⟩;{exact ⟨u0,v0,Or.inr (Or.inr rfl),huv,hu,hv⟩};{exact ⟨u0,v0,Or.inr (Or.inr rfl),huv,hu,hv⟩};{exact ⟨cP (by omega) c,c,Or.inl rfl,hpc,hxp,hxc⟩};{exact ⟨c,u0,Or.inr (Or.inl rfl),hcu,hxc,hxu⟩}
 }
 {rintro ⟨i,j,hi | hi | hi,hij,hxi,hxj⟩;{have hi':i=cP (by omega) c:=Fin.ext hi;rw [hi'] at hij hxi;have hj':j=c:=Fin.ext (hij.symm.trans hpc);rw [hj'] at hxj;exact ⟨Or.inr hxj,Or.inl hxi⟩};{have hi':i=c:=Fin.ext hi;rw [hi'] at hij hxi;have hj':j=u0:=Fin.ext (hij.symm.trans hcu);rw [hj'] at hxj;exact ⟨Or.inr hxi,Or.inr hxj⟩};{have hi':i=u0:=Fin.ext hi;rw [hi'] at hij hxi;have hj':j=v0:=Fin.ext (hij.symm.trans huv);rw [hj'] at hxj;exact ⟨Or.inl ⟨hxi,hxj⟩,Or.inr hxi⟩}}
lemma eoTN {n:ℕ} (hn:5≤n) {u0 v0 c:Fin n}
  (huv:(u0.val+1)%n=v0.val) (hc:c=cN (by omega) v0) (x:Fin n→ Bool) :
  (((x u0&&x v0)||x c)&&(x (cP (by omega) c)||x (cN (by omega) c))) =
   eO {u0.val,v0.val,c.val} x:= by
 have hPv:cP (by omega) c=v0:= by {rw [hc,cpN]};rw [hPv];apply Bool.eq_iff_iff.2;simp only [eO,bAt,bOt,decide_eq_true_eq,
  mI,m1]
 have hvc:(v0.val+1)%n=c.val:=congrArg Fin.val hc.symm;have hcn:(c.val+1)%n=(cN (by omega) c).val:=rfl;constructor;{
  rintro ⟨⟨hu,hv⟩ | hxc,hxv | hxn⟩;{exact ⟨u0,v0,Or.inl rfl,huv,hu,hv⟩};{exact ⟨u0,v0,Or.inl rfl,huv,hu,hv⟩};{exact ⟨v0,c,Or.inr (Or.inl rfl),hvc,hxv,hxc⟩};{exact ⟨c,cN (by omega) c,Or.inr (Or.inr rfl),hcn,hxc,hxn⟩}
 }
 {rintro ⟨i,j,hi | hi | hi,hij,hxi,hxj⟩;{have hi':i=u0:=Fin.ext hi;rw [hi'] at hij hxi;have hj':j=v0:=Fin.ext (hij.symm.trans huv);rw [hj'] at hxj;exact ⟨Or.inl ⟨hxi,hxj⟩,Or.inl hxj⟩};{have hi':i=v0:=Fin.ext hi;rw [hi'] at hij hxi;have hj':j=c:=Fin.ext (hij.symm.trans hvc);rw [hj'] at hxj;exact ⟨Or.inr hxj,Or.inl hxi⟩};{have hi':i=c:=Fin.ext hi;rw [hi'] at hij hxi;have hj':j=cN (by omega) c:=Fin.ext (hij.symm.trans hcn);rw [hj'] at hxj;exact ⟨Or.inr hxi,Or.inr hxj⟩}}
abbrev QS (n:ℕ) (C:Circuit) (qz wc yc:Fin n→ ℕ):Prop:=∀ c∈IS n C,qz c<C.size∧(C.gates[qz c]?=some ⟨.and,[wc c,yc c]⟩∨C.gates[qz c]?=some ⟨.and,[yc c,wc c]⟩)∧S1 n C (wc c)={c}∧(∀ u:Fin n,cA c u→ u∈S1 n C (yc c))∧c∉S1 n C (yc c)
lemma d2E {n:ℕ} (C:Circuit) (hn:5≤n)
  (hIc:(IS n C).card=n/2)
  (hIN:∀ c∈IS n C,∀ u:Fin n,cA c u→ u∈D2 n C) :
  ((univ:Finset (Fin n)).filter
   fun u=>u∈D2 n C∧cN (by omega) u∈D2 n C).card=n %2:= by
 let I:Finset (Fin n):=IS n C;let E:=(univ:Finset (Fin n)).filter fun u=>u∈D2 n C∧cN (by omega) u∈D2 n C;let P:=I.image (cP (by omega));have hPc:P.card=n/2:= by {rw [card_image_of_injective I (cpJ (by omega)),hIc]};have hIP:Disjoint I P:= by {rw [disjoint_left];intro u huI huP;obtain ⟨c,hcI,rfl⟩:=mG.1 huP;exact (mS.1 huI).2 (hIN c hcI _ (cpA (by omega) c))};have hIE:Disjoint I E:= by {rw [disjoint_left];intro u huI huE;exact (mS.1 huI).2 (mF.1 huE).2.1};have hPE:Disjoint P E:= by {rw [disjoint_left];intro u huP huE;obtain ⟨c,hcI,rfl⟩:=mG.1 huP;have h2:=(mF.1 huE).2.2;rw [cnP] at h2;exact (mS.1 hcI).2 h2};have hUn:I∪P∪E=univ:= by
  ext u
  simp only [mem_union,mU,iff_true];by_cases huI:u∈I;{exact Or.inl (Or.inl huI)};{
   have hu2:u∈D2 n C:= by {by_contra hno;exact huI (mS.2 ⟨mU u,hno⟩)};by_cases hnI:cN (by omega) u∈I;{exact Or.inl (Or.inr (mG.2 ⟨cN (by omega) u,hnI,cpN (by omega) u⟩))};{
    have hn2:cN (by omega) u∈D2 n C:= by {by_contra hno;exact hnI (mS.2 ⟨mU _,hno⟩)};exact Or.inr (mF.2 ⟨mU u,hu2,hn2⟩)
   }
  }
 have hTt:=congrArg Finset.card hUn;rw [card_univ,Fintype.card_fin,
  card_union_of_disjoint (disjoint_union_left.2 ⟨hIE,hPE⟩),
  card_union_of_disjoint hIP,hIc,hPc] at hTt
 change E.card=n %2;omega
lemma noA {n:ℕ} (C:Circuit) (hn:5≤n)
  (hf:circuitFun n C=cF n) (ho:C.output=n+C.size - 1) (hb:IsBin n C)
  (hd1:∀ q,q+1<C.size→ wD C (n+q)=1) (hp:0<C.size)
  (hMI:∀ v:Fin n,v∈IS n C↔wD C v.val=1)
  (hM2:∀ v:Fin n,v∈D2 n C↔wD C v.val=2)
  (hIN:∀ c∈IS n C,∀ u:Fin n,cA c u→ u∈D2 n C)
  (hEC:((univ:Finset (Fin n)).filter
   fun u=>u∈D2 n C∧cN (by omega) u∈D2 n C).card=n %2)
  (qz wc yc:Fin n→ ℕ)
  (hQS:QS n C qz wc yc)
  (hQC:∀ c∈IS n C,
   (gL C (qz c)=wc c∧gR C (qz c)=yc c) ∨
   (gL C (qz c)=yc c∧gR C (qz c)=wc c))
  (hwl:∀ c∈IS n C,wc c<n+qz c)
  (hyl:∀ c∈IS n C,yc c<n+qz c)
  (hQI:Set.InjOn qz ((IS n C:Finset (Fin n)):Set (Fin n)))
  (hLQ:∀ c∈IS n C,∀ v:Fin n,
   lM n C v (n+qz c)=lM n C v (wc c)+lM n C v (yc c))
  (hKY:∀ c∈IS n C,∀ u:Fin n,cA c u→ 1≤kS n C u (qz c)) :
  ∀ c∈IS n C,∀ q<C.size,iS n C (n+qz c) (n+q)→ q≠qz c →
   ∀ g,C.gates[q]?=some g→ g.op=.or:= by
 classical
 let I:Finset (Fin n):=IS n C;by_contra hbad;push Not at hbad;let Bad:=(range C.size).filter fun q =>
  ∃ c∈I,iS n C (n+qz c) (n+q)∧q≠qz c ∧
   ∃ g,C.gates[q]?=some g∧g.op=.and
 have hBn:Bad.Nonempty:= by {obtain ⟨c,hc,q,hq,hsb,hne,g,hg,hopne⟩:=hbad;refine ⟨q,mF.2 ⟨mR.2 hq,c,hc,hsb,hne,g,hg,?_⟩⟩;obtain ⟨op,hg',hop,_,_,_⟩:=hbG C hb q hq;rw [hg] at hg';obtain rfl:=oI hg';exact hop.resolve_right hopne};let q:=Bad.max' hBn;obtain ⟨hq_rng,c,hc,sbq,hq_ne,gq,hgq,hgq_and⟩:=mF.1 (max'_mem Bad hBn);have hq:q<C.size:=mR.1 hq_rng;have hOq:∀ r<C.size,iS n C (n+q) (n+r)→ r≠q →
   ∀ g,C.gates[r]?=some g→ g.op=.or:= by
  intro r hr sbr hrne gr hgr;obtain ⟨opr,hgr',hopr,_,_,_⟩:=hbG C hb r hr;rw [hgr] at hgr';obtain rfl:=oI hgr';rcases hopr with rfl | rfl;{
   exfalso;have hle_qr:=isL C hb sbr;have hle_cq:=isL C hb sbq;have hr_in:r∈Bad:=mF.2 ⟨mR.2 hr,c,hc,
    ReflTransGen.trans sbq sbr,by omega,
    ⟨.and,[gL C r,gR C r]⟩,hgr,rfl⟩
   have hle_max:=le_max' Bad r hr_in;omega
  }
  {rfl}
 have hFq:=wvO C hf ho hb hd1 hp q hq hOq;have hSq:S1 n C (n+q)=∅:= by
  ext u
  simp only [S1,mF,mU,true_and,mN,iff_false];intro hTr;have:=hFq (oH u) hTr;rw [cf1 hn u] at this;cases this
 obtain ⟨opq,hgq',_,_,hl_q,hr_q⟩:=hbG C hb q hq;rw [hgq] at hgq';obtain rfl:=oI hgq';simp only at hgq_and;subst hgq_and;have hAB:∃ A B:ℕ,((A=gL C q∧B=gR C q)∨(A=gR C q∧B=gL C q)) ∧
   iS n C (n+qz c) A:= by
  rcases ReflTransGen.cases_tail sbq with hEq | ⟨w',hPv,hls⟩;{exact (hq_ne (by omega)).elim};{
   obtain ⟨q',_,g',hg',heqq,hwin⟩:=hls;have hqq':q'=q:= by omega
   subst hqq';rw [hgq] at hg';obtain rfl:=oI hg';simp only [List.mem_cons,List.not_mem_nil,or_false] at hwin;rcases hwin with rfl | rfl;{exact ⟨gL C q,gR C q,Or.inl ⟨rfl,rfl⟩,hPv⟩};{exact ⟨gR C q,gL C q,Or.inr ⟨rfl,rfl⟩,hPv⟩}
  }
 obtain ⟨A,B,hAB_eq,sbA⟩:=hAB;have hB_lt:B<n+q:= by rcases hAB_eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
 have hLA:1≤lM n C c A:= by
  have h1:1≤lM n C c (wc c):=le_trans
   (sl1 C hb c (wc c) (by have:=hwl c hc;have:=(hQS c hc).1;omega)
    (by rw [(hQS c hc).2.2.1];exact mem_singleton_self c))
   (slM C hb c (wc c) (by have:=hwl c hc;have:=(hQS c hc).1;omega))
  have h2:lM n C c (wc c)≤lM n C c (n+qz c):= by {rw [hLQ c hc c];omega};have h3:lM n C c (n+qz c)≤lM n C c A:=lmM C hb c sbA;omega
 have hLQ0:lM n C c (n+q)≤1:= by {have h1:=lmM C hb c (isO C ho hb hd1 hp q hq);rw [lmO C ho hb hd1 hp c,(hMI c).1 hc] at h1;exact h1};have hAB0:lM n C c A+lM n C c B=lM n C c (n+q):= by
  rw [lmG C hb c q hq];rcases hAB_eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩;{rfl};{exact Nat.add_comm _ _}
 have hLB:lM n C c B=0:= by {omega};have hLq:lM n C c (n+q)=1:= by {omega};have hBN:∀ u:Fin n,cA c u→ u∈S1 n C B:= by
  intro u hAd;by_contra hunot;have hval_u:wv C (oH u) B=false :=
   Bool.eq_false_iff.2 (fun hTr=>hunot (mF.2 ⟨mU u,hTr⟩))
  have hPB:wv C (pI c u) B=false:= by
   rw [← hval_u];apply wvZ C hb (pI c u) (oH u) B (by omega);intro i hi;have hic:i≠c:=fun h=> by rw [h,hLB] at hi;omega
   simp [pI,oH,hic]
  have hQE0:wv C (pI c u) (n+q)=wv C (oH u) (n+q):= by
   rw [wvA C (pI c u) q (gL C q) (gR C q) hq hgq hl_q hr_q,
    wvA C (oH u) q (gL C q) (gR C q) hq hgq hl_q hr_q]
   rcases hAB_eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩;{rw [hPB,hval_u,Bool.and_false,Bool.and_false]};{rw [hPB,hval_u,Bool.false_and,Bool.false_and]}
  have hCZ:lmC n C {q} c C.output=0:= by
   have hTt:=lmcO C ho hb hd1 hp {q}
    (by simp [hq]) (by intro t1 ht1 t2 ht2 _;simp at ht1 ht2;omega) c
   rw [sum_singleton,hLq,(hMI c).1 hc] at hTt;omega
  have hout_eq:wv C (pI c u) C.output=wv C (oH u) C.output:= by
   apply wvcZ C hb {q} (pI c u) (oH u)
    (by intro t ht;rw [m1.1 ht];exact hQE0) C.output (by omega)
   intro i hi;have hic:i≠c:=fun h=> by rw [h,hCZ] at hi;omega
   simp [pI,oH,hic]
  have hf1:=congrFun hf (pI c u);have hf2:=congrFun hf (oH u);change wv C (pI c u) C.output=cF n (pI c u) at hf1;change wv C (oH u) C.output=cF n (oH u) at hf2;have hTr:cF n (pI c u)=true:=(cf2 hn c u).2 hAd;rw [← hf1,hout_eq,hf2,cf1 hn u] at hTr;cases hTr
 by_cases hQq:∃ c'∈I,q=qz c';{
  obtain ⟨c',hc',hqq'⟩:=hQq;have hcc':c'≠c:=fun h=>hq_ne (hqq'.trans (congrArg qz h));have hB_eq_yc':B=yc c':= by
   have hch:=hQC c' hc';rw [← hqq'] at hch;have hB_ne_wc':B≠wc c':= by
    intro hbw;have h1:cN (by omega) c∈S1 n C (wc c'):= by rw [← hbw];exact hBN _ (cnA (by omega) c)
    have h2:cP (by omega) c∈S1 n C (wc c'):= by {rw [← hbw];exact hBN _ (cpA (by omega) c)};rw [(hQS c' hc').2.2.1,m1] at h1 h2;exact cnNP hn c (h1.trans h2.symm)
   rcases hAB_eq with ⟨_,hB'⟩ | ⟨_,hB'⟩ <;> rcases hch with ⟨hL',hR'⟩ | ⟨hL',hR'⟩;{exact hB'.trans hR'};{exact (hB_ne_wc' (hB'.trans hR')).elim};{exact (hB_ne_wc' (hB'.trans hL')).elim};{exact hB'.trans hL'}
  have hSa:∀ u∈S1 n C (yc c'),cA c' u:= by
   intro u hu;have hw_true:wv C (pI c' u) (wc c')=true:= by
    apply wvM C hb (oH c') (pI c' u)
     (fun i hi=> by simp [oH] at hi;simp [pI,hi])
     (wc c') (by have:=hwl c' hc';have:=(hQS c' hc').1;omega)
    have hc'_mem:c'∈S1 n C (wc c'):= by {rw [(hQS c' hc').2.2.1];exact mem_singleton_self c'};exact (mF.1 hc'_mem).2
   have hy_true:wv C (pI c' u) (yc c')=true:= by
    apply wvM C hb (oH u) (pI c' u)
     (fun i hi=> by simp [oH] at hi;simp [pI,hi])
     (yc c') (by have:=hyl c' hc';have:=(hQS c' hc').1;omega)
    exact (mF.1 hu).2
   have hq_true:wv C (pI c' u) (n+q)=true:= by
    rw [wvA C (pI c' u) q (gL C q) (gR C q) hq hgq hl_q hr_q,bAt];have hch:=hQC c' hc';rw [← hqq'] at hch;rcases hch with ⟨h1,h2⟩ | ⟨h1,h2⟩;{rw [h1,h2];exact ⟨hw_true,hy_true⟩};{rw [h1,h2];exact ⟨hy_true,hw_true⟩}
   exact (cf2 hn c' u).1 (hFq (pI c' u) hq_true)
  exact hcc' (caC hn
   (hSa _ (by rw [← hB_eq_yc'];exact hBN _ (cnA (by omega) c)))
   (hSa _ (by rw [← hB_eq_yc'];exact hBN _ (cpA (by omega) c))))
 }
 {
  push Not at hQq;have hN1:∀ u:Fin n,cA c u→ (I.filter fun c'=>cA c' u).card≤1:= by
   intro u hAd;have hu2:u∈D2 n C:=hIN c hc u hAd;have hkq:1≤kS n C u q:= by
    unfold kS;have hNt0:u∉S1 n C (n+q):= by rw [hSq];exact mN u
    simp only [hNt0,not_false_eq_true,↓reduceIte];have h1:=sl1 C hb u B (by omega) (hBN u hAd);rcases hAB_eq with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
   let N:=I.filter fun c'=>cA c' u;let S:=insert q (N.image qz);have hqi:q∉N.image qz:= by {intro hm;obtain ⟨c',hc'N,hqq'⟩:=mG.1 hm;exact hQq c' (mF.1 hc'N).1 hqq'.symm};have hSs0:S⊆range C.size:= by
    intro r hr;rcases mI.1 hr with rfl | hr';{exact mR.2 hq};{obtain ⟨c',hc'N,rfl⟩:=mG.1 hr';exact mR.2 (hQS c' (mF.1 hc'N).1).1}
   have hSg:∀ r∈S,1≤kS n C u r:= by
    intro r hr;rcases mI.1 hr with rfl | hr';{exact hkq};{obtain ⟨c',hc'N,rfl⟩:=mG.1 hr';obtain ⟨hc'I,hc'adj⟩:=mF.1 hc'N;exact hKY c' hc'I u hc'adj}
   have hcl:S.card≤∑ r∈range C.size,kS n C u r:= by
    calc S.card=∑ _r∈S,1:= by simp
     _≤∑ r∈S,kS n C u r:=sum_le_sum hSg
     _≤∑ r∈range C.size,kS n C u r :=
      sum_le_sum_of_subset_of_nonneg hSs0 (fun _ _ _=>zL _)
   rw [kSS C hn hf ho hb hd1 hp u,(hM2 u).1 hu2] at hcl;have hNj:Set.InjOn qz (N:Set (Fin n)) :=
    hQI.mono (fun x hx=>(mF.1 hx).1)
   rw [card_insert_of_notMem hqi,card_image_of_injOn hNj] at hcl;change N.card≤1;omega
  let u1:=cN (by omega) c;let u2:=cP (by omega) c;have h1D:u1∈D2 n C:=hIN c hc u1 (cnA (by omega) c);have h2D:u2∈D2 n C:=hIN c hc u2 (cpA (by omega) c);have h1N:cN (by omega) u1∈D2 n C:= by
   by_contra hno;have hmem1:cN (by omega) u1∈I:=mS.2 ⟨mU _,hno⟩;have hne:cN (by omega) u1≠c:= by have:cP (by omega) u1=c:=cpN (by omega) c;rw [← this];exact cnNP hn u1
   have hle:=hN1 u1 (cnA (by omega) c);have hPr:({c,cN (by omega) u1}:Finset (Fin n))⊆I.filter fun c'=>cA c' u1:= by
    intro x hx;rcases mI.1 hx with hxc | hx';{rw [hxc];exact mF.2 ⟨hc,cnA (by omega) c⟩};{rw [m1.1 hx'];exact mF.2 ⟨hmem1,Or.symm (cnA (by omega) u1)⟩}
   have h2:=card_le_card hPr;rw [cP0 (Ne.symm hne)] at h2;omega
  have h2P:cP (by omega) u2∈D2 n C:= by
   by_contra hno;have hmem2:cP (by omega) u2∈I:=mS.2 ⟨mU _,hno⟩;have hne:c≠cP (by omega) u2:= by have:cN (by omega) u2=c:=cnP (by omega) c;rw [← this];exact cnNP hn u2
   have hle:=hN1 u2 (cpA (by omega) c);have hPr:({c,cP (by omega) u2}:Finset (Fin n))⊆I.filter fun c'=>cA c' u2:= by
    intro x hx;rcases mI.1 hx with hxc | hx';{rw [hxc];exact mF.2 ⟨hc,cpA (by omega) c⟩};{rw [m1.1 hx'];exact mF.2 ⟨hmem2,Or.symm (cpA (by omega) u2)⟩}
   have h2:=card_le_card hPr;rw [cP0 hne] at h2;omega
  let E:=(univ:Finset (Fin n)).filter fun u=>u∈D2 n C∧cN (by omega) u∈D2 n C;have hPr:({u1,cP (by omega) u2}:Finset (Fin n))⊆E:= by
   intro x hx;rcases mI.1 hx with rfl | hx';{exact mF.2 ⟨mU u1,h1D,h1N⟩};{rw [m1.1 hx'];exact mF.2 ⟨mU _,h2P,by rw [cnP];exact h2D⟩}
  have h2:=card_le_card hPr;rw [cP0 (cnPP hn c)] at h2;have hEm:E.card=n %2:=hEC;omega
 }
lemma cfP {n:ℕ} (C:Circuit) (hn:5≤n)
  (hf:circuitFun n C=cF n) (ho:C.output=n+C.size - 1) (hb:IsBin n C)
  (hd1:∀ q,q+1<C.size→ wD C (n+q)=1) (hp:0<C.size)
  (qz wc yc:Fin n→ ℕ)
  (hQS:QS n C qz wc yc)
  (hwl:∀ c∈IS n C,wc c<n+qz c)
  (hyl:∀ c∈IS n C,yc c<n+qz c)
  (hNA:∀ c∈IS n C,∀ q<C.size,
   iS n C (n+qz c) (n+q)→ q≠qz c→ ∀ g,C.gates[q]?=some g→ g.op=.or)
  (hYP:∀ c∈IS n C,∀ v:Fin n,
   lM n C v (yc c)=if cA c v then 1 else 0)
  (hCs :
   ((∀ v:Fin n,lmC n C ((IS n C).image qz) v C.output=0) ∧
    (∀ c∈IS n C,∀ v:Fin n,lM n C v (wc c)=if v=c then 1 else 0)) ∨
   (∃ u0 v0 cs:Fin n,(u0.val+1)%n=v0.val∧cs∈IS n C ∧
    (cs=cP (by omega) u0∨cs=cN (by omega) v0) ∧
    u0∈D2 n C∧v0∈D2 n C ∧
    (∀ v:Fin n,lmC n C ((IS n C).image qz) v C.output=0) ∧
    (∀ c∈IS n C,c≠cs→ ∀ v:Fin n,lM n C v (wc c)=if v=c then 1 else 0) ∧
    (∀ v:Fin n,lM n C v (wc cs)=if v=cs∨v=u0∨v=v0 then 1 else 0)) ∨
   (∃ u0 v0:Fin n,(u0.val+1)%n=v0.val∧u0≠v0 ∧
    (∀ v:Fin n,lmC n C ((IS n C).image qz) v C.output=if v=u0∨v=v0 then 1 else 0) ∧
    (∀ c∈IS n C,∀ v:Fin n,lM n C v (wc c)=if v=c then 1 else 0))) :
  ∀ t:ℕ,t<C.size→ wC n C (n+t):= by
 let I:Finset (Fin n):=IS n C;let T:Finset ℕ:=I.image qz;have hYS:∀ c∈I,∃ qy<C.size,yc c=n+qy ∧
   (C.gates[qy]?=some ⟨.or,[(cP (by omega) c).val,(cN (by omega) c).val]⟩ ∨
    C.gates[qy]?=some ⟨.or,[(cN (by omega) c).val,(cP (by omega) c).val]⟩) ∧
   (∀ x:Fin n→ Bool,wv C x (yc c)=(x (cP (by omega) c)||x (cN (by omega) c))):= by
  intro c hc;have hylt:yc c<n+C.size:= by have:=hyl c hc;have:=(hQS c hc).1;omega
  have hlm:∀ z:Fin n,lM n C z (yc c) =
    if z=cP (by omega) c∨z=cN (by omega) c then 1 else 0:= by
   intro z;simp only [hYP c hc z,caI hn c z,or_comm]
  obtain ⟨qy,hqy,opy,hy_eq,hopy,hgy⟩:=lmP C hb (yc c) hylt
   (cP (by omega) c) (cN (by omega) c) (Ne.symm (cnNP hn c)) hlm
  have hop_or:opy=.or:= by
   rcases hopy with rfl | rfl;{
    exfalso;have h1:cN (by omega) c∈S1 n C (yc c):=(hQS c hc).2.2.2.1 _ (cnA (by omega) c);rw [hy_eq] at h1;rcases hgy with hgy1 | hgy2;{
     rw [s1A n C qy _ _ hqy hgy1 (by omega) (by omega),s1I,s1I,
      mem_inter,m1,m1] at h1
     exact cnNP hn c h1.1
    }
    {
     rw [s1A n C qy _ _ hqy hgy2 (by omega) (by omega),s1I,s1I,
      mem_inter,m1,m1] at h1
     exact cnNP hn c h1.2
    }
   }
   {rfl}
  subst hop_or;refine ⟨qy,hqy,hy_eq,hgy,?_⟩;intro x;rw [hy_eq];rcases hgy with hgy1 | hgy2;{rw [wvR C x qy _ _ hqy hgy1 (by omega) (by omega),wvI,wvI]};{rw [wvR C x qy _ _ hqy hgy2 (by omega) (by omega),wvI,wvI,Bool.or_comm]}
 have hWP:∀ c∈I,(∀ v:Fin n,lM n C v (wc c)=if v=c then 1 else 0) →
   wc c=c.val ∧
   (∃ S:Finset ℕ,S.Nonempty∧(∀ i∈S,i<n) ∧
    ∀ x:Fin n→ Bool,wv C x (n+qz c)=eO S x):= by
  intro c hc hwc1;have wl:wc c<n+C.size:= by have:=hwl c hc;have:=(hQS c hc).1;omega
  have we:=lmI C hb (wc c) wl c hwc1;obtain ⟨_,_,_,_,hy_val⟩:=hYS c hc;refine ⟨we,{(cP (by omega) c).val,c.val},by simp,?_,?_⟩
  {intro i hi;rcases mI.1 hi with rfl | hi';{exact (cP (by omega) c).2};{rw [m1.1 hi'];exact c.2}};{
   intro x;obtain ⟨hqz,hGt,_,_,_⟩:=hQS c hc;have h1:wv C x (n+qz c)=(wv C x (wc c)&&wv C x (yc c)):= by
    rcases hGt with h | h;{exact wvA C x (qz c) (wc c) (yc c) hqz h (hwl c hc) (hyl c hc)};{rw [wvA C x (qz c) (yc c) (wc c) hqz h (hyl c hc) (hwl c hc),Bool.and_comm]}
   rw [h1,we,wvI,hy_val,eoSt hn c x]
  }
 have hTB:∀ (u0 v0 cs:Fin n),(u0.val+1)%n=v0.val→ cs∈I →
   u0∈D2 n C→ v0∈D2 n C →
   (∀ v:Fin n,lM n C v (wc cs)=if v=cs∨v=u0∨v=v0 then 1 else 0) →
   ∃ qw qb:ℕ,qw<C.size∧qb<C.size∧wc cs=n+qw ∧
    (C.gates[qw]?=some ⟨.or,[cs.val,n+qb]⟩ ∨
     C.gates[qw]?=some ⟨.or,[n+qb,cs.val]⟩) ∧
    (C.gates[qb]?=some ⟨.and,[u0.val,v0.val]⟩ ∨
     C.gates[qb]?=some ⟨.and,[v0.val,u0.val]⟩) ∧
    (∀ x:Fin n→ Bool,wv C x (n+qb)=(x u0&&x v0)) ∧
    (∀ x:Fin n→ Bool,wv C x (n+qw)=((x u0&&x v0)||x cs)):= by
  intro u0 v0 cs huv hsI hu0D hv0D hWk;have hcu:cs≠u0:=fun h=>(mS.1 hsI).2 (h▸hu0D);have hcv:cs≠v0:=fun h=>(mS.1 hsI).2 (h▸hv0D);have huvn:u0≠v0:=fun h=>caR hn u0 (Or.inl (h▸huv));have wl:wc cs<n+C.size:= by have:=hwl cs hsI;have:=(hQS cs hsI).1;omega
  obtain ⟨qw,qb,hqw,hqb,we,hgw,hgb⟩ :=
   lmT C hb (wc cs) wl cs u0 v0 hcu hcv huvn (hQS cs hsI).2.2.1 hWk
  have hbw:n+qb<n+qw:= by
   obtain ⟨_,hg',_,_,hl,hr⟩:=hbG C hb qw hqw;rcases hgw with h1 | h1;{
    rw [h1] at hg';have:=congrArg Gate.inputs (oI hg');have:n+qb=gR C qw:= by injection this with _ h2;injection h2
    omega
   }
   {
    rw [h1] at hg';have:=congrArg Gate.inputs (oI hg');have:n+qb=gL C qw:= by injection this
    omega
   }
  have hbv:∀ x:Fin n→ Bool,wv C x (n+qb)=(x u0&&x v0):= by
   intro x;rcases hgb with hgb1 | hgb2;{rw [wvA C x qb u0.val v0.val hqb hgb1 (by omega) (by omega),wvI,wvI]};{rw [wvA C x qb v0.val u0.val hqb hgb2 (by omega) (by omega),wvI,wvI,Bool.and_comm]}
  have hwv:∀ x:Fin n→ Bool,wv C x (n+qw)=((x u0&&x v0)||x cs):= by
   intro x;rcases hgw with hgw1 | hgw2;{rw [wvR C x qw cs.val (n+qb) hqw hgw1 (by omega) hbw,wvI,hbv,Bool.or_comm]};{rw [wvR C x qw (n+qb) cs.val hqw hgw2 hbw (by omega),wvI,hbv]}
  exact ⟨qw,qb,hqw,hqb,we,hgw,hgb,hbv,hwv⟩
 have hQE:∀ c∈I,∃ S:Finset ℕ,S.Nonempty∧(∀ i∈S,i<n) ∧
   ∀ x:Fin n→ Bool,wv C x (n+qz c)=eO S x:= by
  intro c hc;rcases hCs with ⟨_,hWa⟩ | ⟨u0,v0,cs,huv,hsI,hCe,hu0D,hv0D,_,hWo,hWk⟩ | ⟨_,_,_,_,_,hWa⟩;{exact (hWP c hc (hWa c hc)).2};{
   by_cases hcc:c=cs;{
    rw [hcc];obtain ⟨qw,qb,_,_,we,_,_,_,hwv⟩:=hTB u0 v0 cs huv hsI hu0D hv0D hWk;obtain ⟨_,_,_,_,hy_val⟩:=hYS cs hsI;have hqz_val:∀ x:Fin n→ Bool,wv C x (n+qz cs) =
      (((x u0&&x v0)||x cs)&&(x (cP (by omega) cs)||x (cN (by omega) cs))):= by
     intro x;obtain ⟨hqz,hGt,_,_,_⟩:=hQS cs hsI;have h1:wv C x (n+qz cs)=(wv C x (wc cs)&&wv C x (yc cs)):= by
      rcases hGt with h | h;{exact wvA C x (qz cs) (wc cs) (yc cs) hqz h (hwl cs hsI) (hyl cs hsI)};{rw [wvA C x (qz cs) (yc cs) (wc cs) hqz h (hyl cs hsI) (hwl cs hsI),Bool.and_comm]}
     rw [h1,we,hwv,hy_val]
    rcases hCe with hcp | hcn;{
     refine ⟨{(cP (by omega) cs).val,cs.val,u0.val},by simp,?_,?_⟩
     {
      intro i hi;rcases mI.1 hi with rfl | hi';{exact (cP (by omega) cs).2};{
       rcases mI.1 hi' with rfl | hi'';{exact cs.2};{rw [m1.1 hi''];exact u0.2}
      }
     }
     {intro x;rw [hqz_val x,eoTP hn huv hcp x]}
    }
    {
     refine ⟨{u0.val,v0.val,cs.val},by simp,?_,?_⟩
     {
      intro i hi;rcases mI.1 hi with rfl | hi';{exact u0.2};{
       rcases mI.1 hi' with rfl | hi'';{exact v0.2};{rw [m1.1 hi''];exact cs.2}
      }
     }
     {intro x;rw [hqz_val x,eoTN hn huv hcn x]}
    }
   }
   {exact (hWP c hc (hWo c hc hcc)).2}
  }
  {exact (hWP c hc (hWa c hc)).2}
 have hOE:∀ t<C.size,
   (∀ c∈I,iS n C (n+t) (n+qz c)→ t=qz c) →
   ∃ S:Finset ℕ,S.Nonempty∧(∀ i∈S,i<n) ∧
    ∀ x:Fin n→ Bool,wv C x (n+t)=eO S x:= by
  intro t;induction t using Nat.strong_induction_on with
  | _ t ih =>
   intro ht hNS;by_cases hIq:∃ c∈I,t=qz c;{obtain ⟨c,hc,rfl⟩:=hIq;exact hQE c hc};{
    push Not at hIq;have hNt:∀ c∈I,¬ iS n C (n+t) (n+qz c) :=
     fun c hc hsb=>hIq c hc (hNS c hc hsb)
    by_cases hAb:∃ c∈I,iS n C (n+qz c) (n+t);{
     obtain ⟨c,hc,sbct⟩:=hAb;obtain ⟨op,hgt,_,_,hl_t,hr_t⟩:=hbG C hb t ht;have hop_or:op=.or :=
      hNA c hc t ht sbct (hIq c hc) _ hgt
     subst hop_or;have hOt:∀ r<C.size,iS n C (n+t) (n+r)→ r≠t →
       ∀ g,C.gates[r]?=some g→ g.op=.or:= by
      intro r hr sbtr hrt gr hgr;have h1:=isL C hb sbct;have h2:=isL C hb sbtr;have h3:=hIq c hc;exact hNA c hc r hr (ReflTransGen.trans sbct sbtr) (by omega) gr hgr
     have hFt:=wvO C hf ho hb hd1 hp t ht hOt;have hSt:S1 n C (n+t)=∅:= by
      ext u
      simp only [S1,mF,mU,true_and,mN,iff_false];intro hTr;have:=hFt (oH u) hTr;rw [cf1 hn u] at this;cases this
     have hCE:∀ w,(w=gL C t∨w=gR C t) →
       ∃ S:Finset ℕ,S.Nonempty∧(∀ i∈S,i<n) ∧
        ∀ x:Fin n→ Bool,wv C x w=eO S x:= by
      intro w hw;have hw_ge_n:n≤w:= by
       by_contra hlt;let u:Fin n:=⟨w,by omega⟩
       have hu_in_t:u∈S1 n C (n+t):= by
        rw [s1O n C t (gL C t) (gR C t) ht hgt hl_t hr_t,mem_union];rcases hw with rfl | rfl;{left;rw [show gL C t=u.val from rfl,s1I];exact mem_singleton_self u};{right;rw [show gR C t=u.val from rfl,s1I];exact mem_singleton_self u}
       rw [hSt] at hu_in_t;exact mN u hu_in_t
      let tw:=w - n;have htw_lt:tw<t:= by rcases hw with rfl | rfl <;> omega
      have we:w=n+tw:= by {omega};rw [we];apply ih tw htw_lt (by omega);intro c' hc' sbtw;by_contra hne_tw;rcases ReflTransGen.cases_head sbtw with hEq | ⟨m,hs1,hr1⟩;{exact hne_tw (by omega)};{
       obtain ⟨q1,_,g1,hg1,rfl,htw1⟩:=hs1;have heq_t:=uR1 C (n+tw) q1 t (hd1 tw (by omega))
        g1 ⟨.or,[gL C t,gR C t]⟩ hg1 htw1 hgt
        (by rw [← we];rcases hw with rfl | rfl <;> simp)
       rw [heq_t] at hr1;exact hNt c' hc' hr1
      }
     obtain ⟨S1,h1n,h1l,h1v⟩:=hCE (gL C t) (Or.inl rfl);obtain ⟨S2,h2n,h2l,h2v⟩:=hCE (gR C t) (Or.inr rfl);refine ⟨S1∪S2,h1n.mono subset_union_left,?_,?_⟩;{
      intro i hi;rcases mem_union.1 hi with h1 | h2;{exact h1l i h1};{exact h2l i h2}
     }
     {intro x;rw [wvR C x t (gL C t) (gR C t) ht hgt hl_t hr_t,h1v x,h2v x,← eoU]}
    }
    {
     push Not at hAb;have hDT:∀ r∈T,¬ iS n C (n+r) (n+t):= by intro r hr;obtain ⟨c,hc,rfl⟩:=mG.1 hr;exact hAb c hc
     have hNC:∀ q<C.size,iS n C (n+t) (n+q) →
       iS n C (n+q) C.output→ q∉T:= by
      intro q _ h1 _ hqT;obtain ⟨c,hc,rfl⟩:=mG.1 hqT;exact hNt c hc h1
     have hle_out:∀ v:Fin n,lM n C v (n+t)≤lmC n C T v C.output:= by
      intro v;rw [← lmcD C hb T v (n+t) (by omega) hDT];exact lmcM C hb T v
       (isO C ho hb hd1 hp t ht) hNC
     have h2_le:=lm2 C hb t ht;have hsum_le:∑ v:Fin n,lM n C v (n+t) ≤
       ∑ v:Fin n,lmC n C T v C.output :=
      sum_le_sum (fun v _=>hle_out v)
     rcases hCs with ⟨hOz,_⟩ | ⟨_,_,_,_,_,_,_,_,hOz,_,_⟩ |
       ⟨u0,v0,huv,huvn,hOp,_⟩
     {
      exfalso;have hZr:∑ v:Fin n,lmC n C T v C.output=0:= by simp [T,I,hOz]
      omega
     }
     {
      exfalso;have hZr:∑ v:Fin n,lmC n C T v C.output=0:= by simp [T,I,hOz]
      omega
     }
     {
      have hOs:∑ v:Fin n,lmC n C T v C.output=2:= by
       have hrw:(∑ v:Fin n,lmC n C T v C.output) =
         ∑ v∈(univ:Finset (Fin n)).filter (fun v=>v=u0∨v=v0),1:= by
        rw [sum_filter];exact sC rfl (fun v _=>hOp v)
       have hfl:(univ:Finset (Fin n)).filter (fun v=>v=u0∨v=v0)={u0,v0}:= by {ext v;simp};rw [hrw,hfl,sum_const,cP0 huvn,smul_eq_mul,mul_one]
      have hEa:∀ v:Fin n,lM n C v (n+t)=lmC n C T v C.output:= by
       intro v;by_contra hne_v;have hSc:∑ z:Fin n,lM n C z (n+t) <
         ∑ z:Fin n,lmC n C T z C.output :=
        sum_lt_sum (fun z _=>hle_out z) ⟨v,mU v,lt_of_le_of_ne (hle_out v) hne_v⟩
       omega
      have lmt:∀ z:Fin n,lM n C z (n+t)=if z=u0∨z=v0 then 1 else 0 :=
       fun z=>(hEa z).trans (hOp z)
      obtain ⟨q0,hq0,op0,hteq,hop0,hg0⟩ :=
       lmP C hb (n+t) (by omega) u0 v0 huvn lmt
      have hq0_eq:q0=t:= by {omega};rw [hq0_eq] at hg0;have hOt:∀ r<C.size,iS n C (n+t) (n+r)→ r≠t →
        ∀ g,C.gates[r]?=some g→ g.op=.or:= by
       intro r hr sbtr hrt gr hgr;have h3_le:3≤∑ v:Fin n,lM n C v (n+r):= by
        rcases ReflTransGen.cases_tail sbtr with hEq | ⟨w',hPv,hls⟩;{exact (hrt (by omega)).elim};{
         obtain ⟨r',_,g',hg',heqr,hwin⟩:=hls;have hr'eq:r'=r:= by omega
         rw [hr'eq] at hg';obtain ⟨opr,hgr',_,_,hl_r,hr_r⟩:=hbG C hb r hr;rw [hgr'] at hg';obtain rfl:=oI hg';have hSr0:∑ v:Fin n,lM n C v (n+r) =
           (∑ v:Fin n,lM n C v (gL C r)) +
           (∑ v:Fin n,lM n C v (gR C r)):= by
          rw [← sum_add_distrib];exact sC rfl (fun v _=>lmG C hb v r hr)
         have hPl:∑ v:Fin n,lM n C v (n+t)≤∑ v:Fin n,lM n C v w' :=
          sum_le_sum (fun v _=>lmM C hb v hPv)
         simp only [List.mem_cons,List.not_mem_nil,or_false] at hwin;rcases hwin with rfl | rfl;{have:=lm1 C hb (gR C r) (by omega);omega};{have:=lm1 C hb (gL C r) (by omega);omega}
        }
       have hRq:∃ c∈I,iS n C (n+qz c) (n+r):= by
        by_contra hno_qz;push Not at hno_qz;have hRd:∀ s∈T,¬ iS n C (n+s) (n+r):= by intro s hs;obtain ⟨c,hc,rfl⟩:=mG.1 hs;exact hno_qz c hc
        have hRn:∀ q'<C.size,iS n C (n+r) (n+q') →
          iS n C (n+q') C.output→ q'∉T:= by
         intro q' _ h1 _ hq'T;obtain ⟨c,hc,rfl⟩:=mG.1 hq'T;exact hNt c hc (ReflTransGen.trans sbtr h1)
        have hr_le:∑ v:Fin n,lM n C v (n+r) ≤
          ∑ v:Fin n,lmC n C T v C.output:= by
         apply sum_le_sum;intro v _;rw [← lmcD C hb T v (n+r) (by omega) hRd];exact lmcM C hb T v
          (isO C ho hb hd1 hp r hr) hRn
        omega
       obtain ⟨c,hc,sbcr⟩:=hRq;have hrc:r≠qz c:=fun heq=>hNt c hc (heq▸sbtr);exact hNA c hc r hr sbcr hrc gr hgr
      have hop0_and:op0=.and:= by
       rcases hop0 with rfl | rfl;{rfl};{
        exfalso;have ht_le:=wvO C hf ho hb hd1 hp t ht hOt;have hu0_true:wv C (oH u0) (n+t)=true:= by
         rcases hg0 with h1 | h1;{rw [wvR C (oH u0) t u0.val v0.val ht h1 (by omega) (by omega),wvI,wvI];simp [oH]};{rw [wvR C (oH u0) t v0.val u0.val ht h1 (by omega) (by omega),wvI,wvI];simp [oH]}
        have:=ht_le (oH u0) hu0_true;rw [cf1 hn u0] at this;cases this
       }
      subst hop0_and;refine ⟨{u0.val},by simp,by simp [u0.2],?_⟩
      intro x;rcases hg0 with h1 | h1;{rw [wvA C x t u0.val v0.val ht h1 (by omega) (by omega),wvI,wvI,eoS huv x]};{rw [wvA C x t v0.val u0.val ht h1 (by omega) (by omega),wvI,wvI,Bool.and_comm,eoS huv x]}
     }
    }
   }
 intro t ht;by_cases hSc:∃ c∈I,iS n C (n+t) (n+qz c)∧t≠qz c;{
  obtain ⟨c,hc,sbtc,hne_tc⟩:=hSc;rcases ReflTransGen.cases_tail sbtc with hEq | ⟨w',hPv,hls⟩;{exact (hne_tc (by omega)).elim};{
   obtain ⟨q',_,g',hg',heqq,hwin⟩:=hls;have hq'eq:q'=qz c:= by omega
   rw [hq'eq] at hg';have hw'_in:w'=wc c∨w'=yc c:= by
    rcases (hQS c hc).2.1 with h1 | h1;{rw [h1] at hg';obtain rfl:=oI hg';simpa using hwin};{rw [h1] at hg';obtain rfl:=oI hg';simpa [or_comm] using hwin}
   rcases hw'_in with rfl | rfl;{
    rcases hCs with ⟨_,hWa⟩ | ⟨u0,v0,cs,huv,hsI,hCe,hu0D,hv0D,_,hWo,hWk⟩ | ⟨_,_,_,_,_,hWa⟩;{exfalso;have we:=(hWP c hc (hWa c hc)).1;have hle:=isL C hb hPv;have:=c.2;omega};{
     by_cases hcc:c=cs;{
      rw [hcc] at hPv;obtain ⟨qw,qb,hqw,hqb,we,hgw,hgb,hbv,hwv⟩ :=
       hTB u0 v0 cs huv hsI hu0D hv0D hWk
      rw [we] at hPv;rcases ReflTransGen.cases_tail hPv with hEq | ⟨z',hzprev,hzlast⟩;{
       have ht_eq:t=qw:= by {omega};rw [ht_eq];right;right;refine ⟨u0,v0,cs,huv,?_,hwv⟩;rcases hCe with hcp | hcn;{right;rw [hcp];exact congrArg Fin.val (cnP (by omega) u0)};{left;rw [hcn];rfl}
      }
      {
       obtain ⟨qw',_,gw',hgw',heqqw,hzin⟩:=hzlast;have hqweq:qw'=qw:= by omega
       rw [hqweq] at hgw';have hz_eq:z'=n+qb:= by
        have hle:=isL C hb hzprev;have hc_lt:=cs.2;rcases hgw with h1 | h1;{rw [h1] at hgw';obtain rfl:=oI hgw';simp only [List.mem_cons,List.not_mem_nil,or_false] at hzin;rcases hzin with rfl | rfl <;> omega};{rw [h1] at hgw';obtain rfl:=oI hgw';simp only [List.mem_cons,List.not_mem_nil,or_false] at hzin;rcases hzin with rfl | rfl <;> omega}
       rw [hz_eq] at hzprev;rcases ReflTransGen.cases_tail hzprev with hEq | ⟨u',huprev,hulast⟩;{
        have ht_eq:t=qb:= by {omega};rw [ht_eq];left;exact ⟨{u0.val},by simp,by simp [u0.2],fun x=> by rw [hbv x,eoS huv x]⟩
       }
       {
        exfalso;obtain ⟨qb',_,gb',hgb',heqqb,huin⟩:=hulast;have hqbeq:qb'=qb:= by omega
        rw [hqbeq] at hgb';have hle:=isL C hb huprev;have hu0lt:=u0.2;have hv0lt:=v0.2;rcases hgb with h1 | h1;{rw [h1] at hgb';obtain rfl:=oI hgb';simp only [List.mem_cons,List.not_mem_nil,or_false] at huin;rcases huin with rfl | rfl <;> omega};{rw [h1] at hgb';obtain rfl:=oI hgb';simp only [List.mem_cons,List.not_mem_nil,or_false] at huin;rcases huin with rfl | rfl <;> omega}
       }
      }
     }
     {exfalso;have we:=(hWP c hc (hWo c hc hcc)).1;have hle:=isL C hb hPv;have:=c.2;omega}
    }
    {exfalso;have we:=(hWP c hc (hWa c hc)).1;have hle:=isL C hb hPv;have:=c.2;omega}
   }
   {
    obtain ⟨qy,hqy,hy_eq,hgy,hy_val⟩:=hYS c hc;rw [hy_eq] at hPv;rcases ReflTransGen.cases_tail hPv with hEq | ⟨u',huprev,hulast⟩;{
     have ht_eq:t=qy:= by {omega};rw [ht_eq];right;left;refine ⟨cP (by omega) c,c,cN (by omega) c,
      congrArg Fin.val (cnP (by omega) c),rfl,fun x=> by rw [← hy_eq];exact hy_val x⟩
    }
    {
     exfalso;obtain ⟨qy',_,gy',hgy',heqqy,huin⟩:=hulast;have hqyeq:qy'=qy:= by omega
     rw [hqyeq] at hgy';have hle:=isL C hb huprev;have hplt:=(cP (by omega) c).2;have hnlt:=(cN (by omega) c).2;rcases hgy with h1 | h1;{rw [h1] at hgy';obtain rfl:=oI hgy';simp only [List.mem_cons,List.not_mem_nil,or_false] at huin;rcases huin with rfl | rfl <;> omega};{rw [h1] at hgy';obtain rfl:=oI hgy';simp only [List.mem_cons,List.not_mem_nil,or_false] at huin;rcases huin with rfl | rfl <;> omega}
    }
   }
  }
 }
 {push Not at hSc;exact Or.inl (hOE t ht hSc)}
lemma lpT {n:ℕ} (C:Circuit) (hn:5≤n)
  (hf:circuitFun n C=cF n) (ho:C.output=n+C.size - 1) (hb:IsBin n C)
  (hMI:∀ v:Fin n,v∈IS n C↔wD C v.val=1)
  (hM2:∀ v:Fin n,v∈D2 n C↔wD C v.val=2)
  (hIN:∀ c∈IS n C,∀ u:Fin n,cA c u→ u∈D2 n C)
  (hEC:((univ:Finset (Fin n)).filter
   fun u=>u∈D2 n C∧cN (by omega) u∈D2 n C).card=n %2)
  (qz wc yc:Fin n→ ℕ)
  (hQS:QS n C qz wc yc)
  (hwl:∀ c∈IS n C,wc c<n+qz c)
  (hyl:∀ c∈IS n C,yc c<n+qz c)
  (hB:∀ v:Fin n,
   lmC n C ((IS n C).image qz) v C.output +
    ∑ c∈IS n C,(lM n C v (wc c)+lM n C v (yc c))=wD C v.val) :
  (∀ c∈IS n C,∀ v:Fin n,lM n C v (yc c)=if cA c v then 1 else 0) ∧
  (((∀ v:Fin n,lmC n C ((IS n C).image qz) v C.output=0) ∧
    (∀ c∈IS n C,∀ v:Fin n,lM n C v (wc c)=if v=c then 1 else 0)) ∨
   (∃ u0 v0 cs:Fin n,(u0.val+1)%n=v0.val∧cs∈IS n C ∧
    (cs=cP (by omega) u0∨cs=cN (by omega) v0) ∧
    u0∈D2 n C∧v0∈D2 n C ∧
    (∀ v:Fin n,lmC n C ((IS n C).image qz) v C.output=0) ∧
    (∀ c∈IS n C,c≠cs→ ∀ v:Fin n,lM n C v (wc c)=if v=c then 1 else 0) ∧
    (∀ v:Fin n,lM n C v (wc cs)=if v=cs∨v=u0∨v=v0 then 1 else 0)) ∨
   (∃ u0 v0:Fin n,(u0.val+1)%n=v0.val∧u0≠v0 ∧
    (∀ v:Fin n,lmC n C ((IS n C).image qz) v C.output=if v=u0∨v=v0 then 1 else 0) ∧
    (∀ c∈IS n C,∀ v:Fin n,lM n C v (wc c)=if v=c then 1 else 0))):= by
 let I:Finset (Fin n):=IS n C;let T:Finset ℕ:=I.image qz;change ∀ v:Fin n,lmC n C T v C.output +
  ∑ c∈I,(lM n C v (wc c)+lM n C v (yc c))=wD C v.val at hB
 have hWS:∀ c∈I,1≤lM n C c (wc c):= by
  intro c hc;have hlt:wc c<n+C.size:= by have:=hwl c hc;have:=(hQS c hc).1;omega
  exact le_trans (sl1 C hb c (wc c) hlt (by rw [(hQS c hc).2.2.1];exact mem_singleton_self c))
   (slM C hb c (wc c) hlt)
 have hYA:∀ c∈I,∀ u:Fin n,cA c u→ 1≤lM n C u (yc c):= by
  intro c hc u hAd;have hlt:yc c<n+C.size:= by have:=hyl c hc;have:=(hQS c hc).1;omega
  exact le_trans (sl1 C hb u (yc c) hlt ((hQS c hc).2.2.2.1 u hAd))
   (slM C hb u (yc c) hlt)
 have hBI:∀ v∈I,
   lmC n C T v C.output=0∧lM n C v (wc v)=1∧lM n C v (yc v)=0 ∧
   ∀ c∈I,c≠v→ lM n C v (wc c)=0∧lM n C v (yc c)=0:= by
  intro v hv;have hb:=hB v;rw [(hMI v).1 hv] at hb;have hSf:=hWS v hv;have h1:=aSe I (fun c=>lM n C v (wc c)+lM n C v (yc c)) hv;have hRe:∑ c∈I.erase v,(lM n C v (wc c)+lM n C v (yc c))=0:= by omega
  refine ⟨by omega,by omega,by omega,?_⟩
  intro c hc hcv;have hle:=s1s (f:=fun c'=>lM n C v (wc c')+lM n C v (yc c'))
   (fun _ _=>zL _) (mE.2 ⟨hcv,hc⟩)
  omega
 have hBD:∀ v∈D2 n C,cN (by omega) v∈I→ cP (by omega) v∈I →
   lmC n C T v C.output=0∧(∀ c∈I,lM n C v (wc c)=0) ∧
   (∀ c∈I,lM n C v (yc c)=if cA c v then 1 else 0):= by
  intro v hv hnext hPv;have hb:=hB v;rw [(hM2 v).1 hv] at hb;let c1:=cN (by omega) v;let c2:=cP (by omega) v;have hc12:c1≠c2:=cnNP hn v;have h1:=hYA c1 hnext v (Or.symm (cnA (by omega) v));have h2:=hYA c2 hPv v (Or.symm (cpA (by omega) v));have hPs:({c1,c2}:Finset (Fin n))⊆I:= by
   intro x hx;rcases mI.1 hx with rfl | hx';{exact hnext};{rw [m1.1 hx'];exact hPv}
  have hSs:=sum_sdiff hPs (f:=fun c=>lM n C v (wc c)+lM n C v (yc c));rw [sum_pair hc12] at hSs;have hRe:∑ c∈I \ {c1,c2},(lM n C v (wc c)+lM n C v (yc c))=0:= by {omega};refine ⟨by omega,?_,?_⟩
  {
   intro c hc;by_cases hc1:c=c1;{subst hc1;omega};{
    by_cases hc2:c=c2;{subst hc2;omega};{
     have hnot12:c∉({c1,c2}:Finset (Fin n)):= by {rw [mI,m1];push Not;exact ⟨hc1,hc2⟩};have hle:=s1s (f:=fun c'=>lM n C v (wc c')+lM n C v (yc c'))
      (fun _ _=>zL _) (mS.2 ⟨hc,hnot12⟩)
     omega
    }
   }
  }
  {
   intro c hc;by_cases hc1:c=c1;{rw [hc1];have hAd:cA c1 v:=Or.symm (cnA (by omega) v);simp only [hAd,↓reduceIte];omega};{
    by_cases hc2:c=c2;{rw [hc2];have hAd:cA c2 v:=Or.symm (cpA (by omega) v);simp only [hAd,↓reduceIte];omega};{
     have hnadj:¬ cA c v:= by
      intro h;rcases (caI hn v c).1 (Or.symm h) with rfl | rfl;{exact hc1 rfl};{exact hc2 rfl}
     simp only [hnadj,↓reduceIte];have hnot12:c∉({c1,c2}:Finset (Fin n)):= by rw [mI,m1];push Not;exact ⟨hc1,hc2⟩
     have hle:=s1s (f:=fun c'=>lM n C v (wc c')+lM n C v (yc c'))
      (fun _ _=>zL _) (mS.2 ⟨hc,hnot12⟩)
     omega
    }
   }
  }
 let E:=(univ:Finset (Fin n)).filter fun u=>u∈D2 n C∧cN (by omega) u∈D2 n C;have hEm:E.card=n %2:=hEC;by_cases hEe:E=∅;{
  have hDA:∀ v∈D2 n C,cN (by omega) v∈I∧cP (by omega) v∈I:= by
   intro v hv;constructor;{
    by_contra hno;have hn2:cN (by omega) v∈D2 n C:= by by_contra hno2;exact hno (mS.2 ⟨mU _,hno2⟩)
    have hMm:v∈E:=mF.2 ⟨mU v,hv,hn2⟩;rw [hEe] at hMm;exact mN v hMm
   }
   {
    by_contra hno;have hp2:cP (by omega) v∈D2 n C:= by by_contra hno2;exact hno (mS.2 ⟨mU _,hno2⟩)
    have hMm:cP (by omega) v∈E :=
     mF.2 ⟨mU _,hp2,by rw [cnP];exact hv⟩
    rw [hEe] at hMm;exact mN _ hMm
   }
  refine ⟨?_,Or.inl ⟨?_,?_⟩⟩;{
   intro c hc v;by_cases hvI:v∈I;{
    have hnadj:¬ cA c v:=fun h=>(mS.1 hvI).2 (hIN c hc v h);simp only [hnadj,↓reduceIte];by_cases hcv:c=v;{subst hcv;exact (hBI c hc).2.2.1};{exact ((hBI v hvI).2.2.2 c hc hcv).2}
   }
   {have hv2:v∈D2 n C:= by {by_contra hno;exact hvI (mS.2 ⟨mU v,hno⟩)};exact (hBD v hv2 (hDA v hv2).1 (hDA v hv2).2).2.2 c hc}
  }
  {
   intro v;by_cases hvI:v∈I;{exact (hBI v hvI).1};{
    have hv2:v∈D2 n C:= by {by_contra hno;exact hvI (mS.2 ⟨mU v,hno⟩)};exact (hBD v hv2 (hDA v hv2).1 (hDA v hv2).2).1
   }
  }
  {
   intro c hc v;by_cases hvI:v∈I;{
    by_cases hvc:v=c;{subst hvc;simp only [↓reduceIte];exact (hBI v hvI).2.1};{simp only [hvc,↓reduceIte];exact ((hBI v hvI).2.2.2 c hc (Ne.symm hvc)).1}
   }
   {have hv2:v∈D2 n C:= by {by_contra hno;exact hvI (mS.2 ⟨mU v,hno⟩)};have hvc:v≠c:=fun h=>hvI (h▸hc);simp only [hvc,↓reduceIte];exact (hBD v hv2 (hDA v hv2).1 (hDA v hv2).2).2.1 c hc}
  }
 }
 {
  obtain ⟨u0,hu0E⟩:=nonempty_iff_ne_empty.2 hEe;have hEc:E.card=1:= by have hpos_E:1≤E.card:=one_le_card.2 ⟨u0,hu0E⟩;omega
  have hEq0:E={u0}:=(card_eq_one.1 hEc).elim fun x hx=> by have:u0=x:=m1.1 (hx▸hu0E);rwa [← this] at hx
  let v0:=cN (by omega) u0;have huv:(u0.val+1)%n=v0.val:=rfl;have huD:u0∈D2 n C:=(mF.1 hu0E).2.1;have hvD:v0∈D2 n C:=(mF.1 hu0E).2.2;have huvn:u0≠v0:=fun h=>caR hn u0 (Or.inl (h▸huv));let cu:=cP (by omega) u0;let cv:=cN (by omega) v0;have hcI:cu∈I:= by
   by_contra hno;have h2:cu∈D2 n C:= by by_contra hno2;exact hno (mS.2 ⟨mU _,hno2⟩)
   have hMm:cu∈E:=mF.2 ⟨mU _,h2,by rw [cnP];exact huD⟩
   rw [hEq0,m1] at hMm;have h1:=cpA (by omega) u0;rw [show cP (by omega) u0=u0 from hMm] at h1;exact caR hn u0 h1
  have hvI:cv∈I:= by
   by_contra hno;have h2:cv∈D2 n C:= by by_contra hno2;exact hno (mS.2 ⟨mU _,hno2⟩)
   have hMm:v0∈E:=mF.2 ⟨mU _,hvD,h2⟩;rw [hEq0,m1] at hMm;exact huvn hMm.symm
  have hDO:∀ v∈D2 n C,v≠u0→ v≠v0 →
    cN (by omega) v∈I∧cP (by omega) v∈I:= by
   intro v hv hvu hvv;constructor;{
    by_contra hno;have hn2:cN (by omega) v∈D2 n C:= by by_contra hno2;exact hno (mS.2 ⟨mU _,hno2⟩)
    have hMm:v∈E:=mF.2 ⟨mU v,hv,hn2⟩;rw [hEq0,m1] at hMm;exact hvu hMm
   }
   {
    by_contra hno;have hp2:cP (by omega) v∈D2 n C:= by by_contra hno2;exact hno (mS.2 ⟨mU _,hno2⟩)
    have hMm:cP (by omega) v∈E :=
     mF.2 ⟨mU _,hp2,by rw [cnP];exact hv⟩
    rw [hEq0,m1] at hMm;have:v=v0:= by have:=congrArg (cN (by omega)) hMm;rwa [cnP] at this
    exact hvv this
   }
  have mkY :
    lM n C u0 (yc cu)=1→ (∀ c∈I,c≠cu→ lM n C u0 (yc c)=0) →
    lM n C v0 (yc cv)=1→ (∀ c∈I,c≠cv→ lM n C v0 (yc c)=0) →
    ∀ c∈I,∀ v:Fin n,lM n C v (yc c)=if cA c v then 1 else 0:= by
   intro hu1 hu0 hv1 hv0 c hc v;by_cases hvI:v∈I;{
    have hnadj:¬ cA c v:=fun h=>(mS.1 hvI).2 (hIN c hc v h);simp only [hnadj,↓reduceIte];by_cases hcv':c=v;{subst hcv';exact (hBI c hc).2.2.1};{exact ((hBI v hvI).2.2.2 c hc hcv').2}
   }
   {
    have hv2:v∈D2 n C:= by {by_contra hno;exact hvI (mS.2 ⟨mU v,hno⟩)};by_cases hvu:v=u0;{
     rw [hvu];have hAi:cA c u0↔c=cu:= by
      constructor;{
       intro h;rcases (caI hn u0 c).1 (Or.symm h) with rfl | rfl;{exact ((mS.1 hc).2 hvD).elim};{rfl}
      }
      {rintro rfl;exact Or.symm (cpA (by omega) u0)}
     by_cases hcu':c=cu;{rw [hcu'];have h1:cA cu u0:=Or.symm (cpA (by omega) u0);simp only [h1,↓reduceIte];exact hu1};{simp only [show ¬ cA c u0 from fun h=>hcu' (hAi.1 h),↓reduceIte];exact hu0 c hc hcu'}
    }
    {
     by_cases hvv:v=v0;{
      rw [hvv];have hAi:cA c v0↔c=cv:= by
       constructor;{
        intro h;rcases (caI hn v0 c).1 (Or.symm h) with rfl | rfl;{rfl};{have:cP (by omega) v0=u0:=cpN (by omega) u0;rw [this] at hc;exact ((mS.1 hc).2 huD).elim}
       }
       {rintro rfl;exact Or.symm (cnA (by omega) v0)}
      by_cases hcv':c=cv;{rw [hcv'];have h1:cA cv v0:=Or.symm (cnA (by omega) v0);simp only [h1,↓reduceIte];exact hv1};{simp only [show ¬ cA c v0 from fun h=>hcv' (hAi.1 h),↓reduceIte];exact hv0 c hc hcv'}
     }
     {
      exact (hBD v hv2 (hDO v hv2 hvu hvv).1
       (hDO v hv2 hvu hvv).2).2.2 c hc
     }
    }
   }
  have hUc:1≤lM n C u0 (yc cu) :=
   hYA cu hcI u0 (Or.symm (cpA (by omega) u0))
  have hVc:1≤lM n C v0 (yc cv) :=
   hYA cv hvI v0 (Or.symm (cnA (by omega) v0))
  have hbu0:lmC n C T u0 C.output +
    ∑ c∈I,(lM n C u0 (wc c)+lM n C u0 (yc c))=2:= by
   have:=hB u0;rwa [(hM2 u0).1 huD] at this
  have hbv0:lmC n C T v0 C.output +
    ∑ c∈I,(lM n C v0 (wc c)+lM n C v0 (yc c))=2:= by
   have:=hB v0;rwa [(hM2 v0).1 hvD] at this
  by_cases hTy:∃ cs∈I,wv C (pI u0 v0) (n+qz cs)=true;{
   obtain ⟨cs,hsI,hCt⟩:=hTy;have hCw:wv C (pI u0 v0) (wc cs)=true:= by
    obtain ⟨hqz,hGt,_,_,_⟩:=hQS cs hsI;rcases hGt with h1 | h1;{
     rw [wvA C (pI u0 v0) (qz cs) (wc cs) (yc cs) hqz h1 (hwl cs hsI) (hyl cs hsI),
      bAt] at hCt;exact hCt.1
    }
    {
     rw [wvA C (pI u0 v0) (qz cs) (yc cs) (wc cs) hqz h1 (hyl cs hsI) (hwl cs hsI),
      bAt] at hCt;exact hCt.2
    }
   have hCy:wv C (pI u0 v0) (yc cs)=true:= by
    obtain ⟨hqz,hGt,_,_,_⟩:=hQS cs hsI;rcases hGt with h1 | h1;{
     rw [wvA C (pI u0 v0) (qz cs) (wc cs) (yc cs) hqz h1 (hwl cs hsI) (hyl cs hsI),
      bAt] at hCt;exact hCt.2
    }
    {
     rw [wvA C (pI u0 v0) (qz cs) (yc cs) (wc cs) hqz h1 (hyl cs hsI) (hwl cs hsI),
      bAt] at hCt;exact hCt.1
    }
   have hWu:1≤lM n C u0 (wc cs):= by
    by_contra h0;have hZr:lM n C u0 (wc cs)=0:= by omega
    have heq:=wvZ C hb (pI u0 v0) (oH v0) (wc cs)
     (by have:=hwl cs hsI;have:=(hQS cs hsI).1;omega)
     (fun i hi=> by
      have hiu:i≠u0:=fun h=> by rw [h,hZr] at hi;omega
      simp [pI,oH,hiu])
    rw [heq] at hCw;have hv0_in:v0∈S1 n C (wc cs):=mF.2 ⟨mU v0,hCw⟩;rw [(hQS cs hsI).2.2.1,m1] at hv0_in;exact (mS.1 hsI).2 (hv0_in▸hvD)
   have hWv:1≤lM n C v0 (wc cs):= by
    by_contra h0;have hZr:lM n C v0 (wc cs)=0:= by omega
    have heq:=wvZ C hb (pI u0 v0) (oH u0) (wc cs)
     (by have:=hwl cs hsI;have:=(hQS cs hsI).1;omega)
     (fun i hi=> by
      have hiv:i≠v0:=fun h=> by rw [h,hZr] at hi;omega
      simp [pI,oH,hiv])
    rw [heq] at hCw;have hu0_in:u0∈S1 n C (wc cs):=mF.2 ⟨mU u0,hCw⟩;rw [(hQS cs hsI).2.2.1,m1] at hu0_in;exact (mS.1 hsI).2 (hu0_in▸huD)
   have hUe:lmC n C T u0 C.output=0 ∧
     lM n C u0 (wc cs)=1∧lM n C u0 (yc cu)=1 ∧
     (∀ c∈I,c≠cs→ lM n C u0 (wc c)=0) ∧
     (∀ c∈I,c≠cu→ lM n C u0 (yc c)=0):= by
    have hSu0:=(sum_add_distrib (s:=I) (f:=fun c=>lM n C u0 (wc c))
     (g:=fun c=>lM n C u0 (yc c))).symm
    have h1:=aSe I (fun c=>lM n C u0 (wc c)) hsI;have h2:=aSe I (fun c=>lM n C u0 (yc c)) hcI;refine ⟨by omega,by omega,by omega,?_,?_⟩
    {
     intro c hc hne;have:=s1s (f:=fun c'=>lM n C u0 (wc c'))
      (fun _ _=>zL _) (mE.2 ⟨hne,hc⟩);omega
    }
    {
     intro c hc hne;have:=s1s (f:=fun c'=>lM n C u0 (yc c'))
      (fun _ _=>zL _) (mE.2 ⟨hne,hc⟩);omega
    }
   have hVe:lmC n C T v0 C.output=0 ∧
     lM n C v0 (wc cs)=1∧lM n C v0 (yc cv)=1 ∧
     (∀ c∈I,c≠cs→ lM n C v0 (wc c)=0) ∧
     (∀ c∈I,c≠cv→ lM n C v0 (yc c)=0):= by
    have hSv0:=(sum_add_distrib (s:=I) (f:=fun c=>lM n C v0 (wc c))
     (g:=fun c=>lM n C v0 (yc c))).symm
    have h1:=aSe I (fun c=>lM n C v0 (wc c)) hsI;have h2:=aSe I (fun c=>lM n C v0 (yc c)) hvI;refine ⟨by omega,by omega,by omega,?_,?_⟩
    {
     intro c hc hne;have:=s1s (f:=fun c'=>lM n C v0 (wc c'))
      (fun _ _=>zL _) (mE.2 ⟨hne,hc⟩);omega
    }
    {
     intro c hc hne;have:=s1s (f:=fun c'=>lM n C v0 (yc c'))
      (fun _ _=>zL _) (mE.2 ⟨hne,hc⟩);omega
    }
   have hCe:cs=cu∨cs=cv:= by
    by_contra hno;push Not at hno;have h0u:=hUe.2.2.2.2 cs hsI hno.1;have h0v:=hVe.2.2.2.2 cs hsI hno.2;have heq:=wvZ C hb (pI u0 v0) (fun _=>false) (yc cs)
     (by have:=hyl cs hsI;have:=(hQS cs hsI).1;omega)
     (fun i hi=> by
      have hiu:i≠u0:=fun h=> by rw [h,h0u] at hi;omega
      have hiv:i≠v0:=fun h=> by rw [h,h0v] at hi;omega
      simp [pI,hiu,hiv])
    rw [heq] at hCy;have hMn:=wvM C hb (fun _=>false) (oH cs) (fun _ h=> by cases h)
     (yc cs) (by have:=hyl cs hsI;have:=(hQS cs hsI).1;omega) hCy
    exact (hQS cs hsI).2.2.2.2 (mF.2 ⟨mU cs,hMn⟩)
   refine ⟨mkY hUe.2.2.1 hUe.2.2.2.2 hVe.2.2.1 hVe.2.2.2.2,
    Or.inr (Or.inl ⟨u0,v0,cs,huv,hsI,hCe,huD,hvD,?_,?_,?_⟩)⟩
   {
    intro v;by_cases hvI:v∈I;{exact (hBI v hvI).1};{
     have hv2:v∈D2 n C:= by {by_contra hno;exact hvI (mS.2 ⟨mU v,hno⟩)};by_cases hvu:v=u0;{subst hvu;exact hUe.1};{
      by_cases hvv:v=v0;{subst hvv;exact hVe.1};{
       exact (hBD v hv2 (hDO v hv2 hvu hvv).1
        (hDO v hv2 hvu hvv).2).1
      }
     }
    }
   }
   {
    intro c hc hcc v;by_cases hvI:v∈I;{
     by_cases hvc:v=c;{subst hvc;simp only [↓reduceIte];exact (hBI v hvI).2.1};{simp only [hvc,↓reduceIte];exact ((hBI v hvI).2.2.2 c hc (Ne.symm hvc)).1}
    }
    {
     have hv2:v∈D2 n C:= by {by_contra hno;exact hvI (mS.2 ⟨mU v,hno⟩)};have hvc:v≠c:=fun h=>hvI (h▸hc);simp only [hvc,↓reduceIte];by_cases hvu:v=u0;{subst hvu;exact hUe.2.2.2.1 c hc hcc};{
      by_cases hvv:v=v0;{subst hvv;exact hVe.2.2.2.1 c hc hcc};{
       exact (hBD v hv2 (hDO v hv2 hvu hvv).1
        (hDO v hv2 hvu hvv).2).2.1 c hc
      }
     }
    }
   }
   {
    intro v;by_cases hvI:v∈I;{
     have hvu:v≠u0:=fun h=>(mS.1 hvI).2 (h▸huD);have hvv:v≠v0:=fun h=>(mS.1 hvI).2 (h▸hvD);by_cases hvc:v=cs;{subst hvc;simp only [true_or,↓reduceIte];exact (hBI v hvI).2.1};{simp only [hvc,hvu,hvv,or_self,↓reduceIte];exact ((hBI v hvI).2.2.2 cs hsI (Ne.symm hvc)).1}
    }
    {
     have hv2:v∈D2 n C:= by {by_contra hno;exact hvI (mS.2 ⟨mU v,hno⟩)};have hvc:v≠cs:=fun h=>hvI (h▸hsI);by_cases hvu:v=u0;{subst hvu;simp only [true_or,or_true,↓reduceIte];exact hUe.2.1};{
      by_cases hvv:v=v0;{subst hvv;simp only [or_true,↓reduceIte];exact hVe.2.1};{
       simp only [hvc,hvu,hvv,or_self,↓reduceIte];exact (hBD v hv2 (hDO v hv2 hvu hvv).1
        (hDO v hv2 hvu hvv).2).2.1 cs hsI
      }
     }
    }
   }
  }
  {
   push Not at hTy;have hFP:∀ c∈I,wv C (pI u0 v0) (n+qz c)=false :=
    fun c hc=>Bool.eq_false_iff.2 (hTy c hc)
   have hFU:∀ c∈I,wv C (oH u0) (n+qz c)=false:= by
    intro c hc;rw [Bool.eq_false_iff];intro hTr;have h1:=wvM C hb (oH u0) (pI u0 v0)
     (fun i hi=> by simp [oH] at hi;simp [pI,hi])
     (n+qz c) (by have:=(hQS c hc).1;omega) hTr
    rw [hFP c hc] at h1;cases h1
   have hFV:∀ c∈I,wv C (oH v0) (n+qz c)=false:= by
    intro c hc;rw [Bool.eq_false_iff];intro hTr;have h1:=wvM C hb (oH v0) (pI u0 v0)
     (fun i hi=> by simp [oH] at hi;simp [pI,hi])
     (n+qz c) (by have:=(hQS c hc).1;omega) hTr
    rw [hFP c hc] at h1;cases h1
   have hUp:1≤lmC n C T u0 C.output:= by
    by_contra h0;have hZr:lmC n C T u0 C.output=0:= by omega
    have heq:=wvcZ C hb T (pI u0 v0) (oH v0)
     (fun t ht=> by obtain ⟨c,hc,rfl⟩:=mG.1 ht;rw [hFP c hc,hFV c hc])
     C.output (by omega)
     (fun i hi=> by
      have hiu:i≠u0:=fun h=> by rw [h,hZr] at hi;omega
      simp [pI,oH,hiu])
    have hf1:=congrFun hf (pI u0 v0);have hf2:=congrFun hf (oH v0);change wv C (pI u0 v0) C.output=cF n (pI u0 v0) at hf1;change wv C (oH v0) C.output=cF n (oH v0) at hf2;have hTr:cF n (pI u0 v0)=true:=(cf2 hn u0 v0).2 (Or.inl huv);rw [← hf1,heq,hf2,cf1 hn v0] at hTr;cases hTr
   have hVp:1≤lmC n C T v0 C.output:= by
    by_contra h0;have hZr:lmC n C T v0 C.output=0:= by omega
    have heq:=wvcZ C hb T (pI u0 v0) (oH u0)
     (fun t ht=> by obtain ⟨c,hc,rfl⟩:=mG.1 ht;rw [hFP c hc,hFU c hc])
     C.output (by omega)
     (fun i hi=> by
      have hiv:i≠v0:=fun h=> by rw [h,hZr] at hi;omega
      simp [pI,oH,hiv])
    have hf1:=congrFun hf (pI u0 v0);have hf2:=congrFun hf (oH u0);change wv C (pI u0 v0) C.output=cF n (pI u0 v0) at hf1;change wv C (oH u0) C.output=cF n (oH u0) at hf2;have hTr:cF n (pI u0 v0)=true:=(cf2 hn u0 v0).2 (Or.inl huv);rw [← hf1,heq,hf2,cf1 hn u0] at hTr;cases hTr
   have hU0:lmC n C T u0 C.output=1∧lM n C u0 (yc cu)=1 ∧
     (∀ c∈I,lM n C u0 (wc c)=0)∧(∀ c∈I,c≠cu→ lM n C u0 (yc c)=0):= by
    have hSu0:=(sum_add_distrib (s:=I) (f:=fun c=>lM n C u0 (wc c))
     (g:=fun c=>lM n C u0 (yc c))).symm
    have h2:=aSe I (fun c=>lM n C u0 (yc c)) hcI;refine ⟨by omega,by omega,?_,?_⟩
    {intro c hc;have:=s1s (f:=fun c'=>lM n C u0 (wc c')) (fun _ _=>zL _) hc;omega};{
     intro c hc hne;have:=s1s (f:=fun c'=>lM n C u0 (yc c'))
      (fun _ _=>zL _) (mE.2 ⟨hne,hc⟩);omega
    }
   have hV0:lmC n C T v0 C.output=1∧lM n C v0 (yc cv)=1 ∧
     (∀ c∈I,lM n C v0 (wc c)=0)∧(∀ c∈I,c≠cv→ lM n C v0 (yc c)=0):= by
    have hSv0:=(sum_add_distrib (s:=I) (f:=fun c=>lM n C v0 (wc c))
     (g:=fun c=>lM n C v0 (yc c))).symm
    have h2:=aSe I (fun c=>lM n C v0 (yc c)) hvI;refine ⟨by omega,by omega,?_,?_⟩
    {intro c hc;have:=s1s (f:=fun c'=>lM n C v0 (wc c')) (fun _ _=>zL _) hc;omega};{
     intro c hc hne;have:=s1s (f:=fun c'=>lM n C v0 (yc c'))
      (fun _ _=>zL _) (mE.2 ⟨hne,hc⟩);omega
    }
   refine ⟨mkY hU0.2.1 hU0.2.2.2 hV0.2.1 hV0.2.2.2,
    Or.inr (Or.inr ⟨u0,v0,huv,huvn,?_,?_⟩)⟩
   {
    intro v;by_cases hvI:v∈I;{have hvu:v≠u0:=fun h=>(mS.1 hvI).2 (h▸huD);have hvv:v≠v0:=fun h=>(mS.1 hvI).2 (h▸hvD);simp only [hvu,hvv,or_self,↓reduceIte];exact (hBI v hvI).1};{
     have hv2:v∈D2 n C:= by {by_contra hno;exact hvI (mS.2 ⟨mU v,hno⟩)};by_cases hvu:v=u0;{subst hvu;simp only [true_or,↓reduceIte];exact hU0.1};{
      by_cases hvv:v=v0;{subst hvv;simp only [or_true,↓reduceIte];exact hV0.1};{
       simp only [hvu,hvv,or_self,↓reduceIte];exact (hBD v hv2 (hDO v hv2 hvu hvv).1
        (hDO v hv2 hvu hvv).2).1
      }
     }
    }
   }
   {
    intro c hc v;by_cases hvI:v∈I;{
     by_cases hvc:v=c;{subst hvc;simp only [↓reduceIte];exact (hBI v hvI).2.1};{simp only [hvc,↓reduceIte];exact ((hBI v hvI).2.2.2 c hc (Ne.symm hvc)).1}
    }
    {
     have hv2:v∈D2 n C:= by {by_contra hno;exact hvI (mS.2 ⟨mU v,hno⟩)};have hvc:v≠c:=fun h=>hvI (h▸hc);simp only [hvc,↓reduceIte];by_cases hvu:v=u0;{subst hvu;exact hU0.2.2.1 c hc};{
      by_cases hvv:v=v0;{subst hvv;exact hV0.2.2.1 c hc};{
       exact (hBD v hv2 (hDO v hv2 hvu hvv).1
        (hDO v hv2 hvu hvv).2).2.1 c hc
      }
     }
    }
   }
  }
 }
theorem classify_of_struct (n : ℕ) (C : Circuit) (hn : 5 ≤ n)
    (hfun : circuitFun n C =
      (fun x : Fin n → Bool =>
        decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)))
    (hout : C.output = n + C.size - 1)
    (hbin : ∀ q < C.size, ∃ g op a b, C.gates[q]? = some g ∧ g.op = op ∧
      (op = GateOp.and ∨ op = GateOp.or) ∧ g.inputs = [a, b] ∧ a ≠ b ∧ a < n + q ∧ b < n + q)
    (hD_bounds : ∀ v : Fin n,
      1 ≤ (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length ∧
      (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length ≤ 2)
    (hsplit : ∃ (D₁' : Finset (Fin n)) (gSplit : Fin n → ℕ),
      (∀ v ∈ D₁',
        (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length = 1 ∧
        n ≤ gSplit v ∧ gSplit v < C.output ∧
        (C.gates.filter fun g => decide (gSplit v ∈ g.inputs)).length = 2 ∧
        (Finset.univ.filter fun u : Fin n =>
          (C.wires (List.ofFn fun i : Fin n => decide (i = u))).getD (gSplit v) false = true) = {v} ∧
        ∀ q < C.size, ∀ g, C.gates[q]? = some g → gSplit v ∈ g.inputs → g.op = GateOp.and) ∧
      (∀ q, q + 1 < C.size → (∀ v ∈ D₁', n + q ≠ gSplit v) →
        (C.gates.filter fun g => decide (n + q ∈ g.inputs)).length = 1) ∧
      (Finset.univ.filter fun v : Fin n =>
        (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length = 2).card + D₁'.card = (n + 1) / 2 ∧
      (∀ u v : Fin n, ((u.val + 1) % n = v.val ∨ (v.val + 1) % n = u.val) →
        u ∈ (Finset.univ.filter fun v : Fin n =>
          (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length = 2) ∪ D₁' ∨
        v ∈ (Finset.univ.filter fun v : Fin n =>
          (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length = 2) ∪ D₁') ∧
      (∀ c : Fin n,
        (C.gates.filter fun g => decide (c.val ∈ g.inputs)).length = 1 → c ∉ D₁' →
        ∃ qz w_c y_c : ℕ, qz < C.size ∧
          (C.gates[qz]? = some ⟨GateOp.and, [w_c, y_c]⟩ ∨ C.gates[qz]? = some ⟨GateOp.and, [y_c, w_c]⟩) ∧
          (Finset.univ.filter fun u : Fin n =>
            (C.wires (List.ofFn fun i : Fin n => decide (i = u))).getD w_c false = true) = {c} ∧
          (∀ u : Fin n, ((c.val + 1) % n = u.val ∨ (u.val + 1) % n = c.val) →
            u ∈ Finset.univ.filter fun u : Fin n =>
              (C.wires (List.ofFn fun i : Fin n => decide (i = u))).getD y_c false = true) ∧
          c ∉ Finset.univ.filter fun u : Fin n =>
            (C.wires (List.ofFn fun i : Fin n => decide (i = u))).getD y_c false = true)) :
    ∀ t : ℕ, t < C.size →
      ((∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, i < n) ∧
          ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false =
            decide (∃ i j : Fin n, i.val ∈ S ∧ (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) ∨
        (∃ a c b : Fin n, (a.val + 1) % n = c.val ∧ (c.val + 1) % n = b.val ∧
          ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = (x a || x b)) ∨
        (∃ i j k : Fin n, (i.val + 1) % n = j.val ∧ ((j.val + 1) % n = k.val ∨ (k.val + 1) % n = i.val) ∧
          ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = ((x i && x j) || x k))) := by
 obtain ⟨D₁',gS,hS1,hD1o,hCc,hCv,hCe0⟩:=hsplit;have h1e:D₁'=∅ :=
  d1E C hn hfun hout hbin hD_bounds D₁' gS hS1 hD1o hCc hCv hCe0
 subst h1e;simp only [card_empty,add_zero,union_empty,mN,
  not_false_eq_true,forall_const] at hCc hCv hCe0 hD1o
 let I:Finset (Fin n):=IS n C;have hIc:I.card=n/2:= by {have hc:=card_sdiff_add_card_eq_card (subset_univ (D2 n C));rw [card_univ,Fintype.card_fin,show (D2 n C).card=(n+1)/2 from hCc] at hc;change I.card+(n+1)/2=n at hc;omega};have hMI:∀ v:Fin n,v∈I↔wD C v.val=1:= by {intro v;have h0:1≤wD C v.val∧wD C v.val≤2:=hD_bounds v;simp only [I,D2,mS,mU,true_and,mF];omega};have hM2:∀ v:Fin n,v∈D2 n C↔wD C v.val=2:= by {intro v;simp [D2]};have hIN:∀ c∈I,∀ u:Fin n,cA c u→ u∈D2 n C :=
  fun c hc u hAd=>(hCv c u hAd).resolve_left (mS.1 hc).2
 have hEd:=d2E C hn hIc hIN;have hCe0':∀ c:Fin n,c∈I →
   ∃ qz w_c y_c:ℕ,qz<C.size ∧
    (C.gates[qz]?=some ⟨.and,[w_c,y_c]⟩∨C.gates[qz]?=some ⟨.and,[y_c,w_c]⟩) ∧
    S1 n C w_c={c}∧(∀ u:Fin n,cA c u→ u∈S1 n C y_c)∧c∉S1 n C y_c :=
  fun c hc=>hCe0 c ((hMI c).1 hc)
 classical
 let qz:Fin n→ ℕ:=fun c=>if hc:c∈I then (hCe0' c hc).choose else 0;let wc:Fin n→ ℕ:=fun c=>if hc:c∈I then (hCe0' c hc).choose_spec.choose else 0;let yc:Fin n→ ℕ:=fun c=>if hc:c∈I then (hCe0' c hc).choose_spec.choose_spec.choose else 0;have hQS:∀ c∈I,qz c<C.size ∧
   (C.gates[qz c]?=some ⟨.and,[wc c,yc c]⟩∨C.gates[qz c]?=some ⟨.and,[yc c,wc c]⟩) ∧
   S1 n C (wc c)={c}∧(∀ u:Fin n,cA c u→ u∈S1 n C (yc c))∧c∉S1 n C (yc c):= by
  intro c hc;simpa only [qz,wc,yc,hc,↓reduceDIte] using (hCe0' c hc).choose_spec.choose_spec.choose_spec
 have hp:0<C.size:= by {obtain ⟨c0,hc0⟩:=card_pos.1 (by omega:0<I.card);have:=(hQS c0 hc0).1;omega};have hQC:∀ c∈I,
   (gL C (qz c)=wc c∧gR C (qz c)=yc c) ∨
   (gL C (qz c)=yc c∧gR C (qz c)=wc c):= by
  intro c hc;rcases (hQS c hc).2.1 with h1 | h1;{left;simp [gL,gR,h1]};{right;simp [gL,gR,h1]}
 have hwl:∀ c∈I,wc c<n+qz c:= by
  intro c hc;obtain ⟨_,_,_,_,hl,hr⟩:=hbG C hbin (qz c) (hQS c hc).1;rcases hQC c hc with ⟨h1,_⟩ | ⟨_,h2⟩ <;> omega
 have hyl:∀ c∈I,yc c<n+qz c:= by
  intro c hc;obtain ⟨_,_,_,_,hl,hr⟩:=hbG C hbin (qz c) (hQS c hc).1;rcases hQC c hc with ⟨_,h2⟩ | ⟨h1,_⟩ <;> omega
 have hSE:∀ c∈I,S1 n C (n+qz c)=∅:= by
  intro c hc;obtain ⟨hqz,hGt,hSw,_,hcnoty⟩:=hQS c hc
  ext u
  simp only [mN,iff_false];rcases hGt with h1 | h1;{rw [s1A n C (qz c) (wc c) (yc c) hqz h1 (hwl c hc) (hyl c hc),hSw,mem_inter,m1];rintro ⟨rfl,hy⟩;exact hcnoty hy};{rw [s1A n C (qz c) (yc c) (wc c) hqz h1 (hyl c hc) (hwl c hc),hSw,mem_inter,m1];rintro ⟨hy,rfl⟩;exact hcnoty hy}
 have hQI:Set.InjOn qz (I:Set (Fin n)):= by
  intro c1 hc1 c2 hc2 heq;have h1:=hQC c1 hc1;have h2:=hQC c2 hc2;rw [heq] at h1;have hSw1:=(hQS c1 hc1).2.2.1;have hSw2:=(hQS c2 hc2).2.2.1;have hSy2:=(hQS c2 hc2).2.2.2.1;have hw1_ne_y2:wc c1≠yc c2:= by
   intro hwy;have ha:cN (by omega) c2∈S1 n C (wc c1):= by rw [hwy];exact hSy2 _ (cnA (by omega) c2)
   have hbin:cP (by omega) c2∈S1 n C (wc c1):= by {rw [hwy];exact hSy2 _ (cpA (by omega) c2)};rw [hSw1,m1] at ha hbin;exact cnNP hn c2 (ha.trans hbin.symm)
  have hw_eq:wc c1=wc c2:= by
   rcases h1 with ⟨ha1,hb1⟩ | ⟨ha1,hb1⟩ <;> rcases h2 with ⟨ha2,hb2⟩ | ⟨ha2,hb2⟩;{exact ha1.symm.trans ha2};{exact (hw1_ne_y2 (ha1.symm.trans ha2)).elim};{exact (hw1_ne_y2 (hb1.symm.trans hb2)).elim};{exact hb1.symm.trans hb2}
  exact singleton_injective (by rw [← hSw1,← hSw2,hw_eq]:({c1}:Finset (Fin n))={c2})
 have hLQ:∀ c∈I,∀ v:Fin n,
   lM n C v (n+qz c)=lM n C v (wc c)+lM n C v (yc c):= by
  intro c hc v;rw [lmG C hbin v (qz c) (hQS c hc).1];rcases hQC c hc with ⟨h1,h2⟩ | ⟨h1,h2⟩;{rw [h1,h2]};{rw [h1,h2,Nat.add_comm]}
 have hKY:∀ c∈I,∀ u:Fin n,cA c u→ 1≤kS n C u (qz c):= by
  intro c hc u hAd;unfold kS;have hNt0:u∉S1 n C (n+qz c):= by rw [hSE c hc];exact mN u
  simp only [hNt0,not_false_eq_true,↓reduceIte];have h1:=sl1 C hbin u (yc c) (by have:=hyl c hc;have:=(hQS c hc).1;omega)
   ((hQS c hc).2.2.2.1 u hAd)
  rcases hQC c hc with ⟨_,h2⟩ | ⟨h1',_⟩;{rw [h2];omega};{rw [h1'];omega}
 have hno_and:=noA C hn hfun hout hbin hD1o hp
  hMI hM2 hIN hEd qz wc yc hQS hQC hwl hyl hQI hLQ hKY
 have hTs:∀ t∈I.image qz,t<C.size:= by {intro t ht;obtain ⟨c,hc,rfl⟩:=mG.1 ht;exact (hQS c hc).1};have hAn:∀ t1∈I.image qz,∀ t2∈I.image qz,iS n C (n+t1) (n+t2)→ t1=t2:= by
  intro t1 ht1 t2 ht2 hsb;obtain ⟨c1,hc1,rfl⟩:=mG.1 ht1;obtain ⟨c2,hc2,rfl⟩:=mG.1 ht2;by_contra hne;rcases (hQS c2 hc2).2.1 with h1 | h1 <;>
  {have:=hno_and c1 hc1 (qz c2) (hQS c2 hc2).1 hsb (Ne.symm hne) _ h1;cases this}
 have hB:∀ v:Fin n,
   lmC n C (I.image qz) v C.output +
    ∑ c∈I,(lM n C v (wc c)+lM n C v (yc c))=wD C v.val:= by
  intro v;have h1:=lmcO C hout hbin hD1o hp (I.image qz) hTs hAn v;rw [sum_image (fun x hx y hy h=>hQI hx hy h)] at h1;have h2:∑ c∈I,lM n C v (n+qz c)=∑ c∈I,(lM n C v (wc c)+lM n C v (yc c)) :=
   sC rfl (fun c hc=>hLQ c hc v)
  omega
 obtain ⟨hYP,hCs⟩:=lpT C hn hfun hout hbin
  hMI hM2 hIN hEd qz wc yc hQS hwl hyl hB
 exact cfP C hn hfun hout hbin hD1o hp
  qz wc yc hQS hwl hyl hno_and hYP hCs
end PEqualNP.Outside.L_meta_314_aux.WirePart2
namespace PEqualNP.Outside.L_meta_314_aux.Final
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_314_aux
theorem main:∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), 5 ≤ n → PEqualNP.MetaComplexity.IsMinimalCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ t : ℕ, t < C.size → ((∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, i < n) ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = decide (∃ i j : Fin n, i.val ∈ S ∧ (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) ∨ (∃ a c b : Fin n, (a.val + 1) % n = c.val ∧ (c.val + 1) % n = b.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = (x a || x b)) ∨ (∃ i j k : Fin n, (i.val + 1) % n = j.val ∧ ((j.val + 1) % n = k.val ∨ (k.val + 1) % n = i.val) ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = ((x i && x j) || x k))):=by
 intro n C hn hmin hfun
 have hfunB:circuitFun n C=Bridge.cycFun n:=hfun
 obtain ⟨hnn,_,_,hsz,_,_,hbin⟩:=NoNot.minimal_clean_cyc n C hn hmin hfunB
 refine ⟨hnn,?_⟩
 have hout:C.output=n + C.size - 1:=WrapOut.output_eq_top hn C hmin hfunB
 have hbin2:∀ q < C.size,∃ g op a b,C.gates[q]?=some g∧g.op=op∧(op=GateOp.and∨op=GateOp.or)∧g.inputs=[a,b]∧a≠b∧a < n + q∧b < n + q:=by
  intro q hq;have hql:q < C.gates.length:=hq
  obtain ⟨hop,a,b,ha,hb,hne,hin⟩:=hbin q hq C.gates[q] (List.getElem?_eq_getElem hql)
  exact ⟨C.gates[q],C.gates[q].op,a,b,List.getElem?_eq_getElem hql,rfl,hop,hin,hne,ha,hb⟩
 have hSA:=WireClass.wire_class_stageA hn C hmin hnn hout hsz hfun hbin2 (fun p D hf he=>Bridge.cyc_false_size_lower hn p hf he) (fun p D hf he=>Bridge.cyc_true_size_lower hn p hf he)
 exact WirePart2.classify_of_struct n C hn hfun hout hbin2 hSA.1 hSA.2
end PEqualNP.Outside.L_meta_314_aux.Final

theorem PEqualNP.Outside.L_meta_314 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), 5 ≤ n → PEqualNP.MetaComplexity.IsMinimalCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ t : ℕ, t < C.size → ((∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, i < n) ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = decide (∃ i j : Fin n, i.val ∈ S ∧ (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) ∨ (∃ a c b : Fin n, (a.val + 1) % n = c.val ∧ (c.val + 1) % n = b.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = (x a || x b)) ∨ (∃ i j k : Fin n, (i.val + 1) % n = j.val ∧ ((j.val + 1) % n = k.val ∨ (k.val + 1) % n = i.val) ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = ((x i && x j) || x k))) := by
  exact PEqualNP.Outside.L_meta_314_aux.Final.main
