import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_172_aux
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity
namespace As
abbrev Fn (n:ℕ):=(Fin n→Bool)→Bool
def nT {n} (u:Fn n):Fn n:=fun x=> !(u x)
def eP {n} (u v:Fn n):Fn n:=fun x=>u x && v x
def ext {n} (P:Fn n→Prop) (g h:Fn n):=P h∨h=g∨h=nT g
def iT (n:ℕ) (h:Fn n):=(∃b:Bool,h=fun _=>b)∨∃i:Fin n,h=(fun x=>x i)∨h=nT (fun x=>x i)
def Build {n:ℕ} (P:Fn n→Prop) (f:Fn n):ℕ→Prop
 | 0=>P f
 | s+1=>P f∨∃u v,P u∧P v∧Build (ext P (eP u v)) f s
lemma Build.oN {n:ℕ} {P:Fn n→Prop} {f:Fn n} {s:ℕ} (a:P f):
  Build P f s:=by
 cases s with
 | zero=>exact a
 | succ s=>exact Or.inl a
lemma Build.mF {n:ℕ} {P:Fn n→Prop} {u v f:Fn n} {s:ℕ}
  (a:P u) (b:P v) (h:Build (ext P (eP u v)) f s):Build P f (s+1):=
 Or.inr ⟨u,v,a,b,h⟩
lemma Build.mG {n:ℕ}
  {a:(P:Fn n→Prop)→(f:Fn n)→(s:ℕ)→Build P f s→Prop}
  (oN:∀{P f s},(h:P f)→a P f s (Build.oN h))
  (mF:∀{P u v f s} (b:P u) (c:P v) (h:Build (ext P (eP u v)) f s),
    a _ f s h→a P f (s+1) (Build.mF b c h))
  {P f s} (h:Build P f s):a P f s h:=by
 induction s generalizing P with
 | zero=>exact oN h
 | succ s ih=>
   rcases h with d|⟨u,v,b,c,h⟩
   ·exact oN d
   ·exact mF b c h (ih h)
def dO (n:ℕ) (f:Fn n) (s:ℕ):=Build (iT n) f s
variable {n : ℕ}
def R (p:Fin n) (b:Bool) (f:Fn n):Fn n:=fun x=>f (Function.update x p b)
def cI (p:Fin n) (f:Fn n):=∀b,R p b f=f
def nU (f:Fn n):=∃b:Bool,f=fun _=>b
def gY (P:Fn n→Prop):=(∀b:Bool,P (fun _=>b))∧∀u,P u→P (nT u)
@[simp] lemma neg_neg (u : Fn n) : nT (nT u) = u := by funext x; simp [nT]
lemma gZ {P:Fn n→Prop} (a:gY P) (u:Fn n):gY (ext P u):=by
 refine⟨fun b=>Or.inl (a.1 b),?_⟩;rintro v (hv|rfl|rfl)
 ·exact Or.inl (a.2 _ hv)
 ·exact Or.inr (Or.inr rfl)
 ·exact Or.inr (Or.inl (neg_neg _))
lemma iU (n:ℕ):gY (iT n):=by
 refine⟨fun b=>Or.inl ⟨b,rfl⟩,?_⟩;rintro v (⟨b,rfl⟩|⟨i,rfl|rfl⟩)
 ·exact Or.inl ⟨!b,rfl⟩
 ·exact Or.inr ⟨i,Or.inr rfl⟩
 ·exact Or.inr ⟨i,Or.inl (neg_neg _)⟩
lemma nV {p:Fin n} {u v:Fn n} (a:cI p u) (c:cI p v):
  cI p (eP u v):=by
 intro b;exact congrArg₂ eP (a b) (c b)
lemma hF {p:Fin n} {u:Fn n} (a:cI p u):cI p (nT u):=fun b=>congrArg nT (a b)
lemma vJ {P Q:Fn n→Prop} {u:Fn n} {p:Fin n} {b:Bool}
  (h:∀v,P v→Q (R p b v)):
  ∀v,ext P u v→ext Q (R p b u) (R p b v):=by
 rintro v (hv|rfl|rfl)
 ·exact Or.inl (h _ hv)
 ·exact Or.inr (Or.inl rfl)
 ·exact Or.inr (Or.inr rfl)
lemma yS {P:Fn n→Prop} {f:Fn n} {s} (h:Build P f s)
  (p:Fin n) (b:Bool) {Q:Fn n→Prop} (a:∀v,P v→Q (R p b v)):
  Build Q (R p b f) s:=by
 induction h using Build.mG generalizing Q with
 | oN hf=>exact .oN (a _ hf)
 | mF hu hv _ ih=>exact .mF (a _ hu) (a _ hv) (ih (vJ a))
lemma Build.mono {P:Fn n→Prop} {f:Fn n} {s t} (h:Build P f s) (a:s≤t):
  Build P f t:=by
 induction h using Build.mG generalizing t with
 | oN hf=>exact .oN hf
 | mF hu hv _ ih=>
   cases t with
   | zero=>omega
   | succ t=>exact .mF hu hv (ih (by omega))
lemma pB {P Q:Fn n→Prop} {u:Fn n} {p:Fin n} {b:Bool} (c:gY Q)
  (h:∀v,P v→Q (R p b v)) (a:Q (R p b u)):
  ∀v,ext P u v→Q (R p b v):=by
 rintro v (hv|rfl|rfl)
 ·exact h _ hv
 ·exact a
 ·exact c.2 _ a
lemma rG (u:Fn n):eP (fun _=>false) u=fun _=>false:=by funext x;change(false && u x)=false;cases u x<;>rfl
lemma yT (u:Fn n):eP (fun _=>true) u=u:=by funext x;change(true && u x)=u x;cases u x<;>rfl
lemma rH (u:Fn n):eP u (fun _=>false)=fun _=>false:=by funext x;change(u x && false)=false;cases u x<;>rfl
lemma yU (u:Fn n):eP u (fun _=>true)=u:=by funext x;change(u x && true)=u x;cases u x<;>rfl
lemma vK {Q:Fn n→Prop} {u v:Fn n} (a:gY Q)
  (c:Q u) (d:Q v) (h:nU u∨nU v):Q (eP u v):=by
 rcases h with⟨b,rfl⟩|⟨b,rfl⟩
 ·cases b
  ·rw[rG];exact a.1 false
  ·rw[yT];exact d
 ·cases b
  ·rw[rH];exact a.1 false
  ·rw[yU];exact c
lemma mH {P:Fn n→Prop} {f:Fn n} {s} (h:Build P f s)
  (p:Fin n) (b:Bool) {Q:Fn n→Prop} (g:gY Q)
  (c:∀v,P v→Q (R p b v))
  (a:∀v,P v→¬cI p v→nU (R p b v))
  (i:¬cI p f) (e:¬nU (R p b f)):
  ∃t,t+1≤ s∧Build Q (R p b f) t:=by
 classical
 induction h using Build.mG generalizing Q with
 | oN hf=>exact(e (a _ hf i)).elim
 | @mF P u v f s hu hv h ih=>
   by_cases d:cI p u∧cI p v
   ·have hs:=nV d.1 d.2;obtain⟨t,ht,hh⟩:=ih (gZ g _) (vJ c) (by
     rintro w (hw|rfl|rfl) hn
     ·exact a _ hw hn
     ·exact(hn hs).elim
     ·exact(hn (hF hs)).elim) i e
    exact⟨t+1,by omega,.mF (c _ hu) (c _ hv) hh⟩
   ·have k:Q (R p b (eP u v)):=by
     apply vK g (c _ hu) (c _ hv);by_cases j:cI p u
     ·exact Or.inr (a _ hv (fun l=>d ⟨j,l⟩))
     ·exact Or.inl (a _ hu j)
    exact⟨s,by omega,yS h p b (pB g c k)⟩
lemma sB {P:Fn n→Prop} {f:Fn n} {s} (h:Build P f s)
  (p:Fin n) {Q:Bool→Fn n→Prop} (g:∀b,gY (Q b))
  (i:∀b v,P v→Q b (R p b v))
  (a:∀v,P v→¬cI p v→
    (∀b,nU (R p b v))∧∃b,R p b v=fun _=>false)
  (k:¬cI p f) (d:∀b,¬nU (R p b f)):
  ∃b t,t+2≤ s∧Build (Q b) (R p b f) t:=by
 classical
 induction h using Build.mG generalizing Q with
 | oN hf=>exact(d false ((a _ hf k).1 false)).elim
 | @mF P u v f s hu hv h ih=>
   by_cases e:cI p u∧cI p v
   ·have hs:=nV e.1 e.2;obtain⟨b,t,ht,hh⟩:=ih (fun b=>gZ (g b) (R p b (eP u v)))
     (fun b=>vJ (i b)) (by
       rintro w (hw|rfl|rfl) hn
       ·exact a _ hw hn
       ·exact(hn hs).elim
       ·exact(hn (hF hs)).elim) k d
    exact⟨b,t+1,by omega,.mF (i b _ hu) (i b _ hv) hh⟩
   ·have j:∃b,R p b (eP u v)=fun _=>false:=by
     by_cases l:cI p u
     ·obtain⟨b,c⟩:=(a _ hv (fun o=>e ⟨l,o⟩)).2;refine⟨b,?_⟩;change eP (R p b u) (R p b v)=_;rw[c,rH]
     ·obtain⟨b,c⟩:=(a _ hu l).2;refine⟨b,?_⟩;change eP (R p b u) (R p b v)=_;rw[c,rG]
    obtain⟨b,c⟩:=j;have m:Q b (R p b (eP u v)):=c▸(g b).1 false;obtain⟨t,ht,hh⟩:=mH h p b (g b) (pB (g b) (i b) m) (by
     rintro w (hw|rfl|rfl) hn
     ·exact(a _ hw hn).1 b
     ·exact⟨false,c⟩
     ·exact⟨true,congrArg nT c⟩) k (d b)
    exact⟨b,t,by omega,hh⟩
lemma dZ {i p:Fin n} (a:i≠p):cI p (fun x=>x i):=by intro b;funext x;exact Function.update_of_ne a _ _
lemma cQ (i:Fin n) (b:Bool):R i b (fun x=>x i)=fun _=>b:=by funext x;exact Function.update_self _ _ _
lemma wP (p:Fin n) (b:Bool):∀v,iT n v→iT n (R p b v):=by
 rintro v (⟨k,rfl⟩|⟨i,rfl|rfl⟩)
 ·exact Or.inl ⟨k,rfl⟩
 ·by_cases a:i=p
  ·subst i;exact Or.inl ⟨b,cQ p b⟩
  ·exact Or.inr ⟨i,Or.inl (dZ a b)⟩
 ·by_cases a:i=p
  ·subst i;exact Or.inl ⟨!b,congrArg nT (cQ p b)⟩
  ·exact Or.inr ⟨i,Or.inr (hF (dZ a) b)⟩
lemma wQ (p:Fin n):∀v,iT n v→¬cI p v→
  (∀b,nU (R p b v))∧∃b,R p b v=fun _=>false:=by
 rintro v (⟨c,rfl⟩|⟨i,rfl|rfl⟩) hn
 ·exact(hn (fun _=>rfl)).elim
 ·by_cases a:i=p
  ·subst i;exact⟨fun b=>⟨b,cQ p b⟩,false,cQ p false⟩
  ·exact(hn (dZ a)).elim
 ·by_cases a:i=p
  ·subst i;exact⟨fun b=>⟨!b,congrArg nT (cQ p b)⟩,true,congrArg nT (cQ p true)⟩
  ·exact(hn (hF (dZ a))).elim
lemma rI {p:Fin n} {f:Fn n}
  (h:∃x,f (Function.update x p (!x p))≠f x):¬cI p f:=by
 obtain⟨x,a⟩:=h;exact fun hs=>a (congrFun (hs (!x p)) x)
lemma tQ {f:Fn n} (h:∃x y,f x≠f y):¬nU f:=by obtain⟨x,y,hh⟩:=h;rintro⟨k,rfl⟩;exact hh rfl
lemma eI (n:ℕ) (f:Fn (n+1)) (p:Fin (n+1)) (b:Bool) (s:ℕ)
  (a:∃x,f (Function.update x p (!x p))≠f x)
  (c:∃x y,f (Function.update x p b)≠f (Function.update y p b))
  (h:dO (n+1) f (s+1)):
  dO (n+1) (fun x=>f (Function.update x p b)) s:=by
 obtain⟨t,ht,hh⟩:=mH h p b (iU _) (wP p b)
  (fun v e d=>(wQ p v e d).1 b) (rI a) (tQ c)
 exact hh.mono (by omega)
lemma dG (n:ℕ) (f:Fn (n+1)) (p:Fin (n+1)) (s:ℕ)
  (a:∃x,f (Function.update x p (!x p))≠f x)
  (c:∀b:Bool,∃x y,f (Function.update x p b)≠f (Function.update y p b))
  (h:dO (n+1) f s):
  ∃b s',s'+2≤ s∧dO (n+1) (fun x=>f (Function.update x p b)) s':=
 sB h p (Q:=fun _=>iT (n+1)) (fun _=>iU _) (wP p) (wQ p) (rI a) (fun b=>tQ (c b))
end As
namespace As
variable {n : ℕ}
def oO (T:Finset (Fn n)) (f:Fn n):Prop:=∀x y,(∀w∈T,w x=w y)→f x=f y
lemma kG {P:Fn n→Prop} {f:Fn n} {s:ℕ}
  (h:Build P f s):
  ∃T:Finset (Fn n),T.card≤ s+1∧(∀w∈T,P w)∧oO T f:=by
 classical
 induction h using Build.mG with
 | @oN P f s hf=>
   refine⟨{f},by simp,?_,?_⟩
   ·simpa using hf
   ·intro x y d;exact d _ (Finset.mem_singleton_self _)
 | @mF P u v f s hu hv _ ih=>
   obtain⟨T,E,m,o⟩:=ih
   let g:=eP u v
   by_cases e:g∈T∨nT g∈T
   ·let U:=(T.erase g).erase (nT g)
    have F:U.card+1≤T.card:=by
     rcases e with e|e
     ·have r:U.card≤(T.erase g).card:=
       Finset.card_le_card (Finset.erase_subset _ _)
      have j:=Finset.card_erase_add_one e;omega
     ·have q:U⊆T.erase (nT g):=by
       intro w a;have b:=Finset.mem_erase.mp a;exact Finset.mem_erase.mpr ⟨b.1,(Finset.mem_erase.mp b.2).2⟩
      have r:=Finset.card_le_card q;have j:=Finset.card_erase_add_one e;omega
    refine⟨insert u (insert v U),?_,?_,?_⟩
    ·have A:=Finset.card_insert_le u (insert v U);have B:=Finset.card_insert_le v U;omega
    ·intro w a;rcases Finset.mem_insert.mp a with rfl|a
     ·exact hu
     rcases Finset.mem_insert.mp a with rfl|a
     ·exact hv
     have b:=Finset.mem_erase.mp a;have i:=Finset.mem_erase.mp b.2;rcases m w i.2 with a|c|c
     ·exact a
     ·exact(i.1 c).elim
     ·exact(b.1 c).elim
    ·intro x y d;have t:=d u (Finset.mem_insert_self _ _);have z:=d v (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _));have p:g x=g y:=congrArg₂ (· && ·) t z;apply o x y;intro w a;by_cases k:w=g
     ·simpa only[k] using p
     by_cases l:w=nT g
     ·simpa only[l,nT] using congrArg (! ·) p
     exact d w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨l,Finset.mem_erase.mpr ⟨k,a⟩⟩)))
   ·refine⟨T,by omega,?_,o⟩;intro w a;rcases m w a with C|k|l
    ·exact C
    ·exact(e (Or.inl (by simpa only[←k,g] using a))).elim
    ·exact(e (Or.inr (by simpa only[←l,g] using a))).elim
lemma pC {w:Fn n} (a:iT n w):
  ∃
   A:Finset (Fin n),A.card≤1∧
   ∀x y:Fin n→Bool,(∀i∈A,x i=y i)→w x=w y:=by
 classical
 rcases a with⟨b,rfl⟩|⟨i,rfl|rfl⟩
 ·exact⟨∅,by simp,fun _ _ _=>rfl⟩
 ·exact⟨{i},by simp,fun _ _ h=>h i (Finset.mem_singleton_self i)⟩
 ·exact⟨{i},by simp,fun _ _ h=>congrArg (! ·) (h i (Finset.mem_singleton_self i))⟩
lemma lJ (T:Finset (Fn n)) (f:∀w∈T,iT n w):
  ∃
   A:Finset (Fin n),A.card≤T.card∧
   ∀x y:Fin n→Bool,(∀i∈A,x i=y i)→∀w∈T,w x=w y:=by
 classical
 induction T using Finset.induction_on with
 | empty=>
   refine⟨∅,le_rfl,?_⟩;simp
 | @insert w T hw ih=>
   obtain⟨A,h,d⟩:=ih (fun z a=>f z (Finset.mem_insert_of_mem a));obtain⟨B,j,e⟩:=pC (f w (Finset.mem_insert_self _ _));refine⟨A∪B,?_,?_⟩
   ·rw[Finset.card_insert_of_notMem hw];have g:=Finset.card_union_le A B;omega
   ·intro x y b z a;rcases Finset.mem_insert.mp a with rfl|a
    ·exact e x y (fun i c=>b i (Finset.mem_union_right A c))
    ·exact d x y (fun i c=>b i (Finset.mem_union_left B c)) z a
lemma kH {f:Fn n} {s:ℕ} (h:dO n f s):
  ∃
   A:Finset (Fin n),A.card≤ s+1∧
   ∀x y:Fin n→Bool,(∀i∈A,x i=y i)→f x=f y:=by
 obtain⟨T,d,c,e⟩:=kG h;obtain⟨A,a,b⟩:=lJ T c;exact⟨A,a.trans d,fun x y g=>e x y (b x y g)⟩
lemma cD (n:ℕ) (f:Fn n) (T:Finset (Fin n))
  (a:∀i∈T,∃x:Fin n→Bool,f (Function.update x i (!x i))≠f x)
  (s:ℕ) (h:dO n f s):T.card≤ s+1:=by
 classical
 obtain⟨A,b,c⟩:=kH h;refine(Finset.card_le_card ?_).trans b;intro i g;by_contra d;obtain⟨x,l⟩:=a i g;apply l;apply c;intro j k;exact Function.update_of_ne (by intro e;exact d (e▸k)) _ _
end As
namespace PEqualNP.MetaComplexity.Aa.Ak
open SimpleGraph
lemma kI {V:Type*} [Fintype V] (G:SimpleGraph V) [Nonempty V]:
  ∃
   (a b:V) (P:G.Walk a b),P.IsPath∧
   ∀(c d:V) (Q:G.Walk c d),Q.IsPath→Q.length≤P.length:=by
 by_contra e
 push Not at e
 have g:∀k:ℕ,∃(a b:V) (P:G.Walk a b),P.IsPath∧k≤P.length:=by
  intro k
  induction k with
  | zero=>
    obtain⟨v⟩:= ‹Nonempty V›;exact⟨v,v,Walk.nil,Walk.IsPath.nil,le_refl _⟩
  | succ k ih=>
    obtain⟨a,b,P,f,g⟩:=ih;obtain⟨c,d,Q,h,j⟩:=e a b P f;exact⟨c,d,Q,h,by omega⟩
 obtain⟨a,b,P,f,i⟩:=g (Fintype.card V);have:=f.length_lt;omega
lemma gM {V:Type*} [Fintype V] (G:SimpleGraph V) (r:G.IsAcyclic)
  (J:∃u v:V,G.Adj u v):
  ∃
   l p:V,G.Adj l p∧(∀w,G.Adj l w→w=p)∧
   ((∃q:V,∀w,G.Adj p w→w=l∨w=q)∨
     (∃f:V,f≠l∧G.Adj p f∧∀w,G.Adj f w→w=p)):=by
 classical
 obtain⟨F,K,y⟩:=J
 have:Nonempty V:=⟨F⟩
 obtain⟨l,z,P,A,k⟩:=kI G
 have H:1≤P.length:=by
  have:=k F K (Walk.cons y Walk.nil) (by simp[Walk.cons_isPath_iff,y.ne])
  simpa using this
 cases P with
 | nil=>simp at H
 | @cons _ p _ hlp P'=>
   rw[Walk.cons_isPath_iff] at A
   obtain⟨j,s⟩:=A
   have g:∀(c d:V) (Q:G.Walk c d),Q.IsPath→Q.length≤P'.length+1:=by
    intro c d Q i
    have:=k c d Q i
    simpa using this
   have b:(Walk.cons hlp P').IsPath:=(Walk.cons_isPath_iff _ _).2 ⟨j,s⟩
   have n:∀w,G.Adj l w→w=p:=by
    intro w a
    by_cases e:w∈(Walk.cons hlp P').support
    ·have:=r.eq_snd_of_adj_start b a e
     simpa using this
    ·exfalso
     have i:(Walk.cons a.symm (Walk.cons hlp P')).IsPath:=
      (Walk.cons_isPath_iff _ _).2 ⟨b,e⟩
     have:=g _ _ _ i
     simp at this
   refine⟨l,p,hlp,n,?_⟩
   have t:∀w,G.Adj p w→w∉(Walk.cons hlp P').support→
     ∀u,G.Adj w u→u=p:=by
    intro w a E u C
    have x:w∉P'.support:=by
     intro h;exact E (by simp[h])
    have i:(Walk.cons a.symm P').IsPath:=(Walk.cons_isPath_iff _ _).2 ⟨j,x⟩
    by_cases e:u∈(Walk.cons a.symm P').support
    ·have:=r.eq_snd_of_adj_start i C e
     simpa using this
    ·exfalso
     have B:(Walk.cons C.symm (Walk.cons a.symm P')).IsPath:=
      (Walk.cons_isPath_iff _ _).2 ⟨i,e⟩
     have:=g _ _ _ B
     simp at this
   by_cases o:∃f:V,f≠l∧G.Adj p f∧∀w,G.Adj f w→w=p
   ·exact Or.inr o
   ·left
    refine⟨P'.snd,fun w a=> ?_⟩
    by_cases m:w=l
    ·exact Or.inl m
    ·right
     by_cases e:w∈P'.support
     ·exact r.eq_snd_of_adj_start j a e
     ·exfalso
      apply o
      refine⟨w,m,a,t w a ?_⟩
      simp[m,e]
end PEqualNP.MetaComplexity.Aa.Ak
namespace PEqualNP.MetaComplexity.Aa.Ak
open SimpleGraph
noncomputable def F {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (x:Fin n→Bool):
  Bool:=
 @decide ((∃a∈A,x a=true)∨∃i j:Fin n,G.Adj i j∧x i=true∧x j=true)
  (Classical.propDecidable _)
lemma hK {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (x:Fin n→Bool):
  F
   G A x=true↔
   ((∃a∈A,x a=true)∨∃i j:Fin n,G.Adj i j∧x i=true∧x j=true):=by
 unfold F;exact @decide_eq_true_iff _ (Classical.propDecidable _)
lemma aCh {n:ℕ} (G G':SimpleGraph (Fin n)) (A A':Finset (Fin n)) (x y:Fin n→Bool)
  (h:((∃a∈A,x a=true)∨∃i j:Fin n,G.Adj i j∧x i=true∧x j=true)↔
    ((∃a∈A',y a=true)∨∃i j:Fin n,G'.Adj i j∧y i=true∧y j=true)):
  F G A x=F G' A' y:=by
 rw[Bool.eq_iff_iff,hK,hK];exact h
lemma yV {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)):
  F G A (fun _=>false)=false:=by
 rw[Bool.eq_false_iff,ne_eq,hK];simp
lemma aBy {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n))
  (h:A.Nonempty∨∃i j:Fin n,G.Adj i j):
  ∃x y:Fin n→Bool,F G A x≠F G A y:=by
 refine⟨fun _=>true,fun _=>false,?_⟩;rw[yV];have:F G A (fun _=>true)=true:=by
  rw[hK];rcases h with⟨a,c⟩|⟨i,j,b⟩
  ·exact Or.inl ⟨a,c,rfl⟩
  ·exact Or.inr ⟨i,j,b,rfl,rfl⟩
 rw[this];simp
lemma yW {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (u v:Fin n)
  (d:G.Adj u v) (l:v∉A):
  ∃x:Fin n→Bool,F G A (Function.update x u (!x u))≠F G A x:=by
 have c:u≠v:=d.ne;refine⟨Function.update (fun _=>false) v true,?_⟩;have g:F G A (Function.update (Function.update (fun _=>false) v true) u
   (!(Function.update (fun _=>false) v true u)))=true:=by
  rw[hK];right;refine⟨u,v,d,?_,?_⟩
  ·simp[Function.update_of_ne c]
  ·simp[Function.update_of_ne c.symm]
 have k:F G A (Function.update (fun _=>false) v true)=false:=by
  rw[Bool.eq_false_iff,ne_eq,hK];rintro(⟨a,ha,hx⟩|⟨i,j,hij,hi,hj⟩)
  ·by_cases b:a=v
   ·exact l (b▸ha)
   ·simp[Function.update_of_ne b] at hx
  ·have e:i=v:=by
    by_contra h;simp[Function.update_of_ne h] at hi
   have f:j=v:=by by_contra h;simp[Function.update_of_ne h] at hj
   exact hij.ne (e.trans f.symm)
 rw[g,k];simp
lemma aAz {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (a:Fin n)
  (b:a∈A):
  ∃x:Fin n→Bool,F G A (Function.update x a (!x a))≠F G A x:=by
 refine⟨fun _=>false,?_⟩;rw[yV];have:F G A (Function.update (fun _=>false) a (!false))=true:=by rw[hK];exact Or.inl ⟨a,b,by simp⟩
 rw[this];simp
lemma iV {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (l p:Fin n)
  (m:l∉A) (f:∀w,G.Adj l w→w=p) (x:Fin n→Bool):
  F G A (Function.update x l false)=F (G.deleteEdges {s(l,p)}) A x:=by
 apply aCh;apply or_congr
 ·constructor
  ·rintro⟨a,g,h⟩;have k:a≠l:=fun e=>m (e▸g)
   exact⟨a,g,by rwa [Function.update_of_ne k] at h⟩
  ·rintro⟨a,g,h⟩;have k:a≠l:=fun e=>m (e▸g)
   exact⟨a,g,by rwa [Function.update_of_ne k]⟩
 ·constructor
  ·rintro⟨i,j,b,q,r⟩;have c:i≠l:=by rintro rfl;simp at q
   have d:j≠l:=by rintro rfl;simp at r
   refine⟨i,j,?_,by rwa [Function.update_of_ne c] at q,by rwa [Function.update_of_ne d] at r⟩;rw[deleteEdges_adj];refine⟨b,?_⟩;simp[c,d]
  ·rintro⟨i,j,b,q,r⟩;rw[deleteEdges_adj] at b;obtain⟨b,o⟩:=b;have c:i≠l:=by
    rintro rfl;have:=f j b;subst this;exact o rfl
   have d:j≠l:=by rintro rfl;have:=f i b.symm;subst this;exact o (Sym2.eq_swap)
   exact⟨i,j,b,by rwa [Function.update_of_ne c],by rwa [Function.update_of_ne d]⟩
lemma kT {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (l p q:Fin n)
  (z:l∉A) (o:G.Adj l p) (d:∀w,G.Adj l w→w=p)
  (B:∀w,G.Adj p w→w=l∨w=q) (x:Fin n→Bool):
  F G A (Function.update x l true)=F (G.deleteEdges {s(p,l),s(p,q)}) (insert p A) x:=by
 have k:p≠l:=o.ne.symm
 have r:∀a∈A,Function.update x l true a=x a:=fun a c=>
  Function.update_of_ne (by rintro rfl;exact z c) _ _
 have m:∀i j,(G.deleteEdges {s(p,l),s(p,q)}).Adj i j→i≠p∧i≠l:=by
  intro i j b
  rw[deleteEdges_adj] at b
  obtain⟨b,g⟩:=b
  constructor
  ·rintro rfl
   rcases B j b with rfl|rfl
   ·exact g (by simp)
   ·exact g (by simp)
  ·rintro rfl
   have:=d j b
   subst this
   exact g (by simp[Sym2.eq_swap])
 apply aCh
 constructor
 ·rintro(⟨a,c,h⟩|⟨i,j,b,hi,hj⟩)
  ·exact Or.inl ⟨a,Finset.mem_insert_of_mem c,by rwa [r a c] at h⟩
  ·by_cases e:i=p
   ·subst e
    exact Or.inl ⟨i,Finset.mem_insert_self _ _,by rwa [Function.update_of_ne k] at hi⟩
   by_cases f:j=p
   ·subst f
    exact Or.inl ⟨j,Finset.mem_insert_self _ _,by rwa [Function.update_of_ne k] at hj⟩
   have u:i≠l:=by
    rintro rfl;exact f (d j b)
   have y:j≠l:=by
    rintro rfl;exact e (d i b.symm)
   right
   refine⟨i,j,?_,by rwa [Function.update_of_ne u] at hi,
    by rwa [Function.update_of_ne y] at hj⟩
   rw[deleteEdges_adj]
   refine⟨b,?_⟩
   simp[e,f]
 ·rintro(⟨a,c,h⟩|⟨i,j,b,hi,hj⟩)
  ·rcases Finset.mem_insert.1 c with rfl|c
   ·right
    exact⟨l,a,o,by simp,by rwa [Function.update_of_ne k]⟩
   ·exact Or.inl ⟨a,c,by rwa [r a c]⟩
  ·right
   have t:=m i j b
   have v:=m j i b.symm
   rw[deleteEdges_adj] at b
   exact⟨i,j,b.1,by rwa [Function.update_of_ne t.2],
    by rwa [Function.update_of_ne v.2]⟩
def yX {n:ℕ} (G:SimpleGraph (Fin n)) (T:Finset (Fin n)):Prop:=∀i j,G.Adj i j→i∈T∨j∈T
lemma lK {n:ℕ} (G:SimpleGraph (Fin n)) (S:Set (Sym2 (Fin n))) (p:Fin n)
  (c:∀e∈S,p∈e) (T:Finset (Fin n)) (d:yX (G.deleteEdges S) T):
  yX G (insert p T):=by
 intro i j b;by_cases a:s(i,j)∈S
 ·have:=c _ a;rcases Sym2.mem_iff.1 this with rfl|rfl
  ·exact Or.inl (Finset.mem_insert_self _ _)
  ·exact Or.inr (Finset.mem_insert_self _ _)
 ·rcases d i j ((deleteEdges_adj).2 ⟨b,a⟩) with h|h
  ·exact Or.inl (Finset.mem_insert_of_mem h)
  ·exact Or.inr (Finset.mem_insert_of_mem h)
lemma tR {n:ℕ} (G:SimpleGraph (Fin n)) (l p a:Fin n) (k:ℕ)
  (v:a≠l) (g:G.Adj p a) (b:∀w,G.Adj a w→w=p)
  (z:∀T,yX G T→k≤T.card) (T:Finset (Fin n))
  (o:yX (G.deleteEdges {s(l,p)}) T):k≤T.card:=by
 have B:∀e∈({s(l,p)}:Set (Sym2 (Fin n))),p∈e:=by intro e y;rw[Set.mem_singleton_iff] at y;subst y;exact Sym2.mem_mk_right _ _
 by_cases m:p∈T
 ·have:=z _ (lK G _ p B T o);rwa [Finset.insert_eq_of_mem m] at this
 ·have u:a∈T:=by
   have x:p≠a:=g.ne;rcases o p a ((deleteEdges_adj).2 ⟨g,by simp[v,x.symm]⟩) with h|h
   ·exact absurd h m
   ·exact h
  have q:yX G (insert p (T.erase a)):=by
   intro i j c;by_cases d:i=p
   ·exact Or.inl (d▸Finset.mem_insert_self _ _)
   by_cases f:j=p
   ·exact Or.inr (f▸Finset.mem_insert_self _ _)
   have A:(G.deleteEdges {s(l,p)}).Adj i j:=(deleteEdges_adj).2 ⟨c,by simp[d,f]⟩;rcases o i j A with h | h
   ·have r:i≠a:=by
     rintro rfl;exact f (b j c)
    exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨r,h⟩))
   ·have t:j≠a:=by
     rintro rfl;exact d (b i c.symm)
    exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨t,h⟩))
  have C:=z _ q;have E:=Finset.card_insert_le p (T.erase a);have F:=Finset.card_erase_add_one u;omega
lemma fG {n:ℕ} (G:SimpleGraph (Fin n)) (l p:Fin n) (h:G.Adj l p):
  (G.deleteEdges {s(l,p)}).edgeSet.ncard+1=G.edgeSet.ncard:=by
 rw[edgeSet_deleteEdges];exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.2 h)
lemma pD {n:ℕ} (G:SimpleGraph (Fin n)) (l p q:Fin n) (h:G.Adj l p):
  G.edgeSet.ncard≤(G.deleteEdges {s(p,l),s(p,q)}).edgeSet.ncard+2∧(G.deleteEdges {s(p,l),s(p,q)}).edgeSet.ncard<G.edgeSet.ncard:=by
 rw[edgeSet_deleteEdges];constructor
 ·have g:=Set.ncard_le_ncard_sdiff_add_ncard G.edgeSet ({s(p,l),s(p,q)}:Set (Sym2 (Fin n)));have d:=Set.ncard_insert_le (s(p,l)) ({s(p,q)}:Set (Sym2 (Fin n)));rw[Set.ncard_singleton] at d;omega
 ·have b:s(l,p)∈G.edgeSet:=G.mem_edgeSet.2 h;have c:G.edgeSet \ {s(p,l),s(p,q)}⊆G.edgeSet \ {s(l,p)}:=by
   intro e f;refine⟨f.1,?_⟩;intro a;apply f.2;rw[Set.mem_singleton_iff] at a;rw[a,Sym2.eq_swap];exact Set.mem_insert _ _
  have g:=Set.ncard_le_ncard c;have d:=Set.ncard_sdiff_singleton_lt_of_mem b;omega
lemma hM {n:ℕ} (G:SimpleGraph (Fin n)) (h:∀i j,¬G.Adj i j):
  G.edgeSet.ncard=0:=by
 have:G.edgeSet= ∅ :=by
  apply Set.eq_empty_iff_forall_notMem.2;intro e
  induction e using Sym2.ind with
  | _ i j=>exact fun a=>h i j (G.mem_edgeSet.1 a)
 rw[this,Set.ncard_empty]
lemma xO {n:ℕ} (G:SimpleGraph (Fin n)) (l p q:Fin n)
  (c:∀w,G.Adj p w→w=l∨w=q) (i j:Fin n)
  (a:(G.deleteEdges {s(p,l),s(p,q)}).Adj i j):i≠p:=by
 rw[deleteEdges_adj] at a;obtain⟨a,b⟩:=a;rintro rfl;rcases c j a with rfl|rfl
 ·exact b (by simp)
 ·exact b (by simp)
end PEqualNP.MetaComplexity.Aa.Ak
namespace As
open PEqualNP.MetaComplexity.Aa.Ak
open SimpleGraph
section
variable
    (dO : (n : ℕ) → ((Fin n → Bool) → Bool) → ℕ → Prop)
    (eI : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool)
      (p : Fin (n + 1)) (b : Bool) (s : ℕ),
      (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) →
      (∃ x y : Fin (n + 1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) →
      dO (n + 1) f (s + 1) → dO (n + 1) (fun x => f (Function.update x p b)) s)
    (dG : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool)
      (p : Fin (n + 1)) (s : ℕ),
      (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) →
      (∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b)) →
      dO (n + 1) f s →
      ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
        dO (n + 1) (fun x => f (Function.update x p b)) s')
    (cD : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n)),
      (∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x) →
      ∀ (s : ℕ), dO n f s → T.card ≤ s + 1)
include eI dG cD
lemma iQ:
  ∀
   (m n:ℕ) (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (k s:ℕ),
   G.edgeSet.ncard=m→G.IsAcyclic→(∀i j,G.Adj i j→i∉A)→
   (∀T,yX G T→k≤T.card)→(A.Nonempty∨∃i j,G.Adj i j)→
   dO n (F G A) s→A.card+m+k≤ s+1:=by
 intro m
 induction m using Nat.strong_induction_on with
 | _ m ih=>
 intro n G A k s hm M o O b6 X;by_cases Z:∃i j,G.Adj i j;swap
 ·push Not at Z
  have u:k≤(∅ :Finset (Fin n)).card:=O ∅ (fun i j h=>absurd h (Z i j));have b4:m=0:=by rw[←hm];exact hM G Z
  have:=cD n (F G A) A (fun a ha=>aAz G A a ha) s X;simp at u;omega
 obtain⟨l,p,c,C,a0⟩:=gM G M Z;obtain⟨r,rfl⟩:∃r,n=r+1:=⟨n-1,by have:=l.2;omega⟩
 have R:l∉A:=o l p c;have a3:p∉A:=o p l c.symm;have g:=yW G A l p c a3;have a1:=yW G A p l c.symm R;have c0:2≤ s+1:=by
  have:=cD _ (F G A) {l,p} (by
   intro i t;rcases Finset.mem_insert.1 t with rfl|t
   ·exact g
   ·rw[Finset.mem_singleton] at t;subst t;exact a1) s X
  rwa [Finset.card_pair c.ne] at this
 set G0:=G.deleteEdges {s(l,p)} with b7
 have b4:G0.edgeSet.ncard+1=m:=by rw[←hm];exact fG G l p c
 have N:G0.IsAcyclic:=M.anti (deleteEdges_le _);have B:∀i j,G0.Adj i j→i∉A:=fun i j h=>o i j ((deleteEdges_adj).1 h).1
 have a8:∀e∈({s(l,p)}:Set (Sym2 (Fin (r+1)))),p∈e:=by intro e w;rw[Set.mem_singleton_iff] at w;subst w;exact Sym2.mem_mk_right _ _
 have f:(fun x=>F G A (Function.update x l false))=F G0 A:=funext (iV G A l p R C);rcases a0 with⟨q,hq⟩|⟨l',Q,z,S⟩
 ·set G1:=G.deleteEdges {s(p,l),s(p,q)} with a7
  by_cases V:A.Nonempty∨∃i j,G0.Adj i j
  ·have U:(fun x=>F G A (Function.update x l true))=F G1 (insert p A):=
    funext (kT G A l p q R c C hq)
   have b5:∀b:Bool,∃x y:Fin (r+1)→Bool,
     F G A (Function.update x l b)≠F G A (Function.update y l b):=by
    intro b
    cases b
    ·obtain⟨x,y,v⟩:=aBy G0 A V;refine⟨x,y,?_⟩;have H:=congrFun f x;have J:=congrFun f y;rw[H,J];exact v
    ·obtain⟨x,y,v⟩:=aBy G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _));refine⟨x,y,?_⟩;have H:=congrFun U x;have J:=congrFun U y;rw[H,J];exact v
   obtain⟨b,s',b9,d⟩:=dG r (F G A) l s g b5 X
   cases b
   ·rw[f] at d;have u:∀T,yX G0 T→k-1≤T.card:=fun T hT=>by
     have:=O _ (lK G _ p a8 T hT);have:=Finset.card_insert_le p T;omega
    have:=ih G0.edgeSet.ncard (by omega) _ G0 A (k-1) s' rfl N B u V d;omega
   ·rw[U] at d;have a9:∀e∈({s(p,l),s(p,q)}:Set (Sym2 (Fin (r+1)))),p∈e:=by
     intro e w;rcases w with rfl|w
     ·exact Sym2.mem_mk_left _ _
     ·rw[Set.mem_singleton_iff] at w;subst w;exact Sym2.mem_mk_left _ _
    have P:∀T,yX G1 T→k-1≤T.card:=fun T hT=>by have:=O _ (lK G _ p a9 T hT);have:=Finset.card_insert_le p T;omega
    have a4:G1.IsAcyclic:=M.anti (deleteEdges_le _);have a2:∀i j,G1.Adj i j→i∉insert p A:=by
     intro i j h t;rcases Finset.mem_insert.1 t with b2|t
     ·exact xO G l p q hq i j h b2
     ·exact o i j ((deleteEdges_adj).1 h).1 t
    obtain⟨b0,b1⟩:=pD G l p q c;rw[←a7] at b0 b1;have:=ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k-1) s' rfl a4 a2
     P (Or.inl (Finset.insert_nonempty _ _)) d
    rw[Finset.card_insert_of_notMem a3] at this;omega
  ·push Not at V
   obtain⟨a6,K⟩:=V;have b8:m=1:=by have:=hM G0 K;omega
   have P:k≤({p}:Finset (Fin (r+1))).card:=by
    apply O;intro i j b3;have h1:=K i j;rw[deleteEdges_adj] at h1
    push Not at h1
    have h2:=h1 b3;rw[Set.mem_singleton_iff,Sym2.eq_iff] at h2;rcases h2 with⟨_,rfl⟩|⟨rfl,_⟩
    ·exact Or.inr (Finset.mem_singleton_self _)
    ·exact Or.inl (Finset.mem_singleton_self _)
   rw[Finset.card_singleton] at P;subst a6;simp only[Finset.card_empty];omega
 ·obtain⟨s0,rfl⟩:∃s0,s=s0+1:=⟨s-1,by omega⟩
  have E:G0.Adj p l':=(deleteEdges_adj).2 ⟨z,by simp[Q,z.ne.symm]⟩;have a5:∃x y:Fin (r+1)→Bool,
    F G A (Function.update x l false)≠F G A (Function.update y l false):=by
   obtain⟨x,y,v⟩:=aBy G0 A (Or.inr ⟨p,l',E⟩);refine⟨x,y,?_⟩;have H:=congrFun f x;have J:=congrFun f y;rw[H,J];exact v
  have d:=eI r (F G A) l false s0 g a5 X;rw[f] at d;have u:∀T,yX G0 T→k≤T.card:=tR G l p l' k Q z S O;have:=ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl N B u
   (Or.inr ⟨p,l',E⟩) d
  omega
lemma sC
  (n t s:ℕ) (K:SimpleGraph (Fin n)) [DecidableRel K.Adj] (A:Finset (Fin n))
  (d:K.IsAcyclic)
  (h:∀a∈A,∀v:Fin n,¬K.Adj a v)
  (b:A.Nonempty∨∃u v:Fin n,K.Adj u v)
  (e:∀S:Finset (Fin n),K.IsVertexCover (S:Set (Fin n))→t≤S.card)
  (c:dO n (fun x:Fin n→Bool=>
    decide ((∃a∈A,x a=true)∨∃u v:Fin n,K.Adj u v∧x u=true∧x v=true)) s):
  A.card+K.edgeFinset.card+t≤ s+1:=by
 have j:(fun x:Fin n→Bool=>
   decide ((∃a∈A,x a=true)∨∃u v:Fin n,K.Adj u v∧x u=true∧x v=true))=
   F K A:=by
  funext x;rw[Bool.eq_iff_iff,decide_eq_true_iff,hK]
 rw[j] at c;have g:K.edgeFinset.card=K.edgeSet.ncard:=by rw[←Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset]
 rw[g];exact iQ dO eI dG cD
  _ _ K A t s rfl d (fun u v f k=>h u k v f)
  (fun S i=>e S (fun _ _ f=>i _ _ f)) b c
end
end As
namespace As
lemma eV
  (n t s:ℕ) (K:SimpleGraph (Fin n)) [DecidableRel K.Adj] (A:Finset (Fin n))
  (c:K.IsAcyclic)
  (f:∀a∈A,∀v:Fin n,¬K.Adj a v)
  (b:A.Nonempty∨∃u v:Fin n,K.Adj u v)
  (d:∀S:Finset (Fin n),K.IsVertexCover (S:Set (Fin n))→t≤S.card)
  (e:dO n (fun x:Fin n→Bool=>
    decide ((∃a∈A,x a=true)∨∃u v:Fin n,K.Adj u v∧x u=true∧x v=true)) s):
  A.card+K.edgeFinset.card+t≤ s+1:=
 sC dO eI dG cD
  n t s K A c f b d e
end As
namespace Ap
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity As
def iI (g:Gate):Bool:=
 match g.op with
 | .not=>true
 | _=>false
@[simp] lemma isNot_iff (g : Gate) : iI g = true ↔ g.op = .not := by
 rcases g with⟨op,a⟩
 cases op<;>simp[iI]
def eJ (C:Circuit):ℕ:=C.gates.countP (fun g=> !iI g)
lemma fH (C:Circuit):
  C.size=eJ C+C.gates.countP iI:=by
 simpa[Circuit.size,eJ] using(List.length_eq_countP_add_countP (fun g=> !iI g) (l:=C.gates))
lemma nC {α:Type} {P:α→Prop} {w:List α} {d:α}
  (b:∀u∈w,P u) (a:P d) (i:ℕ):P (w.getD i d):=by
 rw[List.getD_eq_getElem?_getD]
 cases h:w[i]? with
 | none=>exact a
 | some u=>exact b u (List.mem_of_getElem? h)
def cB {n} (w:List (Fn n)) (i:ℕ):Fn n:=w.getD i (fun _=>false)
def yY {n} (w:List (Fn n)) (a:List ℕ) (j:ℕ) (d:Bool):Fn n:=(a.map (cB w)).getD j (fun _=>d)
lemma iW {n} {w:List (Fn n)} {P:Fn n→Prop}
  (a:gY P) (c:∀u∈w,P u) (e:List ℕ) (j:ℕ) (d:Bool):
  P (yY w e j d):=by
 apply nC _ (a.1 d);intro u b;obtain⟨i,-,rfl⟩:=List.mem_map.mp b;exact nC c (a.1 false) i
def eX {n} (w:List (Fn n)) (g:Gate):Fn n:=fun x=>g.op.eval (g.inputs.map (fun i=>cB w i x))
lemma tS {n} (w:List (Fn n)) (a:List ℕ) (b:a.length≤2):
  eX w ⟨.and,a⟩=eP (yY w a 0 true) (yY w a 1 true):=by
 funext x;rcases a with _|⟨i,_|⟨j,_|⟨k,a⟩⟩⟩
 ·rfl
 ·simp[eX,GateOp.eval,eP,yY]
 ·simp[eX,GateOp.eval,eP,yY]
 ·simp at b
lemma vL {n} (w:List (Fn n)) (a:List ℕ) (b:a.length≤2):
  eX w ⟨.or,a⟩=nT (eP (nT (yY w a 0 false)) (nT (yY w a 1 false))):=by
 funext x;rcases a with _|⟨i,_|⟨j,_|⟨k,a⟩⟩⟩
 ·rfl
 ·simp[eX,GateOp.eval,eP,nT,yY]
 ·simp[eX,GateOp.eval,eP,nT,yY]
 ·simp at b
lemma tT {n} (w:List (Fn n)) (a:List ℕ):
  eX w ⟨.not,a⟩=nT (yY w a 0 false):=by
 funext x
 cases a<;>rfl
def step (w:List Bool) (g:Gate):List Bool:=w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma tU {n} (w:List (Fn n)) (g:Gate) (x:Fin n→Bool):
  step (w.map fun u=>u x) g=(w++[eX w g]).map fun u=>u x:=by
 simp only[step,List.map_append,List.map_cons,List.map_nil,eX];congr 3;apply List.map_congr_left;intro i _;exact List.getD_map w (fun _=>false) (fun u:Fn n=>u x)
lemma iX {n} {w:List (Fn n)} {P:Fn n→Prop} {u:Fn n}
  (b:∀v∈w,P v) (c:P u):∀v∈w++[u],P v:=by
 intro v a;rcases List.mem_append.mp a with h|h
 ·exact b v h
 ·rwa [List.mem_singleton.mp h]
lemma vM {n} (gs:List Gate) (out:ℕ)
  (i:FanInTwo (⟨gs,out⟩:Circuit)) (w:List (Fn n)) (P:Fn n→Prop)
  (a:gY P) (b:∀u∈w,P u):
  Build P (fun x=>(gs.foldl step (w.map fun u=>u x)).getD out false) (gs.countP (fun g=> !iI g)):=by
 induction gs generalizing w P with
 | nil=>
   apply Build.oN;change P (fun x=>(w.map fun u=>u x).getD out false);have h:(fun x:Fin n→Bool=>(w.map fun u=>u x).getD out false)=cB w out:=by funext x;exact List.getD_map w (fun _=>false) (fun u:Fn n=>u x)
   rw[h];exact nC b (a.1 false) out
 | cons g gs ih=>
   have ht:FanInTwo (⟨gs,out⟩:Circuit):=fun g h=>i g (List.mem_cons_of_mem _ h)
   obtain⟨e,d⟩:=i g List.mem_cons_self;simp only[List.foldl_cons,tU,List.countP_cons];rcases g with⟨op,c⟩
   change op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) at e;change c.length≤2 at d
   cases op with
   | and=>
     simp only[iI,Bool.not_false,↓reduceIte,tS w c d];refine Build.mF (iW a b c 0 true) (iW a b c 1 true)
      (ih ht _ _ (gZ a _) (iX (fun v f=>Or.inl (b v f)) ?_))
     exact Or.inr (Or.inl rfl)
   | or=>
     simp only[iI,Bool.not_false,↓reduceIte,vL w c d];refine Build.mF (a.2 _ (iW a b c 0 false)) (a.2 _ (iW a b c 1 false))
      (ih ht _ _ (gZ a _) (iX (fun v f=>Or.inl (b v f)) ?_))
     exact Or.inr (Or.inr rfl)
   | not=>
     simpa only[iI,Bool.not_true,Bool.false_eq_true,↓reduceIte,Nat.add_zero,
      tT] using
      ih ht (w++[nT (yY w c 0 false)]) P a
       (iX b (a.2 _ (iW a b c 0 false)))
   | mod m=>simp at e
   | maj=>simp at e
lemma pE (n:ℕ) (C:Circuit) (h:FanInTwo C):
  dO n (circuitFun n C) (eJ C):=by
 let w:List (Fn n):=List.ofFn (fun i:Fin n=>fun x=>x i)
 have b:∀u∈w,iT n u:=by intro u a;obtain⟨i,rfl⟩:=List.mem_ofFn.mp a;exact Or.inr ⟨i,Or.inl rfl⟩
 change Build (iT n) (fun x=>(C.gates.foldl step (List.ofFn x)).getD C.output false) (C.gates.countP (fun g=> !iI g));simpa only[w,List.map_ofFn,Function.comp_def] using vM C.gates C.output h w (iT n) (iU n) b
end Ap
namespace PEqualNP.MetaComplexity.NestedCover.An
open PEqualNP.CircuitLowerBounds
open scoped BigOperators
lemma pF (W:Finset ℕ) (b:List ℕ)
  (d:∀w∈b,w∈W):
  (∑w∈W,b.count w)=b.length:=by
 induction b with
 | nil=>simp
 | cons a b ih=>
   have e:a∈W:=d a (by simp);have ht:∀w∈b,w∈W:=fun w c=>d w (by simp[c])
   calc
    (∑w∈W,(a::b).count w)=
        (∑w∈W,b.count w)+∑w∈W,(if w=a then 1 else 0):=by
      rw[←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro w _;by_cases c:w=a
      ·subst w;simp
      ·simp[c,Ne.symm c]
    _=(a::b).length:=by rw[ih ht];simp[e]
lemma gN {n C G L ρ} (h:IsOrTree n C G L ρ):G.card+1=L.card:=by
 rcases h with⟨q,hl,hr,a⟩
 by_cases m:G= ∅
 ·simp only[m,ite_true] at a;simp[m,a]
 ·let W:=L∪G.image (fun j=>n+j)
  have b:ρ∈W:=by rw[ite_eq_right m] at a;obtain⟨j,d,rfl⟩:=a;exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ d)
  have g:Disjoint L (G.image (fun j=>n+j)):=by refine Finset.disjoint_left.mpr ?_;intro w c r;obtain⟨j,d,rfl⟩:=Finset.mem_image.mp r;exact(hl _ c).1 ⟨Nat.le_add_right n j,by simpa using d⟩
  have f:W.card=L.card+G.card:=by
   exact(Finset.card_union_of_disjoint g).trans
    (congrArg (L.card+ ·) (Finset.card_image_of_injective _ (fun _ _ h=>Nat.add_left_cancel h)))
  have e:∀w∈W,readsIn C G w=if w=ρ then 0 else 1:=by
   intro w c;rcases Finset.mem_union.mp c with c|c
   ·exact(hl _ c).2
   ·obtain⟨j,d,rfl⟩:=Finset.mem_image.mp c;exact hr j d
  have l:(∑w∈W,readsIn C G w)+1=W.card:=by
   have s:readsIn C G ρ=0:=by simp[e ρ b]
   rw[←Finset.sum_erase_add _ _ b,s,add_zero];have hs:(∑w∈W.erase ρ,readsIn C G w)=(W.erase ρ).card:=by
    calc
     (∑w∈W.erase ρ,readsIn C G w)=∑v∈W.erase ρ,1:=by
       apply Finset.sum_congr rfl;intro w c;rw[e w (Finset.mem_of_mem_erase c),ite_eq_right (Finset.ne_of_mem_erase c)]
     _=(W.erase ρ).card:=by simp
   rw[hs];exact Finset.card_erase_add_one b
  have k:(∑w∈W,readsIn C G w)=G.card*2:=by
   unfold readsIn;rw[Finset.sum_comm]
   calc
    (∑j∈G,∑w∈W,(gateAt C j).inputs.count w)=∑u∈G,2:=by
      apply Finset.sum_congr rfl;intro j d;rw[pF,(q j d).2.1];intro i o;rcases (q j d).2.2 i o with o|⟨t,p⟩
      ·exact Finset.mem_union_left _ o
      ·exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i-n,p,by omega⟩)
    _=G.card*2:=by simp
  rw[k,f] at l;omega
end PEqualNP.MetaComplexity.NestedCover.An
namespace PEqualNP.MetaComplexity.NestedCover.An
open PEqualNP.CircuitLowerBounds
open scoped BigOperators
lemma xP {n:ℕ} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {d:NCCData n} (h:OwnerOK K d):
  (∑t∈d.cover,(Finset.univ.filter (fun r=>d.owns t r=true)).card)=
    K.edgeFinset.card:=by
 rw[←Finset.card_sigma];have a (t r:Fin n):
   (⟨t,r⟩:Σ _:Fin n,Fin n)∈
      d.cover.sigma (fun u=>Finset.univ.filter (fun v=>d.owns u v=true))↔
     t∈d.cover∧d.owns t r=true:=by
  simp[Finset.mem_sigma]
 refine Finset.card_bij (fun p _=>s(p.1,p.2)) ?_ ?_ ?_
 ·intro⟨t,r⟩ c;apply SimpleGraph.mem_edgeFinset.mpr;exact(h.1 t r ((a t r).mp c).2).1
 ·intro⟨t,r⟩ c ⟨u,v⟩ g b;rcases Sym2.eq_iff.mp b with⟨rfl,rfl⟩|⟨rfl,rfl⟩
  ·rfl
  ·have ht:=((a t r).mp c).2;have hr:=((a r t).mp g).2;exact(h.2 t r (h.1 t r ht).1 (ht.trans hr.symm)).elim
 ·intro e
  induction e using Sym2.ind with
  | _ t r=>
    intro b;have f:K.Adj t r:=SimpleGraph.mem_edgeFinset.mp b;by_cases ht:d.owns t r=true
    ·exact⟨⟨t,r⟩,(a t r).mpr ⟨(h.1 t r ht).2,ht⟩,rfl⟩
    ·have hr:d.owns r t=true:=by
      have i:=h.2 t r f
      cases htr:d.owns t r<;>cases hrt:d.owns r t<;>simp_all
     exact⟨⟨r,t⟩,(a r t).mpr ⟨(h.1 r t hr).2,hr⟩,Sym2.eq_swap⟩
end PEqualNP.MetaComplexity.NestedCover.An
namespace PEqualNP.MetaComplexity.NestedCover.An
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit} {d : NCCData n}
lemma pG (h:Valid n K A C d) {s:Fin n} (hs:s∈d.cover):TermOK n C d s:=(h.2.2.2.2.2.1 s hs).1
lemma aBs (h:Valid n K A C d) {s:Fin n} (hs:s∈d.cover):
  n≤d.bw s:=by
 obtain⟨j,_,e,_⟩:=pG h hs;omega
lemma yZ (h:Valid n K A C d):Set.InjOn d.bw (↑d.cover):=by
 intro s hs t ht e;obtain⟨j,_,f,b,_⟩:=pG h hs;obtain⟨i,_,c,a,_⟩:=pG h ht;obtain rfl:i=j:=by omega
 exact Fin.ext (congrArg Prod.snd (b.symm.trans a))
lemma aBz (h:Valid n K A C d) (t:Fin n):
  (zLeaves d t).card=(d.cover.filter (fun s=>d.tie s=some t)).card+1:=by
 unfold zLeaves;rw[Finset.card_insert_of_notMem,Finset.card_image_of_injOn]
 ·exact(yZ h).mono (Finset.filter_subset _ _)
 ·intro a;obtain⟨s,hs,e⟩:=Finset.mem_image.mp a;have:=aBs h (Finset.mem_filter.mp hs).1;have:=t.isLt;omega
lemma zA (h:Valid n K A C d):
  (topLeaves d A).card=A.card+(d.cover.filter (fun t=>d.tie t=none)).card:=by
 unfold topLeaves;rw[Finset.card_union_of_disjoint,Finset.card_image_of_injective _ Fin.val_injective,Finset.card_image_of_injOn]
 ·exact(yZ h).mono (Finset.filter_subset _ _)
 ·apply Finset.disjoint_left.mpr;intro x b c;obtain⟨a,_,rfl⟩:=Finset.mem_image.mp b;obtain⟨s,hs,e⟩:=Finset.mem_image.mp c;have:=aBs h (Finset.mem_filter.mp hs).1;have:=a.isLt;omega
lemma rJ {t r:Fin n} (h:LamOK n C d t r):
  d.lam t r=r.val∨∃j,d.lam t r=n+j∧d.role j=(Kind.z,r.val):=by
 unfold LamOK at h
 split at h
 ·obtain a|⟨j,_,e,b⟩:=h.2.1
  ·exact Or.inl a
  ·exact Or.inr ⟨j,e,b⟩
 ·exact Or.inl h
lemma aB0 (h:Valid n K A C d) {t:Fin n} (ht:t∈d.cover):
  (oLeaves d t).card=(Finset.univ.filter (fun r=>d.owns t r=true)).card:=by
 apply Finset.card_image_of_injOn;intro r hr s hs e;have hl:=(h.2.2.2.2.2.1 t ht).2.2.2;obtain a|⟨i,g,c⟩:=rJ (hl r (Finset.mem_filter.mp hr).2)
 all_goals obtain b|⟨j,k,f⟩:=rJ (hl s (Finset.mem_filter.mp hs).2)
 ·exact Fin.ext (a.symm.trans (e.trans b))
 ·have:=r.isLt;omega
 ·have:=s.isLt;omega
 ·obtain rfl:i=j:=by omega
  exact Fin.ext (congrArg Prod.snd (c.symm.trans f))
lemma zB (h:Valid n K A C d):
  (d.cover.filter (fun s=>d.tie s=none)).card+
    (∑t∈d.cover,(d.cover.filter (fun s=>d.tie s=some t)).card)=d.cover.card:=by
 classical
 let U:=insert none (d.cover.image some)
 have b:(↑d.cover:Set (Fin n)).MapsTo d.tie (↑U):=by
  intro s hs;change d.tie s∈insert none (d.cover.image some)
  cases he:d.tie s with
  | none=>simp
  | some t=>
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (h.2.2.1.1 _ _ (h.2.2.2.1 _ _ he).2).2)
 have a:=Finset.card_eq_sum_card_fiberwise b;dsimp[U] at a;rw[Finset.sum_insert (by simp),Finset.sum_image] at a
 ·exact a.symm
 ·exact Option.some_injective _ |>.injOn
end PEqualNP.MetaComplexity.NestedCover.An
namespace PEqualNP.MetaComplexity.NestedCover.An
open PEqualNP.CircuitLowerBounds
open scoped BigOperators
lemma bF {n:ℕ} {d:NCCData n} {C:Circuit}
  {k:Kind} {v j:ℕ}:
  j∈gatesOf d C k v↔j<C.gates.length∧d.role j=(k,v):=by
 simp[gatesOf]
lemma eY {n:ℕ} {d:NCCData n} {C:Circuit} {j:ℕ}:
  j∈topGates d C↔j<C.gates.length∧(d.role j).1=Kind.top:=by
 simp[topGates]
lemma gO {n K A C d} (h:Valid n K A C d) {t}
  (ht:t∈d.cover):
  ∃
   j∈gatesOf d C Kind.b t.val,gatesOf d C Kind.b t.val={j}∧
   (gateAt C j).op=GateOp.and∧(gateAt C j).inputs.length=2:=by
 obtain⟨j,p,r,f,o,l⟩:=(h.2.2.2.2.2.1 t ht).1;have m:=bF.mpr ⟨p,f⟩;refine⟨j,m,?_,o,?_⟩
 ·ext i;refine⟨fun a=> ?_,fun a=>by simpa only[Finset.mem_singleton.mp a] using m⟩;obtain⟨k,c⟩:=bF.mp a;rcases h.2.2.2.2.1 i k with e|⟨u,_,q,g⟩
  ·simp[c] at e
  ·have v:u=t:=Fin.ext (by simpa[c] using q.symm);subst u;have s:=g (by simp[c]);exact Finset.mem_singleton.mpr (by omega)
 ·rcases l with a|a<;>simp[a]
lemma eW {n K A C d} (h:Valid n K A C d)
  {j:ℕ} (c:j<C.gates.length):
  j
   ∈topGates d C∨∃t∈d.cover,
   j
    ∈gatesOf d C Kind.z t.val∨j∈gatesOf d C Kind.o t.val∨
    j∈gatesOf d C Kind.b t.val:=by
 rcases h.2.2.2.2.1 j c with e|⟨t,ht,f,_⟩
 ·exact Or.inl (eY.mpr ⟨c,e⟩)
 ·have hr (k:Kind) (a:(d.role j).1=k):
    j∈gatesOf d C k t.val:=
   bF.mpr ⟨c,Prod.ext a f⟩
  cases a:(d.role j).1 with
  | z=>exact Or.inr ⟨t,ht,Or.inl (hr _ a)⟩
  | o=>exact Or.inr ⟨t,ht,Or.inr (Or.inl (hr _ a))⟩
  | b=>exact Or.inr ⟨t,ht,Or.inr (Or.inr (hr _ a))⟩
  | top=>exact Or.inl (eY.mpr ⟨c,a⟩)
lemma zC {n K A C d} (h:Valid n K A C d):
  C.size=(topGates d C).card+(∑t∈d.cover,(gatesOf d C Kind.z t.val).card)+(∑t∈d.cover,(gatesOf d C Kind.o t.val).card)+d.cover.card:=by
 let G (k:Kind):=d.cover.biUnion (fun t=>gatesOf d C k t.val)
 have c {k j}:j∈G k↔∃t∈d.cover,j∈gatesOf d C k t.val:=Finset.mem_biUnion;have a {k j} (g:j∈G k):
   j<C.gates.length∧(d.role j).1=k:=by
  obtain⟨t,_,ht⟩:=c.mp g;exact⟨(bF.mp ht).1,congrArg Prod.fst (bF.mp ht).2⟩
 have e (k:Kind):(G k).card=∑t∈d.cover,(gatesOf d C k t.val).card:=by apply Finset.card_biUnion;intro t _ u _ y;apply Finset.disjoint_left.mpr;intro j ht H;exact y (Fin.ext (by have F:=(bF.mp ht).2.symm.trans (bF.mp H).2;exact congrArg Prod.snd F))
 have E:(G Kind.b).card=d.cover.card:=by
  rw[e]
  calc
   _
    =∑J∈d.cover,1:=by
    apply Finset.sum_congr rfl;intro t ht;obtain⟨_,_,hs,_,_⟩:=gO h ht;simp[hs]
   _=_:=by simp
 have m:Finset.range C.gates.length=
   topGates d C∪G Kind.z∪G Kind.o∪G Kind.b:=by
  ext j;simp only[Finset.mem_range,Finset.mem_union];constructor
  ·intro g;rcases eW h g with ht|⟨t,ht,s|r|p⟩
   ·exact Or.inl (Or.inl (Or.inl ht))
   ·exact Or.inl (Or.inl (Or.inr (c.mpr ⟨t,ht,s⟩)))
   ·exact Or.inl (Or.inr (c.mpr ⟨t,ht,r⟩))
   ·exact Or.inr (c.mpr ⟨t,ht,p⟩)
  ·rintro(((ht|s)|r)|p)
   ·exact(eY.mp ht).1
   ·exact(a s).1
   ·exact(a r).1
   ·exact(a p).1
 have i {k} (q:Kind.top≠k):Disjoint (topGates d C) (G k):=by apply Finset.disjoint_left.mpr;intro j ht g;exact q ((eY.mp ht).2.symm.trans (a g).2)
 have f {k l} (v:k≠l):Disjoint (G k) (G l):=by apply Finset.disjoint_left.mpr;intro j q hl;exact v ((a q).2.symm.trans (a hl).2)
 have B:Disjoint (topGates d C) (G Kind.z):=i (by decide);have x:Disjoint (topGates d C∪G Kind.z) (G Kind.o):=Finset.disjoint_union_left.mpr ⟨i (by decide),f (by decide)⟩;have w:Disjoint (topGates d C∪G Kind.z∪G Kind.o) (G Kind.b):=
  Finset.disjoint_union_left.mpr
   ⟨Finset.disjoint_union_left.mpr ⟨i (by decide),f (by decide)⟩,f (by decide)⟩
 rw[Circuit.size,←Finset.card_range C.gates.length,m,Finset.card_union_of_disjoint w,Finset.card_union_of_disjoint x,Finset.card_union_of_disjoint B,E,e,e]
lemma pH {n K A C d} (h:Valid n K A C d):FanInTwo C:=by
 intro g m;obtain⟨j,k,rfl⟩:=List.mem_iff_getElem.mp m;rw[←List.getD_eq_getElem _ _ k];change(gateAt C j).op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)∧(gateAt C j).inputs.length≤2;have a (c:(gateAt C j).op=GateOp.or) (hl:(gateAt C j).inputs.length=2):
  (gateAt C j).op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)∧
    (gateAt C j).inputs.length≤2:=by simp[c,hl]
 rcases eW h k with f|⟨t,ht,o|c|l⟩
 ·obtain⟨b,hl,_⟩:=h.2.2.2.2.2.2.1 j f;exact a b hl
 ·obtain⟨b,hl,_⟩:=(h.2.2.2.2.2.1 t ht).2.1.1 j o;exact a b hl
 ·obtain⟨b,hl,_⟩:=(h.2.2.2.2.2.1 t ht).2.2.1.1 j c;exact a b hl
 ·obtain⟨i,_,hs,b,hl⟩:=gO h ht;have e:j=i:=Finset.mem_singleton.mp (hs▸l);simp[e,b,hl]
end PEqualNP.MetaComplexity.NestedCover.An
namespace PEqualNP.MetaComplexity.NestedCover.An
open PEqualNP.CircuitLowerBounds
lemma vN {n:ℕ} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {A:Finset (Fin n)} {C:Circuit} {d:NCCData n} (h:Valid n K A C d):
  C.size+1=A.card+K.edgeFinset.card+d.cover.card:=by
 have f:(∑t∈d.cover,(gatesOf d C Kind.z t.val).card)=
   ∑t∈d.cover,(d.cover.filter (fun s=>d.tie s=some t)).card:=by
  apply Finset.sum_congr rfl;intro t ht;have a:=gN (h.2.2.2.2.2.1 t ht).2.1;rw[aBz h t] at a;omega
 have c:(∑t∈d.cover,(gatesOf d C Kind.o t.val).card)+d.cover.card=
   K.edgeFinset.card:=by
  rw[←xP h.2.2.1]
  calc
   _
    =∑t∈d.cover,((gatesOf d C Kind.o t.val).card+1):=by
    rw[Finset.sum_add_distrib];simp
   _
    =_:=by
    apply Finset.sum_congr rfl;intro t ht;exact(gN (h.2.2.2.2.2.1 t ht).2.2.1).trans (aB0 h ht)
 have ht:=(gN h.2.2.2.2.2.2).trans (zA h);have b:=zB h;have e:=zC h;omega
end PEqualNP.MetaComplexity.NestedCover.An
namespace Aq
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
lemma lL {n} (K:SimpleGraph (Fin n)) [DecidableRel K.Adj]
  (A:Finset (Fin n)):
  graphFun K A=fun x=>decide ((∃a∈A,x a=true)∨∃u v:Fin n,K.Adj u v∧x u=true∧x v=true):=by
 funext x;simp[graphFun]
lemma nD {n} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {A T:Finset (Fin n)} {D:Circuit} (b:K.IsAcyclic)
  (e:∀a∈A,∀v:Fin n,¬K.Adj a v)
  (f:A.Nonempty∨∃u v,K.Adj u v) (ht:IsMinCover K T)
  (c:FanInTwo D) (d:circuitFun n D =graphFun K A):
  A.card+K.edgeFinset.card+T.card≤Ap.eJ D +1:=by
 have hs:=Ap.pE n D c;rw[d,lL] at hs;exact As.eV n _ _ K A b e f ht.2 hs
lemma iR {n} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {A:Finset (Fin n)} {C:Circuit} {d:NCCData n} (b:K.IsAcyclic)
  (g:∀a∈A,∀v:Fin n,¬K.Adj a v)
  (i:A.Nonempty∨∃u v,K.Adj u v) (h:Valid n K A C d)
  (f:circuitFun n C=graphFun K A):IsMinimalCircuit n C:=by
 refine⟨An.pH h,?_⟩;intro D e c;have j:=nD b g i h.2.1 e (c.trans f);have size:=An.vN h;have k:=Ap.fH D;omega
end Aq
namespace PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
lemma vO (b:IsOrTree n C G L ρ) {w:ℕ}
  (f:w∈L∨∃j∈G,w=n+j) (a:w≠ρ):
  ∃j∈G,w∈(gateAt C j).inputs:=by
 have g:readsIn C G w=1:=by
  rcases f with e|⟨j,c,rfl⟩
  ·simpa[a] using(b.2.1 w e).2
  ·simpa[a] using b.2.2.1 j c
 by_contra d
 push Not at d
 have h:readsIn C G w=0:=Finset.sum_eq_zero (fun j c=>List.count_eq_zero_of_not_mem (d j c));omega
lemma pI (p:IsOrTree n C G L ρ)
  (d:ReadsBack n C) (q:∀j∈G,j<C.gates.length)
  (P:ℕ→Prop)
  (e:∀j∈G,∀w∈(gateAt C j).inputs,P w→P (n+j))
  {i:ℕ} (r:i∈L∨∃j∈G,i=n+j) (k:P i):P ρ:=by
 classical
 let S:=(L∪G.image (fun j=>n+j)).filter P
 have a (w:ℕ):w∈S↔(w∈L∨∃j∈G,w=n+j)∧P w:=by simp only[S,Finset.mem_filter,Finset.mem_union,Finset.mem_image,eq_comm]
 have l:S.Nonempty:=⟨i,(a i).2 ⟨r,k⟩⟩
 let m:=S.max' l
 have s:m∈S:=S.max'_mem l;obtain⟨c,f⟩:=(a m).1 s;by_cases g:m=ρ
 ·simpa[g] using f
 ·obtain⟨j,h,b⟩:=vO p c g;have o:n+j∈S:=(a (n+j)).2
   ⟨Or.inr ⟨j,h,rfl⟩,e j h m b f⟩
  exact False.elim ((not_lt_of_ge (S.le_max' _ o)) (d j (q j h) m b))
lemma tV (o:IsOrTree n C G L ρ)
  (c:ReadsBack n C) (p:∀j∈G,j<C.gates.length)
  (P:ℕ→Prop)
  (m:∀j∈G,P (n+j)↔∃i∈(gateAt C j).inputs,P i):
  ∀j∈G,P (n+j)→∃i∈L,P i∧i≤n+j:=by
 intro j
 induction j using Nat.strong_induction_on with
 | ind j ih=>
   intro d f;obtain⟨i,a,e⟩:=(m j d).1 f;have l:=c j (p j d) i a;rcases (o.1 j d).2.2 i a with q|⟨s,k⟩
   ·exact⟨i,q,e,l.le⟩
   ·have h:n+(i-n)=i:=by omega
    have b:P (n+(i-n)):=by rwa [h]
    obtain⟨w,r,g,t⟩:=ih (i-n) (by omega) k b;exact⟨w,r,g,by omega⟩
lemma fI (c:IsOrTree n C G L ρ)
  (b:ReadsBack n C) (k:∀j∈G,j<C.gates.length)
  (P:ℕ→Prop)
  (f:∀j∈G,P (n+j)↔∃i∈(gateAt C j).inputs,P i):
  P ρ↔∃i∈L,P i:=by
 constructor
 ·intro l;by_cases a:G= ∅
  ·have o:L={ρ}:=by simpa[a] using c.2.2.2
   exact⟨ρ,by simp[o],l⟩
  ·have e:∃j∈G,ρ=n+j:=by simpa[a] using c.2.2.2
   obtain⟨j,h,rfl⟩:=e;obtain⟨i,g,d,_⟩:=tV c b k P f j h l;exact⟨i,g,d⟩
 ·rintro⟨i,g,d⟩;exact pI c b k P
   (fun j h w p m=>(f j h).2 ⟨w,p,m⟩) (Or.inl g) d
lemma lM (d:IsOrTree n C G L ρ)
  (a:ReadsBack n C) (b:∀j∈G,j<C.gates.length):
  ∀i∈L,i≤ρ:=by
 intro i e;exact pI d a b (i≤ ·)
  (fun j f w g c=>c.trans (a j (b j f) w g).le) (Or.inl e) le_rfl
end PEqualNP.MetaComplexity.NestedCover
namespace PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitLowerBounds
def W {n:ℕ} (C:Circuit) (x:Fin n→Bool) (i:ℕ):Prop:=(C.wires (List.ofFn x)).getD i false=true
def aP (f:List Bool→Gate→Bool) (w:List Bool) (g:Gate):
  List Bool:=
 w++[f w g]
lemma kJ (f:List Bool→Gate→Bool) (gs:List Gate)
  (w:List Bool):(gs.foldl (aP f) w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil=>simp
 | cons g gs ih=>
   simp[ih,aP];omega
lemma dH (f:List Bool→Gate→Bool) (gs:List Gate)
  (w:List Bool) (i:ℕ) (a:i<w.length):
  (gs.foldl (aP f) w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
   rw[List.foldl_cons,ih _ (by simp[aP];omega)];exact List.getD_append _ _ _ _ a
lemma fJ {n:ℕ} (f:List Bool→Gate→Bool)
  (gs:List Gate) (x:Fin n→Bool) (t:Fin n):
  (gs.foldl (aP f) (List.ofFn x)).getD t.val false=x t:=by
 have ht:t.val<(List.ofFn x).length:=by simp
 rw[dH _ _ _ _ ht,List.getD_eq_getElem _ _ ht];simp
lemma gB {n:ℕ} {C:Circuit} {j:ℕ}
  (f:List Bool→Gate→Bool) (v:List Bool) (h:v.length=n)
  (g:j<C.gates.length):
  ∃
   w:List Bool,w.length=n+j∧
   (C.gates.foldl (aP f) v).getD (n+j) false=f w (gateAt C j)∧
   ∀i<n+j,w.getD i false=(C.gates.foldl (aP f) v).getD i false:=by
 let w:=(C.gates.take j).foldl (aP f) v
 let b:=C.gates.drop (j+1)
 have c:C.gates=C.gates.take j++C.gates[j]::b:=
  (List.take_append_drop j C.gates).symm.trans
    (congrArg (C.gates.take j++ ·) (List.drop_eq_getElem_cons (l:=C.gates) g))
 have e:w.length=n+j:=by simp[w,kJ,h,Nat.min_eq_left g.le]
 have d:gateAt C j=C.gates[j]:=List.getD_eq_getElem _ _ g;have a:C.gates.foldl (aP f) v=
   b.foldl (aP f) (aP f w C.gates[j]):=by
  conv_lhs=>rw[c]
  rw[List.foldl_append,List.foldl_cons]
 refine⟨w,e,?_,?_⟩
 ·rw[a,dH f b (aP f w C.gates[j]) (n+j)
   (by simp[aP,e]),d]
  unfold aP;rw[List.getD_append_right _ _ _ _ (by omega),e,Nat.sub_self];rfl
 ·intro i k;rw[a,dH f b (aP f w C.gates[j]) i
   (by simp[aP,e];omega)]
  exact(List.getD_append w [f w C.gates[j]] false i (by omega)).symm
lemma aC {n:ℕ} {C:Circuit} {x:Fin n→Bool} (t:Fin n):
  W C x t.val↔x t=true:=by
 have a:=fJ (fun w g=>g.op.eval (g.inputs.map fun i=>w.getD i false)) C.gates x t;change(C.wires (List.ofFn x)).getD t.val false=x t at a;unfold W;rw[a]
lemma aO {n:ℕ} {C:Circuit} {x:Fin n→Bool} {j:ℕ}
  (b:ReadsBack n C) (d:j<C.gates.length):
  (C.wires (List.ofFn x)).getD (n+j) false=
    (gateAt C j).op.eval ((gateAt C j).inputs.map
      fun i=>(C.wires (List.ofFn x)).getD i false):=by
 obtain⟨w,_,a,c⟩:=gB (n:=n) (fun w g=>g.op.eval (g.inputs.map fun i=>w.getD i false)) (List.ofFn x) (by simp) d;change(C.wires (List.ofFn x)).getD (n+j) false=(gateAt C j).op.eval ((gateAt C j).inputs.map fun i=>w.getD i false) at a;rw[a];congr 1;exact List.map_congr_left (fun i e=>c i (b j d i e))
lemma aY {n:ℕ} {C:Circuit} {x:Fin n→Bool} {j:ℕ}
  (a:ReadsBack n C) (c:j<C.gates.length) (b:(gateAt C j).op=GateOp.or):
  W C x (n+j)↔∃i∈(gateAt C j).inputs,W C x i:=by
 simp only[W,aO a c,b,GateOp.eval,List.any_map,Function.comp_def,id_eq,List.any_eq_true]
lemma bO {n:ℕ} {C:Circuit} {x:Fin n→Bool} {d:NCCData n}
  {t:Fin n} (b:ReadsBack n C) (ht:TermOK n C d t):
  W C x (d.bw t)↔W C x (d.zroot t)∧W C x (d.oroot t):=by
 obtain⟨j,f,e,_,c,a⟩:=ht;unfold W;rw[e,aO b f,c];rcases a with a|a<;>simp[a,GateOp.eval,and_comm]
lemma cL {n:ℕ} {C:Circuit} {x:Fin n→Bool}:
  circuitFun n C x=true↔W C x C.output:=
 Iff.rfl
lemma aG {n:ℕ} {C:Circuit} {d:NCCData n} (t:Fin n):
  IsCentred n C d t.val↔t∈d.cover:=by
 have a:=fJ (fun w g=>
  decide ((d.role (w.length-n)).1=Kind.z) && g.inputs.any (fun i=>w.getD i false))
  C.gates (fun i=>decide (i∈d.cover)) t
 change(centreFlags n C d).getD t.val false=decide (t∈d.cover) at a;unfold IsCentred;rw[a,decide_eq_true_eq]
lemma eK {n:ℕ} {C:Circuit} {d:NCCData n} {j:ℕ}
  (e:j<C.gates.length):
  ∃
   w:List Bool,
   (centreFlags n C d).getD (n+j) false=
     (decide ((d.role j).1=Kind.z) && (gateAt C j).inputs.any (fun i=>w.getD i false))∧
   ∀i<n+j,w.getD i false=(centreFlags n C d).getD i false:=by
 obtain⟨w,f,a,c⟩:=
  gB (n:=n) (fun w g=>
   decide ((d.role (w.length-n)).1=Kind.z) && g.inputs.any (fun i=>w.getD i false))
   (List.ofFn fun i:Fin n=>decide (i∈d.cover)) (by simp) e
 have b:w.length-n=j:=by omega
 rw[b] at a;exact⟨w,a,c⟩
lemma aR {n:ℕ} {C:Circuit} {d:NCCData n} {j:ℕ}
  (a:ReadsBack n C) (e:j<C.gates.length):
  IsCentred n C d (n+j)↔(d.role j).1=Kind.z∧
   ∃i∈(gateAt C j).inputs,IsCentred n C d i:=by
 obtain⟨w,h,c⟩:=eK (d:=d) e
 simp only[IsCentred,h,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true]
 constructor
 ·rintro⟨g,i,b,f⟩
  exact⟨g,i,b,(c i (a j e i b)).symm▸f⟩
 ·rintro⟨g,i,b,f⟩
  exact⟨g,i,b,(c i (a j e i b))▸f⟩
lemma cJ {n:ℕ} {C:Circuit} {d:NCCData n} {j:ℕ}
  (a:ReadsBack n C) (b:j<C.gates.length) (c:(d.role j).1=Kind.z):
  IsCentred n C d (n+j)↔∃i∈(gateAt C j).inputs,IsCentred n C d i:=by
 rw[aR a b,c,eq_self_iff_true,true_and]
lemma cM {n:ℕ} {C:Circuit} {d:NCCData n} {t:Fin n}
  (ht:TermOK n C d t):¬IsCentred n C d (d.bw t):=by
 obtain⟨j,c,b,a,_,_⟩:=ht;obtain⟨w,e,_⟩:=eK (d:=d) c;unfold IsCentred;rw[b,e,a];simp
end PEqualNP.MetaComplexity.NestedCover
namespace PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitLowerBounds
namespace A7
variable {n : ℕ} {C : Circuit} {d : NCCData n} {K : SimpleGraph (Fin n)}
    {A : Finset (Fin n)} {x : Fin n → Bool}
lemma cE (k:Kind) (t:ℕ):
  ∀j∈gatesOf d C k t,j<C.gates.length:=by
 intro j a;exact Finset.mem_range.mp (Finset.mem_filter.mp a).1
lemma iY:∀j∈topGates d C,j<C.gates.length:=by intro j a;exact Finset.mem_range.mp (Finset.mem_filter.mp a).1
lemma dF {t:Fin n} {i}:
  i∈zLeaves d t↔i=t.val∨∃s∈d.cover,d.tie s=some t∧d.bw s=i:=by
 simp[zLeaves,and_assoc]
lemma iZ {t:Fin n} {i}:
  i∈oLeaves d t↔∃r,d.owns t r=true∧d.lam t r=i:=by
 simp[oLeaves]
lemma dA {i}:
  i∈topLeaves d A↔(∃a∈A,a.val=i)∨∃s∈d.cover,d.tie s=none∧d.bw s=i:=by
 simp[topLeaves,and_assoc]
lemma kC (back:ReadsBack n C) {t} (dN:TermOK n C d t):
  d.zroot t<d.bw t∧d.oroot t<d.bw t:=by
 obtain⟨j,c,b,_,_,a⟩:=dN;rw[b];rcases a with a|a<;>constructor<;>apply back j c<;>simp[a]
lemma sD {G L ρ} (back:ReadsBack n C) (tr:IsOrTree n C G L ρ)
  (b:∀j∈G,j<C.gates.length):
  ∀j∈G,W C x (n+j)↔∃i∈(gateAt C j).inputs,W C x i:=
 fun j a=>aY (x:=x) back (b j a) (tr.1 j a).1
lemma vP {t:Fin n} (back:ReadsBack n C)
  (b:∀s∈d.cover,TermOK n C d s)
  (tr:IsOrTree n C (gatesOf d C Kind.z t.val) (zLeaves d t) (d.zroot t))
  (k:x t=true):
  ∀j∈gatesOf d C Kind.z t.val,IsCentred n C d (n+j)→W C x (n+j):=by
 intro j
 induction j using Nat.strong_induction_on with
 | ind j ih=>
   intro a c;have g:=cE _ _ j a;have role:=(Finset.mem_filter.mp a).2;obtain⟨i,f,h⟩:=(cJ back g (congrArg Prod.fst role)).1 c;apply(aY (x:=x) back g (tr.1 j a).1).2;refine⟨i,f,?_⟩;rcases (tr.1 j a).2.2 i f with leaf|⟨m,gi⟩
   ·rcases dF.mp leaf with e|⟨s,hs,_,e⟩
    ·exact e▸(aC (C:=C) (x:=x) t).2 k
    ·exact False.elim (cM (b s hs) (e▸h))
   ·have l:=back j g i f;have e:n+(i-n)=i:=by omega
    exact e▸ih (i-n) (by omega) gi (e.symm▸h)
lemma iJ (eM:Valid n K A C d) (x:Fin n→Bool):
  W C x C.output↔(∃a∈A,x a=true)∨(∃u v,K.Adj u v∧x u=true∧x v=true):=by
 classical
 obtain⟨back,_,k,tie,_,c,top⟩:=eM;have f:=fun t ht=>(c t ht).1
 have h:=fun t ht=>(c t ht).2.1
 have w:=fun t ht=>(c t ht).2.2.1
 have lam:=fun t ht=>(c t ht).2.2.2
 have g:=fI top back iY (W C x) (sD (x:=x) back top iY);have O:=fun t ht=>fI (h t ht) back (cE _ _) (W C x) (sD (x:=x) back (h t ht) (cE _ _))
 have J:=fun t ht=>fI (w t ht) back (cE _ _) (W C x) (sD (x:=x) back (w t ht) (cE _ _))
 have sT:∀t r,d.owns t r=true→x r=true→W C x (d.lam t r):=by
  intro t r edge m;have L:=lam t (k.1 _ _ edge).2 r edge;by_cases hr:r∈d.cover
  ·simp only[LamOK,hr,↓reduceIte] at L;rcases L.2.1 with e|⟨j,B,e,role⟩
   ·exact e▸(aC (C:=C) (x:=x) r).2 m
   ·rw[e] at L ⊢
    apply vP back f (h r hr) m j _ L.1;exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr B,role⟩
  ·simp only[LamOK,hr,↓reduceIte] at L;exact L▸(aC (C:=C) (x:=x) r).2 m
 have sU:∀t r,d.owns t r=true→W C x (d.lam t r)→
   x r=true∨∃s∈d.cover,W C x (d.bw s)∧d.bw s≤d.lam t r:=by
  intro t r edge M;have L:=lam t (k.1 _ _ edge).2 r edge;by_cases hr:r∈d.cover
  ·simp only[LamOK,hr,↓reduceIte] at L;rcases L.2.1 with e|⟨j,B,e,role⟩
   ·exact Or.inl ((aC (C:=C) (x:=x) r).1 (e▸M))
   ·have Z:j∈gatesOf d C Kind.z r.val:=
     Finset.mem_filter.mpr ⟨Finset.mem_range.mpr B,role⟩
    obtain⟨i,li,y,le⟩:=tV (h r hr) back (cE _ _) (W C x)
     (sD (x:=x) back (h r hr) (cE _ _)) j Z (e▸M)
    rcases dF.mp li with q|⟨s,hs,_,q⟩
    ·exact Or.inl ((aC (C:=C) (x:=x) r).1 (q▸y))
    ·exact Or.inr ⟨s,hs,q.symm▸y,by omega⟩
  ·simp only[LamOK,hr,↓reduceIte] at L;exact Or.inl ((aC (C:=C) (x:=x) r).1 (L▸M))
 constructor
 ·intro N;have E (b:ℕ):∀t∈d.cover,d.bw t=b→W C x b→
    ∃u v,K.Adj u v∧x u=true∧x v=true:=by
   induction b using Nat.strong_induction_on with
   | ind b ih=>
     intro t ht q wb;obtain⟨wz,wo⟩:=(bO (x:=x) back (f t ht)).1 (q.symm▸wb);obtain⟨z,Q,F⟩:=(O t ht).1 wz;obtain⟨o,P,T⟩:=(J t ht).1 wo;have zl:=lM (h t ht) back (cE _ _) _ Q;have ol:=lM (w t ht) back (cE _ _) _ P;obtain⟨zb,ob⟩:=kC back (f t ht);rcases dF.mp Q with X|⟨s,hs,_,G⟩
     ·obtain⟨r,owns,V⟩:=iZ.mp P;rcases sU _ _ owns (V.symm▸T) with m|⟨s,hs,ws,a1⟩
      ·exact⟨t,r,(k.1 t r owns).1,(aC (C:=C) (x:=x) t).1 (X▸F),m⟩
      ·exact ih _ (by omega) s hs rfl ws
     ·exact ih _ (by omega) s hs rfl (G.symm▸F)
  obtain⟨i,hi,y⟩:=g.1 N;rcases dA.mp hi with⟨a,H,U⟩|⟨s,hs,_,G⟩
  ·exact Or.inl ⟨a,H,(aC (C:=C) (x:=x) a).1 (U.symm▸y)⟩
  ·exact Or.inr (E _ s hs G y)
 ·rintro(⟨a,H,xa⟩|⟨u,v,adj,xu,xv⟩)
  ·exact g.2 ⟨_,dA.mpr (Or.inl ⟨a,H,rfl⟩),(aC (C:=C) (x:=x) a).2 xa⟩
  ·have l (b:ℕ):∀s∈d.cover,n+C.gates.length-d.bw s=b→
         W C x (d.bw s)→W C x C.output:=by
    induction b using Nat.strong_induction_on with
    | ind b ih=>
      intro s hs a0 ws
      cases τ:d.tie s with
      | none=>exact g.2 ⟨_,dA.mpr (Or.inr ⟨s,hs,τ,rfl⟩),ws⟩
      | some t=>
        have owner:=(tie s t τ).2;have ht:=(k.1 _ _ owner).2;have L:=lam t ht s owner;simp only[LamOK,hs,↓reduceIte] at L;have S:d.bw s∈zLeaves d t:=dF.mpr (Or.inr ⟨s,hs,τ,rfl⟩);have wt:=(bO (x:=x) back (f t ht)).2
         ⟨(O t ht).2 ⟨_,S,ws⟩,(J t ht).2
           ⟨_,iZ.mpr ⟨s,owner,rfl⟩,(L.2.2 τ).symm▸((bO (x:=x) back (f s hs)).1 ws).1⟩⟩
        obtain⟨j,B,ej,_⟩:=f t ht;have le:=lM (h t ht) back (cE _ _) _ S;have lt:=(kC back (f t ht)).1;exact ih _ (by omega) t ht rfl wt
   have p (t r:Fin n) (edge:d.owns t r=true) (xt:x t=true)
     (m:x r=true):W C x C.output:=by
    have ht:=(k.1 _ _ edge).2;apply l _ t ht rfl;exact(bO (x:=x) back (f t ht)).2
     ⟨(O t ht).2 ⟨_,dF.mpr (Or.inl rfl),(aC (C:=C) (x:=x) t).2 xt⟩,
      (J t ht).2 ⟨_,iZ.mpr ⟨r,edge,rfl⟩,sT t r edge m⟩⟩
   cases e:d.owns u v with
   | true=>exact p u v e xu xv
   | false=>
     have R:=k.2 _ _ adj;rw[e] at R
     cases e':d.owns v u with
     | false=>exact(R e'.symm).elim
     | true=>exact p v u e' xv xu
end A7
end PEqualNP.MetaComplexity.NestedCover
namespace PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitLowerBounds
lemma mI {n:ℕ} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {A:Finset (Fin n)} {C:Circuit} {d:NCCData n} (h:Valid n K A C d):
  circuitFun n C=graphFun K A:=by
 funext x;rw[Bool.eq_iff_iff];change W C x C.output↔graphFun K A x=true;simpa only[graphFun,Bool.or_eq_true,decide_eq_true_eq] using A7.iJ h x
end PEqualNP.MetaComplexity.NestedCover
namespace Aq
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
lemma mJ {n:ℕ} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {A:Finset (Fin n)} {C:Circuit} (b:K.IsAcyclic)
  (f:∀a∈A,∀v:Fin n,¬K.Adj a v)
  (g:A.Nonempty∨∃u v,K.Adj u v) (h:IsNestedCoverCircuit n K A C):
  IsMinimalCircuit n C∧circuitFun n C=graphFun K A:=by
 obtain⟨d,c⟩:=h;have e:=mI c;exact⟨iR b f g c e,e⟩
end Aq
namespace Aq
open PEqualNP.MetaComplexity.NestedCover SimpleGraph
def cK {n} (K:SimpleGraph (Fin n)) (A:Finset (Fin n)):=∀a∈A,∀v,¬K.Adj a v
def nE {n} (K:SimpleGraph (Fin n)) (A:Finset (Fin n)):=A.Nonempty∨∃u v,K.Adj u v
def bC {n} (K:SimpleGraph (Fin n)) (l p:Fin n):=∀v,K.Adj l v↔v=p
lemma kK {n} (K:SimpleGraph (Fin n)) (l p r:Fin n)
  (left:bC K l p) (q:r≠l) (e:K.Adj p r)
  (right:∀w,K.Adj r w→w=p) (T:Finset (Fin n))
  (d:IsMinCover K T):l∉T:=by
 intro hl;have c:∀S,PEqualNP.MetaComplexity.Aa.Ak.yX K S→T.card≤S.card:=fun S hs=>d.2 S (fun _ _ h=>hs _ _ h)
 have f:PEqualNP.MetaComplexity.Aa.Ak.yX (K.deleteEdges {s(l,p)}) (T.erase l):=by
  intro i j h;obtain⟨a,b⟩:=deleteEdges_adj.mp h;have m:i≠l:=by rintro rfl;exact b (by rw[(left j).1 a];simp)
  have o:j≠l:=by rintro rfl;exact b (by rw[(left i).1 a.symm];simp[Sym2.eq_swap])
  exact(d.1 a).imp (fun g=>Finset.mem_erase.mpr ⟨m,g⟩) (fun k=>Finset.mem_erase.mpr ⟨o,k⟩)
 have aT:=PEqualNP.MetaComplexity.Aa.Ak.tR K l p r T.card q e
  right c _ f
 have:=Finset.card_erase_add_one hl;omega
lemma jA {n} (P:SimpleGraph (Fin n)→Finset (Fin n)→Prop)
  (zero:∀K A,(∀u v,¬K.Adj u v)→A.Nonempty→P K A)
  (M:∀K A l p,K.IsAcyclic→cK K A→bC K l p→
    (∀T,IsMinCover K T→l∉T)→P (K.deleteIncidenceSet l) A→P K A)
  (pair:∀K A l p q,K.IsAcyclic→cK K A→bC K l p→q≠l→
    (∀v,K.Adj p v↔v=l∨v=q)→P (K.deleteIncidenceSet l) A→
    P ((K.deleteIncidenceSet l).deleteIncidenceSet p) (insert p A)→P K A)
  (edge:∀K A l p,K.IsAcyclic→cK K A→bC K l p→bC K p l→
    (nE (K.deleteIncidenceSet l) A→P (K.deleteIncidenceSet l) A)→
    P ((K.deleteIncidenceSet l).deleteIncidenceSet p) (insert p A)→P K A)
  (K:SimpleGraph (Fin n)) (A:Finset (Fin n)) (Q:K.IsAcyclic)
  (V:cK K A) (C:nE K A):P K A:=by
 suffices all:∀m (G:SimpleGraph (Fin n)) B,G.edgeSet.ncard=m→
   G.IsAcyclic→cK G B→nE G B→P G B by
  exact all _ _ _ rfl Q V C
 intro m
 induction m using Nat.strong_induction_on with
 | _ m ih=>
   intro G B e g iso N;by_cases o:∃u v,G.Adj u v;swap
   ·exact zero G B (fun u v h=>o ⟨u,v,h⟩) (N.resolve_right o)
   obtain⟨l,p,lp,X,j⟩:=PEqualNP.MetaComplexity.Aa.Ak.gM G g o;have leaf:bC G l p:=fun v=>⟨X v,fun U=>U▸lp⟩
   let H:=G.deleteIncidenceSet l
   let J:=H.deleteIncidenceSet p
   have s:H≤G:=deleteIncidenceSet_le _ _;have E:J≤H:=deleteIncidenceSet_le _ _;have x:H<G:=lt_of_le_of_ne s (by intro d;have h:H.Adj l p:=d▸lp;exact(deleteIncidenceSet_adj.mp h).2.1 rfl);have f:H.edgeSet.ncard< m:=e▸Set.ncard_lt_ncard (edgeSet_strict_mono x);have t:J.edgeSet.ncard< m:=lt_of_le_of_lt (Set.ncard_le_ncard (edgeSet_mono E)) f;have c:P J (insert p B):=by
    apply ih _ t J _ rfl (g.anti (le_trans E s)) _ (Or.inl (Finset.insert_nonempty _ _));intro a k v y;rcases Finset.mem_insert.mp k with rfl|k
    ·exact(deleteIncidenceSet_adj.mp y).2.1 rfl
    ·exact iso a k v (s (E y))
   have b (z:nE H B):P H B:=ih _ f H B rfl (g.anti s) (fun a k v h=>iso a k v (s h)) z;rcases j with⟨q,i⟩|⟨r,S,R,Z⟩
   ·by_cases extra:∃w,G.Adj p w∧w≠l
    ·obtain⟨w,F,O⟩:=extra;have wq:=(i w F).resolve_left O;subst q;apply pair G B l p w g iso leaf O
     ·intro v;exact⟨i v,fun h=>h.elim (fun d=>d▸lp.symm) (fun d=>d▸F)⟩
     ·exact b (Or.inr ⟨p,w,deleteIncidenceSet_adj.mpr ⟨F,lp.ne.symm,O⟩⟩)
     ·exact c
    ·exact edge G B l p g iso leaf (fun v=>⟨fun h=>Classical.byContradiction (fun C=>extra ⟨v,h,C⟩),fun d=>d▸lp.symm⟩) b c
   ·exact M G B l p g iso leaf (kK G l p r leaf S R Z)
     (b (Or.inr ⟨p,r,deleteIncidenceSet_adj.mpr ⟨R,lp.ne.symm,S⟩⟩))
end Aq
namespace Aq
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover SimpleGraph
variable {n : ℕ} {K : SimpleGraph (Fin n)} {A T S : Finset (Fin n)} {l p q : Fin n}
lemma bP (leaf:bC K l p):
  K.deleteIncidenceSet l=K.deleteEdges {s(l,p)}:=by
 ext u v;rw[deleteIncidenceSet_adj,deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff];constructor
 ·rintro⟨h,b,c⟩;exact⟨h,by tauto⟩
 ·rintro⟨h,a⟩;exact⟨h,fun e=>a (Or.inl ⟨e,(leaf v).1 (e▸h)⟩),fun e=>a (Or.inr ⟨(leaf u).1 (e▸h.symm),e⟩)⟩
lemma gC (leaf:bC K l p)
  (a:∀v,K.Adj p v→v=l∨v=q):
  (K.deleteIncidenceSet l).deleteIncidenceSet p=K.deleteEdges {s(p,l),s(p,q)}:=by
 ext u v;simp only[deleteIncidenceSet_adj,deleteEdges_adj,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_iff];constructor
 ·tauto
 ·rintro⟨h,g⟩;have b (e:u=l):=(leaf v).1 (e▸h);have d (e:v=l):=(leaf u).1 (e▸h.symm);have c (e:u=p):=a v (e▸h);have f (e:v=p):=a u (e▸h.symm);tauto
lemma mK (hs:IsMinCover (K.deleteIncidenceSet l) S):
  K.IsVertexCover ((insert l S:Finset (Fin n)):Set (Fin n)):=by
 intro u v a;by_cases h:u=l
 ·exact Or.inl (h▸Finset.mem_insert_self _ _)
 by_cases g:v=l
 ·exact Or.inr (g▸Finset.mem_insert_self _ _)
 exact(hs.1 (deleteIncidenceSet_adj.mpr ⟨a,h,g⟩)).imp
  (fun b=>Finset.mem_insert_of_mem b) (fun c=>Finset.mem_insert_of_mem c)
lemma oP (ht:IsMinCover K T) (hs:IsMinCover (K.deleteIncidenceSet l) S):
  S.card≤T.card∧T.card≤S.card+1:=
 ⟨hs.2 T (fun _ _ h=>ht.1 (deleteIncidenceSet_le _ _ h)),
   (ht.2 _ (mK hs)).trans (Finset.card_insert_le _ _)⟩
lemma pJ (ht:IsMinCover K T) (hs:IsMinCover (K.deleteIncidenceSet l) S)
  (a:∀U,IsMinCover K U→l∉U):T.card=S.card:=by
 have b:=hs.2 T (fun _ _ h=>ht.1 (deleteIncidenceSet_le _ _ h));by_contra! d;exact a _ ⟨mK hs,fun U c=>(Finset.card_insert_le l S).trans (le_trans (by omega:S.card+1≤T.card) (ht.2 U c))⟩ (Finset.mem_insert_self _ _)
lemma jB (leaf:bC K l p) (ht:IsMinCover K T)
  (hs:IsMinCover ((K.deleteIncidenceSet l).deleteIncidenceSet p) S):
  T.card=S.card+1:=by
 have d:T.card≤S.card+1:=by
  apply le_trans (ht.2 (insert p S) _) (Finset.card_insert_le _ _);intro u v b;by_cases g:u=p
  ·exact Or.inl (g▸Finset.mem_insert_self _ _)
  by_cases i:v=p
  ·exact Or.inr (i▸Finset.mem_insert_self _ _)
  have k:u≠l:=fun e=>i ((leaf v).1 (e▸b))
  have m:v≠l:=fun e=>g ((leaf u).1 (e▸b.symm))
  exact(hs.1 (deleteIncidenceSet_adj.mpr
   ⟨deleteIncidenceSet_adj.mpr ⟨b,k,m⟩,g,i⟩)).imp
   (fun s=>Finset.mem_insert_of_mem s) (fun t=>Finset.mem_insert_of_mem t)
 have f (a:Fin n) (q:a∈T) (e:a=l∨a=p):S.card+1≤T.card:=by
  have j:((K.deleteIncidenceSet l).deleteIncidenceSet p).IsVertexCover
    ((T.erase a:Finset (Fin n)):Set (Fin n)):=by
   intro u v h;obtain⟨o,up,x⟩:=deleteIncidenceSet_adj.mp h;obtain⟨b,w,vl⟩:=deleteIncidenceSet_adj.mp o;rcases e with rfl|rfl
   ·exact(ht.1 b).imp (fun c=>Finset.mem_erase.mpr ⟨w,c⟩) (fun c=>Finset.mem_erase.mpr ⟨vl,c⟩)
   ·exact(ht.1 b).imp (fun c=>Finset.mem_erase.mpr ⟨up,c⟩) (fun c=>Finset.mem_erase.mpr ⟨x,c⟩)
  have:=hs.2 _ j;have:=Finset.card_erase_add_one q;omega
 rcases ht.1 ((leaf p).2 rfl) with hl|r
 ·exact le_antisymm d (f _ hl (Or.inl rfl))
 ·exact le_antisymm d (f _ r (Or.inr rfl))
lemma lN [DecidableRel K.Adj]:
  graphFun K A=PEqualNP.MetaComplexity.Aa.Ak.F K A:=by
 funext y;rw[Bool.eq_iff_iff,PEqualNP.MetaComplexity.Aa.Ak.hK];simp[graphFun]
lemma eA [DecidableRel K.Adj] (leaf:bC K l p) (iso:cK K A)
  (x:Fin n→Bool):
  graphFun K A (Function.update x l false)=graphFun (K.deleteIncidenceSet l) A x:=by
 have a:l∉A:=fun b=>iso l b p ((leaf p).2 rfl)
 simp only[lN,bP leaf];exact PEqualNP.MetaComplexity.Aa.Ak.iV K A l p a (fun v=>(leaf v).1) x
lemma iK [DecidableRel K.Adj] (leaf:bC K l p) (iso:cK K A)
  (a:∀v,K.Adj p v→v=l∨v=q) (x:Fin n→Bool):
  graphFun K A (Function.update x l false)=graphFun (K.deleteIncidenceSet l) A x∧
  graphFun K A (Function.update x l true)=graphFun ((K.deleteIncidenceSet l).deleteIncidenceSet p) (insert p A) x:=by
 classical
 have b:l∉A:=fun c=>iso l c p ((leaf p).2 rfl)
 refine⟨eA leaf iso x,?_⟩;simp only[lN,gC leaf a];exact PEqualNP.MetaComplexity.Aa.Ak.kT K A l p q
  b ((leaf p).2 rfl) (fun v=>(leaf v).1) a x
lemma gD [DecidableRel K.Adj] (leaf:bC K l p) (iso:cK K A):
  ∃x,graphFun K A (Function.update x l (!x l))≠graphFun K A x:=by
 rw[lN];exact PEqualNP.MetaComplexity.Aa.Ak.yW K A l p ((leaf p).2 rfl)
  (fun a=>iso _ a _ ((leaf p).2 rfl).symm)
end Aq
namespace PEqualNP.MetaComplexity.Aa
open PEqualNP.CircuitLowerBounds
def aD (gs:List Gate) (w:List Bool):List Bool:=gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
lemma tW (C:Circuit) (x:List Bool):C.wires x=aD C.gates x:=rfl
lemma bD (gs gs':List Gate) (w:List Bool):
  aD (gs++gs') w=aD gs' (aD gs w):=by
 simp[aD,List.foldl_append]
lemma dQ (gs:List Gate):∀w:List Bool,
  ∃t:List Bool,aD gs w=w++t∧t.length=gs.length:=by
 induction gs with
 | nil=>intro w;exact⟨[],by simp[aD],rfl⟩
 | cons g gs ih=>
   intro w;obtain⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]);refine⟨g.op.eval (g.inputs.map fun i=>w.getD i false)::t,?_,by simp[hl]⟩;have:aD (g::gs) w=aD gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl;rw[this,ht];simp
lemma aV (gs:List Gate) (w:List Bool):
  (aD gs w).length=w.length+gs.length:=by
 obtain⟨t,ht,hl⟩:=dQ gs w;rw[ht];simp[hl]
lemma bG (gs:List Gate) (w:List Bool) (i:ℕ) (h:i<w.length):
  (aD gs w).getD i false=w.getD i false:=by
 obtain⟨t,ht,_⟩:=dQ gs w;rw[ht,List.getD_append _ _ _ _ h]
def Ok (g:Gate):Prop:=g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)∧g.inputs.length≤2
lemma bQ {α:Type} (L:List α) (S d:α) (j:ℕ) (h:j≠L.length):
  (L++[S]).getD j d=L.getD j d:=by
 by_cases a:j<L.length
 ·exact List.getD_append _ _ _ _ a
 ·rw[List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
lemma bR {α:Type} (L:List α) (S d:α):(L++[S]).getD L.length d=S:=by simp
def NOk (g:Gate):Prop:=Ok g∧(g.op=GateOp.not→ g.inputs.length≤1)
inductive Stat : Type
  | const (c : Bool)
  | cB (j : ℕ)
def Stat.val (w:List Bool):Stat→Bool
 | Stat.const c=>c
 | Stat.cB j=>w.getD j false
def Stat.Valid (m:ℕ):Stat→Prop
 | Stat.const _=>True
 | Stat.cB j=>j< m
def hO (m:ℕ):List Stat→Option Gate×Stat
 | []=>(none,Stat.const true)
 | Stat.const c::_=>(none,Stat.const (!c))
 | Stat.cB j::_=>(some ⟨GateOp.not,[j]⟩,Stat.cB m)
def eC (m:ℕ):List Stat→Option Gate×Stat
 | []=>(none,Stat.const true)
 | [Stat.const c]=>(none,Stat.const c)
 | [Stat.cB j]=>(none,Stat.cB j)
 | [Stat.const c,Stat.const d]=>(none,Stat.const (c && d))
 | [Stat.const c,Stat.cB j]=>(none,bif c then Stat.cB j else Stat.const false)
 | [Stat.cB j,Stat.const c]=>(none,bif c then Stat.cB j else Stat.const false)
 | [Stat.cB j,Stat.cB k]=>(some ⟨GateOp.and,[j,k]⟩,Stat.cB m)
 | _=>(none,Stat.const false)
def gJ (m:ℕ):List Stat→Option Gate×Stat
 | []=>(none,Stat.const false)
 | [Stat.const c]=>(none,Stat.const c)
 | [Stat.cB j]=>(none,Stat.cB j)
 | [Stat.const c,Stat.const d]=>(none,Stat.const (c || d))
 | [Stat.const c,Stat.cB j]=>(none,bif c then Stat.const true else Stat.cB j)
 | [Stat.cB j,Stat.const c]=>(none,bif c then Stat.const true else Stat.cB j)
 | [Stat.cB j,Stat.cB k]=>(some ⟨GateOp.or,[j,k]⟩,Stat.cB m)
 | _=>(none,Stat.const false)
def aH (op:GateOp) (m:ℕ) (bS:List Stat):Option Gate×Stat:=
 match op with
 | GateOp.and=>eC m bS
 | GateOp.or=>gJ m bS
 | GateOp.not=>hO m bS
 | _=>(none,Stat.const false)
lemma tX (op:GateOp) (m:ℕ) (bS:List Stat):
  ∀g∈(aH op m bS).1,Ok g:=by
 intro g d
 cases op<;>simp only[aH] at d
 ·rcases bS with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b)<;>simp[eC] at d<;>(subst d;simp[Ok])
 ·rcases bS with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b)<;>simp[gJ] at d<;>(subst d;simp[Ok])
 ·rcases bS with _|⟨a,l⟩<;>(try cases a)<;>simp[hO] at d<;>(subst d;simp[Ok])
 ·simp at d
 ·simp at d
lemma fK (op:GateOp) (m:ℕ) (bS:List Stat)
  (f:op=GateOp.and∨op=GateOp.or∨op=GateOp.not) (g:bS.length≤2)
  (hnot:op=GateOp.not→bS.length≤1) (e:∃c,Stat.const c∈bS):
  (aH op m bS).1=none:=by
 obtain⟨c,e⟩:=e;rcases f with rfl|rfl|rfl
 ·rcases bS with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩<;>(try cases a)<;>(try cases b)<;>simp_all[aH,eC]
 ·rcases bS with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩<;>(try cases a)<;>(try cases b)<;>simp_all[aH,gJ]
 ·have:=hnot rfl;rcases bS with _|⟨a,_|⟨b,l⟩⟩<;>(try cases a)<;>simp_all[aH,hO]
lemma pK (op:GateOp) (g:op=GateOp.and∨op=GateOp.or∨op=GateOp.not)
  (w:List Bool) (bS:List Stat) (f:bS.length≤2)
  (h:∀s∈bS,s.Valid w.length):
  ((aH op w.length bS).2).Valid (w.length+(aH op w.length bS).1.toList.length)∧
  ((aH op w.length bS).2).val (aD (aH op w.length bS).1.toList w)
    =op.eval (bS.map (Stat.val w)):=by
 rcases g with rfl|rfl|rfl
 ·rcases bS with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩
  ·simp[aH,eC,Stat.Valid,Stat.val,GateOp.eval]
  ·cases a<;>simp_all[aH,eC,Stat.Valid,Stat.val,GateOp.eval,aD]
  ·cases a<;>cases b<;>(try rename_i c e;cases c)<;>(try cases e)<;>simp_all[aH,eC,Stat.Valid,Stat.val,GateOp.eval,aD]
  ·simp at f
 ·rcases bS with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩
  ·simp[aH,gJ,Stat.Valid,Stat.val,GateOp.eval]
  ·cases a<;>simp_all[aH,gJ,Stat.Valid,Stat.val,GateOp.eval,aD]
  ·cases a<;>cases b<;>(try rename_i c e;cases c)<;>(try cases e)<;>simp_all[aH,gJ,Stat.Valid,Stat.val,GateOp.eval,aD]
  ·simp at f
 ·rcases bS with _|⟨a,l⟩
  ·simp[aH,hO,Stat.Valid,Stat.val,GateOp.eval]
  ·cases a<;>simp_all[aH,hO,Stat.Valid,Stat.val,GateOp.eval,aD]
def aI (n:ℕ) (a:List Stat×List Gate) (g:Gate):List Stat×List Gate:=
 (a.1++[(aH g.op (n+a.2.length)
    (g.inputs.map fun i=>a.1.getD i (Stat.const false))).2],
   a.2++(aH g.op (n+a.2.length)
    (g.inputs.map fun i=>a.1.getD i (Stat.const false))).1.toList)
def elim (n:ℕ) (gs:List Gate) (a:List Stat×List Gate):List Stat×List Gate:=gs.foldl (aI n) a
lemma kU {α:Type} (L:List α) (S d:α) (k:ℕ) (h:L.length=k):
  (L++[S]).getD k d=S:=by
 subst h;simp
lemma rK (n k:ℕ) (d:Stat) (gs:List Gate):∀a:List Stat×List Gate,
  k<a.1.length→(elim n gs a).1.getD k d=a.1.getD k d:=by
 induction gs with
 | nil=>intro a _;rfl
 | cons g gs ih=>
   intro a c;have b:elim n (g::gs) a=elim n gs (aI n a g):=rfl;rw[b,ih (aI n a g) (by simp[aI];omega)];exact bQ _ _ _ _ (by omega)
lemma dR {α:Type} (o:Option α):o.toList.length≤1:=by cases o<;>simp
lemma wR (n:ℕ) (gs:List Gate):∀a:List Stat×List Gate,
  (∀g∈a.2,Ok g)→∀g∈(elim n gs a).2,Ok g:=by
 induction gs with
 | nil=>intro a h;exact h
 | cons g gs ih=>
   intro a h;apply ih (aI n a g);intro c d;rcases List.mem_append.1 d with b|b
   ·exact h c b
   ·exact tX _ _ _ c (by simpa using b)
lemma gP (n:ℕ) (gs:List Gate):∀a:List Stat×List Gate,
  (elim n gs a).2.length≤a.2.length+gs.length:=by
 induction gs with
 | nil=>intro a;simp[elim]
 | cons g gs ih=>
   intro a;have c:=ih (aI n a g);have d:(aI n a g).2.length≤a.2.length+1:=by
    simp only[aI,List.length_append];have:=dR (aH g.op (n+a.2.length)
     (g.inputs.map fun i=>a.1.getD i (Stat.const false))).1
    omega
   have b:elim n (g::gs) a=elim n gs (aI n a g):=rfl;rw[b,List.length_cons];omega
lemma tY (n k:ℕ) (gs:List Gate):∀a:List Stat×List Gate,
  (∀g∈gs,NOk g)→k<a.1.length→(∃c,a.1.getD k (Stat.const false)=Stat.const c)→
  (∃g∈gs,k∈g.inputs)→(elim n gs a).2.length+1≤a.2.length+gs.length:=by
 induction gs with
 | nil=>intro a _ _ _ h;obtain⟨g,t,_⟩:=h;simp at t
 | cons g gs ih=>
   intro a o v d q;have s:elim n (g::gs) a=elim n gs (aI n a g):=rfl;rw[s,List.length_cons];by_cases m:k∈g.inputs
   ·obtain⟨c,d⟩:=d;have b:=o g List.mem_cons_self;have j:(aH g.op (n+a.2.length)
      (g.inputs.map fun i=>a.1.getD i (Stat.const false))).1=none:=by
     apply fK
     ·exact b.1.1
     ·simpa using b.1.2
     ·intro h;simpa using b.2 h
     ·exact⟨c,List.mem_map.2 ⟨k,m,d⟩⟩
    have r:(aI n a g).2.length=a.2.length:=by
     show(a.2++(aH g.op (n+a.2.length)
      (g.inputs.map fun i=>a.1.getD i (Stat.const false))).1.toList).length=_
     rw[j];simp
    have:=gP n gs (aI n a g);omega
   ·have p:∃e∈gs,k∈e.inputs:=by
     obtain⟨e,f,l⟩:=q;rcases List.mem_cons.1 f with rfl|h
     ·exact absurd l m
     ·exact⟨e,h,l⟩
    have u:=ih (aI n a g) (fun e f=>o e (List.mem_cons_of_mem _ f))
     (by simp[aI];omega)
     (by
       obtain⟨c,d⟩:=d;refine⟨c,?_⟩;simp only[aI];rw[bQ _ _ _ _ (by omega)];exact d)
     p
    have r:(aI n a g).2.length≤a.2.length+1:=by
     simp only[aI,List.length_append];have:=dR (aH g.op (n+a.2.length)
      (g.inputs.map fun i=>a.1.getD i (Stat.const false))).1
     omega
    omega
lemma Stat.vQ {m a:ℕ} (h:m≤a):∀s:Stat,s.Valid m→s.Valid a
 | Stat.const _,_=>trivial
 | Stat.cB _,hj=>lt_of_lt_of_le hj h
lemma Stat.vR (w t:List Bool):∀s:Stat,s.Valid w.length→
  s.val (w++t)=s.val w
 | Stat.const _,_=>rfl
 | Stat.cB _,hj=>List.getD_append _ _ _ _ hj
def yR (n:ℕ) (y:List Bool) (w:List Bool) (a:List Stat×List Gate):Prop:=
 a.1.length=w.length∧∀i:ℕ,
  (a.1.getD i (Stat.const false)).Valid (n+a.2.length)∧
  (a.1.getD i (Stat.const false)).val (aD a.2 y)=w.getD i false
lemma fL (n:ℕ) (y:List Bool) (v:y.length=n) (gs:List Gate):
  ∀
   (w:List Bool) (b:List Stat×List Gate),(∀g∈gs,Ok g)→yR n y w b→
   yR n y (aD gs w) (elim n gs b):=by
 induction gs with
 | nil=>intro w b _ h;exact h
 | cons g gs ih=>
   intro w b m h;apply ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) (aI n b g) (fun u p=>m u (List.mem_cons_of_mem _ p));obtain⟨hl,d⟩:=h;set j:=aD b.2 y with q
   have f:j.length=n+b.2.length:=by rw[q,aV,v]
   set bS:=g.inputs.map fun i=>b.1.getD i (Stat.const false) with e
   have c:=m g List.mem_cons_self;have hs:=pK g.op c.1 j bS (by simpa[e] using c.2)
    (by
      intro s hs;obtain⟨a,_,rfl⟩:=List.mem_map.1 hs;rw[f];exact(d a).1)
   rw[f] at hs;set r:=aH g.op (n+b.2.length) bS with hr
   have k:bS.map (Stat.val j)=g.inputs.map fun i=>w.getD i false:=by rw[e,List.map_map];apply List.map_congr_left;intro a _;exact(d a).2
   have o:aD (b.2++r.1.toList) y=aD r.1.toList j:=by rw[bD]
   obtain⟨t,ht,x⟩:=dQ r.1.toList j;refine⟨by simp[aI,hl],?_⟩;intro i
   show((b.1++[r.2]).getD i (Stat.const false)).Valid (n+(b.2++r.1.toList).length)∧((b.1++[r.2]).getD i (Stat.const false)).val (aD (b.2++r.1.toList) y)=_
   rw[o,List.length_append,←Nat.add_assoc];by_cases l:i=b.1.length
   ·subst l;rw[bR,hl,bR];exact⟨hs.1,by rw[hs.2,k]⟩
   ·rw[bQ _ _ _ _ l,bQ _ _ _ _ (by omega)];refine⟨Stat.vQ (by omega) _ (d i).1,?_⟩;rw[ht,Stat.vR _ _ _ (by rw[f];exact(d i).1)];exact(d i).2
def CleanGate (m:ℕ) (g:Gate):Prop:=
 (g.op=GateOp.not∧∃j,j< m∧g.inputs=[j])∨
 ((g.op=GateOp.and∨g.op=GateOp.or)∧∃j k,j< m∧k< m∧g.inputs=[j,k])
def aW (m:ℕ) (gs:List Gate):Prop:=∀(p:ℕ) (g:Gate),gs[p]?=some g→CleanGate (m+p) g
lemma CleanGate.nok {m:ℕ} {g:Gate} (h:CleanGate m g):NOk g:=by
 rcases h with⟨a,j,_,b⟩|⟨a|a,j,k,_,_,b⟩
 ·refine⟨⟨?_,?_⟩,?_⟩
  ·rw[a];exact Or.inr (Or.inr rfl)
  ·rw[b];simp
  ·intro _;rw[b];simp
 ·refine⟨⟨?_,?_⟩,?_⟩
  ·rw[a];exact Or.inl rfl
  ·rw[b];simp
  ·intro h;rw[a] at h;cases h
 ·refine⟨⟨?_,?_⟩,?_⟩
  ·rw[a];exact Or.inr (Or.inl rfl)
  ·rw[b];simp
  ·intro h;rw[a] at h;cases h
lemma CleanGate.lt {m:ℕ} {g:Gate} (h:CleanGate m g):∀a∈g.inputs,a< m:=by
 intro a b;rcases h with⟨_,j,d,c⟩|⟨_,j,k,d,e,c⟩
 ·rw[c] at b;simp at b;subst b;exact d
 ·rw[c] at b;simp at b;rcases b with rfl|rfl
  ·exact d
  ·exact e
lemma dS (m:ℕ) (gs:List Gate) (h:aW m gs):∀g∈gs,NOk g:=by intro g a;obtain⟨p,b⟩:=List.mem_iff_getElem?.1 a;exact(h p g b).nok
lemma pL (op:GateOp) (m:ℕ) (bS:List Stat) (e:∀s∈bS,s.Valid m):
  ∀g∈(aH op m bS).1,CleanGate m g:=by
 intro g d
 cases op<;>simp only[aH] at d
 ·rcases bS with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b)<;>
   simp[eC] at d
  subst d;refine Or.inr ⟨Or.inl rfl,_,_,?_,?_,rfl⟩
  ·exact e _ List.mem_cons_self
  ·exact e _ (List.mem_cons_of_mem _ List.mem_cons_self)
 ·rcases bS with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b)<;>
   simp[gJ] at d
  subst d;refine Or.inr ⟨Or.inr rfl,_,_,?_,?_,rfl⟩
  ·exact e _ List.mem_cons_self
  ·exact e _ (List.mem_cons_of_mem _ List.mem_cons_self)
 ·rcases bS with _|⟨a,l⟩<;>(try cases a)<;>simp[hO] at d
  subst d;refine Or.inl ⟨rfl,_,?_,rfl⟩;exact e _ List.mem_cons_self
 ·simp at d
 ·simp at d
lemma oQ {α:Type} (o:Option α) (k:ℕ) (a:α)
  (h:o.toList[k]?=some a):k=0∧a∈o:=by
 cases o with
 | none=>simp at h
 | some b=>
   cases k with
   | zero=>simp at h;simp[h]
   | succ k=>simp at h
lemma lO (n:ℕ) (y:List Bool) (r:y.length=n) (gs:List Gate):
  ∀
   (w:List Bool) (b:List Stat×List Gate),(∀g∈gs,Ok g)→yR n y w b→
   aW n b.2→aW n (elim n gs b).2:=by
 induction gs with
 | nil=>intro w b _ _ h;exact h
 | cons g gs ih=>
   intro w b k f hcl;have j:yR n y (aD [g] w) (aI n b g):=fL n y r [g] w b (fun c d=>k c (by simp at d;simp[d])) f;refine ih _ (aI n b g) (fun c d=>k c (List.mem_cons_of_mem _ d)) j ?_;intro p c q;have e:(b.2++(aH g.op (n+b.2.length) (g.inputs.map fun i=>b.1.getD i (Stat.const false))).1.toList)[p]?=some c:=q;by_cases m:p<b.2.length
   ·rw[List.getElem?_append_left m] at e;exact hcl p c e
   ·rw[List.getElem?_append_right (by omega)] at e;obtain⟨t,l⟩:=oQ _ _ _ e;have o:p=b.2.length:=by omega
    rw[o];exact pL _ _ _ (fun s hs=>by obtain⟨a,_,rfl⟩:=List.mem_map.1 hs;exact(f.2 a).1) c l
def aL (n:ℕ):List Stat:=List.ofFn (fun i:Fin n=>Stat.cB i)
lemma sE (n:ℕ) (y:Fin n→Bool):
  yR n (List.ofFn y) (List.ofFn y) (aL n,[]):=by
 refine⟨by simp[aL],?_⟩;intro i;by_cases a:i<n
 ·simp[aL,a,Stat.Valid,Stat.val,aD]
 ·rw[List.getD_eq_default _ _ (by simp[aL];omega),
   List.getD_eq_default _ _ (by simp;omega)]
  exact⟨trivial,rfl⟩
lemma dT {α:Type} (m:ℕ) (F:Fin m→α) (d:α) (j:Fin m):
  (List.ofFn F).getD j d=F j:=by
 simp
lemma jC {α:Type}:∀(l:List α) (p:ℕ) (g:α),l[p]?=some g→
  ∃b a,l=b++g::a∧b.length=p:=by
 intro l
 induction l with
 | nil=>intro p g h;simp at h
 | cons x l ih=>
   intro p g h
   cases p with
   | zero=>
     simp at h;subst h;exact⟨[],l,rfl,rfl⟩
   | succ p=>
     simp at h;obtain⟨b,a,rfl,rfl⟩:=ih p g h;exact⟨x::b,a,rfl,rfl⟩
def vl {k:ℕ} (gs:List Gate) (u:Fin k→Bool) (j:ℕ):Bool:=(aD gs (List.ofFn u)).getD j false
lemma tZ {k:ℕ} (gs:List Gate) (u:Fin k→Bool) (j:ℕ) (h:j<k):
  vl gs u j=u ⟨j,h⟩:=by
 unfold vl;rw[bG gs _ j (by simpa using h)];exact dT k u false ⟨j,h⟩
lemma eZ {k:ℕ} (gs:List Gate) (hcl:aW k gs) (u:Fin k→Bool) (p:ℕ)
  (g:Gate) (h:gs[p]?=some g):
  vl gs u (k+p)=g.op.eval (g.inputs.map (vl gs u)):=by
 have f:=(hcl p g h).lt;obtain⟨b,c,rfl,rfl⟩:=jC gs p g h;have d:(aD b (List.ofFn u)).length=k+b.length:=by rw[aV];simp
 have e:aD (b++g::c) (List.ofFn u)
   =
    aD c (aD b (List.ofFn u)++
    [g.op.eval (g.inputs.map fun i=>(aD b (List.ofFn u)).getD i false)]):=by
  rw[bD];rfl
 have full:∀j,j<k+b.length→
   (aD (b++g::c) (List.ofFn u)).getD j false
     =(aD b (List.ofFn u)).getD j false:=by
  intro j m;rw[e,bG _ _ j (by simp[d];omega),bQ _ _ _ _ (by omega)]
 have top:(aD (b++g::c) (List.ofFn u)).getD (k+b.length) false
   =g.op.eval (g.inputs.map fun i=>(aD b (List.ofFn u)).getD i false):=by
  rw[e,bG _ _ _ (by simp[d]),kU _ _ _ _ d]
 show(aD (b++g::c) (List.ofFn u)).getD (k+b.length) false
  =g.op.eval (g.inputs.map fun j=>(aD (b++g::c) (List.ofFn u)).getD j false)
 rw[top];congr 1;apply List.map_congr_left;intro a l;exact(full a (f a l)).symm
lemma rL (k:ℕ) (b:List Gate) (g:Gate) (d:List Gate)
  (hcl:aW k (b++g::d)) (o:ℕ) (S:Stat)
  (x:∀y:Fin k→Bool,S.Valid (k+(elim k b (aL k,[])).2.length)∧
    S.val (aD (elim k b (aL k,[])).2 (List.ofFn y))
     =vl (b++g::d) y (k+b.length))
  (E:∃y w:Fin k→Bool,vl (b++g::d) y o≠vl (b++g::d) w o):
  ∃
   gs' o',aW k gs'∧gs'.length+1≤(b++g::d).length∧
   ∀y:Fin k→Bool,vl gs' y o'=vl (b++g::d) y o:=by
 have r:∀e∈b++g::d,Ok e:=fun e B=>(dS _ _ hcl e B).1
 have i:∀e∈b,Ok e:=fun e h=>r e (List.mem_append_left _ h)
 have f:∀e∈d,Ok e:=fun e h=>r e (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have u:∀y:Fin k→Bool,yR k (List.ofFn y) (aD b (List.ofFn y))
   (elim k b (aL k,[])):=
  fun y=>fL k _ (by simp) b _ _ i (sE k y)
 have s:∀y:Fin k→Bool,(aD b (List.ofFn y)).length=k+b.length:=by intro y;rw[aV];simp
 have m:∀y:Fin k→Bool,aD (b++g::d) (List.ofFn y)
   =
    aD d (aD b (List.ofFn y)++
    [g.op.eval (g.inputs.map fun a=>(aD b (List.ofFn y)).getD a false)]):=by
  intro y;rw[bD];rfl
 have C:∀y:Fin k→Bool,vl (b++g::d) y (k+b.length)
   =g.op.eval (g.inputs.map fun a=>(aD b (List.ofFn y)).getD a false):=by
  intro y
  show(aD (b++g::d) (List.ofFn y)).getD (k+b.length) false=_
  rw[m,bG _ _ _ (by simp[s y]),kU _ _ _ _ (s y)]
 have n:∀y:Fin k→Bool,yR k (List.ofFn y)
   (aD b (List.ofFn y)++
     [g.op.eval (g.inputs.map fun a=>(aD b (List.ofFn y)).getD a false)])
   ((elim k b (aL k,[])).1++[S],(elim k b (aL k,[])).2):=by
  intro y;obtain⟨hl,G⟩:=u y;refine⟨by simp[hl],?_⟩;intro a
  show(((elim k b (aL k,[])).1++[S]).getD a (Stat.const false)).Valid
    (k+(elim k b (aL k,[])).2.length)∧
   (((elim k b (aL k,[])).1++[S]).getD a (Stat.const false)).val
    (aD (elim k b (aL k,[])).2 (List.ofFn y))=_
  by_cases q:a=(elim k b (aL k,[])).1.length
  ·rw[q,bR,hl,bR];exact⟨(x y).1,by rw[(x y).2,C]⟩
  ·rw[bQ _ _ _ _ q,bQ _ _ _ _ (by omega)];exact G a
 have v:∀y:Fin k→Bool,yR k (List.ofFn y)
   (aD (b++g::d) (List.ofFn y))
   (elim k d ((elim k b (aL k,[])).1++[S],(elim k b (aL k,[])).2)):=by
  intro y;rw[m];exact fL k _ (by simp) d _ _ f (n y)
 have z:aW k (elim k b (aL k,[])).2:=lO k (List.ofFn fun _:Fin k=>false) (by simp) b _ _ i (sE k _) (by intro p e H;simp at H);have A:aW k
   (elim k d ((elim k b (aL k,[])).1++[S],(elim k b (aL k,[])).2)).2:=
  lO k (List.ofFn fun _:Fin k=>false) (by simp) d _ _ f (n _) z
 have t:(elim k d ((elim k b (aL k,[])).1++[S],
   (elim k b (aL k,[])).2)).2.length+1≤(b++g::d).length:=by
  have J:(elim k d ((elim k b (aL k,[])).1++[S],
   (elim k b (aL k,[])).2)).2.length
   ≤(elim k b (aL k,[])).2.length+d.length:=gP k d _
  have K:(elim k b (aL k,[])).2.length≤0+b.length:=gP k b (aL k,[]);simp only[List.length_append,List.length_cons];omega
 have l:∀y:Fin k→Bool,
  ((elim k d ((elim k b (aL k,[])).1++[S],
    (elim k b (aL k,[])).2)).1.getD o (Stat.const false)).val
    (aD (elim k d ((elim k b (aL k,[])).1++[S],
      (elim k b (aL k,[])).2)).2 (List.ofFn y))
  =vl (b++g::d) y o:=fun y=>((v y).2 o).2
 cases hst:(elim k d ((elim k b (aL k,[])).1++[S],(elim k b (aL k,[])).2)).1.getD o (Stat.const false) with
 | const c=>
   exfalso;obtain⟨y,w,F⟩:=E;apply F;rw[←l y,←l w,hst];rfl
 | cB j=>
   refine⟨_,j,A,t,?_⟩;intro y;have h:=l y;rw[hst] at h;exact h
lemma pM (k:ℕ) (gs:List Gate) (hcl:aW k gs) (o p j:ℕ) (m:p<gs.length)
  (q:j<k+p) (f:∀y:Fin k→Bool,vl gs y (k+p)=vl gs y j)
  (i:∃y n:Fin k→Bool,vl gs y o≠vl gs n o):
  ∃
   gs' o',aW k gs'∧gs'.length+1≤gs.length∧
   ∀y:Fin k→Bool,vl gs' y o'=vl gs y o:=by
 obtain⟨g,l⟩:∃g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem m⟩
 obtain⟨a,b,rfl,rfl⟩:=jC gs p g l;apply rL k a g b hcl o ((elim k a (aL k,[])).1.getD j (Stat.const false))
  ?_ i
 intro y;have c:∀e∈a,Ok e:=fun e h=>(dS _ _ hcl e (List.mem_append_left _ h)).1
 have d:=fL k (List.ofFn y) (by simp) a _ _ c (sE k y);refine⟨(d.2 j).1,?_⟩;rw[(d.2 j).2,f y]
 show(aD a (List.ofFn y)).getD j false
  =(aD (a++g::b) (List.ofFn y)).getD j false
 rw[bD,bG (g::b) (aD a (List.ofFn y)) j
  (by rw[aV];simp;omega)]
lemma vS (k:ℕ) (gs:List Gate) (hcl:aW k gs) (o p:ℕ) (c:Bool)
  (h:p<gs.length) (b:∀y:Fin k→Bool,vl gs y (k+p)=c)
  (d:∃y i:Fin k→Bool,vl gs y o≠vl gs i o):
  ∃
   gs' o',aW k gs'∧gs'.length+1≤gs.length∧
   ∀y:Fin k→Bool,vl gs' y o'=vl gs y o:=by
 obtain⟨g,f⟩:∃g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem h⟩
 obtain⟨e,a,rfl,rfl⟩:=jC gs p g f;exact rL k e g a hcl o (Stat.const c) (fun y=>⟨trivial,(b y).symm⟩) d
end PEqualNP.MetaComplexity.Aa
namespace PEqualNP.MetaComplexity.Aa.Au
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Aa
structure Ao (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : aW m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), aW m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length
def bW (gs:List Gate) (p w:ℕ):Prop:=∃g,gs[p]?=some g∧w∈g.inputs
lemma sF (k:ℕ) (gs:List Gate) (o:ℕ) (hcl:aW k gs):
  HasCircuitSize k (fun y=>vl gs y o) gs.length:=by
 refine⟨⟨gs,o⟩,?_,le_refl _,fun y=>rfl⟩;intro g a;exact(dS k gs hcl g a).1
lemma uA {k:ℕ} {gs:List Gate} (hcl:aW k gs) {q w:ℕ} (h:bW gs q w):
  w<k+q:=by
 obtain⟨g,a,b⟩:=h;exact(hcl q g a).lt w b
lemma dU {gs:List Gate} {q w:ℕ} (h:bW gs q w):q<gs.length:=by obtain⟨g,a,_⟩:=h;exact(List.getElem?_eq_some_iff.1 a).1
lemma rM {k:ℕ} (gs:List Gate) (u:Fin k→Bool) (w:ℕ) (h:k+gs.length≤w):
  vl gs u w=false:=by
 unfold vl;exact List.getD_eq_default _ _ (by rw[aV];simp;omega)
lemma xQ (k:ℕ) (gs:List Gate) (hcl:aW k gs) (o p:ℕ) (J:p<gs.length)
  (C:o≠k+p) (H:∀q,¬bW gs q (k+p))
  (G:∃y s:Fin k→Bool,vl gs y o≠vl gs s o):
  ∃
   gs' o',aW k gs'∧gs'.length+1≤gs.length∧
   ∀y:Fin k→Bool,vl gs' y o'=vl gs y o:=by
 obtain⟨g,M⟩:∃g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem J⟩
 have m:0<k+p:=by rcases hcl p g M with⟨_,j,N,_⟩|⟨_,j,_,N,_,_⟩<;>omega
 let u:Gate:=⟨GateOp.and,[0,0]⟩
 let gs':=gs.set p u
 have P:gs'.length=gs.length:=by simp[gs']
 have f:gs'[p]?=some u:=by simp[gs',J]
 have c:∀r,r≠p→ gs'[r]?=gs[r]?:=by intro r hr;simp[gs',Ne.symm hr]
 have l:aW k gs':=by
  intro r i d;by_cases n:r=p
  ·subst n;rw[f] at d
   cases d
   exact Or.inr ⟨Or.inl rfl,0,0,m,m,rfl⟩
  ·rw[c r n] at d;exact hcl r i d
 have b:∀y:Fin k→Bool,∀w,w≠k+p→vl gs' y w=vl gs y w:=by
  intro y w
  induction w using Nat.strong_induction_on with
  | _ w ih=>
    intro Q;by_cases v:w<k
    ·rw[tZ gs' y w v,tZ gs y w v]
    ·obtain⟨r,rfl⟩:∃r,w=k+r:=⟨w-k,by omega⟩
     have n:r≠p:=fun e=>Q (by rw[e])
     cases hr:gs[r]? with
     | none=>
       have hl:gs.length≤ r:=List.getElem?_eq_none_iff.1 hr;rw[rM gs' y _ (by omega),rM gs y _ (by omega)]
     | some i=>
       have d:gs'[r]?=some i:=by rw[c r n];exact hr
       rw[eZ gs' l y r i d,eZ gs hcl y r i hr];congr 1;apply List.map_congr_left;intro a E;have F:=(hcl r i hr).lt a E;exact ih a F (fun e=>H r ⟨i,hr,e▸E⟩)
 have t:∀y:Fin k→Bool,vl gs' y (k+p)=vl gs' y 0:=by intro y;rw[eZ gs' l y p u f];simp[u,GateOp.eval]
 have B:∃y s:Fin k→Bool,vl gs' y o≠vl gs' s o:=by obtain⟨y,s,h⟩:=G;exact⟨y,s,by rw[b y o C,b s o C];exact h⟩
 obtain⟨x,K,z,O,A⟩:=pM k gs' l o p 0 (by omega) m t B;exact⟨x,K,z,by omega,fun y=>by rw[A y,b y o C]⟩
section
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
lemma Ao.ncv (L:Ao m f gs o) (a:∃x y:Fin m→Bool,f x≠f y):
  ∃y b:Fin m→Bool,vl gs y o≠vl gs b o:=by
 obtain⟨x,y,h⟩:=a;exact⟨x,y,by rw[L.hev,L.hev];exact h⟩
lemma Ao.no_const (L:Ao m f gs o) (e:∃x y:Fin m→Bool,f x≠f y) (p:ℕ)
  (g:p<gs.length) (c:Bool):¬ ∀u:Fin m→Bool,vl gs u (m+p)=c:=by
 intro a;obtain⟨gs',o',b,h,d⟩:=vS m gs L.hcl o p c g a (L.ncv e);have:=L.hmin gs' o' b (fun x=>by rw[d x];exact L.hev x);omega
lemma Ao.no_alias (L:Ao m f gs o) (d:∃x y:Fin m→Bool,f x≠f y) (p:ℕ)
  (g:p<gs.length) (j:ℕ) (e:j< m+p):
  ¬ ∀u:Fin m→Bool,vl gs u (m+p)=vl gs u j:=by
 intro a;obtain⟨gs',o',b,h,c⟩:=pM m gs L.hcl o p j g e a (L.ncv d);have:=L.hmin gs' o' b (fun x=>by rw[c x];exact L.hev x);omega
lemma Ao.live (L:Ao m f gs o) (d:∃x y:Fin m→Bool,f x≠f y) (p:ℕ)
  (j:p<gs.length) (i:o≠m+p):∃q,p<q∧bW gs q (m+p):=by
 by_contra e;have a:∀q,¬bW gs q (m+p):=by
  intro q h;by_cases g:p<q
  ·exact e ⟨q,g,h⟩
  ·have:=uA L.hcl h;omega
 obtain⟨gs',o',b,k,c⟩:=xQ m gs L.hcl o p j i a (L.ncv d);have:=L.hmin gs' o' b (fun x=>by rw[c x];exact L.hev x);omega
end
end PEqualNP.MetaComplexity.Aa.Au
namespace PEqualNP.MetaComplexity.Aa.Ay
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Aa
def qQ (n:ℕ) (F:(Fin n→Bool)→Bool) (s:ℕ):Prop:=
 ∀
  m,n≤ m→∃(gs:List Gate) (out:ℕ),(∀g∈gs,Ok g)∧(∀g∈gs,g.op≠GateOp.not)∧gs.length≤ s∧
  out< m+gs.length∧∀w:List Bool,w.length=m→(aD gs w).getD out false=F (fun i=>w.getD i false)
lemma dI {n:ℕ} {F:(Fin n→Bool)→Bool} {s s':ℕ} (h:qQ n F s) (hs:s≤ s'):
  qQ n F s':=by
 intro m b;obtain⟨gs,out,e,d,a,c,ev⟩:=h m b;exact⟨gs,out,e,d,le_trans a hs,c,ev⟩
lemma cF {n:ℕ} {F H:(Fin n→Bool)→Bool} {s:ℕ} (h:qQ n F s)
  (e:∀x,F x=H x):qQ n H s:=by
 intro m b;obtain⟨gs,out,g,f,a,c,ev⟩:=h m b;exact⟨gs,out,g,f,a,c,fun w d=>by rw[ev w d,e]⟩
lemma sG {n:ℕ} (i:Fin n):qQ n (fun x=>x i) 0:=by intro m a;refine⟨[],i,by simp,by simp,le_rfl,by simp;omega,?_⟩;intro w _;simp[aD]
lemma wS {n:ℕ} (op:GateOp) (l:op=GateOp.and∨op=GateOp.or)
  (c:Bool→Bool→Bool) (N:∀a b,op.eval [a,b]=c a b)
  {F H:(Fin n→Bool)→Bool} {C E:ℕ} (K:qQ n F C) (M:qQ n H E):
  qQ n (fun x=>c (F x) (H x)) (C+E+1):=by
 intro m O;obtain⟨e,j,A,y,P,S,q⟩:=K m O;obtain⟨f,k,B,z,Q,T,r⟩:=M (m+e.length) (by omega);refine⟨e++f++[⟨op,[j,k]⟩],m+e.length+f.length,?_,?_,?_,?_,?_⟩
 ·intro g d;simp only[List.mem_append,List.mem_singleton] at d;rcases d with(d|d)|d
  ·exact A g d
  ·exact B g d
  ·subst d;rcases l with h|h<;>simp[Ok,h]
 ·intro g d;simp only[List.mem_append,List.mem_singleton] at d;rcases d with(d|d)|d
  ·exact y g d
  ·exact z g d
  ·subst d;rcases l with h|h<;>simp[h]
 ·simp;omega
 ·simp;omega
 ·intro w s;rw[bD,bD];set v:=aD e w with p
  have t:v.length=m+e.length:=by rw[p,aV,s]
  set u:=aD f v with o
  have R:u.length=m+e.length+f.length:=by rw[o,aV,t]
  have step:aD [⟨op,[j,k]⟩] u
   =u++[op.eval ([j,k].map fun i=>u.getD i false)]:=rfl
  rw[step,←R,bR];simp only[List.map_cons,List.map_nil,N];have G:u.getD j false=F (fun i=>w.getD i false):=by rw[o,bG _ _ _ (by omega),p,q w s]
  have J:u.getD k false=H (fun i=>w.getD i false):=by rw[o,r v t];congr 1;funext i;rw[p,bG _ _ _ (by have:=i.2;omega)]
  rw[G,J]
lemma vT {n:ℕ} {F H:(Fin n→Bool)→Bool} {c d:ℕ} (e:qQ n F c)
  (f:qQ n H d):qQ n (fun x=>F x || H x) (c+d+1):=
 wS GateOp.or (Or.inr rfl) (· || ·) (by intro a b;simp[GateOp.eval]) e f
lemma aA1 {n:ℕ} {F H:(Fin n→Bool)→Bool} {c d:ℕ} (e:qQ n F c)
  (f:qQ n H d):qQ n (fun x=>F x && H x) (c+d+1):=
 wS GateOp.and (Or.inl rfl) (· && ·) (by intro a b;simp[GateOp.eval]) e f
lemma nW {n:ℕ} {F:(Fin n→Bool)→Bool} {s:ℕ} (h:qQ n F s):
  ∃
   D:Circuit,FanInTwo D ∧(∀g∈D.gates,g.op≠GateOp.not)∧
   circuitFun n D =F∧D.size≤ s:=by
 obtain⟨gs,out,c,b,a,_,ev⟩:=h n le_rfl;refine⟨⟨gs,out⟩,c,b,?_,a⟩;funext x;have e:=ev (List.ofFn x) (by simp);simp only[circuitFun,Circuit.eval,tW,e];congr 1;funext i;simp
lemma uB {n:ℕ} (a:List (Fin n)):∀v:Fin n,
  qQ n (fun x=>(v::a).any fun j=>x j) a.length:=by
 induction a with
 | nil=>intro v;exact cF (sG v) (by intro x;simp)
 | cons w ws ih=>
   intro v;have:=vT (sG v) (ih w);refine cF (dI this (by simp)) ?_;intro x;simp
lemma eD {n:ℕ} (S:Finset (Fin n)) (b:S.Nonempty):
  qQ n (fun x=>decide (∃v∈S,x v=true)) (S.card-1):=by
 obtain⟨v,a,hl⟩:∃v a,S.toList=v::a:=by
  cases h:S.toList with
  | nil=>simp at h;exact absurd h b.ne_empty
  | cons v a=>exact⟨v,a,rfl⟩
 have c:S.card=a.length+1:=by rw[←Finset.length_toList,hl];rfl
 refine cF (dI (uB a v) (by omega)) ?_;intro x;rw[Bool.eq_iff_iff,decide_eq_true_iff,←hl,List.any_eq_true];simp
open Classical in
lemma xR (n:ℕ) (T:Finset (Fin n)):∀E:Finset (Sym2 (Fin n)),E.Nonempty→
  (∀e∈E,∃t∈T,t∈e)→
  qQ n (fun x=>decide (∃e∈E,∀v∈e,x v=true)) (E.card+T.card-1):=by
 induction T using Finset.induction_on with
 | empty=>
   intro E w A
   obtain⟨e,c⟩:=w
   obtain⟨t,ht,_⟩:=A e c
   simp at ht
 | @insert t T0 htT ih=>
   intro E w A
   set E1:=E.filter (fun e=>t∈e) with k
   set E2:=E.filter (fun e=>t∉e) with r
   have g:E1.card+E2.card=E.card:=Finset.card_filter_add_card_filter_not _
   have p:(insert t T0).card=T0.card+1:=Finset.card_insert_of_notMem htT
   have C:∀e∈E2,∃B∈T0,B∈e:=by
    intro e c
    rw[r,Finset.mem_filter] at c
    obtain⟨B,G,i⟩:=A e c.1
    rcases Finset.mem_insert.1 G with h|h
    ·subst h;exact absurd i c.2
    ·exact⟨B,h,i⟩
   set S:=Finset.univ.filter (fun v:Fin n=>s(t,v)∈E1) with y
   have K:S.card≤E1.card:=by
    refine Finset.card_le_card_of_injOn (fun v=>s(t,v)) ?_ ?_
    ·intro v q
     simp only[y,Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq] at q
     exact q
    ·intro a _ b _ F
     exact Sym2.congr_right.1 F
   have star:E1.Nonempty→qQ n (fun x=>decide (∃e∈E1,∀v∈e,x v=true))
     E1.card:=by
    intro j
    have l:S.Nonempty:=by
     obtain⟨e,c⟩:=j
     have f:=c
     rw[k,Finset.mem_filter] at f
     obtain⟨b,z⟩:=Sym2.mem_iff_exists.1 f.2
     exact⟨b,by simp[y,←z,c]⟩
    have:=aA1 (sG t) (eD S l)
    have H:=l.card_pos
    refine cF (dI this (by omega)) ?_
    intro x
    rw[Bool.eq_iff_iff,Bool.and_eq_true,decide_eq_true_iff,decide_eq_true_iff]
    constructor
    ·rintro⟨ht,v,q,M⟩
     refine⟨s(t,v),(Finset.mem_filter.1 q).2,?_⟩
     intro u J
     rcases Sym2.mem_iff.1 J with rfl|rfl<;>assumption
    ·rintro⟨e,c,m⟩
     have f:=c
     rw[k,Finset.mem_filter] at f
     obtain⟨b,z⟩:=Sym2.mem_iff_exists.1 f.2
     subst z
     exact⟨m t (Sym2.mem_mk_left _ _),b,by simp[y,c],
      m b (Sym2.mem_mk_right _ _)⟩
   have o:∀x:Fin n→Bool,decide (∃e∈E,∀v∈e,x v=true)
     =(decide (∃e∈E1,∀v∈e,x v=true) || decide (∃e∈E2,∀v∈e,x v=true)):=by
    intro x
    rw[Bool.eq_iff_iff]
    simp only[Bool.or_eq_true,decide_eq_true_iff,k,r,Finset.mem_filter]
    constructor
    ·rintro⟨e,c,h⟩
     by_cases i:t∈e
     ·exact Or.inl ⟨e,⟨c,i⟩,h⟩
     ·exact Or.inr ⟨e,⟨c,i⟩,h⟩
    ·rintro(⟨e,⟨c,_⟩,h⟩|⟨e,⟨c,_⟩,h⟩)<;>exact⟨e,c,h⟩
   rw[p]
   by_cases j:E1.Nonempty
   ·by_cases d:E2.Nonempty
    ·have:=vT (star j) (ih E2 d C)
     have N:=d.card_pos
     refine cF (dI this (by omega)) ?_
     intro x
     rw[o]
    ·rw[Finset.not_nonempty_iff_eq_empty] at d
     refine cF (dI (star j) (by omega)) ?_
     intro x
     rw[o,d]
     simp
   ·rw[Finset.not_nonempty_iff_eq_empty] at j
    have d:E2.Nonempty:=by
     by_contra d
     rw[Finset.not_nonempty_iff_eq_empty] at d
     have:=w.card_pos
     rw[j,d] at g
     simp at g
     omega
    refine cF (dI (ih E2 d C) (by omega)) ?_
    intro x
    rw[o,j]
    simp
end PEqualNP.MetaComplexity.Aa.Ay
namespace PEqualNP.MetaComplexity.NestedCover.Ai
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.Aa.Ay
variable {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {A T : Finset (Fin n)} {C : Circuit}
lemma aU (K:SimpleGraph (Fin n)):
  ∃T:Finset (Fin n),IsMinCover K T:=by
 classical
 let P:=fun k:ℕ=>∃T:Finset (Fin n),K.IsVertexCover (T:Set (Fin n))∧T.card=k
 have b:∃k,P k:=⟨n,Finset.univ,by simp[SimpleGraph.IsVertexCover],by simp⟩
 obtain⟨T,c,a⟩:=Nat.find_spec b;refine⟨T,c,?_⟩;intro S d;rw[a];exact Nat.find_min' b (show P S.card from⟨S,d,rfl⟩)
lemma uC (x:Fin n→Bool):
  (∃e∈K.edgeFinset,∀v∈e,x v=true)↔
    ∃u v,K.Adj u v∧x u=true∧x v=true:=by
 constructor
 ·rintro⟨e,c,h⟩
  revert c h
  refine Sym2.ind (fun a b=> ?_) e;intro c h;rw[SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at c;exact⟨a,b,c,h a (Sym2.mem_mk_left _ _),h b (Sym2.mem_mk_right _ _)⟩
 ·rintro⟨i,j,d,g,k⟩;refine⟨s(i,j),by simpa using d,?_⟩;intro v f;rcases Sym2.mem_iff.1 f with rfl|rfl<;>assumption
lemma wT (g:K.IsVertexCover (T:Set (Fin n))) (f:K.edgeFinset.Nonempty):
  qQ n (fun x=>decide (∃u v,K.Adj u v∧x u=true∧x v=true)) (K.edgeFinset.card+T.card-1):=by
 have c:∀e∈K.edgeFinset,∃t∈T,t∈e:=by
  intro e;refine Sym2.ind (fun a b=> ?_) e;intro d;rw[SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at d;rcases g d with h|h
  ·exact⟨a,h,Sym2.mem_mk_left _ _⟩
  ·exact⟨b,h,Sym2.mem_mk_right _ _⟩
 exact cF (xR n T K.edgeFinset f c)
  (fun _=>decide_eq_decide.mpr (uC _))
lemma uD (k:K.IsVertexCover (T:Set (Fin n)))
  (l:A.Nonempty∨∃u v,K.Adj u v):
  ∃
   D:Circuit,FanInTwo D ∧(∀g∈D.gates,g.op≠GateOp.not)∧
   circuitFun n D =graphFun K A∧D.size+1≤A.card+K.edgeFinset.card+T.card:=by
 have c:A.Nonempty∨K.edgeFinset.Nonempty:=l.imp_right (by rintro⟨u,v,d⟩;exact⟨s(u,v),by simpa using d⟩);have q:qQ n (graphFun K A) (A.card+K.edgeFinset.card+T.card-1):=by
  by_cases a:A.Nonempty
  ·have j:=a.card_pos;by_cases b:K.edgeFinset.Nonempty
   ·have p:=b.card_pos;exact dI (vT (eD A a) (wT k b)) (by omega)
   ·refine dI (cF (eD A a) ?_) (by omega);intro x;have m:¬ ∃u v,K.Adj u v∧x u=true∧x v=true:=by
     rintro⟨u,v,d,_,_⟩;exact b ⟨s(u,v),by simpa using d⟩
    simp[graphFun,m]
  ·have b:=c.resolve_left a;refine dI (cF (wT k b) ?_) (by omega);rw[Finset.not_nonempty_iff_eq_empty] at a;intro x;simp[graphFun,a]
 obtain⟨D,e,i,f,o⟩:=nW q;have j:0<A.card+K.edgeFinset.card+T.card:=by rcases c with h|h<;>have:=h.card_pos<;>omega
 exact⟨D,e,i,f,by omega⟩
lemma gQ (e:K.IsAcyclic)
  (d:∀a∈A,∀v,¬K.Adj a v)
  (g:A.Nonempty∨∃u v,K.Adj u v)
  (i:IsMinCover K T) (b:FanInTwo C)
  (c:circuitFun n C=graphFun K A):
  A.card+K.edgeFinset.card+T.card≤Ap.eJ C+1:=by
 have h:=Ap.pE n C b;have f:graphFun K A=fun x:Fin n→Bool=>
   decide ((∃a∈A,x a=true)∨∃u v,K.Adj u v∧x u=true∧x v=true):=by
  funext x;rw[Bool.eq_iff_iff];simp[graphFun]
 rw[c,f] at h;exact As.eV n T.card _ K A e d g i.2 h
lemma nX (e:K.IsAcyclic)
  (d:∀a∈A,∀v,¬K.Adj a v)
  (f:A.Nonempty∨∃u v,K.Adj u v)
  (g:IsMinCover K T) (b:FanInTwo C)
  (c:circuitFun n C=graphFun K A):
  A.card+K.edgeFinset.card+T.card≤C.size+1:=by
 have i:=gQ e d f g b c;have h:=Ap.fH C;omega
lemma aK (j:K.IsAcyclic)
  (f:∀a∈A,∀v,¬K.Adj a v)
  (d:A.Nonempty∨∃u v,K.Adj u v)
  (i:IsMinCover K T) (c:IsMinimalCircuit n C)
  (b:circuitFun n C=graphFun K A):
  C.size+1=A.card+K.edgeFinset.card+T.card∧∀g∈C.gates,g.op≠GateOp.not:=by
 obtain⟨D,e,_,h,hBound⟩:=uD (A:=A) i.1 d;have p:=c.2 D e (h.trans b.symm);have q:=gQ j f d i c.1 b;have o:=Ap.fH C;have r:C.gates.countP Ap.iI=0:=by omega
 refine⟨by omega,?_⟩;intro g l k;have m:0<C.gates.countP Ap.iI:=List.countP_pos_iff.mpr ⟨g,l,(Ap.isNot_iff _).mpr k⟩;omega
end PEqualNP.MetaComplexity.NestedCover.Ai
namespace PEqualNP.MetaComplexity.NestedCover.Al
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Aa
open PEqualNP.MetaComplexity.Aa.Au
variable {n : ℕ} {C : Circuit}
lemma pN (x:Fin n→Bool) (h:n+C.size≤C.output):
  circuitFun n C x=false:=by
 rw[circuitFun,Circuit.eval,tW,List.getD_eq_default];simpa[Circuit.size,aV] using h
lemma nF (a:∃x y,circuitFun n C x≠circuitFun n C y):
  C.output<n+C.size:=by
 by_contra! h;obtain⟨x,y,b⟩:=a;exact b ((pN x h).trans (pN y h).symm)
lemma lP (gs:List Gate) (a:List Stat×List Gate):
  (elim n gs a).1.length=a.1.length+gs.length:=by
 induction gs generalizing a with
 | nil=>simp[elim]
 | cons g gs ih=>
   change(elim n gs (aI n a g)).1.length=_;rw[ih];simp[aI];omega
lemma pO (c:IsMinimalCircuit n C)
  (j:∃x y,circuitFun n C x≠circuitFun n C y):
  (elim n C.gates (aL n,[])).2.length=C.size:=by
 let a:=elim n C.gates (aL n,[])
 have g (x:Fin n→Bool):
   yR n (List.ofFn x) (aD C.gates (List.ofFn x)) a:=
  fL n _ (by simp) C.gates _ _ c.1 (sE n x)
 have hev (x:Fin n→Bool):
   (a.1.getD C.output (Stat.const false)).val (aD a.2 (List.ofFn x))=
     circuitFun n C x:=
  ((g x).2 C.output).2
 have h:a.2.length≤C.size:=by simpa[a,Circuit.size] using gP n C.gates (aL n,[])
 cases hs:a.1.getD C.output (Stat.const false) with
 | const b=>
   obtain⟨x,y,k⟩:=j;have d:=hev x;have l:=hev y;rw[hs,Stat.val] at d l;exact False.elim (k (d.symm.trans l))
 | cB i=>
   have f:circuitFun n ⟨a.2,i⟩=circuitFun n C:=by funext x;have d:=hev x;rw[hs,Stat.val] at d;exact d
   have e:FanInTwo ⟨a.2,i⟩:=wR n C.gates _ (by simp);exact Nat.le_antisymm h (c.2 _ e f)
lemma uE {g:Gate} {w:List Stat} {m:ℕ}
  (e:Ok g) (j:g.op≠GateOp.not)
  (c:(aH g.op m (g.inputs.map fun i=>w.getD i (Stat.const false))).1≠none):
  (g.op=GateOp.and∨g.op=GateOp.or)∧
    ∃a b,a<w.length∧b<w.length∧g.inputs=[a,b]:=by
 have d:g.op=GateOp.and∨g.op=GateOp.or:=by
  rcases e.1 with h|h|h
  ·exact Or.inl h
  ·exact Or.inr h
  ·exact False.elim (j h)
 have f:∀a∈g.inputs,a<w.length:=by intro a k;by_contra! hl;apply c;apply fK _ _ _ e.1 (by simpa using e.2) (fun h=>False.elim (j h));exact⟨false,List.mem_map.mpr ⟨a,k,List.getD_eq_default _ _ hl⟩⟩
 refine⟨d,?_⟩
 cases hins:g.inputs with
 | nil=>
   rcases d with h|h<;>simp[hins,h,aH,eC,gJ] at c
 | cons a as=>
   cases as with
   | nil=>
     rw[hins,List.map_cons,List.map_nil] at c
     cases hw:w.getD a (Stat.const false)<;>
      rw[hw] at c<;>rcases d with h|h<;>
      simp[h,aH,eC,gJ] at c
   | cons b bs=>
     have hl:=e.2;rw[hins] at hl;have l:bs=[]:=List.length_eq_zero_iff.mp (by simpa using hl);subst bs;exact⟨a,b,f a (by simp[hins]),f b (by simp[hins]),rfl⟩
lemma zE (h:IsMinimalCircuit n C)
  (v:∃x y,circuitFun n C x≠circuitFun n C y)
  (o:∀g∈C.gates,g.op≠GateOp.not):aW n C.gates:=by
 intro p g w;obtain⟨e,d,f,l⟩:=jC C.gates p g w;have u:g∈C.gates:=List.mem_of_getElem? w
 let c:=elim n e (aL n,[])
 have s:c.1.length=n+p:=by simp[c,lP,aL,l]
 have k:(aH g.op (n+c.2.length)
   (g.inputs.map fun i=>c.1.getD i (Stat.const false))).1≠none:=by
  intro B;have j:=pO h v;rw[f] at j;change(elim n (e++g::d) (aL n,[])).2.length=C.size at j;change((List.foldl (aI n) (aL n,[]) (e++g::d)).2.length=C.size) at j;rw[List.foldl_append,List.foldl_cons] at j;change(elim n d (aI n c g)).2.length=C.size at j;have z:(aI n c g).2.length=c.2.length:=by unfold aI;rw[B];simp
  have E:c.2.length≤e.length:=by simpa[c] using gP n e (aL n,[])
  have A:=gP n d (aI n c g);have F:C.size=e.length+(d.length+1):=by simp[Circuit.size,f]
  omega
 obtain⟨m,a,b,q,t,r⟩:=uE (h.1 g u) (o g u) k;rw[s] at q t;exact Or.inr ⟨m,a,b,q,t,r⟩
lemma gE {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {A:Finset (Fin n)} (b:A.Nonempty∨∃u v,K.Adj u v):
  graphFun K A (fun _=>false)≠graphFun K A (fun _=>true):=by
 rcases b with⟨a,d⟩|⟨u,v,c⟩
 ·have:∃a,a∈A:=⟨a,d⟩
  simp[graphFun,this]
 ·have:∃u v,K.Adj u v:=⟨u,v,c⟩
  simp[graphFun,this]
lemma least (a:IsMinimalCircuit n C)
  (d:∃x y,circuitFun n C x≠circuitFun n C y)
  (c:∀g∈C.gates,g.op≠GateOp.not):
  Ao n (circuitFun n C) C.gates C.output:=by
 refine⟨zE a d c,fun _=>rfl,?_⟩;intro gs o hcl e;have b:FanInTwo ⟨gs,o⟩:=fun g f=>(dS n gs hcl g f).1
 exact a.2 ⟨gs,o⟩ b (funext e)
lemma nY (j:IsMinimalCircuit n C)
  (f:∃x y,circuitFun n C x≠circuitFun n C y)
  (c:∀g∈C.gates,g.op≠GateOp.not)
  {p:ℕ} {g:Gate} (d:C.gates[p]?=some g):
  (g.op=GateOp.and∨g.op=GateOp.or)∧
    ∃a b,a<n+p∧b<n+p∧a≠b∧g.inputs=[a,b]:=by
 have L:=least j f c;rcases L.hcl p g d with⟨h,_⟩|⟨i,a,b,k,l,e⟩
 ·exact False.elim (c g (List.mem_of_getElem? d) h)
 refine⟨i,a,b,k,l,?_,e⟩;rintro rfl;apply L.no_alias f p (List.getElem?_eq_some_iff.mp d).1 a k;intro x;rw[eZ C.gates L.hcl x p g d,e];rcases i with h|h<;>simp[h,GateOp.eval]
lemma bM (a:IsMinimalCircuit n C)
  (c:∃x y,circuitFun n C x≠circuitFun n C y)
  (b:∀g∈C.gates,g.op≠GateOp.not):ReadsBack n C:=by
 intro j e;have d:C.gates[j]?=some (gateAt C j):=by simp[gateAt,e]
 exact(zE a c b _ _ d).lt
lemma uF (b:IsMinimalCircuit n C)
  (a:∃x y,circuitFun n C x≠circuitFun n C y)
  (c:∀g∈C.gates,g.op≠GateOp.not) (i:0<C.size):
  C.output=n+(C.size-1):=by
 have L:=least b a c;by_contra e;obtain⟨q,f,d⟩:=L.live a (C.size-1) (by change _<C.size;omega) e;have h:q<C.size:=dU d;omega
def cW (p:Fin n) (b:Bool):List Stat:=List.ofFn (fun i:Fin n=>if i=p then Stat.const b else Stat.cB i)
lemma sH (p:Fin n) (b:Bool) (x:Fin n→Bool):
  yR n (List.ofFn x) (List.ofFn (Function.update x p b)) (cW p b,[]):=by
 refine⟨by simp[cW],?_⟩;intro j;by_cases c:j<n
 ·let i:Fin n:=⟨j,c⟩
  change((cW p b).getD (i:ℕ) (Stat.const false)).Valid n∧
   ((cW p b).getD (i:ℕ) (Stat.const false)).val (List.ofFn x)=
     (List.ofFn (Function.update x p b)).getD (i:ℕ) false
  simp only[cW,Aa.dT];by_cases a:i=p
  ·simp[a,Stat.Valid,Stat.val]
  ·simp[a,Stat.Valid,Stat.val,Function.update_of_ne]
 ·rw[List.getD_eq_default _ _ (by simpa[cW] using Nat.le_of_not_gt c),
   List.getD_eq_default (List.ofFn (Function.update x p b)) _ (by simpa using Nat.le_of_not_gt c)]
  exact⟨trivial,rfl⟩
lemma kL (d:IsMinimalCircuit n C)
  (s:∃x y,circuitFun n C x≠circuitFun n C y)
  (m:∀g∈C.gates,g.op≠GateOp.not)
  (p:Fin n) (b:Bool)
  (o:∀x,circuitFun n C (Function.update x p b)=circuitFun n C x):
  ∀g∈C.gates,(p:ℕ)∉g.inputs:=by
 intro g f z
 let init:=(cW p b,([]:List Gate))
 let a:=elim n C.gates init
 have j:init.1.getD (p:ℕ) (Stat.const false)=Stat.const b:=by change(cW p b).getD (p:ℕ) (Stat.const false)=Stat.const b;simp[cW]
 have l:∀g∈C.gates,NOk g:=fun g f=>⟨d.1 g f,fun w=>False.elim (m g f w)⟩
 have v:a.2.length+1≤C.size:=by
  have h:=tY n p C.gates init l (by simp[init,cW])
   ⟨b,j⟩ ⟨g,f,z⟩
  simpa[a,init,Circuit.size] using h
 have hev (x:Fin n→Bool):
   (a.1.getD C.output (Stat.const false)).val (aD a.2 (List.ofFn x))=
     circuitFun n C x:=by
  rw[←o x];exact((fL n _ (by simp) C.gates _ init d.1 (sH p b x)).2 C.output).2
 cases hs:a.1.getD C.output (Stat.const false) with
 | const c=>
   obtain⟨x,y,t⟩:=s;have e:=hev x;have u:=hev y;rw[hs,Stat.val] at e u;exact t (e.symm.trans u)
 | cB i=>
   have q:circuitFun n ⟨a.2,i⟩=circuitFun n C:=by funext x;have e:=hev x;rw[hs,Stat.val] at e;exact e
   have k:FanInTwo ⟨a.2,i⟩:=wR n C.gates init (by simp[init]);have r:=d.2 _ k q;change C.size≤a.2.length at r;omega
end PEqualNP.MetaComplexity.NestedCover.Al
namespace PEqualNP.MetaComplexity.NestedCover.Ax
open PEqualNP.CircuitLowerBounds
def ws {n:ℕ} (C:Circuit) (k:ℕ) (x:Fin n→Bool):=(Circuit.mk (C.gates.take k) 0).wires (List.ofFn x)
def ev (g:Gate) (v:ℕ→Bool):=g.op.eval (g.inputs.map v)
lemma wU {n} (C:Circuit) {k:ℕ} (a:k<C.gates.length)
  (x:Fin n→Bool):
  ws C (k+1) x=ws C k x++[ev (gateAt C k) (fun i=>(ws C k x).getD i false)]:=by
 have b:gateAt C k=C.gates[k]:=List.getD_eq_getElem _ _ a;unfold ws Circuit.wires ev;simp only[List.take_succ_eq_append_getElem a,List.foldl_append,List.foldl_cons,List.foldl_nil,b]
lemma aB1 {n} (C:Circuit) {k:ℕ} (a:k≤C.gates.length)
  (x:Fin n→Bool):(ws C k x).length=n+k:=by
 induction k with
 | zero=>simp[ws,Circuit.wires]
 | succ k ih=>simp[wU C (by omega:k<C.gates.length),ih (by omega),Nat.add_assoc]
lemma pP {n} (C:Circuit) {k:ℕ} (b:k<C.gates.length)
  (x:Fin n→Bool) (w:ℕ):
  (ws C (k+1) x).getD w false=
    if w=n+k then ev (gateAt C k) (fun i=>(ws C k x).getD i false)
    else(ws C k x).getD w false:=by
 have a:=aB1 C b.le x;rw[wU C b]
 split_ifs with he
 ·subst w;simp[a]
 ·by_cases h:w<(ws C k x).length
  ·exact List.getD_append _ _ _ _ h
  ·rw[List.getD_eq_default _ _ (by simp[a];omega),List.getD_eq_default _ _ (by omega)]
noncomputable def gF (g:Gate) (z:ℕ→Bool):List ℕ:=by
 classical
 exact if(g.op= .and∧∀i,z i=false)∨g.op= .not then g.inputs.take 1 else g.inputs
lemma vU (g:Gate) (z:ℕ→Bool) (h:g.inputs.length≤2):
  (gF g z).length≤2:=by
 classical
 unfold gF
 split<;>simp_all
lemma sI (g:Gate) (z:ℕ→Bool) (b:∀i,z i=false)
  (basis:g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp))
  (h:(gF g z).length=2):g.op= .or∧gF g z=g.inputs:=by
 classical
 simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at basis;rcases basis with a|a|a<;>simp_all[gF]<;>omega
lemma pQ (g:Gate) (z y:ℕ→Bool)
  (b:ev g y≠ev g z):∃i∈gF g z,y i≠z i:=by
 classical
 by_contra! h;apply b;unfold gF at h
 split at h
 ·rename_i hs
  rcases hs with⟨a,c⟩|a
  ·rcases he:g.inputs with _|⟨i,e⟩
   ·simp[ev,he]
   ·have d:y i=false:=(h i (by simp[he])).trans (c i);simp[ev,he,a,GateOp.eval,d,c]
  ·rcases he:g.inputs with _|⟨i,e⟩
   ·simp[ev,he]
   ·simp[ev,he,a,GateOp.eval,h i (by simp[he])]
 ·unfold ev;rw[List.map_congr_left h]
def aA2 {n} (a:Fin n) (i:Fin n):Bool:=decide (i=a)
def jD (n:ℕ):Fin n→Bool:=fun _=>false
def jE {n} (A:Finset (Fin n)) (C:Circuit) (k:ℕ) (E:List ℕ):Prop:=∀a∈A,∃i∈E,(ws C k (aA2 a)).getD i false≠(ws C k (jD n)).getD i false
def pR {n} (A:Finset (Fin n)) (C:Circuit) (k:ℕ) (E:List ℕ):Prop:=
 k+E.length=A.card∧
 (0<k→n+(k-1)∈E)∧
 (∀i,(ws C k (jD n)).getD i false=false)∧
 (∀j<k,(gateAt C j).op= .or∧(gateAt C j).inputs.length=2∧
   ∀i∈(gateAt C j).inputs,i<n+j∧(i∈A.image Fin.val∨n≤ i))∧
 ∀
  i,readsIn C (Finset.range k) i+E.count i=
  if i∈A.image Fin.val∨n≤ i∧i<n+k then 1 else 0
lemma sJ {n} {A:Finset (Fin n)} {w:ℕ} (b:w∈A.image Fin.val):w<n:=by obtain⟨a,_,rfl⟩:=Finset.mem_image.mp b;exact a.isLt
lemma xS {n} (A:Finset (Fin n)) (C:Circuit) (E:List ℕ)
  (hs:jE A C 0 E) (s:E.length≤A.card):pR A C 0 E:=by
 have c:A.image Fin.val⊆E.toFinset:=by
  intro w p;obtain⟨a,k,rfl⟩:=Finset.mem_image.mp p;obtain⟨i,l,b⟩:=hs a k;change(List.ofFn (aA2 a)).getD i false≠(List.ofFn (jD n)).getD i false at b;by_cases e:i<n
  ·have m:i=a:=by
    by_contra h;have o:(⟨i,e⟩:Fin n)≠a:=by exact fun j=>h (congrArg Fin.val j)
    simp[e,aA2,jD,o] at b
   simpa[←m] using l
  ·simp[e] at b
 have g:(A.image Fin.val).card=A.card:=Finset.card_image_of_injective _ Fin.val_injective;have q:=Finset.card_le_card c;have r:=List.toFinset_card_le E;have d:=Finset.eq_of_subset_of_card_le c (by omega);have f:E.Nodup:=List.nodup_iff_length_dedup_eq.mpr (by rw[←List.card_toFinset];omega);refine⟨by omega,by simp,?_,by simp,?_⟩
 ·intro i;change(List.ofFn (jD n)).getD i false=false;by_cases h:i<n
  ·simp[h,jD]
  ·simp[h]
 ·intro i;by_cases h:i∈E
  ·simp[readsIn,d,List.count_eq_one_of_mem f h,h]
  ·simp[readsIn,d,List.count_eq_zero.mpr h,h]
lemma uG {n} (A:Finset (Fin n)) (C:Circuit) (fan:FanInTwo C)
  (k:ℕ) (M:k≤C.gates.length) (E:List ℕ) (hs:jE A C k E)
  (R:k+E.length≤A.card):pR A C k E:=by
 classical
 induction k generalizing E with
 | zero=>exact xS A C E hs (by omega)
 | succ k ih=>
   have b:k<C.gates.length:=M
   let N:=n+k
   let g:=gateAt C k
   let z:=fun i=>(ws C k (jD n)).getD i false
   let D:=gF g z
   have K:g∈C.gates:=by change C.gates.getD k _∈_;rw[List.getD_eq_getElem _ _ b];exact List.getElem_mem _
   obtain⟨basis,w⟩:=fan _ K;have v:=vU g z w;change D.length≤2 at v;have q:N∈E:=by
    by_contra B;have o:jE A C k E:=by
     intro a y;obtain⟨i,l,hh⟩:=hs a y;have F:i≠n+k:=fun e=>B (show n+k∈E by rwa [←e])
     exact⟨i,l,by simpa only[pP C b,ite_eq_right F] using hh⟩
    have:=(ih b.le E o (by omega)).1;omega
   let E':=E.erase N++D
   have o:jE A C k E':=by
    intro a y;obtain⟨i,l,hh⟩:=hs a y;by_cases f:i=N
    ·subst i;rw[pP C b,pP C b,ite_eq_left rfl,ite_eq_left rfl] at hh;obtain⟨u,G,r⟩:=pQ _ _ _ hh;exact⟨u,List.mem_append_right _ G,r⟩
    ·change i≠n+k at f;exact⟨i,List.mem_append_left _ ((List.mem_erase_of_ne f).mpr l),by simpa only[pP C b,ite_eq_right f] using hh⟩
   have P:=List.length_pos_of_mem q;have O:E'.length=E.length-1+D.length:=by simp[E',q]
   obtain⟨Q,_,d,x,c⟩:=ih b.le E' o (by omega);have H:D.length=2:=by omega
   obtain⟨t,p⟩:=sI g z d basis H;change D =g.inputs at p;have s:∀i∈g.inputs,i<N∧(i∈A.image Fin.val∨n≤ i):=by
    intro i l;have B:i∈E':=List.mem_append_right _ (p▸l:i∈D);have J:=List.count_pos_iff.mpr B;have m:=c i
    split at m
    ·rename_i G
     rcases G with h|h
     ·have:=sJ h;exact⟨by dsimp[N];omega,Or.inl h⟩
     ·exact⟨h.2,Or.inr h.1⟩
    ·omega
   refine⟨by omega,fun _=>by simpa[N] using q,?_,?_,?_⟩
   ·intro i;rw[pP C b]
    split
    ·change ev g z=false;simp[ev,t,GateOp.eval,show ∀i,z i=false from d]
    ·exact d i
   ·intro j S;by_cases f:j=k
    ·subst j;exact⟨t,(congrArg List.length p).symm.trans H,s⟩
    ·exact x j (by omega)
   ·intro i;have hh:=c i;change readsIn C _ i+(E.erase N++D).count i=_ at hh;rw[List.count_append,p] at hh;rw[readsIn,Finset.sum_range_succ];change readsIn C (Finset.range k) i+g.inputs.count i+E.count i=_;by_cases f:i=N
    ·subst i;have F:N∉A.image Fin.val:=fun h=>by have:=sJ h;dsimp[N] at*;omega
     have J:=List.count_pos_iff.mpr q;simp only[List.count_erase_self,F,false_or,N,Nat.lt_irrefl,and_false,ite_false] at hh;have:n≤N∧N<n+(k+1):=by dsimp[N];omega
     rw[ite_eq_left (Or.inr this)];dsimp only[N] at J ⊢
     omega
    ·rw[List.count_erase_of_ne f] at hh;have l:i<n+(k+1)↔i<n+k:=by dsimp[N] at f;omega
     simpa only[l,add_assoc,add_left_comm,add_comm] using hh
lemma vV {n:ℕ} {A:Finset (Fin n)} {C:Circuit}
  (fan:FanInTwo C) (t:∀a∈A,
    circuitFun n C (fun i=>decide (i=a))≠circuitFun n C (fun _=>false))
  (r:C.size+1≤A.card):
  ReadsBack n C∧IsOrTree n C (Finset.range C.gates.length) (A.image Fin.val) C.output:=by
 have hs:jE A C C.gates.length [C.output]:=by intro a y;refine⟨C.output,by simp,?_⟩;have hh:circuitFun n C (aA2 a)≠circuitFun n C (jD n):=t a y;simpa only[ws,List.take_length,circuitFun,Circuit.eval,Circuit.wires] using hh
 have h:=uG A C fan C.gates.length le_rfl [C.output] hs (by simpa[Circuit.size] using r);obtain⟨x,p,_,e,b⟩:=h;have d (i:ℕ) (k:i∈A.image Fin.val∨n≤ i∧i<n+C.gates.length):
   readsIn C (Finset.range C.gates.length) i=if i=C.output then 0 else 1:=by
  have hh:=b i;rw[ite_eq_left k] at hh;by_cases g:i=C.output
  ·subst i;simpa using hh
  ·simpa[g,Ne.symm g] using hh
 refine⟨fun j l i k=>(e j l).2.2 i k |>.1,?_,?_,?_,?_⟩
 ·intro j l;have u:=Finset.mem_range.mp l;obtain⟨v,c,o⟩:=e j u;refine⟨v,c,?_⟩;intro i k;obtain⟨z,h⟩:=o i k;exact h.imp_right fun m=>⟨m,Finset.mem_range.mpr (by omega)⟩
 ·intro w q;have z:=sJ q;exact⟨by omega,d w (.inl q)⟩
 ·intro j l;have u:=Finset.mem_range.mp l;have f:n≤n+j∧n+j<n+C.gates.length:=by omega
  exact d _ (.inr f)
 ·split_ifs with g
  ·have c:C.gates.length=0:=by simpa using g
   have s:C.output∈A.image Fin.val:=by by_contra m;have hh:=b C.output;simp[c,m,readsIn] at hh
   exact Finset.eq_singleton_iff_unique_mem.mpr ⟨s,by intro w q;have hh:=b w;by_contra m;simp[c,q,readsIn,Ne.symm m] at hh⟩
  ·have c:0<C.gates.length:=by
    by_contra! hh;exact g (by simp[Nat.le_zero.mp hh])
   exact⟨C.gates.length-1,Finset.mem_range.mpr (by omega),by simpa[eq_comm] using p c⟩
def hR (n:ℕ):NCCData n:=
 ⟨∅,fun _ _=>false,fun _=>none,fun _=>(.top,0),
   fun _=>0,fun _=>0,fun _=>0,fun _ _=>0⟩
lemma pS {n:ℕ} {A:Finset (Fin n)} {K:SimpleGraph (Fin n)}
  {C:Circuit} (empty:∀u v,¬K.Adj u v)
  (back:ReadsBack n C) (a:IsOrTree n C (Finset.range C.gates.length)
    (A.image Fin.val) C.output):IsNestedCoverCircuit n K A C:=by
 refine⟨hR n,back,⟨fun u v h=>(empty u v h).elim,by simp[hR]⟩,⟨by simp[hR],fun u v h=>(empty u v h).elim⟩,?_,?_,?_,?_⟩
 ·simp[TieOK,hR]
 ·simp[RolesOK,hR]
 ·simp[hR]
 ·simpa[hR,topGates,topLeaves] using a
end PEqualNP.MetaComplexity.NestedCover.Ax
namespace PEqualNP.MetaComplexity.NestedCover.Ax
open PEqualNP.CircuitLowerBounds Aa.Ay
lemma nG {n:ℕ} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {A:Finset (Fin n)} {C:Circuit} (empty:∀u v,¬K.Adj u v)
  (nonempty:A.Nonempty) (b:IsMinimalCircuit n C)
  (output:circuitFun n C=graphFun K A):IsNestedCoverCircuit n K A C:=by
 have d:circuitFun n C=fun x=>decide (∃a∈A,x a=true):=by funext x;simp[output,graphFun,empty]
 obtain⟨D,e,_,h,f⟩:=nW (eD A nonempty);have hmin:=b.2 D e (h.trans d.symm);have i:=nonempty.card_pos;have c:=vV b.1 (A:=A) (by intro a g;simp[d,g]) (by omega);exact pS empty c.1 c.2
end PEqualNP.MetaComplexity.NestedCover.Ax
namespace PEqualNP.MetaComplexity.NestedCover.Ax
open PEqualNP.CircuitLowerBounds
def cX {n:ℕ} (l p:Fin n):NCCData n:=
 ⟨{l},fun i j=>decide (i=l∧j=p),fun _=>none,fun _=>(.b,l.val),
   fun _=>n,fun _=>l.val,fun _=>p.val,fun _ j=>j.val⟩
lemma cR {n:ℕ} (C:Circuit) (w:ℕ):IsOrTree n C ∅ {w} w:=by simp[IsOrTree,readsIn]
lemma vW {n:ℕ} {l p:Fin n} {K:SimpleGraph (Fin n)} {C:Circuit}
  (b:l≠p) (c:K.Adj l p) (only:∀i j,K.Adj i j→i=l∧j=p∨i=p∧j=l)
  (d:IsMinCover K {l}) (back:ReadsBack n C) (g:C.gates.length=1)
  (out:C.output=n) (op:(gateAt C 0).op= .and)
  (inputs:(gateAt C 0).inputs=[l.val,p.val]∨(gateAt C 0).inputs=[p.val,l.val]):
  IsNestedCoverCircuit n K ∅ C:=by
 refine⟨cX l p,back,d,⟨?_,?_⟩,?_,?_,?_,?_⟩
 ·intro i j h;obtain⟨rfl,rfl⟩:i=l∧j=p:=by simpa[cX] using h
  exact⟨c,Finset.mem_singleton_self _⟩
 ·intro i j h;rcases only i j h with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>simp[cX,b,Ne.symm b]
 ·simp[TieOK,cX]
 ·intro j k;have f:j=0:=by omega
  subst j;exact .inr ⟨l,Finset.mem_singleton_self _,rfl,fun _=>by simp[cX]⟩
 ·intro t ht;have e:t=l:=by simpa[cX] using ht
  subst t;refine⟨⟨0,by omega,by simp[cX],rfl,op,inputs⟩,?_,?_,?_⟩
  ·simpa[gatesOf,zLeaves,cX] using cR (n:=n) C l.val
  ·have a:(Finset.univ.filter (fun x:Fin n=>x=p))={p}:=by ext i;simp
   simpa[gatesOf,oLeaves,cX,a] using cR (n:=n) C p.val
  ·intro r hr;have e:r=p:=by simpa[cX] using hr
   subst r;simp[cX,LamOK,Ne.symm b]
 ·simpa[topGates,topLeaves,cX,out] using cR (n:=n) C n
lemma fM {n:ℕ} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {C:Circuit} {l p:Fin n} (H:K.IsAcyclic) (c:K.Adj l p)
  (one:K.edgeFinset.card=1)
  (a:IsMinimalCircuit n C) (output:circuitFun n C=graphFun K ∅):
  IsNestedCoverCircuit n K ∅ C:=by
 have only(i j:Fin n) (h:K.Adj i j):i=l∧j=p∨i=p∧j=l:=by
  obtain⟨e,S⟩:=Finset.card_eq_one.mp one;apply Sym2.eq_iff.mp;have G:s(i,j)∈K.edgeFinset:=by simpa using h
  have J:s(l,p)∈K.edgeFinset:=by simpa using c
  rw[S,Finset.mem_singleton] at G J;exact G.trans J.symm
 have t:IsMinCover K {l}:=by
  constructor
  ·intro i j h;rcases only i j h with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>simp
  ·intro T R;have E:T.Nonempty:=by
    rcases R c with h|h
    ·exact⟨_,h⟩
    ·exact⟨_,h⟩
   simpa using E.card_pos
 have d (x:Fin n→Bool):circuitFun n C x=(x l && x p):=by
  rw[output,Bool.eq_iff_iff];simp only[graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq,Bool.and_eq_true];constructor
  ·rintro⟨i,j,h,M,hj⟩;rcases only i j h with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>exact⟨by assumption,by assumption⟩
  ·rintro⟨hl,F⟩;exact⟨_,_,c,hl,F⟩
 have f:∃x y,circuitFun n C x≠circuitFun n C y:=⟨fun _=>false,fun _=>true,by simp[d]⟩
 obtain⟨sz,uM⟩:=Ai.aK H (by simp)
  (Or.inr ⟨l,p,c⟩) t a output
 have A:C.size=1:=by simpa[one] using sz
 have z:C.gates.length=1:=A;obtain⟨g,q⟩:=List.length_eq_one_iff.mp z;have F:C.gates[0]?=some g:=by simp[q]
 have w:gateAt C 0=g:=by simp[gateAt,q]
 have m:C.output=n:=by simpa[A] using Al.uF a f uM (by omega)
 obtain⟨N,u,v,X,Z,a0,k⟩:=Al.nY a f uM F;have b (i:ℕ) (M:i<n) (V:i∈g.inputs):i=l.val∨i=p.val:=by
  by_contra! hh
  let r:Fin n:=⟨i,M⟩
  have hl:l≠r:=fun h=>hh.1 (congrArg Fin.val h.symm)
  have Q:p≠r:=fun h=>hh.2 (congrArg Fin.val h.symm)
  exact Al.kL a f uM r false
   (by intro x;simp[d,Function.update_of_ne hl,Function.update_of_ne Q])
   g (by simp[q]) V
 have o:g.inputs=[l.val,p.val]∨g.inputs=[p.val,l.val]:=by
  rcases b u (by simpa using X) (by simp[k]) with h|h<;>
  rcases b v (by simpa using Z) (by simp[k]) with P|P<;>
  simp_all
 have B:g.op=GateOp.and:=by apply N.resolve_right;intro O;have U:=d (fun i=>decide (i=l));have E:=c.ne;rcases o with h|h<;>simp[circuitFun,Circuit.eval,Circuit.wires,m,q,h,O,GateOp.eval,Ne.symm E] at U
 apply vW c.ne c only t (Al.bM a f uM) z m
 ·simpa[w] using B
 ·simpa[w] using o
lemma kM {n:ℕ} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {C:Circuit} (b:K.IsAcyclic) (one:K.edgeFinset.card=1)
  (a:IsMinimalCircuit n C) (output:circuitFun n C=graphFun K ∅):
  IsNestedCoverCircuit n K ∅ C:=by
 have f:K.edgeFinset.Nonempty:=Finset.card_pos.mp (by omega);obtain⟨e,d⟩:=f
 revert d
 refine Sym2.ind (fun u v=> ?_) e;intro c;exact fM b (by simpa using c:K.Adj u v) one a output
end PEqualNP.MetaComplexity.NestedCover.Ax
namespace Aq
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover SimpleGraph
variable {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj] {A : Finset (Fin n)}
  {l p q : Fin n} {C D : Circuit}
lemma hV (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]:G.edgeFinset.card=G.edgeSet.ncard:=by rw[←Set.ncard_coe_finset,coe_edgeFinset]
lemma xT (leaf:bC K l p) (a:∀T,IsMinCover K T→l∉T):
  nE (K.deleteIncidenceSet l) A:=by
 by_contra b;have e:=(leaf p).2 rfl;have f:K.IsVertexCover (({l}:Finset (Fin n)):Set (Fin n)):=by
  intro u v h;by_contra! g;have c:u≠l:=by simpa using g.1
  have d:v≠l:=by simpa using g.2
  exact b (Or.inr ⟨u,v,deleteIncidenceSet_adj.mpr ⟨h,c,d⟩⟩)
 apply a {l} ⟨f,?_⟩ (Finset.mem_singleton_self l);intro S hs;have pos:S.Nonempty:=(hs e).elim (fun h=>⟨l,h⟩) (fun h=>⟨p,h⟩);simpa using pos.card_pos
def zG (C:Circuit) (l:Fin n) (b:Bool) (k:ℕ):=
 ∀
  D:Circuit,FanInTwo D→
  circuitFun n D =(fun x=>circuitFun n C (Function.update x l b))→C.size≤D.size+k
lemma hW (c:cK K A):cK (K.deleteIncidenceSet l) A:=fun a b v h=>c a b v (deleteIncidenceSet_le _ _ h)
lemma rN (c:cK K A):cK ((K.deleteIncidenceSet l).deleteIncidenceSet p)
  (insert p A):=by
 intro a b v h;rcases Finset.mem_insert.mp b with rfl|b
 ·exact(deleteIncidenceSet_adj.mp h).2.1 rfl
 ·exact c a b v (deleteIncidenceSet_le _ _ (deleteIncidenceSet_le _ _ h))
lemma nZ (leaf:bC K l p) (f:K.IsAcyclic) (iso:cK K A)
  (e:nE (K.deleteIncidenceSet l) A) (q:IsMinimalCircuit n C)
  (i:circuitFun n C=graphFun K A) {k:ℕ}
  (gap:∀T S,IsMinCover K T→IsMinCover (K.deleteIncidenceSet l) S→
    T.card+1≤S.card+k):zG C l false k:=by
 obtain⟨T,h⟩:=Ai.aU K;obtain⟨S,g⟩:=Ai.aU (K.deleteIncidenceSet l);have b:=(leaf p).2 rfl;have c:=(Ai.aK f iso (Or.inr ⟨_,_,b⟩) h q i).1;intro E o j;have m:circuitFun n E=graphFun (K.deleteIncidenceSet l) A:=j.trans (by funext x;rw[i];exact eA leaf iso x);have d:=Ai.nX (f.anti (deleteIncidenceSet_le _ _)) (hW iso) e g o m;have a:=PEqualNP.MetaComplexity.Aa.Ak.fG K l p b;rw[←bP leaf] at a;simp only[hV] at c d;have:=gap _ _ h g;omega
lemma vX (leaf:bC K l p) (e:∀v,K.Adj p v→v=l∨v=q)
  (f:K.IsAcyclic) (iso:cK K A) (o:IsMinimalCircuit n C)
  (i:circuitFun n C=graphFun K A):zG C l true 2:=by
 obtain⟨T,h⟩:=Ai.aU K;obtain⟨S,g⟩:=Ai.aU ((K.deleteIncidenceSet l).deleteIncidenceSet p);have a:=(leaf p).2 rfl;have c:=(Ai.aK f iso (Or.inr ⟨_,_,a⟩) h o i).1;intro E m j;have k:circuitFun n E=graphFun ((K.deleteIncidenceSet l).deleteIncidenceSet p) (insert p A):=j.trans (by funext x;rw[i];exact(iK leaf iso e x).2);have d:=Ai.nX (f.anti ((deleteIncidenceSet_le _ _).trans
  (deleteIncidenceSet_le _ _))) (rN iso) (Or.inl (Finset.insert_nonempty _ _)) g m k
 have b:=(PEqualNP.MetaComplexity.Aa.Ak.pD K l p q a).1;rw[←gC leaf e] at b;simp only[hV] at c d;have s:=Finset.card_insert_of_notMem (fun r=>iso p r l a.symm);have:=jB leaf h g;omega
lemma jF (leaf:bC K l p) (i:K.IsAcyclic) (iso:cK K A)
  (g:nE (K.deleteIncidenceSet l) A) (r:IsMinimalCircuit n C)
  (q:circuitFun n C=graphFun K A) (s:IsMinimalCircuit n D)
  (m:circuitFun n D =graphFun (K.deleteIncidenceSet l) A) (size:D.size+2=C.size)
  {S:Finset (Fin n)} (hs:IsMinCover (K.deleteIncidenceSet l) S):p∉S:=by
 intro j;have k:K.IsVertexCover (S:Set (Fin n)):=by
  intro u v h;by_cases e:u=l
  ·exact Or.inr ((leaf v).1 (e▸h)▸j)
  by_cases f:v=l
  ·exact Or.inl ((leaf u).1 (f▸h.symm)▸j)
  exact hs.1 (deleteIncidenceSet_adj.mpr ⟨h,e,f⟩)
 have t:IsMinCover K S:=⟨k,fun T o=>hs.2 T (fun _ _ h=>o (deleteIncidenceSet_le _ _ h))⟩
 have b:=(leaf p).2 rfl;have c:=(Ai.aK i iso (Or.inr ⟨_,_,b⟩) t r q).1;have d:=(Ai.aK (i.anti (deleteIncidenceSet_le _ _)) (hW iso)
  g hs s m).1
 have a:=PEqualNP.MetaComplexity.Aa.Ak.fG K l p b;rw[←bP leaf] at a;simp only[hV] at c d;omega
lemma hX (leaf:bC K l p) (f:K.IsAcyclic) (iso:cK K A)
  (o:IsMinimalCircuit n C) (m:circuitFun n C=graphFun K A) (r:IsMinimalCircuit n D)
  (k:circuitFun n D =graphFun ((K.deleteIncidenceSet l).deleteIncidenceSet p) (insert p A))
  (size:D.size+2=C.size):∃v,K.Adj p v∧v≠l:=by
 by_contra! i;have j:(K.deleteIncidenceSet l).deleteIncidenceSet p=K.deleteIncidenceSet l:=by
  ext u v;constructor
  ·exact fun ev=>(deleteIncidenceSet_adj.mp ev).1
  ·intro ev;obtain⟨a,s,vl⟩:=deleteIncidenceSet_adj.mp ev;exact deleteIncidenceSet_adj.mpr ⟨ev,fun e=>vl (i v (e▸a)),fun e=>s (i u (e▸a.symm))⟩
 obtain⟨T,h⟩:=Ai.aU K;obtain⟨S,g⟩:=Ai.aU ((K.deleteIncidenceSet l).deleteIncidenceSet p);have a:=(leaf p).2 rfl;have c:=(Ai.aK f iso (Or.inr ⟨_,_,a⟩) h o m).1;have d:=(Ai.aK (f.anti ((deleteIncidenceSet_le _ _).trans
  (deleteIncidenceSet_le _ _))) (rN iso) (Or.inl (Finset.insert_nonempty _ _)) g r k).1
 have b:=PEqualNP.MetaComplexity.Aa.Ak.fG K l p a;rw[←bP leaf] at b;simp only[hV] at c d;rw[j] at d;have:=Finset.card_insert_of_notMem (fun q=>iso p q l a.symm);have:=jB leaf h g;omega
lemma uH (leaf:bC K l p) (u v:Fin n):
  K.Adj u v↔(K.deleteIncidenceSet l).Adj u v∨(u=p∧v=l)∨(u=l∧v=p):=by
 rw[deleteIncidenceSet_adj];have lp:=(leaf p).2 rfl;constructor
 ·intro h;by_cases a:u=l
  ·exact Or.inr (Or.inr ⟨a,(leaf v).1 (a▸h)⟩)
  by_cases b:v=l
  ·exact Or.inr (Or.inl ⟨(leaf u).1 (b▸h.symm),b⟩)
  exact Or.inl ⟨h,a,b⟩
 ·rintro(⟨h,_⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  ·exact h
  ·exact lp.symm
  ·exact lp
end Aq
namespace Aq
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover SimpleGraph
def hY {n} (K:SimpleGraph (Fin n)) (A:Finset (Fin n)):Prop:=
 ∀
  (dec:DecidableRel K.Adj) (C:Circuit),IsMinimalCircuit n C→
  circuitFun n C=@graphFun n K dec A→IsNestedCoverCircuit n K A C
def uI (n:ℕ):Prop:=
 ∀
  (K:SimpleGraph (Fin n)) A l p,K.IsAcyclic→cK K A→bC K l p→
  (∀T,IsMinCover K T→l∉T)→hY (K.deleteIncidenceSet l) A→hY K A
def wV (n:ℕ):Prop:=
 ∀
  (K:SimpleGraph (Fin n)) A l p q,K.IsAcyclic→cK K A→bC K l p→
  (∀v,K.Adj p v→v=l∨v=q)→nE (K.deleteIncidenceSet l) A→
  hY (K.deleteIncidenceSet l) A→
  hY ((K.deleteIncidenceSet l).deleteIncidenceSet p) (insert p A)→hY K A
lemma eQ {n} (free:uI n) (g:wV n)
  (K:SimpleGraph (Fin n)) [DecidableRel K.Adj] (A:Finset (Fin n))
  (f:K.IsAcyclic) (r:cK K A) (s:nE K A) (C:Circuit):
  (IsMinimalCircuit n C∧circuitFun n C=graphFun K A)↔IsNestedCoverCircuit n K A C:=by
 have induction:hY K A:=by
  refine jA hY ?_ free ?_ ?_ K A f r s
  ·intro G B a u dec D o m
   letI:=dec
   exact Ax.nG a u o m
  ·intro G B l p q d iso leaf x k left right;have pq:=(k q).2 (Or.inr rfl);have lp:=(leaf p).2 rfl;exact g G B l p q d iso leaf (fun v=>(k v).1) (Or.inr ⟨p,q,deleteIncidenceSet_adj.mpr ⟨pq,lp.ne.symm,x⟩⟩) left right
  ·intro G B l p d iso leaf e left right
   classical
   by_cases b:nE (G.deleteIncidenceSet l) B
   ·exact g G B l p l d iso leaf (fun v t=>Or.inl ((e v).1 t)) b (left b) right
   ·have y:B= ∅ :=Finset.not_nonempty_iff_eq_empty.mp (fun h=>b (Or.inl h));have a:∀i j,¬(G.deleteIncidenceSet l).Adj i j:=
     fun i j h=>b (Or.inr ⟨i,j,h⟩)
    have c:G.edgeSet.ncard=1:=by have w:=PEqualNP.MetaComplexity.Aa.Ak.hM _ a;rw[bP leaf] at w;have:=PEqualNP.MetaComplexity.Aa.Ak.fG G l p ((leaf p).2 rfl);omega
    subst B;intro dec D o m
    letI:=dec
    exact Ax.kM d (by rwa [←Set.ncard_coe_finset,coe_edgeFinset]) o m
 exact⟨fun h=>induction inferInstance C h.1 h.2,mJ f r s⟩
end Aq
namespace PEqualNP.MetaComplexity.Aa
open PEqualNP.CircuitLowerBounds
lemma rO (n:ℕ) (g:Gate) (gs:List Gate) (a:List Stat×List Gate):elim n (g::gs) a=elim n gs (aI n a g):=rfl
lemma oA (n:ℕ) (c a:List Gate) (b:List Stat×List Gate):
  elim n (c++a) b=elim n a (elim n c b):=by
 simp[elim,List.foldl_append]
lemma hZ (n:ℕ) (gs:List Gate):∀a:List Stat×List Gate,
  (elim n gs a).1.length=a.1.length+gs.length:=by
 induction gs with
 | nil=>intro a;rfl
 | cons g gs ih=>
   intro a;rw[rO,ih];simp only[aI,List.length_append,List.length_cons,List.length_nil];omega
lemma pT (op:GateOp) (m:ℕ) (bS:List Stat)
  (g:op=GateOp.and∨op=GateOp.or∨op=GateOp.not) (i:bS.length≤2)
  (hnot:op=GateOp.not→bS.length≤1) (b:Bool)
  (f:op=GateOp.and→b=false) (h:op=GateOp.or→b=true)
  (j:Stat.const b∈bS):∃c,(aH op m bS).2=Stat.const c:=by
 rcases g with rfl|rfl|rfl
 ·have:=f rfl;subst this;rcases bS with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩<;>(try cases a)<;>(try cases d)<;>simp_all[aH,eC]
 ·have:=h rfl;subst this;rcases bS with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩<;>(try cases a)<;>(try cases d)<;>simp_all[aH,gJ]
 ·have:=hnot rfl;rcases bS with _|⟨a,_|⟨d,l⟩⟩<;>(try cases a)<;>simp_all[aH,hO]
lemma qR (n:ℕ) (a:List Stat×List Gate) (g:Gate) (d:NOk g) (k:ℕ)
  (f:k∈g.inputs) (c:Bool) (e:a.1.getD k (Stat.const false)=Stat.const c):
  (aI n a g).2.length=a.2.length:=by
 have b:(aH g.op (n+a.2.length)
   (g.inputs.map fun i=>a.1.getD i (Stat.const false))).1=none:=by
  apply fK
  ·exact d.1.1
  ·simpa using d.1.2
  ·intro h;simpa using d.2 h
  ·exact⟨c,List.mem_map.2 ⟨k,f,e⟩⟩
 show(a.2++(aH g.op (n+a.2.length)
  (g.inputs.map fun i=>a.1.getD i (Stat.const false))).1.toList).length=_
 rw[b];simp
def eR (g:Gate):Bool:=
 match g.op with
 | GateOp.or=>true
 | _=>false
lemma pU (n:ℕ) (a:List Stat×List Gate) (g:Gate) (b:NOk g) (k:ℕ)
  (f:k∈g.inputs) (d:a.1.getD k (Stat.const false)=Stat.const (eR g)):
  ∃c,(aI n a g).1.getD a.1.length (Stat.const false)=Stat.const c:=by
 have e:(aI n a g).1.getD a.1.length (Stat.const false)
  =
   (aH g.op (n+a.2.length)
   (g.inputs.map fun i=>a.1.getD i (Stat.const false))).2:=bR _ _ _
 rw[e];apply pT _ _ _ b.1.1 (by simpa using b.1.2) (fun h=>by simpa using b.2 h) (eR g)
 ·intro h;simp[eR,h]
 ·intro h;simp[eR,h]
 ·exact List.mem_map.2 ⟨k,f,d⟩
def bH (n:ℕ) (i:Fin (n+1)) (b:Bool):List Stat:=List.ofFn (Fin.insertNth i (Stat.const b) (fun k:Fin n=>Stat.cB k):Fin (n+1)→Stat)
lemma eE (n:ℕ) (i:Fin (n+1)) (b:Bool):(bH n i b).length=n+1:=by simp[bH]
lemma rP (n:ℕ) (i:Fin (n+1)) (b:Bool):
  (bH n i b).getD i (Stat.const false)=Stat.const b:=by
 rw[bH,dT,Fin.insertNth_apply_same]
lemma sK (n:ℕ) (i:Fin (n+1)) (b:Bool) (k:Fin n):
  (bH n i b).getD (i.succAbove k) (Stat.const false)=Stat.cB k:=by
 rw[bH,dT,Fin.insertNth_apply_succAbove]
lemma zH (n:ℕ) (i:Fin (n+1)) (b:Bool) (y:Fin n→Bool):
  yR n (List.ofFn y) (List.ofFn (Fin.insertNth i b y:Fin (n+1)→Bool))
   (bH n i b,[]):=by
 refine⟨by simp[bH],?_⟩;have c:∀j:Fin (n+1),
   ((bH n i b).getD j (Stat.const false)).Valid (n+0)∧
   ((bH n i b).getD j (Stat.const false)).val (List.ofFn y)
     =(List.ofFn (Fin.insertNth i b y:Fin (n+1)→Bool)).getD j false:=by
  intro j;rcases Fin.eq_self_or_eq_succAbove i j with rfl|⟨k,rfl⟩
  ·rw[rP,dT,Fin.insertNth_apply_same];exact⟨trivial,rfl⟩
  ·rw[sK,dT,Fin.insertNth_apply_succAbove];refine⟨?_,?_⟩
   ·show(k:ℕ)<n+0
    have:=k.isLt;omega
   ·show(List.ofFn y).getD k false=y k
    exact dT n y false k
 intro j;by_cases a:j<n+1
 ·exact c ⟨j,a⟩
 ·show((bH n i b).getD j (Stat.const false)).Valid (n+0)∧
   ((bH n i b).getD j (Stat.const false)).val (List.ofFn y)
     =(List.ofFn (Fin.insertNth i b y:Fin (n+1)→Bool)).getD j false
  rw[List.getD_eq_default _ _ (by rw[eE];omega),List.getD_eq_default _ _ (by simp;omega)];exact⟨trivial,rfl⟩
def stF (n:ℕ) (gs:List Gate) (i:Fin (n+1)) (b:Bool) (a:ℕ):Stat:=(elim n gs (bH n i b,[])).1.getD a (Stat.const false)
lemma uJ (n:ℕ) (gs:List Gate) (i:Fin (n+1)) (b:Bool):
  stF n gs i b i=Stat.const b:=by
 show(elim n gs (bH n i b,[])).1.getD i (Stat.const false)=_
 rw[rK n i _ gs _ (by
  show(i:ℕ)<(bH n i b).length
  rw[eE];exact i.isLt)]
 exact rP n i b
lemma iL (n:ℕ) (c:List Gate) (g:Gate) (e:List Gate)
  (b:List Stat×List Gate) (a:ℕ) (d:Stat) (h:a≤b.1.length+c.length):
  (elim n (c++g::e) b).1.getD a d=(aI n (elim n c b) g).1.getD a d:=by
 rw[oA,rO,rK n a d e _ (by
  show a<((elim n c b).1++[_]).length
  rw[List.length_append,hZ,List.length_singleton];omega)]
lemma fN (n:ℕ) (c:List Gate) (g:Gate) (e:List Gate)
  (b:List Stat×List Gate) (a:ℕ) (d:Stat) (h:a<b.1.length+c.length):
  (elim n (c++g::e) b).1.getD a d=(elim n c b).1.getD a d:=by
 rw[iL n c g e b a d (le_of_lt h)]
 show((elim n c b).1++[_]).getD a d=_
 exact bQ _ _ _ _ (by rw[hZ];omega)
lemma qS (n:ℕ) (gs:List Gate) (b:List Stat×List Gate) (p:ℕ) (g:Gate)
  (l:gs[p]?=some g) (k:NOk g) (a:ℕ) (j:a∈g.inputs)
  (i:a<b.1.length+p)
  (h:(elim n gs b).1.getD a (Stat.const false)=Stat.const (eR g)):
  ∃c,(elim n gs b).1.getD (b.1.length+p) (Stat.const false)=Stat.const c:=by
 obtain⟨e,d,rfl,rfl⟩:=jC gs p g l;rw[fN n e g d b a _ i] at h;obtain⟨c,f⟩:=pU n (elim n e b) g k a j h;refine⟨c,?_⟩;rw[iL n e g d b _ _ (le_refl _)];rw[hZ] at f;exact f
lemma vY (n:ℕ) (b:List Stat×List Gate):∀gs:List Gate,
  (∀g∈gs,NOk g)→∀S:Finset ℕ,
  (∀p∈S,∃g,gs[p]?=some g∧∃a∈g.inputs,a<b.1.length+p∧
      ∃c,(elim n gs b).1.getD a (Stat.const false)=Stat.const c)→
    (elim n gs b).2.length+S.card≤b.2.length+gs.length:=by
 intro gs
 induction gs using List.reverseRecOn with
 | nil=>
   intro _ S o;have C:S= ∅ :=by apply Finset.eq_empty_of_forall_notMem;intro p u;obtain⟨g,E,_⟩:=o p u;simp at E
   subst C;simp[elim]
 | append_singleton gs g ih=>
   intro r S o;have q:elim n (gs++[g]) b=aI n (elim n gs b) g:=by rw[oA];rfl
   have m:∀(a:ℕ) (d:Stat),a<b.1.length+gs.length→
     (elim n (gs++[g]) b).1.getD a d=(elim n gs b).1.getD a d:=
    fun a d h=>fN n gs g [] b a d h
   have t:∀f∈gs,NOk f:=fun f h=>r f (List.mem_append_left _ h)
   have y:=ih t (S.erase gs.length) (by
    intro p u;obtain⟨G,w⟩:=Finset.mem_erase.1 u;obtain⟨f,e,a,s,l,c,k⟩:=o p w;have x:p<gs.length:=by obtain⟨A,_⟩:=List.getElem?_eq_some_iff.1 e;rw[List.length_append,List.length_singleton] at A;omega
    rw[List.getElem?_append_left x] at e;rw[m a _ (by omega)] at k;exact⟨f,e,a,s,l,c,k⟩)
   rw[q,List.length_append,List.length_singleton];by_cases j:gs.length∈S
   ·obtain⟨f,e,a,s,l,c,k⟩:=o _ j;have v:f=g:=by
     rw[List.getElem?_concat_length] at e;exact(Option.some.inj e).symm
    subst v;rw[m a _ l] at k;have B:=qR n (elim n gs b) f (r f (by simp)) a s c k;have z:=Finset.card_erase_of_mem j;have F:1≤S.card:=Finset.card_pos.2 ⟨_,j⟩;omega
   ·have B:(aI n (elim n gs b) g).2.length≤(elim n gs b).2.length+1:=by
     simp only[aI,List.length_append];have:=dR (aH g.op (n+(elim n gs b).2.length)
      (g.inputs.map fun i=>(elim n gs b).1.getD i (Stat.const false))).1
     omega
    rw[Finset.erase_eq_of_notMem j] at y;omega
def RC (n:ℕ) (gs:List Gate) (i:Fin (n+1)) (b:Bool) (p:ℕ):Prop:=∃g,gs[p]?=some g∧∃a∈g.inputs,∃c,stF n gs i b a=Stat.const c
abbrev bS {n:ℕ} (i:Fin (n+1)) (b:Bool) (y:Fin n→Bool):Fin (n+1)→Bool:=Fin.insertNth i b y
def uK (n:ℕ) (gs:List Gate) (i:Fin (n+1)) (b:Bool):List Gate:=(elim n gs (bH n i b,[])).2
def IsC (n:ℕ) (gs:List Gate) (i:Fin (n+1)) (b:Bool) (a:ℕ):Prop:=∃c,stF n gs i b a=Stat.const c
lemma wW (n:ℕ) (gs:List Gate) (hcl:aW (n+1) gs) (i:Fin (n+1)) (b:Bool)
  (y:Fin n→Bool):
  yR n (List.ofFn y) (aD gs (List.ofFn (bS i b y))) (elim n gs (bH n i b,[])):=
 fL n _ (by simp) gs _ _ (fun g a=>(dS _ gs hcl g a).1) (zH n i b y)
lemma mL (n:ℕ) (gs:List Gate) (hcl:aW (n+1) gs) (i:Fin (n+1))
  (b:Bool) (j:ℕ) (c:Bool) (h:stF n gs i b j=Stat.const c) (y:Fin n→Bool):
  vl gs (bS i b y) j=c:=by
 have a:=((wW n gs hcl i b y).2 j).2;rw[show(elim n gs (bH n i b,[])).1.getD j (Stat.const false)=Stat.const c from h] at a;exact a.symm
lemma uL (n:ℕ) (gs:List Gate) (hcl:aW (n+1) gs) (i:Fin (n+1))
  (b:Bool) (j q:ℕ) (h:stF n gs i b j=Stat.cB q) (y:Fin n→Bool):
  vl gs (bS i b y) j=vl (uK n gs i b) y q:=by
 have a:=((wW n gs hcl i b y).2 j).2;rw[show(elim n gs (bH n i b,[])).1.getD j (Stat.const false)=Stat.cB q from h] at a;exact a.symm
lemma pV (n:ℕ) (gs:List Gate) (hcl:aW (n+1) gs) (i:Fin (n+1))
  (b:Bool) (p:ℕ) (g:Gate) (c:gs[p]?=some g) (a:ℕ) (e:a∈g.inputs)
  (f:stF n gs i b a=Stat.const (eR g)):IsC n gs i b (n+1+p):=by
 have d:(bH n i b,([]:List Gate)).1.length=n+1:=eE n i b;have h:=qS n gs (bH n i b,[]) p g c ((hcl p g c).nok) a e
  (by rw[d];exact(hcl p g c).lt a e) f
 rw[d] at h;exact h
end PEqualNP.MetaComplexity.Aa
namespace PEqualNP.MetaComplexity.Aa.A6
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def qT (n m:ℕ) (π:Fin n→Fin m) (w:ℕ):ℕ:=if h:w<n then(π ⟨w,h⟩:ℕ) else w-n+m
def iA (n m:ℕ) (π:Fin n→Fin m) (g:Gate):Gate:=⟨g.op,g.inputs.map (qT n m π)⟩
def wX (n m:ℕ) (π:Fin n→Fin m) (C:Circuit):Circuit:=⟨C.gates.map (iA n m π),qT n m π C.output⟩
def step (w:List Bool) (g:Gate):List Bool:=w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
def Rel (n m:ℕ) (π:Fin n→Fin m) (W W':List Bool):Prop:=
 n
  ≤W.length∧W'.length+n=W.length+m∧
  ∀w:ℕ,W'.getD (qT n m π w) false=W.getD w false
lemma zI (n m:ℕ) (π:Fin n→Fin m) (W W':List Bool) (g:Gate)
  (h:Rel n m π W W'):Rel n m π (step W g) (step W' (iA n m π g)):=by
 obtain⟨k,l,c⟩:=h;have f:(iA n m π g).op.eval
   ((iA n m π g).inputs.map fun i=>W'.getD i false)
   =g.op.eval (g.inputs.map fun i=>W.getD i false):=by
  simp only[iA,List.map_map];congr 1;apply List.map_congr_left;intro a _;exact c a
 refine⟨by simp[step];omega,by simp[step];omega,?_⟩;intro w;simp only[step,f];rcases Nat.lt_trichotomy w W.length with b|b|b
 ·have d:qT n m π w<W'.length:=by
   unfold qT
   split
   ·have:=(π ⟨w,by assumption⟩).2;omega
   ·omega
  rw[List.getD_append _ _ _ _ d,List.getD_append _ _ _ _ b];exact c w
 ·have e:qT n m π w=W'.length:=by
   unfold qT
   split
   ·omega
   ·omega
  rw[e,b,bR,bR]
 ·have j:W'.length+1≤qT n m π w:=by
   unfold qT
   split
   ·omega
   ·omega
  rw[List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
lemma zJ (n m:ℕ) (π:Fin n→Fin m) (gs:List Gate):
  ∀
   W W':List Bool,Rel n m π W W'→
   Rel n m π (gs.foldl step W) ((gs.map (iA n m π)).foldl step W'):=by
 induction gs with
 | nil=>intro W W' h;exact h
 | cons g gs ih=>
   intro W W' h;exact ih _ _ (zI n m π W W' g h)
lemma zK (n m:ℕ) (π:Fin n→Fin m) (x:Fin m→Bool):
  Rel n m π (List.ofFn (x∘π)) (List.ofFn x):=by
 refine⟨by simp,by simp;omega,?_⟩;intro w;unfold qT
 split
 ·rename_i hw
  rw[List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)];simp
 ·rename_i hw
  rw[List.getD_eq_default _ _ (by simp),List.getD_eq_default _ _ (by simp;omega)]
lemma sL {n m:ℕ} (π:Fin n→Fin m) (h:(Fin n→Bool)→Bool) (s:ℕ)
  (e:HasCircuitSize n h s):HasCircuitSize m (fun x=>h (x∘π)) s:=by
 obtain⟨C,d,c,hev⟩:=e;refine⟨wX n m π C,?_,?_,?_⟩
 ·intro g f;obtain⟨b,a,rfl⟩:=List.mem_map.1 f;exact⟨(d b a).1,by simpa[iA] using(d b a).2⟩
 ·simpa[wX,Circuit.size] using c
 ·intro x
  show _=h (x∘π)
  rw[←hev (x∘π)];have:=(zJ n m π C.gates _ _ (zK n m π x)).2.2 C.output;exact this
end PEqualNP.MetaComplexity.Aa.A6
namespace PEqualNP.MetaComplexity.Aa.Au
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Aa
open PEqualNP.MetaComplexity.Aa.A6
def Dep {m:ℕ} (f:(Fin m→Bool)→Bool) (p:Fin m):Prop:=∃x:Fin m→Bool,f (Function.update x p (!x p))≠f x
def xU {m:ℕ} (f:(Fin m→Bool)→Bool) (y:Fin m) (b:Bool) (k s:ℕ):Prop:=∃s':ℕ,s'+k≤ s∧HasCircuitSize m (fun x=>f (Function.update x y b)) s'
lemma zM {m:ℕ} {f:(Fin m→Bool)→Bool} {p:Fin m} (h:Dep f p):
  ∃x y:Fin m→Bool,f x≠f y:=by
 obtain⟨x,a⟩:=h;exact⟨_,_,a⟩
lemma aB2 {k:ℕ} (gs:List Gate) (hcl:aW k gs) (u:Fin k→Bool) (q:ℕ) (g:Gate)
  (c:gs[q]?=some g) (j:ℕ) (b:g.op=GateOp.not) (a:g.inputs=[j]):
  vl gs u (k+q)= !vl gs u j:=by
 rw[eZ gs hcl u q g c,b,a];rfl
lemma sM {n:ℕ} (i:Fin (n+1)) (b:Bool) (x:Fin (n+1)→Bool):
  Function.update x i b=bS i b (Fin.removeNth i x):=
 (Fin.insertNth_removeNth i b x).symm
lemma dC {n:ℕ} {f:(Fin (n+1)→Bool)→Bool} {gs:List Gate} {o:ℕ}
  (hcl:aW (n+1) gs) (hev:∀x:Fin (n+1)→Bool,vl gs x o=f x)
  (i:Fin (n+1)) (b c:Bool) (h:stF n gs i b o=Stat.const c) (x:Fin (n+1)→Bool):
  f (Function.update x i b)=c:=by
 rw[sM,←hev];exact mL n gs hcl i b o c h _
lemma save (n:ℕ) (f:(Fin (n+1)→Bool)→Bool) (gs:List Gate) (o:ℕ)
  (hcl:aW (n+1) gs) (hev:∀x:Fin (n+1)→Bool,vl gs x o=f x)
  (i:Fin (n+1)) (b:Bool)
  (q:∃x y:Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (S:Finset ℕ) (u:∀p∈S,RC n gs i b p):xU f i b S.card gs.length:=by
 have t:(bH n i b,([]:List Gate)).1.length=n+1:=eE n i b;have d:=vY n (bH n i b,[]) gs (dS _ gs hcl) S (by intro p l;obtain⟨g,h,a,m,c,k⟩:=u p l;refine⟨g,h,a,m,?_,c,k⟩;rw[t];exact(hcl p g h).lt a m);simp only[List.length_nil,zero_add] at d
 cases hst:stF n gs i b o with
 | const c=>
   exfalso;obtain⟨x,y,r⟩:=q;exact r ((dC hcl hev i b c hst x).trans (dC hcl hev i b c hst y).symm)
 | cB j=>
   have k:aW n (uK n gs i b):=lO n (List.ofFn fun _:Fin n=>false) (by simp) gs _ _ (fun g h=>(dS _ gs hcl g h).1) (zH n i b _) (by intro p g l;simp at l);have s:=sL (Fin.succAbove i) _ _ (sF n (uK n gs i b) j k);have e:(fun x:Fin (n+1)→Bool=>f (Function.update x i b))
     =fun x=>vl (uK n gs i b) (x∘Fin.succAbove i) j:=by
    funext x;rw[sM,←hev,uL n gs hcl i b o j hst];rfl
   refine⟨(uK n gs i b).length,d,?_⟩;rw[e];exact s
section
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
lemma Ao.save (L:Ao (n+1) f gs o) (i:Fin (n+1)) (b:Bool)
  (a:∃x y:Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (S:Finset ℕ) (c:∀p∈S,RC n gs i b p):xU f i b S.card gs.length:=
 PEqualNP.MetaComplexity.Aa.Au.save n f gs o L.hcl L.hev i b a S c
lemma Ao.save2 (L:Ao (n+1) f gs o) (i:Fin (n+1)) (b:Bool)
  (e:∃x y:Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (a c:ℕ) (d:a≠c) (h:RC n gs i b a) (j:RC n gs i b c):
  xU f i b 2 gs.length:=by
 have:=L.save i b e {a,c} (by intro p g;simp only[Finset.mem_insert,Finset.mem_singleton] at g;rcases g with rfl | rfl<;>assumption);rwa [Finset.card_pair d] at this
lemma Ao.save3 (L:Ao (n+1) f gs o) (i:Fin (n+1)) (b:Bool)
  (j:∃x y:Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (a c d:ℕ) (e:a≠c) (g:a≠d) (h:c≠d)
  (l:RC n gs i b a) (m:RC n gs i b c) (q:RC n gs i b d):
  xU f i b 3 gs.length:=by
 have:=L.save i b j {a,c,d} (by intro p k;simp only[Finset.mem_insert,Finset.mem_singleton] at k;rcases k with rfl | rfl | rfl<;>assumption);rwa [Finset.card_eq_three.2 ⟨a,c,d,e,g,h,rfl⟩] at this
lemma fO {gs:List Gate} {q:ℕ} {i:Fin (n+1)} (b:Bool) (h:bW gs q i):
  RC n gs i b q:=by
 obtain⟨g,c,a⟩:=h;exact⟨g,c,i,a,b,uJ n gs i b⟩
lemma oB {gs:List Gate} {q w:ℕ} {i:Fin (n+1)} {b:Bool} (h:bW gs q w)
  (a:IsC n gs i b w):RC n gs i b q:=by
 obtain⟨g,e,d⟩:=h;obtain⟨c,a⟩:=a;exact⟨g,e,w,d,c,a⟩
lemma Ao.next (L:Ao (n+1) f gs o) (i:Fin (n+1)) (b:Bool)
  (d:∃x y:Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (p:ℕ) (r:p<gs.length) (j:IsC n gs i b (n+1+p)):
  ∃q,p<q∧bW gs q (n+1+p)∧RC n gs i b q:=by
 have g:∃x y:Fin (n+1)→Bool,f x≠f y:=by obtain⟨x,y,h⟩:=d;exact⟨_,_,h⟩
 have m:o≠n+1+p:=by intro e;obtain⟨c,a⟩:=j;obtain⟨x,y,l⟩:=d;rw[←e] at a;exact l ((dC L.hcl L.hev i b c a x).trans (dC L.hcl L.hev i b c a y).symm)
 obtain⟨q,k,hr⟩:=L.live g p r m;exact⟨q,k,hr,oB hr j⟩
end
end PEqualNP.MetaComplexity.Aa.Au
namespace PEqualNP.MetaComplexity.Aa.Au
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Aa
lemma dV {k:ℕ} (gs:List Gate) (hcl:aW k gs) (q:ℕ) (g:Gate)
  (d:gs[q]?=some g) (a:ℕ) (f:a∈g.inputs):
  (g.op=GateOp.not∧g.inputs=[a]∧∀u:Fin k→Bool,vl gs u (k+q)= !vl gs u a)∨
  ∃
   w,(g.inputs=[a,w]∨g.inputs=[w,a])∧
   ((g.op=GateOp.and∧∀u:Fin k→Bool,vl gs u (k+q)=(vl gs u a && vl gs u w))∨
    (g.op=GateOp.or∧∀u:Fin k→Bool,vl gs u (k+q)=(vl gs u a || vl gs u w))):=by
 rcases hcl q g d with⟨b,j,_,c⟩|⟨b,j,h,_,_,c⟩
 ·left;have e:a=j:=by rw[c] at f;simpa using f
  subst e;exact⟨b,c,fun u=>aB2 gs hcl u q g d a b c⟩
 ·right;have e:a=j∨a=h:=by rw[c] at f;simpa using f
  rcases e with e|e
  ·subst e;refine⟨h,Or.inl c,?_⟩;rcases b with b|b
   ·exact Or.inl ⟨b,fun u=>by rw[eZ gs hcl u q g d,b,c];simp[GateOp.eval]⟩
   ·exact Or.inr ⟨b,fun u=>by rw[eZ gs hcl u q g d,b,c];simp[GateOp.eval]⟩
  ·subst e;refine⟨j,Or.inr c,?_⟩;rcases b with b|b
   ·refine Or.inl ⟨b,fun u=> ?_⟩;rw[eZ gs hcl u q g d,b,c];simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id,
     Bool.and_true]
    exact Bool.and_comm _ _
   ·refine Or.inr ⟨b,fun u=> ?_⟩;rw[eZ gs hcl u q g d,b,c];simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id,
     Bool.or_false]
    exact Bool.or_comm _ _
section
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
lemma Ao.no_tri (L:Ao m f gs o) (h:∃x y:Fin m→Bool,f x≠f y) (p q a:ℕ)
  (A:bW gs p a) (B:bW gs q a) (C:bW gs q (m+p)):False:=by
 obtain⟨v,t,s⟩:=A;obtain⟨F,j,z⟩:=B;obtain⟨l,n,i⟩:=C;have e:l=F:=by rw[j] at n;exact(Option.some.inj n).symm
 subst e;have E:a< m+p:=(L.hcl p v t).lt a s;have k:m+p< m+q:=(L.hcl q l j).lt _ i;have b:q<gs.length:=(List.getElem?_eq_some_iff.1 j).1;rcases dV gs L.hcl q l j a z with⟨_,g,_⟩|⟨w,g,c⟩
 ·rw[g] at i;simp at i;omega
 ·have G:w=m+p:=by
   rcases g with g|g<;>rw[g] at i<;>simp at i<;>omega
  subst G;rcases dV gs L.hcl p v t a s with⟨_,_,d⟩|⟨r,_,d⟩
  ·rcases c with⟨_,c⟩|⟨_,c⟩
   ·exact L.no_const h q b false (fun u=>by rw[c u,d u];cases vl gs u a<;>rfl)
   ·exact L.no_const h q b true (fun u=>by rw[c u,d u];cases vl gs u a<;>rfl)
  ·rcases c with⟨_,c⟩|⟨_,c⟩<;>rcases d with⟨_,d⟩|⟨_,d⟩
   ·exact L.no_alias h q b (m+p) k (fun u=>by rw[c u,d u];cases vl gs u a<;>cases vl gs u r<;>rfl)
   ·exact L.no_alias h q b a (by omega) (fun u=>by rw[c u,d u];cases vl gs u a<;>cases vl gs u r<;>rfl)
   ·exact L.no_alias h q b a (by omega) (fun u=>by rw[c u,d u];cases vl gs u a<;>cases vl gs u r<;>rfl)
   ·exact L.no_alias h q b (m+p) k (fun u=>by rw[c u,d u];cases vl gs u a<;>cases vl gs u r<;>rfl)
end
section
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
lemma Ao.third (L:Ao (n+1) f gs o) (i:Fin (n+1)) (b:Bool)
  (a:∃x y:Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (p q:ℕ) (k:p≠q) (e:bW gs p i) (l:bW gs q i)
  (m:IsC n gs i b (n+1+p)):xU f i b 3 gs.length:=by
 have d:∃x y:Fin (n+1)→Bool,f x≠f y:=by obtain⟨x,y,h⟩:=a;exact⟨_,_,h⟩
 obtain⟨J,r,j,c⟩:=L.next i b a p (dU e) m;have g:J≠q:=by rintro rfl;exact L.no_tri d p J i e l j
 exact L.save3 i b a p q J k (by omega) (Ne.symm g) (fO b e) (fO b l) c
end
end PEqualNP.MetaComplexity.Aa.Au
namespace PEqualNP.MetaComplexity.NestedCover.Ac
open PEqualNP.CircuitLowerBounds
def skip (k:ℕ):ℕ ↪ ℕ:=
 ⟨fun j=>if j<k then j else j+1,by
   intro i j h;dsimp at h
   split at h<;>split at h<;>omega⟩
def contract (k h i:ℕ):ℕ:=if i<k then i else if i=k then h else i-1
lemma aQ (k i:ℕ):skip k i=if i<k then i else i+1:=rfl
lemma align (n p j:ℕ):skip (n+p) (n+j)=n+skip p j:=by simp only[aQ];split_ifs<;>omega
@[simp] lemma contract_skip (k h j : ℕ) : contract k h (skip k j) = j := by
 simp only[aQ,contract];split_ifs<;>omega
lemma eF {k h i:ℕ} (a:i≠k):skip k (contract k h i)=i:=by simp only[aQ,contract];split_ifs<;>omega
lemma fA (k j:ℕ):skip k j≠k:=by simp only[aQ];split<;>omega
lemma zN {k h a i:ℕ}:contract k h a=i↔a=skip k i∨a=k∧i=h:=by
 constructor
 ·rintro rfl;by_cases b:a=k
  ·simp[b,contract]
  ·exact Or.inl (eF b).symm
 ·rintro(rfl|⟨rfl,rfl⟩)
  ·simp
  ·simp[contract]
def nH (f:ℕ→ℕ) (g:Gate):Gate:=⟨g.op,g.inputs.map f⟩
def erase (n:ℕ) (C:Circuit) (p h:ℕ):Circuit:=⟨(C.gates.eraseIdx p).map (nH (contract (n+p) h)),contract (n+p) h C.output⟩
variable {n p h : ℕ} {C : Circuit}
@[simp] lemma erase_length (a : p < C.gates.length) :
  (erase n C p h).gates.length+1=C.gates.length:=by
 simp[erase,List.length_eraseIdx_of_lt a];omega
lemma fP (j:ℕ):gateAt (erase n C p h) j=
  nH (contract (n+p) h) (gateAt C (skip p j)):=by
 simp only[gateAt,erase,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eraseIdx,aQ];by_cases a:j<p<;>simp only[a,↓reduceIte]
 ·cases C.gates[j]?<;>rfl
 ·cases C.gates[j+1]?<;>rfl
lemma aS (a:p<C.gates.length) {j}:
  j<(erase n C p h).gates.length↔skip p j<C.gates.length:=by
 have:=erase_length (n:=n) (h:=h) a;simp only[aQ];split<;>omega
lemma bM (f:p<C.gates.length) (hh:h<n+p) (d:ReadsBack n C):
  ReadsBack n (erase n C p h):=by
 intro j e i b;rw[fP] at b;obtain⟨a,c,rfl⟩:=List.mem_map.mp b;have:=d _ ((aS f).mp e) a c;simp only[aQ] at this;unfold contract
 split at this<;>split_ifs<;>omega
lemma fan (a:FanInTwo C):FanInTwo (erase n C p h):=by intro g b;obtain⟨k,c,rfl⟩:=List.mem_map.mp b;have:=a k ((List.eraseIdx_sublist ..).subset c);simpa[nH] using this
lemma uM (a:∀g∈C.gates,g.op≠GateOp.not):
  ∀g∈(erase n C p h).gates,g.op≠GateOp.not:=by
 intro g b;obtain⟨k,c,rfl⟩:=List.mem_map.mp b;exact a k ((List.eraseIdx_sublist ..).subset c)
lemma pin {j s i:ℕ}:(gateAt (erase n C p h) j).inputs[s]?=some i↔
  (gateAt C (skip p j)).inputs[s]?=some (skip (n+p) i)∨
  (gateAt C (skip p j)).inputs[s]?=some (n+p)∧i=h:=by
 rw[fP];simp only[nH,List.getElem?_map]
 cases he:(gateAt C (skip p j)).inputs[s]? with
 | none=>simp
 | some a=>simp[zN]
lemma sN {i}:(erase n C p h).output=i↔C.output=skip (n+p) i∨C.output=n+p∧i=h:=zN
lemma aA3 (j:ℕ):(gateAt C (skip p j)).op=(gateAt (erase n C p h) j).op:=by rw[fP];rfl
def val (C:Circuit) (x:Fin n→Bool) (i:ℕ):Bool:=(C.wires (List.ofFn x)).getD i false
lemma aBu {x:Fin n→Bool} {i} (a:i<n):val C x i=x ⟨i,a⟩:=Bool.eq_iff_iff.mpr (aC ⟨i,a⟩)
lemma nI {x:Fin n→Bool} (e:p<C.gates.length) (hh:h<n+p)
  (d:ReadsBack n C) (g:val C x (n+p)=val C x h):
  ∀i<n+C.gates.length,val (erase n C p h) x (contract (n+p) h i)=val C x i:=by
 have f:=bM e hh d;intro i
 induction i using Nat.strong_induction_on with
 | _ i ih=>
   intro s;by_cases b:i<n
   ·rw[show contract (n+p) h i=i by simp[contract,show i<n+p by omega],aBu b,aBu b]
   by_cases q:i=n+p
   ·subst i;simpa[contract,hh] using(ih h hh (by omega)).trans g.symm
   let j:=contract p 0 (i-n)
   have r:skip p j=i-n:=eF (by omega);have c:i=n+skip p j:=by omega
   have k:j<(erase n C p h).gates.length:=(aS e).mpr (by omega);have o:contract (n+p) h i=n+j:=by rw[c,←align,contract_skip]
   rw[o];unfold val;rw[aO f k]
   conv_rhs=>rw[c,aO d (by omega)]
   rw[fP];simp only[nH,List.map_map];congr 1;apply List.map_congr_left;intro a l;have m:=d _ ((aS e).mp k) a l;exact ih a (by omega) (by omega)
lemma vZ {x:Fin n→Bool} (d:p<C.gates.length) (hh:h<n+p)
  (b:ReadsBack n C) (a:val C x (n+p)=val C x h)
  (c:C.output<n+C.gates.length):
  circuitFun n (erase n C p h) x=circuitFun n C x:=
 nI d hh b a _ c
end PEqualNP.MetaComplexity.NestedCover.Ac
namespace PEqualNP.MetaComplexity.NestedCover.Ac
open PEqualNP.CircuitLowerBounds
structure Splice (n : ℕ) (D P : Circuit) (g w : ℕ ↪ ℕ) (source fresh : ℕ) : Prop where
  align : ∀ j, w (n+j) = n + g j
  hole : ∀ i, w i ≠ fresh
  op : ∀ j, (gateAt P (g j)).op = (gateAt D j).op
  pin : ∀ j s i : ℕ, (gateAt D j).inputs[s]? = some i ↔
    (gateAt P (g j)).inputs[s]? = some (w i) ∨
    (gateAt P (g j)).inputs[s]? = some fresh ∧ i = source
  total : ∀ j, (gateAt P (g j)).inputs.length = (gateAt D j).inputs.length
  output : ∀ i, D.output = i ↔ P.output = w i ∨ P.output = fresh ∧ i = source
variable {n p h : ℕ} {C : Circuit}
lemma fB:Splice n (erase n C p h) C (skip p) (skip (n+p)) h (n+p) where
 align:=align n p
 hole:=fA _
 op:=aA3
 pin:=fun _ _ _=>pin
 total:=fun j=>by simp[fP,nH]
 output:=fun _=>sN
namespace Splice
variable {D P : Circuit} {g w : ℕ ↪ ℕ} {u v : ℕ} (S : Splice n D P g w u v)
include S
lemma unchanged (j:ℕ) (hs:v∉(gateAt P (g j)).inputs):
  (gateAt P (g j)).inputs=(gateAt D j).inputs.map w:=by
 apply List.ext_getElem
 ·simp[S.total]
 ·intro i d b;have c:i<(gateAt D j).inputs.length:=by simpa using b
  have a:=(S.pin j i _).mp (List.getElem?_eq_getElem c);rcases a with a|⟨a,_⟩
  ·simpa[d] using a
  ·exact(hs (List.mem_of_getElem? a)).elim
lemma lQ (j:ℕ) (hs:w u∉(gateAt P (g j)).inputs):
  (gateAt P (g j)).inputs=(gateAt D j).inputs.map (fun i=>if i=u then v else w i):=by
 apply List.ext_getElem
 ·simp[S.total]
 ·intro i c d;have f:i<(gateAt D j).inputs.length:=by simpa using d
  rcases (S.pin j i _).mp (List.getElem?_eq_getElem f) with a|⟨a,h⟩
  ·have e:(gateAt D j).inputs[i]≠u:=by
    intro b;exact hs (b▸List.mem_of_getElem? a)
   simpa[c,e] using a
  ·simpa[c,h] using a
end Splice
def bT (n:ℕ) (C:Circuit) (p h q a:ℕ):Circuit:=erase n (erase n C p h) q (contract (n+p) h a)
def cN (p q:ℕ):=(skip q).trans (skip p)
lemma bX (p q i:ℕ):cN p q i=skip p (skip q i):=rfl
lemma kV {q a} (b:p<C.gates.length) (c:skip p q<C.gates.length):
  (bT n C p h q a).gates.length+2=C.gates.length:=by
 have d:=erase_length (n:=n) (h:=h) b;have e:=erase_length (n:=n) (C:=erase n C p h) (h:=contract (n+p) h a)
  ((aS b).mpr c)
 change(erase n (erase n C p h) q _).gates.length+2=_;omega
lemma kW {q a:ℕ} (d:C.output≠n+p)
  (hs:∀j,n+p∉(gateAt C (cN p q j)).inputs):
  Splice n (bT n C p h q a) C (cN p q) (cN (n+p) (n+q))
   (contract (n+p) h a) (n+skip p q):=by
 let S:=fB (n:=n) (C:=C) (p:=p) (h:=h)
 let T:=fB (n:=n) (C:=erase n C p h) (p:=q) (h:=contract (n+p) h a)
 refine⟨fun j=>by simp[bX,align],fun i=> ?_,fun j=> ?_,fun j s i=> ?_,fun j=> ?_,fun i=> ?_⟩
 ·rw[bX,←align];exact fun b=>fA _ _ ((skip _).injective b)
 ·exact(S.op _).trans (T.op _)
 ·rw[bT,T.pin,S.pin,S.pin,←align n p q];have c:(gateAt C (skip p (skip q j))).inputs[s]?≠some (n+p):=
   fun b=>hs j (List.mem_of_getElem? b)
  simp[c,bX]
 ·exact(S.total _).trans (T.total _)
 ·rw[bT,T.output,S.output,S.output,←align n p q];simp[d,bX]
lemma bI {k h i b:ℕ} (hh:h<k) (a:i<skip k b):
  contract k h i<b:=by
 rw[aQ] at a;unfold contract
 split at a<;>split_ifs<;>omega
lemma wA {q a:ℕ} {x:Fin n→Bool} (b:p<C.gates.length)
  (m:skip p q<C.gates.length) (hh:h<n+p) (o:a<n+skip p q)
  (e:ReadsBack n C) (k:val C x (n+p)=val C x h)
  (l:val C x (n+skip p q)=val C x a):
  ∀
   i<n+C.gates.length,
   val (bT n C p h q a) x (contract (n+q) (contract (n+p) h a) (contract (n+p) h i))=val C x i:=by
 have g:q<(erase n C p h).gates.length:=(aS b).mpr m;have d:=bI hh (show a<skip (n+p) (n+q) by rwa [align]);have B:=nI b hh e k;have D:=B (n+skip p q) (by omega);rw[←align,contract_skip,align] at D;have c:=D.trans (l.trans (B a (by omega)).symm);intro i f;have j:skip (n+p) (n+(erase n C p h).gates.length)=n+C.gates.length:=by have:=erase_length (n:=n) (h:=h) b;rw[align,aQ];split<;>omega
 exact(nI g d (bM b hh e) c _ (bI hh (j▸f))).trans (B i f)
end PEqualNP.MetaComplexity.NestedCover.Ac
namespace PEqualNP.MetaComplexity.NestedCover.Ac
open PEqualNP.CircuitLowerBounds
variable {n p h : ℕ} {C : Circuit}
lemma bE {x:Fin n→Bool} (l:Fin n):val C x l=x l:=Bool.eq_iff_iff.mpr (aC l)
lemma jG (b:p<C.gates.length) (hh:h<n+p) {a}
  (c:a<n+C.gates.length):contract (n+p) h a<n+(erase n C p h).gates.length:=by
 apply bI hh;have:=erase_length (n:=n) (h:=h) b;rw[align,aQ];split<;>omega
def mM (C:Circuit) (j i k:ℕ):Prop:=(gateAt C j).inputs=[i,k]∨(gateAt C j).inputs=[k,i]
def bU (b:Bool):GateOp:=if b then GateOp.and else GateOp.or
lemma kX {x:Fin n→Bool} {u a j} {b:Bool}
  (f:ReadsBack n C) (g:j<C.gates.length) (op:(gateAt C j).op=bU b)
  (d:mM C j u a) (c:val C x u=b):val C x (n+j)=val C x a:=by
 unfold val at c ⊢
 rw[aO f g,op];rcases d with e|e<;>cases b<;>
  simp only[e,bU,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.any_cons,
   List.all_nil,List.any_nil,id_eq,c,Bool.false_eq_true,↓reduceIte,
   Bool.false_or,Bool.or_false,Bool.true_and,Bool.and_true]
lemma iM {x:Fin n→Bool} {u a j} {b:Bool}
  (f:ReadsBack n C) (g:j<C.gates.length) (op:(gateAt C j).op=bU (!b))
  (d:mM C j u a) (c:val C x u=b):val C x (n+j)=val C x u:=by
 unfold val at c ⊢
 rw[aO f g,op];rcases d with e|e<;>cases b<;>
  simp only[e,bU,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.any_cons,
   List.all_nil,List.any_nil,id_eq,c,Bool.false_eq_true,Bool.not_false,
   Bool.not_true,↓reduceIte,Bool.false_and,Bool.and_false,Bool.true_or,Bool.or_true,
   Bool.or_false,Bool.and_true]
lemma jH {l:Fin n} (e:ReadsBack n C)
  (o:∀j<C.gates.length,l.val∉(gateAt C j).inputs)
  (x:Fin n→Bool) (b:Bool):
  ∀i<n+C.gates.length,i≠l.val→val C (Function.update x l b) i=val C x i:=by
 intro i
 induction i using Nat.strong_induction_on with
 | _ i ih=>
   intro p m;by_cases c:i<n
   ·have k:(⟨i,c⟩:Fin n)≠l:=fun h=>m (congrArg Fin.val h)
    exact((bE (C:=C) (x:=Function.update x l b) ⟨i,c⟩).trans
     (Function.update_of_ne k b x)).trans (bE (C:=C) (x:=x) ⟨i,c⟩).symm
   let j:=i-n
   have f:i=n+j:=by dsimp[j];omega
   have d:j<C.gates.length:=by omega
   rw[f];unfold val;rw[aO e d,aO e d];congr 1;exact List.map_congr_left (fun a g=>ih a (f▸e j d a g) (by have:=e j d a g;omega) (fun h=>o j d (h▸g)))
lemma Splice.unused {D:Circuit} {g w:ℕ ↪ ℕ} {s v:ℕ} (S:Splice n D C g w s v)
  (l:Fin n) (c:w l.val=l.val) (hs:s≠l.val)
  (h:C.output≠l.val) (f:∀j<D.gates.length,l.val∉(gateAt C (g j)).inputs):
  D.output≠l.val∧∀j<D.gates.length,l.val∉(gateAt D j).inputs:=by
 constructor
 ·intro a;rcases (S.output _).mp a with a|⟨_,a⟩
  ·exact h (a.trans c)
  ·exact hs a.symm
 ·intro j e hl;obtain⟨i,d,b⟩:=List.mem_iff_getElem.mp hl;have a:=(S.pin j i l.val).mp ((List.getElem?_eq_getElem d).trans (congrArg some b));rcases a with a|⟨_,a⟩
  ·exact f j e (c▸List.mem_of_getElem? a)
  ·exact hs a.symm
lemma uN {D:Circuit} (l:Fin n) (b:Bool) (a:ReadsBack n D)
  (c:D.output<n+D.gates.length)
  (unused:D.output≠l.val∧∀j<D.gates.length,l.val∉(gateAt D j).inputs)
  (d:∀x:Fin n→Bool,x l=b→circuitFun n D x=circuitFun n C x):
  circuitFun n D =fun x=>circuitFun n C (Function.update x l b):=by
 funext x;exact(jH a unused.2 x b _ c unused.1).symm.trans (d _ (Function.update_self ..))
lemma sO (l:Fin n) (b:Bool) (a:p<C.gates.length)
  (c:ReadsBack n C) (d:mM C p l.val h) (op:(gateAt C p).op=bU b)
  (hh:h<n+p) (e:h≠l.val) (f:C.output<n+C.gates.length)
  (g:C.output≠l.val)
  (unique:∀j<C.gates.length,j≠p→l.val∉(gateAt C j).inputs):
  circuitFun n (erase n C p h)=fun x=>circuitFun n C (Function.update x l b):=by
 have k:skip (n+p) l.val=l.val:=by simp[aQ,show l.val<n+p by have:=l.isLt;omega]
 refine uN l b (bM a hh c) (jG a hh f)
  (fB.unused l k e g (fun j i=>unique _ ((aS a).mp i) (fA _ _))) ?_
 intro x m;exact vZ a hh c (kX c a op d ((bE l).trans m)) f
lemma sP (l:Fin n) (b:Bool) {q a z}
  (d:p<C.gates.length) (r:skip p q<C.gates.length)
  (f:ReadsBack n C) (g:mM C p l.val z) (opB:(gateAt C p).op=bU (!b))
  (h:mM C (skip p q) (n+p) a) (opD:(gateAt C (skip p q)).op=bU b)
  (A:a<n+skip p q) (F:a≠l.val) (E:a≠n+p)
  (u:C.output<n+C.gates.length) (w:C.output≠l.val) (v:C.output≠n+p)
  (unique:∀j,l.val∉(gateAt C (cN p q j)).inputs∧n+p∉(gateAt C (cN p q j)).inputs):
  circuitFun n (bT n C p l.val q a)=fun x=>circuitFun n C (Function.update x l b):=by
 have e:l.val<n+p:=by have:=l.isLt;omega
 have o:q<(erase n C p l.val).gates.length:=(aS d).mpr r;have m:=bI e (show a<skip (n+p) (n+q) by rwa [align]);have y {k:ℕ}:skip (n+k) l.val=l.val:=by simp[aQ,show l.val<n+k by have:=l.isLt;omega]
 have t:contract (n+p) l.val a≠l.val:=by rw[ne_eq,zN,y];tauto
 apply uN l b (bM o m (bM d e f))
  (jG o m (jG d e u))
  ((kW v (fun j=>(unique j).2)).unused l (by simp[bX,y])
    t w (fun j _=>(unique j).1))
 intro x B;have c:=(bE (C:=C) (x:=x) l).trans B;have i:=iM f d opB g c;have s:=kX f r opD h (i.trans c);exact wA d r e A f i s _ u
end PEqualNP.MetaComplexity.NestedCover.Ac
namespace PEqualNP.MetaComplexity.NestedCover.Ac
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.Aa Au
def fC {n:ℕ} (C:Circuit) (l:Fin n) (b:Bool):Prop:=∃x y:Fin n→Bool,circuitFun n C (Function.update x l b)≠circuitFun n C (Function.update y l b)
def Cap {n:ℕ} (C:Circuit) (l:Fin n) (b:Bool) (k:ℕ):Prop:=¬xU (circuitFun n C) l b (k+1) C.gates.length
lemma mN {n b k} {C:Circuit} {l:Fin n}
  (hl:∀D:Circuit,FanInTwo D→
    circuitFun n D =(fun x=>circuitFun n C (Function.update x l b))→C.size≤D.size+k):
  Cap C l b k:=by
 rintro⟨s,hs,D,d,a,c⟩;have:=hl D d (funext c);change s+(k+1)≤C.size at hs;omega
lemma pW {n b k} {C D:Circuit} {l:Fin n}
  (c:Cap C l b k) (f:FanInTwo D) (hs:D.size+k=C.size)
  (e:circuitFun n D =fun x=>circuitFun n C (Function.update x l b)):IsMinimalCircuit n D:=by
 refine⟨f,fun E d a=> ?_⟩;by_contra! g;exact c ⟨E.size,by change _≤C.size;omega,E,d,le_rfl,congrFun (a.trans e)⟩
lemma oC {n} {C:Circuit} {l:Fin n} {b} (a:fC C l b):
  ∃x y,circuitFun n C x≠circuitFun n C y:=by
 obtain⟨x,y,c⟩:=a;exact⟨_,_,c⟩
lemma mO {n} {C:Circuit} {l:Fin n} {b} (a:fC C l b):
  C.output≠l.val:=by
 intro d;obtain⟨x,y,c⟩:=a;apply c;change val C _ C.output=val C _ C.output;simp[d,bE]
lemma dJ {C:Circuit} {p a}:bW C.gates p a↔a∈(gateAt C p).inputs:=by
 unfold bW gateAt;rw[List.getD_eq_getElem?_getD]
 cases C.gates[p]?<;>simp
lemma lR {m p a} {C:Circuit} (hmin:IsMinimalCircuit m C)
  (n:∃x y,circuitFun m C x≠circuitFun m C y) (hnot:∀g∈C.gates,g.op≠GateOp.not)
  (hr:bW C.gates p a):∃h,mM C p a h∧
  h< m+p∧h≠a∧((gateAt C p).op= .and∨(gateAt C p).op= .or):=by
 have l:=dU hr;have c:=dJ.mp hr;obtain⟨op,i,j,f,k,d,b⟩:=Al.nY hmin n hnot (show C.gates[p]?=some (gateAt C p) by simp[gateAt,l]);have e:a=i∨a=j:=by simpa[b] using c
 rcases e with rfl|rfl
 ·exact⟨_,Or.inl b,k,d.symm,op⟩
 ·exact⟨_,Or.inr b,f,d,op⟩
lemma pX {g:Gate} {b:Bool} (h:g.op= .and∨g.op= .or)
  (c:b≠eR g):g.op=bU b:=by
 rcases h with a|a<;>cases b<;>simp_all[bU,eR]
lemma sQ {g:Gate} {b:Bool} (h:g.op= .and∨g.op= .or)
  (c:b=eR g):g.op=bU (!b):=by
 rcases h with a|a<;>cases b<;>simp_all[bU,eR]
lemma gR {m b p} {C:Circuit} {l:Fin (m+1)}
  (c:aW (m+1) C.gates) (hr:bW C.gates p l) (a:b=eR (gateAt C p)):
  IsC m C.gates l b (m+1+p):=by
 have d:=dU hr;exact pV m C.gates c l b p (gateAt C p) (by simp[gateAt,d]) l (dJ.mp hr)
  ((uJ _ _ _ _).trans (congrArg Stat.const a))
structure Av {n} (C : Circuit) (l : Fin n) (b : Bool) (p h : ℕ) : Prop where
  real : p < C.gates.length
  pair : mM C p l.val h
  op : (gateAt C p).op = bU b
  earlier : h < n+p
  distinct : h ≠ l.val
  only : ∀ j, bW C.gates j l → j = p
  computes : circuitFun n (erase n C p h) = fun x => circuitFun n C (Function.update x l b)
  least : IsMinimalCircuit n (erase n C p h)
lemma aA4 {m b p} {C:Circuit} (l:Fin (m+1))
  (hmin:IsMinimalCircuit (m+1) C) (hnot:∀g∈C.gates,g.op≠GateOp.not)
  (a:fC C l b) (c:Cap C l b 1) (hr:bW C.gates p l):
  ∃h,Av C l b p h:=by
 have f:=oC a;have L:=Al.least hmin f hnot;obtain⟨h,d,hh,hl,op⟩:=lR hmin f hnot hr;have e:=dU hr;have only:∀j,bW C.gates j l→j=p:=by intro j s;by_contra q;exact c (L.save2 l b a j p q (fO _ s) (fO _ hr))
 have i:(gateAt C p).op=bU b:=by apply pX op;intro o;have r:=gR L.hcl hr o;obtain⟨j,v,_,k⟩:=L.next l b a p e r;exact c (L.save2 l b a p j (by omega) (fO _ hr) k)
 have n:=sO l b e (Al.bM hmin f hnot) d i hh hl (Al.nF f)
  (mO a) (fun j _ u t=>u (only j (dJ.mpr t)))
 exact⟨h,e,d,i,hh,hl,only,n,pW c (fan hmin.1) (erase_length e) n⟩
structure At {n} (C : Circuit) (l : Fin n) (b : Bool) (p h q a : ℕ) : Prop where
  realB : p < C.gates.length
  realD : skip p q < C.gates.length
  ordered : p < skip p q
  pairB : mM C p l.val h
  opB : (gateAt C p).op = bU (!b)
  pairD : mM C (skip p q) (n+p) a
  opD : (gateAt C (skip p q)).op = bU b
  earlierH : h < n+p
  earlierA : a < n+skip p q
  distinctH : h ≠ l.val
  distinctA : a ≠ l.val ∧ a ≠ n+p
  onlyL : ∀ j, bW C.gates j l → j = p
  onlyB : ∀ j, bW C.gates j (n+p) → j = skip p q
  notOutputB : C.output ≠ n+p
  splice : Splice n (bT n C p l.val q a) C (cN p q) (cN (n+p) (n+q))
    (contract (n+p) l.val a) (n+skip p q)
  computes : circuitFun n (bT n C p l.val q a) = fun x => circuitFun n C (Function.update x l b)
  least : IsMinimalCircuit n (bT n C p l.val q a)
lemma aA5 {m b p} {C:Circuit} (l:Fin (m+1))
  (hmin:IsMinimalCircuit (m+1) C) (hnot:∀g∈C.gates,g.op≠GateOp.not)
  (d:fC C l b) (v:Cap C l b 2) (hr:bW C.gates p l)
  (K:b=eR (gateAt C p)):∃h q a,At C l b p h q a:=by
 have B:=oC d;have L:=Al.least hmin B hnot;have back:=Al.bM hmin B hnot;obtain⟨h,o,hh,hl,opB⟩:=lR hmin B hnot hr;have u:=sQ opB K;have A:=dU hr;have k:=gR L.hcl hr K;obtain⟨r,S,n,M⟩:=L.next l b d p A k;have onlyL:∀j,bW C.gates j l→j=p:=by intro j w;by_contra N;exact v (L.third l b d p j (Ne.symm N) hr w k)
 have onlyB:∀j,bW C.gates j (m+1+p)→j=r:=by intro j w;by_contra N;have X:=uA L.hcl w;exact v (L.save3 l b d p j r (by omega) (by omega) N (fO _ hr) (oB w k) M)
 have i:C.output≠m+1+p:=by intro F;obtain⟨c,k⟩:=k;obtain⟨x,y,T⟩:=d;rw[←F] at k;exact T ((dC L.hcl L.hev l b c k x).trans (dC L.hcl L.hev l b c k y).symm)
 have t:=dU n;obtain⟨a,s,Q,H,opD⟩:=lR hmin B hnot n;have J:a≠l.val:=by
  intro F;subst a;have z:l.val∈(gateAt C r).inputs:=by rcases s with h|h<;>simp[h]
  exact(by omega:r≠p) (onlyL r (dJ.mpr z))
 have E:(gateAt C r).op=bU b:=by
  apply pX opD;intro V;obtain⟨c,hs⟩:=k
  let x:Fin (m+1)→Bool:=Function.update (fun _=>false) l b
  have O:val C x (m+1+p)=b:=(iM back A u o (by simp[x,bE])).trans (by simp[x,bE]);have F:c=b:=by have P:=mL m C.gates L.hcl l b _ c hs (Fin.removeNth l (fun _=>false));rw[←sM] at P;change val C x (m+1+p)=c at P;exact P.symm.trans O
  have R:=pV m C.gates L.hcl l b r (gateAt C r) (by simp[gateAt,t]) _ (dJ.mp n)
   (hs.trans (congrArg Stat.const (F.trans V)))
  obtain⟨j,Z,_,U⟩:=L.next l b d r t R;exact v (L.save3 l b d p r j (by omega) (by omega) (by omega) (fO _ hr) M U)
 let q:=r-1
 have f:skip p q=r:=by rw[aQ];dsimp[q];split<;>omega
 have unique:∀j,l.val∉(gateAt C (cN p q j)).inputs∧
   m+1+p∉(gateAt C (cN p q j)).inputs:=by
  intro j;refine⟨fun z=>fA p _ (onlyL _ (dJ.mpr z)),fun z=> ?_⟩;have e:=onlyB _ (dJ.mpr z);rw[←f] at e;exact fA q j ((skip p).injective e)
 have G:=sP l b A (f▸t) back o u (f▸s) (f▸E)
  (f▸Q) J H (Al.nF B) (mO d) i unique
 refine⟨h,q,a,A,f▸t,f▸S,o,u,f▸s,f▸E,hh,f▸Q,hl,
  ⟨J,H⟩,onlyL,fun j w=>(onlyB j w).trans f.symm,i,
  kW i (fun j=>(unique j).2),G,
  pW v (fan (fan hmin.1)) (kV A (f▸t)) G⟩
end PEqualNP.MetaComplexity.NestedCover.Ac
namespace PEqualNP.MetaComplexity.NestedCover.Ac
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.Aa Au
variable {n p q h a : ℕ} {C : Circuit} {b : Bool} {l : Fin n}
lemma gG (g:ReadsBack n C) (d:fC C l b)
  (e:Dep (circuitFun n C) l):∃p,bW C.gates p l:=by
 by_contra! f;have i:∀j<C.gates.length,l.val∉(gateAt C j).inputs:=fun j _ hl=>f j (dJ.mpr hl)
 have k:C.output≠l.val:=by intro h;obtain⟨x,y,c⟩:=d;apply c;change val C _ C.output=val C _ C.output;simp[h,bE]
 obtain⟨x,y,c⟩:=d;have a:=Al.nF ⟨_,_,c⟩;obtain⟨z,m⟩:=e;exact m (jH g i z _ _ a k)
def zO (C:Circuit) (l:Fin n) (b:Bool) (k:ℕ):Prop:=
 ∀
  D:Circuit,FanInTwo D→circuitFun n D =(fun x=>circuitFun n C (Function.update x l b))→
  C.size≤D.size+k
lemma sR (hmin:IsMinimalCircuit n C) (hnot:∀g∈C.gates,g.op≠GateOp.not)
  (a:Dep (circuitFun n C) l) (c:fC C l b) (aT:zO C l b 1):
  ∃p h,Av C l b p h:=by
 cases n with
 | zero=>exact Fin.elim0 l
 | succ m=>
   have d:=zM a;obtain⟨p,hr⟩:=gG (Al.bM hmin d hnot) c a;exact⟨p,aA4 l hmin hnot c (mN aT) hr⟩
lemma sS (hmin:IsMinimalCircuit n C) (hnot:∀g∈C.gates,g.op≠GateOp.not)
  (c:Dep (circuitFun n C) l) (d:∀b,fC C l b) (aT:∀b,zO C l b 2):
  ∃b p h q a,At C l b p h q a:=by
 cases n with
 | zero=>exact Fin.elim0 l
 | succ m=>
   obtain⟨p,hr⟩:=gG (Al.bM hmin (zM c) hnot) (d false) c;exact⟨_,p,aA5 l hmin hnot (d _) (mN (aT _)) hr rfl⟩
lemma lS (b:p<C.gates.length):
  Finset.range C.gates.length=insert p ((Finset.range (erase n C p h).gates.length).map (skip p)):=by
 ext i;simp only[Finset.mem_range,Finset.mem_insert,Finset.mem_map];constructor
 ·intro d;by_cases c:i=p
  ·exact Or.inl c
  ·have a:=eF (h:=0) c;exact Or.inr ⟨_,(aS b).mpr (by rw[a];exact d),a⟩
 ·rintro(rfl|⟨j,a,rfl⟩)
  ·exact b
  ·exact(aS b).mp a
lemma pY (b:p<C.gates.length) (d:skip p q<C.gates.length):
  Finset.range C.gates.length=insert p (insert (skip p q)
   ((Finset.range (bT n C p h q a).gates.length).map (cN p q))):=by
 have hr:=lS (n:=n) (h:=h) b;have c:q<(erase n C p h).gates.length:=(aS b).mpr d;rw[lS (n:=n) (h:=contract (n+p) h a) c,Finset.map_insert,Finset.map_map] at hr;exact hr
lemma fixed (l:Fin n) (p:ℕ):skip (n+p) l.val=l.val:=by simp[aQ,show l.val<n+p by have:=l.isLt;omega]
lemma nJ (l:Fin n) (p q:ℕ):cN (n+p) (n+q) l.val=l.val:=by simp[bX,fixed]
lemma zP (p q k:ℕ):cN p q k≠p∧cN p q k≠skip p q:=⟨fA _ _,fun a=>fA _ _ ((skip p).injective a)⟩
lemma Av.size (s:Av C l b p h):(erase n C p h).size+1=C.size:=erase_length s.real
lemma At.size (s:At C l b p h q a):(bT n C p l.val q a).size+2=C.size:=kV s.realB s.realD
lemma Av.splice (a:Av C l b p h):Splice n (erase n C p h) C (skip p) (skip (n+p)) h (n+p):=fB
lemma Av.mapH (s:Av C l b p h):skip (n+p) h=h:=by simp[aQ,s.earlier]
lemma At.mapH (s:At C l b p h q a):cN (n+p) (n+q) h=h:=by
 have d:=s.earlierH;have c:=s.ordered;rw[aQ] at c;have hh:h<n+q:=by split at c<;>omega
 simp[bX,aQ,hh,d]
lemma At.mapA (s:At C l b p h q a):
  cN (n+p) (n+q) (contract (n+p) l.val a)=a:=by
 have hh:l.val<n+p:=by have:=l.isLt;omega
 have c:=bI hh (show a<skip (n+p) (n+q) by rw[align];exact s.earlierA);rw[bX,show skip (n+q) (contract (n+p) l.val a)=contract (n+p) l.val a by simp[aQ,c],eF s.distinctA.2]
end PEqualNP.MetaComplexity.NestedCover.Ac
namespace Aq
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover SimpleGraph
open Ac
def lT (n:ℕ):Prop:=
 ∀
  (K:SimpleGraph (Fin n)) [DecidableRel K.Adj] A l p C i h,
  K.IsAcyclic→cK K A→bC K l p→
  IsMinimalCircuit n C→circuitFun n C=graphFun K A→
  Av C l false i h→IsNestedCoverCircuit n (K.deleteIncidenceSet l) A (erase n C i h)→
  IsNestedCoverCircuit n K A C
def iB (n:ℕ):Prop:=
 ∀
  (K:SimpleGraph (Fin n)) [DecidableRel K.Adj] A l p q C i h j a,
  K.IsAcyclic→cK K A→bC K l p→(∀v,K.Adj p v→v=l∨v=q)→
  (∀S,IsMinCover (K.deleteIncidenceSet l) S→p∉S)→
  IsMinimalCircuit n C→circuitFun n C=graphFun K A→
  At C l false i h j a→
  IsNestedCoverCircuit n (K.deleteIncidenceSet l) A (bT n C i l.val j a)→
  IsNestedCoverCircuit n K A C
def jI (n:ℕ):Prop:=
 ∀
  (K:SimpleGraph (Fin n)) [DecidableRel K.Adj] A l p q C i h j a,
  K.IsAcyclic→cK K A→bC K l p→q≠l→
  (∀v,K.Adj p v↔v=l∨v=q)→
  IsMinimalCircuit n C→circuitFun n C=graphFun K A→
  At C l true i h j a→
  IsNestedCoverCircuit n ((K.deleteIncidenceSet l).deleteIncidenceSet p) (insert p A)
   (bT n C i l.val j a)→IsNestedCoverCircuit n K A C
lemma pZ {n} {C:Circuit} {l:Fin n} {b:Bool}
  {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {U:Finset (Fin n)} (a:nE G U)
  (c:∀x,circuitFun n C (Function.update x l b)=graphFun G U x):fC C l b:=by
 exact⟨fun _=>false,fun _=>true,by simpa only[c] using(Al.gE a)⟩
lemma jJ {n} (tO:lT n):uI n:=by
 intro K A l p f iso leaf a m dec C min d
 letI:=dec
 have e:=xT (A:=A) leaf a;have j:=fun x=>(congrFun d (Function.update x l false)).trans (eA leaf iso x)
 have b:=nZ leaf f iso e min d (k:=1) (fun T S ht hs=>by rw[pJ ht hs a]);have g:Aa.Au.Dep (circuitFun n C) l:=by rw[d];exact gD leaf iso
 have lp:=(leaf p).2 rfl;obtain⟨T,ht⟩:=Ai.aU K;have o:=(Ai.aK f iso (Or.inr ⟨_,_,lp⟩) ht min d).2;obtain⟨i,h,c⟩:=sR min o g (pZ e j) b;exact tO K A l p C i h f iso leaf min d c
  (m inferInstance _ c.least (c.computes.trans (funext j)))
lemma kN {n} (J:iB n) (H:jI n):wV n:=by
 intro K A l p q k iso leaf f m t u dec C min d
 letI:=dec
 have o:=fun x=>(congrFun d (Function.update x l false)).trans (eA leaf iso x)
 have r:=fun x=>(congrFun d (Function.update x l true)).trans ((iK leaf iso f x).2)
 have F:∀b,fC C l b:=by
  intro b
  cases b
  ·exact pZ m o
  ·exact pZ (Or.inl (Finset.insert_nonempty _ _)) r
 have y:∀b,zO C l b 2:=by
  intro b
  cases b
  ·apply nZ leaf k iso m min d;intro T S ht hs;have:=(oP ht hs).2;omega
  ·exact vX leaf f k iso min d
 have z:Aa.Au.Dep (circuitFun n C) l:=by rw[d];exact gD leaf iso
 have lp:=(leaf p).2 rfl;obtain⟨T,ht⟩:=Ai.aU K;have G:=(Ai.aK k iso (Or.inr ⟨_,_,lp⟩) ht min d).2;obtain⟨b,i,h,j,a,c⟩:=sS min G z F y
 cases b
 ·have s:=c.computes.trans (funext o);exact J K A l p q C i h j a k iso leaf f
   (fun S hs=>jF leaf k iso m min d c.least s c.size hs)
   min d c (t inferInstance _ c.least s)
 ·have s:=c.computes.trans (funext r);obtain⟨w,E,B⟩:=hX leaf k iso min d c.least s c.size;obtain rfl:=(f w E).resolve_left B;have eP (v):K.Adj p v↔v=l∨v=w:=
   ⟨f v,fun e=>e.elim (fun g=>g▸lp.symm) (fun g=>g▸E)⟩
  exact H K A l p w C i h j a k iso leaf B eP min d c (u inferInstance _ c.least s)
lemma dW {n} (one:lT n) (zero:iB n)
  (a:jI n) (K:SimpleGraph (Fin n)) [DecidableRel K.Adj] (A:Finset (Fin n))
  (b:K.IsAcyclic) (iso:cK K A) (c:nE K A) (C:Circuit):
  (IsMinimalCircuit n C∧circuitFun n C=graphFun K A)↔IsNestedCoverCircuit n K A C:=
 eQ (jJ one)
  (kN zero a) K A b iso c C
end Aq
namespace PEqualNP.MetaComplexity.NestedCover.Af
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
inductive Below (n : ℕ) (C : Circuit) (G : Finset ℕ) (a : ℕ) : ℕ → Prop where
  | refl : Below n C G a a
  | step {w j} : Below n C G a w → j ∈ G → w ∈ (gateAt C j).inputs →
      Below n C G a (n+j)
lemma Below.le {a w} (b:Below n C G a w) (back:ReadsBack n C)
  (bd:∀j∈G,j<C.gates.length):a≤w:=by
 induction b with
 | refl=>exact le_rfl
 | step _ hj hw ih=>exact ih.trans (back _ (bd _ hj) _ hw).le
lemma Below.push {a w} (b:Below n C G a w) {P:ℕ→Prop}
  (step:∀j∈G,∀i∈(gateAt C j).inputs,P i→P (n+j)) (h:P a):P w:=by
 induction b with
 | refl=>exact h
 | step _ hj hw ih=>exact step _ hj _ hw ih
def fQ (n:ℕ) (G L:Finset ℕ) (w:ℕ):Prop:=w∈L∨∃j∈G,w=n+j
lemma gS (tr:IsOrTree n C G L ρ) (back:ReadsBack n C)
  (bd:∀j∈G,j<C.gates.length) (P:ℕ→Prop)
  (e:∀j∈G,P (n+j)↔∃i∈(gateAt C j).inputs,P i)
  {w} (node:fQ n G L w):
  P w↔∃a∈L,Below n C G a w∧P a:=by
 constructor
 ·induction w using Nat.strong_induction_on with
  | ind w ih=>
    intro d;rcases node with g|⟨j,c,rfl⟩
    ·exact⟨_,g,.refl,d⟩
    obtain⟨i,f,pi⟩:=(e _ c).1 d;have m:=back j (bd j c) i f;have o:fQ n G L i:=by
     rcases (tr.1 _ c).2.2 _ f with hl|⟨p,gi⟩
     ·exact Or.inl hl
     ·exact Or.inr ⟨_,gi,by omega⟩
    obtain⟨a,l,k,h⟩:=ih i m o pi;exact⟨a,l,k.step c f,h⟩
 ·rintro⟨a,_,b,h⟩;exact b.push (fun j c w g d=>(e j c).2 ⟨w,g,d⟩) h
variable {K : SimpleGraph (Fin n)} {d : NCCData n} {A : Finset (Fin n)}
    {x : Fin n → Bool} {u v s t r q k : Fin n}
abbrev Z (v:Fin n) (d:NCCData n) (C:Circuit):=gatesOf d C Kind.z v.val
abbrev O (v:Fin n) (d:NCCData n) (C:Circuit):=gatesOf d C Kind.o v.val
abbrev dP (v:Fin n) (d:NCCData n) (C:Circuit):=fQ n (Z v d C) (zLeaves d v)
abbrev uO (v:Fin n) (d:NCCData n) (C:Circuit):=fQ n (O v d C) (oLeaves d v)
lemma aT {k:Kind} {v:ℕ}:∀j∈gatesOf d C k v,j<C.gates.length:=fun _ a=>Finset.mem_range.mp (Finset.mem_filter.mp a).1
lemma dF {i}:
  i∈zLeaves d v↔i=v.val∨∃s∈d.cover,d.tie s=some v∧d.bw s=i:=by
 simp[zLeaves,and_assoc]
lemma iZ {i}:i∈oLeaves d v↔∃r,d.owns v r=true∧d.lam v r=i:=by simp[oLeaves]
lemma gT (back:ReadsBack n C) (tr:IsOrTree n C G L ρ)
  (bd:∀j∈G,j<C.gates.length):
  ∀j∈G,W C x (n+j)↔∃i∈(gateAt C j).inputs,W C x i:=
 fun _ a=>aY back (bd _ a) (tr.1 _ a).1
lemma cC (tr:IsOrTree n C G L ρ):fQ n G L ρ:=by
 by_cases h:G= ∅
 ·have e:L={ρ}:=by simpa[h] using tr.2.2.2
  exact Or.inl (by simp[e])
 ·exact Or.inr (by simpa[h] using tr.2.2.2)
variable (h : Valid n K A C d)
include h
lemma dN (a:v∈d.cover):TermOK n C d v:=(h.2.2.2.2.2.1 v a).1
lemma bL (a:v∈d.cover):IsOrTree n C (Z v d C) (zLeaves d v) (d.zroot v):=(h.2.2.2.2.2.1 v a).2.1
lemma cT (a:v∈d.cover):IsOrTree n C (O v d C) (oLeaves d v) (d.oroot v):=(h.2.2.2.2.2.1 v a).2.2.1
lemma lam (edge:d.owns u v=true):LamOK n C d u v:=(h.2.2.2.2.2.1 u (h.2.2.1.1 _ _ edge).2).2.2.2 _ edge
lemma jK (e:v∈d.cover) {w} (k:dP v d C w):
  IsCentred n C d w↔Below n C (Z v d C) v.val w:=by
 have c:=fun j (hj:j∈Z v d C)=>
  cJ (d:=d) h.1 (aT j hj)
   (congrArg Prod.fst (Finset.mem_filter.mp hj).2)
 rw[gS (bL h e) h.1 aT _ c k];constructor
 ·rintro⟨a,i,f,g⟩;rcases dF.mp i with rfl|⟨s,hs,_,rfl⟩
  ·exact f
  ·exact(cM (dN h hs) g).elim
 ·intro b;exact⟨_,dF.mpr (Or.inl rfl),b,(aG v).2 e⟩
lemma qA (c:v∈d.cover) {w} (e:dP v d C w):
  W
   C x w↔(IsCentred n C d w∧x v=true)∨
   ∃s∈d.cover,d.tie s=some v∧Below n C (Z v d C) (d.bw s) w∧W C x (d.bw s):=by
 rw[jK h c e,gS (bL h c) h.1 aT _ (gT h.1 (bL h c) aT) e];constructor
 ·rintro⟨a,g,b,f⟩;rcases dF.mp g with rfl|⟨s,hs,τ,rfl⟩
  ·exact Or.inl ⟨b,(aC v).1 f⟩
  ·exact Or.inr ⟨s,hs,τ,b,f⟩
 ·rintro(⟨b,xv⟩|⟨s,hs,τ,b,ws⟩)
  ·exact⟨_,dF.mpr (Or.inl rfl),b,(aC v).2 xv⟩
  ·exact⟨_,dF.mpr (Or.inr ⟨s,hs,τ,rfl⟩),b,ws⟩
lemma iC (b:v∈d.cover):
  W C x (d.zroot v)↔x v=true∨∃s∈d.cover,d.tie s=some v∧W C x (d.bw s):=by
 rw[fI (bL h b) h.1 aT _ (gT h.1 (bL h b) aT)];constructor
 ·rintro⟨a,e,c⟩;rcases dF.mp e with rfl|⟨s,hs,τ,rfl⟩
  ·exact Or.inl ((aC v).1 c)
  ·exact Or.inr ⟨s,hs,τ,c⟩
 ·rintro(xv|⟨s,hs,τ,ws⟩)
  ·exact⟨_,dF.mpr (Or.inl rfl),(aC v).2 xv⟩
  ·exact⟨_,dF.mpr (Or.inr ⟨s,hs,τ,rfl⟩),ws⟩
lemma fR (e:v∈d.cover):
  W C x (d.oroot v)↔∃r,d.owns v r=true∧W C x (d.lam v r):=by
 rw[fI (cT h e) h.1 aT _ (gT h.1 (cT h e) aT)];constructor
 ·rintro⟨a,f,c⟩;obtain⟨r,b,rfl⟩:=iZ.mp f;exact⟨r,b,c⟩
 ·rintro⟨r,b,c⟩;exact⟨_,iZ.mpr ⟨r,b,rfl⟩,c⟩
lemma sT (c:d.owns u v=true) (b:x v=true):W C x (d.lam u v):=by
 have l:=lam h c;by_cases a:v∈d.cover
 ·simp only[LamOK,a,↓reduceIte] at l;rcases l.2.1 with e|⟨j,f,e,role⟩
  ·exact e▸(aC v).2 b
  ·exact(qA h a (Or.inr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f,role⟩,e⟩)).2
    (Or.inl ⟨l.1,b⟩)
 ·simp only[LamOK,a,↓reduceIte] at l;exact l▸(aC v).2 b
lemma sU (f:d.owns u v=true) (b:W C x (d.lam u v)):
  x v=true∨∃s∈d.cover,d.tie s=some v∧W C x (d.bw s)∧d.bw s≤d.lam u v:=by
 have l:=lam h f;by_cases a:v∈d.cover
 ·simp only[LamOK,a,↓reduceIte] at l;rcases l.2.1 with e|⟨j,g,e,role⟩
  ·exact Or.inl ((aC v).1 (e▸b))
  ·have node:dP v d C (d.lam u v):=
    Or.inr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr g,role⟩,e⟩
   rcases (qA h a node).1 b with⟨_,i⟩|⟨s,hs,τ,c,ws⟩
   ·exact Or.inl i
   ·exact Or.inr ⟨s,hs,τ,ws,c.le h.1 aT⟩
 ·simp only[LamOK,a,↓reduceIte] at l;exact Or.inl ((aC v).1 (l▸b))
lemma kC (e:v∈d.cover):
  d.zroot v<d.bw v∧d.oroot v<d.bw v:=by
 obtain⟨j,c,b,_,_,a⟩:=dN h e;rw[b];rcases a with a|a<;>constructor<;>apply h.1 j c<;>simp[a]
def May (x:Fin n→Bool) (d:NCCData n) (P:Fin n→Prop) (v:Fin n):=x v=true∨∃s∈d.cover,d.tie s=some v∧P s
lemma dK (P:Fin n→Prop)
  (step:∀u∈d.cover,May x d P u→(∃v,d.owns u v=true∧May x d P v)→P u)
  (a:u∈d.cover) (e:W C x (d.bw u)):P u:=by
 suffices all:∀b,∀u∈d.cover,d.bw u=b→W C x b→P u from all _ u a rfl e
 intro b
 induction b using Nat.strong_induction_on with
 | ind b ih=>
   rintro u a rfl e;obtain⟨l,k⟩:=(bO h.1 (dN h a)).1 e;obtain⟨v,c,j⟩:=(fR h a).1 k;obtain⟨i,g⟩:=kC h a;apply step _ a
   ·rcases (iC h a).1 l with m|⟨s,hs,τ,ws⟩
    ·exact Or.inl m
    ·have le:=lM (bL h a) h.1 aT _ (dF.mpr (Or.inr ⟨s,hs,τ,rfl⟩));exact Or.inr ⟨s,hs,τ,ih _ (le.trans_lt i) s hs rfl ws⟩
   ·refine⟨v,c,?_⟩;rcases sU h c j with o|⟨s,hs,τ,ws,le⟩
    ·exact Or.inl o
    ·have f:=lM (cT h a) h.1 aT _ (iZ.mpr ⟨v,c,rfl⟩);exact Or.inr ⟨s,hs,τ,ih _ ((le.trans f).trans_lt g) s hs rfl ws⟩
lemma uP (edge:d.owns t r=true) (b:x t=true) (a:x r=true):
  W C x (d.bw t):=by
 have ht:=(h.2.2.1.1 _ _ edge).2;exact(bO h.1 (dN h ht)).2
  ⟨(iC h ht).2 (.inl b),(fR h ht).2 ⟨_,edge,sT h edge a⟩⟩
lemma aA6 (τ:d.tie t=some q) (c:W C x (d.bw t)):W C x (d.bw q):=by
 obtain⟨ht,a⟩:=h.2.2.2.1 _ _ τ;have b:=(h.2.2.1.1 _ _ a).2;have l:=lam h a;simp only[LamOK,ht,↓reduceIte] at l;exact(bO h.1 (dN h b)).2
  ⟨(iC h b).2 (.inr ⟨t,ht,τ,c⟩),
    (fR h b).2 ⟨_,a,(l.2.2 τ)▸((bO h.1 (dN h ht)).1 c).1⟩⟩
def pair (t r:Fin n) (v:Fin n):=decide (v=t∨v=r)
def single (t:Fin n) (v:Fin n):=decide (v=t)
lemma mP (edge:d.owns t r=true) (τ:d.tie t=none) (c:u∈d.cover):
  W C (pair t r) (d.bw u)↔u=t:=by
 constructor
 ·apply dK h (· =t) _ c;intro u _ e ⟨v,ev,f⟩;have a (i):May (pair t r) d (· =t) i→i=t∨i=r:=by
   rintro(xi|⟨s,_,ts,rfl⟩)
   ·simpa[pair] using xi
   ·simp[τ] at ts
  rcases a _ e with b|rfl
  ·exact b
  rcases a _ f with rfl|rfl
  ·exact False.elim ((h.2.2.1.2 _ _ (h.2.2.1.1 _ _ edge).1) (edge.trans ev.symm))
  ·exact False.elim ((h.2.2.1.1 _ _ ev).1.ne rfl)
 ·rintro rfl;exact uP h edge (by simp[pair]) (by simp[pair])
lemma jL (edge:d.owns t r=true) (τ:d.tie t=some q)
  (τq:d.tie q=none) (hr:r∉d.cover) (a:u∈d.cover):
  W C (pair t r) (d.bw u)↔u=t∨u=q:=by
 constructor
 ·apply dK h (fun i=>i=t∨i=q) _ a;rintro u a (xu|⟨s,_,ts,es⟩) _
  ·rcases of_decide_eq_true xu with e|e
   ·exact Or.inl e
   ·exact(hr (e▸a)).elim
  ·rcases es with rfl|rfl
   ·exact Or.inr (Option.some.inj (ts.symm.trans τ))
   ·simp[τq] at ts
 ·have b:=uP h (x:=pair t r) edge (by simp[pair]) (by simp[pair]);rintro(rfl|rfl)
  ·exact b
  ·exact aA6 h τ b
lemma bY (b:u∈d.cover) (k:Fin n):¬W C (single k) (d.bw u):=by
 apply dK h (fun _=>False) _ b;rintro u _ (xu|⟨_,_,_,a⟩) ⟨v,ev,mv⟩
 ·rcases mv with c|⟨_,_,_,a⟩
  ·have f:u=k:=of_decide_eq_true xu;have e:v=k:=of_decide_eq_true c;subst u;subst v;exact(h.2.2.1.1 _ _ ev).1.ne rfl
  ·exact a
 ·exact a
lemma zQ (edge:d.owns t r=true) (τ:d.tie t=none)
  (a:v∈d.cover) {w} (b:dP v d C w):
  W C (pair t r) w↔IsCentred n C d w∧(v=t∨v=r):=by
 rw[qA h a b];simp only[pair,decide_eq_true_eq];refine or_iff_left ?_;rintro⟨s,hs,c,_,ws⟩;obtain rfl:=(mP h edge τ hs).1 ws;simp[τ] at c
lemma aA7 (edge:d.owns t r=true) (τ:d.tie t=some q)
  (τq:d.tie q=none) (hr:r∉d.cover) (c:v∈d.cover) {w} (e:dP v d C w):
  W
   C (pair t r) w↔(IsCentred n C d w∧(v=t∨v=r))∨
   (q=v∧Below n C (Z v d C) (d.bw t) w):=by
 rw[qA h c e];simp only[pair,decide_eq_true_eq];apply or_congr_right;constructor
 ·rintro⟨s,hs,b,a,ws⟩;rcases (jL h edge τ τq hr hs).1 ws with rfl|rfl
  ·exact⟨Option.some.inj (τ.symm.trans b),a⟩
  ·simp[τq] at b
 ·rintro⟨rfl,a⟩;have ht:=(h.2.2.1.1 _ _ edge).2;exact⟨t,ht,τ,a,(jL h edge τ τq hr ht).2 (Or.inl rfl)⟩
lemma jM (a:v∈d.cover) {w} (b:dP v d C w) (k:Fin n):
  W C (single k) w↔IsCentred n C d w∧v=k:=by
 rw[qA h a b];simp only[single,decide_eq_true_eq];refine or_iff_left ?_;rintro⟨s,hs,_,_,ws⟩;exact bY h hs k ws
lemma iD (edge:d.owns u v=true) (k:Fin n):
  W C (single k) (d.lam u v)↔v=k:=by
 constructor
 ·intro a;rcases sU h edge a with b|⟨s,hs,_,ws,_⟩
  ·exact of_decide_eq_true b
  ·exact(bY h hs k ws).elim
 ·rintro rfl;exact sT h edge (by simp[single])
lemma jN (c:u∈d.cover) {w} (g:uO u d C w) (k:Fin n):
  W C (single k) w↔d.owns u k=true∧Below n C (O u d C) (d.lam u k) w:=by
 rw[gS (cT h c) h.1 aT _ (gT h.1 (cT h c) aT) g];constructor
 ·rintro⟨a,f,e,i⟩;obtain⟨v,ev,rfl⟩:=iZ.mp f;obtain rfl:=(iD h ev k).1 i;exact⟨ev,e⟩
 ·rintro⟨ev,b⟩;exact⟨_,iZ.mpr ⟨_,ev,rfl⟩,b,(iD h ev k).2 rfl⟩
end PEqualNP.MetaComplexity.NestedCover.Af
namespace PEqualNP.MetaComplexity.NestedCover.Af
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ w i j k : ℕ}
lemma bZ (tr:IsOrTree n C G L ρ) (b:j∈G) (a:i∈(gateAt C j).inputs):
  fQ n G L i:=by
 rcases (tr.1 _ b).2.2 _ a with hl|⟨c,gi⟩
 ·exact Or.inl hl
 ·exact Or.inr ⟨_,gi,by omega⟩
lemma iE (tr:IsOrTree n C G L ρ) (b:fQ n G L w):
  readsIn C G w=if w=ρ then 0 else 1:=by
 rcases b with hl|⟨j,a,rfl⟩
 ·exact(tr.2.1 _ hl).2
 ·exact tr.2.2.1 _ a
lemma jO (tr:IsOrTree n C G L ρ) (e:fQ n G L w) (a:w≠ρ):
  ∃j∈G,w∈(gateAt C j).inputs:=by
 by_contra! hh;have b:readsIn C G w=0:=Finset.sum_eq_zero (fun j d=>List.count_eq_zero_of_not_mem (hh j d));have c:=iE tr e;simp[a,b] at c
lemma kY (tr:IsOrTree n C G L ρ)
  (c:j∈G) (g:k∈G) (e:w∈(gateAt C j).inputs) (i:w∈(gateAt C k).inputs):
  j=k:=by
 by_contra h
 let f:=fun j=>(gateAt C j).inputs.count w
 have l:0<f j:=List.count_pos_iff.mpr e;have m:0<f k:=List.count_pos_iff.mpr i;have d:∑p∈({j,k}:Finset ℕ),f p≤ readsIn C G w:=
  Finset.sum_le_sum_of_subset_of_nonneg (fun z b=>by
   rcases Finset.mem_insert.mp b with rfl|b
   ·exact c
   ·obtain rfl:=Finset.mem_singleton.mp b;exact g) (by intros;omega)
 simp[h] at d;have a:=iE tr (bZ tr c e)
 split at a<;>omega
lemma jP (tr:IsOrTree n C G L ρ) (d:j∈G):
  ∃a b,(gateAt C j).inputs=[a,b]∧a≠b:=by
 obtain⟨a,b,c⟩:=List.length_eq_two.mp (tr.1 _ d).2.1;refine⟨a,b,c,?_⟩;rintro rfl;have g:a∈(gateAt C j).inputs:=by simp[c]
 have e:=iE tr (bZ tr d g);have le:(gateAt C j).inputs.count a≤ readsIn C G a:=Finset.single_le_sum (f:=fun p=>(gateAt C p).inputs.count a) (fun _ _=>Nat.zero_le _) d;rw[c] at le;simp at le
 split at e<;>omega
lemma Below.first {a w} (b:Below n C G a w) (g:a≠w):
  ∃j∈G,a∈(gateAt C j).inputs∧Below n C G (n+j) w:=by
 induction b with
 | refl=>exact(g rfl).elim
 | @step i k bi hk hi ih=>
   by_cases d:a=i
   ·exact⟨k,hk,d▸hi,.refl⟩
   ·obtain⟨j,f,c,e⟩:=ih d;exact⟨j,f,c,e.step hk hi⟩
lemma Below.advance {a w} (b:Below n C G a w) (h:a≠w) (tr:IsOrTree n C G L ρ)
  (f:j∈G) (e:a∈(gateAt C j).inputs):Below n C G (n+j) w:=by
 obtain⟨k,g,c,d⟩:=b.first h;obtain rfl:=kY tr g f c e;exact d
lemma fS (tr:IsOrTree n C G L ρ) (back:ReadsBack n C)
  (bd:∀j∈G,j<C.gates.length) (P:ℕ→Prop)
  (d:∀a∈L,P a)
  (c:∀j∈G,(∀a∈(gateAt C j).inputs,P a)→P (n+j)):
  ∀w,fQ n G L w→P w:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
   rintro(b|⟨j,hj,rfl⟩)
   ·exact d _ b
   ·exact c _ hj (fun a b=>ih _ (back _ (bd _ hj) _ b) (bZ tr hj b))
lemma jQ (tr:IsOrTree n C G L ρ) (back:ReadsBack n C)
  (bd:∀j∈G,j<C.gates.length) (l:fQ n G L w)
  (all:∀a∈L,Below n C G a w):w=ρ:=by
 have c:=fS tr back bd (fun a=>Below n C G a w) all
  (fun j d hh=>by
    obtain⟨a,b,e,m⟩:=jP tr d;have f:a∈(gateAt C j).inputs:=by simp[e]
    have h:b∈(gateAt C j).inputs:=by simp[e]
    by_cases g:a=w
    ·exact(hh _ h).advance (fun k=>m (g.trans k.symm)) tr d h
    ·exact(hh _ f).advance g tr d f)
 by_contra i;obtain⟨j,d,f⟩:=jO tr l i;exact(not_lt_of_ge ((c _ (.inr ⟨j,d,rfl⟩)).le back bd)) (back _ (bd _ d) _ f)
lemma lU (tr:IsOrTree n C G L ρ) (back:ReadsBack n C)
  (bd:∀j∈G,j<C.gates.length):
  ∀j∈G,∃a∈L,∃b∈L,a≠b∧Below n C G a (n+j)∧Below n C G b (n+j):=by
 intro j
 induction j using Nat.strong_induction_on with
 | ind j ih=>
   intro c;obtain⟨a,b,e,m⟩:=jP tr c;have h:a∈(gateAt C j).inputs:=by simp[e]
   have l:b∈(gateAt C j).inputs:=by simp[e]
   have lift (i) (hi:i∈(gateAt C j).inputs) (g:∃k∈G,i=n+k):
     ∃a∈L,∃b∈L,a≠b∧Below n C G a (n+j)∧Below n C G b (n+j):=by
    obtain⟨k,s,rfl⟩:=g;have lt:=back _ (bd _ c) _ hi;obtain⟨a,d,b,f,m,o,q⟩:=ih k (by omega) s;exact⟨a,d,b,f,m,o.step c hi,q.step c hi⟩
   rcases bZ tr c h with d|p
   ·rcases bZ tr c l with f|r
    ·exact⟨a,d,b,f,m,Below.step Below.refl c h,Below.step Below.refl c l⟩
    ·exact lift _ l r
   ·exact lift _ h p
variable {K : SimpleGraph (Fin n)} {d : NCCData n} {A : Finset (Fin n)} {v : Fin n}
lemma kZ (h:Valid n K A C d) (c:v∈d.cover) (g:j∈O v d C):
  ∃
   a b,a≠b∧d.owns v a=true∧d.owns v b=true∧
   W C (single a) (n+j)∧W C (single b) (n+j):=by
 obtain⟨a,m,b,p,q,l,o⟩:=lU (cT h c) h.1 aT j g;obtain⟨u,f,rfl⟩:=iZ.mp m;obtain⟨k,ev,rfl⟩:=iZ.mp p;have i:uO v d C (n+j):=Or.inr ⟨j,g,rfl⟩;exact⟨u,k,fun e=>q (congrArg _ e),f,ev,(jN h c i u).2 ⟨f,l⟩,(jN h c i k).2 ⟨ev,o⟩⟩
lemma xV (h:Valid n K A C d) (b:v∈d.cover) (c:dP v d C w)
  (f:IsCentred n C d w) (all:∀s∈d.cover,d.tie s=some v→Below n C (Z v d C) (d.bw s) w):
  w=d.zroot v:=by
 apply jQ (bL h b) h.1 aT c;intro a e;rcases dF.mp e with rfl|⟨s,hs,g,rfl⟩
 ·exact(jK h b c).1 f
 ·exact all _ hs g
end PEqualNP.MetaComplexity.NestedCover.Af
namespace PEqualNP.MetaComplexity.NestedCover.Ar
variable {n : ℕ} {d : NCCData n} {A : Finset (Fin n)} {p : Fin n}
variable {K : SimpleGraph (Fin n)}
structure Sig (d : NCCData n) where
  z : Fin n → Prop
  o : Fin n → Prop
  top : Prop
  part : Fin n → Fin n → Fin n → Prop
  part_tie : ∀ {t r s}, part t r s → d.tie s = some r
  full : ∀ {t r s}, d.tie r = some t → d.tie s = some r → part t r s
  tie_lt : ∀ {t s}, d.tie s = some t → d.bw s < d.bw t
  part_lt : ∀ {t r s}, d.owns t r = true → part t r s → d.bw s < d.bw t
  b : Finset (Fin n) → Fin n → Prop
def Z0 (M:Sig d) (X:Finset (Fin n)) (t:Fin n):=t∈X∨∃s∈d.cover,d.tie s=some t∧M.b X s
def O0 (M:Sig d) (X:Finset (Fin n)) (t:Fin n):=∃r,d.owns t r=true∧(r∈X∨∃s∈d.cover,M.part t r s∧M.b X s)
def Out (M:Sig d) (A X:Finset (Fin n)):=M.top∨(∃a∈A,a∈X)∨∃t∈d.cover,d.tie t=none∧M.b X t
def zR (K:SimpleGraph (Fin n)) (A:Finset (Fin n)) (p:Fin n) (X:Finset (Fin n)):=p∈X∨(∃a∈A,a∈X)∨∃u∈X,∃v∈X,K.Adj u v
structure Macro (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (p : Fin n) (M : Sig d) : Prop where
  prod : ∀ X t, t ∈ d.cover → (M.b X t ↔ (Z0 M X t ∨ M.z t) ∧ (O0 M X t ∨ M.o t))
  output : ∀ X, Out M A X ↔ zR K A p X
lemma wY (P:Fin n→Prop) (f:Fin n→ℕ) (h:∃t,P t):
  ∃t,P t∧∀s,P s→f s≤f t:=by
 classical
 let S:=Finset.univ.filter P
 have hs (v):v∈S↔P v:=by simp[S]
 obtain⟨t,ht⟩:=h;obtain⟨y,c,a⟩:=S.exists_max_image f ⟨t,(hs t).2 ht⟩;exact⟨y,(hs y).1 c,fun v b=>a v ((hs v).2 b)⟩
lemma wZ (P:Fin n→Prop) (f:Fin n→ℕ) (h:∃t,P t):
  ∃t,P t∧∀s,P s→f t≤f s:=by
 classical
 let S:=Finset.univ.filter P
 have hs (v):v∈S↔P v:=by simp[S]
 obtain⟨t,ht⟩:=h;obtain⟨y,c,a⟩:=S.exists_min_image f ⟨t,(hs t).2 ht⟩;exact⟨y,(hs y).1 c,fun v b=>a v ((hs v).2 b)⟩
lemma bA (j:IsMinCover K d.cover) (g:OwnerOK K d) {t}
  (ht:t∈d.cover):∃r,r∉d.cover∧d.owns t r=true:=by
 classical
 by_contra! h;have o:K.IsVertexCover ((d.cover.erase t:Finset (Fin n)):Set (Fin n)):=by
  intro a b f;have c (u v) (x:u=t) (e:K.Adj u v):v∈d.cover.erase t:=by
   subst u;refine Finset.mem_erase.mpr ⟨e.ne.symm,?_⟩;by_contra i;have w:=h v i;have q:d.owns v t≠true:=fun p=>i (g.1 v t p).2
   have k:=g.2 t v e
   cases e1:d.owns t v<;>cases e2:d.owns v t<;>simp_all
  rcases j.1 f with l|m
  ·by_cases e:a=t
   ·exact Or.inr (c _ _ e f)
   ·exact Or.inl (Finset.mem_erase.mpr ⟨e,l⟩)
  ·by_cases e:b=t
   ·exact Or.inl (c _ _ e f.symm)
   ·exact Or.inr (Finset.mem_erase.mpr ⟨e,m⟩)
 have hmin:=j.2 _ o;have s:=Finset.card_erase_lt_of_mem ht;omega
variable {M : Sig d}
lemma aB4 (g:OwnerOK K d) (tie:TieOK d) (m:Macro K A p M)
  {X t} (ht:t∈d.cover) (k:M.b X t) (l:Z0 M X t):Out M A X:=by
 obtain⟨v,⟨c,a,q⟩,n⟩:=wY
  (fun s=>s∈d.cover∧M.b X s∧Z0 M X s) d.bw ⟨t,ht,k,l⟩
 cases e:d.tie v with
 | none=>exact Or.inr (Or.inr ⟨v,c,e,a⟩)
 | some w=>
   have edge:=(tie v w e).2;have f:=(g.1 w v edge).2;have i:Z0 M X w:=Or.inr ⟨v,c,e,a⟩;have o:O0 M X w:=by
    refine⟨v,edge,?_⟩;obtain h|⟨s,hs,st,j⟩:=q
    ·exact Or.inl h
    ·exact Or.inr ⟨s,hs,M.full e st,j⟩
   have bw:=(m.prod X w f).2 ⟨Or.inl i,Or.inl o⟩;exact((not_lt_of_ge (n w ⟨f,bw,i⟩)) (M.tie_lt e)).elim
lemma uQ {u:Fin n} (c:u∉A) (hh:zR K A p {u}):u=p:=by
 obtain h|⟨a,b,hs⟩|⟨v,d,w,f,e⟩:=hh
 ·exact(Finset.mem_singleton.mp h).symm
 ·exact(c ((Finset.mem_singleton.mp hs)▸b)).elim
 ·rw[Finset.mem_singleton.mp d,Finset.mem_singleton.mp f] at e;exact(e.ne rfl).elim
lemma zS (a:Macro K A p M):¬M.top:=by intro h;have hh:=(a.output ∅).1 (Or.inl h);simp[zR] at hh
lemma wB (i:IsMinCover K d.cover) (c:OwnerOK K d) (tie:TieOK d)
  (iso:∀a∈A,∀r,¬K.Adj a r) (f:Macro K A p M)
  {u} (e:u∈d.cover) (mark:M.o u):u=p:=by
 obtain⟨r,_,hr⟩:=bA i c e;have g:Z0 M {u} u:=Or.inl (Finset.mem_singleton_self _);have b:=(f.prod {u} u e).2 ⟨Or.inl g,Or.inr mark⟩;exact uQ (fun h=>iso _ h _ (c.1 _ _ hr).1) ((f.output _).1 (aB4 c tie f e b g))
lemma uR (o:IsMinCover K d.cover) (g:OwnerOK K d) (tie:TieOK d)
  (iso:∀a∈A,∀r,¬K.Adj a r) (l:Macro K A p M)
  (y:p∈d.cover) {t} (ht:t∈d.cover):¬M.z t:=by
 classical
 intro mark
 let X:=Finset.univ.filter (fun i=>i∉d.cover∧i∉A)
 have x (i):i∈X↔i∉d.cover∧i∉A:=by simp[X]
 have c (u) (j:u∈d.cover):O0 M X u:=by obtain⟨r,hr,n⟩:=bA o g j;exact⟨r,n,Or.inl ((x _).2 ⟨hr,fun h=>iso r h _ (g.1 _ _ n).1.symm⟩)⟩
 have b:=(l.prod X t ht).2 ⟨Or.inr mark,Or.inl (c t ht)⟩;have out:Out M A X:=by
  obtain⟨s,⟨hs,m⟩,B⟩:=wY (fun v=>v∈d.cover∧M.b X v) d.bw ⟨t,ht,b⟩
  cases e:d.tie s with
  | none=>exact Or.inr (Or.inr ⟨s,hs,e,m⟩)
  | some v=>
    have f:=(g.1 _ _ (tie _ _ e).2).2;have C:Z0 M X v:=Or.inr ⟨s,hs,e,m⟩;have q:=(l.prod X v f).2 ⟨Or.inl C,Or.inl (c v f)⟩;exact((not_lt_of_ge (B v ⟨f,q⟩)) (M.tie_lt e)).elim
 obtain k|⟨a,w,k⟩|⟨u,j,v,f,e⟩:=(l.output X).1 out
 ·exact((x _).1 k).1 y
 ·exact((x _).1 k).2 w
 ·exact(o.1 e).elim ((x _).1 j).1 ((x _).1 f).1
lemma outside (mi:IsMinCover K d.cover) (c:OwnerOK K d) (tie:TieOK d)
  (iso:∀a∈A,∀r,¬K.Adj a r) (k:Macro K A p M) (B:p∉d.cover)
  (J:p∉A) (Q:K.CliqueFree 3)
  (C:∀t∈d.cover,∀s∈d.cover,M.z t→M.z s→t=s):
  ∃t∈d.cover,M.z t∧d.tie t=none∧(∀r,d.owns t r=true↔r=p):=by
 classical
 have g (v) (i:v∈d.cover):¬M.o v:=fun h=>B ((wB mi c tie iso k i h)▸i)
 have y:Out M A {p}:=(k.output _).2 (Or.inl (Finset.mem_singleton_self _));obtain X|⟨a,V,f⟩|⟨u,N,R,F⟩:=y
 ·exact(zS k X).elim
 ·exact(J ((Finset.mem_singleton.mp f)▸V)).elim
 obtain⟨t,⟨ht,T⟩,mn⟩:=wZ (fun s=>s∈d.cover∧M.b {p} s) d.bw ⟨u,N,F⟩;have first (s) (hs:s∈d.cover) (j:M.b {p} s):¬d.bw s<d.bw t:=not_lt_of_ge (mn s ⟨hs,j⟩)
 obtain⟨zt,ot⟩:=(k.prod _ _ ht).1 T;have E:M.z t:=by
  rcases zt with(f|⟨s,hs,st,j⟩)|mark
  ·exact(B ((Finset.mem_singleton.mp f)▸ht)).elim
  ·exact(first _ hs j (M.tie_lt st)).elim
  ·exact mark
 have q:d.owns t p=true:=by
  obtain⟨r,l,f|⟨s,hs,sp,j⟩⟩:=ot.resolve_right (g t ht)
  ·exact(Finset.mem_singleton.mp f)▸l
  ·exact(first _ hs j (M.part_lt l sp)).elim
 have x:d.tie t=none:=by
  cases tt:d.tie t with
  | none=>rfl
  | some w=>
    exfalso;have H:u≠t:=by rintro rfl;simp[tt] at R
    obtain⟨s,⟨hs,j,st⟩,O⟩:=wZ
     (fun s=>s∈d.cover∧M.b {p} s∧s≠t) d.bw ⟨u,N,F,H⟩
    have only(v) (i:v∈d.cover) (m:M.b {p} v) (hb:d.bw v<d.bw s):
      v=t:=by
     by_contra Z;have:=O v ⟨i,m,Z⟩;omega
    obtain⟨zs,os⟩:=(k.prod _ _ hs).1 j;have sw:s=w:=by
     rcases zs with(f|⟨v,i,n,m⟩)|mark
     ·exact(B ((Finset.mem_singleton.mp f)▸hs)).elim
     ·have U:=only _ i m (M.tie_lt n);rw[U,tt] at n;exact(Option.some.inj n).symm
     ·exact(st (C s hs t ht mark E)).elim
    subst w;obtain⟨r,l,f|⟨v,i,P,m⟩⟩:=os.resolve_right (g s hs)
    ·have G:d.owns s p=true:=(Finset.mem_singleton.mp f)▸l;have n:=(c.1 _ _ (tie t s tt).2).1.symm;exact Q {t,s,p} (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨n,(c.1 _ _ q).1,(c.1 _ _ G).1⟩)
    ·have vt:=only _ i m (M.part_lt l P);have tr:=M.part_tie P;rw[vt,tt] at tr;have sr:=Option.some.inj tr;exact(c.1 _ _ l).1.ne sr
 refine⟨t,ht,E,x,fun r=>⟨fun hr=> ?_,fun e=>e▸q⟩⟩;have S:M.b {r} t:=(k.prod _ _ ht).2 ⟨Or.inr E,Or.inl ⟨r,hr,Or.inl (Finset.mem_singleton_self _)⟩⟩;exact uQ (fun h=>iso r h t (c.1 t r hr).1.symm) ((k.output _).1 (Or.inr (Or.inr ⟨t,ht,x,S⟩)))
lemma qU (g:IsMinCover K d.cover) (b:OwnerOK K d) (tie:TieOK d)
  (iso:∀a∈A,∀r,¬K.Adj a r) (e:Macro K A p M)
  (i:p∉A) (j:K.CliqueFree 3)
  (f:∀t∈d.cover,∀s∈d.cover,M.z t→M.z s→t=s):
  ¬M.top∧
  ((p∈d.cover∧(∀t∈d.cover,¬M.z t)∧(∀t∈d.cover,M.o t→t=p))∨
   (p∉d.cover∧(∀t∈d.cover,¬M.o t)∧
    ∃
     t∈d.cover,M.z t∧(∀s∈d.cover,M.z s→s=t)∧d.tie t=none∧
     ∀r,d.owns t r=true↔r=p)):=by
 classical
 refine⟨zS e,?_⟩;by_cases c:p∈d.cover
 ·exact Or.inl ⟨c,fun _ ht=>uR g b tie iso e c ht,fun _ ht=>wB g b tie iso e ht⟩
 ·obtain⟨t,ht,l,k,N⟩:=outside g b tie iso e c i j f;exact Or.inr ⟨c,fun s hs h=>c ((wB g b tie iso e hs h)▸hs),t,ht,l,fun s hs h=>f s hs t ht h l,k,N⟩
end PEqualNP.MetaComplexity.NestedCover.Ar
namespace PEqualNP.MetaComplexity.NestedCover.Ae
open PEqualNP.CircuitLowerBounds Ac Af Ar
variable {n : ℕ} {D P : Circuit} {g w : ℕ ↪ ℕ} {src fresh : ℕ}
def Sel (P:Circuit) (g:ℕ ↪ ℕ) (src fresh j i:ℕ):Prop:=i=src∧fresh∈(gateAt P (g j)).inputs
def qB (n:ℕ) (D:Circuit) (v:ℕ):=∃j<D.gates.length,v=n+j∧(gateAt D j).op=GateOp.or
inductive Flow (n : ℕ) (D : Circuit) (sel : ℕ → ℕ → Prop) (leaf : ℕ → Prop) : ℕ → Prop
  | iT {v} : ¬qB n D v → leaf v → Flow n D sel leaf v
  | step {j i} : j < D.gates.length → (gateAt D j).op = GateOp.or →
      i ∈ (gateAt D j).inputs → Flow n D sel leaf i → Flow n D sel leaf (n+j)
  | hit {j i} : j < D.gates.length → (gateAt D j).op = GateOp.or →
      i ∈ (gateAt D j).inputs → sel j i → Flow n D sel leaf (n+j)
variable {pick : ℕ → ℕ → Prop} {L : ℕ → Prop}
lemma jR {v} (a:¬qB n D v):Flow n D pick L v↔L v:=by
 constructor
 ·rintro(⟨_,hv⟩| @⟨j,i,hj,op,_,_⟩| @⟨j,i,hj,op,_,_⟩)
  ·exact hv
  ·exact(a ⟨j,hj,rfl,op⟩).elim
  ·exact(a ⟨j,hj,rfl,op⟩).elim
 ·exact .iT a
lemma sV {j} (c:j<D.gates.length) (op:(gateAt D j).op=GateOp.or):
  Flow n D pick L (n+j)↔∃i∈(gateAt D j).inputs,Flow n D pick L i∨pick j i:=by
 constructor
 ·intro hh
  generalize a:n+j=v at hh
  cases hh with
  | iT hn _=>exact(hn ⟨_,c,a.symm,op⟩).elim
  | @step k i _ _ b hh=>
    have:=Nat.add_left_cancel a;subst k;exact⟨i,b,Or.inl hh⟩
  | @hit k i _ _ b hh=>
    obtain rfl:=Nat.add_left_cancel a;exact⟨i,b,Or.inr hh⟩
 ·rintro⟨i,b,a|a⟩
  ·exact .step c op b a
  ·exact .hit c op b a
abbrev sW (n:ℕ) (D P:Circuit) (g:ℕ ↪ ℕ) (src fresh:ℕ):=Flow n D (Sel P g src fresh) (fun _=>False)
abbrev fT (n:ℕ) (D P:Circuit) (w:ℕ ↪ ℕ) (x:Fin n→Bool):=Flow n D (fun _ _=>False) (fun i=>W P x (w i))
lemma qC {x:Fin n→Bool} {j} (a:j<D.gates.length)
  (op:(gateAt D j).op=GateOp.or):
  fT n D P w x (n+j)↔∃i∈(gateAt D j).inputs,fT n D P w x i:=by
 simp[fT,sV a op]
lemma qD (v:Fin n):¬qB n D v.val:=by rintro⟨j,_,a,_⟩;have:=v.isLt;omega
lemma rQ {d:NCCData n} {t:Fin n} (T:TermOK n D d t):¬qB n D (d.bw t):=by obtain⟨j,_,e,_,op,_⟩:=T;rintro⟨k,_,a,b⟩;obtain rfl:=Nat.add_left_cancel (e.symm.trans a);simp_all
variable (S : Splice n D P g w src fresh)
include S
lemma pos {j s i a:ℕ} {x:Fin n→Bool} {I:Prop}
  (t:(gateAt D j).inputs.Nodup)
  (d:(gateAt D j).inputs[s]?=some i) (p:(gateAt P (g j)).inputs[s]?=some a)
  (c:W P x fresh↔W P x (w src)∨I):
  W P x a↔W P x (w i)∨I∧Sel P g src fresh j i:=by
 rcases (S.pin j s i).1 d with e|⟨e,m⟩
 ·have r:=Option.some.inj (p.symm.trans e);rw[r];apply(or_iff_left _).symm;rintro⟨_,m,o⟩;subst i;obtain⟨k,l⟩:=List.mem_iff_getElem?.1 o;have q:=(S.pin j k src).2 (Or.inr ⟨l,rfl⟩);obtain⟨_,f⟩:=List.getElem?_eq_some_iff.1 d;obtain⟨_,h⟩:=List.getElem?_eq_some_iff.1 q;obtain rfl:=t.getElem_inj_iff.1 (f.trans h.symm);exact S.hole _ (Option.some.inj (e.symm.trans l))
 ·rw[Option.some.inj (p.symm.trans e),m];have b:Sel P g src fresh j src:=⟨rfl,List.mem_of_getElem? e⟩
  simpa[b] using c
def
    gA (P : Circuit) (w g : ℕ ↪ ℕ) (src fresh : ℕ) (x : Fin n → Bool) (I : Prop)
    (j i : ℕ) := W P x (w i) ∨ I ∧ Sel P g src fresh j i
lemma jS {j} {x:Fin n→Bool} {I:Prop}
  (o:(gateAt D j).inputs.Nodup) (d:W P x fresh↔W P x (w src)∨I):
  ((∃a∈(gateAt P (g j)).inputs,W P x a)↔
    ∃i∈(gateAt D j).inputs,gA P w g src fresh x I j i)∧
  ((∀a∈(gateAt P (g j)).inputs,W P x a)↔
    ∀i∈(gateAt D j).inputs,gA P w g src fresh x I j i):=by
 have e (i) (c:i∈(gateAt D j).inputs):
   ∃a∈(gateAt P (g j)).inputs,W P x a↔gA P w g src fresh x I j i:=by
  obtain⟨s,k⟩:=List.mem_iff_getElem?.1 c;have m:s<(gateAt P (g j)).inputs.length:=S.total j▸(List.getElem?_eq_some_iff.1 k).1;exact⟨_,List.getElem_mem m,pos S o k (List.getElem?_eq_getElem m) d⟩
 have f (a) (b:a∈(gateAt P (g j)).inputs):
   ∃i∈(gateAt D j).inputs,W P x a↔gA P w g src fresh x I j i:=by
  obtain⟨s,p⟩:=List.mem_iff_getElem?.1 b;have l:s<(gateAt D j).inputs.length:=(S.total j).symm▸(List.getElem?_eq_some_iff.1 p).1;exact⟨_,List.getElem_mem l,pos S o (List.getElem?_eq_getElem l) p d⟩
 constructor<;>constructor
 ·rintro⟨a,b,q⟩;obtain⟨i,c,h⟩:=f a b;exact⟨i,c,h.1 q⟩
 ·rintro⟨i,c,r⟩;obtain⟨a,b,h⟩:=e i c;exact⟨a,b,h.2 r⟩
 ·intro all i c;obtain⟨a,b,h⟩:=e i c;exact h.1 (all a b)
 ·intro all a b;obtain⟨i,c,h⟩:=f a b;exact h.2 (all i c)
structure bB (n : ℕ) (D P : Circuit) (g w : ℕ ↪ ℕ) : Prop where
  back : ReadsBack n P
  validGate : ∀ j < D.gates.length, g j < P.gates.length
  input : ∀ v : Fin n, w v.val = v.val
variable (F : bB n D P g w)
omit S
lemma jT {K A d t} (h:Valid n K A D d) (ht:t∈d.cover):
  d.zroot t≠d.oroot t:=by
 intro a;have z:=(iC h (x:=single t) ht).2 (Or.inl (by simp[single]));rw[a,fR h ht] at z;obtain⟨r,edge,b⟩:=z;exact(h.2.2.1.1 _ _ edge).1.ne ((iD h edge t).1 b).symm
lemma aBv {K A d j} (h:Valid n K A D d) (f:j<D.gates.length)
  (op:(gateAt D j).op=GateOp.or):(gateAt D j).inputs.Nodup:=by
 have c {G L ρ} (tr:IsOrTree n D G L ρ) (f:j∈G):(gateAt D j).inputs.Nodup:=by obtain⟨a,b,e,m⟩:=jP tr f;simp[e,m]
 rcases h.2.2.2.2.1 j f with top|⟨t,ht,e,i⟩
 ·exact c h.2.2.2.2.2.2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f,top⟩)
 ·cases g:(d.role j).1 with
  | b=>
    obtain⟨k,_,l,_,p,_⟩:=dN h ht;obtain rfl:=Nat.add_left_cancel (l.symm.trans (i g));simp_all
  | z=>exact c (bL h ht) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f,Prod.ext g e⟩)
  | o=>exact c (cT h ht) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f,Prod.ext g e⟩)
  | top=>exact c h.2.2.2.2.2.2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f,g⟩)
variable {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {d : NCCData n}
variable (h : Valid n K A D d) {x : Fin n → Bool} {I : Prop}
include S F h
lemma uS (b:W P x fresh↔W P x (w src)∨I) (v:ℕ):
  W P x (w v)↔fT n D P w x v∨I∧sW n D P g src fresh v:=by
 induction v using Nat.strong_induction_on with
 | ind v ih=>
   by_cases c:qB n D v
   ·obtain⟨j,a,rfl,op⟩:=c;rw[S.align j,aY F.back (F.validGate _ a) ((S.op _).trans op),
     (jS S (aBv h a op) b).1,qC a op,
     show sW n D P g src fresh (n+j)↔_ from sV a op]
    have d (i) (hi:i∈(gateAt D j).inputs):=ih i (h.1 _ a _ hi);unfold gA;grind
   ·simp[fT,sW,jR c]
lemma uT (a:W P x fresh↔W P x (w src)∨I) (j i:ℕ):
  gA P w g src fresh x I j i↔fT n D P w x i∨I∧(sW n D P g src fresh i∨Sel P g src fresh j i):=by
 rw[gA,uS S F h a];tauto
lemma xW (c:W P x fresh↔W P x (w src)∨I) {t} (ht:t∈d.cover):
  W
   P x (w (d.bw t))↔(gA P w g src fresh x I (d.bw t-n) (d.zroot t)∧
   gA P w g src fresh x I (d.bw t-n) (d.oroot t)):=by
 obtain⟨j,i,f,_,op,b⟩:=dN h ht;have k:(gateAt D j).inputs.Nodup:=by rcases b with e|e<;>simp[e,jT h ht,Ne.symm (jT h ht)]
 have l:W P x (n+g j)↔∀a∈(gateAt P (g j)).inputs,W P x a:=by simp only[W,aO F.back (F.validGate j i),S.op j,op,GateOp.eval,List.all_map,Function.comp_def,id_eq,List.all_eq_true]
 rw[f,S.align,l,(jS S k c).2,Nat.add_sub_cancel_left];rcases b with e|e<;>simp[e,and_comm]
end PEqualNP.MetaComplexity.NestedCover.Ae
namespace PEqualNP.MetaComplexity.NestedCover.Ae
open PEqualNP.CircuitLowerBounds Ac Af Ar
variable {n : ℕ} {D P : Circuit} {g w : ℕ ↪ ℕ} {src fresh : ℕ}
variable {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {d : NCCData n}
lemma fU {G L:Finset ℕ} {a ρ} (tr:IsOrTree n D G L ρ)
  (rb:ReadsBack n D) (bd:∀j∈G,j<D.gates.length) (d:a∈L):
  Below n D G a ρ:=by
 apply(fI tr rb bd (Below n D G a) _).2 ⟨a,d,.refl⟩;intro j f;constructor
 ·intro b
  generalize e:n+j=i at b
  cases b with
  | refl=>exact((tr.2.1 a d).1 ⟨by omega,by simpa[←e] using f⟩).elim
  | @step i k bi hk c=>
    obtain rfl:=Nat.add_left_cancel e;exact⟨i,c,bi⟩
 ·rintro⟨i,c,b⟩;exact b.step f c
def aB5 (D:Circuit) (d:NCCData n) (t r s:Fin n):=d.tie s=some r∧Below n D (Z r d D) (d.bw s) (d.lam t r)
variable (h : Valid n K A D d)
def
    iF (h : Valid n K A D d) (P : Circuit) (g w : ℕ ↪ ℕ) (src fresh : ℕ)
    (α : Finset (Fin n) → Fin n → Bool) : Sig d where
  z t := sW n D P g src fresh (d.zroot t) ∨ Sel P g src fresh (d.bw t-n) (d.zroot t)
  o t := sW n D P g src fresh (d.oroot t) ∨ Sel P g src fresh (d.bw t-n) (d.oroot t)
  top := sW n D P g src fresh D.output ∨ P.output = fresh
  part := aB5 D d
  part_tie hh := hh.1
  full {t r s} rt sr := by
    obtain ⟨hr,edge⟩ := h.2.2.2.1 _ _ rt
    have hl := lam h edge
    simp only [LamOK,hr,↓reduceIte] at hl
    refine ⟨sr,?_⟩
    rw [hl.2.2 rt]
    exact fU (bL h hr) h.1 aT (dF.mpr (.inr ⟨s,(h.2.2.2.1 _ _ sr).1,sr,rfl⟩))
  tie_lt {t s} st := by
    obtain ⟨hs,edge⟩ := h.2.2.2.1 _ _ st
    have ht := (h.2.2.1.1 _ _ edge).2
    exact (lM (bL h ht) h.1 aT _ (dF.mpr (.inr ⟨s,hs,st,rfl⟩))).trans_lt
      (kC h ht).1
  part_lt {t r s} edge hh := by
    have ht := (h.2.2.1.1 _ _ edge).2
    exact ((hh.2.le h.1 aT).trans (lM (cT h ht) h.1 aT _
      (iZ.mpr ⟨r,edge,rfl⟩))).trans_lt (kC h ht).2
  b X t := W P (α X) (w (d.bw t))
variable (F : bB n D P g w) {x : Fin n → Bool}
include F in
lemma cO (i:Fin n):fT n D P w x i.val↔x i=true:=by rw[fT,jR (qD i),F.input,aC]
include h
lemma dX {s} (hs:s∈d.cover):fT n D P w x (d.bw s)↔W P x (w (d.bw s)):=jR (rQ (dN h hs))
lemma lV {G L:Finset ℕ} {ρ} (tr:IsOrTree n D G L ρ)
  (bd:∀j∈G,j<D.gates.length):
  fT n D P w x ρ↔∃i∈L,fT n D P w x i:=
 fI tr h.1 bd _ (fun j a=>qC (bd j a) (tr.1 _ a).1)
include F
lemma aBa {t} (ht:t∈d.cover):
  fT n D P w x (d.zroot t)↔x t=true∨∃s∈d.cover,d.tie s=some t∧W P x (w (d.bw s)):=by
 rw[lV h (bL h ht) aT];constructor
 ·rintro⟨i,b,a⟩;rcases dF.mp b with rfl|⟨s,hs,τ,rfl⟩
  ·exact .inl ((cO F _).1 a)
  ·exact .inr ⟨s,hs,τ,(dX h hs).1 a⟩
 ·rintro(xt|⟨s,hs,τ,bs⟩)
  ·exact⟨_,dF.mpr (.inl rfl),(cO F _).2 xt⟩
  ·exact⟨_,dF.mpr (.inr ⟨s,hs,τ,rfl⟩),(dX h hs).2 bs⟩
lemma rR {t r} (e:d.owns t r=true):
  fT n D P w x (d.lam t r)↔x r=true∨∃s∈d.cover,aB5 D d t r s∧W P x (w (d.bw s)):=by
 have hl:=lam h e;by_cases hr:r∈d.cover
 ·simp only[LamOK,hr,↓reduceIte] at hl;have node:dP r d D (d.lam t r):=by
   rcases hl.2.1 with b|⟨j,a,b,role⟩
   ·exact Or.inl (dF.mpr (.inl b))
   ·exact Or.inr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a,role⟩,b⟩
  have g:=(jK h hr node).1 hl.1;rw[gS (bL h hr) h.1 aT _ (fun j a=>qC (aT j a) ((bL h hr).1 _ a).1) node];constructor
  ·rintro⟨i,k,f,c⟩;rcases dF.mp k with rfl|⟨s,hs,τ,rfl⟩
   ·exact .inl ((cO F _).1 c)
   ·exact .inr ⟨s,hs,⟨τ,f⟩,(dX h hs).1 c⟩
  ·rintro(xr|⟨s,hs,⟨τ,bb⟩,bs⟩)
   ·exact⟨_,dF.mpr (.inl rfl),g,(cO F _).2 xr⟩
   ·exact⟨_,dF.mpr (.inr ⟨s,hs,τ,rfl⟩),bb,(dX h hs).2 bs⟩
 ·simp only[LamOK,hr,↓reduceIte] at hl;rw[hl,cO F];apply(or_iff_left _).symm;rintro⟨s,_,hh,_⟩;exact hr (h.2.2.1.1 _ _ (h.2.2.2.1 _ _ hh.1).2).2
lemma aBb {t} (ht:t∈d.cover):
  fT n D P w x (d.oroot t)↔∃r,d.owns t r=true∧(x r=true∨∃s∈d.cover,aB5 D d t r s∧W P x (w (d.bw s))):=by
 rw[lV h (cT h ht) aT];constructor
 ·rintro⟨i,c,a⟩;obtain⟨r,e,rfl⟩:=iZ.mp c;exact⟨r,e,(rR h F e).1 a⟩
 ·rintro⟨r,e,b⟩;exact⟨_,iZ.mpr ⟨r,e,rfl⟩,(rR h F e).2 b⟩
lemma xX:
  fT n D P w x D.output↔(∃a∈A,x a=true)∨∃t∈d.cover,d.tie t=none∧W P x (w (d.bw t)):=by
 rw[lV h h.2.2.2.2.2.2 (fun _ g=>Finset.mem_range.mp (Finset.mem_filter.mp g).1)];have b {i}:i∈topLeaves d A↔(∃a∈A,a.val=i)∨∃s∈d.cover,d.tie s=none∧d.bw s=i:=by simp[topLeaves,and_assoc]
 constructor
 ·rintro⟨i,f,e⟩;rcases b.mp f with⟨a,c,rfl⟩|⟨s,hs,τ,rfl⟩
  ·exact .inl ⟨a,c,(cO F _).1 e⟩
  ·exact .inr ⟨s,hs,τ,(dX h hs).1 e⟩
 ·rintro(⟨a,c,xa⟩|⟨s,hs,τ,bs⟩)
  ·exact⟨_,b.mpr (.inl ⟨a,c,rfl⟩),(cO F _).2 xa⟩
  ·exact⟨_,b.mpr (.inr ⟨s,hs,τ,rfl⟩),(dX h hs).2 bs⟩
variable (S : Splice n D P g w src fresh)
variable {α : Finset (Fin n) → Fin n → Bool} {X : Finset (Fin n)} {I : Prop}
structure Slice (d : NCCData n) (A X : Finset (Fin n)) (x : Fin n → Bool) : Prop where
  centre : ∀ t ∈ d.cover, x t = true ↔ t ∈ X
  owner : ∀ t r, d.owns t r = true → (x r = true ↔ r ∈ X)
  extra : ∀ a ∈ A, x a = true ↔ a ∈ X
include S F in
lemma prod (c:Slice d A X (α X)) (a:W P (α X) fresh↔W P (α X) (w src)∨I)
  {t} (ht:t∈d.cover):
  (iF h P g w src fresh α).b X t↔(Z0 (iF h P g w src fresh α) X t∨I∧(iF h P g w src fresh α).z t)∧(O0 (iF h P g w src fresh α) X t∨I∧(iF h P g w src fresh α).o t):=by
 change W P (α X) (w (d.bw t))↔_;rw[xW S F h a ht,uT S F h a,uT S F h a,aBa h F ht,aBb h F ht];simp only[iF,Z0,O0,c.centre t ht];have e (r) (hr:d.owns t r=true):=c.owner t r hr;grind
include S F in
lemma output (j:Slice d A X (α X)) (c:W P (α X) fresh↔W P (α X) (w src)∨I):
  W
   P (α X) P.output↔(I∧(iF h P g w src fresh α).top)∨(∃a∈A,a∈X)∨
   ∃t∈d.cover,d.tie t=none∧(iF h P g w src fresh α).b X t:=by
 have iT:W P (α X) P.output↔W P (α X) (w D.output)∨I∧P.output=fresh:=by
  rcases (S.output D.output).1 rfl with e|⟨e,f⟩
  ·simp[e,S.hole]
  ·simpa[e,f] using c
 rw[iT,uS S F h c,xX h F];have k (a) (i:a∈A):=j.extra a i;simp only[iF];grind
include S F in
lemma xY {p:Fin n} (e:∀X,Slice d A X (α X))
  (a:∀X,W P (α X) fresh)
  (b:∀X,W P (α X) P.output↔zR K A p X):Macro K A p (iF h P g w src fresh α) where
 prod X t ht:=by
  have c:W P (α X) fresh↔W P (α X) (w src)∨True:=by simp[a X]
  simpa using prod h F S (e X) c ht
 output X:=by
  have c:W P (α X) fresh↔W P (α X) (w src)∨True:=by simp[a X]
  exact(show W P (α X) P.output↔Out (iF h P g w src fresh α) A X by simpa[Out] using output h F S (e X) c).symm.trans
   (b X)
end PEqualNP.MetaComplexity.NestedCover.Ae
namespace PEqualNP.MetaComplexity.NestedCover.Ae
open PEqualNP.CircuitLowerBounds Ac Af Ar
variable {n : ℕ} {D P : Circuit} {g w : ℕ ↪ ℕ} {src fresh : ℕ}
variable {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)} {d : NCCData n}
variable {p l : Fin n} {j : ℕ}
def bJ (l:Fin n) (X:Finset (Fin n)) (v:Fin n):=decide (v=l∨v∈X)
lemma qE (h:Valid n K A D d) (c:∀v,¬K.Adj l v) (g:l∉A) (X):
  Slice d A X (bJ l X) where
 centre t ht:=by
  obtain⟨r,_,e⟩:=bA h.2.1 h.2.2.1 ht;have f:t≠l:=fun b=>c r (b▸(h.2.2.1.1 _ _ e).1)
  simp[bJ,f]
 owner t r e:=by
  have f:r≠l:=fun b=>c t (b▸(h.2.2.1.1 _ _ e).1.symm)
  simp[bJ,f]
 extra a ha:=by
  have f:a≠l:=fun b=>g (b▸ha)
  simp[bJ,f]
lemma oD [DecidableRel K'.Adj] (c:∀v,¬K.Adj l v) (g:l∉A)
  (ext:∀u v,K'.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p))
  (d:circuitFun n P=graphFun K' A) (X):
  W P (bJ l X) P.output↔zR K A p X:=by
 rw[←cL,d];simp only[graphFun,Bool.or_eq_true,decide_eq_true_eq,bJ,zR];have f:K'.Adj p l:=(ext _ _).2 (.inr (.inl ⟨rfl,rfl⟩));have ne:=f.ne;constructor
 ·rintro(⟨a,ha,ax⟩|⟨u,v,uv,xu,xv⟩)
  ·exact .inr (.inl ⟨a,ha,ax.resolve_left (fun b=>g (b▸ha))⟩)
  ·rcases (ext _ _).1 uv with e|⟨rfl,rfl⟩|⟨rfl,rfl⟩
   ·exact .inr (.inr ⟨u,xu.resolve_left (fun b=>c v (b▸e)),v,xv.resolve_left (fun b=>c u (b▸e.symm)),e⟩)
   ·exact .inl (xu.resolve_left ne)
   ·exact .inl (xv.resolve_left ne)
 ·rintro(px|⟨a,ha,ax⟩|⟨u,xu,v,xv,e⟩)
  ·exact .inr ⟨p,l,f,.inr px,.inl rfl⟩
  ·exact .inl ⟨a,ha,.inr ax⟩
  ·exact .inr ⟨u,v,(ext _ _).2 (.inl e),.inr xu,.inr xv⟩
lemma xA {x:Fin n→Bool} {i a:ℕ}
  (rb:ReadsBack n P) (b:j<P.gates.length) (op:(gateAt P j).op=GateOp.or)
  (bS:(gateAt P j).inputs=[a,i]∨(gateAt P j).inputs=[i,a]):
  W P x (n+j)↔W P x a∨W P x i:=by
 rw[aY rb b op];rcases bS with e|e<;>simp[e,or_comm]
lemma xZ [DecidableRel K'.Adj] (h:Valid n K A D d)
  (F:bB n D P g w) (S:Splice n D P g w src (n+j))
  (e:j<P.gates.length) (op:(gateAt P j).op=GateOp.or)
  (bS:(gateAt P j).inputs=[w src,l.val]∨(gateAt P j).inputs=[l.val,w src])
  (a:∀v,¬K.Adj l v) (c:l∉A)
  (ext:∀u v,K'.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p))
  (b:circuitFun n P=graphFun K' A):
  Macro K A p (iF h P g w src (n+j) (bJ l)):=by
 apply xY h F S (qE h a c) _ (oD a c ext b);intro X;exact(xA F.back e op bS).2 (.inr ((aC l).2 (by simp[bJ])))
end PEqualNP.MetaComplexity.NestedCover.Ae
namespace PEqualNP.MetaComplexity.NestedCover.Ad
open PEqualNP.CircuitLowerBounds Af
variable {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    {d : NCCData n} {t u r : Fin n} {w j k : ℕ}
def tP (d:NCCData n) (w:ℕ):ℕ⊕(Kind×ℕ):=if w<n then .inl w else .inr (d.role (w-n))
lemma oW (r:Fin n):tP d r.val= .inl r.val:=by simp[tP,r.isLt]
lemma gU (j:ℕ):tP d (n+j)= .inr (d.role j):=by simp[tP]
variable (h : Valid n K A C d)
include h
lemma zT (ht:t∈d.cover):tP d (d.bw t)= .inr (.b,t.val):=by obtain⟨j,_,e,hr,_⟩:=dN h ht;rw[e,gU,hr]
lemma xB (c:dP t d C w):
  tP d w= .inl t.val∨tP d w= .inr (.z,t.val)∨
  ∃s,d.tie s=some t∧tP d w= .inr (.b,s.val):=by
 rcases c with hl|⟨j,a,rfl⟩
 ·rcases dF.mp hl with rfl|⟨s,hs,τ,rfl⟩
  ·exact Or.inl (oW _)
  ·exact Or.inr (Or.inr ⟨s,τ,zT h hs⟩)
 ·exact Or.inr (Or.inl ((gU j).trans (congrArg Sum.inr (Finset.mem_filter.mp a).2)))
lemma qV (ht:dP t d C w) (a:dP u d C w):t=u:=by have T:=xB h ht;have U:=xB h a;grind
lemma xC (e:d.owns u r=true):
  tP d (d.lam u r)= .inl r.val∨tP d (d.lam u r)= .inr (.z,r.val):=by
 have hl:=lam h e;unfold LamOK at hl
 split at hl
 ·rcases hl.2.1 with hr|⟨j,_,hr,a⟩
  ·rw[hr];exact Or.inl (oW _)
  ·rw[hr,gU,a];exact Or.inr rfl
 ·rw[hl];exact Or.inl (oW _)
lemma mQ (ht:t∈d.cover) (f:dP t d C w) (c:uO u d C w):
  d.owns u t=true∧d.lam u t=w∧IsCentred n C d w:=by
 have T:=xB h f;rcases c with hl|⟨j,b,rfl⟩
 ·obtain⟨r,e,a⟩:=iZ.mp hl;have R:=xC h e;have rt:r=t:=by grind
  subst r;have H:=lam h e;simp[LamOK,ht] at H;exact⟨e,a,a▸H.1⟩
 ·have g:=(gU (d:=d) j).trans (congrArg Sum.inr (Finset.mem_filter.mp b).2);grind
lemma zU (ht:t∈d.cover) (b:dP t d C w):¬uO t d C w:=by intro a;exact(h.2.2.1.1 _ _ (mQ h ht b a).1).1.ne rfl
abbrev bK (d:NCCData n) (C:Circuit) (A:Finset (Fin n)):=fQ n (topGates d C) (topLeaves d A)
lemma xD (f:bK d C A w):
  (∃a∈A,tP d w= .inl a.val)∨(∃i,tP d w= .inr (.top,i))∨
    ∃s∈d.cover,d.tie s=none∧tP d w= .inr (.b,s.val):=by
 rcases f with hl|⟨j,e,rfl⟩
 ·rcases Finset.mem_union.mp hl with hl|hl
  ·obtain⟨a,c,rfl⟩:=Finset.mem_image.mp hl;exact Or.inl ⟨a,c,oW _⟩
  ·obtain⟨s,hs,rfl⟩:=Finset.mem_image.mp hl;obtain⟨hs,τ⟩:=Finset.mem_filter.mp hs;exact Or.inr (Or.inr ⟨s,hs,τ,zT h hs⟩)
 ·refine Or.inr (Or.inl ⟨(d.role j).2,?_⟩);rw[gU];exact congrArg Sum.inr (Prod.ext (Finset.mem_filter.mp e).2 rfl)
variable (iso : ∀ a ∈ A, ∀ r, ¬ K.Adj a r)
include iso
lemma lW (b:bK d C A w) (ht:t∈d.cover):¬dP t d C w:=by
 intro c;obtain⟨r,_,e⟩:=Ar.bA h.2.1 h.2.2.1 ht;have f:t∉A:=fun a=>iso t a r (h.2.2.1.1 t r e).1
 have T:=xD h b;have Z':=xB h c;grind
lemma qF (b:bK d C A w):¬uO t d C w:=by
 have T:=xD h b;rintro(hl|⟨j,hj,rfl⟩)
 ·obtain⟨r,e,c⟩:=iZ.mp hl;have L:=xC h e;have f:r∉A:=fun a=>iso r a t (h.2.2.1.1 t r e).1.symm
  grind
 ·have g:=(gU (d:=d) j).trans (congrArg Sum.inr (Finset.mem_filter.mp hj).2);grind
omit iso h
def gA (C:Circuit) (G:Finset ℕ) (ρ:ℕ) (sink:Option ℕ) (w:ℕ) (c:Option ℕ):=(∃j∈G,c=some j∧w∈(gateAt C j).inputs)∨(c=sink∧w=ρ)
lemma cG {G L ρ sink c} (tr:IsOrTree n C G L ρ) (P:gA C G ρ sink w c):
  fQ n G L w:=by
 rcases P with⟨j,b,_,a⟩|⟨_,rfl⟩
 ·exact bZ tr b a
 ·exact cC tr
lemma oE {G L ρ sink c₁ c₂} (tr:IsOrTree n C G L ρ)
  (P:gA C G ρ sink w c₁) (Q:gA C G ρ sink w c₂):c₁=c₂:=by
 have g {j} (a:j∈G) (hr:ρ∈(gateAt C j).inputs):False:=by have z:=iE tr (cC tr);simp at z;have le:(gateAt C j).inputs.count ρ≤ readsIn C G ρ:=Finset.single_le_sum (f:=fun j=>(gateAt C j).inputs.count ρ) (fun _ _=>Nat.zero_le _) a;have:=List.count_pos_iff.mpr hr;omega
 rcases P with⟨j,a,rfl,b⟩|⟨rfl,rfl⟩<;>rcases Q with⟨k,c,rfl,d⟩|⟨e,h⟩
 ·exact congrArg some (kY tr a c b d)
 ·exact(g a (h▸b)).elim
 ·exact(g c d).elim
 ·exact e.symm
abbrev zV (d:NCCData n) (C:Circuit) (t:Fin n):=gA C (Z t d C) (d.zroot t) (some (d.bw t-n))
abbrev zW (d:NCCData n) (C:Circuit) (t:Fin n):=gA C (O t d C) (d.oroot t) (some (d.bw t-n))
abbrev xE (d:NCCData n) (C:Circuit):=gA C (topGates d C) C.output none
def bB (C:Circuit) (w:ℕ):Option ℕ→Prop
 | none=>w=C.output
 | some j=>j<C.gates.length∧w∈(gateAt C j).inputs
include h in
lemma lX {c} (P:bB C w c):
  xE d C w c∨∃t∈d.cover,zV d C t w c∨zW d C t w c:=by
 cases c with
 | none=>exact Or.inl (Or.inr ⟨rfl,P⟩)
 | some j=>
   obtain⟨f,g⟩:=P;obtain ht|⟨t,ht,a,l⟩:=h.2.2.2.2.1 j f
   ·exact Or.inl (Or.inl ⟨j,by simp[topGates,f,ht],rfl,g⟩)
   cases hr:(d.role j).1 with
   | top=>exact Or.inl (Or.inl ⟨j,by simp[topGates,f,hr],rfl,g⟩)
   | z=>exact Or.inr ⟨t,ht,Or.inl (Or.inl ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f,Prod.ext hr a⟩,rfl,g⟩)⟩
   | o=>exact Or.inr ⟨t,ht,Or.inr (Or.inl ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f,Prod.ext hr a⟩,rfl,g⟩)⟩
   | b=>
     have r:=l hr;obtain⟨k,_,e,_,_,i⟩:=dN h ht;obtain rfl:k=j:=by omega
     have s:w=d.zroot t∨w=d.oroot t:=by rcases i with i|i<;>simp_all[or_comm]
     have m:some k=some (d.bw t-n):=by rw[r];simp
     exact Or.inr ⟨t,ht,s.elim (fun q=>Or.inl (Or.inr ⟨m,q⟩)) (fun p=>Or.inr (Or.inr ⟨m,p⟩))⟩
structure Trace (n : ℕ) (C : Circuit) (d : NCCData n) (W : ℕ) where
  sel : ℕ → ℕ → Prop
  selTop : Prop
  mark : ℕ → Prop
  source : ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, sel j i → i = W
  sourceTop : selTop → C.output = W
  raw : ∀ r : Fin n, ¬ mark r.val
  and_ : ∀ t ∈ d.cover, ¬ mark (d.bw t)
  or_ : ∀ j < C.gates.length, (gateAt C j).op = .or →
    (mark (n+j) ↔ ∃ i ∈ (gateAt C j).inputs, mark i ∨ sel j i)
variable {W : ℕ} (S : Trace n C d W)
def gH:Option ℕ→ℕ→Prop
 | none,_=>S.selTop
 | some j,i=>S.sel j i
def mR (ρ:ℕ) (sink:Option ℕ):=S.mark ρ∨gH S sink ρ
abbrev eL (t:Fin n):=mR S (d.zroot t) (some (d.bw t-n))
abbrev jU (t:Fin n):=mR S (d.oroot t) (some (d.bw t-n))
abbrev eG:=mR S C.output none
lemma wC {c i} (a:bB C i c) (sel:gH S c i):i=W:=by
 cases c with
 | some j=>exact S.source j a.1 i a.2 sel
 | none=>exact a.trans (S.sourceTop sel)
variable {G L : Finset ℕ} {ρ : ℕ} {sink c : Option ℕ}
lemma kD:∀j∈topGates d C,j<C.gates.length:=fun _ a=>Finset.mem_range.mp (Finset.mem_filter.mp a).1
lemma zX (tr:IsOrTree n C G L ρ) (rb:ReadsBack n C)
  (bd:∀j∈G,j<C.gates.length) (e:fQ n G L w) (g:S.mark w):S.mark ρ:=by
 classical
 let U:=(L∪G.image (n+·)).filter S.mark
 have u (v):v∈U↔fQ n G L v∧S.mark v:=by simp[U,fQ,eq_comm]
 let v:=U.max' ⟨w,(u w).2 ⟨e,g⟩⟩
 obtain⟨h,d⟩:=(u v).1 (U.max'_mem _);by_cases b:v=ρ
 ·exact b▸d
 obtain⟨j,a,c⟩:=jO tr h b;have f:=(S.or_ j (bd j a) (tr.1 j a).1).2 ⟨v,c,Or.inl d⟩;have le:=U.le_max' (n+j) ((u _).2 ⟨Or.inr ⟨j,a,rfl⟩,f⟩);exact(not_lt_of_ge le (rb j (bd j a) v c)).elim
lemma dD (tr:IsOrTree n C G L ρ) (rb:ReadsBack n C)
  (bd:∀j∈G,j<C.gates.length) (P:gA C G ρ sink W c)
  (sel:gH S c W):mR S ρ sink:=by
 rcases P with⟨j,a,rfl,b⟩|⟨rfl,rfl⟩
 ·apply Or.inl (zX S tr rb bd (Or.inr ⟨j,a,rfl⟩) _);exact(S.or_ _ (bd _ a) (tr.1 _ a).1).2 ⟨W,b,Or.inr sel⟩
 ·exact Or.inr sel
def jV (S:Trace n C d W) (G:Finset ℕ) (ρ:ℕ) (sink:Option ℕ):=∃c,gA C G ρ sink W c∧gH S c W
lemma eS (tr:IsOrTree n C G L ρ) (rb:ReadsBack n C)
  (bd:∀j∈G,j<C.gates.length) (b:bB C ρ sink)
  (m:mR S ρ sink):jV S G ρ sink∨∃i∈L,S.mark i:=by
 rcases m with m|m
 ·refine fS tr rb bd (fun w=>S.mark w→_) ?_ ?_ _ (cC tr) m
  ·exact fun a g k=>Or.inr ⟨a,g,k⟩
  ·intro j c h o;obtain⟨i,d,l|f⟩:=(S.or_ j (bd j c) (tr.1 j c).1).1 o
   ·exact h _ d l
   ·obtain rfl:=S.source j (bd j c) i d f;exact Or.inl ⟨some j,Or.inl ⟨j,c,rfl,d⟩,f⟩
 ·have e:=wC S b m;exact Or.inl ⟨sink,Or.inr ⟨rfl,e.symm⟩,e▸m⟩
include h in
lemma dL (ht:t∈d.cover):
  bB C (d.zroot t) (some (d.bw t-n))∧bB C (d.oroot t) (some (d.bw t-n)):=by
 obtain⟨j,b,e,_,_,a⟩:=dN h ht;rcases a with a|a<;>simp[bB,e,b,a]
abbrev oX (t:Fin n):=jV S (Z t d C) (d.zroot t) (some (d.bw t-n))
abbrev fE (t:Fin n):=jV S (O t d C) (d.oroot t) (some (d.bw t-n))
abbrev gV:=jV S (topGates d C) C.output none
include h
lemma mS (ht:t∈d.cover):eL S t↔oX S t:=by
 constructor
 ·intro m;obtain p|⟨i,b,a⟩:=eS S (bL h ht) h.1 aT (dL h ht).1 m
  ·exact p
  rcases dF.mp b with rfl|⟨s,hs,_,rfl⟩
  ·exact(S.raw _ a).elim
  ·exact(S.and_ _ hs a).elim
 ·rintro⟨c,p,sel⟩;exact dD S (bL h ht) h.1 aT p sel
lemma qG:eG S↔gV S:=by
 constructor
 ·intro m;obtain p|⟨i,d,b⟩:=eS S h.2.2.2.2.2.2 h.1 kD (show bB C C.output none from rfl) m
  ·exact p
  rcases Finset.mem_union.mp d with hl|hl
  ·obtain⟨a,e,rfl⟩:=Finset.mem_image.mp hl;exact(S.raw _ b).elim
  ·obtain⟨s,hs,rfl⟩:=Finset.mem_image.mp hl;exact(S.and_ _ (Finset.mem_filter.mp hs).1 b).elim
 ·rintro⟨c,p,sel⟩;exact dD S h.2.2.2.2.2.2 h.1 kD p sel
lemma xF (ht:t∈d.cover) (m:jU S t):
  fE S t∨∃r∈d.cover,d.owns t r=true∧S.mark (d.lam t r)∧eL S r:=by
 obtain p|⟨i,c,a⟩:=eS S (cT h ht) h.1 aT (dL h ht).2 m
 ·exact Or.inl p
 obtain⟨r,e,rfl⟩:=iZ.mp c;have hl:=lam h e;unfold LamOK at hl
 split at hl
 ·rename_i hr
  refine Or.inr ⟨r,hr,e,a,Or.inl (zX S (bL h hr) h.1 aT ?_ a)⟩;rcases hl.2.1 with b|⟨j,f,b,role⟩
  ·exact Or.inl (dF.mpr (Or.inl b))
  ·exact Or.inr ⟨j,by simp[gatesOf,f,role],b⟩
 ·rw[hl] at a;exact(S.raw _ a).elim
lemma mT (ht:t∈d.cover) (m:eL S t):dP t d C W:=by obtain⟨_,P,_⟩:=(mS h S ht).1 m;exact cG (bL h ht) P
lemma rS (ht:t∈d.cover) (a:u∈d.cover) (mt:eL S t) (b:eL S u):t=u:=qV h (mT h S ht mt) (mT h S a b)
lemma yA (ht:t∈d.cover) (m:eL S t):¬jU S t:=by
 intro a;obtain⟨_,p,_⟩|⟨r,hr,e,_,b⟩:=xF h S ht a
 ·exact zU h ht (mT h S ht m) (cG (cT h ht) p)
 ·exact(h.2.2.1.1 _ _ e).1.ne (rS h S ht hr m b)
lemma yB (ht:t∈d.cover) (node:dP t d C w) (m:S.mark w):W<w:=by
 refine fS (bL h ht) h.1 aT (fun i=>S.mark i→W< i) ?_ ?_ _ node m
 ·intro a f e;rcases dF.mp f with rfl|⟨s,hs,_,rfl⟩
  ·exact(S.raw _ e).elim
  ·exact(S.and_ _ hs e).elim
 ·intro j b g l;obtain⟨i,c,k|n⟩:=(S.or_ _ (aT _ b) ((bL h ht).1 _ b).1).1 l
  ·exact(g _ c k).trans (h.1 _ (aT _ b) _ c)
  ·exact S.source _ (aT _ b) _ c n▸h.1 _ (aT _ b) _ c
lemma tiedRoot (ht:t∈d.cover) (i:eL S t) (τ:d.tie t=some u)
  (g:d.zroot t=W) (f:jU S u):fE S u:=by
 have edge:=(h.2.2.2.1 _ _ τ).2;have c:=(h.2.2.1.1 _ _ edge).2;obtain b|⟨r,hr,_,a,e⟩:=xF h S c f
 ·exact b
 obtain rfl:=rS h S hr ht e i;have hl:=lam h edge;simp only[LamOK,ht,↓reduceIte] at hl;rw[hl.2.2 τ] at a;have j:=yB h S ht (cC (bL h ht)) a;omega
include iso in
lemma fF {c} (a:bK d C A w) (b:bB C w c):xE d C w c:=by
 obtain f|⟨t,ht,g|e⟩:=lX h b
 ·exact f
 ·exact(lW h iso a ht (cG (bL h ht) g)).elim
 ·exact(qF h iso a (cG (cT h ht) e)).elim
lemma aB6 {p} (k:p∈d.cover) (top:¬eG S)
  (f:∀t∈d.cover,¬eL S t)
  (g:∀t∈d.cover,jU S t→t=p) {c} (e:bB C W c) (sel:gH S c W):
  zW d C p W c:=by
 obtain i|⟨u,a,j|b⟩:=lX h e
 ·exact(top (dD S h.2.2.2.2.2.2 h.1 kD i sel)).elim
 ·exact(f _ a (dD S (bL h a) h.1 aT j sel)).elim
 ·exact g _ a (dD S (cT h a) h.1 aT b sel)▸b
lemma aB7 (ht:t∈d.cover) (j:eL S t) (top:¬eG S)
  (f:∀u∈d.cover,¬jU S u) {c} (e:bB C W c) (sel:gH S c W):
  zV d C t W c:=by
 obtain i|⟨u,a,b|g⟩:=lX h e
 ·exact(top (dD S h.2.2.2.2.2.2 h.1 kD i sel)).elim
 ·exact rS h S a ht (dD S (bL h a) h.1 aT b sel) j▸b
 ·exact(f _ a (dD S (cT h a) h.1 aT g sel)).elim
end PEqualNP.MetaComplexity.NestedCover.Ad
namespace PEqualNP.MetaComplexity.NestedCover.Ad
open PEqualNP.CircuitLowerBounds Af Ac
variable {n : ℕ} {D P : Circuit} {g w : ℕ ↪ ℕ} {src fresh j : ℕ}
variable {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {d : NCCData n}
variable (h : Valid n K A D d) (sp : Splice n D P g w src fresh)
def aE:Trace n D d src where
 sel:=Ae.Sel P g src fresh
 selTop:=P.output=fresh
 mark:=Ae.sW n D P g src fresh
 source:=fun _ _ _ _ b=>b.1
 sourceTop:=fun e=>(sp.output src).2 (Or.inr ⟨e,rfl⟩)
 raw r:=(Ae.jR (Ae.qD r)).1
 and_ _ ht:=(Ae.jR (Ae.rQ (dN h ht))).1
 or_:=fun _ a op=>Ae.sV a op
include sp
lemma fresh_actual (c:j<D.gates.length) (a:fresh∈(gateAt P (g j)).inputs):
  bB D src (some j):=by
 obtain⟨i,b⟩:=List.mem_iff_getElem?.1 a;exact⟨c,List.mem_of_getElem? ((sp.pin j i src).2 (Or.inr ⟨b,rfl⟩))⟩
omit sp
include h in
lemma yC (c:j<D.gates.length):(gateAt D j).inputs.Nodup:=by
 by_cases op:(gateAt D j).op= .or
 ·exact Ae.aBv h c op
 have a (e:(d.role j).1= .top):False:=op
  (h.2.2.2.2.2.2.1 _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr c,e⟩)).1
 obtain e|⟨t,ht,tP,g⟩:=h.2.2.2.2.1 j c
 ·exact(a e).elim
 cases hr:(d.role j).1 with
 | top=>exact(a hr).elim
 | z=>exact(op ((bL h ht).1 _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr c,Prod.ext hr tP⟩)).1).elim
 | o=>exact(op ((cT h ht).1 _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr c,Prod.ext hr tP⟩)).1).elim
 | b=>
   obtain⟨i,_,e,_,_,f⟩:=dN h ht;have ij:=Nat.add_left_cancel (e.symm.trans (g hr));subst i;rcases f with f|f<;>simp[f,Ae.jT h ht,Ne.symm (Ae.jT h ht)]
include sp h
lemma cH (r:j<D.gates.length):
  (gateAt P (g j)).inputs=(gateAt D j).inputs.map (fun i=>
    if i=src∧fresh∈(gateAt P (g j)).inputs then fresh else w i):=by
 classical
 apply List.ext_getElem
 ·simp[sp.total]
 intro s hs f;have p:s<(gateAt D j).inputs.length:=by simpa using f
 rw[List.getElem_map]
 let i:=(gateAt D j).inputs[s]
 have b:(gateAt D j).inputs[s]?=some i:=List.getElem?_eq_getElem p;have l:=List.getElem?_eq_getElem hs;rcases (sp.pin j s i).1 b with a|⟨a,o⟩
 ·have hh:¬(i=src∧fresh∈(gateAt P (g j)).inputs):=by
   rintro⟨n,q⟩;obtain⟨k,e⟩:=List.mem_iff_getElem?.1 q;have m:=(sp.pin j k i).2 (Or.inr ⟨e,n⟩);obtain⟨_,c⟩:=List.getElem?_eq_some_iff.1 b;obtain⟨_,d⟩:=List.getElem?_eq_some_iff.1 m;obtain rfl:=(yC h r).getElem_inj_iff.1 (c.trans d.symm);exact sp.hole _ (Option.some.inj (a.symm.trans e))
  change _=if i=src∧_ then _ else _
  rw[ite_eq_right hh];exact Option.some.inj (l.symm.trans a)
 ·have hh:i=src∧fresh∈(gateAt P (g j)).inputs:=⟨o,List.mem_of_getElem? a⟩
  change _=if i=src∧_ then _ else _
  rw[ite_eq_left hh];exact Option.some.inj (l.symm.trans a)
def zY (D P:Circuit) (g:ℕ ↪ ℕ) (fresh:ℕ):=P.output=fresh∨∃j<D.gates.length,fresh∈(gateAt P (g j)).inputs
lemma uU (live:zY D P g fresh):
  ∃c,bB D src c∧gH (aE h sp) c src:=by
 obtain b|⟨j,d,a⟩:=live
 ·exact⟨none,((sp.output src).2 (Or.inr ⟨b,rfl⟩)).symm,b⟩
 ·exact⟨some j,fresh_actual sp d a,rfl,a⟩
lemma qW (a:¬eG (aE h sp)):P.output=w D.output:=by
 obtain e|⟨e,_⟩:=(sp.output D.output).1 rfl
 ·exact e
 ·exact(a (Or.inr e)).elim
lemma lB {G L ρ sink} (tr:IsOrTree n D G L ρ)
  (live:zY D P g fresh) (only:∀c,bB D src c→ gH (aE h sp) c src→ gA D G ρ sink src c)
  {c} (b:bB D src c):
  gH (aE h sp) c src↔gA D G ρ sink src c:=by
 obtain⟨k,d,a⟩:=uU h sp live;refine⟨only _ b,fun e=> ?_⟩;exact oE tr (only _ d a) e▸a
lemma zZ (iso:∀a∈A,∀r,¬K.Adj a r)
  (o:bK d D A src) (live:zY D P g fresh):
  (∀j<D.gates.length,(gateAt P (g j)).inputs=(gateAt D j).inputs.map
    (fun i=>if i=src then fresh else w i))∧
  P.output=(if D.output=src then fresh else w D.output)∧
  ∀
   j<D.gates.length,(d.role j).1≠ .top→
   (gateAt P (g j)).inputs=(gateAt D j).inputs.map w:=by
 have tr:=h.2.2.2.2.2.2;have all {c} (f:bB D src c):gH (aE h sp) c src:=(lB h sp tr live (fun _ f _=>fF h iso o f) f).2 (fF h iso o f);refine⟨?_,?_,?_⟩
 ·intro j l;rw[cH h sp l];apply List.map_congr_left;intro i q;by_cases b:i=src
  ·subst i;have n:=(all (c:=some j) ⟨l,q⟩).2;simp[n]
  ·simp[b]
 ·by_cases b:D.output=src
  ·rw[ite_eq_left b];exact all (c:=none) b.symm
  ·obtain e|⟨_,p⟩:=(sp.output D.output).1 rfl
   ·simpa[b] using e
   ·exact(b p).elim
 ·intro j l t;apply sp.unchanged;intro n;obtain⟨k,s,m,_⟩|⟨m,_⟩:=fF h iso o (fresh_actual sp l n)
  ·obtain rfl:=Option.some.inj m;exact t (Finset.mem_filter.mp s).2
  ·cases m
end PEqualNP.MetaComplexity.NestedCover.Ad
namespace PEqualNP.MetaComplexity.NestedCover.Ad
open PEqualNP.CircuitLowerBounds
structure OneLayout (n : ℕ) (D P : Circuit) (l : Fin n) (g w : ℕ ↪ ℕ) (j src : ℕ) : Prop where
  range_eq : Finset.range P.gates.length = insert j ((Finset.range D.gates.length).map g)
  gap : ∀ k, g k ≠ j
  fixed : ∀ v : Fin n, w v.val = v.val
  rb : ReadsBack n P
  opNew : (gateAt P j).op = GateOp.or
  insNew : (gateAt P j).inputs = [w src,l.val] ∨ (gateAt P j).inputs = [l.val,w src]
end PEqualNP.MetaComplexity.NestedCover.Ad
namespace PEqualNP.MetaComplexity.NestedCover.Am
open PEqualNP.CircuitLowerBounds
def aN (a:ℕ→Gate) (G:Finset ℕ) (w:ℕ):ℕ:=∑j∈G,(a j).inputs.count w
def aM (n:ℕ) (G:Finset ℕ) (i:ℕ):=n≤ i∧i-n∈G
def bN (n:ℕ) (a:ℕ→Gate) (G L:Finset ℕ) (ρ:ℕ):Prop:=
 (∀j∈G,(a j).op=GateOp.or∧(a j).inputs.length=2∧
     ∀i∈(a j).inputs,i∈L∨aM n G i)∧
   (∀w∈L,¬aM n G w∧aN a G w=(if w=ρ then 0 else 1))∧
   (∀j∈G,aN a G (n+j)=(if n+j=ρ then 0 else 1))∧
   (if G= ∅ then L={ρ} else ∃j∈G,ρ=n+j)
lemma aX {n C G L ρ}:bN n (gateAt C) G L ρ↔IsOrTree n C G L ρ:=Iff.rfl
lemma eH {n G i}:aM n G i↔∃j∈G,i=n+j:=by
 constructor
 ·rintro⟨b,a⟩;exact⟨_,a,by omega⟩
 ·rintro⟨j,a,rfl⟩;simpa[aM] using a
lemma uV {n a G L ρ} (tr:bN n a G L ρ):
  ρ∈L∨aM n G ρ:=by
 rcases eq_or_ne G ∅ with b|b
 ·have hl:L={ρ}:=by simpa[b] using tr.2.2.2
  simp[hl]
 ·exact Or.inr (eH.mpr (by simpa[b] using tr.2.2.2))
lemma qH {n a G L ρ} (tr:bN n a G L ρ) {w}
  (d:w∈L∨aM n G w):
  aN a G w=(if w=ρ then 0 else 1):=by
 rcases d with hl|b
 ·exact(tr.2.1 _ hl).2
 ·obtain⟨j,c,rfl⟩:=eH.mp b;exact tr.2.2.1 j c
lemma lC {n a G L ρ} (tr:bN n a G L ρ) {w}
  (hl:w∉L) (b:¬aM n G w):aN a G w=0:=
 Finset.sum_eq_zero fun j c=>List.count_eq_zero_of_not_mem fun d=>((tr.1 j c).2.2 w d).elim hl b
lemma fV {n m a b G L ρ}
  (tr:bN n a G L ρ) (f w:ℕ ↪ ℕ)
  (align:∀j∈G,w (n+j)=m+f j)
  (op:∀j∈G,(b (f j)).op=(a j).op)
  (bS:∀j∈G,(b (f j)).inputs=(a j).inputs.map w):
  bN m b (G.map f) (L.map w) (w ρ):=by
 have p (v:ℕ):aM m (G.map f) (w v)↔aM n G v:=by
  simp only[eH];constructor
  ·rintro⟨k,e,d⟩;obtain⟨j,c,rfl⟩:=Finset.mem_map.mp e;exact⟨j,c,w.injective (d.trans (align _ c).symm)⟩
  ·rintro⟨j,c,rfl⟩;exact⟨_,Finset.mem_map.mpr ⟨_,c,rfl⟩,align _ c⟩
 have q (v:ℕ):aN b (G.map f) (w v)=aN a G v:=by unfold aN;rw[Finset.sum_map];exact Finset.sum_congr rfl (fun j c=>by simp[bS j c,List.count_map_of_injective _ _ w.injective])
 refine⟨?_,?_,?_,?_⟩
 ·intro k e;obtain⟨j,c,rfl⟩:=Finset.mem_map.mp e;obtain⟨t,g,i⟩:=tr.1 j c;rw[op j c,bS j c];refine⟨t,by simpa using g,?_⟩;intro v o;obtain⟨u,l,rfl⟩:=List.mem_map.mp o;exact(i _ l).imp (fun h=>Finset.mem_map.mpr ⟨_,h,rfl⟩) (p _).mpr
 ·intro v o;obtain⟨u,l,rfl⟩:=Finset.mem_map.mp o;obtain⟨s,r⟩:=tr.2.1 u l;simpa[p,q] using And.intro s r
 ·intro k e;obtain⟨j,c,rfl⟩:=Finset.mem_map.mp e;rw[←align _ c,q];simpa using tr.2.2.1 j c
 ·by_cases d:G= ∅
  ·have hl:L={ρ}:=by simpa[d] using tr.2.2.2
   simp[d,hl]
  ·obtain⟨j,c,hρ⟩:∃j∈G,ρ=n+j:=by simpa[d] using tr.2.2.2
   simpa[d] using(show ∃k∈G.map f,w ρ=m+k from⟨_,Finset.mem_map.mpr ⟨_,c,rfl⟩,by rw[hρ,align _ c]⟩)
lemma aCk {n a b G L ρ j x l}
  (tr:bN n a G L ρ)
  (z:x∈L∨aM n G x) (M:j∉G) (F:n+j∉L)
  (C:l∉L) (w:¬aM n G l) (q:l≠n+j)
  (op:∀k∈G,(b k).op=(a k).op)
  (bS:∀k∈G,(b k).inputs=
    (a k).inputs.map (fun i=>if i=x then n+j else i))
  (Z:(b j).op=GateOp.or)
  (J:(b j).inputs=[x,l]∨(b j).inputs=[l,x]):
  bN n b (insert j G) (insert l L) (if ρ=x then n+j else ρ):=by
 let u:=n+j
 let s:=Equiv.swap x u
 have f {v} (g:v∈L∨aM n G v):v≠u:=by
  rintro rfl;rcases g with h|h
  ·exact F h
  ·exact M (by simpa[u,aM] using h)
 have m {v} (g:v∈L∨aM n G v):v≠l:=by rintro rfl;exact g.elim C w
 have A:=f z;have r:=m z;have huρ:=f (uV tr);have hlρ:=m (uV tr);have K (k) (c:k∈G):(b k).inputs=(a k).inputs.map s:=by
  rw[bS k c];apply List.map_congr_left;intro i y;have V:=f ((tr.1 k c).2.2 i y);by_cases d:i=x
  ·subst i;simp[s,u]
  ·simp[s,d,Equiv.swap_apply_of_ne_of_ne d V]
 have P (v:ℕ):aN b G v=aN a G (s v):=by have E:s (s v)=v:=Equiv.swap_apply_self _ _ _;unfold aN;apply Finset.sum_congr rfl;intro k c;rw[K k c,←E,List.count_map_of_injective _ _ s.injective,E]
 have p (v:ℕ):aN b (insert j G) v=
   ((if x=v then 1 else 0)+(if l=v then 1 else 0))+
   aN a G (s v):=by
  change(∑k∈insert j G,(b k).inputs.count v)=_;rw[Finset.sum_insert M,←P];congr 1;rcases J with e|e<;>rw[e]<;>by_cases h:x=v<;>by_cases h':l=v<;>simp_all
 have t {v} (g:v∈L∨aM n G v):
   aN b (insert j G) v=if v=(if ρ=x then u else ρ) then 0 else 1:=by
  have H:=f g;have S:=m g;rw[p];by_cases d:v=x
  ·subst v;have hz:=lC tr F (show ¬aM n G u by simpa[aM,u] using M);rw[show s x=u from Equiv.swap_apply_left ..,hz];by_cases h:ρ=x
   ·simp[h,A,Ne.symm r]
   ·simp[h,Ne.symm h,Ne.symm r]
  ·rw[show s v=v from Equiv.swap_apply_of_ne_of_ne d H,
       qH tr g]
   by_cases h:ρ=x<;>simp[h,d,Ne.symm d,Ne.symm S,H]
 have U:aN b (insert j G) u=if u=(if ρ=x then u else ρ) then 0 else 1:=by
  rw[p,show s u=x from Equiv.swap_apply_right ..,qH tr z];have o:l≠u:=q;by_cases d:ρ=x
  ·simp[d,A,o]
  ·simp[d,Ne.symm d,A,o,Ne.symm huρ]
 have T:aN b (insert j G) l=if l=(if ρ=x then u else ρ) then 0 else 1:=by rw[p,show s l=l from Equiv.swap_apply_of_ne_of_ne (Ne.symm r) q,lC tr C w];have o:l≠u:=q;by_cases d:ρ=x<;>simp[d,r,o,Ne.symm hlρ]
 have B {v} (g:v∈L∨aM n G v):
   v∈insert l L∨aM n (insert j G) v:=by
  rcases g with h|⟨hl,X⟩
  ·exact Or.inl (Finset.mem_insert_of_mem h)
  ·exact Or.inr ⟨hl,Finset.mem_insert_of_mem X⟩
 refine⟨?_,?_,?_,?_⟩
 ·intro k c;rcases Finset.mem_insert.mp c with rfl|c
  ·refine⟨Z,?_,?_⟩
   ·rcases J with e|e<;>simp[e]
   ·intro i y;have hh:i=x∨i=l:=by rcases J with e|e<;>simpa[e,or_comm] using y
    rcases hh with rfl|rfl
    ·exact B z
    ·simp
  ·obtain⟨R,N,O⟩:=tr.1 k c;rw[op k c,bS k c];refine⟨R,by simpa using N,?_⟩;intro i y;obtain⟨v,g,rfl⟩:=List.mem_map.mp y;by_cases d:v=x
   ·simp[d,aM]
   ·simpa[d] using B (O v g)
 ·intro v g;rcases Finset.mem_insert.mp g with rfl|g
  ·exact⟨fun h=>by
    obtain⟨k,c,e⟩:=eH.mp h;rcases Finset.mem_insert.mp c with rfl|c
    ·exact q e
    ·exact w (eH.mpr ⟨_,c,e⟩),T⟩
  ·exact⟨fun h=>by
    obtain⟨k,c,e⟩:=eH.mp h;rcases Finset.mem_insert.mp c with rfl|c
    ·exact f (Or.inl g) e
    ·exact(tr.2.1 _ g).1 (eH.mpr ⟨_,c,e⟩),t (Or.inl g)⟩
 ·intro k c;rcases Finset.mem_insert.mp c with rfl|c
  ·exact U
  ·exact t (Or.inr (eH.mpr ⟨_,c,rfl⟩))
 ·rw[ite_eq_right (Finset.insert_ne_empty _ _)];by_cases d:ρ=x
  ·exact⟨j,Finset.mem_insert_self ..,ite_eq_left d⟩
  ·have Q:G≠ ∅ :=by
    rintro rfl;have hl:L={ρ}:=by simpa using tr.2.2.2
    simp[aM,hl,Ne.symm d] at z
   obtain⟨k,c,e⟩:∃k∈G,ρ=n+k:=by simpa[Q] using tr.2.2.2
   exact⟨_,Finset.mem_insert_of_mem c,(ite_eq_right d).trans e⟩
lemma gK {n m C D G L ρ j x l}
  (tr:IsOrTree n C G L ρ) (f w:ℕ ↪ ℕ)
  (align:∀k∈G,w (n+k)=m+f k)
  (v:x∈L∨aM n G x)
  (t:j∉G.map f) (s:m+j∉L.map w)
  (q:l∉L.map w) (p:¬aM m (G.map f) l) (r:l≠m+j)
  (op:∀k∈G,(gateAt D (f k)).op=(gateAt C k).op)
  (bS:∀k∈G,(gateAt D (f k)).inputs=
    (gateAt C k).inputs.map (fun i=>if i=x then m+j else w i))
  (u:(gateAt D j).op=GateOp.or)
  (d:(gateAt D j).inputs=[w x,l]∨(gateAt D j).inputs=[l,w x]):
  IsOrTree m D (insert j (G.map f)) (insert l (L.map w)) (if ρ=x then m+j else w ρ):=by
 classical
 let a (k:ℕ):Gate:=let g:=gateAt C (Function.invFun f k);⟨g.op,g.inputs.map w⟩
 have e (k:ℕ):Function.invFun f (f k)=k:=Function.leftInverse_invFun f.injective _;have ht:=fV (b:=a) (aX.mpr tr) f w align
  (fun k _=>by simp[a,e]) (fun k _=>by simp[a,e])
 have o:w x∈L.map w∨aM m (G.map f) (w x):=by
  rcases v with h|h
  ·exact Or.inl (Finset.mem_map.mpr ⟨_,h,rfl⟩)
  ·obtain⟨k,c,rfl⟩:=eH.mp h;exact Or.inr (eH.mpr ⟨_,Finset.mem_map.mpr ⟨_,c,rfl⟩,align _ c⟩)
 apply aX.mp;simpa only[EmbeddingLike.apply_eq_iff_eq] using
  (aCk ht o t s q p r (b:=gateAt D) (fun k c=>by
    obtain⟨i,d,rfl⟩:=Finset.mem_map.mp c;simpa[a,e] using op i d)
    (fun k c=>by
      obtain⟨i,d,rfl⟩:=Finset.mem_map.mp c;simpa[a,e,List.map_map,Function.comp_def] using bS i d) u d)
end PEqualNP.MetaComplexity.NestedCover.Am
namespace PEqualNP.MetaComplexity.NestedCover.Am
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C D : Circuit} {d : NCCData n} {p l : Fin n} {j x : ℕ} {f w : ℕ ↪ ℕ}
structure OwnerPins (n : ℕ) (C D : Circuit) (d : NCCData n)
    (p l : Fin n) (f w : ℕ ↪ ℕ) (j x : ℕ) : Prop where
  range_eq : Finset.range D.gates.length = insert j ((Finset.range C.gates.length).map f)
  gap : ∀ k, f k ≠ j
  fixed : ∀ v : Fin n, w v.val = v.val
  align : ∀ k, w (n+k) = n+f k
  rb : ReadsBack n D
  output : D.output = w C.output
  op : ∀ k < C.gates.length, (gateAt D (f k)).op = (gateAt C k).op
  opNew : (gateAt D j).op = GateOp.or
  insNew : (gateAt D j).inputs = [w x,l.val] ∨ (gateAt D j).inputs = [l.val,w x]
  insO : ∀ k < C.gates.length, d.role k = (.o,p.val) →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map (fun i => if i = x then n+j else w i)
  insB : ∀ k < C.gates.length, d.role k = (.b,p.val) → d.oroot p = x →
    (gateAt D (f k)).inputs =
      (if (gateAt C k).inputs = [d.zroot p,d.oroot p]
       then [w (d.zroot p),n+j] else [n+j,w (d.zroot p)])
  insOther : ∀ k < C.gates.length, d.role k ≠ (.o,p.val) →
    (d.role k ≠ (.b,p.val) ∨ d.oroot p ≠ x) →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map w
noncomputable def aF (d:NCCData n) (p l:Fin n) (f w:ℕ ↪ ℕ)
  (j x:ℕ):NCCData n where
 cover:=d.cover
 owns t r:=if t=p∧r=l then true else d.owns t r
 tie:=d.tie
 role k:=if k=j then(.o,p.val) else d.role (Function.invFun f k)
 bw t:=w (d.bw t)
 zroot t:=w (d.zroot t)
 oroot t:=if t=p∧d.oroot t=x then n+j else w (d.oroot t)
 lam t r:=if t=p∧r=l then l.val else w (d.lam t r)
lemma mU (P:OwnerPins n C D d p l f w j x) (k):
  (aF d p l f w j x).role (f k)=d.role k:=by
 simp[aF,P.gap k,Function.leftInverse_invFun f.injective k]
lemma oldBound (P:OwnerPins n C D d p l f w j x) {k} (h:k<C.gates.length):
 f
  k<D.gates.length:=Finset.mem_range.mp (P.range_eq▸
  Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨_,Finset.mem_range.mpr h,rfl⟩))
lemma xG (P:OwnerPins n C D d p l f w j x)
  (Q:Kind×ℕ→Prop) [DecidablePred Q]:
  (Finset.range D.gates.length).filter (fun k=>Q ((aF d p l f w j x).role k))=
    (if Q (.o,p.val) then insert j else id)
      (((Finset.range C.gates.length).filter (fun k=>Q (d.role k))).map f):=by
 classical
 have b (k):(aF d p l f w j x).role (f k)=d.role k:=mU P _;have a:(aF d p l f w j x).role j=(.o,p.val):=by simp[aF]
 rw[P.range_eq,Finset.filter_insert,Finset.filter_map];simp only[Function.comp_def,b,a]
 split_ifs<;>rfl
lemma wD (P:OwnerPins n C D d p l f w j x) (t):
  zLeaves (aF d p l f w j x) t=(zLeaves d t).map w:=by
 ext v;simp[zLeaves,aF,P.fixed,eq_comm]
lemma sX (P:OwnerPins n C D d p l f w j x):
  topLeaves (aF d p l f w j x) A=(topLeaves d A).map w:=by
 ext v;simp[topLeaves,Finset.map_union,aF,P.fixed,eq_comm]
lemma qI (h:d.owns p l=false) (t):
  oLeaves (aF d p l f w j x) t=(if t=p then insert l.val else id) ((oLeaves d t).map w):=by
 classical
 by_cases b:t=p
 ·subst t;ext v;simp only[oLeaves,aF,true_and,Finset.mem_image,Finset.mem_filter,
   Finset.mem_univ,Finset.mem_map,Finset.mem_insert,ite_true]
  constructor
  ·rintro⟨r,a,e⟩;by_cases hr:r=l
   ·subst r;exact Or.inl (by simpa using e.symm)
   ·simp[hr] at a e;exact Or.inr ⟨_,⟨r,a,rfl⟩,e⟩
  ·rintro(rfl|⟨_,⟨r,a,rfl⟩,rfl⟩)
   ·exact⟨l,by simp,by simp⟩
   ·have hr:r≠l:=by rintro rfl;simp_all
    exact⟨r,by simp[hr,a],by simp[hr]⟩
 ·ext v;simp[oLeaves,aF,b]
lemma wE (P:OwnerPins n C D d p l f w j x) (rb:ReadsBack n C)
  {v} (t:v<n+C.gates.length):IsCentred n D (aF d p l f w j x) (w v)↔IsCentred n C d v:=by
 induction v using Nat.strong_induction_on with
 | ind v ih=>
   by_cases h:v<n
   ·let r:Fin n:=⟨v,h⟩
    change IsCentred n D (aF d p l f w j x) (w r.val)↔IsCentred n C d r.val;rw[P.fixed,aG,aG];rfl
   ·obtain⟨k,rfl⟩:∃k,v=n+k:=⟨v-n,by omega⟩
    have c:k<C.gates.length:=by omega
    rw[P.align,aR P.rb (oldBound P c),aR rb c,mU P];by_cases g:(d.role k).1=Kind.z
    ·have q:d.role k≠(.o,p.val):=by rintro e;simp[e] at g
     have m:d.role k≠(.b,p.val):=by rintro e;simp[e] at g
     rw[P.insOther k c q (Or.inl m)];simp only[g,true_and];have e (i) (a:i∈(gateAt C k).inputs):=ih i (rb k c i a)
      (show i<n+C.gates.length by have:=rb k c i a;omega)
     constructor
     ·rintro⟨_,s,hh⟩;obtain⟨i,a,rfl⟩:=List.mem_map.mp s;exact⟨_,a,(e i a).mp hh⟩
     ·rintro⟨i,a,hh⟩;exact⟨_,List.mem_map.mpr ⟨i,a,rfl⟩,(e i a).mpr hh⟩
    ·simp[g]
lemma qJ (P:OwnerPins n C D d p l f w j x) {Q:Kind×ℕ→Prop}
  [DecidablePred Q] (c:¬Q (.o,p.val)) (h:¬Q (.b,p.val))
  {L ρ} (ht:IsOrTree n C ((Finset.range C.gates.length).filter
   fun k=>Q (d.role k)) L ρ):
  IsOrTree n D ((Finset.range D.gates.length).filter fun k=>Q ((aF d p l f w j x).role k)) (L.map w) (w ρ):=by
 rw[xG P Q,ite_eq_right c,id_eq];apply aX.mp (fV (aX.mpr ht) f w (fun k _=>P.align k) _ _)
 ·intro k a;exact P.op _ (Finset.mem_range.mp (Finset.mem_filter.mp a).1)
 ·intro k a;obtain⟨i,g⟩:=Finset.mem_filter.mp a;apply P.insOther _ (Finset.mem_range.mp i)
  ·intro e;exact c (e▸g)
  ·exact Or.inl (fun e=>h (e▸g))
lemma yD (P:OwnerPins n C D d p l f w j x) (i):w i≠n+j:=by
 by_cases h:i<n
 ·have e:=P.fixed ⟨i,h⟩;change w i=i at e;omega
 ·obtain⟨k,rfl⟩:∃k,i=n+k:=⟨i-n,by omega⟩
  rw[P.align];have:=P.gap k;omega
lemma wF (v:Valid n K A C d) (iso:∀r,¬K.Adj l r)
  (i:p∈d.cover):l.val∉oLeaves d p:=by
 intro h;obtain⟨r,hr,e⟩:=Finset.mem_image.mp h;have g:=(Finset.mem_filter.mp hr).2;have b:r≠l:=by rintro rfl;exact iso _ ((v.2.2.1.1 _ _ g).1.symm)
 have a:=(v.2.2.2.2.2.1 p i).2.2.2 r g;by_cases f:r∈d.cover
 ·rw[LamOK,ite_eq_left f] at a;rcases a.2.1 with c|⟨k,_,c,_⟩
  ·exact b (Fin.ext (c.symm.trans e))
  ·have:=l.isLt;omega
 ·rw[LamOK,ite_eq_right f] at a;exact b (Fin.ext (a.symm.trans e))
lemma sY (v:Valid n K A C d) (P:OwnerPins n C D d p l f w j x)
  (iso:∀r,¬K.Adj l r) (B:p∈d.cover)
  (E:x∈oLeaves d p∨aM n (gatesOf d C .o p.val) x):
  (∀t∈d.cover,
    IsOrTree n D (gatesOf (aF d p l f w j x) D .z t.val) (zLeaves (aF d p l f w j x) t) ((aF d p l f w j x).zroot t)∧
    IsOrTree n D (gatesOf (aF d p l f w j x) D .o t.val) (oLeaves (aF d p l f w j x) t) ((aF d p l f w j x).oroot t))∧
    IsOrTree n D (topGates (aF d p l f w j x) D) (topLeaves (aF d p l f w j x) A) D.output:=by
 have s:d.owns p l=false:=by
  cases e:d.owns p l
  ·rfl
  ·exact False.elim (iso _ (v.2.2.1.1 _ _ e).1.symm)
 constructor
 ·intro t ht;obtain⟨_,F,q,_⟩:=v.2.2.2.2.2.1 t ht;constructor
  ·rw[wD P];exact qJ P (Q:=(· =(.z,t.val))) (by simp) (by simp) F
  ·by_cases b:t=p
   ·subst t;have i:gatesOf (aF d p l f w j x) D .o p.val=insert j ((gatesOf d C .o p.val).map f):=by
     simpa[gatesOf] using xG P (· =(.o,p.val))
    rw[i,qI s p];have m:l.val∉(oLeaves d p).map w:=by rw[←P.fixed l];simpa using wF v iso B
    simp only[ite_true,aF,eq_self,true_and];apply gK q f w (fun k _=>P.align k) E
    ·rintro a;obtain⟨k,_,e⟩:=Finset.mem_map.mp a;exact P.gap _ e
    ·rintro a;obtain⟨k,_,e⟩:=Finset.mem_map.mp a;exact yD P _ e
    ·exact m
    ·exact fun h=>(Nat.not_le.mpr l.isLt) h.1
    ·have:=l.isLt;omega
    ·intro k c;exact P.op _ (Finset.mem_range.mp (Finset.mem_filter.mp c).1)
    ·intro k c;obtain⟨a,y⟩:=Finset.mem_filter.mp c;exact P.insO _ (Finset.mem_range.mp a) y
    ·exact P.opNew
    ·exact P.insNew
   ·have g:p.val≠t.val:=fun e=>b (Fin.ext e.symm)
    rw[qI s t,ite_eq_right b,id_eq];have u:(aF d p l f w j x).oroot t=w (d.oroot t):=by simp[aF,b]
    rw[u];exact qJ P (Q:=(· =(.o,t.val))) (by simp[g]) (by simp) q
 ·rw[P.output,sX P];exact qJ P (Q:=(·.1= .top)) (by simp) (by simp) v.2.2.2.2.2.2
lemma aBc (P:OwnerPins n C D d p l f w j x)
  {t} (dN:TermOK n C d t):TermOK n D (aF d p l f w j x) t:=by
 obtain⟨k,c,g,hr,o,m⟩:=dN;refine⟨f k,oldBound P c,?_,(mU P _).trans hr,(P.op _ c).trans o,?_⟩
 ·change w (d.bw t)=n+f k;rw[g,P.align]
 ·by_cases h:t=p∧d.oroot t=x
  ·obtain⟨rfl,i⟩:=h;rw[P.insB _ c hr i];simp only[aF,i,eq_self,and_self,ite_true]
   split<;>simp
  ·have a:d.role k≠(.b,p.val)∨d.oroot p≠x:=by
    by_cases ht:t=p
    ·subst t;exact Or.inr (fun e=>h ⟨rfl,e⟩)
    ·exact Or.inl (fun e=>ht (Fin.ext (congrArg Prod.snd (hr.symm.trans e))))
   rw[P.insOther _ c (by simp[hr]) a];simp only[aF,ite_eq_right h];rcases m with e|e<;>simp[e]
lemma aB8 (v:Valid n K A C d) (P:OwnerPins n C D d p l f w j x)
  (hl:l∉d.cover) {t r} (ht:t∈d.cover) (i:(aF d p l f w j x).owns t r=true):
  LamOK n D (aF d p l f w j x) t r:=by
 by_cases h:t=p∧r=l
 ·obtain⟨rfl,rfl⟩:=h;simp[LamOK,aF,hl]
 ·have a:=(v.2.2.2.2.2.1 _ ht).2.2.2 r (by simpa[aF,h] using i);by_cases b:r∈d.cover
  ·rw[LamOK,ite_eq_left b] at a;simp only[LamOK,aF,h,ite_false,b,ite_true];have g:d.lam t r<n+C.gates.length:=by
    rcases a.2.1 with e|⟨k,c,e,_⟩
    ·have:=r.isLt;omega
    ·omega
   refine⟨(wE P v.1 g).mpr a.1,?_,fun e=>congrArg w (a.2.2 e)⟩;rcases a.2.1 with e|⟨k,c,e,hr⟩
   ·exact Or.inl (by rw[e,P.fixed])
   ·exact Or.inr ⟨f k,oldBound P c,by rw[e,P.align],(mU P k).trans hr⟩
  ·rw[LamOK,ite_eq_right b] at a;simp[LamOK,aF,h,b,a,P.fixed]
lemma aAa (P:OwnerPins n C D d p l f w j x)
  (m:p∈d.cover) (lD:RolesOK n C d):RolesOK n D (aF d p l f w j x):=by
 intro k g;have a:=P.range_eq▸Finset.mem_range.mpr g;rcases Finset.mem_insert.mp a with rfl|a
 ·exact Or.inr ⟨_,m,by simp[aF],by simp[aF]⟩
 ·obtain⟨i,c,rfl⟩:=Finset.mem_map.mp a;rw[mU P];rcases lD i (Finset.mem_range.mp c) with h|⟨t,ht,e,b⟩
  ·exact Or.inl h
  ·exact Or.inr ⟨_,ht,e,fun h=>(congrArg w (b h)).trans (P.align _)⟩
lemma uW (v:Valid n K A C d) (iso:∀r,¬K.Adj l r)
  (g:p∈d.cover) (ext:∀u v,K'.Adj u v↔
    K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p)):
  IsMinCover K' (aF d p l f w j x).cover∧OwnerOK K' (aF d p l f w j x)∧TieOK (aF d p l f w j x):=by
 have b:p≠l:=by rintro rfl;exact K'.loopless.irrefl _ ((ext _ _).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)))
 obtain⟨cover,m⟩:=v.2.1;obtain⟨a,o⟩:=v.2.2.1;refine⟨⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
 ·intro u z h;rcases (ext _ _).mp h with h|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  ·exact cover h
  ·exact Or.inl g
  ·exact Or.inr g
 ·intro S E;apply m S;intro u z h;exact E ((ext _ _).mpr (Or.inl h))
 ·intro u z c;by_cases k:u=p∧z=l
  ·obtain⟨rfl,rfl⟩:=k;exact⟨(ext _ _).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)),g⟩
  ·obtain⟨F,ht⟩:=a _ _ (by simpa[aF,k] using c);exact⟨(ext _ _).mpr (Or.inl F),ht⟩
 ·intro u z h;rcases (ext _ _).mp h with h|⟨y,B⟩|⟨y,B⟩
  ·have e:¬(u=p∧z=l):=by rintro⟨rfl,rfl⟩;exact iso _ h.symm
   have q:¬(z=p∧u=l):=by rintro⟨rfl,rfl⟩;exact iso _ h
   simpa only[aF,ite_eq_right e,ite_eq_right q] using o _ _ h
  ·subst u;subst z;have i:d.owns l p≠true:=fun e=>iso _ (a _ _ e).1
   simpa[aF,b,Ne.symm b] using Ne.symm i
  ·subst u;subst z;have i:d.owns l p≠true:=fun e=>iso _ (a _ _ e).1
   simpa[aF,b,Ne.symm b] using i
 ·intro s t h;obtain⟨hs,c⟩:=v.2.2.2.1 s t h;exact⟨hs,by simp[aF,c]⟩
lemma eT (v:Valid n K A C d) (P:OwnerPins n C D d p l f w j x)
  (iso:∀r,¬K.Adj l r) (b:p∈d.cover)
  (ext:∀u v,K'.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p))
  (m:x∈oLeaves d p∨aM n (gatesOf d C .o p.val) x):
  Valid n K' A D (aF d p l f w j x):=by
 have hl:l∉d.cover:=by
  intro h;have c:K.IsVertexCover (↑(d.cover.erase l):Set (Fin n)):=by
   intro u z e;have k:u≠l:=by rintro rfl;exact iso _ e
   have q:z≠l:=by rintro rfl;exact iso _ e.symm
   simpa[k,q] using v.2.1.1 e
  have g:=v.2.1.2 _ c;have:=Finset.card_erase_lt_of_mem h;omega
 obtain⟨s,y,B⟩:=uW (f:=f) (w:=w) (j:=j) (x:=x) v iso b ext;obtain⟨a,top⟩:=sY v P iso b m;exact⟨P.rb,s,y,B,aAa P b v.2.2.2.2.1,fun t ht=>
  ⟨aBc P (v.2.2.2.2.2.1 _ ht).1,(a t ht).1,(a t ht).2,
    fun _ i=>aB8 v P hl ht i⟩,top⟩
end PEqualNP.MetaComplexity.NestedCover.Am
namespace PEqualNP.MetaComplexity.NestedCover.Ad
open PEqualNP.CircuitLowerBounds Af Ac Am
variable {n : ℕ} {D P : Circuit} {g w : ℕ ↪ ℕ} {src j : ℕ}
variable {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)} {d : NCCData n}
    {p l : Fin n}
variable (h : Valid n K A D d) (sp : Splice n D P g w src (n+j))
    (lay : OneLayout n D P l g w j src)
include h in
lemma aBd (ht:p∈d.cover):d.role (d.bw p-n)=(.b,p.val):=by obtain⟨k,_,a,c,_⟩:=dN h ht;simpa[a] using c
include h in
lemma aBe {k} (c:k<D.gates.length) (hr:d.role k=(.b,p.val)):
  d.bw p=n+k:=by
 rcases h.2.2.2.2.1 k c with ht|⟨v,f,ev,a⟩
 ·simp[hr] at ht
 ·have e:v=p:=Fin.ext (ev.symm.trans (congrArg Prod.snd hr));exact e▸a (congrArg Prod.fst hr)
include lay in
lemma yE
    (live : zY D P g (n+j)) (hp : p ∈ d.cover) (top : ¬eG (aE h sp))
    (nz : ∀ t ∈ d.cover, ¬eL (aE h sp) t) (oo : ∀ t ∈ d.cover, jU (aE h sp) t → t = p)
    (iso : ∀ r, ¬K.Adj l r)
    (ext : ∀ u v, K'.Adj u v ↔ K.Adj u v ∨ (u = p ∧ v = l) ∨ (u = l ∧ v = p)) :
    IsNestedCoverCircuit n K' A P := by
  have only := fun c => @aB6 _ _ _ _ _ h _ (aE h sp) p hp top nz oo c
  have tr := cT h hp
  obtain ⟨c,ac,sel⟩ := uU h sp live
  have node := cG tr (only c ac sel)
  have marked {c} (ac : bB D src c) (oc : zW d D p src c) : gH (aE h sp) c src :=
    (lB h sp tr live only ac).2 oc
  have pins : OwnerPins n D P d p l g w j src := by
    refine ⟨lay.range_eq,lay.gap,lay.fixed,sp.align,lay.rb,qW h sp top,
      fun k _ => sp.op k,lay.opNew,lay.insNew,?_,?_,?_⟩
    · intro k hk rk
      rw [cH h sp hk]
      apply List.map_congr_left
      intro i hi
      by_cases ei : i = src
      · subst i
        have kg : k ∈ O p d D :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,rk⟩
        have sf := (marked (c := some k) ⟨hk,hi⟩ (Or.inl ⟨k,kg,rfl,hi⟩)).2
        simp [sf]
      · simp [ei]
    · intro k hk rk er
      have eq := aBe h hk rk
      have ki : d.bw p - n = k := by simp [eq]
      have zne := (Ae.jT h hp).trans_eq er
      have sr := (dL h hp).2
      have aa : bB D src (some k) := by rwa [ki,er] at sr
      have sf := (marked aa (Or.inr ⟨by rw [ki],er.symm⟩)).2
      obtain ⟨k',_,e,_,_,bS⟩ := dN h hp
      have ek : k' = k := by omega
      subst k'
      rw [cH h sp hk]
      rcases bS with bS|bS
      · simp [bS,er,zne,sf]
      · simp [bS,er,zne,sf,Ne.symm zne]
    · intro k hk rk rx
      apply sp.unchanged
      intro hf
      have pp := only (some k) (fresh_actual sp hk hf) ⟨rfl,hf⟩
      obtain ⟨k',hk',eq,_⟩|⟨eq,root⟩ := pp
      · obtain rfl := Option.some.inj eq
        exact rk (Finset.mem_filter.mp hk').2
      · have ek := Option.some.inj eq
        exact rx.elim (fun hn => hn (ek ▸ aBd h hp)) (fun hn => hn root.symm)
  refine ⟨_,eT h pins iso hp ext ?_⟩
  rcases node with hl|⟨k,hk,rfl⟩
  · exact Or.inl hl
  · exact Or.inr (by simpa [aM] using hk)
end PEqualNP.MetaComplexity.NestedCover.Ad
namespace PEqualNP.MetaComplexity.NestedCover.Aj
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K : SimpleGraph (Fin n)} {C : Circuit} {d : NCCData n}
  {A : Finset (Fin n)} {r q : Fin n}
def aB (d:NCCData n) (r q:Fin n):NCCData n:={
 cover:=insert q (d.cover.erase r)
 owns:=fun u v=>if u=q∧v=r then true else if u=r∧v=q then false else d.owns u v
 tie:=d.tie
 role:=fun j=>if d.role j=(.b,r.val) then(.b,q.val) else d.role j
 bw:=fun t=>if t=q then d.bw r else d.bw t
 zroot:=fun t=>if t=q then q.val else d.zroot t
 oroot:=fun t=>if t=q then r.val else d.oroot t
 lam:=fun u v=>if u=q then v.val else d.lam u v
}
structure SwapOK (d : NCCData n) (r q : Fin n) : Prop where
  outside : q ∉ d.cover
  edge : d.owns r q = true
  single : ∀ v, d.owns r v = true → v = q
  free : d.tie r = none
lemma wG (h:Valid n K A C d) (s:SwapOK d r q):
  (aB d r q).cover.card=d.cover.card:=by
 have hr:=(h.2.2.1.1 r q s.edge).2;have a:q∉d.cover.erase r:=fun h=>s.outside (Finset.mem_of_mem_erase h)
 exact(Finset.card_insert_of_notMem a).trans (Finset.card_erase_add_one hr)
lemma xH (h:Valid n K A C d) (s:SwapOK d r q):OwnerOK K (aB d r q):=by
 have e:=h.2.2.1;constructor
 ·intro u v c;change(if u=q∧v=r then true else if u=r∧v=q then false else d.owns u v)=true at c
  split at c
  ·obtain⟨rfl,rfl⟩:= ‹u=q∧v=r›;exact⟨(e.1 _ _ s.edge).1.symm,Finset.mem_insert_self ..⟩
  split at c
  ·contradiction
  ·obtain⟨f,k⟩:=e.1 _ _ c;exact⟨f,Finset.mem_insert_of_mem (Finset.mem_erase.mpr
    ⟨fun g=> ‹¬(u=r∧v=q)› ⟨g,s.single v (g▸c)⟩,k⟩)⟩
 ·intro u v f;have diff:=e.2 _ _ f;have ne:u≠v:=f.ne;by_cases a:u=q∧v=r
  ·obtain⟨rfl,rfl⟩:=a;simp[aB,ne,Ne.symm ne]
  by_cases b:u=r∧v=q
  ·obtain⟨rfl,rfl⟩:=b;simp[aB,ne,Ne.symm ne]
  have i:¬(v=r∧u=q):=fun hh=>a hh.symm
  have j:¬(v=q∧u=r):=fun hh=>b hh.symm
  simpa only[aB,ite_eq_right a,ite_eq_right b,ite_eq_right i,ite_eq_right j] using diff
lemma aAb (h:Valid n K A C d) (s:SwapOK d r q):IsMinCover K (aB d r q).cover:=by
 have a:=xH h s;constructor
 ·intro u v c;have b:=a.2 _ _ c
  cases eu:(aB d r q).owns u v<;>cases ev:(aB d r q).owns v u
  ·exact(b (eu.trans ev.symm)).elim
  ·exact Or.inr (a.1 _ _ ev).2
  ·exact Or.inl (a.1 _ _ eu).2
  ·exact(b (eu.trans ev.symm)).elim
 ·rw[wG h s];exact h.2.1.2
lemma aAc (h:Valid n K A C d) (s:SwapOK d r q) (u:Fin n):
  d.tie u≠some r:=by
 intro ht;have a:=h.2.2.2.1 u r ht;exact s.outside ((s.single u a.2)▸a.1)
lemma aAd (h:Valid n K A C d) (s:SwapOK d r q) (u:Fin n):
  d.tie u≠some q:=
 fun ht=>s.outside (h.2.2.1.1 _ _ (h.2.2.2.1 _ _ ht).2).2
lemma aBw (h:Valid n K A C d) (s:SwapOK d r q):d.tie q=none:=by
 cases eq:d.tie q with
 | none=>rfl
 | some v=>exact False.elim (s.outside (h.2.2.2.1 _ _ eq).1)
lemma aCl (h:Valid n K A C d) (s:SwapOK d r q):TieOK (aB d r q):=by
 intro u v ht;change d.tie u=some v at ht;have a:=h.2.2.2.1 _ _ ht;have f:v≠r:=fun b=>aAc h s u (b▸ht)
 have e:v≠q:=fun b=>aAd h s u (b▸ht)
 have c:u≠r:=by rintro rfl;rw[s.free] at ht;contradiction
 exact⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨c,a.1⟩),by simpa[aB,f,e] using a.2⟩
lemma gL {G L:Finset ℕ} {ρ w:ℕ}
  (tr:IsOrTree n C G L ρ) (a:L={w}):G= ∅ ∧ρ=w:=by
 have card:=An.gN tr;rw[a,Finset.card_singleton] at card;have b:G= ∅ :=Finset.card_eq_zero.mp (by omega);have c:L={ρ}:=by simpa[b] using tr.2.2.2
 exact⟨b,Finset.singleton_inj.mp (c.symm.trans a)⟩
lemma dM (h:Valid n K A C d) (s:SwapOK d r q):
  gatesOf d C .z r.val= ∅ ∧d.zroot r=r.val∧
  gatesOf d C .o r.val= ∅ ∧d.oroot r=q.val:=by
 have hr:=(h.2.2.1.1 _ _ s.edge).2;have a:=h.2.2.2.2.2.1 r hr;have b:zLeaves d r={r.val}:=by ext;simp[zLeaves,aAc h s]
 have c:d.lam r q=q.val:=by simpa[LamOK,s.outside] using a.2.2.2 q s.edge
 have e:oLeaves d r={q.val}:=by
  ext w;simp only[oLeaves,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton];constructor
  ·rintro⟨v,f,rfl⟩;exact s.single v f▸c
  ·rintro rfl;exact⟨q,s.edge,c⟩
 exact⟨(gL a.2.1 b).1,(gL a.2.1 b).2,gL a.2.2.1 e⟩
lemma mV (j:ℕ):((aB d r q).role j).1=(d.role j).1:=by simp only[aB];split<;>simp_all
lemma lD (h:Valid n K A C d) (s:SwapOK d r q):RolesOK n C (aB d r q):=by
 intro j l;by_cases c:(d.role j).1= .top
 ·exact Or.inl ((mV j).trans c)
 rcases h.2.2.2.2.1 j l with ht|⟨t,ht,hr,i⟩
 ·exact Or.inl ((mV j).trans ht)
 right;by_cases tr:t=r
 ·subst t;have e:d.role j=(.b,r.val):=by
   have f (k:Kind) (g:(d.role j).1=k):j∈gatesOf d C k r.val:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr l,Prod.ext g hr⟩
   cases a:(d.role j).1 with
   | b=>exact Prod.ext a hr
   | z=>have m:=f .z a;rw[(dM h s).1] at m;contradiction
   | o=>have m:=f .o a;rw[(dM h s).2.2.1] at m;contradiction
   | top=>contradiction
  refine⟨q,Finset.mem_insert_self ..,by simp[aB,e],?_⟩;exact fun _=>by simpa[aB] using i (congrArg Prod.fst e)
 ·have u:t≠q:=fun a=>s.outside (a▸ht)
  have p:d.role j≠(.b,r.val):=fun a=>tr (Fin.ext (hr.symm.trans (congrArg Prod.snd a)))
  exact⟨t,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨tr,ht⟩),by simp[aB,p,hr],fun e=>by simpa[aB,u] using i ((mV j).symm.trans e)⟩
lemma cY (k:Kind) (c:k≠ .b) (u:ℕ):
  gatesOf (aB d r q) C k u=gatesOf d C k u:=by
 ext j;unfold gatesOf;rw[Finset.mem_filter,Finset.mem_filter];change(_∧(if d.role j=(.b,r.val) then(.b,q.val) else d.role j)=(k,u))↔_;by_cases a:d.role j=(.b,r.val)<;>simp[a,Ne.symm c]
lemma aAe (h:Valid n K A C d) (s:SwapOK d r q)
  (k:Kind) (c:k≠ .top):gatesOf d C k q.val= ∅ :=by
 apply Finset.eq_empty_iff_forall_notMem.mpr;intro j b;obtain⟨f,a⟩:=Finset.mem_filter.mp b;rcases h.2.2.2.2.1 j (Finset.mem_range.mp f) with hh|⟨t,ht,e,_⟩
 ·exact c ((congrArg Prod.fst a).symm.trans hh)
 ·exact s.outside ((Fin.ext (e.symm.trans (congrArg Prod.snd a)))▸ht)
lemma aBx (h:Valid n K A C d) (s:SwapOK d r q) (u:Fin n):
  zLeaves (aB d r q) u=zLeaves d u:=by
 ext w;simp only[zLeaves,Finset.mem_insert,Finset.mem_image,Finset.mem_filter];apply or_congr_right;constructor
 ·rintro⟨v,⟨b,a⟩,e⟩;have c:v≠q:=by rintro rfl;change d.tie v=some u at a;rw[aBw h s] at a;contradiction
  exact⟨v,⟨Finset.mem_of_mem_erase ((Finset.mem_insert.mp b).resolve_left c),a⟩,by simpa[aB,c] using e⟩
 ·rintro⟨v,⟨b,a⟩,e⟩;have f:v≠r:=by rintro rfl;rw[s.free] at a;contradiction
  have c:v≠q:=by rintro rfl;exact s.outside b
  exact⟨v,⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨f,b⟩),a⟩,by simpa[aB,c] using e⟩
lemma aBf (h:Valid n K A C d) (s:SwapOK d r q):
  topLeaves (aB d r q) A=topLeaves d A:=by
 have hr:=(h.2.2.1.1 _ _ s.edge).2;ext w;simp only[topLeaves,Finset.mem_union,Finset.mem_image,Finset.mem_filter];apply or_congr_right;constructor
 ·rintro⟨v,⟨c,e⟩,a⟩;by_cases b:v=q
  ·exact⟨r,⟨hr,s.free⟩,by simpa[aB,b] using a⟩
  ·exact⟨v,⟨Finset.mem_of_mem_erase ((Finset.mem_insert.mp c).resolve_left b),e⟩,by simpa[aB,b] using a⟩
 ·rintro⟨v,⟨c,e⟩,a⟩;by_cases f:v=r
  ·exact⟨q,⟨Finset.mem_insert_self ..,by change d.tie q=none;exact aBw h s⟩,by simpa[aB,f] using a⟩
  ·have b:v≠q:=by rintro rfl;exact s.outside c
   exact⟨v,⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨f,c⟩),e⟩,by simpa[aB,b] using a⟩
lemma sZ (h:Valid n K A C d) (s:SwapOK d r q)
  {v:Fin n} (l:v∈d.cover) (p:v≠r):
  ∀j∈gatesOf d C .z v.val,IsCentred n C d (n+j)→IsCentred n C (aB d r q) (n+j):=by
 intro j
 induction j using Nat.strong_induction_on with
 | ind j ih=>
   intro k b;obtain⟨m,o⟩:=Finset.mem_filter.mp k;have a:=Finset.mem_range.mp m;have role:(d.role j).1= .z:=congrArg Prod.fst o;obtain⟨i,c,f⟩:=(cJ h.1 a role).1 b;apply(cJ h.1 a ((mV j).trans role)).2;refine⟨i,c,?_⟩;have tr:=(h.2.2.2.2.2.1 v l).2.1;rcases (tr.1 j k).2.2 i c with leaf|⟨u,g⟩
   ·simp only[zLeaves,Finset.mem_insert,Finset.mem_image,Finset.mem_filter] at leaf;rcases leaf with rfl|⟨t,⟨ht,_⟩,rfl⟩
    ·exact(aG _).2 (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨p,l⟩))
    ·exact(cM (h.2.2.2.2.2.1 t ht).1 f).elim
   ·have lt:=h.1 j a i c;have e:n+(i-n)=i:=by omega
    exact e▸ih (i-n) (by omega) g (e.symm▸f)
lemma yF (h:Valid n K A C d) (s:SwapOK d r q)
  {u:Fin n} (b:u∈d.cover) (edge:d.owns u r=true):d.lam u r=r.val:=by
 have hr:=(h.2.2.1.1 _ _ s.edge).2;have L:=(h.2.2.2.2.2.1 u b).2.2.2 _ edge;simp only[LamOK,hr,↓reduceIte] at L;rcases L.2.1 with raw|⟨j,a,_,c⟩
 ·exact raw
 ·have m:j∈gatesOf d C .z r.val:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a,c⟩;rw[(dM h s).1] at m;contradiction
lemma uX (h:Valid n K A C d) (s:SwapOK d r q)
  {u:Fin n} (l:u∈d.cover) (t:u≠r) (c:u≠q)
  {v:Fin n} (edge:(aB d r q).owns u v=true):LamOK n C (aB d r q) u v:=by
 have a:d.owns u v=true:=by simpa[aB,c,t] using edge
 have L:=(h.2.2.2.2.2.1 u l).2.2.2 _ a;have p:r≠q:=(h.2.2.1.1 _ _ s.edge).1.ne;by_cases m:v=r
 ·subst v;simpa[LamOK,aB,c,p] using yF h s l a
 by_cases k:v=q
 ·subst v;have raw:d.lam u q=q.val:=by simpa[LamOK,s.outside] using L
  have o:IsCentred n C (aB d r q) q.val:=(aG _).2 (Finset.mem_insert_self ..);simpa[LamOK,aB,c,raw] using o
 by_cases b:v∈d.cover
 ·have e:v∈(aB d r q).cover:=Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨m,b⟩);simp only[LamOK,b,↓reduceIte] at L;simp only[LamOK,e,↓reduceIte];have i:(aB d r q).lam u v=d.lam u v:=by simp[aB,c]
  rw[i];refine⟨?_,?_,?_⟩
  ·rcases L.2.1 with raw|⟨j,f,raw,g⟩
   ·rw[raw];exact(aG _).2 e
   ·rw[raw];exact sZ h s b m j
     (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f,g⟩) (raw▸L.1)
  ·rcases L.2.1 with raw|⟨j,f,raw,g⟩
   ·exact Or.inl raw
   ·exact Or.inr ⟨j,f,raw,by simp[aB,g]⟩
  ·simpa[aB,k] using L.2.2
 ·have out:v∉(aB d r q).cover:=by simp[aB,k,b]
  simpa[LamOK,out,aB,c,k,b] using L
lemma cR (w:ℕ):IsOrTree n C ∅ {w} w:=by simp[IsOrTree,readsIn]
lemma tA (h:Valid n K A C d) (s:SwapOK d r q)
  {u:Fin n} (c:u∈d.cover) (b:u≠r) (a:u≠q):
  TermOK n C (aB d r q) u∧
  IsOrTree n C (gatesOf (aB d r q) C .z u.val) (zLeaves (aB d r q) u) ((aB d r q).zroot u)∧
  IsOrTree n C (gatesOf (aB d r q) C .o u.val) (oLeaves (aB d r q) u) ((aB d r q).oroot u)∧
  ∀v,(aB d r q).owns u v=true→LamOK n C (aB d r q) u v:=by
 obtain⟨dN,p,l,_⟩:=h.2.2.2.2.2.1 u c;have k:oLeaves (aB d r q) u=oLeaves d u:=by simp[oLeaves,aB,a,b]
 refine⟨?_,?_,?_,fun _=>uX h s c b a⟩
 ·obtain⟨j,g,bw,m,op,e⟩:=dN;have i:u.val≠r.val:=fun f=>b (Fin.ext f)
  exact⟨j,g,by simpa[aB,a] using bw,by simp[aB,m,i],op,by simpa[aB,a] using e⟩
 ·rw[cY .z (by decide),aBx h s];simpa[aB,a] using p
 ·rw[cY .o (by decide),k];simpa[aB,a] using l
lemma aB9 (h:Valid n K A C d) (s:SwapOK d r q):
  TermOK n C (aB d r q) q∧
  IsOrTree n C (gatesOf (aB d r q) C .z q.val) (zLeaves (aB d r q) q) ((aB d r q).zroot q)∧
  IsOrTree n C (gatesOf (aB d r q) C .o q.val) (oLeaves (aB d r q) q) ((aB d r q).oroot q)∧
  ∀v,(aB d r q).owns q v=true→LamOK n C (aB d r q) q v:=by
 have hr:=(h.2.2.1.1 _ _ s.edge).2;have e:=(h.2.2.1.1 _ _ s.edge).1.ne;have out (v:Fin n):d.owns q v=false:=by
  cases eq:d.owns q v
  ·rfl
  ·exact False.elim (s.outside (h.2.2.1.1 _ _ eq).2)
 have b (v:Fin n):(aB d r q).owns q v=true↔v=r:=by by_cases k:v=r<;>simp[aB,k,Ne.symm e,out]
 obtain⟨_,l,_,c⟩:=dM h s;refine⟨?_,?_,?_,?_⟩
 ·obtain⟨j,f,bw,i,op,a⟩:=(h.2.2.2.2.2.1 _ hr).1;refine⟨j,f,by simpa[aB] using bw,by simp[aB,i],op,?_⟩;simpa[aB,l,c,or_comm] using a
 ·rw[cY .z (by decide),aAe h s .z (by decide),aBx h s];simpa[zLeaves,aAd h s,aB] using(cR (n:=n) (C:=C) q.val)
 ·have g:oLeaves (aB d r q) q={r.val}:=by
   ext w;simp only[oLeaves,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,b,Finset.mem_singleton];simp[aB,eq_comm]
  rw[cY .o (by decide),aAe h s .o (by decide),g];simpa[aB] using(cR (n:=n) (C:=C) r.val)
 ·intro v edge;obtain rfl:=(b v).mp edge;simp[LamOK,aB,e]
lemma eM (h:Valid n K A C d) (s:SwapOK d r q):
  Valid n K A C (aB d r q):=by
 refine⟨h.1,aAb h s,xH h s,aCl h s,lD h s,?_,?_⟩
 ·intro u e;rcases Finset.mem_insert.mp e with rfl|b
  ·exact aB9 h s
  ·obtain⟨g,a⟩:=Finset.mem_erase.mp b;exact tA h s a g (fun c=>s.outside (c▸a))
 ·have f:topGates (aB d r q) C=topGates d C:=by
   ext j;simp only[topGates,Finset.mem_filter,mV]
  rw[f,aBf h s];exact h.2.2.2.2.2.2
end PEqualNP.MetaComplexity.NestedCover.Aj
namespace PEqualNP.MetaComplexity.NestedCover.A0
open PEqualNP.CircuitLowerBounds
open Aj (aB SwapOK)
open Am (OwnerPins aF eT)
variable {n : ℕ} {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)}
  {C D : Circuit} {d : NCCData n} {r p l : Fin n} {f w : ℕ ↪ ℕ} {j : ℕ}
structure Pins (n : ℕ) (C D : Circuit) (d : NCCData n)
    (r l : Fin n) (f w : ℕ ↪ ℕ) (j : ℕ) : Prop where
  range_eq : Finset.range D.gates.length = insert j ((Finset.range C.gates.length).map f)
  gap : ∀ k, f k ≠ j
  fixed : ∀ v : Fin n, w v.val = v.val
  align : ∀ k, w (n+k) = n+f k
  rb : ReadsBack n D
  output : D.output = w C.output
  op : ∀ k < C.gates.length, (gateAt D (f k)).op = (gateAt C k).op
  opNew : (gateAt D j).op = GateOp.or
  insNew : (gateAt D j).inputs = [w r.val,l.val] ∨
    (gateAt D j).inputs = [l.val,w r.val]
  insRetained : ∀ k < C.gates.length, d.role k = (.b,r.val) →
    (gateAt D (f k)).inputs =
      (gateAt C k).inputs.map (fun i => if i = r.val then n+j else w i)
  insOther : ∀ k < C.gates.length, d.role k ≠ (.b,r.val) →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map w
lemma rT (v:Valid n K A C d) (s:SwapOK d r p)
  {k mV} (c:k<C.gates.length) (e:mV≠ .top):
  d.role k≠(mV,p.val):=by
 intro a;rcases v.2.2.2.2.1 k c with hh|⟨t,ht,b,_⟩
 ·exact e ((congrArg Prod.fst a).symm.trans hh)
 ·exact s.outside ((Fin.ext (b.symm.trans (congrArg Prod.snd a)))▸ht)
lemma mW (v:Valid n K A C d) (s:SwapOK d r p)
  {k} (a:k<C.gates.length):
  (aB d r p).role k=(.b,p.val)↔d.role k=(.b,r.val):=by
 by_cases hr:d.role k=(.b,r.val)
 ·simp[aB,hr]
 ·simp[aB,hr,rT v s a (by decide:Kind.b≠ .top)]
lemma wH (v:Valid n K A C d) (s:SwapOK d r p)
  {k} (c:k<C.gates.length):(aB d r p).role k≠(.o,p.val):=by
 intro h;have a:d.role k=(.o,p.val):=by
  by_cases hr:d.role k=(.b,r.val)
  ·simp[aB,hr] at h
  ·simpa[aB,hr] using h
 exact rT v s c (by decide) a
lemma qX (v:Valid n K A C d) (s:SwapOK d r p)
  {k} (f:k<C.gates.length) (h:(aB d r p).role k=(.b,p.val)):
  (gateAt C k).inputs=[p.val,r.val]∨(gateAt C k).inputs=[r.val,p.val]:=by
 have g:p∈(aB d r p).cover:=Finset.mem_insert_self ..;have ev:=Aj.eM v s;obtain⟨i,_,bw,_,_,a⟩:=(ev.2.2.2.2.2.1 p g).1;have m:(aB d r p).bw p=n+k:=by
  rcases ev.2.2.2.2.1 k f with ht|⟨t,_,c,e⟩
  ·simp[h] at ht
  ·have l:t=p:=Fin.ext (c.symm.trans (congrArg Prod.snd h));subst t;exact e (congrArg Prod.fst h)
 have j:k=i:=by omega
 simpa[j,aB] using a
lemma yG (v:Valid n K A C d) (s:SwapOK d r p)
  (P:Pins n C D d r l f w j):OwnerPins n C D (aB d r p) p l f w j r.val:=by
 have e:r.val≠p.val:=fun h=>(v.2.2.1.1 _ _ s.edge).1.ne (Fin.ext h)
 refine⟨P.range_eq,P.gap,P.fixed,P.align,P.rb,P.output,P.op,P.opNew,P.insNew,?_,?_,?_⟩
 ·intro k a h;exact(wH v s a h).elim
 ·intro k a h _;rw[P.insRetained k a ((mW v s a).mp h)];simp only[aB,ite_true];rcases qX v s a h with b|c
  ·simp[b,Ne.symm e]
  ·simp[c,e,Ne.symm e]
 ·intro k a _ h;apply P.insOther k a;rcases h with h|h
  ·exact fun hr=>h ((mW v s a).mpr hr)
  ·exact(h (by simp[aB])).elim
lemma eM (v:Valid n K A C d) (s:SwapOK d r p)
  (P:Pins n C D d r l f w j)
  (iso:∀t,¬K.Adj l t)
  (ext:∀u t,K'.Adj u t↔K.Adj u t∨(u=p∧t=l)∨(u=l∧t=p)):
  Valid n K' A D (aF (aB d r p) p l f w j r.val):=by
 have a:r.val∈oLeaves (aB d r p) p:=Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp[aB]⟩,by simp[aB]⟩;exact eT (Aj.eM v s) (yG v s P) iso
  (Finset.mem_insert_self ..) ext (Or.inl a)
def wI (D:Circuit) (b:ℕ):Circuit:=
 {D with gates:=D.gates.modify b fun g=>{g with inputs:=g.inputs.reverse}}
@[simp] lemma flip_length (D : Circuit) (b : ℕ) :
 (wI D b).gates.length=D.gates.length:=List.length_modify ..
end PEqualNP.MetaComplexity.NestedCover.A0
namespace PEqualNP.MetaComplexity.NestedCover.Ad
open PEqualNP.CircuitLowerBounds Af Ac
variable {n : ℕ} {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)} {D P : Circuit}
    {d : NCCData n} {t p l : Fin n} {src j : ℕ} {g w : ℕ ↪ ℕ}
lemma yH (h:Valid n K A D d) (S:Trace n D d src)
  (ht:t∈d.cover) (swap:Aj.SwapOK d t p)
  (j:eL S t) (top:¬eG S) (q:∀u∈d.cover,¬jU S u):
  Z
   t d D = ∅ ∧src=t.val∧gH S (some (d.bw t-n)) src∧
   ∀c,bB D src c→ gH S c src→c=some (d.bw t-n):=by
 have r (u:Fin n):d.tie u≠some t:=by intro e;have i:=h.2.2.2.1 u t e;exact swap.outside ((swap.single u i.2)▸i.1)
 have a:zLeaves d t={t.val}:=by ext;simp[zLeaves,r]
 have tr:=bL h ht;have card:=An.gN tr;rw[a,Finset.card_singleton] at card;have empty:Z t d D = ∅ :=Finset.card_eq_zero.mp (by omega);have g:d.zroot t=t.val:=by
  have m:zLeaves d t={d.zroot t}:=by simpa only[empty,ite_true] using tr.2.2.2
  exact Finset.singleton_inj.mp (m.symm.trans a)
 have f {c} (b:zV d D t src c):c=some (d.bw t-n)∧src=t.val:=by
  rcases b with⟨k,o,_⟩|⟨b,hs⟩
  ·simp[empty] at o
  ·exact⟨b,hs.trans g⟩
 obtain⟨c,b,sel⟩:=(mS h S ht).mp j;obtain⟨rfl,hs⟩:=f b;exact⟨empty,hs,sel,fun _ l s=>(f (aB7 h S ht j top q l s)).1⟩
lemma aAf (h : Valid n K A D d) (sp : Splice n D P g w src (n+j))
    (lay : OneLayout n D P l g w j src) (ht : t ∈ d.cover)
    (swap : Aj.SwapOK d t p) (zm : eL (aE h sp) t)
    (top : ¬eG (aE h sp)) (no : ∀ u ∈ d.cover, ¬jU (aE h sp) u)
    (iso : ∀ v, ¬K.Adj l v)
    (ext : ∀ u v, K'.Adj u v ↔ K.Adj u v ∨ (u = p ∧ v = l) ∨ (u = l ∧ v = p)) :
    IsNestedCoverCircuit n K' A P := by
  obtain ⟨_,hs,sel,only⟩ := yH h (aE h sp) ht swap zm top no
  subst src
  have live : n+j ∈ (gateAt P (g (d.bw t - n))).inputs :=
    (show Ae.Sel P g t.val (n+j) (d.bw t - n) t.val from sel).2
  obtain ⟨b,hb,bw,role,_,_⟩ := dN h ht
  have ix : d.bw t - n = b := by omega
  have single {k} (hk : k < D.gates.length) (hr : d.role k = (.b,t.val)) :
      k = d.bw t - n := by
    rcases h.2.2.2.2.1 k hk with topK | ⟨u,_,eu,hu⟩
    · simp [hr] at topK
    · obtain rfl : u = t := Fin.ext (eu.symm.trans (congrArg Prod.snd hr))
      have hbw := hu (congrArg Prod.fst hr)
      omega
  have out : P.output = w D.output := by
    rcases (sp.output D.output).mp rfl with eq | ⟨e,_⟩
    · exact eq
    · exact (top (Or.inr e)).elim
  refine ⟨_, A0.eM (f := g) (w := w) (j := j) h swap ?_ iso ext⟩
  refine ⟨lay.range_eq,lay.gap,lay.fixed,sp.align,lay.rb,out,fun k _ => sp.op k,
    lay.opNew,lay.insNew,?_,?_⟩
  · intro k hk hr
    have liveK : n+j ∈ (gateAt P (g k)).inputs := (single hk hr).symm ▸ live
    rw [cH h sp hk]
    simp [liveK]
  · intro k hk hr
    apply sp.unchanged
    intro hf
    have a := fresh_actual sp hk hf
    have eq := only (some k) a ⟨rfl,hf⟩
    exact hr (((Option.some.inj eq).trans ix).symm ▸ role)
end PEqualNP.MetaComplexity.NestedCover.Ad
namespace PEqualNP.MetaComplexity.NestedCover.Ad
open PEqualNP.CircuitLowerBounds Ac
variable {n : ℕ} {D P : Circuit} {g w : ℕ ↪ ℕ} {src j : ℕ}
variable {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)} {d : NCCData n}
    {p l : Fin n}
variable (h : Valid n K A D d) (sp : Splice n D P g w src (n+j))
    (lay : OneLayout n D P l g w j src)
include lay in
lemma tB (live:zY D P g (n+j)) (iso:∀r,¬K.Adj l r)
  (ext:∀u v,K'.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p))
  (pos:¬eG (aE h sp)∧
    ((p∈d.cover∧(∀t∈d.cover,¬eL (aE h sp) t)∧(∀t∈d.cover,jU (aE h sp) t→t=p))∨
     (p
       ∉d.cover∧(∀t∈d.cover,¬jU (aE h sp) t)∧∃t∈d.cover,
       eL (aE h sp) t∧(∀s∈d.cover,eL (aE h sp) s→s=t)∧d.tie t=none∧∀r,d.owns t r=true↔r=p))):IsNestedCoverCircuit n K' A P:=by
 obtain⟨top,⟨a,c,e⟩|⟨a,b,t,ht,f,_,τ,owns⟩⟩:=pos
 ·exact yE h sp lay live a top c e iso ext
 ·exact aAf h sp lay ht ⟨a,(owns p).2 rfl,fun r hr=>(owns r).1 hr,τ⟩ f top b iso ext
end PEqualNP.MetaComplexity.NestedCover.Ad
namespace PEqualNP.MetaComplexity.NestedCover.Ad
open PEqualNP.CircuitLowerBounds Ac Af Ar
variable {n : ℕ} {D P : Circuit} {g w : ℕ ↪ ℕ} {src fresh : ℕ}
    {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)} {d : NCCData n} {l p : Fin n}
lemma qY {M:Sig d} (j:OwnerOK K d) (i:Macro K A p M)
  (h:p∉A):M.top∨∃t∈d.cover,M.z t∨M.o t:=by
 classical
 obtain top|⟨a,m,q⟩|⟨u,n,_,l⟩:=(i.output {p}).2 (.inl (Finset.mem_singleton_self p))
 ·exact .inl top
 ·exact(h ((Finset.mem_singleton.mp q)▸m)).elim
 let T:=d.cover.filter (M.b {p})
 obtain⟨t,ht,f⟩:=T.exists_min_image d.bw ⟨u,Finset.mem_filter.mpr ⟨n,l⟩⟩;obtain⟨ht,k⟩:=Finset.mem_filter.mp ht;refine .inr ⟨t,ht,?_⟩;have c {s} (hs:s∈d.cover) (g:M.b {p} s):¬d.bw s<d.bw t:=not_lt_of_ge (f _ (Finset.mem_filter.mpr ⟨hs,g⟩));obtain⟨y,v⟩:=(i.prod {p} t ht).1 k;rcases y with(tp|⟨s,hs,st,g⟩)|z
 ·rcases v with⟨r,e,x|⟨s,hs,w,g⟩⟩|o
  ·exact((j.1 _ _ e).1.ne ((Finset.mem_singleton.mp tp).trans (Finset.mem_singleton.mp x).symm)).elim
  ·exact(c hs g (M.part_lt e w)).elim
  ·exact .inr o
 ·exact(c hs g (M.tie_lt st)).elim
 ·exact .inl z
lemma iG {i} (m:Ae.sW n D P g src fresh i):
  P.output=fresh∨∃j<D.gates.length,fresh∈(gateAt P (g j)).inputs:=by
 induction m with
 | iT _ h=>exact h.elim
 | step _ _ _ _ ih=>exact ih
 | hit hj _ _ hs=>exact .inr ⟨_,hj,hs.2⟩
lemma aAg (h:Valid n K A D d) {α:Finset (Fin n)→Fin n→Bool}
  (b:Macro K A p (Ae.iF h P g w src fresh α)) (a:p∉A):
  P.output=fresh∨∃j<D.gates.length,fresh∈(gateAt P (g j)).inputs:=by
 obtain(m|out)|⟨t,ht,(m|sel)|(m|sel)⟩:=qY h.2.2.1 b a
 ·exact iG m
 ·exact .inl out
 ·exact iG m
 ·exact .inr ⟨_,(dL h ht).1.1,sel.2⟩
 ·exact iG m
 ·exact .inr ⟨_,(dL h ht).2.1,sel.2⟩
variable {j : ℕ}
lemma oR [DecidableRel K'.Adj]
  (h:Valid n K A (erase n P j src) d) (b:Av P l false j src)
  (rb:ReadsBack n P) (isoL:∀v,¬K.Adj l v) (r:l∉A) (k:p∉A)
  (f:∀a∈A,∀v,¬K.Adj a v) (m:K.CliqueFree 3)
  (ext:∀u v,K'.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p))
  (e:circuitFun n P=graphFun K' A):
  IsNestedCoverCircuit n K' A P:=by
 let D:=erase n P j src
 let g:=skip j
 let w:=skip (n+j)
 have bS:(gateAt P j).inputs=[w src,l.val]∨(gateAt P j).inputs=[l.val,w src]:=by dsimp only[w];rw[b.mapH];exact b.pair.symm
 have lay:OneLayout n D P l g w j src:=⟨lS b.real,fA _,fun v=>fixed v j,rb,b.op,bS⟩
 have c:Ae.bB n D P g w:=⟨rb,fun _ o=>(aS b.real).1 o,lay.fixed⟩
 have i:=Ae.xZ h c b.splice b.real lay.opNew bS isoL r ext e;have live:=aAg h i k
 let S:=aE h b.splice
 have pos:=qU h.2.1 h.2.2.1 h.2.2.2.1 f i k m
  (fun _ ht _ q=>rS h S ht q)
 exact tB h b.splice lay live isoL ext pos
end PEqualNP.MetaComplexity.NestedCover.Ad
namespace PEqualNP.MetaComplexity.NestedCover.Ag
open PEqualNP.CircuitLowerBounds
open Am
variable {n : ℕ}
def cA (w:ℕ ↪ ℕ) (x v:ℕ) (b:Bool):ℕ ↪ ℕ:=if b then w.trans (Equiv.swap (w x) v).toEmbedding else w
def bV:Option (Fin n)→Kind×ℕ
 | none=>(.top,0)
 | some t=>(.z,t.val)
def dY (w:ℕ ↪ ℕ) (x v:ℕ) (i:ℕ):ℕ:=if i=x then v else w i
noncomputable def aA (d:NCCData n) (p l:Fin n) (host:Option (Fin n))
  (mark:Fin n→Bool) (f w:ℕ ↪ ℕ) (i j x:ℕ):NCCData n where
 cover:=insert p d.cover
 owns t r:=if t=p then decide (r=l) else d.owns t r
 tie t:=if t=p then host else d.tie t
 role k:=if k=i then(.b,p.val) else if k=j then bV host
  else d.role (Function.invFun f k)
 bw t:=if t=p then n+i else w (d.bw t)
 zroot t:=if t=p then p.val else if host=some t then dY w x (n+j) (d.zroot t)
  else w (d.zroot t)
 oroot t:=if t=p then l.val else cA w x (n+j) (mark t) (d.oroot t)
 lam t r:=if t=p then r.val else cA w x (n+j) (mark t) (d.lam t r)
variable {C D : Circuit} {d : NCCData n} {p l : Fin n} {host : Option (Fin n)}
  {mark : Fin n → Bool} {f w : ℕ ↪ ℕ} {i j x : ℕ}
structure Pins (n : ℕ) (C D : Circuit) (d : NCCData n) (p l : Fin n)
    (host : Option (Fin n)) (mark : Fin n → Bool) (f w : ℕ ↪ ℕ) (i j x : ℕ) : Prop where
  range_eq : Finset.range D.gates.length = insert i (insert j ((Finset.range C.gates.length).map f))
  gapI : ∀ k, f k ≠ i
  gapJ : ∀ k, f k ≠ j
  ij : i ≠ j
  fixed : ∀ r : Fin n, w r.val = r.val
  align : ∀ k, w (n+k) = n + f k
  rb : ReadsBack n D
  output : D.output = if host = none then dY w x (n+j) C.output else w C.output
  op : ∀ k < C.gates.length, (gateAt D (f k)).op = (gateAt C k).op
  andOp : (gateAt D i).op = .and
  andIns : (gateAt D i).inputs = [p.val,l.val] ∨ (gateAt D i).inputs = [l.val,p.val]
  orOp : (gateAt D j).op = .or
  orIns : (gateAt D j).inputs = [w x,n+i] ∨ (gateAt D j).inputs = [n+i,w x]
  insTop : ∀ k < C.gates.length, (d.role k).1 = .top →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map (if host = none then dY w x (n+j) else ⇑w)
  insZ : ∀ k < C.gates.length, ∀ t : Fin n, d.role k = (.z,t.val) →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map (if host = some t then dY w x (n+j) else ⇑w)
  insO : ∀ k < C.gates.length, ∀ t : Fin n, d.role k = (.o,t.val) →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map (cA w x (n+j) (mark t))
  insB : ∀ k < C.gates.length, ∀ t : Fin n, d.role k = (.b,t.val) →
    let z := if host = some t then dY w x (n+j) (d.zroot t) else w (d.zroot t)
    let o := cA w x (n+j) (mark t) (d.oroot t)
    (gateAt D (f k)).inputs = [z,o] ∨ (gateAt D (f k)).inputs = [o,z]
structure Positions (n : ℕ) (C : Circuit) (d : NCCData n) (A : Finset (Fin n)) (p : Fin n)
    (host : Option (Fin n)) (mark : Fin n → Bool) (x : ℕ) : Prop where
  hostOwns : ∀ q, host = some q → d.owns q p = true
  atZ : ∀ q, host = some q → x ∈ zLeaves d q ∨ aM n (gatesOf d C .z q.val) x
  atTop : host = none → x ∈ topLeaves d A ∨ aM n (topGates d C) x
  hits : ∀ t, mark t = true → ∃ q, host = some q ∧ d.owns t q = true ∧ d.lam t q = x
  tiedRoot : ∀ t q, host = some q → d.tie q = some t → d.zroot q = x → mark t = true
lemma aCa (P:Pins n C D d p l host mark f w i j x) (v:ℕ):w v≠n+i:=by
 by_cases h:v<n
 ·have e:=P.fixed ⟨v,h⟩;change w v=v at e;omega
 ·obtain⟨k,rfl⟩:∃k,v=n+k:=⟨v-n,by omega⟩
  rw[P.align];have:=P.gapI k;omega
lemma aAh (P:Pins n C D d p l host mark f w i j x) (v:ℕ):w v≠n+j:=by
 by_cases h:v<n
 ·have e:=P.fixed ⟨v,h⟩;change w v=v at e;omega
 ·obtain⟨k,rfl⟩:∃k,v=n+k:=⟨v-n,by omega⟩
  rw[P.align];have:=P.gapJ k;omega
lemma lE (P:Pins n C D d p l host mark f w i j x) (v:ℕ) (b:Bool):
  cA w x (n+j) b v=(if b=true∧v=x then n+j else w v):=by
 cases b
 ·simp[cA]
 ·by_cases a:v=x
  ·subst v;simp[cA]
  ·have c:w v≠w x:=fun e=>a (w.injective e)
   simp[cA,a,Equiv.swap_apply_of_ne_of_ne c (aAh P v)]
lemma fW (P:Pins n C D d p l host mark f w i j x) (k:ℕ):
  (aA d p l host mark f w i j x).role (f k)=d.role k:=by
 simp[aA,P.gapI k,P.gapJ k,Function.leftInverse_invFun f.injective k]
lemma jW (P:Pins n C D d p l host mark f w i j x) {k} (a:k<C.gates.length):
 f
  k<D.gates.length:=Finset.mem_range.mp (P.range_eq▸Finset.mem_insert_of_mem
  (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨_,Finset.mem_range.mpr a,rfl⟩)))
lemma aCb (P:Pins n C D d p l host mark f w i j x):i<D.gates.length:=Finset.mem_range.mp (P.range_eq▸Finset.mem_insert_self ..)
lemma aAi (P:Pins n C D d p l host mark f w i j x):j<D.gates.length:=Finset.mem_range.mp (P.range_eq▸Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
end PEqualNP.MetaComplexity.NestedCover.Ag
namespace PEqualNP.MetaComplexity.NestedCover.Ag
open PEqualNP.CircuitLowerBounds Ad Af
variable {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C : Circuit} {d : NCCData n} {p : Fin n} {x : ℕ}
structure Route (A : Finset (Fin n)) (p : Fin n) (S : Trace n C d x)
    (host : Option (Fin n)) (mark : Fin n → Bool) : Prop where
  pos : Positions n C d A p host mark x
  top : gV S ↔ host = none
  z : ∀ t ∈ d.cover, oX S t ↔ host = some t
  o : ∀ t ∈ d.cover, fE S t ↔ mark t = true
lemma xI {G L w} (h:fQ n G L w):
  w∈L∨Am.aM n G w:=by
 rcases h with h|⟨k,a,rfl⟩
 ·exact Or.inl h
 ·exact Or.inr (by simp[Am.aM,a])
lemma wJ (v:Valid n K A C d) (iso:∀a∈A,∀r,¬K.Adj a r)
  (S:Trace n C d x) (top:eG S):
  Route A p S none (fun _=>false):=by
 have h:=(qG v S).1 top;obtain⟨c,e,_⟩:=h;have b:=cG v.2.2.2.2.2.2 e;refine⟨⟨by simp,by simp,fun _=>xI b,by simp,by simp⟩,⟨fun _=>rfl,fun _=>(qG v S).1 top⟩,?_,?_⟩
 ·intro t ht;simp only[reduceCtorEq,iff_false];rintro⟨_,g,_⟩;exact lW v iso b ht (cG (bL v ht) g)
 ·intro t ht;simp only[Bool.false_eq_true,iff_false];rintro⟨_,f,_⟩;exact qF v iso b (cG (cT v ht) f)
noncomputable def nK (S:Trace n C d x) (t:Fin n):Bool:=by classical exact decide (t∈d.cover∧fE S t)
lemma aAj (v:Valid n K A C d) (iso:∀a∈A,∀r,¬K.Adj a r)
  (S:Trace n C d x) {q:Fin n} (f:q∈d.cover) (i:eL S q)
  (owns:d.owns q p=true)
  (tied:∀s,d.tie q=some s→d.zroot q=x→fE S s):
  Route A p S (some q) (nK S):=by
 classical
 have j:=mT v S f i;have m:=(mS v S f).mp i;have b (t:Fin n):nK S t=true↔t∈d.cover∧fE S t:=by simp[nK]
 refine⟨⟨?_,?_,by simp,?_,?_⟩,?_,?_,?_⟩
 ·intro t h;cases h;exact owns
 ·intro t h;cases h;exact xI j
 ·intro t k;obtain⟨ht,c,g,_⟩:=(b _).mp k;have e:=mQ v f j (cG (cT v ht) g);exact⟨q,rfl,e.1,e.2.1⟩
 ·intro t r hh e hr;cases hh
  exact(b _).mpr ⟨(v.2.2.1.1 _ _ (v.2.2.2.1 _ _ e).2).2,tied _ e hr⟩
 ·simp only[reduceCtorEq,iff_false];rintro⟨_,l,_⟩;exact lW v iso (cG v.2.2.2.2.2.2 l) f j
 ·intro t ht;constructor
  ·intro h;exact congrArg some (rS v S f ht i ((mS v S ht).2 h))
  ·intro h;cases h;exact m
 ·intro t ht;rw[b];simp[ht]
end PEqualNP.MetaComplexity.NestedCover.Ag
namespace PEqualNP.MetaComplexity.NestedCover.Ad
open PEqualNP.CircuitLowerBounds Af Ac
variable {n : ℕ} {D P : Circuit} {g w : ℕ ↪ ℕ} {src fresh j : ℕ}
    {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {d : NCCData n} {t : Fin n}
lemma cU (S:Trace n D d src)
  {G L:Finset ℕ} {a:ℕ} {sink c:Option ℕ}
  (tr:IsOrTree n D G L a) (p:gA D G a sink src c):
  gH S c src↔jV S G a sink:=by
 constructor
 ·exact fun h=>⟨c,p,h⟩
 ·rintro⟨u,q,h⟩;exact oE tr q p▸h
noncomputable def cV (w:ℕ ↪ ℕ) (src fresh:ℕ) (a:Prop) (i:ℕ):ℕ:=
 open Classical in
 if a∧i=src then fresh else w i
variable (h : Valid n K A D d) (sp : Splice n D P g w src fresh)
lemma nL {G L:Finset ℕ} {a:ℕ} {sink:Option ℕ} {i:ℕ}
  (tr:IsOrTree n D G L a) (p:gA D G a sink i (some j)):
  (if i=src∧fresh∈(gateAt P (g j)).inputs then fresh else w i)=
    cV w src fresh (jV (aE h sp) G a sink) i:=by
 classical
 by_cases e:i=src
 ·subst i;have hs:fresh∈(gateAt P (g j)).inputs↔jV (aE h sp) G a sink:=
   (and_iff_right rfl).symm.trans (cU (aE h sp) tr p)
  simp only[cV,and_true,true_and,hs]
 ·simp[cV,e]
lemma lY {G L:Finset ℕ} {a:ℕ} {sink:Option ℕ}
  (tr:IsOrTree n D G L a) (d:j<D.gates.length) (b:j∈G):
  (gateAt P (g j)).inputs=
    (gateAt D j).inputs.map (cV w src fresh (jV (aE h sp) G a sink)):=by
 rw[cH h sp d];apply List.map_congr_left;intro i c;exact nL h sp tr (Or.inl ⟨j,b,rfl,c⟩)
include h in
lemma nM (g:j<D.gates.length) {k:Kind}
  (a:d.role j=(k,t.val)) (i:k≠ .top):
  t∈d.cover∧(k= .b→d.bw t=n+j):=by
 obtain e|⟨u,l,tP,c⟩:=h.2.2.2.2.1 j g
 ·exact(i ((congrArg Prod.fst a).symm.trans e)).elim
 ·have e:t=u:=Fin.ext ((congrArg Prod.snd a).symm.trans tP);subst u;exact⟨l,fun f=>c ((congrArg Prod.fst a).trans f)⟩
lemma yI (a:j<D.gates.length) (role:(d.role j).1= .top):
  (gateAt P (g j)).inputs=
    (gateAt D j).inputs.map (cV w src fresh (gV (aE h sp))):=
 lY h sp h.2.2.2.2.2.2 a (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a,role⟩)
lemma aBg (a:j<D.gates.length) (role:d.role j=(.z,t.val)):
  (gateAt P (g j)).inputs=
    (gateAt D j).inputs.map (cV w src fresh (oX (aE h sp) t)):=
 lY h sp (bL h (nM h a role (by decide)).1) a
  (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a,role⟩)
lemma aBh (a:j<D.gates.length) (role:d.role j=(.o,t.val)):
  (gateAt P (g j)).inputs=
    (gateAt D j).inputs.map (cV w src fresh (fE (aE h sp) t)):=
 lY h sp (cT h (nM h a role (by decide)).1) a
  (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a,role⟩)
lemma aBi (i:j<D.gates.length) (role:d.role j=(.b,t.val)):
  let z:=cV w src fresh (oX (aE h sp) t) (d.zroot t)
  let o:=cV w src fresh (fE (aE h sp) t) (d.oroot t)
  (gateAt P (g j)).inputs=[z,o]∨(gateAt P (g j)).inputs=[o,z]:=by
 obtain⟨ht,a⟩:=nM h i role (by decide);have a:=a rfl;obtain⟨k,_,p,_,_,c⟩:=dN h ht;have e:k=j:=Nat.add_left_cancel (p.symm.trans a);subst k;have f:some j=some (d.bw t-n):=by simp[a]
 have m:=nL h sp (bL h ht) (Or.inr ⟨f,rfl⟩);have l:=nL h sp (cT h ht) (Or.inr ⟨f,rfl⟩);dsimp only;rw[cH h sp i];rcases c with c|c
 ·left;simp only[c,List.map_cons,List.map_nil,m,l]
 ·right;simp only[c,List.map_cons,List.map_nil,m,l]
lemma tC:P.output=cV w src fresh (gV (aE h sp)) D.output:=by
 classical
 have hs:P.output=fresh↔gV (aE h sp)∧D.output=src:=by
  constructor
  ·intro b;have e:D.output=src:=(aE h sp).sourceTop b;exact⟨(cU (aE h sp) h.2.2.2.2.2.2 (Or.inr ⟨rfl,e.symm⟩)).mp b,e⟩
  ·rintro⟨d,e⟩;exact(cU (aE h sp) h.2.2.2.2.2.2 (Or.inr ⟨rfl,e.symm⟩)).mpr d
 rcases (sp.output D.output).mp rfl with a|⟨a,_⟩
 ·have f:P.output≠fresh:=a▸sp.hole D.output;rw[cV,ite_eq_right (fun c=>f (hs.mpr c))];exact a
 ·rw[cV,ite_eq_left (hs.mp a)];exact a
end PEqualNP.MetaComplexity.NestedCover.Ad
namespace PEqualNP.MetaComplexity.NestedCover.Ag
open PEqualNP.CircuitLowerBounds Ac
variable {n : ℕ} {C D : Circuit} {d : NCCData n} {p l : Fin n}
    {host : Option (Fin n)} {mark : Fin n → Bool} {f w : ℕ ↪ ℕ} {i j x : ℕ}
lemma oS {v:ℕ} (hole:∀u,w u≠v) (u:ℕ) (b:Bool):
  cA w x v b u=(if b=true∧u=x then v else w u):=by
 cases b
 ·simp[cA]
 ·by_cases a:u=x
  ·subst u;simp[cA]
  ·have c:w u≠w x:=fun e=>a (w.injective e)
   simp[cA,a,Equiv.swap_apply_of_ne_of_ne c (hole u)]
end PEqualNP.MetaComplexity.NestedCover.Ag
namespace PEqualNP.MetaComplexity.NestedCover.Ag
open PEqualNP.CircuitLowerBounds Am
variable {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C D : Circuit} {d : NCCData n} {p l : Fin n} {host : Option (Fin n)}
    {mark : Fin n → Bool} {f w : ℕ ↪ ℕ} {i j x : ℕ}
lemma kE (P:Pins n C D d p l host mark f w i j x)
  (Q:Kind×ℕ→Prop) [DecidablePred Q] (a:¬Q (.b,p.val)):
  (Finset.range D.gates.length).filter (fun k=>Q ((aA d p l host mark f w i j x).role k))=
    (if Q (bV host) then insert j else id)
      (((Finset.range C.gates.length).filter (fun k=>Q (d.role k))).map f):=by
 classical
 have g (k):(aA d p l host mark f w i j x).role (f k)=d.role k:=fW P _;have c:(aA d p l host mark f w i j x).role i=(.b,p.val):=by simp[aA]
 have e:(aA d p l host mark f w i j x).role j=bV host:=by simp[aA,Ne.symm P.ij]
 rw[P.range_eq,Finset.filter_insert,Finset.filter_insert,Finset.filter_map];simp only[Function.comp_def,g,c,e,a,ite_false]
 split_ifs<;>rfl
lemma rU (P:Pins n C D d p l host mark f w i j x) {G L:Finset ℕ}:
  j∉G.map f∧n+j∉L.map w∧n+i∉L.map w∧¬aM n (G.map f) (n+i)∧n+i≠n+j:=by
 refine⟨?_,?_,?_,?_,by have:=P.ij;omega⟩
 ·rintro h;obtain⟨_,_,e⟩:=Finset.mem_map.mp h;exact P.gapJ _ e
 ·rintro h;obtain⟨_,_,e⟩:=Finset.mem_map.mp h;exact aAh P _ e
 ·rintro h;obtain⟨_,_,e⟩:=Finset.mem_map.mp h;exact aCa P _ e
 ·rintro⟨_,a⟩;simp only[Nat.add_sub_cancel_left] at a;obtain⟨_,_,e⟩:=Finset.mem_map.mp a;exact P.gapI _ e
lemma qK (t:Fin n):
  bV host=(.z,t.val)↔host=some t:=by
 cases host<;>simp[bV,Fin.val_inj]
lemma tD:(bV host).1= .top↔host=none:=by cases host<;>simp[bV]
lemma aAk (v:Valid n K A C d) (P:Pins n C D d p l host mark f w i j x)
  (pos:Positions n C d A p host mark x) (y:p∉d.cover) {t} (ht:t∈d.cover):
  IsOrTree n D (gatesOf (aA d p l host mark f w i j x) D .z t.val)
   ((if host=some t then insert (n+i) else id) ((zLeaves d t).map w)) ((aA d p l host mark f w i j x).zroot t):=by
 have h:t≠p:=fun c=>y (c▸ht)
 have g:gatesOf (aA d p l host mark f w i j x) D .z t.val=
   (if host=some t then insert j else id) ((gatesOf d C .z t.val).map f):=by
  simpa[gatesOf,qK] using kE P (· =(.z,t.val)) (by simp)
 rw[g];obtain⟨_,m,_,_⟩:=v.2.2.2.2.2.1 _ ht;by_cases b:host=some t
 ·simp only[b,ite_true,eq_self,aA,h,ite_false,dY];obtain⟨o,q,r,s,u⟩:=rU (G:=gatesOf d C .z t.val) (L:=zLeaves d t) P;apply gK m f w (fun k _=>P.align k) (pos.atZ _ b) o q r s u
  ·intro k a;exact P.op _ (Finset.mem_range.mp (Finset.mem_filter.mp a).1)
  ·intro k a;obtain⟨e,c⟩:=Finset.mem_filter.mp a;rw[P.insZ _ (Finset.mem_range.mp e) t c,ite_eq_left b];rfl
  ·exact P.orOp
  ·exact P.orIns
 ·simp only[b,ite_false,id_eq,aA,h];apply aX.mp (fV (aX.mpr m) f w (fun k _=>P.align k) _ _)
  ·intro k a;exact P.op _ (Finset.mem_range.mp (Finset.mem_filter.mp a).1)
  ·intro k a;obtain⟨e,c⟩:=Finset.mem_filter.mp a;simpa[b] using P.insZ _ (Finset.mem_range.mp e) t c
lemma cZ (v:Valid n K A C d) (P:Pins n C D d p l host mark f w i j x)
  (pos:Positions n C d A p host mark x):
  IsOrTree n D (topGates (aA d p l host mark f w i j x) D)
   ((if host=none then insert (n+i) else id) ((topLeaves d A).map w)) D.output:=by
 have g:topGates (aA d p l host mark f w i j x) D =(if host=none then insert j else id) ((topGates d C).map f):=by simpa[topGates,tD] using kE P (·.1= .top) (by simp)
 rw[g,P.output];have h:=v.2.2.2.2.2.2;by_cases b:host=none
 ·simp only[b,ite_true,eq_self,dY];obtain⟨m,o,q,r,s⟩:=rU (G:=topGates d C) (L:=topLeaves d A) P;apply gK h f w (fun k _=>P.align k) (pos.atTop b) m o q r s
  ·intro k a;exact P.op _ (Finset.mem_range.mp (Finset.mem_filter.mp a).1)
  ·intro k a;obtain⟨e,c⟩:=Finset.mem_filter.mp a;rw[P.insTop _ (Finset.mem_range.mp e) c,ite_eq_left b];rfl
  ·exact P.orOp
  ·exact P.orIns
 ·simp only[b,ite_false,id_eq];apply aX.mp (fV (aX.mpr h) f w (fun k _=>P.align k) _ _)
  ·intro k a;exact P.op _ (Finset.mem_range.mp (Finset.mem_filter.mp a).1)
  ·intro k a;obtain⟨e,c⟩:=Finset.mem_filter.mp a;simpa[b] using P.insTop _ (Finset.mem_range.mp e) c
lemma rV (P:Pins n C D d p l host mark f w i j x) (t:Fin n):
  gatesOf (aA d p l host mark f w i j x) D .o t.val=(gatesOf d C .o t.val).map f:=by
 have h:bV host≠(.o,t.val):=by cases host<;>simp[bV]
 simpa[gatesOf,h] using kE P (· =(.o,t.val)) (by simp)
lemma qZ {t:Fin n} (a:t≠p):
  oLeaves (aA d p l host mark f w i j x) t=(oLeaves d t).map (cA w x (n+j) (mark t)):=by
 ext v;simp[oLeaves,aA,a]
lemma aAl (v:Valid n K A C d) (P:Pins n C D d p l host mark f w i j x)
  (pos:Positions n C d A p host mark x) (m:p∉d.cover) {t} (ht:t∈d.cover):
  IsOrTree n D (gatesOf (aA d p l host mark f w i j x) D .o t.val) (oLeaves (aA d p l host mark f w i j x) t) ((aA d p l host mark f w i j x).oroot t):=by
 have g:t≠p:=fun a=>m (a▸ht)
 obtain⟨_,_,h,_⟩:=v.2.2.2.2.2.1 _ ht;rw[rV P,qZ g];simp only[aA,g,ite_false];apply aX.mp (fV (aX.mpr h) f (cA w x (n+j) (mark t)) _ _ _)
 ·intro k b;rw[lE P,←P.align];apply ite_eq_right;rintro⟨c,a⟩;obtain⟨q,_,e,r⟩:=pos.hits t c;have hh:x∈oLeaves d t:=Finset.mem_image.mpr ⟨q,
   Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩,r⟩
  exact(h.2.1 x hh).1 (by rw[←a];simpa using b)
 ·intro k b;exact P.op _ (Finset.mem_range.mp (Finset.mem_filter.mp b).1)
 ·intro k b;obtain⟨c,a⟩:=Finset.mem_filter.mp b;exact P.insO _ (Finset.mem_range.mp c) t a
lemma lF (v:Valid n K A C d) (f:p∉d.cover)
  (k:Kind) (h:k≠ .top):gatesOf d C k p.val= ∅ :=by
 apply Finset.eq_empty_iff_forall_notMem.mpr;intro g b;obtain⟨c,a⟩:=Finset.mem_filter.mp b;rcases v.2.2.2.2.1 g (Finset.mem_range.mp c) with ht|⟨t,ht,e,_⟩
 ·exact h (by simpa[a] using ht)
 ·exact f ((Fin.ext (show t.val=p.val by simpa[a] using e.symm))▸ht)
lemma uY (v:Valid n K A C d) (P:Pins n C D d p l host mark f w i j x)
  (pos:Positions n C d A p host mark x) (a:p∉d.cover)
  (g:zLeaves (aA d p l host mark f w i j x) p={p.val}):
  IsOrTree n D (gatesOf (aA d p l host mark f w i j x) D .z p.val) (zLeaves (aA d p l host mark f w i j x) p) ((aA d p l host mark f w i j x).zroot p)∧
  IsOrTree n D (gatesOf (aA d p l host mark f w i j x) D .o p.val) (oLeaves (aA d p l host mark f w i j x) p) ((aA d p l host mark f w i j x).oroot p):=by
 have c:host≠some p:=fun h=>a (v.2.2.1.1 _ _ (pos.hostOwns _ h)).2
 have b:gatesOf (aA d p l host mark f w i j x) D .z p.val= ∅ :=by
  simpa[gatesOf,qK,c,show
   ((Finset.range C.gates.length).filter fun k=>d.role k=(.z,p.val))= ∅
     from lF v a _ (by decide)] using kE P (· =(.z,p.val)) (by simp)
 have e:oLeaves (aA d p l host mark f w i j x) p={l.val}:=by ext v;simp[oLeaves,aA,eq_comm]
 rw[b,g,rV P,lF v a .o (by decide),e];simp[IsOrTree,readsIn,aA]
lemma aBj (P:Pins n C D d p l host mark f w i j x):TermOK n D (aA d p l host mark f w i j x) p:=by exact⟨i,aCb P,by simp[aA],by simp[aA],P.andOp,by simpa[aA] using P.andIns⟩
lemma aBk (P:Pins n C D d p l host mark f w i j x) {t}
  (b:t≠p) (ht:TermOK n C d t):TermOK n D (aA d p l host mark f w i j x) t:=by
 obtain⟨k,a,e,hr,c,_⟩:=ht;exact⟨f k,jW P a,by simp[aA,b,e,P.align],(fW P _).trans hr,(P.op _ a).trans c,by simpa[aA,b] using P.insB _ a t hr⟩
lemma lD (v:Valid n K A C d) (P:Pins n C D d p l host mark f w i j x)
  (pos:Positions n C d A p host mark x) (o:p∉d.cover):RolesOK n D (aA d p l host mark f w i j x):=by
 intro k m;have a:=P.range_eq▸Finset.mem_range.mpr m;rcases Finset.mem_insert.mp a with e|a
 ·subst k;exact Or.inr ⟨p,by simp[aA],by simp[aA],by simp[aA]⟩
 rcases Finset.mem_insert.mp a with e|a
 ·subst k
  cases hh:host with
  | none=>exact Or.inl (by simp[aA,Ne.symm P.ij,bV])
  | some q=>
    have r:=(v.2.2.1.1 _ _ (pos.hostOwns _ hh)).2;exact Or.inr ⟨q,Finset.mem_insert_of_mem r,by simp[aA,Ne.symm P.ij,bV],by simp[aA,Ne.symm P.ij,bV]⟩
 ·obtain⟨k,c,rfl⟩:=Finset.mem_map.mp a;rw[fW P];rcases v.2.2.2.2.1 k (Finset.mem_range.mp c) with h|⟨t,ht,e,g⟩
  ·exact Or.inl h
  ·have s:t≠p:=fun h=>o (h▸ht)
   exact Or.inr ⟨_,Finset.mem_insert_of_mem ht,e,fun b=>by simp[aA,s,g b,P.align]⟩
end PEqualNP.MetaComplexity.NestedCover.Ag
namespace PEqualNP.MetaComplexity.NestedCover.Ag
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C : Circuit} {d d' : NCCData n} {p l : Fin n}
lemma iH
  (a:IsMinCover K d.cover)
  (outside:∀T,IsMinCover K T→p∉T)
  (iso:∀r,¬K.Adj l r)
  (ext:∀u v,K'.Adj u v↔
    K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p)):
  IsMinCover K' (insert p d.cover):=by
 constructor
 ·intro u v h;rcases (ext u v).mp h with h|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  ·exact(a.1 h).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
  ·exact Or.inl (Finset.mem_insert_self _ _)
  ·exact Or.inr (Finset.mem_insert_self _ _)
 ·intro S f;have g:K'.Adj p l:=(ext p l).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩));rw[Finset.card_insert_of_notMem (outside _ a)];by_cases hl:l∈S
  ·have b:K.IsVertexCover ((S.erase l:Finset (Fin n)):Set (Fin n)):=by
    intro u v e;have o:u≠l:=by rintro rfl;exact iso _ e
    have q:v≠l:=by rintro rfl;exact iso _ e.symm
    simpa[Finset.mem_erase,o,q] using f ((ext u v).mpr (Or.inl e))
   have c:=a.2 _ b;rw[Finset.card_erase_of_mem hl] at c;have m:=Finset.card_pos.mpr ⟨l,hl⟩;omega
  ·have k:p∈S:=(f g).resolve_right hl;have b:K.IsVertexCover (S:Set (Fin n)):=by
    intro u v e;exact f ((ext u v).mpr (Or.inl e))
   have c:=a.2 _ b;have s:S.card≠d.cover.card:=by intro j;apply outside S _ k;exact⟨b,fun T i=>j.trans_le (a.2 T i)⟩
   omega
lemma iS
  (a:OwnerOK K d) (o:p∉d.cover)
  (iso:∀r,¬K.Adj l r)
  (ext:∀u v,K'.Adj u v↔
    K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p))
  (f:d'.cover=insert p d.cover)
  (owns:∀u v,d'.owns u v=(if u=p then decide (v=l) else d.owns u v)):
  OwnerOK K' d':=by
 have c:K'.Adj p l:=(ext p l).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩));have g:p≠l:=by rintro rfl;exact K'.loopless.irrefl _ c
 have j (u v) (h:K.Adj u v):d'.owns u v=d.owns u v:=by
  by_cases i:u=p
  ·subst u;have k:v≠l:=by rintro rfl;exact iso _ h.symm
   have n:d.owns p v=false:=by
    cases e:d.owns p v
    ·rfl
    ·exact False.elim (o (a.1 _ _ e).2)
   simp[owns,k,n]
  ·simp[owns,i]
 have hl:d.owns l p=false:=by
  cases e:d.owns l p
  ·rfl
  ·exact False.elim (iso _ (a.1 _ _ e).1)
 constructor
 ·intro u v h;by_cases i:u=p
  ·subst u;have k:v=l:=by simpa[owns] using h
   subst v;exact⟨c,f▸Finset.mem_insert_self _ _⟩
  ·obtain⟨b,m⟩:=a.1 _ _ (by simpa[owns,i] using h);exact⟨(ext _ _).mpr (Or.inl b),f▸Finset.mem_insert_of_mem m⟩
 ·intro u v h;rcases (ext u v).mp h with b|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  ·simpa[j _ _ b,j _ _ b.symm] using a.2 _ _ b
  ·simp[owns,g.symm,hl]
  ·simp[owns,g.symm,hl]
lemma kO
  {host:Option (Fin n)}
  (a:OwnerOK K d) (c:TieOK d) (i:p∉d.cover)
  (hostOwns:∀q,host=some q→d.owns q p=true)
  (f:d'.cover=insert p d.cover)
  (owns:∀u v,d'.owns u v=(if u=p then decide (v=l) else d.owns u v))
  (tie:∀u,d'.tie u=if u=p then host else d.tie u):
  TieOK d':=by
 intro u v h;have b (r s) (e:d.owns r s=true):d'.owns r s=true:=by
  have hr:r≠p:=by rintro rfl;exact i (a.1 _ _ e).2
  simpa[owns,hr] using e
 by_cases j:u=p
 ·subst u;exact⟨f▸Finset.mem_insert_self _ _,b _ _
   (hostOwns _ (by simpa[tie] using h))⟩
 ·obtain⟨g,e⟩:=c _ _ (by simpa[tie,j] using h);exact⟨f▸Finset.mem_insert_of_mem g,b _ _ e⟩
variable {D : Circuit} {host : Option (Fin n)} {mark : Fin n → Bool}
    {f w : ℕ ↪ ℕ} {i j x : ℕ}
lemma aCc
  (v:Valid n K A C d) (pos:Positions n C d A p host mark x)
  (outside:∀T,IsMinCover K T→p∉T)
  (iso:∀r,¬K.Adj l r)
  (ext:∀u v,K'.Adj u v↔
    K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p)):
  IsMinCover K' (aA d p l host mark f w i j x).cover∧OwnerOK K' (aA d p l host mark f w i j x)∧TieOK (aA d p l host mark f w i j x):=
 ⟨iH v.2.1 outside iso ext,
   iS v.2.2.1 (outside _ v.2.1) iso ext rfl (fun _ _=>rfl),
   kO v.2.2.1 v.2.2.2.1 (outside _ v.2.1) pos.hostOwns
    rfl (fun _ _=>rfl) (fun _=>rfl)⟩
lemma fX (k:p∉d.cover) (h:Option (Fin n)):
  (((aA d p l host mark f w i j x).cover.filter (fun t=>(aA d p l host mark f w i j x).tie t=h)).image (aA d p l host mark f w i j x).bw)=
   (if host=h then insert (n+i) else id)
     (((d.cover.filter (fun t=>d.tie t=h)).image d.bw).map w):=by
 have b:
   ((d.cover.filter (fun t=>(aA d p l host mark f w i j x).tie t=h)).image (aA d p l host mark f w i j x).bw)=
     (((d.cover.filter (fun t=>d.tie t=h)).image d.bw).map w):=by
  ext v;simp only[Finset.mem_image,Finset.mem_map,Finset.mem_filter];constructor
  ·rintro⟨t,⟨ht,e⟩,rfl⟩;have a:t≠p:=by rintro rfl;exact k ht
   refine⟨d.bw t,⟨t,⟨ht,?_⟩,rfl⟩,?_⟩
   ·simpa[aA,a] using e
   ·simp[aA,a]
  ·rintro⟨v,⟨t,⟨ht,e⟩,rfl⟩,rfl⟩;have a:t≠p:=by rintro rfl;exact k ht
   exact⟨t,⟨ht,by simp[aA,a,e]⟩,by simp[aA,a]⟩
 conv_lhs=>rw[show(aA d p l host mark f w i j x).cover=insert p d.cover from rfl]
 rw[Finset.filter_insert];have c:(aA d p l host mark f w i j x).tie p=host:=by simp[aA]
 have g:(aA d p l host mark f w i j x).bw p=n+i:=by simp[aA]
 rw[c];by_cases hh:host=h
 ·rw[ite_eq_left hh,ite_eq_left hh,Finset.image_insert,g,b]
 ·rw[ite_eq_right hh,ite_eq_right hh,id_eq,b]
lemma iN (P:Pins n C D d p l host mark f w i j x)
  (a:p∉d.cover) (t:Fin n):
  zLeaves (aA d p l host mark f w i j x) t=(if host=some t then insert (n+i) else id) ((zLeaves d t).map w):=by
 unfold zLeaves;rw[fX a,Finset.map_insert,P.fixed];by_cases ht:host=some t<;>simp[ht,Finset.insert_comm]
lemma eN
  (P:Pins n C D d p l host mark f w i j x)
  (pos:Positions n C d A p host mark x)
  (a:OwnerOK K d) (c:TieOK d) (g:p∉d.cover):
  zLeaves (aA d p l host mark f w i j x) p={p.val}:=by
 have e:host≠some p:=fun h=>g (a.1 _ _ (pos.hostOwns _ h)).2
 have b:(d.cover.filter fun t=>d.tie t=some p)= ∅ :=by apply Finset.eq_empty_iff_forall_notMem.mpr;intro t ht;exact g (a.1 _ _ (c _ _ (Finset.mem_filter.mp ht).2).2).2
 rw[iN P g,ite_eq_right e,id_eq];simp[zLeaves,b,P.fixed]
lemma mX
  (P:Pins n C D d p l host mark f w i j x) (b:p∉d.cover):
  topLeaves (aA d p l host mark f w i j x) A=(if host=none then insert (n+i) else id) ((topLeaves d A).map w):=by
 have a:(A.image Fin.val).map w=A.image Fin.val:=by ext v;simp[P.fixed]
 unfold topLeaves;rw[fX b,Finset.map_union,a];by_cases h:host=none<;>simp[h,Finset.union_insert]
end PEqualNP.MetaComplexity.NestedCover.Ag
namespace PEqualNP.MetaComplexity.NestedCover.Ag
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
  {C D : Circuit} {d : NCCData n} {p l : Fin n} {host : Option (Fin n)}
  {mark : Fin n → Bool} {f w : ℕ ↪ ℕ} {i j x : ℕ}
lemma aAm (P:Pins n C D d p l host mark f w i j x) {q:Fin n}
  (a:host=some q):(aA d p l host mark f w i j x).role j=(.z,q.val):=by
 simp[aA,P.ij.symm,a,bV]
lemma rW (P:Pins n C D d p l host mark f w i j x) {q:Fin n}
  (b:host=some q) (a:IsCentred n D (aA d p l host mark f w i j x) (w x)):
  IsCentred n D (aA d p l host mark f w i j x) (n+j):=by
 apply(aR P.rb (aAi P)).2;refine⟨by rw[aAm P b],w x,?_,a⟩;rcases P.orIns with e|e<;>rw[e]<;>simp
lemma oT (P:Pins n C D d p l host mark f w i j x)
  (rb:ReadsBack n C) (lD:RolesOK n C d) {v} (E:v<n+C.gates.length)
  (t:IsCentred n C d v):IsCentred n D (aA d p l host mark f w i j x) (w v):=by
 induction v using Nat.strong_induction_on with
 | ind v ih=>
   by_cases h:v<n
   ·let r:Fin n:=⟨v,h⟩
    change IsCentred n D (aA d p l host mark f w i j x) (w r.val);rw[P.fixed,aG];exact Finset.mem_insert_of_mem ((aG r).1 t)
   ·obtain⟨k,rfl⟩:∃k,v=n+k:=⟨v-n,by omega⟩
    have a:k<C.gates.length:=by omega
    obtain⟨s,y,g,u⟩:=(aR rb a).1 t;obtain m|⟨q,_,o,_⟩:=lD k a
    ·rw[s] at m;contradiction
    have e:d.role k=(.z,q.val):=Prod.ext s o;have A:=rb k a y g;have b:=ih y A (by omega) u;rw[P.align,aR P.rb (jW P a),fW P k];refine⟨s,?_⟩;rw[P.insZ k a q e];by_cases c:host=some q
    ·by_cases B:y=x
     ·subst y;refine⟨n+j,List.mem_map.mpr ⟨x,g,?_⟩,rW P c b⟩;simp[c,dY]
     ·refine⟨w y,List.mem_map.mpr ⟨y,g,?_⟩,b⟩;simp[c,dY,B]
    ·refine⟨w y,List.mem_map.mpr ⟨y,g,?_⟩,b⟩;simp[c]
lemma oG (h:LamOK n C d t r):
  d.lam t r=r.val∨∃k<C.gates.length,d.lam t r=n+k∧d.role k=(.z,r.val):=by
 by_cases hr:r∈d.cover
 ·rw[LamOK,ite_eq_left hr] at h;exact h.2.1
 ·rw[LamOK,ite_eq_right hr] at h;exact Or.inl h
lemma yJ {t r s:Fin n}
  (hr:LamOK n C d t r) (hs:LamOK n C d t s)
  (h:d.lam t r=d.lam t s):r=s:=by
 rcases oG hr with a|⟨k,_,a,c⟩<;>rcases oG hs with b|⟨m,_,b,f⟩
 ·exact Fin.ext (a.symm.trans (h.trans b))
 ·have:=r.isLt;omega
 ·have:=s.isLt;omega
 ·have e:k=m:=by omega
  subst m;exact Fin.ext (congrArg Prod.snd (c.symm.trans f))
lemma uZ (v:Valid n K A C d) (P:Pins n C D d p l host mark f w i j x)
  (S:Positions n C d A p host mark x)
  (X:p∉d.cover) (hl:l∉d.cover) (O:l≠p) {t r:Fin n}
  (ht:t∈(aA d p l host mark f w i j x).cover) (Q:(aA d p l host mark f w i j x).owns t r=true):LamOK n D (aA d p l host mark f w i j x) t r:=by
 by_cases B:t=p
 ·subst t;have a0:r=l:=by simpa[aA] using Q
  subst r;simp[LamOK,aA,hl,O]
 have T:t∈d.cover:=(Finset.mem_insert.mp ht).resolve_left B;have R:d.owns t r=true:=by simpa[aA,B] using Q
 have o:=(v.2.2.2.2.2.1 t T).2.2.2;have c:=o r R;have a (h:mark t=true∧d.lam t r=x):host=some r:=by obtain⟨q,Z,H,V⟩:=S.hits t h.1;have e:=yJ c (o q H) (h.2.trans V.symm);simpa[e] using Z
 have b:
   (aA d p l host mark f w i j x).lam t r=(if mark t=true∧d.lam t r=x then n+j else w (d.lam t r)):=by
  simpa only[aA,B,ite_false] using lE P (d.lam t r) (mark t)
 by_cases hr:r∈d.cover
 ·have u:r≠p:=fun e=>X (e▸hr)
  have z:r∈(aA d p l host mark f w i j x).cover:=Finset.mem_insert_of_mem hr;rw[LamOK,ite_eq_left hr] at c;rw[LamOK,ite_eq_left z];have U:d.lam t r<n+C.gates.length:=by
   rcases c.2.1 with e|⟨k,N,e,_⟩
   ·have:=r.isLt;omega
   ·omega
  have s:=oT P v.1 v.2.2.2.2.1 U c.1;refine⟨?_,?_,?_⟩
  ·rw[b]
   split_ifs with m
   ·exact rW P (a m) (m.2▸s)
   ·exact s
  ·rw[b]
   split_ifs with m
   ·exact Or.inr ⟨j,aAi P,rfl,aAm P (a m)⟩
   ·rcases c.2.1 with e|⟨k,N,e,E⟩
    ·exact Or.inl (by rw[e,P.fixed])
    ·exact Or.inr ⟨f k,jW P N,by rw[e,P.align],(fW P k).trans E⟩
  ·intro J;have y:d.tie r=some t:=by simpa[aA,u] using J
   have e:=c.2.2 y;rw[b];simp only[aA,ite_eq_right u];by_cases hh:host=some r
   ·by_cases M:d.zroot r=x
    ·have m:=S.tiedRoot t r hh y M;simp[hh,dY,e,M,m]
    ·simp[hh,dY,e,M]
   ·have G:¬(mark t=true∧d.lam t r=x):=fun m=>hh (a m)
    rw[ite_eq_right G,e,ite_eq_right hh]
 ·rw[LamOK,ite_eq_right hr] at c;have G:¬(mark t=true∧d.lam t r=x):=by
   intro m;exact hr (v.2.2.1.1 r p (S.hostOwns r (a m))).2
  have g:(aA d p l host mark f w i j x).lam t r=r.val:=by rw[b,ite_eq_right G,c,P.fixed]
  by_cases u:r=p
  ·subst r;have F:p∈(aA d p l host mark f w i j x).cover:=Finset.mem_insert_self _ _;rw[LamOK,ite_eq_left F];refine⟨?_,Or.inl g,fun _=> ?_⟩
   ·rw[g,aG];exact F
   ·simpa[aA] using g
  ·have z:r∉(aA d p l host mark f w i j x).cover:=by simpa[aA,u] using hr
   rw[LamOK,ite_eq_right z];exact g
end PEqualNP.MetaComplexity.NestedCover.Ag
namespace PEqualNP.MetaComplexity.NestedCover.Ag
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C D : Circuit} {d : NCCData n} {p l : Fin n} {host : Option (Fin n)}
    {mark : Fin n → Bool} {f w : ℕ ↪ ℕ} {i j x : ℕ}
lemma eM (v:Valid n K A C d) (P:Pins n C D d p l host mark f w i j x)
  (pos:Positions n C d A p host mark x)
  (outside:∀T,IsMinCover K T→p∉T) (iso:∀r,¬K.Adj l r)
  (ext:∀u v,K'.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p)):
  Valid n K' A D (aA d p l host mark f w i j x):=by
 have a:=outside _ v.2.1;have hl:l∉d.cover:=by
  intro k;have c:K.IsVertexCover (↑(d.cover.erase l):Set (Fin n)):=by
   intro u z e;have m:u≠l:=by rintro rfl;exact iso _ e
   have o:z≠l:=by rintro rfl;exact iso _ e.symm
   simpa[m,o] using v.2.1.1 e
  have g:=v.2.1.2 _ c;have:=Finset.card_erase_lt_of_mem k;omega
 have b:l≠p:=by rintro rfl;exact K'.loopless.irrefl _ ((ext _ _).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)))
 obtain⟨q,s,y⟩:=aCc (f:=f) (w:=w) (i:=i) (j:=j) v pos outside iso ext;refine⟨P.rb,q,s,y,lD v P pos a,?_,?_⟩
 ·intro t ht;refine⟨?_,?_,?_,fun r=>uZ v P pos a hl b ht⟩
  ·rcases Finset.mem_insert.mp ht with e|h
   ·subst t;exact aBj P
   ·exact aBk P (fun e=>a (e▸h)) (v.2.2.2.2.2.1 _ h).1
  ·rcases Finset.mem_insert.mp ht with e|h
   ·subst t;exact(uY v P pos a (eN P pos v.2.2.1 v.2.2.2.1 a)).1
   ·rw[iN P a];exact aAk v P pos a h
  ·rcases Finset.mem_insert.mp ht with e|h
   ·subst t;exact(uY v P pos a (eN P pos v.2.2.1 v.2.2.2.1 a)).2
   ·exact aAl v P pos a h
 ·rw[mX P a];exact cZ v P pos
end PEqualNP.MetaComplexity.NestedCover.Ag
namespace PEqualNP.MetaComplexity.NestedCover.Ar
variable {n : ℕ} {d : NCCData n} {A : Finset (Fin n)} {p : Fin n}
  {K : SimpleGraph (Fin n)} {M : Sig d}
lemma oH (P:Fin n→Prop) (f:Fin n→ℕ) (h:∃t,P t):
  ∃t,P t∧∀s,P s→f t≤f s:=by
 classical
 let S:=Finset.univ.filter P
 have hs (v):v∈S↔P v:=by simp[S]
 obtain⟨t,ht⟩:=h;obtain⟨y,c,a⟩:=S.exists_min_image f ⟨t,(hs t).2 ht⟩;exact⟨y,(hs y).1 c,fun v b=>a v ((hs v).2 b)⟩
lemma lZ (f:OwnerOK K d) (tie:TieOK d) (H:K.CliqueFree 3)
  (B:p∉d.cover) (C:p∉A) (out:Out M A {p})
  (prod:∀t∈d.cover,
    M.b {p} t↔(Z0 M {p} t∨M.z t)∧(O0 M {p} t∨M.o t))
  (single:∀t∈d.cover,∀s∈d.cover,M.z t→M.z s→t=s)
  (G:∀t∈d.cover,M.z t→¬M.o t):
  M.top∨∃t∈d.cover,M.z t∧d.owns t p=true∧(∀s∈d.cover,M.z s→s=t)∧(∀s,d.tie t=some s→M.o s):=by
 classical
 obtain top|⟨a,P,c⟩|⟨u,E,J,q⟩:=out
 ·exact Or.inl top
 ·exact(C ((Finset.mem_singleton.mp c)▸P)).elim
 right;obtain⟨t,⟨ht,N⟩,R⟩:=oH (fun s=>s∈d.cover∧M.b {p} s) d.bw ⟨u,E,q⟩;have first (s) (hs:s∈d.cover) (e:M.b {p} s):¬d.bw s<d.bw t:=not_lt_of_ge (R s ⟨hs,e⟩)
 obtain⟨X,T⟩:=(prod t ht).1 N;have n:M.z t:=by
  rcases X with(c|⟨s,hs,st,e⟩)|mark
  ·exact(B ((Finset.mem_singleton.mp c)▸ht)).elim
  ·exact(first _ hs e (M.tie_lt st)).elim
  ·exact mark
 have edge:d.owns t p=true:=by
  obtain⟨r,g,c|⟨s,hs,l,e⟩⟩:=T.resolve_right (G t ht n)
  ·exact(Finset.mem_singleton.mp c)▸g
  ·exact(first _ hs e (M.part_lt g l)).elim
 refine⟨t,ht,n,edge,fun s hs h=>single s hs t ht h n,?_⟩;intro w m;have y:u≠t:=by rintro rfl;simp[m] at J
 obtain⟨s,⟨hs,e,st⟩,F⟩:=oH
  (fun s=>s∈d.cover∧M.b {p} s∧s≠t) d.bw ⟨u,E,q,y⟩
 have only(v) (j:v∈d.cover) (i:M.b {p} v) (hb:d.bw v<d.bw s):
   v=t:=by
  by_contra Q;have:=F v ⟨j,i,Q⟩;omega
 obtain⟨V,S⟩:=(prod s hs).1 e;have Z:s=w:=by
  rcases V with(c|⟨v,j,k,i⟩)|mark
  ·exact(B ((Finset.mem_singleton.mp c)▸hs)).elim
  ·have O:=only _ j i (M.tie_lt k);rw[O,m] at k;exact(Option.some.inj k).symm
  ·exact(st (single s hs t ht mark n)).elim
 subst w;rcases S with⟨r,g,c|⟨v,j,l,i⟩⟩|mark
 ·have x:d.owns s p=true:=(Finset.mem_singleton.mp c)▸g;have k:=(f.1 _ _ (tie t s m).2).1.symm;exact(H {t,s,p} (SimpleGraph.is3Clique_triple_iff.mpr
   ⟨k,(f.1 _ _ edge).1,(f.1 _ _ x).1⟩)).elim
 ·have U:=only _ j i (M.part_lt g l);have tr:=M.part_tie l;rw[U,m] at tr;exact((f.1 _ _ g).1.ne (Option.some.inj tr)).elim
 ·exact mark
end PEqualNP.MetaComplexity.NestedCover.Ar
namespace PEqualNP.MetaComplexity.NestedCover.A4
open PEqualNP.CircuitLowerBounds Ac Ar Ad
variable {n : ℕ} {D C : Circuit} {f w : ℕ ↪ ℕ} {src i j : ℕ}
variable {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)} {d : NCCData n}
variable {p l : Fin n}
lemma kP [DecidableRel K'.Adj]
  (h:Valid n K A D d) (F:Ae.bB n D C f w)
  (S:Splice n D C f w src (n+j))
  (G:i<C.gates.length) (H:j<C.gates.length)
  (andOp:(gateAt C i).op= .and)
  (andIns:(gateAt C i).inputs=[p.val,l.val]∨(gateAt C i).inputs=[l.val,p.val])
  (orOp:(gateAt C j).op= .or)
  (orIns:(gateAt C j).inputs=[w src,n+i]∨(gateAt C j).inputs=[n+i,w src])
  (a:∀v,¬K.Adj l v) (x:l∉A)
  (ext:∀u v,K'.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p))
  (c:circuitFun n C=graphFun K' A)
  (E:K.CliqueFree 3) (J:p∉d.cover) (r:p∉A):
  eG (aE h S)∨∃q∈d.cover,eL (aE h S) q∧d.owns q p=true∧∀s,d.tie q=some s→jU (aE h S) s:=by
 let α:=Ae.bJ l
 let M:=Ae.iF h C f w src (n+j) α
 have k:W C (α {p}) p.val:=(aC p).2 (by simp[α,Ae.bJ]);have g:W C (α {p}) l.val:=(aC l).2 (by simp[α,Ae.bJ]);have P:W C (α {p}) (n+i):=by
  unfold W at k g ⊢
  rw[aO F.back G,andOp];rcases andIns with e|e<;>simp[e,GateOp.eval,List.getD_eq_getElem?_getD] at k g ⊢ <;>simp[k,g]
 have m:W C (α {p}) (n+j)↔W C (α {p}) (w src)∨True:=(Ae.xA F.back H orOp orIns).trans (by simp[P]);have B:=Ae.qE h a x {p};have Q:W C (α {p}) C.output:=(Ae.oD a x ext c {p}).2 (.inl (Finset.mem_singleton_self p));have out:Out M A {p}:=by simpa[Out,M] using(Ae.output h F S B m).1 Q
 have prod (t) (ht:t∈d.cover):
   M.b {p} t↔(Z0 M {p} t∨M.z t)∧(O0 M {p} t∨M.o t):=by
  simpa[M] using Ae.prod h F S B m ht
 obtain top|⟨q,N,R,y,_,tied⟩:=lZ h.2.2.1 h.2.2.2.1 E J r out prod
  (fun t ht s hs mt O=>rS h (aE h S) ht hs mt O)
  (fun t ht mt=>yA h (aE h S) ht mt)
 ·exact .inl top
 ·exact .inr ⟨q,N,R,y,tied⟩
end PEqualNP.MetaComplexity.NestedCover.A4
namespace PEqualNP.MetaComplexity.NestedCover.Ag
open PEqualNP.CircuitLowerBounds Ac Ad
variable {n : ℕ} {K K' : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C D : Circuit} {d : NCCData n} {p l : Fin n} {host : Option (Fin n)}
    {mark : Fin n → Bool} {f w : ℕ ↪ ℕ} {i j x : ℕ}
lemma jX (v:Valid n K A C d) {k t mV}
  (c:k<C.gates.length) (a:d.role k=(mV,(t:Fin n).val)) (e:mV≠ .top):
  t∈d.cover:=by
 rcases v.2.2.2.2.1 k c with h|⟨s,hs,b,_⟩
 ·exact False.elim (e (by simpa[a] using h))
 ·exact(Fin.ext (show s.val=t.val by simpa[a] using b.symm))▸hs
lemma rX {Q P:Prop} [Decidable P] (a:Q↔P) (w:ℕ ↪ ℕ) (x v:ℕ):
  cV w x v Q=(if P then dY w x v else ⇑w):=by
 funext z;by_cases h:P<;>simp[cV,a,h,dY]
structure TwoFresh (n : ℕ) (C D : Circuit) (p l : Fin n) (f w : ℕ ↪ ℕ) (i j x : ℕ) : Prop where
  roster : Finset.range D.gates.length = insert i (insert j ((Finset.range C.gates.length).map f))
  gapI : ∀ k, f k ≠ i
  ij : i ≠ j
  rb : ReadsBack n D
  fixed : ∀ r : Fin n, w r.val = r.val
  andOp : (gateAt D i).op = .and
  andIns : (gateAt D i).inputs = [p.val,l.val] ∨ (gateAt D i).inputs = [l.val,p.val]
  orOp : (gateAt D j).op = .or
  orIns : (gateAt D j).inputs = [w x,n+i] ∨ (gateAt D j).inputs = [n+i,w x]
lemma aBl (v:Valid n K A C d) (sp:Splice n C D f w x (n+j))
  (F:TwoFresh n C D p l f w i j x) (R:Route A p (aE v sp) host mark):
  Pins n C D d p l host mark f w i j x:=by
 classical
 let S:=aE v sp
 have g {t} (ht:t∈d.cover):=rX (R.z t ht) w x (n+j);have b {t} (ht:t∈d.cover):cV w x (n+j) (fE S t)=
   ⇑(cA w x (n+j) (mark t)):=by
  funext u;rw[oS sp.hole];simp only[cV,R.o t ht,S]
 have c:=rX R.top w x (n+j);refine⟨F.roster,F.gapI,fun k e=>sp.hole (n+k) (by rw[sp.align,e]),F.ij,F.fixed,sp.align,F.rb,?_,fun k _=>sp.op k,F.andOp,F.andIns,F.orOp,F.orIns,?_,?_,?_,?_⟩
 ·rw[tC v sp,c];by_cases h:host=none<;>simp[h]
 ·intro k a e;rw[yI v sp a e,c]
 ·intro k a t e;rw[aBg v sp a e,g (jX v a e (by decide))]
 ·intro k a t e;rw[aBh v sp a e,b (jX v a e (by decide))]
 ·intro k a t e;have ht:=jX v a e (by decide);have h:=aBi v sp a e;dsimp only at h ⊢
  rw[g ht,b ht] at h;by_cases hh:host=some t<;>simpa only[hh,ite_true,ite_false] using h
lemma rB [DecidableRel K'.Adj] (v:Valid n K A C d)
  (sp:Splice n C D f w x (n+j)) (F:TwoFresh n C D p l f w i j x)
  (outside:∀T,IsMinCover K T→p∉T)
  (iso:∀a∈A,∀r,¬K.Adj a r) (e:∀r,¬K.Adj l r)
  (E:l∉A) (G:p∉A) (t:K.CliqueFree 3)
  (ext:∀u v,K'.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p))
  (g:circuitFun n D =graphFun K' A):IsNestedCoverCircuit n K' A D:=by
 have c:Ae.bB n C D f w:=⟨F.rb,fun k B=>Finset.mem_range.mp
  (F.roster▸Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_map.mpr ⟨_,Finset.mem_range.mpr B,rfl⟩))),F.fixed⟩
 have y:i<D.gates.length:=Finset.mem_range.mp (F.roster▸Finset.mem_insert_self ..);have z:j<D.gates.length:=Finset.mem_range.mp
  (F.roster▸Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
 let S:=aE v sp
 have b {h m} (r:Route A p S h m):IsNestedCoverCircuit n K' A D:=⟨_,eM v (aBl v sp F r) r.pos outside e ext⟩
 rcases A4.kP v c sp y z F.andOp F.andIns F.orOp F.orIns
  e E ext g t (outside _ v.2.1) G with hm|⟨q,hq,zm,owns,follow⟩
 ·exact b (wJ v iso S hm)
 ·exact b (aAj v iso S hq zm owns fun s tie o=>tiedRoot v S hq zm tie o (follow s tie))
end PEqualNP.MetaComplexity.NestedCover.Ag
namespace PEqualNP.MetaComplexity.NestedCover.Af
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K : SimpleGraph (Fin n)} {d : NCCData n} {C : Circuit}
  {A : Finset (Fin n)} {q t r : Fin n} {w : ℕ} (h : Valid n K A C d)
lemma dA {w}:
  w∈topLeaves d A↔(∃a∈A,a.val=w)∨∃s∈d.cover,d.tie s=none∧d.bw s=w:=by
 simp[topLeaves,and_assoc]
include h
lemma vA {x:Fin n→Bool} (g:fQ n (topGates d C) (topLeaves d A) w):
  W
   C x w↔(∃a∈A,Below n C (topGates d C) a.val w∧x a=true)∨
   ∃s∈d.cover,d.tie s=none∧Below n C (topGates d C) (d.bw s) w∧W C x (d.bw s):=by
 have top:=h.2.2.2.2.2.2;have bd:∀j∈topGates d C,j<C.gates.length:=fun _ hh=>Finset.mem_range.mp (Finset.mem_filter.mp hh).1
 rw[gS top h.1 bd _ (gT h.1 top bd) g];constructor
 ·rintro⟨i,f,c,e⟩;rcases dA.mp f with⟨a,b,rfl⟩|⟨s,hs,τ,rfl⟩
  ·exact Or.inl ⟨a,b,c,(aC a).1 e⟩
  ·exact Or.inr ⟨s,hs,τ,c,e⟩
 ·rintro(⟨a,b,ba,xa⟩|⟨s,hs,τ,bs,ws⟩)
  ·exact⟨_,dA.mpr (Or.inl ⟨a,b,rfl⟩),ba,(aC a).2 xa⟩
  ·exact⟨_,dA.mpr (Or.inr ⟨s,hs,τ,rfl⟩),bs,ws⟩
lemma dB (e:fQ n (topGates d C) (topLeaves d A) w) (k:Fin n):
  W C (single k) w↔k∈A∧Below n C (topGates d C) k.val w:=by
 rw[vA h e];constructor
 ·rintro(⟨a,c,b,xa⟩|⟨s,hs,_,_,ws⟩)
  ·obtain rfl:a=k:=of_decide_eq_true xa;exact⟨c,b⟩
  ·exact(bY h hs k ws).elim
 ·rintro⟨c,b⟩;exact Or.inl ⟨k,c,b,by simp[single]⟩
lemma jY (m:w<n+C.gates.length) (E:q∉A)
  (c:W C (single q) w)
  (unique:∀k,(∃u,K.Adj u k)→W C (single k) w→k=q):
  w=q.val∨q∈d.cover∧IsCentred n C d w∧∃j∈Z q d C,w=n+j:=by
 by_cases F:w<n
 ·let k:Fin n:=⟨w,F⟩
  have iF:=(aC (C:=C) (x:=single q) k).1 c;exact Or.inl (congrArg Fin.val (of_decide_eq_true iF:k=q))
 let j:=w-n
 have l:j<C.gates.length:=by dsimp[j];omega
 have e:w=n+j:=by dsimp[j];omega
 have top (ht:(d.role j).1=Kind.top):False:=by have y:j∈topGates d C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr l,ht⟩;exact E (((dB h (.inr ⟨_,y,e⟩) q).1 c).1)
 rcases h.2.2.2.2.1 j l with ht|⟨u,f,H,s⟩
 ·exact(top ht).elim
 have i {k} (B:(d.role j).1=k):j∈gatesOf d C k u.val:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr l,Prod.ext B H⟩
 cases k:(d.role j).1 with
 | top=>exact(top k).elim
 | b=>exact(bY h f q ((e.trans (s k).symm)▸c)).elim
 | z=>
   obtain⟨g,rfl⟩:=(jM h f (.inr ⟨_,i k,e⟩) q).1 c;exact Or.inr ⟨f,g,_,i k,e⟩
 | o=>
   obtain⟨a,b,G,t,v,J,M⟩:=kZ h f (i k);have p:=unique a ⟨_,(h.2.2.1.1 _ _ t).1⟩ (e▸J);have r:=unique b ⟨_,(h.2.2.1.1 _ _ v).1⟩ (e▸M);exact(G (p.trans r.symm)).elim
lemma kQ (a:q∈d.cover) (τq:d.tie q=none)
  (c:dP q d C w) (e:IsCentred n C d w)
  (wK:∀s∈d.cover,d.tie s=some q→
    ∃r∉d.cover,d.owns s r=true∧W C (pair s r) w):w=d.zroot q:=by
 apply xV h a c e;intro s hs τ;obtain⟨r,hr,f,i⟩:=wK s hs τ;rcases (aA7 h f τ τq hr a c).1 i with⟨_,sq|g⟩|⟨_,b⟩
 ·subst s;simp[τq] at τ
 ·exact(hr (g▸a)).elim
 ·exact b
lemma mY (i:w<n+C.gates.length) (t:q∉A)
  (out:q∉d.cover) (a:W C (single q) w):
  w
   =q.val∨∃u∈d.cover,d.owns u q=true∧
   ∃j∈O u d C,w=n+j∧Below n C (O u d C) q.val w:=by
 by_cases v:w<n
 ·let k:Fin n:=⟨w,v⟩
  have iF:=(aC (C:=C) (x:=single q) k).1 a;exact Or.inl (congrArg Fin.val (of_decide_eq_true iF:k=q))
 let j:=w-n
 have g:j<C.gates.length:=by dsimp[j];omega
 have e:w=n+j:=by dsimp[j];omega
 have top (ht:(d.role j).1=Kind.top):False:=by have r:j∈topGates d C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr g,ht⟩;exact t (((dB h (.inr ⟨_,r,e⟩) q).1 a).1)
 rcases h.2.2.2.2.1 j g with ht|⟨u,c,y,m⟩
 ·exact(top ht).elim
 have f {k} (s:(d.role j).1=k):j∈gatesOf d C k u.val:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr g,Prod.ext s y⟩
 cases k:(d.role j).1 with
 | top=>exact(top k).elim
 | b=>exact(bY h c q ((e.trans (m k).symm)▸a)).elim
 | z=>
   obtain⟨_,rfl⟩:=(jM h c (.inr ⟨_,f k,e⟩) q).1 a;exact(out c).elim
 | o=>
   obtain⟨l,b⟩:=(jN h c (.inr ⟨_,f k,e⟩) q).1 a;have p:d.lam u q=q.val:=by simpa[LamOK,out] using lam h l
   exact Or.inr ⟨u,c,l,j,f k,e,p▸b⟩
end PEqualNP.MetaComplexity.NestedCover.Af
namespace PEqualNP.MetaComplexity.NestedCover.A3
open PEqualNP.CircuitLowerBounds Ac Af
variable {n : ℕ} {D P : Circuit} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
  {d : NCCData n} {g w : ℕ ↪ ℕ} {u f H : ℕ} {p r l : Fin n}
lemma gW {x:Fin n→Bool} {j:ℕ} (back:ReadsBack n D)
  (aT:j<D.gates.length) (op:(gateAt D j).op= .and):
  W D x (n+j)↔∀i∈(gateAt D j).inputs,W D x i:=by
 unfold W;rw[aO back aT,op];simp[GateOp.eval]
structure Setup (n : ℕ) (D P : Circuit) (g w : ℕ ↪ ℕ) (u f H : ℕ) (l : Fin n) :
    Prop extends Splice n D P g w u f where
  raw : ∀ v : Fin n, w v.val = v.val
  validGate : ∀ j, j < D.gates.length → g j < P.gates.length
  back : ReadsBack n P
  fresh : ∀ x : Fin n → Bool, W P x f ↔ W P x (w u) ∨ x l = true ∧ W P x (w H)
variable (h : Valid n K A D d) (S : Setup n D P g w u f H l)
include S
lemma vB (j a:ℕ) (h:a∈(gateAt D j).inputs):
  ∃b∈(gateAt P (g j)).inputs,b=w a∨b=f∧a=u:=by
 obtain⟨i,k,e⟩:=List.mem_iff_getElem.mp h;rcases (S.pin j i a).mp ((List.getElem?_eq_getElem k).trans (congrArg some e)) with c|⟨c,d⟩
 ·exact⟨_,List.mem_of_getElem? c,.inl rfl⟩
 ·exact⟨_,List.mem_of_getElem? c,.inr ⟨rfl,d⟩⟩
lemma nN (j b:ℕ) (k:b∈(gateAt P (g j)).inputs):
  ∃a∈(gateAt D j).inputs,b=w a∨b=f∧a=u:=by
 obtain⟨i,d,e⟩:=List.mem_iff_getElem.mp k;have h:i<(gateAt D j).inputs.length:=S.total j▸d;refine⟨_,List.getElem_mem h,?_⟩;rcases (S.pin j i _).mp (List.getElem?_eq_getElem h) with c|⟨c,l⟩
 ·exact .inl (e.symm.trans (Option.some.inj ((List.getElem?_eq_getElem d).symm.trans c)))
 ·exact .inr ⟨e.symm.trans (Option.some.inj ((List.getElem?_eq_getElem d).symm.trans c)),l⟩
omit S
include h
lemma dV {j} (c:j<D.gates.length):
  (gateAt D j).op= .or∨∃t∈d.cover,(gateAt D j).op= .and∧
    Ac.mM D j (d.zroot t) (d.oroot t):=by
 have top (e:(d.role j).1= .top):(gateAt D j).op= .or:=(h.2.2.2.2.2.2.1 j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr c,e⟩)).1;rcases h.2.2.2.2.1 j c with ht|⟨t,ht,i,g⟩
 ·exact .inl (top ht)
 have f {k} (e:(d.role j).1=k):j∈gatesOf d D k t.val:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr c,Prod.ext e i⟩
 cases k:(d.role j).1 with
 | top=>exact .inl (top k)
 | z=>exact .inl (((bL h ht).1 j (f k)).1)
 | o=>exact .inl (((cT h ht).1 j (f k)).1)
 | b=>
   obtain⟨a,_,e,_,op,bS⟩:=dN h ht;obtain rfl:a=j:=by have:=g k;omega
   exact .inr ⟨t,ht,op,bS⟩
include S
lemma tE {x y:Fin n→Bool} (le:∀v,x v=true→y v=true)
  {i} (r:i<n+D.gates.length):W D x i→W P y (w i):=by
 induction i using Nat.strong_induction_on with
 | ind i ih=>
   by_cases p:i<n
   ·let v:Fin n:=⟨i,p⟩
    rw[show w i=v.val from S.raw v];exact fun q=>(aC v).2 (le v ((aC v).1 q))
   let j:=i-n
   have o:i=n+j:=by dsimp[j];omega
   have d:j<D.gates.length:=by omega
   have g (a b) (c:a∈(gateAt D j).inputs)
     (e:b=w a∨b=f∧a=u) (l:W D x a):W P y b:=by
    have lt:=h.1 _ d _ c;have m:=ih a (by omega) (by omega) l;rcases e with rfl|⟨rfl,rfl⟩
    ·exact m
    ·exact(S.fresh y).2 (.inl m)
   rw[o,S.align];rcases dV h d with op|⟨t,ht,op,_⟩
   ·rw[aY h.1 d op,aY S.back (S.validGate j d) ((S.op j).trans op)];rintro⟨a,c,l⟩;obtain⟨b,k,e⟩:=vB S j a c;exact⟨b,k,g a b c e l⟩
   ·rw[gW h.1 d op,gW S.back (S.validGate j d) ((S.op j).trans op)];intro all b k;obtain⟨a,c,e⟩:=nN S j b k;exact g a b c e (all a c)
omit h
lemma aBm {x y:Fin n→Bool} {j} (e:j<D.gates.length)
  (op:(gateAt D j).op= .or)
  (d:W P x (w (n+j))) (a:¬W P y (w (n+j))):
  ∃b∈(gateAt P (g j)).inputs,W P x b∧¬W P y b:=by
 rw[S.align,aY S.back (S.validGate j e) ((S.op j).trans op)] at d a;obtain⟨b,c,f⟩:=d;exact⟨b,c,f,fun h=>a ⟨b,c,h⟩⟩
lemma aAn {x y:Fin n→Bool} {j} (e:j<D.gates.length)
  (op:(gateAt D j).op= .and)
  (d:W P x (w (n+j))) (a:¬W P y (w (n+j))):
  ∃b∈(gateAt P (g j)).inputs,W P x b∧¬W P y b:=by
 rw[S.align,gW S.back (S.validGate j e) ((S.op j).trans op)] at d a
 push Not at a
 obtain⟨b,c,f⟩:=a;exact⟨b,c,d b c,f⟩
include h
lemma aAo (E:p∉d.cover) {q:Fin n}
  (unique:∀t,d.owns t p=true→t=q) (G:d.owns q r=true)
  (B:W P (pair r l) f)
  {i} (M:i<n+D.gates.length):
  W P (pair p l) (w i)→¬W P (pair r l) (w i)→W D (single p) i:=by
 induction i using Nat.strong_induction_on with
 | ind i ih=>
   intro z k;by_cases J:i<n
   ·let v:Fin n:=⟨i,J⟩
    rw[show w i=v.val from S.raw v,aC] at z k;change W D (single p) v.val;rw[aC];simp[pair] at z k;simp[single];tauto
   let j:=i-n
   have H:i=n+j:=by dsimp[j];omega
   have o:j<D.gates.length:=by omega
   rw[H] at z k ⊢
   have u {b} (s:b∈(gateAt P (g j)).inputs) (A:W P (pair p l) b)
     (c:¬W P (pair r l) b):
     ∃a∈(gateAt D j).inputs,W D (single p) a∧¬W P (pair r l) (w a):=by
    obtain⟨a,m,rfl|⟨rfl,_⟩⟩:=nN S j b s
    ·have lt:=h.1 _ o _ m;exact⟨a,m,ih a (by omega) (by omega) A c,c⟩
    ·exact(c B).elim
   rcases dV h o with op|⟨t,ht,op,F⟩
   ·obtain⟨b,s,A,c⟩:=aBm S o op z k;obtain⟨a,m,C,_⟩:=u s A c;exact(aY h.1 o op).2 ⟨a,m,C⟩
   ·obtain⟨b,s,A,c⟩:=aAn S o op z k;obtain⟨a,m,C,c⟩:=u s A c;have e:a=d.zroot t∨a=d.oroot t:=by
     rcases F with e|e<;>simp[e] at m<;>tauto
    exfalso;rcases e with rfl|rfl
    ·obtain⟨_,rfl⟩:=(jM h ht (cC (bL h ht)) p).1 C;exact E ht
    ·obtain rfl:=unique t ((jN h ht (cC (cT h ht)) p).1 C).1;have K:W D (single r) (d.oroot t):=
      (fR h ht).2 ⟨r,G,(iD h G r).2 rfl⟩
     have lt:=h.1 _ o _ m;exact c (tE h S (x:=single r) (y:=pair r l)
      (by intro v;simp[pair,single];tauto) (by omega) K)
lemma xJ (s:∀j<D.gates.length,l.val∉(gateAt D j).inputs)
  (before:w u<f) (k:ℕ)
  (o:f<k→W P (pair p l) f→W P (pair p l) (w u))
  {i} (E:i<n+D.gates.length) (C:w i<k) (x:i≠l.val):
  W P (pair p l) (w i)→W D (single p) i:=by
 induction i using Nat.strong_induction_on with
 | ind i ih=>
   by_cases A:i<n
   ·let v:Fin n:=⟨i,A⟩
    change W P (pair p l) (w v.val)→W D (single p) v.val;rw[S.raw,aC,aC];simp only[pair,single,decide_eq_true_eq];rintro(e|e);exact e;exact(x (congrArg Fin.val e)).elim
   let j:=i-n
   have t:i=n+j:=by dsimp[j];omega
   have d:j<D.gates.length:=by omega
   have q (a b) (c:a∈(gateAt D j).inputs) (m:b∈(gateAt P (g j)).inputs)
     (e:b=w a∨b=f∧a=u) (r:W P (pair p l) b):W D (single p) a:=by
    have F:=h.1 _ d _ c;have z:=S.back _ (S.validGate j d) _ m;rw[←S.align,←t] at z;have B:a≠l.val:=fun y=>s j d (y▸c)
    apply ih a (by omega) (by omega) _ B
    ·rcases e with rfl|⟨rfl,rfl⟩
     ·exact r
     ·exact o (by omega) r
    ·rcases e with rfl|⟨rfl,rfl⟩<;>omega
   rw[t,S.align];rcases dV h d with op|⟨_,_,op,_⟩
   ·rw[aY h.1 d op,aY S.back (S.validGate j d) ((S.op j).trans op)];rintro⟨b,m,r⟩;obtain⟨a,c,e⟩:=nN S j b m;exact⟨a,c,q a b c m e r⟩
   ·rw[gW h.1 d op,gW S.back (S.validGate j d) ((S.op j).trans op)];intro all a c;obtain⟨b,m,e⟩:=vB S j a c;exact q a b c m e (all b m)
lemma wK (z:p∉A) (g:∀j<D.gates.length,l.val∉(gateAt D j).inputs)
  (i:D.output≠l.val) (b:D.output<n+D.gates.length)
  (o:w u<f) (d:u<n+D.gates.length)
  (t:w H<f) (c:H<n+D.gates.length) (hl:H≠l.val)
  (q:W P (pair p l) P.output):
  W D (single p) H∧¬W D (single p) u:=by
 have k:¬W D (single p) D.output:=fun E=>z (((dB h (cC h.2.2.2.2.2.2) p).1 E).1)
 have a (bypass:W P (pair p l) f→W P (pair p l) (w u)):False:=by
  apply k;apply xJ h S g o (w D.output+1) (fun _=>bypass) b (by omega) i;rcases (S.output D.output).1 rfl with e|⟨e,s⟩
  ·exact e▸q
  ·rw[s];exact bypass (e▸q)
 have r:W P (pair p l) (w H):=by
  by_contra hh;apply a;intro C;rcases (S.fresh _).1 C with ws|⟨_,m⟩
  ·exact ws
  ·exact(hh m).elim
 refine⟨xJ h S g o f (fun e=>(Nat.lt_irrefl _ e).elim) c t hl r,?_⟩;intro B;apply a;intro _;exact tE h S (x:=single p) (y:=pair p l) (by intro v;simp[single,pair];tauto) d B
lemma wL (C:p∉A) (outside:p∉d.cover)
  (only:∀s t,d.owns s p=true→d.owns t p=true→s=t)
  (z:∀j<D.gates.length,l.val∉(gateAt D j).inputs)
  (k:D.output≠l.val) (g:D.output<n+D.gates.length)
  (T:w u<f) (i:u<n+D.gates.length)
  (R:w H<f) (c:H<n+D.gates.length) (hl:H≠l.val)
  (B:W P (pair p l) P.output)
  (K:∀q r,d.owns q p=true→d.owns q r=true→ r≠p→¬W P (pair r l) P.output):
  H=p.val:=by
 have⟨o,_⟩:=wK h S C z k g T i R c hl B;rcases mY h c C outside o with e|⟨q,X,F,j,V,e,_⟩
 ·exact e
 obtain⟨a,b,Z,N,O,wa,wb⟩:=kZ h X V;have E:∃r,r≠p∧d.owns q r=true∧W D (single r) H:=by
  by_cases J:a=p
  ·exact⟨b,fun U=>Z (J.trans U.symm),O,e▸wb⟩
  ·exact⟨a,J,N,e▸wa⟩
 obtain⟨r,rp,G,signal⟩:=E;have M:W P (pair r l) f:=(S.fresh _).2 (.inr ⟨by simp[pair],tE h S (by intro v;simp[single,pair];tauto) c signal⟩);have y:=K q r F G rp;exfalso;rcases (S.output D.output).1 rfl with m|⟨m,_⟩
 ·rw[m] at B y;have x:=aAo h S outside (fun t Q=>only t q Q F) G M g B y;exact C (((dB h (cC h.2.2.2.2.2.2) p).1 x).1)
 ·exact y (m▸M)
end PEqualNP.MetaComplexity.NestedCover.A3
namespace PEqualNP.MetaComplexity.NestedCover.A3
open PEqualNP.CircuitLowerBounds Ac Af
variable {n B H J a : ℕ} {P : Circuit} {l p : Fin n} {K KP : SimpleGraph (Fin n)}
  {A : Finset (Fin n)} {d : NCCData n}
lemma yK (s : At P l false B H J a) (back : ReadsBack n P) :
    Setup n (bT n P B l.val J a) P (cN B J) (cN (n+B) (n+J))
      (contract (n+B) l.val a) (n+skip B J) H l where
  toSplice := s.splice
  raw := fun v => nJ v B J
  validGate := by
    intro j hj
    have hJ := (aS (n := n) (h := l.val) s.realB).mpr s.realD
    exact (aS s.realB).mp ((aS hJ).mp hj)
  back := back
  fresh := by
    intro x
    rw [s.mapH,s.mapA]
    rw [aY back s.realD (show (gateAt P (skip B J)).op = .or from s.opD)]
    have hb : W P x (n+B) ↔ x l = true ∧ W P x H := by
      rw [gW back s.realB (show (gateAt P B).op = .and from s.opB)]
      rcases s.pairB with e|e <;> simp [e,aC,and_comm]
    rcases s.pairD with e|e <;> simp [e,hb,or_comm]
lemma kF {D:Circuit} (h:Valid n K A D d):D.output<n+D.gates.length:=by
 rcases cC h.2.2.2.2.2.2 with hl|⟨j,c,e⟩
 ·rcases dA.mp hl with⟨a,_,e⟩|⟨s,hs,_,e⟩
  ·have:=a.isLt;omega
  ·obtain⟨j,c,b,_,_⟩:=dN h hs;omega
 ·have:=Finset.mem_range.mp (Finset.mem_filter.mp c).1;omega
lemma wM [DecidableRel KP.Adj] (s:At P l false B H J a)
  (h:Valid n K A (bT n P B l.val J a) d)
  (back:ReadsBack n P) (N:p∉A) (outside:p∉d.cover)
  (only:∀s t,K.Adj p s→K.Adj p t→s=t)
  (isoL:∀r,¬K.Adj l r) (x:l∉A) (k:∀i∈A,∀r,¬K.Adj i r)
  (ext:∀u v,KP.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p))
  (c:circuitFun n P=graphFun KP A):H=p.val:=by
 let D:=bT n P B l.val J a
 let u:=contract (n+B) l.val a
 let w:=cN (n+B) (n+J)
 have b:D.output≠l.val:=by intro M;apply x;apply((dB h (cC h.2.2.2.2.2.2) l).1 _).1;change W D (single l) D.output;rw[M,aC];simp[single]
 have E:u≠l.val:=by intro e;exact s.distinctA.1 (s.mapA.symm.trans ((congrArg w e).trans (nJ _ _ _)))
 have m:=s.splice.unused l (nJ _ _ _) E
  (fun e=>b ((s.splice.output _).2 (.inl (e.trans (nJ l B J).symm))))
  (fun j _ hl=>(zP B J j).1 (s.onlyL _ (dJ.mpr hl)))
 have f:=s.ordered;have realD:=s.realD;have realB:=s.realB;have earlier:=s.earlierH;have y:=s.size;change D.gates.length+2=P.gates.length at y;have R:skip B J=J+1:=by rw[aQ] at f ⊢;split at f<;>split<;>omega
 have C:u<n+D.gates.length:=by
  have G:l.val<n+B:=by have:=l.isLt;omega
  have Q:=bI G (show a<skip (n+B) (n+J) by rw[align];exact s.earlierA);change u<n+J at Q;omega
 have o:KP.Adj p l:=(ext _ _).2 (.inr (.inl ⟨rfl,rfl⟩));apply wL h (yK s back) N outside
  (fun s t hs ht=>only s t (h.2.2.1.1 _ _ hs).1.symm (h.2.2.1.1 _ _ ht).1.symm)
  m.2 b (kF h) (by rw[s.mapA];exact s.earlierA) C
  (by rw[s.mapH];omega) (by change H<n+D.gates.length;omega) s.distinctH
 ·rw[←cL,c];simp only[graphFun,pair,Bool.or_eq_true,decide_eq_true_eq];exact .inr ⟨p,l,o,.inl rfl,.inr rfl⟩
 ·intro q r _ F z;have O:r∉A:=fun hr=>k r hr q (h.2.2.1.1 _ _ F).1.symm
  have pl:=o.ne;rw[←cL,c];simp only[graphFun,pair,Bool.or_eq_true,decide_eq_true_eq];rintro(⟨i,hi,ix⟩|⟨i,j,e,ix,jx⟩)
  ·rcases ix with rfl|rfl
   ·exact O hi
   ·exact x hi
  ·rcases (ext _ _).1 e with g|⟨rfl,rfl⟩|⟨rfl,rfl⟩
   ·rcases ix with rfl|rfl<;>rcases jx with rfl|rfl
    ·exact g.ne rfl
    ·exact isoL _ g.symm
    ·exact isoL _ g
    ·exact g.ne rfl
   ·exact ix.elim (Ne.symm z) pl
   ·exact jx.elim (Ne.symm z) pl
end PEqualNP.MetaComplexity.NestedCover.A3
namespace PEqualNP.MetaComplexity.NestedCover.Ag
open Ac PEqualNP.CircuitLowerBounds
lemma tG {n:ℕ} {K K':SimpleGraph (Fin n)} [DecidableRel K'.Adj]
  {A:Finset (Fin n)} {P:Circuit} {p l:Fin n} {b h j a:ℕ}
  (s:At P l false b h j a)
  (i:IsNestedCoverCircuit n K A (bT n P b l.val j a))
  (rb:ReadsBack n P) (c:circuitFun n P=graphFun K' A)
  (outside:∀T,IsMinCover K T→p∉T)
  (only:∀u v,K.Adj p u→K.Adj p v→u=v)
  (iso:∀u∈A,∀v,¬K.Adj u v) (e:∀v,¬K.Adj l v)
  (f:l∉A) (g:p∉A) (m:K.CliqueFree 3)
  (ext:∀u v,K'.Adj u v↔K.Adj u v∨(u=p∧v=l)∨(u=l∧v=p)):
  IsNestedCoverCircuit n K' A P:=by
 obtain⟨d,eM⟩:=i;have o:=A3.wM s eM rb g (outside _ eM.2.1) only
  e f iso ext c
 have F:TwoFresh n (bT n P b l.val j a) P p l (cN b j) (cN (n+b) (n+j))
   b (skip b j) (contract (n+b) l.val a):=by
  refine⟨pY s.realB s.realD,fun k=>(zP b j k).1,Ne.symm (fA b j),rb,fun v=>nJ v b j,s.opB,?_,s.opD,?_⟩
  ·simpa only[o,or_comm] using(show(gateAt P b).inputs=[l.val,h]∨(gateAt P b).inputs=[h,l.val] from s.pairB)
  ·rw[s.mapA];exact s.pairD.symm
 exact rB eM s.splice F outside iso e f g m ext c
end PEqualNP.MetaComplexity.NestedCover.Ag
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
structure TrueGraph (K K' : SimpleGraph (Fin n)) (p l q : Fin n) : Prop where
  pl : p ≠ l
  pq : p ≠ q
  lq : l ≠ q
  isoP : ∀ v, ¬ K.Adj p v
  isoL : ∀ v, ¬ K.Adj l v
  ext : ∀ u v, K'.Adj u v ↔ K.Adj u v ∨ (u = p ∧ (v = l ∨ v = q)) ∨ (v = p ∧ (u = l ∨ u = q))
def qL (n:ℕ) (p:Fin n) (ear:Option ℕ):ℕ:=match ear with | none=>p.val | some k=>n+k
noncomputable def aA (d:NCCData n) (p l q:Fin n) (f w:ℕ ↪ ℕ)
  (i j H:ℕ) (ear:Option ℕ):NCCData n where
 cover:=insert p d.cover
 owns u v:=if u=p then decide (v=l∨v=q) else d.owns u v
 tie u:=if u=q∧ear.isSome then some p else d.tie u
 role k:=if k=i then(.o,p.val) else if k=j then(.b,p.val) else if ear=some (Function.invFun f k) then(.z,p.val) else d.role (Function.invFun f k)
 bw u:=if u=p then n+j else w (d.bw u)
 zroot u:=if u=p then w (qL n p ear) else w (d.zroot u)
 oroot u:=if u=p then n+i else w (d.oroot u)
 lam u v:=if u=p then(if v=q then w H else v.val) else w (d.lam u v)
structure TruePins (n : ℕ) (C D : Circuit) (d : NCCData n) (p l q : Fin n)
    (f w : ℕ ↪ ℕ) (i j H : ℕ) (ear : Option ℕ) : Prop where
  range : Finset.range D.gates.length = insert i (insert j ((Finset.range C.gates.length).map f))
  gaps : ∀ k, f k ≠ i ∧ f k ≠ j
  ij : i ≠ j
  fixed : ∀ v : Fin n, w v.val = v.val
  align : ∀ k, w (n+k) = n+f k
  back : ReadsBack n D
  oldOp : ∀ k < C.gates.length, (gateAt D (f k)).op = (gateAt C k).op
  oldNative : ∀ k < C.gates.length, (d.role k).1 ≠ .top →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map w
  oldTop : ∀ k < C.gates.length, (d.role k).1 = .top →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map
      (fun z => if z=qL n p ear then n+j else w z)
  out : D.output = if C.output=qL n p ear then n+j else w C.output
  iOp : (gateAt D i).op = .or
  jOp : (gateAt D j).op = .and
  iIns : (gateAt D i).inputs = [l.val,w H] ∨ (gateAt D i).inputs = [w H,l.val]
  jIns : (gateAt D j).inputs = [w (qL n p ear),n+i] ∨ (gateAt D j).inputs = [n+i,w (qL n p ear)]
  earTop : ∀ k, ear=some k → k ∈ topGates d C
  earIns : ∀ k, ear=some k → (gateAt C k).inputs = [p.val,d.bw q] ∨
    (gateAt C k).inputs = [d.bw q,p.val]
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K : SimpleGraph (Fin n)} {D C : Circuit} {d : NCCData n}
  {A : Finset (Fin n)} {p l q : Fin n} {f w : ℕ ↪ ℕ} {i j H : ℕ} {ear : Option ℕ}
structure TrueLabels (n : ℕ) (C : Circuit) (d : NCCData n) (q : Fin n)
    (H : ℕ) (ear : Option ℕ) : Prop where
  Hform : if q ∈ d.cover then
    IsCentred n C d H ∧ (H = q.val ∨ ∃ k < C.gates.length, H = n+k ∧ d.role k = (.z,q.val))
    else H = q.val
  tied : ear.isSome → q ∈ d.cover ∧ d.tie q = none ∧ H = d.zroot q
lemma iBound (P:(TruePins n C D d p l q f w i j H ear)):i<D.gates.length:=Finset.mem_range.mp (P.range▸Finset.mem_insert_self ..)
lemma jBound (P:(TruePins n C D d p l q f w i j H ear)):j<D.gates.length:=Finset.mem_range.mp (P.range▸Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
lemma oldBound (P:(TruePins n C D d p l q f w i j H ear)) {k} (a:k<C.gates.length):f k<D.gates.length:=
 Finset.mem_range.mp (P.range▸Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
  (Finset.mem_map.mpr ⟨k,Finset.mem_range.mpr a,rfl⟩)))
lemma qM (P:(TruePins n C D d p l q f w i j H ear)) (k):
  (aA d p l q f w i j H ear).role (f k)=if ear=some k then(.z,p.val) else d.role k:=by
 simp[aA,(P.gaps k).1,(P.gaps k).2,Function.leftInverse_invFun f.injective k]
lemma jZ (P:(TruePins n C D d p l q f w i j H ear)) {k} (b:(d.role k).1≠ .top):
  (aA d p l q f w i j H ear).role (f k)=d.role k:=by
 rw[qM P,ite_eq_right];exact fun a=>b ((Finset.mem_filter.mp (P.earTop k a)).2)
lemma xK (P:(TruePins n C D d p l q f w i j H ear)):n+j∉Set.range w:=by
 rintro⟨v,c⟩;by_cases e:v<n
 ·have a:=P.fixed ⟨v,e⟩;change w v=v at a;omega
 ·have a:n+(v-n)=v:=by omega
  have b:=P.align (v-n);rw[a,c] at b;have:=(P.gaps (v-n)).2;omega
lemma aBn (P:(TruePins n C D d p l q f w i j H ear)) (Q:Kind×ℕ→Prop) [DecidablePred Q]:
  (Finset.range D.gates.length).filter (fun k=>Q ((aA d p l q f w i j H ear).role k))=
    (if Q (.o,p.val) then insert i else id)
      ((if Q (.b,p.val) then insert j else id)
      (((Finset.range C.gates.length).filter (fun k=>
          Q (if ear=some k then(.z,p.val) else d.role k))).map f)):=by
 classical
 have a:(aA d p l q f w i j H ear).role i=(.o,p.val):=by simp[aA]
 have c:(aA d p l q f w i j H ear).role j=(.b,p.val):=by simp[aA,Ne.symm P.ij]
 rw[P.range,Finset.filter_insert,Finset.filter_insert,Finset.filter_map];simp only[Function.comp_def,qM P,a,c]
 split_ifs<;>rfl
lemma yL (P:(TruePins n C D d p l q f w i j H ear)) (u:Fin n) (up:u≠p) (a:Kind)
  (e:a≠ .top):
  gatesOf (aA d p l q f w i j H ear) D a u.val=(gatesOf d C a u.val).map f:=by
 have c:p.val≠u.val:=fun b=>up (Fin.ext b.symm)
 unfold gatesOf;rw[aBn P (· =(a,u.val))];simp only[Prod.mk.injEq,c,and_false,↓reduceIte,id_eq];congr 1;apply Finset.filter_congr;intro k _;split
 ·have hh:=(Finset.mem_filter.mp (P.earTop _ ‹ear=some k›)).2;have g:d.role k≠(a,u.val):=fun b=>e ((congrArg Prod.fst b).symm.trans hh)
  simp[c,g]
 ·rfl
lemma wN (v:Valid n K (insert p A) C d) (e:p∉d.cover)
  (a:Kind) (g:a≠ .top) {k} (c:k<C.gates.length):d.role k≠(a,p.val):=by
 intro b;rcases v.2.2.2.2.1 k c with top|⟨u,f,snd,_⟩
 ·exact g ((congrArg Prod.fst b).symm.trans top)
 ·exact e ((Fin.ext (snd.symm.trans (congrArg Prod.snd b)))▸f)
def fY (f:ℕ ↪ ℕ):Option ℕ→Finset ℕ
 | none=> ∅
 | some k=>{f k}
lemma aBo (P:(TruePins n C D d p l q f w i j H ear)) (v:Valid n K (insert p A) C d) (c:p∉d.cover):
  gatesOf (aA d p l q f w i j H ear) D .z p.val=fY f ear:=by
 unfold gatesOf;rw[aBn P (· =(.z,p.val))];simp only[Prod.mk.injEq,reduceCtorEq,false_and,↓reduceIte,id_eq];ext z;rw[Finset.mem_map]
 cases eq:ear with
 | none=>
   simp only[fY,reduceCtorEq,ite_false,Finset.mem_filter,Finset.mem_range,Finset.notMem_empty,iff_false,not_exists,not_and];rintro k ⟨b,a⟩;exact(wN v c _ (by decide) b a).elim
 | some u=>
   simp only[fY,Option.some.injEq,Finset.mem_singleton,Finset.mem_filter,Finset.mem_range];constructor
   ·rintro⟨k,⟨b,a⟩,rfl⟩
    split at a
    ·simp_all
    ·exact(wN v c _ (by decide) b a).elim
   ·rintro rfl;exact⟨u,⟨Finset.mem_range.mp (Finset.mem_filter.mp (P.earTop _ eq)).1,by simp⟩,rfl⟩
lemma aBp (P:(TruePins n C D d p l q f w i j H ear)) (v:Valid n K (insert p A) C d) (e:p∉d.cover):
  gatesOf (aA d p l q f w i j H ear) D .o p.val={i}:=by
 unfold gatesOf;rw[aBn P (· =(.o,p.val))];simp only[eq_self,Prod.mk.injEq,reduceCtorEq,false_and,↓reduceIte,id_eq];have a:(Finset.range C.gates.length).filter (fun k=>
   (if ear=some k then(Kind.z,p.val) else d.role k)=(.o,p.val))= ∅ :=by
  apply Finset.eq_empty_iff_forall_notMem.mpr;intro k b;obtain⟨c,hh⟩:=Finset.mem_filter.mp b
  split at hh
  ·simp at hh
  ·exact wN v e _ (by decide) (Finset.mem_range.mp c) hh
 simp[a]
lemma yM (P:(TruePins n C D d p l q f w i j H ear)):
  topGates (aA d p l q f w i j H ear) D =((match ear with | none=>topGates d C | some k=>(topGates d C).erase k).map f):=by
 unfold topGates;rw[aBn P (·.1= .top)];simp only[reduceCtorEq,ite_false,id_eq];congr 1;ext k;simp only[Finset.mem_filter,Finset.mem_range]
 cases ear with
 | none=>simp
 | some m=>
   simp only[Finset.mem_erase,Finset.mem_filter,Finset.mem_range,Option.some.injEq];by_cases a:m=k
   ·subst k;simp
   ·simp[a,Ne.symm a]
lemma aAp (P:(TruePins n C D d p l q f w i j H ear)) (v:Valid n K (insert p A) C d) (m:p∉d.cover):
  RolesOK n D (aA d p l q f w i j H ear):=by
 intro k h;have a:=P.range▸Finset.mem_range.mpr h;rcases Finset.mem_insert.mp a with rfl|a
 ·exact Or.inr ⟨p,Finset.mem_insert_self ..,by simp[aA],by simp[aA]⟩
 rcases Finset.mem_insert.mp a with rfl|a
 ·exact Or.inr ⟨p,Finset.mem_insert_self ..,by simp[aA,Ne.symm P.ij],by simp[aA]⟩
 obtain⟨k,b,rfl⟩:=Finset.mem_map.mp a;rw[qM P]
 split
 ·exact Or.inr ⟨p,Finset.mem_insert_self ..,rfl,by simp⟩
 rcases v.2.2.2.2.1 _ (Finset.mem_range.mp b) with hh|⟨u,e,c,g⟩
 ·exact Or.inl hh
 ·have up:u≠p:=fun c=>m (c▸e)
  exact Or.inr ⟨_,Finset.mem_insert_of_mem e,c,fun hh=>by simpa[aA,up] using(congrArg w (g hh)).trans (P.align _)⟩
lemma aAq (P:(TruePins n C D d p l q f w i j H ear)) {u} (up:u≠p) (g:TermOK n C d u):TermOK n D (aA d p l q f w i j H ear) u:=by
 obtain⟨k,b,bw,e,op,c⟩:=g;have a:(d.role k).1≠ .top:=by simp[e]
 refine⟨f k,oldBound P b,?_,(jZ P a).trans e,(P.oldOp k b).trans op,?_⟩
 ·simpa[aA,up,bw] using P.align k
 ·rw[P.oldNative k b a];rcases c with hh|hh<;>simp[hh,aA,up]
lemma aCd (P:(TruePins n C D d p l q f w i j H ear)):TermOK n D (aA d p l q f w i j H ear) p:=by exact⟨j,jBound P,by simp[aA],by simp[aA,Ne.symm P.ij],P.jOp,by simpa[aA] using P.jIns⟩
lemma xL (P:(TruePins n C D d p l q f w i j H ear)) {u:Fin n} (up:u≠p) {a:Kind} (c:a≠ .top)
  {L:Finset ℕ} {ρ:ℕ} (tr:IsOrTree n C (gatesOf d C a u.val) L ρ):
  IsOrTree n D (gatesOf (aA d p l q f w i j H ear) D a u.val) (L.map w) (w ρ):=by
 rw[yL P _ up _ c];apply Am.aX.mp (Am.fV (Am.aX.mpr tr) f w
  (fun k _=>P.align k) _ _)
 ·intro k b;exact P.oldOp k (Finset.mem_range.mp (Finset.mem_filter.mp b).1)
 ·intro k b;obtain⟨g,e⟩:=Finset.mem_filter.mp b;exact P.oldNative _ (Finset.mem_range.mp g) (by simpa[e] using c)
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {A : Finset (Fin n)} {K K' : SimpleGraph (Fin n)}
  {C : Circuit} {d : NCCData n} {p l q : Fin n} {f w : ℕ ↪ ℕ}
  {i j H : ℕ} {ear : Option ℕ}
lemma gX (h:Valid n K A C d) {t:Fin n} (iso:∀v,¬K.Adj t v):
  t∉d.cover:=by
 intro ht;have b:K.IsVertexCover (↑(d.cover.erase t):Set (Fin n)):=by
  intro u v e;have f:u≠t:=fun a=>iso v (a▸e)
  have g:v≠t:=fun a=>iso u (a▸e.symm)
  simpa[f,g] using h.2.1.1 e
 have c:=h.2.1.2 _ b;have i:=Finset.card_erase_lt_of_mem ht;omega
lemma dE (h:Valid n K A C d) (a:TrueGraph K K' p l q):
  p∉d.cover:=
 gX h a.isoP
lemma yN (h:Valid n K A C d) (a:TrueGraph K K' p l q):
  l∉d.cover:=
 gX h a.isoL
lemma aJ {t:Fin n}:
  t∈(aA d p l q f w i j H ear).cover↔t=p∨t∈d.cover:=
 Finset.mem_insert
lemma cP {t:Fin n}:
  (aA d p l q f w i j H ear).owns p t=true↔t=l∨t=q:=by
 simp[aA]
lemma aZ {t v:Fin n} (ht:t≠p):
  (aA d p l q f w i j H ear).owns t v=d.owns t v:=by
 simp[aA,ht]
lemma lG (a:ear.isSome):
  (aA d p l q f w i j H ear).tie q=some p:=by
 simp[aA,a]
lemma eU {t:Fin n} (ht:¬(t=q∧ear.isSome)):
  (aA d p l q f w i j H ear).tie t=d.tie t:=by
 simp[aA,ht]
lemma nO (h:Valid n K A C d) (b:TrueGraph K K' p l q) {t:Fin n}:
  (aA d p l q f w i j H ear).tie t=some p↔t=q∧ear.isSome:=by
 by_cases ht:t=q∧ear.isSome
 ·simp[aA,ht]
 ·refine iff_of_false (fun c=> ?_) ht;have a:d.tie t=some p:=(eU ht).symm.trans c;exact dE h b (h.2.2.1.1 _ _ (h.2.2.2.1 _ _ a).2).2
lemma yO (h:Valid n K A C d) (a:TrueGraph K K' p l q):
  IsMinCover K' (aA d p l q f w i j H ear).cover:=by
 constructor
 ·intro u v e;rcases (a.ext u v).mp e with c|⟨k,_⟩|⟨m,_⟩
  ·rcases h.2.1.1 c with k|m
   ·exact Or.inl (aJ.mpr (Or.inr k))
   ·exact Or.inr (aJ.mpr (Or.inr m))
  ·exact Or.inl (aJ.mpr (Or.inl k))
  ·exact Or.inr (aJ.mpr (Or.inl m))
 ·intro S o
  let T:=(S.erase p).erase l
  have z:K.IsVertexCover (↑T:Set (Fin n)):=by
   intro u v e;have s:u≠p:=fun b=>a.isoP v (b▸e)
   have r:u≠l:=fun b=>a.isoL v (b▸e)
   have y:v≠p:=fun b=>a.isoP u (b▸e.symm)
   have x:v≠l:=fun b=>a.isoL u (b▸e.symm)
   have h:=o ((a.ext u v).mpr (Or.inl e));simpa[T,s,r,y,x] using h
  have E:T.card<S.card:=by
   have pl:K'.Adj p l:=(a.ext p l).mpr (Or.inr (Or.inl ⟨rfl,Or.inl rfl⟩));rcases o pl with B|hl
   ·exact(Finset.card_le_card (Finset.erase_subset l (S.erase p))).trans_lt
     (Finset.card_erase_lt_of_mem B)
   ·have g:T⊆S.erase l:=by
     intro t ht;obtain⟨c,ht⟩:=Finset.mem_erase.mp ht;exact Finset.mem_erase.mpr ⟨c,Finset.mem_of_mem_erase ht⟩
    exact(Finset.card_le_card g).trans_lt (Finset.card_erase_lt_of_mem hl)
  have F:=h.2.1.2 T z;change(insert p d.cover).card≤S.card;rw[Finset.card_insert_of_notMem (dE h a)];omega
lemma aAr (h:Valid n K A C d) (b:TrueGraph K K' p l q):
  OwnerOK K' (aA d p l q f w i j H ear):=by
 have a (t:Fin n):d.owns t p≠true:=fun k=>b.isoP t (h.2.2.1.1 _ _ k).1.symm
 constructor
 ·intro u v k;by_cases m:u=p
  ·subst u;exact⟨(b.ext p v).mpr (Or.inr (Or.inl ⟨rfl,cP.mp k⟩)),aJ.mpr (Or.inl rfl)⟩
  ·have s:d.owns u v=true:=by simpa only[aZ m] using k
   obtain⟨e,y⟩:=h.2.2.1.1 _ _ s;exact⟨(b.ext u v).mpr (Or.inl e),aJ.mpr (Or.inr y)⟩
 ·intro u v e;rcases (b.ext u v).mp e with r|⟨z,x⟩|⟨B,m⟩
  ·have c:u≠p:=fun o=>b.isoP v (o▸r)
   have g:v≠p:=fun o=>b.isoP u (o▸r.symm)
   simpa only[aZ c,aZ g] using h.2.2.1.2 _ _ r
  ·subst u;have g:v≠p:=by
    rcases x with rfl|rfl
    ·exact b.pl.symm
    ·exact b.pq.symm
   rw[cP.mpr x,aZ g];exact(a v).symm
  ·subst v;have c:u≠p:=by
    rcases m with rfl|rfl
    ·exact b.pl.symm
    ·exact b.pq.symm
   rw[cP.mpr m,aZ c];exact a u
lemma tH (h:Valid n K A C d) (a:TrueGraph K K' p l q)
  (r:ear.isSome→q∈d.cover):
  IsMinCover K' (aA d p l q f w i j H ear).cover∧OwnerOK K' (aA d p l q f w i j H ear)∧TieOK (aA d p l q f w i j H ear):=by
 refine⟨yO h a,aAr h a,?_⟩;intro u v ht;by_cases k:u=q∧ear.isSome
 ·obtain⟨rfl,c⟩:=k;have m:v=p:=Option.some.inj (ht.symm.trans (lG c));subst v;exact⟨aJ.mpr (Or.inr (r c)),cP.mpr (Or.inr rfl)⟩
 ·have b:d.tie u=some v:=(eU k).symm.trans ht;obtain⟨o,g⟩:=h.2.2.2.1 _ _ b;have m:v≠p:=fun e=>dE h a (e▸(h.2.2.1.1 _ _ g).2)
  exact⟨aJ.mpr (Or.inr o),(aZ m).trans g⟩
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {A : Finset (Fin n)} {K : SimpleGraph (Fin n)}
  {C D : Circuit} {d : NCCData n} {p l q : Fin n} {f w : ℕ ↪ ℕ}
  {i j H k : ℕ} {ear : Option ℕ}
lemma aAs {a:ℕ} {t:Fin n}:
  a∈zLeaves d t↔a=t.val∨∃s∈d.cover,d.tie s=some t∧d.bw s=a:=by
 simp[zLeaves,and_assoc]
lemma oY {a:ℕ}:
  a
   ∈topLeaves d A↔
   (∃s∈A,s.val=a)∨∃s∈d.cover,d.tie s=none∧d.bw s=a:=by
 simp[topLeaves,and_assoc]
lemma kR (h:Valid n K (insert p A) C d) (a:p∉d.cover):
  d.tie p=none:=by
 cases ht:d.tie p with
 | none=>rfl
 | some s=>exact(a (h.2.2.2.1 p s ht).1).elim
lemma gI (h:Valid n K (insert p A) C d) (a:p∉d.cover)
  (s:Fin n):d.tie s≠some p:=
 fun ht=>a (h.2.2.1.1 p s (h.2.2.2.1 s p ht).2).2
lemma lH (h:Valid n K (insert p A) C d) (b:p∉d.cover)
  (a:¬(p=q∧ear.isSome)):(aA d p l q f w i j H ear).tie p=none:=by
 simp[aA,a,kR h b]
lemma vC {t:Fin n} (h:Valid n K (insert p A) C d)
  (P:TruePins n C D d p l q f w i j H ear) (m:p∉d.cover) (r:p≠q)
  (ht:t≠p) (b:ear.isSome→d.tie q=none):
  zLeaves (aA d p l q f w i j H ear) t=(zLeaves d t).map w:=by
 have g (s:Fin n):(aA d p l q f w i j H ear).tie s=some t↔d.tie s=some t:=by
  by_cases hs:s=q∧ear.isSome
  ·obtain⟨rfl,o⟩:=hs;simp[aA,o,b o,Ne.symm ht]
  ·simp[aA,hs]
 ext a;simp only[aAs,Finset.mem_map];constructor
 ·rintro(rfl|⟨s,hs,hst,e⟩)
  ·exact⟨_,Or.inl rfl,P.fixed t⟩
  ·have k:s∈d.cover:=by
    rcases Finset.mem_insert.mp hs with rfl|hs
    ·simp[lH h m (fun u=>r u.1)] at hst
    ·exact hs
   have c:s≠p:=fun e=>m (e▸k)
   exact⟨d.bw s,Or.inr ⟨s,k,(g s).mp hst,rfl⟩,by simpa[aA,c] using e⟩
 ·rintro⟨a,(rfl|⟨s,hs,hst,rfl⟩),rfl⟩
  ·exact Or.inl (P.fixed t)
  ·have c:s≠p:=fun e=>m (e▸hs)
   exact Or.inr ⟨s,Finset.mem_insert_of_mem hs,(g s).mpr hst,by simp[aA,c]⟩
lemma vD {t:Fin n} (ht:t≠p):
  oLeaves (aA d p l q f w i j H ear) t=(oLeaves d t).map w:=by
 ext a;simp[oLeaves,aA,ht]
lemma nP (h:Valid n K (insert p A) C d) (c:p∉d.cover)
  (b:ear=none):zLeaves (aA d p l q f w i j H ear) p={p.val}:=by
 ext a;simp[aAs,aA,b,gI h c]
lemma nQ (h:Valid n K (insert p A) C d) (m:p∉d.cover)
  (b:p≠q) (g:ear=some k) (o:q∈d.cover):
  zLeaves (aA d p l q f w i j H ear) p={p.val,w (d.bw q)}:=by
 have c (s:Fin n):(aA d p l q f w i j H ear).tie s=some p↔s=q:=by
  by_cases hs:s=q
  ·simp[aA,g,hs]
  ·simp[aA,g,hs,gI h m]
 ext a;simp only[aAs,c,Finset.mem_insert,Finset.mem_singleton];constructor
 ·rintro(rfl|⟨s,_,rfl,e⟩)
  ·exact Or.inl rfl
  ·exact Or.inr (by simpa[aA,Ne.symm b] using e.symm)
 ·rintro(rfl|rfl)
  ·exact Or.inl rfl
  ·exact Or.inr ⟨q,Finset.mem_insert_of_mem o,rfl,by simp[aA,Ne.symm b]⟩
lemma vE (b:l≠q):oLeaves (aA d p l q f w i j H ear) p={l.val,w H}:=by
 ext a;simp only[oLeaves,aA,ite_true,decide_eq_true_eq,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton];constructor
 ·rintro⟨r,(rfl|rfl),e⟩
  ·exact Or.inl (by simpa[b] using e.symm)
  ·exact Or.inr (by simpa using e.symm)
 ·rintro(rfl|rfl)
  ·exact⟨l,Or.inl rfl,by simp[b]⟩
  ·exact⟨q,Or.inr rfl,by simp⟩
lemma oI (h:Valid n K (insert p A) C d) {t:Fin n}
  (ht:t∈d.cover) (s:Fin n):d.bw t≠s.val:=by
 obtain⟨b,_,a,_⟩:=(h.2.2.2.2.2.1 t ht).1;have hs:=s.isLt;omega
lemma aAt (h:Valid n K (insert p A) C d) {s t:Fin n}
  (hs:s∈d.cover) (ht:t∈d.cover) (e:d.bw s=d.bw t):s=t:=by
 obtain⟨a,_,i,c,_⟩:=(h.2.2.2.2.2.1 s hs).1;obtain⟨b,_,j,f,_⟩:=(h.2.2.2.2.2.1 t ht).1;have g:a=b:=by omega
 subst b;exact Fin.ext (congrArg Prod.snd (c.symm.trans f))
lemma oJ (h:Valid n K (insert p A) C d) (f:p∉A):
  (topLeaves d (insert p A)).erase p.val=topLeaves d A:=by
 have b:topLeaves d (insert p A)=insert p.val (topLeaves d A):=by ext a;simp[topLeaves,Finset.image_insert]
 have c:p.val∉topLeaves d A:=by
  intro c;rcases oY.mp c with⟨s,hs,e⟩|⟨s,hs,_,e⟩
  ·exact f (Fin.ext e▸hs)
  ·exact oI h hs p e
 rw[b,Finset.erase_insert c]
lemma iO {a:ℕ} (h:Valid n K (insert p A) C d)
  (P:TruePins n C D d p l q f w i j H ear) (m:p∉d.cover)
  (k:¬(p=q∧ear.isSome)):
  a
   ∈topLeaves (aA d p l q f w i j H ear) A↔a=n+j∨
   (∃s∈A,w s.val=a)∨
   ∃s∈d.cover,d.tie s=none∧¬(s=q∧ear.isSome)∧w (d.bw s)=a:=by
 rw[oY];constructor
 ·rintro(⟨s,hs,rfl⟩|⟨s,hs,ht,e⟩)
  ·exact Or.inr (Or.inl ⟨s,hs,P.fixed s⟩)
  ·rcases Finset.mem_insert.mp hs with rfl|hs
   ·exact Or.inl (by simpa[aA] using e.symm)
   ·have c:s≠p:=fun g=>m (g▸hs)
    have b:¬(s=q∧ear.isSome):=by intro o;simp[aA,o] at ht
    exact Or.inr (Or.inr ⟨s,hs,by simpa[aA,b] using ht,b,by simpa[aA,c] using e⟩)
 ·rintro(rfl|⟨s,hs,e⟩|⟨s,hs,ht,b,e⟩)
  ·exact Or.inr ⟨p,Finset.mem_insert_self ..,lH h m k,by simp[aA]⟩
  ·exact Or.inl ⟨s,hs,(P.fixed s).symm.trans e⟩
  ·have c:s≠p:=fun g=>m (g▸hs)
   exact Or.inr ⟨s,Finset.mem_insert_of_mem hs,by simpa[aA,b] using ht,by simpa[aA,c] using e⟩
lemma mA (h:Valid n K (insert p A) C d)
  (P:TruePins n C D d p l q f w i j H ear) (g:p∉d.cover) (c:p∉A)
  (b:ear=none):
  topLeaves (aA d p l q f w i j H ear) A=insert (n+j) (((topLeaves d (insert p A)).erase p.val).map w):=by
 rw[oJ h c];ext a;rw[iO h P g (by simp[b])];simp only[b,Option.isSome_none,Bool.false_eq_true,and_false,not_false_eq_true,true_and,Finset.mem_insert,Finset.mem_map,oY];constructor
 ·rintro(rfl|⟨s,hs,e⟩|⟨s,hs,ht,e⟩)
  ·exact Or.inl rfl
  ·exact Or.inr ⟨s.val,Or.inl ⟨s,hs,rfl⟩,e⟩
  ·exact Or.inr ⟨d.bw s,Or.inr ⟨s,hs,ht,rfl⟩,e⟩
 ·rintro(rfl|⟨a,(⟨s,hs,rfl⟩|⟨s,hs,ht,rfl⟩),e⟩)
  ·exact Or.inl rfl
  ·exact Or.inr (Or.inl ⟨s,hs,e⟩)
  ·exact Or.inr (Or.inr ⟨s,hs,ht,e⟩)
lemma mB (h:Valid n K (insert p A) C d)
  (P:TruePins n C D d p l q f w i j H ear) (r:p∉d.cover) (b:p∉A)
  (c:p≠q) (o:ear=some k) (g:q∈d.cover):
  topLeaves (aA d p l q f w i j H ear) A=insert (n+j) ((((topLeaves d (insert p A)).erase p.val).erase (d.bw q)).map w):=by
 rw[oJ h b];ext a;rw[iO h P r (by simp[c])];simp only[o,Option.isSome_some,and_true,Finset.mem_insert,Finset.mem_map,Finset.mem_erase,oY];constructor
 ·rintro(rfl|⟨s,hs,e⟩|⟨s,hs,ht,hsq,e⟩)
  ·exact Or.inl rfl
  ·exact Or.inr ⟨s.val,⟨(oI h g s).symm,Or.inl ⟨s,hs,rfl⟩⟩,e⟩
  ·exact Or.inr ⟨d.bw s,⟨fun e=>hsq (aAt h hs g e),Or.inr ⟨s,hs,ht,rfl⟩⟩,e⟩
 ·rintro(rfl|⟨a,⟨hne,ha⟩,e⟩)
  ·exact Or.inl rfl
  ·rcases ha with⟨s,hs,rfl⟩|⟨s,hs,ht,rfl⟩
   ·exact Or.inr (Or.inl ⟨s,hs,e⟩)
   ·exact Or.inr (Or.inr ⟨s,hs,ht,fun m=>hne (congrArg d.bw m),e⟩)
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.A5
open PEqualNP.CircuitLowerBounds Am
lemma cS {n G i}:
  aM n G i↔∃j∈G,i=n+j:=by
 constructor
 ·rintro⟨b,a⟩;exact⟨_,a,by omega⟩
 ·rintro⟨j,a,rfl⟩;simpa[aM] using a
lemma wO {n a G L ρ k p q}
  (tr:bN n a G L ρ)
  (back:∀j∈G,∀v∈(a j).inputs,v<n+j)
  (t:k∈G) (B:p∈L) (C:q∈L)
  (s:(a k).inputs=[p,q]∨(a k).inputs=[q,p]):
  bN n a (G.erase k) (insert (n+k) ((L.erase p).erase q)) ρ:=by
 have h {j} (d:j∈G.erase k):j∈G:=(Finset.mem_erase.mp d).2;have sum_erase (v:ℕ):
   aN a (G.erase k) v+(a k).inputs.count v=aN a G v:=
  Finset.sum_erase_add _ _ t
 have m (v:ℕ) (y:v≠p) (A:v≠q):
   aN a (G.erase k) v=aN a G v:=by
  have z:(a k).inputs.count v=0:=by apply List.count_eq_zero_of_not_mem;rcases s with l|l<;>simp[l,y,A]
  simpa[z] using sum_erase v
 have c (v:ℕ) (g:v∈L) (hvk:v∈(a k).inputs) {j:ℕ}
   (d:j∈G.erase k):v∉(a j).inputs:=by
  have sp:=sum_erase v;have O:=(tr.2.1 v g).2;have pos:=List.count_pos_iff.mpr hvk;have x:aN a (G.erase k) v=0:=by split at O<;>omega
  intro Q;have a0:(a j).inputs.count v≤aN a (G.erase k) v:=Finset.single_le_sum (f:=fun z=>(a z).inputs.count v) (fun _ _=>Nat.zero_le _) d;have V:=List.count_pos_iff.mpr Q;omega
 have M:p∈(a k).inputs:=by rcases s with l|l<;>simp[l]
 have N:q∈(a k).inputs:=by rcases s with l|l<;>simp[l]
 have b {j:ℕ} (d:j∈G) {v:ℕ} (g:v∈L):n+j≠v:=by intro R;exact(tr.2.1 v g).1 (cS.mpr ⟨j,d,R.symm⟩)
 have u:∃j∈G,ρ=n+j:=by have E:G≠ ∅ :=Finset.ne_empty_of_mem t;simpa[E] using tr.2.2.2
 refine⟨?_,?_,?_,?_⟩
 ·intro j d;obtain⟨U,H,K⟩:=tr.1 j (h d);refine⟨U,H,?_⟩;intro v g;rcases K v g with hl|o
  ·exact Or.inl (Finset.mem_insert_of_mem
    (Finset.mem_erase.mpr ⟨fun e=>c q C N d (e▸g),
      Finset.mem_erase.mpr ⟨fun e=>c p B M d (e▸g),hl⟩⟩))
  ·obtain⟨i,P,rfl⟩:=cS.mp o;by_cases e:i=k
   ·subst i;exact Or.inl (Finset.mem_insert_self ..)
   ·exact Or.inr (cS.mpr ⟨_,Finset.mem_erase.mpr ⟨e,P⟩,rfl⟩)
 ·intro v g;rcases Finset.mem_insert.mp g with rfl|g
  ·refine⟨?_,(m _ (b t B) (b t C)).trans
    (tr.2.2.1 k t)⟩
   rintro o;obtain⟨j,d,e⟩:=cS.mp o;exact(Finset.mem_erase.mp d).1 (by omega)
  ·have⟨A,y,hl⟩:=Finset.mem_erase.mp g |>.imp_right Finset.mem_erase.mp
   exact⟨fun o=>(tr.2.1 v hl).1 ⟨o.1,h o.2⟩,(m _ y A).trans (tr.2.1 v hl).2⟩
 ·intro j d;have F:=h d;exact(m _ (b F B) (b F C)).trans (tr.2.2.1 j F)
 ·obtain⟨j,d,hr⟩:=u;by_cases l:G.erase k= ∅
  ·rw[ite_eq_left l];have hρ:ρ=n+k:=by
    by_contra ne;have J:j∈G.erase k:=Finset.mem_erase.mpr ⟨by omega,d⟩;simp[l] at J
   rw[hρ];have T:(L.erase p).erase q= ∅ :=by
    apply Finset.eq_empty_iff_forall_notMem.mpr;intro v g;obtain⟨A,g⟩:=Finset.mem_erase.mp g;obtain⟨y,hl⟩:=Finset.mem_erase.mp g;have X:v≠ρ:=by rw[hρ];exact Ne.symm (b t hl)
    have r:=(m _ y A).trans (tr.2.1 v hl).2;simp[l,aN,X] at r
   simp[T]
  ·rw[ite_eq_right l];have E:n+k≠ρ:=by
    intro e;have w:=Finset.nonempty_iff_ne_empty.mpr l
    let z:=(G.erase k).max' w
    have x:z∈G.erase k:=Finset.max'_mem _ w;have Z:n+z≠ρ:=by have:=(Finset.mem_erase.mp x).1;omega
    have r:=(m _ (b (h x) B) (b (h x) C)).trans
     (tr.2.2.1 z (h x))
    have S:aN a (G.erase k) (n+z)=0:=by apply Finset.sum_eq_zero;intro i o;apply List.count_eq_zero_of_not_mem;intro J;have lt:=back i (h o) _ J;have ge:=Finset.le_max' _ _ o;omega
    rw[S,ite_eq_right Z] at r;omega
   exact⟨j,Finset.mem_erase.mpr ⟨by omega,d⟩,hr⟩
def lQ (w:ℕ ↪ ℕ) (p fresh:ℕ):ℕ ↪ ℕ:=⟨fun v=>Equiv.swap (w p) fresh (w v),(Equiv.swap (w p) fresh).injective.comp w.injective⟩
lemma nR (w:ℕ ↪ ℕ) (p fresh:ℕ)
  (a:fresh∉Set.range w) (v:ℕ):
  lQ w p fresh v=if v=p then fresh else w v:=by
 change Equiv.swap (w p) fresh (w v)=_;by_cases h:v=p
 ·subst v;simp
 ·rw[ite_eq_right h];exact Equiv.swap_apply_of_ne_of_ne (fun e=>h (w.injective e)) (fun e=>a ⟨v,e⟩)
lemma lI {n m a b G L ρ p fresh}
  (tr:bN n a G L ρ) (q:p∈L)
  (f w:ℕ ↪ ℕ) (g:fresh∉Set.range w)
  (align:∀j∈G,w (n+j)=m+f j)
  (op:∀j∈G,(b (f j)).op=(a j).op)
  (bS:∀j∈G,(b (f j)).inputs=(a j).inputs.map (fun i=>if i=p then fresh else w i)):
  bN m b (G.map f) (insert fresh ((L.erase p).map w))
   (if ρ=p then fresh else w ρ):=by
 let k:=lQ w p fresh
 have c (v:ℕ):k v=if v=p then fresh else w v:=nR w p fresh g v
 have s (j:ℕ) (h:j∈G):k (n+j)=m+f j:=by
  have o:n+j≠p:=by intro e;exact(tr.2.1 p q).1 (cS.mpr ⟨j,h,e.symm⟩)
  simpa[c,o] using align j h
 have r:=fV (b:=b) tr f k s op (fun j h=>by rw[bS j h];exact List.map_congr_left (fun v _=>(c v).symm));have u:L.map k=insert fresh ((L.erase p).map w):=by
  ext t;simp only[Finset.mem_map,Finset.mem_insert,Finset.mem_erase,c];constructor
  ·rintro⟨v,l,e⟩;by_cases d:v=p
   ·exact Or.inl (by simpa[d] using e.symm)
   ·exact Or.inr ⟨v,⟨d,l⟩,by simpa[d] using e⟩
  ·rintro(rfl|⟨v,⟨d,l⟩,rfl⟩)
   ·exact⟨p,q,by simp⟩
   ·exact⟨v,l,by simp[d]⟩
 rwa [u,c] at r
lemma oU {n m C D G L ρ p fresh}
  (tr:IsOrTree n C G L ρ) (b:p∈L)
  (f w:ℕ ↪ ℕ) (a:fresh∉Set.range w)
  (align:∀j∈G,w (n+j)=m+f j)
  (op:∀j∈G,(gateAt D (f j)).op=(gateAt C j).op)
  (bS:∀j∈G,(gateAt D (f j)).inputs=
    (gateAt C j).inputs.map (fun i=>if i=p then fresh else w i)):
  IsOrTree m D (G.map f) (insert fresh ((L.erase p).map w))
   (if ρ=p then fresh else w ρ):=
 aX.mp (lI (aX.mpr tr) b f w a align op bS)
lemma rC {n m C D G L ρ k p q fresh}
  (tr:IsOrTree n C G L ρ) (back:ReadsBack n C)
  (aT:∀j∈G,j<C.gates.length)
  (d:k∈G) (l:p∈L) (o:q∈L)
  (c:(gateAt C k).inputs=[p,q]∨(gateAt C k).inputs=[q,p])
  (f w:ℕ ↪ ℕ) (a:fresh∉Set.range w)
  (align:∀j∈G.erase k,w (n+j)=m+f j)
  (op:∀j∈G.erase k,(gateAt D (f j)).op=(gateAt C j).op)
  (bS:∀j∈G.erase k,(gateAt D (f j)).inputs=
    (gateAt C j).inputs.map (fun i=>if i=n+k then fresh else w i)):
  IsOrTree m D ((G.erase k).map f) (insert fresh (((L.erase p).erase q).map w))
   (if ρ=n+k then fresh else w ρ):=by
 have b:=wO (aX.mpr tr) (fun j g=>back j (aT j g)) d l o c;have r:n+k∈insert (n+k) ((L.erase p).erase q):=Finset.mem_insert_self ..;have e:n+k∉(L.erase p).erase q:=fun h=>
  (tr.2.1 _ ((Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2)).1
    (cS.mpr ⟨k,d,rfl⟩)
 rw[←aX];simpa[Finset.erase_insert e] using lI b r f w a align op bS
end PEqualNP.MetaComplexity.NestedCover.A5
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K K' : SimpleGraph (Fin n)} {D C : Circuit} {d : NCCData n}
  {A : Finset (Fin n)} {p l q : Fin n} {f w : ℕ ↪ ℕ} {i j H : ℕ} {ear : Option ℕ}
lemma xM {k a b:ℕ} (back:ReadsBack n D) (f:k<D.gates.length)
  (op:(gateAt D k).op= .or) (d:(gateAt D k).inputs=[a,b]∨
    (gateAt D k).inputs=[b,a]) (e:a≠b):
  IsOrTree n D {k} {a,b} (n+k):=by
 have g:a<n+k:=back k f a (by rcases d with c|c<;>simp[c]);have h:b<n+k:=back k f b (by rcases d with c|c<;>simp[c]);have i:¬(n≤a∧a-n=k):=by omega
 have j:¬(n≤b∧b-n=k):=by omega
 rcases d with c|c<;>simp[IsOrTree,readsIn,op,c,e,Ne.symm e,ne_of_lt g,ne_of_lt h]<;>omega
lemma rY (P:(TruePins n C D d p l q f w i j H ear)) (v:Valid n K (insert p A) C d) (a:TrueGraph K K' p l q)
  (Lab:(TrueLabels n C d q H ear)) {u} (c:u∈d.cover):
  IsOrTree n D (gatesOf (aA d p l q f w i j H ear) D .z u.val) (zLeaves (aA d p l q f w i j H ear) u) ((aA d p l q f w i j H ear).zroot u)∧
  IsOrTree n D (gatesOf (aA d p l q f w i j H ear) D .o u.val) (oLeaves (aA d p l q f w i j H ear) u) ((aA d p l q f w i j H ear).oroot u):=by
 have b:=dE v a;have up:u≠p:=fun e=>b (e▸c)
 obtain⟨_,k,h,_⟩:=v.2.2.2.2.2.1 u c;rw[vC v P b a.pq up (fun g=>(Lab.tied g).2.1),vD up];simpa only[aA,ite_eq_right up] using And.intro
  (xL P up (by decide:Kind.z≠ .top) k)
  (xL P up (by decide:Kind.o≠ .top) h)
lemma aCe (c:TrueGraph K K' p l q) (Lab:(TrueLabels n C d q H ear)):l.val≠H:=by
 by_cases e:q∈d.cover
 ·have hh:=Lab.Hform;simp only[e,↓reduceIte] at hh;rcases hh.2 with a|⟨k,_,a,_⟩
  ·exact fun b=>c.lq (Fin.ext (b.trans a))
  ·have:=l.isLt;omega
 ·have a:H=q.val:=by simpa[e] using Lab.Hform
  exact fun b=>c.lq (Fin.ext (b.trans a))
lemma aAu (P:(TruePins n C D d p l q f w i j H ear)) (v:Valid n K (insert p A) C d) (a:TrueGraph K K' p l q)
  (Lab:(TrueLabels n C d q H ear)):
  IsOrTree n D (gatesOf (aA d p l q f w i j H ear) D .o p.val) (oLeaves (aA d p l q f w i j H ear) p) ((aA d p l q f w i j H ear).oroot p):=by
 rw[aBp P v (dE v a),vE a.lq];have b:l.val≠w H:=fun hh=>aCe a Lab (w.injective ((P.fixed l).trans hh))
 simpa[aA] using xM P.back (iBound P) P.iOp P.iIns b
lemma aAv (P:(TruePins n C D d p l q f w i j H ear)) (v:Valid n K (insert p A) C d) (m:TrueGraph K K' p l q)
  (Lab:(TrueLabels n C d q H ear)):
  IsOrTree n D (gatesOf (aA d p l q f w i j H ear) D .z p.val) (zLeaves (aA d p l q f w i j H ear) p) ((aA d p l q f w i j H ear).zroot p):=by
 have g:=dE v m;rw[aBo P v g]
 cases ear with
 | none=>
   rw[nP v g rfl];simp[fY,aA,qL,P.fixed,IsOrTree,readsIn]
 | some k=>
   have r:=(Lab.tied rfl).1;have o:=P.earTop _ rfl;have op:=(v.2.2.2.2.2.2.1 _ o).1;obtain⟨e,top⟩:=Finset.mem_filter.mp o;have bS:=P.oldTop k (Finset.mem_range.mp e) top;rw[nQ v g m.pq rfl r];have bw:=(v.2.2.2.2.2.1 q r).1;obtain⟨t,_,u,_,_,_⟩:=bw;have c:=P.earIns k rfl;have a:p.val<n+k:=v.1 _ (Finset.mem_range.mp e) p.val
    (by rcases c with hh|hh<;>simp[hh])
   have b:d.bw q<n+k:=v.1 _ (Finset.mem_range.mp e) (d.bw q)
    (by rcases c with hh|hh<;>simp[hh])
   have h:(gateAt D (f k)).inputs=[p.val,w (d.bw q)]∨
     (gateAt D (f k)).inputs=[w (d.bw q),p.val]:=by
    rw[bS];rcases c with hh|hh<;>simp[hh,qL,ne_of_lt a,ne_of_lt b,P.fixed]
   have s:p.val≠w (d.bw q):=by intro hh;have x:=w.injective ((P.fixed p).trans hh);have:=p.isLt;omega
   simpa[aA,qL,fY,P.align] using xM P.back
    (oldBound P (Finset.mem_range.mp e)) ((P.oldOp _ (Finset.mem_range.mp e)).trans op) h s
lemma aAw (P:(TruePins n C D d p l q f w i j H ear)) (v:Valid n K (insert p A) C d) (h:TrueGraph K K' p l q)
  (Lab:(TrueLabels n C d q H ear)) (c:p∉A):
  IsOrTree n D (topGates (aA d p l q f w i j H ear) D) (topLeaves (aA d p l q f w i j H ear) A) D.output:=by
 have m:=dE v h;have tr:=v.2.2.2.2.2.2;have g:p.val∈topLeaves d (insert p A):=Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_insert_self ..));have bd {k} (a:k∈topGates d C):k<C.gates.length:=Finset.mem_range.mp (Finset.mem_filter.mp a).1;rw[yM P,P.out]
 cases ear with
 | none=>
   rw[mA v P m c rfl];apply A5.oU tr g f w (xK P) (fun k _=>P.align k) (fun k a=>P.oldOp k (bd a));intro k a;rw[P.oldTop _ (bd a) (Finset.mem_filter.mp a).2];apply List.map_congr_left;intro z _;by_cases e:z=p.val<;>simp[qL,e]
 | some k=>
   have b:=Lab.tied rfl;have o:d.bw q∈topLeaves d (insert p A):=Finset.mem_union_right _<|
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨b.1,b.2.1⟩)
   rw[mB v P m c h.pq rfl b.1];apply A5.rC tr v.1 (fun _ a=>bd a) (P.earTop _ rfl) g o
    (P.earIns _ rfl) f w (xK P) (fun k _=>P.align k)
    (fun k a=>P.oldOp k (bd (Finset.mem_of_mem_erase a)))
   intro u r;have hh:=Finset.mem_of_mem_erase r;rw[P.oldTop _ (bd hh) (Finset.mem_filter.mp hh).2];apply List.map_congr_left;intro z _;by_cases e:z=n+k<;>simp[qL,e]
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {A : Finset (Fin n)} {K K' : SimpleGraph (Fin n)}
  {C D : Circuit} {d : NCCData n} {p l q : Fin n} {f w : ℕ ↪ ℕ}
  {i j H : ℕ} {ear : Option ℕ}
lemma oK (P:(TruePins n C D d p l q f w i j H ear)) (rb:ReadsBack n C)
  {v:ℕ} (s:v<n+C.gates.length) (b:IsCentred n C d v):
  IsCentred n D (aA d p l q f w i j H ear) (w v):=by
 induction v using Nat.strong_induction_on with
 | ind v ih=>
   by_cases h:v<n
   ·let r:Fin n:=⟨v,h⟩
    change IsCentred n D (aA d p l q f w i j H ear) (w r.val);rw[P.fixed,aG];exact Finset.mem_insert_of_mem ((aG r).1 b)
   ·obtain⟨k,rfl⟩:∃k,v=n+k:=⟨v-n,by omega⟩
    have a:k<C.gates.length:=by omega
    obtain⟨o,y,m,c⟩:=(aR rb a).1 b;have g:(d.role k).1≠ .top:=by rw[o];decide
    have e:=rb k a y m;rw[P.align,aR P.back (oldBound P a),jZ P g,P.oldNative k a g];exact⟨o,w y,List.mem_map.mpr ⟨y,m,rfl⟩,ih y e (by omega) c⟩
lemma oL (P:(TruePins n C D d p l q f w i j H ear)) (rb:ReadsBack n C) {v:Fin n} {z:ℕ}
  (b:IsCentred n C d z)
  (a:z=v.val∨∃k<C.gates.length,z=n+k∧d.role k=(.z,v.val)):
  IsCentred n D (aA d p l q f w i j H ear) (w z)∧(w z=v.val∨∃k<D.gates.length,w z=n+k∧(aA d p l q f w i j H ear).role k=(.z,v.val)):=by
 rcases a with rfl|⟨k,c,rfl,hr⟩
 ·exact⟨oK P rb (by have:=v.isLt;omega) b,Or.inl (P.fixed v)⟩
 ·have e:(d.role k).1≠ .top:=by simp[hr]
  exact⟨oK P rb (by omega) b,Or.inr ⟨f k,oldBound P c,P.align k,(jZ P e).trans hr⟩⟩
lemma aCf (h:Valid n K (insert p A) C d) (P:(TruePins n C D d p l q f w i j H ear))
  (c:TrueGraph K K' p l q) (Lab:TrueLabels n C d q H ear):
  ∀u∈(aA d p l q f w i j H ear).cover,∀v,(aA d p l q f w i j H ear).owns u v=true→LamOK n D (aA d p l q f w i j H ear) u v:=by
 intro u G v x;by_cases up:u=p
 ·subst u;rcases cP.mp x with ev|ev
  ·subst v;have hl:l∉(aA d p l q f w i j H ear).cover:=fun k=>
    (aJ.mp k).elim c.pl.symm (yN h c)
   rw[LamOK,ite_eq_right hl];simp[aA,c.lq]
  ·subst v;have lq:(aA d p l q f w i j H ear).lam p q=w H:=by simp[aA]
   by_cases m:q∈d.cover
   ·have a:q∈(aA d p l q f w i j H ear).cover:=aJ.mpr (Or.inr m);rw[LamOK,ite_eq_left a,lq];obtain⟨s,hs⟩:=ite_eq_left m▸Lab.Hform;obtain⟨t,y⟩:=oL P h.1 s hs;refine⟨t,y,fun ht=> ?_⟩;have g:=((nO h c).mp ht).2;simp[aA,c.pq.symm,(Lab.tied g).2.2]
   ·have a:q∉(aA d p l q f w i j H ear).cover:=fun k=>
     (aJ.mp k).elim c.pq.symm m
    have g:H=q.val:=by simpa only[ite_eq_right m] using Lab.Hform
    rw[LamOK,ite_eq_right a,lq,g,P.fixed]
 ·have B:=(aJ.mp G).resolve_left up;have r:d.owns u v=true:=(aZ up).symm.trans x;have e:=(h.2.2.1.1 _ _ r).1;have E:v≠p:=fun F=>c.isoP u (F▸e.symm)
  have hl:(aA d p l q f w i j H ear).lam u v=w (d.lam u v):=by simp[aA,up]
  have b:=(h.2.2.2.2.2.1 u B).2.2.2 v r;by_cases o:v∈d.cover
  ·have a:v∈(aA d p l q f w i j H ear).cover:=aJ.mpr (Or.inr o);rw[LamOK,ite_eq_left o] at b;rw[LamOK,ite_eq_left a,hl];obtain⟨s,hs⟩:=oL P h.1 b.1 b.2.1;refine⟨s,hs,fun ht=> ?_⟩;have g:¬(v=q∧ear.isSome):=by
    rintro⟨rfl,g⟩;exact up (Option.some.inj (ht.symm.trans (lG g)))
   have z:=(eU g).symm.trans ht;simp[aA,E,b.2.2 z]
  ·have a:v∉(aA d p l q f w i j H ear).cover:=fun k=>(aJ.mp k).elim E o
   rw[LamOK,ite_eq_right o] at b;rw[LamOK,ite_eq_right a,hl,b,P.fixed]
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K K' : SimpleGraph (Fin n)} {D C : Circuit} {d : NCCData n}
  {A : Finset (Fin n)} {p l q : Fin n} {f w : ℕ ↪ ℕ} {i j H : ℕ} {ear : Option ℕ}
lemma eM (h:Valid n K (insert p A) C d) (P:TruePins n C D d p l q f w i j H ear)
  (b:TrueGraph K K' p l q) (Lab:TrueLabels n C d q H ear) (g:p∉A):
  Valid n K' A D (aA d p l q f w i j H ear):=by
 obtain⟨r,s,t⟩:=tH (f:=f) (w:=w) (i:=i) (j:=j) (H:=H)
  h b (fun m=>(Lab.tied m).1)
 have e:=dE h b;refine⟨P.back,r,s,t,aAp P h e,?_,aAw P h b Lab g⟩;intro u c;refine⟨?_,?_,?_,fun _ o=>aCf h P b Lab u c _ o⟩
 ·rcases Finset.mem_insert.mp c with rfl|a
  ·exact aCd P
  ·exact aAq P (fun k=>e (k▸a)) (h.2.2.2.2.2.1 u a).1
 ·rcases Finset.mem_insert.mp c with rfl|a
  ·exact aAv P h b Lab
  ·exact(rY P h b Lab a).1
 ·rcases Finset.mem_insert.mp c with rfl|a
  ·exact aAu P h b Lab
  ·exact(rY P h b Lab a).2
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Aw
open PEqualNP.CircuitLowerBounds
open Af Aj
variable {n : ℕ} {K : SimpleGraph (Fin n)} {C : Circuit} {d : NCCData n}
    {A : Finset (Fin n)} {q t u : Fin n} {H : ℕ}
lemma bA (h:Valid n K A C d) (ht:t∈d.cover):
  ∃r∉d.cover,d.owns t r=true:=by
 classical
 by_contra! hh;have i:=h.2.2.1;have c (r:Fin n) (j:K.Adj t r):r∈d.cover.erase t:=by
  refine Finset.mem_erase.mpr ⟨j.ne.symm,?_⟩;by_contra hr;have rev:d.owns r t≠true:=fun e=>hr (i.1 r t e).2
  have diff:=i.2 t r j
  cases e:d.owns t r<;>cases f:d.owns r t<;>simp_all
 have g:K.IsVertexCover (↑(d.cover.erase t):Set (Fin n)):=by
  intro a b edge;rcases h.2.1.1 edge with k|l
  ·by_cases e:a=t
   ·exact Or.inr (c b (e▸edge))
   ·exact Or.inl (Finset.mem_erase.mpr ⟨e,k⟩)
  ·by_cases e:b=t
   ·exact Or.inl (c a (e▸edge.symm))
   ·exact Or.inr (Finset.mem_erase.mpr ⟨e,l⟩)
 exact(not_le_of_gt (Finset.card_erase_lt_of_mem ht)) (h.2.1.2 _ g)
lemma vF (h:Valid n K A C d) (st:SwapOK d t q) (f:SwapOK d u q):
  u=t:=by
 by_contra b;have a:=(h.2.2.1.1 _ _ f.edge).2;have i:u≠q:=fun e=>st.outside (e▸a)
 obtain⟨r,hr,g⟩:=bA (Aj.eM h st)
  (t:=u) (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨b,a⟩))
 have c:d.owns u r=true:=by simpa[aB,i,b] using g
 exact hr (f.single _ c▸Finset.mem_insert_self q (d.cover.erase t))
def Signal (d:NCCData n) (C:Circuit) (q:Fin n) (H:ℕ):Prop:=H=q.val∨q∈d.cover∧IsCentred n C d H∧∃j∈Z q d C,H=n+j
lemma vG (c:q∈d.cover) (hs:Signal d C q H):
  dP q d C H∧IsCentred n C d H:=by
 rcases hs with rfl|⟨_,a,b⟩
 ·exact⟨Or.inl (dF.mpr (.inl rfl)),(aG q).2 c⟩
 ·exact⟨Or.inr b,a⟩
lemma oM (h:Valid n K A C d) (iF:Signal d C q H)
  {r:Fin n} (edge:d.owns t r=true) (free:d.tie t=none)
  (a:W C (pair t r) H):q=t∨q=r:=by
 rcases iF with rfl|⟨c,_,b⟩
 ·exact of_decide_eq_true ((aC q).1 a)
 ·exact((zQ h edge free c (.inr b)).1 a).2
def aCm (d:NCCData n) (q:Fin n) (H:ℕ) (U:Fin n→Prop):Prop:=
 (∀t,¬U t)∨
 (q∈d.cover∧d.tie q=none∧H=d.zroot q∧∀t,U t↔t=q)∨
 ∃t,SwapOK d t q∧H=q.val∧∀u,U u↔u=t
lemma aBq (h:Valid n K A C d) (iF:Signal d C q H)
  {U:Fin n→Prop} (free:∀t,U t→t∈d.cover∧d.tie t=none)
  (a:∀t r,U t→d.owns t r=true→W C (pair t r) H)
  (f:U q→∀s r,d.tie s=some q→ r∉d.cover→
    d.owns s r=true→W C (pair s r) H):aCm d q H U:=by
 classical
 by_cases empty:∀t,¬U t
 ·exact Or.inl empty
 push Not at empty
 obtain⟨t,ht⟩:=empty;by_cases g:q∈d.cover
 ·have only(u:Fin n) (c:U u):u=q:=by
   obtain⟨r,hr,b⟩:=bA h (free u c).1;exact((oM h iF b (free u c).2 (a u r c b)).resolve_right
    (fun e=>hr (e▸g))).symm
  have i:U q:=only _ ht▸ht;have l:=(free q i).2;obtain⟨o,m⟩:=vG g iF;have k:H=d.zroot q:=by apply kQ h g l o m;intro s hs τ;obtain⟨r,hr,b⟩:=bA h hs;exact⟨r,hr,b,f i s r τ hr b⟩
  exact Or.inr (Or.inl ⟨g,l,k,fun u=>⟨only u,fun e=>e▸i⟩⟩)
 ·have swap (u:Fin n) (c:U u):SwapOK d u q:=by
   have j:=(free u c).1;have i:q≠u:=fun e=>g (e▸j)
   have only r b:=((oM h iF b (free u c).2
    (a u r c b)).resolve_left i).symm
   obtain⟨r,_,b⟩:=bA h j;exact⟨g,only r b▸b,only,(free u c).2⟩
  have st:=swap t ht;exact Or.inr (Or.inr ⟨t,st,iF.resolve_right (fun hs=>g hs.1),fun u=>⟨fun c=>vF h st (swap u c),fun e=>e▸ht⟩⟩)
section TreeShape
variable {G L : Finset ℕ} {ρ a b z : ℕ}
  (tr : IsOrTree n C G L ρ) (back : ReadsBack n C) (bd : ∀ j ∈ G, j < C.gates.length)
include tr back bd
lemma qN (d:Below n C G a b) (c:Below n C G a z) (le:b≤z):
  Below n C G b z:=by
 induction d generalizing z with
 | refl=>exact c
 | @step i j bi hj hi ih=>
   have lt:=(back j (bd j hj) i hi).trans_le le;exact(ih c lt.le).advance (ne_of_lt lt) tr hj hi
lemma rZ {j:ℕ} (c:j∈G) (d:a∈(gateAt C j).inputs)
  (e:b∈(gateAt C j).inputs) (f:a≠b):
  ¬(Below n C G z a∧Below n C G z b):=by
 rintro⟨g,h⟩;rcases le_total a b with le|le
 ·exact(not_le_of_gt (back j (bd j c) b e))
   (((qN tr back bd g h le).advance f tr c d).le back bd)
 ·exact(not_le_of_gt (back j (bd j c) a d))
   (((qN tr back bd h g le).advance f.symm tr c e).le back bd)
lemma tI (node:fQ n G L z):∃a∈L,Below n C G a z:=by have h:=(gS tr back bd (fun _=>True) (by intro j c;obtain⟨a,b,e,_⟩:=jP tr c;simp[e]) node).1 trivial;exact⟨h.choose,h.choose_spec.1,h.choose_spec.2.1⟩
lemma tJ (node:fQ n G L z) (only:∀i∈L,Below n C G i z→i=a):
  z=a:=by
 rcases node with leaf|⟨j,d,rfl⟩
 ·exact only _ leaf .refl
 obtain⟨x,e,y,f,g,c,b⟩:=lU tr back bd j d;exact(g ((only _ e c).trans (only _ f b).symm)).elim
lemma rD (node:fQ n G L z)
  (J:Below n C G a z) (K:Below n C G b z) (S:a≠b)
  (only:∀i∈L,Below n C G i z→i=a∨i=b):
  ∃j∈G,z=n+j∧((gateAt C j).inputs=[a,b]∨(gateAt C j).inputs=[b,a]):=by
 rcases node with leaf|⟨j,c,rfl⟩
 ·have d (i) (m:Below n C G i z):i=z:=by
   cases m with
   | refl=>rfl
   | @step i k _ t _=>
     exfalso;exact(tr.2.1 _ leaf).1 ⟨by omega,by simpa using t⟩
  exact(S ((d _ J).trans (d _ K).symm)).elim
 obtain⟨x,y,u,l⟩:=jP tr c;have f:x∈(gateAt C j).inputs:=by simp[u]
 have g:y∈(gateAt C j).inputs:=by simp[u]
 have F {x y:ℕ} (f:x∈(gateAt C j).inputs) (g:y∈(gateAt C j).inputs)
   (l:x≠y):x=a∨x=b:=by
  rcases bZ tr c f with leaf|⟨k,t,rfl⟩
  ·exact only _ leaf (.step .refl c f)
  obtain⟨i,Q,N,E,q,m,o⟩:=lU tr back bd k t;obtain⟨v,R,s⟩:=tI tr back bd (bZ tr c g);have T:=only _ R (s.step c g);have B:=only _ Q (m.step c f);have p:=only _ E (o.step c f);have H:v≠i:=by rintro rfl;exact rZ tr back bd c f g l ⟨m,s⟩
  have r:v≠N:=by rintro rfl;exact rZ tr back bd c f g l ⟨o,s⟩
  rcases T with h|h
  ·have P:=B.resolve_left (fun e=>H (h.trans e.symm));have A:=p.resolve_left (fun e=>r (h.trans e.symm));exact(q (P.trans A.symm)).elim
  ·have O:=B.resolve_right (fun e=>H (h.trans e.symm));have w:=p.resolve_right (fun e=>r (h.trans e.symm));exact(q (O.trans w.symm)).elim
 refine⟨j,c,rfl,?_⟩;rcases F f g l with h|h<;>rcases F g f l.symm with M|M<;>simp_all
end TreeShape
section TopShape
variable {p : Fin n} {w : ℕ}
abbrev tK (d:NCCData n) (C:Circuit) (w:ℕ) (t:Fin n):Prop:=t∈d.cover∧d.tie t=none∧Below n C (topGates d C) (d.bw t) w
abbrev bK (d:NCCData n) (C:Circuit) (A:Finset (Fin n)) (w:ℕ):=fQ n (topGates d C) (topLeaves d A) w
lemma iY (d:NCCData n) (C:Circuit):∀j∈topGates d C,j<C.gates.length:=fun _ a=>Finset.mem_range.mp (Finset.mem_filter.mp a).1
lemma vH (h:Valid n K A C d) (node:bK d C A w)
  (b:∀a∈A,Below n C (topGates d C) a.val w→a=p)
  (empty:∀t,¬tK d C w t):w=p.val:=by
 apply tJ h.2.2.2.2.2.2 h.1 (iY d C) node;intro i f c;rcases dA.mp f with⟨a,e,rfl⟩|⟨s,hs,g,rfl⟩
 ·exact congrArg Fin.val (b _ e c)
 ·exact(empty s ⟨hs,g,c⟩).elim
lemma mZ (h:Valid n K A C d) (node:bK d C A w)
  (f:Below n C (topGates d C) p.val w)
  (b:∀a∈A,Below n C (topGates d C) a.val w→a=p)
  (single:∀u,tK d C w u↔u=t):
  ∃
   j∈topGates d C,w=n+j∧
   ((gateAt C j).inputs=[p.val,d.bw t]∨(gateAt C j).inputs=[d.bw t,p.val]):=by
 obtain⟨ht,r,g⟩:=(single t).2 rfl;have m:p.val≠d.bw t:=by obtain⟨j,q,e,_⟩:=dN h ht;have lt:=p.isLt;omega
 apply rD h.2.2.2.2.2.2 h.1 (iY d C) node f g m;intro i l c;rcases dA.mp l with⟨a,k,rfl⟩|⟨s,hs,o,rfl⟩
 ·exact .inl (congrArg Fin.val (b _ k c))
 ·exact .inr (congrArg d.bw ((single s).1 ⟨hs,o,c⟩))
end TopShape
section Formula
variable {p l : Fin n} {w : ℕ} {x : Fin n → Bool}
def
    Outside (d : NCCData n) (A : Finset (Fin n)) (C : Circuit) (w : ℕ)
    (x : Fin n → Bool) : Prop :=
  (∃ a ∈ A, ¬ Below n C (topGates d C) a.val w ∧ x a = true) ∨
    ∃ t ∈ d.cover, d.tie t = none ∧ ¬ Below n C (topGates d C) (d.bw t) w ∧ W C x (d.bw t)
def oZ (K:SimpleGraph (Fin n)) (x:Fin n→Bool):Prop:=∃u v,K.Adj u v∧x u=true∧x v=true
def zR (K:SimpleGraph (Fin n)) (A:Finset (Fin n)) (p q:Fin n) (x:Fin n→Bool):Prop:=(∃a∈A,a≠p∧x a=true)∨oZ K x∨(x p=true∧x q=true)
lemma kS (h:Valid n K A C d) (nT:¬oZ K x)
  (ht:t∈d.cover):¬W C x (d.bw t):=by
 apply dK h (fun _=>False) _ ht;rintro u _ (xu|⟨_,_,_,a⟩) ⟨v,ev,mv⟩
 ·rcases mv with b|⟨_,_,_,a⟩
  ·exact nT ⟨u,v,(h.2.2.1.1 _ _ ev).1,xu,b⟩
  ·exact a
 ·exact a
lemma Signal.rejects (iF:Signal d C q H) (h:Valid n K A C d) {a:Fin n} (c:a≠q):
  ¬W C (single a) H:=by
 intro b;rcases iF with rfl|⟨f,_,e⟩
 ·exact c (of_decide_eq_true ((aC q).1 b)).symm
 ·exact c ((jM h f (.inr e) a).1 b).2.symm
structure Attachment (d : NCCData n) (C : Circuit) (p q : Fin n) (w H : ℕ) : Prop where
  signal : Signal d C q H
  cases : w = p.val ∨
    (q ∈ d.cover ∧ d.tie q = none ∧ H = d.zroot q ∧
      ∃ j ∈ topGates d C, w = n+j ∧
        ((gateAt C j).inputs = [p.val,d.bw q] ∨ (gateAt C j).inputs = [d.bw q,p.val])) ∨
    ∃ t, SwapOK d t q ∧ H = q.val ∧
      ∃ j ∈ topGates d C, w = n+j ∧
        ((gateAt C j).inputs = [p.val,d.bw t] ∨ (gateAt C j).inputs = [d.bw t,p.val])
lemma tL (h:Valid n K A C d) (node:bK d C A w)
  (G:p∈A) (P:q∉A) (hl:l∉A) (lq:l≠q)
  (Aiso:∀a∈A,∀v,¬K.Adj a v) (B:∀v,¬K.Adj l v)
  (O:Below n C (topGates d C) p.val w) (Hbd:H<n+C.gates.length)
  (Q:∀k,k≠p→(W C (pair p k) H↔W C (single k) H))
  (y:∀x,x l=false→
    ((Outside d A C w x∨(W C x w∧W C x H))↔zR K A p q x)):
  Attachment d C p q w H:=by
 have J {k:Fin n} (U:k∉A) (kl:k≠l):
   W C (single k) H↔k=q:=by
  have kp:k≠p:=fun e=>U (e▸G)
  let x:=pair p k
  have lp:l≠p:=fun e=>hl (e▸G)
  have N:x l=false:=by simp[x,pair,lp,Ne.symm kl]
  have m:¬oZ K x:=by
   rintro⟨u,v,e,xu,xv⟩;rcases of_decide_eq_true xu with rfl|rfl<;>rcases of_decide_eq_true xv with rfl|rfl
   ·exact e.ne rfl
   ·exact Aiso _ G _ e
   ·exact Aiso _ G _ e.symm
   ·exact e.ne rfl
  have g:¬ ∃a∈A,a≠p∧x a=true:=by
   rintro⟨a,c,ne,E⟩;rcases of_decide_eq_true E with rfl|rfl
   ·exact ne rfl
   ·exact U c
  have b:¬Outside d A C w x:=by
   rintro(⟨a,c,ba,E⟩|⟨s,hs,_,_,ws⟩)
   ·exact g ⟨a,c,fun e=>ba (e▸O),E⟩
   ·exact kS h m hs ws
  have V:W C x w:=(vA h node).2 (.inl ⟨p,G,O,by simp[x,pair]⟩);have M:=y x N;rw[or_iff_right b,and_iff_right V,zR,or_iff_right g,or_iff_right m] at M;have qp:q≠p:=fun e=>P (e▸G)
  simpa[x,pair,qp,eq_comm] using(Q k kp).symm.trans M
 have iF:Signal d C q H:=by apply jY h Hbd P ((J P lq.symm).2 rfl);rintro k ⟨u,e⟩ hi;exact(J (fun c=>Aiso _ c _ e.symm) (fun T=>B _ (T▸e.symm))).1 hi
 have i (a:Fin n) (c:a∈A) (ba:Below n C (topGates d C) a.val w):a=p:=by
  by_contra ne
  let x:=single a
  have la:l≠a:=fun e=>hl (e▸c)
  have N:x l=false:=by simp[x,single,la]
  have b:¬Outside d A C w x:=by
   rintro(⟨a',_,ba',E⟩|⟨s,hs,_,_,ws⟩)
   ·exact ba' ((of_decide_eq_true E:a'=a)▸ba)
   ·exact bY h hs a ws
  have S:=(y x N).2 (.inl ⟨a,c,ne,by simp[x,single]⟩);exact iF.rejects h (fun e=>P (e▸c)) ((S.resolve_left b).2)
 have F {s r:Fin n} (o:d.owns s r=true)
   (only:∀t∈d.cover,d.tie t=none→W C (pair s r) (d.bw t)→
     Below n C (topGates d C) (d.bw t) w):W C (pair s r) H:=by
  have e:=(h.2.2.1.1 _ _ o).1;have ls:l≠s:=fun R=>B _ (R▸e)
  have lr:l≠r:=fun R=>B _ (R▸e.symm)
  have N:pair s r l=false:=by simp[pair,ls,lr]
  have b:¬Outside d A C w (pair s r):=by
   rintro(⟨a,c,_,E⟩|⟨t,ht,tt,bt,wt⟩)
   ·rcases of_decide_eq_true E with rfl|rfl
    ·exact Aiso _ c _ e
    ·exact Aiso _ c _ e.symm
   ·exact bt (only t ht tt wt)
  have S:=(y _ N).2 (.inr (.inl ⟨s,r,e,by simp[pair],by simp[pair]⟩));exact(S.resolve_left b).2
 have f:∀t r,tK d C w t→d.owns t r=true→W C (pair t r) H:=by intro t r ht o;apply F o;intro s hs _ ws;obtain rfl:=(mP h o ht.2.1 hs).1 ws;exact ht.2.2
 have j:tK d C w q→∀s r,d.tie s=some q→ r∉d.cover→
   d.owns s r=true→W C (pair s r) H:=by
  intro Z s r X hr o;apply F o;intro u hu tu wu;rcases (jL h o X Z.2.1 hr hu).1 wu with rfl|rfl
  ·simp[tu] at X
  ·exact Z.2.2
 refine⟨iF,?_⟩;rcases aBq h iF (fun _ z=>⟨z.1,z.2.1⟩) f j with empty|⟨hq',tq,rh,one⟩|⟨t,sw,rh,one⟩
 ·exact .inl (vH h node i empty)
 ·exact .inr (.inl ⟨hq',tq,rh,mZ h node O i one⟩)
 ·exact .inr (.inr ⟨t,sw,rh,mZ h node O i one⟩)
lemma yP {K':SimpleGraph (Fin n)} [DecidableRel K'.Adj]
  (b:∀u v,K'.Adj u v↔K.Adj u v∨
    (u=p∧(v=l∨v=q))∨(v=p∧(u=l∨u=q)))
  (i:x l=false):
  graphFun K' (A.erase p) x=true↔zR K A p q x:=by
 simp only[graphFun,Bool.or_eq_true,decide_eq_true_eq,zR,oZ];have extra:(∃a∈A.erase p,x a=true)↔∃a∈A,a≠p∧x a=true:=by
  simp only[Finset.mem_erase];constructor
  ·rintro⟨a,⟨f,g⟩,h⟩;exact⟨a,g,f,h⟩
  ·rintro⟨a,g,f,h⟩;exact⟨a,⟨f,g⟩,h⟩
 rw[extra];apply or_congr_right;constructor
 ·rintro⟨u,v,e,c,d⟩;rcases (b u v).1 e with e|⟨rfl,rfl|rfl⟩|⟨rfl,rfl|rfl⟩
  ·exact .inl ⟨u,v,e,c,d⟩
  ·simp[i] at d
  ·exact .inr ⟨c,d⟩
  ·simp[i] at c
  ·exact .inr ⟨d,c⟩
 ·rintro(⟨u,v,e,c,d⟩|⟨xp,xq⟩)
  ·exact⟨u,v,(b u v).2 (.inl e),c,d⟩
  ·exact⟨p,q,(b p q).2 (.inr (.inl ⟨rfl,.inr rfl⟩)),xp,xq⟩
lemma mC {K':SimpleGraph (Fin n)} [DecidableRel K'.Adj] {D:Circuit}
  (h:Valid n K A C d) (node:bK d C A w)
  (o:p∈A) (r:q∉A) (hl:l∉A) (lq:l≠q)
  (Aiso:∀a∈A,∀v,¬K.Adj a v) (i:∀v,¬K.Adj l v)
  (m:Below n C (topGates d C) p.val w) (Hbd:H<n+C.gates.length)
  (e:∀k,k≠p→(W C (pair p k) H↔W C (single k) H))
  (g:∀x,W D x D.output↔Outside d A C w x∨(W C x w∧(x l=true∨W C x H)))
  (f:circuitFun n D =graphFun K' (A.erase p))
  (c:∀u v,K'.Adj u v↔K.Adj u v∨
    (u=p∧(v=l∨v=q))∨(v=p∧(u=l∨u=q))):
  Attachment d C p q w H:=by
 apply tL h node o r hl lq Aiso i m Hbd e;intro x j;have b:=(g x).symm;rw[←cL,f] at b;simpa[j] using b.trans (yP (A:=A) (p:=p) (q:=q) c j)
end Formula
end PEqualNP.MetaComplexity.NestedCover.Aw
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {K K' : SimpleGraph (Fin n)} {C D : Circuit} {d : NCCData n}
   {A : Finset (Fin n)} {p l q : Fin n} {f w : ℕ ↪ ℕ} {i j H s : ℕ}
structure SitePins (n : ℕ) (C D : Circuit) (d : NCCData n) (l : Fin n)
    (f w : ℕ ↪ ℕ) (i j H s : ℕ) : Prop where
  range : Finset.range D.gates.length = insert i (insert j ((Finset.range C.gates.length).map f))
  gaps : ∀ k, f k ≠ i ∧ f k ≠ j
  ij : i ≠ j
  fixed : ∀ v : Fin n, w v.val = v.val
  align : ∀ k, w (n+k) = n+f k
  back : ReadsBack n D
  oldOp : ∀ k < C.gates.length, (gateAt D (f k)).op = (gateAt C k).op
  oldNative : ∀ k < C.gates.length, (d.role k).1 ≠ .top →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map w
  oldTop : ∀ k < C.gates.length, (d.role k).1 = .top →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map
      (fun z => if z=s then n+j else w z)
  out : D.output = if C.output=s then n+j else w C.output
  iOp : (gateAt D i).op = .or
  jOp : (gateAt D j).op = .and
  iIns : (gateAt D i).inputs = [l.val,w H] ∨ (gateAt D i).inputs = [w H,l.val]
  jIns : (gateAt D j).inputs = [w s,n+i] ∨ (gateAt D j).inputs = [n+i,w s]
lemma aAx (P:SitePins n C D d l f w i j H s) {d':NCCData n}
  (lD:∀k,(d'.role k).1=(d.role k).1):SitePins n C D d' l f w i j H s:=
 {P with
         oldNative:=fun k a ht=>P.oldNative k a (by rwa [←lD])
         oldTop:=fun k a ht=>P.oldTop k a (by rwa [←lD])}
lemma aAy (P:SitePins n C D d l f w i j H s) {ear:Option ℕ}
  (a:s=qL n p ear)
  (earTop:∀k,ear=some k→k∈topGates d C)
  (earIns:∀k,ear=some k→(gateAt C k).inputs=[p.val,d.bw q]∨
    (gateAt C k).inputs=[d.bw q,p.val]):
  TruePins n C D d p l q f w i j H ear:=by
 subst s;exact⟨P.range,P.gaps,P.ij,P.fixed,P.align,P.back,P.oldOp,P.oldNative,P.oldTop,P.out,P.iOp,P.jOp,P.iIns,P.jIns,earTop,earIns⟩
lemma xN (iF:Aw.Signal d C q H):
  if q∈d.cover then
  IsCentred n C d H∧(H=q.val∨∃k<C.gates.length,H=n+k∧d.role k=(.z,q.val))
  else H=q.val:=by
 by_cases a:q∈d.cover
 ·simp only[a,ite_true];rcases iF with rfl|⟨_,e,k,b,c⟩
  ·exact⟨(aG q).2 a,Or.inl rfl⟩
  ·exact⟨e,Or.inr ⟨k,Finset.mem_range.mp (Finset.mem_filter.mp b).1,c,(Finset.mem_filter.mp b).2⟩⟩
 ·simpa only[a,ite_false] using iF.resolve_right (fun hh=>a hh.1)
lemma aBr (h:Valid n K (insert p A) C d) (G:TrueGraph K K' p l q)
  (m:p∉A) (P:SitePins n C D d l f w i j H s)
  (rec:Aw.Attachment d C p q s H):IsNestedCoverCircuit n K' A D:=by
 have tied {d':NCCData n} (v:Valid n K (insert p A) C d')
   (P':SitePins n C D d' l f w i j H s) (iF:Aw.Signal d' C q H)
   (c:q∈d'.cover) (free:d'.tie q=none) (hr:H=d'.zroot q)
   (k:ℕ) (b:k∈topGates d' C) (g:s=n+k)
   (bS:(gateAt C k).inputs=[p.val,d'.bw q]∨(gateAt C k).inputs=[d'.bw q,p.val]):
   IsNestedCoverCircuit n K' A D:=by
  have o:=aAy (p:=p) (q:=q) (ear:=some k) P' g
   (fun z hh=>(Option.some.inj hh)▸b) (fun z hh=>(Option.some.inj hh)▸bS)
  exact⟨_,eM v o G ⟨xN iF,fun _=>⟨c,free,hr⟩⟩ m⟩
 obtain⟨iF,cases⟩:=rec;rcases cases with u|⟨c,free,hr,k,b,g,bS⟩|⟨t,swap,raw,k,b,g,bS⟩
 ·have o:=aAy (p:=p) (q:=q) (ear:=none) P u (by simp) (by simp);exact⟨_,eM h o G ⟨xN iF,by simp⟩ m⟩
 ·exact tied h P iF c free hr k b g bS
 ·let d':=Aj.aB d t q
  have v:Valid n K (insert p A) C d':=Aj.eM h swap;have a (k):(d'.role k).1=(d.role k).1:=by simp only[d',Aj.aB];split<;>simp_all
  have c:q∈d'.cover:=Finset.mem_insert_self ..;have free:d'.tie q=none:=by
   change d.tie q=none
   cases e:d.tie q with
   | none=>rfl
   | some z=>exact(swap.outside (h.2.2.2.1 _ _ e).1).elim
  have r:k∈topGates d' C:=Finset.mem_filter.mpr
   ⟨(Finset.mem_filter.mp b).1,(a k).trans (Finset.mem_filter.mp b).2⟩
  apply tied v (aAx P a) (.inl raw) c free _ k r g
  ·simpa[d',Aj.aB] using bS
  ·simpa[d',Aj.aB] using raw
lemma tM {G:SimpleGraph (Fin n)}
  (leaf:∀v,G.Adj l v↔v=p) (lq:l≠q)
  (a:∀v,G.Adj p v↔v=l∨v=q):
  TrueGraph ((G.deleteIncidenceSet l).deleteIncidenceSet p) G p l q:=by
 have lp:=(leaf p).2 rfl;have pq:=(a q).2 (Or.inr rfl);refine⟨lp.ne.symm,pq.ne,lq,by simp[SimpleGraph.deleteIncidenceSet_adj],by simp[SimpleGraph.deleteIncidenceSet_adj],?_⟩;intro u z;rw[SimpleGraph.deleteIncidenceSet_adj,SimpleGraph.deleteIncidenceSet_adj];constructor
 ·intro e;by_cases up:u=p
  ·exact Or.inr (Or.inl ⟨up,(a z).1 (up▸e)⟩)
  by_cases b:z=p
  ·exact Or.inr (Or.inr ⟨b,(a u).1 (b▸e.symm)⟩)
  exact Or.inl ⟨⟨e,fun c=>b ((leaf _).1 (c▸e)),fun c=>up ((leaf _).1 (c▸e.symm))⟩,up,b⟩
 ·rintro(⟨⟨e,_,_⟩,_,_⟩|⟨rfl,hz⟩|⟨rfl,hu⟩)
  ·exact e
  ·exact(a _).2 hz
  ·exact((a _).2 hu).symm
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds Ac
variable {n : ℕ} {C D : Circuit} {l : Fin n} {f w : ℕ ↪ ℕ} {i j H s k a : ℕ}
structure A2 (n : ℕ) (C D : Circuit) (l : Fin n) (f w : ℕ ↪ ℕ)
    (i j H s : ℕ) : Prop where
  splice : Splice n C D f w s (n+j)
  fixed : ∀ v : Fin n, w v.val = v.val
  oldBound : ∀ m < C.gates.length, f m < D.gates.length
  iBound : i < D.gates.length
  jBound : j < D.gates.length
  back : ReadsBack n D
  iOp : (gateAt D i).op = .or
  jOp : (gateAt D j).op = .and
  iIns : mM D i l.val (w H)
  jIns : mM D j (w s) (n+i)
  range : Finset.range D.gates.length =
    insert i (insert j ((Finset.range C.gates.length).map f))
  gaps : ∀ m, f m ≠ i ∧ f m ≠ j
  ij : i ≠ j
  hBound : H < n+C.gates.length
  sBound : s < n+C.gates.length
lemma yQ (T:At D l true i H k a) (back:ReadsBack n D):
  A2 n (bT n D i l.val k a) D l (cN i k) (cN (n+i) (n+k))
   i (skip i k) H (contract (n+i) l.val a):=by
 have b:=(aS (n:=n) (h:=l.val) T.realB).mpr T.realD;have d:=erase_length (n:=n) (h:=contract (n+i) l.val a) b;have le:i≤k:=by by_contra! lt;have c:=T.ordered;simp only[aQ,lt,↓reduceIte] at c;omega
 have f:k≤(bT n D i l.val k a).gates.length:=by change k≤(erase n (erase n D i l.val) k _).gates.length;omega
 have hs:contract (n+i) l.val a<n+k:=bI (by have:=l.isLt;omega) (by rw[align];exact T.earlierA);refine
  {splice:=T.splice
   fixed:=fun v=>nJ v i k
   oldBound:= ?_
   iBound:=T.realB
   jBound:=T.realD
   back:=back
   iOp:=T.opB
   jOp:=T.opD
   iIns:= ?_
   jIns:= ?_
   range:=pY T.realB T.realD
   gaps:=zP i k
   ij:=Nat.ne_of_lt T.ordered
   hBound:=by have:=T.earlierH;omega
   sBound:=by omega}
 ·intro m e;exact(aS T.realB).mp ((aS b).mp e)
 ·rw[T.mapH];exact T.pairB
 ·rw[T.mapA];exact T.pairD.symm
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds Ac Af
variable {n : ℕ} {C D : Circuit} {d : NCCData n} {A : Finset (Fin n)}
  {K : SimpleGraph (Fin n)} {p l : Fin n} {f w : ℕ ↪ ℕ} {i j H s : ℕ}
structure Az (n : ℕ) (C D : Circuit) (l : Fin n) (f w : ℕ ↪ ℕ) (i j H s : ℕ) :
    Prop where
  splice : Splice n C D f w s (n+j)
  fixed : ∀ a : Fin n, w a.val = a.val
  oldBound : ∀ k < C.gates.length, f k < D.gates.length
  iBound : i < D.gates.length
  jBound : j < D.gates.length
  back : ReadsBack n D
  iOp : (gateAt D i).op = .or
  jOp : (gateAt D j).op = .and
  iIns : mM D i l.val (w H)
  jIns : mM D j (w s) (n+i)
namespace Az
variable (R : Az n C D l f w i j H s) {x : Fin n → Bool}
include R
lemma gate_congr (o:ReadsBack n C) {k:ℕ} (h:k<C.gates.length)
  (fP:∀a∈(gateAt C k).inputs,w a∈(gateAt D (f k)).inputs→
    val D x (w a)=val C x a)
  (b:n+j∈(gateAt D (f k)).inputs→val D x (n+j)=val C x s):
  val D x (w (n+k))=val C x (n+k):=by
 unfold val;rw[R.splice.align,aO R.back (R.oldBound k h),aO o h,R.splice.op];congr 1;apply List.ext_getElem
 ·simpa only[List.length_map] using R.splice.total k
 intro t ht l;have i:t<(gateAt D (f k)).inputs.length:=by simpa using ht
 have c:t<(gateAt C k).inputs.length:=by simpa using l
 let a:=(gateAt C k).inputs[t]
 have m:a∈(gateAt C k).inputs:=List.getElem_mem c;rcases (R.splice.pin k t a).mp (List.getElem?_eq_getElem c) with e|⟨e,g⟩
 ·have em:(gateAt D (f k)).inputs[t]=w a:=by simpa[i] using e
  have d:=fP a m (List.mem_of_getElem? e);simpa only[List.getElem_map,em,val,a] using d
 ·have em:(gateAt D (f k)).inputs[t]=n+j:=by simpa[i] using e
  have d:=(b (List.mem_of_getElem? e)).trans (congrArg (val C x) g.symm);simpa only[List.getElem_map,em,val,a] using d
lemma raw_input (a:Fin n):val D x (w a.val)=val C x a.val:=by rw[R.fixed,bE,bE]
lemma before (h:ReadsBack n C):
  ∀a<n+C.gates.length,w a<n+j→val D x (w a)=val C x a:=by
 intro a
 induction a using Nat.strong_induction_on with
 | ind a ih=>
   intro m i;by_cases l:a<n
   ·exact R.raw_input ⟨a,l⟩
   have e:a=n+(a-n):=by omega
   rw[e,R.splice.align] at i;rw[e];apply R.gate_congr h (by omega)
   ·intro b d g;have k:=h (a-n) (by omega) b d;have c:=R.back (f (a-n)) (R.oldBound _ (by omega)) (w b) g;exact ih b (by omega) (by omega) (c.trans i)
   ·intro d;have:=R.back (f (a-n)) (R.oldBound _ (by omega)) (n+j) d;omega
lemma operands_before:
  w s<n+j∧w H<n+j:=by
 have c:w s∈(gateAt D j).inputs:=by rcases R.jIns with e|e<;>simp[e]
 have b:n+i∈(gateAt D j).inputs:=by rcases R.jIns with e|e<;>simp[e]
 have a:w H∈(gateAt D i).inputs:=by rcases R.iIns with e|e<;>simp[e]
 exact⟨R.back j R.jBound _ c,(R.back i R.iBound _ a).trans (R.back j R.jBound _ b)⟩
lemma inserted (d:ReadsBack n C) (hs:s<n+C.gates.length)
  (hh:H<n+C.gates.length):
  W D x (n+j)↔W C x s∧(x l=true∨W C x H):=by
 have a:=R.before (x:=x) d s hs R.operands_before.1;have b:=R.before (x:=x) d H hh R.operands_before.2;have e:=bE (C:=D) (x:=x) l;change val D x (n+j)=true↔val C x s=true∧(x l=true∨val C x H=true)
 unfold val at a b e ⊢
 rw[aO R.back R.jBound,R.jOp];rcases R.jIns with h|h<;>simp only[h,GateOp.eval,List.map_cons,List.map_nil,
  List.all_cons,List.all_nil,id_eq,Bool.and_true,Bool.and_eq_true,a]<;>
  rw[aO R.back R.iBound,R.iOp]<;>
  rcases R.iIns with c|c<;>
  simp only[c,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,e,b,Bool.or_eq_true]<;>tauto
lemma aliases (f:ReadsBack n C) (out:C.output<n+C.gates.length)
  (g:val D x (n+j)=val C x s):W D x D.output↔W C x C.output:=by
 have d:∀a<n+C.gates.length,val D x (w a)=val C x a:=by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih=>
    intro l;by_cases k:a<n
    ·exact R.raw_input ⟨a,k⟩
    have e:a=n+(a-n):=by omega
    rw[e];apply R.gate_congr f (by omega)
    ·intro b i _;have lt:=f (a-n) (by omega) b i;exact ih b (by omega) (by omega)
    ·exact fun _=>g
 rcases (R.splice.output C.output).mp rfl with c|⟨c,h⟩
 ·change val D x D.output=true↔val C x C.output=true;rw[c,d _ out]
 ·change val D x D.output=true↔val C x C.output=true;rw[c,g,h]
lemma unchanged_where (i:ReadsBack n C) (P:ℕ→Prop)
  (step:∀k<C.gates.length,P (n+k)→
    n+j∉(gateAt D (f k)).inputs∧∀a∈(gateAt C k).inputs,P a):
  ∀a<n+C.gates.length,P a→val D x (w a)=val C x a:=by
 intro a
 induction a using Nat.strong_induction_on with
 | ind a ih=>
   intro m d;by_cases l:a<n
   ·exact R.raw_input ⟨a,l⟩
   have e:a=n+(a-n):=by omega
   rw[e] at d ⊢
   have c:=step (a-n) (by omega) d;apply R.gate_congr i (by omega)
   ·intro b h _;have lt:=i (a-n) (by omega) b h;exact ih b (by omega) (by omega) (c.2 _ h)
   ·exact fun g=>(c.1 g).elim
lemma some_redirect (g:ReadsBack n C) (out:C.output<n+C.gates.length)
  (b:W C x C.output) (a:¬W D x D.output):
  D.output=n+j∨∃k<C.gates.length,n+j∈(gateAt D (f k)).inputs:=by
 by_contra! d;have c:D.output=w C.output:=by
  rcases (R.splice.output C.output).mp rfl with c|⟨c,_⟩
  ·exact c
  ·exact(d.1 c).elim
 have e:=R.unchanged_where (x:=x) g (fun _=>True) (fun k h _=>⟨d.2 k h,fun _ _=>trivial⟩) _ out trivial;apply a;change val D x D.output=true;rw[c,e];exact b
end Az
abbrev bK (d:NCCData n) (C:Circuit) (A:Finset (Fin n)):=fQ n (topGates d C) (topLeaves d A)
lemma cZ (h:Valid n K A C d):IsOrTree n C (topGates d C) (topLeaves d A) C.output:=h.2.2.2.2.2.2
lemma sA {k:ℕ} (a:k∈topGates d C):k<C.gates.length:=Finset.mem_range.mp (Finset.mem_filter.mp a).1
lemma tN {k:ℕ} (a:k<C.gates.length):
  k∈topGates d C↔(d.role k).1= .top:=
 Finset.mem_filter.trans (and_iff_right (Finset.mem_range.mpr a))
lemma qO {a:ℕ} (h:Valid n K A C d) (b:a∈topLeaves d A):
  a<n+C.gates.length:=by
 rcases dA.mp b with⟨u,_,rfl⟩|⟨t,ht,_,rfl⟩
 ·have:=u.isLt;omega
 ·obtain⟨k,c,e,_,_,_⟩:=dN h ht;omega
lemma kF {a:ℕ} (h:Valid n K A C d) (b:bK d C A a):
  a<n+C.gates.length:=by
 rcases b with b|⟨k,c,rfl⟩
 ·exact qO h b
 ·have:=sA c;omega
lemma rE (h:Valid n K A C d) (c:∀v,¬K.Adj p v):
  p∉d.cover:=by
 intro f;have cover:K.IsVertexCover (↑(d.cover.erase p):Set (Fin n)):=by
  intro u v e;have g:u≠p:=fun b=>c v (b▸e)
  have i:v≠p:=fun b=>c u (b▸e.symm)
  exact(h.2.1.1 e).imp (fun a=>Finset.mem_erase.mpr ⟨g,a⟩) (fun a=>Finset.mem_erase.mpr ⟨i,a⟩)
 exact(not_le_of_gt (Finset.card_erase_lt_of_mem f)) (h.2.1.2 _ cover)
lemma fZ (h:Valid n K A C d) (B:p∈A)
  (j:∀v,¬K.Adj p v) {a:ℕ} (E:a<n+C.gates.length):
  W C (single p) a↔Below n C (topGates d C) p.val a:=by
 constructor
 ·intro c;by_cases x:a<n
  ·let q:Fin n:=⟨a,x⟩
   have r:q=p:=of_decide_eq_true ((aC q).mp c);have m:a=p.val:=congrArg Fin.val r;exact m.symm▸Below.refl
  let k:=a-n
  have f:a=n+k:=by dsimp[k];omega
  have g:k<C.gates.length:=by dsimp[k];omega
  rcases h.2.2.2.2.1 k g with w|⟨t,ht,rt,l⟩
  ·exact((dB h (.inr ⟨k,(tN g).2 w,f⟩) p).1 c).2
  have i {mV:Kind} (e:(d.role k).1=mV):k∈gatesOf d C mV t.val:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr g,Prod.ext e rt⟩
  cases e:(d.role k).1 with
  | top=>exact((dB h (.inr ⟨k,(tN g).2 e,f⟩) p).1 c).2
  | b=>exact(bY h ht p ((f.trans (l e).symm)▸c)).elim
  | z=>
    obtain⟨_,rfl⟩:=(jM h ht (.inr ⟨k,i e,f⟩) p).1 c;exact(rE h j ht).elim
  | o=>
    obtain⟨op,_⟩:=(jN h ht (.inr ⟨k,i e,f⟩) p).1 c;exact(j t (h.2.2.1.1 _ _ op).1.symm).elim
 ·intro hr;exact hr.push (fun k u b s y=>(gT h.1 (cZ h)
   (fun _=>sA) k u).2 ⟨b,s,y⟩)
   ((aC p).2 (by simp[single]))
def
    Outside (d : NCCData n) (A : Finset (Fin n)) (C : Circuit) (s : ℕ)
    (x : Fin n → Bool) : Prop :=
  (∃ a ∈ A, ¬ Below n C (topGates d C) a.val s ∧ x a = true) ∨
  ∃ t ∈ d.cover, d.tie t = none ∧ ¬ Below n C (topGates d C) (d.bw t) s ∧ W C x (d.bw t)
structure A1 (n : ℕ) (C D : Circuit) (d : NCCData n) (A : Finset (Fin n))
    (p l : Fin n) (f w : ℕ ↪ ℕ) (i j H s : ℕ) : Prop where
  raw : Az n C D l f w i j H s
  node : bK d C A s
  cone : Below n C (topGates d C) p.val s
  hOff : ¬ Below n C (topGates d C) p.val H
  hBound : H < n+C.gates.length
  oldNative : ∀ k < C.gates.length, (d.role k).1 ≠ .top →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map w
  oldTop : ∀ k < C.gates.length, (d.role k).1 = .top →
    (gateAt D (f k)).inputs = (gateAt C k).inputs.map
      (fun a => if a = s then n+j else w a)
  out : D.output = if C.output = s then n+j else w C.output
lemma iP {a:ℕ} (c:p∈A)
  (b:Below n C (topGates d C) p.val a):bK d C A a:=by
 cases b with
 | refl=>exact .inl (dA.mpr (.inl ⟨p,c,rfl⟩))
 | step _ hg _=>exact .inr ⟨_,hg,rfl⟩
lemma Az.toTopAttach (R:Az n C D l f w i j H s) (h:Valid n K A C d)
  (iso:∀a∈A,∀v,¬K.Adj a v) (m:p∈A) (E:p≠l)
  (hs:s<n+C.gates.length) (hh:H<n+C.gates.length)
  (o:¬W D (single p) D.output):A1 n C D d A p l f w i j H s:=by
 have c:W C (single p) C.output:=(A7.iJ h _).2 (.inl ⟨p,m,by simp[single]⟩);have y:=kF h (cC (cZ h));have diff:val D (single p) (n+j)≠val C (single p) s:=fun q=>o ((R.aliases h.1 y q).2 c)
 have inserted:=R.inserted (x:=single p) h.1 hs hh;have ws:W C (single p) s:=by
  by_contra t;have u:¬W D (single p) (n+j):=fun e=>t (inserted.1 e).1
  exact diff (Bool.eq_iff_iff.mpr ⟨fun e=>(u e).elim,fun e=>(t e).elim⟩)
 have r:¬W C (single p) H:=by intro r;have fresh:=inserted.2 ⟨ws,Or.inr r⟩;exact diff (Bool.eq_iff_iff.mpr ⟨fun _=>ws,fun _=>fresh⟩)
 have cone:=(fZ h m (iso _ m) hs).1 ws;have node:=iP m cone;have z:=fun b=>r ((fZ h m (iso _ m) hh).2 b)
 have g:=Ad.zZ h R.splice iso node (R.some_redirect h.1 y c o);exact⟨R,node,cone,z,hh,g.2.2,fun k B _=>g.1 k B,g.2.1⟩
lemma nA (h:Valid n K A C d) (iso:∀a∈A,∀v,¬K.Adj a v)
  {a k} (b:bK d C A a) (g:k<C.gates.length)
  (f:a∈(gateAt C k).inputs):k∈topGates d C:=by
 rcases Ad.fF h iso b (c:=some k) ⟨g,f⟩ with⟨m,hm,e,_⟩|⟨ne,_⟩
 ·simpa using(Option.some.inj e)▸hm
 ·cases ne
lemma rF (h:Valid n K A C d) (iso:∀a∈A,∀v,¬K.Adj a v) (m:p∈A)
  {x y:Fin n→Bool} (f:∀a,a≠p→x a=y a):
  ∀a<n+C.gates.length,¬Below n C (topGates d C) p.val a→val C x a=val C y a:=by
 intro a
 induction a using Nat.strong_induction_on with
 | ind a ih=>
   intro s c;by_cases q:a<n
   ·let v:Fin n:=⟨a,q⟩
    have r:v≠p:=by intro l;have j:a=p.val:=congrArg Fin.val l;exact c (j.symm▸Below.refl)
    change val C x v.val=val C y v.val;rw[bE,bE,f _ r]
   let k:=a-n
   have o:a=n+k:=by dsimp[k];omega
   have g:k<C.gates.length:=by dsimp[k];omega
   rw[o] at c ⊢
   unfold val;rw[aO h.1 g,aO h.1 g];congr 1;apply List.map_congr_left;intro b i;have lt:=h.1 k g b i;apply ih b (by omega) (by omega);intro e;exact c (e.step (nA h iso (iP m e) g i) i)
lemma vI {a b c:ℕ} (e:Below n C (topGates d C) a b)
  (f:Below n C (topGates d C) b c):Below n C (topGates d C) a c:=by
 exact f.push (fun _ h _ g i=>i.step h g) e
lemma mE {a b:ℕ} (c:Below n C (topGates d C) a b) (f:a≠b):
  ∃
   k∈topGates d C,b=n+k∧
   ∃e∈(gateAt C k).inputs,Below n C (topGates d C) a e:=by
 cases c with
 | refl=>exact(f rfl).elim
 | step aa hk hi=>exact⟨_,hk,rfl,_,hi,aa⟩
lemma fU (h:Valid n K A C d) {a} (g:bK d C A a):
  Below n C (topGates d C) a C.output:=by
 have i (b:ℕ):∀a,bK d C A a→n+C.gates.length-a≤b→
   Below n C (topGates d C) a C.output:=by
  induction b using Nat.strong_induction_on with
  | ind b ih=>
    intro u l aT;by_cases e:u=C.output
    ·simpa only[e] using(Below.refl:Below n C (topGates d C) C.output C.output)
    obtain⟨k,c,f⟩:=jO (cZ h) l e;have j:=h.1 k (sA c) u f;have m:=sA c;have lt:n+C.gates.length-(n+k)<b:=by omega
    exact vI (Below.step Below.refl c f) (ih _ lt _ (.inr ⟨k,c,rfl⟩) le_rfl)
 exact i _ a g le_rfl
namespace A1
variable (T : A1 n C D d A p l f w i j H s)
include T
lemma signal_independent (h:Valid n K A C d) (iso:∀a∈A,∀v,¬K.Adj a v) (c:p∈A)
  {x y:Fin n→Bool} (b:∀a,a≠p→x a=y a):
  W C x H↔W C y H:=by
 change val C x H=true↔val C y H=true;rw[rF h iso c b _ T.hBound T.hOff]
lemma leaf_stable (h:Valid n K A C d) (iso:∀a∈A,∀v,¬K.Adj a v)
  {x:Fin n→Bool} {a} (e:a∈topLeaves d A):
  W D x (w a)↔W C x a:=by
 let P:=fun u=>¬ ∃k∈topGates d C,u=n+k
 have o:P a:=by rintro⟨k,l,rfl⟩;exact((cZ h).2.1 _ e).1 ⟨by omega,by simpa using l⟩
 have step (k) (c:k<C.gates.length) (pk:P (n+k)):
   n+j∉(gateAt D (f k)).inputs∧∀b∈(gateAt C k).inputs,P b:=by
  have m:(d.role k).1≠ .top:=fun ht=>pk ⟨k,(tN c).2 ht,rfl⟩
  constructor
  ·rw[T.oldNative k c m];rintro z;obtain⟨b,_,g⟩:=List.mem_map.mp z;exact T.raw.splice.hole b g
  ·rintro b i ⟨v,p,rfl⟩;exact pk ⟨k,nA h iso (.inr ⟨v,p,rfl⟩) c i,rfl⟩
 change val D x (w a)=true↔val C x a=true;rw[T.raw.unchanged_where h.1 P step _ (qO h e) o]
lemma patch_tree (h:Valid n K A C d) (iso:∀a∈A,∀v,¬K.Adj a v)
  (x:Fin n→Bool):
  ∀
   a,bK d C A a→(a=s∨¬Below n C (topGates d C) a s)→
   (W D x (if a=s then n+j else w a)↔
     (∃b∈topLeaves d A,Below n C (topGates d C) b a∧
       ¬Below n C (topGates d C) b s∧W C x b)∨
     (Below n C (topGates d C) s a∧W D x (n+j))):=by
 intro a
 induction a using Nat.strong_induction_on with
 | ind a ih=>
   intro M l;by_cases q:a=s
   ·subst a;rw[ite_eq_left rfl];exact⟨fun i=> .inr ⟨.refl,i⟩,by
     rintro(⟨_,_,c,nb,_⟩|⟨_,i⟩)
     ·exact(nb c).elim
     ·exact i⟩
   have H:=l.resolve_left q;rw[ite_eq_right q];rcases M with y|⟨k,g,rfl⟩
   ·have unique (b) (ba:Below n C (topGates d C) b a):b=a:=by
     by_contra O;obtain⟨k,N,e,-⟩:=mE ba O;exact((cZ h).2.1 _ y).1 ⟨by omega,by simpa[e] using N⟩
    rw[T.leaf_stable h iso y];refine⟨fun P=> .inl ⟨a,y,.refl,H,P⟩,?_⟩;rintro(⟨b,_,ba,_,F⟩|⟨sa,_⟩)
    ·exact unique b ba▸F
    ·exact(q (unique s sa).symm).elim
   have r:=sA g;rw[T.raw.splice.align,aY T.raw.back (T.raw.oldBound k r)
       ((T.raw.splice.op k).trans ((cZ h).1 k g).1),
    T.oldTop k r ((tN r).mp g)]
   simp only[List.mem_map,exists_exists_and_eq_and];have f (b) (c:b∈(gateAt C k).inputs):=
    ih b (h.1 k r b c) (bZ (cZ h) g c)
     (by
       by_cases o:b=s
       ·exact .inl o
       ·exact .inr (fun z=>H (z.advance o (cZ h) g c)))
   constructor
   ·rintro⟨b,c,F⟩;rcases (f b c).1 F with⟨u,t,E,p,G⟩|⟨B,i⟩
    ·exact .inl ⟨u,t,E.step g c,p,G⟩
    ·exact .inr ⟨B.step g c,i⟩
   ·rintro(⟨u,t,ua,p,G⟩|⟨sa,i⟩)
    ·have J:u≠n+k:=fun o=>((cZ h).2.1 _ t).1
      ⟨by omega,by simpa[o] using g⟩
     obtain⟨m,_,o,b,c,E⟩:=mE ua J;have em:m=k:=by omega
     subst m;exact⟨b,c,(f b c).2 (.inl ⟨u,t,E,p,G⟩)⟩
    ·obtain⟨m,_,o,b,c,B⟩:=mE sa (Ne.symm q);have em:m=k:=by omega
     subst m;exact⟨b,c,(f b c).2 (.inr ⟨B,i⟩)⟩
lemma response (h:Valid n K A C d) (iso:∀a∈A,∀v,¬K.Adj a v)
  (x:Fin n→Bool):
  W D x D.output↔Outside d A C s x∨W C x s∧(x l=true∨W C x H):=by
 have tr:=cZ h;have bd:∀k∈topGates d C,k<C.gates.length:=fun _=>sA
 have sr:=fU h T.node;rw[T.out,T.patch_tree h iso x _ (cC tr) (by
  by_cases u:C.output=s
  ·exact .inl u
  ·exact .inr (fun g=>by have p:=g.le h.1 bd;have q:=sr.le h.1 bd;omega)),
  T.raw.inserted h.1 (kF h T.node) T.hBound]
 simp only[sr,true_and];have e:(∃b∈topLeaves d A,Below n C (topGates d C) b C.output∧
   ¬Below n C (topGates d C) b s∧W C x b)↔Outside d A C s x:=by
  constructor
  ·rintro⟨b,r,_,c,o⟩;rcases dA.mp r with⟨a,f,rfl⟩|⟨t,ht,i,rfl⟩
   ·exact .inl ⟨a,f,c,(aC a).1 o⟩
   ·exact .inr ⟨t,ht,i,c,o⟩
  ·rintro(⟨a,f,c,xa⟩|⟨t,ht,i,c,wt⟩)
   ·have j:a.val∈topLeaves d A:=dA.mpr (.inl ⟨a,f,rfl⟩);exact⟨_,j,fU h (.inl j),c,(aC a).2 xa⟩
   ·have m:d.bw t∈topLeaves d A:=dA.mpr (.inr ⟨t,ht,i,rfl⟩);exact⟨_,m,fU h (.inl m),c,wt⟩
 rw[e]
end A1
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds Ac
variable {n : ℕ} {C D : Circuit} {l : Fin n} {f w : ℕ ↪ ℕ} {i j H s k a : ℕ}
lemma A2.raw (L:A2 n C D l f w i j H s):
  Az n C D l f w i j H s where
 splice:=L.splice
 fixed:=L.fixed
 oldBound:=L.oldBound
 iBound:=L.iBound
 jBound:=L.jBound
 back:=L.back
 iOp:=L.iOp
 jOp:=L.jOp
 iIns:=L.iIns
 jIns:=L.jIns
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace PEqualNP.MetaComplexity.NestedCover.Ah
open PEqualNP.CircuitLowerBounds Ac Af
variable {n : ℕ} {D C : Circuit} {G K : SimpleGraph (Fin n)}
  {p l q : Fin n} {A : Finset (Fin n)} {d : NCCData n}
  {f w : ℕ ↪ ℕ} {i j H s k a : ℕ}
lemma qP [DecidableRel G.Adj] (L:A2 n C D l f w i j H s)
  (b:TrueGraph K G p l q) (extra:∀a∈A,∀z,¬G.Adj a z)
  (g:circuitFun n D =graphFun G A)
  (h:Valid n K (insert p A) C d):IsNestedCoverCircuit n G A D:=by
 have pl:G.Adj p l:=(b.ext p l).2 (Or.inr (Or.inl ⟨rfl,Or.inl rfl⟩));have pq:G.Adj p q:=(b.ext p q).2 (Or.inr (Or.inl ⟨rfl,Or.inr rfl⟩));have x:p∉A:=fun c=>extra p c l pl
 have J:l∉insert p A:=fun r=>(Finset.mem_insert.mp r).elim b.pl.symm (fun c=>extra l c p pl.symm)
 have M:q∉insert p A:=fun r=>(Finset.mem_insert.mp r).elim b.pq.symm (fun c=>extra q c p pq.symm)
 have iso:∀a∈insert p A,∀v,¬K.Adj a v:=by
  intro a c v e;rcases Finset.mem_insert.mp c with rfl|c
  ·exact b.isoP _ e
  ·exact extra a c v ((b.ext _ _).2 (Or.inl e))
 have t:p∈insert p A:=Finset.mem_insert_self ..;have o:¬W D (single p) D.output:=by
  rw[←cL,g];simp only[graphFun,Bool.or_eq_true,decide_eq_true_eq,single,not_or];constructor
  ·rintro⟨u,F,rfl⟩;exact x F
  ·rintro⟨u,v,edge,rfl,rfl⟩;exact edge.ne rfl
 have T:=L.raw.toTopAttach h iso t b.pl L.sBound L.hBound o;have y (v:Fin n) (N:v≠p):
   W C (pair p v) H↔W C (single v) H:=by
  apply T.signal_independent h iso t;intro u ne;simp[pair,single,ne]
 have m:circuitFun n D =graphFun G ((insert p A).erase p):=by simpa[x] using g
 have E:=Aw.mC h T.node t M J b.lq iso b.isoL T.cone L.hBound
  y (T.response h iso) m b.ext
 have B:SitePins n C D d l f w i j H s:=
  ⟨L.range,L.gaps,L.ij,L.fixed,L.splice.align,L.back,fun k _=>L.splice.op k,
    T.oldNative,T.oldTop,T.out,L.iOp,L.jOp,L.iIns,L.jIns⟩
 exact aBr h b x B E
lemma tO [DecidableRel G.Adj] (extra:∀a∈A,∀z,¬G.Adj a z)
  (leaf:∀v,G.Adj l v↔v=p) (f:q≠l)
  (e:∀v,G.Adj p v↔v=l∨v=q) (back:ReadsBack n D)
  (c:circuitFun n D =graphFun G A) (T:At D l true i H k a)
  (b:IsNestedCoverCircuit n ((G.deleteIncidenceSet l).deleteIncidenceSet p)
    (insert p A) (bT n D i l.val k a)):IsNestedCoverCircuit n G A D:=by
 obtain⟨d,h⟩:=b;exact qP (yQ T back) (tM leaf f.symm e) extra c h
end PEqualNP.MetaComplexity.NestedCover.Ah
namespace Aq
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover SimpleGraph
lemma kB {n} {K:SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {C:Circuit} {l p:Fin n} {A:Finset (Fin n)} (c:K.IsAcyclic) (iso:cK K A)
  (leaf:bC K l p) (min:IsMinimalCircuit n C) (b:circuitFun n C=graphFun K A):
  ReadsBack n C:=by
 have a:nE K A:=Or.inr ⟨l,p,(leaf p).2 rfl⟩;obtain⟨T,ht⟩:=Ai.aU K;apply Al.bM min _ (Ai.aK c iso a ht min b).2;exact⟨fun _=>false,fun _=>true,by rw[b];exact Al.gE a⟩
lemma oV {n}:lT n:=by
 intro G dec A l p C i h c iso leaf min f e a;obtain⟨d,j⟩:=a;have lp:=(leaf p).2 rfl;exact Ad.oR j e (kB c iso leaf min f)
  (fun v g=>(deleteIncidenceSet_adj.mp g).2.1 rfl)
  (fun b=>iso l b p lp) (fun b=>iso p b l lp.symm)
  (hW iso) (c.anti (deleteIncidenceSet_le _ _)).cliqueFree_three (uH leaf) f
lemma nB {n}:iB n:=by
 intro G dec A l p q C i h j a f iso leaf c outside min k g b;have lp:=(leaf p).2 rfl;apply Ag.tG g b (kB f iso leaf min k) k outside _
  (hW iso) (fun v e=>(deleteIncidenceSet_adj.mp e).2.1 rfl)
  (fun d=>iso l d p lp) (fun d=>iso p d l lp.symm)
  (f.anti (deleteIncidenceSet_le _ _)).cliqueFree_three (uH leaf)
 intro u v m e;obtain⟨o,_,s⟩:=deleteIncidenceSet_adj.mp m;obtain⟨r,_,vl⟩:=deleteIncidenceSet_adj.mp e;exact((c u o).resolve_left s).trans ((c v r).resolve_left vl).symm
lemma nS {n}:jI n:=by intro G dec A l p q C i h j a f iso leaf g e min d c b;exact Ah.tO iso leaf g e (kB f iso leaf min d) d c b
end Aq
theorem nestedIff : ∀ (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n)), K.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K A) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K A C) := by
 intro n K _ A c iso b C;exact Aq.dW Aq.oV Aq.nB
  Aq.nS K A c iso b C

-- final part, still inside the helper namespace
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_172_aux.PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_172_aux.PEqualNP.MetaComplexity.NestedCover.A7
open PEqualNP.Outside.L_meta_172_aux.PEqualNP.MetaComplexity.NestedCover.An

namespace P172

def X {N : ℕ} (x : Fin N → Bool) (i : ℕ) : Bool := if h : i < N then x ⟨i, h⟩ else false

lemma X_fin {N : ℕ} (x : Fin N → Bool) (i : Fin N) : X x i.val = x i := by simp [X]

lemma X_lt {N : ℕ} {x : Fin N → Bool} {i : ℕ} (h : X x i = true) : i < N := by
  unfold X at h
  split at h
  · assumption
  · simp at h

def EF (m : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, i + 1 < 2 * m) ∧
    ∀ x : Fin (2 * m) → Bool, W C x w ↔ ∃ i ∈ S, X x i = true ∧ X x (i + 1) = true

lemma oddCover {m : ℕ} : (SimpleGraph.pathGraph (2 * m)).IsVertexCover
    ((Finset.univ.filter (fun v : Fin (2 * m) => v.val % 2 = 1) : Finset (Fin (2 * m))) :
      Set (Fin (2 * m))) := by
  intro v w hvw
  rw [SimpleGraph.pathGraph_adj] at hvw
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

lemma oddCard {m : ℕ} : (Finset.univ.filter (fun v : Fin (2 * m) => v.val % 2 = 1)).card ≤ m := by
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun v : Fin (2 * m) => v.val % 2 = 1)) (t := Finset.range m)
    (fun v => v.val / 2) ?_ ?_
  · simpa using h
  · intro v hv
    have := v.isLt
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  · intro a ha b hb e
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    simp only at e
    exact Fin.ext (by omega)

lemma coverInj {m : ℕ} {T : Finset (Fin (2 * m))}
    (hc : IsMinCover (SimpleGraph.pathGraph (2 * m)) T) :
    ∀ u ∈ T, ∀ v ∈ T, u.val / 2 = v.val / 2 → u = v := by
  classical
  have h1 : T.card ≤ m := le_trans (hc.2 _ oddCover) oddCard
  have h2 : Finset.range m ⊆ T.image (fun v : Fin (2 * m) => v.val / 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hadj : (SimpleGraph.pathGraph (2 * m)).Adj ⟨2 * i, by omega⟩ ⟨2 * i + 1, by omega⟩ := by
      rw [SimpleGraph.pathGraph_adj]; simp
    rcases hc.1 hadj with h | h
    · exact Finset.mem_image.mpr ⟨_, h, by simp⟩
    · exact Finset.mem_image.mpr ⟨_, h, by simp; omega⟩
  have h3 := Finset.card_le_card h2
  rw [Finset.card_range] at h3
  have h4 : (T.image (fun v : Fin (2 * m) => v.val / 2)).card = T.card :=
    le_antisymm Finset.card_image_le (by omega)
  have h5 := Finset.card_image_iff.mp h4
  intro u hu v hv e
  exact h5 hu hv e

lemma edgeX {m : ℕ} {u v : Fin (2 * m)} (a : (SimpleGraph.pathGraph (2 * m)).Adj u v)
    (x : Fin (2 * m) → Bool) :
    (X x (min u.val v.val) = true ∧ X x (min u.val v.val + 1) = true) ↔
      (x u = true ∧ x v = true) := by
  rw [SimpleGraph.pathGraph_adj] at a
  rcases a with e | e
  · rw [min_eq_left (by omega), e, X_fin, X_fin]
  · rw [min_eq_right (by omega), e, X_fin, X_fin, and_comm]

section
variable {m : ℕ} {C : Circuit} {d : NCCData (2 * m)}

lemma noTwo (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {r s t : Fin (2 * m)}
    (hr : r ∈ d.cover) (hs : s ∈ d.cover) (ht : t ∈ d.cover)
    (ars : (SimpleGraph.pathGraph (2 * m)).Adj r s)
    (art : (SimpleGraph.pathGraph (2 * m)).Adj r t) : s = t := by
  have inj := coverInj h.2.1
  have e1 : s.val / 2 ≠ r.val / 2 := fun e => ars.ne (inj s hs r hr e).symm
  have e2 : t.val / 2 ≠ r.val / 2 := fun e => art.ne (inj t ht r hr e).symm
  rw [SimpleGraph.pathGraph_adj] at ars art
  exact Fin.ext (by omega)

lemma noTieInto (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {t r : Fin (2 * m)}
    (ho : d.owns t r = true) (hr : r ∈ d.cover) : ∀ s ∈ d.cover, d.tie s ≠ some r := by
  intro s hs e
  have hrs := (h.2.2.2.1 s r e).2
  obtain ⟨atr, ht⟩ := h.2.2.1.1 t r ho
  obtain ⟨ars, _⟩ := h.2.2.1.1 r s hrs
  have hst := noTwo h hr hs ht ars atr.symm
  subst hst
  exact (h.2.2.1.2 _ _ atr) (ho.trans hrs.symm)

lemma zEmpty (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {t : Fin (2 * m)}
    (ht : t ∈ d.cover) (hno : ∀ s ∈ d.cover, d.tie s ≠ some t) :
    gatesOf d C Kind.z t.val = ∅ ∧ d.zroot t = t.val := by
  have tr := (h.2.2.2.2.2.1 t ht).2.1
  have hL : zLeaves d t = {t.val} := by
    ext i
    rw [dF, Finset.mem_singleton]
    constructor
    · rintro (e | ⟨s, hs, e, _⟩)
      · exact e
      · exact absurd e (hno s hs)
    · intro e
      exact Or.inl e
  have hc := gN tr
  rw [hL, Finset.card_singleton] at hc
  have hG : gatesOf d C Kind.z t.val = ∅ := Finset.card_eq_zero.mp (by omega)
  refine ⟨hG, ?_⟩
  have := tr.2.2.2
  rw [if_pos hG, hL] at this
  exact (Finset.singleton_inj.mp this).symm

lemma lamEq (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {t r : Fin (2 * m)}
    (ht : t ∈ d.cover) (ho : d.owns t r = true) : d.lam t r = r.val := by
  have L := (h.2.2.2.2.2.1 t ht).2.2.2 r ho
  unfold LamOK at L
  split_ifs at L with hr
  · rcases L.2.1 with e | ⟨j, hj, e, role⟩
    · exact e
    · exfalso
      have hG := (zEmpty h hr (noTieInto h ho hr)).1
      have hmem : j ∈ gatesOf d C Kind.z r.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, role⟩
      rw [hG] at hmem
      simp at hmem
  · exact L

lemma bVal (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {t : Fin (2 * m)}
    (ht : t ∈ d.cover) (x : Fin (2 * m) → Bool) :
    W C x (d.bw t) ↔ (x t = true ∨ ∃ s ∈ d.cover, d.tie s = some t ∧ W C x (d.bw s)) ∧
      ∃ r, d.owns t r = true ∧ x r = true := by
  obtain ⟨term, trz, tro, _⟩ := h.2.2.2.2.2.1 t ht
  rw [bO h.1 term]
  rw [fI trz h.1 (cE _ _) (W C x) (sD (x := x) h.1 trz (cE _ _)),
    fI tro h.1 (cE _ _) (W C x) (sD (x := x) h.1 tro (cE _ _))]
  apply and_congr
  · constructor
    · rintro ⟨i, hi, wi⟩
      rcases dF.mp hi with e | ⟨s, hs, e, b⟩
      · subst e
        exact Or.inl ((aC t).mp wi)
      · subst b
        exact Or.inr ⟨s, hs, e, wi⟩
    · rintro (xt | ⟨s, hs, e, ws⟩)
      · exact ⟨t.val, dF.mpr (Or.inl rfl), (aC t).mpr xt⟩
      · exact ⟨d.bw s, dF.mpr (Or.inr ⟨s, hs, e, rfl⟩), ws⟩
  · constructor
    · rintro ⟨i, hi, wi⟩
      obtain ⟨r, ho, e⟩ := iZ.mp hi
      rw [lamEq h ht ho] at e
      subst e
      exact ⟨r, ho, (aC r).mp wi⟩
    · rintro ⟨r, ho, xr⟩
      exact ⟨r.val, iZ.mpr ⟨r, ho, lamEq h ht ho⟩, (aC r).mpr xr⟩

lemma ownsSome (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {t : Fin (2 * m)}
    (ht : t ∈ d.cover) : ∃ r, d.owns t r = true := by
  have tro := (h.2.2.2.2.2.1 t ht).2.2.1
  have hc := gN tro
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (oLeaves d t).card)
  obtain ⟨r, ho, _⟩ := iZ.mp hi
  exact ⟨r, ho⟩

lemma bEF (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {t : Fin (2 * m)}
    (ht : t ∈ d.cover) : EF m C (d.bw t) := by
  classical
  let P : Fin (2 * m) × Fin (2 * m) → Prop := fun p =>
    (p.1 = t ∨ (p.1 ∈ d.cover ∧ d.tie p.1 = some t)) ∧ d.owns p.1 p.2 = true
  let S := ((Finset.univ : Finset (Fin (2 * m) × Fin (2 * m))).filter P).image
    (fun p => min p.1.val p.2.val)
  obtain ⟨r0, ho0⟩ := ownsSome h ht
  have memS : ∀ u v : Fin (2 * m), (u = t ∨ (u ∈ d.cover ∧ d.tie u = some t)) →
      d.owns u v = true → min u.val v.val ∈ S := by
    intro u v h1 h2
    exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩, rfl⟩
  refine ⟨S, ⟨_, memS t r0 (Or.inl rfl) ho0⟩, ?_, ?_⟩
  · intro i hi
    obtain ⟨⟨u, v⟩, hp, rfl⟩ := Finset.mem_image.mp hi
    have a := (h.2.2.1.1 u v (Finset.mem_filter.mp hp).2.2).1
    rw [SimpleGraph.pathGraph_adj] at a
    have := u.isLt
    have := v.isLt
    show min u.val v.val + 1 < 2 * m
    omega
  · intro x
    rw [bVal h ht x]
    constructor
    · rintro ⟨xt | ⟨s, hs, e, ws⟩, r, ho, xr⟩
      · exact ⟨_, memS t r (Or.inl rfl) ho, (edgeX (h.2.2.1.1 _ _ ho).1 x).mpr ⟨xt, xr⟩⟩
      · have hst := (h.2.2.2.1 s t e).2
        rw [bVal h hs x] at ws
        obtain ⟨xs | ⟨s', hs', e', _⟩, r', ho', xr'⟩ := ws
        · exact ⟨_, memS s r' (Or.inr ⟨hs, e⟩) ho', (edgeX (h.2.2.1.1 _ _ ho').1 x).mpr ⟨xs, xr'⟩⟩
        · exact absurd e' (noTieInto h hst hs s' hs')
    · rintro ⟨i, hi, xi⟩
      obtain ⟨⟨u, v⟩, hp, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨_, hP, ho⟩ := Finset.mem_filter.mp hp
      obtain ⟨xu, xv⟩ := (edgeX (h.2.2.1.1 _ _ ho).1 x).mp xi
      rcases hP with e | ⟨hs, e⟩
      · simp only at e
        subst e
        exact ⟨Or.inl xu, v, ho, xv⟩
      · refine ⟨Or.inr ⟨u, hs, e, ?_⟩, u, (h.2.2.2.1 _ _ e).2, xu⟩
        rw [bVal h hs x]
        exact ⟨Or.inl xu, v, ho, xv⟩

lemma topEF (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) :
    ∀ j ∈ topGates d C, EF m C (2 * m + j) := by
  have tr := h.2.2.2.2.2.2
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  have hlen := iY j hj
  obtain ⟨_, hl2, hin⟩ := tr.1 j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl2
  have hEF : ∀ i ∈ (gateAt C j).inputs, EF m C i := by
    intro i hi
    rcases hin i hi with hL | ⟨hn, hG⟩
    · rcases dA.mp hL with ⟨a, ha, _⟩ | ⟨s, hs, _, e⟩
      · simp at ha
      · rw [← e]
        exact bEF h hs
    · have hlt := h.1 j hlen i hi
      have := ih (i - 2 * m) (by omega) hG
      rwa [show 2 * m + (i - 2 * m) = i by omega] at this
  rw [hab] at hEF
  obtain ⟨Sa, hSa, hSa', ha⟩ := hEF a (by simp)
  obtain ⟨Sb, hSb, hSb', hb⟩ := hEF b (by simp)
  refine ⟨Sa ∪ Sb, hSa.mono Finset.subset_union_left, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hSa' i hi
    · exact hSb' i hi
  · intro x
    rw [sD (x := x) h.1 tr iY j hj, hab]
    simp only [List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left]
    rw [ha x, hb x]
    simp only [Finset.mem_union]
    constructor
    · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
      · exact ⟨i, Or.inl hi, hx⟩
      · exact ⟨i, Or.inr hi, hx⟩
    · rintro ⟨i, hi | hi, hx⟩
      · exact Or.inl ⟨i, hi, hx⟩
      · exact Or.inr ⟨i, hi, hx⟩

lemma efA {w : ℕ} (e : EF m C w) : ∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, i + 1 < 2 * m) ∧
    ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD w false =
      decide (∃ i j : Fin (2 * m), i.val ∈ S ∧ i.val + 1 = j.val ∧ x i = true ∧ x j = true) := by
  obtain ⟨S, h1, h2, h3⟩ := e
  refine ⟨S, h1, h2, fun x => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  change W C x w ↔ _
  rw [h3 x]
  constructor
  · rintro ⟨i, hi, xi, xj⟩
    have hj := X_lt xj
    refine ⟨⟨i, by omega⟩, ⟨i + 1, hj⟩, hi, rfl, ?_, ?_⟩
    · rw [← X_fin x ⟨i, by omega⟩]
      exact xi
    · rw [← X_fin x ⟨i + 1, hj⟩]
      exact xj
  · rintro ⟨i, j, hi, e, xi, xj⟩
    refine ⟨i.val, hi, by rw [X_fin]; exact xi, ?_⟩
    rw [e, X_fin]
    exact xj

lemma zForm (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {j : ℕ} {t : Fin (2 * m)}
    (ht : t ∈ d.cover) (hj : j ∈ gatesOf d C Kind.z t.val) :
    ∃ i jj k : Fin (2 * m), i.val % 2 = 0 ∧ i.val + 1 = jj.val ∧
      (k.val = jj.val + 1 ∨ k.val + 1 = i.val) ∧
      ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + j) false =
        ((x i && x jj) || x k) := by
  classical
  obtain ⟨s, hs, e⟩ : ∃ s ∈ d.cover, d.tie s = some t := by
    by_contra hno
    push Not at hno
    rw [(zEmpty h ht hno).1] at hj
    simp at hj
  have hts := (h.2.2.2.1 s t e).2
  have ats := (h.2.2.1.1 t s hts).1
  have tr := (h.2.2.2.2.2.1 t ht).2.1
  have hL : zLeaves d t = {t.val, d.bw s} := by
    ext i
    rw [dF, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (e1 | ⟨s', hs', e', rfl⟩)
      · exact Or.inl e1
      · right
        have := noTwo h ht hs' hs (h.2.2.1.1 t s' (h.2.2.2.1 s' t e').2).1 ats
        rw [this]
    · rintro (e1 | e1)
      · exact Or.inl e1
      · exact Or.inr ⟨s, hs, e, e1.symm⟩
  have hc := gN tr
  have hcard : (gatesOf d C Kind.z t.val).card ≤ 1 := by
    have := Finset.card_insert_le t.val ({d.bw s} : Finset ℕ)
    rw [Finset.card_singleton, ← hL] at this
    omega
  have hG : gatesOf d C Kind.z t.val = {j} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hj, fun j' hj' => Finset.card_le_one.mp hcard j' hj' j hj⟩
  have hroot : d.zroot t = 2 * m + j := by
    have := tr.2.2.2
    rw [if_neg (by rw [hG]; exact Finset.singleton_ne_empty j)] at this
    obtain ⟨j', hj', e'⟩ := this
    rw [hG, Finset.mem_singleton] at hj'
    rw [e', hj']
  obtain ⟨r0, ho0⟩ := ownsSome h hs
  have ars0 := (h.2.2.1.1 s r0 ho0).1
  have notT : ∀ r, d.owns s r = true → r.val ≠ t.val := by
    intro r ho er
    have : r = t := Fin.ext er
    subst this
    exact (h.2.2.1.2 _ _ ats) (hts.trans ho.symm)
  have inj := coverInj h.2.1
  have hst2 : t.val / 2 ≠ s.val / 2 := fun e2 => ats.ne (inj t ht s hs e2)
  have uniq : ∀ r, d.owns s r = true → r = r0 := by
    intro r ho
    have ar := (h.2.2.1.1 s r ho).1
    have n1 := notT r ho
    have n0 := notT r0 ho0
    have a1 := ats
    have a0 := ars0
    rw [SimpleGraph.pathGraph_adj] at ar a0 a1
    have := r.isLt
    have := r0.isLt
    have := t.isLt
    exact Fin.ext (by omega)
  have hval : ∀ x : Fin (2 * m) → Bool,
      W C x (2 * m + j) ↔ x t = true ∨ (x s = true ∧ x r0 = true) := by
    intro x
    rw [← hroot, fI tr h.1 (cE _ _) (W C x) (sD (x := x) h.1 tr (cE _ _)), hL]
    simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
    rw [aC, bVal h hs x]
    have nt := noTieInto h hts hs
    constructor
    · rintro (xt | ⟨xs | ⟨s', hs', e', _⟩, r, ho, xr⟩)
      · exact Or.inl xt
      · rw [uniq r ho] at xr
        exact Or.inr ⟨xs, xr⟩
      · exact absurd e' (nt s' hs')
    · rintro (xt | ⟨xs, xr⟩)
      · exact Or.inl xt
      · exact Or.inr ⟨Or.inl xs, r0, ho0, xr⟩
  have n0 := notT r0 ho0
  have a1 := ats
  have a0 := ars0
  rw [SimpleGraph.pathGraph_adj] at a1 a0
  have := r0.isLt
  have := t.isLt
  by_cases hlt : s.val < r0.val
  · refine ⟨s, r0, t, by omega, by omega, by omega, fun x => ?_⟩
    apply Bool.eq_iff_iff.mpr
    change W C x (2 * m + j) ↔ _
    rw [hval x]
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    tauto
  · refine ⟨r0, s, t, by omega, by omega, by omega, fun x => ?_⟩
    apply Bool.eq_iff_iff.mpr
    change W C x (2 * m + j) ↔ _
    rw [hval x]
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    tauto

lemma oForm (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {j : ℕ} {t : Fin (2 * m)}
    (ht : t ∈ d.cover) (hj : j ∈ gatesOf d C Kind.o t.val) :
    ∃ c : Fin (2 * m), 1 ≤ c.val ∧ c.val + 1 < 2 * m ∧
      ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + j) false =
        decide (∃ k : Fin (2 * m), (k.val + 1 = c.val ∨ k.val = c.val + 1) ∧ x k = true) := by
  classical
  have tr := (h.2.2.2.2.2.1 t ht).2.2.1
  have hL : oLeaves d t = (Finset.univ.filter (fun r => d.owns t r = true)).image Fin.val := by
    ext i
    rw [iZ, Finset.mem_image]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, ho, rfl⟩
      exact ⟨r, ho, (lamEq h ht ho).symm⟩
    · rintro ⟨r, ho, rfl⟩
      exact ⟨r, ho, lamEq h ht ho⟩
  have hc := gN tr
  have hpos : 0 < (gatesOf d C Kind.o t.val).card := Finset.card_pos.mpr ⟨j, hj⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (oLeaves d t).card)
  rw [hL] at ha hb
  obtain ⟨r1, hr1, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨r2, hr2, rfl⟩ := Finset.mem_image.mp hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr1 hr2
  have a1 := (h.2.2.1.1 t r1 hr1).1
  have a2 := (h.2.2.1.1 t r2 hr2).1
  rw [SimpleGraph.pathGraph_adj] at a1 a2
  have := r1.isLt
  have := r2.isLt
  have := t.isLt
  have all : ∀ r : Fin (2 * m), (SimpleGraph.pathGraph (2 * m)).Adj t r → r = r1 ∨ r = r2 := by
    intro r a
    rw [SimpleGraph.pathGraph_adj] at a
    by_cases e1 : r.val = r1.val
    · exact Or.inl (Fin.ext e1)
    · exact Or.inr (Fin.ext (by omega))
  have hsub : oLeaves d t ⊆ {r1.val, r2.val} := by
    intro i hi
    rw [hL] at hi
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rcases all r (h.2.2.1.1 t r hr).1 with e | e
    · rw [e]; simp
    · rw [e]; simp
  have hcard : (gatesOf d C Kind.o t.val).card ≤ 1 := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le r1.val ({r2.val} : Finset ℕ)
    rw [Finset.card_singleton] at h2
    omega
  have hG : gatesOf d C Kind.o t.val = {j} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hj, fun j' hj' => Finset.card_le_one.mp hcard j' hj' j hj⟩
  have hroot : d.oroot t = 2 * m + j := by
    have := tr.2.2.2
    rw [if_neg (by rw [hG]; exact Finset.singleton_ne_empty j)] at this
    obtain ⟨j', hj', e'⟩ := this
    rw [hG, Finset.mem_singleton] at hj'
    rw [e', hj']
  refine ⟨t, by omega, by omega, fun x => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  change W C x (2 * m + j) ↔ _
  rw [← hroot, fI tr h.1 (cE _ _) (W C x) (sD (x := x) h.1 tr (cE _ _))]
  constructor
  · rintro ⟨i, hi, wi⟩
    obtain ⟨r, ho, e⟩ := iZ.mp hi
    rw [lamEq h ht ho] at e
    subst e
    have ar := (h.2.2.1.1 t r ho).1
    rw [SimpleGraph.pathGraph_adj] at ar
    exact ⟨r, by omega, (aC r).mp wi⟩
  · rintro ⟨k, hk, xk⟩
    have ak : (SimpleGraph.pathGraph (2 * m)).Adj t k := by
      rw [SimpleGraph.pathGraph_adj]; omega
    rcases all k ak with e | e
    · rw [e] at xk
      exact ⟨_, iZ.mpr ⟨_, hr1, lamEq h ht hr1⟩, (aC _).mpr xk⟩
    · rw [e] at xk
      exact ⟨_, iZ.mpr ⟨_, hr2, lamEq h ht hr2⟩, (aC _).mpr xk⟩

lemma opAO (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {j : ℕ}
    (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.or ∨ (gateAt C j).op = GateOp.and := by
  rcases h.2.2.2.2.1 j hj with htop | ⟨t, ht, e2, hb⟩
  · exact Or.inl (h.2.2.2.2.2.2.1 j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, htop⟩)).1
  · obtain ⟨term, trz, tro, _⟩ := h.2.2.2.2.2.1 t ht
    rcases hk : (d.role j).1 with _ | _ | _ | _
    · exact Or.inl (trz.1 j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, Prod.ext hk e2⟩)).1
    · exact Or.inl (tro.1 j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, Prod.ext hk e2⟩)).1
    · have hbw := hb hk
      obtain ⟨j', _, e', _, hop, _⟩ := term
      have : j' = j := by omega
      subst this
      exact Or.inr hop
    · exact Or.inl (h.2.2.2.2.2.2.1 j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hk⟩)).1

lemma gateForm (h : Valid (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅ C d) {j : ℕ}
    (hj : j < C.gates.length) :
    EF m C (2 * m + j) ∨
    (∃ c : Fin (2 * m), 1 ≤ c.val ∧ c.val + 1 < 2 * m ∧
      ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + j) false =
        decide (∃ k : Fin (2 * m), (k.val + 1 = c.val ∨ k.val = c.val + 1) ∧ x k = true)) ∨
    (∃ i jj k : Fin (2 * m), i.val % 2 = 0 ∧ i.val + 1 = jj.val ∧
      (k.val = jj.val + 1 ∨ k.val + 1 = i.val) ∧
      ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + j) false =
        ((x i && x jj) || x k)) := by
  rcases h.2.2.2.2.1 j hj with htop | ⟨t, ht, e2, hb⟩
  · exact Or.inl (topEF h j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, htop⟩))
  · rcases hk : (d.role j).1 with _ | _ | _ | _
    · exact Or.inr (Or.inr (zForm h ht
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, Prod.ext hk e2⟩)))
    · exact Or.inr (Or.inl (oForm h ht
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, Prod.ext hk e2⟩)))
    · rw [← hb hk]
      exact Or.inl (bEF h ht)
    · exact Or.inl (topEF h j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hk⟩))

end

end P172


end PEqualNP.Outside.L_meta_172_aux
theorem PEqualNP.Outside.L_meta_172 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), 1 ≤ m → PEqualNP.MetaComplexity.IsMinimalCircuit (2 * m) C → PEqualNP.MetaComplexity.circuitFun (2 * m) C = (fun x : Fin (2 * m) → Bool => decide (∃ i j : Fin (2 * m), i.val + 1 = j.val ∧ x i = true ∧ x j = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ t : ℕ, t < C.size → ((∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, i + 1 < 2 * m) ∧ ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + t) false = decide (∃ i j : Fin (2 * m), i.val ∈ S ∧ i.val + 1 = j.val ∧ x i = true ∧ x j = true)) ∨ (∃ c : Fin (2 * m), 1 ≤ c.val ∧ c.val + 1 < 2 * m ∧ ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + t) false = decide (∃ k : Fin (2 * m), (k.val + 1 = c.val ∨ k.val = c.val + 1) ∧ x k = true)) ∨ (∃ i j k : Fin (2 * m), i.val % 2 = 0 ∧ i.val + 1 = j.val ∧ (k.val = j.val + 1 ∨ k.val + 1 = i.val) ∧ ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + t) false = ((x i && x j) || x k))) := by
  intro m C hm hmin hfun
  classical
  have hK : PEqualNP.MetaComplexity.circuitFun (2 * m) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun (SimpleGraph.pathGraph (2 * m)) ∅ := by
    rw [hfun]
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true, decide_eq_true_eq,
      SimpleGraph.pathGraph_adj]
    constructor
    · rintro ⟨i, j, e, xi, xj⟩
      exact Or.inr ⟨i, j, Or.inl e, xi, xj⟩
    · rintro (⟨a, ha, _⟩ | ⟨u, v, e | e, xu, xv⟩)
      · simp at ha
      · exact ⟨u, v, e, xu, xv⟩
      · exact ⟨v, u, e, xv, xu⟩
  have hedge : ∃ u v : Fin (2 * m), (SimpleGraph.pathGraph (2 * m)).Adj u v :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by rw [SimpleGraph.pathGraph_adj]; simp⟩
  obtain ⟨d, h⟩ := (PEqualNP.Outside.L_meta_172_aux.nestedIff (2 * m) (SimpleGraph.pathGraph (2 * m)) ∅
    (SimpleGraph.isAcyclic_pathGraph _) (by simp) (Or.inr hedge) C).1 ⟨hmin, hK⟩
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] :=
      List.getD_eq_getElem _ _ hj
    rw [← hga]
    intro hc
    rcases PEqualNP.Outside.L_meta_172_aux.P172.opAO h hj with e | e
    · rw [e] at hc
      cases hc
    · rw [e] at hc
      cases hc
  · intro t ht
    rcases PEqualNP.Outside.L_meta_172_aux.P172.gateForm h ht with e | e | e
    · exact Or.inl (PEqualNP.Outside.L_meta_172_aux.P172.efA e)
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
