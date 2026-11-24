import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_281

lemma encode_lt {k m : ℕ} (u v : Fin m) (i : Fin (2 * k)) :
    m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m := by
  have hmul : u.val * m + v.val + 1 ≤ m * m := by
    have hu : u.val + 1 ≤ m := u.isLt
    have hv : v.val + 1 ≤ m := v.isLt
    nlinarith
  have h2k : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) :=
    Nat.mul_le_mul_left (2 * k) hmul
  have hassoc : 2 * k * m * m = 2 * k * (m * m) := by ring
  have hexp : 2 * k * (u.val * m + v.val) + 2 * k = 2 * k * (u.val * m + v.val + 1) := by ring
  have hi : i.val < 2 * k := i.isLt
  omega

lemma div_eq {d a₁ b₁ a₂ b₂ : ℕ} (hb₁ : b₁ < d) (hb₂ : b₂ < d)
    (h : d * a₁ + b₁ = d * a₂ + b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have ha : a₁ = a₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : d * (a₁ + 1) ≤ d * a₂ := Nat.mul_le_mul_left d hlt
      nlinarith
    · have : d * (a₂ + 1) ≤ d * a₁ := Nat.mul_le_mul_left d hgt
      nlinarith
  subst ha
  exact ⟨rfl, by omega⟩

def incl {k m : ℕ} (u : Fin m) : Fin (m + 2 * k * m * m) :=
  ⟨u.val, by omega⟩

def thread {k m : ℕ} (u v : Fin m) (i : Fin (2 * k)) : Fin (m + 2 * k * m * m) :=
  ⟨m + 2 * k * (u.val * m + v.val) + i.val, encode_lt u v i⟩

lemma incl_inj {k m : ℕ} : Function.Injective (@incl k m) := by
  intro a b h
  exact Fin.ext (by simpa [incl] using congrArg Fin.val h)

lemma thread_inj {k m : ℕ} {u₁ v₁ u₂ v₂ : Fin m} {i₁ i₂ : Fin (2 * k)}
    (h : thread u₁ v₁ i₁ = thread u₂ v₂ i₂) : u₁ = u₂ ∧ v₁ = v₂ ∧ i₁ = i₂ := by
  have hval : m + 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      m + 2 * k * (u₂.val * m + v₂.val) + i₂.val := congrArg Fin.val h
  have h1 : 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      2 * k * (u₂.val * m + v₂.val) + i₂.val := by omega
  obtain ⟨huv, hi⟩ := div_eq i₁.isLt i₂.isLt h1
  have huv' : m * u₁.val + v₁.val = m * u₂.val + v₂.val := by
    linarith [Nat.mul_comm u₁.val m, Nat.mul_comm u₂.val m]
  obtain ⟨hu, hv⟩ := div_eq v₁.isLt v₂.isLt huv'
  exact ⟨Fin.ext hu, Fin.ext hv, Fin.ext hi⟩

lemma incl_ne_thread {k m : ℕ} (w u v : Fin m) (i : Fin (2 * k)) :
    incl w ≠ thread u v i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [incl, thread] at hv
  have := w.isLt
  omega

def subRel (k m : ℕ) (H : SimpleGraph (Fin m)) :
    Fin (m + 2 * k * m * m) → Fin (m + 2 * k * m * m) → Prop :=
  fun x y => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
    x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
    ((i.val = 0 ∧ y.val = u.val) ∨
     (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
     (i.val + 1 = 2 * k ∧ y.val = v.val))

lemma adj_first {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k)
    {u v : Fin m} (huv : u < v) (hadj : H.Adj u v) :
    (SimpleGraph.fromRel (subRel k m H)).Adj (thread u v ⟨0, by omega⟩) (incl u) := by
  rw [SimpleGraph.fromRel_adj]
  refine ⟨(incl_ne_thread u u v ⟨0, by omega⟩).symm, Or.inl ?_⟩
  exact ⟨u, v, huv, hadj, ⟨0, by omega⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma adj_step {k m : ℕ} {H : SimpleGraph (Fin m)}
    {u v : Fin m} (huv : u < v) (hadj : H.Adj u v) {i : ℕ} (hi : i + 1 < 2 * k) :
    (SimpleGraph.fromRel (subRel k m H)).Adj (thread u v ⟨i, by omega⟩) (thread u v ⟨i + 1, hi⟩) := by
  rw [SimpleGraph.fromRel_adj]
  refine ⟨fun h => by have := congrArg Fin.val h; dsimp [thread] at this; omega, Or.inl ?_⟩
  exact ⟨u, v, huv, hadj, ⟨i, by omega⟩, rfl, Or.inr (Or.inl ⟨hi, rfl⟩)⟩

lemma adj_last {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k)
    {u v : Fin m} (huv : u < v) (hadj : H.Adj u v) :
    (SimpleGraph.fromRel (subRel k m H)).Adj (thread u v ⟨2 * k - 1, by omega⟩) (incl v) := by
  rw [SimpleGraph.fromRel_adj]
  refine ⟨(incl_ne_thread v u v ⟨2 * k - 1, by omega⟩).symm, Or.inl ?_⟩
  exact ⟨u, v, huv, hadj, ⟨2 * k - 1, by omega⟩, rfl, Or.inr (Or.inr ⟨by dsimp; omega, rfl⟩)⟩

abbrev V (k m : ℕ) := Fin (m+2*k*m*m)

def prev {k m : ℕ} (u v : Fin m) (i : Fin (2*k)) : V k m :=
  if h : i.val=0 then incl u else thread u v ⟨i.val-1,by have := i.isLt; omega⟩

def nextV {k m : ℕ} (u v : Fin m) (i : Fin (2*k)) : V k m :=
  if h : i.val+1<2*k then thread u v ⟨i.val+1,h⟩ else incl v

theorem relationCases {k m} {H : SimpleGraph (Fin m)} {x y : V k m} (h : subRel k m H x y) :
    ∃ (u v : Fin m) (i : Fin (2*k)), u<v ∧ H.Adj u v ∧ x=thread u v i ∧
    ((i.val=0 ∧ y=incl u) ∨ (∃ h : i.val+1<2*k, y=thread u v ⟨i.val+1,h⟩) ∨
      (i.val+1=2*k ∧ y=incl v)) := by
  obtain ⟨u,v,huv,ha,i,hi,hy⟩ := h
  refine ⟨u,v,i,huv,ha,Fin.ext hi,?_⟩
  rcases hy with ⟨h,h'⟩ | ⟨h,h'⟩ | ⟨h,h'⟩
  · exact Or.inl ⟨h,Fin.ext h'⟩
  · exact Or.inr (Or.inl ⟨h,Fin.ext (by simpa [thread,Nat.add_assoc] using h')⟩)
  · exact Or.inr (Or.inr ⟨h,Fin.ext h'⟩)

theorem neigh {k m} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k) (u v : Fin m) (i : Fin (2*k))
    (huv : u<v) (hadj : H.Adj u v) (w : V k m) :
    (SimpleGraph.fromRel (subRel k m H)).Adj (thread u v i) w ↔
      w=prev u v i ∨ w=nextV u v i := by
  have hi := i.isLt
  constructor
  · intro h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with h | h
    · obtain ⟨a,b,j,_,_,he,hy⟩ := relationCases h
      obtain ⟨rfl,rfl,rfl⟩ := thread_inj he
      rcases hy with ⟨hz,hw⟩ | ⟨hs,hw⟩ | ⟨hl,hw⟩
      · exact Or.inl (by simpa [prev,hz] using hw)
      · exact Or.inr (by simpa [nextV,hs] using hw)
      · exact Or.inr (by simpa [nextV,show ¬i.val+1<2*k by omega] using hw)
    · obtain ⟨a,b,j,_,_,rfl,hy⟩ := relationCases h
      rcases hy with ⟨_,he⟩ | ⟨hs,he⟩ | ⟨_,he⟩
      · exact (incl_ne_thread _ _ _ _ he.symm).elim
      · obtain ⟨rfl,rfl,rfl⟩ := thread_inj he
        left
        unfold prev
        simp
      · exact (incl_ne_thread _ _ _ _ he.symm).elim
  · rintro (rfl | rfl)
    · unfold prev
      split_ifs with hz
      · have he : i=⟨0,by omega⟩ := Fin.ext hz
        rw [he]
        exact adj_first hk huv hadj
      · have hs : i.val-1+1<2*k := by omega
        have he : (⟨i.val-1+1,hs⟩ : Fin (2*k))=i := Fin.ext (by dsimp;omega)
        simpa only [he] using (adj_step huv hadj hs).symm
    · unfold nextV
      split_ifs with hs
      · exact adj_step huv hadj hs
      · have he : i=⟨2*k-1,by omega⟩ := Fin.ext (by dsimp;omega)
        rw [he]
        exact adj_last hk huv hadj

end PEqualNP.Outside.L_meta_281

open PEqualNP.Outside.L_meta_281 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_281 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ pos : Fin (m + 2 * k * m * m) → ℕ, (∀ j : Fin (m + 2 * k * m * m), pos j = ∑ u : Fin m, ∑ v : Fin m, ∑ i : Fin (2 * k), if u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val then i.val + 1 else 0) → (∀ u v : Fin (m + 2 * k * m * m), S.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin (m + 2 * k * m * m), pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin (m + 2 * k * m * m), (∀ w : Fin (m + 2 * k * m * m), S.Adj v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1) := by
  intro k m H _ hk S hS pos hp
  subst S
  change (∀ u v : V k m, (SimpleGraph.fromRel (subRel k m H)).Adj u v → _) ∧ _
  have pt (u v : Fin m) (i : Fin (2*k)) (huv : u<v) (ha : H.Adj u v) :
      pos (thread u v i) = i.val+1 := by
    rw [hp]
    have key (a b : Fin m) (j : Fin (2*k)) :
        (if a < b ∧ H.Adj a b ∧ (thread u v i).val = m+2*k*(a.val*m+b.val)+j.val then j.val+1 else 0) =
          (if a=u then (if b=v then (if j=i then i.val+1 else 0) else 0) else 0) := by
      have eqv : (thread u v i).val = m+2*k*(a.val*m+b.val)+j.val ↔ u=a ∧ v=b ∧ i=j :=
        ⟨fun h => thread_inj (show thread u v i=thread a b j from Fin.ext h),
         by rintro ⟨rfl,rfl,rfl⟩; rfl⟩
      simp only [eqv]
      by_cases h₁ : a=u <;> by_cases h₂ : b=v <;> by_cases h₃ : j=i <;>
        simp_all <;> grind
    simp_rw [key]
    simp [Finset.sum_ite_irrel]
  have p0 (u : Fin m) : pos (incl (k:=k) u)=0 := by
    rw [hp]
    have hn (a b : Fin m) (i : Fin (2*k)) :
        (incl (k:=k) u).val ≠ m+2*k*(a.val*m+b.val)+i.val :=
        fun h => incl_ne_thread u a b i (Fin.ext h)
    simp [hn]
  have src (x y : V k m) (h : subRel k m H x y) : pos x ≠ 0 := by
    obtain ⟨u,v,i,hl,ha,rfl,_⟩ := relationCases h
    rw [pt _ _ _ hl ha]; omega
  constructor
  · intro x y h
    rw [SimpleGraph.fromRel_adj] at h
    exact h.2.imp (src _ _) (src _ _)
  · intro w hn
    have hex : ∃ (u v : Fin m) (i : Fin (2*k)), u<v ∧ H.Adj u v ∧ w=thread u v i := by
      by_contra! h
      apply hn
      rw [hp]
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      apply Finset.sum_eq_zero
      intro j _
      apply if_neg
      rintro ⟨hl,ha,hj⟩
      exact h a b j hl ha (Fin.ext hj)
    obtain ⟨u,v,i,hl,ha,rfl⟩ := hex
    rw [pt _ _ _ hl ha]
    have hlt := i.isLt
    refine ⟨by omega,prev u v i,nextV u v i,neigh hk u v i hl ha,?_,?_⟩
    · unfold prev
      split_ifs with hz
      · simp [p0,hz]
      · rw [pt _ _ _ hl ha]
        dsimp; omega
    · unfold nextV
      split_ifs with hs
      · rw [pt _ _ _ hl ha,Nat.mod_eq_of_lt (by omega)]
      · rw [p0,show i.val+1+1=2*k+1 by omega, Nat.mod_self]
