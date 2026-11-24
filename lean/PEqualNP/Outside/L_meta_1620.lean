import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1620

abbrev F := (Fin 14 → Bool) → Bool
abbrev S := Nat × Nat

def cnt : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n+1, f => cnt n f + (f n).toNat

lemma cnt_congr {f g : Nat → Bool} (n : Nat) (h : ∀ i < n, f i = g i) : cnt n f = cnt n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cnt, ih (fun i hi => h i (by omega)), h n (by omega)]

lemma cnt_add (a b : Nat) (f : Nat → Bool) : cnt (a+b) f = cnt a f + cnt b (fun i => f (a+i)) := by
  induction b with
  | zero => simp [cnt]
  | succ b ih => simp [cnt,ih,Nat.add_assoc]

lemma cnt_gate (f g : Nat → Bool) (n : Nat) :
    let a := cnt n f
    let b := cnt n g
    let m := cnt n (fun i => f i && g i)
    let j := cnt n (fun i => f i || g i)
    m ≤ a ∧ m ≤ b ∧ a ≤ j ∧ b ≤ j ∧ j ≤ n ∧ m+j = a+b := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    dsimp only at ih ⊢
    simp only [cnt]
    cases f n <;> cases g n <;> simp_all [Bool.toNat] <;> omega

def slow (n x : Nat) : Nat := cnt n x.testBit
def digit (x : Nat) : Nat := (6200905725313299744266893093789502126063071545881165772838446113976729779337224604478033454164508541879741555464632174598044869083865094223170395258822928 >>> (4*(x % 128))) &&& 15

lemma digit_correct (x : Nat) : digit x = slow 7 x := by
  have table : ∀ i : Fin 128, digit i.val = slow 7 i.val := by decide +kernel
  let i : Fin 128 := ⟨x % 128, Nat.mod_lt _ (by decide)⟩
  have eq : digit x = digit i.val := by simp [digit,i]
  rw [eq, table i]
  apply cnt_congr
  intro j hj
  change (x % 2^7).testBit j = x.testBit j
  rw [Nat.testBit_mod_two_pow x 7 j]
  simp [hj]

def pc : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, x => digit x + pc k (x >>> 7)

lemma pc_correct (k x : Nat) : pc k x = slow (7*k) x := by
  induction k generalizing x with
  | zero => simp [pc,slow,cnt]
  | succ k ih =>
    rw [pc,digit_correct,ih]
    unfold slow
    rw [show 7*(k+1) = 7+7*k by omega,cnt_add]
    congr 1
    apply cnt_congr
    intro i _
    simp [Nat.testBit_shiftRight, Nat.add_comm]

def meet (a b : S) : S := (a.1 &&& b.1,a.2 &&& b.2)
def join (a b : S) : S := (a.1 ||| b.1,a.2 ||| b.2)

def limit : Nat → Nat → Nat → Bool
  | 2,p,n => (p ≤ 2) || (p ≤ 3 && n ≥ 2) || (p ≤ 4 && n ≥ 5) ||
      (p ≤ 7 && n ≥ 8) || (p ≤ 9 && n ≥ 9) || (p ≤ 12 && n ≥ 11)
  | 3,p,n => (p ≤ 4) || (p ≤ 7 && n ≥ 2) || (p ≤ 9 && n ≥ 4) ||
      (p ≤ 14 && n ≥ 8) || (p ≤ 18 && n ≥ 9) || (p ≤ 21 && n ≥ 11)
  | 4,p,n => (p ≤ 9) || (p ≤ 14 && n ≥ 2) || (p ≤ 18 && n ≥ 4) || (n ≥ 8)
  | 5,p,n => (p ≤ 18) || (n ≥ 2)
  | _,_,_ => true

def box (a : S) : Bool := limit 2 (pc 3 a.1) (pc 2 a.2)

def posRows : Array Nat := #[129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112]
def negRows : Array Nat := #[244,314,541,1102,2087,3716,4179,5008,7426,8297,9992,10656,13504,14849]
def rawProfiles : Array S := #[(7,8788),(56,346),(448,61),(3584,1550),(28672,199),(229376,2579),(1835008,4681),(521,6305),(262210,3458),(557072,9380),(69636,5416),(1057792,10544),(133248,12736),(16672,15872)]
def part0 : List S := [(0,3),(0,5),(0,6),(0,9),(0,10),(0,12),(0,17),(0,18)]
def part1 : List S := [(0,20),(0,24),(0,33),(0,36),(0,40),(0,48),(0,65),(0,66)]
def part2 : List S := [(0,68),(0,72),(0,80),(0,129),(0,130),(0,132),(0,160),(0,192)]
def part3 : List S := [(0,258),(0,264),(0,272),(0,288),(0,320),(0,384),(0,513),(0,514)]
def part4 : List S := [(0,516),(0,520),(0,528),(0,576),(0,1026),(0,1028),(0,1032),(0,1056)]
def part5 : List S := [(0,1152),(0,1280),(0,1536),(0,2049),(0,2050),(0,2064),(0,2080),(0,2176)]
def part6 : List S := [(0,2304),(0,2560),(0,3072),(0,4097),(0,4104),(0,4128),(0,4160),(0,4224)]
def part7 : List S := [(0,4352),(0,4608),(0,5120),(0,6144),(0,8196),(0,8208),(0,8224),(0,8256)]
def part8 : List S := [(0,8320),(0,8448),(0,8704),(0,9216),(0,10240),(0,12288),(1,0),(2,0)]
def part9 : List S := [(4,0),(7,8788),(8,0),(16,0),(32,0),(56,346),(63,9054),(64,0)]
def part10 : List S := [(128,0),(256,0),(448,61),(455,8829),(504,383),(512,0),(521,6305),(527,15093)]
def part11 : List S := [(569,6651),(969,6333),(1024,0),(2048,0),(3584,1550),(3591,9822),(3593,7855),(3640,1886)]
def part12 : List S := [(4032,1599),(4096,0),(8192,0),(16384,0),(16672,15872),(16679,15956),(16696,16218),(16864,15933)]
def part13 : List S := [(17193,16033),(20256,15886),(28672,199),(28679,8919),(28728,479),(28960,16071),(29120,255),(29193,6375)]
def part14 : List S := [(32256,1743),(32768,0),(65536,0),(69636,5416),(69639,14204),(69692,5498),(70084,5437),(70157,7593)]
def part15 : List S := [(73220,5934),(86308,16168),(94212,5615),(131072,0),(133248,12736),(133255,13268),(133304,12762),(133568,12797)]
def part16 : List S := [(133769,14817),(134784,14286),(149920,16320),(161920,12743),(202884,13800),(229376,2579),(229383,10839),(229432,2907)]
def part17 : List S := [(229824,2623),(229897,6835),(231552,15315),(232960,3615),(233476,7995),(246048,15891),(258048,2775),(262144,0)]
def part18 : List S := [(262210,3458),(262215,12246),(262266,3546),(262594,3519),(262731,7587),(265794,3982),(278882,16258),(290882,3527)]
def part19 : List S := [(331846,7594),(395458,15810),(491586,3987),(524288,0),(557072,9380),(557079,9972),(557112,9726),(557520,9405)]
def part20 : List S := [(557593,15525),(560656,9902),(573744,16036),(585744,9447),(626708,13740),(690320,13796),(753680,11959),(819282,11686)]
def part21 : List S := [(1048576,0),(1057792,10544),(1057799,11124),(1057848,10618),(1058240,10557),(1058313,14769),(1060352,12094),(1074464,16176)]
def part22 : List S := [(1078272,10743),(1127428,15672),(1191040,14832),(1287168,11059),(1320002,11698),(1614864,11700),(1835008,4681),(1835015,12893)]
def part23 : List S := [(1835064,4955),(1835074,8139),(1835456,4733),(1835529,6889),(1838592,5711),(1844224,15225),(1851680,15945),(1863680,4815)]
def part24 : List S := [(1867792,14061),(1904644,5993),(1968256,13257),(2064384,6747)]
def catalogue : List S := part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7 ++ part8 ++ part9 ++ part10 ++ part11 ++ part12 ++ part13 ++ part14 ++ part15 ++ part16 ++ part17 ++ part18 ++ part19 ++ part20 ++ part21 ++ part22 ++ part23 ++ part24
def okPair (a b : S) : Bool := box (meet a b) && box (join a b)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell0 : part0.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell1 : part1.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell2 : part2.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell3 : part3.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell4 : part4.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell5 : part5.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell6 : part6.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell7 : part7.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell8 : part8.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell9 : part9.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell10 : part10.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell11 : part11.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell12 : part12.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell13 : part13.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell14 : part14.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell15 : part15.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell16 : part16.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell17 : part17.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell18 : part18.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell19 : part19.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell20 : part20.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell21 : part21.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell22 : part22.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell23 : part23.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cell24 : part24.all (fun a => catalogue.all (okPair a)) = true := by decide +kernel
lemma allPairs : catalogue.all (fun a => catalogue.all (okPair a)) = true := by
  change (part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7 ++ part8 ++ part9 ++ part10 ++ part11 ++ part12 ++ part13 ++ part14 ++ part15 ++ part16 ++ part17 ++ part18 ++ part19 ++ part20 ++ part21 ++ part22 ++ part23 ++ part24).all (fun a => catalogue.all (okPair a)) = true
  simp only [List.all_append, cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15, cell16, cell17, cell18, cell19, cell20, cell21, cell22, cell23, cell24, Bool.and_self]

def graph : F := fun z => (z 0 && z 7) || (z 0 && z 8) || (z 0 && z 10) || (z 1 && z 7) || (z 1 && z 9) || (z 1 && z 13) || (z 2 && z 8) || (z 2 && z 12) || (z 2 && z 13) || (z 3 && z 7) || (z 3 && z 11) || (z 3 && z 12) || (z 4 && z 10) || (z 4 && z 11) || (z 4 && z 13) || (z 5 && z 9) || (z 5 && z 10) || (z 5 && z 12) || (z 6 && z 8) || (z 6 && z 9) || (z 6 && z 11)

def onRows (rs : Array Nat) (f : F) (i : Nat) : Bool :=
  f (fun v => (rs[i]?.getD 0).testBit v.val)

def Rep (f : F) (s : S) : Prop :=
  (∀ i : Fin 21, onRows posRows f i.val = s.1.testBit i.val) ∧
  (∀ i : Fin 14, onRows negRows f i.val = s.2.testBit i.val)

def raw (v : Fin 14) : S := rawProfiles[v.val]?.getD (0,0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma projections : ∀ v : Fin 14, Rep (fun x => x v) (raw v) := by
  unfold Rep
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstPairs : ∀ i j : Fin 14, meet (raw i) (raw j) ∈ catalogue ∧ join (raw i) (raw j) ∈ catalogue := by
  decide +kernel

lemma rep_meet {f g : F} {a b : S} (hf : Rep f a) (hg : Rep g b) :
    Rep (fun x => f x && g x) (meet a b) := by
  constructor
  · intro i
    change (onRows posRows f i.val && onRows posRows g i.val) = (a.1 &&& b.1).testBit i.val
    rw [hf.1 i, hg.1 i, Nat.testBit_and]
  · intro i
    change (onRows negRows f i.val && onRows negRows g i.val) = (a.2 &&& b.2).testBit i.val
    rw [hf.2 i, hg.2 i, Nat.testBit_and]

lemma rep_join {f g : F} {a b : S} (hf : Rep f a) (hg : Rep g b) :
    Rep (fun x => f x || g x) (join a b) := by
  constructor
  · intro i
    change (onRows posRows f i.val || onRows posRows g i.val) = (a.1 ||| b.1).testBit i.val
    rw [hf.1 i, hg.1 i, Nat.testBit_or]
  · intro i
    change (onRows negRows f i.val || onRows negRows g i.val) = (a.2 ||| b.2).testBit i.val
    rw [hf.2 i, hg.2 i, Nat.testBit_or]

def bounded (k : Nat) (f : F) : Prop :=
  limit k (cnt 21 (onRows posRows f)) (cnt 14 (onRows negRows f)) = true

lemma of_box {f : F} {a : S} (h : Rep f a) (hb : box a = true) : bounded 2 f := by
  have ep : cnt 21 (onRows posRows f) = slow 21 a.1 :=
    cnt_congr 21 (fun i hi => h.1 ⟨i,hi⟩)
  have en : cnt 14 (onRows negRows f) = slow 14 a.2 :=
    cnt_congr 14 (fun i hi => h.2 ⟨i,hi⟩)
  unfold bounded
  rw [ep,en]
  simpa only [box,pc_correct] using hb

set_option maxHeartbeats 0 in
lemma lift_limits {k a b c d u v w z : Nat} (lo : 2 ≤ k) (hi : k ≤ 4)
    (h1 : limit k a b = true) (h2 : limit k c d = true)
    (hp : u ≤ a ∧ u ≤ c ∧ a ≤ w ∧ c ≤ w ∧ w ≤ 21 ∧ u+w = a+c)
    (hn : v ≤ b ∧ v ≤ d ∧ b ≤ z ∧ d ≤ z ∧ z ≤ 14 ∧ v+z = b+d) :
    limit (k+1) u v = true ∧ limit (k+1) w z = true := by
  interval_cases k <;> norm_num [limit] at * <;> omega

lemma bounded_step {k : Nat} (lo : 2 ≤ k) (hi : k ≤ 4) (f g : F)
    (hf : bounded k f) (hg : bounded k g) :
    bounded (k+1) (fun x => f x && g x) ∧ bounded (k+1) (fun x => f x || g x) := by
  exact lift_limits lo hi hf hg (cnt_gate (onRows posRows f) (onRows posRows g) 21)
    (cnt_gate (onRows negRows f) (onRows negRows g) 14)

def level : Nat → Set F
  | 0 => {f | ∃ v : Fin 14, f = fun x => x v}
  | 1 => {f | ∃ a ∈ catalogue, Rep f a}
  | k+2 => {f | bounded (k+2) f}

lemma closed (k : Nat) (f g : F) (hf : f ∈ level k) (hg : g ∈ level k) :
    (fun x => f x && g x) ∈ level (k+1) ∧ (fun x => f x || g x) ∈ level (k+1) := by
  match k with
  | 0 =>
    obtain ⟨i,rfl⟩ := hf
    obtain ⟨j,rfl⟩ := hg
    exact ⟨⟨_,(firstPairs i j).1,rep_meet (projections i) (projections j)⟩,
      ⟨_,(firstPairs i j).2,rep_join (projections i) (projections j)⟩⟩
  | 1 =>
    obtain ⟨a,ha,hfa⟩ := hf
    obtain ⟨b,hb,hgb⟩ := hg
    have hp := List.all_eq_true.mp (List.all_eq_true.mp allPairs a ha) b hb
    have ok : box (meet a b) = true ∧ box (join a b) = true := by
      simpa only [okPair, Bool.and_eq_true] using hp
    exact ⟨of_box (rep_meet hfa hgb) ok.1,of_box (rep_join hfa hgb) ok.2⟩
  | j+2 =>
    by_cases h : j+2 ≤ 4
    · exact bounded_step (by omega : 2 ≤ j+2) h f g hf hg
    · have hj : 3 ≤ j := by omega
      obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hj
      change bounded _ _ ∧ bounded _ _
      rw [show 3+r+2+1 = r+6 by omega]
      exact ⟨rfl,rfl⟩

set_option maxHeartbeats 0 in
lemma end_check : ¬ bounded 5 graph := by
  unfold bounded
  decide +kernel

end PEqualNP.Outside.L_meta_1620

open PEqualNP.Outside.L_meta_1620

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1620 : ¬ (∀ T : ℕ → Set ((Fin 14 → Bool) → Bool), (∀ i : Fin 14, (fun x : Fin 14 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 14 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 14 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 14 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 14 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 14 → Bool => (z 0 && z 7) || (z 0 && z 8) || (z 0 && z 10) || (z 1 && z 7) || (z 1 && z 9) || (z 1 && z 13) || (z 2 && z 8) || (z 2 && z 12) || (z 2 && z 13) || (z 3 && z 7) || (z 3 && z 11) || (z 3 && z 12) || (z 4 && z 10) || (z 4 && z 11) || (z 4 && z 13) || (z 5 && z 9) || (z 5 && z 10) || (z 5 && z 12) || (z 6 && z 8) || (z 6 && z 9) || (z 6 && z 11)) ∈ T 5) := by
  intro universal
  have start (i : Fin 14) : (fun x : Fin 14 → Bool => x i) ∈ level 0 := ⟨i,rfl⟩
  have up (k : Nat) (f : F) (hf : f ∈ level k) : f ∈ level (k+1) := by
    simpa using (closed k f f hf hf).1
  exact end_check (show graph ∈ level 5 from universal level start up closed)
