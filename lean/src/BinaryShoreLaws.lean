import RegionalEightTwelveHalfLaws
import OddHalfPartition

namespace QGI.Coherent.BinaryShore
open SixTenCoordinates
abbrev Point (n : Nat) := Fin n
abbrev Cell (n : Nat) := Finset (Fin n)
abbrev Table (n : Nat) := Fin n → Fin n → Nat
def support {k m} (B : Fin k → Fin m → Bool) (j : Fin m) := Finset.univ.filter fun i => B i j=true
def degree {k m} (B : Fin k → Fin m → Bool) (i : Fin k) := (Finset.univ.filter fun j => B i j=true).card
def count {k} (c : Table k) (s : Cell k) (i : Fin k) (u : Nat) := (s.filter fun j => c i j=u).card
def valency {k} [NeZero k] (c : Table k) (u : Nat) := count c Finset.univ 0 u
def first {k} [NeZero k] (s : Cell k) := ((List.finRange k).find? (fun j => decide (j∈s))).getD 0
def sig {k} [NeZero k] (c : Table k) (s : Cell k) (i : Fin k) := (List.finRange k).map fun j => count c s i (c 0 j)
def profile {k} [NeZero k] (c : Table k) (s : Cell k) := (sig c s (first s),sig c s (first sᶜ))
def Admits {k} [NeZero k] (c : Table k) (b : Nat) (s : Cell k) :=
  (∀ i, sig c s i=if i∈s then (profile c s).1 else (profile c s).2) ∧
  ∀ i : Fin k, valency c (c 0 i) ∣ b*count c s (first s) (c 0 i)
instance {k} [NeZero k] (c : Table k) (b : Nat) (s : Cell k) : Decidable (Admits c b s) := by unfold Admits; infer_instance

private theorem first_mem {k} [NeZero k] {s : Cell k} (h : s.Nonempty) : first s∈s := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp ((List.find?_isSome).mpr ⟨i,List.mem_finRange i,decide_eq_true hi⟩ :
    ((List.finRange k).find? (fun j => decide (j∈s))).isSome)
  have found := List.find?_some hj
  rw [first,hj]; exact of_decide_eq_true found

variable {n k m l r b d : Nat} [NeZero k] {c : Fin n → Fin n → Nat} (X : Shore c l (Fin k)) (Y : Shore c r (Fin m))
    (B : Fin k → Fin m → Bool) (M : Table k)

structure Chart : Prop where
  law : Laws c c
  bits : Block X X Y Y B B
  reflect : ∀ i j x y, B i j=B x y → c (atPoint X i) (atPoint Y j)=c (atPoint X x) (atPoint Y y)
  names : ∀ i j x y, M i j=M x y ↔ c (atPoint X i) (atPoint X j)=c (atPoint X x) (atPoint X y)
  rows : ∀ i, degree B i=b
  cols : ∀ j, (support B j).card=d

variable {X Y B M}
private theorem equal_count (A : Chart (b:=b) (d:=d) X Y B M) {i j x y} (same : B i j=B x y) (u : Nat) :
    count M (support B j) i u=count M (support B y) x u := by
  have name : Block X X X X M M := fun ⦃a b x y⦄ e => (A.names a b x y).mpr e
  have z := Block.fold A.law name A.bits (fun t bit => if t=u ∧ bit=true then 1 else 0) (A.reflect i j x y same)
  have fmt (a s) : (Finset.univ.filter (fun z => M a z=u ∧ B z s=true)).card=count M (support B s) a u := by
    congr 1; ext v; simp [support,count,and_comm]
  simpa only [Finset.sum_boole,fmt] using z

theorem product_eq (A : Chart (b:=b) (d:=d) X Y B M) (j : Fin m) (z : Fin k) (hit : B z j=true) (i x : Fin k) :
    valency M (M i x)*Block.overlap B i x=b*count M (support B j) z (M i x) := by
  let u := M i x
  let neigh := Finset.univ.filter fun a => M i a=u
  have hloc : Block X X X X (fun a v => decide (M a v=u)) (fun a v => decide (M a v=u)) :=
    fun ⦃a v c d⦄ h => congrArg (fun t => decide (t=u)) ((A.names a v c d).mpr h)
  have size : neigh.card=valency M u := by
    simpa only [neigh,valency,count,decide_eq_true_eq] using Block.degree_eq A.law hloc i 0
  have const (a) (ha : a∈neigh) : Block.overlap B i a=Block.overlap B i x :=
    Block.gram A.law A.bits ((A.names i a i x).mp (Finset.mem_filter.mp ha).2)
  have calcSum : ∑ a∈neigh, Block.overlap B i a=valency M u*Block.overlap B i x := by
    rw [Finset.sum_congr rfl const,Finset.sum_const,nsmul_eq_mul,size]
    rfl
  rw [←calcSum]
  have expand (a) : Block.overlap B i a=∑ t, if B i t=true ∧ B a t=true then 1 else 0 := by simp [Block.overlap]
  simp_rw [expand]; rw [Finset.sum_comm]
  have one (t : Fin m) : (∑ a∈neigh, if B i t=true ∧ B a t=true then 1 else 0)=
      (if B i t=true then 1 else 0)*count M (support B j) z u := by
    by_cases yes : B i t=true
    · rw [if_pos yes,one_mul,←equal_count A (yes.trans hit.symm) u]
      simp only [yes,true_and,Finset.sum_boole]
      unfold count
      apply congrArg Finset.card
      ext a; simp [support,neigh,and_comm]
    · simp [yes]
  simp_rw [one]
  rw [←Finset.sum_mul,Finset.sum_boole]
  exact congrArg (·*_) (A.rows i)

theorem necessary (A : Chart (b:=b) (d:=d) X Y B M) (positive : 0<d) (small : d<k) :
    (∀ j, Admits M b (support B j)) ∧ ∀ j y, profile M (support B j)=profile M (support B y) := by
  have inside (j) : B (first (support B j)) j=true :=
    (Finset.mem_filter.mp (first_mem (Finset.card_pos.mp (positive.trans_eq (A.cols j).symm)))).2
  have outside (j) : B (first (support B j)ᶜ) j=false := by
    have hh : 0<(support B j)ᶜ.card := by rw [Finset.card_compl,A.cols,Fintype.card_fin]; omega
    have h := Finset.mem_compl.mp (first_mem (Finset.card_pos.mp hh))
    exact Bool.eq_false_of_not_eq_true (fun eq => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩))
  have same {i j x y} (h : B i j=B x y) : sig M (support B j) i=sig M (support B y) x :=
    List.map_congr_left (fun z _ => equal_count A h _)
  refine ⟨fun j => ⟨fun i => ?_,fun i => ?_⟩,fun j y =>
    Prod.ext (same ((inside j).trans (inside y).symm)) (same ((outside j).trans (outside y).symm))⟩
  · by_cases h : i∈support B j
    · rw [if_pos h]; exact same ((Finset.mem_filter.mp h).2.trans (inside j).symm)
    · rw [if_neg h]; exact same ((Bool.eq_false_of_not_eq_true (fun e => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩))).trans (outside j).symm)
  · exact ⟨_,(product_eq A j _ (inside j) 0 i).symm⟩

end QGI.Coherent.BinaryShore
