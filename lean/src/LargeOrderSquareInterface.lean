import LargeOrderStrongPaths
import RegionalFourFourEight

noncomputable section
namespace QGI.Coherent.LargeOrderSquareInterface
open SixTenCoordinates LargeOrderStrongPaths FiberPairExtension
open FourTwelveFunctional (source)
open private twins from RegionalFourFourEight

abbrev I := Fin 4
abbrev Shape {n l r X Y} {c : Fin n → Fin n → Nat} (F : Shore c l X) (S : Shore c r Y)
    (m : X → Y → Bool) := Block F F S S m m

def Pin {n l r X Y} {c : Fin n → Fin n → Nat} (F : Shore c l X) (S : Shore c r Y) : Prop :=
  ∃ i j, ∀ z, c (atPoint F i) (atPoint S z)=c (atPoint F i) (atPoint S j) → z=j

private def BoolTwins (B : I → I → Bool) :=
  (∀ i x j, B i j=B x j → ∀ y, B i y=B x y) ∧ (∀ i j y, B i j=B i y → ∀ x, B x j=B x y)

private instance (B : I → I → Bool) : Decidable (BoolTwins B) := by
  unfold BoolTwins; infer_instance

private theorem normal : ∀ B : I → I → Bool,
    (∀ i, FiberRectangles.degree (B i)=2) → (∀ j, FiberRectangles.degree (fun i => B i j)=2) →
    BoolTwins B ∨ ∃ h k : Equiv.Perm I, ∀ i j, B i j=cycle (h i) (k j) := by native_decide

def colors {n l r} {c : Fin n → Fin n → Nat} (F : Shore c l I) (S : Shore c r I) (i j : I) :=
  c (atPoint F i) (atPoint S j)

theorem binary {n l r} {c : Fin n → Fin n → Nat} (law : Laws c c) (F : Shore c l I) (S : Shore c r I)
    (pin : ¬Pin F S) (uniform : ¬∀ i j, colors F S i j=colors F S 0 0) :
    ∃ B : I → I → Bool, B 0 0=true ∧ (∀ i, FiberRectangles.degree (B i)=2) ∧
      (∀ j, FiberRectangles.degree (fun i => B i j)=2) ∧
      ∀ i j x y, B i j=B x y ↔ colors F S i j=colors F S x y := by
  classical
  let M := fun i j => c (atPoint F i) (atPoint S j)
  let s := M 0 0
  change ¬∀ i j, M i j=s at uniform
  push_neg at uniform
  obtain ⟨x,y,hs⟩ := uniform
  let t := M x y
  let B (v : Nat) (i j : I) := decide (M i j=v)
  let N (v : Nat) (i : I) := Finset.univ.filter (fun j => M i j=v)
  have base (v : Nat) : Shape F S (B v) := fun ⦃_ _ _ _⦄ h => congrArg (fun z => decide (z=v)) h
  have rows (v : Nat) (i j : I) : (N v i).card=(N v j).card := by
    simpa only [N,B,decide_eq_true_eq] using Block.degree_eq law (base v) i j
  have two (i j : I) : 2≤(N (M i j) i).card := by
    by_contra! small
    have one := Finset.card_le_one.mp (show (N (M i j) i).card≤1 by omega)
    exact pin ⟨i,j,fun z h => one z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)⟩
  have disj (i : I) : Disjoint (N s i) (N t i) := Finset.disjoint_left.mpr fun j h k =>
    hs ((Finset.mem_filter.mp k).2.symm.trans (Finset.mem_filter.mp h).2)
  have both (i : I) : (N s i).card=2 ∧ (N t i).card=2 := by
    have a := (two 0 0).trans_eq (rows s 0 i)
    have b := (two x y).trans_eq (rows t x i)
    have sz := Finset.card_le_univ (N s i ∪ N t i)
    rw [Finset.card_union_of_disjoint (disj i)] at sz
    change _ ≤ 4 at sz
    omega
  have palette (i j : I) : M i j=s ∨ M i j=t := by
    have all : N s i ∪ N t i=Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_union_of_disjoint (disj i),(both i).1,(both i).2]; decide)
    have hit : j ∈ N s i ∪ N t i := all ▸ Finset.mem_univ _
    simpa only [Finset.mem_union,N,Finset.mem_filter,Finset.mem_univ,true_and] using hit
  have deg (i : I) : FiberRectangles.degree (B s i)=2 := by
    simpa only [FiberRectangles.degree,B,decide_eq_true_eq] using (both i).1
  have cols (j : I) := Block.degree_eq law (Block.flip law (base s)) j 0
  have bal := FiberRectangles.balance (B s) deg (fun j => cols j)
  change 4*2=4*FiberRectangles.degree (fun i => B s i 0) at bal
  have degCol : FiberRectangles.degree (fun i => B s i 0)=2 := by omega
  refine ⟨B s,by simp [B,s],deg,fun j => (cols j).trans degCol,?_⟩
  intro i j x y
  change B s i j=B s x y ↔ M i j=M x y
  have diff : t≠s := hs
  rcases palette i j with l|l <;> rcases palette x y with r|r <;> simp [B,l,r,diff,Ne.symm diff]

theorem classify {n l r} {c : Fin n → Fin n → Nat} (law : Laws c c) (F : Shore c l I) (S : Shore c r I) :
    Pin F S ∨ FiberPairExtension.twins c l r ∨ ∃ h k : Equiv.Perm I,
      Shape F S (fun i j => cycle (h i) (k j)) := by
  classical
  by_cases pin : Pin F S
  · exact Or.inl pin
  right
  let M := fun i j => c (atPoint F i) (atPoint S j)
  let s := M 0 0
  by_cases uniform : ∀ i j, M i j=s
  · exact Or.inl (twins F S ⟨fun i x _ _ y => (uniform i y).trans (uniform x y).symm,
      fun _ j y _ x => (uniform x j).trans (uniform x y).symm⟩)
  obtain ⟨B,_,deg,cols,same⟩ := binary law F S pin uniform
  rcases normal B deg cols with h | ⟨a,b,eq⟩
  · apply Or.inl (twins F S ?_)
    exact ⟨fun i x j hit y => (same i y x y).mp (h.1 i x j ((same i j x j).mpr hit) y),
      fun i j y hit x => (same x j x y).mp (h.2 i j y ((same i j i y).mpr hit) x)⟩
  · exact Or.inr ⟨a,b,fun ⦃i j x y⦄ h => (eq i j).symm.trans (((same i j x y).mpr h).trans (eq x y))⟩

end QGI.Coherent.LargeOrderSquareInterface

namespace QGI.Coherent.LargeOrderSquareInterface
open SixTenCoordinates FourSixSix LargeOrderStrongPaths
open FourSixSix.Interfaces (flag)
open private twins from RegionalFourFourEight

def MapsOne {n} (c : Fin n → Fin n → Nat) (l r : Nat) :=
  ∃ x y, c x x=l ∧ c y y=r ∧ ∀ z, c x z=c x y → z=y

def CycleAt {n} (c : Fin n → Fin n → Nat) (l r : Nat) :=
  ∃ (F : Shore c l I) (S : Shore c r I), Shape F S cycle

def TetraAt {n} (c : Fin n → Fin n → Nat) (l v : Nat) :=
  ∃ (F : Shore c l I) (Y : Shore c v E), Shape F Y flag

private theorem maps_one {n l r X Y} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l X) (S : Shore c r Y) (h : Pin F S) : MapsOne c l r := by
  obtain ⟨i,j,one⟩ := h
  refine ⟨atPoint F i,atPoint S j,(F i).property,(S j).property,fun z h => ?_⟩
  let t := S.symm ⟨z,(law.last h).trans (S j).property⟩
  have ht : atPoint S t=z := congrArg Subtype.val (S.apply_symm_apply _)
  exact ht.symm.trans (congrArg (atPoint S) (one t (by rw [ht]; exact h)))

theorem square {n l r} {c : Fin n → Fin n → Nat} (law : Laws c c) (F : Shore c l I) (S : Shore c r I) :
    MapsOne c l r ∨ FiberPairExtension.twins c l r ∨ CycleAt c l r := by
  rcases classify law F S with one|twin|⟨a,b,shape⟩
  · exact Or.inl (maps_one law F S one)
  · exact Or.inr (Or.inl twin)
  · refine Or.inr (Or.inr ⟨a.symm.trans F,b.symm.trans S,fun ⦃i j x y⦄ h => ?_⟩)
    simpa only [Equiv.apply_symm_apply] using shape (i:=a.symm i) (j:=b.symm j) (x:=a.symm x) (y:=b.symm y) h

theorem four_six {n l v} {c : Fin n → Fin n → Nat} (law : Laws c c) (F : Shore c l I) (S : Shore c v E) :
    FiberPairExtension.twins c l v ∨ TetraAt c l v := by
  rcases Interfaces.classify law F S with ⟨s,all⟩|twin|⟨s,b,edge⟩
  · apply Or.inl (twins F S ?_)
    exact ⟨fun i x _ _ y => (all i y).trans (all x y).symm,fun _ j y _ x => (all x j).trans (all x y).symm⟩
  · exact Or.inl twin
  · refine Or.inr ⟨F,b.symm.trans S,fun ⦃i j x y⦄ h => ?_⟩
    apply Bool.decide_congr
    have eq : Interfaces.cells F S i (b.symm j)=Interfaces.cells F S x (b.symm y) := h
    have same : Interfaces.cells F S i (b.symm j)=s ↔ Interfaces.cells F S x (b.symm y)=s := by rw [eq]
    simpa only [Equiv.apply_symm_apply] using (edge i (b.symm j)).symm.trans (same.trans (edge x (b.symm y)))

theorem cycles_force {n l r v} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (a : CycleAt c l v) (b : CycleAt c r v) : MapsOne c l r := by
  obtain ⟨F,L,left⟩ := a
  obtain ⟨S,R,right⟩ := b
  obtain ⟨h,mix,reg⟩ := path law F S L R cycle cycle left right 0
  obtain ⟨j,hj⟩ := cycles h reg
  exact maps_one law F S ⟨0,j,fun z eq => hj z (mix eq)⟩

theorem tetra_force {n l r v} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (a : TetraAt c l v) (b : TetraAt c r v) : MapsOne c l r := by
  obtain ⟨F,L,left⟩ := a
  obtain ⟨S,R,right⟩ := b
  obtain ⟨h,mix,reg⟩ := path law F S L R flag flag left right 0
  obtain ⟨j,hj⟩ := tetrahedra h reg
  exact maps_one law F S ⟨0,j,fun z eq => hj z (mix eq)⟩

theorem cycle_reverse {n l r} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (a : CycleAt c l r) : CycleAt c r l := by
  obtain ⟨F,S,hit⟩ := a
  refine ⟨S,F,fun ⦃i j x y⦄ eq => ?_⟩
  simpa only [cycle,Nat.add_comm] using (Block.flip law hit) eq

theorem mixed_false {n l r v} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (a : TetraAt c v l) (b : CycleAt c r v) : False := by
  obtain ⟨N,F,edge⟩ := a
  obtain ⟨S,M,square⟩ := b
  obtain ⟨h,_,reg⟩ := path law F S N M (fun j k => flag k j) cycle (Block.flip law edge) square 0
  exact mixed h reg

end QGI.Coherent.LargeOrderSquareInterface
