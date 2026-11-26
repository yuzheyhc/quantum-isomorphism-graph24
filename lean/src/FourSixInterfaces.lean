import FourSixSixGeometry
import SplitRectangleGluing
import SixTenCrossNormal
import Mathlib.Data.Fin.VecNotation

noncomputable section
namespace QGI.Coherent.FourSixSix.Interfaces

open FourSixSix SixTenCoordinates

abbrev Table := I → E → Nat
abbrev Bits := I → E → Bool
def select (M : Table) (v : Nat) (i : I) (j : E) := decide (M i j = v)
def cells {n : Nat} {c : Fin n → Fin n → Nat} {l v : Nat}
    (F : Shore c l I) (S : Shore c v E) : Table := fun i j => c (atPoint F i) (atPoint S j)
def flag (i : I) (j : E) : Bool := decide (QGI.MixedFourSixSix.N i j = 1)

private theorem two {M : Table} (bireg : FiberRectangles.BiregularColors M) :
    (∃ v, ∀ i j, M i j=v) ∨ (∃ v w, v≠w ∧ (∀ i j, M i j=v ∨ M i j=w) ∧
      (∀ i, FiberRectangles.degree (select M v i) = 3) ∧
      (∀ j, FiberRectangles.degree (fun i => select M v i j) = 2)) := by
  classical
  let v := M 0 0
  by_cases all : ∀ i j, M i j = v
  · exact Or.inl ⟨v,all⟩
  push_neg at all
  obtain ⟨a,b,hab⟩ := all
  let w := M a b
  let S (k : Nat) (i : I) := Finset.univ.filter (fun j : E => M i j = k)
  have deg (k : Nat) (i : I) : FiberRectangles.degree ((select M) k i) = (S k i).card := by
    simp [FiberRectangles.degree,select,S]
  obtain ⟨r₁,s₁,hr₁,hs₁⟩ := bireg v
  obtain ⟨r₂,s₂,hr₂,hs₂⟩ := bireg w
  have bal₁ := FiberRectangles.balance ((select M) v) hr₁ hs₁
  have bal₂ := FiberRectangles.balance ((select M) w) hr₂ hs₂
  have card₁ (i : I) : (S v i).card = r₁ := (deg v i).symm.trans (hr₁ i)
  have card₂ (i : I) : (S w i).card = r₂ := (deg w i).symm.trans (hr₂ i)
  have pos₁ : 0 < r₁ := (card₁ 0) ▸ Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have pos₂ : 0 < r₂ := (card₂ a) ▸ Finset.card_pos.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have disj (i : I) : Disjoint (S v i) (S w i) := by
    refine Finset.disjoint_left.mpr fun j hv hw => ?_
    exact hab ((Finset.mem_filter.mp hw).2.symm.trans (Finset.mem_filter.mp hv).2)
  have size (i : I) : (S v i ∪ S w i).card = r₁+r₂ := by
    rw [Finset.card_union_of_disjoint (disj i),card₁,card₂]
  have bound := Finset.card_le_univ (S v 0 ∪ S w 0)
  rw [size] at bound
  change r₁+r₂ ≤ 6 at bound
  change 4*r₁ = 6*s₁ at bal₁
  change 4*r₂ = 6*s₂ at bal₂
  have num : r₁=3 ∧ s₁=2 ∧ r₂=3 := by omega
  refine Or.inr ⟨v,w,Ne.symm hab,?_,fun i => (hr₁ i).trans num.1,fun j => (hs₁ j).trans num.2.1⟩
  intro i j
  have full : S v i ∪ S w i = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [size,num.1,num.2.2]; decide)
  have mem : j ∈ S v i ∪ S w i := full ▸ Finset.mem_univ _
  simpa only [Finset.mem_union,S,Finset.mem_filter,Finset.mem_univ,true_and] using mem

private theorem identify : ∀ m ∈ List.range 16,
    (Finset.univ.filter (fun i : I => m.testBit i.val = true)).card = 2 →
    ∃ j : E, ∀ i : I, m.testBit i.val = flag i j := by decide

theorem column_eq : ∀ x y : E, ((Finset.univ.filter (fun i : I =>
    flag i x = true ∧ flag i y = true)).card = 2) ↔ x=y := by decide

private def sameRows (e : E → E) : Prop :=
  (∀ i x j, flag i (e j) = flag x (e j) → ∀ y, flag i (e y) = flag x (e y)) ∧
  (∀ i j y, flag i (e j) = flag i (e y) → ∀ x, flag x (e j) = flag x (e y))

private instance (e : E → E) : Decidable (sameRows e) := by unfold sameRows; infer_instance

private theorem finite_geometry : ∀ (a b c d f g : E), let e : E → E := ![a,b,c,d,f,g];
    (∀ i : I, (Finset.univ.filter (fun h => flag i (e h) = true)).card = 3) →
    (∀ j v : E, (Finset.univ.filter (fun h => e j = e h)).card =
      (Finset.univ.filter (fun h => e v = e h)).card) →
    (∀ i j, e i=e j → i=j) ∨ sameRows e := by native_decide

theorem columnChoice {X : Type} {B : I → X → Bool} (cols : ∀ j, FiberRectangles.degree (fun i => B i j) = 2) :
    ∃ e : X → E, ∀ i j, B i j = flag i (e j) := by
  have pick (j : X) : ∃ q : E, ∀ i : I, B i j = flag i q := by
    let m := QGI.SixTen.Cross.encode (fun i => B i j)
    have bits (i : I) : m.testBit i.val = B i j := QGI.SixTen.Cross.decode _ _
    obtain ⟨q,h⟩ := identify m (List.mem_range.mpr (QGI.SixTen.Cross.encode_lt _)) (by
      simpa only [bits] using cols j)
    exact ⟨q,fun i => (bits i).symm.trans (h i)⟩
  choose e he using pick
  exact ⟨e,fun i j => he j i⟩

private theorem classify_bits {B : Bits}
    (rows : ∀ i, FiberRectangles.degree (B i) = 3)
    (cols : ∀ j, FiberRectangles.degree (fun i => B i j) = 2)
    (dup : ∀ j v : E, Block.hist (Block.overlap (fun j i => B i j)) j 2 =
      Block.hist (Block.overlap (fun j i => B i j)) v 2) :
    (∃ q : Equiv.Perm E, ∀ i j, B i j = flag i (q j)) ∨
    ((∀ i x j, B i j = B x j → ∀ y, B i y = B x y) ∧
     (∀ i j y, B i j = B i y → ∀ x, B x j = B x y)) := by
  obtain ⟨e,he⟩ := columnChoice cols
  have cv (i j : E) : (Block.overlap (fun j i => B i j)) i j = 2 ↔ e i=e j := by
    simpa only [Block.overlap,he] using column_eq (e i) (e j)
  have hs := finite_geometry (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
  have eq : (![e 0,e 1,e 2,e 3,e 4,e 5] : E → E) = e := by funext i; fin_cases i <;> rfl
  rw [eq] at hs
  have degrees (i : I) : (Finset.univ.filter fun h => flag i (e h) = true).card = 3 := by
    simpa only [FiberRectangles.degree,he] using rows i
  have counts (j v : E) : (Finset.univ.filter fun h => e j = e h).card =
      (Finset.univ.filter fun h => e v = e h).card := by
    simpa only [Block.hist,cv] using dup j v
  rcases hs degrees counts with inj | twins
  · exact Or.inl ⟨Equiv.ofBijective e (Finite.injective_iff_bijective.mp inj),he⟩
  · right; simpa only [he] using twins

/-- Classify one source-side 4-by-6 rectangle. The four-point labeling
is arbitrary and remains fixed when labeling the six tetrahedral edges. -/
theorem classify {n : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c) {l v : Nat}
    (F : Shore c l I) (S : Shore c v E) :
    (∃ n, ∀ i j, cells F S i j = n) ∨
    SplitRectangle.Twins (fun (x : {x : Fin n // c x x=l}) (y : {y : Fin n // c y y=v}) => c x.val y.val) ∨
    (∃ n, ∃ q : Equiv.Perm E, ∀ i j, cells F S i j = n ↔ incident i (q j)) := by
  let M := cells F S
  have base (n : Nat) : Block F F S S (select M n) (select M n) :=
    fun ⦃_ _ _ _⦄ eq => congrArg (fun k => decide (k=n)) eq
  have br : FiberRectangles.BiregularColors M := by
    intro n
    exact ⟨_,_,fun i => Block.degree_eq law (base n) i 0,
      fun j => Block.degree_eq law (Block.flip law (base n)) j 0⟩
  rcases two br with uniform | ⟨n,m,ne,names,rows,cols⟩
  · exact Or.inl uniform
  right
  rcases classify_bits rows cols (fun j v => Block.hist_eq law (Block.gram law (Block.flip law (base n))) j v 2) with ⟨q,h⟩ | twin
  · right; refine ⟨n,q,fun i j => ?_⟩
    have eq := congrArg (fun b : Bool => b = true) (h i j)
    simpa [select,flag,incident,M] using iff_of_eq eq
  · left
    have same (i x : I) (j y : E) : select M n i j = select M n x y ↔ M i j = M x y := by
      rcases names i j with h | h <;> rcases names x y with k | k <;> simp [select,h,k,ne,Ne.symm ne]
    constructor
    · intro i x j h y
      obtain ⟨i,rfl⟩ := F.surjective i
      obtain ⟨x,rfl⟩ := F.surjective x
      obtain ⟨j,rfl⟩ := S.surjective j
      obtain ⟨y,rfl⟩ := S.surjective y
      exact (same i x y y).mp (twin.1 i x j ((same i x j j).mpr h) y)
    · intro i j y h x
      obtain ⟨i,rfl⟩ := F.surjective i
      obtain ⟨x,rfl⟩ := F.surjective x
      obtain ⟨j,rfl⟩ := S.surjective j
      obtain ⟨y,rfl⟩ := S.surjective y
      exact (same x x j y).mp (twin.2 i j y ((same i i j y).mpr h) x)


private def meet (a b : E) : Nat := ∑ i : I, if flag i a = true ∧ flag i b = true then 1 else 0

private def diagonal (e : E → E) (a : E) : Nat := ∑ j : E, meet a (e j) * meet a (e j)

private theorem allEdges : ∀ a b c d f g : E, let e : E → E := ![a,b,c,d,f,g];
    (∀ i : I, (Finset.univ.filter (fun h => flag i (e h) = true)).card = 3) →
    (∀ i : E, diagonal e i = diagonal e 0) → ∀ x y : E, e x=e y → x=y := by native_decide

/-- A point--edge interface forces every other nonuniform four-by-six interface
to use all six distinct edges as well. -/
theorem next_to_tetra {n : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c) {l u v : Nat}
    (F : Shore c l I) (Y : Shore c u E) (S : Shore c v E) {t : Nat}
    (tetra : ∀ i j, cells F Y i j = t ↔ incident i j) :
    (∃ n, ∀ i j, cells F S i j = n) ∨
    (∃ n, ∃ q : Equiv.Perm E, ∀ i j, cells F S i j = n ↔ incident i (q j)) := by
  let M := cells F S
  have base (n : Nat) : Block F F S S (select M n) (select M n) :=
    fun ⦃_ _ _ _⦄ eq => congrArg (fun k => decide (k=n)) eq
  have br : FiberRectangles.BiregularColors M := by
    intro n
    exact ⟨_,_,fun i => Block.degree_eq law (base n) i 0,
      fun j => Block.degree_eq law (Block.flip law (base n)) j 0⟩
  rcases two br with uniform | ⟨n,_,_,_,rows,cols⟩
  · exact Or.inl uniform
  obtain ⟨e,he⟩ := columnChoice cols
  have inc : Block F F Y Y flag flag := by
    intro i j x y eq
    have same : incident i j ↔ incident x y := (tetra i j).symm.trans ((show cells F Y i j=t ↔ cells F Y x y=t by rw [show cells F Y i j = cells F Y x y from eq]).trans (tetra x y))
    exact Bool.decide_congr same
  have col : Block F F S S (fun i j => flag i (e j)) (fun i j => flag i (e j)) := by
    intro i j x y eq; exact (he i j).symm.trans ((base n eq).trans (he x y))
  have products : Block Y Y S S (fun i j => meet i (e j)) (fun i j => meet i (e j)) :=
    Block.fold law (Block.flip law inc) col (fun a b => if a=true ∧ b=true then 1 else 0)
  have gram := Block.fold law products (Block.flip law products) (· * ·)
  have stable (i : E) : diagonal e i = diagonal e 0 := Block.diag gram i 0
  have h := allEdges (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
  have eq : (![e 0,e 1,e 2,e 3,e 4,e 5] : E → E) = e := by funext i; fin_cases i <;> rfl
  rw [eq] at h
  have inj := h (fun i => by simpa only [FiberRectangles.degree,he] using rows i) stable
  let q := Equiv.ofBijective e (Finite.injective_iff_bijective.mp inj)
  refine Or.inr ⟨n,q,fun i j => ?_⟩
  have both := iff_of_eq (congrArg (fun b : Bool => b = true) (he i j))
  simpa only [select,flag,decide_eq_true_eq,M,incident,q,Equiv.ofBijective_apply] using both

end QGI.Coherent.FourSixSix.Interfaces
