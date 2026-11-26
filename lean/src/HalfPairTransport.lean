import HalfPairLayout
import RegionalEightTwelveHalfModels

noncomputable section
namespace QGI.Coherent.HalfPair
open EightTwelveHalf RegionalEightTwelveStats RegionalEightTwelveHalfLaws
open SixTenCoordinates StrategyColorLaws
open FourTwelveFunctional (source)

theorem groups (A : J → C) (L : Layout A) (a : Label) : ∃ i,L.label i=a := by
  obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (L.two a).symm)
  exact ⟨i,(Finset.mem_filter.mp hi).2⟩

private theorem same_rows (A : J → C) (i k : P) (h : (rowCells A i).card=(rowCells A k).card) :
    (∀ j,i∈A j ↔ k∈A j) ↔ crossGram A i k=crossGram A i i := by
  have diagonal : crossGram A i i=(rowCells A i).card := by simp [crossGram,rowCells]
  have inter : crossGram A i k=(rowCells A i∩rowCells A k).card := by
    apply congrArg Finset.card; ext j; simp [rowCells,crossGram]
  rw [inter,diagonal]
  constructor
  · intro all
    have eq : rowCells A i=rowCells A k := by ext j; simp [rowCells,all]
    rw [eq,Finset.inter_self]
  · intro eq
    have h₁ := Finset.eq_of_subset_of_card_le Finset.inter_subset_left eq.ge
    have h₂ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (eq.trans h).ge
    intro j
    simpa only [rowCells,Finset.mem_filter,Finset.mem_univ,true_and] using Finset.ext_iff.mp (h₁.symm.trans h₂) j

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
 (p : PerfectStrategy G H K)

structure Transport {A : J → C} (L : Layout A) (F : Shore (source G) l P) (T : Shore (targetName p) l P) (B : J → C) : Prop where
  internal : ∀ i j x y, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T x) (atPoint T y) →
    (L.label i=L.label j ↔ L.label x=L.label y)
  constant : ∀ {i k}, L.label i=L.label k → ∀ j, i∈B j ↔ k∈B j
  pairColumn : ∀ a b : Label, a≠b → b≠omitted a → ∃ j, ∀ i, i∈B j ↔ L.label i=a ∨ L.label i=b

theorem transport (F : Shore (source G) l P) (Y : Shore (source G) r J)
    (T : Shore (targetName p) l P) (Z : Shore (targetName p) r J) (v : Nat)
    (L : Layout (family F Y v)) (size : ∀ j,(family F Y v j).card=4)
    (left : ∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T i) (atPoint T j)) :
    Transport p L F T (family T Z v) := by
  classical
  let A := family F Y v
  let B := family T Z v
  have law := commonLaws p
  have gram {i k x y : P} (eq : source G (atPoint F i) (atPoint F k)=targetName p (atPoint T x) (atPoint T y)) :
      crossGram A i k=crossGram B x y := by
    simpa only [A,B,crossGram,Block.overlap,decide_eq_true_eq] using Block.gram law (Block.flip law (incidence F Y T Z v)) eq
  have rowsA (i k : P) : (rowCells A i).card=(rowCells A k).card :=
    ((degrees (sourceLaws _) F Y v).2.1 i).trans ((degrees (sourceLaws _) F Y v).2.1 k).symm
  have rowsB (i k : P) : (rowCells B i).card=(rowCells B k).card :=
    ((degrees (targetLaws p) T Z v).2.1 i).trans ((degrees (targetLaws p) T Z v).2.1 k).symm
  have src (i k) : L.label i=L.label k ↔ crossGram A i k=crossGram A i i :=
    (L.distinct i k).symm.trans (same_rows A i k (rowsA i k))
  have raw (i k x y) (e : source G (atPoint F i) (atPoint F k)=targetName p (atPoint T x) (atPoint T y)) :
      (L.label i=L.label k ↔ L.label x=L.label y) := by
    rw [src,src,gram e,gram (left x y),gram ((F i).property.trans (T x).property.symm),gram (left x x)]
  have constant {i k} (h : L.label i=L.label k) : ∀ j, i∈B j ↔ k∈B j := by
    apply (same_rows B i k (rowsB i k)).mpr
    rw [←gram (left i k),←gram (left i i)]; exact (src i k).mp h
  refine ⟨raw,constant,?_⟩
  intro a b ab miss
  obtain ⟨i,hi⟩ := groups A L a
  obtain ⟨k,hk⟩ := groups A L b
  obtain ⟨j,pair⟩ := L.pairs a b ab miss
  have pos : 0<crossGram A i k := Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (L.mark j i).mpr (by rw [hi,pair]; simp),(L.mark j k).mpr (by rw [hk,pair]; simp)⟩⟩
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (pos.trans_eq (gram (left i k)))
  have mem := (Finset.mem_filter.mp hy).2
  let S (a : Label) := Finset.univ.filter (fun u => L.label u=a)
  have subset : S a∪S b⊆B y := by
    intro u hu
    rcases Finset.mem_union.mp hu with ha|hb
    · exact (constant ((Finset.mem_filter.mp ha).2.trans hi.symm) y).mpr mem.1
    · exact (constant ((Finset.mem_filter.mp hb).2.trans hk.symm) y).mpr mem.2
  have dis : Disjoint (S a) (S b) := Finset.disjoint_left.mpr (fun _ e f => ab ((Finset.mem_filter.mp e).2.symm.trans (Finset.mem_filter.mp f).2))
  have target : (B y).card=4 := by
    have h := Block.degree_eq law (incidence F Y T Z v) 0 y
    simpa only [A,B,decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter,size] using h.symm
  have eq := Finset.eq_of_subset_of_card_le subset (by rw [target,Finset.card_union_of_disjoint dis,L.two,L.two])
  exact ⟨y,fun u => by change u∈B y ↔ _; rw [←eq]; simp [S]⟩

end QGI.Coherent.HalfPair
