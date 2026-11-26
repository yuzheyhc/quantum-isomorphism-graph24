import TenTenHalves
import RegionalFourFourEight

noncomputable section
namespace QGI.Coherent.RegionalTenTen
open TenTenMoments (V)
open SixTenCoordinates (Shore atPoint Block sourceLaws)
open SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private twins from RegionalFourFourEight

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
   (p : PerfectStrategy G H K)

def entry (X : Shore (source G) l V) (Y : Shore (source G) r V) (i j : V) := source G (atPoint X i) (atPoint Y j)
def fiberAt (X : Shore (source G) l V) (Y : Shore (source G) r V) (v : Nat) (i : V) :=
  Finset.univ.filter (fun j => entry X Y i j=v)

private theorem twins_realize (X : Shore (source G) l V) (Y : Shore (source G) r V) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (shape : SplitRectangle.Twins (entry X Y)) : Realizes p reg := by
  let keep := fun k => k=r
  have old := LargeOrderBlocks.small p keep ((RegionalTwoAnchor.card Y).le.trans (by decide))
  let anchor : Region (source G) keep := ⟨atPoint Y 0,(mem_vertices _ _ _).mpr (Y 0).property⟩
  have ht : source G anchor.val anchor.val=r := (Y 0).property
  have rect : FiberPairExtension.twins (source G) l (source G anchor.val anchor.val) := ht ▸ twins X Y shape
  apply RegionalFourFourEight.restrict_map p (FiberPairExtension.attach p X 0 (by decide) keep old anchor anchor
    (fun j => Or.inl (((mem_vertices _ _ _).mp j.property).trans ht.symm)) rect rect)
  exact fun i h => (cover i h).symm

theorem reduction (X : Shore (source G) l V) (Y : Shore (source G) r V) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) :
    Realizes p reg ∨ ∃ j : V, let d := (fiberAt X Y (entry X Y 0 j) 0).card
                              d=2 ∨ d=3 ∨ d=4 := by
  classical
  let A := entry X Y
  let S := fiberAt X Y
  let B (v : Nat) (i j : V) := decide (A i j=v)
  have named (v) : Block X X Y Y (B v) (B v) := fun ⦃_ _ _ _⦄ e => congrArg (fun t => decide (t=v)) e
  have rows (v i) : (S v i).card=(S v 0).card := by
    simpa only [S,fiberAt,A,B,decide_eq_true_eq] using Block.degree_eq (sourceLaws _) (named v) i 0
  by_cases doneAlready : Realizes p reg
  · exact Or.inl doneAlready
  right
  by_contra none
  have five (j : V) : 5≤(S (A 0 j) 0).card := by
    let v := A 0 j
    have inside : j∈S v 0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    have pos := Finset.card_pos.mpr ⟨j,inside⟩
    have no1 : (S v 0).card≠1 := by
      intro one
      obtain ⟨u,only⟩ := Finset.card_eq_one.mp one
      have unit (z) (hz : z∈S v 0) : z=u := Finset.mem_singleton.mp (only ▸ hz)
      have old := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.card X).le.trans (by decide))
      apply doneAlready (RegionalFourFourEight.functional p old cover (atPoint X 0) (atPoint Y j) (X 0).property (Y j).property ?_)
      intro z eq
      have ht := (Relations.end_colors (closure G) eq).2.trans (Y j).property
      let k := Y.symm ⟨z,ht⟩
      have loc : atPoint Y k=z := congrArg Subtype.val (Y.apply_symm_apply _)
      have mem : k∈S v 0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by change source G (atPoint X 0) (atPoint Y k)=_; rw [loc]; exact eq⟩
      exact loc.symm.trans (congrArg (atPoint Y) ((unit k mem).trans (unit j inside).symm))
    have out : ¬((S v 0).card=2 ∨ (S v 0).card=3 ∨ (S v 0).card=4) := fun e => none ⟨j,e⟩
    change 5≤(S v 0).card; omega
  let v := A 0 0
  by_cases uniform : ∀ i j, A i j=v
  · exact doneAlready (twins_realize p X Y reg cover ⟨fun i k _ _ j => (uniform i j).trans (uniform k j).symm,
      fun _ j k _ i => (uniform i j).trans (uniform i k).symm⟩)
  push_neg at uniform
  obtain ⟨i₁,j₁,ne⟩ := uniform
  let w := A i₁ j₁
  have existsW : ∃ j, A 0 j=w := by
    have pos := Finset.card_pos.mpr (show (S w i₁).Nonempty from ⟨j₁,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩)
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (pos.trans_eq (rows w i₁))
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  obtain ⟨j,hj⟩ := existsW
  have fv := five 0
  have fw := five j
  rw [hj] at fw
  have dis (i) : Disjoint (S v i) (S w i) := Finset.disjoint_left.mpr (fun k h t => ne (((Finset.mem_filter.mp t).2).symm.trans (Finset.mem_filter.mp h).2))
  have cap := Finset.card_le_univ (S v 0∪S w 0)
  rw [Finset.card_union_of_disjoint (dis 0),Fintype.card_fin] at cap
  have dv : (S v 0).card=5 := by change 5≤(S v 0).card at fv; omega
  have dw : (S w 0).card=5 := by omega
  have palette (i j) : A i j=v ∨ A i j=w := by
    have both : S v i∪S w i=Finset.univ := Finset.eq_univ_of_card _ (by rw [Finset.card_union_of_disjoint (dis i),rows v i,rows w i,dv,dw]; decide)
    have mem : j∈S v i∪S w i := by rw [both]; exact Finset.mem_univ _
    simpa only [S,A,fiberAt,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using mem
  have rd (i) : FiberRectangles.degree (B v i)=5 := by simpa only [FiberRectangles.degree,B,A,decide_eq_true_eq,S,fiberAt] using (rows v i).trans dv
  have cd := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) (named v))
  have bal := FiberRectangles.balance (B v) rd (fun j => cd j 0)
  have ct (j) : FiberRectangles.degree (fun i => B v i j)=5 := (cd j 0).trans (by omega)
  have para := TenTenHalves.parallel (sourceLaws _) X Y v rfl (B v) (fun i j => by simp [B,A,entry]) rd ct
  let ls (i : V) := B v i 0
  let rs (j : V) := B v 0 j
  have mark (i j) : A i j=v ↔ ls i=rs j := by
    have hit : A i j=v ↔ B v i j=true := by simp [B]
    have first : B v 0 0=true := by simp [B,v]
    rw [hit]; change B v i j=true ↔ B v i 0=B v 0 j
    rcases para i with h|h
    · rw [h j,h 0,first]; exact eq_comm
    · rw [h j,h 0,first]; cases B v 0 j <;> decide
  have model : A=fun i j => if ls i=rs j then v else w := by
    funext i j
    by_cases h : ls i=rs j
    · rw [if_pos h]; exact (mark i j).mpr h
    · rw [if_neg h]; exact (palette i j).resolve_left (mt (mark i j).mp h)
  apply doneAlready (twins_realize p X Y reg cover ?_)
  change SplitRectangle.Twins A
  rw [model]
  exact SplitRectangle.twins_of_halves ls rs v w

end QGI.Coherent.RegionalTenTen
