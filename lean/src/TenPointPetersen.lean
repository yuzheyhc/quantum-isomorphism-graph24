import TenPointCrossLaws
import NineTwelveSteiner
import RegionalMarkPins
import OddHalfPartition

namespace QGI.TenPointCross

abbrev Pair := {s : Finset (Fin 5) // s.card=2}
private def digits (i : V) := (![3,12,20,24,17,18,10,9,6,5] : V → Nat) i
private def vertices (i : V) := Finset.univ.filter fun k : Fin 5 => (digits i).testBit k.val=true
private theorem two : ∀ i, (vertices i).card=2 := by decide
private def vertex (i : V) : Pair := ⟨vertices i,two i⟩

theorem petersen_numbering : ∃ e : V ≃ Pair, ∀ i j, decide (cell 2 i j=1)=decide (Disjoint (e i).val (e j).val) := by
  have bij : (∀ i j, vertex i=vertex j → i=j) ∧ (∀ a : Pair, ∃ i, vertex i=a) := by native_decide
  refine ⟨Equiv.ofBijective vertex ⟨fun _ _ => bij.1 _ _,bij.2⟩,?_⟩
  change ∀ i j : V, decide (cell 2 i j=1)=decide (Disjoint (vertices i) (vertices j))
  native_decide

end QGI.TenPointCross

namespace QGI.Literature
open TenPointCross

/-- Schmidt, The Petersen graph has no quantum symmetry, Bull. Lond. Math. Soc.
50 (2018), 395–400. The Petersen graph in Kneser coordinates has the
two-subsets of five points as vertices, with disjoint pairs adjacent.
https://doi.org/10.1112/blms.12154 -/
axiom schmidt_petersen {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (g : V → V → Bool) (e : V ≃ Pair) (graph : ∀ i j, g i j=decide (Disjoint (e i).val (e j).val))
    (U : V → V → (E →L[ℂ] E)) (proj : ∀ i j, U i j*U i j=U i j ∧ U i j=(U i j).adjoint)
    (rows : ∀ i, ∑ a, U i a=1) (cols : ∀ a, ∑ i, U i a=1)
    (inter : ∀ i b, (∑ a, if g a b then U i a else 0)=∑ j, if g i j then U j b else 0) :
    ∀ i a j b, Commute (U i a) (U j b)
end QGI.Literature

noncomputable section
namespace QGI.Coherent.TenPointPetersen
open TenPointCross TenPointCrossLaws
open SixTenCoordinates (Shore atPoint sourceLaws Block)
open SmallUnion SmallFiberExtension StrategyColorLaws
open Intertwiner (U)
open FourTwelveFunctional (source)
open private incompatible from RegionalPlanar
open private uniform_fiber_dvd from HalfRectangle

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

theorem fixed (A : Shore (source G) l V) (chart : Chart A 2) :
    ∃ (ξ : Synchrony.cyclic p) (f : V → Fin n), ξ≠0 ∧ ∀ i, U p (atPoint A i) (f i) ξ=ξ := by
  classical
  obtain ⟨e,he⟩ := realize_region p (·=l) (by rw [SixSixCycle.size A]; decide) (by rw [SixSixCycle.size A]; decide)
  let R : Shore (targetName p) l V := ((SixSixCycle.regEquiv A).trans e).trans
    (Equiv.subtypeEquivRight (fun x => mem_vertices (targetName p) (·=l) x))
  have colors (i j) : source G (atPoint A i) (atPoint A j)=targetName p (atPoint R i) (atPoint R j) :=
    he (SixSixCycle.regEquiv A i) (SixSixCycle.regEquiv A j)
  let g (i j : V) := decide (cell 2 i j=1)
  let M := fun i a => ColorTensor.P p (atPoint A i) (atPoint R a)
  have mismatch (i j a b) (ne : g i j≠g a b) : M i a*M j b=0 :=
    incompatible p _ _ _ _ (fun same => ne (congrArg (fun t => decide (t=1)) ((chart _ _ _ _).mp (same.trans (colors a b).symm))))
  obtain ⟨hp,_,_⟩ := ColorTensor.quantumPermutation p
  obtain ⟨rr,cc⟩ := NineTwelveSteiner.sums p A R
  obtain ⟨label,graph⟩ := petersen_numbering
  have hc := Literature.schmidt_petersen g label graph M (fun i j => hp _ _) rr cc (NamedQuantumGraph.intertwines g M rr cc mismatch)
  have unbounded (i j x y) : Commute (U p (atPoint A i) (atPoint R x)) (U p (atPoint A j) (atPoint R y)) := by
    ext ξ
    let z : ColorTensor.space p := ⟨ξ.val,(Synchrony.cyclic p).le_topologicalClosure ξ.property⟩
    exact congrArg (fun f : ColorTensor.space p →L[ℂ] ColorTensor.space p => (f z : K)) (hc i x j y).eq
  obtain ⟨ξ,f,nz,h⟩ := SevenFourteenAnchor.fixed_block p (RegionalCycleExtension.emb A) (RegionalCycleExtension.emb R)
    (fun i a ξ h => (RegionalCycleExtension.range_emb R a).mpr ((DoubledEdges.diag_of_nonzero p h).symm.trans (A i).property)) unbounded
  exact ⟨ξ,fun i => atPoint R (f i),nz,h⟩

theorem short (A : Shore (source G) l V) (Y : Shore (source G) r V) (v : Nat)
    (sz : ∀ i, (row A Y v i).card=4) : RegionalShorePins.Short Y (atPoint A) := by
  classical
  let B (j i : V) := decide (entry A Y i j=v)
  have d (j) : FiberRectangles.degree (B j)=4 := by
    simpa only [FiberRectangles.degree,B,decide_eq_true_eq,col] using (col_size A Y (sourceLaws _) v 0 j).trans (sz 0)
  have cb := OddHalfPartition.column_block (v:=v) (sourceLaws _) A Y B (fun _ _ => by simp [B,entry]) d
  let C (j : V) := Finset.univ.filter fun k => B k=B j
  let m := (C 0).card
  have sizes (j) : (C j).card=m := by
    have rev (i k : V) : decide (B i=B k)=true ↔ B k=B i := by rw [decide_eq_true_eq]; exact eq_comm
    simpa only [C,m,rev] using Block.degree_eq (sourceLaws _) cb j 0
  have divides := uniform_fiber_dvd B m sizes
  intro j
  have positive : 0<(col A Y v j).card := (by decide : 0<4).trans_eq ((col_size A Y (sourceLaws _) v 0 j).trans (sz 0)).symm
  obtain ⟨i,hi⟩ := Finset.card_pos.mp positive
  have cap : m≤4 := by
    rw [←sizes j,←sz i]
    apply Finset.card_le_card; intro k hk
    have eq := congrFun (Finset.mem_filter.mp hk).2 i
    have hit : B j i=true := decide_eq_true (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,of_decide_eq_true (eq.trans hit)⟩
  have not4 : m≠4 := fun h => (by decide : ¬4∣10) (h ▸ divides)
  apply (Finset.card_le_card (t:=C j) ?_).trans ((sizes j).le.trans (by omega))
  intro k hk
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hk
  have same := hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,funext (fun i => congrArg (fun t => decide (t=v)) (Relations.transpose _ (same i)))⟩

theorem realize (A : Shore (source G) l V) (Y : Shore (source G) r V) (chart : Chart A 2)
    (v : Nat) (sz : ∀ i, (row A Y v i).card=4) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) : Realizes p reg := by
  obtain ⟨ξ,f,nz,fix⟩ := fixed p A chart
  have s := RegionalShorePins.pinned A
  apply RegionalShorePins.realize p A Y Y reg _ (fun i h => (cover i h).imp_right Or.inl) ξ nz (atPoint A) f fix s (short A Y v sz) (short A Y v sz)
  intro i h; rcases cover i h with h|h
  · rw [h,LargeFourteenRegion.large,RegionalTwoAnchor.card A]; decide
  · rw [h,LargeFourteenRegion.large,RegionalTwoAnchor.card Y]; decide

end QGI.Coherent.TenPointPetersen
