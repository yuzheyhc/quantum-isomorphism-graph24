import LargeOrderFourFourSixSix
import RegionalMarkPins
import SixSixEightPins

noncomputable section
namespace QGI.Coherent.FourSixSixSixRoot
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion RegionalShorePins
open FourTwelveFunctional (source)
open Intertwiner (U)
open Synchrony
open SixSixEightPins (Flat)
open FourSixSix (E)
open LargeOrderSquareInterface (I)
variable {n l : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

private theorem four (F : Shore (source G) l I) : Short F (fun _ : Unit => atPoint F 0) := by
  apply one
  intro i
  by_cases zero : i=0
  · subst i
    apply (Finset.card_le_card (t:={0}) ?_).trans (by simp)
    intro j hj
    have eq := (Finset.mem_filter.mp hj).2
    have h := Relations.diagonal (closure G) eq
    exact Finset.mem_singleton.mpr (F.injective (Subtype.ext h))
  · apply (Finset.card_le_card (t:=Finset.univ.erase 0) ?_).trans (by decide)
    intro j hj
    apply Finset.mem_erase.mpr; refine ⟨?_,Finset.mem_univ _⟩
    rintro rfl
    exact zero (F.injective (Subtype.ext (Relations.diagonal _ (Finset.mem_filter.mp hj).2.symm)))

private theorem six {r} (F : Shore (source G) l I) (Y : Shore (source G) r E) (mixed : ¬Flat F Y) :
    Short Y (fun _ : Unit => atPoint F 0) := by
  let f := fun i j => source G (atPoint F i) (atPoint Y j)
  rcases OddHalfPartition.palette (p:=3) (sourceLaws _) F Y (by intro x y pos eq; omega) with ⟨v,all⟩|⟨v,w,vw,pal,rows⟩
  · exact (mixed (fun i j => (all i j).trans (all 0 0).symm)).elim
  apply one
  intro i
  let b := Finset.univ.filter (fun j => f 0 j=v)
  have sz : b.card=3 := rows 0
  have small : bᶜ.card=3 := by rw [Finset.card_compl,sz,Fintype.card_fin]
  by_cases hit : f 0 i=v
  · apply (Finset.card_le_card (t:=b) ?_).trans sz.le
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Relations.transpose _ (Finset.mem_filter.mp hj).2).trans hit⟩
  · apply (Finset.card_le_card (t:=bᶜ) ?_).trans small.le
    intro j hj
    exact Finset.mem_compl.mpr (fun hz => hit ((Relations.transpose _ (Finset.mem_filter.mp hj).2).symm.trans (Finset.mem_filter.mp hz).2))

attribute [local instance 2000] Classical.propDecidable in
theorem realize {v : Fin 3 → Nat} (F : Shore (source G) l I) (Y : ∀ j, Shore (source G) (v j) E)
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ ∃ j, source G i i=v j)
    (mixed : ∀ j, ¬Flat F (Y j)) : Realizes p reg := by
  let x := atPoint F 0
  let ψ : cyclic p := ⟨p.psi,psi_mem p⟩
  have nz : ψ≠0 := fun h => psi_ne_zero p (congrArg Subtype.val h)
  obtain ⟨y,hy⟩ := DoubledEdges.nonzero_row p ψ nz x
  let ξ := U p x y ψ
  have fix : U p x y ξ=ξ := congrArg (fun Z : Module.End ℂ (cyclic p) => Z ψ) (restricted_projection p _ _).1
  apply LargeOrderBlocks.of_solver p reg active rfl
  intro f g D
  apply RegionalTernaryChoice.source_pins p D ξ hy (fun _ : Unit => x) (fun _ => y) (fun _ => fix)
  intro i
  have bound {q h : Nat} (S : Shore (source G) q (Fin h)) (short : Short S (fun _ : Unit => x)) (tag : source G (f i) (f i)=q) :
      (Finset.univ.filter (fun b => source G (f b) (f b)=source G (f i) (f i) ∧ ∀ _ : Unit, source G (f b) x=source G (f i) x)).card≤3 := by
    obtain ⟨a,ha⟩ := (RegionalCycleExtension.range_emb S (f i)).mpr tag
    apply (RegionalSignatureBound.bound_set f D.injF (atPoint S) _ _ ?_).trans (short a)
    intro b hb; simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb
    obtain ⟨z,hz⟩ := (RegionalCycleExtension.range_emb S (f b)).mpr (hb.1.trans tag)
    refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hz⟩
    intro j; rw [show atPoint S z=f b from hz,show atPoint S a=f i from ha]; exact hb.2 j
  rcases cover _ ((D.src _).mp ⟨i,rfl⟩) with h|⟨j,h⟩
  · exact bound F (four F) h
  · exact bound (Y j) (six F (Y j) (mixed j)) h
end QGI.Coherent.FourSixSixSixRoot
