import RegionalShorePins
import SevenFourteenAnchor
import NinePointRigidity

noncomputable section
namespace QGI.Coherent.RegionalMarkPins
open Intertwiner Synchrony SixTenCoordinates SmallUnion StrategyColorLaws RegionalShorePins
open FourTwelveFunctional (source)
open RegionalCycleExtension (emb range_emb)
open private sums from Intertwiner

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

theorem source_name {ξ : cyclic p} {x a j b : Fin n} (pin : U p j b ξ=ξ) (nz : U p x a ξ≠0) :
    source G x j=targetName p a b := by
  apply (associated p).mpr (StrategyColors.maps_support p ?_)
  intro zero
  have eq := congrArg (fun q : Module.End ℂ (cyclic p) => q ξ) zero
  change U p x a (U p j b ξ)=0 at eq
  exact nz (pin ▸ eq)

/-- Once fixed source vertices distinguish a row in its own fiber, its image
is also fixed on the same vector, by summing over the target column. -/
theorem grow {J : Type*} {ξ : cyclic p} (nz : ξ≠0) (s t : J → Fin n)
    (fixed : ∀ j, U p (s j) (t j) ξ=ξ) {k l : Nat} (S : Shore (source G) l (Fin k))
    (unique : ∀ i b, (∀ j, source G (atPoint S b) (s j)=source G (atPoint S i) (s j)) → b=i) :
    ∃ g : Fin k → Fin n, ∀ i, U p (atPoint S i) (g i) ξ=ξ := by
  classical
  choose g hg using fun i => DoubledEdges.nonzero_row p ξ nz (atPoint S i)
  refine ⟨g,fun i => ?_⟩
  have one (z : Fin n) (h : U p z (g i) ξ≠0) : z=atPoint S i := by
    have tag := (DoubledEdges.diag_of_nonzero p h).trans ((DoubledEdges.diag_of_nonzero p (hg i)).symm.trans (S i).property)
    obtain ⟨b,hb⟩ := (range_emb S z).mpr tag
    have bActive : U p (atPoint S b) (g i) ξ≠0 := by rw [show atPoint S b=z from hb]; exact h
    exact hb.symm.trans (congrArg (atPoint S) (unique i b (fun j => (source_name p (fixed j) bActive).trans (source_name p (fixed j) (hg i)).symm)))
  exact (Finset.sum_eq_single (atPoint S i) (fun z _ ne => not_not.mp (fun h => ne (one z h))) (by simp)).symm.trans (sums p (g i) ξ).2

variable [CompleteSpace K]

theorem fixed {k l : Nat} (A : Shore (source G) l (Fin k))
    (comm : ∀ i j x y, Commute (ColorTensor.P p (atPoint A i) x) (ColorTensor.P p (atPoint A j) y)) :
    ∃ (ξ : cyclic p) (g : Fin k → Fin n), ξ≠0 ∧ ∀ i, U p (atPoint A i) (g i) ξ=ξ := by
  obtain ⟨m,hm⟩ := diagonal_names p
  let T := A.trans (Equiv.subtypeEquiv m (q:=fun z => targetName p z z=l) (fun i => ⟨fun h => (hm i).symm.trans h,fun h => (hm i).trans h⟩))
  have unbounded (i j x y) : Commute (U p (atPoint A i) (atPoint T x)) (U p (atPoint A j) (atPoint T y)) := by
    ext ξ
    let z : ColorTensor.space p := ⟨ξ.val,(cyclic p).le_topologicalClosure ξ.property⟩
    exact congrArg (fun f : ColorTensor.space p →L[ℂ] ColorTensor.space p => (f z : K)) (comm i j (atPoint T x) (atPoint T y)).eq
  obtain ⟨ξ,e,nz,h⟩ := SevenFourteenAnchor.fixed_block p (emb A) (emb T) (fun i a ξ h =>
    (range_emb T a).mpr ((DoubledEdges.diag_of_nonzero p h).symm.trans (A i).property)) unbounded
  exact ⟨ξ,fun i => atPoint T (e i),nz,h⟩

theorem widen {J I : Type*} {k l : Nat} {s : J → Fin n} {t : I → Fin n} (A : Shore (source G) l (Fin k))
    (short : Short A s) (subset : ∀ j, ∃ i, t i=s j) : Short A t := by
  intro i
  apply (Finset.card_le_card ?_).trans (short i)
  intro b h
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h ⊢
  intro j
  obtain ⟨z,hz⟩ := subset j
  rw [←hz]
  exact h z

end QGI.Coherent.RegionalMarkPins
