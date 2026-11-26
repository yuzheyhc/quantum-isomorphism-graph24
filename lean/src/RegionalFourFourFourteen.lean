import TwoShoreAttachment
import LargeOrderFourteen
import FourByEven

noncomputable section
namespace QGI.Coherent.RegionalFourFourFourteen
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source fiber_eq)
open private shore from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

theorem realize (reg : Nat → Prop) (total : (vertices (source G) reg).card=22)
    (fours : ∃ x z, reg (source G x x) ∧ reg (source G z z) ∧ (fiber G x).card=4 ∧ (fiber G z).card=4 ∧ source G x x≠source G z z)
    (fourteen : ∃ y, reg (source G y y) ∧ (fiber G y).card=14) : Realizes p reg := by
  obtain ⟨x,z,hx,hz,sx,sz,xz⟩ := fours
  obtain ⟨y,hy,sy⟩ := fourteen
  obtain ⟨A⟩ := shore x sx; obtain ⟨B⟩ := shore z sz; obtain ⟨Y⟩ := shore y sy
  let c := source G
  have ne (i : Fin n) (e : (fiber G i).card=4) : c i i≠c y y := by
    intro eq
    have same : fiber G i=fiber G y := by ext u; rw [fiber_eq,fiber_eq]; change (c u u=c i i ↔ c u u=c y y); rw [eq]
    have h := congrArg Finset.card same; omega
  have all := RegionalFourFourEight.three_cover hx hz hy xz (ne x sx) (ne z sz) (by rw [sx,sz,sy,total])
  let keep := fun t => t=c y y
  have old := LargeOrderBlocks.fourteen p keep (fun i h => by
    change source G i i=source G y y at h
    change 3 < (vertices (source G) (·=source G i i)).card; rw [h,RegionalTwoAnchor.card Y]; decide)
    (RegionalTwoAnchor.card Y)
  let base : Region c keep := ⟨y,(mem_vertices _ _ _).mpr rfl⟩
  have new' := TwoShoreAttachment.attach p x z rfl rfl ((RegionalTwoAnchor.pair_bound A B).trans (by decide))
    keep old base rfl (FourByEven.rectangle (sourceLaws _) A Y (Or.inr rfl))
    (FourByEven.rectangle (sourceLaws _) B Y (Or.inr rfl)) (fun _ _ _ _ _ h no => (no h).elim)
  apply RegionalFourFourEight.restrict_map p new'
  intro i h
  rcases all i h with h|h|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

end QGI.Coherent.RegionalFourFourFourteen
