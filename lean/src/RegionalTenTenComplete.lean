import TenMatchedFlat

noncomputable section
namespace QGI.Coherent.RegionalTenTenComplete
open TenPointCross TenPointCrossLaws TenPointMatched
open SixTenCoordinates (Shore atPoint sourceLaws)
open SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private shore from RegionalFourFourEight

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

theorem solve (lr : l≠r) (X : Shore (source G) l V) (W : Shore (source G) r V) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) : Realizes p reg := by
  obtain ⟨a,e,ca⟩ := chart p X
  obtain ⟨b,f,cb⟩ := chart p W
  let F := e.trans X
  let Y := f.trans W
  rcases RegionalTenTenPairs.reduction p F Y reg cover with yes|⟨v,⟨S⟩⟩
  · exact yes
  rcases local_cases S (sourceLaws _) ca with rich|⟨af,pairA⟩
  · exact detected p F Y lr S rich reg cover
  obtain ⟨u,D,sl,sr,_⟩ := reverse S (sourceLaws _)
  rcases local_cases D (sourceLaws _) cb with rich|⟨bf,pairB⟩
  · exact detected p Y F (Ne.symm lr) D rich reg (fun i h => (cover i h).symm)
  rw [sl] at pairB
  obtain ⟨A⟩ := frames p F Y S ca cb af bf pairA pairB
  exact flat_solve p A reg cover

theorem of_size (reg : Nat → Prop) (total : (vertices (source G) reg).card=20)
    (pair : ∃ x y, reg (source G x x) ∧ reg (source G y y) ∧ (fiber G x).card=10 ∧ (fiber G y).card=10 ∧ source G x x≠source G y y) :
    Realizes p reg := by
  obtain ⟨x,y,hx,hy,sx,sy,ne⟩ := pair
  obtain ⟨A⟩ := shore x sx
  obtain ⟨Y⟩ := shore y sy
  let keep := fun t => t=source G x x ∨ t=source G y y
  have eq : vertices (source G) keep=vertices (source G) reg := by
    apply Finset.eq_of_subset_of_card_le _ (total.trans (RegionalFourSixEight.pair_card ne A Y).symm).le
    intro i hi
    exact (mem_vertices _ _ _).mpr (((mem_vertices (source G) keep i).mp hi).elim
      (fun h => (congrArg reg h).mpr hx) (fun h => (congrArg reg h).mpr hy))
  apply solve p ne A Y reg
  intro i hi
  exact (mem_vertices (source G) keep i).mp (eq.symm ▸ (mem_vertices _ _ _).mpr hi)

end QGI.Coherent.RegionalTenTenComplete
