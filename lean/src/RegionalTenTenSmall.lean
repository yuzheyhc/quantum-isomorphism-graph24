import TenPointCrossFour
import TenPointPetersen

noncomputable section
namespace QGI.Coherent.RegionalTenTenSmall
open TenPointCross TenPointCrossLaws
open SixTenCoordinates (Shore atPoint sourceLaws)
open SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

omit [CompleteSpace K] in
private theorem singleton (X : Shore (source G) l V) (Y : Shore (source G) r V) (i j : V)
    (single : (row X Y (entry X Y i j) i).card=1) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) : Realizes p reg := by
  have old := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.card X).le.trans (by decide))
  apply RegionalFourFourEight.functional p old cover (atPoint X i) (atPoint Y j) (X i).property (Y j).property
  intro t eq
  obtain ⟨k,rfl⟩ := SixSixCycle.point Y ((Relations.end_colors (closure G) eq).2.trans (Y j).property)
  exact congrArg (atPoint Y) (Finset.card_le_one.mp single.le k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩)
    j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩))

/-- A non-realizable ten-by-ten region must have a cross color of valency two. -/
theorem reduction (X : Shore (source G) l V) (Z : Shore (source G) r V) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) :
    Realizes p reg ∨ ∃ i j : V, (row X Z (entry X Z i j) i).card=2 := by
  classical
  obtain ⟨a,e,ca⟩ := chart p X
  obtain ⟨b,g,cb⟩ := chart p Z
  let F := e.trans X
  let Y := g.trans Z
  let c := source G
  let dg (i j : V) := (row F Y (entry F Y i j) i).card
  rcases RegionalTenTen.reduction p F Y reg cover with solved|⟨j,hj⟩
  · exact Or.inl solved
  change dg 0 j=2 ∨ dg 0 j=3 ∨ dg 0 j=4 at hj
  obtain ⟨y,_,min⟩ := Finset.exists_min_image (Finset.univ : Finset V) (dg 0) Finset.univ_nonempty
  let v := entry F Y 0 y
  let d := dg 0 y
  have rows (u i k) : (row F Y u i).card=(row F Y u k).card :=
    (col_size F Y (sourceLaws _) u i 0).symm.trans (col_size F Y (sourceLaws _) u k 0)
  have smallest (i j) : d≤dg i j := by
    let v' := entry F Y i j
    have pos : 0<(row F Y v' i).card := Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (pos.trans_eq (rows v' i 0))
    have eq : entry F Y 0 z=v' := (Finset.mem_filter.mp hz).2
    have lower := min z (Finset.mem_univ _)
    change d≤(row F Y (entry F Y 0 z) 0).card at lower
    exact lower.trans_eq (by rw [eq,rows v' 0 i])
  have cap := min j (Finset.mem_univ _)
  have pos : 0<d := Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have choice : d=1 ∨ d=2 ∨ d=3 ∨ d=4 := by change d≤dg 0 j at cap; omega
  rcases choice with one|two|higher
  · exact Or.inl (singleton p F Y 0 y one reg cover)
  · right
    refine ⟨e 0,g y,?_⟩
    exact (SixEightGeometry.count_equiv g (fun j => entry F Y 0 j=v) (fun j => entry X Z (e 0) j=entry X Z (e 0) (g y))
      (fun _ => Iff.rfl)).symm.trans two
  obtain ⟨d4,who⟩ := four_shore (sourceLaws _) F Y ca cb 0 y d higher rfl smallest
  left
  rcases who with h|h
  · subst a
    exact TenPointPetersen.realize p F Y ca v (fun i => (rows v i 0).trans d4) reg cover
  · subst b
    let w := entry Y F y 0
    have four (j) : (row Y F w j).card=4 := by
      rw [show row Y F w j=col F Y v j from row_transpose (sourceLaws _) Y F j y 0]
      exact (col_size F Y (sourceLaws _) v 0 j).trans d4
    exact TenPointPetersen.realize p Y F cb w four reg (fun i h => (cover i h).symm)

end QGI.Coherent.RegionalTenTenSmall
