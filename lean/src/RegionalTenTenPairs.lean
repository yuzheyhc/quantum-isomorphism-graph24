import TenPointMatched
import TenPointEdgeRealize

noncomputable section
namespace QGI.Coherent.RegionalTenTenPairs
open TenPointCross TenPointCrossLaws TenPointMatched
open SixTenCoordinates (Shore atPoint sourceLaws)
open SmallUnion SmallFiberExtension
open FourTwelveFunctional (source)
open private singleton from RegionalTenTenSmall

/-- All remaining ten-by-ten strategies have a single named color which links
five pairs on the left to five pairs on the right by complete two-by-two rectangles. -/
theorem reduction {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (X : Shore (source G) l V) (Y : Shore (source G) r V)
    (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) :
    Realizes p reg ∨ ∃ v, Nonempty (Pairs X Y v) := by
  classical
  by_cases solved : Realizes p reg
  · exact Or.inl solved
  obtain ⟨a,e,chart⟩ := chart p X
  let F := e.trans X
  obtain ⟨i,j,d⟩ := (RegionalTenTenSmall.reduction p F Y reg cover).resolve_left solved
  let v := entry F Y i j
  have sz (k) : (row F Y v k).card=2 := (col_size F Y (sourceLaws _) v k 0).symm.trans ((col_size F Y (sourceLaws _) v i 0).trans d)
  have mn (k t) : 2≤(col F Y (entry F Y k t) t).card := by
    rw [col_size F Y (sourceLaws _) _ k t]
    let u := entry F Y k t
    have pos : 0<(row F Y u k).card := Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
    have ne : (row F Y u k).card≠1 := fun h => solved (singleton p F Y k t h reg cover)
    change 2≤(row F Y u k).card; omega
  by_cases inj : Function.Injective (col F Y v)
  · exact Or.inl (TenPointEdgeRealize.simple p F Y chart v sz mn inj reg cover)
  obtain ⟨S⟩ := of_repeat (sourceLaws _) F Y v sz inj
  refine Or.inr ⟨v,⟨⟨S.left ∘ e.symm,S.right,?_,S.right_two,?_⟩⟩⟩
  · intro q
    exact (SixEightGeometry.count_equiv e.symm (fun i => (S.left ∘ e.symm) i=q) (fun i => S.left i=q) (fun _ => Iff.rfl)).trans (S.left_two q)
  · intro k t
    simpa only [F,entry,Function.comp_apply,atPoint,Equiv.trans_apply,Equiv.apply_symm_apply] using S.member_iff (e.symm k) t

end QGI.Coherent.RegionalTenTenPairs
