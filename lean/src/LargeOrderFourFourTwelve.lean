import LargeOrderTwelveCommon
import TwoShoreAttachment

noncomputable section
namespace QGI.Coherent.LargeOrderFourFourTwelve
open SixTenCoordinates LargeOrderSquareInterface LargeOrderFourFourTwelveGeometry LargeOrderTwelveTargets
open SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source fiber_eq)
open private shore reverse from RegionalFourFourEight

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

private theorem both_twin (F : Shore c₀ l I) (S : Shore c₀ r I) (Y : Shore c₀ v Twelve)
    (fa : FiberPairExtension.twins c₀ l v) (sa : FiberPairExtension.twins c₀ r v) (reg : Nat → Prop)
    (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v) : Realizes p reg := by
  let keep := fun t => t=v
  let y : Region c₀ keep := ⟨atPoint Y 0,(mem_vertices _ _ _).mpr (Y 0).property⟩
  have old := LargeOrderBlocks.small p keep ((RegionalTwoAnchor.card Y).le.trans (by decide))
  apply RegionalFourFourEight.restrict_map p (TwoShoreAttachment.attach p (atPoint F 0) (atPoint S 0)
    (F 0).property (S 0).property ((RegionalTwoAnchor.pair_bound F S).trans (by decide))
    keep old y (Y 0).property fa sa (fun _ _ _ _ _ h no => (no h).elim))
  intro z hz; rcases cover z hz with h|h|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem frames (F : Shore c₀ l I) (S : Shore c₀ r I) (Y : Shore c₀ v Twelve)
    (lr : l≠r) (lv : l≠v) (rv : r≠v) (reg : Nat → Prop)
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i))
    (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v) : Realizes p reg := by
  classical
  by_contra bad
  have swapped (z) (hz : reg (c₀ z z)) : c₀ z z=r ∨ c₀ z z=l ∨ c₀ z z=v := by
    rcases cover z hz with h|h|h; exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h)
  have thin {a b : Nat} (T : Shore c₀ a I) (av : a≠v)
      (regions : ∀ z, reg (c₀ z z) → c₀ z z=b ∨ c₀ z z=a ∨ c₀ z z=v) : ¬MapsOne c₀ v b := by
    rintro ⟨x,y,dx,dy,one⟩
    apply bad (RegionalFourFourEight.functional p (LargeOrderTwelveCycle.pair p T Y av) _ x y (Or.inr dx) dy one)
    exact fun z hz => (regions z hz).elim Or.inr Or.inl
  have first := (classify F Y lv).resolve_left (thin S rv cover)
  have second := (classify S Y rv).resolve_left (thin F lv swapped)
  by_cases uniform : ∀ i j, c₀ (atPoint F i) (atPoint S j)=c₀ (atPoint F 0) (atPoint S 0)
  · have back (j i) := Relations.transpose (closure G) (uniform i j)
    rcases first with tw|⟨B,cy|twoB⟩
    · exact bad (LargeOrderTwelveCycle.twinAttach p F S Y rv tw uniform reg cover)
    · exact bad (LargeOrderTwelveCycle.cycleAttach p F S Y B (Classical.choice cy) lr lv rv uniform reg cover)
    rcases second with tw|⟨C,cy|twoC⟩
    · exact bad (LargeOrderTwelveCycle.twinAttach p S F Y lv tw back reg swapped)
    · exact bad (LargeOrderTwelveCycle.cycleAttach p S F Y C (Classical.choice cy) (Ne.symm lr) rv lv back reg swapped)
    obtain ⟨A⟩ := LargeOrderTwelvePairs.matching B.col twoB
    obtain ⟨D⟩ := LargeOrderTwelvePairs.matching C.col twoC
    by_cases disjoint : ∀ j, A.mate j≠D.mate j
    · exact bad (LargeOrderTwelvePairs.separate p B C twoB twoC A D disjoint uniform reg cover)
    push_neg at disjoint
    obtain ⟨j,hj⟩ := disjoint
    have sameB := (A.unique j _).mpr rfl
    have sameC := (D.unique j _).mpr hj
    exact bad (LargeOrderTwelveCommon.realize p F S Y lv rv B C twoB j (A.mate j)
      (Ne.symm sameB.1) sameB.2.symm sameC.2.symm reg active cover)
  · push_neg at uniform
    rcases first with tw|⟨B,h⟩
    · rcases second with sw|⟨C,h⟩
      · exact bad (both_twin p F S Y tw sw reg cover)
      · obtain ⟨i,j,ne⟩ := uniform
        exact bad (LargeOrderTwelveVector.mixed p S F Y rv C h ⟨j,i,fun eq => ne (Relations.transpose _ eq)⟩ reg active swapped)
    · exact bad (LargeOrderTwelveVector.mixed p F S Y lv B h uniform reg active cover)

theorem realize (reg : Nat → Prop) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i))
    (total : (vertices c₀ reg).card=20)
    (fours : ∃ x z, reg (c₀ x x) ∧ reg (c₀ z z) ∧ (fiber G x).card=4 ∧ (fiber G z).card=4 ∧ c₀ x x≠c₀ z z)
    (twelve : ∃ y, reg (c₀ y y) ∧ (fiber G y).card=12) : Realizes p reg := by
  obtain ⟨x,z,hx,hz,sx,sz,xz⟩ := fours
  obtain ⟨y,hy,sy⟩ := twelve
  obtain ⟨F⟩ := shore x sx; obtain ⟨S⟩ := shore z sz; obtain ⟨Y⟩ := shore y sy
  have ne (i : Fin n) (size : (fiber G i).card=4) : c₀ i i≠c₀ y y := by
    intro eq
    have e : fiber G i=fiber G y := by ext u; rw [fiber_eq,fiber_eq,eq]
    have h := congrArg Finset.card e; omega
  exact frames p F S Y xz (ne x sx) (ne z sz) reg active
    (RegionalFourFourEight.three_cover hx hz hy xz (ne x sx) (ne z sz) (by rw [sx,sz,sy,total]))

end QGI.Coherent.LargeOrderFourFourTwelve
