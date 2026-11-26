import SixSixEightPins
import DoubleTetraExclusion

noncomputable section
namespace QGI.Coherent.RegionalSixSixEight
open SixTenCoordinates SixEightGeometry SmallUnion SmallFiberExtension LargeFourteenRegion StrategyColorLaws
open FourTwelveFunctional (source)
open SixEightCatalog (Six Eight)
open SixSixEightPins (Flat flat_twins flip_flat)
open private reverse twins shore from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (p : PerfectStrategy G H K)

theorem solve {l r z : Nat} (lr : l≠r) (lz : l≠z) (rz : r≠z)
    (A : Shore (source G) l Six) (B : Shore (source G) r Six) (Y : Shore (source G) z Eight)
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=z) : Realizes p reg := by
  classical
  let c := source G
  have base := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.pair_bound A B).trans (by decide))
  have swapped := RegionalFourFourEight.restrict_map p base (t:=fun t => t=r ∨ t=l) (fun _ h => Or.symm h)
  have bigPair {a} (F : Shore c a Six) (diff : a≠z) : Realizes p (fun t => t=a ∨ t=z) := by
    apply LargeOrderBlocks.fourteen p _ _ (RegionalFourSixEight.pair_card diff F Y)
    intro i h
    change 3 < (vertices (source G) (·=source G i i)).card
    rcases h with ha|hz
    · rw [ha,RegionalTwoAnchor.card F]; decide
    · rw [hz,RegionalTwoAnchor.card Y]; decide
  have ay := bigPair A lz
  have by' := bigPair B rz
  have cv (i) (h : reg (c i i)) : c i i=r ∨ c i i=l ∨ c i i=z := by rcases cover i h with h|h|h <;> tauto
  have yc (i) (h : reg (c i i)) : c i i=z ∨ c i i=l ∨ c i i=r := by rcases cover i h with h|h|h <;> tauto
  have cases {a} (F : Shore c a Six) (diff : a≠z) : SplitRectangle.Twins (rect F Y) ∨
      (∃ v w, v≠w ∧ Nonempty (RepeatedTetra.Repeated 2 F Y v w)) ∨ Cube F Y ∧ ¬Flat F Y := by
    rcases (classify diff F Y).2 with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases f : Flat F Y
      · exact Or.inl (flat_twins F Y f)
      · exact Or.inr (Or.inr ⟨h,f⟩)
  rcases cases A lz with atw|⟨v,w,vw,⟨P⟩⟩|⟨ac,am⟩
  · rcases cases B rz with btw|⟨v,w,vw,⟨Q⟩⟩|⟨bc,bm⟩
    · exact RegionalFourFourEight.centered p Y A B (by decide) base yc (reverse (twins A Y atw)) (reverse (twins B Y btw))
    · by_cases flat : Flat A B
      · exact RegionalFourFourEight.centered p A B Y (by decide) by' cover (twins A B (flat_twins A B flat)) (twins A Y atw)
      · exact SixSixEightPins.tetra p B A Y reg active cv by' vw Q flat
    · exact SixSixEightPins.cube p B A Y reg active cv swapped by' rz lz bc bm
  · by_cases flat : Flat B A
    · rcases cases B rz with btw|⟨h,k,hk,⟨Q⟩⟩|⟨bc,bm⟩
      · exact RegionalFourFourEight.centered p B A Y (by decide) ay cv (twins B A (flat_twins B A flat)) (twins B Y btw)
      · exact (DoubleTetraExclusion.exclude A B Y vw hk P Q (flip_flat B A flat)).elim
      · exact SixSixEightPins.cube p B A Y reg active cv swapped by' rz lz bc bm
    · exact SixSixEightPins.tetra p A B Y reg active cover ay vw P flat
  · exact SixSixEightPins.cube p A B Y reg active cover base ay lz rz ac am

theorem realize (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (total : (vertices (source G) reg).card=20)
    (eight : ∃ y, reg (source G y y) ∧ (fiber G y).card=8)
    (sixes : ∃ a b, reg (source G a a) ∧ reg (source G b b) ∧ (fiber G a).card=6 ∧ (fiber G b).card=6 ∧ source G a a≠source G b b) :
    Realizes p reg := by
  obtain ⟨y,hy,sy⟩ := eight
  obtain ⟨a,b,ha,hb,sa,sb,ab⟩ := sixes
  obtain ⟨A⟩ := shore a sa
  obtain ⟨B⟩ := shore b sb
  obtain ⟨Y⟩ := shore y sy
  have diff (x : Fin n) (sx : (fiber G x).card=6) : source G x x≠source G y y := by
    intro eq
    have same : fiber G x=fiber G y := by ext i; rw [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.fiber_eq,eq]
    rw [same,sy] at sx
    contradiction
  exact solve p ab (diff a sa) (diff b sb) A B Y reg active
    (RegionalFourFourEight.three_cover ha hb hy ab (diff a sa) (diff b sb) (by rw [sa,sb,sy,total]))

end QGI.Coherent.RegionalSixSixEight
