import LargeOrderFourFourSixEightFlat
import LargeOrderFourFourSixEightTetra

noncomputable section
namespace QGI.Coherent.LargeOrderFourFourSixEight
open SmallUnion SmallFiberExtension StrategyColorLaws SixTenCoordinates SixEightGeometry LargeOrderFourFourSixEightFrame
open SixSixEightPins (Flat)
open FourTwelveFunctional (source)
open private shore from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (p : PerfectStrategy G H K)
local notation "c₀" => source G

private theorem mixed (Q : Quad G) (h : ¬Flat Q.A Q.S) : Realizes p Q.whole := by
  rcases FourSixSix.Interfaces.classify (sourceLaws _) Q.A Q.S with ⟨t,u⟩|weak|⟨t,perm,shape⟩
  · exact (h (fun i j => (u i j).trans (u 0 0).symm)).elim
  · exact removeS p Q (m:=2) (Or.inl rfl) Q.A (Or.inl rfl) weak h
  · exact LargeOrderFourFourSixEightTetra.solve p Q t perm shape

theorem solve (Q : Quad G) : Realizes p Q.whole := by
  by_cases as' : Flat Q.A Q.S
  · by_cases bs : Flat Q.B Q.S
    · exact LargeOrderFourFourSixEightFlat.solve p Q as' bs
    · exact swapped p Q (mixed p Q.swap bs)
  · exact mixed p Q as'

theorem realize (reg : Nat → Prop) (total : (vertices c₀ reg).card=22)
    (fours : ∃ x z, reg (c₀ x x) ∧ reg (c₀ z z) ∧ (fiber G x).card=4 ∧ (fiber G z).card=4 ∧ c₀ x x≠c₀ z z)
    (six : ∃ x, reg (c₀ x x) ∧ (fiber G x).card=6) (eight : ∃ x, reg (c₀ x x) ∧ (fiber G x).card=8) :
    Realizes p reg := by
  obtain ⟨a,b,ha,hb,sa,sb,ab⟩ := fours
  obtain ⟨s,hs,ss⟩ := six; obtain ⟨y,hy,sy⟩ := eight
  obtain ⟨A⟩ := shore a sa; obtain ⟨B⟩ := shore b sb; obtain ⟨S⟩ := shore s ss; obtain ⟨Y⟩ := shore y sy
  let Q : Quad G := ⟨c₀ a a,c₀ b b,c₀ s s,c₀ y y,A,B,S,Y,ab⟩
  have sub : vertices c₀ Q.whole ⊆ vertices c₀ reg := by
    intro i hi; apply (mem_vertices _ _ _).mpr
    rcases (mem_vertices _ _ _).mp hi with h|h|h|h
    · exact (congrArg reg h).mpr ha
    · exact (congrArg reg h).mpr hb
    · exact (congrArg reg h).mpr hs
    · exact (congrArg reg h).mpr hy
  have same := Finset.eq_of_subset_of_card_le sub (total.trans (card Q).symm).le
  apply RegionalFourFourEight.restrict_map p (solve p Q)
  intro i hi
  apply (mem_vertices _ _ _).mp
  rw [same]; exact (mem_vertices _ _ _).mpr hi

end QGI.Coherent.LargeOrderFourFourSixEight
