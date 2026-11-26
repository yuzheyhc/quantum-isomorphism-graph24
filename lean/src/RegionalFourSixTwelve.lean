import FourSixTwelveRoot
import FourSixTwelveCases
import FourSixTwelveFlat

noncomputable section
namespace QGI.Coherent.RegionalFourSixTwelve
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)
open private card_core from LargeFourteenRegion
open private shore from RegionalFourFourEight
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)

theorem realize (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (total : (vertices (source G) reg).card=22)
    (four : ∃ a, reg (source G a a) ∧ (fiber G a).card=4)
    (six : ∃ a, reg (source G a a) ∧ (fiber G a).card=6)
    (twelve : ∃ a, reg (source G a a) ∧ (fiber G a).card=12) : Realizes p reg := by
  obtain ⟨a,ha,sa⟩ := four
  obtain ⟨b,hb,sb⟩ := six
  obtain ⟨y,hy,sy⟩ := twelve
  obtain ⟨F⟩ := shore a sa
  obtain ⟨S⟩ := shore b sb
  obtain ⟨Y⟩ := shore y sy
  have ne (i j : Fin n) (diff : (fiber G i).card≠(fiber G j).card) : source G i i≠source G j j := by
    intro h
    apply diff <| congrArg Finset.card (show fiber G i=fiber G j by ext z; rw [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.fiber_eq,h])
  have ab := ne a b (by rw [sa,sb]; decide)
  have ay := ne a y (by rw [sa,sy]; decide)
  have by' := ne b y (by rw [sb,sy]; decide)
  have cover := RegionalFourFourEight.three_cover ha hb hy ab ay by' (by rw [sa,sb,sy,total])
  exact FourSixTwelveCases.reduce p F S Y ab ay by' reg active cover
    (FourSixTwelveRoot.solve p F S Y reg active cover)
    (fun B _ flat => FourSixTwelveFlat.solve p F S Y ay B flat reg cover)

theorem isomorphic {xs : List Nat} (P : CoprimeProfiles.Profile G xs)
    (total : (xs.filter (fun k => 3<k)).sum=22) (four : 4∈xs) (six : 6∈xs) (twelve : 12∈xs)
    (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,ng,ip,cs,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := cs
  obtain ⟨a,ha⟩ := P.fiber_of_mem four (by decide)
  obtain ⟨b,hb⟩ := P.fiber_of_mem six (by decide)
  obtain ⟨y,hy⟩ := P.fiber_of_mem twelve (by decide)
  have region := realize p (large G) (fun _ h => h) ((card_core P).trans total)
    ⟨a,(LargeOrderBlocks.large_iff _).mpr (by rw [ha] <;> decide),ha⟩
    ⟨b,(LargeOrderBlocks.large_iff _).mpr (by rw [hb] <;> decide),hb⟩
    ⟨y,(LargeOrderBlocks.large_iff _).mpr (by rw [hy] <;> decide),hy⟩
  obtain ⟨e,he⟩ := SmallFiberExtension.of_large_region p region
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩⟩
end QGI.Coherent.RegionalFourSixTwelve
