import SixNineAttachments
import SixNineCuts
import LargeOrderFourteen

noncomputable section
namespace QGI.Coherent.RegionalSixEightNine
open Relations SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source fiber_eq)
open private twins reverse shore from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

theorem solve {l r v : Nat} (lr : l≠r) (rv : r≠v) (F : Shore (source G) l (Fin 8))
    (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) v (Fin 9)) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v) : Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  have sz {t k : Nat} (A : Shore c t (Fin k)) (i : Fin n) (h : c i i=t) : (fiber G i).card=k := by
    have eq : fiber G i=vertices c (·=t) := by ext z; rw [fiber_eq,mem_vertices]; change c z z=c i i ↔ c z z=t; rw [h]
    rw [eq]; exact RegionalTwoAnchor.card A
  have uniform (i j : Fin n) (hi : c i i=l) (hj : c j j=v) : c i j=c (atPoint F 0) (atPoint Y 0) :=
    CoprimeFibers.monochromatic G _ _ (by rw [sz F _ (F 0).property,sz Y _ (Y 0).property]; decide)
      ((fiber_eq _ _).mpr (hi.trans (F 0).property.symm)) ((fiber_eq _ _).mpr (hj.trans (Y 0).property.symm))
  have fy := fun i j => uniform (atPoint F i) (atPoint Y j) (F i).property (Y j).property
  have ft : FiberPairExtension.twins c l v := twins F Y
    ⟨fun i x _ _ j => (fy i j).trans (fy x j).symm,fun _ j z _ i => (fy i j).trans (fy i z).symm⟩
  let keep := fun s => s=l ∨ s=r
  have old := LargeOrderBlocks.fourteen p keep (fun i h => by
    rcases h with h|h
    · change 3 < (vertices (source G) (·=source G i i)).card; rw [h,RegionalTwoAnchor.card F]; decide
    · change 3 < (vertices (source G) (·=source G i i)).card; rw [h,RegionalTwoAnchor.card S]; decide)
    (RegionalFourSixEight.pair_card lr F S)
  have small69 := LargeOrderBlocks.of_solver p (fun z => z=r ∨ z=v) (fun i h => by
    rcases h with h|h
    · change 3 < (vertices (source G) (fun w => w=source G i i)).card; rw [h,RegionalTwoAnchor.card S]; decide
    · change 3 < (vertices (source G) (fun w => w=source G i i)).card; rw [h,RegionalTwoAnchor.card Y]; decide)
    (RegionalFourSixEight.pair_card rv S Y) (Fifteen.solve p _)
  have good (fs : FiberPairExtension.twins c l r) : Realizes p reg :=
    RegionalFourFourEight.centered p F S Y (by decide) small69 cover fs ft
  by_cases dup : ∃ i j, i≠j ∧ ∀ t, c (atPoint S i) (atPoint Y t)=c (atPoint S j) (atPoint Y t)
  · rcases SixNineTriples.classify rv S Y dup with uni|⟨v₀,A,B,oa,ob,rect,wt⟩
    · have sy : FiberPairExtension.twins c r v := twins S Y
        ⟨fun i x _ _ j => (uni i j).trans (uni x j).symm,fun _ j z _ i => (uni i j).trans (uni i z).symm⟩
      apply RegionalFourFourEight.centered p Y F S (by decide) old _ (reverse ft) (reverse sy)
      intro i h; rcases cover i h with h|h|h <;> tauto
    · exact SixNineAttachments.attach p F S Y reg cover uniform old v₀ A B oa ob rect wt
  obtain ⟨side,sur,coh⟩ := SixNineCuts.cut rv S Y dup
  exact good (reverse (twins S F (SixNineCuts.even_rectangle (k:=4) S F side sur coh (fun x y hx h => by omega))))

theorem realize (reg : Nat → Prop) (total : (vertices (source G) reg).card=23)
    (eight : ∃ a, reg (source G a a) ∧ (fiber G a).card=8)
    (six : ∃ a, reg (source G a a) ∧ (fiber G a).card=6)
    (nine : ∃ a, reg (source G a a) ∧ (fiber G a).card=9) : Realizes p reg := by
  obtain ⟨a,ha,sa⟩ := eight; obtain ⟨b,hb,sb⟩ := six; obtain ⟨y,hy,sy⟩ := nine
  obtain ⟨F⟩ := shore a sa; obtain ⟨S⟩ := shore b sb; obtain ⟨Y⟩ := shore y sy
  have ne (i j : Fin n) (diff : (fiber G i).card≠(fiber G j).card) : source G i i≠source G j j := by
    intro h; apply diff <| congrArg Finset.card (show fiber G i=fiber G j by ext z; rw [fiber_eq,fiber_eq,h])
  have ab := ne a b (by rw [sa,sb]; decide)
  have ay := ne a y (by rw [sa,sy]; decide)
  have by' := ne b y (by rw [sb,sy]; decide)
  exact solve p ab by' F S Y reg (RegionalFourFourEight.three_cover ha hb hy ab ay by' (by rw [sa,sb,sy,total]))

end QGI.Coherent.RegionalSixEightNine
