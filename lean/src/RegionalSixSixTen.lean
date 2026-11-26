import SixSixTenInterfaces
import SixSixEightPins
import DeterminedShore

noncomputable section
namespace QGI.Coherent.RegionalSixSixTen
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws RegionalShorePins LargeFourteenRegion
open FourTwelveFunctional (source)
open SixSixTenInterfaces (S T)
open SixSixEightPins (Flat flat_twins)
open Intertwiner (U)
open private twins shore from RegionalFourFourEight

variable {n l r z : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

private theorem rigid (F : Shore (source G) z T) (A : Shore (source G) l S) (B : Shore (source G) r S)
    (chart : TenPointCrossLaws.Chart F 2)
    (uniq : ∀ i x, (∀ j, SixSixTenInterfaces.rect F A j i=SixSixTenInterfaces.rect F A j x) → i=x)
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=z) : Realizes p reg := by
  obtain ⟨ξ,f,nz,hf⟩ := TenPointPetersen.fixed p F chart
  obtain ⟨g,hg⟩ := RegionalMarkPins.grow p nz (atPoint F) f hf A (fun i b h => uniq b i (fun j => Relations.transpose _ (h j)))
  let s := Sum.elim (atPoint F) (atPoint A)
  let t := Sum.elim f g
  have fixed : ∀ j, U p (s j) (t j) ξ=ξ := by rintro (j|j); exact hf j; exact hg j
  have inclF (j : T) : ∃ k, s k=atPoint F j := ⟨.inl j,rfl⟩
  have inclA (j : S) : ∃ k, s k=atPoint A j := ⟨.inr j,rfl⟩
  have sa := RegionalMarkPins.widen A (pinned A) inclA
  have sf := RegionalMarkPins.widen F (pinned F) inclF
  have finish : Short B s → Realizes p reg := fun sb => RegionalShorePins.realize p A B F reg active cover ξ nz s t fixed sa sb sf
  have halfBound {k v} [NeZero k] (X : Shore (source G) v (Fin k)) (h : ¬Flat B X) : Short B (atPoint X) := by
    intro i
    apply (Finset.card_le_card ?_).trans (ShoreSignatureSize.half (sourceLaws _) B X h i)
    intro b hb; simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb ⊢; exact hb
  by_cases ba : Flat B A
  · by_cases bf : Flat B F
    · let keep := fun k => k=l ∨ k=z
      have largeKeep (i) (h : keep (source G i i)) : large G (source G i i) := by
        rcases h with h|h
        · rw [h,large,RegionalTwoAnchor.card A]; decide
        · rw [h,large,RegionalTwoAnchor.card F]; decide
      have old := RegionalShorePins.realize p A F F keep largeKeep (fun i h => h.imp_right Or.inl) ξ nz s t fixed sa sf sf
      let x : Region (source G) keep := ⟨atPoint F 0,(mem_vertices _ _ _).mpr (Or.inr (F 0).property)⟩
      have hx : source G x.val x.val=z := (F 0).property
      have rect : FiberPairExtension.twins (source G) r (source G x.val x.val) := hx ▸ twins B F (flat_twins B F bf)
      refine RegionalFourFourEight.restrict_map p (DeterminedShore.attach p (atPoint B 0) (B 0).property
        ((RegionalTwoAnchor.card B).le.trans (by decide)) keep old x rect ?_) ?_
      · intro i b _ j
        obtain ⟨u,hu⟩ := SixSixCycle.point B i.property
        obtain ⟨v,hv⟩ := SixSixCycle.point B b.property
        rcases (mem_vertices _ _ _).mp j.property with ha|hz
        · obtain ⟨w,hw⟩ := SixSixCycle.point A ha
          rw [←hu,←hv,←hw]; exact (ba u w).trans (ba v w).symm
        · obtain ⟨w,hw⟩ := SixSixCycle.point F hz
          rw [←hu,←hv,←hw]; exact (bf u w).trans (bf v w).symm
      · intro i hi; rcases cover i hi with h|h|h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
    · exact finish (RegionalMarkPins.widen B (halfBound F bf) inclF)
  · exact finish (RegionalMarkPins.widen B (halfBound A ba) inclA)

theorem solve (lr : l≠r) (_lz : l≠z) (_rz : r≠z)
    (A : Shore (source G) l S) (B : Shore (source G) r S) (Y : Shore (source G) z T)
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=z) : Realizes p reg := by
  obtain ⟨a,e,ca⟩ := TenPointCrossLaws.chart p Y
  let F := e.trans Y
  rcases SixSixTenInterfaces.shape F A a ca with sa|⟨rfl,ua⟩
  swap
  · exact rigid p F A B ca ua reg active cover
  rcases SixSixTenInterfaces.shape F B a ca with sb|⟨rfl,ub⟩
  swap
  · exact rigid p F B A ca ub reg active (fun i hi => by rcases cover i hi with h|h|h <;> tauto)
  let keep := fun t => t=l ∨ t=r
  have old := LargeOrderBlocks.small p keep ((RegionalFourSixEight.pair_card lr A B).le.trans (by decide))
  let x : Region (source G) keep := ⟨atPoint A 0,(mem_vertices _ _ _).mpr (Or.inl (A 0).property)⟩
  have size {v} (X : Shore (source G) v S) (i : Fin n) (h : source G i i=v) : (fiber G i).card=6 := by
    have eq : fiber G i=vertices (source G) (·=v) := by ext y; rw [FourTwelveFunctional.fiber_eq,mem_vertices,h]
    rw [eq]; exact RegionalTwoAnchor.card X
  refine RegionalFourFourEight.restrict_map p (OddShoreAttachment.extend_common p (q:=3) (Or.inr rfl) F keep old x ?_ ?_) ?_
  · intro i; rcases (mem_vertices _ _ _).mp i.property with h|h
    · exact size A _ h
    · exact size B _ h
  · intro i; rcases (mem_vertices _ _ _).mp i.property with h|h
    · rw [h]; exact twins F A sa
    · rw [h]; exact twins F B sb
  · intro i hi; rcases cover i hi with h|h|h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem realize (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (total : (vertices (source G) reg).card=22)
    (ten : ∃ y, reg (source G y y) ∧ (fiber G y).card=10)
    (sixes : ∃ a b, reg (source G a a) ∧ reg (source G b b) ∧ (fiber G a).card=6 ∧ (fiber G b).card=6 ∧ source G a a≠source G b b) :
    Realizes p reg := by
  obtain ⟨y,hy,sy⟩ := ten
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

end QGI.Coherent.RegionalSixSixTen
