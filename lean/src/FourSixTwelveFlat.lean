import FourSixTwelveParity
import ThreeShoreCoordinates

noncomputable section
namespace QGI.Coherent.FourSixTwelveFlat
open SixTenCoordinates FourTwelveCycle FourTwelveTypes LargeOrderSquareInterface LargeOrderFourFourTwelveGeometry
open SmallUnion SmallFiberExtension StrategyColorLaws RegionalSixTwelveStats
open FourTwelveFunctional (source)
open private narrow from TwoAnchorUnionGlue
open private range from RegionalSixTwelveDispatch
open private twins reverse from RegionalFourFourEight
variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)
local notation "c" => source G
local notation "d" => targetName p

theorem solve (F : Shore c l I) (S : Shore c r (Fin 6)) (Y : Shore c v Twelve)
    (lv : l≠v) (B : Layout F Y) (flat : SixSixEightPins.Flat F S)
    (reg : Nat → Prop) (cover : ∀ z, reg (c z z) → c z z=l ∨ c z z=r ∨ c z z=v) : Realizes p reg := by
  classical
  let keep := fun z => z=l ∨ z=v
  have old : Realizes p keep := LargeOrderTwelveCycle.pair p F Y lv
  rcases SixTwelveAlternatives.classify p S Y with ⟨j,i,one⟩|relative|tw|⟨a,b,shape⟩
  · apply RegionalFourFourEight.functional p old (fun x h => by rcases cover x h with h|h|h <;> tauto)
      (atPoint Y j) (atPoint S i) (Or.inr (Y j).property) (S i).property
    intro z eq
    obtain ⟨x,rfl⟩ := (range S z).mpr ((Relations.end_colors (closure G) eq).2.trans (S i).property)
    have mem (u : Fin 6) (hit : color S Y j u=color S Y j i) : u∈family S Y (color S Y j i) j :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
    exact congrArg (atPoint S) ((Finset.card_le_one.mp one.le) x (mem _ eq) i (mem _ rfl))
  · obtain ⟨e,oldNames⟩ := old
    let A := F.trans (narrow e oldNames (show keep l from Or.inl rfl))
    let Z := Y.trans (narrow e oldNames (show keep v from Or.inr rfl))
    let f (i : I) : Region c keep := ⟨atPoint F i,(mem_vertices _ _ _).mpr (Or.inl (F i).property)⟩
    let y (i : Twelve) : Region c keep := ⟨atPoint Y i,(mem_vertices _ _ _).mpr (Or.inr (Y i).property)⟩
    have yy (i j) : c (atPoint Y i) (atPoint Y j)=d (atPoint Z i) (atPoint Z j) := oldNames (y i) (y j)
    obtain ⟨m,diag⟩ := diagonal_names p
    let T := S.trans (Equiv.subtypeEquiv m (q:=fun z => d z z=r) (fun i => ⟨fun h => (diag i).symm.trans h,fun h => (diag i).trans h⟩))
    obtain ⟨g,inside,cross⟩ := relative T Z yy
    exact ThreeShoreCoordinates.join p F S Y reg cover (atPoint A) (fun i => atPoint T (g i)) (atPoint Z)
      (fun i j => oldNames (f i) (f j)) inside yy
      (fun i j => ThreeShoreCoordinates.flat p F S flat _ _ (A i).property (T (g j)).property i j)
      (fun i j => oldNames (f i) (y j)) (fun i j => common_transpose p (cross j i))
  · have fs : FiberPairExtension.twins c l r := twins F S
      ⟨fun i x _ _ j => (flat i j).trans (flat x j).symm,fun _ j z _ i => (flat i j).trans (flat i z).symm⟩
    apply RegionalFourFourEight.centered p S F Y (by decide) old _ (reverse fs) (reverse (twins Y S tw))
    intro i h; rcases cover i h with h|h|h <;> tauto
  · obtain ⟨P⟩ := RegionalTetraLayout.make (sourceLaws _) S Y shape.palette shape.weight shape.four shape.intersection shape.tripled
    exact (FourSixTwelveParity.exclude F S Y B P shape.vw flat).elim
end QGI.Coherent.FourSixTwelveFlat
