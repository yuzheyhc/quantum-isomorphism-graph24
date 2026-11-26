import LargeOrderEightCycles
import RegionalCycleSupport

noncomputable section
namespace QGI.Coherent.LargeOrderEightBinary
open LargeOrderEightCycles SmallUnion SmallFiberExtension LargeFourteenRegion SixTenCoordinates
open FourTwelveFunctional (source)
open FourEightGeometry (L Eight)

/-- A doubled cycle fixes the four-point block on a nonzero vector.
Each further mixed four-point block has at most two candidates per row. -/
theorem realize {n l v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (F : Shore (source G) l L) (Y : Shore (source G) v Eight)
    (D : CycleData F Y) (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ x, reg (source G x x) → ∃ r : Nat, ∃ S : Shore (source G) r L,
      (source G x x=l ∨ source G x x=r ∨ source G x x=v) ∧
      ∃ i j, source G (atPoint F i) (atPoint S j)≠source G (atPoint F 0) (atPoint S 0)) :
    Realizes p reg := by
  apply LargeOrderBlocks.of_solver p reg active rfl
  intro f g data
  apply RegionalCycleSupport.solve_patterns p data F Y D.mark D.code D.cells D.cycle
  intro j
  obtain ⟨_,S,side,mixed⟩ := cover (f j) ((data.src _).mp ⟨j,rfl⟩)
  exact FourEightMixed.patterns_at F S Y (f j) (side.imp_right (Or.imp_right Or.inl)) mixed
    D.mark D.code D.cells D.cycle

end QGI.Coherent.LargeOrderEightBinary
