import LargeOrderBlocks
import ZivAvCoreQuantum

namespace QGI.Coherent.LargeOrderBlocks
open LargeFourteenRegion SmallFiberExtension SmallUnion
open FourTwelveFunctional (source)

/-- The exceptional catalog correspondence is tested inside the selected
fourteen vertices, also in the presence of other large fibers. -/
theorem fourteen {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (reg : Nat → Prop)
    (active : ∀ i, reg (source G i i) → large G (source G i i))
    (size : (vertices (source G) reg).card=14) : Realizes p reg :=
  of_solver p reg active size (ZivAv.solveRegion p)

end QGI.Coherent.LargeOrderBlocks
