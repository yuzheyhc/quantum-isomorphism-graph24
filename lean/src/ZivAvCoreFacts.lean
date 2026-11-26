import ZivAvPositions

namespace QGI.ZivAv
open SixteenMapSearch QGI.DoubleEight.Prepared
attribute [local irreducible] raw keyed color cores14
open private histogram histogram_at coefficients get_ofFn from DoubleEightPrepared

private def pairIndex (a : Index) (x y z : Vertex) :=
  finProdFinEquiv (name a x z,name a z y)

private def localHist (a : Index) (k : Fin (raw a).rank) :=
  histogram (List.ofFn (pairIndex a (atName a k).1 (atName a k).2))

theorem tables : ∀ a : Index, ∀ k : Fin (raw a).rank,
    coefficients (raw a) k = localHist a k := by native_decide

end QGI.ZivAv
