import CatalogComparison
import ZivAvPositions
import FifteenCatalog

namespace QGI.CatalogComparison
open private get_ofFn from DoubleEightPrepared

def fourteen (a : ZivAv.Index) : Frame 14 (ZivAv.raw a).rank :=
  ⟨ZivAv.name a,ZivAv.atName a⟩
def fifteen (a : Fifteen.Index) : Frame 15 (Fifteen.rank a) :=
  let M := Fifteen.model a
  ⟨M.name,M.spot⟩

private def ids14 := ids fourteen
private def ids15 := ids fifteen
set_option maxRecDepth 10000 in
private theorem distinct14 : Function.Injective ids14.get := by
  unfold Function.Injective
  native_decide
set_option maxRecDepth 10000 in
private theorem distinct15 : Function.Injective ids15.get := by
  unfold Function.Injective
  native_decide

theorem fourteen_row {a b : ZivAv.Index} {e} (h : Respects (fourteen a) (fourteen b) e) : a=b :=
  distinct14 (ids_eq fourteen h)
theorem fifteen_row {a b : Fifteen.Index} {e} (h : Respects (fifteen a) (fifteen b) e) : a=b :=
  distinct15 (ids_eq fifteen h)

end QGI.CatalogComparison

