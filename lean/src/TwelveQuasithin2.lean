import TwelveQuasithinRows
import data.RowCensus12Units2

namespace QGI.TwelveQuasithin
open RowCensus

private def nodes2 := decode raw12Units2

set_option maxRecDepth 100000 in
private theorem checked2 : (List.range nodes2.size).all
    (fun i => verifiedBy TwelveRowCensus.cells (options 2) nodes2 i)=true := by native_decide

theorem units2 (m : Matrix 12) (h : Laws m) (root : word m 0∈blockRoots 12)
    (fit : profile 2 (word m 0)=true) : ∃ a, RowCensus.Iso (TwelveRowCensus.cells a) m :=
  fromChecks nodes2 (by native_decide) (by native_decide)
    (fun i => List.all_eq_true.mp checked2 _ (List.mem_range.mpr i.isLt)) m h root fit

end QGI.TwelveQuasithin
