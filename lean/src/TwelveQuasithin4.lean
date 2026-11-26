import TwelveQuasithinRows
import data.RowCensus12Units4

namespace QGI.TwelveQuasithin
open RowCensus

private def nodes4 := decode raw12Units4

set_option maxRecDepth 100000 in
private theorem checked4 : (List.range nodes4.size).all
    (fun i => verifiedBy TwelveRowCensus.cells (options 4) nodes4 i)=true := by native_decide

theorem units4 (m : Matrix 12) (h : Laws m) (root : word m 0∈blockRoots 12)
    (fit : profile 4 (word m 0)=true) : ∃ a, RowCensus.Iso (TwelveRowCensus.cells a) m :=
  fromChecks nodes4 (by native_decide) (by native_decide)
    (fun i => List.all_eq_true.mp checked4 _ (List.mem_range.mpr i.isLt)) m h root fit

end QGI.TwelveQuasithin
