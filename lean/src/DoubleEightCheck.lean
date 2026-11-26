import Lean
import DoubleEightMaps

namespace QGI.DoubleEight
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem catalogueCheck : checked = true := by native_decide
end QGI.DoubleEight
