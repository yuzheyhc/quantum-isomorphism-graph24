import Lean
import Single16Maps

/- A closed finite census claim for these 208 input matrices. Native reduction
also trusts Lean's compiled evaluator. It gives no theorem that these matrices
exhaust all coherent configurations, nor that a qc map preserves planar counts.
The proof below has not been compiled in the authoring environment. -/
namespace QGI.Single16
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem catalogueCheck : checked = true := by native_decide
end QGI.Single16
