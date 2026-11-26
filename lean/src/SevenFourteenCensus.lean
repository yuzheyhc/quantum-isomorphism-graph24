import SevenFourteenEnum
import data.SevenFourteenShort

namespace QGI.SevenFourteen.Enum
/-- The complete set of normalized degree-two and degree-three incidence
rectangles surviving the two Gram histogram tests. -/
theorem enumerate : shortlist 2 ++ shortlist 3 = Short.entries.toList.map Prod.fst := by
  native_decide
end QGI.SevenFourteen.Enum
