import NineNineEnum
import data.NineNineShort

namespace QGI.NineNine.Sieve

/-- The computed double-lexicographic candidates of degrees two, three and
four whose two Gram histograms are uniform, in the search's exact order. -/
theorem enumerate : shortlist 2 ++ shortlist 3 ++ shortlist 4 = Short.entries.toList.map Prod.fst := by
  native_decide

end QGI.NineNine.Sieve
