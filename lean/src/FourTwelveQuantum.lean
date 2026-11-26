import FourTwelveDispatch
import DoubledEdges

namespace QGI.Coherent.FourTwelveQuantum

/-- A sixteen-point graph with coherent fibers of sizes four and twelve
is determined up to ordinary isomorphism by its commuting quantum
isomorphism class. -/
theorem isomorphic_of_four_and_twelve {G H : Graph 16} (four : ∃ x, (fiber G x).card = 4)
    (twelve : ∃ x, (fiber G x).card = 12) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,g,ip,complete,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := complete
  apply FourTwelveDispatch.reduce_to_doubled p four twelve ⟨K,g,ip,complete,⟨p⟩⟩
  intro S T hl hr v _ t
  exact DoubledEdges.isomorphic p S T hl.symm hr.symm v t.column t.cells t.twice

end QGI.Coherent.FourTwelveQuantum
