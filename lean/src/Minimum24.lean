import Orders.Through23
import WholeClaim

/-- The minimum order of a quantum-isomorphic, classically nonisomorphic pair of graphs. -/
theorem QGI.exactMinimum24 : QGI.ExactMinimum 24 :=
  QGI.minimum24_from_lower23 QGI.noSeparation23
