import HomogeneousUnions

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem homogeneousUnionCoverage18 :
    QGI.Homogeneous.Unions.passed 18 4690 292 = true := by
  native_decide
