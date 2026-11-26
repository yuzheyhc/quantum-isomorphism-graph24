import HomogeneousUnions

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem homogeneousUnionCoverage16 :
    QGI.Homogeneous.Unions.passed 16 22710 218 = true := by
  native_decide
