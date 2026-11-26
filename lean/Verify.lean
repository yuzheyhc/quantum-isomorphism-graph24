import Minimum24

example : QGI.NoSeparation 16 := QGI.noSeparation16
#print axioms QGI.noSeparation16

example : QGI.NoSeparation 17 := QGI.noSeparation17
#print axioms QGI.noSeparation17

example : QGI.NoSeparation 18 := QGI.noSeparation18
#print axioms QGI.noSeparation18

example : QGI.NoSeparation 19 := QGI.noSeparation19
#print axioms QGI.noSeparation19

example : QGI.NoSeparation 20 := QGI.noSeparation20
#print axioms QGI.noSeparation20

example : QGI.NoSeparation 21 := QGI.noSeparation21
#print axioms QGI.noSeparation21

example : QGI.NoSeparation 22 := QGI.noSeparation22
#print axioms QGI.noSeparation22

example : QGI.NoSeparation 23 := QGI.noSeparation23
#print axioms QGI.noSeparation23

example : QGI.Through 23 := QGI.through23
#print axioms QGI.through23

example : QGI.Separation 24 := Upper24Hilbert.existsSeparation24
#print axioms Upper24Hilbert.existsSeparation24

example : QGI.Separation 24 ∧
    ∀ n < 24, ¬ ∃ G H : QGI.Graph n, QGI.QuantumIso G H ∧ ¬ QGI.Isomorphic G H :=
  QGI.exactMinimum24
#print axioms QGI.exactMinimum24

open QGI.Certificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checkWitness476 : check m_double_307 m_double_307 .tetra [0,1,4,3,2,5,6,8,9,7,10,11,12,13] [2,10,10,10,10,7] 32 0 = true := by decide
#print axioms checkWitness476
