import OrderTargets

namespace QGI

/-- External result for ordinary finite simple graphs. Simon Schmidt, *Quantum
automorphism groups of finite graphs* (2020), §8.5, pp. 134–135, paragraph
following Question 8.5.1, states the strict lower bound. Lupini, Mančinska and
Roberson, *Nonlocal games and quantum permutation groups*, Theorem 4.4,
identifies the operator-algebraic formulation with the commuting-operator
isomorphism game used by `QuantumIso`.

https://doi.org/10.22028/D291-31806
https://arxiv.org/abs/1712.01820 -/
axiom Literature.schmidt_noSeparation_lt_sixteen {n : Nat} (hn : n < 16) :
    NoSeparation n

theorem through15 : Through 15 := by
  intro n hn
  exact Literature.schmidt_noSeparation_lt_sixteen (Nat.lt_succ_of_le hn)

end QGI
