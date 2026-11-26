import FourTwelveFunctional

noncomputable section
open scoped BigOperators

namespace QGI.Coherent.FourAnchor
open StrategyColorLaws
abbrev V := Fin 16
abbrev Source (G : Graph 16) := Relations.color (closure G)

/-- Each vertex is singled out by its outgoing color from at least one of the four anchors. -/
def Determines (c : V → V → Nat) (u : Fin 4 → V) : Prop :=
  ∀ x : V, ∃ i : Fin 4, ∀ z : V, c (u i) z = c (u i) x → z = x

variable {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

/-- A compatible four-tuple of target anchors extends to an actual point
bijection. The input strategy supplies equal intersection numbers and
transpose maps, so every color singleton at an anchor transfers uniquely. -/
theorem extend {u v : Fin 4 → V} (thin : Determines (Source G) u)
    (pair : ∀ i j, i < j → Source G (u i) (u j) = targetName p (v i) (v j)) :
    ∃ e : Equiv.Perm V, ∀ i j, Source G i j = targetName p (e i) (e j) := by
  have diag (i : Fin 4) : Source G (u i) (u i) = targetName p (v i) (v i) := by
    by_cases small : i < 3
    · exact (SmallShore.endpoints p (pair i 3 small)).1
    · have pos : (0 : Fin 4) < i := by omega
      exact (SmallShore.endpoints p (pair 0 i pos)).2
  apply FourTwelveFunctional.extend p u v _ thin
  intro i j
  rcases lt_trichotomy i j with lt | rfl | gt
  · exact pair i j lt
  · exact diag i
  · exact common_transpose p (pair j i gt)

end QGI.Coherent.FourAnchor
