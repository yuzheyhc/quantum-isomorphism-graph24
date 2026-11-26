import StrategyColorLaws
import Mathlib.Logic.Equiv.Sum

noncomputable section
namespace QGI.Coherent.DiagonalCoordinates
open StrategyColorLaws

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The paired diagonal colors have the same multiplicities. A single
permutation aligns all diagonal colors, including when several classes
have the same cardinality. -/
theorem align (p : PerfectStrategy G H K) : ∃ e : Equiv.Perm (Fin n), ∀ i,
    Relations.color (closure G) i i = targetName p (e i) (e i) := by
  classical
  let c := fun i => Relations.color (closure G) i i
  let d := fun j => targetName p j j
  have counts (v : Nat) : Fintype.card {i // c i = v} = Fintype.card {j // d j = v} := by
    have trace := Intertwiner.trace_eq p (mark_intertwines p v)
    simp only [Fintype.card_subtype]
    simpa [Matrix.trace,Matrix.diag_apply,mark,c,d] using trace
  let localMap := fun v => Fintype.equivOfCardEq (counts v)
  let s := Equiv.sigmaFiberEquiv c
  let t := Equiv.sigmaFiberEquiv d
  let e := s.symm.trans ((Equiv.sigmaCongrRight localMap).trans t)
  refine ⟨e,?_⟩
  intro i
  obtain ⟨⟨v,x⟩,rfl⟩ := s.surjective i
  change c (s ⟨v,x⟩) = d (e (s ⟨v,x⟩))
  simp only [e,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact x.property.trans (localMap v x).property.symm

end QGI.Coherent.DiagonalCoordinates
