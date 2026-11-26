import StrategyColorLaws
import BinaryVectorChoice

noncomputable section
namespace QGI.Coherent.RootedTwoChoices
open Relations StrategyColors StrategyColorLaws Synchrony Intertwiner
open scoped BigOperators

/-- At any order, if all color classes in one rooted row contain at most two
vertices, a commuting quantum isomorphism already gives a graph isomorphism. -/
theorem isomorphic {n : Nat} {G H : Graph n} (a : Fin n)
    (small : ∀ b, ∃ s t : Fin n, ∀ z, color (closure G) a z = color (closure G) a b → z=s ∨ z=t)
    (q : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,gr,ip,_,⟨p⟩⟩ := q.symm
  letI : NormedAddCommGroup K := gr
  letI : InnerProductSpace ℂ K := ip
  let ψ : cyclic p := ⟨p.psi,psi_mem p⟩
  have column : ∃ i, U p i a ψ ≠ 0 := by
    by_contra! none
    have h := (magic_sums p a ψ).2
    simp only [←show ∀ i, U p i a = restricted p (false,i) a from fun _ => rfl,none,
      Submodule.coe_zero,Finset.sum_const_zero] at h
    exact psi_ne_zero p h.symm
  obtain ⟨i,ni⟩ := column
  let ξ := U p i a ψ
  have fixed : U p i a ξ=ξ :=
    congrArg (fun Z : Module.End ℂ (cyclic p) => Z ψ) (restricted_projection p (false,i) a).1
  apply Isomorphic.symm (BinaryVectorChoice.isomorphic_on_cyclic p ξ ni ?_)
  intro j
  have active : ∃ b, U p j b ξ ≠ 0 := by
    by_contra! none
    have h := (magic_sums p j ξ).1
    simp only [←show ∀ b, U p j b = restricted p (false,j) b from fun _ => rfl,none,
      Submodule.coe_zero,Finset.sum_const_zero] at h
    exact ni (Subtype.ext h.symm)
  obtain ⟨b,hb⟩ := active
  have tag {z : Fin n} (hz : U p j z ξ≠0) : color (closure H) i j = targetName p a z := by
    apply common_transpose p
    apply (associated p).mpr (maps_support p ?_)
    intro zero
    have h := congrArg (fun Z : Module.End ℂ (cyclic p) => Z ξ) zero
    change U p j z (U p i a ξ)=0 at h
    exact hz (fixed ▸ h)
  obtain ⟨s,t,hs⟩ := small b
  exact ⟨s,t,fun z hz => hs z ((target_same p _ _ _ _).mp ((tag hz).symm.trans (tag hb)))⟩

end QGI.Coherent.RootedTwoChoices
