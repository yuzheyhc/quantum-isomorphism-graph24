import Intertwiner

noncomputable section
open scoped BigOperators

namespace QGI.ColorTensor
open Synchrony Intertwiner

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

/-- A closed subspace of the original commuting strategy's Hilbert space. -/
abbrev space := (cyclic p).topologicalClosure

instance [CompleteSpace K] : CompleteSpace (space p) :=
  (cyclic p).isClosed_topologicalClosure.completeSpace_coe

instance : Nontrivial (space p) :=
  ⟨⟨⟨p.psi, (cyclic p).le_topologicalClosure (psi_mem p)⟩, 0,
    fun e => psi_ne_zero p (congrArg (fun v : space p => (v : K)) e)⟩⟩

/-- Alice's forward projectors restrict as bounded operators on this same
closed space. Invariance on the algebraic cyclic space propagates by continuity. -/
def P (x a : Fin n) : space p →L[ℂ] space p :=
  ((p.alice (false,x) a).comp (space p).subtypeL).codRestrict (space p) fun v => by
    have stable : Set.MapsTo (p.alice (false,x) a) (cyclic p) (cyclic p) :=
      fun z hz => (U p x a (⟨z,hz⟩ : cyclic p)).property
    exact stable.closure (p.alice (false,x) a).continuous v.property

private theorem rows (x : Fin n) (v : space p) : ∑ a, P p x a v = v := by
  apply Subtype.ext
  change (space p).subtype (∑ a, P p x a v) = (v : K)
  rw [map_sum]
  exact (p.alicePVM (false,x)).complete v

private theorem cols (a : Fin n) (v : space p) : ∑ x, P p x a v = v := by
  have denseEq : Set.EqOn (fun z : K => ∑ x, p.alice (false,x) a z) id (cyclic p) :=
    fun z hz => (magic_sums p a ⟨z,hz⟩).2
  apply Subtype.ext
  change (space p).subtype (∑ x, P p x a v) = (v : K)
  rw [map_sum]
  exact denseEq.closure (continuous_finset_sum _ fun x _ => (p.alice (false,x) a).continuous)
    continuous_id v.property

/-- The entries defining the quantum permutation are projections with all
row and column sums the identity on a nonzero Hilbert space (Cai–Young Def. 5). -/
theorem quantumPermutation [CompleteSpace K] :
    (∀ x a, P p x a * P p x a = P p x a ∧ P p x a = (P p x a).adjoint) ∧
    (∀ x, ∑ a, P p x a = 1) ∧ (∀ a, ∑ x, P p x a = 1) := by
  refine ⟨fun x a => ⟨?_, ?_⟩, fun x => ?_, fun a => ?_⟩
  · apply ContinuousLinearMap.ext
    intro v
    apply Subtype.ext
    exact (p.alicePVM (false,x)).idempotent a v
  · apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro u v
    exact (p.alicePVM (false,x)).selfAdjoint a u v
  · apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.sum_apply]
    exact rows p x v
  · apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.sum_apply]
    exact cols p a v

theorem product_zero {A B : Mat n} (h : Intertwines p A B)
    (x y a b : Fin n) (bad : A x y ≠ B a b) (v : space p) :
    P p x a (P p y b v) = 0 := by
  have zero := compatible_of_intertwines p h x y a b bad
  have onCyclic : Set.EqOn (fun z : K => p.alice (false,x) a (p.alice (false,y) b z))
      (fun _ => 0) (cyclic p) := by
    intro z hz
    exact congrArg (fun f : cyclic p →ₗ[ℂ] cyclic p => (f ⟨z,hz⟩ : K)) zero
  apply Subtype.ext
  exact onCyclic.closure ((p.alice (false,x) a).continuous.comp (p.alice (false,y) b).continuous)
    continuous_const v.property

/-- The (x,y) component of U⊗² vec(B) = vec(A), as an actual bounded
operator identity. It applies to directed, individually named binary constraints.
All intertwiners for the same strategy use exactly the same U. -/
theorem tensor_square {A B : Mat n} (h : Intertwines p A B) (x y : Fin n) :
    (∑ a, ∑ b, B a b • (P p x a * P p y b)) =
      A x y • (1 : space p →L[ℂ] space p) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
  calc
    _ = ∑ a, ∑ b, A x y • P p x a (P p y b v) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases e : A x y = B a b
      · rw [e]
      · rw [product_zero p h x y a b e v, smul_zero, smul_zero]
    _ = A x y • v := by simp_rw [← Finset.smul_sum, ← map_sum, rows]

end QGI.ColorTensor
