import DoubledEdges
import FourEightGeometry

noncomputable section
open scoped BigOperators
namespace QGI.Coherent.FourCycleVectors
open StrategyColorLaws Intertwiner Synchrony FourTwelveCycle FourTwelveCycleGraph
open DoubledEdges (Src Dst)

abbrev L := Fin 4
abbrev V := Fin 16

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

private theorem row_sum (i : Fin n) : ∑ a, U p i a = 1 := by
  apply LinearMap.ext
  intro ξ
  apply Subtype.ext
  simpa only [LinearMap.sum_apply,Submodule.coe_sum,Module.End.one_apply,U] using (magic_sums p i ξ).1

/-- When two target labels of the four-point block form a visible pair
for each of the two neighbors of a given label, the fourth commutator
vanishes by the row-sum identity. -/
theorem fixed_of_cycle (sl tl : L ↪ Fin n) (v : Nat)
    (support : ∀ i a (ξ : cyclic p), U p (sl i) a ξ ≠ 0 → ∃ j, tl j=a)
    (pairs : ∀ a : L, ∃ t : L, ∀ b, a≠b → b≠t → ∃ y, neighbors (Dst p) v y={tl a,tl b}) :
    ∃ (ξ : cyclic p) (e : Equiv.Perm L), ξ ≠ 0 ∧ ∀ i, U p (sl i) (tl (e i)) ξ=ξ := by
  classical
  have total (i : L) : ∑ a : L, U p (sl i) (tl a) = 1 := by
    rw [←row_sum p (sl i)]
    apply Fintype.sum_of_injective tl tl.injective _ _ _ (fun _ => rfl)
    intro b outside
    apply LinearMap.ext
    intro ξ
    by_contra h
    exact outside (support i b ξ h)
  apply DoubledEdges.fixed_block p sl tl support
  intro i j a b
  obtain ⟨t,has⟩ := pairs a
  let A := U p (sl i) (tl a)
  let T (b : L) := U p (sl j) (tl b)
  have other (k : L) (ne : k≠t) : Commute A (T k) :=
    DoubledEdges.pair_commute p v _ _ _ _ (fun h => has _ (fun eq => h (congrArg tl eq)) ne)
  by_cases ne : b≠t
  · exact other b ne
  have hbt : b=t := not_not.mp ne
  subst b
  let s := (Finset.univ : Finset L).erase t
  have rest := Commute.sum_right s T A (fun k hk => other k (Finset.mem_erase.mp hk).1)
  have sum : (∑ k ∈ s, T k) + T t = 1 :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ t)).trans (total j)
  have val : T t = 1 - ∑ k ∈ s, T k := by rw [←sum]; abel
  change Commute A (T t)
  rw [val]
  exact (Commute.one_right A).sub_right rest

/-- After fixing all four images, any other source row is supported on
one target pattern relative to those four images and one diagonal name. -/
theorem isomorphic_of_patterns (sl tl : L ↪ Fin n) (v : Nat)
    (support : ∀ i a (ξ : cyclic p), U p (sl i) a ξ ≠ 0 → ∃ j, tl j=a)
    (pairs : ∀ a : L, ∃ t : L, ∀ b, a≠b → b≠t → ∃ y, neighbors (Dst p) v y={tl a,tl b})
    (patterns : ∀ a : Fin n, ∃ u w : Fin n, ∀ b, Dst p a a=Dst p b b →
      (∀ i, Dst p a (tl i)=Dst p b (tl i)) → b=u ∨ b=w) : Isomorphic G H := by
  obtain ⟨ξ,e,nz,fixed⟩ := fixed_of_cycle p sl tl v support pairs
  apply BinaryVectorChoice.isomorphic_on_cyclic p ξ nz
  intro x
  obtain ⟨a,act⟩ := DoubledEdges.nonzero_row p ξ nz x
  obtain ⟨u,w,rows⟩ := patterns a
  refine ⟨u,w,fun b hb => rows b ((DoubledEdges.diag_of_nonzero p act).symm.trans (DoubledEdges.diag_of_nonzero p hb)) ?_⟩
  have entry {b : Fin n} (h : U p x b ξ≠0) (i : L) :
      Src G x (sl i) = Dst p b (tl (e i)) := by
    apply (associated p).mpr (StrategyColors.maps_support p ?_)
    intro zero
    have eq := congrArg (fun Z : Module.End ℂ (cyclic p) => Z ξ) zero
    change U p x b (U p (sl i) (tl (e i)) ξ) = 0 at eq
    exact h ((congrArg (U p x b) (fixed i)).symm.trans eq)
  intro i
  obtain ⟨i,rfl⟩ := e.surjective i
  exact (entry act i).symm.trans (entry hb i)

end QGI.Coherent.FourCycleVectors
