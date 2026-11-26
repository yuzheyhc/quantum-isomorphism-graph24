import BinaryVectorChoice
import DoubledEdges
import LargeOrderBlocks

noncomputable section
open scoped InnerProductSpace
namespace QGI.Coherent.RegionalBinaryChoice
open FourTwelveFunctional (source)
open Synchrony Intertwiner StrategyColorLaws LargeFourteenRegion SmallUnion

variable {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

/-- The actual cyclic operators for a mismatched ordered pair of coherent
colors have orthogonal output vectors, for every common input vector. -/
theorem orthogonal {i j a b : Fin n} (ξ : cyclic p) (bad : source G i j ≠ targetName p a b) :
    ⟪U p i a ξ,U p j b ξ⟫_ℂ=0 := by
  have zero : (U p i a).comp (U p j b)=0 := by
    by_contra hit
    exact bad ((associated p).mpr (StrategyColors.maps_support p hit))
  change ⟪(U p i a ξ : K),(U p j b ξ : K)⟫_ℂ=0
  rw [(restricted_projection p _ _).2]
  have h := congrArg (fun f : Module.End ℂ (cyclic p) => f ξ) zero
  change U p i a (U p j b ξ)=0 at h
  rw [h]
  simp

/-- Two candidate target labels for each source point on a common nonzero
cyclic vector suffice to realize all original names, in any ambient order. -/
theorem solve (F T : Fin k → Fin n) (fi : Function.Injective F) (ti : Function.Injective T)
    (ξ : cyclic p) (nz : ξ≠0)
    (support : ∀ i, ∃ a b : Fin k, ∀ z, U p (F i) z ξ≠0 → z=T a ∨ z=T b) :
    ∃ h : Equiv.Perm (Fin k), ∀ i j, source G (F i) (F j)=targetName p (T (h i)) (T (h j)) := by
  classical
  choose a b allowed using support
  let row := fun (i : Fin k) (z : Fin n) => U p (F i) z ξ
  let label := fun (i : Fin k) (s : Bool) => if s then b i else a i
  let vec := fun (i : Fin k) (s : Bool) =>
    if s && decide (a i=b i) then 0 else row i (T (label i s))
  have sum (i : Fin k) : vec i false+vec i true=ξ := by
    have truncated : ∑ j ∈ ({T (a i),T (b i)} : Finset (Fin n)), row i j=ξ := by
      calc
        _ = ∑ j : Fin n, row i j := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ outside
          by_contra ne
          exact outside (by simpa only [Finset.mem_insert,Finset.mem_singleton] using allowed i j ne)
        _ = ξ := by
          apply Subtype.ext
          change (cyclic p).subtype (∑ j, row i j)=_
          rw [map_sum]
          exact (magic_sums p (F i) ξ).1
    by_cases eq : a i=b i
    · simpa [vec,label,eq] using truncated
    · simpa [vec,label,eq,ti.ne eq] using truncated
  have zero (i j : Fin k) (s t : Bool)
      (h : ⟪row i (T (label i s)),row j (T (label j t))⟫_ℂ=0) : ⟪vec i s,vec j t⟫_ℂ=0 := by
    dsimp only [vec]
    split_ifs <;> simp [h]
  have orth (i : Fin k) : ⟪vec i false,vec i true⟫_ℂ=0 := by
    by_cases eq : a i=b i
    · simp [vec,eq]
    · apply zero
      apply orthogonal
      intro hit
      have d := entries p hit (closure H).one_mem (Intertwiner.initial_diagonal p)
      simp [Matrix.one_apply,label,ti.ne eq] at d
  obtain ⟨h,_,cell⟩ := BinaryVectorChoice.color_equiv_of_binary_candidates ξ nz label vec sum orth
    (fun i j => source G (F i) (F j)) (fun a b => targetName p (T a) (T b)) (by
      intro i j s t ij eq
      apply zero
      apply orthogonal
      intro hit
      have d := entries p hit (closure H).one_mem (Intertwiner.initial_diagonal p)
      simp [Matrix.one_apply,fi.ne ij,eq] at d) (fun i j s t bad => zero _ _ _ _ (orthogonal p ξ bad))
  exact ⟨h,cell⟩

end QGI.Coherent.RegionalBinaryChoice
