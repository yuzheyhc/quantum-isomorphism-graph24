import PinnedShoreSignatures

noncomputable section
namespace QGI.Coherent.TwelveSignatureAlignment
open SixTenCoordinates StrategyColorLaws Intertwiner Synchrony RegionalShorePins
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch
open private row_partner from LargeOrderTwelveCommon
open Classical

theorem dichotomy {α : Type*} (f : Fin 12 → α)
    (equal : ∀ i, (Finset.univ.filter (fun j => f j=f i)).card=(Finset.univ.filter (fun j => f j=f 0)).card) :
    (∀ i, (Finset.univ.filter (fun j => f j=f i)).card≤3) ∨ (Finset.univ.image f).card≤3 := by
  classical
  let k := (Finset.univ.filter (fun j => f j=f 0)).card
  by_cases h : k≤3
  · exact Or.inl (fun i => (equal i).le.trans h)
  right
  let V := Finset.univ.image f
  have total := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin 12)) V f
  have counted : ∑ x∈V, (Finset.univ.filter (fun j => f j=x)).card=∑ _x∈V,k := by
    apply Finset.sum_congr rfl; intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact equal i
  have all (i : Fin 12) : f i∈V := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rw [counted] at total
  have value : V.card*k=12 := by simpa [all] using total
  change V.card≤3
  by_contra! large
  have high := Nat.mul_le_mul large (show 4≤k by omega)
  omega

variable {n r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

theorem align {α : Type*} (Y : Shore (source G) r (Fin 12)) (Z : Shore (targetName p) r (Fin 12))
    (ξ : cyclic p) (nz : ξ≠0) (f g : Fin 12 → α)
    (supported : ∀ i a, U p (atPoint Y i) (atPoint Z a) ξ≠0 → f i=g a)
    (pair : ∀ i j a b, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z a) (atPoint Z b) →
      (f i=f j ↔ g a=g b))
    (few : (Finset.univ.image f).card≤3) :
    ∃ e : Equiv.Perm (Fin 12), (∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z (e i)) (atPoint Z (e j))) ∧
      ∀ i, f i=g (e i) := by
  classical
  obtain ⟨i,j,separate⟩ := PinnedShoreSignatures.representatives f few
  obtain ⟨a,ha⟩ := DoubledEdges.nonzero_row p ξ nz (atPoint Y i)
  obtain ⟨x,rfl⟩ := (range Z a).mpr ((DoubledEdges.diag_of_nonzero p ha).symm.trans (Y i).property)
  obtain ⟨b,hb,hit⟩ := row_partner p ξ ha (atPoint Y j)
  obtain ⟨y,rfl⟩ := (range Z b).mpr ((DoubledEdges.diag_of_nonzero p hb).symm.trans (Y j).property)
  obtain ⟨e,ei,ej,names⟩ := RegionalThreeClasses.small_pair p Y Z (by decide) i j x y hit
  have inV (a : Fin 12) : g a∈Finset.univ.image f := by
    have col : ∑ u, U p u (atPoint Z a) ξ=ξ := by
      apply Subtype.ext
      change (cyclic p).subtype (∑ u, U p u (atPoint Z a) ξ)=_
      rw [map_sum]; exact (magic_sums p (atPoint Z a) ξ).2
    obtain ⟨u,hu⟩ : ∃ u, U p u (atPoint Z a) ξ≠0 := by by_contra! zero; exact nz (col.symm.trans (by simp [zero]))
    obtain ⟨s,rfl⟩ := (range Y u).mpr ((DoubledEdges.diag_of_nonzero p hu).trans (Z a).property)
    exact Finset.mem_image.mpr ⟨s,Finset.mem_univ _,supported s a hu⟩
  refine ⟨e,names,fun s => separate _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)) _ (inV _) ?_ ?_⟩
  · have h := pair _ _ _ _ (names s i)
    rwa [ei,←supported i x ha] at h
  · have h := pair _ _ _ _ (names s j)
    rwa [ej,←supported j y hb] at h
end QGI.Coherent.TwelveSignatureAlignment
