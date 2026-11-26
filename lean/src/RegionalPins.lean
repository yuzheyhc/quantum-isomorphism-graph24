import RegionalCycleSupport

noncomputable section
namespace QGI.Coherent.RegionalPins
open Intertwiner Synchrony StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)

variable {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (ξ : cyclic p)

def Pinned (a : Fin n) : Prop := ∃ i, U p i a ξ=ξ

theorem equal {i a b t : Fin n} (ha : U p i a ξ≠0) (hb : U p i b ξ≠0) (pin : Pinned p ξ t) :
    targetName p a t=targetName p b t := by
  obtain ⟨j,fixed⟩ := pin
  have name (z : Fin n) (h : U p i z ξ≠0) : source G i j=targetName p z t := by
    apply (associated p).mpr (StrategyColors.maps_support p ?_)
    intro zero
    have eq := congrArg (fun Z : Module.End ℂ (cyclic p) => Z ξ) zero
    change U p i z (U p j t ξ)=0 at eq
    exact h ((congrArg (U p i z) fixed).symm.trans eq)
  exact (name a ha).symm.trans (name b hb)

theorem grow {m : Nat} (nz : ξ≠0) (T : Fin m ↪ Fin n)
    (fiber : ∀ i a, targetName p a a=targetName p (T i) (T i) → ∃ j, T j=a)
    (dist : ∀ i j : Fin m, (∀ t, Pinned p ξ t → targetName p (T i) t=targetName p (T j) t) → i=j) :
    ∀ j, Pinned p ξ (T j) := by
  classical
  obtain ⟨m₀,hm⟩ := SmallUnion.diagonal_names p
  let S := T.trans m₀.symm.toEmbedding
  have diag (i) : source G (S i) (S i)=targetName p (T i) (T i) := by
    simpa only [S,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using hm (S i)
  have supports (i a) (h : U p (S i) a ξ≠0) : ∃ j, T j=a :=
    fiber i a ((DoubledEdges.diag_of_nonzero p h).symm.trans (diag i))
  have each (i : Fin m) : ∃ a, U p (S i) (T a) ξ=ξ := by
    obtain ⟨a,ha⟩ := DoubledEdges.nonzero_row p ξ nz (S i)
    obtain ⟨a,rfl⟩ := supports i a ha
    have only (z : Fin n) (h : U p (S i) z ξ≠0) : z=T a := by
      obtain ⟨b,rfl⟩ := supports i z h
      exact congrArg T (dist b a (fun t pin => equal p ξ h ha pin))
    refine ⟨a,?_⟩
    have total : (∑ z, U p (S i) z ξ)=ξ := by
      apply Subtype.ext
      change (cyclic p).subtype (∑ z, U p (S i) z ξ)=_
      rw [map_sum]; exact (magic_sums p (S i) ξ).1
    rw [Finset.sum_eq_single (T a) (fun b _ hb => not_not.mp (fun act => hb (only b act))) (by simp)] at total
    exact total
  choose f fixed using each
  have inj : Function.Injective f := by
    intro i j h
    by_contra ne
    have bad := congrArg (fun z : Module.End ℂ (cyclic p) => z ξ) (magic_orthogonal p (T (f i)) _ _ (S.injective.ne ne)).2
    change U p (S i) (T (f i)) (U p (S j) (T (f i)) ξ)=0 at bad
    rw [show U p (S j) (T (f i)) ξ=ξ from h ▸ fixed j,fixed] at bad
    exact nz bad
  intro j
  obtain ⟨i,rfl⟩ := (Finite.injective_iff_bijective.mp inj).2 j
  exact ⟨S i,fixed i⟩

/-- A color test made against any already pinned target points can
reduce every row to two candidates on the same vector. -/
theorem realize (nz : ξ≠0) (f g : Fin k → Fin n) (fi : Function.Injective f) (gi : Function.Injective g)
    (range : ∀ i a, U p (f i) a ξ≠0 → ∃ j, g j=a)
    (short : ∀ a, ∃ u v : Fin k, ∀ b, targetName p (g a) (g a)=targetName p (g b) (g b) →
      (∀ t, Pinned p ξ t → targetName p (g a) t=targetName p (g b) t) → b=u ∨ b=v) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) := by
  apply RegionalBinaryChoice.solve p f g fi gi ξ nz
  intro i
  obtain ⟨a,ha⟩ := DoubledEdges.nonzero_row p ξ nz (f i)
  obtain ⟨a,rfl⟩ := range i a ha
  obtain ⟨u,v,rows⟩ := short a
  refine ⟨u,v,fun b hb => ?_⟩
  obtain ⟨b,rfl⟩ := range i b hb
  exact (rows b ((DoubledEdges.diag_of_nonzero p ha).symm.trans (DoubledEdges.diag_of_nonzero p hb))
    (fun _ h => equal p ξ ha hb h)).imp (congrArg g) (congrArg g)

end QGI.Coherent.RegionalPins
