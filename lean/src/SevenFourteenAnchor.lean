import RegionalBinaryChoice
import SixSixCycle


noncomputable section
namespace QGI.Coherent.SevenFourteenAnchor
open StrategyColorLaws SmallUnion SmallFiberExtension Synchrony Intertwiner
open SixTenCoordinates (Shore atPoint)
open FourTwelveFunctional (source)

open DoubledEdges (nonzero_row diag_of_nonzero)
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

private def emb {k l : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l (Fin k)) : Fin k ↪ Fin n :=
  F.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩

theorem coordinates {I J : Type} {c : Table n} {a b} (A : Shore c a I) (Y : Shore c b J) (diff : a≠b) :
    ∃ F : (I ⊕ J) ≃ Region c (fun t => t=a ∨ t=b),
      (∀ i, (F (.inl i)).val=atPoint A i) ∧ ∀ i, (F (.inr i)).val=atPoint Y i := by
  let f : (I ⊕ J) → Region c (fun t => t=a ∨ t=b) := Sum.elim
    (fun i => ⟨atPoint A i,(mem_vertices _ _ _).mpr (Or.inl (A i).property)⟩)
    (fun i => ⟨atPoint Y i,(mem_vertices _ _ _).mpr (Or.inr (Y i).property)⟩)
  have apart (i : I) (j : J) : atPoint A i≠atPoint Y j := by
    intro h; exact diff ((A i).property.symm.trans ((congrArg (fun x => c x x) h).trans (Y j).property))
  have inj : Function.Injective f := by
    intro x y eq
    have e := congrArg Subtype.val eq
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (A.injective (Subtype.ext e))
      | inr j => exact (apart i j e).elim
    | inr i =>
      cases y with
      | inl j => exact (apart j i e.symm).elim
      | inr j => exact congrArg Sum.inr (Y.injective (Subtype.ext e))
  have surj : Function.Surjective f := by
    intro z
    rcases (mem_vertices _ _ _).mp z.property with h|h
    · obtain ⟨i,hi⟩ := SixSixCycle.point A h; exact ⟨.inl i,Subtype.ext hi⟩
    · obtain ⟨i,hi⟩ := SixSixCycle.point Y h; exact ⟨.inr i,Subtype.ext hi⟩
  exact ⟨Equiv.ofBijective f ⟨inj,surj⟩,fun _ => rfl,fun _ => rfl⟩

theorem fixed_block {k : Nat} (sl tl : Fin k ↪ Fin n)
    (supported : ∀ i a (ξ : cyclic p), U p (sl i) a ξ ≠ 0 → ∃ j, tl j=a)
    (commutes : ∀ i j a b, Commute (U p (sl i) (tl a)) (U p (sl j) (tl b))) :
    ∃ (ξ : cyclic p) (e : Equiv.Perm (Fin k)), ξ ≠ 0 ∧ ∀ i, U p (sl i) (tl (e i)) ξ = ξ := by
  classical
  have localFix (s : Finset (Fin k)) : ∃ ξ : cyclic p, ξ ≠ 0 ∧
      ∀ i ∈ s, ∃ a : Fin k, U p (sl i) (tl a) ξ = ξ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨⟨p.psi,psi_mem p⟩,fun h => psi_ne_zero p (congrArg Subtype.val h),by simp⟩
    | @insert i s _ ih =>
      obtain ⟨ξ,nz,keep⟩ := ih
      obtain ⟨a,nonzero⟩ := nonzero_row p ξ nz (sl i)
      obtain ⟨a,rfl⟩ := supported i a ξ nonzero
      refine ⟨_,nonzero,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | old
      · exact ⟨a,congrArg (fun F : Module.End ℂ (cyclic p) => F ξ) (restricted_projection p _ _).1⟩
      · obtain ⟨b,hb⟩ := keep j old
        have comm := congrArg (fun F : Module.End ℂ (cyclic p) => F ξ)
          (commutes j i b a).eq
        exact ⟨b,comm.trans (congrArg (U p (sl i) (tl a)) hb)⟩
  obtain ⟨ξ,nz,h⟩ := localFix Finset.univ
  choose f hf using fun i => h i (Finset.mem_univ _)
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    have zero := congrArg (fun F : Module.End ℂ (cyclic p) => F ξ)
      (magic_orthogonal p (tl (f i)) _ _ (sl.injective.ne ne)).2
    change U p (sl i) (tl (f i)) (U p (sl j) (tl (f i)) ξ) = 0 at zero
    rw [show U p (sl j) (tl (f i)) ξ = ξ by rw [eq,hf],hf] at zero
    exact nz zero
  exact ⟨ξ,Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),nz,hf⟩



/-- A commuting anchor and at most two target labels for each full external
signature realize both named shores, including all their internal colors. -/
theorem realize {a b k h : Nat} (diff : a≠b) (A : Shore (source G) a (Fin k)) (Y : Shore (source G) b (Fin h))
    (S : Shore (targetName p) a (Fin k)) (Z : Shore (targetName p) b (Fin h))
    (comm : ∀ i j x y, Commute (ColorTensor.P p (atPoint A i) (atPoint S x))
      (ColorTensor.P p (atPoint A j) (atPoint S y)))
    (twins : ∀ j, ∃ u w, ∀ t, (∀ i, targetName p (atPoint Z t) (atPoint S i)=
      targetName p (atPoint Z j) (atPoint S i)) → t=u ∨ t=w) :
    Realizes p (fun t => t=a ∨ t=b) := by
  classical
  have unbounded (i j x y) : Commute (U p (atPoint A i) (atPoint S x)) (U p (atPoint A j) (atPoint S y)) := by
    ext ξ
    let z : ColorTensor.space p := ⟨ξ.val,(cyclic p).le_topologicalClosure ξ.property⟩
    exact congrArg (fun f : ColorTensor.space p →L[ℂ] ColorTensor.space p => (f z : K)) (comm i j x y).eq
  obtain ⟨ξ,e,nz,fixed⟩ := fixed_block p (emb A) (emb S) (fun i x _ hx =>
    SixSixCycle.point S ((diag_of_nonzero p hx).symm.trans (A i).property)) unbounded
  have named {x z} (active : U p x z ξ≠0) (i : Fin k) :
      source G x (atPoint A i)=targetName p z (atPoint S (e i)) := by
    apply (associated p).mpr
    apply StrategyColors.maps_support
    intro zero
    have eq := congrArg (fun q : Module.End ℂ (cyclic p) => q ξ) zero
    change U p x z (U p (atPoint A i) (atPoint S (e i)) ξ)=0 at eq
    exact active ((congrArg (U p x z) (fixed i)).symm.trans eq)
  obtain ⟨F,FL,FR⟩ := coordinates A Y diff
  obtain ⟨T,TL,TR⟩ := coordinates S Z diff
  let idx : Fin k ⊕ Fin h ≃ Fin (k+h) := finSumFinEquiv
  let f (i) := (F (idx.symm i)).val
  let g (i) := (T (idx.symm i)).val
  have fi : Function.Injective f := Subtype.val_injective.comp (F.injective.comp idx.symm.injective)
  have gi : Function.Injective g := Subtype.val_injective.comp (T.injective.comp idx.symm.injective)
  have sourcePt (i) : f (idx i)=(F i).val := by simp [f]
  have targetPt (i) : g (idx i)=(T i).val := by simp [g]
  obtain ⟨w,names⟩ := RegionalBinaryChoice.solve p f g fi gi ξ nz (by
    intro i
    obtain ⟨i,rfl⟩ := idx.surjective i
    rw [sourcePt]
    cases i with
    | inl i =>
      rw [FL]
      refine ⟨idx (.inl (e i)),idx (.inl (e i)),fun z active => Or.inl ?_⟩
      rw [targetPt,TL]
      by_contra ne
      have eq := congrArg (fun q : Module.End ℂ (cyclic p) => q ξ) (magic_orthogonal p (atPoint A i) z _ ne).1
      change U p (atPoint A i) z (U p (atPoint A i) (atPoint S (e i)) ξ)=0 at eq
      exact active ((congrArg (U p (atPoint A i) z) (fixed i)).symm.trans eq)
    | inr j =>
      rw [FR]
      have locate {z} (active : U p (atPoint Y j) z ξ≠0) : ∃ t, atPoint Z t=z :=
        SixSixCycle.point Z ((diag_of_nonzero p active).symm.trans (Y j).property)
      obtain ⟨z,active⟩ := nonzero_row p ξ nz (atPoint Y j)
      obtain ⟨l,rfl⟩ := locate active
      obtain ⟨u,w,only⟩ := twins l
      refine ⟨idx (.inr u),idx (.inr w),fun z hz => ?_⟩
      rw [targetPt,targetPt,TR,TR]
      obtain ⟨j',rfl⟩ := locate hz
      apply (only j' _).imp (congrArg (atPoint Z)) (congrArg (atPoint Z))
      intro i; obtain ⟨i,rfl⟩ := e.surjective i
      exact (named hz i).symm.trans (named active i))
  let full := F.symm.trans (idx.trans (w.trans (idx.symm.trans T)))
  refine ⟨full,fun i j => ?_⟩
  obtain ⟨i,rfl⟩ := F.surjective i
  obtain ⟨j,rfl⟩ := F.surjective j
  simpa only [f,g,full,Equiv.trans_apply,Equiv.symm_apply_apply] using names (idx i) (idx j)

end QGI.Coherent.SevenFourteenAnchor


