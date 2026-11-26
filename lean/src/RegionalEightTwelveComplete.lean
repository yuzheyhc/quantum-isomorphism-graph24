import HalfPairRealize

noncomputable section
namespace QGI.Coherent.RegionalEightTwelveComplete
open EightTwelveHalf RegionalEightTwelveStats RegionalEightTwelveHalfLaws SmallUnion SmallFiberExtension StrategyColorLaws SixTenCoordinates
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (F : Shore (source G) l P) (Y : Shore (source G) r J)

/-- The only remaining incidence family has twelve distinct four-subsets of eight points. -/
theorem reduction (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) :
    Realizes p reg ∨ ∃ v w, v≠w ∧ (∀ j i, color F Y j i=v ∨ color F Y j i=w) ∧
      (∀ j, (family F Y v j).card=4) ∧ NamedGram F (family F Y v) ∧
      ∃ e : Equiv.Perm P, (supports (family F Y v)).image (fun s => s.image e)=model 4 := by
  rcases RegionalEightTwelve.reduction p F Y reg cover with doneAlready|⟨v,w,vw,two,size⟩
  · exact Or.inl doneAlready
  obtain ⟨m,diag⟩ := diagonal_names p
  let T : Shore (targetName p) l P := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  have data := (SmallShore.correspondence p (atPoint F) (atPoint T) l (Subtype.val_injective.comp F.injective)
    (Subtype.val_injective.comp T.injective) (range F) (range T)).1
  obtain ⟨names,k,e,shape⟩ := classification F Y data (sourceLaws _) two size
  by_cases pair : k=1 ∨ k=2
  · obtain ⟨lay⟩ := HalfPair.layout (sourceLaws _) F Y v k pair e shape
    exact Or.inl (HalfPair.realize p F Y reg cover lay size)
  have other : k=0 ∨ k=3 ∨ k=4 := by omega
  rcases other with h|h|h
  · subst k; exact Or.inl (RegionalEightTwelve.of_twins p F Y reg cover
      (RegionalEightTwelveHalfModels.model_zero_twins F Y two e shape))
  · subst k; exact Or.inl (RegionalEightTwelveHalfModels.cube p F Y reg cover two size names e shape)
  · subst k; exact Or.inr ⟨v,w,vw,two,size,names,e,shape⟩

end QGI.Coherent.RegionalEightTwelveComplete
