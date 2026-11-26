import EightFourteenComparison
import EightFourteenTransfer
import CoprimeProfiles

noncomputable section
namespace QGI.Coherent.RegionalEightFourteen
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open EightFourteenWords (I J)
open EightFourteenPlacement (rightName inside key)
open EightFourteenReduction (entry flag HardData)
open EightFourteenTransfer (coarse Data)
open EightFourteenComparison (pts)
open private range from RegionalSixTwelveDispatch
open private shore from RegionalFourFourEight
variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
   (p : PerfectStrategy G H K)

private theorem hard_region (F : Shore (source G) l I) (Y : Shore (source G) r J)
    {d : EightFourteenCatalog.RK} {v w : Nat} (D : HardData F Y d v w) :
    AlmostFullRegion.EdgeRealizes p (fun z => z=l ∨ z=r) := by
  have lr : l≠r := by
    rintro rfl; have h := Fintype.card_congr (F.trans Y.symm); simp only [Fintype.card_fin] at h; omega
  obtain ⟨m,diag⟩ := diagonal_names p
  let U : Shore (targetName p) l I := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let W : Shore (targetName p) r J := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨f,_,lf⟩ := SmallShore.realize_at p (by decide : 0<8) (by decide) (atPoint F) (atPoint U) l
    (Subtype.val_injective.comp F.injective) (Subtype.val_injective.comp U.injective) (range F) (range U) 0 0
  obtain ⟨s,t,u,h⟩ := SmallShore.correspondence p (atPoint Y) (atPoint W) r
    (Subtype.val_injective.comp Y.injective) (Subtype.val_injective.comp W.injective) (range Y) (range W)
  obtain ⟨g,rg⟩ := Literature.zivAv_named_fourteen_scheme s t u h
  let T := f.trans U
  let Z := g.trans W
  have leftOld (i j) : source G (atPoint F i) (atPoint F j)=targetName p (atPoint T i) (atPoint T j) := lf i j
  have rightOld (i j) : source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j) := rg i j
  obtain ⟨⟨A⟩,⟨B⟩⟩ := EightFourteenTransfer.layouts p F Y T Z D leftOld rightOld
  let F' := A.rows.trans F
  let Y' := A.cols.trans Y
  let T' := B.rows.trans T
  let Z' := B.cols.trans Z
  have rnamed (i j x y : J) : source G (atPoint Y' i) (atPoint Y' j)=targetName p (atPoint Z' x) (atPoint Z' y) ↔
      EightFourteenCatalog.right d (A.cols i) (A.cols j)=EightFourteenCatalog.right d (B.cols x) (B.cols y) := by
    change source G (atPoint Y _) (atPoint Y _)=targetName p (atPoint Z _) (atPoint Z _) ↔ _
    rw [←rightOld]; exact D.rightNames _ _ _ _
  have folded (i j x y : J) : rightName (key A.rep) i j=rightName (key B.rep) x y ↔
      rightName (coarse d) (A.cols i) (A.cols j)=rightName (coarse d) (B.cols x) (B.cols y) := by
    rw [A.sameKey,B.sameKey,A.names,B.names]
  have rr (i j x y : J) (eq : source G (atPoint Y' i) (atPoint Y' j)=targetName p (atPoint Z' x) (atPoint Z' y)) :=
    (folded i j x y).mpr ((EightFourteenTransfer.colors d D.hardKey _ _ _ _).1 ((rnamed i j x y).mp eq))
  have ll (i j x y : I) : source G (atPoint F' i) (atPoint F' j)=targetName p (atPoint T' x) (atPoint T' y) ↔ (i=j ↔ x=y) := by
    change source G (atPoint F _) (atPoint F _)=targetName p (atPoint T _) (atPoint T _) ↔ _
    rw [←leftOld,D.leftNames,A.rows.injective.eq_iff,B.rows.injective.eq_iff]
  have cr (i : I) (j : J) (x : I) (y : J) :
      source G (atPoint F' i) (atPoint Y' j)=targetName p (atPoint T' x) (atPoint Z' y) ↔ inside A.rep i j=inside B.rep x y := by
    rw [←A.flags,←B.flags,Bool.eq_iff_iff]
    simp only [flag,decide_eq_true_eq]
    exact RegionalEightTwelveHalfModels.both_colors (D.palette _ _) (EightFourteenTransfer.target_palette p F Y T Z D.palette _ _)
  have rev {i j x y : Fin n} : source G i j=targetName p x y ↔ source G j i=targetName p y x :=
    ⟨fun h => common_transpose p h,fun h => common_transpose p h⟩
  apply EightFourteenComparison.solve p F' Y' T' Z' lr (A.sameKey.trans B.sameKey.symm)
  · intro i j x y h
    have ends := SmallShore.endpoints p h
    have dy {i : J} : source G (atPoint Y' i) (atPoint Y' i)=r := (Y' i).property
    have df {i : I} : source G (atPoint F' i) (atPoint F' i)=l := (F' i).property
    have dz {i : J} : targetName p (atPoint Z' i) (atPoint Z' i)=r := (Z' i).property
    have dt {i : I} : targetName p (atPoint T' i) (atPoint T' i)=l := (T' i).property
    rcases i with i|i <;> rcases j with j|j <;> rcases x with x|x <;> rcases y with y|y <;>
      simp only [pts,Sum.elim_inl,Sum.elim_inr] at ends h <;>
      simp only [dy,df,dz,dt,lr,Ne.symm lr,false_and,and_false] at ends
    all_goals first
      | contradiction
      | exact rr i j x y h
      | exact congrArg (fun b : Bool => 16+b.toNat) ((cr j i y x).mp (rev.mp h))
      | exact congrArg (fun b : Bool => 18+b.toNat) ((cr i j x y).mp h)
      | exact congrArg (fun b : Bool => 20+b.toNat) (Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using (ll i j x y).mp h))
  · intro same i j
    rcases i with i|i <;> rcases j with j|j
    · have eq := (folded i j i j).mp (by rw [same])
      rcases (EightFourteenTransfer.colors d D.hardKey _ _ _ _).2 eq with h|h
      · exact common_edge p ((rnamed i j i j).mpr h)
      · exact (G.symm _ _).trans (common_edge p ((rnamed j i i j).mpr h))
    · exact common_edge p (rev.mpr ((cr j i j i).mpr (by rw [same])))
    · exact common_edge p ((cr i j i j).mpr (by rw [same]))
    · exact common_edge p ((ll i j i j).mpr Iff.rfl)

theorem region (F : Shore (source G) l I) (Y : Shore (source G) r J) : AlmostFullRegion.EdgeRealizes p (fun z => z=l ∨ z=r) := by
  rcases EightFourteenReduction.reduction p F Y (fun z => z=l ∨ z=r) (fun _ h => h) with h|⟨F',Y',d,v,w,D⟩
  · exact AlmostFullRegion.of_named p h
  · exact hard_region p F' Y' D

include p in
theorem isomorphic (bound : n≤23) (eight : ∃ i : Fin n, (fiber G i).card=8) (fourteen : ∃ i : Fin n, (fiber G i).card=14) : Isomorphic G H := by
  classical
  obtain ⟨a,sa⟩ := eight
  obtain ⟨b,sb⟩ := fourteen
  obtain ⟨F⟩ := shore a sa
  obtain ⟨Y⟩ := shore b sb
  have diff : source G a a≠source G b b := by
    rintro eq
    have same : fiber G a=fiber G b := by ext i; rw [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.fiber_eq,eq]
    rw [same,sb] at sa; contradiction
  have dj : Disjoint (fiber G a) (fiber G b) := Finset.disjoint_left.mpr fun _ h k =>
    diff (((FourTwelveFunctional.fiber_eq _ _).mp h).symm.trans ((FourTwelveFunctional.fiber_eq _ _).mp k))
  have inc : fiber G a∪fiber G b=vertices (source G) (fun u => u=source G a a ∨ u=source G b b) := by
    ext z; simp only [Finset.mem_union,FourTwelveFunctional.fiber_eq,mem_vertices]
  apply AlmostFullRegion.isomorphic p (fun u => u=source G a a ∨ u=source G b b) _ (region p F Y)
  rw [←inc,Finset.card_union_of_disjoint dj,sa,sb]; omega

end QGI.Coherent.RegionalEightFourteen
