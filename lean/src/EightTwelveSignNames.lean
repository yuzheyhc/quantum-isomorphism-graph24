import EightTwelveSignComparison

noncomputable section
namespace QGI.Coherent.EightTwelveSignNames
open EightTwelveSigns SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws RegionalEightTwelveStats
open RegionalEightTwelveHalfLaws (rowCells crossGram)
open EightTwelveSignComparison (Site pts name)
open FourTwelveFunctional (source)

theorem overlap_eq {o : Pairing} {b : I → Finset J} (P : RowPresentation o b) (i t : I) :
    rowOverlap P.rep i t=(b (P.left i)∩b (P.left t)).card := by
  unfold rowOverlap
  apply Finset.card_bij' (fun j _ => P.right j) (fun k _ => P.right.symm k)
  · intro j h
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bool.and_eq_true] at h
    exact Finset.mem_inter.mpr ⟨(P.hit i j).mpr h.1,(P.hit t j).mpr h.2⟩
  · intro k h
    obtain ⟨j,rfl⟩ := P.right.surjective k
    obtain ⟨u,v⟩ := Finset.mem_inter.mp h
    simpa only [Equiv.symm_apply_apply,Finset.mem_filter,Finset.mem_univ,true_and,Bool.and_eq_true] using
      And.intro ((P.hit i j).mp u) ((P.hit t j).mp v)
  · exact fun j _ => P.right.symm_apply_apply j
  · exact fun k _ => P.right.apply_symm_apply k

variable {n l r v w : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)
    (F : Shore (source G) l I) (Y : Shore (source G) r J)
    (T : Shore (targetName p) l I) (Z : Shore (targetName p) r J)

theorem glue {o : Pairing} (lr : l≠r) (A : RowPresentation o (rowCells (family F Y v)))
    (B : RowPresentation o (rowCells (family T Z v)))
    (right : ∀ i j x y, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z x) (atPoint Z y) ↔
      rightName (atlas o) i j=rightName (atlas o) x y)
    (left : ∀ i j x y, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T x) (atPoint T y) ↔
      crossGram (family F Y v) i j=crossGram (family T Z v) x y)
    (two : ∀ j i, color F Y j i=v ∨ color F Y j i=w)
    (reg : Nat → Prop) (cover : ∀ z, reg (source G z z) → source G z z=l ∨ source G z z=r) : Realizes p reg := by
  let F' := A.left.trans F
  let Y' := A.right.trans Y
  let T' := B.left.trans T
  let Z' := B.right.trans Z
  have rr (i j x y : J) : source G (atPoint Y' i) (atPoint Y' j)=targetName p (atPoint Z' x) (atPoint Z' y) ↔
      rightName (key A.rep) i j=rightName (key B.rep) x y := by
    rw [A.catalog,B.catalog,←A.names i j,←B.names x y]
    exact right _ _ _ _
  have ll (i j x y : I) : source G (atPoint F' i) (atPoint F' j)=targetName p (atPoint T' x) (atPoint T' y) ↔
      rowOverlap A.rep i j=rowOverlap B.rep x y := by
    rw [overlap_eq,overlap_eq,EightTwelveSignLaws.row_gram,EightTwelveSignLaws.row_gram]
    exact left _ _ _ _
  have rl (i : J) (j : I) (x : J) (y : I) :
      source G (atPoint Y' i) (atPoint F' j)=targetName p (atPoint Z' x) (atPoint T' y) ↔
      inside A.rep j i=inside B.rep y x := by
    rw [Bool.eq_iff_iff,←A.hit,←B.hit]
    simp only [rowCells,family,Finset.mem_filter,Finset.mem_univ,true_and]
    exact RegionalEightTwelveHalfModels.both_colors (two _ _) (RegionalEightTwelveHalfModels.target_two p F Y T Z two _ _)
  have rev {i j x y : Fin n} : source G i j=targetName p x y ↔ source G j i=targetName p y x :=
    ⟨fun h => common_transpose p h,fun h => common_transpose p h⟩
  apply EightTwelveSignComparison.solve p F' Y' T' Z' lr (A.catalog.trans B.catalog.symm) _ _ reg cover
  · intro u v s t eq
    have tags := SmallShore.endpoints p eq
    have dy {i : J} : source G (atPoint Y' i) (atPoint Y' i)=r := (Y' i).property
    have df {i : I} : source G (atPoint F' i) (atPoint F' i)=l := (F' i).property
    have dz {i : J} : targetName p (atPoint Z' i) (atPoint Z' i)=r := (Z' i).property
    have dt {i : I} : targetName p (atPoint T' i) (atPoint T' i)=l := (T' i).property
    rcases u with i|i <;> rcases v with j|j <;> rcases s with x|x <;> rcases t with y|y <;>
      simp only [pts,Sum.elim_inl,Sum.elim_inr] at tags eq <;>
      simp only [dy,df,dz,dt,lr,Ne.symm lr,false_and,and_false] at tags
    all_goals first
      | contradiction
      | exact (rr i j x y).mp eq
      | exact congrArg (fun b : Bool => 16+b.toNat) ((rl i j x y).mp eq)
      | exact congrArg (fun b : Bool => 18+b.toNat) ((rl j i y x).mp (rev.mp eq))
      | exact congrArg (20+·) ((ll i j x y).mp eq)
  · intro eq u v
    rcases u with i|i <;> rcases v with j|j
    · exact (rr i j i j).mpr (by rw [eq])
    · exact (rl i j i j).mpr (by rw [eq])
    · exact rev.mpr ((rl j i j i).mpr (by rw [eq]))
    · exact (ll i j i j).mpr (by rw [eq])

end QGI.Coherent.EightTwelveSignNames
