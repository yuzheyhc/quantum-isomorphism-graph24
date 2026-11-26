import SixShoreCube
import SixShoreInterface
import ShoreEdgeMerge

noncomputable section
namespace QGI.Coherent.SixShoreExtension
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open SixShoreAtlas (Key Point hard cell mask subsets)
open SixShoreInterface (Reads Columns flag)
open private range from RegionalSixTwelveDispatch
open private narrow from TwoAnchorUnionGlue
open private twins from RegionalFourFourEight
variable {n l h : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) [NeZero (2*h)]

def keep (r : Fin 2 → Nat) (k : Nat) := ∃ i, k=r i

theorem extend {r : Fin 2 → Nat} (half : h=4 ∨ h=8) (F₀ : Shore (source G) l Point)
    (Y : ∀ i, Shore (source G) (r i) (Fin (2*h))) (apart : ∀ i, l≠r i) (previous : Realizes p (keep r)) :
    AlmostFullRegion.EdgeRealizes p (fun k => keep r k ∨ k=l) := by
  classical
  obtain ⟨m,diag⟩ := diagonal_names p
  let W : Shore (targetName p) l Point := F₀.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  have ind := (SmallShore.correspondence p (atPoint F₀) (atPoint W) l (Subtype.val_injective.comp F₀.injective)
    (Subtype.val_injective.comp W.injective) (range F₀) (range W)).1
  obtain ⟨a,f,sf⟩ := Literature.zivAv_six_homogeneous_catalog _ ind
  let F := f.trans F₀
  have atlas : Reads F a := sf
  let site (i : Fin 2) (j : Fin (2*h)) : Region (source G) (keep r) :=
    ⟨atPoint (Y i) j,(mem_vertices _ _ _).mpr ⟨i,(Y i j).property⟩⟩
  have sn (i j) : source G (site i j).val (site i j).val=r i := (Y i j).property
  by_cases ha : hard a
  swap
  · have model (i : Fin 2) : FiberPairExtension.twins (source G) l (r i) := by
      apply twins F (Y i)
      rcases SixShoreInterface.palette F (Y i) (sourceLaws _) half with ⟨v,all⟩|⟨v,w,pal,rows⟩
      · exact ⟨fun j x _ _ k => (all j k).trans (all x k).symm,fun _ j k _ x => (all x j).trans (all x k).symm⟩
      · exact (SixShoreInterface.description F (Y i) (sourceLaws _) half atlas pal rows).1 ha
    apply AlmostFullRegion.of_named p (FiberPairExtension.attach p F 0 (by decide) (keep r) previous (site 0 0) (site 1 0) ?_ ?_ ?_)
    · intro j; obtain ⟨i,hi⟩ := (mem_vertices _ _ _).mp j.property
      fin_cases i
      · exact Or.inl (hi.trans (sn 0 0).symm)
      · exact Or.inr (Or.inl (hi.trans (sn 1 0).symm))
    · rw [sn]; exact model _
    · rw [sn]; exact model _
  obtain ⟨e,old⟩ := previous
  obtain ⟨g,_,gg⟩ := SmallShore.realize_at p (by decide : 0<6) (by decide) (atPoint F) (atPoint W) l
    (Subtype.val_injective.comp F.injective) (Subtype.val_injective.comp W.injective) (range F) (range W) 0 0
  let T := g.trans W
  let Z (i : Fin 2) := (Y i).trans (narrow e old (show keep r (r i) from ⟨i,rfl⟩))
  have target (i j) : (e (site i j)).val=atPoint (Z i) j := rfl
  have ll (i j) : source G (atPoint F i) (atPoint F j)=targetName p (atPoint T i) (atPoint T j) := gg i j
  have atT : Reads T a := by
    intro i j x y; rw [←ll,←ll]; exact atlas i j x y
  let D (i : Fin 2) : Columns F (Y i) T (Z i) a := Classical.choice
    (SixShoreInterface.choose F (Y i) T (Z i) (commonLaws p) (sourceLaws _) (targetLaws p) half atlas atT ha)
  let u (x : Fin 2 × Fin (2*h)) := (D x.1).leftWord x.2
  let v (x : Fin 2 × Fin (2*h)) := (D x.1).rightWord x.2
  have coincide (x y) : SixShoreCube.meet (u x) (u y)=SixShoreCube.meet (v x) (v y) := by
    obtain ⟨i,j⟩ := x; obtain ⟨a,b⟩ := y
    have c₁ := SixShoreInterface.cross F (Y i) T (Z i) (D i).mark
    have c₂ := SixShoreInterface.cross F (Y a) T (Z a) (D a).mark
    have h := Block.fold (commonLaws p) (Block.flip (commonLaws p) c₁) c₂
      (fun u v => if u=true ∧ v=true then 1 else 0) (old (site i j) (site a b))
    have fmt (x y : Fin 9) : (Finset.univ.filter (fun z => mask x z=true ∧ mask y z=true)).card=SixShoreCube.meet x y := by
      apply congrArg Finset.card; ext z; simp [SixShoreCube.meet,subsets]
    simpa only [Finset.sum_boole,(D i).sourceBits,(D i).targetBits,(D a).sourceBits,(D a).targetBits,fmt] using h
  obtain ⟨motion,hm⟩ := SixShoreCube.extend u v coincide
  let σ : Equiv.Perm Point := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (SixShoreCube.bijective motion))
  apply ShoreEdgeMerge.join p F (σ.trans T) (keep r) (fun ⟨i,hi⟩ => apart i hi) e old
  · intro i j
    rcases SixShoreCube.internal a ha motion i j with h|h
    · exact common_edge p (((atlas _ _ _ _).mpr h).trans (ll _ _))
    · exact (G.symm _ _).trans (common_edge p (((atlas _ _ _ _).mpr h).trans (ll _ _)))
  · intro i x
    obtain ⟨q,hq⟩ := (mem_vertices _ _ _).mp x.property
    let j := (Y q).symm ⟨x.val,hq⟩
    have eq : site q j=x := Subtype.ext (congrArg (fun z : {u : Fin n // source G u u=r q} => z.val) ((Y q).apply_symm_apply ⟨x.val,hq⟩))
    rw [←eq,target]
    apply common_edge p ((D q).reflect i j (σ i) j ?_)
    rw [(D q).sourceBits,(D q).targetBits]
    exact of_decide_eq_true (hm (q,j)) i
end QGI.Coherent.SixShoreExtension
