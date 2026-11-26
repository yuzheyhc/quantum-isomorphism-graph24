import RegionalFourFourEight
import NineNineRectangles

noncomputable section
namespace QGI.Coherent.DeterminedShore
open SmallUnion SmallFiberExtension StrategyColorLaws FiberPairExtension SixTenCoordinates
open FourTwelveFunctional (source)
open private rectangle from FiberPairExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

/-- A single old point distinguishes all classes of new points that have
different external colors. A named map on the old side then extends. -/
theorem attach {l : Nat} (u : Fin n) (tag : source G u u=l)
    (small : (vertices (source G) (·=l)).card≤13) (keep : Nat → Prop)
    (old : Realizes p keep) (x : Region (source G) keep)
    (shape : twins (source G) l (source G x.val x.val))
    (determines : ∀ i t : Cell (source G) l, source G i.val x.val=source G t.val x.val →
      ∀ j : Region (source G) keep, source G i.val j.val=source G t.val j.val) :
    Realizes p (fun v => keep v ∨ v=l) := by
  classical
  let c := source G
  let d := targetName p
  obtain ⟨e,he⟩ := old
  obtain ⟨s,hxs,_⟩ := PartialFunctional.middle c d (fun a b => common_products p a b (he x x)) u
  let i₀ : Region c (·=l) := ⟨u,(mem_vertices _ _ _).mpr tag⟩
  let j₀ : Region d (·=l) := ⟨s,(mem_vertices _ _ _).mpr ((SmallShore.endpoints p hxs).2.symm.trans tag)⟩
  have ss := (SmallShore.endpoints p hxs).2
  obtain ⟨f,atU,_,hf⟩ := realize_region_pair p (·=l) (Finset.card_pos.mpr ⟨u,i₀.property⟩) small i₀ i₀ j₀ j₀ ss
  let ins (i : Cell c l) : Region c (·=l) := ⟨i.val,(mem_vertices _ _ _).mpr i.property⟩
  let out (i : Cell c l) : Cell d l := ⟨(f (ins i)).val,(mem_vertices _ _ _).mp (f (ins i)).property⟩
  have pin : c u x.val=d (out ⟨u,tag⟩).val (e x).val := by
    change c u x.val=d (f i₀).val (e x).val
    rw [atU]; exact common_transpose p hxs
  have atX (i : Cell c l) : c i.val x.val=d (out i).val (e x).val :=
    rectangle p Subtype.val (fun v => (e v).val) out (fun a b => hf (ins a) (ins b)) he
      ⟨u,tag⟩ x rfl pin shape i x rfl
  apply ThreeRectangleExtension.merge_maps p keep l e f he hf
  intro j i
  let a : Cell c l := ⟨i.val,(mem_vertices _ _ _).mp i.property⟩
  obtain ⟨t,ht,hj⟩ := PartialFunctional.middle d c (fun u v => (common_products p u v (he x j)).symm) (f i).val
  have same := (common_transpose p (atX a)).trans ht
  let b : Cell c l := ⟨t,(Relations.end_colors _ same).2.symm.trans a.property⟩
  exact common_transpose p ((determines a b (Relations.transpose _ same) j).trans hj.symm)

end QGI.Coherent.DeterminedShore
