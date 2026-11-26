import SixNineGridGeometry
import SixNineAttachments
import RegionalOverlap

noncomputable section
namespace QGI.Coherent.SixNineSameTriples
open SixTenCoordinates SixEightGeometry SmallUnion SmallFiberExtension StrategyColorLaws
open SixNineGridGeometry
open FourTwelveFunctional (source)
open private narrow from TwoAnchorUnionGlue
open private cell from SixNineAttachments

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

/-- An old point that selects a class of new vertices determines the
cross names of every old row that is constant on that class. -/
theorem transport {keep : Nat → Prop} {v : Nat} (f : Region (source G) keep ≃ Region (targetName p) keep)
    (g : ThreeRectangleExtension.Cell (source G) v ≃ ThreeRectangleExtension.Cell (targetName p) v)
    (old : ∀ i j, source G i.val j.val=targetName p (f i).val (f j).val)
    (new : ∀ i j, source G i.val j.val=targetName p (g i).val (g j).val)
    (x a : Region (source G) keep) (y : ThreeRectangleExtension.Cell (source G) v)
    (anchor : ∀ j, source G a.val j.val=targetName p (f a).val (g j).val)
    (flat : ∀ u, source G u u=source G x.val x.val → ∀ j : ThreeRectangleExtension.Cell (source G) v,
      source G a.val j.val=source G a.val y.val → source G u j.val=source G u y.val) :
    source G x.val y.val=targetName p (f x).val (g y).val := by
  let c := source G
  let d := targetName p
  obtain ⟨e,links⟩ := (commonLaws p).middle (old x a)
  have ha := (links y.val).2
  have hy := (mem_vertices _ _ _).mp y.property
  have tag : d (e y.val) (e y.val)=v := (SmallShore.endpoints p ha).1.symm.trans hy
  let y' := g.symm ⟨e y.val,(mem_vertices _ _ _).mpr tag⟩
  have loc : (g y').val=e y.val := congrArg Subtype.val (g.apply_symm_apply _)
  have same : c a.val y'.val=c a.val y.val := (anchor y').trans ((congrArg (d (f a).val) loc).trans (common_transpose p ha).symm)
  obtain ⟨u,hu⟩ := (commonLaws p).middle (new y' y)
  let j := u.symm (f x).val
  have pos : u j=(f x).val := u.apply_symm_apply _
  have xy := common_transpose p (hu j).1
  have yy := (hu j).2
  rw [pos] at xy yy
  have jtag := (SmallShore.endpoints p yy).1.trans (old x x).symm
  calc
    _ = d (f x).val (e y.val) := (links y.val).1
    _ = c j y'.val := (congrArg (d (f x).val) loc.symm).trans xy.symm
    _ = c j y.val := flat j jtag y' same
    _ = _ := yy

variable [CompleteSpace K]
theorem attach {l r v : Nat} (A : Shore (source G) l (Fin 6)) (B : Shore (source G) r (Fin 6))
    (Y : Shore (source G) v (Fin 9)) (P : Triple A Y) (Q : Triple B Y)
    (equal : ∀ i j, P.b i=P.b j → Q.b i=Q.b j) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v)
    (old : Realizes p (fun t => t=r ∨ t=l)) : Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  let keep := fun t => t=r ∨ t=l
  obtain ⟨f,hf⟩ := old
  let ck := cell c l
  let cy := cell c v
  let fc := ck.trans ((narrow f hf (show keep l from Or.inr rfl)).trans (cell d l).symm)
  let an (i : ThreeRectangleExtension.Cell c l) : Region c keep := ⟨i.val,(mem_vertices _ _ _).mpr (Or.inr ((mem_vertices _ _ _).mp i.property))⟩
  let ix := ck.trans A.symm
  let iy := cy.trans Y.symm
  have ax (i) : atPoint A (ix i)=i.val := congrArg Subtype.val (A.apply_symm_apply _)
  have ay (i) : atPoint Y (iy i)=i.val := congrArg Subtype.val (Y.apply_symm_apply _)
  have ontoA : Function.Surjective P.a := fun t => by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun i => P.a i=t)).card by rw [P.aSize]; decide)
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  have ontoB : Function.Surjective P.b := fun t => by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun i => P.b i=t)).card by rw [P.bSize]; decide)
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  obtain ⟨g,hg,cross⟩ := ThreeRectangleExtension.three_map p (s:=v) ((RegionalTwoAnchor.card Y).trans_le (by decide))
    (P.a ∘ ix) (P.b ∘ iy) (ontoA.comp ix.surjective) (ontoB.comp iy.surjective)
    (fun i j => by simpa only [Function.comp_apply,rect,ax,ay] using P.flag (ix i) (iy j))
    (fun i j h k => by simpa only [rect,ax,ay] using P.uniform _ _ h (ix k)) fc (fun i j => hf (an i) (an j))
  apply RegionalFourFourEight.restrict_map p (ThreeRectangleExtension.merge_maps p keep v f g hf hg (fun x y => ?_))
  · intro i h; rcases cover i h with h|h|h <;> tauto
  · by_cases xl : c x.val x.val=l
    · let i : ThreeRectangleExtension.Cell c l := ⟨x.val,(mem_vertices _ _ _).mpr xl⟩
      exact cross i y
    have xr := ((mem_vertices _ _ _).mp x.property).resolve_right xl
    obtain ⟨a,ha⟩ := ontoA (P.b (iy y))
    let sel := ix.symm a
    have ia : ix sel=a := ix.apply_symm_apply _
    apply transport p f g hf hg x (an sel) y (cross sel)
    intro u hu j h
    obtain ⟨b,hb⟩ := (RegionalCycleExtension.range_emb B u).mpr (hu.trans xr)
    have pair : rect A Y a (iy j)=rect A Y a (iy y) := by rw [←ia]; simpa only [rect,ax,ay] using h
    have matched := (P.flag a (iy j)).mp (pair.trans ((P.flag a (iy y)).mpr ha))
    have eq := Q.uniform (iy j) (iy y) (equal _ _ (matched.symm.trans ha)) b
    simpa only [rect,ay,show atPoint B b=u from hb] using eq

end QGI.Coherent.SixNineSameTriples
