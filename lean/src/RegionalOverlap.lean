import RegionalFourFourEight
import NineNineRectangles

noncomputable section
namespace QGI.Coherent.RegionalOverlap
open SmallUnion SmallFiberExtension StrategyColorLaws SixTenCoordinates
open FourTwelveFunctional (source)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

def member {c : Fin n → Fin n → Nat} {s : Nat → Prop} (x : Fin n) (hx : s (c x x)) : Region c s :=
  ⟨x,(mem_vertices _ _ _).mpr hx⟩

/-- A named map on overlapping fibers gives honest coordinate permutations
on each constituent fiber. -/
theorem index_on {l k} {reg : Nat → Prop} (e : Region (source G) reg ≃ Region (targetName p) reg)
    (he : ∀ x y, source G x.val y.val=targetName p (e x).val (e y).val)
    (F : Shore (source G) l (Fin k)) (T : Shore (targetName p) l (Fin k)) (hl : reg l) :
    ∃ f : Equiv.Perm (Fin k), ∀ i, atPoint T (f i)=(e (member (atPoint F i) ((congrArg reg (F i).property).mpr hl))).val := by
  let a (i) : Region (source G) reg := member (atPoint F i) ((congrArg reg (F i).property).mpr hl)
  have tag (i) : targetName p (e (a i)).val (e (a i)).val=l := (he _ _).symm.trans (F i).property
  let v (i) := T.symm ⟨(e (a i)).val,tag i⟩
  have pos (i) : atPoint T (v i)=(e (a i)).val := congrArg Subtype.val (T.apply_symm_apply _)
  have inject : Function.Injective v := by
    intro i j eq
    have h := (pos i).symm.trans ((congrArg (atPoint T) eq).trans (pos j))
    have eq₁ : a i=a j := e.injective (Subtype.ext h)
    exact F.injective (Subtype.ext (congrArg (fun z : Region (source G) reg => z.val) eq₁))
  exact ⟨Equiv.ofBijective v (Finite.injective_iff_bijective.mp inject),pos⟩

/-- Glue maps on F+Z and F+Y when the Z/Y rectangle is uniform and
every named automorphism of F extends across F+Y. -/
theorem attach {l r v k m : Nat} (F : Shore (source G) l (Fin k)) (Y : Shore (source G) v (Fin m))
    (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v)
    (old : Realizes p (fun t => t=l ∨ t=r)) (pair : Realizes p (fun t => t=l ∨ t=v))
    (uniform : ∀ i j a b, source G i i=r → source G j j=v → source G a a=r → source G b b=v → source G i j=source G a b)
    (extend : ∀ e : Equiv.Perm (Fin k), (∀ i j, source G (atPoint F (e i)) (atPoint F (e j))=source G (atPoint F i) (atPoint F j)) →
      ∃ e' : Equiv.Perm (Fin m), (∀ i j, source G (atPoint F (e i)) (atPoint Y (e' j))=source G (atPoint F i) (atPoint Y j)) ∧
        ∀ i j, source G (atPoint Y (e' i)) (atPoint Y (e' j))=source G (atPoint Y i) (atPoint Y j)) : Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  obtain ⟨q,hq⟩ := old
  obtain ⟨w,hw⟩ := pair
  obtain ⟨b,hab⟩ := diagonal_names p
  let T : Shore d l (Fin k) := F.trans (Equiv.subtypeEquiv b (fun i => ⟨fun h => (hab i).symm.trans h,fun h => (hab i).trans h⟩))
  let Z : Shore d v (Fin m) := Y.trans (Equiv.subtypeEquiv b (fun i => ⟨fun h => (hab i).symm.trans h,fun h => (hab i).trans h⟩))
  obtain ⟨f,hf⟩ := index_on p q hq F T (Or.inl rfl)
  obtain ⟨g,hg⟩ := index_on p w hw F T (Or.inl rfl)
  obtain ⟨z,hz⟩ := index_on p w hw Y Z (Or.inr rfl)
  let atF (i) : Region c (fun t => t=l ∨ t=v) := member (atPoint F i) (Or.inl (F i).property)
  let atY (i) : Region c (fun t => t=l ∨ t=v) := member (atPoint Y i) (Or.inr (Y i).property)
  let oldF (i) : Region c (fun t => t=l ∨ t=r) := member (atPoint F i) (Or.inl (F i).property)
  let e := f.trans g.symm
  have transfer (i) : atPoint T (g (e i))=atPoint T (f i) := by simp [e]
  have fc (i j) : c (atPoint F (e i)) (atPoint F (e j))=c (atPoint F i) (atPoint F j) := by
    calc
      _ = d (atPoint T (g (e i))) (atPoint T (g (e j))) := by rw [hg,hg]; exact hw (atF (e i)) (atF (e j))
      _ = d (atPoint T (f i)) (atPoint T (f j)) := by rw [transfer,transfer]
      _ = _ := by rw [hf,hf]; exact (hq (oldF i) (oldF j)).symm
  obtain ⟨y,xy,yy⟩ := extend e fc
  let sy : Fin m ≃ ThreeRectangleExtension.Cell c v := Y.trans (Equiv.subtypeEquivRight (fun i => (mem_vertices c (·=v) i).symm))
  let tz : Fin m ≃ ThreeRectangleExtension.Cell d v := Z.trans (Equiv.subtypeEquivRight (fun i => (mem_vertices d (·=v) i).symm))
  let gY := sy.symm.trans ((y.trans z).trans tz)
  have loc (i) : (gY (sy i)).val=atPoint Z (z (y i)) := by simp only [gY,Equiv.trans_apply,Equiv.symm_apply_apply]; rfl
  have finY (i) : (sy i).val=atPoint Y i := rfl
  have marks (x y' : ThreeRectangleExtension.Cell c v) : c x.val y'.val=d (gY x).val (gY y').val := by
    obtain ⟨i,rfl⟩ := sy.surjective x
    obtain ⟨j,rfl⟩ := sy.surjective y'
    rw [loc,loc,finY,finY]
    change source G (atPoint Y i) (atPoint Y j)=_
    rw [←yy i j,hz,hz]
    exact hw (atY (y i)) (atY (y j))
  apply RegionalFourFourEight.restrict_map p (t:=reg) (s:=fun t => (t=l ∨ t=r) ∨ t=v) _ (fun x h => or_assoc.mpr (cover x h))
  apply ThreeRectangleExtension.merge_maps p _ v q gY hq marks
  intro x j
  obtain ⟨i,rfl⟩ := sy.surjective j
  rw [loc,finY]
  rcases (mem_vertices _ _ _).mp x.property with xl|xr
  · let a := F.symm ⟨x.val,xl⟩
    have pos : atPoint F a=x.val := congrArg Subtype.val (F.apply_symm_apply _)
    have target : atPoint T (f a)=(q x).val := (hf a).trans (congrArg (fun i => (q i).val) (Subtype.ext pos))
    rw [←pos,←target,←transfer a]
    change source G (atPoint F a) (atPoint Y i)=_
    rw [←xy a i,hg,hz]
    exact hw (atF (e a)) (atY (y i))
  · obtain ⟨a,b,hit⟩ := StrategyColors.exists_source p (q x).val (atPoint Z (z (y i)))
    have eq := (associated p).mpr (StrategyColors.maps_support p hit)
    obtain ⟨ea,eb⟩ := SmallShore.endpoints p eq
    exact (uniform _ _ a b xr (Y i).property (ea.trans ((hq x x).symm.trans xr)) (eb.trans (Z _).property)).trans eq

end QGI.Coherent.RegionalOverlap
