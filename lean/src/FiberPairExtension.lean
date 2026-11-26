import SmallFiberExtension
import SmallShoreRealization
import SplitRectangleGluing
import SixTenCoordinates

noncomputable section
namespace QGI.Coherent.FiberPairExtension
open SmallFiberExtension SmallUnion StrategyColorLaws SixTenCoordinates
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension

abbrev Cell {n : Nat} (c : Fin n → Fin n → Nat) (l : Nat) := {x // c x x=l}

def twins {n : Nat} (c : Fin n → Fin n → Nat) (l v : Nat) :=
  SplitRectangle.Twins (fun (x : Cell c l) (y : Cell c v) => c x.val y.val)

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

private theorem rectangle {l k : Nat} {I : Type} (u t : I → Fin n)
    (f : Cell (source G) l → Cell (targetName p) l)
    (hf : ∀ i j, source G i.val j.val=targetName p (f i).val (f j).val)
    (ht : ∀ i j, source G (u i) (u j)=targetName p (t i) (t j))
    (i₀ : Cell (source G) l) (j₀ : I) (hj : source G (u j₀) (u j₀)=k)
    (base : source G i₀.val (u j₀)=targetName p (f i₀).val (t j₀))
    (shape : twins (source G) l k)
    (i : Cell (source G) l) (j : I) (name : source G (u j) (u j)=k) :
    source G i.val (u j)=targetName p (f i).val (t j) := by
  let c := source G
  let d := targetName p
  let j0 : Cell c k := ⟨u j₀,hj⟩
  let j' : Cell c k := ⟨u j,name⟩
  have column : c i.val (u j₀)=d (f i).val (t j₀) := by
    obtain ⟨w,h₁,h₂⟩ := PartialFunctional.middle d c (fun a b => (common_products p a b (hf i₀ i)).symm) (t j₀)
    have match' := base.trans h₁
    let mid : Cell c k := ⟨w,(Relations.end_colors _ match').2.symm.trans hj⟩
    have eq := shape.2 i₀ j0 mid match' i
    exact common_transpose p ((Relations.transpose _ eq).trans h₂.symm)
  obtain ⟨w,h₁,h₂⟩ := PartialFunctional.middle d c (fun a b => (common_products p a b (ht j₀ j)).symm) (f i).val
  have same := (common_transpose p column).trans h₁
  let mid : Cell c l := ⟨w,(Relations.end_colors _ same).2.symm.trans i.property⟩
  exact (shape.1 i mid j0 (Relations.transpose _ same) j').trans h₂.symm

/-- A previously realized union of full fibers can be enlarged by one
fiber of order at most thirteen. Two interacting exterior fibers can be
synchronized by prescribing one point on each. Additional uniform
rectangles impose no further choice. Both exterior anchors may coincide. -/
theorem attach {m l : Nat} (F : Shore (source G) l (Fin m)) (base : Fin m) (small : m≤13)
    (reg : Nat → Prop) (old : Realizes p reg) (y z : Region (source G) reg)
    (cover : ∀ j : Region (source G) reg, source G j.val j.val=source G y.val y.val ∨
      source G j.val j.val=source G z.val z.val ∨
      ∀ i x : Cell (source G) l, ∀ w : Fin n, source G w w=source G j.val j.val →
        source G i.val j.val=source G x.val w)
    (first : twins (source G) l (source G y.val y.val))
    (second : twins (source G) l (source G z.val z.val)) : Realizes p (fun v => reg v ∨ v=l) := by
  classical
  obtain ⟨e,he⟩ := old
  let c := source G
  let d := targetName p
  obtain ⟨m₀,hm⟩ := SmallUnion.diagonal_names p
  let T : Shore d l (Fin m) := F.trans (Equiv.subtypeEquiv m₀
    (fun x => ⟨fun h => (hm x).symm.trans h,fun h => (hm x).trans h⟩))
  let i₀ := F base
  obtain ⟨s,hy,hz⟩ := PartialFunctional.middle c d (fun a b => common_products p a b (he y z)) i₀.val
  let chosen : Cell d l := ⟨s,(SmallShore.endpoints p hy).2.symm.trans i₀.property⟩
  have onto {h : Fin n → Fin n → Nat} (A : Shore h l (Fin m)) (x : Fin n) :
      (∃ j, atPoint A j=x) ↔ h x x=l :=
    ⟨fun ⟨j,eq⟩ => eq ▸ (A j).property,fun h => ⟨A.symm ⟨x,h⟩,congrArg Subtype.val (A.apply_symm_apply _)⟩⟩
  have inj {h : Fin n → Fin n → Nat} (A : Shore h l (Fin m)) : Function.Injective (atPoint A) :=
    fun _ _ eq => A.injective (Subtype.ext eq)
  obtain ⟨u,atA,hu⟩ := SmallShore.realize_at p (Nat.zero_lt_of_lt base.isLt) small
    (atPoint F) (atPoint T) l (inj F) (inj T) (onto F) (onto T) base (T.symm chosen)
  let f : Cell c l ≃ Cell d l := (F.symm.trans u).trans T
  have hf (i j : Cell c l) : c i.val j.val=d (f i).val (f j).val := by
    simpa only [f,atPoint,Equiv.trans_apply,Equiv.apply_symm_apply] using hu (F.symm i) (F.symm j)
  have anchor : f i₀=chosen :=
    (congrArg (fun j => T (u j)) (F.symm_apply_apply base)).trans ((congrArg T atA).trans (T.apply_symm_apply chosen))
  have cross (i : Cell c l) (j : Region c reg) : c i.val j.val = d (f i).val (e j).val := by
    rcases cover j with h|h|h
    · apply rectangle p Subtype.val (fun j => (e j).val) f hf he i₀ y rfl _ first i j h
      rw [anchor]; exact common_transpose p hy
    · apply rectangle p Subtype.val (fun j => (e j).val) f hf he i₀ z rfl _ second i j h
      rw [anchor]; exact hz
    · obtain ⟨w,t,hit⟩ := StrategyColors.exists_source p (f i).val (e j).val
      have eq := (associated p).mpr (StrategyColors.maps_support p hit)
      obtain ⟨dw,dt⟩ := SmallShore.endpoints p eq
      exact (h i ⟨w,dw.trans (f i).property⟩ t (dt.trans (he j j).symm)).trans eq
  let U := Region c (fun v => reg v ∨ v=l)
  let old (x : U) (h : reg (c x.val x.val)) : Region c reg := ⟨x.val,(mem_vertices _ _ _).mpr h⟩
  let newPoint (x : U) (h : ¬reg (c x.val x.val)) : Cell c l :=
    ⟨x.val,((mem_vertices _ _ _).mp x.property).resolve_left h⟩
  let image (x : U) := if h : reg (c x.val x.val) then (e (old x h)).val else (f (newPoint x h)).val
  have name (x y : U) : c x.val y.val=d (image x) (image y) := by
    by_cases hx : reg (c x.val x.val) <;> by_cases hy : reg (c y.val y.val)
    · rw [show image x=_ from dif_pos hx,show image y=_ from dif_pos hy]
      exact he (old x hx) (old y hy)
    · rw [show image x=_ from dif_pos hx,show image y=_ from dif_neg hy]
      exact common_transpose p (cross (newPoint y hy) (old x hx))
    · rw [show image x=_ from dif_neg hx,show image y=_ from dif_pos hy]
      exact cross (newPoint x hx) (old y hy)
    · rw [show image x=_ from dif_neg hx,show image y=_ from dif_neg hy]
      exact hf (newPoint x hx) (newPoint y hy)
  obtain ⟨out,ho⟩ := bundle p _ image name
  exact ⟨out,fun i j => by rw [ho,ho]; exact name i j⟩

end QGI.Coherent.FiberPairExtension
