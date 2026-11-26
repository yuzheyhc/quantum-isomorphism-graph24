import SmallFiberExtension

noncomputable section
namespace QGI.Coherent.ThreeRectangleExtension
open SmallFiberExtension SmallUnion StrategyColorLaws
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension

abbrev Cell {n} (c : Fin n → Fin n → Nat) (l : Nat) := Region c (fun t => t=l)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

theorem merge_maps (reg : Nat → Prop) (s : Nat)
    (f : Region (source G) reg ≃ Region (targetName p) reg)
    (g : Cell (source G) s ≃ Cell (targetName p) s)
    (hf : ∀ x y, source G x.val y.val=targetName p (f x).val (f y).val)
    (hg : ∀ x y, source G x.val y.val=targetName p (g x).val (g y).val)
    (cross : ∀ x y, source G x.val y.val=targetName p (f x).val (g y).val) :
    Realizes p (fun t => reg t ∨ t=s) := by
  classical
  let c := source G
  let d := targetName p
  let U := Region c (fun t => reg t ∨ t=s)
  let old (i : U) (h : reg (c i.val i.val)) : Region c reg := ⟨i.val,(mem_vertices _ _ _).mpr h⟩
  let next (i : U) (h : ¬reg (c i.val i.val)) : Cell c s :=
    ⟨i.val,(mem_vertices _ _ _).mpr (((mem_vertices _ _ _).mp i.property).resolve_left h)⟩
  let m (i : U) := if hi : reg (c i.val i.val) then (f (old i hi)).val else (g (next i hi)).val
  have colored (i j : U) : c i.val j.val=d (m i) (m j) := by
    by_cases hi : reg (c i.val i.val) <;> by_cases hj : reg (c j.val j.val)
    · simpa only [m,dif_pos hi,dif_pos hj] using hf (old i hi) (old j hj)
    · simpa only [m,dif_pos hi,dif_neg hj] using cross (old i hi) (next j hj)
    · simpa only [m,dif_neg hi,dif_pos hj] using common_transpose p (cross (old j hj) (next i hi))
    · simpa only [m,dif_neg hi,dif_neg hj] using hg (next i hi) (next j hj)
  obtain ⟨e,h⟩ := bundle p _ m colored
  exact ⟨e,fun i j => by rw [h,h]; exact colored i j⟩

/-- A cross relation consisting of three matching full rectangles synchronizes
two local realizations. Every other cross relation must be constant on each
of the three column classes. The first shore may have arbitrary size. -/
theorem three_map {a s v : Nat} (small : (vertices (source G) (fun t => t=s)).card≤13)
    (A : Cell (source G) a → Fin 3) (Y : Cell (source G) s → Fin 3)
    (ontoA : Function.Surjective A) (ontoY : Function.Surjective Y)
    (rectangle : ∀ i j, source G i.val j.val=v ↔ A i=Y j)
    (tw : ∀ j k, Y j=Y k → ∀ i : Cell (source G) a, source G i.val j.val=source G i.val k.val)
    (f : Cell (source G) a ≃ Cell (targetName p) a)
    (hf : ∀ i j, source G i.val j.val=targetName p (f i).val (f j).val) :
    ∃ g : Cell (source G) s ≃ Cell (targetName p) s,
      (∀ i j, source G i.val j.val=targetName p (g i).val (g j).val) ∧
      ∀ i j, source G i.val j.val=targetName p (f i).val (g j).val := by
  classical
  let c := source G
  let d := targetName p

  choose ai hai using ontoA
  choose bj hbj using ontoY
  have anchor (r : Fin 3) : c (ai r).val (bj r).val=v := (rectangle _ _).mpr ((hai _).trans (hbj _).symm)
  let H₀ := anchor 0
  have dA {x z : Fin n} (hit : c x z=v) : c x x=a :=
    (Relations.end_colors (closure G) (hit.trans H₀.symm)).1.trans ((mem_vertices _ _ _).mp (ai 0).property)
  have dY {x z : Fin n} (hit : c x z=v) : c z z=s :=
    (Relations.end_colors (closure G) (hit.trans H₀.symm)).2.trans ((mem_vertices _ _ _).mp (bj 0).property)
  have targetA {x z : Fin n} (hit : d x z=v) : d x x=a :=
    (SmallShore.endpoints p (H₀.trans hit.symm)).1.symm.trans ((mem_vertices _ _ _).mp (ai 0).property)
  have targetY {x z : Fin n} (hit : d x z=v) : d z z=s :=
    (SmallShore.endpoints p (H₀.trans hit.symm)).2.symm.trans ((mem_vertices _ _ _).mp (bj 0).property)
  have pos := Finset.card_pos.mpr ⟨(bj 0).val,(bj 0).property⟩
  obtain ⟨prep,hprep⟩ := realize_region p (fun t => t=s) pos small
  have pick (j : Cell d s) : ∃ i : Cell c a, d (f i).val j.val=v := by
    let k := prep.symm j
    have eq : c k.val k.val=d j.val j.val := by simpa [k] using hprep k k
    let i := ai (Y k)
    have hit := (rectangle i k).mpr (hai _)
    obtain ⟨w,_,same⟩ := PartialFunctional.middle c d (fun u t => common_products p u t eq) i.val
    have match' := same.symm.trans hit
    let x : Cell d a := ⟨w,(mem_vertices _ _ _).mpr (targetA match')⟩
    exact ⟨f.symm x,by simpa [x] using match'⟩
  choose pickI chosen using pick
  let tag (j : Cell d s) := A (pickI j)
  have marked (i : Cell c a) (j : Cell d s) : d (f i).val j.val=v ↔ A i=tag j := by
    let h := pickI j
    obtain ⟨w,ww,wj⟩ := PartialFunctional.middle d c (fun u t => (common_products p u t (hf h i)).symm) j.val
    have hit := ww.symm.trans (chosen j)
    let z : Cell c s := ⟨w,(mem_vertices _ _ _).mpr (dY hit)⟩
    have link : d (f i).val j.val=c i.val z.val := (common_transpose p wj.symm).symm
    rw [link,rectangle]
    have dz : A h=Y z := (rectangle h z).mp hit
    exact ⟨fun eq => eq.trans dz.symm,fun eq => eq.trans dz⟩
  have classEq (j k : Cell c s) (y w : Cell d s) (eq : c j.val k.val=d y.val w.val) :
      Y j=Y k ↔ tag y=tag w := by
    constructor
    · intro h
      let i := ai (Y j)
      have lj := (rectangle i j).mpr (hai _)
      have lk := (rectangle i k).mpr ((hai _).trans h)
      obtain ⟨t,ly,lw⟩ := PartialFunctional.middle c d (fun u v => common_products p u v eq) i.val
      have ry := (common_transpose p ly).symm.trans lj
      have rw' := lw.symm.trans lk
      let t' : Cell d a := ⟨t,(mem_vertices _ _ _).mpr (targetA ry)⟩
      let i' := f.symm t'
      have iy : d (f i').val y.val=v := by simpa [i',t'] using ry
      have iw : d (f i').val w.val=v := by simpa [i',t'] using rw'
      exact ((marked _ _).mp iy).symm.trans ((marked _ _).mp iw)
    · intro h
      let i := pickI y
      have iy := chosen y
      have iw := (marked i w).mpr h
      obtain ⟨t,ly,lw⟩ := PartialFunctional.middle d c (fun u v => (common_products p u v eq).symm) (f i).val
      have ry := (common_transpose p ly.symm).trans iy
      have rw' := lw.symm.trans iw
      let i' : Cell c a := ⟨t,(mem_vertices _ _ _).mpr (dA ry)⟩
      exact ((rectangle i' j).mp ry).symm.trans ((rectangle i' k).mp rw')
  obtain ⟨u,lu,ru⟩ := PartialFunctional.middle c d (fun x y => common_products p x y (hf (ai 0) (ai 1))) (bj 0).val
  obtain ⟨w,lw,rw'⟩ := PartialFunctional.middle c d (fun x y => common_products p x y ru) (bj 1).val
  have Uhit := lu.symm.trans (anchor 0)
  have Whit := (common_transpose p rw').symm.trans (anchor 1)
  let U : Cell d s := ⟨u,(mem_vertices _ _ _).mpr (targetY Uhit)⟩
  let W : Cell d s := ⟨w,(mem_vertices _ _ _).mpr (targetY Whit)⟩
  have tU : tag U=0 := ((marked (ai 0) U).mp Uhit).symm.trans (hai 0)
  have tW : tag W=1 := ((marked (ai 1) W).mp Whit).symm.trans (hai 1)
  obtain ⟨g,gU,gW,hg⟩ := realize_region_pair p (fun t => t=s) pos small (bj 0) (bj 1) U W lw
  have tags (j : Cell c s) : tag (g j)=Y j := by
    have e₀ := classEq j (bj 0) (g j) (g (bj 0)) (hg j (bj 0))
    have e₁ := classEq j (bj 1) (g j) (g (bj 1)) (hg j (bj 1))
    rw [hbj,gU,tU] at e₀
    rw [hbj,gW,tW] at e₁
    exact (by decide : ∀ i j : Fin 3, (i=0 ↔ j=0) → (i=1 ↔ j=1) → j=i) _ _ e₀ e₁
  refine ⟨g,hg,?_⟩
  intro i j
  let h := ai (Y j)
  have used : d (f h).val (g j).val=v := (marked h _).mpr ((hai _).trans (tags _).symm)
  obtain ⟨k,lk,rk⟩ := PartialFunctional.middle d c (fun x y => (common_products p x y (hf h i)).symm) (g j).val
  have hk := lk.symm.trans used
  let k' : Cell c s := ⟨k,(mem_vertices _ _ _).mpr (dY hk)⟩
  have id := ((rectangle h k').mp hk).symm.trans (hai _)
  exact (tw k' j id i).symm.trans (common_transpose p rk.symm)

theorem three {a s v : Nat} (small : (vertices (source G) (fun t => t=s)).card≤13)
    (A : Cell (source G) a → Fin 3) (Y : Cell (source G) s → Fin 3)
    (ontoA : Function.Surjective A) (ontoY : Function.Surjective Y)
    (rectangle : ∀ i j, source G i.val j.val=v ↔ A i=Y j)
    (tw : ∀ j k, Y j=Y k → ∀ i : Cell (source G) a, source G i.val j.val=source G i.val k.val)
    (old : Realizes p (fun t => t=a)) : Realizes p (fun t => t=a ∨ t=s) := by
  obtain ⟨f,hf⟩ := old
  obtain ⟨g,hg,cross⟩ := three_map p small A Y ontoA ontoY rectangle tw f hf
  exact merge_maps p _ s f g hf hg cross

end QGI.Coherent.ThreeRectangleExtension

