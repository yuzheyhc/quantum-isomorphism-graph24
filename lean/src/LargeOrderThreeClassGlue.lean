import RegionalTwoAnchor

noncomputable section
namespace QGI.Coherent.LargeOrderThreeClassGlue
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension

/-- Glue a small two-fiber realization to an arbitrary realized region.
Two fixed points in the common fiber determine how its vertices interact
with the rest. Each remaining fiber has a constant rectangle to the new one. -/
theorem overlap {n l v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (reg old : Nat → Prop) (vo : old v)
    (cover : ∀ x, reg (source G x x) → source G x x=l ∨ old (source G x x))
    (given : Realizes p old) (small : (vertices (source G) (fun t => t=l ∨ t=v)).card≤13)
    (a b : Fin n) (da : source G a a=v) (db : source G b b=v)
    (uniform : ∀ i j x y, source G i i=l → old (source G j j) → source G j j≠v →
      source G x x=l → source G y y=source G j j → source G i j=source G x y)
    (rows : ∀ i x j, source G i i=v → source G x x=v → old (source G j j) → source G j j≠v →
      source G a i=source G a x → source G b i=source G b x → source G i j=source G x j) : Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  let side := fun t => t=l ∨ t=v
  let X := Region c reg
  let put (t : Nat → Prop) (x : Fin n) (h : t (c x x)) : Region c t := ⟨x,(mem_vertices _ _ _).mpr h⟩
  obtain ⟨r,hr⟩ := given
  let ra := put old a ((congrArg old da).mpr vo)
  let rb := put old b ((congrArg old db).mpr vo)
  let fa := put side a (Or.inr da)
  let fb := put side b (Or.inr db)
  let ta : Region d side := ⟨(r ra).val,(mem_vertices _ _ _).mpr (Or.inr ((hr ra ra).symm.trans da))⟩
  let tb : Region d side := ⟨(r rb).val,(mem_vertices _ _ _).mpr (Or.inr ((hr rb rb).symm.trans db))⟩
  obtain ⟨f,af,bf,hf⟩ := realize_region_pair p side (Finset.card_pos.mpr ⟨_,fa.property⟩) small fa fb ta tb (hr ra rb)
  have aeq : (f fa).val=(r ra).val := congrArg Subtype.val af
  have beq : (f fb).val=(r rb).val := congrArg Subtype.val bf
  have owned (x : X) := cover x.val ((mem_vertices _ _ _).mp x.property)
  have back (x : X) (h : ¬side (c x.val x.val)) : old (c x.val x.val) := (owned x).resolve_left (fun e => h (Or.inl e))
  let image (x : X) := if h : side (c x.val x.val) then (f (put side x.val h)).val else (r (put old x.val (back x h))).val
  have inner (x : X) (h : side (c x.val x.val)) : image x=(f (put side x.val h)).val := dif_pos h
  have outer (x : X) (h : ¬side (c x.val x.val)) : image x=(r (put old x.val (back x h))).val := dif_neg h
  have diag (x : X) : c x.val x.val=d (image x) (image x) := by
    by_cases h : side (c x.val x.val)
    · rw [inner x h]; exact hf (put side x.val h) (put side x.val h)
    · rw [outer x h]; exact hr (put old x.val (back x h)) (put old x.val (back x h))
  have cross (x y : X) (hx : side (c x.val x.val)) (hy : ¬side (c y.val y.val)) :
      c x.val y.val=d (image x) (image y) := by
    have dy : c y.val y.val≠v := fun h => hy (Or.inr h)
    rcases hx with hx|hx
    · obtain ⟨s,t,support⟩ := StrategyColors.exists_source p (image x) (image y)
      have h := (associated p).mpr (StrategyColors.maps_support p support)
      obtain ⟨ds,dt⟩ := SmallShore.endpoints p h
      exact (uniform _ _ _ _ hx (back y hy) dy (ds.trans ((diag x).symm.trans hx)) (dt.trans (diag y).symm)).trans h
    · have dt := (diag x).symm.trans hx
      let z := r.symm ⟨image x,(mem_vertices _ _ _).mpr ((congrArg old dt).mpr vo)⟩
      have eq : (r z).val=image x := congrArg Subtype.val (r.apply_symm_apply _)
      have dz : c z.val z.val=v := (hr z z).trans (by rw [eq]; exact dt)
      have ex : (r z).val=(f (put side x.val (Or.inr hx))).val := eq.trans (inner x (Or.inr hx))
      have first : c a x.val=c a z.val := (hf fa (put side x.val (Or.inr hx))).trans (by rw [aeq,←ex]; exact (hr ra z).symm)
      have second : c b x.val=c b z.val := (hf fb (put side x.val (Or.inr hx))).trans (by rw [beq,←ex]; exact (hr rb z).symm)
      refine (rows _ _ _ hx dz (back y hy) dy first second).trans ?_
      rw [←eq,outer y hy]; exact hr z (put old y.val (back y hy))
  have hit (x y : X) : c x.val y.val=d (image x) (image y) := by
    by_cases hx : side (c x.val x.val) <;> by_cases hy : side (c y.val y.val)
    · rw [inner x hx,inner y hy]; exact hf (put side x.val hx) (put side y.val hy)
    · exact cross x y hx hy
    · exact common_transpose p (cross y x hy hx)
    · rw [outer x hx,outer y hy]; exact hr (put old x.val (back x hx)) (put old y.val (back y hy))
  obtain ⟨e,he⟩ := bundle p reg image hit
  exact ⟨e,fun i j => by rw [he,he]; exact hit i j⟩

end QGI.Coherent.LargeOrderThreeClassGlue
