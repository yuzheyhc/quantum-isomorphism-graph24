import TwoAnchorUnionGlue
import LargeOrderBlocks

noncomputable section
namespace QGI.Coherent.RegionalTwoAnchor
open Relations StrategyColorLaws SixTenCoordinates SmallUnion SmallFiberExtension
open FourTwelveFunctional (source)
open private narrow from TwoAnchorUnionGlue
open private bundle from SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

theorem card {k v : Nat} (F : Shore (source G) v (Fin k)) :
    (vertices (source G) (·=v)).card=k := by
  let e := Equiv.subtypeEquivRight (p := fun i => i ∈ vertices (source G) (·=v))
    (q := fun i => source G i i=v) (fun i => mem_vertices _ _ i)
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_congr (e.trans F.symm)

theorem pair_bound {s t l r : Nat} (F : Shore (source G) l (Fin s)) (Y : Shore (source G) r (Fin t)) :
    (vertices (source G) (fun k => k=l ∨ k=r)).card≤s+t := by
  have eq : vertices (source G) (fun k => k=l ∨ k=r)=vertices (source G) (·=l) ∪ vertices (source G) (·=r) := by
    ext i; simp only [mem_vertices,Finset.mem_union]
  rw [eq,←card F,←card Y]
  exact Finset.card_union_le _ _

theorem solve {l r v : Nat} (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (F : Shore (source G) l (Fin 4)) (S : Shore (source G) r (Fin 4)) (Y : Shore (source G) v (Fin 8))
    (uniform : ∀ i j, source G (atPoint F i) (atPoint S j)=source G (atPoint F 0) (atPoint S 0))
    (base : TwoAnchorUnionGlue.TwoBase (fun i j => source G (atPoint Y i) (atPoint Y j))) :
    Realizes p (fun t => t=l ∨ t=r ∨ t=v) := by
  classical
  let c := source G
  let d := targetName p
  let L := fun k => k=l ∨ k=v
  let R := fun k => k=r ∨ k=v
  let reg := fun k => k=l ∨ k=r ∨ k=v
  let X := Region c reg
  let jl (x : Fin n) (hx : L (c x x)) : Region c L := ⟨x,(mem_vertices _ _ _).mpr hx⟩
  let jr (x : Fin n) (hx : R (c x x)) : Region c R := ⟨x,(mem_vertices _ _ _).mpr hx⟩
  obtain ⟨e,he⟩ := LargeOrderBlocks.small p L ((pair_bound F Y).trans (by decide))
  let A := Y.trans (narrow e he (show L v from Or.inr rfl))
  let sx (i) := jr (atPoint Y i) (Or.inr (Y i).property)
  let tx (i) : Region d R := ⟨(A i).val,(mem_vertices _ _ _).mpr (Or.inr (A i).property)⟩
  obtain ⟨i,j,rigid⟩ := base
  have nameA (i j) : c (atPoint Y i) (atPoint Y j)=d (A i).val (A j).val :=
    he (jl _ (Or.inr (Y i).property)) (jl _ (Or.inr (Y j).property))
  obtain ⟨f,fi,fj,hf⟩ := realize_region_pair p R (Finset.card_pos.mpr ⟨_,(sx i).property⟩)
    ((pair_bound S Y).trans (by decide)) (sx i) (sx j) (tx i) (tx j) (nameA i j)
  let B := Y.trans (narrow f hf (show R v from Or.inr rfl))
  let σ := A.trans B.symm
  have nameB (i j) : c (atPoint Y i) (atPoint Y j)=d (B i).val (B j).val := hf (sx i) (sx j)
  have fix (k) (hk : f (sx k)=tx k) : σ k=k :=
    B.injective (by rw [show B (σ k)=A k from B.apply_symm_apply _]; exact Subtype.ext (congrArg Subtype.val hk).symm)
  have all := rigid σ (fix i fi) (fix j fj) (fun x y => (nameA x y).trans (by
    have shift (z) : B (σ z)=A z := B.apply_symm_apply _
    simpa only [shift] using (nameB (σ x) (σ y)).symm))
  have agree (x : Fin n) (tag : c x x=v) :
      (e (jl x (Or.inr tag))).val=(f (jr x (Or.inr tag))).val := by
    let k := Y.symm ⟨x,tag⟩
    have h : (A k).val=(B k).val := congrArg Subtype.val ((B.apply_symm_apply (A k)).symm.trans (congrArg B (all k)))
    change (e (jl (atPoint Y k) (Or.inr (Y k).property))).val=(f (jr (atPoint Y k) (Or.inr (Y k).property))).val at h
    simpa only [k,atPoint,Equiv.apply_symm_apply] using h
  have region (x : X) : reg (c x.val x.val) := (mem_vertices _ _ _).mp x.property
  have onL (x : X) (h : c x.val x.val≠r) : L (c x.val x.val) :=
    (region x).elim Or.inl (fun hv => Or.inr (hv.resolve_left h))
  let pt (x : X) := if h : c x.val x.val=r then (f (jr x.val (Or.inl h))).val else (e (jl x.val (onL x h))).val
  have useL (x : X) (h : L (c x.val x.val)) : pt x=(e (jl x.val h)).val := by
    apply dif_neg
    exact h.elim (fun hl hr => lr (hl.symm.trans hr)) (fun hv hr => rv (hr.symm.trans hv))
  have useR (x : X) (h : R (c x.val x.val)) : pt x=(f (jr x.val h)).val := by
    rcases h with hr|hv
    · exact dif_pos hr
    · exact (useL x (Or.inr hv)).trans (agree x.val hv)
  have diag (x : X) : c x.val x.val=d (pt x) (pt x) := by
    by_cases h : c x.val x.val=r
    · rw [useR x (Or.inl h)]; exact hf (jr x.val (Or.inl h)) (jr x.val (Or.inl h))
    · rw [useL x (onL x h)]; exact he (jl x.val (onL x h)) (jl x.val (onL x h))
  have uniform' (x y : Fin n) (hx : c x x=l) (hy : c y y=r) : c x y=c (atPoint F 0) (atPoint S 0) := by
    simpa only [atPoint,Equiv.apply_symm_apply] using uniform (F.symm ⟨x,hx⟩) (S.symm ⟨y,hy⟩)
  have cross (x y : X) (hx : c x.val x.val=l) (hy : c y.val y.val=r) : c x.val y.val=d (pt x) (pt y) := by
    obtain ⟨a,b,hit⟩ := StrategyColors.exists_source p (pt x) (pt y)
    have eq := (associated p).mpr (StrategyColors.maps_support p hit)
    obtain ⟨ha,hb⟩ := SmallShore.endpoints p eq
    exact (uniform' _ _ hx hy).trans ((uniform' _ _ (ha.trans ((diag x).symm.trans hx)) (hb.trans ((diag y).symm.trans hy))).symm.trans eq)
  have names (x y : X) : c x.val y.val=d (pt x) (pt y) := by
    have localL (hx : L (c x.val x.val)) (hy : L (c y.val y.val)) : c x.val y.val=d (pt x) (pt y) := by
      rw [useL x hx,useL y hy]; exact he (jl x.val hx) (jl y.val hy)
    have localR (hx : R (c x.val x.val)) (hy : R (c y.val y.val)) : c x.val y.val=d (pt x) (pt y) := by
      rw [useR x hx,useR y hy]; exact hf (jr x.val hx) (jr y.val hy)
    rcases region x with hl|hr|hv <;> rcases region y with hl'|hr'|hv'
    · exact localL (Or.inl hl) (Or.inl hl')
    · exact cross _ _ hl hr'
    · exact localL (Or.inl hl) (Or.inr hv')
    · exact common_transpose p (cross _ _ hl' hr)
    · exact localR (Or.inl hr) (Or.inl hr')
    · exact localR (Or.inl hr) (Or.inr hv')
    · exact localL (Or.inr hv) (Or.inl hl')
    · exact localR (Or.inr hv) (Or.inl hr')
    · exact localL (Or.inr hv) (Or.inr hv')
  obtain ⟨e,pt_eq⟩ := bundle p reg pt names
  exact ⟨e,fun i j => by rw [pt_eq,pt_eq]; exact names i j⟩

end QGI.Coherent.RegionalTwoAnchor
