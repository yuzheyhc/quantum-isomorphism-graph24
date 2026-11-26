import RegionalFourTwelveGeometry
import RegionalFourFourEight

noncomputable section
namespace QGI.Coherent.RegionalCycleExtension
open Relations StrategyColorLaws SixTenCoordinates FourEightGeometry FourTwelveCycle SmallUnion SmallFiberExtension
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

def emb {l k : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l (Fin k)) : Fin k ↪ Fin n :=
  F.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩

theorem range_emb {l k : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l (Fin k)) (z) :
    z∈Set.range (emb F) ↔ c z z=l :=
  ⟨fun ⟨i,h⟩ => h ▸ (F i).property,fun h => ⟨F.symm ⟨z,h⟩,congrArg Subtype.val (F.apply_symm_apply _)⟩⟩

theorem edges {l v : Nat} (F : Shore (source G) l L) (Y : Shore (source G) v Eight)
    (t w : Nat) (palette : ∀ i j, source G (atPoint F i) (atPoint Y j)=t ∨ source G (atPoint F i) (atPoint Y j)=w)
    (b : Eight → Edge) (cells : ∀ i j, source G (atPoint F i) (atPoint Y j)=t ↔ i∈edge (b j))
    (C : RepeatedCycle b) :
    let sl := C.points.toEmbedding.trans (emb F)
    ∃ a z, a≠z ∧ (∀ j, neighbors (source G) a (atPoint Y j)=(edge (cycle (C.label j))).map sl) ∧
       ∀ j i, source G (atPoint Y j) (sl i)=if i∈edge (cycle (C.label j)) then a else z := by
  classical
  let c := source G
  let sl := C.points.toEmbedding.trans (emb F)
  have mark (i j) : c (sl i) (atPoint Y j)=t ↔ i∈edge (cycle (C.label j)) := by
    change source G (atPoint F (C.points i)) (atPoint Y j)=t ↔ _
    rw [cells,C.edges]
    exact Finset.mem_map' C.points.toEmbedding
  have slots : ∀ k : Fin 4, ∃ i x : Fin 4, i∈edge (cycle k) ∧ x∉edge (cycle k) := by decide
  obtain ⟨i₀,x₀,yes,no⟩ := slots (C.label 0)
  have active := (mark i₀ 0).mpr yes
  have neg := mt (mark x₀ 0).mp no
  have other := (palette (C.points x₀) 0).resolve_left neg
  let a := c (atPoint Y 0) (sl i₀)
  let z := c (atPoint Y 0) (sl x₀)
  have az : a≠z := fun h => neg ((transpose (closure G) h).symm.trans active)
  have names (j i) : c (atPoint Y j) (sl i)=if i∈edge (cycle (C.label j)) then a else z := by
    by_cases h : i∈edge (cycle (C.label j))
    · rw [if_pos h]; exact transpose (closure G) (((mark i j).mpr h).trans active.symm)
    · rw [if_neg h]; exact transpose (closure G) (((palette (C.points i) j).resolve_left (mt (mark i j).mp h)).trans other.symm)
  refine ⟨a,z,az,fun j => ?_,names⟩
  ext x
  constructor
  · intro hx
    have hit := (Finset.mem_filter.mp hx).2
    have tag := (end_colors (closure G) hit).2.trans (F (C.points i₀)).property
    obtain ⟨i,hi⟩ := (range_emb F x).mpr tag
    obtain ⟨i,rfl⟩ := C.points.surjective i
    have loc : sl i=x := hi
    have body : c (atPoint Y j) (sl i)=a := loc ▸ hit
    rw [names] at body
    by_cases h : i∈edge (cycle (C.label j))
    · exact Finset.mem_map.mpr ⟨i,h,loc⟩
    · exact (az (by simpa [h] using body.symm)).elim
  · rintro hx; obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(names j i).trans (if_pos hi)⟩

/-- Attach the four-point shore of a doubled cycle to a named exterior
bijection. A further shore with a monochromatic cross relation adds no
restriction on the cycle coordinates. -/
theorem attach_to {l v m : Nat} (F : Shore (source G) l L) (Y : Shore (source G) v (Fin m))
    (keep reg : Nat → Prop) (inside : keep v)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ keep (source G i i)) (old : Realizes p keep)
    (flat : ∀ i j u w : Fin n, source G i i=l → keep (source G j j) → source G j j≠v →
      source G u u=l → source G w w=source G j j → source G i j=source G u w)
    (points : Equiv.Perm L) (label : Fin m → Fin 4) (full : Function.Surjective label)
    (a z : Nat) (az : a≠z)
    (rows : ∀ j, neighbors (source G) a (atPoint Y j)=(edge (cycle (label j))).map (points.toEmbedding.trans (emb F)))
    (names : ∀ j i, source G (atPoint Y j) (atPoint F (points i))=if i∈edge (cycle (label j)) then a else z) :
    Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  obtain ⟨e,he⟩ := old
  let extPt (x : Fin n) (h : keep (c x x)) : Region c keep := ⟨x,(mem_vertices _ _ _).mpr h⟩
  let atY (j : (Fin m)) := extPt (atPoint Y j) ((congrArg keep (Y j).property).mpr inside)
  let Z : (Fin m) ↪ Fin n := ⟨fun j => (e (atY j)).val,fun i j h =>
    (emb Y).injective (congrArg (fun x : Region c keep => x.val) (e.injective (Subtype.ext h)))⟩
  obtain ⟨m,hm⟩ := diagonal_names p
  let T : Shore d l L := F.trans (Equiv.subtypeEquiv m (fun x => ⟨fun h => (hm x).symm.trans h,fun h => (hm x).trans h⟩))
  let sl := points.toEmbedding.trans (emb F)
  have rangeS (x) : x∈Set.range sl ↔ c x x=l := by
    refine Iff.trans ?_ (range_emb F x)
    exact ⟨fun ⟨i,h⟩ => ⟨points i,h⟩,fun ⟨i,h⟩ => ⟨points.symm i,by simpa [sl] using h⟩⟩
  obtain ⟨h,internal,across⟩ := RegionalFourTwelve.cycle_named p az sl (emb T) (emb Y) Z rangeS (range_emb T)
    (fun i j => he (atY i) (atY j)) label full rows names
  let X := Region c reg
  have outside (x : X) (nx : c x.val x.val≠l) : keep (c x.val x.val) :=
    (cover x.val ((mem_vertices _ _ _).mp x.property)).resolve_left nx
  let idx (x : Fin n) (hl : c x x=l) := points.symm (F.symm ⟨x,hl⟩)
  have locate (x hl) : sl (idx x hl)=x := by simp [sl,idx,emb]
  let pt (x : X) := if hl : c x.val x.val=l then emb T (h (idx x.val hl)) else (e (extPt x.val (outside x hl))).val
  have basePt (x : X) (hx : c x.val x.val=l) : pt x=emb T (h (idx x.val hx)) := dif_pos hx
  have oldPt (x : X) (hx : c x.val x.val≠l) : pt x=(e (extPt x.val (outside x hx))).val := dif_neg hx
  have oldName (x y : X) (hx : c x.val x.val≠l) (hy : c y.val y.val≠l) : c x.val y.val=d (pt x) (pt y) := by
    rw [oldPt x hx,oldPt y hy]; exact he (extPt x.val (outside x hx)) (extPt y.val (outside y hy))
  have cross (x y : X) (hx : c x.val x.val=l) (hy : c y.val y.val≠l) : c x.val y.val=d (pt x) (pt y) := by
    by_cases hv : c y.val y.val≠v
    · obtain ⟨u,w,hit⟩ := StrategyColors.exists_source p (pt x) (pt y)
      have eq := (associated p).mpr (StrategyColors.maps_support p hit)
      obtain ⟨a,b⟩ := SmallShore.endpoints p eq
      rw [basePt x hx] at a
      exact (flat _ _ _ _ hx (outside y hy) hv (a.trans (T _).property) (b.trans (oldName y y hy hy).symm)).trans eq
    · obtain ⟨j,hj⟩ := (range_emb Y y.val).mpr (not_not.mp hv)
      have rel := common_transpose p (across j (idx x.val hx))
      rw [show sl (idx x.val hx)=x.val from locate _ _,hj] at rel
      rw [basePt x hx,oldPt y hy]
      convert rel using 2
      exact congrArg (fun u : Region c keep => (e u).val) (Subtype.ext hj.symm)
  have all (x y : X) : c x.val y.val=d (pt x) (pt y) := by
    by_cases hx : c x.val x.val=l <;> by_cases hy : c y.val y.val=l
    · rw [basePt x hx,basePt y hy]
      simpa only [locate] using internal (idx x.val hx) (idx y.val hy)
    · exact cross x y hx hy
    · exact common_transpose p (cross y x hy hx)
    · exact oldName _ _ hx hy
  obtain ⟨g,hg⟩ := bundle p reg pt all
  exact ⟨g,fun i j => by rw [hg,hg]; exact all i j⟩

theorem attach_mapped {l r v m : Nat} (lr : l≠r) (lv : l≠v) (F : Shore (source G) l L)
    (Y : Shore (source G) v (Fin m)) (z₀ : Fin n) (hz : source G z₀ z₀=r)
    (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v)
    (old : Realizes p (fun t => t=r ∨ t=v))
    (uniform : ∀ i x, source G x x=r → source G (atPoint F i) x = source G (atPoint F 0) z₀)
    (points : Equiv.Perm L) (label : Fin m → Fin 4) (full : Function.Surjective label)
    (a z : Nat) (az : a≠z)
    (rows : ∀ j, neighbors (source G) a (atPoint Y j)=(edge (cycle (label j))).map (points.toEmbedding.trans (emb F)))
    (names : ∀ j i, source G (atPoint Y j) (atPoint F (points i))=if i∈edge (cycle (label j)) then a else z) :
    Realizes p reg := by
  apply attach_to p F Y (fun s => s=r ∨ s=v) reg (Or.inr rfl) cover old _ points label full a z az rows names
  intro i j u w hi hj nv hu hw
  have hs := hj.resolve_right nv
  have same (x y : Fin n) (hx : source G x x=l) (hy : source G y y=r) :
      source G x y=source G (atPoint F 0) z₀ := by
    simpa only [atPoint,Equiv.apply_symm_apply] using uniform (F.symm ⟨x,hx⟩) y hy
  exact (same i j hi hs).trans (same u w hu (hw.trans hs)).symm

theorem attach {l r v : Nat} (lr : l≠r) (lv : l≠v) (F : Shore (source G) l L)
    (Y : Shore (source G) v Eight) (z₀ : Fin n) (hz : source G z₀ z₀=r)
    (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v)
    (old : Realizes p (fun t => t=r ∨ t=v))
    (uniform : ∀ i x, source G x x=r → source G (atPoint F i) x = source G (atPoint F 0) z₀)
    (t w : Nat) (pal : ∀ i j, source G (atPoint F i) (atPoint Y j)=t ∨ source G (atPoint F i) (atPoint Y j)=w)
    (b : Eight → Edge) (cells : ∀ i j, source G (atPoint F i) (atPoint Y j)=t ↔ i∈edge (b j)) (C : RepeatedCycle b) :
    Realizes p reg := by
  obtain ⟨a,z,az,rows,names⟩ := edges F Y t w pal b cells C
  have full (k) : ∃ i, C.label i=k := by
    obtain ⟨j,mem⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun i => C.label i=k)).card by rw [C.twice]; decide)
    exact ⟨j,(Finset.mem_filter.mp mem).2⟩
  exact attach_mapped p lr lv F Y z₀ hz reg cover old uniform C.points C.label full a z az rows names

end QGI.Coherent.RegionalCycleExtension
