import NineNineRegion
import NineNineGeometry

noncomputable section
namespace QGI.Coherent.NineNineMain
open QGI.NineNine QGI.NineNine.Checks
open BareLex (V rows transpose)
open SixTenCoordinates (Shore atPoint Block Laws)
open SmallUnion SmallFiberExtension StrategyColorLaws NineNineGeometry
open FourTwelveFunctional (source)
open private small_map uniform_merge bundle convert_real from SmallFiberExtension
open private disjoint_degrees from FiberRectangles

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

private theorem one {a b} (A : Shore (source G) a V) (Y : Shore (source G) b V)
    (thin : Thin (cell A Y)) : Realizes p (fun t => t=a ∨ t=b) :=
  SixSixRegion.thin_extend p (fun t => t=a) rfl A Y thin (small_map p _ (by rw [SixSixCycle.size A]; decide))

private theorem pappus_case {a b v : Nat} (ab : a≠b) (A : Shore (source G) a V) (Y : Shore (source G) b V)
    (src : rows (mark A Y v)=pappusRows) : Realizes p (fun t => t=a ∨ t=b) := by
  obtain ⟨e,he⟩ := diagonal_names p
  let transfer (s : Nat) := Equiv.subtypeEquiv (p:=fun i => source G i i=s)
    (q:=fun i => targetName p i i=s) e (fun i => ⟨fun h => (he i).symm.trans h,fun h => (he i).trans h⟩)
  let S := A.trans (transfer a)
  let T := Y.trans (transfer b)
  have base : FiberRectangles.degree (mark A Y v 0)=3 := by
    rw [show mark A Y v=matrix pappusRows from (matrix_rows _).symm.trans (congrArg matrix src)]
    native_decide
  have d := (marked_degree (SixTenCoordinates.commonLaws p) A Y S T v 0 0).symm.trans base
  obtain ⟨rr,cc⟩ := regular (SixTenCoordinates.targetLaws p) S T v
  rcases NineNineRegion.classify_color (SixTenCoordinates.targetLaws p) S T v 3 (Or.inr (Or.inl rfl))
      (fun i => (rr i).trans d) (fun j => (cc j).trans d) with thin|⟨r,t,choice⟩
  · exact one p A Y (pull_thin (SixTenCoordinates.commonLaws p) A Y S T thin)
  · rcases choice with h|h
    · exact pappus p ab A Y (r.trans S) (t.trans T) src h
    · exact (different (SixTenCoordinates.commonLaws p) A Y (r.trans S) (t.trans T) v src h).elim

private theorem rect_tags {c : Table n} {a b v : Nat} (A : Shore c a V) (Y : Shore c b V)
    (e f : Equiv.Perm V) (shape : rows (mark (e.trans A) (f.trans Y) v)=rectangleRows) :
    ∀ i j, cell A Y i j=v ↔ Partition.tag (e.symm i)=Partition.tag (f.symm j) := by
  have spec : ∀ i j, matrix rectangleRows i j=true ↔ Partition.tag i=Partition.tag j := by native_decide
  have id := (matrix_rows _).symm.trans (congrArg matrix shape)
  intro i j
  obtain ⟨i,rfl⟩ := e.surjective i
  obtain ⟨j,rfl⟩ := f.surjective j
  simp only [Equiv.symm_apply_apply]
  exact (show cell A Y (e i) (f j)=v ↔ mark (e.trans A) (f.trans Y) v i j=true from ⟨decide_eq_true,of_decide_eq_true⟩).trans
    ((show mark (e.trans A) (f.trans Y) v i j=true ↔ matrix rectangleRows i j=true by rw [id]).trans (spec i j))

private theorem rect_case {a b u : Nat} (A : Shore (source G) a V) (Y : Shore (source G) b V)
    (first : rows (mark A Y u)=rectangleRows)
    (other : ∀ v i j, cell A Y i j=v → FiberRectangles.degree (mark A Y v i)≤4 →
      ∃ e f : Equiv.Perm V, rows (mark (e.trans A) (f.trans Y) v)=rectangleRows) :
    Realizes p (fun t => t=a ∨ t=b) := by
  let tag := Partition.tag
  have marked (i j : V) : cell A Y i j=u ↔ tag i=tag j :=
    rect_tags A Y (Equiv.refl V) (Equiv.refl V) first i j
  have transport (v : Nat) (i j k : V) (hit : cell A Y i j=v) (small : FiberRectangles.degree (mark A Y v i)≤4)
      (same : tag j=tag k) : cell A Y i k=v := by
    by_cases uv : u=v
    · rw [←uv] at hit ⊢; exact (marked _ _).mpr (((marked _ _).mp hit).trans same)
    obtain ⟨e,f,hw⟩ := other v i j hit small
    have block := rect_tags A Y e f hw
    have three (t : Fin 3) : (Finset.univ.filter fun h : V => tag (f.symm h)=t).card=3 := by
      let p : V → Prop := fun h => tag h=t
      have eq := Fintype.card_congr (Equiv.subtypeEquiv (p:=fun h => tag (f.symm h)=t) (q:=p) f.symm (fun _ => Iff.rfl))
      simpa only [Fintype.card_subtype,p] using eq.trans (by simpa only [Fintype.card_subtype,p] using Partition.three_each t)
    have cols := Partition.compatible (SixTenCoordinates.sourceLaws (closure G)) A Y uv marked
      (tag ∘ e.symm) (tag ∘ f.symm) (Partition.onto.comp e.symm.surjective) three block
    exact (block _ _).mpr (((block _ _).mp hit).trans (cols j k same))
  have stable (i j k : V) (same : tag j=tag k) : cell A Y i j=cell A Y i k := by
    by_cases neq : cell A Y i j=cell A Y i k
    · exact neq
    have h := disjoint_degrees (cell A Y i) neq
    change FiberRectangles.degree (mark A Y (cell A Y i j) i) +
      FiberRectangles.degree (mark A Y (cell A Y i k) i) ≤ 9 at h
    by_cases low : FiberRectangles.degree (mark A Y (cell A Y i j) i) ≤4
    · exact (transport _ _ j k rfl low same).symm
    · exact transport _ _ k j rfl (by omega) same.symm
  let L := SixSixCycle.regEquiv A
  let R := SixSixCycle.regEquiv Y
  apply ThreeRectangleExtension.three p (v:=u) (by rw [SixSixCycle.size Y]; decide) (tag ∘ L.symm) (tag ∘ R.symm)
    (Partition.onto.comp L.symm.surjective) (Partition.onto.comp R.symm.surjective) _ _
    (small_map p _ (by rw [SixSixCycle.size A]; decide))
  · intro i j
    obtain ⟨i,rfl⟩ := L.surjective i
    obtain ⟨j,rfl⟩ := R.surjective j
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using marked i j
  · intro j k same i
    obtain ⟨i,rfl⟩ := L.surjective i
    obtain ⟨j,rfl⟩ := R.surjective j
    obtain ⟨k,rfl⟩ := R.surjective k
    exact stable i j k (by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using same)

theorem realize {a b : Nat} (A : Shore (source G) a V) (Y : Shore (source G) b V) (ab : a≠b) :
    Realizes p (fun t => t=a ∨ t=b) := by
  classical
  by_cases thin : ∃ (L : Shore (source G) a V) (R : Shore (source G) b V), Thin (cell L R)
  · obtain ⟨L,R,h⟩ := thin; exact one p L R h
  by_cases pp : ∃ (L : Shore (source G) a V) (R : Shore (source G) b V) (v : Nat), rows (mark L R v)=pappusRows
  · obtain ⟨L,R,v,h⟩ := pp; exact pappus_case p ab L R h
  have other (L : Shore (source G) a V) (R : Shore (source G) b V) (v : Nat) (i j : V)
      (hit : cell L R i j=v) (bound : FiberRectangles.degree (mark L R v i) ≤4) :
      ∃ e f : Equiv.Perm V, rows (mark (e.trans L) (f.trans R) v)=rectangleRows := by
    let d := FiberRectangles.degree (mark L R v 0)
    obtain ⟨rr,cc⟩ := regular (SixTenCoordinates.sourceLaws (closure G)) L R v
    have pos : 0<FiberRectangles.degree (mark L R v i) :=
      Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true hit⟩⟩
    have n1 : d≠1 := fun one => thin ⟨L,R,thin_of_degree (i:=0) one⟩
    have r0 : FiberRectangles.degree (mark L R v i)=d := rr i
    rcases NineNineRegion.classify_color (SixTenCoordinates.sourceLaws (closure G)) L R v d
      (by omega) rr cc with h|⟨e,f,h|h⟩
    · exact (thin ⟨L,R,h⟩).elim
    · exact (pp ⟨_,_,v,h⟩).elim
    · exact ⟨e,f,h⟩
  by_cases equal : ∀ i j x y, cell A Y i j=cell A Y x y
  · obtain ⟨e,he⟩ := small_map p (fun t => t=a) (by rw [SixSixCycle.size A]; decide)
    obtain ⟨g,hg⟩ := small_map p (fun t => t=b) (by rw [SixSixCycle.size Y]; decide)
    obtain ⟨f,hf,_⟩ := uniform_merge p (fun t => t=a) b e he g hg (by
      intro i j x y hi hj hx hy
      obtain ⟨x,rfl⟩ := SixSixCycle.point A (hx.trans hi)
      obtain ⟨i,rfl⟩ := SixSixCycle.point A hi
      obtain ⟨j,rfl⟩ := SixSixCycle.point Y hj
      obtain ⟨y,rfl⟩ := SixSixCycle.point Y hy
      exact equal _ _ _ _)
    obtain ⟨q,hq⟩ := bundle p _ f hf
    exact ⟨q,fun i j => (hf i j).trans (congrArg₂ (targetName p) (hq i).symm (hq j).symm)⟩
  push_neg at equal
  obtain ⟨i,j,x,y,diff⟩ := equal
  let u := cell A Y i j
  let v := cell A Y x y
  have limit := disjoint_degrees (cell A Y i) diff
  have reg := (regular (SixTenCoordinates.sourceLaws (closure G)) A Y v).1
  have common : FiberRectangles.degree (mark A Y v i)=FiberRectangles.degree (mark A Y v x) := (reg i).trans (reg x).symm
  change FiberRectangles.degree (mark A Y u i)+FiberRectangles.degree (mark A Y v i)≤9 at limit
  have existsRect : ∃ (L : Shore (source G) a V) (R : Shore (source G) b V) (w : Nat), rows (mark L R w)=rectangleRows := by
    by_cases low : FiberRectangles.degree (mark A Y u i)≤4
    · obtain ⟨e,f,h⟩ := other A Y u i j rfl low; exact ⟨_,_,u,h⟩
    · obtain ⟨e,f,h⟩ := other A Y v x y rfl (by omega); exact ⟨_,_,v,h⟩
  obtain ⟨L,R,w,h⟩ := existsRect
  exact rect_case p L R h (other L R)

/-- A named region consisting of eighteen vertices in nine-point fibers. -/
theorem realize_of_size (reg : Nat → Prop) (total : (vertices (source G) reg).card=18)
    (nine : ∀ t, reg t → (vertices (source G) (fun w => w=t)).card=9) : Realizes p reg := by
  classical
  let c := source G
  let d := fun i : Fin n => c i i
  let names := (vertices c reg).image d
  have mem (v : Nat) : v∈names ↔ reg v := by
    constructor
    · rintro hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      exact (mem_vertices _ _ _).mp hi
    · intro hv
      have pos : 0 < (vertices c (fun w => w=v)).card := by rw [nine v hv]; decide
      obtain ⟨i,hi⟩ := Finset.card_pos.mp pos
      have eq := (mem_vertices _ _ _).mp hi
      exact Finset.mem_image.mpr ⟨i,(mem_vertices _ _ _).mpr (eq ▸ hv),eq⟩
  have bound := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) names d
  have nineAt (v) (hv : v∈names) : (Finset.univ.filter (fun i => d i=v)).card=9 := by
    have eq : Finset.univ.filter (fun i => d i=v) = vertices c (fun w => w=v) := by
      ext i; simp [d]
    rw [eq]; exact nine v ((mem v).mp hv)
  have all : (Finset.univ.filter (fun i => d i∈names)) = vertices c reg := by
    ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_vertices,mem,d]
  rw [all,total,Finset.sum_congr rfl nineAt] at bound
  simp only [Finset.sum_const,smul_eq_mul] at bound
  have sz : names.card=2 := by omega
  obtain ⟨a,b,ab,namesEq⟩ := Finset.card_eq_two.mp sz
  have within (w : Nat) : (w=a ∨ w=b) ↔ reg w := by
    rw [←mem,namesEq]; simp only [Finset.mem_insert,Finset.mem_singleton]
  have frame (v) (hv : reg v) : Nonempty (Shore c v V) := by
    let m := Fintype.equivOfCardEq (show Fintype.card V=Fintype.card (Region c (fun w => w=v)) by
      rw [Fintype.card_fin,Fintype.card_coe,nine v hv])
    exact ⟨m.trans (Equiv.subtypeEquivRight (fun i => mem_vertices c (fun t => t=v) i))⟩
  obtain ⟨A⟩ := frame a ((within _).mp (Or.inl rfl))
  obtain ⟨B⟩ := frame b ((within _).mp (Or.inr rfl))

  exact convert_real p within (realize p A B ab)

open LargeFourteenRegion CoprimeProfiles
open private card_core from LargeFourteenRegion

/-- Any ambient order with exactly two nine-point fibers after removing
all fibers of size at most three. This includes the profile [9,9] at order eighteen. -/
theorem isomorphic {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (shape : xs.filter (fun k => 3<k)=[9,9]) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,gn,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gn
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  have total : (vertices (source G) (large G)).card=18 := by rw [card_core P,shape]; decide
  have nine (v : Nat) (hv : large G v) : (vertices (source G) (fun w => w=v)).card=9 := by
    have pos : 0 < (vertices (source G) (fun w => w=v)).card := (by decide : 0<3).trans hv
    obtain ⟨i,hi⟩ := Finset.card_pos.mp pos
    have eq := (mem_vertices _ _ _).mp hi
    have same : vertices (source G) (fun w => w=v)=fiber G i := by
      ext j; simp only [mem_vertices,FourTwelveFunctional.fiber_eq,eq]
    have occurs : (fiber G i).card ∈ xs := by rw [P.fiber_size]; exact List.getElem_mem _
    have big : 3<(fiber G i).card := (LargeOrderBlocks.large_iff _).mp (eq ▸ hv)
    have mem : (fiber G i).card ∈ xs.filter (fun k => 3<k) := List.mem_filter.mpr ⟨occurs,decide_eq_true big⟩
    rw [same]
    simpa only [shape,List.mem_cons,List.not_mem_nil,or_false,or_self] using mem
  obtain ⟨e,he⟩ := of_large_region p (realize_of_size p (large G) total nine)
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩⟩


end QGI.Coherent.NineNineMain



