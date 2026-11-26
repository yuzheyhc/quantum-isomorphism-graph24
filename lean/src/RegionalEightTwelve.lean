import RegionalEightTwelveComponents
import RegionalEightTwelveRepeated
import RegionalEightTwelveGrid

noncomputable section
namespace QGI.Coherent.RegionalEightTwelve
open SmallUnion SmallFiberExtension StrategyColorLaws SixTenCoordinates RegionalEightTwelveGeometry RegionalEightTwelveStats
open RegionalEightTwelvePartitions (Split)
open FourTwelveFunctional (source)
open private twins from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

private theorem disjoint {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index)
    (j) {s t : Nat} (diff : s≠t) : Disjoint (family F Y s j) (family F Y t j) :=
  Finset.disjoint_left.mpr fun _ h k => diff ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp k).2)

private theorem repeated_shape {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index)
    (weight : (family F Y v 0).card=2) (dup : ¬Function.Injective (family F Y v)) : Nonempty (Split (family F Y v)) := by
  have d := degrees (sourceLaws (closure G)) F Y v
  have sum := d.2.2
  rw [weight] at sum
  exact RegionalEightTwelvePartitions.split_repeated _ (fun j => (d.1 j).trans weight) (fun i => (d.2.1 i).trans (by omega))
    (uniform_copies (sourceLaws (closure G)) F Y v) dup

/-- Every named 8 × 12 interface with a genuine degree-two color realizes the
region. Other cross colors and all directed internal names may be arbitrarily refined. -/
theorem of_degree_two {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (weight : (family F Y v 0).card=2) : Realizes p reg := by
  classical
  by_cases simple : Function.Injective (family F Y v)
  · exact of_simple p F Y reg cover weight simple
  obtain ⟨S⟩ := repeated_shape F Y weight simple
  by_cases constant : ∀ i j k, S.column j=S.column k → color F Y j i=color F Y k i
  · exact of_common_triples p F Y reg cover S constant
  push_neg at constant
  obtain ⟨i,j,k,same,diff⟩ := constant
  let x := color F Y j i
  let y := color F Y k i
  have xy : x≠y := diff
  have vx : v≠x := by
    intro eq
    have h := (S.pair j i).mp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq.symm⟩)
    exact diff (eq.symm.trans (Finset.mem_filter.mp ((S.pair k i).mpr (h.trans same))).2.symm)
  have vy : v≠y := by
    intro eq
    have h := (S.pair k i).mp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq.symm⟩)
    exact diff ((Finset.mem_filter.mp ((S.pair j i).mpr (h.trans same.symm))).2.trans eq)
  have choices (t : Index) : (family F Y (color F Y t i) 0).card=2 ∨ 4≤(family F Y (color F Y t i) 0).card := by
    let u := color F Y t i
    have d := degrees (sourceLaws (closure G)) F Y u
    have hu := Finset.card_pos.mpr (show (family F Y u t).Nonempty from ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩)
    have eq := d.1 t
    have sum := d.2.2
    change (family F Y u 0).card=2 ∨ 4≤(family F Y u 0).card
    omega
  have cap := Finset.card_le_univ ((family F Y v 0∪family F Y x 0)∪family F Y y 0)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disjoint F Y _ vy,disjoint F Y _ xy⟩),
    Finset.card_union_of_disjoint (disjoint F Y _ vx),Fintype.card_fin,weight] at cap
  have kind : (family F Y x 0).card=2 ∨ (family F Y y 0).card=2 := by
    have a := choices j; have b := choices k
    change (family F Y x 0).card=2 ∨ 4≤(family F Y x 0).card at a
    change (family F Y y 0).card=2 ∨ 4≤(family F Y y 0).card at b
    omega
  have other : ∃ w t u, (family F Y w 0).card=2 ∧ S.column t=S.column u ∧ i∈family F Y w t ∧ i∉family F Y w u := by
    rcases kind with xTwo|yTwo
    · exact ⟨x,j,k,xTwo,same,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,fun hit => xy (Finset.mem_filter.mp hit).2.symm⟩
    · exact ⟨y,k,j,yTwo,same.symm,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,fun hit => xy (Finset.mem_filter.mp hit).2⟩
  obtain ⟨w,t,u,ww,eq,hit,miss⟩ := other
  by_cases plain : Function.Injective (family F Y w)
  · exact of_simple p F Y reg cover ww plain
  obtain ⟨D⟩ := repeated_shape F Y ww plain
  exact RegionalEightTwelveGrid.realize p F Y reg cover S D ⟨t,u,eq,fun same =>
    miss ((D.pair u i).mpr (((D.pair t i).mp hit).trans same))⟩

theorem of_twins {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (shape : SplitRectangle.Twins (color F Y)) : Realizes p reg := by
  let keep := fun k => k=l
  have old := LargeOrderBlocks.small p keep ((RegionalTwoAnchor.card F).le.trans (by decide))
  let anchor : Region (source G) keep := ⟨atPoint F 0,(mem_vertices _ _ _).mpr (F 0).property⟩
  have type : source G anchor.val anchor.val=l := (F 0).property
  have rect : FiberPairExtension.twins (source G) r (source G anchor.val anchor.val) := type ▸ twins Y F shape
  apply RegionalFourFourEight.restrict_map p (FiberPairExtension.attach p Y 0 (by decide) keep old anchor anchor
    (fun j => Or.inl (((mem_vertices _ _ _).mp j.property).trans type.symm)) rect rect) cover

theorem reduction {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) :
    Realizes p reg ∨ ∃ v w, v≠w ∧ (∀ j i, color F Y j i=v ∨ color F Y j i=w) ∧
      ∀ j, (family F Y v j).card=4 := by
  classical
  by_cases doneAlready : Realizes p reg
  · exact Or.inl doneAlready
  right
  let v := color F Y 0 0
  by_cases constant : ∀ j i, color F Y j i=v
  · exact False.elim (doneAlready (of_twins p F Y reg cover
      ⟨fun j k _ _ i => (constant j i).trans (constant k i).symm,fun _ i x _ j => (constant j i).trans (constant j x).symm⟩))
  push_neg at constant
  obtain ⟨s,t,diff⟩ := constant
  let w := color F Y s t
  have vw : v≠w := Ne.symm diff
  have ge (j i) : 4≤(family F Y (color F Y j i) 0).card := by
    let u := color F Y j i
    have st := degrees (sourceLaws (closure G)) F Y u
    have pos := Finset.card_pos.mpr (show (family F Y u j).Nonempty from ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩)
    have x := st.1 j
    have sum := st.2.2
    have ne : (family F Y u 0).card≠2 := fun h => doneAlready (of_degree_two p F Y reg cover h)
    change 4≤(family F Y u 0).card
    omega
  have a : 4≤(family F Y v 0).card := ge 0 0
  have b : 4≤(family F Y w 0).card := ge s t
  have cap := Finset.card_le_univ (family F Y v 0∪family F Y w 0)
  rw [Finset.card_union_of_disjoint (disjoint F Y _ vw),Fintype.card_fin] at cap
  have fv : (family F Y v 0).card=4 := by omega
  have fw : (family F Y w 0).card=4 := by omega
  refine ⟨v,w,vw,fun j i => ?_,fun j => ((degrees (sourceLaws _) F Y v).1 j).trans fv⟩
  have full : family F Y v j∪family F Y w j=Finset.univ := Finset.eq_univ_of_card _ (by
    rw [Finset.card_union_of_disjoint (disjoint F Y _ vw),(degrees (sourceLaws _) F Y v).1 j,
      (degrees (sourceLaws _) F Y w).1 j,fv,fw]; decide)
  have mem : i∈family F Y v j∪family F Y w j := by rw [full]; exact Finset.mem_univ i
  simpa only [family,color,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using mem

end QGI.Coherent.RegionalEightTwelve

