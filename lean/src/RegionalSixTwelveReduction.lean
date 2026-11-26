import RegionalSixTwelvePairs

noncomputable section
namespace QGI.Coherent.RegionalSixTwelve
open SixTenCoordinates SmallFiberExtension RegionalSixTwelveStats
open RegionalSixTwelveGeometry (Point)
open FourTwelveFunctional (source)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

private theorem disjoint {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right)
    (j) {s t : Nat} (diff : s≠t) : Disjoint (family F Y s j) (family F Y t j) :=
  Finset.disjoint_left.mpr fun _ h k => diff ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp k).2)

private theorem minimum {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) (no : ¬Realizes p reg) (j i) :
    2≤(family F Y (color F Y j i) j).card := by
  have pos : 0 < (family F Y (color F Y j i) j).card :=
    Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have bad : (family F Y (color F Y j i) j).card≠1 := fun h => no (of_single p F Y reg cover j i h)
  omega

/-- Every genuine relation selecting two of the six vertices per column
realizes the region, including arbitrary refinements of the complementary color. -/
theorem of_degree_two {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (weight : (family F Y v 0).card=2) : Realizes p reg := by
  classical
  by_contra no
  obtain ⟨three,_⟩ := (edge_reduction p F Y reg cover weight).resolve_left no
  by_cases const : ∀ j i x, (∀ t, i∈family F Y v t ↔ x∈family F Y v t) → color F Y j i=color F Y j x
  · exact no (of_matching p F Y reg cover weight three const)
  push_neg at const
  obtain ⟨j,i,x,similar,unequal⟩ := const
  let w := color F Y j i
  let t := color F Y j x
  have vw : v≠w := by
    intro eq
    have hi : i∈family F Y v j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq.symm⟩
    exact unequal (eq.symm.trans (Finset.mem_filter.mp ((similar j).mp hi)).2.symm)
  have vt : v≠t := by
    intro eq
    have hx : x∈family F Y v j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq.symm⟩
    exact unequal ((Finset.mem_filter.mp ((similar j).mpr hx)).2.trans eq)
  have vwSize := ((statistics (sourceLaws _) F Y v).1 j).trans weight
  have wMin := minimum p F Y reg cover no j i
  have tMin := minimum p F Y reg cover no j x
  change 2≤(family F Y w j).card at wMin
  change 2≤(family F Y t j).card at tMin
  have cap := Finset.card_le_univ ((family F Y v j∪family F Y w j)∪family F Y t j)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disjoint F Y j vt,disjoint F Y j unequal⟩),
    Finset.card_union_of_disjoint (disjoint F Y j vw),Fintype.card_fin] at cap
  have wCount : (family F Y w j).card=2 := by omega
  have w0 : (family F Y w 0).card=2 := ((statistics (sourceLaws _) F Y w).1 j).symm.trans wCount
  obtain ⟨threeW,_⟩ := (edge_reduction p F Y reg cover w0).resolve_left no
  have diff : support (family F Y v)≠support (family F Y w) := by
    intro eq
    have mem : family F Y w j∈support (family F Y v) := by
      rw [eq]
      exact Finset.mem_image_of_mem (family F Y w) (Finset.mem_univ j)
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp mem
    have iin : i∈family F Y v s := by rw [hs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    have xin := (similar s).mp iin
    rw [hs] at xin
    exact unequal (Finset.mem_filter.mp xin).2.symm
  exact no (of_two_matchings p F Y reg cover weight w0 three threeW diff)

structure TetraShape (b : Right → Cell) (u : Right → Point → Nat) (v w : Nat) : Prop where
  vw : v≠w
  palette : ∀ j i, u j i=v ∨ u j i=w
  weight : ∀ j, (b j).card=3
  four : (support b).card=4
  intersection : ∀ s∈support b, ∀ t∈support b, s≠t → (s∩t).card=1
  tripled : ∀ s∈support b, mu b s=3

private theorem tetra_of_counts {n l r v w : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l Point) (Y : Shore c r Right) (vw : v≠w)
    (palette : ∀ j i, color F Y j i=v ∨ color F Y j i=w) (wt : (family F Y v 0).card=3)
    (four : (support (family F Y v)).card=4)
    (pairs : ∀ s∈support (family F Y v), ∀ t∈support (family F Y v), s≠t → (s∩t).card=1) :
    TetraShape (family F Y v) (color F Y) v w := by
  have counts := statistics (m:=12) law F Y v
  have freq := counts.2.1
  have total := weighted (family F Y v) _ freq (fun _ => 1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,four] at total
  refine ⟨vw,palette,fun j => (counts.1 j).trans wt,four,pairs,fun s hs => ?_⟩
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
  exact (freq j).trans (by omega)

/-- The only remaining six-by-twelve geometry is the four triples of a
tetrahedron, with each of its stars occurring exactly three times. -/
theorem reduce_to_tetra {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) :
    Realizes p reg ∨ ∃ v w, TetraShape (family F Y v) (color F Y) v w := by
  classical
  by_cases doneAlready : Realizes p reg
  · exact Or.inl doneAlready
  right
  let v := color F Y 0 0
  by_cases constant : ∀ j i, color F Y j i=v
  · have rect : SplitRectangle.Twins (color F Y) :=
      ⟨fun i x _ _ y => (constant i y).trans (constant x y).symm,
       fun _ j y _ x => (constant x j).trans (constant x y).symm⟩
    exact False.elim (doneAlready (of_twins p F Y reg cover rect))
  push_neg at constant
  obtain ⟨j₀,i₀,distinct⟩ := constant
  let w := color F Y j₀ i₀
  have vw : v≠w := Ne.symm distinct
  have atLeast (j i) : 3≤(family F Y (color F Y j i) 0).card := by
    let s := color F Y j i
    have ge := minimum p F Y reg cover doneAlready j i
    have h := (statistics (sourceLaws _) F Y s).1 j
    have no : (family F Y s 0).card≠2 := fun h => doneAlready (of_degree_two p F Y reg cover h)
    change 2≤(family F Y s j).card at ge
    change 3≤(family F Y s 0).card
    omega
  have a : 3≤(family F Y v 0).card := atLeast 0 0
  have b : 3≤(family F Y w 0).card := atLeast j₀ i₀
  have cap := Finset.card_le_univ (family F Y v 0∪family F Y w 0)
  rw [Finset.card_union_of_disjoint (disjoint F Y _ vw),Fintype.card_fin] at cap
  have lens : (family F Y v 0).card=3 ∧ (family F Y w 0).card=3 := by omega
  have palette (j i) : color F Y j i=v ∨ color F Y j i=w := by
    have all : family F Y v j∪family F Y w j=Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_union_of_disjoint (disjoint F Y _ vw),(statistics (sourceLaws _) F Y v).1 j,
        (statistics (sourceLaws _) F Y w).1 j,lens.1,lens.2]; decide)
    have mem : i∈family F Y v j∪family F Y w j := by rw [all]; exact Finset.mem_univ _
    simpa only [family,color,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using mem
  have half := half_reduction (v:=v) (w:=w) p F Y reg cover vw palette lens.1
  have shape := half.resolve_left doneAlready
  exact ⟨v,w,tetra_of_counts (c:=source G) (sourceLaws (closure G)) F Y vw palette lens.1 shape.1 shape.2⟩

end QGI.Coherent.RegionalSixTwelve

