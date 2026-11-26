import RegionalSixTwelveComplete

noncomputable section
namespace QGI.Coherent.SixTwelveAlternatives
open SixTenCoordinates RegionalSixTwelve RegionalSixTwelveStats StrategyColorLaws
open RegionalSixTwelveGeometry (Point)
open FourTwelveFunctional (source)
open private disjoint tetra_of_counts from RegionalSixTwelveReduction
variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (F : Shore (source G) l Point) (Y : Shore (source G) r Right)

def Relative := ∀ (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r Right),
    (∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j)) →
    ∃ e : Equiv.Perm Point, (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
      ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i))

def Single := ∃ j i, (family F Y (color F Y j i) j).card=1

private theorem edgeCase {v : Nat} (weight : (family F Y v 0).card=2) : Relative p F Y ∨ (support (family F Y v)).card=3 := by
  let b := family F Y v
  obtain ⟨weights,_,div,regu⟩ := statistics (sourceLaws (closure G)) F Y v
  have wf (s) (hs : s∈support b) : s.card=2 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact (weights j).trans weight
  have eq := regular_degree (support b) wf regu
  change (support b).card∣12 at div
  have sizes : (support b).card=3 ∨ (support b).card=6 ∨ (support b).card=12 := by
    have bound := Nat.le_of_dvd (by decide : 0<12) div
    have pos := Finset.card_pos.mpr (show (support b).Nonempty from ⟨b 0,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    have nine : (support b).card≠9 := by intro h; rw [h] at div; norm_num at div
    omega
  rcases sizes with h|h
  · exact Or.inr h
  · exact Or.inl (fun T Z names => edge_named p F Y T Z names weight h)

private theorem lower (no : ¬ Single F Y) (j i) : 2≤(family F Y (color F Y j i) j).card := by
  have pos := Finset.card_pos.mpr (show (family F Y (color F Y j i) j).Nonempty from
    ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩)
  have bad : (family F Y (color F Y j i) j).card≠1 := fun eq => no ⟨j,i,eq⟩
  omega

private theorem two {v : Nat} (nos : ¬ Single F Y) (weight : (family F Y v 0).card=2) : Relative p F Y := by
  classical
  by_contra no
  obtain three := (edgeCase p F Y weight).resolve_left no
  by_cases const : ∀ j i x, (∀ t, i∈family F Y v t ↔ x∈family F Y v t) → color F Y j i=color F Y j x
  · exact no (fun T Z names => matching_named p F Y T Z names weight three const)
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
  have wMin := lower F Y nos j i
  have tMin := lower F Y nos j x
  change 2≤(family F Y w j).card at wMin
  change 2≤(family F Y t j).card at tMin
  have cap := Finset.card_le_univ ((family F Y v j∪family F Y w j)∪family F Y t j)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disjoint F Y j vt,disjoint F Y j unequal⟩),
    Finset.card_union_of_disjoint (disjoint F Y j vw),Fintype.card_fin] at cap
  have wCount : (family F Y w j).card=2 := by omega
  have w0 : (family F Y w 0).card=2 := ((statistics (sourceLaws _) F Y w).1 j).symm.trans wCount
  obtain threeW := (edgeCase p F Y w0).resolve_left no
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
  exact no (fun T Z names => two_matchings_named p F Y T Z names weight w0 three threeW diff)

theorem classify : Single F Y ∨ Relative p F Y ∨ SplitRectangle.Twins (color F Y) ∨
    ∃ v w, TetraShape (family F Y v) (color F Y) v w := by
  classical
  by_cases nos : Single F Y
  · exact Or.inl nos
  right
  by_cases no : Relative p F Y
  · exact Or.inl no
  right
  let v := color F Y 0 0
  by_cases constant : ∀ j i, color F Y j i=v
  · have rect : SplitRectangle.Twins (color F Y) :=
      ⟨fun i x _ _ y => (constant i y).trans (constant x y).symm,
       fun _ j y _ x => (constant x j).trans (constant x y).symm⟩
    exact Or.inl rect
  push_neg at constant
  obtain ⟨j₀,i₀,distinct⟩ := constant
  let w := color F Y j₀ i₀
  have vw : v≠w := Ne.symm distinct
  have atLeast (j i) : 3≤(family F Y (color F Y j i) 0).card := by
    let s := color F Y j i
    have ge := lower F Y nos j i
    have h := (statistics (sourceLaws _) F Y s).1 j
    have no : (family F Y s 0).card≠2 := fun h => no (two p F Y nos h)
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
  let b := family F Y v
  obtain ⟨weights,_,sz,regular⟩ := statistics (sourceLaws (closure G)) F Y v
  have len (s) (hs : s∈support b) : s.card=3 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact (weights j).trans lens.1
  rcases RegionalSixTwelveGeometry.half_shapes (support b) len sz
    ⟨b 0,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ regular (half_values (sourceLaws _) F Y vw palette) with comp|tetra
  · exact Or.inl (complementary_twins F Y vw palette comp.1 comp.2)
  · exact Or.inr ⟨v,w,tetra_of_counts (sourceLaws _) F Y vw palette lens.1 tetra.1 tetra.2⟩
end QGI.Coherent.SixTwelveAlternatives
