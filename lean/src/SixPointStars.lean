import RegionalSixTwelveGeometry

namespace QGI.Coherent.RegionalSixTwelveGeometry
open private check sound pool from RegionalSixTwelveGeometry

private def fiveStar (f : Family) : Bool := if f.card=5 then
  if ∀ a∈f, ∀ b∈f, (a∩b).Nonempty then decide (∃ i : Point, ∀ a∈f, i∈a) else true else true

private theorem checked : check fiveStar ∅ (pool 2)=true := by native_decide

theorem star_center_many (f : Family) (weights : ∀ a∈f, a.card=2)
    (size : (f.card=2 ∨ f.card=4) ∨ f.card=5) (overlap : ∀ a∈f, ∀ b∈f, (a∩b).Nonempty) :
    ∃ i : Point, ∀ a∈f, i∈a := by
  rcases size with old|five
  · exact star_center f weights old overlap
  · simpa only [fiveStar,if_pos five,if_pos overlap,decide_eq_true_eq] using sound fiveStar checked f weights

theorem determines_more (f : Family) (weights : ∀ s∈f, s.card=2)
    (size : (f.card=6 ∨ f.card=12) ∨ f.card=15) (regular : Regular f) : Determines f := by
  rcases size with old|all
  · exact determines_of_edges f weights old regular
  have eq : f=blocks 2 := Finset.eq_of_subset_of_card_le
    (fun s hs => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,weights s hs⟩)
    ((by native_decide : (blocks 2).card=15).trans all.symm).le
  rw [eq]
  native_decide

end QGI.Coherent.RegionalSixTwelveGeometry
