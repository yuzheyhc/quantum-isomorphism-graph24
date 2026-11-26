import SixTenCoordinates
import SixTenCrossNormal
import TwoShoreRealization
import SixTenDesignBridge

noncomputable section
namespace QGI.Coherent.SixTenGraphs
open SixTenCoordinates Relations StrategyColorLaws
open QGI.SixTen

private def named {c l r} (f : Frame c l r) : TwoShore.Named c 6 10 l r :=
  ⟨f.e,f.left_iff,f.right_iff⟩

private theorem twins_split {c l r} (f : Frame c l r) {v w : Nat}
    (two : ∀ i j, cross f i j = v ∨ cross f i j = w)
    {s : Equiv.Perm A} {t : Equiv.Perm B}
    (split : ∀ i j, basic f v i j = Cross.splitModel (s i) (t j)) :
    SplitRectangle.Twins (cross f) := by
  let left := fun i => decide ((s i).val < 3)
  let right := fun j => decide ((t j).val < 5)
  have eq : cross f = fun i j => if left i = right j then v else w := by
    funext i j
    have active : cross f i j = v ↔ left i = right j := by
      calc
        _ ↔ basic f v i j = true := by simp [basic]
        _ ↔ Cross.splitModel (s i) (t j) = true := by rw [split]
        _ ↔ _ := by simp [Cross.splitModel,left,right]
    by_cases h : cross f i j = v
    · rw [if_pos (active.mp h),h]
    · rw [if_neg (mt active.mpr h)]
      exact (two i j).resolve_left h
  rw [eq]
  exact SplitRectangle.twins_of_halves _ _ _ _

variable {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Dispatch the complete normalized cross census on both sides. All
non-design cases already yield a single named point isomorphism. -/
theorem reduce_to_design (p : PerfectStrategy G H K) {l r : Nat}
    (f : Frame (color (closure G)) l r) (g : Frame (targetName p) l r)
    (designCase : ∀ v w, (∀ i j, cross f i j = v ∨ cross f i j = w) →
      (∀ i j, cross g i j = v ∨ cross g i j = w) →
      ∀ (s u : Equiv.Perm A) (t z : Equiv.Perm B),
      (∀ i j, basic f v i j = Cross.design (s i) (t j)) →
      (∀ i j, basic g v i j = Cross.design (u i) (z j)) → Isomorphic G H) : Isomorphic G H := by
  have closed (h : SplitRectangle.Twins (cross f) ∨ SplitRectangle.Twins (cross g)) : Isomorphic G H := by
    obtain ⟨e,he⟩ := TwoShore.named_of_twins p (named f) (named g) 0 0 (by decide) (by decide) h
    exact TwoShore.graph_of_named p e he
  rcases uniform_or_two (sourceLaws _) f with ⟨v,hv⟩ | ⟨v,w,_,two,rows,cols⟩
  · apply closed (Or.inl ?_)
    constructor <;> intros <;> simp [hv]
  have targetTwo (i j) : cross g i j = v ∨ cross g i j = w := by
    obtain ⟨x,y,h⟩ := cross_source p f g i j
    rw [←h]; exact two x y
  obtain ⟨rs,cs,lh,rh⟩ := statistics (commonLaws p) f g v
  obtain ⟨s,t,hs⟩ := Cross.normal (basic f v) rows cols
    (fun i j k => (lh i 0 k).trans (lh j 0 k).symm)
    (fun i j k => (rh i 0 k).trans (rh j 0 k).symm)
  rcases hs with split | src
  · exact closed (Or.inl (twins_split f two split))
  obtain ⟨u,z,ht⟩ := Cross.normal (basic g v)
    (fun i => (rs 0 i).symm.trans (rows 0)) (fun j => (cs 0 j).symm.trans (cols 0))
    (fun i j k => (lh 0 i k).symm.trans (lh 0 j k))
    (fun i j k => (rh 0 i k).symm.trans (rh 0 j k))
  rcases ht with split | tgt
  · exact closed (Or.inr (twins_split g targetTwo split))
  · exact designCase v w two targetTwo s u t z src tgt

/-- Any commuting perfect isomorphism strategy with coherent fiber
sizes six and ten on the source already has a classical point map. -/
theorem isomorphic_of_six_and_ten (six : ∃ x, (fiber G x).card = 6)
    (ten : ∃ x, (fiber G x).card = 10) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,g,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  obtain ⟨l,r,⟨f⟩,⟨t⟩⟩ := paired p six ten
  exact reduce_to_design p f t (SixTenDesignBridge.isomorphic p f t)

end QGI.Coherent.SixTenGraphs
