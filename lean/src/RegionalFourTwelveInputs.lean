import FourTwelveDispatch
import RegionalSixTen
import LargeOrderSixteen

noncomputable section
namespace QGI.Coherent.RegionalFourTwelve
open FourTwelveCycle FourTwelveTypes FourTwelveCycleGraph
open SmallUnion StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)
open private shore_range from RegionalSixTen
open private side_eq from TwoShoreRealization

def line {c : C} (f : Frame c) (s : Nat) (j : R) := Finset.univ.filter fun i => crosses f j i=s

structure Binary {c : C} (f : Frame c) where
  v : Nat
  w : Nat
  vw : v≠w
  palette : ∀ j i, crosses f j i=v ∨ crosses f j i=w
  col : R → Edge
  cells : ∀ j, edge (col j)=line f v j

theorem frame {c : C} {l r : Nat} (four : (SixTenCoordinates.named c l).card=4)
    (twelve : (SixTenCoordinates.named c r).card=12) : Nonempty (Frame c) := by
  classical
  let s := SixTenCoordinates.named c l
  let t := SixTenCoordinates.named c r
  have dl (z) : z∈s ↔ c z z=l := by simp [s,SixTenCoordinates.named]
  have dr (z) : z∈t ↔ c z z=r := by simp [t,SixTenCoordinates.named]
  have ne : l≠r := by rintro rfl; omega
  have comp : t=sᶜ := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; exact Finset.mem_compl.mpr (fun h => ne (((dl z).mp h).symm.trans ((dr z).mp hz)))
    · rw [Finset.card_compl,Fintype.card_fin,four,twelve]
  let left := Fintype.equivOfCardEq (show Fintype.card L=Fintype.card {z // z∈s} by rw [Fintype.card_coe,four]; rfl)
  let right := Fintype.equivOfCardEq (show Fintype.card R=Fintype.card {z : V // z∉s} by
    rw [Fintype.card_subtype_compl,Fintype.card_coe,four]; decide)
  exact ⟨⟨(Equiv.sumCongr left right).trans (Equiv.sumCompl _),l,r,ne,
    fun i => (dl _).mp (left i).property,fun i => (dr _).mp (comp ▸ Finset.mem_compl.mpr (right i).property)⟩⟩

theorem classify {c : C} (f : Frame c) (law : SixTenCoordinates.Laws c c) :
    SplitRectangle.Twins (crosses f) ∨ (∃ j i, (line f (crosses f j i) j).card=1) ∨ Nonempty (Binary f) := by
  classical
  let v := crosses f 0 0
  by_cases uniform : ∀ j i, crosses f j i=v
  · left; constructor <;> intros <;> simp [uniform]
  push_neg at uniform
  obtain ⟨j₀,i₀,diff⟩ := uniform
  let w := crosses f j₀ i₀
  have vw : v≠w := Ne.symm diff
  have const (t : Nat) (j) : (line f t j).card=(line f t 0).card := by
    simpa [line,active,FiberRectangles.degree] using (regular law f t).1 j
  by_cases one : ∃ j i, (line f (crosses f j i) j).card=1
  · exact Or.inr (Or.inl one)
  have atLeast (j : R) (i : L) : 2≤(line f (crosses f j i) 0).card := by
    have pos : 0<(line f (crosses f j i) j).card := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
    have notOne : (line f (crosses f j i) j).card≠1 := fun h => one ⟨j,i,h⟩
    have z : 2≤(line f (crosses f j i) j).card := by omega
    exact z.trans_eq (const _ j)
  have disjoint (j) : Disjoint (line f v j) (line f w j) :=
    Finset.disjoint_left.mpr fun i h k => vw (((Finset.mem_filter.mp h).2).symm.trans (Finset.mem_filter.mp k).2)
  have bound := Finset.card_le_univ (line f v 0 ∪ line f w 0)
  rw [Finset.card_union_of_disjoint (disjoint _)] at bound
  change _≤4 at bound
  have av : 2≤(line f v 0).card := atLeast 0 0
  have aw : 2≤(line f w 0).card := atLeast j₀ i₀
  have both : (line f v 0).card=2 ∧ (line f w 0).card=2 := by omega
  have palette (j i) : crosses f j i=v ∨ crosses f j i=w := by
    have eq : line f v j ∪ line f w j=Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_union_of_disjoint (disjoint _),const,const w,both.1,both.2]; decide)
    have mem : i∈line f v j ∪ line f w j := by rw [eq]; exact Finset.mem_univ i
    simpa only [Finset.mem_union,line,Finset.mem_filter,Finset.mem_univ,true_and] using mem
  have choose : ∀ s : Finset L, s.card=2 → ∃ e, edge e=s := by decide
  choose a ha using fun j => choose (line f v j) ((const v j).trans both.1)
  exact Or.inr (Or.inr ⟨⟨v,w,vw,palette,a,ha⟩⟩)

theorem matching {c : C} {f : Frame c} (B : Binary f) (e : Edge)
    (shape : ∀ j, B.col j=e ∨ B.col j=opposite e) : SplitRectangle.Twins (crosses f) := by
  let a := fun j => decide (B.col j=e)
  let b := fun i => decide (i∈edge e)
  have ne : opposite e≠e := (show ∀ j, opposite j≠j by decide) e
  have pattern : crosses f = fun j i => if a j=b i then B.v else B.w := by
    funext j i
    have mem : crosses f j i=B.v ↔ i∈edge (B.col j) := by simp [B.cells,line]
    have agree : crosses f j i=B.v ↔ a j=b i := by
      rcases shape j with h|h
      · simp [mem,h,a,b]
      · simp [mem,h,ne,a,b,opposite_edge]
    by_cases h : crosses f j i=B.v
    · rw [if_pos (agree.mp h),h]
    · rw [if_neg (mt agree.mpr h)]; exact (B.palette j i).resolve_left h
  rw [pattern]; exact SplitRectangle.twins_of_halves _ _ _ _

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

set_option maxHeartbeats 1500000 in
/-- On the two whole shores the ambient strategy supplies the anchored maps
needed by the twin-rectangle extension. -/
theorem twins_named (p : PerfectStrategy G H K) (reg : Nat → Prop) (F T : V → Fin n) (D : DataFor p reg F T)
    (f : Frame (restricted (source G) F)) (g : Frame (restricted (targetName p) T)) (hl : g.l=f.l) (hr : g.r=f.r)
    (twins : SplitRectangle.Twins (crosses f)) :
    ∃ e : Equiv.Perm V, ∀ i j, source G (F i) (F j)=targetName p (T (e i)) (T (e j)) := by
  let S : TwoShore.Named (restricted (source G) F) 12 4 f.r f.l :=
    ⟨(Equiv.sumComm _ _).trans f.points,f.right_iff,f.left_iff⟩
  let W : TwoShore.Named (restricted (targetName p) T) 12 4 f.r f.l :=
    ⟨(Equiv.sumComm _ _).trans g.points,hr ▸ g.right_iff,hl ▸ g.left_iff⟩
  let c := fun i j => source G (F (S.e i)) (F (S.e j))
  let d := fun i j => targetName p (T (W.e i)) (T (W.e j))
  have rect {i j x y} (eq : c i j=c x y) : (i.isLeft,j.isLeft)=(x.isLeft,y.isLeft) := by
    obtain ⟨a,b⟩ := Relations.end_colors (closure G) eq
    exact Prod.ext (side_eq S a) (side_eq S b)
  have rectT {i j x y} (eq : d i j=d x y) : (i.isLeft,j.isLeft)=(x.isLeft,y.isLeft) := by
    obtain ⟨a,b⟩ := Relations.end_colors (closure H) ((target_same p _ _ _ _).mp eq)
    exact Prod.ext (side_eq W ((target_same p _ _ _ _).mpr a)) (side_eq W ((target_same p _ _ _ _).mpr b))
  have prod : SplitRectangle.Products c d := fun h u v =>
    (count_relabel (restricted (source G) F) S.e u v _ _).trans
      ((D.products u v _ _ _ _ h).trans (count_relabel (restricted (targetName p) T) W.e u v _ _).symm)
  obtain ⟨t,_,ht⟩ := SmallShore.realize_at p (by decide : 0<4) (by decide)
    (fun j => F (S.e (.inr j))) (fun j => T (W.e (.inr j))) f.l
    (D.injF.comp (S.e.injective.comp Sum.inr_injective)) (D.injG.comp (W.e.injective.comp Sum.inr_injective))
    (shore_range _ reg F _ 0 _ D.src S.right) (shore_range _ reg T _ 0 _ D.tgt W.right) 0 0
  obtain ⟨e,he⟩ := SplitRectangle.realize_either c d (0:R) (0:L) rect rectT (fun h => Relations.transpose _ h)
    (fun h => (target_same p _ _ _ _).mpr (Relations.transpose _ ((target_same p _ _ _ _).mp h)))
    (fun h => common_transpose p h) prod (Or.inl twins) (fun u x => SmallShore.realize_at p (by decide : 0<12) (by decide)
      (fun i => F (S.e (.inl i))) (fun i => T (W.e (.inl i))) f.r
      (D.injF.comp (S.e.injective.comp Sum.inl_injective)) (D.injG.comp (W.e.injective.comp Sum.inl_injective))
      (shore_range _ reg F _ 0 _ D.src S.left) (shore_range _ reg T _ 0 _ D.tgt W.left) u x) t ht
  exact ⟨S.e.symm.trans (e.trans W.e),fun i j => by simpa [c,d] using he (S.e.symm i) (S.e.symm j)⟩

end QGI.Coherent.RegionalFourTwelve
