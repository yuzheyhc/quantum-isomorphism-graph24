import RegionalSixTwelveEdges
import RegionalFourFourEight

noncomputable section
namespace QGI.Coherent.RegionalSixTwelve
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws RegionalSixTwelveStats
open RegionalSixTwelveGeometry (Point)
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension
open private twins from RegionalFourFourEight
open private rows from RegionalSixTwelveEdges

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

private theorem range {c : Fin n → Fin n → Nat} {l : Nat} {X : Type} (F : Shore c l X) (z : Fin n) :
    (∃ i, atPoint F i=z) ↔ c z z=l := by
  constructor
  · rintro ⟨i,rfl⟩; exact (F i).property
  · intro h; exact ⟨F.symm ⟨z,h⟩,congrArg Subtype.val (F.apply_symm_apply ⟨z,h⟩)⟩

theorem on_pair {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (solve : ∀ (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r Right),
      (∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j)) →
      ∃ e : Equiv.Perm Point, (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
        ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i))) : Realizes p reg := by
  obtain ⟨m,diag⟩ := diagonal_names p
  let T : Shore (targetName p) l Point := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let W : Shore (targetName p) r Right := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨h,_,names⟩ := SmallShore.realize_at p (by decide : 0<12) (by decide) (atPoint Y) (atPoint W) r
    (Subtype.val_injective.comp Y.injective) (Subtype.val_injective.comp W.injective) (range Y) (range W) 0 0
  let Z := h.trans W
  obtain ⟨e,ll,rl⟩ := solve T Z names
  let s : Point ⊕ Right → Fin n := Sum.elim (atPoint F) (atPoint Y)
  let t : Point ⊕ Right → Fin n := Sum.elim (fun i => atPoint T (e i)) (atPoint Z)
  have eq (i j) : source G (s i) (s j)=targetName p (t i) (t j) := by
    cases i with
    | inl i => cases j with | inl j => exact ll i j | inr j => exact common_transpose p (rl j i)
    | inr i => cases j with | inl j => exact rl i j | inr j => exact names i j
  have pick (x : Region (source G) reg) : ∃ i, s i=x.val := by
    rcases cover _ ((mem_vertices _ _ _).mp x.property) with left|right
    · obtain ⟨i,hi⟩ := (range F _).mpr left; exact ⟨.inl i,hi⟩
    · obtain ⟨i,hi⟩ := (range Y _).mpr right; exact ⟨.inr i,hi⟩
  choose k hk using pick
  have both (i j) : source G i.val j.val=targetName p (t (k i)) (t (k j)) := by rw [←hk i,←hk j]; exact eq _ _
  obtain ⟨u,hu⟩ := bundle p reg (fun i => t (k i)) both
  exact ⟨u,fun i j => by rw [hu,hu]; exact both i j⟩

theorem of_edge {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (weight : (family F Y v 0).card=2)
    (size : (support (family F Y v)).card=6 ∨ (support (family F Y v)).card=12) : Realizes p reg :=
  on_pair p F Y reg cover (fun T Z same => edge_named p F Y T Z same weight size)

theorem of_single {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (j : Right) (i : Point) (one : (family F Y (color F Y j i) j).card=1) : Realizes p reg := by
  have old := LargeOrderBlocks.small p (·=r) ((RegionalTwoAnchor.card Y).le.trans (by decide))
  apply RegionalFourFourEight.functional p old (fun x h => (cover x h).symm) (atPoint Y j) (atPoint F i) (Y j).property (F i).property
  intro z eq
  obtain ⟨x,rfl⟩ := (range F z).mpr ((Relations.end_colors (closure G) eq).2.trans (F i).property)
  have mem (u : Point) (hit : color F Y j u=color F Y j i) : u∈family F Y (color F Y j i) j :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
  exact congrArg (atPoint F) ((Finset.card_le_one.mp one.le) x (mem _ eq) i (mem _ rfl))

theorem edge_reduction {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (weight : (family F Y v 0).card=2) :
    Realizes p reg ∨ ((support (family F Y v)).card=3 ∧ ∀ i, RegionalSixTwelveGeometry.degree (support (family F Y v)) i=1) := by
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
  rcases sizes with small|big
  · exact Or.inr ⟨small,fun i => (regu i).trans (by change RegionalSixTwelveGeometry.degree (support b) 0=1; omega)⟩
  · exact Or.inl (of_edge p F Y reg cover weight big)

theorem of_twins {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (shape : SplitRectangle.Twins (color F Y)) : Realizes p reg := by
  let keep := fun k => k=l
  have old := LargeOrderBlocks.small p keep ((RegionalTwoAnchor.card F).le.trans (by decide))
  let anchor : Region (source G) keep := ⟨atPoint F 0,(mem_vertices _ _ _).mpr (F 0).property⟩
  have type : source G anchor.val anchor.val=l := (F 0).property
  have rect : FiberPairExtension.twins (source G) r (source G anchor.val anchor.val) := type ▸ twins Y F shape
  apply RegionalFourFourEight.restrict_map p (FiberPairExtension.attach p Y 0 (by decide) keep old anchor anchor
    (fun j => Or.inl (((mem_vertices _ _ _).mp j.property).trans type.symm)) rect rect) cover

theorem complementary_twins {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l Point) (Y : Shore c r Right)
    {v w : Nat} (vw : v≠w) (palette : ∀ j i, color F Y j i=v ∨ color F Y j i=w)
    (two : (support (family F Y v)).card=2) (closed : ∀ s∈support (family F Y v), sᶜ∈support (family F Y v)) :
    SplitRectangle.Twins (color F Y) := by
  classical
  let b := family F Y v
  let s := b 0
  have mem (j) : b j∈support b := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have ne : s≠sᶜ := fun h => by
    have eq : (0 : Point)∈s ↔ 0∈sᶜ := Iff.of_eq (congrArg (fun u : Cell => (0 : Point)∈u) h)
    simp only [Finset.mem_compl] at eq
    by_cases z : (0 : Point)∈s
    · exact eq.mp z z
    · exact z (eq.mpr z)
  have all : ({s,sᶜ} : RegionalSixTwelveGeometry.Family)=support b := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset (mem 0) (Finset.singleton_subset_iff.mpr (closed s (mem 0)))
    · change (support b).card≤_
      rw [two,Finset.card_pair ne]
  let left := fun j => decide (b j=s)
  let right := fun i : Point => decide (i∈s)
  have pattern : color F Y=fun j i => if left j=right i then v else w := by
    funext j i
    have belongs : b j=s ∨ b j=sᶜ := by
      have h := mem j; rw [←all] at h; simpa only [Finset.mem_insert,Finset.mem_singleton] using h
    have read : color F Y j i=v ↔ i∈b j := by simp [color,b,family]
    have equiv : color F Y j i=v ↔ left j=right i := by
      rcases belongs with h|h
      · simp [read,left,right,h]
      · simp [read,left,right,h,ne.symm]
    by_cases h : color F Y j i=v
    · rw [if_pos (equiv.mp h),h]
    · rw [if_neg (mt equiv.mpr h)]; exact (palette j i).resolve_left h
  rw [pattern]; exact SplitRectangle.twins_of_halves _ _ _ _

/-- All genuine half-color interfaces either realize the region by the twin
extension or have four triples with every pair meeting in exactly one point. -/
theorem half_reduction {l r v w : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (vw : v≠w) (palette : ∀ j i, color F Y j i=v ∨ color F Y j i=w) (weight : (family F Y v 0).card=3) :
    Realizes p reg ∨ ((support (family F Y v)).card=4 ∧ ∀ s∈support (family F Y v), ∀ t∈support (family F Y v),
      s≠t → (s∩t).card=1) := by
  let b := family F Y v
  have law := sourceLaws (closure G)
  obtain ⟨weights,_,size,regular⟩ := statistics law F Y v
  have len (s) (hs : s∈support b) : s.card=3 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact (weights j).trans weight
  rcases RegionalSixTwelveGeometry.half_shapes (support b) len size
      ⟨b 0,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ regular (half_values law F Y vw palette) with comp | tetra
  · exact Or.inl (of_twins p F Y reg cover (complementary_twins F Y vw palette comp.1 comp.2))
  · exact Or.inr tetra

end QGI.Coherent.RegionalSixTwelve

