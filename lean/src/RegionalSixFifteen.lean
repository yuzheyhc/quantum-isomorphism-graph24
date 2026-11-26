import RegionalSixTwelvePairs
import FifteenNamed
import RegionalFourSixEight
import NineNineRectangles

noncomputable section
namespace QGI.Coherent.RegionalSixFifteen
open SixTenCoordinates SmallFiberExtension SmallUnion StrategyColorLaws RegionalSixTwelveStats
open RegionalSixTwelveGeometry (Point degree)
open RegionalSixTwelve (regular_degree matching_named two_matchings_named named_from_probes_more)
open FourTwelveFunctional (source fiber_eq)
open private shore twins from RegionalFourFourEight

private def coords {n k d} {c : Table n} (F : Shore c d (Fin k)) : Fin k ≃ Region c (·=d) :=
  F.trans (Equiv.subtypeEquivRight (fun i => (mem_vertices c (·=d) i).symm))

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

theorem on_pair {k m l r : Nat} (F : Shore (source G) l (Fin k)) (Y : Shore (source G) r (Fin m))
    (old : Realizes p (·=r))
    (solve : ∀ (T : Shore (targetName p) l (Fin k)) (Z : Shore (targetName p) r (Fin m)),
      (∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j)) →
      ∃ e : Equiv.Perm (Fin k), (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
        ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i))) :
    Realizes p (fun t => t=r ∨ t=l) := by
  obtain ⟨f,hf⟩ := old
  obtain ⟨u,hu⟩ := diagonal_names p
  let T : Shore (targetName p) l (Fin k) := F.trans (Equiv.subtypeEquiv u (fun i => by rw [←hu]))
  let Z := ((coords Y).trans f).trans (Equiv.subtypeEquivRight (fun i => mem_vertices (targetName p) (·=r) i))
  obtain ⟨e,one,both⟩ := solve T Z (fun i j => hf (coords Y i) (coords Y j))
  let g := (coords F).symm.trans (e.trans (coords T))
  have loc (i) : g (coords F i)=coords T (e i) := by simp [g]
  apply ThreeRectangleExtension.merge_maps p (·=r) l f g hf
  · intro i j; obtain ⟨i,rfl⟩ := (coords F).surjective i; obtain ⟨j,rfl⟩ := (coords F).surjective j
    rw [loc,loc]; exact one i j
  · intro j i; obtain ⟨j,rfl⟩ := (coords Y).surjective j; obtain ⟨i,rfl⟩ := (coords F).surjective i
    rw [loc]; exact both j i

abbrev Large := Fin 15
private theorem degree_even {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Large) (t : Nat) :
    2 ∣ (family F Y t 0).card := by
  let B := fun j i => decide (i∈family F Y t j)
  have block := incidence F Y F Y t
  have h := FiberRectangles.balance B (fun j => Block.degree_eq (sourceLaws _) block j 0)
    (fun i => Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) block) i 0)
  have zero : FiberRectangles.degree (B 0)=(family F Y t 0).card := by simp [FiberRectangles.degree,B]
  change 15*FiberRectangles.degree (B 0)=6*FiberRectangles.degree (fun j => B j 0) at h
  rw [zero] at h
  omega

private theorem disjoint {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Large)
    (j) {s t : Nat} (diff : s≠t) : Disjoint (family F Y s j) (family F Y t j) :=
  Finset.disjoint_left.mpr fun _ h k => diff ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp k).2)

private theorem count_labels (u d : Nat) (dv : u∣15) (eq : 6*d=u*2) : u=3 ∨ u=15 := by
  have lim : u≤15 := Nat.le_of_dvd (by decide) dv
  have test : ∀ i : Fin 16, i.val∣15 → 3∣i.val → i.val=3 ∨ i.val=15 := by native_decide
  have mult : 3∣u := ⟨d,by omega⟩
  exact test ⟨u,by omega⟩ dv mult

set_option maxHeartbeats 1200000 in
theorem extend {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Large)
    (old : Realizes p (·=r)) : Realizes p (fun t => t=r ∨ t=l) := by
  classical
  let doneHere := Realizes p (fun t => t=r ∨ t=l)
  by_contra no
  have ge (j i) : 2≤(family F Y (color F Y j i) 0).card := by
    let s := color F Y j i
    have even := degree_even F Y s
    have pos := Finset.card_pos.mpr (show (family F Y s j).Nonempty from
      ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩)
    have same := (statistics (sourceLaws _) F Y s).1 j
    change 2≤(family F Y s 0).card; omega
  have alternative (v : Nat) (weight : (family F Y v 0).card=2) : (support (family F Y v)).card=3 := by
    obtain ⟨wt,_,div,regA⟩ := statistics (sourceLaws _) F Y v
    let b := family F Y v
    have wf (s) (hs : s∈support b) : s.card=2 := by
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact (wt j).trans weight
    have eq := regular_degree (support b) wf regA
    change (support b).card∣15 at div
    have sizes := count_labels (support b).card (degree (support b) 0) div eq
    rcases sizes with easy|full
    · exact easy
    apply False.elim <| no ?_
    apply on_pair p F Y old
    intro T Z same
    exact named_from_probes_more p F Y T Z same id (fun _ => v) Function.surjective_id (fun j => (wt j).trans weight)
      regA (statistics (targetLaws p) T Z v).2.2.2 (Or.inr full)
  let a := color F Y 0 0
  by_cases uniform : ∀ j i, color F Y j i=a
  · let y := coords Y 0
    have yr : source G y.val y.val=r := (Y 0).property
    have rect := twins F Y (show SplitRectangle.Twins (fun i j => source G (atPoint F i) (atPoint Y j)) from
      ⟨fun i x _ _ j => Relations.transpose _ ((uniform j i).trans (uniform j x).symm),
       fun _ j k _ i => Relations.transpose _ ((uniform j i).trans (uniform k i).symm)⟩)
    apply no <| FiberPairExtension.attach p F 0 (by decide) (·=r) old y y
      (fun t => Or.inl (((mem_vertices _ _ _).mp t.property).trans yr.symm)) (by rw [yr]; exact rect) (by rw [yr]; exact rect)
  push_neg at uniform
  obtain ⟨j₀,i₀,ne⟩ := uniform
  let b := color F Y j₀ i₀
  have diff : a≠b := Ne.symm ne
  have cap := Finset.card_le_univ (family F Y a 0∪family F Y b 0)
  rw [Finset.card_union_of_disjoint (disjoint F Y _ diff),Fintype.card_fin] at cap
  have binary : ∃ v, (family F Y v 0).card=2 := by
    have x := degree_even F Y a; have y := degree_even F Y b
    have z : 2≤(family F Y a 0).card := ge 0 0
    have w : 2≤(family F Y b 0).card := ge j₀ i₀
    by_cases eq : (family F Y a 0).card=2
    · exact ⟨a,eq⟩
    · exact ⟨b,by omega⟩
  obtain ⟨v,weight⟩ := binary
  have three := alternative v weight
  by_cases const : ∀ j i x, (∀ t, i∈family F Y v t ↔ x∈family F Y v t) → color F Y j i=color F Y j x
  · exact no <| on_pair p F Y old (fun T Z same => matching_named p F Y T Z same weight three const)
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
  have cap := Finset.card_le_univ ((family F Y v j∪family F Y w j)∪family F Y t j)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disjoint F Y j vt,disjoint F Y j unequal⟩),
    Finset.card_union_of_disjoint (disjoint F Y j vw),Fintype.card_fin] at cap
  have gw : 2≤(family F Y w j).card := (ge j i).trans_eq ((statistics (sourceLaws _) F Y w).1 j).symm
  have gt : 2≤(family F Y t j).card := (ge j x).trans_eq ((statistics (sourceLaws _) F Y t).1 j).symm
  have w0 := ((statistics (sourceLaws _) F Y w).1 j).symm.trans (show (family F Y w j).card=2 by omega)
  have diff : support (family F Y v)≠support (family F Y w) := by
    intro eq
    have mem : family F Y w j∈support (family F Y v) := by
      rw [eq]; exact Finset.mem_image_of_mem (family F Y w) (Finset.mem_univ j)
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp mem
    have iin : i∈family F Y v s := by
      rw [hs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,rfl⟩
    have xin := (similar s).mp iin
    rw [hs] at xin
    exact unequal (Finset.mem_filter.mp xin).2.symm
  exact no <| on_pair p F Y old (fun T Z same => two_matchings_named p F Y T Z same weight w0 three (alternative w w0) diff)

variable [CompleteSpace K]
theorem realize (reg : Nat → Prop) (size : (vertices (source G) reg).card=21)
    (six : ∃ i, reg (source G i i) ∧ (fiber G i).card=6)
    (fifteen : ∃ i, reg (source G i i) ∧ (fiber G i).card=15) : Realizes p reg := by
  classical
  obtain ⟨a,ha,sa⟩ := six; obtain ⟨b,hb,sb⟩ := fifteen
  let c := source G
  obtain ⟨F⟩ := shore a sa; obtain ⟨Y⟩ := shore b sb
  have old := LargeOrderBlocks.of_solver p (·=c b b) (fun i h => by
      change source G i i=source G b b at h; change 3 < (vertices (source G) (·=source G i i)).card; rw [h,RegionalTwoAnchor.card Y]; decide)
    (RegionalTwoAnchor.card Y) (Fifteen.solve p _)
  have ne : c b b≠c a a := by
    intro eq
    have same : fiber G b=fiber G a := by ext z; rw [fiber_eq,fiber_eq]; change (c z z=c b b ↔ c z z=c a a); rw [eq]
    have h := congrArg Finset.card same; omega
  let R := fun t => t=c b b ∨ t=c a a
  have all : vertices c R=vertices c reg := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi; apply (mem_vertices _ _ _).mpr
      rcases (mem_vertices _ _ _).mp hi with h|h
      · exact (congrArg reg h).mpr hb
      · exact (congrArg reg h).mpr ha
    · rw [size,RegionalFourSixEight.pair_card ne Y F]
  apply RegionalFourFourEight.restrict_map p (extend p F Y old)
  intro i hi
  apply (mem_vertices c R i).mp
  rw [all]; exact (mem_vertices _ _ _).mpr hi

end QGI.Coherent.RegionalSixFifteen
