import RegionalSixTwelveMatching

noncomputable section
namespace QGI.Coherent.RegionalSixTwelve
open SixTenCoordinates SmallFiberExtension StrategyColorLaws RegionalSixTwelveStats
open RegionalSixTwelveGeometry (Point Family degree touch Regular)
open FourTwelveFunctional (source)

private def dye {m : Nat} (v w : Nat) (s : Bool × (Fin m)) := if s.1 then w else v

private def joint {n m l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l Point) (Y : Shore c r (Fin m)) (v w : Nat) :=
  Finset.univ.image (fun s : Bool × (Fin m) => family F Y (dye v w s) s.2)

private theorem joined {n m l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l Point) (Y : Shore c r (Fin m)) (v w : Nat) :
    joint F Y v w=support (family F Y v)∪support (family F Y w) := by
  ext u
  simp only [joint,support,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨flag,j⟩,h⟩
    cases flag with | false => exact Or.inl ⟨j,h⟩ | true => exact Or.inr ⟨j,h⟩
  · rintro (⟨j,h⟩|⟨j,h⟩)
    · exact ⟨(false,j),h⟩
    · exact ⟨(true,j),h⟩

private theorem touching {n m l r : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c) (F : Shore c l Point) (Y : Shore c r (Fin m)) (v : Nat) :
    Block F F F F (touch (support (family F Y v))) (touch (support (family F Y v))) := by
  let b := family F Y v
  let a := fun i j => decide (i∈b j)
  have test (i j) : touch (support b) i j=true ↔ 0 < Block.overlap a i j := by
    simp only [touch,support,decide_eq_true_eq,Finset.mem_image,Finset.mem_univ,true_and,
      Block.overlap,a,Finset.card_pos,Finset.Nonempty,Finset.mem_filter]
    constructor
    · rintro ⟨s,⟨k,rfl⟩,hi,hj⟩; exact ⟨k,by simp [hi,hj]⟩
    · rintro ⟨j,hj⟩; exact ⟨b j,⟨j,rfl⟩,by simpa only [Finset.mem_univ,true_and] using hj⟩
  intro i j x y hit
  apply Bool.eq_iff_iff.mpr
  rw [test,test]
  exact Iff.of_eq (congrArg (0<·) (Block.gram law (Block.flip law (incidence F Y F Y v)) hit))

private theorem joint_regular {n m l r : Nat} [NeZero m] {c : Fin n → Fin n → Nat} (law : Laws c c) (F : Shore c l Point) (Y : Shore c r (Fin m))
    (v w : Nat) (vlen : (family F Y v 0).card=2) (wlen : (family F Y w 0).card=2) :
    Regular (joint F Y v w) := by
  let f := support (family F Y v)
  let g := support (family F Y w)
  obtain ⟨wc,_,_,ra⟩ := statistics law F Y v
  obtain ⟨wd,_,_,_⟩ := statistics law F Y w
  have fw (e) (he : e∈f) : e.card=2 := by obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he; exact (wc j).trans vlen
  have gw (e) (he : e∈g) : e.card=2 := by obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he; exact (wd j).trans wlen
  have weights (e) (he : e∈f∪g) : e.card=2 := (Finset.mem_union.mp he).elim (fw _) (gw _)
  have count := regular_degree f fw ra
  have pos : 0<f.card := Finset.card_pos.mpr ⟨_,Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩
  have covers (i) : ∃ e∈f∪g, i∈e := by
    have base : 0 < degree f 0 := by omega
    have d : 0 < degree f i := base.trans_eq (ra i).symm
    obtain ⟨e,he⟩ := Finset.card_pos.mp d
    exact ⟨e,Finset.mem_union_left _ (Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩
  have unions (i j) : touch (f∪g) i j=(touch f i j || touch g i j) := by
    apply Bool.eq_iff_iff.mpr
    simp only [touch,decide_eq_true_eq,Bool.or_eq_true,Finset.mem_union]
    constructor
    · rintro ⟨e,he,hit⟩; exact he.elim (fun h => Or.inl ⟨e,h,hit⟩) (fun h => Or.inr ⟨e,h,hit⟩)
    · rintro (⟨e,he,hit⟩|⟨e,he,hit⟩)
      · exact ⟨e,Or.inl he,hit⟩
      · exact ⟨e,Or.inr he,hit⟩
  have comb : Block F F F F (touch (f∪g)) (touch (f∪g)) := by
    intro i j x y hit; rw [unions,unions,touching law F Y v hit,touching law F Y w hit]
  rw [joined]
  intro i
  have d := Block.degree_eq law comb i 0
  rw [RegionalSixTwelveGeometry.neighbor_degree _ weights _ (covers i),
    RegionalSixTwelveGeometry.neighbor_degree _ weights _ (covers 0)] at d
  exact Nat.add_right_cancel d

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

/-- Two different partitions of the six points into three pairs give a
six-edge support. Each of its two color names is retained on all probes. -/
theorem two_matchings_named {m l r v w : Nat} [NeZero m] (F : Shore (source G) l Point) (Y : Shore (source G) r (Fin m)) (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r (Fin m))
    (same : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j))
    (vl : (family F Y v 0).card=2) (wl : (family F Y w 0).card=2)
    (vc : (support (family F Y v)).card=3) (wc : (support (family F Y w)).card=3)
    (diff : support (family F Y v)≠support (family F Y w)) :
    ∃ e : Equiv.Perm Point, (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
      ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i)) := by
  let f := support (family F Y v)
  let g := support (family F Y w)
  have sreg := joint_regular (sourceLaws _) F Y v w vl wl
  have get (s : Nat) : (family T Z s 0).card=(family F Y s 0).card := by
    simpa only [Finset.inter_self] using (mixed_counts (commonLaws p) F Y T Z s s (same 0 0)).symm
  have treg := joint_regular (targetLaws p) T Z v w ((get _).trans vl) ((get _).trans wl)
  have wt (s : Bool × (Fin m)) : (family F Y (dye v w s) s.2).card=2 := by
    obtain ⟨b,j⟩ := s
    cases b with
    | false => exact ((statistics (sourceLaws _) F Y v).1 j).trans vl
    | true => exact ((statistics (sourceLaws _) F Y w).1 j).trans wl
  apply named_from_probes p F Y T Z same Prod.snd (dye v w) (fun j => ⟨(false,j),rfl⟩) wt sreg treg
  left
  change (joint F Y v w).card=6
  have weights (e) (he : e∈joint F Y v w) : e.card=2 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he; exact wt j
  have eq := regular_degree _ weights sreg
  rw [joined] at eq ⊢
  change (f∪g).card=6
  change f.card=3 at vc
  change g.card=3 at wc
  change 6*degree (f∪g) 0=(f∪g).card*2 at eq
  have up := Finset.card_union_le f g
  have lf := Finset.card_le_card (Finset.subset_union_left (s₁:=f) (s₂:=g))
  have neq : (f∪g).card≠3 := by
    intro h
    exact diff ((Finset.eq_of_subset_of_card_le Finset.subset_union_left (h.trans vc.symm).le).trans
      (Finset.eq_of_subset_of_card_le Finset.subset_union_right (h.trans wc.symm).le).symm)
  omega

theorem of_two_matchings {l r v w : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (vl : (family F Y v 0).card=2) (wl : (family F Y w 0).card=2)
    (vc : (support (family F Y v)).card=3) (wc : (support (family F Y w)).card=3)
    (diff : support (family F Y v)≠support (family F Y w)) : Realizes p reg :=
  on_pair p F Y reg cover (fun T Z same => two_matchings_named p F Y T Z same vl wl vc wc diff)

end QGI.Coherent.RegionalSixTwelve

