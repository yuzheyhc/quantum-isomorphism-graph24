import RegionalSixTwelveReduction
import RegionalTetraRealize

noncomputable section
namespace QGI.Coherent.RegionalSixTwelve
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws RegionalSixTwelveStats RegionalTetraLayout
open RegionalSixTwelveGeometry (Point)
open FourTwelveFunctional (source)
open LargeFourteenRegion (large)
open private range from RegionalSixTwelveDispatch
open private full_inter from RegionalSixTwelveStats
open private card_core from LargeFourteenRegion
open private shore from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

private theorem target_layout {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right)
    {v w : Nat} (S : TetraShape (family F Y v) (color F Y) v w) (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r Right)
    (names : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j)) :
    Nonempty (Layout T Z v w) := by
  classical
  let u := family F Y v
  let b := family T Z v
  let law := commonLaws p
  have palette (j i) : color T Z j i=v ∨ color T Z j i=w := by
    obtain ⟨q,has⟩ := law.middle (names j j)
    obtain ⟨x,hx⟩ := q.surjective (atPoint T i)
    have eq : source G (atPoint Y j) x=targetName p (atPoint Z j) (atPoint T i) := by simpa only [hx] using (has x).1
    obtain ⟨i',hi'⟩ := (range F x).mpr ((law.last eq).trans (T i).property)
    rw [←hi'] at eq
    change color F Y j i'=color T Z j i at eq
    exact eq ▸ S.palette j i'
  have gram (i j) : (u i∩u j).card=(b i∩b j).card := overlap_names law F Y T Z v (names i j)
  have wt (j) : (b j).card=3 := by
    have h := gram j j
    simp only [Finset.inter_self] at h
    exact h.symm.trans (S.weight j)
  have coincide (i j) : u i=u j ↔ b i=b j := by
    rw [←full_inter _ _ ((S.weight i).trans (S.weight j).symm),←full_inter _ _ ((wt i).trans (wt j).symm)]
    change (u i∩u j).card=(u i).card ↔ (b i∩b j).card=(b i).card
    rw [gram,S.weight,wt]
  have triple (j) : mu b (b j)=3 := by
    have same : Finset.univ.filter (fun i => b i=b j)=Finset.univ.filter (fun i => u i=u j) := by ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,coincide]
    exact (congrArg Finset.card same).trans (S.tripled _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have total := weighted b 3 triple (fun _ => 1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at total
  have four : (support b).card=4 := by
    change 12=3*(support b).card at total
    omega
  apply make (targetLaws p) T Z palette wt four
  · intro s hs t ht ne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
    exact (gram i j).symm.trans (S.intersection _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)) (fun eq => ne ((coincide i j).mp eq)))
  · intro s hs
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
    exact triple j

/-- Every region covered by a six-point and a twelve-point diagonal fiber
admits a bijection preserving all original directed color names. -/
theorem solve {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) : Realizes p reg := by
  rcases reduce_to_tetra p F Y reg cover with doneAlready | ⟨v,w,S⟩
  · exact doneAlready
  obtain ⟨P⟩ := make (sourceLaws _) F Y S.palette S.weight S.four S.intersection S.tripled
  obtain ⟨m,diag⟩ := diagonal_names p
  let T : Shore (targetName p) l Point := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let W : Shore (targetName p) r Right := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨h,_,names⟩ := SmallShore.realize_at p (by decide : 0<12) (by decide) (atPoint Y) (atPoint W) r
    (Subtype.val_injective.comp Y.injective) (Subtype.val_injective.comp W.injective) (range Y) (range W) 0 0
  let Z := h.trans W
  obtain ⟨Q⟩ := target_layout p F Y S T Z names
  exact RegionalTetraRealize.realize p S.vw P Q reg cover

theorem realize (reg : Nat → Prop) (_active : ∀ i, reg (source G i i) → large G (source G i i))
    (total : (vertices (source G) reg).card=18)
    (six : ∃ i, reg (source G i i) ∧ (fiber G i).card=6)
    (twelve : ∃ i, reg (source G i i) ∧ (fiber G i).card=12) : Realizes p reg := by
  classical
  obtain ⟨a,ha,sa⟩ := six
  obtain ⟨b,hb,sb⟩ := twelve
  obtain ⟨F⟩ := shore a sa
  obtain ⟨Y⟩ := shore b sb
  have diff : source G a a≠source G b b := by
    intro eq
    have same : fiber G a=fiber G b := by ext i; rw [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.fiber_eq,eq]
    rw [same,sb] at sa
    contradiction
  have dj : Disjoint (fiber G a) (fiber G b) := Finset.disjoint_left.mpr fun _ h k =>
    diff (((FourTwelveFunctional.fiber_eq _ _).mp h).symm.trans ((FourTwelveFunctional.fiber_eq _ _).mp k))
  have full : fiber G a∪fiber G b=vertices (source G) reg := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      simp only [Finset.mem_union,FourTwelveFunctional.fiber_eq] at hi
      exact (mem_vertices _ _ _).mpr (hi.elim (fun h => h ▸ ha) (fun h => h ▸ hb))
    · rw [Finset.card_union_of_disjoint dj,sa,sb,total]
  apply solve p F Y reg
  intro i hi
  have mem := (mem_vertices _ _ _).mpr hi
  rw [←full] at mem
  simpa only [Finset.mem_union,FourTwelveFunctional.fiber_eq] using mem

theorem isomorphic {xs : List Nat} (P : CoprimeProfiles.Profile G xs)
    (total : (xs.filter (fun k => 3<k)).sum=18) (six : 6∈xs) (twelve : 12∈xs)
    (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,gn,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gn
  letI : InnerProductSpace ℂ K := ip
  obtain ⟨x,hx⟩ := P.fiber_of_mem six (by decide)
  obtain ⟨y,hy⟩ := P.fiber_of_mem twelve (by decide)
  have region := realize p (large G) (fun _ h => h) ((card_core P).trans total)
    ⟨x,(LargeOrderBlocks.large_iff _).mpr (by rw [hx]; decide),hx⟩
    ⟨y,(LargeOrderBlocks.large_iff _).mpr (by rw [hy]; decide),hy⟩
  obtain ⟨e,he⟩ := SmallFiberExtension.of_large_region p region
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩⟩

end QGI.Coherent.RegionalSixTwelve

