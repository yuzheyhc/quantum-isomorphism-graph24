import EightTwelveSignNames

noncomputable section
namespace QGI.Coherent.RegionalEightTwelveSigned
open EightTwelveSigns SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open EightTwelveHalf (P C model)
open RegionalEightTwelveStats
open RegionalEightTwelveHalfLaws (rowCells NamedGram crossGram supports)
open EightTwelveSignGeometry (geometric zero_iff_complement)
open EightTwelveSignLaws (pairing row_gram row_weight split_rows uniform)
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch

variable {n l r v w : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)
    (F : Shore (source G) l I) (Y : Shore (source G) r J)
    (T : Shore (targetName p) l I) (Z : Shore (targetName p) r J)

private theorem model_four (key' : Key)
    (chart : ∀ i j x y, source G (atPoint Y i) (atPoint Y j)=source G (atPoint Y x) (atPoint Y y) ↔
      rightName key' i j=rightName key' x y)
    (rr : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j))
    (ll : ∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T i) (atPoint T j))
    (two : ∀ j i, color F Y j i=v ∨ color F Y j i=w) (wt : ∀ j, (family F Y v j).card=4)
    (names : NamedGram F (family F Y v)) (e : Equiv.Perm I)
    (shape : (supports (family F Y v)).image (fun s => s.image e)=model 4)
    (reg : Nat → Prop) (cover : ∀ z, reg (source G z z) → source G z z=l ∨ source G z z=r) : Realizes p reg := by
  let a := family F Y v
  let b := family T Z v
  obtain ⟨inj,opp,dist,diag⟩ := geometric e shape
  have col (j k) : (a j∩a k).card=(b j∩b k).card := mixed_counts (commonLaws p) F Y T Z v v (rr j k)
  have cross {i j x y} (h : source G (atPoint F i) (atPoint F j)=targetName p (atPoint T x) (atPoint T y)) :
      crossGram a i j=crossGram b x y := by
    simpa only [crossGram,Block.overlap,decide_eq_true_eq] using
      Block.gram (commonLaws p) (Block.flip (commonLaws p) (incidence F Y T Z v)) h
  have cr (i j) : crossGram a i j=crossGram b i j := cross (ll i j)
  obtain ⟨o,ka,pa⟩ := pairing (a:=key') wt inj opp (fun j k x y h =>
    mixed_counts (sourceLaws _) F Y F Y v v ((chart j k x y).mpr h))
  have wb (j) : (b j).card=4 := (by simpa only [Finset.inter_self] using (col j j).symm : (b j).card=(a j).card).trans (wt j)
  have pb (i) : b (point o i false)=(b (point o i true))ᶜ := by
    apply (zero_iff_complement (wb _) (wb _)).mp
    rw [←col]
    exact (zero_iff_complement (wt _) (wt _)).mpr (pa i)
  have st (i j x y) : source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z x) (atPoint Z y) ↔
      rightName (atlas o) i j=rightName (atlas o) x y := by rw [ka,←rr]; exact chart i j x y
  have lr : l≠r := by
    rintro rfl
    have h := Fintype.card_congr (F.trans Y.symm)
    simp only [Fintype.card_fin] at h
    omega
  have sgram (i t : I) (h : i≠t) := dist i t h
  have tgram (i t : I) (h : i≠t) : crossGram b i t=2 ∨ crossGram b i t=3 := cr i t ▸ sgram i t h
  have sa := present o (rowCells a) (split_rows pa)
    (fun i t h => row_gram a i t ▸ sgram i t h)
    (fun i => (row_weight a i).trans (diag i))
    (uniform (sourceLaws _) F Y two (fun i j x y h => (st i j x y).mp (h.trans (rr x y))))
  have ta := present o (rowCells b) (split_rows pb)
    (fun i t h => row_gram b i t ▸ tgram i t h)
    (fun i => (row_weight b i).trans ((cr i i).symm.trans (diag i)))
    (uniform (targetLaws p) T Z (RegionalEightTwelveHalfModels.target_two p F Y T Z two)
      (fun i j x y h => (st i j x y).mp ((rr i j).trans h)))
  have mono : Function.Injective (rowCells a) := by
    intro i t eq
    by_contra ne
    have h : crossGram a i t=2 ∨ crossGram a i t=3 := sgram i t ne
    have same : crossGram a i t=6 := by rw [←row_gram a i t,eq,Finset.inter_self,row_weight]; exact diag t
    rw [same] at h
    omega
  obtain ⟨A⟩ := sa
  obtain ⟨B⟩ := ta
  exact EightTwelveSignNames.glue p F Y T Z lr A B st
    (fun i j x y => ⟨cross,fun h => (names mono i j x y (h.trans (cr x y).symm)).trans (ll x y)⟩) two reg cover

include F Y in
/-- Both named fibers, including all five balanced incidence templates. -/
theorem realize (reg : Nat → Prop) (cover : ∀ z, reg (source G z z) → source G z z=l ∨ source G z z=r) : Realizes p reg := by
  obtain ⟨m,diag⟩ := diagonal_names p
  let W : Shore (targetName p) r J := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let U : Shore (targetName p) l I := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  have data := (SmallShore.correspondence p (atPoint Y) (atPoint W) r (Subtype.val_injective.comp Y.injective)
    (Subtype.val_injective.comp W.injective) (range Y) (range W)).1
  obtain ⟨k,d,hk⟩ := Literature.zivAv_eight_twelve_homogeneous_catalog (Or.inr rfl) _ data
  let Y' := d.trans Y
  rcases RegionalEightTwelveComplete.reduction p F Y' reg cover with doneAlready|⟨v,w,_,two,wt,ng,e,shape⟩
  · exact doneAlready
  obtain ⟨g,_,hg⟩ := SmallShore.realize_at p (by decide : 0<12) (by decide) (atPoint Y') (atPoint W) r
    (Subtype.val_injective.comp Y'.injective) (Subtype.val_injective.comp W.injective) (range Y') (range W) 0 0
  obtain ⟨f,_,hf⟩ := SmallShore.realize_at p (by decide : 0<8) (by decide) (atPoint F) (atPoint U) l
    (Subtype.val_injective.comp F.injective) (Subtype.val_injective.comp U.injective) (range F) (range U) 0 0
  exact model_four p F Y' (f.trans U) (g.trans W) k hk hg hf two wt ng e shape reg cover

open private shore from RegionalFourFourEight

theorem of_size (reg : Nat → Prop) (total : (vertices (source G) reg).card=20)
    (eight : ∃ i, reg (source G i i) ∧ (fiber G i).card=8)
    (twelve : ∃ i, reg (source G i i) ∧ (fiber G i).card=12) : Realizes p reg := by
  classical
  obtain ⟨a,ha,sa⟩ := eight
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
  apply realize p F Y reg
  intro i hi
  have mem := (mem_vertices _ _ _).mpr hi
  rw [←full] at mem
  simpa only [Finset.mem_union,FourTwelveFunctional.fiber_eq] using mem

end QGI.Coherent.RegionalEightTwelveSigned
