import TenTwelveCatalog
import RegionalEightTwelveHalfModels

noncomputable section
namespace QGI.Coherent.RegionalTenTwelve
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open BinaryShore TenTwelveCatalog
open private twins shore from RegionalFourFourEight
open private range from RegionalSixTwelveDispatch
open private first_mem from BinaryShoreLaws

private theorem simple_twins {k m v w : Nat} (f : Fin k → Fin m → Nat)
    (two : ∀ i j, f i j=v ∨ f i j=w) (s : Cell k)
    (simpCol : ∀ j, support (fun i j => decide (f i j=v)) j=s ∨ support (fun i j => decide (f i j=v)) j=sᶜ) :
    SplitRectangle.Twins f := by
  classical
  let col := support (fun i j => decide (f i j=v))
  let ls (i : Fin k) := decide (i∈s)
  let rs (j : Fin m) := decide (col j=s)
  have mark (i j) : f i j=v ↔ ls i=rs j := by
    have mem : i∈col j ↔ f i j=v := by simp [col,support]
    rw [←mem]
    by_cases h : col j=s
    · simp [rs,ls,h]
    · have e := (simpCol j).resolve_left h
      change col j=sᶜ at e
      have tag : rs j=false := by simp [rs,h]
      rw [tag,e]; simp [ls]
  have model : f=fun i j => if ls i=rs j then v else w := by
    funext i j
    by_cases h : ls i=rs j
    · rw [if_pos h]; exact (mark i j).mpr h
    · rw [if_neg h]; exact (two i j).resolve_left (mt (mark i j).mp h)
  rw [model]
  exact SplitRectangle.twins_of_halves ls rs v w

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

private theorem twins_realize (X : Shore (source G) l I) (Y : Shore (source G) r J) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (shape : SplitRectangle.Twins (fun i j => source G (atPoint X i) (atPoint Y j))) : Realizes p reg := by
  let keep := fun k => k=r
  have old := LargeOrderBlocks.small p keep ((RegionalTwoAnchor.card Y).le.trans (by decide))
  let anchor : Region (source G) keep := ⟨atPoint Y 0,(mem_vertices _ _ _).mpr (Y 0).property⟩
  have ht : source G anchor.val anchor.val=r := (Y 0).property
  have rect : FiberPairExtension.twins (source G) l (source G anchor.val anchor.val) := ht ▸ twins X Y shape
  apply RegionalFourFourEight.restrict_map p (FiberPairExtension.attach p X 0 (by decide) keep old anchor anchor
    (fun j => Or.inl (((mem_vertices _ _ _).mp j.property).trans ht.symm)) rect rect)
  exact fun i h => (cover i h).symm

private theorem solve (F : Shore (source G) l I) (Y : Shore (source G) r J) (a : TenTwelveCatalog.A) (d : D)
    (ca : TenPointCrossLaws.Chart F a)
    (cd : ∀ i j x y, source G (atPoint Y i) (atPoint Y j)=source G (atPoint Y x) (atPoint Y y) ↔ right d i j=right d x y)
    (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) : Realizes p reg := by
  classical
  let f := fun i j => source G (atPoint F i) (atPoint Y j)
  rcases OddHalfPartition.palette (p:=6) (sourceLaws _) F Y (by intro x y pos eq; omega) with ⟨v,uniform⟩|⟨v,w,_,two,wt⟩
  · exact twins_realize p F Y reg cover ⟨fun i k _ _ j => (uniform i j).trans (uniform k j).symm,
      fun _ j k _ i => (uniform i j).trans (uniform i k).symm⟩
  let B := fun i j => decide (f i j=v)
  let R := fun j i => B i j
  have bits : Block F F Y Y B B := fun ⦃_ _ _ _⦄ eq => congrArg (fun u => decide (u=v)) eq
  have reflect (i j x y) (h : B i j=B x y) : f i j=f x y :=
    (RegionalEightTwelveHalfModels.both_colors (two i j) (two x y)).mpr
      (by simpa only [B,decide_eq_decide] using h)
  have rows (i) : degree B i=6 := by simpa only [degree,B,f,decide_eq_true_eq] using wt i
  have eqrows := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) bits)
  have balance := FiberRectangles.balance B rows (fun j => eqrows j 0)
  have cols (j) : (support B j).card=5 := (eqrows j 0).trans (by omega)
  have AL : BinaryShore.Chart (b:=6) (d:=5) F Y B (left a) :=
    ⟨sourceLaws _,bits,reflect,fun i j x y => (ca i j x y).symm,rows,cols⟩
  have AR : BinaryShore.Chart (b:=5) (d:=6) Y F R (right d) :=
    ⟨sourceLaws _,Block.flip (sourceLaws _) bits,fun i j x y h => (sourceLaws _).rev (reflect j i y x h),
     fun i j x y => (cd i j x y).symm,cols,rows⟩
  obtain ⟨hl,pl⟩ := necessary AL (by decide) (by decide)
  obtain ⟨hr,pr⟩ := necessary AR (by decide) (by decide)
  have fitL (j) := inLeft a (AL.cols j) (hl j) (pl j 0)
  have fitR (i) := inRight d (AR.cols i) (hr i) (pr i 0)
  rcases right_cases d (AR.cols 0) (hr 0) with simpR|⟨tri,cap⟩
  · have h := simple_twins (fun j i => f i j) (fun j i => two i j) _ (fun i => simpR _ (fitR i))
    exact twins_realize p F Y reg cover ⟨fun i x j e k => h.2 j i x e k,fun i j y e x => h.1 j y i e x⟩
  rcases left_cases a (AL.cols 0) (hl 0) with simpL|other
  · exact twins_realize p F Y reg cover (simple_twins f two _ (fun j => simpL _ (fitL j)))
  have hit : R (first (support R 0)) 0=true :=
    (Finset.mem_filter.mp (first_mem (Finset.card_pos.mp ((by decide : 0<6).trans_eq (AR.cols 0).symm)))).2
  have pre (i j : J) : (support B i∩support B j).card=predicted (right d) (support R 0) i j := by
    have h := product_eq AR 0 _ hit i j
    have fmt : Block.overlap R i j=(support B i∩support B j).card := by
      apply congrArg Finset.card; ext z; simp [Block.overlap,support,R]
    rw [predicted,←h, Nat.mul_div_cancel_left _ (positive d i j),fmt]
  rcases other with hkey|odd
  · subst a
    obtain ⟨ξ,g,nz,fix⟩ := TenPointPetersen.fixed p F ca
    have sc : RegionalShorePins.Short Y (atPoint F) := by
      intro j
      apply (Finset.card_le_card (t:=Finset.univ.filter (fun k => predicted (right d) (support R 0) j k=5)) ?_).trans (cap j)
      intro k hk
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hk
      have eq := hk
      have same : support B k=support B j := by
        ext i
        simp only [support,Finset.mem_filter,Finset.mem_univ,true_and,B,decide_eq_true_eq]
        change (f i k=v) ↔ (f i j=v)
        rw [show f i k=f i j from Relations.transpose _ (eq i)]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [←pre,same,Finset.inter_self,cols]⟩
    apply RegionalShorePins.realize p F Y Y reg _ (fun i h => (cover i h).imp_right Or.inl)
      ξ nz (atPoint F) g fix (RegionalShorePins.pinned F) sc sc
    intro i h; rcases cover i h with h|h
    · rw [h,LargeFourteenRegion.large,RegionalTwoAnchor.card F]; decide
    · rw [h,LargeFourteenRegion.large,RegionalTwoAnchor.card Y]; decide
  · obtain ⟨i,j,k,even⟩ := tri
    have z := odd _ (fitL i) _ (fitL j) _ (fitL k)
    unfold TenTwelveCatalog.Odd at z
    rw [pre,pre,pre] at z
    omega

theorem realize (X : Shore (source G) l I) (Y : Shore (source G) r J) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) : Realizes p reg := by
  obtain ⟨a,e,ca⟩ := TenPointCrossLaws.chart p X
  obtain ⟨m,diag⟩ := diagonal_names p
  let W : Shore (targetName p) r J := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  have data := (SmallShore.correspondence p (atPoint Y) (atPoint W) r (Subtype.val_injective.comp Y.injective)
    (Subtype.val_injective.comp W.injective) (range Y) (range W)).1
  obtain ⟨d,g,cd⟩ := Literature.zivAv_eight_twelve_homogeneous_catalog (Or.inr rfl) _ data
  exact solve p (e.trans X) (g.trans Y) a d ca cd reg cover

theorem of_size (reg : Nat → Prop) (total : (vertices (source G) reg).card=22)
    (ten : ∃ i, reg (source G i i) ∧ (fiber G i).card=10)
    (twelve : ∃ i, reg (source G i i) ∧ (fiber G i).card=12) : Realizes p reg := by
  classical
  obtain ⟨a,ha,sa⟩ := ten
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

end QGI.Coherent.RegionalTenTwelve
