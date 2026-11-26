import EightFourteenCatalog
import RegionalTenTwelve
import FourteenFiber

noncomputable section
namespace QGI.Coherent.EightFourteenReduction
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws BinaryShore
open EightFourteenCatalog hiding left right
open FourTwelveFunctional (source)
open private twins from RegionalFourFourEight
open private simple_twins from RegionalTenTwelve
open private first_mem from BinaryShoreLaws
open private range from RegionalSixTwelveDispatch

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)
def entry {c : Fin n → Fin n → Nat} (F : Shore c l I) (Y : Shore c r J) (i : I) (j : J) := c (atPoint F i) (atPoint Y j)
def flag {c : Fin n → Fin n → Nat} (F : Shore c l I) (Y : Shore c r J) (v : Nat) (i : I) (j : J) := decide (entry F Y i j=v)

theorem twins_realize (F : Shore (source G) l I) (Y : Shore (source G) r J) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (tw : SplitRectangle.Twins (entry F Y)) : Realizes p reg := by
  let keep := fun t => t=r
  have old := LargeOrderBlocks.fourteen p keep (fun i h => by
    change source G i i=r at h; rw [h,LargeFourteenRegion.large,RegionalTwoAnchor.card Y]; decide) (RegionalTwoAnchor.card Y)
  let anchor : Region (source G) keep := ⟨atPoint Y 0,(mem_vertices _ _ _).mpr (Y 0).property⟩
  have ht : source G anchor.val anchor.val=r := (Y 0).property
  have rect : FiberPairExtension.twins (source G) l (source G anchor.val anchor.val) := ht ▸ twins F Y tw
  apply RegionalFourFourEight.restrict_map p (FiberPairExtension.attach p F 0 (by decide) keep old anchor anchor
    (fun j => Or.inl (((mem_vertices _ _ _).mp j.property).trans ht.symm)) rect rect)
  exact fun i h => (cover i h).symm

structure HardData (F : Shore (source G) l I) (Y : Shore (source G) r J) (d : RK) (v w : Nat) : Prop where
  hardKey : hard d
  palette : ∀ i j, entry F Y i j=v ∨ entry F Y i j=w
  leftNames : ∀ i j x y, source G (atPoint F i) (atPoint F j)=source G (atPoint F x) (atPoint F y) ↔ (i=j ↔ x=y)
  rightNames : ∀ i j x y, source G (atPoint Y i) (atPoint Y j)=source G (atPoint Y x) (atPoint Y y) ↔
    EightFourteenCatalog.right d i j=EightFourteenCatalog.right d x y
  splitRows : ∀ i q, flag F Y v i (point q false)=true ↔ flag F Y v i (point q true)≠true
  overlap : ∀ i j, i≠j → Block.overlap (flag F Y v) i j=3

private theorem solve (F : Shore (source G) l I) (Y : Shore (source G) r J) (a : LK) (d : RK)
    (ca : ∀ i j x y, source G (atPoint F i) (atPoint F j)=source G (atPoint F x) (atPoint F y) ↔
      EightFourteenCatalog.left a i j=EightFourteenCatalog.left a x y)
    (cd : ∀ i j x y, source G (atPoint Y i) (atPoint Y j)=source G (atPoint Y x) (atPoint Y y) ↔
      EightFourteenCatalog.right d i j=EightFourteenCatalog.right d x y)
    (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) :
    Realizes p reg ∨ ∃ v w, HardData F Y d v w := by
  classical
  let f := entry F Y
  rcases OddHalfPartition.palette (p:=7) (sourceLaws _) F Y (by intro x y pos eq; omega) with ⟨v,uniform⟩|⟨v,w,_,two,wt⟩
  · exact Or.inl (twins_realize p F Y reg cover ⟨fun i k _ _ j => (uniform i j).trans (uniform k j).symm,
      fun _ j k _ i => (uniform i j).trans (uniform i k).symm⟩)
  let B := flag F Y v
  let R := fun j i => B i j
  have bits : Block F F Y Y B B := fun ⦃_ _ _ _⦄ eq => congrArg (fun u => decide (u=v)) eq
  have reflect (i j x y) (h : B i j=B x y) : f i j=f x y :=
    (RegionalEightTwelveHalfModels.both_colors (two i j) (two x y)).mpr (by simpa only [B,flag,decide_eq_decide] using h)
  have rows (i) : degree B i=7 := by simpa only [degree,B,flag,entry,decide_eq_true_eq] using wt i
  have eqrows := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) bits)
  have balance := FiberRectangles.balance B rows (fun j => eqrows j 0)
  have cols (j) : (support B j).card=4 := (eqrows j 0).trans (by omega)
  have AL : BinaryShore.Chart (b:=7) (d:=4) F Y B (EightFourteenCatalog.left a) :=
    ⟨sourceLaws _,bits,reflect,fun i j x y => (ca i j x y).symm,rows,cols⟩
  have AR : BinaryShore.Chart (b:=4) (d:=7) Y F R (EightFourteenCatalog.right d) :=
    ⟨sourceLaws _,Block.flip (sourceLaws _) bits,fun i j x y h => (sourceLaws _).rev (reflect j i y x h),
     fun i j x y => (cd i j x y).symm,cols,rows⟩
  obtain ⟨hl,pl⟩ := necessary AL (by decide) (by decide)
  obtain ⟨hr,pr⟩ := necessary AR (by decide) (by decide)
  have fitL (j) := lmem a (AL.cols j) (hl j) (pl j 0)
  have fitR (i) := rmem d (AR.cols i) (hr i) (pr i 0)
  rcases right_cases d (AR.cols 0) (hr 0) with simpR|⟨key,sides⟩
  · have h := simple_twins (fun j i => f i j) (fun j i => two i j) _ (fun i => simpR _ (fitR i))
    exact Or.inl (twins_realize p F Y reg cover ⟨fun i x j e k => h.2 j i x e k,fun i j y e x => h.1 j y i e x⟩)
  rcases left_cases a (AL.cols 0) (hl 0) with simpL|⟨rank,check⟩
  · exact Or.inl (twins_realize p F Y reg cover (simple_twins f two _ (fun j => simpL _ (fitL j))))
  refine Or.inr ⟨v,w,key,two,fun i j x y => (ca i j x y).trans (rank i j x y),cd,?_,?_⟩
  · intro i q
    simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and] using sides _ (fitR i) q
  · intro i j ne
    have hit : B (first (support B 0)) 0=true :=
      (Finset.mem_filter.mp (first_mem (Finset.card_pos.mp ((by decide : 0<4).trans_eq (AL.cols 0).symm)))).2
    have h := product_eq AL 0 _ hit i j
    obtain ⟨pos,val⟩ := check i j ne
    exact Nat.eq_of_mul_eq_mul_left pos (h.trans val)

theorem reduction (X : Shore (source G) l I) (Y₀ : Shore (source G) r J) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) :
    Realizes p reg ∨ ∃ (F : Shore (source G) l I) (Y : Shore (source G) r J) (d : RK) (v w : Nat), HardData F Y d v w := by
  obtain ⟨m,diag⟩ := diagonal_names p
  let T : Shore (targetName p) l I := X.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let Z : Shore (targetName p) r J := Y₀.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  have lx := (SmallShore.correspondence p (atPoint X) (atPoint T) l (Subtype.val_injective.comp X.injective)
    (Subtype.val_injective.comp T.injective) (range X) (range T)).1
  have ly := (SmallShore.correspondence p (atPoint Y₀) (atPoint Z) r (Subtype.val_injective.comp Y₀.injective)
    (Subtype.val_injective.comp Z.injective) (range Y₀) (range Z)).1
  obtain ⟨a,e,ca⟩ := Literature.eight_homogeneous_catalog _ lx
  let c := SmallShore.restrict (source G) (atPoint Y₀)
  have allDiag (j) : c j j=r := (Y₀ j).property
  have hc : Configuration c := ⟨fun _ _ x h => (ly.diag _ _).mp (h.trans (allDiag x)),ly.reverse,ly.products⟩
  obtain ⟨k,⟨P⟩,_⟩ := Literature.zivAv_fourteen_common_catalog hc hc (fun i => by simp only [allDiag,Finset.filter_true_of_mem,Finset.card_univ,Fintype.card_fin]; decide)
    (fun _ => Iff.rfl) hc.products
  have hom (i : J) : ZivAv.color k i i=ZivAv.color k 0 0 := by
    have eq : P.labels (ZivAv.name k i i)=P.labels (ZivAv.name k 0 0) := by rw [←P.cell,←P.cell,allDiag,allDiag]
    exact congrArg Fin.val (P.labels.injective eq)
  let d : RK := ⟨k.val,first_sixteen k hom⟩
  have cd (i j x y : J) : c (P.coordinates i) (P.coordinates j)=c (P.coordinates x) (P.coordinates y) ↔
      EightFourteenCatalog.right d i j=EightFourteenCatalog.right d x y := by
    rw [P.cell,P.cell,P.labels.injective.eq_iff]; exact Fin.ext_iff
  rcases solve p (e.trans X) (P.coordinates.trans Y₀) a d ca cd reg cover with doneAlready|⟨v,w,z⟩
  · exact Or.inl doneAlready
  · exact Or.inr ⟨_,_,d,v,w,z⟩
end QGI.Coherent.EightFourteenReduction
