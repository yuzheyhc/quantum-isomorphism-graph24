import SixNineAttachments

noncomputable section
namespace QGI.Coherent.RegionalFourSixNine
open Relations SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source fiber_eq)
open private twins reverse shore from RegionalFourFourEight
open private narrow from TwoAnchorUnionGlue
open FourSixSix.Interfaces (flag)
open RegionalCycleExtension (emb range_emb)

def deg (col : Fin 6 → Bool) (i : Fin 4) := ∑ e, if flag i e=true then (if col e=true then 1 else 0 : Nat) else 0
private theorem opposite : ∀ a b c d e f : Bool, let col := ![a,b,c,d,e,f]
    (∀ i, deg col i=deg col 0) → col 0=col 5 := by native_decide

private theorem duplicate {n l r v : Nat} {G : Graph n} (F : Shore (source G) l (Fin 4))
    (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) v (Fin 9)) (t : Nat) (p : Equiv.Perm (Fin 6))
    (cells : ∀ i j, source G (atPoint F i) (atPoint S j)=t ↔ FourSixSix.incident i (p j))
    (uniform : ∀ i j, source G (atPoint F i) (atPoint Y j)=source G (atPoint F 0) (atPoint Y 0)) :
    ∃ a b, a≠b ∧ ∀ j, source G (atPoint S a) (atPoint Y j)=source G (atPoint S b) (atPoint Y j) := by
  let c := source G
  let A := fun i k => flag i (p k)
  have named : Block F F S S A A := by
    intro i j x y h
    apply Bool.eq_iff_iff.mpr
    change decide (FourSixSix.incident i (p j))=true ↔ decide (FourSixSix.incident x (p y))=true
    simp only [decide_eq_true_eq,←cells,h]
  refine ⟨p.symm 0,p.symm 5,p.symm.injective.ne (by decide),fun j => ?_⟩
  let v := c (atPoint S (p.symm 0)) (atPoint Y j)
  let B := fun k z => decide (c (atPoint S k) (atPoint Y z)=v)
  have names : Block S S Y Y B B := fun ⦃_ _ _ _⦄ h => congrArg (fun u => decide (u=v)) h
  let col := fun k => B (p.symm k) j
  let test := fun b z : Bool => if b=true then (if z=true then 1 else 0 : Nat) else 0
  have prod := Block.fold (sourceLaws (closure G)) named names test
  have shift (i) : deg col i=∑ z, test (A i z) (B z j) := by
    have eq := Equiv.sum_comp p (fun k => test (flag i k) (col k))
    simpa only [deg,A,col,test,Equiv.symm_apply_apply] using eq.symm
  have value (i) : deg col i=deg col 0 := by rw [shift,shift]; exact prod ((uniform i j).trans (uniform 0 j).symm)
  have eqv : (![col 0,col 1,col 2,col 3,col 4,col 5] : Fin 6 → Bool)=col := by funext i; fin_cases i <;> rfl
  have special := opposite (col 0) (col 1) (col 2) (col 3) (col 4) (col 5)
  dsimp only at special
  rw [eqv] at special
  have eq := special value
  have x : col 0=true := by simp [col,B,v]
  have y : col 5=true := eq ▸ x
  exact (of_decide_eq_true y).symm

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

theorem solve {l r v : Nat} (lr : l≠r) (rv : r≠v) (F : Shore (source G) l (Fin 4))
    (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) v (Fin 9)) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v) : Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  have sz {t k : Nat} (A : Shore c t (Fin k)) (i : Fin n) (h : c i i=t) : (fiber G i).card=k := by
    have eq : fiber G i=vertices c (·=t) := by ext z; rw [fiber_eq,mem_vertices]; change c z z=c i i ↔ c z z=t; rw [h]
    rw [eq]; exact RegionalTwoAnchor.card A
  have uniform (i j : Fin n) (hi : c i i=l) (hj : c j j=v) : c i j=c (atPoint F 0) (atPoint Y 0) :=
    CoprimeFibers.monochromatic G _ _ (by rw [sz F _ (F 0).property,sz Y _ (Y 0).property]; decide)
      ((fiber_eq _ _).mpr (hi.trans (F 0).property.symm)) ((fiber_eq _ _).mpr (hj.trans (Y 0).property.symm))
  have fy := fun i j => uniform (atPoint F i) (atPoint Y j) (F i).property (Y j).property
  have ft : FiberPairExtension.twins c l v := twins F Y
    ⟨fun i x _ _ j => (fy i j).trans (fy x j).symm,fun _ j z _ i => (fy i j).trans (fy i z).symm⟩
  let keep := fun s => s=l ∨ s=r
  have small46 := LargeOrderBlocks.small p keep ((RegionalTwoAnchor.pair_bound F S).trans (by decide))
  have small69 := LargeOrderBlocks.of_solver p (fun z => z=r ∨ z=v) (fun i h => by
    rcases h with h|h
    · change 3 < (vertices (source G) (fun w => w=source G i i)).card; rw [h,RegionalTwoAnchor.card S]; decide
    · change 3 < (vertices (source G) (fun w => w=source G i i)).card; rw [h,RegionalTwoAnchor.card Y]; decide)
    (RegionalFourSixEight.pair_card rv S Y) (Fifteen.solve p _)
  have good (fs : FiberPairExtension.twins c l r) : Realizes p reg :=
    RegionalFourFourEight.centered p F S Y (by decide) small69 cover fs ft
  rcases FourSixSix.Interfaces.classify (sourceLaws _) F S with ⟨z,all⟩|fs|⟨t,map,inc⟩
  · exact good (twins F S ⟨fun i x _ _ j => (all i j).trans (all x j).symm,fun _ j z _ i => (all i j).trans (all i z).symm⟩)
  · exact good fs
  rcases SixNineTriples.classify rv S Y (duplicate F S Y t map inc fy) with uni|⟨v₀,A,B,oa,ob,rect,wt⟩
  · have sy : FiberPairExtension.twins c r v := twins S Y
      ⟨fun i x _ _ j => (uni i j).trans (uni x j).symm,fun _ j z _ i => (uni i j).trans (uni i z).symm⟩
    apply RegionalFourFourEight.centered p Y F S (by decide) small46 _ (reverse ft) (reverse sy)
    intro i h; rcases cover i h with h|h|h <;> tauto
  exact SixNineAttachments.attach p F S Y reg cover uniform small46 v₀ A B oa ob rect wt

theorem realize (reg : Nat → Prop) (total : (vertices (source G) reg).card=19)
    (four : ∃ a, reg (source G a a) ∧ (fiber G a).card=4)
    (six : ∃ a, reg (source G a a) ∧ (fiber G a).card=6)
    (nine : ∃ a, reg (source G a a) ∧ (fiber G a).card=9) : Realizes p reg := by
  obtain ⟨a,ha,sa⟩ := four; obtain ⟨b,hb,sb⟩ := six; obtain ⟨y,hy,sy⟩ := nine
  obtain ⟨F⟩ := shore a sa; obtain ⟨S⟩ := shore b sb; obtain ⟨Y⟩ := shore y sy
  have ne (i j : Fin n) (diff : (fiber G i).card≠(fiber G j).card) : source G i i≠source G j j := by
    intro h; apply diff <| congrArg Finset.card (show fiber G i=fiber G j by ext z; rw [fiber_eq,fiber_eq,h])
  have ab := ne a b (by rw [sa,sb]; decide)
  have ay := ne a y (by rw [sa,sy]; decide)
  have by' := ne b y (by rw [sb,sy]; decide)
  exact solve p ab by' F S Y reg (RegionalFourFourEight.three_cover ha hb hy ab ay by' (by rw [sa,sb,sy,total]))

end QGI.Coherent.RegionalFourSixNine
