import RegionalShorePins
import ShoreSignatureSize
import RegionalOverlap
import LargeOrderFourteen
import RegionalFourSixEight

noncomputable section
namespace QGI.Coherent.SixSixEightPins
open SixTenCoordinates SixEightGeometry SmallUnion SmallFiberExtension LargeFourteenRegion StrategyColorLaws RegionalShorePins
open FourTwelveFunctional (source)
open SixEightCatalog (Six Eight)
open RepeatedTetra (Repeated)
open private narrow from TwoAnchorUnionGlue
open Classical

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

abbrev Flat {l r a b : Nat} [NeZero a] [NeZero b] (F : Shore (source G) l (Fin a)) (Y : Shore (source G) r (Fin b)) :=
  ∀ i j, rect F Y i j=rect F Y 0 0

theorem flip_flat {l r a b : Nat} [NeZero a] [NeZero b] (F : Shore (source G) l (Fin a)) (Y : Shore (source G) r (Fin b))
    (h : Flat F Y) : Flat Y F := fun i j => Relations.transpose _ (h j i)

theorem flat_twins {l r a b : Nat} [NeZero a] [NeZero b] (F : Shore (source G) l (Fin a)) (Y : Shore (source G) r (Fin b))
    (h : Flat F Y) : SplitRectangle.Twins (rect F Y) :=
  ⟨fun i x _ _ y => (h i y).trans (h x y).symm,fun _ j y _ x => (h x j).trans (h x y).symm⟩

theorem tetra_short {l r v w : Nat} (A : Shore (source G) l Six) (Y : Shore (source G) r Eight)
    (vw : v≠w) (P : Repeated 2 A Y v w) : Short Y (atPoint A) := by
  intro i
  let a := P.right.symm i
  have hi : P.right a=i := P.right.apply_symm_apply _
  have two : (Finset.univ : Finset (Fin 2)).card≤3 := by decide
  apply (RegionalSignatureBound.bound_set id Function.injective_id (fun j : Fin 2 => P.right (a.1,j)) _ _ ?_).trans two
  intro b hb
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb
  let z := P.right.symm b
  have hz : P.right z=b := P.right.apply_symm_apply _
  have face : z.1=a.1 := by
    apply (show ∀ i j : Fin 4, (∀ e, i∈FourTwelveCycle.edge e ↔ j∈FourTwelveCycle.edge e) → i=j by decide) z.1 a.1
    intro e
    have h := hb (P.left e)
    have m := P.names z.1 z.2 e
    have m' := P.names a.1 a.2 e
    change rect Y A (P.right (z.1,z.2)) (P.left e)=_ at m
    change rect Y A (P.right (a.1,a.2)) (P.left e)=_ at m'
    rw [Prod.mk.eta,hz] at m
    rw [Prod.mk.eta,hi] at m'
    have eq := m.symm.trans (h.trans m')
    by_cases left : z.1∈FourTwelveCycle.edge e <;> by_cases right : a.1∈FourTwelveCycle.edge e <;> simp_all
  exact ⟨z.2,Finset.mem_univ _,by change P.right (a.1,z.2)=b; rw [←face,Prod.mk.eta,hz]⟩

theorem tetra {l r z v w : Nat} (A : Shore (source G) l Six) (B : Shore (source G) r Six) (Y : Shore (source G) z Eight)
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=z)
    (pair : Realizes p (fun t => t=l ∨ t=z)) (vw : v≠w) (P : Repeated 2 A Y v w) (mixed : ¬Flat B A) : Realizes p reg := by
  obtain ⟨e,he⟩ := pair
  let T := A.trans (narrow e he (show l=l ∨ l=z from Or.inl rfl))
  let Z := Y.trans (narrow e he (show z=l ∨ z=z from Or.inr rfl))
  let Q : Repeated 2 T Z v w := ⟨P.left,P.right,fun a k i => by
    let y : Region (source G) (fun t => t=l ∨ t=z) := RegionalOverlap.member (c:=source G) (s:=fun t => t=l ∨ t=z) (atPoint Y (P.right (a,k))) (Or.inr (Y _).property : _=l ∨ _=z)
    let x : Region (source G) (fun t => t=l ∨ t=z) := RegionalOverlap.member (c:=source G) (s:=fun t => t=l ∨ t=z) (atPoint A (P.left i)) (Or.inl (A _).property : _=l ∨ _=z)
    exact (he y x).symm.trans (P.names a k i)⟩
  obtain ⟨V⟩ := RepeatedTetra.choose p vw P Q
  let t := fun i => RepeatedTetra.left Q (V.point (P.left.symm i))
  have fix (i) : Intertwiner.U p (atPoint A i) (t i) V.ξ=V.ξ := by
    simpa only [RepeatedTetra.left,Equiv.apply_symm_apply,t] using V.left_fixed (P.left.symm i)
  apply RegionalShorePins.realize p A B Y reg active cover V.ξ V.nz (atPoint A) t fix (pinned A) _ (tetra_short A Y vw P)
  intro i
  apply (Finset.card_le_card ?_).trans (ShoreSignatureSize.half (sourceLaws _) B A mixed i)
  intro b h
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h ⊢
  exact h

theorem cube {l r z : Nat} (A : Shore (source G) l Six) (B : Shore (source G) r Six) (Y : Shore (source G) z Eight)
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=z)
    (base : Realizes p (fun t => t=l ∨ t=r)) (pair : Realizes p (fun t => t=l ∨ t=z))
    (az : l≠z) (bz : r≠z) (cube : Cube A Y) (mixed : ¬Flat A Y) : Realizes p reg := by
  by_cases h : Flat B Y
  · apply RegionalOverlap.attach p A Y reg cover base pair _ cube.lift
    intro i j a b hr hz ha hb
    let i' := B.symm ⟨i,hr⟩
    let j' := Y.symm ⟨j,hz⟩
    let a' := B.symm ⟨a,ha⟩
    let b' := Y.symm ⟨b,hb⟩
    simpa only [i',j',a',b',rect,atPoint,Equiv.apply_symm_apply] using (h i' j').trans (h a' b').symm
  have sa := (classify az A Y).1.resolve_left mixed
  have sb := (classify bz B Y).1.resolve_left h
  apply RegionalShorePins.root p A B Y reg active cover (atPoint Y 0) (one A _ (sa 0)) (one B _ (sb 0)) (one Y _ ?_)
  intro i
  apply (Finset.card_le_card ?_).trans (cube.small 0 i)
  intro t ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relations.transpose _ (Finset.mem_filter.mp ht).2⟩

end QGI.Coherent.SixSixEightPins
