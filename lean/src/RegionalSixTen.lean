import RegionalSixTenTables
import SixTenQuantum
import LargeOrderBlocks

noncomputable section
namespace QGI.Coherent.RegionalSixTen
open SixTenCoordinates SmallUnion StrategyColorLaws LargeFourteenRegion
open QGI.SixTen
open FourTwelveFunctional (source)
open private side_eq from TwoShoreRealization
open private twins_split from SixTenQuantum
open private frame_of_cards from SixTenCoordinates
open private card_core from LargeFourteenRegion

private theorem shore_range {n k : Nat} (C : Fin n → Fin n → Nat) (reg : Nat → Prop)
    (F : V → Fin n) (t : Fin k → V) (u : Fin k) (v : Nat)
    (range : ∀ z, (∃ i, F i=z) ↔ reg (C z z))
    (shore : ∀ z, (∃ i, t i=z) ↔ C (F z) (F z)=v) :
    ∀ z, (∃ i, F (t i)=z) ↔ C z z=v := by
  have inside : reg v := ((shore _).mp ⟨u,rfl⟩) ▸ (range _).mp ⟨t u,rfl⟩
  intro z
  constructor
  · rintro ⟨i,rfl⟩; exact (shore _).mp ⟨i,rfl⟩
  · intro h
    obtain ⟨i,rfl⟩ := (range z).mpr (h ▸ inside)
    obtain ⟨j,rfl⟩ := (shore i).mpr h
    exact ⟨j,rfl⟩

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

private theorem twins_named (p : PerfectStrategy G H K) (reg : Nat → Prop) (F T : V → Fin n)
    (D : DataFor p reg F T) {l r : Nat}
    (f : Frame (restricted (source G) F) l r) (g : Frame (restricted (targetName p) T) l r)
    (twins : SplitRectangle.Twins (cross f) ∨ SplitRectangle.Twins (cross g)) :
    ∃ e : Equiv.Perm V, ∀ i j, source G (F i) (F j)=targetName p (T (e i)) (T (e j)) := by
  let c := fun i j => source G (F (f.e i)) (F (f.e j))
  let d := fun i j => targetName p (T (g.e i)) (T (g.e j))
  let S : TwoShore.Named (restricted (source G) F) 6 10 l r := ⟨f.e,f.left_iff,f.right_iff⟩
  let W : TwoShore.Named (restricted (targetName p) T) 6 10 l r := ⟨g.e,g.left_iff,g.right_iff⟩
  have rect {i j x y} (eq : c i j=c x y) : (i.isLeft,j.isLeft)=(x.isLeft,y.isLeft) := by
    obtain ⟨a,b⟩ := Relations.end_colors (closure G) eq
    exact Prod.ext (side_eq S a) (side_eq S b)
  have rectT {i j x y} (eq : d i j=d x y) : (i.isLeft,j.isLeft)=(x.isLeft,y.isLeft) := by
    obtain ⟨a,b⟩ := Relations.end_colors (closure H) ((target_same p _ _ _ _).mp eq)
    exact Prod.ext (side_eq W ((target_same p _ _ _ _).mpr a)) (side_eq W ((target_same p _ _ _ _).mpr b))
  have prod : SplitRectangle.Products c d := fun h u v =>
    (count_relabel (restricted (source G) F) f.e u v _ _).trans ((D.products u v _ _ _ _ h).trans
      (count_relabel (restricted (targetName p) T) g.e u v _ _).symm)
  obtain ⟨t,_,ht⟩ := SmallShore.realize_at p (by decide : 0<10) (by decide)
    (fun j => F (f.e (.inr j))) (fun j => T (g.e (.inr j))) r
    (D.injF.comp (f.e.injective.comp Sum.inr_injective)) (D.injG.comp (g.e.injective.comp Sum.inr_injective))
    (shore_range _ reg F _ 0 r D.src f.right_iff) (shore_range _ reg T _ 0 r D.tgt g.right_iff) 0 0
  obtain ⟨e,he⟩ := SplitRectangle.realize_either c d (0:A) (0:B) rect rectT
    (fun eq => Relations.transpose _ eq)
    (fun eq => (target_same p _ _ _ _).mpr (Relations.transpose _ ((target_same p _ _ _ _).mp eq)))
    (fun eq => common_transpose p eq) prod twins (fun u x => SmallShore.realize_at p (by decide : 0<6) (by decide)
      (fun i => F (f.e (.inl i))) (fun i => T (g.e (.inl i))) l
      (D.injF.comp (f.e.injective.comp Sum.inl_injective)) (D.injG.comp (g.e.injective.comp Sum.inl_injective))
      (shore_range _ reg F _ 0 l D.src f.left_iff) (shore_range _ reg T _ 0 l D.tgt g.left_iff) u x) t ht
  refine ⟨f.e.symm.trans (e.trans g.e),?_⟩
  intro i j
  obtain ⟨i,rfl⟩ := f.e.surjective i
  obtain ⟨j,rfl⟩ := f.e.surjective j
  simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using he i j

theorem solve (p : PerfectStrategy G H K) (reg : Nat → Prop) (F T : V → Fin n)
    (D : DataFor p reg F T) {l r : Nat}
    (six : (named (restricted (source G) F) l).card=6) (ten : (named (restricted (source G) F) r).card=10) :
    ∃ e : Equiv.Perm V, ∀ i j, source G (F i) (F j)=targetName p (T (e i)) (T (e j)) := by
  let c := restricted (source G) F
  let d := restricted (targetName p) T
  obtain ⟨f⟩ := frame_of_cards c l r six ten
  let g : Frame d l r := ⟨f.e,fun i => (D.sameDiag _).symm.trans (f.left i),
    fun j => (D.sameDiag _).symm.trans (f.right j),f.distinct⟩
  have sourceLaw : Laws c c := ⟨fun h => Relations.transpose _ h,fun h => (Relations.end_colors _ h).2,
    fun a b i j x y eq => D.srcConfig.products a b i j x y eq⟩
  have targetLaw : Laws d d := ⟨fun h => (target_same p _ _ _ _).mpr (Relations.transpose _ ((target_same p _ _ _ _).mp h)),
    fun h => (target_same p _ _ _ _).mpr (Relations.end_colors _ ((target_same p _ _ _ _).mp h)).2,
    fun a b i j x y eq => D.tgtConfig.products a b i j x y eq⟩
  have law : Laws c d := ⟨fun h => common_transpose p h,fun h => (SmallShore.endpoints p h).2,
    fun a b i j x y h => D.products a b i j x y h⟩
  rcases uniform_or_two sourceLaw f with ⟨v,hv⟩ | ⟨v,w,_,two,rows,cols⟩
  · apply twins_named p reg F T D f g (Or.inl ?_)
    constructor <;> intros <;> simp [hv]
  have twoT (i j) : cross g i j=v ∨ cross g i j=w := by
    obtain ⟨x,y,eq⟩ := (D.used (cross g i j)).mpr ⟨g.e (.inl i),g.e (.inr j),rfl⟩
    obtain ⟨hx,hy⟩ := SmallShore.endpoints p eq
    obtain ⟨s,hs⟩ := (f.left_iff x).mpr (hx.trans (g.left i))
    obtain ⟨t,ht⟩ := (f.right_iff y).mpr (hy.trans (g.right j))
    have match' : cross f s t=cross g i j := by simpa only [cross,hs,ht] using eq
    rw [←match']; exact two s t
  obtain ⟨rs,cs,lh,rh⟩ := statistics law f g v
  obtain ⟨s,t,hs⟩ := Cross.normal (basic f v) rows cols
    (fun i j k => (lh i 0 k).trans (lh j 0 k).symm)
    (fun i j k => (rh i 0 k).trans (rh j 0 k).symm)
  rcases hs with split | src
  · exact twins_named p reg F T D f g (Or.inl (twins_split f two split))
  obtain ⟨u,z,ht⟩ := Cross.normal (basic g v)
    (fun i => (rs 0 i).symm.trans (rows 0)) (fun j => (cs 0 j).symm.trans (cols 0))
    (fun i j k => (lh 0 i k).symm.trans (lh 0 j k)) (fun i j k => (rh 0 i k).symm.trans (rh 0 j k))
  rcases ht with split | tgt
  · exact twins_named p reg F T D f g (Or.inr (twins_split g twoT split))
  · exact design_named D.tgtConfig targetLaw law f g v w two twoT s u t z src tgt

theorem realize (p : PerfectStrategy G H K) (reg : Nat → Prop)
    (active : ∀ i, reg (source G i i) → large G (source G i i))
    (size : (vertices (source G) reg).card=16)
    (six : ∃ i, reg (source G i i) ∧ (fiber G i).card=6)
    (ten : ∃ i, reg (source G i i) ∧ (fiber G i).card=10) : SmallFiberExtension.Realizes p reg := by
  apply LargeOrderBlocks.of_solver p reg active size
  intro F T D
  obtain ⟨u,hu,su⟩ := six
  obtain ⟨v,hv,sv⟩ := ten
  obtain ⟨i,rfl⟩ := (D.src _).mpr hu
  obtain ⟨j,rfl⟩ := (D.src _).mpr hv
  exact solve p reg F T D ((LargeOrderBlocks.fiber_card F D.injF D.src i).trans su)
    ((LargeOrderBlocks.fiber_card F D.injF D.src j).trans sv)

theorem isomorphic {xs : List Nat} (P : CoprimeProfiles.Profile G xs)
    (total : (xs.filter (fun k => 3<k)).sum=16) (six : 6∈xs) (ten : 10∈xs)
    (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,gn,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gn
  letI : InnerProductSpace ℂ K := ip
  obtain ⟨x,hx⟩ := P.fiber_of_mem six (by decide)
  obtain ⟨y,hy⟩ := P.fiber_of_mem ten (by decide)
  have region := realize p (large G) (fun _ h => h) ((card_core P).trans total)
    ⟨x,(LargeOrderBlocks.large_iff _).mpr (by rw [hx]; decide),hx⟩
    ⟨y,(LargeOrderBlocks.large_iff _).mpr (by rw [hy]; decide),hy⟩
  obtain ⟨e,he⟩ := SmallFiberExtension.of_large_region p region
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩⟩

end QGI.Coherent.RegionalSixTen
