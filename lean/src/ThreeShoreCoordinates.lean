import SixSixEightPins
import LargeOrderFourFourTwelve
import RegionalSixTwelveComplete
import RegionalMarkPins

noncomputable section
namespace QGI.Coherent.ThreeShoreCoordinates
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch
open private bundle from SmallFiberExtension
variable {n l r v k m h : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)
local notation "c" => source G
local notation "d" => targetName p

theorem join (F : Shore c l (Fin k)) (S : Shore c r (Fin m)) (Y : Shore c v (Fin h))
    (reg : Nat → Prop) (cover : ∀ z, reg (c z z) → c z z=l ∨ c z z=r ∨ c z z=v)
    (a : Fin k → Fin n) (b : Fin m → Fin n) (y : Fin h → Fin n)
    (aa : ∀ i j, c (atPoint F i) (atPoint F j)=d (a i) (a j)) (bb : ∀ i j, c (atPoint S i) (atPoint S j)=d (b i) (b j))
    (yy : ∀ i j, c (atPoint Y i) (atPoint Y j)=d (y i) (y j)) (ab : ∀ i j, c (atPoint F i) (atPoint S j)=d (a i) (b j))
    (ay : ∀ i j, c (atPoint F i) (atPoint Y j)=d (a i) (y j)) (by' : ∀ i j, c (atPoint S i) (atPoint Y j)=d (b i) (y j)) : Realizes p reg := by
  let s : Fin k ⊕ Fin m ⊕ Fin h → Fin n := Sum.elim (atPoint F) (Sum.elim (atPoint S) (atPoint Y))
  let t : Fin k ⊕ Fin m ⊕ Fin h → Fin n := Sum.elim a (Sum.elim b y)
  have eq (i j) : c (s i) (s j)=d (t i) (t j) := by
    rcases i with i|i|i <;> rcases j with j|j|j
    · exact aa i j
    · exact ab i j
    · exact ay i j
    · exact common_transpose p (ab j i)
    · exact bb i j
    · exact by' i j
    · exact common_transpose p (ay j i)
    · exact common_transpose p (by' j i)
    · exact yy i j
  have pick (x : Region c reg) : ∃ i, s i=x.val := by
    rcases cover _ ((mem_vertices _ _ _).mp x.property) with h|h|h
    · obtain ⟨i,hi⟩ := (range F _).mpr h; exact ⟨.inl i,hi⟩
    · obtain ⟨i,hi⟩ := (range S _).mpr h; exact ⟨.inr (.inl i),hi⟩
    · obtain ⟨i,hi⟩ := (range Y _).mpr h; exact ⟨.inr (.inr i),hi⟩
  choose idx idxEq using pick
  obtain ⟨e,he⟩ := bundle p reg (t ∘ idx) (fun i j => by rw [←idxEq i,←idxEq j]; exact eq _ _)
  exact ⟨e,fun i j => by rw [he,he,←idxEq i,←idxEq j]; exact eq _ _⟩

theorem flat [NeZero k] [NeZero m] (F : Shore c l (Fin k)) (S : Shore c r (Fin m)) (hf : SixSixEightPins.Flat F S)
    (a b : Fin n) (ha : d a a=l) (hb : d b b=r) (i j) : c (atPoint F i) (atPoint S j)=d a b := by
  obtain ⟨x,y,supp⟩ := StrategyColors.exists_source p a b
  have hit := (associated p).mpr (StrategyColors.maps_support p supp)
  obtain ⟨u,hu⟩ := (range F _).mpr ((SmallShore.endpoints p hit).1.trans ha)
  obtain ⟨w,hw⟩ := (range S _).mpr ((SmallShore.endpoints p hit).2.trans hb)
  rw [←hu,←hw] at hit
  exact (hf i j).trans ((hf u w).symm.trans hit)
end QGI.Coherent.ThreeShoreCoordinates
