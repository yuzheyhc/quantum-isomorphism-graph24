import FourSixJointPins
import TwelveSignatureAlignment

noncomputable section
namespace QGI.Coherent.FourSixTwelveRoot
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion RegionalShorePins
open Synchrony Intertwiner
open FourTwelveFunctional (source)
open Classical
variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
local notation "c" => source G
local notation "d" => targetName p

private def sig {u : Fin n → Fin n → Nat} (F : Shore u l (Fin 4)) (S : Shore u r (Fin 6)) (Y : Shore u v (Fin 12))
    (i : Fin 12) (j : Fin 4 ⊕ Fin 6) := u (atPoint Y i) (Sum.elim (atPoint F) (atPoint S) j)

private theorem rows {u : Fin n → Fin n → Nat} (F : Shore u l (Fin 4)) (S : Shore u r (Fin 6)) (Y : Shore u v (Fin 12)) (i j) :
    sig F S Y i=sig F S Y j ↔ (∀ a, u (atPoint Y i) (atPoint F a)=u (atPoint Y j) (atPoint F a)) ∧
      ∀ b, u (atPoint Y i) (atPoint S b)=u (atPoint Y j) (atPoint S b) :=
  ⟨fun h => ⟨fun a => congrFun h (.inl a),fun b => congrFun h (.inr b)⟩,fun ⟨f,s⟩ => funext (fun a => by cases a with | inl i => exact f i | inr i => exact s i)⟩

private theorem equal {u w : Fin n → Fin n → Nat} (law : Laws u w)
    (F : Shore u l (Fin 4)) (S : Shore u r (Fin 6)) (Y : Shore u v (Fin 12))
    (T : Shore w l (Fin 4)) (D : Shore w r (Fin 6)) (Z : Shore w v (Fin 12)) {i j a b}
    (hit : u (atPoint Y i) (atPoint Y j)=w (atPoint Z a) (atPoint Z b)) :
    sig F S Y i=sig F S Y j ↔ sig T D Z a=sig T D Z b := by
  rw [rows,rows]
  exact and_congr (PinnedShoreSignatures.same law Y F Z T hit) (PinnedShoreSignatures.same law Y S Z D hit)

attribute [local instance 2000] Classical.propDecidable Classical.typeDecidableEq in
theorem solve (F : Shore c l (Fin 4)) (S : Shore c r (Fin 6)) (Y : Shore c v (Fin 12)) (reg : Nat → Prop)
    (active : ∀ i, reg (c i i) → large G (c i i)) (cover : ∀ z, reg (c z z) → c z z=l ∨ c z z=r ∨ c z z=v)
    (mark : Nat) (m : Equiv.Perm (Fin 6)) (inc : ∀ i j, c (atPoint F i) (atPoint S j)=mark ↔ FourSixSix.incident i (m j)) :
    Realizes p reg := by
  classical
  obtain ⟨ξ,a,b,nz,pf,ps⟩ := FourSixJointPins.pinned p F S mark m inc
  obtain ⟨T,ta⟩ := PinnedShoreSignatures.coordinates p F ξ nz a pf
  obtain ⟨D,sb⟩ := PinnedShoreSignatures.coordinates p S ξ nz b ps
  let points := Sum.elim (atPoint F) (atPoint S)
  let targets := Sum.elim (atPoint T) (atPoint D)
  have fixed (i) : U p (points i) (targets i) ξ=ξ := by
    rcases i with i|i
    · change U p (atPoint F i) (atPoint T i) ξ=ξ; rw [ta]; exact pf i
    · change U p (atPoint S i) (atPoint D i) ξ=ξ; rw [sb]; exact ps i
  let B := fun i j => decide (sig F S Y j=sig F S Y i)
  have block : Block Y Y Y Y B B := by
    intro i j a b h
    simp only [B,decide_eq_decide]
    exact equal (sourceLaws _) F S Y F S Y ((sourceLaws (closure G)).rev h)
  have sz (i) := Block.degree_eq (sourceLaws _) block i 0
  simp only [B,decide_eq_true_eq] at sz
  rcases TwelveSignatureAlignment.dichotomy (sig F S Y) sz with small|few
  · apply RegionalShorePins.realize p F S Y reg active cover ξ nz points targets fixed
    · exact RegionalMarkPins.widen F (pinned F) (fun j => ⟨.inl j,rfl⟩)
    · exact RegionalMarkPins.widen S (pinned S) (fun j => ⟨.inr j,rfl⟩)
    · intro i; apply (Finset.card_le_card ?_).trans (small i)
      intro j hj
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
      exact funext hj
  obtain ⟨e,diag⟩ := diagonal_names p
  let Z := Y.trans (Equiv.subtypeEquiv e (q:=fun x => d x x=v) (fun x => ⟨fun h => (diag x).symm.trans h,fun h => (diag x).trans h⟩))
  obtain ⟨g,yy,align⟩ := TwelveSignatureAlignment.align p Y Z ξ nz (sig F S Y) (sig T D Z)
    (fun i z on => funext (fun j => RegionalMarkPins.source_name p (fixed j) on))
    (fun _ _ _ _ h => equal (commonLaws p) F S Y T D Z h) few
  have old (i j) : c (points i) (points j)=d (targets i) (targets j) :=
    RegionalMarkPins.source_name p (fixed j) (fun h => nz ((fixed i).symm.trans h))
  exact ThreeShoreCoordinates.join p F S Y reg cover (atPoint T) (atPoint D) (fun j => atPoint Z (g j))
    (fun i j => old (.inl i) (.inl j)) (fun i j => old (.inr i) (.inr j)) yy (fun i j => old (.inl i) (.inr j))
    (fun i j => common_transpose p (congrFun (align j) (.inl i))) (fun i j => common_transpose p (congrFun (align j) (.inr i)))
end QGI.Coherent.FourSixTwelveRoot
