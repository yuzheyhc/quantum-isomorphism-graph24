import CoprimeProfiles
import SeventeenHardRegion
import FourEightMixed
import TwoAnchorUnionGlue
import TwoCycleMatchings

noncomputable section
namespace QGI.Coherent.SeventeenHardEight
open Relations StrategyColorLaws SixTenCoordinates FourEightGeometry FourTwelveCycle SeventeenHardRegion
open FourTwelveFunctional (source)
open private root_unique from SingletonSwitch

private theorem twins {n k t l v} {c : Fin n → Fin n → Nat}
    (F : Shore c l (Fin k)) (Y : Shore c v (Fin t))
    (h : SplitRectangle.Twins (fun i j => c (atPoint F i) (atPoint Y j))) :
    SeventeenHardGlue.Twins.twinBlock c l v := by
  constructor
  · intro i x j he y
    simpa only [atPoint,Equiv.apply_symm_apply] using h.1 (F.symm i) (F.symm x) (Y.symm j)
      (by simpa only [atPoint,Equiv.apply_symm_apply] using he) (Y.symm y)
  · intro i j y he x
    simpa only [atPoint,Equiv.apply_symm_apply] using h.2 (F.symm i) (Y.symm j) (Y.symm y)
      (by simpa only [atPoint,Equiv.apply_symm_apply] using he) (F.symm x)

private theorem reverse {n l r} {G : Graph n}
    (h : SeventeenHardGlue.Twins.twinBlock (source G) l r) :
    SeventeenHardGlue.Twins.twinBlock (source G) r l := by
  exact ⟨fun i x j e y => transpose _ (h.2 j i x (transpose _ e) y),
    fun i j y e x => transpose _ (h.1 j y i (transpose _ e) x)⟩

private theorem center {G H : Graph 17} (R : Core G) {l r v k m t : Nat}
    [NeZero k] [NeZero m] [NeZero t] (F : Shore (source G) l (Fin k))
    (S : Shore (source G) r (Fin m)) (Y : Shore (source G) v (Fin t))
    (lr : l≠r) (lv : l≠v) (lo : 4≤k) (hi : k≤13)
    (cover : ∀ x, source G x x=l ∨ source G x x=r ∨ source G x x=v ∨ source G x x=R.rootName)
    (first : SeventeenHardGlue.Twins.twinBlock (source G) l r)
    (second : SeventeenHardGlue.Twins.twinBlock (source G) l v) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,ng,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  let c := source G
  let x : SeventeenHardGlue.Twins.Outside c l := ⟨atPoint S 0,fun h => lr (h.symm.trans (S 0).property)⟩
  let y : SeventeenHardGlue.Twins.Outside c l := ⟨atPoint Y 0,fun h => lv (h.symm.trans (Y 0).property)⟩
  have hx : c x.val x.val=r := (S 0).property
  have hy : c y.val y.val=v := (Y 0).property
  have size : (fiber G (atPoint F 0)).card=k := by
    let e := Equiv.subtypeEquivRight (fun z => (FourTwelveFunctional.fiber_eq (atPoint F 0) z).trans
      (show (c z z=c (atPoint F 0) (atPoint F 0)) ↔ c z z=l by rw [show c (atPoint F 0) (atPoint F 0)=l from (F 0).property]))
    simpa using Fintype.card_congr (e.trans F.symm)
  apply SeventeenHardGlue.Twins.isomorphic p F 0 hi x y
  · rw [Core.outside_card (i:=atPoint F 0) (F 0).property,size]; omega
  · intro j
    rcases cover j.val with h|h|h|h
    · exact (j.property h).elim
    · exact Or.inl (h.trans hx.symm)
    · exact Or.inr (Or.inl (h.trans hy.symm))
    · right; right
      intro i z w hw
      rw [root_unique R.root R.one j.val h,root_unique R.root R.one w (hw.trans h)]
      exact R.root_pair (i.property.trans z.property.symm)
  · change SeventeenHardGlue.Twins.twinBlock c l (c x.val x.val)
    rw [hx]; exact first
  · change SeventeenHardGlue.Twins.twinBlock c l (c y.val y.val)
    rw [hy]; exact second

/-- Both four-by-eight interfaces come from the same named configuration.
A common two-point base on the eight-point overlap suffices when both are
doubled cycles. The singleton belongs to both maps and has a unique image. -/
theorem four_four_eight {G H : Graph 17} (P : CoprimeProfiles.Profile G [1,4,4,8])
    (q : QuantumIso G H) : Isomorphic G H := by
  classical
  let c := source G
  have pos : ∀ i : Fin 4, 0 < ([1,4,4,8] : List Nat)[i.val] := by decide
  choose rep tag using fun i : Fin 4 => P.occurs i (pos i)
  let name := fun i : Fin 4 => c (rep i) (rep i)
  have ne {i j : Fin 4} (h : i≠j) : name i ≠ name j := fun eq =>
    h ((tag i).symm.trans (((P.same _ _).mpr eq).trans (tag j)))
  have size (i : Fin 4) : (fiber G (rep i)).card = ([1,4,4,8] : List Nat)[i.val] := by
    rw [P.fiber_size,tag]
  let R : Core G := ⟨rep 0,size 0⟩
  let l := name 1
  let r := name 2
  let v := name 3
  have lr : l≠r := ne (by decide : (1:Fin 4)≠2)
  have lv : l≠v := ne (by decide : (1:Fin 4)≠3)
  have rv : r≠v := ne (by decide : (2:Fin 4)≠3)
  have frame (i : Fin 4) : Nonempty (Shore c (name i) (Fin (([1,4,4,8] : List Nat)[i.val]))) := by
    let f := Fintype.equivOfCardEq (show Fintype.card (Fin (([1,4,4,8] : List Nat)[i.val])) =
      Fintype.card {z // z∈fiber G (rep i)} by simp [size i])
    exact ⟨f.trans (Equiv.subtypeEquivRight (FourTwelveFunctional.fiber_eq (rep i)))⟩
  obtain ⟨F⟩ : Nonempty (Shore c l (Fin 4)) := frame 1
  obtain ⟨S⟩ : Nonempty (Shore c r (Fin 4)) := frame 2
  obtain ⟨Y⟩ : Nonempty (Shore c v (Fin 8)) := frame 3
  have cover (x) : c x x=l ∨ c x x=r ∨ c x x=v ∨ c x x=R.rootName := by
    have eq : c x x=name (P.tag x) := (P.same x (rep (P.tag x))).mp (tag _).symm
    rcases (show ∀ i : Fin 4, i=0 ∨ i=1 ∨ i=2 ∨ i=3 by decide) (P.tag x) with e|e|e|e <;> rw [e] at eq
    · exact Or.inr (Or.inr (Or.inr eq))
    · exact Or.inl eq
    · exact Or.inr (Or.inl eq)
    · exact Or.inr (Or.inr (Or.inl eq))
  have flex (x) : c x x=l ∨ c x x=r ∨ c x x=v ∨ (∀ z, c z z=c x x → z=x) :=
    (cover x).imp_right (Or.imp_right (Or.imp_right (fun h z eq =>
      (root_unique R.root R.one z (eq.trans h)).trans (root_unique R.root R.one x h).symm)))
  have flexS (x) : c x x=r ∨ c x x=l ∨ c x x=v ∨ (∀ z, c z z=c x x → z=x) := by
    rcases flex x with h|h|h|h <;> tauto
  have coverS (x) : c x x=r ∨ c x x=l ∨ c x x=v ∨ c x x=R.rootName := by
    rcases cover x with h|h|h|h <;> tauto
  have coverY (x) : c x x=v ∨ c x x=l ∨ c x x=r ∨ c x x=R.rootName := by
    rcases cover x with h|h|h|h <;> tauto
  by_cases mixed : ∃ i j, c (atPoint F i) (atPoint S j) ≠ c (atPoint F 0) (atPoint S 0)
  · have mixedS : ∃ j i, c (atPoint S j) (atPoint F i) ≠ c (atPoint S 0) (atPoint F 0) := by
      obtain ⟨i,j,h⟩ := mixed
      exact ⟨j,i,fun eq => h (transpose (closure G) eq)⟩
    rcases dispatch lv F Y q with done|ft|⟨u,_,_,b,fb,⟨B⟩⟩
    · exact done
    · rcases dispatch rv S Y q with done|st|⟨w,_,_,d,sd,⟨D⟩⟩
      · exact done
      · exact center R Y F S lv.symm rv.symm (by decide) (by decide) coverY
          (reverse (twins F Y ft)) (reverse (twins S Y st)) q
      · exact FourEightMixed.isomorphic_with_singletons S F Y flexS mixedS w d sd D q
    · exact FourEightMixed.isomorphic_with_singletons F S Y flex mixed u b fb B q
  · push_neg at mixed
    have uniform : SplitRectangle.Twins (fun i j => c (atPoint F i) (atPoint S j)) :=
      ⟨fun i x _ _ y => (mixed i y).trans (mixed x y).symm,fun _ j y _ x => (mixed x j).trans (mixed x y).symm⟩
    rcases dispatch lv F Y q with done|ft|⟨u,_,_,b,fb,⟨B⟩⟩
    · exact done
    · exact center R F S Y lr lv (by decide) (by decide) cover (twins F S uniform) (twins F Y ft) q
    · rcases dispatch rv S Y q with done|st|⟨w,_,_,d,sd,⟨D⟩⟩
      · exact done
      · exact center R S F Y lr.symm rv (by decide) (by decide) coverS
          (reverse (twins F S uniform)) (twins S Y st) q
      · exact TwoAnchorUnionGlue.isomorphic_with_singletons (by decide) (by decide) lr lv rv F S Y flex mixed
          (TwoCycleMatchings.two_base (sourceLaws _) F S Y mixed u w b d fb sd B D) q

end QGI.Coherent.SeventeenHardEight

