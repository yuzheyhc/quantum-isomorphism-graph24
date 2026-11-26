import LargeOrderSquareInterface
import LargeOrderFiveAnchors

noncomputable section
namespace QGI.Coherent.LargeOrderFourDirections
open SixTenCoordinates LargeOrderSquareInterface LargeOrderStrongPaths LargeOrderFiveAnchors
open FiberPairExtension
open private BoolTwins from LargeOrderSquareInterface

private theorem factor : ∀ B : I → I → Bool, B 0 0=true → BoolTwins B →
    (∀ i, FiberRectangles.degree (B i)=2) → (∀ j, FiberRectangles.degree (fun i => B i j)=2) →
    ∀ i j, B i j=decide (B i 0=B 0 j) := by native_decide

private theorem repeated : ∀ X : I → I → Bool, (∀ i, X i 0=true) →
    (∀ i, FiberRectangles.degree (X i)=2) → ∃ i j, i≠j ∧ X i=X j := by native_decide

private theorem score : ∀ (X : I → Bool) (u v : Bool), FiberRectangles.degree X=2 →
    (∑ k, if X k=u ∧ X k=v then 1 else 0 : Nat) = (if u=v then 2 else 0) := by native_decide

variable {n l r v : Nat} {c : Fin n → Fin n → Nat}

private theorem direction (law : Laws c c) (F : Shore c l I) (S : Shore c r I)
    (pin : ¬Pin F S) (uniform : ¬∀ i j, colors F S i j=colors F S 0 0)
    (twin : twins c l r) :
    ∃ X Y : I → Bool, X 0=true ∧ Y 0=true ∧ FiberRectangles.degree X=2 ∧ FiberRectangles.degree Y=2 ∧
      ∀ i j x y, colors F S i j=colors F S x y ↔ (X i=Y j ↔ X x=Y y) := by
  obtain ⟨B,zero,rows,cols,same⟩ := binary law F S pin uniform
  have tw : BoolTwins B := ⟨fun i x j hit y => (same i y x y).mpr
    (twin.1 (F i) (F x) (S j) ((same i j x j).mp hit) (S y)),
    fun i j y hit x => (same x j x y).mpr (twin.2 (F i) (S j) (S y) ((same i j i y).mp hit) (F x))⟩
  refine ⟨fun i => B i 0,B 0,zero,zero,cols 0,rows 0,fun i j x y => ?_⟩
  rw [←same i j x y,factor B zero tw rows cols i j,factor B zero tw rows cols x y]
  exact decide_eq_decide

theorem uniform_forces (law : Laws c c) (F : Shore c l I) (S : Shore c r I)
    (uniform : ∀ i j, colors F S i j=colors F S 0 0) (z : Fin n) :
    Forced c (atPoint F 0) (atPoint S 0) z := by
  intro x y t h k
  let i := F.symm ⟨x,(law.last (law.rev h)).trans (F 0).property⟩
  let j := S.symm ⟨y,(law.last k).trans (S 0).property⟩
  simpa only [i,j,colors,atPoint,Equiv.apply_symm_apply] using uniform i j

private theorem chord (law : Laws c c) (P : Shore c v I) (F : Shore c l I) (S : Shore c r I)
    (X Y Z : I → Bool) (x0 : X 0=true) (y0 : Y 0=true) (z0 : Z 0=true)
    (x2 : FiberRectangles.degree X=2) (z2 : FiberRectangles.degree Z=2)
    (a : ∀ i j x y, colors P F i j=colors P F x y ↔ (X i=Y j ↔ X x=Y y))
    (b : ∀ i j x y, colors P S i j=colors P S x y ↔ (X i=Z j ↔ X x=Z y))
    (pin : ¬Pin F S) (uniform : ¬∀ i j, colors F S i j=colors F S 0 0) :
    Forced c (atPoint F 0) (atPoint S 0) (atPoint P 0) := by
  classical
  let A := fun i j => decide (X i=Y j)
  let B := fun i j => decide (X i=Z j)
  have left : Block P P F F A A := fun ⦃i j x y⦄ h => Bool.decide_congr ((a i j x y).mp h)
  have right : Block P P S S B B := fun ⦃i j x y⦄ h => Bool.decide_congr ((b i j x y).mp h)
  let m := fun i j => if Y i=Z j then 2 else 0
  have common : Block F F S S m m := by
    have fold := Block.fold law (Block.flip law left) right (fun a b => if a=true ∧ b=true then 1 else 0)
    have form (i j) : (∑ t, if A t i=true ∧ B t j=true then 1 else 0 : Nat)=m i j := by
      simpa only [A,B,decide_eq_true_eq] using score X (Y i) (Z j) x2
    exact fun ⦃i j x y⦄ h => (form i j).symm.trans ((fold h).trans (form x y))
  obtain ⟨bit,_,_,_,same⟩ := binary law F S pin uniform
  obtain ⟨j,zj⟩ : ∃ j, Z j=false := by
    by_contra! none
    have all : Z=fun _ => true := funext (fun i => by simpa using none i)
    rw [all] at z2
    exact (by decide : FiberRectangles.degree (fun _ : I => true)≠2) z2
  have neq : m 0 0 ≠ m 0 j := by simp [m,y0,z0,zj]
  have sep : bit 0 0 ≠ bit 0 j := fun h => neq (common ((same 0 0 0 j).mp h))
  intro x y t h k
  let i := F.symm ⟨x,(law.last (law.rev h)).trans (F 0).property⟩
  let e := P.symm ⟨t,(law.last h).trans (P 0).property⟩
  let q := S.symm ⟨y,(law.last k).trans (S 0).property⟩
  have ixy : colors P F e i=colors P F 0 0 := by simpa only [colors,i,e,atPoint,Equiv.apply_symm_apply] using law.rev h
  have jxy : colors P S e q=colors P S 0 0 := by simpa only [colors,q,e,atPoint,Equiv.apply_symm_apply] using k
  have xy : Y i=Z q := (((a e i 0 0).mp ixy).mpr (x0.trans y0.symm)).symm.trans
    (((b e q 0 0).mp jxy).mpr (x0.trans z0.symm))
  have good : m i q=m 0 0 := by simp [m,xy,y0,z0]
  have exclude : bit i q≠bit 0 j := fun hit => neq (good.symm.trans (common ((same i q 0 j).mp hit)))
  have eq : bit i q=bit 0 0 := (by decide : ∀ a b z : Bool, a≠z → b≠z → a=b) _ _ _ exclude sep
  simpa only [colors,i,q,atPoint,Equiv.apply_symm_apply] using (same i q 0 0).mp eq

/-- Four nonconstant twin interfaces at a four-point fiber induce only
three distinct partitions into pairs. Two neighbors therefore determine
their cross color from their two colors to the common anchor. -/
theorem four_neighbors {L : I → Nat} (law : Laws c c) (P : Shore c v I) (F : ∀ i : I, Shore c (L i) I)
    (no : ∀ i, ¬Pin P (F i)) (nonuniform : ∀ i, ¬∀ a b, colors P (F i) a b=colors P (F i) 0 0)
    (tw : ∀ i, twins c v (L i))
    (nop : ∀ i j, i≠j → ¬Pin (F i) (F j))
    (nonu : ∀ i j, i≠j → ¬∀ a b, colors (F i) (F j) a b=colors (F i) (F j) 0 0) :
    ∃ i j : I, i≠j ∧ Forced c (atPoint (F i) 0) (atPoint (F j) 0) (atPoint P 0) := by
  choose X Y x0 y0 x2 y2 eq using fun i => direction law P (F i) (no i) (nonuniform i) (tw i)
  obtain ⟨i,j,ne,same⟩ := repeated X x0 x2
  refine ⟨i,j,ne,chord law P (F i) (F j) (X i) (Y i) (Y j) (x0 i) (y0 i) (y0 j) (x2 i) (y2 j)
    (eq i) ?_ (nop i j ne) (nonu i j ne)⟩
  rw [same]; exact eq j

end QGI.Coherent.LargeOrderFourDirections
