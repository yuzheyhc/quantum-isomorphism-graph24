import LargeOrderFourDirections
import LargeOrderTetraInterfaces

noncomputable section
namespace QGI.Coherent.LargeOrderSixDirections
open SixTenCoordinates LargeOrderSquareInterface LargeOrderStrongPaths LargeOrderTetraInterfaces LargeOrderFiveAnchors
open FourSixSix (E)
open private two from FourSixInterfaces
open private twins from RegionalFourFourEight

private theorem rank_two {A : Type} (u v : A → Bool) (h : ∀ x y, u x=u y → v x=v y)
    (a b : A) (diff : v a≠v b) (x y : A) : u x=u y ↔ v x=v y := by
  refine ⟨h x y,fun eq => ?_⟩
  have ab : u a≠u b := fun e => diff (h a b e)
  have each (z) : u z=u a ∨ u z=u b :=
    (by decide : ∀ x a b : Bool, a≠b → x=a ∨ x=b) _ _ _ ab
  rcases each x with xa|xb <;> rcases each y with ya|yb
  · exact xa.trans ya.symm
  · exact (diff ((h _ _ xa).symm.trans (eq.trans (h _ _ yb)))).elim
  · exact (diff ((h _ _ ya).symm.trans (eq.symm.trans (h _ _ xb)))).elim
  · exact xb.trans yb.symm

variable {n l r v : Nat} {c : Fin n → Fin n → Nat}

structure Direction (F : Shore c l I) (Y : Shore c v E) where
  left : I → Bool
  right : E → Bool
  lzero : left 0=true
  rzero : right 0=true
  lsize : FiberRectangles.degree left=2
  rsize : FiberRectangles.degree right=3
  names : ∀ i j x y, raw F Y i j=raw F Y x y ↔ (left i=right j ↔ left x=right y)

theorem form (law : Laws c c) (F : Shore c l I) (Y : Shore c v E)
    (tw : FiberPairExtension.twins c l v) (notUniform : ¬∀ i j, raw F Y i j=raw F Y 0 0) :
    Nonempty (Direction F Y) := by
  let M := fun i j => raw F Y i j
  let B (s : Nat) (i j) := decide (M i j=s)
  have base (s : Nat) : Shape F Y (B s) := fun ⦃_ _ _ _⦄ h => congrArg (fun n => decide (n=s)) h
  have reg : FiberRectangles.BiregularColors M := fun s =>
    ⟨_,_,fun i => Block.degree_eq law (base s) i 0,fun j => Block.degree_eq law (Block.flip law (base s)) j 0⟩
  rcases two reg with ⟨t,all⟩|⟨s,t,ne,pal,rows,cols⟩
  · exact (notUniform (fun i j => (all i j).trans (all 0 0).symm)).elim
  have same (i j x y) : M i j=M x y ↔ B s i j=B s x y := by
    rcases pal i j with h|h <;> rcases pal x y with k|k <;> simp [B,h,k,ne,Ne.symm ne]
  let tag (a : Bool) := decide (a=B s 0 0)
  let X := fun i => tag (B s i 0)
  let Z := fun j => tag (B s 0 j)
  have inv : Function.Injective tag := (by decide : ∀ q : Bool, Function.Injective (fun a : Bool => decide (a=q))) _
  have right' (i j) : B s i j=B s 0 0 ↔ X i=Z j := by
    rw [show X i=Z j ↔ B s i 0=B s 0 j from inv.eq_iff]
    by_cases hit : B s i 0=B s 0 0
    · have eq := (same i j 0 j).mp (tw.1 (F i) (F 0) (Y 0) ((same i 0 0 0).mpr hit) (Y j))
      rw [hit,eq]; exact eq_comm
    · have inv' : B s i j≠B s 0 j := fun eq => hit ((same i 0 0 0).mp
        (tw.1 (F i) (F 0) (Y j) ((same i j 0 j).mpr eq) (Y 0)))
      exact (by decide : ∀ a b c d : Bool, a≠b → c≠d → (c=b ↔ a=d)) _ _ _ _ hit inv'
  have zd (i j) : decide (X i=Z j)=tag (B s i j) := Bool.decide_congr (right' i j).symm
  have bal : ∀ (u : I → Bool) (a : Bool), FiberRectangles.degree u=2 → FiberRectangles.degree (fun i => decide (u i=a))=2 := by decide
  have six : ∀ (u : E → Bool) (a : Bool), FiberRectangles.degree u=3 → FiberRectangles.degree (fun i => decide (u i=a))=3 := by native_decide
  refine ⟨⟨X,Z,by simp [X,tag],by simp [Z,tag],bal _ _ (cols 0),six _ _ (rows 0),fun i j x y => ?_⟩⟩
  calc
    _ ↔ B s i j=B s x y := same i j x y
    _ ↔ tag (B s i j)=tag (B s x y) := inv.eq_iff.symm
    _ ↔ _ := by rw [←zd,←zd]; exact decide_eq_decide

private def oddMeet (u v : E → Bool) (a b : Bool) : Nat := ∑ j, if u j=a ∧ v j=b then 1 else 0

private theorem odd : ∀ (u v : E → Bool), FiberRectangles.degree u=3 → FiberRectangles.degree v=3 →
    ∀ a b x y : Bool, oddMeet u v a b=oddMeet u v x y → (a=b ↔ x=y) := by native_decide

/-- Two equal half-sizes of three give complementary intersection counts.
Their parity forces the cut between either pair of four-point neighbors. -/
theorem square_names (law : Laws c c) (F : Shore c l I) (S : Shore c r I) (Y : Shore c v E)
    (A : Direction F Y) (B : Direction S Y) (pin : ¬Pin F S) (nonu : ¬∀ i j, raw F S i j=raw F S 0 0) :
    ∀ i j x y, raw F S i j=raw F S x y ↔ (A.left i=B.left j ↔ A.left x=B.left y) := by
  let op (i j) := decide (A.left i=A.right j)
  let oq (i j) := decide (B.left i=B.right j)
  have fa : Shape F Y op := fun ⦃i j x y⦄ h => Bool.decide_congr ((A.names i j x y).mp h)
  have fb : Shape S Y oq := fun ⦃i j x y⦄ h => Bool.decide_congr ((B.names i j x y).mp h)
  have paired := Block.fold law fa (Block.flip law fb) (fun a b => if a=true ∧ b=true then 1 else 0)
  have mass (i j) : (∑ z, if op i z=true ∧ oq j z=true then 1 else 0 : Nat)=oddMeet A.right B.right (A.left i) (B.left j) := by
    apply Finset.sum_congr rfl
    intro z _
    simp only [op,oq,decide_eq_true_eq]
    exact (by decide : ∀ a b c d : Bool, (if a=b ∧ c=d then 1 else 0 : Nat) =
      (if b=a ∧ d=c then 1 else 0)) _ _ _ _
  obtain ⟨color,_,_,_,eq⟩ := binary law F S pin nonu
  let code := fun z : I × I => decide (A.left z.1=B.left z.2)
  have forward (p q : I × I) (hit : color p.1 p.2=color q.1 q.2) : code p=code q := by
    apply Bool.decide_congr
    exact odd A.right B.right A.rsize B.rsize _ _ _ _ ((mass _ _).symm.trans
      ((paired ((eq _ _ _ _).mp hit)).trans (mass _ _)))
  obtain ⟨j,hj⟩ := (by decide : ∀ z : I → Bool, FiberRectangles.degree z=2 → ∃ j, z j=false) _ B.lsize
  have diff : code (0,0)≠code (0,j) := by simp [code,A.lzero,B.lzero,hj]
  intro i j x y
  exact (eq i j x y).symm.trans ((rank_two (fun z : I × I => color z.1 z.2) code forward _ _ diff (i,j) (x,y)).trans decide_eq_decide)

end QGI.Coherent.LargeOrderSixDirections
