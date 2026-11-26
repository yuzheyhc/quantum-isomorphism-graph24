import HalfRectangle

namespace QGI.Coherent.TenTenMoments
open SixTenCoordinates
abbrev V := Fin 10
abbrev Inc := V → V → Bool
abbrev Mat := Matrix V V Nat

def indicator (B : Inc) : Mat := fun i j => if B i j then 1 else 0
def gram (B : Inc) : Mat := indicator B * (indicator B).transpose
def walks (B : Inc) : Mat := gram B * indicator B

private theorem gram_block {n l r} {c : Fin n → Fin n → Nat} (law : Laws c c) {X : Shore c l V} {Y : Shore c r V}
    {B : Inc} (b : Block X X Y Y B B) : Block X X X X (gram B) (gram B) := by
  apply Block.fold law b (Block.flip law b) (fun u v => (if u then 1 else 0)*(if v then 1 else 0))

private theorem walk_block {n l r} {c : Fin n → Fin n → Nat} (law : Laws c c) {X : Shore c l V} {Y : Shore c r V}
    {B : Inc} (b : Block X X Y Y B B) : Block X X Y Y (walks B) (walks B) := by
  apply Block.fold law (gram_block law b) b (fun k u => k*(if u then 1 else 0))

theorem two_scores {n l r} {c : Fin n → Fin n → Nat} (law : Laws c c) (X : Shore c l V) (Y : Shore c r V)
    (v w : Nat) (palette : ∀ i j, c (atPoint X i) (atPoint Y j)=v ∨ c (atPoint X i) (atPoint Y j)=w)
    (B : Inc) (bits : ∀ i j, B i j=true ↔ c (atPoint X i) (atPoint Y j)=v)
    (present : ∃ i j, B i j=true) (absent : ∃ i j, B i j=false) :
    ∃ a b : Nat, ∀ i j, walks B i j=if B i j then a else b := by
  obtain ⟨i₀,j₀,h₀⟩ := present
  obtain ⟨i₁,j₁,h₁⟩ := absent
  have named : Block X X Y Y B B := by
    intro i j k t h; apply Bool.eq_iff_iff.mpr; rw [bits,bits,h]
  have walk := walk_block law named
  have off (i j) (h : B i j=false) : c (atPoint X i) (atPoint Y j)=w :=
    (palette i j).resolve_left (fun e => Bool.noConfusion (h.symm.trans ((bits i j).mpr e)))
  refine ⟨walks B i₀ j₀,walks B i₁ j₁,?_⟩
  intro i j
  cases h : B i j with
  | false => exact walk ((off i j h).trans (off i₁ j₁ h₁).symm)
  | true => exact walk (((bits i j).mp h).trans ((bits i₀ j₀).mp h₀).symm)

private theorem masked_sum (t : V → Bool) (a b : Nat) :
    (∑ j, if t j then a else b)=FiberRectangles.degree t*a+(10-FiberRectangles.degree t)*b := by
  classical
  let s := Finset.univ.filter (fun j => t j=true)
  have yes : ∀ j∈s, (if t j then a else b)=a := fun j hj => if_pos (Finset.mem_filter.mp hj).2
  have no : ∀ j∈sᶜ, (if t j then a else b)=b := fun j hj => if_neg (fun h => Finset.mem_compl.mp hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
  rw [←Finset.sum_add_sum_compl s,Finset.sum_congr rfl yes,Finset.sum_congr rfl no,Finset.sum_const,Finset.sum_const,Finset.card_compl]
  rfl

private theorem sumMul (A C : Mat) (k : Nat) (h : ∀ j, ∑ z, C j z=k) (i : V) :
      ∑ j, (A*C) i j=(∑ j, A i j)*k := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [←Finset.mul_sum,h,Finset.sum_mul]

theorem gram_sum {B : Inc} {d : Nat} (rows : ∀ i, FiberRectangles.degree (B i)=d)
    (cols : ∀ j, FiberRectangles.degree (fun i => B i j)=d) (i : V) : ∑ j, gram B i j=d*d := by
  have rowI : ∑ j, indicator B i j=d := by simpa only [indicator,Finset.sum_boole,FiberRectangles.degree] using rows i
  have colI (j : V) : ∑ k, (indicator B).transpose j k=d := by
    simpa only [Matrix.transpose_apply,indicator,Finset.sum_boole,FiberRectangles.degree] using cols j
  exact (sumMul (indicator B) (indicator B).transpose d colI i).trans (by rw [rowI])

theorem gram_overlap (B : Inc) (i j) : gram B i j=Block.overlap B i j := by
  have term (k : V) : indicator B i k*indicator B j k=(if B i k=true ∧ B j k=true then 1 else 0 : Nat) := by
    cases h : B i k <;> cases t : B j k <;> simp [indicator,h,t]
  simpa only [gram,Matrix.mul_apply,Matrix.transpose_apply,term,Finset.sum_boole,Nat.cast_id,Block.overlap]

theorem moments {B : Inc} {d a b : Nat}
    (rows : ∀ i, FiberRectangles.degree (B i)=d) (cols : ∀ j, FiberRectangles.degree (fun i => B i j)=d)
    (weight : ∀ i j, walks B i j=if B i j then a else b) :
    d*a+(10-d)*b=d^3 ∧ ∀ i j, (gram B * gram B) i j+b*(gram B i j)=a*(gram B i j)+b*d := by
  let I := indicator B
  have rowI (i) : ∑ j, I i j=d := by simpa only [I,indicator,Finset.sum_boole,FiberRectangles.degree] using rows i
  have sumGram (i : V) : ∑ j, gram B i j=d*d := gram_sum rows cols i
  constructor
  · have same := sumMul (gram B) I d rowI 0
    change (∑ j, walks B 0 j)=_ at same
    simp only [sumGram,weight,masked_sum,rows] at same
    simpa [pow_succ] using same
  · intro i j
    have assoc : (gram B * gram B) i j=(walks B * I.transpose) i j := by
      exact congrArg (fun m : Mat => m i j) (Matrix.mul_assoc (gram B) I I.transpose).symm
    have term (k : V) : walks B i k*I j k+b*(I i k*I j k)=a*(I i k*I j k)+b*I j k := by
      rw [weight]; cases h : B i k <;> cases t : B j k <;> simp [I,indicator,h,t]
    change _+b*(∑ k, I i k*I j k)=a*(∑ k, I i k*I j k)+b*d
    rw [assoc,Matrix.mul_apply,←rowI j,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => term k)

end QGI.Coherent.TenTenMoments
