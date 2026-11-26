import RegionalPlanar
import SmallFiberExtension
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
namespace QGI.Coherent.SixSixAtoms
open StrategyColorLaws SmallFiberExtension
open FourTwelveFunctional (source)
open private incompatible from RegionalPlanar
open private bundle from SmallFiberExtension

/-- Three partitions of the identity admit choices with nonzero products
on all three directed edges. This uses no trace or mutual commutativity. -/
theorem triangle {A I J K : Type} [Semiring A] [Nontrivial A] [Fintype I] [Fintype J] [Fintype K]
    (P : I → A) (Q : J → A) (S : K → A) (oneP : ∑ i, P i=1)
    (oneQ : ∑ i, Q i=1) (oneS : ∑ i, S i=1) (idem : ∀ i, P i * P i = P i) :
    ∃ i j k, P i * Q j ≠ 0 ∧ Q j * S k ≠ 0 ∧ S k * P i ≠ 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, P i ≠ 0 := by
    by_contra! h
    simp [h] at oneP
  have row : ∑ j, P i * Q j * P i = P i := by
    rw [←Finset.sum_mul,←Finset.mul_sum,oneQ,mul_one,idem]
  obtain ⟨j,hj⟩ : ∃ j, P i * Q j * P i ≠ 0 := by
    by_contra! h
    exact hi (row.symm.trans (by simp [h]))
  have entry : ∑ k, (P i * Q j) * S k * P i = P i * Q j * P i := by
    rw [←Finset.sum_mul,←Finset.mul_sum,oneS,mul_one]
  obtain ⟨k,hk⟩ : ∃ k, (P i * Q j) * S k * P i ≠ 0 := by
    by_contra! h
    exact hj (entry.symm.trans (by simp [h]))
  exact ⟨i,j,k,fun h => hk (by rw [h,zero_mul,zero_mul]),
    fun h => hk (by rw [mul_assoc (P i) (Q j),h,mul_zero,zero_mul]),
    fun h => hk (by rw [mul_assoc (P i * Q j),h,mul_zero])⟩

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

/-- Each local operator chooses an image for every point of this block.
Absorption on both sides records compatibility with the original quantum
permutation on those points. -/
structure Choices {X : Type} (pt : X → Fin n) (tag : X → Fin 3) (block : Fin 3) where
  size : Nat
  op : Fin size → (ColorTensor.space p →L[ℂ] ColorTensor.space p)
  pick : Fin size → X → Fin n
  total : ∑ i, op i = 1
  idem : ∀ i, op i * op i = op i
  right : ∀ i x, tag x=block → op i * ColorTensor.P p (pt x) (pick i x) = op i
  left : ∀ i x, tag x=block → ColorTensor.P p (pt x) (pick i x) * op i = op i

private theorem compatible {X} {pt : X → Fin n} {tag : X → Fin 3} {s t : Fin 3}
    (A : Choices p pt tag s) (B : Choices p pt tag t) {i j} (nz : A.op i * B.op j ≠ 0)
    {x y} (hx : tag x=s) (hy : tag y=t) :
    source G (pt x) (pt y) = targetName p (A.pick i x) (B.pick j y) := by
  by_contra bad
  have zero := incompatible p _ _ _ _ bad
  apply nz
  calc A.op i * B.op j
      = (A.op i * ColorTensor.P p (pt x) (A.pick i x)) *
        (ColorTensor.P p (pt y) (B.pick j y) * B.op j) := by rw [A.right _ _ hx,B.left _ _ hy]
    _ = A.op i * (ColorTensor.P p (pt x) (A.pick i x) * ColorTensor.P p (pt y) (B.pick j y)) * B.op j := by
      simp only [mul_assoc]
    _ = 0 := by rw [zero,mul_zero,zero_mul]

/-- Three locally decomposed blocks realize every original ordered color
on their union, including colors between distinct blocks. -/
theorem realize (reg : Nat → Prop) (tag : Region (source G) reg → Fin 3)
    (L : ∀ k, Choices p Subtype.val tag k) : Realizes p reg := by
  obtain ⟨i,j,k,ab,bc,ca⟩ := triangle (L 0).op (L 1).op (L 2).op
    (L 0).total (L 1).total (L 2).total (L 0).idem
  let pick : (b : Fin 3) → Fin (L b).size := Fin.cons i (Fin.cons j (Fin.cons k (fun t => t.elim0)))
  have aa : (L 0).op i * (L 0).op i ≠ 0 := by rw [(L 0).idem]; exact fun h => ab (by rw [h,zero_mul])
  have bb : (L 1).op j * (L 1).op j ≠ 0 := by rw [(L 1).idem]; exact fun h => bc (by rw [h,zero_mul])
  have cc : (L 2).op k * (L 2).op k ≠ 0 := by rw [(L 2).idem]; exact fun h => ca (by rw [h,zero_mul])
  have either (a b : Fin 3) : (L a).op (pick a) * (L b).op (pick b) ≠ 0 ∨
      (L b).op (pick b) * (L a).op (pick a) ≠ 0 := by
    fin_cases a <;> fin_cases b <;>
      first | exact Or.inl aa | exact Or.inl bb | exact Or.inl cc |
              exact Or.inl ab | exact Or.inl bc | exact Or.inl ca |
              exact Or.inr ab | exact Or.inr bc | exact Or.inr ca
  let out := fun x => (L (tag x)).pick (pick (tag x)) x
  have names (x y) : source G x.val y.val=targetName p (out x) (out y) := by
    rcases either (tag x) (tag y) with forward | reverse
    · exact compatible p _ _ forward rfl rfl
    · exact common_transpose p (compatible p _ _ reverse (x:=y) (y:=x) rfl rfl)
  obtain ⟨e,he⟩ := bundle p reg out names
  exact ⟨e,fun i j => (names i j).trans (congrArg₂ (targetName p) (he i).symm (he j).symm)⟩

end QGI.Coherent.SixSixAtoms
