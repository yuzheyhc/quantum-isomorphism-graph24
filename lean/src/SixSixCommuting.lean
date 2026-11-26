import SixSixAtoms

noncomputable section
namespace QGI.Coherent.SixSixAtoms
open SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)

private structure Family {A X Y : Type} [Semiring A] (P : X → Y → A) (s : Finset X) where
  size : Nat
  op : Fin size → A
  image : Fin size → X → Y
  total : ∑ k, op k=1
  idem : ∀ k, op k * op k=op k
  comm : ∀ k x y, Commute (op k) (P x y)
  support : ∀ k x, x ∈ s → op k * P x (image k x)=op k

private theorem family {A X Y : Type} [Semiring A] [Fintype Y] (fallback : Y) (P : X → Y → A)
    (row : ∀ x, ∑ y, P x y=1) (idem : ∀ x y, P x y * P x y=P x y)
    (localComm : ∀ x y u v, Commute (P x y) (P u v)) (s : Finset X) : Nonempty (Family P s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨⟨1,fun _ => 1,fun _ _ => fallback,by simp,by simp,by simp,by simp⟩⟩
  | @insert x s outside ih =>
    obtain ⟨F⟩ := ih
    let e := (Fintype.equivFin (Fin F.size × Y)).symm
    let op := fun k => F.op (e k).1 * P x (e k).2
    let send := fun k z => if z=x then (e k).2 else F.image (e k).1 z
    refine ⟨⟨_,op,send,?_,?_,?_,?_⟩⟩
    · calc ∑ k, op k = ∑ v : Fin F.size × Y, F.op v.1 * P x v.2 :=
            e.sum_comp (fun v : Fin F.size × Y => F.op v.1 * P x v.2)
          _ = 1 := by simp only [Fintype.sum_prod_type,←Finset.mul_sum,row,mul_one,F.total]
    · intro k
      let a := F.op (e k).1
      let b := P x (e k).2
      have commute : b*a=a*b := (F.comm _ _ _).eq.symm
      change (a*b)*(a*b)=a*b
      calc (a*b)*(a*b) = a*(b*a)*b := by simp only [mul_assoc]
           _ = (a*a)*(b*b) := by rw [commute]; simp only [mul_assoc]
           _ = a*b := by rw [show a*a=a from F.idem _,show b*b=b from idem _ _]
    · intro k z b
      exact (F.comm _ z b).mul_left (localComm _ _ z b)
    · intro k z hz
      rcases Finset.mem_insert.mp hz with rfl | mem
      · simp only [op,send,if_pos rfl,mul_assoc,idem]
      · have ne : z≠x := fun eq => outside (eq ▸ mem)
        change (F.op (e k).1 * P x (e k).2) * P z (send k z) = _
        rw [show send k z=F.image (e k).1 z from if_neg ne,mul_assoc,(localComm x _ z _).eq,
          ←mul_assoc,F.support _ _ mem]

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

theorem choices_of_commuting {X : Type} [Fintype X] (fallback : Fin n) (pt : X → Fin n)
    (tag : X → Fin 3) (b : Fin 3)
    (comm : ∀ x z, tag x=b → tag z=b → ∀ y v,
      Commute (ColorTensor.P p (pt x) y) (ColorTensor.P p (pt z) v)) :
    Nonempty (Choices p pt tag b) := by
  classical
  let S := {x : X // tag x=b}
  let M := fun (x : S) (z : Fin n) => ColorTensor.P p (pt x.val) z
  obtain ⟨proj,rows,_⟩ := ColorTensor.quantumPermutation p
  obtain ⟨F⟩ := family fallback M (fun x => rows (pt x.val)) (fun x z => (proj (pt x.val) z).1)
    (fun x y z w => comm x.val z.val x.property z.property y w) Finset.univ
  let send := fun (i : Fin F.size) (x : X) => if h : tag x=b then F.image i ⟨x,h⟩ else fallback
  refine ⟨⟨F.size,F.op,send,F.total,F.idem,?_,?_⟩⟩
  · intro i x hx
    simpa only [send,dif_pos hx] using F.support i (⟨x,hx⟩ : S) (Finset.mem_univ _)
  · intro i x hx
    rw [show send i x=F.image i ⟨x,hx⟩ from dif_pos hx]
    exact ((F.comm i (⟨x,hx⟩ : S) _).eq.symm).trans (F.support i ⟨x,hx⟩ (Finset.mem_univ _))

/-- In any ambient order, three internally commuting fibers admit a common
point realization of all named binary relations on their union. -/
theorem realize_of_commuting (reg : Nat → Prop) (tag : Region (source G) reg → Fin 3) (fallback : Fin n)
    (comm : ∀ x z : Region (source G) reg, tag x=tag z → ∀ y v,
      Commute (ColorTensor.P p x.val y) (ColorTensor.P p z.val v)) : Realizes p reg := by
  classical
  let L := fun b : Fin 3 => Classical.choice (choices_of_commuting p fallback Subtype.val tag b
    (fun x z hx hz => comm x z (hx.trans hz.symm)))
  exact realize p reg tag L

end QGI.Coherent.SixSixAtoms
