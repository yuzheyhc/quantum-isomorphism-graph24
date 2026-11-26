import SixSixCommuting
import RegionalTetraOperators

noncomputable section
namespace QGI.Coherent.RegionalEightTwelveAtoms
open Intertwiner Synchrony StrategyColorLaws SmallFiberExtension SmallUnion
open FourTwelveFunctional (source)
open private family Family from SixSixCommuting
open private bundle from SmallFiberExtension
open private sums from Intertwiner

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

/-- Operators commute within each of two groups of source rows. A nonzero
product of two local permutation atoms realizes every original name. -/
theorem realize {X : Type} [Fintype X] (rows : X → Fin n) (side : X → Bool) (fallback : Fin n)
    (reg : Nat → Prop) (cover : ∀ z : Region (source G) reg, ∃ x, rows x=z.val)
    (comm : ∀ x t : X, side x=side t → ∀ a b : Fin n, Commute (U p (rows x) a) (U p (rows t) b)) :
    Realizes p reg := by
  classical
  let A := Module.End ℂ (cyclic p)
  let V (b : Bool) := {x : X // side x=b}
  let M (s : Bool) (x : V s) (a : Fin n) : A := U p (rows x.val) a
  have build (s : Bool) : Nonempty (Family (M s) Finset.univ) := by
    exact family fallback (M s) (fun x => LinearMap.ext (fun ξ => by
      change (∑ a, U p (rows x.val) a) ξ=ξ
      rw [LinearMap.sum_apply]
      exact (sums p (rows x.val) ξ).1))
      (fun x y => (restricted_projection p _ _).1) (fun x a t b => comm _ _ (x.property.trans t.property.symm) a b) Finset.univ
  obtain ⟨⟨nc,C,imC,totalC,idemC,commC,holdC⟩⟩ := build false
  obtain ⟨⟨nd,D,imD,totalD,idemD,commD,holdD⟩⟩ := build true
  have one : (1 : A)≠0 := by
    intro z
    exact psi_ne_zero p (congrArg Subtype.val (congrArg (fun e : A => e ⟨p.psi,psi_mem p⟩) z))
  obtain ⟨i,j,hit⟩ : ∃ i j, C i*D j≠0 := by
    by_contra! z
    apply one
    calc (1 : A) = (∑ i, C i)*(∑ j, D j) := by rw [totalC,totalD,one_mul]
         _ = ∑ i, ∑ j, C i*D j := by rw [Finset.sum_mul]; simp only [Finset.mul_sum]
         _ = 0 := by simp [z]
  have leftNZ : C i≠0 := fun z => hit (by rw [z,zero_mul])
  have rightNZ : D j≠0 := fun z => hit (by rw [z,mul_zero])
  have name {x t a b : Fin n} {L R : A} (nz : L*R≠0) (lx : L * U p x a=L) (tr : U p t b * R=R) :
      source G x t=targetName p a b := by
    apply (associated p).mpr
    apply StrategyColors.maps_support
    intro zero
    change U p x a * U p t b=0 at zero
    exact nz (calc L*R = (L*U p x a)*(U p t b*R) := by rw [lx,tr]
                   _ = L*(U p x a*U p t b)*R := by simp only [mul_assoc]
                   _ = 0 := by rw [zero,mul_zero,zero_mul])
  let f (x : X) := if h : side x=false then imC i ⟨x,h⟩ else imD j ⟨x,Bool.eq_true_of_not_eq_false h⟩
  have falseR (x : X) (h : side x=false) : C i*U p (rows x) (f x)=C i := by
    simpa only [f,dif_pos h] using holdC i ⟨x,h⟩ (Finset.mem_univ _)
  have falseL (x : X) (h : side x=false) : U p (rows x) (f x)*C i=C i := by
    rw [show f x=imC i ⟨x,h⟩ from dif_pos h]
    exact (commC i ⟨x,h⟩ _).eq.symm.trans (holdC i ⟨x,h⟩ (Finset.mem_univ _))
  have trueR (x : X) (h : side x=true) : D j*U p (rows x) (f x)=D j := by
    have ne : side x≠false := by simp [h]
    simpa only [f,dif_neg ne] using holdD j ⟨x,h⟩ (Finset.mem_univ _)
  have trueL (x : X) (h : side x=true) : U p (rows x) (f x)*D j=D j := by
    have ne : side x≠false := by simp [h]
    rw [show f x=imD j ⟨x,h⟩ from dif_neg ne]
    exact (commD j ⟨x,h⟩ _).eq.symm.trans (holdD j ⟨x,h⟩ (Finset.mem_univ _))
  have all (x t) : source G (rows x) (rows t)=targetName p (f x) (f t) := by
    cases hx : side x <;> cases ht : side t
    · exact name (by rw [idemC]; exact leftNZ) (falseR _ hx) (falseL _ ht)
    · exact name hit (falseR _ hx) (trueL _ ht)
    · exact common_transpose p (name hit (falseR _ ht) (trueL _ hx))
    · exact name (by rw [idemD]; exact rightNZ) (trueR _ hx) (trueL _ ht)
  choose pick eq using cover
  have names (x t) : source G x.val t.val=targetName p (f (pick x)) (f (pick t)) := by rw [←eq x,←eq t]; exact all _ _
  obtain ⟨e,he⟩ := bundle p reg (fun x => f (pick x)) names
  exact ⟨e,fun x t => by rw [he,he]; exact names _ _⟩

end QGI.Coherent.RegionalEightTwelveAtoms

