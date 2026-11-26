import SixSixCycle
import NineNinePappus
import RegionalThreeClasses

noncomputable section
namespace QGI.Literature

/-- Banica and Bichon, *Quantum automorphism groups of vertex-transitive
graphs of order ≤ 11*, J. Algebraic Combin. 26 (2007), §7, classification
table (p. 19 in the author PDF), rows of order nine, modulo complementation.
Corollary 3.1(3)
and Theorem 5.1. Among the table's representatives, only the chorded
cycle C₉(3) and the 3-by-3 torus have valency four. Both quantum groups
are classical. Complementation preserves the magic-unitary intertwiner
because every magic unitary commutes with the identity and all-ones
matrices. A finite family of self-adjoint projections with sum one is
pairwise orthogonal by positivity, so the displayed row and column
hypotheses give a magic unitary. https://lmbp.uca.fr/~bichon/qgrc.pdf -/
axiom banica_bichon_nine_valency_four {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nontrivial E] (edge : Fin 9 → Fin 9 → Bool)
    (simple : ∀ i, edge i i=false) (sym : ∀ i j, edge i j=edge j i)
    (regular : ∀ i,FiberRectangles.degree (edge i)=4)
    (transitive : ∀ x y, ∃ e : Equiv.Perm (Fin 9), e x=y ∧ ∀ i j, edge (e i) (e j)=edge i j)
    (U : Fin 9 → Fin 9 → (E →L[ℂ] E)) (proj : ∀ i j, U i j*U i j=U i j ∧ U i j=(U i j).adjoint)
    (row : ∀ i, ∑ j, U i j=1) (col : ∀ j, ∑ i, U i j=1)
    (inter : ∀ i b, (∑ a, if edge a b then U i a else 0)=∑ j, if edge i j then U j b else 0) :
    ∀ i a j b, Commute (U i a) (U j b)

end QGI.Literature

namespace QGI.Coherent.NinePointRigidity
open FourTwelveFunctional (source)
open SixTenCoordinates (Shore atPoint Block)
open SmallUnion SmallFiberExtension StrategyColorLaws
open private incompatible outside from RegionalPlanar

/-- A named undirected four-regular graph on a nine-point shore forces
the entries in that entire shore of the original strategy to commute. -/
theorem commuting {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) {l} (A : Shore (source G) l (Fin 9))
    (g : Fin 9 → Fin 9 → Bool) (simple : ∀ i, g i i=false) (sym : ∀ i j, g i j=g j i)
    (regular : ∀ i,FiberRectangles.degree (g i)=4) (named : Block A A A A g g) :
    ∀ i j x y, Commute (ColorTensor.P p (atPoint A i) x) (ColorTensor.P p (atPoint A j) y) := by
  classical
  obtain ⟨e,he⟩ := realize_region p (fun t => t=l) (by rw [SixSixCycle.size A]; decide)
    (by rw [SixSixCycle.size A]; decide)
  let R : Shore (targetName p) l (Fin 9) := ((SixSixCycle.regEquiv A).trans e).trans
    (Equiv.subtypeEquivRight (fun x => mem_vertices (targetName p) (fun t => t=l) x))
  have colors (i j) : source G (atPoint A i) (atPoint A j)=targetName p (atPoint R i) (atPoint R j) :=
    he (SixSixCycle.regEquiv A i) (SixSixCycle.regEquiv A j)
  have transitive (x y) : ∃ f : Equiv.Perm (Fin 9), f x=y ∧ ∀ i j, g (f i) (f j)=g i j := by
    obtain ⟨f,fx,_,pres⟩ := RegionalThreeClasses.small_pair p A R (by decide) x x y y
      ((A x).property.trans (R y).property.symm)
    exact ⟨f,fx,fun i j => (named ((pres i j).trans (colors (f i) (f j)).symm)).symm⟩
  let U := fun i a => ColorTensor.P p (atPoint A i) (atPoint R a)
  obtain ⟨hp,rr,cc⟩ := ColorTensor.quantumPermutation p
  have rows (i) : ∑ a, U i a=1 := by
    apply Eq.trans _ (rr (atPoint A i))
    apply Fintype.sum_of_injective (atPoint R) (fun _ _ eq => R.injective (Subtype.ext eq))
      (U i) (ColorTensor.P p (atPoint A i)) _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (SixSixCycle.point R (eq.symm.trans (A i).property)))
  have cols (a) : ∑ i, U i a=1 := by
    apply Eq.trans _ (cc (atPoint R a))
    apply Fintype.sum_of_injective (atPoint A) (fun _ _ eq => A.injective (Subtype.ext eq))
      (fun i => U i a) (fun x => ColorTensor.P p x (atPoint R a)) _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (SixSixCycle.point A (eq.trans (R a).property)))
  have mismatch (i j a b) (bad : g i j≠g a b) : U i a * U j b=0 :=
    incompatible p _ _ _ _ (fun eq => bad (named (eq.trans (colors a b).symm)))
  have hc := Literature.banica_bichon_nine_valency_four g simple sym regular transitive U
    (fun i j => hp _ _) rows cols (NamedQuantumGraph.intertwines g U rows cols mismatch)
  intro i j x y
  by_cases hx : targetName p x x=l
  · obtain ⟨u,rfl⟩ := SixSixCycle.point R hx
    by_cases hy : targetName p y y=l
    · obtain ⟨v,rfl⟩ := SixSixCycle.point R hy
      exact hc i u j v
    · rw [outside p _ _ (fun eq => hy (eq.symm.trans (A j).property))]; exact Commute.zero_right _
  · rw [outside p _ _ (fun eq => hx (eq.symm.trans (A i).property))]; exact Commute.zero_left _

end QGI.Coherent.NinePointRigidity


