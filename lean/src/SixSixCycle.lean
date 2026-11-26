import SixSixCatalog
import SixSixCommuting

noncomputable section
namespace QGI.Literature
open ZivAvSix

/-- Banica–Bichon, *Quantum automorphism groups of vertex-transitive
graphs of order ≤ 11*, J. Algebraic Combin. 26 (2007), Corollary 3.1(1),
p. 91. The undirected six-cycle has classical quantum automorphism group.
Here the adjacency intertwiner UD=DU is written entrywise and the
coefficient algebra is the bounded operators on a complex Hilbert space.
https://www.kurims.kyoto-u.ac.jp/EMIS/journals/JACO/Volume26_1/l35k4u4r1531k21n.fulltext.pdf -/
axiom banica_bichon_cycle_six {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nontrivial E] (U : S → S → (E →L[ℂ] E))
    (proj : ∀ i j, U i j*U i j=U i j ∧ U i j=(U i j).adjoint)
    (row : ∀ i, ∑ j, U i j=1) (col : ∀ j, ∑ i, U i j=1)
    (edge : ∀ i b, (∑ a, if cycleEdge a b then U i a else 0)=
                    ∑ j, if cycleEdge i j then U j b else 0) :
    ∀ i j x y, Commute (U i j) (U x y)
end QGI.Literature

namespace QGI.Coherent.SixSixCycle
open FourTwelveFunctional (source)
open SixTenCoordinates (Shore atPoint)
open SmallUnion SmallFiberExtension StrategyColorLaws ZivAvSix
open private incompatible outside from RegionalPlanar

def regEquiv {n l X} {c : Fin n → Fin n → Nat} (F : Shore c l X) : X ≃ Region c (fun t => t=l) :=
  F.trans (Equiv.subtypeEquivRight (fun x => (mem_vertices c (fun t => t=l) x).symm))

theorem size {n l k} {c : Fin n → Fin n → Nat} (F : Shore c l (Fin k)) :
    (vertices c (fun t => t=l)).card=k := by simpa using (Fintype.card_congr (regEquiv F)).symm

theorem point {n l X} {c : Fin n → Fin n → Nat} (F : Shore c l X) {x : Fin n} (h : c x x=l) :
    ∃ j, atPoint F j=x := ⟨F.symm ⟨x,h⟩,congrArg Subtype.val (F.apply_symm_apply _)⟩

theorem magic_edge {A : Type} [Semiring A] (U : S → S → A)
    (row : ∀ i, ∑ j, U i j=1) (col : ∀ j, ∑ i, U i j=1)
    (mismatch : ∀ i j a b, cycleEdge i j≠cycleEdge a b → U i a * U j b = 0)
    (i b : S) : (∑ a, if cycleEdge a b then U i a else 0) =
    ∑ j, if cycleEdge i j then U j b else 0 := by
  classical
  calc
    _ = ∑ a, ∑ j, if cycleEdge a b then U i a * U j b else 0 := by
      apply Finset.sum_congr rfl; intro a _
      by_cases hit : cycleEdge a b=true <;> simp [hit,←Finset.mul_sum,col]
    _ = ∑ a, ∑ j, if cycleEdge i j then U i a * U j b else 0 := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro j _
      by_cases eq : cycleEdge i j=cycleEdge a b
      · rw [eq]
      · simp [mismatch i j a b eq]
    _ = _ := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
      by_cases hit : cycleEdge i j=true <;> simp [hit,←Finset.sum_mul,row]

theorem commuting {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) {l} (F : Shore (source G) l S)
    (cyclic : Cyclic (fun i j => source G (atPoint F i) (atPoint F j))) :
    ∀ x z, source G x x=l → source G z z=l → ∀ y w, Commute (ColorTensor.P p x y) (ColorTensor.P p z w) := by
  classical
  obtain ⟨perm,admissible⟩ := cyclic
  let L := perm.trans F
  obtain ⟨e,he⟩ := realize_region p (fun t => t=l)
    (by rw [size F]; decide) (by rw [size F]; decide)
  let R : Shore (targetName p) l S := ((regEquiv L).trans e).trans
    (Equiv.subtypeEquivRight (fun x => mem_vertices (targetName p) (fun t => t=l) x))
  have named (i j : S) : source G (atPoint L i) (atPoint L j)=targetName p (atPoint R i) (atPoint R j) :=
    he (regEquiv L i) (regEquiv L j)
  let U := fun i a => ColorTensor.P p (atPoint L i) (atPoint R a)
  obtain ⟨hp,rr,cc⟩ := ColorTensor.quantumPermutation p
  have rows (i : S) : ∑ a, U i a=1 := by
    apply Eq.trans _ (rr (atPoint L i))
    apply Fintype.sum_of_injective (atPoint R) (fun _ _ eq => R.injective (Subtype.ext eq))
      (U i) (ColorTensor.P p (atPoint L i)) _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (point R (eq.symm.trans (L i).property)))
  have cols (a : S) : ∑ i, U i a=1 := by
    apply Eq.trans _ (cc (atPoint R a))
    apply Fintype.sum_of_injective (atPoint L) (fun _ _ eq => L.injective (Subtype.ext eq))
      (fun i => U i a) (fun x => ColorTensor.P p x (atPoint R a)) _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (point L (eq.trans (R a).property)))
  have mismatch (i j a b : S) (bad : cycleEdge i j≠cycleEdge a b) : U i a * U j b=0 :=
    incompatible p _ _ _ _ (fun eq => bad (admissible i j a b (eq.trans (named a b).symm)))
  have hc := Literature.banica_bichon_cycle_six U (fun i j => hp _ _) rows cols (magic_edge U rows cols mismatch)
  intro x z hx hz y w
  obtain ⟨i,rfl⟩ := point L hx
  obtain ⟨j,rfl⟩ := point L hz
  by_cases hy : targetName p y y=l
  · obtain ⟨a,rfl⟩ := point R hy
    by_cases hw : targetName p w w=l
    · obtain ⟨b,rfl⟩ := point R hw; exact hc i a j b
    · rw [outside p _ _ (fun eq => hw (eq.symm.trans hz))]; exact Commute.zero_right _
  · rw [outside p _ _ (fun eq => hy (eq.symm.trans hx))]; exact Commute.zero_left _

end QGI.Coherent.SixSixCycle

