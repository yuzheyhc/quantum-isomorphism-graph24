import SixSixCommuting
import NineNineNormal

noncomputable section
namespace QGI.NineNine.Pappus

/-- The Levi graph of the Pappus configuration in LCF notation
[5, 7, -7, 7, -7, -5] repeated three times. SageMath independently lists this numbering in its PappusGraph example.
https://doc.sagemath.org/html/en/reference/graphs/sage/graphs/graph_generators.html#sage.graphs.graph_generators.GraphGenerators.PappusGraph -/
def edge (i j : Fin 18) : Bool :=
  let d : Fin 18 := (![5,7,11,7,11,13] : Fin 6 → Fin 18) (Fin.ofNat' 6 i.val)
  decide (i+1=j ∨ j+1=i ∨ i+d=j)

def pairEdge (i j : Fin 18) : Bool :=
  let rs := [448,304,268,162,137,81,70,37,26]
  if i.val<9 then if j.val<9 then false else BareEnum.digit (rs.getD i.val 0) (j.val-9)
  else if j.val<9 then BareEnum.digit (rs.getD j.val 0) (i.val-9) else false

private def toCycle : Fin 18 → Fin 18 := ![0,8,2,16,12,6,4,10,14,1,17,5,9,7,13,3,15,11]
theorem numbering : ∃ e : Equiv.Perm (Fin 18), ∀ i j, pairEdge i j=edge (e i) (e j) := by
  have inj : ∀ i j, toCycle i=toCycle j → i=j := by native_decide
  exact ⟨Equiv.ofBijective toCycle (Finite.injective_iff_bijective.mp inj),by change ∀ i j, pairEdge i j=edge (toCycle i) (toCycle j); native_decide⟩

end QGI.NineNine.Pappus

namespace QGI.Literature
/-- Simon Schmidt, *On the quantum symmetry of distance-transitive graphs*,
Theorem 1.5, Table 2, and §5.2 explicitly for the Pappus graph. This
is its universal magic-unitary form represented on a complex Hilbert space.
https://arxiv.org/pdf/1906.06537 -/
axiom schmidt_pappus {I E : Type} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nontrivial E] (adj : I → I → Bool) (e : I ≃ Fin 18)
    (graph : ∀ i j, adj i j=NineNine.Pappus.edge (e i) (e j))
    (U : I → I → (E →L[ℂ] E)) (proj : ∀ i j, U i j*U i j=U i j ∧ U i j=(U i j).adjoint)
    (row : ∀ i, ∑ a, U i a=1) (col : ∀ a, ∑ i, U i a=1)
    (inter : ∀ i b, (∑ a, if adj a b then U i a else 0)=∑ j, if adj i j then U j b else 0) :
    ∀ i a j b, Commute (U i a) (U j b)
end QGI.Literature

namespace QGI.Coherent.NamedQuantumGraph
open FourTwelveFunctional (source)
open StrategyColorLaws SmallUnion SmallFiberExtension
open private incompatible outside from RegionalPlanar

theorem intertwines {I A : Type} [Fintype I] [Semiring A] (edge : I → I → Bool) (U : I → I → A)
    (row : ∀ i, ∑ a, U i a=1) (col : ∀ a, ∑ i, U i a=1)
    (mismatch : ∀ i j a b, edge i j≠edge a b → U i a * U j b=0) (i b : I) :
    (∑ a, if edge a b then U i a else 0)=∑ j, if edge i j then U j b else 0 := by
  classical
  calc
    _ = ∑ a, ∑ j, if edge a b then U i a * U j b else 0 := by
      apply Finset.sum_congr rfl; intro a _
      by_cases hit : edge a b=true <;> simp [hit,←Finset.mul_sum,col]
    _ = ∑ a, ∑ j, if edge i j then U i a * U j b else 0 := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro j _
      by_cases eq : edge i j=edge a b
      · rw [eq]
      · simp [mismatch i j a b eq]
    _ = _ := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
      by_cases hit : edge i j=true <;> simp [hit,←Finset.sum_mul,row]

/-- A common Boolean fusion of the source and target relations with classical
quantum automorphism group realizes all colors of the original region. -/
theorem realize {n : Nat} {G H : Graph n} {K I : Type} [Fintype I] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (reg : Nat → Prop) (fallback : I)
    (F : I ≃ Region (source G) reg) (T : I ≃ Region (targetName p) reg) (adj : I → I → Bool)
    (names : ∀ i j a b, source G (F i).val (F j).val=targetName p (T a).val (T b).val → adj i j=adj a b)
    (rigid : ∀ U : I → I → (ColorTensor.space p →L[ℂ] ColorTensor.space p),
      (∀ i j, U i j*U i j=U i j ∧ U i j=(U i j).adjoint) →
      (∀ i, ∑ a, U i a=1) → (∀ a, ∑ i, U i a=1) →
      (∀ i b, (∑ a, if adj a b then U i a else 0)=∑ j, if adj i j then U j b else 0) →
      ∀ i a j b, Commute (U i a) (U j b)) : Realizes p reg := by
  classical
  let U := fun i a => ColorTensor.P p (F i).val (T a).val
  have point {c : Fin n → Fin n → Nat} (L : I ≃ Region c reg) (x : Fin n) (hx : reg (c x x)) :
      ∃ i, (L i).val=x := ⟨L.symm ⟨x,(mem_vertices _ _ _).mpr hx⟩,congrArg Subtype.val (L.apply_symm_apply _)⟩
  obtain ⟨hp,rr,cc⟩ := ColorTensor.quantumPermutation p
  have rows (i : I) : ∑ a, U i a=1 := by
    apply Eq.trans _ (rr (F i).val)
    apply Fintype.sum_of_injective (fun a => (T a).val) (fun _ _ eq => T.injective (Subtype.ext eq))
      (U i) (ColorTensor.P p (F i).val) _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (point T z (eq ▸ (mem_vertices _ _ _).mp (F i).property)))
  have cols (a : I) : ∑ i, U i a=1 := by
    apply Eq.trans _ (cc (T a).val)
    apply Fintype.sum_of_injective (fun i => (F i).val) (fun _ _ eq => F.injective (Subtype.ext eq))
      (fun i => U i a) (fun x => ColorTensor.P p x (T a).val) _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (point F z ((congrArg reg (show source G z z=targetName p (T a).val (T a).val from eq)).mpr ((mem_vertices _ _ _).mp (T a).property))))
  have bad (i j a b : I) (ne : adj i j≠adj a b) : U i a * U j b=0 :=
    incompatible p _ _ _ _ (fun same => ne (names i j a b same))
  have hc := rigid U (fun i j => hp _ _) rows cols (intertwines adj U rows cols bad)
  apply SixSixAtoms.realize_of_commuting p reg (fun _ => 0) (F fallback).val
  intro x z _ y w
  obtain ⟨i,rfl⟩ := F.surjective x
  obtain ⟨j,rfl⟩ := F.surjective z
  by_cases hy : reg (targetName p y y)
  · obtain ⟨a,rfl⟩ := point T y hy
    by_cases hw : reg (targetName p w w)
    · obtain ⟨b,rfl⟩ := point T w hw; exact hc i a j b
    · rw [outside p _ _ (fun eq => hw (eq ▸ (mem_vertices _ _ _).mp (F j).property))]
      exact Commute.zero_right _
  · rw [outside p _ _ (fun eq => hy (eq ▸ (mem_vertices _ _ _).mp (F i).property))]
    exact Commute.zero_left _

end QGI.Coherent.NamedQuantumGraph



