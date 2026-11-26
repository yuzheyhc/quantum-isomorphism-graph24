import SixTenCoordinates
import ComponentReduction

noncomputable section
namespace QGI.Coherent.RecoloredStrategy
open Synchrony Intertwiner StrategyColorLaws

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

private theorem forward_item (q : Question n) (a : Fin n) :
    restricted p q a = U p (ends q a).1 (ends q a).2 := by
  obtain ⟨q,x⟩ := q
  cases q
  · rfl
  · exact (restricted_inverse p _ _).symm

/-- The same two measurements implement every pair of ordinary graphs
whose new edges agree on corresponding coherent colors. -/
def recode (A B : Graph n) (compatible : ∀ i j x y,
    Relations.color (closure G) i j = targetName p x y → A.edge i j = B.edge x y) :
    PerfectStrategy A B K := by
  refine {p with perfect := ?_}
  intro q r a b loss
  by_contra result
  have old := not_not.mp (mt (p.perfect q r a b) result)
  have nonzero : StrategyColors.Supported p (ends q a).1 (ends r b).1 (ends q a).2 (ends r b).2 := by
    intro zero
    change (U p _ _).comp (U p _ _) = 0 at zero
    rw [←forward_item p q a,←forward_item p r b] at zero
    have same := congrArg (fun F : Module.End ℂ (cyclic p) => (F ⟨p.psi,psi_mem p⟩ : K)) zero
    change p.alice q a (p.alice r b p.psi) = 0 at same
    rw [same_outcome p r b] at same
    exact result same
  apply loss
  have equal : decide ((ends q a).1 = (ends r b).1) = decide ((ends q a).2 = (ends r b).2) := congrArg (fun g : Bool × Bool => g.1) old
  exact Prod.ext equal
    (compatible _ _ _ _ ((associated p).mpr (StrategyColors.maps_support p nonzero)))

theorem preserves_degree {A B : Graph n} (e : Equiv.Perm (Fin n))
    (edges : ∀ i j, A.edge i j = B.edge (e i) (e j)) (i : Fin n) :
    DegreeSpectrum.degree A i = DegreeSpectrum.degree B (e i) := by
  simp only [DegreeSpectrum.degree,edges]
  exact Equiv.sum_comp e (fun j => if B.edge (e i) j = true then 1 else (0:Nat))

theorem swapping {n : Nat} (A : Graph n) (a b : Fin n)
    (s : ∀ i, A.edge a i = false) (t : ∀ i, A.edge b i = false) (i j : Fin n) :
    A.edge i j = A.edge (Equiv.swap a b i) (Equiv.swap a b j) := by
  by_cases x : i=a
  · subst i; simp [s,t]
  by_cases y : i=b
  · subst i; simp [s,t]
  rw [Equiv.swap_apply_of_ne_of_ne x y]
  by_cases z : j=a
  · subst j; simp [A.symm i,s,t]
  by_cases w : j=b
  · subst j; simp [A.symm i,s,t]
  rw [Equiv.swap_apply_of_ne_of_ne z w]

open private cut_disconnected smaller_component from ComponentReduction

/-- A specified isolated vertex can be matched when all smaller orders
are known. The component bound applies to the recolored graphs. -/
theorem isolated_via_smaller {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K) (lower : Through (n-1))
    (A B : Graph n) (compatible : ∀ i j x y,
      Relations.color (closure G) i j = targetName p x y → A.edge i j = B.edge x y)
    (a b : Fin n) (another : ∃ i, i ≠ a)
    (sa : ∀ i, A.edge a i = false) (sb : ∀ i, B.edge b i = false) :
    ∃ e : Equiv.Perm (Fin n), e a=b ∧ ∀ i j, A.edge i j = B.edge (e i) (e j) := by
  let side := fun i : Fin n => decide (i=a)
  obtain ⟨other,diff⟩ := another
  have onto : Function.Surjective side := by
    intro v
    cases v with
    | false => exact ⟨other,by simp [side,diff]⟩
    | true => exact ⟨a,by simp [side]⟩
  have disc := cut_disconnected A side onto (by
    intro i j adj
    by_cases hi : i=a
    · subst i; rw [sa] at adj; contradiction
    by_cases hj : j=a
    · subst j; rw [A.symm,sa] at adj; contradiction
    simp [side,hi,hj])
  obtain ⟨iso⟩ := Components.of_component_bound lower (fun c => by
    have bound := smaller_component A disc c
    omega) (H:=B) ⟨K,inferInstance,inferInstance,inferInstance,⟨recode p A B compatible⟩⟩
  let f : Equiv.Perm (Fin n) := ⟨iso.toFun,iso.invFun,iso.leftInv,iso.rightInv⟩
  have sf (z : Fin n) : B.edge (f a) z=false := by
    obtain ⟨i,rfl⟩ := f.surjective z
    exact (iso.edge_eq a i).symm.trans (sa i)
  exact ⟨f.trans (Equiv.swap (f a) b),Equiv.swap_apply_left _ _,
    fun i j => (iso.edge_eq i j).trans (swapping B _ b sf sb (f i) (f j))⟩

/-- In order sixteen a coherent recoloring that isolates corresponding
vertices admits an ordinary isomorphism taking the selected root to the
selected target root, even when other isolated vertices are present. -/
theorem isolated {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (A B : Graph 16)
    (compatible : ∀ i j x y, Relations.color (closure G) i j = targetName p x y → A.edge i j = B.edge x y)
    (a b : Fin 16) (sa : ∀ i, A.edge a i = false) (sb : ∀ i, B.edge b i = false) :
    ∃ e : Equiv.Perm (Fin 16), e a=b ∧ ∀ i j, A.edge i j = B.edge (e i) (e j) := by
  apply isolated_via_smaller p through15 A B compatible a b _ sa sb
  by_cases h : a=0
  · exact ⟨1,by simp [h]⟩
  · exact ⟨0,Ne.symm h⟩

end QGI.Coherent.RecoloredStrategy



