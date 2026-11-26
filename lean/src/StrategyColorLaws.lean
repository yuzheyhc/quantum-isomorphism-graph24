import StrategyColors
import QuantumCounts
import CoherentFiberRigidity

noncomputable section
open scoped BigOperators

namespace QGI.Coherent.StrategyColorLaws
open StrategyColors
open Intertwiner (Intertwines)

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

def targetName (x y : Fin n) : Nat := ((equiv p).symm (label H x y)).val

theorem associated {i j x y : Fin n} :
    Relations.color (closure G) i j = targetName p x y ↔ equiv p (label G i j) = label H x y := by
  change (label G i j).val = ((equiv p).symm (label H x y)).val ↔ _
  rw [Subtype.val_inj,Equiv.eq_symm_apply]

theorem target_same (i j x y : Fin n) : targetName p i j = targetName p x y ↔
    Relations.color (closure H) i j = Relations.color (closure H) x y := by
  change ((equiv p).symm (label H i j)).val = ((equiv p).symm (label H x y)).val ↔
    (label H i j).val = (label H x y).val
  rw [Subtype.val_inj,Subtype.val_inj,(equiv p).symm.injective.eq_iff]

/-- The target matrix is constant on its own basic relations, so support
at one representative gives the same scalar at every corresponding pair. -/
theorem entries {i j x y : Fin n} (eq : Relations.color (closure G) i j = targetName p x y)
    {A B : Coherent.Mat n} (belongs : B ∈ (closure H).space) (h : Intertwines p A B) :
    A i j = B x y := by
  obtain ⟨a,b,hit⟩ := exists_target p i j
  have labels := (maps_support p hit).symm.trans ((associated p).mp eq)
  exact (entry_eq p h hit).trans ((Relations.same _ _ _ _ _).mp (congrArg Subtype.val labels) B belongs)

def mark (c : Fin n → Fin n → Nat) (v : Nat) : Coherent.Mat n :=
  fun i j => if c i j = v then 1 else 0

theorem mark_intertwines (v : Nat) : Intertwines p (mark (Relations.color (closure G)) v) (mark (targetName p) v) := by
  apply Intertwiner.intertwines_of_compatible
  intro i j x y bad
  by_contra hit
  exact bad (by simp only [mark,(associated p).mpr (maps_support p hit)])

theorem target_mark_mem (v : Nat) : mark (targetName p) v ∈ (closure H).space := by
  by_cases h : ∃ i j, targetName p i j = v
  · obtain ⟨i,j,rfl⟩ := h
    convert Relations.indicator_mem (closure H) (Relations.color (closure H) i j) using 1
    ext x y
    simp only [mark,target_same]
  · push_neg at h
    convert (closure H).space.zero_mem using 1
    ext x y
    simp [mark,h]

theorem common_edge {i j x y : Fin n} (h : Relations.color (closure G) i j = targetName p x y) :
    G.edge i j = H.edge x y := by
  have eq := entries p h (adjacency_mem H) (Intertwiner.initial_adjacency p)
  cases s : G.edge i j <;> cases t : H.edge x y <;> first | rfl | simp [Intertwiner.adjacency,s,t] at eq

theorem common_transpose {i j x y : Fin n} (h : Relations.color (closure G) i j = targetName p x y) :
    Relations.color (closure G) j i = targetName p y x := by
  let v := Relations.color (closure G) j i
  have eq := entries p h ((closure H).adjoint_mem (target_mark_mem p v))
    (Intertwiner.conjugate_transpose p (mark_intertwines p v))
  by_contra ne
  simp [Matrix.conjTranspose_apply,mark,v,Ne.symm ne] at eq

def count {X : Type} [Fintype X] (c : X → X → Nat) (a b : Nat) (i j : X) :=
  ∑ k, if c i k = a ∧ c k j = b then 1 else 0

private theorem mul_mark (c : Fin n → Fin n → Nat) (a b : Nat) (i j : Fin n) :
    (mark c a * mark c b) i j = (count c a b i j : ℂ) := by
  simp only [Matrix.mul_apply,mark,count,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

theorem common_products (a b : Nat) {i j x y : Fin n} (h : Relations.color (closure G) i j = targetName p x y) :
    count (Relations.color (closure G)) a b i j = count (targetName p) a b x y := by
  have eq := entries p h ((closure H).mul_mem (target_mark_mem p a) (target_mark_mem p b))
    (Intertwiner.matrix_mul p (mark_intertwines p a) (mark_intertwines p b))
  simp only [mul_mark] at eq
  exact_mod_cast eq

theorem count_relabel {X Y : Type} [Fintype X] [Fintype Y] (c : X → X → Nat) (e : Y ≃ X)
    (a b : Nat) (i j : Y) :
    count (fun x y => c (e x) (e y)) a b i j = count c a b (e i) (e j) :=
  Equiv.sum_comp e (fun k => if c (e i) k = a ∧ c k (e j) = b then 1 else 0)

include p in
/-- The target vertex belongs to a fiber of the same cardinality as a
source fiber, for the specified strategy and with arbitrary vertex names. -/
theorem fiber_size (a : Fin n) : ∃ i : Fin n, (fiber G i).card = (fiber H a).card := by
  classical
  obtain ⟨i,j,hit⟩ := exists_source p a a
  have d := entry_eq p (Intertwiner.initial_diagonal p) hit
  have ij : i = j := by
    by_contra ne
    simp [Matrix.one_apply,ne] at d
  subst j
  have same := (associated p).mpr (maps_support p hit)
  let v := Relations.color (closure G) i i
  have traces := Intertwiner.trace_eq p (mark_intertwines p v)
  have fsrc (z) : Relations.color (closure G) z z = v ↔ z ∈ fiber G i :=
    (Relations.same _ _ _ _ _).trans mem_fiber.symm
  have ftgt (z) : targetName p z z = v ↔ z ∈ fiber H a := by
    change targetName p z z = Relations.color (closure G) i i ↔ _
    rw [same,target_same]; exact (Relations.same _ _ _ _ _).trans mem_fiber.symm
  simp only [Matrix.trace,Matrix.diag_apply,mark,fsrc,ftgt] at traces
  refine ⟨i,?_⟩
  simpa using traces

end QGI.Coherent.StrategyColorLaws