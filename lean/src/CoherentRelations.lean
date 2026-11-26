import CoherentHomogeneous
import Mathlib.Data.Fintype.EquivFin


noncomputable section

namespace QGI.Coherent.Relations
open Coherent
open scoped BigOperators

abbrev Cell (n : Nat) := Fin n × Fin n

def equivSetoid {n : Nat} (C : CoherentAlgebra n) : Setoid (Cell n) where
  r a b := ∀ M ∈ C.space, M a.1 a.2 = M b.1 b.2
  iseqv := ⟨fun _ _ _ => rfl, fun h M hm => (h M hm).symm, fun h g M hm => (h M hm).trans (g M hm)⟩

def color {n : Nat} (C : CoherentAlgebra n) (i j : Fin n) : Nat := by
  classical
  exact (Fintype.equivFin (Quotient (equivSetoid C)) (Quotient.mk _ (i,j))).val

theorem same {n : Nat} (C : CoherentAlgebra n) (i j x y : Fin n) :
    color C i j = color C x y ↔ ∀ M ∈ C.space, M i j = M x y := by
  classical
  simp only [color,Fin.val_inj,Equiv.apply_eq_iff_eq]
  exact Quotient.eq

private theorem separator {n : Nat} (C : CoherentAlgebra n) (a b : Cell n)
    (diff : color C a.1 a.2 ≠ color C b.1 b.2) :
    ∃ M ∈ C.space, M a.1 a.2 = 1 ∧ M b.1 b.2 = 0 := by
  classical
  have h := mt (same C _ _ _ _).mpr diff
  push_neg at h
  obtain ⟨A,ha,ne⟩ := h
  let z := A a.1 a.2 - A b.1 b.2
  refine ⟨z⁻¹ • (A - A b.1 b.2 • ones n),C.space.smul_mem _ (C.space.sub_mem ha (C.space.smul_mem _ C.ones_mem)),?_,?_⟩
  · change z⁻¹ * (A a.1 a.2 - A b.1 b.2 * 1) = 1
    simp [z,sub_ne_zero.mpr ne]
  · change z⁻¹ * (A b.1 b.2 - A b.1 b.2 * 1) = 0
    simp

/-- Finite pointwise interpolation constructs the indicator of a relation
inside the original complex matrix algebra. -/
theorem indicator_mem {n : Nat} (C : CoherentAlgebra n) (u : Nat) :
    (fun i j => if color C i j = u then (1 : ℂ) else 0) ∈ C.space := by
  classical
  by_cases used : ∃ i j, color C i j = u
  · obtain ⟨i,j,rfl⟩ := used
    have build (s : Finset (Cell n)) : ∃ M ∈ C.space,
        M i j = 1 ∧ ∀ b ∈ s, color C b.1 b.2 ≠ color C i j → M b.1 b.2 = 0 := by
      induction s using Finset.induction_on with
      | empty => exact ⟨ones n,C.ones_mem,rfl,by simp⟩
      | @insert b s _ ih =>
        obtain ⟨M,hm,atA,zero⟩ := ih
        by_cases eq : color C b.1 b.2 = color C i j
        · exact ⟨M,hm,atA,fun k hk diff => zero _ ((Finset.mem_insert.mp hk).resolve_left (fun e => diff (e ▸ eq))) diff⟩
        · obtain ⟨N,hn,nA,nB⟩ := separator C (i,j) b (Ne.symm eq)
          refine ⟨schur M N,C.schur_mem hm hn,by simp [schur,atA,nA],?_⟩
          intro k hk diff
          rcases Finset.mem_insert.mp hk with rfl | old
          · simp [schur,nB]
          · simp [schur,zero k old diff]
    obtain ⟨M,hm,one,zero⟩ := build Finset.univ
    convert hm using 1
    ext x y
    by_cases eq : color C x y = color C i j
    · simp [eq,(same C _ _ _ _).mp eq M hm,one]
    · simp [eq,zero (x,y) (Finset.mem_univ _) eq]
  · push_neg at used
    simp only [used,if_false]
    exact C.space.zero_mem

theorem transpose {n : Nat} (C : CoherentAlgebra n) {i j x y : Fin n}
    (h : color C i j = color C x y) : color C j i = color C y x := by
  apply (same C _ _ _ _).mpr
  intro M hM
  have e := (same C _ _ _ _).mp h M.conjTranspose (C.adjoint_mem hM)
  exact star_injective e

theorem products {n : Nat} (C : CoherentAlgebra n) :
    ∀ a b i j x y, color C i j = color C x y →
      (∑ z, if color C i z = a ∧ color C z j = b then 1 else 0 : Nat) =
      (∑ z, if color C x z = a ∧ color C z y = b then 1 else 0 : Nat) := by
  classical
  intro a b i j x y eq
  have e := (same C _ _ _ _).mp eq _ (C.mul_mem (indicator_mem C a) (indicator_mem C b))
  have entry (i j : Fin n) :
      (∑ z : Fin n, (if color C i z = a then (1:ℂ) else 0) * (if color C z j = b then 1 else 0)) =
      ((∑ z : Fin n, if color C i z = a ∧ color C z j = b then 1 else 0 : Nat) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> simp_all
  simp only [Matrix.mul_apply,entry] at e
  exact_mod_cast e

theorem end_colors {n : Nat} (C : CoherentAlgebra n) {i j x y : Fin n}
    (h : color C i j = color C x y) : color C i i = color C x x ∧ color C j j = color C y y := by
  have source {i j x y : Fin n} (e : color C i j = color C x y) : color C i i = color C x x := by
    apply (same C _ _ _ _).mpr
    intro M hm
    have pair := (same C _ _ _ _).mp e _ (C.mul_mem (C.schur_mem hm C.one_mem) C.ones_mem)
    simpa [Matrix.mul_apply,schur,ones,Matrix.one_apply] using pair
  exact ⟨source h,source (transpose C h)⟩

theorem diagonal {n : Nat} (C : CoherentAlgebra n) {i j x : Fin n} (h : color C i j = color C x x) :
    i = j := by
  have eq := (same C _ _ _ _).mp h _ C.one_mem
  by_contra ne
  simp [Matrix.one_apply,ne] at eq

end QGI.Coherent.Relations