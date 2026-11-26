import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.GCD.Basic

namespace QGI.FiberRectangles

open Finset

/-- The number of ones in a Boolean row, including the empty row. -/
def degree {n : Nat} (row : Fin n → Bool) : Nat :=
  (univ.filter (fun j => row j = true)).card

private theorem degree_as_sum {n : Nat} (row : Fin n → Bool) :
    degree row = ∑ j, (if row j then 1 else 0 : Nat) := by
  simp [degree]

/-- Count a rectangular relation by its rows and its columns. -/
theorem balance {a b r s : Nat} (R : Fin a → Fin b → Bool)
    (rows : ∀ i, degree (R i) = r) (cols : ∀ j, degree (fun i => R i j) = s) :
    a * r = b * s := by
  calc
    a * r = ∑ i : Fin a, degree (R i) := by simp [rows]
    _ = ∑ j : Fin b, degree (fun i => R i j) := by
      simp only [degree_as_sum]
      exact Finset.sum_comm
    _ = b * s := by simp [cols]

/-- Any nonempty biregular basis relation between coprime-sized fibers is
the full rectangle. Thus there is only one possible color across these fibers. -/
theorem full_of_coprime {a b r s : Nat} (R : Fin a → Fin b → Bool)
    (cop : a.Coprime b) (rows : ∀ i, degree (R i) = r)
    (cols : ∀ j, degree (fun i => R i j) = s)
    (present : ∃ i j, R i j = true) : ∀ i j, R i j = true := by
  obtain ⟨x, y, hxy⟩ := present
  have pos : 0 < r := by
    rw [← rows x]
    apply Finset.card_pos.mpr
    exact ⟨y, by simpa using hxy⟩
  have bound : r ≤ b := by
    rw [← rows x]
    simpa [degree] using (Finset.card_filter_le univ (fun j => R x j = true))
  have divides : b ∣ r := cop.symm.dvd_mul_left.mp ⟨s, balance R rows cols⟩
  have eq := Nat.le_antisymm bound (Nat.le_of_dvd pos divides)
  intro i j
  have full : (univ.filter (fun k => R i k = true)).card = (univ : Finset (Fin b)).card := by
    simpa [degree] using (rows i).trans eq
  exact Finset.card_filter_eq_iff.mp full j (mem_univ j)

/-- Each color in a coherent rectangle has constant row and column degrees. -/
def BiregularColors {a b : Nat} {ι : Type*} [DecidableEq ι]
    (color : Fin a → Fin b → ι) : Prop :=
  ∀ c, ∃ r s,
    (∀ i, degree (fun j => decide (color i j = c)) = r) ∧
    (∀ j, degree (fun i => decide (color i j = c)) = s)

theorem color_constant_of_coprime {a b : Nat} {ι : Type*} [DecidableEq ι]
    {color : Fin a → Fin b → ι} (regular : BiregularColors color) (cop : a.Coprime b)
    (x : Fin a) (y : Fin b) : ∀ i j, color i j = color x y := by
  obtain ⟨_, _, hr, hc⟩ := regular (color x y)
  have full := full_of_coprime (fun i j => decide (color i j = color x y))
    cop hr hc ⟨x, y, by simp⟩
  exact fun i j => of_decide_eq_true (full i j)

private theorem degree_pos {n : Nat} {P : Fin n → Bool} {i : Fin n}
    (h : P i = true) : 0 < degree P :=
  Finset.card_pos.mpr ⟨i, by simpa using h⟩

private theorem disjoint_degrees {b : Nat} {ι : Type*} [DecidableEq ι]
    (row : Fin b → ι) {c d : ι} (h : c ≠ d) :
    degree (fun j => decide (row j = c)) + degree (fun j => decide (row j = d)) ≤ b := by
  rw [degree_as_sum, degree_as_sum, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _ : Fin b, (1 : Nat) := Finset.sum_le_sum fun j _ => by
      by_cases hc : row j = c
      · simp [hc, h]
      · simp [hc]
        split <;> decide
    _ = b := by simp

/-- In a nonuniform rectangle with at most three columns, some color is the
graph of a surjection from the row fiber. This yields the map required to
reattach that fiber using its induced same-image relation. -/
theorem surjection_of_small_fiber {a b : Nat} {ι : Type*} [DecidableEq ι]
    {color : Fin a → Fin b → ι} (regular : BiregularColors color) (small : b ≤ 3)
    (mixed : ∃ i j k l, color i j ≠ color k l) :
    ∃ c, ∃ q : Fin a → Fin b, Function.Surjective q ∧
      ∀ i j, color i j = c ↔ q i = j := by
  classical
  obtain ⟨x, y, z, w, different⟩ := mixed
  obtain ⟨r, s, hr, hs⟩ := regular (color x y)
  obtain ⟨t, u, ht, hu⟩ := regular (color z w)
  have rp : 0 < r := (hr x) ▸ degree_pos (i := y) (by simp)
  have tp : 0 < t := (ht z) ▸ degree_pos (i := w) (by simp)
  have total := disjoint_degrees (color x) different
  rw [hr, ht] at total
  have functional : ∃ c, (∀ i, degree (fun j => decide (color i j = c)) = 1) ∧
      (∀ j, 0 < degree (fun i => decide (color i j = c))) := by
    rcases (show r = 1 ∨ t = 1 by omega) with e | e
    · have sp : 0 < s := (hs y) ▸ degree_pos (i := x) (by simp)
      exact ⟨_, fun i => (hr i).trans e, fun j => (hs j).symm ▸ sp⟩
    · have up : 0 < u := (hu w) ▸ degree_pos (i := z) (by simp)
      exact ⟨_, fun i => (ht i).trans e, fun j => (hu j).symm ▸ up⟩
  obtain ⟨c, singleton, hits⟩ := functional
  choose q hq using fun i => Finset.card_eq_one.mp (singleton i)
  have spec (i j) : color i j = c ↔ q i = j := by
    have h := Finset.ext_iff.mp (hq i) j
    simpa [eq_comm] using h
  refine ⟨c, q, ?_, spec⟩
  intro j
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (hits j)
  exact ⟨i, (spec i j).mp (by simpa using hi)⟩

end QGI.FiberRectangles
