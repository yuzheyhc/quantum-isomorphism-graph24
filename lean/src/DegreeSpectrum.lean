import Intertwiner

open scoped BigOperators

namespace QGI.DegreeSpectrum
open QGI.Intertwiner QGI.Synchrony

/-- The row sum of the Boolean adjacency matrix as a natural number. -/
def degree {n : Nat} (G : Graph n) (x : Fin n) : Nat :=
  ∑ y : Fin n, if G.edge x y = true then 1 else 0

def ones (n : Nat) : Mat n := fun _ _ => 1

theorem rowSumEntry {n : Nat} (G : Graph n) (x y : Fin n) :
    (adjacency G * ones n) x y = (degree G x : ℂ) := by
  rw [Matrix.mul_apply]
  simp only [degree, ones, Nat.cast_sum, mul_one]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : G.edge x z = true <;> simp [adjacency, hz]

/-- Occurrence of every diagonal value in either input. If entries differ,
compatibility gives U_xa² = 0, whereas idempotence gives U_xa² = U_xa.
A row or column of zero operators is incompatible with the unit state. -/
theorem matchedDiagonals {n : Nat} {G H : Graph n} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)
    {A B : Mat n} (h : Intertwines p A B) :
    (∀ x, ∃ a, A x x = B a a) ∧ (∀ a, ∃ x, A x x = B a a) := by
  classical
  let v : cyclic p := ⟨p.psi, psi_mem p⟩
  have vanish (x a : Fin n) (bad : A x x ≠ B a a) : (U p x a v : K) = 0 := by
    have hz : U p x a = 0 :=
      (restricted_projection p (false,x) a).1.symm.trans
        (compatible_of_intertwines p h x x a a bad)
    rw [hz] <;> rfl
  constructor
  · intro x
    by_contra! bad
    apply psi_ne_zero p
    calc
      p.psi = ∑ a, (U p x a v : K) := ((magic_sums p x v).1).symm
      _ = 0 := Finset.sum_eq_zero (fun a _ => vanish x a (bad a))
  · intro a
    by_contra! bad
    apply psi_ne_zero p
    calc
      p.psi = ∑ x, (U p x a v : K) := ((magic_sums p a v).2).symm
      _ = 0 := Finset.sum_eq_zero (fun x _ => vanish x a (bad x))

/-- Apply the diagonal criterion to AJ, where J is the all-ones matrix. -/
theorem matchedDegrees {n : Nat} {G H : Graph n} (hq : QuantumIso G H) :
    (∀ x, ∃ a, degree G x = degree H a) ∧
    (∀ a, ∃ x, degree G x = degree H a) := by
  obtain ⟨K, g, ip, _hc, ⟨p⟩⟩ := hq
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  have inter : Intertwines p (adjacency G * ones n) (adjacency H * ones n) :=
    matrix_mul p (initial_adjacency p) (initial_full p 1)
  have m := matchedDiagonals p inter
  simpa only [rowSumEntry, Nat.cast_inj] using m

theorem occurs_iff {n : Nat} {G H : Graph n} (hq : QuantumIso G H) (d : Nat) :
    (∃ x, degree G x = d) ↔ (∃ a, degree H a = d) := by
  obtain ⟨rows, cols⟩ := matchedDegrees hq
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := rows x
    exact ⟨a, ha.symm.trans hx⟩
  · rintro ⟨a, ha⟩
    obtain ⟨x, hx⟩ := cols a
    exact ⟨x, hx.trans ha⟩

end QGI.DegreeSpectrum
