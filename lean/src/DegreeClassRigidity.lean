import BinaryVectorChoice
import DegreeSpectrum

namespace QGI.DegreeClassRigidity
open Intertwiner Synchrony

/-- Entries in a target matrix having a prescribed value on the diagonal. -/
noncomputable def diagonalClass {n : Nat} (B : Mat n) (z : ℂ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun a => B a a = z

theorem two_labels {α : Type*} [DecidableEq α] (s : Finset α) (fallback : α)
    (small : s.card ≤ 2) : ∃ a b, ∀ k ∈ s, k = a ∨ k = b := by
  rcases Nat.lt_or_eq_of_le small with h | h
  · obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
    · exact ⟨fallback, fallback, by simp⟩
    · exact ⟨a, a, fun k hk => Or.inl (Finset.card_le_one.mp (by omega : s.card ≤ 1) k hk a ha)⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, b, by simp⟩

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A nonzero outcome vector must preserve each intertwined diagonal entry. -/
theorem supported_diagonal (p : PerfectStrategy G H K) {A B : Mat n}
    (h : Intertwines p A B) {x a : Fin n} (nz : p.alice (false, x) a p.psi ≠ 0) :
    A x x = B a a := by
  by_contra different
  have hz : U p x a = 0 := (restricted_projection p (false,x) a).1.symm.trans
    (compatible_of_intertwines p h x x a a different)
  let v : cyclic p := ⟨p.psi, psi_mem p⟩
  have zero : (U p x a v : K) = 0 := by rw [hz]; rfl
  exact nz zero

/-- For each source vertex, at most two target diagonals can match its value.
The binary vector theorem then gives a classical graph isomorphism. -/
theorem isomorphic_of_small_diagonal_classes (p : PerfectStrategy G H K) {A B : Mat n}
    (h : Intertwines p A B) (small : ∀ x, (diagonalClass B (A x x)).card ≤ 2) :
    Isomorphic G H := by
  apply BinaryVectorChoice.isomorphic_of_two_images p
  intro x
  obtain ⟨a,b,cover⟩ := two_labels _ x (small x)
  refine ⟨a,b,?_⟩
  intro k nz
  apply cover k
  simpa [diagonalClass] using (supported_diagonal p h nz).symm

/-- The target vertices of degree d. -/
def degreeClass (H : Graph n) (d : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun a => DegreeSpectrum.degree H a = d

/-- When each degree in the target occurs at most twice, quantum commuting
isomorphism implies ordinary isomorphism, at any order. -/
theorem isomorphic_of_small_degree_classes (small : ∀ d, (degreeClass H d).card ≤ 2)
    (hq : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K, g, ip, _hc, ⟨p⟩⟩ := hq
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  have inter : Intertwines p (adjacency G * DegreeSpectrum.ones n)
      (adjacency H * DegreeSpectrum.ones n) :=
    matrix_mul p (initial_adjacency p) (initial_full p 1)
  apply isomorphic_of_small_diagonal_classes p inter
  intro x
  have same : diagonalClass (adjacency H * DegreeSpectrum.ones n)
        ((adjacency G * DegreeSpectrum.ones n) x x) =
      degreeClass H (DegreeSpectrum.degree G x) := by
    ext a
    simp [diagonalClass, degreeClass, DegreeSpectrum.rowSumEntry]
  rw [same]
  exact small _

end QGI.DegreeClassRigidity
