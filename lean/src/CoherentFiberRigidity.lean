import CoherentIntertwines
import DegreeClassRigidity
import QuantumIsoSymmetry
import HomogeneousCoverage

namespace QGI.Coherent

/-- Vertices sharing all diagonal values of the graph's coherent closure. -/
noncomputable def fiber {n : Nat} (G : Graph n) (a : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k => ∀ B ∈ (closure G).space, B k k = B a a

theorem mem_fiber {n : Nat} {G : Graph n} {a k : Fin n} :
    k ∈ fiber G a ↔ ∀ B ∈ (closure G).space, B k k = B a a := by
  classical
  simp [fiber]

/-- Two nonzero outcomes for the same source vertex lie in one target fiber. -/
theorem supported_in_one_fiber {n : Nat} {G H : Graph n} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)
    {i a k : Fin n} (ha : p.alice (false, i) a p.psi ≠ 0)
    (hk : p.alice (false, i) k p.psi ≠ 0) : k ∈ fiber H a := by
  apply mem_fiber.mpr
  intro B hB
  obtain ⟨A, h⟩ := exists_intertwining_source p hB
  exact (DegreeClassRigidity.supported_diagonal p h hk).symm.trans
    (DegreeClassRigidity.supported_diagonal p h ha)

/-- A graph all of whose stable diagonal classes have size at most two is
determined up to classical isomorphism by its quantum commuting isomorphism class. -/
theorem isomorphic_of_small_target_fibers {n : Nat} {G H : Graph n}
    (small : ∀ a, (fiber H a).card ≤ 2) (q : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K, g, ip, _, ⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  apply BinaryVectorChoice.isomorphic_of_two_images p
  intro i
  by_cases present : ∃ a, p.alice (false, i) a p.psi ≠ 0
  · obtain ⟨a, ha⟩ := present
    obtain ⟨x, y, covers⟩ := DegreeClassRigidity.two_labels (fiber H a) a (small a)
    exact ⟨x, y, fun k hk => covers k (supported_in_one_fiber p ha hk)⟩
  · exact ⟨i, i, fun k hk => (present ⟨k, hk⟩).elim⟩

theorem isomorphic_of_small_fibers {n : Nat} {G H : Graph n}
    (small : ∀ a, (fiber G a).card ≤ 2) (q : QuantumIso G H) : Isomorphic G H :=
  (isomorphic_of_small_target_fibers small q.symm).symm

/-- At orders 16–23 a counterexample must have a proper fiber with at least
three vertices. Apply the same theorem to the reversed pair for the other graph. -/
theorem counterexample_has_proper_large_fiber {n : Nat} (lo : 16 ≤ n) (hi : n ≤ 23)
    {G H : Graph n} (q : QuantumIso G H) (sep : ¬ Isomorphic G H) :
    ∃ a, 3 ≤ (fiber G a).card ∧ (fiber G a).card < n := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, 2 < (fiber G a).card := by
    by_contra! small
    exact sep (isomorphic_of_small_fibers small q)
  obtain ⟨M, hM, x, y, different⟩ := counterexample_has_distinct_diagonals lo hi q sep
  refine ⟨a, ha, ?_⟩
  have proper : fiber G a ≠ Finset.univ := by
    intro full
    have allMem (i : Fin n) : i ∈ fiber G a := by simp [full]
    exact different (((mem_fiber.mp (allMem x)) M hM).trans ((mem_fiber.mp (allMem y)) M hM).symm)
  simpa using (Finset.card_lt_iff_ne_univ _).mpr proper

end QGI.Coherent
