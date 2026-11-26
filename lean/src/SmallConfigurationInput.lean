import SmallCatalogProof
import SmallCatalogHomogeneous

namespace QGI.Literature
open Coherent.SmallUnion
/-- Ziv-Av, §2.1, single-input completeness of the GAP representatives.
The archived matrices omit singleton fibers; the explicitly indexed rows
restore them. The independently classified homogeneous inputs are excluded. -/
axiom zivAv_small_catalog_coverage {k : Nat} [NeZero k] (small : k≤13)
    {c : Table k} (hc : Configuration c) (remaining : ¬QGI.SmallCatalog.KnownHomogeneous c) :
    ∃ a : QGI.SmallCatalog.Index k, Nonempty (QGI.CatalogComparison.Placement (QGI.SmallCatalog.frame a) c)

theorem small_catalog_placement {k : Nat} [NeZero k] (small : k≤13) {c : Table k}
    (hc : Configuration c) :
    ∃ a : QGI.SmallCatalog.Index k, Nonempty (QGI.CatalogComparison.Placement (QGI.SmallCatalog.frame a) c) := by
  by_cases known : QGI.SmallCatalog.KnownHomogeneous c
  · exact QGI.SmallCatalog.homogeneous_coverage hc known
  · exact zivAv_small_catalog_coverage small hc known

/-- Realize all prescribed color names simultaneously using the finite
stabilizer-chain witnesses for the common representative. -/
theorem zivAv_named_small_configuration {k : Nat} (positive : 0 < k) (small : k ≤ 13)
    {c d : Table k} (src : Configuration c) (tgt : Configuration d)
    (used : ∀ s, (∃ i j, c i j = s) ↔ ∃ x y, d x y = s)
    (numbers : ∀ s t i j x y, c i j = d x y →
      (∑ z, if c i z = s ∧ c z j = t then 1 else 0 : Nat) =
      (∑ z, if d x z = s ∧ d z y = t then 1 else 0 : Nat)) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, c i j = d (e i) (e j) := by
  letI : NeZero k := ⟨Nat.ne_of_gt positive⟩
  obtain ⟨a,⟨A⟩⟩ := small_catalog_placement small src
  obtain ⟨b,⟨B⟩⟩ := small_catalog_placement small tgt
  exact QGI.SmallCatalog.named small src tgt ⟨used,numbers⟩ A B

/-- Align two ordered entries using verified color-preserving point permutations. -/
theorem zivAv_small_relation_transitive {k : Nat} (positive : 0 < k) (small : k ≤ 13)
    {c : Table k} (hc : Configuration c) (i j x y : Fin k) (hit : c i j = c x y) :
    ∃ e : Equiv.Perm (Fin k), e i=x ∧ e j=y ∧ ∀ u v, c u v=c (e u) (e v) := by
  letI : NeZero k := ⟨Nat.ne_of_gt positive⟩
  obtain ⟨a,⟨A⟩⟩ := small_catalog_placement small hc
  exact QGI.SmallCatalog.paired small A i j x y hit
end QGI.Literature
