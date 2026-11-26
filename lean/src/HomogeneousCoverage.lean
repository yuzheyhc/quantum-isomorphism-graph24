import HomogeneousCensus
import UnionMask
import CatalogSixteen
import CatalogOrders
import data.homogeneous.unions.Check16
import data.homogeneous.unions.Check18

namespace QGI.Coherent
open QGI.ThetaBridge QGI.CatalogRigidity
open QGI.Homogeneous.Unions

private def targetMatrix (n : Nat) (g : QGI.Homogeneous.Graph) : NMat n :=
  tab fun i j => targetEntry g i.val j.val

/-- Tie the archived matrices, the parsed mask certificates and the actual
graph6 representatives to the same inputs, in their original order. -/
private def Aligned (n : Nat) (v : Parsed) : Prop :=
  rawTables n = v.blocks.map Block.table ∧
  v.targets.toList.map (targetMatrix n) = records n ∧
  (v.blocks.all fun b => decide (MaskCompatible n b.table b.code)) = true

private instance (n : Nat) (v : Parsed) : Decidable (Aligned n v) := by
  unfold Aligned
  infer_instance

private def alignedAt (n : Nat) : Bool :=
  match parseOrder n with
  | .error _ => false
  | .ok v => decide (Aligned n v)

set_option maxHeartbeats 0 in
private theorem aligned16 : alignedAt 16 = true := by native_decide

set_option maxHeartbeats 0 in
private theorem aligned18 : alignedAt 18 = true := by native_decide

private theorem represented_of_table {n : Nat} {G : QGI.Graph n}
    (v : Parsed) (aligned : Aligned n v) (checked : allRealized n v = true)
    {t : Table} (listed : t ∈ rawTables n) (label : HasTableLabel (closure G) t) :
    Represented G := by
  obtain ⟨tables, targets, masks⟩ := aligned
  rw [tables] at listed
  obtain ⟨b, member, rfl⟩ := List.mem_map.mp listed
  have ok : MaskCompatible n b.table b.code := of_decide_eq_true (List.all_eq_true.mp masks b member)
  obtain ⟨e, values⟩ := label
  let edgeG := fun i j => G.edge (e i) (e j)
  have constant : ∀ i j u w : Fin n,
      colorAt b.table i.val j.val = colorAt b.table u.val w.val → edgeG i j = edgeG u w := by
    intro i j u w h
    have h' := values _ (adjacency_mem G) i j u w h
    change G.edge (e i) (e j) = G.edge (e u) (e w)
    cases h₁ : G.edge (e i) (e j) <;> cases h₂ : G.edge (e u) (e w) <;>
      first | rfl | simp [Intertwiner.adjacency, h₁, h₂] at h'
  obtain ⟨m, bound, hm⟩ := exists_mask_of_compatible ok edgeG
    (fun i j => G.symm (e i) (e j)) (fun i => G.loopless (e i)) constant
  obtain ⟨id, g, row, f, perm⟩ := allRealized_sound checked member bound
  have inRecords : targetMatrix n g ∈ records n := by
    rw [← targets]
    exact List.mem_map.mpr ⟨g, Array.mem_toList_iff.mpr (Array.mem_of_getElem? row), rfl⟩
  refine ⟨targetMatrix n g, inRecords, f.symm.trans e, ?_⟩
  intro i j
  have both := (perm (f.symm i) (f.symm j)).symm.trans (hm (f.symm i) (f.symm j))
  simp only [Equiv.apply_symm_apply] at both
  simp only [targetMatrix, entry_tab, Equiv.trans_apply, both, edgeG]
  cases h : G.edge (e (f.symm i)) (e (f.symm j)) <;> simp [Intertwiner.adjacency, h]

private theorem represented_of_archive {n u h : Nat} {G : QGI.Graph n}
    (pass : passed n u h = true) (alignment : alignedAt n = true)
    (cover : ∃ t ∈ rawTables n, HasTableLabel (closure G) t) : Represented G := by
  obtain ⟨v, parse, checked⟩ := parsed_coverage_of_passed pass
  have aligned : Aligned n v := of_decide_eq_true (by simpa only [alignedAt, parse] using alignment)
  obtain ⟨t, listed, label⟩ := cover
  exact represented_of_table v aligned checked listed label

private theorem isomorphic_of_homogeneous_archive {n : Nat} (hn : n = 16 ∨ n = 18)
    {G H : QGI.Graph n} (hom : IsHomogeneous G) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨e, adj⟩ := Literature.lmr_coherentIso_of_qc q
  rcases realized_or_tables hn hom e with spatial | ⟨source, target⟩
  · exact iso_of_realized adj spatial
  · rcases hn with rfl | rfl
    · exact represented16 (represented_of_archive homogeneousUnionCoverage16 aligned16 source)
        (represented_of_archive homogeneousUnionCoverage16 aligned16 target) q
    · exact represented18 (represented_of_archive homogeneousUnionCoverage18 aligned18 source)
        (represented_of_archive homogeneousUnionCoverage18 aligned18 target) q

/-- Across the entire range, a single diagonal class of the source's coherent
closure suffices. The target graph and both vertex labellings are arbitrary. -/
theorem isomorphic_of_homogeneous_16_to_23 {n : Nat} (lo : 16 ≤ n) (hi : n ≤ 23)
    {G H : QGI.Graph n} (hom : IsHomogeneous G) (q : QuantumIso G H) : Isomorphic G H := by
  rcases (show (n = 16 ∨ n = 18) ∨ (n = 19 ∨ n = 23) ∨
      (n = 17 ∨ n = 20 ∨ n = 21 ∨ n = 22) by omega) with archive | tournament | spatial
  · exact isomorphic_of_homogeneous_archive archive hom q
  · exact isomorphic_of_homogeneous_tournament_orders tournament hom q
  · exact isomorphic_of_homogeneous spatial hom q

/-- Any putative counterexample at these orders has at least two diagonal
classes. A matrix in the coherent closure distinguishes a pair of vertices. -/
theorem counterexample_has_distinct_diagonals {n : Nat} (lo : 16 ≤ n) (hi : n ≤ 23)
    {G H : QGI.Graph n} (q : QuantumIso G H) (separated : ¬ Isomorphic G H) :
    ∃ M ∈ (closure G).space, ∃ x y : Fin n, M x x ≠ M y y := by
  by_contra! uniform
  apply separated
  refine isomorphic_of_homogeneous_16_to_23 lo hi ?_ q
  intro M member
  let base : Fin n := ⟨0, by omega⟩
  refine ⟨M base base, ?_⟩
  ext x y
  by_cases equal : x = y
  · subst y
    simpa [schur, Matrix.one_apply] using uniform M member x base
  · simp [schur, Matrix.one_apply, equal]

end QGI.Coherent
