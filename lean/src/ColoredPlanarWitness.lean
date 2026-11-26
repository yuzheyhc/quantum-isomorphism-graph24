import ColorTensorStrategy
import ColoredPatternSemantics
import DoubleEightAttach

noncomputable section
open scoped BigOperators

namespace QGI.Certificate

abbrev PlanePoint := Int × Int

private def determinant (a b c : PlanePoint) : Int :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

/-- A sufficient certificate for a planar incidence drawing. The vertices
are distinct, every vertex off an edge misses its supporting line, and two
edges without a common endpoint are strictly separated by a supporting line.
The unoriented edges are distinct. Subdividing each segment at its midpoint
therefore draws the binary constraint's incidence vertex, with the two
arguments ordered by the original directed edge. -/
def Draws (p : Pattern) (v : Array PlanePoint) : Prop :=
  v.size = p.order ∧ v.toList.Nodup ∧
  (p.edges.map fun (x,y) => (min x y, max x y)).Nodup ∧
  (∀ e ∈ p.edges, e.1 < p.order ∧ e.2 < p.order ∧ e.1 ≠ e.2 ∧
    ∀ k : Fin p.order, k.val ≠ e.1 → k.val ≠ e.2 →
      determinant v[e.1]! v[e.2]! v[k.val]! ≠ 0) ∧
  ∀ e ∈ p.edges, ∀ f ∈ p.edges,
    e.1 ≠ f.1 → e.1 ≠ f.2 → e.2 ≠ f.1 → e.2 ≠ f.2 →
      0 < determinant v[e.1]! v[e.2]! v[f.1]! * determinant v[e.1]! v[e.2]! v[f.2]! ∨
      0 < determinant v[f.1]! v[f.2]! v[e.1]! * determinant v[f.1]! v[f.2]! v[e.2]!

private instance (p : Pattern) (v : Array PlanePoint) : Decidable (Draws p v) := by
  unfold Draws
  infer_instance

def tetraPrism : Pattern → Bool
  | .tetra | .prismTransitive | .prismCyclic => true
  | _ => false

theorem drawing_of_tetraPrism {p : Pattern} (h : tetraPrism p = true) :
    ∃ v : Array PlanePoint, Draws p v := by
  cases p with
  | tetra => exact ⟨#[(0,0),(20,0),(0,20),(4,4)], by decide⟩
  | prismTransitive => exact ⟨#[(0,0),(20,0),(0,20),(4,4),(10,4),(4,10)], by decide⟩
  | prismCyclic => exact ⟨#[(0,0),(20,0),(0,20),(4,4),(10,4),(4,10)], by decide⟩
  | nearClique | bipyramid => contradiction

/-- Real binary constraint with ordered arguments for a specified table color. -/
def binary {n : Nat} (m : ColorMatrix) (c : Nat) (x y : Fin n) : ℝ :=
  if m.get x.val y.val = c then 1 else 0

def binaryMatrix {n : Nat} (m : ColorMatrix) (c : Nat) : Intertwiner.Mat n :=
  fun x y => (binary m c x y : ℂ)

end QGI.Certificate

namespace QGI.Literature
open Certificate

/-- Cai and Young, ICALP 2023, Definitions 2, 3, 5, 6, 8 and Theorem 9,
forward implication for real binary indicator constraints on a common
nonempty finite domain. The nonzero unital C*-algebra is the bounded
operators on the given nontrivial complex Hilbert space. A subdivision
of the explicitly drawn edges is the planar incidence graph. The same
quantum permutation intertwines every ordered binary constraint.
https://doi.org/10.4230/LIPIcs.ICALP.2023.33 -/
axiom caiYoung_binary_planar {n : Nat} (positive : 0 < n)
    (a b : ColorMatrix) (ha : a.order = n) (hb : b.order = n)
    (p : Pattern) (drawing : ∃ v : Array PlanePoint, Draws p v)
    (colors : List Nat) (arity : colors.length = p.edges.length) (rename : Nat → Nat)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (U : Fin n → Fin n → E →L[ℂ] E)
    (projections : ∀ x u, U x u * U x u = U x u ∧ U x u = (U x u).adjoint)
    (rowSum : ∀ x, ∑ u, U x u = 1) (colSum : ∀ u, ∑ x, U x u = 1)
    (binaryTransport : ∀ c ∈ colors, ∀ x y : Fin n,
      (∑ u, ∑ v, (binary b (rename c) u v : ℂ) • (U x u * U y v)) =
        (binary a c x y : ℂ) • (1 : E →L[ℂ] E)) :
    binaryCspCount a p colors = binaryCspCount b p (colors.map rename)

end QGI.Literature

namespace QGI.Certificate
open Intertwiner

/-- An actual commuting-operator strategy preserving each named binary
constraint preserves the count returned by the archive's executable. -/
theorem planar_homCount {n : Nat} (positive : 0 < n) {G H : Graph n}
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (strat : PerfectStrategy G H K) (a b : ColorMatrix) (ha : a.order = n) (hb : b.order = n)
    (p : Pattern) (drawing : ∃ v : Array PlanePoint, Draws p v) (colors : List Nat)
    (arity : colors.length = p.edges.length) (rename : Nat → Nat)
    (named : ∀ c ∈ colors, Intertwines strat (binaryMatrix a c) (binaryMatrix b (rename c))) :
    homCount a p colors = homCount b p (colors.map rename) := by
  obtain ⟨proj, rows, cols⟩ := ColorTensor.quantumPermutation strat
  rw [homCount_eq_binaryCspCount, homCount_eq_binaryCspCount]
  exact Literature.caiYoung_binary_planar positive a b ha hb p drawing colors arity rename
    (ColorTensor.P strat) proj rows cols (fun c hc => ColorTensor.tensor_square strat (named c hc))

/-- The label map goes from catalog points to graph vertices. -/
def inGraphLabels {n : Nat} (e : Fin n ≃ Fin n) (A : Mat n) : Mat n :=
  fun x y => A (e.symm x) (e.symm y)

/-- Independent point relabelings on the two sides preserve the obstruction.
The reindexed quantum permutation sends catalog point x to catalog point a
with operator P(e x,f a). Thus no relabeled game strategy has to be constructed. -/
theorem planar_homCount_reindexed {n : Nat} (positive : 0 < n) {G H : Graph n}
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (strat : PerfectStrategy G H K) (e f : Fin n ≃ Fin n) (a b : ColorMatrix)
    (ha : a.order = n) (hb : b.order = n) (p : Pattern)
    (drawing : ∃ v : Array PlanePoint, Draws p v) (colors : List Nat)
    (arity : colors.length = p.edges.length) (rename : Nat → Nat)
    (named : ∀ c ∈ colors, Intertwines strat (inGraphLabels e (binaryMatrix a c))
      (inGraphLabels f (binaryMatrix b (rename c)))) :
    homCount a p colors = homCount b p (colors.map rename) := by
  obtain ⟨proj, rows, cols⟩ := ColorTensor.quantumPermutation strat
  rw [homCount_eq_binaryCspCount, homCount_eq_binaryCspCount]
  let U := ColorTensor.P strat
  apply Literature.caiYoung_binary_planar positive a b ha hb p drawing colors arity rename
    (fun x u => U (e x) (f u)) (fun x u => proj (e x) (f u))
  · intro x
    exact (f.sum_comp (U (e x))).trans (rows (e x))
  · intro u
    exact (e.sum_comp (fun x => U x (f u))).trans (cols (f u))
  · intro c hc x y
    let A : Mat n := binaryMatrix a c
    let B : Mat n := binaryMatrix b (rename c)
    change (∑ i, ∑ j, B i j • (U (e x) (f i) * U (e y) (f j))) =
      A x y • (1 : ColorTensor.space strat →L[ℂ] ColorTensor.space strat)
    calc
      _ = ∑ i, ∑ j, (inGraphLabels f B) i j •
          (U (e x) i * U (e y) j) := by
        apply Fintype.sum_equiv f
        intro i
        apply Fintype.sum_equiv f
        intro j
        simp only [inGraphLabels, Equiv.symm_apply_apply]
      _ = A x y • 1 := by
        have h := ColorTensor.tensor_square strat (named c hc) (e x) (e y)
        change _ = inGraphLabels e A (e x) (e y) • _ at h
        simpa only [inGraphLabels, Equiv.symm_apply_apply] using h

end QGI.Certificate

namespace QGI.DoubleEight.Attachment
open Certificate Intertwiner

private theorem pattern_checks : rows.all (fun r =>
    tetraPrism r.pattern && r.colors.length == r.pattern.edges.length) = true := by
  native_decide

/-- No commuting strategy can intertwine all the colors of any of the 260
attached exceptional maps between the two source-labeled catalog tables. -/
theorem exceptional_row_excluded (r : Row) (hr : r ∈ rows)
    {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (strat : PerfectStrategy G H K) :
    ¬ ∀ c ∈ r.colors, Intertwines strat (binaryMatrix r.src c)
        (binaryMatrix r.dst (r.perm[c]?.getD r.src.rank)) := by
  intro named
  have metadata := List.all_eq_true.mp pattern_checks r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at metadata
  have bound := of_decide_eq_true (List.all_eq_true.mp attachedMatrices r hr)
  exact counts_differ_of_checked r.passed (planar_homCount (by decide) strat r.src r.dst
    bound.2.2.1 bound.2.2.2.1 r.pattern (drawing_of_tetraPrism metadata.1) r.colors
    metadata.2 (fun c => r.perm[c]?.getD r.src.rank) named)

/-- The obstruction attaches to the original catalog entries and exact
permutation of every exceptional key returned by the finite census. -/
theorem exceptional_key_excluded (C : SixteenMapSearch.Counts) (hC : census = some C)
    (k : Key) (hk : k ∈ C.exceptions) {G H : Graph 16} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (strat : PerfectStrategy G H K) :
    ∃ r ∈ rows, r.key = k ∧ OnCatalog r ∧
      ¬ ∀ c ∈ r.colors, Intertwines strat (binaryMatrix r.src c)
        (binaryMatrix r.dst (r.perm[c]?.getD r.src.rank)) := by
  obtain ⟨r, hr, key, catalog, _⟩ := actual_key_has_checked_witness C hC k hk
  exact ⟨r, hr, key, catalog, exceptional_row_excluded r hr strat⟩

/-- The catalog exclusion in independently chosen vertex labels on the two
input graphs. The witness still retains the original source, target, and color permutation. -/
theorem exceptional_key_excluded_reindexed (C : SixteenMapSearch.Counts) (hC : census = some C)
    (k : Key) (hk : k ∈ C.exceptions) {G H : Graph 16} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (strat : PerfectStrategy G H K) (e f : Fin 16 ≃ Fin 16) :
    ∃ r ∈ rows, r.key = k ∧ OnCatalog r ∧
      ¬ ∀ c ∈ r.colors, Intertwines strat (inGraphLabels e (binaryMatrix r.src c))
        (inGraphLabels f (binaryMatrix r.dst (r.perm[c]?.getD r.src.rank))) := by
  obtain ⟨r, hr, key, bound, diff⟩ := actual_key_has_checked_witness C hC k hk
  refine ⟨r, hr, key, bound, ?_⟩
  intro named
  have metadata := List.all_eq_true.mp pattern_checks r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at metadata
  exact diff (planar_homCount_reindexed (by decide) strat e f r.src r.dst
    bound.2.2.1 bound.2.2.2.1 r.pattern (drawing_of_tetraPrism metadata.1)
    r.colors metadata.2 (fun c => r.perm[c]?.getD r.src.rank) named)

end QGI.DoubleEight.Attachment
