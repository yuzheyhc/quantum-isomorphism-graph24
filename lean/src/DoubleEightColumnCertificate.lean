import DoubleEightColumnEnum
import data.DoubleEightUniformInput

namespace QGI.DoubleEight.ColumnEnum

private def parseLeaf (line : String) : Option (Nat × Nat × List Nat) := do
  let s :: p :: cols ← (line.splitOn " ").mapM String.toNat? | none
  return (s,p,cols)

/-- All 375 source-normalized, sorted column lists produced by the point-count search. -/
def leaves : List (Nat × Nat × List Nat) :=
  (((include_str "data/double-eight-column-enum.txt").splitOn "\n").map String.trim
    |>.filter (· != "") |>.mapM parseLeaf).getD []

private def expected (s p : Nat) : List (List Nat) :=
  leaves.filterMap fun (a,b,cols) => if (a,b) = (s,p) then some cols else none

private def agreesWithRows (actual advertised : List (List Nat)) : Bool :=
  actual.length == advertised.length && actual.all (fun cols => decide (cols ∈ advertised))
    && advertised.all (fun cols => decide (cols ∈ actual))

private def checkOneProfile (p : Fin 6) : Bool :=
  let ds := profiles[p.val]!
  let pool := columnPool ds
  (List.finRange 21).all fun s =>
    agreesWithRows (enumerateWith UniformInput.shores[s.val]! ds pool) (expected s.val p.val)

private theorem recomputed : ∀ p : Fin 6, checkOneProfile p = true := by native_decide

theorem leaf_count : leaves.length = 375 ∧ leaves.Nodup := by native_decide

/-- For every one of the 126 input pairs the enumerator's outputs and the
named certificate rows have the same members. -/
theorem mem_enumerate_iff_leaf (s : Fin 21) (p : Fin 6) (cols : List Nat) :
    cols ∈ enumerate UniformInput.shores[s.val]! profiles[p.val]! ↔
    (s.val,p.val,cols) ∈ leaves := by
  have hs : s ∈ List.finRange 21 :=
    List.mem_iff_getElem.mpr ⟨s.val, by simp, by simp⟩
  obtain h := List.all_eq_true.mp (recomputed p) s hs
  change agreesWithRows (enumerate UniformInput.shores[s.val]! profiles[p.val]!)
    (expected s.val p.val) = true at h
  simp only [agreesWithRows, Bool.and_eq_true] at h
  have e : cols ∈ expected s.val p.val ↔ (s.val,p.val,cols) ∈ leaves := by
    simp only [expected, List.mem_filterMap]
    constructor
    · rintro ⟨⟨a,b,l⟩, hl, test⟩
      split at test
      · rename_i pair
        cases pair
        cases test
        exact hl
      · cases test
    · intro hl
      exact ⟨(s.val,p.val,cols),hl,by simp⟩
  exact (Iff.intro (fun ha => of_decide_eq_true (List.all_eq_true.mp h.1.2 _ ha))
    (fun hb => of_decide_eq_true (List.all_eq_true.mp h.2 _ hb))).trans e

/-- A matrix with arbitrary entries satisfying the named intersection-number
conditions belongs to the concrete 375-row certificate. -/
theorem admissible_mem_leaf (s : Fin 21) (p : Fin 6) {q : Signature} {cols : List Nat}
    (h : Admissible UniformInput.shores[s.val]! profiles[p.val]! q cols) :
    (s.val,p.val,cols) ∈ leaves :=
  (mem_enumerate_iff_leaf s p cols).1 (mem_enumerate h)

end QGI.DoubleEight.ColumnEnum
