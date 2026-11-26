import Lean

namespace QGI.DoubleEight.BareEnum

/-- Column zero occupies the most significant bit. The usual order on row
masks then agrees with the left-to-right lexicographic order. -/
def digit (m j : Nat) : Bool := m.testBit (7 - j)

def rowDegree (m : Nat) : Nat := ((List.range 8).filter (digit m)).length

def colDegree (rows : List Nat) (j : Nat) : Nat :=
  (rows.filter fun m => digit m j).length

/-- If adjacent columns tied above the current row, the left one cannot now
have zero while the right one has one. -/
def colPrefixOrdered (rows : List Nat) : Prop :=
  ∀ (pre : List Nat) (r : Nat) (post : List Nat), rows = pre ++ r :: post →
    ∀ j : Fin 7, (∀ p ∈ pre, digit p j.val = digit p (j.val+1)) →
      digit r (j.val+1) = true → digit r j.val = true

private def allowed (d remaining : Nat) (pre : List Nat) (r : Nat) : Prop :=
  (∀ p ∈ pre, p ≥ r) ∧
  (∀ j : Fin 7, (∀ p ∈ pre, digit p j.val = digit p (j.val+1)) →
      digit r (j.val+1) = true → digit r j.val = true) ∧
  ∀ j : Fin 8, let count := colDegree (pre ++ [r]) j.val
    count ≤ d ∧ d ≤ count + remaining

private instance {d remaining pre r} : Decidable (allowed d remaining pre r) := by
  unfold allowed
  infer_instance

private def extend (pool : List Nat) (d : Nat) : Nat → List Nat → List (List Nat)
  | 0, pre => [pre]
  | n+1, pre =>
    (pool.filter fun r => decide (allowed d n pre r)).flatMap fun r =>
      extend pool d n (pre ++ [r])

/-- The concrete search tree: each row is an eight-bit mask of degree d,
in full natural-number order. Column counts are pruned against both remaining
capacity and the required final degree. -/
def candidates (d : Nat) : List (List Nat) :=
  extend ((List.range 256).filter fun m => rowDegree m == d) d 8 []

private theorem extend_complete {pool rows : List Nat} {d : Nat}
    (inPool : ∀ r ∈ rows, r ∈ pool) (ordered : rows.Pairwise (· ≥ ·))
    (cols : ∀ j : Fin 8, colDegree rows j.val = d) (hprefix : colPrefixOrdered rows)
    (tail pre : List Nat) (split : rows = pre ++ tail) :
    rows ∈ extend pool d tail.length pre := by
  induction tail generalizing pre with
  | nil => simpa [extend] using split
  | cons r tail ih =>
    have step : allowed d tail.length pre r := by
      constructor
      · have pairwise := List.pairwise_append.mp (split ▸ ordered)
        exact fun p hp => pairwise.2.2 p hp r (by simp)
      constructor
      · exact hprefix pre r tail split
      · intro j
        have pad : rows = (pre ++ [r]) ++ tail := by simpa using split
        have total := cols j
        rw [pad] at total
        have sum : colDegree (pre ++ [r]) j.val + colDegree tail j.val = d := by
          simpa only [colDegree, List.filter_append, List.length_append] using total
        have bound : colDegree tail j.val ≤ tail.length :=
          List.length_filter_le (fun m => digit m j.val) tail
        exact ⟨by omega, by omega⟩
    have inWhole : r ∈ rows := by simp [split]
    simp only [List.length_cons, extend, List.mem_flatMap]
    exact ⟨r, List.mem_filter.mpr ⟨inPool r inWhole, decide_eq_true step⟩,
      ih (pre ++ [r]) (by simpa using split)⟩

/-- Completeness for arbitrary data: every ordered matrix with the prescribed
row and column degrees occurs in the actual executable candidate list. -/
theorem of_regular_prefix {rows : List Nat} {d : Nat}
    (size : rows.length = 8) (bounded : ∀ r ∈ rows, r < 256)
    (degrees : ∀ r ∈ rows, rowDegree r = d) (ordered : rows.Pairwise (· ≥ ·))
    (cols : ∀ j : Fin 8, colDegree rows j.val = d) (hprefix : colPrefixOrdered rows) :
    rows ∈ candidates d := by
  have mem (r : Nat) (hr : r ∈ rows) :
      r ∈ (List.range 256).filter (fun m => rowDegree m == d) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr (bounded r hr), beq_iff_eq.mpr (degrees r hr)⟩
  simpa only [candidates, size] using extend_complete mem ordered cols hprefix rows [] (by simp)

end QGI.DoubleEight.BareEnum
