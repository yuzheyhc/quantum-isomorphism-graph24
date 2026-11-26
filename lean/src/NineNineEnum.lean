import Lean
namespace QGI.NineNine.BareEnum

/-- Column zero occupies the most significant bit. The usual order on row
masks then agrees with the left-to-right lexicographic order. -/
def digit (m j : Nat) : Bool := m.testBit (8 - j)

def rowDegree (m : Nat) : Nat := ((List.range 9).filter (digit m)).length

def colDegree (rows : List Nat) (j : Nat) : Nat :=
  (rows.filter fun m => digit m j).length

/-- If adjacent columns tied above the current row, the left one cannot now
have zero while the right one has one. -/
def colPrefixOrdered (rows : List Nat) : Prop :=
  ∀ (pre : List Nat) (r : Nat) (post : List Nat), rows = pre ++ r :: post →
    ∀ j : Fin 8, (∀ p ∈ pre, digit p j.val = digit p (j.val+1)) →
      digit r (j.val+1) = true → digit r j.val = true

private def allowed (d remaining : Nat) (pre : List Nat) (r : Nat) : Prop :=
  (∀ p ∈ pre, p ≥ r) ∧
  (∀ j : Fin 8, (∀ p ∈ pre, digit p j.val = digit p (j.val+1)) →
      digit r (j.val+1) = true → digit r j.val = true) ∧
  ∀ j : Fin 9, let count := colDegree (pre ++ [r]) j.val
    count ≤ d ∧ d ≤ count + remaining

private instance {d remaining pre r} : Decidable (allowed d remaining pre r) := by
  unfold allowed
  infer_instance

/-- Column counts and adjacent ties depend only on the prefix. Compute
them once at each node of the canonical search. -/
private structure Cache where
  prior : List Nat
  ties : List (Fin 8)
  counts : List (Fin 9 × Nat)

private def cache (pre : List Nat) : Cache :=
  ⟨pre, (List.ofFn (fun j : Fin 8 => j)).filter (fun j => pre.all
      (fun p => digit p j.val == digit p (j.val+1))),
    List.ofFn (fun j : Fin 9 => (j,colDegree pre j.val))⟩

private def accept (d remaining : Nat) (s : Cache) (r : Nat) : Bool :=
  s.prior.all (fun v => decide (r≤v)) &&
  s.ties.all (fun j => !digit r (j.val+1) || digit r j.val) &&
  s.counts.all (fun slot =>
    let total := slot.2 + (digit r slot.1.val).toNat
    decide (total≤d ∧ d≤total+remaining))

private theorem accept_eq (d remaining : Nat) (pre : List Nat) (r : Nat) :
    accept d remaining (cache pre) r=true ↔ allowed d remaining pre r := by
  have add (j : Fin 9) : colDegree (pre++[r]) j.val=colDegree pre j.val+(digit r j.val).toNat := by
    cases e : digit r j.val <;> simp [colDegree,e]
  have ties (j : Fin 8) : j∈(cache pre).ties ↔ ∀ p∈pre, digit p j.val=digit p (j.val+1) := by
    have member : j∈List.ofFn (fun x : Fin 8 => x) := List.mem_ofFn.mpr ⟨j,rfl⟩
    simp only [cache,List.mem_filter,member,true_and,List.all_eq_true,beq_iff_eq]
  have pass (j : Fin 8) : (!digit r (j.val+1) || digit r j.val)=true ↔
      digit r (j.val+1)=true → digit r j.val=true := by
    cases digit r (j.val+1) <;> cases digit r j.val <;> decide
  simp only [accept,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,allowed]
  constructor
  · rintro ⟨⟨above,tie⟩,bound⟩
    refine ⟨above,fun j hj => (pass j).mp (tie j ((ties j).mpr hj)),fun j => ?_⟩
    rw [add]
    exact bound (j,colDegree pre j.val) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  · rintro ⟨above,tie,bound⟩
    refine ⟨⟨above,fun j hj => (pass j).mpr (tie j ((ties j).mp hj))⟩,?_⟩
    intro slot hh
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hh
    simpa only [add] using bound j

private def extend (pool : List Nat) (d : Nat) : Nat → List Nat → List (List Nat)
  | 0, pre => [pre]
  | n+1, pre =>
    let context := cache pre
    (pool.filter (accept d n context)).flatMap fun r =>
      extend pool d n (pre ++ [r])

/-- The concrete search tree: each row is an nine-bit mask of degree d,
in full natural-number order. Column counts are pruned against both remaining
capacity and the required final degree. -/
def candidates (d : Nat) : List (List Nat) :=
  extend ((List.range 512).filter fun m => rowDegree m == d) d 9 []

private theorem extend_complete {pool rows : List Nat} {d : Nat}
    (inPool : ∀ r ∈ rows, r ∈ pool) (ordered : rows.Pairwise (· ≥ ·))
    (cols : ∀ j : Fin 9, colDegree rows j.val = d) (hprefix : colPrefixOrdered rows)
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
    exact ⟨r, List.mem_filter.mpr ⟨inPool r inWhole, (accept_eq _ _ _ _).mpr step⟩,
      ih (pre ++ [r]) (by simpa using split)⟩

/-- Completeness for arbitrary data: every ordered matrix with the prescribed
row and column degrees occurs in the actual executable candidate list. -/
theorem of_regular_prefix {rows : List Nat} {d : Nat}
    (size : rows.length = 9) (bounded : ∀ r ∈ rows, r < 512)
    (degrees : ∀ r ∈ rows, rowDegree r = d) (ordered : rows.Pairwise (· ≥ ·))
    (cols : ∀ j : Fin 9, colDegree rows j.val = d) (hprefix : colPrefixOrdered rows) :
    rows ∈ candidates d := by
  have mem (r : Nat) (hr : r ∈ rows) :
      r ∈ (List.range 512).filter (fun m => rowDegree m == d) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr (bounded r hr), beq_iff_eq.mpr (degrees r hr)⟩
  simpa only [candidates, size] using extend_complete mem ordered cols hprefix rows [] (by simp)

end QGI.NineNine.BareEnum

namespace QGI.NineNine.Sieve

def weights : Array Nat := ((List.range 512).map (fun v => 16 ^ BareEnum.rowDegree v)).toArray

def score (rs : List Nat) (v : Nat) := (rs.map fun r => weights.getD (r &&& v) 0).sum

def uniform (rs : List Nat) : Bool :=
  let expected := score rs (rs.getD 0 0)
  rs.all fun r => score rs r == expected

def transposeRows (rs : List Nat) := (List.range 9).map fun j => ((List.range 9).map fun i =>
  2^(8-i) * (BareEnum.digit (rs.getD i 0) j).toNat).sum

def admissible (rs : List Nat) : Bool := uniform rs && uniform (transposeRows rs)

def shortlist (d : Nat) := (BareEnum.candidates d).filter admissible

end QGI.NineNine.Sieve



