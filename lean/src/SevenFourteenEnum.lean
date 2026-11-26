import Lean
namespace QGI.SevenFourteen.Enum

/-- Column zero occupies the most significant bit. The usual order on row
masks then agrees with the left-to-right lexicographic order. -/
def digit (m j : Nat) : Bool := m.testBit (6 - j)

def rowDegree (m : Nat) : Nat := ((List.range 7).filter (digit m)).length

def colDegree (rows : List Nat) (j : Nat) : Nat :=
  (rows.filter fun m => digit m j).length

/-- If adjacent columns tied above the current row, the left one cannot now
have zero while the right one has one. -/
def colPrefixOrdered (rows : List Nat) : Prop :=
  ∀ (pre : List Nat) (r : Nat) (post : List Nat), rows = pre ++ r :: post →
    ∀ j : Fin 6, (∀ p ∈ pre, digit p j.val = digit p (j.val+1)) →
      digit r (j.val+1) = true → digit r j.val = true

private def allowed (d remaining : Nat) (pre : List Nat) (r : Nat) : Prop :=
  (∀ p ∈ pre, p ≥ r) ∧
  (∀ j : Fin 6, (∀ p ∈ pre, digit p j.val = digit p (j.val+1)) →
      digit r (j.val+1) = true → digit r j.val = true) ∧
  ∀ j : Fin 7, let count := colDegree (pre ++ [r]) j.val
    count ≤ d ∧ d ≤ count + remaining

private instance {d remaining pre r} : Decidable (allowed d remaining pre r) := by
  unfold allowed
  infer_instance

/-- Column counts and adjacent ties depend only on the prefix. Compute
them once at each node of the canonical search. -/
private structure Cache where
  prior : List Nat
  ties : List (Fin 6)
  counts : List (Fin 7 × Nat)

private def cache (pre : List Nat) : Cache :=
  ⟨pre, (List.ofFn (fun j : Fin 6 => j)).filter (fun j => pre.all
      (fun p => digit p j.val == digit p (j.val+1))),
    List.ofFn (fun j : Fin 7 => (j,colDegree pre j.val))⟩

private def accept (d remaining : Nat) (s : Cache) (r : Nat) : Bool :=
  s.prior.all (fun v => decide (r≤v)) &&
  s.ties.all (fun j => !digit r (j.val+1) || digit r j.val) &&
  s.counts.all (fun slot =>
    let total := slot.2 + (digit r slot.1.val).toNat
    decide (total≤d ∧ d≤total+remaining))

private theorem accept_eq (d remaining : Nat) (pre : List Nat) (r : Nat) :
    accept d remaining (cache pre) r=true ↔ allowed d remaining pre r := by
  have add (j : Fin 7) : colDegree (pre++[r]) j.val=colDegree pre j.val+(digit r j.val).toNat := by
    cases e : digit r j.val <;> simp [colDegree,e]
  have ties (j : Fin 6) : j∈(cache pre).ties ↔ ∀ p∈pre, digit p j.val=digit p (j.val+1) := by
    have member : j∈List.ofFn (fun x : Fin 6 => x) := List.mem_ofFn.mpr ⟨j,rfl⟩
    simp only [cache,List.mem_filter,member,true_and,List.all_eq_true,beq_iff_eq]
  have pass (j : Fin 6) : (!digit r (j.val+1) || digit r j.val)=true ↔
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

def weights : Array Nat := ((List.range 128).map (fun v => 16 ^ rowDegree v)).toArray

def score (rs : List Nat) (v : Nat) := (rs.map (fun r =>
  let common := r &&& v
  weights.getD (common % 128) 0 * weights.getD (common >>> 7) 0)).sum

def uniform (rs : List Nat) : Bool :=
  let expected := score rs (rs.getD 0 0)
  rs.all fun r => score rs r == expected

def transposeRows (rs : List Nat) := (List.range 7).map fun j => ((List.range 14).map fun i =>
  2^(13-i) * (digit (rs.getD i 0) j).toNat).sum

def admissible (rs : List Nat) : Bool := uniform rs && uniform (transposeRows rs)

set_option maxRecDepth 15000
set_option exponentiation.threshold 600

private def mask (pred : Nat → Bool) : Nat :=
  (List.range 128).foldl (fun a r => if pred r then a ||| (1 <<< r) else a) 0

private def full := 2^128-1
private def ties := (List.ofFn (fun j : Fin 6 => mask fun r => !digit r (j.val+1) || digit r j.val)).toArray
private def yes := (List.ofFn (fun j : Fin 7 => mask fun r => digit r j.val)).toArray
private def no := (List.ofFn (fun j : Fin 7 => mask fun r => !digit r j.val)).toArray
private theorem full_bit : ∀ r : Fin 128, full.testBit r.val=true := by native_decide
private theorem ties_bit : ∀ (j : Fin 6) (r : Fin 128), (ties.getD j.val 0).testBit r.val=
    (!digit r.val (j.val+1) || digit r.val j.val) := by native_decide
private theorem yes_bit : ∀ (j : Fin 7) (r : Fin 128), (yes.getD j.val 0).testBit r.val=digit r.val j.val := by native_decide
private theorem no_bit : ∀ (j : Fin 7) (r : Fin 128), (no.getD j.val 0).testBit r.val=(!digit r.val j.val) := by native_decide

private def slot (d remaining : Nat) (j : Fin 7) (used : Nat) : Nat :=
  let ok (v : Nat) := decide (v≤d ∧ d≤v+remaining)
  match ok used, ok (used+1) with
  | true,true => full
  | true,false => no.getD j.val 0
  | false,true => yes.getD j.val 0
  | false,false => 0

private theorem slot_bit (d remaining : Nat) (j : Fin 7) (used : Nat) (r : Fin 128) :
    (slot d remaining j used).testBit r.val=
      decide (used+(digit r.val j.val).toNat≤d ∧ d≤used+(digit r.val j.val).toNat+remaining) := by
  unfold slot
  cases h : digit r.val j.val <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
  all_goals
    generalize ha : decide (used≤d ∧ d≤used+remaining) = u
    generalize hb : decide (used+1≤d ∧ d≤used+1+remaining) = w
    cases u <;> cases w <;> simp only [full_bit,yes_bit,no_bit,h,Nat.zero_testBit] <;> rfl

private def allMask (xs : List Nat) : Nat := xs.foldr (· &&& ·) full
private theorem all_bit (xs : List Nat) (r : Fin 128) :
    (allMask xs).testBit r.val=xs.all (fun v => v.testBit r.val) := by
  induction xs with
  | nil => exact full_bit r
  | cons a xs ih => exact (Nat.testBit_and a (allMask xs) r.val).trans (congrArg (a.testBit r.val && ·) ih)

private def constraints (d remaining : Nat) (s : Cache) : Nat :=
  allMask (s.ties.map fun j => ties.getD j.val 0) &&&
  allMask (s.counts.map fun t => slot d remaining t.1 t.2)

private theorem exact_test (d remaining : Nat) (s : Cache) (r : Fin 128) :
    ((s.prior.all fun v => decide (r.val≤v)) && (constraints d remaining s).testBit r.val) = accept d remaining s r.val := by
  simp only [constraints,Nat.testBit_and,all_bit,List.all_map,Function.comp_def,ties_bit,slot_bit,accept,Bool.and_assoc]

/-- A deficient column must still receive a one. Since subsequent rows
are nonincreasing, the next row is at least the weight of that column. -/
private def minimumRow (d : Nat) : List (Fin 7 × Nat) → Nat
  | [] => 0
  | (j,used)::tail => max (if used<d then 2^(6-j.val) else 0) (minimumRow d tail)

private theorem minimumRow_le {d r : Nat} {xs : List (Fin 7 × Nat)}
    (h : ∀ t∈xs, t.2<d → 2^(6-t.1.val)≤r) : minimumRow d xs≤r := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons t tail ih =>
    obtain ⟨j,used⟩ := t
    apply Nat.max_le.mpr
    constructor
    · by_cases need : used<d
      · simpa only [need,if_true] using h (j,used) (by simp) need
      · simp only [need,if_false,Nat.zero_le]
    · exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht))

private theorem below_bit : ∀ (j : Fin 7) (x : Fin 128), x.val<2^(6-j.val) → digit x.val j.val=false := by native_decide

private theorem ceiling_le {pre : List Nat} {r} (small : r<128) (sorted : ∀ x∈pre,r≤x) :
    r≤pre.foldr min 127 := by
  induction pre with
  | nil => change r≤127; omega
  | cons x tail ih =>
    exact Nat.le_min.mpr ⟨sorted x (by simp),ih (fun y h => sorted y (List.mem_cons_of_mem _ h))⟩

private def extend (pool : List Nat) (d : Nat) : Nat → List Nat → List (List Nat)
  | 0, pre => if admissible pre then [pre] else []
  | n+1, pre =>
    let context := cache pre
    let bits := constraints d n context
    let lower := minimumRow d context.counts
    let upper := pre.foldr min 127
    (pool.filter fun r => decide (lower≤r ∧ r≤upper) && bits.testBit r).flatMap fun r =>
      extend pool d n (pre ++ [r])

def shortlist (d : Nat) := extend ((List.range 128).filter fun m => rowDegree m == d) (2*d) 14 []
private theorem extend_complete {pool rows : List Nat} {d : Nat}
    (good : admissible rows=true) (bounded : ∀ r∈pool, r<128)
    (inPool : ∀ r ∈ rows, r ∈ pool) (ordered : rows.Pairwise (· ≥ ·))
    (cols : ∀ j : Fin 7, colDegree rows j.val = d) (hprefix : colPrefixOrdered rows)
    (tail pre : List Nat) (split : rows = pre ++ tail) :
    rows ∈ extend pool d tail.length pre := by
  induction tail generalizing pre with
  | nil => simp only [List.append_nil] at split; subst pre; simp [extend,good]
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
    have small := bounded r (inPool r inWhole)
    have cut : minimumRow d (cache pre).counts≤r := by
      apply minimumRow_le
      intro t ht deficient
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
      have sum : colDegree pre j.val+colDegree (r::tail) j.val=d := by
        have hit := cols j
        rw [split] at hit
        simpa only [colDegree,List.filter_append,List.length_append] using hit
      change colDegree pre j.val<d at deficient
      obtain ⟨x,hx⟩ := List.exists_mem_of_length_pos (by
        change 0<colDegree (r::tail) j.val; omega :
        0<((r::tail).filter (fun x => digit x j.val)).length)
      obtain ⟨hx,bit⟩ := List.mem_filter.mp hx
      have le : x≤r := by
        rcases List.mem_cons.mp hx with eq|inside
        · subst x; exact Nat.le_refl _
        · exact (List.pairwise_cons.mp (List.pairwise_append.mp (split ▸ ordered)).2.1).1 x inside
      change 2^(6-j.val)≤r
      by_cases ok : 2^(6-j.val)≤r
      · exact ok
      have xlow : x<2^(6-j.val) := by omega
      have zero := below_bit j ⟨x,Nat.lt_of_le_of_lt le small⟩ xlow
      change digit x j.val=false at zero
      rw [zero] at bit; contradiction
    have checks := (exact_test d tail.length (cache pre) ⟨r,small⟩).trans ((accept_eq ..).mpr step)
    simp only [List.length_cons, extend, List.mem_flatMap]
    simp only [Bool.and_eq_true] at checks
    exact ⟨r,List.mem_filter.mpr ⟨inPool r inWhole,by
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨⟨cut,ceiling_le small step.1⟩,checks.2⟩⟩,
      ih (pre ++ [r]) (by simpa using split)⟩

/-- Completeness for arbitrary data: every ordered matrix with the prescribed
row and column degrees occurs in the actual executable candidate list. -/
theorem of_regular_prefix {rows : List Nat} {d : Nat}
    (good : admissible rows=true) (size : rows.length = 14) (bounded : ∀ r ∈ rows, r < 128)
    (degrees : ∀ r ∈ rows, rowDegree r = d) (ordered : rows.Pairwise (· ≥ ·))
    (cols : ∀ j : Fin 7, colDegree rows j.val = 2*d) (hprefix : colPrefixOrdered rows) :
    rows ∈ shortlist d := by
  have mem (r : Nat) (hr : r ∈ rows) :
      r ∈ (List.range 128).filter (fun m => rowDegree m == d) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr (bounded r hr), beq_iff_eq.mpr (degrees r hr)⟩
  simpa only [shortlist, size] using extend_complete good (fun r h => List.mem_range.mp (List.mem_filter.mp h).1) mem ordered cols hprefix rows [] (by simp)


end QGI.SevenFourteen.Enum



