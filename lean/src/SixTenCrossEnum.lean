import Lean

namespace QGI.SixTen.Cross

abbrev L := Fin 6
abbrev R := Fin 10
abbrev Matrix := L → R → Bool

def bit (c : Nat) (i : L) : Bool := c.testBit i.val
def weight (c : Nat) : Nat := (List.finRange 6).countP (bit c)
def rowCount (cols : List Nat) (i : L) := cols.countP fun c => bit c i
def asMatrix (cols : List Nat) : Matrix := fun i j => bit (cols.getD j.val 0) i

def leftOverlap (cols : List Nat) (i h : L) := cols.countP fun c => bit c i && bit c h
def rightOverlap (c d : Nat) := (List.finRange 6).countP fun i => bit c i && bit d i

def leftHist (cols : List Nat) (i : L) : List Nat :=
  List.ofFn fun k : Fin 6 => (List.finRange 6).countP fun h => leftOverlap cols i h == k.val

def rightHist (cols : List Nat) (j : R) : List Nat :=
  List.ofFn fun k : Fin 4 => cols.countP fun c => rightOverlap (cols.getD j.val 0) c == k.val

def uniformHist (cols : List Nat) : Bool :=
  let h₁ := leftHist cols 0
  let h₂ := rightHist cols 0
  (List.finRange 6).all (fun i => leftHist cols i == h₁) &&
    (List.finRange 10).all (fun j => rightHist cols j == h₂)

private def pool := (List.range 64).filter fun c => weight c == 3

private def feasible (counts : Array Nat) (c more : Nat) : Bool :=
  (List.finRange 6).all fun i =>
    let next := counts.getD i.val 0 + (bit c i).toNat
    next ≤ 5 && 5 ≤ next + more

private def extend : Nat → Nat → List Nat → List (List Nat)
  | 0, _, pre => [pre]
  | more+1, lo, pre =>
    let counts := Array.ofFn (rowCount pre)
    pool.flatMap fun c =>
      if decide (lo ≤ c) && feasible counts c more then extend more c (pre ++ [c]) else []

def regularMatrices : List (List Nat) := extend 10 0 []

private theorem step {pre tail : List Nat} {c : Nat} (degree : ∀ i, rowCount (pre ++ c :: tail) i = 5) :
    feasible (Array.ofFn (rowCount pre)) c tail.length = true := by
  apply List.all_eq_true.mpr
  intro i _
  have total := degree i
  have upper := @List.countP_le_length Nat (fun c => bit c i) tail
  simp only [rowCount,List.countP_append,List.countP_cons] at total
  simp only [Array.getD, Array.size_ofFn, i.isLt, Array.getElem_ofFn, dite_true]
  cases h : bit c i <;> simp_all [rowCount,Bool.toNat] <;> omega

private theorem extend_complete {cols : List Nat} (bound : ∀ c ∈ cols, c < 64)
    (weights : ∀ c ∈ cols, weight c = 3) (degrees : ∀ i, rowCount cols i = 5)
    (sorted : cols.Pairwise (· ≤ ·)) (pre tail : List Nat) (lo : Nat)
    (eqn : cols = pre ++ tail) (lower : ∀ c ∈ tail, lo ≤ c) :
    cols ∈ extend tail.length lo pre := by
  induction tail generalizing pre lo with
  | nil => simpa [extend] using eqn
  | cons c tail ih =>
    have member : c ∈ cols := by simp [eqn]
    have inPool : c ∈ pool :=
      List.mem_filter.mpr ⟨List.mem_range.mpr (bound c member),beq_iff_eq.mpr (weights c member)⟩
    have later : ∀ x ∈ tail, c ≤ x :=
      (List.pairwise_cons.mp (List.pairwise_append.mp (eqn ▸ sorted)).2.1).1
    have pass := step (eqn ▸ degrees)
    apply List.mem_flatMap.mpr
    refine ⟨c,inPool,?_⟩
    simpa only [decide_eq_true (lower c (by simp)),Bool.true_and,pass,if_true] using
      ih (pre ++ [c]) c (by simpa using eqn) later

theorem regular_complete {cols : List Nat} (size : cols.length = 10)
    (bound : ∀ c ∈ cols, c < 64) (weights : ∀ c ∈ cols, weight c = 3)
    (degrees : ∀ i, rowCount cols i = 5) (sorted : cols.Pairwise (· ≤ ·)) :
    cols ∈ regularMatrices := by
  simpa only [regularMatrices, size] using
    extend_complete bound weights degrees sorted [] cols 0 (by simp) (by simp)

end QGI.SixTen.Cross