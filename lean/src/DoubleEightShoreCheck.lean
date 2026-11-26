import Std.Data.HashSet.Lemmas
import Std.Data.HashMap

namespace QGI.DoubleEight.ShoreCheck

abbrev Word := Array Nat

private def decode (line : String) : Word := line.toList.toArray.map fun c =>
  if '0' ≤ c && c ≤ '7' then c.toNat - '0'.toNat else 8

def bank : List Word :=
  (((include_str "data/double-eight-shores.txt").splitOn "\n").map String.trim).filterMap
    (fun s => if s.isEmpty then none else some (decode s))

def bankSet : Std.HashSet Word := Std.HashSet.ofList bank

/-- Rename relation colors in first-appearance order, without moving points. -/
def normalize (w : Word) : Word := Id.run do
  let mut names := Array.replicate 8 8
  let mut next := 0
  let mut out := #[]
  for c in w do
    if c ≥ 8 then return #[]
    if names[c]! = 8 then
      names := names.set! c next
      next := next + 1
    out := out.push names[c]!
  return out

/-- Conjugate the matrix by a point ordering and canonicalize only color names. -/
def relabel (w : Word) (p : Array Nat) : Word :=
  normalize ((Array.range 64).map fun i => w[8 * p[i/8]! + p[i%8]!]!)

def adjacent (w : Word) (j : Nat) : Word := relabel w ((Array.range 8).swapIfInBounds j (j+1))

def normalizedSeeds (seeds : Array Word) : List Word := seeds.toList.map normalize

/-- Validate size, canonical words, containment of seeds, and every generating swap. -/
def checkBank (seeds : Array Word) : Bool :=
  bank.length == 11196 && bankSet.size == 11196 && seeds.size == 21 &&
  (normalizedSeeds seeds).all bankSet.contains &&
  bank.all (fun w => w.size == 64 && w == normalize w &&
    (List.range 7).all fun j => bankSet.contains (adjacent w j))

/-- The explicit seed and point permutation are checked afresh on every
member. Breadth-first search is only a witness generator. -/
structure Witness where
  seed : Nat
  permutation : Array Nat
  deriving Inhabited

def Witness.Valid (p : Witness) (seeds : Array Word) (w : Word) : Prop :=
  p.seed < seeds.size ∧ p.permutation.toList.Perm (List.range 8) ∧
    relabel seeds[p.seed]! p.permutation = w

instance (p : Witness) (seeds : Array Word) (w : Word) : Decidable (p.Valid seeds w) := by
  unfold Witness.Valid
  infer_instance

private def witnesses (seeds : Array Word) : Std.HashMap Word Witness := Id.run do
  let mut queue : Array (Word × Witness) := #[]
  let mut seen : Std.HashMap Word Witness := {}
  for i in [:seeds.size] do
    let w := normalize seeds[i]!
    if !seen.contains w then
      let p := Witness.mk i (Array.range 8)
      seen := seen.insert w p
      queue := queue.push (w,p)
  for i in [:bank.length] do
    let some (w,p) := queue[i]? | return seen
    for j in [:7] do
      let z := adjacent w j
      if bankSet.contains z && !seen.contains z then
        let q := { p with permutation := p.permutation.swapIfInBounds j (j+1) }
        seen := seen.insert z q
        queue := queue.push (z,q)
  return seen

def checkWitnesses (seeds : Array Word) : Bool :=
  let found := witnesses seeds
  bank.all fun w => match found[w]? with
    | some p => decide (p.Valid seeds w)
    | none => false

theorem has_witness_of_check {seeds : Array Word} (ok : checkWitnesses seeds = true)
    {w : Word} (hw : w ∈ bank) : ∃ p : Witness, p.Valid seeds w := by
  obtain h := List.all_eq_true.mp ok w hw
  split at h
  · exact ⟨_, of_decide_eq_true h⟩
  · contradiction

/-- Check inclusion directly against each explicit point permutation, allowing
the caller to use mathlib's complete permutation list. -/
def checkEveryRelabeling (seeds : Array Word) (perms : List (List Nat)) : Bool :=
  seeds.toList.all fun w => perms.all fun p => bankSet.contains (relabel w p.toArray)

theorem relabel_mem_of_check {seeds : Array Word} {perms : List (List Nat)}
    (ok : checkEveryRelabeling seeds perms = true) {w : Word} (hw : w ∈ seeds.toList)
    {p : List Nat} (hp : p ∈ perms) : relabel w p.toArray ∈ bank := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp ok w hw) p hp
  simpa only [bankSet, Std.HashSet.contains_ofList, List.contains_iff_mem] using h

private structure Square where
  rank : Nat
  /-- For each cell: the first cell of its color. -/
  refs : Array Nat
  /-- For each (color,row), a bit mask of its columns. -/
  rowMasks : Array Nat
  /-- For each (color,column), a bit mask of its rows. -/
  colMasks : Array Nat
  deriving Inhabited

private def square (w : Word) : Square := Id.run do
  let rank := w.foldl max 0 + 1
  let mut first := Array.replicate rank 64
  let mut rows := Array.replicate (8*rank) 0
  let mut cols := Array.replicate (8*rank) 0
  for p in [:64] do
    let c := w[p]!
    let i := p/8
    let j := p%8
    if first[c]! = 64 then first := first.set! c p
    rows := rows.modify (8*c+i) (fun mask => mask ||| (1 <<< j))
    cols := cols.modify (8*c+j) (fun mask => mask ||| (1 <<< i))
  return ⟨rank, w.map (fun c => first[c]!), rows, cols⟩

private def bits : Array Nat := (Array.range 256).map fun mask =>
  ((List.range 8).filter fun i => mask.testBit i).length

/-- Encode all (C_s C_tᵀ)(i,j) in base nine. A digit counts at most eight
common neighbors, so equality means equality of every Gram entry. -/
private def gramSignature (cross : Square) : Array Nat := (Array.range 64).map fun p => Id.run do
  let mut sig := 0
  for s in [:cross.rank] do
    let mask := cross.rowMasks[8*s+p/8]!
    for t in [:cross.rank] do
      sig := 9*sig + bits[mask &&& cross.rowMasks[8*t+p%8]!]!
  return sig

private def leftFits (cross : Square) (gram : Array Nat) (shore : Square) : Bool := Id.run do
  -- A uniform cross has constant Gram matrices. A_r J has row sums of A_r.
  if cross.rank = 1 then
    for r in [:shore.rank] do
      let d := bits[shore.rowMasks[8*r]!]!
      for i in [1:8] do
        if bits[shore.rowMasks[8*r+i]!]! != d then return false
    return true
  for p in [:64] do
    if gram[p]! != gram[shore.refs[p]!]! then return false
  -- (A_r C_s)(i,j) is the size of an intersection of two 8-bit masks.
  for r in [:shore.rank] do
    for s in [:cross.rank] do
      for p in [:64] do
        let q := cross.refs[p]!
        if p != q then
          let v := bits[shore.rowMasks[8*r+p/8]! &&& cross.colMasks[8*s+p%8]!]!
          let u := bits[shore.rowMasks[8*r+q/8]! &&& cross.colMasks[8*s+q%8]!]!
          if u != v then return false
  return true

private def parsedBank : Array (Word × Square) := bank.toArray.map fun w => (w, square w)

/-- The actual legal left choices in the order of the supplied bank. -/
def legalWords (w : Word) : Array Word :=
  let cross := square w
  let gram := gramSignature cross
  parsedBank.filterMap fun ⟨word, shore⟩ =>
    if leftFits cross gram shore then some word else none

def transposeWord (w : Word) : Word := (Array.range 64).map fun p => w[8*(p%8)+p/8]!

/-- Right decorations are left decorations for the transposed cross word.
The same point-labeled shore family is used on both sides. -/
def counts (interfaces : Array Word) : Array (Nat × Nat) := interfaces.map fun w =>
  let t := transposeWord w
  let left := (legalWords w).size
  (left, if w == t then left else (legalWords t).size)

def checkCounts (layers : Array (Word × Nat × Nat)) : Bool :=
  layers.size == 89 && layers.all (fun l => l.1.size == 64 && l.1.all (· < 8)) &&
  counts (layers.map Prod.fst) == layers.map Prod.snd

/-- Interpret a row-major finite coloring of the eight points. -/
def colorAt (w : Word) (i j : Fin 8) : Fin 8 := Fin.ofNat' 8 w[8*i.val+j.val]!

def pointRow (p : Nat) : Fin 8 := Fin.ofNat' 8 (p/8)
def pointCol (p : Nat) : Fin 8 := Fin.ofNat' 8 (p%8)

/-- Literal sum over the eight intermediate points, independent of all
mask computations used to find obstruction witnesses. -/
def directProduct (gram : Bool) (cross shore : Word) (r s : Fin 8) (i j : Fin 8) : Nat :=
  (List.ofFn fun k : Fin 8 =>
    if gram then
      if colorAt cross i k = r ∧ colorAt cross j k = s then 1 else 0
    else if colorAt shore i k = r ∧ colorAt cross k j = s then 1 else 0).sum

/-- The two types of intersection numbers must be constant on their output color. -/
def IntersectionRegular (cross shore : Word) : Prop :=
  ∀ (gram : Bool) (r s : Fin 8) (i j i' j' : Fin 8),
    colorAt (if gram then shore else cross) i j = colorAt (if gram then shore else cross) i' j' →
      directProduct gram cross shore r s i j = directProduct gram cross shore r s i' j'

private structure Violation where
  gram : Bool
  r : Nat
  s : Nat
  p : Nat
  q : Nat
  deriving Inhabited

private def Violation.Valid (v : Violation) (cross shore : Word) : Prop :=
  let w := if v.gram then shore else cross
  let r := Fin.ofNat' 8 v.r
  let s := Fin.ofNat' 8 v.s
  colorAt w (pointRow v.p) (pointCol v.p) = colorAt w (pointRow v.q) (pointCol v.q) ∧
    directProduct v.gram cross shore r s (pointRow v.p) (pointCol v.p) ≠
    directProduct v.gram cross shore r s (pointRow v.q) (pointCol v.q)

private instance (v : Violation) (cross shore : Word) : Decidable (v.Valid cross shore) := by
  unfold Violation.Valid
  infer_instance

private def gramObstructions (cross : Square) (signatures : Array Nat) :
    Array (Option Violation) := (Array.range 4096).map fun n => Id.run do
  let p := n/64
  let q := n%64
  if signatures[p]! = signatures[q]! then return none
  for r in [:cross.rank] do
    for s in [:cross.rank] do
      let v := bits[cross.rowMasks[8*r+p/8]! &&& cross.rowMasks[8*s+p%8]!]!
      let u := bits[cross.rowMasks[8*r+q/8]! &&& cross.rowMasks[8*s+q%8]!]!
      if u != v then return some ⟨true,r,s,p,q⟩
  return none

private def findViolation (cross shore : Square) (grams : Array (Option Violation)) :
    Option Violation := Id.run do
  for p in [:64] do
    let q := shore.refs[p]!
    if let some v := grams[64*p+q]! then return some v
  for r in [:shore.rank] do
    for s in [:cross.rank] do
      for p in [:64] do
        let q := cross.refs[p]!
        if p != q then
          let v := bits[shore.rowMasks[8*r+p/8]! &&& cross.colMasks[8*s+p%8]!]!
          let u := bits[shore.rowMasks[8*r+q/8]! &&& cross.colMasks[8*s+q%8]!]!
          if u != v then return some ⟨false,r,s,p,q⟩
  return none

/-- For every bank word outside the chosen list, validate a concrete unequal
entry pair by directly summing its two matrix products over the eight points. -/
def checkExcluded (w : Word) : Bool :=
  let selected := Std.HashSet.ofList (legalWords w).toList
  let cross := square w
  let grams := gramObstructions cross (gramSignature cross)
  parsedBank.toList.all fun ⟨shore, sq⟩ =>
    selected.contains shore || match findViolation cross sq grams with
      | none => false
      | some v => decide (v.Valid w shore)

theorem selected_of_excluded_check {w a : Word} (ok : checkExcluded w = true)
    (ha : a ∈ bank) (h : IntersectionRegular w a) : a ∈ (legalWords w).toList := by
  have ha' : (a,square a) ∈ parsedBank.toList := by
    simpa only [parsedBank, Array.toList_map, List.toList_toArray, List.mem_map] using
      (show ∃ b ∈ bank, (b,square b) = (a,square a) from ⟨a,ha,rfl⟩)
  have checked := List.all_eq_true.mp ok (a,square a) ha'
  change (_ || _) = true at checked
  rcases (Bool.or_eq_true_iff.mp checked) with yes | no
  · simpa only [Std.HashSet.contains_ofList, List.contains_iff_mem] using yes
  · split at no
    · contradiction
    · rename_i v _
      obtain ⟨same, unequal⟩ := of_decide_eq_true no
      exact (unequal (h v.gram _ _ _ _ _ _ same)).elim

end QGI.DoubleEight.ShoreCheck
