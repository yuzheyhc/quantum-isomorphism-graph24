import Lean
import Std.Data.HashSet

/-!
Computations for the eight *homogeneous ordinary graph* catalogs.
Input is the original short graph6 text. All signatures are recomputed in Nat.
Nothing in this module assumes that every graph of the order is homogeneous.
-/
namespace QGI.Homogeneous

structure Graph where
  order : Nat
  rows : Array (Array Nat)
  deriving Inhabited

abbrev Mat := Array (Array Nat)

private def entry (m : Mat) (i j : Nat) : Nat := (m[i]?.getD #[])[j]?.getD 0

private def matrix (n : Nat) (f : Nat → Nat → Nat) : Mat := Id.run do
  let mut a := #[]
  for i in [:n] do
    let mut row := #[]
    for j in [:n] do
      row := row.push (f i j)
    a := a.push row
  return a

/-- Only a single terminal newline is optional; interior empty records are errors. -/
def lines (s : String) : List String :=
  match (s.splitOn "\n").reverse with
  | "" :: rs => rs.reverse
  | rs => rs.reverse

/-- Decode graph6 for orders 0..62, checking alphabet, byte count and zero
padding. Pair (i,j) with i<j has index j(j-1)/2+i, in most-significant-bit order. -/
def decode (expected : Nat) (s : String) : Except String Graph := do
  let codes := (s.toList.map Char.toNat).toArray
  if expected > 62 || codes.isEmpty then throw "invalid short graph6 header"
  if !codes.all (fun c => decide (63 ≤ c ∧ c ≤ 126)) then throw "invalid graph6 character"
  if codes[0]?.getD 0 != expected+63 then throw "order differs from header"
  let edges := expected*(expected-1)/2
  let blocks := (edges+5)/6
  if codes.size != 1+blocks then throw "incorrect graph6 length"
  let bitAt := fun (k : Nat) =>
    (((codes[1+k/6]?.getD 63 - 63) >>> (5-k%6)) &&& 1)
  for k in [edges:6*blocks] do
    if bitAt k != 0 then throw "nonzero graph6 padding"
  let adj := matrix expected fun i j =>
    if i == j then 0 else
      let a := min i j
      let b := max i j
      bitAt (b*(b-1)/2+a)
  return ⟨expected, adj⟩

private def dot (a b : Array Nat) : Nat := Id.run do
  let mut total := 0
  for k in [:a.size] do
    total := total + a[k]! * b[k]!
  return total

/-- Multiply on the right by a symmetric matrix; its rows are its columns. -/
private def mulSymm (n : Nat) (a b : Mat) : Mat :=
  matrix n fun i j => dot a[i]! b[j]!

private def tracePair (n : Nat) (a b : Mat) : Nat := Id.run do
  let mut total := 0
  for i in [:n] do
    for j in [:n] do
      total := total + a[i]![j]! * b[j]![i]!
  return total

private def cliques4 (g : Graph) : Nat := Id.run do
  let mut num := 0
  for i in [:g.order] do
    for j in [i+1:g.order] do
      if entry g.rows i j == 1 then
        for k in [j+1:g.order] do
          if entry g.rows i k == 1 && entry g.rows j k == 1 then
            for l in [k+1:g.order] do
              if entry g.rows i l == 1 && entry g.rows j l == 1 && entry g.rows k l == 1 then
                num := num+1
  return 24*num

/-- Ordered signature: K4, C11, theta(1,3,9), and the 4-cycle with triangles
attached along opposite edges. The second coordinate uses tr(A²A⁹). -/
abbrev Signature := Nat × Nat × Nat × Nat

def signature (g : Graph) : Signature := Id.run do
  let n := g.order
  let a := g.rows
  let a2 := mulSymm n a a
  let a3 := mulSymm n a2 a
  let a6 := mulSymm n a3 a3
  let a9 := mulSymm n a6 a3
  let triangles := matrix n (fun i j => a[i]![j]! * a2[i]![j]!)
  let l := mulSymm n triangles a
  let mut theta := 0
  for i in [:n] do
    for j in [:n] do
      if a[i]![j]! == 1 then
        theta := theta + a3[i]![j]! * a9[i]![j]!
  return (cliques4 g, tracePair n a2 a9, theta, tracePair n l l)

def catalog : Nat → Option (Nat × String)
  | 16 => some (286, include_str "data/homogeneous/trans16.g6")
  | 17 => some (36, include_str "data/homogeneous/trans17.g6")
  | 18 => some (380, include_str "data/homogeneous/trans18.g6")
  | 19 => some (60, include_str "data/homogeneous/trans19.g6")
  | 20 => some (1214, include_str "data/homogeneous/trans20.g6")
  | 21 => some (240, include_str "data/homogeneous/trans21.g6")
  | 22 => some (816, include_str "data/homogeneous/trans22.g6")
  | 23 => some (188, include_str "data/homogeneous/trans23.g6")
  | _ => none

/-- Recover the projected signature list, in the same order as the input
records. Malformed records and wrong input lengths are rejected. -/
def signatures (n : Nat) (select : Signature → Signature) :
    Except String (List Signature) := do
  let some (expected, src) := catalog n | throw "order outside 16..23"
  let records := lines src
  if records.length != expected then throw "wrong number of input records"
  records.mapM fun s => do
    let g ← decode n s
    return select (signature g)

/-- A successful command requires every record to parse and every computed
signature in that order to be distinct. -/
def checkWith (n : Nat) (select : Signature → Signature) : Except String Nat := do
  let values ← signatures n select
  let mut seen : Std.HashSet Signature := {}
  for key in values do
    if seen.contains key then throw s!"signature collision at order {n}"
    seen := seen.insert key
  return seen.size

def checkOrder (n : Nat) : Except String Nat := checkWith n id

/-- The following projections were injective on the corresponding original
graph6 files. They are statements about these finite lists, not all simple graphs. -/
def minimalProjection (n : Nat) (s : Signature) : Signature :=
  let (k,c,t,h) := s
  match n with
  | 16 => (k,c,t,0)
  | 17 | 19 | 23 => (0,0,t,0)
  | 18 | 22 => (0,c,t,0)
  | 20 | 21 => (0,c,t,h)
  | _ => (k,c,t,h)

def checkMinimal (n : Nat) : Except String Nat := checkWith n (minimalProjection n)

/-- A mathematical finite proposition for a given order: after parsing, the
actual list of projected signature values has the claimed length and is Nodup.
The proof probes use list equality and do not need to trust a hash table. -/
def CatalogUnique (n expected : Nat) : Prop :=
  match signatures n (minimalProjection n) with
  | .error _ => False
  | .ok values => values.length = expected ∧ values.Nodup

instance catalogUniqueDecidable (n expected : Nat) : Decidable (CatalogUnique n expected) := by
  unfold CatalogUnique
  split <;> infer_instance

def passed (n expected : Nat) : Bool := decide (CatalogUnique n expected)

theorem unique_of_passed {n expected : Nat} (h : passed n expected = true) :
    CatalogUnique n expected := of_decide_eq_true h

/-- Run as lake env lean --run cli/Homogeneous.lean [order]. -/
def runCLI (args : List String) : IO Unit := do
  let orders ← match args with
    | [] => pure (List.range' 16 8)
    | [arg] =>
      match arg.toNat? with
      | some n => pure [n]
      | none => throw (IO.userError "expected one decimal order or no arguments")
    | _ => throw (IO.userError "usage: HomogeneousCounts.lean [order]")
  for n in orders do
    match checkMinimal n with
    | .error msg => throw (IO.userError msg)
    | .ok k => IO.println s!"order {n}: {k} distinct homogeneous catalog signatures"

end QGI.Homogeneous
