import HomogeneousCounts
import Mathlib

/-!
Enumerate every symmetric union of non-diagonal relations in the archived
non-thin schemes of each listed order. Check a vertex permutation from each
union to one specified graph6 record. The discovery program and nauty are not
used by the Lean checker. The external completeness of the small scheme and
vertex-transitive catalogs is a separate input to the graph-theoretic argument.
-/
namespace QGI.Homogeneous.Unions
open QGI.Homogeneous

abbrev Table := Array (Array Nat)

private def at2 (a : Table) (i j d : Nat) : Nat :=
  (a[i]?.getD #[])[j]?.getD d

def colorAt (a : Table) (i j : Nat) : Nat := at2 a i j 0

def targetEntry (target : Graph) (i j : Nat) : Nat := at2 target.rows i j 2

private def schemeTables (raw : String) : Except String (Array Table) := do
  let uncommented := String.intercalate "\n" <|
    (raw.splitOn "\n").map (fun line => (line.splitOn "#").head?.getD "")
  let [_, payload] := uncommented.splitOn ":=" | throw "missing GAP assignment"
  let [arrays, after] := payload.splitOn ";" | throw "missing end of GAP input"
  if !after.trim.isEmpty then throw "extra GAP input after the matrix list"
  let value ← Lean.Json.parse arrays
  Lean.fromJson? value

/-- Colour indices in a cell become powers of two for the independent
non-diagonal transpose orbits. Index 0 in the power table is reserved for the
zero contribution of the diagonal; positive numbers are exponents plus one. -/
structure UnionCode where
  bits : Table
  orbitCount : Nat

private def prepareScheme (n : Nat) (a : Table) : Except String UnionCode := do
  if a.size != n || !a.all (fun row => row.size == n) then throw "invalid scheme dimensions"
  let rank := 1 + a.foldl (fun largest row => row.foldl max largest) 0
  let mut transpose := Array.replicate rank rank
  for i in [:n] do
    for j in [:n] do
      let c := at2 a i j rank
      let ct := at2 a j i rank
      if (c == 0) != (i == j) then throw "unexpected diagonal colour"
      let prev := transpose[c]?.getD rank
      if prev != rank && prev != ct then throw "inconsistent transpose relation"
      transpose := transpose.set! c ct
  let mut orbitNumber := Array.replicate rank 0
  let mut seen := 0
  for c in [1:rank] do
    let ct := transpose[c]?.getD rank
    if ct ≥ rank || transpose[ct]?.getD rank != c then throw "missing transpose partner"
    if c ≤ ct then
      seen := seen + 1
      orbitNumber := (orbitNumber.set! c seen).set! ct seen
  let bits := a.map fun row => row.map (fun c => orbitNumber[c]?.getD 0)
  return ⟨bits, seen⟩

def bitIndex (code : UnionCode) (i j : Nat) : Nat := at2 code.bits i j 0

def edge (code : UnionCode) (mask i j : Nat) : Nat :=
  let k := bitIndex code i j
  if k = 0 then 0 else (mask >>> (k-1)) &&& 1

def image (n : Nat) (p : Array Nat) (i : Fin n) : Nat := p[i.val]?.getD n

/-- Every value is in range, all values differ, all target vertices are met,
and all ordered adjacency entries agree. -/
def Realizes (n : Nat) (src : Nat → Nat → Nat) (target : Graph) (p : Array Nat) : Prop :=
  (∀ i : Fin n, image n p i < n) ∧
  (∀ i j : Fin n, image n p i = image n p j → i = j) ∧
  (∀ j : Fin n, ∃ i : Fin n, image n p i = j.val) ∧
  (∀ i j : Fin n, src i.val j.val = at2 target.rows (image n p i) (image n p j) 2)

instance (n : Nat) (src : Nat → Nat → Nat) (target : Graph) (p : Array Nat) :
    Decidable (Realizes n src target p) := by
  unfold Realizes
  infer_instance

/-- A true result checks an actual adjacency-preserving bijection. -/
theorem permutation_of_passed {n : Nat} {src : Nat → Nat → Nat} {target : Graph} {p : Array Nat}
    (h : decide (Realizes n src target p) = true) :
    ∃ f : Fin n ≃ Fin n, ∀ i j : Fin n,
      src i.val j.val = at2 target.rows (f i).val (f j).val 2 := by
  obtain ⟨rangeOK, inj, sur, edges⟩ := of_decide_eq_true h
  let f : Fin n → Fin n := fun i => ⟨image n p i,rangeOK i⟩
  have one : Function.Injective f := fun i j e => inj i j (congrArg Fin.val e)
  have onto : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := sur j
    exact ⟨i, Fin.ext hi⟩
  exact ⟨Equiv.ofBijective f ⟨one,onto⟩, fun i j => edges i j⟩

private def certRecord (n : Nat) (s : String) : Except String (Nat × Array Nat) := do
  let [target, values] := s.splitOn " " | throw "invalid witness record"
  let some key := target.toNat? | throw "invalid target index"
  let p := (values.toList.map Char.toNat).toArray
  if p.size != n || !p.all (fun c => decide (65 ≤ c ∧ c < 65+n)) then
    throw "permutation length or alphabet is invalid"
  return (key, p.map (fun c => c-65))

structure Inputs where
  schemes : Nat
  unions : Nat
  hits : Nat
  raw : String
  witnesses : String

def inputs : Nat → Option Inputs
  | 16 => some ⟨208,22710,218, include_str "data/homogeneous/unions/as16.gap",
      include_str "data/homogeneous/unions/perms16.txt"⟩
  | 17 => some ⟨4,278,36, include_str "data/homogeneous/unions/as17.gap",
      include_str "data/homogeneous/unions/perms17.txt"⟩
  | 18 => some ⟨90,4690,292, include_str "data/homogeneous/unions/as18.gap",
      include_str "data/homogeneous/unions/perms18.txt"⟩
  | 19 => some ⟨6,534,60, include_str "data/homogeneous/unions/as19.gap",
      include_str "data/homogeneous/unions/perms19.txt"⟩
  | 20 => some ⟨90,10562,620, include_str "data/homogeneous/unions/as20.gap",
      include_str "data/homogeneous/unions/perms20.txt"⟩
  | 21 => some ⟨30,1782,236, include_str "data/homogeneous/unions/as21.gap",
      include_str "data/homogeneous/unions/perms21.txt"⟩
  | 22 => some ⟨14,2362,420, include_str "data/homogeneous/unions/as22.gap",
      include_str "data/homogeneous/unions/perms22.txt"⟩
  | 23 => some ⟨21,2088,188, include_str "data/homogeneous/unions/as23.gap",
      include_str "data/homogeneous/unions/perms23.txt"⟩
  | _ => none

/-- The relation matrices in the published non-thin association-scheme catalog. -/
def rawTables (n : Nat) : List Table :=
  match inputs n with
  | none => []
  | some bundle => ((schemeTables bundle.raw).toOption.getD #[]).toList

structure Block where
  table : Table
  code : UnionCode
  certificates : Array (Nat × Array Nat)

structure Parsed where
  targets : Array Graph
  blocks : List Block
  total : Nat
  hits : Nat

/-- The arrays for a block always come from the complete sequence 0,...,2^r-1.
Each record supplies only a candidate target and vertex permutation. -/
def parseOrder (n : Nat) : Except String Parsed := do
  let some bundle := inputs n | throw "no scheme coverage input for this order"
  let some (recordCount, text) := QGI.Homogeneous.catalog n | throw "missing target catalog"
  let targetRows ← (QGI.Homogeneous.lines text).mapM (QGI.Homogeneous.decode n)
  let targets := targetRows.toArray
  if targets.size != recordCount then throw "target file size mismatch"
  let matrices ← schemeTables bundle.raw
  if matrices.size != bundle.schemes then throw "scheme file size mismatch"
  let certs := (QGI.Homogeneous.lines bundle.witnesses).toArray
  let mut pos := 0
  let mut hit : Std.HashSet Nat := {}
  let mut blocks := #[]
  for A in matrices do
    let code ← prepareScheme n A
    let mut witnesses := #[]
    for _mask in [:2^code.orbitCount] do
      let some record := certs[pos]? | throw "missing permutation"
      let (targetIndex, perm) ← certRecord n record
      if targetIndex ≥ targets.size then throw "target is not in catalog"
      witnesses := witnesses.push (targetIndex,perm)
      hit := hit.insert targetIndex
      pos := pos + 1
    blocks := blocks.push (⟨A, code, witnesses⟩ : Block)
  if certs.size != pos || pos != bundle.unions || hit.size != bundle.hits then
    throw "unexpected coverage totals"
  return ⟨targets,blocks.toList,pos,hit.size⟩

def succeedsFor (n : Nat) (targets : Array Graph) (b : Block) (mask : Nat) : Bool :=
  match b.certificates[mask]? with
  | none => false
  | some (i,p) =>
    match targets[i]? with
    | none => false
    | some target => decide (Realizes n (edge b.code mask) target p)

def allRealized (n : Nat) (v : Parsed) : Bool :=
  v.blocks.all fun b => (List.range (2^b.code.orbitCount)).all (succeedsFor n v.targets b)

def checkOrder (n : Nat) : Except String (Nat × Nat) := do
  let v ← parseOrder n
  if !(allRealized n v) then throw "at least one proposed vertex permutation failed"
  return (v.total, v.hits)

/-- Universal consequence for every parsed scheme and every allowed mask.
The conclusion exhibits an actual equivalence of vertices. -/
theorem allRealized_sound {n : Nat} {v : Parsed} (ok : allRealized n v = true)
    {b : Block} (member : b ∈ v.blocks) {mask : Nat} (bound : mask < 2^b.code.orbitCount) :
    ∃ (i : Nat) (target : Graph), v.targets[i]? = some target ∧
      ∃ f : Fin n ≃ Fin n, ∀ x y : Fin n,
      edge b.code mask x.val y.val = targetEntry target (f x).val (f y).val := by
  have blockOK := List.all_eq_true.mp ok b member
  have thisMask := List.all_eq_true.mp blockOK mask (List.mem_range.mpr bound)
  cases cert : b.certificates[mask]? with
  | none => simp [succeedsFor, cert] at thisMask
  | some w =>
    rcases w with ⟨i,p⟩
    cases row : v.targets[i]? with
    | none => simp [succeedsFor, cert, row] at thisMask
    | some target =>
      refine ⟨i,target,row,permutation_of_passed (p := p) ?_⟩
      simpa only [succeedsFor, cert, row] using thisMask

/-- Closed native evaluation requests, one for each order. These are not
certificates of completeness for the external Hanaki--Miyamoto census. -/
def passed (n expectedUnions expectedHits : Nat) : Bool :=
  match parseOrder n with
  | .error _ => false
  | .ok v => allRealized n v && (v.total == expectedUnions && v.hits == expectedHits)

theorem parsed_coverage_of_passed {n u h : Nat} (ok : passed n u h = true) :
    ∃ v, parseOrder n = .ok v ∧ allRealized n v = true := by
  cases eqParse : parseOrder n with
  | error msg => simp [passed,eqParse] at ok
  | ok v =>
    refine ⟨v, by simp [eqParse], ?_⟩
    cases eqCheck : allRealized n v with
    | false => simp [passed,eqParse,eqCheck] at ok
    | true => rfl

end QGI.Homogeneous.Unions
