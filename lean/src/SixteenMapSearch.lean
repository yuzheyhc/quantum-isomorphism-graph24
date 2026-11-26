import Std

/-! Exhaustive exact color and vertex bijection searches on named 16-point
relation matrices with any given multiset of fiber sizes. -/
namespace QGI.SixteenMapSearch

private def atN (a : Array Nat) (i : Nat) : Nat := a[i]?.getD 0
private def vertex (m : Array Nat) (x y : Nat) : Nat := atN m (16*x+y)
private def index (r k i j : Nat) : Nat := (k*r+i)*r+j

/-- A collision merely leaves more candidates for the subsequent exact checks.
All hash inputs are sorted multisets of label-independent invariants. -/
private def digest (ns : List Nat) : Nat :=
  ns.foldl (fun h x => (1000003*h+x+1) % 4294967291) 17

private def sorted (ns : List Nat) : List Nat :=
  ns.mergeSort (fun x y => decide (x ≤ y))

private def refine (r : Nat) (p tr old : Array Nat) : Array Nat := Id.run do
  let mut next : Array Nat := #[]
  for k in [:r] do
    let mut triples : List Nat := []
    for i in [:r] do
      for j in [:r] do
        let mult := atN p (index r k i j)
        if mult > 0 then
          triples := digest [atN old i, atN old j, mult] :: triples
    next := next.push (digest (atN old k :: atN old (atN tr k) :: sorted triples))
  return next

structure Scheme where
  id : Nat
  colors : Array Nat
  rank : Nat
  trans : Array Nat
  tensor : Array Nat
  keys : Array Nat
  profile : List Nat

/-- Validate the fiber-size multiset, transpose and full intersection tensor.
The initial color keys use cardinality/diagonal/transpose invariants; they
do not fix a name for an individual fiber. Equal-size fibers may be exchanged. -/
def prepare (shape : List Nat) (id : Nat) (m : Array Nat) : Option Scheme := Id.run do
  if m.size != 256 then return none
  let r := m.foldl max 0 + 1
  if r > 256 then return none
  let mut diag := Array.replicate r 0
  for x in [:16] do
    let c := vertex m x x
    diag := diag.set! c (atN diag c + 1)
  if sorted (diag.toList.filter (fun v => v != 0)) != sorted shape then return none
  let mut seen := Array.replicate r false
  let mut left := Array.replicate r 0
  let mut right := Array.replicate r 0
  let mut size := Array.replicate r 0
  let mut rows : Array (Array Nat) := #[]
  let mut tr := Array.replicate r 0
  let mut p := Array.replicate (r*r*r) 0
  for x in [:16] do
    let mut row := Array.replicate r 0
    for y in [:16] do
      let k := vertex m x y
      if (x == y) != (atN diag k != 0) then return none
      row := row.set! k (atN row k + 1)
      size := size.set! k (atN size k + 1)
      let mut counts := Array.replicate (r*r) 0
      for z in [:16] do
        let t := vertex m x z * r + vertex m z y
        counts := counts.set! t (atN counts t + 1)
      if seen[k]?.getD false then
        if atN left k != vertex m x x || atN right k != vertex m y y ||
            atN tr k != vertex m y x then return none
        for t in [:r*r] do
          if atN p (k*r*r+t) != atN counts t then return none
      else
        seen := seen.set! k true
        left := left.set! k (vertex m x x)
        right := right.set! k (vertex m y y)
        tr := tr.set! k (vertex m y x)
        for t in [:r*r] do
          p := p.set! (k*r*r+t) (atN counts t)
    for u in [:x] do
      if vertex m x x == vertex m u u && rows[u]?.getD #[] != row then return none
    rows := rows.push row
  if size.any (· == 0) then return none
  let mut keys := ((List.range r).map (fun k =>
    digest [if atN diag k != 0 then 1 else 0, if atN tr k == k then 1 else 0,
      atN size k, atN diag (atN left k), atN diag (atN right k)])).toArray
  for _ in [:3] do
    keys := refine r p tr keys
  return some ⟨id,m,r,tr,p,keys,sorted keys.toList⟩

abbrev Pair := Nat × Nat
abbrev Assigned := List Pair
abbrev Key := Nat × Nat × List Nat

private def mulC (a : Scheme) (k i j : Nat) : Nat :=
  atN a.tensor (index a.rank k i j)

/-- Compare every newly determined tensor entry. All three positions for the
new colour matter, including repeated indices. -/
private def tensorOK (s t : Scheme) (d : Assigned) (x y : Nat) : Bool :=
  let ds := (x,y)::d
  ds.all fun a => ds.all fun b =>
    mulC s x a.1 b.1 == mulC t y a.2 b.2 &&
    mulC s a.1 x b.1 == mulC t a.2 y b.2 &&
    mulC s a.1 b.1 x == mulC t a.2 b.2 y

private def transOK (s t : Scheme) (d : Assigned) (x y : Nat) : Bool :=
  ((atN s.trans x == x) == (atN t.trans y == y)) &&
    d.all (fun a => (atN s.trans x == a.1) == (atN t.trans y == a.2))

/-- Choose one source element, preferring its shortest available target list.
Ties are immaterial; all choices for the selected element are still searched. -/
private def nextChoice (pending : List Nat) (options : Nat → List Nat) :
    Option (Nat × List Nat) :=
  pending.foldl (fun best x =>
    let ys := options x
    match best with
    | none => some (x,ys)
    | some old => if ys.length < old.2.length then some (x,ys) else best) none

private def asMap (n : Nat) (d : Assigned) : List Nat :=
  (List.range n).map fun i => ((d.find? (fun a => a.1 == i)).map Prod.snd).getD n

private def searchMaps (s t : Scheme) : Nat → List Nat → List Nat → Assigned → List (List Nat)
  | 0, pending, free, d => if pending.isEmpty && free.isEmpty then [asMap s.rank d] else []
  | fuel+1, pending, free, d =>
    match nextChoice pending (fun x => free.filter (fun y =>
      atN s.keys x == atN t.keys y && transOK s t d x y)) with
    | none => []
    | some (x,ys) =>
      ys.flatMap fun y =>
        if tensorOK s t d x y then
          searchMaps s t fuel (pending.erase x) (free.erase y) ((x,y)::d)
        else []

private def pointOK (s t : Scheme) (pi : Array Nat) (d : Assigned) (x y : Nat) : Bool :=
  ((x,y)::d).all fun a =>
    atN pi (vertex s.colors x a.1) == vertex t.colors y a.2 &&
    atN pi (vertex s.colors a.1 x) == vertex t.colors a.2 y

/-- Assigned source and image vertices are removed after every decision.
The leaf is reached only after every ordered coloured pair has been checked. -/
private def pointMap (s t : Scheme) (pi : Array Nat) : Nat → List Nat → List Nat → Assigned → Bool
  | 0, pending, free, _ => pending.isEmpty && free.isEmpty
  | fuel+1, pending, free, d =>
    match nextChoice pending (fun x => free.filter (fun y => pointOK s t pi d x y)) with
    | none => false
    | some (x,ys) => ys.any fun y =>
       pointMap s t pi fuel (pending.erase x) (free.erase y) ((x,y)::d)

structure Counts where
  orderedPairs : Nat := 0
  algebraicPairs : Nat := 0
  algebraic : Nat := 0
  geometric : Nat := 0
  exceptions : List Key := []

def onMatrices (shape : List Nat) (data : List (Array Nat)) : Option Counts := do
  let ids := List.range data.length
  let raw := ids.zip data
  let schemes ← raw.mapM (fun im => prepare shape (im.1+1) im.2)
  let vs := List.range 16
  return Id.run do
    let mut result : Counts := {}
    for s in schemes do
      for t in schemes do
        if s.rank == t.rank && s.profile == t.profile then
          result := {result with orderedPairs := result.orderedPairs+1}
          let cs := List.range s.rank
          let maps := searchMaps s t s.rank cs cs []
          if !maps.isEmpty then
            result := {result with algebraicPairs := result.algebraicPairs+1}
          for pi in maps do
            result := {result with algebraic := result.algebraic+1}
            if pointMap s t pi.toArray 16 vs vs [] then
              result := {result with geometric := result.geometric+1}
            else
              result := {result with exceptions := (s.id,t.id,pi)::result.exceptions}
    return result

end QGI.SixteenMapSearch
