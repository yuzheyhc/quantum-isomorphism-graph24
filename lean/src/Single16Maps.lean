import data.Single16Catalog
import SixteenMapSearch

/-! Exact census on Hanaki–Miyamoto's 208 supplied non-thin schemes of order 16.
The scheme tests verify that for every colour k and every (x,y) of colour k,
the number of z with colours (i,j) on (x,z),(z,y) is p[k,i,j].
A colour isomorphism preserves sizes and transposes in the homogeneous
case, hence preserves each refinement multiset by induction. Hash equality
is necessary; a collision can only make the subsequent tensor search longer.
On assigning a new colour the search compares every tensor cell involving
that colour and already assigned ones. At a leaf this covers all r³ cells.
Any genuine bijection extends the current partial assignment along its image
of the chosen colour. The vertex search uses the same argument and compares
both orders of each pair. The expected keys are read only after both searches.
This argument records the justification of the pruning rules; a Lean theorem
equating the general search with all mathematical bijections remains open.
To execute after building dependencies: lake env lean --run cli/Single16.lean.
-/
namespace QGI.Single16

abbrev Key := QGI.SixteenMapSearch.Key

def census : Option QGI.SixteenMapSearch.Counts :=
  if Input.matrices.all (fun m => m.all (fun c => decide (c < 15))) then
    QGI.SixteenMapSearch.onMatrices [16] Input.matrices
  else none

/-- Compare actual distinct keys, rather than just the two list lengths.
For this finite input a duplicate key on either side makes comparison fail. -/
def expectedKeysMatch (ks : List Key) : Bool :=
  Input.expected.length == 419 && Input.expected.eraseDups.length == 419 &&
  ks.length == 419 && ks.eraseDups.length == 419 &&
  ks.all (fun k => Input.expected.contains k)

def agrees (c : QGI.SixteenMapSearch.Counts) : Bool :=
  Input.matrices.length == 208 && c.algebraicPairs == 256 &&
    c.algebraic == 2861 && c.geometric == 2442 && expectedKeysMatch c.exceptions

def checked : Bool := (census.map agrees).getD false

def runCensus : IO Unit := do
  let some c := census | throw (IO.userError "invalid relation matrix")
  IO.println s!"catalog={Input.matrices.length}, candidate ordered pairs={c.orderedPairs}"
  IO.println s!"algebraic pairs={c.algebraicPairs}, maps={c.algebraic}, point-induced={c.geometric}, exceptions={c.exceptions.length}"
  unless agrees c do
    throw (IO.userError "census result or exceptional-key set differs from archive")
  IO.println "All 419 exceptional keys match the archived table."

end QGI.Single16
