import data.DoubleEightCatalog
import SixteenMapSearch

/-! Exhaustive map search on 636 supplied 8+8 matrices without a cross-fiber
matching. The expected exceptional keys are read only after the search.
This module does not prove the completeness of the input catalog. -/
namespace QGI.DoubleEight

private def color (m : Array Nat) (x y : Nat) : Nat := m[16*x+y]?.getD 256

/-- Every cross color has degree at least two at each vertex of its source
fiber. The common validator additionally checks that all row degrees are
constant within each fiber. -/
private def noCrossMatching (m : Array Nat) : Bool :=
  (List.range 16).all fun x => (List.range 16).all fun y =>
    color m x x == color m y y ||
    decide (2 ≤ ((List.range 16).filter (fun z => color m x z == color m x y)).length)

abbrev Key := SixteenMapSearch.Key

def expectedKeysMatch (ks : List Key) : Bool :=
  Input.expected.length == 260 && Input.expected.eraseDups.length == 260 &&
  ks.length == 260 && ks.eraseDups.length == 260 && ks.all (fun k => Input.expected.contains k)

def census : Option SixteenMapSearch.Counts := do
  if Input.matrices.length != 636 || !Input.matrices.all noCrossMatching then none
  else SixteenMapSearch.onMatrices [8,8] Input.matrices

def agrees (c : SixteenMapSearch.Counts) : Bool :=
  c.algebraicPairs == 642 && c.algebraic == 95167 && c.geometric == 94907 &&
    expectedKeysMatch c.exceptions

def checked : Bool := (census.map agrees).getD false

def runCensus : IO Unit := do
  let some c := census | throw (IO.userError "invalid 8+8 matrices or a matching cross color")
  IO.println s!"catalog={Input.matrices.length}, candidate ordered pairs={c.orderedPairs}"
  IO.println s!"algebraic pairs={c.algebraicPairs}, maps={c.algebraic}, point-induced={c.geometric}, exceptions={c.exceptions.length}"
  unless agrees c do throw (IO.userError "8+8 census counts or exceptional keys differ")
  IO.println "All 260 exceptional keys agree with the archive."

end QGI.DoubleEight
