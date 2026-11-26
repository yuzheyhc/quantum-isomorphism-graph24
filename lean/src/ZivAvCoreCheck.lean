import ZivAvIntrinsic
import SixteenPointSound
import data.ZivAv14

namespace QGI.ZivAv
open SixteenMapSearch
open private pointMap from SixteenMapSearch

abbrev Vertex := Fin 14
abbrev Index := Fin 768

def original (i : Index) : Nat × Nat := cores14[i.val]?.getD (0,0)
def color (i : Index) (x y : Vertex) : Nat := ((original i).2 >>> (8*(14*x.val+y.val))) % 256

private def numerical (word x y : Nat) := (word >>> (8*(14*x+y))) % 256

private def prepareRow (input : Nat × Nat) : Scheme := Id.run do
  let cell := numerical input.2
  let colors := (List.range 256).toArray.map fun t =>
    if t/16 < 14 ∧ t%16 < 14 then cell (t/16) (t%16) else 0
  let rank := colors.foldl max 0 + 1
  let mut places := Array.replicate rank (0,0)
  for x in [:14] do
    for y in [:14] do
      places := places.set! (cell x y) (x,y)
  let mut tr := #[]
  let mut table := Array.replicate (rank*rank*rank) 0
  for k in [:rank] do
    let (x,y) := places[k]!
    tr := tr.push (cell y x)
    for z in [:14] do
      let atIndex := (k*rank+cell x z)*rank+cell z y
      table := table.set! atIndex (table[atIndex]!+1)
  return ⟨input.1,colors,rank,tr,table,#[],[]⟩

private def rawRows := cores14.map prepareRow
private def keyedRows := rawRows.map DoubleEight.Prepared.intrinsicKeys

def raw (i : Index) : Scheme := rawRows[i.val]?.getD ⟨0,#[],0,#[],#[],#[],[]⟩
def keyed (i : Index) : Scheme := keyedRows[i.val]?.getD ⟨0,#[],0,#[],#[],#[],[]⟩

def pointCheck (s : Scheme) (pi : List Nat) : Bool :=
  pointMap s s pi.toArray 14 (List.range 14) (List.range 14) []

def misses (s : Scheme) : List (List Nat) := (enumeratedMaps s s).filter fun pi => !(pointCheck s pi)

/-- Original GAP row identifiers and every palette map without a point
realization in the induced fourteen-point configuration. -/
def exceptions : List (Nat × List Nat) :=
  keyedRows.toList.flatMap fun s => (misses s).map (fun pi => (s.id,pi))

end QGI.ZivAv
