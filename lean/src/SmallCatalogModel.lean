import CatalogComparison
import data.SmallCatalog

namespace QGI.SmallCatalog
open CatalogComparison
open Fifteen (System)
open private get_ofFn from DoubleEightPrepared

/-- Number of rows of a fixed order, including configurations with singleton fibers. -/
def size : Nat → Nat
  | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 10 | 5 => 15 | 6 => 38 | 7 => 57
  | 8 => 143 | 9 => 228 | 10 => 492 | 11 => 769 | 12 => 1845 | 13 => 2806 | _ => 0

abbrev Index (n : Nat) := Fin (size n)
def row {n} (a : Index n) := (rows n)[a.val]?.getD default
def rank {n} (a : Index n) := (row a).rank-1+1
instance {n} (a : Index n) : NeZero (rank a) := ⟨Nat.succ_ne_zero _⟩
abbrev Color {n} (a : Index n) := Fin (rank a)
def model {n} [NeZero n] (a : Index n) : System (rank a) n :=
  let input := row a
  let cells := Vector.ofFn fun (i : Fin n) => Vector.ofFn fun j : Fin n =>
    Fin.ofNat' (rank a) ((input.cells >>> (8*(i.val*n+j.val))) % 256)
  let spots := Vector.ofFn fun (k : Color a) =>
    let v := (input.places >>> (8*k.val)) % 256
    (Fin.ofNat' n (v/n),Fin.ofNat' n (v%n))
  ⟨cells,spots⟩
def frame {n} [NeZero n] (a : Index n) : Frame n (rank a) :=
  let M := model a
  ⟨M.name,M.spot⟩
def chain {n} (a : Index n) : Fifteen.System.Chain (rank a) :=
  (row a).chain.map fun (x,ws) => (Fin.ofNat' (rank a) x,ws)

def good {n r : Nat} (s : System r n) (w : Nat) : Bool :=
  let p := Vector.ofFn (Fifteen.System.point (n:=n) w)
  decide ((∀ i j,p.get i=p.get j → i=j) ∧ ∀ i j,s.name i j=s.name (p.get i) (p.get j))

def covers {n r : Nat} (s : System r n) (ws : List Nat) : Bool :=
  (ws.all (good s)) && decide (∀ i j, let p := s.spot (s.name i j)
    (p=(i,j)) ∨ ws.any (fun w => Fifteen.System.point w p.1 == i && Fifteen.System.point w p.2 == j)=true)

def checkedRow {n} [NeZero n] (a : Index n) : Bool :=
  let s := model a
  decide (∀ k, s.name (s.spot k).1 (s.spot k).2=k) &&
    s.check s.features [] (chain a) && covers s (row a).pairMaps

def rowsOK (n : Nat) [NeZero n] := (List.finRange (size n)).all (fun a => checkedRow (n:=n) a)
def typesOK (n : Nat) [NeZero n] : Bool :=
  let keys := ids (@frame n _)
  decide (∀ a b,keys.get a=keys.get b → a=b)

end QGI.SmallCatalog
