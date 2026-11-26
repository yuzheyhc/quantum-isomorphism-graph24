import Lean

/- Native row propagation for the quasithin certificates. Every rejection
condition is proved sound in RowSwitchKernelSound. -/
namespace QGI.RowSwitchKernel

abbrev Row := Array Nat
abbrev Placed := Nat × Row
abbrev Known := List Placed

def value (r : Row) (i : Nat) := r[i]?.getD 0
def unpack (n w : Nat) : Row := ((List.range n).map fun i => (w/n^i)%n).toArray
def swapMap (n : Nat) (r : Row) : Row := ((List.range n).map fun i =>
  ((List.range n).find? (fun j => j != i && value r i == value r j)).getD i).toArray

def soundMap (n : Nat) (r p : Row) := (List.range n).all fun i =>
  let j := value p i
  j<n && value r j==value r i && value p j==i &&
    (List.range n).all (fun k => value r k != value r i || k==j || k==i)

def act (n : Nat) (p r : Row) : Row := ((List.range n).map fun j => value r (value p j)).toArray

def add (n : Nat) (p : Row) (v : Placed) (known : Known) : Option Known :=
  let i := value p v.1
  let w := act n p v.2
  match known.lookup i with
  | none => some ((i,w)::known)
  | some r => if w==r then some known else none

def applyMap (n : Nat) (p : Row) : Known → Known → Option Known
  | [], known => some known
  | v::vs, known => (add n p v known).bind (applyMap n p vs)

def applyAll (n : Nat) (old : Known) : List Row → Known → Option Known
  | [], known => some known
  | p::ps, known => (applyMap n p old known).bind (applyAll n old ps)

def taggedMaps (n : Nat) (old : Known) := old.filterMap fun v =>
  let p := swapMap n v.2
  if soundMap n v.2 p then some p else none

/-- An additive statistic of the ordered pairs appearing in two rows.
Coincidences of the statistic only leave extra candidates to check. -/
def weight (a b : Nat) := (a+13)*(a+5)*(b+7)*(b+3)*(a+2*b+1)
def sig (n : Nat) (u v : Row) := ((List.range n).map (fun z => weight (value u z) (value v z))).sum

def coherent (n : Nat) (known : Known) : Bool :=
  let tags := known.flatMap fun i => known.map fun j =>
    (value i.2 j.1,value j.2 i.1,sig n i.2 j.2)
  tags.all fun x => tags.lookup x.1 == some x.2

def run (n : Nat) : Nat → Known → Bool
  | 0, old => coherent n old
  | f+1, old =>
    match applyAll n old (taggedMaps n old) old with
    | none => false
    | some xs => if xs.length==old.length then coherent n xs else run n f xs

def start (n : Nat) (rs : List Nat) := ((List.range rs.length).map fun i => (i,unpack n (rs.getD i 0)))
def accepts (n : Nat) (rs : List Nat) := run n 3 (start n rs)

end QGI.RowSwitchKernel
