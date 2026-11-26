import ZivAvIntrinsic

namespace QGI.Fifteen
abbrev Vertex := Fin 15
structure System (r : Nat) (n : Nat := 15) where
  cells : Vector (Vector (Fin r) n) n
  spots : Vector (Fin n × Fin n) r

namespace System
variable {n r : Nat}
local instance {n : Nat} : BEq (Fin n × Fin n) := instBEqOfDecidableEq
def name (s : System r n) (x y : (Fin n)) := (s.cells.get x).get y
def spot (s : System r n) (k : Fin r) := s.spots.get k
def rev (s : System r n) (k : Fin r) := s.name (s.spot k).2 (s.spot k).1
def paths (s : System r n) (k : Fin r) : Vector (Fin r × Fin r) n :=
  Vector.ofFn fun z => (s.name (s.spot k).1 z,s.name z (s.spot k).2)
abbrev Features (r : Nat) (n : Nat := 15) := Vector (Vector (Fin r × Fin r × Nat) n) r
def features (s : System r n) : Features r n :=
  Vector.ofFn fun k =>
    let ps := s.paths k
    let list := ps.toList
    ps.map fun p => (p.1,p.2,list.count p)

def hash (l : List Nat) : Nat := l.foldl (fun h v => (1000003*h+v+1)%4294967296) 17
def sorted (xs : List Nat) := xs.mergeSort (fun x y => decide (x ≤ y))

def initial (s : System r n) (base : List (Fin r)) : Vector Nat r :=
  Vector.ofFn fun k => hash [if k ∈ base then base.idxOf k + 1 else 0,
    (decide ((s.spot k).1 = (s.spot k).2)).toNat,(decide (s.rev k = k)).toNat]

def step (s : System r n) (fs : Features r n) (old : Vector Nat r) : Vector Nat r :=
  Vector.ofFn fun k =>
    let ts := (fs.get k).toList.map fun p => hash [old.get p.1, old.get p.2.1,p.2.2]
    hash (old.get k :: old.get (s.rev k) :: sorted ts)

def keys (s : System r n) (fs : Features r n) (base : List (Fin r)) : Vector Nat r :=
  let start := s.initial base
  s.step fs (s.step fs (s.step fs start))

def mark (s : System r n) (fs : Features r n) (base : List (Fin r)) (k : Fin r) : Nat :=
  hash (sorted (s.keys fs (base ++ [k])).toList)

def point (w : Nat) (x : (Fin n)) : (Fin n) := ⟨((w >>> (4*x.val)) % 16) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt x.isLt)⟩
def action (s : System r n) (w : Nat) (k : Fin r) :=
  s.name (point w (s.spot k).1) (point w (s.spot k).2)

def Good (s : System r n) (base : List (Fin r)) (x y : Fin r) (w : Nat) : Prop :=
  s.action w x = y ∧ (∀ k ∈ base, s.action w k = k) ∧ Function.Injective (point (n:=n) w) ∧
    Function.Injective (s.action w) ∧
    ∀ i j : (Fin n), s.action w (s.name i j) = s.name (point w i) (point w j)

instance (s : System r n) (base : List (Fin r)) (x y : Fin r) (w : Nat) :
    Decidable (s.Good base x y w) := by unfold Good Function.Injective; infer_instance

abbrev Chain (r : Nat) := List (Fin r × List Nat)

def check (s : System r n) (fs : Features r n) (base : List (Fin r)) : Chain r → Bool
  | [] =>
    let keys := s.keys fs base
    decide (∀ i j : Fin r, keys.get i = keys.get j → i = j)
  | (x,ws)::tail =>
    let keys := s.keys fs base
    let fingerprint := s.mark fs base x
    (List.finRange r).all (fun y => x == y || keys.get x != keys.get y ||
      fingerprint != s.mark fs base y || ws.any (fun w => decide (s.Good base x y w))) &&
      check s fs (base ++ [x]) tail

end System
end QGI.Fifteen
