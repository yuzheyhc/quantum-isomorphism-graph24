import Std

namespace QGI.DoubleEight.Placements

abbrev Word := Array Nat
abbrev Vertex := Fin 16

structure Witness where
  row : Nat
  points : Array Nat
  deriving Inhabited

def point (p : Array Nat) (i : Vertex) : Vertex :=
  ⟨p.getD i.val 16 % 16, Nat.mod_lt _ (by decide)⟩

/-- Independent palettes for the left, forward, reverse, and right blocks.
Reverse colors on the opposite rectangle are indexed by their transpose. -/
def model (cross left right : Word) (i j : Vertex) : Nat :=
  if i.val < 8 then
    if j.val < 8 then left.getD (8*i.val+j.val) 255
    else 8 + cross.getD (8*i.val+(j.val-8)) 255
  else if j.val < 8 then 16 + cross.getD (8*j.val+(i.val-8)) 255
  else 24 + right.getD (8*(i.val-8)+(j.val-8)) 255

def color (m : Word) (i j : Vertex) : Nat := m.getD (16*i.val+j.val) 255

private def inverse (p : Array Nat) : Array Nat := Id.run do
  let mut inv := Array.replicate 16 16
  for i in [:p.size] do
    inv := inv.setIfInBounds p[i]! i
  return inv

private def colorMaps (c l r m : Word) (p : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut forward := Array.replicate 32 255
  let mut backward := Array.replicate 64 255
  for i in List.finRange 16 do
    for j in List.finRange 16 do
      let a := model c l r i j
      let b := color m (point p i) (point p j)
      forward := forward.setIfInBounds a b
      backward := backward.setIfInBounds b a
  return (forward, backward)

def Naming (c l r m : Word) (p forward backward : Array Nat) : Prop :=
  ∀ i j : Vertex,
    forward[model c l r i j]? = some (color m (point p i) (point p j)) ∧
    backward[color m (point p i) (point p j)]? = some (model c l r i j)

private instance (c l r m : Word) (p fw bw : Array Nat) : Decidable (Naming c l r m p fw bw) := by
  unfold Naming
  infer_instance

def checkPlacement (c l r m : Word) (p : Array Nat) : Bool :=
  let inv := inverse p
  let (fw,bw) := colorMaps c l r m p
  decide (∀ i : Vertex, point inv (point p i) = i) &&
    decide (∀ i : Vertex, point p (point inv i) = i) && decide (Naming c l r m p fw bw)

theorem sound {c l r m : Word} {p : Array Nat} (ok : checkPlacement c l r m p = true) :
    (∀ i : Vertex, point (inverse p) (point p i) = i) ∧
    (∀ i : Vertex, point p (point (inverse p) i) = i) ∧
    ∀ i j x y : Vertex, model c l r i j = model c l r x y ↔
      color m (point p i) (point p j) = color m (point p x) (point p y) := by
  simp only [checkPlacement, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨left, right⟩, names⟩ := ok
  refine ⟨left, right, ?_⟩
  intro i j x y
  constructor
  · intro h
    exact Option.some.inj (((names i j).1.symm.trans
      (congrArg (fun a : Nat => (colorMaps c l r m p).1[a]?) h)).trans (names x y).1)
  · intro h
    exact Option.some.inj (((names i j).2.symm.trans
      (congrArg (fun b : Nat => (colorMaps c l r m p).2[b]?) h)).trans (names x y).2)

/-- One layer of legal shore tables, in row-major product order. -/
structure Stratum where
  cross : Word
  left : Array Word
  right : Array Word
  start : Nat
  deriving Inhabited

def checkPair (rows : Array Word) (witnesses : Array Witness) (s : Stratum) (i j : Nat) : Bool :=
  match witnesses[s.start + i*s.right.size + j]?, rows, s.left[i]?, s.right[j]? with
  | some w, ms, some l, some r =>
    match ms[w.row]? with
    | some m => checkPlacement s.cross l r m w.points
    | none => false
  | _, _, _, _ => false

def checkStratum (rows : Array Word) (ws : Array Witness) (s : Stratum) : Bool :=
  (List.range s.left.size).all fun i => (List.range s.right.size).all (checkPair rows ws s i)

def parseWitness (line : String) : Option Witness := do
  let [ident, ps] := line.trim.splitOn " " | none
  let vertices ← ps.toList.mapM fun c =>
    if 'A' ≤ c && c ≤ 'P' then some (c.toNat - 'A'.toNat) else none
  if vertices.length != 16 then none else return ⟨← ident.toNat?, vertices.toArray⟩

end QGI.DoubleEight.Placements
