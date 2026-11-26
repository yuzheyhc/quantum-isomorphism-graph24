import Mathlib
import data.SixPointWitnesses

namespace QGI.SixPointSearch
open scoped BigOperators

abbrev V := Fin 6
abbrev Edge := V × V
abbrev Table := V → V → Nat

def edge (i j : V) : Edge := (min i j, max i j)
def edges : List Edge := (List.finRange 6).flatMap fun i =>
  ((List.finRange 6).filter (fun j => i < j)).map (fun j => (i,j))

structure Atom where
  support : List Edge
  forward : Option (List Edge)
  deriving DecidableEq

def Atom.mark (a : Atom) (i j : V) : Nat :=
  if edge i j ∈ a.support then
    match a.forward with
    | none => 1
    | some f => if (i ≤ j ↔ edge i j ∈ f) then 1 else 2
  else 0

def degree (p : V → V → Bool) (i : V) := ∑ j, if p i j then 1 else 0
abbrev Regular (p : V → V → Bool) := ∀ i, degree p i = degree p 0

def supports (pivot : Edge) (rest : List Edge) : List (List Edge) :=
  (rest.sublists.map (pivot :: ·)).filter fun s =>
    decide (Regular fun i j => decide (edge i j ∈ s))

def atoms (pivot : Edge) (rest : List Edge) : List Atom :=
  (supports pivot rest).flatMap fun s =>
    ⟨s,none⟩ :: (((s.sublists.filter (fun f => pivot ∈ f)).map
      (fun f => (⟨s,some f⟩ : Atom))).filter (fun a =>
      decide (Regular fun i j => decide (a.mark i j = 1))))

def generate : Nat → List Edge → List (List Atom)
  | _, [] => [[]]
  | 0, _ :: _ => []
  | k+1, p :: tail => (atoms p tail).flatMap fun a =>
      (generate k (tail.filter (fun e => e ∉ a.support))).map (a :: ·)

def code : List Atom → Table
  | [], _, _ => 0
  | a::as, i, j => a.mark i j + 3 * code as i j

private def mask (s : List Edge) : Nat :=
  (edges.zipIdx.map (fun (e,k) => if e ∈ s then 2^k else 0)).sum

private def key : List Atom → Nat
  | [] => 0
  | a::as => 1 + mask a.support + 32768 * (a.forward.elim 0 (fun f => mask f + 1)) +
      2^32 * key as

def witness (as : List Atom) : Nat :=
  ((witnesses.binSearch (key as,0) (fun a b => a.1 < b.1)).getD (0,0)).2

def digit (word pos : Nat) : V := ⟨(word / 6^pos)%6, Nat.mod_lt _ (by decide)⟩

def steps (m : Table) (a b : Nat) (i j : V) :=
  ∑ z, if m i z=a ∧ m z j=b then 1 else 0

def checked (cells : Fin 8 → Table) (as : List Atom) : Bool :=
  let m := code as
  let w := witness as
  let u := w/2
  if w%2=0 then
    let f := fun i : V => digit (u/8) i.val
    let model : Fin 8 := ⟨u%8, Nat.mod_lt _ (by decide)⟩
    decide ((∀ i j, f i=f j → i=j) ∧ ∀ i j x y,
      m (f i) (f j)=m (f x) (f y) ↔ cells model i j=cells model x y)
  else
    let a := m 0 (digit u 0)
    let b := m 0 (digit u 1)
    let i := digit u 2
    let j := digit u 3
    let x := digit u 4
    let y := digit u 5
    decide (m i j=m x y ∧ steps m a b i j ≠ steps m a b x y)

end QGI.SixPointSearch
