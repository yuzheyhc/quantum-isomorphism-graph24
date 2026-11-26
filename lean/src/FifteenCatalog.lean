import FifteenChain
import data.ZivAv15
import certificates.Witnesses

namespace QGI.Fifteen
abbrev Index := Fin 553
def row (a : Index) : Row := rows15[a.val]?.getD default
def rank (a : Index) := (row a).rank - 1 + 1
abbrev Color (a : Index) := Fin (rank a)
def number (a : Index) (i : Nat) : Color a :=
  ⟨i % (rank a),Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

private def prepare (a : Index) : System (rank a) :=
  let input := row a
  let cells := Vector.ofFn fun (i : Vertex) => Vector.ofFn fun (j : Vertex) =>
    number a ((input.cells >>> (8*(15*i.val+j.val))) % 256)
  let spots := Vector.ofFn fun (k : Color a) =>
    let code := (input.places >>> (8*k.val)) % 256
    (Fin.ofNat' 15 (code/15),Fin.ofNat' 15 (code%15))
  ⟨cells,spots⟩

def model (a : Index) : System (rank a) := prepare a

def base (a : Index) : List (Color a) := if (row a).id = 5 then [number a 1] else []
def chain (a : Index) : System.Chain (rank a) := (row a).chain.map fun (x,ws) => (number a x,ws)

attribute [local irreducible] row model rank rows15

theorem positions : ∀ a : Index, ∀ k : Color a, (model a).name ((model a).spot k).1 ((model a).spot k).2 = k := by
  native_decide

private def checkRow (a : Index) : Bool :=
  let s := model a
  s.check s.features (base a) (chain a)

set_option maxRecDepth 10000 in
private theorem verified : ∀ a : Index, checkRow a=true := by native_decide

theorem passes (a : Index) : (model a).check (model a).features (base a) (chain a) = true :=
  verified a

theorem exceptional : ∀ a : Index, (row a).id=5 →
    (∀ i j : Vertex, ((model a).name i j).val = Certificate.m_fifteen_5.get i.val j.val) ∧
    (number a 1).val=1 ∧
    ∀ t : Color a, (((model a).spot (number a 1)).1=((model a).spot (number a 1)).2 ↔
      ((model a).spot t).1=((model a).spot t).2) → t ≠ number a 1 → t.val=2 := by native_decide

end QGI.Fifteen
