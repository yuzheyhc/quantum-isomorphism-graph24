import FifteenNamed

namespace QGI.Coherent.SixNineCatalog
open QGI.Fifteen
def left (i : Fin 6) : Vertex := ⟨i.val,by omega⟩
def right (j : Fin 9) : Vertex := ⟨6+j.val,by omega⟩
open private prepare from FifteenCatalog
def value (a : Index) (i j : Vertex) := number a (((row a).cells >>> (8*(15*i.val+j.val))) % 256)

theorem read_cell (a : Index) (i j : Vertex) : (model a).name i j=value a i j := by
  change ((Vector.ofFn (fun (x : Vertex) => Vector.ofFn (fun (y : Vertex) => value a x y)))[i.val])[j.val] = value a i j
  simp only [Vector.getElem_ofFn]

def diagSize (a : Index) (i : Vertex) := (Finset.univ.filter (fun j => value a j j=value a i i)).card
def M (a : Index) (i : Fin 6) (j : Fin 9) := value a (left i) (right j)
private def witness : Nat → Nat × Nat × Nat
  | 91 => (6,2640,1386)
  | 96 => (4,2448,17514)
  | 98 => (0,2640,173376)
  | 115 => (6,2640,1386)
  | 117 => (4,2640,17514)
  | 121 => (4,2640,20586)
  | 123 => (4,2640,20586)
  | 125 => (4,2640,17514)
  | 154 => (6,2448,1386)
  | 157 => (6,2448,1386)
  | 161 => (4,2448,20586)
  | 163 => (4,2448,20586)
  | 165 => (4,2448,17514)
  | 174 => (0,2640,173376)
  | 178 => (0,2640,92196)
  | 180 => (0,2640,156036)
  | 182 => (0,2640,170256)
  | 206 => (0,2640,173376)
  | 208 => (0,2640,173376)
  | 211 => (0,2640,92196)
  | 213 => (0,2640,156036)
  | 215 => (0,2640,170256)
  | _ => (0,0,0)
def flag (a : Index) : Color a := M a 0 (Fin.ofNat' 9 (witness a.val).1)
def rowClass (a : Index) (i : Fin 6) : Fin 3 := Fin.ofNat' 3 (((witness a.val).2.1 >>> (2*i.val)) % 4)
def colClass (a : Index) (i : Fin 9) : Fin 3 := Fin.ofNat' 3 (((witness a.val).2.2 >>> (2*i.val)) % 4)

attribute [local irreducible] row model rank rows15
theorem coordinates : ∀ a : Index, (∃ x, diagSize a x=6) → (∃ x, diagSize a x=9) →
    (∀ i, diagSize a (left i)=6) ∧ ∀ j, diagSize a (right j)=9 := by native_decide

/-- Every six-by-nine restriction with twin rows is uniform or uses
three classes on each shore. The 22 nonuniform certificates supply the
matching color and verify the remaining ordered colors column by column. -/
theorem alternatives : ∀ a : Index, diagSize a (left 0)=6 → diagSize a (right 0)=9 →
    (∃ i j, i≠j ∧ ∀ y, M a i y=M a j y) →
    (∀ i j, M a i j=M a 0 0) ∨
      ((∀ t, ∃ i, rowClass a i=t) ∧ (∀ t, ∃ j, colClass a j=t) ∧
       (∀ i j, M a i j=flag a ↔ rowClass a i=colClass a j) ∧
       ∀ j k, colClass a j=colClass a k → ∀ i, M a i j=M a i k) := by native_decide

end QGI.Coherent.SixNineCatalog
