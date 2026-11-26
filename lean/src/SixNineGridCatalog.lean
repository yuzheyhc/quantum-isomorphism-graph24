import SixNineCatalog
import SixTenCoordinates

namespace QGI.Coherent.SixNineGridCatalog
open QGI.Fifteen SixNineCatalog SixTenCoordinates
private def fields : Nat → Nat × Nat × Nat
  | 91 => (6,90,173376)
  | 96 => (4,282,157248)
  | 98 => (0,2640,173376)
  | 115 => (6,90,173376)
  | 117 => (4,90,157248)
  | 121 => (4,90,154176)
  | 123 => (4,90,154176)
  | 125 => (4,90,157248)
  | 154 => (6,282,173376)
  | 157 => (6,282,173376)
  | 161 => (4,282,154176)
  | 163 => (4,282,154176)
  | 165 => (4,282,157248)
  | 174 => (0,2640,173376)
  | 178 => (0,2640,92196)
  | 180 => (0,2640,156036)
  | 182 => (0,2640,170256)
  | 185 => (0,2640,173376)
  | 188 => (0,2640,173376)
  | 190 => (0,2640,157248)
  | 193 => (0,2640,154176)
  | 195 => (0,2640,154176)
  | 197 => (0,2640,157248)
  | 206 => (0,2640,173376)
  | 208 => (0,2640,173376)
  | 211 => (0,2640,92196)
  | 213 => (0,2640,156036)
  | 215 => (0,2640,170256)
  | _ => (0,0,0)
def label (z : Nat) (i : Nat) := Fin.ofNat' 3 ((z >>> (2*i))%4)
def A (a : Index) (i : Fin 6) := label (fields a.val).2.1 i.val
def B (a : Index) (j : Fin 9) := label (fields a.val).2.2 j.val
def z (a : Index) := M a 0 (Fin.ofNat' 9 (fields a.val).1)
def gridMark (a : Index) := M a 0 (if a.val=93 then 4 else if a.val=132 then 2 else 0)
def incidence (a : Index) (j : Fin 9) (i : Fin 6) := decide (M a i j=gridMark a)
def rook (a : Index) (i j : Fin 9) := decide (Block.overlap (incidence a) i j=1)

attribute [local irreducible] row model rows15 rank
theorem classify : ∀ a : Index, diagSize a (left 0)=6 → diagSize a (right 0)=9 →
    (∀ i j, M a i j=M a 0 0) ∨
    ((∀ t, (Finset.univ.filter (fun i => A a i=t)).card=2) ∧
     (∀ t, (Finset.univ.filter (fun j => B a j=t)).card=3) ∧
     (∀ i j, M a i j=z a ↔ A a i=B a j) ∧ ∀ j k, B a j=B a k → ∀ i, M a i j=M a i k) ∨
    ((∀ i, rook a i i=false) ∧ (∀ i j, rook a i j=rook a j i) ∧
     (∀ i, FiberRectangles.degree (rook a i)=4) ∧ ∀ i k, (∀ j, M a i j=M a k j) → i=k) := by native_decide

end QGI.Coherent.SixNineGridCatalog
