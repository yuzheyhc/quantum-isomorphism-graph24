import DoubleEightPrepared
import RegionalPlanar

namespace QGI.FourHalfCatalog
open Certificate
set_option maxRecDepth 16000
abbrev Eight := Fin 8
abbrev Four := Fin 4
abbrev W := Fin 20
abbrev Key := DoubleEight.Prepared.Index

def slot (swap : Bool) (i : Fin 16) : Fin 16 := if swap then i+8 else i

def base (a : Key) (swap : Bool) (i j : Fin 16) : Nat :=
  (DoubleEight.Prepared.row a).getD (16*(slot swap i).val+(slot swap j).val) 255

def eight (s : Bool) (i : Eight) : Fin 16 := ⟨(if s then 8 else 0)+i.val,by split <;> omega⟩
def pos (i j : Four) : Nat := if i=j then 0 else if i=j+2 then 2 else 1
def hit (v q : Four) : Bool := decide (v=q ∨ v=q+1)
def cycle (key : Nat) (i : Eight) : Four := Fin.ofNat' 4 (key >>> (2*i.val))
def side (key : Nat) (i : Eight) : Bool := key.testBit i.val

def value (a : Key) (swap : Bool) (q s : Nat) (rev : Bool) (i j : W) : Nat :=
  let qx (x : W) := cycle q (Fin.ofNat' 8 x.val)
  let ys (x : W) := xor (side s (Fin.ofNat' 8 x.val)) rev
  let pt (x : W) := Fin.ofNat' 4 x.val
  let sc (x y : W) := decide ((pt x).val%2=(ys y).toNat)
  if i.val<16 then
    if j.val<16 then base a swap (Fin.ofNat' 16 i.val) (Fin.ofNat' 16 j.val)
    else if i.val<8 then 100+(hit (pt j) (qx i)).toNat else 102+(sc j i).toNat
  else if j.val<8 then 104+(hit (pt i) (qx j)).toNat
  else if j.val<16 then 106+(sc i j).toNat
  else 108+pos (pt i) (pt j)

def fromFn (k : Nat) (f : Fin (k*k) → Nat) : ColorMatrix := ⟨k,111,Array.ofFn f⟩

private theorem lookup {k : Nat} (f : Fin k → Nat) (t : Fin k) (fallback : Nat) :
    (Array.ofFn f)[t.val]?.getD fallback=f t := by
  have h : t.val < (Array.ofFn f).size := by simpa only [Array.size_ofFn] using t.isLt
  rw [getElem?_pos (Array.ofFn f) t.val h]
  simp only [Option.getD_some,Array.getElem_ofFn]

theorem fromFn_read {k : Nat} (f : Fin (k*k) → Nat) (i j : Fin k) (h : i.val*k+j.val<k*k) :
    (fromFn k f).get i.val j.val=f ⟨i.val*k+j.val,h⟩ := by
  unfold fromFn ColorMatrix.get
  exact lookup f ⟨_,h⟩ 111

def matrix (a : Key) (sw : Bool) (q s : Nat) (rev : Bool) : ColorMatrix :=
  fromFn 20 (fun k => value a sw q s rev (Fin.ofNat' 20 (k.val/20)) (Fin.ofNat' 20 k.val))

attribute [local irreducible] value fromFn DoubleEight.Prepared.row
theorem read (a : Key) (sw : Bool) (q s : Nat) (rev : Bool) (i j : W) :
    (matrix a sw q s rev).get i.val j.val=value a sw q s rev i j := by
  unfold matrix
  rw [fromFn_read _ i j (by omega)]
  have ar : ∀ i j : W, Fin.ofNat' 20 ((i.val*20+j.val)/20)=i ∧ Fin.ofNat' 20 (i.val*20+j.val)=j := by decide
  exact congrArg₂ (value a sw q s rev) (ar i j).1 (ar i j).2

end QGI.FourHalfCatalog
