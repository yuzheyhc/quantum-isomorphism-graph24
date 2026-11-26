import NineNineNormal
import data.NineNineShort
import SixTenCoordinates

namespace QGI.NineNine.Checks
open BareLex (V rows mask transpose)

set_option maxRecDepth 10000
abbrev B := V → V → Bool
abbrev N := V → V → Nat
def matrix (rs : List Nat) : B := fun i j => BareEnum.digit (rs.getD i.val 0) j.val
def prod (f g : N) : N := fun i j => ∑ k, f i k * g k j
def bit (b : B) : N := fun i j => (b i j).toNat
def gram (b : B) := prod (bit b) (bit (transpose b))
def power (g : N) : Nat → N
  | 0 => g
  | k+1 => prod (power g k) g
def hist (g : N) (i : V) (v : Nat) : Nat := ∑ j, if g i j=v then 1 else 0

def pappusRows : List Nat := [448,304,268,162,137,81,70,37,26]
def rectangleRows : List Nat := [448,448,448,56,56,56,7,7,7]
abbrev Entry := List Nat × Nat × Nat × Nat × Nat × Nat
def check (r : Entry) : Bool :=
  let (rs,kind,k,x,y,v) := r
  let i := Fin.ofNat' 9 x
  let j := Fin.ofNat' 9 y
  let b := matrix rs
  let g := power (gram b) k
  let f := prod g (bit b)
  match kind with
  | 0 => decide (b 0 0=true ∧ b i j=true ∧ f 0 0≠f i j)
  | 1 => decide (hist g 0 v≠hist g i v)
  | 2 => decide (∀ z, f i z=f i j → z=j)
  | 3 => decide (rs=pappusRows)
  | 4 => decide (rs=rectangleRows)
  | _ => false

theorem checked : Short.entries.all check=true := by native_decide

def Thin (c : N) := ∃ i j, ∀ z, c i z=c i j → z=j
def Respects (c f : N) := ∀ {i j x y}, c i j=c x y → f i j=f x y

theorem classify (r : Entry) {c : N} (mem : r∈Short.entries)
    (marked : ∀ i j x y, matrix r.1 i j=true → matrix r.1 x y=true → c i j=c x y)
    (constant : ∀ k, Respects c (prod (power (gram (matrix r.1)) k) (bit (matrix r.1))))
    (uniform : ∀ k i v, hist (power (gram (matrix r.1)) k) 0 v=hist (power (gram (matrix r.1)) k) i v) :
    Thin c ∨ r.1=pappusRows ∨ r.1=rectangleRows := by
  obtain ⟨rs,kind,k,x,y,v⟩ := r
  have h : check (rs,kind,k,x,y,v)=true := List.all_eq_true.mp (by simpa using checked : Short.entries.toList.all check=true) _ (by simpa using mem)
  match eq : kind with
  | 0 =>
    simp only [check,eq,decide_eq_true_eq] at h
    exact (h.2.2 (constant k (marked _ _ _ _ h.1 h.2.1))).elim
  | 1 =>
    simp only [check,eq,decide_eq_true_eq] at h
    exact (h (uniform _ _ _)).elim
  | 2 =>
    simp only [check,eq,decide_eq_true_eq] at h
    exact Or.inl ⟨_,_,fun _ hz => h _ (constant k hz)⟩
  | 3 =>
    simp only [check,eq,decide_eq_true_eq] at h
    exact Or.inr (Or.inl h)
  | 4 =>
    simp only [check,eq,decide_eq_true_eq] at h
    exact Or.inr (Or.inr h)
  | k'+5 => simp only [check,eq,Bool.false_eq_true] at h

theorem matrix_rows (b : B) : matrix (rows b)=b := by
  funext i j
  simp only [matrix,rows,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt,
    Option.getD_some,BareEnum.digit,BareLex.mask_digit]

theorem transpose_rows (b : B) : Sieve.transposeRows (rows b)=rows (transpose b) := by
  have range : List.range 9=List.ofFn (fun i : V => i.val) := by decide
  simp only [Sieve.transposeRows,range,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  unfold rows
  congr 1
  funext j
  apply Finset.sum_congr rfl; intro i _
  change 2^(8-i.val) * (matrix (rows b) i j).toNat = 2^(8-i.val) * (b i j).toNat
  rw [matrix_rows]

open private filter_sum from NineNineNormal
private theorem weight (i j : Fin 512) : Sieve.weights.getD (i.val &&& j.val) 0 =
    16 ^ (∑ k : V, (BareEnum.digit i.val k.val).toNat * (BareEnum.digit j.val k.val).toNat) := by
  have lookup : ∀ k : Fin 512, Sieve.weights.getD k.val 0=16^BareEnum.rowDegree k.val := by native_decide
  rw [lookup ⟨_,Nat.and_le_left.trans_lt i.isLt⟩]
  congr 1
  have range : List.range 9=List.ofFn (fun i : V => i.val) := by decide
  simp only [BareEnum.rowDegree,filter_sum,range,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl; intro k _
  simp only [BareEnum.digit,Nat.testBit_and]
  cases i.val.testBit (8-k.val) <;> cases j.val.testBit (8-k.val) <;> rfl

private theorem score (b : B) (i : V) : Sieve.score (rows b) (mask (b i))=∑ j, 16^(gram b j i) := by
  unfold Sieve.score rows
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl; intro j _
  rw [weight ⟨_,BareLex.mask_lt (b j)⟩ ⟨_,BareLex.mask_lt (b i)⟩]
  simp only [BareEnum.digit,BareLex.mask_digit,gram,prod,bit,transpose]

theorem uniform_score (b : B) (eq : ∀ i : V, (∑ j, 16^(gram b j i))=∑ j, 16^(gram b j 0)) :
    Sieve.uniform (rows b)=true := by
  unfold Sieve.uniform
  rw [show (rows b).getD 0 0=mask (b 0) by rfl]
  apply List.all_eq_true.mpr
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  exact beq_iff_eq.mpr ((score b i).trans ((eq i).trans (score b 0).symm))

end QGI.NineNine.Checks



