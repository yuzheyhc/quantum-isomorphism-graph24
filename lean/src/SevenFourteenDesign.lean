import SevenFourteenRegular
import data.SevenFourteenShort
import SixTenCoordinates

namespace QGI.SevenFourteen.Design
open Regular Enum
open Coherent.SixTenCoordinates (Shore atPoint Block Laws)
abbrev V := Fin 7
abbrev W := Fin 14
abbrev Matrix (m n : Nat) := Fin m → Fin n → Nat
abbrev N := Matrix 14 7
abbrev B := Bit 14 7
def matrix (rs : List Nat) : B := fun i j => digit (rs.getD i.val 0) j.val
def prod {m n h} (f : Matrix m n) (g : Matrix n h) : Matrix m h := fun i j => ∑ k, f i k*g k j
def bit {m n} (b : Bit m n) : Matrix m n := fun i j => (b i j).toNat
def gram {m n} (b : Bit m n) := prod (bit b) (bit (transpose b))
def power {m} (g : Matrix m m) : Nat → Matrix m m
  | 0 => g
  | k+1 => prod (power g k) g
def score (b : B) (k : Nat) : N :=
  if k=4 then fun i j => (b i j).toNat +
    prod (fun x y => if gram b x y=0 then 1 else 0) (bit b) i j
  else prod (power (gram b) k) (bit b)
def fanoRows : List Nat := [112,112,76,76,67,67,42,42,37,37,25,25,22,22]
def Thin (c : N) := ∃ i j, ∀ z, c i z=c i j → z=j
abbrev Entry := List Nat × Nat × Nat × Nat × Nat
private def check (e : Entry) : Bool :=
  let (rs,kind,k,x,y) := e
  let i := Fin.ofNat' 14 x
  let j := Fin.ofNat' 7 y
  let b := matrix rs
  let t := score b k
  match kind with
  | 1 => decide (∀ z, t i z=t i j → z=j)
  | 2 => decide (rs=fanoRows)
  | _ => false

private theorem checked : Short.entries.all check=true := by native_decide

attribute [local irreducible] Enum.shortlist Short.entries

private theorem classify (r : Entry) (c : N) (mem : r∈Short.entries)
    (constant : ∀ k i j x y, c i j=c x y → score (matrix r.1) k i j=score (matrix r.1) k x y) :
    Thin c ∨ r.1=fanoRows := by
  obtain ⟨rs,kind,k,x,y⟩ := r
  have h := List.all_eq_true.mp (by simpa using checked : Short.entries.toList.all check=true)
    (rs,kind,k,x,y) (by simpa using mem)
  match eq : kind with
  | 0 => simp [check,eq] at h
  | 1 =>
    simp only [check,eq,decide_eq_true_eq] at h
    exact Or.inl ⟨_,_,fun z hz => h z (constant k _ _ _ _ hz)⟩
  | 2 =>
    simp only [check,eq,decide_eq_true_eq] at h
    exact Or.inr h
  | n+3 => simp [check,eq] at h

theorem matrix_rows (b : B) : matrix (rows b)=b := by
  funext i j
  simp only [matrix,rows,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt,
    Option.getD_some,digit,digit7]

private theorem transpose_rows (b : B) : Enum.transposeRows (rows b)=rows (transpose b) := by
  have l : List.range 7=List.ofFn (fun i : V => i.val) := by decide
  have r : List.range 14=List.ofFn (fun i : W => i.val) := by decide
  simp only [Enum.transposeRows,l,r,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  unfold rows
  congr 1
  funext j
  apply Finset.sum_congr rfl; intro i _
  change 2^(13-i.val)*(matrix (rows b) i j).toNat=2^(13-i.val)*(b i j).toNat
  rw [matrix_rows]

private def Lookup (n : Nat) := ∀ t : Fin (2^n),
  weights.getD (t.val%128) 0 * weights.getD (t.val>>>7) 0 =
    16^(∑ i : Fin n, (t.val.testBit (n-1-i.val)).toNat)
private theorem lookup7 : Lookup 7 := by unfold Lookup; native_decide
private theorem lookup14 : Lookup 14 := by unfold Lookup; native_decide

private theorem gram_score {m n} [NeZero m] (b : Bit m n) (i : Fin m)
    (lt : ∀ x : Fin n → Bool, mask x<2^n)
    (bits : ∀ (x : Fin n → Bool) (k : Fin n), (mask x).testBit (n-1-k.val)=x k)
    (table : Lookup n) : Enum.score (rows b) (mask (b i))=∑ j, 16^(gram b j i) := by
  unfold Enum.score rows
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl; intro j _
  rw [table ⟨_,Nat.and_le_left.trans_lt (lt (b j))⟩]
  congr 1
  apply Finset.sum_congr rfl; intro k _
  simp only [Nat.testBit_and,bits,gram,prod,bit,transpose]
  cases b j k <;> cases b i k <;> rfl

private theorem uniform_rows {m n} [NeZero m] (b : Bit m n)
    (lt : ∀ x : Fin n → Bool, mask x<2^n)
    (bits : ∀ (x : Fin n → Bool) (k : Fin n), (mask x).testBit (n-1-k.val)=x k)
    (table : Lookup n) (eq : ∀ i, (∑ j, 16^(gram b j i))=∑ j, 16^(gram b j 0)) :
    Enum.uniform (rows b)=true := by
  unfold Enum.uniform
  rw [show (rows b).getD 0 0=mask (b 0) by simp [rows,List.getD_eq_getElem?_getD,List.getElem?_ofFn,NeZero.pos m]]
  apply List.all_eq_true.mpr
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  exact beq_iff_eq.mpr ((gram_score b i lt bits table).trans ((eq i).trans (gram_score b 0 lt bits table).symm))

variable {s : Nat} {c : Fin s → Fin s → Nat} {a t : Nat}
abbrev cells (Y : Shore c t W) (A : Shore c a V) : N := fun i j => c (atPoint Y i) (atPoint A j)
abbrev mark (Y : Shore c t W) (A : Shore c a V) (v : Nat) : B := fun i j => decide (cells Y A i j=v)

private theorem product_block {j k l m n h} {X : Shore c j (Fin m)} {Y : Shore c k (Fin n)}
    {Z : Shore c l (Fin h)} {f : Matrix m n} {g : Matrix n h} (law : Laws c c)
    (hf : Block X X Y Y f f) (hg : Block Y Y Z Z g g) : Block X X Z Z (prod f g) (prod f g) :=
  fun ⦃_ _ _ _⦄ e => Block.fold law hf hg (fun x y => x*y) e

private theorem gram_block {j k m n} {X : Shore c j (Fin m)} {Y : Shore c k (Fin n)} {b : Bit m n}
    (law : Laws c c) (h : Block X X Y Y b b) : Block X X X X (gram b) (gram b) :=
  product_block law (Block.map h Bool.toNat) (Block.map (Block.flip law h) Bool.toNat)

private theorem sum_gram {j k m n} [NeZero m] {X : Shore c j (Fin m)} {Y : Shore c k (Fin n)} {b : Bit m n}
    (law : Laws c c) (h : Block X X Y Y b b) (i : Fin m) : (∑ z, 16^(gram b z i))=∑ z, 16^(gram b z 0) :=
  Block.diag (Block.fold law (Block.const (L:=X) (L':=X) (R:=X) (R':=X) ()) (gram_block law h)
    (fun _ z => 16^z)) i 0

private theorem named_score {A : Shore c a V} {Y : Shore c t W} {b : B} (law : Laws c c)
    (hb : Block Y Y A A b b) (k : Nat) : Block Y Y A A (score b k) (score b k) := by
  have hg := gram_block law hb
  have bits := Block.map hb Bool.toNat
  by_cases four : k=4
  · simp only [score,four,if_true]
    exact Block.map₂ bits (product_block law (Block.map hg (fun t => if t=0 then (1:Nat) else 0)) bits) Nat.add
  · simp only [score,four,if_false]
    apply product_block law _ bits
    clear four
    induction k with
    | zero => exact hg
    | succ k ih => exact product_block law ih hg

/-- Complete source or target classification. A basic color of either of the
two possible nontrivial small valencies gives a thin interface or the
standard Fano incidence with each line duplicated. -/
theorem alternatives (catalog : Enum.shortlist 2 ++ Enum.shortlist 3=Short.entries.toList.map Prod.fst)
    (law : Laws c c) (Y : Shore c t W) (A : Shore c a V) (v d : Nat)
    (degree : d=2 ∨ d=3) (rd : ∀ i, FiberRectangles.degree (mark Y A v i)=d)
    (cd : ∀ j, FiberRectangles.degree (transpose (mark Y A v) j)=2*d) :
    Thin (cells Y A) ∨ ∃ (e : Equiv.Perm W) (f : Equiv.Perm V), rows (mark (e.trans Y) (f.trans A) v)=fanoRows := by
  obtain ⟨e,f,mem⟩ := Regular.exists_enumerated (mark Y A v) d rd cd (by
    intro e f
    let h : Block (e.trans Y) (e.trans Y) (f.trans A) (f.trans A)
        (move (mark Y A v) e f) (move (mark Y A v) e f) := Block.map Block.names fun z => decide (z=v)
    simp only [Enum.admissible,transpose_rows,Bool.and_eq_true]
    exact ⟨uniform_rows _ lt7 digit7 lookup7 (sum_gram law h),
      uniform_rows _ lt14 digit14 lookup14 (sum_gram law (Block.flip law h))⟩)
  let b := mark (e.trans Y) (f.trans A) v
  have inside : rows b∈shortlist 2++shortlist 3 := by
    rcases degree with rfl|rfl
    · exact List.mem_append.mpr (Or.inl mem)
    · exact List.mem_append.mpr (Or.inr mem)
  rw [catalog] at inside
  obtain ⟨entry,listed,rowEq⟩ := List.mem_map.mp inside
  have cond := classify entry (cells (e.trans Y) (f.trans A)) (by simpa using listed)
  rw [rowEq,matrix_rows] at cond
  have cases := cond
    (fun k _ _ _ _ h => named_score law (Block.map Block.names (fun z => decide (z=v))) k h)
  rcases cases with ⟨i,j,only⟩|fano
  · left; refine ⟨e i,f j,fun z hz => ?_⟩
    obtain ⟨z,rfl⟩ := f.surjective z
    exact congrArg f (only z hz)
  · exact Or.inr ⟨e,f,fano⟩

end QGI.SevenFourteen.Design







