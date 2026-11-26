import QuasithinFast
import RowDegreeCapacity

namespace QGI.RowCensus
open private eligible eligible_sound from QuasithinFast

private def partitionOK (n : Nat) (rs : List Nat) (w : Nat) :=
  let first := wordDigits n (rs.getD 0 0)
  (List.range rs.length).all fun i =>
    let r := rs.getD i 0
    first.count (digit n r rs.length) != 1 || (List.range n).all fun j => (List.range n).all fun l =>
      (digit n r j==digit n r l) == (digit n w j==digit n w l)

private theorem partition_sound {n : Nat} [NeZero n] {m : Matrix n} (h : Laws m) {rs : List Nat}
    (f : Fits m rs) (pos : 0<rs.length) (k : Fin n) (hk : k.val=rs.length) :
    partitionOK n rs (word m k)=true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hit := List.mem_range.mp hi
  let x : Fin n := ⟨i,lt_trans hit (hk ▸ k.isLt)⟩
  have val (j : Fin n) : digit n (rs.getD i 0) j.val=(m x j).val := f x j hit
  have base (j : Fin n) : digit n (rs.getD 0 0) j.val=(m 0 j).val := f 0 j pos
  have col : digit n (rs.getD i 0) rs.length=(m x k).val := hk ▸ val k
  by_cases one : degree m (m x k)=1
  · apply Bool.or_eq_true_iff.mpr; right
    apply List.all_eq_true.mpr; intro j hj
    apply List.all_eq_true.mpr; intro l hl
    let y : Fin n := ⟨j,List.mem_range.mp hj⟩
    let z : Fin n := ⟨l,List.mem_range.mp hl⟩
    have u := thin_degree h x k one
    have v := thin_degree h k x ((degree_reverse h k x).trans one)
    have equiv : m x y=m x z ↔ m k y=m k z :=
      ⟨rename_one h x k x k y z u rfl,rename_one h k x k x y z v rfl⟩
    exact beq_iff_eq.mpr (Bool.eq_iff_iff.mpr (by
      change (digit n (rs.getD i 0) y.val == digit n (rs.getD i 0) z.val)=true ↔
        (digit n (word m k) y.val == digit n (word m k) z.val)=true
      simpa only [val,digit_word,beq_iff_eq,Fin.val_inj] using equiv))
  · apply Bool.or_eq_true_iff.mpr; left
    simpa only [wordDigits,base,col,countFiber,Fin.val_inj,bne_iff_ne,degree,fiber] using one

def highRows (n : Nat) [NeZero n] (rs : List Nat) :=
  let old := indexed n rs
  let first := wordDigits n (rs.getD 0 0)
  let opts := eligible n old first (Fin.ofNat' n rs.length)
  let tags := facts n rs
  opts.filter fun w => RowSwitchKernel.accepts n (rs++[w]) && freshOK n rs tags w &&
    balancedNext n rs w && partitionOK n rs w

open private index_sound from RowPredictions in
open private extend from RowCensusSound in
theorem high_complete {n : Nat} [NeZero n] (m : Matrix n) (h : Laws m) (rs : List Nat)
    (f : Fits m rs) (pos : 0<rs.length) (k : Fin n) (hk : k.val=rs.length) : word m k∈highRows n rs := by
  have bound : rs.length<n := hk ▸ k.isLt
  have base : wordDigits n (rs.getD 0 0)=wordDigits n (word m 0) :=
    congrArg List.ofFn (funext (fun j => (f 0 j pos).trans (digit_word m 0 j).symm))
  have index : Fin.ofNat' n rs.length=k := Fin.ext (by simp [Fin.ofNat',Nat.mod_eq_of_lt bound,hk])
  refine List.mem_filter.mpr ⟨?_,?_⟩
  · rw [base,index]; exact eligible_sound h k (index_sound f bound.le)
  · simp only [Bool.and_eq_true]
    exact ⟨⟨⟨RowSwitchKernel.accepts_sound h (extend f k hk) (by simp; omega),
      (List.mem_filter.mp (next_complete h f pos k hk)).2⟩,
      (List.mem_filter.mp (balanced_complete m h rs f pos k hk)).2⟩,partition_sound h f pos k hk⟩

end QGI.RowCensus
