import DoubleEightBareLex
import DoubleEightBareEnum
import FiberRectangles

namespace QGI.DoubleEight.BareNormal

open BareLex BareEnum FiberRectangles

private theorem degree_sum (f : V → Bool) : degree f = ∑ i, (f i).toNat := by
  have e (i : V) : (f i).toNat = (if f i = true then 1 else 0 : Nat) := by cases f i <;> rfl
  simp [degree, e]

private theorem degree_perm (f : V → Bool) (p : Equiv.Perm V) :
    degree (fun i => f (p i)) = degree f := by
  simp only [degree_sum]
  exact Equiv.sum_comp p (fun j => (f j).toNat)

private theorem filter_sum (xs : List Nat) (f : Nat → Bool) :
    (xs.filter f).length = (xs.map (fun x => (f x).toNat)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h,ih,Nat.add_comm]

private theorem row_degree (f : V → Bool) : rowDegree (mask f) = degree f := by
  have range8 : List.range 8 = List.ofFn (fun i : V => i.val) := by decide
  simp only [rowDegree,range8,filter_sum,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    digit,mask_digit,degree_sum]

private theorem col_degree (a : Matrix) (j : V) : colDegree (rows a) j.val = degree (transpose a j) := by
  simp only [colDegree,rows,filter_sum,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    digit,mask_digit,degree_sum,transpose]

private theorem columns_ordered (a : Matrix) (hc : ordered (transpose a)) : colPrefixOrdered (rows a) := by
  intro pre r post split j tied
  have len : pre.length + (post.length + 1) = 8 := by
    simpa [rows] using congrArg List.length split.symm
  let k : V := ⟨pre.length, by omega⟩
  have atK : mask (a k) = r := by
    have eq := congrArg (fun xs : List Nat => xs[pre.length]?) split
    change (List.ofFn (fun i => mask (a i)))[pre.length]? = _ at eq
    rw [List.getElem?_ofFn, dif_pos k.isLt] at eq
    simpa [List.getElem?_append,k] using eq
  have before (t : V) (ht : t < k) : mask (a t) ∈ pre := by
    have lt : t.val < pre.length := ht
    have eq := congrArg (fun xs : List Nat => xs[t.val]?) split
    have same : mask (a t) = pre[t.val] := by
      change (List.ofFn (fun i => mask (a i)))[t.val]? = _ at eq
      rw [List.getElem?_ofFn, dif_pos t.isLt] at eq
      simpa [List.getElem?_append,lt] using eq
    rw [same]; exact List.getElem_mem _
  let l := j.castSucc
  let s := j.succ
  have bits (t : V) (v : V) : digit (mask (a t)) v.val = a t v := mask_digit _ _
  have left := hc l s (by exact Fin.castSucc_lt_succ j)
  have first := leading_bit_order ⟨_,mask_lt (transpose a l)⟩ ⟨_,mask_lt (transpose a s)⟩ k left
  have equal : ∀ t : V, t < k →
      (mask (transpose a l)).testBit (7-t.val) = (mask (transpose a s)).testBit (7-t.val) := by
    intro t ht
    rw [mask_digit, mask_digit]
    exact ((bits t l).symm.trans (tied _ (before t ht))).trans (bits t s)
  have cmp := first equal
  rw [mask_digit,mask_digit] at cmp
  rw [← atK]
  exact fun h => (bits k l).trans (cmp ((bits k s).symm.trans h))

/-- Every regular 8-by-8 relation has two point permutations putting its
actual Boolean entries into the executable search. -/
theorem exists_enumerated (a : Matrix) (d : Nat)
    (rd : ∀ i, degree (a i) = d) (cd : ∀ j, degree (transpose a j) = d) :
    ∃ p q : Equiv.Perm V, rows (move a p q) ∈ candidates d := by
  obtain ⟨p,q,ord,dual⟩ := exists_normal a
  refine ⟨p,q,of_regular_prefix (by simp [rows]) ?_ ?_ (List.pairwise_ofFn.mpr (fun {_ _} h => ord _ _ h)) ?_ (columns_ordered _ dual)⟩
  · intro r mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact mask_lt _
  · intro r mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact (row_degree _).trans ((degree_perm (a (p i)) q).trans (rd _))
  · intro j
    exact (col_degree _ _).trans ((degree_perm (transpose a (q j)) p).trans (cd _))

end QGI.DoubleEight.BareNormal