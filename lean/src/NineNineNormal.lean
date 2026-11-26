import Mathlib
import NineNineEnum
import FiberRectangles
namespace QGI.NineNine.BareLex


abbrev V := Fin 9
abbrev Matrix := V → V → Bool

private def weight (i : V) : Nat := 2 ^ (8 - i.val)

/-- The first vertex has the most significant bit. -/
def mask (a : V → Bool) : Nat := ∑ j, weight j * (a j).toNat

def rows (a : Matrix) : List Nat := List.ofFn fun i => mask (a i)

def transpose (a : Matrix) : Matrix := fun i j => a j i

def move (a : Matrix) (p q : Equiv.Perm V) : Matrix := fun i j => a (p i) (q j)

def ordered (a : Matrix) : Prop := ∀ i j : V, i < j → mask (a j) ≤ mask (a i)

private def score (a : Matrix) : Nat := ∑ i, weight i * mask (a i)

private theorem score_transpose (a : Matrix) : score (transpose a) = score a := by
  unfold score mask transpose
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem split_sum (f : V → Nat) {i j : V} (ne : i ≠ j) :
    ∑ k, f k = f i + (f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k) := by
  rw [Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨ne.symm, Finset.mem_univ _⟩),
    Finset.add_sum_erase _ _ (Finset.mem_univ _)]

private theorem ordered_of_max (a : Matrix)
    (upper : ∀ i j, score (move a (Equiv.swap i j) (Equiv.refl _)) ≤ score a) : ordered a := by
  intro i j hij
  by_contra! h
  have hw : weight j < weight i := (by decide : ∀ x y : V, x < y → weight y < weight x) i j hij
  have le := upper i j
  change (∑ k, weight k * mask (a (Equiv.swap i j k))) ≤ ∑ k, weight k * mask (a k) at le
  rw [split_sum _ hij.ne, split_sum (fun k => weight k * mask (a k)) hij.ne] at le
  have rest : (∑ k ∈ (Finset.univ.erase i).erase j, weight k * mask (a (Equiv.swap i j k))) =
      ∑ k ∈ (Finset.univ.erase i).erase j, weight k * mask (a k) := by
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hj, hi, _⟩ := (by simpa only [Finset.mem_erase] using hk :
      k ≠ j ∧ k ≠ i ∧ k ∈ (Finset.univ : Finset V))
    rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  rw [rest, Equiv.swap_apply_left, Equiv.swap_apply_right] at le
  rw [← Nat.add_assoc, ← Nat.add_assoc, Nat.add_le_add_iff_right] at le
  zify at le hw h
  nlinarith [mul_pos (sub_pos.mpr hw) (sub_pos.mpr h)]

private theorem argmax {α : Type} [Fintype α] [Nonempty α] (f : α → Nat) :
    ∃ s, ∀ t, f t ≤ f s := by
  obtain ⟨s,_,upper⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  exact ⟨s,fun t => upper t (Finset.mem_univ t)⟩

/-- Maximize a symmetric weighted sum over the finite set of independent
row and column permutations. A swap of two out-of-order rows or columns
would strictly increase it. -/
theorem exists_normal (a : Matrix) :
    ∃ p q : Equiv.Perm V, ordered (move a p q) ∧ ordered (transpose (move a p q)) := by
  classical
  obtain ⟨⟨p,q⟩, upper⟩ := argmax (fun t : Equiv.Perm V × Equiv.Perm V => score (move a t.1 t.2))
  have bound (s t : Equiv.Perm V) : score (move a s t) ≤ score (move a p q) := upper (s,t)
  refine ⟨p,q,ordered_of_max (move a p q) (fun i j => bound ((Equiv.swap i j).trans p) q),
    ordered_of_max _ ?_⟩
  intro i j
  rw [score_transpose]
  exact (score_transpose (move a p ((Equiv.swap i j).trans q))).trans_le
    (bound p ((Equiv.swap i j).trans q))

private def word (a b c d e f g h i : Bool) : Nat :=
  256*a.toNat + (128*b.toNat + (64*c.toNat + (32*d.toNat + (16*e.toNat +
    (8*f.toNat + (4*g.toNat + (2*h.toNat + i.toNat)))))))

private theorem mask_eq (r : V → Bool) :
    mask r = word (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) := by
  simp [mask, weight, word, Fin.sum_univ_succ]

private theorem word_spec : ∀ a b c d e f g h i : Bool,
    let n := word a b c d e f g h i
    n < 512 ∧ ∀ j : V, n.testBit (8-j.val) = (![a,b,c,d,e,f,g,h,i] : V → Bool) j := by
  native_decide

theorem mask_lt (r : V → Bool) : mask r < 512 := by
  rw [mask_eq]; exact (word_spec _ _ _ _ _ _ _ _ _).1

theorem mask_digit (r : V → Bool) (j : V) : (mask r).testBit (8-j.val) = r j := by
  rw [mask_eq, (word_spec _ _ _ _ _ _ _ _ _).2 j]
  fin_cases j <;> rfl

theorem leading_bit_order (u v : Fin 512) (k : V) (h : v ≤ u)
    (earlier : ∀ t : V, t < k → u.val.testBit (8-t.val) = v.val.testBit (8-t.val)) :
    v.val.testBit (8-k.val) = true → u.val.testBit (8-k.val) = true := by
  intro hv
  cases hu : u.val.testBit (8-k.val) with
  | true => rfl
  | false =>
    exfalso
    apply Nat.not_lt_of_ge (show v.val ≤ u.val from h)
    apply Nat.lt_of_testBit _ hu hv
    intro j hj
    by_cases huge : 9 ≤ j
    · have bound : 512 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < 2) huge
      simp [Nat.testBit_eq_false_of_lt (u.isLt.trans_le bound),
            Nat.testBit_eq_false_of_lt (v.isLt.trans_le bound)]
    · have t : 8-j < 9 := by omega
      have eq := earlier ⟨8-j,t⟩ (by change 8-j < k.val; omega)
      have e : 8-(8-j)=j := by omega
      simpa only [e] using eq

end QGI.NineNine.BareLex
namespace QGI.NineNine.BareNormal

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
  have range9 : List.range 9 = List.ofFn (fun i : V => i.val) := by decide
  simp only [rowDegree,range9,filter_sum,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    digit,mask_digit,degree_sum]

private theorem col_degree (a : Matrix) (j : V) : colDegree (rows a) j.val = degree (transpose a j) := by
  simp only [colDegree,rows,filter_sum,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    digit,mask_digit,degree_sum,transpose]

private theorem columns_ordered (a : Matrix) (hc : ordered (transpose a)) : colPrefixOrdered (rows a) := by
  intro pre r post split j tied
  have len : pre.length + (post.length + 1) = 9 := by
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
      (mask (transpose a l)).testBit (8-t.val) = (mask (transpose a s)).testBit (8-t.val) := by
    intro t ht
    rw [mask_digit, mask_digit]
    exact ((bits t l).symm.trans (tied _ (before t ht))).trans (bits t s)
  have cmp := first equal
  rw [mask_digit,mask_digit] at cmp
  rw [← atK]
  exact fun h => (bits k l).trans (cmp ((bits k s).symm.trans h))

/-- Every regular 9-by-9 relation has two point permutations putting its
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

end QGI.NineNine.BareNormal


