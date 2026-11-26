import SevenFourteenEnum
import FiberRectangles
import Mathlib

namespace QGI.SevenFourteen.Regular
open Enum FiberRectangles
abbrev Bit (m n : Nat) := Fin m → Fin n → Bool
def weight {n} (i : Fin n) := 2^(n-1-i.val)
def mask {n} (f : Fin n → Bool) : Nat := ∑ i, weight i * (f i).toNat
def rows {m n} (a : Bit m n) := List.ofFn (fun i => mask (a i))
def transpose {m n} (a : Bit m n) : Bit n m := fun j i => a i j
def move {m n} (a : Bit m n) (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n)) : Bit m n :=
  fun i j => a (p i) (q j)
def ordered {m n} (a : Bit m n) := ∀ i j, i<j → mask (a j) ≤ mask (a i)
private def score {m n} (a : Bit m n) : Nat := ∑ i, weight i * mask (a i)
private theorem score_transpose {m n} (a : Bit m n) : score (transpose a)=score a := by
  unfold score mask transpose
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

private theorem split_sum {n} (f : Fin n → Nat) {i j : Fin n} (ne : i ≠ j) :
    ∑ k, f k = f i + (f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k) := by
  rw [Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨ne.symm, Finset.mem_univ _⟩),
    Finset.add_sum_erase _ _ (Finset.mem_univ _)]

private theorem ordered_of_max {m n} (a : Bit m n)
    (upper : ∀ i j, score (move a (Equiv.swap i j) (Equiv.refl _)) ≤ score a) : ordered a := by
  intro i j hij
  by_contra! h
  have hw : weight j < weight i := Nat.pow_lt_pow_right (by decide) (by omega)
  have le := upper i j
  change (∑ k, weight k * mask (a (Equiv.swap i j k))) ≤ ∑ k, weight k * mask (a k) at le
  rw [split_sum _ hij.ne, split_sum (fun k => weight k * mask (a k)) hij.ne] at le
  have rest : (∑ k ∈ (Finset.univ.erase i).erase j, weight k * mask (a (Equiv.swap i j k))) =
      ∑ k ∈ (Finset.univ.erase i).erase j, weight k * mask (a k) := by
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hj, hi, _⟩ := (by simpa only [Finset.mem_erase] using hk :
      k ≠ j ∧ k ≠ i ∧ k ∈ (Finset.univ : Finset (Fin m)))
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
theorem exists_normal {m n} (a : Bit m n) :
    ∃ (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n)), ordered (move a p q) ∧ ordered (transpose (move a p q)) := by
  classical
  obtain ⟨⟨p,q⟩, upper⟩ := argmax (fun t : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) => score (move a t.1 t.2))
  have bound (s : Equiv.Perm (Fin m)) (t : Equiv.Perm (Fin n)) : score (move a s t) ≤ score (move a p q) := upper (s,t)
  refine ⟨p,q,ordered_of_max (move a p q) (fun i j => bound ((Equiv.swap i j).trans p) q),
    ordered_of_max _ ?_⟩
  intro i j
  rw [score_transpose]
  exact (score_transpose (move a p ((Equiv.swap i j).trans q))).trans_le
    (bound p ((Equiv.swap i j).trans q))


theorem lt7 : ∀ f : Fin 7 → Bool, mask f<128 := by native_decide
theorem lt14 : ∀ f : Fin 14 → Bool, mask f<16384 := by native_decide
theorem digit7 : ∀ (f : Fin 7 → Bool) (i : Fin 7), (mask f).testBit (6-i.val)=f i := by native_decide
theorem digit14 : ∀ (f : Fin 14 → Bool) (i : Fin 14), (mask f).testBit (13-i.val)=f i := by native_decide

theorem leading_bit_order (u v : Fin 16384) (k : Fin 14) (h : v ≤ u)
    (earlier : ∀ t : Fin 14, t < k → u.val.testBit (13-t.val) = v.val.testBit (13-t.val)) :
    v.val.testBit (13-k.val) = true → u.val.testBit (13-k.val) = true := by
  intro hv
  cases hu : u.val.testBit (13-k.val) with
  | true => rfl
  | false =>
    exfalso
    apply Nat.not_lt_of_ge (show v.val ≤ u.val from h)
    apply Nat.lt_of_testBit _ hu hv
    intro j hj
    by_cases huge : 14 ≤ j
    · have bound : 16384 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < 2) huge
      simp [Nat.testBit_eq_false_of_lt (u.isLt.trans_le bound),
            Nat.testBit_eq_false_of_lt (v.isLt.trans_le bound)]
    · have t : 13-j < 14 := by omega
      have eq := earlier ⟨13-j,t⟩ (by change 13-j < k.val; omega)
      have e : 13-(13-j)=j := by omega
      simpa only [e] using eq


private theorem degree_sum {m} (f : Fin m → Bool) : degree f = ∑ i, (f i).toNat := by
  have e (i : Fin m) : (f i).toNat = (if f i = true then 1 else 0 : Nat) := by cases f i <;> rfl
  simp [degree, e]

private theorem degree_perm {m} (f : Fin m → Bool) (p : Equiv.Perm (Fin m)) :
    degree (fun i => f (p i)) = degree f := by
  simp only [degree_sum]
  exact Equiv.sum_comp p (fun j => (f j).toNat)

private theorem filter_sum (xs : List Nat) (f : Nat → Bool) :
    (xs.filter f).length = (xs.map (fun x => (f x).toNat)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h,ih,Nat.add_comm]


private theorem row_degree (f : Fin 7 → Bool) : rowDegree (mask f) = degree f := by
  have range7 : List.range 7 = List.ofFn (fun i : Fin 7 => i.val) := by decide
  simp only [rowDegree,range7,filter_sum,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    digit,digit7,degree_sum]

private theorem col_degree (a : Bit 14 7) (j : Fin 7) : colDegree (rows a) j.val = degree (transpose a j) := by
  simp only [colDegree,rows,filter_sum,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    digit,digit7,degree_sum,transpose]

private theorem columns_ordered (a : Bit 14 7) (hc : ordered (transpose a)) : colPrefixOrdered (rows a) := by
  intro pre r post split j tied
  have len : pre.length + (post.length + 1) = 14 := by
    simpa [rows] using congrArg List.length split.symm
  let k : Fin 14 := ⟨pre.length, by omega⟩
  have atK : mask (a k) = r := by
    have eq := congrArg (fun xs : List Nat => xs[pre.length]?) split
    change (List.ofFn (fun i => mask (a i)))[pre.length]? = _ at eq
    rw [List.getElem?_ofFn, dif_pos k.isLt] at eq
    simpa [List.getElem?_append,k] using eq
  have before (t : Fin 14) (ht : t < k) : mask (a t) ∈ pre := by
    have lt : t.val < pre.length := ht
    have eq := congrArg (fun xs : List Nat => xs[t.val]?) split
    have same : mask (a t) = pre[t.val] := by
      change (List.ofFn (fun i => mask (a i)))[t.val]? = _ at eq
      rw [List.getElem?_ofFn, dif_pos t.isLt] at eq
      simpa [List.getElem?_append,lt] using eq
    rw [same]; exact List.getElem_mem _
  let l := j.castSucc
  let s := j.succ
  have bits (t : Fin 14) (v : Fin 7) : digit (mask (a t)) v.val = a t v := digit7 _ _
  have left := hc l s (by exact Fin.castSucc_lt_succ j)
  have first := leading_bit_order ⟨_,lt14 (transpose a l)⟩ ⟨_,lt14 (transpose a s)⟩ k left
  have equal : ∀ t : Fin 14, t < k →
      (mask (transpose a l)).testBit (13-t.val) = (mask (transpose a s)).testBit (13-t.val) := by
    intro t ht
    rw [digit14, digit14]
    exact ((bits t l).symm.trans (tied _ (before t ht))).trans (bits t s)
  have cmp := first equal
  rw [digit14,digit14] at cmp
  rw [← atK]
  exact fun h => (bits k l).trans (cmp ((bits k s).symm.trans h))

/-- Every regular 14-by-7 relation has two point permutations putting its
actual Boolean entries into the executable search. -/
theorem exists_enumerated (a : Bit 14 7) (d : Nat)
    (rd : ∀ i, degree (a i) = d) (cd : ∀ j, degree (transpose a j) = 2*d)
    (all : ∀ (p : Equiv.Perm (Fin 14)) (q : Equiv.Perm (Fin 7)), admissible (rows (move a p q))=true) :
    ∃ (p : Equiv.Perm (Fin 14)) (q : Equiv.Perm (Fin 7)), rows (move a p q) ∈ shortlist d := by
  obtain ⟨p,q,ord,dual⟩ := exists_normal a
  refine ⟨p,q,of_regular_prefix (all p q) (by simp [rows]) ?_ ?_ (List.pairwise_ofFn.mpr (fun {_ _} h => ord _ _ h)) ?_ (columns_ordered _ dual)⟩
  · intro r mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact lt7 _
  · intro r mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact (row_degree _).trans ((degree_perm (a (p i)) q).trans (rd _))
  · intro j
    exact (col_degree _ _).trans ((degree_perm (transpose a (q j)) p).trans (cd _))


end QGI.SevenFourteen.Regular



