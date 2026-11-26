import DoubleEightBareLaws

namespace QGI.DoubleEight.ColumnLaws

open ShoreCensus (V Coloring Homogeneous side)
open FixedInterface (Compatible HasIntersectionNumbers product transpose)
open BareLaws (Respects rowHistogram)
open Finset
open scoped BigOperators

/-- Value of a table at a representative of a specified color, or zero when
that color does not occur. Its use below is independent of the representative. -/
noncomputable def colorValue (partition table : Coloring) (value : Nat) : Nat := by
  classical
  exact if h : ∃ p : V × V, partition p.1 p.2 = value then table h.choose.1 h.choose.2 else 0

private theorem colorValue_eq {partition table : Coloring} (h : Respects partition table)
    {v : Nat} {i j : V} (e : partition i j = v) : colorValue partition table v = table i j := by
  classical
  have he : ∃ p : V × V, partition p.1 p.2 = v := ⟨(i,j), e⟩
  simp only [colorValue, dif_pos he]
  exact h _ _ _ _ (he.choose_spec.trans e.symm)

/-- For cross entry C(x,j)=s, quota(a,s,t) counts y with L(x,y)=a and C(y,j)=t. -/
noncomputable def quota (left cross : Coloring) (a s t : Nat) : Nat :=
  colorValue cross (product left cross a t) s

/-- For left entry L(x,y)=a, gram(a,s,t) counts j with C(x,j)=s and C(y,j)=t. -/
noncomputable def gram (left cross : Coloring) (a s t : Nat) : Nat :=
  colorValue left (product cross (transpose cross) s t) a

theorem quota_at {left cross : Coloring} (h : Compatible cross left) (a t : Nat) (x j : V) :
    quota left cross a (cross x j) t = product left cross a t x j :=
  colorValue_eq (h.2 a t) rfl

theorem gram_at {left cross : Coloring} (h : Compatible cross left) (s t : Nat) (x y : V) :
    gram left cross (left x y) s t = product cross (transpose cross) s t x y :=
  colorValue_eq (h.1 s t) rfl

/-- All columns obey the same quotas after their entries are colored by C.
The left degree uses the directed relation from x to y. -/
theorem column_quota {left cross : Coloring} (h : Compatible cross left) {s : Nat}
    (a t : Nat) (x j : V) (entry : cross x j = s) :
    (∑ y : V, if left x y = a ∧ cross y j = t then 1 else 0 : Nat) = quota left cross a s t := by
  rw [← entry, quota_at h]
  simp only [product, List.sum_ofFn]

/-- Two orders of counting the same pairs (y,j) at a fixed point x. The
identity also holds for absent colors, with both resulting products zero. -/
theorem balance_at {left cross : Coloring} (h : Compatible cross left) (a s t : Nat) (x : V) :
    rowHistogram left a x * gram left cross a s t =
      rowHistogram cross s x * quota left cross a s t := by
  let incidence := fun y j : V =>
    if left x y = a ∧ cross x j = s ∧ cross y j = t then 1 else 0
  calc
    _ = ∑ y : V, ∑ j : V, incidence y j := by
      rw [rowHistogram, Finset.sum_mul]
      apply sum_congr rfl
      intro y _
      by_cases hy : left x y = a
      · rw [if_pos hy, one_mul, ← hy, gram_at h]
        simp only [product, transpose, List.sum_ofFn, incidence, hy, true_and]
      · simp [hy, incidence]
    _ = ∑ j : V, ∑ y : V, incidence y j := Finset.sum_comm
    _ = _ := by
      rw [rowHistogram, Finset.sum_mul]
      apply sum_congr rfl
      intro j _
      by_cases hj : cross x j = s
      · rw [if_pos hj, one_mul, ← hj, quota_at h]
        simp only [product, List.sum_ofFn, incidence, hj, true_and]
      · simp [hj, incidence]

/-- k_a is the outgoing internal valency, d_s the outgoing cross valency,
both evaluated at the distinguished point 0. No reverse relation is needed. -/
theorem valency_balance {left cross : Coloring} (h : Compatible cross left) (a s t : Nat) :
    rowHistogram left a 0 * gram left cross a s t =
      rowHistogram cross s 0 * quota left cross a s t := balance_at h a s t 0

/-- For a specified internal edge this is the actual shared-column count in
its row-pair, expressed using the same global quotas for all columns. -/
theorem gram_entry_balance {left cross : Coloring} (h : Compatible cross left)
    (s t : Nat) (x y : V) :
    rowHistogram left (left x y) 0 * product cross (transpose cross) s t x y =
      rowHistogram cross s 0 * quota left cross (left x y) s t := by
  simpa only [gram_at h] using valency_balance h (left x y) s t

theorem column_quota_card {left cross : Coloring} (h : Compatible cross left)
    (a s t : Nat) (x j : V) (entry : cross x j = s) :
    ((univ : Finset V).filter fun y => left x y = a ∧ cross y j = t).card =
      quota left cross a s t := by
  simpa using column_quota h a t x j entry

theorem quota_recovered {left cross : Coloring} (h : Compatible cross left)
    (a s t : Nat) (hs : 0 < rowHistogram cross s 0) :
    (rowHistogram left a 0 * gram left cross a s t) / rowHistogram cross s 0 =
      quota left cross a s t := by
  rw [valency_balance h]
  exact Nat.mul_div_cancel_left _ hs

/-- The exact divisibility test and target used by the column enumeration.
The remainder is zero even when the internal relation is absent. -/
theorem gram_integral {left cross : Coloring} (h : Compatible cross left) (a s t : Nat) :
    (rowHistogram cross s 0 * quota left cross a s t) % rowHistogram left a 0 = 0 := by
  rw [← valency_balance h]
  exact Nat.mul_mod_right _ _

theorem gram_recovered {left cross : Coloring} (h : Compatible cross left)
    (a s t : Nat) (ha : 0 < rowHistogram left a 0) :
    (rowHistogram cross s 0 * quota left cross a s t) / rowHistogram left a 0 =
      gram left cross a s t := by
  rw [← valency_balance h]
  exact Nat.mul_div_cancel_left _ ha

theorem raw_column_laws (m : V ⊕ V → V ⊕ V → Nat)
    (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x) (products : HasIntersectionNumbers m) :
    let c : Coloring := fun i j => m (.inl i) (.inr j)
    let l : Coloring := fun i j => m (.inl i) (.inl j)
    (∀ a t x j, (∑ y : V, if l x y = a ∧ c y j = t then 1 else 0 : Nat) =
      quota l c a (c x j) t) ∧
    ∀ s t x y, rowHistogram l (l x y) 0 * product c (transpose c) s t x y =
      rowHistogram c s 0 * quota l c (l x y) s t := by
  have h := (BareLaws.raw_compatible m rectangle rev products).1
  exact ⟨fun a t x j => column_quota h a t x j rfl, gram_entry_balance h⟩

end QGI.DoubleEight.ColumnLaws
