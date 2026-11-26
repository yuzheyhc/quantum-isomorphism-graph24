import Mathlib

namespace QGI.DoubleEight.BareLex


abbrev V := Fin 8
abbrev Matrix := V → V → Bool

private def weight (i : V) : Nat := 2 ^ (7 - i.val)

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

private def octet (a b c d e f g h : Bool) : Nat :=
  128*a.toNat + (64*b.toNat + (32*c.toNat + (16*d.toNat + (8*e.toNat +
    (4*f.toNat + (2*g.toNat + h.toNat))))))

private theorem mask_eq (r : V → Bool) :
    mask r = octet (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) := by
  simp [mask, weight, octet, Fin.sum_univ_succ]

private theorem octet_spec : ∀ a b c d e f g h : Bool,
    let n := octet a b c d e f g h
    n < 256 ∧ ∀ j : V, n.testBit (7-j.val) = (![a,b,c,d,e,f,g,h] : V → Bool) j := by
  native_decide

theorem mask_lt (r : V → Bool) : mask r < 256 := by
  rw [mask_eq]; exact (octet_spec _ _ _ _ _ _ _ _).1

theorem mask_digit (r : V → Bool) (j : V) : (mask r).testBit (7-j.val) = r j := by
  rw [mask_eq, (octet_spec _ _ _ _ _ _ _ _).2 j]
  fin_cases j <;> rfl

theorem leading_bit_order (u v : Fin 256) (k : V) (h : v ≤ u)
    (earlier : ∀ t : V, t < k → u.val.testBit (7-t.val) = v.val.testBit (7-t.val)) :
    v.val.testBit (7-k.val) = true → u.val.testBit (7-k.val) = true := by
  intro hv
  cases hu : u.val.testBit (7-k.val) with
  | true => rfl
  | false =>
    exfalso
    apply Nat.not_lt_of_ge (show v.val ≤ u.val from h)
    apply Nat.lt_of_testBit _ hu hv
    intro j hj
    by_cases huge : 8 ≤ j
    · have bound : 256 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < 2) huge
      simp [Nat.testBit_eq_false_of_lt (u.isLt.trans_le bound),
            Nat.testBit_eq_false_of_lt (v.isLt.trans_le bound)]
    · have t : 7-j < 8 := by omega
      have eq := earlier ⟨7-j,t⟩ (by change 7-j < k.val; omega)
      have e : 7-(7-j)=j := by omega
      simpa only [e] using eq

end QGI.DoubleEight.BareLex